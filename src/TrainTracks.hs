module TrainTracks where

{- Train Track Puzzles see e.g. https://puzzlemadness.co.uk/howwemaketraintracks/
-}

import System.Random (RandomGen, randoms, split, randomR)
import Data.List (sortBy, intersect, nub, (\\))
import Data.Ord (comparing)

-- | track pieces (will be associated with coordinates to make track)
data Piece = NS | WE | NW | SW | NE | SE  deriving (Eq,Show,Read)

-- | 4 possible directions 
data Direction = N | S | W | E deriving (Eq,Show,Read)

-- | Move is the same as direction, BUT used specifically to represent a move direction
-- maybe a newtype is needed to distinguish the latter 
type Move = Direction

-- | type for coordinates with column first, then row as in (x,y)
type Square = (Int,Int)

-- | Path is used when the list of coordinates forms a path
-- a newtype would be better, but many functions work on arbitrary coord lists including paths
type Path = [Square]

-- | TrackSquare represents a single track piece at a specified coordinate
type TrackSquare = (Piece,Square)

-- | Track  is a list of TrackSquares (not necessarily ordered or linked up)
type Track = [TrackSquare]

-- | Immediate neighbours of a coordinate - may be off the board
extend :: Square -> [Square]
extend (i,j) = [(i-1,j),(i+1,j),(i,j-1),(i,j+1)]

-- | predicatte to determine if a coordinate is on the board ((0,0)..(n,n)) where n=brdSize-1
-- and brdSize is the first arg
onBoard :: Int -> Square -> Bool
onBoard brdSize (i,j) = i>=0 && i < brdSize && j>=0 && j < brdSize

-- | checks if a new square is not already on a path when extending a path (given boardSize arg)
validSquare :: Int -> Square -> Path -> Bool
validSquare brdSize x path = onBoard brdSize x && x `notElem` path

-- | randPathStep: used by randGenPath
-- When extending a non-empty path the first (head) element is used
-- to find all validSquare neighbours
-- The valid neighbours are randomly shuffled, and a list of possible extended paths returned.
-- If there are no valid extensions an empty list will result.
-- Being random, means a random number generator is required as first argument
-- (and boardsize is second arg)
randPathStep :: (RandomGen g) => g -> Int -> Path -> [Path]
randPathStep g brdSize [] = []
randPathStep g brdSize (p @ (h:_)) = map (:p) rands
      where rands  = rshuffle g [x | x <- extend h, validSquare brdSize x p]

-- | random shuffle of a list, used by randPathStep
rshuffle :: (RandomGen g) => g -> [x] -> [x]
rshuffle g [] = []
rshuffle g [a] = [a]
rshuffle g es = map snd . sortBy (comparing fst) $ zip rs es
    where rs = randoms g :: [Integer]

{- | randGenPath (new version) 
 main function to generate a random path given a boardSize and a minimum length (using randGrowTrack).
 Arguments are a random generator and a minimum path length.
 It uses the random generator to select a finish position (column number),
 then randomly grows paths backwards from the finish square using randGrowTrack
 with a new random generator.  It filters for accpted finishing paths. 
 HOWEVER
 there are random occasions when no finishing paths are found in a reasonable time 
 (many minutes = millions of rejcted paths) so we use a cut off after 1000 paths.
 If no finishing (and acceptable) paths are found in the first 1000,
 randGrowTrack is restarted with a new generator
-}
randGenPath :: (RandomGen g) => g -> Int -> Int -> Path
randGenPath gen brdSize len = try gen1 where
    (finishCol, gen1) = randomR (0,brdSize-1) gen
    try g = case findInChunk (accept brdSize) 1000 $ randGrowTrack g brdSize (len-1) [[(finishCol,0)]] of
              (p:_) -> p
              []    -> try g' where (g',_) = split g

-- | findInChunk acceptable n paths  produces acceptable finishing paths found in the first n paths             
findInChunk:: (Path->Bool) -> Int -> [Path] -> [Path]
findInChunk acceptable n = filter acceptable . filter finishing . take n 

{-OLD VERSION could, on occasion, genearate overwhelming numbers of non-finishing paths
randGenPath :: (RandomGen g) => g -> Int -> Path
randGenPath g n = 
    let (finishCol, g') = randomR (0,boardSize-1) g
    in head $ filter accept $ filter finishing $ randGrowTrack g' n [[(finishCol,0)]]
-}


{- |
randGrowTrack randomly grows paths for a given boardSize of a given minimum length from a list of given paths.
Paths are grown backwards from finish to start, so the head item is the newest.
The integer argument is the minimum length to grow (additional to each starting path length)
It requires a random generator and produces a new list of possible paths.
It works by supplying a new random generator to randPathStep and applying this to all the paths
(with the same generater for each path). 
It recurses with a new random generator and decremented minimum.
-}
randGrowTrack :: (RandomGen g) => g -> Int -> Int -> [Path] -> [Path]
randGrowTrack g brdSize 0 sofar = sofar
randGrowTrack g brdSize n sofar = 
    randGrowTrack g' brdSize (n-1) $ concatMap (randPathStep g'' brdSize) sofar
    where (g',g'') = split g

-- | used by randGenPath to check a path has completed (reaching start column)
finishing :: Path -> Bool
finishing (sq:_) = colNum sq == 0
finishing [] = False
 
-- | used by randGenPath to remove final paths with empty rows or columns 
-- (requires boardSize as first arg)        
accept :: Int -> Path -> Bool
accept brdSize p = all (>0) (allColCount brdSize p)  && all (>0) (allRowCount brdSize p) 

-- | integer specific versions for coordinate selectors (fst for colNum, snd for rowNum)
rowNum, colNum :: (Int,Int) -> Int
rowNum = snd
colNum = fst

-- | much code is common for dealing with rows vs columns
-- ColRow allows a simple C or R to be passed as argument to common code to select rows or columns
data ColRow = C | R

-- | colrow selects for columns or rows using a more general type than colNum and rowNum
-- This is needed later to specialise common code for row/col sums
colrow:: ColRow -> (a,a) -> a
colrow C  = fst
colrow R  = snd

-- | common code for summing elements from a list of squares
-- in each colomn or each row (depending on ColRow argument)
-- it requires boardSize arg
-- it ruturns a list of Ints which are sums in order of the rows/columns
allCountCR:: ColRow -> Int -> [Square] -> [Int]
allCountCR cr brdSize path = map count [0..brdSize-1] where
    count n = length $ filter ((n==).colrow cr) path

-- | allColCount,allRowCount are specialised versions of allCountCR,
-- counting elements in a list of squares for each col and each row respecively   
allColCount,allRowCount:: Int -> [Square] -> [Int]
allColCount = allCountCR C
allRowCount = allCountCR R

{- | checking that given rowSums and colSums match up with a completed path
-- assumes ordered rowSums and colSums
-- boardSize is calculated from length of summs argument
-}
checkSumsCR:: ColRow -> [Int] -> Path -> Bool
checkSumsCR cr sums path = sums == allCountCR cr (length sums) path

checkRowSums:: [Int] -> Path -> Bool
checkRowSums = checkSumsCR R

checkColSums:: [Int] -> Path -> Bool
checkColSums = checkSumsCR C

-- | pathToMoves turns a path into a sequence of moves from the start square (head of path)
pathToMoves :: Path -> [Move]
pathToMoves path = zipWith mkMove path (tail path)

-- | used by pathToMoves, mkMove makes a Move from 2 adjacent squares first square to second
-- results can be spurious for non adjacent squares
mkMove:: Square -> Square -> Move
mkMove (x1,y1) (x2,y2) = 
          if x1==x2
          then if y2==y1-1 then S else N
          else if x2==x1-1 then W else E

-- | pathToPieces  makes a list of track pieces from a path in order (from the start)
-- it uses pathToMoves path with an extra move E at the start and a final move S at the finish
pathToPieces :: Path -> [Piece]
pathToPieces p = snd $ foldr addPiece (S,[]) (E:pathToMoves p)
     where addPiece m1 (m2,tr) = (m1, combineMoves m1 m2: tr)

-- | converts a path into a track list ordered from start to finish
pathToTrack :: Path -> Track
pathToTrack path = zip (pathToPieces path) path

-- | two consecutive moves determine a track piece.
-- opp is needed to get direction of where first move came from when calling mkPiece
combineMoves:: Move -> Move -> Piece
combineMoves m1 m2 = mkPiece (opp m1)  m2 
-- e.g. going West then North is  NE track piece   

-- | two directions determine a track piece (provided they are not identical directions)
mkPiece::  Direction -> Direction -> Piece   
mkPiece W N = NW
mkPiece W S = SW
mkPiece W W = error "mkPiece W W"
mkPiece W E = WE
mkPiece E N = NE
mkPiece E S = SE
mkPiece E E = error "mkPiece E E" 
mkPiece E W = WE 
mkPiece N E = NE
mkPiece N W = NW
mkPiece N N = error "mkPiece N N"  
mkPiece N S = NS
mkPiece S W = SW
mkPiece S E = SE
mkPiece S S = error "mkPiece S S"
mkPiece S N = NS

-- | opp reverses a direction (also used for moves and moves <-> directions)
opp:: Direction -> Direction
opp N = S
opp W = E
opp E = W
opp S = N

{- | 
Type Board is used to keep information about the state of play while looking for solution
Dots are squares that are known to require track, but undetermined piece.
Unknowns (usually) record remaining undetermined squares.
in which case "known blanks" are implicitly the squares that are not track or dots or unknowns
Exceptions: Solution and Game Boards
In a Solution Board, unknowns are removed, no dots, so just track.
Similarly a Game Board is a Solution board but with some track removed 
(so no unknowns or dots)
-}
data Board = Board
        { track::Track -- ^ track is a list of known track pieces with their coordinates
        , dots::[Square] -- ^ dots represent squares which are known to need a track piece
        , start::Square -- ^ start is a square on the board - always in column 0
        , finish::Square  -- ^ finish is a square on the board - always in row 0
        , colSums::[Int] -- ^ colSums records the required sum of track pieces in each column 
        , rowSums::[Int] -- ^ rowSums records the required sum of track pieces in each row 
        , unknowns::[Square]  -- ^ unknowns (usually) records remaining undetermined squares.
        } deriving (Show,Read)

-- board Size can be calculated from either rowSums or colSums length
-- so not included explicitly in a board
boardSize:: Board -> Int
boardSize b = length (colSums b)

-- | a Solution is a board with no dots, no unknowns, complete track, calculated final colSums and rowSums
-- track is path ordered (when created from a path by solutionBoard)
newtype Solution = Solution Board deriving (Show,Read)

-- | a Game is a board which is a like a solution board but with (most) track removed
newtype Game = Game Board deriving (Show,Read)

-- | solutionBoard creates a Solution board from a given path                   
solutionBoard:: Path -> Solution
solutionBoard path = Solution $ Board
  { start = head path
  , finish = last path
  , colSums = allColCount brdSize path
  , rowSums = allRowCount brdSize path
  , dots = [] 
  , track = pathToTrack path
  , unknowns = [] 
  } where brdSize = 1+max (maximum(map fst path)) (maximum (map snd path))

{- |
solveInit creates an initialised board from a Game.
Start finish are added to dots; track ends are added to dots (when not already in track)
Unknowns are initialised to everything else.
-}
solveInit :: Game -> Board
solveInit (Game b) = b { dots = newdots , unknowns = initunknowns \\ newdots }
        where
            size = boardSize b
            trackcoords = map snd (track b) 
            checked = newdots++trackcoords
            trackends = map snd $ concatMap findends $ track b
            newdots = nub $ start b: finish b : (initunknowns `intersect` trackends)
                      -- nub removes duplicates
            initunknowns = [(i,j) | i<-[0..size-1], 
                                    j<-[0..size-1], 
                                    notElem (i,j) trackcoords ]

-- | findends is applied to a track piece and returns the squares at each end of the piece 
-- along with the direction of the move to that square
findends:: TrackSquare -> [(Move,Square)]
findends (piece, (i,j)) =
    case piece of
        NS -> [(S,(i,j-1)), (N,(i,j+1))]
        WE -> [(W,(i-1,j)), (E,(i+1,j))]
        NW -> [(W,(i-1,j)), (N,(i,j+1))]
        SW -> [(S,(i,j-1)), (W,(i-1,j))]
        NE -> [(E,(i+1,j)), (N,(i,j+1))]
        SE -> [(S,(i,j-1)), (E,(i+1,j))]

-- | trackLength calculated from argument boardsize (also uses a percentageTrack of 50)
--  used by randGenSamples
trackLength:: Int -> Int
trackLength brdSize = (brdSize * brdSize * percentageTrack) `div` 100
  where percentageTrack = 50

-- | randGenSamples uses a random generator and a boardsize, returning an infinite list of Solutions
-- It uses a new generator for each call of randGenPath and returns the first Solution in each list
randGenSamples:: (RandomGen g) => g -> Int -> [Solution]              
randGenSamples gen brdSize = 
   solutionBoard (randGenPath gen1 brdSize (trackLength brdSize)): randGenSamples gen2 brdSize
        where (gen1,gen2) = split gen

{- |
randGenGames creates games from solutions by randomly selecting track items to keep
from each supplied Solution to create Game boards
It uses rSelect to do this and a different generator for each board.
Note that track is expected to be in path order in a solution board
-}
randGenGames ::(RandomGen g) => g -> [Solution] -> [Game]
randGenGames g [] = []
randGenGames g (Solution b : more) = 
    Game( b{track = selectedtrack} ) : randGenGames g2 more
    where
      tr = track b
      selectedtrack = map (tr!!) (rSelect g1 (length tr))
      (g1,g2) = split g

-- | rSelect 'randomly' selects indices (of track to keep) when given a max (track length) BUT 
-- it is designed to keep a reasonable spread between indices and total number of indices
-- e.g. usually 3 items for max 32, not too close together or too near start/finish
rSelect::(RandomGen g) => g -> Int -> [Int]
rSelect gen length = rIndex gen gap (length-gap)
     where gap = 3
           rIndex g minim maxim = 
               if minim + (2*gap+1) >= maxim 
               then []
               else rIndex g2 minim (i-gap) ++ [i] ++ rIndex g3 (i+gap) maxim
                    where (i,g1) = randomR (minim, maxim) g
                          (g2,g3) = split g1

{- Older version of rSelect
rSelect::(RandomGen g) => g -> Int -> [Int]
rSelect gen length = randIndex gen low high
     where tenp = length `div` 10
           low = 3
           high = length-low
           mingap = low+1
           maxgap = 2*mingap
           randIndex g minim maxim = 
               if minim + maxgap > maxim 
               then []
               else i:randIndex g' (i+mingap) maxim
                    where (i,g') = randomR (minim, minim+maxgap) g
-}









