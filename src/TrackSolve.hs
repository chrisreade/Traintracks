module TrackSolve where
{- |
Apply 'deterministic' tactics to progress the first board in a goal (current board) uniquely
Checking if the current board has become a solution with checkSolved or a dead-end with checkFaulty.

Only try `non-deterministic` tactics when the deterministic ones make no further progress.
Non-deterministic tactics can introduce `faulty` boards that have no solution, so tactics can
remove boards which they find have gone wrong.

Every Tactic returns 
    Nothing if it cannot make progress, 
    Just newgoal only if it has made a change to current board or goal

To try several tactics on a goal, use alternative combinator <|> but then repeat (e.g. with cycleTac)
as the first success will ignore further tactics in a list of alternates a <|> b <|> c....
Tactic combinator cycleTac uses the sequence tactic combinator >>> 

The final solver tactic is the main one.
-}

        
import TrainTracks
import PuzzlePics
import Data.List (intersect, (\\))
import Data.Maybe (mapMaybe)
import System.Random (RandomGen,split)



{- | Goal represents the state of play while looking for solutions
 The list of boards are those remaining to be solved.
 Only the current board (first one) is checked at each step
 Other boards are alternatives if the first one is found to be faulty/dead-end
 The list of solutions are completed boards
 Starting from a goal ([b],[]) where b is an initialised 'current' board with dots, 
 and [] is list of initial Solutions
 Hope to end up with ([],solns) then check how many solutions there are.
-}
type Goal = ([Board],[Solution])

-- | Setup goal from game            
startGoal:: Game -> Goal                
startGoal game  = ([solveInit game],[])


{- | A tactic contains a function to try to progress the goal
   All tactics return Nothing if they cannot progress the goal 
   (including when applied to a finished goal of the form ([],solutions))
   -- Except okTac which does not inspect the goal (not actually used)
   They return Just g when g is a new goal.
   A tactic can remove a current board if it finds it is a dead end.
   The tactic checkSol is the only one that can create a new solution if the current board is a finished solution
-}
newtype Tactic = Tactic (Goal -> Maybe Goal)


{-----------------
Tactic combinators
------------------}

{-
Thoughts about tactic combinators

okTac and failTac are a bit like True and False and
<|> is like `or` (but not commutative)  
    failTac <|> t = t,   
    okTac   <|> t = okTac

A strict sequence `before` could be defined as a kind of `and`
a `before` b would only succeed if both a and b succeed.
This is not actually defined as it is not useful
    Tactic t1 `before` Tactic t2 = Tactic t where
       t g =  Just g >>= t1 >>= t2  -- using Monad Maybe bind
   or: t g = do g' <- t1 g 
                t2 g' -- using do notation for Maybe
    
>>> is the more useful sequence (like `when..do..`) as it preserves any progress made
It could be defined in terms of `before` and <|>

    a >>> b = a `before` (b <|> okTac) 
and
    failTac >>> t = failTac = failTac `before` t,   
    okTac   >>> t = t       = okTac   `before` t
-}


{- | Tactic combinator  <|> 
   t1 <|> t2 is an alternatives tactic 
   It fails with Nothing if both t1 and t2 fail
   It tries t1 first and tries t2 only if t1 fails
   (i.e. t2 will not be tried if t1 succeeds)
-}
infixr 0 <|>
(<|>):: Tactic -> Tactic -> Tactic
Tactic t1 <|> Tactic t2 = Tactic t where
-- t g = fromMaybe (t2 g) (t1 g)
    t g = case t1 g of
           Nothing -> t2 g
           okother -> okother


{- | Tactic combinator  >>> 
t1 >>> t2 is a sequence that only tries t2 if t1 succeeds.
However the progress from t1 is retained if t2 fails
The combination fails with Nothing if t1 fails (so t2 not tried)

Equivalent to this:-
t1 >>> t2 = t1 `before` (t2 <|> okTac) where
    Tactic t1 `before` Tactic t2  = Tactic t 
          where t g = Just g >>= t1 >>= t2  -- using Maybe bind >>=
    okTac = Tactic Just
Here the stricter `before` succeeds only if both tactics in the sequence succeed
but the use of okTac (which always succeeds) will recover progress from t1 when t2 fails

We are only going to use >>> and <|> with basic tactics (and do not need okTac and `before`)
-}
infixr 1 >>>
(>>>):: Tactic -> Tactic -> Tactic
Tactic t1 >>> Tactic t2 = Tactic t where
    t g = case t1 g of
           Nothing -> Nothing
           Just g1 -> case t2 g1  of
                        Nothing -> Just g1 -- retain progress from t1 when t2 fails
                        okother -> okother

-- | a trivial tactic. This never succeeds.
failTac :: Tactic
failTac = Tactic (\_-> Nothing) -- always fails
 
-- | a trivial tactic. This always succeeds. Not actually used.
okTac :: Tactic
okTac = Tactic Just -- always succeeds

-- | sequence the argument tactic a given number of times 
-- (mostly used for debugging to inspect when cycleTac fails)
rptTac:: Int -> Tactic -> Tactic
rptTac 0 t = failTac
rptTac n t = t >>> rptTac (n-1) t


-- | sequence the argument tactic indefinitely until it fails
-- cycleTac t = t >>> cycleTac t   -- this causes a <<loop>> so need to expand the definition one step
cycleTac:: Tactic -> Tactic
cycleTac (Tactic t) =  Tactic rt where
        rt g = case t g of
               Nothing -> Nothing
               Just g1 -> case rt g1  of
                            Nothing -> Just g1
                            okother -> okother


                
{-----------------------
 Deterministic tactics: 
 these do not increase number of boards in a goal
 but may remove a faulty or completed current board from the goal
                        
 checkFaulty, checkSolved, checkDots, colUtoDot, rowUtoDot, colUtoBlank, rowUtoBlank, colUtoBlank
                        
-----------------------}

-- | checkFaulty (deterministic) Tactic
-- abandons a board with unused track but with a path from start to finish
-- It returns Nothing if the board seems to be finished (to be picked up by checkSolved tactic)
checkFaulty::Tactic
checkFaulty = Tactic see where
    see ([],solns) = Nothing
    see (b:more, solns) = 
        case trackToPath b of
            Nothing -> Nothing
            Just p -> if dots b == [] 
                      then Nothing -- not apparently Faulty
                      else Just (more,solns) -- left over dots faulty board 

-- | checkSolved (deterministic) Tactic
-- looks for a completed board (no dots left)
-- It abandons a board unless it is correctly completed 
-- (with a path from start to finish using all track and correct colSums, rowSums)
-- It returns Nothing if there are remaining dots
checkSolved::Tactic
checkSolved = Tactic see where
    see ([],solns) = Nothing 
    see (b:more, solns) = 
        if dots b /= []
        then Nothing
        else case trackToPath b of
                Nothing -> Just (more,solns)  -- incomplete path and no dots - remove faulty board
                Just path ->  if checkColSums (colSums b) path && checkRowSums (rowSums b) path
                              then Just (more,solutionBoard path:solns) -- finished board
                              else Just (more,solns) -- faulty checkSum - remove faulty board



-- | trackToPath looks for a completed path from start to finish using All the track in a board
-- used by checkSolved and checkFaulty tactics
trackToPath:: Board -> Maybe Path
trackToPath b = tToP (start b) (track b) (finish b) S [] where

tToP :: Square -> Track -> Square -> Move -> Path -> Maybe Path
tToP _ [] _ _ _ = Nothing -- no track left (and start not reached)
tToP start [(p,sq')] sq m path = 
        if sq'==start && p==mkPiece m W 
        then Just (sq':path) 
        else Nothing 
tToP start trs sq  m path = case findInTrack trs sq of
        Nothing -> Nothing
        Just t -> tToP start (trs\\[t]) sq' m' (sq:path) 
                    where (m',sq') = nextSq m t
                     -- sq' not on board if sq == start
                     -- and will fail in the next step (findInTrack)
                     -- this will also be the case if there is unused track when path reaches the start

-- | finding if a square contains a piece of track                  
-- used by trackToPath and elsewhere
findInTrack :: Track -> Square -> Maybe TrackSquare
findInTrack [] sq = Nothing
findInTrack (t@(_,tsq):more) sq = if tsq==sq then Just t else findInTrack more sq


-- | nextSq takes a direction 'Coming From' (i.e. direction back) when entering at one end of a TrackSquare
-- and returns the next square going out at the other end of the TrackSquare
-- along with the 'Coming From' direction (i.e. direction back again)
-- used by trackToPath
nextSq:: Direction -> TrackSquare -> (Direction, Square)
nextSq W (NW,(i,j)) = (opp N,(i,j+1))  -- from W to N becomes from S (=from opp N)
nextSq N (NW,(i,j)) = (opp W,(i-1,j))
nextSq _ (NW,_    ) = error "nextSq with NW"
nextSq W (SW,(i,j)) = (opp S,(i,j-1)) 
nextSq S (SW,(i,j)) = (opp W,(i-1,j))
nextSq _ (SW,_    ) = error "nextSq with SW"
nextSq E (NE,(i,j)) = (opp N,(i,j+1))
nextSq N (NE,(i,j)) = (opp E,(i+1,j))
nextSq _ (NE,_    ) = error "nextSq with NE"
nextSq E (SE,(i,j)) = (opp S,(i,j-1)) 
nextSq S (SE,(i,j)) = (opp E,(i+1,j))
nextSq _ (SE,_    ) = error "nextSq with SE"
nextSq S (NS,(i,j)) = (opp N,(i,j+1))
nextSq N (NS,(i,j)) = (opp S,(i,j-1))
nextSq _ (NS,_    ) = error "nextSq with NS"
nextSq W (WE,(i,j)) = (opp E,(i+1,j)) 
nextSq E (WE,(i,j)) = (opp W,(i-1,j))
nextSq _ (WE,_    ) = error "nextSq with WE"

-- | domove takes a move direction and a square and gives the next square in that direction
domove :: Move -> Square -> Square
domove S (i,j)  = (i,j-1)   
domove E (i,j)  = (i+1,j)   
domove W (i,j)  = (i-1,j)   
domove N (i,j)  = (i,j+1)   
        
        
{- |
checkDots (deterministic) Tactic
tries to convert dots to track by inspecting neighbours
If any dot converts it progresses board with the single dot conversion
Fails if no dots will convert (so needs to be repeated until it fails)
It calls trydot which can remove a faulty board by returnurning a Just [].
-}
checkDots::Tactic
checkDots = Tactic try where
      try ([],s) = Nothing
      try (b:rest,s) = trydots (dots b) b (rest,s)
 
      trydots [] b (_) = Nothing
      trydots (d:more) b (rest,s) =  case trydot d b of
        Nothing -> trydots more b (rest,s)
        Just blist -> Just (blist++rest,s) --  b replaced by blist - either [] for bad board or [b'] for progress


{- |
trydot takes a board and a dot from the board and returns a Maybe list of boards
so
    Nothing (no progress)
    Just [b']  success with new board b'
    Just [] to remove faulty board b
It is deterministic so not more than 1 board returned

It inspects neighbours of the dot and each neighbour Must be a dot or a trackSquare or unknowns
anything else is confirmed blank and can't be used
contrackSqs contains neighbours with connecting track only 
(ignoring other track neighbours which cannot be connected to dot)   
-}
trydot:: Square -> Board -> Maybe [Board]
trydot dot b =
    let size = boardSize b
        nbs = filter (onBoard size) (extend dot)
        tracknbs = mapMaybe (findInTrack (track b)) nbs
        contrackSqs = map snd (filter connecting tracknbs) -- squares with connecting track to dot
        connecting n = dot `elem` (map snd (findends n))
        ndots = intersect nbs (dots b)
        nukns = intersect nbs (unknowns b)
    in
       case contrackSqs of
        (_:_:_:_) -> Just [] -- failed board with 3 or 4 connecting track neighbours - to be abandoned  
        [s1,s2] -> if dot `elem` [start b, finish b]
                     then Just [] -- failed board - to be abandoned 
                     else Just [newtrackanddots b dot (s1,s2) []] 
        [sq] -> if dot == start b 
                then Just [newtrackanddots b dot (sq, domove W dot) []]
                else if dot == finish b
                then Just [newtrackanddots b dot (sq, domove S dot) []]
                else processnbsWith sq dot ndots nukns  b
        []  ->  if dot == start b 
                then processnbsWith (domove W dot) dot ndots nukns  b -- use of sq off board
                else if dot == finish b
                then processnbsWith (domove S dot) dot ndots nukns  b -- use of sq off board
                else processnbs dot ndots nukns  b

{- | processnbsWith sq dot ndots nukns b  returns a Maybe list of boards
-- the first sq arg is an end of track connecting to dot (which is the second arg)
-- If dot is start or finish then sq is the corresponding track-end off the board     
-- ndots and nukns are remaining neighbours of dot (dots and unknowns respectively)
-- b is the board in question
-- So we are looking for a unique second neighbour to connect to.
-- When dot is converted to track, some unknowns may become new dots
-- (handled by newtrackanddots)
-}
processnbsWith :: Square -> Square -> [Square] -> [Square] -> Board -> Maybe [Board]
processnbsWith sq dot ndots nukns b =
    case (ndots,nukns) of
      ([d],[]) -> Just [newtrackanddots b dot (sq,d) []]
      ([],[u]) -> Just [newtrackanddots b dot (sq,u) [u]]
      ([],[])  -> Just [] -- dead end not at start or finish - Abandon board
      _        -> Nothing


{- | processnbs dot ndots nukns b
-- dot is first argument and is not start or finish and has no connected track nbs
-- The only neighbours of dot are ndots and nukns (dots and unknowns, respectively)  on the board b
-- So we are looking for cases with exactly two viable neighbours
-- When dot is converted to track, some unknowns may become new dots
-- (handled by newtrackanddots)
-}
processnbs:: Square -> [Square] -> [Square] -> Board -> Maybe [Board]   
processnbs dot ndots nukns b =
     case (ndots,nukns) of
       ([],[u1,u2]) -> Just [newtrackanddots b dot (u1,u2) [u1,u2]]
       ([d1,d2],[]) -> Just [newtrackanddots b dot (d1,d2) []]
       ([d],[u])    -> Just [newtrackanddots b dot (d,u) [u]]
       _            -> Nothing

{- | newtrackanddots b dot (n1,n2) utodots - replaces dot with a TrackSquare on board b returning a new board
  utodots should only contain unknowns from the pair of neighbours (n1,n2) being connected
  by the new track at dot
  It makes the unknowns utodots into dots in the resulting board.
-}
newtrackanddots :: Board -> Square -> (Square, Square) -> [Square] -> Board
newtrackanddots b dot (n1,n2) utodots = b {dots = newdots, track = newtrack, unknowns = newunks} where
        newtrack = (piece,dot):track b
        piece = mkPiece (mkMove dot n1) (mkMove dot n2)
        newdots = utodots ++ (dots b \\ [dot])
        newunks = unknowns b \\ utodots

{- |
colUtoBlank (deterministic) Tactic       
looks for (newly) completed columns (with sum accounted for by dots and track) and also over-filled ones
(newly = unknowns found in column, so this column has not been previously completed)
If it finds a completed column 'with remaining unknowns',
    it removes unknowns from the column (making them blanks) and updates the board
It abandons the current board if it finds an overfilled column
    (needs to be repeated until it fails in order to check all columns)
Note that if it finds no unknowns in a col, it has already been completed, so no progress in that column
-}
colUtoBlank::Tactic
colUtoBlank = colrowUtoBlank C

{- |
rowUtoBlank (deterministic) Tactic
 same as colUtoBlank but rows instead of columns      
-}
rowUtoBlank::Tactic
rowUtoBlank = colrowUtoBlank R

-- | colrowUtoBlank - Common code for colUtoBlank and rowUtoBlank
colrowUtoBlank ::ColRow -> Tactic
colrowUtoBlank cr = Tactic try where
    try ([],s) = Nothing -- Just ([],s)
    try (b:rest,s) = tryCR 0 sums (dots b ++ map snd (track b)) b (rest,s)  -- start row/col 0  
                      where sums = colrow cr (colSums b, rowSums b)

    tryCR i [] sqs b (_) = Nothing
    tryCR i (n:more) sqs b (rest,s) =  
        -- This test is ESSENTIAL to check whether this tactic progresses the board
        if length unks == 0 then tryCR (i+1) more sqs b (rest,s)  -- no progress this row/col
        else if filled>n 
        then Just(rest,s) -- abandon board b
        else if filled==n 
        then Just (b':rest,s) -- progress b to b'         
        else tryCR (i+1) more sqs b (rest,s)
        where 
            unks = filter ((==i).colrow cr) (unknowns b)
            filled = length (filter ((==i).colrow cr) sqs)
            b' = b {unknowns = unknowns b \\ unks} -- remove unknowns from col/row
       
{- |
colUtoDot (deterministic) Tactic
looks for columns with remaining unknowns where all non blanks account for the column sum
If it finds such a column (with remaining unknowns) these unknowns are converted to dots,
    (needs to be repeated until it fails in order to check all columns)
If a col has no unknowns it cannot progress
 uses common code colrowUtoDot
-}
colUtoDot::Tactic
colUtoDot = colrowUtoDot C

{- |
rowUtoDot (deterministic) Tactic
 same as colUtoDot but with rows instead of columns
 uses common code colrowUtoDot
-}
rowUtoDot::Tactic
rowUtoDot = colrowUtoDot R

-- | colrowUtoDot - Common code for colUtoDot and rowUtoDot
colrowUtoDot:: ColRow -> Tactic
colrowUtoDot cr = Tactic try where
    try ([],s) = Nothing
    try (b:rest,s) = tryCR 0 sums (dots b ++ map snd (track b) ++ (unknowns b)) b (rest,s)  
                      where sums = colrow cr (colSums b, rowSums b)

    tryCR i [] sqs b (_) = Nothing
    tryCR i (n:more) sqs b (rest,s) = 
        -- ESSENTIAL to check whether this tactic progresses the board
        if length unks == 0 then tryCR (i+1) more sqs b (rest,s) -- no progress this row/col
        else if nonblank==n 
        then Just (b':rest,s)          
        else tryCR (i+1) more sqs b (rest,s)
        where
            unks = filter ((==i).colrow cr) (unknowns b) 
            nonblank = length (filter ((==i).colrow cr) sqs)
            b' = b { unknowns = unknowns b \\ unks -- filter ((/=i).colrow cr) (unknowns b)
                   , dots =  unks ++ dots b 
                   } -- make unknowns into dots in column


-- | deadUtoBlank (deterministic) Tactic - removes an unknown with too few non-blank neighbours
deadUtoBlank::Tactic
deadUtoBlank = Tactic deadUnk where
    deadUnk ([],s) = Nothing
    deadUnk (b:rest,s) = tryUnks (unknowns b) b (rest,s)
    
    tryUnks [] b (rest,s) = Nothing
    tryUnks (u:more) b (rest,s) = case tryU u (filter (onBoard (boardSize b)) (extend u)) b of
        Nothing -> tryUnks more b (rest,s)
        Just b' -> Just (b':rest,s)
    tryU u nbs b = if 2 > length (nbs `intersect` nonBlanks b)
                   then Just (b{unknowns = unknowns b \\ [u]})  -- make dead-end unknown u into blank
                   else Nothing

nonBlanks:: Board -> [Square]
nonBlanks b = dots b ++ unknowns b ++ map snd (track b)



{- |-----------------------
Non Deterministic tactics:  explore alternatives when no progress from deterministic tactics
May split the leading goal board into more than 1 - increasing the number of boards to try to solve
May remove a faulty board from the goal
                        
   dotsChoices  (only one non-deterministic tactic)
                        
-----------------------}

{- |
dotsChoices (non-deterministic) Tactic
Similar to checkDots looking at neighbours of a dot, but can create board alternatives
if there is not a unique choice for converting dot to track             
-}
dotsChoices::Tactic
dotsChoices = Tactic choices where
      choices ([],s) = Nothing
      choices (b:rest,s) = choicedots (dots b) b (rest,s)
 
      choicedots [] b (_) = Nothing
      choicedots (d:more) b (rest,s) = case choosedot d b of
        Nothing -> choicedots more b (rest,s)
        Just blist -> Just (blist++rest,s)


-- | choosedot - main auxilliary function for dotsChoices tactic
-- similar to tryDot in the easyDot tactic but can return multiple boards
choosedot:: Square -> Board -> Maybe [Board]
choosedot dot b  =
    let nbs = filter (onBoard (boardSize b)) (extend dot)
        tracknbs = mapMaybe (findInTrack (track b)) nbs
        contrackSqs = map snd (filter connecting tracknbs) -- squares with connecting track to dot
        connecting n = dot `elem` (map snd (findends n))
        ndots = intersect nbs (dots b)
        nukns = intersect nbs (unknowns b)
    in
       case contrackSqs of
        (_:_:_:_) -> Just [] -- failed board to be abandoned  
        [s1,s2] -> if dot `elem` [start b, finish b]
                     then Just [] -- failed board to be abandoned 
                     else Just [newtrackanddots b dot (s1,s2) []] 
        [sq] -> if dot == start b 
                then Just [newtrackanddots b dot (sq, domove W dot) []]
                else if dot == finish b
                then Just [newtrackanddots b dot (sq, domove S dot) []]
                else choosenbsWith sq dot ndots nukns b
        []  ->  if dot == start b 
                then choosenbsWith (domove W dot) dot ndots nukns b  -- sq off board
                else if dot == finish b
                then choosenbsWith (domove S dot) dot ndots nukns b -- sq off board
                else choosenbs dot ndots nukns b
        

{- | choosenbsWith is non deterministic counterpart of deterministic processnbsWith
choosenbsWith sq dot ndots nukns b
 sq is an end of track connecting to dot (ndots and nukns are remaining neighbours of dot) 
 if dot is start or finish then sq is the adjacent track-end off the board  
returns Nothing for 4 neighbours cases otherwise
returns list of new boards  (empty list when no neighbours) - abandons board 
-}
choosenbsWith :: Square -> Square -> [Square] -> [Square] -> Board -> Maybe [Board]
choosenbsWith sq dot ndots nukns b =  --Assumes  dot is not start or finish
    case (ndots,nukns) of
--      ([d],[]) -> Just [newtrackanddots b dot (sq,d) []]
--      ([],[u]) -> Just [newtrackanddots b dot (sq,u) [u]]
      ([d1,d2],[]) -> Just [newtrackanddots b dot (sq,d1) [] -- TRY BOTH
                           , newtrackanddots b dot (sq,d2) []
                           ] 
      ([d],[u]) -> Just [newtrackanddots b dot (sq,d) [] -- TRY BOTH
                         , newtrackanddots b dot (sq,u) [u]
                         ] 
      ([],[u1,u2]) ->  Just [ newtrackanddots b dot (sq,u1) [u1]  -- TRY BOTH
                            , newtrackanddots b dot (sq,u2) [u2]
                            ]
      ([d1,d2],[u]) -> Just [ newtrackanddots b dot (sq,d1) []   -- TRY ALL THREE
                            , newtrackanddots b dot (sq,d2) []
                            , newtrackanddots b dot (sq,u)  [u]
                            ]
      ([d1,d2,d3],[]) -> Just [ newtrackanddots b dot (sq,d1) []   -- TRY ALL THREE
                              , newtrackanddots b dot (sq,d2) []
                              , newtrackanddots b dot (sq,d3) []
                              ]
      ([d],[u1,u2]) -> Just [ newtrackanddots b dot (sq,d)  []   -- TRY ALL THREE
                            , newtrackanddots b dot (sq,u1) [u1]
                            , newtrackanddots b dot (sq,u2) [u2]
                            ]

      ([],[u1,u2,u3]) -> Just [ newtrackanddots b dot (sq,u1) [u1]   -- TRY ALL THREE
                              , newtrackanddots b dot (sq,u2) [u2]
                              , newtrackanddots b dot (sq,u3) [u3]
                              ]

      ([],[])   -> Just [] -- dead end not at start or finish Abandon board
      _         -> Nothing
                            
{- | choosenbs is non deterministic counterpart of deterministic processnbs
   dot is not start or finish and has no neighbouring connecting track
   that leaves ndots (neighbouring dots) and nunks (neighbouring unknowns)
   only cases of exactly two or three neighbours are considered.  0,1 and 4 nbs produce Nothing
   When dot is converted to track, it may cause unknowns to become new dots
-}
choosenbs :: Square -> [Square] -> [Square] -> Board -> Maybe [Board]
choosenbs dot ndots nukns b =
     case (ndots,nukns) of
       ([d1,d2],[])    -> Just [newtrackanddots b dot (d1,d2) []]
       ([d],[u])       -> Just [newtrackanddots b dot (d,u) [u]]
       ([],[u1,u2])    -> Just [newtrackanddots b dot (u1,u2) [u1,u2]]
       ([d1,d2,d3],[]) -> Just [ newtrackanddots b dot (d1,d2) []
                               , newtrackanddots b dot (d1,d3) []
                               , newtrackanddots b dot (d2,d3) []
                               ]
       ([d1,d2],[u])   -> Just [ newtrackanddots b dot (d1,d2) []
                               , newtrackanddots b dot (d1,u) [u]
                               , newtrackanddots b dot (d2,u) [u]
                               ]
       ([d],[u1,u2])   -> Just [ newtrackanddots b dot (d,u1) [u1]
                               , newtrackanddots b dot (d,u2) [u2]
                               , newtrackanddots b dot (u1,u2) [u1,u2]
                               ]
       ([],[u1,u2,u3]) -> Just [ newtrackanddots b dot (u1,u2) [u1,u2]
                               , newtrackanddots b dot (u1,u3) [u1,u3]
                               , newtrackanddots b dot (u2,u3) [u2,u3]
                               ]

       _               -> Nothing



    

{------------------------
Main tactic combinations
-------------------------}

-- | tactics are combined with combinators.
-- applyTac applies a tactic to a goal
applyTac :: Tactic -> Goal -> Maybe Goal
applyTac (Tactic f) g = f g

-- | oneStepTac (deterministic) Tactic tries each of the deterministic tactics excluding checkSolved and checkFaulty
oneStepTac :: Tactic
oneStepTac = colUtoBlank <|> rowUtoBlank <|> colUtoDot <|> rowUtoDot  <|> checkDots  <|> deadUtoBlank

-- |  maxStepsTac (non-deterministic) Tactic
-- keep trying oneStepTac until it fails then try checkSolved and then checkFaulty and
-- only then attempt Non Deterministic dotsChoices when no more progress
maxStepsTac :: Tactic
maxStepsTac = cycleTac oneStepTac <|> checkSolved <|> checkFaulty  <|> dotsChoices

-- | solver is the main tactic
-- it cycles the maxStepsTac until no more progress
-- Starting with goal ([b],[])
-- It will result in Just ([],sols) where sols are all the solutions for the original board b
solver :: Tactic
solver =  cycleTac maxStepsTac


{--------------------------
Main Functions using solver
---------------------------}

-- | a predicate to check if a game has a unique solution - using solver
uniqueSol:: Game -> Bool    
uniqueSol game = case applyTac solver (startGoal game) of
                    Just ([],[_]) -> True
                    _             -> False
            
-- | main random game generator which uses the solver to filter only games with unique solutions
-- requires boardSize as well as no. of games
generateGames :: RandomGen g => g -> Int -> Int -> [Game]
generateGames gen bs n =  take n (filter uniqueSol gamestotest) where
    sols = randGenSamples g1 bs
    gamestotest = randGenGames g2 sols
    (g1,g2) = split gen










