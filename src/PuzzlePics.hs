module PuzzlePics (seeBoard,seeGame,seeGames,seeSolution) where


import Charpics
import TrainTracks
    
blank, fblank, dotPic :: Picture
blank = mkpic [spaces 3]
fblank = frame blank
dotPic = mkpic ["o"]

boardPicSize:: Int -> Picture
boardPicSize n = table $ take n $ repeat $ take n $ repeat blank

spaces n = replicate n ' '

pieceToPic :: Piece -> Picture
pieceToPic m = case m of
     NE -> paste 0 2 fblank (mkpic ["#-+","###"])
     NW -> paste 0 0 fblank (mkpic ["+-#","###"])
     NS -> paste 0 0 fblank (mkpic ["+-#","| #","+-#"])
     WE -> paste 1 0 fblank (mkpic ["#####"])
     SW -> paste 1 0 fblank (mkpic ["###", "+-#"])
     SE -> paste 1 2 fblank (mkpic ["###", "#-+"])

placeon :: Picture -> Square -> Picture -> Picture
placeon pic (i,j) pp 
    = paste down across pic pp where
      down = depth pic - (depth fblank-1) * (j+1) - 1
      across = (width fblank -1) * i

placeDoton :: Picture -> Square -> Picture -> Picture
placeDoton pic (i,j) pp 
    = paste (down+1) (across+2) pic pp where
      down = depth pic - (depth fblank-1) * (j+1) - 1
      across = (width fblank -1) * i

seeBoard :: Board -> Picture
seeBoard b = addFinal (addStart basePic) where
    basePic = column [colNums, row [dotstrackB,rowNums]]
    boardPic = boardPicSize (length (colSums b))
    trackB = foldl addPiece boardPic (track b)
    dotstrackB = foldl addDot trackB (dots b)
    rowNums = colwith (" "," "," ") $ map sumPic $ reverse $ rowSums b
    colNums = rowwith ("  ","   ","  ") $ map sumPic $ colSums b
    addPiece p (piece,coord) = placeon p coord (pieceToPic piece)
    addDot p coord = placeDoton p coord dotPic
    sumPic s = mkpic [show s]
    addStart p = placeon p (sx-1,sy) (mkpic["    +"," A ##","    +"])
    addFinal p = placeon p (fx+1,fy-1) (mkpic["+-#-+", "  #  ","  B  "])
    (sx,sy) = start b
    (fx,fy) = finish b

seeGame :: Game -> Picture
seeGame (Game b) = seeBoard b

seeSolution :: Solution -> Picture
seeSolution (Solution b) = seeBoard b

seeGames :: [Game] -> Picture
seeGames gs = colwith  (spaces vgap, spaces vgap, spaces vgap) $ pairpics $ map seeGame gs
  where
    pairpics [] = []
    pairpics [a] = [indent margin a]
    pairpics (a:b:more) = rowwith (spaces margin, spaces hgap, "") [a,b] : pairpics more
    margin = 2
    hgap = 2
    vgap = 2

{-
+---+
|   |   fblank
+---+

+---+
### |   SW
+-#-+

+-#-+
| ###   NE
+---+

+---+
#####   WE
+---+

+-#-+
| # |   NS
+-#-+

+---+
| ###   SE
+-#-+

+-#-+
### |   NW
+---+


-}


