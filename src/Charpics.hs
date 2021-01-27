{- ********************************************************
 | module Charpics containing ABSTRACT TYPE Picture      |
 |                                                       |
 |                                                       |
 | Chris Reade                                           |
 | Originally defined for ML in  Oct 1987                |
 | Appeared in appendix 2 of                             |
 |                  Elements of Functional Programming,  |
 |                  by Chris Reade                       |
 |                  Addison Wesley 1989                  |
 |                                                       |
 | Redefined for SML '97 standard Jan 1999               |
 | Converted to Haskell  Sept '01                        |
 |                                                       |
 |                                                       |
 ******************************************************** -}

module Charpics (Picture, cutfrom,paste,header,frame,table,lower,indent,
                 column,colwith,row,rowwith,padbottom,padside,nullpic,mkpic,
                 linesof,width,depth)

where

   {-  Some functions from ChrisPrelude are not imported but 
       duplicated for easier reference -}

maxposlist:: (Num a, Ord a) => [a] -> a
maxposlist  = foldl max (fromInteger 0)
spaces n = replicate n ' '
linkwith (front,sep,back) xs
               = let f []  = [back] 
                     f [a] = [a,back] 
                     f (a:x) = a:sep:f x
                 in concat (front: f xs)
transpose [] = [] 
transpose x  = if any null x 
               then [] 
               else (map head x): transpose (map tail x)
splice f = let sf (a:x) (b:y) = f a b : sf x y 
               sf x [] = x 
               sf [] x = x
           in sf


{- Main Functions -}
data Picture = Pic{depth::Int, width::Int, linesof::[String]}

instance Show Picture where
   show picture = linkwith ("","\n","\n") (linesof picture)

mkpic linelist 
        = let d = length linelist
              shape = map length linelist
              w = maxposlist shape
              addspaces line = let a = length line
                               in
                                 if a<w then line++spaces(w-a) 
                                        else line
              checkedlines = map addspaces linelist
           in Pic d w checkedlines

nullpic = Pic 0 0 []
padside n (pic @ (Pic d w sl))
          = if n <= w then pic
                      else Pic d n (map (++spaces(n-w)) sl)
padbottom n (pic @ (Pic d w sl))
          = if n <= d then pic
                      else Pic n w (sl ++ replicate (n-d) (spaces w))

rowwith fsb piclist 
          = let d' = maxposlist(map depth piclist)
                blocks = map (linesof . padbottom d') piclist
                mkline n = linkwith fsb (map (!!(n-1)) blocks)
                sl' = map mkline [1..d']
                w' = if null sl' then 0 else length(head sl')
            in Pic d' w' sl'

row = rowwith ("","","")

colwith (f,s,b) piclist
          = let w' = maxposlist(map width piclist)
                flines = map (replicate w') f
                slines = map (replicate w') s
                blines = map (replicate w') b
                sl' = linkwith(flines,slines,blines)
                              (map (linesof . padside w') piclist)
                d' = length sl'
             in Pic d' w' sl'

column = colwith ("","","")

indent n (pic @ (Pic d w sl))
               = if n<1 then pic
                        else Pic d (w+n) (map (spaces n ++) sl)

lower n (pic @ (Pic d w sl))
               = if n<1 then pic
                        else Pic (d+n) w (replicate n (spaces w) ++ sl)

table [] = nullpic
table piclistlist 
         = let mkrect piclistlist  {-  makes sure each list has same length  -}
                      = let sizerows = map length piclistlist
                            maxrow = maxposlist sizerows
                            addnulls len piclist
                                = if len<maxrow 
                                  then piclist ++ (replicate (maxrow-len) nullpic)
                                  else piclist
                        in zipWith addnulls sizerows piclistlist
               newpics = mkrect piclistlist
               picwidths = map(map width) newpics
               colwidths = map maxposlist (transpose picwidths)
               picrowlists = map (zipWith padside colwidths) newpics
               tablerows = map (rowwith ("|","|","|")) picrowlists
               dashes n = replicate n '-'
               sep = linkwith ("+","+","+") (map dashes colwidths)
               sl' = linkwith ([sep],[sep],[sep]) (map linesof tablerows)
               d' = length sl'
               w' = length(head sl')
           in Pic d' w' sl'

frame picture = table [[picture]]
           
header s pic = colwith ("","~","") [mkpic[s],pic]

paste n m pic1 pic2   {-  n,m may be negative, pic2 goes over  -}
                      {-  pic1 at n rows down and m chars in   -}
            = if n<0 then paste 0 m (lower (-n) pic1) pic2 else
              if m<0 then paste n 0 (indent(-m) pic1) pic2 else
              let pic1' = padbottom (n+depth pic2) (padside (m+width pic2) pic1)
                  spliceat n f x y = if n<1 
                                     then splice f x y
                                     else head x:spliceat (n-1) f (tail x) y
                  overlay a b = b
                  stringop line line' = spliceat m overlay line line'
                  sl' = spliceat n stringop (linesof pic1') (linesof pic2)
                  w' = if null sl' then 0 else length(head sl')
                  d' = length sl'
              in Pic d' w' sl'

cutfrom pic n m a b  {-  n,m,a,b may be negative, a picture of size a deep and b wide  -}
                     {-  is cut from pic starting at n rows down and m chars in        -}
            = if n<0 then cutfrom (lower (-n) pic) 0 m a b else
              if m<0 then cutfrom (indent(-m) pic) n 0 a b else
              if a<0 then cutfrom pic (n+a) m (-a) b       else
              if b<0 then cutfrom pic n (m+b) a (-b)       else
              let pic' = padbottom (n+a) (padside (m+b) pic)
                  edit str = take b (drop m str)
                             {-was  sublist (m+1) b str -}
                  newsl = (map edit . take a . drop n . linesof ) pic'
                                  
              in Pic a b newsl





{- ******************** COMMENTS **********************************

Abstract type Picture 

The following are available for constructing character pictures
 


** BASIC OPERATIONS ****************

 mkpic       :: [String] -> Picture
             This can be used to form very simple atomic pictures.
             The argument should be a list of the picture lines.
 show        :: Picture -> String
             This is used to see pictures.
 depth       :: Picture -> Int  -- selector function
             Returns the number of lines
 width       :: Picture -> Int  -- selector function
             Returns the length of the longest line
 linesof     :: Picture -> [String]  -- selector function
             Returns the lines themselves (used in defining some other ops.)
 nullpic     :: Picture
             An empty picture. (Equivalent to mkpic[]).

** MAIN PICTURE OPERATIONS *******

 frame       :: Picture -> Picture
             This outlines a picture using "+---+" and "|"
 table       :: [[Picture]] -> Picture
             This forms a table when supplied with a list of the rows of the
             table. Each row should be a list of pictures.
 paste       :: Int -> Int -> Picture -> Picture -> Picture
             paste n m p1 p2 places p2 ontop of p1 at the point after
             n characters down and m characters along. It is robust in that
             it works for negative n and m and when p1 is too small.
 cutfrom     :: Picture -> Int -> Int -> Int -> Int -> Picture
             cutfrom p n m d w produces a picture of depth d and width w
             cut from p starting at the point after n characters down and
             m characters along. (None of the integers are required to be 
             positive.

** SOME OTHER PICTURE OPERATIONS *******

 row         :: [Picture] -> Picture
             This forms a picture by lining up a list of pictures as a row
 column      :: [Picture] -> Picture
             This forms a picture by lining up a list of pictures as a column
 rowwith     :: ([Char],[Char],[Char]) -> [Picture] -> Picture
             Similar to row, but a triple of strings must be supplied
             to be duplicated on the left, between pictures and on the
             right respectively.
 colwith     :: ([Char],[Char],[Char]) -> [Picture] -> Picture
             Similar to column, but a triple of strings must be supplied
             (characters) to be duplicated along the top, between pictures
             and along the bottom, respectively.
 indent      :: Int -> Picture -> Picture
             indent n p adds spaces to the left of p
 lower       :: Int -> Picture -> Picture
             lower n p adds spaces at the top of p
 padside     :: Int -> Picture -> Picture
             padside n p forms a picture of AT LEAST width n using
             spaces to pad when necessary.
 padbottom   :: Int -> Picture -> Picture
             padbottom n p forms a picture of AT LEAST depth n using
             spaces to pad when necessary.
 header      :: [Char] -> Picture -> Picture
             The string is supplied as a heading to be placed above the picture.

********************************************************************** -}
