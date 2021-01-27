module TrackDebug where

    
import TrainTracks
import TrackSolve
import PuzzlePics
import System.Random (randomR, newStdGen,split)
import Data.List (intersect, (\\))
import Data.Maybe (mapMaybe)


-- | debugGenGames is a dubugging version of generateGames with IO
-- it reports progress with accepted and rejected games
debugGenGames :: Int -> Int -> IO()
debugGenGames brdSize n =  do 
    gen <- newStdGen
    let (g1,g2) = split gen
    let sols = randGenSamples g1 brdSize
    let gamestotest = randGenGames g2 sols
    loop n 0 (zip gamestotest sols)
    where loop 0 bad gs = putStrLn ("Rejected Games: " ++ show bad)
          loop n bad ((g,s):more) = do
              putStrLn "rand game from solution"
              print $ seeGame g
              let ans = uniqueSol g
              putStrLn ("Unique solution: " ++ show ans ++"\n\n\n")
              if ans then loop (n-1) bad more else loop n (bad+1) more

{- | dubug tool debugRGP used to see number of rejected paths in randGenPath
The integer argument is the boardSize
A major problem was found in randomness of older randGenPath and randGrowTrack:  
occasionally MILLIONS of non-finishing paths generated and rejected taking many minutes
This version outputs a message each time it gives up after 1000 rejected cases and restarts with a new generator
-}
debugRGP:: Int -> IO()
debugRGP brdSize = do
    gen <- newStdGen
    let (fin, g') = randomR (0,brdSize-1) gen
    try g' fin
    where len = trackLength brdSize - 1 -- accounts for finish square included at start
          possibles ps = filter (accept brdSize) $ filter finishing $ take 1000 ps
          try g fin = case possibles $ randGrowTrack g brdSize len [[(fin,0)]] of
                        [] -> do putStrLn "none found in 1000 paths, retrying"
                                 let (g'',_) = split g
                                 try g'' fin
                        other -> putStrLn ("Accepted path: " ++ show (head other))

                                                
-- | debug tool used to look for faults in pathToTrack and trackToPath (tToP)
-- when generating solutionboards (with randGenSamples)
debugSamples brdSize n = do
    gen <- newStdGen
    loop gen n where
        loop g 0 = putStrLn "all ok"
        loop g m = do
         let (gen1,gen2) = split g
         let p = randGenPath gen1 brdSize (trackLength brdSize)
         putStrLn ("Path: " ++ show p)
         case tToP (head p) (pathToTrack p) (head (reverse p)) S [] of
             Nothing -> putStrLn ("tToP Failed with:"++show p) 
             Just p' -> if p==p'
                        then do putStrLn ("path ok: "++show(n-m+1)) 
                                loop gen2 (m-1)
                        else do putStrLn ("Failed equality path:" ++ show p)
                                putStrLn ("and after" ++ show p')

-- | DEBUG tool ---- Tracing debug version of trackToPath returning a report string
traceTrackToPath :: Board -> [Char]
traceTrackToPath b = trace (start b) (track b) (finish b) S [] where
    trace _ [] _ _ path = "Failed No track left "++ show path
    trace start [(p,sq')] sq m path = 
        if sq'==start && p==mkPiece m W 
        then "Finished: "++ show (Just (sq:path)) 
        else "Failed Start check: "++ show (p,sq') ++ " Path:" ++ show path  
    trace start trs sq  m path = case findInTrack trs sq of
        Nothing -> " >>> Missing in Track: " ++ show sq ++ " not in " ++ show trs
        Just t -> trace start (trs\\[t]) sq' m' (sq:path)
                          where (m',sq') = nextSq m t


-- | debug tool to show status of a goal
printGoal :: Goal -> IO ()
printGoal ([], []) = putStrLn "No more solutions"
printGoal (b:more,solns) = do print $ seeBoard b
                              printGoal (more,solns)
printGoal ([], s:solns)  = do putStrLn ("Solution " ++ show (length solns+1))
                              print $ seeSolution s
                              printGoal ([],solns)

               
-- | tactic debug tool
tacticFromGame:: [Char] -> Tactic -> Game -> IO()
tacticFromGame tacticname tactic g = do
    putStrLn "Game"
    print $ seeGame g
    tacticFromGoal tacticname tactic (startGoal g)

-- | tactic debug tool
tacticFromBoard:: [Char] -> Tactic -> Board -> IO()
tacticFromBoard tacticname tactic b = do
    putStrLn "Starting Board"
    print $ seeBoard b
    tacticFromGoal tacticname tactic ([b],[])

-- | tactic debug tool
tacticFromGoal:: [Char] -> Tactic -> Goal -> IO()
tacticFromGoal tacticname tactic goal = do
    putStrLn ("Tactic applied: " ++ tacticname)
    putStrLn "--------Results--------"
    case applyTac tactic goal of
        Nothing -> putStrLn "Nothing"
        Just gl -> do putStrLn ("Boards unsolved:     " ++ show (length (fst gl)))
                      putStrLn ("Number of Solutions: " ++ show (length (snd gl)))
                      putStrLn  "-----------------------"
                      printGoal gl
                      putStrLn "Current Board: "
                      case gl of 
                        ((b1:_),_) -> do print $ seeBoard b1
                                         print $ show b1 -- to record result board if needed
                        _         -> putStrLn "-- No current board --"

-- | debug tool to report on all dots on a board
inspectDots:: Board -> IO ()
inspectDots b = putStrLn $ concatMap (inspectDot b) (dots b)

-- | debug tool to show types of neighbours of a dot
inspectDot:: Board -> Square -> String
inspectDot b dot =
    let size = boardSize b
        nbs = filter (onBoard size) (extend dot)
        tracknbs = mapMaybe (findInTrack (track b)) nbs
        contrackSqs = map snd (filter connecting tracknbs) -- squares with connecting track to dot
        connecting n = dot `elem` (map snd (findends n))
        ndots = intersect nbs (dots b)
        nukns = intersect nbs (unknowns b)
    in ("Dot=" ++ show dot ++
        "\nNbs=" ++ show nbs ++
        "\ncontrackSqs=" ++ show contrackSqs ++
        "\ntracknbs=" ++ show tracknbs ++
        "\nndots=" ++ show ndots ++
        "\nnunks=" ++ show nukns++ "\n\n")

-- | debug tool to see results of rSelect (integer argument  = track length)
testSelect::Int -> IO[Int]
testSelect n = do
    gen <- newStdGen
    return (rSelect gen n)

-- | debug tool to see results of randGenPath given Board size
testPath::Int -> IO(Path)
testPath brdSize = do
    gen <- newStdGen
    return (randGenPath gen brdSize (trackLength brdSize))

{-
-- needs Rank2types
rtest:: (forall g. (RandomGen g) => g -> a -> b) -> a -> IO(b)
rtest f a = do
    gen <- newStdGen
    return (f gen a)
-}

