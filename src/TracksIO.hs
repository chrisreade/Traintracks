module TracksIO where
    
import TrainTracks(Game)
import TrackSolve(generateGames)
import PuzzlePics(seeGames)
import System.Random (newStdGen)
import Data.List (intercalate)

{- | createGames
Main top level function used to generate a given number of random games 
(using the solver to ensure unique solutions)
Requires board size first then number of games
-}
createGames :: Int -> Int -> IO[Game]
createGames brdSize number = do
    gen <- newStdGen
    return (generateGames gen brdSize number)

-- | display games (in pairs) 
displayGames:: [Game] -> IO()
displayGames games = print $ seeGames games

-- | convert games to a string with newlines after each
gameLines:: [Game] -> String
gameLines games = intercalate "\n" (map show games)++"\n"

-- | append games to a given text file
saveGames:: FilePath -> [Game] -> IO()
saveGames filepath games = appendFile filepath (gameLines games)

-- | append single game to a given text file
saveGame:: FilePath -> Game -> IO()
saveGame filepath game = do
    appendFile filepath (gameLines [game])

readGameFrom :: FilePath -> IO(Game)
readGameFrom filepath = do
    contents <- readFile filepath
    case reads contents of
        [] -> error ("no game parsed from " ++ filepath)
        [(g,more)] -> return g

readGamesFrom :: FilePath  -> IO[Game]
readGamesFrom filepath = do
    contents <- readFile filepath
    return (parseGames contents)

fetchGamesFrom :: FilePath  -> Int -> Int -> IO[Game]
fetchGamesFrom filepath n m = do
    contents <- readFile filepath
    return (take m $ drop n $ parseGames contents)

parseGames:: [Char] -> [Game]
parseGames s = case reads s of
               [] -> []
               [(g,more)] -> g: parseGames more
    
printGamesFrom:: FilePath -> Int -> IO()              
printGamesFrom filepath n = do
    games <- readGamesFrom filepath
    displayGames $ take n games


    