module Main where


import TracksIO
import TrackDebug
import System.IO
import System.Environment



{-  TO DO
use diagrams to print instead of charpics
-}

-- | default boardSize and number of games to generate
brdSize, numberofgames::Int
brdSize = 8
numberofgames = 4

-- | creates and displays games, then saves games to specified argument file or stdout
main :: IO ()
main = do args <- getArgs
          games <- createGames brdSize numberofgames
          displayGames games
          case args of
            []     -> putStrLn (gameLines games)
            [file] -> do appendFile file (gameLines games)
                         putStrLn ("Games saved to: " ++ file)


