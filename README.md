# traintracks

## Train Track Puzzles - Chris Reade 2021

This software written in Haskell contains a random generator for train track puzzles and also a solver.
The solver is necessary to check that a game/puzzle instance has unique solutions and this
is the more interesting part of the code.

A simple ascii graphics display is available for debugging, testing and trying out the games generated.

The solver is written using a type for tactics and tactic combinators.
The tactic type is not as general as for e.g. theorem proving tactics, but is simplified for writing short steps in progressing towards a solution. 

### Main
`main` takes an optional filepath argument
It creates games and displays them in pairs then
saves the games in re-readable format appended to specified filepath or to stdout
Default is board size 8 and 4 games at a time

### TrainTracks
Contains the types for boards, track, games, solutions, etc and generators `randGenSamples`, `randGenGames`
### TrackSolve
Contains the tactics and tactic combinators as well as goal type - solver is the main tactic.
It also contains the main `generateGames` which checks generated games for unique solutions using the solver.
### PuzzlePics
Contains code for simple ascii displays of puzzles (using Charpics)
### TracksIO
Contains some IO functions including createGames, saveGames, readGames, displayGames
### TrackDebug
Contains a few functions used in debugging
## Technicality
A major problem with earlier version was resolved.
Very unpredictable timing resulted from randomness.  This turned out to be in the game generator.
Specifically `randGenPath` could, on occasion, generate huge numbers of unacceptable paths. To resolve this,
it now generates a block of 1000 paths to check at a time and, if none are acceptable, it starts again with a new random generator.

