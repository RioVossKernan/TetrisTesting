# TetrisTesting
Final Project for CS1710 at Brown University

This project explores Tetris using the Forge language to model the system/logic behind the game using states and transitions. The core logic behind the game revolves around several components: wellformed, isFloor, addPiece, delta, clear, and gameover. 

wellformed - checks whether the game state is valid (tiles must be in bounds of the game board)

isFloor - checks whether a position x,y is part of the "floor", tiles that are already solidified or the bottom of the grid 

addPiece - adds one of the available Tetris pieces: L, J, Z, T, S, I 2x2 

delta - keeps the game running, clears if possible otherwise add another piece

clear - clears all rows at the bottom that are filled just like the original game

gameover - when neither addPiece or clear are possible anymore

Tradeoffs/Limitations: We were very extensive with simulating all the various possible Tetris pieces as well as implementing a visualizer to see the transitions graphically in real time. However we did not simulate "falling" like the actual game but rather "stamping" pieces onto the board when transitioning between states. This made the model much easier to implement with Temporal Forge and reduces the computation needed. We also chose to simulate the game on a smaller board since the game space of the original sized game is way to large to run in reasonable time on our local machines. 

Goals/Achievements: We originally planned to have a open-ended attempt at modeling the game of Tetris, hoping to simulate all the original game logic and all the pieces. We managed to simulate most of the game as well as modeling each of the possible "rotations" of each of the original game pieces by using separate versions of the orignal predicate. The rotations were a bonus to our original goal of just having a functional game with pieces. We wanted to attempt simulating a larger game and with the "falling" mechanic but the computation time was too great for those additional complexities. 

Visualization: We have our own custom visualizer for our game and when running the model we can see each transition as a "screenshot" of the tetris game when another piece "lands" onto the "floor", we can imagine this as a piece being "stamped" instead of falling to simplify the transition logic between game states. An example instance of our model is running game_over trace, which will show a random sequence of pieces being placed until eventually the game is over. 

Testing: We were extensive with our testing and proved/verified many properties of our game using text expects. All our tests and properties are in tetris.tests and some include: always able to win/lose regardless of sequence, going back to an empty board after filling pieces, fewest number of pieces needed to lose the game. 

Collaborators: Rio Voss-Kernan, Jason Eveleth, Jonathan Dou



