#lang forge/temporal

option max_tracelength 15
option min_tracelength 8

option run_sterling "tetris_vis.js"

//Board is represented as a set of (Int, Int) coords.
//If a pos is in the set, that tile is filled on the board.
one sig Board {
    var tiles : set Int -> Int  // x,y coords
}

-------------- HELPER FUNCTIONS --------------

//The possible rows/cols:
fun Rows : Set { 0 + 1 + 2 + 3 + 4 + 6 + 7 + 8 + 9}
fun Cols : Set { 0 + 1 + 2 + 3 + 4 + 6 + 7 + 8 + 9}
//Values for reference in preds (kinda like a global const variable)
fun MaxX : Int { 9 }
fun MaxY : Int { 9 }
fun MinX : Int { 0 }
fun MinY : Int { 0 }
//Above and Below a given row
fun above[y : Rows] : Int { add[1,y] }
fun below[y : Rows] : Int { add[-1,y] }
fun left[x : Rows] : Int { add[-1,x] }
fun right[x : Rows] : Int { add[1,x] }

-------------- CORE PREDS --------------

//tiles must be in bounds of Rows,Cols
pred wellformed {
    always {
        all i: Int | {
            (i not in Cols) => (i not in (Board.tiles).Int)
            (i not in Rows) => (i not in Int.(Board.tiles))
        }
    }
}

//is pos (x,y) either on the grid-bottom or on another block
pred isFloor[x,y: Int] {
    y = MinY or 
    (x->below[y]) in Board.tiles
}

-------------- PIECES --------------

pred noPieceAtOrAbove[x : Cols, y : Rows] {
    no y2 : Rows | {
        y2 >= y
        (x->y2) in Board.tiles
    }
}

// |‾‾|
// |__|  <-  x,y
pred add1x2_isPossible[x : Cols, y : Rows] {
    --On Floor
    isFloor[x,y]
    --Piece fits
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
}
pred add1x2 {
    some x : Cols, y : Rows | {
        add1x2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]))
    }
}

// |‾‾‾‾|  <- x,y
//  ‾‾‾‾
pred add2x1_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y]
    --Piece fits
    noPieceAtOrAbove[x,y]
    noPieceAtOrAbove[left[x],y]
    --Stay in bounds
    left[x] in Cols
}
pred add2x1 {
    some x : Cols, y : Rows | {
        add2x1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y))
    }
}

--- SMALL L MOVES ---
pred addSmallL{
    addSmallL1 or
    addSmallL2 or
    addSmallL3 or
    addSmallL4
}

// |‾‾‾‾|
//  ‾|__|  <-  x,y
pred addSmallL1_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],above[y]]    
    --Piece fits
    noPieceAtOrAbove[left[x],above[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    left[x] in Cols
}
pred addSmallL1 {
    some x : Cols, y : Rows | {
        addSmallL1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (left[x]->above[y]))
    }
}

// |‾‾|_
// |____|  <-  x,y
pred addSmallL2_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y]    
    --Piece fits
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    left[x] in Cols
}
pred addSmallL2 {
    some x : Cols, y : Rows | {
        addSmallL2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[x]->above[y]))
    }
}

//        |‾‾‾‾|
// x,y -> |__|‾ 
pred addSmallL3_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[right[x],above[y]]    
    --Piece fits
    noPieceAtOrAbove[right[x],above[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    right[x] in Cols
}
pred addSmallL3 {
    some x : Cols, y : Rows | {
        addSmallL3_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (right[x]->above[y]))
    }
}

//  _|‾‾|
// |____|  <-  x,y
pred addSmallL4_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y]    
    --Piece fits
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    left[x] in Cols
}
pred addSmallL4 {
    some x : Cols, y : Rows | {
        addSmallL4_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (left[x]->y))
    }
}

--------- J Moves -------
pred addJ{
    addJ1 or
    addJ2 or
    addJ3 or
    addJ4
}

//    |‾‾|
//  __|  |
// |_____|  <-  x,y
pred addJ1_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y]
    --Piece fits
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[above[y]] in Rows
    left[x] in Cols
}
pred addJ1 {
    some x : Cols, y : Rows | {
        addJ1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (x->above[y]) + (x->above[above[y]]))
    }
}

// |‾‾|___
// |______|  <-  x,y
pred addJ2_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y] or isFloor[left[left[x]],y]
    --Piece fits
    noPieceAtOrAbove[left[left[x]],y]
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    left[left[x]] in Cols
}
pred addJ2 {
    some x : Cols, y : Rows | {
        addJ2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[left[x]]->y) + (left[left[x]]->above[y]))
    }
}

// |‾‾‾‾‾|
// |  |‾‾  
// |__| <-  x,y
pred addJ3_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[right[x],above[above[y]]]
    --Piece fits
    noPieceAtOrAbove[right[x],above[above[y]]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[above[y]] in Rows
    right[x] in Cols
}
pred addJ3 {
    some x : Cols, y : Rows | {
        addJ3_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (x->above[above[y]]) + (right[x]->above[above[y]]))
    }
}

// |‾‾‾‾‾‾|
//  ‾‾‾|__| <-  x,y
pred addJ4_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],above[y]]or isFloor[left[left[x]],above[y]]
    --Piece fits
    noPieceAtOrAbove[left[left[x]],above[y]]
    noPieceAtOrAbove[left[x],above[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    left[left[x]] in Cols
}
pred addJ4 {
    some x : Cols, y : Rows | {
        addJ4_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (left[x]->above[y]) + (left[left[x]]->above[y]))
    }
}

--------- L Moves -------
pred addL {
    addL1 or
    addL2 or
    addL3 or
    addL4
}

// |‾‾|
// |  |__
// |_____|<-  x,y
pred addL1_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x], y]
    --Piece fits
    noPieceAtOrAbove[left[x], y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[above[y]] in Rows
    left[x] in Cols
}
pred addL1 {
    some x : Cols, y : Rows | {
        addL1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[x]->above[y]) + (left[x]->above[above[y]]))
    }
}

//  ___|‾‾|
// |______|  <-  x,y
pred addL2_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y] or isFloor[left[left[x]],y]
    --Piece fits
    noPieceAtOrAbove[left[left[x]],y]
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    left[left[x]] in Cols
}
pred addL2 {
    some x : Cols, y : Rows | {
        addL2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[left[x]]->y) + (x->above[y]))
    }
}

// |‾‾‾‾‾|
//  ‾‾|  |  
//    |__| <-  x,y
pred addL3_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],above[above[y]]]
    --Piece fits
    noPieceAtOrAbove[left[x],above[above[y]]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[above[y]] in Rows
    left[x] in Cols
}
pred addL3 {
    some x : Cols, y : Rows | {
        addL3_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (x->above[above[y]]) + (left[x]->above[above[y]]))
    }
}

// |‾‾‾‾‾‾|<-  x,y
// |__|‾‾‾
pred addL4_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y] or isFloor[left[left[x]],below[y]]
    --Piece fits
    noPieceAtOrAbove[left[left[x]],below[y]]
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    below[y] in Rows
    left[left[x]] in Cols
}
pred addL4 {
    some x : Cols, y : Rows | {
        addL4_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[left[x]]->below[y]) + (left[left[x]]->y))
    }
}

--------- 2x2 Moves -------

// |‾‾‾‾|
// |____|  <-  x,y
pred add2x2_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y]    
    --Piece fits
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    left[x] in Cols
}
pred add2x2 {
    some x : Cols, y : Rows | {
        add2x2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (left[x]->y) + (left[x]->above[y]))
    }
}

--------- Z Moves ---------
pred addZ{
    addZ1 or
    addZ2
}

// |‾‾‾‾|__
//  ‾‾|____|  <-  x,y
pred addZ1_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y] or isFloor[left[left[x]],above[y]]  
    --Piece fits
    noPieceAtOrAbove[left[left[x]],above[y]]
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    left[left[x]] in Cols
}
pred addZ1 {
    some x : Cols, y : Rows | {
        addZ1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[x]->above[y]) + (left[left[x]]->above[y]))
    }
}

//       |‾‾|
//    |‾‾   |  <-  x,y
//    |__|‾‾ 
pred addZ2_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],below[y]]
    --Piece fits
    noPieceAtOrAbove[left[x],below[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[y] in Rows
    below[y] in Rows
    left[x] in Cols
}
pred addZ2 {
    some x : Cols, y : Rows | {
        addZ2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[x]->below[y]) + (x->above[y]))
    }
}

-------- S Moves ---------
pred addS{
    addS1 or
    addS2
}
//  __|‾‾‾‾| <-  x,y
// |____|‾‾  
pred addS1_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],below[y]] or isFloor[left[left[x]],below[y]]
    --Piece fits
    noPieceAtOrAbove[left[left[x]],below[y]]
    noPieceAtOrAbove[left[x],below[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    below[y] in Rows
    left[left[x]] in Cols
}
pred addS1 {
    some x : Cols, y : Rows | {
        addS1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[x]->below[y]) + (left[left[x]]->below[y]))
    }
}

// |‾‾|__
// |__   |
//    |__| <-  x,y
pred addS2_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],above[y]]
    --Piece fits
    noPieceAtOrAbove[left[x],above[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[above[y]] in Rows
    left[x] in Cols
}
pred addS2 {
    some x : Cols, y : Rows | {
        addS2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->above[above[y]]) + (x->above[y]) + (left[x]->above[y]))
    }
}

-------- I Moves ---------
pred addI{
    addI1 or
    addI2
}

// |‾‾‾‾‾‾‾‾‾‾| <-  x,y
//  ‾‾‾‾‾‾‾‾‾‾  
pred addI1_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y] or isFloor[left[left[x]],y] or isFloor[left[left[left[x]]],y]
    --Piece fits
    noPieceAtOrAbove[left[left[left[x]]],y]
    noPieceAtOrAbove[left[left[x]],y]
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    left[left[left[x]]] in Cols
}
pred addI1 {
    some x : Cols, y : Rows | {
        addI1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[left[x]]->y) + (left[left[left[x]]]->y))
    }
}

// |‾‾|
// |  |
// |  | 
// |__| <-  x,y
pred addI2_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[x,above[y]] or isFloor[x,above[above[y]]] or isFloor[x,above[above[above[y]]]]
    --Piece fits
    noPieceAtOrAbove[x,above[above[above[y]]]]
    noPieceAtOrAbove[x,above[above[y]]]
    noPieceAtOrAbove[x,above[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[above[above[y]]] in Rows
}
pred addI2 {
    some x : Cols, y : Rows | {
        addI2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (x->above[above[y]]) + (x->above[above[above[y]]]))
    }
}

-------- T Moves ---------
pred addT{
    addT1 or
    addT2 or
    addT3 or
    addT4
}
// |‾‾‾‾‾‾| <-  x,y
//  ‾|__|‾  
pred addT1_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],below[y]] or isFloor[left[left[x]],y]
    --Piece fits
    noPieceAtOrAbove[left[left[x]],y]
    noPieceAtOrAbove[left[x],below[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    below[y] in Rows
    left[left[x]] in Cols
}
pred addT1 {
    some x : Cols, y : Rows | {
        addT1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->below[y]) + (left[x]->y) + (left[left[x]]->y))
    }
}

// |‾‾|__
// |   __|  <-  x,y
// |__|
pred addT2_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],below[y]]
    --Piece fits
    noPieceAtOrAbove[left[x],below[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    below[y] in Rows
    above[y] in Rows
    left[x] in Cols
}
pred addT2 {
    some x : Cols, y : Rows | {
        addT2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->below[y]) + (left[x]->above[y]) + (left[x]->y))
    }
}

//  __|‾‾|
// |__   |  
//    |__| <-  x,y
pred addT3_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],above[y]]
    --Piece fits
    noPieceAtOrAbove[left[x],above[y]]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    above[above[y]] in Rows
    left[x] in Cols
}
pred addT3 {
    some x : Cols, y : Rows | {
        addT3_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->above[y]) + (x->above[y]) + (x->above[above[y]]))
    }
}

//  _|‾‾|_
// |______|  <-  x,y
pred addT4_isPossible[x,y : Int] {
    --On Floor
    isFloor[x,y] or isFloor[left[x],y] or isFloor[left[left[x]],y]
    --Piece fits
    noPieceAtOrAbove[left[x],y]
    noPieceAtOrAbove[left[left[x]],y]
    noPieceAtOrAbove[x,y]
    --Stay in bounds
    left[left[x]] in Cols
    above[y] in Rows
}
pred addT4 {
    some x : Cols, y : Rows | {
        addT4_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[left[x]]->y) + (left[x]->above[y]))
    }
}
-------------- TRANSITIONS --------------

//!!!!  WHEN YOU WRITE A NEW PIECE PRED PUT IT HERE !!!!
pred addPiece {
    //add1x2 or
    //add2x1 or
    //addSmallL or 

    //These are the official tetris pieces
    add2x2 or
    addL or
    addJ or 
    addS or
    addZ or 
    addI or 
    addT
}

pred NonRepeatingAddPiece{
    addPiece

    // add2x2 => {
    //     next_state{not add2x2}
    //     next_state{next_state{not add2x2}}
    //     next_state{next_state{next_state{not add2x2}}}
    // }
}

pred doNothing {
    Board.tiles' = Board.tiles
}

//When a row is filled, clear it then go back to adding pieces
pred delta {
    clearIsPossible => clear
    else
    addPiece
}

pred delta_non_repeating {
    clearIsPossible => clear
    else
    NonRepeatingAddPiece
}

//GAMEOVER
pred gameover {
    all x: Cols, y: Rows | {
        not add1x2_isPossible[x,y]
        not add2x2_isPossible[x,y]
        not add2x1_isPossible[x,y]
        not addL1_isPossible[x,y]
        not addL2_isPossible[x,y]
        not clearIsPossible 
    }
    not clearIsPossible
}

-------------- CLEAR PREDS --------------

pred clearIsPossible {
    some y : Rows | {
        (Board.tiles).y = Cols
    }
}

//row is full now, then in next state all rows below stay the same and rows above move down
pred clearRow[y : Rows] {
    (Board.tiles).y = Cols
    all r : Rows | {
        (r < y) => Board.tiles'.r = Board.tiles.r 
        (r >= y) => Board.tiles'.r = Board.tiles.(above[r])
    }
}

pred clear{
    some y : Rows | {
        clearRow[y]
    }
}

-------------- TRACES --------------
pred init {
    no tiles
}

-- gameplay eventually halts
pred finite_trace {
    wellformed
    init
    delta until always doNothing
}

pred gameover_trace {
    wellformed
    init 
    delta until always gameover 
}

-- Infinite gameplay
pred lasso {
    wellformed
    init
    always delta
}

pred lasso_unique_pieces {
    wellformed
    init
    always delta_non_repeating
}
 
-------------- RUNS --------------
run {
    lasso
} for exactly 5 Int

// run {
//     lasso_unique_pieces
// } for exactly 4 Int
