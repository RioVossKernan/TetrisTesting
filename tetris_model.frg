#lang forge/temporal

option max_tracelength 10
option min_tracelength 2

option run_sterling "tetris_vis.js"

//Board is represented as a set of (Int, Int) coords.
//If a pos is in the set, that tile is filled on the board.
one sig Board {
    var tiles : set Int -> Int  // x,y coords
}

-------------- HELPER FUNCTIONS --------------

//The possible rows/cols:
fun Rows : Set { 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 }
fun Cols : Set { 0 + 1 + 2 + 3 + 4 + 5 + 6 + 7 }
//Values for reference in preds (kinda like a global const variable)
fun MaxX : Int { 7 }
fun MaxY : Int { 7 }
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

// |‾‾|
// |__|  <-  x,y
pred add1x2_isPossible[x,y : Int] {
    isFloor[x,y]
    (x->y) not in Board.tiles
    (x->above[y]) not in Board.tiles
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
    isFloor[x,y]
    isFloor[left[x],y]
    (x->y) not in Board.tiles
    (left[x]->y) not in Board.tiles
    left[x] in Cols
}
pred add2x1 {
    some x : Cols, y : Rows | {
        add2x1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y))
    }
}

// |‾‾‾‾|
// |____|  <-  x,y
pred add2x2_isPossible[x,y : Int] {
    isFloor[x,y]
    isFloor[left[x],y]
    (x->y) not in Board.tiles
    (x->above[y]) not in Board.tiles
    (left[x]->y) not in Board.tiles
    (left[x]->above[y]) not in Board.tiles
    above[y] in Rows
    left[x] in Cols
}
pred add2x2 {
    some x : Cols, y : Rows | {
        add2x2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (left[x]->y) + (left[x]->above[y]))
    }
}

// |‾‾‾‾|
//  ‾|__|  <-  x,y
pred addL1_isPossible[x,y : Int] {
    isFloor[x,y]
    (x->y) not in Board.tiles
    (x->above[y]) not in Board.tiles
    (left[x]->above[y]) not in Board.tiles
    above[y] in Rows
    left[x] in Cols
}
pred addL1 {
    some x : Cols, y : Rows | {
        addL1_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (x->above[y]) + (left[x]->above[y]))
    }
}

// |‾‾|_
// |____|  <-  x,y
pred addL2_isPossible[x,y : Int] {
    isFloor[x,y]
    isFloor[left[x],y]
    (x->y) not in Board.tiles
    (left[x]->y) not in Board.tiles
    (left[x]->above[y]) not in Board.tiles
    (right[x]->above[y]) not in Board.tiles
    above[y] in Rows
    left[x] in Cols
}
pred addL2 {
    some x : Cols, y : Rows | {
        addL2_isPossible[x,y]
        Board.tiles' = Board.tiles + ((x->y) + (left[x]->y) + (left[x]->above[y]))
    }
}

-------------- TRANSITIONS --------------

pred addL{
    addL1 or
    addL2
}

//!!!!  WHEN YOU WRITE A NEW PIECE PRED PUT IT HERE !!!!
pred addPiece{
    add1x2 or
    add2x2 or
    add2x1 or
    addL
}

pred NonRepeatingAddPiece{
    addPiece

    add1x2 => {
        next_state{not add1x2}
        next_state{next_state{not add1x2}}
        next_state{next_state{next_state{not add1x2}}}
    }
    add2x2 => {
        next_state{not add2x2}
        next_state{next_state{not add2x2}}
        next_state{next_state{next_state{not add2x2}}}
    }
    add2x1 => {
        next_state{not add2x1}
        next_state{next_state{not add2x1}}
        next_state{next_state{next_state{not add2x1}}}
    }
    addL => {
        next_state{not addL}
        next_state{next_state{not addL}}
        next_state{next_state{next_state{not addL}}}
    }
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
// run {
//     lasso
// } for exactly 4 Int

run {
    lasso_unique_pieces
} for exactly 4 Int

