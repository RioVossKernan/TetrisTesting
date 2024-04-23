#lang forge/temporal

option max_tracelength 10
option min_tracelength 5

option run_sterling "tetris_vis.js"

abstract sig TileStatus {}
one sig Filled extends TileStatus {}
one sig Empty extends TileStatus {}

//The possible rows: currently 0-4
fun rows : Set {
    0 + 1 + 2 + 3 + 4
}
//The possible cols: currently 0-4
fun cols : Set {
    0 + 1 + 2 + 3 + 4
}

//Board
one sig Board {
    var values: pfunc Int -> Int -> TileStatus // (row, col) -> value
}

pred wellformed {
    //values field maps to all and only the values within row,col
    always {
        Board.values.TileStatus = rows -> cols
    }
}

pred init {
    //at init, all values map to empty
    Board.values[rows][cols] = Empty
}

pred is_floor[row, col: Int] {
    (row = 0 or Board.values[add[-1, row], col] = Filled)
    Board.values[row, col] = Empty
}

pred add1by2_possible[col: cols, row1, row2: rows] {
    row2 = add[1, row1]
    is_floor[row1, col]
    Board.values[row2, col] = Empty
}

//adding a 1x2 block
pred add1by2 {
    some col : cols, row1, row2 : rows | {
        //check thats its empty now
        add1by2_possible[col, row1, row2]
        //check thats its full in the next state
        Board.values'[row1,col] = Filled 
        Board.values'[row2,col] = Filled
        //check that everything else stayed the same
        Board.values - (row1->col->Empty + row2->col->Empty) = Board.values' - (row1->col->Filled + row2->col->Filled)
    }  
}

//adding a 2x1 block
pred add2by1 {
    some col1, col2 : cols, row : rows | {
        col2 = add[1, col1]
        //check thats its empty col
        is_floor[row, col1]
        is_floor[row, col2]
        //check thats its full in the next state
        Board.values'[row,col1] = Filled 
        Board.values'[row,col2] = Filled
        //check that everything else stayed the same
        Board.values - (row->col1->Empty + row->col2->Empty) = Board.values' - (row->col1->Filled + row->col2->Filled)
    }  
}

pred add2by2 {
    some col1, col2: cols, row1, row2: rows | {
        col2 = add[1, col1]
        row2 = add[1, col2]
        // check it's empty
        is_floor[row1, col1]
        is_floor[row2, col2]
        Board.values[row2, col1] = Empty
        Board.values[row2, col2] = Empty
        // check they're full in next state
        Board.values'[row1, col1] = Filled
        Board.values'[row1, col2] = Filled
        Board.values'[row2, col1] = Filled
        Board.values'[row2, col2] = Filled
        // check everything else is the same
        Board.values - ((row1 + row2)->(col1+col2)->Empty) = Board.values' - ((row1 + row2)->(col1+col2)->Filled)
    }
}

pred movepossible {
    // some col: cols, row1, row2: rows | {
    //     add1by2_possible[col, row1, row2]
    // }
    false
}

-- keep the board the same
pred doNothing {
    -- guard
    not movepossible

    Board.values = Board.values'
}

-- any transition
pred delta { 
    add1by2 or
    // add2by1 or
    // add2by2 or
    doNothing
}

pred lasso {
    init
    wellformed
    always { delta }
}

run {
    lasso
}