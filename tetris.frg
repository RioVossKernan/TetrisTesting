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
    Board.values[Int][Int] = Empty
}

//adding a 1x2 block
pred add1by2 {
    some col : cols, row1, row2 : rows | {
        row2 = add[1, row1]
        //check thats its empty now
        Board.values[row1,col] = Empty 
        Board.values[row2,col] = Empty
        //check thats its full in the next state
        Board.values'[row1,col] = Filled 
        Board.values'[row2,col] = Filled
        //check that everything else stayed the same
        Board.values - (row1->col->Empty + row2->col->Empty) = Board.values' - (row1->col->Filled + row2->col->Filled)
    }  
}

run {
    init
    wellformed
    add1by2
}