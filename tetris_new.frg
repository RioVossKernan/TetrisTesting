#lang forge/temporal

option max_tracelength 10
option min_tracelength 2

option run_sterling "tetris_vis.js"

//The possible rows/cols:
fun Rows : Set {
    0 + 1 + 2 + 3 + 4
}
fun Cols : Set {
    0 + 1 + 2 + 3 + 4
}
fun MaxX : Int { 4 }
fun MaxY : Int { 4 }
fun MinX : Int { 0 }
fun MinY : Int { 0 }

fun above[y : Rows] : Int { add[1,y] }
fun below[y : Rows] : Int { add[-1,y] }

one sig Board {
    var tiles : set Int -> Int  // x,y coords
}

pred wellformed {
    //values field maps to only the values within row,col
    always {
        all i: Int | {
            (i not in Cols) => (i not in (Board.tiles).Int)
            (i not in Rows) => (i not in Int.(Board.tiles))
        }
    }
}

pred init {
    no tiles
    //Board.tiles = Cols -> (0 + 1)
}

pred isFloor[x,y: Int] {
    y = MinY or //update is we change board size
    (x->below[y]) in Board.tiles //check if space below is on the board
}

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

pred doNothing {
    Board.tiles' = Board.tiles
}

pred moveIsPossible {
    some x : Cols, y : Rows | {
        add1x2_isPossible[x,y]
    }
}

pred clearIsPossible {
    some y : Rows | {
        (Board.tiles).y = Cols
    }
}
pred clearRow[y : Rows] {
    all r : Rows | {
        (r < y) => Board.tiles'.r = Board.tiles.r 
        (r >= y) => Board.tiles'.r = Board.tiles.(above[r])
    }
}
pred clear{
    one y : Rows | {
        (Board.tiles).y = Cols
        clearRow[y]
    }
}

pred addPiece{
    add1x2
}

pred delta {
    clearIsPossible => clear
    else
    addPiece
}

pred traces {
    wellformed
    init
    delta until always doNothing
}

run {
    traces 
    eventually clearIsPossible
} for exactly 4 Int