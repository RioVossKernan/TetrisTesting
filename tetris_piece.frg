#lang forge

fun MaxX : Int { 3 }
fun MaxY : Int { 3 }

one sig Board {
    tiles : set Int -> Int  // x,y coords
}

pred wellformed {
    all x : Int, y : Int | {{x->y in Board.tiles} implies 0 <= x && x < MaxX && 0 <= y && y < MaxY}
}

pred size3 {
    #Board.tiles = 3
}

fun add1[x : Int] : Int { add[1,x] }
fun sub1[x : Int] : Int { add[-1,x] }

pred contiguous {
    all x : Int, y : Int | {{x->y in Board.tiles} implies 
        (add1[x]->y in Board.tiles) or (sub1[x]->y in Board.tiles) or (x->add1[y] in Board.tiles) or (x->sub1[y] in Board.tiles)}
}

run {
    wellformed
    size3
    contiguous
}