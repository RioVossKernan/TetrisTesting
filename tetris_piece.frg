#lang forge

fun Rows : Set { 0 + 1 + 2}
fun Cols : Set { 0 + 1 + 2}
//Values for reference in preds (kinda like a global const variable)
fun MaxX : Int { 3 }
fun MaxY : Int { 3 }
fun MinX : Int { 0 }
fun MinY : Int { 0 }
//Above and Below a given row

one sig Board {
    tiles : set Int -> Int  // x,y coords
}

pred wellformed {
    all x : Int, y : Int | {{x->y in Board.tiles} implies 0 <= x && x < MaxX && 0 <= y && y < MaxY}
}

pred size4 {
    #Board.tiles = 4
}

fun add1[x : Int] : Int { add[1,x] }
fun sub1[x : Int] : Int { add[-1,x] }


sig Position {
    x: one Int,
    y: one Int
}

pred inBounds[p : Position] {
    0 <= p.x
    p.x < MaxX
    0 <= p.y
    p.y < MaxY
}

pred contiguous {
    all x1, y1: Int {
        {x1 in Cols
        y1 in Rows} => {some p: Position | p.x = x1 and p.y = y1}
    }
    all p1 : Position, p2 : Position | {
        {p1.x->p1.y in Board.tiles
        p2.x->p2.y in Board.tiles
        } implies p1->p2 in {^{p3: Position, p4: Position | adjacent[p3,p4]}}
    }
}

pred nextToEachOther[x1 : Int, y1 : Int, x2 : Int, y2 : Int] {
    {add1[x1] = x2 and y1 = y2 or
    sub1[x1] = x2 and y1 = y2 or
    x1 = x2 and add1[y1] = y2 or
    x1 = x2 and sub1[y1] = y2}
    x1->y1 in Board.tiles and x2->y2 in Board.tiles
}

pred adjacent[p1 : Position, p2 : Position] {
    nextToEachOther[p1.x, p1.y, p2.x, p2.y]
}

pred oneTileOnBottom {
    some x : Int | x->0 in Board.tiles
}

pred L1_0 {
    (0->2 + 0->1 + 0->0 + 1->0) = Board.tiles
}

pred L1_1 {
    (1->2 + 1->1 + 1->0 + 2->0) = Board.tiles
}

pred L2 {
    (0->0 + 1->0 + 2->0 + 2->1) = Board.tiles
}

pred L3_1 {
    (2->0 + 2->1 + 2->2 + 1->2) = Board.tiles
}

pred L3_0 {
    (1->0 + 1->1 + 1->2 + 0->2) = Board.tiles
}

pred L4 {
    (0->1 + 1->1 + 2->1 + 0->0) = Board.tiles
}

pred T1 {
    (0->1 + 1->1 + 2->1 + 1->0) = Board.tiles
}

pred T2_0 {
    (0->0 + 0->1 + 0->2 + 1->1) = Board.tiles
}

pred T2_1 {
    (1->0 + 1->1 + 1->2 + 2->1) = Board.tiles
}

pred T3_1 {
    (2->0 + 2->1 + 2->2 + 1->1) = Board.tiles
}

pred T3_0 {
    (1->0 + 1->1 + 1->2 + 0->1) = Board.tiles
}

pred T4 {
    (0->0 + 1->0 + 2->0 + 1->1) = Board.tiles
}

pred J1_1 {
    (1->0 + 2->0 + 2->1 + 2->2) = Board.tiles
}

pred J1_0 {
    (0->0 + 1->0 + 1->1 + 1->2) = Board.tiles
}

pred J2 {
    (0->0 + 1->0 + 2->0 + 0->1) = Board.tiles
}

pred J3_1 {
    (1->0 + 1->1 + 1->2 + 2->2) = Board.tiles
}

pred J3_0 {
    (0->0 + 0->1 + 0->2 + 1->2) = Board.tiles
}

pred J4 {
    (0->1 + 1->1 + 2->1 + 2->0) = Board.tiles
}

pred O_1 {
    (1->0 + 1->1 + 2->0 + 2->1) = Board.tiles
}

pred O_0 {
    (0->0 + 0->1 + 1->0 + 1->1) = Board.tiles
}

pred S2_1 {
    (2->0 + 2->1 + 1->1 + 1->2) = Board.tiles
}

pred S2_0 {
    (1->0 + 1->1 + 0->1 + 0->2) = Board.tiles
}

pred S1 {
    (0->0 + 1->0 + 1->1 + 2->1) = Board.tiles
}

pred Z1 {
    (0->1 + 1->1 + 1->0 + 2->0) = Board.tiles
}

pred Z2_0 {
    (0->0 + 0->1 + 1->1 + 1->2) = Board.tiles
}

pred Z2_1 {
    (1->0 + 1->1 + 2->1 + 2->2) = Board.tiles
}

run {
    wellformed
    size4
    contiguous
    oneTileOnBottom

    not L1_0
    not L1_1
    not L2
    not L3_0
    not L3_1
    not L4

    not T1
    not T2_0
    not T2_1
    not T3_1
    not T3_0
    not T4

    not J1_1
    not J1_0
    not J2
    not J3_1
    not J3_0
    not J4

    not O_1
    not O_0

    not S1
    not S2_0
    not S2_1

    not Z1
    not Z2_0
    not Z2_1
} for 9 Position