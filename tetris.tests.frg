#lang forge/temporal

open "tetris_model.frg"

pred delta_L3 { clearIsPossible => clear else addL3 }

pred delta_L1L2 {
    clearIsPossible => clear
    else
    {addL1 or addL2}
}

pred delta_1x2 { clearIsPossible => clear else add1x2 }
pred delta_2x1 { clearIsPossible => clear else add2x1 }
pred delta_2x2 { clearIsPossible => clear else add2x2 }

test suite for wellformed {
    test expect {
        clearIsSat : {
            wellformed
            init
            delta until clear
        } is sat
        remainsWellformed : {
            {wellformed
            init
            delta until clear} => always wellformed
        } is theorem
    }
}

test suite for init {
    // If you have tests for this predicate, put them here!
    test expect {
        // -- technically you can, uncomment to see the counter example
        // cantUseL3ToClear : {
        //     wellformed
        //     init
        //     delta_L3 until clear
        // } is unsat
        cantUseL3ToClearBottomRow : {
            wellformed
            init
            delta_L3 until clearRow[0]
        } is unsat
        clearL1L2 : {
            wellformed
            init
            delta_L1L2 until clear
        } is sat
        clear1x2 : {
            wellformed
            init
            delta_1x2 until clear
        } is sat

        -- require a even x even board
        clear2x1REQUIRES_EVEN : {
            wellformed
            init
            delta_2x1 until clear
        } is sat
        clear2x2REQUIRES_EVEN : {
            wellformed
            init
            delta_2x2 until clear
        } is sat
        getBackToEmptyBoard : {
            wellformed
            init
            delta until clear
            next_state { eventually init }
        } is sat
    }
}

test suite for addPiece {
    test expect {
        addIsSat : {
            wellformed
            init
            addPiece
        } is sat

        cantAddWhenGameOver : {
            wellformed 
            gameover 
            addPiece
        } is unsat 
    }
}

test suite for gameover {
    test expect {
        eventuallyGameOver : {
            wellformed
            init 
            delta until gameover 
        } is sat 

        initNotGameOver : {
            wellformed
            init 
            gameover
        } is unsat
    }
}

test suite for delta_non_repeating {
    test expect {
        delta_non_repeatingTest : {
            wellformed
            init
            always delta_non_repeating until doNothing
        } is sat
    }
}

test expect {
    unPlaceAbleBoard: {
        init_unplace_able_board
        addPiece
    } is unsat
    impossibleBoard2: {
        {init_unplace_able_board
        addPiece} => gameover
    } is theorem
    badBoardEventuallyGameOverAsTheorem: {
        {init_impossible_board
        always {(not gameover) => delta else doNothing}} => eventually gameover
    } is theorem
}

/*
>>Potential properties to check<<

- [x] pieces stay on the board when you place pieces (remainsWellformed)
- [x] you can always win/lose given any sequence of pieces (eventuallyGameOver)
- [x] get back to empty board (getBackToEmptyBoard)
- [x] given a board configuration, you will always lose
- [x] how to say: "you can't play the same piece twice in a row"
- [x] fewest number of filled in squares that you're guarenteed to lose
- [x] are there any missing pieces of 4 squares that fit into 3x3?

>>Properties we can't check or aren't interesting<<

- you can always clear a line given any sequence of pieces
We actually can't do this because temporal forge requires a lasso trace

- reachability: investigate whether any configuration of blocks is reachable from any other configuration within a finite number of moves
This is quantification over sets which is not doable in forge

- you shouldn't able to clear a line below a line with ... (some property)
This property is ill-defined

- smallest piece that you can't clear a line with
This is not very interesting because on an odd board, a 1x2 piece can't clear a line.

- explore when T-spins are possible
A Tspin is a when the last thing to happen to a T piece is a rotation (which we can't check since we model them as 4 individual pieces)
The other part is there's a square in the two front corners of the T piece, and one of the back corners.
for example: the X is the piece, the O is existing blocks and ? can be anything.
OO XX ??
XX XX ??
OO XX OO

>>VIDEO<<

show small pieces
show real pieces
show line clearing
show game over
show init from built in puzzle
show a pitfall -- odd length boards aren't clearable
show unique/nonrepeat trace
show L1 can actually clear

*/