#lang forge/temporal

open "tetris_model.frg"

pred delta_L1 { clearIsPossible => clear else addL1 }

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
    }
}

test suite for init {
    // If you have tests for this predicate, put them here!
    test expect {
        // -- technically you can, uncomment to see the counter example
        // cantUseL1ToClear : {
        //     wellformed
        //     init
        //     delta_L1 until clear
        // } is unsat
        cantUseL1ToClearBottomRow : {
            wellformed
            init
            delta_L1 until clearRow[0]
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

        // -- require a even x even board
        // clear2x1 : {
        //     wellformed
        //     init
        //     delta_2x1 until clear
        // } is sat
        // clear2x2 : {
        //     wellformed
        //     init
        //     delta_2x2 until clear
        // } is sat
    }
}

/*
Potential properties to check:
- pieces stay on the board when you place pieces
- you can always win given any sequence of pieces (play forever/lasso)
- you can always lose given any sequence of pieces
- you can always clear a line given any sequence of pieces
- get back to empty board
- given a board configuration, you will always lose
- reachability: investigate whether any configuration of blocks is reachable from any other configuration within a finite number of moves
- explore when T-spins are possible
- fewest number of filled in squares that you're guarenteed to lose
- you shouldn't able to clear a line below a line with ... (some property)
- smallest piece(s) that you can't clear a line with
- how to say: "you can't play the same piece twice in a row"
*/