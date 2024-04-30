#lang forge/temporal

open "tetris_model.frg"

pred delta_L1 {
    clearIsPossible => clear
    else
    addL1
}

pred delta_L1L2 {
    clearIsPossible => clear
    else
    {addL1 or addL2}
}

test suite for tetrisTesting {
    // If you have tests for this predicate, put them here!
    test expect {
        clearIsSat : {
            wellformed
            init
            delta until clear
        } is sat
        // -- technically you can, uncomment to see the counter example
        // cantUseL1ToClear : {
        //     wellformed
        //     init
        //     delta_L1 until clear
        // } is unsat
        clearL1L2 : {
            wellformed
            init
            delta_L1L2 until clear
        } is sat
    }
}

/*
Potential properties to check:
- pieces stay on the board when you place pieces
- you can always win given any sequence of pieces
- you can always lose given any sequence of pieces
- you can always clear a line given any sequence of pieces
- given a board configuration, you will always lose
- reachability: investigate whether any configuration of blocks is reachable from any other configuration within a finite number of moves
- explore when T-spins are possible/useful
*/