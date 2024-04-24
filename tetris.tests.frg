#lang forge/temporal

open "tetris_new.frg"

test suite for neverStealing {
    // If you have tests for this predicate, put them here!
    test expect {
        clearIsSat : {
            wellformed
            init
            delta until clear
        } is sat
    }
}