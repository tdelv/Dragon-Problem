#lang forge

sig Dragon {}

abstract sig Color {}
one sig Blue extends Color {}
one sig Green extends Color {}

sig World {
    eyeColors : set Dragon -> Color
}
one sig TrueWorld extends World {}

sig State {
    possibleWorlds : set Dragon->World->World
}



pred WorldSetup {
    all w : World | {
        (w.eyeColors).Color = Dragon
        all d : Dragon |
            one (w.eyeColors)[d]
    }
}

pred PossibleWorldSetup {
    all s : State, d : Dragon | let possWorlds = s.possibleWorlds[d] | {
        -- Reflexive
        all w : World |
            w->w in possWorlds

        -- Symmetric
        all w1, w2 : World |
            w1->w2 in possWorlds implies w2->w1 in possWorlds

        -- Transitive
        all w1, w2, w3 : World |
            w1->w2 + w2->w3 in possWorlds implies w1->w3 in possWorlds
    }
    
}

pred Setup {
    Color = Blue + Green
    WorldSetup
}



run {Setup} for 5 Dragon