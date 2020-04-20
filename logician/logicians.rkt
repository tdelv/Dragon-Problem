#lang forge

sig Logician {}

sig World {
    preferences: set Logician->Boolean
}
one sig TrueWorld extends World {} --defined to be TTT in setup predicate

sig Boolean {}
one sig True extends Boolean {}
one sig False extends Boolean {}

sig Answer {}
one sig Idk extends Answer{}
one sig Ya extends Answer{}
one sig Na extends Answer{}

sig State {
    worlds: set Logician->World->World,
    answered: set Logician -- who has answered the bartender already
}

pred setup {
    -- all worlds represent each Logician once
    all w : World | {
        (w.preferences).Boolean = Logician
        all l : Logician |
            one (w.preferences)[l]
    }

    -- all unique worlds are in the set (specific number constrained in run statement)
    all w1: World, w2: World - w1 | not (w1.preferences = w2.preferences)

    -- hardcoding the Trueworld
    all l: Logician | l->True in TrueWorld.preferences

    -- well formed stuff
    Boolean = True + False
    Answer = Idk + Ya + Na
    one TrueWorld
}


sig Event {
    speaker: one Logician,
    answer: one Answer,
    pre: one State,
    post: one State
}


-- constrains all worlds that connect to each other
pred consistent[l: Logician, w1: World, w2: World] {
    w1.preferences[l] = w2.preferences[l]
}

--run { setup } for exactly 3 Logician, 1 State, exactly 8 World

state[State] initState {
   all l: Logician, w1: World, w2: World | consistent[l, w1, w2] iff l->w1->w2 in worlds
   no answered -- no one has answered yet
}

transition[State] logicianSays[e: Event] {
    answered' = answered + e.speaker
    
    -- propagate that answer and update worlds
    all l: Logician | {
        -- this feels like cheating lol
        -- are we supposed to break it down into cases where if they answer yes then we do this and if they ansewr no then we do that etc
        all w1: World, w2: World | (l->w1->w2 in worlds and consistent[e.speaker, w1, w2]) iff l->w1->w2 in worlds'
    }

    e.pre = this
    e.post = this'
}

pred validAnswer[e: Event] {
    -- find a Logician that hasn't answered yet
    e.speaker not in e.pre.answered
    
    -- make that Logician think and answer
    (all w: e.pre.worlds[e.speaker][TrueWorld] | w.preferences[Logician] = True) => e.answer = Ya
    else {
        (all w: e.pre.worlds[e.speaker][TrueWorld] | False in w.preferences[Logician] ) => e.answer = Na
        else e.answer = Idk
    }
}

transition[State] step {
    some e: Event | validAnswer[e] and logicianSays[this, this', e]
}

trace<|State, initState, step, _|> traces: linear {}

run<|traces|> setup for exactly 4 State, 3 Event, exactly 3 Logician, exactly 8 World