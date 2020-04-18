#lang forge

sig Logician {}

one sig LogicianA extends Logician{}
one sig LogicianB extends Logician{}
one sig LogicianC extends Logician{}

sig World {
    preferences: set Logician->Boolean
}

one sig TrueWorld extends World {}

sig Boolean {}

one sig True extends Boolean {}
one sig False extends Boolean {}

sig Answer {}
one sig Idk extends Answer{}
one sig Ya extends Answer{}
one sig Na extends Answer{}

sig State {
    worlds: set Logician->World->World
    answered: set Logician -- who has answered the Bartender already
}

one sig InitState extends State {} -- delete later

pred setup {
    -- all worlds represent each Logician once
    all w : World | {
        (w.preferences).Boolean = Logician -- what is this line lol
        all l : Logician |
            one (w.preferences)[l]
    }

    -- attempt 2: no worlds have the same preferences
    all w1: World, w2: World - w1 | not (w1.preferences = w2.preferences)
    
    all l:Logician | l->True in TrueWorld.preferences

    Boolean = True + False
    Answer = Idk + Ya + Na
    Logician = LogicianA + LogicianB + LogicianC -- not extensible but putting this here for now
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

pred t
run { setup } for exactly 3 Logician, 1 State, exactly 8 World

state[State] initState {
   all l: Logician, w1: World, w2: World | consistent[l, w1, w2] iff l->w1->w2 in worlds
   no answered -- no one has answered yet
}

transition[State] logicianSays[e: Event] {
    -- propagate that answer and update worlds
    answered' = answered + e.speaker
    

    e.pre = this
    e.post = this'
}

pred validAnswer[e: Event] {
    -- find a Logician that hasn't answered yet
    e.speaker not in e.pre.answered
    -- make that Logician think and answer
    all w: e.pre.worlds[e.speaker].world | 
    -- e.answer
}

transition[State] step {
    some e: Event | validAnswer[e] and logicianSays[this, this', e] -- this has to be one Logician answering something
}



--pred noEating[animals: set Animal] {
    -- if there exists a goat, there must be more goats than wolves
    --some Goat & animals implies (#(Goat & animals) >= #(Wolf & animals))
--}

trace<|State, initState, step, _|> traces: linear {}

run<|traces|> for exactly 12 State, 11 Event, 6 Animal, exactly 3 Goat, exactly 3 Wolf, 2 Position, 4 Int