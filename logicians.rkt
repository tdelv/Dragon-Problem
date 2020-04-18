#lang forge

sig Logician {}

one sig LogicianA extends Logician{}
one sig LogicianB extends Logician{}
one sig LogicianC extends Logician{}

sig World {
    preferences: set Logician->Boolean
}

--one sig TrueWorld extends World {}

sig Boolean {}

one sig True extends Boolean {}
one sig False extends Boolean {}

sig Answer {}
one sig Idk extends Answer{}
one sig Ya extends Answer{}
one sig Na extends Answer{}

sig State {
    worlds: set Logician->World->World
}

one sig InitState extends State {} -- delete later

pred setup {
    -- all worlds represent each Logician once
    all w : World | {
        (w.preferences).Boolean = Logician -- what is this line lol
        all l : Logician |
            one (w.preferences)[l]
    }

    -- all possible combinations of preferences are in a world
    --all l: Logician, b: Boolean | divide[# (World), 2] = # ({w: World | l->b in w.preferences})


    -- attempt 2: no worlds have the same preferences
    all w1: World, w2: World - w1 | not (w1.preferences = w2.preferences)
    
    Boolean = True + False
    Answer = Idk + Ya + Na
    Logician = LogicianA + LogicianB + LogicianC -- not extensible but putting this here for now
}


sig Event {
    answer: one Logician->Answer,
    pre: one State,
    post: one State
}


-- constrains all worlds that connect to each other
pred consistent[l: Logician, w1: World, w2: World] {
    w1.preferences[l] = w2.preferences[l]
}

pred iState {
    all l: Logician, w1: World, w2: World | consistent[l, w1, w2] iff l->w1->w2 in InitState.worlds
}

run { setup iState } for exactly 3 Logician, 1 State, exactly 8 World

state[State] initState {
   all l: Logician, w1: World, w2: World | consistent[l, w1, w2] iff l->w1->w2 in worlds
}

transition[State] logicianSays[e: Event] {
    e.pre = this
    e.post = this'
}

transition[State] step {
    some e: Event | logicianSays[this, this', e] -- this has to be one Logician answering something
}



--pred noEating[animals: set Animal] {
    -- if there exists a goat, there must be more goats than wolves
    --some Goat & animals implies (#(Goat & animals) >= #(Wolf & animals))
--}

--trace<|State, initState, step, _|> traces: linear {}

--run<|traces|> neverEating for exactly 12 State, 11 Event, 6 Animal, exactly 3 Goat, exactly 3 Wolf, 2 Position, 4 Int