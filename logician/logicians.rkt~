#lang forge

sig Logician {
}

sig LogicianA extends Logician{}
sig LogicianB extends Logician{}
sig LogicianC extends Logician{}

sig World {
    preference: Logician->Boolean
}

one sig TrueWorld extends World {}

sig Boolean {}

sig True extends Boolean {}
sig False extends Boolean {}

sig Answer {}
sig Idk extends Answer{}
sig Ya extends Answer{}
sig Na extends Answer{}

sig State {
    worlds: Logician->World->World
}


sig Event {
    toMove: set Animal,
    pre: one State,
    post: one State
}


pred noEating[animals: set Animal] {
    -- if there exists a goat, there must be more goats than wolves
    some Goat & animals implies (#(Goat & animals) >= #(Wolf & animals))
}

-- constrains all worlds that connect to each other
pred consistent[l: Logician, w1: World, w2: World] {
    w1.preferences.l = w2.preferences.l
}

state[State] initState[l: Logician] {
   all l: Logician, w1: World, w2: World | consistent[l, w1, w2] iff l->w1->w2 in worlds
}

transition[State] logicianSays[e: Event] {
    e.pre = this
    e.post = this'
}

transition[State] step {
    some e: Event | logicianSays[this, this', e]
}

trace<|State, initState, puzzle, _|> traces: linear {}

run<|traces|> neverEating for exactly 12 State, 11 Event, 6 Animal, exactly 3 Goat, exactly 3 Wolf, 2 Position, 4 Int