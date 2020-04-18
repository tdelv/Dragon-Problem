#lang forge

sig Logician {
    say: one Boolean,
    -- worlds: set World->World
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


pred wellFormed {
    all l: Logician |
       all w: Logician.world |
           Logician.wantBeer = w.want.Logician
}
// todo : [wellformed] predicate saying a valid world is one where what they want is in it
// todo: predicate 

pred noEating[animals: set Animal] {
    -- if there exists a goat, there must be more goats than wolves
    some Goat & animals implies (#(Goat & animals) >= #(Wolf & animals))
}

pred neverEating {
    -- for any state, there's no eating
    all s: State | {
        noEating[s.near]
        noEating[s.far]
    }
}

sig Event {
    toMove: set Animal,
    pre: one State,
    post: one State
}

state[State] initState {
    no far
    near = Animal
    boat = Near
}

state[State] finalState {
    -- constraints for the last state that should hold for a valid solution
    -- Fill me in!
    no near
    far = Animal
    boat = Far

}
transition[State] crossRiver[e: Event] {
    -- constrains the animals to move to be on the proper side, and from 0 to 2
    #(e.toMove) < 3 and #(e.toMove) > 0
    boat = Near implies e.toMove in near
    boat = Far implies e.toMove not in near

    -- constrains the sets that live on both sides of the river
    boat = Near implies boat' = Far and (near' = near - e.toMove and far' = far + e.toMove)
    boat = Far implies boat' = Near and (near' = near + e.toMove and far' = far - e.toMove)

    e.pre = this
    e.post = this'
}

transition[State] puzzle {
    some e: Event | crossRiver[this, this', e]
}

trace<|State, initState, puzzle, finalState|> traces: linear {}

run<|traces|> neverEating for exactly 12 State, 11 Event, 6 Animal, exactly 3 Goat, exactly 3 Wolf, 2 Position, 4 Int