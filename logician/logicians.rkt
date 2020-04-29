#lang forge

sig Logician {}

sig World {
    preferences: set Logician->Boolean
}

sig Boolean {} -- symbolizes if a logician wants a drink or not
one sig True extends Boolean {}
one sig False extends Boolean {}

sig Answer {} -- what a logician says
one sig Idk extends Answer{}
one sig Ya extends Answer{}
one sig Na extends Answer{}

sig State {
    knowledge: set Logician->World->World,
    evidence: set Logician->Answer->World,
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

    -- well formed stuff
    Boolean = True + False
    Answer = Idk + Ya + Na
}


sig Event {
    speaker: one Logician,
    pre: one State,
    post: one State
}

-- constrains all worlds that connect to each other
pred consistent[l: Logician, w1: World, w2: World] {
    w1.preferences[l] = w2.preferences[l]
}

pred consistentEvidence[w: World, knowledge: World->World, a: Answer] {
    (all connected: knowledge[w] | connected.preferences[Logician] = True) => a = Ya
    else {
        (all connected: knowledge[w] | False in connected.preferences[Logician]) => a = Na
        else a = Idk
    }
}

--run { setup } for exactly 3 Logician, 1 State, exactly 8 World

state[State] initState {
   all l: Logician, w1: World, w2: World | consistent[l, w1, w2] iff l->w1->w2 in knowledge
   all l: Logician, w: World, a: Answer | consistentEvidence[w, knowledge[l], a] iff l->a->w in evidence
   no answered -- no one has answered yet
}

transition[State] logicianSays[e: Event] {
    answered' = answered + e.speaker
    
    -- build evidence graph for this speaker
    -- intersect everyone else's knowledge graph with that evidence graph
    all l: Logician | {
        all w1: World, w2: World | (l->w1->w2 in knowledge and consistent[e.speaker, w1, w2]) iff l->w1->w2 in knowledge'
    }

    e.pre = this
    e.post = this'
}

-- wrapper for an event to happen
transition[State] step {
    some e: Event | logicianSays[this, this', e]
}

trace<|State, initState, step, _|> traces: linear {}

run<|traces|> setup for exactly 4 State, 3 Event, exactly 3 Logician, exactly 8 World