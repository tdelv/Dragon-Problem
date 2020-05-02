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
    ---all w : World | {
    ---    (w.preferences).Boolean = Logician
    ---    all l : Logician |
    ---        one (w.preferences)[l]
    ---}

    -- all unique worlds are in the set (specific number constrained in run statement)
    ---all w1: World, w2: World - w1 | not (w1.preferences = w2.preferences)

    -- well formed stuff
    Boolean = True + False
    Answer = Idk + Ya + Na
}


sig Event {
    speaker: one Logician,
    pre: one State,
    post: one State
}

pred consistentEvidence[w: World, knowledge: World->World, a: Answer] {
    (all connected: knowledge[w] | connected.preferences[Logician] = True) => a = Ya
    else {
        (all connected: knowledge[w] | False in connected.preferences[Logician]) => a = Na
        else a = Idk
    }
}

-- defines knowledge at each state
pred wellFormedEvidence {
    all s: State, l: Logician, w: World, a: Answer | 
        l->a->w in s.evidence iff consistentEvidence[w, s.knowledge[l], a]
}


-- constrains all worlds that connect to each other
pred consistent[l: Logician, w1: World, w2: World] {
    w1.preferences[l] = w2.preferences[l]
}

state[State] initState {
   all l: Logician, w1: World, w2: World | consistent[l, w1, w2] iff l->w1->w2 in knowledge
   no answered -- no one has answered yet
}

transition[State] logicianSays[e: Event] {
    answered' = answered + e.speaker
    answered' != answered
    
    -- intersect everyone else's knowledge graph with that evidence graph
    all l: Logician, w1: World, w2: World | 
        l->w1->w2 in knowledge' iff (l->w1->w2 in knowledge) and ((evidence[e.speaker]).w1 = (evidence[e.speaker]).w2)

    e.pre = this
    e.post = this'
}

-- wrapper for an event to happen
transition[State] step {
    some e: Event | logicianSays[this, this', e]
}

trace<|State, initState, step, _|> traces: linear {}

pred logicanProblem {
    setup
    wellFormedEvidence
}

inst PossibleWorldsInst {
    Logician = Logician0 + Logician1 + Logician2 + Logician3 + Logician4
    
    World = World0 + World1 + World2 + World3 + World4 + World5 + World6 + World7 + World8 + World9 + World10 + World11 + World12 + World13 + World14 + World15 + World16 + World17 + World18 + World19 + World20 + World21 + World22 + World23 + World24 + World25 + World26 + World27 + World28 + World29 + World30 + World31
    preferences = (
        World0->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->True0) +
        World1->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->False0) +
        World2->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->True0) +
        World3->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->False0) +
        World4->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->True0) +
        World5->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->False0) +
        World6->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->True0) +
        World7->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->False0) +
        World8->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->True0) +
        World9->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->False0) +
        World10->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->True0) +
        World11->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->False0) +
        World12->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->True0) +
        World13->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->False0) +
        World14->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->True0) +
        World15->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->False0) +
        World16->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->True0) +
        World17->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->False0) +
        World18->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->True0) +
        World19->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->False0) +
        World20->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->True0) +
        World21->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->False0) +
        World22->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->True0) +
        World23->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->False0) +
        World24->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->True0) +
        World25->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->False0) +
        World26->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->True0) +
        World27->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->False0) +
        World28->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->True0) +
        World29->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->False0) +
        World30->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->True0) +
        World31->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->False0))

    #State = 5
    #Event = 4
}


run<|traces|> setup for PossibleWorldsInst