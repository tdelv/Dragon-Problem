#lang forge

sig Dragon {}

sig World {
    eyeColors: set Dragon->Color
}

sig Color {} -- eye color
one sig Blue extends Boolean {}
one sig Green extends Boolean {}

sig Action {} -- what a dragon does. they leave if they find out they have green eyes
one sig Leave extends Answer{}
one sig Stay extends Answer{}

sig State {
    knowledge: set Dragon->World->World,
    evidence: set Dragon->Action->World,
}

pred setup {
    -- all worlds represent each Dragon once
    all w : World | {
        (w.eyeColors).Color = Dragon
        all d : Dragon |
            one (w.eyeColors)[d]
    }

    -- all unique worlds are in the set (specific number constrained in run statement)
    all w1: World, w2: World - w1 | not (w1.eyeColors = w2.eyeColors)

    -- well formed stuff
    Color = Blue + Green
    Action = Leave + Stay
}


sig Event {
    -- do we need anything else here?
    pre: one State,
    post: one State
}


pred consistentEvidence[w: World, knowledge: World->World, a: Answer] {
    -- TODO: rewrite this. stay if they don't know they have green eyes, leave if all worlds say they have green eyes
    (all connected: knowledge[w] | connected.preferences[Logician] = True) => a = Ya
    else {
        (all connected: knowledge[w] | False in connected.preferences[Logician]) => a = Na
        else a = Idk
    }
}

state[State] initState {
    -- TODO: two worlds have an edge if all the other dragons have the same eye color, and both worlds have at least one with green eyes
   all l: Logician, w1: World, w2: World | consistent[l, w1, w2] iff l->w1->w2 in knowledge
   all l: Logician, w: World, a: Answer | consistentEvidence[w, knowledge[l], a] iff l->a->w in evidence
}

transition[State] nextDay[e: Event] {
    -- build evidence graph for this speaker
    -- intersect everyone else's knowledge graph with that evidence graph
    all l: Logician | {
        all w1: World, w2: World | l->w1->w2 in knowledge' iff ((evidence[e.speaker]).w1 = (evidence[e.speaker]).w2 and l->w1->w2 in knowledge)
        all w: World, a: Answer | l->a->w in evidence' iff consistentEvidence[w, knowledge'[l], a]
    }

    e.pre = this
    e.post = this'
}

-- wrapper for an event to happen
transition[State] step {
    some e: Event | nextDay[this, this', e]
}

trace<|State, initState, step, _|> traces: linear {}

run<|traces|> setup for exactly 4 State, 3 Event, exactly 3 Dragon, exactly 8 World