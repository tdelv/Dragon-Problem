#lang forge

sig Dragon {}

sig World {
    eyeColors: set Dragon->Color
}

sig Color {} -- eye color
one sig Blue extends Color {}
one sig Green extends Color {}

sig Action {} -- what a dragon does. they leave if they find out they have green eyes
one sig Leave extends Action{}
one sig Stay extends Action{}

sig State {
    communal: set World->World, --shared evidence from all dragons
    knowledge: set Dragon->World->World,
    evidence: set Dragon->Action->World
}

pred setup {
    -- all worlds represent each Dragon once
    all w : World | {
        all d : Dragon |
            one (w.eyeColors)[d]
    }

    -- all unique worlds are in the set (specific number constrained in run statement)
    all w1: World, w2: World - w1 | not (w1.eyeColors = w2.eyeColors)

    -- well formed stuff
    Color = Blue + Green
    Action = Leave + Stay
}

-- the witch tells the dragons that at least one of them has green eyes
pred witch {
    all w: World | Green in w.eyeColors[Dragon]
}

pred consistentEvidence[d: Dragon, w: World, knowledge: World->World, a: Answer] {
    (all connected: knowledge[w] | connected.eyeColors[d] = Green) => a = Leave
    else a = Stay
}

-- true if this edge is shared by all the evidence graphs
pred communalEdge[w1: World, w2: World, evidence: Dragon->Action->World] {
    all d: Dragon | evidence[d].w1 = evidence[d].w2
}

pred wellFormedEvidence {
    all s: State | {
        all d: Dragon, w: World, a: Action | (d->a->w in s.evidence) iff consistentEvidence[d, w, s.knowledge[d], a]
        all w1: World, w2: World | (w1->w2 in s.communal) iff communalEdge[w1, w2, s.evidence]
    }
}

sig Event {
    pre: one State,
    post: one State
}

-- true if all dragons OTHER than the one passed in have the same eye color
pred consistent[d: Dragon, w1: World, w2: World] {
    all other: Dragon - d | w1.eyeColors[other] = w2.eyeColors[other]
}

state[State] initState {
    all d: Dragon, w1: World, w2: World | (d->w1->w2 in knowledge) iff consistent[d, w1, w2]
}

transition[State] nextDay[e: Event] {
    all d: Dragon | knowledge'[d] = knowledge[d] & communal

    e.pre = this
    e.post = this'
}

-- wrapper for an event to happen
transition[State] step {
    some e: Event | nextDay[this, this', e]
}

trace<|State, initState, step, _|> traces: linear {}

pred dragonProblem {
    setup
    wellFormedEvidence
    witch
}

-- n Dragon, 2^n - 1 World, n State, n - 1 Event
run<|traces|> dragonProblem for exactly 3 Dragon, exactly 7 World, exactly 3 State, 2 Event