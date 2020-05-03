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
    knowledge: set Dragon->World->World,
    evidence: set Dragon->Action->World,
    communal: set World->World --shared evidence from all dragons
}

-- well formed stuff
pred setup {
    Color = Blue + Green
    Action = Leave + Stay
}

-- the witch tells the dragons that at least one of them has green eyes
pred witch {
    all w: World | Green in w.eyeColors[Dragon]
}

-- dragons leave if they know they have green eyes, and stay otherwise
pred consistentEvidence[d: Dragon, w: World, knowledge: World->World, a: Answer] {
    (all connected: knowledge[w] | connected.eyeColors[d] = Green) => a = Leave
    else a = Stay
}

-- true if this edge is shared by all the evidence graphs
pred communalEdge[w1: World, w2: World, evidence: Dragon->Action->World] {
    all d: Dragon | evidence[d].w1 = evidence[d].w2
}

-- defines the evidence graphs for each dragon as well as the communal evidence for each state
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

-- used for init setup
-- true if all dragons OTHER than the one passed in have the same eye color
pred consistent[d: Dragon, w1: World, w2: World] {
    all other: Dragon - d | w1.eyeColors[other] = w2.eyeColors[other]
}

state[State] initState {
    all d: Dragon, w1: World, w2: World | (d->w1->w2 in knowledge) iff consistent[d, w1, w2]
}

-- update each dragon's knowledge graph witih the communal evidence
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

inst PossibleWorldsInst {
    Dragon = Dragon0 + Dragon1 + Dragon2 + Dragon3 + Dragon4
    
    World = World0 + World1 + World2 + World3 + World4 + World5 + World6 + World7 + World8 + World9 + World10 + World11 + World12 + World13 + World14 + World15 + World16 + World17 + World18 + World19 + World20 + World21 + World22 + World23 + World24 + World25 + World26 + World27 + World28 + World29 + World30
    eyeColors = (
        World0->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0) +
        World1->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0) +
        World2->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0) +
        World3->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0) +
        World4->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0) +
        World5->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0) +
        World6->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0) +
        World7->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0) +
        World8->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0) +
        World9->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0) +
        World10->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0) +
        World11->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0) +
        World12->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0) +
        World13->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0) +
        World14->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0) +
        World15->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0) +
        World16->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0) +
        World17->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0) +
        World18->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0) +
        World19->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0) +
        World20->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0) +
        World21->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0) +
        World22->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0) +
        World23->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0) +
        World24->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0) +
        World25->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0) +
        World26->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0) +
        World27->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0) +
        World28->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0) +
        World29->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0) +
        World30->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0))

    #State = 5
    #Event = 4
}

run<|traces|> dragonProblem for PossibleWorldsInst