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

-- use this predicate to automatically generate possible worlds
pred possibleWorlds {
    -- every dragon has one eye color in each world
    all w: World, d: Dragon | 
        one (w.eyeColors)[d]

    -- no two worlds have the same eye color assignment
    all w1: World, w2: (World - w1) |
        w1.eyeColors != w2.eyeColors

    -- the witch tells the dragons that at least one of them has green eyes
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




---------------------------------
-- BEGIN USER INTERACTION ZONE --
---------------------------------

pred dragonProblem {
    setup
    wellFormedEvidence

    -- uncomment the below line to autogenerate instances
    possibleWorlds
}

-- insert what instance you want to run here
-- for premade instances, use 'Dragons[n]' for n = 1 .. 6
-- for automatic instance, use 'AutomaticInst', and fill in the below instance

inst InstanceToRun { AutomaticInst }

inst AutomaticInst {
    #Dragon = 3 -- Whatever number you want
    #World = 7 -- 2^(#Dragon) - 1

    #State = 3
    #Event = 2
}


-------------------------------
-- END USER INTERACTION ZONE --
-------------------------------




-- below are the automatically generated instances to make Forge run faster on larger inputs

inst Dragons1 {
    Dragon = Dragon0
    
    World = World0
    eyeColors = (
        World0->(Dragon0->Green0))

    #State = 1
    #Event = 0
}

inst Dragons2 {
    Dragon = Dragon0 + Dragon1
    
    World = World0 + World1 + World2
    eyeColors = (
        World0->(Dragon0->Green0 + Dragon1->Green0) +
        World1->(Dragon0->Green0 + Dragon1->Blue0) +
        World2->(Dragon0->Blue0 + Dragon1->Green0))

    #State = 2
    #Event = 1
}

inst Dragons3 {
    Dragon = Dragon0 + Dragon1 + Dragon2
    
    World = World0 + World1 + World2 + World3 + World4 + World5 + World6
    eyeColors = (
        World0->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0) +
        World1->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0) +
        World2->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0) +
        World3->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0) +
        World4->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0) +
        World5->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0) +
        World6->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0))

    #State = 3
    #Event = 2
}

inst Dragons4 {
    Dragon = Dragon0 + Dragon1 + Dragon2 + Dragon3
    
    World = World0 + World1 + World2 + World3 + World4 + World5 + World6 + World7 + World8 + World9 + World10 + World11 + World12 + World13 + World14
    eyeColors = (
        World0->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0) +
        World1->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0) +
        World2->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0) +
        World3->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0) +
        World4->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0) +
        World5->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0) +
        World6->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0) +
        World7->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0) +
        World8->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0) +
        World9->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0) +
        World10->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0) +
        World11->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0) +
        World12->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0) +
        World13->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0) +
        World14->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0))

    #State = 4
    #Event = 3
}

inst Dragons5 {
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

inst Dragons6 {
    Dragon = Dragon0 + Dragon1 + Dragon2 + Dragon3 + Dragon4 + Dragon5
    
    World = World0 + World1 + World2 + World3 + World4 + World5 + World6 + World7 + World8 + World9 + World10 + World11 + World12 + World13 + World14 + World15 + World16 + World17 + World18 + World19 + World20 + World21 + World22 + World23 + World24 + World25 + World26 + World27 + World28 + World29 + World30 + World31 + World32 + World33 + World34 + World35 + World36 + World37 + World38 + World39 + World40 + World41 + World42 + World43 + World44 + World45 + World46 + World47 + World48 + World49 + World50 + World51 + World52 + World53 + World54 + World55 + World56 + World57 + World58 + World59 + World60 + World61 + World62
    eyeColors = (
        World0->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Green0) +
        World1->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Blue0) +
        World2->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Green0) +
        World3->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World4->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Green0) +
        World5->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Blue0) +
        World6->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Green0) +
        World7->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World8->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Green0) +
        World9->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Blue0) +
        World10->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Green0) +
        World11->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World12->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Green0) +
        World13->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Blue0) +
        World14->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Green0) +
        World15->(Dragon0->Green0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World16->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Green0) +
        World17->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Blue0) +
        World18->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Green0) +
        World19->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World20->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Green0) +
        World21->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Blue0) +
        World22->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Green0) +
        World23->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World24->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Green0) +
        World25->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Blue0) +
        World26->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Green0) +
        World27->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World28->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Green0) +
        World29->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Blue0) +
        World30->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Green0) +
        World31->(Dragon0->Green0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World32->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Green0) +
        World33->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Blue0) +
        World34->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Green0) +
        World35->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World36->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Green0) +
        World37->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Blue0) +
        World38->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Green0) +
        World39->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World40->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Green0) +
        World41->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Blue0) +
        World42->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Green0) +
        World43->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World44->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Green0) +
        World45->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Blue0) +
        World46->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Green0) +
        World47->(Dragon0->Blue0 + Dragon1->Green0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World48->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Green0) +
        World49->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Blue0) +
        World50->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Green0) +
        World51->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World52->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Green0) +
        World53->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Blue0) +
        World54->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Green0) +
        World55->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Green0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World56->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Green0) +
        World57->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Green0 + Dragon5->Blue0) +
        World58->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Green0) +
        World59->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Green0 + Dragon4->Blue0 + Dragon5->Blue0) +
        World60->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Green0) +
        World61->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Green0 + Dragon5->Blue0) +
        World62->(Dragon0->Blue0 + Dragon1->Blue0 + Dragon2->Blue0 + Dragon3->Blue0 + Dragon4->Blue0 + Dragon5->Green0))

    #State = 6
    #Event = 5
}

run<|traces|> dragonProblem for InstanceToRun

--test expect {
--    reachableYes1 : reachable for reachableYes1 is sat
--    reachableYes2 : reachable for reachableYes2 is sat
--    reachableYes3 : reachable for reachableYes3 is sat
--}

