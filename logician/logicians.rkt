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

-- well formed stuff
pred setup {
    Boolean = True + False
    Answer = Idk + Ya + Na
}

-- use this predicate to automatically generate possible worlds
pred possibleWorlds {
    -- every dragon has one eye color in each world
    all w: World, l: Logician | 
        one (w.preferences)[l]

    -- no two worlds have the same eye color assignment
    all w1: World, w2: (World - w1) |
        w1.preferences != w2.preferences
}

-- logicians say:
--   yes if they know all logicians want a drink,
--   no if they know some logician doesn't want a drink,
--   idk otherwise
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


sig Event {
    speaker: one Logician,
    pre: one State,
    post: one State
}

-- used for init setup
-- true if the given logician has the same preference in both worlds
pred consistent[l: Logician, w1: World, w2: World] {
    w1.preferences[l] = w2.preferences[l]
}

state[State] initState {
   all l: Logician, w1: World, w2: World | consistent[l, w1, w2] iff l->w1->w2 in knowledge
   no answered -- no one has answered yet
}

-- update each dragon's knowledge graph witih the speaker's evidence
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


---------------------------------
-- BEGIN USER INTERACTION ZONE --
---------------------------------

pred logicianProblem {
    setup
    wellFormedEvidence

    -- uncomment the below line to autogenerate instances
    -- possibleWorlds
}

-- insert what instance you want to run here
-- for premade instances, use 'Logicians[n]' for n = 1 .. 6
-- for automatic instance, use 'AutomaticInst', and fill in the below instance

inst InstanceToRun { Logicians4 }

inst AutomaticInst {
    #Logician = 3 -- Whatever number you want
    #World = 8 -- 2^(#Logician)

    #State = 3
    #Event = 2
}


-------------------------------
-- END USER INTERACTION ZONE --
-------------------------------




-- below are the automatically generated instances to make Forge run faster on larger inputs

inst Logicians1 {
    Logician = Logician0
    
    World = World0 + World1
    preferences = (
        World0->(Logician0->True0) +
        World1->(Logician0->False0))

    #State = 1
    #Event = 0
}

inst Logicians2 {
    Logician = Logician0 + Logician1
    
    World = World0 + World1 + World2 + World3
    preferences = (
        World0->(Logician0->True0 + Logician1->True0) +
        World1->(Logician0->True0 + Logician1->False0) +
        World2->(Logician0->False0 + Logician1->True0) +
        World3->(Logician0->False0 + Logician1->False0))

    #State = 2
    #Event = 1
}

inst Logicians3 {
    Logician = Logician0 + Logician1 + Logician2
    
    World = World0 + World1 + World2 + World3 + World4 + World5 + World6 + World7
    preferences = (
        World0->(Logician0->True0 + Logician1->True0 + Logician2->True0) +
        World1->(Logician0->True0 + Logician1->True0 + Logician2->False0) +
        World2->(Logician0->True0 + Logician1->False0 + Logician2->True0) +
        World3->(Logician0->True0 + Logician1->False0 + Logician2->False0) +
        World4->(Logician0->False0 + Logician1->True0 + Logician2->True0) +
        World5->(Logician0->False0 + Logician1->True0 + Logician2->False0) +
        World6->(Logician0->False0 + Logician1->False0 + Logician2->True0) +
        World7->(Logician0->False0 + Logician1->False0 + Logician2->False0))

    #State = 3
    #Event = 2
}

inst Logicians4 {
    Logician = Logician0 + Logician1 + Logician2 + Logician3
    
    World = World0 + World1 + World2 + World3 + World4 + World5 + World6 + World7 + World8 + World9 + World10 + World11 + World12 + World13 + World14 + World15
    preferences = (
        World0->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->True0) +
        World1->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->False0) +
        World2->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->True0) +
        World3->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->False0) +
        World4->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->True0) +
        World5->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->False0) +
        World6->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->True0) +
        World7->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->False0) +
        World8->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->True0) +
        World9->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->False0) +
        World10->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->True0) +
        World11->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->False0) +
        World12->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->True0) +
        World13->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->False0) +
        World14->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->True0) +
        World15->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->False0))

    #State = 4
    #Event = 3
}

inst Logicians5 {
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

inst Logicians6 {
    Logician = Logician0 + Logician1 + Logician2 + Logician3 + Logician4 + Logician5
    
    World = World0 + World1 + World2 + World3 + World4 + World5 + World6 + World7 + World8 + World9 + World10 + World11 + World12 + World13 + World14 + World15 + World16 + World17 + World18 + World19 + World20 + World21 + World22 + World23 + World24 + World25 + World26 + World27 + World28 + World29 + World30 + World31 + World32 + World33 + World34 + World35 + World36 + World37 + World38 + World39 + World40 + World41 + World42 + World43 + World44 + World45 + World46 + World47 + World48 + World49 + World50 + World51 + World52 + World53 + World54 + World55 + World56 + World57 + World58 + World59 + World60 + World61 + World62 + World63
    preferences = (
        World0->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->True0 + Logician5->True0) +
        World1->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->True0 + Logician5->False0) +
        World2->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->False0 + Logician5->True0) +
        World3->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->False0 + Logician5->False0) +
        World4->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->True0 + Logician5->True0) +
        World5->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->True0 + Logician5->False0) +
        World6->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->False0 + Logician5->True0) +
        World7->(Logician0->True0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->False0 + Logician5->False0) +
        World8->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->True0 + Logician5->True0) +
        World9->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->True0 + Logician5->False0) +
        World10->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->False0 + Logician5->True0) +
        World11->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->False0 + Logician5->False0) +
        World12->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->True0 + Logician5->True0) +
        World13->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->True0 + Logician5->False0) +
        World14->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->False0 + Logician5->True0) +
        World15->(Logician0->True0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->False0 + Logician5->False0) +
        World16->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->True0 + Logician5->True0) +
        World17->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->True0 + Logician5->False0) +
        World18->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->False0 + Logician5->True0) +
        World19->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->False0 + Logician5->False0) +
        World20->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->True0 + Logician5->True0) +
        World21->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->True0 + Logician5->False0) +
        World22->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->False0 + Logician5->True0) +
        World23->(Logician0->True0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->False0 + Logician5->False0) +
        World24->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->True0 + Logician5->True0) +
        World25->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->True0 + Logician5->False0) +
        World26->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->False0 + Logician5->True0) +
        World27->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->False0 + Logician5->False0) +
        World28->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->True0 + Logician5->True0) +
        World29->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->True0 + Logician5->False0) +
        World30->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->False0 + Logician5->True0) +
        World31->(Logician0->True0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->False0 + Logician5->False0) +
        World32->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->True0 + Logician5->True0) +
        World33->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->True0 + Logician5->False0) +
        World34->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->False0 + Logician5->True0) +
        World35->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->True0 + Logician4->False0 + Logician5->False0) +
        World36->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->True0 + Logician5->True0) +
        World37->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->True0 + Logician5->False0) +
        World38->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->False0 + Logician5->True0) +
        World39->(Logician0->False0 + Logician1->True0 + Logician2->True0 + Logician3->False0 + Logician4->False0 + Logician5->False0) +
        World40->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->True0 + Logician5->True0) +
        World41->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->True0 + Logician5->False0) +
        World42->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->False0 + Logician5->True0) +
        World43->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->True0 + Logician4->False0 + Logician5->False0) +
        World44->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->True0 + Logician5->True0) +
        World45->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->True0 + Logician5->False0) +
        World46->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->False0 + Logician5->True0) +
        World47->(Logician0->False0 + Logician1->True0 + Logician2->False0 + Logician3->False0 + Logician4->False0 + Logician5->False0) +
        World48->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->True0 + Logician5->True0) +
        World49->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->True0 + Logician5->False0) +
        World50->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->False0 + Logician5->True0) +
        World51->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->True0 + Logician4->False0 + Logician5->False0) +
        World52->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->True0 + Logician5->True0) +
        World53->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->True0 + Logician5->False0) +
        World54->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->False0 + Logician5->True0) +
        World55->(Logician0->False0 + Logician1->False0 + Logician2->True0 + Logician3->False0 + Logician4->False0 + Logician5->False0) +
        World56->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->True0 + Logician5->True0) +
        World57->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->True0 + Logician5->False0) +
        World58->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->False0 + Logician5->True0) +
        World59->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->True0 + Logician4->False0 + Logician5->False0) +
        World60->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->True0 + Logician5->True0) +
        World61->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->True0 + Logician5->False0) +
        World62->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->False0 + Logician5->True0) +
        World63->(Logician0->False0 + Logician1->False0 + Logician2->False0 + Logician3->False0 + Logician4->False0 + Logician5->False0))

    #State = 6
    #Event = 5
}


-------------------------
-- Running and Testing --
-------------------------

run<|traces|> logicianProblem for InstanceToRun


-- knowledge is always increasing
pred increasingKnowledge {
    all e: Event |
        e.pre.knowledge ni e.post.knowledge
}

expect {
    increasingKnowledge1 : increasingKnowledge for Logicians1 is sat
    increasingKnowledge2 : increasingKnowledge for Logicians2 is sat
    increasingKnowledge3 : increasingKnowledge for Logicians3 is sat
    increasingKnowledge4 : increasingKnowledge for Logicians4 is sat
}

-- once Yes/No, always Yes/No
pred answerPermanent {
    all e: Event |
        all w: World, l: Logician | {
            w in e.pre.evidence[l][Ya] => w in e.post.evidence[l][Ya]
            w in e.pre.evidence[l][Na] => w in e.post.evidence[l][Na]
        }
}

expect {
    answerPermanent1 : answerPermanent for Logicians1 is sat
    answerPermanent2 : answerPermanent for Logicians2 is sat
    answerPermanent3 : answerPermanent for Logicians3 is sat
    answerPermanent4 : answerPermanent for Logicians4 is sat
}

-- all logicians agree once someone says an answer
pred logiciansAgree {
    all e1, e2: Event |
        e1.post = e2.pre implies {
            e1.pre.evidence[e1.speaker][Na] in e2.pre.evidence[e2.speaker][Na]
            e1.pre.evidence[e1.speaker][Ya] in e2.pre.evidence[e2.speaker][Ya]
        }
}

expect {
    logiciansAgree1 : logiciansAgree for Logicians1 is sat
    logiciansAgree2 : logiciansAgree for Logicians2 is sat
    logiciansAgree3 : logiciansAgree for Logicians3 is sat
    logiciansAgree4 : logiciansAgree for Logicians4 is sat
}

-- Idk, Idk, ..., Idk, Yes when all want drinks
pred correctSolution {
    let yesWorld = {w: World | w.preferences[Logician] = True} |
        all e: Event | {
            e.post !in Event.pre implies (e.pre.evidence[e.speaker]).yesWorld = Ya
                                 else (e.pre.evidence[e.speaker]).yesWorld = Idk
        }
}

expect {
    correctSolution1 : correctSolution for Logicians1 is sat
    correctSolution2 : correctSolution for Logicians2 is sat
    correctSolution3 : correctSolution for Logicians3 is sat
    correctSolution4 : correctSolution for Logicians4 is sat
}
