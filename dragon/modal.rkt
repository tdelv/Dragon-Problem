#lang forge

abstract sig Expression {}

sig Atom extends Expression {}

sig Not extends Expression {
    notVal: one Expression
}

sig Or extends Expression {
    orLeft: one Expression,
    orRight: one Expression
}

sig And extends Expression {
    andLeft: one Expression,
    andRight: one Expression
}

sig Box extends Expression {
    boxVal: one Expression
}

sig Diamond extends Expression {
    diamondVal: one Expression
}


sig World {
    trueAtoms: set Atom,
    relates: set World
}

sig Assignment {
    trueExpressions: set World->Expression
}

pred ExpressionsWellFormed {
    let allSubExpressions = notVal + orLeft + orRight + 
                            andLeft + andRight + boxVal + diamondVal |
        no iden & ^allSubExpressions
}

pred AssignmentDefinition {
    all a: Assignment, w: World | {
        -- Atom
        all e: Atom |
            e in a.trueExpressions[w] <=> 
            e in w.trueAtoms

        -- Not
        all e: Not |
            e in a.trueExpressions[w] <=> 
            e.notVal not in a.trueExpressions[w]

        -- Or
        all e: Or |
            e in a.trueExpressions[w] <=> 
            (e.orLeft in a.trueExpressions[w]) or (e.orRight in a.trueExpressions[w])

        -- And
        all e: And |
            e in a.trueExpressions[w] <=> 
            (e.andLeft in a.trueExpressions[w]) and (e.andRight in a.trueExpressions[w])

        -- Box
        all e: Box |
            e in a.trueExpressions[w] <=> {
            all w2: w.relates |
                e.boxVal in a.trueExpressions[w2]}

        -- Diamond
        all e: Diamond |
            e in a.trueExpressions[w] <=> {
            some w2: w.relates |
                e.diamondVal in a.trueExpressions[w2]}
    }
}

pred Setup {
    Expression = Atom + Not + Or + And + Box + Diamond
    ExpressionsWellFormed
    AssignmentDefinition
    #Atom = 5
}

run Setup for exactly 5 Atom, exactly 50 Expression, exactly 5 World, exactly 1 Assignment
