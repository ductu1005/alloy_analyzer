-----------------------------------------------
-- (4) (a⇒b) ∨ (b⇒a)
-----------------------------------------------

abstract sig Bool {}
one sig True, False extends Bool {}

fun notTable: Bool -> Bool {
    True -> False + False -> True
}

fun Not[x: Bool]: Bool {
    notTable[x]
}

// AND table
fun andTable: Bool -> Bool -> Bool {
    True -> True -> True +
    True -> False -> False +
    False -> True -> False +
    False -> False -> False
}

fun And[x, y: Bool]: Bool {
    andTable[x][y]
}

fun orTable: Bool -> Bool -> Bool {
    False -> False -> False +
    False -> True  -> True +
    True  -> False -> True +
    True  -> True  -> True
}

fun Or[x, y: Bool]: Bool {
    orTable[x][y]
}

fun Implies[x, y: Bool]: Bool {
    Or[Not[x], y]
}

one sig Vars {
    a: Bool,
    b: Bool
}

assert FormulaAlwaysTrue {
    Or[
        Implies[Vars.a, Vars.b],
        Implies[Vars.b, Vars.a]
    ] = True
}

check FormulaAlwaysTrue for 2
