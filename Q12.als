-----------------------------------------------
--(12) a ⇒ a∧b == a⇒b == a∨b ⇒ b
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

fun ToBool[x: Bool, y: Bool]: Bool {
    (x = y) => True else False
}

one sig Vars {
    a: Bool,
    b: Bool,
    c: Bool
}

assert FormulaAlwaysTrue {
	Implies[Vars.a, And[Vars.a, Vars.b]] = Implies[Vars.a, Vars.b] 
	and 
	Implies[Vars.a, Vars.b] = Implies[Or[Vars.a, Vars.b], Vars.b]
}

check FormulaAlwaysTrue for 2
