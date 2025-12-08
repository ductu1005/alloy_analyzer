-----------------------------------------------
--(13) (¬a⇒¬b) ∧ (a⧧b) ∨ (a∧c ⇒ b∧c)
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

// XOR:  a⧧b = (a ∧ ¬b) ∨ (¬a ∧ b)
fun Xor[x, y: Bool]: Bool {
    Or[
        And[x, Not[y]],
        And[Not[x], y]
    ]
}
one sig Vars {
    a: Bool,
    b: Bool,
    c: Bool
}

assert FormulaAlwaysTrue {
    Or[
	And[	
	     Implies[Not[Vars.a], Not[Vars.b]],
            Xor[Vars.a, Vars.b]
        ],
        Implies[
            And[Vars.a, Vars.c],
            And[Vars.b, Vars.c]
        ]
    ] = True
}

check FormulaAlwaysTrue for 2
