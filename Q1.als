module Check

// -------------
// Boolean type
// -------------
abstract sig Bool {}
one sig True, False extends Bool {}

// -------------
// Logic tables
// -------------

// NOT table
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

// OR table
fun orTable: Bool -> Bool -> Bool {
    False -> False -> False +
    False -> True  -> True +
    True  -> False -> True +
    True  -> True  -> True
}

fun Or[x, y: Bool]: Bool {
    orTable[x][y]
}

// IMPLIES: ¬a ∨ b
fun Implies[x, y: Bool]: Bool {
    Or[Not[x], y]
}

// -------------
// Variables a, b
// -------------
one sig Vars {
    a: Bool,
    b: Bool
}

// -------------
// Formula test
// -------------
// Kiểm tra xem công thức có LUÔN đúng không
assert FormulaAlwaysTrue {
    Implies[
        And[Vars.a, Not[Vars.b]],
        Or[Vars.a, Vars.b]
    ] = True
}

check FormulaAlwaysTrue for 2
