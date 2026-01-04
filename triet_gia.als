module Check

sig Philosopher {
    left: one Fork,
    right: one Fork
}

sig Fork {}

fact CircularTable {
    #Philosopher = 5
    #Fork = 5

    // mỗi nĩa nằm giữa đúng 2 triết gia
    all f: Fork |
        #(left.f + right.f) = 2
}

//----------------------------------
// STATES
//----------------------------------
abstract sig State {}
one sig Thinking, Eating extends State {}

sig Status {
    st   : Philosopher -> one State,
    next : lone Status
}

one sig Init extends Status {}

// ăn thì phải có đủ 2 nĩa (mô hình hóa quan hệ)
fact EatingNeedsTwoForks {
    all s: Status, p: Philosopher |
        s.st[p] = Eating implies
            some p.left and some p.right
}

// 1 nĩa chỉ phục vụ 1 triết gia tại 1 trạng thái
fact ForkExclusive {
    all s: Status, f: Fork |
        lone p: Philosopher |
            s.st[p] = Eating and
            (p.left = f or p.right = f)
}

// Trong toàn bộ trace, mỗi triết gia bắt buộc phải ăn ít nhất 1 lần
fact Fairness {
    all p: Philosopher |
        some s: Status |
            s.st[p] = Eating
}

// Ăn xong phải bỏ nĩa xuống
fact EatThenThink {
    all s: Status, p: Philosopher |
        s.st[p] = Eating and some s.next implies
            s.next.st[p] = Thinking
}

assert NoStarvation {
    all p: Philosopher |
        some s: Status |
            s.st[p] = Eating
}

check NoStarvation for 5 Philosopher, 5 Fork, 6 Status
