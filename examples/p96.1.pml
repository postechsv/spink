// variant from SPIN example
// from https://github.com/nimble-code/Spin/blob/master/Examples/Book_1991/p96.1.pml

int state[1] = 1
active proctype A() { (state[0] == 1) ; state[0] = state + 1 }
active proctype B() { (state[0] == 1) ; state[0] = state - 1 }
