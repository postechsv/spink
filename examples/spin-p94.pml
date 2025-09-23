// variant of SPIN example
// from https://github.com/nimble-code/Spin/blob/master/Examples/Book_1991/p94.pml

int state[1] = 2
active proctype A() { (state[0] == 1) ; state[0] = 3 }
active proctype B() { state[0] = state[0] - 1 }
