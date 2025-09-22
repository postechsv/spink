// variant of SPIN example
// from https://github.com/nimble-code/Spin/blob/master/Examples/Book_1991/p101.pml

chan name[1] = [0] of { int, int }

active proctype A()
{	name[0] ! 33, 124;
	name[0] ! 33, 121
}

active proctype B()
{	int state[1];
	name[0] ? 33, state[0]
}
