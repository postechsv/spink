// example from SPIN
// from https://spinroot.com/spin/Man/atomic.html

chan q[1] = [0] of { int }
int x[1] = 0
int y[1] = 0

active proctype X() { atomic { x[0] = x[0] + 1 ; q[0] ! 0 ; x[0] = x[0] + 1 } }
active proctype Y() { atomic { q[0] ? 0 } }
active proctype Z() { y[0] = x[0] }

// since atomicity gets tossed back to X from Y, y cannot read 1
