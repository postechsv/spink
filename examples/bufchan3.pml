chan c[1] = [2] of { int, int }
int x[2] = 0

active proctype p1() {
  c[0] ! 42, 43
}

active proctype p2() {
  c[0] ? x[0], x[1] 
}
