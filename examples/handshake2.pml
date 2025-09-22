chan c[1] = [0] of { int, int } // handshake channel
int x[2] = 0

active proctype p1() {
  c[0] ! 42, 43
}

active proctype p2() {
  c[0] ? x[0], x[1] 
}
