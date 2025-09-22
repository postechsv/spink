chan c[1] = [0] of { int } // handshake channel

active proctype p1() {
  c[0] ! 42 // send succeeds
}

active proctype p2() {
  int x ; c[0] ? x // result: x = 42
}
