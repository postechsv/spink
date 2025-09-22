int x[1] = 0

active proctype p1() {
  x[0] = 42
}

active proctype p2() {
  x[0] = 43
}
