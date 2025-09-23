int x[1] = 0
int tmp[1] = 0

active proctype parent() {
  tmp[0] = run child()
}

proctype child() {
  x[0] = 42
}
