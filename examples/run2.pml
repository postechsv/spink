int x[1] = 0
int tmp[1] = 0

active proctype parent() {
  tmp[0] = run child(3)
}

proctype child(int y) {
  x[0] = y[0]
}
