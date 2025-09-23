int x = 0

active proctype parent() {
  run child(3) >= 0
}

proctype child(int y) {
  x = y
}
