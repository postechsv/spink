int x = 0

active proctype parent() {
  run child() >= 0
}

proctype child() {
  x = 42
}
