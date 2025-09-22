// example from the paper (cross-process interference by handshake)

chan c[1] = [0] of { int }
int x[1] = 0
int y[1] = 0

active proctype p1() {
  if :: c[0] ! 1 :: y[0] = 1 fi
}

active proctype p2() {
  if :: y[0] = 1 :: c[0] ? x[0] fi
}

// (x,y) ends up either (1,0) or (0,1)
