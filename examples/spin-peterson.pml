// variant of SPIN example
// from https://github.com/nimble-code/Spin/blob/master/Examples/peterson.pml

int f0
int f1
int turn = 0
int x = 0

active proctype p0() {
  int tmp[1] = 0;
  f0[0] = 1 ; turn[0] = 1 ;
  (f1[0] != 1) || (turn[0] != 1) ;
  tmp[0] = x[0] + 1 ; x[0] = tmp[0] ;
  f0[0] = 0
}

active proctype p1() {
  int tmp[1] = 0;
  f1[0] = 1 ; turn[0] = 0 ;
  (f0[0] != 1) || (turn[0] != 0) ;
  tmp[0] = x[0] + 1 ; x[0] = tmp[0] ;
  f1[0] = 0
}
