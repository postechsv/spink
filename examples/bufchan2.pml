chan c[1] = [3] of { int }

active proctype p() {
  c[0] ! 42 ; c[0] ! 43 ; c[0] ! 44 ; c[0] ! 45 // send blocks after sending 44
}
