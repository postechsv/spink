int x[1] = 0
int y[1] = 0

active proctype p() {
  if
    :: x[0] == 0 ; y[0] = 1
    :: x[0] != 0 ; y[0] = 2
  fi
}
