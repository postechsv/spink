int x[1] = 0
int y[1] = 0

active proctype p() {
  if
    :: x == 0 ; y = 1
    :: x != 0 ; y = 2
  fi
}
