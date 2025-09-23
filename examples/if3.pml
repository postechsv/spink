int x[1] = 0
int y[1] = 0

active proctype p() {
  if
    :: x[0] == 0 ; y[0] = 1 // either this,
    :: if
         :: x[0] != 0 ; y[0] = 2
         :: x[0] < 2 ; y[0] = 3 // or this can be chosen
       fi
  fi
}
