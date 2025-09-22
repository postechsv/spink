int x[1] = 0
int y[1] = 0

active proctype p() {
  if
    :: x == 0 ; y = 1 // either this,
    :: if
         :: x != 0 ; y = 2
         :: x < 2 ; y = 3 // or this can be chosen
       fi
  fi
}
