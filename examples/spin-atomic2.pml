// example from spin
// https://spinroot.com/spin/Man/atomic.html

int a[1] = 0
int b[1] = 0
int flag[1] = 0

active proctype p1() {
  atomic {
    if
      :: a[0] = 1
      :: a[0] = 2
    fi;
    if
      :: b[0] = 1
      :: b[0] = 2
    fi
  }
}

active proctype p2() {
  ((a[0] != 0) && (b[0] == 0)) || ((a[0] == 0) && (b[0] != 0)); flag[0] = 1 // by atomicity, flag can never be set
}
