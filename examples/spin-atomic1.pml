// example from spin
// https://spinroot.com/spin/Man/atomic.html

int a[1] = 1
int b[1] = 2
int tmp[1] = 0
int flag[1] = 0

active proctype p1() {
  atomic {	/* swap the values of a and b */
    tmp[0] = b[0];
    b[0] = a[0];
    a[0] = tmp[0]
  }
}

active proctype p2() {
  a[0] == b[0]; flag[0] = 1 // by atomicity, flag can never be set
}
