int n = 3
int i = 0

active proctype p() {
  do
    :: i < n ; i = i + 1
    :: i >= n ; break
  od
}
