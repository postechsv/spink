// from the summation example from the paper
int n = 5
int s = 0
active proctype sum() {
  do
  :: 0 < n ; s = s + n ; n = n - 1
  :: 0 >= n ; break
  od // s ends up 15
}
