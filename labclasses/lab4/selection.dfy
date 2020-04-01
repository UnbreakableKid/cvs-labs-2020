function sorted(a:array<char>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] }

function partitioned(a:array<char>,i:int,n:int):bool
    requires 0 <= n <= a.Length
    reads a;
{ forall k, l :: 0 <= k < i <= l < n ==> (a[k] <= a[l]) }


method selectSmaller(a:array<char>, i:int, n:int) 
  requires 0 <= i < n <= a.Length
  requires sorted(a, i)
  requires partitioned(a, i, n)
  modifies a
  ensures sorted(a, i+1)
  ensures partitioned(a, i+1, n)
{
  var j := i+1;
  while j < n 
    decreases n - j
    invariant i < j <= n
    invariant a[..i] == old(a[..i])
    invariant forall k :: i < k < j ==> a[i] <= a[k]
    invariant sorted(a, i)
    invariant partitioned(a, i, n)
  {
    if a[j] < a[i]
    { 
      a[i], a[j] := a[j], a[i];
    }
    j := j + 1;
  }
  assert sorted(a, i);
  assert partitioned(a, i, n);
  assert forall k :: i < k < n ==> a[i] <= a[k];
  // ==> 
  assert sorted(a, i+1);
  assert partitioned(a, i+1, n);
}

method selectionSort(a:array<char>, n:int)
  requires 0 <= n <= a.Length
  modifies a
{
  var i := 0;
  while i < n 
    decreases n - i
    invariant 0 <= i <= n
    invariant sorted(a, i)
    invariant partitioned(a, i, n)
  {
    selectSmaller(a, i, n);
    assert sorted(a, i+1);
    assert partitioned(a, i+1, n);
}
    i := i + 1;
  }
}


function sortedRange(a:array<char>, l:int, h:int):bool
    requires 0 <= l <= h <= a.Length
    reads a
{ forall i, j:: (l <= i < j < h) ==> a[i] <= a[j] }


