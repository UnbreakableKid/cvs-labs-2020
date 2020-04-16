function sortedI(a:array<int>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] }

method sortedInsertion(a:array<int>, na:int, e:int) returns (z:array<int>, nz:int, pos:int)
  requires 0 <= na < a.Length
  requires sortedI(a, na)
  ensures sortedI(a, na+1)
  ensures 0 <= pos <= na && a[pos] == e
  ensures forall k :: 0 <= k < pos ==> a[k] == old(a[k])
  ensures forall k :: pos < k < na ==> a[k] == old(a[k-1])
  modifies a
{
  var i := na;
  if( na > 0 ) 
  { a[na] := a[na-1]; }
  while 0 < i && e < a[i-1] 
    decreases i
    invariant 0 <= i <= na
    invariant sortedI(a, na+1)
    invariant forall k :: i < k < na+1 ==> e <= a[k] 
    invariant forall k :: 0 <= k < i ==> a[k] == old(a[k])
    invariant forall k :: i < k < na ==> a[k] == old(a[k-1])
  {
    a[i] := a[i-1];
    i := i - 1;
  }
  a[i] := e;
  return a, na+1, i;
}





function sortedRange(a:array<int>, s:int, e:int) : bool 
requires 0 <= s <= e <= a.Length
reads a
{
    forall i,j :: s <= j <= i < e ==> a[j] <= a[i]
}

method sortedInsertion2(a:array<int>, na:int, e:int) returns (z:array<int>, nz:int, pos:int)

requires 0 <= na < a.Length - 1 //there is at least one empty space
requires sortedRange(a, 0, na)

ensures a == z
ensures nz == na + 1
ensures 0 <= pos < nz
ensures sortedRange(a, 0, nz)
ensures forall i :: 0 <= i < pos ==> a[i] == z[i]
ensures z[pos] == e
ensures forall i :: pos <= i < na ==> old(a[i]) == a[i + 1]
modifies a
{
    if(na == 0) {
        a[0] := e;
        return a, 1, 0;
    }
    assert na > 0;

    var x:int := 0;

    while(x < na && a[x] <= e)
    decreases na - x
    invariant 0 <= x <= na
    invariant forall i :: (0 <= i < x) ==> a[i] <= e
    {
        x := x + 1;
    }

    if(x == na) {
        a[na] := e;
        return a, na + 1, na;
    }
    a[na] := a[na - 1];
    var y := na;

    while (y > x)
    decreases y
    invariant x <= y <= na
    invariant sortedRange(a, 0, na + 1)
    invariant forall i :: 0 <= i < x ==> a[i] <= e
    invariant forall i :: x <= i < na ==> a[i] >= e
    invariant a[x .. y] == old(a[x .. y])
    invariant forall i :: y < i <= na ==> old(a[i - 1]) == a[i]
    {
        a[y] := a[y-1];
        y := y - 1;
    }

    a[x] := e;

    return a, na + 1, x;
}

