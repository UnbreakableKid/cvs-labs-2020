/**
 * The method sortedINsertion receives a sorted array a with na alements and
 * inserts e in a positions such that the array remains sorted. 
 * This operation returns the array after the insertion, the new size of the
 * array, and the position at which the new element was inserted.
 */

method sortedInsertion(a:array<int>, na:int, e:int) returns (z:array<int>, nz:int, pos:int)
{

}

function sortedRange(a:array<char>, l:int, h:int):bool
    requires 0 <= l <= h <= a.Length
    reads a
{ forall i, j:: (l <= i < j < h) ==> a[i] <= a[j] }

function sorted(a:array<char>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] }

method insert(a:array<char>, i:int, v:char, n:int)
  requires 0 <= n < a.Length
  requires sorted(a, n)
  modifies a 
  ensures sorted(a, n+1)
