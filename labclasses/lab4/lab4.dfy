/**
 * The method sortedINsertion receives a sorted array a with na alements and
 * inserts e in a positions such that the array remains sorted. 
 * This operation returns the array after the insertion, the new size of the
 * array, and the position at which the new element was inserted.
 */

// method sortedInsertion(a:array<int>, na:int, e:int) returns (z:array<int>,nz:int, pos:int)
//     requires 0 < na <= a.Length
//     requires sorted(a, na)
//     requires e >= 0
//     ensures 0 < nz <= z.Length
//     ensures sorted(z, nz)
//     ensures pos >= 0
// {
 
// }

function sortedRange(a:array<char>, l:int, h:int):bool
    requires 0 <= l <= h <= a.Length
    reads a
{ forall i, j:: (l <= i < j < h) ==> a[i] <= a[j] }

function sorted(a:array<char>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] }


method orderedInsert(a:array<char>, v:char, n:int)
    requires 0 <= n < a.Length
    requires sorted(a, n)
    ensures sorted(a, n+1)
    modifies a 
{
    if(n > 0)
    {
        a[n] := a[n-1];
    }
    var i := n;
    while(i > 0 && v < a[i-1])
        decreases i
        invariant 0 <= i <= n+1
        invariant sorted(a, n+1)
        invariant forall k:: i < k < n+1 ==> v <= a[k]
    {
        a[i] := a[i-1];
        i := i - 1;
    }
    a[i] := v;
}