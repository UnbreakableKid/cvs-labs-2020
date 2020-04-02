function sorted(a:array<int>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] }

method binarySearch(a:array<int>, n:int, e:int) returns (z:int)
    requires 0 <= n <= a.Length
    requires sorted(a, n)
    
{

}