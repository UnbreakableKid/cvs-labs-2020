//dado na aula 4
function sorted(a:array<int>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] }

// array a, size n, elemento e
// 1 2 3 4 5 6
method BinarySearch(a: array<int>, n: int, e: int) returns (z: int)

    requires 0 < n <= a.Length
    requires sorted(a, n);
    
    ensures z >= 0 && z < n-1 ==> a[z] == e;
    ensures z < 0 ==> forall i :: 0 <= i < n ==> a[i] != e;
    
{
    var left := 0;
    var right := n;
    var mid := 0;

    while (left < right)

    decreases right - left
    invariant 0 <= left <= right <= n;
    invariant 0 <= mid < n;
    invariant forall i :: 0 <= i < left ==> (a[i] < e);
    invariant forall i :: right <= i < n ==> (a[i] > e);

    {
        mid := (left+right) / 2;
        
        if (a[mid] < e) {

            left := mid + 1;
        } 
        
        else if (a[mid] > e) {

            right := mid;
        } 
        
        else {
            return mid;
        }
    }

    z := right + 1;
    
    z := z * - 1;
    
    return z;

}