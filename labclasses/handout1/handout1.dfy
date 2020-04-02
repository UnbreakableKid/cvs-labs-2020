function sorted(a:array<int>, n:int):bool
    requires 0 <= n <= a.Length
    reads a
{ forall i, j:: (0 <= i < j < n) ==> a[i] <= a[j] }




method binarySearch(a:array<int>, n:int, e:int) returns (z:int)
    requires 0 < n <= a.Length
    requires sorted(a, n)
    ensures -n-1 <= z < n
    ensures z >= 0 ==> a[z] == e
    ensures z < 0 ==> forall k :: 0 <= k < n ==> a[k] != e
    ensures -n <= z < 0 ==> a[-z-1] > e
    ensures z == (-n-1) ==> a[n-1] < e 
{
    var left := 0;
    var right := n;

    var mid := 0;

    while(left < right)
        decreases right - left
        
        invariant 0 <= mid < n
        invariant 0 <= left <= right <= n
        invariant forall k :: right <= k < n ==> a[k] > e
        invariant forall k :: left > k >= 0 ==> a[k] < e
    {
        mid := (left + right) / 2;

        if(a[mid] < e){
            left := mid + 1;
        } else if (a[mid] > e){
            right := mid;
        } else{
            return mid;
        }

    }
    
    z := (right+1) * -1;
}