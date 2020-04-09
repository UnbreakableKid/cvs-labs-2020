function sorted(a:array<int>, n:int) : bool 
reads a
requires 0 <= n <= a.Length
{
    forall i, j :: 0 <= j <= i < n ==> a[i] >= a[j]
}
method binaryIndex(a:array<int>, n:int, e:int) returns (z:int)
requires 0 <= n < a.Length
requires sorted(a, n)
ensures sorted(a, n)
ensures -(n + 1) <= z <= n
ensures z >= 0 ==> a[z] == e;
ensures z >= 0 ==> forall i :: 0 <= i < z ==> a[i] <= e
ensures z >= 0 ==> forall i :: z <= i < n ==> a[i] >= e
ensures z < 0 ==> forall i :: 0 <= i < -z-1 ==> a[i] < e
ensures z < 0 ==> forall i :: -z-1 <= i < n ==> a[i] > e
{
    var l:int := 0;
    var r:int := n - 1;
    
    while (l <= r)
    decreases r - l
    invariant 0 <= l <= n
    invariant -1 <= r < n
    invariant forall i :: 0 <= i < l ==> a[i] < e
    invariant forall i :: r < i < n ==> a[i] > e
    {
        var m:int := l + (r - l) / 2;
        assert l <= m <= r;
        if (a[m] < e) {
            l := m + 1;
        } else if (a[m] > e){
            r := m - 1;
        } else {
            return m;
        }
    }
    assert l >= 0;
    return -(l + 1);
}
