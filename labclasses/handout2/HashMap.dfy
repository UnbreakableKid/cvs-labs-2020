class HashMap{

    var maxElems : int;
    ghost var ghostSet : map<int, char>;
    var n : int;
    var arr : array<seq<(int, char)>>;


    function HashMapInv() : bool
        reads this;
        reads arr;
    {
        maxElems > 0
        && arr.Length == maxElems
        && 0 <= n <= maxElems
        && forall i :: 0 <= i < maxElems ==> |arr[i]| <= n
        && forall i :: 0 <= i < maxElems ==> forall j :: 0 <= j < |arr[i]| ==> arr[i][j].0 % maxElems == i
        && forall i :: 0 <= i < maxElems ==> forall j, k :: 0 <= j < k < |arr[i]| ==> arr[i][j].0 != arr[i][k].0
    }

    function Sound() : bool
        reads this, arr
        requires HashMapInv();
    {
        |ghostSet| == n
        && forall x :: x in ghostSet ==> exists i :: 0 <= i < |arr[x % maxElems]| && arr[x % maxElems][i].0 == x && arr[x % maxElems][i].1 == ghostSet[x]
    }

    function AbsInv() : bool
    reads this, arr;
    { HashMapInv() }

    constructor(s:int, l:real)
        requires s > 0;
        requires l > 0.5;
        ensures AbsInv();
        ensures isEmpty();
    {
        maxElems := s;
        n := 0;

        ghostSet := map[];
        var sequences := new seq<(int, char)>[s];
        var i := 0;
        while(i < s)
            decreases s - i
            invariant 0 <= i <= s
            invariant forall k :: 0 <= k < i ==> |sequences[k]| == 0;
        {
            sequences[i] := [];
            i := i + 1;
        }
        arr := sequences;
    }

    function isEmpty() : bool
        reads this
        reads arr;
        requires AbsInv();
    {
        n == 0
        && forall i :: 0 <= i < maxElems ==> |arr[i]| == 0
    }

    function isFull() : bool
        reads this
        reads arr
        requires AbsInv()
    {
        n == maxElems
    }

    function hashFunc(k:int) : int
        reads this
        reads arr
        requires k >= 0
        requires AbsInv()
    {
        k % maxElems
    }

    method hash(k:int) returns (h:int)
        requires k >= 0;
        requires AbsInv();
        ensures h == hashFunc(k);
        ensures 0 <= h < maxElems;
    {
        h := k % maxElems;
    }

    method put(k:int, v:char)
        modifies this, arr
        requires k >= 0
        requires AbsInv()
        requires !isFull()
        ensures AbsInv()
        ensures n == old(n) + 1 <==> arr[hashFunc(k)] == old(arr[hashFunc(k)]) + [(k,v)]
        ensures exists i :: 0 <= i < |arr[hashFunc(k)]| && arr[hashFunc(k)][i].0 == k;
        // ensures n == old(n) + 1 <==> ghostSet == old(ghostSet)[k := v]
        // ensures k in ghostSet
        ensures !isEmpty()
    {
        var index := hash(k);

        if(forall j :: 0 <= j < |arr[index]| ==> arr[index][j].0 != k) {
            arr[index] := arr[index] + [(k, v)];
            ghostSet := ghostSet[k := v];
            n := n + 1;
            assert arr[index][|arr[index]|-1].0 == k && arr[index][|arr[index]|-1].1 == v;
        }
    }

    method get(k:int, def:char) returns(v:char)
        requires AbsInv()
        requires k >= 0
        ensures AbsInv()
        ensures v != def <==> exists j :: 0 <= j < |arr[hashFunc(k)]| && arr[hashFunc(k)][j].0 == k && arr[hashFunc(k)][j].1 != def
        ensures v == def <==> (forall j :: 0 <= j < |arr[hashFunc(k)]| ==> arr[hashFunc(k)][j].0 != k) || (exists j :: 0 <= j < |arr[hashFunc(k)]| && arr[hashFunc(k)][j].0 == k && arr[hashFunc(k)][j].1 == def)
        // ensures v != def <==> k in ghostSet && ghostSet[k] != def
        // ensures v == def <==> k !in ghostSet || (k in ghostSet && ghostSet[k] == def)
        
    {
        var index := hash(k);

        if(|arr[index]| > 0){
            var i := 0;
            while(i < |arr[index]|)
                decreases |arr[index]| - i
                invariant 0 <= i <= |arr[index]|
                invariant forall j :: 0 <= j < i ==> arr[index][j].0 != k
            {
                if(arr[index][i].0 == k){
                    return arr[index][i].1;
                }

                i := i + 1;
            }
        }
        return def;
    }

    method contains(k:int) returns(z:bool)
        requires AbsInv()
        requires k >= 0
        ensures AbsInv()
        ensures z == true <==> exists j :: 0 <= j < |arr[hashFunc(k)]| && arr[hashFunc(k)][j].0 == k
        ensures z == false <==> forall j :: 0 <= j < |arr[hashFunc(k)]| ==> arr[hashFunc(k)][j].0 != k
        // ensures z == true <==> k in ghostSet
        // ensures z == false <==> k !in ghostSet
    {
        var index := hash(k);

        var i := 0;
        while(i < |arr[index]|)
            decreases |arr[index]| - i
            invariant 0 <= i <= |arr[index]|
            invariant forall j :: 0 <= j < i ==> arr[index][j].0 != k
        {
            if(arr[index][i].0 == k){
                return true;
            }

            i := i + 1;
        }
        return false;
    }
}