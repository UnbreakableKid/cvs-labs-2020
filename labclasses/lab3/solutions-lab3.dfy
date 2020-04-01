/**
    ©João Costa Seco, Eduardo Geraldo, CVS, FCT NOVA, MIEI 2020
    This is the first lab assignment for the Construction and Verification of
    Software of the integrated master in computer science and engineering
    (MIEI) http://www.di.fct.unl.pt/miei


    Your mission is to complete all methods below using dafny. Completely 
    specify the methods by writing the weakest pre-condition and the strongest
    post-condition possible. Implement and verify the methods according to that
    same specification.
 */



/**
    Specify and implement the method computeDivision; this method yields a
    pair (a, b), where a is the result of the integer division of x by y 
    and b is the remainder the division.
        (a, b) == (x/y, x%y)

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
    
    The implementation of this method should be iterative.

    To return a pair use:
        <return a, b;>

    Note 1: consider as input only non-negative values

    Note 2: in the postconditions avoid using the existing division <x/y>
    and modulo <x%y> operations.
*/
method computeDivision(x:int, y:int) returns (a:int, b:int)
requires x > 0 && y > 0
ensures x == y*a + b
ensures b < y
{
    var n:int := x;
    var cnt:int := 0;
     
    while(n >= y)
    decreases x - cnt * y
    invariant 0 <= n <= x;
    invariant cnt >= 0
    invariant (cnt * y + n) == x
    {
        cnt := cnt + 1;
        n := n - y;
    }

    return cnt, n;

}

/**
    Specify and implement the method computeFactorial; this method returns
    the factorial of x, i.e.m !x. For instance, computeFactorial(3) yields
    the result 6.

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
    
    Hint: you will most likely need to define an auxilliary function.
*/
function factorial(n:int):int
decreases n
requires n >= 0
{
    if(n <= 1) then 1 else n * factorial(n - 1)
}

method computeFactorial(x:int) returns (z:int)
requires x >= 0
ensures z == factorial(x)
{
    var n:int := 1;
    var acc := 1;


    while(n <= x)
    decreases x - n
    invariant 1 <= n <= x + 1
    invariant acc == factorial(n - 1)
    {
        acc := acc * n;
        n := n + 1;
    }

    return acc;
}

/**
    Specify and implement the method computeFibbonaci; this method returns
    the result of the fibonacci function over the arument x.
    For example, computeFibonacci(3) == 2

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.

    See: https://en.wikipedia.org/wiki/Fibonacci_number
*/
function fib(n:int):int
decreases n
requires n >= 0
{
    if(n <= 1) then n else fib(n-1) + fib (n-2)
}

method computeFibonacci(x:int) returns (z:int)
requires x >= 0
ensures z == fib(x)
{
    if(x <= 1) {
        return x;
    }


    var n:int := 2;
    var acc1:int := 1;
    var acc2:int := 0;

    assert acc1 + acc2 == fib(n);

    while(n <= x)
    decreases x - n
    invariant 2 <= n <= x + 1
    invariant acc1 == fib(n-1)
    invariant acc2 == fib(n-2)
    invariant acc1 + acc2 == fib(n)
    {
        var temp:int := acc1 + acc2;
        acc2 := acc1;
        acc1 := temp;
        n := n+1;
    }

    return acc1;
}


/**
    Specify and implement method indexOf below. The functionality of this method
    it to return the index of the first occurrence of elem in array a.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method indexOf(a:array<int>, n:int, elem:int) returns (z:int)
requires 0 <= n <= a.Length
ensures z < n
ensures (z >= 0) ==> a[z] == elem
ensures z < 0 <==> forall i :: (0 <= i < n) ==> a[i] != elem
{
    var idx:int := 0;

    while(idx < n)
    decreases n - idx
    invariant 0 <= idx <= n
    invariant forall i :: (0 <= i < idx) ==> a[i] != elem
    {
        if(a[idx] == elem){
            return idx;
        }
        idx := idx +1;
    }

    assert forall i :: (0 <= i < n) ==> a[i] != elem;

    return -1;
}

/**
    Specify and implement method max. This method retuns a pair where
    the first element is the greatest value in the array and the second
    element of the pair is its index. The first argument is the array
    to search and the second one the number of elements in the array.


    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method max(a:array<int>, n:int) returns (maxVal:int, maxIdx:int)
requires 0 < n < a.Length
ensures 0 <= maxIdx < n
ensures forall i :: (0 <= i < n) ==> maxVal >= a[i]
{
    var i:int := 1;
    var mi:int := 0;

    while(i < n)
    decreases n - i
    invariant 0 <= i <= n
    invariant 0 <= mi < i
    invariant forall j :: (0 <= j < i) ==> a[mi] >= a[j]
    {
        if(a[i] >= a[mi]) {
            mi := i;
        }
        i := i + 1;
    }

    return a[mi], mi;
}

/**
    Specify and implement method min. This method retuns a pair where
    the first element is the lowest value in the array and the second
    element of the pair is its index. The first argument is the array
    to search and the second one the number of elements in the array.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method min(a:array<int>, n:int) returns (minVal:int, minIdx:int)
requires n > 0 && n <=a.Length
ensures 0 <= minIdx < n
ensures forall i :: (0 <= i < n) ==> minVal <= a[i]
{

    var i:int := 1;
    var mi:int := 0;

    while(i < n)
    decreases n - i
    invariant 0 <= i <= n
    invariant 0 <= mi < i
    invariant forall j :: (0 <= j < i) ==> a[mi] <= a[j]
    {
        if(a[i] <= a[mi]) {
            mi := i;
        }
        i := i + 1;
    }

    return a[mi], mi;
}
/**
    Specify and implement method fillK. This method retuns true if and only
    if the first count elements of array a are equal to k.
    The first argument is the array, the second one is the number of 
    elements in the array, the third argument is the value to use as
    comparison, and the last argument is the number of times that k must
    be appear in the array.
    
    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method fillK(a:array<int>, n:int, k:int, count:int) returns (b:bool)
requires 0 <= count <= n < a.Length
ensures  b <==> forall i :: (0 <= i < count) ==> a[i] == k
{
    var i:int := 0;
    
    while(i < count )
    decreases count - i
    invariant 0 <= i <= count
    invariant forall j :: (0 <= j < i) ==> a[j] == k
    {
        if(a[i] != k) {
            return false;
        }
        i := i + 1;
    }
    return true;
}

method fillk(a:array<int>, n:int, k:int, count:int) returns (b:bool)
requires 0 <= count <= n < a.Length
ensures  b <==> forall i :: (0 <= i < count) ==> a[i] == k
{
    var i:int := 0;
    
    while(i < count )
    decreases count - i
    invariant 0 <= i <= count
    invariant forall j :: (0 <= j < i) ==> a[j] == k
    {
        if(a[i] != k) {
            return false;
        }
        i := i + 1;
    }
    return true;
}

/**
    Specify and implement method containsSubString. This method tests wheteher or
    not the cahr array a contains the char array b. 
    If a contains b, then the method returns the offset of b on a.
    If a does not contain n then the method returns an illegal index.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.

    Hint: you may want to define an auxiliary function and method.
*/
function substring(a:array<char>, b:array<char>, pos:int, n:int):bool
reads a,b
requires a.Length >= b.Length
requires 0 <= n <= b.Length
requires 0 <= pos < a.Length - b.Length
{
    forall i :: (0 <= i < n) ==> a[pos + i] == b[i]
}

method isSubString(a:array<char>, b:array<char>, pos:int) returns (z:bool)
requires a.Length >= b.Length
requires 0 <= pos < a.Length - b.Length
ensures z <==> substring(a,b,pos,b.Length)
{

    var i:int := 0;

    while(i < b.Length)
    decreases b.Length - i
    invariant 0 <= i <= b.Length
    invariant substring(a, b, pos, i)
    {
        if(a[pos + i] != b[i]){
            return false;
        }
        i := i +1;
    }

    return true;
}


method containsSubString(a:array<char>, b:array<char>) returns (pos:int)
    requires a.Length >= b.Length
    ensures pos < a.Length - b.Length
    ensures pos >= 0 ==> substring(a,b,pos,b.Length)
    ensures pos < 0 <==> forall i :: (0 <= i < a.Length-b.Length) ==> !substring(a,b,i,b.Length)
{
    
    var i:int := 0;

    while (i < a.Length - b.Length)
    decreases a.Length - b.Length - i
    invariant 0 <= i <= a.Length - b.Length
    invariant forall j :: (0 <= j < i) ==> !substring(a,b,j,b.Length)
    {
        var isss:bool := isSubString(a,b,i);
        if(isss) {
            return i;
        }
        i := i + 1;
    }

    return -1;
}
    
/**
    Specify and implement method resize. This method returns a new array
    which Length is the double of the length of the array supplied as 
    argument.

    If the length of the array supplied as argument is zero, then set the
    length of b to a constant of your choice.

    All the elements of a should be inserted, in the same order, in b.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method resize(a:array<int>) returns (z:array<int>)
requires true
//ensures z.Length > a.Length
//more specific:~
requires a.Length > 0
ensures z.Length == 2 * a.Length
ensures forall i :: (0 <= i < a.Length) ==> a[i] == z[i]
{

    z := new int[a.Length * 2];

    var i:int := 0;

    while(i < a.Length)
    decreases a.Length - i
    invariant 0 <= i <= a.Length
    invariant forall j :: (0 <= j < i) ==> a[j] == z[j]
    {
        z[i] := a[i];
        i := i + 1;
    }

}

/**
    Specify and implement method reverse. This method returns a new array b
    in which the elements of a appear in the inverse order.

    For instance the inverse of array a, a == [0, 1, 5, *, *], where '*'
    denotes an uninitialized array position, results i:
    b == [5, 1, 0, *, *].

    The first parameter is the array to reverse and the second one
    is the number of values in a.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method reverse(a:array<int>, n:int) returns (z:array<int>)
requires 0 <= n <= a.Length
ensures a.Length == z.Length
ensures forall i :: (0 <= i < n) ==> a[i] == z[n-1 - i]
{

    z := new int[a.Length];
    var i:int := 0;
    
    while(i < n)
    decreases n - i
    invariant 0 <= i <= n
    invariant forall j :: (0 <= j < i) ==> a[j] == z[n-1 - j]
    {
        z[n-1 - i] := a[i];
        i := i + 1;
    }

}

/**
    Specify and implement method push.
    This method accepts three arguments, an array, the number of elements in the
    array, and the new element.

    It will insert the new element at the end of the array and return a pair
    with the modified array and the new number of elements in the array.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.

    Note: You will need to use a modifies clause:
        <modifies a>.
    This clause lets Dafny know that you intend to change the contents of
    array a.
*/
method push(a:array<int>, na:int, elem:int) returns (b:array<int>, nb:int)
requires 0 <= na < a.Length
ensures nb == na + 1
ensures a == b
ensures forall i :: (0 <= i < na) ==> a[i] == b[i]
ensures b[na] == elem
modifies a
{
    a[na] := elem;

    return a, na + 1;
}
/**
    Specify and implement method pop. Given an array and the number of
    elements in it, this method removes the last element of the array and 
    return the modifies array, the number of elements of the modified array
    and the element removed from the array.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method pop(a:array<int>, na:int) returns (b:array<int>, nb:int, elem:int)
requires 0 < na <= a.Length
ensures nb == na - 1
ensures a == b
ensures forall i :: (0 <= i < na - 1) ==> a[i] == b[i]
ensures elem == a[nb]
{
    return a, na - 1, a[na - 1];
}

/**
    Specify and implement method Count. Given an array a and some integer v, 
    this method return the number of occurrences of v in a.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
function count(a:array<int>, n:int, v:int):int
decreases n
requires 0 <= n <= a.Length
reads a
{
    if (n == 0)
    then 0 
    else if (a[n-1] == v) then 1 + count(a, n-1, v) else count(a, n-1, v)
}

method Count(a:array<int>, v:int) returns (z:int)
requires true
ensures z == count(a, a.Length , v)
{
    var i:int := 0;
    var acc:= 0;

    assert acc == count(a, i, v);

    while(i < a.Length)
    decreases a.Length - i;
    invariant 0 <= i <= a.Length
    invariant acc == count(a, i, v)
    {
        if(a[i] == v) {
            acc := acc + 1;
        }
        i := i + 1;
    }

    return acc;
}