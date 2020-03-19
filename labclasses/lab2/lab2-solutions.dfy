/**
    ©João Costa Seco, Eduardo Geraldo, CVS, FCT NOVA, MIEI 2018
    This is the first lab assignment for the Construction and Verification of
    Software of the integrated master in computer science and engineering
    (MIEI) http://www.di.fct.unl.pt/miei

    The piazza page where you can discuss solutions and problems related to
    this lab class is at: piazza.com/fct.unl.pt/spring2019/11159/home

    Your mission is to complete all methods below using dafny. Completely 
    specify the methods by writing the weakest pre-condition and the strongest
    post-condition possible. Implement and verify the methods according to that
    same specification.
 */

/**
    This is a test method just to check if dafny is working properly. 
    Make sure that the invalid assertion 10 != 10 is detected by dafny.
    If so, comment it, and proceed. 
    
    Notice that dafny is capable of deriving general logical properties
    about integer values.
 */
method test(x:int) returns (y:int)
requires true
ensures y == 2*x
{
    assert 10 == 10;
    //assert 10 != 10;
    return 2*x;
}

/**
    Specify and implement method abs below. The functionality of this method
    it to return the absolute value of the value passed as argument.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method abs(x:int) returns (y:int)
    requires true;
    ensures y == x || y == -x;
    ensures y >= 0;
{
    if x >= 0 { return x; } else { return -x; }
}

/**
    Specify and implement the method max. The functionality of this method
    is to return the greatest of the two arguments.

    In the specification define the weakest preconditions and 
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method max(x:int, y:int) returns (z:int)
    requires true
    ensures z == x || z == y;
    ensures z >= x && z >= y;
{
    if x >= y { return x; } else { return y; }
}

/**
    Specify and implement the method min;
    this method returns the lowest of the two arguments.

    As in the exercise above, define the weakest postconditions and 
    the strongest postconditions possible. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method min(x:int, y:int) returns (z:int)

/**
    Specify and implement the method div;
    this method must return the result of the integer division of x by y.

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.

    In this method it is observable that dafny is able to dectect potential
    runtime errors such as a division by zero.
*/
method div(x:int, y:int) returns (z:int)
    requires y != 0
    ensures z == x/y
{
    return x/y;
}

method m() {
    var a := div(1,2);
}

/**
    Specify and implement the method square;
    this method returns x to the power of 2, i.e., x * x.

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method square(x:int) returns (z:int)
requires true
ensures z == x*x && z >= 0
{
    return x*x;
}

/**
    Specify and implement the method module; This method is expected
    to return the remainder of the division of the first argument by
    the second one.

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
*/
method modulo(x:int, y:int) returns (z:int)
    requires y != 0;
    ensures x/y * y + z == x;
{
    return x % y;
}

method quotient(x:int, y:int) returns (q:int, r:int)
    requires y != 0;
    ensures q * y + r == x;
{
    q := x / y;
    r := x % y;
}

/**
    Specify and implement the method sign. This method extraccts the signal
    of the argument. When the result is multiplied by a positive value,
    the that value ets the same signal as the argument.

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.
    
    Notice that in Dafny it is possible to use implications and conditionals.
    Implication:
        <x ==> y>
    Conditional:
        <if x then a else b>
    A conditional must have the two branches, then and else.
*/
method sign(x:int) returns (z:int)
    requires true
    ensures z == 0 <==> x >= 0
    ensures z == 1 <==> x < 0
{
    if x < 0 { return 1; } else { return 0; }
}

/**
    In Dafny, functions consist of one expression (usually an if then else) and are not compiled.
    As such, it is not possible to call them in methods' bodies; it is only possible to use
    functions in specifications.

    Functions usually inductively define some method we are trying to prove correct. Despite
    inefficient, in some cases, it is easier to define recursive algorithms. This way, we can
    check the correctness of an iterative algorithm against its recursive definition.

    The use of functions enables simpler specifications which are less likely to be
    wrong.

    This function has one case base which is:
        sumAllPositive(0) == 0
    and the step is:
        sumAllPositive(n) == n + summallpositive(n - 1)
*/
function sumAllPositive(n:int) : int
decreases n
requires n >= 0
{
    if (n == 0) then 0 else n + sumAllPositive(n - 1)
}

/**
    Using the function above, specify and implement the method
    computeSumAllPositive; this method returns the sum of all 
    all positive numbers plus zero.

    In the specification define the weakest preconditions and
    the strongest postconditions you can think of. Implement the method
    so that it satisfies the post-conditions assuming the pre-conditions.

    For instance for x == 3 the result is 6.

    Suggestion: instead of decrementing the wile control
    variable each iteration, start at 0 and increment it.
*/

method computeSumAllPositive(n:int) returns (z:int)
    requires n >= 0
    ensures z == sumAllPositive(n)
{
    var i := 0;
    var sum := 0;
    assert sum == sumAllPositive(i);
    while i < n 
        decreases n - i
        invariant 0 <= i <= n
        invariant sum == sumAllPositive(i)
    {
        assert sum == sumAllPositive(i);
        i := i + 1;
        assert sum == sumAllPositive(i-1);
        sum := i + sum;
        assert sum == i + sumAllPositive(i-1);
        assert sumAllPositive(i) == i + sumAllPositive(i-1);
        assert sum == sumAllPositive(i);
    }
    assert i >= n;
    assert i == n;
    return sum;
}

method computeSumAllPositive2(n:int) returns (z:int)
    requires n >= 0
    ensures z == n * (n+1) / 2
{
    var i := 0;
    var sum := 0;
    assert sum == i * (i+1) / 2;
    while i < n 
        decreases n - i
        invariant 0 <= i <= n
        invariant sum == i * (i+1) / 2
    {
        assert sum == i * (i+1) / 2;
        i := i + 1;
        assert sum == (i-1) * (i) / 2;
        sum := i + sum;
        assert sum == i + (i-1) * (i) / 2;
        assert i * (i+1) / 2 == i + (i-1) * (i) / 2;
        assert sum == i * (i+1) / 2;
    }
    assert i >= n;
    assert i == n;
    return sum;
}

method computeSumAllPositive3(n:int) returns (z:int)
    requires n >= 0
    ensures z == n * (n+1) / 2
{
    var i := 0;
    var sum := 0;
    while i <= n 
        decreases n - i
        invariant 0 <= i <= n+1
        invariant sum == i * (i-1) / 2
    {
        sum := i + sum;
        i := i + 1;
    }
    return sum;
}

method computeSumAllPositive4(n:int) returns (z:int)
    requires n >= 0
    ensures z == sumAllPositive(n)
{
    var i := 1;
    var sum := 0;
    while i <= n 
        decreases n - i
        invariant 1 <= i <= n+1
        invariant sum == sumAllPositive(i-1)
    {
        sum := i + sum;
        i := i + 1;
    }
    return sum;
}