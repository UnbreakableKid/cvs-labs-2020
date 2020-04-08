/*
 * For this exercise, you'll have to implement and verify a set of positive
 * integers using an underlying array.
 *
 * As always, you should, for each method, use the strongest post-conditions
 * and the weakest pre-conditions possible.
 * 
 * The set should follow usual restrictions for a set (no repetitions) plus 
 * that all of its elements must be positive.
 * 
 * In the specification and  implementation of the set you should start by
 * defining the representation invariant for each instance of the set, and
 * the abstract invariant. To define the abstract invariant you will need to
 * make use of ghost variables; variables that help to obtain a better
 * specification but do not influence the execution of the code.
 *
 * Regarding the available operations, it is possible to verify if a given
 * element is in the array. This operation receives an int X and return a
 * boolean; true if X is in the set, false otherwise.
 *
 * Another operation available is the addition of an element to the set.
 * Given an int X, this operation adds X to the set and returns nothing.
 */


class PositiveSet {
  
  
  ghost var s:set<int>;
  var a:array<int>;
  var n:int;

  function repInv() : bool
  reads `a, `n, a
  {
    0 < a.Length
    &&
    0 <= n <= a.Length
    &&
    forall i,j :: (0 <= i < n && 0 <= j < n) ==> (i != j ==> a[i] != a[j])
    &&
    forall i :: 0 <= i < n ==> a[i] > 0
  }

  function sound() : bool
  reads `n, `s, `a, a
  requires repInv()
  {
    n == |s|
    &&
    forall k :: k in s <==> exists l :: 0 <= l < n && a[l] == k
  }

  function absInv() : bool
  reads `n, `s, `a, a
  {
    repInv() && sound()
  }

  constructor (size:int)
  requires size > 0
  ensures absInv()
  {
    a := new int[size];
    n := 0;

    s := {};
  }

  method find(e:int) returns (z:int)
  requires absInv()
  ensures absInv()
  ensures -1 <= z < n;
  ensures z >= 0 ==> a[z] == e
  ensures z < 0 ==> forall i :: 0 <= i < n ==> a[i] != e
  {

    var i := 0;

    while(i < n)
    decreases n - i
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] != e
    {
      if(a[i] == e) {
        return i;
      }

      i := i + 1;
    }

    return -1;

  }

  method add(e:int)
  modifies a, `n, `s
  requires absInv()
  requires n < a.Length
  requires e > 0
  ensures absInv()
  /*
    ensures n == old(n) + 1
    ensures forall i :: 0 <= i < old(n) ==> a[i] == old(a[i])
    ensures a[old(n)] == e

    Hard and verbose to express. Not that those ensures are not correct. They
    are correct if e is not on this set. However if e is indeed in this set,
    those post-conditions are incorrect. One could change them to take into
    account that fact. One option would be to add a pre-condition, nonetheless,
    we wish to have the weakest pre-conditions possible. Another option
    is to use an implication. Despite correct, that would be somewhat verbose
    and error prone. The best option is to make use of the abstract
    representation, and express the post-condition by means of the ghost
    variable set:
  */
  ensures s == old(s) + {e}
  /*
    if e not in s then the post-condition is correct, and if e is in s the
    post-condition is also correct, as s will not change.
  */
  {
    /*
      Taking into account that we do not have as pre-condition for e to not be in
      this set, we have to verify its presence.
    */

    var i:int := find(e);

    if (i < 0) {
      a[n] := e;
      n := n + 1;

      s := s + {e};

      /*
        Dafny has some trouble ensuring the sound() part of absInv(), more precisely
        that every element in the ghost set is also in the array. We need to give it
        some help. First we start by hinting that every elemet that was in the array
        did not change; that was in the precondtion and remains true. Since we added
        an element e to s (and to a) we just need be certain that it is both 
        collections, hence we give an hint by means of an assertion that e is in a.
      */
      assert forall j :: 0 <= j < n-1 ==> a[j] == old(a[j]);
      assert a[n-1] == e;
      assert forall k :: k in s <==> exists l :: 0 <= l < n && a[l] == k;
    }

  }
  
}