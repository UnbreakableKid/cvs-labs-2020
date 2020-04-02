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
  
  
  constructor (size:int){}

  method find(e:int) returns (z:int){}

  method add(e:int){}
  
}