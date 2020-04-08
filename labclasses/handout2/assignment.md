# CVS 2020 - First Handout Dafny

For the second Dafny handout, you will have to implement and verify in Dafny a hash map. The hash map takes as key integers and characters as values (the Java equivalent would be HashMap<Integer, Character>). You should follow the typical implementation based on an underlying array of collision buckets and make use of abstract states for your specifications. The map must support the following three operations: element insertion, element retrieval, and element existence test operation.

## Insertion Operation: 
Signature:
```
method put(k:int, v:char)
```

This operation takes as arguments a key of type int and a value of type char. Given the input, the operation stores the pair in the map unless the key already exists in the map, in which vase, the operation has no effect. Consider the following map:

```map = [0->'b', 1->10]```

The operation ```map.put(10, 'e')``` will succeed producing the state ```map = [0->'b', 1->10, 10->'e']``` while the operation ```map.put(1, 'z')``` will not change the state in any way.

## Retrieval Operation: 
Signature:
```
method get(k:int, def:int) returns(v:char)
```

The value retrieval operation given a key passed as argument (```k```) will return the corresponding value. If the value is not in the map, then it will return a default value, also supplies as an argument to the method (```def```).

## Test Operation: 
Signature:
```
method contains(k:int) returns(z:bool)
```
This operation tests whether or not the key (```k```) is in the map. It returns true if there is a mapping in this dictionary for (```k```) and false otherwise.


## Remarks:

For each one of the operations you should provide the **weakest preconditions** and **strongest postcondition** possible. Regarding the object states, you should provide the **strongest invariants** possible.

The [Dafny reference manual](http://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf) has some information that might come in handy.


## Evaluation

This handout is worth 5% of the final evaluation. It will be classified from A to F. 

## Submission 

This handout is due on Wednesday, 15th, 23h59. The submission is performed in a google forms in a link to be provided in a later version of this document.