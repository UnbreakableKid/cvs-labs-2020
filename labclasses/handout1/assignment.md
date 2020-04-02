# CVS 2020 - First Handout Dafny

This first handout is about verifying a simple algorithm involving an array using Dafny. 

The algorithm you should use Dafny to specify, implement, and verify, is the equivalente of `binarySearch` of the Java class `Collections`, with `O(log n)` complexity. The oficial (informal) specification in the Java documentation contains the following paragraphs:

  If the ArrayList contains more than one element with the same value, the method returns only one of the occurrences, and it might return any one of the occurrences, not necessarily the first one.

  If the ArrayList does not contain the specified value, the method returns a negative integer. You can apply the bitwise complement operation (~) to this negative integer to get the index of the first element that is larger than the search value. When inserting the value into the ArrayList, this index should be used as the insertion point to maintain the sort order.

**Notice that Dafny does not have a bitwise complement operator, therefore, it is not possible to follow the exact description provided above. As an alternative, you can obtain the insertion position using the following operation: -z-1 where z is the return of the method (the -1 is necessary to deal with the limit case where the insertion position is zero). **

You should use the following type signature 

```
method binarySearch(a:array<int>, n:int, e:int) returns (z:int)
```

and provide the weakest pre-condition and the stronger post-condition that matches to the specification above. You should prove that the returned index is the right one.

## Evaluation

This handout is worth 5% of the final evaluation. It will be classified from A to F. 

## Submission 

This handout is due on Wednesday, 8th, 23h59. The submission is performed in a google forms in a link to be provided in a later version of this document.