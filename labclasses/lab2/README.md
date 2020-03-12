
Dafny is a programming language developed by Microsoft Research; it has built-in specification constructs which allow for the static formal verification of programs functional correctness (the programs do what they are supposed to do) the code produced.  To specify a Dafny program, it is necessary to define the methods' preconditions and postconditions. Assuming the preconditions of a method, Dafny will try to prove then postconditions based on the method's body; if it cannot prove the postconditions, then the program is not correct since it does not comply with its specification.

A guide on Dafny can be found at : [Click me!](https://rise4fun.com/Dafny/tutorial/Guide)

Lab 2:	

* Install Visual Studio Code (VSC) and open __lab2.dfy__.
* When prompted, install the dafny plug-in and dafny.
* Verify if dafny is working correctly by analysing the errors reported in VSC.
* For each unimplemented method in the __lab2.dfy__ file start by defining the most relaxed preconditions and the most strict postconditions you can think of, then implement the method according to the conditions.


# Equipa docente

João Costa Seco
Eduardo Geraldo