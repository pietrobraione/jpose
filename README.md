# jPOSE: Path-Optimal Symbolic Execution, in Java.

This repository contains jPOSE, a prototype implementation of path-optimal symbolic execution. To compile and run it you need Java (at least version 21), and [Z3](https://github.com/Z3Prover/z3). This repository comes with an [Eclipse IDE](https://eclipseide.org/) project, so the easiest way to build it is to import the content of the repo under the Eclipse IDE and let the IDE do its thing. Version 2024-09 of the Eclipse IDE correctly builds jPOSE, so we strongly advice to use it. Previous versions of the Eclipse IDE have a bug in the Eclipse Java compiler (the IDE's Java compiler) that prevents jPOSE to be correctly built: The Eclipse IDE will happily build the project, but running the resulting jPOSE application will raise a java.lang.VerifyException or a java.lang.MatchException at runtime. If you really want to use a version of the Eclipse IDE previous than 2024-09, to circumvent the bug you need to compile the jpose.semantics.interpreter.Interpreter class with a different compiler, e.g. the javac compiler that comes with a standard JDK. My routine is the following: supposing you have cloned the repository in /home/myself/git/jpose, then:

    $ cd /home/myself/git/jpose/src
    $ javac --module-path . -g jpose/semantics/interpreter/Interpreter.java
    $ mv jpose/semantics/interpreter/Interpreter.class ../bin/jpose/semantics/interpreter/.
    
Note also that whenever you modify a Java source file the Eclipse IDE might recompile the jpose.semantics.interpreter.Interpreter class, so consider that, if you want to modify the code of jPOSE, after that you might need to repeat the above procedure.

jPOSE is a breadth-first symbolic executor for programs expressed in a small imperative programming language. To run jPOSE from the command line, you can do it as follows:

    $ java --module-path /home/myself/git/jpose/bin:/home/myself/git/jpose/lib -m jpose/jpose.Main <arguments>

but you can also more conveniently run it from the Eclipse IDE. jPOSE has a sketchy help that you can read by running it with the argument -h. An example of a possible execution of the tool is:

    $ java --module-path /home/myself/git/jpose/bin:/home/myself/git/jpose/lib -m jpose/jpose.Main -p -z3 /usr/bin/z3 dll_add.txt 100

It runs the dll_add.txt example up to depth 100, pruning the infeasible states by using Z3 (option -p), where the Z3 executable is installed at /usr/bin (option -z3). At the end of symbolic execution jPOSE will print the configurations (current program, heap, path condition and next subexpression to evaluate) reached after 100 execution steps.

Some notes on the small programming language that you must use to write the programs you want to symbolically execute with this prototype. It comes with some limitations, that you can mostly work around:

* All fields must have different names even if they belong to different classes. Do not reuse field names across classes or you will confuse the tool.
* There is no sequential composition: Use let-binding, perhaps by assigning to dummy variables.
* There are ifs, but there are no loops (for, while): Use method recursion instead.
* There is a boolean type, but it is really meant only for conditional statements. Please do not use it as a type for fields and variables since it is not very well supported by the tool (returning boolean from methods seems not to cause issues, however).
* All methods have exactly one parameter. Use a suitable object if you want more (or less) than one parameter.

The grammar of the language is reported in the package jpose.parser. The classes in it implement a set of LL parsers based on parser combinators that *are* the grammar of the language. For example, if you want to know the syntax of method declarations, read the source code of the parse method in the ParserMethod class. Alas, due to the need of keeping the grammar LL there are lots of silly parentheses, and you are not even free to add parentheses where you want. Refer the grammar or the examples: The treemap.txt example is quite comprehensive and also shows the previously cited techniques to circumvent the limitations of the language. Another limitation of the parser is that it does not do any semantic error checking, especially of typing errors. Everything is terribly dynamic: If you do a typing error this is detected at runtime, and the typical effect is that the erroneous state is killed. When a state is killed this just means it has not a successor, which makes it sometimes indistinguishable from a final state. Other times, more conveniently, an exception is raised, which however is not much indicative of the issue.  So if your symbolic execution has less end states than you think, maybe it is because you introduced some bug in the program under analysis. My advice is: Use jPOSE to run your program with some concrete inputs (a.k.a., tests) and see if you obtain exactly one end state, and this end state is the one you expect. When you are pretty sure that your program is correct execute it symbolically.

For what concerns the examples included in the repo, you can find them in the examples directory. The biggest are:

* avl.txt: avl tree implementation;
* dll.txt: doubly linked list implementation;
* ncll.txt: node caching linked list implementation;
* treemap.txt: treemap data structure implemented as a red-black tree.

Do not run directly these files, because they only contain the classes definitions: you shall run the files avl_<...>.txt, dll_<...>.txt, ncll_<...>.txt and treemap_<...>.txt, that contain a main program invoking one of the methods of the above classes. For instance, if you want to symbolically execute the add method of the doubly linked list class, run the dll_add.txt file. Note that if you give the run tool the option -l to produce all the leaves you must provide a depth that is at least one more than the maximum depth; otherwise, it will produce the leaves encountered up to depth - 1. None of the example programs have a depth greater than 600.

For your convenience we provided a shell script that runs all the examples. Open a shell, move to the examples directory, put the scripts directory and Z3 on your path, and run `run_all_pose`. Note that some experiments run for a long time, at least on my laptop.

A disclaimer: this tool is a prototype aimed at demonstrating the concept of path-optimal symbolic execution, not an application meant to execute large-scale programs. The tool is, in general, slow and memory-consuming. If its execution crashes by raising a memory exhaustion exception, crank up the stack and the heap memory of the JVM (to execute the examples in this repo we use -Xss1024m -Xms8192m). Expect in any case the execution times to suddenly explode when states start to become big, a thing that usually happens at high depths. We did some minimal optimizations to have decent times with the experiments in this repo, but on other programs your mileage may vary.

