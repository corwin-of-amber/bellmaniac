Bellmania Compiler
==================

Bellmania requires Scala, Z3 with Java bindings, and Sketch if you want to use the 
SynthAuto tactic.

Use the included `.project` file for development in Eclipse.

There is also an IntelliJ IDEA project, but it might be out of date. Scala support in IDEA is buggy.

To run the nightly tests:

    lsc ./test/nightly.ls

LiveScript is required to run the script (install with `npm install -g livescript`).
