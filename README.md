Bellmania Compiler
==================

Bellmania requires Scala, Z3 with Java bindings, and Sketch if you want to use the 
SynthAuto tactic.

Use the included `.project` file for development in Eclipse.

There is also an IntelliJ IDEA project, but it might be out of date. Scala support in IDEA is buggy.

Some screenshots of the Frontend can be found [here](src/main/scala/examples/screenshots.pdf)
The Compiler from frontend to C++ code is in the `codegen` branch of this repository. Examples of generated code can be found [here](https://github.com/corwin-of-amber/bellmaniac/tree/codegen/examples/cpp/autogenerated)



To run the nightly tests:

    lsc ./test/nightly.ls

LiveScript is required to run the script (install with `npm install -g livescript`).
