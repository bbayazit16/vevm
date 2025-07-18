# Verified VM (VeVM)

A stack-based virtual machine written and verified entirely in Rocq.

The VM supports conditional jump, memory assignments, outputting a result (halting with value), and manipulation of items in the stack (which is fairly easy to extend, simply by modifying [Instruction.v](Instruction.v) and copying proof cases based on the argument count). So, all the major instructions that may need 'different' proof cases are covered, and any other instruction is very easy to add.

The VM also features a concept of 'fuel' to prevent itself from running forever. Within the interpret function, the VM is given an initial fuel value, and the interpret function consumes one unit for each instruction executed. If the fuel runs out, the VM halts with an error.

## Verification

The operational semantics for the language are defined in [Semantics.v](Semantics.v).

Below are some of the major proofs in [VmProofs.v](VmProofs.v). These are the most important ones, but there are many other lemmas and theorems that are not listed here:

- Soundness and completeness of the interpret function with respect to the semantics.
- Soundness and completeness of the interpret all function with respect to the semantics.
- If the VM succeeds with a given fuel and outputs `a`, it must also output `a` with a fuel value higher than the original.
- Proofs regarding halting and terminal state.
- Lemmas about the empty program's behaviour.

## Building and Extraction

Run `make` to build the project. This invokes `coq_makefile` to generate another Makefile, which is then executed by the original Makefile. Because of this, you don't need to run `coq_makefile` each time after modifying `_CoqProject`.

Extraction to OCaml is supported, and done automatically by the `make` command.

## License

VeVM is licensed under the MIT License. See the [LICENSE](LICENSE) file for more details.
