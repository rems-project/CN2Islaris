# CN2Islaris
CN2Islaris is an experimental extension of
[CN](https://github.com/rems-project/cerberus) and
[Islaris](https://github.com/rems-project/islaris/tree/CN2Islaris) to verify
binaries (semi-)automatically. It's not meant to be used on production binaries yet.

After a user defines and automatically verifies the type specification of a C
function with CN, CN2Islaris translates this specification to Islaris with a
default Coq proof. To guide this translation process, CN2Islaris uses debug data
that is parses using [read-dwarf](https://github.com/rems-project/read-dwarf).

## External dependencies

Install OCaml's `opam` package manager and the `Rust` programming language along
with its package manager `cargo` on your system.

Add `~/.cargo/bin` to your PATH.

## Installation

Clone this repository and its submodules using

```
$ git clone --recurse-submodules https://github.com/rems-project/CN2Islaris.git
```

and run the install script

```
$ cd CN2Islaris
$ ./install.sh
```

This will take some time.
It builds and installs all REMS dependencies.
Say yes if `opam` asks to install packages.
All `opam` packages will be installed in an isolated environment (opam switch).
The Rust binaries will be installed in `~/.cargo/bin`.

## Example

To run CN2Islaris on one of the examples, use the Makefile in the `examples` directory:
```
$ eval $(opam env)
$ cd examples
$ make -s SOURCES=incr_unsigned.c OPTIMIZATION=2
```

This will type-check `incr_unsigned.c` in CN, compile it with optimization level
2, translate the CN specification to Islaris, and check if the default proof is
sufficient to prove the correctness of the binary.

On success, the command returns without any error. In case of any errors, remove
the `-s` flag for debug output. The command above should successfully generate following output:

```
cc: compiling incr_unsigned.c
objdump: generating dump
read-dwarf: generating html output
tail: removing unparsable header of dump for islaris
islaris: generating assembly instruction traces
islaris: compiling coq isla traces
         gcc frontend/stubs.o        
      coqdep fromCN/incr_unsigned/O2/instructions/.fromCN.incr_unsigned.O2.theory.d
        coqc fromCN/incr_unsigned/O2/instructions/a210128.{glob,vo}
        coqc fromCN/incr_unsigned/O2/instructions/a21012c.{glob,vo}
        coqc fromCN/incr_unsigned/O2/instructions/a210124.{glob,vo}
        coqc fromCN/incr_unsigned/O2/instructions/a210120.{glob,vo}
        coqc fromCN/incr_unsigned/O2/instructions/instrs.{glob,vo}
islaris: found 4 instructions          
sed: generating dune file
../islaris/fromCN/incr_unsigned/O2/incr_unsigned.v
cn: verifying ../islaris/fromCN/incr_unsigned/O2/incr_unsigned.elf
cn: generating assembler spec and proof
islaris: checking automatically generated proof
      coqdep fromCN/incr_unsigned/O2/.fromCN.incr_unsigned.theory.d
        coqc fromCN/incr_unsigned/O2/incr_unsigned.{glob,vo}
Tactic call liARun ran for 2.037 secs (1.872u,0.008s) (success)
Tactic call liARun ran for 1.633 secs (1.499u,0.008s) (success)
```

All generated output, including the `incr_unsigned.v` Coq file with the translated
specification and the default proof, can be then found in
`islaris/fromCN/examples/incr_unsigned/O2/`.

## Explore
The pre-generated Islaris files and necessary proof extensions of the examples are located in the `proofs` subfolder.
## Limitations
CN2Islaris currently does not support
- loops
- data types other than (pointer to, array of) unsigned long int
- global variables
- recursive functions