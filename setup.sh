#!/bin/env sh

opam switch create . "4.14.1"
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git

# install isla
opam install -y z3
cd isla
cargo build --release
cd ..

# install isla-lang
cd isla-lang
opam install -y .
cd ..

## install islaris
cd islaris
make builddep
make
cd ..

## install read-dwarf
opam install -y qcheck
cd read-dwarf
opam install -y .
cd ..

## install cerberus
cd cerberus
opam install -y --deps-only ./cerberus-lib.opam ./cerberus.opam
make
make install
opam install -y monomorphic
make install_cn
cd ..