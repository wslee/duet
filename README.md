# Duet

Duet is an inductive program synthesizer that combines top-down deduction and bottom-up enumeration. 
Because it targets inductive synthesis, which tries to find a program from input-output examples, 
we support SyGuS instances with input-output examples provided upfront and instances with a functional 
logical specification (e.g., forall x. f(x) = f'(x) where f is a target function to be synthesized and f' 
is a known oracle function). 

## Duet Dependencies 
To build Duet, you need
- [OCaml][] >= 4.08.0
- [OPAM][] >= 1.2.2
- [Batteries][] >= 2.3.1
- [Ocamlgraph][] >= 1.8.7
- [Core][] >= 0.13.1 
- [Containers][] == 2.8.1 
- [Z3][] == 4.8.1 

## Install Sparrow with OPAM
The easiest way to install Duet is to use [OPAM][].
Once you have cloned the code repository, do the followings:
```sh
$ git clone https://github.com/wslee/duet
$ cd duet
$ opam switch create 4.08.0 
$ eval `opam config env`
$ opam install containers containers.2.8.1
$ opam install z3 z3.4.8.1 
$ opam install core batteries ocamlgraph 
```

Optionally, you may need to set up environment variables to use Z3. 
```sh
$ export (DY)LD_LIBRARY_PATH=[OPAM home directory (e.g., ~/.opam]/[OCaml version you installed via OPAM]/lib/z3:$(DY)LD_LIBRARY_PATH  # add "DY" on a Mac
```

After that, you can directly run ```make```.

## Run the synthesizer
```sh
# STRING 
$ ./main.native -max_size 400 -lbu tests/string/phone-9-long-repeat.sl 
# BITVEC
$ ./main.native -max_size 10000 -fastdt -ex_all tests/bitvec/13_10.sl 
# CIRCUIT
$ ./main.native -max_size 128 -max_height 16 tests/circuit/CrCy_10-sbox2-D5-sIn102.sl
```

