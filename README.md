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

[OCaml]: http://caml.inria.fr
[OPAM]: https://opam.ocaml.org
[Batteries]: http://batteries.forge.ocamlcore.org
[Ocamlgraph]: http://ocamlgraph.lri.fr/index.en.html
[Core]: https://opensource.janestreet.com/core/
[Containers]: https://github.com/c-cube/ocaml-containers.git
[Z3]: https://github.com/Z3Prover/z3.git

## Install Duet with OPAM
The easiest way to install Duet is to use [OPAM][].
Once you have cloned the code repository, do the followings:
```sh
$ git clone https://github.com/wslee/duet
$ cd duet
$ ./build
```

Optionally, you may need to set up environment variables to use Z3. 
```sh
$ export (DY)LD_LIBRARY_PATH=[OPAM home directory (e.g., ~/.opam)]/[your OCaml version (e.g., 4.08.0)]/lib/z3:$(DY)LD_LIBRARY_PATH  # add "DY" on a Mac
```

After that, you can directly run ```make```.

## Run the synthesizer
The following options are available. 
* -z3cli Use Z3 via command line interface (make sure the path to z3 is in $PATH). This option is available because sometimes Z3 through OCaml API undesirably behaves. 
* -lbu Learning-based unifier. Turn this option if you want to quickly find a conditional program from a small number of input-output examples. If it is turned off, a decision-tree learning-based algorithm will be used (default: false).
* -fastdt Use a heuristic to compute entropies faster. This helps to find conditional programs more quickly but may result in larger solution programs (default: false). 
* -ex_all Provide all the IO examples upfront. 
* -get_size Get size of a program in the form of s-expression. 
* -all Find all possible solutions and pick the smallest one. This may require more synthesis time, but useful for finding smaller solutions (default: false). 
* -debug print info for debugging.
* -max_size set the maximum size of candidates (default: 32). 
* -max_height set the maximum height of candidates (default: 5). 
* -init_comp_size set the initial size of components. The greater number for this option is given, the smaller solution you will get (default: 1).
* -help  Display this list of options

```sh
# STRING 
$ ./main.native -max_size 400 -lbu tests/string/phone-9-long-repeat.sl 
# BITVEC
$ ./main.native -max_size 10000 -fastdt -ex_all -init_comp_size 3 tests/bitvec/113_10.sl 
# CIRCUIT
$ ./main.native -max_size 128 -max_height 16 tests/circuit/CrCy_10-sbox2-D5-sIn102.sl
```

