# MLightDP
[![MIT License](https://img.shields.io/badge/license-MIT%20License-blue.svg)](LICENSE.md)
![build](https://github.com/SSoelvsten/mlightdp/workflows/build/badge.svg?branch=master)
![unit tests](https://github.com/SSoelvsten/mlightdp/workflows/unit%20tests/badge.svg?branch=master)
![end-to-end tests](https://github.com/SSoelvsten/mlightdp/workflows/end-to-end%20tests/badge.svg?branch=master)

Zhang and Kifer [[ZK17](#references)] designed the language LightDP in which
they track the distance of a variable, i.e. how different its values are during
two executions on almost identical inputs. If the returned expression has
distance zero, then it returns identical values in both executions. Using the
notion of randomness alignment they allow noise to compensate for any non-zero
distance at a cost to the privacy budget. This is all encapsulated in a type
system and program transformations, such that if a program type checks and the
transformed program is validated by off-the-shelf verification software, then a
program is differentially private [[ZK17](#references)]. Furthermore, they
implement a small prototype for LightDP in Python capable of type checking and
transforming a Python program [[Wan+17](#references)].

We follow up on the work of Zhang and Kifer by implementing a tool in OCaml
capable of parsing, type checking and transforming a LightDP program into an
input for our software verification tool of choice, Dafny
[[Lei10](#references)]. The primary goal of this project, aptly named
_MLightDP_, is to hopefully provide a less prototypical and more fully fleshed
experience than the current Python prototype of [[Wan+17](#references)].

<!-- markdown-toc start - Don't edit this section. Run M-x markdown-toc-refresh-toc -->
**Table of Contents**

- [MLightDP](#mlightdp)
    - [Dependencies](#dependencies)
    - [Usage](#usage)
    - [Examples](#examples)
    - [References](#references)

<!-- markdown-toc end -->

## Dependencies
To compile the source code and run our tool, one needs to have the _OCaml_
compiler installed together with the _opam_ packages `menhir` and `ounit`.

To verify the transformed program, one needs [Dafny version
2.3.0](https://github.com/dafny-lang/dafny/releases/tag/v2.3.0) or higher.
Versions 2.0 and higher of Dafny may be enough.

## Usage
By merely writing `make` one should be able to freshly compile the source code
and run the compiled tool on all the examples present in _examples/_.

**Compilation and usage**

For more fine-grained control than the target above is provided in the following
targets.

| Target              | Effect                                                                        |
|---------------------|-------------------------------------------------------------------------------|
| `compile`           | Compile the MLightDP tool with OCaml                                          |
| `clean`             | Remove all compilation from OCaml                                             |
| `run I=<filename>`  | Run the MLightDP tool on _<filename>_ (default: _examples/sparsevector.mldp_) |
| `examples`          | The same as `run`, but for all examples simultaneously                        |
| `clean-examples`    | Remove all compiled examples of the MLightDP tool                             |

**Unit Tests**

All tests can be compiled and run with `make test`. More precisely one can choose
to only run some of the unit tests with the following targets.

| Target             | Tests                                        |
|--------------------|----------------------------------------------|
| `make test-parser` | Run unit tests for AST creation from strings |
| `make test-menhir` | Get Menhir output for shift-reduce conflicts |
| `make test-semant` | Test semantic analysis step                  |

As one can see, we do yet not cover the _refinement_ or the _differential
privacy type checking_ steps in the unit testing. Currently these are only
tested by the examples.

## Examples
In _examples/_ one can find 6 examples that all compile with our tool. We mark
in the list below the examples where the transformed output is verified by
Dafny.

- [X] `helloise.mldp`: The simplest possible program based on the presentation
      of _randomness alignment_ in [[Wan+19](#references)].

- [X] `sparse_vector.mldp`: The running example in [[ZK17](#references)], that
      outputs boolean values detailing the relation between the query results
      and a given threshold.

- [X] `numerical_sparse_vector.mldp`: A variation of the `sparse_vector` example
      from [[ZK17](#references)].

- [X] `gap_sparse_vector.mldp`: A variation of the `sparse_vector` example
      from [[Wan+19](#references)].

- [ ] `partial_sum.mldp`: A summation algorithm from [[ZK17](#references)].

- [X] `sum.mldp`: A variant of `sum` on simpler to reason about input.

- [ ] `smart_sum.mldp`: A more complicated summation algorithm also from
      [[ZK17](#references)].

## References

- [Lei10] Rustan Leino.
     _“Dafny: An Automatic Program Verifier for Functional Correctness”._
     In: _16th International Conference, LPAR-16, Dakar, Senegal_.
     Springer Berlin Heidelberg,
     Apr. 2010,
     pp. 348–370.

- [Wan+17] Yuxin Wang, Zeyu Ding, Guanhong Wang, Daniel Kifer, and Danfeng Zhang.
           _“lightdp”_.
           URL: [github.com/yxwangcs/lightdp](https://github.com/yxwangcs/lightdp) .
           2017

- [Wan+19] Yuxin Wang, Zeyu Ding, Guanhong Wang, Daniel Kifer, and Danfeng Zhang.
           _“Proving Differential Privacy with Shadow Execution”_.
           In: _Proceedings of the 40th ACM SIGPLAN Conference on Programming Language Design and Implementation_.
           PLDI 2019. Phoenix, AZ,
           USA: ACM, 2019,
           pp. 655 - 669

- [ZK17] Danfeng Zhang and Daniel Kifer.
         _“LightDP: towards automating differential privacy proofs”_.
         In: _Proceedings of the 44th ACM SIGPLAN Symposium on Principles of Programming Languages._
         POPL 2017.
         ACM Press, 2017.


