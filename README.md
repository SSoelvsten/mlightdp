# MLightDP
[![MIT License](https://img.shields.io/badge/license-MIT%20License-blue.svg)](LICENSE.md)

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
    - [References](#references)

<!-- markdown-toc end -->



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

- [ZK17] Danfeng Zhang and Daniel Kifer.
         _“LightDP: towards automating differential privacy proofs”_.
         In: _Proceedings of the 44th ACM SIGPLAN Symposium on Principles of Programming Languages._
         POPL 2017.
         ACM Press, 2017.


