<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Inquisitive Logic

[![Docker CI][docker-action-shield]][docker-action-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]

[docker-action-shield]: https://github.com/motrellin/inquisitive-logic/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/motrellin/inquisitive-logic/actions/workflows/docker-action.yml

[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://motrellin.github.io/inquisitive-logic/./html/toc.html

This project formalizes inquisitive logic in Rocq, based on the work of e.g. [Ivano Ciardelli](doi.org/10.1007/978-3-031-09706-5).
The current focus lies on (bounded) inquisitive first-order logic, therefore providing a formalization of the basic syntax (using arity types), support and truth semantics, followed by the formalization of a sequent calculus by Litak/Sano whose corresponding paper (Bounded inquistive logics: Sequent calculi and schematic validity) got accepted for [TABLEAUX 2025](https://icetcs.github.io/frocos-itp-tableaux25/tableaux/).
The theory is located under `theories/`.
Some concrete instances of type classes (e.g. signatures) are located under `instances/`.
We also provide some examples (`examples/`) in order to demonstrate the implemented theory.

## Meta

- Author(s):
  + Max Ole Elliger (initial)
- License: [BSD 3-Clause "New" or "Revised" License](LICENSE)
- Compatible Rocq/Coq versions: Developed for 9.0
- Additional dependencies:
  + Autosubst
- Rocq/Coq namespace: `InqLog`
- Related publication(s):
  + [Inquisitive Logic: Consequence and Inference in the Realm of Questions](https://link.springer.com/book/10.1007/978-3-031-09706-5) doi:[10.1007/978-3-031-09706-5](https://doi.org/10.1007/978-3-031-09706-5)
  + [Coherence in inquisitive first-order logic](https://www.sciencedirect.com/science/article/pii/S0168007222000707) doi:[10.1016/j.apal.2022.103155](https://doi.org/10.1016/j.apal.2022.103155)
  + [Bounded inquisitive logic: Sequent calculi and schematic validity](https://icetcs.github.io/frocos-itp-tableaux25/tableaux/)

## Building and installation instructions

The easiest way to install the latest released version of Inquisitive Logic
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-inqlog
```

To instead build and install manually, do:

``` shell
git clone --recurse-submodules https://github.com/motrellin/inquisitive-logic.git
cd inquisitive-logic
make all  # or make -j <number-of-cores-on-your-machine> all
make install
```

## Documentation

This project formalizes inquisitive logic in Rocq, based on the work of e.g. [Ivano Ciardelli](doi.org/10.1007/978-3-031-09706-5).
The current focus lies on (bounded) inquisitive first-order logic, therefore providing a formalization of the basic syntax (using arity types), support and truth semantics, followed by the formalization of a sequent calculus by Litak/Sano whose corresponding paper (Bounded inquistive logics: Sequent calculi and schematic validity) got accepted for [TABLEAUX 2025](https://icetcs.github.io/frocos-itp-tableaux25/tableaux/).

### Repository Structure

- `theories/` provides the main theory, including some preliminary libaries, e.g. `SetoidLib.v`, `ListLib.v`
  + `theories/FO` focuses on inquisitive first-order logic.
- `instances/` provides some concrete of type classes (e.g. signatures).
- `examples/` demonstrates some ongoing examples.

### Contributing

You can find information on how to contribute in the [CONTRIBUTING.md](.github/CONTRIBUTING.md) file.
