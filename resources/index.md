---
# This file was generated from `meta.yml`, please do not edit manually.
# Follow the instructions on https://github.com/coq-community/templates to regenerate.
title: Inquisitive Logic
lang: en
header-includes:
  - |
    <style type="text/css"> body {font-family: Arial, Helvetica; margin-left: 5em; font-size: large;} </style>
    <style type="text/css"> h1 {margin-left: 0em; padding: 0px; text-align: center} </style>
    <style type="text/css"> h2 {margin-left: 0em; padding: 0px; color: #580909} </style>
    <style type="text/css"> h3 {margin-left: 1em; padding: 0px; color: #C05001;} </style>
    <style type="text/css"> body { width: 1100px; margin-left: 30px; }</style>
---

<div style="text-align:left"><img src="https://gist.github.com/johan/1007813/raw/a25829510f049194b6404a8f98d22978e8744a6f/octocat.svg" height="25" style="border:0px">
<a href="https://github.com/motrellin/inquisitive-logic">View the project on GitHub</a>
<img src="https://gist.github.com/johan/1007813/raw/a25829510f049194b6404a8f98d22978e8744a6f/octocat.svg" height="25" style="border:0px"></div>

## About

Welcome to the Inquisitive Logic project website!

This project formalizes inquisitive logic in Rocq, based on the work of e.g. [Ivano Ciardelli](doi.org/10.1007/978-3-031-09706-5).
The current focus lies on (bounded) inquisitive first-order logic, therefore providing a formalization of the basic syntax (using arity types), support and truth semantics, followed by the formalization of a sequent calculus by Litak/Sano whose corresponding paper (Bounded inquistive logics: Sequent calculi and schematic validity) got accepted for [TABLEAUX 2025](https://icetcs.github.io/frocos-itp-tableaux25/tableaux/).
The theory is located under `theories/`.
Some concrete instances of type classes (e.g. signatures) are located under `instances/`.
We also provide some examples (`examples/`) in order to demonstrate the implemented theory.

This is an open source project, licensed under the BSD 3-Clause "New" or "Revised" License.

## Get the code

The current stable release of Inquisitive Logic can be [downloaded from GitHub](https://github.com/motrellin/inquisitive-logic/releases).

## Documentation

The coqdoc presentation of the source files can be browsed [here](./html/toc.html)

Related publications, if any, are listed below.

- [Inquisitive Logic: Consequence and Inference in the Realm of Questions](https://link.springer.com/book/10.1007/978-3-031-09706-5) doi:[10.1007/978-3-031-09706-5](https://doi.org/10.1007/978-3-031-09706-5)
- [Coherence in inquisitive first-order logic](https://www.sciencedirect.com/science/article/pii/S0168007222000707) doi:[10.1016/j.apal.2022.103155](https://doi.org/10.1016/j.apal.2022.103155)
- [Bounded inquisitive logic: Sequent calculi and schematic validity](https://icetcs.github.io/frocos-itp-tableaux25/tableaux/)

## Help and contact

- Report issues on [GitHub](https://github.com/motrellin/inquisitive-logic/issues)

## Authors and contributors

- Max Ole Elliger (initial)
