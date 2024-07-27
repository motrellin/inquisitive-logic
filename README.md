<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Inquisivite Logic

[![Docker CI][docker-action-shield]][docker-action-link]
[![coqdoc][coqdoc-shield]][coqdoc-link]

[docker-action-shield]: https://github.com/motrellin/inqlog/actions/workflows/docker-action.yml/badge.svg?branch=main
[docker-action-link]: https://github.com/motrellin/inqlog/actions/workflows/docker-action.yml

[coqdoc-shield]: https://img.shields.io/badge/docs-coqdoc-blue.svg
[coqdoc-link]: https://motrellin.github.io/inqlog/./docs/toc.html

A formalization of inquisitive logic in Coq, based on the work of
[Ivano Ciardelli](doi.org/10.1007/978-3-031-09706-5).

## Meta

- Author(s):
  + Max Ole Elliger (initial)
- License: [GNU General Public License v3.0 or later](LICENSE)
- Compatible Coq versions: Developed for 8.19.0
- Additional dependencies: none
- Coq namespace: `InqLog`
- Related publication(s): none

## Building and installation instructions

The easiest way to install the latest released version of Inquisivite Logic
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-inqlog
```

To instead build and install manually, do:

``` shell
git clone --recurse-submodules https://github.com/motrellin/inqlog.git
cd inqlog
make all  # or make -j <number-of-cores-on-your-machine> all
make install
```

## Documentation

This project tries to formalize inquisitive logic in Coq. The formalization
is based on the work of [Ivano Ciardelli](doi.org/10.1007/978-3-031-09706-5).

### Contributing

You can find information on how to contribute in the [CONTRIBUTING.md](.github/CONTRIBUTING.md) file.
