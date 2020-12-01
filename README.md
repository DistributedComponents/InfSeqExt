# InfSeqExt

[![CI][action-shield]][action-link]

[action-shield]: https://github.com/DistributedComponents/InfSeqExt/workflows/CI/badge.svg?branch=master
[action-link]: https://github.com/DistributedComponents/InfSeqExt/actions?query=workflow%3ACI




Coq library for reasoning inductively and coinductively on infinite sequences,
using modal operators similar to those in linear temporal logic (LTL).

## Meta

- Author(s):
  - Yuxin Deng (initial)
  - Jean-Francois Monin (initial)
  - Karl Palmskog
  - Ryan Doenges
- Compatible Coq versions: 8.7 or later
- Additional dependencies: none
- Coq namespace: `InfSeqExt`
- Related publication(s): none

## Building and installation instructions

The easiest way to install InfSeqExt is via
[OPAM](https://opam.ocaml.org/doc/Install.html):
```shell
opam repo add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam install coq-inf-seq-ext
```

To instead build and install manually, do:
```shell
git clone https://github.com/DistributedComponents/InfSeqExt.git
cd InfSeqExt
make   # or make -j <number-of-cores-on-your-machine>
make install
```

## Documentation

InfSeqExt is based on an [earlier library][infseq-paper] by Deng and Monin.
It is intended as a more comprehensive alternative to [Streams][streams-link]
in the Coq standard library. In particular, InfSeqExt provides machinery commonly
used when reasoning about temporal properties of system execution traces, and
follows the modal operator [name conventions][spin-ltl-link] used in the Spin model checker.

### Files

- `infseq.v`: main definitions and results
  - coinductive definition of infinite sequences
  - definitions and notations for modal operators and connectors
      - basic modal operators: `now`, `next`, `consecutive`, `always1`, `always`, `weak_until`, `until`, `release`, `eventually`
      - composite modal operators: `inf_often`, `continuously`
      - modal connectors: `impl_tl` (`->_`), `and_tl` (`/\_`), `or_tl` (`\/_`), `not_tl` (`~_`)
  - lemmas about modal operators and connectors
  - tactics
- `map.v`: corecursive definitions of the `map` and `zip` functions for use on infinite sequences, and related lemmas
- `exteq.v`: coinductive definition of extensional equality (`exteq`) for infinite sequences, and related lemmas
- `subseq.v`: coinductive definitions of infinite subsequences and related lemmas
- `classical.v`: lemmas about modal operators and connectors when assuming classical logic (excluded middle)

### Related libraries

InfSeqExt has some overlap with the less exhaustive [CTLTCTL][ctltctl-link]
and [LTL][ltl-link] Coq contributions, which provide similar machinery.
In contrast to CTLTCTL and LTL, InfSeqExt does not provide a definition
of traces following some labeled reduction relation, nor an explicit
notion of time. Fairness is also left up to library users to define.

[infseq-paper]: http://ieeexplore.ieee.org/xpls/abs_all.jsp?arnumber=5198503
[streams-link]: https://coq.inria.fr/library/Coq.Lists.Streams.html
[spin-ltl-link]: http://spinroot.com/spin/Man/ltl.html
[ctltctl-link]: https://github.com/coq-contribs/ctltctl
[ltl-link]: https://github.com/coq-contribs/ltl
