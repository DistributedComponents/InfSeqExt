# InfSeqExt
InfSeqExt is collection of Coq libraries for reasoning inductively and coinductively on infinite sequences, based on an [earlier library](http://ieeexplore.ieee.org/xpls/abs_all.jsp?arnumber=5198503) by Deng and Monin. InfSeqExt is intended as a more comprehensive alternative to [Streams](https://coq.inria.fr/library/Coq.Lists.Streams.html) in the Coq standard library. In particular, InfSeqExt provides machinery commonly used when reasoning about temporal properties of execution traces produced by distributed systems.

This project uses [`coqproject.sh`](https://github.com/dwoos/coqproject) for dependency management. To build the libraries, first run `./configure` in the base directory and then run `make`. When added as a dependency to another project using `coqproject.sh`, the namespace is `InfSeqExt`, so Coq files that rely on InfSeqExt will typically include `Require Import InfSeqExt.infseq.`

## infseq
This file contains the main definitions and results:
* coinductive definition of infinite sequences
* definitions and notations for modal operators and connectors
  - basic modal operators: `now`, `next`, `consecutive`, `always1`, `always`, `weak_until`, `until`, `release`, `eventually`
  - composite modal operators: `inf_often`, `continuously`
  - modal connectors: `impl_tl` (`->_`), `and_tl` (`/\_`), `or_tl` (`\/_`), `not_tl` (`~_`)
* lemmas about modal operators and connectors
* tactics

## map
This file contains corecursive definitions of the `map` and `zip` functions for use on infinite sequences, and related lemmas.

## exteq
This file contains a coinductive definition of extensional equality (`exteq`) for infinite sequences, and related lemmas.

## subseq
This file contains coinductive definitions of infinite subsequences and related lemmas.

## classical
This file contains lemmas about modal operators and connectors when assuming classical logic (excluded middle).
