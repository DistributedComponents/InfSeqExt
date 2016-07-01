# InfSeqExt
InfSeqExt is collection of Coq libraries for reasoning inductively and coinductively on infinite sequences, based on an [earlier library](http://ieeexplore.ieee.org/xpls/abs_all.jsp?arnumber=5198503) by Deng and Monin.

This project uses [`coqproject.sh`](https://github.com/dwoos/coqproject) for dependency management. To build the libraries, first run `./configure` in the base directory and then run `make`. 

## `infseq.v`
This file contains the main definitions and results:
* definition of infinite sequences
* definitions and notations for modal operators and connectors
* lemmas about modal operators and connectors
* tactics

## `map.v`
This file contains corecursive definitions of `map` and `zip` functions for use on infinite sequences, and related lemmas.

## `exteq.v`
This file contains a definition of extensional equality for infinite sequences, and related lemmas.

## `subseq.v`
This file contains a definition of infinite subsequences and related lemmas.

## `classical.v`
This file contains lemmas on modal operators and connectors when assuming classical logic (excluded middle).
