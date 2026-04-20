The library `ia63` provides the module `Uint63`.
This module is a copy of the module `uint63_63.ml` in Rocq's kernel
([interface](https://github.com/rocq-prover/rocq/blob/master/kernel/uint63.mli))
([implementation](https://github.com/rocq-prover/rocq/blob/master/kernel/uint63_63.ml)).

The library `ia63` also declares, but does not implement, the module `Array63`.
It is a [virtual library](https://dune.readthedocs.io/en/latest/virtual-libraries.html).
The interface of this module is a fragment of the persistent-array API in Rocq's kernel
([interface](https://github.com/rocq-prover/rocq/blob/master/kernel/parray.mli)).

The libraries `unsafe`, `defensive`, and `persistent`
provide three implementations of the module `Array63`.

* `unsafe` provides *unsafe non-persistent arrays*. They are implemented as
  mutable arrays. Although they obey the interface of persistent arrays, they
  are not persistent. Any attempt to exploit their persistence will lead to
  incorrect results.

* `defensive` provides *safe non-persistent arrays*. They are implemented as
  mutable arrays together with a mutable validity flag. They are not
  persistent. An attempt to exploit their persistent will cause an exception
  at runtime.

* `persistent` provides *persistent arrays*. Their implementation is a copy
  of the module `Parray` in Rocq's kernel
  ([implementation](https://github.com/rocq-prover/rocq/blob/master/kernel/parray.ml)).
