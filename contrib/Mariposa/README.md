Mariposa
========

Mariposa is a tool for perturbing SMT-LIB2-formatted files. It
produces files that are semantically equivalent to its inputs but
syntactically different, and can be used to test the stability of SMT
solvers.

Mariposa's handling of the SMT-LIB2 format is incomplete, but it
should work on all `.smt2` files produced by Boogie and F*.

Installing Mariposa
-------------------

The `Mariposa.sln` file is tested to work with Visual Studio 2015 and
with Mono on macOS. Mariposa relies on FsLexYacc, which should be
installed using NuGet's "Restore Packages" procedure. Note that it
might be necessary to reload the solution file after installing
FsLexYacc, as it includes compilation targets which VS doesn't seem to
discover until the solution is reloaded.

Running Mariposa
----------------
Mariposa is run as follows:

```
Mariposa.exe <input.smt2> <output.smt2> <name of perturbation> [<arguments to perturbation>]
```
