# Compilation
This development must be compiled with the latest stable release of
Coq 8.3, namely Coq 8.3pl5, which can be downloaded from

  http://coq.inria.fr/

To compile the source using GNU make, just launch

```console
make
```

from the top level folder (where this `README.md` file is located). The Coq
compiler (`coqc`) should be in your `PATH` for this to work. Depending on
your computer, and on whether you are using the native or the bytecode
version of the Coq compiler, this can take some time (expect 15
minutes with a native compiler). You will be able to see the progress
in your terminal.


# Interactive interpretation
If you want to use the Coq interpreter interactively to explore the
development, e.g. by using CoqIDE of ProofGeneral, you should first
add the directories `ALEA/`, `Lib/`, and `Semantics/` to the Coq `loadpath`.
An easy way to do this is to create a text file named `.coqrc` in your
home folder containing:

```
Add LoadPath "<topdir>/Lib".
Add LoadPath "<topdir>/ALEA".
Add LoadPath "<topdir>/Semantics".
```

Where `<topdir>` stands for the absolute path to the top level folder of
the development.

# COPYRIGHT
This work belongs to:

**Gilles Barthe, Boris Köpf, Federico Olmedo, and Santiago Zanella-Béguelin**

as per http://certicrypt.gforge.inria.fr/certipriv/.
