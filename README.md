Description
--

This repository contains Magma code for determining parts of Prym varieties cut out by intermediate Jacobians.

Installation 
--

You can enable the functionality of this code in Magma by attaching the `spec` file with `AttachSpec`. To make this independent of the directory in which you find yourself, and to active this on startup by default, you may want to indicate the relative path in your `~/.magmarc` file, by adding a line such as
```
AttachSpec("~/Programs/prym_decomposition/spec");
```

Usage
--

Examples are given in the directory `examples/`. The file `ranks.m` gives examples of calculations with the Chevalley--Weil decomposition, while `test-tools.m` runs our algorithms on an example.

Verbose comments are enabled by
```
SetVerbose("FindCovs", n)
```
where `n` is either `1`, `2` or `3`. A higher value gives more feedback.

Citing this code
--

This package includes algorithms by Paulhus and before her Breuer that can be found at [`jenpaulhus/breuer-modified`](https://github.com/jenpaulhus/breuer-modified) and without which none of this work would have been possible. An explanation of this work can be found [`here`](https://paulhus.math.grinnell.edu/monodromy.html).

If this code has been helpful in your research, then please cite the GitHub repository by Paulhus, as well as the book where Breuer explains these techniques:

Thomas Breuer
*Characters and automorphism groups of compact Riemann surfaces.*
London Mathematical Society Lecture Note Series, volume 280. Cambridge University Press, Cambridge, 2000.

Please also cite our preprint:

Davide Lombardo, Elisa Lorenzo García, Christophe Ritzenthaler, and Jeroen Sijsling
*Decomposing Jacobians via Galois covers*

Preprint available at [TBA](TBA)
