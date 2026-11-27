module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Bounds_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Mellin_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Rows_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Lifts_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Division_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Circle_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Projections_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Basis_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Trace_Isolated

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes

This module re-exports the split leaf modules formalizing the constructive extension of the
fixed-box Paley–Wiener subquotients ((11.3.1.3)–(11.3.1.4), pp. 494–496) to arbitrary primitive
nontrivial Dirichlet characters `χ` of conductor `N > 1`, following `@mrshu`'s Comment #8 on GitHub
issue `#7351`.

## Leaf modules

1. `Sec3_DirichletFixedBox_Bounds_Isolated` — analytic/arithmetic reciprocal bounds and twisted Poisson summation.
2. `Sec3_DirichletFixedBox_Mellin_Isolated` — twisted half-logarithmic profiles and Mellin transforms.
3. `Sec3_DirichletFixedBox_Rows_Isolated` — strip Sobolev embedding and normalized row functionals.
4. `Sec3_DirichletFixedBox_Lifts_Isolated` — annular logarithmic lifts and back-half shift operators.
5. `Sec3_DirichletFixedBox_Division_Isolated` — fixed-box cardinal lifts and exact denominator division.
6. `Sec3_DirichletFixedBox_Circle_Isolated` — stage spaces, quotient semigroups, and modulated circle action.
7. `Sec3_DirichletFixedBox_Projections_Isolated` — eigenprojections and smooth lifts on the quotient.
8. `Sec3_DirichletFixedBox_Basis_Isolated` — averaged quotient and unconditional Hilbert basis.
9. `Sec3_DirichletFixedBox_Trace_Isolated` — convolution trace expansion and positive-support trace-norm lower bound.

All declarations live in `namespace RiemannMasullo.Isolated`.
-/
