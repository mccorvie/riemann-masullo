module

public import RiemannMasullo.ForMathlib.NumberTheory.Transcendental.Baker.Auxiliary
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # The bound functions of the parametric core of the Baker method

Ported from HOL Light, Baker/parametric_core.ml (jrh13/hol-light, commit 1a0c0e6): the
definitions only. They are kept in a file of their own because both the parametric core and
the numeric layer use them. -/

@[expose] public section

namespace RiemannMasullo.Baker

/-- HOL Light: Baker/parametric_core.ml, baker_ub. The size of the auxiliary function on a
disc of radius `N`. -/
noncomputable def bakerUb (n h L k : ℕ) (P Bb Lam : ℝ) (N : ℕ) : ℝ :=
  P * Real.exp ((h : ℝ) + ((n + 1 : ℕ) : ℝ) * (L : ℝ) + ((L + 2 : ℕ) : ℝ) * ((N + h : ℕ) : ℝ) +
    ((2 * k : ℕ) : ℝ) * Real.log (2 * (k : ℝ) * Bb * Lam) + (N : ℝ) * (L : ℝ) * (Lam + 1))

/-- HOL Light: Baker/parametric_core.ml, baker_err. The distance of the auxiliary function
from its algebraic counterpart. -/
noncomputable def bakerErr (n h L k : ℕ) (P Bb Lam d0 : ℝ) (N : ℕ) : ℝ :=
  P * Real.exp ((h : ℝ) + ((n + 1 : ℕ) : ℝ) * (L : ℝ) + ((L + 2 : ℕ) : ℝ) * ((N + h : ℕ) : ℝ) +
    ((2 * k : ℕ) : ℝ) * Real.log (2 * (k : ℝ) * Bb * Lam) + (N : ℝ) * (L : ℝ) * Lam) *
    ((N : ℝ) * (L : ℝ) * d0 * Real.exp ((N : ℝ) * (L : ℝ) * d0))

/-- HOL Light: Baker/parametric_core.ml, baker_pbound. The Siegel bound for the coefficients
of the auxiliary function. -/
noncomputable def bakerPbound (n h L k : ℕ) (V : Finset ℕ) (G : ℝ) (H : ℕ → ℝ) (e : ℕ → ℕ) : ℝ :=
  ((bakerIndex h L n).card : ℝ) *
    max 1 ((Real.exp (36 * (h : ℝ)) ^ k * 2 ^ ((L + 2) * ((h + 1) + h)) * ((k : ℝ) + 1) ^ k *
        (2 * (L : ℝ) * G) ^ k) *
      ∏ r ∈ V, (2 * H r) ^ ((if r ∈ Finset.Icc 1 n then L * h else 0) + k * e r))

/-- HOL Light: Baker/parametric_core.ml, baker_nmax. The size of a common multiple of
`l + 1, …, l + h` for `l ≤ R`. -/
noncomputable def bakerNmax (h R : ℕ) : ℝ :=
  (Real.exp 19 * ((R : ℝ) + (h : ℝ)) / (h : ℝ)) ^ h

/-- HOL Light: Baker/parametric_core.ml, baker_liou5. The Liouville lower bound of Lemma 5. -/
noncomputable def bakerLiou5 (n h L k : ℕ) (V : Finset ℕ) (G : ℝ) (H : ℕ → ℝ) (e d : ℕ → ℕ)
    (P : ℝ) (R : ℕ) : ℝ :=
  Real.exp (-(((∏ r ∈ V, d r : ℕ) : ℝ) *
    (Real.log ((∏ r ∈ V, d r : ℕ) : ℝ) +
      Real.log (((bakerIndex h L n).card : ℝ) * P *
        (bakerNmax h R ^ k * 2 ^ ((L + 2) * ((R + 1) + h)) * ((k : ℝ) + 1) ^ k *
          (2 * (L : ℝ) * G) ^ k)) +
      ∑ r ∈ V, (((if r ∈ Finset.Icc 1 n then L * R else 0) + k * e r : ℕ) : ℝ) *
        Real.log (((d r + 1 : ℕ) : ℝ) * H r ^ 3))))

/-- HOL Light: Baker/parametric_core.ml, baker_liou7. The Liouville lower bound of Lemma 7. -/
noncomputable def bakerLiou7 (n h L k : ℕ) (d : ℕ → ℕ) (H : ℕ → ℝ) (P : ℝ) (X7 lmax : ℕ) : ℝ :=
  Real.exp (-(((∏ r ∈ Finset.Icc 1 n, k * d r : ℕ) : ℝ) *
    (Real.log ((∏ r ∈ Finset.Icc 1 n, k * d r : ℕ) : ℝ) +
      Real.log (((bakerIndex h L n).card : ℝ) *
        (P * (k : ℝ) ^ (2 * h * (L + 2)) * 2 ^ ((L + 2) * (X7 + h)))) +
      ∑ r ∈ Finset.Icc 1 n, ((L * lmax : ℕ) : ℝ) *
        Real.log (((k * d r + 1 : ℕ) : ℝ) * H r ^ 3))))

/-- HOL Light: Baker/parametric_core.ml, baker_vb. The gap of the dichotomy of Lemma 6. -/
noncomputable def bakerVb (n h L k : ℕ) (V : Finset ℕ) (G : ℝ) (H : ℕ → ℝ) (e d : ℕ → ℕ)
    (P Bb Lam d0 lmin Gn : ℝ) (R : ℕ) : ℝ :=
  lmin ^ k * bakerLiou5 n h L k V G H e d P R / (bakerNmax h R ^ k * Gn ^ k) -
    bakerErr n h L k P Bb Lam d0 (R + 1)

end RiemannMasullo.Baker
