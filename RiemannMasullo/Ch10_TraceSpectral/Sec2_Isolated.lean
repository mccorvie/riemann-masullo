module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.AppA_AlgebraicNT.Sec2
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec2a
import RiemannMasullo.Ch09_HardySobolev.Sec2
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta.MultipleZero

/-! # The uniform bound of Proposition 10.2.2.2: what it is equivalent to, and what holds without it

The upper bound for the norms of the strip jets (Proposition 10.2.2.2, pp. 446–447) is proved in
`Sec2` from two statements on the multiple zeros of the completed Hecke L-functions.

* The multiplicity bound: one integer bounds all multiplicities. This is the open statement
  `spectralStripJet_order_and_margin_multiplicity_bounded` (#7220).
* The finiteness of the lines: the multiple zeros lie on finitely many vertical lines. This is
  `spectralStripJet_order_and_margin_multiple_zero_lines_finite` (#7453). It is proved in `Sec2`
  (#7470) from two open statements,
  `spectralStripJet_multiple_zero_bounded_height_representatives` and
  `spectralStripJet_multiple_real_zeros_finite`.

So the upper bound rests on three open statements. This file shows that nothing weaker than
the multiplicity bound together with the finiteness of the lines can give it, where each of the
two is needed, and what remains true without them.

* `spectralStripJet_upperBound_iff_order_and_margin`: on each strip separately, the upper bound
  holds if and only if the orders of the jets are bounded and the jets of order at least
  `(s - 1) / 2` stay at a fixed distance from the edges.
* `spectralStripJet_upperBound_iff_multiple_zeros`: the upper bound on all strips holds if and
  only if the multiplicity bound and the finiteness of the lines hold. The strips of half-width
  one with `s = 2` and all centers suffice.
* `spectralStripJet_multiple_zeros_iff_locally_finite`: the two statements together say the
  same as the local statement
  `spectralStripJet_order_and_margin_locally_finite_multiple_zeros`.
* `spectralStripJet_upperBound_wide_iff_multiplicity_bounded`: the multiplicity bound alone is
  equivalent to the upper bound on one strip that contains all the zeros, for any `s > 1`.
* `spectralStripJet_upperBound_eventually_iff_multiplicity_le`: on each strip, the upper bound
  holds for all large `s` if and only if the multiplicities of the zeros inside the strip are
  bounded. The finiteness of the lines is not needed for `s > 2 M - 1`, where `M` bounds the
  multiplicities (`spectralStripJet_upperBound_of_multiplicity_bounded`), nor on strips whose
  edges lie outside the closed interval from zero to one
  (`spectralStripJet_upperBound_of_multiplicity_bounded_of_wide`).
* `spectralStripJet_multiplicity_le_of_upperBound`: the upper bound on a strip bounds the
  multiplicities of the zeros inside it. The proof of Theorem 10.3.2.1, p. 454, says that the
  strip multiplicity is unbounded if `α > 0`, and p. 455 uses only a logarithmic bound for it.
* `spectralStripMarkushevichBasis_normalized_iff_upperBound`: on each strip the normalization
  statement of Corollary 10.2.2.3 for the jets themselves is equivalent to the upper bound.
* `spectralStripMarkushevichBasis_unitNormalized`: the jets divided by their norms are the
  functionals of a spectral Markushevich basis, all of norm one. This needs none of the open
  statements, and the product of the norms of a functional and its biorthogonal vector, for
  which the proof of Theorem 10.3.1.1 asks one constant on p. 451, is the same as for the jets
  themselves (`spectralStripMarkushevichBasis_unitNormalized_of_basis`).
* What the later pages take (pp. 451, 455, 463–464):
  `spectralStripMarkushevichBasis_offDiagonal_product_iff` reduces the products that p. 451
  bounds to those with equal orders, by `spectralStripJet_norm_le_of_order_le` of `Sec2`;
  `spectralStripMarkushevichBasis_unitNormalized_primal_normalized_iff` and
  `spectralStripMarkushevichBasis_unitNormalized_regular` give the bounds of (10.4.2.24) for
  the jets divided by their norms from that one product bound;
  `spectralStripMarkushevichBasis_primal_normalized_and_product_iff` shows that the lower bound
  of (10.4.2.24) for the jets themselves is the one use of the upper bound after §10.2.
* Single-character bounded-height representatives (#7453), order-one strip jets, and interaction
  with real multiple-zero finiteness (#7485):
  `continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo` and
  `continuedCompletedHeckeL_multiplicity_reflect_same_character` confine zeros to the open
  strip `(0, 1)` and reflect multiplicities across `1 / 2` for each single unitary character;
  `spectralStripJet_bounded_height_iff_of_restriction_eq`,
  `spectralStripJet_bounded_height_iff_right_lines_finite`,
  `spectralStripJet_bounded_height_iff_lines_finite`, and
  `spectralStripJet_bounded_height_iff_isolated_lines` prove basepoint-independence and
  equivalence of #7453 with finiteness and isolation of all multiple-zero vertical lines;
  `spectralStripJet_bounded_height_iff_orderOne_upperBound`,
  `spectralStripJet_multiple_zero_lines_finite_iff_orderOne_upperBound`, and
  `spectralStripJet_multiple_zero_lines_finite_iff_boundedOrder_upperBound` isolate #7453 and
  `#7453 ∧ #7485` purely in terms of order-one (or bounded-order) strip jets without #7220;
  `spectralStripJet_criticalStrip_component_orderOne_iff`,
  `spectralStripJet_criticalStrip_orderOne_iff_uniform_margin`, and
  `spectralStripJet_criticalStrip_upperBound_iff` characterize the single critical strip
  `(a = 1 / 2, α = 1 / 2, s = 2)` by a multiple-zero-free strip `(0, δ) ∪ (1 - δ, 1)`;
  `spectralStripJet_bounded_height_of_notMem_finiteCover`,
  `spectralStripJet_multiple_real_zeros_finite_implies_cofinite_bounded_height_and_margin`, and
  `spectralStripJet_multiple_zero_lines_finite_iff_finiteCover_and_exceptional` show that #7485
  already forces #7453 and a uniform margin outside a finite exceptional set `E` of components;
  `spectralStripJet_zero_free_strip_of_order_forcing` transfers #7453 to any multiplicity-forcing
  factor, and `spectralStripJet_multiple_zeros_unbounded_height_cubic` rules out bounding the
  heights of all multiple zeros on the splitting field of `X³ - 2`.

Nothing here is used by the rest of the library. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "mult(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jetLp(" χ ", " hα ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (stripJet(χ, j))
local notation "Q(" a ", " hα ", " hs ")" => spectralSobolevQuotient F a hStrip(hα) hs₀(hs)
local notation "D(" a ", " hα ", " hs ")" =>
  spectralSobolevDualEmbedding F a hStrip(hα) hs₀(hs)

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. On one strip, the norms of the
strip jets have a common upper bound if and only if the orders of the jets are bounded and the
jets of order at least `(s - 1) / 2` stay at a fixed distance from the two edges. The second
statement is the conclusion of `spectralStripJet_order_and_margin`.
Deviation: The paper does not state this. It shows that, strip by strip, the upper bound of
the proposition needs exactly the bound on the orders and the margin. -/
theorem spectralStripJet_upperBound_iff_order_and_margin
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    (∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C) ↔
    ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a α s,
      j.val.2.2.2 ≤ K ∧ ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ) := by
  constructor
  · rintro ⟨C, hC⟩
    exact spectralStripJet_order_and_margin_of_upperBound χ hα hs C hC
  · rintro ⟨K, δ, hδ, h⟩
    obtain ⟨C, _, hC⟩ := spectralStripJet_upperBound_of_margin χ hα hs K δ hδ h
    exact ⟨C, hC⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447. If one integer bounds the multiplicity of every
zero of every chosen completed Hecke L-function, and the multiple zeros lie on finitely many
vertical lines, then on every strip the orders of the jets are bounded and the jets of order
at least `(s - 1) / 2` stay at a fixed distance from the edges.
Deviation: The paper does not state this. It is `spectralStripJet_order_and_margin` with the
multiplicity bound (#7220) and the finiteness of the lines (#7453) as hypotheses. -/
theorem spectralStripJet_order_and_margin_of_multiple_zeros
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (M : ℕ)
    (_hM : ∀ (ω : PontryaginDual C₁) (σ t : ℝ), mult(χ ω, shift(σ, t)) ≤ M)
    (_hfin : {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ),
      1 < mult(χ ω, shift(σ, t))}.Finite) (a α s : ℝ) (_hs : 1 < s) :
    ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a α s,
      j.val.2.2.2 ≤ K ∧ ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ) := by
  let T := {σ : ℝ | (∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))) ∧
    |σ - a| < α}
  have hT : T.Finite := _hfin.subset fun σ hσ ↦ hσ.1
  let d (σ : ℝ) := α - |σ - a|
  obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image _ id ((hT.image d).insert 1)
    (insert_nonempty _ _)
  have hδ : 0 < δ := by
    rcases hmem with rfl | ⟨σ, hσ, rfl⟩
    · exact one_pos
    · exact sub_pos.mpr hσ.2
  refine ⟨max M ⌈(s - 1) / 2⌉₊, δ, hδ, fun j ↦ ?_⟩
  by_cases hlow : (j.val.2.2.2 : ℝ) < (s - 1) / 2
  · exact ⟨(Nat.lt_ceil.mpr hlow).le.trans (le_max_right _ _), fun h ↦ (hlow.not_ge h).elim⟩
  have hk : 0 < j.val.2.2.2 := by exact_mod_cast (by linarith : (0 : ℝ) < j.val.2.2.2)
  have hj := j.property
  unfold spectralStripMultiplicity at hj
  split_ifs at hj with hb he
  · have hσ : a + j.val.2.1 ∈ T :=
      ⟨⟨j.val.1, j.val.2.2.1, by omega⟩, by simpa using abs_lt.mpr hb⟩
    have hdist : δ ≤ α - |j.val.2.1| := by
      simpa [d] using hmin (d (a + j.val.2.1)) (Or.inr (mem_image_of_mem d hσ))
    exact ⟨hj.le.trans ((_hM _ _ _).trans (le_max_left _ _)), fun _ ↦ by linarith⟩
  · exact (hlow ((lt_spectralBoundaryMultiplicity _ _ _).mp hj).2).elim
  · omega

/-- A completed Hecke L-function has no zero with real part outside the closed interval from
zero to one: to the right of one by the Euler product, and to the left of zero by the
functional equation. -/
private theorem spectralStripJet_multiple_zeros_of_upperBound_confined
    (ψ : PontryaginDual C𝔽) (z : ℂ) (hz : z.re ∉ Icc (0 : ℝ) 1) : mult(ψ, z) = 0 := by
  have hne (θ : PontryaginDual C𝔽) {w : ℂ} (hw : 1 < w.re) :
      continuedCompletedHeckeL θ w ≠ 0 := by
    rw [show continuedCompletedHeckeL θ w = completedHeckeL θ ⟨w, hw⟩ from
      (continuedCompletedHeckeL_spec θ).2 ⟨w, hw⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos θ (zero_lt_one.trans hw))
      (finiteHeckeL_ne_zero_of_one_lt_re θ ⟨w, hw⟩)
  have hval : continuedCompletedHeckeL ψ z ≠ 0 := by
    rcases lt_or_ge z.re 0 with hneg | hn
    · obtain ⟨ε, _, _, he⟩ := completedHeckeL_continuation_functionalEquation ψ _ _
        (continuedCompletedHeckeL_spec ψ).1 (continuedCompletedHeckeL_spec ψ).2
        (continuedCompletedHeckeL_spec ψ⁻¹).1 (continuedCompletedHeckeL_spec ψ⁻¹).2
      have hw : 1 < (1 - z).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      intro h0
      exact hne ψ⁻¹ hw (by rw [he z, h0, mul_zero])
    · exact hne ψ (lt_of_not_ge fun h ↦ hz ⟨hn, h⟩)
  rw [((continuedCompletedHeckeL_spec ψ).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval]
  rfl

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. If on every strip of half-width
one with `s = 2` the norms of the strip jets have a common upper bound, then one integer bounds
the multiplicity of every zero of every chosen completed Hecke L-function, and the multiple
zeros lie on finitely many vertical lines. These are the statements of
`spectralStripJet_order_and_margin_multiplicity_bounded` (#7220, open) and of
`spectralStripJet_order_and_margin_multiple_zero_lines_finite` (#7453, proved in `Sec2` from
two open statements).
Deviation: The paper does not state this. It shows that the upper bound of the proposition
cannot be had from less than these two statements. -/
theorem spectralStripJet_multiple_zeros_of_upperBound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_h : ∀ a : ℝ, ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a 1 2,
      ‖(spectralStripJet_memLp χ zero_le_one zero_le_two j).toLp (stripJet(χ, j))‖ ≤ C) :
    (∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (σ t : ℝ), mult(χ ω, shift(σ, t)) ≤ M) ∧
      {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))}.Finite := by
  have h' : ∀ a : ℝ, ∃ (K : ℕ) (δ : ℝ), 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a 1 2,
      j.val.2.2.2 ≤ K ∧ (((2 : ℝ) - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ 1 - δ) := by
    intro a
    obtain ⟨C, hC⟩ := _h a
    exact spectralStripJet_order_and_margin_of_upperBound χ zero_le_one one_lt_two C hC
  choose K δ hδ hj using h'
  -- A zero inside the open strip with center `c` gives a jet of the highest order there.
  have atZero (c y t : ℝ) (ω : PontryaginDual C₁) (hi : |y - c| < 1)
      (hm : 0 < mult(χ ω, shift(y, t))) :
      mult(χ ω, shift(y, t)) ≤ K c + 1 ∧
        (1 < mult(χ ω, shift(y, t)) → |y - c| ≤ 1 - δ c) := by
    let j : SpectralStripJetIndex χ c 1 2 := ⟨(ω, y - c, t, mult(χ ω, shift(y, t)) - 1), by
      change mult(χ ω, shift(y, t)) - 1 < spectralStripMultiplicity 1 2 (y - c)
        (mult(χ ω, shift(c + (y - c), t)))
      rw [spectralStripMultiplicity_interior (abs_lt.mp hi), show c + (y - c) = y by ring]
      omega⟩
    obtain ⟨hK, hd⟩ := hj c j
    change mult(χ ω, shift(y, t)) - 1 ≤ K c at hK
    refine ⟨by omega, fun h1 ↦ hd ?_⟩
    change ((2 : ℝ) - 1) / 2 ≤ ((mult(χ ω, shift(y, t)) - 1 : ℕ) : ℝ)
    have h2 : (1 : ℝ) ≤ ((mult(χ ω, shift(y, t)) - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ mult(χ ω, shift(y, t)) - 1)
    linarith
  have hsub : ∀ (ω : PontryaginDual C₁) (σ t : ℝ), 0 < mult(χ ω, shift(σ, t)) →
      σ ∈ Icc (0 : ℝ) 1 := by
    intro ω σ t hpos
    by_contra hσ
    rw [spectralStripJet_multiple_zeros_of_upperBound_confined (χ ω) (shift(σ, t))
      (by simpa using hσ)] at hpos
    exact lt_irrefl _ hpos
  constructor
  · refine ⟨K (1 / 2) + 1, fun ω σ t ↦ ?_⟩
    rcases Nat.eq_zero_or_pos (mult(χ ω, shift(σ, t))) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    · have hσ := hsub ω σ t hpos
      exact (atZero (1 / 2) σ t ω (abs_lt.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
        hpos).1
  · let r (x : ℝ) := min 1 (min (δ (x - 1)) (δ (x + 1)))
    have hr (x : ℝ) : 0 < r x := lt_min one_pos (lt_min (hδ _) (hδ _))
    obtain ⟨T, _, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).elim_nhds_subcover
      (fun x ↦ Ioo (x - r x) (x + r x))
      (fun x _ ↦ Ioo_mem_nhds (by linarith [hr x]) (by linarith [hr x]))
    refine T.finite_toSet.subset ?_
    rintro y ⟨ω, t, h1⟩
    obtain ⟨x, hxT, hxl, hxr⟩ := mem_iUnion₂.mp (hcover (hsub ω y t (by omega)))
    have hr1 : r x ≤ 1 := min_le_left _ _
    have hrL : r x ≤ δ (x - 1) := (min_le_right _ _).trans (min_le_left _ _)
    have hrR : r x ≤ δ (x + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have heq : y = x := by
      rcases lt_trichotomy y x with hlt | heq | hgt
      · have hsep := (atZero (x - 1) y t ω (abs_lt.mpr ⟨by linarith, by linarith⟩)
          (by omega)).2 h1
        linarith [le_abs_self (y - (x - 1))]
      · exact heq
      · have hsep := (atZero (x + 1) y t ω (abs_lt.mpr ⟨by linarith, by linarith⟩)
          (by omega)).2 h1
        linarith [neg_le_abs (y - (x + 1))]
    rw [heq]
    exact hxT

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. The norms of the strip jets have
a common upper bound on every strip if and only if one integer bounds the multiplicity of every
zero of every chosen completed Hecke L-function and the multiple zeros lie on finitely many
vertical lines. The right-hand side is the conjunction of the statements of
`spectralStripJet_order_and_margin_multiplicity_bounded` (#7220, open) and of
`spectralStripJet_order_and_margin_multiple_zero_lines_finite` (#7453). The second is proved in
`Sec2` from the open statements `spectralStripJet_multiple_zero_bounded_height_representatives`
and `spectralStripJet_multiple_real_zeros_finite`, to which it is equivalent when all choices
of base points are taken together (`spectralStripJet_multiple_zero_lines_iff`).
Deviation: The paper does not state this. The upper bound is the one that
`spectralStripJet_upperBound` asserts, and no hypothesis on the choice of the base points is
needed for the equivalence. -/
theorem spectralStripJet_upperBound_iff_multiple_zeros
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) :
    (∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s), ∃ C : ℝ,
      ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C) ↔
    ((∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (σ t : ℝ), mult(χ ω, shift(σ, t)) ≤ M) ∧
      {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))}.Finite) := by
  constructor
  · intro h
    exact spectralStripJet_multiple_zeros_of_upperBound χ
      (fun a ↦ h a 1 2 zero_le_one one_lt_two)
  · rintro ⟨⟨M, hM⟩, hfin⟩ a α s hα hs
    obtain ⟨K, δ, hδ, hj⟩ :=
      spectralStripJet_order_and_margin_of_multiple_zeros χ M hM hfin a α s hs
    obtain ⟨C, _, hC⟩ := spectralStripJet_upperBound_of_margin χ hα hs K δ hδ hj
    exact ⟨C, hC⟩

/-- Paper: Remark 10.2.1.5, p. 444, and Proposition 10.2.2.2, pp. 446–447. Near every real
number only finitely many pairs of real part and multiplicity occur among the multiple zeros
of the chosen completed Hecke L-functions, if and only if one integer bounds all the
multiplicities and the multiple zeros lie on finitely many vertical lines. The left-hand side
is the statement of `spectralStripJet_order_and_margin_locally_finite_multiple_zeros`, the
right-hand side the conjunction of the multiplicity bound (#7220) and the finiteness of the
lines (#7453).
Deviation: The paper does not state this. The zeros have real part between zero and one, and
that interval is compact, so the local form and the global form say the same. -/
theorem spectralStripJet_multiple_zeros_iff_locally_finite
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) :
    (∀ x : ℝ, ∃ U ∈ 𝓝 x, {p : ℝ × ℕ | p.1 ∈ U ∧ 1 < p.2 ∧
      ∃ (ω : PontryaginDual C₁) (t : ℝ), mult(χ ω, shift(p.1, t)) = p.2}.Finite) ↔
    ((∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (σ t : ℝ), mult(χ ω, shift(σ, t)) ≤ M) ∧
      {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))}.Finite) := by
  constructor
  · intro h
    choose U hU hloc using h
    obtain ⟨T, _, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).elim_nhds_subcover U
      (fun x _ ↦ hU x)
    let S : Set (ℝ × ℕ) := ⋃ x ∈ (T : Set ℝ), {p : ℝ × ℕ | p.1 ∈ U x ∧ 1 < p.2 ∧
      ∃ (ω : PontryaginDual C₁) (t : ℝ), mult(χ ω, shift(p.1, t)) = p.2}
    have hS : S.Finite := T.finite_toSet.biUnion fun x _ ↦ hloc x
    have hmem : ∀ (ω : PontryaginDual C₁) (σ t : ℝ), 1 < mult(χ ω, shift(σ, t)) →
        (σ, mult(χ ω, shift(σ, t))) ∈ S := by
      intro ω σ t h1
      have hσ : σ ∈ Icc (0 : ℝ) 1 := by
        by_contra hσ
        rw [spectralStripJet_multiple_zeros_of_upperBound_confined (χ ω) (shift(σ, t))
          (by simpa using hσ)] at h1
        omega
      obtain ⟨x, hxT, hxU⟩ := mem_iUnion₂.mp (hcover hσ)
      exact mem_iUnion₂.mpr ⟨x, Finset.mem_coe.mpr hxT, hxU, h1, ω, t, rfl⟩
    obtain ⟨K, hK⟩ := (hS.image Prod.snd).bddAbove
    refine ⟨⟨max K 1, fun ω σ t ↦ ?_⟩, (hS.image Prod.fst).subset ?_⟩
    · by_cases h1 : 1 < mult(χ ω, shift(σ, t))
      · exact (hK (mem_image_of_mem Prod.snd (hmem ω σ t h1))).trans (le_max_left _ _)
      · exact (not_lt.mp h1).trans (le_max_right _ _)
    · rintro σ ⟨ω, t, h1⟩
      exact ⟨_, hmem ω σ t h1, rfl⟩
  · rintro ⟨⟨M, hM⟩, hfin⟩ x
    refine ⟨univ, univ_mem, (hfin.prod (finite_Iic M)).subset ?_⟩
    rintro ⟨σ, n⟩ ⟨-, hn, ω, t, h⟩
    exact ⟨⟨ω, t, h.symm ▸ hn⟩, h ▸ hM ω σ t⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447. If every zero of the chosen completed Hecke
L-functions has real part `1 / 2`, the multiple zeros lie on one vertical line. So the
statement of `spectralStripJet_order_and_margin_multiple_zero_lines_finite` (#7453) follows
from the main claim of the paper, which Proposition 10.2.2.2 stands on the way to.
Deviation: The paper does not state this. -/
theorem spectralStripJet_multiple_zero_lines_finite_of_re_eq_half
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (_h : ∀ (ω : PontryaginDual C₁) (σ t : ℝ), 0 < mult(χ ω, shift(σ, t)) → σ = 1 / 2) :
    {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))}.Finite := by
  refine (finite_singleton (1 / 2 : ℝ)).subset ?_
  rintro σ ⟨ω, t, h1⟩
  exact _h ω σ t (by omega)

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. If the zeros inside one open
strip have multiplicity at most `M` and `s > 2 M - 1`, the norms of the strip jets of that
strip have a common upper bound. No statement on the real parts of the multiple zeros is used:
every admitted jet then has order below `(s - 1) / 2`.
Deviation: The paper does not state this. -/
theorem spectralStripJet_upperBound_of_multiplicity_le
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (M : ℕ)
    (_hM : ∀ (ω : PontryaginDual C₁) (b t : ℝ), |b| < α →
      mult(χ ω, shift(a + b, t)) ≤ M) (_hsM : 2 * (M : ℝ) - 1 < s) :
    ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C := by
  have hlow (j : SpectralStripJetIndex χ a α s) : (j.val.2.2.2 : ℝ) < (s - 1) / 2 := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with hb he
    · have h1 : j.val.2.2.2 + 1 ≤ M :=
        (Nat.succ_le_of_lt hj).trans (_hM _ _ _ (abs_lt.mpr hb))
      have h2 : (j.val.2.2.2 : ℝ) + 1 ≤ M := by exact_mod_cast h1
      linarith
    · exact ((lt_spectralBoundaryMultiplicity _ _ _).mp hj).2
    · omega
  obtain ⟨C, _, hC⟩ := spectralStripJet_upperBound_of_margin χ hα hs ⌈(s - 1) / 2⌉₊ 1 one_pos
    (fun j ↦ ⟨(Nat.lt_ceil.mpr (hlow j)).le, fun h ↦ absurd h (not_le.mpr (hlow j))⟩)
  exact ⟨C, hC⟩

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. For the strip of half-width zero
the norms of the strip jets have a common upper bound, with no hypothesis on the zeros: the
open strip is empty, and the jets on the two edges have order below `(s - 1) / 2`.
Deviation: The paper does not state this case separately. It is the case `α = 0` of
`spectralStripJet_upperBound`, here without any of the open statements. -/
theorem spectralStripJet_upperBound_zeroWidth
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a 0 s, ‖jetLp(χ, le_rfl, hs, j)‖ ≤ C :=
  spectralStripJet_upperBound_of_multiplicity_le (a := a) (α := 0) χ le_rfl hs 0
    (fun _ b _ hb ↦ absurd hb (not_lt.mpr (abs_nonneg b)))
    (by rw [Nat.cast_zero, mul_zero, zero_sub]; linarith)

/-- Paper: Proposition 10.2.2.2, pp. 446–447. From the statement of the open
`spectralStripJet_order_and_margin_multiplicity_bounded` (#7220) alone, with bound `M`, the
norms of the strip jets have a common upper bound on every strip for every `s > 2 M - 1`.
So the finiteness of the vertical lines that carry multiple zeros (#7453), and with it the two
open statements from which `Sec2` proves it, is needed only for `1 < s ≤ 2 M - 1`.
Deviation: The paper does not state this. -/
theorem spectralStripJet_upperBound_of_multiplicity_bounded
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (M : ℕ)
    (_hM : ∀ (ω : PontryaginDual C₁) (σ t : ℝ), mult(χ ω, shift(σ, t)) ≤ M)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (_hsM : 2 * (M : ℝ) - 1 < s) :
    ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C :=
  spectralStripJet_upperBound_of_multiplicity_le χ hα hs M
    (fun ω b t _ ↦ _hM ω (a + b) t) _hsM

/-- Paper: Proposition 10.2.2.2, pp. 446–447. From the statement of the open
`spectralStripJet_order_and_margin_multiplicity_bounded` (#7220) alone, the norms of the strip
jets have a common upper bound, for every `s > 1`, on every strip whose two edges lie outside
the closed interval from zero to one. All zeros then keep a fixed distance from the edges.
So the finiteness of the lines (#7453) is needed only for strips with an edge of real part
between zero and one, and there only for `1 < s ≤ 2 M - 1`.
Deviation: The paper does not state this. -/
theorem spectralStripJet_upperBound_of_multiplicity_bounded_of_wide
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (M : ℕ)
    (_hM : ∀ (ω : PontryaginDual C₁) (σ t : ℝ), mult(χ ω, shift(σ, t)) ≤ M)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) (_ha : a < α) (_ha' : 1 < a + α) :
    ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C := by
  obtain ⟨C, _, hC⟩ := spectralStripJet_upperBound_of_margin χ hα hs M
    (min (α - a) (a + α - 1)) (lt_min (by linarith) (by linarith)) (fun j ↦ by
      have hj := j.property
      have hmult : j.val.2.2.2 < mult(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1)) := by
        unfold spectralStripMultiplicity spectralBoundaryMultiplicity at hj
        split_ifs at hj <;> omega
      have hσ : a + j.val.2.1 ∈ Icc (0 : ℝ) 1 := by
        by_contra hσ
        rw [spectralStripJet_multiple_zeros_of_upperBound_confined (χ j.val.1)
          (shift(a + j.val.2.1, j.val.2.2.1)) (by simpa using hσ)] at hmult
        omega
      refine ⟨hmult.le.trans (_hM _ _ _), fun _ ↦ abs_le.mpr ⟨?_, ?_⟩⟩
      · linarith [hσ.1, min_le_left (α - a) (a + α - 1)]
      · linarith [hσ.2, min_le_right (α - a) (a + α - 1)])
  exact ⟨C, hC⟩

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. A common upper bound for the
norms of the strip jets of one strip bounds the multiplicities of the zeros inside the open
strip. The proof of Theorem 10.3.2.1, p. 454, says that the strip multiplicity of (10.2.2.5)
and (10.2.2.6) "is unbounded if `α > 0`", and p. 455 uses for it only a bound that grows like
the logarithm of the ordinate. By this theorem the upper bound of Proposition 10.2.2.2 on a
strip excludes unbounded multiplicities inside that strip.
Deviation: The paper does not state this. -/
theorem spectralStripJet_multiplicity_le_of_upperBound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (_h : ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C) :
    ∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (b t : ℝ), |b| < α →
      mult(χ ω, shift(a + b, t)) ≤ M := by
  obtain ⟨C, hC⟩ := _h
  obtain ⟨K, δ, -, hj⟩ := spectralStripJet_order_and_margin_of_upperBound χ hα hs C hC
  refine ⟨K + 1, fun ω b t hb ↦ ?_⟩
  rcases Nat.eq_zero_or_pos (mult(χ ω, shift(a + b, t))) with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  · let j : SpectralStripJetIndex χ a α s := ⟨(ω, b, t, mult(χ ω, shift(a + b, t)) - 1), by
      change mult(χ ω, shift(a + b, t)) - 1 < spectralStripMultiplicity α s b
        (mult(χ ω, shift(a + b, t)))
      rw [spectralStripMultiplicity_interior (abs_lt.mp hb)]
      omega⟩
    have hK := (hj j).1
    change mult(χ ω, shift(a + b, t)) - 1 ≤ K at hK
    omega

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. On one strip whose two edges lie
outside the closed interval from zero to one, for example center `1 / 2` and half-width `1`,
and for any `s > 1`, the norms of the strip jets have a common upper bound if and only if one
integer bounds the multiplicity of every zero of every chosen completed Hecke L-function. The
right-hand side is the statement of the open
`spectralStripJet_order_and_margin_multiplicity_bounded` (#7220).
Deviation: The paper does not state this. One instance of the upper bound of the proposition
is already equivalent to the multiplicity bound. -/
theorem spectralStripJet_upperBound_wide_iff_multiplicity_bounded
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (_ha : a < α) (_ha' : 1 < a + α) :
    (∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C) ↔
    ∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (σ t : ℝ), mult(χ ω, shift(σ, t)) ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := spectralStripJet_multiplicity_le_of_upperBound χ hα hs h
    refine ⟨M, fun ω σ t ↦ ?_⟩
    rcases Nat.eq_zero_or_pos (mult(χ ω, shift(σ, t))) with h0 | hpos
    · rw [h0]
      exact Nat.zero_le _
    · have hσ : σ ∈ Icc (0 : ℝ) 1 := by
        by_contra hσ
        rw [spectralStripJet_multiple_zeros_of_upperBound_confined (χ ω) (shift(σ, t))
          (by simpa using hσ)] at hpos
        exact lt_irrefl _ hpos
      have h1 := hM ω (σ - a) t (abs_lt.mpr ⟨by linarith [hσ.1], by linarith [hσ.2]⟩)
      rwa [show a + (σ - a) = σ by ring] at h1
  · rintro ⟨M, hM⟩
    exact spectralStripJet_upperBound_of_multiplicity_bounded_of_wide χ M hM hα hs _ha _ha'

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. On one strip, the norms of the
strip jets have a common upper bound for all large `s` if and only if the multiplicities of the
zeros inside the open strip are bounded.
Deviation: The paper does not state this. For large `s` the only content of the upper bound
on a strip is a bound for the multiplicities of the zeros in that strip. -/
theorem spectralStripJet_upperBound_eventually_iff_multiplicity_le
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α : ℝ} (hα : 0 ≤ α) :
    (∃ s₀ : ℝ, ∀ (s : ℝ) (hs : 1 < s), s₀ < s → ∃ C : ℝ,
      ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C) ↔
    ∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (b t : ℝ), |b| < α →
      mult(χ ω, shift(a + b, t)) ≤ M := by
  constructor
  · rintro ⟨s₀, h⟩
    have hs : 1 < max s₀ 1 + 1 := by linarith [le_max_right s₀ 1]
    exact spectralStripJet_multiplicity_le_of_upperBound χ hα hs
      (h _ hs (by linarith [le_max_left s₀ 1]))
  · rintro ⟨M, hM⟩
    exact ⟨2 * (M : ℝ) - 1, fun s hs hsM ↦
      spectralStripJet_upperBound_of_multiplicity_le χ hα hs M hM hsM⟩

/-- Paper: Corollary 10.2.2.3, p. 447. On one strip, the strip jets themselves are the
functionals of a normalized spectral Markushevich basis if and only if their norms have a common
upper bound.
Deviation: The paper does not state this. The lower bound and the basis are unconditional
(`spectralStripJet_lowerBound`, `spectralStripMarkushevichBasis`), so the corollary for the
jets themselves is exactly the upper bound of Proposition 10.2.2.2. -/
theorem spectralStripMarkushevichBasis_normalized_iff_upperBound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    (∃ (x : SpectralStripJetIndex χ a α s → Q(a, hα, hs))
      (Λ : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, hα, hs)),
      IsSpectralMarkushevichBasis x Λ ∧
      (∀ j, D(a, hα, hs) (Λ j) = jetLp(χ, hα, hs, j)) ∧
      IsNormalizedSpectralFamily (fun j ↦ D(a, hα, hs) (Λ j))) ↔
    ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C := by
  constructor
  · rintro ⟨x, Λ, -, hD, ⟨C, hC⟩, -⟩
    exact ⟨C, fun j ↦ by simpa only [hD j] using hC j⟩
  · rintro ⟨C, hC⟩
    obtain ⟨x, Λ, hB, hD⟩ := (spectralStripMarkushevichBasis (a := a) χ _hχ hα hs₀(hs)).2
    obtain ⟨c, hc, hlower⟩ := spectralStripJet_lowerBound (a := a) χ _hχ hα hs
    refine ⟨x, Λ, hB, hD, ⟨C, fun j ↦ ?_⟩, ⟨c, hc, fun j ↦ ?_⟩⟩
    · simpa only [hD j] using hC j
    · simpa only [hD j] using hlower j

/-- Multiplying the vectors of a family by nonzero scalars does not change its linear span. -/
private theorem spectralStripMarkushevichBasis_unitNormalized_of_basis_span {ι M : Type*}
    [AddCommGroup M] [Module ℂ M] (y : ι → M) (d : ι → ℂ) (hd : ∀ i, d i ≠ 0) :
    Submodule.span ℂ (range fun i ↦ d i • y i) = Submodule.span ℂ (range y) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h : y i = (d i)⁻¹ • (d i • y i) := by
      rw [smul_smul, inv_mul_cancel₀ (hd i), one_smul]
    rw [h]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self i))

/-- A spectral Markushevich basis stays one when each vector is multiplied by a nonzero scalar
and its functional by the inverse scalar. -/
private theorem spectralStripMarkushevichBasis_unitNormalized_of_basis_smul {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {x : ι → E} {Λ : ι → StrongDual ℂ E}
    (h : IsSpectralMarkushevichBasis x Λ) (c : ι → ℂ) (hc : ∀ i, c i ≠ 0) :
    IsSpectralMarkushevichBasis (fun i ↦ c i • x i) (fun i ↦ (c i)⁻¹ • Λ i) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun i ↦ ?_, fun i j hij ↦ ?_, ?_, ?_⟩
  · change (c i)⁻¹ • (Λ i) (c i • x i) = 1
    rw [map_smul, h1 i, smul_eq_mul, smul_eq_mul, mul_one, inv_mul_cancel₀ (hc i)]
  · change (c j)⁻¹ • (Λ j) (c i • x i) = 0
    rw [map_smul, h2 i j hij, smul_zero, smul_zero]
  · rw [spectralStripMarkushevichBasis_unitNormalized_of_basis_span x c hc]
    exact h3
  · rw [spectralStripMarkushevichBasis_unitNormalized_of_basis_span Λ (fun i ↦ (c i)⁻¹)
      (fun i ↦ inv_ne_zero (hc i))]
    exact h4

/-- Paper: Corollary 10.2.2.3, p. 447. Take a spectral Markushevich basis whose functionals
are the strip jets. Dividing each functional by the norm of its jet, and multiplying its vector
by that norm, gives a spectral Markushevich basis again. Its functionals are the jets divided
by their norms, they have norm one, and for every index the product of the norms of the vector
and of the functional is the same as before.
Deviation: The paper does not state this. The product of the two norms is the quantity for
which the proof of Theorem 10.3.1.1, p. 451, needs one constant. -/
theorem spectralStripMarkushevichBasis_unitNormalized_of_basis
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (x : SpectralStripJetIndex χ a α s → Q(a, hα, hs))
    (Λ : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, hα, hs))
    (_hB : IsSpectralMarkushevichBasis x Λ)
    (_hD : ∀ j, D(a, hα, hs) (Λ j) = jetLp(χ, hα, hs, j)) :
    IsSpectralMarkushevichBasis (fun j ↦ ((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ) • x j)
        (fun j ↦ ((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • Λ j) ∧
      (∀ j, D(a, hα, hs) (((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • Λ j) =
        ((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • jetLp(χ, hα, hs, j)) ∧
      (∀ j, ‖D(a, hα, hs) (((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • Λ j)‖ = 1) ∧
      (∀ j, ‖((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ) • x j‖ *
          ‖D(a, hα, hs) (((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • Λ j)‖ =
        ‖x j‖ * ‖D(a, hα, hs) (Λ j)‖) := by
  obtain ⟨c, hc, hlower⟩ := spectralStripJet_lowerBound (a := a) χ _hχ hα hs
  have hpos (j : SpectralStripJetIndex χ a α s) : 0 < ‖jetLp(χ, hα, hs, j)‖ :=
    hc.trans_le (hlower j)
  have hne (j : SpectralStripJetIndex χ a α s) :
      ((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (hpos j).ne'
  have hDj (j : SpectralStripJetIndex χ a α s) :
      D(a, hα, hs) (((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • Λ j) =
        ((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • jetLp(χ, hα, hs, j) := by
    rw [map_smul, _hD j]
  have hnorm (j : SpectralStripJetIndex χ a α s) :
      ‖D(a, hα, hs) (((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • Λ j)‖ = 1 := by
    rw [hDj j, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (hpos j).ne']
  refine ⟨spectralStripMarkushevichBasis_unitNormalized_of_basis_smul _hB _ hne, hDj, hnorm,
    fun j ↦ ?_⟩
  rw [hnorm j, mul_one, norm_smul, Complex.norm_real, norm_norm, _hD j, mul_comm]

/-- Paper: Corollary 10.2.2.3, p. 447. The strip jets, each divided by its norm, are the
functionals of a spectral Markushevich basis of the strip quotient, and all of them have norm
one in the reciprocal strip space. No bound on the multiplicities of the zeros is used.
Deviation: The corollary takes the jets themselves, and for those the upper bound is equivalent
to two open statements (`spectralStripJet_upperBound_iff_multiple_zeros`). Here each jet is
divided by its own norm, which changes neither the linear spans nor the product of the norms of
a functional and its biorthogonal vector
(`spectralStripMarkushevichBasis_unitNormalized_of_basis`). -/
theorem spectralStripMarkushevichBasis_unitNormalized
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ (x : SpectralStripJetIndex χ a α s → Q(a, hα, hs))
      (Λ : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, hα, hs)),
      IsSpectralMarkushevichBasis x Λ ∧
      (∀ j, D(a, hα, hs) (Λ j) =
        ((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • jetLp(χ, hα, hs, j)) ∧
      (∀ j, ‖D(a, hα, hs) (Λ j)‖ = 1) ∧
      IsNormalizedSpectralFamily (fun j ↦ D(a, hα, hs) (Λ j)) := by
  obtain ⟨x, Λ, hB, hD⟩ := (spectralStripMarkushevichBasis (a := a) χ _hχ hα hs₀(hs)).2
  obtain ⟨hB', hDj, hnorm, -⟩ :=
    spectralStripMarkushevichBasis_unitNormalized_of_basis χ _hχ hα hs x Λ hB hD
  exact ⟨_, _, hB', hDj, hnorm, ⟨1, fun j ↦ (hnorm j).le⟩, 1, one_pos, fun j ↦ (hnorm j).ge⟩

/-! ## What the later pages take from the normalization

The proofs of Theorems 10.3.1.1 and 10.3.2.1 (p. 451, repeated on p. 455) and of Theorem
10.4.2.8 (pp. 463–464) use the bases of §10.2 through the products of the norm of a jet and
the norm of the biorthogonal vector of a jet of the same or a higher order at the same zero,
and through bounds for the biorthogonal vectors. The theorems below show that these uses do
not involve the upper bound of Proposition 10.2.2.2, hence none of the open statements under
it, once each jet is divided by its norm. The one use that does involve it is the lower bound
for the biorthogonal vectors of the jets themselves in (10.4.2.24), p. 463. -/

/-- Paper: Terminology 10.2.1.2, p. 444. For a spectral Markushevich basis of the strip
quotient, the product of the norms of a functional, measured in the reciprocal strip space,
and of its biorthogonal vector is at least one.
Deviation: The paper does not state this. -/
theorem spectralStripMarkushevichBasis_one_le_norm_mul
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (x : SpectralStripJetIndex χ a α s → Q(a, hα, hs))
    (Λ : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, hα, hs))
    (_hB : IsSpectralMarkushevichBasis x Λ) (j : SpectralStripJetIndex χ a α s) :
    1 ≤ ‖D(a, hα, hs) (Λ j)‖ * ‖x j‖ := by
  have hiso : ‖D(a, hα, hs) (Λ j)‖ = ‖Λ j‖ := by
    have h := (spectralSobolevDualEmbedding_isometry_range (F := F) a hStrip(hα)
      hs₀(hs)).1.dist_eq (Λ j) 0
    simpa only [map_zero, dist_zero_right] using h
  rw [hiso]
  calc (1 : ℝ) = ‖Λ j (x j)‖ := by rw [_hB.1 j, norm_one]
    _ ≤ ‖Λ j‖ * ‖x j‖ := (Λ j).le_opNorm (x j)

/-- Paper: Theorem 10.3.1.1, the bound before (10.3.1.19), p. 451, used again for Theorem
10.3.2.1 on p. 455 and for (10.4.2.34) on p. 464. The proof asks one constant for the products
of the norm of a jet and the norm of the biorthogonal vector of a jet of the same or a higher
order at the same zero. Such a constant exists if and only if one constant bounds the products
with equal orders. Neither side involves an upper bound for the norms of the jets.
Deviation: The paper does not state this. It deduces the constant from the normalization of
the jets and of their biorthogonal vectors. -/
theorem spectralStripMarkushevichBasis_offDiagonal_product_iff
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (x : SpectralStripJetIndex χ a α s → Q(a, hα, hs))
    (Λ : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, hα, hs))
    (_hD : ∀ j, D(a, hα, hs) (Λ j) = jetLp(χ, hα, hs, j)) :
    (∃ C : ℝ, ∀ j j' : SpectralStripJetIndex χ a α s, j'.val.1 = j.val.1 →
      j'.val.2.1 = j.val.2.1 → j'.val.2.2.1 = j.val.2.2.1 → j'.val.2.2.2 ≤ j.val.2.2.2 →
      ‖D(a, hα, hs) (Λ j')‖ * ‖x j‖ ≤ C) ↔
    ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖D(a, hα, hs) (Λ j)‖ * ‖x j‖ ≤ C := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun j ↦ hC j j rfl rfl rfl le_rfl⟩
  · rintro ⟨C, hC⟩
    obtain ⟨R, hR, hratio⟩ := spectralStripJet_norm_le_of_order_le (a := a) χ _hχ hα hs
    refine ⟨R * C, fun j j' _ hb _ hm ↦ ?_⟩
    have h1 : ‖D(a, hα, hs) (Λ j')‖ ≤ R * ‖D(a, hα, hs) (Λ j)‖ := by
      rw [_hD j', _hD j]
      exact hratio j j' hb hm
    calc ‖D(a, hα, hs) (Λ j')‖ * ‖x j‖
        ≤ R * ‖D(a, hα, hs) (Λ j)‖ * ‖x j‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ = R * (‖D(a, hα, hs) (Λ j)‖ * ‖x j‖) := by ring
      _ ≤ R * C := mul_le_mul_of_nonneg_left (hC j) hR.le

/-- Paper: Remark 10.2.1.5, p. 444, and (10.4.2.24), p. 463. Divide each strip jet by its norm
and multiply its biorthogonal vector by that norm. The vectors so obtained form a normalized
family, in the sense of Terminology 10.2.1.2, if and only if one constant bounds the products
of the norms of a jet and of its biorthogonal vector. Their norms are at least one in any
case. So for the jets divided by their norms, the bounds of (10.4.2.24) are the bound that
p. 451 asks for, and no upper bound for the norms of the jets enters.
Deviation: The paper does not state this. -/
theorem spectralStripMarkushevichBasis_unitNormalized_primal_normalized_iff
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (x : SpectralStripJetIndex χ a α s → Q(a, hα, hs))
    (Λ : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, hα, hs))
    (_hB : IsSpectralMarkushevichBasis x Λ)
    (_hD : ∀ j, D(a, hα, hs) (Λ j) = jetLp(χ, hα, hs, j)) :
    IsNormalizedSpectralFamily (fun j ↦ ((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ) • x j) ↔
    ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖D(a, hα, hs) (Λ j)‖ * ‖x j‖ ≤ C := by
  have hnorm (j : SpectralStripJetIndex χ a α s) :
      ‖((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ) • x j‖ = ‖D(a, hα, hs) (Λ j)‖ * ‖x j‖ := by
    rw [norm_smul, Complex.norm_real, norm_norm, _hD j]
  constructor
  · rintro ⟨⟨C, hC⟩, -⟩
    exact ⟨C, fun j ↦ by simpa only [hnorm j] using hC j⟩
  · rintro ⟨C, hC⟩
    refine ⟨⟨C, fun j ↦ ?_⟩, 1, one_pos, fun j ↦ ?_⟩
    · simpa only [hnorm j] using hC j
    · simpa only [hnorm j] using
        spectralStripMarkushevichBasis_one_le_norm_mul χ hα hs x Λ _hB j

/-- Paper: (10.4.2.24), p. 463, with Proposition 10.2.2.2, pp. 446–447. For the strip jets
themselves and their biorthogonal vectors: the vectors form a normalized family and one
constant bounds the products of the norms of a jet and of its biorthogonal vector, if and only
if the norms of the jets have a common upper bound and one constant bounds those products.
So, granted the bound for the products that p. 451 asks for, the lower bound for the
biorthogonal vectors in (10.4.2.24) is exactly the upper bound of Proposition 10.2.2.2. This
is the one place after §10.2 where that upper bound, and with it the multiplicity bound
(#7220) and the finiteness of the lines (#7453), is used, and it disappears when each jet is
divided by its norm
(`spectralStripMarkushevichBasis_unitNormalized_primal_normalized_iff`).
Deviation: The paper does not state this. -/
theorem spectralStripMarkushevichBasis_primal_normalized_and_product_iff
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (x : SpectralStripJetIndex χ a α s → Q(a, hα, hs))
    (Λ : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, hα, hs))
    (_hB : IsSpectralMarkushevichBasis x Λ)
    (_hD : ∀ j, D(a, hα, hs) (Λ j) = jetLp(χ, hα, hs, j)) :
    (IsNormalizedSpectralFamily x ∧
      ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖D(a, hα, hs) (Λ j)‖ * ‖x j‖ ≤ C) ↔
    ((∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖jetLp(χ, hα, hs, j)‖ ≤ C) ∧
      ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, ‖D(a, hα, hs) (Λ j)‖ * ‖x j‖ ≤ C) := by
  constructor
  · rintro ⟨⟨-, c, hc, hlow⟩, C, hC⟩
    refine ⟨⟨C / c, fun j ↦ ?_⟩, C, hC⟩
    rw [← _hD j, le_div_iff₀ hc]
    exact (mul_le_mul_of_nonneg_left (hlow j) (norm_nonneg _)).trans (hC j)
  · rintro ⟨⟨B, hB⟩, C, hC⟩
    obtain ⟨c, hc, hlower⟩ := spectralStripJet_lowerBound (a := a) χ _hχ hα hs
    have hmax : 0 < max B 1 := lt_max_of_lt_right zero_lt_one
    refine ⟨⟨⟨C / c, fun j ↦ ?_⟩, (max B 1)⁻¹, inv_pos.mpr hmax, fun j ↦ ?_⟩, C, hC⟩
    · have hl : c ≤ ‖jetLp(χ, hα, hs, j)‖ := hlower j
      rw [le_div_iff₀ hc]
      calc ‖x j‖ * c ≤ ‖x j‖ * ‖jetLp(χ, hα, hs, j)‖ :=
            mul_le_mul_of_nonneg_left hl (norm_nonneg _)
        _ = ‖D(a, hα, hs) (Λ j)‖ * ‖x j‖ := by rw [_hD j, mul_comm]
        _ ≤ C := hC j
    · have h1 := spectralStripMarkushevichBasis_one_le_norm_mul χ hα hs x Λ _hB j
      have h2 : ‖D(a, hα, hs) (Λ j)‖ ≤ max B 1 := by
        rw [_hD j]
        exact (hB j).trans (le_max_left _ _)
      rw [inv_eq_one_div, div_le_iff₀ hmax]
      calc (1 : ℝ) ≤ ‖D(a, hα, hs) (Λ j)‖ * ‖x j‖ := h1
        _ ≤ max B 1 * ‖x j‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
        _ = ‖x j‖ * max B 1 := mul_comm _ _

/-- Paper: Corollary 10.2.2.3, p. 447, with Remark 10.2.1.5, p. 444, and (10.4.2.24), p. 463.
There is a spectral Markushevich basis of the strip quotient whose functionals are the strip
jets divided by their norms, hence of norm one, and whose vectors have norm at least one. So
the functionals form a normalized family and the vectors a regular family, with no hypothesis
on the zeros. What is not proved, and what the multiplicity bound (#7220) and the finiteness
of the lines (#7453) would not give either, is an upper bound for the norms of the vectors.
Deviation: The corollary takes the jets themselves. -/
theorem spectralStripMarkushevichBasis_unitNormalized_regular
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ (x : SpectralStripJetIndex χ a α s → Q(a, hα, hs))
      (Λ : SpectralStripJetIndex χ a α s → StrongDual ℂ Q(a, hα, hs)),
      IsSpectralMarkushevichBasis x Λ ∧
      (∀ j, D(a, hα, hs) (Λ j) =
        ((‖jetLp(χ, hα, hs, j)‖ : ℝ) : ℂ)⁻¹ • jetLp(χ, hα, hs, j)) ∧
      (∀ j, ‖D(a, hα, hs) (Λ j)‖ = 1) ∧
      IsNormalizedSpectralFamily (fun j ↦ D(a, hα, hs) (Λ j)) ∧
      (∀ j, 1 ≤ ‖x j‖) ∧ IsRegularSpectralFamily x := by
  obtain ⟨x, Λ, hB, hD, hnorm, hN⟩ :=
    spectralStripMarkushevichBasis_unitNormalized (a := a) χ _hχ hα hs
  have hx (j : SpectralStripJetIndex χ a α s) : 1 ≤ ‖x j‖ := by
    have h := spectralStripMarkushevichBasis_one_le_norm_mul χ hα hs x Λ hB j
    rwa [hnorm j, one_mul] at h
  exact ⟨x, Λ, hB, hD, hnorm, hN, hx, 1, one_pos, hx⟩

/-! ## Single-character bounded-height representatives (#7453), order-one strip jets,
and interaction with real multiple-zero finiteness (#7485) -/

section BoundedHeightAndOrderOne

open scoped ComplexConjugate

local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "L2μ'(" l ", " r ", " s ")" => (μ𝔽 |>.withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity l r s (logNorm g))⁻¹)

/-- Conjugating both argument and value preserves a meromorphic normal form and its order. -/
private theorem boundedHeight_conjugate_germ_order (f : ℂ → ℂ) (s : ℂ)
    (hf : MeromorphicNFAt f (conj s)) :
    MeromorphicNFAt (conj ∘ f ∘ conj) s ∧
      meromorphicOrderAt (conj ∘ f ∘ conj) s = meromorphicOrderAt f (conj s) := by
  have hc := Complex.continuous_conj.tendsto s
  rcases hf with hz | ⟨n, g, hg, hn, hfg⟩
  · have hr : conj ∘ f ∘ conj =ᶠ[𝓝 s] 0 := by
      filter_upwards [hc.eventually hz] with w hw
      exact (congrArg conj hw).trans (map_zero _)
    exact ⟨Or.inl hr,
      (meromorphicOrderAt_eq_top_iff.mpr (hr.filter_mono nhdsWithin_le_nhds)).trans
        (meromorphicOrderAt_eq_top_iff.mpr (hz.filter_mono nhdsWithin_le_nhds)).symm⟩
  · have hga : AnalyticAt ℂ (conj ∘ g ∘ conj) s := by
      apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      filter_upwards [hc.eventually (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)] with
        w hw
      simpa only [Complex.conj_conj] using hw.comp_ringHom conj conj
    have hgn : (conj ∘ g ∘ conj) s ≠ 0 := (map_ne_zero_iff _ (starRingEnd ℂ).injective).mpr hn
    have he : (conj ∘ f ∘ conj) =ᶠ[𝓝 s] (· - s) ^ n • (conj ∘ g ∘ conj) := by
      filter_upwards [hc.eventually hfg] with w hw
      simpa only [comp_apply, Pi.smul_apply', Pi.pow_apply, smul_eq_mul, map_mul, map_zpow₀,
        map_sub, Complex.conj_conj] using congrArg conj hw
    have hr : MeromorphicNFAt (conj ∘ f ∘ conj) s := Or.inr ⟨n, _, hga, hgn, he⟩
    have hf' : MeromorphicNFAt f (conj s) := Or.inr ⟨n, g, hg, hn, hfg⟩
    exact ⟨hr, ((meromorphicOrderAt_eq_int_iff hr.meromorphicAt).mpr
      ⟨_, hga, hgn, he.filter_mono nhdsWithin_le_nhds⟩).trans
      ((meromorphicOrderAt_eq_int_iff hf'.meromorphicAt).mpr
        ⟨g, hg, hn, hfg.filter_mono nhdsWithin_le_nhds⟩).symm⟩

/-- On the half-plane of absolute convergence, conjugating the finite Euler product replaces
the unitary character by its inverse and conjugates the complex parameter. -/
private theorem boundedHeight_finite_euler_conj (ψ : PontryaginDual C𝔽) (s : ℂ) (hs : 1 < s.re) :
    finiteHeckeL ψ⁻¹ ⟨s, hs⟩ = conj (finiteHeckeL ψ ⟨conj s, hs⟩) := by
  have htwist (z : ℂ) (g : C𝔽) :
      ideleClassNormTwist ψ⁻¹ z g = conj (ideleClassNormTwist ψ (conj z) g) := by
    have hn : (((ideleClassNorm F g).val : ℝ) : ℂ).arg ≠ Real.pi := by
      rw [Complex.arg_ofReal_of_nonneg (NNReal.coe_nonneg _)]
      exact Real.pi_ne_zero.symm
    change (((ψ g)⁻¹ : Circle) : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ z =
      conj ((ψ g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ (conj z))
    rw [Circle.coe_inv_eq_conj, map_mul, ← Complex.conj_cpow _ _ hn, Complex.conj_ofReal]
  apply (finiteHeckeL_hasProd ψ⁻¹ ⟨s, hs⟩).unique
  apply ((finiteHeckeL_hasProd ψ ⟨conj s, hs⟩).map conj Complex.continuous_conj).congr_fun
  intro v
  have hunit (x : (v.adicCompletionIntegers F)ˣ) :
      (ideleClassNormTwist ψ⁻¹ 0).restrict v x = conj ((ideleClassNormTwist ψ 0).restrict v x) := by
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist ψ⁻¹ 0).restrict v (u : v.adicCompletion F) =
      conj ((ideleClassNormTwist ψ 0).restrict v (u : v.adicCompletion F))
    simp only [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change ideleClassNormTwist ψ⁻¹ 0 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u) =
      conj (ideleClassNormTwist ψ 0 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u))
    simpa only [map_zero] using htwist 0 (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)
  have hu : (ideleClassNormTwist ψ⁻¹ 0).IsUnramifiedAt v ↔
      (ideleClassNormTwist ψ 0).IsUnramifiedAt v := by
    simp only [HeckeCharacter.isUnramifiedAt_iff, hunit,
      map_eq_one_iff _ (starRingEnd ℂ).injective]
  change finiteHeckeEulerFactor ψ⁻¹ v s = conj (finiteHeckeEulerFactor ψ v (conj s))
  by_cases h : (ideleClassNormTwist ψ 0).IsUnramifiedAt v
  · let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    have hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
    let π : (v.adicCompletion F)ˣ := Units.mk0 _ hπ.ne_zero
    rw [← inv_inj, ← map_inv₀,
      finiteHeckeEulerFactor_inv_uniformizer ψ⁻¹ v π hπ (hu.mpr h) hs,
      finiteHeckeEulerFactor_inv_uniformizer ψ v π hπ h (show 1 < (conj s).re from hs),
      map_sub, map_one]
    exact congrArg (1 - ·) (htwist s (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π))
  · unfold finiteHeckeEulerFactor
    rw [ite_eq_right (mt hu.mp h), ite_eq_right h, map_one]

/-- The finite Hecke continuations for inverse unitary characters have the same order at
conjugate points. -/
private theorem boundedHeight_finite_conj_order (ψ : PontryaginDual C𝔽) (s : ℂ) :
    meromorphicOrderAt (finiteHeckeL_exists_continuation ψ⁻¹).choose s =
      meromorphicOrderAt (finiteHeckeL_exists_continuation ψ).choose (conj s) := by
  let fψ := (finiteHeckeL_exists_continuation ψ).choose
  let fI := (finiteHeckeL_exists_continuation ψ⁻¹).choose
  have hψ := (finiteHeckeL_exists_continuation ψ).choose_spec
  have hI := (finiteHeckeL_exists_continuation ψ⁻¹).choose_spec
  let R := conj ∘ fψ ∘ conj
  have hg (z : ℂ) := boundedHeight_conjugate_germ_order fψ z (hψ.1 (mem_univ _))
  have hR : MeromorphicOn R univ := fun z _ ↦ (hg z).1.meromorphicAt
  have he (z : ℂ) (hz : 1 < z.re) : fI z = R z :=
    (hI.2 ⟨z, hz⟩).trans <|
      (boundedHeight_finite_euler_conj ψ z hz).trans (congrArg conj (hψ.2 ⟨conj z, hz⟩)).symm
  have hU : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have ht : meromorphicOrderAt (fI - R) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr
      (eventuallyEq_iff_sub.mp ((hU.mono he).filter_mono nhdsWithin_le_nhds))
  have ht' := (hI.1.meromorphicOn.sub hR).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) ht
  have heq : fI =ᶠ[𝓝[≠] s] R :=
    (meromorphicOrderAt_eq_top_iff.mp ht').mono fun _ hz ↦ sub_eq_zero.mp hz
  exact (meromorphicOrderAt_congr heq).trans (hg s).2

/-- In the open right half-plane, the archimedean factor is holomorphic and nonvanishing, so
the finite and completed continuations have the same meromorphic order. -/
private theorem boundedHeight_meromorphicOrderAt_finite_eq_completed (ψ : PontryaginDual C𝔽)
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (finiteHeckeL_exists_continuation ψ).choose s =
      meromorphicOrderAt (continuedCompletedHeckeL ψ) s := by
  let f := (finiteHeckeL_exists_continuation ψ).choose
  have hf := (finiteHeckeL_exists_continuation ψ).choose_spec
  let L := continuedCompletedHeckeL ψ
  have hL := continuedCompletedHeckeL_spec ψ
  let G (z : ℂ) := (heckeGammaFactor ψ z)⁻¹
  have hG : Differentiable ℂ G := differentiable_inv_heckeGammaFactor ψ
  have hm : MeromorphicOn (fun z ↦ G z * L z) univ :=
    fun z hz ↦ (hG.analyticAt z).meromorphicAt.mul (hL.1 hz).meromorphicAt
  have hU : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have hEq : ∀ z : ℂ, 1 < z.re → f z = G z * L z := fun z hz ↦ by
    change (finiteHeckeL_exists_continuation ψ).choose z = G z * L z
    rw [hf.2 ⟨z, hz⟩]
    change finiteHeckeL ψ ⟨z, hz⟩ = (heckeGammaFactor ψ z)⁻¹ * continuedCompletedHeckeL ψ z
    rw [show continuedCompletedHeckeL ψ z = completedHeckeL ψ ⟨z, hz⟩ from hL.2 ⟨z, hz⟩]
    exact (inv_mul_cancel_left₀
      (heckeGammaFactor_ne_zero_of_re_pos ψ (zero_lt_one.trans hz)) _).symm
  have ht : meromorphicOrderAt (f - fun z ↦ G z * L z) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr
      (eventuallyEq_iff_sub.mp ((hU.mono hEq).filter_mono nhdsWithin_le_nhds))
  have ht' := (hf.1.meromorphicOn.sub hm).meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s) ht
  have heq : f =ᶠ[𝓝[≠] s] fun z ↦ G z * L z :=
    (meromorphicOrderAt_eq_top_iff.mp ht').mono fun _ hz ↦ sub_eq_zero.mp hz
  rw [meromorphicOrderAt_congr heq]
  exact meromorphicOrderAt_mul_of_ne_zero (hG.analyticAt s)
    (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos ψ hs))

/-- Reflection of zero multiplicities by the completed functional equation. -/
private theorem boundedHeight_reflect_dual (ψ : PontryaginDual C𝔽) (σ t : ℝ) :
    mult(ψ, shift(σ, t)) = mult(ψ⁻¹, shift(1 - σ, (-t : ℝ))) := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation ψ _ _
    (continuedCompletedHeckeL_spec ψ).1 (continuedCompletedHeckeL_spec ψ).2
    (continuedCompletedHeckeL_spec ψ⁻¹).1 (continuedCompletedHeckeL_spec ψ⁻¹).2
  let r (z : ℂ) := 1 - z
  have heq : continuedCompletedHeckeL ψ⁻¹ ∘ r = ε * continuedCompletedHeckeL ψ := funext he
  have hr : HasDerivAt r (-1) (shift(σ, t)) := (hasDerivAt_id _).const_sub 1
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL ψ⁻¹)
    (show AnalyticAt ℂ r (shift(σ, t)) by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [heq, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt _) (hne _)] at ho
  have hz : r (shift(σ, t)) = shift(1 - σ, (-t : ℝ)) := by
    dsimp [r]
    push_cast
    ring
  rw [hz] at ho
  rw [ho]

/-- For one character, a bounded height interval contributes only finitely many multiple-zero
abscissae in the closed critical strip. -/
private theorem boundedHeight_lines_finite_on_compact (ψ : PontryaginDual C𝔽) (T : ℝ) :
    {σ : ℝ | σ ∈ Icc (0 : ℝ) 1 ∧ ∃ t : ℝ, |t| ≤ T ∧
      1 < mult(ψ, shift(σ, t))}.Finite := by
  let R := (Icc (0 : ℝ) 1) ×ˢ (Icc (-T) T)
  let A (p : ℝ × ℝ) : ℂ := shift(p.1, p.2)
  have hA : Continuous A :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  have hK : IsCompact (A '' R) := (isCompact_Icc.prod isCompact_Icc).image hA
  let L := continuedCompletedHeckeL ψ
  have hL : MeromorphicOn L (A '' R) :=
    fun z _ ↦ (continuedCompletedHeckeL_spec ψ).1.meromorphicOn z (mem_univ z)
  apply (((MeromorphicOn.divisor L (A '' R)).finiteSupport hK).image Complex.re).subset
  rintro σ ⟨hσ, t, ht, hm⟩
  refine ⟨A (σ, t), ?_, by simp [A]⟩
  change MeromorphicOn.divisor L (A '' R) (A (σ, t)) ≠ 0
  rw [hL.divisor_apply ⟨(σ, t), ⟨hσ, abs_le.mp ht⟩, rfl⟩]
  change 1 < (meromorphicOrderAt L (A (σ, t))).untop₀.toNat at hm
  exact fun heq ↦ by rw [heq] at hm; simp at hm

/-- Paper: Proposition 3.2.1.3(4), p. 123, and Proposition 10.2.2.2, pp. 446–447.
Every positive-order zero of a continued completed Hecke L-function lies in the open
critical strip `0 < Re s < 1`: to the right of or on `Re s = 1` by the nonvanishing on
`Re s ≥ 1`, and to the left of or on `Re s = 0` by the functional equation. -/
theorem continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo
    (ψ : PontryaginDual C𝔽) {σ : ℝ} (t : ℝ) (hσ : σ ∉ Ioo (0 : ℝ) 1) :
    mult(ψ, shift(σ, t)) = 0 := by
  have hge (θ : PontryaginDual C𝔽) (x y : ℝ) (hx : 1 ≤ x) : mult(θ, shift(x, y)) = 0 := by
    by_contra hne
    have hpos : 0 < mult(θ, shift(x, y)) := Nat.pos_of_ne_zero hne
    have ho : 0 < meromorphicOrderAt (continuedCompletedHeckeL θ) (shift(x, y)) := by
      generalize meromorphicOrderAt (continuedCompletedHeckeL θ) (shift(x, y)) = o at hpos ⊢
      cases o with
      | top => simp at hpos
      | coe k =>
        rw [WithTop.untop₀_coe] at hpos
        exact_mod_cast (by omega : 0 < k)
    have hlt := completedHeckeL_continuation_zeros θ _ (continuedCompletedHeckeL_spec θ).1
      (continuedCompletedHeckeL_spec θ).2 (by simp; linarith) ho
    simp at hlt
    linarith
  rcases le_or_gt σ 0 with hle | hpos
  · rw [boundedHeight_reflect_dual ψ σ t]
    exact hge ψ⁻¹ (1 - σ) (-t) (by linarith)
  · exact hge ψ σ t (not_lt.mp fun hlt ↦ hσ ⟨hpos, hlt⟩)

/-- Paper: Proposition 3.2.1.3, p. 123, and Proposition 10.2.2.2, pp. 446–447.
For every single unitary Hecke character (even when not self-dual), the zero multiplicities
of its continued completed L-function are symmetric across the critical line `Re s = 1 / 2`
at the same ordinate `t`. This combines the completed functional equation with Schwarz
reflection of the finite Euler product.
Deviation: The paper uses the functional equation with the inverse character; combining with
conjugation keeps the same character. -/
theorem continuedCompletedHeckeL_multiplicity_reflect_same_character
    (ψ : PontryaginDual C𝔽) (σ t : ℝ) :
    mult(ψ, shift(1 - σ, t)) = mult(ψ, shift(σ, t)) := by
  by_cases hσ : σ ∈ Ioo (0 : ℝ) 1
  · have h1σ : 1 - σ ∈ Ioo (0 : ℝ) 1 := ⟨by linarith [hσ.2], by linarith [hσ.1]⟩
    let s : ℂ := shift(σ, t)
    have hs1 : s.re < 1 := by simpa [s] using hσ.2
    have hrpos : 0 < (1 - s).re := by
      simpa only [Complex.sub_re, Complex.one_re] using sub_pos.mpr hs1
    obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation ψ _ _
      (continuedCompletedHeckeL_spec ψ).1 (continuedCompletedHeckeL_spec ψ).2
      (continuedCompletedHeckeL_spec ψ⁻¹).1 (continuedCompletedHeckeL_spec ψ⁻¹).2
    let r (z : ℂ) := 1 - z
    have hr : HasDerivAt r (-1) s := by simpa [r] using (hasDerivAt_id s).const_sub 1
    have hcomp : continuedCompletedHeckeL ψ⁻¹ ∘ r = ε * continuedCompletedHeckeL ψ := funext he
    have hfe := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL ψ⁻¹)
      (show AnalyticAt ℂ r s by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
    rw [hcomp, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hne s)] at hfe
    have hconj : 1 - conj s = shift(1 - σ, t) := by
      simp [s]
      ring
    have hord : meromorphicOrderAt (continuedCompletedHeckeL ψ) (1 - conj s) =
        meromorphicOrderAt (continuedCompletedHeckeL ψ) s := by
      calc
        meromorphicOrderAt (continuedCompletedHeckeL ψ) (1 - conj s)
            = meromorphicOrderAt (finiteHeckeL_exists_continuation ψ).choose (conj (1 - s)) := by
              rw [map_sub, map_one]
              exact (boundedHeight_meromorphicOrderAt_finite_eq_completed ψ
                (by simpa using hrpos)).symm
        _ = meromorphicOrderAt (finiteHeckeL_exists_continuation ψ⁻¹).choose (1 - s) :=
              (boundedHeight_finite_conj_order ψ (1 - s)).symm
        _ = meromorphicOrderAt (continuedCompletedHeckeL ψ⁻¹) (1 - s) :=
              boundedHeight_meromorphicOrderAt_finite_eq_completed ψ⁻¹ hrpos
        _ = meromorphicOrderAt (continuedCompletedHeckeL ψ) s := hfe.symm
    rw [← hconj]
    exact congrArg (fun o : WithTop ℤ ↦ o.untop₀.toNat) hord
  · have h1σ : 1 - σ ∉ Ioo (0 : ℝ) 1 := fun h ↦ hσ ⟨by linarith [h.2], by linarith [h.1]⟩
    rw [continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo ψ t h1σ,
      continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo ψ t hσ]

/-- Paper: Notation 10.2.1.1, p. 440, and Proposition 10.2.2.2, pp. 446–447.
The bounded-height representative property of #7453 depends only on the norm-one component
of the unitary Hecke character, not on the chosen unitary lift.
Deviation: The paper does not state this. -/
theorem spectralStripJet_bounded_height_iff_of_restriction_eq
    {ψ η : PontryaginDual C𝔽} (hres : ψ.comp restriction = η.comp restriction) :
    (∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(ψ, shift(σ, u))) ↔
    (∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(η, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(η, shift(σ, u))) := by
  obtain ⟨d, hd, -⟩ := spectralZeroMultiplicity_existsUnique_shift_of_restriction_eq ψ η hres
  have hmul (σ t : ℝ) :
      mult(ψ, shift(σ, t)) = mult(η, ((σ : ℝ) : ℂ) + ((t + d : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.ofReal_add]
    exact (hd σ t).2
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T + |d|, fun σ t hσ hm ↦ ?_⟩
    have hm' : 1 < mult(ψ, ((σ : ℝ) : ℂ) + ((t - d : ℝ) : ℂ) * Complex.I) := by
      have h := hmul σ (t - d)
      rw [sub_add_cancel] at h
      rwa [h]
    obtain ⟨u, hu, hmu⟩ := hT σ (t - d) hσ hm'
    refine ⟨u + d, by linarith [abs_add_le u d], ?_⟩
    exact (hmul σ u).symm ▸ hmu
  · rintro ⟨T, hT⟩
    refine ⟨T + |d|, fun σ t hσ hm ↦ ?_⟩
    have hm' : 1 < mult(η, ((σ : ℝ) : ℂ) + ((t + d : ℝ) : ℂ) * Complex.I) :=
      hmul σ t ▸ hm
    obtain ⟨u, hu, hmu⟩ := hT σ (t + d) hσ hm'
    refine ⟨u - d, by linarith [abs_sub u d], ?_⟩
    have h := hmul σ (u - d)
    rw [sub_add_cancel] at h
    rwa [h]

/-- Paper: Proposition 10.2.2.2, pp. 446–447. For a single unitary Hecke character, the
bounded-height representative property of #7453 holds if and only if the multiple zeros in
the open right half-strip `(1 / 2, 1)` lie on finitely many vertical lines.
Deviation: The paper does not state this. -/
theorem spectralStripJet_bounded_height_iff_right_lines_finite (ψ : PontryaginDual C𝔽) :
    (∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(ψ, shift(σ, u))) ↔
    {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ t : ℝ, 1 < mult(ψ, shift(σ, t))}.Finite := by
  classical
  constructor
  · rintro ⟨T, hT⟩
    apply (boundedHeight_lines_finite_on_compact ψ T).subset
    rintro σ ⟨hσ, t, hm⟩
    exact ⟨⟨by linarith [hσ.1], hσ.2.le⟩, hT σ t hσ hm⟩
  · intro hfin
    let S := {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ t : ℝ, 1 < mult(ψ, shift(σ, t))}
    choose u hu using fun σ : S ↦ σ.property.2
    let := hfin.fintype
    obtain ⟨T, hT⟩ := (finite_range (fun σ : S ↦ |u σ|)).bddAbove
    refine ⟨T, fun σ t hσ hm ↦ ?_⟩
    let p : S := ⟨σ, hσ, t, hm⟩
    exact ⟨u p, hT (mem_range_self p), hu p⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447. For a single unitary Hecke character, the
bounded-height representative property of #7453 holds if and only if all multiple zeros of
its continued completed L-function (on both sides of the critical line) lie on finitely
many vertical lines. Unlike the functional equation alone, single-character reflection
requires no passage to the inverse character.
Deviation: The paper does not state this. -/
theorem spectralStripJet_bounded_height_iff_lines_finite (ψ : PontryaginDual C𝔽) :
    (∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(ψ, shift(σ, u))) ↔
    {σ : ℝ | ∃ t : ℝ, 1 < mult(ψ, shift(σ, t))}.Finite := by
  rw [spectralStripJet_bounded_height_iff_right_lines_finite]
  constructor
  · intro hright
    let R := {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ t : ℝ, 1 < mult(ψ, shift(σ, t))}
    apply ((hright.union (hright.image (fun σ : ℝ ↦ 1 - σ))).insert (1 / 2)).subset
    rintro σ ⟨t, hm⟩
    have hopen : σ ∈ Ioo (0 : ℝ) 1 := by
      by_contra hnot
      rw [continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo ψ t hnot] at hm
      omega
    rcases lt_trichotomy σ (1 / 2) with hlt | heq | hgt
    · refine Or.inr (Or.inr ⟨1 - σ, ⟨⟨by linarith, by linarith [hopen.1]⟩, t, ?_⟩, by ring⟩)
      rwa [continuedCompletedHeckeL_multiplicity_reflect_same_character]
    · exact Or.inl heq
    · exact Or.inr (Or.inl ⟨⟨hgt, hopen.2⟩, t, hm⟩)
  · intro hall
    exact hall.subset fun _ h ↦ h.2

/-- Paper: Proposition 10.2.2.2, pp. 446–447. For a single unitary Hecke character, the
bounded-height representative property of #7453 holds if and only if every vertical line
`Re s = x` is isolated from all other vertical lines carrying a multiple zero of `ψ`.
Deviation: The paper does not state this. -/
theorem spectralStripJet_bounded_height_iff_isolated_lines (ψ : PontryaginDual C𝔽) :
    (∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(ψ, shift(σ, u))) ↔
    ∀ x : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ σ t : ℝ, 0 < |σ - x| → |σ - x| < δ →
      mult(ψ, shift(σ, t)) ≤ 1 := by
  rw [spectralStripJet_bounded_height_iff_lines_finite]
  let S := {σ : ℝ | ∃ t : ℝ, 1 < mult(ψ, shift(σ, t))}
  constructor
  · intro hS x
    let F' := (S \ {x}).image (fun σ : ℝ ↦ |σ - x|)
    have hF' : F'.Finite := (hS.sdiff).image _
    obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image _ id (hF'.insert 1) (insert_nonempty _ _)
    have hδ : 0 < δ := by
      rcases hmem with rfl | ⟨σ, ⟨-, hne⟩, rfl⟩
      · exact one_pos
      · exact abs_pos.mpr (sub_ne_zero.mpr hne)
    refine ⟨δ, hδ, fun σ t hpos hlt ↦ ?_⟩
    by_contra! hm
    have hmem' : |σ - x| ∈ insert (1 : ℝ) F' :=
      Or.inr ⟨σ, ⟨⟨t, hm⟩, sub_ne_zero.mp (abs_pos.mp hpos)⟩, rfl⟩
    exact (hmin _ hmem').not_gt hlt
  · intro hiso
    choose δ hδ hfree using hiso
    obtain ⟨T, _, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).elim_nhds_subcover
      (fun x ↦ Ioo (x - δ x) (x + δ x))
      (fun x _ ↦ Ioo_mem_nhds (by linarith [hδ x]) (by linarith [hδ x]))
    refine T.finite_toSet.subset ?_
    rintro σ ⟨t, hm⟩
    have hopen : σ ∈ Ioo (0 : ℝ) 1 := by
      by_contra hnot
      rw [continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo ψ t hnot] at hm
      omega
    obtain ⟨x, hxT, hxl, hxr⟩ := mem_iUnion₂.mp (hcover ⟨hopen.1.le, hopen.2.le⟩)
    have heq : σ = x := by
      by_contra hne
      have hle := hfree x σ t (abs_pos.mpr (sub_ne_zero.mpr hne))
        (abs_lt.mpr ⟨by linarith, by linarith⟩)
      omega
    rwa [heq]

/-- Paper: Proposition 10.2.2.2, pp. 446–447. For a single unitary Hecke character, the
bounded-height representative property of #7453 forces a positive-width multiple-zero-free
strip on both sides of the critical strip (`0 < Re s < δ` and `1 - δ < Re s < 1`), uniformly
in the ordinate.
Deviation: The paper does not state this. -/
theorem spectralStripJet_multiple_zero_free_strip_of_bounded_height (ψ : PontryaginDual C𝔽)
    (h : ∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(ψ, shift(σ, u))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ t : ℝ,
      (σ ∈ Ioo (1 - δ) 1 ∨ σ ∈ Ioo 0 δ) → mult(ψ, shift(σ, t)) ≤ 1 := by
  obtain ⟨δ, hδ, hfree⟩ := (spectralStripJet_bounded_height_iff_isolated_lines ψ).mp h 1
  refine ⟨δ, hδ, fun σ t hσ ↦ ?_⟩
  rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact hfree σ t (abs_pos.mpr (by linarith)) (abs_lt.mpr ⟨by linarith, by linarith⟩)
  · rw [← continuedCompletedHeckeL_multiplicity_reflect_same_character]
    exact hfree (1 - σ) t (abs_pos.mpr (by linarith)) (abs_lt.mpr ⟨by linarith, by linarith⟩)

/-- The logarithm of the idele class norm is continuous. -/
private theorem boundedHeight_continuous_logNorm : Continuous (logNorm : C𝔽 → ℝ) :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp (m𝔽).continuous)).log
    fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt (m𝔽 g))).ne'

/-- Under the canonical modulated Haar measure on an abstract locally compact abelian group with
a continuous section, the log-module pushes forward to Lebesgue measure on `ℝ`. -/
private theorem boundedHeight_logModule_preserving
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (σ : ℝ≥0ˣ →ₜ* G) (hσ : RightInverse σ m) :
    MeasurePreserving (fun g : G ↦ Real.log ((m g).val : ℝ)) (canonicalModulatedHaar m hm) volume := by
  let : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure m.toMonoidHom.ker := Measure.haarMeasure ⊤
  let : IsProbabilityMeasure μ₁ := ⟨Measure.haarMeasure_self⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by
    have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure_of_lebesgue
    infer_instance
  let φ : m.toMonoidHom.ker × ℝ≥0ˣ → G := fun z ↦ (z.1 : G) * σ z.2
  have hφ_cont : Continuous φ :=
    (continuous_subtype_val.comp continuous_fst).mul (σ.continuous.comp continuous_snd)
  have hlog_unit_cont : Continuous (fun t : ℝ≥0ˣ ↦ Real.log (t.val : ℝ)) :=
    (NNReal.continuous_coe.comp Units.continuous_val).log
      fun t ↦ (NNReal.coe_pos.mpr (Units.zero_lt t)).ne'
  have hlog_meas : Measurable (fun g : G ↦ Real.log ((m g).val : ℝ)) :=
    (hlog_unit_cont.comp m.continuous).measurable
  refine ⟨hlog_meas, ?_⟩
  rw [canonicalModulatedHaar_eq_map_prod m hm σ hσ μ₁ Measure.haarMeasure_self,
    Measure.map_map hlog_meas hφ_cont.measurable]
  have hcomp : (fun g : G ↦ Real.log ((m g).val : ℝ)) ∘ φ =
      (fun t : ℝ≥0ˣ ↦ Real.log (t.val : ℝ)) ∘ Prod.snd := by
    funext ⟨k, t⟩
    change Real.log ((m ((k : G) * σ t)).val : ℝ) = Real.log (t.val : ℝ)
    rw [map_mul, show m (k : G) = 1 from k.property, one_mul, hσ t]
  rw [hcomp, ← Measure.map_map hlog_unit_cont.measurable measurable_snd, Measure.map_snd_prod,
    measure_univ, one_smul]
  unfold positiveRealHaar
  have hexp_meas : Measurable (fun x : ℝ ↦ Units.mk0 (Real.exp x).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) :=
    measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
  rw [Measure.map_map hlog_unit_cont.measurable hexp_meas]
  have hid : ((fun t : ℝ≥0ˣ ↦ Real.log (t.val : ℝ)) ∘
      fun x : ℝ ↦ Units.mk0 (Real.exp x).toNNReal
        (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x)))) = id := by
    funext x
    change Real.log ((Real.exp x).toNNReal : ℝ) = x
    rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.log_exp]
  rw [hid, Measure.map_id]

/-- Under the canonical modulated Haar measure on `C𝔽`, the log-norm pushes forward to Lebesgue
measure on `ℝ`. -/
private theorem boundedHeight_logNorm_preserving :
    MeasurePreserving (logNorm : C𝔽 → ℝ) (canonicalModulatedHaar m𝔽 hm𝔽) volume := by
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let σ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  exact boundedHeight_logModule_preserving m𝔽 hm𝔽 σ (canonicalIdeleNormSection_rightInverse F)

/-- Symmetric interval Sobolev density written with `|x|`. -/
private theorem boundedHeight_symmDensity_eq {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x = Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ (s / 2) := by
  unfold intervalSobolevDensity
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos hx, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

private theorem boundedHeight_symmDensity_pos {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    0 < intervalSobolevDensity (-α) α s x := by
  rw [boundedHeight_symmDensity_eq hα]
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

private theorem boundedHeight_symmDensity_inv_continuous {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity (-α) α s (logNorm g))⁻¹) := by
  have hρ : Continuous (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) := by
    have heq : (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) =
        fun g : C𝔽 ↦ Real.exp (2 * α * |logNorm g|) * (1 + (logNorm g) ^ 2) ^ (s / 2) :=
      funext fun g ↦ boundedHeight_symmDensity_eq hα s (logNorm g)
    rw [heq]
    exact (Real.continuous_exp.comp
      (continuous_const.mul boundedHeight_continuous_logNorm.abs)).mul
      (((continuous_const : Continuous (fun _ : C𝔽 ↦ (1 : ℝ))).add
        (boundedHeight_continuous_logNorm.pow 2)).rpow_const fun g ↦ Or.inl (by
          change (1 : ℝ) + (logNorm g) ^ 2 ≠ 0
          positivity))
  exact hρ.inv₀ fun g ↦ (boundedHeight_symmDensity_pos hα s (logNorm g)).ne'

private theorem boundedHeight_integrand_continuous (α s b : ℝ) (k : ℕ) :
    Continuous (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub (continuous_const.mul continuous_abs))).mul
    (continuous_id.pow (2 * k))).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem boundedHeight_integrable_pow_rpow_inv {k : ℕ} {s : ℝ} (h : 2 * (k : ℝ) + 1 < s) :
    Integrable (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < s - 2 * k := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hr).mono'
    ((measurable_id.pow_const (2 * k)).mul
      ((measurable_const.add (measurable_id.pow_const 2)).pow_const
        (s / 2)).inv).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hy : 0 < 1 + x ^ 2 := by positivity
  have h1 : x ^ (2 * k) ≤ (1 + x ^ 2) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg x) (by linarith) k
  have h2 : (1 + x ^ 2) ^ (-(s - 2 * k) / 2) = (1 + x ^ 2) ^ k * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    rw [← Real.rpow_natCast (1 + x ^ 2) k, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
    congr 1
    ring
  rw [Real.norm_of_nonneg (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
    (inv_nonneg.2 (Real.rpow_nonneg hy.le _))), Real.norm_eq_abs, sq_abs, h2]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (Real.rpow_nonneg hy.le _))

private theorem boundedHeight_integrable_exp_neg_abs_mul_pow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) volume := by
  have hcont : Continuous (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul (continuous_id.pow (2 * k))
  let M : ℝ := ((2 * k).factorial : ℝ) / c ^ (2 * k) +
    ((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)
  refine (integrable_inv_one_add_sq.const_mul M).mono' hcont.aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  have hnonneg : 0 ≤ Real.exp (-c * |x|) * x ^ (2 * k) :=
    mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x)
  rw [Real.norm_of_nonneg hnonneg]
  have hu : 0 ≤ c * |x| := mul_nonneg hc.le (abs_nonneg x)
  have h1 := Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k)
  have h2 := Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k + 2)
  have hfac1 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
  have hfac2 : (0 : ℝ) < ((2 * k + 2).factorial : ℝ) := by positivity
  have hc1 : 0 < c ^ (2 * k) := pow_pos hc _
  have hc2 : 0 < c ^ (2 * k + 2) := pow_pos hc _
  have hpow1 : x ^ (2 * k) ≤ (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k) ≤ ((2 * k).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac1).mp h1]
    have hxa : |x| ^ (2 * k) = x ^ (2 * k) := by rw [pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
    linarith
  have hpow2 : x ^ (2 * k) * x ^ 2 ≤
      (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k + 2) ≤ ((2 * k + 2).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac2).mp h2]
    have hxa : |x| ^ (2 * k + 2) = x ^ (2 * k) * x ^ 2 := by
      rw [pow_add, pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    linarith
  have hsum : x ^ (2 * k) * (1 + x ^ 2) ≤ M * Real.exp (c * |x|) := by
    have hM : M * Real.exp (c * |x|) =
        (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) +
        (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
      dsimp only [M]; ring
    linarith
  have hexp_neg : Real.exp (-c * |x|) = (Real.exp (c * |x|))⁻¹ := by rw [neg_mul, Real.exp_neg]
  rw [hexp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _), mul_comm (M * _), ← mul_assoc,
    ← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  linarith

private theorem boundedHeight_stripJet_integrable {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {k : ℕ}
    (h : (-α < b ∧ b < α) ∨ ((b = -α ∨ b = α) ∧ 2 * (k : ℝ) + 1 < s)) :
    Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  rcases h with ⟨hb1, hb2⟩ | ⟨hb, hk⟩
  · have hδ : 0 < α - |b| := by linarith [abs_lt.mpr ⟨hb1, hb2⟩]
    refine (boundedHeight_integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * (α - |b|)) k).mono'
      (boundedHeight_integrand_continuous α s b k).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg]
    have hbx : b * x ≤ |b| * |x| := (le_abs_self (b * x)).trans_eq (abs_mul b x)
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ Real.exp (-(2 * (α - |b|)) * |x|) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hinv : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
    calc Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
        ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * 1 :=
          mul_le_mul_of_nonneg_left hinv
            (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
      _ = Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) := mul_one _
      _ ≤ Real.exp (-(2 * (α - |b|)) * |x|) * x ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hexp (Even.pow_nonneg (even_two_mul k) x)
  · refine (boundedHeight_integrable_pow_rpow_inv hk).mono'
      (boundedHeight_integrand_continuous α s b k).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg, mul_assoc]
    have hba : |b| = α := by
      rcases hb with rfl | rfl
      · rw [abs_neg, abs_of_nonneg hα]
      · exact abs_of_nonneg hα
    have hbx : b * x ≤ α * |x| := by
      calc b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
        _ = α * |x| := by rw [hba]
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (2 * b * x - 2 * α * |x|) * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
        ≤ 1 * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
          mul_le_mul_of_nonneg_right hexp
            (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
              (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
      _ = x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _

/-- Exact squared norm formula for an individual strip jet in `Sec2_Isolated`. -/
private theorem boundedHeight_jetLp_norm_sq (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hν : ν = canonicalModulatedHaar m𝔽 hm𝔽) :
    ‖(spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))‖ ^ 2 =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
  let u := (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
  let f : ℝ → ℝ := fun x ↦
    Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) := by
    have hre : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
    have hre_int : (∫ g : C𝔽, inner ℂ (u g) (u g) ∂(L2μ'(-α, α, s))).re =
        ∫ g : C𝔽, (inner ℂ (u g) (u g)).re ∂(L2μ'(-α, α, s)) :=
      (Complex.reCLM.integral_comp_comm (L2.integrable_inner u u)).symm
    rw [← hre, L2.inner_def, hre_int]
    exact integral_congr_ae (ae_of_all _ fun g ↦ inner_self_eq_norm_sq (𝕜 := ℂ) (u g))
  have hjet_sq (g : C𝔽) : ‖stripJet(χ, j) g‖ ^ 2 =
      Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2) := by
    have hpos : 0 < ((ideleClassNorm F g).val : ℝ) :=
      NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
    have htwist : ‖ideleClassNormTwist (χ j.val.1) (shift(j.val.2.1, j.val.2.2.1)) g‖ =
        Real.exp (j.val.2.1 * logNorm g) := by
      change ‖(χ j.val.1 g : ℂ) *
        (((ideleClassNorm F g).val : ℝ) : ℂ) ^ shift(j.val.2.1, j.val.2.2.1)‖ = _
      rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_def_of_pos hpos,
        mul_comm]
    change ‖ideleClassNormTwist (χ j.val.1) (shift(j.val.2.1, j.val.2.2.1)) g *
      (logNorm g : ℂ) ^ j.val.2.2.2‖ ^ 2 = _
    rw [norm_mul, htwist, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      show Real.exp (j.val.2.1 * logNorm g) ^ 2 = Real.exp (2 * j.val.2.1 * logNorm g) by
        rw [sq, ← Real.exp_add]; congr 1; ring,
      show (|logNorm g| ^ j.val.2.2.2) ^ 2 = (logNorm g) ^ (2 * j.val.2.2.2) by
        rw [← pow_mul, Nat.mul_comm, pow_mul, sq_abs, ← pow_mul]]
  have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) =
      ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
        ∂(L2μ'(-α, α, s)) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (spectralStripJet_memLp χ hα hs j)] with g hg
    rw [hg, hjet_sq g]
  have h3 : ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
      ∂(L2μ'(-α, α, s)) = ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 := by
    rw [integral_withDensity_eq_integral_toReal_smul
      ((boundedHeight_symmDensity_inv_continuous hα s).measurable.ennreal_ofReal)
      (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
    dsimp only [f]
    rw [smul_eq_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (boundedHeight_symmDensity_pos hα s (logNorm g)).le),
      mul_comm, boundedHeight_symmDensity_eq hα, mul_inv, Real.exp_sub, div_eq_mul_inv]
    ring
  have hmp : MeasurePreserving (logNorm : C𝔽 → ℝ) ν volume := by
    rw [hν]; exact boundedHeight_logNorm_preserving
  have hν_eq : ∫ g : C𝔽, f (logNorm g) ∂ν = ∫ x : ℝ, f x ∂volume := by
    rw [← hmp.map_eq, integral_map boundedHeight_continuous_logNorm.measurable.aemeasurable
      (boundedHeight_integrand_continuous α s j.val.2.1 j.val.2.2.2).aestronglyMeasurable]
  have h4 : ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) * ∫ x : ℝ, f x ∂volume := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hν_eq]
  exact h1.trans (h2.trans (h3.trans h4))

/-- A single jet whose norm is bounded by `C` and whose order is at least `(s - 1) / 2` stays at
a positive distance `δ(C, s)` from the edges of the strip, independent of the other jets. -/
private theorem boundedHeight_single_jet_margin {a α s C : ℝ} (hα : 0 ≤ α) (hs : 1 < s) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
      (j : SpectralStripJetIndex χ a α s),
      (s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → ‖jetLp(χ, hα, hs, j)‖ ≤ C →
      |j.val.2.1| ≤ α - δ := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  let c₂ : ℝ := Real.exp (-2) * ((2 : ℝ) ^ (s / 2))⁻¹
  have hc₂ : 0 < c₂ :=
    mul_pos (Real.exp_pos _) (inv_pos.mpr (Real.rpow_pos_of_pos (by norm_num) _))
  let L : ℝ := C ^ 2 / ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₂)
  have hL : 0 ≤ L := div_nonneg (sq_nonneg C) (mul_pos hfac_pos hc₂).le
  refine ⟨Real.exp (-L), Real.exp_pos _, fun χ j hk hC ↦ ?_⟩
  have hj := j.property
  unfold spectralStripMultiplicity at hj
  split_ifs at hj with hb he
  · have habs : |j.val.2.1| < α := abs_lt.mpr hb
    by_cases h1 : 1 ≤ α - |j.val.2.1|
    · have : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    · have hε : α - |j.val.2.1| < 1 := not_le.mp h1
      have hε0 : 0 < α - |j.val.2.1| := sub_pos.mpr habs
      have hone : 1 ≤ (α - |j.val.2.1|)⁻¹ := (one_le_inv₀ hε0).mpr hε.le
      have h2pos : 0 < (2 : ℝ) ^ (s / 2) := Real.rpow_pos_of_pos (by norm_num) _
      have hint' : Integrable (fun x : ℝ ↦ Real.exp (2 * |j.val.2.1| * x - 2 * α * |x|) *
          x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹) volume :=
        boundedHeight_stripJet_integrable hα hs₀(hs)
          (Or.inl ⟨by linarith [abs_nonneg j.val.2.1], habs⟩)
      have hg_int : Integrable ((Ioc 1 (α - |j.val.2.1|)⁻¹).indicator fun x : ℝ ↦ c₂ * x⁻¹)
          volume := by
        refine ((ContinuousOn.integrableOn_Icc ?_).mono_set
          Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
        exact continuousOn_const.mul
          (continuousOn_inv₀.mono fun x hx ↦ (zero_lt_one.trans_le hx.1).ne')
      have hle : ∀ x : ℝ, (Ioc 1 (α - |j.val.2.1|)⁻¹).indicator (fun x : ℝ ↦ c₂ * x⁻¹) x ≤
          Real.exp (2 * |j.val.2.1| * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
        intro x
        by_cases hx : x ∈ Ioc 1 (α - |j.val.2.1|)⁻¹
        · rw [indicator_of_mem hx]
          have hx1 : 1 ≤ x := hx.1.le
          have hx0 : 0 < x := zero_lt_one.trans hx.1
          have hεx : (α - |j.val.2.1|) * x ≤ 1 := by
            have h := mul_le_mul_of_nonneg_left hx.2 hε0.le
            rwa [mul_inv_cancel₀ hε0.ne'] at h
          have hexp : Real.exp (-2) ≤ Real.exp (2 * |j.val.2.1| * x - 2 * α * |x|) := by
            rw [abs_of_pos hx0]
            exact Real.exp_le_exp.mpr (by nlinarith)
          have hD : (1 + x ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * x ^ s := by
            calc (1 + x ^ 2) ^ (s / 2) ≤ (2 * x ^ 2) ^ (s / 2) :=
                  Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
              _ = 2 ^ (s / 2) * x ^ s := by
                  rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast x 2,
                    ← Real.rpow_mul hx0.le]
                  congr 2; push_cast; ring
          have hpow : x ^ s ≤ x ^ (2 * j.val.2.2.2) * x := by
            calc x ^ s ≤ x ^ ((2 * j.val.2.2.2 + 1 : ℕ) : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le hx1 (by push_cast; linarith)
              _ = x ^ (2 * j.val.2.2.2) * x := by rw [Real.rpow_natCast, pow_succ]
          have hDpos : 0 < (1 + x ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos (by positivity) _
          have hfrac : ((2 : ℝ) ^ (s / 2))⁻¹ * x⁻¹ ≤
              x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
            rw [← mul_inv, ← div_eq_mul_inv, inv_eq_one_div,
              div_le_div_iff₀ (mul_pos h2pos hx0) hDpos]
            calc 1 * (1 + x ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * x ^ s := by rw [one_mul]; exact hD
              _ ≤ 2 ^ (s / 2) * (x ^ (2 * j.val.2.2.2) * x) :=
                  mul_le_mul_of_nonneg_left hpow h2pos.le
              _ = x ^ (2 * j.val.2.2.2) * (2 ^ (s / 2) * x) := by ring
          calc c₂ * x⁻¹ = Real.exp (-2) * (((2 : ℝ) ^ (s / 2))⁻¹ * x⁻¹) := by dsimp [c₂]; ring
            _ ≤ Real.exp (2 * |j.val.2.1| * x - 2 * α * |x|) *
                (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
                  mul_le_mul hexp hfrac (by positivity) (Real.exp_pos _).le
            _ = _ := by ring
        · rw [indicator_of_notMem hx]
          exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
            (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
      have hlog : c₂ * Real.log (α - |j.val.2.1|)⁻¹ ≤
          ∫ x : ℝ, Real.exp (2 * |j.val.2.1| * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
        have hmono := integral_mono hg_int hint' hle
        have h2 : ∫ x : ℝ, (Ioc 1 (α - |j.val.2.1|)⁻¹).indicator (fun x : ℝ ↦ c₂ * x⁻¹) x
            ∂volume = c₂ * Real.log (α - |j.val.2.1|)⁻¹ := by
          rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hone,
            intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos
              (zero_lt_one.trans_le hone), div_one]
        linarith
      have hsym : ∫ x : ℝ, Real.exp (2 * |j.val.2.1| * x - 2 * α * |x|) *
          x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume =
          ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
            x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
        rcases abs_cases j.val.2.1 with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]
        · rw [h, ← integral_neg_eq_self (fun x : ℝ ↦ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
            x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹) volume]
          refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
          dsimp only
          rw [abs_neg, neg_sq, (even_two_mul _).neg_pow,
            show 2 * j.val.2.1 * -x = 2 * -j.val.2.1 * x by ring]
      rw [hsym] at hlog
      have hsq : (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
          ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ C ^ 2 := by
        rw [← boundedHeight_jetLp_norm_sq χ hα hs₀(hs) j ν rfl]
        exact pow_le_pow_left₀ (norm_nonneg _) hC 2
      have h4 : Real.log (α - |j.val.2.1|)⁻¹ ≤ L := by
        rw [le_div_iff₀ (mul_pos hfac_pos hc₂)]
        linarith [(mul_le_mul_of_nonneg_left hlog hfac_pos.le).trans hsq]
      rw [Real.log_inv] at h4
      have h5 : Real.exp (-L) ≤ α - |j.val.2.1| := by
        calc Real.exp (-L) ≤ Real.exp (Real.log (α - |j.val.2.1|)) :=
              Real.exp_le_exp.mpr (by linarith)
          _ = α - |j.val.2.1| := Real.exp_log hε0
      linarith
  · linarith [((lt_spectralBoundaryMultiplicity _ _ _).mp hj).2]
  · omega

/-- A subset of strip jets with bounded orders and a positive margin from the strip edges for
orders `≥ (s - 1) / 2` has uniformly bounded norms. -/
private theorem boundedHeight_subset_jetLp_upper {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (K : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
      (j : SpectralStripJetIndex χ a α s),
      j.val.2.2.2 ≤ K → ((s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ) →
      ‖jetLp(χ, hα, hs, j)‖ ≤ C := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let M_bdry : ℝ := ∑ m ∈ Finset.range N,
    ∫ x : ℝ, x ^ (2 * m) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume
  let M_int : ℝ :=
    ∫ x : ℝ, Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) ∂volume
  have hfac_nonneg : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) := NNReal.coe_nonneg _
  have hM_bdry_nonneg : 0 ≤ M_bdry :=
    Finset.sum_nonneg fun m _ ↦ integral_nonneg fun x ↦
      mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have hM_int_nonneg : 0 ≤ M_int :=
    integral_nonneg fun x ↦
      mul_nonneg (Real.exp_pos _).le (add_nonneg zero_le_one (Even.pow_nonneg (even_two_mul K) x))
  have hM_int_integrable : Integrable
      (fun x : ℝ ↦ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K))) volume := by
    have h0 := boundedHeight_integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) 0
    have hK := boundedHeight_integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) K
    refine (h0.add hK).congr (ae_of_all _ fun x ↦ ?_)
    change Real.exp (-(2 * δ) * |x|) * x ^ (2 * 0) +
        Real.exp (-(2 * δ) * |x|) * x ^ (2 * K) =
      Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K))
    simp only [mul_zero, pow_zero, mul_one]
    ring
  let B : ℝ := 1 + (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int)
  have hB_pos : 0 < B := by
    have : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int) :=
      mul_nonneg hfac_nonneg (add_nonneg hM_bdry_nonneg hM_int_nonneg)
    linarith
  refine ⟨Real.sqrt B, Real.sqrt_pos.mpr hB_pos, fun χ j hjK hjmargin ↦ ?_⟩
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      linarith [((lt_spectralBoundaryMultiplicity s _ _).mp hj).2]
    · omega
  have hf_int := boundedHeight_stripJet_integrable hα hs₀(hs) hcond
  have hint_bound : ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
      x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry + M_int := by
    by_cases hk : (j.val.2.2.2 : ℝ) < (s - 1) / 2
    · have hk' : 2 * (j.val.2.2.2 : ℝ) + 1 < s := by linarith
      have hba : |j.val.2.1| ≤ α := abs_le.mpr (SpectralStripJetIndex.mem_strip_order_pos hα j).1
      have h1 : ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
          x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
          ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
        refine integral_mono hf_int (boundedHeight_integrable_pow_rpow_inv hk') fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ α * |x| :=
          ((le_abs_self _).trans_eq (abs_mul _ _)).trans
            (mul_le_mul_of_nonneg_right hba (abs_nonneg x))
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith)
        rw [mul_assoc]
        calc Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
              (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
            ≤ 1 * (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
              mul_le_mul_of_nonneg_right hexp
                (mul_nonneg (Even.pow_nonneg (even_two_mul _) x)
                  (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
          _ = _ := one_mul _
      have hmem : j.val.2.2.2 ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_ceil.mpr hk)
      have h2 : ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry :=
        Finset.single_le_sum (fun m _ ↦ integral_nonneg fun x ↦
          mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
            (inv_nonneg.mpr (Real.rpow_pos_of_pos (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg x)) _).le)) hmem
      linarith
    · have hmargin : |j.val.2.1| ≤ α - δ := hjmargin (not_lt.mp hk)
      have h1 : ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
          x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_int := by
        refine integral_mono hf_int hM_int_integrable fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ (α - δ) * |x| :=
          ((le_abs_self _).trans_eq (abs_mul _ _)).trans
            (mul_le_mul_of_nonneg_right hmargin (abs_nonneg x))
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ Real.exp (-(2 * δ) * |x|) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hpow : x ^ (2 * j.val.2.2.2) ≤ 1 + x ^ (2 * K) := by
          rcases le_or_gt |x| 1 with hx | hx
          · have : x ^ (2 * j.val.2.2.2) ≤ 1 := by
              rw [pow_mul, ← sq_abs]
              exact pow_le_one₀ (sq_nonneg _) (by nlinarith [abs_nonneg x])
            linarith [Even.pow_nonneg (even_two_mul K) x]
          · have : x ^ (2 * j.val.2.2.2) ≤ x ^ (2 * K) := by
              rw [pow_mul, pow_mul, ← sq_abs]
              exact pow_le_pow_right₀ (by nlinarith [abs_nonneg x]) hjK
            linarith
        have hinv : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
        calc Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
              ((1 + x ^ 2) ^ (s / 2))⁻¹
            ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * 1 :=
              mul_le_mul_of_nonneg_left hinv
                (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
          _ = Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) := mul_one _
          _ ≤ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) :=
              mul_le_mul hexp hpow (Even.pow_nonneg (even_two_mul _) x) (Real.exp_pos _).le
      linarith
  have hsq : ‖jetLp(χ, hα, hs, j)‖ ^ 2 ≤ B := by
    rw [boundedHeight_jetLp_norm_sq χ hα hs₀(hs) j ν rfl]
    calc (Measure.haarScalarFactor μ𝔽 ν : ℝ) * _
        ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int) :=
          mul_le_mul_of_nonneg_left hint_bound hfac_nonneg
      _ ≤ B := by dsimp [B]; linarith
  calc ‖jetLp(χ, hα, hs, j)‖ = Real.sqrt (‖jetLp(χ, hα, hs, j)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hsq

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. For a single norm-one component `ω`,
the bounded-height representative property of #7453 is equivalent to a common upper bound for the
norms of the order-one strip jets in component `ω` on every strip of half-width one with `s = 2`.
No multiplicity bound (#7220) is involved on either side.
Deviation: The paper does not state this. It separates #7453 from #7220 at the strip-jet norm
level for each fixed component. -/
theorem spectralStripJet_bounded_height_iff_orderOne_upperBound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ω : PontryaginDual C₁) :
    (∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(χ ω, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(χ ω, shift(σ, u))) ↔
    (∀ a : ℝ, ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a 1 2,
      j.val.1 = ω → j.val.2.2.2 = 1 →
      ‖(spectralStripJet_memLp χ zero_le_one zero_le_two j).toLp (stripJet(χ, j))‖ ≤ C) := by
  rw [spectralStripJet_bounded_height_iff_lines_finite]
  constructor
  · intro hfin a
    let T := {σ : ℝ | (∃ t : ℝ, 1 < mult(χ ω, shift(σ, t))) ∧ |σ - a| < 1}
    have hT : T.Finite := hfin.subset fun _ h ↦ h.1
    let d (σ : ℝ) := (1 : ℝ) - |σ - a|
    obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image _ id ((hT.image d).insert 1)
      (insert_nonempty _ _)
    have hδ : 0 < δ := by
      rcases hmem with rfl | ⟨σ, hσ, rfl⟩
      · exact one_pos
      · exact sub_pos.mpr hσ.2
    obtain ⟨C, -, hC⟩ := boundedHeight_subset_jetLp_upper (F := F) (a := a) zero_le_one one_lt_two
      1 δ hδ
    refine ⟨C, fun j hω hk ↦ hC χ j hk.le fun _ ↦ ?_⟩
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with hb he
    · have hσ : a + j.val.2.1 ∈ T :=
        ⟨⟨j.val.2.2.1, by rw [← hω]; omega⟩, by simpa using abs_lt.mpr hb⟩
      have hdist : δ ≤ 1 - |j.val.2.1| := by
        simpa [d] using hmin (d (a + j.val.2.1)) (Or.inr (mem_image_of_mem d hσ))
      linarith
    · have hlt := ((lt_spectralBoundaryMultiplicity 2 _ _).mp hj).2
      rw [hk] at hlt
      norm_num at hlt
    · omega
  · intro hbd
    have hmargin : ∀ a : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ σ t : ℝ,
        |σ - a| < 1 → 1 < mult(χ ω, shift(σ, t)) → |σ - a| ≤ 1 - δ := by
      intro a
      obtain ⟨C, hC⟩ := hbd a
      obtain ⟨δ, hδ, hδC⟩ := boundedHeight_single_jet_margin (F := F) (a := a) (C := C)
        zero_le_one one_lt_two
      refine ⟨δ, hδ, fun σ t hlt hm ↦ ?_⟩
      let j : SpectralStripJetIndex χ a 1 2 := ⟨(ω, σ - a, t, 1), by
        change 1 < spectralStripMultiplicity 1 2 (σ - a) (mult(χ ω, shift(a + (σ - a), t)))
        rw [spectralStripMultiplicity_interior (abs_lt.mp hlt), show a + (σ - a) = σ by ring]
        exact hm⟩
      exact hδC χ j (by norm_num) (hC j rfl rfl)
    choose δ hδ hsep using hmargin
    let r (x : ℝ) := min 1 (min (δ (x - 1)) (δ (x + 1)))
    have hr (x : ℝ) : 0 < r x := lt_min one_pos (lt_min (hδ _) (hδ _))
    obtain ⟨T, _, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).elim_nhds_subcover
      (fun x ↦ Ioo (x - r x) (x + r x))
      (fun x _ ↦ Ioo_mem_nhds (by linarith [hr x]) (by linarith [hr x]))
    refine T.finite_toSet.subset ?_
    rintro y ⟨t, hm⟩
    have hy : y ∈ Icc (0 : ℝ) 1 := by
      by_contra hnot
      have hopen : y ∉ Ioo (0 : ℝ) 1 := fun h ↦ hnot ⟨h.1.le, h.2.le⟩
      rw [continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo (χ ω) t hopen] at hm
      omega
    obtain ⟨x, hxT, hxl, hxr⟩ := mem_iUnion₂.mp (hcover hy)
    have hr1 : r x ≤ 1 := min_le_left _ _
    have hrL : r x ≤ δ (x - 1) := (min_le_right _ _).trans (min_le_left _ _)
    have hrR : r x ≤ δ (x + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have heq : y = x := by
      rcases lt_trichotomy y x with hlt | heq | hgt
      · have h := hsep (x - 1) y t (abs_lt.mpr ⟨by linarith, by linarith⟩) hm
        linarith [le_abs_self (y - (x - 1))]
      · exact heq
      · have h := hsep (x + 1) y t (abs_lt.mpr ⟨by linarith, by linarith⟩) hm
        linarith [neg_le_abs (y - (x + 1))]
    rwa [heq]

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. Across all components, the
multiple zeros of the chosen completed Hecke L-functions lie on finitely many vertical lines
(#7453 together with #7485) if and only if on every strip of half-width one with `s = 2`, the
order-one strip jets have a common norm upper bound. No bound on multiplicities (#7220) is
involved on either side.
Deviation: The paper does not state this. Together with
`spectralStripJet_upperBound_wide_iff_multiplicity_bounded`, it separates the multiplicity
bound (#7220) from the finiteness of the vertical lines (#7453 and #7485) purely in terms of
strip-jet norms. -/
theorem spectralStripJet_multiple_zero_lines_finite_iff_orderOne_upperBound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) :
    {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))}.Finite ↔
    (∀ a : ℝ, ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a 1 2, j.val.2.2.2 = 1 →
      ‖(spectralStripJet_memLp χ zero_le_one zero_le_two j).toLp (stripJet(χ, j))‖ ≤ C) := by
  constructor
  · intro hfin a
    let T := {σ : ℝ | (∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))) ∧
      |σ - a| < 1}
    have hT : T.Finite := hfin.subset fun _ h ↦ h.1
    let d (σ : ℝ) := (1 : ℝ) - |σ - a|
    obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image _ id ((hT.image d).insert 1)
      (insert_nonempty _ _)
    have hδ : 0 < δ := by
      rcases hmem with rfl | ⟨σ, hσ, rfl⟩
      · exact one_pos
      · exact sub_pos.mpr hσ.2
    obtain ⟨C, -, hC⟩ := boundedHeight_subset_jetLp_upper (F := F) (a := a) zero_le_one one_lt_two
      1 δ hδ
    refine ⟨C, fun j hk ↦ hC χ j hk.le fun _ ↦ ?_⟩
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with hb he
    · have hσ : a + j.val.2.1 ∈ T :=
        ⟨⟨j.val.1, j.val.2.2.1, by omega⟩, by simpa using abs_lt.mpr hb⟩
      have hdist : δ ≤ 1 - |j.val.2.1| := by
        simpa [d] using hmin (d (a + j.val.2.1)) (Or.inr (mem_image_of_mem d hσ))
      linarith
    · have hlt := ((lt_spectralBoundaryMultiplicity 2 _ _).mp hj).2
      rw [hk] at hlt
      norm_num at hlt
    · omega
  · intro hbd
    have hmargin : ∀ a : ℝ, ∃ δ : ℝ, 0 < δ ∧ ∀ (ω : PontryaginDual C₁) (σ t : ℝ),
        |σ - a| < 1 → 1 < mult(χ ω, shift(σ, t)) → |σ - a| ≤ 1 - δ := by
      intro a
      obtain ⟨C, hC⟩ := hbd a
      obtain ⟨δ, hδ, hδC⟩ := boundedHeight_single_jet_margin (F := F) (a := a) (C := C)
        zero_le_one one_lt_two
      refine ⟨δ, hδ, fun ω σ t hlt hm ↦ ?_⟩
      let j : SpectralStripJetIndex χ a 1 2 := ⟨(ω, σ - a, t, 1), by
        change 1 < spectralStripMultiplicity 1 2 (σ - a) (mult(χ ω, shift(a + (σ - a), t)))
        rw [spectralStripMultiplicity_interior (abs_lt.mp hlt), show a + (σ - a) = σ by ring]
        exact hm⟩
      exact hδC χ j (by norm_num) (hC j rfl)
    choose δ hδ hsep using hmargin
    let r (x : ℝ) := min 1 (min (δ (x - 1)) (δ (x + 1)))
    have hr (x : ℝ) : 0 < r x := lt_min one_pos (lt_min (hδ _) (hδ _))
    obtain ⟨T, _, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).elim_nhds_subcover
      (fun x ↦ Ioo (x - r x) (x + r x))
      (fun x _ ↦ Ioo_mem_nhds (by linarith [hr x]) (by linarith [hr x]))
    refine T.finite_toSet.subset ?_
    rintro y ⟨ω, t, hm⟩
    have hy : y ∈ Icc (0 : ℝ) 1 := by
      by_contra hnot
      have hopen : y ∉ Ioo (0 : ℝ) 1 := fun h ↦ hnot ⟨h.1.le, h.2.le⟩
      rw [continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo (χ ω) t hopen] at hm
      omega
    obtain ⟨x, hxT, hxl, hxr⟩ := mem_iUnion₂.mp (hcover hy)
    have hr1 : r x ≤ 1 := min_le_left _ _
    have hrL : r x ≤ δ (x - 1) := (min_le_right _ _).trans (min_le_left _ _)
    have hrR : r x ≤ δ (x + 1) := (min_le_right _ _).trans (min_le_right _ _)
    have heq : y = x := by
      rcases lt_trichotomy y x with hlt | heq | hgt
      · have h := hsep (x - 1) ω y t (abs_lt.mpr ⟨by linarith, by linarith⟩) hm
        linarith [le_abs_self (y - (x - 1))]
      · exact heq
      · have h := hsep (x + 1) ω y t (abs_lt.mpr ⟨by linarith, by linarith⟩) hm
        linarith [neg_le_abs (y - (x + 1))]
    rwa [heq]

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. Across all components, finiteness
of the vertical lines carrying multiple zeros is equivalent to boundedness of the strip jets of
every fixed order cap `K` on every strip `(a, α, s)`.
Deviation: The paper does not state this. -/
theorem spectralStripJet_multiple_zero_lines_finite_iff_boundedOrder_upperBound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) :
    {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))}.Finite ↔
    (∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s) (K : ℕ), ∃ C : ℝ,
      ∀ j : SpectralStripJetIndex χ a α s, j.val.2.2.2 ≤ K → ‖jetLp(χ, hα, hs, j)‖ ≤ C) := by
  constructor
  · intro hfin a α s hα hs K
    let T := {σ : ℝ | (∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))) ∧
      |σ - a| < α}
    have hT : T.Finite := hfin.subset fun _ h ↦ h.1
    let d (σ : ℝ) := α - |σ - a|
    obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image _ id ((hT.image d).insert 1)
      (insert_nonempty _ _)
    have hδ : 0 < δ := by
      rcases hmem with rfl | ⟨σ, hσ, rfl⟩
      · exact one_pos
      · exact sub_pos.mpr hσ.2
    obtain ⟨C, -, hC⟩ := boundedHeight_subset_jetLp_upper (F := F) (a := a) hα hs K δ hδ
    refine ⟨C, fun j hjK ↦ hC χ j hjK fun hk ↦ ?_⟩
    have hkpos : 0 < j.val.2.2.2 := by exact_mod_cast (by linarith : (0 : ℝ) < j.val.2.2.2)
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with hb he
    · have hσ : a + j.val.2.1 ∈ T :=
        ⟨⟨j.val.1, j.val.2.2.1, by omega⟩, by simpa using abs_lt.mpr hb⟩
      have hdist : δ ≤ α - |j.val.2.1| := by
        simpa [d] using hmin (d (a + j.val.2.1)) (Or.inr (mem_image_of_mem d hσ))
      linarith
    · linarith [((lt_spectralBoundaryMultiplicity s _ _).mp hj).2]
    · omega
  · intro hall
    rw [spectralStripJet_multiple_zero_lines_finite_iff_orderOne_upperBound]
    intro a
    obtain ⟨C, hC⟩ := hall a 1 2 zero_le_one one_lt_two 1
    exact ⟨C, fun j hk ↦ hC j hk.le⟩

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. For a single norm-one component `ω`,
the norms of all strip jets in component `ω` have a common upper bound on every strip if and only
if the zero multiplicities of `χ ω` are bounded and `χ ω` satisfies the bounded-height
representative property of #7453.
Deviation: The paper does not state this. It is the single-component counterpart of
`spectralStripJet_upperBound_iff_multiple_zeros`. -/
theorem spectralStripJet_component_upperBound_iff
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ω : PontryaginDual C₁) :
    (∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s), ∃ C : ℝ,
      ∀ j : SpectralStripJetIndex χ a α s, j.val.1 = ω → ‖jetLp(χ, hα, hs, j)‖ ≤ C) ↔
    ((∃ M : ℕ, ∀ σ t : ℝ, mult(χ ω, shift(σ, t)) ≤ M) ∧
      (∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(χ ω, shift(σ, t)) →
        ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(χ ω, shift(σ, u)))) := by
  let χc : PontryaginDual C₁ → PontryaginDual C𝔽 := fun _ ↦ χ ω
  have hcast (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s) :
      (∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, j.val.1 = ω → ‖jetLp(χ, hα, hs, j)‖ ≤ C) ↔
      (∃ C : ℝ, ∀ j : SpectralStripJetIndex χc a α s, ‖jetLp(χc, hα, hs, j)‖ ≤ C) := by
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨C, fun j ↦ ?_⟩
      let j' : SpectralStripJetIndex χ a α s :=
        ⟨(ω, j.val.2.1, j.val.2.2.1, j.val.2.2.2), j.property⟩
      have heq : ‖jetLp(χc, hα, hs, j)‖ = ‖jetLp(χ, hα, hs, j')‖ := by
        let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
        let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
        have hsq : ‖jetLp(χc, hα, hs, j)‖ ^ 2 = ‖jetLp(χ, hα, hs, j')‖ ^ 2 :=
          (boundedHeight_jetLp_norm_sq χc hα hs₀(hs) j ν rfl).trans
            (boundedHeight_jetLp_norm_sq χ hα hs₀(hs) j' ν rfl).symm
        nlinarith [sq_nonneg (‖jetLp(χc, hα, hs, j)‖ - ‖jetLp(χ, hα, hs, j')‖),
          norm_nonneg (jetLp(χc, hα, hs, j)), norm_nonneg (jetLp(χ, hα, hs, j'))]
      rw [heq]
      exact hC j' rfl
    · rintro ⟨C, hC⟩
      refine ⟨C, fun j hω ↦ ?_⟩
      let j' : SpectralStripJetIndex χc a α s :=
        ⟨(ω, j.val.2.1, j.val.2.2.1, j.val.2.2.2), by
          have hj := j.property
          rwa [hω] at hj⟩
      have heq : ‖jetLp(χ, hα, hs, j)‖ = ‖jetLp(χc, hα, hs, j')‖ := by
        let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
        let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
        have hsq : ‖jetLp(χ, hα, hs, j)‖ ^ 2 = ‖jetLp(χc, hα, hs, j')‖ ^ 2 :=
          (boundedHeight_jetLp_norm_sq χ hα hs₀(hs) j ν rfl).trans
            (boundedHeight_jetLp_norm_sq χc hα hs₀(hs) j' ν rfl).symm
        nlinarith [sq_nonneg (‖jetLp(χ, hα, hs, j)‖ - ‖jetLp(χc, hα, hs, j')‖),
          norm_nonneg (jetLp(χ, hα, hs, j)), norm_nonneg (jetLp(χc, hα, hs, j'))]
      rw [heq]
      exact hC j'
  have hall : (∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s), ∃ C : ℝ,
      ∀ j : SpectralStripJetIndex χ a α s, j.val.1 = ω → ‖jetLp(χ, hα, hs, j)‖ ≤ C) ↔
      (∀ (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s), ∃ C : ℝ,
      ∀ j : SpectralStripJetIndex χc a α s, ‖jetLp(χc, hα, hs, j)‖ ≤ C) :=
    forall₅_congr fun a α s hα hs ↦ hcast a α s hα hs
  rw [hall, spectralStripJet_upperBound_iff_multiple_zeros χc,
    spectralStripJet_bounded_height_iff_lines_finite (χ ω)]
  constructor
  · rintro ⟨⟨M, hM⟩, hfin⟩
    refine ⟨⟨M, fun σ t ↦ hM ω σ t⟩, hfin.subset fun σ ⟨t, hm⟩ ↦ ⟨ω, t, hm⟩⟩
  · rintro ⟨⟨M, hM⟩, hfin⟩
    refine ⟨⟨M, fun _ σ t ↦ hM σ t⟩, hfin.subset fun σ ⟨_, t, hm⟩ ↦ ⟨t, hm⟩⟩

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. On the single critical strip
`a = 1 / 2`, `α = 1 / 2`, `s = 2`, the order-one strip jets in a fixed component `ω` have
bounded norms if and only if `χ ω` has a positive-width multiple-zero-free strip
`(0, δ) ∪ (1 - δ, 1)` uniformly in the ordinate.
Deviation: The paper does not state this. -/
theorem spectralStripJet_criticalStrip_component_orderOne_iff
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (ω : PontryaginDual C₁) :
    (∃ C : ℝ, ∀ j : SpectralStripJetIndex χ (1 / 2) (1 / 2) 2,
      j.val.1 = ω → j.val.2.2.2 = 1 →
      ‖(spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1 / 2) zero_le_two j).toLp
        (stripJet(χ, j))‖ ≤ C) ↔
    (∃ δ : ℝ, 0 < δ ∧ ∀ σ t : ℝ,
      (σ ∈ Ioo (1 - δ) 1 ∨ σ ∈ Ioo 0 δ) → mult(χ ω, shift(σ, t)) ≤ 1) := by
  have hα : (0 : ℝ) ≤ 1 / 2 := by norm_num
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨δ, hδ, hmargin⟩ := boundedHeight_single_jet_margin (F := F) (a := 1 / 2) (C := C)
      hα one_lt_two
    refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), fun σ t hσ ↦ ?_⟩
    by_contra! hm
    have hopen : σ ∈ Ioo (0 : ℝ) 1 := by
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [min_le_right δ (1 / 2)], h2⟩
      · exact ⟨h1, by linarith [min_le_right δ (1 / 2)]⟩
    have hb : σ - 1 / 2 ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [hopen.1], by linarith [hopen.2]⟩
    let j : SpectralStripJetIndex χ (1 / 2) (1 / 2) 2 := ⟨(ω, σ - 1 / 2, t, 1), by
      change 1 < spectralStripMultiplicity (1 / 2) 2 (σ - 1 / 2)
        (mult(χ ω, shift(1 / 2 + (σ - 1 / 2), t)))
      rw [spectralStripMultiplicity_interior hb, show (1 / 2 : ℝ) + (σ - 1 / 2) = σ by ring]
      exact hm⟩
    have hsep : |σ - 1 / 2| ≤ 1 / 2 - δ := hmargin χ j (by norm_num) (hC j rfl rfl)
    have hbounds := abs_le.mp hsep
    rcases hσ with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith [min_le_left δ (1 / 2)]
    · linarith [min_le_left δ (1 / 2)]
  · rintro ⟨δ, hδ, hfree⟩
    obtain ⟨C, -, hC⟩ := boundedHeight_subset_jetLp_upper (F := F) (a := 1 / 2) hα one_lt_two
      1 (min δ (1 / 2)) (lt_min hδ (by norm_num))
    refine ⟨C, fun j hω hk ↦ hC χ j hk.le fun _ ↦ ?_⟩
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with hb he
    · have hm : 1 < mult(χ ω, shift(1 / 2 + j.val.2.1, j.val.2.2.1)) := by
        rw [← hω]; omega
      have hleft : δ ≤ 1 / 2 + j.val.2.1 := by
        by_contra! hlt
        exact (hfree (1 / 2 + j.val.2.1) j.val.2.2.1 (Or.inr ⟨by linarith [hb.1], hlt⟩)).not_gt hm
      have hright : 1 / 2 + j.val.2.1 ≤ 1 - δ := by
        by_contra! hgt
        exact (hfree (1 / 2 + j.val.2.1) j.val.2.2.1 (Or.inl ⟨hgt, by linarith [hb.2]⟩)).not_gt hm
      exact abs_le.mpr ⟨by linarith [min_le_left δ (1 / 2)], by linarith [min_le_left δ (1 / 2)]⟩
    · have hlt := ((lt_spectralBoundaryMultiplicity 2 _ _).mp hj).2
      rw [hk] at hlt
      norm_num at hlt
    · omega

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. On the single critical strip
`a = 1 / 2`, `α = 1 / 2`, `s = 2`, the order-one strip jets across all components have bounded
norms if and only if there is one positive width `δ > 0` such that no unitary Hecke character
of `F` has any multiple zero in `(0, δ) ∪ (1 - δ, 1)`, uniformly in both character and height.
Deviation: The paper does not state this. -/
theorem spectralStripJet_criticalStrip_orderOne_iff_uniform_margin
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) :
    (∃ C : ℝ, ∀ j : SpectralStripJetIndex χ (1 / 2) (1 / 2) 2, j.val.2.2.2 = 1 →
      ‖(spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1 / 2) zero_le_two j).toLp
        (stripJet(χ, j))‖ ≤ C) ↔
    (∃ δ : ℝ, 0 < δ ∧ ∀ (ψ : PontryaginDual C𝔽) (σ t : ℝ),
      (σ ∈ Ioo (1 - δ) 1 ∨ σ ∈ Ioo 0 δ) → mult(ψ, shift(σ, t)) ≤ 1) := by
  have hα : (0 : ℝ) ≤ 1 / 2 := by norm_num
  constructor
  · rintro ⟨C, hC⟩
    obtain ⟨δ, hδ, hmargin⟩ := boundedHeight_single_jet_margin (F := F) (a := 1 / 2) (C := C)
      hα one_lt_two
    refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), fun ψ σ t hσ ↦ ?_⟩
    obtain ⟨d, hd, -⟩ := hχ.existsUnique_ordinate_shift ψ
    let td : ℝ := t + d
    have hmul : mult(ψ, shift(σ, t)) = mult(χ (ψ.comp restriction), shift(σ, td)) := by
      dsimp only [td]
      rw [Complex.ofReal_add]
      exact (hd σ t).2
    rw [hmul]
    by_contra! hm
    have hopen : σ ∈ Ioo (0 : ℝ) 1 := by
      rcases hσ with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [min_le_right δ (1 / 2)], h2⟩
      · exact ⟨h1, by linarith [min_le_right δ (1 / 2)]⟩
    have hb : σ - 1 / 2 ∈ Ioo (-(1 / 2) : ℝ) (1 / 2) := ⟨by linarith [hopen.1], by linarith [hopen.2]⟩
    let j : SpectralStripJetIndex χ (1 / 2) (1 / 2) 2 :=
      ⟨(ψ.comp restriction, σ - 1 / 2, td, 1), by
        change 1 < spectralStripMultiplicity (1 / 2) 2 (σ - 1 / 2)
          (mult(χ (ψ.comp restriction), shift(1 / 2 + (σ - 1 / 2), td)))
        rw [spectralStripMultiplicity_interior hb, show (1 / 2 : ℝ) + (σ - 1 / 2) = σ by ring]
        exact hm⟩
    have hsep : |σ - 1 / 2| ≤ 1 / 2 - δ := hmargin χ j (by norm_num) (hC j rfl)
    have hbounds := abs_le.mp hsep
    rcases hσ with ⟨h1, _⟩ | ⟨_, h2⟩
    · linarith [min_le_left δ (1 / 2)]
    · linarith [min_le_left δ (1 / 2)]
  · rintro ⟨δ, hδ, hfree⟩
    obtain ⟨C, -, hC⟩ := boundedHeight_subset_jetLp_upper (F := F) (a := 1 / 2) hα one_lt_two
      1 (min δ (1 / 2)) (lt_min hδ (by norm_num))
    refine ⟨C, fun j hk ↦ hC χ j hk.le fun _ ↦ ?_⟩
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with hb he
    · have hm : 1 < mult(χ j.val.1, shift(1 / 2 + j.val.2.1, j.val.2.2.1)) := by omega
      have hleft : δ ≤ 1 / 2 + j.val.2.1 := by
        by_contra! hlt
        exact (hfree (χ j.val.1) (1 / 2 + j.val.2.1) j.val.2.2.1
          (Or.inr ⟨by linarith [hb.1], hlt⟩)).not_gt hm
      have hright : 1 / 2 + j.val.2.1 ≤ 1 - δ := by
        by_contra! hgt
        exact (hfree (χ j.val.1) (1 / 2 + j.val.2.1) j.val.2.2.1
          (Or.inl ⟨hgt, by linarith [hb.2]⟩)).not_gt hm
      exact abs_le.mpr ⟨by linarith [min_le_left δ (1 / 2)], by linarith [min_le_left δ (1 / 2)]⟩
    · have hlt := ((lt_spectralBoundaryMultiplicity 2 _ _).mp hj).2
      rw [hk] at hlt
      norm_num at hlt
    · omega

/-- Paper: Proposition 10.2.2.2 and (10.2.2.8), pp. 446–447. On the single critical strip
`a = 1 / 2`, `α = 1 / 2`, `s = 2`, the norms of all strip jets have a common upper bound if and
only if the multiplicity bound #7220 holds and there is a uniform multiple-zero-free strip
`(0, δ) ∪ (1 - δ, 1)` across all unitary Hecke characters.
Deviation: The paper does not state this. Unlike the full all-strips equivalence
`spectralStripJet_upperBound_iff_multiple_zeros`, the critical strip alone does not control
accumulation of multiple-zero lines at interior abscissae in `(0, 1)`. -/
theorem spectralStripJet_criticalStrip_upperBound_iff
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) :
    (∃ C : ℝ, ∀ j : SpectralStripJetIndex χ (1 / 2) (1 / 2) 2,
      ‖(spectralStripJet_memLp χ (by norm_num : (0 : ℝ) ≤ 1 / 2) zero_le_two j).toLp
        (stripJet(χ, j))‖ ≤ C) ↔
    ((∃ M : ℕ, ∀ (ω : PontryaginDual C₁) (σ t : ℝ), mult(χ ω, shift(σ, t)) ≤ M) ∧
      ∃ δ : ℝ, 0 < δ ∧ ∀ (ψ : PontryaginDual C𝔽) (σ t : ℝ),
        (σ ∈ Ioo (1 - δ) 1 ∨ σ ∈ Ioo 0 δ) → mult(ψ, shift(σ, t)) ≤ 1) := by
  have hα : (0 : ℝ) ≤ 1 / 2 := by norm_num
  constructor
  · intro h
    obtain ⟨M, hM⟩ := spectralStripJet_multiplicity_le_of_upperBound χ hα one_lt_two h
    refine ⟨⟨M, fun ω σ t ↦ ?_⟩,
      (spectralStripJet_criticalStrip_orderOne_iff_uniform_margin χ hχ).mp
        (h.imp fun C hC j _ ↦ hC j)⟩
    by_cases hopen : σ ∈ Ioo (0 : ℝ) 1
    · have hlt : |σ - 1 / 2| < 1 / 2 := abs_lt.mpr ⟨by linarith [hopen.1], by linarith [hopen.2]⟩
      simpa only [show (1 / 2 : ℝ) + (σ - 1 / 2) = σ by ring] using hM ω (σ - 1 / 2) t hlt
    · rw [continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo (χ ω) t hopen]
      exact Nat.zero_le _
  · rintro ⟨⟨M, hM⟩, δ, hδ, hfree⟩
    obtain ⟨C, -, hC⟩ := spectralStripJet_upperBound_of_margin (a := 1 / 2) χ hα one_lt_two
      (max M 1) (min δ (1 / 2)) (lt_min hδ (by norm_num)) (fun j ↦ by
        have hj := j.property
        unfold spectralStripMultiplicity at hj
        split_ifs at hj with hb he
        · refine ⟨hj.le.trans ((hM _ _ _).trans (le_max_left _ _)), fun hk ↦ ?_⟩
          have hkpos : 0 < j.val.2.2.2 := by exact_mod_cast (by linarith : (0 : ℝ) < j.val.2.2.2)
          have hm : 1 < mult(χ j.val.1, shift(1 / 2 + j.val.2.1, j.val.2.2.1)) := by omega
          have hleft : δ ≤ 1 / 2 + j.val.2.1 := by
            by_contra! hlt
            exact (hfree (χ j.val.1) (1 / 2 + j.val.2.1) j.val.2.2.1
              (Or.inr ⟨by linarith [hb.1], hlt⟩)).not_gt hm
          have hright : 1 / 2 + j.val.2.1 ≤ 1 - δ := by
            by_contra! hgt
            exact (hfree (χ j.val.1) (1 / 2 + j.val.2.1) j.val.2.2.1
              (Or.inl ⟨hgt, by linarith [hb.2]⟩)).not_gt hm
          exact abs_le.mpr ⟨by linarith [min_le_left δ (1 / 2)],
            by linarith [min_le_left δ (1 / 2)]⟩
        · have hlt := ((lt_spectralBoundaryMultiplicity 2 _ _).mp hj).2
          exact ⟨(show j.val.2.2.2 ≤ 1 by exact_mod_cast (by linarith : (j.val.2.2.2 : ℝ) ≤ 1)).trans
            (le_max_right _ _), fun hk ↦ by linarith⟩
        · omega)
    exact ⟨C, hC⟩

/-! ### Interaction between #7485 (real-segment finiteness) and #7453 (bounded-height
representatives) -/

/-- Paper: Proposition 10.2.2.2, pp. 446–447. Given a finite cover `(E, S)` of the right-half
multiple zeros (the characterization of #7485 from `spectralStripJet_multiple_real_zeros_finite_iff_finite_cover`),
every unitary character whose norm-one restriction lies outside the finite exceptional set `E`
automatically satisfies the bounded-height representative property of #7453.
Deviation: The paper does not state this. -/
theorem spectralStripJet_bounded_height_of_notMem_finiteCover
    (E : Finset (PontryaginDual C₁)) (S : Finset ℝ)
    (hcover : ∀ (ψ : PontryaginDual C𝔽) (σ t : ℝ),
      σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
        ψ.comp restriction ∈ E ∨ σ ∈ S)
    (ψ : PontryaginDual C𝔽) (hψ : ψ.comp restriction ∉ E) :
    ∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(ψ, shift(σ, u)) := by
  rw [spectralStripJet_bounded_height_iff_right_lines_finite]
  refine S.finite_toSet.subset ?_
  rintro σ ⟨hσ, t, hm⟩
  exact (hcover ψ σ t hσ hm).resolve_left hψ

/-- Paper: Proposition 10.2.2.2, pp. 446–447. The real-segment finiteness statement #7485 alone
already implies that outside a finite exceptional set `E` of norm-one components, every unitary
Hecke character satisfies #7453 (bounded-height representatives) and shares one uniform positive
multiple-zero-free strip `(0, δ) ∪ (1 - δ, 1)` at all heights.
Deviation: The paper does not state this. -/
theorem spectralStripJet_multiple_real_zeros_finite_implies_cofinite_bounded_height_and_margin
    (hreal : ∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁,
        1 < mult(χ ω, (σ : ℂ))}.Finite) :
    ∃ (E : Finset (PontryaginDual C₁)) (δ : ℝ), 0 < δ ∧
      ∀ ψ : PontryaginDual C𝔽, ψ.comp restriction ∉ E →
        (∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
          ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(ψ, shift(σ, u))) ∧
        (∀ σ t : ℝ, (σ ∈ Ioo (1 - δ) 1 ∨ σ ∈ Ioo 0 δ) → mult(ψ, shift(σ, t)) ≤ 1) := by
  classical
  obtain ⟨E, S, hcover⟩ :=
    (spectralStripJet_multiple_real_zeros_finite_iff_finite_cover (F := F)).mp hreal
  let D := (S.filter (fun σ : ℝ ↦ σ ∈ Ioo (1 / 2 : ℝ) 1)).image (fun σ : ℝ ↦ (1 : ℝ) - σ)
  obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image _ id ((D.finite_toSet).insert (1 / 2))
    (insert_nonempty _ _)
  have hδ : 0 < δ := by
    rcases hmem with rfl | hD
    · norm_num
    · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hD
      exact sub_pos.mpr (Finset.mem_filter.mp hσ).2.2
  have hδhalf : δ ≤ 1 / 2 := hmin (1 / 2) (Or.inl rfl)
  refine ⟨E, δ, hδ, fun ψ hψ ↦ ⟨spectralStripJet_bounded_height_of_notMem_finiteCover E S hcover
    ψ hψ, fun σ t hσ ↦ ?_⟩⟩
  have hright (x : ℝ) (hx : x ∈ Ioo (1 - δ) 1) : mult(ψ, shift(x, t)) ≤ 1 := by
    by_contra! hm
    have hx_strip : x ∈ Ioo (1 / 2 : ℝ) 1 := ⟨by linarith [hx.1], hx.2⟩
    have hxS : x ∈ S := (hcover ψ x t hx_strip hm).resolve_left hψ
    have hxD : 1 - x ∈ (D : Set ℝ) :=
      Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨hxS, hx_strip⟩, rfl⟩)
    have hle : δ ≤ 1 - x := hmin (1 - x) (Or.inr hxD)
    linarith [hx.1]
  rcases hσ with hr | hl
  · exact hright σ hr
  · rw [← continuedCompletedHeckeL_multiplicity_reflect_same_character]
    exact hright (1 - σ) ⟨by linarith [hl.2], by linarith [hl.1]⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447. Finiteness of the vertical lines carrying multiple
zeros across all components holds if and only if #7485 holds (a finite cover `(E, S)` exists) and
the bounded-height representative property #7453 holds on the finite exceptional set `E` alone.
This refines the #7470 split by restricting #7453 from all components to `E`.
Deviation: The paper does not state this. -/
theorem spectralStripJet_multiple_zero_lines_finite_iff_finiteCover_and_exceptional :
    (∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ →
      {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ), 1 < mult(χ ω, shift(σ, t))}.Finite) ↔
    ∃ (E : Finset (PontryaginDual C₁)) (S : Finset ℝ),
      (∀ (ψ : PontryaginDual C𝔽) (σ t : ℝ), σ ∈ Ioo (1 / 2 : ℝ) 1 →
        1 < mult(ψ, shift(σ, t)) → ψ.comp restriction ∈ E ∨ σ ∈ S) ∧
      (∀ ω ∈ E, ∃ ψ : PontryaginDual C𝔽, ψ.comp restriction = ω ∧
        ∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
          ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(ψ, shift(σ, u))) := by
  classical
  constructor
  · intro hlines
    obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice F
    have hS : {σ : ℝ | ∃ (ω : PontryaginDual C₁) (t : ℝ),
        1 < mult(χ₀ ω, shift(σ, t))}.Finite := hlines χ₀ hχ₀
    refine ⟨∅, hS.toFinset, fun ψ σ t _ hm ↦ Or.inr ?_, fun _ h ↦ absurd h (Finset.notMem_empty _)⟩
    obtain ⟨d, hd, -⟩ := hχ₀.existsUnique_ordinate_shift ψ
    let td : ℝ := t + d
    have hm' : 1 < mult(χ₀ (ψ.comp restriction), shift(σ, td)) := by
      dsimp only [td]
      rw [Complex.ofReal_add]
      exact (hd σ t).2 ▸ hm
    exact hS.mem_toFinset.mpr ⟨ψ.comp restriction, td, hm'⟩
  · rintro ⟨E, S, hcover, hexcept⟩ χ hχ
    have hcomp (ω : PontryaginDual C₁) (hω : ω ∈ E) :
        {σ : ℝ | ∃ t : ℝ, 1 < mult(χ ω, shift(σ, t))}.Finite := by
      obtain ⟨ψ, hψ, hbh⟩ := hexcept ω hω
      rw [← spectralStripJet_bounded_height_iff_lines_finite]
      exact (spectralStripJet_bounded_height_iff_of_restriction_eq
        (hψ.trans (hχ ω).symm)).mp hbh
    let R : Set ℝ := (S : Set ℝ)
    have hR : R.Finite := S.finite_toSet
    let Lset : Set ℝ := (R.union (R.image (fun σ : ℝ ↦ 1 - σ))).insert (1 / 2)
    have hLfin : Lset.Finite := (hR.union (hR.image _)).insert _
    refine (hLfin.union (E.finite_toSet.biUnion hcomp)).subset ?_
    rintro σ ⟨ω, t, hm⟩
    by_cases hω : ω ∈ E
    · exact Or.inr (mem_iUnion₂.mpr ⟨ω, hω, t, hm⟩)
    · apply Or.inl
      have hopen : σ ∈ Ioo (0 : ℝ) 1 := by
        by_contra hnot
        rw [continuedCompletedHeckeL_multiplicity_eq_zero_of_not_mem_Ioo (χ ω) t hnot] at hm
        omega
      rcases lt_trichotomy σ (1 / 2) with hlt | heq | hgt
      · have h1σ : 1 - σ ∈ Ioo (1 / 2 : ℝ) 1 := ⟨by linarith, by linarith [hopen.1]⟩
        have hm' : 1 < mult(χ ω, shift(1 - σ, t)) := by
          rwa [continuedCompletedHeckeL_multiplicity_reflect_same_character]
        have hmem : 1 - σ ∈ S :=
          (hcover (χ ω) (1 - σ) t h1σ hm').resolve_left (by rwa [hχ ω])
        exact Or.inr (Or.inr ⟨1 - σ, hmem, by ring⟩)
      · exact Or.inl heq
      · have hσ' : σ ∈ Ioo (1 / 2 : ℝ) 1 := ⟨hgt, hopen.2⟩
        have hmem : σ ∈ S :=
          (hcover (χ ω) σ t hσ' hm).resolve_left (by rwa [hχ ω])
        exact Or.inr (Or.inl hmem)

/-! ### Multiplicity-forcing zero-free strip transfer and unbounded-height contrast -/

/-- Paper: Proposition 10.2.2.2, pp. 446–447. If a meromorphic factor `f` (such as an Artin
L-function or Dedekind zeta quotient) forces a multiple zero of `continuedCompletedHeckeL ψ`
at every positive-order zero of `f` in `1 / 2 < Re z < 1`, then the single-character
bounded-height property #7453 for `ψ` forces the right-half zeros of `f` onto finitely many
vertical lines and yields a positive-width zero-free strip `1 - δ < Re z < 1` uniformly in
height.
Deviation: The paper does not state this. -/
theorem spectralStripJet_zero_free_strip_of_order_forcing
    (ψ : PontryaginDual C𝔽) (f : ℂ → ℂ)
    (hforce : ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 →
      0 < (meromorphicOrderAt f (shift(σ, t))).untop₀.toNat →
      1 < mult(ψ, shift(σ, t)))
    (hbh : ∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (1 / 2 : ℝ) 1 → 1 < mult(ψ, shift(σ, t)) →
      ∃ u : ℝ, |u| ≤ T ∧ 1 < mult(ψ, shift(σ, u))) :
    {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧
      ∃ t : ℝ, 0 < (meromorphicOrderAt f (shift(σ, t))).untop₀.toNat}.Finite ∧
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ t : ℝ, σ ∈ Ioo (1 - δ) 1 →
      (meromorphicOrderAt f (shift(σ, t))).untop₀.toNat = 0 := by
  constructor
  · refine ((spectralStripJet_bounded_height_iff_right_lines_finite ψ).mp hbh).subset ?_
    rintro σ ⟨hσ, t, hf⟩
    exact ⟨hσ, t, hforce σ t hσ hf⟩
  · obtain ⟨δ, hδ, hfree⟩ := spectralStripJet_multiple_zero_free_strip_of_bounded_height ψ hbh
    refine ⟨min δ (1 / 2), lt_min hδ (by norm_num), fun σ t hσ ↦ ?_⟩
    by_contra hne
    have hpos : 0 < (meromorphicOrderAt f (shift(σ, t))).untop₀.toNat := Nat.pos_of_ne_zero hne
    have hstrip : σ ∈ Ioo (1 / 2 : ℝ) 1 := ⟨by linarith [hσ.1, min_le_right δ (1 / 2)], hσ.2⟩
    have hm : 1 < mult(ψ, shift(σ, t)) := hforce σ t hstrip hpos
    have hle := hfree σ t (Or.inl ⟨by linarith [hσ.1, min_le_left δ (1 / 2)], hσ.2⟩)
    omega

/-- Paper: Proposition 10.2.2.2, pp. 446–447. For the splitting field of `X³ - 2` and its trivial
character, the multiple zeros in the open critical strip do not have bounded height. Thus the
bounded-height hypothesis of #7453 cannot be strengthened from one bounded-height representative
per vertical line to a height bound for all multiple zeros.
Deviation: The paper does not state this. Proved from
`cubicSplittingField_completedDedekindZeta_multipleZeros_unbounded`. -/
theorem spectralStripJet_multiple_zeros_unbounded_height_cubic :
    let L := (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).SplittingField
    letI : NumberField L := ⟨⟩
    ¬ ∃ T : ℝ, ∀ σ t : ℝ, σ ∈ Ioo (0 : ℝ) 1 →
      1 < (meromorphicOrderAt
        (continuedCompletedHeckeL (1 : PontryaginDual (IdeleClassGroup (𝓞 L) L)))
        (shift(σ, t))).untop₀.toNat → |t| ≤ T := by
  intro L
  let : NumberField L := ⟨⟩
  rintro ⟨T, hT⟩
  obtain ⟨z, hzT, h0, h1, hm⟩ := cubicSplittingField_completedDedekindZeta_multipleZeros_unbounded T
  have hz_eq : shift(z.re, z.im) = z := Complex.re_add_im z
  have hle : |z.im| ≤ T := hT z.re z.im ⟨h0, h1⟩ (by simpa only [hz_eq] using hm)
  linarith [le_abs_self z.im]

end BoundedHeightAndOrderOne

end RiemannMasullo.Isolated
