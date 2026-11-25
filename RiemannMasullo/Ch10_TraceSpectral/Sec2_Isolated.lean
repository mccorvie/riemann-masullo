module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch06_LocalGlobal.Sec3

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

end RiemannMasullo.Isolated
