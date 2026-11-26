module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_Clusters
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_HeckeMultipliers
import RiemannMasullo.Ch10_TraceSpectral.Sec3_BasepointChoice
import RiemannMasullo.Ch10_TraceSpectral.Sec3_MellinDecay
import RiemannMasullo.Ch10_TraceSpectral.Sec2_Basepoint
import RiemannMasullo.Ch10_TraceSpectral.Sec3_ArchimedeanFlows
import RiemannMasullo.ForMathlib.Analysis.Complex.GoodHeightFamily
import RiemannMasullo.ForMathlib.Topology.Algebra.InfiniteSum.PolynomialCount

/-! # Trace class of the spectral convolution, for every number field and every test

Theorems 10.3.1.1(2) and 10.3.2.1(2), pp. 448 and 454, say that convolution by a test on the
line and strip spectral quotients is trace class. `Sec3` proves them from the recorded gap
`spectralStripConvolution_traceCauchy_compact_block_series` (#7241). This file proves the same
two statements without it: `spectralStripConvolution_nuclear_of_summable_clusterTraceNorms` and
`spectralLineConvolution_nuclear_of_summable_clusterTraceNorms`. The zeros are summed in clusters
between well-chosen heights and not one at a time, so no distance between two zeros enters.

`Sec3_Clusters` proves that the convolution on the strip spectral quotient is trace class from
data on rectangle boundaries for the angular components that see the test
(`spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData`). This file produces
that data, with every constant uniform in the component, and sums over the components
(`spectralStripConvolution_exists_clusterBoundaryData`,
`spectralStripConvolution_summable_clusterTraceNorms`).

The pieces, each from another file:
* the entire multipliers `ϑ ω`, bounded by one on a wide strip and bounded below on the two
  vertical sides (`Sec3_HeckeMultipliers`);
* heights `T ω k ∈ [2k, 2k + 1]` with a lower bound on the horizontal sides
  (`exists_goodHeight_windows_of_norm_le_one` of `ForMathlib/Analysis/Complex/GoodHeightFamily`);
* the number of zeros between two heights, by Jensen's inequality (`Sec3_HeckeMultipliers`);
* the decay of the Mellin transform of the test along one-parameter subgroups, uniform in the
  character (`Sec3_MellinDecay`);
* a basepoint choice that is trivial on the image of a norm section (`Sec2_Basepoint`), and the
  link between the archimedean parameters of such a character and its frequencies along
  one-parameter subgroups (`Sec3_ArchimedeanFlows`);
* the polynomial count of the characters by their frequencies
  (`idelicExplicitFormula_normOneFourier_count` of `AppB_AnalyticNT/Sec4b`) and the summation
  lemma `summable_prod_int_of_encard_le_of_norm_le`;
* the transport of the clustered statement from one basepoint choice to every other
  (`Sec3_BasepointChoice`). -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F

section BoundaryData

/-- A weaker lower bound: a smaller constant and a larger exponent over a base at least one. -/
private theorem uniform_div_pow_le_div_pow {c c' b : ℝ} {n n' : ℕ} (hc : 0 ≤ c) (hcc : c ≤ c')
    (hb : 1 ≤ b) (hn : n' ≤ n) : c / b ^ n ≤ c' / b ^ n' := by
  have hb0 : 0 < b := by linarith
  exact div_le_div₀ (hc.trans hcc) hcc (pow_pos hb0 n') (pow_le_pow_right₀ hb hn)

open Classical in
/-- Paper: Theorem 10.3.2.1(1), pp. 453–455. The boundary data of the cluster theorem for one
character, with every constant uniform in the character.
For a centre `a` and a half-width `α` there are `β`, `X` with `α < β < X`, and for every bound
`A₀` for the logarithm of the discriminant–conductor product a constant `c > 0` and an exponent
`n`, such that for every unitary character `ψ` of the idele classes that is the trivial
character, or is not trivial on the norm-one classes and has
`heckeLogDiscriminantConductor ψ ≤ A₀`, and for every bound `Y ≥ 1` for its archimedean
parameters, there are an entire function `ϑ` and heights `T k ∈ [2k, 2k + 1]` with:
`ϑ` vanishes at `u` to at least the order of the zero of the completed L-function of `ψ` at
`a + u`; `‖ϑ u‖ ≤ 1` for `|Re u| ≤ X + 2`; and `c / (Y + |k| + 1) ^ n ≤ ‖ϑ w‖` on the boundary of
the rectangle `[-X, X] × [T k, T (k + 1)]`, for every integer `k`.
The lower bound is for the multiplier `ϑ`, which is built from `Λ(s, ψ) Λ(s, ψ⁻¹)` over shifted
gamma factors (`Sec3_HeckeMultipliers`), not for the L-function itself.
Reconstruction: The paper does not state this. It is the classical lower bound at well-chosen
heights (`ForMathlib/Analysis/Complex/GoodHeightFamily`), applied to `ϑ`, with the dependence
on the character made explicit, in the form of the hypotheses `hgrowth`, `hord`, `hT`, `hlow`
of `spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData_on`. -/
theorem exists_uniform_heckeMultiplier_rectBoundary (F : Type*) [Field F] [NumberField F]
    (a α : ℝ) :
    ∃ β X : ℝ, α < β ∧ β < X ∧ ∀ A₀ : ℝ, ∃ (c : ℝ) (n : ℕ), 0 < c ∧
      ∀ ψ : PontryaginDual (IdeleClassGroup (𝓞 F) F),
        (ψ = 1 ∨ (ψ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 ∧
          heckeLogDiscriminantConductor ψ ≤ A₀)) →
        ∀ Y : ℝ, 1 ≤ Y →
          (∀ w : InfinitePlace F, if hw : w.IsReal then
              ‖(realHeckeCharacter_parameters ψ w hw).exists.choose.1‖ ≤ Y
            else
              let p := (complexHeckeCharacter_parameters ψ w
                (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
              ‖p.1‖ ≤ Y ∧ (p.2.natAbs : ℝ) ≤ Y) →
          ∃ (ϑ : ℂ → ℂ) (T : ℤ → ℝ), Differentiable ℂ ϑ ∧
            (∀ u : ℂ, (((meromorphicOrderAt (continuedCompletedHeckeL ψ)
              ((a : ℂ) + u)).untop₀.toNat : ℕ) : ℕ∞) ≤ analyticOrderAt ϑ u) ∧
            (∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ u‖ ≤ 1) ∧
            (∀ k : ℤ, T k ∈ Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 1)) ∧
            ∀ k : ℤ, ∀ w ∈ rectBoundary (-X) X (T k) (T (k + 1)),
              c / (Y + |(k : ℝ)| + 1) ^ n ≤ ‖ϑ w‖ := by
  let k₀ : ℕ := ⌈2 * |a| + |α| + 1⌉₊
  have hk₀ : 2 * |a| + |α| + 1 ≤ k₀ := Nat.le_ceil _
  let X : ℝ := a + k₀ + 1 / 2
  have hαX : α < X := by
    dsimp only [X]
    linarith [le_abs_self α, neg_abs_le a, abs_nonneg a]
  have hX1 : 1 ≤ X := by
    dsimp only [X]
    linarith [neg_abs_le a, abs_nonneg a, abs_nonneg α]
  have hline : (3 / 2 : ℝ) ≤ 2 * a + k₀ + 1 / 2 := by
    linarith [neg_abs_le a, abs_nonneg α]
  let W : ℝ := 7 * X + 6
  refine ⟨(α + X) / 2, X, by linarith, by linarith, fun A₀ ↦ ?_⟩
  obtain ⟨c₂, n₂, hc₂, hmult⟩ := exists_uniform_heckeMultiplier_strip_of_line F a k₀ hline W A₀
  obtain ⟨c₁, n₁, ϑ₁, hc₁, hd₁, hord₁, hup₁, hr₁, hl₁⟩ :=
    exists_trivial_heckeMultiplier_strip_of_line F a k₀ hline W
  let cs : ℝ := min c₁ c₂
  have hcs : 0 < cs := lt_min hc₁ hc₂
  let ns : ℕ := n₁ + n₂
  obtain ⟨c', n', hc', hgood⟩ := exists_goodHeight_windows_of_norm_le_one (x₀ := X)
    (ρ := X + 1) (c := cs) (n := ns) (by linarith) hcs
  let c : ℝ := min (cs / (X + 6) ^ ns) (c' / 7 ^ n')
  have hc : 0 < c := lt_min (by positivity) (by positivity)
  refine ⟨c, ns + n', hc, fun ψ hψ Y hY harch ↦ ?_⟩
  -- One multiplier with the common constants `cs`, `ns`.
  have hex : ∃ ϑ : ℂ → ℂ, Differentiable ℂ ϑ ∧
      (∀ u : ℂ, (((meromorphicOrderAt (continuedCompletedHeckeL ψ)
        ((a : ℂ) + u)).untop₀.toNat : ℕ) : ℕ∞) ≤ analyticOrderAt ϑ u) ∧
      (∀ u : ℂ, |u.re| ≤ W → ‖ϑ u‖ ≤ 1) ∧
      (∀ u : ℂ, X ≤ u.re → cs / (‖u‖ + Y) ^ ns ≤ ‖ϑ u‖) ∧
      (∀ u : ℂ, u.re = -X → cs / (‖u‖ + Y) ^ ns ≤ ‖ϑ u‖) := by
    rcases hψ with rfl | ⟨hne, hcond⟩
    · refine ⟨ϑ₁, hd₁, hord₁, hup₁, fun u hu ↦ ?_, fun u hu ↦ ?_⟩
      · refine le_trans ?_ (hr₁ u hu)
        refine (uniform_div_pow_le_div_pow hcs.le (min_le_left _ _)
          (by linarith [norm_nonneg u]) (Nat.le_add_right n₁ n₂)).trans ?_
        exact div_le_div_of_nonneg_left hc₁.le (by positivity)
          (pow_le_pow_left₀ (by positivity) (by linarith) n₁)
      · refine le_trans ?_ (hl₁ u hu)
        refine (uniform_div_pow_le_div_pow hcs.le (min_le_left _ _)
          (by linarith [norm_nonneg u]) (Nat.le_add_right n₁ n₂)).trans ?_
        exact div_le_div_of_nonneg_left hc₁.le (by positivity)
          (pow_le_pow_left₀ (by positivity) (by linarith) n₁)
    · obtain ⟨ϑ, hd, hord, hup, hlow⟩ := hmult ψ hne hcond
      refine ⟨ϑ, hd, hord, hup, fun u hu ↦ ?_, fun u hu ↦ ?_⟩
      · exact (uniform_div_pow_le_div_pow hcs.le (min_le_right _ _)
          (by linarith [norm_nonneg u]) (Nat.le_add_left n₂ n₁)).trans
          ((hlow Y hY harch).1 u hu)
      · exact (uniform_div_pow_le_div_pow hcs.le (min_le_right _ _)
          (by linarith [norm_nonneg u]) (Nat.le_add_left n₂ n₁)).trans
          ((hlow Y hY harch).2 u hu)
  obtain ⟨ϑ, hd, hord, hup, hright, hleft⟩ := hex
  -- Heights with a lower bound on the horizontal segments.
  obtain ⟨T, hT, hTlow⟩ := hgood ϑ Y hd hY
    (fun s h1 h2 ↦ hup s (abs_le.mpr ⟨by dsimp only [W]; linarith, by dsimp only [W]; linarith⟩))
    (fun s hs ↦ hright s hs.ge)
  have hTabs (j : ℤ) : |T j| ≤ 2 * |(j : ℝ)| + 1 := by
    have h1 := (hT j).1
    have h2 := (hT j).2
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (j : ℝ)]
    · linarith [le_abs_self (j : ℝ)]
  have hk1 (k : ℤ) : |((k + 1 : ℤ) : ℝ)| ≤ |(k : ℝ)| + 1 := by
    push_cast
    exact (abs_add_le _ _).trans (by rw [abs_one])
  refine ⟨ϑ, T, hd, hord, fun u hu ↦ hup u (by dsimp only [W]; linarith), hT, fun k w hw ↦ ?_⟩
  have hL1 : 1 ≤ Y + |(k : ℝ)| + 1 := by linarith [abs_nonneg (k : ℝ)]
  have hL0 : 0 < Y + |(k : ℝ)| + 1 := by linarith
  -- The two kinds of sides.
  have hhor (j : ℤ) (hj : |(j : ℝ)| ≤ |(k : ℝ)| + 1) (hre : w.re ∈ Icc (-X) X)
      (him : w.im = T j) : c / (Y + |(k : ℝ)| + 1) ^ (ns + n') ≤ ‖ϑ w‖ := by
    have hw' : w = ⟨w.re, T j⟩ := Complex.ext rfl him
    have h1 := hTlow j w.re ⟨by linarith [hre.1], by linarith [hre.2]⟩
    rw [← hw'] at h1
    refine le_trans ?_ h1
    have hbase : Y + |T j| + 2 ≤ 7 * (Y + |(k : ℝ)| + 1) := by
      linarith [hTabs j, abs_nonneg (k : ℝ)]
    have hpos : 0 < Y + |T j| + 2 := by linarith [abs_nonneg (T j)]
    calc c / (Y + |(k : ℝ)| + 1) ^ (ns + n')
        ≤ (c' / 7 ^ n') / (Y + |(k : ℝ)| + 1) ^ n' :=
          uniform_div_pow_le_div_pow hc.le (min_le_right _ _) hL1 (Nat.le_add_left n' ns)
      _ = c' / (7 * (Y + |(k : ℝ)| + 1)) ^ n' := by rw [div_div, ← mul_pow]
      _ ≤ c' / (Y + |T j| + 2) ^ n' :=
          div_le_div_of_nonneg_left hc'.le (pow_pos hpos n') (pow_le_pow_left₀ hpos.le hbase n')
  have hver (him : w.im ∈ Icc (T k) (T (k + 1)))
      (hlow : cs / (‖w‖ + Y) ^ ns ≤ ‖ϑ w‖) (hre : |w.re| = X) :
      c / (Y + |(k : ℝ)| + 1) ^ (ns + n') ≤ ‖ϑ w‖ := by
    refine le_trans ?_ hlow
    have h1 := hTabs k
    have h2 : |T (k + 1)| ≤ 2 * |(k : ℝ)| + 3 := (hTabs (k + 1)).trans (by linarith [hk1 k])
    have him' : |w.im| ≤ 2 * |(k : ℝ)| + 3 := by
      rw [abs_le]
      constructor
      · linarith [him.1, (abs_le.mp h1).1]
      · linarith [him.2, (abs_le.mp h2).2]
    have hnorm : ‖w‖ ≤ X + (2 * |(k : ℝ)| + 3) := by
      have := Complex.norm_le_abs_re_add_abs_im w
      rw [hre] at this
      linarith
    have hbase : ‖w‖ + Y ≤ (X + 6) * (Y + |(k : ℝ)| + 1) := by
      nlinarith [abs_nonneg (k : ℝ), norm_nonneg w]
    have hpos : 0 < ‖w‖ + Y := by linarith [norm_nonneg w]
    calc c / (Y + |(k : ℝ)| + 1) ^ (ns + n')
        ≤ (cs / (X + 6) ^ ns) / (Y + |(k : ℝ)| + 1) ^ ns :=
          uniform_div_pow_le_div_pow hc.le (min_le_left _ _) hL1 (Nat.le_add_right ns n')
      _ = cs / ((X + 6) * (Y + |(k : ℝ)| + 1)) ^ ns := by rw [div_div, ← mul_pow]
      _ ≤ cs / (‖w‖ + Y) ^ ns :=
          div_le_div_of_nonneg_left hcs.le (pow_pos hpos ns) (pow_le_pow_left₀ hpos.le hbase ns)
  have hX0 : 0 < X := by linarith
  rcases mem_rectBoundary_iff.mp hw with ⟨hre, him | him⟩ | ⟨him, hre | hre⟩
  · exact hhor k (by linarith) hre him
  · exact hhor (k + 1) (hk1 k) hre him
  · exact hver him (hleft w hre) (by rw [hre, abs_neg, abs_of_pos hX0])
  · exact hver him (hright w hre.ge) (by rw [hre, abs_of_pos hX0])

end BoundaryData

section Level

/-- If each of finitely many nonnegative quantities, raised to the power `N`, times `g` is
bounded, and `g` is bounded, then one plus their sum, raised to the power `N`, times `g` is
bounded. -/
private theorem uniform_one_add_sum_pow_mul_le {ι : Type*} [Fintype ι] (x : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (N : ℕ) {g K₀ : ℝ} (K : ι → ℝ) (hg : 0 ≤ g) (h0 : g ≤ K₀)
    (hK : ∀ i, x i ^ N * g ≤ K i) :
    (1 + ∑ i, x i) ^ N * g ≤ ((Fintype.card ι : ℝ) + 1) ^ N * (K₀ + ∑ i, K i) := by
  have hK0 (i : ι) : 0 ≤ K i := (mul_nonneg (pow_nonneg (hx i) N) hg).trans (hK i)
  have hK₀ : 0 ≤ K₀ := hg.trans h0
  have hsumK : 0 ≤ ∑ i, K i := Finset.sum_nonneg fun i _ ↦ hK0 i
  have hcard : (1 : ℝ) ≤ (Fintype.card ι : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card ι)]
  rcases isEmpty_or_nonempty ι with hι | hι
  · have hs : ∑ i, x i = 0 := Finset.sum_eq_zero fun i _ ↦ (hι.false i).elim
    rw [hs, add_zero, one_pow, one_mul]
    calc g ≤ K₀ := h0
      _ ≤ 1 * (K₀ + ∑ i, K i) := by linarith
      _ ≤ _ := mul_le_mul_of_nonneg_right (one_le_pow₀ hcard) (by linarith)
  · obtain ⟨i₀, hi₀⟩ := Finite.exists_max x
    have hsum : ∑ i, x i ≤ Fintype.card ι * x i₀ := by
      calc ∑ i, x i ≤ ∑ _i : ι, x i₀ := Finset.sum_le_sum fun i _ ↦ hi₀ i
        _ = Fintype.card ι * x i₀ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rcases le_or_gt (x i₀) 1 with h1 | h1
    · have hbase : 1 + ∑ i, x i ≤ (Fintype.card ι : ℝ) + 1 := by
        have : (Fintype.card ι : ℝ) * x i₀ ≤ Fintype.card ι :=
          mul_le_of_le_one_right (Nat.cast_nonneg _) h1
        linarith
      have hnn : 0 ≤ 1 + ∑ i, x i :=
        add_nonneg zero_le_one (Finset.sum_nonneg fun i _ ↦ hx i)
      calc (1 + ∑ i, x i) ^ N * g ≤ ((Fintype.card ι : ℝ) + 1) ^ N * g :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hbase N) hg
        _ ≤ ((Fintype.card ι : ℝ) + 1) ^ N * (K₀ + ∑ i, K i) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · have hbase : 1 + ∑ i, x i ≤ ((Fintype.card ι : ℝ) + 1) * x i₀ := by linarith
      have hnn : 0 ≤ 1 + ∑ i, x i :=
        add_nonneg zero_le_one (Finset.sum_nonneg fun i _ ↦ hx i)
      have hKi : K i₀ ≤ K₀ + ∑ i, K i := by
        have := Finset.single_le_sum (f := K) (fun i _ ↦ hK0 i) (Finset.mem_univ i₀)
        linarith
      calc (1 + ∑ i, x i) ^ N * g ≤ (((Fintype.card ι : ℝ) + 1) * x i₀) ^ N * g :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hnn hbase N) hg
        _ = ((Fintype.card ι : ℝ) + 1) ^ N * (x i₀ ^ N * g) := by rw [mul_pow, mul_assoc]
        _ ≤ ((Fintype.card ι : ℝ) + 1) ^ N * (K₀ + ∑ i, K i) :=
            mul_le_mul_of_nonneg_left ((hK i₀).trans hKi) (by positivity)

/-- A unitary character with a nonzero Mellin coefficient of a test is trivial on every period
subgroup of the test that lies in the norm-one classes. This is the argument of the private
`idelicExplicitFormula_summable_spectral_characters_annihilator` of `AppB_AnalyticNT/Sec4b`,
proved again here because that lemma is private. -/
theorem bruhatCompactSupport_mellin_eq_one_on_period_of_ne_zero (φ : BruhatCompactSupport C𝔽) (kg : Subgroup C𝔽)
    (hkg : IsBruhatGoodSubgroup kg) (hinv : ∀ h : kg, ∀ x, φ.val (h.val * x) = φ.val x)
    (ψ : PontryaginDual C𝔽) (w : ℂ)
    (hw : (∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽) ≠ 0) (h : C𝔽)
    (hh : h ∈ kg) : ψ h = 1 := by
  let m : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  have hn : ideleClassNorm F h = 1 :=
    MonoidHom.mem_ker.mp (compactSubgroup_le_modulation_ker m kg hkg.isCompact hh)
  let f (g : C𝔽) := φ.val g * ideleClassNormTwist (F := F) ψ w g
  have htw : ideleClassNormTwist (F := F) ψ w h = (ψ h : ℂ) := by
    change ((ψ h : Circle) : ℂ) * (((ideleClassNorm F h).val : ℝ) : ℂ) ^ w = _
    rw [hn]
    simp
  have hm (g : C𝔽) : f (h * g) = (ψ h : ℂ) * f g := by
    dsimp only [f]
    rw [hinv ⟨h, hh⟩ g, map_mul, htw]
    ring
  have he := integral_mul_left_eq_self (μ := μ𝔽) f h
  simp_rw [hm, integral_const_mul] at he
  exact Circle.ext ((mul_eq_right₀ hw).mp he)

/-- The logarithm of the discriminant–conductor product (the quantity `log A_χ` of
(B.4.2.3), p. 614) is bounded on the unitary characters that have a nonzero Mellin coefficient
of a fixed test: these characters have a common finite conductor level
(`bruhatCompactSupport_mellin_conductor_level`). The paper does not state this bound.
The passage from the common level to the bound is the computation in the proof of
`bruhatCompactSupport_bounded_angular_logConductor` of `AppB_AnalyticNT/Sec4b`. That theorem is
not used here because its hypothesis is another one: a nonzero angular profile, the integral of
the test times the character over a coset of the norm-one classes. A nonzero Mellin
coefficient gives a nonzero angular profile only through the disintegration of the class
measure over the norm-one classes, which is longer than the computation. -/
theorem bruhatCompactSupport_mellin_logConductor_le (φ : BruhatCompactSupport C𝔽) :
    ∃ A₀ : ℝ, ∀ (ψ : PontryaginDual C𝔽) (w : ℂ),
      (∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽) ≠ 0 →
      heckeLogDiscriminantConductor ψ ≤ A₀ := by
  obtain ⟨N, hN, hlevel⟩ := bruhatCompactSupport_mellin_conductor_level φ μ𝔽
  refine ⟨Real.log (Int.natAbs (NumberField.discr F)) +
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 F),
      Real.log (v.asIdeal.absNorm : ℝ) * (N v : ℝ), fun ψ w hw ↦ ?_⟩
  have hlog (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) :
      0 ≤ Real.log (v.asIdeal.absNorm : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (NumberField.HeightOneSpectrum.one_lt_absNorm v).le)
  have support_weight (b : IsDedekindDomain.HeightOneSpectrum (𝓞 F) → ℕ) (h : ∀ v, b v ≤ N v) :
      (Function.support (fun v ↦ Real.log (v.asIdeal.absNorm : ℝ) * (b v : ℝ))).Finite := by
    apply hN.subset
    intro v hv hn
    have hb : b v = 0 := Nat.eq_zero_of_le_zero ((h v).trans_eq hn)
    exact hv (by simp [hb])
  unfold heckeLogDiscriminantConductor
  apply add_le_add_right
  refine finsum_le_finsum (support_weight _ fun v ↦ Nat.sInf_le (hlevel ψ w hw v))
    (support_weight N fun _ ↦ le_rfl) fun v ↦ ?_
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.sInf_le (hlevel ψ w hw v)) (hlog v)

open Classical in
/-- Paper: Lemma B.4.4.8, p. 624, and Lemma B.4.4.9, pp. 624–625. A size function for the
unitary characters of the idele classes that are trivial on the image of a norm section `τ`,
adapted to a test `φ`: a function `κ ≥ 0` such that
* `1 + κ ψ` bounds the archimedean parameters of `ψ`;
* the characters that have a nonzero Mellin coefficient of `φ` and `κ ψ ≤ T` number at most a
  polynomial in `T`;
* on every vertical strip and for every `N`, the Mellin transform of `φ` at `ψ |·| ^ w` times
  `(1 + ‖w‖ + κ ψ) ^ N` is bounded, uniformly in `ψ` and `w`.
`κ ψ` is the sum of the frequencies of `ψ` along the flows of
`idelicExplicitFormula_normOneFourier_count` (for a period subgroup of the test) and along the
archimedean flows of `exists_flows_archimedean_parameters_le`.
So `κ` depends on the test, through its period subgroup, and has no part for the finite
conductor; of the archimedean parameters only the bound by `1 + κ ψ` is proved.
Reconstruction: The paper does not state this. In the sum over the characters `κ` plays the
role that the analytic conductor plays in analytic number theory, in the form in which the
library can count the characters. -/
theorem exists_spectralLevel (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) :
    ∃ κ : PontryaginDual C𝔽 → ℝ, (∀ ψ, 0 ≤ κ ψ) ∧
      (∀ ψ : PontryaginDual C𝔽, (∀ t : ℝ≥0ˣ, ψ (τ t) = 1) →
        ∀ w : InfinitePlace F, if hw : w.IsReal then
            ‖(realHeckeCharacter_parameters ψ w hw).exists.choose.1‖ ≤ 1 + κ ψ
          else
            let p := (complexHeckeCharacter_parameters ψ w
              (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
            ‖p.1‖ ≤ 1 + κ ψ ∧ (p.2.natAbs : ℝ) ≤ 1 + κ ψ) ∧
      (∃ C d : ℕ, ∀ T : ℕ, {ψ : PontryaginDual C𝔽 | (∀ t : ℝ≥0ˣ, ψ (τ t) = 1) ∧
          (∃ w : ℂ, (∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽) ≠ 0) ∧
          κ ψ ≤ (T : ℝ)}.encard ≤ ((C * (T + 1) ^ d : ℕ) : ℕ∞)) ∧
      ∀ (W : ℝ) (N : ℕ), ∃ K : ℝ, ∀ ψ : PontryaginDual C𝔽, (∀ t : ℝ≥0ˣ, ψ (τ t) = 1) →
        ∀ w : ℂ, |w.re| ≤ W →
          (1 + ‖w‖ + κ ψ) ^ N *
            ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) ψ w g ∂μ𝔽‖ ≤ K := by
  obtain ⟨kg, hkg, hinv, -⟩ := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1 0
  obtain ⟨r, b, hb, C, d, hcount⟩ := idelicExplicitFormula_normOneFourier_count τ hτ kg hkg
  obtain ⟨m, Yf, hYf, hlink⟩ := exists_flows_archimedean_parameters_le τ hτ
  let fb (j : Fin r) (ψ : PontryaginDual C𝔽) : ℝ :=
    ‖bruhatDirectionalDeriv (b j) (fun x : C𝔽 ↦ (ψ x : ℂ)) 1‖
  let fY (i : Fin m) (ψ : PontryaginDual C𝔽) : ℝ :=
    ‖bruhatDirectionalDeriv (Yf i) (fun x : C𝔽 ↦ (ψ x : ℂ)) 1‖
  let κ (ψ : PontryaginDual C𝔽) : ℝ := ∑ j, fb j ψ + ∑ i, fY i ψ
  have hfb0 (ψ : PontryaginDual C𝔽) : 0 ≤ ∑ j, fb j ψ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hfY0 (ψ : PontryaginDual C𝔽) : 0 ≤ ∑ i, fY i ψ :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hfb (ψ : PontryaginDual C𝔽) (j : Fin r) : fb j ψ ≤ κ ψ := by
    have := Finset.single_le_sum (f := fun j ↦ fb j ψ) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ j)
    linarith [hfY0 ψ]
  have hfY (ψ : PontryaginDual C𝔽) (i : Fin m) : fY i ψ ≤ κ ψ := by
    have := Finset.single_le_sum (f := fun i ↦ fY i ψ) (fun _ _ ↦ norm_nonneg _)
      (Finset.mem_univ i)
    linarith [hfb0 ψ]
  refine ⟨κ, fun ψ ↦ add_nonneg (hfb0 ψ) (hfY0 ψ), fun ψ hψ ↦ hlink ψ hψ (1 + κ ψ)
    (fun i ↦ by linarith [hfY ψ i]), ⟨C, d, fun T ↦ ?_⟩, fun W N ↦ ?_⟩
  · -- The count, through the characters trivial on the section as a subtype.
    refine le_trans ?_ (hcount T)
    refine le_trans (Set.encard_mono ?_) (Subtype.val_injective.injOn.encard_image).le
    rintro ψ ⟨hψ, ⟨w, hw⟩, hκ⟩
    exact ⟨⟨ψ, hψ⟩, ⟨fun u hu ↦ bruhatCompactSupport_mellin_eq_one_on_period_of_ne_zero φ kg hkg hinv ψ w hw u hu,
      fun j ↦ (hfb ψ j).trans hκ⟩, rfl⟩
  · -- The decay, along the section and along each of the flows.
    obtain ⟨K0, hK0⟩ := bruhatCompactSupport_mellin_frequency_pow_le φ
      (τ.comp (positiveRealLogEquiv.symm : _ →ₜ* _)) W 0
    obtain ⟨Krad, hKrad⟩ := bruhatCompactSupport_mellin_frequency_pow_le φ
      (τ.comp (positiveRealLogEquiv.symm : _ →ₜ* _)) W N
    choose Kb hKb using fun j ↦ bruhatCompactSupport_mellin_frequency_pow_le φ (b j) W N
    choose KY hKY using fun i ↦ bruhatCompactSupport_mellin_frequency_pow_le φ (Yf i) W N
    let Kall : Option (Fin r ⊕ Fin m) → ℝ := fun o ↦ o.elim Krad (Sum.elim Kb KY)
    refine ⟨((Fintype.card (Option (Fin r ⊕ Fin m)) : ℝ) + 1) ^ N * (K0 + ∑ o, Kall o),
      fun ψ hψ w hw ↦ ?_⟩
    let x : Option (Fin r ⊕ Fin m) → ℝ := fun o ↦
      o.elim ‖w‖ (Sum.elim (fun j ↦ fb j ψ) (fun i ↦ fY i ψ))
    have hsum : 1 + ‖w‖ + κ ψ = 1 + ∑ o, x o := by
      simp only [x, Fintype.sum_option, Fintype.sum_sum_type, Option.elim_none, Option.elim_some,
        Sum.elim_inl, Sum.elim_inr, κ]
      ring
    rw [hsum]
    refine uniform_one_add_sum_pow_mul_le x (fun o ↦ ?_) N Kall (norm_nonneg _) ?_ fun o ↦ ?_
    · rcases o with _ | (j | i)
      · exact norm_nonneg _
      · exact norm_nonneg _
      · exact norm_nonneg _
    · simpa only [pow_zero, one_mul] using hK0 ψ w hw
    · rcases o with _ | (j | i)
      · have h := hKrad ψ w hw
        rwa [bruhatDirectionalDeriv_ideleClassNormTwist_normSection τ hτ ψ hψ w] at h
      · have h := hKb j ψ w hw
        rwa [bruhatDirectionalDeriv_ideleClassNormTwist_of_mem_ker (b j) (hb j) ψ w] at h
      · have h := hKY i ψ w hw
        rwa [bruhatDirectionalDeriv_ideleClassNormTwist_of_mem_ker (Yf i) (hYf i) ψ w] at h

end Level

section Assembly

local notation "Q(" a ", " hI ", " hs ")" => spectralSobolevQuotient F a hI hs
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "mult(" χ ", " z ")" => (order(χ, z)).untop₀.toNat

variable (a : ℝ)

local notation "Z(" χ ", " α ")" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" χ ", " α ", " s ", " z ")" => spectralStripMultiplicity α s (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

/-- The jets of the zeros of one angular component with heights in a window of length three are
at most the zeros of its completed L-function in a disc around `2 + i (τ₀ + 3/2)`, counted with
multiplicity. -/
private theorem uniform_jetCount_le_of_closedBall
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {α s : ℝ} (ω : PontryaginDual C₁) {τ₀ C : ℝ}
    (hC : ∀ S : Finset ℂ,
      (∀ z ∈ S, z ∈ Metric.closedBall (⟨2, τ₀ + 3 / 2⟩ : ℂ) (|a - 2| + α + 2)) →
      ∑ z ∈ S, ((mult(χ ω, z) : ℕ) : ℝ) ≤ C)
    (K : Finset Z(χ, α)) (hK : ∀ z ∈ K, z.val.1 = ω ∧ τ₀ ≤ z.val.2.2 ∧ z.val.2.2 ≤ τ₀ + 3) :
    ((∑ z ∈ K, N(χ, α, s, z) : ℕ) : ℝ) ≤ C := by
  classical
  let pt (z : Z(χ, α)) : ℂ := shift(a + z.val.2.1, z.val.2.2)
  have hre (z : Z(χ, α)) : (pt z).re = a + z.val.2.1 := by simp [pt]
  have him (z : Z(χ, α)) : (pt z).im = z.val.2.2 := by simp [pt]
  have hinj : Set.InjOn pt K := by
    intro z hz z' hz' h
    have h1 : a + z.val.2.1 = a + z'.val.2.1 := by rw [← hre z, ← hre z', h]
    have h2 : z.val.2.2 = z'.val.2.2 := by rw [← him z, ← him z', h]
    exact Subtype.ext (Prod.ext ((hK z hz).1.trans (hK z' hz').1.symm)
      (Prod.ext (add_left_cancel h1) h2))
  have hle (z : Z(χ, α)) (hz : z ∈ K) :
      ((N(χ, α, s, z) : ℕ) : ℝ) ≤ ((mult(χ ω, pt z) : ℕ) : ℝ) := by
    have h1 : N(χ, α, s, z) ≤ mult(χ z.val.1, shift(a + z.val.2.1, z.val.2.2)) := by
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity
      split_ifs
      · exact le_rfl
      · exact min_le_left _ _
      · exact Nat.zero_le _
    have h2 : mult(χ z.val.1, shift(a + z.val.2.1, z.val.2.2)) = mult(χ ω, pt z) := by
      rw [(hK z hz).1]
    exact Nat.cast_le.mpr (h1.trans h2.le)
  have hball (z : Z(χ, α)) (hz : z ∈ K) :
      pt z ∈ Metric.closedBall (⟨2, τ₀ + 3 / 2⟩ : ℂ) (|a - 2| + α + 2) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have hb := z.property.1
    obtain ⟨-, h1, h2⟩ := hK z hz
    have hr : |(pt z - (⟨2, τ₀ + 3 / 2⟩ : ℂ)).re| ≤ |a - 2| + α := by
      rw [Complex.sub_re, hre z]
      have : a + z.val.2.1 - 2 = (a - 2) + z.val.2.1 := by ring
      change |a + z.val.2.1 - 2| ≤ _
      rw [this]
      refine (abs_add_le _ _).trans ?_
      have : |z.val.2.1| ≤ α := abs_le.mpr ⟨hb.1, hb.2⟩
      linarith
    have hi : |(pt z - (⟨2, τ₀ + 3 / 2⟩ : ℂ)).im| ≤ 3 / 2 := by
      rw [Complex.sub_im, him z]
      change |z.val.2.2 - (τ₀ + 3 / 2)| ≤ 3 / 2
      rw [abs_le]
      constructor <;> linarith
    linarith
  calc ((∑ z ∈ K, N(χ, α, s, z) : ℕ) : ℝ) = ∑ z ∈ K, ((N(χ, α, s, z) : ℕ) : ℝ) := by
        push_cast
        rfl
    _ ≤ ∑ z ∈ K, ((mult(χ ω, pt z) : ℕ) : ℝ) := Finset.sum_le_sum hle
    _ = ∑ w ∈ K.image pt, ((mult(χ ω, w) : ℕ) : ℝ) :=
        (Finset.sum_image (f := fun w ↦ ((mult(χ ω, w) : ℕ) : ℝ)) hinj).symm
    _ ≤ C := hC _ fun w hw ↦ by
        obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
        exact hball z hz

/-- Paper: Theorems 10.3.1.1(1)–(2) and 10.3.2.1(1)–(2), pp. 448–455. The analytic input of the
clustered statement `spectralStripConvolution_summable_clusterTraceNorms`, with no operator, no
quotient space and no biorthogonal vector in it, for every number field and every test. There
are a choice `χ` of the unitary extensions of the norm-one characters, a half-width `X` and,
for each angular component `ω`, an entire function `ϑ ω` of polynomial growth on a vertical
strip that vanishes at every zero of the component to at least the surviving multiplicity, and
heights `T ω k ∈ [2k, 2k + 1]`, such that: with lower bounds `ℓ ω k > 0` for `ϑ ω` and upper
bounds `φb ω k` for the Mellin transform of the test on the boundary of the rectangle
`[-X, X] × [T ω k, T ω (k + 1)]`, the numbers of jets between consecutive heights, times
`φb / ℓ`, times a power of the height, form a summable family over the components and heights.
The extensions are chosen, not given: the heights and the growth of `ϑ ω` are measured from
height `0` in the chart of `χ ω`. For extensions `χ ω · |·|^{iτ_ω}` with `τ_ω` growing fast the
summability is not to be expected, since each term is at least the number of jets times a
positive constant times the squared height times the size of the Mellin transform on the
boundary; this remark is not formalized.
In the proof the extensions `χ ω` are those of a norm section, trivial on its image
(`exists_spectralBasepointChoice_of_normSection`). The functions `ϑ ω` are the multipliers of
`exists_uniform_heckeMultiplier_rectBoundary`, bounded by one, so `A ω = 0`.
The lower bounds are `ℓ ω k = c / (Y ω + |k| + 1) ^ n` with `Y ω = 1 + κ (χ ω)` for the size
`κ` of `exists_spectralLevel`; the constants `c`, `n` are the same for all the components that
see the test. For these components the number of jets between two heights is at most a constant
times `Y ω + |k|` (Jensen), and the Mellin transform of the test on the boundary of the `k`-th
rectangle is at most a constant times any negative power of `1 + κ (χ ω) + |k|`. The components
that see the test with `κ (χ ω) ≤ T` number at most a polynomial in `T`, so the sum over the
components and the heights converges. The other components carry a zero Mellin transform, and
their data come from the same theorems without uniformity.
The statement holds for every real Sobolev order `s`: it enters only through the surviving
multiplicities, which are at most the orders of the zeros.
Reconstruction: The paper does not state this. It is the project's formulation of what the
trace-class assertion of Theorem 10.3.2.1(2) needs when the zeros are summed by clusters cut
along well-chosen heights and not one at a time. The clustered statement, and from it trace
class, are proved from it below (`spectralStripConvolution_summable_clusterTraceNorms`,
`spectralStripConvolution_nuclear_of_summable_clusterTraceNorms`), through the contour
multiplier of `spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData` of
`Sec3_Clusters`. It asks for no bound at a single zero, so no lower bound for the distance
between two zeros enters. -/
theorem spectralStripConvolution_exists_clusterBoundaryData
    {α s : ℝ} (hα : 0 ≤ α) (φ : BruhatCompactSupport C𝔽) :
    ∃ (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (β X : ℝ) (A : PontryaginDual C₁ → ℕ)
      (ϑ : PontryaginDual C₁ → ℂ → ℂ)
      (T : PontryaginDual C₁ → ℤ → ℝ) (φb ℓ : PontryaginDual C₁ → ℤ → ℝ)
      (hfin : ∀ ω (k : ℤ),
        {z : Z(χ, α) | z.val.1 = ω ∧ T ω k ≤ z.val.2.2 ∧ z.val.2.2 < T ω (k + 1)}.Finite),
      IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) ∧
      α < β ∧ β < X ∧ (∀ ω, Differentiable ℂ (ϑ ω)) ∧
      (∀ ω (u : ℂ), |u.re| ≤ X + 2 → ‖ϑ ω u‖ ≤ (1 + |u.im|) ^ A ω) ∧
      (∀ z : Z(χ, α), ((N(χ, α, s, z) : ℕ) : ℕ∞) ≤
        analyticOrderAt (ϑ z.val.1) (shift(z.val.2.1, z.val.2.2))) ∧
      (∀ ω (k : ℤ), T ω k ∈ Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 1)) ∧
      (∀ ω k, 0 < ℓ ω k) ∧
      (∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)), ℓ ω k ≤ ‖ϑ ω w‖) ∧
      (∀ ω k, ∀ w ∈ rectBoundary (-X) X (T ω k) (T ω (k + 1)),
        ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽‖ ≤ φb ω k) ∧
      Summable (fun p : PontryaginDual C₁ × ℤ ↦
        ((∑ z ∈ (hfin p.1 p.2).toFinset, N(χ, α, s, z) : ℕ) : ℝ) *
          (rectInterpolantGaussianConstant X β (A p.1) *
            (φb p.1 p.2 / ℓ p.1 p.2 * (1 + |T p.1 p.2|) ^ (A p.1 + 2)))) := by
  classical
  -- A norm section and a basepoint choice trivial on its image.
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  obtain ⟨χ, hχ, hχτ, hχ1⟩ := exists_spectralBasepointChoice_of_normSection τ hτ
  -- The uniform constants.
  obtain ⟨β, X, hαβ, hβX, hdata⟩ := exists_uniform_heckeMultiplier_rectBoundary F a α
  obtain ⟨A₀, hA₀⟩ := bruhatCompactSupport_mellin_logConductor_le φ
  obtain ⟨c, n, hc, huni⟩ := hdata A₀
  obtain ⟨κ, hκ0, hκblock, ⟨Cc, d, hκcount⟩, hκdecay⟩ := exists_spectralLevel τ hτ φ
  have hX0 : 0 < X := (hα.trans_lt hαβ).trans hβX
  let M (ω : PontryaginDual C₁) (w : ℂ) : ℂ :=
    ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) w g ∂μ𝔽
  let S : Set (PontryaginDual C₁) := {ω | ∃ w : ℂ, M ω w ≠ 0}
  let Y (ω : PontryaginDual C₁) : ℝ := 1 + κ (χ ω)
  have hY1 (ω : PontryaginDual C₁) : 1 ≤ Y ω := by
    dsimp only [Y]
    linarith [hκ0 (χ ω)]
  have hnontriv (ω : PontryaginDual C₁) (hω : ω ≠ 1) :
      (χ ω).toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 := by
    intro h
    apply hω
    rw [← hχ ω]
    ext x : 1
    exact DFunLike.congr_fun h x
  have hψ (ω : PontryaginDual C₁) (B : ℝ) (hB : ω ≠ 1 → heckeLogDiscriminantConductor (χ ω) ≤ B) :
      χ ω = 1 ∨ ((χ ω).toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1 ∧
        heckeLogDiscriminantConductor (χ ω) ≤ B) := by
    by_cases h1 : ω = 1
    · left
      rw [h1]
      exact hχ1
    · exact Or.inr ⟨hnontriv ω h1, hB h1⟩
  -- The data of each component; the constants are uniform on the components that see the test.
  have hcomp : ∀ ω : PontryaginDual C₁, ∃ (cω : ℝ) (nω : ℕ) (ϑ : ℂ → ℂ) (T : ℤ → ℝ),
      0 < cω ∧ (ω ∈ S → cω = c ∧ nω = n) ∧ Differentiable ℂ ϑ ∧
      (∀ u : ℂ, ((mult(χ ω, (a : ℂ) + u) : ℕ) : ℕ∞) ≤ analyticOrderAt ϑ u) ∧
      (∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ u‖ ≤ 1) ∧
      (∀ k : ℤ, T k ∈ Icc (2 * (k : ℝ)) (2 * (k : ℝ) + 1)) ∧
      ∀ k : ℤ, ∀ w ∈ rectBoundary (-X) X (T k) (T (k + 1)),
        cω / (Y ω + |(k : ℝ)| + 1) ^ nω ≤ ‖ϑ w‖ := by
    intro ω
    have hblock := hκblock (χ ω) (hχτ ω)
    by_cases hS : ω ∈ S
    · obtain ⟨w, hw⟩ := hS
      obtain ⟨ϑ, T, h1, h2, h3, h4, h5⟩ :=
        huni (χ ω) (hψ ω A₀ fun _ ↦ hA₀ (χ ω) w hw) (Y ω) (hY1 ω) hblock
      exact ⟨c, n, ϑ, T, hc, fun _ ↦ ⟨rfl, rfl⟩, h1, h2, h3, h4, h5⟩
    · obtain ⟨c₂, n₂, hc₂, h₂⟩ := hdata (heckeLogDiscriminantConductor (χ ω))
      obtain ⟨ϑ, T, h1, h2, h3, h4, h5⟩ :=
        h₂ (χ ω) (hψ ω _ fun _ ↦ le_rfl) (Y ω) (hY1 ω) hblock
      exact ⟨c₂, n₂, ϑ, T, hc₂, fun h ↦ absurd h hS, h1, h2, h3, h4, h5⟩
  choose cc nn ϑ T hcc hSc hϑd hϑord hϑup hT hlow using hcomp
  have hT1 (ω : PontryaginDual C₁) (k : ℤ) : T ω k ≤ T ω (k + 1) := by
    have h1 := (hT ω k).2
    have h2 := (hT ω (k + 1)).1
    push_cast at h2
    linarith
  have hT3 (ω : PontryaginDual C₁) (k : ℤ) : T ω (k + 1) ≤ T ω k + 3 := by
    have h1 := (hT ω k).1
    have h2 := (hT ω (k + 1)).2
    push_cast at h2
    linarith
  have hTabs (ω : PontryaginDual C₁) (k : ℤ) : |T ω k| ≤ 2 * |(k : ℝ)| + 1 := by
    have h1 := (hT ω k).1
    have h2 := (hT ω k).2
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (k : ℝ)]
    · linarith [le_abs_self (k : ℝ)]
  -- The constants of the zero count and of the decay.
  have hρ₀ : 0 < |a - 2| + α + 2 := by positivity
  obtain ⟨CJ, hCJ0, hCJ⟩ := continuedCompletedHeckeL_closedBall_zeros_le_log_uniform F hρ₀ A₀
  obtain ⟨CJ1, hCJ10, hCJ1⟩ := continuedCompletedHeckeL_one_closedBall_zeros_le_log F hρ₀
  let CJ' : ℝ := max CJ CJ1
  have hCJ' : 0 ≤ CJ' := hCJ0.trans (le_max_left _ _)
  let Nd : ℕ := n + 3 + (d + 3)
  obtain ⟨Kd, hKd⟩ := hκdecay X Nd
  have hKd0 : 0 ≤ Kd :=
    (mul_nonneg (pow_nonneg (by positivity [hκ0 (χ 1)]) Nd) (norm_nonneg _)).trans
      (hKd (χ 1) (hχτ 1) 0 (by simpa using hX0.le))
  let L (ω : PontryaginDual C₁) (k : ℤ) : ℝ := 1 + κ (χ ω) + |(k : ℝ)|
  have hL1 (ω : PontryaginDual C₁) (k : ℤ) : 1 ≤ L ω k := by
    dsimp only [L]
    linarith [hκ0 (χ ω), abs_nonneg (k : ℝ)]
  let φb (ω : PontryaginDual C₁) (k : ℤ) : ℝ :=
    if ω ∈ S then Kd * 3 ^ Nd / L ω k ^ Nd else 0
  let ℓ (ω : PontryaginDual C₁) (k : ℤ) : ℝ := cc ω / (Y ω + |(k : ℝ)| + 1) ^ nn ω
  have hfin (ω : PontryaginDual C₁) (k : ℤ) :
      {z : Z(χ, α) | z.val.1 = ω ∧ T ω k ≤ z.val.2.2 ∧ z.val.2.2 < T ω (k + 1)}.Finite :=
    spectralStripComponent_finite_window a χ ω (T ω k) (T ω (k + 1))
  -- The number of jets of a cluster of a component that sees the test.
  have hJ (ω : PontryaginDual C₁) (hS : ω ∈ S) (k : ℤ) :
      ((∑ z ∈ (hfin ω k).toFinset, N(χ, α, s, z) : ℕ) : ℝ) ≤ 6 * CJ' * L ω k := by
    obtain ⟨w₀, hw₀⟩ := hS
    have hpos : 0 < Y ω + |T ω k + 3 / 2| + 2 := by linarith [hY1 ω, abs_nonneg (T ω k + 3 / 2)]
    have hlog0 : 0 ≤ Real.log (Y ω + |T ω k + 3 / 2| + 2) :=
      Real.log_nonneg (by linarith [hY1 ω, abs_nonneg (T ω k + 3 / 2)])
    have hcount : ∀ S' : Finset ℂ,
        (∀ z ∈ S', z ∈ Metric.closedBall (⟨2, T ω k + 3 / 2⟩ : ℂ) (|a - 2| + α + 2)) →
        ∑ z ∈ S', ((mult(χ ω, z) : ℕ) : ℝ) ≤
          CJ' * Real.log (Y ω + |T ω k + 3 / 2| + 2) := by
      intro S' hS'
      by_cases h1 : ω = 1
      · have hχω : χ ω = 1 := by rw [h1]; exact hχ1
        rw [hχω]
        refine (hCJ1 (T ω k + 3 / 2) S' hS').trans ?_
        have hpos1 : 0 < 1 + |T ω k + 3 / 2| + 2 := by linarith [abs_nonneg (T ω k + 3 / 2)]
        exact mul_le_mul (le_max_right _ _)
          (Real.log_le_log hpos1 (by linarith [hY1 ω]))
          (Real.log_nonneg (by linarith [abs_nonneg (T ω k + 3 / 2)])) hCJ'
      · exact (hCJ (χ ω) (hnontriv ω h1) (hA₀ (χ ω) w₀ hw₀) (Y ω) (hY1 ω)
          (hκblock (χ ω) (hχτ ω)) (T ω k + 3 / 2) S' hS').trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog0)
    have h1 := uniform_jetCount_le_of_closedBall a χ (s := s) ω hcount (hfin ω k).toFinset
      (fun z hz ↦ by
        obtain ⟨hω, h1, h2⟩ := (hfin ω k).mem_toFinset.mp hz
        exact ⟨hω, h1, h2.le.trans (hT3 ω k)⟩)
    refine h1.trans ?_
    have hlog := Real.log_le_sub_one_of_pos hpos
    have habs : |T ω k + 3 / 2| ≤ 2 * |(k : ℝ)| + 5 / 2 := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]
      linarith [hTabs ω k]
    have hbound : Real.log (Y ω + |T ω k + 3 / 2| + 2) ≤ 6 * L ω k := by
      dsimp only [L, Y] at hlog ⊢
      linarith [hκ0 (χ ω), abs_nonneg (k : ℝ)]
    calc CJ' * Real.log (Y ω + |T ω k + 3 / 2| + 2) ≤ CJ' * (6 * L ω k) :=
          mul_le_mul_of_nonneg_left hbound hCJ'
      _ = 6 * CJ' * L ω k := by ring
  let G₀ : ℝ := rectInterpolantGaussianConstant X β 0
  have hG₀ : 0 ≤ G₀ := rectInterpolantGaussianConstant_nonneg hX0.le _
  refine ⟨χ, β, X, fun _ ↦ 0, ϑ, T, φb, ℓ, hfin, hχ, hαβ, hβX, hϑd, fun ω u hu ↦ ?_,
    fun z ↦ spectralStripMultiplicity_le_analyticOrderAt a χ z (hϑord z.val.1), hT,
    fun ω k ↦ ?_, hlow, fun ω k w hw ↦ ?_, ?_⟩
  · rw [pow_zero]
    exact hϑup ω u hu
  · have := hcc ω
    have hbase : 0 < Y ω + |(k : ℝ)| + 1 := by linarith [hY1 ω, abs_nonneg (k : ℝ)]
    exact div_pos this (pow_pos hbase _)
  · -- The Mellin transform on the boundary of a rectangle.
    change ‖M ω w‖ ≤ if ω ∈ S then Kd * 3 ^ Nd / L ω k ^ Nd else 0
    by_cases hS : ω ∈ S
    · have hbd : |w.re| ≤ X ∧ T ω k ≤ w.im ∧ w.im ≤ T ω (k + 1) := by
        rcases mem_rectBoundary_iff.mp hw with ⟨h1, h | h⟩ | ⟨h1, h | h⟩
        · exact ⟨abs_le.mpr h1, h.ge, h.le.trans (hT1 ω k)⟩
        · exact ⟨abs_le.mpr h1, (hT1 ω k).trans h.ge, h.le⟩
        · exact ⟨by rw [h, abs_neg, abs_of_pos hX0], h1.1, h1.2⟩
        · exact ⟨by rw [h, abs_of_pos hX0], h1.1, h1.2⟩
      have hdec := hKd (χ ω) (hχτ ω) w hbd.1
      have him : |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm w
      have hkw : |(k : ℝ)| ≤ ‖w‖ + 2 := by
        have h1 := (hT ω k).1
        have h2 := (hT ω (k + 1)).2
        push_cast at h2
        rcases le_or_gt 0 k with hk | hk
        · have hk' : (0 : ℝ) ≤ k := by exact_mod_cast hk
          rw [abs_of_nonneg hk']
          linarith [le_abs_self w.im]
        · have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hk
          rw [abs_of_nonpos (by linarith)]
          linarith [neg_abs_le w.im]
      have hLle : L ω k ≤ 3 * (1 + ‖w‖ + κ (χ ω)) := by
        dsimp only [L]
        linarith [hκ0 (χ ω), norm_nonneg w]
      have hL0 : 0 < L ω k := by linarith [hL1 ω k]
      rw [ite_eq_left hS, le_div_iff₀ (pow_pos hL0 Nd)]
      calc ‖M ω w‖ * L ω k ^ Nd ≤ ‖M ω w‖ * (3 * (1 + ‖w‖ + κ (χ ω))) ^ Nd :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0.le hLle Nd) (norm_nonneg _)
        _ = 3 ^ Nd * ((1 + ‖w‖ + κ (χ ω)) ^ Nd * ‖M ω w‖) := by
            rw [mul_pow]
            ring
        _ ≤ 3 ^ Nd * Kd := mul_le_mul_of_nonneg_left hdec (by positivity)
        _ = Kd * 3 ^ Nd := mul_comm _ _
    · have h0 : M ω w = 0 := by
        by_contra h
        exact hS ⟨w, h⟩
      rw [ite_eq_right hS, h0, norm_zero]
  · -- The sum over the components and the heights.
    have hinjχ : Function.Injective χ := fun ω ω' h ↦ by rw [← hχ ω, ← hχ ω', h]
    refine summable_prod_int_of_encard_le_of_norm_le (E := ℝ) S (fun ω ↦ κ (χ ω))
      (fun ω _ ↦ hκ0 _) Cc d (6 * CJ' * (G₀ * (Kd * 3 ^ Nd * (2 ^ n / c) * 4))) (fun T' ↦ ?_) _
      (fun ω hS k ↦ ?_) (fun ω hS k ↦ ?_)
    · refine le_trans ?_ (hκcount T')
      rw [← hinjχ.injOn.encard_image]
      refine Set.encard_mono ?_
      rintro _ ⟨ω, ⟨hS, hk⟩, rfl⟩
      exact ⟨hχτ ω, hS, hk⟩
    · -- The decay of one term.
      have hLk1 := hL1 ω k
      have hLk0 : 0 < L ω k := by linarith
      have hJk := hJ ω hS k
      obtain ⟨hcω, hnω⟩ := hSc ω hS
      have hbase : 0 < Y ω + |(k : ℝ)| + 1 := by linarith [hY1 ω, abs_nonneg (k : ℝ)]
      have hbase2 : Y ω + |(k : ℝ)| + 1 ≤ 2 * L ω k := by
        dsimp only [L, Y]
        linarith [hκ0 (χ ω), abs_nonneg (k : ℝ)]
      have hT2 : 1 + |T ω k| ≤ 2 * L ω k := by
        dsimp only [L]
        linarith [hTabs ω k, hκ0 (χ ω)]
      have hJ0 : (0 : ℝ) ≤ ((∑ z ∈ (hfin ω k).toFinset, N(χ, α, s, z) : ℕ) : ℝ) :=
        Nat.cast_nonneg _
      change ‖((∑ z ∈ (hfin ω k).toFinset, N(χ, α, s, z) : ℕ) : ℝ) *
        (G₀ * ((if ω ∈ S then Kd * 3 ^ Nd / L ω k ^ Nd else 0) /
          (cc ω / (Y ω + |(k : ℝ)| + 1) ^ nn ω) * (1 + |T ω k|) ^ (0 + 2)))‖ ≤ _
      rw [ite_eq_left hS, hcω, hnω, Real.norm_of_nonneg (by positivity)]
      have hquot : Kd * 3 ^ Nd / L ω k ^ Nd / (c / (Y ω + |(k : ℝ)| + 1) ^ n) ≤
          Kd * 3 ^ Nd / L ω k ^ Nd * ((2 * L ω k) ^ n / c) := by
        rw [div_div_eq_mul_div, mul_div_assoc]
        exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
          (pow_le_pow_left₀ hbase.le hbase2 n) hc.le) (by positivity)
      have hsq : (1 + |T ω k|) ^ (0 + 2) ≤ (2 * L ω k) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hT2 2
      calc ((∑ z ∈ (hfin ω k).toFinset, N(χ, α, s, z) : ℕ) : ℝ) *
            (G₀ * (Kd * 3 ^ Nd / L ω k ^ Nd / (c / (Y ω + |(k : ℝ)| + 1) ^ n) *
              (1 + |T ω k|) ^ (0 + 2)))
          ≤ (6 * CJ' * L ω k) * (G₀ * (Kd * 3 ^ Nd / L ω k ^ Nd * ((2 * L ω k) ^ n / c) *
              (2 * L ω k) ^ 2)) :=
            mul_le_mul hJk (mul_le_mul_of_nonneg_left
              (mul_le_mul hquot hsq (by positivity) (by positivity)) hG₀) (by positivity)
              (by positivity)
        _ = 6 * CJ' * (G₀ * (Kd * 3 ^ Nd * (2 ^ n / c) * 4)) /
              (1 + κ (χ ω) + |(k : ℝ)|) ^ (d + 3) := by
            have hpow : L ω k ^ Nd = L ω k ^ (d + 3) * L ω k ^ n * L ω k ^ 3 := by
              rw [← pow_add, ← pow_add]
              congr 1
              dsimp only [Nd]
              omega
            change _ = _ / L ω k ^ (d + 3)
            rw [hpow]
            field_simp
            ring_nf
    · change ((∑ z ∈ (hfin ω k).toFinset, N(χ, α, s, z) : ℕ) : ℝ) *
        (G₀ * ((if ω ∈ S then Kd * 3 ^ Nd / L ω k ^ Nd else 0) /
          (cc ω / (Y ω + |(k : ℝ)| + 1) ^ nn ω) * (1 + |T ω k|) ^ (0 + 2))) = 0
      rw [ite_eq_right hS]
      simp

-- Select the norm topology directly when using the locally convex nuclear ideal, as in `Sec3`.
attribute [local instance] instSpectralQuotientPolynormableSec3

/-- Paper: Theorems 10.3.1.1(1)–(2) and 10.3.2.1(1)–(2), pp. 448–455. For a suitable choice of
the unitary extensions of the norm-one characters, and every Markushevich basis realizing the
strip jets of that choice, the zeros of the strip can be grouped into finite clusters, pairwise
disjoint and covering all the zeros, so that the trace norms of the cluster blocks of the
spectral convolution form a summable series. The block of a cluster is the finite section over
its zeros, with all their surviving jets; equivalently it is the convolution followed by the
projection onto the span of the biorthogonal vectors of the cluster.
It holds for every number field and every test. The extensions are those of a norm section. It
follows from `spectralStripConvolution_exists_clusterBoundaryData` through
`spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData` of `Sec3_Clusters`. No
distance between two zeros of a Hecke L-function enters, and the recorded gap #7241 is not used.
Reconstruction: The paper does not state this. It is the project's formulation of what the
trace-class assertion of Theorem 10.3.2.1(2) needs from part (1) when the zeros are summed by
clusters and not one at a time. Trace class follows from it
(`spectralStripConvolution_nuclear_of_summable_clusterTraceNorms`). It does not give the sums of
(10.3.2.1) over single zeros in an arbitrary order (`spectralStripConvolution_traceCauchy` of
`Sec3`); those need the recorded gap #7241.
Deviation: Stated for one choice of the extensions, which is all that trace class needs. The
conclusion for every choice is `spectralStripConvolution_summable_clusterTraceNorms_forall`.
Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1` (p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽) :
    ∃ χ : PontryaginDual C₁ → PontryaginDual C𝔽,
      IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω) ∧
      ∀ (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
        (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s →
          StrongDual ℂ Q(a, hStrip(hα), hs)),
        IsSpectralMarkushevichBasis x Λ →
        (∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
          (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
            (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) →
        ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
          P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
          (∀ K : P, (R K).val = spectralConvolutionFiniteSum
            (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
            (fun z ↦ N(χ, α, s, z))
            (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
          Summable (fun K : P ↦ traceNorm (R K)) :=
  (spectralStripConvolution_exists_clusterBoundaryData (s := s) a hα φ).elim
    fun χ h ↦ h.elim fun _β h ↦ h.elim fun _X h ↦ h.elim fun A h ↦ h.elim fun ϑ h ↦
    h.elim fun T h ↦ h.elim fun φb h ↦ h.elim fun ℓ h ↦ h.elim fun hfin h ↦
      ⟨χ, h.1, fun x Λ hb hj ↦
        spectralStripConvolution_summable_clusterTraceNorms_of_boundaryData a χ h.1 hα hs h.2.1
          h.2.2.1 φ x Λ hb hj A ϑ h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 T h.2.2.2.2.2.2.1 φb ℓ
          h.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2.2.2.1 hfin
          h.2.2.2.2.2.2.2.2.2.2⟩

/-- Paper: Theorems 10.3.1.1(1)–(2) and 10.3.2.1(1)–(2), pp. 448–455. The clustered statement
for every choice of the unitary extensions of the norm-one characters: for every such choice
`χ` and every Markushevich basis realizing the strip jets of `χ`, the zeros of the strip can be
grouped into finite clusters, pairwise disjoint and covering all the zeros, so that the trace
norms of the cluster blocks of the spectral convolution form a summable series.
The boundary data of `spectralStripConvolution_exists_clusterBoundaryData` are produced for one
choice only, trivial on the image of a norm section. The clustered conclusion holds for every
choice: it is carried over by relabelling the zeros
(`spectralStripConvolution_summable_clusterTraceNorms_forall_of_exists` of
`Sec3_BasepointChoice`).
Reconstruction: The paper does not state this. As for
`spectralStripConvolution_summable_clusterTraceNorms`, it is the project's formulation of what
the trace-class assertion of Theorem 10.3.2.1(2) needs from part (1) when the zeros are summed
by clusters and not one at a time.
Deviation: Stated for every Sobolev order `s ≥ 0`; §10.3 of the paper assumes `s > 1`
(p. 455). -/
theorem spectralStripConvolution_summable_clusterTraceNorms_forall
    {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) (fun ω ↦ χ ω))
    (x : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s → Q(a, hStrip(hα), hs))
    (Λ : SpectralStripJetIndex (F := F) (fun ω ↦ χ ω) a α s →
      StrongDual ℂ Q(a, hStrip(hα), hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a hStrip(hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) (fun ω ↦ χ ω) hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ (P : Set (Finset Z(χ, α))) (R : P → nuclearEndomorphisms Q(a, hStrip(hα), hs)),
      P.PairwiseDisjoint id ∧ (∀ z : Z(χ, α), ∃ K ∈ P, z ∈ K) ∧
      (∀ K : P, (R K).val = spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a hStrip(hα) hs φ) x Λ K.val
        (fun z ↦ N(χ, α, s, z))
        (fun z m ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩)) ∧
      Summable (fun K : P ↦ traceNorm (R K)) :=
  spectralStripConvolution_summable_clusterTraceNorms_forall_of_exists a hα hs φ
    (spectralStripConvolution_summable_clusterTraceNorms a hα hs φ) χ hχ x Λ hb hj

/-- Paper: Theorem 10.3.2.1(2), p. 454. The statement of `spectralStripConvolution_nuclear` of
`Sec3`, for every number field, every test and every Sobolev order `s ≥ 0`: convolution on the
strip spectral quotient is trace class. It is proved from the clustered statement
`spectralStripConvolution_summable_clusterTraceNorms`, without the recorded gap
`spectralStripConvolution_traceCauchy_compact_block_series` of `Sec3` (#7241) and with no
hypothesis on the zeros: the zeros are summed by clusters between well-chosen heights, and the
estimates of the classical kind are proved for multipliers built from the Hecke L-functions
(`Sec3_HeckeMultipliers`), with constants uniform in the character.
Deviation: Theorem 10.3.2.1 and §10.3 assume `s > 1` (p. 455); here `s ≥ 0`. This includes the
orders `0 ≤ s ≤ 1` at which Theorems 10.4.2.1, 10.4.2.2 and 10.4.2.8 (pp. 459–463) use trace
class. The statement of `Sec3`, for `s > 1`, is the case checked after the line theorem below. -/
theorem spectralStripConvolution_nuclear_of_summable_clusterTraceNorms {α s : ℝ} (hα : 0 ≤ α)
    (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, hStrip(hα), hs)
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a hStrip(hα) hs φ) := by
  obtain ⟨χ, hχ, hclusters⟩ := spectralStripConvolution_summable_clusterTraceNorms a hα hs φ
  obtain ⟨_, x, Λ, hb, hj⟩ := spectralStripMarkushevichBasis (a := a) χ hχ hα hs
  obtain ⟨P, R, hdisj, hcover, hR, hsum⟩ := hclusters x Λ hb hj
  exact spectralStripConvolution_nuclear_of_clusters a χ hα hs φ x Λ hb P R hdisj hcover hR hsum

local notation "h₀" => le_rfl (a := (0 : ℝ))

/-- Paper: Theorem 10.3.1.1(2), p. 448. The statement of `spectralLineConvolution_nuclear` of
`Sec3`, for every number field and every test: for every real `a` and every `s ≥ 0`,
convolution on the `a`-line spectral quotient is trace class. It is the strip statement
`spectralStripConvolution_nuclear_of_summable_clusterTraceNorms` at half-width zero, carried
along `-0 = 0`; so it is proved without the recorded gap #7241 and with no hypothesis on the
zeros.
Deviation: Theorem 10.3.1.1 assumes `s > 1` (p. 448); here `s ≥ 0`. For `s ≤ 1` the line quotient
is zero (`globalThetaSobolev_line_eq_top_of_le_one`), so only `s > 1` has content. The statement
of `Sec3`, for `s > 1`, is the case checked below. -/
theorem spectralLineConvolution_nuclear_of_summable_clusterTraceNorms {s : ℝ} (hs : 0 ≤ s)
    (φ : BruhatCompactSupport C𝔽) :
    let H := Q(a, h₀, hs)
    IsNuclearOperator (E := H) (F := H) (spectralConvolution (F := F) a h₀ hs φ) := by
  have key : ∀ (l r : ℝ) (hI : l ≤ r), l = -r → 0 ≤ r →
      IsNuclearOperator (E := Q(a, hI, hs)) (F := Q(a, hI, hs))
        (spectralConvolution (F := F) a hI hs φ) := by
    intro l r hI hl hr
    subst hl
    exact spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hr hs φ
  exact key 0 0 le_rfl neg_zero.symm le_rfl

-- The two theorems above give the statements `spectralStripConvolution_nuclear` and
-- `spectralLineConvolution_nuclear` of `Sec3`, stated there for `1 < s`.
example : type_of% @spectralStripConvolution_nuclear :=
  @fun _ _ _ a _ _ hα hs φ ↦
    spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα (zero_lt_one.trans hs).le φ

example : type_of% @spectralLineConvolution_nuclear :=
  @fun _ _ _ a _ hs φ ↦
    spectralLineConvolution_nuclear_of_summable_clusterTraceNorms a (zero_lt_one.trans hs).le φ

end Assembly

end RiemannMasullo
