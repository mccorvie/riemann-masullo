module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineQuarticWindows
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
@[expose] public noncomputable section
open Set Function Filter
open scoped BigOperators
namespace RiemannMasullo.Isolated
open MeasureTheory NumberField
open scoped InnerProductSpace NNReal NumberField.AdeleRing
set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "Ω" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "ν𝔽" => canonicalModulatedHaar m𝔽 hm𝔽



local notation "J(" χ ", " a ")" => SpectralStripJetIndex χ a 0 4

private theorem quartic_jet_divisor_pos
    {a : ℝ} (χ : Ω → PontryaginDual C𝔽) (ω : Ω) (j : J(χ, a)) (hjω : j.val.1 = ω) :
    0 < MeromorphicOn.divisor (continuedCompletedHeckeL (χ ω)) univ
      ((a : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I) := by
  have h := j.property
  rw [spectralStripMultiplicity_boundary (le_refl (0 : ℝ))
    (Or.inr (spectralLineQuarticJet_re_zero χ j))] at h
  have hn := Nat.zero_lt_of_lt (((lt_spectralBoundaryMultiplicity 4 _ _).mp h).1)
  have hp : 0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
      ((a : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I)).untop₀.toNat := by
    simpa only [spectralLineQuarticJet_re_zero χ j, add_zero, hjω] using hn
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn (mem_univ _)]
  omega

/-- In each fixed character, the number of retained order-four jets in
`[-R,R]` is at most quadratic in `R`. The bound follows from the established
summability of the positive Hecke divisor against `(1 + |Im z|)⁻²`. -/
theorem spectralLineQuartic_jets_quadratic_count
    (a : ℝ) (χ : Ω → PontryaginDual C𝔽) (ω : Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R → ∀ K : Finset J(χ, a),
      (∀ j ∈ K, j.val.1 = ω ∧ |j.val.2.2.1| ≤ R) →
        (K.card : ℝ) ≤ C * (1 + R) ^ 2 := by
  classical
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL (χ ω)) univ
  let Z := {z : ℂ // 0 < D z}
  let w (p : Fin 2 × Z) : ℝ := (D p.2.val : ℝ) / (1 + |p.2.val.im|) ^ 2
  have hw0 (p : Fin 2 × Z) : 0 ≤ w p := div_nonneg
    (by exact_mod_cast p.2.property.le) (sq_nonneg _)
  have hw : Summable w := by
    apply (summable_prod_of_nonneg hw0).mpr
    refine ⟨fun i ↦ ?_, Summable.of_finite⟩
    exact explicitFormulaCompletedHeckeL_summable_divisor_div_sq (χ ω)
  refine ⟨∑' p, w p, tsum_nonneg hw0, fun R hR K hK ↦ ?_⟩
  let e (j : K) : Fin 2 × Z :=
    (⟨j.val.val.2.2.2, by have h := spectralLineQuarticJet_order_le_one χ j.val; omega⟩,
      ⟨(a : ℂ) + (j.val.val.2.2.1 : ℂ) * Complex.I,
        quartic_jet_divisor_pos χ ω j.val (hK j.val j.property).1⟩)
  have he : Injective e := by
    intro j k h
    have ho := congrArg (fun p : Fin 2 × Z ↦ p.1.val) h
    have ht := congrArg (fun p : Fin 2 × Z ↦ p.2.val.im) h
    have ht' : j.val.val.2.2.1 = k.val.val.2.2.1 := by
      simpa only [e, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero, zero_add] using ht
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext ((hK j.val j.property).1.trans (hK k.val k.property).1.symm)
    apply Prod.ext ((spectralLineQuarticJet_re_zero χ j.val).trans
      (spectralLineQuarticJet_re_zero χ k.val).symm)
    exact Prod.ext ht' ho
  have hsum : (∑ j : K, w (e j)) ≤ ∑' p, w p := by
    have hh := (show Summable (fun j : K ↦ w (e j)) from .of_finite).tsum_le_tsum_of_inj
      e he (fun p _ ↦ hw0 p) (fun _ ↦ le_rfl) hw
    simpa only [tsum_fintype] using hh
  have hpoint (j : K) : 1 ≤ (1 + R) ^ 2 * w (e j) := by
    have hD : (1 : ℝ) ≤ (D (e j).2.val : ℝ) := by
      exact_mod_cast (show 1 ≤ D (e j).2.val from (e j).2.property)
    have hIm : |(e j).2.val.im| ≤ R := by
      simpa only [e, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero, zero_add] using (hK j.val j.property).2
    dsimp only [w]
    rw [← mul_div_assoc, le_div_iff₀ (by positivity : 0 < (1 + |(e j).2.val.im|) ^ 2), one_mul]
    calc
      (1 + |(e j).2.val.im|) ^ 2 ≤ (1 + R) ^ 2 := by gcongr
      _ ≤ (1 + R) ^ 2 * (D (e j).2.val : ℝ) := le_mul_of_one_le_right (sq_nonneg _) hD
  calc
    (K.card : ℝ) = ∑ _j : K, (1 : ℝ) := by simp
    _ ≤ ∑ j : K, (1 + R) ^ 2 * w (e j) := Finset.sum_le_sum fun j _ ↦ hpoint j
    _ = (1 + R) ^ 2 * ∑ j : K, w (e j) := (Finset.mul_sum ..).symm
    _ ≤ (1 + R) ^ 2 * ∑' p, w p := mul_le_mul_of_nonneg_left hsum (sq_nonneg _)
    _ = _ := mul_comm _ _

local notation "W₄" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-0) 0 4
local notation "hs₁" => (show (1 : ℝ) < 4 by norm_num)
local notation "Pspec(" a ")" => spectralProjection (F := F) a (le_refl (0 : ℝ)) (show (0 : ℝ) ≤ 4 by norm_num)

/-- In a fixed angular character, the ambient rank of order-four frequency
windows grows at most quadratically with their radius, uniformly in the symbol. -/
theorem spectralLineQuartic_window_rank_quadratic
    (a : ℝ) (χ : Ω → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      ∀ (A : W₄ →L[ℂ] W₄) (b : Ω → ℝ → ℂ),
        (∀ ζ t u, fractionalLineWaveEval hs₁ (χ ζ) t (A u) =
          b ζ t * fractionalLineWaveEval hs₁ (χ ζ) t u) →
        (∀ ζ t, b ζ t ≠ 0 → ζ = ω ∧ |t| < R) →
        FiniteDimensional ℂ (A.comp Pspec(a)).toLinearMap.range ∧
          (Module.finrank ℂ (A.comp Pspec(a)).toLinearMap.range : ℝ) ≤ C * (1 + R) ^ 2 := by
  classical
  obtain ⟨C, hC, hcount⟩ := spectralLineQuartic_jets_quadratic_count a χ ω
  refine ⟨4 + C, by positivity, fun R hR A b hA hb ↦ ?_⟩
  have h := spectralLineQuartic_window_finiteRank a χ hχ A b ω (-R) R hA
    (fun ζ t ht ↦ ⟨(hb ζ t ht).1, abs_lt.mp (hb ζ t ht).2⟩)
  refine ⟨h.1, ?_⟩
  let S := {j : J(χ, a) | j.val.1 = ω ∧ j.val.2.2.1 ∈ Icc (-R) R}
  have hS : S.Finite := spectralLineQuartic_finite_jets_on_compact a χ ω _ isCompact_Icc
  have hn := hcount R hR hS.toFinset (fun j hj ↦
    ⟨(hS.mem_toFinset.mp hj).1, abs_le.mpr (hS.mem_toFinset.mp hj).2⟩)
  have hr : (Module.finrank ℂ (A.comp Pspec(a)).toLinearMap.range : ℝ) ≤ 4 + S.ncard := by
    exact_mod_cast h.2
  have hn' : (S.ncard : ℝ) ≤ C * (1 + R) ^ 2 := by
    simpa only [Set.ncard_eq_toFinset_card S hS] using hn
  have hR1 : 1 ≤ (1 + R) ^ 2 := by nlinarith
  nlinarith

end RiemannMasullo.Isolated
