module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoissonAsymptotic
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoissonFormula
public import RiemannMasullo.ForMathlib.NumberTheory.NumberField.DedekindZeta.MultipleZero
import Mathlib.Tactic

/-! # Comparing multiplicities for two completed Hecke functions

An excess of field degree, or an excess of conductor with the same degree, gives
infinitely many distinct zeros where one positive divisor order is larger. A
finite set of excess sites can contribute only a bounded amount to the scaled
real Poisson mass. The degree and conductor terms give growth on the same axis.

The principal-character specialization gives a different proof of the unbounded
multiple zeros in the splitting field of X³ − 2, using its existing cubic
subfield relation. Hu, Kaneko, Martin and Schildkraut, *Order of zeros of
Dedekind zeta functions*, Theorem 1.1, p. 2, prove the multiple-zero conclusion
for arbitrary nonabelian Galois extensions.
[Paper](https://arxiv.org/pdf/2107.03269#page=2)
-/

@[expose] public noncomputable section

open Filter Function NumberField Set Topology
open scoped NNReal
namespace RiemannMasullo.HeckePoisson
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F] {E : Type*} [Field E] [NumberField E]
local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F

/-- Positive divisor order, extended by zero to every point of the complex plane. -/
def positiveOrder (χ : PontryaginDual C𝔽(F)) (z : ℂ) : ℕ :=
  (MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z).toNat

private theorem positiveOrder_pos_iff (χ : PontryaginDual C𝔽(F)) (z : ℂ) :
    0 < positiveOrder χ z ↔ 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z := by
  unfold positiveOrder
  omega

private theorem scaled_weight_bounds {a : ℝ} (ha : 1 ≤ a) {z : ℂ} (h : z.re < 1) :
    0 ≤ a * poissonWeight (a+1/2) 0 z ∧ a * poissonWeight (a+1/2) 0 z ≤ 2 := by
  let d := a+1/2-z.re
  have hd : 0 < d := by dsimp [d]; linarith
  have hda : a ≤ 2*d := by dsimp [d]; linarith
  have hden : 0 < d^2+(0-z.im)^2 := by positivity
  change 0 ≤ a * (d / (d^2+(0-z.im)^2)) ∧ a * (d / (d^2+(0-z.im)^2)) ≤ 2
  refine ⟨mul_nonneg (by linarith) (div_nonneg hd.le hden.le), ?_⟩
  rw [← mul_div_assoc, div_le_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_right hda hd.le, sq_nonneg (0-z.im)]

private theorem scaled_order_nonneg (χ : PontryaginDual C𝔽(F)) {a : ℝ} (ha : 1 ≤ a) (z : ℂ) :
    0 ≤ (positiveOrder χ z : ℝ) * (a * poissonWeight (a+1/2) 0 z) := by
  by_cases hz : positiveOrder χ z = 0
  · simp [hz]
  · have hs := positive_divisor_re_mem_Ioo χ ((positiveOrder_pos_iff χ z).1 (Nat.pos_of_ne_zero hz))
    exact mul_nonneg (Nat.cast_nonneg _) (scaled_weight_bounds ha hs.2).1

private theorem hasSum_scaled_order (τ : ℝ≥0ˣ →ₜ* C𝔽(F)) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual C𝔽(F)) (hχ : ∀ r, χ (τ r) = 1) {a : ℝ} (ha : 1 ≤ a) :
    HasSum (fun z : ℂ ↦ (positiveOrder χ z : ℝ) * (a * poissonWeight (a+1/2) 0 z))
      (a * logDerivativeMass χ (a+1/2) 0) := by
  let w (z : ℂ) := (positiveOrder χ z : ℝ) * (a * poissonWeight (a+1/2) 0 z)
  change HasSum w _
  have hs : support w ⊆ {z : ℂ | 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ z} := by
    intro z hz
    by_contra h
    have h0 : positiveOrder χ z = 0 :=
      Int.toNat_eq_zero.2 (le_of_not_gt h)
    exact hz (by simp [w,h0])
  apply (hasSum_subtype_iff_of_support_subset hs).1
  have hp := (hasSum_logDerivativeMass τ hτ χ hχ (a+1/2) 0 (by linarith)).mul_left a
  apply hp.congr_fun
  intro p
  change (multiplicity p : ℝ) * (a * poissonWeight (a+1/2) 0 p.val) =
    a * ((multiplicity p : ℝ) * poissonWeight (a+1/2) 0 p.val)
  ring

private theorem bounded_scaled_excess_of_finite (τ : ℝ≥0ˣ →ₜ* C𝔽(F)) (hτ : RightInverse τ (ideleClassNorm F))
    (υ : ℝ≥0ˣ →ₜ* C𝔽(E)) (hυ : RightInverse υ (ideleClassNorm E))
    (χ : PontryaginDual C𝔽(F)) (hχ : ∀ r, χ (τ r) = 1)
    (ψ : PontryaginDual C𝔽(E)) (hψ : ∀ r, ψ (υ r) = 1)
    (he : {z : ℂ | positiveOrder ψ z < positiveOrder χ z}.Finite) :
    ∃ B : ℝ, ∀ a : ℝ, 1 ≤ a →
      a * logDerivativeMass χ (a+1/2) 0 - a * logDerivativeMass ψ (a+1/2) 0 ≤ B := by
  classical
  let S := he.toFinset
  let bound (z : ℂ) : ℝ := if z ∈ S then 2 * positiveOrder χ z else 0
  have hb : HasSum bound (∑ z ∈ S, bound z) := hasSum_sum_of_ne_finset_zero (s := S) (f := bound) (fun z hz ↦ by simp [bound,hz])
  refine ⟨∑ z ∈ S, bound z, fun a ha ↦ ?_⟩
  apply hasSum_le _ ((hasSum_scaled_order τ hτ χ hχ ha).sub (hasSum_scaled_order υ hυ ψ hψ ha)) hb
  intro z
  change (positiveOrder χ z : ℝ) * (a * poissonWeight (a+1/2) 0 z) -
    (positiveOrder ψ z : ℝ) * (a * poissonWeight (a+1/2) 0 z) ≤ bound z
  by_cases hz : positiveOrder χ z = 0
  · have hn := scaled_order_nonneg ψ ha z
    simp only [hz, Nat.cast_zero, zero_mul, zero_sub, bound, mul_zero, ite_self]
    linarith
  · have hs := positive_divisor_re_mem_Ioo χ ((positiveOrder_pos_iff χ z).1 (Nat.pos_of_ne_zero hz))
    obtain ⟨hpos,hmax⟩ := scaled_weight_bounds ha hs.2
    by_cases hm : z ∈ S
    · simp only [bound, ite_eq_left hm]
      have h := mul_le_mul_of_nonneg_left hmax (Nat.cast_nonneg (positiveOrder χ z) : (0:ℝ) ≤ _)
      linarith [scaled_order_nonneg ψ ha z]
    · have ht : positiveOrder χ z ≤ positiveOrder ψ z := le_of_not_gt (fun h ↦ hm (he.mem_toFinset.2 h))
      have hn : (positiveOrder χ z : ℝ) ≤ positiveOrder ψ z := by exact_mod_cast ht
      simp only [bound, ite_eq_right hm]
      linarith [mul_le_mul_of_nonneg_right hn hpos]

/-- The degree is the leading term, and the conductor distinguishes equal degrees. -/
theorem tendsto_scaled_mass_excess (χ : PontryaginDual C𝔽(F)) (ψ : PontryaginDual C𝔽(E))
    (h : Module.finrank ℚ E < Module.finrank ℚ F ∨ (Module.finrank ℚ E = Module.finrank ℚ F ∧
      heckeLogDiscriminantConductor ψ < heckeLogDiscriminantConductor χ)) :
    Tendsto (fun a : ℝ ↦ a * logDerivativeMass χ (a+1/2) 0 -
      a * logDerivativeMass ψ (a+1/2) 0) atTop atTop := by
  classical
  let d : ℝ := ((Module.finrank ℚ F : ℝ) - (Module.finrank ℚ E : ℝ))/2
  let q := (heckeLogDiscriminantConductor χ - heckeLogDiscriminantConductor ψ)/2
  let c := ((if χ=1 then 2 else 0) + archimedeanCountConstant χ) -
    ((if ψ=1 then 2 else 0) + archimedeanCountConstant ψ)
  have eqn (a : ℝ) : elementaryCount χ a - elementaryCount ψ a =
      a * (d * Real.log (a/(2*Real.pi)) + q) + c := by
    dsimp [elementaryCount,d,q,c]
    ring
  have logtop : Tendsto (fun a : ℝ ↦ Real.log (a/(2*Real.pi))) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))
  have main : Tendsto (fun a : ℝ ↦ a * (d * Real.log (a/(2*Real.pi))+q)) atTop atTop := by
    rcases h with hh | ⟨hd,hq⟩
    · have hcast : (Module.finrank ℚ E : ℝ) < (Module.finrank ℚ F : ℝ) := by exact_mod_cast hh
      have hd : 0 < d := div_pos (sub_pos.2 hcast) (by norm_num)
      exact tendsto_id.atTop_mul_atTop₀
        (tendsto_atTop_add_const_right atTop q (logtop.const_mul_atTop hd))
    · have d0 : d = 0 := by simp [d, hd]
      simpa only [d0, zero_mul, zero_add] using
        (tendsto_id.atTop_mul_const (div_pos (sub_pos.2 hq) (by norm_num)) :
          Tendsto (fun a : ℝ ↦ a*q) atTop atTop)
  have he : Tendsto (fun a : ℝ ↦ elementaryCount χ a - elementaryCount ψ a) atTop atTop :=
    (tendsto_atTop_add_const_right atTop c main).congr (fun a ↦ (eqn a).symm)
  have herr := (tendsto_logDerivativeMass_sub_elementary χ).sub (tendsto_logDerivativeMass_sub_elementary ψ)
  exact (he.atTop_add herr).congr (fun a ↦ by ring)

/-- A larger degree, or a larger conductor at the same degree, forces infinitely many
distinct points of greater positive divisor order. The fields and characters may differ. -/
theorem infinite_positiveOrder_excess
    (τ : ℝ≥0ˣ →ₜ* C𝔽(F)) (hτ : RightInverse τ (ideleClassNorm F))
    (υ : ℝ≥0ˣ →ₜ* C𝔽(E)) (hυ : RightInverse υ (ideleClassNorm E))
    (χ : PontryaginDual C𝔽(F)) (hχ : ∀ r, χ (τ r) = 1)
    (ψ : PontryaginDual C𝔽(E)) (hψ : ∀ r, ψ (υ r) = 1)
    (h : Module.finrank ℚ E < Module.finrank ℚ F ∨ (Module.finrank ℚ E = Module.finrank ℚ F ∧
      heckeLogDiscriminantConductor ψ < heckeLogDiscriminantConductor χ)) :
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧ positiveOrder ψ z < positiveOrder χ z}.Infinite := by
  have hi : {z : ℂ | positiveOrder ψ z < positiveOrder χ z}.Infinite := by
    intro hf
    obtain ⟨B,hB⟩ := bounded_scaled_excess_of_finite τ hτ υ hυ χ hχ ψ hψ hf
    have he := (tendsto_scaled_mass_excess χ ψ h).eventually_gt_atTop B
    obtain ⟨a,ha,hg⟩ := (he.and (eventually_ge_atTop (1 : ℝ))).exists
    exact ha.not_ge (hB a hg)
  apply hi.mono
  intro z hz
  have hop : 0 < positiveOrder χ z := lt_of_le_of_lt (Nat.zero_le _) hz
  have ⟨h0,h1⟩ := positive_divisor_re_mem_Ioo χ ((positiveOrder_pos_iff χ z).1 hop)
  exact ⟨h0,h1,hz⟩

/-- The positive order agrees everywhere with the finite part of the meromorphic order. -/
theorem positiveOrder_eq_meromorphicOrder (χ : PontryaginDual C𝔽(F)) (z : ℂ) :
    positiveOrder χ z = (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat := by
  exact congrArg Int.toNat ((continuedCompletedHeckeL_spec χ).1.meromorphicOn.divisor_apply (mem_univ z))

private theorem exists_positiveOrder_normSection (K : Type*) [Field K] [NumberField K] :
    ∃ τ : ℝ≥0ˣ →ₜ* C𝔽(K), RightInverse τ (ideleClassNorm K) := by
  let τ : ℝ≥0ˣ →ₜ* C𝔽(K) := (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
    IdeleGroup (𝓞 K) K →ₜ* C𝔽(K)).comp
      ⟨canonicalIdeleNormSection K, canonicalIdeleNormSection_continuous K⟩
  exact ⟨τ, canonicalIdeleNormSection_rightInverse K⟩

/-- Unconditional excess over the rational completed zeta function for principal characters. -/
theorem dedekindZeta_positiveOrder_excess_infinite (F : Type*) [Field F] [NumberField F]
    (hdeg : 1 < Module.finrank ℚ F) :
    {z : ℂ | 0 < z.re ∧ z.re < 1 ∧
      (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) z).untop₀.toNat <
      (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(F))) z).untop₀.toNat}.Infinite := by
  obtain ⟨τ,hτ⟩ := exists_positiveOrder_normSection F
  obtain ⟨υ,hυ⟩ := exists_positiveOrder_normSection ℚ
  simpa only [positiveOrder_eq_meromorphicOrder] using
    infinite_positiveOrder_excess τ hτ υ hυ 1 (by simp) 1 (by simp)
      (Or.inl (by simpa using hdeg))

/-- The splitting field of X³ − 2 has arbitrarily high multiple zeros. This proof uses
the scaled real Poisson sums for the cubic subfield and the rational field. -/
theorem cubicSplittingField_multipleZeros_unbounded_of_poisson (B : ℝ) :
    let L := (Polynomial.X ^ 3 - Polynomial.C (2 : ℚ)).SplittingField
    letI : NumberField L := ⟨⟩
    ∃ z : ℂ, B < z.im ∧ 0 < z.re ∧ z.re < 1 ∧
      1 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(L))) z).untop₀.toNat := by
  apply cubicSplittingField_multipleZeros_unbounded_of_subfield_excess _ B
  intro K _ _ hd
  exact dedekindZeta_positiveOrder_excess_infinite K (by omega)

end RiemannMasullo.HeckePoisson
