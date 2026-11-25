module

public import RiemannMasullo.Ch01_Introduction.Sec4_ExpandingPoisson
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoissonFormula
import Mathlib.Tactic

/-! # Translated Poisson deficits at high ordinate

For a fixed real abscissa greater than one, multiply the arithmetic Poisson
mass left after subtracting all critical-line contributions by the square of
the translation height. Reflection then records every off-line copy with the
same limiting weight. At abscissa two the resulting threshold is three.

The fixed translated positive kernel comes from the finite-height method of
Hiary, Ireland and Kyi, §5, Theorem 11. The index set and its multiplicities
here are the ones used for the expanding real-width count.
[Paper](https://arxiv.org/html/2408.00187v1#S5)
-/

@[expose] public noncomputable section

open Filter Function NumberField Set Topology
open scoped ComplexConjugate ENNReal NNReal
namespace RiemannMasullo.HeckePoisson

/-- In either real direction a single translated Cauchy kernel has leading
coefficient equal to its horizontal distance. -/
theorem tendsto_height_sq_mul_poissonWeight (σ : ℝ) (p : ℂ) :
    Tendsto (fun t : ℝ ↦ t^2 * poissonWeight σ t p) (cocompact ℝ) (𝓝 (σ-p.re)) := by
  have hInv : Tendsto (fun t : ℝ ↦ t⁻¹) (cocompact ℝ) (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [norm_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ ↦ t⁻¹) atTop (𝓝 0)).comp
        (tendsto_norm_cocompact_atTop (E := ℝ))
  have hx : Tendsto (fun t : ℝ ↦ (σ-p.re)*t⁻¹) (cocompact ℝ) (𝓝 0) := by
    simpa using hInv.const_mul (σ-p.re)
  have hy : Tendsto (fun t : ℝ ↦ 1-p.im*t⁻¹) (cocompact ℝ) (𝓝 1) := by
    simpa using (hInv.const_mul p.im).const_sub (1:ℝ)
  have hd : Tendsto (fun t : ℝ ↦ ((σ-p.re)*t⁻¹)^2 + (1-p.im*t⁻¹)^2)
      (cocompact ℝ) (𝓝 1) := by simpa using (hx.pow 2).add (hy.pow 2)
  have h := (tendsto_const_nhds (x := σ-p.re)).div hd one_ne_zero
  rw [div_one] at h
  apply h.congr'
  have hn : ∀ᶠ t : ℝ in cocompact ℝ, t ≠ 0 := isCompact_singleton.compl_mem_cocompact
  filter_upwards [hn] with t ht
  have he : ((σ-p.re)*t⁻¹)^2 + (1-p.im*t⁻¹)^2 =
      ((σ-p.re)^2+(t-p.im)^2)/t^2 := by field_simp
  change (σ-p.re) / (((σ-p.re)*t⁻¹)^2 + (1-p.im*t⁻¹)^2) = _
  rw [he, div_div_eq_mul_div]
  unfold poissonWeight
  ring

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual CF
local notation "Off(" χ ")" => {z : Site χ // z.val.re ≠ 1/2}
local notation "Central(" χ ")" => {z : Site χ // z.val.re = 1/2}

/-- Sum of the Cauchy weights over the genuine critical-line sites at one
translated point, counted with all their multiplicities. -/
def centralTranslatedMass (χ : U) (σ t : ℝ) : ℝ :=
  ∑' p : Central(χ), (multiplicity p.val : ℝ) * poissonWeight σ t p.val.val

private def offReflection (χ : U) : Off(χ) ≃ Off(χ) :=
  (positiveSiteReflection χ).subtypeEquiv fun z ↦ by
    change (z.val.re ≠ 1/2) ↔ ((1-conj z.val).re ≠ 1/2)
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    constructor <;> intro h he <;> apply h <;> linarith

private def highSiteWeight {χ : U} (σ t : ℝ) (p : Site χ) : ℝ :=
  (multiplicity p : ℝ) * poissonWeight σ t p.val

private def pairedHeightWeight {χ : U} (σ t : ℝ) (p : Off(χ)) : ℝ :=
  t^2/(2*(σ-1/2)) *
      (highSiteWeight σ t p.val + highSiteWeight σ t ((offReflection χ) p).val)

private theorem pairedHeightWeight_nonneg {χ : U} {σ : ℝ} (hσ : 1 < σ)
    (t : ℝ) (p : Off(χ)) : 0 ≤ pairedHeightWeight σ t p := by
  have hp (z : Site χ) : 0 ≤ highSiteWeight σ t z :=
    mul_nonneg (Nat.cast_nonneg _) (poissonWeight_pos_of_site hσ t z).le
  unfold pairedHeightWeight
  exact mul_nonneg (div_nonneg (sq_nonneg _) (by linarith)) (add_nonneg (hp _) (hp _))

private theorem tendsto_pairedHeightWeight {χ : U} {σ : ℝ} (hσ : 1 < σ)
    (p : Off(χ)) : Tendsto (fun t ↦ pairedHeightWeight σ t p)
      (cocompact ℝ) (𝓝 (multiplicity p.val : ℝ)) := by
  let q := (offReflection χ) p
  have hm : multiplicity q.val = multiplicity p.val := multiplicity_reflection p.val
  have hr : q.val.val.re = 1 - p.val.val.re := by
    change (1-conj p.val.val).re = _
    simp
  have h := (((tendsto_height_sq_mul_poissonWeight σ p.val.val).const_mul (multiplicity p.val : ℝ)).add
    ((tendsto_height_sq_mul_poissonWeight σ q.val.val).const_mul (multiplicity q.val : ℝ))).div_const
    (2*(σ-1/2))
  have hgap : σ-(1/2:ℝ) ≠ 0 := by linarith
  have e : ((multiplicity p.val:ℝ)*(σ-p.val.val.re) + (multiplicity q.val:ℝ)*(σ-q.val.val.re)) /
      (2*(σ-1/2)) = (multiplicity p.val:ℝ) := by
    rw [hm, hr]
    apply (div_eq_iff (mul_ne_zero (by norm_num) hgap)).2
    ring
  rw [e] at h
  apply h.congr
  intro t
  change (_ * (t^2 * _) + _ * (t^2 * _)) / (2*(σ-1/2)) =
    t^2 / (2*(σ-1/2)) * ((multiplicity p.val:ℝ)*_ + (multiplicity q.val:ℝ)*_)
  ring

private theorem hasSum_pairedHeightWeight {χ : U} {σ t d : ℝ}
    (hσ : 1 < σ) (hd : HasSum (highSiteWeight (χ := χ) σ t) d) :
    HasSum (pairedHeightWeight (χ := χ) σ t)
      (t^2/(σ-1/2) * (d-centralTranslatedMass χ σ t)) := by
  let w (p : Off(χ)) := highSiteWeight σ t p.val
  let c := centralTranslatedMass χ σ t
  have s := hd.summable.tsum_subtype_add_tsum_subtype_compl {z : Site χ | z.val.re = 1/2}
  change c + (∑' z : Off(χ), w z) = ∑' z, highSiteWeight σ t z at s
  rw [hd.tsum_eq] at s
  have ho : HasSum w (d-c) := by
    have hh : Summable w := hd.summable.subtype _
    rw [← (show ∑' z, w z = d-c by linarith)]
    exact hh.hasSum
  have hr := ((offReflection χ).hasSum_iff).2 ho
  have hh := (ho.add hr).mul_left (t^2/(2*(σ-1/2)))
  have hgap : σ-(1/2:ℝ) ≠ 0 := by linarith
  have e : t^2/(2*(σ-1/2)) * ((d-c)+(d-c)) = t^2/(σ-1/2) * (d-c) := by
    field_simp
    ring
  rwa [e] at hh

/-- Along either tail of the height axis, the square-height normalized
arithmetic deficit converges to the full off-line multiplicity times the
distance from the critical line to the fixed abscissa. -/
theorem tendsto_highOrdinate_deficit (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U) (hχ : ∀ u, χ (τ u) = 1) (σ : ℝ) (hσ : 1 < σ) :
    Tendsto (fun t : ℝ ↦ ENNReal.ofReal
      (t^2 * (logDerivativeMass χ σ t - centralTranslatedMass χ σ t)))
      (cocompact ℝ) (𝓝 (ENNReal.ofReal (σ-1/2) * offLineCount χ)) := by
  have hl := tendsto_tsum_of_positive_nat_limits (l := cocompact ℝ)
    (fun p : Off(χ) ↦ multiplicity p.val) (fun p ↦ one_le_multiplicity p.val)
    (fun t p ↦ ENNReal.ofReal (pairedHeightWeight σ t p))
    (fun p ↦ by simpa using ENNReal.tendsto_ofReal (tendsto_pairedHeightWeight hσ p))
  have hgap : 0 < σ-(1/2:ℝ) := by linarith
  have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (σ-1/2)) hl
    (Or.inr ENNReal.ofReal_ne_top)
  apply h.congr
  intro t
  have hd := hasSum_logDerivativeMass τ hτ χ hχ σ t hσ
  have hs := hasSum_pairedHeightWeight hσ hd
  rw [← ENNReal.ofReal_tsum_of_nonneg (pairedHeightWeight_nonneg hσ t) hs.summable,
    hs.tsum_eq, ← ENNReal.ofReal_mul hgap.le]
  congr 1
  rw [← mul_assoc, mul_comm (σ-1/2) _, div_mul_cancel₀ _ hgap.ne']

/-- A fixed positive margin below twice the horizontal distance along arbitrarily
late samples excludes every off-line pair. The same equivalence applies along any
prescribed height path whose absolute value tends to infinity. -/
theorem criticalLine_iff_cofinal_highOrdinate_deficit
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U) (hχ : ∀ u, χ (τ u) = 1) (σ : ℝ) (hσ : 1 < σ)
    {A : Type*} {l : Filter A} [l.NeBot] (T : A → ℝ) (hT : Tendsto T l (cocompact ℝ)) :
    (∀ p : Site χ, p.val.re = 1/2) ↔ ∃ B : ℝ, B < 2*(σ-1/2) ∧
      ∃ᶠ i in l, (T i)^2 * (logDerivativeMass χ σ (T i) - centralTranslatedMass χ σ (T i)) ≤ B := by
  let D (i : A) := (T i)^2 * (logDerivativeMass χ σ (T i) - centralTranslatedMass χ σ (T i))
  have lim : Tendsto (fun i ↦ ENNReal.ofReal (D i)) l
      (𝓝 (ENNReal.ofReal (σ-1/2) * offLineCount χ)) :=
    (tendsto_highOrdinate_deficit τ hτ χ hχ σ hσ).comp hT
  have hc : 0 < σ-(1/2:ℝ) := by linarith
  constructor
  · intro hcentral
    have he : IsEmpty Off(χ) := ⟨fun z ↦ z.property (hcentral z.val)⟩
    have hz : offLineCount χ = 0 := tsum_empty
    rw [hz, mul_zero] at lim
    have hev := lim.eventually (eventually_lt_nhds (ENNReal.ofReal_pos.mpr hc))
    refine ⟨σ-1/2, by linarith, (hev.mono fun i hi ↦ ?_).frequently⟩
    exact ((ENNReal.ofReal_lt_ofReal_iff hc).1 hi).le
  · rintro ⟨B, hB, hfre⟩ p
    by_contra hbad
    have hpair : (2 : ℝ≥0∞) ≤ offLineCount χ :=
      (le_mul_of_one_le_right zero_le_two (show (1 : ℝ≥0∞) ≤ multiplicity p by
        exact_mod_cast one_le_multiplicity p)).trans (two_mul_multiplicity_le_offLineCount p hbad)
    have hstrong : ENNReal.ofReal B < ENNReal.ofReal (σ-1/2) * offLineCount χ := calc
      _ < ENNReal.ofReal (2*(σ-1/2)) := (ENNReal.ofReal_lt_ofReal_iff (by linarith)).2 hB
      _ = ENNReal.ofReal (σ-1/2) * 2 := by
        rw [mul_comm (2:ℝ), ENNReal.ofReal_mul hc.le]
        norm_num
      _ ≤ _ := mul_le_mul_of_nonneg_left hpair zero_le
    have hev := lim.eventually (eventually_gt_nhds hstrong)
    obtain ⟨i, hi, hhi⟩ := (hfre.and_eventually hev).exists
    exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal hi)) hhi

end RiemannMasullo.HeckePoisson
