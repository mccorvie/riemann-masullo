module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ExteriorPrimeTrace
import Mathlib.Tactic

/-! # Horizontal Abel residues of the signed exterior discrepancy -/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.RationalWidthLoss

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Z" => {ρ : ℂ // 0 < MeromorphicOn.divisor completedRiemannZeta univ ρ}
local notation "w(" ρ ")" => ((ρ : Z).val - (1/2 : ℂ))
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  (H : ℝ → ℂ) (logIdeleClassNorm ℚ x)
local notation "shift(" H ", " y ")" => (fun x ↦ H (x-y))
local notation "L(" F ", " z ")" => (∫ y in Ioi (0:ℝ), (F : ℝ → ℂ) y * Complex.exp (-((z:ℂ)*y)))
local notation "weighted(" c ", " F ")" => (fun y : ℝ ↦ (Real.exp (-(c:ℝ)*y):ℂ)*(F : ℝ → ℂ) y)

private theorem laplace_closed_half_plane_bound {F : ℝ → ℂ} {c : ℝ}
    (hF : IntegrableOn weighted(c,F) (Ioi 0)) {z : ℂ} (hz : c ≤ z.re) :
    IntegrableOn (fun y : ℝ ↦ F y * Complex.exp (-(z*y))) (Ioi 0) ∧
      ‖L(F,z)‖ ≤ ∫ y in Ioi (0:ℝ), ‖weighted(c,F) y‖ := by
  let d (y : ℝ) := Complex.exp (((c:ℂ)-z)*y)
  have hd : Continuous d := by unfold d; fun_prop
  have hb : ∀ᵐ y ∂volume.restrict (Ioi (0:ℝ)), ‖d y‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
    change ‖Complex.exp _‖ ≤ 1
    rw [Complex.norm_exp,Real.exp_le_one_iff]
    simp only [Complex.mul_re,Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hz) hy.le
  have he (y : ℝ) : d y * weighted(c,F) y = F y * Complex.exp (-(z*y)) := by
    dsimp only [d]
    rw [← mul_assoc,Complex.ofReal_exp,← Complex.exp_add,mul_comm]
    push_cast
    congr 2
    ring
  refine ⟨(hF.bdd_mul hd.aestronglyMeasurable hb).congr (ae_of_all _ he),?_⟩
  apply norm_integral_le_of_norm_le hF.norm
  filter_upwards [hb] with y hy
  rw [← he,norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) hy

private theorem tendsto_abel_zero_of_integrable {F : ℝ → ℂ} {c : ℝ} {w : ℂ}
    (hF : IntegrableOn weighted(c,F) (Ioi 0)) (hw : c ≤ w.re) :
    Tendsto (fun δ : ℝ ↦ (δ:ℂ)*L(F,w+δ)) (𝓝[>] 0) (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  let M := ∫ y in Ioi (0:ℝ), ‖weighted(c,F) y‖
  have ht : Tendsto (fun δ : ℝ ↦ δ*M) (𝓝[>] 0) (𝓝 0) := by
    have ht : Tendsto (fun δ : ℝ ↦ δ*M) (𝓝 0) (𝓝 (0*M)) := (continuous_id.mul continuous_const).tendsto 0
    simpa only [zero_mul] using ht.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ ht
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  have hz : c ≤ (w+(δ:ℂ)).re := by rw [Complex.add_re,Complex.ofReal_re]; linarith
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ]
  exact mul_le_mul_of_nonneg_left (laplace_closed_half_plane_bound hF hz).2 hδ.le

/-- A prescribed test can have many active zero frequencies. Wherever its
polar-corrected exterior error has absolutely convergent Laplace transform to the
right of `c ≥ a/2`, horizontal Abel limits recover its signed missing coefficients
on and to the right of `c`, including the boundary. -/
theorem exterior_abel_residue {a l u c : ℝ} (ha : 0 < a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hb : tsupport H ⊆ Icc l u)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,H)) (hc : a/2 ≤ c) :
    let E := fun y : ℝ ↦ exteriorStripTrace ha.le φ y + V * rationalFirstPrimeSum shift(H,y) -
      V * bilateralLaplace shift(H,y) (1/2)
    (∀ σ, c < σ → IntegrableOn weighted(σ,E) (Ioi 0)) → ∀ ρ : Z, c ≤ w(ρ).re →
      Tendsto (fun δ : ℝ ↦ (δ:ℂ) * L(E,w(ρ)+δ)) (𝓝[>] 0)
        (𝓝 (-(V * ((omittedOrder a ρ : ℂ) * bilateralLaplace H w(ρ))))) := by
  intro E hE ρ hρ
  let S := omittedMellinTrace a H
  let R (y : ℝ) := E y + S y
  have hR : IntegrableOn weighted(a/2,R) (Ioi 0) := by
    apply (integrable_exterior_first_add_omitted_sub_pole ha hl H hH hb φ hφ).congr
    filter_upwards with y
    dsimp only [R,E,S]
    rw [show -(a/2)*y = -a*y/2 by ring]; ring
  have hSi (σ : ℝ) (hσ : c < σ) : IntegrableOn weighted(σ,S) (Ioi 0) := by
    have hr := (laplace_closed_half_plane_bound hR (z := (σ:ℂ)) (hc.trans hσ.le)).1
    apply (hr.sub (hE σ hσ)).congr
    filter_upwards with y
    dsimp only [Pi.sub_apply,R]
    rw [show -((σ:ℂ)*y) = ((-σ*y:ℝ):ℂ) by push_cast; ring,← Complex.ofReal_exp]
    ring
  have hs := tendsto_omitted_laplace_residue a H hH (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hb)
    (fun _ hx ↦ hl.trans_le (hb hx).1) (c := c) (fun σ hσ ↦ (hSi σ hσ).norm.congr (by
      filter_upwards with y
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),mul_comm])) ρ hρ
  have hlim := tendsto_abel_zero_of_integrable hR (hc.trans hρ)
  apply (by simpa only [zero_sub] using hlim.sub hs : Tendsto _ _ _).congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  change 0 < δ at hδ
  let z := w(ρ)+(δ:ℂ)
  have hz : c < z.re := by change c < (w(ρ)+(δ:ℂ)).re; rw [Complex.add_re,Complex.ofReal_re]; linarith
  have hr := (laplace_closed_half_plane_bound (z := z) hR (hc.trans hz.le)).1
  have hs' := (laplace_closed_half_plane_bound (z := z) (hSi z.re hz) (le_refl z.re)).1
  change (δ:ℂ)*L(R,z) - δ*L(S,z) = δ*L(E,z)
  rw [← mul_sub,← integral_sub hr hs']
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro y _
  dsimp only [Pi.sub_apply,R]; ring

/-- Above the detector exponent, the half-planes of absolute Laplace
convergence of the physical error are determined exactly by the nonzero
missing coefficients strictly to their right. -/
theorem exterior_laplace_halfPlane_iff {a l u c : ℝ} (ha : 0 < a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hb : tsupport H ⊆ Icc l u)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,H)) (hc : a/2 ≤ c) :
    let E := fun y : ℝ ↦ exteriorStripTrace ha.le φ y + V * rationalFirstPrimeSum shift(H,y) -
      V * bilateralLaplace shift(H,y) (1/2)
    (∀ σ, c < σ → IntegrableOn weighted(σ,E) (Ioi 0)) ↔
      ∀ ρ : Z, c < w(ρ).re → 0 < omittedOrder a ρ → bilateralLaplace H w(ρ) = 0 := by
  intro E
  constructor
  · intro hE ρ hρ hm
    let σ := (c+w(ρ).re)/2
    have h₁ := exterior_abel_residue ha hl H hH hb φ hφ hc hE ρ hρ.le
    have h₂ := tendsto_abel_zero_of_integrable (hE σ (by dsimp only [σ]; linarith only [hρ]))
      (show σ ≤ w(ρ).re by dsimp only [σ]; linarith only [hρ])
    have hz := neg_eq_zero.mp (tendsto_nhds_unique h₁ h₂)
    exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left normOneVolume_ne_zero)).resolve_left
      (by exact_mod_cast hm.ne')
  · intro hsite σ hσ
    have hs := integrable_omitted_above_active_sites a H hH
      (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hb) (fun _ hx ↦ hl.trans_le (hb hx).1) hσ hsite
    let R (y : ℝ) := exteriorStripTrace ha.le φ y + V*rationalFirstPrimeSum shift(H,y) +
      omittedMellinTrace a H y - V*bilateralLaplace shift(H,y) (1/2)
    have hR : IntegrableOn weighted(a/2,R) (Ioi 0) := by
      have hw (y : ℝ) : -(a/2)*y = -a*y/2 := by ring
      simpa only [R,hw] using
        integrable_exterior_first_add_omitted_sub_pole ha hl H hH hb φ hφ
    have hr := (laplace_closed_half_plane_bound hR (z := (σ:ℂ)) (hc.trans hσ.le)).1
    apply (hr.sub hs).congr
    filter_upwards with y
    dsimp only [Pi.sub_apply,R,E]
    rw [show -((σ:ℂ)*y) = ((-σ*y:ℝ):ℂ) by push_cast; ring,← Complex.ofReal_exp]
    ring

/-- For an arbitrary fixed test, every active zero on its rightmost active
vertical line can be read separately from the physical trace. Other active zeros
on the same line or approaching it from below are allowed. -/
theorem exterior_rightmost_abel_residue {a l u : ℝ} (ha : 0 < a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hb : tsupport H ⊆ Icc l u)
    (φ : BruhatCompactSupport Cℚ) (hφ : radial(φ,H)) (ρ : Z) (hc : a/2 ≤ w(ρ).re)
    (hsite : ∀ z : Z, w(ρ).re < w(z).re → 0 < omittedOrder a z → bilateralLaplace H w(z) = 0) :
    let E := fun y : ℝ ↦ exteriorStripTrace ha.le φ y + V * rationalFirstPrimeSum shift(H,y) -
      V * bilateralLaplace shift(H,y) (1/2)
    Tendsto (fun δ : ℝ ↦ (δ:ℂ) * L(E,w(ρ)+δ)) (𝓝[>] 0)
      (𝓝 (-(V * ((omittedOrder a ρ : ℂ) * bilateralLaplace H w(ρ))))) := by
  exact exterior_abel_residue ha hl H hH hb φ hφ hc
    ((exterior_laplace_halfPlane_iff ha hl H hH hb φ hφ hc).mpr hsite) ρ le_rfl

end RiemannMasullo.RationalWidthLoss
