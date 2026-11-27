module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.CutoffH2
public import RiemannMasullo.ForMathlib.Analysis.Fourier.Integrable
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

open Set MeasureTheory Filter
open scoped SchwartzMap Interval Topology FourierTransform Real

@[expose] public noncomputable section

namespace RiemannMasullo.WeakCardinal

local notation "D" => SchwartzMap.derivCLM ℂ ℂ
local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

private theorem integral_of_ae_hasDerivAt_ac {q q₁ : ℝ → ℂ} {u v : ℝ}
    (hac : AbsolutelyContinuousOnInterval q u v) (hd : ∀ᵐ x, HasDerivAt q (q₁ x) x)
    (hi : IntervalIntegrable q₁ volume u v) :
    (∫ x in u..v, q₁ x) = q v-q u := by
  have hL (L : ℂ →L[ℝ] ℝ) : L (∫ x in u..v, q₁ x) = L (q v-q u) := by
    rw [← L.intervalIntegral_comp_comm hi, map_sub]
    have hca := L.lipschitzWith.comp_absolutelyContinuousOnInterval hac
    change _ = (L ∘ q) v - (L ∘ q) u
    rw [← hca.integral_deriv_eq_sub]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hd] with x hx _
    exact (L.hasFDerivAt.comp_hasDerivAt x hx).deriv.symm
  exact Complex.ext (hL Complex.reCLM) (hL Complex.imCLM)


private theorem integral_zero_of_ae_hasDerivAt_ac {q q₁ : ℝ → ℂ}
    (hac : ∀ u v, AbsolutelyContinuousOnInterval q u v) (hd : ∀ᵐ x, HasDerivAt q (q₁ x) x)
    (hi : Integrable q₁) (hlim : Tendsto q (cocompact ℝ) (𝓝 0)) : (∫ x, q₁ x) = 0 := by
  have hb : Tendsto (fun t : ℝ ↦ -t) atTop atBot := tendsto_neg_atTop_atBot
  have hp : Tendsto q atTop (𝓝 0) := hlim.mono_left atTop_le_cocompact
  have hn : Tendsto (fun t : ℝ ↦ q (-t)) atTop (𝓝 0) := (hlim.mono_left atBot_le_cocompact).comp hb
  apply tendsto_nhds_unique (intervalIntegral_tendsto_integral hi hb tendsto_id)
  apply Tendsto.congr (f₁ := fun t : ℝ ↦ q t - q (-t)) ?_ ?_
  · intro t
    exact (integral_of_ae_hasDerivAt_ac (hac _ _) hd (hi.intervalIntegrable)).symm
  · simpa only [sub_zero] using hp.sub hn

/-- Fourier differentiation across a finite number of seams, using absolute continuity. -/
private theorem fourier_of_ac {q q₁ : ℝ → ℂ} (hq : Integrable q) (hi : Integrable q₁)
    (hac : ∀ u v, AbsolutelyContinuousOnInterval q u v) (hd : ∀ᵐ x, HasDerivAt q (q₁ x) x)
    (hlim : Tendsto q (cocompact ℝ) (𝓝 0)) (ξ : ℝ) :
    (𝓕 q₁) ξ = ((2*Real.pi*ξ : ℝ) : ℂ)*Complex.I*(𝓕 q) ξ := by
  let k (x : ℝ) : ℂ := 𝐞 (-(x*ξ))
  let c : ℂ := ((2*Real.pi*ξ : ℝ) : ℂ)*Complex.I
  have hk (x : ℝ) : HasDerivAt k (-c * k x) x := by
    have hd₀ : HasDerivAt (fun x : ℝ ↦ -(x*ξ)) (-ξ) x := by
      convert ((hasDerivAt_id x).mul_const ξ).neg using 1
      · rfl
      · simp
    convert (Real.hasDerivAt_fourierChar (-(x*ξ))).scomp x hd₀ using 1
    · rfl
    · dsimp [c, k]
      push_cast
      ring
  have hkcon : ContDiff ℝ 1 k := contDiff_one_iff_deriv.mpr
    ⟨fun x ↦ (hk x).differentiableAt, by
      rw [show deriv k = (fun x ↦ -c * k x) from funext (fun x ↦ (hk x).deriv)]
      exact continuous_const.mul (continuous_iff_continuousAt.mpr fun x ↦ (hk x).continuousAt)⟩
  have hkn (x : ℝ) : ‖k x‖ ≤ 1 := le_of_eq (Circle.norm_coe _)
  have hki : Integrable (fun x ↦ k x * q x) := hq.bdd_mul (c := 1) hkcon.continuous.aestronglyMeasurable (.of_forall hkn)
  have hkid : Integrable (fun x ↦ k x * q₁ x) := hi.bdd_mul (c := 1) hkcon.continuous.aestronglyMeasurable (.of_forall hkn)
  have hkc : IsBoundedUnder (· ≤ ·) (cocompact ℝ) (norm ∘ k) := isBoundedUnder_of ⟨1, hkn⟩
  have he := integral_zero_of_ae_hasDerivAt_ac (q := fun x ↦ k x*q x)
    (q₁ := fun x ↦ -c * (k x * q x) + k x * q₁ x)
    (fun u v ↦ hkcon.contDiffOn.absolutelyContinuousOnInterval.smul (hac u v))
    (hd.mono fun x hx ↦ by convert (hk x).mul hx using 1; ring)
    ((hki.const_mul (-c)).add hkid) (hkc.smul_tendsto_zero hlim)
  rw [integral_add (hki.const_mul (-c)) hkid, integral_const_mul] at he
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  change (∫ x, k x*q₁ x) = c * (∫ x, k x*q x)
  linear_combination he


private theorem fourier_sub_integrable {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (ξ : ℝ) :
    𝓕 (fun x ↦ f x-g x) ξ = 𝓕 f ξ - 𝓕 g ξ := by
  simp only [Real.fourier_eq, smul_sub]
  apply integral_sub
  · exact (VectorFourier.fourierIntegral_convergent_iff (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner ξ).mpr hf
  · exact (VectorFourier.fourierIntegral_convergent_iff (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner ξ).mpr hg

private theorem integrable_and_decay {b : ℝ → ℝ} {K : ℝ} (hb : Measurable b)
    (hK : ∀ x, |b x| ≤ K) (φ : 𝓢(ℝ, ℂ)) :
    Integrable (fun x ↦ b x • φ x) ∧ Tendsto (fun x ↦ b x • φ x) (cocompact ℝ) (𝓝 0) := by
  have hbn : ∀ x, ‖b x‖ ≤ K := hK
  exact ⟨φ.integrable.bdd_smul K hb.aestronglyMeasurable (.of_forall hbn),
    (isBoundedUnder_of (f := cocompact ℝ) ⟨K, hbn⟩).smul_tendsto_zero φ.tendsto_cocompact⟩

/-- On the Schwartz graph the bounded physical coefficient and the true Plancherel
transform satisfy the full weighted Fourier endpoint relation. -/
theorem exists_fourier_graph_scaledCutoffQuotient (w : ℝ) {R : ℝ} (hR : 0 < R) (f : 𝓢(ℝ, ℂ)) :
    ∃ k : H, (k : ℝ → ℂ) =ᵐ[volume] (fun ξ ↦ (1+(2*Real.pi*ξ)^2) •
        (𝓕 (scaledCutoffQuotientL2 w hR (f.toLp 2 volume)) : H) ξ) ∧
      ‖k‖ ≤ ((9/8)/R + 2/R^2 + 6/R^3) * ‖(graphH2 f).toLp 2 volume‖ := by
  let a := scaledCutoffQuotient w R
  let b (x : ℝ) := cutoffQuotientPrime ((x-w)/R)/R^2
  let c (x : ℝ) := cutoffQuotientSecond ((x-w)/R)/R^3
  let q (x : ℝ) := a x • f x
  let q₁ (x : ℝ) := a x • (D f) x + b x • f x
  let q₂ (x : ℝ) := (a x • (D (D f)) x + b x • (D f) x) + (b x • (D f) x + c x • f x)
  have hq (x : ℝ) : HasDerivAt q (q₁ x) x := (hasDerivAt_scaledCutoffQuotient w R x).smul (f.hasDerivAt x)
  have heq : deriv q = q₁ := funext (fun x ↦ (hq x).deriv)
  have haeq : ∀ᵐ x, HasDerivAt q₁ (q₂ x) x := (ae_hasDerivAt_scaledCutoffQuotientPrime w hR).mono
    (fun x hx ↦ ((hasDerivAt_scaledCutoffQuotient w R x).smul ((D f).hasDerivAt x)).add (hx.smul (f.hasDerivAt x)))
  have hma : Measurable a := (continuous_iff_continuousAt.mpr
    (fun x ↦ (hasDerivAt_scaledCutoffQuotient w R x).continuousAt)).measurable
  have hmb : Measurable b :=
    ((continuous_cutoffQuotientPrime.comp ((continuous_id.sub continuous_const).div_const R)).div_const (R^2)).measurable
  have hsec : Measurable cutoffQuotientSecond := by
    unfold cutoffQuotientSecond
    apply Measurable.ite (measurableSet_le continuous_abs.measurable measurable_const) <;> fun_prop
  have hmc : Measurable c := (hsec.comp ((measurable_id.sub measurable_const).div_const R)).div_const (R^3)
  have hb (x : ℝ) : |b x| ≤ 2/R^2 := by
    dsimp only [b]
    rw [abs_div, abs_of_pos (sq_pos_of_pos hR)]
    exact div_le_div_of_nonneg_right (abs_cutoffQuotientPrime_le _) (sq_nonneg _)
  have hc (x : ℝ) : |c x| ≤ 6/R^3 := by
    dsimp only [c]
    rw [abs_div, abs_of_pos (pow_pos hR _)]
    exact div_le_div_of_nonneg_right (abs_cutoffQuotientSecond_le _) (pow_nonneg hR.le _)
  have A := integrable_and_decay hma (scaledCutoffQuotient_value_bound hR w)
  have B := integrable_and_decay hmb hb
  have C := integrable_and_decay hmc hc
  have i₀ : Integrable q := (A f).1
  have i₁ : Integrable q₁ := (A (D f)).1.add (B f).1
  have i₂ : Integrable q₂ := ((A (D (D f))).1.add (B (D f)).1).add ((B (D f)).1.add (C f).1)
  have d₁ : Tendsto q₁ (cocompact ℝ) (𝓝 0) := by
    simpa only [add_zero] using (A (D f)).2.add (B f).2
  have ac (u v : ℝ) : AbsolutelyContinuousOnInterval q₁ u v := by
    rw [← heq]
    exact absolutelyContinuousOnInterval_deriv_scaledCutoffQuotient_smul w R u v f
  have raw (ξ : ℝ) : 𝓕 (fun x ↦ q x - q₂ x) ξ = (1+(2*Real.pi*ξ)^2) • (𝓕 q) ξ := by
    rw [fourier_sub_integrable i₀ i₂, fourier_of_ac i₁ i₂ ac haeq d₁]
    have hf₁ := Real.fourier_deriv i₀ (fun x ↦ (hq x).differentiableAt) (heq.symm ▸ i₁)
    rw [heq] at hf₁
    rw [hf₁]
    dsimp only
    simp only [smul_eq_mul, Complex.real_smul]
    push_cast
    linear_combination -((2*(Real.pi:ℂ)*(ξ:ℂ))^2 * (𝓕 q) ξ) * Complex.I_sq
  obtain ⟨g, hg, hnorm⟩ := exists_graphH2_scaledCutoffQuotient w hR f
  change (g : ℝ → ℂ) =ᵐ[volume] fun x ↦ q x - deriv (deriv q) x at hg
  rw [heq] at hg
  have heg : (g : ℝ → ℂ) =ᵐ[volume] fun x ↦ q x-q₂ x :=
    hg.trans (haeq.mono fun x hx ↦ congrArg (q x - ·) hx.deriv)
  let t := scaledCutoffQuotientL2 w hR (f.toLp 2 volume)
  have het : (t : ℝ → ℂ) =ᵐ[volume] q := by
    filter_upwards [scaledCutoffQuotientL2_apply_ae w hR (f.toLp 2 volume), f.coeFn_toLp 2 volume]
      with x ht hf using ht.trans (congrArg _ hf)
  refine ⟨𝓕 g, ?_, (Lp.norm_fourier_eq g).le.trans hnorm⟩
  have hiq : Integrable (fun x ↦ q x - q₂ x) := i₀.sub i₂
  filter_upwards [fourier_L2_coeFn_of_integrable g (hiq.congr heg.symm),
    fourier_L2_coeFn_of_integrable t (i₀.congr het.symm)] with ξ hk ht
  change _ = _ • (𝓕 t : H) ξ
  rw [hk, ht, Real.fourier_congr_ae heg, Real.fourier_congr_ae het, raw]

end RiemannMasullo.WeakCardinal
