module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.BesselCardinal.Cutoff
public import Mathlib.Analysis.Fourier.LpSpace
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Tactic

/-! # The explicit cutoff on the order-two graph norm -/

open Set Filter MeasureTheory
open scoped FourierTransform SchwartzMap Real Topology

@[expose] public noncomputable section

namespace RiemannMasullo.WeakCardinal

local notation "D" => SchwartzMap.derivCLM ℂ ℂ
local notation "H" => Lp ℂ 2 (volume : Measure ℝ)

/-- The operator `1-∂²` on Schwartz functions. Its angular Fourier symbol is
`1+(2πξ)²` for Mathlib's Fourier transform. -/
def graphH2 (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) := f - D (D f)

private theorem fourier_schwartzDeriv (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕 (D f)) x = ((2*Real.pi*x : ℝ) : ℂ) * Complex.I * (𝓕 f) x := by
  have hd : ⇑(D f) = deriv f := rfl
  have hf := Real.fourier_deriv f.integrable f.differentiable (hd ▸ (D f).integrable)
  simp only [SchwartzMap.fourier_coe, hd, hf, smul_eq_mul]
  push_cast
  ring

theorem fourier_graphH2 (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    (𝓕 (graphH2 f)) x = (((1+(2*Real.pi*x)^2 : ℝ) : ℂ)) * (𝓕 f) x := by
  rw [graphH2, FourierTransform.fourier_sub]
  change (𝓕 f) x - (𝓕 (D (D f))) x = _
  rw [fourier_schwartzDeriv, fourier_schwartzDeriv]
  push_cast
  have hI := Complex.I_sq
  linear_combination -((2*(Real.pi:ℂ)*(x:ℂ))^2 * (𝓕 f) x) * hI

private theorem schwartz_norm_fourier (f : 𝓢(ℝ, ℂ)) :
    ‖(𝓕 f).toLp 2 volume‖ = ‖f.toLp 2 volume‖ := by
  rw [← SchwartzMap.toLp_fourier_eq, Lp.norm_fourier_eq]

/-- Plancherel for the unscaled physical graph norm. The second estimate retains the factor two. -/
theorem schwartz_norm_and_twice_deriv_le_graphH2 (f : 𝓢(ℝ, ℂ)) :
    ‖f.toLp 2 volume‖ ≤ ‖(graphH2 f).toLp 2 volume‖ ∧
      2 * ‖(D f).toLp 2 volume‖ ≤ ‖(graphH2 f).toLp 2 volume‖ := by
  have hg (x : ℝ) : ‖(𝓕 (graphH2 f)) x‖ = (1+(2*Real.pi*x)^2) * ‖(𝓕 f) x‖ := by
    rw [fourier_graphH2, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hd (x : ℝ) : ‖(𝓕 (D f)) x‖ = |2*Real.pi*x| * ‖(𝓕 f) x‖ := by
    rw [fourier_schwartzDeriv, norm_mul, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
  rw [← schwartz_norm_fourier f, ← schwartz_norm_fourier (graphH2 f), ← schwartz_norm_fourier (D f)]
  constructor
  · apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(𝓕 f).coeFn_toLp 2 volume, (𝓕 (graphH2 f)).coeFn_toLp 2 volume] with x hf hx
    rw [hf, hx, hg]
    exact le_mul_of_one_le_left (norm_nonneg _) (by nlinarith [sq_nonneg (2*Real.pi*x)])
  · have hs : ‖(2:ℝ) • (𝓕 (D f)).toLp 2 volume‖ ≤ ‖(𝓕 (graphH2 f)).toLp 2 volume‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [Lp.coeFn_smul (2:ℝ) ((𝓕 (D f)).toLp 2 volume),
        (𝓕 (D f)).coeFn_toLp 2 volume, (𝓕 (graphH2 f)).coeFn_toLp 2 volume] with x hs hd' hg'
      rw [hs, Pi.smul_apply, hd', hg', norm_smul, Real.norm_of_nonneg (by norm_num), hd, hg, ← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      nlinarith [sq_nonneg (|2*Real.pi*x|-1), sq_abs (2*Real.pi*x)]
    simpa only [norm_smul, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 2)] using hs


theorem boundedRealMultiplier_memLp (a : ℝ → ℝ) (ha : Measurable a) {K : ℝ}
    (h : ∀ x, |a x| ≤ K) (f : H) : MemLp (fun x ↦ a x • f x) 2 volume := by
  refine (Lp.memLp f).of_le_mul (c := K) (ha.aestronglyMeasurable.smul (Lp.aestronglyMeasurable f)) ?_
  filter_upwards with x
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)

/-- Multiplication on complex `L²` by a bounded measurable real coefficient. -/
def boundedRealMultiplier (a : ℝ → ℝ) (ha : Measurable a)
    {K : ℝ} (h : ∀ x, |a x| ≤ K) : H →L[ℂ] H := by
  let hmem := boundedRealMultiplier_memLp a ha h
  let T : H →ₗ[ℂ] H := {
    toFun := fun f ↦ (hmem f).toLp _
    map_add' := fun f g ↦ by
      apply Lp.ext
      filter_upwards [(hmem (f+g)).coeFn_toLp, Lp.coeFn_add f g, Lp.coeFn_add
        ((hmem f).toLp _) ((hmem g).toLp _), (hmem f).coeFn_toLp, (hmem g).coeFn_toLp]
        with x h₁ h₂ h₃ h₄ h₅
      simp only [h₁, h₂, h₃, Pi.add_apply, h₄, h₅, smul_add]
    map_smul' := fun k f ↦ by
      apply Lp.ext
      filter_upwards [(hmem (k • f)).coeFn_toLp, Lp.coeFn_smul k f, Lp.coeFn_smul k ((hmem f).toLp _),
        (hmem f).coeFn_toLp] with x h₁ h₂ h₃ h₄
      simp only [h₁, h₂, h₃, Pi.smul_apply, h₄, RingHom.id_apply]
      exact smul_comm _ _ _ }
  apply T.mkContinuous K
  intro f
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(hmem f).coeFn_toLp] with x hx
  change ‖((hmem f).toLp _ : H) x‖ ≤ _
  rw [hx, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)

theorem boundedRealMultiplier_apply_ae (a : ℝ → ℝ) (ha : Measurable a)
    {K : ℝ} (h : ∀ x, |a x| ≤ K) (f : H) :
    (boundedRealMultiplier a ha h f : ℝ → ℂ) =ᵐ[volume] fun x ↦ a x • f x :=
  (boundedRealMultiplier_memLp a ha h f).coeFn_toLp

theorem boundedRealMultiplier_norm_le (a : ℝ → ℝ) (ha : Measurable a)
    {K : ℝ} (h : ∀ x, |a x| ≤ K) (f : H) :
    ‖boundedRealMultiplier a ha h f‖ ≤ K * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [boundedRealMultiplier_apply_ae a ha h f] with x hx
  rw [hx, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (h x) (norm_nonneg _)

private theorem bounded_smul_schwartz (a : ℝ → ℝ) (ha : Measurable a) {K : ℝ}
    (h : ∀ x, |a x| ≤ K) (f : 𝓢(ℝ, ℂ)) :
    ∃ g : H, (g : ℝ → ℂ) =ᵐ[volume] (fun x ↦ a x • f x) ∧ ‖g‖ ≤ K * ‖f.toLp 2 volume‖ := by
  refine ⟨_, ?_, boundedRealMultiplier_norm_le a ha h (f.toLp 2 volume)⟩
  filter_upwards [boundedRealMultiplier_apply_ae a ha h (f.toLp 2 volume), f.coeFn_toLp 2 volume]
    with x hg hf using hg.trans (congrArg _ hf)

/-- The other interpolation endpoint acts on the full unweighted space. -/
def scaledCutoffQuotientL2 (w : ℝ) {R : ℝ} (hR : 0 < R) : H →L[ℂ] H :=
  boundedRealMultiplier _ (continuous_iff_continuousAt.mpr
    (fun x ↦ (hasDerivAt_scaledCutoffQuotient w R x).continuousAt)).measurable
    (scaledCutoffQuotient_value_bound hR w)

theorem scaledCutoffQuotientL2_apply_ae (w : ℝ) {R : ℝ} (hR : 0 < R) (f : H) :
    (scaledCutoffQuotientL2 w hR f : ℝ → ℂ) =ᵐ[volume] fun x ↦ scaledCutoffQuotient w R x • f x :=
  boundedRealMultiplier_apply_ae _ _ _ _

theorem scaledCutoffQuotientL2_norm_le (w : ℝ) {R : ℝ} (hR : 0 < R) :
    ‖scaledCutoffQuotientL2 w hR‖ ≤ (9/8)/R := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact boundedRealMultiplier_norm_le _ _ _


/-- The first derivative of the product is absolutely continuous on each finite interval.
This identifies its almost-everywhere derivative with its weak derivative across both seams. -/
theorem absolutelyContinuousOnInterval_deriv_scaledCutoffQuotient_smul
    (w R u v : ℝ) (f : 𝓢(ℝ, ℂ)) :
    AbsolutelyContinuousOnInterval (deriv (fun x : ℝ ↦ scaledCutoffQuotient w R x • f x)) u v := by
  have ht : ContDiff ℝ 1 (fun x : ℝ ↦ (x-w)/R) := (contDiff_id.sub contDiff_const).div_const R
  have ha : ContDiff ℝ 1 (scaledCutoffQuotient w R) :=
    (contDiff_cutoffQuotient.comp ht).div_const R
  have hb := lipschitzWith_cutoffQuotientPrime.comp_absolutelyContinuousOnInterval
    (ht.contDiffOn.absolutelyContinuousOnInterval (a := u) (b := v))
  have hb' : AbsolutelyContinuousOnInterval (fun x : ℝ ↦ cutoffQuotientPrime ((x-w)/R)/R^2) u v := by
    simpa only [Function.comp_apply, div_eq_inv_mul] using hb.const_mul (R^2)⁻¹
  have hq : deriv (fun x : ℝ ↦ scaledCutoffQuotient w R x • f x) =
      (fun x ↦ scaledCutoffQuotient w R x • (D f) x + (cutoffQuotientPrime ((x-w)/R)/R^2) • f x) :=
    funext fun x ↦ ((hasDerivAt_scaledCutoffQuotient w R x).smul (f.hasDerivAt x)).deriv
  rw [hq]
  exact (ha.contDiffOn.absolutelyContinuousOnInterval.smul
    ((D f).smooth 1).contDiffOn.absolutelyContinuousOnInterval).add
    (hb'.smul (f.smooth 1).contDiffOn.absolutelyContinuousOnInterval)


/-- Multiplication of a complex Schwartz function by the explicit cutoff coefficient,
in the physical graph norm of `1-∂²`. The output is represented by its actual
almost-everywhere second derivative, with the normalization used by the centered moment. -/
theorem exists_graphH2_scaledCutoffQuotient (w : ℝ) {R : ℝ} (hR : 0 < R) (f : 𝓢(ℝ, ℂ)) :
    ∃ g : H, (g : ℝ → ℂ) =ᵐ[volume] (fun x ↦ scaledCutoffQuotient w R x • f x -
      deriv (deriv (fun y : ℝ ↦ scaledCutoffQuotient w R y • f y)) x) ∧
      ‖g‖ ≤ ((9/8)/R + 2/R^2 + 6/R^3) * ‖(graphH2 f).toLp 2 volume‖ := by
  let a := scaledCutoffQuotient w R
  let b (x : ℝ) := cutoffQuotientPrime ((x-w)/R)/R^2
  let c (x : ℝ) := cutoffQuotientSecond ((x-w)/R)/R^3
  let q (x : ℝ) := a x • f x
  have hq1 : deriv q = (fun x ↦ a x • (D f) x + b x • f x) := funext fun x ↦
    ((hasDerivAt_scaledCutoffQuotient w R x).smul (f.hasDerivAt x)).deriv
  have hq2 : ∀ᵐ x : ℝ, deriv (deriv q) x =
      (a x • (D (D f)) x + b x • (D f) x) + (b x • (D f) x + c x • f x) := by
    filter_upwards [ae_hasDerivAt_scaledCutoffQuotientPrime w hR] with x hx
    rw [hq1]
    exact (((hasDerivAt_scaledCutoffQuotient w R x).smul ((D f).hasDerivAt x)).add
      (hx.smul (f.hasDerivAt x))).deriv
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
  obtain ⟨u, hu, Nu⟩ := bounded_smul_schwartz a hma (K := (9/8)/R)
    (scaledCutoffQuotient_value_bound hR w) (graphH2 f)
  obtain ⟨v, hv, Nv⟩ := bounded_smul_schwartz b hmb (K := 2/R^2) hb (D f)
  obtain ⟨z, hz, Nz⟩ := bounded_smul_schwartz c hmc (K := 6/R^3) hc f
  refine ⟨(u-v)-(v+z), ?_, ?_⟩
  · filter_upwards [Lp.coeFn_sub (u-v) (v+z), Lp.coeFn_sub u v, Lp.coeFn_add v z, hu, hv, hz,
      hq2] with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
    change ((u-v)-(v+z)) x = a x • f x - deriv (deriv q) x
    rw [h₁, Pi.sub_apply, h₂, Pi.sub_apply, h₃, Pi.add_apply, h₄, h₅, h₆, h₇]
    change a x • (f x - (D (D f)) x) - b x • (D f) x - (b x • (D f) x + c x • f x) = _
    rw [smul_sub]
    abel
  · obtain ⟨hf₀, hf₁⟩ := schwartz_norm_and_twice_deriv_le_graphH2 f
    calc
      _ ≤ (‖u‖+‖v‖)+(‖v‖+‖z‖) :=
        (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (norm_add_le _ _))
      _ ≤ (((9/8)/R)*‖(graphH2 f).toLp 2 volume‖ + (2/R^2)*‖(D f).toLp 2 volume‖) +
          ((2/R^2)*‖(D f).toLp 2 volume‖ + (6/R^3)*‖f.toLp 2 volume‖) :=
        add_le_add (add_le_add Nu Nv) (add_le_add Nv Nz)
      _ = ((9/8)/R)*‖(graphH2 f).toLp 2 volume‖ + (2/R^2)*(2*‖(D f).toLp 2 volume‖) +
          (6/R^3)*‖f.toLp 2 volume‖ := by ring
      _ ≤ ((9/8)/R)*‖(graphH2 f).toLp 2 volume‖ + (2/R^2)*‖(graphH2 f).toLp 2 volume‖ +
          (6/R^3)*‖(graphH2 f).toLp 2 volume‖ := by gcongr
      _ = _ := by ring

/-- The genuine order-two graph bound for the radius-six centered cutoff. -/
theorem exists_graphH2_scaledCutoffQuotient_six (w : ℝ) (f : 𝓢(ℝ, ℂ)) :
    ∃ g : H, (g : ℝ → ℂ) =ᵐ[volume] (fun x ↦ scaledCutoffQuotient w 6 x • f x -
      deriv (deriv (fun y : ℝ ↦ scaledCutoffQuotient w 6 y • f y)) x) ∧
      ‖g‖ ≤ (13/48) * ‖(graphH2 f).toLp 2 volume‖ := by
  simpa only [radius_six_multiplier_constant] using exists_graphH2_scaledCutoffQuotient w
    (R := 6) (by norm_num) f

end RiemannMasullo.WeakCardinal
