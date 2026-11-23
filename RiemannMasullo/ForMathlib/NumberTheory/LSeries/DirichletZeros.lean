module

import RiemannMasullo.External.Grh.Lemmas.ZeroFreeDiskLogDeriv
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.Analysis.Meromorphic.Order
/-!
# A zero for odd Dirichlet characters modulo five

Mathlib's Hurwitz theta kernel gives subquadratic logarithmic growth for the
completed L-function. Neal Patel's vendored zero-free disk estimate then forces
a zero-free completed L-function to have constant logarithmic derivative.
The Dirichlet-series expansion and the archimedean factor exclude that case.
-/

noncomputable section

namespace RiemannMasullo

section
open Complex Filter Set Metric
open scoped Topology
private theorem subquadratic_zeroFree_logDeriv_constant (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hn : ∀ z, f z ≠ 0)
    (B : ℝ → ℝ) (hB : Tendsto (fun R ↦ B R / R^2) atTop (𝓝 0))
    (hbound : ∀ᶠ R : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ 6 * R → ‖f z‖ ≤ Real.exp (B R)) :
    ∀ z w, logDeriv f z = logDeriv f w := by
  have hd : Differentiable ℂ (logDeriv f) := hf.deriv.div hf hn
  apply is_const_of_deriv_eq_zero hd
  intro c
  have hc := norm_pos_iff.mpr (hn c)
  have hh : ∀ᶠ R : ℝ in atTop, ‖deriv (logDeriv f) c‖ ≤
      8 * (B R - Real.log ‖f c‖ + 1) / R^2 := by
    filter_upwards [hbound, eventually_gt_atTop (0 : ℝ), eventually_ge_atTop ‖c‖] with R hR hRp hcR
    let g (w : ℂ) := f (c + (R : ℂ) * w)
    have hg : Differentiable ℂ g := hf.comp ((differentiable_const c).add ((differentiable_const (R : ℂ)).mul differentiable_id))
    have hgB (w : ℂ) (hw : w ∈ ball (0 : ℂ) 5) : ‖g w‖ ≤ Real.exp (B R) := by
      apply hR
      have hw' : ‖w‖ < 5 := by simpa using hw
      calc ‖c + (R : ℂ) * w‖ ≤ ‖c‖ + ‖(R : ℂ) * w‖ := norm_add_le _ _
           _ ≤ 6 * R := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp]; nlinarith
    have hscale (w : ℂ) : logDeriv g w = (R : ℂ) * logDeriv f (c + R*w) := by
      have hder := (hf (c + R*w)).hasDerivAt.comp w
        (((hasDerivAt_id w).const_mul (R : ℂ)).const_add c)
      rw [logDeriv_apply, logDeriv_apply, show deriv g w = _ from hder.deriv]
      ring
    have h₁ := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRp (hd.diffContOnCl (s := ball c R))
      (C := 8 * (B R - Real.log ‖f c‖ + 1) / R) (fun z hz ↦ ?_)
    · calc
        _ ≤ _ := h₁
        _ = _ := by ring
    · let w : ℂ := (z-c) / R
      have hR₀ : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hRp.ne'
      have hw : ‖w‖ = 1 := by
        rw [show ‖w‖ = ‖z-c‖ / ‖(R : ℂ)‖ from norm_div _ _,
          ← dist_eq_norm, mem_sphere.mp hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp,
          div_self hRp.ne']
      have hw' : w ∈ closedBall (0 : ℂ) 3 := by simp [hw]
      have hl := External.Grh.norm_logDeriv_le_on_inner_ball (fun z _ ↦ hg.analyticAt z) (fun u _ ↦ hn _)
        hgB hw'
      have hcz : c + (R : ℂ) * w = z := by dsimp [w]; field_simp; ring
      have h0 : g 0 = f c := by simp [g]
      change ‖logDeriv g w‖ ≤ 8 * (Real.log (Real.exp (B R) / ‖g 0‖) + 1) at hl
      rw [hscale, hcz, h0, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRp,
        Real.log_div (Real.exp_pos _).ne' hc.ne', Real.log_exp] at hl
      exact (le_div_iff₀ hRp).mpr (by linarith)
  have h₀ : Tendsto (fun R : ℝ ↦ (R^2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_pow_atTop (by decide : 2 ≠ 0))
  have hlim := ((tendsto_const_nhds (x := (8:ℝ))).mul
    (hB.add ((tendsto_const_nhds (x := 1 - Real.log ‖f c‖)).mul h₀)))
  have hlim' : Tendsto (fun R ↦ 8 * (B R - Real.log ‖f c‖ + 1) / R^2) atTop (𝓝 0) := by
    convert hlim using 1
    · funext R; ring
    · norm_num
  exact norm_le_zero_iff.mp (le_of_tendsto_of_tendsto tendsto_const_nhds hlim' hh)


/-- A zero-free entire function of order strictly less than two has constant relative shift.
The disk bounds are stated at scale 6R to allow arbitrary centers in Cauchy's estimate. -/
private theorem subquadratic_zeroFree_shift (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) (hn : ∀ z, f z ≠ 0)
    (B : ℝ → ℝ) (hB : Tendsto (fun R ↦ B R / R^2) atTop (𝓝 0))
    (hbound : ∀ᶠ R : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ 6 * R → ‖f z‖ ≤ Real.exp (B R))
    (a : ℂ) : ∃ k : ℂ, k ≠ 0 ∧ ∀ z, f (z + a) = k * f z := by
  have hd := subquadratic_zeroFree_logDeriv_constant f hf hn B hB hbound
  have he : EqOn (logDeriv (fun z ↦ f (z+a))) (logDeriv f) univ := by
    intro z _
    change deriv (fun u ↦ f (u+a)) z / f (z+a) = _
    rw [deriv_comp_add_const]
    exact hd (z+a) z
  obtain ⟨k,hk,h⟩ := (logDeriv_eqOn_iff (hf.comp (differentiable_id.add_const a)).differentiableOn
    hf.differentiableOn isOpen_univ isPreconnected_univ (fun z _ ↦ hn z) (fun z _ ↦ hn (z+a))).mp he
  exact ⟨k,hk,fun z ↦ h (mem_univ z)⟩


end

section
open Filter Set MeasureTheory Asymptotics
open scoped Topology
private def kernelWeight (x : ℝ) := Real.exp (|Real.log x| ^ 3)
private theorem kernelWeight_top (F : ℝ → ℝ) (p : ℝ) (hp : 0 < p)
    (hF : F =O[atTop] (fun x ↦ Real.exp (-p*x))) (r : ℝ) :
    (fun x ↦ ((kernelWeight x * F x : ℝ) : ℂ) - 0) =O[atTop] (fun x : ℝ ↦ x ^ r) := by
  obtain ⟨C,hCpos,hC⟩ := hF.exists_pos
  apply IsBigO.trans (g := fun x : ℝ ↦ Real.exp (-(p/2)*x)) _ (isLittleO_exp_neg_mul_rpow_atTop (half_pos hp) r).isBigO
  apply Asymptotics.IsBigO.of_bound C
  have hl := (isLittleO_log_rpow_rpow_atTop (3 : ℝ) (show (0:ℝ)<1 by norm_num)).bound (half_pos hp)
  filter_upwards [hC.bound, hl, eventually_ge_atTop (1:ℝ)] with x h hlog hx
  have hx' := zero_le_one.trans hx
  simp only [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_mul, kernelWeight,
    abs_of_pos (Real.exp_pos _), abs_of_nonneg (Real.log_nonneg hx)] at *
  rw [show (3:ℝ) = (3:ℕ) by norm_num, Real.rpow_natCast, Real.rpow_one,
    abs_of_nonneg (pow_nonneg (Real.log_nonneg hx) 3), abs_of_nonneg hx'] at hlog
  calc
    Real.exp (Real.log x ^ 3) * |F x| ≤ Real.exp (Real.log x ^ 3) * (C * Real.exp (-p*x)) := by gcongr
    _ = C * Real.exp (Real.log x ^ 3 + -p*x) := by rw [Real.exp_add]; ring
    _ ≤ C * Real.exp (-(p/2)*x) := by gcongr; linarith

private theorem oddKernel_weight_integrable (a : UnitAddCircle) :
    IntegrableOn (fun x ↦ kernelWeight x * |HurwitzZeta.oddKernel a x|) (Ioi 0) := by
  let P := HurwitzZeta.hurwitzOddFEPair a
  have hw : ContinuousOn kernelWeight (Ioi 0) := Real.continuous_exp.comp_continuousOn
    ((Real.continuousOn_log.mono fun x hx ↦ ne_of_gt hx).abs.pow 3)
  have hft := HurwitzZeta.isBigO_atTop_oddKernel a
  have hgt := HurwitzZeta.isBigO_atTop_sinKernel a
  let Q : WeakFEPair ℂ :=
    { f := fun x ↦ ((kernelWeight x * HurwitzZeta.oddKernel a x : ℝ) : ℂ)
      g := fun x ↦ ((kernelWeight x * HurwitzZeta.sinKernel a x : ℝ) : ℂ)
      f₀ := 0, g₀ := 0, k := P.k, hk := P.hk, ε := P.ε, hε := P.hε
      hf_int := (Complex.continuous_ofReal.comp_continuousOn (hw.mul (HurwitzZeta.continuousOn_oddKernel a))).locallyIntegrableOn measurableSet_Ioi
      hg_int := (Complex.continuous_ofReal.comp_continuousOn (hw.mul (HurwitzZeta.continuousOn_sinKernel a))).locallyIntegrableOn measurableSet_Ioi
      hf_top := fun r ↦ kernelWeight_top _ hft.choose hft.choose_spec.1 hft.choose_spec.2 r
      hg_top := fun r ↦ kernelWeight_top _ hgt.choose hgt.choose_spec.1 hgt.choose_spec.2 r
      h_feq := fun x hx ↦ by
        have h := P.h_feq x hx
        have hw' : kernelWeight (1/x) = kernelWeight x := by simp [kernelWeight, Real.log_inv, one_div]
        change ((HurwitzZeta.oddKernel a (1/x) : ℝ) : ℂ) = (P.ε * ↑(x ^ P.k)) • ((HurwitzZeta.sinKernel a x : ℝ) : ℂ) at h
        simp only [Complex.ofReal_mul, hw', h, smul_eq_mul]
        ring }
  have hs : IsStrongFEPair Q := ⟨rfl,rfl⟩
  have hi := (hs.hasMellin (1:ℂ)).1.norm
  change IntegrableOn (fun x : ℝ ↦ ‖(x : ℂ) ^ (1 - 1 : ℂ) • (((kernelWeight x * HurwitzZeta.oddKernel a x : ℝ) : ℂ))‖) (Ioi 0) at hi
  simpa only [sub_self, Complex.cpow_zero, one_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _), kernelWeight] using hi

private theorem abs_log_exponent (x : ℝ) (T : ℝ) (hT : 0 ≤ T) {u : ℝ} (hu : |u| ≤ T) :
    Real.log x * u ≤ T * Real.sqrt T + |Real.log x| ^ 3 := by
  have h : Real.log x * u ≤ |Real.log x| * T :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left hu (abs_nonneg _)))
  by_cases he : |Real.log x| ≤ Real.sqrt T
  · exact h.trans ((mul_le_mul_of_nonneg_right he hT).trans (by rw [mul_comm]; linarith [pow_nonneg (abs_nonneg (Real.log x)) 3]))
  · have hs := Real.sq_sqrt hT
    have hsq : T ≤ |Real.log x| ^ 2 := by rw [← hs]; gcongr; exact le_of_not_ge he
    have hpow := mul_le_mul_of_nonneg_left hsq (abs_nonneg (Real.log x))
    have hT' := mul_nonneg hT (Real.sqrt_nonneg T)
    nlinarith

private theorem oddHurwitz_growth (a : UnitAddCircle) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (s : ℂ), 1 ≤ R → ‖s‖ ≤ 6*R →
      ‖HurwitzZeta.completedHurwitzZetaOdd a s‖ ≤ C * Real.exp ((8*R) * Real.sqrt (8*R)) := by
  let F := HurwitzZeta.oddKernel a
  let g (x : ℝ) := kernelWeight x * |F x|
  have hg : IntegrableOn g (Ioi 0) := oddKernel_weight_integrable a
  let C := ∫ x in Ioi (0:ℝ), g x
  have hC : 0 ≤ C := integral_nonneg (fun x ↦ mul_nonneg (Real.exp_pos _).le (abs_nonneg _))
  refine ⟨C,hC,fun R s hR hs ↦ ?_⟩
  let z := (s+1)/2
  let A := Real.exp ((8*R) * Real.sqrt (8*R))
  have hz : |(z-1).re| ≤ 8*R := by
    have h : (z-1).re = s.re / 2 - 1/2 := by simp [z, Complex.div_ofNat_re]; ring
    rw [h, abs_le]
    have h' := abs_le.mp (Complex.abs_re_le_norm s)
    constructor <;> linarith
  let P := HurwitzZeta.hurwitzOddFEPair a
  have hbound : ‖mellin P.f z‖ ≤ A*C := by
    calc
      _ ≤ ∫ x in Ioi (0:ℝ), ‖(x:ℂ) ^ (z-1) • P.f x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in Ioi (0:ℝ), A * g x := by
        apply setIntegral_mono_on ((HurwitzZeta.isStrong_hurwitzOddFEPair a).hasMellin z).1.norm
          (hg.const_mul _) measurableSet_Ioi
        intro x hx
        rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Real.rpow_def_of_pos hx]
        change Real.exp _ * ‖((F x : ℝ) : ℂ)‖ ≤ A * (kernelWeight x * |F x|)
        rw [Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
        dsimp only [A, kernelWeight]
        rw [← Real.exp_add]
        gcongr
        exact abs_log_exponent x _ (by positivity) hz
      _ = _ := integral_const_mul _ _
  change ‖P.Λ z / 2‖ ≤ _
  rw [(HurwitzZeta.isStrong_hurwitzOddFEPair a).Λ_eq, norm_div, Complex.norm_ofNat]
  change ‖mellin P.f z‖ / 2 ≤ C*A
  rw [mul_comm C A]
  linarith [norm_nonneg (mellin P.f z)]

private theorem oddDirichlet_subquadratic (χ : DirichletCharacter ℂ 5) (ho : χ.Odd) :
    ∃ B : ℝ → ℝ, Tendsto (fun R ↦ B R / R^2) atTop (𝓝 0) ∧
      ∀ᶠ R : ℝ in atTop, ∀ z : ℂ, ‖z‖ ≤ 6*R → ‖χ.completedLFunction z‖ ≤ Real.exp (B R) := by
  choose C hC hB using oddHurwitz_growth
  let A := ∑ j : ZMod 5, ‖χ j‖ * C (ZMod.toAddCircle j)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun j _ ↦ mul_nonneg (norm_nonneg _) (hC _))
  let K := Real.log (A+1)
  let B (R : ℝ) := K + 6*R*Real.log 5 + 8*R*Real.sqrt (8*R)
  refine ⟨B, ?_, ?_⟩
  · have hs : Tendsto (fun R : ℝ ↦ (Real.sqrt R)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
    have hl := ((tendsto_const_nhds (x := K)).mul (tendsto_inv_atTop_zero.comp
      (tendsto_pow_atTop (by decide : 2 ≠ 0)))).add
      (((tendsto_const_nhds (x := 6*Real.log 5)).mul tendsto_inv_atTop_zero).add
        ((tendsto_const_nhds (x := 8*Real.sqrt 8)).mul hs))
    apply Filter.Tendsto.congr' _ (by simpa using hl)
    filter_upwards [eventually_gt_atTop (0:ℝ)] with R hR
    dsimp [B]
    rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤8)]
    field_simp [hR.ne', (Real.sqrt_pos.mpr hR).ne']
    ring_nf
    rw [Real.sq_sqrt hR.le]
    ring
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with R hR
    intro z hz
    let E := Real.exp (8*R*Real.sqrt (8*R))
    have hsum : ‖∑ j : ZMod 5, χ j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) z‖ ≤ A * E := by
      calc
        _ ≤ ∑ j : ZMod 5, ‖χ j * HurwitzZeta.completedHurwitzZetaOdd (ZMod.toAddCircle j) z‖ := norm_sum_le _ _
        _ ≤ ∑ j : ZMod 5, (‖χ j‖ * C (ZMod.toAddCircle j)) * E := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (hB _ R z hR hz) (norm_nonneg _)
        _ = _ := (Finset.sum_mul ..).symm
    have hN : ‖(5:ℂ)^(-z)‖ ≤ Real.exp (6*R*Real.log 5) := by
      rw [show (5:ℂ) = ((5:ℝ):ℂ) by norm_num, Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0:ℝ)<5),
        Real.rpow_def_of_pos (by norm_num : (0:ℝ)<5), Complex.neg_re]
      apply Real.exp_le_exp.mpr
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right ((neg_le_abs _).trans ((Complex.abs_re_le_norm z).trans hz))
        (Real.log_nonneg (by norm_num))
    change ‖ZMod.completedLFunction χ z‖ ≤ _
    rw [ZMod.completedLFunction_def_odd ho.to_fun, norm_mul]
    calc
      _ ≤ Real.exp (6*R*Real.log 5) * (A*E) := mul_le_mul hN hsum (norm_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (6*R*Real.log 5) * ((A+1)*E) := by gcongr; linarith
      _ = Real.exp (B R) := by
        dsimp [B,K,E]
        rw [Real.exp_add, Real.exp_add, Real.exp_log (by linarith)]
        ring


end

section
open Filter
open scoped Topology

/-- On positive real arguments the gamma recurrence forces the ratio at shifts
of two to grow linearly, since the Dirichlet L-series tends to one. -/
private theorem oddDirichlet_shift_impossible (χ : DirichletCharacter ℂ 5) (ho : χ.Odd)
    (k : ℂ) (_hk : k ≠ 0)
    (he : ∀ z : ℂ, χ.completedLFunction (z + 2) = k * χ.completedLFunction z) : False := by
  have hlim : Tendsto (fun x : ℝ ↦ χ.LFunction x) atTop (𝓝 1) := by
    have ha := LSeries.tendsto_atTop (f := fun n : ℕ ↦ χ n)
      (lt_of_eq_of_lt (χ.abscissaOfAbsConv_eq_one (by norm_num)) (by exact_mod_cast EReal.coe_lt_top (1 : ℝ)))
    have ha' : Tendsto (fun x : ℝ ↦ LSeries (fun n : ℕ ↦ χ n) x) atTop (𝓝 1) := by
      simpa using ha
    apply ha'.congr'
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    exact (χ.LFunction_eq_LSeries hx).symm
  have hf (z : ℂ) (hz : 0 < (z + 1).re) :
      χ.completedLFunction z = χ.LFunction z * Complex.Gammaℝ (z + 1) := by
    rw [χ.LFunction_eq_completed_div_gammaFactor z (Or.inr (by decide)), ho.gammaFactor_def,
      div_mul_cancel₀ _ (Complex.Gammaℝ_ne_zero_of_re_pos hz)]
  have hrel (x : ℝ) (hx : 1 < x) :
      χ.LFunction ((x + 2 : ℝ) : ℂ) =
        (2 * (Real.pi : ℂ) * k) * χ.LFunction x * (((x + 1)⁻¹ : ℝ) : ℂ) := by
    let z : ℂ := x
    have hz : 0 < (z + 1).re := by simp [z]; linarith
    have hn : z + 1 ≠ 0 := fun e ↦ by simp [e] at hz
    have hg := Complex.Gammaℝ_ne_zero_of_re_pos hz
    have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h := he z
    rw [hf _ (by simp [z]; linarith), hf _ hz,
      show z + 2 + 1 = z + 1 + 2 by ring, Complex.Gammaℝ_add_two hn] at h
    push_cast
    change χ.LFunction (z + 2) = (2 * (Real.pi : ℂ) * k) * χ.LFunction z * (z + 1)⁻¹
    field_simp [hn]
    field_simp [hp] at h
    exact h
  have hinv : Tendsto (fun x : ℝ ↦ (((x + 1)⁻¹ : ℝ) : ℂ)) atTop (𝓝 0) := by
    exact_mod_cast Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ (1 : ℝ) tendsto_id))
  have hzero : Tendsto (fun x : ℝ ↦ χ.LFunction ((x + 2 : ℝ) : ℂ)) atTop (𝓝 0) := by
    have hl := ((hlim.const_mul (2 * (Real.pi : ℂ) * k)).mul hinv)
    apply (show Tendsto _ _ (𝓝 (0 : ℂ)) from by simpa using hl).congr'
    exact (eventually_gt_atTop (1 : ℝ)).mono fun x hx ↦ by simpa using (hrel x hx).symm
  exact zero_ne_one (tendsto_nhds_unique hzero
    (hlim.comp (tendsto_atTop_add_const_right _ (2 : ℝ) tendsto_id)))


end
open Filter Set
open scoped Topology
/-- A character mod 5 detecting -1 is primitive and odd, and its L-function
has a zero of finite positive order in the open critical strip. -/
public theorem dirichletFive_positiveOrder (χ : DirichletCharacter ℂ 5) (h4 : χ 4 ≠ 1) :
    χ.IsPrimitive ∧ ∃ z : ℂ, 0 < z.re ∧ z.re < 1 ∧
      0 < (meromorphicOrderAt χ.LFunction z).untop₀.toNat := by
  have ho : χ.Odd := χ.even_or_odd.resolve_left (fun e ↦ h4 (by
    rw [show (4 : ZMod 5) = -1 by decide]; exact e))
  have hn : χ ≠ 1 := by
    intro e
    subst χ
    exact DirichletCharacter.Odd.not_even _ ho (by simp)
  have hp : χ.IsPrimitive := by
    apply (Nat.dvd_prime Nat.prime_five).mp χ.conductor_dvd_level |>.resolve_left
    exact fun h ↦ hn (χ.eq_one_iff_conductor_eq_one.mpr h)
  refine ⟨hp, ?_⟩
  obtain ⟨z, hz⟩ : ∃ z, χ.completedLFunction z = 0 := by
    by_contra! hall
    obtain ⟨B,hB,hbound⟩ := oddDirichlet_subquadratic χ ho
    obtain ⟨k,hk,hk'⟩ := subquadratic_zeroFree_shift _ (DirichletCharacter.differentiable_completedLFunction hn)
      hall B hB hbound 2
    exact oddDirichlet_shift_impossible χ ho k hk hk'
  have hrs : z.re < 1 := lt_of_not_ge (fun h ↦ χ.completedLFunction_ne_zero_of_one_le_re (.inl hn) h hz)
  have hr : 0 < z.re := by
    by_contra! he
    have h := hp.completedLFunction_one_sub (1-z)
    rw [sub_sub_cancel] at h
    have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hn
    have hne := DirichletCharacter.completedLFunction_ne_zero_of_one_le_re χ⁻¹ (s := 1-z)
      (.inl hinv) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    rw [hz] at h
    exact (mul_ne_zero (mul_ne_zero (by simp [Complex.cpow_eq_zero_iff]) (DirichletCharacter.rootNumber_ne_zero hp)) hne) h.symm
  have hval : χ.LFunction z = 0 := by
    rw [χ.LFunction_eq_completed_div_gammaFactor z (.inr (by decide)), hz, zero_div]
  have hd := DirichletCharacter.differentiable_LFunction hn
  have hm : MeromorphicOn χ.LFunction univ := fun t _ ↦ (hd.analyticAt t).meromorphicAt
  have hfin : meromorphicOrderAt χ.LFunction z ≠ ⊤ := by
    have h₁ := χ.LFunction_ne_zero_of_one_le_re (s := 2) (.inl hn) (by norm_num)
    apply hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ (2:ℂ)) (mem_univ z)
    rw [(hd.analyticAt _).meromorphicOrderAt_eq, (hd.analyticAt _).analyticOrderAt_eq_zero.mpr h₁]
    simp
  have hpos : 0 < meromorphicOrderAt χ.LFunction z := by
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm _ (mem_univ _))).mp
    rw [← hval]
    exact (hd z).continuousAt.continuousWithinAt
  refine ⟨z, hr, hrs, ?_⟩
  lift meromorphicOrderAt χ.LFunction z to ℤ using hfin with n
  have hpos' : (0:ℤ) < n := by exact_mod_cast hpos
  simp only [WithTop.untop₀_coe]
  omega

end RiemannMasullo
