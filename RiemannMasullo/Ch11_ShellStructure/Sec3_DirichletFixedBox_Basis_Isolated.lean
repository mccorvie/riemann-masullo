module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Projections_Isolated
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes (Basis)

Averaged inner-product quotient and unconditional Hilbert basis (`dirichletFixedBox_unconditional_basis`).

Nothing outside the `Sec3_DirichletFixedBox*` / `Sec3_RatBridge*` isolated stack imports this module.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField RiemannMasullo Set Topology
open scoped BigOperators ContDiff FourierTransform NNReal Real SchwartzMap

namespace RiemannMasullo.Isolated

section CircleActionAndTraceNorm

open MeasureTheory Filter Topology Real
open scoped InnerProductSpace Convolution ENNReal

private theorem dirichletDeplete_intervalIntegral_shift {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {L : ℝ} (_hL : 0 < L) (c : ℝ → ℂ) (hc : Continuous c) (U : ℝ → ℂ) (hU : Continuous U) (x : ℝ) :
    dirichletDeplete χ T (fun y : ℝ ↦ ∫ a in (0 : ℝ)..L, c a * U (y - a)) x =
      ∫ a in (0 : ℝ)..L, c a * dirichletDeplete χ T U (x - a) := by
  induction T using Finset.induction_on generalizing x with
  | empty =>
    simp [dirichletDeplete_empty]
  | insert q S hqS ih =>
    have hq0 : 0 < q := hT q (Finset.mem_insert_self q S)
    have hS : ∀ r ∈ S, 0 < r := fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
    have hsub1 : dirichletDeplete χ S (fun y : ℝ ↦ ∫ a in (0 : ℝ)..L, c a * U (y - a)) =
        fun y : ℝ ↦ ∫ a in (0 : ℝ)..L, c a * dirichletDeplete χ S U (y - a) := by
      ext y
      exact ih hS y
    rw [dirichletDeplete_insert χ hqS, LinearMap.comp_apply, LinearMap.comp_apply, hsub1]
    simp only [depleteStepFun, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      halfTwistLogDilate, hq0.ne', ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hUS_cont : Continuous (dirichletDeplete χ S U) := dirichletDeplete_continuous χ S hS hU
    have hint1 : IntervalIntegrable (fun a : ℝ ↦ c a * dirichletDeplete χ S U (x - a)) volume 0 L :=
      (hc.mul (hUS_cont.comp (continuous_const.sub continuous_id))).intervalIntegrable 0 L
    have hint2 : IntervalIntegrable (fun a : ℝ ↦
        χ (q : ZMod N) * ((q : ℂ) ^ (-(1 / 2 : ℂ)) * (c a * dirichletDeplete χ S U (x + Real.log q - a))))
        volume 0 L :=
      (continuous_const.mul (continuous_const.mul (hc.mul (hUS_cont.comp (continuous_const.sub continuous_id))))).intervalIntegrable 0 L
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hint1 hint2]
    refine intervalIntegral.integral_congr fun a _ ↦ ?_
    have hxq : x + Real.log q - a = x - a + Real.log q := by ring
    rw [hxq]
    ring

private theorem backHalfShiftCLM_coeFn_ae {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (a : ℝ)
    {U : ℝ → ℂ} (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false)) :
    (backHalfShiftCLM α s hα hs a (toDirichletStrip α s U hU) : ℝ → ℂ) =ᵐ[
        intervalSobolevMeasure volume id (-α) α s false]
      fun x : ℝ ↦ (Real.exp (a / 2) : ℂ) * U (x - a) := by
  have hV := (halfShift_memLp_and_eLpNorm hα hs a hU).1
  rw [backHalfShiftCLM_apply_toDirichletStrip α s hα hs a hU hV]
  exact hV.coeFn_toLp

private theorem strip_dirichletSmoothLift_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (_hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hTpos : ∀ q ∈ T, 0 < q)
    {p : ℕ} (hp : p.Prime) {R α s : ℝ} (hR_pos : 0 < R) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ R f₀) (j : ℤ)
    (hmem_H : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ (dirichletSmoothLift χ hp hR_pos hf₀ j))) 2
      (intervalSobolevMeasure volume id (-α) α s false))
    (hmem₀ : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
      (intervalSobolevMeasure volume id (-α) α s false)) :
    toDirichletStrip α s
        (dirichletDeplete χ T (twistedHalfLogProfile χ (dirichletSmoothLift χ hp hR_pos hf₀ j))) hmem_H =
      ((Real.log p)⁻¹ : ℂ) • ∫ a in (0 : ℝ)..Real.log p,
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
          backHalfShiftCLM α s hα hs a
            (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem₀) := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let H := dirichletSmoothLift χ hp hR_pos hf₀ j
  let v_H := toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ H)) hmem_H
  let v₀ := toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem₀
  let μ₀ := intervalSobolevMeasure volume id (-α) α s false
  refine ext_inner_left ℂ fun z ↦ ?_
  have hc_exp : Continuous (fun a : ℝ ↦
      Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hcont_shift : Continuous (fun a : ℝ ↦
      Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
        backHalfShiftCLM α s hα hs a v₀) :=
    hc_exp.smul (continuous_backHalfShiftCLM α s hα hs v₀)
  have hinner_comm : ⟪z, ∫ a in (0 : ℝ)..L,
      Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
        backHalfShiftCLM α s hα hs a v₀⟫_ℂ =
      ∫ a in (0 : ℝ)..L,
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          ⟪z, backHalfShiftCLM α s hα hs a v₀⟫_ℂ := by
    have hc := ((innerSL ℂ z).intervalIntegral_comp_comm
      (hcont_shift.intervalIntegrable 0 L (μ := volume))).symm
    change ⟪z, ∫ a in (0 : ℝ)..L, _⟫_ℂ = ∫ a in (0 : ℝ)..L, ⟪z, _⟫_ℂ at hc
    simpa only [inner_smul_right] using hc
  rw [inner_smul_right, hinner_comm]
  have hlhs : ⟪z, v_H⟫_ℂ = ∫ x : ℝ, starRingEnd ℂ ((z : ℝ → ℂ) x) *
      dirichletDeplete χ T (twistedHalfLogProfile χ H) x ∂μ₀ := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hmem_H.coeFn_toLp] with x hx
    have hx' : (v_H : ℝ → ℂ) x = dirichletDeplete χ T (twistedHalfLogProfile χ H) x := hx
    rw [RCLike.inner_apply, hx']
    ring
  have hpt_H : ∀ x : ℝ, dirichletDeplete χ T (twistedHalfLogProfile χ H) x =
      (L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L,
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          (Real.exp (a / 2) : ℂ) * dirichletDeplete χ T (twistedHalfLogProfile χ f₀) (x - a) := by
    intro x
    have htw_eq : twistedHalfLogProfile χ H = fun y : ℝ ↦ ∫ a in (0 : ℝ)..L,
        ((L⁻¹ : ℂ) * Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          (Real.exp (a / 2) : ℂ)) * twistedHalfLogProfile χ f₀ (y - a) := by
      ext y
      rw [twistedHalfLogProfile_dirichletSmoothLift χ hN hp hR_pos hf₀ j y,
        ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun a _ ↦ ?_
      ring
    rw [htw_eq]
    have hc_cont : Continuous (fun a : ℝ ↦ (L⁻¹ : ℂ) *
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) * (Real.exp (a / 2) : ℂ)) :=
      (continuous_const.mul hc_exp).mul
        (Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2)))
    rw [dirichletDeplete_intervalIntegral_shift χ T hTpos hL_pos _ hc_cont _
      (twistedHalfLogProfile_continuous χ hN f₀) x, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun a _ ↦ ?_
    ring
  let G_swap : ℝ → ℝ → ℂ := fun a x ↦
    starRingEnd ℂ ((z : ℝ → ℂ) x) *
      (Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
        (Real.exp (a / 2) : ℂ) * dirichletDeplete χ T (twistedHalfLogProfile χ f₀) (x - a))
  have hcont_U0 : Continuous (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) :=
    dirichletDeplete_continuous χ T hTpos (twistedHalfLogProfile_continuous χ hN f₀)
  let M_shift : ℝ := Real.exp (L / 2 + α * L) * (2 + 2 * L ^ 2) ^ (s / 4)
  have hG_swap_int : Integrable (Function.uncurry G_swap)
      ((volume.restrict (Set.uIoc 0 L)).prod μ₀) := by
    have hG_meas : AEStronglyMeasurable (Function.uncurry G_swap)
        ((volume.restrict (Set.uIoc 0 L)).prod μ₀) := by
      have h1 : AEStronglyMeasurable (fun q : ℝ × ℝ ↦ starRingEnd ℂ ((z : ℝ → ℂ) q.2))
          ((volume.restrict (Set.uIoc 0 L)).prod μ₀) :=
        (Lp.aestronglyMeasurable z).star.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
      have hc_right : Continuous (fun q : ℝ × ℝ ↦
          Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (q.1 : ℂ)) *
            (Real.exp (q.1 / 2) : ℂ) *
            dirichletDeplete χ T (twistedHalfLogProfile χ f₀) (q.2 - q.1)) :=
        ((hc_exp.comp continuous_fst).mul
          ((Complex.continuous_ofReal.comp
            (Real.continuous_exp.comp (continuous_id.div_const 2))).comp continuous_fst)).mul
          (hcont_U0.comp (continuous_snd.sub continuous_fst))
      exact h1.mul hc_right.aestronglyMeasurable
    have hG_a : ∀ a : ℝ, Integrable (G_swap a) μ₀ := fun a ↦ by
      have hw_ae := backHalfShiftCLM_coeFn_ae hα hs a hmem₀
      have hint_zw : Integrable (fun x : ℝ ↦
          ⟪(z : ℝ → ℂ) x, (backHalfShiftCLM α s hα hs a v₀ : ℝ → ℂ) x⟫_ℂ) μ₀ :=
        L2.integrable_inner z (backHalfShiftCLM α s hα hs a v₀)
      refine (hint_zw.const_mul
        (Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)))).congr ?_
      filter_upwards [hw_ae] with x hx
      dsimp only [G_swap]
      rw [RCLike.inner_apply]
      have hx' : (backHalfShiftCLM α s hα hs a v₀ : ℝ → ℂ) x =
          (Real.exp (a / 2) : ℂ) * dirichletDeplete χ T (twistedHalfLogProfile χ f₀) (x - a) := hx
      rw [hx']
      ring
    refine (MeasureTheory.integrable_prod_iff hG_meas).mpr ⟨Filter.Eventually.of_forall hG_a, ?_⟩
    have hconst_int : Integrable (fun _ : ℝ ↦ ‖z‖ * (M_shift * ‖v₀‖))
        (volume.restrict (Set.uIoc 0 L)) := by
      change IntegrableOn (fun _ : ℝ ↦ ‖z‖ * (M_shift * ‖v₀‖)) (Set.uIoc 0 L) volume
      rw [Set.uIoc_of_le hL_pos.le]
      exact continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
    refine hconst_int.mono' (hG_meas.norm.integral_prod_right') ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with a ha
    rw [Set.uIoc_of_le hL_pos.le] at ha
    have hw_ae := backHalfShiftCLM_coeFn_ae hα hs a hmem₀
    let w_a := backHalfShiftCLM α s hα hs a v₀
    let z_pos : Lp ℝ 2 μ₀ := (Lp.memLp z).norm.toLp _
    let w_pos : Lp ℝ 2 μ₀ := (Lp.memLp w_a).norm.toLp _
    have hz_pos_norm : ‖z_pos‖ = ‖z‖ := by
      rw [Lp.norm_toLp, Lp.norm_def]
      congr 1
      exact eLpNorm_norm (f := (z : ℝ → ℂ)) (Lp.aestronglyMeasurable z)
    have hw_pos_norm : ‖w_pos‖ = ‖w_a‖ := by
      rw [Lp.norm_toLp, Lp.norm_def]
      congr 1
      exact eLpNorm_norm (f := (w_a : ℝ → ℂ)) (Lp.aestronglyMeasurable w_a)
    have hint_norm_eq : ∫ x : ℝ, ‖G_swap a x‖ ∂μ₀ = ⟪z_pos, w_pos⟫_ℝ := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hw_ae, (Lp.memLp z).norm.coeFn_toLp, (Lp.memLp w_a).norm.coeFn_toLp]
        with x hwx hzx hwx'
      dsimp only [G_swap]
      have hexp1 : ‖Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ))‖ = 1 := by
        rw [Complex.norm_exp]
        have hre : (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)).re = 0 := by
          simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.neg_re,
            Complex.ofReal_re, Complex.ofReal_im]
        rw [hre, Real.exp_zero]
      have hwx'' : (w_a : ℝ → ℂ) x = (Real.exp (a / 2) : ℂ) *
          dirichletDeplete χ T (twistedHalfLogProfile χ f₀) (x - a) := hwx
      rw [mul_assoc (Complex.exp _), ← hwx'', norm_mul, norm_mul, Complex.norm_conj, hexp1, one_mul]
      have hz_eq : (z_pos : ℝ → ℝ) x = ‖(z : ℝ → ℂ) x‖ := hzx
      have hw_eq : (w_pos : ℝ → ℝ) x = ‖(w_a : ℝ → ℂ) x‖ := hwx'
      rw [hz_eq, hw_eq, RCLike.inner_apply, conj_trivial, mul_comm]
    have hw_bound : ‖w_a‖ ≤ M_shift * ‖v₀‖ := by
      refine (ContinuousLinearMap.le_opNorm (backHalfShiftCLM α s hα hs a) v₀).trans ?_
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      refine (norm_backHalfShiftCLM_le α s hα hs a).trans ?_
      have ha_nonneg : 0 ≤ a := ha.1.le
      have h1 : a / 2 + α * |a| ≤ L / 2 + α * L := by
        rw [abs_of_nonneg ha_nonneg]
        nlinarith [ha.2]
      have h2 : 2 + 2 * a ^ 2 ≤ 2 + 2 * L ^ 2 := by
        nlinarith [sq_le_sq' (by linarith [ha.1, ha.2]) ha.2]
      exact mul_le_mul (Real.exp_le_exp.mpr h1)
        (Real.rpow_le_rpow (by positivity) h2 (by positivity))
        (by positivity) (Real.exp_pos _).le
    calc ‖∫ y : ℝ, ‖Function.uncurry G_swap (a, y)‖ ∂μ₀‖
        = ∫ x : ℝ, ‖G_swap a x‖ ∂μ₀ :=
          Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
      _ = ⟪z_pos, w_pos⟫_ℝ := hint_norm_eq
      _ ≤ ‖z_pos‖ * ‖w_pos‖ := real_inner_le_norm z_pos w_pos
      _ = ‖z‖ * ‖w_a‖ := by rw [hz_pos_norm, hw_pos_norm]
      _ ≤ ‖z‖ * (M_shift * ‖v₀‖) := mul_le_mul_of_nonneg_left hw_bound (norm_nonneg _)
  have hswap := MeasureTheory.intervalIntegral_integral_swap hG_swap_int
  have hlhs' : ⟪z, v_H⟫_ℂ = (L⁻¹ : ℂ) * ∫ x : ℝ, (∫ a in (0 : ℝ)..L, G_swap a x) ∂μ₀ := by
    rw [hlhs, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
    dsimp only
    rw [hpt_H x, mul_left_comm _ (L⁻¹ : ℂ), ← intervalIntegral.integral_const_mul]
  rw [hlhs', ← hswap]
  congr 1
  refine intervalIntegral.integral_congr fun a _ ↦ ?_
  have hw_ae := backHalfShiftCLM_coeFn_ae hα hs a hmem₀
  rw [L2.inner_def, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hw_ae] with x hx
  dsimp only [G_swap]
  have hx' : (backHalfShiftCLM α s hα hs a v₀ : ℝ → ℂ) x =
      (Real.exp (a / 2) : ℂ) * dirichletDeplete χ T (twistedHalfLogProfile χ f₀) (x - a) := hx
  rw [RCLike.inner_apply, hx']
  ring

theorem dirichletQuotProj_eq_row_smul {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f_j : 𝓢(ℝ, ℂ)} (hf_j : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f_j)
    (j : ℤ) (hdiag : ∀ m : ℤ,
      ∀ hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f_j)) 2
          (intervalSobolevMeasure volume id (-α) α s false),
        dirichletNormalizedRow χ T p X α s hα hs m
          (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_j)) hmem) =
          if m = j then 1 else 0)
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    let hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
    let hR_pos : 0 < X / ∏ q ∈ T, (q : ℝ) :=
      div_pos hX (Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hTpos q hq))
    let hmem_j : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f_j)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs hf_j
    let e_j := dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
      ⟨toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_j)) hmem_j,
        mem_dirichletStageSpace_of_test T hα hs hf_j hmem_j⟩
    dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j q =
      dirichletQuotRow χ T p X α s hα hs j q • e_j := by
  intro hTpos hR_pos hmem_j e_j
  let E := dirichletStageSpace χ T X α s hα hs
  let Q := dirichletStageQuotient χ T p X α s hα hs
  let qMap := dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
  let P_j := dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j
  let R : ℝ := X / ∏ q ∈ T, (q : ℝ)
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let Φ_diff : E →L[ℂ] Q := P_j.comp qMap -
    ((dirichletQuotRow χ T p X α s hα hs j).comp qMap).smulRight e_j
  have hdiff_zero : ∀ x : E, Φ_diff x = 0 := by
    refine clm_zero_on_dirichletStageSpace χ T X α s hα hs Φ_diff fun f₀ hf₀ hmem₀ ↦ ?_
    rw [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.comp_apply, sub_eq_zero]
    let x₀ : E := ⟨toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem₀,
      mem_dirichletStageSpace_of_test T hα hs hf₀ hmem₀⟩
    let c₀ : ℂ := dirichletQuotRow χ T p X α s hα hs j (qMap x₀)
    let H := dirichletSmoothLift χ hp hR_pos hf₀ j
    have hH_box : IsDirichletFixedBoxTest χ R H := dirichletSmoothLift_isFixedBox χ hp hR_pos hf₀ j
    have hmem_H : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ H)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs hH_box
    let v_H := toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ H)) hmem_H
    let v₀ := toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem₀
    have hv_H_eq : v_H = (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
          backHalfShiftCLM α s hα hs a v₀ :=
      strip_dirichletSmoothLift_eq hχ hN T hTpos hp hR_pos hα hs hf₀ j hmem_H hmem₀
    have hx_lift : (⟨v_H, mem_dirichletStageSpace_of_test T hα hs hH_box hmem_H⟩ : E) =
        (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
          Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
            ⟨backHalfShiftCLM α s hα hs (max a 0) v₀,
              backHalfShiftCLM_mem_dirichletStageSpace hχ hN T hTpos hX hα hs (max a 0)
                (le_max_right a 0) x₀.2⟩ := by
      let F_E : ℝ → E := fun a ↦
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
          ⟨backHalfShiftCLM α s hα hs (max a 0) v₀,
            backHalfShiftCLM_mem_dirichletStageSpace hχ hN T hTpos hX hα hs (max a 0)
              (le_max_right a 0) x₀.2⟩
      have hc_exp : Continuous (fun a : ℝ ↦
          Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ))) :=
        Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
      have hFE_cont : Continuous F_E := by
        refine hc_exp.smul ?_
        refine Continuous.subtype_mk ?_ _
        exact (continuous_backHalfShiftCLM α s hα hs v₀).comp (continuous_id.max continuous_const)
      refine Subtype.ext ?_
      change v_H = (L⁻¹ : ℂ) • ((E.subtypeL) (∫ a in (0 : ℝ)..L, F_E a))
      rw [← E.subtypeL.intervalIntegral_comp_comm (hFE_cont.intervalIntegrable 0 L), hv_H_eq]
      congr 1
      refine intervalIntegral.integral_congr fun a ha ↦ ?_
      rw [Set.uIcc_of_le hL_pos.le] at ha
      change Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
          backHalfShiftCLM α s hα hs a v₀ =
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
          backHalfShiftCLM α s hα hs (max a 0) v₀
      rw [max_eq_left ha.1]
    have hP_eq_lift : P_j (qMap x₀) =
        qMap ⟨v_H, mem_dirichletStageSpace_of_test T hα hs hH_box hmem_H⟩ := by
      let F_E : ℝ → E := fun a ↦
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
          ⟨backHalfShiftCLM α s hα hs (max a 0) v₀,
            backHalfShiftCLM_mem_dirichletStageSpace hχ hN T hTpos hX hα hs (max a 0)
              (le_max_right a 0) x₀.2⟩
      have hc_exp : Continuous (fun a : ℝ ↦
          Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ))) :=
        Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
      have hFE_cont : Continuous F_E := by
        refine hc_exp.smul ?_
        refine Continuous.subtype_mk ?_ _
        exact (continuous_backHalfShiftCLM α s hα hs v₀).comp (continuous_id.max continuous_const)
      rw [hx_lift, map_smul, ← qMap.intervalIntegral_comp_comm (hFE_cont.intervalIntegrable 0 L),
        dirichletQuotProj_apply]
      change (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
          Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) •
            dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a (qMap x₀) =
        (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L, qMap (F_E a)
      congr 1
      refine intervalIntegral.integral_congr fun a ha ↦ ?_
      rw [Set.uIcc_of_le hL_pos.le] at ha
      dsimp only [F_E]
      have hmax : max a 0 = a := max_eq_left ha.1
      rw [map_smul, dirichletQuotModulatedAction_eq_of_Icc hχ hN T hT hp hpN hpT hX hα hs ha.1 ha.2,
        smul_apply, smul_smul, ← Complex.exp_add]
      have hsub_eq : (⟨backHalfShiftCLM α s hα hs (max a 0) v₀,
            backHalfShiftCLM_mem_dirichletStageSpace hχ hN T hTpos hX hα hs (max a 0)
              (le_max_right a 0) x₀.2⟩ : E) =
          ⟨backHalfShiftCLM α s hα hs a v₀,
            backHalfShiftCLM_mem_dirichletStageSpace hχ hN T hTpos hX hα hs a ha.1 x₀.2⟩ := by
        ext1; simp [hmax]
      rw [hsub_eq, ← dirichletQuotSemigroup_quotMap hχ hN T hT hp hpT hX hα hs ha.1 x₀]
      congr 2
      dsimp only [dirichletPrimeFreq, L]
      push_cast
      have hL_C : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
      field_simp [hL_C]
      ring
    rw [hP_eq_lift]
    let v_j := toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_j)) hmem_j
    let f_diff := H - c₀ • f_j
    have hf_diff_box : IsDirichletFixedBoxTest χ R f_diff :=
      hH_box.sub (hf_j.smul c₀)
    have hmem_diff : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f_diff)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs hf_diff_box
    have hv_diff_eq : toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_diff)) hmem_diff =
        v_H - c₀ • v_j := by
      ext1
      have hpt_sub : dirichletDeplete χ T (twistedHalfLogProfile χ f_diff) =
          dirichletDeplete χ T (twistedHalfLogProfile χ H) -
            c₀ • dirichletDeplete χ T (twistedHalfLogProfile χ f_j) := by
        have htw_sub : twistedHalfLogProfile χ f_diff =
            twistedHalfLogProfile χ H - c₀ • twistedHalfLogProfile χ f_j := by
          ext y
          rw [twistedHalfLogProfile_sub, twistedHalfLogProfile_smul, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul]
        dsimp only [dirichletDeplete]
        rw [htw_sub, map_sub, map_smul]
      filter_upwards [hmem_diff.coeFn_toLp,
        Lp.coeFn_sub v_H (c₀ • v_j),
        hmem_H.coeFn_toLp,
        Lp.coeFn_smul c₀ v_j,
        hmem_j.coeFn_toLp] with x h1 h2 h3 h4 h5
      have h1' : (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_diff)) hmem_diff : ℝ → ℂ) x =
          dirichletDeplete χ T (twistedHalfLogProfile χ f_diff) x := h1
      have h3' : (v_H : ℝ → ℂ) x = dirichletDeplete χ T (twistedHalfLogProfile χ H) x := h3
      have h5' : (v_j : ℝ → ℂ) x = dirichletDeplete χ T (twistedHalfLogProfile χ f_j) x := h5
      rw [h1', h2, Pi.sub_apply, h4, Pi.smul_apply, h3', h5', hpt_sub, Pi.sub_apply, Pi.smul_apply]
    have hrow_zero : ∀ m : ℤ,
        dirichletNormalizedRow χ T p X α s hα hs m
          (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_diff)) hmem_diff) = 0 := by
      intro m
      rw [hv_diff_eq]
      let x_diff : E := ⟨v_H, mem_dirichletStageSpace_of_test T hα hs hH_box hmem_H⟩ -
        c₀ • ⟨v_j, mem_dirichletStageSpace_of_test T hα hs hf_j hmem_j⟩
      have hx_diff_coe : x_diff.1 = v_H - c₀ • v_j := rfl
      rw [← hx_diff_coe, ← dirichletQuotRow_quotMap hχ hN T hT hp hpN hpT hX hα hs m x_diff]
      rw [map_sub, map_smul, map_sub, map_smul, smul_eq_mul,
        ← hP_eq_lift, dirichletQuotRow_proj hχ hN T hT hp hpN hpT hX hα hs m j (qMap x₀)]
      have hej_m : dirichletQuotRow χ T p X α s hα hs m e_j = if m = j then 1 else 0 := by
        dsimp only [e_j]
        rw [dirichletQuotRow_quotMap hχ hN T hT hp hpN hpT hX hα hs m]
        exact hdiag m hmem_j
      rw [hej_m]
      by_cases hmj : m = j
      · simp [hmj, c₀]
      · simp [hmj]
    obtain ⟨g₀, hg₀, hdep⟩ := (dirichletFixedBox_stage_exact_division hχ hN T hT hp hpN hpT hX hα hs hf_diff_box).mpr
      hrow_zero
    have hg₀' : IsDirichletFixedBoxTest χ (X / ∏ q ∈ insert p T, (q : ℝ)) g₀ := by
      rwa [Finset.prod_insert hpT]
    have hmem_g : MemLp (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN (insert p T)
        (fun q hq ↦ by rcases Finset.mem_insert.mp hq with rfl | hqT; exact hp.pos; exact (hT q hqT).1.pos)
        (div_pos hX (Finset.prod_pos fun q hq ↦ by
          rcases Finset.mem_insert.mp hq with rfl | hqT
          · exact_mod_cast hp.pos
          · exact_mod_cast (hT q hqT).1.pos)) hα hs hg₀'
    have hstrip_mem : toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_diff)) hmem_diff ∈
        dirichletStageSpace χ (insert p T) X α s hα hs := by
      have hcomm : dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀) =
          dirichletDeplete χ T (twistedHalfLogProfile χ f_diff) := by
        rw [dirichletDeplete_insert χ hpT, LinearMap.comp_apply,
          dirichletDeplete_commute_step χ p T (twistedHalfLogProfile χ g₀),
          ← twistedHalfLogProfile_testDepleteStep χ hp.pos, hdep]
      have hmem_g' : toDirichletStrip α s (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) hmem_g ∈
          dirichletStageSpace χ (insert p T) X α s hα hs :=
        mem_dirichletStageSpace_of_test (insert p T) hα hs hg₀' hmem_g
      have hcoincide : toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_diff)) hmem_diff =
          toDirichletStrip α s (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) hmem_g := by
        ext1
        filter_upwards [hmem_diff.coeFn_toLp, hmem_g.coeFn_toLp] with x hx1 hx2
        have hx1' : (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_diff)) hmem_diff : ℝ → ℂ) x =
            dirichletDeplete χ T (twistedHalfLogProfile χ f_diff) x := hx1
        have hx2' : (toDirichletStrip α s (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) hmem_g : ℝ → ℂ) x =
            dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀) x := hx2
        rw [hx1', hx2', hcomm]
      rwa [hcoincide]
    have hq_sub : qMap (⟨v_H, mem_dirichletStageSpace_of_test T hα hs hH_box hmem_H⟩ -
        c₀ • ⟨v_j, mem_dirichletStageSpace_of_test T hα hs hf_j hmem_j⟩) = 0 :=
      (dirichletStageQuotMap_eq_zero_iff hχ hN T hT hp hpT hX hα hs _).mpr (by
        change v_H - c₀ • v_j ∈ _
        rw [← hv_diff_eq]
        exact hstrip_mem)
    rw [map_sub, map_smul, sub_eq_zero] at hq_sub
    exact hq_sub
  have h0 := hdiff_zero ⟨q.1, q.2.1⟩
  rw [sub_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.comp_apply, dirichletStageQuotMap_self, sub_eq_zero] at h0
  exact h0

theorem dirichletQuot_eq_zero_of_forall_proj_eq_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {q : dirichletStageQuotient χ T p X α s hα hs}
    (hq : ∀ j : ℤ, dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j q = 0) :
    q = 0 := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  let g : ℝ → ℂ := fun a ↦ ⟪q, τ a q⟫_ℂ
  have hg_cont : Continuous g :=
    continuous_const.inner (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs q)
  have hf_zero : ∀ j : ℤ, fourierCoeffOn hL_pos g j = 0 := by
    intro j
    rw [fourierCoeffOn_eq_integral]
    have hc_exp : Continuous (fun a : ℝ ↦
        Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) :=
      Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
    have hint : IntervalIntegrable (fun a : ℝ ↦
        Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q)
        volume 0 L :=
      (hc_exp.smul (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs q)).intervalIntegrable 0 L
    have hinner_comm : ⟪q, ∫ a in (0 : ℝ)..L,
        Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q⟫_ℂ =
        ∫ a in (0 : ℝ)..L,
          ⟪q, Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q⟫_ℂ :=
      ((innerSL ℂ q).intervalIntegral_comp_comm hint).symm
    have hrew : (fun x : ℝ ↦ fourier (-j) (x : AddCircle (L - 0)) • g x) =
        fun x : ℝ ↦ ⟪q, Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (x : ℂ)) • τ x q⟫_ℂ := by
      funext x
      rw [fourier_coe_apply, smul_eq_mul, inner_smul_right]
      congr 1
      push_cast
      rw [sub_zero]
      ring_nf
    rw [hrew, ← hinner_comm, sub_zero, one_div, Complex.real_smul, Complex.ofReal_inv,
      ← inner_smul_right, ← dirichletQuotProj_apply hχ hN T hT hp hpN hpT hX hα hs j q,
      hq j, inner_zero_right]
  have hmemL2 : MemLp g 2 (volume.restrict (Set.Ioc 0 L)) := by
    have : IsFiniteMeasure (volume.restrict (Set.Ioc 0 L)) := ⟨by simp [Real.volume_Ioc]⟩
    let M_g : ℝ := sSup ((fun a : ℝ ↦ ‖g a‖) '' Set.Icc 0 L) + 1
    have hbdd : BddAbove ((fun a : ℝ ↦ ‖g a‖) '' Set.Icc 0 L) :=
      (isCompact_Icc.image hg_cont.norm).bddAbove
    have hbdd_ae : ∀ᵐ a ∂(volume.restrict (Set.Ioc 0 L)), ‖g a‖ ≤ M_g := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      exact (le_csSup hbdd ⟨a, Set.Ioc_subset_Icc_self ha, rfl⟩).trans (by linarith)
    exact MemLp.of_bound hg_cont.aestronglyMeasurable M_g hbdd_ae
  have hparseval := tsum_sq_fourierCoeffOn hL_pos hmemL2
  simp only [hf_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    tsum_zero, sub_zero, smul_eq_mul] at hparseval
  have hint_zero : ∫ a in (0 : ℝ)..L, ‖g a‖ ^ 2 = 0 := by
    rcases mul_eq_zero.mp hparseval.symm with hinv | hint0
    · exfalso; exact (inv_ne_zero hL_pos.ne') hinv
    · exact hint0
  have hg0 : g 0 = 0 := by
    by_contra hne
    have hpos0 : 0 < ‖g 0‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hne)
    have hcont_norm : Continuous (fun a : ℝ ↦ ‖g a‖ ^ 2) := (hg_cont.norm).pow 2
    obtain ⟨δ₀, hδ₀, hball⟩ := Metric.continuousAt_iff.mp hcont_norm.continuousAt (‖g 0‖ ^ 2 / 2)
      (by linarith)
    let δ : ℝ := min L (δ₀ / 2)
    have hδ_pos : 0 < δ := lt_min hL_pos (by linarith)
    have hδ_le_L : δ ≤ L := min_le_left L (δ₀ / 2)
    have hδ_lt_δ₀ : δ < δ₀ := (min_le_right L (δ₀ / 2)).trans_lt (by linarith)
    have hnorm_int1 : IntervalIntegrable (fun _ : ℝ ↦ ‖g 0‖ ^ 2 / 2) volume 0 δ :=
      intervalIntegrable_const
    have hnorm_int2 : IntervalIntegrable (fun a : ℝ ↦ ‖g a‖ ^ 2) volume 0 δ :=
      hcont_norm.intervalIntegrable 0 δ
    have hlow : δ * (‖g 0‖ ^ 2 / 2) ≤ ∫ a in (0 : ℝ)..δ, ‖g a‖ ^ 2 := by
      have hc : ∫ _ in (0 : ℝ)..δ, ‖g 0‖ ^ 2 / 2 = δ * (‖g 0‖ ^ 2 / 2) := by
        rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
      rw [← hc]
      refine intervalIntegral.integral_mono_on hδ_pos.le hnorm_int1 hnorm_int2 fun a ha ↦ ?_
      have hdist : dist a 0 < δ₀ := by
        rw [Real.dist_eq, sub_zero, abs_of_nonneg ha.1]
        exact ha.2.trans_lt hδ_lt_δ₀
      have hba := hball hdist
      rw [Real.dist_eq, abs_lt] at hba
      linarith [hba.1]
    have hmono : ∫ a in (0 : ℝ)..δ, ‖g a‖ ^ 2 ≤ ∫ a in (0 : ℝ)..L, ‖g a‖ ^ 2 := by
      rw [intervalIntegral.integral_of_le hδ_pos.le, intervalIntegral.integral_of_le hL_pos.le]
      exact setIntegral_mono_set
        (hcont_norm.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall fun _ ↦ sq_nonneg _)
        (Filter.Eventually.of_forall fun _ hx ↦ Set.Ioc_subset_Ioc_right hδ_le_L hx)
    have hcontra : δ * (‖g 0‖ ^ 2 / 2) ≤ 0 := hlow.trans (hmono.trans_eq hint_zero)
    linarith [mul_pos hδ_pos (by linarith : 0 < ‖g 0‖ ^ 2 / 2)]
  have hqq : ⟪q, q⟫_ℂ = 0 := by
    have h0' : τ 0 q = q :=
      congrFun (congrArg DFunLike.coe
        (dirichletQuotModulatedAction_zero hχ hN T hT hp hpN hpT hX hα hs)) q
    simpa [g, h0'] using hg0
  exact inner_self_eq_zero.mp hqq

theorem dirichletQuot_eq_zero_of_forall_row_eq_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {q : dirichletStageQuotient χ T p X α s hα hs}
    (hq : ∀ j : ℤ, dirichletQuotRow χ T p X α s hα hs j q = 0) :
    q = 0 := by
  refine dirichletQuot_eq_zero_of_forall_proj_eq_zero hχ hN T hT hp hpN hpT hX hα hs fun j ↦ ?_
  obtain ⟨f, hf_box, _, hf_diag, _⟩ :=
    dirichletFixedBox_cardinal_lifts hχ hN T hT hp hpN hpT hX hα hs
  rw [dirichletQuotProj_eq_row_smul hχ hN T hT hp hpN hpT hX hα hs (hf_box j) j (hf_diag j) q,
    hq j, zero_smul]

private theorem continuous_nonneg_intervalIntegral_eq_zero_at_zero
    {f : ℝ → ℝ} (hf_cont : Continuous f) (hf_nn : ∀ a : ℝ, 0 ≤ f a)
    {L : ℝ} (hL : 0 < L) (hint0 : ∫ a in (0 : ℝ)..L, f a = 0) :
    f 0 = 0 := by
  by_contra hne
  have hpos0 : 0 < f 0 := lt_of_le_of_ne (hf_nn 0) (Ne.symm hne)
  obtain ⟨δ₀, hδ₀, hball⟩ := Metric.continuousAt_iff.mp hf_cont.continuousAt (f 0 / 2)
    (by linarith)
  let δ : ℝ := min L (δ₀ / 2)
  have hδ_pos : 0 < δ := lt_min hL (by linarith)
  have hδ_le_L : δ ≤ L := min_le_left L (δ₀ / 2)
  have hδ_lt_δ₀ : δ < δ₀ := (min_le_right L (δ₀ / 2)).trans_lt (by linarith)
  have hlow : δ * (f 0 / 2) ≤ ∫ a in (0 : ℝ)..δ, f a := by
    have hc : ∫ _ in (0 : ℝ)..δ, f 0 / 2 = δ * (f 0 / 2) := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
    rw [← hc]
    refine intervalIntegral.integral_mono_on hδ_pos.le intervalIntegrable_const
      (hf_cont.intervalIntegrable 0 δ) fun a ha ↦ ?_
    have hdist : dist a 0 < δ₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ha.1]
      exact ha.2.trans_lt hδ_lt_δ₀
    have hba := hball hdist
    rw [Real.dist_eq, abs_lt] at hba
    linarith [hba.1]
  have hmono : ∫ a in (0 : ℝ)..δ, f a ≤ ∫ a in (0 : ℝ)..L, f a := by
    rw [intervalIntegral.integral_of_le hδ_pos.le, intervalIntegral.integral_of_le hL.le]
    exact setIntegral_mono_set
      (hf_cont.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall fun _ ↦ hf_nn _)
      (Filter.Eventually.of_forall fun _ hx ↦ Set.Ioc_subset_Ioc_right hδ_le_L hx)
  have hcontra : δ * (f 0 / 2) ≤ 0 := hlow.trans (hmono.trans_eq hint0)
  linarith [mul_pos hδ_pos (by linarith : 0 < f 0 / 2)]

/-- Averaged Hilbert space `Q_avg` on the quotient `dirichletStageQuotient χ T p X α s hα hs`,
equipped with the circle-averaged inner product making `dirichletAvgModulatedAction` unitary and
every `dirichletAvgProj j` self-adjoint.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
structure DirichletAvgQuotient {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    (X α s : ℝ) (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) where
  val : dirichletStageQuotient χ T p X α s hα hs

section DirichletAvgQuotientSec

variable {N : ℕ} [NeZero N]
  {χ : DirichletCharacter ℂ N} {hχ : χ.IsPrimitive} {hN : 1 < N}
  {T : Finset ℕ} {hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N}
  {p : ℕ} {hp : p.Prime} {hpN : p.Coprime N} {hpT : p ∉ T}
  {X α s : ℝ} {hX : 0 < X} {hα : 0 ≤ α} {hs : 0 ≤ s}

@[ext]
theorem DirichletAvgQuotient.ext
    {x y : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs}
    (h : x.val = y.val) : x = y := by
  cases x; cases y; congr

instance instAddCommGroupDirichletAvgQuotient :
    AddCommGroup (DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) where
  add x y := ⟨x.val + y.val⟩
  add_assoc x y z := DirichletAvgQuotient.ext (add_assoc x.val y.val z.val)
  zero := ⟨0⟩
  zero_add x := DirichletAvgQuotient.ext (zero_add x.val)
  add_zero x := DirichletAvgQuotient.ext (add_zero x.val)
  nsmul n x := ⟨n • x.val⟩
  nsmul_zero x := DirichletAvgQuotient.ext (zero_smul ℕ x.val)
  nsmul_succ n x := DirichletAvgQuotient.ext (by
    change (n + 1) • x.val = n • x.val + x.val
    exact succ_nsmul x.val n)
  neg x := ⟨-x.val⟩
  sub x y := ⟨x.val - y.val⟩
  sub_eq_add_neg x y := DirichletAvgQuotient.ext (sub_eq_add_neg x.val y.val)
  zsmul n x := ⟨n • x.val⟩
  zsmul_zero' x := DirichletAvgQuotient.ext (zero_smul ℤ x.val)
  zsmul_succ' n x := DirichletAvgQuotient.ext (by
    change ((n.succ : ℕ) : ℤ) • x.val = (n : ℤ) • x.val + x.val
    exact SubNegMonoid.zsmul_succ' n x.val)
  zsmul_neg' n x := DirichletAvgQuotient.ext (SubNegMonoid.zsmul_neg' n x.val)
  neg_add_cancel x := DirichletAvgQuotient.ext (neg_add_cancel x.val)
  add_comm x y := DirichletAvgQuotient.ext (add_comm x.val y.val)

instance instModuleComplexDirichletAvgQuotient :
    Module ℂ (DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) where
  smul c x := ⟨c • x.val⟩
  one_smul x := DirichletAvgQuotient.ext (one_smul ℂ x.val)
  mul_smul c d x := DirichletAvgQuotient.ext (mul_smul c d x.val)
  smul_zero c := DirichletAvgQuotient.ext (smul_zero c)
  smul_add c x y := DirichletAvgQuotient.ext (smul_add c x.val y.val)
  add_smul c d x := DirichletAvgQuotient.ext (add_smul c d x.val)
  zero_smul x := DirichletAvgQuotient.ext (zero_smul ℂ x.val)

@[simp]
theorem DirichletAvgQuotient.val_zero :
    (0 : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs).val = 0 := rfl

@[simp]
theorem DirichletAvgQuotient.val_add
    (x y : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    (x + y).val = x.val + y.val := rfl

@[simp]
theorem DirichletAvgQuotient.val_sub
    (x y : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    (x - y).val = x.val - y.val := rfl

@[simp]
theorem DirichletAvgQuotient.val_neg
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    (-x).val = -x.val := rfl

@[simp]
theorem DirichletAvgQuotient.val_smul (c : ℂ)
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    (c • x).val = c • x.val := rfl

private theorem continuous_dirichletAvgIntegrand
    (x y : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    Continuous (fun a : ℝ ↦
      ⟪dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a x.val,
        dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a y.val⟫_ℂ) :=
  (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs x.val).inner
    (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs y.val)

/-- Inner product core on `DirichletAvgQuotient` given by averaging the quotient inner product over
one period `[0, log p]`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
@[instance_reducible]
noncomputable def dirichletAvgCore
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    (X α s : ℝ) (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    InnerProductSpace.Core ℂ
      (DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) where
  inner x y := ((Real.log p)⁻¹ : ℂ) * ∫ a in (0 : ℝ)..Real.log p,
    ⟪dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a x.val,
      dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a y.val⟫_ℂ
  conj_inner_symm x y := by
    let L : ℝ := Real.log p
    let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
    let f : ℝ → ℂ := fun a ↦ ⟪τ a y.val, τ a x.val⟫_ℂ
    have hf_int : IntervalIntegrable f volume 0 L :=
      (continuous_dirichletAvgIntegrand y x).intervalIntegrable 0 L
    have hconj_comm := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm hf_int).symm
    change starRingEnd ℂ ((L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L, f a) = _
    rw [← Complex.ofReal_inv, map_mul, Complex.conj_ofReal, Complex.ofReal_inv]
    congr 1
    rw [show starRingEnd ℂ (∫ a in (0 : ℝ)..L, f a) =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) (∫ a in (0 : ℝ)..L, f a) from rfl, hconj_comm]
    refine intervalIntegral.integral_congr fun a _ ↦ ?_
    exact inner_conj_symm (τ a x.val) (τ a y.val)
  re_inner_nonneg x := by
    let L : ℝ := Real.log p
    have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
    let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
    let f : ℝ → ℂ := fun a ↦ ⟪τ a x.val, τ a x.val⟫_ℂ
    have hf_int : IntervalIntegrable f volume 0 L :=
      (continuous_dirichletAvgIntegrand x x).intervalIntegrable 0 L
    have hre_comm := (Complex.reCLM.intervalIntegral_comp_comm hf_int).symm
    change 0 ≤ RCLike.re ((L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L, f a)
    rw [← Complex.ofReal_inv, RCLike.re_eq_complex_re, Complex.re_ofReal_mul,
      show (∫ a in (0 : ℝ)..L, f a).re = Complex.reCLM (∫ a in (0 : ℝ)..L, f a) from rfl,
      hre_comm]
    refine mul_nonneg (inv_nonneg.mpr hL_pos.le) ?_
    refine intervalIntegral.integral_nonneg hL_pos.le fun a _ ↦ ?_
    exact inner_self_nonneg (𝕜 := ℂ) (x := τ a x.val)
  definite x hx := by
    let L : ℝ := Real.log p
    have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
    let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
    let f : ℝ → ℂ := fun a ↦ ⟪τ a x.val, τ a x.val⟫_ℂ
    have hf_int : IntervalIntegrable f volume 0 L :=
      (continuous_dirichletAvgIntegrand x x).intervalIntegrable 0 L
    have hre_comm := (Complex.reCLM.intervalIntegral_comp_comm hf_int).symm
    have hre0 : (((L⁻¹ : ℝ) : ℂ) * ∫ a in (0 : ℝ)..L, f a).re = 0 := by
      have hx' : (L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L, f a = 0 := hx
      rw [← Complex.ofReal_inv] at hx'
      rw [hx', Complex.zero_re]
    rw [Complex.re_ofReal_mul, show (∫ a in (0 : ℝ)..L, f a).re =
        Complex.reCLM (∫ a in (0 : ℝ)..L, f a) from rfl, hre_comm] at hre0
    have hint0 : ∫ a in (0 : ℝ)..L, (f a).re = 0 := by
      rcases mul_eq_zero.mp hre0 with hinv | h0
      · exfalso; exact (inv_ne_zero hL_pos.ne') hinv
      · exact h0
    have hcont_re : Continuous (fun a : ℝ ↦ (f a).re) :=
      Complex.continuous_re.comp (continuous_dirichletAvgIntegrand x x)
    have hf0 : (f 0).re = 0 :=
      continuous_nonneg_intervalIntegral_eq_zero_at_zero hcont_re
        (fun a ↦ inner_self_nonneg (𝕜 := ℂ) (x := τ a x.val)) hL_pos hint0
    have h0' : τ 0 x.val = x.val :=
      congrFun (congrArg DFunLike.coe
        (dirichletQuotModulatedAction_zero hχ hN T hT hp hpN hpT hX hα hs)) x.val
    have hsq0 : ‖x.val‖ ^ 2 = 0 := by
      have hre_sq : (f 0).re = ‖x.val‖ ^ 2 := by
        dsimp only [f]
        rw [h0', ← RCLike.re_eq_complex_re, ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
      linarith
    have hval0 : x.val = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hsq0)
    exact DirichletAvgQuotient.ext hval0
  add_left x y z := by
    let L : ℝ := Real.log p
    let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
    have h1 : IntervalIntegrable (fun a : ℝ ↦ ⟪τ a x.val, τ a z.val⟫_ℂ) volume 0 L :=
      (continuous_dirichletAvgIntegrand x z).intervalIntegrable 0 L
    have h2 : IntervalIntegrable (fun a : ℝ ↦ ⟪τ a y.val, τ a z.val⟫_ℂ) volume 0 L :=
      (continuous_dirichletAvgIntegrand y z).intervalIntegrable 0 L
    change ((L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L, ⟪τ a (x + y).val, τ a z.val⟫_ℂ) = _
    have hadd : (fun a : ℝ ↦ ⟪τ a (x + y).val, τ a z.val⟫_ℂ) =
        fun a : ℝ ↦ ⟪τ a x.val, τ a z.val⟫_ℂ + ⟪τ a y.val, τ a z.val⟫_ℂ := by
      funext a
      rw [DirichletAvgQuotient.val_add, map_add, inner_add_left]
    rw [hadd, intervalIntegral.integral_add h1 h2, mul_add]
  smul_left x y r := by
    let L : ℝ := Real.log p
    let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
    change ((L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L, ⟪τ a (r • x).val, τ a y.val⟫_ℂ) = _
    have hsmul : (fun a : ℝ ↦ ⟪τ a (r • x).val, τ a y.val⟫_ℂ) =
        fun a : ℝ ↦ starRingEnd ℂ r * ⟪τ a x.val, τ a y.val⟫_ℂ := by
      funext a
      rw [DirichletAvgQuotient.val_smul, map_smul, inner_smul_left]
    rw [hsmul, intervalIntegral.integral_const_mul]
    ring

noncomputable instance instNormedAddCommGroupDirichletAvgQuotient :
    NormedAddCommGroup (DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :=
  (dirichletAvgCore χ hχ hN T hT p hp hpN hpT X α s hX hα hs).toNormedAddCommGroup

noncomputable instance instInnerProductSpaceDirichletAvgQuotient :
    InnerProductSpace ℂ (DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :=
  InnerProductSpace.ofCore
    (dirichletAvgCore χ hχ hN T hT p hp hpN hpT X α s hX hα hs).toCore

theorem inner_dirichletAvgQuotient_def
    (x y : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    ⟪x, y⟫_ℂ = ((Real.log p)⁻¹ : ℂ) * ∫ a in (0 : ℝ)..Real.log p,
      ⟪dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a x.val,
        dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a y.val⟫_ℂ := rfl

theorem norm_sq_dirichletAvgQuotient_def
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    ‖x‖ ^ 2 = (Real.log p)⁻¹ * ∫ a in (0 : ℝ)..Real.log p,
      ‖dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a x.val‖ ^ 2 := by
  let L : ℝ := Real.log p
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  have hf_int : IntervalIntegrable (fun a : ℝ ↦ ⟪τ a x.val, τ a x.val⟫_ℂ) volume 0 L :=
    (continuous_dirichletAvgIntegrand x x).intervalIntegrable 0 L
  have hre_comm := (Complex.reCLM.intervalIntegral_comp_comm hf_int).symm
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), inner_dirichletAvgQuotient_def,
    RCLike.re_eq_complex_re]
  change ((L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L, ⟪τ a x.val, τ a x.val⟫_ℂ).re = _
  rw [← Complex.ofReal_inv, Complex.re_ofReal_mul,
    show (∫ a in (0 : ℝ)..L, ⟪τ a x.val, τ a x.val⟫_ℂ).re =
      Complex.reCLM (∫ a in (0 : ℝ)..L, ⟪τ a x.val, τ a x.val⟫_ℂ) from rfl, hre_comm]
  congr 1
  refine intervalIntegral.integral_congr fun a _ ↦ ?_
  change (⟪τ a x.val, τ a x.val⟫_ℂ).re = ‖τ a x.val‖ ^ 2
  rw [← RCLike.re_eq_complex_re, ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]

theorem norm_dirichletAvgQuotient_le
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    ‖x‖ ≤ dirichletQuotActionBound p α s * ‖x.val‖ := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let M : ℝ := dirichletQuotActionBound p α s
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  have hM_nonneg : 0 ≤ M := dirichletQuotActionBound_pos.le
  have hcont_norm_sq : Continuous (fun a : ℝ ↦ ‖τ a x.val‖ ^ 2) :=
    ((continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs x.val).norm).pow 2
  have hsq : ‖x‖ ^ 2 ≤ (M * ‖x.val‖) ^ 2 := by
    rw [norm_sq_dirichletAvgQuotient_def]
    have hbd : ∀ a ∈ Set.Icc 0 L, ‖τ a x.val‖ ^ 2 ≤ (M * ‖x.val‖) ^ 2 := fun a _ ↦ by
      have hn : ‖τ a x.val‖ ≤ M * ‖x.val‖ :=
        (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (norm_dirichletQuotModulatedAction_le hχ hN T hT hp hpT hX hα hs a) (norm_nonneg _))
      exact sq_le_sq' (by linarith [norm_nonneg (τ a x.val), mul_nonneg hM_nonneg (norm_nonneg x.val)]) hn
    have hint_le : ∫ a in (0 : ℝ)..L, ‖τ a x.val‖ ^ 2 ≤ ∫ _ in (0 : ℝ)..L, (M * ‖x.val‖) ^ 2 :=
      intervalIntegral.integral_mono_on hL_pos.le (hcont_norm_sq.intervalIntegrable 0 L)
        intervalIntegrable_const hbd
    have hconst : ∫ _ in (0 : ℝ)..L, (M * ‖x.val‖) ^ 2 = L * (M * ‖x.val‖) ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
    calc L⁻¹ * ∫ a in (0 : ℝ)..L, ‖τ a x.val‖ ^ 2
        ≤ L⁻¹ * (L * (M * ‖x.val‖) ^ 2) :=
          mul_le_mul_of_nonneg_left (hint_le.trans_eq hconst) (inv_pos.mpr hL_pos).le
      _ = (M * ‖x.val‖) ^ 2 := by field_simp [hL_pos.ne']
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg x), Real.sqrt_sq (mul_nonneg hM_nonneg (norm_nonneg x.val))] at hsqrt

theorem norm_val_le_dirichletAvgQuotient
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    ‖x.val‖ ≤ dirichletQuotActionBound p α s * ‖x‖ := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let M : ℝ := dirichletQuotActionBound p α s
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  have hM_pos : 0 < M := dirichletQuotActionBound_pos
  have hcont_norm_sq : Continuous (fun a : ℝ ↦ ‖τ a x.val‖ ^ 2) :=
    ((continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs x.val).norm).pow 2
  have hsq : ‖x.val‖ ^ 2 ≤ (M * ‖x‖) ^ 2 := by
    have hpt : ∀ a : ℝ, ‖x.val‖ ^ 2 ≤ M ^ 2 * ‖τ a x.val‖ ^ 2 := fun a ↦ by
      have hinv_id : τ (-a) (τ a x.val) = x.val := by
        have h1 := congrFun (congrArg DFunLike.coe
          (dirichletQuotModulatedAction_add hχ hN T hT hp hpN hpT hX hα hs (-a) a)) x.val
        have h0 := congrFun (congrArg DFunLike.coe
          (dirichletQuotModulatedAction_zero hχ hN T hT hp hpN hpT hX hα hs)) x.val
        rw [ContinuousLinearMap.comp_apply, neg_add_cancel] at h1
        rw [← h1, h0]
        rfl
      have hle : ‖x.val‖ ≤ M * ‖τ a x.val‖ := by
        conv_lhs => rw [← hinv_id]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (norm_dirichletQuotModulatedAction_le hχ hN T hT hp hpT hX hα hs (-a)) (norm_nonneg _))
      calc ‖x.val‖ ^ 2 ≤ (M * ‖τ a x.val‖) ^ 2 :=
            sq_le_sq' (by linarith [norm_nonneg x.val, mul_nonneg hM_pos.le (norm_nonneg (τ a x.val))]) hle
        _ = M ^ 2 * ‖τ a x.val‖ ^ 2 := by ring
    have hint_le : ∫ _ in (0 : ℝ)..L, ‖x.val‖ ^ 2 ≤
        ∫ a in (0 : ℝ)..L, M ^ 2 * ‖τ a x.val‖ ^ 2 :=
      intervalIntegral.integral_mono_on hL_pos.le intervalIntegrable_const
        (continuous_const.mul hcont_norm_sq |>.intervalIntegrable 0 L) fun a _ ↦ hpt a
    have hconst : ∫ _ in (0 : ℝ)..L, ‖x.val‖ ^ 2 = L * ‖x.val‖ ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
    rw [hconst, intervalIntegral.integral_const_mul] at hint_le
    have havg : ‖x‖ ^ 2 = L⁻¹ * ∫ a in (0 : ℝ)..L, ‖τ a x.val‖ ^ 2 :=
      norm_sq_dirichletAvgQuotient_def x
    calc ‖x.val‖ ^ 2 = L⁻¹ * (L * ‖x.val‖ ^ 2) := by field_simp [hL_pos.ne']
      _ ≤ L⁻¹ * (M ^ 2 * ∫ a in (0 : ℝ)..L, ‖τ a x.val‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hint_le (inv_pos.mpr hL_pos).le
      _ = M ^ 2 * (L⁻¹ * ∫ a in (0 : ℝ)..L, ‖τ a x.val‖ ^ 2) := by ring
      _ = (M * ‖x‖) ^ 2 := by rw [← havg]; ring
  have hsqrt := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg x.val), Real.sqrt_sq (mul_nonneg hM_pos.le (norm_nonneg x))] at hsqrt

/-- Canonical continuous linear equivalence `Q_avg ≃L[ℂ] Q` identifying `DirichletAvgQuotient`
with `dirichletStageQuotient`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
noncomputable def dirichletAvgEquivQ
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    (X α s : ℝ) (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs ≃L[ℂ]
      dirichletStageQuotient χ T p X α s hα hs :=
  { toFun := fun x ↦ x.val
    invFun := fun q ↦ ⟨q⟩
    left_inv := fun ⟨_⟩ ↦ rfl
    right_inv := fun _ ↦ rfl
    map_add' := fun _ _ ↦ rfl
    map_smul' := fun _ _ ↦ rfl
    continuous_toFun := AddMonoidHomClass.continuous_of_bound
      ({ toFun := fun x ↦ x.val, map_zero' := rfl, map_add' := fun _ _ ↦ rfl } :
        DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs →+
          dirichletStageQuotient χ T p X α s hα hs)
      (dirichletQuotActionBound p α s) norm_val_le_dirichletAvgQuotient
    continuous_invFun := AddMonoidHomClass.continuous_of_bound
      ({ toFun := fun q ↦ ⟨q⟩, map_zero' := rfl, map_add' := fun _ _ ↦ rfl } :
        dirichletStageQuotient χ T p X α s hα hs →+
          DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs)
      (dirichletQuotActionBound p α s) fun q ↦ norm_dirichletAvgQuotient_le ⟨q⟩ }

@[simp]
theorem dirichletAvgEquivQ_apply
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs x = x.val := rfl

@[simp]
theorem dirichletAvgEquivQ_symm_apply
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    (dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs).symm q = ⟨q⟩ := rfl

noncomputable instance instCompleteSpaceDirichletAvgQuotient :
    CompleteSpace (DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu ↦ ?_
  let e := dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs
  have hv : CauchySeq (fun n ↦ (u n).val) :=
    e.toContinuousLinearMap.lipschitzWith.uniformContinuous.comp_cauchySeq hu
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hv
  refine ⟨⟨q⟩, ?_⟩
  have heq : (fun n ↦ e.symm (u n).val) = u := funext fun _ ↦ rfl
  rw [← heq]
  exact (e.symm.continuous.tendsto q).comp hq

/-- Modulated circle action `τ_avg` on `DirichletAvgQuotient`. -/
noncomputable def dirichletAvgModulatedAction
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    (X α s : ℝ) (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (u : ℝ) :
    DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs →L[ℂ]
      DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs :=
  (dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs).symm.toContinuousLinearMap.comp
    ((dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u).comp
      (dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs).toContinuousLinearMap)

@[simp]
theorem dirichletAvgModulatedAction_val (u : ℝ)
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    (dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u x).val =
      dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u x.val := rfl

theorem dirichletAvgModulatedAction_zero :
    dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs 0 =
      ContinuousLinearMap.id ℂ _ := by
  ext1 x
  apply DirichletAvgQuotient.ext
  rw [dirichletAvgModulatedAction_val,
    dirichletQuotModulatedAction_zero hχ hN T hT hp hpN hpT hX hα hs]
  rfl

theorem dirichletAvgModulatedAction_add (u v : ℝ) :
    dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs (u + v) =
      (dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u).comp
        (dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs v) := by
  ext1 x
  apply DirichletAvgQuotient.ext
  rw [dirichletAvgModulatedAction_val, ContinuousLinearMap.comp_apply,
    dirichletAvgModulatedAction_val, dirichletAvgModulatedAction_val,
    dirichletQuotModulatedAction_add hχ hN T hT hp hpN hpT hX hα hs u v,
    ContinuousLinearMap.comp_apply]

theorem dirichletAvgModulatedAction_periodic :
    Function.Periodic
      (dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs) (Real.log p) := by
  intro u
  ext1 x
  apply DirichletAvgQuotient.ext
  rw [dirichletAvgModulatedAction_val, dirichletAvgModulatedAction_val,
    dirichletQuotModulatedAction_periodic hχ hN T hT hp hpT hX hα hs u]

theorem inner_dirichletAvgModulatedAction (u : ℝ)
    (x y : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    ⟪dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u x,
      dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u y⟫_ℂ = ⟪x, y⟫_ℂ := by
  let L : ℝ := Real.log p
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  let f : ℝ → ℂ := fun a ↦ ⟪τ a x.val, τ a y.val⟫_ℂ
  have hf_per : Function.Periodic f L := fun a ↦ by
    dsimp only [f, τ, L]
    have h := dirichletQuotModulatedAction_periodic hχ hN T hT hp hpT hX hα hs a
    rw [h]
  have hf_shift : (fun a : ℝ ↦ ⟪τ a (τ u x.val), τ a (τ u y.val)⟫_ℂ) = fun a : ℝ ↦ f (a + u) := by
    funext a
    dsimp only [f, τ]
    have h := dirichletQuotModulatedAction_add hχ hN T hT hp hpN hpT hX hα hs a u
    rw [h, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have hcomp : ∫ a in (0 : ℝ)..L, f (a + u) = ∫ a in u..(u + L), f a := by
    simpa only [zero_add, add_comm L u] using
      (intervalIntegral.integral_comp_add_right f u (a := 0) (b := L))
  have hper_int : ∫ a in u..(u + L), f a = ∫ a in (0 : ℝ)..L, f a := by
    simpa only [zero_add] using (hf_per.intervalIntegral_add_eq 0 u).symm
  rw [inner_dirichletAvgQuotient_def, inner_dirichletAvgQuotient_def]
  simp only [dirichletAvgModulatedAction_val]
  rw [hf_shift, hcomp, hper_int]

theorem norm_dirichletAvgModulatedAction_apply (u : ℝ)
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    ‖dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u x‖ = ‖x‖ := by
  have hsq : ‖dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u x‖ ^ 2 =
      ‖x‖ ^ 2 := by
    rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ),
      inner_dirichletAvgModulatedAction u x x]
  have hsqrt := congrArg Real.sqrt hsq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt

theorem inner_dirichletAvgModulatedAction_adj (u : ℝ)
    (x y : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    ⟪dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u x, y⟫_ℂ =
      ⟪x, dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs (-u) y⟫_ℂ := by
  let τ_avg := dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs
  have hcancel : τ_avg (-u) (τ_avg u x) = x := by
    have h1 := congrFun (congrArg DFunLike.coe
      (dirichletAvgModulatedAction_add (χ := χ) (hχ := hχ) (hN := hN) (T := T) (hT := hT)
        (p := p) (hp := hp) (hpN := hpN) (hpT := hpT) (X := X) (α := α) (s := s)
        (hX := hX) (hα := hα) (hs := hs) (-u) u)) x
    rw [ContinuousLinearMap.comp_apply, neg_add_cancel, dirichletAvgModulatedAction_zero] at h1
    exact h1.symm
  calc ⟪τ_avg u x, y⟫_ℂ
      = ⟪τ_avg (-u) (τ_avg u x), τ_avg (-u) y⟫_ℂ := (inner_dirichletAvgModulatedAction (-u) _ _).symm
    _ = ⟪x, τ_avg (-u) y⟫_ℂ := by rw [hcancel]

/-- Spectral projection `P_j` lifted to `DirichletAvgQuotient`. -/
noncomputable def dirichletAvgProj
    (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    (p : ℕ) (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    (X α s : ℝ) (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (j : ℤ) :
    DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs →L[ℂ]
      DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs :=
  (dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs).symm.toContinuousLinearMap.comp
    ((dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j).comp
      (dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs).toContinuousLinearMap)

@[simp]
theorem dirichletAvgProj_val (j : ℤ)
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    (dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j x).val =
      dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j x.val := rfl

theorem dirichletAvgProj_apply (j : ℤ)
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j x =
      ((Real.log p)⁻¹ : ℂ) • ∫ a in (0 : ℝ)..Real.log p,
        Complex.exp (-(2 * Real.pi * (j : ℝ) / Real.log p : ℂ) * Complex.I * (a : ℂ)) •
          dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs a x := by
  let L : ℝ := Real.log p
  let e := dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  have hc_exp : Continuous (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hint : IntervalIntegrable (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a x.val) volume 0 L :=
    (hc_exp.smul (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs x.val)).intervalIntegrable 0 L
  have hcomm := (e.symm.toContinuousLinearMap.intervalIntegral_comp_comm hint).symm
  apply DirichletAvgQuotient.ext
  have he_symm : (dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j x.val) =
      e (e.symm ((L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
        Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a x.val)) := by
    rw [dirichletQuotProj_apply, ContinuousLinearEquiv.apply_symm_apply]
  change (dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j x.val) =
    e ((L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) •
        dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs a x)
  rw [he_symm]
  apply congrArg e
  change (L⁻¹ : ℂ) • e.symm.toContinuousLinearMap (∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a x.val) =
    (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) •
        dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs a x
  rw [hcomm]
  apply congrArg ((L⁻¹ : ℂ) • ·)
  refine intervalIntegral.integral_congr fun a _ ↦ ?_
  rw [map_smul]
  rfl

theorem continuous_dirichletAvgModulatedAction_apply
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    Continuous (fun a : ℝ ↦
      dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs a x) :=
  (dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs).symm.continuous.comp
    (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs x.val)

theorem dirichletAvgProj_isSelfAdjoint (j : ℤ) :
    IsSelfAdjoint (dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j) := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hL_C : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
  let P_j := dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j
  let τ_avg := dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  change ⟪P_j x, y⟫_ℂ = ⟪x, P_j y⟫_ℂ
  have hc_exp : Continuous (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hint_x : IntervalIntegrable (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a x) volume 0 L :=
    (hc_exp.smul (continuous_dirichletAvgModulatedAction_apply x)).intervalIntegrable 0 L
  have hint_y : IntervalIntegrable (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a y) volume 0 L :=
    (hc_exp.smul (continuous_dirichletAvgModulatedAction_apply y)).intervalIntegrable 0 L
  have hinner_L : ⟪P_j x, y⟫_ℂ = (L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L,
      Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) * ⟪τ_avg a x, y⟫_ℂ := by
    dsimp only [P_j]
    rw [dirichletAvgProj_apply]
    change ⟪(L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
        Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a x, y⟫_ℂ = _
    rw [← Complex.ofReal_inv, inner_smul_left, Complex.conj_ofReal, Complex.ofReal_inv]
    congr 1
    have hconj : ⟪∫ a in (0 : ℝ)..L,
          Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a x, y⟫_ℂ =
        starRingEnd ℂ ⟪y, ∫ a in (0 : ℝ)..L,
          Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a x⟫_ℂ :=
      (inner_conj_symm _ _).symm
    have hy_comm : ⟪y, ∫ a in (0 : ℝ)..L,
          Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a x⟫_ℂ =
        ∫ a in (0 : ℝ)..L,
          ⟪y, Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a x⟫_ℂ :=
      ((innerSL ℂ y).intervalIntegral_comp_comm hint_x).symm
    rw [hconj, hy_comm]
    have hc_in : IntervalIntegrable (fun a : ℝ ↦
        ⟪y, Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a x⟫_ℂ) volume 0 L := by
      refine (continuous_const.inner (hc_exp.smul (continuous_dirichletAvgModulatedAction_apply x))).intervalIntegrable 0 L
    have hconj_comm := ((Complex.conjCLE : ℂ →L[ℝ] ℂ).intervalIntegral_comp_comm hc_in).symm
    rw [show starRingEnd ℂ (∫ a in (0 : ℝ)..L,
        ⟪y, Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a x⟫_ℂ) =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) (∫ a in (0 : ℝ)..L,
          ⟪y, Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a x⟫_ℂ) from rfl,
      hconj_comm]
    refine intervalIntegral.integral_congr fun a _ ↦ ?_
    change starRingEnd ℂ ⟪y, _⟫_ℂ = _
    rw [inner_conj_symm, inner_smul_left]
    congr 1
    have hexp_conj : starRingEnd ℂ (Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) =
        Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) := by
      rw [← Complex.exp_conj]
      congr 1
      have hc0 : starRingEnd ℂ ((2 * Real.pi * (j : ℝ) / L : ℂ)) =
          ((2 * Real.pi * (j : ℝ) / L : ℝ) : ℂ) := by
        rw [show (2 * Real.pi * (j : ℝ) / L : ℂ) = ((2 * Real.pi * (j : ℝ) / L : ℝ) : ℂ) by push_cast; rfl,
          Complex.conj_ofReal]
      rw [map_mul, map_mul, map_neg, hc0, Complex.conj_I, Complex.conj_ofReal]
      push_cast; ring
    exact hexp_conj
  have hinner_R : ⟪x, P_j y⟫_ℂ = (L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) * ⟪x, τ_avg a y⟫_ℂ := by
    dsimp only [P_j]
    rw [dirichletAvgProj_apply]
    change ⟪x, (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
        Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a y⟫_ℂ = _
    have hx_comm : ⟪x, ∫ a in (0 : ℝ)..L,
          Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a y⟫_ℂ =
        ∫ a in (0 : ℝ)..L,
          ⟪x, Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ_avg a y⟫_ℂ :=
      ((innerSL ℂ x).intervalIntegral_comp_comm hint_y).symm
    rw [inner_smul_right, hx_comm]
    congr 1
    refine intervalIntegral.integral_congr fun a _ ↦ ?_
    rw [inner_smul_right]
  rw [hinner_L, hinner_R]
  congr 1
  have hsub_var : ∫ b in (0 : ℝ)..L,
      Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * ((L - b : ℝ) : ℂ)) *
        ⟪τ_avg (L - b) x, y⟫_ℂ =
      ∫ a in (0 : ℝ)..L,
        Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) * ⟪τ_avg a x, y⟫_ℂ := by
    simpa only [sub_zero, sub_self] using
      (intervalIntegral.integral_comp_sub_left
        (fun a : ℝ ↦
          Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) * ⟪τ_avg a x, y⟫_ℂ)
        L (a := 0) (b := L))
  rw [← hsub_var]
  refine intervalIntegral.integral_congr fun b _ ↦ ?_
  have hexp_shift : Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * ((L - b : ℝ) : ℂ)) =
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (b : ℂ)) := by
    have harg : (2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * ((L - b : ℝ) : ℂ) =
        -(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (b : ℂ) + (j : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; field_simp [hL_C]; ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hτ_shift : τ_avg (-(L - b)) y = τ_avg b y := by
    have hneg : -(L - b) + L = b := by ring
    calc τ_avg (-(L - b)) y = τ_avg (-(L - b) + L) y := by
          have hp := congrFun (congrArg DFunLike.coe
            (dirichletAvgModulatedAction_periodic (χ := χ) (hχ := hχ) (hN := hN) (T := T)
              (hT := hT) (p := p) (hp := hp) (hpN := hpN) (hpT := hpT) (X := X) (α := α)
              (s := s) (hX := hX) (hα := hα) (hs := hs) (-(L - b)))) y
          exact hp.symm
      _ = τ_avg b y := by rw [hneg]
  rw [hexp_shift, inner_dirichletAvgModulatedAction_adj, hτ_shift]

theorem dirichletAvgProj_comp_ne {m j : ℤ}
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs m
        (dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j x) =
      if m = j then dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j x else 0 := by
  apply DirichletAvgQuotient.ext
  rw [dirichletAvgProj_val, dirichletAvgProj_val,
    dirichletQuotProj_comp_ne hχ hN T hT hp hpN hpT hX hα hs x.val]
  split_ifs <;> rfl

theorem dirichletAvgProj_eq_row_smul
    {f_j : 𝓢(ℝ, ℂ)} (hf_j : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f_j)
    (j : ℤ) (hdiag : ∀ m : ℤ,
      ∀ hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f_j)) 2
          (intervalSobolevMeasure volume id (-α) α s false),
        dirichletNormalizedRow χ T p X α s hα hs m
          (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_j)) hmem) =
          if m = j then 1 else 0)
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    let hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
    let hR_pos : 0 < X / ∏ q ∈ T, (q : ℝ) :=
      div_pos hX (Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hTpos q hq))
    let hmem_j : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f_j)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs hf_j
    let e_j : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs :=
      ⟨dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
        ⟨toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_j)) hmem_j,
          mem_dirichletStageSpace_of_test T hα hs hf_j hmem_j⟩⟩
    dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j x =
      dirichletQuotRow χ T p X α s hα hs j x.val • e_j := by
  intro hTpos hR_pos hmem_j e_j
  apply DirichletAvgQuotient.ext
  rw [dirichletAvgProj_val, DirichletAvgQuotient.val_smul]
  exact dirichletQuotProj_eq_row_smul hχ hN T hT hp hpN hpT hX hα hs hf_j j hdiag x.val

/-- Unconditional orthonormal basis (Hilbert basis) of `DirichletAvgQuotient` (hence an
unconditional Schauder basis of `dirichletStageQuotient`) consisting of normalized joint
eigenvectors of the modulated circle action `dirichletAvgModulatedAction` / `dirichletQuotModulatedAction`.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletFixedBox_unconditional_basis {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ∃ b : HilbertBasis ℤ ℂ
        (DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs),
      (∀ (j : ℤ) (u : ℝ),
        dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u (b j) =
          Complex.exp ((2 * Real.pi * (j : ℝ) / Real.log p : ℂ) * Complex.I * (u : ℂ)) • b j) ∧
      (∀ (j : ℤ) (u : ℝ),
        dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u (b j).val =
          Complex.exp ((2 * Real.pi * (j : ℝ) / Real.log p : ℂ) * Complex.I * (u : ℂ)) • (b j).val) ∧
      (∀ m j : ℤ,
        dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs m (b j) =
          if m = j then b j else 0) ∧
      (∀ j : ℤ, dirichletQuotRow χ T p X α s hα hs j (b j).val ≠ 0) ∧
      (∀ m j : ℤ, m ≠ j → dirichletQuotRow χ T p X α s hα hs m (b j).val = 0) := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
  let hR_pos : 0 < X / ∏ q ∈ T, (q : ℝ) :=
    div_pos hX (Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hTpos q hq))
  obtain ⟨f, hf_box, _, hf_diag, _⟩ :=
    dirichletFixedBox_cardinal_lifts hχ hN T hT hp hpN hpT hX hα hs
  let Q_avg := DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs
  let e_raw : ℤ → Q_avg := fun j ↦
    let hmem_j := dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs (hf_box j)
    ⟨dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
      ⟨toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ (f j))) hmem_j,
        mem_dirichletStageSpace_of_test T hα hs (hf_box j) hmem_j⟩⟩
  have he_eig : ∀ (j : ℤ) (u : ℝ),
      dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u (e_raw j) =
        Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) • e_raw j := by
    intro j u
    apply DirichletAvgQuotient.ext
    rw [dirichletAvgModulatedAction_val, DirichletAvgQuotient.val_smul]
    exact dirichletQuotModulatedAction_eigenvec hχ hN T hT hp hpN hpT hX hα hs (hf_box j) j
      (hf_diag j) u
  have he_proj : ∀ m j : ℤ,
      dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs m (e_raw j) =
        if m = j then e_raw j else 0 := by
    intro m j
    rw [dirichletAvgProj_apply]
    have hrew : (fun a : ℝ ↦
        Complex.exp (-(2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) •
          dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs a (e_raw j)) =
        fun a : ℝ ↦
          (Complex.exp (-(2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) *
            Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) • e_raw j := by
      funext a
      rw [he_eig j a, smul_smul]
    change (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
        Complex.exp (-(2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) •
          dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs a (e_raw j) =
      if m = j then e_raw j else 0
    rw [hrew, intervalIntegral.integral_smul_const, smul_smul,
      intervalIntegral_exp_neg_eq_zero hL_pos]
    split_ifs <;> simp
  have he_row : ∀ m j : ℤ,
      dirichletQuotRow χ T p X α s hα hs m (e_raw j).val = if m = j then 1 else 0 := by
    intro m j
    dsimp only [e_raw]
    rw [dirichletQuotRow_quotMap hχ hN T hT hp hpN hpT hX hα hs m]
    exact hf_diag j m (dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs (hf_box j))
  have he_nz : ∀ j : ℤ, e_raw j ≠ 0 := fun j hj ↦ by
    have h1 := he_row j j
    rw [hj, DirichletAvgQuotient.val_zero, map_zero] at h1
    simp only [↓reduceIte] at h1
    exact zero_ne_one h1
  have he_norm_pos : ∀ j : ℤ, 0 < ‖e_raw j‖ := fun j ↦ norm_pos_iff.mpr (he_nz j)
  have he_ortho : ∀ m j : ℤ, m ≠ j → ⟪e_raw m, e_raw j⟫_ℂ = 0 := fun m j hmj ↦ by
    have hPm : dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs m (e_raw m) = e_raw m := by
      rw [he_proj m m]; simp
    have hPm_j : dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs m (e_raw j) = 0 := by
      rw [he_proj m j]; simp [hmj]
    have hsa := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
      (dirichletAvgProj_isSelfAdjoint (χ := χ) (hχ := hχ) (hN := hN) (T := T) (hT := hT)
        (p := p) (hp := hp) (hpN := hpN) (hpT := hpT) (X := X) (α := α) (s := s)
        (hX := hX) (hα := hα) (hs := hs) m)
    calc ⟪e_raw m, e_raw j⟫_ℂ
        = ⟪dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs m (e_raw m), e_raw j⟫_ℂ := by
            rw [hPm]
      _ = ⟪e_raw m, dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs m (e_raw j)⟫_ℂ :=
            hsa (e_raw m) (e_raw j)
      _ = 0 := by rw [hPm_j, inner_zero_right]
  let b_vec : ℤ → Q_avg := fun j ↦ ((‖e_raw j‖⁻¹ : ℝ) : ℂ) • e_raw j
  have hb_on : Orthonormal ℂ b_vec := by
    rw [orthonormal_iff_ite]
    intro m j
    by_cases hmj : m = j
    · subst hmj
      simp only [↓reduceIte, b_vec]
      rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, inner_self_eq_norm_sq_to_K]
      have hne : (‖e_raw m‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (he_norm_pos m).ne'
      rw [Complex.ofReal_inv]
      calc (‖e_raw m‖ : ℂ)⁻¹ * ((‖e_raw m‖ : ℂ)⁻¹ * (‖e_raw m‖ : ℂ) ^ 2)
          = ((‖e_raw m‖ : ℂ)⁻¹ * (‖e_raw m‖ : ℂ)) * ((‖e_raw m‖ : ℂ)⁻¹ * (‖e_raw m‖ : ℂ)) := by ring
        _ = 1 * 1 := by rw [inv_mul_cancel₀ hne]
        _ = 1 := one_mul 1
    · simp only [hmj, ↓reduceIte, b_vec]
      rw [inner_smul_left, inner_smul_right, he_ortho m j hmj, mul_zero, mul_zero]
  have hb_span : (Submodule.span ℂ (Set.range b_vec))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx_e : ∀ j : ℤ, ⟪e_raw j, x⟫_ℂ = 0 := fun j ↦ by
      have hmem : b_vec j ∈ Submodule.span ℂ (Set.range b_vec) :=
        Submodule.subset_span ⟨j, rfl⟩
      have h0 : ⟪b_vec j, x⟫_ℂ = 0 := hx (b_vec j) hmem
      dsimp only [b_vec] at h0
      rw [inner_smul_left, Complex.conj_ofReal] at h0
      rcases mul_eq_zero.mp h0 with hinv | hinner
      · exfalso
        exact (Complex.ofReal_ne_zero.mpr (inv_ne_zero (he_norm_pos j).ne')) hinv
      · exact hinner
    have hx_row : ∀ j : ℤ, dirichletQuotRow χ T p X α s hα hs j x.val = 0 := fun j ↦ by
      have hPm : dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j (e_raw j) = e_raw j := by
        rw [he_proj j j]; simp
      have hsa := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp
        (dirichletAvgProj_isSelfAdjoint (χ := χ) (hχ := hχ) (hN := hN) (T := T) (hT := hT)
          (p := p) (hp := hp) (hpN := hpN) (hpT := hpT) (X := X) (α := α) (s := s)
          (hX := hX) (hα := hα) (hs := hs) j)
      have hproj_x : dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j x =
          dirichletQuotRow χ T p X α s hα hs j x.val • e_raw j :=
        dirichletAvgProj_eq_row_smul (hf_box j) j (hf_diag j) x
      have h0 := hx_e j
      conv_lhs at h0 => rw [← hPm]
      have hsa' : ⟪dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j (e_raw j), x⟫_ℂ =
          ⟪e_raw j, dirichletAvgProj χ hχ hN T hT p hp hpN hpT X α s hX hα hs j x⟫_ℂ :=
        hsa (e_raw j) x
      rw [hsa', hproj_x, inner_smul_right, inner_self_eq_norm_sq_to_K] at h0
      rcases mul_eq_zero.mp h0 with hrow0 | hnorm0
      · exact hrow0
      · exfalso
        have hpos : (‖e_raw j‖ : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (he_norm_pos j).ne')
        exact hpos hnorm0
    exact DirichletAvgQuotient.ext
      (dirichletQuot_eq_zero_of_forall_row_eq_zero hχ hN T hT hp hpN hpT hX hα hs hx_row)
  let b : HilbertBasis ℤ ℂ Q_avg := HilbertBasis.mkOfOrthogonalEqBot hb_on hb_span
  have hb_coe : ∀ j : ℤ, b j = b_vec j := fun j ↦ by
    rw [HilbertBasis.coe_mkOfOrthogonalEqBot]
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · intro j u
    rw [hb_coe j]
    dsimp only [b_vec]
    rw [map_smul, he_eig j u, smul_comm]
  · intro j u
    rw [hb_coe j]
    dsimp only [b_vec]
    rw [DirichletAvgQuotient.val_smul, map_smul]
    dsimp only [e_raw]
    rw [dirichletQuotModulatedAction_eigenvec hχ hN T hT hp hpN hpT hX hα hs (hf_box j) j (hf_diag j) u,
      smul_comm]
  · intro m j
    rw [hb_coe j]
    dsimp only [b_vec]
    rw [map_smul, he_proj m j]
    split_ifs <;> simp
  · intro j
    rw [hb_coe j]
    dsimp only [b_vec]
    rw [DirichletAvgQuotient.val_smul, map_smul, he_row j j, smul_eq_mul]
    simp only [↓reduceIte, mul_one]
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (he_norm_pos j).ne')
  · intro m j hmj
    rw [hb_coe j]
    dsimp only [b_vec]
    rw [DirichletAvgQuotient.val_smul, map_smul, he_row m j, smul_eq_mul]
    simp only [hmj, ↓reduceIte, mul_zero]

end DirichletAvgQuotientSec

end CircleActionAndTraceNorm

end RiemannMasullo.Isolated
