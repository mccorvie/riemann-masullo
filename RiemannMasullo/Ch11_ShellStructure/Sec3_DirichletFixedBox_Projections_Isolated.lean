module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Circle_Isolated
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes (Projections)

Eigenprojections and smooth lifts on the fixed-box stage quotient for primitive `χ`.

Nothing outside the `Sec3_DirichletFixedBox*` / `Sec3_RatBridge*` isolated stack imports this module.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField RiemannMasullo Set Topology
open scoped BigOperators ContDiff FourierTransform NNReal Real SchwartzMap

namespace RiemannMasullo.Isolated

section CircleActionAndTraceNorm

open MeasureTheory Filter Topology Real
open scoped InnerProductSpace Convolution ENNReal

theorem norm_dirichletQuotModulatedAction_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (u : ℝ) :
    ‖dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u‖ ≤
      Real.exp (Real.log p / 2 + α * Real.log p) * (2 + 2 * Real.log p ^ 2) ^ (s / 4) := by
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  let r := Int.fract (u / Real.log p) * Real.log p
  have hr0 : 0 ≤ r := mul_nonneg (Int.fract_nonneg _) hL_pos.le
  have hrL : r ≤ Real.log p := by
    calc r ≤ 1 * Real.log p := mul_le_mul_of_nonneg_right (Int.fract_lt_one _).le hL_pos.le
      _ = Real.log p := one_mul _
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun q ↦ ?_
  have hexp_norm : ‖Complex.exp (-(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) *
      Complex.I * (r : ℂ)))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (-(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I * (r : ℂ))).re = 0 := by
      rw [Complex.neg_re, Complex.mul_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre, Real.exp_zero]
  have hq_norm : ‖dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u q‖ =
      ‖Complex.exp (-(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I * (r : ℂ))) •
        dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r hr0 q‖ := by
    dsimp [dirichletQuotModulatedAction]
    rw [smul_apply]
    rfl
  rw [hq_norm, norm_smul, hexp_norm, one_mul]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  refine (norm_dirichletQuotSemigroup_le hχ hN T hT hp hpT hX hα hs hr0).trans ?_
  have h1 : Real.exp (r / 2 + α * |r|) ≤ Real.exp (Real.log p / 2 + α * Real.log p) := by
    apply Real.exp_le_exp.mpr
    rw [abs_of_nonneg hr0]
    nlinarith [hα]
  have h2 : (2 + 2 * r ^ 2) ^ (s / 4) ≤ (2 + 2 * Real.log p ^ 2) ^ (s / 4) := by
    apply Real.rpow_le_rpow (by positivity) _ (by positivity)
    have hr2 : r ^ 2 ≤ Real.log p ^ 2 := sq_le_sq' (by linarith) hrL
    linarith
  exact mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le

theorem continuous_dirichletQuotModulatedAction_apply {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    Continuous (fun u : ℝ ↦ dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u q) := by
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  let L := Real.log p
  let t0 := Complex.arg (χ (p : ZMod N)) / L
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  have hτ_Icc : ContinuousOn (fun u : ℝ ↦ τ u q) (Set.Icc 0 L) := by
    have hsemi := continuous_dirichletQuotSemigroup_apply hχ hN T hT hp hpT hX hα hs q
    have hexp_cont : ContinuousOn (fun a : ℝ ↦ Complex.exp (-((t0 : ℂ) * Complex.I * (a : ℂ))))
        (Set.Icc 0 L) :=
      (Complex.continuous_exp.comp
        ((continuous_const.mul Complex.continuous_ofReal).neg)).continuousOn
    have hprod : ContinuousOn (fun a : ℝ ↦
        Complex.exp (-((t0 : ℂ) * Complex.I * (a : ℂ))) •
          (if ha : 0 ≤ a then dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha q else 0))
        (Set.Icc 0 L) :=
      hexp_cont.smul (hsemi.mono Set.Icc_subset_Ici_self)
    refine hprod.congr fun a ha ↦ ?_
    dsimp [τ, t0, L]
    rw [dirichletQuotModulatedAction_eq_of_Icc hχ hN T hT hp hpN hpT hX hα hs ha.1 ha.2,
      smul_apply]
    simp only [ha.1, ↓reduceDIte, Complex.ofReal_div]
  rw [continuous_iff_continuousAt]
  intro u₀
  have hper := dirichletQuotModulatedAction_periodic hχ hN T hT hp hpT hX hα hs
  have hadd_eq : (fun u : ℝ ↦ τ u q) = fun u : ℝ ↦ τ u₀ (τ (u - u₀) q) := by
    funext u
    have hu : u = u₀ + (u - u₀) := by ring
    have hcomp := congrFun (congrArg DFunLike.coe
      (dirichletQuotModulatedAction_add hχ hN T hT hp hpN hpT hX hα hs u₀ (u - u₀))) q
    rw [ContinuousLinearMap.comp_apply] at hcomp
    conv_lhs => rw [hu]
    exact hcomp
  rw [hadd_eq]
  refine (τ u₀).continuous.continuousAt.comp ?_
  have hcont0 : ContinuousAt (fun δ : ℝ ↦ τ δ q) 0 := by
    have hR_tend : Tendsto (fun δ : ℝ ↦ τ δ q) (𝓝[≥] 0) (𝓝 (τ 0 q)) := by
      have hnhds : Set.Icc 0 L ∈ 𝓝[≥] (0 : ℝ) := Icc_mem_nhdsGE hL_pos
      exact (hτ_Icc 0 ⟨le_rfl, hL_pos.le⟩).mono_left (nhdsWithin_le_iff.mpr hnhds)
    have hL_tend : Tendsto (fun δ : ℝ ↦ τ δ q) (𝓝[<] 0) (𝓝 (τ 0 q)) := by
      have hev : (fun δ : ℝ ↦ τ δ q) =ᶠ[𝓝[<] 0] fun δ : ℝ ↦ τ (δ + L) q := by
        filter_upwards with δ
        exact congrFun (congrArg DFunLike.coe (hper δ).symm) q
      rw [tendsto_congr' hev]
      have hL_eq : τ L q = τ 0 q := by
        have := hper 0
        rw [zero_add] at this
        exact congrFun (congrArg DFunLike.coe this) q
      rw [← hL_eq]
      have htend_add : Tendsto (fun δ : ℝ ↦ δ + L) (𝓝[<] 0) (𝓝[Set.Icc 0 L] L) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have hadd0 : ContinuousAt (fun δ : ℝ ↦ δ + L) 0 :=
            (continuous_id.add (continuous_const : Continuous fun _ : ℝ ↦ L)).continuousAt
          rw [ContinuousAt, zero_add] at hadd0
          exact hadd0.mono_left nhdsWithin_le_nhds
        · filter_upwards [Ioo_mem_nhdsLT (by linarith : -L < 0)] with δ hδ
          exact ⟨by linarith [hδ.1], by linarith [hδ.2]⟩
      exact (hτ_Icc L ⟨hL_pos.le, le_rfl⟩).tendsto.comp htend_add
    rw [ContinuousAt, ← nhdsLT_sup_nhdsGE (0 : ℝ)]
    exact tendsto_sup.mpr ⟨hL_tend, hR_tend⟩
  refine ContinuousAt.comp (g := fun δ : ℝ ↦ τ δ q) ?_
    ((continuous_id.sub (continuous_const : Continuous fun _ : ℝ ↦ u₀)).continuousAt)
  simpa using hcont0

theorem dirichletQuotRow_modulatedAction {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (j : ℤ) (u : ℝ) (q : dirichletStageQuotient χ T p X α s hα hs) :
    dirichletQuotRow χ T p X α s hα hs j
        (dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u q) =
      Complex.exp ((2 * Real.pi * (j : ℝ) / Real.log p : ℂ) * Complex.I * (u : ℂ)) *
        dirichletQuotRow χ T p X α s hα hs j q := by
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  let L := Real.log p
  let t0 := Complex.arg (χ (p : ZMod N)) / L
  have hsemigroup_Icc : ∀ a : ℝ, ∀ ha0 : 0 ≤ a, ∀ q0 : dirichletStageQuotient χ T p X α s hα hs,
      dirichletQuotRow χ T p X α s hα hs j
          (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha0 q0) =
        Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          dirichletQuotRow χ T p X α s hα hs j q0 := by
    intro a ha0 q0
    let E := dirichletStageSpace χ T X α s hα hs
    let qMap := dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
    let L_map : E →L[ℂ] ℂ := (dirichletQuotRow χ T p X α s hα hs j).comp
      ((dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha0).comp qMap)
    let R_map : E →L[ℂ] ℂ := Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) •
      ((dirichletQuotRow χ T p X α s hα hs j).comp qMap)
    have hker : ∀ x, (L_map - R_map) x = 0 := by
      refine clm_zero_on_dirichletStageSpace χ T X α s hα hs (L_map - R_map) fun f₀ hf₀ hmem ↦ ?_
      rw [sub_apply, sub_eq_zero]
      change dirichletQuotRow χ T p X α s hα hs j
          (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha0 (qMap ⟨_, _⟩)) =
        Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          dirichletQuotRow χ T p X α s hα hs j (qMap ⟨_, _⟩)
      rw [dirichletQuotSemigroup_quotMap, dirichletQuotRow_quotMap hχ hN T hT hp hpN hpT hX hα hs,
        dirichletQuotRow_quotMap hχ hN T hT hp hpN hpT hX hα hs]
      have hR_pos : 0 < X / ∏ q ∈ T, (q : ℝ) :=
        div_pos hX (Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hT q hq).1.pos)
      have hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
      let fa := schwartzScale (Real.exp (-a)) (Real.exp_pos _).ne' f₀
      have ⟨hfa_box, hshift_eq⟩ :=
        backHalfShiftCLM_apply_depleted_scale hχ hN T hTpos hR_pos hα hs hf₀ a ha0
      have hmem_a : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ fa)) 2
          (intervalSobolevMeasure volume id (-α) α s false) :=
        dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs hfa_box
      dsimp only
      rw [hshift_eq hmem hmem_a,
        dirichletNormalizedRow_apply_depleted hχ hN T hT hp hpN hpT hX hα hs hfa_box j,
        dirichletNormalizedRow_apply_depleted hχ hN T hT hp hpN hpT hX hα hs hf₀ j]
      have hrew : (fun y : ℝ ↦ (𝓕 fa) (Real.exp y) *
            Complex.exp ((1 - (dirichletPrimeFreq χ p j : ℂ) * Complex.I) * (y : ℂ))) =
          fun y : ℝ ↦ Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
            ((𝓕 f₀) (Real.exp (y + a)) *
              Complex.exp ((1 - (dirichletPrimeFreq χ p j : ℂ) * Complex.I) * ((y + a : ℝ) : ℂ))) := by
        ext y
        dsimp only [fa]
        rw [fourier_schwartzScale _ (Real.exp_pos _).ne' f₀ (Real.exp y),
          abs_of_pos (Real.exp_pos _), Real.exp_neg, inv_inv, div_inv_eq_mul,
          mul_comm (Real.exp y) (Real.exp a)]
        have hexp_prod : Real.exp y * Real.exp a = Real.exp (y + a) := (Real.exp_add y a).symm
        have hexp_a : (Real.exp a : ℂ) = Complex.exp ((a : ℂ)) := Complex.ofReal_exp a
        have harg : (1 - (dirichletPrimeFreq χ p j : ℂ) * Complex.I) * (y : ℂ) + (a : ℂ) =
            (dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ) +
              (1 - (dirichletPrimeFreq χ p j : ℂ) * Complex.I) * ((y + a : ℝ) : ℂ) := by
          push_cast; ring
        rw [mul_comm (Real.exp a) (Real.exp y), hexp_prod, hexp_a]
        calc (Complex.exp (a : ℂ) * (𝓕 f₀) (Real.exp (y + a))) *
              Complex.exp ((1 - (dirichletPrimeFreq χ p j : ℂ) * Complex.I) * (y : ℂ))
            = (𝓕 f₀) (Real.exp (y + a)) *
                (Complex.exp ((1 - (dirichletPrimeFreq χ p j : ℂ) * Complex.I) * (y : ℂ)) *
                  Complex.exp (a : ℂ)) := by ring
          _ = (𝓕 f₀) (Real.exp (y + a)) *
                Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ) +
                  (1 - (dirichletPrimeFreq χ p j : ℂ) * Complex.I) * ((y + a : ℝ) : ℂ)) := by
              rw [← Complex.exp_add, harg]
          _ = _ := by rw [Complex.exp_add]; ring
      rw [logFourierProfile, logFourierProfile, hrew, integral_const_mul]
      congr 1
      exact MeasureTheory.integral_add_right_eq_self (μ := volume) (fun y : ℝ ↦ (𝓕 f₀) (Real.exp y) *
        Complex.exp ((1 - (dirichletPrimeFreq χ p j : ℂ) * Complex.I) * (y : ℂ))) a
    have hq0 := dirichletStageQuotMap_self hχ hN T hT hp hpT hX hα hs q0
    have h0 := hker ⟨q0.1, q0.2.1⟩
    rw [sub_apply, sub_eq_zero] at h0
    dsimp [L_map, R_map, qMap] at h0
    simp only [ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul, hq0] at h0
    exact h0
  let r := Int.fract (u / L) * L
  have hr_nn : 0 ≤ r := mul_nonneg (Int.fract_nonneg _) hL_pos.le
  dsimp [dirichletQuotModulatedAction]
  rw [smul_apply, map_smul, smul_eq_mul, hsemigroup_Icc r hr_nn q]
  rw [← mul_assoc, ← Complex.exp_add]
  have hfreq_sub : (dirichletPrimeFreq χ p j : ℂ) - (t0 : ℂ) =
      (2 * Real.pi * (j : ℝ) / L : ℂ) := by
    dsimp [dirichletPrimeFreq, t0, L]
    push_cast
    rw [add_div, add_sub_cancel_left]
  have hr_mod : (u : ℂ) = (r : ℂ) + ((⌊u / L⌋ : ℤ) : ℂ) * (L : ℂ) := by
    have := Int.floor_add_fract (u / L)
    have hr_real : u = r + ((⌊u / L⌋ : ℤ) : ℝ) * L := by
      dsimp [r]
      calc u = (u / L) * L := (div_mul_cancel₀ u hL_pos.ne').symm
        _ = ((⌊u / L⌋ : ℝ) + Int.fract (u / L)) * L := by rw [this]
        _ = _ := by ring
    exact_mod_cast hr_real
  have hexp_eq : Complex.exp
      ((-((t0 : ℂ) * Complex.I * (r : ℂ)) + (dirichletPrimeFreq χ p j : ℂ) * Complex.I * (r : ℂ))) =
      Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) := by
    have hdiff : -((t0 : ℂ) * Complex.I * (r : ℂ)) + (dirichletPrimeFreq χ p j : ℂ) * Complex.I * (r : ℂ) =
        (2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (r : ℂ) := by
      rw [← hfreq_sub]; ring
    rw [hdiff, hr_mod]
    have hL_C : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
    have harg : (2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * ((r : ℂ) + ((⌊u / L⌋ : ℤ) : ℂ) * (L : ℂ)) =
        (2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (r : ℂ) +
          ((j * ⌊u / L⌋ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast
      field_simp [hL_C]
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  congr 1

theorem dirichletQuotModulatedAction_eigenvec {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀)
    (j : ℤ) (hdiag : ∀ m : ℤ,
      ∀ hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
          (intervalSobolevMeasure volume id (-α) α s false),
        dirichletNormalizedRow χ T p X α s hα hs m
          (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem) =
          if m = j then 1 else 0) :
    let hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
    let hR_pos : 0 < X / ∏ q ∈ T, (q : ℝ) :=
      div_pos hX (Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hTpos q hq))
    let hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs hf₀
    let e_j := dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
      ⟨toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem,
        mem_dirichletStageSpace_of_test T hα hs hf₀ hmem⟩
    ∀ u : ℝ, dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u e_j =
      Complex.exp ((2 * Real.pi * (j : ℝ) / Real.log p : ℂ) * Complex.I * (u : ℂ)) • e_j := by
  intro hTpos hR_pos hmem e_j u
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  let L := Real.log p
  let t0 := Complex.arg (χ (p : ZMod N)) / L
  let r := Int.fract (u / L) * L
  have hr0 : 0 ≤ r := mul_nonneg (Int.fract_nonneg _) hL_pos.le
  have hrL : r ≤ L := by
    calc r ≤ 1 * L := mul_le_mul_of_nonneg_right (Int.fract_lt_one _).le hL_pos.le
      _ = L := one_mul _
  have hτ_r : dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u e_j =
      Complex.exp (-((t0 : ℂ) * Complex.I * (r : ℂ))) •
        dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r hr0 e_j := rfl
  let fr := schwartzScale (Real.exp (-r)) (Real.exp_pos _).ne' f₀
  have ⟨hfr_box, hshift_eq⟩ :=
    backHalfShiftCLM_apply_depleted_scale hχ hN T hTpos hR_pos hα hs hf₀ r hr0
  let c_mod := Complex.exp (-((t0 : ℂ) * Complex.I * (r : ℂ)))
  let c_eig := Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (r : ℂ))
  let htest : 𝓢(ℝ, ℂ) := c_mod • fr - c_eig • f₀
  have htest_box : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) htest :=
    (hfr_box.smul c_mod).sub (hf₀.smul c_eig)
  have hmem_fr : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ fr)) 2
      (intervalSobolevMeasure volume id (-α) α s false) :=
    dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs hfr_box
  have hmem_test : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ htest)) 2
      (intervalSobolevMeasure volume id (-α) α s false) :=
    dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs htest_box
  have hdiff_strip : c_mod • toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ fr)) hmem_fr -
      c_eig • toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem =
      toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ htest)) hmem_test := by
    refine toDirichletStrip_sub_smul_congr_ae hmem_fr hmem hmem_test fun x ↦ ?_
    dsimp only [htest]
    rw [twistedHalfLogProfile_sub, twistedHalfLogProfile_smul, twistedHalfLogProfile_smul,
      map_sub, map_smul, map_smul]
    simp
  have hvan_all : ∀ m : ℤ, dirichletNormalizedRow χ T p X α s hα hs m
      (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ htest)) hmem_test) = 0 := by
    intro m
    rw [← hdiff_strip, map_sub, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    have hfr_eval : dirichletNormalizedRow χ T p X α s hα hs m
        (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ fr)) hmem_fr) =
        Complex.exp ((dirichletPrimeFreq χ p m : ℂ) * Complex.I * (r : ℂ)) *
          dirichletNormalizedRow χ T p X α s hα hs m
            (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem) := by
      have h1 : dirichletQuotRow χ T p X α s hα hs m
          (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r hr0 e_j) =
          Complex.exp ((dirichletPrimeFreq χ p m : ℂ) * Complex.I * (r : ℂ)) *
            dirichletQuotRow χ T p X α s hα hs m e_j := by
        have hm := dirichletQuotRow_modulatedAction hχ hN T hT hp hpN hpT hX hα hs m r e_j
        rw [dirichletQuotModulatedAction_eq_of_Icc hχ hN T hT hp hpN hpT hX hα hs hr0 hrL,
          smul_apply, map_smul, smul_eq_mul] at hm
        have hfreq_sub : (dirichletPrimeFreq χ p m : ℂ) =
            (t0 : ℂ) + (2 * Real.pi * (m : ℝ) / L : ℂ) := by
          dsimp [dirichletPrimeFreq, t0, L]; push_cast; rw [add_div]
        calc dirichletQuotRow χ T p X α s hα hs m
              (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r hr0 e_j)
            = Complex.exp ((t0 : ℂ) * Complex.I * (r : ℂ)) *
                (Complex.exp (-((t0 : ℂ) * Complex.I * (r : ℂ))) *
                  dirichletQuotRow χ T p X α s hα hs m
                    (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r hr0 e_j)) := by
                rw [← mul_assoc, ← Complex.exp_add]; simp
          _ = Complex.exp ((t0 : ℂ) * Complex.I * (r : ℂ)) *
                (Complex.exp ((2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (r : ℂ)) *
                  dirichletQuotRow χ T p X α s hα hs m e_j) := by
                have hm' : Complex.exp (-((t0 : ℂ) * Complex.I * (r : ℂ))) *
                      dirichletQuotRow χ T p X α s hα hs m
                        (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r hr0 e_j) =
                    Complex.exp ((2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (r : ℂ)) *
                      dirichletQuotRow χ T p X α s hα hs m e_j := by
                  simpa [t0, L] using hm
                rw [hm']
          _ = Complex.exp ((dirichletPrimeFreq χ p m : ℂ) * Complex.I * (r : ℂ)) *
                dirichletQuotRow χ T p X α s hα hs m e_j := by
                rw [← mul_assoc, ← Complex.exp_add, hfreq_sub]; congr 2; ring
      have h2 : dirichletQuotRow χ T p X α s hα hs m
          (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r hr0 e_j) =
          dirichletNormalizedRow χ T p X α s hα hs m
            (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ fr)) hmem_fr) := by
        dsimp [e_j]
        rw [dirichletQuotSemigroup_quotMap, dirichletQuotRow_quotMap hχ hN T hT hp hpN hpT hX hα hs]
        exact congrArg (dirichletNormalizedRow χ T p X α s hα hs m) (hshift_eq hmem hmem_fr)
      have h3 : dirichletQuotRow χ T p X α s hα hs m e_j =
          dirichletNormalizedRow χ T p X α s hα hs m
            (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem) := by
        dsimp [e_j]
        exact dirichletQuotRow_quotMap hχ hN T hT hp hpN hpT hX hα hs m _
      rw [← h2, h1, h3]
    rw [hfr_eval, hdiag m hmem]
    by_cases hmj : m = j
    · subst hmj
      simp only [↓reduceIte, mul_one]
      dsimp [c_mod, c_eig]
      rw [← Complex.exp_add]
      have hfreq_sub : -((t0 : ℂ) * Complex.I * (r : ℂ)) +
            (dirichletPrimeFreq χ p m : ℂ) * Complex.I * (r : ℂ) =
          (2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (r : ℂ) := by
        dsimp [dirichletPrimeFreq, t0, L]; push_cast; rw [add_div]; ring
      rw [hfreq_sub]
      exact sub_self _
    · simp [hmj]
  obtain ⟨g₀, hg₀, hdep_eq⟩ :=
    (dirichletFixedBox_stage_exact_division hχ hN T hT hp hpN hpT hX hα hs htest_box).mpr hvan_all
  have hTpos' : ∀ q ∈ insert p T, 0 < q := fun q hq ↦ by
    rcases Finset.mem_insert.mp hq with rfl | hqT
    · exact hp.pos
    · exact (hT q hqT).1.pos
  have hR'_pos : 0 < X / ∏ q ∈ insert p T, (q : ℝ) :=
    div_pos hX (Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hTpos' q hq))
  have hg₀' : IsDirichletFixedBoxTest χ (X / ∏ q ∈ insert p T, (q : ℝ)) g₀ := by
    simpa only [Finset.prod_insert hpT, mul_comm (p : ℝ) (∏ q ∈ T, (q : ℝ)), ← div_div] using hg₀
  have hmem_g : MemLp (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) 2
      (intervalSobolevMeasure volume id (-α) α s false) :=
    dirichletDeplete_memLp hχ hN (insert p T) hTpos' hR'_pos hα hs hg₀'
  have hmem_ins : toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ htest)) hmem_test ∈
      dirichletStageSpace χ (insert p T) X α s hα hs := by
    have heq_ins : toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ htest)) hmem_test =
        toDirichletStrip α s (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) hmem_g := by
      apply toDirichletStrip_congr_ae
      refine Filter.Eventually.of_forall fun x ↦ ?_
      rw [← hdep_eq, twistedHalfLogProfile_testDepleteStep χ hp.pos,
        ← dirichletDeplete_commute_step χ p T (twistedHalfLogProfile χ g₀),
        ← LinearMap.comp_apply, ← dirichletDeplete_insert χ hpT]
    rw [heq_ins]
    exact mem_dirichletStageSpace_of_test (insert p T) hα hs hg₀' hmem_g
  have hquot0 : dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u e_j - c_eig • e_j = 0 := by
    rw [hτ_r]
    dsimp [e_j]
    rw [dirichletQuotSemigroup_quotMap, ← map_smul, ← map_smul, ← map_sub,
      dirichletStageQuotMap_eq_zero_iff]
    change c_mod • backHalfShiftCLM α s hα hs r _ - c_eig • _ ∈ _
    rw [hshift_eq hmem hmem_fr, hdiff_strip]
    exact hmem_ins
  have heig_eq : c_eig = Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) := by
    have hr_mod : (u : ℂ) = (r : ℂ) + ((⌊u / L⌋ : ℤ) : ℂ) * (L : ℂ) := by
      have := Int.floor_add_fract (u / L)
      have hr_real : u = r + ((⌊u / L⌋ : ℤ) : ℝ) * L := by
        dsimp [r]
        calc u = (u / L) * L := (div_mul_cancel₀ u hL_pos.ne').symm
          _ = ((⌊u / L⌋ : ℝ) + Int.fract (u / L)) * L := by rw [this]
          _ = _ := by ring
      exact_mod_cast hr_real
    dsimp [c_eig]
    have hL_C : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
    have harg : (2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * ((r : ℂ) + ((⌊u / L⌋ : ℤ) : ℂ) * (L : ℂ)) =
        (2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (r : ℂ) +
          ((j * ⌊u / L⌋ : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; field_simp [hL_C]
    calc Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (r : ℂ))
        = Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (r : ℂ) +
            ((j * ⌊u / L⌋ : ℤ) : ℂ) * (2 * Real.pi * Complex.I)) := by
            rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      _ = Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) := by
            rw [← harg, ← hr_mod]
  rw [← heig_eq]
  exact sub_eq_zero.mp hquot0

/-- Strongly continuous `(Real.log p)`-periodic modulated circle action on the fixed-box quotient `Q`,
bundled with its semigroup law, uniform operator bound, `AddCircle` factorisation, and exact
eigenvalue action on both `dirichletQuotRow` and the cardinal classes `e_j`.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletFixedBox_modulated_circle_action {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let L : ℝ := Real.log p
    let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
    ∃ τ_circle : AddCircle L →
        (dirichletStageQuotient χ T p X α s hα hs →L[ℂ]
          dirichletStageQuotient χ T p X α s hα hs),
      (∀ u : ℝ, τ_circle (u : AddCircle L) = τ u) ∧
      τ 0 = ContinuousLinearMap.id ℂ _ ∧
      (∀ u v : ℝ, τ (u + v) = (τ u).comp (τ v)) ∧
      (∀ u : ℝ, ‖τ u‖ ≤
        Real.exp (L / 2 + α * L) * (2 + 2 * L ^ 2) ^ (s / 4)) ∧
      (∀ q, Continuous fun u : ℝ ↦ τ u q) ∧
      (∀ j : ℤ, ∀ u : ℝ, ∀ q,
        dirichletQuotRow χ T p X α s hα hs j (τ u q) =
          Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) *
            dirichletQuotRow χ T p X α s hα hs j q) := by
  intro L τ
  have hper := dirichletQuotModulatedAction_periodic hχ hN T hT hp hpT hX hα hs
  refine ⟨hper.lift, fun u ↦ hper.lift_coe u,
    dirichletQuotModulatedAction_zero hχ hN T hT hp hpN hpT hX hα hs,
    dirichletQuotModulatedAction_add hχ hN T hT hp hpN hpT hX hα hs,
    norm_dirichletQuotModulatedAction_le hχ hN T hT hp hpT hX hα hs,
    continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs,
    fun j u q ↦ dirichletQuotRow_modulatedAction hχ hN T hT hp hpN hpT hX hα hs j u q⟩

/-- Uniform operator-norm bound `M` on `dirichletQuotModulatedAction` over `ℝ`. -/
noncomputable def dirichletQuotActionBound (p : ℕ) (α s : ℝ) : ℝ :=
  Real.exp (Real.log p / 2 + α * Real.log p) * (2 + 2 * Real.log p ^ 2) ^ (s / 4)

theorem dirichletQuotActionBound_pos {p : ℕ} {α s : ℝ} :
    0 < dirichletQuotActionBound p α s := by
  dsimp [dirichletQuotActionBound]
  positivity

/-- Fourier-circle spectral projection `P_j` on `Q := dirichletStageQuotient χ T p X α s`.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
noncomputable def dirichletQuotProj {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (j : ℤ) :
    dirichletStageQuotient χ T p X α s hα hs →L[ℂ]
      dirichletStageQuotient χ T p X α s hα hs :=
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  let P_fun : dirichletStageQuotient χ T p X α s hα hs →
      dirichletStageQuotient χ T p X α s hα hs := fun q ↦
    (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q
  have hc_exp : Continuous (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hτ_int : ∀ q, IntervalIntegrable (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q)
      volume 0 L := fun q ↦
    (hc_exp.smul (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs q)).intervalIntegrable 0 L
  LinearMap.mkContinuous
    { toFun := P_fun
      map_add' := fun q₁ q₂ ↦ by
        dsimp only [P_fun]
        have hsum : (fun a : ℝ ↦
            Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a (q₁ + q₂)) =
            (fun a : ℝ ↦
              Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q₁ +
              Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q₂) := by
          funext a
          rw [map_add, smul_add]
        rw [hsum, intervalIntegral.integral_add (hτ_int q₁) (hτ_int q₂), smul_add]
      map_smul' := fun c q ↦ by
        dsimp only [P_fun, RingHom.id_apply]
        have hsmul : (fun a : ℝ ↦
            Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a (c • q)) =
            (fun a : ℝ ↦ c •
              (Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q)) := by
          funext a
          rw [map_smul, smul_comm]
        rw [hsmul, intervalIntegral.integral_smul, smul_comm] }
    (dirichletQuotActionBound p α s)
    fun q ↦ by
      dsimp only [P_fun, LinearMap.coe_mk, AddHom.coe_mk]
      have hnorm_wt : ∀ a : ℝ, ‖Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))‖ = 1 := by
        intro a
        rw [Complex.norm_exp]
        have hre : (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)).re = 0 := by
          rw [Complex.mul_re, Complex.mul_re, Complex.I_re, Complex.I_im,
            Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
          have him : ((2 * Real.pi * (j : ℝ) / L : ℂ)).im = 0 := by
            push_cast; simp
          rw [him]; ring
        rw [hre, Real.exp_zero]
      have hbd : ∀ a ∈ Set.uIoc 0 L,
          ‖Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q‖ ≤
            dirichletQuotActionBound p α s * ‖q‖ := fun a _ ↦ by
        rw [norm_smul, hnorm_wt, one_mul]
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (norm_dirichletQuotModulatedAction_le hχ hN T hT hp hpT hX hα hs a) (norm_nonneg _))
      have hint_bd := intervalIntegral.norm_integral_le_of_norm_le_const hbd
      rw [sub_zero, abs_of_pos hL_pos] at hint_bd
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hL_pos.le]
      calc L⁻¹ * ‖∫ a in (0 : ℝ)..L,
            Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q‖
          ≤ L⁻¹ * (dirichletQuotActionBound p α s * ‖q‖ * L) :=
            mul_le_mul_of_nonneg_left hint_bd (inv_pos.mpr hL_pos).le
        _ = dirichletQuotActionBound p α s * ‖q‖ := by field_simp [hL_pos.ne']

theorem dirichletQuotProj_apply {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (j : ℤ)
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j q =
      ((Real.log p)⁻¹ : ℂ) • ∫ a in (0 : ℝ)..Real.log p,
        Complex.exp (-(2 * Real.pi * (j : ℝ) / Real.log p : ℂ) * Complex.I * (a : ℂ)) •
          dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a q := rfl

theorem dirichletQuotProj_comp_modulatedAction {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (j : ℤ) (u : ℝ)
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j
        (dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u q) =
      Complex.exp ((2 * Real.pi * (j : ℝ) / Real.log p : ℂ) * Complex.I * (u : ℂ)) •
        dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j q := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  let f : ℝ → dirichletStageQuotient χ T p X α s hα hs := fun a ↦
    Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q
  have hf_per : Function.Periodic f L := by
    intro a
    dsimp only [f]
    have hL_C : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
    have hexp_per : Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * ((a + L : ℝ) : ℂ)) =
        Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) := by
      have harg : -(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * ((a + L : ℝ) : ℂ) =
          -(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ) +
            ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp [hL_C]; ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hτ_per := congrFun (congrArg DFunLike.coe
      (dirichletQuotModulatedAction_periodic hχ hN T hT hp hpT hX hα hs a)) q
    rw [hexp_per, hτ_per]
  have hc_exp : Continuous (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hf_int : ∀ c d : ℝ, IntervalIntegrable f volume c d := fun c d ↦
    (hc_exp.smul (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs q)).intervalIntegrable c d
  have hper_int : ∫ x in u..(u + L), f x = ∫ x in (0 : ℝ)..L, f x := by
    simpa only [zero_add] using (hf_per.intervalIntegral_add_eq 0 u).symm
  have hcomp_add : ∀ a : ℝ, τ a (τ u q) = τ (a + u) q := fun a ↦ by
    have h := congrFun (congrArg DFunLike.coe
      (dirichletQuotModulatedAction_add hχ hN T hT hp hpN hpT hX hα hs a u)) q
    rw [ContinuousLinearMap.comp_apply] at h
    exact h.symm
  have hshift_eq : ∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a (τ u q) =
      Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) •
        ∫ x in u..(u + L), f x := by
    rw [← intervalIntegral.integral_smul]
    have hcomp_inv : ∫ x in u..(u + L),
        Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) • f x =
        ∫ a in (0 : ℝ)..L,
          Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) • f (a + u) := by
      simpa only [zero_add, add_comm L u] using
        (intervalIntegral.integral_comp_add_right
          (fun x : ℝ ↦ Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) • f x) u
          (a := 0) (b := L)).symm
    rw [hcomp_inv]
    refine intervalIntegral.integral_congr fun a _ ↦ ?_
    dsimp only [f]
    rw [hcomp_add a, smul_smul, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [dirichletQuotProj_apply, dirichletQuotProj_apply]
  change (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a (τ u q) =
    Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) •
      ((L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L, f a)
  rw [hshift_eq, hper_int, smul_comm]

private theorem intervalIntegral_exp_two_pi_int {L : ℝ} (hL : 0 < L) (k : ℤ) :
    ((L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L,
      Complex.exp ((2 * Real.pi * (k : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) =
      if k = 0 then 1 else 0 := by
  have hL_C : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  by_cases hk : k = 0
  · subst hk
    simp [hL_C]
  · simp only [hk, ↓reduceIte]
    let ω₀ : ℂ := (2 * Real.pi * (k : ℝ) / L : ℂ) * Complex.I
    have hω₀ : ω₀ ≠ 0 := by
      refine mul_ne_zero (div_ne_zero ?_ hL_C) Complex.I_ne_zero
      norm_cast
      exact mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.mpr hk)
    let F : ℝ → ℂ := fun a ↦ ω₀⁻¹ * Complex.exp (ω₀ * (a : ℂ))
    have hderiv : ∀ a ∈ Set.uIcc 0 L,
        HasDerivAt F (Complex.exp (ω₀ * (a : ℂ))) a := fun a _ ↦ by
      have hc : HasDerivAt (fun x : ℝ ↦ ω₀ * (x : ℂ)) ω₀ a := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := a)).const_mul ω₀
      have hexp : HasDerivAt F
          (0 * Complex.exp (ω₀ * (a : ℂ)) + ω₀⁻¹ * (Complex.exp (ω₀ * (a : ℂ)) * ω₀)) a :=
        (hasDerivAt_const a ω₀⁻¹).mul ((Complex.hasDerivAt_exp (ω₀ * (a : ℂ))).comp a hc)
      refine hexp.congr_deriv ?_
      rw [zero_mul, zero_add, mul_comm (Complex.exp _) ω₀, ← mul_assoc, inv_mul_cancel₀ hω₀, one_mul]
    have hint : IntervalIntegrable (fun a : ℝ ↦ Complex.exp (ω₀ * (a : ℂ))) volume 0 L :=
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).intervalIntegrable 0 L
    have hval := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
    have hFL0 : F L = F 0 := by
      dsimp only [F]
      have harg : ω₀ * (L : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
        dsimp only [ω₀]; push_cast; field_simp [hL_C]
      rw [harg, Complex.exp_int_mul_two_pi_mul_I, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [hval, hFL0, sub_self, mul_zero]

theorem intervalIntegral_exp_neg_eq_zero {L : ℝ} (hL : 0 < L) {m j : ℤ} :
    ((L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) *
        Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) =
      if m = j then 1 else 0 := by
  have heq : (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) *
        Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) =
      fun a : ℝ ↦ Complex.exp ((2 * Real.pi * ((j - m : ℤ) : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) := by
    funext a
    rw [← Complex.exp_add]
    congr 1
    push_cast; ring
  rw [heq, intervalIntegral_exp_two_pi_int hL (j - m)]
  by_cases hmj : m = j
  · subst hmj; simp
  · have hne : j - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmj)
    simp [hmj, hne]

private theorem dirichletQuotModulatedAction_proj {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (j : ℤ) (u : ℝ)
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u
        (dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j q) =
      Complex.exp ((2 * Real.pi * (j : ℝ) / Real.log p : ℂ) * Complex.I * (u : ℂ)) •
        dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j q := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  let f : ℝ → dirichletStageQuotient χ T p X α s hα hs := fun a ↦
    Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q
  have hf_per : Function.Periodic f L := by
    intro a
    dsimp only [f]
    have hL_C : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
    have hexp_per : Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * ((a + L : ℝ) : ℂ)) =
        Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) := by
      have harg : -(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * ((a + L : ℝ) : ℂ) =
          -(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ) +
            ((-j : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp [hL_C]; ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hτ_per := congrFun (congrArg DFunLike.coe
      (dirichletQuotModulatedAction_periodic hχ hN T hT hp hpT hX hα hs a)) q
    rw [hexp_per, hτ_per]
  have hc_exp : Continuous (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hf_int : IntervalIntegrable f volume 0 L :=
    (hc_exp.smul (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs q)).intervalIntegrable 0 L
  have hlin := (τ u).intervalIntegral_comp_comm hf_int
  have hcomp_add : ∀ x : ℝ, τ u (τ x q) = τ (u + x) q := fun x ↦ by
    have h := congrFun (congrArg DFunLike.coe
      (dirichletQuotModulatedAction_add hχ hN T hT hp hpN hpT hX hα hs u x)) q
    rw [ContinuousLinearMap.comp_apply] at h
    exact h.symm
  rw [dirichletQuotProj_apply]
  change (τ u) ((L⁻¹ : ℂ) • ∫ x in (0 : ℝ)..L, f x) =
    Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) •
      ((L⁻¹ : ℂ) • ∫ x in (0 : ℝ)..L, f x)
  rw [map_smul, ← hlin]
  have hshift : (∫ x in (0 : ℝ)..L, (τ u) (f x)) =
      Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) •
        ∫ y in u..(u + L), f y := by
    rw [← intervalIntegral.integral_smul]
    have hc : ∫ y in u..(u + L),
        Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) • f y =
        ∫ x in (0 : ℝ)..L,
          Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) • f (x + u) := by
      simpa only [zero_add, add_comm L u] using
        (intervalIntegral.integral_comp_add_right
          (fun y : ℝ ↦ Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (u : ℂ)) • f y) u
          (a := 0) (b := L)).symm
    rw [hc]
    refine intervalIntegral.integral_congr fun x _ ↦ ?_
    dsimp only [f]
    rw [map_smul, hcomp_add x, add_comm u x, smul_smul, ← Complex.exp_add]
    congr 2; push_cast; ring
  have hper_int : ∫ y in u..(u + L), f y = ∫ x in (0 : ℝ)..L, f x := by
    simpa only [zero_add] using (hf_per.intervalIntegral_add_eq 0 u).symm
  rw [hshift, hper_int, smul_comm]

theorem dirichletQuotProj_comp_ne {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) {m j : ℤ}
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs m
        (dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j q) =
      if m = j then dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j q else 0 := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let P_j := dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j
  rw [dirichletQuotProj_apply]
  have hrew : (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) •
        dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a (P_j q)) =
      fun a : ℝ ↦
        (Complex.exp (-(2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) *
          Complex.exp ((2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) • P_j q := by
    funext a
    rw [dirichletQuotModulatedAction_proj, smul_smul]
  change (L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) •
        dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a (P_j q) =
    if m = j then P_j q else 0
  rw [hrew, intervalIntegral.integral_smul_const, smul_smul,
    intervalIntegral_exp_neg_eq_zero hL_pos]
  by_cases hmj : m = j
  · simp [hmj]
  · simp [hmj]

theorem dirichletQuotRow_proj {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (m j : ℤ)
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    dirichletQuotRow χ T p X α s hα hs m
        (dirichletQuotProj hχ hN T hT hp hpN hpT hX hα hs j q) =
      if m = j then dirichletQuotRow χ T p X α s hα hs j q else 0 := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let row := dirichletQuotRow χ T p X α s hα hs m
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  have hc_exp : Continuous (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) :=
    Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hint : IntervalIntegrable (fun a : ℝ ↦
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q)
      volume 0 L :=
    (hc_exp.smul (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs q)).intervalIntegrable 0 L
  rw [dirichletQuotProj_apply]
  change row ((L⁻¹ : ℂ) • ∫ a in (0 : ℝ)..L,
      Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q) = _
  rw [map_smul, ← row.intervalIntegral_comp_comm hint]
  have hrew : (fun a : ℝ ↦ row
      (Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) • τ a q)) =
      fun a : ℝ ↦
        (Complex.exp (-(2 * Real.pi * (j : ℝ) / L : ℂ) * Complex.I * (a : ℂ)) *
          Complex.exp ((2 * Real.pi * (m : ℝ) / L : ℂ) * Complex.I * (a : ℂ))) * row q := by
    funext a
    rw [map_smul, smul_eq_mul, dirichletQuotRow_modulatedAction hχ hN T hT hp hpN hpT hX hα hs m a q]
    ring
  rw [hrew, intervalIntegral.integral_mul_const, smul_eq_mul, ← mul_assoc,
    intervalIntegral_exp_neg_eq_zero hL_pos]
  by_cases hmj : m = j
  · subst hmj; simp [row]
  · have hjm : j ≠ m := Ne.symm hmj
    simp [hmj, hjm]

/-- Spectral cardinal Fourier transform `H_hat(w)` obtained by averaging `(exp a) * (𝓕 f₀)(exp a * w)`
against `exp (-i * ω_j * a)` over `[0, log p]`. -/
noncomputable def dirichletSmoothLiftHat {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (p : ℕ) (j : ℤ) (f₀ : 𝓢(ℝ, ℂ)) (w : ℝ) : ℂ :=
  ((Real.log p)⁻¹ : ℂ) * ∫ a in (0 : ℝ)..Real.log p,
    Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
      (Real.exp a : ℂ) * (𝓕 f₀) (Real.exp a * w)

theorem dirichletSmoothLiftHat_tsupport {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) {R : ℝ} (hR : 0 < R)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ R f₀) (j : ℤ) :
    tsupport (dirichletSmoothLiftHat χ p j f₀) ⊆ Set.Icc (-R) R := by
  refine closure_minimal ?_ isClosed_Icc
  intro w hw
  rw [Function.mem_support] at hw
  by_contra hnot
  apply hw
  dsimp only [dirichletSmoothLiftHat]
  have hzero : ∀ a ∈ Set.uIcc (0 : ℝ) (Real.log p),
      Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
        (Real.exp a : ℂ) * (𝓕 f₀) (Real.exp a * w) = 0 := by
    intro a ha
    have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
    rw [Set.uIcc_of_le hL_pos.le, Set.mem_Icc] at ha
    have hexp_ge : 1 ≤ Real.exp a := Real.one_le_exp ha.1
    have hout : Real.exp a * w ∉ Set.Icc (-R) R := by
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot ⊢
      rcases hnot with hlt | hgt
      · left; nlinarith
      · right; nlinarith
    have hf0_zero : (𝓕 f₀) (Real.exp a * w) = 0 := by
      by_contra hnz
      exact hout (hf₀.2 (subset_tsupport _ (Function.mem_support.mpr hnz)))
    rw [hf0_zero, mul_zero]
  rw [intervalIntegral.integral_congr hzero, intervalIntegral.integral_zero, mul_zero]

theorem dirichletSmoothLiftHat_contDiff {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (p : ℕ) (j : ℤ) (f₀ : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (dirichletSmoothLiftHat χ p j f₀) := by
  let F : ℝ × ℝ → ℂ := fun q ↦
    Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (q.2 : ℂ)) *
      (Real.exp q.2 : ℂ) * (𝓕 f₀) (Real.exp q.2 * q.1)
  have hF : ContDiff ℝ ∞ F := by
    refine ((ContDiff.mul ?_ ?_).mul ?_)
    · exact Complex.contDiff_exp.comp
        (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp contDiff_snd))
    · exact Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_snd)
    · exact ((𝓕 f₀).smooth (⊤ : ℕ∞)).comp ((Real.contDiff_exp.comp contDiff_snd).mul contDiff_fst)
  exact contDiff_const.mul (hF.parametric_intervalIntegral)

theorem dirichletSmoothLiftHat_hasDirichletParity {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (p : ℕ) (j : ℤ)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : HasDirichletParity χ f₀) :
    ∀ w : ℝ, dirichletSmoothLiftHat χ p j f₀ (-w) =
      χ (-1) * dirichletSmoothLiftHat χ p j f₀ w := by
  intro w
  dsimp only [dirichletSmoothLiftHat]
  have hmul : ∀ a : ℝ, Real.exp a * (-w) = -(Real.exp a * w) := fun a ↦ by ring
  have hpar : (fun a : ℝ ↦
      Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
        (Real.exp a : ℂ) * (𝓕 f₀) (Real.exp a * (-w))) =
      fun a : ℝ ↦ χ (-1) *
        (Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          (Real.exp a : ℂ) * (𝓕 f₀) (Real.exp a * w)) := by
    funext a
    rw [hmul a, hf₀.fourier]
    ring
  rw [hpar, intervalIntegral.integral_const_mul]
  ring

/-- Smooth cardinal fixed-box Schwartz lift `H` built from a generator `f₀`. -/
noncomputable def dirichletSmoothLift {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) {R : ℝ} (hR : 0 < R)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ R f₀) (j : ℤ) : 𝓢(ℝ, ℂ) :=
  let hsupp : HasCompactSupport (dirichletSmoothLiftHat χ p j f₀) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport _).trans (dirichletSmoothLiftHat_tsupport χ hp hR hf₀ j))
  𝓕⁻ (hsupp.toSchwartzMap (dirichletSmoothLiftHat_contDiff χ p j f₀))

theorem dirichletSmoothLift_isFixedBox {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) {R : ℝ} (hR : 0 < R)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ R f₀) (j : ℤ) :
    IsDirichletFixedBoxTest χ R (dirichletSmoothLift χ hp hR hf₀ j) := by
  let hsupp : HasCompactSupport (dirichletSmoothLiftHat χ p j f₀) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport _).trans (dirichletSmoothLiftHat_tsupport χ hp hR hf₀ j))
  let G : 𝓢(ℝ, ℂ) := hsupp.toSchwartzMap (dirichletSmoothLiftHat_contDiff χ p j f₀)
  have hG_par : HasDirichletParity χ G :=
    dirichletSmoothLiftHat_hasDirichletParity χ p j hf₀.1
  refine ⟨hG_par.fourierInv, ?_⟩
  have hF : (fun w : ℝ ↦ (𝓕 (dirichletSmoothLift χ hp hR hf₀ j)) w) =
      dirichletSmoothLiftHat χ p j f₀ := by
    ext w
    change (𝓕 (𝓕⁻ G)) w = dirichletSmoothLiftHat χ p j f₀ w
    rw [FourierTransform.fourier_fourierInv_eq]
    rfl
  rw [hF]
  exact dirichletSmoothLiftHat_tsupport χ hp hR hf₀ j

theorem dirichletSmoothLift_apply {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) {R : ℝ} (hR : 0 < R)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ R f₀) (j : ℤ) (u : ℝ) :
    dirichletSmoothLift χ hp hR hf₀ j u =
      ((Real.log p)⁻¹ : ℂ) * ∫ a in (0 : ℝ)..Real.log p,
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          f₀ (Real.exp (-a) * u) := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let hsupp : HasCompactSupport (dirichletSmoothLiftHat χ p j f₀) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      ((subset_tsupport _).trans (dirichletSmoothLiftHat_tsupport χ hp hR hf₀ j))
  let G : 𝓢(ℝ, ℂ) := hsupp.toSchwartzMap (dirichletSmoothLiftHat_contDiff χ p j f₀)
  have hH_eq : dirichletSmoothLift χ hp hR hf₀ j u =
      ∫ w : ℝ, Complex.exp (↑(2 * Real.pi * u * w) * Complex.I) *
        dirichletSmoothLiftHat χ p j f₀ w := by
    change (𝓕⁻ G) u = _
    rw [SchwartzMap.fourierInv_apply_eq]
    change (𝓕 G) (-u) = _
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w ↦ ?_)
    simp only [smul_eq_mul, G, HasCompactSupport.toSchwartzMap_toFun]
    congr 2; push_cast; ring
  let K : ℝ → ℝ → ℂ := fun a w ↦
    Complex.exp (↑(2 * Real.pi * u * w) * Complex.I) *
      (Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
        (Real.exp a : ℂ) * (𝓕 f₀) (Real.exp a * w))
  have hK_cont : Continuous (Function.uncurry K) := by
    refine Continuous.mul ?_ ?_
    · exact Complex.continuous_exp.comp
        ((Complex.continuous_ofReal.comp ((continuous_const.mul continuous_snd))).mul continuous_const)
    · refine ((Continuous.mul ?_ ?_).mul ?_)
      · exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst))
      · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp continuous_fst)
      · exact (𝓕 f₀).continuous.comp ((Real.continuous_exp.comp continuous_fst).mul continuous_snd)
  have hK_int : Integrable (Function.uncurry K)
      ((volume.restrict (Set.uIoc 0 L)).prod volume) := by
    have hK_supp : ∀ a ∈ Set.Icc 0 L, ∀ w : ℝ, w ∉ Set.Icc (-R) R → K a w = 0 := by
      intro a ha w hw
      have hexp_ge : 1 ≤ Real.exp a := Real.one_le_exp ha.1
      have hout : Real.exp a * w ∉ Set.Icc (-R) R := by
        rw [Set.mem_Icc, not_and_or, not_le, not_le] at hw ⊢
        rcases hw with hlt | hgt
        · left; nlinarith
        · right; nlinarith
      have hf0_zero : (𝓕 f₀) (Real.exp a * w) = 0 := by
        by_contra hnz
        exact hout (hf₀.2 (subset_tsupport _ (Function.mem_support.mpr hnz)))
      simp [K, hf0_zero]
    let M_K : ℝ :=
      (sSup ((fun p : ℝ × ℝ ↦ ‖Function.uncurry K p‖) '' (Set.Icc 0 L ×ˢ Set.Icc (-R) R))) + 1
    have hMK_pos : 0 ≤ M_K := by
      have hm : 0 ≤ sSup ((fun p : ℝ × ℝ ↦ ‖Function.uncurry K p‖) '' (Set.Icc 0 L ×ˢ Set.Icc (-R) R)) :=
        Real.sSup_nonneg (by rintro _ ⟨_, _, rfl⟩; exact norm_nonneg _)
      linarith
    have hcpt : IsCompact (Set.Icc 0 L ×ˢ Set.Icc (-R) R) := isCompact_Icc.prod isCompact_Icc
    have hbdd : BddAbove ((fun p : ℝ × ℝ ↦ ‖Function.uncurry K p‖) '' (Set.Icc 0 L ×ˢ Set.Icc (-R) R)) :=
      (hcpt.image hK_cont.norm).bddAbove
    let bound : ℝ → ℝ := Set.indicator (Set.Icc (-R) R) (fun _ ↦ M_K)
    have hbound_int : Integrable bound volume :=
      (continuousOn_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    refine (MeasureTheory.integrable_prod_iff hK_cont.aestronglyMeasurable).mpr ⟨?_, ?_⟩
    · filter_upwards [ae_restrict_mem measurableSet_uIoc] with a ha
      rw [Set.uIoc_of_le hL_pos.le] at ha
      refine hbound_int.mono'
        (hK_cont.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun w ↦ ?_
      dsimp only [bound]
      by_cases hw : w ∈ Set.Icc (-R) R
      · rw [Set.indicator_of_mem hw]
        have hmem_prod : (a, w) ∈ Set.Icc 0 L ×ˢ Set.Icc (-R) R :=
          ⟨Set.Ioc_subset_Icc_self ha, hw⟩
        exact (le_csSup hbdd ⟨(a, w), hmem_prod, rfl⟩).trans (by linarith)
      · rw [Set.indicator_of_notMem hw]
        change ‖K a w‖ ≤ 0
        rw [hK_supp a (Set.Ioc_subset_Icc_self ha) w hw, norm_zero]
    · have hconst_int : Integrable (fun _ : ℝ ↦ 2 * R * M_K) (volume.restrict (Set.uIoc 0 L)) := by
        change IntegrableOn (fun _ : ℝ ↦ 2 * R * M_K) (Set.uIoc 0 L) volume
        rw [Set.uIoc_of_le hL_pos.le]
        exact continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
      refine hconst_int.mono'
        ((MeasureTheory.StronglyMeasurable.integral_prod_right' hK_cont.norm.stronglyMeasurable).aestronglyMeasurable) ?_
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with a ha
      rw [Set.uIoc_of_le hL_pos.le] at ha
      have hle_pt : ∀ w : ℝ, ‖K a w‖ ≤ bound w := fun w ↦ by
        dsimp only [bound]
        by_cases hw : w ∈ Set.Icc (-R) R
        · rw [Set.indicator_of_mem hw]
          exact (le_csSup hbdd ⟨(a, w), ⟨Set.Ioc_subset_Icc_self ha, hw⟩, rfl⟩).trans (by linarith)
        · rw [Set.indicator_of_notMem hw, hK_supp a (Set.Ioc_subset_Icc_self ha) w hw, norm_zero]
      have hmeas_w : Integrable (fun w : ℝ ↦ ‖K a w‖) volume := hbound_int.mono'
        (hK_cont.comp (continuous_const.prodMk continuous_id)).norm.aestronglyMeasurable
        (Filter.Eventually.of_forall fun w ↦ by
          change ‖‖K a w‖‖ ≤ bound w
          rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hle_pt w)
      calc ‖∫ w : ℝ, ‖Function.uncurry K (a, w)‖ ∂volume‖
          = ∫ w : ℝ, ‖K a w‖ ∂volume :=
            Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
        _ ≤ ∫ w : ℝ, bound w ∂volume := integral_mono hmeas_w hbound_int hle_pt
        _ = M_K * (volume (Set.Icc (-R) R)).toReal := by
            rw [integral_indicator measurableSet_Icc, setIntegral_const, smul_eq_mul,
              Measure.real_def, mul_comm]
        _ = M_K * (2 * R) := by
            rw [Real.volume_Icc, show R - -R = 2 * R by ring,
              ENNReal.toReal_ofReal (by linarith)]
        _ = 2 * R * M_K := by ring
  have hswap := MeasureTheory.intervalIntegral_integral_swap hK_int
  have hH_rew : (fun w : ℝ ↦ Complex.exp (↑(2 * Real.pi * u * w) * Complex.I) *
        dirichletSmoothLiftHat χ p j f₀ w) =
      fun w : ℝ ↦ (L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L, K a w := by
    funext w
    dsimp only [dirichletSmoothLiftHat, K]
    have hmul_comm : ∀ c x : ℂ, Complex.exp (↑(2 * Real.pi * u * w) * Complex.I) * (c * x) =
        c * (Complex.exp (↑(2 * Real.pi * u * w) * Complex.I) * x) := fun c x ↦ by ring
    rw [hmul_comm, ← intervalIntegral.integral_const_mul]
  rw [hH_eq, hH_rew, integral_const_mul, ← hswap]
  congr 1
  refine intervalIntegral.integral_congr fun a _ ↦ ?_
  have hinner : ∫ w : ℝ, K a w =
      Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
        f₀ (Real.exp (-a) * u) := by
    have hpull : (fun w : ℝ ↦ K a w) =
        fun w : ℝ ↦ Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          ((Real.exp a : ℂ) * (Complex.exp (↑(2 * Real.pi * (Real.exp (-a) * u) * (Real.exp a * w)) * Complex.I) *
            (𝓕 f₀) (Real.exp a * w))) := by
      funext w
      dsimp only [K]
      have hexp_mul : Real.exp (-a) * Real.exp a = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have harg : (2 * Real.pi * u * w) = 2 * Real.pi * (Real.exp (-a) * u) * (Real.exp a * w) := by
        calc 2 * Real.pi * u * w
            = 2 * Real.pi * ((Real.exp (-a) * Real.exp a) * u) * w := by rw [hexp_mul, one_mul]
          _ = _ := by ring
      rw [harg]
      ring
    rw [hpull, integral_const_mul]
    congr 1
    have hcomp : ∫ y : ℝ, Complex.exp (↑(2 * Real.pi * (Real.exp (-a) * u) * (Real.exp a * y)) * Complex.I) *
          (𝓕 f₀) (Real.exp a * y) =
        |(Real.exp a)⁻¹| • ∫ z : ℝ,
          Complex.exp (↑(2 * Real.pi * (Real.exp (-a) * u) * z) * Complex.I) * (𝓕 f₀) z :=
      MeasureTheory.Measure.integral_comp_mul_left
        (fun z : ℝ ↦ Complex.exp (↑(2 * Real.pi * (Real.exp (-a) * u) * z) * Complex.I) * (𝓕 f₀) z)
        (Real.exp a)
    rw [integral_const_mul, hcomp]
    rw [abs_of_pos (inv_pos.mpr (Real.exp_pos a)), Complex.real_smul, Complex.ofReal_inv,
      ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos a).ne'), one_mul]
    have hinv_f₀ : f₀ (Real.exp (-a) * u) =
        ∫ y : ℝ, Complex.exp (↑(2 * Real.pi * (Real.exp (-a) * u) * y) * Complex.I) * (𝓕 f₀) y := by
      have hfourier : (𝓕⁻ (𝓕 f₀ : 𝓢(ℝ, ℂ))) = f₀ := FourierTransform.fourierInv_fourier_eq f₀
      have hff : (𝓕⁻ (𝓕 f₀ : 𝓢(ℝ, ℂ))) (Real.exp (-a) * u) = f₀ (Real.exp (-a) * u) :=
        congrFun (congrArg DFunLike.coe hfourier) (Real.exp (-a) * u)
      rw [← hff, SchwartzMap.fourierInv_apply_eq]
      change (𝓕 (𝓕 f₀ : 𝓢(ℝ, ℂ))) (-(Real.exp (-a) * u)) = _
      rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
      simp only [smul_eq_mul]
      congr 2; push_cast; ring
    exact hinv_f₀.symm
  exact hinner

theorem twistedHalfLogProfile_dirichletSmoothLift {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hN : 1 < N) {p : ℕ} (hp : p.Prime) {R : ℝ} (hR : 0 < R)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ R f₀) (j : ℤ) (x : ℝ) :
    twistedHalfLogProfile χ (dirichletSmoothLift χ hp hR hf₀ j) x =
      ((Real.log p)⁻¹ : ℂ) * ∫ a in (0 : ℝ)..Real.log p,
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          (Real.exp (a / 2) : ℂ) * twistedHalfLogProfile χ f₀ (x - a) := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let H := dirichletSmoothLift χ hp hR hf₀ j
  let G_int : ℤ → ℝ → ℂ := fun m a ↦
    Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
      (Real.exp (a / 2) : ℂ) * (Real.exp ((x - a) / 2) : ℂ) *
      (χ (m : ZMod N) * f₀ ((m : ℝ) * Real.exp (x - a)))
  let μI : Measure ℝ := volume.restrict (Set.Ioc 0 L)
  have : IsFiniteMeasure μI := ⟨by simp [μI, Real.volume_Ioc]⟩
  obtain ⟨C₀, hC₀, hbd⟩ := twistedRadialTheta_term_bound χ hN f₀ 2 (by decide)
  have hG_int : ∀ m : ℤ, Integrable (G_int m) μI := fun m ↦ by
    have hcont_m : Continuous (G_int m) := by
      refine ((Continuous.mul ?_ ?_).mul ?_).mul (continuous_const.mul (f₀.continuous.comp ?_))
      · exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
      · exact Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))
      · exact Complex.continuous_ofReal.comp
          (Real.continuous_exp.comp ((continuous_const.sub continuous_id).div_const 2))
      · exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.sub continuous_id))
    exact hcont_m.continuousOn.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have hG_bound : ∀ m : ℤ, ∀ a ∈ Set.Ioc 0 L,
      ‖G_int m a‖ ≤ (Real.exp (x / 2) * C₀ * Real.exp (-2 * (x - L))) * |(m : ℝ)| ^ (-(2 : ℝ)) := by
    intro m a ha
    dsimp only [G_int]
    have hexp_mod : ‖Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)).re = 0 := by
        rw [Complex.mul_re, Complex.mul_re, Complex.I_re, Complex.I_im,
          Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.ofReal_re, Complex.ofReal_im]
        ring
      rw [hre, Real.exp_zero]
    have hexp_split : Real.exp (a / 2) * Real.exp ((x - a) / 2) = Real.exp (x / 2) := by
      rw [← Real.exp_add]; congr 1; ring
    have hbd_m := hbd m (x - a)
    have hexp_le : Real.exp (-(2 : ℝ) * (x - a)) ≤ Real.exp (-(2 : ℝ) * (x - L)) :=
      Real.exp_le_exp.mpr (by linarith [ha.2])
    rw [norm_mul, norm_mul, norm_mul, hexp_mod, one_mul,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      mul_assoc _ _ ‖_‖, ← mul_assoc (Real.exp (a / 2)), hexp_split]
    calc Real.exp (x / 2) * ‖χ (m : ZMod N) * f₀ ((m : ℝ) * Real.exp (x - a))‖
        ≤ Real.exp (x / 2) * (C₀ * |(m : ℝ)| ^ (-(2 : ℝ)) * Real.exp (-(2 : ℝ) * (x - a))) :=
          mul_le_mul_of_nonneg_left hbd_m (Real.exp_pos _).le
      _ ≤ Real.exp (x / 2) * (C₀ * |(m : ℝ)| ^ (-(2 : ℝ)) * Real.exp (-(2 : ℝ) * (x - L))) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_left hexp_le (by positivity)
      _ = (Real.exp (x / 2) * C₀ * Real.exp (-2 * (x - L))) * |(m : ℝ)| ^ (-(2 : ℝ)) := by
          norm_cast; ring
  have hsum_int : Summable fun m : ℤ ↦ ∫ a, ‖G_int m a‖ ∂μI := by
    have hsum2 : Summable (fun m : ℤ ↦ |(m : ℝ)| ^ (-(2 : ℝ))) :=
      Real.summable_abs_int_rpow one_lt_two
    refine Summable.of_nonneg_of_le (fun m ↦ integral_nonneg fun _ ↦ norm_nonneg _)
      (fun m ↦ ?_) (hsum2.mul_left ((Real.exp (x / 2) * C₀ * Real.exp (-2 * (x - L))) * L))
    have hle_const : ∫ a, ‖G_int m a‖ ∂μI ≤
        ∫ _, (Real.exp (x / 2) * C₀ * Real.exp (-2 * (x - L))) * |(m : ℝ)| ^ (-(2 : ℝ)) ∂μI := by
      refine integral_mono_ae (hG_int m).norm (integrable_const _) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with a ha
      exact hG_bound m a ha
    refine hle_const.trans_eq ?_
    rw [setIntegral_const, smul_eq_mul, Measure.real_def,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_ofReal hL_pos.le]
    ring
  have hswap := (MeasureTheory.hasSum_integral_of_summable_integral_norm hG_int hsum_int).tsum_eq
  have hterm : ∀ m : ℤ,
      (Real.exp (x / 2) : ℂ) * (χ (m : ZMod N) * H ((m : ℝ) * Real.exp x)) =
        (L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L, G_int m a := by
    intro m
    dsimp only [H]
    rw [dirichletSmoothLift_apply χ hp hR hf₀ j ((m : ℝ) * Real.exp x)]
    have hexp_arg : ∀ a : ℝ, Real.exp (-a) * ((m : ℝ) * Real.exp x) = (m : ℝ) * Real.exp (x - a) := by
      intro a; rw [Real.exp_sub, div_eq_mul_inv, Real.exp_neg]; ring
    have hexp_split : ∀ a : ℝ, (Real.exp (x / 2) : ℂ) = (Real.exp (a / 2) : ℂ) * (Real.exp ((x - a) / 2) : ℂ) := by
      intro a; rw [← Complex.ofReal_mul, ← Real.exp_add]; congr 2; ring
    have hpull : (Real.exp (x / 2) : ℂ) * (χ (m : ZMod N) * ((L⁻¹ : ℂ) *
          ∫ a in (0 : ℝ)..L, Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
            f₀ (Real.exp (-a) * ((m : ℝ) * Real.exp x)))) =
        (L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L,
          ((Real.exp (x / 2) : ℂ) * χ (m : ZMod N)) *
            (Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
              f₀ (Real.exp (-a) * ((m : ℝ) * Real.exp x))) := by
      rw [intervalIntegral.integral_const_mul]
      ring
    rw [hpull]
    congr 1
    refine intervalIntegral.integral_congr fun a _ ↦ ?_
    dsimp only [G_int]
    rw [hexp_arg a, hexp_split a]
    ring
  have hrhs : ((L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L,
        Complex.exp (-(dirichletPrimeFreq χ p j : ℂ) * Complex.I * (a : ℂ)) *
          (Real.exp (a / 2) : ℂ) * twistedHalfLogProfile χ f₀ (x - a)) =
      (L⁻¹ : ℂ) * ∫ a, (∑' m : ℤ, G_int m a) ∂μI := by
    congr 1
    rw [intervalIntegral.integral_of_le hL_pos.le]
    refine setIntegral_congr_fun measurableSet_Ioc fun a _ ↦ ?_
    simp only [twistedHalfLogProfile, twistedRadialTheta, G_int, ← tsum_mul_left]
    refine tsum_congr fun m ↦ ?_
    ring
  calc twistedHalfLogProfile χ H x
      = (Real.exp (x / 2) : ℂ) * ∑' m : ℤ, χ (m : ZMod N) * H ((m : ℝ) * Real.exp x) := rfl
    _ = ∑' m : ℤ, (Real.exp (x / 2) : ℂ) * (χ (m : ZMod N) * H ((m : ℝ) * Real.exp x)) :=
        (tsum_mul_left).symm
    _ = ∑' m : ℤ, (L⁻¹ : ℂ) * ∫ a in (0 : ℝ)..L, G_int m a := by
        refine tsum_congr hterm
    _ = (L⁻¹ : ℂ) * ∑' m : ℤ, ∫ a, G_int m a ∂μI := by
        simp_rw [intervalIntegral.integral_of_le hL_pos.le]
        rw [tsum_mul_left]
    _ = (L⁻¹ : ℂ) * ∫ a, (∑' m : ℤ, G_int m a) ∂μI := by rw [hswap]
    _ = _ := hrhs.symm

theorem dirichletDeplete_continuous {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {U : ℝ → ℂ} (hU : Continuous U) :
    Continuous (dirichletDeplete χ T U) := by
  induction T using Finset.induction_on with
  | empty => simpa [dirichletDeplete_empty] using hU
  | insert r S' hrS' ihS =>
    rw [dirichletDeplete_insert χ hrS']
    have hr0 : 0 < r := hT r (Finset.mem_insert_self r S')
    have hS' : ∀ t ∈ S', 0 < t := fun t ht ↦ hT t (Finset.mem_insert_of_mem ht)
    have hcS' := ihS hS'
    change Continuous (fun z : ℝ ↦ depleteStepFun χ r (dirichletDeplete χ S' U) z)
    simp only [depleteStepFun, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply,
      halfTwistLogDilate, hr0.ne', ↓reduceIte, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact hcS'.sub (continuous_const.mul (continuous_const.mul (hcS'.comp (continuous_id.add continuous_const))))


end CircleActionAndTraceNorm

end RiemannMasullo.Isolated
