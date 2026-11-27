module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Basis_Isolated
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes (Trace)

Per-packet convolution trace expansion and positive-support trace-norm lower bound (`dirichletFixedBox_convolution_trace_expansion`, `dirichletFixedBox_traceNorm_lower_bound`).

Nothing outside the `Sec3_DirichletFixedBox*` / `Sec3_RatBridge*` isolated stack imports this module.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField RiemannMasullo Set Topology
open scoped BigOperators ContDiff FourierTransform NNReal Real SchwartzMap

namespace RiemannMasullo.Isolated

section CircleActionAndTraceNorm

open MeasureTheory Filter Topology Real
open scoped InnerProductSpace Convolution ENNReal

section ConvolutionAndTraceNorm

/-- Spectral eigenvalue `λ_j(Φ) = ∫ Φ(u) exp(i ω_j u) du` of the convolution operator
`T_Φ = ∫ Φ(u) exp(i (arg χ(p)/log p) u) τ_u du` at shifted prime frequency
`ω_j = (arg χ(p) + 2π j) / log p`.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
noncomputable def dirichletConvEigenvalue {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (p : ℕ) (Φ : 𝓢(ℝ, ℂ)) (j : ℤ) : ℂ :=
  ∫ u : ℝ, Φ u * Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (u : ℂ))

theorem dirichletConvEigenvalue_eq_fourier {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (p : ℕ) (Φ : 𝓢(ℝ, ℂ)) (j : ℤ) :
    dirichletConvEigenvalue χ p Φ j =
      (𝓕 Φ) (-(dirichletPrimeFreq χ p j) / (2 * Real.pi)) := by
  dsimp only [dirichletConvEigenvalue]
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  dsimp only
  rw [smul_eq_mul, mul_comm (Φ u)]
  congr 2
  have h2pi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  push_cast
  field_simp [h2pi]

theorem summable_norm_dirichletConvEigenvalue {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (Φ : 𝓢(ℝ, ℂ)) :
    Summable fun j : ℤ ↦ ‖dirichletConvEigenvalue χ p Φ j‖ := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨C, hdec⟩ := (𝓕 Φ).decay' 2 0
  have hdec0 : ∀ x : ℝ, ‖x‖ ^ 2 * ‖(𝓕 Φ) x‖ ≤ C := fun x ↦ by
    change ‖x‖ ^ 2 * ‖(𝓕 Φ).toFun x‖ ≤ C
    simpa only [norm_iteratedFDeriv_zero] using hdec x
  have hbd : ∀ j : ℤ,
      ‖dirichletConvEigenvalue χ p Φ j‖ ≤
        if j = 0 then ‖dirichletConvEigenvalue χ p Φ 0‖ else (C * (2 * L) ^ 2) * |(j : ℝ)| ^ (-(2 : ℝ)) := by
    intro j
    by_cases hj : j = 0
    · simp [hj]
    · simp only [hj, ↓reduceIte]
      rw [dirichletConvEigenvalue_eq_fourier]
      let x : ℝ := -(dirichletPrimeFreq χ p j) / (2 * Real.pi)
      have hx_lb : |(j : ℝ)| / (2 * L) ≤ ‖x‖ := by
        have harg_le : |Complex.arg (χ (p : ZMod N))| ≤ Real.pi := Complex.abs_arg_le_pi _
        have hx_eq : x = -(j : ℝ) / L - Complex.arg (χ (p : ZMod N)) / (2 * Real.pi * L) := by
          dsimp only [x, dirichletPrimeFreq, L]
          have h2pi : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
          field_simp [h2pi, hL_pos.ne']
          ring
        have h1 : |Complex.arg (χ (p : ZMod N)) / (2 * Real.pi * L)| ≤ 1 / (2 * L) := by
          rw [abs_div, abs_of_pos (mul_pos (mul_pos two_pos Real.pi_pos) hL_pos)]
          have hdiv : |Complex.arg (χ (p : ZMod N))| / (2 * Real.pi * L) ≤
              Real.pi / (2 * Real.pi * L) :=
            div_le_div_of_nonneg_right harg_le (by positivity)
          refine hdiv.trans_eq ?_
          field_simp [Real.pi_ne_zero, hL_pos.ne']
        have hj1 : (1 : ℝ) ≤ |(j : ℝ)| := by
          have hij : (1 : ℤ) ≤ |j| := Int.one_le_abs hj
          exact_mod_cast hij
        have h2 : |(j : ℝ)| / (2 * L) = |(j : ℝ)| / L - |(j : ℝ)| / (2 * L) := by ring
        have h3 : 1 / (2 * L) ≤ |(j : ℝ)| / (2 * L) :=
          div_le_div_of_nonneg_right hj1 (by positivity)
        have htri : |-(j : ℝ) / L| - |Complex.arg (χ (p : ZMod N)) / (2 * Real.pi * L)| ≤
            ‖x‖ := by
          rw [hx_eq, Real.norm_eq_abs]
          exact abs_sub_abs_le_abs_sub (-(j : ℝ) / L) (Complex.arg (χ (p : ZMod N)) / (2 * Real.pi * L))
        have hjL : |-(j : ℝ) / L| = |(j : ℝ)| / L := by
          rw [abs_div, abs_neg, abs_of_pos hL_pos]
        rw [hjL] at htri
        linarith
      have hx_sq : ((|(j : ℝ)| / (2 * L)) ^ 2) ≤ ‖x‖ ^ 2 :=
        sq_le_sq' (by linarith [div_nonneg (abs_nonneg (j : ℝ)) (mul_pos two_pos hL_pos).le]) hx_lb
      have hmul_le : (|(j : ℝ)| / (2 * L)) ^ 2 * ‖(𝓕 Φ) x‖ ≤ C :=
        (mul_le_mul_of_nonneg_right hx_sq (norm_nonneg _)).trans (hdec0 x)
      have hj_nz : (j : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hj
      have hj_abs_pos : 0 < |(j : ℝ)| := abs_pos.mpr hj_nz
      have hrpow : |(j : ℝ)| ^ (-(2 : ℝ)) = (|(j : ℝ)| ^ 2)⁻¹ := by
        rw [show (-(2 : ℝ)) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg (abs_nonneg _),
          Real.rpow_natCast]
      rw [hrpow]
      have hle_div : ‖(𝓕 Φ) x‖ ≤ C / (|(j : ℝ)| / (2 * L)) ^ 2 :=
        (le_div_iff₀ (sq_pos_of_pos (div_pos hj_abs_pos (by positivity)))).mpr
          (by simpa only [mul_comm] using hmul_le)
      refine hle_div.trans_eq ?_
      rw [div_pow, div_div_eq_mul_div, div_eq_mul_inv]
  have hsum_maj : Summable fun j : ℤ ↦
      if j = 0 then ‖dirichletConvEigenvalue χ p Φ 0‖ else (C * (2 * L) ^ 2) * |(j : ℝ)| ^ (-(2 : ℝ)) := by
    have hmain : Summable fun j : ℤ ↦ (C * (2 * L) ^ 2) * |(j : ℝ)| ^ (-(2 : ℝ)) :=
      (Real.summable_abs_int_rpow one_lt_two).mul_left (C * (2 * L) ^ 2)
    have hcorr : Summable fun j : ℤ ↦
        if j = 0 then ‖dirichletConvEigenvalue χ p Φ 0‖ - (C * (2 * L) ^ 2) * |(j : ℝ)| ^ (-(2 : ℝ))
        else 0 := by
      refine summable_of_ne_finset_zero (s := {0}) fun j hj ↦ ?_
      simp only [Finset.mem_singleton] at hj
      simp [hj]
    have hsum_eq : (fun j : ℤ ↦
        if j = 0 then ‖dirichletConvEigenvalue χ p Φ 0‖ else (C * (2 * L) ^ 2) * |(j : ℝ)| ^ (-(2 : ℝ))) =
        (fun j : ℤ ↦ (C * (2 * L) ^ 2) * |(j : ℝ)| ^ (-(2 : ℝ)) +
          (if j = 0 then ‖dirichletConvEigenvalue χ p Φ 0‖ - (C * (2 * L) ^ 2) * |(j : ℝ)| ^ (-(2 : ℝ))
          else 0)) := by
      funext j
      by_cases hj : j = 0 <;> simp [hj]
    rw [hsum_eq]
    exact hmain.add hcorr
  exact Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbd hsum_maj

theorem dirichletConvolutionIntegrand_integrable {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (Φ : 𝓢(ℝ, ℂ)) (q : dirichletStageQuotient χ T p X α s hα hs) :
    let t0 : ℝ := Complex.arg (χ (p : ZMod N)) / Real.log p
    Integrable (fun u : ℝ ↦
      (Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) •
        dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u q) volume := by
  intro t0
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  have hc_cont : Continuous (fun u : ℝ ↦
      (Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u q) :=
    (Φ.continuous.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).smul
      (continuous_dirichletQuotModulatedAction_apply hχ hN T hT hp hpN hpT hX hα hs q)
  have hmaj : Integrable (fun u : ℝ ↦ ‖Φ u‖ * (dirichletQuotActionBound p α s * ‖q‖)) volume :=
    Φ.integrable.norm.mul_const (dirichletQuotActionBound p α s * ‖q‖)
  refine hmaj.mono' hc_cont.aestronglyMeasurable (Filter.Eventually.of_forall fun u ↦ ?_)
  have hexp_norm : ‖Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : ((t0 : ℂ) * Complex.I * (u : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre, Real.exp_zero]
  rw [norm_smul, norm_mul, hexp_norm, mul_one]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (norm_dirichletQuotModulatedAction_le hχ hN T hT hp hpT hX hα hs u) (norm_nonneg _))

/-- Convolution operator `T_Φ = ∫_ℝ Φ(u) exp(i t₀ u) τ_u du` acting on the Hilbert quotient
`dirichletStageQuotient χ T p X α s hα hs` (`t₀ = arg χ(p) / log p`).
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Deviation: Integrates over all of `ℝ` against the descended periodic circle action
`dirichletQuotModulatedAction`; for admissible positive-support tests supported inside
`[0, Real.log p]`, `dirichletConvolutionOp_eq_semigroup_of_support_subset` proves this equals
the pure positive-time forward-semigroup convolution `∫₀^∞ Φ(u) S(u) du` with no negative times.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
noncomputable def dirichletConvolutionOp {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (Φ : 𝓢(ℝ, ℂ)) :
    dirichletStageQuotient χ T p X α s hα hs →L[ℂ]
      dirichletStageQuotient χ T p X α s hα hs :=
  let t0 : ℝ := Complex.arg (χ (p : ZMod N)) / Real.log p
  let τ := dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs
  let f_op : dirichletStageQuotient χ T p X α s hα hs →
      dirichletStageQuotient χ T p X α s hα hs := fun q ↦
    ∫ u : ℝ, (Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u q
  have hint : ∀ q, Integrable (fun u : ℝ ↦
      (Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u q) volume :=
    dirichletConvolutionIntegrand_integrable hχ hN T hT hp hpN hpT hX hα hs Φ
  LinearMap.mkContinuous
    { toFun := f_op
      map_add' := fun q₁ q₂ ↦ by
        dsimp only [f_op]
        have hsum : (fun u : ℝ ↦
            (Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u (q₁ + q₂)) =
            fun u : ℝ ↦
              (Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u q₁ +
              (Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u q₂ := by
          funext u
          rw [map_add, smul_add]
        rw [hsum, integral_add (hint q₁) (hint q₂)]
      map_smul' := fun c q ↦ by
        dsimp only [f_op, RingHom.id_apply]
        have hsmul : (fun u : ℝ ↦
            (Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u (c • q)) =
            fun u : ℝ ↦ c • ((Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u q) := by
          funext u
          rw [map_smul, smul_comm]
        rw [hsmul, integral_smul] }
    (dirichletQuotActionBound p α s * ∫ u : ℝ, ‖Φ u‖)
    fun q ↦ by
      dsimp only [f_op, LinearMap.coe_mk, AddHom.coe_mk]
      have hnorm : ‖∫ u : ℝ, (Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u q‖ ≤
          ∫ u : ℝ, ‖(Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u q‖ :=
        norm_integral_le_integral_norm _
      have hle : ∫ u : ℝ, ‖(Φ u * Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))) • τ u q‖ ≤
          ∫ u : ℝ, ‖Φ u‖ * (dirichletQuotActionBound p α s * ‖q‖) := by
        refine integral_mono (hint q).norm (Φ.integrable.norm.mul_const _) fun u ↦ ?_
        have hexp_norm : ‖Complex.exp ((t0 : ℂ) * Complex.I * (u : ℂ))‖ = 1 := by
          rw [Complex.norm_exp]
          have hre : ((t0 : ℂ) * Complex.I * (u : ℂ)).re = 0 := by
            simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
          rw [hre, Real.exp_zero]
        rw [norm_smul, norm_mul, hexp_norm, mul_one]
        exact mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right
            (norm_dirichletQuotModulatedAction_le hχ hN T hT hp hpT hX hα hs u)
            (norm_nonneg _))) (norm_nonneg _)
      rw [integral_mul_const] at hle
      refine hnorm.trans (hle.trans_eq ?_)
      ring

theorem dirichletConvolutionOp_apply {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (Φ : 𝓢(ℝ, ℂ))
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    dirichletConvolutionOp hχ hN T hT hp hpN hpT hX hα hs Φ q =
      ∫ u : ℝ,
        (Φ u * Complex.exp (((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) *
          Complex.I * (u : ℂ))) •
          dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u q := rfl

/-- When `Φ` is supported inside the forward fundamental domain `[0, log p]`,
`dirichletConvolutionOp` coincides identically with convolution against the positive-time
forward semigroup `dirichletQuotSemigroup` (no negative times and no phase modulation).
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletConvolutionOp_eq_semigroup_of_support_subset {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (Φ : 𝓢(ℝ, ℂ))
    (hsupp : ∀ u : ℝ, Φ u ≠ 0 → 0 ≤ u ∧ u ≤ Real.log p)
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    dirichletConvolutionOp hχ hN T hT hp hpN hpT hX hα hs Φ q =
      ∫ u : ℝ,
        if hu : 0 ≤ u then Φ u • dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs u hu q
        else 0 := by
  rw [dirichletConvolutionOp_apply]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  dsimp only
  by_cases hΦ : Φ u = 0
  · split_ifs <;> simp [hΦ]
  · obtain ⟨hu0, huL⟩ := hsupp u hΦ
    split_ifs
    rw [dirichletQuotModulatedAction_eq_of_Icc hχ hN T hT hp hpN hpT hX hα hs hu0 huL,
      smul_apply, smul_smul, mul_assoc, ← Complex.exp_add]
    have hexp0 :
        (((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I * (u : ℂ) +
          -((Complex.arg (χ (p : ZMod N)) / Real.log p : ℂ) * Complex.I * (u : ℂ))) = 0 := by
      rw [Complex.ofReal_div]
      ring
    rw [hexp0, Complex.exp_zero, mul_one]

/-- Convolution operator `T_Φ` conjugated to `DirichletAvgQuotient`. -/
noncomputable def dirichletConvolutionOpAvg {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (Φ : 𝓢(ℝ, ℂ)) :
    DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs →L[ℂ]
      DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs :=
  (dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs).symm.toContinuousLinearMap.comp
    ((dirichletConvolutionOp hχ hN T hT hp hpN hpT hX hα hs Φ).comp
      (dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs).toContinuousLinearMap)

theorem dirichletConvolutionOpAvg_apply {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (Φ : 𝓢(ℝ, ℂ))
    (x : DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs) :
    dirichletConvolutionOpAvg hχ hN T hT hp hpN hpT hX hα hs Φ x =
      ∫ u : ℝ,
        (Φ u * Complex.exp (((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) *
          Complex.I * (u : ℂ))) •
          dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u x := by
  let e := dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs
  have hint := dirichletConvolutionIntegrand_integrable hχ hN T hT hp hpN hpT hX hα hs Φ (e x)
  have hcomm := (e.symm.toContinuousLinearMap.integral_comp_comm hint).symm
  change e.symm.toContinuousLinearMap (dirichletConvolutionOp hχ hN T hT hp hpN hpT hX hα hs Φ (e x)) = _
  rw [dirichletConvolutionOp_apply, hcomm]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
  dsimp only
  rw [map_smul]
  rfl

section DiagHelper

private noncomputable def lpDiag {ι : Type*} (c : ι → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ i, ‖c i‖ ≤ C) : lp (fun _ : ι ↦ ℂ) 2 →L[ℂ] lp (fun _ : ι ↦ ℂ) 2 :=
  LinearMap.mkContinuous
    { toFun := fun u ↦ ⟨fun i ↦ c i * u i, by
        refine memℓp_gen ?_
        have hu : Summable fun i : ι ↦ ‖u i‖ ^ (2 : ℝ) := by
          simpa only [ENNReal.toReal_ofNat] using
            (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp (lp.memℓp u)
        refine (hu.mul_left (C ^ 2)).of_nonneg_of_le (fun _ ↦ by positivity) fun i ↦ ?_
        rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num,
          Real.rpow_natCast, Real.rpow_natCast, norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (sq_le_sq' (by linarith [norm_nonneg (c i), hC]) (hc i)) (by positivity)⟩
      map_add' := fun u v ↦ by
        ext i
        simpa only [lp.coeFn_add, Pi.add_apply] using mul_add (c i) (u i) (v i)
      map_smul' := fun r u ↦ by
        ext i
        simpa only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] using
          mul_left_comm (c i) r (u i) }
    C
    fun u ↦ by
      have hu_sum : Summable fun i : ι ↦ ‖u i‖ ^ (2 : ℝ) := by
        simpa only [ENNReal.toReal_ofNat] using
          (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp (lp.memℓp u)
      have hpoint : ∀ i : ι, ‖c i * u i‖ ^ (2 : ℝ) ≤ C ^ 2 * ‖u i‖ ^ (2 : ℝ) := fun i ↦ by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
          Real.rpow_natCast, norm_mul, mul_pow]
        exact mul_le_mul_of_nonneg_right
          (sq_le_sq' (by linarith [norm_nonneg (c i), hC]) (hc i)) (by positivity)
      have hw_sum : Summable fun i : ι ↦ ‖c i * u i‖ ^ (2 : ℝ) :=
        (hu_sum.mul_left (C ^ 2)).of_nonneg_of_le (fun _ ↦ by positivity) hpoint
      have hnorm_eq : ∀ w : lp (fun _ : ι ↦ ℂ) 2,
          ‖w‖ ^ 2 = ∑' i : ι, ‖w i‖ ^ (2 : ℝ) := fun w ↦ by
        have h := lp.norm_rpow_eq_tsum (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) w
        rw [ENNReal.toReal_ofNat, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at h
        exact h
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      let w : lp (fun _ : ι ↦ ℂ) 2 :=
        ⟨fun i ↦ c i * u i, memℓp_gen (by simpa only [ENNReal.toReal_ofNat] using hw_sum)⟩
      change ‖w‖ ≤ C * ‖u‖
      have hsq : ‖w‖ ^ 2 ≤ (C * ‖u‖) ^ 2 := by
        rw [hnorm_eq w, mul_pow, hnorm_eq u]
        show (∑' i : ι, ‖c i * u i‖ ^ (2 : ℝ)) ≤ C ^ 2 * ∑' i : ι, ‖u i‖ ^ (2 : ℝ)
        rw [← tsum_mul_left]
        exact hw_sum.tsum_le_tsum hpoint (hu_sum.mul_left (C ^ 2))
      have hsqrt := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (mul_nonneg hC (norm_nonneg u))] at hsqrt
      exact hsqrt

private noncomputable def hilbertDiagCLM {ι : Type*} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (c : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    H →L[ℂ] H :=
  b.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((lpDiag c hC hc).comp b.repr.toLinearIsometry.toContinuousLinearMap)

private theorem hilbertDiagCLM_apply_basis {ι : Type*} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (c : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C)
    (j : ι) :
    hilbertDiagCLM b c hC hc (b j) = c j • b j := by
  classical
  dsimp only [hilbertDiagCLM]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  change b.repr.symm (lpDiag c hC hc (b.repr (b j))) = c j • b j
  have hsingle : lpDiag c hC hc (b.repr (b j)) = c j • b.repr (b j) := by
    ext i
    simp only [lpDiag, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mkContinuous_apply,
      lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, b.repr_self]
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  rw [hsingle, map_smul, b.repr.symm_apply_apply]

private theorem clm_eq_of_basis_eq {ι : Type*} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) {A B : H →L[ℂ] H} (hAB : ∀ i : ι, A (b i) = B (b i)) :
    A = B := by
  ext1 x
  have hx := b.hasSum_repr x
  have hA : HasSum (fun i : ι ↦ b.repr x i • A (b i)) (A x) := by
    simpa only [map_smul] using A.hasSum hx
  have hB : HasSum (fun i : ι ↦ b.repr x i • B (b i)) (B x) := by
    simpa only [map_smul] using B.hasSum hx
  simp_rw [hAB] at hA
  exact hA.unique hB

private theorem hilbertDiagCLM_mul {ι : Type*} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (c₁ c₂ : ι → ℂ) {C₁ C₂ : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hc₁ : ∀ i, ‖c₁ i‖ ≤ C₁) (hc₂ : ∀ i, ‖c₂ i‖ ≤ C₂) :
    hilbertDiagCLM b c₁ hC₁ hc₁ * hilbertDiagCLM b c₂ hC₂ hc₂ =
      hilbertDiagCLM b (fun i ↦ c₁ i * c₂ i) (mul_nonneg hC₁ hC₂)
        (fun i ↦ (by simp only [norm_mul]; exact mul_le_mul (hc₁ i) (hc₂ i) (norm_nonneg _) hC₁)) := by
  refine clm_eq_of_basis_eq b fun j ↦ ?_
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    hilbertDiagCLM_apply_basis, map_smul, hilbertDiagCLM_apply_basis,
    hilbertDiagCLM_apply_basis, smul_smul, mul_comm]

private theorem hilbertDiagCLM_adjoint {ι : Type*} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (c : ι → ℂ) {C : ℝ} (hC : 0 ≤ C) (hc : ∀ i, ‖c i‖ ≤ C) :
    (hilbertDiagCLM b c hC hc).adjoint =
      hilbertDiagCLM b (fun i ↦ starRingEnd ℂ (c i)) hC
        (fun i ↦ (by simp only [Complex.norm_conj]; exact hc i)) := by
  refine clm_eq_of_basis_eq b fun j ↦ ?_
  refine ext_inner_left ℂ fun v ↦ ?_
  have hv_sum := b.hasSum_repr v
  have hL : HasSum (fun i : ι ↦ starRingEnd ℂ (b.repr v i) *
      ⟪b i, (hilbertDiagCLM b c hC hc).adjoint (b j)⟫_ℂ)
      ⟪v, (hilbertDiagCLM b c hC hc).adjoint (b j)⟫_ℂ := by
    have hs := ((innerSL ℂ ((hilbertDiagCLM b c hC hc).adjoint (b j))).hasSum hv_sum)
    have hs' := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasSum hs
    simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, innerSL_apply_apply,
      inner_conj_symm, inner_smul_left] using hs'
  have hR : HasSum (fun i : ι ↦ starRingEnd ℂ (b.repr v i) *
      ⟪b i, hilbertDiagCLM b (fun i ↦ starRingEnd ℂ (c i)) hC
        (fun i ↦ (by simp only [Complex.norm_conj]; exact hc i)) (b j)⟫_ℂ)
      ⟪v, hilbertDiagCLM b (fun i ↦ starRingEnd ℂ (c i)) hC
        (fun i ↦ (by simp only [Complex.norm_conj]; exact hc i)) (b j)⟫_ℂ := by
    have hs := ((innerSL ℂ (hilbertDiagCLM b (fun i ↦ starRingEnd ℂ (c i)) hC
      (fun i ↦ (by simp only [Complex.norm_conj]; exact hc i)) (b j))).hasSum hv_sum)
    have hs' := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasSum hs
    simpa only [ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, innerSL_apply_apply,
      inner_conj_symm, inner_smul_left] using hs'
  rw [← hL.tsum_eq, ← hR.tsum_eq]
  refine tsum_congr fun i ↦ ?_
  congr 1
  rw [ContinuousLinearMap.adjoint_inner_right, hilbertDiagCLM_apply_basis,
    hilbertDiagCLM_apply_basis, inner_smul_left, inner_smul_right]
  by_cases hij : i = j
  · subst hij; rfl
  · simp only [b.orthonormal.2 hij, mul_zero]

private theorem hilbertDiagCLM_nonneg {ι : Type*} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (b : HilbertBasis ι ℂ H) (r : ι → ℝ) {C : ℝ} (hC : 0 ≤ C) (hr_nn : ∀ i, 0 ≤ r i)
    (hr : ∀ i, ‖(r i : ℂ)‖ ≤ C) :
    0 ≤ hilbertDiagCLM b (fun i ↦ (r i : ℂ)) hC hr := by
  classical
  rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
  intro x
  let D := hilbertDiagCLM b (fun i ↦ (r i : ℂ)) hC hr
  have hx := b.hasSum_repr x
  have hDx' : HasSum (fun i : ι ↦ b.repr x i • D (b i)) (D x) := by
    simpa only [map_smul] using D.hasSum hx
  have hinner_hasSum : HasSum (fun i : ι ↦ ((r i * ‖b.repr x i‖ ^ 2 : ℝ) : ℂ)) ⟪D x, x⟫_ℂ := by
    have hs : HasSum (fun i : ι ↦ ⟪b.repr x i • D (b i), x⟫_ℂ) ⟪D x, x⟫_ℂ := by
      let φ : H →L[ℂ] ℂ :=
        { toLinearMap :=
            { toFun := fun y ↦ ⟪x, y⟫_ℂ
              map_add' := fun _ _ ↦ inner_add_right _ _ _
              map_smul' := fun _ _ ↦ inner_smul_right _ _ _ }
          cont := continuous_const.inner continuous_id }
      have hconj := (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasSum (φ.hasSum hDx')
      simpa only [φ, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.coe_mk',
        ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, inner_conj_symm] using hconj
    refine hs.congr_fun fun i ↦ ?_
    dsimp only [D]
    rw [hilbertDiagCLM_apply_basis, smul_smul, inner_smul_left, b.repr_apply_apply,
      map_mul, Complex.conj_ofReal]
    have hconj_inner := Complex.mul_conj' ⟪b i, x⟫_ℂ
    calc ((r i * ‖⟪b i, x⟫_ℂ‖ ^ 2 : ℝ) : ℂ)
        = (r i : ℂ) * ((‖⟪b i, x⟫_ℂ‖ : ℂ) ^ 2) := by push_cast; rfl
      _ = (r i : ℂ) * (⟪b i, x⟫_ℂ * starRingEnd ℂ ⟪b i, x⟫_ℂ) := by rw [← hconj_inner]
      _ = (starRingEnd ℂ ⟪b i, x⟫_ℂ * (r i : ℂ)) * ⟪b i, x⟫_ℂ := by ring
  have hre_hasSum : HasSum (fun i : ι ↦ r i * ‖b.repr x i‖ ^ 2) (RCLike.re ⟪D x, x⟫_ℂ) := by
    rw [RCLike.re_eq_complex_re]
    simpa only [Complex.reCLM_apply, Complex.ofReal_re] using Complex.reCLM.hasSum hinner_hasSum
  have hre : (RCLike.re ⟪D x, x⟫_ℂ : ℂ) = ⟪D x, x⟫_ℂ := by
    have hc := Complex.ofRealCLM.hasSum hre_hasSum
    simpa only [Complex.ofRealCLM_apply] using hc.unique hinner_hasSum
  have hnn : 0 ≤ RCLike.re ⟪D x, x⟫_ℂ := by
    rw [← hre_hasSum.tsum_eq]
    exact tsum_nonneg fun i ↦ mul_nonneg (hr_nn i) (sq_nonneg _)
  exact ⟨hre, hnn⟩

private theorem exists_orthonormal_upperTriangular {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (A : H →L[ℂ] H) :
    ∀ {m : ℕ} (e : Fin m → H) (lam : Fin m → ℂ),
      LinearIndependent ℂ e → (∀ k, A (e k) = lam k • e k) →
      ∃ u : Fin m → H, Orthonormal ℂ u ∧
        Submodule.span ℂ (Set.range u) = Submodule.span ℂ (Set.range e) ∧
        ∀ k : Fin m, ⟪u k, A (u k)⟫_ℂ = lam k := by
  intro m
  induction m with
  | zero =>
    intro e lam _ _
    refine ⟨Fin.elim0, ?_, ?_, fun k ↦ k.elim0⟩
    · rw [orthonormal_iff_ite]
      intro i
      exact i.elim0
    · simp only [Set.range_eq_empty, Submodule.span_empty]
  | succ m ih =>
    intro e lam hli heig
    let e' : Fin m → H := fun i ↦ e i.castSucc
    let lam' : Fin m → ℂ := fun i ↦ lam i.castSucc
    have hli' : LinearIndependent ℂ e' := hli.comp Fin.castSucc fun _ _ h ↦ Fin.castSucc_injective _ h
    obtain ⟨u', hu'_on, hspan', hdiag'⟩ := ih e' lam' hli' fun i ↦ heig i.castSucc
    let w : H := ∑ i : Fin m, ⟪u' i, e (Fin.last m)⟫_ℂ • u' i
    let r : H := e (Fin.last m) - w
    have hw_mem_u : w ∈ Submodule.span ℂ (Set.range u') :=
      Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hw_mem_e : w ∈ Submodule.span ℂ (Set.range e') := hspan' ▸ hw_mem_u
    have hr_ne : r ≠ 0 := by
      intro hr0
      have he_mem : e (Fin.last m) ∈ Submodule.span ℂ (Set.range e') := by
        have : e (Fin.last m) = w := sub_eq_zero.mp hr0
        rw [this]
        exact hw_mem_e
      obtain ⟨c_fs, hc_fs⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp he_mem
      let c : Fin m → ℂ := c_fs
      have hc : ∑ i : Fin m, c i • e' i = e (Fin.last m) := by
        rw [Finsupp.sum] at hc_fs
        exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ by
          simp [c, Finsupp.notMem_support_iff.mp hi]).symm.trans hc_fs
      let c' : Fin (m + 1) → ℂ := Fin.snoc c (-1)
      have hsum0 : ∑ j : Fin (m + 1), c' j • e j = 0 := by
        rw [Fin.sum_univ_castSucc]
        simp only [c', Fin.snoc_castSucc, Fin.snoc_last, neg_smul, one_smul]
        change (∑ i : Fin m, c i • e' i) + -e (Fin.last m) = 0
        rw [hc, add_neg_cancel]
      have hlast0 := Fintype.linearIndependent_iff.mp hli c' hsum0 (Fin.last m)
      have hc' : c' (Fin.last m) = -1 := by dsimp only [c']; simp
      rw [hc'] at hlast0
      norm_num at hlast0
    have hr_norm_pos : 0 < ‖r‖ := norm_pos_iff.mpr hr_ne
    let u_last : H := ((‖r‖ : ℂ)⁻¹) • r
    let u : Fin (m + 1) → H := Fin.snoc u' u_last
    have hu'_ortho_r : ∀ j : Fin m, ⟪u' j, r⟫_ℂ = 0 := fun j ↦ by
      dsimp only [r, w]
      rw [inner_sub_right, inner_sum]
      have hsum_eq : ∑ i : Fin m, ⟪u' j, ⟪u' i, e (Fin.last m)⟫_ℂ • u' i⟫_ℂ =
          ⟪u' j, e (Fin.last m)⟫_ℂ := by
        calc ∑ i : Fin m, ⟪u' j, ⟪u' i, e (Fin.last m)⟫_ℂ • u' i⟫_ℂ
            = ∑ i : Fin m, ⟪u' i, e (Fin.last m)⟫_ℂ * (if j = i then (1 : ℂ) else 0) := by
              refine Finset.sum_congr rfl fun i _ ↦ ?_
              rw [inner_smul_right, orthonormal_iff_ite.mp hu'_on j i]
          _ = ⟪u' j, e (Fin.last m)⟫_ℂ := by simp
      rw [hsum_eq, sub_self]
    have hu_last_left : ∀ j' : Fin m, ⟪u_last, u' j'⟫_ℂ = 0 := fun j' ↦ by
      dsimp only [u_last]
      rw [inner_smul_left, ← inner_conj_symm, hu'_ortho_r j', map_zero, mul_zero]
    have hu_last_right : ∀ i' : Fin m, ⟪u' i', u_last⟫_ℂ = 0 := fun i' ↦ by
      dsimp only [u_last]
      rw [inner_smul_right, hu'_ortho_r i', mul_zero]
    have hu_last_norm : ‖u_last‖ = 1 := by
      dsimp only [u_last]
      rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg r),
        inv_mul_cancel₀ hr_norm_pos.ne']
    have hu_on : Orthonormal ℂ u := by
      rw [orthonormal_iff_ite]
      intro i j
      refine Fin.lastCases ?_ (fun i' ↦ ?_) i <;> refine Fin.lastCases ?_ (fun j' ↦ ?_) j
      · simp only [u, Fin.snoc_last, ↓reduceIte, inner_self_eq_norm_sq_to_K, hu_last_norm]
        norm_num
      · simp only [u, Fin.snoc_last, Fin.snoc_castSucc, (Fin.castSucc_lt_last j').ne', ↓reduceIte]
        exact hu_last_left j'
      · simp only [u, Fin.snoc_castSucc, Fin.snoc_last, (Fin.castSucc_lt_last i').ne, ↓reduceIte]
        exact hu_last_right i'
      · simp only [u, Fin.snoc_castSucc, Fin.castSucc_inj]
        exact (orthonormal_iff_ite.mp hu'_on) i' j'
    have hrange_u : Set.range u = insert u_last (Set.range u') := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        refine Fin.lastCases (Or.inl (by simp [u])) (fun j ↦ Or.inr ⟨j, by simp [u]⟩) i
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨Fin.last m, by simp [u]⟩
        · exact ⟨i.castSucc, by simp [u]⟩
    have hrange_e : Set.range e = insert (e (Fin.last m)) (Set.range e') := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        refine Fin.lastCases (Or.inl rfl) (fun j ↦ Or.inr ⟨j, rfl⟩) i
      · rintro (rfl | ⟨i, rfl⟩)
        · exact ⟨Fin.last m, rfl⟩
        · exact ⟨i.castSucc, rfl⟩
    have hspan_eq : Submodule.span ℂ (Set.range u) = Submodule.span ℂ (Set.range e) := by
      rw [hrange_u, hrange_e, Submodule.span_insert, Submodule.span_insert, hspan']
      apply le_antisymm
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have hr_mem : r ∈ (ℂ ∙ e (Fin.last m)) ⊔ Submodule.span ℂ (Set.range e') :=
          Submodule.sub_mem (p := (ℂ ∙ e (Fin.last m)) ⊔ Submodule.span ℂ (Set.range e'))
            (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
            (Submodule.mem_sup_right hw_mem_e)
        exact Submodule.smul_mem _ _ hr_mem
      · refine sup_le ?_ le_sup_right
        rw [Submodule.span_singleton_le_iff_mem]
        have hr_eq : r = (‖r‖ : ℂ) • u_last := by
          dsimp only [u_last]
          rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr_norm_pos.ne'), one_smul]
        have he_eq : e (Fin.last m) = (‖r‖ : ℂ) • u_last + w := by
          rw [← hr_eq]
          dsimp only [r]
          abel
        rw [he_eq]
        exact Submodule.add_mem (p := (ℂ ∙ u_last) ⊔ Submodule.span ℂ (Set.range e'))
          (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
          (Submodule.mem_sup_right hw_mem_e)
    have hA_inv : ∀ v ∈ Submodule.span ℂ (Set.range e'), A v ∈ Submodule.span ℂ (Set.range e') := by
      intro v hv
      refine Submodule.span_induction (fun y hy ↦ ?_) (by simp)
        (fun x y _ _ hx hy ↦ by
          rw [map_add]
          exact Submodule.add_mem (p := Submodule.span ℂ (Set.range e')) hx hy)
        (fun c x _ hx ↦ by rw [map_smul]; exact Submodule.smul_mem _ _ hx) hv
      rcases hy with ⟨i, rfl⟩
      dsimp only [e']
      rw [heig i.castSucc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hu_last_ortho_span : ∀ v ∈ Submodule.span ℂ (Set.range u'), ⟪u_last, v⟫_ℂ = 0 := by
      intro v hv
      refine Submodule.span_induction (fun y hy ↦ ?_) (inner_zero_right _)
        (fun x y _ _ hx hy ↦ by rw [inner_add_right, hx, hy, add_zero])
        (fun c x _ hx ↦ by rw [inner_smul_right, hx, mul_zero]) hv
      rcases hy with ⟨i, rfl⟩
      exact hu_last_left i
    have hdiag_last : ⟪u_last, A u_last⟫_ℂ = lam (Fin.last m) := by
      let μ : ℂ := lam (Fin.last m)
      have hAr_sub : A r - μ • r ∈ Submodule.span ℂ (Set.range u') := by
        have heq : A r - μ • r = -(A w - μ • w) := by
          dsimp only [r, μ]
          rw [map_sub, heig (Fin.last m), smul_sub]
          abel
        rw [heq]
        have hw_mul : μ • w ∈ Submodule.span ℂ (Set.range e') :=
          Submodule.smul_mem (Submodule.span ℂ (Set.range e')) μ hw_mem_e
        have hAw_sub : A w - μ • w ∈ Submodule.span ℂ (Set.range e') :=
          Submodule.sub_mem (p := Submodule.span ℂ (Set.range e')) (hA_inv w hw_mem_e) hw_mul
        rw [← hspan'] at hAw_sub
        exact Submodule.neg_mem (p := Submodule.span ℂ (Set.range u')) hAw_sub
      have hinner_diff : ⟪u_last, A r - μ • r⟫_ℂ = 0 := hu_last_ortho_span _ hAr_sub
      rw [inner_sub_right, inner_smul_right, sub_eq_zero] at hinner_diff
      have hinner_u : ⟪u_last, r⟫_ℂ = (‖r‖ : ℂ) := by
        have hr_eq : r = (‖r‖ : ℂ) • u_last := by
          dsimp only [u_last]
          rw [smul_smul, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hr_norm_pos.ne'), one_smul]
        conv_lhs => rw [hr_eq]
        rw [inner_smul_right, inner_self_eq_norm_sq_to_K, hu_last_norm]
        simp
      have hAu : A u_last = ((‖r‖ : ℂ)⁻¹) • A r := map_smul A _ _
      rw [hAu, inner_smul_right, hinner_diff, hinner_u,
        mul_left_comm, inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hr_norm_pos.ne'), mul_one]
    refine ⟨u, hu_on, hspan_eq, fun k ↦ ?_⟩
    refine Fin.lastCases ?_ (fun k' ↦ ?_) k
    · simpa only [u, Fin.snoc_last] using hdiag_last
    · simpa only [u, Fin.snoc_castSucc] using hdiag' k'

private theorem sum_norm_eigenvalues_le_traceNorm {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : nuclearEndomorphisms H) {m : ℕ} (e : Fin m → H) (lam : Fin m → ℂ)
    (hli : LinearIndependent ℂ e) (heig : ∀ k : Fin m, T.val (e k) = lam k • e k) :
    ∑ k : Fin m, ‖lam k‖ ≤ traceNorm T := by
  classical
  obtain ⟨u, hu_on, _, hdiag⟩ := exists_orthonormal_upperTriangular T.val e lam hli heig
  let θ : Fin m → ℂ := fun k ↦ if lam k = 0 then 0 else starRingEnd ℂ (lam k) / (‖lam k‖ : ℂ)
  have hθ_norm : ∀ k : Fin m, ‖θ k‖ ≤ 1 := fun k ↦ by
    dsimp only [θ]
    split_ifs with h0
    · simp
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h0)]
  have hθ_mul : ∀ k : Fin m, θ k * lam k = (‖lam k‖ : ℂ) := fun k ↦ by
    dsimp only [θ]
    split_ifs with h0
    · simp [h0]
    · rw [div_mul_eq_mul_div, mul_comm (starRingEnd ℂ (lam k)), Complex.mul_conj', sq,
        mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0))]
  let V : H →L[ℂ] H := ∑ k : Fin m, (θ k • innerSL ℂ (u k)).smulRight (u k)
  have hV_apply : ∀ x : H, V x = ∑ k : Fin m, (θ k * ⟪u k, x⟫_ℂ) • u k := fun x ↦ by
    dsimp only [V]
    simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
      smul_apply, smul_eq_mul, innerSL_apply_apply]
  have hV_norm : ‖V‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
    rw [one_mul]
    let c : Fin m → ℂ := fun k ↦ ⟪u k, x⟫_ℂ
    let z : H := ∑ k : Fin m, c k • u k
    have hnorm_sum : ∀ d : Fin m → ℂ,
        ‖∑ k : Fin m, d k • u k‖ ^ 2 = ∑ k : Fin m, ‖d k‖ ^ 2 := fun d ↦ by
      have hre_sq : (‖∑ k : Fin m, d k • u k‖ ^ 2 : ℝ) =
          (⟪∑ k : Fin m, d k • u k, ∑ k : Fin m, d k • u k⟫_ℂ).re := by
        rw [← RCLike.re_eq_complex_re, ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
      rw [hre_sq, sum_inner]
      simp_rw [inner_sum, inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hu_on]
      have hinner_d : ∑ i : Fin m, ∑ j : Fin m,
          starRingEnd ℂ (d i) * (d j * (if i = j then (1 : ℂ) else 0)) =
          ∑ k : Fin m, ((‖d k‖ ^ 2 : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        have hsing : ∑ j : Fin m, starRingEnd ℂ (d k) * (d j * (if k = j then (1 : ℂ) else 0)) =
            starRingEnd ℂ (d k) * d k := by
          simp
        rw [hsing, mul_comm (starRingEnd ℂ (d k)), Complex.mul_conj']
        push_cast; rfl
      rw [hinner_d, Complex.re_sum]
      refine Finset.sum_congr rfl fun k _ ↦ Complex.ofReal_re _
    have hinner_xz : ⟪x, z⟫_ℂ = ∑ k : Fin m, ((‖c k‖ ^ 2 : ℝ) : ℂ) := by
      dsimp only [z]
      rw [inner_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [inner_smul_right, ← inner_conj_symm x (u k)]
      change c k * starRingEnd ℂ (c k) = ((‖c k‖ ^ 2 : ℝ) : ℂ)
      rw [Complex.mul_conj']
      push_cast; rfl
    have hinner_zx : ⟪z, x⟫_ℂ = ∑ k : Fin m, ((‖c k‖ ^ 2 : ℝ) : ℂ) := by
      rw [← inner_conj_symm, hinner_xz, map_sum]
      refine Finset.sum_congr rfl fun k _ ↦ Complex.conj_ofReal _
    have hbessel : ∑ k : Fin m, ‖c k‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      have hsub_nn : 0 ≤ ‖x - z‖ ^ 2 := sq_nonneg _
      have hsub_eq : ‖x - z‖ ^ 2 = (⟪x - z, x - z⟫_ℂ).re := by
        rw [← RCLike.re_eq_complex_re, ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
      have hzz : ⟪z, z⟫_ℂ = ∑ k : Fin m, ((‖c k‖ ^ 2 : ℝ) : ℂ) := by
        dsimp only [z]
        rw [sum_inner]
        simp_rw [inner_sum, inner_smul_left, inner_smul_right, orthonormal_iff_ite.mp hu_on]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        have hsing : ∑ j : Fin m, starRingEnd ℂ (c k) * (c j * (if k = j then (1 : ℂ) else 0)) =
            starRingEnd ℂ (c k) * c k := by
          simp
        rw [hsing, mul_comm (starRingEnd ℂ (c k)), Complex.mul_conj']
        push_cast; rfl
      have hxx : (⟪x, x⟫_ℂ).re = ‖x‖ ^ 2 := by
        rw [← RCLike.re_eq_complex_re, ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)]
      rw [hsub_eq, inner_sub_left, inner_sub_right, inner_sub_right, hinner_xz, hinner_zx, hzz,
        Complex.sub_re, Complex.sub_re, Complex.sub_re, hxx] at hsub_nn
      simp only [Complex.re_sum, Complex.ofReal_re] at hsub_nn
      linarith
    have hVx_sq : ‖V x‖ ^ 2 ≤ ‖x‖ ^ 2 := by
      rw [hV_apply, hnorm_sum]
      calc ∑ k : Fin m, ‖θ k * c k‖ ^ 2
          = ∑ k : Fin m, ‖θ k‖ ^ 2 * ‖c k‖ ^ 2 := by
            refine Finset.sum_congr rfl fun k _ ↦ ?_
            rw [norm_mul, mul_pow]
        _ ≤ ∑ k : Fin m, 1 * ‖c k‖ ^ 2 := by
            refine Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
            have hk := hθ_norm k
            nlinarith [norm_nonneg (θ k)]
        _ = ∑ k : Fin m, ‖c k‖ ^ 2 := by simp
        _ ≤ ‖x‖ ^ 2 := hbessel
    have hsqrt := Real.sqrt_le_sqrt hVx_sq
    rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hsqrt
  let VT : nuclearEndomorphisms H := ⟨V * T.val, mul_mem_nuclearEndomorphisms_left V T⟩
  let VT_sum : nuclearEndomorphisms H := ∑ k : Fin m,
    ⟨((θ k • innerSL ℂ (u k)).comp T.val).smulRight (u k), smulRight_mem_nuclearEndomorphisms _ _⟩
  have hVT_eq : VT = VT_sum := by
    apply Subtype.ext
    rw [show VT.val = V * T.val from rfl,
      show VT_sum.val = ∑ k : Fin m, ((θ k • innerSL ℂ (u k)).comp T.val).smulRight (u k) by
        simp [VT_sum]]
    ext1 x
    rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, hV_apply, sum_apply]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    simp [ContinuousLinearMap.smulRight_apply]
  have htr_VT : hilbertTrace VT = ((∑ k : Fin m, ‖lam k‖ : ℝ) : ℂ) := by
    obtain ⟨L, hL⟩ := hilbertTrace_linear (H := H)
    rw [hVT_eq, ← hL VT_sum, map_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hL, hilbertTrace_smulRight, ContinuousLinearMap.comp_apply,
      smul_apply, smul_eq_mul, innerSL_apply_apply, hdiag k, hθ_mul k]
  have htn_nn : 0 ≤ traceNorm T := (norm_nonneg (hilbertTrace T)).trans (norm_hilbertTrace_le T)
  calc ∑ k : Fin m, ‖lam k‖
      = ‖((∑ k : Fin m, ‖lam k‖ : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
    _ = ‖hilbertTrace VT‖ := by rw [htr_VT]
    _ ≤ traceNorm VT := norm_hilbertTrace_le VT
    _ ≤ ‖V‖ * traceNorm T := traceNorm_mul_left_le V T
    _ ≤ 1 * traceNorm T := mul_le_mul_of_nonneg_right hV_norm htn_nn
    _ = traceNorm T := one_mul _

end DiagHelper

/-- **Per-packet trace and trace-norm expansion for the convolution operator on fixed-box quotients.**
For any Schwartz kernel `Φ : 𝓢(ℝ, ℂ)`:
1. On the averaged Hilbert space `Q_avg`, the convolution operator `dirichletConvolutionOpAvg Φ` is
   diagonal in the unconditional orthonormal basis `b` from `dirichletFixedBox_unconditional_basis`,
   with eigenvalues `λ_j = dirichletConvEigenvalue χ p Φ j`, is nuclear, has Hilbert/nuclear trace
   `∑' j, λ_j`, and has trace norm `∑' j, ‖λ_j‖`.
2. On the original Sobolev quotient `Q`, the convolution operator `dirichletConvolutionOp Φ` is
   nuclear, has the exact same Hilbert/nuclear trace `∑' j, λ_j`, and satisfies the Weyl
   eigenvalue bound `∑' j, ‖λ_j‖ ≤ traceNorm ⟨dirichletConvolutionOp Φ, _⟩` (via Gram–Schmidt on
   finite spans of eigenvectors inside `Q`).
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletFixedBox_convolution_trace_expansion {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (Φ : 𝓢(ℝ, ℂ)) :
    let Q := dirichletStageQuotient χ T p X α s hα hs
    let Q_avg := DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs
    let T_Q : Q →L[ℂ] Q := dirichletConvolutionOp hχ hN T hT hp hpN hpT hX hα hs Φ
    let T_avg : Q_avg →L[ℂ] Q_avg := dirichletConvolutionOpAvg hχ hN T hT hp hpN hpT hX hα hs Φ
    ∃ (hN_avg : IsNuclearOperator T_avg) (hN_Q : IsNuclearOperator T_Q),
      hilbertTrace ⟨T_avg, hN_avg⟩ = ∑' j : ℤ, dirichletConvEigenvalue χ p Φ j ∧
      traceNorm ⟨T_avg, hN_avg⟩ = ∑' j : ℤ, ‖dirichletConvEigenvalue χ p Φ j‖ ∧
      hilbertTrace ⟨T_Q, hN_Q⟩ = ∑' j : ℤ, dirichletConvEigenvalue χ p Φ j ∧
      ∑' j : ℤ, ‖dirichletConvEigenvalue χ p Φ j‖ ≤ traceNorm ⟨T_Q, hN_Q⟩ := by
  intro Q Q_avg T_Q T_avg
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  obtain ⟨b, hb_eig, _, _, _, _⟩ :=
    dirichletFixedBox_unconditional_basis hχ hN T hT hp hpN hpT hX hα hs
  let eig := dirichletConvEigenvalue χ p Φ
  have hC_int : 0 ≤ ∫ u : ℝ, ‖Φ u‖ := integral_nonneg fun _ ↦ norm_nonneg _
  have heig_bd : ∀ j : ℤ, ‖eig j‖ ≤ ∫ u : ℝ, ‖Φ u‖ := fun j ↦ by
    dsimp only [eig, dirichletConvEigenvalue]
    refine (norm_integral_le_integral_norm _).trans_eq ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
    have hexp1 : ‖Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (u : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have hre : ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (u : ℂ)).re = 0 := by
        simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
      rw [hre, Real.exp_zero]
    dsimp only
    rw [norm_mul, hexp1, mul_one]
  have hT_avg_eig : ∀ j : ℤ, T_avg (b j) = eig j • b j := by
    intro j
    dsimp only [T_avg]
    rw [dirichletConvolutionOpAvg_apply]
    have hrew : (fun u : ℝ ↦
        (Φ u * Complex.exp (((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) *
          Complex.I * (u : ℂ))) •
          dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u (b j)) =
        fun u : ℝ ↦
          (Φ u * Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (u : ℂ))) • b j := by
      funext u
      rw [hb_eig j u, smul_smul]
      congr 1
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      dsimp only [dirichletPrimeFreq]
      push_cast
      have hL_C : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
      field_simp [hL_C]
    change ∫ u : ℝ,
        (Φ u * Complex.exp (((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) *
          Complex.I * (u : ℂ))) •
          dirichletAvgModulatedAction χ hχ hN T hT p hp hpN hpT X α s hX hα hs u (b j) =
      eig j • b j
    rw [hrew, integral_smul_const]
    rfl
  let D := hilbertDiagCLM b eig hC_int heig_bd
  have hT_eq_D : T_avg = D := clm_eq_of_basis_eq b fun j ↦ by
    rw [hT_avg_eig j, hilbertDiagCLM_apply_basis]
  let D_abs := hilbertDiagCLM b (fun j ↦ (‖eig j‖ : ℂ)) hC_int
    (fun j ↦ by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact heig_bd j)
  have hsqrt_eq : CFC.sqrt (T_avg.adjoint * T_avg) = D_abs := by
    apply CFC.sqrt_unique
    · rw [hT_eq_D, hilbertDiagCLM_adjoint, hilbertDiagCLM_mul, hilbertDiagCLM_mul]
      refine clm_eq_of_basis_eq b fun j ↦ ?_
      rw [hilbertDiagCLM_apply_basis, hilbertDiagCLM_apply_basis]
      congr 1
      have hmul : (‖eig j‖ : ℂ) * (‖eig j‖ : ℂ) = starRingEnd ℂ (eig j) * eig j := by
        simpa only [sq, mul_comm] using (Complex.mul_conj' (eig j)).symm
      rw [hmul]
    · exact hilbertDiagCLM_nonneg b (fun j ↦ ‖eig j‖) hC_int (fun _ ↦ norm_nonneg _)
        (fun j ↦ by rw [Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]; exact heig_bd j)
  have hb_diag : ∀ j : ℤ, ⟪b j, b j⟫_ℂ = 1 := fun j ↦ by
    simp [inner_self_eq_norm_sq_to_K, b.orthonormal.1 j]
  have hdiag_re : ∀ j : ℤ,
      (⟪b j, CFC.sqrt (T_avg.adjoint * T_avg) (b j)⟫_ℂ).re = ‖eig j‖ := fun j ↦ by
    rw [hsqrt_eq, hilbertDiagCLM_apply_basis, inner_smul_right, hb_diag j, mul_one,
      Complex.ofReal_re]
  have hsum_eig : Summable fun j : ℤ ↦ ‖eig j‖ :=
    summable_norm_dirichletConvEigenvalue χ hp Φ
  have hN_avg : IsNuclearOperator T_avg := by
    rw [isNuclearOperator_iff_summable_traceNorm_diagonal b]
    exact hsum_eig.congr fun j ↦ (hdiag_re j).symm
  have htr_avg : hilbertTrace ⟨T_avg, hN_avg⟩ = ∑' j : ℤ, eig j := by
    let b₀ := (exists_hilbertBasis (𝕜 := ℂ) (E := Q_avg)).choose_spec.choose
    change (∑' i, ⟪b₀ i, T_avg (b₀ i)⟫_ℂ) = ∑' j : ℤ, eig j
    rw [tsum_hilbertDiagonal_eq b₀ b T_avg hN_avg]
    refine tsum_congr fun j ↦ ?_
    rw [hT_avg_eig j, inner_smul_right, hb_diag j, mul_one]
  have htn_avg : traceNorm ⟨T_avg, hN_avg⟩ = ∑' j : ℤ, ‖eig j‖ := by
    have hhs : HasSum (fun j : ℤ ↦ (⟪b j, CFC.sqrt (T_avg.adjoint * T_avg) (b j)⟫_ℂ).re)
        (traceNorm ⟨T_avg, hN_avg⟩) :=
      hasSum_traceNorm_diagonal b ⟨T_avg, hN_avg⟩
    exact (hhs.congr_fun fun j ↦ (hdiag_re j).symm).tsum_eq.symm
  let e := dirichletAvgEquivQ χ hχ hN T hT p hp hpN hpT X α s hX hα hs
  let A₀ : Q →L[ℂ] Q_avg := T_avg.comp e.symm.toContinuousLinearMap
  have hA₀ : IsNuclearOperator A₀ := by
    obtain ⟨c, φ, y, hc, hφ, hy, hseries⟩ :=
      (isNuclearOperator_iff_isBanachNuclear T_avg).mp hN_avg
    refine (isNuclearOperator_iff_isBanachNuclear A₀).mpr ?_
    let precomp := (ContinuousLinearMap.compL ℂ Q Q_avg ℂ).flip e.symm.toContinuousLinearMap
    refine ⟨c, fun n ↦ (φ n).comp e.symm.toContinuousLinearMap, y, hc, ?_, hy, fun q ↦ ?_⟩
    · change Filter.Tendsto (⇑precomp ∘ φ) Filter.atTop (nhds 0)
      simpa only [map_zero] using (precomp.continuous.tendsto 0).comp hφ
    · simpa only [A₀, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe] using
        hseries (e.symm q)
  have hfc := isNuclearOperator_factor_comps e.toContinuousLinearMap e.injective A₀ hA₀
  have hT_Q_eq : e.toContinuousLinearMap.comp A₀ = T_Q := by
    ext1 q
    rfl
  have hN_Q : IsNuclearOperator T_Q := by
    rw [← hT_Q_eq]
    exact hfc.2
  have hT_avg_eq : A₀.comp e.toContinuousLinearMap = T_avg := by
    ext1 x
    rfl
  have hnt_eq := nuclearTrace_factor_comps hilbert_approximationProperty
    hilbert_approximationProperty e.toContinuousLinearMap e.injective A₀ hA₀
  have htr_Q : hilbertTrace ⟨T_Q, hN_Q⟩ = ∑' j : ℤ, eig j := by
    rw [hilbertTrace_eq_nuclearTrace ⟨T_Q, hN_Q⟩]
    have heq1 : nuclearTrace hilbert_approximationProperty T_Q hN_Q =
        nuclearTrace hilbert_approximationProperty (e.toContinuousLinearMap.comp A₀) hfc.2 := by
      congr 1
    have heq2 : nuclearTrace hilbert_approximationProperty (A₀.comp e.toContinuousLinearMap) hfc.1 =
        nuclearTrace hilbert_approximationProperty T_avg hN_avg := by
      congr 1
    rw [heq1, ← hnt_eq, heq2, ← hilbertTrace_eq_nuclearTrace ⟨T_avg, hN_avg⟩, htr_avg]
  have hT_Q_eig : ∀ j : ℤ, T_Q (e (b j)) = eig j • e (b j) := fun j ↦ by
    have heq : T_Q (e (b j)) = e (T_avg (b j)) := by
      change T_Q (e (b j)) = e (e.symm (T_Q (e (b j))))
      rw [e.apply_symm_apply]
    rw [heq, hT_avg_eig j, map_smul]
  have hweyl_fin : ∀ S : Finset ℤ, ∑ j ∈ S, ‖eig j‖ ≤ traceNorm ⟨T_Q, hN_Q⟩ := by
    intro S
    let idx : Fin S.card → ℤ := fun k ↦ (S.equivFin.symm k).1
    have hidx_inj : Function.Injective idx := fun a b hab ↦
      S.equivFin.symm.injective (Subtype.ext hab)
    let e_S : Fin S.card → Q := fun k ↦ e (b (idx k))
    have hb_li : LinearIndependent ℂ (fun j : ℤ ↦ b j) :=
      linearIndependent_of_ne_zero_of_inner_eq_zero
        (fun j hz ↦ by
          have h1 := b.orthonormal.1 j
          simp [hz] at h1)
        (fun i j hij ↦ b.orthonormal.2 hij)
    have he_S_li : LinearIndependent ℂ e_S :=
      (hb_li.comp idx hidx_inj).map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
    have hle_fin := sum_norm_eigenvalues_le_traceNorm ⟨T_Q, hN_Q⟩ e_S (fun k ↦ eig (idx k))
      he_S_li fun k ↦ hT_Q_eig (idx k)
    have hsum_eq : ∑ j ∈ S, ‖eig j‖ = ∑ k : Fin S.card, ‖eig (idx k)‖ := by
      rw [← Finset.sum_attach S fun j ↦ ‖eig j‖]
      refine (Fintype.sum_equiv S.equivFin (fun j : S ↦ ‖eig j.1‖)
        (fun k : Fin S.card ↦ ‖eig (idx k)‖) fun j ↦ ?_).symm.symm
      dsimp only [idx]
      simp
    rw [hsum_eq]
    exact hle_fin
  have hweyl_le : ∑' j : ℤ, ‖eig j‖ ≤ traceNorm ⟨T_Q, hN_Q⟩ :=
    le_of_tendsto hsum_eig.hasSum (Filter.Eventually.of_forall hweyl_fin)
  exact ⟨hN_avg, hN_Q, htr_avg, htn_avg, htr_Q, hweyl_le⟩

noncomputable def dirichletPositiveBumpFun : ContDiffBump (3 / 64 : ℝ) :=
  ⟨1 / 128, 1 / 64, by norm_num, by norm_num⟩

/-- Admissible smooth compactly supported test `Φ₊` supported strictly inside
`[1 / 32, 1 / 16] ⊂ (0, Real.log 2) ⊆ (0, Real.log p)` for every prime `p`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
noncomputable def dirichletPositiveBump : 𝓢(ℝ, ℂ) :=
  (dirichletPositiveBumpFun.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp dirichletPositiveBumpFun.contDiff)

@[simp]
theorem dirichletPositiveBump_apply (u : ℝ) :
    dirichletPositiveBump u = (dirichletPositiveBumpFun u : ℂ) := rfl

theorem dirichletPositiveBump_support (u : ℝ) (hu : dirichletPositiveBump u ≠ 0) :
    1 / 32 ≤ u ∧ u ≤ 1 / 16 := by
  have hne : dirichletPositiveBumpFun u ≠ 0 := fun h0 ↦
    hu (by simp only [dirichletPositiveBump_apply, h0, Complex.ofReal_zero])
  have hmem : u ∈ Metric.ball (3 / 64 : ℝ) (1 / 64 : ℝ) := by
    have hs := dirichletPositiveBumpFun.support_eq
    change u ∈ Function.support dirichletPositiveBumpFun at hne
    rw [hs] at hne
    exact hne
  rw [Metric.mem_ball, Real.dist_eq] at hmem
  have hlt := abs_lt.mp hmem
  exact ⟨by linarith, by linarith⟩

theorem dirichletPositiveBump_integral_ge :
    1 / 64 ≤ ∫ u : ℝ, dirichletPositiveBumpFun u := by
  let S : Set ℝ := Set.Icc (5 / 128 : ℝ) (7 / 128 : ℝ)
  have hS_meas : MeasurableSet S := measurableSet_Icc
  have hφ_int : Integrable (fun u : ℝ ↦ dirichletPositiveBumpFun u) volume :=
    dirichletPositiveBumpFun.continuous.integrable_of_hasCompactSupport
      dirichletPositiveBumpFun.hasCompactSupport
  have hrin : dirichletPositiveBumpFun.rIn = 1 / 128 := rfl
  have h_le : ∫ u in S, (1 : ℝ) ∂volume ≤ ∫ u : ℝ, dirichletPositiveBumpFun u := by
    have h1 : IntegrableOn (fun _ : ℝ ↦ (1 : ℝ)) S volume :=
      continuousOn_const.integrableOn_Icc
    have hmono := setIntegral_mono_on h1 hφ_int.integrableOn hS_meas fun u hu ↦ by
      refine (dirichletPositiveBumpFun.one_of_mem_closedBall ?_).symm.le
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le, hrin]
      rcases hu with ⟨hu1, hu2⟩
      exact ⟨by linarith, by linarith⟩
    refine hmono.trans (setIntegral_le_integral hφ_int (Filter.Eventually.of_forall fun _ ↦
      dirichletPositiveBumpFun.nonneg))
  have hS_int : ∫ _ in S, (1 : ℝ) ∂volume = 1 / 64 := by
    dsimp only [S]
    rw [setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc_of_le (by norm_num)]
    norm_num
  linarith

/-- For any compactly supported Schwartz kernel `Φ` strictly supported inside `(0, Real.log p)`,
Poisson summation on the shifted frequency lattice forces the packet trace `∑' j, λ_j(Φ)`
to vanish identically.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem tsum_dirichletConvEigenvalue_eq_zero_of_support_Ioo {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (Φ : 𝓢(ℝ, ℂ))
    (hsupp : ∀ u : ℝ, Φ u ≠ 0 → 0 < u ∧ u < Real.log p) :
    ∑' j : ℤ, dirichletConvEigenvalue χ p Φ j = 0 := by
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let t0 : ℝ := Complex.arg (χ (p : ZMod N))
  let g0 : ℝ → ℂ := fun x ↦ Φ (L * x) * Complex.exp ((t0 : ℂ) * Complex.I * (x : ℂ))
  have hg0_smooth : ContDiff ℝ ∞ g0 :=
    ((Φ.smooth (⊤ : ℕ∞)).comp (contDiff_const.mul contDiff_id)).mul
      (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff))
  have hg0_supp : tsupport g0 ⊆ Set.Icc (0 : ℝ) 1 := by
    refine closure_minimal (fun x hx ↦ ?_) isClosed_Icc
    change g0 x ≠ 0 at hx
    have hΦ_ne : Φ (L * x) ≠ 0 := fun h0 ↦ hx (by simp [g0, h0])
    obtain ⟨hpos, hlt⟩ := hsupp (L * x) hΦ_ne
    have hx0 : 0 ≤ x := by nlinarith
    have hx1 : x ≤ 1 := by nlinarith
    exact ⟨hx0, hx1⟩
  have hg0_cs : HasCompactSupport g0 :=
    isCompact_Icc.of_isClosed_subset isClosed_closure hg0_supp
  let g_mod : 𝓢(ℝ, ℂ) := hg0_cs.toSchwartzMap hg0_smooth
  have hg0_int : ∀ k : ℤ, g_mod (k : ℝ) = 0 := fun k ↦ by
    change Φ (L * (k : ℝ)) * Complex.exp ((t0 : ℂ) * Complex.I * ((k : ℝ) : ℂ)) = 0
    have hΦ0 : Φ (L * (k : ℝ)) = 0 := by
      by_contra hne
      obtain ⟨hpos, hlt⟩ := hsupp (L * (k : ℝ)) hne
      have hk0 : (0 : ℝ) < k := by nlinarith
      have hk1 : (k : ℝ) < 1 := by nlinarith
      have hki0 : (0 : ℤ) < k := by exact_mod_cast hk0
      have hki1 : k < (1 : ℤ) := by exact_mod_cast hk1
      omega
    rw [hΦ0, zero_mul]
  have hfourier_eq : ∀ j : ℤ,
      (𝓕 g_mod) (-(j : ℝ)) = ((L⁻¹ : ℝ) : ℂ) * dirichletConvEigenvalue χ p Φ j := by
    intro j
    rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
    have hrew : (fun x : ℝ ↦
        Complex.exp ((-2 * Real.pi * x * (-(j : ℝ)) : ℝ) * Complex.I) • g_mod x) =
        fun x : ℝ ↦
          Φ (L * x) * Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * ((L * x : ℝ) : ℂ)) := by
      funext x
      rw [smul_eq_mul]
      change Complex.exp ((-2 * Real.pi * x * (-(j : ℝ)) : ℝ) * Complex.I) *
          (Φ (L * x) * Complex.exp ((t0 : ℂ) * Complex.I * (x : ℂ))) =
        Φ (L * x) * Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * ((L * x : ℝ) : ℂ))
      rw [mul_left_comm, ← Complex.exp_add]
      refine congrArg (fun z ↦ Φ (L * x) * Complex.exp z) ?_
      have harg_real : -2 * Real.pi * x * (-(j : ℝ)) + t0 * x = dirichletPrimeFreq χ p j * (L * x) := by
        dsimp only [dirichletPrimeFreq, t0, L]
        have hlog0 : Real.log (p : ℝ) ≠ 0 := hL_pos.ne'
        field_simp [hlog0]
        ring
      have harg_C := congrArg (fun r : ℝ ↦ (r : ℂ) * Complex.I) harg_real
      push_cast at harg_C ⊢
      linear_combination harg_C
    rw [hrew]
    have hcov := MeasureTheory.Measure.integral_comp_mul_left
      (fun u : ℝ ↦ Φ u * Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (u : ℂ))) L
    simpa only [abs_of_pos (inv_pos.mpr hL_pos), Complex.real_smul, dirichletConvEigenvalue] using hcov
  have hpoiss := SchwartzMap.tsum_eq_tsum_fourier g_mod 0
  have hlhs : ∑' k : ℤ, g_mod (0 + k) = 0 := by
    simp only [zero_add, hg0_int, tsum_zero]
  have hrhs : ∑' m : ℤ, (𝓕 g_mod) (m : ℝ) * fourier m ((0 : ℝ) : UnitAddCircle) =
      ((L⁻¹ : ℝ) : ℂ) * ∑' j : ℤ, dirichletConvEigenvalue χ p Φ j := by
    have hterm0 : (fun m : ℤ ↦ (𝓕 g_mod) (m : ℝ) * fourier m ((0 : ℝ) : UnitAddCircle)) =
        fun m : ℤ ↦ (𝓕 g_mod) (m : ℝ) := by
      funext m
      simp
    rw [hterm0]
    have hneg : ∑' m : ℤ, (𝓕 g_mod) (m : ℝ) = ∑' j : ℤ, (𝓕 g_mod) (-(j : ℝ)) := by
      refine ((Equiv.neg ℤ).tsum_eq (fun m : ℤ ↦ (𝓕 g_mod) (m : ℝ))).symm.trans ?_
      congr 1
      funext j
      simp only [Equiv.neg_apply, Int.cast_neg]
    rw [hneg]
    simp_rw [hfourier_eq]
    exact tsum_mul_left
  rw [hlhs, hrhs] at hpoiss
  have hmulL := congrArg (fun z : ℂ ↦ (L : ℂ) * z) hpoiss.symm
  rw [mul_zero, ← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hL_pos.ne', Complex.ofReal_one,
    one_mul] at hmulL
  exact hmulL

/-- **Admissible positive-support zero-trace / `log p` trace-norm lower bound (obstruction).**
Using the single universal bump `Φ₊ := dirichletPositiveBump` supported strictly inside
`[1 / 32, 1 / 16] ⊂ (0, log 2) ⊆ (0, log p)`:
1. `T_{Φ₊, Q}` agrees identically with positive-time forward-semigroup convolution;
2. Its trace on both `Q_avg` and `Q` vanishes identically (`hilbertTrace = 0`);
3. Yet there exists an explicit universal constant `c₀ > 0` (independent of `χ, N, T, p, X, α, s`)
   such that `c₀ * Real.log p ≤ traceNorm ⟨T_{Φ₊, avg}, _⟩` and `c₀ * Real.log p ≤ traceNorm ⟨T_{Φ₊, Q}, _⟩`
   at every stage `(T, p, X, α, s)` and for every primitive character `χ : DirichletCharacter ℂ N`.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletFixedBox_traceNorm_lower_bound :
    ∃ c₀ > (0 : ℝ),
      ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
        (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
        {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
        {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s),
        let Q := dirichletStageQuotient χ T p X α s hα hs
        let Q_avg := DirichletAvgQuotient χ hχ hN T hT p hp hpN hpT X α s hX hα hs
        let T_Q : Q →L[ℂ] Q :=
          dirichletConvolutionOp hχ hN T hT hp hpN hpT hX hα hs dirichletPositiveBump
        let T_avg : Q_avg →L[ℂ] Q_avg :=
          dirichletConvolutionOpAvg hχ hN T hT hp hpN hpT hX hα hs dirichletPositiveBump
        (∀ q : Q, T_Q q =
          ∫ u : ℝ,
            if hu : 0 ≤ u then
              dirichletPositiveBump u • dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs u hu q
            else 0) ∧
        ∃ (hN_avg : IsNuclearOperator T_avg) (hN_Q : IsNuclearOperator T_Q),
          hilbertTrace ⟨T_avg, hN_avg⟩ = 0 ∧
          hilbertTrace ⟨T_Q, hN_Q⟩ = 0 ∧
          c₀ * Real.log p ≤ traceNorm ⟨T_avg, hN_avg⟩ ∧
          c₀ * Real.log p ≤ traceNorm ⟨T_Q, hN_Q⟩ := by
  let c₀ : ℝ := 1 / (256 * Real.pi)
  have hc₀ : 0 < c₀ := by
    dsimp only [c₀]
    positivity
  refine ⟨c₀, hc₀, ?_⟩
  intro N _ χ hχ hN T hT p hp hpN hpT X α s hX hα hs Q Q_avg T_Q T_avg
  let L : ℝ := Real.log p
  have hL_pos : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog2_le_L : Real.log 2 ≤ L :=
    Real.log_le_log zero_lt_two (by exact_mod_cast hp.two_le)
  have hlog2_gt : (1 / 2 : ℝ) < Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hsupp_Ioo : ∀ u : ℝ, dirichletPositiveBump u ≠ 0 → 0 < u ∧ u < L := fun u hu ↦ by
    obtain ⟨h1, h2⟩ := dirichletPositiveBump_support u hu
    exact ⟨by linarith, by linarith⟩
  have hsupp_Icc : ∀ u : ℝ, dirichletPositiveBump u ≠ 0 → 0 ≤ u ∧ u ≤ L := fun u hu ↦
    ⟨(hsupp_Ioo u hu).1.le, (hsupp_Ioo u hu).2.le⟩
  obtain ⟨hN_avg, hN_Q, htr_avg, htn_avg, htr_Q, hweyl_Q⟩ :=
    dirichletFixedBox_convolution_trace_expansion hχ hN T hT hp hpN hpT hX hα hs
      dirichletPositiveBump
  have htr0 : ∑' j : ℤ, dirichletConvEigenvalue χ p dirichletPositiveBump j = 0 :=
    tsum_dirichletConvEigenvalue_eq_zero_of_support_Ioo χ hp dirichletPositiveBump hsupp_Ioo
  let B₀ : ℝ := Real.pi / Real.log 2 + 1
  have hB₀_lt : B₀ < 9 := by
    dsimp only [B₀]
    have hpi4 : Real.pi < 4 := Real.pi_lt_four
    have hdiv_lt : Real.pi / Real.log 2 < 4 / (1 / 2 : ℝ) := by
      have h1 : Real.pi / Real.log 2 < 4 / Real.log 2 := div_lt_div_of_pos_right hpi4 hlog2_pos
      have h2 : 4 / Real.log 2 < 4 / (1 / 2 : ℝ) :=
        div_lt_div_of_pos_left (by norm_num) (by norm_num) hlog2_gt
      exact h1.trans h2
    linarith
  let M_cnt : ℕ := Nat.floor (L / (2 * Real.pi)) + 1
  let S_fin : Finset ℤ := Finset.image (fun k : ℕ ↦ (k : ℤ)) (Finset.range M_cnt)
  let eig := dirichletConvEigenvalue χ p dirichletPositiveBump
  have h_sum_eig : Summable fun j : ℤ ↦ ‖eig j‖ :=
    summable_norm_dirichletConvEigenvalue χ hp dirichletPositiveBump
  have hterm_lb : ∀ j ∈ S_fin, (1 / 128 : ℝ) ≤ ‖eig j‖ := by
    intro j hj
    rw [Finset.mem_image] at hj
    rcases hj with ⟨k, hk, rfl⟩
    rw [Finset.mem_range] at hk
    have hk_le : (k : ℝ) ≤ L / (2 * Real.pi) := by
      have hk1 : k ≤ Nat.floor (L / (2 * Real.pi)) := Nat.lt_succ_iff.mp hk
      exact (Nat.cast_le.mpr hk1).trans (Nat.floor_le (by positivity))
    have h2pik : 0 ≤ 2 * Real.pi * (k : ℝ) := by positivity
    have h2pik_le : 2 * Real.pi * (k : ℝ) ≤ L := by
      calc 2 * Real.pi * (k : ℝ) ≤ 2 * Real.pi * (L / (2 * Real.pi)) :=
            mul_le_mul_of_nonneg_left hk_le (by positivity)
        _ = L := by field_simp [Real.pi_ne_zero]
    have hfreq_bd : |dirichletPrimeFreq χ p (k : ℤ)| ≤ B₀ := by
      dsimp only [dirichletPrimeFreq, B₀]
      rw [abs_div, abs_of_pos hL_pos]
      have harg_le : |Complex.arg (χ (p : ZMod N))| ≤ Real.pi := Complex.abs_arg_le_pi _
      have hnum : |Complex.arg (χ (p : ZMod N)) + 2 * Real.pi * ((k : ℤ) : ℝ)| ≤ Real.pi + L := by
        calc |Complex.arg (χ (p : ZMod N)) + 2 * Real.pi * ((k : ℤ) : ℝ)|
            ≤ |Complex.arg (χ (p : ZMod N))| + |2 * Real.pi * (k : ℝ)| := by
              simpa only [Int.cast_natCast] using
                abs_add_le (Complex.arg (χ (p : ZMod N))) (2 * Real.pi * (k : ℝ))
          _ ≤ Real.pi + L := add_le_add harg_le (by rw [abs_of_nonneg h2pik]; exact h2pik_le)
      have hdiv_le : Real.pi / L ≤ Real.pi / Real.log 2 :=
        div_le_div_of_nonneg_left Real.pi_pos.le hlog2_pos hlog2_le_L
      calc |Complex.arg (χ (p : ZMod N)) + 2 * Real.pi * ((k : ℤ) : ℝ)| / L
          ≤ (Real.pi + L) / L := div_le_div_of_nonneg_right hnum hL_pos.le
        _ = Real.pi / L + 1 := by field_simp [hL_pos.ne']
        _ ≤ Real.pi / Real.log 2 + 1 := by linarith
    have hfreq_lt : |dirichletPrimeFreq χ p (k : ℤ)| < 9 := hfreq_bd.trans_lt hB₀_lt
    let freq : ℝ := dirichletPrimeFreq χ p (k : ℤ)
    have hint_f : Integrable (fun u : ℝ ↦
        dirichletPositiveBump u * Complex.exp ((freq : ℂ) * Complex.I * (u : ℂ))) volume := by
      have hint_norm : Integrable (fun u : ℝ ↦ ‖dirichletPositiveBump u‖) volume :=
        dirichletPositiveBump.integrable.norm
      refine hint_norm.mono' ?_ (Filter.Eventually.of_forall fun u ↦ ?_)
      · exact (dirichletPositiveBump.continuous.mul
          (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable
      · have hexp1 : ‖Complex.exp ((freq : ℂ) * Complex.I * (u : ℂ))‖ = 1 := by
          rw [Complex.norm_exp]
          have hre : ((freq : ℂ) * Complex.I * (u : ℂ)).re = 0 := by
            simp [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
          rw [hre, Real.exp_zero]
        rw [norm_mul, hexp1, mul_one]
    have hre_eig : (eig (k : ℤ)).re =
        ∫ u : ℝ, dirichletPositiveBumpFun u * Real.cos (freq * u) := by
      dsimp only [eig, dirichletConvEigenvalue]
      change (∫ u : ℝ, dirichletPositiveBump u *
          Complex.exp ((freq : ℂ) * Complex.I * (u : ℂ))).re = _
      rw [← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint_f]
      refine integral_congr_ae (Filter.Eventually.of_forall fun u ↦ ?_)
      simp only [Complex.reCLM_apply, dirichletPositiveBump_apply]
      have hexp_eq : Complex.exp ((freq : ℂ) * Complex.I * (u : ℂ)) =
          Complex.cos ((freq * u : ℝ) : ℂ) + Complex.sin ((freq * u : ℝ) : ℂ) * Complex.I := by
        rw [show (freq : ℂ) * Complex.I * (u : ℂ) = ((freq * u : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.exp_mul_I]
      rw [hexp_eq, ← Complex.ofReal_cos, ← Complex.ofReal_sin, mul_add, Complex.add_re]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
      ring
    have hφ_int : Integrable (fun u : ℝ ↦ dirichletPositiveBumpFun u) volume :=
      dirichletPositiveBumpFun.continuous.integrable_of_hasCompactSupport
        dirichletPositiveBumpFun.hasCompactSupport
    have hφ_cos_int : Integrable (fun u : ℝ ↦ dirichletPositiveBumpFun u * Real.cos (freq * u)) volume :=
      (hφ_int.norm).mono'
        ((dirichletPositiveBumpFun.continuous.mul
          (Real.continuous_cos.comp (continuous_const.mul continuous_id))).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun u ↦ by
          rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (abs_nonneg _))
    have hpt_lb : ∀ u : ℝ,
        (1 / 2 : ℝ) * dirichletPositiveBumpFun u ≤
          dirichletPositiveBumpFun u * Real.cos (freq * u) := fun u ↦ by
      by_cases hu0 : dirichletPositiveBump u = 0
      · have hφ0 : dirichletPositiveBumpFun u = 0 := by
          simpa [dirichletPositiveBump_apply] using hu0
        simp [hφ0]
      · obtain ⟨hu_lo, hu_hi⟩ := dirichletPositiveBump_support u hu0
        have hwu_le : |freq * u| ≤ Real.pi / 3 := by
          rw [abs_mul, abs_of_pos (by linarith : 0 < u)]
          have h1 : |freq| * u ≤ 9 * (1 / 16 : ℝ) :=
            mul_le_mul hfreq_lt.le hu_hi (by linarith) (by norm_num)
          have hpi3 : (1 : ℝ) < Real.pi / 3 := by linarith [Real.pi_gt_three]
          linarith
        have hcos_lb : (1 / 2 : ℝ) ≤ Real.cos (freq * u) := by
          rw [← Real.cos_pi_div_three, ← Real.cos_abs (freq * u)]
          exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
            (by linarith [Real.pi_pos]) hwu_le
        rw [mul_comm (1 / 2 : ℝ)]
        exact mul_le_mul_of_nonneg_left hcos_lb dirichletPositiveBumpFun.nonneg
    have hre_ge : (1 / 128 : ℝ) ≤ (eig (k : ℤ)).re := by
      rw [hre_eig]
      have h1 : (1 / 2 : ℝ) * ∫ u : ℝ, dirichletPositiveBumpFun u ≤
          ∫ u : ℝ, dirichletPositiveBumpFun u * Real.cos (freq * u) := by
        rw [← integral_const_mul]
        exact integral_mono (hφ_int.const_mul _) hφ_cos_int hpt_lb
      linarith [dirichletPositiveBump_integral_ge]
    exact hre_ge.trans (Complex.re_le_norm _)
  have hsum_lb : c₀ * L ≤ ∑' j : ℤ, ‖eig j‖ := by
    have hfin_le : ∑ j ∈ S_fin, ‖eig j‖ ≤ ∑' j : ℤ, ‖eig j‖ :=
      h_sum_eig.sum_le_tsum S_fin fun j _ ↦ norm_nonneg _
    have hcard : S_fin.card = M_cnt := by
      dsimp only [S_fin]
      rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    have hM_gt : L / (2 * Real.pi) < (M_cnt : ℝ) := by
      dsimp only [M_cnt]
      push_cast
      exact Nat.lt_floor_add_one _
    have hfin_lb : c₀ * L ≤ ∑ j ∈ S_fin, ‖eig j‖ := by
      calc c₀ * L
          = (L / (2 * Real.pi)) * (1 / 128 : ℝ) := by
            dsimp only [c₀]; ring
        _ ≤ (M_cnt : ℝ) * (1 / 128 : ℝ) :=
            mul_le_mul_of_nonneg_right hM_gt.le (by norm_num)
        _ = ∑ _ ∈ S_fin, (1 / 128 : ℝ) := by
            rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ ≤ ∑ j ∈ S_fin, ‖eig j‖ := Finset.sum_le_sum hterm_lb
    exact hfin_lb.trans hfin_le
  refine ⟨fun q ↦ dirichletConvolutionOp_eq_semigroup_of_support_subset hχ hN T hT hp hpN hpT
    hX hα hs dirichletPositiveBump hsupp_Icc q, hN_avg, hN_Q, ?_, ?_, ?_, ?_⟩
  · exact htr_avg.trans htr0
  · exact htr_Q.trans htr0
  · exact hsum_lb.trans htn_avg.symm.le
  · exact hsum_lb.trans hweyl_Q

end ConvolutionAndTraceNorm

end CircleActionAndTraceNorm

end RiemannMasullo.Isolated
