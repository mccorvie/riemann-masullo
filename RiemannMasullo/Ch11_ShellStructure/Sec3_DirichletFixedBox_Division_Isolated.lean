module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Lifts_Isolated
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes (Division)

Mesh bump cardinal lifts in a fixed box and exact denominator division (`dirichletFixedBox_cardinal_lifts`, `dirichletFixedBox_stage_exact_division`).

Nothing outside the `Sec3_DirichletFixedBox*` / `Sec3_RatBridge*` isolated stack imports this module.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField RiemannMasullo Set Topology
open scoped BigOperators ContDiff FourierTransform NNReal Real SchwartzMap

namespace RiemannMasullo.Isolated

section CardinalLiftsAndDivision

open MeasureTheory Filter Topology Real
open scoped InnerProductSpace Convolution

/-- Smooth compactly supported unit bump on the `L`-periodic logarithmic mesh `[y₀, y₀ + L + 1]`,
orthogonal to all nonzero frequencies `2 * π * k / L` (`k ≠ 0`).
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
def dirichletMeshBump (L y₀ : ℝ) : ℝ → ℝ :=
  let φ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by positivity, by norm_num⟩
  let η : ℝ → ℝ := φ.normed volume
  let box : ℝ → ℝ := fun y ↦ L⁻¹ * Set.indicator (Set.Ioc (y₀ + 1 / 2) (y₀ + 1 / 2 + L)) 1 y
  η ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] box

theorem contDiff_dirichletMeshBump (L y₀ : ℝ) :
    ContDiff ℝ ∞ (dirichletMeshBump L y₀) := by
  let φ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by positivity, by norm_num⟩
  let box : ℝ → ℝ := fun y ↦ L⁻¹ * Set.indicator (Set.Ioc (y₀ + 1 / 2) (y₀ + 1 / 2 + L)) 1 y
  have hbox_int : Integrable box volume :=
    (IntegrableOn.integrable_indicator
      (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc).const_mul _
  exact (φ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ)
    (φ.contDiff_normed (μ := volume)) hbox_int.locallyIntegrable

theorem tsupport_dirichletMeshBump_subset {L : ℝ} (_hL : 0 < L) (y₀ : ℝ) :
    tsupport (dirichletMeshBump L y₀) ⊆ Set.Icc y₀ (y₀ + L + 1) := by
  let φ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by positivity, by norm_num⟩
  let η : ℝ → ℝ := φ.normed volume
  let box : ℝ → ℝ := fun y ↦ L⁻¹ * Set.indicator (Set.Ioc (y₀ + 1 / 2) (y₀ + 1 / 2 + L)) 1 y
  refine closure_minimal ?_ isClosed_Icc
  intro y hy
  dsimp only [dirichletMeshBump] at hy
  have hsub := support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) (f := η) (g := box) (μ := volume) hy
  rw [Set.mem_add] at hsub
  obtain ⟨v, hv, w, hw, rfl⟩ := hsub
  have hv_ball : v ∈ Metric.ball (0 : ℝ) (1 / 2) := by
    rwa [← φ.support_normed_eq (μ := volume)]
  have hv_abs : |v| < 1 / 2 := by simpa [Real.dist_eq] using hv_ball
  have hv_Icc : v ∈ Set.Icc (-1 / 2) (1 / 2) := by
    have := abs_lt.mp hv_abs
    exact ⟨by linarith, by linarith⟩
  have hw_Ioc : w ∈ Set.Ioc (y₀ + 1 / 2) (y₀ + 1 / 2 + L) := by
    by_contra hnot
    apply hw
    dsimp [box]
    rw [Set.indicator_of_notMem hnot, mul_zero]
  exact ⟨by linarith [hv_Icc.1, hw_Ioc.1], by linarith [hv_Icc.2, hw_Ioc.2]⟩

theorem dirichletMeshBump_fourier {L : ℝ} (hL : 0 < L) (y₀ : ℝ) (k : ℤ) :
    ∫ y : ℝ, (dirichletMeshBump L y₀ y : ℂ) *
        Complex.exp ((2 * Real.pi * (k : ℝ) / L : ℂ) * Complex.I * (y : ℂ)) =
      if k = 0 then 1 else 0 := by
  let φ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by positivity, by norm_num⟩
  let η : ℝ → ℝ := φ.normed volume
  let box : ℝ → ℝ := fun y ↦ L⁻¹ * Set.indicator (Set.Ioc (y₀ + 1 / 2) (y₀ + 1 / 2 + L)) 1 y
  let freq : ℝ := 2 * Real.pi * (k : ℝ) / L
  let ηℂ : ℝ → ℂ := fun v ↦ (η v : ℂ) * Complex.exp ((freq : ℂ) * Complex.I * (v : ℂ))
  let boxℂ : ℝ → ℂ := fun w ↦ (box w : ℂ) * Complex.exp ((freq : ℂ) * Complex.I * (w : ℂ))
  have hη_int : Integrable η volume := φ.integrable_normed
  have hbox_int : Integrable box volume :=
    (IntegrableOn.integrable_indicator
      (continuousOn_const.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self) measurableSet_Ioc).const_mul _
  have hηℂ_int : Integrable ηℂ volume := by
    refine Integrable.mono' hη_int.norm
      (((Complex.continuous_ofReal.comp φ.continuous_normed).mul
        (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun v ↦ ?_)
    rw [norm_mul, Complex.norm_real, Complex.norm_exp]
    have hre : ((freq : ℂ) * Complex.I * (v : ℂ)).re = 0 := by simp [mul_re]
    rw [hre, Real.exp_zero, mul_one]
  have hboxℂ_int : Integrable boxℂ volume := by
    refine Integrable.mono' hbox_int.norm ?_ (Filter.Eventually.of_forall fun w ↦ ?_)
    · exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable hbox_int.aestronglyMeasurable).mul
        (Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable)
    · rw [norm_mul, Complex.norm_real, Complex.norm_exp]
      have hre : ((freq : ℂ) * Complex.I * (w : ℂ)).re = 0 := by simp [mul_re]
      rw [hre, Real.exp_zero, mul_one]
  have hconv_eq : (fun y : ℝ ↦ (dirichletMeshBump L y₀ y : ℂ) *
        Complex.exp ((2 * Real.pi * (k : ℝ) / L : ℂ) * Complex.I * (y : ℂ))) =
      ηℂ ⋆[ContinuousLinearMap.mul ℂ ℂ, volume] boxℂ := by
    ext y
    dsimp only [dirichletMeshBump, convolution]
    simp only [ContinuousLinearMap.mul_apply']
    have hfreq_coe : (2 * Real.pi * (k : ℝ) / L : ℂ) = (freq : ℂ) := by
      dsimp [freq]; push_cast; rfl
    rw [hfreq_coe, ← Complex.ofRealCLM_apply, ← Complex.ofRealCLM.integral_comp_comm]
    · rw [← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v ↦ ?_)
      dsimp only [ηℂ, boxℂ]
      rw [Complex.ofRealCLM_apply, Complex.ofReal_mul]
      have hexp : Complex.exp ((freq : ℂ) * Complex.I * (y : ℂ)) =
          Complex.exp ((freq : ℂ) * Complex.I * (v : ℂ)) *
            Complex.exp ((freq : ℂ) * Complex.I * ((y - v : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1; push_cast; ring
      rw [hexp]
      ring
    · have hex := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
          (ContinuousLinearMap.mul ℝ ℝ) φ.continuous_normed hbox_int.locallyIntegrable y
      exact hex
  rw [hconv_eq, integral_convolution (ContinuousLinearMap.mul ℂ ℂ) hηℂ_int hboxℂ_int]
  simp only [ContinuousLinearMap.mul_apply']
  by_cases hk : k = 0
  · subst hk
    simp only [↓reduceIte]
    have hηℂ_0 : ηℂ = fun v ↦ (η v : ℂ) := by
      ext v; simp [ηℂ, freq]
    have hboxℂ_0 : boxℂ = fun w ↦ (box w : ℂ) := by
      ext w; simp [boxℂ, freq]
    have h1 : (∫ v : ℝ, ηℂ v) = 1 := by
      rw [hηℂ_0]
      change ∫ v : ℝ, Complex.ofRealCLM (η v) = 1
      rw [Complex.ofRealCLM.integral_comp_comm hη_int]
      simp [η, φ.integral_normed]
    have h2 : (∫ w : ℝ, boxℂ w) = 1 := by
      rw [hboxℂ_0]
      change ∫ w : ℝ, Complex.ofRealCLM (box w) = 1
      rw [Complex.ofRealCLM.integral_comp_comm hbox_int, Complex.ofRealCLM_apply]
      have hint_box : ∫ w : ℝ, box w = 1 := by
        dsimp only [box]
        rw [integral_const_mul, integral_indicator measurableSet_Ioc]
        simp_rw [Pi.one_apply]
        rw [MeasureTheory.setIntegral_const, smul_eq_mul,
          Real.volume_real_Ioc_of_le (by linarith)]
        field_simp [hL.ne']
        ring
      rw [hint_box, Complex.ofReal_one]
    rw [h1, h2, mul_one]
  · simp only [hk, ↓reduceIte]
    have hfreq_ne : (freq : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      dsimp [freq]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) (Int.cast_ne_zero.mpr hk)) hL.ne'
    have hbox_zero : ∫ w : ℝ, boxℂ w = 0 := by
      have heq_ind : boxℂ = Set.indicator (Set.Ioc (y₀ + 1 / 2) (y₀ + 1 / 2 + L))
          (fun w : ℝ ↦ (L⁻¹ : ℂ) * Complex.exp ((freq : ℂ) * Complex.I * (w : ℂ))) := by
        ext w
        by_cases hw : w ∈ Set.Ioc (y₀ + 1 / 2) (y₀ + 1 / 2 + L)
        · rw [Set.indicator_of_mem hw]; dsimp [boxℂ, box]
          rw [Set.indicator_of_mem hw, Pi.one_apply, mul_one, Complex.ofReal_inv]
        · rw [Set.indicator_of_notMem hw]; dsimp [boxℂ, box]
          rw [Set.indicator_of_notMem hw, mul_zero, Complex.ofReal_zero, zero_mul]
      rw [heq_ind, integral_indicator measurableSet_Ioc,
        ← intervalIntegral.integral_of_le (by linarith)]
      rw [intervalIntegral.integral_const_mul]
      let F : ℝ → ℂ := fun w ↦ ((freq : ℂ) * Complex.I)⁻¹ * Complex.exp ((freq : ℂ) * Complex.I * (w : ℂ))
      have hderiv : ∀ w ∈ Set.uIcc (y₀ + 1 / 2) (y₀ + 1 / 2 + L),
          HasDerivAt F (Complex.exp ((freq : ℂ) * Complex.I * (w : ℂ))) w := by
        intro w _
        have hlin2 : HasDerivAt (fun z : ℝ ↦ (freq : ℂ) * Complex.I * (z : ℂ)) ((freq : ℂ) * Complex.I) w := by
          simpa using (hasDerivAt_id w).ofReal_comp.const_mul ((freq : ℂ) * Complex.I)
        exact (hlin2.cexp.const_mul ((freq : ℂ) * Complex.I)⁻¹).congr_deriv
          (by field_simp [hfreq_ne, Complex.I_ne_zero])
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
        ((Complex.continuous_exp.comp (by fun_prop)).intervalIntegrable _ _)]
      have hperiod : F (y₀ + 1 / 2 + L) = F (y₀ + 1 / 2) := by
        dsimp [F]
        congr 1
        have harg : (freq : ℂ) * Complex.I * ((y₀ + 1 / 2 + L : ℝ) : ℂ) =
            (freq : ℂ) * Complex.I * ((y₀ + 1 / 2 : ℝ) : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) := by
          dsimp [freq]
          push_cast
          field_simp [hL.ne']
        rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      rw [hperiod, sub_self, mul_zero]
    rw [hbox_zero, mul_zero]

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Constructive existence of exact same-box smooth cardinal lifts `f_j` inside the shrunk box
`X / ∏_{q ∈ T} q`, biorthogonal to `dirichletNormalizedRow χ T p` and of polynomial Sobolev-strip
norm growth in `|j|`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletFixedBox_cardinal_lifts {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let _hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
    let R : ℝ := X / ∏ q ∈ T, (q : ℝ)
    ∃ f : ℤ → 𝓢(ℝ, ℂ),
      (∀ j : ℤ, IsDirichletFixedBoxTest χ R (f j)) ∧
      (∀ j : ℤ, MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ (f j))) 2
        (intervalSobolevMeasure volume id (-α) α s false)) ∧
      (∀ j m : ℤ,
        ∀ (hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ (f j))) 2
          (intervalSobolevMeasure volume id (-α) α s false)),
          dirichletNormalizedRow χ T p X α s hα hs m
            (toDirichletStrip α s _ hmem) = if m = j then 1 else 0) ∧
      (∃ K : ℕ, ∃ C > (0 : ℝ), ∀ j : ℤ,
        ∀ (hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ (f j))) 2
          (intervalSobolevMeasure volume id (-α) α s false)),
          ‖toDirichletStrip α s _ hmem‖ ≤ C * (1 + |(j : ℝ)|) ^ K) := by
  intro _hTpos R
  have hprod_pos : 0 < ∏ q ∈ T, (q : ℝ) :=
    Finset.prod_pos fun q hq ↦ by exact_mod_cast (hT q hq).1.pos
  have hR_pos : 0 < R := div_pos hX hprod_pos
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  let L : ℝ := Real.log p
  let y₀ : ℝ := Real.log R - L - 2
  let a : ℝ := y₀
  let b : ℝ := y₀ + L + 1
  have hb_le : b ≤ Real.log R := by dsimp [b, y₀]; linarith
  let β : ℝ → ℂ := fun y ↦ (dirichletMeshBump L y₀ y : ℂ)
  have hβ_smooth : ContDiff ℝ ∞ β :=
    Complex.ofRealCLM.contDiff.comp (contDiff_dirichletMeshBump L y₀)
  have hβ_supp : tsupport β ⊆ Set.Icc a b := by
    have hcomp : support β = support (dirichletMeshBump L y₀) := by
      ext y; simp [β]
    change closure (support β) ⊆ Set.Icc a b
    rw [hcomp]
    exact tsupport_dirichletMeshBump_subset hL_pos y₀
  let ψ : ℤ → ℝ → ℂ := fun j y ↦
    Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (y : ℂ)) * β y
  have hψ_smooth : ∀ j : ℤ, ContDiff ℝ ∞ (ψ j) := fun j ↦
    (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)).mul hβ_smooth
  have hψ_supp : ∀ j : ℤ, tsupport (ψ j) ⊆ Set.Icc a b := fun j ↦
    tsupport_mul_subset_right.trans hβ_supp
  let f : ℤ → 𝓢(ℝ, ℂ) := fun j ↦
    annularLogLift χ hR_pos hb_le (hψ_smooth j) (hψ_supp j)
  refine ⟨f, fun j ↦ annularLogLift_isFixedBox χ hR_pos hb_le (hψ_smooth j) (hψ_supp j),
    fun j ↦ dirichletDeplete_memLp hχ hN T _hTpos hR_pos hα hs
      (annularLogLift_isFixedBox χ hR_pos hb_le (hψ_smooth j) (hψ_supp j)),
    fun j m hmem ↦ ?_, ?_⟩
  · have hrow := dirichletNormalizedRow_apply_depleted hχ hN T hT hp hpN hpT hX hα hs
      (annularLogLift_isFixedBox χ hR_pos hb_le (hψ_smooth j) (hψ_supp j)) m
    rw [hrow, annularLogLift_logFourier]
    have hsub_freq : dirichletPrimeFreq χ p j - dirichletPrimeFreq χ p m =
        2 * Real.pi * ((j - m : ℤ) : ℝ) / L := by
      dsimp [dirichletPrimeFreq, L]
      push_cast
      ring
    have heq_int : (fun y : ℝ ↦ ψ j y * Complex.exp (-(dirichletPrimeFreq χ p m : ℂ) * Complex.I * (y : ℂ))) =
        fun y : ℝ ↦ (dirichletMeshBump L y₀ y : ℂ) *
          Complex.exp ((2 * Real.pi * ((j - m : ℤ) : ℝ) / L : ℂ) * Complex.I * (y : ℂ)) := by
      ext y
      dsimp [ψ, β]
      have hexp : Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (y : ℂ)) *
            Complex.exp (-(dirichletPrimeFreq χ p m : ℂ) * Complex.I * (y : ℂ)) =
          Complex.exp ((2 * Real.pi * ((j - m : ℤ) : ℝ) / L : ℂ) * Complex.I * (y : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        calc (dirichletPrimeFreq χ p j : ℂ) * Complex.I * (y : ℂ) +
              -(dirichletPrimeFreq χ p m : ℂ) * Complex.I * (y : ℂ)
            = ((dirichletPrimeFreq χ p j - dirichletPrimeFreq χ p m : ℝ) : ℂ) *
                Complex.I * (y : ℂ) := by push_cast; ring
          _ = ((2 * Real.pi * ((j - m : ℤ) : ℝ) / L : ℝ) : ℂ) * Complex.I * (y : ℂ) := by
              rw [hsub_freq]
          _ = (2 * Real.pi * ((j - m : ℤ) : ℝ) / L : ℂ) * Complex.I * (y : ℂ) := by
              push_cast; rfl
      calc Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (y : ℂ)) *
            (dirichletMeshBump L y₀ y : ℂ) *
            Complex.exp (-(dirichletPrimeFreq χ p m : ℂ) * Complex.I * (y : ℂ))
          = (dirichletMeshBump L y₀ y : ℂ) *
              (Complex.exp ((dirichletPrimeFreq χ p j : ℂ) * Complex.I * (y : ℂ)) *
                Complex.exp (-(dirichletPrimeFreq χ p m : ℂ) * Complex.I * (y : ℂ))) := by ring
        _ = (dirichletMeshBump L y₀ y : ℂ) *
              Complex.exp ((2 * Real.pi * ((j - m : ℤ) : ℝ) / L : ℂ) * Complex.I * (y : ℂ)) := by
            rw [hexp]
    rw [heq_int, dirichletMeshBump_fourier hL_pos y₀ (j - m)]
    by_cases hmj : m = j
    · subst hmj; simp
    · have hjmn : j - m ≠ 0 := sub_ne_zero.mpr (Ne.symm hmj)
      simp [hmj, hjmn]
  · obtain ⟨K, C0, hC0_pos, hbd⟩ :=
      annularLogLift_deplete_norm_poly_bound hχ hN T hT hX hα hs hR_pos hb_le le_rfl
        hβ_smooth hβ_supp
    let t0 : ℝ := Complex.arg (χ p) / L
    let S : ℝ := max 1 (1 + |t0| + 2 * Real.pi / L)
    have hS_pos : 1 ≤ S := le_max_left _ _
    refine ⟨K, C0 * S ^ K, mul_pos hC0_pos (pow_pos (by positivity) K), fun j hmem ↦ ?_⟩
    have hle := hbd (dirichletPrimeFreq χ p j)
    have h1t : 1 + |dirichletPrimeFreq χ p j| ≤ S * (1 + |(j : ℝ)|) := by
      have hfreq : |dirichletPrimeFreq χ p j| ≤ |t0| + (2 * Real.pi / L) * |(j : ℝ)| := by
        dsimp [dirichletPrimeFreq, t0, L]
        rw [add_div]
        refine (abs_add_le _ _).trans ?_
        rw [mul_div_right_comm, abs_mul, abs_of_pos (div_pos (mul_pos two_pos Real.pi_pos) hL_pos)]
      have hS1 : 1 + |t0| ≤ S := by
        calc 1 + |t0| ≤ 1 + |t0| + 2 * Real.pi / L := le_add_of_nonneg_right (by positivity)
          _ ≤ S := le_max_right _ _
      have hS2 : 2 * Real.pi / L ≤ S := by
        calc 2 * Real.pi / L ≤ 1 + |t0| + 2 * Real.pi / L := le_add_of_nonneg_left (by positivity)
          _ ≤ S := le_max_right _ _
      nlinarith [abs_nonneg (j : ℝ)]
    have hpow : (1 + |dirichletPrimeFreq χ p j|) ^ K ≤ S ^ K * (1 + |(j : ℝ)|) ^ K := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by positivity) h1t K
    exact hle.trans (mul_le_mul_of_nonneg_left hpow hC0_pos.le |>.trans_eq (by ring))

private theorem logFourierProfile_integrable (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    Integrable (fun y : ℝ ↦
      (𝓕 g) (Real.exp y) * Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))) volume := by
  obtain ⟨C0, hC0, hbd0⟩ := (𝓕 g).decay 0 0
  obtain ⟨C2, hC2, hbd2⟩ := (𝓕 g).decay 2 0
  have hC0' : ∀ u : ℝ, ‖(𝓕 g) u‖ ≤ C0 := fun u ↦ by
    simpa [norm_iteratedFDeriv_zero] using hbd0 u
  have hC2' : ∀ u : ℝ, ‖u‖ ^ 2 * ‖(𝓕 g) u‖ ≤ C2 := fun u ↦ by
    simpa [norm_iteratedFDeriv_zero] using hbd2 u
  let M : ℝ := max C0 C2
  have hM_nn : 0 ≤ M := le_trans hC0.le (le_max_left _ _)
  let dom : ℝ → ℝ := fun y ↦ M * Real.exp (-|y|)
  have hdom_int : Integrable dom volume := by
    have hsplit : dom = fun y : ℝ ↦
        Set.indicator (Set.Iic 0) (fun y : ℝ ↦ M * Real.exp y) y +
          Set.indicator (Set.Ioi 0) (fun y : ℝ ↦ M * Real.exp (-y)) y := by
      ext y
      dsimp [dom]
      rcases le_or_gt y 0 with hy | hy
      · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hy),
          Set.indicator_of_notMem (Set.mem_Ioi.not.mpr (not_lt_of_ge hy)),
          add_zero, abs_of_nonpos hy, neg_neg]
      · rw [Set.indicator_of_notMem (Set.mem_Iic.not.mpr (not_le_of_gt hy)),
          Set.indicator_of_mem (Set.mem_Ioi.mpr hy),
          zero_add, abs_of_pos hy]
    rw [hsplit]
    have hi1 : Integrable (Set.indicator (Set.Iic 0) (fun y : ℝ ↦ M * Real.exp y)) volume :=
      IntegrableOn.integrable_indicator ((integrableOn_exp_Iic 0).const_mul M) measurableSet_Iic
    have hi2 : Integrable (Set.indicator (Set.Ioi 0) (fun y : ℝ ↦ M * Real.exp (-y))) volume :=
      IntegrableOn.integrable_indicator ((integrableOn_exp_neg_Ioi 0).const_mul M) measurableSet_Ioi
    exact hi1.add hi2
  refine hdom_int.mono'
    ((((𝓕 g).continuous.comp Real.continuous_exp).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y ↦ ?_)
  rw [norm_mul, Complex.norm_exp]
  have hre : ((1 - (t : ℂ) * Complex.I) * (y : ℂ)).re = y := by
    simp [mul_re]
  rw [hre]
  dsimp only [dom]
  rcases le_or_gt y 0 with hy | hy
  · calc ‖(𝓕 g) (Real.exp y)‖ * Real.exp y
        ≤ C0 * Real.exp y := mul_le_mul_of_nonneg_right (hC0' _) (Real.exp_pos _).le
      _ ≤ M * Real.exp y := mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
      _ = M * Real.exp (-|y|) := by rw [abs_of_nonpos hy, neg_neg]
  · have hexp_pos : 0 < Real.exp y := Real.exp_pos y
    have h2 : ‖(𝓕 g) (Real.exp y)‖ * Real.exp y ≤ C2 * Real.exp (-y) := by
      have hb := hC2' (Real.exp y)
      rw [Real.norm_of_nonneg hexp_pos.le, sq] at hb
      calc ‖(𝓕 g) (Real.exp y)‖ * Real.exp y
          = (Real.exp y * Real.exp y * ‖(𝓕 g) (Real.exp y)‖) * Real.exp (-y) := by
            rw [Real.exp_neg]; field_simp [hexp_pos.ne']
        _ ≤ C2 * Real.exp (-y) := mul_le_mul_of_nonneg_right hb (Real.exp_pos _).le
    calc ‖(𝓕 g) (Real.exp y)‖ * Real.exp y
        ≤ C2 * Real.exp (-y) := h2
      _ ≤ M * Real.exp (-y) := mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
      _ = M * Real.exp (-|y|) := by rw [abs_of_pos hy]

/-- On the imaginary axis `z = i t`, `testDepleteStep χ p` multiplies `logFourierProfile` by the
Euler factor `1 - χ(p) p^{-i t}`.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem logFourierProfile_testDepleteStep {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (g : 𝓢(ℝ, ℂ)) (t : ℝ) :
    logFourierProfile (testDepleteStep χ p g) ((t : ℂ) * Complex.I) =
      (1 - χ (p : ZMod N) * (p : ℂ) ^ (-((t : ℂ) * Complex.I))) *
        logFourierProfile g ((t : ℂ) * Complex.I) := by
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp_ne : (p : ℝ) ≠ 0 := hp_pos.ne'
  have hpC_ne : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp_ne
  have hfg : (fun y : ℝ ↦ (𝓕 (testDepleteStep χ p g)) (Real.exp y) *
        Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))) =
      fun y : ℝ ↦
        (𝓕 g) (Real.exp y) * Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ)) -
        χ (p : ZMod N) * (((p : ℂ)⁻¹) * (𝓕 g) (Real.exp (y - Real.log p)) *
          Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))) := by
    ext y
    have hstep : testDepleteStep χ p g = g - χ (p : ZMod N) • schwartzScale (p : ℝ) hp_ne g := by
      simp [testDepleteStep, hp.ne_zero]
    have hfour_lin : 𝓕 (g - χ (p : ZMod N) • schwartzScale (p : ℝ) hp_ne g) =
        𝓕 g - χ (p : ZMod N) • 𝓕 (schwartzScale (p : ℝ) hp_ne g) := by
      ext w
      simp [SchwartzMap.fourier_coe]
    rw [hstep, hfour_lin, sub_apply, smul_apply, smul_eq_mul,
      fourier_schwartzScale (p : ℝ) hp_ne g (Real.exp y)]
    have hdiv : Real.exp y / (p : ℝ) = Real.exp (y - Real.log p) := by
      rw [Real.exp_sub, Real.exp_log hp_pos]
    rw [abs_of_pos hp_pos, hdiv, Complex.ofReal_inv, Complex.ofReal_natCast]
    ring
  rw [logFourierProfile, hfg]
  have hi1 := logFourierProfile_integrable g t
  have hi2 : Integrable (fun y : ℝ ↦
      (p : ℂ)⁻¹ * (𝓕 g) (Real.exp (y - Real.log p)) *
        Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))) volume := by
    have hrew : (fun y : ℝ ↦ (p : ℂ)⁻¹ * (𝓕 g) (Real.exp (y - Real.log p)) *
          Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))) =
        fun y : ℝ ↦ ((p : ℂ)⁻¹ * Complex.exp ((1 - (t : ℂ) * Complex.I) * (Real.log p : ℂ))) *
          ((𝓕 g) (Real.exp (y - Real.log p)) *
            Complex.exp ((1 - (t : ℂ) * Complex.I) * ((y - Real.log p : ℝ) : ℂ))) := by
      ext y
      have harg : (1 - (t : ℂ) * Complex.I) * (y : ℂ) =
          (1 - (t : ℂ) * Complex.I) * (Real.log p : ℂ) +
            (1 - (t : ℂ) * Complex.I) * ((y - Real.log p : ℝ) : ℂ) := by
        push_cast; ring
      rw [harg, Complex.exp_add]
      ring
    rw [hrew]
    exact (hi1.comp_sub_right (Real.log p)).const_mul _
  rw [integral_sub hi1 (hi2.const_mul _), integral_const_mul]
  have hshift : (∫ y : ℝ, (p : ℂ)⁻¹ * (𝓕 g) (Real.exp (y - Real.log p)) *
        Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))) =
      (p : ℂ) ^ (-((t : ℂ) * Complex.I)) * logFourierProfile g ((t : ℂ) * Complex.I) := by
    have hrew : (fun y : ℝ ↦ (p : ℂ)⁻¹ * (𝓕 g) (Real.exp (y - Real.log p)) *
          Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))) =
        fun y : ℝ ↦ ((p : ℂ) ^ (-((t : ℂ) * Complex.I))) *
          ((𝓕 g) (Real.exp (y - Real.log p)) *
            Complex.exp ((1 - (t : ℂ) * Complex.I) * ((y - Real.log p : ℝ) : ℂ))) := by
      ext y
      have harg : (1 - (t : ℂ) * Complex.I) * (y : ℂ) =
          (1 - (t : ℂ) * Complex.I) * (Real.log p : ℂ) +
            (1 - (t : ℂ) * Complex.I) * ((y - Real.log p : ℝ) : ℂ) := by
        push_cast; ring
      have hexp_p : (p : ℂ)⁻¹ * Complex.exp ((1 - (t : ℂ) * Complex.I) * (Real.log p : ℂ)) =
          (p : ℂ) ^ (-((t : ℂ) * Complex.I)) := by
        have hp_cpow : Complex.exp ((1 - (t : ℂ) * Complex.I) * (Real.log p : ℂ)) =
            (p : ℂ) ^ (1 - (t : ℂ) * Complex.I) := by
          rw [Complex.cpow_def_of_ne_zero hpC_ne, ← Complex.ofReal_natCast p,
            ← Complex.ofReal_log hp_pos.le]
          congr 1; ring
        rw [hp_cpow, ← Complex.cpow_neg_one (p : ℂ), ← Complex.cpow_add _ _ hpC_ne]
        congr 1; ring
      rw [harg, Complex.exp_add]
      calc (p : ℂ)⁻¹ * (𝓕 g) (Real.exp (y - Real.log p)) *
            (Complex.exp ((1 - (t : ℂ) * Complex.I) * ↑(Real.log p)) *
              Complex.exp ((1 - (t : ℂ) * Complex.I) * ↑(y - Real.log p)))
          = ((p : ℂ)⁻¹ * Complex.exp ((1 - (t : ℂ) * Complex.I) * ↑(Real.log p))) *
              ((𝓕 g) (Real.exp (y - Real.log p)) *
                Complex.exp ((1 - (t : ℂ) * Complex.I) * ↑(y - Real.log p))) := by ring
        _ = _ := by rw [hexp_p]
    have hsub_eq := integral_sub_right_eq_self (μ := volume) (fun y : ℝ ↦ (𝓕 g) (Real.exp y) *
        Complex.exp ((1 - (t : ℂ) * Complex.I) * (y : ℂ))) (Real.log p)
    rw [hrew, integral_const_mul, hsub_eq, logFourierProfile]
  rw [hshift]
  change logFourierProfile g ((t : ℂ) * Complex.I) -
      χ (p : ZMod N) * ((p : ℂ) ^ (-((t : ℂ) * Complex.I)) * logFourierProfile g ((t : ℂ) * Complex.I)) = _
  ring

/-- Exact fixed-box denominator division for a primitive nontrivial Dirichlet character `χ` at a
prime `p ∤ N`: a test `f` supported in `Set.Icc (-R) R` on the Fourier side is `testDepleteStep χ p g`
for some `g` on the shrunk box `Set.Icc (-(R / p)) (R / p)` if and only if `logFourierProfile f`
vanishes on the shifted prime frequency mesh `dirichletPrimeFreq χ p`.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletFixedBox_exact_division {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (_hχ : χ.IsPrimitive) (_hN : 1 < N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N)
    {R : ℝ} (hR : 0 < R) {f : 𝓢(ℝ, ℂ)} (hf : IsDirichletFixedBoxTest χ R f) :
    (∃ g : 𝓢(ℝ, ℂ), IsDirichletFixedBoxTest χ (R / p) g ∧ testDepleteStep χ p g = f) ↔
      ∀ j : ℤ, logFourierProfile f ((dirichletPrimeFreq χ p j : ℂ) * Complex.I) = 0 := by
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hp_gt_one : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp_ne : (p : ℝ) ≠ 0 := hp_pos.ne'
  have hpC_ne : (p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp_ne
  have hL_pos : 0 < Real.log p := Real.log_pos hp_gt_one
  let L : ℝ := Real.log p
  let c : ℂ := χ (p : ZMod N)
  have hc_norm : ‖c‖ = 1 := dirichlet_norm_apply_eq_one_of_coprime χ hpN
  have hc_ne : c ≠ 0 := norm_ne_zero_iff.mp (by rw [hc_norm]; exact one_ne_zero)
  let t0 : ℝ := Complex.arg c / L
  have hcexp_arg : Complex.exp ((Complex.arg c : ℂ) * Complex.I) = c := by
    have h := Complex.norm_mul_exp_arg_mul_I c
    rwa [hc_norm, Complex.ofReal_one, one_mul] at h
  constructor
  · rintro ⟨g, _, rfl⟩ j
    rw [logFourierProfile_testDepleteStep χ hp g (dirichletPrimeFreq χ p j)]
    have hzero : 1 - c * (p : ℂ) ^ (-((dirichletPrimeFreq χ p j : ℂ) * Complex.I)) = 0 := by
      have hmul1 := dirichlet_mul_cpow_primeFreq_eq_one χ hp hpN j
      have hmul1' : c * (p : ℂ) ^ (-((dirichletPrimeFreq χ p j : ℂ) * Complex.I)) = 1 := by
        simpa [c, neg_mul] using hmul1
      rw [hmul1', sub_self]
    change (1 - c * (p : ℂ) ^ (-((dirichletPrimeFreq χ p j : ℂ) * Complex.I))) * _ = 0
    rw [hzero, zero_mul]
  · intro hvan
    let F_hat : 𝓢(ℝ, ℂ) := 𝓕 f
    let F : ℝ → ℂ := F_hat
    have hF_smooth : ContDiff ℝ ∞ F := (𝓕 f).smooth ⊤
    have hF_supp : tsupport F ⊆ Set.Icc (-R) R := hf.2
    have hF_zero_gt : ∀ u : ℝ, R < u → F u = 0 := fun u hu ↦ by
      by_contra hne
      have hmem : u ∈ tsupport F := subset_tsupport F (Function.mem_support.mpr hne)
      have hIcc := hF_supp hmem
      linarith [hIcc.2]
    let h : ℝ → ℂ := fun y ↦ F (Real.exp y) * Complex.exp ((1 - (t0 : ℂ) * Complex.I) * (y : ℂ))
    have hh_cont : Continuous h :=
      (hF_smooth.continuous.comp Real.continuous_exp).mul
        (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
    obtain ⟨C0, hC0, hC0_bd⟩ := (𝓕 f).decay 0 0
    have hF_bd : ∀ u : ℝ, ‖F u‖ ≤ C0 := fun u ↦ by
      simpa [F, norm_iteratedFDeriv_zero] using hC0_bd u
    have hh_bd : ∀ y : ℝ, ‖h y‖ ≤ C0 * Real.exp y := fun y ↦ by
      dsimp [h]
      rw [norm_mul, Complex.norm_exp]
      have hre : ((1 - (t0 : ℂ) * Complex.I) * (y : ℂ)).re = y := by simp [mul_re]
      rw [hre]
      exact mul_le_mul_of_nonneg_right (hF_bd _) (Real.exp_pos _).le
    have hh_zero_gt : ∀ y : ℝ, Real.log R < y → h y = 0 := fun y hy ↦ by
      have hexp_gt : R < Real.exp y := by
        simpa [Real.exp_log hR] using Real.exp_lt_exp.mpr hy
      simp [h, hF_zero_gt (Real.exp y) hexp_gt]
    let hsC : C(ℝ, ℂ) := ⟨fun u : ℝ ↦ h (L * u), hh_cont.comp (continuous_const.mul continuous_id)⟩
    have hs_loc : ∀ K : TopologicalSpace.Compacts ℝ,
        Summable fun n : ℤ ↦ ‖(hsC.comp (ContinuousMap.addRight n)).restrict K‖ := by
      intro K
      obtain ⟨M₀, hM₀⟩ := K.isCompact.isBounded.subset_closedBall (0 : ℝ)
      let M : ℝ := max M₀ 0
      have hKM : ∀ u ∈ K, |u| ≤ M := fun u hu ↦
        (by simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hM₀ hu : |u| ≤ M₀).trans
          (le_max_left _ _)
      have hM_nn : 0 ≤ M := le_max_right _ _
      let N_pos : ℕ := Nat.ceil (max 0 ((Real.log R / L) + M)) + 1
      let q : ℝ := Real.exp (-L)
      have hq_pos : 0 < q := Real.exp_pos (-L)
      have hq_lt_one : q < 1 := Real.exp_lt_one_iff.mpr (by linarith [hL_pos])
      let C_tail : ℝ := C0 * Real.exp (L * M)
      have hC_tail_nn : 0 ≤ C_tail := by positivity
      have hsum_neg : Summable (fun m : ℕ ↦ C_tail * q ^ m) :=
        (summable_geometric_of_lt_one hq_pos.le hq_lt_one).mul_left C_tail
      have hsum_pos : Summable (fun n : ℕ ↦ if n ≤ N_pos then C_tail * q ^ (-(n : ℝ)) else 0) :=
        summable_of_ne_finset_zero (s := Finset.range (N_pos + 1)) fun n hn ↦ by
          have hnot : ¬ (n ≤ N_pos) := by
            simp only [Finset.mem_range, not_lt] at hn
            omega
          exact ite_eq_right_iff.mpr fun h ↦ (hnot h).elim
      let g_dom : ℤ → ℝ := fun n ↦
        if 0 ≤ n then (if n.toNat ≤ N_pos then C_tail * q ^ (-(n.toNat : ℝ)) else 0)
        else C_tail * q ^ ((-n).toNat)
      have hdom_sum : Summable g_dom := by
        rw [summable_int_iff_summable_nat_and_neg]
        constructor
        · refine hsum_pos.congr fun n ↦ ?_
          simp [g_dom]
        · rw [← summable_nat_add_iff 1]
          refine (hsum_neg.comp_injective Nat.succ_injective).congr fun m ↦ ?_
          have hneg : ¬ (0 : ℤ) ≤ -((m + 1 : ℕ) : ℤ) := by omega
          have hrew_m : g_dom (-((m + 1 : ℕ) : ℤ)) = C_tail * q ^ (m + 1) := by
            have htoNat : (- -((m + 1 : ℕ) : ℤ)).toNat = m + 1 := by omega
            have hite : g_dom (-((m + 1 : ℕ) : ℤ)) = C_tail * q ^ (- -((m + 1 : ℕ) : ℤ)).toNat := by
              dsimp only [g_dom]
              exact ite_eq_right_iff.mpr fun h ↦ (hneg h).elim
            rw [hite, htoNat]
          exact hrew_m.symm
      refine Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) hdom_sum
      rw [ContinuousMap.norm_le _]
      · intro u
        simp only [ContinuousMap.restrict_apply, ContinuousMap.comp_apply,
          ContinuousMap.coe_addRight, hsC, ContinuousMap.coe_mk]
        have hu_abs : |u.1| ≤ M := hKM u.1 u.2
        have hu_bounds : -M ≤ u.1 ∧ u.1 ≤ M := abs_le.mp hu_abs
        by_cases hn : 0 ≤ n
        · have hn_toNat : (n.toNat : ℝ) = n := by exact_mod_cast Int.toNat_of_nonneg hn
          by_cases hle : n.toNat ≤ N_pos
          · simp only [g_dom, hn, ↓reduceIte, hle]
            refine (hh_bd (L * (u.1 + n))).trans ?_
            have hle_arg : L * (u.1 + n) ≤ L * M + (-L) * (-(n.toNat : ℝ)) := by
              have h1 : L * (u.1 + n) = L * u.1 + L * (n.toNat : ℝ) := by rw [hn_toNat]; ring
              nlinarith [hL_pos]
            calc C0 * Real.exp (L * (u.1 + n))
                ≤ C0 * Real.exp (L * M + (-L) * (-(n.toNat : ℝ))) :=
                  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle_arg) hC0.le
              _ = C_tail * q ^ (-(n.toNat : ℝ)) := by
                  dsimp [C_tail, q]
                  rw [Real.exp_add, Real.rpow_def_of_pos (Real.exp_pos (-L)), Real.log_exp]
                  ring
          · simp only [g_dom, hn, ↓reduceIte, hle]
            have hN_lt : (N_pos : ℝ) < (n.toNat : ℝ) := by exact_mod_cast Nat.lt_of_not_le hle
            have hgt_R : Real.log R < L * (u.1 + n) := by
              have hceil : max 0 (Real.log R / L + M) ≤ (N_pos : ℝ) := by
                have hc := Nat.le_ceil (max 0 (Real.log R / L + M))
                have h1 : (Nat.ceil (max 0 (Real.log R / L + M)) : ℝ) ≤ (N_pos : ℝ) := by
                  dsimp [N_pos]; push_cast; linarith
                exact hc.trans h1
              have harg_gt : Real.log R / L < u.1 + (n : ℝ) := by
                have h2 : Real.log R / L + M < (n.toNat : ℝ) :=
                  lt_of_le_of_lt ((le_max_right 0 _).trans hceil) hN_lt
                calc Real.log R / L < (n.toNat : ℝ) - M := by linarith [h2]
                  _ = (n : ℝ) - M := by rw [hn_toNat]
                  _ ≤ u.1 + (n : ℝ) := by linarith [hu_bounds.1]
              calc Real.log R = L * (Real.log R / L) := (mul_div_cancel₀ _ hL_pos.ne').symm
                _ < L * (u.1 + (n : ℝ)) := mul_lt_mul_of_pos_left harg_gt hL_pos
            rw [hh_zero_gt _ hgt_R, norm_zero]
        · have hlt : n < 0 := Int.lt_of_not_ge hn
          simp only [g_dom, hn, ↓reduceIte]
          have hmn : ((-n).toNat : ℝ) = -n := by exact_mod_cast Int.toNat_of_nonneg (by omega)
          refine (hh_bd (L * (u.1 + n))).trans ?_
          have hle_arg : L * (u.1 + n) ≤ L * M + (-L) * ((-n).toNat : ℝ) := by
            have h1 : u.1 + n ≤ M - (-n : ℝ) := by linarith [hu_bounds.2]
            have h2 : (-L) * ((-n).toNat : ℝ) = L * (n : ℝ) := by rw [hmn]; ring
            nlinarith [hL_pos]
          calc C0 * Real.exp (L * (u.1 + n))
              ≤ C0 * Real.exp (L * M + (-L) * ((-n).toNat : ℝ)) :=
                mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hle_arg) hC0.le
            _ = C_tail * q ^ ((-n).toNat) := by
                dsimp [C_tail, q]
                rw [Real.exp_add, mul_comm (-L), Real.exp_nat_mul, ← mul_assoc]
      · by_cases hn : 0 ≤ n
        · simp only [g_dom, hn, ↓reduceIte]
          split_ifs <;> positivity
        · simp only [g_dom, hn, ↓reduceIte]
          positivity
    have hfc_zero : ∀ m : ℤ, 𝓕 (hsC : ℝ → ℂ) (m : ℝ) = 0 := by
      intro m
      change 𝓕 (fun u : ℝ ↦ h (L * u)) (m : ℝ) = 0
      rw [Real.fourier_real_eq_integral_exp_smul]
      have hrew : (fun u : ℝ ↦
            Complex.exp (↑(-2 * Real.pi * u * (m : ℝ)) * Complex.I) • h (L * u)) =
          fun u : ℝ ↦ (𝓕 f) (Real.exp (L * u)) *
            Complex.exp ((1 - (dirichletPrimeFreq χ p m : ℂ) * Complex.I) * ((L * u : ℝ) : ℂ)) := by
        ext u
        dsimp [h, F]
        have h_freq_real : dirichletPrimeFreq χ p m = t0 + 2 * Real.pi * (m : ℝ) / L := by
          have hc_eq : c = χ p := rfl
          dsimp [dirichletPrimeFreq, t0, L]
          rw [hc_eq, add_div]
        have harg : (1 - (dirichletPrimeFreq χ p m : ℂ) * Complex.I) * ((L * u : ℝ) : ℂ) =
            (↑(-2 * Real.pi * u * (m : ℝ)) * Complex.I) +
              ((1 - (t0 : ℂ) * Complex.I) * ((L * u : ℝ) : ℂ)) := by
          have hmul_real : (2 * Real.pi * (m : ℝ) / L) * (L * u) = 2 * Real.pi * u * (m : ℝ) := by
            dsimp [L]
            field_simp [hL_pos.ne']
          rw [h_freq_real]
          calc (1 - ((t0 + 2 * Real.pi * (m : ℝ) / L : ℝ) : ℂ) * Complex.I) * ((L * u : ℝ) : ℂ)
              = (1 - (t0 : ℂ) * Complex.I) * ((L * u : ℝ) : ℂ) -
                  (((2 * Real.pi * (m : ℝ) / L) * (L * u) : ℝ) : ℂ) * Complex.I := by
                  push_cast; ring
            _ = (↑(-2 * Real.pi * u * (m : ℝ)) * Complex.I) +
                  ((1 - (t0 : ℂ) * Complex.I) * ((L * u : ℝ) : ℂ)) := by
                  rw [hmul_real]
                  push_cast; ring
        rw [harg, Complex.exp_add]
        ring
      have hmul_eq := MeasureTheory.Measure.integral_comp_mul_left
        (fun y : ℝ ↦ (𝓕 f) (Real.exp y) *
          Complex.exp ((1 - (dirichletPrimeFreq χ p m : ℂ) * Complex.I) * (y : ℂ))) L
      rw [hrew, hmul_eq, abs_of_pos (inv_pos.mpr hL_pos), Complex.real_smul]
      change ((L⁻¹ : ℝ) : ℂ) * logFourierProfile f ((dirichletPrimeFreq χ p m : ℂ) * Complex.I) = 0
      rw [hvan m, mul_zero]
    have h_sum : Summable (fun m : ℤ ↦ 𝓕 (hsC : ℝ → ℂ) (m : ℝ)) := by
      simp_rw [hfc_zero]
      exact summable_zero
    have hP_zero : ∀ y : ℝ, ∑' k : ℤ, h (y + (k : ℝ) * L) = 0 := by
      intro y
      have hpt := Real.tsum_eq_tsum_fourier hs_loc h_sum (y / L)
      simp_rw [hfc_zero, zero_mul, tsum_zero] at hpt
      calc ∑' k : ℤ, h (y + (k : ℝ) * L)
          = ∑' k : ℤ, hsC (y / L + (k : ℝ)) := by
              refine tsum_congr fun k ↦ ?_
              dsimp only [hsC, ContinuousMap.coe_mk]
              have harg : y + (k : ℝ) * L = L * (y / L + (k : ℝ)) := by
                rw [mul_add, mul_div_cancel₀ _ hL_pos.ne', mul_comm (k : ℝ) L]
              rw [harg]
        _ = 0 := hpt
    let rℂ : ℂ := c * (p : ℂ)⁻¹
    have hrℂ_norm : ‖rℂ‖ = (p : ℝ)⁻¹ := by
      dsimp [rℂ]
      rw [norm_mul, hc_norm, one_mul, norm_inv, Complex.norm_natCast]
    have hp_inv_le : (p : ℝ)⁻¹ ≤ 1 / 2 := by
      have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
      simpa [one_div] using inv_anti₀ zero_lt_two h2p
    let G : ℝ → ℂ := fun u ↦ ∑' k : ℕ, rℂ ^ k * F (((p : ℝ)⁻¹ ^ k) * u)
    let C_bound : ℕ → ℝ := fun n ↦ Classical.choose (F_hat.decay 0 n)
    have hC_bound_pos : ∀ n : ℕ, 0 < C_bound n := fun n ↦ (Classical.choose_spec (F_hat.decay 0 n)).1
    have hC_bound_le : ∀ n : ℕ, ∀ u : ℝ, ‖iteratedFDeriv ℝ n F u‖ ≤ C_bound n := fun n u ↦ by
      have hb := (Classical.choose_spec (F_hat.decay 0 n)).2 u
      rw [pow_zero, one_mul] at hb
      exact hb
    have hG_smooth : ContDiff ℝ ∞ G := by
      refine (contDiff_tsum (v := fun n k ↦ C_bound n * (1 / 2 : ℝ) ^ k) ?_ ?_ ?_).of_le
        (by exact le_rfl)
      · intro k
        have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ ↦ ((p : ℝ)⁻¹ ^ k) * u) :=
          contDiff_const.mul contDiff_id
        exact contDiff_const.mul ((hF_smooth.of_le (le_rfl : ∞ ≤ ∞)).comp hlin)
      · intro n _
        exact (summable_geometric_two).mul_left (C_bound n)
      · intro n k u _
        let a : ℂ := rℂ ^ k
        let r : ℝ := (p : ℝ)⁻¹ ^ k
        let L_mul : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℂ ℂ a).restrictScalars ℝ
        let g_lin : ℝ →L[ℝ] ℝ := r • ContinuousLinearMap.id ℝ ℝ
        have hfun_eq : (fun w : ℝ ↦ rℂ ^ k * F (((p : ℝ)⁻¹ ^ k) * w)) = L_mul ∘ (F ∘ g_lin) := rfl
        rw [hfun_eq]
        have hL_norm : ‖L_mul‖ ≤ ‖a‖ := by
          refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) fun z ↦ ?_
          simp [L_mul]
        have hr_nn : 0 ≤ r := by positivity
        have hr_le_one : r ≤ 1 := pow_le_one₀ (by positivity) (by linarith [hp_inv_le])
        have hg_norm : ‖g_lin‖ ≤ 1 := by
          refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w ↦ ?_
          simp only [g_lin, FunLike.coe_smul, ContinuousLinearMap.coe_id',
            Pi.smul_apply, id_eq, smul_eq_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hr_nn,
            one_mul]
          exact mul_le_of_le_one_left (abs_nonneg w) hr_le_one
        have ha_le : ‖a‖ ≤ (1 / 2 : ℝ) ^ k := by
          dsimp [a]
          rw [norm_pow, hrℂ_norm]
          exact pow_le_pow_left₀ (by positivity) hp_inv_le k
        have hFg : ContDiffAt ℝ ∞ (F ∘ g_lin) u := (hF_smooth.comp g_lin.contDiff).contDiffAt
        have h1 : ‖iteratedFDeriv ℝ n (L_mul ∘ (F ∘ g_lin)) u‖ ≤
            ‖L_mul‖ * ‖iteratedFDeriv ℝ n (F ∘ g_lin) u‖ :=
          L_mul.norm_iteratedFDeriv_comp_left hFg (mod_cast le_top)
        have h2 : iteratedFDeriv ℝ n (F ∘ g_lin) u =
            (iteratedFDeriv ℝ n F (g_lin u)).compContinuousLinearMap (fun _ ↦ g_lin) :=
          g_lin.iteratedFDeriv_comp_right hF_smooth u (mod_cast le_top)
        have h3 : ‖iteratedFDeriv ℝ n (F ∘ g_lin) u‖ ≤ C_bound n := by
          rw [h2]
          refine ((iteratedFDeriv ℝ n F (g_lin u)).norm_compContinuousLinearMap_le _).trans ?_
          have hprod_one : (∏ _i : Fin n, ‖g_lin‖) ≤ 1 := by
            calc (∏ _i : Fin n, ‖g_lin‖) = ‖g_lin‖ ^ n := by simp
              _ ≤ 1 ^ n := pow_le_pow_left₀ (norm_nonneg _) hg_norm n
              _ = 1 := one_pow n
          calc ‖iteratedFDeriv ℝ n F (g_lin u)‖ * ∏ _i : Fin n, ‖g_lin‖
              ≤ C_bound n * 1 := mul_le_mul (hC_bound_le n _) hprod_one (by positivity) (hC_bound_pos n).le
            _ = C_bound n := mul_one _
        calc ‖iteratedFDeriv ℝ n (L_mul ∘ (F ∘ g_lin)) u‖
            ≤ ‖L_mul‖ * ‖iteratedFDeriv ℝ n (F ∘ g_lin) u‖ := h1
          _ ≤ (1 / 2 : ℝ) ^ k * C_bound n :=
              mul_le_mul (hL_norm.trans ha_le) h3 (norm_nonneg _) (by positivity)
          _ = C_bound n * (1 / 2 : ℝ) ^ k := mul_comm _ _
    have hG_summable : ∀ u : ℝ, Summable (fun k : ℕ ↦ rℂ ^ k * F (((p : ℝ)⁻¹ ^ k) * u)) := by
      intro u
      refine (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun k ↦ ?_)
        ((summable_geometric_two).mul_right C0)).of_norm
      rw [norm_mul, norm_pow, hrℂ_norm]
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hp_inv_le k) (hF_bd _) (norm_nonneg _)
        (by positivity)
    have hG_eq : ∀ u : ℝ, G u - c * (p : ℂ)⁻¹ * G ((p : ℝ)⁻¹ * u) = F u := by
      intro u
      have hsplit : G u = F u + ∑' k : ℕ, rℂ ^ (k + 1) * F (((p : ℝ)⁻¹ ^ (k + 1)) * u) := by
        dsimp [G]
        rw [(hG_summable u).tsum_eq_zero_add]
        simp
      have hshift : (∑' k : ℕ, rℂ ^ (k + 1) * F (((p : ℝ)⁻¹ ^ (k + 1)) * u)) =
          rℂ * G ((p : ℝ)⁻¹ * u) := by
        have hrew : (fun k : ℕ ↦ rℂ ^ (k + 1) * F (((p : ℝ)⁻¹ ^ (k + 1)) * u)) =
            fun k : ℕ ↦ rℂ * (rℂ ^ k * F (((p : ℝ)⁻¹ ^ k) * ((p : ℝ)⁻¹ * u))) := by
          ext k
          rw [pow_succ', pow_succ, mul_assoc ((p : ℝ)⁻¹ ^ k) (p : ℝ)⁻¹ u]
          ring
        rw [hrew, tsum_mul_left]
      rw [hsplit, hshift]
      dsimp [rℂ]
      ring
    have hG_par : ∀ u : ℝ, G (-u) = χ (-1) * G u := by
      intro u
      have hrew : (fun k : ℕ ↦ rℂ ^ k * F (((p : ℝ)⁻¹ ^ k) * (-u))) =
          fun k : ℕ ↦ χ (-1) * (rℂ ^ k * F (((p : ℝ)⁻¹ ^ k) * u)) := by
        ext k
        dsimp only [F]
        have hneg : ((p : ℝ)⁻¹ ^ k) * (-u) = -(((p : ℝ)⁻¹ ^ k) * u) := by ring
        rw [hneg, hf.1.fourier]
        ring
      dsimp [G]
      rw [hrew, tsum_mul_left]
    have hG_zero_gt : ∀ u : ℝ, R / p < u → G u = 0 := by
      intro u hu_gt
      have hR_div_pos : 0 < R / p := div_pos hR hp_pos
      have hu_pos : 0 < u := lt_trans hR_div_pos hu_gt
      let y : ℝ := Real.log u
      have hy_exp : Real.exp y = u := Real.exp_log hu_pos
      have hrℂ_exp : rℂ = Complex.exp (-(L : ℂ) + (Complex.arg c : ℂ) * Complex.I) := by
        dsimp [rℂ]
        rw [Complex.exp_add, Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hp_pos,
          Complex.ofReal_natCast, hcexp_arg, mul_comm]
      let G_all : ℤ → ℂ := fun k ↦
        Complex.exp ((k : ℤ) * (-(L : ℂ) + (Complex.arg c : ℂ) * Complex.I)) *
          F (Real.exp (y - (k : ℝ) * L))
      have hG_all_eq : ∀ k : ℤ,
          G_all k = Complex.exp (-((1 - (t0 : ℂ) * Complex.I) * (y : ℂ))) *
            h (y - (k : ℝ) * L) := by
        intro k
        dsimp [G_all, h]
        have harg : -((1 - (t0 : ℂ) * Complex.I) * (y : ℂ)) +
              (1 - (t0 : ℂ) * Complex.I) * ((y - (k : ℝ) * L : ℝ) : ℂ) =
            (k : ℤ) * (-(L : ℂ) + (Complex.arg c : ℂ) * Complex.I) := by
          have htL : (t0 : ℂ) * (L : ℂ) = (Complex.arg c : ℂ) := by
            have hL_ne : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
            dsimp [t0]
            rw [Complex.ofReal_div, div_mul_cancel₀ _ hL_ne]
          push_cast
          calc -((1 - (t0 : ℂ) * Complex.I) * (y : ℂ)) +
                (1 - (t0 : ℂ) * Complex.I) * ((y : ℂ) - (k : ℂ) * (L : ℂ))
              = (k : ℂ) * (-(L : ℂ) + ((t0 : ℂ) * (L : ℂ)) * Complex.I) := by ring
            _ = (k : ℂ) * (-(L : ℂ) + (Complex.arg c : ℂ) * Complex.I) := by rw [htL]
        calc Complex.exp ((k : ℤ) * (-(L : ℂ) + (Complex.arg c : ℂ) * Complex.I)) *
              F (Real.exp (y - (k : ℝ) * L))
            = Complex.exp (-((1 - (t0 : ℂ) * Complex.I) * (y : ℂ)) +
                (1 - (t0 : ℂ) * Complex.I) * ((y - (k : ℝ) * L : ℝ) : ℂ)) *
                F (Real.exp (y - (k : ℝ) * L)) := by rw [harg]
          _ = Complex.exp (-((1 - (t0 : ℂ) * Complex.I) * (y : ℂ))) *
                (F (Real.exp (y - (k : ℝ) * L)) *
                  Complex.exp ((1 - (t0 : ℂ) * Complex.I) * ((y - (k : ℝ) * L : ℝ) : ℂ))) := by
              rw [Complex.exp_add]; ring
      have hG_all_sum_zero : ∑' k : ℤ, G_all k = 0 := by
        have hrew : (fun k : ℤ ↦ G_all k) =
            fun k : ℤ ↦ Complex.exp (-((1 - (t0 : ℂ) * Complex.I) * (y : ℂ))) *
              h (y + ((-k : ℤ) : ℝ) * L) := by
          ext k
          rw [hG_all_eq k]
          congr 2
          push_cast
          ring
        have hneg_sum : (∑' k : ℤ, h (y + ((-k : ℤ) : ℝ) * L)) =
            ∑' m : ℤ, h (y + (m : ℝ) * L) :=
          Equiv.tsum_eq (Equiv.neg ℤ) (fun m : ℤ ↦ h (y + (m : ℝ) * L))
        rw [hrew, tsum_mul_left, hneg_sum, hP_zero y, mul_zero]
      have hG_all_nat : ∀ k : ℕ, G_all (k : ℤ) = rℂ ^ k * F (((p : ℝ)⁻¹ ^ k) * u) := by
        intro k
        dsimp [G_all]
        have hexp_k : Complex.exp (((k : ℕ) : ℤ) * (-(L : ℂ) + (Complex.arg c : ℂ) * Complex.I)) =
            rℂ ^ k := by
          rw [Int.cast_natCast, hrℂ_exp, ← Complex.exp_nat_mul]
        have hexp_arg : Real.exp (y - (((k : ℕ) : ℤ) : ℝ) * L) = ((p : ℝ)⁻¹ ^ k) * u := by
          rw [Int.cast_natCast, Real.exp_sub, Real.exp_nat_mul, Real.exp_log hp_pos, hy_exp,
            div_eq_mul_inv, inv_pow, mul_comm]
        rw [hexp_k, hexp_arg]
      have hG_all_neg : ∀ k : ℤ, k < 0 → G_all k = 0 := by
        intro k hk_lt
        let m : ℕ := (-k - 1).toNat
        have hkm : k = -((m + 1 : ℕ) : ℤ) := by omega
        have hkm_real : (k : ℝ) = -((m + 1 : ℕ) : ℝ) := by rw [hkm]; push_cast; rfl
        dsimp [G_all]
        have hexp_gt : R < Real.exp (y - (k : ℝ) * L) := by
          have hexp_eq : Real.exp (y - (k : ℝ) * L) = (p : ℝ) ^ (m + 1) * u := by
            have hrew_arg : y - (k : ℝ) * L = y + ((m + 1 : ℕ) : ℝ) * L := by
              rw [hkm_real]; ring
            rw [hrew_arg, Real.exp_add, Real.exp_nat_mul, Real.exp_log hp_pos, hy_exp, mul_comm]
          rw [hexp_eq]
          have hp_pow : (p : ℝ) ≤ (p : ℝ) ^ (m + 1) :=
            le_self_pow₀ hp_gt_one.le (Nat.succ_ne_zero m)
          calc R = (p : ℝ) * (R / p) := (mul_div_cancel₀ _ hp_ne).symm
            _ < (p : ℝ) * u := mul_lt_mul_of_pos_left hu_gt hp_pos
            _ ≤ (p : ℝ) ^ (m + 1) * u := mul_le_mul_of_nonneg_right hp_pow hu_pos.le
        rw [hF_zero_gt _ hexp_gt, mul_zero]
      have hsum_nat : ∑' k : ℤ, G_all k = ∑' k : ℕ, G_all (k : ℤ) := by
        symm
        refine Int.ofNat_injective.tsum_eq fun k hk ↦ ?_
        by_contra hnot
        have hk_lt : k < 0 := by
          by_contra h0
          rw [not_lt] at h0
          exact hnot ⟨k.toNat, by simpa [Int.ofNat_eq_natCast] using Int.toNat_of_nonneg h0⟩
        exact hk (hG_all_neg k hk_lt)
      rw [hsum_nat] at hG_all_sum_zero
      simpa [G, hG_all_nat] using hG_all_sum_zero
    have hG_supp : tsupport G ⊆ Set.Icc (-(R / p)) (R / p) := by
      refine closure_minimal (fun u hu ↦ ?_) isClosed_Icc
      by_contra hnot
      rw [Set.mem_Icc, not_and_or, not_le, not_le] at hnot
      rcases hnot with hlt | hgt
      · have hneg_gt : R / p < -u := by linarith
        have h1 : G (-u) = 0 := hG_zero_gt (-u) hneg_gt
        have h2 : G u = 0 := by
          calc G u = G (-(-u)) := by rw [neg_neg]
            _ = χ (-1) * G (-u) := hG_par (-u)
            _ = 0 := by rw [h1, mul_zero]
        exact hu h2
      · exact hu (hG_zero_gt u hgt)
    have hG_csupp : HasCompactSupport G :=
      HasCompactSupport.of_support_subset_isCompact isCompact_Icc (subset_tsupport G |>.trans hG_supp)
    let ψ : 𝓢(ℝ, ℂ) := hG_csupp.toSchwartzMap hG_smooth
    have hψ_coe : ∀ u : ℝ, ψ u = G u := fun _ ↦ rfl
    refine ⟨𝓕⁻ ψ, ⟨fun x ↦ ?_, ?_⟩, ?_⟩
    · have hψ_par : HasDirichletParity χ ψ := fun u ↦ by simpa [ψ] using hG_par u
      exact hψ_par.fourierInv x
    · have hfourier_eq : (fun x : ℝ ↦ (𝓕 (𝓕⁻ ψ)) x) = G := by
        ext x
        rw [FourierTransform.fourier_fourierInv_eq]
        rfl
      rwa [hfourier_eq]
    · have hstep_fourier : 𝓕 (testDepleteStep χ p (𝓕⁻ ψ)) = 𝓕 f := by
        ext u
        have hstep : testDepleteStep χ p (𝓕⁻ ψ) =
            𝓕⁻ ψ - c • schwartzScale (p : ℝ) hp_ne (𝓕⁻ ψ) := by
          simp [testDepleteStep, hp.ne_zero, c]
        have hfour_lin : 𝓕 (𝓕⁻ ψ - c • schwartzScale (p : ℝ) hp_ne (𝓕⁻ ψ)) =
            𝓕 (𝓕⁻ ψ) - c • 𝓕 (schwartzScale (p : ℝ) hp_ne (𝓕⁻ ψ)) := by
          ext w
          simp [SchwartzMap.fourier_coe]
        rw [hstep, hfour_lin, sub_apply, smul_apply, smul_eq_mul,
          fourier_schwartzScale (p : ℝ) hp_ne (𝓕⁻ ψ) u, abs_of_pos hp_pos,
          Complex.ofReal_inv, Complex.ofReal_natCast, FourierTransform.fourier_fourierInv_eq,
          hψ_coe, hψ_coe, div_eq_mul_inv, mul_comm u (p : ℝ)⁻¹, ← mul_assoc]
        exact hG_eq u
      calc testDepleteStep χ p (𝓕⁻ ψ)
          = 𝓕⁻ (𝓕 (testDepleteStep χ p (𝓕⁻ ψ))) := (FourierTransform.fourierInv_fourier_eq _).symm
        _ = 𝓕⁻ (𝓕 f) := by rw [hstep_fourier]
        _ = f := FourierTransform.fourierInv_fourier_eq f

/-- Stage-level exact denominator division for a primitive nontrivial Dirichlet character `χ` at
a prime `p ∉ T` with `p ∤ N`, expressed directly in terms of `dirichletNormalizedRow`.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
theorem dirichletFixedBox_stage_exact_division {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀) :
    let hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
    let hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN T hTpos
        (div_pos hX (Finset.prod_pos fun q hq ↦ by exact_mod_cast (hT q hq).1.pos)) hα hs hf₀
    (∃ g₀ : 𝓢(ℝ, ℂ), IsDirichletFixedBoxTest χ (X / ((p : ℝ) * ∏ q ∈ T, (q : ℝ))) g₀ ∧
        testDepleteStep χ p g₀ = f₀) ↔
      ∀ j : ℤ, dirichletNormalizedRow χ T p X α s hα hs j
        (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem) = 0 := by
  intro hTpos hmem
  have hR_pos : 0 < X / ∏ q ∈ T, (q : ℝ) :=
    div_pos hX (Finset.prod_pos fun q hq ↦ by exact_mod_cast (hT q hq).1.pos)
  have hdiv : (X / ∏ q ∈ T, (q : ℝ)) / p = X / ((p : ℝ) * ∏ q ∈ T, (q : ℝ)) := by
    rw [div_div, mul_comm (∏ q ∈ T, (q : ℝ)) (p : ℝ)]
  rw [← hdiv, dirichletFixedBox_exact_division hχ hN hp hpN hR_pos hf₀]
  refine forall_congr' fun j ↦ ?_
  rw [dirichletNormalizedRow_apply_depleted hχ hN T hT hp hpN hpT hX hα hs hf₀ j]

end CardinalLiftsAndDivision

end RiemannMasullo.Isolated
