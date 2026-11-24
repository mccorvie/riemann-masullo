module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.NumberTheory.ZetaValues

/-! # A first-derivative bound for integer theta series on a half-line

Poisson summation turns small lattice spacings into large Fourier frequencies. Counting
the positive integer dilates in the reciprocal half-line gives an $L^2$ estimate, which
Plancherel converts into a bound for the first derivative of the test.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap Topology

namespace RiemannMasullo

-- Change variables in each dilation before collecting its contribution at each frequency.
private theorem schwartz_int_lattice_energy_le_deriv_integral_sum_dilates (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n)
    (m : ℕ → ℝ) (G : ℝ → ℝ) (hG : Integrable G) (t : ℝ) :
    (∫ r in Ici t, ∑ n ∈ S, m n * G ((n : ℝ) * r)) =
      ∫ u, (∑ n ∈ S, if (n : ℝ) * t ≤ u then m n / n else 0) * G u := by
  classical
  let f (n : ℕ) : ℝ → ℝ := (Ici ((n : ℝ) * t)).indicator (fun u ↦ (m n / n) * G u)
  have hfi (n : ℕ) : Integrable (f n) := (hG.const_mul (m n / n)).indicator measurableSet_Ici
  have he (n : ℕ) (hn : n ∈ S) :
      (∫ r in Ici t, m n * G ((n : ℝ) * r)) = ∫ u, f n u := by
    have hp : 0 < (n : ℝ) := by exact_mod_cast hS n hn
    rw [integral_const_mul, integral_Ici_eq_integral_Ioi, integral_comp_mul_left_Ioi G t hp,
      smul_eq_mul]
    dsimp [f]
    rw [integral_indicator measurableSet_Ici, integral_const_mul, integral_Ici_eq_integral_Ioi]
    ring
  rw [integral_finsetSum S (fun n hn ↦
    ((hG.comp_mul_left' (by exact_mod_cast (hS n hn).ne')).const_mul (m n)).integrableOn)]
  calc
    _ = ∑ n ∈ S, ∫ u, f n u := Finset.sum_congr rfl he
    _ = ∫ u, ∑ n ∈ S, f n u := (integral_finsetSum S (fun n _ ↦ hfi n)).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with u
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hu : (n : ℝ) * t ≤ u <;> simp [f, hu, Ici]

private theorem schwartz_int_lattice_energy_le_deriv_sum_weights_le {A u : ℝ} (hA : 0 < A) (hu : A ≤ u) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, if (n : ℝ) * A ≤ u then (n : ℝ) else 0) ≤ (u / A) ^ 2 := by
  classical
  let K := ⌊u / A⌋₊
  let S := (Finset.Icc 1 N).filter fun n : ℕ ↦ (n : ℝ) * A ≤ u
  have hus : 0 ≤ u / A := by positivity [hA.trans_le hu]
  have hsub : S ⊆ Finset.Icc 1 K := by
    intro n hn
    obtain ⟨hn', hb⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hn').1, Nat.le_floor ((le_div_iff₀ hA).mpr hb)⟩
  have hcard : S.card ≤ K := by simpa using Finset.card_le_card hsub
  have hNat : (∑ n ∈ S, n) ≤ K * K := by
    calc _ ≤ ∑ _ ∈ S, K := Finset.sum_le_sum (fun n hn ↦ (Finset.mem_Icc.mp (hsub hn)).2)
         _ = _ := by simp
         _ ≤ _ := Nat.mul_le_mul_right K hcard
  rw [← Finset.sum_filter]
  have hK : (K : ℝ) ≤ u / A := Nat.floor_le hus
  calc _ ≤ (K : ℝ) * (K : ℝ) := by
         change (∑ n ∈ S, (n : ℝ)) ≤ _
         have hh := (Nat.cast_le (α := ℝ)).mpr hNat
         push_cast at hh
         exact hh
       _ ≤ _ := by nlinarith [sq_nonneg (u / A-(K : ℝ)), mul_nonneg (show 0 ≤ (K : ℝ) by positivity) (sub_nonneg.mpr hK)]

-- Cauchy–Schwarz with reciprocal-square weights, followed by counting the dilates below each frequency.
private theorem schwartz_int_lattice_energy_le_deriv_finite_dilates {A : ℝ} (hA : 0 < A) (N : ℕ) (H : ℝ → ℂ)
    (hcont : Continuous H) (hH : Integrable (fun x ↦ ‖H x‖ ^ 2))
    (hW : IntegrableOn (fun x ↦ (x / A) ^ 2 * ‖H x‖ ^ 2) (Ici A)) :
    IntegrableOn (fun y ↦ ‖∑ n ∈ Finset.Icc 1 N, H ((n : ℝ) * y)‖ ^ 2) (Ici A) ∧
    (∫ y in Ici A, ‖∑ n ∈ Finset.Icc 1 N, H ((n : ℝ) * y)‖ ^ 2) ≤ (∑ n ∈ Finset.Icc 1 N, ((n : ℝ)⁻¹) ^ 2) * (∫ u in Ici A, (u / A) ^ 2 * ‖H u‖ ^ 2) := by
  classical
  let S := Finset.Icc 1 N
  let C : ℝ := ∑ n ∈ S, ((n : ℝ)⁻¹) ^ 2
  let Q (y : ℝ) := ∑ n ∈ S, ((n : ℝ) ^ 2 * ‖H ((n : ℝ) * y)‖ ^ 2)
  have hnpos (n : ℕ) (hn : n ∈ S) : 0 < n := (Finset.mem_Icc.mp hn).1
  have hC : 0 ≤ C := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hiQ : Integrable Q := integrable_finsetSum S (fun n hn ↦
    (hH.comp_mul_left' (by exact_mod_cast (hnpos n hn).ne')).const_mul _)
  have hB (y : ℝ) : ‖∑ n ∈ S, H ((n : ℝ) * y)‖ ^ 2 ≤ C * Q y := by
    have h₁ := norm_sum_le S (fun n ↦ H ((n : ℝ) * y))
    have h₂ := Finset.sum_mul_sq_le_sq_mul_sq S (fun n : ℕ ↦ (n : ℝ)⁻¹)
      (fun n ↦ (n : ℝ) * ‖H ((n : ℝ) * y)‖)
    have he : ∑ n ∈ S, (n : ℝ)⁻¹ * ((n : ℝ) * ‖H ((n : ℝ) * y)‖) = ∑ n ∈ S, ‖H ((n : ℝ) * y)‖ :=
      Finset.sum_congr rfl fun n hn ↦ inv_mul_cancel_left₀ (by exact_mod_cast (hnpos n hn).ne') _
    rw [he] at h₂
    simpa only [C, Q, mul_pow] using (pow_le_pow_left₀ (norm_nonneg _) h₁ 2).trans h₂
  have hiL : IntegrableOn (fun y ↦ ‖∑ n ∈ S, H ((n : ℝ) * y)‖ ^ 2) (Ici A) := by
    apply ((hiQ.const_mul C).integrableOn).mono' (by fun_prop)
    filter_upwards with y
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hB y
  refine ⟨hiL, ?_⟩
  refine (setIntegral_mono_on hiL (hiQ.const_mul C).integrableOn measurableSet_Ici
    (fun y _ ↦ hB y)).trans ?_
  rw [integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ hC
  rw [show (∫ y in Ici A, Q y) = ∫ u, (∑ n ∈ S, if (n : ℝ) * A ≤ u then (n : ℝ) else 0) * ‖H u‖ ^ 2 from ?_]
  · rw [← integral_indicator measurableSet_Ici]
    apply integral_mono ?_ (hW.integrable_indicator measurableSet_Ici)
    · intro u
      by_cases hu : A ≤ u
      · simpa [Set.indicator_of_mem, hu] using
          mul_le_mul_of_nonneg_right (schwartz_int_lattice_energy_le_deriv_sum_weights_le hA hu N) (sq_nonneg ‖H u‖)
      · have hnone (n : ℕ) (hn : n ∈ S) : ¬ (n : ℝ) * A ≤ u := by
          have h := hnpos n hn
          have hh : (1 : ℝ) ≤ n := by exact_mod_cast h
          nlinarith [mul_nonneg (sub_nonneg.mpr hh) hA.le]
        have he : (∑ n ∈ S, if (n : ℝ) * A ≤ u then (n : ℝ) else 0) = 0 := Finset.sum_eq_zero (fun n hn ↦ by simp [hnone n hn])
        simp [he, Set.indicator_of_notMem (show u ∉ Ici A from hu)]
    · simp_rw [Finset.sum_mul]
      apply integrable_finsetSum
      intro n hn
      have he (x : ℝ) : (if (n : ℝ) * A ≤ x then (n : ℝ) else 0) * ‖H x‖ ^ 2 = (Ici ((n : ℝ) * A)).indicator (fun y ↦ (n : ℝ) * ‖H y‖ ^ 2) x := by
        by_cases hh : (n : ℝ) * A ≤ x <;> simp [hh, Ici, indicator]
      simp_rw [he]; exact (hH.const_mul _).indicator measurableSet_Ici
  · have h := schwartz_int_lattice_energy_le_deriv_integral_sum_dilates S hnpos (fun n ↦ (n : ℝ) ^ 2) (fun u ↦ ‖H u‖ ^ 2) hH A
    convert h using 2
    funext u
    apply congrArg (fun v : ℝ ↦ v * ‖H u‖ ^ 2)
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> simp_all [sq, (show (n : ℝ)≠0 by exact_mod_cast (hnpos n hn).ne')]

private theorem schwartz_int_lattice_energy_le_deriv_limit_dilates {A : ℝ} (hA : 0 < A) (H U : ℝ → ℂ)
    (hcont : Continuous H) (hH : Integrable (fun x ↦ ‖H x‖ ^ 2))
    (hW : IntegrableOn (fun x ↦ (x / A) ^ 2 * ‖H x‖ ^ 2) (Ici A))
    (hU : ∀ y ∈ Ici A, Tendsto (fun (N : ℕ) ↦ ∑ n ∈ Finset.Icc 1 N, H ((n : ℝ) * y)) atTop (𝓝 (U y))) :
    IntegrableOn (fun y ↦ ‖U y‖ ^ 2) (Ici A) ∧
    (∫ y in Ici A, ‖U y‖ ^ 2) ≤ (∑' n : ℕ, ((n : ℝ)⁻¹) ^ 2) * ∫ u in Ici A, (u / A) ^ 2 * ‖H u‖ ^ 2 := by
  let μ := volume.restrict (Ici A)
  let L (N : ℕ) (y : ℝ) := ‖∑ n ∈ Finset.Icc 1 N, H ((n : ℝ) * y)‖ ^ 2
  let B := (∑' n : ℕ, ((n : ℝ)⁻¹) ^ 2) * ∫ u in Ici A, (u / A) ^ 2 * ‖H u‖ ^ 2
  have hζ : Summable (fun n : ℕ ↦ ((n : ℝ)⁻¹) ^ 2) := by
    simpa only [inv_pow] using (Real.summable_nat_pow_inv (p := 2)).mpr (by norm_num)
  have hB : 0 ≤ B := mul_nonneg (tsum_nonneg fun _ ↦ sq_nonneg _) (integral_nonneg fun u ↦ by positivity)
  have hsum (N : ℕ) : Integrable (L N) μ ∧ ∫ y, L N y ∂μ ≤ B := by
    obtain ⟨hi, hu⟩ := schwartz_int_lattice_energy_le_deriv_finite_dilates hA N H hcont hH hW
    exact ⟨hi, hu.trans (mul_le_mul_of_nonneg_right (hζ.sum_le_tsum _ (fun _ _ ↦ sq_nonneg _))
      (integral_nonneg fun u ↦ by positivity))⟩
  have hlim : ∀ᵐ y ∂μ, Tendsto (fun n ↦ L n y) atTop (𝓝 (‖U y‖ ^ 2)) := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ici] with y hy
    exact (hU y hy).norm.pow 2
  have en (N : ℕ) : ∫⁻ y, ‖L N y‖ₑ ∂μ ≤ ENNReal.ofReal B := by
    have hnon (y : ℝ) : 0 ≤ L N y := sq_nonneg _
    rw [lintegral_eNorm_of_nonneg hnon, ← ofReal_integral_eq_lintegral_ofReal (hsum N).1 (.of_forall hnon)]
    exact ENNReal.ofReal_le_ofReal (hsum N).2
  have hliminf := Filter.liminf_le_of_frequently_le' (f := atTop) (Filter.Frequently.of_forall en)
  have hi := integrable_of_tendsto hlim (fun n ↦ (hsum n).1.aestronglyMeasurable)
    (lt_of_le_of_lt hliminf ENNReal.ofReal_lt_top).ne
  refine ⟨hi, ?_⟩
  have he := (lintegral_eNorm_le_liminf_of_tendsto hlim
    (fun n ↦ (hsum n).1.aestronglyMeasurable.aemeasurable.eNorm)).trans hliminf
  rw [lintegral_eNorm_of_nonneg (fun _ ↦ sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun _ ↦ sq_nonneg _)] at he
  exact (ENNReal.ofReal_le_ofReal_iff hB).mp he

-- Scaled Poisson summation, following Penner’s LogLatticePoisson at revision 63ea7fc.
private theorem schwartz_int_lattice_energy_le_deriv_poisson (f : 𝓢(ℝ, ℂ)) {L : ℝ} (hL : 0 < L) :
    HasSum (fun k : ℤ ↦ 𝓕 f ((k : ℝ) / L)) ((L : ℂ) * ∑' m : ℤ, f ((m : ℝ) * L)) := by
  let e : ℝ ≃L[ℝ] ℝ := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL.ne')
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have hg (x : ℝ) : g x = f (x * L) := rfl
  have hFourier (u : ℝ) : 𝓕 g u = L⁻¹ • 𝓕 f (u / L) := by
    simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq]
    have hphase (x : ℝ) : x * L * (u / L) = x * u := by field_simp
    simpa only [hg, hphase, abs_of_pos (inv_pos.mpr hL)] using
      Measure.integral_comp_mul_right (fun x : ℝ ↦ 𝐞 (-(x * (u / L))) • f x) L
  have hs : Summable (fun k : ℤ ↦ 𝓕 g (k : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      (((𝓕 g).isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  have hunit := g.tsum_eq_tsum_fourier 0
  simp at hunit
  have h := (hunit.symm ▸ hs.hasSum).const_smul L
  simpa only [hFourier, Complex.real_smul, smul_eq_mul, Complex.ofReal_inv,
    mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr hL.ne'), hg] using h

private theorem schwartz_int_lattice_energy_le_deriv_plancherel_deriv {A : ℝ} (hA : 0 < A) (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ ↦ (x / A) ^ 2 * ‖𝓕 f x‖ ^ 2) ∧
    (∫ x : ℝ, (x / A) ^ 2 * ‖𝓕 f x‖ ^ 2) = (2 * Real.pi * A)⁻¹ ^ 2 * ∫ x, ‖deriv f x‖ ^ 2 := by
  let D := SchwartzMap.derivCLM ℂ ℂ f
  have hd : ⇑D = deriv f := funext (SchwartzMap.derivCLM_apply ℂ f)
  have hform := Real.fourier_deriv f.integrable f.differentiable (hd ▸ D.integrable)
  have he (x : ℝ) : (x / A) ^ 2 * ‖𝓕 f x‖ ^ 2 = (2 * Real.pi * A)⁻¹ ^ 2 * ‖𝓕 D x‖ ^ 2 := by
    simp only [SchwartzMap.fourier_coe, hd, hform]
    simp only [norm_smul, Complex.norm_mul, Complex.norm_two, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_pow, sq_abs]
    field_simp [Real.pi_ne_zero, hA.ne']
  have hi : Integrable (fun x : ℝ ↦ ‖𝓕 D x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (𝓕 D).continuous.aestronglyMeasurable).mp ((𝓕 D).memLp 2)
  simp_rw [he]
  exact ⟨hi.const_mul _, by rw [integral_const_mul, SchwartzMap.integral_norm_sq_fourier, hd]⟩

-- Absolute convergence of the Fourier samples identifies the limit in the dilation estimate.
private theorem schwartz_int_lattice_energy_le_deriv_fourier_samples (f : 𝓢(ℝ, ℂ)) {A : ℝ} (hA : 0 < A) :
    let U (y : ℝ) := ∑' n : ℕ, 𝓕 f (((n : ℝ) + 1) * y)
    IntegrableOn (fun y ↦ ‖U y‖ ^ 2) (Ici A) ∧
    (∫ y in Ici A, ‖U y‖ ^ 2) ≤ (∑' n : ℕ, ((n : ℝ)⁻¹) ^ 2) * (∫ u in Ici A, (u / A) ^ 2 * ‖𝓕 f u‖ ^ 2) := by
  intro U
  have hi : Integrable (fun u : ℝ ↦ ‖𝓕 f u‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (𝓕 f).continuous.aestronglyMeasurable).mp ((𝓕 f).memLp 2)
  obtain ⟨hw, hm⟩ := schwartz_int_lattice_energy_le_deriv_plancherel_deriv hA f
  have hlim (y : ℝ) (hy : y∈ Ici A) :
      Tendsto (fun (N : ℕ) ↦ ∑ n ∈ Finset.Icc 1 N, 𝓕 f ((n : ℝ) * y)) atTop (𝓝 (U y)) := by
    have hpos := hA.trans_le (mem_Ici.mp hy)
    have hz := (schwartz_int_lattice_energy_le_deriv_poisson f (inv_pos.mpr hpos)).summable
    have hinj : Function.Injective (fun n : ℕ ↦ (n : ℤ) + 1) := by
      intro i j h
      change (i : ℤ) + 1 = (j : ℤ) + 1 at h
      exact_mod_cast add_right_cancel h
    have hNat : Summable (fun n : ℕ ↦ 𝓕 f (((n : ℝ) + 1) * y)) := by
      simpa [Function.comp_def, div_inv_eq_mul] using hz.comp_injective hinj
    have eqn (N : ℕ) : ∑ n ∈ Finset.Icc 1 N, 𝓕 f ((n : ℝ) * y) =
        ∑ n ∈ Finset.range N, 𝓕 f (((n : ℝ) + 1) * y) := by
      induction N with
      | zero => simp
      | succ k ih =>
        rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih, Nat.cast_succ]
    simpa only [eqn] using hNat.hasSum.tendsto_sum_nat
  exact schwartz_int_lattice_energy_le_deriv_limit_dilates hA (⇑(𝓕 f : 𝓢(ℝ, ℂ))) U (𝓕 f).continuous hi hw.integrableOn hlim

private theorem schwartz_int_lattice_energy_le_deriv_inversion (g : ℝ → ℝ) {a : ℝ} (ha : 0 < a)
    (hi : IntegrableOn g (Ici a⁻¹)) :
    IntegrableOn (fun r ↦ (r⁻¹) ^ 2 * g r⁻¹) (Ioc 0 a) ∧
    (∫ r in Ioc 0 a, (r⁻¹) ^ 2 * g r⁻¹) = ∫ y in Ici a⁻¹, g y := by
  have himage : (fun r : ℝ ↦ r⁻¹) '' Ioc 0 a = Ici a⁻¹ := by
    ext y
    constructor
    · rintro ⟨r, hr, rfl⟩
      exact inv_anti₀ hr.1 hr.2
    · intro hy
      have hp := (inv_pos.mpr ha).trans_le (mem_Ici.mp hy)
      refine ⟨y⁻¹, ⟨inv_pos.mpr hp, ?_⟩, inv_inv _⟩
      simpa using inv_anti₀ (inv_pos.mpr ha) (mem_Ici.mp hy)
  have hd (r : ℝ) (hr : r ∈ Ioc 0 a) :
      HasDerivWithinAt (fun x : ℝ ↦ x⁻¹) (-(r ^ 2)⁻¹) (Ioc 0 a) r :=
    (hasDerivAt_inv hr.1.ne').hasDerivWithinAt
  have h₁ := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioc hd inv_injective.injOn g
  have h₂ := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioc hd inv_injective.injOn g
  rw [himage] at h₁ h₂
  have he (r : ℝ) : |-(r ^ 2)⁻¹| • g r⁻¹ = (r⁻¹) ^ 2 * g r⁻¹ := by simp [abs_of_nonneg (sq_nonneg r), smul_eq_mul]
  simp only [he] at h₁ h₂
  exact ⟨h₁.mp hi, h₂.symm⟩

/-- For an even complex Schwartz test of mean zero, the squared norm of its integer
theta series is integrable on $(0, a]$, with integral at most $a ^ 2 / 12$ times the squared
$L ^ 2$ norm of its first derivative. The log-coordinate half-density $√r$ converts
the multiplicative measure $dr / r$ to the additive measure $dr$ in this estimate. -/
theorem schwartz_int_lattice_energy_le_deriv (f : 𝓢(ℝ, ℂ)) (he : Function.Even (⇑f))
    (hmean : 𝓕 f 0 = 0) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun r ↦ ‖∑' n : ℤ, f ((n : ℝ) * r)‖ ^ 2) (Ioc 0 a) ∧
    (∫ r in Ioc 0 a, ‖∑' n : ℤ, f ((n : ℝ) * r)‖ ^ 2) ≤ a ^ 2 / 12 * ∫ x, ‖deriv f x‖ ^ 2 := by
  let A := a⁻¹
  let U (y : ℝ) := ∑' n : ℕ, 𝓕 f (((n : ℝ) + 1) * y)
  let w (y : ℝ) := (y / A) ^ 2 * ‖𝓕 f y‖ ^ 2
  have hA : 0 < A := inv_pos.mpr ha
  have hfEven : Function.Even (⇑(𝓕 f : 𝓢(ℝ, ℂ))) := by
    intro x
    have h := Real.fourier_comp_linearIsometry (LinearIsometryEquiv.neg ℝ (E := ℝ)) (⇑f) x
    have hc : ⇑f ∘ (LinearIsometryEquiv.neg ℝ (E := ℝ)) = (⇑f) := funext he
    rw [hc] at h
    change 𝓕 (⇑f) (-x) = 𝓕 (⇑f) x
    exact h.symm
  have hwe : Function.Even w := by
    intro x; dsimp [w]; rw [hfEven x, neg_div, neg_sq]
  have hpos (y : ℝ) (hy : 0 < y) :
      ∑' n : ℤ, 𝓕 f ((n : ℝ) * y) = 2 * U y := by
    have hsum := (schwartz_int_lattice_energy_le_deriv_poisson f (inv_pos.mpr hy)).summable
    simp only [div_inv_eq_mul] at hsum
    have hev : Function.Even (fun n : ℤ ↦ 𝓕 f ((n : ℝ) * y)) := fun n ↦ by
      simpa only [Int.cast_neg, neg_mul] using hfEven ((n : ℝ) * y)
    rw [tsum_int_eq_zero_add_two_mul_tsum_pnat hev hsum]
    simp only [Int.cast_zero, zero_mul, hmean, zero_add, Int.cast_natCast, nsmul_eq_mul]
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ 𝓕 f ((n : ℝ) * y))]
    simp [U]
  have hraw (r : ℝ) (hr : 0 < r) :
      ‖∑' n : ℤ, f ((n : ℝ) * r)‖ ^ 2 = (r⁻¹) ^ 2 * (4 * ‖U r⁻¹‖ ^ 2) := by
    have h := (schwartz_int_lattice_energy_le_deriv_poisson f hr).tsum_eq
    simp only [div_eq_mul_inv] at h
    rw [hpos _ (inv_pos.mpr hr)] at h
    have hn := congrArg norm h
    simp only [norm_mul, Complex.norm_two, Complex.norm_real, Real.norm_of_nonneg hr.le] at hn
    calc _ = (r⁻¹ * (2 * ‖U r⁻¹‖)) ^ 2 := by rw [hn, inv_mul_cancel_left₀ hr.ne']
         _ = _ := by ring
  obtain ⟨hi, hu⟩ := schwartz_int_lattice_energy_le_deriv_fourier_samples f hA
  obtain ⟨hInv, hInvEq⟩ := schwartz_int_lattice_energy_le_deriv_inversion (fun y ↦ 4 * ‖U y‖ ^ 2) ha (hi.const_mul 4)
  have hInt : IntegrableOn (fun r ↦ ‖∑' n : ℤ, f ((n : ℝ) * r)‖ ^ 2) (Ioc 0 a) :=
    hInv.congr_fun (fun r hr ↦ (hraw r hr.1).symm) measurableSet_Ioc
  refine ⟨hInt, ?_⟩
  have hphy : (∫ r in Ioc 0 a, ‖∑' n : ℤ, f ((n : ℝ) * r)‖ ^ 2) = 4*∫ y in Ici A, ‖U y‖ ^ 2 := by
    calc _ = ∫ r in Ioc 0 a, (r⁻¹) ^ 2 * (4 * ‖U r⁻¹‖ ^ 2) :=
           setIntegral_congr_fun measurableSet_Ioc (fun r hr ↦ hraw r hr.1)
         _ = ∫ y in Ici A, 4 * ‖U y‖ ^ 2 := hInvEq
         _ = _ := integral_const_mul ..
  have hfull := integral_comp_abs (f := w)
  have hab (x : ℝ) : w |x| = w x := by
    rcases le_total 0 x with hx|hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, hwe]
  simp only [hab] at hfull
  obtain ⟨hw, hD⟩ := schwartz_int_lattice_energy_le_deriv_plancherel_deriv hA f
  have hhalf : (∫ y in Ici A, w y) ≤ (∫ y, w y) / 2 := by
    have hsub : Ici A ⊆ Ioi 0 := fun _ hy ↦ hA.trans_le hy
    have h := setIntegral_mono_set (f := w) hw.integrableOn
      (Filter.Eventually.of_forall fun y ↦ by dsimp [w]; positivity) (Filter.Eventually.of_forall (fun y (hy : y ∈ Ici A) ↦ hsub hy))
    linarith
  change (∫ y in Ici A, ‖U y‖ ^ 2) ≤ _ * (∫ y in Ici A, w y) at hu
  have hz : (∑' n : ℕ, ((n : ℝ)⁻¹) ^ 2) = Real.pi ^ 2 / 6 := by
    simpa only [one_div, inv_pow] using hasSum_zeta_two.tsum_eq
  rw [hz] at hu
  rw [hphy]
  have hh := mul_le_mul_of_nonneg_left (hu.trans (mul_le_mul_of_nonneg_left hhalf (by positivity))) (by norm_num : (0 : ℝ) ≤ 4)
  refine hh.trans_eq ?_
  change _ * (_ * ((∫ y, (y / A) ^ 2 * ‖𝓕 f y‖ ^ 2) / 2)) = _
  rw [hD]; dsimp [A]; field_simp [Real.pi_ne_zero, ha.ne']; ring

end RiemannMasullo
