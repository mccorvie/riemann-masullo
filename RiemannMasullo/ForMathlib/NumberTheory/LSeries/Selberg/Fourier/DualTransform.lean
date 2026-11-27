module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.KernelSymmetry
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.KernelBound
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.KernelRealTransform
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.ShiftTransform
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.ArchimedeanNormalization
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

public section

open MeasureTheory Set
open scoped ComplexConjugate

namespace RiemannMasullo.Selberg

private lemma angle_mem_strip {N : ℕ} (hN : 2 ≤ N) : |angle N| < Real.pi / 4 := by
  have hH : 1 ≤ (H N : ℝ) := by
    exact_mod_cast (one_le_pow₀ (show 1 ≤ N by omega) : 1 ≤ N ^ 100)
  have hpos : 0 < 2 * (H N : ℝ) := by linarith
  have hsmall : 1 / (2 * (H N : ℝ)) ≤ 1 / 2 := (div_le_iff₀ hpos).2 (by linarith)
  rw [angle, abs_lt]
  constructor <;> linarith [Real.two_le_pi, one_div_pos.mpr hpos]

private lemma integrable_shifted_kernel {a : ℝ} (ha : |a| < Real.pi / 4) :
    Integrable (fun y : ℝ ↦ K ((y : ℂ) + Complex.I * a)) := by
  have hstrip (y : ℝ) : |((y : ℂ) + Complex.I * a).im| < Real.pi / 4 := by
    simpa using ha
  have hc : Continuous (fun y : ℝ ↦ K ((y : ℂ) + Complex.I * a)) := by
    apply continuous_iff_continuousAt.mpr
    intro y
    exact (kernel_symmetry (hstrip y)).2.2.continuousAt.comp (f := fun x : ℝ ↦
      (x : ℂ) + Complex.I * a) (by fun_prop)
  have hdecay : Integrable (fun y : ℝ ↦ Real.exp (-|y| / 2)) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
    constructor
    · apply (integrableOn_congr_fun _ measurableSet_Iic).mpr
        (integrableOn_exp_mul_Iic (a := 1 / 2) (by norm_num) 0)
      intro y hy
      simp only [abs_of_nonpos (mem_Iic.mp hy)]
      ring_nf
    · apply (integrableOn_congr_fun _ measurableSet_Ioi).mpr
        (integrableOn_exp_mul_Ioi (a := -1 / 2) (by norm_num) 0)
      intro y hy
      simp only [abs_of_pos (mem_Ioi.mp hy)]
      ring_nf
  obtain ⟨C, _, hC⟩ := kernel_bound
  apply (hdecay.const_mul (C * (1 + (Real.sqrt (Real.cos (2*a)))⁻¹))).mono'
    hc.aestronglyMeasurable
  exact ae_of_all _ fun y ↦ by simpa using hC _ (hstrip y)

private lemma osc_add (x y : ℝ) : osc (x + y) = osc x * osc y := by
  simp [osc, mul_add, Complex.exp_add]

/-- Translation with the positive-sign Fourier convention, summed with finite weights. -/
private lemma ft_sum_translates {ι : Type*} (s : Finset ι) (c : ι → ℂ) (d : ι → ℝ)
    (f : ℝ → ℂ) (hf : Integrable f) (t : ℝ) :
    ft (fun y ↦ ∑ i ∈ s, c i * f (y + d i)) t =
      (∑ i ∈ s, c i * osc (-t * d i)) * ft f t := by
  let g (x : ℝ) := f x * osc (t * x)
  have hg : Integrable g := by
    apply hf.mul_bdd (c := 1)
    · apply Continuous.aestronglyMeasurable
      unfold osc
      fun_prop
    · exact ae_of_all _ fun x ↦ (Complex.norm_exp_I_mul_ofReal _).le
  have hterm (y : ℝ) (i : ι) :
      c i * f (y + d i) * osc (t * y) = (c i * osc (-t * d i)) * g (y + d i) := by
    rw [show t * y = -t * d i + t * (y + d i) by ring, osc_add]
    dsimp [g]
    ring
  unfold ft
  simp_rw [Finset.sum_mul, hterm]
  rw [integral_finsetSum s]
  · simp only [integral_const_mul, integral_add_right_eq_self g]
    rfl
  · intro i _
    exact ((measurePreserving_add_right volume (d i)).integrable_comp_of_integrable hg).const_mul _

private lemma mollifier_phase_sum (N : ℕ) (b : ℕ → ℝ) (t : ℝ) :
    (∑ k ∈ D N, ∑ l ∈ D N, ((b k * b l / Real.sqrt ((k : ℝ) * l) : ℝ) : ℂ) *
      osc (-t * Real.log ((k : ℝ) / l))) =
    ((‖∑ n ∈ D N, ((b n / Real.sqrt n : ℝ) : ℂ) * osc (-t * Real.log n)‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj, map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  have hpos (n : ℕ) (hn : n ∈ D N) : 0 < (n : ℝ) := by
    exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hphase : osc (-t * Real.log ((k : ℝ) / l)) =
      osc (-t * Real.log k) * conj (osc (-t * Real.log l)) := by
    have hconj (x : ℝ) : osc (-x) = conj (osc x) := by
      simp [osc, ← Complex.exp_conj]
    rw [Real.log_div (hpos k hk).ne' (hpos l hl).ne', mul_sub, sub_eq_add_neg, osc_add]
    rw [hconj]
  rw [hphase, map_mul, Complex.conj_ofReal, Real.sqrt_mul (hpos k hk).le,
    show b k * b l / (Real.sqrt k * Real.sqrt l) =
      (b k / Real.sqrt k) * (b l / Real.sqrt l) by ring, Complex.ofReal_mul]
  ring

/-- Card 20. For N ≥ 2 the tapered Hardy signal equals the Fourier transform of its dual
multiplied by 2π^(1/4).
Titchmarsh, §10.10, p. 269, finite mollifier inserted in the transform. -/
theorem dual_transform (N : ℕ) (hN : 2 ≤ N) (t : ℝ) :
    (signal N t : ℂ) = ((2*Real.pi ^ (1/4 : ℝ) : ℝ) : ℂ) * ft (dual N (beta N)) t := by
  let f (y : ℝ) := K ((y : ℂ) + Complex.I * angle N)
  have ha := angle_mem_strip hN
  have h := ft_sum_translates (D N ×ˢ D N)
    (fun p ↦ ((beta N p.1 * beta N p.2 / Real.sqrt ((p.1 : ℝ) * p.2) : ℝ) : ℂ))
    (fun p ↦ Real.log ((p.1 : ℝ) / p.2)) f (integrable_shifted_kernel ha) t
  simp only [Finset.sum_product] at h
  change ft (dual N (beta N)) t = _ at h
  rw [mollifier_phase_sum] at h
  rw [signal, archimedean_normalization, h, show ft f t = _ from shift_transform t _ ha,
    kernel_real_transform, ← angle]
  push_cast
  ring

end RiemannMasullo.Selberg
