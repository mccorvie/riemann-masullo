module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Fourier.KernelSymmetry

public section

namespace RiemannMasullo.Selberg

private theorem pos_of_mem_D {n N : ℕ} (hn : n ∈ D N) : 0 < (n : ℝ) := by
  exact_mod_cast (Finset.mem_Icc.mp hn).1

private theorem angle_mem_strip {N : ℕ} (hN : 2 ≤ N) : |angle N| < Real.pi / 4 := by
  have hH : 1 ≤ (H N : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 100 (by omega : N ≠ 0))
  have hsmall : 1 / (2 * (H N : ℝ)) ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num)
    linarith
  rw [angle, abs_lt]
  constructor
  · linarith [Real.one_le_pi_div_two]
  · exact sub_lt_self _ (by positivity)

private theorem kernel_reflect (x a : ℝ) (ha : |a| < Real.pi / 4) :
    K (-(x : ℂ) + Complex.I * a) = star (K ((x : ℂ) + Complex.I * a)) := by
  let z : ℂ := x + Complex.I * a
  have hz : |z.im| < Real.pi / 4 := by simpa [z] using ha
  have hc : |(star z).im| < Real.pi / 4 := by simpa [Complex.star_def] using hz
  change _ = star (K z)
  rw [← (kernel_symmetry hz).2.1, ← (kernel_symmetry hc).1]
  congr 1
  simp [z, add_comm]

private theorem weighted_kernel (y a c k l : ℝ) (hk : 0 < k) (hl : 0 < l) :
    ((c / Real.sqrt (k * l) : ℝ) : ℂ) *
        K (((y + Real.log (k / l) : ℝ) : ℂ) + Complex.I * a) =
      (Real.exp (y / 2) : ℂ) * osc (a / 2) *
        (((c / l : ℝ) : ℂ) * psi (((Real.exp y * k / l : ℝ) : ℂ) * osc a) -
          osc (-a) * ((c / k : ℝ) : ℂ) / (2 * (Real.exp y : ℂ))) := by
  let z : ℂ := ((y + Real.log (k / l) : ℝ) : ℂ) + Complex.I * a
  have hz : Complex.exp z = ((Real.exp y * k / l : ℝ) : ℂ) * osc a := by
    simp only [z, Complex.exp_add, ← Complex.ofReal_exp, Real.exp_add,
      Real.exp_log (div_pos hk hl), mul_div_assoc, osc]
  have hhalf : Complex.exp (z / 2) =
      (Real.exp (y / 2) : ℂ) * osc (a / 2) * (Real.sqrt (k / l) : ℂ) := by
    have hsplit : z / 2 = ((y / 2 : ℝ) : ℂ) + Complex.I * ((a / 2 : ℝ) : ℂ) +
        ((Real.log (k / l) / 2 : ℝ) : ℂ) := by
      dsimp [z]
      push_cast
      ring
    rw [hsplit, Complex.exp_add, Complex.exp_add, ← Complex.ofReal_exp,
      ← Complex.ofReal_exp (Real.log (k / l) / 2), Real.exp_half (Real.log _),
      Real.exp_log (div_pos hk hl), osc]
  have hcoef : c / Real.sqrt (k * l) * Real.sqrt (k / l) = c / l := by
    rw [Real.sqrt_mul hk.le, Real.sqrt_div hk.le]
    field_simp [(Real.sqrt_pos.2 hk).ne', (Real.sqrt_pos.2 hl).ne', hl.ne']
    rw [Real.sq_sqrt hl.le]
  have hphase : (osc a)⁻¹ = osc (-a) := by simp [osc, Complex.exp_neg]
  have hneg : Complex.exp (-z / 2) = Complex.exp (z / 2) * (Complex.exp z)⁻¹ := by
    rw [← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    ring
  change _ * K z = _
  have hK : K z = Complex.exp (z / 2) * (psi (Complex.exp z) - (Complex.exp z)⁻¹ / 2) := by
    rw [K, hneg]
    ring
  rw [hK, ← mul_assoc, hhalf, mul_left_comm ((c / Real.sqrt (k * l) : ℝ) : ℂ),
    ← Complex.ofReal_mul, hcoef, mul_assoc, hz, mul_inv_rev, hphase, mul_sub]
  congr 2
  push_cast
  field_simp [show (l : ℂ) ≠ 0 by exact_mod_cast hl.ne']

/-- Card 21. Reflection in y conjugates the dual function. At y the dual decomposes into the
rotated Gaussian sum at exp(y) and its explicit correction involving `constTerm`.
Titchmarsh, §§10.10–10.11, pp. 269–270, positive half of f. -/
theorem dual_formula (N : ℕ) (hN : 2 ≤ N) (b : ℕ → ℝ) (y : ℝ) :
    dual N b (-y) = star (dual N b y) ∧
    dual N b y = ((Real.exp (y/2) : ℝ) : ℂ)*osc (angle N/2) *
      (g N b (Real.exp y) - osc (-angle N)*(constTerm N b : ℂ)/(2*(Real.exp y : ℂ))) := by
  constructor
  · unfold dual
    rw [Finset.sum_comm]
    simp only [star_sum, star_mul', Complex.star_def, Complex.conj_ofReal]
    refine Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl fun l hl ↦ ?_
    have hk' := pos_of_mem_D hk
    have hl' := pos_of_mem_D hl
    rw [mul_comm (b l) (b k), mul_comm (l : ℝ) (k : ℝ)]
    congr 1
    have hlog : -y + Real.log ((l : ℝ) / k) = -(y + Real.log ((k : ℝ) / l)) := by
      rw [Real.log_div hl'.ne' hk'.ne', Real.log_div hk'.ne' hl'.ne']
      ring
    rw [hlog, Complex.ofReal_neg]
    exact kernel_reflect _ _ (angle_mem_strip hN)
  · unfold dual g constTerm
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum, Complex.ofReal_sum, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr rfl fun l hl ↦ ?_
    rw [weighted_kernel y (angle N) _ _ _ (pos_of_mem_D hk) (pos_of_mem_D hl)]
    congr 3
    push_cast
    ring

end RiemannMasullo.Selberg
