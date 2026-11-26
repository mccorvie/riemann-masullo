module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Int.ModEq
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Separated Taylor remainder for a polynomial weight

For `p(x) = (1 + x²)^(s/2)`, subtract the logarithmic derivative term from the
translated weight difference and divide by the geometric mean of the two weights.
On every strip `|x - y| ≤ R`, this normalized remainder is a finite sum of products
of real functions in `L²(ℝ)`. Each factor is bounded by a constant times `1 / (1 + |x|)`.

On a pair of unit intervals with a fixed offset, expansion about their common
integer anchor gives six products. Coloring the integers modulo a number larger
than the range of offsets then selects the correct products throughout the strip.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped BigOperators

namespace RiemannMasullo.TranslationWeight

/-- The real polynomial Sobolev weight. -/
def polynomialWeight (s x : ℝ) : ℝ := (1 + x ^ 2) ^ (s / 2)

/-- Logarithmic derivative of the polynomial weight. -/
private def logSlope (s z : ℝ) : ℝ := s * z / (1 + z ^ 2)

/-- Weight divided by its value at the cell center. -/
private def cellPolynomial (s n z : ℝ) : ℝ := polynomialWeight s z / polynomialWeight s n

/-- Remainder for the polynomial weight normalized at `n`. -/
private def cellTaylor (s n z : ℝ) : ℝ := cellPolynomial s n z - 1 - logSlope s n * (z - n)

/-- The conjugated scalar residual on a pair of cells, before the exponential factor. -/
private def cellDefect (s n x y : ℝ) : ℝ :=
  (cellPolynomial s n x - cellPolynomial s n y - logSlope s x * (x - y) * cellPolynomial s n y) /
    Real.sqrt (cellPolynomial s n x * cellPolynomial s n y)

private def bracket (n : ℝ) : ℝ := 1 + |n|
private def invRoot (s n z : ℝ) : ℝ := (Real.sqrt (cellPolynomial s n z))⁻¹

private theorem bpos (z : ℝ) : 0 < 1 + z ^ 2 := by positivity
private theorem bracket_pos (n : ℝ) : 0 < bracket n := by unfold bracket; positivity
private theorem ppos (s z : ℝ) : 0 < polynomialWeight s z := Real.rpow_pos_of_pos (bpos z) _
private theorem cpos (s n z : ℝ) : 0 < cellPolynomial s n z := div_pos (ppos s z) (ppos s n)

private theorem polynomialWeight_hasDerivAt (s z : ℝ) :
    HasDerivAt (polynomialWeight s) (logSlope s z * polynomialWeight s z) z := by
  have h := (((hasDerivAt_id z).fun_pow 2).const_add 1).rpow_const (p := s / 2) (Or.inl (bpos z).ne')
  change HasDerivAt (fun u : ℝ ↦ (1 + u ^ 2) ^ (s / 2)) _ z
  apply h.congr_deriv
  dsimp [logSlope, polynomialWeight]
  rw [Real.rpow_sub_one (bpos z).ne']
  ring

private theorem bracket_sq (z : ℝ) : bracket z ^ 2 ≤ 2 * (1 + z ^ 2) := by
  unfold bracket
  nlinarith only [sq_nonneg (|z|-1), sq_abs z]

private theorem abs_le_square (z : ℝ) : |z| ≤ 1 + z ^ 2 := by
  nlinarith only [sq_nonneg (|z|-1), sq_abs z, sq_nonneg z]

private theorem bracket_compare {a b D : ℝ} (h : |a - b| ≤ D) :
    bracket a ≤ (1 + D) * bracket b := by
  have H : |a| ≤ |a - b| + |b| := by simpa using abs_add_le (a - b) b
  have hD := (abs_nonneg _).trans h
  dsimp [bracket]
  nlinarith only [H, h, mul_nonneg hD (abs_nonneg b)]

private theorem slope_bound (s z : ℝ) : |logSlope s z| * bracket z ≤ 2 * |s| := by
  have A : |z| * bracket z ≤ 2 * (1 + z ^ 2) := by
    dsimp [bracket]
    nlinarith only [abs_le_square z, sq_abs z]
  calc |logSlope s z| * bracket z = |s| * (|z| * bracket z / (1 + z ^ 2)) := by
         rw [logSlope, abs_div, abs_mul, abs_of_pos (bpos z)]
         ring
       _ ≤ |s| * 2 := mul_le_mul_of_nonneg_left ((div_le_iff₀ (bpos z)).mpr A) (abs_nonneg _)
       _ = _ := mul_comm _ _

private theorem slope_diff_bound (s : ℝ) {n z D : ℝ} (h : |z - n| ≤ D) :
    |logSlope s n - logSlope s z| * bracket n ^ 2 ≤ 2 * |s| * D * (1 + D) := by
  have hd := (abs_nonneg _).trans h
  have hnz : |n - z| ≤ D := by simpa [abs_sub_comm n z] using h
  have hn : |n| ≤ |z| + D := by
    have htri : |n| ≤ |n - z| + |z| := by simpa using abs_add_le (n - z) z
    linarith only [htri, hnz]
  have hp : |1 - n * z| ≤ (1 + D) * (1 + z ^ 2) := by
    calc |1 - n * z| ≤ 1 + |n| * |z| := by simpa only [abs_one, abs_mul] using abs_sub (1:ℝ) (n * z)
         _ ≤ 1 + (|z| + D) * |z| := add_le_add le_rfl (mul_le_mul_of_nonneg_right hn (abs_nonneg _))
         _ ≤ _ := by nlinarith only [sq_abs z, mul_le_mul_of_nonneg_left (abs_le_square z) hd]
  have he : (logSlope s n - logSlope s z) * (1 + n ^ 2) = s * (n - z) * (1 - n * z) / (1 + z ^ 2) := by
    unfold logSlope
    field_simp [(bpos n).ne', (bpos z).ne']
    ring
  have hs : |logSlope s n - logSlope s z| * (1 + n ^ 2) ≤ |s| * D * (1 + D) := by
    calc _ = |(logSlope s n - logSlope s z) * (1 + n ^ 2)| := by rw [abs_mul, abs_of_pos (bpos n)]
         _ = |s| * |n - z| * (|1 - n * z| / (1 + z ^ 2)) := by
            rw [he, abs_div, abs_mul, abs_mul, abs_of_pos (bpos z)]
            ring
         _ ≤ _ := mul_le_mul (mul_le_mul_of_nonneg_left hnz (abs_nonneg _))
           ((div_le_iff₀ (bpos z)).mpr hp) (div_nonneg (abs_nonneg _) (bpos z).le)
           (mul_nonneg (abs_nonneg _) hd)
  calc _ ≤ |logSlope s n - logSlope s z| * (2 * (1 + n ^ 2)) :=
         mul_le_mul_of_nonneg_left (bracket_sq n) (abs_nonneg _)
       _ ≤ _ := by linarith only [hs]

private theorem nearby_quadratic {n z D : ℝ} (h : |z - n| ≤ D) :
    (1 + z ^ 2) / (1 + n ^ 2) ≤ 2 * (1 + D ^ 2) := by
  have tri : |z| ≤ |n| + D := by
    have h' : |z| ≤ |z - n| + |n| := by simpa using abs_add_le (z - n) n
    linarith only [h', h]
  have hs := pow_le_pow_left₀ (abs_nonneg _) tri 2
  apply (div_le_iff₀ (bpos n)).mpr
  nlinarith only [hs, sq_abs z, sq_abs n, sq_nonneg (|n|-D), mul_nonneg (sq_nonneg D) (sq_nonneg n)]

private theorem nearby_power (p : ℝ) {n z D : ℝ} (h : |z - n| ≤ D) :
    ((1 + z ^ 2) / (1 + n ^ 2)) ^ p ≤ (2 * (1 + D ^ 2)) ^ |p| := by
  by_cases hp : 0 ≤ p
  · rw [abs_of_nonneg hp]
    exact Real.rpow_le_rpow (div_nonneg (bpos z).le (bpos n).le) (nearby_quadratic h) hp
  · have hnz : |n - z| ≤ D := by simpa only [abs_sub_comm n z] using h
    have hp' := lt_of_not_ge hp
    rw [abs_of_neg hp']
    calc
      ((1 + z ^ 2) / (1 + n ^ 2)) ^ p = ((1 + n ^ 2) / (1 + z ^ 2)) ^ (-p) := by
        rw [← inv_div, ← Real.rpow_neg_eq_inv_rpow]
      _ ≤ _ := Real.rpow_le_rpow (div_nonneg (bpos n).le (bpos z).le)
        (nearby_quadratic hnz) (neg_nonneg.mpr hp'.le)

private theorem cell_as_power (s n z : ℝ) :
    cellPolynomial s n z = ((1 + z ^ 2) / (1 + n ^ 2)) ^ (s / 2) := by
  rw [Real.div_rpow (bpos z).le (bpos n).le]; rfl

private theorem inv_root_bound (s : ℝ) {n z D : ℝ} (h : |z - n| ≤ D) :
    |invRoot s n z| ≤ (2 * (1 + D ^ 2)) ^ |-(s / 4)| := by
  have hq : 0 ≤ (1 + z ^ 2) / (1 + n ^ 2) := div_nonneg (bpos z).le (bpos n).le
  rw [invRoot, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (cpos _ _ _))), cell_as_power,
    Real.sqrt_eq_rpow, ← Real.rpow_mul hq, ← Real.rpow_neg hq]
  convert nearby_power (-(s / 4)) h using 1
  ring_nf

private theorem cell_hasDerivAt (s n z : ℝ) :
    HasDerivAt (cellPolynomial s n) (cellPolynomial s n z * logSlope s z) z := by
  have h := (polynomialWeight_hasDerivAt s z).div_const (polynomialWeight s n)
  apply h.congr_deriv
  dsimp only [cellPolynomial]
  ring

private theorem cellTaylor_hasDerivAt (s n z : ℝ) :
    HasDerivAt (cellTaylor s n) (cellPolynomial s n z * logSlope s z - logSlope s n) z := by
  have lin := ((hasDerivAt_id z).sub_const n).const_mul (logSlope s n)
  simpa using! ((cell_hasDerivAt s n z).sub_const 1).sub lin

/-- Mean value estimate on a window centered at the anchor, in either direction. -/
private theorem change_on_window {f g : ℝ → ℝ} {n z D K : ℝ} (hz : |z - n| ≤ D)
    (hg : ∀ u, HasDerivAt f (g u) u) (hb : ∀ u, |u - n| ≤ D → |g u| ≤ K) :
    |f z - f n| ≤ K * D := by
  let I := Icc (n - D) (n + D)
  have hD := (abs_nonneg _).trans hz
  have hn : n ∈ I := ⟨by linarith, by linarith⟩
  have hzi : z ∈ I := by
    obtain ⟨h₁, h₂⟩ := abs_le.mp hz
    exact ⟨by linarith, by linarith⟩
  have mem (u : ℝ) (hu : u ∈ I) : |u - n| ≤ D := by
    obtain ⟨h₁, h₂⟩ := hu
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h := (convex_Icc (n - D) (n + D)).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun u _ ↦ (hg u).hasDerivWithinAt)
    (fun u hu ↦ by simpa only [Real.norm_eq_abs] using hb u (mem u hu)) hn hzi
  have hK := (abs_nonneg _).trans (hb n (mem n hn))
  exact (show |f z - f n| ≤ K * |z - n| by simpa only [Real.norm_eq_abs] using h).trans
    (mul_le_mul_of_nonneg_left hz hK)

private theorem continuous_p (s : ℝ) : Continuous (polynomialWeight s) :=
  continuous_iff_continuousAt.mpr fun z ↦ (polynomialWeight_hasDerivAt s z).continuousAt

private structure Controls (s n z K : ℝ) : Prop where
  one : 1 ≤ K
  root : |invRoot s n z| ≤ K
  displacement : |z - n| ≤ K
  error : |cellTaylor s n z * bracket n ^ 2| ≤ K
  difference : |(logSlope s n - logSlope s z) * bracket n ^ 2| ≤ K
  slope : |logSlope s z * bracket n| ≤ K
  change : |(cellPolynomial s n z - 1) * bracket n| ≤ K

/-- All quantities appearing in the separated products are uniformly bounded after
their indicated bracket rescalings. The two applications of the mean value theorem
first estimate the normalized weight change and then its Taylor remainder. -/
private theorem controls_uniform (s D : ℝ) (hD : 0 ≤ D) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n z, |z - n| ≤ D → Controls s n z K := by
  let P := (2 * (1 + D ^ 2)) ^ |s / 2|
  let I := (2 * (1 + D ^ 2)) ^ |-(s / 4)|
  let S := 2 * |s| * (1 + D)
  let G := 2 * |s| * D * (1 + D)
  let Q := P * S * D
  let E := (Q * S + G) * D
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have sl {n z : ℝ} (hz : |z - n| ≤ D) : |logSlope s z * bracket n| ≤ S := by
    rw [abs_mul, abs_of_pos (bracket_pos n)]
    have hn : |n - z| ≤ D := by simpa only [abs_sub_comm n z] using hz
    calc
      _ ≤ |logSlope s z| * ((1 + D) * bracket z) :=
        mul_le_mul_of_nonneg_left (bracket_compare hn) (abs_nonneg _)
      _ = (|logSlope s z| * bracket z) * (1 + D) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (slope_bound s z) (by linarith)
  have delta {n z : ℝ} (hz : |z - n| ≤ D) : |(cellPolynomial s n z - 1) * bracket n| ≤ Q := by
    have bound (u : ℝ) (hu : |u - n| ≤ D) :
        |(cellPolynomial s n u * logSlope s u) * bracket n| ≤ P * S := by
      have cp : |cellPolynomial s n u| ≤ P := by
        rw [abs_of_pos (cpos s n u), cell_as_power]
        exact nearby_power _ hu
      rw [mul_assoc, abs_mul]
      exact mul_le_mul cp (sl hu) (abs_nonneg _) hP
    have h := change_on_window hz
      (fun u ↦ (cell_hasDerivAt s n u).mul_const (bracket n)) bound
    have en : cellPolynomial s n n = 1 := div_self (ppos s n).ne'
    change |cellPolynomial s n z * bracket n - cellPolynomial s n n * bracket n| ≤ _ at h
    simpa only [en, sub_mul] using h
  have err {n z : ℝ} (hz : |z - n| ≤ D) : |cellTaylor s n z * bracket n ^ 2| ≤ E := by
    have bound (u : ℝ) (hu : |u - n| ≤ D) :
        |(cellPolynomial s n u * logSlope s u - logSlope s n) * bracket n ^ 2| ≤ Q * S + G := by
      have idn : (cellPolynomial s n u * logSlope s u - logSlope s n) * bracket n ^ 2 =
          ((cellPolynomial s n u - 1) * bracket n) * (logSlope s u * bracket n) -
          (logSlope s n - logSlope s u) * bracket n ^ 2 := by ring
      rw [idn]
      apply (abs_sub _ _).trans
      rw [abs_mul]
      refine add_le_add (mul_le_mul (delta hu) (sl hu) (abs_nonneg _) ((abs_nonneg _).trans (delta hu))) ?_
      rw [abs_mul, abs_of_nonneg (sq_nonneg (bracket n))]
      exact slope_diff_bound s hu
    have en : cellTaylor s n n = 0 := by simp [cellTaylor, cellPolynomial, (ppos s n).ne']
    have h := change_on_window hz
      (fun u ↦ (cellTaylor_hasDerivAt s n u).mul_const (bracket n ^ 2)) bound
    change |cellTaylor s n z * bracket n ^ 2 - cellTaylor s n n * bracket n ^ 2| ≤ _ at h
    simpa only [en, zero_mul, sub_zero] using h
  let K := max 1 (max D (max I (max E (max G (max S Q)))))
  have hK : 1 ≤ K ∧ D ≤ K ∧ I ≤ K ∧ E ≤ K ∧ G ≤ K ∧ S ≤ K ∧ Q ≤ K := by
    simp [K, le_max_iff]
  refine ⟨K, hK.1, fun n z hz ↦ ?_⟩
  exact ⟨hK.1, (inv_root_bound s hz).trans hK.2.2.1, hz.trans hK.2.1, (err hz).trans hK.2.2.2.1,
    by simpa only [abs_mul, abs_of_nonneg (sq_nonneg (bracket n))] using
      (slope_diff_bound s hz).trans hK.2.2.2.2.1,
    (sl hz).trans hK.2.2.2.2.2.1, (delta hz).trans hK.2.2.2.2.2.2⟩

/-- Numerators of the six output factors. Moving one bracket from the input to the
output distributes the second-order decay between the two one-variable factors. -/
private def leftCoeff (s n z : ℝ) : Fin 6 → ℝ :=
  let u := z - n
  let D := (logSlope s n - logSlope s z) * bracket n ^ 2
  let E := cellTaylor s n z * bracket n ^ 2
  let A := logSlope s z * bracket n
  ![D * u, -D, E, -1, -(A * u), A]

/-- Numerators of the six input factors, in the matching order. -/
private def rightCoeff (s n z : ℝ) : Fin 6 → ℝ :=
  let v := z - n
  let E := cellTaylor s n z * bracket n ^ 2
  let Q := (cellPolynomial s n z - 1) * bracket n
  ![1, v, 1, E, Q, Q * v]

private def leftMaskAt (s n z : ℝ) (i : Fin 6) : ℝ :=
  invRoot s n z * leftCoeff s n z i / bracket n

private def rightMaskAt (s n z : ℝ) (i : Fin 6) : ℝ :=
  invRoot s n z * rightCoeff s n z i / bracket n

private theorem coefficient_bounds {s n z K : ℝ} (h : Controls s n z K) (i : Fin 6) :
    |leftCoeff s n z i| ≤ K ^ 2 ∧ |rightCoeff s n z i| ≤ K ^ 2 := by
  have k0 : 0 ≤ K := zero_le_one.trans h.one
  have k1 : K ≤ K ^ 2 := by nlinarith only [mul_nonneg k0 (sub_nonneg.mpr h.one)]
  have h1 : |(1:ℝ)| ≤ K ^ 2 := by simpa only [abs_one] using h.one.trans k1
  have hn1 : |(-1:ℝ)| ≤ K ^ 2 := (abs_neg (1:ℝ)) ▸ h1
  have prod {x y : ℝ} (hx : |x| ≤ K) (hy : |y| ≤ K) : |x * y| ≤ K ^ 2 := by
    rw [abs_mul, sq]
    exact mul_le_mul hx hy (abs_nonneg _) k0
  fin_cases i
  · exact ⟨prod h.difference h.displacement, h1⟩
  · refine ⟨?_, h.displacement.trans k1⟩
    change abs (-((logSlope s n - logSlope s z) * bracket n ^ 2)) ≤ K ^ 2
    rw [abs_neg]
    exact h.difference.trans k1
  · exact ⟨h.error.trans k1, h1⟩
  · exact ⟨hn1, h.error.trans k1⟩
  · refine ⟨?_, h.change.trans k1⟩
    change abs (-(logSlope s z * bracket n * (z - n))) ≤ K ^ 2
    rw [abs_neg]
    exact prod h.slope h.displacement
  · exact ⟨h.slope.trans k1, prod h.change h.displacement⟩

private theorem masks_bound {s n z K D : ℝ} (hz : |z - n| ≤ D) (h : Controls s n z K) (i : Fin 6) :
    |leftMaskAt s n z i| ≤ (K ^ 3 * (1 + D)) / bracket z ∧
    |rightMaskAt s n z i| ≤ (K ^ 3 * (1 + D)) / bracket z := by
  have hh (a : ℝ) (ha : |a| ≤ K ^ 2) :
      |invRoot s n z * a / bracket n| ≤ K ^ 3 * (1 + D) / bracket z := by
    rw [abs_div, abs_mul, abs_of_pos (bracket_pos n)]
    apply (div_le_div_iff₀ (bracket_pos n) (bracket_pos z)).mpr
    have h0 : 0 ≤ K := zero_le_one.trans h.one
    calc
      |invRoot s n z| * |a| * bracket z ≤ (K * K ^ 2) * ((1 + D) * bracket n) :=
        mul_le_mul (mul_le_mul h.root ha (abs_nonneg _) h0) (bracket_compare hz)
          (bracket_pos _).le (mul_nonneg h0 (sq_nonneg _))
      _ = _ := by ring
  exact ⟨hh _ (coefficient_bounds h i).1, hh _ (coefficient_bounds h i).2⟩

private theorem masks_sum (s n x y : ℝ) :
    ∑ i : Fin 6, leftMaskAt s n x i * rightMaskAt s n y i = cellDefect s n x y := by
  have hbx := (Real.sqrt_pos.mpr (cpos s n x)).ne'
  have hby := (Real.sqrt_pos.mpr (cpos s n y)).ne'
  have hn := (bracket_pos n).ne'
  rw [cellDefect, Real.sqrt_mul (cpos s n x).le]
  simp [Fin.sum_univ_succ, leftMaskAt, rightMaskAt, leftCoeff, rightCoeff, invRoot, cellTaylor]
  field_simp [hbx, hby, hn]
  ring

/-- The scalar symbol in a normalization independent of the cell center. -/
private def scalarDefect (s x y : ℝ) : ℝ :=
  (polynomialWeight s x - polynomialWeight s y - logSlope s x * (x - y) * polynomialWeight s y) /
    Real.sqrt (polynomialWeight s x * polynomialWeight s y)

/-- Dividing both polynomial weights by their common central value leaves the symbol unchanged. -/
private theorem cellDefect_eq_scalarDefect (s n x y : ℝ) : cellDefect s n x y = scalarDefect s x y := by
  have hn := ppos s n
  have hxy := mul_pos (ppos s x) (ppos s y)
  have hxy' := (Real.sqrt_pos.mpr hxy).ne'
  unfold cellDefect scalarDefect cellPolynomial
  rw [div_mul_div_comm, ← sq, Real.sqrt_div hxy.le, Real.sqrt_sq hn.le]
  field_simp [hn.ne', hxy']

private theorem measurable_six {f₀ f₁ f₂ f₃ f₄ f₅ : ℝ → ℝ} (h₀ : Measurable f₀)
    (h₁ : Measurable f₁) (h₂ : Measurable f₂) (h₃ : Measurable f₃) (h₄ : Measurable f₄)
    (h₅ : Measurable f₅) (i : Fin 6) :
    Measurable (fun z ↦ ![f₀ z, f₁ z, f₂ z, f₃ z, f₄ z, f₅ z] i) := by
  fin_cases i
  · exact h₀
  · exact h₁
  · exact h₂
  · exact h₃
  · exact h₄
  · exact h₅

private theorem measurable_logSlope (s : ℝ) : Measurable (logSlope s) := by
  have hl : Continuous (logSlope s) := (continuous_const.mul continuous_id).div
    (continuous_const.add (continuous_id.pow 2)) fun z ↦ (bpos z).ne'
  exact hl.measurable

private theorem measurable_mask_vectors {u d e a q r b : ℝ → ℝ}
    (hu : Measurable u) (hd : Measurable d) (he : Measurable e) (ha : Measurable a)
    (hq : Measurable q) (hr : Measurable r) (hb : Measurable b) (i : Fin 6) :
    Measurable (fun z ↦ r z * ![d z * u z, -d z, e z, -1, -(a z * u z), a z] i / b z) ∧
      Measurable (fun z ↦ r z * ![1, u z, 1, e z, q z, q z * u z] i / b z) := by
  have ml := measurable_six (f₀ := fun z ↦ d z * u z) (f₁ := fun z ↦ -d z) (f₂ := e) (f₃ := fun _ ↦ -1)
    (f₄ := fun z ↦ -(a z * u z)) (f₅ := a) (hd.mul hu) hd.neg he measurable_const (ha.mul hu).neg ha i
  have mr := measurable_six (f₀ := fun _ ↦ 1) (f₁ := u) (f₂ := fun _ ↦ 1) (f₃ := e) (f₄ := q)
    (f₅ := fun z ↦ q z * u z) measurable_const hu measurable_const he hq (hq.mul hu) i
  exact ⟨(hr.mul ml).div hb, (hr.mul mr).div hb⟩

private theorem measurable_cellPolynomial_comp (s : ℝ) {n : ℝ → ℝ} (hn : Measurable n) :
    Measurable (fun z ↦ cellPolynomial s (n z) z) := by
  have hp := (continuous_p s).measurable
  exact hp.div (hp.comp hn)

private theorem measurable_cellTaylor_comp (s : ℝ) {n : ℝ → ℝ} (hn : Measurable n) :
    Measurable (fun z ↦ cellTaylor s (n z) z) := by
  exact ((measurable_cellPolynomial_comp s hn).sub_const 1).sub
    (((measurable_logSlope s).comp hn).mul (measurable_id.sub hn))

private theorem measurable_invRoot_comp (s : ℝ) {n : ℝ → ℝ} (hn : Measurable n) :
    Measurable (fun z ↦ invRoot s (n z) z) :=
  (measurable_cellPolynomial_comp s hn).sqrt.inv

private theorem masks_measurable (s : ℝ) (n : ℝ → ℝ) (hn : Measurable n) (i : Fin 6) :
    Measurable (fun z ↦ leftMaskAt s (n z) z i) ∧ Measurable (fun z ↦ rightMaskAt s (n z) z i) := by
  let d := fun z ↦ (logSlope s (n z) - logSlope s z) * bracket (n z) ^ 2
  let e := fun z ↦ cellTaylor s (n z) z * bracket (n z) ^ 2
  let a := fun z ↦ logSlope s z * bracket (n z)
  let q := fun z ↦ (cellPolynomial s (n z) z - 1) * bracket (n z)
  have hb : Measurable (fun z ↦ bracket (n z)) := measurable_const.add (continuous_abs.measurable.comp hn)
  have hb2 : Measurable (fun z ↦ bracket (n z) ^ 2) := hb.pow_const 2
  have hl := measurable_logSlope s
  exact measurable_mask_vectors (u := fun z ↦ z - n z) (d := d) (e := e) (a := a) (q := q)
    (r := fun z ↦ invRoot s (n z) z) (b := fun z ↦ bracket (n z))
    (measurable_id.sub hn) (((hl.comp hn).sub hl).mul hb2) ((measurable_cellTaylor_comp s hn).mul hb2)
    (hl.mul hb) (((measurable_cellPolynomial_comp s hn).sub_const 1).mul hb)
    (measurable_invRoot_comp s hn) hb i

/-- A shifted floor anchor, used with zero shift for the output coordinate. -/
private def anchor (j : ℤ) (x : ℝ) : ℤ := ⌊x⌋ + j

private theorem measurable_anchor (j : ℤ) : Measurable (anchor j) :=
  Int.measurable_floor.add_const j

private def center (j : ℤ) (z : ℝ) : ℝ := (anchor j z : ℝ)

private theorem measurable_center (j : ℤ) : Measurable (center j) := by
  have hi : Measurable (fun a : ℤ ↦ (a : ℝ)) := measurable_of_countable _
  exact hi.comp (measurable_anchor j)

private theorem center_distance (j : ℤ) (z : ℝ) : |z - center j z| ≤ 1 + |(j:ℝ)| := by
  have hf := Int.floor_le z
  have ht := Int.lt_floor_add_one z
  have hd : |z - (⌊z⌋ : ℝ)| ≤ 1 := by rw [abs_of_nonneg (sub_nonneg.mpr hf)]; linarith
  have eqn : z - center j z = (z - (⌊z⌋ : ℝ)) - (j:ℝ) := by unfold center anchor; push_cast; ring
  rw [eqn]
  exact (abs_sub _ _).trans (add_le_add hd le_rfl)

private theorem memLp_two_of_bracket_bound {f : ℝ → ℝ} {C : ℝ} (hm : Measurable f)
    (hb : ∀ z, |f z| ≤ C / (1 + |z|)) : MemLp f 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (integrable_inv_one_add_sq.const_mul (C ^ 2)).mono' (hm.aestronglyMeasurable.norm.pow 2)
  apply Eventually.of_forall
  intro z
  change ‖‖f z‖ ^ 2‖ ≤ C ^ 2 * (1 + z ^ 2)⁻¹
  rw [Real.norm_of_nonneg (sq_nonneg (‖f z‖)), Real.norm_eq_abs, ← div_eq_mul_inv]
  have hz : 1 + z ^ 2 ≤ (1 + |z|) ^ 2 := by nlinarith only [sq_abs z, abs_nonneg z]
  calc |f z| ^ 2 ≤ (C / (1 + |z|)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb z) 2
       _ = C ^ 2 / (1 + |z|) ^ 2 := div_pow _ _ _
       _ ≤ _ := div_le_div_of_nonneg_left (sq_nonneg C) (bpos z) hz

/-- On any prescribed difference of floor indices the scalar symbol is the sum of
six products of real measurable functions. Both factors have the same global
inverse-linear decay bound, including the cells meeting the origin. -/
private theorem exists_six_cell_masks (s : ℝ) (j : ℤ) :
    ∃ (A B : Fin 6 → ℝ → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ i, Measurable (A i) ∧ Measurable (B i)) ∧
      (∀ i z, |A i z| ≤ C / (1 + |z|) ∧ |B i z| ≤ C / (1 + |z|)) ∧
      ∀ x y : ℝ, ⌊x⌋ = ⌊y⌋ + j → (∑ i, A i x * B i y) = scalarDefect s x y := by
  let D : ℝ := 1 + |(j:ℝ)|
  have hd : 0 ≤ D := by dsimp [D]; positivity
  obtain ⟨K, hk, controls⟩ := controls_uniform s D hd
  let A (i : Fin 6) (x : ℝ) := leftMaskAt s (center 0 x) x i
  let B (i : Fin 6) (y : ℝ) := rightMaskAt s (center j y) y i
  let C := K ^ 3 * (1 + D)
  have hm (i : Fin 6) : Measurable (A i) ∧ Measurable (B i) :=
    ⟨(masks_measurable s (center 0) (measurable_center 0) i).1,
     (masks_measurable s (center j) (measurable_center j) i).2⟩
  have bd (i : Fin 6) (z : ℝ) : |A i z| ≤ C / (1 + |z|) ∧ |B i z| ≤ C / (1 + |z|) := by
    have h0 : |z - center 0 z| ≤ D :=
      (center_distance 0 z).trans (by simp [D])
    have hj := center_distance j z
    exact ⟨(masks_bound h0 (controls _ _ h0) i).1,
      (masks_bound hj (controls _ _ hj) i).2⟩
  have k0 := zero_le_one.trans hk
  refine ⟨A, B, C, by dsimp [C]; positivity, hm, bd, ?_⟩
  intro x y hxy
  have hc : center 0 x = center j y := by simp [center, anchor, hxy]
  change (∑ i, leftMaskAt s (center 0 x) x i * rightMaskAt s (center j y) y i) = _
  rw [← hc, masks_sum, cellDefect_eq_scalarDefect]

/-- A uniform bound on the integer floor difference for a propagation radius `R`. -/
private def radiusCells (R : ℝ) : ℕ := ⌈R⌉₊ + 1

/-- The modulus separating all admissible floor offsets. -/
private def modulus (N : ℕ) : ℤ := 2 * (N : ℤ) + 1

/-- The canonical residue representatives. -/
private def colors (N : ℕ) : Finset ℤ := Finset.Ico 0 (modulus N)

/-- The admissible source offsets. -/
private def offsets (N : ℕ) : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)

/-- The indicator that the shifted anchor has the specified residue. -/
private def mask (N : ℕ) (i j : ℤ) (x : ℝ) : ℝ :=
  if anchor j x % modulus N = i then 1 else 0

private theorem modulus_pos (N : ℕ) : 0 < modulus N := by
  unfold modulus
  omega

private theorem residue_mem_colors (N : ℕ) (n : ℤ) : n % modulus N ∈ colors N :=
  Finset.mem_Ico.mpr ⟨Int.emod_nonneg n (modulus_pos N).ne', Int.emod_lt_of_pos n (modulus_pos N)⟩

private theorem measurable_mask (N : ℕ) (i j : ℤ) : Measurable (mask N i j) := by
  have hm : Measurable (fun x : ℝ ↦ anchor j x % modulus N) :=
    (measurable_of_countable (fun n : ℤ ↦ n % modulus N)).comp (measurable_anchor j)
  exact Measurable.ite (measurableSet_eq_fun hm measurable_const) measurable_const measurable_const

/-- The color cutoffs take only the values zero and one. -/
private theorem mask_zero_or_one (N : ℕ) (i j : ℤ) (x : ℝ) : mask N i j x = 0 ∨ mask N i j x = 1 := by
  unfold mask
  split <;> simp

/-- Finite propagation bounds the floor difference, including negative coordinates and unit boundaries. -/
private theorem floor_sub_mem_offsets {R x y : ℝ} (h : |x - y| ≤ R) :
    ⌊x⌋ - ⌊y⌋ ∈ offsets (radiusCells R) := by
  have hR : R ≤ (⌈R⌉₊ : ℝ) := Nat.le_ceil R
  have hx := Int.floor_le x
  have hy := Int.floor_le y
  have hx' := Int.lt_floor_add_one x
  have hy' := Int.lt_floor_add_one y
  obtain ⟨hlo, hup⟩ := abs_le.mp h
  apply Finset.mem_Icc.mpr
  constructor
  · have : -((⌈R⌉₊ : ℝ) + 1) ≤ (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) := by linarith
    exact_mod_cast this
  · have : (⌊x⌋ : ℝ) - (⌊y⌋ : ℝ) ≤ (⌈R⌉₊ : ℝ) + 1 := by linarith
    exact_mod_cast this

/-- Within the allowed range, equal shifted residues force the actual integer anchors to coincide. -/
private theorem anchor_eq_of_same_color {N : ℕ} {x y : ℝ} {i j : ℤ}
    (hxy : ⌊x⌋ - ⌊y⌋ ∈ offsets N) (hj : j ∈ offsets N)
    (hx : anchor 0 x % modulus N = i) (hy : anchor j y % modulus N = i) :
    anchor 0 x = anchor j y := by
  have hd := (Int.modEq_iff_dvd.mp (show anchor j y ≡ anchor 0 x [ZMOD modulus N] from hy.trans hx.symm))
  have hxy' := Finset.mem_Icc.mp hxy
  have hj' := Finset.mem_Icc.mp hj
  have habs : |anchor 0 x - anchor j y| < modulus N := by
    unfold modulus anchor
    rw [abs_lt]
    constructor <;> omega
  exact sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd hd habs)

/-- On the propagation window exactly the output residue and the true floor difference have
both masks active. -/
private theorem mask_product_eq {N : ℕ} {x y : ℝ} {j : ℤ}
    (hxy : ⌊x⌋ - ⌊y⌋ ∈ offsets N) (hj : j ∈ offsets N) (i : ℤ) :
    mask N i 0 x * mask N i j y =
      if i = ⌊x⌋ % modulus N ∧ j = ⌊x⌋ - ⌊y⌋ then 1 else 0 := by
  by_cases hx : anchor 0 x % modulus N = i
  · by_cases hy : anchor j y % modulus N = i
    · have ha := anchor_eq_of_same_color hxy hj hx hy
      have h₁ : i = ⌊x⌋ % modulus N := by simpa [anchor] using hx.symm
      have h₂ : j = ⌊x⌋ - ⌊y⌋ := by unfold anchor at ha; omega
      have hp : i = ⌊x⌋ % modulus N ∧ j = ⌊x⌋ - ⌊y⌋ := ⟨h₁, h₂⟩
      rw [ite_eq_left hp]
      simp only [mask, ite_eq_left hx, ite_eq_left hy, one_mul]
    · have hh : ¬ (i = ⌊x⌋ % modulus N ∧ j = ⌊x⌋ - ⌊y⌋) := by
        rintro ⟨rfl, rfl⟩
        exact hy (by simp [anchor])
      simp [mask, hx, hy, hh]
  · have hh : i ≠ ⌊x⌋ % modulus N := by simpa [anchor, eq_comm] using hx
    simp [mask, hx, hh]

/-- The unique active rectangular mask selects the summand at the output floor residue
and the exact floor difference. -/
private theorem sum_mask_mul {N : ℕ} {x y : ℝ}
    (hxy : ⌊x⌋ - ⌊y⌋ ∈ offsets N) (F : ℤ → ℤ → ℝ) :
    ∑ i ∈ colors N, ∑ j ∈ offsets N, (mask N i 0 x * mask N i j y) * F i j =
      F (⌊x⌋ % modulus N) (⌊x⌋ - ⌊y⌋) := by
  rw [Finset.sum_eq_single_of_mem (⌊x⌋ % modulus N) (residue_mem_colors N _)]
  · rw [Finset.sum_eq_single_of_mem (⌊x⌋ - ⌊y⌋) hxy]
    · simp [mask_product_eq hxy hxy]
    · intro j hj hne
      simp [mask_product_eq hxy hj, hne]
  · intro i _ hi
    apply Finset.sum_eq_zero
    intro j hj
    simp [mask_product_eq hxy hj, hi]

private theorem abs_mask_mul_le (N : ℕ) (i j : ℤ) (x u : ℝ) :
    |mask N i j x * u| ≤ |u| := by
  rcases mask_zero_or_one N i j x with h | h <;> simp [h]

/-- On every bounded translation strip, the normalized first-order Taylor remainder of
`polynomialWeight` is a finite sum of products of measurable real L² factors. Each
factor is bounded by a constant times `1 / (1 + |z|)` on the entire real line. -/
theorem exists_finite_polynomialWeight_masks (s R : ℝ) :
    ∃ (ι : Type) (_ : Fintype ι) (A B : ι → ℝ → ℝ),
      (∀ i, Measurable (A i) ∧ Measurable (B i)) ∧
      (∀ i, MemLp (A i) 2 volume ∧ MemLp (B i) 2 volume) ∧
      (∀ i, ∃ C : ℝ, 0 ≤ C ∧ ∀ z, ‖A i z‖ ≤ C / (1 + |z|) ∧ ‖B i z‖ ≤ C / (1 + |z|)) ∧
      ∀ x y, |x - y| ≤ R →
        (∑ i, A i x * B i y) = (polynomialWeight s x - polynomialWeight s y -
          (s * x / (1 + x ^ 2)) * (x - y) * polynomialWeight s y) /
          Real.sqrt (polynomialWeight s x * polynomialWeight s y) := by
  classical
  choose f g C hC hm hdec hrep using exists_six_cell_masks s
  let N := radiusCells R
  let A (p : (colors N) × (offsets N) × Fin 6) (x : ℝ) :=
    mask N p.1.val 0 x * f p.2.1.val p.2.2 x
  let B (p : (colors N) × (offsets N) × Fin 6) (y : ℝ) :=
    mask N p.1.val p.2.1.val y * g p.2.1.val p.2.2 y
  have hmeas (p : (colors N) × (offsets N) × Fin 6) : Measurable (A p) ∧ Measurable (B p) :=
    ⟨(measurable_mask N p.1 0).mul (hm p.2.1 p.2.2).1,
     (measurable_mask N p.1 p.2.1).mul (hm p.2.1 p.2.2).2⟩
  have hnorm (p : (colors N) × (offsets N) × Fin 6) (z : ℝ) :
      |A p z| ≤ |f p.2.1 p.2.2 z| ∧ |B p z| ≤ |g p.2.1 p.2.2 z| :=
    ⟨abs_mask_mul_le N _ _ _ _, abs_mask_mul_le N _ _ _ _⟩
  have hb (p : (colors N) × (offsets N) × Fin 6) (z : ℝ) :
      |A p z| ≤ C p.2.1 / (1 + |z|) ∧ |B p z| ≤ C p.2.1 / (1 + |z|) :=
    ⟨(hnorm p z).1.trans (hdec p.2.1 p.2.2 z).1, (hnorm p z).2.trans (hdec p.2.1 p.2.2 z).2⟩
  refine ⟨(colors N) × (offsets N) × Fin 6, inferInstance, A, B, hmeas, ?_, ?_, ?_⟩
  · intro p
    exact ⟨memLp_two_of_bracket_bound (hmeas p).1 (fun z ↦ (hb p z).1),
      memLp_two_of_bracket_bound (hmeas p).2 (fun z ↦ (hb p z).2)⟩
  · intro p
    exact ⟨C p.2.1, hC _, fun z ↦ by simpa only [Real.norm_eq_abs] using hb p z⟩
  · intro x y hxy
    calc
      _ = ∑ i ∈ colors N, ∑ j ∈ offsets N,
          (mask N i 0 x * mask N i j y) * (∑ k, f j k x * g j k y) := by
        simp only [Fintype.sum_prod_type, A, B]
        rw [← Finset.sum_coe_sort (colors N) (fun i ↦ ∑ j ∈ offsets N,
          (mask N i 0 x * mask N i j y) * (∑ k, f j k x * g j k y))]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.sum_coe_sort (offsets N) (fun j ↦
          (mask N i 0 x * mask N i j y) * (∑ k, f j k x * g j k y))]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k, f (⌊x⌋ - ⌊y⌋) k x * g (⌊x⌋ - ⌊y⌋) k y :=
        sum_mask_mul (floor_sub_mem_offsets hxy) (fun _ j ↦ ∑ k, f j k x * g j k y)
      _ = _ := hrep _ _ _ (by simp)

end RiemannMasullo.TranslationWeight
