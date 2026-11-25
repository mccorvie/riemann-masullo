module

public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.GramMatrix
public import Mathlib.Order.SuccPred.Fin
import Mathlib.Analysis.SpecialFunctions.Exp

/-! # Finite inverse Gram diagonals for the exponential kernel on an ordered line -/

@[expose] public noncomputable section

open scoped Matrix InnerProductSpace

namespace RiemannMasullo

private def gapWeight (d : ℝ) : ℝ := 1 / (Real.exp (2 * d) - 1)

private def edgeResponse (x t v : ℝ) : ℝ :=
  gapWeight |t - v| * (Real.exp (-|x - t|) - Real.exp |t - v| * Real.exp (-|x - v|))

private theorem dist_add_between {x y z : ℝ} (h : (x ≤ y ∧ y ≤ z) ∨ (z ≤ y ∧ y ≤ x)) :
    |x - z| = |x - y| + |y - z| := by
  rcases h with ⟨hxy, hyz⟩ | ⟨hzy, hyx⟩
  · rw [abs_of_nonpos (sub_nonpos.mpr (hxy.trans hyz)), abs_of_nonpos (sub_nonpos.mpr hxy),
      abs_of_nonpos (sub_nonpos.mpr hyz)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (hzy.trans hyx)), abs_of_nonneg (sub_nonneg.mpr hyx),
      abs_of_nonneg (sub_nonneg.mpr hzy)]
    ring

private theorem edgeResponse_zero {x t v : ℝ} (h : |x - v| = |x - t| + |t - v|) :
    edgeResponse x t v = 0 := by
  simp only [edgeResponse, ← Real.exp_add, h, show ∀ a b : ℝ, b + -(a + b) = -a by intros; ring,
    sub_self, mul_zero]

private theorem edgeResponse_cancel {x t v : ℝ} (hne : t ≠ v)
    (h : |x - t| = |x - v| + |t - v|) :
    edgeResponse x t v = -Real.exp (-|x - t|) := by
  have hd : 1 < Real.exp (2 * |t - v|) :=
    Real.one_lt_exp_iff.mpr (mul_pos two_pos (abs_pos.mpr (sub_ne_zero.mpr hne)))
  have he : Real.exp |t - v| * Real.exp (-|x - v|) =
      Real.exp (2 * |t - v|) * Real.exp (-|x - t|) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    linarith
  rw [edgeResponse, he, gapWeight]
  field_simp [(sub_pos.mpr hd).ne']
  ring

variable {ι : Type*} [Fintype ι] [LinearOrder ι] [PredOrder ι] [SuccOrder ι]

private def edgeColumn (t : ι → ℝ) (i k : ι) : ι → ℂ :=
  (gapWeight |t i - t k| : ℂ) •
    (Pi.single i 1 - (Real.exp |t i - t k| : ℂ) • Pi.single k 1)

private theorem edgeColumn_apply_self (t : ι → ℝ) (i k : ι) :
    edgeColumn t i k i = (gapWeight |t i - t k| : ℂ) := by
  rcases eq_or_ne i k with rfl | h
  · simp [edgeColumn, gapWeight]
  · simp [edgeColumn, Pi.single_eq_of_ne h]

private theorem edgeColumn_mulVec (t : ι → ℝ) (G : Matrix ι ι ℂ)
    (hG : ∀ i j, G i j = (Real.exp (-|t i - t j|) : ℂ)) (i k j : ι) :
    (G *ᵥ edgeColumn t i k) j = (edgeResponse (t j) (t i) (t k) : ℂ) := by
  simp only [edgeColumn, Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_single_one,
    Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Matrix.col_apply, hG, edgeResponse,
    Complex.ofReal_mul, Complex.ofReal_sub]

/-- The two nearest gaps at a site contribute to the diagonal independently.
The predecessor and successor fix the endpoints, where the missing terms are zero. -/
def exponentialGramDiagonal (t : ι → ℝ) (i : ι) : ℝ :=
  1 + (if Order.pred i = i then 0 else 1 / (Real.exp (2 * (t i - t (Order.pred i))) - 1)) +
    (if Order.succ i = i then 0 else 1 / (Real.exp (2 * (t (Order.succ i) - t i)) - 1))

private theorem exponentialGramDiagonal_nonneg (t : ι → ℝ) (ht : StrictMono t) (i : ι) :
    0 ≤ exponentialGramDiagonal t i := by
  have hL := sub_nonneg.mpr (Real.one_le_exp_iff.mpr
    (mul_nonneg zero_le_two (sub_nonneg.mpr (ht.monotone (Order.pred_le i)))))
  have hR := sub_nonneg.mpr (Real.one_le_exp_iff.mpr
    (mul_nonneg zero_le_two (sub_nonneg.mpr (ht.monotone (Order.le_succ i)))))
  unfold exponentialGramDiagonal
  split_ifs <;> positivity

/-- Each column of the inverse exponential covariance matrix is supported on the site
and its immediate neighbors. This gives the coefficients of its finite cardinal vector. -/
theorem exponentialGram_inverse_col (t : ι → ℝ) (ht : StrictMono t) (G : Matrix ι ι ℂ)
    (hG : ∀ i j, G i j = (Real.exp (-|t i - t j|) : ℂ)) (i : ι) :
    let edge (k : ι) := ((1 / (Real.exp (2 * |t i - t k|) - 1) : ℝ) : ℂ) •
      (Pi.single i 1 - (Real.exp |t i - t k| : ℂ) • Pi.single k 1 : ι → ℂ)
    G⁻¹.col i = Pi.single i 1 + edge (Order.pred i) + edge (Order.succ i) := by
  let B : Matrix ι ι ℂ := fun j k ↦
    (Pi.single k 1 + edgeColumn t k (Order.pred k) + edgeColumn t k (Order.succ k) : ι → ℂ) j
  have hB : G * B = 1 := by
    ext j k
    change (G *ᵥ (Pi.single k 1 + edgeColumn t k (Order.pred k) + edgeColumn t k (Order.succ k))) j = _
    simp only [Matrix.mulVec_add, Matrix.mulVec_single_one, Pi.add_apply, Matrix.col_apply,
      edgeColumn_mulVec t G hG, hG, Matrix.one_apply]
    have hl := ht.monotone (Order.pred_le k)
    have hr := ht.monotone (Order.le_succ k)
    rcases lt_trichotomy j k with hj | rfl | hj
    · have hjl := ht.monotone (Order.le_pred_of_lt hj)
      have hlt := ht (Order.pred_lt_of_not_isMin hj.not_isMin)
      rw [edgeResponse_cancel hlt.ne' (by
          rw [abs_sub_comm (t k) (t (Order.pred k))]
          exact dist_add_between (Or.inl ⟨hjl, hl⟩)),
        edgeResponse_zero (dist_add_between (Or.inl ⟨(ht hj).le, hr⟩)), ite_eq_right hj.ne]
      simp
    · rw [edgeResponse_zero (v := t (Order.pred j)) (by simp),
        edgeResponse_zero (v := t (Order.succ j)) (by simp)]
      simp
    · have hjr := ht.monotone (Order.succ_le_of_lt hj)
      have hlt := ht (Order.lt_succ_of_not_isMax hj.not_isMax)
      rw [edgeResponse_zero (dist_add_between (Or.inr ⟨hl, (ht hj).le⟩)),
        edgeResponse_cancel hlt.ne (by
          rw [abs_sub_comm (t k) (t (Order.succ k))]
          exact dist_add_between (Or.inr ⟨hr, hjr⟩)), ite_eq_right hj.ne']
      simp
  rw [Matrix.inv_eq_right_inv hB]
  rfl

/-- For increasing sites, the inverse of the exponential covariance matrix has a diagonal
determined by the immediately preceding and following sites. At an endpoint its missing
neighbor contributes zero, including both contributions for a singleton. -/
theorem exponentialGram_inverse_diag (t : ι → ℝ) (ht : StrictMono t) (G : Matrix ι ι ℂ)
    (hG : ∀ i j, G i j = (Real.exp (-|t i - t j|) : ℂ)) (i : ι) :
    G⁻¹ i i = (exponentialGramDiagonal t i : ℂ) := by
  have h := congrFun (exponentialGram_inverse_col t ht G hG i) i
  change G⁻¹ i i = _ at h
  rw [h, exponentialGramDiagonal]
  change (Pi.single i (1 : ℂ) + edgeColumn t i (Order.pred i) + edgeColumn t i (Order.succ i) : ι → ℂ) i = _
  simp only [Pi.add_apply, Pi.single_eq_same, edgeColumn_apply_self, Complex.ofReal_add,
    Complex.ofReal_one]
  have hl := ht.monotone (Order.pred_le i)
  have hr := ht.monotone (Order.le_succ i)
  rw [abs_of_nonneg (sub_nonneg.mpr hl), abs_of_nonpos (sub_nonpos.mpr hr), neg_sub]
  by_cases hp : Order.pred i = i <;> by_cases hs : Order.succ i = i <;> simp [hp, hs, gapWeight]

/-- The normalized finite Gram factor on a block sorted by increasing frequency.
A common positive scalar in the inner products, such as the angular Haar mass, cancels. -/
theorem norm_mul_finiteGramCoordinate_sq_of_exponential_inner
    {σ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : σ → H) (S : Finset σ) {n : ℕ} (e : Fin n ≃ S) (t : Fin n → ℝ) (ht : StrictMono t)
    {C : ℝ} (hC : 0 < C)
    (hG : ∀ j k, ⟪u (e j).val, u (e k).val⟫_ℂ = ((C * Real.exp (-|t j - t k|) : ℝ) : ℂ))
    (i : Fin n) :
    (‖u (e i).val‖ * finiteGramCoordinate u (e i).val S) ^ 2 = exponentialGramDiagonal t i := by
  classical
  have hn (k : S) : ‖u k.val‖ = Real.sqrt C := by
    obtain ⟨j, rfl⟩ := e.surjective k
    have hs := congrArg Complex.re (hG j j)
    simp only [sub_self, abs_zero, neg_zero, Real.exp_zero, mul_one,
      Complex.ofReal_re] at hs
    rw [← hs, show (⟪u (e j).val, u (e j).val⟫_ℂ).re = ‖u (e j).val‖ ^ 2 from
      inner_self_eq_norm_sq (𝕜 := ℂ) _, Real.sqrt_sq (norm_nonneg _)]
  let K := Matrix.gram ℂ (fun k : S ↦ ((‖u k.val‖⁻¹ : ℝ) : ℂ) • u k.val)
  have hg (j k : Fin n) : K.submatrix e e j k = (Real.exp (-|t j - t k|) : ℂ) := by
    simp only [K, Matrix.submatrix_apply, Matrix.gram_apply, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal, hn, hG, ← Complex.ofReal_mul]
    congr 1
    field_simp [(Real.sqrt_pos.mpr hC).ne']
    nlinarith [Real.sq_sqrt hC.le]
  have hdiag := exponentialGram_inverse_diag t ht (K.submatrix e e) hg i
  rw [Matrix.inv_submatrix_equiv] at hdiag
  have hnonzero (j : σ) (hj : j ∈ S) : u j ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hn ⟨j, hj⟩]
    exact Real.sqrt_pos.mpr hC
  rw [norm_mul_finiteGramCoordinate_eq_normalized_inverse_diag S hnonzero (e i)]
  change (Real.sqrt (K⁻¹ (e i) (e i)).re) ^ 2 = _
  rw [show K⁻¹ (e i) (e i) = _ from hdiag, Complex.ofReal_re,
    Real.sq_sqrt (exponentialGramDiagonal_nonneg t ht i)]

/-- Removing columns orthogonal to all retained columns preserves the principal
Gram coordinate at a retained site. -/
theorem finiteGramCoordinate_eq_of_orthogonal
    {σ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {u : σ → H} (hu : LinearIndependent ℂ u) {S T : Finset σ} (hT : T ⊆ S)
    {i : σ} (hi : i ∈ T)
    (hoff : ∀ j ∈ T, ∀ k ∈ S, k ∉ T → ⟪u j, u k⟫_ℂ = 0) :
    finiteGramCoordinate u i S = finiteGramCoordinate u i T := by
  classical
  have hS := finiteGramCoordinate_isGreatest hu i S
  have hT' := finiteGramCoordinate_isGreatest hu i T
  apply le_antisymm
  · obtain ⟨c, hc, hval⟩ := hS.1
    let d := c.filter (· ∈ T)
    let b := c.filter (· ∉ T)
    let L := Finsupp.linearCombination ℂ u
    have hd : d.support ⊆ T := fun j hj ↦ (Finset.mem_filter.mp hj).2
    have hdis : ⟪L d, L b⟫_ℂ = 0 := by
      simp only [L, Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum]
      apply Finset.sum_eq_zero fun k hk ↦ Finset.sum_eq_zero fun j hj ↦ ?_
      have hk' := Finset.mem_filter.mp (show k ∈ c.support.filter (· ∉ T) from hk)
      rw [inner_smul_left, inner_smul_right, hoff j (hd hj) k (hc hk'.1) hk'.2, mul_zero, mul_zero]
    have hsum : L d + L b = L c := by
      rw [← map_add, show d + b = c from c.filter_add_filter_not _]
    have hnorm : ‖L d‖ ≤ ‖L c‖ := by
      have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L d) (L b) hdis
      rw [hsum] at h
      nlinarith [norm_nonneg (L c), norm_nonneg (L d), sq_nonneg ‖L b‖]
    have hdi : d i = c i := c.filter_apply_pos _ hi
    have hmax : ‖c i‖ / ‖L d‖ ≤ finiteGramCoordinate u i T := hdi ▸ hT'.2 ⟨d, hd, rfl⟩
    change ‖c i‖ / ‖L c‖ = finiteGramCoordinate u i S at hval
    rw [← hval]
    apply le_trans _ hmax
    by_cases hz : L d = 0
    · have hd0 := linearIndependent_iff.mp hu d hz
      simp [← hdi, hd0]
    · exact div_le_div_of_nonneg_left (norm_nonneg _) (norm_pos_iff.mpr hz) hnorm
  · obtain ⟨c, hc, hval⟩ := hT'.1
    exact hS.2 ⟨c, hc.trans hT, hval⟩

end RiemannMasullo
