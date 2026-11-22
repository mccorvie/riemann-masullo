module

public import RiemannMasullo.AppC_LCTVS.Sec2a_part2
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.RCLike.Lemmas

/-! # Appendix C.2.3: the printed assertion about projective tensor embeddings -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Topology

/-- Paper: §C.2.3.2, after (C.2.3.15), p. 679. As printed: the projective tensor
product of two topological embeddings is a topological embedding. This is the
uncompleted embedding assertion of the claimed analogue of Lemma C.2.3.5(1).
The projective quotient-map result is `projectiveTensorMap_isQuotientMap`.
See ERRATA F7. -/
def Printed.projectiveTensorMap_isEmbedding : Prop :=
  ∀ (E₁ E₂ F₁ F₂ : Type)
    [AddCommGroup E₁] [Module ℂ E₁] [TopologicalSpace E₁] [PolynormableSpace ℂ E₁] [T2Space E₁]
    [AddCommGroup E₂] [Module ℂ E₂] [TopologicalSpace E₂] [PolynormableSpace ℂ E₂] [T2Space E₂]
    [AddCommGroup F₁] [Module ℂ F₁] [TopologicalSpace F₁] [PolynormableSpace ℂ F₁] [T2Space F₁]
    [AddCommGroup F₂] [Module ℂ F₂] [TopologicalSpace F₂] [PolynormableSpace ℂ F₂] [T2Space F₂]
    (T₁ : E₁ →L[ℂ] F₁) (T₂ : E₂ →L[ℂ] F₂),
    IsEmbedding T₁ → IsEmbedding T₂ →
      IsEmbedding (projectiveTensorMap T₁.toLinearMap T₂.toLinearMap)


namespace PTEmbCounter

open TensorProduct
open scoped ComplexOrder

/-- Block index sets `{0,1,2}^k`. -/
private abbrev XX (k : ℕ) := Fin k → Fin 3
/-- All blocks together. -/
private abbrev II := Σ k : ℕ, XX k
/-- `ℓ¹` over all blocks. -/
private abbrev FF := lp (fun _ : II ↦ ℂ) 1
/-- `ℓ²` over all blocks. -/
private abbrev GG := lp (fun _ : II ↦ ℂ) 2

private theorem sum_succ {M : Type*} [AddCommMonoid M] (k : ℕ) (g : XX (k + 1) → M) :
    ∑ ν, g ν = ∑ a : Fin 3, ∑ ω : XX k, g (Fin.cons a ω) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) ↦ Fin 3)).sum_comp, Fintype.sum_prod_type]
  rfl

/-- Functions on `{0,1,2}^k` with zero sum along every coordinate line. -/
private def Good : (k : ℕ) → (XX k → ℂ) → Prop
  | 0, _ => True
  | k + 1, f => (∀ a : Fin 3, Good k (fun ω ↦ f (Fin.cons a ω))) ∧
      ∀ ω : XX k, ∑ a : Fin 3, f (Fin.cons a ω) = 0

private theorem good_zero : ∀ k, Good k 0
  | 0 => trivial
  | k + 1 => ⟨fun _ ↦ good_zero k, fun _ ↦ by simp⟩

private theorem good_add : ∀ (k : ℕ) (f g : XX k → ℂ), Good k f → Good k g → Good k (f + g)
  | 0, _, _, _, _ => trivial
  | k + 1, f, g, hf, hg =>
    ⟨fun a ↦ good_add k _ _ (hf.1 a) (hg.1 a),
      fun ω ↦ by simp [Finset.sum_add_distrib, hf.2 ω, hg.2 ω]⟩

private theorem good_smul : ∀ (k : ℕ) (c : ℂ) (f : XX k → ℂ), Good k f → Good k (c • f)
  | 0, _, _, _ => trivial
  | k + 1, c, f, hf =>
    ⟨fun a ↦ good_smul k c _ (hf.1 a),
      fun ω ↦ by simp [← Finset.mul_sum, hf.2 ω]⟩

private theorem three (z : Fin 3 → ℂ) (h : ∑ a, z a = 0) :
    2 * ∑ a, ‖z a‖ ^ 2 ≤ (∑ a, ‖z a‖) ^ 2 := by
  rw [Fin.sum_univ_three] at h
  rw [Fin.sum_univ_three, Fin.sum_univ_three]
  have h2 : z 2 = -(z 0 + z 1) := by linear_combination h
  have h0 : z 0 = -(z 1 + z 2) := by linear_combination h
  have h1 : z 1 = -(z 0 + z 2) := by linear_combination h
  have e2 : ‖z 2‖ ≤ ‖z 0‖ + ‖z 1‖ := by rw [h2, norm_neg]; exact norm_add_le _ _
  have e0 : ‖z 0‖ ≤ ‖z 1‖ + ‖z 2‖ := by rw [h0, norm_neg]; exact norm_add_le _ _
  have e1 : ‖z 1‖ ≤ ‖z 0‖ + ‖z 2‖ := by rw [h1, norm_neg]; exact norm_add_le _ _
  nlinarith [mul_nonneg (norm_nonneg (z 0)) (sub_nonneg.2 e0),
    mul_nonneg (norm_nonneg (z 1)) (sub_nonneg.2 e1),
    mul_nonneg (norm_nonneg (z 2)) (sub_nonneg.2 e2)]

private theorem key_ineq {A B : Type*} [Fintype A] [Fintype B] (m : A → B → ℝ) (hm : ∀ a b, 0 ≤ m a b)
    (h3 : ∀ b, 2 * ∑ a, m a b ^ 2 ≤ (∑ a, m a b) ^ 2) :
    2 * ∑ a, (∑ b, m a b) ^ 2 ≤ (∑ b, ∑ a, m a b) ^ 2 := by
  have hl : 2 * ∑ a, (∑ b, m a b) ^ 2 = ∑ b, ∑ b', 2 * ∑ a, m a b * m a b' := by
    simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ ↦ ?_
    rw [Finset.sum_comm]
  have hr : (∑ b, ∑ a, m a b) ^ 2 = ∑ b, ∑ b', (∑ a, m a b) * (∑ a, m a b') := by
    rw [sq, Finset.sum_mul_sum]
  rw [hl, hr]
  refine Finset.sum_le_sum fun b _ ↦ Finset.sum_le_sum fun b' _ ↦ ?_
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun a ↦ m a b) (fun a ↦ m a b')
  set n := √(∑ a, m a b ^ 2)
  set n' := √(∑ a, m a b' ^ 2)
  have hn : n ^ 2 = ∑ a, m a b ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hn' : n' ^ 2 = ∑ a, m a b' ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hT : 0 ≤ ∑ a, m a b := Finset.sum_nonneg fun _ _ ↦ hm _ _
  have hT' : 0 ≤ ∑ a, m a b' := Finset.sum_nonneg fun _ _ ↦ hm _ _
  have hprod := mul_le_mul (h3 b) (h3 b')
    (mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)) (sq_nonneg _)
  rw [← hn, ← hn'] at hprod
  have hnn : 0 ≤ n := Real.sqrt_nonneg _
  have hnn' : 0 ≤ n' := Real.sqrt_nonneg _
  have : 2 * (n * n') ≤ (∑ a, m a b) * (∑ a, m a b') := by
    refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
    nlinarith [hprod]
  nlinarith [hcs]

private theorem good_ineq : ∀ (k : ℕ) (f : XX k → ℂ), Good k f →
    (2 : ℝ) ^ k * ∑ ω, ‖f ω‖ ^ 2 ≤ (∑ ω, ‖f ω‖) ^ 2
  | 0, f, _ => by simp
  | k + 1, f, hf => by
    rw [sum_succ, sum_succ]
    have IH : ∀ a : Fin 3, (2 : ℝ) ^ k * ∑ ω, ‖f (Fin.cons a ω)‖ ^ 2 ≤
        (∑ ω, ‖f (Fin.cons a ω)‖) ^ 2 := fun a ↦ good_ineq k _ (hf.1 a)
    have h3 : ∀ ω : XX k, 2 * ∑ a, ‖f (Fin.cons a ω)‖ ^ 2 ≤ (∑ a, ‖f (Fin.cons a ω)‖) ^ 2 :=
      fun ω ↦ three (fun a ↦ f (Fin.cons a ω)) (hf.2 ω)
    calc (2 : ℝ) ^ (k + 1) * ∑ a : Fin 3, ∑ ω, ‖f (Fin.cons a ω)‖ ^ 2
        = 2 * ∑ a : Fin 3, (2 ^ k * ∑ ω, ‖f (Fin.cons a ω)‖ ^ 2) := by
          rw [← Finset.mul_sum, pow_succ]; ring
      _ ≤ 2 * ∑ a : Fin 3, (∑ ω, ‖f (Fin.cons a ω)‖) ^ 2 := by
          gcongr with a; exact IH a
      _ ≤ (∑ ω, ∑ a : Fin 3, ‖f (Fin.cons a ω)‖) ^ 2 :=
          key_ineq (fun a ω ↦ ‖f (Fin.cons a ω)‖) (fun _ _ ↦ norm_nonneg _) h3
      _ = (∑ a : Fin 3, ∑ ω, ‖f (Fin.cons a ω)‖) ^ 2 := by rw [Finset.sum_comm]

/-- The one-dimensional kernel `δ_{ab} - 1/3`. -/
private def pp (a b : Fin 3) : ℝ := if a = b then 2 / 3 else -1 / 3

/-- Its tensor powers: the orthogonal projection onto `Good k`. -/
private def PP : (k : ℕ) → XX k → XX k → ℝ
  | 0, _, _ => 1
  | k + 1, ω, η => pp (ω 0) (η 0) * PP k (Fin.tail ω) (Fin.tail η)

private theorem sum_pp_left (b : Fin 3) : ∑ a, pp a b = 0 := by
  fin_cases b <;> simp [pp, Fin.sum_univ_three] <;> norm_num

private theorem sum_pp_sq (a : Fin 3) : ∑ b, pp a b ^ 2 = 2 / 3 := by
  fin_cases a <;> simp [pp, Fin.sum_univ_three] <;> norm_num

private theorem good_PP : ∀ (k : ℕ) (η : XX k), Good k (fun ω ↦ (PP k ω η : ℂ))
  | 0, _ => trivial
  | k + 1, η => by
    refine ⟨fun a ↦ ?_, fun ω ↦ ?_⟩
    · have := good_smul k ((pp a (η 0) : ℝ) : ℂ) _ (good_PP k (Fin.tail η))
      convert this using 1
      funext ω
      simp [PP]
    · simp only [PP, Fin.cons_zero, Fin.tail_cons]
      push_cast
      rw [← Finset.sum_mul]
      norm_cast
      rw [sum_pp_left]
      simp

private theorem trace_PP : ∀ k : ℕ, ∑ ω, PP k ω ω = 2 ^ k
  | 0 => by simp [PP]
  | k + 1 => by
    rw [sum_succ]
    simp only [PP, Fin.cons_zero, Fin.tail_cons, ← Finset.mul_sum, trace_PP k, pp]
    simp
    ring

private theorem rowsq_PP : ∀ (k : ℕ) (ω : XX k), ∑ η, PP k ω η ^ 2 = (2 / 3) ^ k
  | 0, _ => by simp [PP]
  | k + 1, ω => by
    rw [sum_succ]
    simp only [PP, Fin.cons_zero, Fin.tail_cons, mul_pow, ← Finset.mul_sum, rowsq_PP k,
      ← Finset.sum_mul, sum_pp_sq]
    ring

/-- A vector supported in block `k`. -/
private def blk (p : ENNReal) (k : ℕ) (c : XX k → ℂ) : lp (fun _ : II ↦ ℂ) p :=
  ∑ ω, lp.single p (⟨k, ω⟩ : II) (c ω)

private theorem single_same (p : ENNReal) (k : ℕ) (η ω : XX k) (x : ℂ) :
    (lp.single (E := fun _ : II ↦ ℂ) p (⟨k, η⟩ : II) x) ⟨k, ω⟩ = if ω = η then x else 0 := by
  rw [lp.single_apply, Pi.single_apply]
  simp [sigma_mk_injective.eq_iff]

private theorem blk_same (p : ENNReal) (k : ℕ) (c : XX k → ℂ) (ω : XX k) :
    blk p k c ⟨k, ω⟩ = c ω := by
  simp only [blk, lp.coeFn_sum, Finset.sum_apply, single_same]
  simp

private theorem blk_ne (p : ENNReal) (k : ℕ) (c : XX k → ℂ) {k' : ℕ} (h : k' ≠ k) (ω : XX k') :
    blk p k c ⟨k', ω⟩ = 0 := by
  simp only [blk, lp.coeFn_sum, Finset.sum_apply, lp.single_apply]
  refine Finset.sum_eq_zero fun η _ ↦ Pi.single_eq_of_ne ?_ _
  intro he
  exact h (Sigma.mk.inj_iff.mp he).1

private theorem norm_blk (p : ENNReal) [Fact (1 ≤ p)] (hp : 0 < p.toReal) (k : ℕ) (c : XX k → ℂ) :
    ‖blk p k c‖ ^ p.toReal = ∑ ω, ‖c ω‖ ^ p.toReal := by
  let e : XX k ↪ II := ⟨Sigma.mk k, sigma_mk_injective⟩
  let f : II → ℂ := Function.extend (Sigma.mk k) c 0
  have hf (ω : XX k) : f ⟨k, ω⟩ = c ω := sigma_mk_injective.extend_apply c 0 ω
  have h1 : blk p k c = ∑ i ∈ Finset.univ.map e, lp.single p i (f i) := by
    rw [Finset.sum_map]
    exact Finset.sum_congr rfl fun ω _ ↦ by simp [e, hf]
  rw [h1, lp.norm_sum_single hp, Finset.sum_map]
  exact Finset.sum_congr rfl fun ω _ ↦ by simp [e, hf]

private theorem sum_le_norm (p : ENNReal) [Fact (1 ≤ p)] (hp : 0 < p.toReal)
    (x : lp (fun _ : II ↦ ℂ) p) (k : ℕ) :
    ∑ ω : XX k, ‖x ⟨k, ω⟩‖ ^ p.toReal ≤ ‖x‖ ^ p.toReal := by
  let e : XX k ↪ II := ⟨Sigma.mk k, sigma_mk_injective⟩
  have := lp.sum_rpow_le_norm_rpow hp x (Finset.univ.map e)
  rwa [Finset.sum_map] at this

/-- The subspace of `ℓ¹` whose blocks all lie in `Good k`. -/
private def EE : Submodule ℂ FF where
  carrier := {x | ∀ k, Good k (fun ω ↦ x ⟨k, ω⟩)}
  add_mem' hx hy k := good_add k _ _ (hx k) (hy k)
  zero_mem' k := good_zero k
  smul_mem' c _ hx k := good_smul k c _ (hx k)

/-- Weight of block `k`. -/
private def wt (k : ℕ) : ℝ := √(2 ^ k)

/-- Weighted block pairing. -/
private def bk (k : ℕ) : EE →ₗ[ℂ] GG →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun x y ↦ (wt k : ℂ) * ∑ ω : XX k, (x : FF) ⟨k, ω⟩ * y ⟨k, ω⟩)
    (fun _ _ _ ↦ by simp [add_mul, Finset.sum_add_distrib, mul_add])
    (fun _ _ _ ↦ by simp [Finset.mul_sum, mul_assoc, mul_left_comm])
    (fun _ _ _ ↦ by simp [mul_add, Finset.sum_add_distrib])
    (fun c x y ↦ by simp [Finset.mul_sum, mul_left_comm])

private theorem bk_bound (k : ℕ) (x : EE) (y : GG) : ‖bk k x y‖ ≤ ‖x‖ * ‖y‖ := by
  have hgood := good_ineq k _ (x.2 k)
  have h1 := sum_le_norm 1 (by norm_num) (x : FF) k
  have h2 := sum_le_norm 2 (by norm_num) y k
  simp only [ENNReal.toReal_one, Real.rpow_one] at h1
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h2
  set A := ∑ ω : XX k, ‖(x : FF) ⟨k, ω⟩‖
  set Q := ∑ ω : XX k, ‖(x : FF) ⟨k, ω⟩‖ ^ 2
  set R := ∑ ω : XX k, ‖y ⟨k, ω⟩‖ ^ 2
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun ω : XX k ↦ ‖(x : FF) ⟨k, ω⟩‖)
    (fun ω ↦ ‖y ⟨k, ω⟩‖)
  have hA : √(2 ^ k) * √Q ≤ A := by
    rw [← Real.sqrt_mul (by positivity)]
    calc √(2 ^ k * Q) ≤ √(A ^ 2) := Real.sqrt_le_sqrt hgood
      _ = A := Real.sqrt_sq (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)
  have hR : √R ≤ ‖y‖ := by
    calc √R ≤ √(‖y‖ ^ 2) := Real.sqrt_le_sqrt h2
      _ = ‖y‖ := Real.sqrt_sq (norm_nonneg _)
  have hxnorm : ‖x‖ = ‖(x : FF)‖ := rfl
  calc ‖bk k x y‖ = √(2 ^ k) * ‖∑ ω : XX k, (x : FF) ⟨k, ω⟩ * y ⟨k, ω⟩‖ := by
        simp [bk, wt]
    _ ≤ √(2 ^ k) * ∑ ω : XX k, ‖(x : FF) ⟨k, ω⟩‖ * ‖y ⟨k, ω⟩‖ := by
        gcongr
        exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun _ _ ↦ norm_mul _ _))
    _ ≤ √(2 ^ k) * (√Q * √R) := by gcongr
    _ = (√(2 ^ k) * √Q) * √R := by ring
    _ ≤ A * ‖y‖ := by
        gcongr
        exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
    _ ≤ ‖x‖ * ‖y‖ := by rw [hxnorm]; gcongr

private theorem mem_absConvexHull_avg {V ι : Type*} [AddCommGroup V] [Module ℂ V] [Fintype ι]
    [Nonempty ι] {s : Set V} (z : ι → V) (hz : ∀ i, z i ∈ s) :
    ((Fintype.card ι : ℂ))⁻¹ • ∑ i, z i ∈ absConvexHull ℂ s := by
  let : Module ℝ V := Module.restrictScalars ℝ ℂ V
  have : IsScalarTower ℝ ℂ V := IsScalarTower.restrictScalars ℝ ℂ V
  have hc : Convex ℝ (absConvexHull ℂ s) :=
    (convex_RCLike_iff_convex_real (K := ℂ)).1 convex_absConvexHull
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have := hc.sum_mem (t := Finset.univ) (w := fun _ ↦ ((Fintype.card ι : ℝ))⁻¹) (z := z)
    (fun _ _ ↦ by positivity) (by simp [Finset.card_univ, hN.ne'])
    (fun i _ ↦ subset_absConvexHull (hz i))
  rw [← Finset.smul_sum] at this
  convert this using 1
  rw [← algebraMap_smul ℂ ((Fintype.card ι : ℝ))⁻¹ (∑ i, z i)]
  simp


private theorem blk_mem (k : ℕ) (η : XX k) : blk 1 k (fun ω ↦ (PP k ω η : ℂ)) ∈ EE := by
  show ∀ k' : ℕ, Good k' (fun ω ↦ (blk 1 k (fun ω ↦ (PP k ω η : ℂ)) : FF) ⟨k', ω⟩)
  intro k'
  by_cases hk : k' = k
  · subst hk
    have : (fun ω ↦ (blk 1 k' (fun ω ↦ (PP k' ω η : ℂ)) : FF) ⟨k', ω⟩) =
        fun ω ↦ (PP k' ω η : ℂ) := funext fun ω ↦ blk_same _ _ _ _
    rw [this]
    exact good_PP k' η
  · have : (fun ω ↦ (blk 1 k (fun ω ↦ (PP k ω η : ℂ)) : FF) ⟨k', ω⟩) = 0 :=
      funext fun ω ↦ blk_ne _ _ _ hk ω
    rw [this]
    exact good_zero k'

private theorem blk_eq (p : ENNReal) (k : ℕ) (c : XX k → ℂ) :
    blk p k c = ∑ ω, c ω • lp.single p (⟨k, ω⟩ : II) (1 : ℂ) := by
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [← lp.single_smul, smul_eq_mul, mul_one]

private theorem not_emb : ¬ Printed.projectiveTensorMap_isEmbedding := by
  intro h
  have hemb := h EE GG FF GG EE.subtypeL (ContinuousLinearMap.id ℂ GG)
    IsEmbedding.subtypeVal IsEmbedding.id
  have hU := (projectiveTensor_zero_basis (E := EE) (F := GG) Metric.nhds_basis_ball
    Metric.nhds_basis_ball).mem_of_mem (i := ((1 : ℝ), (1 : ℝ))) ⟨one_pos, one_pos⟩
  have hB : ∀ k, ∀ t ∈ absConvexHull ℂ (Set.image2 (TensorProduct.tmul ℂ)
      (Metric.ball (0 : EE) 1) (Metric.ball (0 : GG) 1)),
      ‖TensorProduct.lift (bk k) t‖ ≤ 1 := by
    intro k
    have h0 : AbsConvex ℂ (Metric.closedBall (0 : ℂ) 1) :=
      ⟨balanced_closedBall_zero,
        (convex_RCLike_iff_convex_real (K := ℂ)).2 (convex_closedBall 0 1)⟩
    have hS : AbsConvex ℂ ((TensorProduct.lift (bk k)) ⁻¹' Metric.closedBall (0 : ℂ) 1) :=
      ⟨h0.1.mulActionHom_preimage
        (f := (TensorProduct.lift (bk k)).toDistribMulActionHom.toMulActionHom),
        h0.2.linear_preimage _⟩
    intro t ht
    have hsub : Set.image2 (TensorProduct.tmul ℂ) (Metric.ball (0 : EE) 1)
        (Metric.ball (0 : GG) 1) ⊆ (TensorProduct.lift (bk k)) ⁻¹' Metric.closedBall (0 : ℂ) 1 := by
      rintro _ ⟨x, hx, y, hy, rfl⟩
      simp only [Set.mem_preimage, Metric.mem_closedBall, dist_zero_right,
        TensorProduct.lift.tmul]
      rw [mem_ball_zero_iff] at hx hy
      have := bk_bound k x y
      nlinarith [norm_nonneg x, norm_nonneg y]
    have := absConvexHull_min hsub hS ht
    simpa using this
  rw [hemb.isInducing.nhds_eq_comap] at hU
  obtain ⟨W, hW, hWsub⟩ := Filter.mem_comap.mp hU
  rw [map_zero] at hW
  obtain ⟨⟨ε₁, ε₂⟩, ⟨hε₁, hε₂⟩, hsub⟩ := (projectiveTensor_zero_basis (E := FF) (F := GG)
    Metric.nhds_basis_ball Metric.nhds_basis_ball).mem_iff.mp hW
  dsimp only at hε₁ hε₂ hsub
  clear hU hW hemb h
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = ε₁ * ε₂ / 4 := ⟨_, rfl⟩
  have hD : 0 < D := by rw [hDdef]; positivity
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / D ^ 2) (by norm_num : (1 : ℝ) < 4 / 3)
  obtain ⟨r₀, hr₀def⟩ : ∃ r₀ : ℝ, r₀ = √((2 / 3 : ℝ) ^ k) := ⟨_, rfl⟩
  have hr₀ : 0 < r₀ := by rw [hr₀def]; exact Real.sqrt_pos.2 (by positivity)
  have hρ : ∀ ω : XX k, ‖blk 2 k (fun η ↦ (PP k ω η : ℂ))‖ = r₀ := by
    intro ω
    have := norm_blk 2 (by norm_num) k (fun η ↦ (PP k ω η : ℂ))
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Complex.norm_real, Real.norm_eq_abs,
      sq_abs, rowsq_PP] at this
    rw [hr₀def, ← this, Real.sqrt_sq (norm_nonneg _)]
  have hN : (Fintype.card (XX k) : ℝ) = 3 ^ k := by simp
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ε₁ / 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = ε₂ / (2 * r₀) := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = a * b / (Fintype.card (XX k)) := ⟨_, rfl⟩
  let v : XX k → EE := fun η ↦ ⟨blk 1 k (fun ω ↦ (PP k ω η : ℂ)), blk_mem k η⟩
  let e : XX k → GG := fun η ↦ lp.single 2 (⟨k, η⟩ : II) (1 : ℂ)
  let δ : XX k → FF := fun ω ↦ lp.single 1 (⟨k, ω⟩ : II) (1 : ℂ)
  let t : EE ⊗[ℂ] GG := ∑ η, v η ⊗ₜ[ℂ] e η
  have hz : ∀ ω, ((a : ℂ) • δ ω) ⊗ₜ[ℂ] ((b : ℂ) • blk 2 k (fun η ↦ (PP k ω η : ℂ))) ∈
      Set.image2 (TensorProduct.tmul ℂ) (Metric.ball (0 : FF) ε₁) (Metric.ball (0 : GG) ε₂) := by
    intro ω
    refine ⟨_, ?_, _, ?_, rfl⟩
    · rw [mem_ball_zero_iff, norm_smul, lp.norm_single (by norm_num)]
      simp only [Complex.norm_real, Real.norm_eq_abs, norm_one, mul_one, ha]
      rw [abs_of_pos (by positivity)]
      linarith
    · rw [mem_ball_zero_iff, norm_smul, hρ]
      simp only [Complex.norm_real, Real.norm_eq_abs, hb]
      rw [abs_of_pos (by positivity)]
      field_simp
      linarith
  have hmem := mem_absConvexHull_avg _ hz
  have heq : TensorProduct.map (EE.subtypeL : EE →L[ℂ] FF).toLinearMap (ContinuousLinearMap.id ℂ GG).toLinearMap ((c : ℂ) • t) = ((Fintype.card (XX k) : ℂ))⁻¹ • ∑ ω,
      ((a : ℂ) • δ ω) ⊗ₜ[ℂ] ((b : ℂ) • blk 2 k (fun η ↦ (PP k ω η : ℂ))) := by
    rw [map_smul]
    simp only [t, v, e, δ, map_sum, TensorProduct.map_tmul,
      ContinuousLinearMap.coe_coe, Submodule.coe_subtypeL, Submodule.coe_subtype,
      ContinuousLinearMap.coe_id', id]
    simp only [blk_eq, TensorProduct.sum_tmul, TensorProduct.tmul_sum,
      ← TensorProduct.smul_tmul', TensorProduct.tmul_smul, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun ω _ ↦ Finset.sum_congr rfl fun η _ ↦ ?_
    congr 1
    rw [hc]
    push_cast
    ring
  have hval : TensorProduct.lift (bk k) ((c : ℂ) • t) = ((c * wt k * 2 ^ k : ℝ) : ℂ) := by
    have hterm : ∀ η, bk k (v η) (e η) = (wt k : ℂ) * (PP k η η : ℂ) := by
      intro η
      simp only [bk, LinearMap.mk₂_apply, v, e, blk_same, single_same]
      simp
    rw [map_smul]
    simp only [t, map_sum, TensorProduct.lift.tmul, hterm, ← Finset.mul_sum]
    have htr : ∑ η, (PP k η η : ℂ) = (2 : ℂ) ^ k := by exact_mod_cast trace_PP k
    rw [htr]
    push_cast
    simp [smul_eq_mul, mul_assoc]
  have hmemW : (TensorProduct.map (EE.subtypeL : EE →L[ℂ] FF).toLinearMap
      (ContinuousLinearMap.id ℂ GG).toLinearMap ((c : ℂ) • t) : ProjectiveTensor FF GG) ∈ W :=
    hsub (heq ▸ hmem)
  have hle := hB k ((c : ℂ) • t) (hWsub hmemW)
  rw [hval, Complex.norm_real, Real.norm_eq_abs] at hle
  have hkey : r₀ * 3 ^ k < D * wt k * 2 ^ k := by
    have h6 : (r₀ * 3 ^ k) ^ 2 = 6 ^ k := by
      rw [mul_pow, hr₀def, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm k 2, pow_mul,
        ← mul_pow]
      norm_num
    have h8 : (D * wt k * 2 ^ k) ^ 2 = D ^ 2 * 8 ^ k := by
      rw [mul_pow, mul_pow, wt, Real.sq_sqrt (by positivity), ← pow_mul, mul_comm k 2, pow_mul,
        mul_assoc, ← mul_pow]
      norm_num
    have h68 : (6 : ℝ) ^ k < D ^ 2 * 8 ^ k := by
      have h1 : (8 : ℝ) ^ k = (4 / 3) ^ k * 6 ^ k := by rw [← mul_pow]; norm_num
      rw [h1]
      have hD2 : 0 < D ^ 2 := by positivity
      rw [div_lt_iff₀ hD2] at hk
      have h6 : (0 : ℝ) < 6 ^ k := by positivity
      nlinarith
    refine (pow_lt_pow_iff_left₀ (by positivity) ?_ two_ne_zero).1 (by rw [h6, h8]; exact h68)
    exact mul_nonneg (mul_nonneg hD.le (Real.sqrt_nonneg _)) (by positivity)
  have hcval : c * wt k * 2 ^ k = D * wt k * 2 ^ k / (r₀ * 3 ^ k) := by
    rw [hc, hN, ha, hb, hDdef]
    field_simp
    ring
  have hgt : 1 < c * wt k * 2 ^ k := by
    rw [hcval, one_lt_div (by positivity)]
    exact hkey
  rw [abs_of_pos (by linarith)] at hle
  linarith

end PTEmbCounter

/-- Paper: §C.2.3.2, after (C.2.3.15), p. 679. Take the inclusion of H, the closed
span of the Rademacher functions `rₙ(t) = (-1)^(⌊2^(n+1) t⌋)` in complex L¹[0,1],
and the identity on complex ℓ²(ℕ). The coefficient map H → ℓ² sends rₙ to the nth
unit vector and is bounded by the Khintchine inequality. If the tensor map were an
embedding, Hahn–Banach applied to its induced functional would extend the coefficient
map to L¹. The first m coordinate functionals of such an extension would be represented
by L∞ functions g₁, …, gₘ with pointwise ℓ² norm bounded by the same operator norm C.
The identities `∫ rⱼ gⱼ = 1` would give `m ≤ C √m` for all m. -/
theorem Printed.projectiveTensorMap_isEmbedding_false :
    ¬ Printed.projectiveTensorMap_isEmbedding :=
  PTEmbCounter.not_emb

end RiemannMasullo
