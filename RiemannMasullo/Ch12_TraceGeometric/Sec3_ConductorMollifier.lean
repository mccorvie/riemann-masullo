module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_CylinderPlancherel
public import RiemannMasullo.Ch13_ZerosHecke.DirichletZeroDisplacement
public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.FiniteMobiusPolynomial
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

/-! # Character means for the ordinary Möbius mollifier

Splitting a Dirichlet L-function after one complete period gives an Abel
remainder with a bounded coefficient at each residue. Character orthogonality
controls both that error and the product of the finite truncation with the
Möbius mollifier, including frequencies above the modulus.
-/

@[expose] public noncomputable section

open Classical Filter Set MeasureTheory
open scoped Topology Asymptotics

section
open Finset
namespace RiemannMasullo.ConductorCylinder
open RationalConductor

/-- Character orthogonality with residue collisions. A set of frequencies up
to `qL` costs at most `L+1` in mean square, uniformly through composite moduli. -/
theorem character_polynomial_mean_sq_le (q : ℕ) [NeZero q] (S : Finset ℕ) (A : ℕ → ℂ)
    (L : ℕ) (hL : ∀ n ∈ S, n ≤ q*L) :
    (∑ χ : DirichletCharacter ℂ q, ‖∑ n ∈ S, A n * χ (n : ZMod q)‖^2) / q.totient ≤
      (L+1:ℕ) * ∑ n ∈ S, ‖A n‖^2 := by
  let V (χ : DirichletCharacter ℂ q) := ∑ n ∈ S, A n * χ (n : ZMod q)
  let T (r : (ZMod q)ˣ) := S.filter (fun n : ℕ ↦ (r : ZMod q) = (n : ZMod q))
  have hV : V = ∑ n ∈ S, A n • (fun χ : DirichletCharacter ℂ q ↦ χ (n : ZMod q)) := by
    ext χ; simp [V]
  have he (r : (ZMod q)ˣ) : cylinderAverage q r V = ∑ n ∈ T r, A n := by
    rw [hV, map_sum]
    simp only [map_smul, cylinderAverage_eval, smul_eq_mul, mul_ite, mul_one, mul_zero, T, Finset.sum_filter]
  have hcard (r : (ZMod q)ˣ) : (T r).card ≤ L+1 := by
    have hmem (n : ℕ) (hn : n ∈ T r) : n / q ∈ Finset.range (L+1) := by
      rw [Finset.mem_range]
      have h := hL n (Finset.mem_filter.mp hn).1
      apply Nat.lt_succ_of_le
      exact (Nat.div_le_div_right h).trans_eq (Nat.mul_div_cancel_left L (NeZero.pos q))
    have hi : Set.InjOn (fun n : ℕ ↦ n/q) ↑(T r) := by
      intro m hm n hn hh
      have hm' := (Finset.mem_filter.mp hm).2
      have hn' := (Finset.mem_filter.mp hn).2
      have hmod := (ZMod.natCast_eq_natCast_iff' m n q).mp (hm'.symm.trans hn')
      calc m = m%q + q*(m/q) := (Nat.mod_add_div m q).symm
           _ = n := by rw [hmod, show m/q=n/q from hh, Nat.mod_add_div]
    exact (Finset.card_le_card_of_injOn _ hmem hi).trans_eq (Finset.card_range _)
  have hrow (r : (ZMod q)ˣ) : ‖∑ n ∈ T r, A n‖^2 ≤ (L+1:ℕ)*∑ n ∈ T r, ‖A n‖^2 := calc
    _ ≤ (∑ n ∈ T r, ‖A n‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le ..) 2
    _ ≤ ((T r).card : ℝ)*∑ n ∈ T r, ‖A n‖^2 := sq_sum_le_card_mul_sum_sq
    _ ≤ _ := by gcongr; exact hcard r
  change (∑ χ, ‖V χ‖^2) / _ ≤ _
  rw [← sum_norm_sq_cylinderAverage]
  simp_rw [he]
  apply (Finset.sum_le_sum (fun r _ ↦ hrow r)).trans
  rw [← Finset.mul_sum]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  simp only [T, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro n _
  by_cases hn : IsUnit (n : ZMod q)
  · obtain ⟨r,hr⟩ := hn
    rw [← hr]
    simp [Units.val_inj]
  · have he (r : (ZMod q)ˣ) : (r : ZMod q) ≠ (n : ZMod q) := fun h ↦ hn (h ▸ r.isUnit)
    simp [he]

end RiemannMasullo.ConductorCylinder

end

namespace RiemannMasullo.ConductorCylinder

private def abelKernel (s : ℂ) (x : ℝ) : ℂ := (x : ℂ)^(-(s+1))

private theorem kernel_integrable {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (abelKernel s) (Ioi c) := integrableOn_Ioi_cpow_of_lt (by simpa using neg_lt_neg (lt_add_of_pos_left 1 hs)) hc

private theorem bounded_kernel_integrable {s : ℂ} (hs : 0 < s.re) {c : ℝ} (hc : 0 < c)
    (A : ℝ → ℂ) (hm : Measurable A) (B : ℝ) (hb : ∀ x, ‖A x‖ ≤ B) :
    IntegrableOn (fun x ↦ A x * abelKernel s x) (Ioi c) := by
  have hi := ((kernel_integrable hs hc).norm).const_mul B
  have hk : Measurable (abelKernel s) := by unfold abelKernel; fun_prop
  apply hi.mono' (hm.mul hk).aestronglyMeasurable
  filter_upwards with x
  simpa only [Pi.mul_apply,norm_mul] using mul_le_mul_of_nonneg_right (hb x) (norm_nonneg (abelKernel s x))

private def residueTail (q j : ℕ) (s : ℂ) : ℂ :=
  s * ∫ x in Ioi (q : ℝ), if j ≤ ⌊x⌋₊ % q then abelKernel s x else 0

private theorem tail_integrable {q : ℕ} [NeZero q] (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ ↦ if j ≤ ⌊x⌋₊%q then abelKernel s x else 0) (Ioi (q:ℝ)) := by
  have hm : MeasurableSet {x : ℝ | j ≤ ⌊x⌋₊%q} :=
    ((measurable_of_countable (fun n : ℕ ↦ n%q)).comp measurable_id.nat_floor) ((Set.Ici j).to_countable.measurableSet)
  have he : ({x : ℝ | j ≤ ⌊x⌋₊%q}.indicator (abelKernel s)) =
      (fun x : ℝ ↦ if j ≤ ⌊x⌋₊%q then abelKernel s x else 0) := by
    funext x
    by_cases h : j ≤ ⌊x⌋₊%q <;> simp [Set.indicator,h]
  rw [← he]
  exact (kernel_integrable hs (Nat.cast_pos.mpr (NeZero.pos q))).indicator hm

private theorem norm_residueTail (q : ℕ) [NeZero q] (j : ℕ) {s : ℂ} (hs : 0 < s.re) :
    ‖residueTail q j s‖ ≤ ‖s‖ * ((q : ℝ)^(-s.re) / s.re) := by
  have hq := Nat.cast_pos (α := ℝ).mpr (NeZero.pos q)
  rw [residueTail,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  refine (norm_integral_le_integral_norm _).trans ?_
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -(s.re+1) < -1) hq
  calc _ ≤ ∫ x : ℝ in Ioi (q:ℝ), x^(-(s.re+1)) := by
          apply setIntegral_mono_on (tail_integrable j hs).norm hi measurableSet_Ioi
          intro x hx
          have hx' := hq.trans hx
          split_ifs
          · rw [abelKernel, Complex.norm_cpow_eq_rpow_re_of_pos hx']; simp
          · simp [Real.rpow_nonneg hx'.le]
       _ = _ := by
          rw [integral_Ioi_rpow_of_lt (by linarith) hq]
          ring_nf

private theorem partial_sum_bound (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (n : ℕ) : ‖∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)‖ ≤ (q:ℝ) := by
  rw [dirichletCharacter_partial_sum_mod χ hχ n]
  apply (norm_sum_le ..).trans
  calc _ ≤ ∑ _ ∈ Finset.Icc 1 (n%q), (1:ℝ) := Finset.sum_le_sum (fun _ _ ↦ χ.norm_le_one _)
       _ ≤ _ := by simp; exact_mod_cast (Nat.mod_lt n (NeZero.pos q)).le

/-- Above real part zero, the error after one full period is a finite
character polynomial. Each coefficient is bounded by `|s| q^(-Re s)/Re s`
because complete nonprincipal periods sum to zero. -/
theorem conductorTruncation_abel_error {q : ℕ} [NeZero q] (s : ℂ) (hs : 0 < s.re) :
    ∃ A : ℕ → ℂ, (∀ j, ‖A j‖ ≤ ‖s‖*((q:ℝ)^(-s.re)/s.re)) ∧
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        χ.LFunction s - conductorTruncation χ q s = ∑ j ∈ Finset.Icc 1 q, A j * χ (j : ZMod q) := by
  refine ⟨fun j ↦ residueTail q j s,fun j ↦ norm_residueTail q j hs,?_⟩
  intro χ hχ
  let f (n : ℕ) := if n ≤ q then χ (n : ZMod q) else 0
  let P (n : ℕ) := ∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)
  let Q (n : ℕ) := ∑ j ∈ Finset.Icc 1 n, f j
  have htr (n : ℕ) : Q n = P (min n q) := by
    simp only [Q,P,f,← Finset.sum_filter]
    congr 1; ext k; simp only [Finset.mem_filter,Finset.mem_Icc,le_min_iff]; tauto
  have normtr (n : ℕ) : ∑ j ∈ Finset.Icc 1 n, ‖f j‖ ≤ (q:ℝ) := by
    calc _ ≤ ∑ j ∈ Finset.Icc 1 n, if j≤q then (1:ℝ) else 0 := by
            apply Finset.sum_le_sum; intro j _; dsimp [f]; split_ifs <;> first | exact χ.norm_le_one _ | simp
         _ = ∑ _ ∈ Finset.Icc 1 (min n q), (1:ℝ) := by
            rw [← Finset.sum_filter]
            congr 1; ext k; simp only [Finset.mem_filter,Finset.mem_Icc,le_min_iff]; tauto
         _ ≤ _ := by simp
  have hO : (fun n : ℕ ↦ ∑ j ∈ Finset.Icc 1 n, ‖f j‖) =O[atTop] (fun n : ℕ ↦ (n:ℝ)^(0:ℝ)) :=
    Asymptotics.isBigO_iff.mpr ⟨q,Eventually.of_forall (fun n ↦ by
      simpa only [Real.rpow_zero,norm_one,mul_one,Real.norm_of_nonneg (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))] using normtr n)⟩
  have hP := dirichletLFunction_eq_abelIntegral χ hχ (partial_sum_bound q χ hχ) hs
  have hQ := LSeries_eq_mul_integral' f le_rfl hs hO
  have hD : LSeries f s = conductorTruncation χ q s := by
    unfold LSeries conductorTruncation conductorPolynomial
    rw [tsum_eq_sum (s := Finset.Icc 1 q)]
    · apply Finset.sum_congr rfl
      intro n hn
      have hn₀ := (Finset.mem_Icc.mp hn).1
      simp [LSeries.term,f,(Finset.mem_Icc.mp hn).2, show n≠0 by omega, Complex.cpow_neg, div_eq_mul_inv]
    · intro n hn
      by_cases h : n=0
      · simp [h,LSeries.term]
      · have hN : ¬n≤q := fun hn' ↦ hn (Finset.mem_Icc.mpr ⟨by omega,hn'⟩)
        simp [LSeries.term,f,hN]
  have hq0 : P q = 0 := by dsimp only [P]; rw [dirichletCharacter_partial_sum_mod χ hχ q]; simp
  have hker (W : ℕ → ℂ) (hW : ∀ n, ‖W n‖ ≤ q) :
      IntegrableOn (fun x : ℝ ↦ W ⌊x⌋₊ * abelKernel s x) (Ioi 1) :=
    bounded_kernel_integrable hs zero_lt_one _ ((measurable_of_countable W).comp measurable_id.nat_floor) _ (fun _ ↦ hW _)
  let B (x : ℝ) := (P ⌊x⌋₊-Q ⌊x⌋₊)*abelKernel s x
  have hind : B = (Ioi (q:ℝ)).indicator (fun x ↦ P ⌊x⌋₊ * abelKernel s x) := by
    funext x
    by_cases hx : (q:ℝ) < x
    · have hn : q ≤ ⌊x⌋₊ := Nat.le_floor hx.le
      simp [B,htr,min_eq_right hn,hq0,Set.indicator_of_mem (show x ∈ Ioi (q:ℝ) from hx)]
    · have hn : ⌊x⌋₊ ≤ q := (Nat.floor_mono (le_of_not_gt hx)).trans_eq (Nat.floor_natCast q)
      simp [B,htr,min_eq_left hn,Set.indicator_of_notMem (show x ∉ Ioi (q:ℝ) from hx)]
  have hsub := Set.Ioi_subset_Ioi (show (1:ℝ) ≤ q by exact_mod_cast NeZero.pos q)
  calc χ.LFunction s - conductorTruncation χ q s = s*∫ x : ℝ in Ioi 1, B x := by
          rw [← hD,hP,hQ,← mul_sub]
          change s*((∫ x : ℝ in Ioi 1, P ⌊x⌋₊*abelKernel s x) -
            ∫ x : ℝ in Ioi 1, Q ⌊x⌋₊*abelKernel s x) = _
          rw [← integral_sub (hker P (partial_sum_bound q χ hχ))
            (hker Q (fun n ↦ htr n ▸ partial_sum_bound q χ hχ _))]
          congr 1; apply setIntegral_congr_fun measurableSet_Ioi; intro x _
          dsimp only [B,P,Q,abelKernel]; ring
       _ = s*∫ x : ℝ in Ioi (q:ℝ), P ⌊x⌋₊ * abelKernel s x := by
          rw [hind,integral_indicator measurableSet_Ioi, Measure.restrict_restrict_of_subset hsub]
       _ = _ := by
          have hex (n : ℕ) : P n = ∑ j ∈ Finset.Icc 1 q, if j≤n%q then χ (j : ZMod q) else 0 := by
            dsimp only [P]
            rw [dirichletCharacter_partial_sum_mod χ hχ n,← Finset.sum_filter]
            congr 1; ext j; simp only [Finset.mem_filter,Finset.mem_Icc]
            have := Nat.mod_lt n (NeZero.pos q); omega
          simp_rw [hex, Finset.sum_mul, ite_mul,zero_mul]
          rw [integral_finsetSum]
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro j _
            rw [residueTail]
            rw [show (fun x : ℝ ↦ if j ≤ ⌊x⌋₊ % q then χ (j : ZMod q) * abelKernel s x else 0) =
              (fun x : ℝ ↦ χ (j : ZMod q) * (if j ≤ ⌊x⌋₊ % q then abelKernel s x else 0)) by funext x; split_ifs <;> simp]
            rw [integral_const_mul]; ring
          · intro j _
            simpa only [mul_ite,mul_zero] using (tail_integrable j hs).const_mul (χ (j : ZMod q))

end RiemannMasullo.ConductorCylinder
