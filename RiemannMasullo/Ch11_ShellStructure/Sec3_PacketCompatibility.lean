module

public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-! # Compatibility of two Paley–Wiener packet lifts

For the fixed-box lifting question in (11.3.1.3)–(11.3.1.4), p. 494, this
isolates an obstruction to combining two packet lifts in one preceding stage.
For summable data, the synthesis result verifies the ambient rank-one expansion
from prescribed coordinate functionals and their cardinal lifts, as needed on
p. 496. Nothing imports this file.
-/

public section

open Filter Function Set
open scoped Topology

namespace RiemannMasullo.Isolated

/-- Paper: (11.3.1.3)–(11.3.1.4), p. 494.
Fix a lift of the first packet. A second packet can be realized by the same
stage vector exactly when its discrepancy from the fixed lift is in the range
of the first period difference acting on the second quotient.
Reconstruction: This is the two-packet compatibility condition in one fixed box. -/
theorem packetJointLift_iff
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E Q₁ Q₂ : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Q₁] [NormedSpace 𝕜 Q₁]
    [NormedAddCommGroup Q₂] [NormedSpace 𝕜 Q₂]
    (q₁ : E →L[𝕜] Q₁) (q₂ : E →L[𝕜] Q₂) (hq₂ : Surjective q₂)
    (A : E →L[𝕜] E) (D : Q₂ →L[𝕜] Q₂)
    (hker : q₁.toLinearMap.ker = A.toLinearMap.range) (hcomp : ∀ v, q₂ (A v) = D (q₂ v))
    (x : E) (y : Q₂) :
    (q₁ x, y) ∈ Set.range (fun v ↦ (q₁ v, q₂ v)) ↔ y - q₂ x ∈ Set.range D := by
  constructor
  · rintro ⟨v, hv⟩
    have hmem : v - x ∈ A.toLinearMap.range := by
      rw [← hker, LinearMap.mem_ker, map_sub]
      exact sub_eq_zero.mpr (congrArg Prod.fst hv)
    obtain ⟨u, hu⟩ := hmem
    change A u = v - x at hu
    have hv₂ : q₂ v = y := congrArg Prod.snd hv
    refine ⟨q₂ u, ?_⟩
    rw [← hcomp, hu, map_sub, hv₂]
  · rintro ⟨z, hz⟩
    obtain ⟨u, rfl⟩ := hq₂ z
    have hzero : q₁ (A u) = 0 := by
      change q₁.toLinearMap (A u) = 0
      apply LinearMap.mem_ker.mp
      rw [hker]
      exact ⟨u, rfl⟩
    refine ⟨x + A u, Prod.ext ?_ ?_⟩
    · change q₁ (x + A u) = q₁ x
      rw [map_add, hzero, add_zero]
    · change q₂ (x + A u) = y
      rw [map_add, hcomp, hz, add_comm, sub_add_cancel]

private theorem packetDifference_range_not_isClosed
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {Q : Type*} [NormedAddCommGroup Q] [NormedSpace 𝕜 Q] [CompleteSpace Q]
    (D : Q →L[𝕜] Q) (P : ℕ → Q →L[𝕜] Q) (z : ℕ → Q) (μ : ℕ → 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hz : ∀ n, z n ∈ Set.range D) (hnorm : ∀ n, ‖z n‖ = 1)
    (hfix : ∀ n, P n (z n) = z n) (hmul : ∀ n v, P n (D v) = μ n • P n v)
    (hsmall : ∀ ε > 0, ∃ n, ‖μ n‖ < ε) :
    ¬ IsClosed (Set.range D) := by
  intro hclosed
  let : CompleteSpace D.toLinearMap.range := hclosed.completeSpace_coe
  have hsurj : Surjective D.rangeRestrict := by
    intro y
    obtain ⟨v, hv⟩ := y.property
    exact ⟨v, Subtype.ext hv⟩
  obtain ⟨K, hK, hpre⟩ := D.rangeRestrict.exists_preimage_norm_le hsurj
  have hpos : 0 < C * K + 1 := add_pos_of_nonneg_of_pos (mul_nonneg hC hK.le) zero_lt_one
  obtain ⟨n, hn⟩ := hsmall (1 / (C * K + 1)) (div_pos zero_lt_one hpos)
  obtain ⟨v, hv, hvnorm⟩ := hpre ⟨z n, hz n⟩
  have hv' : D v = z n := congrArg Subtype.val hv
  have hvle : ‖v‖ ≤ K := by
    change ‖v‖ ≤ K * ‖z n‖ at hvnorm
    simpa only [hnorm n, mul_one] using hvnorm
  have hPv : ‖P n v‖ ≤ C * K :=
    ((P n).le_opNorm v).trans (mul_le_mul (hP n) hvle (norm_nonneg v) hC)
  have hone : 1 ≤ ‖μ n‖ * (C * K) := calc
    1 = ‖P n (D v)‖ := by rw [hv', hfix, hnorm]
    _ = ‖μ n‖ * ‖P n v‖ := by rw [hmul, norm_smul]
    _ ≤ ‖μ n‖ * (C * K) := mul_le_mul_of_nonneg_left hPv (norm_nonneg _)
  refine (not_lt_of_ge hone) ?_
  calc
    ‖μ n‖ * (C * K) ≤ ‖μ n‖ * (C * K + 1) :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg _)
    _ < 1 := (lt_div_iff₀ hpos).mp hn

/-- Paper: (11.3.1.3)–(11.3.1.4), p. 494.
In a completed stage with two quotient maps, suppose the kernel of the first map
is a period-difference range. On the second quotient the same difference acts
on uniformly bounded mode projections by multipliers arbitrarily close to zero.
If these modes belong to the difference range, the jointly realizable pairs
form a nonclosed subspace of the product of the two packet quotients.

Reconstruction: This is a test for simultaneous lifting in two packet quotients
with the same preceding fixed box. It applies to the period differences for
two distinct rational primes via the second packet's circle action. -/
theorem packetJointLift_range_not_isClosed
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E Q₁ Q₂ : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup Q₁] [NormedSpace 𝕜 Q₁]
    [NormedAddCommGroup Q₂] [NormedSpace 𝕜 Q₂] [CompleteSpace Q₂]
    (q₁ : E →L[𝕜] Q₁) (q₂ : E →L[𝕜] Q₂) (hq₂ : Surjective q₂)
    (A : E →L[𝕜] E) (D : Q₂ →L[𝕜] Q₂)
    (hker : q₁.toLinearMap.ker = A.toLinearMap.range) (hcomp : ∀ v, q₂ (A v) = D (q₂ v))
    (P : ℕ → Q₂ →L[𝕜] Q₂) (z : ℕ → Q₂) (μ : ℕ → 𝕜) {C : ℝ}
    (hC : 0 ≤ C) (hP : ∀ n, ‖P n‖ ≤ C)
    (hz : ∀ n, z n ∈ Set.range D) (hnorm : ∀ n, ‖z n‖ = 1)
    (hfix : ∀ n, P n (z n) = z n) (hmul : ∀ n v, P n (D v) = μ n • P n v)
    (hsmall : ∀ ε > 0, ∃ n, ‖μ n‖ < ε) :
    ¬ IsClosed (Set.range fun v ↦ (q₁ v, q₂ v)) := by
  intro hclosed
  have heq : (fun y : Q₂ ↦ ((0 : Q₁), y)) ⁻¹' (Set.range fun v ↦ (q₁ v, q₂ v)) =
      Set.range D := by
    ext y
    change ((0 : Q₁), y) ∈ Set.range (fun v ↦ (q₁ v, q₂ v)) ↔ y ∈ Set.range D
    simpa only [map_zero, sub_zero] using packetJointLift_iff q₁ q₂ hq₂ A D hker hcomp 0 y
  apply packetDifference_range_not_isClosed D P z μ hC hP hz hnorm hfix hmul hsmall
  rw [← heq]
  exact hclosed.preimage (continuous_const.prodMk continuous_id)

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Given cardinal lifts in a complete ambient space, prescribed output coordinates
with summable rank-one costs assemble into an operator with an absolutely
convergent rank-one expansion. Its norm is bounded by the total lift cost.
Reconstruction: This verifies the synthesis step of the finite-rank
approximation on p. 496 from the estimates on the individual lifts. -/
theorem packetSynthesis_of_summable_rankOne
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι E F : Type*}
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (sample : ι → F →L[𝕜] 𝕜) (row : ι → E →L[𝕜] 𝕜) (lift : ι → F)
    (hdiag : ∀ i, sample i (lift i) = 1)
    (hoff : ∀ i j, j ≠ i → sample i (lift j) = 0)
    (hcost : Summable (fun i ↦ ‖row i‖ * ‖lift i‖)) :
    ∃ S : E →L[𝕜] F,
      HasSum (fun i ↦ (row i).smulRight (lift i)) S ∧
      (∀ i x, sample i (S x) = row i x) ∧
      (∀ x, (∀ i, row i x = 0) → S x = 0) ∧
      ‖S‖ ≤ ∑' i, ‖row i‖ * ‖lift i‖ := by
  classical
  let term (i : ι) := (row i).smulRight (lift i)
  have habs : Summable (fun i ↦ ‖term i‖) := by
    simpa only [term, ContinuousLinearMap.norm_smulRight_apply] using hcost
  let S := ∑' i, term i
  have hS : HasSum term S := habs.of_norm.hasSum
  refine ⟨S, hS, ?_, ?_, ?_⟩
  · intro i x
    have hsum := (hS.mapL (ContinuousLinearMap.apply 𝕜 F x)).mapL (sample i)
    refine hsum.unique ((hasSum_ite_eq i (row i x)).congr_fun fun j ↦ ?_)
    change sample i (row j x • lift j) = if j = i then row i x else 0
    by_cases hji : j = i
    · subst j
      simp [hdiag]
    · simp [hji, hoff i j hji]
  · intro x hx
    have hsum := hS.mapL (ContinuousLinearMap.apply 𝕜 F x)
    refine hsum.unique (hasSum_zero.congr_fun fun i ↦ ?_)
    change row i x • lift i = (0 : F)
    rw [hx, zero_smul]
  · simpa only [S, term, ContinuousLinearMap.norm_smulRight_apply] using
      norm_tsum_le_tsum_norm habs

/-- Paper: (11.3.2.4)–(11.3.2.5), p. 496.
On a Hilbert space, the cardinal synthesis has a trace-norm convergent expansion.
The sum of the omitted rank-one costs bounds the trace-norm error for each truncation.
Reconstruction: The cutoffs here retain orbital coordinates in the synthesized
operator. The geometric cutoff comparison requires a further identification. -/
theorem packetSynthesis_traceNorm_tendsto
    {ι κ H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (sample row : ι → H →L[ℂ] ℂ) (lift : ι → H)
    (hdiag : ∀ i, sample i (lift i) = 1)
    (hoff : ∀ i j, j ≠ i → sample i (lift j) = 0)
    (hcost : Summable (fun i ↦ ‖row i‖ * ‖lift i‖))
    (W : κ → Set ι) (l : Filter κ) (hW : ∀ i, ∀ᶠ k in l, i ∈ W k) :
    ∃ S : H →L[ℂ] H, (∀ i x, sample i (S x) = row i x) ∧
      ∃ hS : IsNuclearOperator S,
      ∃ hK : ∀ k, IsNuclearOperator (∑' i : W k, (row i.val).smulRight (lift i.val)),
        (∀ k, traceNorm ((⟨S, hS⟩ : nuclearEndomorphisms H) - ⟨_, hK k⟩) ≤
          ∑' i : ↥((W k)ᶜ : Set ι), ‖row i.val‖ * ‖lift i.val‖) ∧
        Tendsto (fun k ↦ traceNorm ((⟨S, hS⟩ : nuclearEndomorphisms H) - ⟨_, hK k⟩)) l
          (𝓝 0) := by
  obtain ⟨S, hsum, hsample, _, _⟩ :=
    packetSynthesis_of_summable_rankOne sample row lift hdiag hoff hcost
  let R (i : ι) : nuclearEndomorphisms H :=
    ⟨(row i).smulRight (lift i), smulRight_mem_nuclearEndomorphisms _ _⟩
  refine ⟨S, hsample, ?_⟩
  exact traceNorm_tendsto_of_hasSum_subseries R S hsum _ hcost
    (fun i ↦ (traceNorm_smulRight (row i) (lift i)).le) W l hW

end RiemannMasullo.Isolated
