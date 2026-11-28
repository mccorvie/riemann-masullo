module

public import Mathlib.Analysis.Normed.Group.AddCircle
public import Mathlib.Topology.Instances.AddCircle.DenseSubgroup
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Topology.Baire.CompleteMetrizable
public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Separation.GDelta
import Mathlib.Tactic

/-!
# Shrinking targets for dense orbits

These are generic topological statements. They do not assert that a phase arising
from a Hecke character belongs to the exceptional set.
-/

open Set Metric Filter
open scoped Topology

public section

namespace RiemannMasullo.Isolated

/-- Deleting every index of bounded height leaves a dense family, when the
original range is dense and bounded height sets are finite. -/
theorem dense_image_height_tail
    {X I : Type*} [MetricSpace X] [PerfectSpace X]
    (u : I → X) (height : I → ℕ) (hu : DenseRange u)
    (hfinite : ∀ N : ℕ, Set.Finite {i | height i < N}) (N : ℕ) :
    Dense (u '' {i | N ≤ height i}) := by
  have hd := (hu : Dense (Set.range u)).sdiff_finite ((hfinite N).image u)
  refine hd.mono ?_
  rintro x ⟨⟨i, rfl⟩, hi⟩
  refine ⟨i, ?_, rfl⟩
  change N ≤ height i
  by_contra h
  exact hi ⟨i, Nat.lt_of_not_ge h, rfl⟩

/-- For arbitrary positive radii, simultaneous infinitely frequent approximation
along a dense family is a dense Gδ condition. There is no lower bound on the radii. -/
theorem shrinking_targets_dense_Gdelta
    {X I : Type*} [MetricSpace X] [BaireSpace X] [PerfectSpace X]
    (u : I → X) (height : I → ℕ) (hu : DenseRange u)
    (hfinite : ∀ N : ℕ, Set.Finite {i | height i < N})
    (radius : ℕ → I → ℝ) (hpositive : ∀ k i, 0 < radius k i) :
    IsGδ {x : X | ∀ k N : ℕ, ∃ i, N ≤ height i ∧ dist x (u i) < radius k i} ∧
    Dense {x : X | ∀ k N : ℕ, ∃ i, N ≤ height i ∧ dist x (u i) < radius k i} := by
  let U (p : ℕ × ℕ) : Set X :=
    ⋃ i, ⋃ (_ : p.2 ≤ height i), Metric.ball (u i) (radius p.1 i)
  have hopen (p : ℕ × ℕ) : IsOpen (U p) :=
    isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ Metric.isOpen_ball
  have hdense (p : ℕ × ℕ) : Dense (U p) := by
    refine (dense_image_height_tail u height hu hfinite p.2).mono ?_
    rintro x ⟨i, hi, rfl⟩
    simp only [U, Set.mem_iUnion, Metric.mem_ball]
    exact ⟨i, hi, by simpa using hpositive p.1 i⟩
  have heq : {x : X | ∀ k N : ℕ, ∃ i, N ≤ height i ∧
      dist x (u i) < radius k i} = ⋂ p : ℕ × ℕ, U p := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, U, Set.mem_iUnion, Metric.mem_ball]
    constructor
    · intro hx p
      obtain ⟨i, hi, hd⟩ := hx p.1 p.2
      exact ⟨i, hi, hd⟩
    · intro hx k N
      obtain ⟨i, hi, hd⟩ := hx (k, N)
      exact ⟨i, hi, hd⟩
  rw [heq]
  exact ⟨IsGδ.iInter_of_isOpen hopen, dense_iInter_of_isOpen hopen hdense⟩

/-- The countable exceptional phases may be removed without losing density. -/
theorem shrinking_targets_dense_Gdelta_avoiding_countable
    {X I : Type*} [MetricSpace X] [BaireSpace X] [PerfectSpace X]
    (u : I → X) (height : I → ℕ) (hu : DenseRange u)
    (hfinite : ∀ N : ℕ, Set.Finite {i | height i < N})
    (radius : ℕ → I → ℝ) (hpositive : ∀ k i, 0 < radius k i)
    (D : Set X) (hD : D.Countable) :
    IsGδ ({x : X | ∀ k N : ℕ, ∃ i, N ≤ height i ∧ dist x (u i) < radius k i} \ D) ∧
    Dense ({x : X | ∀ k N : ℕ, ∃ i, N ≤ height i ∧ dist x (u i) < radius k i} \ D) := by
  obtain ⟨hG, hd⟩ := shrinking_targets_dense_Gdelta u height hu hfinite radius hpositive
  have : Countable D := hD.to_subtype
  have hc : Dense (Dᶜ : Set X) := by
    have ht : Dense (⋂ d : D, ({(d : X)}ᶜ : Set X)) :=
      dense_iInter_of_isOpen (fun _ ↦ isOpen_compl_singleton)
        (fun d ↦ dense_compl_singleton (d : X))
    convert ht using 1
    ext x
    simp only [Set.mem_compl_iff, Set.mem_iInter, Set.mem_singleton_iff]
    constructor
    · intro hx d heq
      exact hx (by simpa only [heq] using d.property)
    · intro hx hmem
      exact hx ⟨x, hmem⟩ rfl
  exact ⟨hG.inter hD.isGδ_compl, hd.inter_of_Gδ hG hD.isGδ_compl hc⟩

/-- Every bounded absolute-height subset of the integers is finite. -/
private theorem finite_int_natAbs_lt (N : ℕ) : Set.Finite {n : ℤ | n.natAbs < N} := by
  refine (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).subset ?_
  intro n hn
  have hc : (n.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast (Nat.le_of_lt hn)
  exact abs_le.mp (by simpa only [Int.natCast_natAbs] using hc)

/-- For an irrational rotation, phases approximable faster than every inverse
power form a dense Gδ even after removal of any prescribed countable set. This
is about arbitrary phases; no assertion is made about arithmetic Hecke phases. -/
theorem irrational_rotation_superpolynomial_targets
    (α : ℝ) (hα : Irrational α) (D : Set (AddCircle (1 : ℝ))) (hD : D.Countable) :
    IsGδ ({β : AddCircle (1 : ℝ) | ∀ k N : ℕ, ∃ n : ℤ,
      N ≤ n.natAbs ∧ dist β (n • (α : AddCircle (1 : ℝ))) <
        ((1 + (n.natAbs : ℝ)) ^ k)⁻¹} \ D) ∧
    Dense ({β : AddCircle (1 : ℝ) | ∀ k N : ℕ, ∃ n : ℤ,
      N ≤ n.natAbs ∧ dist β (n • (α : AddCircle (1 : ℝ))) <
        ((1 + (n.natAbs : ℝ)) ^ k)⁻¹} \ D) := by
  have hu : DenseRange (fun n : ℤ ↦ n • (α : AddCircle (1 : ℝ))) :=
    AddCircle.denseRange_zsmul_coe_iff.mpr (by simpa using hα)
  exact shrinking_targets_dense_Gdelta_avoiding_countable _ Int.natAbs hu
    finite_int_natAbs_lt (fun k n ↦ ((1 + (n.natAbs : ℝ)) ^ k)⁻¹)
    (by intro k n; positivity) D hD

/-- The simultaneous shrinking-target property rules out every inverse-polynomial
lower bound, including bounds with constants depending on the target phase. -/
theorem superpolynomial_targets_no_polynomial_lower_bound
    {X I : Type*} [MetricSpace X]
    (u : I → X) (height : I → ℕ) (x : X)
    (hx : ∀ k N : ℕ, ∃ i, N ≤ height i ∧
      dist x (u i) < ((1 + (height i : ℝ)) ^ k)⁻¹) :
    ¬ ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ i,
      1 ≤ C * (1 + (height i : ℝ)) ^ d * dist x (u i) := by
  rintro ⟨d, C, _hC, hbound⟩
  obtain ⟨N, hN⟩ := exists_nat_gt C
  obtain ⟨i, hiN, hi⟩ := hx (d + 1) N
  let b : ℝ := 1 + (height i : ℝ)
  have hb : 0 < b := by dsimp [b]; positivity
  have hCb : C < b := by
    have hn : (N : ℝ) ≤ (height i : ℝ) := by exact_mod_cast hiN
    dsimp [b]
    linarith
  have hpow : 0 < b ^ (d + 1) := pow_pos hb _
  have hsmall := mul_lt_mul_of_pos_right hi hpow
  change dist x (u i) * b ^ (d + 1) < (b ^ (d + 1))⁻¹ * b ^ (d + 1) at hsmall
  rw [inv_mul_cancel₀ hpow.ne'] at hsmall
  have hsmall' : b * (b ^ d * dist x (u i)) < 1 := by
    calc
      b * (b ^ d * dist x (u i)) = dist x (u i) * b ^ (d + 1) := by
        rw [pow_succ]
        ring
      _ < 1 := hsmall
  have ht : 0 ≤ b ^ d * dist x (u i) :=
    mul_nonneg (pow_nonneg hb.le _) dist_nonneg
  have hupper : C * (b ^ d * dist x (u i)) < 1 :=
    (mul_le_mul_of_nonneg_right hCb.le ht).trans_lt hsmall'
  have hlower := hbound i
  change 1 ≤ C * b ^ d * dist x (u i) at hlower
  rw [mul_assoc] at hlower
  exact (not_lt_of_ge hlower) hupper

/-- An irrational rotation has a target outside the rational span of its angle
that admits arbitrarily accurate inhomogeneous approximations and no polynomial
lower bound. The exclusion is the scalar rational-affine obstruction to clearing
the shift by a common integer power; it is not a Hecke-character construction. -/
theorem exists_superpolynomial_phase_outside_rational_span
    (α : ℝ) (hα : Irrational α) :
    ∃ β : AddCircle (1 : ℝ),
      (∀ q r : ℚ, β ≠ (((q : ℝ) + (r : ℝ) * α : ℝ) : AddCircle (1 : ℝ))) ∧
      (∀ k N : ℕ, ∃ n : ℤ, N ≤ n.natAbs ∧
        dist β (n • (α : AddCircle (1 : ℝ))) <
          ((1 + (n.natAbs : ℝ)) ^ k)⁻¹) ∧
      ¬ ∃ d : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℤ,
        1 ≤ C * (1 + (n.natAbs : ℝ)) ^ d *
          dist β (n • (α : AddCircle (1 : ℝ))) := by
  let D : Set (AddCircle (1 : ℝ)) := Set.range
    (fun qr : ℚ × ℚ ↦ (((qr.1 : ℝ) + (qr.2 : ℝ) * α : ℝ) : AddCircle (1 : ℝ)))
  obtain ⟨β, hβ⟩ :=
    (irrational_rotation_superpolynomial_targets α hα D (Set.countable_range _)).2.nonempty
  refine ⟨β, ?_, hβ.1, ?_⟩
  · intro q r heq
    exact hβ.2 ⟨(q, r), heq.symm⟩
  · exact superpolynomial_targets_no_polynomial_lower_bound
      (fun n : ℤ ↦ n • (α : AddCircle (1 : ℝ))) Int.natAbs β hβ.1

end RiemannMasullo.Isolated
