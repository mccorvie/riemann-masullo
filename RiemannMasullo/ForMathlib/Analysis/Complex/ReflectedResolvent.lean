module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Topology.Instances.Complex
import Mathlib.Tactic

/-! # Positive resolvent sums from reflection and finite pole corrections

Reflection pairs the real parts at opposite evaluation points. Nonnegative
weights make the real sum at one point absolutely convergent. A separate
summation lemma removes the finitely many simple negative orders.
-/

public noncomputable section

open Complex Filter Function Set Topology
open scoped ComplexConjugate

namespace Complex

/-- Real part of the resolvent at a reflected pole, with respect to the vertical line
through one half. This applies to non-real weights only after the multiplicity has been
separately identified as real. -/
theorem re_resolvent_reflect (s p : ℂ) (m : ℝ) :
    ((m : ℂ) / (1 - conj s - p)).re =
      -((m : ℂ) / (s - (1 - conj p))).re := by
  have h : 1 - conj s - p = -(conj (s - (1 - conj p))) := by
    simp only [map_sub, map_one, Complex.conj_conj]; ring
  rw [h, div_neg, Complex.neg_re]
  rw [show (m : ℂ) / (conj (s - (1 - conj p))) =
      conj ((m : ℂ) / (s - (1 - conj p))) by simp only [map_div₀, Complex.conj_ofReal]]
  simp only [Complex.conj_re]

/-- A meromorphic resolvent difference evaluated at a pair of reflected arguments
determines the full, positive real Poisson sum. Positivity gives absolute summability
of the one-sided terms even when only summability of the paired differences is known. -/
theorem hasSum_real_resolvent_of_mirror {ι : Type*} (p : ι → ℂ) (m : ι → ℝ)
    (e : ι ≃ ι) (he : ∀ i, p (e i) = 1 - conj (p i)) (hm : ∀ i, m (e i) = m i)
    (s : ℂ) (P : ℂ → ℂ) (c : ℝ)
    (hR : ∀ i, 0 ≤ ((m i : ℂ) / (s - p i)).re)
    (hP : (P (1 - conj s)).re = -(P s).re - c)
    (hd : HasSum (fun i ↦ (m i : ℂ) * (1 / (s-p i) - 1 / (1-conj s-p i)))
      (P s - P (1-conj s))) :
    HasSum (fun i ↦ ((m i : ℂ) / (s-p i)).re) ((P s).re + c / 2) := by
  let R (i : ι) := ((m i : ℂ) / (s-p i)).re
  have hmirror (i : ι) : ((m i : ℂ) / (1-conj s-p i)).re = -R (e i) := by
    simp only [R, hm, he, re_resolvent_reflect]
  have hpair : HasSum (fun i ↦ R i + R (e i)) ((P s).re - (P (1-conj s)).re) := by
    apply (Complex.hasSum_re hd).congr_fun
    intro i
    rw [mul_sub, mul_one_div, mul_one_div, Complex.sub_re, hmirror]
    simp [R]
  have hsum : Summable R :=
    hpair.summable.of_nonneg_of_le hR fun i ↦ le_add_of_nonneg_right (hR (e i))
  have hsum' : HasSum (fun i ↦ R i + R (e i)) ((∑' i, R i) + ∑' i, R i) :=
    hsum.hasSum.add ((e.hasSum_iff).mpr hsum.hasSum)
  have heq := hpair.unique hsum'
  have htarget : (∑' i, R i) = (P s).re + c/2 := by linarith
  exact htarget ▸ hsum.hasSum

/-- The signed series over a divisor with finitely many simple poles is the
positive-order series minus the finite sum of pole samples. -/
theorem hasSum_signed_simple_poles {ι : Type*} (m : ι → ℤ) (f : ι → ℂ) (P : Finset ι)
    (hP : ∀ j : ι, j ∈ P ↔ m j < 0) (hm : ∀ j ∈ P, m j = -1)
    (hp : Summable (fun j : {i : ι // 0 < m i} ↦ ((m j.val).toNat : ℂ)*f j.val)) :
    HasSum (fun j ↦ (m j : ℂ)*f j)
      ((∑' j : {i : ι // 0 < m i}, ((m j.val).toNat : ℂ)*f j.val) - ∑ j ∈ P, f j) := by
  classical
  let pos (j : ι) := if 0 < m j then ((m j).toNat : ℂ)*f j else 0
  have hsupp : support pos ⊆ {j : ι | 0 < m j} := by
    intro j hj
    by_contra h
    change ¬ 0 < m j at h
    exact hj (by simp [pos,h])
  have hpos : HasSum pos (∑' j : {i : ι // 0 < m i}, ((m j.val).toNat : ℂ)*f j.val) := by
    apply (hasSum_subtype_iff_of_support_subset hsupp).mp
    exact hp.hasSum.congr_fun (fun j ↦ by simp [pos,j.property])
  let pol (j : ι) := if j ∈ P then f j else 0
  have hpol : HasSum pol (∑ j ∈ P, f j) := by
    have h : HasSum pol (∑ j ∈ P, pol j) := hasSum_sum_of_ne_finset_zero (s := P) (f := pol) fun j hj ↦ by simp [pol,hj]
    simpa only [pol,Finset.sum_ite_mem,Finset.inter_self] using h
  refine (hpos.sub hpol).congr_fun fun j ↦ ?_
  by_cases hj : j ∈ P
  · have hn := hm j hj
    simp [pos,pol,hj,hn]
  · have hn : 0 ≤ m j := not_lt.mp (fun hb ↦ hj ((hP j).mpr hb))
    rcases hn.eq_or_lt with he | he
    · simp [pos,pol,hj,← he]
    · have hcast : ((m j).toNat : ℂ) = (m j : ℂ) := by exact_mod_cast Int.toNat_of_nonneg hn
      simp [pos,pol,hj,he,hcast]

end Complex
