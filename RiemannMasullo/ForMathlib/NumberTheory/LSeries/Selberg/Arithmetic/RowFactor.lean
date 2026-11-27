module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions
import Mathlib.Algebra.Order.Floor.Semifield
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Arithmetic.SmoothSplit

public section

open Classical

namespace RiemannMasullo.Selberg

private theorem mem_quotient_cutoff {N d s : ℕ} (hd : 0 < d) :
    s ∈ D (N / d) ↔ d * s ∈ D N := by
  simp only [D, Finset.mem_Icc, Nat.le_div_iff_mul_le hd, Nat.mul_comm s d]
  exact and_congr_left' ⟨Nat.mul_pos hd, Nat.pos_of_mul_pos_left⟩

/-- Reindex a finite sum by the supported and coprime parts of each index. -/
private theorem sum_smooth_split (r N : ℕ) (hr : 0 < r) (f : ℕ → ℝ) :
    ∑ n ∈ D N, f n = ∑ d ∈ (D N).filter (smooth r),
      ∑ s ∈ (D (N / d)).filter (Nat.Coprime r), f (d * s) := by
  let pairs := ((D N).filter (smooth r)).sigma fun d ↦ (D (N / d)).filter (Nat.Coprime r)
  have mem_pairs (a : (_ : ℕ) × ℕ) :
      a ∈ pairs ↔ smooth r a.1 ∧ r.Coprime a.2 ∧ a.1 * a.2 ∈ D N := by
    simp only [pairs, Finset.mem_sigma, Finset.mem_filter]
    constructor
    · rintro ⟨⟨hd, hsm⟩, hs, hc⟩
      exact ⟨hsm, hc, (mem_quotient_cutoff (Finset.mem_Icc.mp hd).1).mp hs⟩
    · rintro ⟨hsm, hc, hm⟩
      obtain ⟨hpos, hle⟩ := Finset.mem_Icc.mp hm
      have hd := Nat.pos_of_mul_pos_right hpos
      have hs := Nat.pos_of_mul_pos_left hpos
      exact ⟨⟨Finset.mem_Icc.mpr ⟨hd, (Nat.le_mul_of_pos_right _ hs).trans hle⟩, hsm⟩,
        (mem_quotient_cutoff hd).mpr hm, hc⟩
  symm
  rw [Finset.sum_sigma']
  apply Finset.sum_bij (fun a _ ↦ a.1 * a.2)
  · exact fun a ha ↦ ((mem_pairs a).mp ha).2.2
  · intro a ha b hb hab
    obtain ⟨ha₁, ha₂, hN⟩ := (mem_pairs a).mp ha
    obtain ⟨hb₁, hb₂, _⟩ := (mem_pairs b).mp hb
    have heq : (a.1, a.2) = (b.1, b.2) :=
      (smooth_split r _ hr (Finset.mem_Icc.mp hN).1).unique ⟨ha₁, ha₂, rfl⟩ ⟨hb₁, hb₂, hab.symm⟩
    exact Sigma.ext (congrArg Prod.fst heq) (heq_of_eq (congrArg Prod.snd heq))
  · intro n hn
    obtain ⟨⟨d, s⟩, ⟨hd, hs, hprod⟩, _⟩ := smooth_split r n hr (Finset.mem_Icc.mp hn).1
    exact ⟨⟨d, s⟩, (mem_pairs _).mpr ⟨hd, hs, hprod ▸ hn⟩, hprod⟩
  · exact fun _ _ ↦ rfl

/-- Sum out the coprime part of a tapered index when the extra weight is invariant
under multiplication by numbers coprime to `r`. -/
private theorem sum_tapered (r N : ℕ) (hr : 0 < r) (f : ℕ → ℝ)
    (hf : ∀ d s, r.Coprime s → f (d * s) = f d) :
    ∑ n ∈ D N, beta N n / n * f n =
      ∑ d ∈ (D N).filter (smooth r),
        (alpha d / d * logSum r ((N : ℝ) / d) / Real.log N) * f d := by
  rw [sum_smooth_split r N hr]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  obtain ⟨hdN, hsm⟩ := Finset.mem_filter.mp hd
  simp only [logSum, Nat.floor_div_eq_div, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  obtain ⟨hsN, hc⟩ := Finset.mem_filter.mp hs
  have hds := (mem_quotient_cutoff (Finset.mem_Icc.mp hdN).1).mp hsN
  have hcop : d.Coprime s := by
    refine Nat.coprime_of_dvd fun p hp hpd ↦ hp.coprime_iff_not_dvd.mp ?_
    exact hc.of_dvd_left (Nat.dvd_of_mem_primeFactors (Nat.mem_factoredNumbers'.mp hsm p hp hpd))
  have hα : alpha (d * s) = alpha d * alpha s :=
    spectralLineJet_selbergHalfMoebius_mult.map_mul_of_coprime hcop
  rw [beta, ite_eq_left hds, hα, hf d s hc, Nat.cast_mul, div_mul_eq_div_div (N : ℝ) d s]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ac_rfl

/-- Card 8. At power one the tapered row factors into a sum over pairs of r-supported divisors.
Each term contains two coprime logarithmic sums and the denominator (log N)².
Titchmarsh, §10.11, p. 271, last display before Lemma 10.12. -/
theorem row_factor (r N : ℕ) (hr : 0 < r) (hN : 2 ≤ N) :
    row N (beta N) 1 r =
      (∑ d ∈ (D N).filter (smooth r), ∑ e ∈ (D N).filter (fun e ↦ smooth r e ∧ r ∣ d*e),
        alpha d * alpha e / ((d : ℝ)*e) * logSum r ((N : ℝ)/d) * logSum r ((N : ℝ)/e)) /
        (Real.log N)^2 := by
  let w (n : ℕ) := beta N n / n
  let A (d : ℕ) := alpha d / d * logSum r ((N : ℝ) / d) / Real.log N
  let I (k v : ℕ) : ℝ := if r ∣ k * v then 1 else 0
  let S := (D N).filter (smooth r)
  calc
    row N (beta N) 1 r =
        ∑ k ∈ D N, w k * ∑ v ∈ D N, w v * I k v := by
      simp only [row, Real.rpow_one, w, I, Finset.sum_filter, Finset.mul_sum,
        mul_ite, mul_one, mul_zero, div_mul_div_comm]
    _ = ∑ d ∈ S, A d * ∑ v ∈ D N, w v * I d v := by
      apply sum_tapered r N hr
      intro d s hs
      simp only [I, Nat.mul_right_comm d s, hs.dvd_mul_right]
    _ = ∑ d ∈ S, A d * ∑ e ∈ S, A e * I d e := by
      refine Finset.sum_congr rfl fun d _ ↦ congrArg (A d * ·) ?_
      apply sum_tapered r N hr
      intro e s hs
      simp only [I, ← Nat.mul_assoc, hs.dvd_mul_right]
    _ = _ := by
      simp only [S, A, I, Finset.sum_div, Finset.mul_sum, mul_ite, mul_one, mul_zero,
        ← Finset.sum_filter, Finset.filter_filter]
      refine Finset.sum_congr rfl fun d _ ↦ ?_
      refine Finset.sum_congr rfl fun e _ ↦ ?_
      have hlog : Real.log N ≠ 0 := (Real.log_pos (by exact_mod_cast (show 1 < N from hN))).ne'
      rw [div_mul_div_comm, ← sq, div_left_inj₀ (pow_ne_zero 2 hlog)]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ac_rfl

end RiemannMasullo.Selberg
