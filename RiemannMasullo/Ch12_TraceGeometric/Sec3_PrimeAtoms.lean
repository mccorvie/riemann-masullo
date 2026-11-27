module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.ShrinkingLaplaceProbe
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.Analysis.Meromorphic.Divisor
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! # The rational logarithmic prime atoms and the smooth archimedean error -/

@[expose] public noncomputable section

open Filter Set MeasureTheory
open scoped ArithmeticFunction ContDiff Topology

namespace RiemannMasullo.PrimeShrink

/-- Genuine rational log-prime-power samples, with zero entries at 0 and 1. -/
def primeSeries (H : ℝ → ℝ) : ℝ := ∑' n : ℕ, Λ n * H (Real.log n)

/-- The mass at a logarithmic site, including the case of an empty fiber. -/
def atomWeight (c : ℝ) : ℝ := ∑' n : ℕ, if Real.log (n : ℝ) = c then Λ n else 0

/-- Every log location has a neighborhood meeting the logarithms of positive integers
only at its center, if at all. -/
theorem logNat_isolation (c : ℝ) :
    ∃ r > 0, ∀ n : ℕ, 0 < n → |Real.log (n : ℝ) - c| ≤ r → Real.log (n : ℝ) = c := by
  classical
  let N := ⌈Real.exp (c + 1)⌉₊
  let W := (Finset.range (N + 1)).image fun n : ℕ ↦ Real.log (n : ℝ)
  let S := W.erase c
  have hopen : IsOpen ((S : Set ℝ)ᶜ) := S.finite_toSet.isClosed.isOpen_compl
  have hc : c ∈ ((S : Set ℝ)ᶜ) := by simp [S]
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen c hc
  refine ⟨min 1 (ε / 2), lt_min zero_lt_one (by positivity), ?_⟩
  intro n hn h
  have hn' : (n : ℝ) ≤ Real.exp (c + 1) := by
    calc (n : ℝ) = Real.exp (Real.log n) := (Real.exp_log (Nat.cast_pos.mpr hn)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith [(abs_le.mp h).2, min_le_left (1 : ℝ) (ε / 2)])
  have hnN : n ≤ N := by exact_mod_cast hn'.trans (Nat.le_ceil (Real.exp (c + 1)))
  have hin : Real.log (n : ℝ) ∈ W := Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr (by omega), rfl⟩
  by_contra he
  have hmem : Real.log (n : ℝ) ∈ Metric.ball c ε := by
    rw [Metric.mem_ball, Real.dist_eq]
    linarith [h.trans (min_le_right (1 : ℝ) (ε / 2))]
  exact hball hmem (Finset.mem_erase.mpr ⟨he, hin⟩)

/-- At an arbitrary prime power the mass has the same weight as at its prime. -/
theorem atomWeight_log_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    atomWeight (Real.log ((p ^ k : ℕ) : ℝ)) = Real.log p := by
  classical
  unfold atomWeight
  rw [tsum_eq_single (p ^ k)]
  · simp [ArithmeticFunction.vonMangoldt_apply_pow hk, ArithmeticFunction.vonMangoldt_apply_prime hp]
  · intro n hn
    by_cases hz : n = 0
    · simp [hz]
    have hneq : Real.log (n : ℝ) ≠ Real.log ((p ^ k : ℕ) : ℝ) := by
      intro he
      have he' := Real.strictMonoOn_log.injOn
        (show (n : ℝ) ∈ Ioi 0 by exact Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz))
        (show ((p ^ k : ℕ) : ℝ) ∈ Ioi 0 by exact Nat.cast_pos.mpr (pow_pos hp.pos k)) he
      exact hn (by exact_mod_cast he')
    exact ite_eq_right hneq

theorem atomWeight_eq_zero {c : ℝ}
    (h : ∀ n : ℕ, IsPrimePow n → Real.log (n : ℝ) ≠ c) : atomWeight c = 0 := by
  have he : (fun n : ℕ ↦ if Real.log (n : ℝ) = c then Λ n else 0) = fun _ ↦ (0 : ℝ) := by
    funext n
    by_cases hp : IsPrimePow n
    · simp [h n hp]
    · simp [ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hp]
  rw [atomWeight, he, tsum_zero]

/-- If the support lies in an isolating window, the whole prime sum is one atom. -/
theorem primeSeries_eq_atom {c r : ℝ} (H : ℝ → ℝ)
    (hiso : ∀ n : ℕ, 0 < n → |Real.log (n : ℝ) - c| ≤ r → Real.log (n : ℝ) = c)
    (hs : ∀ x, H x ≠ 0 → |x - c| ≤ r) :
    primeSeries H = atomWeight c * H c := by
  unfold primeSeries atomWeight
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  by_cases h : Real.log (n : ℝ) = c
  · simp [h]
  by_cases hn : n = 0
  · simp [hn]
  have hz : H (Real.log n) = 0 := by
    by_contra hh
    exact h (hiso n (Nat.pos_of_ne_zero hn) (hs _ hh))
  simp [h, hz]

/-- The smooth term in the distributional von Mangoldt formula on the positive log axis. -/
def archIntegral (H : ℝ → ℝ) : ℝ := ∫ x in Ioi 0, H x / (Real.exp (2 * x) - 1)

/-- On a log window bounded away from zero, the archimedean contribution is bounded
by its length times the maximum of the test times the maximum of the kernel. -/
theorem abs_archIntegral_le {c r A : ℝ} (hc : 0 < c) (hr : 0 ≤ r) (hrc : 2 * r ≤ c)
    (H : ℝ → ℝ) (hs : ∀ x, H x ≠ 0 → |x - c| ≤ r) (hA : ∀ x, |H x| ≤ A) :
    |archIntegral H| ≤ A / (Real.exp c - 1) * (2 * r) := by
  let I := Icc (c - r) (c + r)
  let f (x : ℝ) := H x / (Real.exp (2 * x) - 1)
  have hI (x : ℝ) (hx : H x ≠ 0) : x ∈ I := by
    obtain ⟨hl, hu⟩ := abs_le.mp (hs x hx)
    exact ⟨by linarith, by linarith⟩
  have ho (x : ℝ) (hx : x ∉ Ioi 0) : f x = 0 := by
    have hz : H x = 0 := by
      by_contra h
      have := (hI x h).1
      exact hx (show 0 < x by linarith)
    simp [f, hz]
  have hd (x : ℝ) (hx : x ∉ I) : f x = 0 := by
    have hz : H x = 0 := by by_contra h; exact hx (hI x h)
    simp [f, hz]
  have heq : archIntegral H = ∫ x in I, f x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) ho).trans
      (setIntegral_eq_integral_of_forall_compl_eq_zero hd).symm
  have hpos : 0 < Real.exp c - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hc)
  rw [heq, ← Real.norm_eq_abs]
  calc
    ‖∫ x in I, f x‖ ≤ A / (Real.exp c - 1) * volume.real I := by
      apply norm_setIntegral_le_of_norm_le_const isCompact_Icc.measure_lt_top
      intro x hx
      have hx' : c ≤ 2 * x := by linarith [hx.1]
      have hden : Real.exp c - 1 ≤ Real.exp (2 * x) - 1 := sub_le_sub_right (Real.exp_le_exp.mpr hx') 1
      change |H x / (Real.exp (2 * x) - 1)| ≤ _
      rw [abs_div, abs_of_pos (hpos.trans_le hden)]
      apply (div_le_div_iff₀ (hpos.trans_le hden) hpos).mpr
      exact (mul_le_mul_of_nonneg_right (hA x) hpos.le).trans
        (mul_le_mul_of_nonneg_left hden ((abs_nonneg _).trans (hA x)))
    _ = _ := by
      rw [show volume.real I = (c + r) - (c - r) from Real.volume_real_Icc_of_le (by linarith)]
      ring

/-- Prime-side value after vanishing of the Mellin pole moment at 1. -/
def positiveAxis (H : ℝ → ℝ) : ℝ := -primeSeries H - archIntegral H

/-- Uniform local estimate for profiles of radius `Rη`, independent of any zero data.
The parameter set can encode an arbitrary bounded family of translates. -/
theorem positiveAxis_local_atom {ι : Type*} {c R A E : ℝ} (hc : 0 < c) (hR : 0 < R)
    (H : ℝ → ι → ℝ → ℝ) (J : ι → ℝ) (U : Set ι)
    (hs : ∀ η, 0 < η → η ≤ 1 → ∀ t ∈ U, ∀ x, H η t x ≠ 0 → |x - c| ≤ R * η)
    (hb : ∀ η, 0 < η → η ≤ 1 → ∀ t ∈ U, ∀ x, |H η t x| ≤ A)
    (hj : ∀ η, 0 < η → η ≤ 1 → ∀ t ∈ U, |H η t c - J t| ≤ E * η) :
    ∃ δ > 0, ∃ K : ℝ, ∀ η, 0 < η → η ≤ δ → ∀ t ∈ U,
      |positiveAxis (H η t) + atomWeight c * J t| ≤ K * η := by
  obtain ⟨r, hr, hsep⟩ := logNat_isolation c
  let δ := min 1 (min (r / R) (c / (2 * R)))
  have hδ : 0 < δ := lt_min zero_lt_one (lt_min (div_pos hr hR) (div_pos hc (mul_pos two_pos hR)))
  refine ⟨δ, hδ, |atomWeight c| * E + A / (Real.exp c - 1) * (2 * R), ?_⟩
  intro η hη hsmall t ht
  have hη1 := hsmall.trans (min_le_left 1 _)
  have hrη : R * η ≤ r := by
    rw [mul_comm]; apply (le_div_iff₀ hR).mp
    exact hsmall.trans ((min_le_right 1 _).trans (min_le_left _ _))
  have hcη : 2 * (R * η) ≤ c := by
    have he := (le_div_iff₀ (mul_pos two_pos hR)).mp
      (hsmall.trans ((min_le_right 1 _).trans (min_le_right _ _)))
    linarith [show η * (2 * R) = 2 * (R * η) by ring]
  have hp := primeSeries_eq_atom (H η t) hsep (fun x hx ↦ (hs η hη hη1 t ht x hx).trans hrη)
  have ha := abs_archIntegral_le hc (mul_nonneg hR.le hη.le) hcη (H η t)
    (hs η hη hη1 t ht) (hb η hη hη1 t ht)
  have hjet := mul_le_mul_of_nonneg_left (hj η hη hη1 t ht) (abs_nonneg (atomWeight c))
  rw [positiveAxis, hp]
  calc
    |- (atomWeight c * H η t c) - archIntegral (H η t) + atomWeight c * J t|
      = |-(atomWeight c * (H η t c - J t)) + (-archIntegral (H η t))| := by congr 1; ring
    _ ≤ |atomWeight c| * |H η t c - J t| + |archIntegral (H η t)| := by
      simpa only [abs_neg, abs_mul] using abs_add_le (-(atomWeight c * (H η t c - J t))) (-archIntegral (H η t))
    _ ≤ _ := (add_le_add hjet ha).trans_eq (by ring)

/-- Nontrivial zeta zeros indexed once each by the positive divisor of the completion. -/
def zetaZeros : Set ℂ := {z : ℂ | 0 < MeromorphicOn.divisor completedRiemannZeta univ z}

/-- The positive zero multiplicity times the physical, uncentered bilateral Laplace transform. -/
def zeroTerm (H : ℝ → ℝ) (ρ : zetaZeros) : ℂ :=
  ((MeromorphicOn.divisor completedRiemannZeta univ ρ.val : ℤ) : ℂ) *
    bilateralLaplace (fun x ↦ (H x : ℂ)) ρ.val

/-- The compactly smoothed von Mangoldt formula on the positive logarithmic axis.
Connes–Marcolli, *Noncommutative Geometry, Quantum Fields and Motives*, Chapter II,
§2, equations (2.17)–(2.19), p. 322, in their distributional derivative form. See also
§8.2, Theorem 2.37, pp. 365–366 for the multiplicity convention. -/
def PositiveAxisExplicitFormula : Prop :=
  ∀ H : ℝ → ℝ, ContDiff ℝ ∞ H → HasCompactSupport H → tsupport H ⊆ Ioi 0 →
    HasSum (zeroTerm H)
      (bilateralLaplace (fun x ↦ (H x : ℂ)) 1 + (positiveAxis H : ℂ))

/-- Transfer of the local atom estimate to the genuine unordered full zero sum. The
historical formula is an explicit input. The vanishing pole moment is the only one
needed by this prime-side transfer. -/
theorem fullZeroSum_local_atom (hef : PositiveAxisExplicitFormula) {ι : Type*}
    {c R A E : ℝ} (hc : 0 < c) (hR : 0 < R)
    (H : ℝ → ι → ℝ → ℝ) (J : ι → ℝ) (U : Set ι)
    (hreg : ∀ η, 0 < η → η ≤ 1 → ∀ t ∈ U, ContDiff ℝ ∞ (H η t) ∧ HasCompactSupport (H η t))
    (hpole : ∀ η, 0 < η → η ≤ 1 → ∀ t ∈ U, bilateralLaplace (fun x ↦ (H η t x : ℂ)) 1 = 0)
    (hs : ∀ η, 0 < η → η ≤ 1 → ∀ t ∈ U, ∀ x, H η t x ≠ 0 → |x - c| ≤ R * η)
    (hb : ∀ η, 0 < η → η ≤ 1 → ∀ t ∈ U, ∀ x, |H η t x| ≤ A)
    (hj : ∀ η, 0 < η → η ≤ 1 → ∀ t ∈ U, |H η t c - J t| ≤ E * η) :
    ∃ δ > 0, ∃ K : ℝ, ∀ η, 0 < η → η ≤ δ → ∀ t ∈ U,
      Summable (zeroTerm (H η t)) ∧
        ‖(∑' ρ : zetaZeros, zeroTerm (H η t) ρ) + ((atomWeight c * J t : ℝ) : ℂ)‖ ≤ K * η := by
  obtain ⟨d, hd, K, he⟩ := positiveAxis_local_atom hc hR H J U hs hb hj
  let δ := min d (min 1 (c / (2 * R)))
  refine ⟨δ, lt_min hd (lt_min zero_lt_one (div_pos hc (mul_pos two_pos hR))), K, ?_⟩
  intro η hη hsmall t ht
  have hη1 : η ≤ 1 := hsmall.trans ((min_le_right d _).trans (min_le_left _ _))
  have hr := (le_div_iff₀ (mul_pos two_pos hR)).mp
    (hsmall.trans ((min_le_right d _).trans (min_le_right _ _)))
  have hsup : tsupport (H η t) ⊆ Icc (c - R * η) (c + R * η) := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    have h := abs_le.mp (hs η hη hη1 t ht x hx)
    exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have hpos : tsupport (H η t) ⊆ Ioi 0 := by
    intro x hx
    have h := (hsup hx).1
    change 0 < x
    nlinarith [mul_comm η (2 * R)]
  have hsum := hef (H η t) (hreg η hη hη1 t ht).1 (hreg η hη hη1 t ht).2 hpos
  refine ⟨hsum.summable, ?_⟩
  have hvalue := hsum.tsum_eq
  rw [hpole η hη hη1 t ht, zero_add] at hvalue
  rw [hvalue, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  exact he η hη (hsmall.trans (min_le_left d _)) t ht

/-- The full zero sum of the canonical four-moment test recovers the signed prime
atom with a uniform linear error on every bounded set of translation parameters. -/
theorem profile_fullZeroSum_local_atom (hef : PositiveAxisExplicitFormula)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ Icc (-1) 1)
    {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) :
    ∃ δ > 0, ∃ K : ℝ, ∀ η, 0 < η → η ≤ δ → ∀ t ∈ Icc (-T) T,
      Summable (zeroTerm (profile g η c t)) ∧
        ‖(∑' ρ : zetaZeros, zeroTerm (profile g η c t) ρ) +
        ((atomWeight c * iteratedDeriv 4 g (-t) : ℝ) : ℂ)‖ ≤ K * η := by
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  obtain ⟨A, E, _, _, hbound⟩ := profile_physical_bounds hg hgc
  apply fullZeroSum_local_atom (R := T + 1) (A := A) (E := E) hef hc (by linarith)
    (fun η t ↦ profile g η c t) (fun t ↦ iteratedDeriv 4 g (-t)) (Icc (-T) T)
    (fun _ hη _ t _ ↦ profile_smooth_compact hg hs hη c t)
    (fun _ hη _ t _ ↦ profile_four_moments hg hgc hη c t 1 (Or.inr (Or.inr (Or.inr rfl))))
  · exact fun _ hη _ _ ht _ hx ↦ profile_dist_le_of_ne_zero hs hη (abs_le.mpr ht) hx
  · exact fun η hη hη1 t _ ↦ (hbound η hη hη1 c t).1
  · exact fun η hη hη1 t _ ↦ (hbound η hη hη1 c t).2

end RiemannMasullo.PrimeShrink
