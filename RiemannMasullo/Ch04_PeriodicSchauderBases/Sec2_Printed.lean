module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # Chapter 4.2: the printed fixed-support periodization claims -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function Set TopologicalSpace
open scoped Distributions

local notation "D[" K "]" => 𝓓_{K}(ℝ, ℂ)
local notation "quotientAt[" γ "]" => fun x : ℝ ↦ ((x / Real.log γ : ℝ) : AddCircle (1 : ℝ))

/-- Paper: Proposition 4.2.2.2(1), p. 171. As printed: for γ > 1, if a compact support
set has nonempty interior and maps onto the cyclic quotient, the induced periodization
on the fixed-support space modulo its kernel is surjective. This is the surjectivity
part of the stated isomorphism, in log coordinates. `compactIntervalPeriodization_quotient_equiv`
gives the strict-width interval case. See ERRATA F15. -/
def Printed.compactPeriodization_surjective : Prop :=
  ∀ (γ : ℝ) (hγ : 1 < γ) (K : Compacts ℝ), (interior (K : Set ℝ)).Nonempty →
    SurjOn (quotientAt[γ]) (K : Set ℝ) univ →
    Surjective ((cyclicPeriodizationCLM γ hγ).comp (compactLogProfileInclusion K))

/-- Paper: Proposition 4.2.2.2(1), p. 171. For γ > 1 take the multiplicative support
interval [1, γ], so K = [0, log γ] in log coordinates. It covers the quotient, but
every smooth function supported there vanishes at both endpoints. Its periodization
vanishes at the zero class, so the constant one is missed. -/
theorem Printed.compactPeriodization_surjective_false :
    ¬ Printed.compactPeriodization_surjective := by
  intro h
  have hγ : (1 : ℝ) < 2 := one_lt_two
  have hl : 0 < Real.log 2 := Real.log_pos hγ
  let K : Compacts ℝ := ⟨Icc 0 (Real.log 2), isCompact_Icc⟩
  have hint : (interior (K : Set ℝ)).Nonempty := by
    refine ⟨Real.log 2 / 2, ?_⟩
    change Real.log 2 / 2 ∈ interior (Icc 0 (Real.log 2))
    rw [interior_Icc]
    constructor <;> linarith
  have hsurj : SurjOn (fun x : ℝ ↦ ((x / Real.log 2 : ℝ) : AddCircle (1 : ℝ)))
      (K : Set ℝ) univ := by
    intro z _
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    refine ⟨Int.fract x * Real.log 2,
      ⟨by have := Int.fract_nonneg x; positivity,
       by have := Int.fract_lt_one x; nlinarith⟩, ?_⟩
    simp only [mul_div_assoc, div_self hl.ne', mul_one]
    rw [← Int.self_sub_floor, AddCircle.coe_sub]
    simp
  obtain ⟨φ, hφ⟩ := h 2 hγ K hint hsurj (cyclicExponential 0)
  have hclos : ∀ x : ℝ, (x ≤ 0 ∨ Real.log 2 ≤ x) → φ x = 0 := by
    have hsub : closure ((K : Set ℝ)ᶜ) ⊆ {y | φ y = 0} :=
      closure_minimal (fun y hy ↦ φ.zero_on_compl hy)
        (isClosed_eq φ.continuous continuous_const)
    intro x hx
    apply hsub
    rcases hx with hx | hx
    · have hs : Iio (0 : ℝ) ⊆ (K : Set ℝ)ᶜ := fun y hy hyK ↦ absurd hyK.1 (not_le.mpr hy)
      exact closure_mono hs (by rw [closure_Iio]; exact hx)
    · have hs : Ioi (Real.log 2) ⊆ (K : Set ℝ)ᶜ :=
        fun y hy hyK ↦ absurd hyK.2 (not_le.mpr hy)
      exact closure_mono hs (by rw [closure_Ioi]; exact hx)
  have hsum := cyclicPeriodization_hasSum 2 hγ (compactLogProfileInclusion K φ) 0
  have hterms : ∀ k : ℤ,
      (compactLogProfileInclusion K φ).val (0 + (k : ℝ) * Real.log 2) = 0 := by
    intro k
    change φ (0 + (k : ℝ) * Real.log 2) = 0
    apply hclos
    rcases le_or_gt k 0 with hk | hk
    · left
      have : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      nlinarith
    · right
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
  have h0 := hsum.unique
    (by simpa only [hterms] using (hasSum_zero : HasSum (fun _ : ℤ ↦ (0 : ℂ)) 0))
  have h1 := cyclicExponential_apply 2 hγ 0 0
  simp only [Int.cast_zero, mul_zero, zero_div, Complex.ofReal_zero, Complex.exp_zero] at h1
  have h2 := congrFun (congrArg Subtype.val hφ)
    (0, fun _ : Fin 1 ↦ ((0 / Real.log 2 : ℝ) : AddCircle (1 : ℝ)), 0, PUnit.unit)
  exact one_ne_zero (h1.symm.trans (h2.symm.trans h0))

/-- Paper: Proposition 4.2.2.2(2), p. 171. As printed: for an admissible support
interval `b · [1/a, a]` contained in `[1/A₀, A₀]`, every kernel element is the difference
of a smooth function supported in `[exp(-A), exp A]` and its translate by γ, where
`A = |log A₀ - log γ|`. The variables and supports on the function side use log
coordinates. The strict-width case of the preceding part is
`compactIntervalPeriodization_quotient_equiv`. See ERRATA F15. -/
def Printed.compactIntervalPeriodization_kernel_support : Prop :=
  ∀ (γ : ℝ) (hγ : 1 < γ) (a b A₀ : ℝ), 1 < a → 0 < b → 0 < A₀ →
    let K : Compacts ℝ := ⟨Icc (Real.log b - Real.log a) (Real.log b + Real.log a), isCompact_Icc⟩
    (interior (K : Set ℝ)).Nonempty → SurjOn (quotientAt[γ]) (K : Set ℝ) univ →
    (K : Set ℝ) ⊆ Icc (-Real.log A₀) (Real.log A₀) →
    ∀ φ : D[K], cyclicPeriodizationCLM γ hγ (compactLogProfileInclusion K φ) = 0 →
      let A := |Real.log A₀ - Real.log γ|
      let Kₐ : Compacts ℝ := ⟨Icc (-A) A, isCompact_Icc⟩
      ∃ ψ : D[Kₐ], ∀ x : ℝ, ψ x - ψ (x + Real.log γ) = φ x

/-- Paper: Proposition 4.2.2.2(2), p. 171. Set a = A₀ = γ > 1 and b = 1. Then A = 0,
so every smooth function supported in the allowed singleton is zero. Take a nonzero
smooth bump u supported in `(0, log γ)` in log coordinates. The difference
`u(x) - u(x + log γ)` is nonzero, is supported in `[-log γ, log γ]`, and has zero
periodization by reindexing the sum. -/
theorem Printed.compactIntervalPeriodization_kernel_support_false :
    ¬ Printed.compactIntervalPeriodization_kernel_support := by
  intro h
  have hγ : (1 : ℝ) < 2 := one_lt_two
  have hl : 0 < Real.log 2 := Real.log_pos hγ
  let K : Compacts ℝ :=
    ⟨Icc (Real.log 1 - Real.log 2) (Real.log 1 + Real.log 2), isCompact_Icc⟩
  have hK : (K : Set ℝ) = Icc (-Real.log 2) (Real.log 2) := by
    change Icc (Real.log 1 - Real.log 2) (Real.log 1 + Real.log 2) = _
    rw [Real.log_one, zero_sub, zero_add]
  let β : ContDiffBump (Real.log 2 / 2) :=
    ⟨Real.log 2 / 8, Real.log 2 / 4, by positivity, by linarith⟩
  have hβ : ∀ x, x ≤ 0 ∨ Real.log 2 ≤ x → β x = 0 := by
    intro x hx
    rw [← Function.notMem_support, β.support_eq, Real.ball_eq_Ioo]
    change ¬ (x ∈ Ioo (Real.log 2 / 2 - Real.log 2 / 4) (Real.log 2 / 2 + Real.log 2 / 4))
    rintro ⟨h1, h2⟩
    rcases hx with hx | hx <;> linarith
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x ↦ (β x : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp β.contDiff
  let u : 𝓓_{K}(ℝ, ℂ) := ⟨fun x ↦ (β x : ℂ), hcd, by
    intro x hx
    rw [hK] at hx
    simp only [Pi.zero_apply, Complex.ofReal_eq_zero]
    apply hβ
    by_contra hc
    push Not at hc
    exact hx ⟨by linarith [hc.1], hc.2.le⟩⟩
  let φ : 𝓓_{K}(ℝ, ℂ) := ⟨fun x ↦ (β x : ℂ) - (β (x + Real.log 2) : ℂ),
    hcd.sub (hcd.comp (contDiff_id.add contDiff_const)), by
    intro x hx
    rw [hK] at hx
    simp only [Pi.zero_apply]
    have hx' : x < -Real.log 2 ∨ Real.log 2 < x := by
      by_contra hc
      push Not at hc
      exact hx ⟨hc.1, hc.2⟩
    rw [hβ x (by rcases hx' with hx' | hx' <;> [left; right] <;> linarith),
      hβ (x + Real.log 2) (by rcases hx' with hx' | hx' <;> [left; right] <;> linarith)]
    simp⟩
  have hint : (interior (K : Set ℝ)).Nonempty := by
    refine ⟨0, ?_⟩
    rw [hK, interior_Icc]
    constructor <;> linarith
  have hsurj : SurjOn (fun x : ℝ ↦ ((x / Real.log 2 : ℝ) : AddCircle (1 : ℝ)))
      (K : Set ℝ) univ := by
    intro z _
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    refine ⟨Int.fract x * Real.log 2, ?_, ?_⟩
    · rw [hK]
      have := Int.fract_nonneg x
      have := Int.fract_lt_one x
      constructor <;> nlinarith
    · simp only [mul_div_assoc, div_self hl.ne', mul_one]
      rw [← Int.self_sub_floor, AddCircle.coe_sub]
      simp
  have hsub : (K : Set ℝ) ⊆ Icc (-Real.log 2) (Real.log 2) := hK.le
  have hker : cyclicPeriodizationCLM 2 hγ (compactLogProfileInclusion K φ) = 0 := by
    apply Subtype.ext
    funext g
    obtain ⟨a, z, c, d⟩ := g
    obtain rfl : a = 0 := Subsingleton.elim _ _
    obtain rfl : c = 0 := Subsingleton.elim _ _
    obtain ⟨t, ht⟩ := QuotientAddGroup.mk_surjective (z 0)
    obtain rfl :
        z = fun _ : Fin 1 ↦ ((t * Real.log 2 / Real.log 2 : ℝ) : AddCircle (1 : ℝ)) := by
      funext i
      fin_cases i
      rw [mul_div_assoc, div_self hl.ne', mul_one]
      exact ht.symm
    cases d
    have hφs := cyclicPeriodization_hasSum 2 hγ (compactLogProfileInclusion K φ) (t * Real.log 2)
    have hus := cyclicPeriodization_hasSum 2 hγ (compactLogProfileInclusion K u) (t * Real.log 2)
    have hsh := ((Equiv.addRight (1 : ℤ)).hasSum_iff).mpr hus
    have hd := hus.sub hsh
    rw [sub_self] at hd
    refine hφs.unique (hd.congr_fun fun k ↦ ?_)
    change (β (t * Real.log 2 + k * Real.log 2) : ℂ) -
        β (t * Real.log 2 + k * Real.log 2 + Real.log 2) =
      (β (t * Real.log 2 + k * Real.log 2) : ℂ) -
        β (t * Real.log 2 + ((k + 1 : ℤ) : ℝ) * Real.log 2)
    push_cast
    ring_nf
  obtain ⟨ψ, hψ⟩ := h 2 hγ 2 1 2 hγ one_pos two_pos hint hsurj (by simp) φ hker
  have hψ0 : ∀ x : ℝ, 0 < x → ψ x = 0 := by
    intro x hx
    apply ψ.zero_on_compl
    intro hmem
    have := hmem.2
    simp only [sub_self, abs_zero] at this
    linarith
  have key := hψ (Real.log 2 / 2)
  rw [hψ0 _ (by positivity), hψ0 _ (by positivity)] at key
  change (0 : ℂ) - 0 = (β (Real.log 2 / 2) : ℂ) - β (Real.log 2 / 2 + Real.log 2) at key
  rw [β.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)),
    hβ _ (Or.inr (by linarith))] at key
  norm_num at key

end RiemannMasullo
