module

public import RiemannMasullo.External.FermatDixmierMalliavin.OneParameter
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Convolution factorization inside positive time

The repository's checked one-parameter Dixmier–Malliavin theorem gives factors
with small two-sided support. Opposite translations move both factors strictly
into positive time while preserving their convolution. This allows factorization
for forward semigroup actions, without assuming a backwards action.
-/

public noncomputable section
open Set Function MeasureTheory
open scoped ContDiff SchwartzMap
namespace RiemannMasullo

private theorem positive_factorization_log (f : ℝ → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ Φ : ℝ → ℂ, ContDiff ℝ (⊤ : ℕ∞) Φ ∧ tsupport Φ ⊆ Real.exp '' tsupport f ∧
      ∀ s, Φ (Real.exp s) = f s := by
  let Φ (y : ℝ) := if 0 < y then f (Real.log y) else 0
  have hK := hc.isCompact.image Real.continuous_exp
  have hs : tsupport Φ ⊆ Real.exp '' tsupport f := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_cases h : 0 < y
    · exact ⟨Real.log y, subset_tsupport f (by simpa [Φ, h, mem_support] using hy), Real.exp_log h⟩
    · exact ((mem_support.mp hy) (ite_eq_right h)).elim
  refine ⟨Φ, contDiff_iff_contDiffAt.mpr fun y ↦ ?_, hs, fun s ↦ by simp [Φ, Real.exp_pos]⟩
  by_cases h : 0 < y
  · apply (hf.contDiffAt.comp y (Real.contDiffAt_log.mpr h.ne')).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds h] with z hz using ite_eq_left hz
  · have hy : y ∉ tsupport Φ := fun hy ↦ by
      obtain ⟨s, _, rfl⟩ := hs hy
      exact h (Real.exp_pos s)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)

private theorem compact_factorization_small (f : 𝓢(ℝ, ℂ)) (hc : HasCompactSupport f)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ g φ ψ : 𝓢(ℝ, ℂ), HasCompactSupport g ∧ tsupport g ⊆ tsupport f ∧
      tsupport φ ⊆ Icc (-ε) ε ∧ tsupport ψ ⊆ Icc (-ε) ε ∧
      ∀ x, f x = (∫ t : ℝ, φ t * g (x + t)) + ∫ t : ℝ, ψ t * f (x + t) := by
  obtain ⟨Φ, hΦ, hΦs, hΦexp⟩ := positive_factorization_log f (f.smooth _) hc
  have hΦc : HasCompactSupport Φ :=
    (hc.isCompact.image Real.continuous_exp).of_isClosed_subset (isClosed_tsupport _) hΦs
  obtain ⟨Φ₁, φ, ψ, h₁, hs₁, hφ, hψ, hsφ, hsψ, heq⟩ :=
    DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add (1 : ℝ) ε hε Φ hΦ hΦc
  have hgs : tsupport (Φ₁ ∘ Real.exp) ⊆ tsupport f := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro t ht
    have hh := hΦs (hs₁ (subset_tsupport Φ₁ ht))
    obtain ⟨s, hs, he⟩ := hh
    exact Real.exp_injective he ▸ hs
  have hgc : HasCompactSupport (Φ₁ ∘ Real.exp) :=
    hc.isCompact.of_isClosed_subset (isClosed_tsupport _) hgs
  have hφc : HasCompactSupport φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ
  have hψc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsψ
  let g := hgc.toSchwartzMap (h₁.comp Real.contDiff_exp)
  let φ' := hφc.toSchwartzMap hφ
  let ψ' := hψc.toSchwartzMap hψ
  refine ⟨g, φ', ψ', hgc, hgs, hsφ, hsψ, fun x ↦ ?_⟩
  simpa only [smul_eq_mul, mul_one, ← Real.exp_eq_exp_ℝ, ← Real.exp_add, hΦexp, comp_apply]
    using! heq (Real.exp x)

private theorem positive_shifted_factors (φ g : 𝓢(ℝ, ℂ)) (hgc : HasCompactSupport g)
    (a : ℝ) (ha : 0 < a) (hφ : tsupport φ ⊆ Icc (-(a / 4)) (a / 4))
    (hg : ∀ t ∈ tsupport g, a ≤ t) :
    ∃ u v : 𝓢(ℝ, ℂ),
      (HasCompactSupport u ∧ tsupport u ⊆ Ioi 0) ∧
      (HasCompactSupport v ∧ tsupport v ⊆ Ioi 0) ∧
      ∀ x, (∫ t : ℝ, φ t * g (x + t)) = ∫ t : ℝ, u t * v (x - t) := by
  have hφc : HasCompactSupport φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hφ
  let e := Homeomorph.subLeft (a / 2)
  let d := Homeomorph.addRight (a / 2)
  let hu := hφc.comp_homeomorph e
  let hv := hgc.comp_homeomorph d
  let u := hu.toSchwartzMap ((φ.smooth _).comp (contDiff_const.sub contDiff_id))
  let v := hv.toSchwartzMap ((g.smooth _).comp (contDiff_id.add contDiff_const))
  refine ⟨u, v, ⟨hu, ?_⟩, ⟨hv, ?_⟩, fun x ↦ ?_⟩
  · intro t ht
    have hh : a / 2 - t ∈ tsupport φ := by
      exact (Set.ext_iff.mp (tsupport_comp_eq_preimage φ e) t).mp ht
    have hb := (hφ hh).2
    change 0 < t
    linarith
  · intro t ht
    have hh : t + a / 2 ∈ tsupport g := by
      exact (Set.ext_iff.mp (tsupport_comp_eq_preimage g d) t).mp ht
    have hb := hg _ hh
    change 0 < t
    linarith
  · have he := integral_sub_left_eq_self (fun t : ℝ ↦ φ t * g (x + t)) volume (a / 2)
    convert he.symm using 1
    apply integral_congr_ae
    filter_upwards with t
    change φ (a / 2 - t) * g (x - t + a / 2) = φ (a / 2 - t) * g (x + (a / 2 - t))
    rw [show x - t + a / 2 = x + (a / 2 - t) by ring]

/-- Positive-time Dixmier–Malliavin factorization: a smooth test compactly
supported inside `(0,∞)` is a sum of two convolutions of tests with the same
support condition. This uses the repository's checked one-parameter theorem. -/
theorem positive_compact_schwartz_factorization (f : 𝓢(ℝ, ℂ))
    (hc : HasCompactSupport f) (hp : tsupport f ⊆ Ioi 0) :
    ∃ u v r s : 𝓢(ℝ, ℂ),
      (HasCompactSupport u ∧ tsupport u ⊆ Ioi 0) ∧
      (HasCompactSupport v ∧ tsupport v ⊆ Ioi 0) ∧
      (HasCompactSupport r ∧ tsupport r ⊆ Ioi 0) ∧
      (HasCompactSupport s ∧ tsupport s ⊆ Ioi 0) ∧
      ∀ x, f x = (∫ t : ℝ, u t * v (x - t)) + ∫ t : ℝ, r t * s (x - t) := by
  obtain ⟨a, ha, hamin⟩ := hc.isCompact.exists_forall_le' (a := (0 : ℝ)) continuous_id.continuousOn
    (fun t ht ↦ hp ht)
  obtain ⟨g, φ, ψ, hgc, hgs, hφ, hψ, hf⟩ := compact_factorization_small f hc (a / 4) (by positivity)
  obtain ⟨u, v, hu, hv, huv⟩ := positive_shifted_factors φ g hgc a ha hφ
    (fun t ht ↦ hamin t (hgs ht))
  obtain ⟨r, s, hr, hs, hrs⟩ := positive_shifted_factors ψ f hc a ha hψ hamin
  exact ⟨u, v, r, s, hu, hv, hr, hs, fun x ↦ (hf x).trans (congrArg₂ (· + ·) (huv x) (hrs x))⟩

end RiemannMasullo
