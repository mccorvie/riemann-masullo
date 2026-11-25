module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import RiemannMasullo.ForMathlib.Analysis.Meromorphic.VerticalStripZeros
public import RiemannMasullo.ForMathlib.Analysis.Fourier.PolarLaplaceProbe
public import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumLowerGrowth
import Mathlib.Tactic

/-! # Principal-row coefficients for nested spectral widths -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Asymptotics BigOperators ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.PrincipalLostJets

set_option quotPrecheck false

variable (F : Type*) [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "L(" η ")" => continuedCompletedHeckeL (F := F) η
/-- The divisor of the completed Hecke function for the genuine trivial character. -/
def principalOrder (ρ : ℂ) : ℤ :=
  MeromorphicOn.divisor (L((1 : PontryaginDual C𝔽))) univ ρ

/-- The principal divisor agrees with the finite part of the meromorphic order. -/
theorem principalOrder_eq (ρ : ℂ) : principalOrder F ρ =
    (meromorphicOrderAt (L((1 : PontryaginDual C𝔽))) ρ).untop₀ :=
  MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (1 : PontryaginDual C𝔽)).1.meromorphicOn
    (mem_univ ρ)

/-- A site is the frequency `w = ρ − a`. Each genuine zero in the closed wide strip
appears once, independently of how many derivatives survive at that zero. -/
def principalSites (a β : ℝ) : Set ℂ :=
  {w : ℂ | |w.re| ≤ β ∧ 0 < principalOrder F (w + (a : ℂ))}

private theorem principalSite_re_le {a β : ℝ} (i : principalSites F a β) : i.val.re ≤ β :=
  (abs_le.mp i.property.1).2

/-- In shifted spectral coordinates, genuine principal zero sites form a locally finite set. -/
theorem principalSite_discrete (a β : ℝ) (z : ℂ) :
    ∀ᶠ u in 𝓝[≠] z, u ∉ range (Subtype.val : principalSites F a β → ℂ) := by
  have hD := (MeromorphicOn.divisor (L((1 : PontryaginDual C𝔽))) univ).eq_zero_codiscreteWithin
  have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hD) (z + (a : ℂ)) (mem_univ _)
  rw [compl_univ, union_empty] at h
  have ht : Tendsto (fun u : ℂ ↦ u + a) (𝓝[≠] z) (𝓝[≠] (z + a)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_id.add continuous_const).tendsto z).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact fun he ↦ hu (add_right_cancel he)
  filter_upwards [ht.eventually h] with u hu
  rintro ⟨i, rfl⟩
  change principalOrder F (i.val + (a : ℂ)) = 0 at hu
  exact (ne_of_gt i.property.2) hu

/-- Width monotonicity includes a zero-width narrow interval and both edges. -/
theorem stripMultiplicity_mono {α β : ℝ} (hα : 0 ≤ α) (hαβ : α < β) (s b : ℝ) (m : ℕ) :
    spectralStripMultiplicity α s b m ≤ spectralStripMultiplicity β s b m := by
  by_cases hi : -α < b ∧ b < α
  · have hj : -β < b ∧ b < β := ⟨(neg_lt_neg hαβ).trans hi.1, hi.2.trans hαβ⟩
    simp [spectralStripMultiplicity, hi, hj]
  by_cases he : b = -α ∨ b = α
  · have hj : -β < b ∧ b < β := by rcases he with rfl | rfl <;> constructor <;> linarith
    simp [spectralStripMultiplicity, hi, he, hj, spectralBoundaryMultiplicity]
  · simp [spectralStripMultiplicity, hi, he]

/-- The multiplicity retained by a given width at a genuine principal site. -/
def retainedJets {a β : ℝ} (γ s : ℝ) (i : principalSites F a β) : ℕ :=
  spectralStripMultiplicity γ s i.val.re (principalOrder F (i.val + (a : ℂ))).toNat

/-- The number of jet orders lost upon restricting from width `β` to width `α`. -/
def jetLoss {a β : ℝ} (α s : ℝ) (i : principalSites F a β) : ℕ :=
  retainedJets F β s i - retainedJets F α s i

/-- Subtracting the retained jet orders in the two widths gives the signed complex coefficient. -/
theorem cast_jetLoss {a α β s : ℝ} (hα : 0 ≤ α) (hαβ : α < β) (i : principalSites F a β) :
    (jetLoss F α s i : ℂ) =
      (retainedJets F β s i : ℂ) - (retainedJets F α s i : ℂ) := by
  exact Nat.cast_sub (stripMultiplicity_mono hα hαβ s i.val.re _)

/-- The inverse-square moment of the actual positive principal divisor on a closed strip.
Jensen's bound uses only the polynomial strip estimates for the finite Hecke function
and its reciprocal on one vertical line. -/
theorem principalSite_weighted_summable (a β : ℝ) :
    Summable (fun i : principalSites F a β ↦
      ((principalOrder F (i.val + (a : ℂ))).toNat : ℝ) / (1 + |i.val.im|) ^ 2) := by
  let η : PontryaginDual C𝔽 := 1
  let Λ := continuedCompletedHeckeL (F := F) η
  let G (z : ℂ) := (heckeGammaFactor η z)⁻¹
  let f := toMeromorphicNFOn (G * Λ) univ
  have hΛ : MeromorphicNFOn Λ univ := (continuedCompletedHeckeL_spec η).1
  have hG : Differentiable ℂ G := differentiable_inv_heckeGammaFactor η
  have hm : MeromorphicOn (G * Λ) univ := fun z hz ↦
    (hG.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  have hf : MeromorphicNFOn f univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have agree (s : Complex.re ⁻¹' Ioi (1 : ℝ)) : f s = finiteHeckeL η s := by
    have hγ := heckeGammaFactor_ne_zero_of_re_pos η (zero_lt_one.trans s.property)
    have hg : G s ≠ 0 := inv_ne_zero hγ
    have hn : MeromorphicNFAt (G * Λ) s :=
      (meromorphicNFAt_mul_iff_right (hG.analyticAt s) hg).2 (hΛ (mem_univ _))
    change toMeromorphicNFOn (G * Λ) univ s = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _), toMeromorphicNFAt_eq_self.mpr hn]
    simp [Pi.mul_apply, G, Λ, (continuedCompletedHeckeL_spec η).2 s, completedHeckeL,
      finiteHeckeL, hγ]
  have hcomp (z : ℂ) : meromorphicOrderAt Λ z ≤ meromorphicOrderAt f z := by
    change _ ≤ meromorphicOrderAt (toMeromorphicNFOn (G * Λ) univ) z
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _),
      meromorphicOrderAt_mul (hG.analyticAt z).meromorphicAt (hΛ (mem_univ z)).meromorphicAt]
    exact le_add_of_nonneg_left (hG.analyticAt z).meromorphicOrderAt_nonneg
  obtain ⟨hline, k, _, hinv⟩ := finiteHeckeL_inv_isBigO_oneLine η f hf agree
  have hw := summable_divisor_div_one_add_abs_im_sq hΛ.meromorphicOn hf hcomp
    (finiteHeckeL_continuation_isBigO_rpow η f hf agree) (hline.mono fun _ ht ↦ ht.2)
    hinv a (β + 1)
  let E := {ρ : ℂ // 0 < MeromorphicOn.divisor Λ univ ρ ∧ |ρ.re - a| < β + 1}
  let emb (i : principalSites F a β) : E :=
    ⟨i.val + (a : ℂ), i.property.2, by
      simpa only [Complex.add_re, Complex.ofReal_re, add_sub_cancel_right] using
        (lt_add_of_le_of_pos i.property.1 zero_lt_one : |i.val.re| < β + 1)⟩
  have hj : Injective emb := fun i j hij ↦
    Subtype.ext (add_right_cancel (congrArg (fun z : E ↦ z.val) hij))
  have hc (i : principalSites F a β) :
      ((principalOrder F (i.val + (a : ℂ))).toNat : ℝ) =
        (principalOrder F (i.val + (a : ℂ)) : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg i.property.2.le
  have hs := hw.comp_injective hj
  refine hs.congr (fun i ↦ ?_)
  change ((principalOrder F (i.val + (a : ℂ)) : ℝ) / (1 + |(i.val + (a : ℂ)).im|) ^ 2) = _
  rw [Complex.add_im, Complex.ofReal_im, add_zero, hc i]

/-- Coefficients at distinct zero sites, with the surviving jet orders collected. -/
def coefficient {a β : ℝ} (α s : ℝ) (K : ℂ → ℂ) (i : principalSites F a β) : ℂ :=
  (jetLoss F α s i : ℂ) * K i.val

private theorem spectralStripMultiplicity_le (α s b : ℝ) (m : ℕ) :
    spectralStripMultiplicity α s b m ≤ m := by
  unfold spectralStripMultiplicity
  split
  · exact le_rfl
  · split
    · exact min_le_left _ _
    · exact Nat.zero_le _

/-- Absolute summability for any function with a uniform inverse-square bound on the strip. -/
theorem coefficient_summable_of_decay (a α β s : ℝ) (K : ℂ → ℂ)
    {D : ℝ} (hD : ∀ z : ℂ, |z.re| ≤ β → ‖K z‖ ≤ D / (1 + |z.im|) ^ 2) :
    Summable (coefficient F (a := a) (β := β) α s K) := by
  apply Summable.of_norm_bounded ((principalSite_weighted_summable F a β).mul_left D)
  intro i
  let m := (principalOrder F (i.val + (a : ℂ))).toNat
  have hj : jetLoss F α s i ≤ m :=
    (Nat.sub_le _ _).trans (spectralStripMultiplicity_le β s i.val.re m)
  rw [coefficient, norm_mul, Complex.norm_natCast]
  calc
    (jetLoss F α s i : ℝ) * ‖K i.val‖ ≤ (m : ℝ) * ‖K i.val‖ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hj) (norm_nonneg _)
    _ ≤ (m : ℝ) * (D / (1 + |i.val.im|) ^ 2) :=
      mul_le_mul_of_nonneg_left (hD _ i.property.1) (Nat.cast_nonneg _)
    _ = D * ((m : ℝ) / (1 + |i.val.im|) ^ 2) := by ring

/-- The actual principal-row coefficients of one fixed compact smooth profile are absolutely
summable, unconditionally, for every center and both widths. -/
theorem coefficient_summable (a α β s : ℝ) (H : ℝ → ℂ) (hs : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) :
    Summable (coefficient F (a := a) (β := β) α s (bilateralLaplace H)) := by
  obtain ⟨D, hD⟩ := exists_bilateralLaplace_inverseSquare_bound H hs hc β
  exact coefficient_summable_of_decay F a α β s (bilateralLaplace H) hD

/-- A site interior to the wide strip and strictly outside the narrow strip loses its full order. -/
theorem jetLoss_eq_order_of_between {a α β s : ℝ} (i : principalSites F a β)
    (hα : 0 ≤ α) (hin : -β < i.val.re ∧ i.val.re < β) (hout : α < |i.val.re|) :
    jetLoss F α s i = (principalOrder F (i.val + (a : ℂ))).toNat := by
  have hni : ¬(-α < i.val.re ∧ i.val.re < α) := fun h ↦
    (not_lt.mpr (abs_le.mpr ⟨h.1.le, h.2.le⟩)) hout
  have hne : ¬(i.val.re = -α ∨ i.val.re = α) := by
    rintro (he | he) <;> simp [he, abs_of_nonneg hα] at hout
  simp [jetLoss, retainedJets, spectralStripMultiplicity, hin, hni, hne]

/-- A detected loss forces arbitrarily late growth in the signed principal-row scalar.
The test-translation and physical operator identities can be applied separately. -/
theorem frequently_exp_lt_principal_lostJet_of_compact (a α : ℝ) {β s : ℝ}
    (H : ℝ → ℂ) (hs : ContDiff ℝ (∞) H) (hcs : HasCompactSupport H) {i : principalSites F a β}
    (hi : 0 < jetLoss F α s i) (hKi : bilateralLaplace H i.val ≠ 0)
    {c : ℝ} (hc : c < i.val.re) (C : ℝ) :
    ∃ᶠ y : ℝ in atTop, C * Real.exp (c * y) <
      ‖∑' j : principalSites F a β,
        coefficient F α s (bilateralLaplace H) j * Complex.exp (j.val * y)‖ := by
  apply frequently_exp_lt_norm_tsum_exp (Subtype.val : principalSites F a β → ℂ)
    (coefficient F α s (bilateralLaplace H)) Subtype.coe_injective (principalSite_discrete F a β)
    (principalSite_re_le F) (coefficient_summable F a α β s H hs hcs) (i := i) _ hc C
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hi.ne') hKi

end RiemannMasullo.PrincipalLostJets
