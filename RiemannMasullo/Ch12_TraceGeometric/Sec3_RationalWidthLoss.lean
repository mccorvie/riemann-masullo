module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.Ch13_ZerosHecke.Targets
public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.ShrinkingHeightKernel
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Tactic

/-! # The rational principal divisor outside a centered vertical band -/

@[expose] public noncomputable section

open Filter Function NumberField Set
open scoped BigOperators ComplexConjugate NumberField.AdeleRing Topology

namespace RiemannMasullo.RationalWidthLoss

local notation "η₀" => (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
local notation "Λ₀" => continuedCompletedHeckeL (F := ℚ) η₀
local notation "m₀" => MeromorphicOn.divisor Λ₀ univ

/-- Each distinct positive-order zero of the actual completed rational principal function. -/
def zeroSites : Set ℂ := {ρ : ℂ | 0 < m₀ ρ}

/-- The full multiplicity of a principal zero before the Sobolev width cutoff. -/
def multiplicity (ρ : zeroSites) : ℕ := (m₀ ρ.val).toNat

private theorem positive_order (ρ : zeroSites) : 0 < meromorphicOrderAt Λ₀ ρ.val := by
  have h := ρ.property
  change 0 < m₀ ρ.val at h
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec η₀).1.meromorphicOn (mem_univ _)] at h
  cases he : meromorphicOrderAt Λ₀ ρ.val with
  | top => simp
  | coe k =>
    rw [he, WithTop.untop₀_coe] at h
    exact_mod_cast h

private theorem ordinary_order_eq_principal {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt riemannZeta z = meromorphicOrderAt Λ₀ z := by
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  exact meromorphicOrderAt_finiteHeckeL_continuation η₀ hm (fun s ↦ by
    rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property]) hz

/-- In the positive half-plane the completed principal order is the ordinary zeta order
used by the classical density theorem. -/
theorem multiplicity_eq_zeta_order (ρ : zeroSites) (hρ : 0 < ρ.val.re) :
    multiplicity ρ = (meromorphicOrderAt riemannZeta ρ.val).untop₀.toNat := by
  have he := ordinary_order_eq_principal hρ
  rw [multiplicity, MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec η₀).1.meromorphicOn
    (mem_univ _), ← he]

private theorem reflected_order (ρ : ℂ) : m₀ (1 - ρ) = m₀ ρ := by
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec η₀
  obtain ⟨ε, hε, hn, he⟩ := completedHeckeL_continuation_functionalEquation η₀ Λ₀ Λ₀
    hL heq hL (by simpa using heq)
  let f := fun z : ℂ ↦ 1 - z
  have hc := meromorphicOrderAt_comp_of_deriv_ne_zero (f := Λ₀)
    (show AnalyticAt ℂ f ρ by dsimp [f]; fun_prop) (show deriv f ρ ≠ 0 by simp [f])
  have he' : Λ₀ ∘ f = ε * Λ₀ := funext he
  rw [he', meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt ρ) (hn ρ)] at hc
  simp only [MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _)]
  exact congrArg WithTop.untop₀ hc.symm

private theorem completedZeta_meromorphic : MeromorphicOn completedRiemannZeta univ := by
  rw [show completedRiemannZeta = (fun z : ℂ ↦ completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) from
    funext completedRiemannZeta_eq]
  intro z _
  exact ((differentiable_completedZeta₀.analyticAt z).meromorphicAt.sub
    (analyticAt_const.meromorphicAt.div analyticAt_id.meromorphicAt)).sub
    (analyticAt_const.meromorphicAt.div (analyticAt_const.sub analyticAt_id).meromorphicAt)

private theorem completedZeta_reflected_order (z : ℂ) :
    meromorphicOrderAt completedRiemannZeta (1 - z) = meromorphicOrderAt completedRiemannZeta z := by
  let f := fun s : ℂ ↦ 1 - s
  have hc := meromorphicOrderAt_comp_of_deriv_ne_zero (f := completedRiemannZeta)
    (show AnalyticAt ℂ f z by dsimp [f]; fun_prop) (show deriv f z ≠ 0 by simp [f])
  have he : completedRiemannZeta ∘ f = completedRiemannZeta := funext completedRiemannZeta_one_sub
  rw [he] at hc
  exact hc.symm

private theorem zeta_order_eq_idelic_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    meromorphicOrderAt completedRiemannZeta z = meromorphicOrderAt Λ₀ z := by
  have hi := ordinary_order_eq_principal hz
  let G := fun s : ℂ ↦ (Complex.Gammaℝ s)⁻¹
  have hnear : ∀ᶠ s : ℂ in 𝓝 z, 0 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
  have hpos : ∀ᶠ s : ℂ in 𝓝[≠] z, 0 < s.re := hnear.filter_mono nhdsWithin_le_nhds
  have he : riemannZeta =ᶠ[𝓝[≠] z] G * completedRiemannZeta := by
    filter_upwards [hpos] with s hs
    have hne : s ≠ 0 := by rintro rfl; simp at hs
    rw [riemannZeta_def_of_ne_zero hne, Pi.mul_apply, div_eq_mul_inv, mul_comm]
  have hn : G z ≠ 0 := inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos hz)
  have hg := meromorphicOrderAt_congr he
  rw [meromorphicOrderAt_mul_of_ne_zero (Complex.differentiable_Gammaℝ_inv.analyticAt z) hn] at hg
  exact hg.symm.trans hi

/-- The actual rational principal divisor and Mathlib's completed Riemann zeta divisor
agree even at the poles. The proof compares the ordinary zeta function on the positive
half-plane, then uses both functional equations. -/
theorem principal_divisor_eq_completedRiemannZeta (z : ℂ) :
    m₀ z = MeromorphicOn.divisor completedRiemannZeta univ z := by
  have hpos (s : ℂ) (hs : 0 < s.re) : m₀ s = MeromorphicOn.divisor completedRiemannZeta univ s := by
    rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec _).1.meromorphicOn (mem_univ _),
      MeromorphicOn.divisor_apply completedZeta_meromorphic (mem_univ _), zeta_order_eq_idelic_of_re_pos hs]
  rcases lt_or_ge 0 z.re with hz | hz
  · exact hpos z hz
  · have hr : 0 < (1 - z).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    rw [← reflected_order z, hpos _ hr]
    simp only [MeromorphicOn.divisor_apply completedZeta_meromorphic (mem_univ _), completedZeta_reflected_order]

private def reflect (ρ : zeroSites) : zeroSites :=
  ⟨1 - ρ.val, by change 0 < m₀ (1 - ρ.val); rw [reflected_order]; exact ρ.property⟩

private def reflectEmbedding : zeroSites ↪ zeroSites :=
  ⟨reflect, fun _ _ h ↦ Subtype.ext (sub_right_inj.mp (congrArg Subtype.val h))⟩

private theorem multiplicity_reflect (ρ : zeroSites) : multiplicity (reflect ρ) = multiplicity ρ :=
  congrArg Int.toNat (reflected_order ρ.val)

/-- Positive principal divisor sites lie in the open critical strip. -/
theorem re_mem_Ioo (ρ : zeroSites) : ρ.val.re ∈ Ioo (0 : ℝ) 1 := by
  have hlt (z : zeroSites) : z.val.re < 1 := by
    rcases le_or_gt z.val.re 0 with h | h
    · exact h.trans_lt zero_lt_one
    · exact completedHeckeL_continuation_zeros η₀ Λ₀ (continuedCompletedHeckeL_spec _).1
        (continuedCompletedHeckeL_spec _).2 h (positive_order z)
  have hh := hlt (reflect ρ)
  change (1 - ρ.val).re < 1 at hh
  rw [Complex.sub_re, Complex.one_re] at hh
  exact ⟨by linarith, hlt ρ⟩

/-- The full multiplicity minus the jet orders lost on restricting from width `β` to width
`α`. It measures the error in replacing the lost-jet sum by the full zero sum. -/
def missingJets (α β s : ℝ) (ρ : zeroSites) : ℕ :=
  multiplicity ρ - (spectralStripMultiplicity β s ρ.val.re (multiplicity ρ) -
    spectralStripMultiplicity α s ρ.val.re (multiplicity ρ))

/-- Every site strictly between the right edge of the narrow strip and that of the wide
strip contributes its full order to the lost-jet sum. -/
theorem missingJets_eq_zero {α β s : ℝ} (hα : 0 ≤ α) {ρ : zeroSites}
    (hn : α < ρ.val.re) (hw : ρ.val.re < β) : missingJets α β s ρ = 0 := by
  have hleft : -β < ρ.val.re := by linarith
  have he : ρ.val.re ≠ -α := by linarith
  simp [missingJets, spectralStripMultiplicity, hleft, hw, not_lt.mpr hn.le, he, hn.ne']

private theorem retained_le (γ s b : ℝ) (m : ℕ) : spectralStripMultiplicity γ s b m ≤ m := by
  unfold spectralStripMultiplicity
  split
  · exact le_rfl
  split
  · exact min_le_left _ _
  · exact Nat.zero_le _

/-- For genuinely nested widths, the discarded part of the full divisor is the full
order minus the signed difference of the two prescribed Sobolev multiplicities. -/
theorem cast_missingJets {α β s : ℝ} (hα : 0 ≤ α) (hab : α < β) (ρ : zeroSites) :
    (missingJets α β s ρ : ℂ) = (multiplicity ρ : ℂ) -
      ((spectralStripMultiplicity β s ρ.val.re (multiplicity ρ) : ℂ) -
        (spectralStripMultiplicity α s ρ.val.re (multiplicity ρ) : ℂ)) := by
  let m := multiplicity ρ
  have hm : spectralStripMultiplicity α s ρ.val.re m ≤ spectralStripMultiplicity β s ρ.val.re m := by
    have hp := (re_mem_Ioo ρ).1
    by_cases h : ρ.val.re ≤ α
    · have hi : ρ.val.re ∈ Ioo (-β) β := ⟨by linarith, h.trans_lt hab⟩
      rw [spectralStripMultiplicity_interior hi]
      exact retained_le _ _ _ _
    · have he : ρ.val.re ≠ -α := by linarith
      have ha : ρ.val.re ≠ α := fun heq ↦ h heq.le
      have hn : ¬ρ.val.re < α := fun hh ↦ h hh.le
      simp [spectralStripMultiplicity, hn, he, ha]
  change ((m - (spectralStripMultiplicity β s ρ.val.re m -
    spectralStripMultiplicity α s ρ.val.re m) : ℕ) : ℂ) = _
  rw [Nat.cast_sub ((Nat.sub_le _ _).trans (retained_le _ _ _ _)), Nat.cast_sub hm]

/-- The actual orders in the two-sided right part of the critical strip. Ingham's
1940 estimate, after including conjugates, gives this bound for
`q = 3*(1-σ)/(2-σ)` and `1/2 < σ ≤ 3/4`. -/
def HasRightDensity (σ q C : ℝ) : Prop :=
  ∀ T : ℝ, 2 ≤ T → ∀ S : Finset zeroSites,
    (∀ ρ ∈ S, σ ≤ ρ.val.re ∧ |ρ.val.im| ≤ T) →
      ∑ ρ ∈ S, (multiplicity ρ : ℝ) ≤ C * T ^ q * Real.log (2 * T) ^ 5

private theorem conjugateOrder {f : ℂ → ℂ} (hm : Meromorphic f)
    (hs : ∀ z, f (conj z) = conj (f z)) (z : ℂ) :
    meromorphicOrderAt f (conj z) = meromorphicOrderAt f z := by
  have hN : Tendsto (conj : ℂ → ℂ) (𝓝 (conj z)) (𝓝 z) := by
    simpa using Complex.continuous_conj.tendsto (conj z)
  have hNE : Tendsto (conj : ℂ → ℂ) (𝓝[≠] (conj z)) (𝓝[≠] z) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hN.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with w hw
    change conj w ≠ z
    exact fun he ↦ hw (by simpa using congrArg (conj : ℂ → ℂ) he)
  cases he : meromorphicOrderAt f z with
  | top =>
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [hNE.eventually (meromorphicOrderAt_eq_top_iff.mp he)] with w hw
    change f w = 0
    change f (conj w) = 0 at hw
    simpa [hs] using hw
  | coe n =>
    obtain ⟨g, hg, hn, hfg⟩ := (meromorphicOrderAt_eq_int_iff (hm z)).mp he
    apply (meromorphicOrderAt_eq_int_iff (hm (conj z))).mpr
    refine ⟨conj ∘ g ∘ conj, ?_, ?_, ?_⟩
    · apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
      filter_upwards [hN.eventually
        (Complex.analyticAt_iff_eventually_differentiableAt.mp hg)] with w hw
      exact differentiableAt_conj_conj_iff.mpr hw
    · simpa [Function.comp_def] using hn
    · filter_upwards [hNE.eventually hfg] with w hw
      simpa [hs, Function.comp_def, smul_eq_mul] using congrArg (conj : ℂ → ℂ) hw

/-- Conjugation preserves the full signed rational principal divisor. -/
theorem principal_divisor_conj (z : ℂ) : m₀ (conj z) = m₀ z := by
  rw [principal_divisor_eq_completedRiemannZeta, principal_divisor_eq_completedRiemannZeta]
  simp only [MeromorphicOn.divisor_apply completedZeta_meromorphic (mem_univ _),
    conjugateOrder (meromorphicOn_univ.mp completedZeta_meromorphic) completedRiemannZeta_conj]

/-- Complex conjugation permutes the genuine rational principal zero sites. -/
def zeroSitesConj : zeroSites ≃ zeroSites :=
  Equiv.subtypeEquiv Complex.conjAe.toEquiv fun z ↦
    iff_of_eq (congrArg (0 < ·) (principal_divisor_conj z).symm)

/-- The induced permutation has the ordinary conjugate as its complex coordinate. -/
@[simp] theorem zeroSitesConj_val (ρ : zeroSites) : (zeroSitesConj ρ).val = conj ρ.val := rfl

/-- Paired principal sites have the same divisor weight. -/
@[simp] theorem multiplicity_zeroSitesConj (ρ : zeroSites) :
    multiplicity (zeroSitesConj ρ) = multiplicity ρ :=
  congrArg Int.toNat (principal_divisor_conj ρ.val)

private theorem finite_real_sites : {z : zeroSites | z.val.im = 0}.Finite := by
  let K := (Complex.ofReal '' Icc (0 : ℝ) 1)
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  have hf : (K ∩ Function.support m₀).Finite :=
    Function.locallyFinsupp.locallyFiniteSupport m₀ |>.finite_inter_support_of_isCompact hK
  refine (hf.preimage (f := (Subtype.val : zeroSites → ℂ)) Subtype.val_injective.injOn).subset ?_
  intro z hz
  change z.val ∈ K ∩ Function.support m₀
  have hreal : z.val.im = 0 := hz
  refine ⟨⟨z.val.re, ⟨(re_mem_Ioo z).1.le, (re_mem_Ioo z).2.le⟩, ?_⟩, ne_of_gt z.property⟩
  exact Complex.ext rfl (by simpa using hreal.symm)

/-- The ordinary positive-height count for genuine Riemann zeta zeros in the open critical
strip. Each zero contributes its order, and the horizontal cutoff is inclusive. -/
def HasPositiveHeightZetaDensity (σ q C : ℝ) : Prop :=
  ∀ T : ℝ, 2 ≤ T → ∀ S : Finset ℂ,
    (∀ z ∈ S, z.re ∈ Ioo (0 : ℝ) 1 ∧ riemannZeta z = 0 ∧ σ ≤ z.re ∧ z.im ∈ Ioc 0 T) →
      ∑ z ∈ S, ((meromorphicOrderAt riemannZeta z).untop₀.toNat : ℝ) ≤
        C * T ^ q * Real.log (2 * T) ^ 5

private theorem zeta_zero_at_site (z : zeroSites) : riemannZeta z.val = 0 := by
  have hne : z.val ≠ 1 := fun h ↦ (ne_of_lt (re_mem_Ioo z).2) (by simp [h])
  have ha : AnalyticAt ℂ riemannZeta z.val := by
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    filter_upwards [isOpen_ne.mem_nhds hne] with s hs using differentiableAt_riemannZeta hs
  apply apply_eq_zero_of_analyticOrderAt_ne_zero
  intro he
  have h := multiplicity_eq_zeta_order z (re_mem_Ioo z).1
  have hp : 0 < multiplicity z := Int.pos_iff_toNat_pos.mp z.property
  rw [ha.meromorphicOrderAt_eq, he] at h
  simp at h
  omega

private theorem count_positive {σ q C : ℝ} (hd : HasPositiveHeightZetaDensity σ q C)
    {T : ℝ} (hT : 2 ≤ T) (S : Finset zeroSites)
    (hS : ∀ z ∈ S, σ ≤ z.val.re ∧ z.val.im ∈ Ioc 0 T) :
    ∑ z ∈ S, (multiplicity z : ℝ) ≤ C * T ^ q * Real.log (2 * T) ^ 5 := by
  let e : zeroSites ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  have h := hd T hT (S.map e) (by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
    exact ⟨re_mem_Ioo w, zeta_zero_at_site w, (hS w hw).1, (hS w hw).2⟩)
  rw [Finset.sum_map] at h
  refine (le_of_eq ?_).trans h
  exact Finset.sum_congr rfl fun z _ ↦
    congrArg Nat.cast (multiplicity_eq_zeta_order z (re_mem_Ioo z).1)

/-- Ingham's one-sided positive-height bound gives the actual two-sided right-strip
count, after enlarging the constant by the fixed mass of real zeros in [0,1]. -/
theorem hasRightDensity_of_positiveHeight {σ q C : ℝ} (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hd : HasPositiveHeightZetaDensity σ q C) : ∃ C' : ℝ, 0 ≤ C' ∧ HasRightDensity σ q C' := by
  classical
  let Z₀ := finite_real_sites.toFinset
  let m (z : zeroSites) : ℝ := multiplicity z
  let M := ∑ z ∈ Z₀, m z
  have mpos (z : zeroSites) : 0 ≤ m z := Nat.cast_nonneg _
  have hM : 0 ≤ M := Finset.sum_nonneg (fun z _ ↦ mpos z)
  refine ⟨2 * C + M, by positivity, ?_⟩
  intro T hT S hS
  let P := S.filter fun z ↦ 0 < z.val.im
  let N := S.filter fun z ↦ z.val.im < 0
  let Z := S.filter fun z ↦ z.val.im = 0
  let W := T ^ q * Real.log (2 * T) ^ 5
  have hW : 1 ≤ W := by
    have hlog : 1 ≤ Real.log (2 * T) := (Real.le_log_iff_exp_le (by linarith)).mpr
      (Real.exp_one_lt_three.le.trans (by linarith))
    exact one_le_mul_of_one_le_of_one_le (Real.one_le_rpow (by linarith) hq) (one_le_pow₀ hlog)
  have ph : (∑ z ∈ P, m z) ≤ C * W := by
    rw [← mul_assoc]
    apply count_positive hd hT
    intro z hz
    obtain ⟨hs, hp⟩ := Finset.mem_filter.mp hz
    exact ⟨(hS z hs).1, hp, (abs_le.mp (hS z hs).2).2⟩
  have nh : (∑ z ∈ N, m z) ≤ C * W := by
    have h := count_positive hd hT (N.map zeroSitesConj.toEmbedding) (by
      intro z hz
      obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hz
      obtain ⟨hS', hn⟩ := Finset.mem_filter.mp hw
      change σ ≤ (conj w.val).re ∧ 0 < (conj w.val).im ∧ (conj w.val).im ≤ T
      simp only [Complex.conj_re, Complex.conj_im]
      exact ⟨(hS w hS').1, neg_pos.mpr hn, by linarith [(abs_le.mp (hS w hS').2).1]⟩)
    rw [Finset.sum_map] at h
    change (∑ z ∈ N, (multiplicity (zeroSitesConj z) : ℝ)) ≤ _ at h
    simpa only [multiplicity_zeroSitesConj, m, W, mul_assoc] using h
  have zh : (∑ z ∈ Z, m z) ≤ M := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact fun z hz ↦ finite_real_sites.mem_toFinset.mpr (Finset.mem_filter.mp hz).2
    · exact fun z _ _ ↦ mpos z
  have hsplit (z : zeroSites) :
      m z = (if 0 < z.val.im then m z else 0) + (if z.val.im < 0 then m z else 0) +
        (if z.val.im = 0 then m z else 0) := by
    rcases lt_trichotomy z.val.im 0 with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  calc
    ∑ z ∈ S, (multiplicity z : ℝ) = (∑ z ∈ P, m z) + (∑ z ∈ N, m z) + ∑ z ∈ Z, m z := by
      simp only [P, N, Z, Finset.sum_filter, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun z _ ↦ hsplit z)
    _ ≤ (C * W + C * W) + M * W := add_le_add (add_le_add ph nh)
      (zh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hW hM))
    _ = _ := by dsimp [W]; ring

/-- Reflection of the actual divisor changes the sign of the height and preserves the
multiplicity. A right-hand density bound thus also counts any nonnegative weight,
bounded by the divisor multiplicity, which vanishes in the central open band. -/
theorem weighted_count_of_right_density {σ q C : ℝ} (hd : HasRightDensity σ q C)
    (m : zeroSites → ℝ) (hm : ∀ ρ, m ρ ≤ (multiplicity ρ : ℝ))
    (hzero : ∀ ρ, 1 - σ < ρ.val.re → ρ.val.re < σ → m ρ = 0)
    (T : ℝ) (hT : 2 ≤ T) (S : Finset zeroSites) (hS : ∀ ρ ∈ S, |ρ.val.im| ≤ T) :
    ∑ ρ ∈ S, m ρ ≤ (2 * C) * T ^ q * Real.log (2 * T) ^ 5 := by
  classical
  let R := S.filter (fun ρ ↦ σ ≤ ρ.val.re)
  let L := S.filter (fun ρ ↦ σ ≤ 1 - ρ.val.re)
  let B := C * T ^ q * Real.log (2 * T) ^ 5
  have hR : (∑ ρ ∈ R, (multiplicity ρ : ℝ)) ≤ B :=
    hd T hT R (fun ρ h ↦ ⟨(Finset.mem_filter.mp h).2, hS ρ (Finset.mem_filter.mp h).1⟩)
  have hL : (∑ ρ ∈ L, (multiplicity ρ : ℝ)) ≤ B := by
    have hmap := hd T hT (L.map reflectEmbedding) (by
      intro ρ hρ
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hρ
      have he := Finset.mem_filter.mp hj
      change σ ≤ (1 - j.val).re ∧ |(1 - j.val).im| ≤ T
      simpa only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub, abs_neg] using
        And.intro he.2 (hS j he.1))
    rw [Finset.sum_map] at hmap
    change (∑ ρ ∈ L, (multiplicity (reflect ρ) : ℝ)) ≤ B at hmap
    simpa only [multiplicity_reflect] using hmap
  have hsplit (ρ : zeroSites) : m ρ ≤
      (if σ ≤ ρ.val.re then (multiplicity ρ : ℝ) else 0) +
      (if σ ≤ 1 - ρ.val.re then (multiplicity ρ : ℝ) else 0) := by
    by_cases hright : σ ≤ ρ.val.re
    · rw [ite_eq_left hright]
      exact (hm ρ).trans (le_add_of_nonneg_right (by split <;> positivity))
    by_cases hleft : σ ≤ 1 - ρ.val.re
    · simpa [hright, hleft] using hm ρ
    · rw [hzero ρ (by linarith) (lt_of_not_ge hright)]
      simp [hright, hleft]
  calc
    ∑ ρ ∈ S, m ρ ≤ _ := Finset.sum_le_sum fun ρ _ ↦ hsplit ρ
    _ = (∑ ρ ∈ R, (multiplicity ρ : ℝ)) + ∑ ρ ∈ L, (multiplicity ρ : ℝ) := by
      rw [Finset.sum_add_distrib]
      simp [R, L, Finset.sum_filter]
    _ ≤ B + B := add_le_add hR hL
    _ = _ := by dsimp [B]; ring

/-- Paper: §12.3, p. 514. Compare the genuine lost-jet weights with the full principal
divisor. Under the classical right-side zero-density input, the absolute error for a
shrinking multiplier is uniformly `O(η^ν)` whenever `ν < 1-q`. -/
theorem missingJets_shrinking_sum_le {α β s σ q C K ν : ℝ} (hα : 0 ≤ α)
    (hα' : α ≤ 1 - σ) (hβ : σ ≤ β) (hq : 0 ≤ q) (hν : 0 < ν) (hqν : ν < 1 - q)
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hd : HasRightDensity σ q C) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ a : zeroSites → ℂ,
      (∀ ρ, ‖a ρ‖ ≤ K * (η / (1 + η * |ρ.val.im|))) →
      Summable (fun ρ ↦ (missingJets α β s ρ : ℝ) * ‖a ρ‖) ∧
        ∑' ρ, (missingJets α β s ρ : ℝ) * ‖a ρ‖ ≤ D * η ^ ν := by
  apply exists_shrinking_sum_le_of_log_count (fun ρ : zeroSites ↦ ρ.val.im)
    (fun ρ ↦ (missingJets α β s ρ : ℝ)) (fun _ ↦ Nat.cast_nonneg _)
    hq hν hqν (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hK 5
  apply weighted_count_of_right_density hd
  · intro ρ
    exact_mod_cast (Nat.sub_le (multiplicity ρ) _)
  · intro ρ h₁ h₂
    rw [missingJets_eq_zero hα (hα'.trans_lt h₁) (h₂.trans_le hβ), Nat.cast_zero]

end RiemannMasullo.RationalWidthLoss
