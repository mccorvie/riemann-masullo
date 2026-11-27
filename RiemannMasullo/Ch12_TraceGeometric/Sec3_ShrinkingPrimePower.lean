module

public import Mathlib.Analysis.Complex.Order
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_PrimeAtoms
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalWidthLoss
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic

/-! # Rational prime-power detection by shrinking four-moment tests

For actual completed principal zeros, a fixed-width density bound controls the missing
part of the full divisor. The compactly smoothed von Mangoldt formula then identifies
the signed lost-jet limit at each positive log location.
-/

@[expose] public noncomputable section

open Filter Set NumberField
open scoped ComplexConjugate ComplexOrder ContDiff Topology

namespace RiemannMasullo.RationalWidthLoss

open PrimeShrink

local notation "L(" H ", " z ")" => bilateralLaplace (fun x : ℝ ↦ ((H : ℝ → ℝ) x : ℂ)) z

private def zeroEquiv : zeroSites ≃ zetaZeros where
  toFun ρ := ⟨ρ.val, by
    change 0 < MeromorphicOn.divisor completedRiemannZeta univ ρ.val
    rw [← principal_divisor_eq_completedRiemannZeta]
    exact ρ.property⟩
  invFun ρ := ⟨ρ.val, by
    change 0 < MeromorphicOn.divisor (continuedCompletedHeckeL (F := ℚ) 1) univ ρ.val
    rw [principal_divisor_eq_completedRiemannZeta]
    exact ρ.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem zeroTerm_eq (H : ℝ → ℝ) (ρ : zeroSites) :
    zeroTerm H (zeroEquiv ρ) = (multiplicity ρ : ℂ) * L(H, ρ.val) := by
  change ((MeromorphicOn.divisor completedRiemannZeta univ ρ.val : ℤ) : ℂ) * _ = _
  rw [← principal_divisor_eq_completedRiemannZeta]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg ρ.property.le).symm

private theorem profile_decay_on_zeros {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (c T a : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ t : ℝ, |t| ≤ T → ∀ ρ : zeroSites,
      ‖L(profile g η c t, ρ.val - (a : ℂ))‖ ≤ K * (η / (1 + η * |ρ.val.im|)) := by
  obtain ⟨K, hK, hbound⟩ := profile_laplace_decay hg hgc c T (1 + |a|) 1
  refine ⟨K, hK, fun η hη h1 t ht ρ ↦ ?_⟩
  have hr := re_mem_Ioo ρ
  have he : |(ρ.val - (a : ℂ)).re| ≤ 1 + |a| := by
    rw [Complex.sub_re, Complex.ofReal_re]
    exact (abs_sub _ _).trans (add_le_add ((abs_of_pos hr.1).le.trans hr.2.le) le_rfl)
  simpa only [pow_one, Complex.sub_im, Complex.ofReal_im, sub_zero, mul_div_assoc] using
    hbound η hη h1 t ht _ he

/-- The full positive principal multiplicity at sites outside the open centered band
of radius `δ`. Its boundary is included. -/
def exteriorWeight (δ : ℝ) (ρ : zeroSites) : ℕ :=
  if δ ≤ |ρ.val.re - 1 / 2| then multiplicity ρ else 0

/-- The exterior sum of absolute Mellin samples is uniformly `O(η^ν)` under the right-side
density estimate. The chart center `a` remains free, so the argument can be `ρ-1/2` as well
as `ρ`. Bounded translations are measured in units of the support width. -/
theorem profile_exterior_mass_le {δ σ q C ν : ℝ} (hδ : σ - 1 / 2 ≤ δ)
    (hq : 0 ≤ q) (hν : 0 < ν) (hqν : ν < 1 - q) (hC : 0 ≤ C) (hd : HasRightDensity σ q C)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (c T a : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ t : ℝ, |t| ≤ T →
      Summable (fun ρ : zeroSites ↦ (exteriorWeight δ ρ : ℝ) *
        ‖L(profile g η c t, ρ.val - (a : ℂ))‖) ∧
      ∑' ρ : zeroSites, (exteriorWeight δ ρ : ℝ) *
        ‖L(profile g η c t, ρ.val - (a : ℂ))‖ ≤ D * η ^ ν := by
  obtain ⟨K, hK, hprobe⟩ := profile_decay_on_zeros hg hgc c T a
  have hcount := weighted_count_of_right_density hd (fun ρ ↦ (exteriorWeight δ ρ : ℝ))
    (fun ρ ↦ by unfold exteriorWeight; split <;> simp) (fun ρ hl hr ↦ by
      have hband : |ρ.val.re - 1 / 2| < δ := (abs_lt.mpr ⟨by linarith, by linarith⟩)
      rw [exteriorWeight, ite_eq_right (not_le.mpr hband), Nat.cast_zero])
  obtain ⟨D, hD, hbound⟩ := exists_shrinking_sum_le_of_log_count
    (fun ρ : zeroSites ↦ ρ.val.im) (fun ρ ↦ (exteriorWeight δ ρ : ℝ))
    (fun _ ↦ Nat.cast_nonneg _) hq hν hqν (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hC) hK 5 hcount
  exact ⟨D, hD, fun η hη h1 t ht ↦ hbound η hη h1 _ (hprobe η hη h1 t ht)⟩

/-- The literal complex wide-minus-narrow jet term, evaluated on the physical logarithmic
test in the center-zero chart. -/
def signedJetTerm (α β s : ℝ) (H : ℝ → ℝ) (ρ : zeroSites) : ℂ :=
  ((spectralStripMultiplicity β s ρ.val.re (multiplicity ρ) : ℂ) -
    spectralStripMultiplicity α s ρ.val.re (multiplicity ρ)) * L(H, ρ.val)

/-- A real profile gives conjugate bilateral Laplace samples at conjugate arguments. -/
private theorem bilateralLaplace_real_conj (H : ℝ → ℝ) (z : ℂ) :
    bilateralLaplace (fun x ↦ (H x : ℂ)) (conj z) =
      conj (bilateralLaplace (fun x ↦ (H x : ℂ)) z) := by
  simp only [bilateralLaplace, ← integral_conj, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj]

private theorem signedJetTerm_conj (α β s : ℝ) (H : ℝ → ℝ) (ρ : zeroSites) :
    signedJetTerm α β s H (zeroSitesConj ρ) = conj (signedJetTerm α β s H ρ) := by
  simp only [signedJetTerm, zeroSitesConj_val, Complex.conj_re, multiplicity_zeroSitesConj,
    bilateralLaplace_real_conj, map_mul, map_sub, map_natCast]

/-- Every unordered signed lost-jet sum against a real profile has zero imaginary part. -/
theorem tsum_signedJetTerm_im (α β s : ℝ) (H : ℝ → ℝ) :
    (∑' ρ, signedJetTerm α β s H ρ).im = 0 := by
  apply Complex.conj_eq_iff_im.mp
  rw [Complex.conj_tsum, tsum_congr (fun ρ ↦ (signedJetTerm_conj α β s H ρ).symm)]
  exact zeroSitesConj.tsum_eq (signedJetTerm α β s H)

private theorem signedJetTerm_eq {α β s : ℝ} (hα : 0 ≤ α) (hab : α < β)
    (H : ℝ → ℝ) (ρ : zeroSites) : signedJetTerm α β s H ρ =
      zeroTerm H (zeroEquiv ρ) - (missingJets α β s ρ : ℂ) * L(H, ρ.val) := by
  rw [zeroTerm_eq, cast_missingJets hα hab, signedJetTerm]
  ring

/-- Paper: §12.3, p. 514. At fixed nested widths on opposite sides of `1/2`,
the signed sum of the actual lost jets recovers the rational prime-power atom. The
remainder is uniform over a bounded range of the scaled translation and the sum is
absolute. The two classical inputs are the right-side density estimate and the
compactly smoothed von Mangoldt formula on the positive log axis. -/
theorem profile_lostJets_local_atom {α β s σ q C ν : ℝ} (hα : 0 ≤ α) (hab : α < β)
    (hα' : α ≤ 1 - σ) (hβ : σ ≤ β) (hq : 0 ≤ q) (hν : 0 < ν) (hqν : ν < 1 - q)
    (hC : 0 ≤ C) (hd : HasRightDensity σ q C) (hef : PositiveAxisExplicitFormula)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ Icc (-1) 1)
    {c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) :
    ∃ δ > 0, ∃ B : ℝ, 0 ≤ B ∧ ∀ η : ℝ, 0 < η → η ≤ δ → ∀ t ∈ Icc (-T) T,
      Summable (fun ρ ↦ ‖signedJetTerm α β s (profile g η c t) ρ‖) ∧
      ‖(∑' ρ, signedJetTerm α β s (profile g η c t) ρ) +
        ((atomWeight c * iteratedDeriv 4 g (-t) : ℝ) : ℂ)‖ ≤ B * η ^ ν := by
  have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs
  obtain ⟨K, hK, hp⟩ := profile_decay_on_zeros hg hgc c T 0
  obtain ⟨D, hD, hmiss⟩ := missingJets_shrinking_sum_le (s := s) hα hα' hβ hq hν hqν hC hK hd
  obtain ⟨δ, hδ, A, hatom⟩ := profile_fullZeroSum_local_atom hef hg hs hc hT
  refine ⟨min δ 1, lt_min hδ zero_lt_one, max A 0 + D, by positivity, ?_⟩
  intro η hη hηδ t ht
  have h1 : η ≤ 1 := hηδ.trans (min_le_right _ _)
  let H := profile g η c t
  let tail := fun ρ : zeroSites ↦ (missingJets α β s ρ : ℂ) * L(H, ρ.val)
  have ht' : |t| ≤ T := abs_le.mpr ht
  have ha (ρ : zeroSites) : ‖L(H, ρ.val)‖ ≤ K * (η / (1 + η * |ρ.val.im|)) := by
    simpa only [Complex.ofReal_zero, sub_zero] using hp η hη h1 t ht' ρ
  obtain ⟨habs, herr⟩ := hmiss η hη h1 (fun ρ ↦ L(H, ρ.val)) ha
  have hn (ρ : zeroSites) : ‖tail ρ‖ = (missingJets α β s ρ : ℝ) * ‖L(H, ρ.val)‖ := by
    simp only [tail, norm_mul, Complex.norm_natCast]
  have htail : Summable (fun ρ ↦ ‖tail ρ‖) := habs.congr (fun ρ ↦ (hn ρ).symm)
  have herr' : ‖∑' ρ, tail ρ‖ ≤ D * η ^ ν :=
    (norm_tsum_le_tsum_norm htail).trans (by simpa only [hn] using herr)
  obtain ⟨hfull, hfullErr⟩ := hatom η hη (hηδ.trans (min_le_left _ _)) t ht
  have hfs : Summable (fun ρ : zeroSites ↦ zeroTerm H (zeroEquiv ρ)) :=
    hfull.comp_injective zeroEquiv.injective
  have hsub := hfs.sub htail.of_norm
  have hterm (ρ : zeroSites) : signedJetTerm α β s H ρ = zeroTerm H (zeroEquiv ρ) - tail ρ :=
    signedJetTerm_eq hα hab H ρ
  refine ⟨(hsub.congr (fun ρ ↦ (hterm ρ).symm)).norm, ?_⟩
  have hadd : (∑' ρ, signedJetTerm α β s H ρ) =
      (∑' ρ, zeroTerm H ρ) - ∑' ρ, tail ρ := by
    rw [tsum_congr hterm, hfs.tsum_sub htail.of_norm, zeroEquiv.tsum_eq (zeroTerm H)]
  change ‖(∑' ρ, signedJetTerm α β s H ρ) + _‖ ≤ _
  rw [hadd, sub_add_eq_add_sub]
  have hηpow : η ≤ η ^ ν := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hη h1 (by linarith : ν ≤ 1)
  calc
    _ ≤ ‖(∑' ρ, zeroTerm H ρ) + ((atomWeight c * iteratedDeriv 4 g (-t) : ℝ) : ℂ)‖ +
        ‖∑' ρ, tail ρ‖ := norm_sub_le _ _
    _ ≤ A * η + D * η ^ ν := add_le_add hfullErr herr'
    _ ≤ (max A 0 + D) * η ^ ν := by
      rw [add_mul]
      exact add_le_add (mul_le_mul (le_max_left A 0) hηpow hη.le (le_max_right _ _)) le_rfl

/-- A fixed scaled translate converges to the signed von Mangoldt atom at its log location. -/
theorem profile_lostJets_tendsto {α β s σ q C ν : ℝ} (hα : 0 ≤ α) (hab : α < β)
    (hα' : α ≤ 1 - σ) (hβ : σ ≤ β) (hq : 0 ≤ q) (hν : 0 < ν) (hqν : ν < 1 - q)
    (hC : 0 ≤ C) (hd : HasRightDensity σ q C) (hef : PositiveAxisExplicitFormula)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ Icc (-1) 1)
    {c : ℝ} (hc : 0 < c) (t : ℝ) :
    Tendsto (fun η ↦ ∑' ρ, signedJetTerm α β s (profile g η c t) ρ) (𝓝[>] 0)
      (𝓝 (-((atomWeight c * iteratedDeriv 4 g (-t) : ℝ) : ℂ))) := by
  obtain ⟨δ, hδ, B, _, he⟩ := profile_lostJets_local_atom (s := s) hα hab hα' hβ hq hν hqν
    hC hd hef hg hs hc (abs_nonneg t)
  have hcut : ∀ᶠ η : ℝ in 𝓝[>] 0, η < δ :=
    (eventually_lt_nhds hδ).filter_mono nhdsWithin_le_nhds
  have h₀ : Tendsto (fun η : ℝ ↦ η) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hp := h₀.rpow_const_nhds_zero hν
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (.of_forall fun _ ↦ norm_nonneg _) _
    (show Tendsto (fun η : ℝ ↦ B * η ^ ν) (𝓝[>] 0) (𝓝 0) by
      simpa using (tendsto_const_nhds (x := B)).mul hp)
  filter_upwards [self_mem_nhdsWithin, hcut] with η hη hηδ
  have h := (he η hη hηδ.le t ⟨neg_abs_le t, le_abs_self t⟩).2
  simpa only [sub_neg_eq_add] using h

/-- Ingham's 1940 right-hand estimate counted with multiplicities (Quart. J. Math.
11, pp. 201–202) on the ordinary Riemann zeros with positive ordinate. -/
def InghamDensity : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 3 / 4 →
    ∃ C : ℝ, 0 ≤ C ∧ HasPositiveHeightZetaDensity σ (3 * (1 - σ) / (2 - σ)) C

private theorem exponents_of_Ingham (hI : InghamDensity) {α β : ℝ}
    (hn : α < 1 / 2) (hw : 1 / 2 < β) :
    ∃ σ q ν C : ℝ, α ≤ 1 - σ ∧ σ ≤ β ∧ 0 ≤ q ∧ 0 < ν ∧ ν < 1 - q ∧
      0 ≤ C ∧ HasRightDensity σ q C := by
  let σ := min (3 / 4) (min (1 - α) β)
  have hσ : 1 / 2 < σ := lt_min (by norm_num) (lt_min (by linarith) hw)
  have hσ' : σ ≤ 3 / 4 := min_le_left _ _
  have hα : σ ≤ 1 - α := (min_le_right _ _).trans (min_le_left _ _)
  have hβ : σ ≤ β := (min_le_right _ _).trans (min_le_right _ _)
  let q := 3 * (1 - σ) / (2 - σ)
  have hden : 0 < 2 - σ := by linarith
  have hq : 0 ≤ q := div_nonneg (mul_nonneg (by norm_num) (by linarith)) hden.le
  have hq' : q < 1 := (div_lt_iff₀ hden).mpr (by linarith)
  obtain ⟨C₀, hC₀, hd₀⟩ := hI σ hσ hσ'
  obtain ⟨C, hC, hd⟩ := hasRightDensity_of_positiveHeight hq hC₀ hd₀
  exact ⟨σ, q, (1 - q) / 2, C, by linarith, hβ, hq, by linarith, by linarith, hC, hd⟩

/-- For widths `1/4, 3/4`, Ingham's exponent is `3/5`, so every remainder exponent
strictly between zero and `2/5` is available. -/
theorem profile_quarter_widths_local_atom (hI : InghamDensity) (hef : PositiveAxisExplicitFormula)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ Icc (-1) 1)
    (s : ℝ) {c T ν : ℝ} (hc : 0 < c) (hT : 0 ≤ T) (hν : 0 < ν) (hν' : ν < 2 / 5) :
    ∃ δ > 0, ∃ B : ℝ, 0 ≤ B ∧ ∀ η : ℝ, 0 < η → η ≤ δ → ∀ t ∈ Icc (-T) T,
      Summable (fun ρ ↦ ‖signedJetTerm (1 / 4) (3 / 4) s (profile g η c t) ρ‖) ∧
      ‖(∑' ρ, signedJetTerm (1 / 4) (3 / 4) s (profile g η c t) ρ) +
        ((atomWeight c * iteratedDeriv 4 g (-t) : ℝ) : ℂ)‖ ≤ B * η ^ ν := by
  obtain ⟨C₀, hC₀, hd₀⟩ := hI (3 / 4) (by norm_num) le_rfl
  have hq : 3 * (1 - (3 / 4 : ℝ)) / (2 - 3 / 4) = 3 / 5 := by norm_num
  rw [hq] at hd₀
  obtain ⟨C, hC, hd⟩ := hasRightDensity_of_positiveHeight (by norm_num : 0 ≤ (3 / 5 : ℝ)) hC₀ hd₀
  exact profile_lostJets_local_atom (by norm_num) (by norm_num) (by norm_num) le_rfl
    (by norm_num) hν (by linarith) hC hd hef hg hs hc hT

/-- At the logarithm of every prime power the lost-jet limit detects minus `log p`
times the fourth derivative. Off the prime-power sites the same limit is zero by
`atomWeight_eq_zero` and `profile_lostJets_tendsto`. -/
theorem profile_lostJets_at_prime_power (hI : InghamDensity) (hef : PositiveAxisExplicitFormula)
    {α β s : ℝ} (hα : 0 ≤ α) (hn : α < 1 / 2) (hw : 1 / 2 < β)
    {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ Icc (-1) 1)
    {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) (t : ℝ) :
    Tendsto (fun η ↦ ∑' ρ, signedJetTerm α β s (profile g η (Real.log ((p ^ k : ℕ) : ℝ)) t) ρ)
      (𝓝[>] 0) (𝓝 (-((Real.log (p : ℝ) * iteratedDeriv 4 g (-t) : ℝ) : ℂ))) := by
  obtain ⟨σ, q, ν, C, hσ, hβ, hq, hν, hqν, hC, hd⟩ := exponents_of_Ingham hI hn hw
  have hc : 0 < Real.log ((p ^ k : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast one_lt_pow₀ hp.one_lt hk)
  simpa only [atomWeight_log_prime_pow hp hk] using
    profile_lostJets_tendsto (s := s) hα (hn.trans hw) hσ hβ hq hν hqν hC hd hef hg hs hc t

/-- One smooth real profile supported in the unit interval around zero has opposite
fourth-derivative signs at zero and at minus one half. -/
theorem exists_seed_opposite_fourth_derivatives :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ tsupport g ⊆ Icc (-1) 1 ∧
      0 < iteratedDeriv 4 g 0 ∧ iteratedDeriv 4 g (-(1 / 2)) < 0 := by
  let b : ContDiffBump (0 : ℝ) := ⟨3 / 4, 1, by norm_num, by norm_num⟩
  let P := fun x : ℝ ↦ x ^ 4 + x ^ 5
  let g := fun x : ℝ ↦ b x * P x
  have hjet (x : ℝ) (hx : x ∈ Metric.ball 0 b.rIn) : iteratedDeriv 4 g x = 24 + 120 * x := by
    have hlocal : g =ᶠ[𝓝 x] P := by
      filter_upwards [b.eventuallyEq_one_of_mem_ball hx] with u hu
      change b u = 1 at hu
      simp [g, hu]
    rw [hlocal.iteratedDeriv_eq 4]
    change iteratedDeriv 4 (fun u : ℝ ↦ u ^ 4 + u ^ 5) x = _
    rw [iteratedDeriv_fun_add (f := fun u : ℝ ↦ u ^ 4) (g := fun u : ℝ ↦ u ^ 5) (by fun_prop) (by fun_prop),
      iteratedDeriv_pow, iteratedDeriv_pow]
    norm_num [Nat.descFactorial]
  refine ⟨g, b.contDiff.mul (by dsimp [P]; fun_prop), ?_, ?_, ?_⟩
  · have hsub : tsupport g ⊆ tsupport (b : ℝ → ℝ) := tsupport_mul_subset_left
    simpa [b.tsupport_eq, Real.closedBall_eq_Icc, b] using hsub
  · rw [hjet 0 (by norm_num [Metric.mem_ball, b])]
    norm_num
  · rw [hjet _ (by norm_num [Metric.mem_ball, Real.dist_eq, b])]
    norm_num

/-- One compact seed gives opposite strict signs at scaled translates zero and one half
at every prime-power logarithm, for all sufficiently small positive scales. -/
theorem exists_opposite_lostJet_prime_power_translates (hI : InghamDensity)
    (hef : PositiveAxisExplicitFormula) {α β s : ℝ} (hα : 0 ≤ α) (hn : α < 1 / 2) (hw : 1 / 2 < β) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ tsupport g ⊆ Icc (-1) 1 ∧
      ∀ (p k : ℕ), p.Prime → k ≠ 0 → ∀ᶠ η : ℝ in 𝓝[>] 0,
        (∑' ρ, signedJetTerm α β s (profile g η (Real.log ((p ^ k : ℕ) : ℝ)) 0) ρ) < 0 ∧
        0 < (∑' ρ, signedJetTerm α β s (profile g η (Real.log ((p ^ k : ℕ) : ℝ)) (1 / 2)) ρ) := by
  obtain ⟨g, hg, hs, h₀, hhalf⟩ := exists_seed_opposite_fourth_derivatives
  refine ⟨g, hg, hs, fun p k hp hk ↦ ?_⟩
  have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlim (t : ℝ) := (Complex.continuous_re.tendsto _).comp
    (profile_lostJets_at_prime_power (s := s) hI hef hα hn hw hg hs hp hk t)
  have hl₀ : (-((Real.log (p : ℝ) * iteratedDeriv 4 g (-(0 : ℝ)) : ℝ) : ℂ)).re < 0 := by
    simpa only [neg_zero, Complex.neg_re, Complex.ofReal_re, neg_lt_zero] using mul_pos hlog h₀
  have hlhalf : 0 < (-((Real.log (p : ℝ) * iteratedDeriv 4 g (-(1 / 2)) : ℝ) : ℂ)).re := by
    simpa only [Complex.neg_re, Complex.ofReal_re, neg_pos] using mul_neg_of_pos_of_neg hlog hhalf
  filter_upwards [(hlim 0).eventually (eventually_lt_nhds hl₀),
    (hlim (1 / 2)).eventually (eventually_gt_nhds hlhalf)] with η hneg hpos
  exact ⟨Complex.neg_iff.mpr ⟨hneg, tsum_signedJetTerm_im _ _ _ _⟩,
    Complex.pos_iff.mpr ⟨hpos, (tsum_signedJetTerm_im _ _ _ _).symm⟩⟩

end RiemannMasullo.RationalWidthLoss
