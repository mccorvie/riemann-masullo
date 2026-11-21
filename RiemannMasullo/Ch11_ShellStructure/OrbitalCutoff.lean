module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.Ch03_IdelicZeta.Sec1
public import Mathlib.Data.Nat.Prime.Nth
public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# The second-variable cutoff in the orbital trace calculation

On p. 24 the lifted kernel is divided into pieces by indicators in its second variable.
Equation (11.3.1.4) leaves that argument implicit. In (11.3.2.3) the additional
stratum indicator is explicitly evaluated at the second argument, while the spatial
cutoff is evaluated at the first. We use the componentwise description of the strata
on p. 493.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function Set NumberField IsDedekindDomain Topology
open scoped ContDiff NNReal

variable (F : Type*) [Field F] [NumberField F]

/-- Paper: §11.3.1, p. 493. An idèle belongs to the kth stratum if it is a local
integer unit at every finite place over one of the first k rational primes. -/
def orbitalUnitStratum (k : ℕ) : Set (IdeleGroup (𝓞 F) F) :=
  {g | ∀ i < k, ∀ v : HeightOneSpectrum (𝓞 F), (Nat.nth Nat.Prime i : 𝓞 F) ∈ v.asIdeal →
    Units.map (RestrictedProduct.evalMonoidHom (fun w : HeightOneSpectrum (𝓞 F) ↦
      w.adicCompletion F) v) (MulEquiv.prodUnits g).2 ∈ (v.adicCompletionIntegers F).units}

/-- Paper: §11.3.1, p. 493. Each additional rational prime imposes more unit conditions. -/
theorem orbitalUnitStratum_antitone : Antitone (orbitalUnitStratum F) :=
  fun _ _ h _ hg i hi ↦ hg i (lt_of_lt_of_le hi h)

/-- Paper: §11.3.1, p. 493. The complex indicator of the kth divisorial stratum. -/
def orbitalUnitCutoff (k : ℕ) : IdeleGroup (𝓞 F) F → ℂ :=
  (orbitalUnitStratum F k).indicator 1

/-- Paper: Equation (11.3.2.3), p. 495.
Deviation: With the shell in (11.3.1.4) acting in the second argument as on p. 24, every later
unit cutoff annihilates the shell pointwise, for any kernel and any spatial cutoff. -/
theorem orbitalShell_laterCutoff_eq_zero (k j : ℕ) (hj : k + 1 ≤ j)
    (ρ : IdeleGroup (𝓞 F) F → ℂ) (K : IdeleGroup (𝓞 F) F → IdeleGroup (𝓞 F) F → ℂ)
    (x y : IdeleGroup (𝓞 F) F) :
    ρ x * ((orbitalUnitCutoff F (k + 1) y - orbitalUnitCutoff F k y) * K x y) *
      orbitalUnitCutoff F j y = 0 := by
  by_cases hy : y ∈ orbitalUnitStratum F j
  · have hnext := orbitalUnitStratum_antitone F hj hy
    have hcur := orbitalUnitStratum_antitone F (Nat.le_succ k) hnext
    simp [orbitalUnitCutoff, hnext, hcur]
  · simp [orbitalUnitCutoff, hy]

/-- A smooth pulse centered at norm two, with closed support strictly inside (3/2, 5/2). -/
def primeTwoNormBump : ContDiffBump (2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

/-- The radial profile is smooth, is compactly supported near two, and takes value one there. -/
theorem primeTwoNormBump_spec :
    ContDiff ℝ ∞ primeTwoNormBump ∧ HasCompactSupport primeTwoNormBump ∧
    tsupport primeTwoNormBump ⊆ Ioo (3 / 2) (5 / 2) ∧ primeTwoNormBump 2 = 1 := by
  refine ⟨primeTwoNormBump.contDiff, primeTwoNormBump.hasCompactSupport, ?_,
    primeTwoNormBump.one_of_mem_closedBall (Metric.mem_closedBall_self primeTwoNormBump.rIn_pos.le)⟩
  rw [primeTwoNormBump.tsupport_eq, Real.closedBall_eq_Icc]
  exact Icc_subset_Ioo (by norm_num [primeTwoNormBump]) (by norm_num [primeTwoNormBump])

private theorem primeTwoNormBump_dyadic (m : ℤ) :
    primeTwoNormBump ((2 : ℝ) ^ (-m)) = if m = -1 then 1 else 0 := by
  split_ifs with hm
  · simpa [hm] using primeTwoNormBump_spec.2.2.2
  · by_contra hn
    obtain ⟨hlo, hhi⟩ := primeTwoNormBump_spec.2.2.1 (subset_tsupport _ hn)
    by_cases h : 0 ≤ m
    · have hm' : -m ≤ 0 := by omega
      have := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hm'
      norm_num only [zpow_zero, zpow_ofNat, Nat.cast_ofNat, pow_two] at this
      linarith
    · have hm' : 2 ≤ -m := by omega
      have := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hm'
      norm_num only [zpow_zero, zpow_ofNat, Nat.cast_ofNat, pow_two] at this
      linarith

/-- Paper: Equation (11.3.2.1), p. 495.
Deviation: Evaluate the radial sum for the prime two and unit Haar volume one.
The inverse uniformizer is the unique power whose norm meets the support. -/
theorem primeTwoNormBump_orbitalSum :
    Real.log 2 * ∑' m : ℤ, primeTwoNormBump ((2 : ℝ) ^ (-m)) = Real.log 2 := by
  simp_rw [primeTwoNormBump_dyadic]
  simp

/-- The finite place (2) of the rational field. -/
def ratPrimeTwoPlace : HeightOneSpectrum (𝓞 ℚ) where
  asIdeal := Ideal.span {(2 : 𝓞 ℚ)}
  isPrime := (Ideal.span_singleton_prime (by norm_num)).2
    ((MulEquiv.prime_iff Rat.ringOfIntegersEquiv).1 (by rw [map_ofNat]; exact Int.prime_two))
  ne_bot := by simp

private theorem ratPrimeTwoPlace_absNorm : ratPrimeTwoPlace.asIdeal.absNorm = 2 := by
  change (Ideal.span {((2 : ℕ) : 𝓞 ℚ)}).absNorm = 2
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Module.finrank_self, pow_one]

/-- Paper: Equation (11.3.2.1), p. 495.
Deviation: The rational radial test is the smooth pulse at two pulled back by the idèle class norm. -/
def primeTwoClassTest (x : IdeleClassGroup (𝓞 ℚ) ℚ) : ℂ :=
  primeTwoNormBump ((ideleClassNorm ℚ x).val : ℝ)

/-- Every translation by a norm-one class preserves the radial test, including finite unit translations. -/
theorem primeTwoClassTest_mul_of_norm_one {u : IdeleClassGroup (𝓞 ℚ) ℚ}
    (hu : ideleClassNorm ℚ u = 1) (x : IdeleClassGroup (𝓞 ℚ) ℚ) :
    primeTwoClassTest (u * x) = primeTwoClassTest x := by
  simp [primeTwoClassTest, hu]

/-- The class of the idèle with component two at (2) and component one elsewhere. -/
def ratPrimeTwoUniformizerClass : IdeleClassGroup (𝓞 ℚ) ℚ :=
  let v := ratPrimeTwoPlace
  IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v
    (Units.map (algebraMap ℚ (v.adicCompletion ℚ)).toMonoidHom (Units.mk0 (2 : ℚ) (by norm_num)))

/-- Paper: Equation (11.3.2.1), p. 495.
Deviation: For the rational place (2), the uniformizer powers give a prime
contribution of log 2 with the unit group assigned Haar volume one. -/
theorem primeTwoClassTest_orbitalSum :
    Real.log 2 * ∑' m : ℤ, primeTwoClassTest (ratPrimeTwoUniformizerClass ^ m) = (Real.log 2 : ℂ) := by
  let v := ratPrimeTwoPlace
  let π := Units.map (algebraMap ℚ (v.adicCompletion ℚ)).toMonoidHom (Units.mk0 (2 : ℚ) (by norm_num))
  let u := ratPrimeTwoUniformizerClass
  have hπ : Valued.v.IsUniformizer (π : v.adicCompletion ℚ) := by
    change Valued.v (algebraMap ℚ (v.adicCompletion ℚ) 2) = _
    rw [show Valued.v (algebraMap ℚ (v.adicCompletion ℚ) 2) = _ from
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (2 : ℚ)]
    rw [← map_ofNat (algebraMap (𝓞 ℚ) ℚ), HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_singleton (by norm_num : (2 : 𝓞 ℚ) ≠ 0) rfl).trans
      (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.valuedAdicCompletion_surjective ℚ))).symm
  have hu : ((ideleClassNorm ℚ u).val : ℝ) = (2 : ℝ)⁻¹ := by
    rw [show ideleClassNorm ℚ u = _ from ideleClassNorm_ofAdicCompletion ℚ v π]
    exact (norm_uniformizer_adicCompletion v _ hπ).trans (by rw [ratPrimeTwoPlace_absNorm]; norm_num)
  have hpow (m : ℤ) : primeTwoClassTest (u ^ m) =
      if m = -1 then (1 : ℂ) else 0 := by
    unfold primeTwoClassTest
    rw [map_zpow, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, hu, inv_zpow, ← zpow_neg,
      primeTwoNormBump_dyadic]
    split_ifs <;> simp
  change (Real.log 2 : ℂ) * ∑' m : ℤ, primeTwoClassTest (u ^ m) = _
  simp_rw [hpow]
  simp

/-- With only the real place in S, the rational S-integers have trivial Picard group. -/
theorem ratPicard_emptyFinitePlaces :
    Subsingleton (CommRing.Pic ((∅ : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)) := by
  rw [IsDedekindDomain.integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv.trans
    Rat.ringOfIntegersEquiv
  let R := (⊥ : Subalgebra (𝓞 ℚ) ℚ)
  let : IsPrincipalIdealRing R := IsPrincipalIdealRing.of_surjective e.symm e.symm.surjective
  let : Subsingleton (ClassGroup R) :=
    Fintype.card_le_one_iff_subsingleton.mp (card_classGroup_eq_one (R := ↥R)).le
  exact (ClassGroup.equivPic R).symm.injective.subsingleton

/-- A finite unit idèle, with real component one, preserves the rational radial test. -/
theorem primeTwoClassTest_finiteUnits_invariant (g : IdeleGroup (𝓞 ℚ) ℚ)
    (hinf : g.val.1 = 1)
    (hfin : ∀ v : HeightOneSpectrum (𝓞 ℚ), Units.map (RestrictedProduct.evalMonoidHom
      (fun w : HeightOneSpectrum (𝓞 ℚ) ↦ w.adicCompletion ℚ) v) (MulEquiv.prodUnits g).2 ∈
        (v.adicCompletionIntegers ℚ).units) (x : IdeleClassGroup (𝓞 ℚ) ℚ) :
    primeTwoClassTest (QuotientGroup.mk g * x) = primeTwoClassTest x := by
  apply primeTwoClassTest_mul_of_norm_one
  change ideleNorm ℚ g = 1
  apply Units.ext
  apply NNReal.eq
  rw [((ideleNorm_spec ℚ).1 g).2]
  have hreal (w : InfinitePlace ℚ) : ‖g.val.1 w‖ = 1 := by
    rw [hinf]
    exact norm_one
  have hlocal (v : HeightOneSpectrum (𝓞 ℚ)) : ‖g.val.2 v‖ = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mpr
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp (hfin v))
  simp [hlocal, hreal]

/-- Paper: Theorem 11.3.2.1, p. 495.
Deviation: For the prime-two rational test we verify the defining Bruhat smoothness
and compact-support conditions on the idèle class group itself. Its closed support
lies over norms strictly between 3/2 and 5/2. -/
theorem primeTwoClassTest_admissible :
    IsBruhatSmooth primeTwoClassTest ∧ HasCompactSupport primeTwoClassTest ∧
      tsupport primeTwoClassTest ⊆ {x | ((ideleClassNorm ℚ x).val : ℝ) ∈ Ioo (3 / 2) (5 / 2)} := by
  obtain ⟨_, _, _, _, _, hT, hLC, _, hn, _, ⟨s, hs, hsn⟩, _⟩ := ideleGroup_quotient.{0, 0} ℚ
  let : T2Space (IdeleClassGroup (𝓞 ℚ) ℚ) := hT
  let : LocallyCompactSpace (IdeleClassGroup (𝓞 ℚ) ℚ) := hLC
  let m : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm ℚ, hn⟩
  let profile (t : ℝ) : ℂ := primeTwoNormBump t
  have hprofile : ContDiff ℝ ∞ profile := Complex.ofRealCLM.contDiff.comp primeTwoNormBump.contDiff
  have hproper : IsProperMap m := isProperMap_ideleClassNorm ℚ
  let sectionMap : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ := ⟨s, hs⟩
  have hright : RightInverse sectionMap m := hsn
  have hsmooth := isBruhatSmooth_comp_splitModulation (G := IdeleClassGroup (𝓞 ℚ) ℚ)
    (f := profile) m hproper sectionMap hright hprofile
  refine ⟨hsmooth, ?_⟩
  let valR (u : ℝ≥0ˣ) := (u.val : ℝ)
  let h := Nonneg.unitsHomeomorphPos ℝ
  have hind : IsInducing valR := by
    change IsInducing ((Subtype.val : Ioi (0 : ℝ) → ℝ) ∘ h)
    exact IsInducing.subtypeVal.comp h.isInducing
  have hrange : range valR = Ioi 0 := by
    change range ((Subtype.val : Ioi (0 : ℝ) → ℝ) ∘ h) = _
    rw [Set.range_comp, h.surjective.range_eq, Set.image_univ, Subtype.range_coe]
  have hsupp : tsupport primeTwoClassTest ⊆ m ⁻¹' (valR ⁻¹' tsupport primeTwoNormBump) := by
    let n : IdeleClassGroup (𝓞 ℚ) ℚ → ℝ := valR ∘ m
    have hn' : Continuous n := hind.continuous.comp m.continuous
    exact (tsupport_comp_subset (g := ((↑) : ℝ → ℂ)) Complex.ofReal_zero (primeTwoNormBump ∘ n)).trans
      (tsupport_comp_subset_preimage (f := n) (primeTwoNormBump : ℝ → ℝ) hn')
  have hpos : tsupport primeTwoNormBump ⊆ range valR := by
    rw [hrange]
    intro t ht
    exact lt_trans (by norm_num : (0 : ℝ) < 3 / 2) (primeTwoNormBump_spec.2.2.1 ht).1
  exact ⟨((isProperMap_ideleClassNorm ℚ).isCompact_preimage
    (hind.isCompact_preimage' primeTwoNormBump.hasCompactSupport hpos)).of_isClosed_subset
      (isClosed_tsupport _) hsupp, fun x hx ↦ primeTwoNormBump_spec.2.2.1 (hsupp hx)⟩

/-- Paper: Equation (11.3.2.3), p. 495.
Deviation: For the first shell (prime two), any orbital sum or integral taking the
zero kernel to zero disagrees with the normalized arithmetic side of (11.3.2.1)
on the displayed test after insertion of a later cutoff. -/
theorem primeTwo_laterCutoff_ne_orbitalSum (j : ℕ) (hj : 1 ≤ j)
    (ρ : IdeleGroup (𝓞 ℚ) ℚ → ℂ) (K : IdeleGroup (𝓞 ℚ) ℚ → IdeleGroup (𝓞 ℚ) ℚ → ℂ)
    (J : (IdeleGroup (𝓞 ℚ) ℚ → IdeleGroup (𝓞 ℚ) ℚ → ℂ) → ℂ) (hJ : J 0 = 0) :
    J (fun x y ↦ ρ x * ((orbitalUnitCutoff ℚ 1 y - orbitalUnitCutoff ℚ 0 y) * K x y) *
        orbitalUnitCutoff ℚ j y) ≠
      Real.log 2 * ∑' m : ℤ, primeTwoClassTest (ratPrimeTwoUniformizerClass ^ m) := by
  simp_rw [orbitalShell_laterCutoff_eq_zero ℚ 0 j hj ρ K]
  rw [primeTwoClassTest_orbitalSum, show J (fun _ _ ↦ 0) = 0 from hJ]
  exact Ne.symm (Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne')

end RiemannMasullo
