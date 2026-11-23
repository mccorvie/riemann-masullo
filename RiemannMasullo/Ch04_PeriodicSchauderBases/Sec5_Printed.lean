module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec5
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-! # §4.5: statements that are false as printed -/

@[expose] public noncomputable section

open Function MeasureTheory Set UniformSpace
open scoped NNReal TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false

local instance printedCh04Sec5QuotientMeasurableSpace {G : Type} [CommGroup G]
    [TopologicalSpace G] (γ : G) : MeasurableSpace (G ⧸ Subgroup.zpowers γ) := borel _

/-- Paper: Remarks 4.5.1.2 and 4.5.1.4, pp. 198, 203. Agreement with (4.5.1.1)
on the original tests, using the split coordinates of
`modulatedExponentialDecay_tensor_equiv` and the canonical tensor comparison. -/
def Printed.AgreesWithFullPeriodization {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (τ : ℝ≥0ˣ →ₜ* G) (γ : G) (hγ : 1 < (m γ).val) (I : Set ℝ)
    (A : Completion (ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker)
        (PositiveRealExponentialDecay I)) → SchwartzBruhat (G ⧸ Subgroup.zpowers γ)) : Prop :=
  let K := m.toMonoidHom.ker
  let TI := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
  let TP := ProjectiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
  letI : UniformContinuousConstSMul ℂ TI := uniformContinuousConstSMul_of_continuousConstSMul ℂ TI
  ∀ e : Completion TI ≃L[ℂ] ModulatedExponentialDecay m I,
    (∀ (h : SchwartzBruhat K) (p : PositiveRealExponentialDecay I) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := TI) (h ⊗ₜ[ℂ] p))).val (u.val * τ t) =
        h u * p.val (Real.log (t.val : ℝ))) →
    ∀ (z : Completion TI) (f : ModulatedExponentialDecay m univ), (e z).val = f.val →
      A (@Completion.map TI _ TP _ (fun v : TI ↦ (show TP from v)) z) = modulatedPeriodizationCLM m γ hm hms hγ f

/-- Paper: Remark 4.5.1.2, p. 198. Ordinary periodization extends sequentially
continuously to the projective completion. The remark leaves I implicit.
Deviation: This records the reading with an arbitrary nonempty interval from
Definition D.3.3.1. The case with zero in I is treated by
`modulatedIntervalPeriodization_projective`. See ERRATA F174. -/
def Printed.modulatedIntervalPeriodization_projective_sequential : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ m → ∀ (γ : G) (hγ : 1 < (m γ).val)
    (I : Set ℝ), OrdConnected I → I.Nonempty →
    let T := ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay I)
    letI : UniformContinuousConstSMul ℂ T := uniformContinuousConstSMul_of_continuousConstSMul ℂ T
    ∃ A : Completion T →ₗ[ℂ] SchwartzBruhat (G ⧸ Subgroup.zpowers γ),
      SeqContinuous A ∧ Printed.AgreesWithFullPeriodization m hm hms τ γ hγ I A

/-- Paper: Remark 4.5.1.2, p. 198. Take the positive reals, period exp 1, and
I = (1,2). In log coordinates take a smooth bump ψ supported in (−1/4,1/4)
with ψ(0) = 1. Its translates ψ(x+n) are full-decay tests tending to zero in
the interval space, since each twist gains exp(−an) against polynomial growth
in n. Tensor with the constant 1 on the trivial kernel and pass to the completion.
Every periodization has value 1 at the identity class. -/
theorem Printed.modulatedIntervalPeriodization_projective_sequential_false :
    ¬ Printed.modulatedIntervalPeriodization_projective_sequential := by
  sorry

/-- Paper: Remark 4.5.1.4, p. 203. The forward map induced by ordinary
periodization on the quotient by its kernel is continuous. In the quotient
topology this is equivalent to continuity of the extension to the projective
completion. It agrees with (4.5.1.1) on its original full-decay domain.
Deviation: I is implicit in the remark. The counterexample works already for
full decay, I = ℝ. See ERRATA F174. -/
def Printed.modulatedIntervalPeriodization_projectiveQuotient_continuous : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (τ : ℝ≥0ˣ →ₜ* G), RightInverse τ m → ∀ (γ : G) (hγ : 1 < (m γ).val)
    (I : Set ℝ), OrdConnected I → I.Nonempty →
    let T := ProjectiveTensor (SchwartzBruhat m.toMonoidHom.ker) (PositiveRealExponentialDecay I)
    letI : UniformContinuousConstSMul ℂ T := uniformContinuousConstSMul_of_continuousConstSMul ℂ T
    ∃ A : Completion T →L[ℂ] SchwartzBruhat (G ⧸ Subgroup.zpowers γ),
      Printed.AgreesWithFullPeriodization m hm hms τ γ hγ I A

/-- Paper: Remark 4.5.1.4, p. 203. Use ℝ × ∏ⱼ ℤ/2 in log coordinates, with
module exp x, splitting through the identity of the compact factor, period
(1, 1), and I = ℝ. On the target the supremum of the jth derivative at zero
in the jth coordinate character is a continuous seminorm on the inductive
limit. Its pullback to pure tensors would be bounded by a product of two
continuous seminorms. On radial tests supported in (−1/4, 1/4), the radial
seminorm has some finite order N. Fix j > N and use that coordinate character
with a radial cutoff equal to one near zero times exp(inx). The output grows
as nʲ while the asserted bound grows at most as nᴺ. -/
theorem Printed.modulatedIntervalPeriodization_projectiveQuotient_continuous_false :
    ¬ Printed.modulatedIntervalPeriodization_projectiveQuotient_continuous := by
  sorry

/-- Paper: Theorem 4.5.2.3, (4.5.2.2), p. 207. As printed: For every compact
module window with nonempty interior, the map induced by inclusion from the
supported quotient to the full isotypic periodization quotient is a linear
homeomorphism. This is the isomorphism preceding the numbered parts.
The repaired statement is `modulatedCompactSupport_isotypicQuotient_equiv`.
See ERRATA F174. -/
def Printed.modulatedCompactSupport_isotypicQuotient_equiv : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m) (γ : G) (hγ : 1 < (m γ).val)
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G),
    (∀ (ω : PontryaginDual m.toMonoidHom.ker) (k : m.toMonoidHom.ker), χ ω k.val = ω k) →
    ∀ (ω : PontryaginDual m.toMonoidHom.ker) (B : Set ℝ≥0ˣ), IsCompact B → (interior B).Nonempty →
    let P := modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
    let D := modulatedCompactSupportSubmodule m B
    let N := P.ker.comap D.subtype
    ∃ e : (D ⧸ N) ≃L[ℂ] (ModulatedExponentialDecay m univ ⧸ P.ker),
      ∀ f : D, e (N.mkQ f) = P.ker.mkQ f.val

/-- A test in the decay space of the positive reals that vanishes off a closed window
vanishes at every point outside the interior of the window: its support is open. -/
private theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_vanish
    (B : Set ℝ≥0ˣ) (hB : IsClosed B)
    (d : modulatedCompactSupportSubmodule (ContinuousMonoidHom.id ℝ≥0ˣ) B)
    (x : ℝ≥0ˣ) (hx : x ∉ interior B) : d.val.val x = 0 := by
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hmem : d.val.val ∈ schwartzBruhatSubmodule ℝ≥0ˣ := by
    have h := (Submodule.mem_iInf _).mp d.val.property ⟨0, mem_univ 0⟩
    rwa [Submodule.mem_comap, modulationWeight_zero] at h
  have hc : Continuous d.val.val := schwartzBruhat_continuous (G := ℝ≥0ˣ) ⟨d.val.val, hmem⟩
  have hsupp := ((mem_modulatedCompactSupportSubmodule_iff (ContinuousMonoidHom.id ℝ≥0ˣ) B hB
    d.val).mp d.property).2
  by_contra hne
  exact hx (interior_maximal (subset_tsupport _ |>.trans hsupp)
    hc.isOpen_support (mem_support.mpr hne))

/-- On the positive reals with identity module, a test that vanishes off a closed window
whose interior misses the orbit of the identity has homogeneous periodization zero at the
identity class. -/
private theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_supported
    (_hSC : SecondCountableTopology ℝ≥0ˣ) (hBo : BorelSpace ℝ≥0ˣ)
    (hm : IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ)) (γ : ℝ≥0ˣ)
    (hγ : 1 < (ContinuousMonoidHom.id ℝ≥0ˣ γ).val)
    (μ₁ : Measure (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (ξ : PontryaginDual ℝ≥0ˣ) (B : Set ℝ≥0ˣ) (hB : IsClosed B)
    (hγB : ∀ n : ℤ, γ ^ n ∉ interior B)
    (d : modulatedCompactSupportSubmodule (ContinuousMonoidHom.id ℝ≥0ˣ) B) :
    modulatedIsotypicPeriodizationCLM (ContinuousMonoidHom.id ℝ≥0ˣ) γ hm surjective_id hγ μ₁ ξ
      d.val (QuotientGroup.mk 1) = 0 := by
  have hs := modulatedIsotypicPeriodization_hasSum (ContinuousMonoidHom.id ℝ≥0ˣ) γ hm
    surjective_id hγ μ₁ ξ d.val 1
  have hz (n : ℤ) : (∫ k : (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker,
      (ξ k.val : ℂ) * d.val.val (γ ^ n * (k.val * 1)) ∂μ₁) = 0 := by
    refine integral_eq_zero_of_ae (.of_forall fun k ↦ ?_)
    change (ξ k.val : ℂ) * d.val.val (γ ^ n * (k.val * 1)) = 0
    have hk : k.val = 1 := k.property
    rw [hk, mul_one, mul_one]
    exact mul_eq_zero_of_right _
      (Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_vanish B hB d _ (hγB n))
  have h0 : HasSum (fun n : ℤ ↦ ∫ k : (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker,
      (ξ k.val : ℂ) * d.val.val (γ ^ n * (k.val * 1)) ∂μ₁) 0 := by
    simp only [hz]
    exact hasSum_zero
  exact hs.unique h0

/-- A smooth bump of radius 1/2 at the origin sums to one over the integers. -/
private theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_bumpSum
    (φ : ContDiffBump (0 : ℝ)) (hφ : φ.rOut = 1 / 2) :
    HasSum (fun n : ℤ ↦ (φ (n : ℝ) : ℂ)) 1 := by
  have hs1 := hasSum_single (f := fun n : ℤ ↦ (φ (n : ℝ) : ℂ)) 0 fun n hn ↦ by
    have hn' : (1 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast Int.one_le_abs hn
    have hdist : φ.rOut ≤ dist (n : ℝ) 0 := by
      rw [Real.dist_0_eq_abs, hφ]
      linarith
    change ((φ (n : ℝ) : ℝ) : ℂ) = 0
    rw [φ.zero_of_le_dist hdist, Complex.ofReal_zero]
  have hv : (fun n : ℤ ↦ (φ (n : ℝ) : ℂ)) 0 = 1 := by
    change ((φ ((0 : ℤ) : ℝ) : ℝ) : ℂ) = 1
    rw [Int.cast_zero, φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le),
      Complex.ofReal_one]
  exact hv ▸ hs1

/-- On the positive reals with identity module, if the generator has logarithm one, a
lifted logarithmic bump has homogeneous periodization one at the identity class. -/
private theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_bump
    (hSC : SecondCountableTopology ℝ≥0ˣ) (hBo : BorelSpace ℝ≥0ˣ)
    (hm : IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ)) (γ : ℝ≥0ˣ)
    (hγ : 1 < (ContinuousMonoidHom.id ℝ≥0ˣ γ).val)
    (hpow : ∀ n : ℤ, Real.log ((γ ^ n).val : ℝ) = n)
    (μ₁ : Measure (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker) [μ₁.IsHaarMeasure]
    (ξ : PontryaginDual ℝ≥0ˣ) :
    ∃ g : ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) univ,
      modulatedIsotypicPeriodizationCLM (ContinuousMonoidHom.id ℝ≥0ˣ) γ hm surjective_id hγ μ₁ ξ
        g (QuotientGroup.mk 1) = 1 := by
  let m := ContinuousMonoidHom.id ℝ≥0ˣ
  let C : TopologicalSpace.Compacts ℝ := ⟨Metric.closedBall 0 (1 / 2), isCompact_closedBall 0 _⟩
  let φ : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let w : ContDiffMapSupportedIn ℝ ℂ ⊤ C :=
    ⟨fun x ↦ (φ x : ℂ), Complex.ofRealCLM.contDiff.comp φ.contDiff, fun x hx ↦ by
      have hx' : φ.rOut ≤ dist x 0 := le_of_lt (not_le.mp hx)
      change ((φ x : ℝ) : ℂ) = 0
      rw [φ.zero_of_le_dist hx', Complex.ofReal_zero]⟩
  let p := compactLogProfileInclusion C w
  let τ : ℝ≥0ˣ →ₜ* ℝ≥0ˣ := ContinuousMonoidHom.id _
  have hτ : RightInverse τ m := fun _ ↦ rfl
  have hJ₀ := modulatedCompactSupport_isotypicQuotient_equiv_profileLift m hm μ₁ τ hτ ξ
  have hJ := hJ₀.choose_spec.1
  refine ⟨hJ₀.choose p, ?_⟩
  have hs := modulatedIsotypicPeriodization_hasSum m γ hm surjective_id hγ μ₁ ξ (hJ₀.choose p) 1
  have hterm (n : ℤ) : (∫ k : m.toMonoidHom.ker,
      (ξ k.val : ℂ) * (hJ₀.choose p).val (γ ^ n * (k.val * 1)) ∂μ₁) = (φ (n : ℝ) : ℂ) := by
    have hpt (k : m.toMonoidHom.ker) : γ ^ n * (k.val * 1) = k.val * τ (γ ^ n) := by
      rw [mul_one]
      exact mul_comm _ _
    calc _ = ∫ k : m.toMonoidHom.ker, (ξ k.val : ℂ) * (hJ₀.choose p).val (k.val * τ (γ ^ n)) ∂μ₁ :=
          integral_congr_ae (.of_forall fun k ↦
            congrArg (fun y ↦ (ξ k.val : ℂ) * (hJ₀.choose p).val y) (hpt k))
      _ = p.val (Real.log ((γ ^ n).val : ℝ)) := hJ p (γ ^ n)
      _ = _ := by
        rw [hpow]
        rfl
  have hs' : HasSum (fun n : ℤ ↦ (φ (n : ℝ) : ℂ))
      (modulatedIsotypicPeriodizationCLM m γ hm surjective_id hγ μ₁ ξ (hJ₀.choose p)
        (QuotientGroup.mk 1)) := by
    simp only [← hterm]
    exact hs
  exact hs'.unique
    (Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_bumpSum φ rfl)

/-- Paper: Theorem 4.5.2.3, (4.5.2.2), p. 207. Take the positive reals with
identity module, the trivial character, γ > 1 and B = [1, γ]. Every smooth
test supported in B vanishes at both endpoints. These are the only orbit
points of the identity in B, so every supported periodization vanishes there.
A nonnegative smooth compactly supported test positive at 1 has nonzero
periodization at the identity, giving a missing class in the full quotient. -/
theorem Printed.modulatedCompactSupport_isotypicQuotient_equiv_false :
    ¬ Printed.modulatedCompactSupport_isotypicQuotient_equiv := by
  intro h
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hm : IsModulation (ContinuousMonoidHom.id ℝ≥0ˣ) :=
    ⟨isProperMap_id, ⟨Units.mk0 2 (by norm_num), by
      intro h
      have := congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) h
      norm_num at this⟩⟩
  -- Logarithmic coordinates.
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr t.zero_lt)).symm
  let γ : ℝ≥0ˣ := e.symm 1
  have hlogγ : Real.log (γ.val : ℝ) = 1 := (he γ).symm.trans (e.apply_symm_apply 1)
  have hγ : 1 < (ContinuousMonoidHom.id ℝ≥0ˣ γ).val := by
    have h1 := (Real.log_pos_iff (NNReal.coe_nonneg _)).mp (hlogγ.symm ▸ one_pos)
    exact_mod_cast h1
  have hpow (n : ℤ) : Real.log ((γ ^ n).val : ℝ) = n := by
    rw [← mul_one (γ ^ n), modulatedCompactSupport_isotypicQuotient_equiv_log,
      Units.val_one, NNReal.coe_one, Real.log_one, zero_add]
    exact (congrArg ((n : ℝ) * ·) hlogγ).trans (mul_one _)
  -- The norm-one group is trivial.
  let K := (ContinuousMonoidHom.id ℝ≥0ˣ).toMonoidHom.ker
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure K := Measure.haar
  let χ : PontryaginDual K → PontryaginDual ℝ≥0ˣ := fun _ ↦ 1
  have hχ (ω : PontryaginDual K) (k : K) : χ ω k.val = ω k := by
    have hk : k = 1 := Subtype.ext k.property
    rw [hk]
    exact (map_one (χ ω)).trans (map_one ω).symm
  -- The window B = exp [0, 1] = [1, γ].
  let B : Set ℝ≥0ˣ := e ⁻¹' Icc 0 1
  have hBc : IsCompact B := e.isCompact_preimage.mpr isCompact_Icc
  have hBint : interior B = e ⁻¹' Ioo 0 1 := by
    change interior (e ⁻¹' Icc 0 1) = _
    rw [← e.preimage_interior, interior_Icc]
  have hBi : (interior B).Nonempty :=
    ⟨e.symm (1 / 2), by rw [hBint, mem_preimage, e.apply_symm_apply]; norm_num⟩
  have hγB (n : ℤ) : γ ^ n ∉ interior B := by
    rw [hBint, mem_preimage, he, hpow]
    rintro ⟨h0, h1⟩
    have h0' : (0 : ℤ) < n := by exact_mod_cast h0
    have h1' : n < 1 := by exact_mod_cast h1
    omega
  have hF₀ := h ℝ≥0ˣ (ContinuousMonoidHom.id ℝ≥0ˣ) hm surjective_id γ hγ μ₁ χ hχ 1 B hBc hBi
  have hd := Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_supported ‹_› ‹_› hm γ hγ μ₁
    (χ 1) B hBc.isClosed hγB
  have hg := Printed.modulatedCompactSupport_isotypicQuotient_equiv_false_bump ‹_› ‹_› hm γ hγ hpow μ₁
    (χ 1)
  -- Inclusion is onto, so some supported test has the periodization of g.
  obtain ⟨g, hg1⟩ := hg
  obtain ⟨F, hF⟩ := hF₀
  obtain ⟨z, hz⟩ := F.surjective (Submodule.mkQ _ g)
  obtain ⟨d, rfl⟩ := Submodule.mkQ_surjective _ z
  have h1 := (hF d).symm.trans hz
  have h2 := (Submodule.Quotient.eq _).mp h1
  have h3 : modulatedIsotypicPeriodizationCLM (ContinuousMonoidHom.id ℝ≥0ˣ) γ hm surjective_id
      hγ μ₁ (χ 1) (d.val - g) = 0 := h2
  rw [map_sub, sub_eq_zero] at h3
  have h4 := congrArg (fun f : SchwartzBruhat (ℝ≥0ˣ ⧸ Subgroup.zpowers γ) ↦
    f (QuotientGroup.mk 1)) h3
  exact zero_ne_one ((hd d).symm.trans (h4.trans hg1))

end RiemannMasullo
