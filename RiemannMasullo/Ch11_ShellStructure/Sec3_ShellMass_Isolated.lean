module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_IndentationShells

/-! # A simultaneous bound for the normalized indentation shells of §11.3 -/

@[expose] public noncomputable section

namespace RiemannMasullo.Isolated

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical

variable {F : Type*} [Field F] [NumberField F]

local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "H𝔽" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "prin" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "π𝔽" => QuotientGroup.mk' H𝔽
local instance instIdeleMeasurableSpaceShellMass : MeasurableSpace I𝔽 := borel _
local instance instIdeleT2ShellMass : T2Space I𝔽 := (ideleGroup_topology F).1
local instance instIdeleBorelShellMass : BorelSpace I𝔽 := ⟨rfl⟩
local instance instNumberFieldCountableShellMass : Countable F := Countable.of_moduleFinite (R := ℚ)
local instance instFieldUnitsCountableShellMass : Countable Fˣ := Units.val_injective.countable
local instance instPrincipalCountableShellMass : Countable H𝔽 :=
  (IdeleGroup.unitEmbedding (𝓞 F) F).rangeRestrict_surjective.countable

private theorem hasSum_sheets {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    (x : I𝔽) : HasSum (fun r : Fˣ ↦ b (prin r * x)) 1 := by
  let e : Fˣ ≃ H𝔽 :=
    (MonoidHom.ofInjective (f := prin) (ideleGroup_quotient.{_, 0} F).1).toEquiv
  obtain ⟨hi, hone⟩ := hb.2.2.2 x
  have hsum : HasSum (fun r : H𝔽 ↦ b ((r : I𝔽)⁻¹ * x)) 1 := by
    have ht : ∑' r : H𝔽, b ((r : I𝔽)⁻¹ * x) = 1 := by
      simpa [integral_countable hi] using hone
    exact ht ▸ ((integrable_count_iff.mp hi).of_norm).hasSum
  apply (e.trans (Equiv.inv H𝔽)).hasSum_iff.mpr hsum |>.congr_fun
  intro r
  simp only [Function.comp_apply, Equiv.trans_apply, Equiv.inv_apply, Subgroup.coe_inv, inv_inv]
  rfl

private theorem prefixMass_properties {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    (x y : I𝔽) :
    let mass := fun T : Finset V ↦ divisorialIndentationPrefixMass T b x y
    Antitone mass ∧ mass ∅ = 1 ∧ ∀ T, 0 ≤ mass T := by
  let A (T : Finset V) : Set (Fˣ × Fˣ) :=
    {rs | ∀ v ∈ T, Valued.v ((prin rs.1).val.2 v) = Valued.v ((prin rs.2 * y).val.2 v)}
  let w (rs : Fˣ × Fˣ) := b (prin rs.1 * x) * b (prin rs.2 * y)
  have hw₀ (rs : Fˣ × Fˣ) : 0 ≤ w rs := mul_nonneg (hb.2.1 _) (hb.2.1 _)
  have hx := hasSum_sheets hb x
  have hy := hasSum_sheets hb y
  have hw : Summable w :=
    hx.summable.mul_of_nonneg hy.summable (fun _ ↦ hb.2.1 _) (fun _ ↦ hb.2.1 _)
  have hmass (T : Finset V) :
      divisorialIndentationPrefixMass T b x y = ∑' i, (A T).indicator w i := by
    apply tsum_congr
    intro i
    simp [A, w, Set.indicator]
  refine ⟨fun T U hTU ↦ ?_, ?_, fun T ↦ ?_⟩
  · change divisorialIndentationPrefixMass U b x y ≤ divisorialIndentationPrefixMass T b x y
    rw [hmass, hmass]
    have hA : A U ⊆ A T := fun _ hi v hv ↦ hi v (hTU hv)
    exact (hw.indicator (A U)).tsum_le_tsum
      (Set.indicator_le_indicator_of_subset hA hw₀) (hw.indicator (A T))
  · change divisorialIndentationPrefixMass ∅ b x y = 1
    have hA : A ∅ = univ := by ext i; simp [A]
    rw [hmass, hA, indicator_univ, hw.tsum_prod]
    change (∑' r : Fˣ, ∑' s : Fˣ, b (prin r * x) * b (prin s * y)) = 1
    simp_rw [tsum_mul_left, hy.tsum_eq, mul_one]
    exact hx.tsum_eq
  · change 0 ≤ divisorialIndentationPrefixMass T b x y
    rw [hmass]
    exact tsum_nonneg (indicator_nonneg (fun i _ ↦ hw₀ i))

private theorem sum_prefixLoss_le_one (mass : ℕ → ℝ) (hm : Antitone mass)
    (hzero : mass 0 = 1) (hpos : ∀ n, 0 ≤ mass n) (J : Finset ℕ) :
    ∑ k ∈ J, (mass k - mass (k + 1)) ≤ 1 := by
  let N := J.sup id + 1
  have hJ : J ⊆ Finset.range N := fun k hk ↦
    Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.le_sup (f := id) hk))
  calc
    _ ≤ ∑ k ∈ Finset.range N, (mass k - mass (k + 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hJ (fun k _ _ ↦ sub_nonneg.mpr (hm k.le_succ))
    _ = mass 0 - mass N := Finset.sum_range_sub' mass N
    _ ≤ 1 := by rw [hzero]; exact sub_le_self _ (hpos N)

/-- Paper: (11.3.1.4), p. 494, and Theorem 11.3.2.1, p. 495.
The sum of the absolute principal-orbit shell masses over any finite set of
layers is bounded by the norm of the original quotient kernel value.
Deviation: Replace the printed section weight (11.3.2.2) by a normalized
indentation from (12.2.2.2), p. 508. The orbital Poisson equality requires
a separate comparison. -/
theorem sum_norm_divisorialKernelDifference_indentation_le (S : Finset V) (J : Finset ℕ)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    (K : (I𝔽 ⧸ H𝔽) × (I𝔽 ⧸ H𝔽) → ℂ) (x y : I𝔽) :
    (∑ k ∈ J, ‖∑' ξ : Fˣ, divisorialKernelDifference S k
      (diagonalIndentationLift H𝔽 Measure.count b K) (x, prin ξ * y)‖) ≤
      ‖K (π𝔽 x, π𝔽 y)‖ := by
  let mass (k : ℕ) := divisorialIndentationPrefixMass (primaryDivisorialPlaces F S k) b x y
  obtain ⟨hm, hzero, hpos⟩ := prefixMass_properties hb x y
  have hanti : Antitone mass := hm.comp_monotone (primaryDivisorialPlaces_mono S)
  have hbudget := sum_prefixLoss_le_one mass hanti
    (by simpa [mass, primaryDivisorialPlaces] using hzero) (fun k ↦ hpos _) J
  have hshell (k : ℕ) :
      ‖∑' ξ : Fˣ, divisorialKernelDifference S k
        (diagonalIndentationLift H𝔽 Measure.count b K) (x, prin ξ * y)‖ =
        (mass k - mass (k + 1)) * ‖K (π𝔽 x, π𝔽 y)‖ := by
    rw [(hasSum_divisorialKernelDifference_indentation_prefixMass S k hb K x y).tsum_eq]
    change ‖((mass (k + 1) - mass k : ℝ) : ℂ) * _‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonpos (sub_nonpos.mpr (hanti k.le_succ)), neg_sub]
  simp_rw [hshell]
  rw [← Finset.sum_mul]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hbudget (norm_nonneg _)

/-- Paper: Theorem 11.3.2.1, p. 495. After any measured sampling of the two ideles,
the integrated shell norms share the same absolute kernel integral as a bound. The
pointwise estimate makes every measurable sampled shell integrable.
Deviation: Integrate the bound for the normalized indentation (12.2.2.2), p. 508,
in place of the printed section weight (11.3.2.2). The orbital Poisson equality
requires a separate comparison. -/
theorem sum_norm_integral_divisorialKernelDifference_indentation_le
    {Z : Type*} [MeasurableSpace Z] (μ : Measure Z) (S : Finset V) (J : Finset ℕ)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    (K : (I𝔽 ⧸ H𝔽) × (I𝔽 ⧸ H𝔽) → ℂ) (x y : Z → I𝔽)
    (hK : Integrable (fun z ↦ K (π𝔽 (x z), π𝔽 (y z))) μ) :
    let shell := fun (k : ℕ) (z : Z) ↦
      ∑' ξ : Fˣ, divisorialKernelDifference S k
        (diagonalIndentationLift H𝔽 Measure.count b K) (x z, prin ξ * y z)
    (∀ k ∈ J, AEStronglyMeasurable (shell k) μ) →
      (∑ k ∈ J, ‖∫ z, shell k z ∂μ‖) ≤ ∫ z, ‖K (π𝔽 (x z), π𝔽 (y z))‖ ∂μ := by
  intro shell hmeas
  have hle (z : Z) : (∑ k ∈ J, ‖shell k z‖) ≤ ‖K (π𝔽 (x z), π𝔽 (y z))‖ :=
    sum_norm_divisorialKernelDifference_indentation_le S J hb K (x z) (y z)
  have hint (k : ℕ) (hk : k ∈ J) : Integrable (shell k) μ :=
    hK.norm.mono' (hmeas k hk) (ae_of_all _ fun z ↦
      (Finset.single_le_sum (fun i _ ↦ norm_nonneg (shell i z)) hk).trans (hle z))
  calc
    _ ≤ ∑ k ∈ J, ∫ z, ‖shell k z‖ ∂μ :=
      Finset.sum_le_sum fun k _ ↦ norm_integral_le_integral_norm _
    _ = ∫ z, ∑ k ∈ J, ‖shell k z‖ ∂μ :=
      (integral_finsetSum J fun k hk ↦ (hint k hk).norm).symm
    _ ≤ _ := integral_mono_of_nonneg
      (ae_of_all _ fun z ↦ Finset.sum_nonneg fun k _ ↦ norm_nonneg (shell k z))
      hK.norm (ae_of_all _ hle)

end RiemannMasullo.Isolated
