module

public import RiemannMasullo.Ch11_ShellStructure.Sec3
public import RiemannMasullo.Ch12_TraceGeometric.Sec2

/-! # Individual divisorial shell masses for normalized indentations -/

@[expose] public noncomputable section

namespace RiemannMasullo

open IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NNReal

section DiscreteShifts

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [MeasurableSpace G]
  (H : Subgroup G) [Countable H] [MeasurableSingletonClass H]
  {b : G → ℝ} (hb : IsIndentation H Measure.count b)

include hb

private theorem hasSum_indentation_sheets (x : G) :
    HasSum (fun r : H ↦ b ((r : G) * x)) 1 := by
  obtain ⟨hi, h1⟩ := hb.2.2.2 x
  have hs := (integrable_count_iff.mp hi).of_norm
  have ht : ∑' r : H, b ((r : G)⁻¹ * x) = 1 := by
    simpa [integral_countable hi] using h1
  apply (Equiv.inv H).hasSum_iff.mp
  simpa only [Function.comp_apply, Equiv.inv_apply, Subgroup.coe_inv] using ht ▸ hs.hasSum

/-- Reindex the two independent sheets by their relative shift and the translate
appearing in the definition of the overlap. -/
private theorem hasSum_indentation_overlap_mask (A : Set H) (x y : G) :
    HasSum (fun h : H ↦ A.indicator
        (fun h : H ↦ diagonalIndentationWeight H Measure.count b (x, (h : G) * y)) h)
      (∑' rs : H × H, if rs.2 / rs.1 ∈ A then b ((rs.1 : G) * x) * b ((rs.2 : G) * y) else 0) := by
  let raw (rs : H × H) :=
    if rs.2 / rs.1 ∈ A then b ((rs.1 : G) * x) * b ((rs.2 : G) * y) else 0
  let e : H × H ≃ H × H :=
    { toFun := fun p ↦ (p.2⁻¹, p.2⁻¹ * p.1)
      invFun := fun p ↦ (p.2 / p.1, p.1⁻¹)
      left_inv := fun p ↦ Prod.ext (mul_div_cancel_left _ _) (inv_inv _)
      right_inv := fun p ↦ Prod.ext (inv_inv _) (by simp) }
  have hprod := (hasSum_indentation_sheets H hb x).summable.mul_of_nonneg
    (hasSum_indentation_sheets H hb y).summable (fun _ ↦ hb.2.1 _) (fun _ ↦ hb.2.1 _)
  have hraw : Summable raw := by
    apply (hprod.indicator {rs : H × H | rs.2 / rs.1 ∈ A}).congr
    intro rs
    simp [raw, Set.indicator]
  have hpair := e.summable_iff.mpr hraw
  have htotal : ∑' p : H × H, raw p = ∑' (h : H) (r : H), raw (e (h, r)) :=
    (e.tsum_eq raw).symm.trans hpair.tsum_prod
  rw [show (∑' rs : H × H, if rs.2 / rs.1 ∈ A then _ else _) = ∑' rs, raw rs from rfl, htotal]
  apply hpair.prod.hasSum.congr_fun
  intro h
  by_cases ha : h ∈ A
  · rw [indicator_of_mem ha]
    let z := (h : G) * y
    have hx := (hb.2.2.2 x).1
    have hz := (hb.2.2.2 z).1
    have hi : Integrable (fun r : H ↦ b ((r : G)⁻¹ * x) * b ((r : G)⁻¹ * z)) Measure.count :=
      hx.mul_bdd hz.aestronglyMeasurable
        (ae_of_all _ fun r ↦ (integrable_count_iff.mp hz).le_tsum r fun _ _ ↦ norm_nonneg _)
    change (∫ r : H, b ((r : G)⁻¹ * x) * b ((r : G)⁻¹ * z) ∂Measure.count) = _
    rw [integral_countable hi]
    apply tsum_congr
    intro r
    simp [e, raw, ha, z, mul_assoc]
  · rw [indicator_of_notMem ha]
    simp [e, raw, ha]

end DiscreteShifts

/-- Equal masses on nested sets force every positive atom in the larger set to
belong to the smaller set. -/
private theorem tsum_indicator_eq_iff_of_subset {ι : Type*} {f : ι → ℝ}
    (hf : Summable f) (hf₀ : ∀ i, 0 ≤ f i) {A B : Set ι} (hBA : B ⊆ A) :
    (∑' i, A.indicator f i) = ∑' i, B.indicator f i ↔
      ∀ i, 0 < f i → i ∈ A → i ∈ B := by
  have hle (i : ι) : B.indicator f i ≤ A.indicator f i := by
    by_cases hb : i ∈ B
    · simp [hb, hBA hb]
    · by_cases ha : i ∈ A <;> simp [ha, hb, hf₀]
  constructor
  · intro he i hi ha
    by_contra hb
    have hlt : B.indicator f i < A.indicator f i := by simpa [hb, ha] using hi
    have hlt' := (hf.indicator B).tsum_lt_tsum hle hlt (hf.indicator A)
    exact (ne_of_lt hlt') he.symm
  · intro h
    apply tsum_congr
    intro i
    by_cases hb : i ∈ B
    · simp [hb, hBA hb]
    · by_cases ha : i ∈ A
      · have hz : f i = 0 := le_antisymm (not_lt.mp fun hi ↦ hb (h i hi ha)) (hf₀ i)
        simp [ha, hb, hz]
      · simp [ha, hb]

section DivisorialShells

variable {F : Type*} [Field F] [NumberField F]

local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "H𝔽" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "prin" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "π𝔽" => QuotientGroup.mk' H𝔽
local instance instIdeleMeasurableSpaceShells : MeasurableSpace I𝔽 := borel _
local instance instIdeleT2Shells : T2Space I𝔽 := (ideleGroup_topology F).1
local instance instIdeleBorelShells : BorelSpace I𝔽 := ⟨rfl⟩
local instance instNumberFieldCountableShells : Countable F := Countable.of_moduleFinite (R := ℚ)
local instance instFieldUnitsCountableShells : Countable Fˣ := Units.val_injective.countable
local instance instPrincipalCountableShells : Countable H𝔽 :=
  (IdeleGroup.unitEmbedding (𝓞 F) F).rangeRestrict_surjective.countable

private def principalSheetEquiv : Fˣ ≃ H𝔽 :=
  (MonoidHom.ofInjective (f := prin) (ideleGroup_quotient.{_, 0} F).1).toEquiv

private theorem principalSheetEquiv_apply (r : Fˣ) :
    ((principalSheetEquiv r : H𝔽) : I𝔽) = prin r :=
  MonoidHom.ofInjective_apply (ideleGroup_quotient.{_, 0} F).1

/-- Paper: (11.3.1.4), p. 494, and (12.2.2.1), p. 508.
The probability that two independent principal translates carrying the indentation weights
pass the local unit tests at every place of a finite packet. The second valuation
includes the starting idele `y`, so this also applies to nonunit representatives.
Reconstruction: its successive differences give the actual shell masses by
`hasSum_divisorialKernelDifference_indentation_prefixMass`. -/
def divisorialIndentationPrefixMass (T : Finset V) (b : I𝔽 → ℝ) (x y : I𝔽) : ℝ :=
  ∑' rs : Fˣ × Fˣ, if ∀ v ∈ T, Valued.v ((prin rs.1).val.2 v) = Valued.v ((prin rs.2 * y).val.2 v)
    then b (prin rs.1 * x) * b (prin rs.2 * y) else 0

/-- Paper: Theorem 11.3.2.1, p. 495, with the normalized weight of Proposition
12.2.2.2, p. 508. A finite packet removes zero mass exactly when every pair of
positive sheets matching on the smaller packet also matches on the larger one. -/
theorem divisorialIndentationPrefixMass_eq_iff_of_subset {T U : Finset V} (hTU : T ⊆ U)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b) (x y : I𝔽) :
    divisorialIndentationPrefixMass T b x y = divisorialIndentationPrefixMass U b x y ↔
      ∀ r s : Fˣ, 0 < b (prin r * x) → 0 < b (prin s * y) →
        (∀ v ∈ T, Valued.v ((prin r).val.2 v) = Valued.v ((prin s * y).val.2 v)) →
        ∀ v ∈ U, Valued.v ((prin r).val.2 v) = Valued.v ((prin s * y).val.2 v) := by
  let A (P : Finset V) : Set (Fˣ × Fˣ) :=
    {rs | ∀ v ∈ P, Valued.v ((prin rs.1).val.2 v) = Valued.v ((prin rs.2 * y).val.2 v)}
  let w (rs : Fˣ × Fˣ) := b (prin rs.1 * x) * b (prin rs.2 * y)
  have hsum (z : I𝔽) : HasSum (fun r : Fˣ ↦ b (prin r * z)) 1 := by
    apply ((principalSheetEquiv (F := F)).hasSum_iff.mpr (hasSum_indentation_sheets H𝔽 hb z)).congr_fun
    intro r
    simp [principalSheetEquiv_apply]
  have hw : Summable w := (hsum x).summable.mul_of_nonneg (hsum y).summable
    (fun _ ↦ hb.2.1 _) (fun _ ↦ hb.2.1 _)
  have hA : A U ⊆ A T := fun _ hi v hv ↦ hi v (hTU hv)
  have hmass (P : Finset V) :
      divisorialIndentationPrefixMass P b x y = ∑' i, (A P).indicator w i := by
    apply tsum_congr
    intro i
    simp [A, w, Set.indicator]
  rw [hmass, hmass, tsum_indicator_eq_iff_of_subset hw (fun _ ↦ mul_nonneg (hb.2.1 _) (hb.2.1 _)) hA]
  constructor
  · intro h r s hr hs hm
    exact h (r, s) (mul_pos hr hs) hm
  · intro h ⟨r, s⟩ hp hm
    exact h r s (pos_of_mul_pos_left hp (hb.2.1 _)) (pos_of_mul_pos_right hp (hb.2.1 _)) hm

private theorem shellVal_mul (r s : I𝔽) (v : V) :
    Valued.v ((r * s).val.2 v) = Valued.v (r.val.2 v) * Valued.v (s.val.2 v) :=
  map_mul _ _ _

private theorem shellVal_ne_zero (r : I𝔽) (v : V) : Valued.v (r.val.2 v) ≠ 0 := by
  have h := congrArg (fun z : I𝔽 ↦ Valued.v (z.val.2 v)) (mul_inv_cancel r)
  change Valued.v (r.val.2 v * (r⁻¹).val.2 v) = Valued.v (1 : v.adicCompletion F) at h
  rw [map_mul, map_one] at h
  exact (mul_ne_zero_iff.mp (h.trans_ne one_ne_zero)).1

private theorem shell_ratio_mem_iff (T : Finset V) (y : I𝔽) (r s : H𝔽) :
    ((s / r : H𝔽) : I𝔽) * y ∈ divisorialStratum F T ↔
      ∀ v ∈ T, Valued.v ((r : I𝔽).val.2 v) = Valued.v (((s : I𝔽) * y).val.2 v) := by
  have he : (r : I𝔽) * (((s / r : H𝔽) : I𝔽) * y) = (s : I𝔽) * y := by
    rw [Subgroup.coe_div, ← mul_assoc, mul_comm (r : I𝔽) ((s : I𝔽) / (r : I𝔽)), div_mul_cancel]
  have hval (v : V) :
      Valued.v ((r : I𝔽).val.2 v) * Valued.v (((((s / r : H𝔽) : I𝔽) * y).val).2 v) =
        Valued.v (((s : I𝔽) * y).val.2 v) := by
    have h := congrArg (fun z : I𝔽 ↦ Valued.v (z.val.2 v)) he
    change Valued.v (((r : I𝔽) * _).val.2 v) = Valued.v (((s : I𝔽) * y).val.2 v) at h
    rwa [shellVal_mul (r : I𝔽) _ v] at h
  constructor
  · intro h v hv
    simpa only [h v hv, mul_one] using hval v
  · intro h v hv
    apply mul_left_cancel₀ (shellVal_ne_zero (r : I𝔽) v)
    rw [mul_one, hval v, h v hv]

private theorem hasSum_divisorialIndicator_indentation_prefixMass (T : Finset V)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    (x y : I𝔽) :
    HasSum (fun h : Fˣ ↦ divisorialIndicator T (prin h * y) *
        (diagonalIndentationWeight H𝔽 Measure.count b (x, prin h * y) : ℂ))
      (divisorialIndentationPrefixMass T b x y : ℂ) := by
  let e := principalSheetEquiv (F := F)
  have he (r : Fˣ) : ((e r : H𝔽) : I𝔽) = prin r := principalSheetEquiv_apply r
  let A : Set H𝔽 := {h | (h : I𝔽) * y ∈ divisorialStratum F T}
  let w (rs : H𝔽 × H𝔽) :=
    if rs.2 / rs.1 ∈ A then b ((rs.1 : I𝔽) * x) * b ((rs.2 : I𝔽) * y) else 0
  have hmass : (∑' rs, w rs) = divisorialIndentationPrefixMass T b x y := by
    rw [← (e.prodCongr e).tsum_eq w]
    apply tsum_congr
    rintro ⟨r, s⟩
    change (if (((e s / e r : H𝔽) : I𝔽) * y) ∈ divisorialStratum F T then _ else _) = _
    rw [shell_ratio_mem_iff T y]
    simp [he]
  have hshift := hasSum_indentation_overlap_mask H𝔽 hb A x y
  change HasSum _ (∑' rs, w rs) at hshift
  rw [hmass] at hshift
  apply (Complex.hasSum_ofReal.mpr (e.hasSum_iff.mpr hshift)).congr_fun
  intro h
  by_cases hunit : prin h * y ∈ divisorialStratum F T
  · have hA : e h ∈ A := hunit
    simp [divisorialIndicator_eq_indicator, hunit, Function.comp_apply, hA, he]
  · have hA : e h ∉ A := hunit
    simp [divisorialIndicator_eq_indicator, hunit, Function.comp_apply, hA]

/-- Paper: (11.3.1.4), p. 494, and (11.3.2.1), p. 495, with the normalized lift
(12.2.2.1–2), p. 508. The sum over the principal translates of one shell is the quotient
kernel times the change in the probability of matching valuations through that packet.
For arbitrary starting ideles the second sheet enters with the valuations of its translate.
Deviation: This determines the individual shell for any normalized indentation, before
angular or norm integration. The comparison with an orbital Poisson trace is separate. -/
theorem hasSum_divisorialKernelDifference_indentation_prefixMass (S : Finset V) (k : ℕ)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b) (K : (I𝔽 ⧸ H𝔽) × (I𝔽 ⧸ H𝔽) → ℂ)
    (x y : I𝔽) :
    HasSum (fun ξ : Fˣ ↦ divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
        (x, prin ξ * y))
      (((divisorialIndentationPrefixMass (primaryDivisorialPlaces F S (k + 1)) b x y -
        divisorialIndentationPrefixMass (primaryDivisorialPlaces F S k) b x y : ℝ) : ℂ) *
        K (π𝔽 x, π𝔽 y)) := by
  have hn := hasSum_divisorialIndicator_indentation_prefixMass (primaryDivisorialPlaces F S (k + 1)) hb x y
  have ho := hasSum_divisorialIndicator_indentation_prefixMass (primaryDivisorialPlaces F S k) hb x y
  rw [Complex.ofReal_sub]
  apply ((hn.sub ho).mul_right (K (π𝔽 x, π𝔽 y))).congr_fun
  intro ξ
  have hπ : π𝔽 (prin ξ) = 1 := (QuotientGroup.eq_one_iff _).mpr ⟨ξ, rfl⟩
  simp only [divisorialKernelDifference, diagonalIndentationLift, Prod.map_apply, map_mul,
    hπ, one_mul, sub_mul, mul_assoc]

/-- Paper: Theorem 11.3.2.1, p. 495, and Proposition 12.2.2.2, p. 508.
At arbitrary starting ideles the signed shell vanishes exactly when the quotient kernel
vanishes or each positive sheet pair passing the old local tests also passes the new ones. -/
theorem divisorialKernelDifference_indentation_eq_zero_iff (S : Finset V) (k : ℕ)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b) (K : (I𝔽 ⧸ H𝔽) × (I𝔽 ⧸ H𝔽) → ℂ)
    (x y : I𝔽) :
    (∑' ξ : Fˣ, divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
        (x, prin ξ * y)) = 0 ↔
      K (π𝔽 x, π𝔽 y) = 0 ∨ ∀ r s : Fˣ, 0 < b (prin r * x) → 0 < b (prin s * y) →
        (∀ v ∈ primaryDivisorialPlaces F S k,
          Valued.v ((prin r).val.2 v) = Valued.v ((prin s * y).val.2 v)) →
        ∀ v ∈ primaryDivisorialPlaces F S (k + 1),
          Valued.v ((prin r).val.2 v) = Valued.v ((prin s * y).val.2 v) := by
  rw [(hasSum_divisorialKernelDifference_indentation_prefixMass S k hb K x y).tsum_eq,
    mul_eq_zero, Complex.ofReal_eq_zero, sub_eq_zero, or_comm]
  exact or_congr Iff.rfl (eq_comm.trans (divisorialIndentationPrefixMass_eq_iff_of_subset
    (primaryDivisorialPlaces_mono S (Nat.le_succ k)) hb _ _))

/-- Paper: Theorem 11.3.2.1, p. 495, and Proposition 12.2.2.2, p. 508.
The signed shell formula at the canonical norm section and a finite-unit angular representative.
Over the rationals these are the samples used before angular integration. -/
theorem hasSum_normSection_divisorialKernelDifference_indentation (S : Finset V) (k : ℕ)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b) (K : (I𝔽 ⧸ H𝔽) × (I𝔽 ⧸ H𝔽) → ℂ)
    (t : ℝ≥0ˣ) (u : outsideIntegralIdeleUnits F ∅) :
    let x := canonicalIdeleNormSection F t
    let y := u.val * x
    HasSum (fun ξ : Fˣ ↦ divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
        (x, prin ξ * y))
      (((divisorialIndentationPrefixMass (primaryDivisorialPlaces F S (k + 1)) b x y -
        divisorialIndentationPrefixMass (primaryDivisorialPlaces F S k) b x y : ℝ) : ℂ) *
        K (π𝔽 x, π𝔽 y)) := by
  exact hasSum_divisorialKernelDifference_indentation_prefixMass S k hb K _ _

/-- Paper: Theorem 11.3.2.1, p. 495, and Proposition 12.2.2.2, p. 508.
On the sampled ideles, the principal sum of an individual normalized shell vanishes
exactly when the quotient kernel vanishes or the new packet separates no pair of
positive sheets whose valuations agreed through the preceding packet. -/
theorem normSection_divisorialKernelDifference_indentation_eq_zero_iff (S : Finset V) (k : ℕ)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b) (K : (I𝔽 ⧸ H𝔽) × (I𝔽 ⧸ H𝔽) → ℂ)
    (t : ℝ≥0ˣ) (u : outsideIntegralIdeleUnits F ∅) :
    let x := canonicalIdeleNormSection F t
    let y := u.val * x
    (∑' ξ : Fˣ, divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
        (x, prin ξ * y)) = 0 ↔
      K (π𝔽 x, π𝔽 y) = 0 ∨ ∀ r s : Fˣ, 0 < b (prin r * x) → 0 < b (prin s * y) →
        (∀ v ∈ primaryDivisorialPlaces F S k,
          Valued.v ((prin r).val.2 v) = Valued.v ((prin s).val.2 v)) →
        ∀ v ∈ primaryDivisorialPlaces F S (k + 1),
          Valued.v ((prin r).val.2 v) = Valued.v ((prin s).val.2 v) := by
  dsimp only
  let y := u.val * canonicalIdeleNormSection F t
  have hu : u.val ∈ sLocalDivisorialStratum F (∅ : Finset V) :=
    (mem_sLocalDivisorialStratum_iff ∅ _).2 ⟨1, u, by simp⟩
  have hy (v : V) : Valued.v (y.val.2 v) = 1 := by
    dsimp only [y]
    rw [shellVal_mul, hu v (by simp), canonicalIdeleNormSection_finite, one_mul]
    exact map_one _
  have he (s : Fˣ) (v : V) : Valued.v ((prin s * y).val.2 v) = Valued.v ((prin s).val.2 v) := by
    rw [shellVal_mul, hy, mul_one]
  simpa only [he] using divisorialKernelDifference_indentation_eq_zero_iff S k hb K
    (canonicalIdeleNormSection F t) y

end DivisorialShells

end RiemannMasullo
