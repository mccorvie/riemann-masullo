module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_IndentationShells
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-! # A necessary independence condition for retained shell weights -/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal ContDiff

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "H𝔽" => IdeleGroup.principalSubgroup (𝓞 F) F
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "𝒟" => BruhatCompactSupport C𝔽
local notation "π𝔽" => (QuotientGroup.mk' H𝔽)
local notation "πclass(" v ", " π ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v π
local notation "normValue(" x ")" => ((ideleClassNorm F x).val : ℝ)

local instance : MeasurableSpace I𝔽 := borel _
local instance : T2Space I𝔽 := (ideleGroup_topology F).1
local instance : BorelSpace I𝔽 := ⟨rfl⟩
local instance : Countable F := Countable.of_moduleFinite (R := ℚ)
local instance : Countable Fˣ := Units.val_injective.countable
local instance : Countable H𝔽 :=
  (IdeleGroup.unitEmbedding (𝓞 F) F).rangeRestrict_surjective.countable

/-- The scalar signed weight of a shell after summing over principal translates. -/
def retainedIndentationWeight (S : Finset V) (k : ℕ) (b : I𝔽 → ℝ) (x y : I𝔽) : ℂ :=
  ((divisorialIndentationPrefixMass (primaryDivisorialPlaces F S (k + 1)) b x y -
    divisorialIndentationPrefixMass (primaryDivisorialPlaces F S k) b x y : ℝ) : ℂ)

/-- The sum of a normalized lifted shell over the principal translates of its second input. -/
def retainedIndentationShell (S : Finset V) (k : ℕ) (b : I𝔽 → ℝ)
    (K : C𝔽 × C𝔽 → ℂ) (x y : I𝔽) : ℂ :=
  ∑' ξ : Fˣ, divisorialKernelDifference S k (diagonalIndentationLift H𝔽 Measure.count b K)
    (x, (IdeleGroup.unitEmbedding (𝓞 F) F ξ) * y)

/-- A principal sum factors as the signed shell weight times the common quotient kernel. -/
theorem retainedIndentationShell_eq_mul (S : Finset V) (k : ℕ)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b) (K : C𝔽 × C𝔽 → ℂ)
    (x y : I𝔽) :
    retainedIndentationShell S k b K x y =
      retainedIndentationWeight S k b x y * K (π𝔽 x, π𝔽 y) :=
  (hasSum_divisorialKernelDifference_indentation_prefixMass S k hb K x y).tsum_eq

/-- Paper: Theorem 11.3.2.1, p. 495, with normalized indentation as in
Proposition 12.2.2.2(2), p. 508.
Deviation: If a family of common kernels realizes a diagonal matrix of retained
shell integrals with nonzero diagonal, the retained weights have no nontrivial
linear relation almost everywhere on the sampled pairs. -/
theorem retainedIndentationWeight_independent_of_integral_matrix
    {Ω J : Type*} [MeasurableSpace Ω] [Fintype J] [DecidableEq J]
    (μ : Measure Ω) (x y : Ω → I𝔽) (S : Finset V) (k : J → ℕ)
    {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    (K : J → C𝔽 × C𝔽 → ℂ) (a : J → ℂ) (ha : ∀ j, a j ≠ 0)
    (hint : ∀ i j, Integrable (fun z ↦ retainedIndentationShell S (k i) b (K j) (x z) (y z)) μ)
    (hdiag : ∀ i j,
      (∫ z, retainedIndentationShell S (k i) b (K j) (x z) (y z) ∂μ) =
        if i = j then a j else 0)
    (c : J → ℂ)
    (hc : ∀ᵐ z ∂μ, ∑ i, c i * retainedIndentationWeight S (k i) b (x z) (y z) = 0) :
    ∀ j, c j = 0 := by
  intro j
  have hvanish : ∀ᵐ z ∂μ, ∑ i, c i *
      retainedIndentationShell S (k i) b (K j) (x z) (y z) = 0 := by
    filter_upwards [hc] with z hz
    simp only [retainedIndentationShell_eq_mul _ _ hb, ← mul_assoc, ← Finset.sum_mul, hz, zero_mul]
  have hz : (∫ z, ∑ i, c i * retainedIndentationShell S (k i) b (K j) (x z) (y z) ∂μ) = 0 := by
    rw [integral_congr_ae hvanish, integral_zero]
  rw [integral_finsetSum _ (fun i _ ↦ (hint i j).const_mul (c i))] at hz
  simp_rw [integral_const_mul, hdiag, mul_ite, mul_zero] at hz
  have hj : c j * a j = 0 := by simpa using hz
  exact (mul_eq_zero.mp hj).resolve_right (ha j)

private theorem isBruhatSmooth_comp_for_radial_bump {G : Type*} [CommGroup G]
    [TopologicalSpace G] {u : G → ℂ} (hu : IsBruhatSmooth u) {f : ℂ → ℂ}
    (hf : ContDiff ℝ (∞) f) : IsBruhatSmooth (fun x ↦ f (u x)) := by
  intro p
  obtain ⟨k, hk, hi, hdesc⟩ := hu p
  refine ⟨k, hk, fun h x ↦ congrArg f (hi h x), ?_⟩
  intro a ha
  obtain ⟨q, hq, hdiff⟩ := hdesc a ha
  exact ⟨fun y ↦ f (q y), fun x ↦ congrArg f (hq x),
    fun e z b ↦ (hf.of_le (by simp)).comp (hdiff e z b)⟩

private theorem exists_radial_quarter_bump {c : ℝ} (hc : 2 ≤ c) :
    ∃ φ : 𝒟,
      tsupport φ.val ⊆ {x | normValue(x) ∈ Icc (c - 1/4) (c + 1/4)} ∧
      (∀ x : C𝔽, normValue(x) = c → φ.val x = 1) ∧
      (∀ x y : C𝔽, normValue(x) = normValue(y) → φ.val x = φ.val y) := by
  let B : ContDiffBump c := ⟨1/8, 1/4, by norm_num, by norm_num⟩
  have hnc : Continuous (fun x : C𝔽 ↦ normValue(x)) := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  let χ : QuasiCharacter C𝔽 :=
    { toFun := fun x ↦ (normValue(x) : ℂ)
      map_one' := by simp
      map_mul' := by intro x y; simp
      continuous_toFun := Complex.continuous_ofReal.comp hnc }
  have hs : IsBruhatSmooth (fun x : C𝔽 ↦ (B normValue(x) : ℂ)) := by
    apply isBruhatSmooth_comp_for_radial_bump (u := fun x ↦ χ x)
      (f := fun z : ℂ ↦ (B z.re : ℂ))
      ((mem_bruhatSmoothSubmodule_iff _).1 (quasiCharacter_mem_bruhatSmooth χ))
    exact Complex.ofRealCLM.contDiff.comp (B.contDiff.comp Complex.reCLM.contDiff)
  have hband {r : ℝ} (hr : B r ≠ 0) : r ∈ Icc (c - 1/4) (c + 1/4) := by
    have hm := subset_tsupport _ hr
    rw [B.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, abs_le] at hm
    change -(1/4 : ℝ) ≤ r - c ∧ r - c ≤ 1/4 at hm
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  let unit (t : ℝ) : ℝ≥0ˣ := Units.mk0 (Real.exp t).toNNReal
    (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'
  have hu : Continuous unit := Units.continuous_iff.mpr
    ⟨continuous_real_toNNReal.comp Real.continuous_exp,
      (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun t ↦
        (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'⟩
  have hsupport : HasCompactSupport (fun x : C𝔽 ↦ (B normValue(x) : ℂ)) := by
    apply HasCompactSupport.intro ((isProperMap_ideleClassNorm F).isCompact_preimage
      ((isCompact_Icc (a := Real.log (c - 1/4)) (b := Real.log (c + 1/4))).image hu))
    intro x hx
    by_contra hn
    obtain ⟨hl, hr⟩ := hband (r := normValue(x)) (fun he ↦ hn (by rw [he, Complex.ofReal_zero]))
    have hpos : 0 < normValue(x) := NNReal.coe_pos.mpr (Units.zero_lt _)
    apply hx
    refine ⟨Real.log normValue(x),
      ⟨Real.log_le_log (by linarith) hl, Real.log_le_log hpos hr⟩, ?_⟩
    apply Units.ext
    change (Real.exp (Real.log _)).toNNReal = _
    rw [Real.exp_log hpos, Real.toNNReal_coe]
  let φ : 𝒟 := ⟨_, (mem_bruhatSmoothSubmodule_iff _).2 hs, hsupport⟩
  refine ⟨φ, ?_, ?_, ?_⟩
  · refine closure_minimal (fun x hx ↦ ?_) (isClosed_Icc.preimage hnc)
    exact hband (r := normValue(x)) (fun he ↦ hx (by change (B normValue(x) : ℂ) = 0; rw [he, Complex.ofReal_zero]))
  · intro x hx
    change (B normValue(x) : ℂ) = _
    rw [hx, B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le), Complex.ofReal_one]
  · intro x y hxy
    change (B normValue(x) : ℂ) = (B normValue(y) : ℂ)
    rw [hxy]

private theorem zpow_two_three_mem_quarter_band {p c : ℝ}
    (hp : p = 2 ∨ p = 3) (hc : c = 2 ∨ c = 3) {n : ℤ}
    (h : p ^ (-n) ∈ Icc (c - 1/4) (c + 1/4)) : p = c ∧ n = -1 := by
  have hp1 : 1 ≤ p := by rcases hp with rfl | rfl <;> norm_num
  have hc2 : 2 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  have hc3 : c ≤ 3 := by rcases hc with rfl | rfl <;> norm_num
  have hn : n = -1 := by
    by_contra hne
    have ha : 0 ≤ n ∨ n ≤ -2 := by omega
    rcases ha with ha | ha
    · have hl : p ^ (-n) ≤ 1 := zpow_le_one_of_nonpos₀ hp1 (by omega)
      linarith [h.1]
    · have h4 : 4 ≤ p ^ (2 : ℤ) := by rcases hp with rfl | rfl <;> norm_num
      have hl := zpow_le_zpow_right₀ hp1 (show (2 : ℤ) ≤ -n by omega)
      linarith [h.2]
  refine ⟨?_, hn⟩
  rw [hn, neg_neg, zpow_one] at h
  rcases hp with rfl | rfl <;> rcases hc with rfl | rfl
  · rfl
  · linarith [h.1]
  · linarith [h.2]
  · rfl

private theorem primeSample_quarter_band (v : V) (π : (v.adicCompletion F)ˣ)
    (hπ : Valued.v.IsUniformizer (π : v.adicCompletion F))
    (hp : (v.asIdeal.absNorm : ℝ) = 2 ∨ (v.asIdeal.absNorm : ℝ) = 3)
    {c : ℝ} (hc : c = 2 ∨ c = 3) {φ : 𝒟}
    (hφ : tsupport φ.val ⊆ {x | normValue(x) ∈ Icc (c - 1/4) (c + 1/4)})
    (hcenter : ∀ x : C𝔽, normValue(x) = c → φ.val x = 1) :
    (∑' n : ℤ, φ.val (πclass(v, π) ^ n)) =
      if (v.asIdeal.absNorm : ℝ) = c then 1 else 0 := by
  have hnorm (n : ℤ) : normValue(πclass(v, π) ^ n) = (v.asIdeal.absNorm : ℝ) ^ (-n) := by
    rw [map_zpow, ideleClassNorm_ofAdicCompletion, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow,
      Units.coe_map]
    change ‖π.val‖ ^ n = _
    rw [norm_uniformizer_adicCompletion v _ hπ, inv_zpow', zpow_neg]
  rw [tsum_eq_single (-1 : ℤ)]
  · split_ifs with h
    · apply hcenter
      rw [hnorm, neg_neg, zpow_one, h]
    · apply image_eq_zero_of_notMem_tsupport
      intro ht
      have hm := hφ ht
      rw [Set.mem_setOf_eq, hnorm] at hm
      exact h (zpow_two_three_mem_quarter_band hp hc hm).1
  · intro n hn
    apply image_eq_zero_of_notMem_tsupport
    intro ht
    have hm := hφ ht
    rw [Set.mem_setOf_eq, hnorm] at hm
    exact hn (zpow_two_three_mem_quarter_band hp hc hm).2

/-- Paper: Theorem 11.3.2.1, p. 495.
Compact radial Bruhat tests supported above norm one independently detect the
two prime-power sample sums at residue sizes two and three. -/
theorem exists_two_three_separating_orbital_tests (v₂ v₃ : V)
    (h₂ : (v₂.asIdeal.absNorm : ℝ) = 2) (h₃ : (v₃.asIdeal.absNorm : ℝ) = 3)
    (π₂ : (v₂.adicCompletion F)ˣ) (π₃ : (v₃.adicCompletion F)ˣ)
    (hπ₂ : Valued.v.IsUniformizer (π₂ : v₂.adicCompletion F))
    (hπ₃ : Valued.v.IsUniformizer (π₃ : v₃.adicCompletion F)) :
    ∃ φ₂ φ₃ : 𝒟,
      tsupport φ₂.val ⊆ {x | 1 < normValue(x)} ∧
      tsupport φ₃.val ⊆ {x | 1 < normValue(x)} ∧
      (∀ x y : C𝔽, normValue(x) = normValue(y) → φ₂.val x = φ₂.val y) ∧
      (∀ x y : C𝔽, normValue(x) = normValue(y) → φ₃.val x = φ₃.val y) ∧
      (∑' n : ℤ, φ₂.val (πclass(v₂, π₂) ^ n)) = 1 ∧
      (∑' n : ℤ, φ₂.val (πclass(v₃, π₃) ^ n)) = 0 ∧
      (∑' n : ℤ, φ₃.val (πclass(v₂, π₂) ^ n)) = 0 ∧
      (∑' n : ℤ, φ₃.val (πclass(v₃, π₃) ^ n)) = 1 := by
  obtain ⟨φ₂, hb₂, hφ₂, hr₂⟩ := exists_radial_quarter_bump (F := F) (c := 2) le_rfl
  obtain ⟨φ₃, hb₃, hφ₃, hr₃⟩ := exists_radial_quarter_bump (F := F) (c := 3) (by norm_num)
  refine ⟨φ₂, φ₃, ?_, ?_, hr₂, hr₃, ?_, ?_, ?_, ?_⟩
  · intro x hx
    change 1 < normValue(x)
    linarith [(hb₂ hx).1]
  · intro x hx
    change 1 < normValue(x)
    linarith [(hb₃ hx).1]
  · simpa [h₂] using primeSample_quarter_band v₂ π₂ hπ₂ (Or.inl h₂) (Or.inl rfl) hb₂ hφ₂
  · simpa [h₃] using primeSample_quarter_band v₃ π₃ hπ₃ (Or.inr h₃) (Or.inl rfl) hb₂ hφ₂
  · simpa [h₂] using primeSample_quarter_band v₂ π₂ hπ₂ (Or.inl h₂) (Or.inr rfl) hb₃ hφ₃
  · simpa [h₃] using primeSample_quarter_band v₃ π₃ hπ₃ (Or.inr h₃) (Or.inr rfl) hb₃ hφ₃

/-- Paper: Theorem 11.3.2.1, p. 495, with the normalized lift of p. 508.
Deviation: A test-independent indentation with equal sampled weights at two
retained shells of residue sizes two and three cannot recover both arithmetic
sums from a common quotient kernel, even if the kernel is allowed to vary with
the test. The samples can be taken on any measure space. -/
theorem retainedIndentationShell_two_three_mismatch_of_equal_weights
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (x y : Ω → I𝔽)
    (S : Finset V) (k₂ k₃ : ℕ) {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    (heq : ∀ᵐ z ∂μ, retainedIndentationWeight S k₂ b (x z) (y z) =
      retainedIndentationWeight S k₃ b (x z) (y z))
    (K : 𝒟 → C𝔽 × C𝔽 → ℂ) (a₂ a₃ : ℂ) (ha₂ : a₂ ≠ 0)
    (v₂ v₃ : V) (h₂ : (v₂.asIdeal.absNorm : ℝ) = 2) (h₃ : (v₃.asIdeal.absNorm : ℝ) = 3)
    (π₂ : (v₂.adicCompletion F)ˣ) (π₃ : (v₃.adicCompletion F)ˣ)
    (hπ₂ : Valued.v.IsUniformizer (π₂ : v₂.adicCompletion F))
    (hπ₃ : Valued.v.IsUniformizer (π₃ : v₃.adicCompletion F)) :
    ∃ φ : 𝒟, tsupport φ.val ⊆ {u | 1 < normValue(u)} ∧
      (∀ x y : C𝔽, normValue(x) = normValue(y) → φ.val x = φ.val y) ∧
      ((∫ z, retainedIndentationShell S k₂ b (K φ) (x z) (y z) ∂μ) ≠
        a₂ * (∑' n : ℤ, φ.val (πclass(v₂, π₂) ^ n)) ∨
      (∫ z, retainedIndentationShell S k₃ b (K φ) (x z) (y z) ∂μ) ≠
        a₃ * (∑' n : ℤ, φ.val (πclass(v₃, π₃) ^ n))) := by
  obtain ⟨φ, _, hφ, _, hrad, _, hsample₂, hsample₃, _, _⟩ :=
    exists_two_three_separating_orbital_tests v₂ v₃ h₂ h₃ π₂ π₃ hπ₂ hπ₃
  have hint :
      (∫ z, retainedIndentationShell S k₂ b (K φ) (x z) (y z) ∂μ) =
      ∫ z, retainedIndentationShell S k₃ b (K φ) (x z) (y z) ∂μ := by
    apply integral_congr_ae
    filter_upwards [heq] with z hz
    simp only [retainedIndentationShell_eq_mul _ _ hb, hz]
  refine ⟨φ, hφ, hrad, ?_⟩
  rw [hsample₂, hsample₃, mul_one, mul_zero, ← hint]
  by_cases h : (∫ z, retainedIndentationShell S k₂ b (K φ) (x z) (y z) ∂μ) = a₂
  · exact Or.inr (h.trans_ne ha₂)
  · exact Or.inl h


local notation "prin" => IdeleGroup.unitEmbedding (𝓞 F) F

private def constantSheetPrefixMass (T : Finset V) (A B : Fˣ → ℝ) : ℝ :=
  ∑' rs : Fˣ × Fˣ, if ∀ v ∈ T,
    Valued.v ((prin rs.1).val.2 v) = Valued.v ((prin rs.2).val.2 v)
    then A rs.1 * B rs.2 else 0

private theorem indentationPrefixMass_eq_of_constant_sheet_weights
    (T : Finset V) (A B : Fˣ → ℝ) {b : I𝔽 → ℝ} {x y : I𝔽}
    (h : ∀ r : Fˣ, b (prin r * x) = A r ∧ b (prin r * y) = B r)
    (hy : ∀ v : V, Valued.v (y.val.2 v) = 1) :
    divisorialIndentationPrefixMass T b x y = constantSheetPrefixMass T A B := by
  unfold divisorialIndentationPrefixMass constantSheetPrefixMass
  apply tsum_congr
  rintro ⟨r, s⟩
  have hv (v : V) : Valued.v ((prin s * y).val.2 v) = Valued.v ((prin s).val.2 v) := by
    change Valued.v (((prin s).val.2 v) * (y.val.2 v)) = _
    rw [map_mul, hy, mul_one]
  simp only [hv, (h r).1, (h s).2]

/-- Paper: Theorem 11.3.2.1, p. 495, with the normalized lift of p. 508.
Deviation: If the two principal-sheet laws are constant across the samples and the
second sampled idele is a finite unit, all retained shell integrals of a common
kernel are scalar multiples of the same integral. Hence no such indentation can
reproduce both orbital terms at residue sizes two and three for every radial test. -/
theorem retainedIndentationShell_two_three_mismatch_of_constant_sheet_weights
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (x y : Ω → I𝔽)
    (S : Finset V) (k₂ k₃ : ℕ) {b : I𝔽 → ℝ} (hb : IsIndentation H𝔽 Measure.count b)
    (A B : Fˣ → ℝ)
    (hweights : ∀ᵐ z ∂μ,
      (∀ r : Fˣ, b (prin r * x z) = A r ∧ b (prin r * y z) = B r) ∧
        (∀ v : V, Valued.v ((y z).val.2 v) = 1))
    (K : 𝒟 → C𝔽 × C𝔽 → ℂ) (a₂ a₃ : ℂ) (ha₂ : a₂ ≠ 0) (ha₃ : a₃ ≠ 0)
    (v₂ v₃ : V) (h₂ : (v₂.asIdeal.absNorm : ℝ) = 2) (h₃ : (v₃.asIdeal.absNorm : ℝ) = 3)
    (π₂ : (v₂.adicCompletion F)ˣ) (π₃ : (v₃.adicCompletion F)ˣ)
    (hπ₂ : Valued.v.IsUniformizer (π₂ : v₂.adicCompletion F))
    (hπ₃ : Valued.v.IsUniformizer (π₃ : v₃.adicCompletion F)) :
    ∃ φ : 𝒟, tsupport φ.val ⊆ {u | 1 < normValue(u)} ∧
      (∀ x y : C𝔽, normValue(x) = normValue(y) → φ.val x = φ.val y) ∧
      ((∫ z, retainedIndentationShell S k₂ b (K φ) (x z) (y z) ∂μ) ≠
        a₂ * (∑' n : ℤ, φ.val (πclass(v₂, π₂) ^ n)) ∨
      (∫ z, retainedIndentationShell S k₃ b (K φ) (x z) (y z) ∂μ) ≠
        a₃ * (∑' n : ℤ, φ.val (πclass(v₃, π₃) ^ n))) := by
  let d (k : ℕ) : ℂ :=
    ((constantSheetPrefixMass (primaryDivisorialPlaces F S (k + 1)) A B -
      constantSheetPrefixMass (primaryDivisorialPlaces F S k) A B : ℝ) : ℂ)
  let D (φ : 𝒟) : ℂ := ∫ z, K φ (π𝔽 (x z), π𝔽 (y z)) ∂μ
  have hfactor (φ : 𝒟) (k : ℕ) :
      (∫ z, retainedIndentationShell S k b (K φ) (x z) (y z) ∂μ) = d k * D φ := by
    unfold D
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hweights] with z hz
    simp only [retainedIndentationShell_eq_mul _ _ hb, retainedIndentationWeight, d,
      indentationPrefixMass_eq_of_constant_sheet_weights _ A B hz.1 hz.2]
  obtain ⟨φ₂, φ₃, hφ₂, hφ₃, hr₂, hr₃, h₂₂, h₃₂, _, h₃₃⟩ :=
    exists_two_three_separating_orbital_tests v₂ v₃ h₂ h₃ π₂ π₃ hπ₂ hπ₃
  by_contra hn
  push Not at hn
  obtain ⟨he₂, he₃⟩ := hn φ₂ hφ₂ hr₂
  rw [hfactor, h₂₂, mul_one] at he₂
  rw [hfactor, h₃₂, mul_zero] at he₃
  have hD : D φ₂ ≠ 0 := by
    intro hd
    rw [hd, mul_zero] at he₂
    exact ha₂ he₂.symm
  have hd₃ : d k₃ = 0 := (mul_eq_zero.mp he₃).resolve_right hD
  have he := (hn φ₃ hφ₃ hr₃).2
  rw [hfactor, hd₃, zero_mul, h₃₃, mul_one] at he
  exact ha₃ he.symm

end RiemannMasullo
