module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2b
import all RiemannMasullo.AppA_AlgebraicNT.Sec1

import all RiemannMasullo.AppA_AlgebraicNT.Sec3

/-!
# General convergence criteria for adelic theta

Masullo, §11.1.1, pp. 475–479. The limit functions are defined on ideles and
need not be Schwartz–Bruhat functions.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set Topology
open scoped Classical ENNReal NNReal NumberField.AdeleRing nonZeroDivisors

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "N[" F "]" => MonoidHom.ker (ideleNorm F)
local notation "C₁[" F "]" => MonoidHom.ker (ideleClassNorm F)
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "Frac[" F "]" => FractionalIdeal (𝓞 F)⁰ F
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "ideleValue" => fun (φ : ℬ[F]) (g : 𝕀[F]) ↦ φ (Multiplicative.ofAdd (Units.val g))
local notation "classOf" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "saturation" => fun (Z : Set 𝕀[F]) ↦ ⋃ ξ : Fˣ, (fun g ↦ principal ξ * g) '' Z

local instance instIdeleMeasurableSpaceSec1a : MeasurableSpace 𝕀[F] := borel _

/-- Paper: Lemma 11.1.1.1, p. 475. The pointwise limit of a sequence of
Schwartz–Bruhat functions restricted to the ideles is Borel measurable. -/
theorem measurable_ideleLimit (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (h : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g))) :
    Measurable f := by
  have hborel : BorelSpace 𝕀[F] := ⟨rfl⟩
  have hk : ∀ k, Measurable (fun g : 𝕀[F] ↦ ideleValue (φ k) g) := fun k ↦
    ((schwartzBruhat_continuous (φ k)).comp
      (continuous_ofAdd.comp Units.continuous_val)).measurable
  exact measurable_of_tendsto_metrizable hk (tendsto_pi_nhds.mpr h)

/-- Paper: Proposition 11.1.1.2, p. 476. The majorant series sums over the
nonzero elements of the given fractional ideal. -/
def fractionalIdealOrbitSum (I : Frac[F]) (α : 𝕀[F] → ℝ≥0) (g : 𝕀[F]) : ℝ :=
  ∑' ξ : {ξ : Fˣ // (ξ.val : F) ∈ I}, (α (principal ξ.val * g) : ℝ)

/-- Paper: Proposition 11.1.1.2, p. 476. If exactly one term indexed by a
nonzero element of the ideal can be nonzero, the series equals that term. -/
theorem fractionalIdealOrbitSum_eq_single (I : Frac[F]) (α : 𝕀[F] → ℝ≥0) (g : 𝕀[F])
    (ξ₀ : Fˣ) (hξ₀ : (ξ₀ : F) ∈ I)
    (h : ∀ ξ : Fˣ, (ξ : F) ∈ I → ξ ≠ ξ₀ → α (principal ξ * g) = 0) :
    fractionalIdealOrbitSum I α g = (α (principal ξ₀ * g) : ℝ) := by
  unfold fractionalIdealOrbitSum
  refine tsum_eq_single (⟨ξ₀, hξ₀⟩ : {ξ : Fˣ // (ξ.val : F) ∈ I}) fun ξ hξ ↦ ?_
  rw [h ξ.val ξ.property fun he ↦ hξ (Subtype.ext he), NNReal.coe_zero]

/-- Paper: Equation (11.1.1.3), p. 476. The theta series of an idele function
sums its values at all nonzero principal multiples of the idele. -/
def ideleThetaSum (f : 𝕀[F] → ℂ) (g : 𝕀[F]) : ℂ :=
  ∑' ξ : Fˣ, f (principal ξ * g)

/-- Paper: Equation (11.1.1.3), p. 476. On Schwartz–Bruhat inputs the
idele series equals the global adelic theta function evaluated on the idele class. -/
theorem ideleThetaSum_schwartzBruhat (φ : ℬ[F]) (g : 𝕀[F]) :
    ideleThetaSum (ideleValue φ) g = adelicTheta φ (classOf g) :=
  (adelicTheta_mk φ g).symm

/-- Paper: Proposition 11.1.1.2(2), p. 476. At each idele in the given set,
the absolute orbit-sum tails can be made small uniformly in the sequence index.
Deviation: This is an extra hypothesis for the convergence claim. -/
def HasUniformThetaTails (φ : ℕ → 𝕀[F] → ℂ) (Z : Set 𝕀[F]) : Prop :=
  ∀ g ∈ Z, ∀ ε : ℝ≥0∞, 0 < ε → ∃ s : Finset Fˣ, ∀ k,
    (∑' ξ : {ξ : Fˣ // ξ ∉ s}, ‖φ k (principal ξ.val * g)‖ₑ) < ε

/-- A family of complex numbers has arbitrarily small tails over the complements of
finite sets exactly when it is absolutely summable. -/
private theorem enorm_tails_lt_iff_summable_norm {ι : Type*} (a : ι → ℂ) :
    (∀ ε : ℝ≥0∞, 0 < ε → ∃ s : Finset ι, (∑' i : {i : ι // i ∉ s}, ‖a i.val‖ₑ) < ε) ↔
      Summable (fun i ↦ ‖a i‖) := by
  have hcoe : (∑' i, ‖a i‖ₑ) ≠ ⊤ ↔ Summable (fun i ↦ ‖a i‖) :=
    (ENNReal.tsum_coe_ne_top_iff_summable (f := fun i ↦ ‖a i‖₊)).trans NNReal.summable_coe.symm
  refine ⟨fun h ↦ hcoe.mp ?_, fun h ε hε ↦ ?_⟩
  · -- One finite set with tail below one bounds the whole series.
    obtain ⟨s, hs⟩ := h 1 one_pos
    have hfin : (∑ i ∈ s, ‖a i‖ₑ) < ⊤ := ENNReal.sum_lt_top.mpr fun _ _ ↦ eNorm_lt_top
    have hsplit := sum_add_tsum_compl s fun i ↦ ‖a i‖ₑ
    exact (hsplit ▸ ENNReal.add_lt_top.mpr ⟨hfin, hs.trans ENNReal.one_lt_top⟩).ne
  · -- A finite total mass makes the tails over finite complements tend to zero.
    exact ((ENNReal.tendsto_tsum_compl_atTop_zero (hcoe.mpr h)).eventually
      (gt_mem_nhds hε)).exists

/-- Paper: Proposition 11.1.1.2(2), p. 476. A constant sequence has
uniform tails exactly when its orbit series are absolutely summable.
Deviation: This checks the extra tail hypothesis. -/
theorem hasUniformThetaTails_const_iff (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F]) :
    HasUniformThetaTails (fun _ ↦ f) Z ↔
      ∀ g ∈ Z, Summable (fun ξ : Fˣ ↦ ‖f (principal ξ * g)‖) := by
  refine forall₂_congr fun g _ ↦ ?_
  change (∀ ε : ℝ≥0∞, 0 < ε → ∃ s : Finset Fˣ, ∀ _ : ℕ,
      (∑' ξ : {ξ : Fˣ // ξ ∉ s}, ‖f (principal ξ.val * g)‖ₑ) < ε) ↔ _
  exact (forall₂_congr fun ε _ ↦ exists_congr fun s ↦ forall_const ℕ).trans
    (enorm_tails_lt_iff_summable_norm fun ξ : Fˣ ↦ f (principal ξ * g))

/-- The orbit series of a Schwartz–Bruhat function at an idele is absolutely summable. -/
private theorem summable_norm_ideleValue_orbit (φ : ℬ[F]) (g : 𝕀[F]) :
    Summable (fun ξ : Fˣ ↦ ‖ideleValue φ (principal ξ * g)‖) := by
  have h := (adelicAverage_summableUniformlyOn (F := F) φ {(g, 0)} isCompact_singleton).summable
    (Set.mem_singleton (g, (0 : 𝔸[F])))
  refine h.congr fun ξ ↦ ?_
  change ‖φ (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] (ξ : F) + 0)))‖ =
    ‖φ (Multiplicative.ofAdd (algebraMap F 𝔸[F] (ξ : F) * g.val))‖
  rw [add_zero, mul_comm]

/-- If the orbit sums of an approximating sequence stay below a bound, so do the finite
partial sums of the orbit series of the pointwise limit. -/
private theorem sum_norm_orbit_le_of_tendsto_of_le (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (g : 𝕀[F])
    (hlim : ∀ ξ : Fˣ, Tendsto (fun k ↦ ideleValue (φ k) (principal ξ * g)) atTop
      (𝓝 (f (principal ξ * g))))
    (c : ℝ) (hc : ∀ k, (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ c)
    (s : Finset Fˣ) : ∑ ξ ∈ s, ‖f (principal ξ * g)‖ ≤ c := by
  have hsum : Tendsto (fun k ↦ ∑ ξ ∈ s, ‖ideleValue (φ k) (principal ξ * g)‖) atTop
      (𝓝 (∑ ξ ∈ s, ‖f (principal ξ * g)‖)) :=
    tendsto_finsetSum s fun ξ _ ↦ (hlim ξ).norm
  exact le_of_tendsto' hsum fun k ↦
    ((summable_norm_ideleValue_orbit (φ k) g).sum_le_tsum s fun _ _ ↦ norm_nonneg _).trans (hc k)

/-- If the orbit sums of an approximating sequence stay below a bound, the orbit series
of the pointwise limit is absolutely summable. -/
private theorem summable_norm_orbit_of_tendsto_of_le (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (g : 𝕀[F])
    (hlim : ∀ ξ : Fˣ, Tendsto (fun k ↦ ideleValue (φ k) (principal ξ * g)) atTop
      (𝓝 (f (principal ξ * g))))
    (c : ℝ) (hc : ∀ k, (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ c) :
    Summable (fun ξ : Fˣ ↦ ‖f (principal ξ * g)‖) :=
  summable_of_sum_le (fun _ ↦ norm_nonneg _) (sum_norm_orbit_le_of_tendsto_of_le φ f g hlim c hc)

/-- Extended by zero from a Borel set, each translate of a pointwise limit of
Schwartz–Bruhat functions is Borel measurable. -/
private theorem measurable_indicator_translate_of_tendsto (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    {Z : Set 𝕀[F]} (hZ : MeasurableSet Z) (ξ : Fˣ)
    (hlim : ∀ g ∈ Z, Tendsto (fun k ↦ ideleValue (φ k) (principal ξ * g)) atTop
      (𝓝 (f (principal ξ * g)))) :
    Measurable (Z.indicator fun g ↦ f (principal ξ * g)) := by
  have hborel : BorelSpace 𝕀[F] := ⟨rfl⟩
  have hk : ∀ k, Measurable
      (Z.indicator fun g : 𝕀[F] ↦ ideleValue (φ k) (principal ξ * g)) := fun k ↦
    ((schwartzBruhat_continuous (φ k)).comp (continuous_ofAdd.comp
      (Units.continuous_val.comp (continuous_const_mul (principal ξ))))).measurable.indicator hZ
  refine measurable_of_tendsto_metrizable hk (tendsto_pi_nhds.mpr fun g ↦ ?_)
  by_cases hg : g ∈ Z
  · simpa only [Set.indicator_of_mem hg] using hlim g hg
  · simpa only [Set.indicator_of_notMem hg] using tendsto_const_nhds

-- TODO(paper-gap): The limit is specified on Z, but (11.1.1.3) uses all of Fˣ Z.
-- Under the ideal-series interpretation, (11.1.1.2) on the whole saturation
-- forces every test function to vanish there. At 2^n g its right side is the
-- subseries on 2^n I, which tends to zero. The nontrivial criterion below
-- imposes the bound on Z. Its norm-convergence conclusion needs control of tails.
-- The references to (11.1.1.11) on pp. 477–478 point to the next corollary.

/-- Paper: Proposition 11.1.1.2(1), p. 476. The limit has an absolutely
summable theta series at every point of the Borel set.
Deviation: The limit is taken on the saturation of the set, and the total-mass
bound is imposed on the Borel set where the majorant is defined in part (1). -/
theorem summable_ideleThetaSum_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F])
    (hlim : ∀ g : 𝕀[F], g ∈ saturation Z → Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    ∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : Fˣ ↦ ‖f (principal ξ * g)‖) := by
  intro g hg
  refine hmajorant.elim fun α hα ↦ hα.elim fun I hI ↦ ?_
  exact summable_norm_orbit_of_tendsto_of_le φ f g
    (fun ξ ↦ hlim _ (Set.mem_iUnion.mpr ⟨ξ, g, hg, rfl⟩)) _ (hI.2.2.2.2 g hg)

/-- Paper: Proposition 11.1.1.2(1), p. 476. Extending the limit theta
series by zero from the Borel set gives a Borel function on the ideles.
Deviation: The pointwise limit is taken on the saturation, and the
total-mass bound is imposed on the Borel set. -/
theorem measurable_indicator_ideleThetaSum_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F])
    (hlim : ∀ g : 𝕀[F], g ∈ saturation Z → Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    Measurable (Z.indicator (ideleThetaSum f)) := by
  have hborel : BorelSpace 𝕀[F] := ⟨rfl⟩
  have hF : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have hFu : Countable Fˣ := Units.val_injective.countable
  have hsum := summable_ideleThetaSum_of_dominated φ f Z hlim hZ η hη r hr hmajorant
  -- Extend each term of the series by zero, so that it is a limit of Borel functions.
  let h : Fˣ → 𝕀[F] → ℂ := fun ξ ↦ Z.indicator fun g ↦ f (principal ξ * g)
  have hh : ∀ ξ, Measurable (h ξ) := fun ξ ↦
    measurable_indicator_translate_of_tendsto φ f hZ ξ fun g hg ↦
      hlim _ (Set.mem_iUnion.mpr ⟨ξ, g, hg, rfl⟩)
  have heq : Z.indicator (ideleThetaSum f) = fun g ↦ ∑' ξ, h ξ g := by
    funext g
    by_cases hg : g ∈ Z
    · simp only [h, Set.indicator_of_mem hg]
      rfl
    · simp only [h, Set.indicator_of_notMem hg, tsum_zero]
  have hsummable : ∀ g, Summable fun ξ ↦ h ξ g := by
    intro g
    by_cases hg : g ∈ Z
    · simpa only [h, Set.indicator_of_mem hg] using (hsum g hg).of_norm
    · simpa only [h, Set.indicator_of_notMem hg] using summable_zero
  rw [heq]
  -- The finite partial sums are Borel and converge pointwise along the finite subsets.
  exact measurable_of_tendsto_metrizable' (atTop : Filter (Finset Fˣ))
    (f := fun s g ↦ ∑ ξ ∈ s, h ξ g) (fun s ↦ Finset.measurable_sum s fun ξ _ ↦ hh ξ)
    (tendsto_pi_nhds.mpr fun g ↦ (hsummable g).hasSum)

/-- Paper: Proposition 11.1.1.2(2), p. 476. The limit theta sum is in
the finite-exponent Lᵣ space for the measure restricted to the Borel set.
Deviation: The pointwise limit is taken on the saturation, and the
total-mass bound is imposed on the Borel set. -/
theorem memLp_ideleThetaSum_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F])
    (hlim : ∀ g : 𝕀[F], g ∈ saturation Z → Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    MemLp (Z.indicator (ideleThetaSum f)) (ENNReal.ofReal r) (η.restrict Z) := by
  have hmeas : AEStronglyMeasurable (Z.indicator (ideleThetaSum f)) (η.restrict Z) :=
    (measurable_indicator_ideleThetaSum_of_dominated φ f Z hlim hZ η hη r hr
      hmajorant).aestronglyMeasurable
  refine hmajorant.elim fun α hα ↦ hα.elim fun I hI ↦ ?_
  -- On the Borel set the limit theta sum is dominated by the majorant series.
  refine hI.2.2.2.1.of_le hmeas ((ae_restrict_iff' hZ).mpr (Eventually.of_forall fun g hg ↦ ?_))
  have hlim' : ∀ ξ : Fˣ, Tendsto (fun k ↦ ideleValue (φ k) (principal ξ * g)) atTop
      (𝓝 (f (principal ξ * g))) := fun ξ ↦ hlim _ (Set.mem_iUnion.mpr ⟨ξ, g, hg, rfl⟩)
  rw [Set.indicator_of_mem hg]
  calc ‖ideleThetaSum f g‖ ≤ ∑' ξ : Fˣ, ‖f (principal ξ * g)‖ :=
        norm_tsum_le_tsum_norm
          (summable_norm_orbit_of_tendsto_of_le φ f g hlim' _ (hI.2.2.2.2 g hg))
    _ ≤ fractionalIdealOrbitSum I α g :=
        Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _)
          (sum_norm_orbit_le_of_tendsto_of_le φ f g hlim' _ (hI.2.2.2.2 g hg))
    _ ≤ ‖fractionalIdealOrbitSum I α g‖ := Real.le_norm_self _

/-- Paper: Proposition 11.1.1.2(2), p. 476. Each approximating theta sum
belongs to the Lᵣ space for the restricted measure.
Deviation: The total-mass bound is imposed on the Borel set. -/
theorem memLp_adelicTheta_of_dominated
    (φ : ℕ → ℬ[F]) (Z : Set 𝕀[F])
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    ∀ k, MemLp (fun g ↦ adelicTheta (φ k) (classOf g))
      (ENNReal.ofReal r) (η.restrict Z) := by
  intro k
  have hborel : BorelSpace 𝕀[F] := ⟨rfl⟩
  have hmeas : AEStronglyMeasurable (fun g : 𝕀[F] ↦ adelicTheta (φ k) (classOf g))
      (η.restrict Z) :=
    ((adelicTheta (φ k)).continuous.comp QuotientGroup.continuous_mk).aestronglyMeasurable
  refine hmajorant.elim fun α hα ↦ hα.elim fun I hI ↦ ?_
  -- On the Borel set each theta function is dominated by the majorant series.
  refine hI.2.2.2.1.of_le hmeas ((ae_restrict_iff' hZ).mpr (Eventually.of_forall fun g hg ↦ ?_))
  rw [← ideleThetaSum_schwartzBruhat]
  calc ‖ideleThetaSum (ideleValue (φ k)) g‖ ≤ ∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖ :=
        norm_tsum_le_tsum_norm (summable_norm_ideleValue_orbit (φ k) g)
    _ ≤ fractionalIdealOrbitSum I α g := hI.2.2.2.2 g hg k
    _ ≤ ‖fractionalIdealOrbitSum I α g‖ := Real.le_norm_self _

/-- If the terms converge one by one and the absolute tails outside finite sets are small
uniformly in the index, then the sums converge to the sum of the limits. -/
private theorem tendsto_eLpNorm_ideleThetaSum_of_dominated_tsum {ι : Type*} (a : ℕ → ι → ℂ)
    (b : ι → ℂ) (hab : ∀ i, Tendsto (fun k ↦ a k i) atTop (𝓝 (b i)))
    (htails : ∀ ε : ℝ≥0∞, 0 < ε → ∃ s : Finset ι, ∀ k,
      (∑' i : {i : ι // i ∉ s}, ‖a k i.val‖ₑ) < ε) :
    Tendsto (fun k ↦ ∑' i, a k i) atTop (𝓝 (∑' i, b i)) := by
  have haS : ∀ k, Summable (fun i ↦ ‖a k i‖) := fun k ↦
    (enorm_tails_lt_iff_summable_norm (a k)).mp fun ε hε ↦ (htails ε hε).imp fun _ hs ↦ hs k
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨s, hs⟩ := htails (ENNReal.ofReal (ε / 4)) (ENNReal.ofReal_pos.mpr (by positivity))
  -- The real tails of the approximating families are at most a quarter of `ε`.
  have hsub : ∀ k, Summable (fun i : {i : ι // i ∉ s} ↦ ‖a k i.val‖) := fun k ↦
    (haS k).comp_injective Subtype.val_injective
  have hatail : ∀ k, (∑' i : {i : ι // i ∉ s}, ‖a k i.val‖) ≤ ε / 4 := by
    intro k
    have heq : (∑' i : {i : ι // i ∉ s}, ‖a k i.val‖ₑ) =
        ENNReal.ofReal (∑' i : {i : ι // i ∉ s}, ‖a k i.val‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ norm_nonneg _) (hsub k)]
      simp only [ofReal_norm]
    have h := hs k
    rw [heq] at h
    exact ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h).le
  -- Passing to the limit on finite sets bounds the tail of the limit family.
  have hbfin : ∀ t : Finset {i : ι // i ∉ s}, ∑ i ∈ t, ‖b i.val‖ ≤ ε / 4 := fun t ↦
    le_of_tendsto' (tendsto_finsetSum t fun i _ ↦ (hab i.val).norm) fun k ↦
      ((hsub k).sum_le_tsum t fun _ _ ↦ norm_nonneg _).trans (hatail k)
  have hbsub : Summable (fun i : {i : ι // i ∉ s} ↦ ‖b i.val‖) :=
    summable_of_sum_le (fun _ ↦ norm_nonneg _) hbfin
  have hbtail : (∑' i : {i : ι // i ∉ s}, ‖b i.val‖) ≤ ε / 4 :=
    Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _) hbfin
  have hbS : Summable b := (Finset.summable_compl_iff s).mp hbsub.of_norm
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_finsetSum s fun i _ ↦ hab i) (ε / 4) (by positivity)
  refine ⟨N, fun k hk ↦ ?_⟩
  have hfin := hN k hk
  rw [dist_eq_norm] at hfin ⊢
  rw [← (haS k).of_norm.sum_add_tsum_subtype_compl s, ← hbS.sum_add_tsum_subtype_compl s]
  have hA : ‖∑' i : {i : ι // i ∉ s}, a k i.val‖ ≤ ε / 4 :=
    (norm_tsum_le_tsum_norm (hsub k)).trans (hatail k)
  have hB : ‖∑' i : {i : ι // i ∉ s}, b i.val‖ ≤ ε / 4 :=
    (norm_tsum_le_tsum_norm hbsub).trans hbtail
  calc ‖(∑ i ∈ s, a k i + ∑' i : {i : ι // i ∉ s}, a k i.val) -
          (∑ i ∈ s, b i + ∑' i : {i : ι // i ∉ s}, b i.val)‖
        = ‖(∑ i ∈ s, a k i - ∑ i ∈ s, b i) +
            (∑' i : {i : ι // i ∉ s}, a k i.val - ∑' i : {i : ι // i ∉ s}, b i.val)‖ := by
          congr 1; ring
    _ ≤ ‖∑ i ∈ s, a k i - ∑ i ∈ s, b i‖ +
          (‖∑' i : {i : ι // i ∉ s}, a k i.val‖ + ‖∑' i : {i : ι // i ∉ s}, b i.val‖) :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
    _ < ε := by linarith

/-- On the Borel set, the approximating theta functions converge pointwise to the limit
theta sum. -/
private theorem tendsto_eLpNorm_ideleThetaSum_of_dominated_pointwise
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F])
    (hlim : ∀ g : 𝕀[F], g ∈ saturation Z → Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (htails : HasUniformThetaTails (fun k ↦ ideleValue (φ k)) Z) (g : 𝕀[F]) (hg : g ∈ Z) :
    Tendsto (fun k ↦ adelicTheta (φ k) (classOf g)) atTop (𝓝 (ideleThetaSum f g)) :=
  (tendsto_eLpNorm_ideleThetaSum_of_dominated_tsum
    (fun k ξ ↦ ideleValue (φ k) (principal ξ * g)) (fun ξ ↦ f (principal ξ * g))
    (fun ξ ↦ hlim _ (Set.mem_iUnion.mpr ⟨ξ, g, hg, rfl⟩)) (htails g hg)).congr
    fun k ↦ ideleThetaSum_schwartzBruhat (φ k) g

/-- Paper: Proposition 11.1.1.2(2), p. 476. The approximating theta
functions converge to the limit theta sum in the restricted Lᵣ norm.
Deviation: The pointwise limit is taken on the saturation, the total-mass
bound is imposed on the Borel set, and the orbit series have uniform tails. -/
theorem tendsto_eLpNorm_ideleThetaSum_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (Z : Set 𝕀[F])
    (hlim : ∀ g : 𝕀[F], g ∈ saturation Z → Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hZ : MeasurableSet Z) (η : Measure 𝕀[F]) (hη : η.Regular) (r : ℝ) (hr : 1 ≤ r)
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
        Measurable (fun g : saturation Z ↦ α g.val) ∧
        (∀ g : 𝕀[F], g ∈ Z → Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦
          (α (principal ξ.val * g) : ℝ))) ∧
        Measurable (fun g : Z ↦ fractionalIdealOrbitSum I α g.val) ∧
        MemLp (fractionalIdealOrbitSum I α) (ENNReal.ofReal r) (η.restrict Z) ∧
        ∀ g : 𝕀[F], g ∈ Z → ∀ k,
          (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g)
    (htails : HasUniformThetaTails (fun k ↦ ideleValue (φ k)) Z) :
    Tendsto (fun k ↦ eLpNorm (fun g ↦
      adelicTheta (φ k) (classOf g) - Z.indicator (ideleThetaSum f) g)
      (ENNReal.ofReal r) (η.restrict Z)) atTop (𝓝 0) := by
  have hborel : BorelSpace 𝕀[F] := ⟨rfl⟩
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hp0 : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.mpr hr0).ne'
  have hptop : ENNReal.ofReal r ≠ ∞ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal r).toReal = r := ENNReal.toReal_ofReal hr0.le
  have hΘ := measurable_indicator_ideleThetaSum_of_dominated φ f Z hlim hZ η hη r hr hmajorant
  refine hmajorant.elim fun α hα ↦ hα.elim fun I hI ↦ ?_
  set S := fractionalIdealOrbitSum I α
  set G : ℕ → 𝕀[F] → ℂ := fun k g ↦ adelicTheta (φ k) (classOf g) - Z.indicator (ideleThetaSum f) g
  have hGm : ∀ k, Measurable (G k) := fun k ↦
    ((adelicTheta (φ k)).continuous.comp QuotientGroup.continuous_mk).measurable.sub hΘ
  -- On the Borel set both theta sums are dominated by the majorant series.
  have hbound : ∀ k, ∀ g ∈ Z, ‖G k g‖ ≤ 2 * S g := by
    intro k g hg
    have hlim' : ∀ ξ : Fˣ, Tendsto (fun k ↦ ideleValue (φ k) (principal ξ * g)) atTop
        (𝓝 (f (principal ξ * g))) := fun ξ ↦ hlim _ (Set.mem_iUnion.mpr ⟨ξ, g, hg, rfl⟩)
    have h1 : ‖adelicTheta (φ k) (classOf g)‖ ≤ S g := by
      rw [← ideleThetaSum_schwartzBruhat]
      exact (norm_tsum_le_tsum_norm (summable_norm_ideleValue_orbit (φ k) g)).trans
        (hI.2.2.2.2 g hg k)
    have h2 : ‖ideleThetaSum f g‖ ≤ S g :=
      (norm_tsum_le_tsum_norm
          (summable_norm_orbit_of_tendsto_of_le φ f g hlim' _ (hI.2.2.2.2 g hg))).trans
        (Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _)
          (sum_norm_orbit_le_of_tendsto_of_le φ f g hlim' _ (hI.2.2.2.2 g hg)))
    calc ‖G k g‖ ≤ ‖adelicTheta (φ k) (classOf g)‖ + ‖ideleThetaSum f g‖ := by
          simp only [G, Set.indicator_of_mem hg]
          exact norm_sub_le _ _
      _ ≤ 2 * S g := by linarith
  -- Dominated convergence for the `r`-th powers of the differences.
  have hint : Tendsto (fun k ↦ ∫⁻ g, ‖G k g‖ₑ ^ r ∂(η.restrict Z)) atTop (𝓝 0) := by
    have hfin : ∫⁻ g, ‖(2 : ℂ) * (S g : ℂ)‖ₑ ^ r ∂(η.restrict Z) ≠ ∞ := by
      have hm : MemLp (fun g ↦ (2 : ℂ) * (S g : ℂ)) (ENNReal.ofReal r) (η.restrict Z) :=
        (hI.2.2.2.1.ofReal.const_mul 2)
      have := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp0 hptop hm.eLpNorm_lt_top
      rw [hpr] at this
      exact this.ne
    have hlim0 := tendsto_lintegral_of_dominated_convergence
      (fun g ↦ ‖(2 : ℂ) * (S g : ℂ)‖ₑ ^ r) (fun k ↦ (hGm k).eNorm.pow_const r)
      (fun k ↦ (ae_restrict_iff' hZ).mpr (Eventually.of_forall fun g hg ↦ by
        refine ENNReal.rpow_le_rpow ?_ hr0.le
        rw [← ofReal_norm, ← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ((hbound k g hg).trans (le_of_eq ?_))
        rw [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ S g from tsum_nonneg fun _ ↦ NNReal.coe_nonneg _)]))
      hfin
      ((ae_restrict_iff' hZ).mpr (Eventually.of_forall fun g hg ↦ by
        have h := (tendsto_sub_nhds_zero_iff.mpr
          (tendsto_eLpNorm_ideleThetaSum_of_dominated_pointwise φ f Z hlim htails g hg)).eNorm
        have h' := (ENNReal.continuous_rpow_const (y := r)).tendsto _ |>.comp h
        simp only [eNorm_zero, ENNReal.zero_rpow_of_pos hr0] at h'
        refine h'.congr fun k ↦ ?_
        simp only [Function.comp_apply, G, Set.indicator_of_mem hg]))
    simpa only [lintegral_zero] using hlim0
  have hpow := (ENNReal.continuous_rpow_const (y := 1 / r)).tendsto _ |>.comp hint
  rw [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hr0)] at hpow
  refine hpow.congr fun k ↦ ?_
  rw [Function.comp_apply, eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hptop
    (hGm k).aestronglyMeasurable, hpr]

/-- Paper: Remark 11.1.1.3, p. 476. The saturation of a Borel set under
the countable group of principal ideles is Borel. -/
theorem measurableSet_principalIdeleSaturation {Z : Set 𝕀[F]} (hZ : MeasurableSet Z) :
    MeasurableSet (saturation Z) := by
  have hborel : BorelSpace 𝕀[F] := ⟨rfl⟩
  have hF : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have hFu : Countable Fˣ := Units.val_injective.countable
  refine MeasurableSet.iUnion fun ξ ↦ ?_
  -- Each translate is the preimage of the set under the inverse translation.
  rw [Set.image_mul_left]
  exact (continuous_const_mul (principal ξ)⁻¹).measurable hZ

section FundamentalDomain

variable (e : (ℝ≥0ˣ × N[F]) ≃ₜ* 𝕀[F])
  (he_norm : ∀ t h, ideleNorm F (e (t, h)) = t)
  (he_one : ∀ h, e (1, h) = h.val)
  (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
  (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
  (rep : CommRing.Pic (𝓞 F) → N[F])
  (hrep₁ : rep 1 = 1) (hrep : ∀ c, ideleIdealClass F (rep c).val = c)

local notation "E₁" => ideleFundamentalDomain F b v₀ σ rep
local notation "TE₁" => e '' (Set.prod (Set.univ : Set ℝ≥0ˣ) E₁)
local notation "μ₁" => normOneIdeleTamagawaMeasure F
local notation "χ" => PontryaginDual C₁[F]

-- TODO(paper-gap): In (11.1.1.8), α_g is evaluated on ξ instead of ξg.
-- The bound on the total orbit sum alone does not imply (11.1.1.10).
-- The proof's references to (11.1.1.12) and (11.1.1.13) point to the next corollary.

/-- Paper: Corollary 11.1.1.4, p. 478. The limit theta series converges
absolutely on the fundamental domain multiplied by the norm section.
Deviation: The orbit majorant is indexed by ξ, with ξ representing ξg. -/
theorem summable_ideleThetaSum_on_fundamentalDomain
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (hlim : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hmajorant : ∀ g : 𝕀[F], ∃ (α : Fˣ → ℝ≥0) (I : Frac[F]),
      Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α ξ.val : ℝ)) ∧
      (g ∈ TE₁ → ∀ k, (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤
        ∑' ξ : {ξ : Fˣ // (ξ.val : F) ∈ I}, (α ξ.val : ℝ))) :
    ∀ g ∈ TE₁, Summable (fun ξ : Fˣ ↦ ‖f (principal ξ * g)‖) := by
  intro g hg
  refine (hmajorant g).elim fun α hα ↦ hα.elim fun I hI ↦ ?_
  exact summable_norm_orbit_of_tendsto_of_le φ f g (fun ξ ↦ hlim _) _ (hI.2 hg)

/-- The theta series of an idele function is invariant under principal translation. -/
private theorem tendsto_adelicTheta_of_dominated_invariant (f : 𝕀[F] → ℂ) (η : Fˣ)
    (g : 𝕀[F]) : ideleThetaSum f (principal η * g) = ideleThetaSum f g := by
  unfold ideleThetaSum
  simp_rw [← mul_assoc, ← map_mul]
  exact (Equiv.mulRight η).tsum_eq fun ξ ↦ f (principal ξ * g)

/-- Every idele has a principal translate in the section times the norm-one domain. -/
private theorem tendsto_adelicTheta_of_dominated_cover
    (e : (ℝ≥0ˣ × N[F]) ≃ₜ* 𝕀[F]) (he_one : ∀ h, e (1, h) = h.val)
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (rep : CommRing.Pic (𝓞 F) → N[F])
    (hrep₁ : rep 1 = 1) (hrep : ∀ c, ideleIdealClass F (rep c).val = c) (g : 𝕀[F]) :
    ∃ ξ : Fˣ, principal ξ * g ∈ e '' (Set.prod (Set.univ : Set ℝ≥0ˣ)
      (ideleFundamentalDomain F b v₀ σ rep)) := by
  obtain ⟨⟨t, h⟩, rfl⟩ := e.surjective g
  have hcov := ideleFundamentalDomain_cover F b v₀ σ rep hrep₁ hrep
  obtain ⟨x, hx⟩ := Set.mem_iUnion.mp (hcov ▸ Set.mem_univ h)
  obtain ⟨y, hy, hyh⟩ := Set.mem_smul_set.mp hx
  have key : ∀ u y : N[F], e (t, u • y) = u.val * e (t, y) := fun u y ↦ by
    rw [← he_one u, ← map_mul, Prod.mk_mul_mk, one_mul, smul_eq_mul]
  refine ⟨x⁻¹, (t, y), ⟨Set.mem_univ _, hy⟩, ?_⟩
  rw [← hyh, key, map_inv]
  exact (inv_mul_cancel_left _ _).symm

include he_norm he_one hrep₁ hrep in
/-- Paper: Corollary 11.1.1.4, p. 478. The approximating theta functions
converge pointwise on the idele class group to the theta series of the limit.
Deviation: The orbit majorant is indexed by ξ, with ξ representing ξg.
The orbit series have uniform tails at each point of the section times the domain. -/
theorem tendsto_adelicTheta_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (hlim : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hmajorant : ∀ g : 𝕀[F], ∃ (α : Fˣ → ℝ≥0) (I : Frac[F]),
      Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α ξ.val : ℝ)) ∧
      (g ∈ TE₁ → ∀ k, (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤
        ∑' ξ : {ξ : Fˣ // (ξ.val : F) ∈ I}, (α ξ.val : ℝ)))
    (htails : HasUniformThetaTails (fun k ↦ ideleValue (φ k)) TE₁) :
    ∃ Θ : C[F] → ℂ, (∀ g, Θ (classOf g) = ideleThetaSum f g) ∧
      ∀ c, Tendsto (fun k ↦ adelicTheta (φ k) c) atTop (𝓝 (Θ c)) := by
  -- The theta series of the limit is constant on idele classes.
  have hclass : ∀ g g' : 𝕀[F], classOf g = classOf g' →
      ideleThetaSum f g' = ideleThetaSum f g := by
    intro g g' hgg
    obtain ⟨u, ⟨ξ, rfl⟩, hu⟩ := (QuotientGroup.mk'_eq_mk' _).mp hgg
    rw [← hu, mul_comm, tendsto_adelicTheta_of_dominated_invariant]
  refine ⟨fun c ↦ ideleThetaSum f c.out, fun g ↦ hclass _ _ (QuotientGroup.out_eq' _).symm,
    fun c ↦ ?_⟩
  obtain ⟨ξ, hξ⟩ := tendsto_adelicTheta_of_dominated_cover e he_one v₀ σ b rep hrep₁ hrep c.out
  have hc : classOf (principal ξ * c.out) = c := by
    refine ((QuotientGroup.mk'_eq_mk' _).mpr ⟨(principal ξ)⁻¹,
      (IdeleGroup.principalSubgroup (𝓞 F) F).inv_mem ⟨ξ, rfl⟩, ?_⟩).trans
      (QuotientGroup.out_eq' c)
    rw [mul_comm (principal ξ), mul_assoc, mul_inv_cancel, mul_one]
  have hconv : Tendsto (fun k ↦ adelicTheta (φ k) (classOf (principal ξ * c.out))) atTop
      (𝓝 (ideleThetaSum f (principal ξ * c.out))) :=
    (tendsto_eLpNorm_ideleThetaSum_of_dominated_tsum
      (fun k ξ' ↦ ideleValue (φ k) (principal ξ' * (principal ξ * c.out)))
      (fun ξ' ↦ f (principal ξ' * (principal ξ * c.out))) (fun ξ' ↦ hlim _)
      (htails _ hξ)).congr fun k ↦ ideleThetaSum_schwartzBruhat (φ k) _
  rw [hc, tendsto_adelicTheta_of_dominated_invariant] at hconv
  exact hconv

-- TODO(paper-gap): Relative compactness and nonempty interior do not show
-- that T ⋅ E₁ is Borel. Use the Borel property of E₁ and the splitting.
-- The citation to part (1) of Lemma A.2.2.9 has no such numbered part.
/-- Paper: Discussion preceding Corollary 11.1.1.5, p. 478. The section
times the idelic fundamental domain is Borel. -/
theorem measurableSet_normSection_fundamentalDomain : MeasurableSet TE₁ := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  change MeasurableSet (e.toEquiv '' ((univ : Set ℝ≥0ˣ) ×ˢ E₁))
  rw [e.toEquiv.image_eq_preimage_symm, univ_prod]
  exact (measurableSet_ideleFundamentalDomain F v₀ σ b rep).preimage
    (continuous_snd.comp e.symm.continuous).measurable

local notation "classOfNormOne" => fun h : N[F] ↦
  (Subtype.mk (classOf (Subtype.val h)) (Subtype.property h) : C₁[F])
local notation "weightedTheta" => fun (ω : χ) (u : 𝕀[F] → ℂ) (g : 𝕀[F]) (h : N[F]) ↦
  ideleThetaSum u (g * Subtype.val h) *
    (ω (classOfNormOne (Prod.snd (ContinuousMulEquiv.symm e (g * Subtype.val h)))) : ℂ)

/-- Paper: Equation (11.1.1.12), p. 479. The homogeneous theta average
integrates the theta series against the character evaluated at the product
of the input idele and the variable of integration.
Deviation: The character of the norm-one classes is extended trivially
on the chosen norm section. On Schwartz–Bruhat inputs this weights the
Chapter 2 homogeneous theta by the character of the input's norm-one component. -/
def homogeneousThetaSectionAverage (ω : χ) (f : 𝕀[F] → ℂ) (g : 𝕀[F]) : ℂ :=
  ∫ h in E₁, weightedTheta ω f g h ∂μ₁

open scoped Pointwise in
include hrep₁ hrep in
/-- The norm-one domain is Borel and is a fundamental domain for the principal ideles. -/
private theorem homogeneousThetaSectionAverage_fundamentalDomain
    (i : Fˣ →* N[F]) (hi : ∀ ξ, (i ξ).val = principal ξ) :
    MeasurableSet E₁ ∧ IsFundamentalDomain i.range E₁ μ₁ := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : (μ₁).IsHaarMeasure := (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let U := (InfiniteAdeleRing F)ˣ
  let K := (infiniteIdeleNorm F).ker
  let : MeasurableSpace U := borel _
  let : BorelSpace U := ⟨rfl⟩
  let D := infiniteIdeleFundamentalDomain F b v₀ σ
  have hD : MeasurableSet D := by
    let L (g : K) : Units.dirichletUnitTheorem.logSpace F := fun w ↦ infiniteIdeleLog F g.val w.val
    have hL : Continuous L := continuous_pi fun w ↦
      (continuous_apply w.val).comp ((infiniteIdeleLog_continuous F).comp continuous_subtype_val)
    let z (g : K) := InfinitePlace.Completion.extensionEmbedding v₀ (g.val.val v₀)
    have hz : Continuous z := (InfinitePlace.Completion.isometry_extensionEmbedding v₀).continuous.comp
      ((continuous_apply v₀).comp (Units.continuous_val.comp continuous_subtype_val))
    exact ((ZSpan.fundamentalDomain_measurableSet _).preimage hL.measurable).inter
      (measurableSet_Ico.preimage
        (Complex.measurable_arg.comp (σ.toLinearMap.continuous_of_finiteDimensional.comp hz).measurable))
  have himg : MeasurableSet (K.subtype '' D) :=
    (infiniteIdeleNorm_ker_closed F).isClosedEmbedding_subtypeVal.measurableEmbedding.measurableSet_image' hD
  have hE : MeasurableSet E₁ := by
    obtain ⟨_, _, _, _, _, hFinite, ⟨ePic⟩⟩ := ideleClassGroup_finiteness F
    have : Finite (CommRing.Pic (𝓞 F)) := @Finite.of_equiv _ _ hFinite ePic.toEquiv
    apply MeasurableSet.iUnion
    intro c
    apply MeasurableSet.const_smul
    let j := Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom
    let q := Units.map (RingHom.fst (InfiniteAdeleRing F) (IsDedekindDomain.FiniteAdeleRing (𝓞 F) F)).toMonoidHom
    have hfin : MeasurableSet ((Subtype.val : N[F] → 𝕀[F]) ⁻¹' Set.range j) :=
      ((isOpenEmbedding_integralAdeleUnits F ∅).isOpen_range.preimage continuous_subtype_val).measurableSet
    have harch : MeasurableSet ((fun g : N[F] ↦ q g.val) ⁻¹' (K.subtype '' D)) :=
      himg.preimage ((continuous_fst.units_map _).comp continuous_subtype_val).measurable
    exact hfin.inter harch
  let j := (IdeleGroup.unitEmbedding (𝓞 F) F).codRestrict (ideleNorm F).ker
    (fun ξ ↦ (ideleNorm_spec F).2 (mem_range_self ξ))
  have hji (ξ : Fˣ) : j ξ = i ξ := Subtype.ext (hi ξ).symm
  refine ⟨hE, IsFundamentalDomain.mk'' hE.nullMeasurableSet ?_ ?_ ?_⟩
  · refine .of_forall fun x ↦ ?_
    have hx : x ∈ ⋃ ξ : Fˣ, j ξ • E₁ :=
      (ideleFundamentalDomain_cover F b v₀ σ rep hrep₁ hrep).symm ▸ mem_univ _
    obtain ⟨ξ, y, hy, hxy⟩ := mem_iUnion.mp hx
    refine ⟨(i.rangeRestrict ξ)⁻¹, ?_⟩
    change (i ξ)⁻¹ * x ∈ E₁
    change j ξ * y = x at hxy
    rwa [← hxy, hji, inv_mul_cancel_left]
  · intro a ha
    obtain ⟨ξ, rfl⟩ := i.rangeRestrict_surjective a
    have hξ : ξ ≠ 1 := fun h ↦ ha (h ▸ map_one i.rangeRestrict)
    change AEDisjoint μ₁ (i ξ • E₁) E₁
    rw [← hji]
    exact (ideleFundamentalDomain_disjoint F b v₀ σ rep hrep₁ hrep ξ hξ).aedisjoint
  · exact fun a ↦ (measurePreserving_mul_left μ₁ a.val).quasiMeasurePreserving

include he_one hrep₁ hrep in
/-- Paper: Equation (11.1.1.12), p. 479. For each Schwartz–Bruhat input,
the section average is the character of the norm-one component times the
Chapter 2 homogeneous adelic theta.
Deviation: Equation (2.2.5.2) weights the integration variable by its
character. Equation (11.1.1.12) also includes the character of the input. -/
theorem homogeneousThetaSectionAverage_schwartzBruhat_eq_character_mul (ω : χ)
    (ψ : ℬ[F]) (g : 𝕀[F]) :
    homogeneousThetaSectionAverage e v₀ σ b rep ω (ideleValue ψ) g =
      (ω (classOfNormOne (e.symm g).2) : ℂ) *
        homogeneousAdelicTheta ω ψ (classOf g) := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  let : (μ₁).IsHaarMeasure := (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  obtain ⟨i, p, hi, hp, hiinj, -, -, hex, -, -⟩ := normOne_idele_quotient F
  let ie : Fˣ ≃* i.range := MulEquiv.ofBijective i.rangeRestrict
    ⟨fun _ _ h ↦ hiinj (congrArg Subtype.val h), i.rangeRestrict_surjective⟩
  let : Countable i.range := i.rangeRestrict_surjective.countable
  have hD := (homogeneousThetaSectionAverage_fundamentalDomain v₀ σ b rep hrep₁ hrep i hi).2
  let Φ (h : N[F]) := ideleValue ψ (h.val * g) * (ω (classOfNormOne h) : ℂ)
  have hΦ : Integrable Φ μ₁ := homogeneousAdelicTheta_idele_integrable ω ψ g
  have hsplit (h : N[F]) : (e.symm (g * h.val)).2 = (e.symm g).2 * h := by
    rw [← he_one h, map_mul, e.symm_apply_apply]
    rfl
  let c : ℂ := ω (classOfNormOne (e.symm g).2)
  have hperiod (h : N[F]) : weightedTheta ω (ideleValue ψ) g h = c * ∑' a : i.range, Φ (a • h) := by
    have hclass (ξ : Fˣ) : classOfNormOne (i ξ * h) = classOfNormOne h := by
      have hp' (x : N[F]) : p x = classOfNormOne x := Subtype.ext (hp x)
      rw [← hp', ← hp', map_mul, (hex (i ξ)).mpr ⟨ξ, rfl⟩, one_mul]
    have hterm (ξ : Fˣ) : Φ (ie ξ • h) =
        ideleValue ψ (principal ξ * (g * h.val)) * (ω (classOfNormOne h) : ℂ) := by
      change ideleValue ψ (((i ξ * h).val) * g) * (ω (classOfNormOne (i ξ * h)) : ℂ) = _
      rw [hclass, Subgroup.coe_mul, hi, mul_assoc, mul_comm h.val g]
    have hsum : (∑' a : i.range, Φ (a • h)) =
        ideleThetaSum (ideleValue ψ) (g * h.val) * (ω (classOfNormOne h) : ℂ) := calc
      _ = ∑' ξ : Fˣ, Φ (ie ξ • h) := (ie.toEquiv.tsum_eq (fun a : i.range ↦ Φ (a • h))).symm
      _ = ∑' ξ : Fˣ, ideleValue ψ (principal ξ * (g * h.val)) * (ω (classOfNormOne h) : ℂ) :=
        tsum_congr hterm
      _ = _ := tsum_mul_right
    have hchar := congrArg (fun x : N[F] ↦ (ω (classOfNormOne x) : ℂ)) (hsplit h)
    change _ * (ω (classOfNormOne (e.symm (g * h.val)).2) : ℂ) = c * _
    rw [hchar, hsum]
    change _ * (ω (classOfNormOne (e.symm g).2 * classOfNormOne h) : ℂ) = _
    simp only [map_mul, Circle.coe_mul]
    exact mul_left_comm _ _ _
  have hfold : (∫ h in E₁, ∑' a : i.range, Φ (a • h) ∂μ₁) = ∫ h, Φ h ∂μ₁ := by
    rw [hD.integral_eq_tsum'' Φ hΦ]
    apply integral_tsum
    · exact fun a ↦ (hΦ.1.comp_quasiMeasurePreserving
      (measurePreserving_mul_left μ₁ a.val).quasiMeasurePreserving).restrict
    · rw [← hD.lintegral_eq_tsum'' (‖Φ ·‖ₑ)]
      exact hΦ.2.ne
  calc
    _ = ∫ h in E₁, c * ∑' a : i.range, Φ (a • h) ∂μ₁ := integral_congr_ae (.of_forall hperiod)
    _ = c * (∫ h in E₁, ∑' a : i.range, Φ (a • h) ∂μ₁) := integral_const_mul _ _
    _ = c * (∫ h, Φ h ∂μ₁) := congrArg (c * ·) hfold
    _ = _ := congrArg (c * ·) (homogeneousAdelicTheta_eq_idele_integral ω ψ g).symm

include he_one hrep₁ hrep in
/-- Paper: Equation (11.1.1.12), p. 479. At an idele on the norm section,
the integral of a Schwartz–Bruhat theta series agrees with homogeneous
adelic theta from Chapter 2.
Deviation: The character is extended trivially on the norm section. -/
theorem homogeneousThetaSectionAverage_schwartzBruhat (ω : χ)
    (ψ : ℬ[F]) (t : ℝ≥0ˣ) :
    homogeneousThetaSectionAverage e v₀ σ b rep ω (ideleValue ψ) (e (t, 1)) =
      homogeneousAdelicTheta ω ψ (classOf (e (t, 1))) := by
  have h := homogeneousThetaSectionAverage_schwartzBruhat_eq_character_mul
    e he_one v₀ σ b rep hrep₁ hrep ω ψ (e (t, 1))
  rw [e.symm_apply_apply] at h
  change _ = (ω (1 : C₁[F]) : ℂ) * _ at h
  simpa using h

-- TODO(paper-gap): The claimed interchange of the limit and orbit sum
-- in the proof of (11.1.1.13) needs control of the orbit tails.

include he_one in
/-- Multiplying by a norm-one idele leaves the norm coordinate fixed. -/
private theorem integrable_homogeneousThetaSectionAverage_of_dominated_section_mul
    (t : ℝ≥0ˣ) (h : N[F]) : e (t, 1) * h.val = e (t, h) := by
  rw [← he_one h, ← map_mul]
  change e (t * 1, 1 * h) = e (t, h)
  rw [mul_one, one_mul]

/-- The pulled-back character on the norm-one ideles is continuous. -/
private theorem integrable_homogeneousThetaSectionAverage_of_dominated_character_continuous
    (ω : χ) : Continuous (fun h : N[F] ↦ (ω (classOfNormOne h) : ℂ)) := by
  have hq : Continuous (fun h : N[F] ↦ classOfNormOne h) := by
    apply Continuous.subtype_mk
    exact QuotientGroup.continuous_mk.comp continuous_subtype_val
  exact continuous_subtype_val.comp (ω.continuous.comp hq)

include he_one in
/-- Principal translations preserve the theta series and its character factor. -/
private theorem integrable_homogeneousThetaSectionAverage_of_dominated_invariant
    (i : Fˣ →* N[F]) (hi : ∀ ξ, (i ξ).val = principal ξ)
    (ω : χ) (f : 𝕀[F] → ℂ) (g : 𝕀[F]) (a : i.range) (h : N[F]) :
    weightedTheta ω f g (a • h) = weightedTheta ω f g h := by
  obtain ⟨ξ, rfl⟩ := i.rangeRestrict_surjective a
  have hξ : classOfNormOne (i ξ) = 1 := by
    apply Subtype.ext
    change classOf (i ξ).val = 1
    rw [hi]
    exact (QuotientGroup.eq_one_iff _).mpr (mem_range_self ξ)
  have hmul : g * (i ξ * h).val = principal ξ * (g * h.val) := by
    rw [Subgroup.coe_mul, hi, mul_left_comm]
  have hsplit : (e.symm (principal ξ * (g * h.val))).2 = i ξ * (e.symm (g * h.val)).2 := by
    rw [← hi ξ, ← he_one (i ξ), map_mul, e.symm_apply_apply]
    rfl
  have hθ : ideleThetaSum f (principal ξ * (g * h.val)) = ideleThetaSum f (g * h.val) := by
    calc
      _ = ∑' ζ : Fˣ, f (principal (ζ * ξ) * (g * h.val)) :=
        tsum_congr fun ζ ↦ congrArg f (by rw [map_mul, mul_assoc])
      _ = _ := (Equiv.mulRight ξ).tsum_eq (fun ζ : Fˣ ↦ f (principal ζ * (g * h.val)))
  let W (x : 𝕀[F]) := ideleThetaSum f x * (ω (classOfNormOne (e.symm x).2) : ℂ)
  change W (g * (i ξ * h).val) = W (g * h.val)
  refine (congrArg W hmul).trans ?_
  have hchar := congrArg (fun x : N[F] ↦ (ω (classOfNormOne x) : ℂ)) hsplit
  change ideleThetaSum f (principal ξ * (g * h.val)) * _ = _
  rw [hθ, hchar]
  change _ * (ω (classOfNormOne (i ξ) * classOfNormOne (e.symm (g * h.val)).2) : ℂ) = _
  rw [hξ, one_mul]

include he_one in
/-- Restricting an input to the norm section translates the variable of integration. -/
private theorem integrable_homogeneousThetaSectionAverage_of_dominated_recenter
    (ω : χ) (f : 𝕀[F] → ℂ) (g : 𝕀[F]) :
    weightedTheta ω f g = weightedTheta ω f (e ((e.symm g).1, 1)) ∘ ((e.symm g).2 * ·) := by
  have hg : e ((e.symm g).1, 1) * (e.symm g).2.val = g :=
    (integrable_homogeneousThetaSectionAverage_of_dominated_section_mul e he_one
      (e.symm g).1 (e.symm g).2).trans (e.apply_symm_apply g)
  funext h
  simp only [Function.comp_apply, Subgroup.coe_mul, ← mul_assoc, hg]

open scoped Pointwise in
include he_norm he_one hrep₁ hrep in
/-- Paper: Corollary 11.1.1.5, p. 479. The character-weighted theta
integrand is integrable over the norm-one domain for every idele.
Deviation: The character is extended trivially on the norm section.
Slice integrability of the majorant is written by pulling it back to the domain. -/
theorem integrable_homogeneousThetaSectionAverage_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (hlim : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
      Measurable α ∧
      (∀ g : 𝕀[F], Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α (principal ξ.val * g) : ℝ))) ∧
      Measurable (fractionalIdealOrbitSum I α) ∧
      (∀ t, Integrable (fun h : N[F] ↦ fractionalIdealOrbitSum I α (e (t, h)))
        ((μ₁).restrict E₁)) ∧
      ∀ g : 𝕀[F], g ∈ TE₁ → ∀ k,
        (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g) :
    ∀ (ω : χ) (g : 𝕀[F]), Integrable (weightedTheta ω f g) ((μ₁).restrict E₁) := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  let : (μ₁).IsHaarMeasure := (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  obtain ⟨i, _, hi, _, _, _, _, _, _, _⟩ := normOne_idele_quotient F
  let : Countable i.range := i.rangeRestrict_surjective.countable
  obtain ⟨hE, hD⟩ := homogeneousThetaSectionAverage_fundamentalDomain v₀ σ b rep hrep₁ hrep i hi
  obtain ⟨α, I, -, -, -, hInt, hbound⟩ := hmajorant
  intro ω g
  let t := (e.symm g).1
  let k := (e.symm g).2
  let P := weightedTheta ω f (e (t, 1))
  have hP (h : N[F]) : P h = ideleThetaSum f (e (t, h)) * (ω (classOfNormOne h) : ℂ) := by
    simp only [P, integrable_homogeneousThetaSectionAverage_of_dominated_section_mul e he_one,
      e.symm_apply_apply]
  have hslice (h : N[F]) (hh : h ∈ E₁) : e (t, h) ∈ TE₁ :=
    ⟨(t, h), ⟨mem_univ _, hh⟩, rfl⟩
  have hsums (h : N[F]) (hh : h ∈ E₁) :
      Summable (fun ξ : Fˣ ↦ ‖f (principal ξ * e (t, h))‖) :=
    summable_norm_orbit_of_tendsto_of_le φ f (e (t, h)) (fun _ ↦ hlim _) _
      (hbound _ (hslice h hh))
  have hTheta : AEStronglyMeasurable (fun h : N[F] ↦ ideleThetaSum f (e (t, h)))
      ((μ₁).restrict E₁) := by
    have hf := measurable_ideleLimit φ f hlim
    have he : Continuous (fun h : N[F] ↦ e (t, h)) :=
      e.continuous.comp (Continuous.prodMk_right t)
    refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset Fˣ))
      (f := fun s h ↦ ∑ ξ ∈ s, f (principal ξ * e (t, h))) ?_ ?_
    · exact fun s ↦ (Finset.measurable_sum s fun ξ _ ↦
        hf.comp ((continuous_const_mul (principal ξ)).comp he).measurable).aestronglyMeasurable
    · exact (ae_restrict_iff' hE).mpr (.of_forall fun h hh ↦ (hsums h hh).of_norm.hasSum)
  have hPint : IntegrableOn P E₁ μ₁ := by
    refine (hInt t).mono' ?_ ((ae_restrict_iff' hE).mpr (.of_forall fun h hh ↦ ?_))
    · have hχ := integrable_homogeneousThetaSectionAverage_of_dominated_character_continuous ω
      exact (hTheta.mul hχ.aestronglyMeasurable).congr (.of_forall fun h ↦ (hP h).symm)
    · rw [hP, norm_mul, Circle.norm_coe, mul_one]
      exact (norm_tsum_le_tsum_norm (hsums h hh)).trans
        (Real.tsum_le_of_sum_le (fun _ ↦ norm_nonneg _)
          (sum_norm_orbit_le_of_tendsto_of_le φ f (e (t, h)) (fun _ ↦ hlim _) _
            (hbound _ (hslice h hh))))
  have hShift : IntegrableOn P (k • E₁) μ₁ :=
    (hD.integrableOn_iff (hD.smul_of_comm k)
      (integrable_homogeneousThetaSectionAverage_of_dominated_invariant e he_one i hi ω f _)).mp hPint
  rw [integrable_homogeneousThetaSectionAverage_of_dominated_recenter e he_one]
  exact ((measurePreserving_mul_left μ₁ k).integrableOn_image
    (measurableEmbedding_const_smul k) (f := P) (s := E₁)).mp hShift

/-- Uniform tails give uniform convergence of the finite orbit sums in the sequence index,
so their limits in the sequence index converge to the orbit sum of the limit. -/
private theorem tendsto_homogeneousThetaSectionAverage_of_dominated_orbit
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ) (g : 𝕀[F])
    (hlim : ∀ ξ : Fˣ, Tendsto (fun k ↦ ideleValue (φ k) (principal ξ * g)) atTop
      (𝓝 (f (principal ξ * g))))
    (hsum : Summable (fun ξ : Fˣ ↦ ‖f (principal ξ * g)‖))
    (htails : ∀ ε : ℝ≥0∞, 0 < ε → ∃ s : Finset Fˣ, ∀ k,
      (∑' ξ : {ξ : Fˣ // ξ ∉ s}, ‖ideleValue (φ k) (principal ξ.val * g)‖ₑ) < ε) :
    Tendsto (fun k ↦ ideleThetaSum (ideleValue (φ k)) g) atTop (𝓝 (ideleThetaSum f g)) := by
  let a (k : ℕ) (ξ : Fˣ) := ideleValue (φ k) (principal ξ * g)
  have ha (k : ℕ) : Summable (a k) := (summable_norm_ideleValue_orbit (φ k) g).of_norm
  have hu : TendstoUniformly (fun (s : Finset Fˣ) k ↦ ∑ ξ ∈ s, a k ξ)
      (fun k ↦ ∑' ξ, a k ξ) atTop := by
    apply EMetric.tendstoUniformly_iff.mpr
    intro ε hε
    obtain ⟨s, hs⟩ := htails ε hε
    filter_upwards [eventually_ge_atTop s] with u hsu k
    change edist (∑' ξ, a k ξ) (∑ ξ ∈ u, a k ξ) < ε
    rw [eDist_eq_eNorm_sub, ← (ha k).sum_add_tsum_subtype_compl u, add_sub_cancel_left]
    have hc : {ξ : Fˣ | ξ ∉ u} ⊆ {ξ : Fˣ | ξ ∉ s} := fun _ hξ hsξ ↦ hξ (hsu hsξ)
    exact eNorm_tsum_le_tsum_eNorm.trans_lt
      ((tsum_mono_subtype (fun ξ ↦ ‖a k ξ‖ₑ) hc).trans_lt (hs k))
  exact hu.tendsto_of_eventually_tendsto
    (.of_forall fun s ↦ tendsto_finsetSum s fun ξ _ ↦ hlim ξ) hsum.of_norm.hasSum

open scoped Pointwise in
include he_one in
/-- Integration of the principal-invariant integrand depends only on the norm coordinate. -/
private theorem tendsto_homogeneousThetaSectionAverage_of_dominated_recenter
    (i : Fˣ →* N[F]) (hi : ∀ ξ, (i ξ).val = principal ξ) [Countable i.range]
    (hD : IsFundamentalDomain i.range E₁ μ₁)
    (ω : χ) (f : 𝕀[F] → ℂ) (g : 𝕀[F]) :
    homogeneousThetaSectionAverage e v₀ σ b rep ω f g =
      homogeneousThetaSectionAverage e v₀ σ b rep ω f (e ((e.symm g).1, 1)) := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : (μ₁).IsHaarMeasure := (normOneIdeleTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let k := (e.symm g).2
  let P := weightedTheta ω f (e ((e.symm g).1, 1))
  calc
    _ = ∫ h in E₁, P (k * h) ∂μ₁ :=
      congrArg (fun V : N[F] → ℂ ↦ ∫ h in E₁, V h ∂μ₁)
        (integrable_homogeneousThetaSectionAverage_of_dominated_recenter e he_one ω f g)
    _ = ∫ h in k • E₁, P h ∂μ₁ :=
      ((measurePreserving_mul_left μ₁ k).setIntegral_image_emb
        (measurableEmbedding_const_smul k) P E₁).symm
    _ = _ := (hD.smul_of_comm k).setIntegral_eq hD
      (integrable_homogeneousThetaSectionAverage_of_dominated_invariant e he_one i hi ω f _)

include he_norm he_one hrep₁ hrep in
/-- Paper: Corollary 11.1.1.5, p. 479. The limit and approximating
averages descend to the quotient by the norm-one classes and converge
pointwise there.
Deviation: The character is extended trivially on the norm section.
Slice integrability is written by pullback, and uniform orbit tails are assumed.
The functions descending to the quotient include the character factor on the input
in (11.1.1.12). The Chapter 2 approximants have inverse-character equivariance. -/
theorem tendsto_homogeneousThetaSectionAverage_of_dominated
    (φ : ℕ → ℬ[F]) (f : 𝕀[F] → ℂ)
    (hlim : ∀ g : 𝕀[F], Tendsto (fun k ↦ ideleValue (φ k) g) atTop (𝓝 (f g)))
    (hmajorant : ∃ (α : 𝕀[F] → ℝ≥0) (I : Frac[F]),
      Measurable α ∧
      (∀ g : 𝕀[F], Summable (fun ξ : {ξ : Fˣ // (ξ.val : F) ∈ I} ↦ (α (principal ξ.val * g) : ℝ))) ∧
      Measurable (fractionalIdealOrbitSum I α) ∧
      (∀ t, Integrable (fun h : N[F] ↦ fractionalIdealOrbitSum I α (e (t, h)))
        ((μ₁).restrict E₁)) ∧
      ∀ g : 𝕀[F], g ∈ TE₁ → ∀ k,
        (∑' ξ : Fˣ, ‖ideleValue (φ k) (principal ξ * g)‖) ≤ fractionalIdealOrbitSum I α g)
    (htails : HasUniformThetaTails (fun k ↦ ideleValue (φ k)) TE₁) :
    ∀ ω : χ, ∃ (A : C[F] ⧸ C₁[F] → ℂ) (Aₖ : ℕ → C[F] ⧸ C₁[F] → ℂ),
      (∀ g, A (QuotientGroup.mk' _ (classOf g)) =
        homogeneousThetaSectionAverage e v₀ σ b rep ω f g) ∧
      (∀ k g, Aₖ k (QuotientGroup.mk' _ (classOf g)) =
        (ω (classOfNormOne (e.symm g).2) : ℂ) *
          homogeneousAdelicTheta ω (φ k) (classOf g)) ∧
      ∀ q, Tendsto (fun k ↦ Aₖ k q) atTop (𝓝 (A q)) := by
  let : BorelSpace 𝕀[F] := ⟨rfl⟩
  let : Countable F := Countable.of_moduleFinite (R := ℚ)
  let : Countable Fˣ := Units.val_injective.countable
  obtain ⟨i, _, hi, _, _, _, _, _, _, _⟩ := normOne_idele_quotient F
  let : Countable i.range := i.rangeRestrict_surjective.countable
  obtain ⟨hE, hD⟩ := homogeneousThetaSectionAverage_fundamentalDomain v₀ σ b rep hrep₁ hrep i hi
  obtain ⟨α, I, -, -, -, hInt, hbound⟩ := hmajorant
  intro ω
  let S (u : 𝕀[F] → ℂ) := homogeneousThetaSectionAverage e v₀ σ b rep ω u
  let qNorm : C[F] ⧸ C₁[F] →* ℝ≥0ˣ := QuotientGroup.lift _ (ideleClassNorm F) le_rfl
  have hq (g : 𝕀[F]) : qNorm (QuotientGroup.mk' _ (classOf g)) = (e.symm g).1 := by
    change ideleNorm F g = (e.symm g).1
    calc
      ideleNorm F g = ideleNorm F (e ((e.symm g).1, (e.symm g).2)) :=
        congrArg (ideleNorm F) (e.apply_symm_apply g).symm
      _ = _ := he_norm _ _
  have hS (u : 𝕀[F] → ℂ) (g : 𝕀[F]) : S u g = S u (e ((e.symm g).1, 1)) :=
    tendsto_homogeneousThetaSectionAverage_of_dominated_recenter e he_one v₀ σ b rep i hi hD ω u g
  refine ⟨fun q ↦ S f (e (qNorm q, 1)), fun k q ↦ S (ideleValue (φ k)) (e (qNorm q, 1)),
    fun g ↦ ?_, fun k g ↦ ?_, fun q ↦ ?_⟩
  · exact (congrArg (fun t ↦ S f (e (t, 1))) (hq g)).trans (hS f g).symm
  · calc
      _ = S (ideleValue (φ k)) (e ((e.symm g).1, 1)) :=
        congrArg (fun t ↦ S (ideleValue (φ k)) (e (t, 1))) (hq g)
      _ = S (ideleValue (φ k)) g := (hS _ g).symm
      _ = _ := homogeneousThetaSectionAverage_schwartzBruhat_eq_character_mul
        e he_one v₀ σ b rep hrep₁ hrep ω (φ k) g
  · let t := qNorm q
    let W (u : 𝕀[F] → ℂ) (h : N[F]) :=
      ideleThetaSum u (e (t, h)) * (ω (classOfNormOne h) : ℂ)
    have hW (u : 𝕀[F] → ℂ) : S u (e (t, 1)) = ∫ h in E₁, W u h ∂μ₁ := by
      simp only [S, homogeneousThetaSectionAverage, W,
        integrable_homogeneousThetaSectionAverage_of_dominated_section_mul e he_one,
        e.symm_apply_apply]
    have hslice (h : N[F]) (hh : h ∈ E₁) : e (t, h) ∈ TE₁ :=
      ⟨(t, h), ⟨mem_univ _, hh⟩, rfl⟩
    have hconv : Tendsto (fun k ↦ ∫ h in E₁, W (ideleValue (φ k)) h ∂μ₁) atTop
        (𝓝 (∫ h in E₁, W f h ∂μ₁)) := by
      refine tendsto_integral_of_dominated_convergence
        (fun h : N[F] ↦ fractionalIdealOrbitSum I α (e (t, h))) ?_ (hInt t) ?_ ?_
      · intro k
        have he : Continuous (fun h : N[F] ↦ e (t, h)) :=
          e.continuous.comp (Continuous.prodMk_right t)
        have hχ := integrable_homogeneousThetaSectionAverage_of_dominated_character_continuous ω
        have hc := ((adelicTheta (φ k)).continuous.comp (QuotientGroup.continuous_mk.comp he)).mul hχ
        exact hc.aestronglyMeasurable.congr (.of_forall fun h ↦
          congrArg (fun z : ℂ ↦ z * (ω (classOfNormOne h) : ℂ))
            (ideleThetaSum_schwartzBruhat (φ k) (e (t, h))).symm)
      · intro k
        refine (ae_restrict_iff' hE).mpr (.of_forall fun h hh ↦ ?_)
        calc
          ‖W (ideleValue (φ k)) h‖ = ‖ideleThetaSum (ideleValue (φ k)) (e (t, h))‖ := by
            change ‖ideleThetaSum (ideleValue (φ k)) (e (t, h)) * (ω (classOfNormOne h) : ℂ)‖ = _
            rw [norm_mul, Circle.norm_coe, mul_one]
          _ ≤ _ := (norm_tsum_le_tsum_norm (summable_norm_ideleValue_orbit (φ k) (e (t, h)))).trans
            (hbound _ (hslice h hh) k)
      · refine (ae_restrict_iff' hE).mpr (.of_forall fun h hh ↦ ?_)
        have hsum := summable_norm_orbit_of_tendsto_of_le φ f (e (t, h)) (fun _ ↦ hlim _) _
          (hbound _ (hslice h hh))
        exact (tendsto_homogeneousThetaSectionAverage_of_dominated_orbit φ f (e (t, h))
          (fun _ ↦ hlim _) hsum (htails _ (hslice h hh))).mul
          (tendsto_const_nhds (x := (ω (classOfNormOne h) : ℂ)))
    change Tendsto (fun k ↦ S (ideleValue (φ k)) (e (t, 1))) atTop (𝓝 (S f (e (t, 1))))
    rw [hW f]
    exact hconv.congr' (.of_forall fun k ↦ (hW (ideleValue (φ k))).symm)

end FundamentalDomain

end RiemannMasullo
