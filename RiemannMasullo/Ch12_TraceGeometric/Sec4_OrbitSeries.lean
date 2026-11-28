module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch12_TraceGeometric.Sec4

/-! # Descent of the additive cutoff orbit series -/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "A" => SAdeleRing F S
local notation "I" => (SAdeleRing F S)ˣ
local notation "G" => AdeleRing (𝓞 F) F
local notation "ν" => sAdditiveTamagawaMeasure F S

attribute [local instance] instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1

local instance instSIdeleT2OrbitSeries : T2Space I := (sIdeleGroup_description F S).2.1

/-- A norm-one S-idele preserves additive Tamagawa measure. Extend it by one
outside S and transfer the global change of variables through the integral-tail projection. -/
private theorem sLocalKernel_measurePreserving_normOne (u : I) (hu : sIdeleNorm F S u = 1) :
    MeasurePreserving (fun z : A ↦ u.val * z) ν ν := by
  let : BorelSpace A := sAdeleRing_borelSpace (F := F) (S := S)
  let : MeasurableSpace G := borel _
  let : BorelSpace G := ⟨rfl⟩
  let μ := additiveTamagawaMeasure F
  let : μ.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let g := sIdeleInsertion F S u
  have hgn : ideleNorm F g = 1 := (ideleNorm_sIdeleInsertion F S u).trans hu
  have hg : MeasurePreserving (fun a : G ↦ g.val * a) μ μ := by
    have hm : Measurable (fun a : G ↦ g.val * a) :=
      (continuous_const.mul continuous_id).measurable
    refine ⟨hm, ?_⟩
    ext B hB
    have hpre : (fun a : G ↦ g.val * a) ⁻¹' B = (fun a : G ↦ g⁻¹.val * a) '' B := by
      ext a
      constructor
      · intro ha
        exact ⟨g.val * a, ha, Units.inv_mul_cancel_left g a⟩
      · rintro ⟨b, hb, rfl⟩
        change g.val * (g⁻¹.val * b) ∈ B
        simpa only [Units.mul_inv_cancel_left] using hb
    rw [Measure.map_apply hm hB, hpre, adeleHaar_mul_image F μ g⁻¹ B hB]
    simp [map_inv, hgn]
  let U : Set G := integralAdelesOutside F S
  have hi := sIdeleInsertion_apply F S u
  have hpre : (fun a : G ↦ g.val * a) ⁻¹' U = U := by
    ext a
    change g.val * a ∈ integralAdelesOutside F S ↔ a ∈ integralAdelesOutside F S
    simp only [integralAdelesOutside, Subring.mem_iInf, Subring.mem_comap]
    change (∀ v, v ∉ S → g.val.2 v * a.2 v ∈ v.adicCompletionIntegers F) ↔
      ∀ v, v ∉ S → a.2 v ∈ v.adicCompletionIntegers F
    constructor <;> intro h v hv <;> simpa only [g, hi.2.2 v hv, one_mul] using h v hv
  have hgU := hg.restrict_preimage_emb (measurableEmbedding_const_smul g) U
  rw [hpre] at hgU
  obtain ⟨c, hc, _, hp, _⟩ := sAdeleProjection_dual_masses F S
  have hproj : adeleProjection F S g.val = u.val := by
    apply Prod.ext
    · exact hi.1
    · funext v
      exact hi.2.1 v
  have hcomm : Semiconj (adeleProjection F S) (fun a : G ↦ g.val * a)
      (fun z : A ↦ u.val * z) := by
    intro a
    rw [map_mul, hproj]
  have hs := hp.of_semiconj hgU hcomm (continuous_const.mul continuous_id).measurable
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hs.smul_measure c⁻¹

/-- Paper: Theorem 12.4.1.1, Step II, pp. 516–517.
The additive cutoff kernel is invariant under simultaneous norm-one dilation in
its two variables whenever both cutoff symbols are invariant under that dilation. -/
theorem sLocalTraceCutoffKernel_covariant_of_normOne
    (f : BruhatCompactSupport I) (ρ : I → ℂ) (σ : A → ℂ)
    (u : I) (hu : sIdeleNorm F S u = 1)
    (hρ : ∀ x, ρ (u * x) = ρ x) (hσ : ∀ z, σ (u.val * z) = σ z)
    (x : I) (y : A) :
    sLocalTraceCutoffKernel f ρ σ (u * x) (u.val * y) =
      sLocalTraceCutoffKernel f ρ σ x y := by
  let : BorelSpace A := sAdeleRing_borelSpace (F := F) (S := S)
  have huinv : sIdeleNorm F S u⁻¹ = 1 := by rw [map_inv, hu, inv_one]
  have hσinv (v : A) : σ (u⁻¹.val * v) = σ v := by
    simpa only [Units.mul_inv_cancel_left] using (hσ (u⁻¹.val * v)).symm
  let g (v : A) : ℂ := σ v * sLocalTraceDilationKernel f
    (fun z ↦ (sAdeleStandardCharacter F S ((z - u.val * y) * v) : ℂ)) (u * x).val
  have hchange : (∫ v, g (u⁻¹.val * v) ∂ν) = ∫ v, g v ∂ν :=
    (sLocalKernel_measurePreserving_normOne u⁻¹ huinv).integral_comp
      (measurableEmbedding_const_smul u⁻¹) g
  unfold sLocalTraceCutoffKernel
  rw [hρ x]
  apply congrArg (ρ x * ·)
  change (∫ v, g v ∂ν) = _
  rw [← hchange]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun v ↦ ?_
  dsimp only [g]
  rw [hσinv v]
  apply congrArg (σ v * ·)
  unfold sLocalTraceDilationKernel
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun a ↦ ?_
  rw [Units.val_mul]
  have hphase : ((a⁻¹.val * (u.val * x.val) - u.val * y) * (u⁻¹.val * v)) =
      (a⁻¹.val * x.val - y) * v := by
    calc
      _ = ((a⁻¹.val * x.val - y) * v) * (u.val * u⁻¹.val) := by ring
      _ = _ := by rw [Units.mul_inv, mul_one]
  exact congrArg
    (fun z : A ↦ f.val a / (Real.sqrt (((sIdeleNorm F S a).val : ℝ)) : ℂ) *
      (sAdeleStandardCharacter F S z : ℂ)) hphase

/-- In particular, the additive cutoff kernel is covariant under a projected diagonal
S-unit whenever both cutoff symbols are invariant under it. -/
private theorem sLocalTraceCutoffKernel_covariant_of_projectedUnit
    (f : BruhatCompactSupport I) (ρ : I → ℂ) (σ : A → ℂ)
    (ξ : sProjectedDiagonal F S)
    (hρ : ∀ x, ρ (ξ.val * x) = ρ x) (hσ : ∀ z, σ (ξ.val.val * z) = σ z)
    (x : I) (y : A) :
    sLocalTraceCutoffKernel f ρ σ (ξ.val * x) (ξ.val.val * y) =
      sLocalTraceCutoffKernel f ρ σ x y := by
  apply sLocalTraceCutoffKernel_covariant_of_normOne f ρ σ ξ.val _ hρ hσ x y
  obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ξ.property
  exact he ▸ (sIdeleNorm_spec F S).2 hγ


local notation "H" => sProjectedDiagonal F S
local notation "J" => SIdeleQuotient F S

/-- Simultaneous S-unit covariance makes the orbit series of the additive cutoff kernel
independent of each quotient representative. The formula uses Lean's `tsum`, which is
zero on an unsummable family. Interpreting it as an absolutely convergent orbit sum
requires a separate summability estimate on the norms. -/
private theorem exists_sLocalTraceOrbitKernel_of_covariance
    (f : BruhatCompactSupport I) (ρ : I → ℂ) (σ : A → ℂ)
    (hcov : ∀ (η : H) (x : I) (y : A),
      sLocalTraceCutoffKernel f ρ σ (η.val * x) (η.val.val * y) =
        sLocalTraceCutoffKernel f ρ σ x y) :
    ∃ κ : J → J → ℂ, ∀ x y : I,
      κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f ρ σ x (ξ.val * y).val := by
  let K := sLocalTraceCutoffKernel f ρ σ
  let P (x y : I) := ∑' ξ : H, K x (ξ.val * y).val
  have hright (η : H) (x y : I) : P x (η.val * y) = P x y := by
    calc
      _ = ∑' ξ : H, K x ((Equiv.mulRight η ξ).val * y).val := by
        apply tsum_congr
        intro ξ
        change K x (ξ.val * (η.val * y)).val = K x ((ξ.val * η.val) * y).val
        rw [mul_assoc]
      _ = _ := (Equiv.mulRight η).tsum_eq (fun ξ : H ↦ K x (ξ.val * y).val)
  have hleft (η : H) (x y : I) : P (η.val * x) y = P x y := by
    calc
      _ = ∑' ξ : H, K x ((Equiv.mulLeft η⁻¹ ξ).val * y).val := by
        apply tsum_congr
        intro ξ
        let z := (η⁻¹ * ξ).val * y
        have hz : η.val * z = ξ.val * y := by
          change η.val * ((η.val⁻¹ * ξ.val) * y) = ξ.val * y
          simp only [mul_assoc, mul_inv_cancel_left]
        have h := hcov η x z.val
        rw [← Units.val_mul, hz] at h
        exact h
      _ = _ := (Equiv.mulLeft η⁻¹).tsum_eq (fun ξ : H ↦ K x (ξ.val * y).val)
  have hcoset {a b : I} (h : (QuotientGroup.mk a : J) = QuotientGroup.mk b) :
      ∃ η : H, η.val * a = b := by
    refine ⟨⟨a⁻¹ * b, QuotientGroup.eq.mp h⟩, ?_⟩
    change (a⁻¹ * b) * a = b
    rw [mul_comm (a⁻¹ * b) a, mul_inv_cancel_left]
  have hrel (x y x' y' : I) (hx : (QuotientGroup.mk x : J) = QuotientGroup.mk x')
      (hy : (QuotientGroup.mk y : J) = QuotientGroup.mk y') : P x y = P x' y' := by
    obtain ⟨η, rfl⟩ := hcoset hx
    obtain ⟨ζ, rfl⟩ := hcoset hy
    exact ((hleft η x (ζ.val * y)).trans (hright ζ x y)).symm
  let κ (a b : J) := Quotient.liftOn₂' a b P
    (fun x y x' y' hx hy ↦ hrel x y x' y' (Quotient.sound hx) (Quotient.sound hy))
  exact ⟨κ, fun _ _ ↦ rfl⟩

/-- Paper: Theorem 12.4.1.1, Step III, p. 517.
The orbit series of the additive cutoff kernel depends only on the two
idèle classes when the cutoff symbols are invariant under diagonal S-units.
Deviation: The statement gives a quotient function. Interpreting the series as
an absolutely convergent orbit sum requires a further summability estimate. -/
theorem exists_sLocalTraceOrbitSeries
    (f : BruhatCompactSupport I) (ρ : I → ℂ) (σ : A → ℂ)
    (hρ : ∀ (η : H) x, ρ (η.val * x) = ρ x)
    (hσ : ∀ (η : H) z, σ (η.val.val * z) = σ z) :
    ∃ κ : J → J → ℂ, ∀ x y : I,
      κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f ρ σ x (ξ.val * y).val :=
  exists_sLocalTraceOrbitKernel_of_covariance f ρ σ fun η x y ↦
    sLocalTraceCutoffKernel_covariant_of_projectedUnit f ρ σ η (hρ η) (hσ η) x y

end RiemannMasullo
