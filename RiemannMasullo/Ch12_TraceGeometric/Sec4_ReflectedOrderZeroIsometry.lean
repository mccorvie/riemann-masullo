module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedLogTransport
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.Tactic.Ring

/-! # The order-zero angular coefficient isometry -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "N" => sIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "η" => sLocalNormOneQuotientMeasure F S
local notation "ℓ" => logSIdeleQuotientNorm F S
local notation "ν" => intervalSobolevMeasure μJ ℓ 0 0 0
local notation "W₀" => CompactIntervalSobolev μJ ℓ 0 0 0
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)
local notation "expUnit" => fun x : ℝ ↦ Units.mk0 (Real.toNNReal (Real.exp x)) (by positivity)
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)

private theorem intervalSobolevMeasure_zero_zero_zero_real :
    intervalSobolevMeasure (volume : Measure ℝ) id 0 0 0 = volume := by
  have h (x : ℝ) : intervalSobolevDensity 0 0 0 x = 1 := by
    simp [intervalSobolevDensity]
  change (volume : Measure ℝ).withDensity (fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 x)) = _
  simp only [h, ENNReal.ofReal_one]
  change (volume : Measure ℝ).withDensity (1 : ℝ → ℝ≥0∞) = volume
  exact withDensity_one

/-- An inverse-character lift recovers the half-density theta function from
its values on the norm section. -/
private theorem sLocalHalfDensityTheta_eq_logSection
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = ω)
    (hsec : ∀ t, χ (QuotientGroup.mk (τ t)) = 1) (f : Bₛ) (g : Jₛ) :
    let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω f
    modulationWeight (continuousSIdeleQuotientNorm F S) (1 / 2) θ g =
      (χ g : ℂ)⁻¹ * ((Real.exp (ℓ g / 2) : ℂ) *
        θ (QuotientGroup.mk (τ (expUnit (ℓ g))))) := by
  intro θ
  let q : Jₛ := QuotientGroup.mk (τ (expUnit (ℓ g)))
  have hp : 0 < ((N g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hexp : Real.exp (ℓ g) = ((N g).val : ℝ) := Real.exp_log hp
  have ht : expUnit (ℓ g) = N g := by
    apply Units.ext
    apply NNReal.eq
    exact (Real.coe_toNNReal _ (Real.exp_pos _).le).trans hexp
  have hN : N q = N g := by
    change N (QuotientGroup.mk (τ (expUnit (ℓ g)))) = _
    rw [sIdeleQuotientNorm_mk, hτ, ht]
  let h : J₁ := ⟨q / g, by rw [MonoidHom.mem_ker, map_div, hN, div_self']⟩
  have hg : h.val⁻¹ * q = g := by
    change (q / g)⁻¹ * q = g
    rw [inv_div, div_mul_cancel]
  have hχh : χ h.val = ω h := congrArg (fun ψ : PontryaginDual J₁ ↦ ψ h) hχ
  have hphase : (ω h : ℂ) = (χ g : ℂ)⁻¹ := by
    rw [← hχh]
    change (χ (q / g) : ℂ) = (χ g : ℂ)⁻¹
    have hq : χ q = 1 := hsec (expUnit (ℓ g))
    rw [map_div, hq, one_div, Circle.coe_inv]
  let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  have hθ : θ g = (χ g : ℂ)⁻¹ * θ q := by
    calc
      θ g = θ (h.val⁻¹ * q) := congrArg θ hg.symm
      _ = (ω h : ℂ) * θ q := sLocalHomogeneousAdelicTheta_homogeneous F S η ω f h q
      _ = _ := congrArg (· * θ q) hphase
  have hpow : ((N g).val : ℝ) ^ (1 / 2 : ℝ) = Real.exp (ℓ g / 2) := by
    change ((N g).val : ℝ) ^ (1 / 2 : ℝ) = Real.exp (Real.log ((N g).val : ℝ) / 2)
    rw [Real.rpow_def_of_pos hp, mul_one_div]
  rw [modulationWeight, LinearMap.mulLeft_apply, Pi.mul_apply]
  change (((((N g).val : ℝ) ^ (1 / 2 : ℝ)) : ℝ) : ℂ) * θ g =
    (χ g : ℂ)⁻¹ * ((Real.exp (ℓ g / 2) : ℂ) * θ q)
  rw [hpow, hθ, mul_left_comm]

/-- At order zero a single inverse-character isometry recovers each half-density
quotient theta vector from its normalized logarithmic coefficient. -/
theorem exists_sLocalWeightedLogCharacterLift_leftInverse_of_representatives_zero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = ω)
    (hsec : ∀ t, χ (QuotientGroup.mk (τ t)) = 1) :
    ∃ L : FlatL2 →ₗᵢ[ℂ] W₀,
      (∀ v, (L v : Jₛ → ℂ) =ᵐ[ν] fun q ↦ (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
        (χ q : ℂ)⁻¹ * v (ℓ q)) ∧
      ∀ (f : Bₛ) (u : W₀) (v : FlatL2),
      let θ := sLocalHomogeneousAdelicThetaLinearMap F S ω f
      ((u : Jₛ → ℂ) =ᵐ[μJ] modulationWeight (continuousSIdeleQuotientNorm F S) (1 / 2) θ) →
      ((v : ℝ → ℂ) =ᵐ[volume] fun t ↦ (Real.sqrt (Measure.real η univ) : ℂ) *
        ((Real.exp (t / 2) : ℂ) * θ (QuotientGroup.mk (τ (expUnit t))))) →
      L v = u := by
  let d : ℂ := Real.sqrt (Measure.real η univ)
  have hLift : ∃ L : FlatL2 →ₗᵢ[ℂ] W₀,
      ∀ v, (L v : Jₛ → ℂ) =ᵐ[ν] fun q ↦ d⁻¹ * (χ q : ℂ)⁻¹ * v (ℓ q) := by
    have transfer (μ : Measure ℝ) (hμ : μ = volume)
        (h : ∃ L : Lp ℂ 2 μ →ₗᵢ[ℂ] W₀,
          ∀ v, (L v : Jₛ → ℂ) =ᵐ[ν] fun q ↦ d⁻¹ * (χ q : ℂ)⁻¹ * v (ℓ q)) :
        ∃ L : FlatL2 →ₗᵢ[ℂ] W₀,
          ∀ v, (L v : Jₛ → ℂ) =ᵐ[ν] fun q ↦ d⁻¹ * (χ q : ℂ)⁻¹ * v (ℓ q) := by
      subst μ
      exact h
    exact transfer _ intervalSobolevMeasure_zero_zero_zero_real
      (exists_sLocalWeightedLogCharacterLift τ hτ 0 0 0 χ)
  obtain ⟨L, hL⟩ := hLift
  let : BorelSpace Jₛ := ⟨rfl⟩
  have hlog : Measurable ℓ := Real.measurable_log.comp
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (continuousSIdeleQuotientNorm F S).continuous)).measurable
  have hlogMap : MeasurePreserving ℓ ν ((η univ) • (volume : Measure ℝ)) :=
    ⟨hlog, by simpa only [intervalSobolevMeasure_zero_zero_zero_real] using
      sLocalLogNorm_map_intervalSobolevMeasure τ hτ 0 0 0⟩
  have hνμ : ν ≪ μJ := withDensity_absolutelyContinuous _ _
  let : CompactSpace J₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1)))
  let : Measure.IsHaarMeasure η := (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1
  let : IsFiniteMeasure η := CompactSpace.isFiniteMeasure
  have hmass : 0 < Measure.real η univ := measureReal_univ_pos
  have hd : d ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hmass).ne'
  refine ⟨L, hL, ?_⟩
  intro f u v θ hu hv
  let profile (t : ℝ) : ℂ := (Real.exp (t / 2) : ℂ) * θ (QuotientGroup.mk (τ (expUnit t)))
  have hPull := hlogMap.quasiMeasurePreserving.ae_eq_comp (Measure.ae_smul_measure hv (η univ))
  apply Lp.ext
  filter_upwards [hL v, hPull, hνμ.ae_eq hu] with g hLg hvg hug
  change v (ℓ g) = d * profile (ℓ g) at hvg
  have hpoint : modulationWeight (continuousSIdeleQuotientNorm F S) (1 / 2) θ g =
      (χ g : ℂ)⁻¹ * profile (ℓ g) := sLocalHalfDensityTheta_eq_logSection τ hτ ω χ hχ hsec f g
  rw [hLg, hvg, hug, hpoint]
  calc
    _ = (d⁻¹ * d) * ((χ g : ℂ)⁻¹ * profile (ℓ g)) := by ring
    _ = _ := by rw [inv_mul_cancel₀ hd, one_mul]

/-- In order zero the normalized angular coefficient has an isometric left
inverse on the closed invariant Paley–Wiener level. -/
theorem exists_sLocalWeightedAngularLogCoefficient_leftInverse_on_level_zero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) (hχ : χ.comp include₁ = ω)
    (hsec : ∀ t, χ (QuotientGroup.mk (τ t)) = 1) (B : ℝ)
    (Q : W₀ →L[ℂ] FlatL2)
    (hQ : ∀ u, (Q u : ℝ → ℂ) =ᵐ[volume] fun x ↦
      (Real.sqrt (Measure.real η univ) : ℂ)⁻¹ *
        ∫ h : J₁, (ω h : ℂ) * u (h.val * QuotientGroup.mk (τ (expUnit x))) ∂η) :
    ∃ L : FlatL2 →ₗᵢ[ℂ] W₀,
      ∀ (u : W₀), u ∈ sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos ω B →
        L (Q u) = u := by
  obtain ⟨L, _, hLeft⟩ :=
    exists_sLocalWeightedLogCharacterLift_leftInverse_of_representatives_zero τ hτ ω χ hχ hsec
  let gen (f : Zₛ) : W₀ := sLocalPWThetaSobolevMap (F := F) (S := S) (s := 0) halfPos ω f
  have hGen (f : Zₛ) : L (Q (gen f)) = gen f :=
    hLeft f.val (gen f) (Q (gen f))
      (sLocalPWThetaSobolevMap_apply (F := F) (S := S) (s := 0) halfPos ω f)
      (sLocalWeightedAngularLogCoefficient_onTheta τ hτ ω Q hQ f)
  let D : W₀ →L[ℂ] W₀ := L.toContinuousLinearMap.comp Q - ContinuousLinearMap.id ℂ W₀
  have hker : sLocalInvariantPWSobolev (F := F) (S := S) (s := 0) le_rfl halfPos ω B ≤ D.ker := by
    unfold sLocalInvariantPWSobolev
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) D.isClosed_ker
    rintro _ ⟨f, rfl⟩
    apply LinearMap.mem_ker.mpr
    change L (Q (gen f.val)) - gen f.val = 0
    exact sub_eq_zero.mpr (hGen f.val)
  refine ⟨L, fun u hu ↦ ?_⟩
  have hu' : D u = 0 := LinearMap.mem_ker.mp (hker hu)
  change L (Q u) - (u : W₀) = 0 at hu'
  exact sub_eq_zero.mp hu'

end RiemannMasullo
