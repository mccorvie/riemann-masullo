module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # The radial part of the S-local trace action

For a test and a vector that factor through the quotient norm, the actual
Hardy–Sobolev test action descends to positive Haar convolution. The quotient
norm contributes the mass of the norm-one subgroup. The positive half-density
then converts this convolution to the additive dilation formula of Step I.
-/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo.SLocalRadialAction

noncomputable section

local notation "HaarRay" => positiveRealHaar
local notation "P" => ℝ≥0ˣ

local instance instBorelSpacePositiveUnits : BorelSpace P :=
  borelSpace_units_of_continuousInv₀ _

/-- The positive real underlying a multiplicative unit. -/
@[expose] public def radius (t : P) : ℝ := (t.val : ℝ)

private theorem radius_pos (t : P) : 0 < radius t :=
  NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr t.ne_zero)

private theorem measurable_radius : Measurable radius :=
  (NNReal.continuous_coe.comp Units.continuous_val).measurable

private theorem radius_inv_mul (a x : P) : radius (a⁻¹ * x) = (radius a)⁻¹ * radius x := by
  simp only [radius, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv]

private def expUnit (t : ℝ) : P :=
  Units.mk0 (Real.exp t).toNNReal
    (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos t)))

private theorem measurable_expUnit : Measurable expUnit :=
  measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable

private theorem radius_expUnit (t : ℝ) : radius (expUnit t) = Real.exp t :=
  Real.coe_toNNReal _ (Real.exp_pos t).le

/-- Multiplying by radius converts the positive multiplicative Haar integral to the
positive additive integral. -/
public theorem positiveRealHaar_integral_radius_mul (f : ℝ → ℂ) (hf : Measurable f) :
    (∫ t : P, (radius t : ℂ) * f (radius t) ∂HaarRay) = ∫ t in Ioi (0 : ℝ), f t := by
  have hm : Measurable (fun t : P ↦ (radius t : ℂ) * f (radius t)) :=
    (Complex.measurable_ofReal.comp measurable_radius).mul (hf.comp measurable_radius)
  change (∫ t : P, (radius t : ℂ) * f (radius t) ∂(Measure.map expUnit volume)) = _
  rw [integral_map measurable_expUnit.aemeasurable hm.aestronglyMeasurable]
  simpa only [radius_expUnit, Complex.real_smul] using MeasureTheory.integral_comp_exp f

/-- The positive half-density that converts an additive profile to a Haar profile. -/
@[expose] public def halfDensity (f : ℝ → ℂ) (x : P) : ℂ :=
  (Real.sqrt (radius x) : ℂ) * f (radius x)

private theorem measurable_halfDensity {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (halfDensity f) :=
  (Complex.measurable_ofReal.comp (Real.continuous_sqrt.measurable.comp measurable_radius)).mul
    (hf.comp measurable_radius)

private theorem sqrt_radius_inv_mul (a x : P) :
    Real.sqrt (radius (a⁻¹ * x)) = Real.sqrt (radius x) * radius a ^ (-(1 / 2 : ℝ)) := by
  rw [radius_inv_mul, Real.sqrt_mul (inv_nonneg.mpr (radius_pos a).le),
    Real.sqrt_inv, Real.rpow_neg (radius_pos a).le, ← Real.sqrt_eq_rpow, mul_comm]

/-- In the half-density coordinate the Haar convolution with radial test
`a ↦ a ψ(a)` uses the additive test `ψ(a)` against Lebesgue measure. -/
public theorem positiveRealHaar_lcaConvolution_halfDensity
    (ψ f : ℝ → ℂ) (hψ : Measurable ψ) (hf : Measurable f) (x : P) :
    lcaConvolution HaarRay (fun a ↦ (radius a : ℂ) * ψ (radius a)) (halfDensity f) x =
      (Real.sqrt (radius x) : ℂ) *
        ∫ a in Ioi (0 : ℝ), ψ a * (((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (a⁻¹ * radius x)) := by
  let K (a : ℝ) := ψ a * (((a ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (a⁻¹ * radius x))
  have hK : Measurable K :=
    hψ.mul ((Complex.measurable_ofReal.comp (measurable_id.pow_const _)).mul
      (hf.comp (measurable_id.inv.mul measurable_const)))
  calc
    lcaConvolution HaarRay (fun a ↦ (radius a : ℂ) * ψ (radius a)) (halfDensity f) x =
        ∫ a : P, (Real.sqrt (radius x) : ℂ) * ((radius a : ℂ) * K (radius a))
            ∂HaarRay := by
      unfold lcaConvolution
      refine integral_congr_ae (Eventually.of_forall fun a ↦ ?_)
      dsimp only [halfDensity, K]
      rw [sqrt_radius_inv_mul, radius_inv_mul, Complex.ofReal_mul]
      ring
    _ = _ := by
      rw [integral_const_mul, positiveRealHaar_integral_radius_mul K hK]

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1

variable (F : Type*) [Field F] [NumberField F]
  (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "J(" p ")" => SIdeleQuotient F p
local notation "N(" p ")" => continuousSIdeleQuotientNorm F p
local notation "μ(" p ")" => sLocalQuotientTamagawaMeasure F p
local notation "W(" p "," a "," b "," s ")" =>
  CompactIntervalSobolev μ(p) (fun x : J(p) ↦ Real.log (radius (N(p) x))) a b s
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)

local instance : MeasurableSpace J₁ := borel _

/-- Paper: Theorem 3.3.1.1(3), p. 129.
The S-idele quotient norm pushes quotient Tamagawa measure to `dt/t`
scaled by the total mass of the norm-one subgroup. -/
public theorem sLocalQuotientTamagawaMeasure_map_norm :
    (sLocalQuotientTamagawaMeasure F S).map
      (continuousSIdeleQuotientNorm F S : J(S) → ℝ≥0ˣ) =
      (sLocalNormOneQuotientMeasure F S Set.univ) • positiveRealHaar := by
  let : BorelSpace J₁ := ⟨rfl⟩
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* Iₛ :=
    ⟨p.comp (canonicalIdeleNormSection F), hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := sIdeleNorm_project_canonicalSection F S
  let j (x : J₁ × ℝ≥0ˣ) : J(S) := x.1.val * QuotientGroup.mk (τ x.2)
  have hj : Measurable j :=
    ((continuous_subtype_val.comp continuous_fst).mul
      ((show Continuous (QuotientGroup.mk : Iₛ → J(S)) from continuous_quotient_mk').comp
        (τ.continuous.comp continuous_snd))).measurable
  let N := continuousSIdeleQuotientNorm F S
  have hN : Measurable (N : J(S) → ℝ≥0ˣ) := N.continuous.measurable
  have hNj : (N : J(S) → ℝ≥0ˣ) ∘ j = Prod.snd := by
    funext x
    change sIdeleQuotientNorm F S (x.1.val * QuotientGroup.mk (τ x.2)) = x.2
    rw [map_mul, MonoidHom.mem_ker.mp x.1.property, one_mul]
    exact (sIdeleQuotientNorm_mk F S (τ x.2)).trans (hτ x.2)
  have hprod : ((sLocalNormOneQuotientMeasure F S).prod positiveRealHaar).map j =
      sLocalQuotientTamagawaMeasure F S :=
    (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).2 τ hτ
  change (sLocalQuotientTamagawaMeasure F S).map (N : J(S) → ℝ≥0ˣ) = _
  rw [← hprod, Measure.map_map hN hj, hNj, Measure.map_snd_prod]

/-- Paper: Step I of Theorem 12.4.1.1, pp. 515–516. The actual weighted test action on a radial
representative is positive Haar convolution multiplied by the norm-one mass.
Deviation: This statement uses radial tests directly on the quotient. -/
public theorem testAction_ae_radial
    (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport J(S)) (χ f : P → ℂ)
    (hχ : Measurable χ) (hf : Measurable f)
    (hφ : ∀ g : J(S), φ.val g = χ (N(S) g)) (u : W(S, a, b, s))
    (hu : (u : J(S) → ℂ) =ᵐ[μ(S)] fun g ↦ f (N(S) g)) :
    (hardySobolevTestAction μ(S) N(S) a b s hab hs φ u : J(S) → ℂ) =ᵐ[μ(S)]
      fun g ↦ (sLocalNormOneQuotientMeasure F S Set.univ).toReal •
        lcaConvolution HaarRay χ f (N(S) g) := by
  refine (hardySobolevTestAction_apply μ(S) N(S) a b s hab hs φ u).trans ?_
  refine Eventually.of_forall fun x ↦ ?_
  unfold lcaConvolution
  let k (t : P) : ℂ := χ t * f (t⁻¹ * N(S) x)
  have htranslate : Continuous (fun t : P ↦ t⁻¹ * N(S) x) :=
    continuous_inv.mul continuous_const
  have hk : Measurable k := hχ.mul (hf.comp htranslate.measurable)
  have hN : Measurable (N(S) : J(S) → P) := (N(S)).continuous.measurable
  calc
    (∫ g, φ.val g * u (g⁻¹ * x) ∂μ(S)) = ∫ g, k (N(S) g) ∂μ(S) := by
      have hshift : MeasurePreserving (fun g : J(S) ↦ g⁻¹ * x) μ(S) μ(S) :=
        (measurePreserving_mul_right μ(S) x).comp (Measure.measurePreserving_inv μ(S))
      refine integral_congr_ae ?_
      filter_upwards [hshift.quasiMeasurePreserving.ae hu] with g hg
      simp only [k, hφ g, hg, map_mul, map_inv]
    _ = ∫ t, k t ∂(μ(S).map (N(S) : J(S) → P)) :=
      (integral_map hN.aemeasurable hk.aestronglyMeasurable).symm
    _ = _ := by
      rw [sLocalQuotientTamagawaMeasure_map_norm, integral_smul_measure]

/-- Paper: (12.4.1.5–7), p. 516. For the radial quotient test
`g ↦ N(g) ψ(N(g))`, the positive half-density in the output multiplies the
additive dilation integral. The norm-one mass is the quotient Haar factor.
Deviation: This is a radial quotient-coordinate identity before the cutoff composition. -/
public theorem testAction_ae_halfDensity
    (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport J(S)) (ψ f : ℝ → ℂ)
    (hψ : Measurable ψ) (hf : Measurable f)
    (hφ : ∀ g : J(S), φ.val g = (radius (N(S) g) : ℂ) * ψ (radius (N(S) g)))
    (u : W(S, a, b, s)) (hu : (u : J(S) → ℂ) =ᵐ[μ(S)] fun g ↦ halfDensity f (N(S) g)) :
    (hardySobolevTestAction μ(S) N(S) a b s hab hs φ u : J(S) → ℂ) =ᵐ[μ(S)]
      fun g ↦ (sLocalNormOneQuotientMeasure F S Set.univ).toReal •
        ((Real.sqrt (radius (N(S) g)) : ℂ) *
          ∫ t in Ioi (0 : ℝ), ψ t *
            (((t ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * f (t⁻¹ * radius (N(S) g)))) := by
  have hχ : Measurable (fun t : P ↦ (radius t : ℂ) * ψ (radius t)) :=
    (Complex.measurable_ofReal.comp measurable_radius).mul (hψ.comp measurable_radius)
  refine (testAction_ae_radial F S a b s hab hs φ _ _ hχ
    (measurable_halfDensity hf) hφ u hu).trans ?_
  exact Eventually.of_forall fun g ↦ congrArg ((sLocalNormOneQuotientMeasure F S Set.univ).toReal • ·)
    (positiveRealHaar_lcaConvolution_halfDensity ψ f hψ hf (N(S) g))

end

end RiemannMasullo.SLocalRadialAction
