module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation

/-! # Chapter 3.2: the printed global idelic functional equation -/

@[expose] public noncomputable section

namespace RiemannMasullo

open MeasureTheory NumberField
open scoped NumberField.AdeleRing

local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])

local instance printedCh03Sec2AdeleMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace 𝔸[F] := borel _

/-- Paper: Theorem 3.2.2.1(1)(b), p. 124. As printed: the global functional equation
holds for the Fourier transform using the character of Examples A.3.1.5, A.3.1.6,
A.3.1.8 and A.3.1.9. Negating the finite coordinates of the input to
`adeleStandardCharacter` implements the printed signs. The corrected identity is
`globalIdelicZFunction_functionalEquation`. See ERRATA F13. -/
def Printed.globalIdelicZFunction_functionalEquation : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : ℬ[F]),
    ∃ fhat : ℬ[F],
      (∀ y : 𝔸[F], fhat (Multiplicative.ofAdd y) =
        tamagawaFourier (additiveTamagawaMeasure F)
          (fun a : 𝔸[F] ↦ adeleStandardCharacter F (a.1, -a.2))
          (fun x ↦ f (Multiplicative.ofAdd x)) y) ∧
      ∀ c : HeckeCharacter (𝓞 F) F,
        globalIdelicZFunction f c = globalIdelicZFunction fhat
          (dualQuasiCharacter (G := IdeleClassGroup (𝓞 F) F) (ideleClassNorm F)
            (isProperMap_ideleClassNorm F).continuous c)

/-- A principal rational idele with real coordinate one must also be one at the prime three. -/
private theorem Printed.globalIdelicZFunction_functionalEquation_false_nonprincipal
    (g : IdeleGroup (𝓞 ℚ) ℚ) (hg : g.val = (1, -1)) :
    (QuotientGroup.mk g : IdeleClassGroup (𝓞 ℚ) ℚ) ≠ 1 := by
  intro he
  obtain ⟨r, hr⟩ := (QuotientGroup.eq_one_iff g).mp he
  have h := (congrArg Units.val hr).trans hg
  have hreal := congrArg (fun x : 𝔸[ℚ] ↦ x.1 Rat.infinitePlace) h
  change algebraMap ℚ Rat.infinitePlace.Completion r.val = 1 at hreal
  have hr₁ : r.val = 1 := (algebraMap ℚ Rat.infinitePlace.Completion).injective
    (hreal.trans (map_one _).symm)
  let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
  have hfinite := congrArg (fun x : 𝔸[ℚ] ↦ x.2 v) h
  change algebraMap ℚ (v.adicCompletion ℚ) r.val = -1 at hfinite
  rw [hr₁, map_one] at hfinite
  have : (1 : ℚ) = -1 := (algebraMap ℚ (v.adicCompletion ℚ)).injective
    (by simpa only [map_neg, map_one] using hfinite)
  norm_num at this

/-- Fourier dilation identifies the printed transform with the corrected transform of
the test translated by the finite sign idele. -/
private theorem Printed.globalIdelicZFunction_functionalEquation_false_fourier
    (g : IdeleGroup (𝓞 ℚ) ℚ) (hg : g.val = (1, -1))
    (hn : ideleClassNorm ℚ (QuotientGroup.mk g) = 1) (f : ℬ[ℚ]) (y : 𝔸[ℚ]) :
    adeleSchwartzFourier (schwartzBruhatUnitTranslate g f) (Multiplicative.ofAdd y) =
      tamagawaFourier (additiveTamagawaMeasure ℚ)
        (fun a : 𝔸[ℚ] ↦ adeleStandardCharacter ℚ (a.1, -a.2))
        (fun x ↦ f (Multiplicative.ofAdd x)) y := by
  have hd := adeleSchwartzFourier_dilation f g⁻¹ y
  have hni : ideleClassNorm ℚ (QuotientGroup.mk g⁻¹) = 1 := by
    rw [QuotientGroup.mk_inv, map_inv, hn, inv_one]
  simp only [hni, Units.val_one, NNReal.coe_one, inv_one, one_smul, inv_inv] at hd
  refine hd.trans ?_
  unfold adeleSchwartzFourier tamagawaFourier
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x ↦ ?_
  have hxy : x * (g.val * y) = ((x * y).1, -(x * y).2) := by
    rw [hg]
    exact Prod.ext (by change x.1 * (1 * y.1) = x.1 * y.1; rw [one_mul])
      (by change x.2 * (-1 * y.2) = -(x.2 * y.2); simp)
  simp only [toAdd_ofAdd, hxy]

/-- Left invariance of multiplicative Tamagawa measure gives the character factor
for the zeta integral of a translated test. -/
private theorem Printed.globalIdelicZFunction_functionalEquation_false_translate
    (g : IdeleGroup (𝓞 ℚ) ℚ) (f : ℬ[ℚ]) (c : HeckeCharacter (𝓞 ℚ) ℚ) :
    globalIdelicZetaIntegral (schwartzBruhatUnitTranslate g f) c =
      c (QuotientGroup.mk g) * globalIdelicZetaIntegral f c := by
  let : MeasurableSpace (IdeleGroup (𝓞 ℚ) ℚ) := borel _
  let : BorelSpace (IdeleGroup (𝓞 ℚ) ℚ) := ⟨rfl⟩
  have : (multiplicativeTamagawaMeasure ℚ).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.1
  unfold globalIdelicZetaIntegral
  rw [← integral_mul_left_eq_self (μ := multiplicativeTamagawaMeasure ℚ)
    (fun x ↦ schwartzBruhatUnitTranslate g f (Multiplicative.ofAdd x.val) *
      c (QuotientGroup.mk x)) g, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x ↦ by
    change f (Multiplicative.ofAdd (g⁻¹ * (g * x)).val) * c (QuotientGroup.mk (g * x)) = _
    rw [inv_mul_cancel_left, QuotientGroup.mk_mul, map_mul, mul_left_comm]

/-- Paper: Theorem 3.2.2.1(1)(b), p. 124. Over ℚ take the quadratic Hecke character
of the odd Dirichlet character modulo 3, twisted by the squared idelic norm. Take f
with a nonnegative real bump near 1, finite factor `1_{1+3ℤ₃}` at 3, and `1_{ℤₚ}`
elsewhere. Its zeta integral is nonzero by the local integrals and the absolutely
convergent Euler product. The printed transform is the corrected transform multiplied
in its argument by the idele with real coordinate 1 and finite coordinates −1.
The dual character takes value −1 on this idele, so the right side acquires a minus
sign by change of variables and meromorphic continuation. -/
theorem Printed.globalIdelicZFunction_functionalEquation_false :
    ¬ Printed.globalIdelicZFunction_functionalEquation := by
  intro hprinted
  have hsign : ((1, -1) : 𝔸[ℚ]) * (1, -1) = 1 :=
    Prod.ext (one_mul _) ((neg_mul_neg 1 1).trans (one_mul 1))
  let g : IdeleGroup (𝓞 ℚ) ℚ := ⟨(1, -1), (1, -1), hsign, hsign⟩
  let q := QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)
  have hg₂ : g ^ 2 = 1 := by rw [sq]; exact Units.ext hsign
  have hn : ideleClassNorm ℚ (q g) = 1 := sq_eq_one.mp (by rw [← map_pow, ← map_pow, hg₂]; simp)
  -- Character separation supplies a unitary character detecting the finite sign.
  obtain ⟨_, _, _, _, _, hT₂, hLC, _⟩ := ideleGroup_quotient.{0, 0} ℚ
  obtain ⟨χ, hχ⟩ := exists_pontryaginDual_apply_ne_one
    (Printed.globalIdelicZFunction_functionalEquation_false_nonprincipal g rfl)
  let c := ideleClassNormTwist χ 2
  have hc : c (q g) ≠ 1 := by
    change (χ (q g) : ℂ) * (((ideleClassNorm ℚ (q g)).val : ℝ) : ℂ) ^ (2 : ℂ) ≠ 1
    simpa [hn] using (show (χ (q g) : ℂ) ≠ 1 from fun h ↦ hχ (Subtype.ext h))
  obtain ⟨f, hf⟩ := exists_globalIdelicZetaIntegral_eq_completedHeckeL χ
  let s : Complex.re ⁻¹' Set.Ioi (1 : ℝ) := ⟨2, by norm_num⟩
  have hnonzero : globalIdelicZetaIntegral f c ≠ 0 := by
    rw [show globalIdelicZetaIntegral f c = completedHeckeL χ s from hf s]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by norm_num [s]))
      (finiteHeckeL_ne_zero_of_one_lt_re χ s)
  -- Comparing the two equations forces the translation to preserve this nonzero integral.
  obtain ⟨fhat, hhat, hfe⟩ := hprinted ℚ f
  have hfourier : fhat = adeleSchwartzFourier (schwartzBruhatUnitTranslate g f) :=
    Subtype.ext (funext fun y ↦ (hhat y.toAdd).trans
      (Printed.globalIdelicZFunction_functionalEquation_false_fourier g rfl hn f y.toAdd).symm)
  have he := hfe c
  rw [hfourier, ← RiemannMasullo.globalIdelicZFunction_functionalEquation] at he
  have hright := tate_twist_mem_rightHalf χ 2 (by norm_num)
  rw [globalIdelicZFunction_eq_integral f hright,
    globalIdelicZFunction_eq_integral _ hright,
    Printed.globalIdelicZFunction_functionalEquation_false_translate] at he
  exact hc (mul_right_cancel₀ hnonzero ((one_mul _).trans he).symm)

end RiemannMasullo
