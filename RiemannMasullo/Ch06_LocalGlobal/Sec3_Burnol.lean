module

public import RiemannMasullo.Ch06_LocalGlobal.Sec3

/-! # Dilation differences of polar-free adelic theta tests

Burnol’s adelic closure theorem uses a polar correction of unit-box tests (An adelic
causality problem related to abelian L-functions, Theorem 3.2, pp. 14–15). The following
realizations give the corresponding correction on the original Schwartz–Bruhat tests.
-/

@[expose] public noncomputable section
open Function IsDedekindDomain NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "ℬ" => SchwartzBruhat (Multiplicative 𝔸[F])

/-- On each nontrivial angular character a fixed norm-one translation difference gives
polar-free representatives of the same projected theta. The formula for the full theta
in particular preserves vanishing on every union of norm fibers. -/
theorem exists_polarFree_preserving_angular_theta (ω : PontryaginDual C₁) (hω : ω ≠ 1) :
    ∃ (h : C₁) (S : ℬ →ₗ[ℂ] adelePolarSubspace F), (ω h : ℂ) ≠ 1 ∧
      (∀ f, homogeneousAdelicTheta ω (S f).val = homogeneousAdelicTheta ω f) ∧
      (∀ f g, adelicTheta (S f).val g = ((ω h : ℂ) - 1)⁻¹ *
        (adelicTheta f (h.val⁻¹ * g) - adelicTheta f g)) := by
  obtain ⟨h, hh⟩ : ∃ h : C₁, (ω h : ℂ) ≠ 1 :=
    not_forall.mp fun hall ↦ hω (PontryaginDual.ext fun x ↦ Subtype.ext (hall x))
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (s := IdeleGroup.principalSubgroup (𝓞 F) F) h.val
  have hnorm : ideleNorm F u = 1 := by
    change ideleClassNorm F (QuotientGroup.mk u) = 1
    rw [hu, MonoidHom.mem_ker.mp h.property]
  let T : ℬ →ₗ[ℂ] ℬ := { toFun := schwartzBruhatUnitTranslate u,
                         map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let S := ((ω h : ℂ) - 1)⁻¹ • (T - LinearMap.id)
  have hS f : S f ∈ adelePolarSubspace F := by
    change adelePolarValues (F := F) (((ω h : ℂ) - 1)⁻¹ • (schwartzBruhatUnitTranslate u f - f)) = 0
    have hp : adelePolarValues (F := F) (schwartzBruhatUnitTranslate u f) = adelePolarValues (F := F) f := by
      apply Prod.ext
      · change f (Multiplicative.ofAdd (u.inv * 0)) = f (Multiplicative.ofAdd 0)
        rw [mul_zero]
      · change adeleSchwartzFourier (schwartzBruhatUnitTranslate u f) _ = adeleSchwartzFourier f _
        rw [adeleSchwartzFourier_zero_unitTranslate, hnorm]
        simp
    rw [map_smul, map_sub, hp, sub_self, smul_zero]
  refine ⟨h, S.codRestrict (adelePolarSubspace F) hS, hh, ?_, ?_⟩
  · intro f
    change homogeneousAdelicThetaLinearMap F ω (((ω h : ℂ) - 1)⁻¹ • (schwartzBruhatUnitTranslate u f - f)) = _
    rw [map_smul, map_sub, globalConverse_nontrivial_exact_theta_translate ω h u hu]
    have he (a : ℂ) (y : C(C𝔽, ℂ)) : a • y - y = (a - 1) • y := by
      apply ContinuousMap.ext
      intro x
      change a * y x - y x = (a - 1) * y x
      ring
    rw [he, inv_smul_smul₀ (sub_ne_zero.mpr hh)]
    rfl
  · intro f g
    change adelicThetaLinearMap F (((ω h : ℂ) - 1)⁻¹ • (schwartzBruhatUnitTranslate u f - f)) g = _
    rw [map_smul, map_sub]
    change ((ω h : ℂ) - 1)⁻¹ * (adelicTheta (schwartzBruhatUnitTranslate u f) g - adelicTheta f g) = _
    rw [adelicTheta_unitTranslate u f g, hu]

/-- A double dilation difference cancels both polar values of any input. Its theta
is the corresponding four-term difference of ordinary theta, so contractions of norm
at most one preserve an upper cutoff on global theta. -/
theorem exists_polarFree_two_dilation_map (u v : I𝔽) :
    let c : ℂ := (((ideleNorm F u).val : ℝ) : ℂ)⁻¹
    let D (f : ℬ) := f - c • schwartzBruhatUnitTranslate u f
    ∃ S : ℬ →ₗ[ℂ] adelePolarSubspace F,
      (∀ f, (S f).val = D f - schwartzBruhatUnitTranslate v (D f)) ∧
      (∀ f (g : C𝔽), let q : I𝔽 → C𝔽 := QuotientGroup.mk
        adelicTheta (S f).val g =
          (adelicTheta f g - c * adelicTheta f ((q u)⁻¹ * g)) -
          (adelicTheta f ((q v)⁻¹ * g) - c * adelicTheta f ((q u)⁻¹ * ((q v)⁻¹ * g)))) := by
  intro c D
  let T (a : I𝔽) : ℬ →ₗ[ℂ] ℬ := { toFun := schwartzBruhatUnitTranslate a,
                                     map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  let S := (LinearMap.id - T v).comp (LinearMap.id - c • T u)
  let Z := Multiplicative.ofAdd (0 : 𝔸[F])
  have hc : ((((ideleNorm F u).val : ℝ) : ℂ)) ≠ 0 := by exact_mod_cast (ideleNorm F u).ne_zero
  have hD (f : ℬ) : (adelePolarValues (F := F) (D f)).2 = 0 := by
    change (adelePolarValues (F := F) (f - c • schwartzBruhatUnitTranslate u f)).2 = 0
    rw [map_sub, map_smul]
    change adeleSchwartzFourier f Z - c * adeleSchwartzFourier (schwartzBruhatUnitTranslate u f) Z = 0
    rw [adeleSchwartzFourier_zero_unitTranslate, ← mul_assoc, inv_mul_cancel₀ hc, one_mul, sub_self]
  have hS f : S f ∈ adelePolarSubspace F := by
    change adelePolarValues (F := F) (D f - schwartzBruhatUnitTranslate v (D f)) = 0
    rw [map_sub, sub_eq_zero]
    refine Prod.ext ?_ ?_
    · change D f Z = D f (Multiplicative.ofAdd (v.inv * 0))
      rw [mul_zero]
    · change adeleSchwartzFourier (D f) Z = adeleSchwartzFourier (schwartzBruhatUnitTranslate v (D f)) Z
      rw [adeleSchwartzFourier_zero_unitTranslate, show adeleSchwartzFourier (D f) Z = 0 from hD f, mul_zero]
  refine ⟨S.codRestrict (adelePolarSubspace F) hS, fun f ↦ rfl, ?_⟩
  intro f g q
  have htheta (x : C𝔽) : adelicTheta (D f) x = adelicTheta f x - c * adelicTheta f ((q u)⁻¹ * x) := by
    change adelicThetaLinearMap F (f - c • schwartzBruhatUnitTranslate u f) x = _
    rw [map_sub, map_smul]
    change adelicTheta f x - c * adelicTheta (schwartzBruhatUnitTranslate u f) x = _
    rw [adelicTheta_unitTranslate]
  change adelicThetaLinearMap F (D f - schwartzBruhatUnitTranslate v (D f)) g = _
  rw [map_sub]
  change adelicTheta (D f) g - adelicTheta (schwartzBruhatUnitTranslate v (D f)) g = _
  rw [adelicTheta_unitTranslate, htheta, htheta]

/-- Burnol's normalized theta minus its additive integral term, in the self-dual
additive Tamagawa normalization (Definition 1.1, p. 3). -/
def regularizedAdelicTheta : ℬ →ₗ[ℂ] (C𝔽 → ℂ) :=
  LinearMap.pi fun g ↦
    let n : ℂ := Real.sqrt ((ideleClassNorm F g).val : ℝ)
    n • ((LinearMap.proj g).comp ((ContinuousMap.coeFnLinearMap (R := ℂ)).comp (adelicThetaLinearMap F))) -
      n⁻¹ • ((LinearMap.snd ℂ ℂ ℂ).comp (adelePolarValues (F := F)))

/-- Critical-line normalization gives the square root of the idele norm under
translation of the Schwartz--Bruhat input. -/
theorem regularizedAdelicTheta_unitTranslate (u : I𝔽) (f : ℬ) (g : C𝔽) :
    regularizedAdelicTheta (schwartzBruhatUnitTranslate u f) g =
      (Real.sqrt ((ideleNorm F u).val : ℝ) : ℂ) *
        regularizedAdelicTheta f ((QuotientGroup.mk u)⁻¹ * g) := by
  let a : ℝ := (ideleNorm F u).val
  let r : ℝ := (ideleClassNorm F g).val
  have ha : 0 < a := (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleNorm F u).ne_zero))
  have hr : 0 < r := (NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (ideleClassNorm F g).ne_zero))
  have hn : ((ideleClassNorm F ((QuotientGroup.mk u : C𝔽)⁻¹ * g)).val : ℝ) = a⁻¹ * r := by
    simp only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, NNReal.coe_mul, NNReal.coe_inv]
    rfl
  let G := (QuotientGroup.mk u : C𝔽)⁻¹ * g
  let Z := Multiplicative.ofAdd (0 : 𝔸[F])
  change (Real.sqrt r : ℂ) * adelicTheta (schwartzBruhatUnitTranslate u f) g -
      (Real.sqrt r : ℂ)⁻¹ * adeleSchwartzFourier (schwartzBruhatUnitTranslate u f) Z =
    (Real.sqrt a : ℂ) * ((Real.sqrt ((ideleClassNorm F G).val : ℝ) : ℂ) * adelicTheta f G -
      (Real.sqrt ((ideleClassNorm F G).val : ℝ) : ℂ)⁻¹ * adeleSchwartzFourier f Z)
  rw [adelicTheta_unitTranslate, adeleSchwartzFourier_zero_unitTranslate, show ((ideleClassNorm F G).val : ℝ) = a⁻¹ * r from hn,
    Real.sqrt_mul (inv_nonneg.mpr ha.le), Real.sqrt_inv, Complex.ofReal_mul, Complex.ofReal_inv]
  change _ - (Real.sqrt r : ℂ)⁻¹ * ((a : ℂ) * _) = _
  have ha' : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
  have hr' : ((Real.sqrt r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hr).ne'
  have ha2 : ((Real.sqrt a : ℂ))^2 = a := by exact_mod_cast Real.sq_sqrt ha.le
  dsimp only [G, Z]
  rw [← ha2]
  field_simp

/-- Two contractions preserve any upper cutoff of the full theta function. On the
regularized theta they realize the two differences with coefficients equal to the
inverse square root of the first norm and the square root of the second. -/
theorem exists_polarFree_regularizedAdelicTheta_differences (u v : I𝔽)
    (hu : ideleNorm F u ≤ 1) (hv : ideleNorm F v ≤ 1) (f : ℬ) (b : ℝ≥0ˣ)
    (hf : ∀ g : C𝔽, b < ideleClassNorm F g → adelicTheta f g = 0) :
    let E := regularizedAdelicTheta f
    let d (g : C𝔽) := E g - (Real.sqrt ((ideleNorm F u).val : ℝ) : ℂ)⁻¹ * E ((QuotientGroup.mk u)⁻¹ * g)
    ∃ p : adelePolarSubspace F,
      (∀ g : C𝔽, b < ideleClassNorm F g → adelicTheta p.val g = 0) ∧
      ∀ g : C𝔽, regularizedAdelicTheta p.val g =
        d g - (Real.sqrt ((ideleNorm F v).val : ℝ) : ℂ) * d ((QuotientGroup.mk v)⁻¹ * g) := by
  intro E d
  obtain ⟨S, hS, hθ⟩ := exists_polarFree_two_dilation_map u v
  refine ⟨S f, ?_, ?_⟩
  · intro g hg
    have hshift (w : I𝔽) (hw : ideleNorm F w ≤ 1) (x : C𝔽) (hx : b < ideleClassNorm F x) :
        b < ideleClassNorm F ((QuotientGroup.mk w)⁻¹ * x) := by
      rw [map_mul, map_inv]
      exact hx.trans_le (le_mul_of_one_le_left' (one_le_inv'.mpr hw))
    rw [hθ, hf g hg, hf _ (hshift u hu g hg), hf _ (hshift v hv g hg),
      hf _ (hshift u hu _ (hshift v hv g hg))]
    simp
  · intro g
    let a : ℝ := (ideleNorm F u).val
    have ha : 0 < a := NNReal.coe_pos.mpr (Units.zero_lt _)
    have hr : (Real.sqrt a : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr ha).ne'
    have hs : (Real.sqrt a : ℂ)^2 = (a : ℂ) := by exact_mod_cast Real.sq_sqrt ha.le
    have hc : (a : ℂ)⁻¹ * (Real.sqrt a : ℂ) = (Real.sqrt a : ℂ)⁻¹ := by rw [←hs]; field_simp
    let D := f - (a : ℂ)⁻¹ • schwartzBruhatUnitTranslate u f
    have hD (x : C𝔽) : regularizedAdelicTheta D x = d x := by
      simp only [D, map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
        regularizedAdelicTheta_unitTranslate]
      change E x - (a : ℂ)⁻¹ * ((Real.sqrt a : ℂ) * E ((QuotientGroup.mk u)⁻¹ * x)) = _
      rw [←mul_assoc, hc]
    rw [hS]
    change regularizedAdelicTheta (D - schwartzBruhatUnitTranslate v D) g = _
    simp only [map_sub, Pi.sub_apply, regularizedAdelicTheta_unitTranslate, hD]

end RiemannMasullo
