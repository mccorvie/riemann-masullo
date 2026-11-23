module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a

import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
import Mathlib.GroupTheory.MonoidLocalization.UniqueFactorization

/-! # §7.3.1 Statements that are false as printed -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 3

local notation "chart(" field ", " places ", " χ ")" =>
  quasiCharacterNormTwist (sIdeleQuotientNorm field places)
  (isProperMap_sIdeleQuotientNorm field places).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ))
local notation "period(" places ", " v ")" =>
  (2 * Real.pi / Real.log ((v : places).val.asIdeal.absNorm : ℝ))
local notation "phase(" field ", " places ", " χ ", " v ", " u ", " t ")" =>
  (t ∈ Ico 0 period(places, v) ∧
    sLocalFiniteRestriction v (chart(field, places, χ) (-(t : ℂ) * Complex.I)) u = 1)
local notation "uniformizerNorm(" field ", " places ", " v ", " u ")" =>
  (‖(↑(u) : (v : places).val.adicCompletion field)‖ = ((v : places).val.asIdeal.absNorm : ℝ)⁻¹)

/-- Paper: Theorem 7.3.1.2(2), p. 341.
Each listed coefficient is called an eigendistribution of its center. The finite
sets S and T specify the finite parts of the printed S and S₀, both of which
contain all infinite places. Pullback to tests expresses the weight equation. -/
def Printed.sLocalOrbitalPrincipalParts_eigendistributions : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S T : Finset (HeightOneSpectrum (𝓞 F))),
    IsSaturatedPlaceSet S →
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) → T ⊆ S →
    ∀ (ω : PontryaginDual (sIdeleQuotientNorm F S).ker) (c : QuasiCharacter (SIdeleQuotient F S)),
      normOneRestriction (sIdeleQuotientNorm F S) c =
        (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp ω →
      0 < sLocalRhoPoleOrder c →
      ∀ k : ℕ, sLocalRhoPoleOrder c - ((sLocalArchPolePlaces c).card +
          sLocalFinitePoleMultiplicity T c) < k → k ≤ sLocalRhoPoleOrder c →
        sLocalPrincipalPartCoeff c k ∈ sLocalEigendistributions c

/-- Paper: Theorem 7.3.1.2(2), p. 341.
For ℚ take S = {∞,2,3}, S₀ = {∞,2}, and c = 1. The real Gaussian times the
integer indicators has a triple pole with leading coefficient 2/(log 2 · log 3).
Dilation of norm 2 multiplies the zeta germ by 2^s and changes the selected
second-order coefficient by (log 2) times the leading coefficient. -/
theorem Printed.sLocalOrbitalPrincipalParts_eigendistributions_false :
    ¬ Printed.sLocalOrbitalPrincipalParts_eigendistributions := by sorry

/-- Paper: Discussion after (7.3.1.11), p. 344.
At a common pole, the phases at two places over the same rational prime differ by a unique
integer multiple of the period for that prime. The integer norm of the rational place is p. -/
def Printed.sLocalOrbitalPhase_sub : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let Jₛ := SIdeleQuotient F S
    IsSaturatedPlaceSet S →
    ∀ (p : HeightOneSpectrum (𝓞 ℚ)) (χ : PontryaginDual Jₛ) (v w : S),
      v.val ∈ sLocalPrimaryPlaces S p → w.val ∈ sLocalPrimaryPlaces S p →
      ∀ (uᵥ : (v.val.adicCompletion F)ˣ) (u_w : (w.val.adicCompletion F)ˣ),
        uniformizerNorm(F, S, v, uᵥ) → uniformizerNorm(F, S, w, u_w) →
        ∀ (tᵥ t_w : ℝ), phase(F, S, χ, v, uᵥ, tᵥ) → phase(F, S, χ, w, u_w, t_w) →
          ∀ c : QuasiCharacter Jₛ, (∃ s, c = chart(F, S, χ) s) →
            v ∈ sLocalFinitePolePlaces (F := F) (S := S) c →
            w ∈ sLocalFinitePolePlaces (F := F) (S := S) c →
            ∃! n : ℤ, tᵥ - t_w = (n : ℝ) * (2 * Real.pi / Real.log (p.asIdeal.absNorm : ℝ))

/-- Paper: Discussion after (7.3.1.11), p. 344.
Take F = ℚ(∛2), p = 5, and S consisting of the places over 5 together with the archimedean
places. Modulo 5, X³ - 2 factors as (X - 3)(X² + 3X + 4), with irreducible quadratic
and discriminant of X³ - 2 prime to 5. The local residue sizes are 5 and 25.
With T = 2π/log 5 and χ = |·|^(3iT/4), take the common pole c = 1.
The local phases are 3T/4 and T/4, so their difference is T/2. -/
theorem Printed.sLocalOrbitalPhase_sub_false : ¬ Printed.sLocalOrbitalPhase_sub := by sorry

/-- At the trivial quasi-character every restricted finite Tate factor has a pole at `0`. -/
private theorem sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_order_neg
    {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))} (v : S) :
    meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v
      (quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous (1 : QuasiCharacter (SIdeleQuotient F S))
        z))) 0 < 0 := by
  have h1 : (1 : QuasiCharacter (SIdeleQuotient F S)) =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
        (1 : PontryaginDual (SIdeleQuotient F S)) := by
    ext x
    change (1 : ℂ) = (((1 : PontryaginDual (SIdeleQuotient F S)) x : Circle) : ℂ)
    rw [PontryaginDual.one_apply, Circle.coe_one]
  have hv : v ∈ sLocalFinitePolePlaces (1 : QuasiCharacter (SIdeleQuotient F S)) := by
    rw [(sLocalPolePlaces_one (F := F) (S := S)).2]
    exact Finset.mem_univ v
  have hv' := (Finset.mem_filter.mp hv).2
  rw [h1] at hv' ⊢
  exact (sLocalRhoPoleOrder_eq_card_polePlaces_finite _ v 0).mp hv'

/-- Over `ℚ` the place below a finite place is the place itself. -/
private theorem sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_under
    (w : HeightOneSpectrum (𝓞 ℚ)) : w.under (𝓞 ℚ) = w := by
  ext x
  change x ∈ Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 ℚ)) w.asIdeal ↔ x ∈ w.asIdeal
  rw [Algebra.algebraMap_self, Ideal.comap_id]

/-- The `S`-integers of `ℚ` have trivial Picard group. -/
private theorem sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_pic
    (S : Set (HeightOneSpectrum (𝓞 ℚ))) : Subsingleton (CommRing.Pic (S.integer ℚ)) := by
  have hpid : IsPrincipalIdealRing (𝓞 ℚ) :=
    NumberField.classNumber_eq_one_iff.mp Rat.classNumber_eq
  have : Subsingleton (ClassGroup (𝓞 ℚ)) := inferInstance
  have : Fact (IsMulTorsion (ClassGroup (𝓞 ℚ))) :=
    ⟨fun x ↦ by rw [Subsingleton.elim x 1]; exact IsOfFinOrder.one⟩
  have : UniqueFactorizationMonoid (S.integer ℚ) :=
    UniqueFactorizationMonoid.of_isLocalization (Localization.submonoid S) _
  let : GCDMonoid (S.integer ℚ) := UniqueFactorizationMonoid.toGCDMonoid _
  infer_instance

open Classical in
/-- Paper: Definition 7.3.1.4, equations (7.3.1.6)–(7.3.1.7), p. 343.
As printed: on the primary pole locus, the natural-number count of contributing
places equals the sum of the signed meromorphic orders of the restricted local
Tate factors. See `sLocalPrimaryPoleMultiplicity` and ERRATA F119. -/
def Printed.sLocalPrimaryPoleMultiplicity_eq_sum_orders : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (p : HeightOneSpectrum (𝓞 ℚ)),
    IsSaturatedPlaceSet S → (sLocalPrimaryPlaces S p).Nonempty →
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    ∀ c : QuasiCharacter (SIdeleQuotient F S),
      0 < sLocalPrimaryPoleMultiplicity p c →
      let twist := quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous c
      ((sLocalPrimaryPoleMultiplicity p c : ℤ) : WithTop ℤ) =
        ∑ v ∈ S.attach.filter (fun v ↦ v.val ∈ sLocalPrimaryPlaces S p),
          meromorphicOrderAt
            (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (twist z))) 0

open Classical in
/-- Paper: Definition 7.3.1.4, equations (7.3.1.6)–(7.3.1.7), p. 343.
Take F = ℚ, S with just the finite place over 2, p = 2, and c = 1.
The local numerator has a simple pole and the reflected denominator is
regular and nonzero at c, giving signed order −1. The primary count is 1. -/
theorem Printed.sLocalPrimaryPoleMultiplicity_eq_sum_orders_false :
    ¬ Printed.sLocalPrimaryPoleMultiplicity_eq_sum_orders := by
  intro h
  let p : HeightOneSpectrum (𝓞 ℚ) :=
    Rat.HeightOneSpectrum.primesEquiv.symm ⟨2, Nat.prime_two⟩
  have hunder := sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_under
  have hP : sLocalPrimaryPlaces ({p} : Finset (HeightOneSpectrum (𝓞 ℚ))) p = {p} := by
    ext w
    rw [mem_sLocalPrimaryPlaces]
    exact ⟨And.left, fun hw ↦ ⟨hw, (hunder w).trans (Finset.mem_singleton.mp hw)⟩⟩
  have hsat : IsSaturatedPlaceSet ({p} : Finset (HeightOneSpectrum (𝓞 ℚ))) := by
    intro v w hv hw
    have hwv : w = v := (hunder w).symm.trans (hw.trans (hunder v))
    rwa [hwv]
  have hne : (sLocalPrimaryPlaces ({p} : Finset (HeightOneSpectrum (𝓞 ℚ))) p).Nonempty := by
    rw [hP]
    exact Finset.singleton_nonempty p
  have hmult : sLocalPrimaryPoleMultiplicity (S := {p}) p 1 = 1 := by
    rw [sLocalPrimaryPoleMultiplicity_one, hP, Finset.card_singleton]
  have H := h ℚ {p} p hsat hne
    (sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_pic _) 1 (by rw [hmult]; exact one_pos)
  dsimp only at H
  rw [hmult] at H
  have hle : (∑ v ∈ ({p} : Finset (HeightOneSpectrum (𝓞 ℚ))).attach.filter
      (fun v ↦ v.val ∈ sLocalPrimaryPlaces {p} p),
        meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v
          (quasiCharacterNormTwist (sIdeleQuotientNorm ℚ {p})
            (isProperMap_sIdeleQuotientNorm ℚ {p}).continuous 1 z))) 0) ≤ 0 :=
    Finset.sum_nonpos fun v _ ↦
      (sLocalPrimaryPoleMultiplicity_eq_sum_orders_false_order_neg v).le
  rw [← H] at hle
  have h0 : ((((1 : ℕ) : ℤ)) : WithTop ℤ) ≤ ((0 : ℤ) : WithTop ℤ) := hle
  exact absurd (WithTop.coe_le_coe.mp h0) (by norm_num)

end RiemannMasullo
