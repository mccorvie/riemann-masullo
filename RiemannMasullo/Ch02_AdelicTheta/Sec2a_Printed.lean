module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.AppD_SchwartzBruhat.Sec1c

/-! # Chapter 2.2: the printed adelic Riemann–Roch identity -/

@[expose] public noncomputable section

namespace RiemannMasullo

open MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing

local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])

local instance printedCh02Sec2aAdeleMeasurableSpace (F : Type) [Field F] [NumberField F] :
    MeasurableSpace 𝔸[F] := borel _

/-- Paper: Theorem 2.2.3.2, p. 82. As printed: the adelic Riemann–Roch identity
holds for the Fourier transform using the character of Examples A.3.1.5, A.3.1.6,
A.3.1.8 and A.3.1.9. Negating the finite coordinates of the input to
`adeleStandardCharacter` restores the printed finite sign and keeps the real sign.
`adelicTheta_riemannRoch` uses the character with opposite signs. See ERRATA F13. -/
def Printed.adelicTheta_riemannRoch : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : ℬ[F]),
    ∃ fhat : ℬ[F],
      (∀ y : 𝔸[F], fhat (Multiplicative.ofAdd y) =
        tamagawaFourier (additiveTamagawaMeasure F)
          (fun a : 𝔸[F] ↦ adeleStandardCharacter F (a.1, -a.2))
          (fun x ↦ f (Multiplicative.ofAdd x)) y) ∧
      ∀ g : IdeleClassGroup (𝓞 F) F,
        let n : ℝ := (ideleClassNorm F g : ℝ≥0)
        let z := Multiplicative.ofAdd (0 : 𝔸[F])
        adelicTheta f g = n⁻¹ • adelicTheta fhat g⁻¹ + n⁻¹ • fhat z - f z

/-- A bump near the adele one sees just one point of the diagonal and misses its
finite-sign reflection altogether. -/
private theorem adelicTheta_riemannRoch_false_test (s : IdeleGroup (𝓞 ℚ) ℚ)
    (hs : s.val = (1, -1)) (hss : s.val * s.val = 1) :
    ∃ f : ℬ[ℚ], adelicTheta f 1 = 1 ∧ adelicTheta f (QuotientGroup.mk s) = 0 := by
  let d := algebraMap ℚ 𝔸[ℚ]
  let D := Set.range d
  obtain ⟨hinj, hclosed, hdisc, _⟩ := adele_additive_quotient.{0, 0} ℚ
  have hsD : s.val ∉ D := by
    rintro ⟨q, hq⟩
    rw [hs] at hq
    have hqinf : algebraMap ℚ (InfiniteAdeleRing ℚ) q = 1 := congrArg Prod.fst hq
    have hq1 := (algebraMap ℚ (InfiniteAdeleRing ℚ)).injective (hqinf.trans (map_one _).symm)
    subst q
    let v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
      Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
    have hv := congrArg (fun a : 𝔸[ℚ] ↦ a.2 v) hq
    change algebraMap ℚ (v.adicCompletion ℚ) 1 = -1 at hv
    apply (by norm_num : (1 : ℚ) ≠ -1)
    apply (algebraMap ℚ (v.adicCompletion ℚ)).injective
    simpa only [map_neg, map_one] using hv
  let U : Set 𝔸[ℚ] := ((D \ {1}) ∪ (fun x : 𝔸[ℚ] ↦ x * s.val) ⁻¹' D)ᶜ
  have hU : IsOpen U :=
    ((isClosed_of_subset_discrete_closed Set.sdiff_subset hdisc hclosed).union
      (hclosed.preimage (continuous_id.mul continuous_const))).isOpen_compl
  have h1U : (1 : 𝔸[ℚ]) ∈ U := by simpa [U] using hsD
  let : LocallyCompactSpace (Multiplicative 𝔸[ℚ]) := adeleGroupLocallyCompact ℚ
  let : T2Space (Multiplicative 𝔸[ℚ]) := adeleGroupT2 ℚ
  obtain ⟨f, -, hf, hf1⟩ := schwartzBruhat_exists_local_unit
    (U := (Multiplicative.toAdd : Multiplicative 𝔸[ℚ] → 𝔸[ℚ]) ⁻¹' U)
    hU (show Multiplicative.ofAdd (1 : 𝔸[ℚ]) ∈ _ from h1U)
  have hz (x : 𝔸[ℚ]) (hx : x ∉ U) : f (Multiplicative.ofAdd x) = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hx (hf h)
  refine ⟨f, ?_, ?_⟩
  · rw [← QuotientGroup.mk_one (N := IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ), adelicTheta_mk]
    simp only [Units.val_one, mul_one]
    rw [tsum_eq_single (1 : ℚˣ)]
    · simpa only [Units.val_one, map_one, Pi.one_apply] using hf1.self_of_nhds
    · intro q hq
      apply hz
      exact fun h ↦ h (Or.inl ⟨⟨q.val, rfl⟩, fun he ↦
        hq (Units.ext (hinj (he.trans (map_one d).symm)))⟩)
  · rw [adelicTheta_mk]
    refine (tsum_congr (g := fun _ ↦ (0 : ℂ)) ?_).trans tsum_zero
    intro q
    apply hz
    refine fun h ↦ h (Or.inr ⟨q.val, ?_⟩)
    change d q.val = d q.val * s.val * s.val
    rw [mul_assoc, hss, mul_one]

/-- Paper: Theorem 2.2.3.2, p. 82. Over ℚ, take g = 1 and let f be a real smooth
bump supported in `(1/2, 3/2)` with f∞(1) = 1, times `1_{1+3ℤ₃}` at 3 and `1_{ℤₚ}`
elsewhere. Including the zero terms, the left side sums f∞ over the integers congruent
to 1 modulo 3 and gives 1. The printed Fourier sum equals the sum of the corrected
Fourier transform of f with its finite inputs negated. By Poisson summation for the
corrected character, this sums f∞ over integers congruent to −1 modulo 3 and gives 0. -/
theorem Printed.adelicTheta_riemannRoch_false : ¬ Printed.adelicTheta_riemannRoch := by
  intro h
  let r : 𝔸[ℚ] := (1, -1)
  have hrr : r * r = 1 := by
    change ((1 * 1, (-1) * (-1)) : 𝔸[ℚ]) = (1, 1)
    simp
  let s : IdeleGroup (𝓞 ℚ) ℚ := ⟨r, r, hrr, hrr⟩
  let c : IdeleClassGroup (𝓞 ℚ) ℚ := QuotientGroup.mk s
  have hc : c⁻¹ = c := rfl
  have hn : ((ideleClassNorm ℚ c : ℝ≥0) : ℝ) = 1 := by
    change ((ideleNorm ℚ s : ℝ≥0) : ℝ) = 1
    rw [((ideleNorm_spec ℚ).1 s).2]
    change (∏ v : InfinitePlace ℚ, ‖(1 : v.Completion)‖ ^ v.mult) *
      (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ‖(-1 : v.adicCompletion ℚ)‖) = 1
    simp
  obtain ⟨f, h1, hs⟩ := adelicTheta_riemannRoch_false_test s rfl hrr
  obtain ⟨fhat, hhat, hprinted⟩ := h ℚ f
  have hfreq (y : 𝔸[ℚ]) :
      fhat (Multiplicative.ofAdd y) = adeleSchwartzFourier f (Multiplicative.ofAdd (y * r)) := by
    rw [hhat]
    apply integral_congr_ae
    filter_upwards with x
    have hxy : ((x * y).1, -(x * y).2) = x * (y * r) := by
      change (x.1 * y.1, -(x.2 * y.2)) = (x.1 * (y.1 * 1), x.2 * (y.2 * -1))
      simp
    simp only [hxy, toAdd_ofAdd]
  have htheta : adelicTheta fhat 1 = adelicTheta (adeleSchwartzFourier f) c := by
    rw [← QuotientGroup.mk_one (N := IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ), adelicTheta_mk,
      show c = QuotientGroup.mk s from rfl, adelicTheta_mk]
    simp only [Units.val_one, mul_one]
    exact tsum_congr fun q ↦ hfreq _
  have hzero := hfreq 0
  rw [zero_mul] at hzero
  have hp := hprinted 1
  have ht := RiemannMasullo.adelicTheta_riemannRoch f c
  simp only [map_one, Units.val_one, NNReal.coe_one, inv_one, one_smul, h1, htheta, hzero] at hp
  change adelicTheta f c = 0 at hs
  simp only [hn, inv_one, one_smul, hc, hs] at ht
  exact one_ne_zero (hp.trans ht.symm)

end RiemannMasullo
