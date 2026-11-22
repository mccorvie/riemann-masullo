module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # Appendix A.3: the printed S-local measure equality -/

@[expose] public noncomputable section

namespace RiemannMasullo

open NumberField IsDedekindDomain

/-- Paper: Lemma A.3.1.3, second equality of (A.3.1.3), p. 556. As printed: for every
finite set of places S containing all infinite places, the additive measure of quotient
covolume one equals the product of the local Tamagawa measures over S. The finite set
parameter lists the finite places of S. `sAdditiveTamagawaMeasure_eq_covolumeOne` gives
the equality when S contains all ramified places. See ERRATA F10. -/
def Printed.sAdditiveTamagawaMeasure_eq_covolumeOne : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    sAdditiveCovolumeOneMeasure F S = sAdditiveTamagawaMeasure F S

private theorem t4644_finrank : 1 < Module.finrank ℚ (CyclotomicField 4 ℚ) := by
  have : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := 4) (K := ℚ)
  rw [IsCyclotomicExtension.Rat.finrank 4 (CyclotomicField 4 ℚ)]
  decide

private theorem t4644_exists_dvd (F : Type) [Field F] [NumberField F]
    (hF : 1 < Module.finrank ℚ F) :
    ∃ v : HeightOneSpectrum (𝓞 F), v.asIdeal ∣ differentIdeal ℤ (𝓞 F) := by
  have hdisc := NumberField.abs_discr_gt_two hF
  have hnorm := NumberField.absNorm_differentIdeal F (𝓞 F)
  have htop : differentIdeal ℤ (𝓞 F) ≠ ⊤ := by
    intro ht
    rw [ht, Ideal.absNorm_top] at hnorm
    have : |discr F| = 1 := by
      rw [Int.abs_eq_natAbs, ← hnorm]; rfl
    omega
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ htop
  have hbot : M ≠ ⊥ := fun hb ↦ differentIdeal_ne_bot (hb ▸ hle |> le_bot_iff.mp)
  exact ⟨⟨M, hM.isPrime, hbot⟩, Ideal.dvd_iff_le.mpr hle⟩

private theorem t4644_ne (F : Type) [Field F] [NumberField F] (v₀ : HeightOneSpectrum (𝓞 F))
    (hv₀ : v₀.asIdeal ∣ differentIdeal ℤ (𝓞 F))
    (h : sAdditiveCovolumeOneMeasure F ∅ = sAdditiveTamagawaMeasure F ∅) : False := by
  obtain ⟨c, -, hscale, hc⟩ := sAdditiveTamagawaMeasure_scale F ∅
  have hD := sAdditiveCovolumeOneMeasure_fundamentalDomain F ∅
  have hc1 : (c : ENNReal) = 1 := by
    have := congrArg (fun μ ↦ μ (sAdeleFundamentalDomain F ∅ (RingOfIntegers.basis F))) hscale
    rw [← h, hD, smul_apply, hD] at this
    simpa [ENNReal.smul_def] using this.symm
  let t : {v : HeightOneSpectrum (𝓞 F) // v ∉ (∅ : Finset _)} → ENNReal := fun v ↦
    ENNReal.ofReal √((Ideal.absNorm v.val.asIdeal : ℝ) ^
      multiplicity v.val.asIdeal (differentIdeal ℤ (𝓞 F)))
  have hct : (c : ENNReal) = ∏ᶠ v, t v := by
    rw [hc]; simp only [inv_inv, t]
  have hfin : (Function.mulSupport t).Finite := by
    refine ((finiteLocalTamagawaMass_finite F).preimage
      (f := fun v : {v : HeightOneSpectrum (𝓞 F) // v ∉ (∅ : Finset _)} ↦ v.val)
      Subtype.val_injective.injOn).subset ?_
    intro v hv
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    intro h1
    exact hv (by simpa [t] using congrArg Inv.inv h1)
  have hone : ∀ v, 1 ≤ t v := by
    intro v
    simp only [t, ENNReal.one_le_ofReal, Real.one_le_sqrt]
    apply one_le_pow₀
    exact_mod_cast (HeightOneSpectrum.one_lt_absNorm v.val).le
  let w₀ : {v : HeightOneSpectrum (𝓞 F) // v ∉ (∅ : Finset _)} := ⟨v₀, by simp⟩
  have hlt : 1 < t w₀ := by
    simp only [t, w₀, ENNReal.one_lt_ofReal]
    rw [Real.lt_sqrt zero_le_one, one_pow]
    apply one_lt_pow₀
    · exact_mod_cast HeightOneSpectrum.one_lt_absNorm v₀
    · exact (multiplicity_pos_of_dvd hv₀ (Ideal.finiteMultiplicity
        (Ideal.IsPrime.ne_top v₀.isPrime) differentIdeal_ne_bot)).ne'
  rw [finprod_eq_prod_of_mulSupport_subset t (s := hfin.toFinset) (by simp)] at hct
  have hmem : w₀ ∈ hfin.toFinset := by simpa using hlt.ne'
  have := hlt.trans_le (Finset.single_le_prod (fun v _ ↦ hone v) hmem)
  rw [← hct, hc1] at this
  exact lt_irrefl _ this

/-- Paper: Lemma A.3.1.3, second equality of (A.3.1.3), p. 556. For F = ℚ(i) and
no finite places in S, the diagonal lattice is ℤ[i] in ℂ. Its fundamental square
`[0, 1) × [0, 1)` has mass one for the covolume-one measure and mass two for the complex
Tamagawa measure `2 dx dy`. -/
theorem Printed.sAdditiveTamagawaMeasure_eq_covolumeOne_false :
    ¬ Printed.sAdditiveTamagawaMeasure_eq_covolumeOne := by
  intro h
  obtain ⟨v₀, hv₀⟩ := t4644_exists_dvd (CyclotomicField 4 ℚ) t4644_finrank
  exact t4644_ne (CyclotomicField 4 ℚ) v₀ hv₀ (h _ ∅)

end RiemannMasullo
