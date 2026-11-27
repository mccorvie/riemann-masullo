module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Archimedean supports of valuation-ball coefficients

At a rational stage with one finite place, the product Fourier support bounds the
archimedean support of each coefficient of a finite valuation-ball expansion.
The product region is that of Definition 7.3.2.3(1), pp. 354–355, used in (11.2.1.6), p. 488.
-/

public noncomputable section

open Function IsDedekindDomain NumberField Set Topology
open scoped NumberField.AdeleRing

namespace RiemannMasullo

/-- For a rational stage with one finite place, the archimedean coefficient of a ball
of radius `q⁻ʲ` in a finite expansion is supported in the interval of radius
`B qʲ` if the test has product support at most `B`. The difference of the
slices at a uniformizer to powers `j` and `j - 1` isolates the coefficient.
This applies to the Fourier transform of a test when the displayed expansion
is available for that transform. -/
theorem singletonProductBand_coefficient_tsupport
    (v : HeightOneSpectrum (𝓞 ℚ)) (B : ℝ) (hB : 0 ≤ B)
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ {v})))
    (hBand : tsupport f.val ⊆ Multiplicative.toAdd ⁻¹' sLocalPWProductRegion {v} B)
    (I : Finset ℤ) (a : ℤ → SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ)))
    (hExpand : ∀ x : SAdeleRing ℚ {v},
      f (Multiplicative.ofAdd x) = ∑ n ∈ I,
        if Valued.v (x.2 ⟨v, Finset.mem_singleton_self v⟩) ≤ WithZero.exp (-n) then
          a n (Multiplicative.ofAdd x.1) else 0)
    (j : ℤ) (hj : j ∈ I) :
    tsupport (a j).val ⊆
      {x | ‖x.toAdd Rat.infinitePlace‖ ≤ B * (v.asIdeal.absNorm : ℝ) ^ j} := by
  classical
  let w : ({v} : Finset (HeightOneSpectrum (𝓞 ℚ))) := ⟨v, Finset.mem_singleton_self v⟩
  let : Subsingleton ({v} : Finset (HeightOneSpectrum (𝓞 ℚ))) :=
    Finset.card_le_one_iff_subsingleton_coe.mp (by simp)
  let q : ℝ := v.asIdeal.absNorm
  have hq : 1 < q := by
    simpa only [q, Nat.one_lt_cast] using HeightOneSpectrum.one_lt_absNorm v
  have hq₀ : 0 < q := zero_lt_one.trans hq
  let K := v.adicCompletion ℚ
  let ν : Valuation K (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := ν.exists_isUniformizer_of_isCyclic_of_nontrivial
  have hπval : ν (π : K) = WithZero.exp (-1 : ℤ) :=
    hπ.trans (congrArg Units.val
      (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.valuedAdicCompletion_surjective ℚ)))
  let slice (n : ℤ) : (i : ({v} : Finset (HeightOneSpectrum (𝓞 ℚ)))) →
      i.val.adicCompletion ℚ := Pi.mulSingle w ((π : K) ^ n)
  have hslice (n : ℤ) : slice n w = (π : K) ^ n := Pi.mulSingle_eq_same w _
  have hVal (n : ℤ) : Valued.v (slice n w) = WithZero.exp (-n) := by
    rw [hslice]
    change ν ((π : K) ^ n) = _
    rw [map_zpow₀ ν, hπval, ← WithZero.exp_zsmul]
    simp
  have hNorm (n : ℤ) : ‖slice n w‖ = (q ^ n)⁻¹ := by
    rw [hslice, norm_zpow, norm_uniformizer_adicCompletion v (π : K) hπ, inv_zpow]
  have hClosed : IsClosed
      {x : Multiplicative (InfiniteAdeleRing ℚ) |
        ‖x.toAdd Rat.infinitePlace‖ ≤ B * q ^ j} :=
    isClosed_le ((continuous_apply Rat.infinitePlace).comp continuous_toAdd).norm continuous_const
  apply closure_minimal _ hClosed
  intro x hx
  change ‖x.toAdd Rat.infinitePlace‖ ≤ B * q ^ j
  by_contra! hOutside
  let pt (n : ℤ) : SAdeleRing ℚ {v} := (x.toAdd, slice n)
  have hZero (n : ℤ) (hn : n ≤ j) : f (Multiplicative.ofAdd (pt n)) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hy
    have hy' : (pt n) ∈ sLocalPWProductRegion {v} B := hBand hy
    change (∏ i : InfinitePlace ℚ, ‖x.toAdd i‖ ^ i.mult) *
      (∏ i : ({v} : Finset (HeightOneSpectrum (𝓞 ℚ))), ‖slice n i‖) ≤ B at hy'
    rw [Fintype.prod_subsingleton _ Rat.infinitePlace, Fintype.prod_subsingleton _ w,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one, hNorm] at hy'
    have hb : ‖x.toAdd Rat.infinitePlace‖ ≤ B * q ^ n :=
      (div_le_iff₀ (zpow_pos hq₀ n)).mp (by simpa only [div_eq_mul_inv] using hy')
    exact hOutside.not_ge
      (hb.trans (mul_le_mul_of_nonneg_left (zpow_le_zpow_right₀ hq.le hn) hB))
  have hRead (n : ℤ) : f (Multiplicative.ofAdd (pt n)) =
      ∑ k ∈ I, if k ≤ n then a k x else 0 := by
    rw [hExpand]
    apply Finset.sum_congr rfl
    intro k _
    change (if Valued.v (slice n w) ≤ WithZero.exp (-k) then a k x else 0) = _
    simp only [hVal, WithZero.exp_le_exp, neg_le_neg_iff]
  have hCoeff :
      (∑ k ∈ I, if k ≤ j then a k x else 0) -
        (∑ k ∈ I, if k ≤ j - 1 then a k x else 0) = a j x := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ∑ k ∈ I, if k = j then a k x else 0 := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hkj : k = j
        · subst k
          have hnot : ¬ j ≤ j - 1 := by omega
          simp [hnot]
        · have hiff : k ≤ j ↔ k ≤ j - 1 := by omega
          by_cases hk : k ≤ j
          · simp [hkj, hk, hiff.mp hk]
          · simp [hkj, hk, mt hiff.mpr hk]
      _ = a j x := by simp [hj]
  rw [← hRead j, ← hRead (j - 1), hZero j le_rfl, hZero (j - 1) (by omega), sub_zero] at hCoeff
  exact hx hCoeff.symm

end RiemannMasullo
