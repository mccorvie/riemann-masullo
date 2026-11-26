module
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineQuarticGram
public import RiemannMasullo.ForMathlib.Analysis.Normed.Operator.FiniteRankClosedSpan

@[expose] public noncomputable section
open Set Function
namespace RiemannMasullo

private def windowExpBasis (b : ℝ → ℂ) (i : Fin 2 × Fin 2) (t : ℝ) : ℂ :=
  b t * (t : ℂ) ^ i.2.val * (Real.exp (if i.1 = 0 then -t else t) : ℂ)

private def quarticProfile (n : ℕ) (t : ℝ) : ℂ :=
  (if n = 0 then ((1 + |t| : ℝ) : ℂ) else Complex.I * t) * (Real.exp (-|t|) : ℂ)

private theorem quarticWindow_profile_mem_span (b : ℝ → ℂ) {l r z : ℝ}
    (hsupp : ∀ t, b t ≠ 0 → t ∈ Ioo l r) (hz : z ∉ Ioo l r) (n : ℕ) :
    (fun t ↦ b t * quarticProfile n (t - z)) ∈
      Submodule.span ℂ (range (windowExpBasis b)) := by
  classical
  let W := Submodule.span ℂ (range (windowExpBasis b))
  have hb (i : Fin 2 × Fin 2) : windowExpBasis b i ∈ W := Submodule.subset_span (mem_range_self i)
  by_cases hleft : z ≤ l
  · let c : ℂ := if n = 0 then (1 - z : ℝ) else -Complex.I * z
    let d : ℂ := if n = 0 then 1 else Complex.I
    have he : (fun t ↦ b t * quarticProfile n (t - z)) =
        (Real.exp z : ℂ) • (c • windowExpBasis b (0, 0) + d • windowExpBasis b (0, 1)) := by
      funext t
      by_cases ht : b t = 0
      · simp [quarticProfile, windowExpBasis, ht]
      · have ht' : 0 ≤ t - z := by linarith [(hsupp t ht).1]
        simp only [quarticProfile, abs_of_nonneg ht', Pi.smul_apply, Pi.add_apply,
          windowExpBasis, Fin.val_zero, Fin.val_one, pow_zero, pow_one, ite_true, smul_eq_mul]
        rw [show -(t - z) = z + -t by ring, Real.exp_add, Complex.ofReal_mul]
        dsimp [c, d]
        split_ifs <;> push_cast <;> ring
    rw [he]
    exact W.smul_mem _ (W.add_mem (W.smul_mem _ (hb (0, 0))) (W.smul_mem _ (hb (0, 1))))
  · have hright : r ≤ z := by
      by_contra h
      exact hz ⟨lt_of_not_ge hleft, lt_of_not_ge h⟩
    let c : ℂ := if n = 0 then (1 + z : ℝ) else -Complex.I * z
    let d : ℂ := if n = 0 then -1 else Complex.I
    have he : (fun t ↦ b t * quarticProfile n (t - z)) =
        (Real.exp (-z) : ℂ) • (c • windowExpBasis b (1, 0) + d • windowExpBasis b (1, 1)) := by
      funext t
      by_cases ht : b t = 0
      · simp [quarticProfile, windowExpBasis, ht]
      · have ht' : t - z ≤ 0 := by linarith [(hsupp t ht).2]
        simp only [quarticProfile, abs_of_nonpos ht', neg_neg, Pi.smul_apply, Pi.add_apply,
          windowExpBasis, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
          show (1 : Fin 2) ≠ 0 by decide, ite_false, smul_eq_mul]
        rw [show t - z = -z + t by ring, Real.exp_add, Complex.ofReal_mul]
        dsimp [c, d]
        split_ifs <;> push_cast <;> ring
    rw [he]
    exact W.smul_mem _ (W.add_mem (W.smul_mem _ (hb (1, 0))) (W.smul_mem _ (hb (1, 1))))

end RiemannMasullo

namespace RiemannMasullo.Isolated
open MeasureTheory NumberField
open scoped InnerProductSpace NNReal NumberField.AdeleRing
set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "Ω" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "ν𝔽" => canonicalModulatedHaar m𝔽 hm𝔽
local notation "W₄" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-0) 0 4
local notation "hI" => (show -(0 : ℝ) ≤ 0 by norm_num)
local notation "hs₀" => (show (0 : ℝ) ≤ 4 by norm_num)
local notation "hs₁" => (show (1 : ℝ) < 4 by norm_num)
local notation "T₄" => (modulatedIntervalSobolev_dual m𝔽 hm𝔽 μ𝔽 (-0) 0 4 hI hs₀).exists.choose
local notation "J(" χ ", " a ")" => SpectralStripJetIndex χ a 0 4
local notation "raw(" χ ", " j ")" => spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jetU(" χ ", " j ")" => (spectralStripJet_memLp χ (le_refl (0 : ℝ)) hs₀ j).toLp raw(χ, j)
local notation "Riesz(" v ")" => (InnerProductSpace.toDual ℂ W₄).symm ((T₄).symm (v))
local notation "E(" η ", " t ")" => fractionalLineWaveEval hs₁ η t
local notation "P(" a ")" => spectralProjection (F := F) a (le_refl (0 : ℝ)) hs₀

local instance quarticLineWindowCanonicalHaar : (ν𝔽).IsHaarMeasure :=
  (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1

/-- Paper: Theorem 10.4.3.5(3), pp. 472–473, and (12.5.1.4), p. 520.
At zero width and Sobolev order four, a bounded multiplier in one compact
frequency window has ambient spectral rank at most four plus the number of
retained jets inside that window. Nearby zeros require no separation.
Reconstruction: The exterior Riesz kernels lie in the span of four functions
`exp(t)`, `t exp(t)`, `exp(-t)`, `t exp(-t)`, each multiplied by the symbol.
This is the local-rank step of the frequency-window argument for the ambient kernel. -/
theorem spectralLineQuartic_window_rank_le
    (a : ℝ) (χ : Ω → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (A : W₄ →L[ℂ] W₄) (b : Ω → ℝ → ℂ) (ω : Ω) (l r : ℝ)
    (hA : ∀ ζ t u, E(χ ζ, t) (A u) = b ζ t * E(χ ζ, t) u)
    (hb : ∀ ζ t, b ζ t ≠ 0 → ζ = ω ∧ t ∈ Ioo l r)
    (K : Finset J(χ, a))
    (hK : ∀ j : J(χ, a), j.val.1 = ω → j.val.2.2.1 ∈ Ioo l r → j ∈ K) :
    FiniteDimensional ℂ (A.comp P(a)).toLinearMap.range ∧
      Module.finrank ℂ (A.comp P(a)).toLinearMap.range ≤ 4 + K.card := by
  classical
  let e : W₄ →ₗ[ℂ] (Ω × ℝ → ℂ) := LinearMap.pi fun p ↦ (E(χ p.1, p.2)).toLinearMap
  have he : Function.Injective e := by
    intro x y h
    apply sub_eq_zero.mp
    apply fractionalLineWaveEval_separates hs₁ χ hχ
    intro ζ t
    have hp := congrFun h (ζ, t)
    change E(χ ζ, t) x = E(χ ζ, t) y at hp
    rw [map_sub, hp, sub_self]
  let u (j : J(χ, a)) : W₄ := Riesz(jetU(χ, j))
  let L : (ℝ → ℂ) →ₗ[ℂ] (Ω × ℝ → ℂ) :=
    { toFun := fun f p ↦ if p.1 = ω then f p.2 else 0
      map_add' := fun f g ↦ by
        funext p
        by_cases hp : p.1 = ω <;> simp [hp]
      map_smul' := fun c f ↦ by
        funext p
        by_cases hp : p.1 = ω <;> simp [hp] }
  let q : (Fin 2 × Fin 2) ⊕ {j // j ∈ K} → (Ω × ℝ → ℂ) :=
    Sum.elim (fun i ↦ L (windowExpBasis (b ω) i)) (fun j ↦ e (A (u j.val)))
  let V := Submodule.span ℂ (range q)
  let : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (finite_range q)
  have hL : Submodule.span ℂ (range (windowExpBasis (b ω))) ≤ V.comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span (show L (windowExpBasis (b ω) i) ∈ range q from
      ⟨Sum.inl i, rfl⟩)
  have hmem (j : J(χ, a)) : e (A (u j)) ∈ V := by
    by_cases hjK : j ∈ K
    · exact Submodule.subset_span (show e (A (u j)) ∈ range q from
        ⟨Sum.inr ⟨j, hjK⟩, rfl⟩)
    by_cases hjω : j.val.1 = ω
    · have hz : j.val.2.2.1 ∉ Ioo l r := fun hz ↦ hjK (hK j hjω hz)
      let c : ℂ := ((Measure.haarScalarFactor μ𝔽 ν𝔽 : ℝ) * (Real.pi / 2) : ℂ)
      have hprofile (t : ℝ) : b ω t * E(χ ω, t) (u j) =
          c * (b ω t * quarticProfile j.val.2.2.2 (t - j.val.2.2.1)) := by
        by_cases ht : b ω t = 0
        · simp [ht]
        have htj : t ≠ j.val.2.2.1 := fun heq ↦ hz (heq ▸ (hb ω t ht).2)
        have hn := spectralLineQuarticJet_order_le_one χ j
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn with hzero | hone
        · have hv := spectralLineQuarticJet_riesz_observation_zero χ j hzero t
          change E(χ j.val.1, t) (u j) = _ at hv
          rw [hjω] at hv
          rw [hv]
          simp only [quarticProfile, hzero, ite_true, c, Complex.ofReal_mul]
          ring
        · have hv := spectralLineQuarticJet_riesz_observation_one χ j hone t htj
          change E(χ j.val.1, t) (u j) = _ at hv
          rw [hjω] at hv
          rw [hv]
          simp only [quarticProfile, hone, Nat.one_ne_zero, ite_false, c, Complex.ofReal_sub]
          ring
      have hshape : e (A (u j)) = c • L (fun t ↦ b ω t * quarticProfile j.val.2.2.2 (t - j.val.2.2.1)) := by
        funext p
        change E(χ p.1, p.2) (A (u j)) = c * (if p.1 = ω then _ else 0)
        rw [hA]
        by_cases hp : p.1 = ω
        · simpa only [hp, ite_true] using hprofile p.2
        · have hb0 : b p.1 p.2 = 0 := by
            by_contra hh
            exact hp (hb p.1 p.2 hh).1
          simp [hp, hb0]
      rw [hshape]
      exact V.smul_mem c (hL (quarticWindow_profile_mem_span (b ω)
        (fun t ht ↦ (hb ω t ht).2) hz j.val.2.2.2))
    · have hz : e (A (u j)) = 0 := by
        funext p
        change E(χ p.1, p.2) (A (u j)) = 0
        rw [hA]
        by_cases hp : b p.1 p.2 = 0
        · simp [hp]
        · have hω := (hb p.1 p.2 hp).1
          rw [hω]
          have hv := spectralLineQuarticJet_riesz_observation_zero_of_angular_ne χ hχ j ω
            (Ne.symm hjω) p.2
          change E(χ ω, p.2) (u j) = 0 at hv
          rw [hv, mul_zero]
      rw [hz]
      exact V.zero_mem
  obtain ⟨hfin, hdim⟩ := finrank_range_comp_le_of_closedSpan_images u P(a) A e he V
    (spectralLineQuartic_projection_mem_closedSpan a χ hχ) hmem
  refine ⟨hfin, hdim.trans ?_⟩
  have hd := finrank_range_le_card (R := ℂ) q
  simpa only [Set.finrank, V, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, Nat.reduceMul] using hd

/-- The retained order-four jets in a fixed character and compact frequency
window form a finite set. -/
theorem spectralLineQuartic_finite_jets_on_compact
    (a : ℝ) (χ : Ω → PontryaginDual C𝔽) (ω : Ω) (K : Set ℝ) (hK : IsCompact K) :
    {j : J(χ, a) | j.val.1 = ω ∧ j.val.2.2.1 ∈ K}.Finite := by
  let A (t : ℝ) := (a : ℂ) + (t : ℂ) * Complex.I
  let L := continuedCompletedHeckeL (χ ω)
  let Z := {t ∈ K | 0 < (meromorphicOrderAt L (A t)).untop₀.toNat}
  have hA : Continuous A := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hi : Injective A := fun x y h ↦ by
    simpa [A, Complex.add_im, Complex.mul_im] using congrArg Complex.im h
  have hL : MeromorphicOn L (A '' K) := fun z _ ↦
    (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn z (mem_univ z)
  have hZ : Z.Finite := by
    have hf := (MeromorphicOn.divisor L (A '' K)).finiteSupport (hK.image hA)
    apply (hf.preimage hi.injOn).subset
    rintro t ⟨ht, hpos⟩
    change MeromorphicOn.divisor L (A '' K) (A t) ≠ 0
    rw [hL.divisor_apply ⟨t, ht, rfl⟩]
    exact fun heq ↦ by rw [heq] at hpos; simp at hpos
  apply Set.Finite.of_injOn (f := fun j : J(χ, a) ↦ (j.val.2.2.1, j.val.2.2.2))
    (t := Z ×ˢ Iic 1) ?_ ?_ (hZ.prod (finite_Iic 1))
  · intro j hj
    refine ⟨⟨hj.2, ?_⟩, spectralLineQuarticJet_order_le_one χ j⟩
    have h := j.property
    rw [spectralStripMultiplicity_boundary (le_refl (0 : ℝ))
      (Or.inr (spectralLineQuarticJet_re_zero χ j))] at h
    have hn := ((lt_spectralBoundaryMultiplicity 4 _ _).mp h).1
    have hp := Nat.zero_lt_of_lt hn
    simpa only [spectralLineQuarticJet_re_zero χ j, add_zero, hj.1] using hp
  · intro j hj k hk h
    apply Subtype.ext
    apply Prod.ext (hj.1.trans hk.1.symm)
    apply Prod.ext ((spectralLineQuarticJet_re_zero χ j).trans
      (spectralLineQuarticJet_re_zero χ k).symm)
    exact h

/-- A bounded order-four multiplier supported in one compact frequency window
has finite rank after the ambient spectral projection. -/
theorem spectralLineQuartic_window_finiteRank
    (a : ℝ) (χ : Ω → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (A : W₄ →L[ℂ] W₄) (b : Ω → ℝ → ℂ) (ω : Ω) (l r : ℝ)
    (hA : ∀ ζ t u, E(χ ζ, t) (A u) = b ζ t * E(χ ζ, t) u)
    (hb : ∀ ζ t, b ζ t ≠ 0 → ζ = ω ∧ t ∈ Ioo l r) :
    FiniteDimensional ℂ (A.comp P(a)).toLinearMap.range ∧
      Module.finrank ℂ (A.comp P(a)).toLinearMap.range ≤
        4 + {j : J(χ, a) | j.val.1 = ω ∧ j.val.2.2.1 ∈ Icc l r}.ncard := by
  classical
  let S := {j : J(χ, a) | j.val.1 = ω ∧ j.val.2.2.1 ∈ Icc l r}
  have hS : S.Finite := spectralLineQuartic_finite_jets_on_compact a χ ω _ isCompact_Icc
  have h := spectralLineQuartic_window_rank_le a χ hχ A b ω l r hA hb hS.toFinset
    (fun j hj ht ↦ hS.mem_toFinset.mpr ⟨hj, ht.1.le, ht.2.le⟩)
  change _ ∧ _ ≤ 4 + S.ncard
  rw [Set.ncard_eq_toFinset_card S hS]
  exact h

end RiemannMasullo.Isolated
