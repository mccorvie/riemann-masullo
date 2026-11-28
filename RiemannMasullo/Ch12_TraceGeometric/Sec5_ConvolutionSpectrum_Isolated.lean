module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.Ch10_TraceSpectral.Sec2_Basepoint
import Mathlib.Analysis.Normed.Operator.Compact.FredholmAlternative
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The Mellin values in the spectrum of a compact convolution

Masullo computes the point spectrum on p. 453 and applies the same argument to the strip
on p. 454. Here the first nonzero jet of an eigenvector identifies its eigenvalue. The
last biorthogonal vector in each finite jet block gives an eigenvector in the other direction.

For Theorem 12.5.1.1 on pp. 519–520, the spectra of the unitary modulations of a single even
radial bump detect the exterior sites. At all widths the remaining estimate is that every
spectral value of these compact convolutions has modulus at most the Haar integral of the
absolute value of the test. The known critical strip gives the unconditional factor
`cosh (3 / 4)` for this bound. No module imports this reconstruction.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

private theorem eigenvalue_iff_block_value {V Z J : Type*} [NormedAddCommGroup V]
    [NormedSpace ℂ V] (N : Z → ℕ) (e : ((z : Z) × Fin (N z)) ≃ J)
    (x : J → V) (f : J → StrongDual ℂ V) (hb : IsSpectralMarkushevichBasis x f)
    (A : V →L[ℂ] V) (d : Z → ℂ)
    (hflag : ∀ z m v, (∀ k < m, f (e ⟨z, k⟩) v = 0) →
      f (e ⟨z, m⟩) (A v) = d z * f (e ⟨z, m⟩) v) (v₀ : ℂ) :
    Module.End.HasEigenvalue A.toLinearMap v₀ ↔ ∃ z, 0 < N z ∧ v₀ = d z := by
  classical
  have separate {v w : V} (h : ∀ z m, f (e ⟨z, m⟩) v = f (e ⟨z, m⟩) w) : v = w := by
    have he : ContinuousLinearMap.apply ℂ ℂ v = ContinuousLinearMap.apply ℂ ℂ w := by
      apply ContinuousLinearMap.ext_on hb.2.2.2
      rintro _ ⟨j, rfl⟩
      obtain ⟨⟨z, m⟩, rfl⟩ := e.surjective j
      exact h z m
    exact (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr fun L ↦ DFunLike.congr_fun he L
  constructor
  · intro heig
    obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
    obtain ⟨z, k, hk⟩ : ∃ z k, f (e ⟨z, k⟩) v ≠ 0 := by
      by_contra! h
      exact hv.2 (separate fun z m ↦ (h z m).trans (map_zero _).symm)
    let S := Finset.univ.filter fun m : Fin (N z) ↦ f (e ⟨z, m⟩) v ≠ 0
    have hS : S.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩⟩
    let m := S.min' hS
    have hm := (Finset.mem_filter.mp (S.min'_mem hS)).2
    have hlow (i : Fin (N z)) (hi : i < m) : f (e ⟨z, i⟩) v = 0 := by
      by_contra hn
      exact hi.not_ge (S.min'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hn⟩))
    have h := hflag z m v hlow
    rw [show A v = v₀ • v from hv.apply_eq_smul, map_smul, smul_eq_mul] at h
    exact ⟨z, k.pos, mul_right_cancel₀ hm h⟩
  · rintro ⟨z, hz, rfl⟩
    let top : Fin (N z) := ⟨N z - 1, by omega⟩
    let j := e ⟨z, top⟩
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := x j) ⟨?_, ?_⟩
    · apply Module.End.mem_eigenspace_iff.mpr
      apply separate
      intro w m
      have hlow (k : Fin (N w)) (hk : k < m) : f (e ⟨w, k⟩) (x j) = 0 := by
        apply hb.2.1
        intro h
        have hz' : z = w := congrArg Sigma.fst (e.injective h)
        subst w
        have he : top = k := eq_of_heq (Sigma.mk.inj (e.injective h)).2
        have hkm : k.val < m.val := hk
        have ht : top.val = N z - 1 := rfl
        have := m.isLt
        rw [← he] at hkm
        omega
      change f (e ⟨w, m⟩) (A (x j)) = _
      rw [hflag w m _ hlow, map_smul, smul_eq_mul]
      by_cases hzw : z = w
      · rw [hzw]
      · have hn : j ≠ e ⟨w, m⟩ := fun h ↦ hzw (congrArg Sigma.fst (e.injective h))
        rw [hb.2.1 _ _ hn, mul_zero, mul_zero]
    · intro hv
      have h := hb.1 j
      rw [hv, map_zero] at h
      exact zero_ne_one h

variable {F : Type*} [Field F] [NumberField F]

local notation "G" => IdeleClassGroup (𝓞 F) F
local notation "G₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "ℓ" => logIdeleClassNorm F
local notation "modF" => (continuousIdeleClassNorm F : G →ₜ* ℝ≥0ˣ)
local notation "hmod" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation modF)
local notation "M(" φ ", " η ", " u ")" =>
  modulatedFourierMellin modF univ hmod μ𝔽 (φ : BruhatCompactSupport G).val (ideleClassNormTwist η u)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "Istrip(" h ")" => (neg_nonpos.mpr h |>.trans h)

section Spectrum

variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
  (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (hχ : IsSpectralBasepointChoice (F := F) χ)

local notation "sites" => {z : PontryaginDual G₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1))
    (shift(a + z.2.1, z.2.2))}
local notation "count(" z ")" => spectralStripMultiplicity α s (z).val.2.1
  (meromorphicOrderAt (continuedCompletedHeckeL (χ (z).val.1))
    (shift(a + (z).val.2.1, (z).val.2.2))).untop₀.toNat
local notation "A(" φ ")" => spectralConvolution (F := F) a (Istrip(hα)) hs φ

include hχ

/-- Paper: Theorem 10.3.2.1(2), pp. 453–454. The eigenvalues of a compactly supported test on
the strip quotient are precisely its Mellin values at sites with a surviving jet. The
description includes the eigenvalue zero when it occurs.
Deviation: This holds at every nonnegative Sobolev order, with the strict boundary cutoff. -/
theorem spectralConvolution_hasEigenvalue_iff (φ : BruhatCompactSupport G) (v₀ : ℂ) :
    Module.End.HasEigenvalue A(φ).toLinearMap v₀ ↔
      ∃ j : SpectralStripJetIndex χ a α s, v₀ = M(φ, χ j.val.1, shift(j.val.2.1, j.val.2.2.1)) := by
  classical
  let J := SpectralStripJetIndex χ a α s
  let e : ((z : sites) × Fin (count(z))) ≃ J :=
    ⟨fun ⟨z, m⟩ ↦ ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩,
      fun j ↦ ⟨⟨(j.val.1, j.val.2.1, j.val.2.2.1), j.mem_strip_order_pos hα⟩, ⟨_, j.property⟩⟩,
      fun _ ↦ rfl, fun _ ↦ rfl⟩
  obtain ⟨_, x, f, hb, hj⟩ := spectralStripMarkushevichBasis (a := a) χ hχ hα hs
  let d (z : sites) := M(φ, χ z.val.1, shift(z.val.2.1, z.val.2.2))
  have hflag (z : sites) (m : Fin (count(z))) (v) (hlow : ∀ k < m, f (e ⟨z, k⟩) v = 0) :
      f (e ⟨z, m⟩) (A(φ) v) = d z * f (e ⟨z, m⟩) v := by
    refine (exists_spectralStripKernelOperator_all_jet_coefficients a hα hs χ f hj φ z m v).trans ?_
    rw [Finset.sum_eq_single (Fin.last m.val)]
    · simp only [Fin.val_last, Nat.choose_self, Nat.cast_one, one_mul, Nat.sub_self,
        pow_zero, mul_one]
      simp [d, modulatedFourierMellin, relativeVerticalStrip, e]
    · intro i _ hi
      have him : i.val < m.val := lt_of_le_of_ne (Nat.le_of_lt_succ i.isLt)
        (fun he ↦ hi (Fin.ext he))
      exact mul_eq_zero_of_right _ (hlow ⟨i.val, him.trans m.isLt⟩ him)
    · simp
  rw [eigenvalue_iff_block_value _ e x f hb _ d hflag]
  constructor
  · rintro ⟨z, hz, he⟩
    exact ⟨e ⟨z, ⟨0, hz⟩⟩, he⟩
  · rintro ⟨j, he⟩
    obtain ⟨⟨z, m⟩, rfl⟩ := e.surjective j
    exact ⟨z, m.pos, he⟩

/-- Paper: Theorem 10.3.2.1(2), pp. 453–454. Away from zero the entire spectrum of the test
on the quotient consists of its Mellin values at the retained sites. -/
theorem spectralConvolution_mem_spectrum_iff (φ : BruhatCompactSupport G) {v₀ : ℂ} (hne : v₀ ≠ 0) :
    v₀ ∈ spectrum ℂ A(φ) ↔
      ∃ j : SpectralStripJetIndex χ a α s, v₀ = M(φ, χ j.val.1, shift(j.val.2.1, j.val.2.2.1)) := by
  let := instSpectralQuotientPolynormableSec3 (F := F) a (Istrip(hα)) hs
  have hn := spectralStripConvolution_nuclear_of_summable_clusterTraceNorms a hα hs φ
  have hc : IsCompactOperator A(φ) := ((mem_traceClassOperators_iff_isNuclearOperator _).mpr hn).1
  exact (hc.hasEigenvalue_iff_mem_spectrum hne).symm.trans
    (spectralConvolution_hasEigenvalue_iff a hα hs χ hχ φ v₀)

end Spectrum

local notation "spectralBump" =>
  (⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩ : ContDiffBump (1 : ℝ))

/-- A fixed smooth even profile in log norm, supported in the two closed intervals with
`1/2 ≤ |x| ≤ 3/2`. Its two bumps have value one at their respective centers. -/
def stripSpectralProfile (x : ℝ) : ℝ := spectralBump x + spectralBump (-x)

private theorem profile_smooth : ContDiff ℝ (∞) stripSpectralProfile :=
  (spectralBump).contDiff.add ((spectralBump).contDiff.comp contDiff_neg)

/-- The two radial bumps have compact support. -/
theorem stripSpectralProfile_hasCompactSupport : HasCompactSupport stripSpectralProfile :=
  (spectralBump).hasCompactSupport.add ((spectralBump).hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ))

private theorem profile_nonneg (x : ℝ) : 0 ≤ stripSpectralProfile x :=
  add_nonneg (spectralBump).nonneg (spectralBump).nonneg

private theorem profile_even (x : ℝ) : stripSpectralProfile (-x) = stripSpectralProfile x := by
  simp [stripSpectralProfile, add_comm]

private theorem profile_one_pos : 0 < stripSpectralProfile 1 := by
  have h : spectralBump 1 = 1 := (spectralBump).one_of_mem_closedBall (by
    simp [Metric.mem_closedBall])
  exact add_pos_of_pos_of_nonneg (h.symm ▸ zero_lt_one) (spectralBump).nonneg

private theorem log_norm_proper : IsProperMap (ℓ : G → ℝ) := by
  have h := ((Homeomorph.ofAdd (X := ℝ)).symm.isProperMap.comp
    positiveRealLogEquiv.toHomeomorph.isProperMap).comp (isProperMap_ideleClassNorm F)
  change IsProperMap (fun x : G ↦ (positiveRealLogEquiv (ideleClassNorm F x)).toAdd) at h
  simpa only [positiveRealLogEquiv_apply] using h

private theorem log_norm_one_attained : ∃ g : G, ℓ g = 1 := by
  let t := positiveRealLogEquiv.symm (Multiplicative.ofAdd (1 : ℝ))
  refine ⟨QuotientGroup.mk (canonicalIdeleNormSection F t), ?_⟩
  change Real.log ((ideleNorm F (canonicalIdeleNormSection F t)).val : ℝ) = 1
  rw [canonicalIdeleNormSection_rightInverse F t, ← positiveRealLogEquiv_apply]
  exact congrArg Multiplicative.toAdd (positiveRealLogEquiv.apply_symm_apply _)

private theorem real_profile_integrable (v : ℝ → ℝ) (hv : Continuous v) :
    Integrable (fun g : G ↦ stripSpectralProfile (ℓ g) * v (ℓ g)) μ𝔽 := by
  have hp := log_norm_proper (F := F)
  have hc : HasCompactSupport (fun g : G ↦ stripSpectralProfile (ℓ g)) :=
    HasCompactSupport.intro (hp.isCompact_preimage stripSpectralProfile_hasCompactSupport)
      fun _ h ↦ image_eq_zero_of_notMem_tsupport h
  exact ((profile_smooth.continuous.comp hp.continuous).mul (hv.comp hp.continuous)).integrable_of_hasCompactSupport
    hc.mul_right

/-- The radial Mellin mass at horizontal distance `b` on the full idele class group.
At zero this is the Haar `L¹` mass of each modulated test. -/
def stripSpectralThreshold (F : Type*) [Field F] [NumberField F] (b : ℝ) : ℝ :=
  ∫ g : IdeleClassGroup (𝓞 F) F, stripSpectralProfile (logIdeleClassNorm F g) *
    Real.cosh (b * logIdeleClassNorm F g) ∂ideleClassTamagawaMeasure F

/-- The threshold is positive at every offset. -/
theorem stripSpectralThreshold_pos (b : ℝ) : 0 < stripSpectralThreshold F b := by
  obtain ⟨g, hg⟩ := log_norm_one_attained (F := F)
  have hv : Continuous (fun x : ℝ ↦ Real.cosh (b * x)) := by fun_prop
  have hc := (log_norm_proper (F := F)).continuous
  apply integral_pos_of_integrable_nonneg_ne_zero (x := g)
    ((profile_smooth.continuous.comp hc).mul (hv.comp hc))
    (real_profile_integrable _ hv) (fun x ↦ mul_nonneg (profile_nonneg _) (Real.cosh_pos _).le)
  change stripSpectralProfile (ℓ g) * Real.cosh (b * ℓ g) ≠ 0
  rw [hg]
  exact mul_ne_zero profile_one_pos.ne' (Real.cosh_pos _).ne'

/-- The radial Mellin threshold increases strictly with distance from the central line. -/
theorem stripSpectralThreshold_strictMonoOn : StrictMonoOn (stripSpectralThreshold F) (Ici 0) := by
  intro u hu v hv huv
  have cu : Continuous (fun x : ℝ ↦ Real.cosh (u * x)) := by fun_prop
  have cv : Continuous (fun x : ℝ ↦ Real.cosh (v * x)) := by fun_prop
  have hc := (log_norm_proper (F := F)).continuous
  obtain ⟨g, hg⟩ := log_norm_one_attained (F := F)
  apply sub_pos.mp
  unfold stripSpectralThreshold
  rw [← integral_sub (real_profile_integrable _ cv) (real_profile_integrable _ cu)]
  apply integral_pos_of_integrable_nonneg_ne_zero (x := g)
    (((profile_smooth.continuous.comp hc).mul (cv.comp hc)).sub
      ((profile_smooth.continuous.comp hc).mul (cu.comp hc)))
    ((real_profile_integrable _ cv).sub (real_profile_integrable _ cu))
  · intro x
    apply sub_nonneg.mpr
    apply mul_le_mul_of_nonneg_left _ (profile_nonneg _)
    apply Real.cosh_le_cosh.mpr
    simp only [abs_mul, abs_of_nonneg (show 0 ≤ u from hu), abs_of_nonneg (show 0 ≤ v from hv)]
    exact mul_le_mul_of_nonneg_right huv.le (abs_nonneg _)
  · change stripSpectralProfile (ℓ g) * Real.cosh (v * ℓ g) -
        stripSpectralProfile (ℓ g) * Real.cosh (u * ℓ g) ≠ 0
    rw [hg, mul_one, mul_one]
    apply (sub_pos.mpr (mul_lt_mul_of_pos_left _ profile_one_pos)).ne'
    rw [Real.cosh_lt_cosh, abs_of_nonneg hu, abs_of_nonneg hv]
    exact huv

private theorem profile_window {x : ℝ} (hx : stripSpectralProfile x ≠ 0) :
    1 / 2 ≤ |x| ∧ |x| ≤ 3 / 2 := by
  have hside (y : ℝ) (hy : spectralBump y ≠ 0) : 1 / 2 ≤ |y| ∧ |y| ≤ 3 / 2 := by
    have hd : dist y 1 < (1 / 2 : ℝ) := lt_of_not_ge fun h ↦ hy ((spectralBump).zero_of_le_dist h)
    rw [Real.dist_eq, abs_lt] at hd
    rw [abs_of_nonneg (by linarith [hd.1] : 0 ≤ y)]
    constructor <;> linarith [hd.1, hd.2]
  by_cases hy : spectralBump x = 0
  · have hh : spectralBump (-x) ≠ 0 := by
      intro h
      apply hx
      change spectralBump x + spectralBump (-x) = 0
      rw [hy, h, add_zero]
    simpa only [abs_neg] using hside (-x) hh
  · exact hside x hy

/-- The radial support bounds the mass at offset `b` between `cosh (|b| / 2)` and
`cosh (3 * |b| / 2)` times the mass on the line. -/
theorem stripSpectralThreshold_cosh_bounds (b : ℝ) :
    Real.cosh (|b| / 2) * stripSpectralThreshold F 0 ≤ stripSpectralThreshold F b ∧
    stripSpectralThreshold F b ≤ Real.cosh (3 * |b| / 2) * stripSpectralThreshold F 0 := by
  have hpoint (x : ℝ) :
      Real.cosh (|b| / 2) * stripSpectralProfile x ≤ stripSpectralProfile x * Real.cosh (b * x) ∧
      stripSpectralProfile x * Real.cosh (b * x) ≤ Real.cosh (3 * |b| / 2) * stripSpectralProfile x := by
    by_cases h : stripSpectralProfile x = 0
    · simp [h]
    obtain ⟨hl, hr⟩ := profile_window h
    rw [mul_comm (Real.cosh (|b| / 2)), mul_comm (Real.cosh (3 * |b| / 2))]
    constructor
    · apply mul_le_mul_of_nonneg_left _ (profile_nonneg _)
      rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : 0 ≤ |b| / 2), abs_mul]
      linarith [mul_le_mul_of_nonneg_left hl (abs_nonneg b)]
    · apply mul_le_mul_of_nonneg_left _ (profile_nonneg _)
      rw [Real.cosh_le_cosh, abs_of_nonneg (by positivity : 0 ≤ 3 * |b| / 2), abs_mul]
      linarith [mul_le_mul_of_nonneg_left hr (abs_nonneg b)]
  have hmass : Integrable (fun g : G ↦ stripSpectralProfile (ℓ g)) μ𝔽 := by
    simpa only [mul_one] using real_profile_integrable (F := F) (fun _ : ℝ ↦ (1 : ℝ)) continuous_const
  have hb := real_profile_integrable (F := F) (fun x : ℝ ↦ Real.cosh (b * x)) (by fun_prop)
  unfold stripSpectralThreshold
  simp only [zero_mul, Real.cosh_zero, mul_one]
  constructor
  · rw [← integral_const_mul]
    exact integral_mono (hmass.const_mul _) hb fun g ↦ (hpoint (ℓ g)).1
  · rw [← integral_const_mul]
    exact integral_mono hb (hmass.const_mul _) fun g ↦ (hpoint (ℓ g)).2

private theorem profile_exp_integral (b : ℝ) :
    ∫ g : G, stripSpectralProfile (ℓ g) * Real.exp (b * ℓ g) ∂μ𝔽 = stripSpectralThreshold F |b| := by
  let f (g : G) := stripSpectralProfile (ℓ g) * Real.exp (b * ℓ g)
  let r (g : G) := stripSpectralProfile (ℓ g) * Real.exp (-(b * ℓ g))
  have hf : Integrable f μ𝔽 := real_profile_integrable (fun x : ℝ ↦ Real.exp (b * x)) (by fun_prop)
  have hr : Integrable r μ𝔽 := real_profile_integrable (fun x : ℝ ↦ Real.exp (-(b * x))) (by fun_prop)
  have he : (∫ g, r g ∂μ𝔽) = ∫ g, f g ∂μ𝔽 := by
    rw [← integral_inv_eq_self f μ𝔽]
    apply integral_congr_ae
    exact .of_forall fun g ↦ by
      have hi : ℓ g⁻¹ = -(ℓ g) := by simp [logIdeleClassNorm, Real.log_inv]
      simp [f, r, hi, profile_even]
  have hav : ∫ g, f g + r g ∂μ𝔽 = 2 * stripSpectralThreshold F |b| := by
    unfold stripSpectralThreshold
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun g ↦ by
      have hc : Real.cosh (|b| * ℓ g) = Real.cosh (b * ℓ g) := by
        rcases le_total 0 b with h | h
        · rw [abs_of_nonneg h]
        · rw [abs_of_nonpos h, neg_mul, Real.cosh_neg]
      dsimp only
      rw [hc, Real.cosh_eq]
      dsimp only [f, r]
      ring
  rw [integral_add hf hr, he] at hav
  change (∫ g, f g ∂μ𝔽) = _
  linarith

/-- Multiplication by a unitary log frequency preserves smoothness of the radial profile. -/
theorem stripSpectralProfile_modulated_contDiff (t : ℝ) :
    ContDiff ℝ (∞) (fun x : ℝ ↦
      (stripSpectralProfile x : ℂ) * Complex.exp (-(x * (t : ℂ) * Complex.I))) := by
  exact (Complex.ofRealCLM.contDiff.comp profile_smooth).mul
    (Complex.contDiff_exp.comp (((Complex.ofRealCLM.contDiff.mul contDiff_const).mul contDiff_const).neg))

/-- The fixed radial bump modulated by the inverse angular character and the negative frequency.
The support of the test is independent of the character, the frequency and the strip width. -/
def stripSpectralBumpTest (η : PontryaginDual G) (t : ℝ) : BruhatCompactSupport G :=
  (exists_characterNormTest (F := F) η⁻¹ _ (stripSpectralProfile_modulated_contDiff t)
    ((stripSpectralProfile_hasCompactSupport.comp_left Complex.ofReal_zero).mul_right)).choose

/-- The value of the modulated test on an idele class. -/
theorem stripSpectralBumpTest_apply (η : PontryaginDual G) (t : ℝ) (g : G) :
    (stripSpectralBumpTest η t).val g = (η⁻¹ g : ℂ) *
      ((stripSpectralProfile (ℓ g) : ℂ) * Complex.exp (-((ℓ g : ℂ) * t * Complex.I))) :=
  (exists_characterNormTest (F := F) η⁻¹ _ (stripSpectralProfile_modulated_contDiff t)
    ((stripSpectralProfile_hasCompactSupport.comp_left Complex.ofReal_zero).mul_right)).choose_spec g

private theorem twist_factor (χ : PontryaginDual G) (b t : ℝ) (g : G) :
    ideleClassNormTwist χ (shift(b, t)) g = (χ g : ℂ) *
      ((Real.exp (b * ℓ g) : ℝ) : ℂ) * Complex.exp ((ℓ g : ℂ) * t * Complex.I) := by
  let y : ℝ := ((ideleClassNorm F g).val : ℝ)
  have hy : 0 < y := NNReal.coe_pos.mpr (Units.zero_lt _)
  change (χ g : ℂ) * (y : ℂ) ^ (shift(b, t)) = _
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
    ← Complex.ofReal_log hy.le, Complex.ofReal_exp, Complex.ofReal_mul, mul_assoc,
    ← Complex.exp_add]
  congr 2
  ring

private theorem bump_mellin_le (η χ : PontryaginDual G) (v b t : ℝ) :
    ‖M(stripSpectralBumpTest η v, χ, shift(b, t))‖ ≤ stripSpectralThreshold F |b| := by
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  rw [← profile_exp_integral]
  apply integral_congr_ae
  exact .of_forall fun g ↦ by
    dsimp only
    rw [stripSpectralBumpTest_apply, twist_factor]
    simp [Complex.norm_exp, Complex.mul_re, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (profile_nonneg _)]

private theorem bump_mellin_self (χ : PontryaginDual G) (b t : ℝ) :
    M(stripSpectralBumpTest χ t, χ, shift(b, t)) = (stripSpectralThreshold F |b| : ℂ) := by
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  rw [← profile_exp_integral]
  refine (integral_congr_ae ?_).trans (integral_complex_ofReal (μ := μ𝔽)
    (f := fun g : G ↦ stripSpectralProfile (ℓ g) * Real.exp (b * ℓ g)))
  exact .of_forall fun g ↦ by
    dsimp only
    rw [stripSpectralBumpTest_apply, twist_factor, Complex.exp_neg, Complex.ofReal_mul]
    have hχ : ((χ⁻¹ g : Circle) : ℂ) * (χ g : ℂ) = 1 := by
      rw [show χ⁻¹ g = (χ g)⁻¹ from rfl, Circle.coe_inv, inv_mul_cancel₀ (Circle.coe_ne_zero _)]
    have he := inv_mul_cancel₀ (Complex.exp_ne_zero ((ℓ g : ℂ) * t * Complex.I))
    calc
      _ = (((χ⁻¹ g : Circle) : ℂ) * (χ g : ℂ)) *
          ((Complex.exp ((ℓ g : ℂ) * t * Complex.I))⁻¹ * Complex.exp ((ℓ g : ℂ) * t * Complex.I)) *
          ((stripSpectralProfile (ℓ g) : ℂ) * (Real.exp (b * ℓ g) : ℂ)) := by ring
      _ = _ := by rw [hχ, he, one_mul, one_mul]

section Detection

variable (a : ℝ) {γ s : ℝ} (hγ : 0 ≤ γ) (hs : 0 ≤ s)
  (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (hχ : IsSpectralBasepointChoice (F := F) χ)

include hχ

local notation "action(" φ ")" => spectralConvolution (F := F) a (Istrip(hγ)) hs φ

/-- Each retained site attains its radial Mellin mass as a positive eigenvalue upon matching
the unitary character and frequency of the fixed test to those of the site. -/
theorem stripSpectralBump_threshold_eigenvalue (j : SpectralStripJetIndex χ a γ s) :
    Module.End.HasEigenvalue
      (action(stripSpectralBumpTest (χ j.val.1) j.val.2.2.1)).toLinearMap
      (stripSpectralThreshold F |j.val.2.1| : ℂ) :=
  (spectralConvolution_hasEigenvalue_iff a hγ hs χ hχ _ _).mpr ⟨j, (bump_mellin_self ..).symm⟩

private theorem matched_threshold_mem_spectrum (j : SpectralStripJetIndex χ a γ s) :
    (stripSpectralThreshold F |j.val.2.1| : ℂ) ∈
      spectrum ℂ (action(stripSpectralBumpTest (χ j.val.1) j.val.2.2.1)) := by
  rw [ContinuousLinearMap.spectrum_eq]
  exact (stripSpectralBump_threshold_eigenvalue a hγ hs χ hχ j).mem_spectrum

/-- A spectral bound by a constant times the mass confines every retained zero quantitatively.
For a zero at offset `b` the constant must be at least `cosh (|b| / 2)`. -/
theorem stripSpectralBump_cosh_le_of_spectral_bound (C : ℝ)
    (hC : ∀ η : PontryaginDual G, ∀ t : ℝ, ∀ v ∈ spectrum ℂ (action(stripSpectralBumpTest η t)),
      ‖v‖ ≤ C * stripSpectralThreshold F 0) (j : SpectralStripJetIndex χ a γ s) :
    Real.cosh (|j.val.2.1| / 2) ≤ C := by
  have h := hC _ _ _ (matched_threshold_mem_spectrum a hγ hs χ hχ j)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (stripSpectralThreshold_pos _)] at h
  apply le_of_mul_le_mul_right _ (stripSpectralThreshold_pos (F := F) 0)
  exact le_trans (by simpa only [abs_abs] using (stripSpectralThreshold_cosh_bounds (F := F) |j.val.2.1|).1) h

/-- Paper: Theorem 12.5.1.1, pp. 519–520. All retained offsets lie in the open target strip
exactly when the spectra of all modulations of the fixed bump lie in the corresponding open
disk. A site on the edge gives an eigenvalue on the boundary circle.
Reconstruction: This uses the Mellin multipliers from pp. 453–454 to test strip confinement. -/
theorem stripSpectralBump_spectrum_iff (δ : ℝ) (hδ : 0 ≤ δ) :
    (∀ η : PontryaginDual G, ∀ t : ℝ, ∀ v ∈ spectrum ℂ (action(stripSpectralBumpTest η t)),
      ‖v‖ < stripSpectralThreshold F δ) ↔
    ∀ j : SpectralStripJetIndex χ a γ s, |j.val.2.1| < δ := by
  constructor
  · intro hall j
    have h := hall _ _ _ (matched_threshold_mem_spectrum a hγ hs χ hχ j)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (stripSpectralThreshold_pos _)] at h
    exact (stripSpectralThreshold_strictMonoOn (F := F)).lt_iff_lt (abs_nonneg _) hδ |>.mp h
  · intro hj η t v hv
    by_cases hzero : v = 0
    · simpa [hzero] using stripSpectralThreshold_pos (F := F) δ
    obtain ⟨j, rfl⟩ := (spectralConvolution_mem_spectrum_iff a hγ hs χ hχ _ hzero).mp hv
    exact (bump_mellin_le ..).trans_lt (stripSpectralThreshold_strictMonoOn (F := F) (abs_nonneg _) hδ (hj j))

end Detection

local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : G₁ →ₜ* G)
local notation "half" => (1 / 2 : ℝ)
local notation "wide" => (show 0 ≤ half by norm_num)
local notation "WTest(" φ ")" => spectralConvolution (F := F) half (Istrip(wide)) (le_refl (0 : ℝ)) φ
local notation "divAt(" ψ ", " u ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) ψ) univ u
local notation "exterior(" τ ", " δ ")" =>
  {p : {ψ : PontryaginDual G // ∀ t : ℝ≥0ˣ, ψ (τ t) = 1} × ℂ //
    0 < divAt(p.1.val, p.2) ∧ δ ≤ |p.2.re - half|}
local notation "term(" φ ", " z ")" => ((divAt((z).val.1.val, (z).val.2) : ℤ) : ℂ) *
  M(φ, (z).val.1.val, (z).val.2 - 1 / 2)

private theorem normalized_lift_eq (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual G₁ → PontryaginDual G) (hχ : IsSpectralBasepointChoice χ)
    (hn : ∀ ξ t, χ ξ (τ t) = 1) (ψ : PontryaginDual G) (hψ : ∀ t, ψ (τ t) = 1) :
    χ (ψ.comp restriction) = ψ := by
  let ξ := ψ.comp restriction
  ext g : 1
  let k := g / τ (ideleClassNorm F g)
  have hk : k ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (g / _) = 1
    rw [map_div, hτ, div_self']
  have h : χ ξ k = ψ k := DFunLike.congr_fun (hχ ξ) (⟨k, hk⟩ : G₁)
  change χ ξ g = ψ g
  simpa only [k, map_div, hn ξ (ideleClassNorm F g), hψ (ideleClassNorm F g), div_one] using h

private theorem wide_jets_iff_empty (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual G₁ → PontryaginDual G) (hχ : IsSpectralBasepointChoice χ)
    (hn : ∀ ξ t, χ ξ (τ t) = 1) (δ : ℝ) :
    (∀ j : SpectralStripJetIndex χ half half 0, |j.val.2.1| < δ) ↔
      IsEmpty exterior(τ, δ) := by
  have hwide := (hasSum_exteriorZeros_iff_isEmpty (F := F) τ hτ half).mp
    (fun φ _ ↦ traceFormula_exteriorZeros_of_half_le τ φ (le_refl half))
  constructor
  · intro hall
    constructor
    rintro ⟨⟨⟨ψ, hψ⟩, u⟩, hpos, hout⟩
    let ξ := ψ.comp restriction
    have hlift : χ ξ = ψ := normalized_lift_eq τ hτ χ hχ hn ψ hψ
    have hin : |u.re - half| < half := by
      by_contra! h
      exact hwide.false ⟨⟨⟨ψ, hψ⟩, u⟩, hpos, h⟩
    have hu : shift(half + (u.re - half), u.im) = u := by
      rw [show half + (u.re - half) = u.re by ring, Complex.re_add_im]
    have hj : 0 < spectralStripMultiplicity half 0 (u.re - half)
        (meromorphicOrderAt (continuedCompletedHeckeL (χ ξ))
          (shift(half + (u.re - half), u.im))).untop₀.toNat := by
      rw [spectralStripMultiplicity_interior (abs_lt.mp hin), hu, hlift]
      change 0 < divAt(ψ, u) at hpos
      rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec ψ).1.meromorphicOn (mem_univ _)] at hpos
      omega
    exact (hall ⟨(ξ, u.re - half, u.im, 0), hj⟩).not_ge hout
  · intro h j
    by_contra! hfar
    let u := shift(half + j.val.2.1, j.val.2.2.1)
    have hsurv := j.property
    have hnum : 0 < (meromorphicOrderAt (continuedCompletedHeckeL (χ j.val.1)) u).untop₀.toNat := by
      dsimp only [u]
      unfold spectralStripMultiplicity spectralBoundaryMultiplicity at hsurv
      split_ifs at hsurv <;> omega
    have hdiv : 0 < divAt(χ j.val.1, u) := by
      rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec _).1.meromorphicOn (mem_univ _)]
      omega
    apply h.false
    refine ⟨⟨⟨χ j.val.1, hn _⟩, u⟩, hdiv, ?_⟩
    simpa [u] using hfar

/-- Paper: Theorem 12.5.1.1, pp. 519–520. At a fixed positive target half-width, the omitted
zero sum vanishes for every admissible test if and only if all unitary modulations of one fixed
radial bump on the full order-zero theta quotient have spectrum in the stated open disk.
Reconstruction: This is an operator criterion for the missing comparison on p. 520. The bump
and the quotient are independent of the target width and of the norm section. -/
theorem exteriorZeros_iff_stripSpectralBump_spectrum (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ (ideleClassNorm F)) {δ : ℝ} (hδ : 0 < δ) :
    (∀ φ : BruhatCompactSupport G, (∀ g : G₁, φ.val g = 0) →
      HasSum (fun z : exterior(τ, δ) ↦ term(φ, z)) 0) ↔
      ∀ η : PontryaginDual G, ∀ t : ℝ, ∀ v ∈ spectrum ℂ (WTest(stripSpectralBumpTest η t)),
        ‖v‖ < stripSpectralThreshold F δ := by
  obtain ⟨χ, hχ, hn, _⟩ := exists_spectralBasepointChoice_of_normSection τ hτ
  exact (hasSum_exteriorZeros_iff_isEmpty τ hτ δ).trans
    ((wide_jets_iff_empty τ hτ χ hχ hn δ).symm.trans
      (stripSpectralBump_spectrum_iff half wide (le_refl 0) χ hχ δ hδ.le).symm)

/-- Each modulation has the same Haar `L¹` mass. It is the zero-offset threshold. -/
theorem stripSpectralBumpTest_integral_norm (η : PontryaginDual G) (t : ℝ) :
    (∫ g : G, ‖(stripSpectralBumpTest η t).val g‖ ∂μ𝔽) = stripSpectralThreshold F 0 := by
  unfold stripSpectralThreshold
  apply integral_congr_ae
  exact .of_forall fun g ↦ by
    dsimp only
    rw [stripSpectralBumpTest_apply]
    simp [Complex.norm_exp, Complex.mul_re, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (profile_nonneg _)]

/-- Unconditionally, every spectral value on the full order-zero quotient has modulus strictly
less than `cosh (3 / 4)` times the mass of the test. The exterior identity at all widths would
give constant one. -/
theorem stripSpectralBump_spectrum_lt_cosh_mul_mass (η : PontryaginDual G) (t : ℝ) {v : ℂ}
    (hv : v ∈ spectrum ℂ (WTest(stripSpectralBumpTest η t))) :
    ‖v‖ < Real.cosh (3 / 4) * ∫ g : G, ‖(stripSpectralBumpTest η t).val g‖ ∂μ𝔽 := by
  let q : IdeleGroup (𝓞 F) F →ₜ* G := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* G := q.comp ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleClassNorm F) := canonicalIdeleNormSection_rightInverse F
  have hh := (exteriorZeros_iff_stripSpectralBump_spectrum τ hτ (by norm_num : 0 < half)).mp
    (fun φ _ ↦ traceFormula_exteriorZeros_of_half_le τ φ (le_refl half)) η t v hv
  rw [stripSpectralBumpTest_integral_norm]
  apply hh.trans_le
  simpa only [abs_of_nonneg wide, show 3 * half / 2 = 3 / 4 by norm_num] using
    (stripSpectralThreshold_cosh_bounds (F := F) half).2

/-- Every probe vanishes on the norm-one classes, as required of the tests on p. 519. -/
theorem stripSpectralBumpTest_normOne (η : PontryaginDual G) (t : ℝ) (g : G₁) :
    (stripSpectralBumpTest η t).val g = 0 := by
  have h0 : (spectralBump) (0 : ℝ) = 0 := (spectralBump).zero_of_le_dist (by
    norm_num [Real.dist_eq])
  rw [stripSpectralBumpTest_apply]
  have hg : ℓ (g : G) = 0 := by simp [logIdeleClassNorm, MonoidHom.mem_ker.mp g.property]
  have hprofile : stripSpectralProfile 0 = 0 := by
    change spectralBump 0 + spectralBump (-(0 : ℝ)) = 0
    rw [neg_zero, h0, add_zero]
  simp [hg, hprofile]

/-- Paper: Theorem 12.5.1.1, pp. 519–520. The exterior cancellation at every positive width is
equivalent to the Haar `L¹` spectral bound for the modulations of one compact test on the
single order-zero quotient. The mass in the bound is independent of the modulation.
Reconstruction: The manuscript does not establish this estimate on the quotient. -/
theorem exteriorZeros_allWidths_iff_stripSpectralBump_mass (τ : ℝ≥0ˣ →ₜ* G)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    (∀ δ : ℝ, 0 < δ → ∀ φ : BruhatCompactSupport G, (∀ g : G₁, φ.val g = 0) →
      HasSum (fun z : exterior(τ, δ) ↦ term(φ, z)) 0) ↔
      ∀ η : PontryaginDual G, ∀ t : ℝ, ∀ v ∈ spectrum ℂ (WTest(stripSpectralBumpTest η t)),
        ‖v‖ ≤ ∫ g : G, ‖(stripSpectralBumpTest η t).val g‖ ∂μ𝔽 := by
  obtain ⟨χ, hχ, hn, _⟩ := exists_spectralBasepointChoice_of_normSection τ hτ
  constructor
  · intro hall η t v hv
    rw [stripSpectralBumpTest_integral_norm]
    by_cases hzero : v = 0
    · simpa [hzero] using (stripSpectralThreshold_pos (F := F) 0).le
    obtain ⟨j, rfl⟩ := (spectralConvolution_mem_spectrum_iff half wide (le_refl 0) χ hχ _ hzero).mp hv
    have hj : |j.val.2.1| = 0 := by
      by_contra h
      have hp := lt_of_le_of_ne (abs_nonneg j.val.2.1) (Ne.symm h)
      have hempty := (hasSum_exteriorZeros_iff_isEmpty τ hτ _).mp (hall _ hp)
      exact lt_irrefl _ ((wide_jets_iff_empty τ hτ χ hχ hn _).mpr hempty j)
    simpa only [hj] using bump_mellin_le η (χ j.val.1) t j.val.2.1 j.val.2.2.1
  · intro h δ hδ
    apply (exteriorZeros_iff_stripSpectralBump_spectrum τ hτ hδ).mpr
    intro η t v hv
    apply (h η t v hv).trans_lt
    rw [stripSpectralBumpTest_integral_norm]
    exact stripSpectralThreshold_strictMonoOn (F := F) (mem_Ici.mpr le_rfl) hδ.le hδ

end RiemannMasullo.Isolated
