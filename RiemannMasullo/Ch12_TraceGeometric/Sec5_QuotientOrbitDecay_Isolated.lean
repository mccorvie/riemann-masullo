module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec2_Basepoint
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch09_HardySobolev.Sec2
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # One-sided translation in the order-zero theta quotient

Finite jet support in the critical strip gives dense families of representatives with
decaying rescaled translates whenever every admitted real offset is below the target.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "half" => (1 / 2 : ℝ)
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-half) half 0
local notation "hI" => (show -half ≤ half by norm_num)
local notation "hH" => (show 0 ≤ half by norm_num)
local notation "Θ" => globalThetaSobolev F half hI (le_refl (0 : ℝ))
local notation "T" => hardySobolevTranslation μ𝔽 m𝔽 (-half) half 0 hI (le_refl (0 : ℝ))

local notation "Basepoints" => PontryaginDual C₁ → PontryaginDual C𝔽

local notation "J(" χ ")" => SpectralStripJetIndex (F := F) χ half half 0
local notation "raw(" χ ", " j ")" =>
  spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "jetLp(" χ ", " j ")" =>
  (spectralStripJet_memLp (F := F) (a := half) (α := half) (s := 0) χ hH (le_refl 0) j).toLp (raw(χ, j))
local notation "dualIso" => (modulatedIntervalSobolev_dual m𝔽
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽 (-half) half 0 hI (le_refl 0)).exists.choose

private def jetMoment (χ : Basepoints) (j : J(χ)) : W →L[ℂ] ℂ := (dualIso).symm (jetLp(χ, j))

private theorem jetMoment_pairing (χ : Basepoints) (j : J(χ)) (x : W) :
    jetMoment χ j x = spectralSobolevPairing (F := F) x (jetLp(χ, j)) :=
  (spectralSobolevPairing_dual (F := F) hI (le_refl 0) (jetMoment χ j) x).2.trans
    (congrArg (spectralSobolevPairing (F := F) x) ((dualIso).apply_symm_apply _))

private theorem jetMoment_integral (χ : Basepoints) (j : J(χ)) (x : W) :
    Integrable (fun y ↦ x y * raw(χ, j) y) μ𝔽 ∧ jetMoment χ j x = ∫ y, x y * raw(χ, j) y ∂μ𝔽 := by
  let w (g : C𝔽) := intervalSobolevDensity (-half) half 0 (logIdeleClassNorm F g)
  have hw : Measurable w := by
    have hD : Continuous (intervalSobolevDensity (-half) half 0) := by unfold intervalSobolevDensity; fun_prop
    exact hD.measurable.comp ((NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)).measurable.log)
  have hac : μ𝔽 ≪ (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹) := by
    refine withDensity_absolutelyContinuous' hw.inv.ennreal_ofReal.aemeasurable (.of_forall fun g ↦ ?_)
    exact ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr
      (mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)))
  have hae : (jetLp(χ, j) : C𝔽 → ℂ) =ᵐ[μ𝔽] raw(χ, j) := hac.ae_le (MemLp.coeFn_toLp _)
  have he := spectralSobolevPairing_dual (F := F) hI (le_refl 0) (jetMoment χ j) x
  change Integrable (fun y ↦ x y * (dualIso ((dualIso).symm (jetLp(χ, j)))) y) μ𝔽 ∧
    jetMoment χ j x = spectralSobolevPairing (F := F) x (dualIso ((dualIso).symm (jetLp(χ, j)))) at he
  rw [(dualIso).apply_symm_apply] at he
  have hh := hae.mono fun y hy ↦ congrArg (x y * ·) hy
  exact ⟨he.1.congr hh, he.2.trans (integral_congr_ae hh)⟩

private abbrev blockLength (χ : Basepoints) (j : J(χ)) : ℕ :=
  spectralStripMultiplicity half 0 j.val.2.1
    (meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ j.val.1))
      (((half + j.val.2.1 : ℝ) : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I)).untop₀.toNat

private def atOrder (χ : Basepoints) (j : J(χ)) (i : Fin (blockLength χ j)) : J(χ) :=
  ⟨(j.val.1, j.val.2.1, j.val.2.2.1, i.val), i.isLt⟩

private abbrev lowerJet (χ : Basepoints) (j : J(χ)) (i : Fin (j.val.2.2.2 + 1)) : J(χ) :=
  atOrder χ j ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt j.property⟩

private theorem jetMoment_translate (χ : Basepoints) (j : J(χ)) (g : C𝔽) (x : W) :
    jetMoment χ j (T g x) = ∑ i : Fin (j.val.2.2.2 + 1),
      (ideleClassNormTwist (χ j.val.1) ((j.val.2.1 : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I) g *
        (logIdeleClassNorm F g : ℂ) ^ (j.val.2.2.2 - i.val) * (j.val.2.2.2.choose i.val : ℂ)) *
          jetMoment χ (lowerJet χ j i) x := by
  have hint (i : ℕ) (hi : i ≤ j.val.2.2.2) : Integrable
      (fun y ↦ x y * spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 i y) μ𝔽 :=
    (jetMoment_integral χ (atOrder χ j ⟨i, hi.trans_lt j.property⟩) x).1
  have h := stripJet_all_translated_moments (F := F) (α := half) (s := 0) (χ j.val.1)
    j.val.2.1 j.val.2.2.1 j.val.2.2.2 x hint g
  refine (jetMoment_integral χ j (T g x)).2.trans ((integral_congr_ae
    ((hardySobolevTranslation_apply μ𝔽 m𝔽 (-half) half 0 hI (le_refl 0) g x).mono
      fun y hy ↦ congrArg (· * raw(χ, j) y) hy)).trans (h.trans ?_))
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (_ * ·) (jetMoment_integral χ (lowerJet χ j i) x).2.symm

private theorem exists_finite_translate_support (χ : Basepoints) (x : W)
    (hx : (support (fun j : J(χ) ↦ jetMoment χ j x)).Finite) :
    ∃ S : Finset J(χ), ∀ g j, j ∉ S → jetMoment χ j (T g x) = 0 := by
  classical
  let S := hx.toFinset.biUnion fun k ↦ Finset.univ.image (atOrder χ k)
  refine ⟨S, fun g j hj ↦ ?_⟩
  rw [jetMoment_translate]
  refine Finset.sum_eq_zero fun i _ ↦ mul_eq_zero_of_right _ ?_
  by_contra hn
  let k := lowerJet χ j i
  have hk : k ∈ hx.toFinset := hx.mem_toFinset.mpr hn
  apply hj
  apply Finset.mem_biUnion.mpr ⟨k, hk, ?_⟩
  exact Finset.mem_image.mpr ⟨⟨j.val.2.2.2, j.property⟩, Finset.mem_univ _, Subtype.ext rfl⟩

private theorem quotient_eq_sum_of_jet_support (χ : Basepoints) (hχ : IsSpectralBasepointChoice χ)
    (z : W) (S : Finset J(χ)) (hz : ∀ j, j ∉ S → jetMoment χ j z = 0) :
    let v (j : J(χ)) := (spectralStripJet_singleInterpolant (F := F) χ hχ hH (le_refl 0) j).choose
    (Θ).mkQ z = ∑ i ∈ S, jetMoment χ i z • (Θ).mkQ (v i) := by
  classical
  intro v
  let y : W := ∑ i ∈ S, jetMoment χ i z • v i
  suffices hh : (Θ).mkQ (z - y) = 0 by
    rw [map_sub, sub_eq_zero] at hh
    simpa [y] using hh
  apply (spectralSobolevQuotient_eq_zero (F := F) half hI (le_refl 0) _).mpr
  apply (spectralStripJet_commonKernel (F := F) χ hχ hH (le_refl 0) _).mpr
  intro j
  rw [← jetMoment_pairing, map_sub, sub_eq_zero]
  have hδ (i : J(χ)) : jetMoment χ j (v i) = if j = i then 1 else 0 :=
    (jetMoment_pairing χ j (v i)).trans
      ((spectralStripJet_singleInterpolant (F := F) χ hχ hH (le_refl 0) i).choose_spec j)
  simp only [y, map_sum, map_smul, hδ, smul_eq_mul, mul_ite, mul_one, mul_zero]
  by_cases hj : j ∈ S <;> simp [hj, hz]

private theorem orbitCoefficient_tendsto_zero (ψ : PontryaginDual C𝔽) (b t α : ℝ) (hb : b < α)
    (g : C𝔽) (hg : logIdeleClassNorm F g = 1) (k : ℕ) (c : ℂ) :
    Tendsto (fun n : ℕ ↦ (Real.exp (-(α * n)) : ℂ) *
      ((ideleClassNormTwist ψ ((b : ℂ) + (t : ℂ) * Complex.I) (g ^ n) *
        (logIdeleClassNorm F (g ^ n) : ℂ) ^ k) * c)) atTop (𝓝 0) := by
  have hlog (n : ℕ) : logIdeleClassNorm F (g ^ n) = n := by
    change Real.log ((ideleClassNorm F g).val : ℝ) = 1 at hg
    simp only [logIdeleClassNorm, map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow,
      Real.log_pow, hg, mul_one]
  have htwist (x : C𝔽) :
      ‖ideleClassNormTwist ψ ((b : ℂ) + (t : ℂ) * Complex.I) x‖ = Real.exp (b * logIdeleClassNorm F x) := by
    have hx : 0 < ((ideleClassNorm F x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change ‖(ψ x : ℂ) * (((ideleClassNorm F x).val : ℝ) : ℂ) ^ ((b : ℂ) + (t : ℂ) * Complex.I)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [Real.rpow_def_of_pos hx, logIdeleClassNorm, mul_comm]
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (k : ℝ) (α - b) (sub_pos.mpr hb)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hlim' := hlim.mul_const ‖c‖
  rw [zero_mul] at hlim'
  apply hlim'.congr'
  filter_upwards [] with n
  simp only [Function.comp_apply, Real.rpow_natCast, norm_mul, norm_pow, htwist, hlog,
    Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_of_nonneg (Nat.cast_nonneg _)]
  rw [show -(α - b) * (n : ℝ) = -(α * n) + b * n by ring, Real.exp_add]
  ring

private theorem dense_orbitDecay_of_moment_decay (χ : Basepoints) (hχ : IsSpectralBasepointChoice χ)
    (g : C𝔽) (α : ℝ) (hdecay : ∀ (j : J(χ)) (x : W),
      Tendsto (fun n : ℕ ↦ (Real.exp (-(α * n)) : ℂ) * jetMoment χ j (T (g ^ n) x)) atTop (𝓝 0)) :
    Dense {x : W | Tendsto (fun n : ℕ ↦ Real.exp (-(α * n)) * ‖(Θ).mkQ (T (g ^ n) x)‖)
      atTop (𝓝 0)} := by
  classical
  apply (spectralStripJet_dense_finite_moment_support (F := F) χ hχ half half 0 hH (le_refl 0)).mono
  intro x hx
  change (support (fun j : J(χ) ↦ spectralSobolevPairing (F := F) x (jetLp(χ, j)))).Finite at hx
  obtain ⟨S, hS⟩ := exists_finite_translate_support χ x (by simpa only [jetMoment_pairing] using hx)
  let v (j : J(χ)) := (spectralStripJet_singleInterpolant (F := F) χ hχ hH (le_refl 0) j).choose
  have hrep (n : ℕ) : (Θ).mkQ (T (g ^ n) x) = ∑ i ∈ S, jetMoment χ i (T (g ^ n) x) • (Θ).mkQ (v i) :=
    quotient_eq_sum_of_jet_support χ hχ _ S (hS _)
  have hsum := tendsto_finsetSum S (fun i _ ↦ (hdecay i x).smul
    (tendsto_const_nhds (x := (Θ).mkQ (v i))))
  have hvec : Tendsto (fun n : ℕ ↦ (Real.exp (-(α * n)) : ℂ) • (Θ).mkQ (T (g ^ n) x)) atTop (𝓝 (0 : W ⧸ Θ)) := by
    simpa only [hrep, Finset.smul_sum, smul_smul, zero_smul, Finset.sum_const_zero] using hsum
  change Tendsto (fun n : ℕ ↦ Real.exp (-(α * n)) * ‖(Θ).mkQ (T (g ^ n) x)‖) atTop (𝓝 0)
  simpa only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), norm_zero]
    using hvec.norm

/-- Reconstruction of the approximation step of Theorem 12.5.1.1, pp. 519–520.
If the real offset of every admitted critical-strip jet is strictly less than `α`, the
rescaled positive powers of a dilation decay modulo theta on a dense set of representatives.
No uniform gap between the offsets and `α` is required. -/
theorem dense_thetaQuotientOrbitDecay_of_jet_offsets_lt (χ : Basepoints) (hχ : IsSpectralBasepointChoice χ)
    (g : C𝔽) (hg : logIdeleClassNorm F g = 1) {α : ℝ}
    (hgap : ∀ j : J(χ), j.val.2.1 < α) :
    Dense {x : W | Tendsto (fun n : ℕ ↦ Real.exp (-(α * n)) * ‖(Θ).mkQ (T (g ^ n) x)‖)
      atTop (𝓝 0)} := by
  apply dense_orbitDecay_of_moment_decay χ hχ g α
  intro j x
  let c (i : Fin (j.val.2.2.2 + 1)) := (j.val.2.2.2.choose i.val : ℂ) * jetMoment χ (lowerJet χ j i) x
  have hh := tendsto_finsetSum Finset.univ fun (i : Fin (j.val.2.2.2 + 1)) _ ↦
    orbitCoefficient_tendsto_zero (χ j.val.1) j.val.2.1 j.val.2.2.1 α (hgap j)
      g hg (j.val.2.2.2 - i.val) (c i)
  simpa only [jetMoment_translate, Finset.mul_sum, c, mul_assoc, Finset.sum_const_zero] using hh

local notation "extZeros(" τ ", " α ")" =>
  {z : {ψ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, ψ (τ t) = 1} × ℂ //
    0 < MeromorphicOn.divisor (continuedCompletedHeckeL z.1.val) univ z.2 ∧ α ≤ |z.2.re - 1 / 2|}

private theorem spectralStripJet_abs_offset_lt_of_isEmpty_exteriorZeros
    (τ : ℝ≥0ˣ →ₜ* C𝔽) {α : ℝ} (h : IsEmpty extZeros(τ, α))
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : ∀ ω t, χ ω (τ t) = 1)
    {w s : ℝ} (j : SpectralStripJetIndex χ (1 / 2) w s) : |j.val.2.1| < α := by
  let ρ : ℂ := ((1 / 2 + j.val.2.1 : ℝ) : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I
  let ψ : PontryaginDual C𝔽 := χ j.val.1
  have horder : 0 < (meromorphicOrderAt (continuedCompletedHeckeL ψ) ρ).untop₀.toNat := by
    have hj : j.val.2.2.2 < spectralStripMultiplicity w s j.val.2.1
        (meromorphicOrderAt (continuedCompletedHeckeL ψ) ρ).untop₀.toNat := j.property
    unfold spectralStripMultiplicity spectralBoundaryMultiplicity at hj
    split_ifs at hj <;> omega
  have hdiv : 0 < MeromorphicOn.divisor (continuedCompletedHeckeL ψ) univ ρ := by
    rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec ψ).1.meromorphicOn (mem_univ ρ)]
    omega
  have hre : ρ.re - 1 / 2 = j.val.2.1 := by simp [ρ]
  apply lt_of_not_ge
  intro hb
  exact h.false ⟨(⟨ψ, hχ j.val.1⟩, ρ), hdiv, hre ▸ hb⟩

/-- Theorem 12.5.1.1, pp. 519–520. Emptiness of the exterior zero set for characters
normalized on the given section gives full-sequence rescaled decay on a dense set. -/
theorem dense_thetaQuotientOrbitDecay_of_isEmpty_exteriorZeros
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (g : C𝔽) (hg : logIdeleClassNorm F g = 1) {α : ℝ} (h : IsEmpty extZeros(τ, α)) :
    Dense {x : W | Tendsto (fun n : ℕ ↦ Real.exp (-(α * n)) * ‖(Θ).mkQ (T (g ^ n) x)‖)
      atTop (𝓝 0)} := by
  obtain ⟨χ, hχ, hχτ, _⟩ := exists_spectralBasepointChoice_of_normSection τ hτ
  exact dense_thetaQuotientOrbitDecay_of_jet_offsets_lt χ hχ g hg fun j ↦
    (le_abs_self j.val.2.1).trans_lt (spectralStripJet_abs_offset_lt_of_isEmpty_exteriorZeros τ h χ hχτ j)

private theorem orderZero_jet_offset_lt_half
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (j : SpectralStripJetIndex χ half half 0) :
    j.val.2.1 < half := by
  have hj := j.property
  unfold spectralStripMultiplicity spectralBoundaryMultiplicity at hj
  split_ifs at hj with hi he
  · exact hi.2
  · have hz : ⌈((0 : ℝ) - 1) / 2⌉₊ = 0 := Nat.ceil_eq_zero.mpr (by norm_num)
    exact False.elim (Nat.not_lt_zero _ ((lt_min_iff.mp hj).2.trans_le hz.le))
  · omega

/-- At the full critical half-width the rescaled translates of every representative
converge to zero modulo theta. Order-zero jets are strictly interior, and the
rescaled translation operators are uniformly contractive. -/
theorem thetaQuotientOrbitDecay_half (g : C𝔽) (hg : logIdeleClassNorm F g = 1) (x : W) :
    Tendsto (fun n : ℕ ↦ Real.exp (-(half * n)) * ‖(Θ).mkQ (T (g ^ n) x)‖) atTop (𝓝 0) := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice F
  have hd := dense_thetaQuotientOrbitDecay_of_jet_offsets_lt χ hχ g hg (orderZero_jet_offset_lt_half χ)
  have hnorm (n : ℕ) (v : W) :
      Real.exp (-(half * n)) * ‖(Θ).mkQ (T (g ^ n) v)‖ ≤ ‖v‖ := by
    have hlog : Real.log ((m𝔽 (g ^ n)).val : ℝ) = n := by
      change Real.log ((m𝔽 g).val : ℝ) = 1 at hg
      rw [map_pow, Units.val_pow_eq_pow_val, NNReal.coe_pow, Real.log_pow, hg, mul_one]
    have hT := norm_hardySobolevTranslation_le μ𝔽 m𝔽 (-half) half 0 hI (le_refl 0) (g ^ n)
    simp only [hlog, zero_div, Real.rpow_zero, mul_one] at hT
    rw [max_eq_right (Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) n]))] at hT
    have hq := (Submodule.Quotient.norm_mk_le (Θ) _).trans ((T (g ^ n)).le_opNorm v)
    rw [Real.exp_neg, ← div_eq_inv_mul, div_le_iff₀ (Real.exp_pos _), mul_comm]
    exact hq.trans (mul_le_mul_of_nonneg_right hT (norm_nonneg v))
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp (hd x) (ε / 2) (half_pos hε)
  rw [dist_eq_norm] at hxy
  filter_upwards [hy.eventually_lt_const (half_pos hε)] with n hn
  let Q := (Θ).mkQ.comp (T (g ^ n)).toLinearMap
  have htri : ‖Q x‖ ≤ ‖Q (x - y)‖ + ‖Q y‖ := by
    simpa only [← Q.map_add, sub_add_cancel] using norm_add_le (Q (x - y)) (Q y)
  change Real.exp (-(half * n)) * ‖Q y‖ < ε / 2 at hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (norm_nonneg _))]
  calc
    Real.exp (-(half * n)) * ‖Q x‖ ≤ _ :=
      mul_le_mul_of_nonneg_left htri (Real.exp_nonneg _)
    _ = _ := mul_add _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add ((hnorm n (x - y)).trans_lt hxy) hn
    _ = ε := add_halves ε

end RiemannMasullo.Isolated
