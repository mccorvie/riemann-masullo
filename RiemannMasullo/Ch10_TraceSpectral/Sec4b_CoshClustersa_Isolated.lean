module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CoshMellin_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec3
public import RiemannMasullo.ForMathlib.Analysis.Complex.RectangleInterpolation
import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.ForMathlib.Analysis.Fourier.PaleyWienerStrip
import RiemannMasullo.AppC_LCTVS.Sec3a
import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-!
# Single-cluster quotient and cosh-weighted spectral bounds (`#7406`)

1. `traceNorm_le_rank_mul_norm` and `traceNorm_spectralConvolutionFiniteSum_le`:
   trace norm of a finite-rank spectral block bounded by its jet count times its operator norm.
2. `spectralConvolution_all_jet_coefficients` and `spectralConvolution_comp_quotClusterProj`:
   triangular moment matrix on all Sobolev orders `s ≥ 0` and cluster commutation.
3. `traceNorm_singleCluster_quotient_le` & `_eq_zero`:
   single-cluster quotient trace-norm estimate via rectangle interpolation (`A = 0`) and
   `exists_spectralStripKernelOperator`, with strip constant `stripKernelNormConstant α β s`.
4. `coshClusterProj` & `traceNorm_coshSpectral_cluster_le`:
   lifting the single-cluster bound to `CoshIntervalSobolev F α s`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology
open scoped BigOperators ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated.CoshPositiveWidth

section FiniteRankTraceNorm

lemma traceNorm_le_rank_mul_norm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : nuclearEndomorphisms H) (n : ℕ)
    (hrank : Module.rank ℂ T.val.toLinearMap.range ≤ (n : Cardinal)) :
    traceNorm T ≤ n * ‖T.val‖ := by
  have ht := schattenNorm_one_eq_traceNorm T
  simp only [schattenNorm, Real.rpow_one, div_one] at ht
  have hlow (k : ℕ) : ∀ r ∈ {r | ∃ S : H →L[ℂ] H,
      Module.rank ℂ S.toLinearMap.range ≤ (k : Cardinal) ∧ r = ‖S - T.val‖}, 0 ≤ r :=
    fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _
  have hle (k : ℕ) : approximationNumber T.val k ≤ ‖T.val‖ := by
    refine (csInf_le ⟨0, hlow k⟩ ⟨0, ?_, rfl⟩).trans_eq (by simp)
    rw [show (0 : H →L[ℂ] H).toLinearMap.range = ⊥ from LinearMap.range_zero, rank_bot]
    exact zero_le
  have hzero (k : ℕ) (hk : k ∉ Finset.range n) : approximationNumber T.val k = 0 := by
    have hnk : (n : Cardinal) ≤ (k : Cardinal) := by
      exact_mod_cast not_lt.mp (Finset.mem_range.not.mp hk)
    apply le_antisymm
    · exact (csInf_le ⟨0, hlow k⟩ ⟨T.val, hrank.trans hnk, rfl⟩).trans_eq (by simp)
    · exact le_csInf ⟨_, T.val, hrank.trans hnk, rfl⟩ (hlow k)
  rw [← ht, tsum_eq_sum hzero]
  refine (Finset.sum_le_sum fun k _ ↦ hle k).trans_eq ?_
  simp

lemma spectralConvolutionFiniteSum_mem_nuclear {H J Z : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) (x : J → H)
    (Λ : J → StrongDual ℂ H) (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    spectralConvolutionFiniteSum A x Λ K N jet ∈ nuclearEndomorphisms H := by
  refine Submodule.sum_mem _ fun z _ ↦ Submodule.sum_mem _ fun m _ ↦ ?_
  exact smulRight_mem_nuclearEndomorphisms ((Λ (jet z m)).comp A) (x (jet z m))

lemma rank_spectralConvolutionFiniteSum_le {H J Z : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    Module.rank ℂ (spectralConvolutionFiniteSum A x Λ K N jet).toLinearMap.range ≤
      ((∑ z ∈ K, N z : ℕ) : Cardinal) := by
  classical
  let Y := (K.sigma fun z ↦ (Finset.univ : Finset (Fin (N z)))).image (fun p ↦ x (jet p.1 p.2))
  have hsub : (spectralConvolutionFiniteSum A x Λ K N jet).toLinearMap.range ≤
      Submodule.span ℂ (Y : Set H) := by
    rintro _ ⟨v, rfl⟩
    change spectralConvolutionFiniteSum A x Λ K N jet v ∈ Submodule.span ℂ (Y : Set H)
    simp only [spectralConvolutionFiniteSum, sum_apply, ContinuousLinearMap.smulRight_apply]
    refine Submodule.sum_mem _ fun z hz ↦ Submodule.sum_mem _ fun m _ ↦
      Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact Finset.mem_image.mpr ⟨⟨z, m⟩, Finset.mem_sigma.mpr ⟨hz, Finset.mem_univ _⟩, rfl⟩
  refine (Submodule.rank_mono hsub).trans ((rank_span_finset_le Y).trans ?_)
  have hcard : Y.card ≤ ∑ z ∈ K, N z := Finset.card_image_le.trans_eq (by simp)
  exact_mod_cast hcard

lemma traceNorm_spectralConvolutionFiniteSum_le {H J Z : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (A : H →L[ℂ] H) (x : J → H)
    (Λ : J → StrongDual ℂ H) (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    traceNorm ⟨spectralConvolutionFiniteSum A x Λ K N jet,
        spectralConvolutionFiniteSum_mem_nuclear A x Λ K N jet⟩ ≤
      ((∑ z ∈ K, N z : ℕ) : ℝ) * ‖spectralConvolutionFiniteSum A x Λ K N jet‖ :=
  traceNorm_le_rank_mul_norm ⟨_, spectralConvolutionFiniteSum_mem_nuclear A x Λ K N jet⟩
    (∑ z ∈ K, N z) (rank_spectralConvolutionFiniteSum_le A x Λ K N jet)

end FiniteRankTraceNorm

section SpectralClusterMachinery

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "logNorm" => logIdeleClassNorm F

/-- A point `(ω, b, t)` whose shifted ordinate `a + b + i t` is a zero of `Λ(s, χ ω)` with
real part in `[-α, α]`. -/
abbrev CoshStripZero (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (a α : ℝ) :=
  {z : PontryaginDual (ideleClassNorm F).ker × ℝ × ℝ //
    z.2.1 ∈ Icc (-α) α ∧
      0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ z.1))
        (((a + z.2.1 : ℝ) : ℂ) + (z.2.2 : ℂ) * Complex.I)}

/-- Surviving multiplicity of a zero `z` in the strip `[-α, α]` at Sobolev order `s`. -/
def coshStripMult (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (a α s : ℝ) (z : CoshStripZero (F := F) χ a α) : ℕ :=
  spectralStripMultiplicity α s z.val.2.1
    (meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ z.val.1))
      (((a + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I)).untop₀.toNat

/-- Package `(z, m)` into a `SpectralStripJetIndex`. -/
def coshStripJet (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (a α s : ℝ) (z : CoshStripZero (F := F) χ a α)
    (m : Fin (coshStripMult χ a α s z)) : SpectralStripJetIndex (F := F) χ a α s :=
  ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩

lemma coshStripJet_injective (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (a α s : ℝ) :
    Injective (fun p : (z : CoshStripZero (F := F) χ a α) × Fin (coshStripMult χ a α s z) ↦
      coshStripJet χ a α s p.1 p.2) := by
  rintro ⟨z₁, m₁⟩ ⟨z₂, m₂⟩ h
  have hz : z₁ = z₂ := Subtype.ext (Prod.ext (congrArg (fun j ↦ j.val.1) h)
    (Prod.ext (congrArg (fun j ↦ j.val.2.1) h) (congrArg (fun j ↦ j.val.2.2.1) h)))
  subst hz
  congr 1
  exact Fin.ext (congrArg (fun j ↦ j.val.2.2.2) h)

private lemma spectralConvolution_jet_eval {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (j : SpectralStripJetIndex (F := F) χ a α s)
    (f : StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hf : spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs f =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (v : CompactIntervalSobolev μ𝔽 logNorm (-α) α s) :
    Integrable (fun y : C𝔽 ↦ v y *
        spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2 y) μ𝔽 ∧
      f ((globalThetaSobolev F a ((neg_nonpos.mpr hα).trans hα) hs).mkQL v) =
        ∫ y : C𝔽, v y *
          spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2 y ∂μ𝔽 := by
  let hI := (neg_nonpos.mpr hα).trans hα
  let θ := globalThetaSobolev F a hI hs
  let w (g : C𝔽) := intervalSobolevDensity (-α) α s (logNorm g)
  have hw : Measurable w := by
    have hD : Continuous (intervalSobolevDensity (-α) α s) := by
      unfold intervalSobolevDensity; fun_prop
    exact hD.measurable.comp continuous_logNorm.measurable
  have habs : μ𝔽 ≪ (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (w g)⁻¹) := by
    refine withDensity_absolutelyContinuous' hw.inv.ennreal_ofReal.aemeasurable (.of_forall fun g ↦ ?_)
    refine ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr ?_)
    exact mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  let D₀ := spectralSobolevDualEmbedding (F := F) a hI hs
  let raw := spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2
  have hae : ((D₀ f : C𝔽 → ℂ) =ᵐ[μ𝔽] raw) := by
    have h1 := MemLp.coeFn_toLp (spectralStripJet_memLp (F := F) χ hα hs j)
    have h2 : (D₀ f : C𝔽 → ℂ) =ᵐ[(μ𝔽).withDensity fun g ↦ ENNReal.ofReal (w g)⁻¹] raw := by
      simpa only [D₀, hf] using h1
    exact habs.ae_eq h2
  have hp := spectralSobolevPairing_dual (F := F) (l := -α) (r := α) (s := s) hI hs
    (f.comp θ.mkQL) v
  have hd : ((modulatedIntervalSobolev_dual
      (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽
      (-α) α s hI hs).exists.choose (f.comp θ.mkQL) : C𝔽 → ℂ) =ᵐ[μ𝔽] raw :=
    hae
  have heq : (fun y : C𝔽 ↦ v y * (modulatedIntervalSobolev_dual
      (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ μ𝔽
      (-α) α s hI hs).exists.choose (f.comp θ.mkQL) y) =ᵐ[μ𝔽]
      fun y : C𝔽 ↦ v y * raw y :=
    hd.mono fun y hy ↦ congrArg (v y * ·) hy
  exact ⟨hp.1.congr heq, hp.2.trans (integral_congr_ae heq)⟩

private lemma stripJet_all_translated_moments_iso {α s : ℝ} (_hα : 0 ≤ α) (_hs : 0 ≤ s)
    (η : PontryaginDual C𝔽) (b t : ℝ) (m : ℕ)
    (v : CompactIntervalSobolev μ𝔽 logNorm (-α) α s)
    (hint : ∀ i ≤ m, Integrable (fun x ↦ v x * spectralZeroJet (F := F) η b t i x) μ𝔽)
    (g : C𝔽) :
    ∫ y : C𝔽, (v : C𝔽 → ℂ) (g⁻¹ * y) * spectralZeroJet (F := F) η b t m y ∂μ𝔽 =
      ∑ i : Fin (m + 1), (ideleClassNormTwist (F := F) η ((b : ℂ) + (t : ℂ) * Complex.I) g *
        (logNorm g : ℂ) ^ (m - i.val) * (m.choose i.val : ℂ)) *
        ∫ y, v y * spectralZeroJet (F := F) η b t i.val y ∂μ𝔽 := by
  let T := ideleClassNormTwist (F := F) η ((b : ℂ) + (t : ℂ) * Complex.I)
  let L (y : C𝔽) : ℂ := (logNorm y : ℂ)
  let c (i : ℕ) := T g * L g ^ (m - i) * (m.choose i : ℂ)
  have hlog (y : C𝔽) : L (g * y) = L y + L g := by
    dsimp only [L, logIdeleClassNorm]
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul
      (NNReal.coe_ne_zero.2 (ideleClassNorm F g).ne_zero)
      (NNReal.coe_ne_zero.2 (ideleClassNorm F y).ne_zero), Complex.ofReal_add, add_comm]
  have hsum (y : C𝔽) : v y * spectralZeroJet (F := F) η b t m (g * y) =
      ∑ i ∈ Finset.range (m + 1), c i * (v y * spectralZeroJet (F := F) η b t i y) := by
    change v y * (T (g * y) * L (g * y) ^ m) = _
    rw [map_mul, hlog, add_pow]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    change v y * (T g * T y * (L y ^ i * L g ^ (m - i) * (m.choose i : ℂ))) =
      (T g * L g ^ (m - i) * (m.choose i : ℂ)) * (v y * (T y * L y ^ i))
    ring
  let J := spectralZeroJet (F := F) η b t m
  let H (y : C𝔽) := v (g⁻¹ * y) * J y
  calc
    _ = ∫ y, H y ∂μ𝔽 := rfl
    _ = ∫ y, H (g * y) ∂μ𝔽 := (integral_mul_left_eq_self H g).symm
    _ = ∫ y, v y * J (g * y) ∂μ𝔽 := by simp only [H, inv_mul_cancel_left]
    _ = _ := by
      simp_rw [show ∀ y, v y * J (g * y) = _ from hsum]
      rw [integral_finsetSum _ fun i hi ↦ (hint i (Finset.mem_range_succ_iff.mp hi)).const_mul (c i)]
      simp_rw [integral_const_mul]
      exact (Fin.sum_univ_eq_sum_range
        (fun i ↦ c i * ∫ y, v y * spectralZeroJet (F := F) η b t i y ∂μ𝔽) _).symm

lemma spectralConvolution_all_jet_coefficients {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (f : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (f j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (z : CoshStripZero (F := F) χ a α)
    (m : Fin (coshStripMult χ a α s z))
    (u : spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs) :
    f (coshStripJet χ a α s z m)
        (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ u) =
      ∑ i : Fin (m.val + 1), (m.val.choose i.val : ℂ) *
        (∫ g : C𝔽, φ.val g *
          ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) g *
          (logNorm g : ℂ) ^ (m.val - i.val) ∂μ𝔽) *
        f (coshStripJet χ a α s z ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩) u := by
  let hI := (neg_nonpos.mpr hα).trans hα
  let θ := globalThetaSobolev F a hI hs
  obtain ⟨v, hv⟩ := θ.mkQ_surjective u
  let J (i : ℕ) := spectralZeroJet (F := F) (χ z.val.1) z.val.2.1 z.val.2.2 i
  have hnorm : Continuous (ideleClassNorm F) := (isProperMap_ideleClassNorm F).continuous
  let mod : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, hnorm⟩
  let τ := hardySobolevTranslation μ𝔽 mod (-α) α s hI hs
  let ℓ := (f (coshStripJet χ a α s z m)).comp θ.mkQL
  let η := ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I)
  have heval (k : SpectralStripJetIndex (F := F) χ a α s)
      (w : CompactIntervalSobolev μ𝔽 logNorm (-α) α s) :=
    spectralConvolution_jet_eval hα hs χ k (f k) (hj k) w
  have hint (i : ℕ) (hi : i ≤ m.val) : Integrable (fun y ↦ v y * J i y) μ𝔽 :=
    (heval ⟨(z.val.1, z.val.2.1, z.val.2.2, i), hi.trans_lt m.isLt⟩ v).1
  let idx (i : Fin (m.val + 1)) : SpectralStripJetIndex (F := F) χ a α s :=
    coshStripJet χ a α s z ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩
  let y (i : Fin (m.val + 1)) := f (idx i) u
  let h (i : Fin (m.val + 1)) (g : C𝔽) :=
    (η g * (logNorm g : ℂ) ^ (m.val - i.val) * (m.val.choose i.val : ℂ)) * y i
  have hi (i : Fin (m.val + 1)) : (∫ x, v x * J i.val x ∂μ𝔽) = y i :=
    (heval (idx i) v).2.symm.trans (congrArg (f (idx i)) hv)
  have hτ (g : C𝔽) : ℓ (τ g v) = ∑ i : Fin (m.val + 1), h i g := by
    have hae := hardySobolevTranslation_apply μ𝔽 mod (-α) α s hI hs g v
    have hshift : ∫ x, (τ g v : C𝔽 → ℂ) x * J m.val x ∂μ𝔽 =
        ∫ x, (v : C𝔽 → ℂ) (g⁻¹ * x) * J m.val x ∂μ𝔽 :=
      integral_congr_ae (hae.mono fun x hx ↦ congrArg (· * J m.val x) hx)
    have ht := stripJet_all_translated_moments_iso hα hs (χ z.val.1) z.val.2.1 z.val.2.2 m.val v hint g
    refine (heval (coshStripJet χ a α s z m) (τ g v)).2.trans (hshift.trans (ht.trans ?_))
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    exact congrArg ((η g * (logNorm g : ℂ) ^ (m.val - i.val) * (m.val.choose i.val : ℂ)) * ·) (hi i)
  have hφ : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hg (i : Fin (m.val + 1)) : Integrable (fun g : C𝔽 ↦ φ.val g * h i g) μ𝔽 :=
    (hφ.mul (((η.continuous.mul (Complex.continuous_ofReal.comp continuous_logNorm |>.pow _)).mul
      continuous_const).mul continuous_const)).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  have pettis := bruhatRegularizedAction_apply μ𝔽 τ
    (exists_hardySobolevTranslation μ𝔽 mod (-α) α s hI hs).choose_spec.2 φ v
  have he : ℓ (hardySobolevTestAction μ𝔽 mod (-α) α s hI hs φ v) =
      ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 :=
    congrArg (fun p : PettisWeakCompletion (CompactIntervalSobolev μ𝔽 logNorm (-α) α s) ↦
      (show Module.Dual ℂ (StrongDual ℂ (CompactIntervalSobolev μ𝔽 logNorm (-α) α s)) from p) ℓ)
      pettis.2
  have conv := spectralConvolution_mkQ (F := F) a hI hs φ v
  simp only at conv
  calc
    f (coshStripJet χ a α s z m) (spectralConvolution (F := F) a hI hs φ u)
        = ℓ (hardySobolevTestAction μ𝔽 mod (-α) α s hI hs φ v) :=
          (congrArg (fun w ↦ f (coshStripJet χ a α s z m)
            (spectralConvolution (F := F) a hI hs φ w)) hv.symm).trans
            (congrArg (f (coshStripJet χ a α s z m)) conv)
    _ = ∫ g, ℓ (φ.val g • τ g v) ∂μ𝔽 := he
    _ = ∫ g, ∑ i : Fin (m.val + 1), φ.val g * h i g ∂μ𝔽 :=
          integral_congr_ae (.of_forall fun g ↦
            (map_smul ℓ (φ.val g) (τ g v)).trans ((congrArg (φ.val g * ·) (hτ g)).trans (Finset.mul_sum ..)))
    _ = ∑ i : Fin (m.val + 1), ∫ g, φ.val g * h i g ∂μ𝔽 :=
          integral_finsetSum _ fun i _ ↦ hg i
    _ = _ := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          have hsc : (fun g : C𝔽 ↦ φ.val g * h i g) =
              fun g ↦ (m.val.choose i.val : ℂ) *
                (φ.val g * η g * (logNorm g : ℂ) ^ (m.val - i.val)) * y i := by
            ext g; dsimp only [h]; ring
          rw [hsc, integral_mul_const, integral_const_mul]

/-- Finite cluster projection on the spectral quotient `Q`. -/
def quotClusterProj {H J Z : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (x : J → H) (Λ : J → StrongDual ℂ H) (K : Finset Z) (N : Z → ℕ)
    (jet : (z : Z) → Fin (N z) → J) : H →L[ℂ] H :=
  ∑ z ∈ K, ∑ m : Fin (N z), (Λ (jet z m)).smulRight (x (jet z m))

lemma quotClusterProj_eval {H J Z : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [DecidableEq Z] (x : J → H) (Λ : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x Λ) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Injective (fun p : (z : Z) × Fin (N z) ↦ jet p.1 p.2))
    (K : Finset Z) (z : Z) (m : Fin (N z)) (u : H) :
    Λ (jet z m) (quotClusterProj x Λ K N jet u) = if z ∈ K then Λ (jet z m) u else 0 := by
  simp only [quotClusterProj, sum_apply, map_sum,
    ContinuousLinearMap.smulRight_apply, map_smul, smul_eq_mul]
  split_ifs with hz
  · rw [Finset.sum_eq_single_of_mem z hz]
    · rw [Finset.sum_eq_single m]
      · rw [hb.1, mul_one]
      · intro k _ hk
        have hne : jet z k ≠ jet z m :=
          fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.mp (hjet (a₁ := ⟨z, k⟩) (a₂ := ⟨z, m⟩) h)).2)
        rw [hb.2.1 _ _ hne, mul_zero]
      · simp
    · intro w _ hw
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      have hne : jet w k ≠ jet z m :=
        fun h ↦ hw (congrArg Sigma.fst (hjet (a₁ := ⟨w, k⟩) (a₂ := ⟨z, m⟩) h))
      rw [hb.2.1 _ _ hne, mul_zero]
  · refine Finset.sum_eq_zero fun w hw ↦ Finset.sum_eq_zero fun k _ ↦ ?_
    have hne : jet w k ≠ jet z m := fun h ↦ by
      have hwz : w = z := congrArg Sigma.fst (hjet (a₁ := ⟨w, k⟩) (a₂ := ⟨z, m⟩) h)
      exact hz (hwz ▸ hw)
    rw [hb.2.1 _ _ hne, mul_zero]

lemma spectralConvolutionFiniteSum_eval {H J Z : Type*} [NormedAddCommGroup H]
    [NormedSpace ℂ H] [DecidableEq Z] (A : H →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x Λ) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (hjet : Injective (fun p : (z : Z) × Fin (N z) ↦ jet p.1 p.2))
    (K : Finset Z) (z : Z) (m : Fin (N z)) (v : H) :
    Λ (jet z m) (spectralConvolutionFiniteSum A x Λ K N jet v) =
      if z ∈ K then Λ (jet z m) (A v) else 0 := by
  simp only [spectralConvolutionFiniteSum, sum_apply, map_sum,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply, map_smul, smul_eq_mul]
  split_ifs with hz
  · rw [Finset.sum_eq_single_of_mem z hz]
    · rw [Finset.sum_eq_single m]
      · rw [hb.1, mul_one]
      · intro k _ hk
        have hne : jet z k ≠ jet z m :=
          fun h ↦ hk (eq_of_heq (Sigma.mk.inj_iff.mp (hjet (a₁ := ⟨z, k⟩) (a₂ := ⟨z, m⟩) h)).2)
        rw [hb.2.1 _ _ hne, mul_zero]
      · simp
    · intro w _ hw
      refine Finset.sum_eq_zero fun k _ ↦ ?_
      have hne : jet w k ≠ jet z m :=
        fun h ↦ hw (congrArg Sigma.fst (hjet (a₁ := ⟨w, k⟩) (a₂ := ⟨z, m⟩) h))
      rw [hb.2.1 _ _ hne, mul_zero]
  · refine Finset.sum_eq_zero fun w hw ↦ Finset.sum_eq_zero fun k _ ↦ ?_
    have hne : jet w k ≠ jet z m := fun h ↦ by
      have hwz : w = z := congrArg Sigma.fst (hjet (a₁ := ⟨w, k⟩) (a₂ := ⟨z, m⟩) h)
      exact hz (hwz ▸ hw)
    rw [hb.2.1 _ _ hne, mul_zero]

lemma spectralConvolution_comp_quotClusterProj {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (K : Finset (CoshStripZero (F := F) χ a α)) :
    (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ).comp
        (quotClusterProj x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)) =
      spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
        x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) := by
  classical
  ext1 u
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
  have hev : ContinuousLinearMap.apply ℂ ℂ
        ((spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
          (quotClusterProj x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) u)) =
      ContinuousLinearMap.apply ℂ ℂ
        (spectralConvolutionFiniteSum
          (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
          x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) u) := by
    apply ContinuousLinearMap.ext_on hb.2.2.2
    rintro _ ⟨j, rfl⟩
    let z : CoshStripZero (F := F) χ a α := ⟨(j.val.1, j.val.2.1, j.val.2.2.1),
      (SpectralStripJetIndex.mem_strip_order_pos hα j).1,
      (SpectralStripJetIndex.mem_strip_order_pos hα j).2⟩
    let m : Fin (coshStripMult χ a α s z) := ⟨j.val.2.2.2, j.property⟩
    have hj_eq : j = coshStripJet χ a α s z m := Subtype.ext rfl
    change Λ j ((spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
        (quotClusterProj x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) u)) =
      Λ j (spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
        x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) u)
    rw [hj_eq, spectralConvolutionFiniteSum_eval _ x Λ hb _ _ (coshStripJet_injective χ a α s) K z m u,
      spectralConvolution_all_jet_coefficients hα hs χ Λ hj φ z m]
    by_cases hz : z ∈ K
    · simp only [hz, ↓reduceIte, spectralConvolution_all_jet_coefficients hα hs χ Λ hj φ z m u]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hi := quotClusterProj_eval x Λ hb (coshStripMult χ a α s) (coshStripJet χ a α s)
        (coshStripJet_injective χ a α s) K z ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ u
      simp only [hz, ↓reduceIte] at hi; exact congrArg _ hi
    · simp only [hz, ↓reduceIte]
      refine Finset.sum_eq_zero fun i _ ↦ ?_
      have hi := quotClusterProj_eval x Λ hb (coshStripMult χ a α s) (coshStripJet χ a α s)
        (coshStripJet_injective χ a α s) K z ⟨i.val, (Nat.le_of_lt_succ i.isLt).trans_lt m.isLt⟩ u
      simp only [hz, ↓reduceIte] at hi; simp [hi]
  exact fun ℓ ↦ DFunLike.congr_fun hev ℓ

private lemma map_logIdeleClassNorm_eq_smul :
    ∃ c : ℝ≥0, c ≠ 0 ∧ Measure.map (logIdeleClassNorm F) μ𝔽 = c • (volume : Measure ℝ) := by
  let μ := ideleClassTamagawaMeasure F; let ν : Measure (Multiplicative ℝ) := (volume : Measure ℝ)
  have : IsFiniteMeasureOnCompacts ν := inferInstanceAs (IsFiniteMeasureOnCompacts (volume : Measure ℝ))
  have : Measure.IsOpenPosMeasure ν := inferInstanceAs (Measure.IsOpenPosMeasure (volume : Measure ℝ))
  have : ν.IsMulLeftInvariant := ⟨fun t ↦ (measurePreserving_add_left (volume : Measure ℝ) t.toAdd).map_eq⟩
  let : ν.IsHaarMeasure := ⟨⟩
  let e : ℝ≥0ˣ ≃ₜ ℝ := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.toHomeomorph.symm
  have he (t : ℝ≥0ˣ) : e t = Real.log (t.val : ℝ) :=
    (Real.log_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))).symm
  let m : C𝔽 →* Multiplicative ℝ :=
    { toFun := fun g ↦ Multiplicative.ofAdd (e (ideleClassNorm F g))
      map_one' := by change e (ideleClassNorm F 1) = 0; simp [he]
      map_mul' := fun g h ↦ by
        change e (ideleClassNorm F (g * h)) = e (ideleClassNorm F g) + e (ideleClassNorm F h)
        rw [he, map_mul, Units.val_mul, NNReal.coe_mul, he, he]
        exact Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' (NNReal.coe_pos.mpr (Units.zero_lt _)).ne' }
  have hm : IsProperMap m := e.isProperMap.comp (isProperMap_ideleClassNorm F)
  obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
  have hsurj : Surjective m := e.surjective.comp hsurj
  let : (μ.map m).IsHaarMeasure :=
    Measure.isHaarMeasure_map μ m hm.continuous hsurj (isProperMap_iff_tendsto_cocompact.mp hm).2
  refine ⟨Measure.haarScalarFactor (μ.map m) ν, (Measure.haarScalarFactor_pos_of_isHaarMeasure (μ.map m) ν).ne', ?_⟩
  have hFun : (m : C𝔽 → ℝ) = logIdeleClassNorm F := funext fun g ↦ he (ideleClassNorm F g)
  rw [← hFun]; exact Measure.isMulLeftInvariant_eq_smul (μ.map m) ν

private lemma twist_mul_of_mem_ker
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) χ)
    {ω ω₀ : PontryaginDual (ideleClassNorm F).ker} (hne : ω ≠ ω₀) (w : ℂ) (H : ℝ → ℂ) :
    ∫ g : C𝔽, (((χ ω₀ g)⁻¹ : Circle) : ℂ) * H (logNorm g) *
      ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽 = 0 := by
  obtain ⟨k, hk⟩ : ∃ k : (ideleClassNorm F).ker, (ω k : ℂ) ≠ (ω₀ k : ℂ) := by
    by_contra! heq
    exact hne (DFunLike.ext _ _ fun k ↦ Subtype.ext (heq k))
  let ξ := ideleClassNormTwist (F := F) (χ ω) w
  have hlog (g : C𝔽) : logNorm (k.val * g) = logNorm g := by
    change Real.log ((ideleClassNorm F (k.val * g)).val : ℝ) = Real.log ((ideleClassNorm F g).val : ℝ)
    rw [map_mul, k.property, one_mul]
  have hk0 : (((χ ω₀ k.val)⁻¹ : Circle) : ℂ) = ((ω₀ k : ℂ))⁻¹ := by
    have h := congrArg (fun u : Circle ↦ (u : ℂ)) (DFunLike.congr_fun (hχ ω₀) k)
    change ((χ ω₀ k.val : Circle) : ℂ) = (ω₀ k : ℂ) at h
    have h1 := (Circle.coe_mul (χ ω₀ k.val) (χ ω₀ k.val)⁻¹).symm
    rw [mul_inv_cancel, Circle.coe_one] at h1
    rw [eq_inv_of_mul_eq_one_right h1, h]
  have hkξ_mul (g : C𝔽) : ξ (k.val * g) = (ω k : ℂ) * ξ g := by
    have hnorm : ((ideleClassNorm F (k.val * g)).val : ℝ) = ((ideleClassNorm F g).val : ℝ) := by
      rw [map_mul, k.property, one_mul]
    change (χ ω (k.val * g) : ℂ) * (((ideleClassNorm F (k.val * g)).val : ℝ) : ℂ) ^ w = _
    rw [map_mul, Circle.coe_mul, hnorm]
    have h := congrArg (fun u : Circle ↦ (u : ℂ)) (DFunLike.congr_fun (hχ ω) k)
    change (χ ω k.val : ℂ) = (ω k : ℂ) at h
    dsimp only [ξ]
    rw [h]
    change (ω k : ℂ) * (χ ω g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w =
      (ω k : ℂ) * ((χ ω g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w)
    ring
  let f (g : C𝔽) := (((χ ω₀ g)⁻¹ : Circle) : ℂ) * H (logNorm g) * ξ g
  have h_isHaar : (μ𝔽).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have h_eq : ((ω₀ k : ℂ)⁻¹ * (ω k : ℂ)) * ∫ g, f g ∂μ𝔽 = ∫ g, f g ∂μ𝔽 := by
    calc ((ω₀ k : ℂ)⁻¹ * (ω k : ℂ)) * ∫ g, f g ∂μ𝔽
        = ∫ g, ((ω₀ k : ℂ)⁻¹ * (ω k : ℂ)) * f g ∂μ𝔽 := (integral_const_mul _ _).symm
      _ = ∫ g, f (k.val * g) ∂μ𝔽 := by
          refine integral_congr_ae (.of_forall fun g ↦ ?_)
          dsimp only [f]
          rw [hlog, hkξ_mul, map_mul, mul_inv, Circle.coe_mul, hk0]
          ring
      _ = ∫ g, f g ∂μ𝔽 := integral_mul_left_eq_self f k.val
  have hne_c : (ω₀ k : ℂ)⁻¹ * (ω k : ℂ) ≠ 1 := by
    intro h
    have h1 : (ω k : ℂ) = (ω₀ k : ℂ) := by
      calc (ω k : ℂ) = (ω₀ k : ℂ) * ((ω₀ k : ℂ)⁻¹ * (ω k : ℂ)) := by
            rw [← mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), one_mul]
        _ = (ω₀ k : ℂ) * 1 := by rw [h]
        _ = (ω₀ k : ℂ) := mul_one _
    exact hk h1
  exact mul_left_cancel₀ (sub_ne_zero.mpr hne_c) (by linear_combination h_eq)

/-- Single-cluster strip norm constant `(1 / 2) * ∫ (1 + |y|)^{s/2} exp(-(β - α)|y|) dy`. -/
def stripKernelNormConstant (α β s : ℝ) : ℝ :=
  (1 / 2) * ∫ y : ℝ, (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|) ∂(volume : Measure ℝ)

lemma stripKernelNormConstant_nonneg (α β s : ℝ) : 0 ≤ stripKernelNormConstant α β s :=
  mul_nonneg (by positivity) (integral_nonneg fun _ ↦ mul_nonneg (by positivity) (Real.exp_pos _).le)

private lemma traceNorm_nonneg_of_hilbert {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (T : nuclearEndomorphisms H) :
    0 ≤ traceNorm T := by
  rw [← schattenNorm_one_eq_traceNorm T]
  dsimp only [schattenNorm, approximationNumber]
  simp only [Real.rpow_one, div_one]
  exact tsum_nonneg fun k ↦ Real.sInf_nonneg fun _ ⟨_, _, h⟩ ↦ h ▸ norm_nonneg _

private lemma traceNorm_zero_of_hilbert {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] :
    traceNorm (0 : nuclearEndomorphisms H) = 0 := by
  have h0 : (⟨(0 : H →L[ℂ] ℂ).smulRight (0 : H),
      smulRight_mem_nuclearEndomorphisms (0 : H →L[ℂ] ℂ) (0 : H)⟩ : nuclearEndomorphisms H) = 0 :=
    Subtype.ext ContinuousLinearMap.zero_smulRight
  exact (congrArg traceNorm h0).symm.trans (by simpa using traceNorm_smulRight (0 : H →L[ℂ] ℂ) (0 : H))

lemma traceNorm_singleCluster_quotient_eq_zero {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (ω : PontryaginDual (ideleClassNorm F).ker)
    (K : Finset (CoshStripZero (F := F) χ a α)) (hK : ∀ z ∈ K, z.val.1 = ω)
    (hvan : ∀ w : ℂ, ∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽 = 0) :
    traceNorm ⟨spectralConvolutionFiniteSum
        (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
        x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s),
      spectralConvolutionFiniteSum_mem_nuclear _ x Λ K _ _⟩ = 0 := by
  classical
  let hI := (neg_nonpos.mpr hα).trans hα
  let A := spectralConvolution (F := F) a hI hs φ
  have hzero : spectralConvolutionFiniteSum A x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) = 0 := by
    ext1 v
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    have hev : ContinuousLinearMap.apply ℂ ℂ
          (spectralConvolutionFiniteSum A x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) v) =
        ContinuousLinearMap.apply ℂ ℂ (0 : spectralSobolevQuotient F a hI hs) := by
      apply ContinuousLinearMap.ext_on hb.2.2.2
      rintro _ ⟨j, rfl⟩
      let z : CoshStripZero (F := F) χ a α := ⟨(j.val.1, j.val.2.1, j.val.2.2.1),
        (SpectralStripJetIndex.mem_strip_order_pos hα j).1,
        (SpectralStripJetIndex.mem_strip_order_pos hα j).2⟩
      let m : Fin (coshStripMult χ a α s z) := ⟨j.val.2.2.2, j.property⟩
      have hj_eq : j = coshStripJet χ a α s z m := Subtype.ext rfl
      change Λ j (spectralConvolutionFiniteSum A x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) v) = Λ j 0
      rw [map_zero, hj_eq, spectralConvolutionFiniteSum_eval A x Λ hb _ _ (coshStripJet_injective χ a α s) K z m v]
      split_ifs with hz
      · rw [spectralConvolution_all_jet_coefficients hα hs χ Λ hj φ z m v]
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        have hmom : ∫ g : C𝔽, φ.val g *
            ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) g *
            (logNorm g : ℂ) ^ (m.val - i.val) ∂μ𝔽 = 0 := by
          have hΦ := spectralStripTest_mellin_iteratedDeriv (F := F) (χ z.val.1) φ
          have hfn : (fun u : ℂ ↦ ∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) (χ z.val.1) u g ∂μ𝔽) =
              fun _ ↦ 0 := funext fun u ↦ by rw [hK z hz]; exact hvan u
          rw [← (hΦ.2 (m.val - i.val) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I)), hfn]
          change iteratedDeriv (m.val - i.val) (fun _ : ℂ ↦ (0 : ℂ)) _ = 0
          simp
        simp [hmom]
      · rfl
    exact fun ℓ ↦ DFunLike.congr_fun hev ℓ
  calc traceNorm ⟨spectralConvolutionFiniteSum A x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s), _⟩
      = traceNorm (0 : nuclearEndomorphisms (spectralSobolevQuotient F a hI hs)) := by
        congr 1; exact Subtype.ext hzero
    _ = 0 := traceNorm_zero_of_hilbert

private lemma exists_singleCluster_kernelOp {a α s β : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hβ : α < β) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) χ)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (ω : PontryaginDual (ideleClassNorm F).ker)
    (m : ℂ → ℂ) (hm : Differentiable ℂ m) (B : ℝ)
    (hbound : ∀ u : ℂ, |u.re| ≤ β → ‖m u‖ ≤ B / (1 + u.im ^ 2)) :
    ∃ Ψ : spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs →L[ℂ]
        spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs,
      ‖Ψ‖ ≤ stripKernelNormConstant α β s * B ∧
      ∀ (z : CoshStripZero (F := F) χ a α),
        ((z.val.1 = ω ∧ ∀ q < coshStripMult χ a α s z,
            iteratedDeriv q m ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) =
              ∫ g : C𝔽, φ.val g *
                ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) g *
                (logNorm g : ℂ) ^ q ∂μ𝔽) →
          ∀ v (m_idx : Fin (coshStripMult χ a α s z)),
            Λ (coshStripJet χ a α s z m_idx) (Ψ v) =
              Λ (coshStripJet χ a α s z m_idx)
                (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ v)) ∧
        ((z.val.1 = ω → ∀ q < coshStripMult χ a α s z,
            iteratedDeriv q m ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) = 0) →
          ∀ v (m_idx : Fin (coshStripMult χ a α s z)),
            Λ (coshStripJet χ a α s z m_idx) (Ψ v) = 0) := by
  classical
  have hβ0 : 0 < β := hα.trans_lt hβ
  have hB : 0 ≤ B := by have h := (norm_nonneg _).trans (hbound 0 (by simpa using hβ0.le)); simpa using h
  obtain ⟨k, hkc, hkb, hkm⟩ := exists_laplaceKernel_of_strip_bound hm hβ0 hbound
  obtain ⟨c, hc0, hc⟩ := map_logIdeleClassNorm_eq_smul (F := F)
  have hcpos : (0 : ℝ) < c := lt_of_le_of_ne c.coe_nonneg (NNReal.coe_ne_zero.mpr hc0).symm
  have hcC : ((c : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcpos.ne'
  let k' (y : ℝ) : ℂ := ((c : ℝ) : ℂ)⁻¹ * k y
  have hk'norm (y : ℝ) : ‖k' y‖ = (c : ℝ)⁻¹ * ‖k y‖ := by
    change ‖((c : ℝ) : ℂ)⁻¹ * k y‖ = _; rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hcpos.le]
  let wt (y : ℝ) : ℝ := max (Real.exp (-α * y)) (Real.exp (α * y)) * (1 + |y|) ^ (s / 2)
  have hwt (y : ℝ) : wt y = Real.exp (α * |y|) * (1 + |y|) ^ (s / 2) := by
    change max (Real.exp (-α * y)) (Real.exp (α * y)) * _ = _; congr 1
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy, max_eq_right (Real.exp_le_exp.mpr (by nlinarith))]
    · rw [abs_of_nonpos hy, max_eq_left (Real.exp_le_exp.mpr (by nlinarith))]; ring_nf
  have hwtc : Continuous wt := (Continuous.max (by fun_prop) (by fun_prop)).mul
    ((continuous_const.add continuous_abs).rpow_const fun y ↦ Or.inl (by positivity : (0 : ℝ) < 1 + |y|).ne')
  have hE : Integrable (fun y : ℝ ↦ (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) :=
    integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (sub_pos.mpr hβ) _
  have hpt (y : ℝ) : ‖k y‖ * wt y ≤ (B / 2) * ((1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) := by
    rw [hwt]
    have hexp : Real.exp (-β * |y|) * Real.exp (α * |y|) = Real.exp (-(β - α) * |y|) := by rw [← Real.exp_add]; congr 1; ring
    calc ‖k y‖ * (Real.exp (α * |y|) * (1 + |y|) ^ (s / 2))
        ≤ (B / 2 * Real.exp (-β * |y|)) * (Real.exp (α * |y|) * (1 + |y|) ^ (s / 2)) :=
          mul_le_mul_of_nonneg_right (hkb y) (by positivity)
      _ = B / 2 * ((1 + |y|) ^ (s / 2) * (Real.exp (-β * |y|) * Real.exp (α * |y|))) := by ring
      _ = _ := by rw [hexp]
  have hkwt : Integrable (fun y : ℝ ↦ ‖k y‖ * wt y) :=
    (hE.const_mul (B / 2)).mono' (hkc.norm.mul hwtc).aestronglyMeasurable
      (.of_forall fun y ↦ by rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by change 0 ≤ max _ _ * _; positivity))]; exact hpt y)
  let κ (g : C𝔽) : ℂ := (((χ ω g)⁻¹ : Circle) : ℂ) * k' (logNorm g)
  have hκnorm (g : C𝔽) : ‖κ g‖ = ‖k' (logNorm g)‖ := by
    change ‖(((χ ω g)⁻¹ : Circle) : ℂ) * k' (logNorm g)‖ = _; rw [norm_mul, Circle.norm_coe, one_mul]
  have hκm : AEStronglyMeasurable κ μ𝔽 :=
    ((continuous_subtype_val.comp ((χ ω).continuous.inv)).aestronglyMeasurable).mul
      ((continuous_const.mul hkc).measurable.comp continuous_logNorm.measurable).aestronglyMeasurable
  have hint_κ : Integrable (fun g : C𝔽 ↦ ‖κ g‖ * wt (logNorm g)) μ𝔽 := by
    have hF : AEStronglyMeasurable (fun y : ℝ ↦ ‖k' y‖ * wt y) (Measure.map logNorm μ𝔽) :=
      ((continuous_const.mul hkc).norm.mul hwtc).aestronglyMeasurable
    refine ((integrable_map_measure hF continuous_logNorm.aemeasurable).mp ?_).congr (.of_forall fun g ↦ ?_)
    · rw [hc]; refine Integrable.smul_measure_nnreal ((hkwt.const_mul (c : ℝ)⁻¹).congr (.of_forall fun y ↦ ?_))
      change (c : ℝ)⁻¹ * (‖k y‖ * wt y) = ‖k' y‖ * wt y; rw [hk'norm, mul_assoc]
    · change ‖k' (logNorm g)‖ * wt (logNorm g) = ‖κ g‖ * wt (logNorm g); rw [hκnorm]
  obtain ⟨Ψ, hΨ_norm, hΨ_eval⟩ := exists_spectralStripKernelOperator (F := F) a hα hs χ Λ hj φ κ hκm hint_κ
  have htw (η : PontryaginDual C𝔽) (w : ℂ) (g : C𝔽) :
      ideleClassNormTwist (F := F) η w g = (η g : ℂ) * Complex.exp (w * (logNorm g : ℂ)) := by
    have hpos : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change (η g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ w = _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'), ← Complex.ofReal_log hpos.le]
    congr 1; simp [logIdeleClassNorm, mul_comm]
  have hmom (z : CoshStripZero (F := F) χ a α) (q : ℕ) :
      ∫ g : C𝔽, κ g * ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) g *
          (logNorm g : ℂ) ^ q ∂μ𝔽 =
        if z.val.1 = ω then iteratedDeriv q m ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) else 0 := by
    split_ifs with hc_eq
    · have hG : AEStronglyMeasurable (fun y : ℝ ↦ k' y *
          (Complex.exp (((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) * (y : ℂ)) * (y : ℂ) ^ q)) (Measure.map logNorm μ𝔽) :=
        (((continuous_const.mul hkc).measurable).mul (by fun_prop)).aestronglyMeasurable
      have h_map : ∫ g : C𝔽, κ g * ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) g *
            (logNorm g : ℂ) ^ q ∂μ𝔽 =
          ∫ y : ℝ, k' y * (Complex.exp (((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) * (y : ℂ)) * (y : ℂ) ^ q)
            ∂(Measure.map logNorm μ𝔽) := by
        rw [integral_map continuous_logNorm.aemeasurable hG]
        refine integral_congr_ae (.of_forall fun g ↦ ?_)
        change (((χ ω g)⁻¹ : Circle) : ℂ) * k' (logNorm g) *
            ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) g * (logNorm g : ℂ) ^ q = _
        rw [htw, hc_eq]
        have hone : (((χ ω g)⁻¹ : Circle) : ℂ) * (χ ω g : ℂ) = 1 := by
          rw [← Circle.coe_mul (χ ω g)⁻¹ (χ ω g), inv_mul_cancel, Circle.coe_one]
        linear_combination (k' (logNorm g) * Complex.exp (((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) * (logNorm g : ℂ)) *
          (logNorm g : ℂ) ^ q) * hone
      rw [h_map, hc, integral_smul_nnreal_measure]
      have hre : |((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I).re| < β := by
        have h1 : ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I).re = z.val.2.1 := by simp
        rw [h1]; exact (abs_le.mpr z.property.1).trans_lt hβ
      rw [← hkm _ hre q, NNReal.smul_def, Complex.real_smul, ← integral_const_mul]
      refine integral_congr_ae (.of_forall fun y ↦ ?_)
      have hcc : ((c : ℝ) : ℂ) * ((c : ℝ) : ℂ)⁻¹ = 1 := mul_inv_cancel₀ hcC
      change ((c : ℝ) : ℂ) * (((c : ℝ) : ℂ)⁻¹ * k y * (Complex.exp (((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) * (y : ℂ)) * (y : ℂ) ^ q)) = _
      linear_combination (k y * (Complex.exp (((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) * (y : ℂ)) * (y : ℂ) ^ q)) * hcc
    · have horth := twist_mul_of_mem_ker χ hχ hc_eq ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) (fun y : ℝ ↦ k' y * (y : ℂ) ^ q)
      refine Eq.trans (integral_congr_ae (.of_forall fun g ↦ ?_)) horth
      change (((χ ω g)⁻¹ : Circle) : ℂ) * k' (logNorm g) * ideleClassNormTwist (F := F) (χ z.val.1) _ g * (logNorm g : ℂ) ^ q = _
      ring
  have hint_z (z : CoshStripZero (F := F) χ a α) (q : ℕ) (_hq : q < coshStripMult χ a α s z) :
      Integrable (fun g : C𝔽 ↦ κ g * ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) g *
        (logNorm g : ℂ) ^ q) μ𝔽 := by
    have hF : AEStronglyMeasurable (fun y : ℝ ↦ ‖k' y‖ * (Real.exp (z.val.2.1 * y) * |y| ^ q)) (Measure.map logNorm μ𝔽) :=
      (((continuous_const.mul hkc).norm).mul (by fun_prop)).aestronglyMeasurable
    have h1 : Integrable (fun y : ℝ ↦ ‖k' y‖ * (Real.exp (z.val.2.1 * y) * |y| ^ q)) (Measure.map logNorm μ𝔽) := by
      rw [hc]; refine Integrable.smul_measure_nnreal ?_
      refine ((integrable_abs_pow_mul_exp_neg_mul_abs (sub_pos.mpr hβ) q).const_mul ((c : ℝ)⁻¹ * (B / 2))).mono'
        (((continuous_const.mul hkc).norm.mul (by fun_prop)).aestronglyMeasurable) (.of_forall fun y ↦ ?_)
      rw [Real.norm_of_nonneg (by positivity), hk'norm]
      have hby : Real.exp (z.val.2.1 * y) ≤ Real.exp (α * |y|) := Real.exp_le_exp.mpr <| calc
        z.val.2.1 * y ≤ |z.val.2.1 * y| := le_abs_self _
        _ = |z.val.2.1| * |y| := abs_mul _ _
        _ ≤ α * |y| := mul_le_mul_of_nonneg_right (abs_le.mpr z.property.1) (abs_nonneg y)
      have hexp : Real.exp (-β * |y|) * Real.exp (α * |y|) = Real.exp (-(β - α) * |y|) := by rw [← Real.exp_add]; congr 1; ring
      calc (c : ℝ)⁻¹ * ‖k y‖ * (Real.exp (z.val.2.1 * y) * |y| ^ q)
          ≤ (c : ℝ)⁻¹ * (B / 2 * Real.exp (-β * |y|)) * (Real.exp (α * |y|) * |y| ^ q) :=
            mul_le_mul (mul_le_mul_of_nonneg_left (hkb y) (inv_nonneg.mpr hcpos.le))
              (mul_le_mul_of_nonneg_right hby (pow_nonneg (abs_nonneg y) q)) (by positivity) (by positivity)
        _ = (c : ℝ)⁻¹ * (B / 2) * (|y| ^ q * Real.exp (-(β - α) * |y|)) := by rw [← hexp]; ring
    refine ((integrable_map_measure hF continuous_logNorm.aemeasurable).mp h1).mono' ((hκm.mul
      (ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I)).continuous.aestronglyMeasurable).mul
      ((Complex.continuous_ofReal.comp continuous_logNorm).pow q).aestronglyMeasurable) (.of_forall fun g ↦ ?_)
    change ‖κ g * ideleClassNormTwist (F := F) (χ z.val.1) ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) g * (logNorm g : ℂ) ^ q‖ ≤ _
    rw [norm_mul, norm_mul, hκnorm, hk'norm, htw,
      norm_mul ((χ z.val.1 g : Circle) : ℂ), mem_sphere_zero_iff_norm.mp (χ z.val.1 g).2, one_mul,
      Complex.norm_exp, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    have hre : (((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) * (logNorm g : ℂ)).re = z.val.2.1 * logNorm g := by simp [Complex.mul_re]
    dsimp only [Function.comp_def]
    rw [hk'norm, hre]
  have h_int_bound : ∫ g : C𝔽, ‖κ g‖ * wt (logNorm g) ∂μ𝔽 ≤ stripKernelNormConstant α β s * B := by
    have hF : AEStronglyMeasurable (fun y : ℝ ↦ ‖k' y‖ * wt y) (Measure.map logNorm μ𝔽) :=
      ((continuous_const.mul hkc).norm.mul hwtc).aestronglyMeasurable
    have h1 : (∫ g : C𝔽, ‖κ g‖ * wt (logNorm g) ∂μ𝔽) = ∫ y : ℝ, ‖k' y‖ * wt y ∂(Measure.map logNorm μ𝔽) := by
      rw [integral_map continuous_logNorm.aemeasurable hF]
      exact integral_congr_ae (.of_forall fun g ↦ by change ‖κ g‖ * wt (logNorm g) = ‖k' (logNorm g)‖ * wt (logNorm g); rw [hκnorm])
    rw [h1, hc, integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
    have h2 : ∫ y : ℝ, ‖k' y‖ * wt y ∂volume = (c : ℝ)⁻¹ * ∫ y : ℝ, ‖k y‖ * wt y ∂volume := by
      rw [← integral_const_mul]; exact integral_congr_ae (.of_forall fun y ↦ by dsimp only; rw [hk'norm, mul_assoc])
    rw [h2, ← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul]
    calc ∫ y : ℝ, ‖k y‖ * wt y ∂volume
        ≤ ∫ y : ℝ, (B / 2) * ((1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|)) ∂volume := integral_mono hkwt (hE.const_mul (B / 2)) hpt
      _ = (B / 2) * ∫ y : ℝ, (1 + |y|) ^ (s / 2) * Real.exp (-(β - α) * |y|) ∂volume := integral_const_mul _ _
      _ = stripKernelNormConstant α β s * B := by unfold stripKernelNormConstant; ring
  refine ⟨Ψ, hΨ_norm.trans h_int_bound, fun z ↦ ⟨?_, ?_⟩⟩
  · intro ⟨hzw, hin⟩ v m_idx
    refine (hΨ_eval z (hint_z z)).1 (fun q hq ↦ ?_) m_idx v
    rw [hmom z q]
    split_ifs
    exact hin q hq
  · intro hout v m_idx
    refine (hΨ_eval z (hint_z z)).2 (fun q hq ↦ ?_) m_idx v
    rw [hmom z q]
    split_ifs with hzw
    · exact hout hzw q hq
    · rfl

theorem traceNorm_singleCluster_quotient_le {a α s β X : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hβ : α < β) (hβX : β < X)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) χ)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (ω : PontryaginDual (ideleClassNorm F).ker)
    (τ₁ τ₂ : ℝ) (hτ₁ : τ₁ + 1 ≤ τ₂) (hτ₂ : τ₂ ≤ τ₁ + 3)
    (K : Finset (CoshStripZero (F := F) χ a α))
    (hK_in : ∀ z ∈ K, z.val.1 = ω ∧ τ₁ ≤ z.val.2.2 ∧ z.val.2.2 < τ₂)
    (hK_all : ∀ z : CoshStripZero (F := F) χ a α, z.val.1 = ω → τ₁ ≤ z.val.2.2 → z.val.2.2 < τ₂ → z ∈ K)
    (ϑ : ℂ → ℂ) (hϑ : Differentiable ℂ ϑ)
    (hgrowth : ∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ u‖ ≤ 1)
    (hord : ∀ z : CoshStripZero (F := F) χ a α, z.val.1 = ω →
      ((coshStripMult χ a α s z : ℕ) : ℕ∞) ≤ analyticOrderAt ϑ ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I))
    (ℓ φb : ℝ) (hℓ : 0 < ℓ) (hlow : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂, ℓ ≤ ‖ϑ w‖)
    (hφb : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂,
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖ ≤ φb) :
    traceNorm ⟨spectralConvolutionFiniteSum (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
        x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s), spectralConvolutionFiniteSum_mem_nuclear _ x Λ K _ _⟩ ≤
      ((∑ z ∈ K, coshStripMult χ a α s z : ℕ) : ℝ) *
        (stripKernelNormConstant α β s * (rectInterpolantGaussianConstant X β 0 * (φb / ℓ * (1 + |τ₁|) ^ 2))) := by
  classical
  have hβ0 : 0 < β := hα.trans_lt hβ
  have hX : 0 < X := hβ0.trans hβX
  have hx : -X ≤ X := by linarith
  have hτ : τ₁ ≤ τ₂ := by linarith
  have hΦ := spectralStripTest_mellin_iteratedDeriv (F := F) (χ ω) φ
  let Φ : ℂ → ℂ := fun u ↦ ∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) (χ ω) u g ∂μ𝔽
  let θ : ℂ → ℂ := fun u ↦ ϑ u * Complex.exp ((u - τ₁ * Complex.I) ^ 2)
  have hθ : Differentiable ℂ θ := hϑ.mul (((differentiable_id.sub_const _).pow 2).cexp)
  have hθne (w : ℂ) (hw : w ∈ rectBoundary (-X) X τ₁ τ₂) : θ w ≠ 0 :=
    mul_ne_zero (fun h0 ↦ by have := hlow w hw; rw [h0, norm_zero] at this; linarith) (Complex.exp_ne_zero _)
  have hθord (z : CoshStripZero (F := F) χ a α) (hz : z.val.1 = ω) :
      ((coshStripMult χ a α s z : ℕ) : ℕ∞) ≤ analyticOrderAt θ ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) := by
    have hE : AnalyticAt ℂ (fun u : ℂ ↦ Complex.exp ((u - τ₁ * Complex.I) ^ 2))
        ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) := (((differentiable_id.sub_const _).pow 2).cexp).analyticAt _
    change _ ≤ analyticOrderAt (ϑ * fun u : ℂ ↦ Complex.exp ((u - τ₁ * Complex.I) ^ 2)) _
    rw [analyticOrderAt_mul (hϑ.analyticAt _) hE]; exact (hord z hz).trans le_self_add
  have hzero (z : CoshStripZero (F := F) χ a α) (hz : z.val.1 = ω) (hN : 0 < coshStripMult χ a α s z) :
      θ ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I) = 0 := by
    have h1 := hθord z hz; by_contra hne
    rw [(hθ.analyticAt _).analyticOrderAt_eq_zero.mpr hne] at h1
    have h2 : coshStripMult χ a α s z = 0 := by exact_mod_cast nonpos_iff_eq_zero.mp h1
    omega
  let m := rectInterpolant Φ θ (-X) X τ₁ τ₂
  have hm : Differentiable ℂ m := differentiable_rectInterpolant hΦ.1 hθ hx hτ hθne
  let B : ℝ := rectInterpolantGaussianConstant X β 0 * (φb / ℓ * (1 + |τ₁|) ^ 2)
  have hbound (u : ℂ) (hu : |u.re| ≤ β) : ‖m u‖ ≤ B / (1 + u.im ^ 2) := by
    have hg := norm_rectInterpolant_gaussian_le (A := 0) hϑ hΦ.1 hβ0 hβX hτ₁ hτ₂
      (fun v hv ↦ by simp [hgrowth v hv]) hℓ hlow hφb hu
    simpa [B] using hg
  obtain ⟨Ψ, hΨ_norm, hΨ_eval⟩ := exists_singleCluster_kernelOp hα hs hβ χ hχ Λ hj φ ω m hm B hbound
  have hre (z : CoshStripZero (F := F) χ a α) : ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I).re = z.val.2.1 := by simp
  have him (z : CoshStripZero (F := F) χ a α) : ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I).im = z.val.2.2 := by simp
  have hbX (z : CoshStripZero (F := F) χ a α) : -X < z.val.2.1 ∧ z.val.2.1 < X :=
    ⟨by linarith [z.property.1.1], by linarith [z.property.1.2]⟩
  have hΨ_eq : Ψ = spectralConvolutionFiniteSum
      (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
      x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) := by
    ext1 v
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    have hev : ContinuousLinearMap.apply ℂ ℂ (Ψ v) = ContinuousLinearMap.apply ℂ ℂ
        (spectralConvolutionFiniteSum (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
          x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) v) := by
      apply ContinuousLinearMap.ext_on hb.2.2.2
      rintro _ ⟨j, rfl⟩
      let z : CoshStripZero (F := F) χ a α := ⟨(j.val.1, j.val.2.1, j.val.2.2.1),
        (SpectralStripJetIndex.mem_strip_order_pos hα j).1, (SpectralStripJetIndex.mem_strip_order_pos hα j).2⟩
      let m_idx : Fin (coshStripMult χ a α s z) := ⟨j.val.2.2.2, j.property⟩
      change Λ j (Ψ v) = Λ j (spectralConvolutionFiniteSum _ x Λ K _ _ v)
      rw [show j = coshStripJet χ a α s z m_idx from Subtype.ext rfl,
        spectralConvolutionFiniteSum_eval _ x Λ hb _ _ (coshStripJet_injective χ a α s) K z m_idx v]
      by_cases hz : z ∈ K
      · simp only [hz, ↓reduceIte]
        refine (hΨ_eval z).1 ⟨(hK_in z hz).1, fun q hq ↦ ?_⟩ v m_idx
        have hstrict : τ₁ < z.val.2.2 := by
          rcases (hK_in z hz).2.1.eq_or_lt with heq | hlt
          · exact absurd (hzero z (hK_in z hz).1 (Nat.zero_lt_of_lt hq))
              (hθne _ (mem_rectBoundary_horizontal (x := z.val.2.1) (y := z.val.2.2)
                ⟨(hbX z).1.le, (hbX z).2.le⟩ (Or.inl heq.symm)))
          · exact hlt
        rw [iteratedDeriv_rectInterpolant_of_mem hΦ.1 hθ hx hτ hθne
          (by rw [hre]; exact (hbX z).1) (by rw [hre]; exact (hbX z).2)
          (by rw [him]; exact hstrict) (by rw [him]; exact (hK_in z hz).2.2)
          (hθord z (hK_in z hz).1) hq, hΦ.2 q, (hK_in z hz).1]
      · simp only [hz, ↓reduceIte]
        refine (hΨ_eval z).2 (fun hzc q hq ↦ ?_) v m_idx
        refine iteratedDeriv_rectInterpolant_of_notMem hΦ.1 hθ hx hτ hθne (fun hmem ↦ ?_) (hθord z hzc) hq
        obtain ⟨_, ht1, ht2⟩ := hmem; rw [him] at ht1 ht2
        rcases ht2.eq_or_lt with heq | hlt
        · exact hθne _ (mem_rectBoundary_horizontal (x := z.val.2.1) (y := z.val.2.2)
            ⟨(hbX z).1.le, (hbX z).2.le⟩ (Or.inr heq)) (hzero z hzc (Nat.zero_lt_of_lt hq))
        · exact hz (hK_all z hzc ht1 hlt)
    exact fun ℓ ↦ DFunLike.congr_fun hev ℓ
  have htr := traceNorm_spectralConvolutionFiniteSum_le
    (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
    x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)
  have hFsum_norm : ‖spectralConvolutionFiniteSum
      (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
      x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)‖ = ‖Ψ‖ := congrArg norm hΨ_eq.symm
  rw [hFsum_norm] at htr
  exact htr.trans (mul_le_mul_of_nonneg_left hΨ_norm (Nat.cast_nonneg _))

/-- Orthogonal lift of `quotClusterProj` onto `CoshIntervalSobolev F α s`. -/
def coshClusterProj (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {J Z : Type*} (x : J → spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : J → StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    CoshIntervalSobolev F α s →L[ℂ] CoshIntervalSobolev F α s :=
  let Φ := (coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap
  let Φi := (coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap
  (coshIsometricSection (F := F) a hα hs).comp
    (Φi.comp ((quotClusterProj x Λ K N jet).comp (Φ.comp (coshQuotMk (F := F) a hα hs))))

lemma coshClusterProj_mem_nuclear (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {J Z : Type*} (x : J → spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : J → StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    IsNuclearOperator (coshClusterProj (F := F) a hα hs x Λ K N jet) := by
  let Φ := (coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap
  let Φi := (coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap
  have hq : IsNuclearOperator (quotClusterProj x Λ K N jet) := by
    change (quotClusterProj x Λ K N jet) ∈ nuclearEndomorphisms _
    unfold quotClusterProj
    refine Submodule.sum_mem _ fun z _ ↦ Submodule.sum_mem _ fun m _ ↦ ?_
    exact smulRight_mem_nuclearEndomorphisms (Λ (jet z m)) (x (jet z m))
  have hsw := (traceNorm_sandwich_le (quotClusterProj x Λ K N jet) hq
    (Φ.comp (coshQuotMk (F := F) a hα hs))
    ((coshIsometricSection (F := F) a hα hs).comp Φi)).1
  have heq : coshClusterProj (F := F) a hα hs x Λ K N jet =
      ((coshIsometricSection (F := F) a hα hs).comp Φi).comp
        ((quotClusterProj x Λ K N jet).comp (Φ.comp (coshQuotMk (F := F) a hα hs))) := by
    ext1 u; rfl
  rw [heq]
  exact hsw

lemma coshSpectralProjection_comp_coshClusterProj (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {J Z : Type*} (x : J → spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : J → StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (K : Finset Z) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J) :
    (coshSpectralProjection (F := F) a hα hs).comp (coshClusterProj (F := F) a hα hs x Λ K N jet) =
      coshClusterProj (F := F) a hα hs x Λ K N jet := by
  have h1 : (coshSpectralProjection (F := F) a hα hs).comp
      (coshIsometricSection (F := F) a hα hs) = coshIsometricSection (F := F) a hα hs := by
    rw [← coshIsometricSection_comp_quotMk a hα hs, ContinuousLinearMap.comp_assoc,
      coshQuotMk_comp_isometricSection a hα hs, ContinuousLinearMap.comp_id]
  dsimp only [coshClusterProj]
  rw [← ContinuousLinearMap.comp_assoc (coshSpectralProjection _ _ _), h1]

lemma coshSpectral_comp_testAction_comp_coshClusterProj (a : ℝ) {α s : ℝ} (hα : 0 ≤ α)
    (hs : 0 ≤ s) (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (K : Finset (CoshStripZero (F := F) χ a α)) :
    ((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ)).comp
        (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)) =
      ((coshIsometricSection (F := F) a hα hs).comp
          (coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap).comp
        ((spectralConvolutionFiniteSum
            (spectralConvolution (F := F) a ((neg_nonpos.mpr hα).trans hα) hs φ)
            x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)).comp
          ((coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap.comp
            (coshQuotMk (F := F) a hα hs))) := by
  let hI := (neg_nonpos.mpr hα).trans hα
  let Φ := (coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap
  let Φi := (coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap
  have hintw : Φi.comp (spectralConvolution (F := F) a hI hs φ) =
      (coshSpectralConvolution (F := F) a hα hs φ).comp Φi := by
    ext1 q
    apply (coshQuotientEquiv a hα hs).injective
    dsimp only [Φ, Φi]
    change (coshQuotientEquiv a hα hs)
        ((coshQuotientEquiv a hα hs).symm (spectralConvolution a hI hs φ q)) =
      (coshQuotientEquiv a hα hs)
        ((coshSpectralConvolution a hα hs φ) ((coshQuotientEquiv a hα hs).symm q))
    rw [(coshQuotientEquiv a hα hs).apply_symm_apply]
    have hi := DFunLike.congr_fun (coshSpectralConvolution_intertwines (F := F) a hα hs φ)
      ((coshQuotientEquiv a hα hs).symm q)
    change (coshQuotientEquiv a hα hs)
        ((coshSpectralConvolution a hα hs φ) ((coshQuotientEquiv a hα hs).symm q)) =
      spectralConvolution a hI hs φ
        ((coshQuotientEquiv a hα hs) ((coshQuotientEquiv a hα hs).symm q)) at hi
    rw [hi, (coshQuotientEquiv a hα hs).apply_symm_apply]
  ext1 u
  have hstep1 := DFunLike.congr_fun
    (coshSpectralProjection_comp_testAction_comp_section (F := F) a hα hs φ)
    (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) u)
  change ((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ))
      (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) u) = _
  rw [hstep1]
  have hmk : coshQuotMk (F := F) a hα hs
      (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s) u) =
      Φi ((quotClusterProj x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s))
        (Φ (coshQuotMk (F := F) a hα hs u))) := by
    dsimp only [coshClusterProj]
    exact DFunLike.congr_fun (coshQuotMk_comp_isometricSection a hα hs) _
  have hintw_u := DFunLike.congr_fun hintw
    ((quotClusterProj x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s))
      (Φ (coshQuotMk (F := F) a hα hs u)))
  have hcomp_u := DFunLike.congr_fun
    (spectralConvolution_comp_quotClusterProj hα hs χ x Λ hb hj φ K)
    (Φ (coshQuotMk (F := F) a hα hs u))
  change coshIsometricSection a hα hs
      ((coshSpectralConvolution a hα hs φ)
        (coshQuotMk a hα hs (coshClusterProj a hα hs x Λ K _ _ u))) = _
  rw [hmk]
  change coshIsometricSection a hα hs ((coshSpectralConvolution a hα hs φ ∘L Φi)
    (quotClusterProj x Λ K _ _ (Φ (coshQuotMk a hα hs u)))) = _
  rw [← hintw_u]
  exact congrArg (fun v ↦ coshIsometricSection a hα hs (Φi v)) hcomp_u

lemma traceNorm_coshSpectral_cluster_le {a α s β X : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (hβ : α < β) (hβX : β < X)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (hχ : IsSpectralBasepointChoice (F := F) χ)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (ω : PontryaginDual (ideleClassNorm F).ker)
    (τ₁ τ₂ : ℝ) (hτ₁ : τ₁ + 1 ≤ τ₂) (hτ₂ : τ₂ ≤ τ₁ + 3)
    (K : Finset (CoshStripZero (F := F) χ a α))
    (hK_in : ∀ z ∈ K, z.val.1 = ω ∧ τ₁ ≤ z.val.2.2 ∧ z.val.2.2 < τ₂)
    (hK_all : ∀ z : CoshStripZero (F := F) χ a α, z.val.1 = ω → τ₁ ≤ z.val.2.2 → z.val.2.2 < τ₂ → z ∈ K)
    (ϑ : ℂ → ℂ) (hϑ : Differentiable ℂ ϑ)
    (hgrowth : ∀ u : ℂ, |u.re| ≤ X + 2 → ‖ϑ u‖ ≤ 1)
    (hord : ∀ z : CoshStripZero (F := F) χ a α, z.val.1 = ω →
      ((coshStripMult χ a α s z : ℕ) : ℕ∞) ≤
        analyticOrderAt ϑ ((z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I))
    (ℓ φb : ℝ) (hℓ : 0 < ℓ)
    (hlow : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂, ℓ ≤ ‖ϑ w‖)
    (hφb : ∀ w ∈ rectBoundary (-X) X τ₁ τ₂,
      ‖∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽‖ ≤ φb) :
    traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ)).comp
          (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)),
        mul_mem_nuclearEndomorphisms_left
          ((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ))
          ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩⟩ ≤
      (‖(coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap‖ *
          ‖(coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap‖) *
        (((∑ z ∈ K, coshStripMult χ a α s z : ℕ) : ℝ) *
          (stripKernelNormConstant α β s *
            (rectInterpolantGaussianConstant X β 0 * (φb / ℓ * (1 + |τ₁|) ^ 2)))) := by
  have hsingle := traceNorm_singleCluster_quotient_le hα hs hβ hβX χ hχ x Λ hb hj φ ω
    τ₁ τ₂ hτ₁ hτ₂ K hK_in hK_all ϑ hϑ hgrowth hord ℓ φb hℓ hlow hφb
  let hI := (neg_nonpos.mpr hα).trans hα
  let A := spectralConvolution (F := F) a hI hs φ
  let Fsum := spectralConvolutionFiniteSum A x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)
  let Φ := (coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap
  let Φi := (coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap
  let B := Φ.comp (coshQuotMk (F := F) a hα hs)
  let C := (coshIsometricSection (F := F) a hα hs).comp Φi
  obtain ⟨hsw, hsw_le⟩ := traceNorm_sandwich_le Fsum
    (spectralConvolutionFiniteSum_mem_nuclear A x Λ K _ _) B C
  have heq := coshSpectral_comp_testAction_comp_coshClusterProj a hα hs χ x Λ hb hj φ K
  have hCB : ‖C‖ * ‖B‖ ≤ ‖Φi‖ * ‖Φ‖ := by
    have hC : ‖C‖ ≤ ‖Φi‖ := by
      calc ‖(coshIsometricSection (F := F) a hα hs).comp Φi‖
          ≤ ‖coshIsometricSection (F := F) a hα hs‖ * ‖Φi‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ 1 * ‖Φi‖ := mul_le_mul_of_nonneg_right (norm_coshIsometricSection_le_one a hα hs) (norm_nonneg _)
        _ = ‖Φi‖ := one_mul _
    have hB : ‖B‖ ≤ ‖Φ‖ := by
      calc ‖Φ.comp (coshQuotMk (F := F) a hα hs)‖
          ≤ ‖Φ‖ * ‖coshQuotMk (F := F) a hα hs‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ ‖Φ‖ * 1 := mul_le_mul_of_nonneg_left (norm_coshQuotMk_le_one a hα hs) (norm_nonneg _)
        _ = ‖Φ‖ := mul_one _
    exact mul_le_mul hC hB (norm_nonneg _) (norm_nonneg _)
  have htn_nn : 0 ≤ traceNorm ⟨Fsum, spectralConvolutionFiniteSum_mem_nuclear A x Λ K _ _⟩ :=
    traceNorm_nonneg_of_hilbert ⟨Fsum, _⟩
  have hsub : (⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ)).comp
        (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)),
      mul_mem_nuclearEndomorphisms_left
        ((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ))
        ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩⟩ :
        nuclearEndomorphisms (CoshIntervalSobolev F α s)) = ⟨C.comp (Fsum.comp B), hsw⟩ :=
    Subtype.ext heq
  calc traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ)).comp _, _⟩
      = traceNorm ⟨C.comp (Fsum.comp B), hsw⟩ := congrArg traceNorm hsub
    _ ≤ (‖C‖ * ‖B‖) * traceNorm ⟨Fsum, _⟩ := hsw_le
    _ ≤ (‖Φi‖ * ‖Φ‖) * traceNorm ⟨Fsum, _⟩ := mul_le_mul_of_nonneg_right hCB htn_nn
    _ ≤ _ := mul_le_mul_of_nonneg_left hsingle (mul_nonneg (norm_nonneg _) (norm_nonneg _))

lemma traceNorm_coshSpectral_cluster_eq_zero {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))
    (φ : BruhatCompactSupport C𝔽) (ω : PontryaginDual (ideleClassNorm F).ker)
    (K : Finset (CoshStripZero (F := F) χ a α)) (hK : ∀ z ∈ K, z.val.1 = ω)
    (hvan : ∀ w : ℂ, ∫ g : C𝔽, φ.val g * ideleClassNormTwist (F := F) (χ ω) w g ∂μ𝔽 = 0) :
    traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ)).comp
          (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)),
        mul_mem_nuclearEndomorphisms_left
          ((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ))
          ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩⟩ = 0 := by
  have h0 := traceNorm_singleCluster_quotient_eq_zero hα hs χ x Λ hb hj φ ω K hK hvan
  let hI := (neg_nonpos.mpr hα).trans hα
  let A := spectralConvolution (F := F) a hI hs φ
  let Fsum := spectralConvolutionFiniteSum A x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)
  let Φ := (coshQuotientEquiv (F := F) a hα hs).toContinuousLinearMap
  let Φi := (coshQuotientEquiv (F := F) a hα hs).symm.toContinuousLinearMap
  obtain ⟨hsw, hsw_le⟩ := traceNorm_sandwich_le Fsum
    (spectralConvolutionFiniteSum_mem_nuclear A x Λ K _ _)
    (Φ.comp (coshQuotMk (F := F) a hα hs)) ((coshIsometricSection (F := F) a hα hs).comp Φi)
  have hsub : (⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ)).comp
        (coshClusterProj (F := F) a hα hs x Λ K (coshStripMult χ a α s) (coshStripJet χ a α s)),
      mul_mem_nuclearEndomorphisms_left
        ((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ))
        ⟨_, coshClusterProj_mem_nuclear a hα hs x Λ K _ _⟩⟩ :
        nuclearEndomorphisms (CoshIntervalSobolev F α s)) = ⟨_, hsw⟩ :=
    Subtype.ext (coshSpectral_comp_testAction_comp_coshClusterProj a hα hs χ x Λ hb hj φ K)
  refine le_antisymm ?_ (traceNorm_nonneg_of_hilbert _)
  calc traceNorm ⟨((coshSpectralProjection (F := F) a hα hs).comp (coshTestAction hα hs φ)).comp _, _⟩
      = traceNorm ⟨_, hsw⟩ := congrArg traceNorm hsub
    _ ≤ _ * traceNorm ⟨Fsum, _⟩ := hsw_le
    _ = 0 := by rw [h0, mul_zero]

end SpectralClusterMachinery

end RiemannMasullo.Isolated.CoshPositiveWidth
