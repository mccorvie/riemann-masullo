module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2_RatActualThetaEulerPointwise
import RiemannMasullo.AppA_AlgebraicNT.Sec2
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
public import RiemannMasullo.External.TauCeti.MeasureTheory.Function.Lp.Translation
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! # Logarithmic Hilbert realization of actual rational standard theta

The positive canonical norm section gives the correct finite-place angular
representative. The half-twist of a Schwartz real source lies in logarithmic
L², and the full finite-place cone converges there absolutely. -/

public noncomputable section

namespace RiemannMasullo.RatActualThetaEulerPointwise

open NumberField IsDedekindDomain InfinitePlace.Completion RatFinitePositiveUnitRep MeasureTheory
open scoped Classical NumberField.AdeleRing NNReal

local notation "V" => HeightOneSpectrum (𝓞 ℚ)

private def expNorm : ℝ ≃ₜ ℝ≥0ˣ :=
  Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm

/-- The rational canonical norm section projected to the selected completions. -/
def logChart (S : Finset V) (t : ℝ) : (SAdeleRing ℚ S)ˣ :=
  Units.map (adeleProjection ℚ S).toMonoidHom (canonicalIdeleNormSection ℚ (expNorm t))

theorem realCoord_logChart (S : Finset V) (t : ℝ) :
    realCoord S (logChart S t) = Real.exp t := by
  apply Complex.ofReal_injective
  change (extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
    ((canonicalIdeleNormSection ℚ (expNorm t)).val.1 Rat.infinitePlace) : ℂ) = _
  rw [extensionEmbeddingOfIsReal_apply, canonicalIdeleNormSection_infinite]
  simp [expNorm, Module.finrank_self]
  rw [← Complex.ofReal_exp]
  rfl

theorem normalized_logChart (S : Finset V) (t : ℝ) : Normalized S (logChart S t) := by
  refine ⟨(realCoord_logChart S t).symm ▸ Real.exp_pos t, fun v ↦ ?_⟩
  change Valued.v ((canonicalIdeleNormSection ℚ (expNorm t)).val.2 v.val) = 1
  rw [canonicalIdeleNormSection_finite]
  change Valued.v (1 : v.val.adicCompletion ℚ) = 1
  exact map_one _

@[simp] theorem radius_logChart (S : Finset V) (t : ℝ) : radius S (logChart S t) = Real.exp t :=
  (norm_normalized S (normalized_logChart S t)).trans (realCoord_logChart S t)

/-- Substituting `r = exp t` absorbs the squared half-twist exactly. -/
theorem memLp_halfProfile_log_of_integrableOn {phi : ℝ → ℂ} (hc : Continuous phi)
    (hi : IntegrableOn (fun r ↦ ‖signedProfile phi r‖ ^ 2) (Set.Ioi 0)) :
    MemLp (fun t ↦ halfProfile phi (Real.exp t)) 2 volume := by
  have hs : Continuous (signedProfile phi) := by
    simp_rw [show signedProfile phi = fun r ↦ phi r + phi (-r) from
      funext (signedProfile_apply phi)]
    exact hc.add (hc.comp continuous_neg)
  have hc' : Continuous (fun t ↦ halfProfile phi (Real.exp t)) := by
    simp only [halfProfile_apply]
    exact (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp Real.continuous_exp)).mul
      (hs.comp Real.continuous_exp)
  apply (memLp_two_iff_integrable_sq_norm hc'.aestronglyMeasurable).2
  have h := (integrable_comp_exp (fun r ↦ ‖signedProfile phi r‖ ^ 2)).2 hi
  simpa only [halfProfile_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (Real.exp_pos _).le,
    smul_eq_mul] using h

/-- Schwartz decay supplies square integrability of the signed archimedean profile. -/
theorem schwartz_memLp_halfProfile_log (phi : SchwartzMap ℝ ℂ) :
    MemLp (fun t ↦ halfProfile phi (Real.exp t)) 2 volume := by
  apply memLp_halfProfile_log_of_integrableOn phi.continuous
  have hp := phi.memLp 2 (volume : Measure ℝ)
  have hn := hp.comp_measurePreserving (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hs : MemLp (signedProfile phi) 2 (volume : Measure ℝ) := by
    rw [show signedProfile phi = fun r ↦ phi r + phi (-r) from funext (signedProfile_apply phi)]
    exact hp.add hn
  exact ((memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).1 hs).integrableOn

end RiemannMasullo.RatActualThetaEulerPointwise

namespace RiemannMasullo.RatFiniteEulerLogLpSeries
open MeasureTheory NumberField IsDedekindDomain RatFinitePositiveUnitRep RatUnramifiedThetaLattice
open RatActualThetaEulerPointwise
open scoped Classical NumberField.AdeleRing

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "rc" => InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
abbrev LogL2 := Lp ℂ 2 (volume : Measure ℝ)

private theorem cone_pos {S : Finset V} (n : S → ℕ) : 0 < latticeRadius n :=
  Finset.prod_pos fun v _ ↦ pow_pos (Nat.cast_pos.mpr
    (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val))) _

private theorem sqrt_natPow (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    Real.sqrt (a ^ k) = (Real.sqrt a) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (pow_nonneg ha _), ih, pow_succ]

private def ratio (v : V) : ℝ := (Real.sqrt (v.asIdeal.absNorm : ℝ))⁻¹

private theorem ratio_lt (v : V) : ratio v < 1 := by
  have h : (1 : ℝ) < v.asIdeal.absNorm := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  apply inv_lt_one_of_one_lt₀
  simpa using Real.sqrt_lt_sqrt zero_le_one h

/-- Product of the masses of the local geometric kernels. -/
def chartBound (S : Finset V) : ℝ := ∏ v : S, (1 - (Real.sqrt (v.val.asIdeal.absNorm : ℝ))⁻¹)⁻¹

theorem chartBound_nonneg (S : Finset V) : 0 ≤ chartBound S :=
  Finset.prod_nonneg fun v _ ↦ inv_nonneg.mpr (sub_nonneg.mpr (ratio_lt v.val).le)

/-- Dominate each finite subsum by its rectangular hull, then sum each geometric factor. -/
private theorem coneMass_partial_le (S : Finset V) (A : Finset (S → ℕ)) :
    (∑ n ∈ A, (Real.sqrt (latticeRadius n))⁻¹) ≤ chartBound S := by
  classical
  let b (v : S) := ratio v.val
  have hb (v : S) : 0 ≤ b v := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have factor (n : S → ℕ) : (Real.sqrt (latticeRadius n))⁻¹ = ∏ v, b v ^ n v := by
    rw [latticeRadius, Real.sqrt_prod _ (fun _ _ ↦ by positivity), ← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro v _
    rw [sqrt_natPow _ (by positivity)]
    exact (inv_pow _ _).symm
  simp_rw [factor]
  let K (v : S) := A.image (fun n ↦ n v)
  calc
    _ ≤ ∑ n ∈ Fintype.piFinset K, ∏ v, b v ^ n v := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        exact Fintype.mem_piFinset.mpr fun v ↦ Finset.mem_image_of_mem _ hn
      · exact fun n _ _ ↦ Finset.prod_nonneg fun v _ ↦ pow_nonneg (hb v) _
    _ = ∏ v, ∑ k ∈ K v, b v ^ k := (Finset.prod_univ_sum K _).symm
    _ ≤ chartBound S := by
      apply Finset.prod_le_prod₀ (fun v _ ↦ Finset.sum_nonneg fun k _ ↦ pow_nonneg (hb v) k)
      intro v _
      exact ((summable_geometric_of_lt_one (hb v) (ratio_lt v.val)).sum_le_tsum _
        (fun k _ ↦ pow_nonneg (hb v) k)).trans_eq (tsum_geometric_of_lt_one (hb v) (ratio_lt v.val))

theorem weight_summable (S : Finset V) : Summable fun n : S → ℕ ↦ (Real.sqrt (latticeRadius n))⁻¹ :=
  summable_of_sum_le (c := chartBound S) (fun _ ↦ inv_nonneg.mpr (Real.sqrt_nonneg _))
    (coneMass_partial_le S)

theorem coneMass_le (S : Finset V) : (∑' n : S → ℕ, (Real.sqrt (latticeRadius n))⁻¹) ≤ chartBound S := by
  exact le_of_tendsto (weight_summable S).hasSum (Filter.Eventually.of_forall (coneMass_partial_le S))

def coneTerm {S : Finset V} (P : LogL2) (n : S → ℕ) : LogL2 :=
  (Real.sqrt (latticeRadius n) : ℂ)⁻¹ • Measure.translateLp volume 2 (Real.log (latticeRadius n)) P

theorem norm_coneTerm_summable (S : Finset V) (P : LogL2) :
    Summable fun n : S → ℕ ↦ ‖coneTerm P n‖ := by
  simpa only [coneTerm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), LinearIsometryEquiv.norm_map] using
    (weight_summable S).mul_right ‖P‖

def chartSeries (S : Finset V) (P : LogL2) : LogL2 := ∑' n : S → ℕ, coneTerm P n

theorem chartSeries_hasSum (S : Finset V) (P : LogL2) :
    HasSum (fun n : S → ℕ ↦ coneTerm P n) (chartSeries S P) :=
  (norm_coneTerm_summable S P).of_norm.hasSum

/-- The chart of actual normalized representatives agrees with the absolutely convergent
log-translation series. No measurability of the choice of representatives is required. -/
theorem chartSeries_eq_halfTheta (S : Finset V) (f : B∞) (phi : ℝ → ℂ)
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = phi (rc (a Rat.infinitePlace)))
    (x : ℝ → (SAdeleRing ℚ S)ˣ) (hx : ∀ t, Normalized S (x t))
    (hr : ∀ t, radius S (x t) = Real.exp t) (P : LogL2)
    (hP : ⇑P =ᵐ[volume] fun t ↦ halfProfile phi (Real.exp t)) :
    ⇑(chartSeries S P) =ᵐ[volume] fun t ↦ halfTheta S f (x t) := by
  have terms (n : S → ℕ) : ∀ᵐ t : ℝ, coneTerm P n t =
      (Real.sqrt (latticeRadius n) : ℂ)⁻¹ * halfProfile phi (radius S (x t) * latticeRadius n) := by
    let h := Real.log (latticeRadius n)
    filter_upwards [Lp.coeFn_smul ((Real.sqrt (latticeRadius n) : ℂ)⁻¹)
        (Measure.translateLp volume 2 h P), Measure.coeFn_translateLp h P,
      (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hP] with t hc ht hp
    change coneTerm P n t = (Real.sqrt (latticeRadius n) : ℂ)⁻¹ *
      (Measure.translateLp volume 2 h P) t at hc
    change (Measure.translateLp volume 2 h P) t = P (t + h) at ht
    change P (t + h) = halfProfile phi (Real.exp (t + h)) at hp
    rw [hc, ht, hp, Real.exp_add, show Real.exp h = latticeRadius n from Real.exp_log (cone_pos n), hr]
  filter_upwards [ae_all_iff.mpr terms, Lp.hasSum_coeFn_tsum
    (tsum_eNorm_ne_top_iff_summable_norm.mpr (norm_coneTerm_summable S P))] with t ht hs
  exact hs.unique ((halfTheta_lattice_hasSum f phi hf S (x t) (hx t)).congr_fun (ht))

/-- An actual standard tensor with a Schwartz real profile has the claimed logarithmic
half-density in `L²(dt)`, represented by the absolutely convergent finite-place Euler cone. -/
theorem halfTheta_logChart_memLp (S : Finset V) (f : B∞) (phi : SchwartzMap ℝ ℂ)
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = phi (rc (a Rat.infinitePlace))) :
    MemLp (fun t ↦ halfTheta S f (logChart S t)) 2 volume := by
  let h := schwartz_memLp_halfProfile_log phi
  let P := h.toLp (fun t ↦ halfProfile phi (Real.exp t))
  exact (Lp.memLp (chartSeries S P)).ae_eq (chartSeries_eq_halfTheta S f phi hf (logChart S)
    (normalized_logChart S) (radius_logChart S) P h.coeFn_toLp)

theorem norm_chartSeries_le (S : Finset V) (P : LogL2) : ‖chartSeries S P‖ ≤ chartBound S * ‖P‖ := by
  rw [chartSeries]
  refine (norm_tsum_le_tsum_norm (norm_coneTerm_summable S P)).trans ?_
  simp only [coneTerm, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), LinearIsometryEquiv.norm_map, tsum_mul_right]
  exact mul_le_mul_of_nonneg_right (coneMass_le S) (norm_nonneg _)

private theorem translate_complex_smul (h : ℝ) (c : ℂ) (P : LogL2) :
    Measure.translateLp volume 2 h (c • P) = c • Measure.translateLp volume 2 h P := by
  apply Lp.ext
  filter_upwards [Measure.coeFn_translateLp h (c • P), Lp.coeFn_smul c (Measure.translateLp volume 2 h P),
    Measure.coeFn_translateLp h P, (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_smul c P)] with t ha hb hc hd
  simp only [Function.comp_apply, Pi.smul_apply] at ha hb hc hd
  exact ha.trans (hd.trans ((congrArg (c • ·) hc.symm).trans hb.symm))

/-- The finite Euler cone defines a bounded complex-linear operator on logarithmic L². -/
def chartOperator (S : Finset V) : LogL2 →L[ℂ] LogL2 :=
  LinearMap.mkContinuous
    ({ toFun := chartSeries S
       map_add' := fun P Q ↦ (chartSeries_hasSum S (P + Q)).unique (by
         simpa only [coneTerm, map_add, smul_add] using (chartSeries_hasSum S P).add (chartSeries_hasSum S Q))
       map_smul' := fun c P ↦ (chartSeries_hasSum S (c • P)).unique (by
         simpa only [coneTerm, translate_complex_smul, RingHom.id_apply, smul_comm c] using
           (chartSeries_hasSum S P).const_smul c) } : LogL2 →ₗ[ℂ] LogL2)
    (chartBound S) (norm_chartSeries_le S)

@[simp] theorem chartOperator_apply (S : Finset V) (P : LogL2) :
    chartOperator S P = chartSeries S P := by
  unfold chartOperator
  rfl

theorem norm_chartOperator_le (S : Finset V) : ‖chartOperator S‖ ≤ chartBound S :=
  (chartOperator S).opNorm_le_bound (chartBound_nonneg S) (norm_chartSeries_le S)

/-- The Hilbert class of the actual half-density. -/
def actualChartL2 (S : Finset V) (f : B∞) (phi : SchwartzMap ℝ ℂ)
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = phi (rc (a Rat.infinitePlace))) : LogL2 :=
  (halfTheta_logChart_memLp S f phi hf).toLp _

theorem actualChartL2_eq_chartOperator (S : Finset V) (f : B∞) (phi : SchwartzMap ℝ ℂ)
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = phi (rc (a Rat.infinitePlace))) :
    actualChartL2 S f phi hf = chartOperator S ((schwartz_memLp_halfProfile_log phi).toLp _) := by
  apply Lp.ext
  exact (halfTheta_logChart_memLp S f phi hf).coeFn_toLp.trans (chartSeries_eq_halfTheta S f phi hf
    (logChart S) (normalized_logChart S) (radius_logChart S) _ (schwartz_memLp_halfProfile_log phi).coeFn_toLp).symm

/-- One finite-place Euler difference of actual rational standard tensors, in the Hilbert space. -/
theorem actualChartL2_insert_euler (T : Finset V) (v : V) (hv : v ∉ T) (f : B∞) (phi : SchwartzMap ℝ ℂ)
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = phi (rc (a Rat.infinitePlace))) :
    actualChartL2 (insert v T) f phi hf - (Real.sqrt (v.asIdeal.absNorm : ℝ) : ℂ)⁻¹ •
      Measure.translateLp volume 2 (Real.log (v.asIdeal.absNorm : ℝ)) (actualChartL2 (insert v T) f phi hf) =
      actualChartL2 T f phi hf := by
  let S := insert v T
  let q : ℝ := v.asIdeal.absNorm
  let a : ℂ := (Real.sqrt q : ℂ)⁻¹
  let F := actualChartL2 S f phi hf
  let U := Measure.translateLp volume 2 (Real.log q) F
  have hq : 0 < q := Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub F (a • U), Lp.coeFn_smul a U,
    (halfTheta_logChart_memLp S f phi hf).coeFn_toLp,
    (halfTheta_logChart_memLp S f phi hf).coeFn_translateLp_toLp (Real.log q),
    (halfTheta_logChart_memLp T f phi hf).coeFn_toLp] with t he hs hF hU hT
  change (F - a • U) t = actualChartL2 T f phi hf t
  change (F - a • U) t = F t - (a • U) t at he
  change (a • U) t = a * U t at hs
  change F t = _ at hF
  change U t = _ at hU
  change actualChartL2 T f phi hf t = _ at hT
  have hshift : radius S (logChart S (t + Real.log q)) = radius S (logChart S t) * q := by
    rw [radius_logChart, radius_logChart, Real.exp_add, Real.exp_log hq]
  have hsame : radius T (logChart T t) = radius S (logChart S t) := by
    rw [radius_logChart, radius_logChart]
  rw [he, hs, hF, hU, hT]
  exact insert_euler_eq_halfTheta f phi hf T v hv _ _ _ (normalized_logChart S t)
    (normalized_logChart S (t + Real.log q)) (normalized_logChart T t) hshift hsame

end RiemannMasullo.RatFiniteEulerLogLpSeries
