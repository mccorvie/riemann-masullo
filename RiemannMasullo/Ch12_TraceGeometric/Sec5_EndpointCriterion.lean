module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import RiemannMasullo.ForMathlib.Analysis.Complex.ExpSumCesaro
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Endpoint Cesàro criteria and fixed-width local-terms equivalences for Theorem 12.5.1.1

In `Sec5.lean`, relaxing the exact strip trace identity at half-width `α` to an integrable majorant
requires a strict exponent saving `c < α` when using Laplace analyticity on `Re z > c` alone, which
does not see zeros on the boundary `|Re s - 1/2| = c`. Moreover, at any single fixed width
`0 < α < 1/2`, asking for an exponent `c < α` on the signed local terms is strictly stronger than
`IsEmpty exteriorZeros(τ, α)`, since interior zeros in `|Re s - 1/2| < α` could approach the edges
as `|Im s| → ∞`.

Using the horizontal Abel–Laplace residue formula and zero-saving Cesàro uniqueness from
`ExpSumCesaro.lean`, we eliminate the `c < α` slack completely:

1. (`isEmpty_exteriorZeros_of_cesaro`, `isEmpty_exteriorZeros_of_endpoint_integrable`,
   `isEmpty_exteriorZeros_of_tendsto_zero`) At any half-width `α`, Cesàro mean `o(exp(α y))` (in
   particular `o(exp(α y))` pointwise or endpoint `L¹(exp(-α y))`, requiring **no** power saving
   below `α`) on polar-free translated tests supported above norm one excludes all exterior zeros
   in `|Re s - 1/2| ≥ α`, boundary included.
2. (`traceFormula_exteriorZeros_of_stripTrace_cesaro`,
   `traceFormula_exteriorZeros_of_stripTrace_endpoint_integrable`) The strip-trace defect comparison
   for Theorem 12.5.1.1 needs no `c < β` exponent saving and no global kernel `hK`.
3. (`hasSum_exteriorZeros_iff_localTerms_tendsto_zero`,
   `hasSum_exteriorZeros_iff_localTerms_cesaro`) At **every individual fixed half-width `α > 0`**,
   the exterior-zero vanishing of `traceFormula_exteriorZeros` is **equivalent (`↔`)** to `o(exp(α y))`
   decay (and to Cesàro `o(exp(α y))` decay) of the pure non-polar local terms of polar-free
   translated tests supported above norm one.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ContDiff

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSpectralQuotientPolynormableSec3

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" => (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ :
  IsModulation m𝔽)
local notation "M(" φ ", " c ")" =>
  modulatedFourierMellin m𝔽 univ hm𝔽 μ𝔽 (φ : BruhatCompactSupport C𝔽).val c
local notation "twist(" χ ", " s ")" => ideleClassNormTwist (F := F) χ s
local notation "ord(" χ ", " s ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ s
local notation "order(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) χ) z
local notation "interiorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ |z.2.re - 1 / 2| < α}
local notation "exteriorZeros(" τ ", " α ")" =>
  {z : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
    0 < ord(z.1.val, z.2) ∧ α ≤ |z.2.re - 1 / 2|}
local notation "characterZeros(" ψ ")" => {s : ℂ // 0 < ord(ψ, s)}
local notation "zeroTerm(" φ ", " z ")" =>
  ((ord((z).val.1.val, (z).val.2) : ℤ) : ℂ) * M(φ, twist((z).val.1.val, (z).val.2 - 1 / 2))
local notation "classVolume" => (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : V) → BruhatCompactSupport (v.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "finiteTerm(" v ", " b ")" =>
  ((Real.log ((v : V).asIdeal.absNorm : ℝ) / finiteVolume(v) : ℝ) : ℂ) *
    finiteConnesWeilPrincipalValue v 1 b
local notation "localTerms(" φ ", " a ", " b ")" =>
  (M(φ, twist(1, 1 / 2)) + M(φ, twist(1, -1 / 2)) -
    classVolume * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
      ∑' v : V, finiteTerm(v, b v)))
local notation "nonpolarLocalTerms(" a ", " b ")" =>
  (-(classVolume * ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑' v : V, finiteTerm(v, b v))))
local notation "archRestricts(" φ ", " a ")" =>
  (∀ (w : InfinitePlace F) (u : w.Completionˣ), (a w).val u = (φ).val (archClass(w) u))
local notation "finiteRestricts(" φ ", " b ")" =>
  (∀ (v : V) (u : (v.adicCompletion F)ˣ), (b v).val u = (φ).val (finiteClass(v) u))
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "stripQuot(" hα ", " hs ")" =>
  spectralSobolevQuotient F (1 / 2) (hStrip(hα)) (le_of_lt (zero_lt_one.trans hs))
local notation "stripConv(" hα ", " hs ", " φ ")" =>
  spectralConvolution (F := F) (1 / 2) (hStrip(hα)) (le_of_lt (zero_lt_one.trans hs)) φ
local notation "three" => (show (1 : ℝ) < 3 by norm_num)
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "σ𝔽" => fun t : ℝ≥0ˣ ↦
  (QuotientGroup.mk (canonicalIdeleNormSection F t) : C𝔽)
local notation "translatedCoeff(" χ ", " H ", " z ")" =>
  ((ord(χ, (z : ℂ)) : ℤ) : ℂ) *
    (classVolume * ∫ x : ℝ, H x * Complex.exp (((z : ℂ) - 1 / 2) * x))

private theorem endpoint_isEmpty_half_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) {α : ℝ} (hα : 1 / 2 ≤ α) :
    IsEmpty exteriorZeros(τ, α) :=
  (hasSum_exteriorZeros_iff_isEmpty τ hτ α).mp fun φ _ ↦
    traceFormula_exteriorZeros_of_half_le τ φ hα

private theorem endpoint_mul_twist (p q a b n : ℂ) (h : p = q * a) :
    p * (b * n) = q * (b * a * n) := by
  rw [h]; ring

open Classical in
private theorem endpoint_characterNormTest_mellin (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g)
    (hgc : HasCompactSupport g) (ψ : PontryaginDual C𝔽) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ x, φ.val x = (ψ x : ℂ) * g (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ)))
    (χ : PontryaginDual C𝔽) (s : ℂ) :
    M(φ, twist(χ, s)) =
      (if ∀ u : C₁, (χ * ψ) u.val = 1 then classVolume else 0) *
        ∫ t, g (Real.log ((t : ℝ≥0) : ℝ)) * ((χ * ψ) (σ𝔽 t) : ℂ) * (((t : ℝ≥0) : ℝ) : ℂ) ^ s
          ∂positiveRealHaar := by
  obtain ⟨φr, hφr⟩ := exists_normTest (F := F) g hg hgc
  rw [← normTest_mellin g hg.continuous φr hφr (χ * ψ) s]
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  change φ.val x * ((χ x : ℂ) * (((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ s) =
    φr.val x * (((χ * ψ) x : ℂ) * (((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ s)
  rw [show (((χ * ψ) x : Circle) : ℂ) = (χ x : ℂ) * (ψ x : ℂ) from Circle.coe_mul _ _]
  exact endpoint_mul_twist _ _ _ _ _ ((hφ x).trans ((congrArg _ (hφr x)).symm.trans (mul_comm _ _)))

private theorem endpoint_character_eq (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    {χ χ₀ : PontryaginDual C𝔽} (h1 : ∀ t, χ (τ t) = 1) (h0 : ∀ t, χ₀ (τ t) = 1)
    (hC : ∀ u : C₁, (χ * χ₀⁻¹) u.val = 1) : χ = χ₀ := by
  refine ContinuousMonoidHom.ext fun x ↦ ?_
  let t := ideleClassNorm F x
  have hu : (τ t)⁻¹ * x ∈ C₁ := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hτ t, inv_mul_cancel]
  have key : ∀ ψ : PontryaginDual C𝔽, (∀ t, ψ (τ t) = 1) → ψ x = ψ ((τ t)⁻¹ * x) :=
    fun ψ hψ ↦ by rw [map_mul, map_inv, hψ, inv_one, one_mul]
  have h := hC ⟨_, hu⟩
  change χ ((τ t)⁻¹ * x) * (χ₀ ((τ t)⁻¹ * x))⁻¹ = 1 at h
  exact (key χ h1).trans ((mul_inv_eq_one.mp h).trans (key χ₀ h0).symm)

private theorem endpoint_classVolume_ne_zero : classVolume ≠ 0 := by
  have hvol := normOneIdeleClassTamagawaMeasure_volume (F := F)
  have hc0 : normOneIdeleClassTamagawaMeasure F univ ≠ 0 := by
    rw [hvol, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have := NumberField.Units.regulator_pos F
    have := NumberField.classNumber_pos F
    have := NumberField.Units.torsionOrder_pos F
    have : (0 : ℝ) < Real.sqrt (Int.natAbs (NumberField.discr F) : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast Int.natAbs_pos.mpr (NumberField.discr_ne_zero F))
    positivity
  have hct : normOneIdeleClassTamagawaMeasure F univ ≠ ⊤ := by
    rw [hvol]; exact ENNReal.ofReal_ne_top
  exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩)

private theorem endpoint_zeros_discrete (χ : PontryaginDual C𝔽) (z : ℂ) :
    ∀ᶠ u in 𝓝[≠] z, ¬ 0 < ord(χ, u + 1 / 2) := by
  have hD :=
    (MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ).eq_zero_codiscreteWithin
  have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hD) (z + 1 / 2) (mem_univ _)
  rw [compl_univ, union_empty] at h
  have ht : Tendsto (fun u : ℂ ↦ u + 1 / 2) (𝓝[≠] z) (𝓝[≠] (z + 1 / 2)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_id.add continuous_const).tendsto z).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact fun h' ↦ hu (add_right_cancel h')
  filter_upwards [ht.eventually h] with u hu
  change _ = (0 : ℤ) at hu
  rw [hu]; exact lt_irrefl 0

private theorem endpoint_zero_re_le_one (χ : PontryaginDual C𝔽) {s : ℂ} (hs : 0 < ord(χ, s)) :
    s.re ≤ 1 := by
  rcases le_or_gt s.re 0 with h | h
  · linarith
  · have hspec := continuedCompletedHeckeL_spec χ
    rw [MeromorphicOn.divisor_apply hspec.1.meromorphicOn (mem_univ s)] at hs
    have ho : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) s := by
      by_contra hle
      rw [not_lt] at hle
      obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp
        (ne_top_of_le_ne_top (WithTop.coe_ne_top (a := (0 : ℤ))) hle)
      rw [← hn, WithTop.untop₀_coe] at hs
      rw [← hn] at hle
      exact absurd (WithTop.coe_le_coe.mp hle) (not_le.mpr hs)
    exact (completedHeckeL_continuation_zeros χ _ hspec.1 hspec.2 h ho).le

private theorem endpoint_bump_mul_exp (b w : ℂ) : b * Complex.exp (-w) * Complex.exp w = b := by
  rw [mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]

private theorem endpoint_integral_deriv_mul_cexp (h : ℝ → ℂ) (hh : ContDiff ℝ (∞) h)
    (hc : HasCompactSupport h) (w : ℂ) :
    ∫ x : ℝ, deriv h x * Complex.exp (w * x) = -(w * ∫ x : ℝ, h x * Complex.exp (w * x)) := by
  have he (x : ℝ) :
      HasDerivAt (fun x : ℝ ↦ Complex.exp (w * x)) (w * Complex.exp (w * x)) x := by
    convert (((hasDerivAt_id' (x : ℂ)).const_mul w).cexp).comp_ofReal using 1
    ring
  have hce : Continuous fun x : ℝ ↦ Complex.exp (w * x) := by fun_prop
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ ↦ Complex.exp (w * x)) (u' := fun x ↦ w * Complex.exp (w * x))
    (v := h) (v' := deriv h) (fun x _ ↦ he x)
    (fun x _ ↦ ((hh.differentiable (by simp)) x).hasDerivAt)
    ((hce.mul (hh.continuous_deriv (by simp))).integrable_of_hasCompactSupport hc.deriv.mul_left)
    (((continuous_const.mul hce).mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hce.mul hh.continuous).integrable_of_hasCompactSupport hc.mul_left)
  calc ∫ x : ℝ, deriv h x * Complex.exp (w * x)
      = ∫ x : ℝ, Complex.exp (w * x) * deriv h x := by congr 1; funext x; ring
    _ = -∫ x : ℝ, w * Complex.exp (w * x) * h x := key
    _ = -(w * ∫ x : ℝ, h x * Complex.exp (w * x)) := by
        rw [← integral_const_mul]; congr 2; funext x; ring

private theorem endpoint_integral_polarFilter_mul_cexp (h : ℝ → ℂ) (hh : ContDiff ℝ (∞) h)
    (hc : HasCompactSupport h) (w : ℂ) :
    ∫ x : ℝ, (deriv (deriv h) x - 1 / 4 * h x) * Complex.exp (w * x) =
      (w ^ 2 - 1 / 4) * ∫ x : ℝ, h x * Complex.exp (w * x) := by
  have hh' : ContDiff ℝ (∞) (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have hce : Continuous fun x : ℝ ↦ Complex.exp (w * x) := by fun_prop
  have i1 : Integrable (fun x : ℝ ↦ deriv (deriv h) x * Complex.exp (w * x)) :=
    ((hh'.continuous_deriv (by simp)).mul hce).integrable_of_hasCompactSupport
      hc.deriv.deriv.mul_right
  have i0 : Integrable (fun x : ℝ ↦ h x * Complex.exp (w * x)) :=
    (hh.continuous.mul hce).integrable_of_hasCompactSupport hc.mul_right
  have hsplit : (fun x : ℝ ↦ (deriv (deriv h) x - 1 / 4 * h x) * Complex.exp (w * x)) =
      fun x ↦ deriv (deriv h) x * Complex.exp (w * x) -
        1 / 4 * (h x * Complex.exp (w * x)) := by
    funext x; ring
  rw [hsplit, integral_sub i1 (i0.const_mul _), integral_const_mul,
    endpoint_integral_deriv_mul_cexp _ hh' hc.deriv, endpoint_integral_deriv_mul_cexp _ hh hc]
  ring

private theorem endpoint_ord_reflection (χ : PontryaginDual C𝔽) (z : ℂ) :
    ord(χ⁻¹, 1 - z) = ord(χ, z) := by
  obtain ⟨hL, hl⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨hD, hd⟩ := continuedCompletedHeckeL_spec χ⁻¹
  obtain ⟨ε, hε, hne, hfe⟩ := completedHeckeL_continuation_functionalEquation χ _ _ hL hl hD hd
  have he : meromorphicOrderAt (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) z =
      meromorphicOrderAt (continuedCompletedHeckeL χ⁻¹) (1 - z) := by
    simpa [Function.comp_def] using meromorphicOrderAt_comp_of_deriv_ne_zero
      (f := continuedCompletedHeckeL χ⁻¹) (show AnalyticAt ℂ (fun s : ℂ ↦ 1 - s) z by fun_prop)
      (show deriv (fun s : ℂ ↦ 1 - s) z ≠ 0 by simp)
  rw [show (fun s ↦ continuedCompletedHeckeL χ⁻¹ (1 - s)) =
      ε * continuedCompletedHeckeL χ from funext hfe,
    meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt z) (hne z)] at he
  rw [MeromorphicOn.divisor_apply hD.meromorphicOn (mem_univ _),
    MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), ← he]

private theorem endpoint_localTerms_congr (φ : BruhatCompactSupport C𝔽)
    {a a' : archTest} {b b' : finiteTest} (ha : archRestricts(φ, a)) (hb : finiteRestricts(φ, b))
    (ha' : archRestricts(φ, a')) (hb' : finiteRestricts(φ, b')) :
    localTerms(φ, a, b) = localTerms(φ, a', b') := by
  have h1 : a = a' := funext fun w ↦ Subtype.ext (funext fun u ↦ (ha w u).trans (ha' w u).symm)
  have h2 : b = b' := funext fun v ↦ Subtype.ext (funext fun u ↦ (hb v u).trans (hb' v u).symm)
  rw [h1, h2]

open Classical in
private theorem endpoint_polar_mellin_eq_zero (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hH : ContDiff ℝ (∞) H) (hHc : HasCompactSupport H) (y : ℝ)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y))
    (s : ℂ) (hs : ∫ x : ℝ, H x * Complex.exp (s * x) = 0) :
    M(φ, twist(1, s)) = 0 := by
  have hsy : ContDiff ℝ (∞) (fun x ↦ H (x - y)) := hH.comp (contDiff_id.sub contDiff_const)
  have hcy : HasCompactSupport (fun x ↦ H (x - y)) := hHc.comp_homeomorph (Homeomorph.subRight y)
  rw [endpoint_characterNormTest_mellin _ hsy hcy ψ φ hφ]
  have hinv (t) : ψ⁻¹ (τ t) = 1 := by change (ψ (τ t))⁻¹ = 1; rw [hψ, inv_one]
  by_cases hχ : (1 : PontryaginDual C𝔽) = ψ⁻¹
  · have hone : (1 : PontryaginDual C𝔽) * ψ = 1 := by nth_rw 1 [hχ]; exact inv_mul_cancel ψ
    beta_reduce
    rw [grh_shift_integral H hH.continuous _ (fun t ↦ by rw [hone]; rfl) y, hs, mul_zero,
      mul_zero]
  · have hoff : ¬ ∀ u : C₁, ((1 : PontryaginDual C𝔽) * ψ) u.val = 1 := fun h1 ↦
      hχ (endpoint_character_eq τ hτ (fun _ ↦ PontryaginDual.one_apply _) hinv
        (by simpa [inv_inv] using h1))
    rw [ite_eq_right hoff, zero_mul]

/-- Construct the polar-filtered modulated bump centered at `1/2`, supported in `[3/8, 5/8] ⊂ (0, ∞)`
with vanishing polar moments at `±1/2` and nonzero Mellin transform at `w₀` when `|Re w₀| < 1/2`. -/
private theorem endpoint_exists_detecting_profile {w₀ : ℂ} (hw_strip : |w₀.re| < 1 / 2) :
    ∃ H₀ : ℝ → ℂ, ContDiff ℝ (∞) H₀ ∧ HasCompactSupport H₀ ∧ (∀ x ≤ 0, H₀ x = 0) ∧
      (∫ x : ℝ, H₀ x * Complex.exp ((1 / 2 : ℂ) * x) = 0) ∧
      (∫ x : ℝ, H₀ x * Complex.exp ((-1 / 2 : ℂ) * x) = 0) ∧
      (∫ x : ℝ, H₀ x * Complex.exp (w₀ * x) ≠ 0) := by
  let β : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  let h₀ : ℝ → ℂ := fun x ↦ (β x : ℂ) * Complex.exp (-(w₀ * x))
  have hh₀ : ContDiff ℝ (∞) h₀ :=
    (Complex.ofRealCLM.contDiff.comp β.contDiff).mul
      (Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff).neg)
  have hh₀c : HasCompactSupport h₀ :=
    (β.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  let H₀ : ℝ → ℂ := fun x ↦ deriv (deriv h₀) x - 1 / 4 * h₀ x
  have hoff : ∀ x, x ∉ tsupport h₀ → H₀ x = 0 := fun x hx ↦ by
    have h1 : deriv (deriv h₀) x = 0 :=
      deriv_of_notMem_tsupport fun h ↦ hx (tsupport_deriv_subset h)
    simp only [H₀, h1, image_eq_zero_of_notMem_tsupport hx, mul_zero, sub_zero]
  have hH₀ : ContDiff ℝ (∞) H₀ :=
    (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hh₀).2).2.sub
      (contDiff_const.mul hh₀)
  have hH₀c : HasCompactSupport H₀ := HasCompactSupport.intro hh₀c hoff
  have hH₀v : ∀ x ≤ 0, H₀ x = 0 := fun x hx ↦ by
    apply hoff
    rw [notMem_tsupport_iff_eventuallyEq]
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 8)] with x' hx'
    have hb : β x' = 0 := β.zero_of_le_dist (by
      rw [Metric.mem_ball, Real.dist_eq] at hx'
      rw [Real.dist_eq]
      change (1 / 4 : ℝ) ≤ _
      rw [abs_lt] at hx'
      rw [abs_of_neg (by linarith)]
      linarith)
    simp only [h₀, hb, Complex.ofReal_zero, zero_mul, Pi.zero_apply]
  have hfilt (s : ℂ) : ∫ x : ℝ, H₀ x * Complex.exp (s * x) =
      (s ^ 2 - 1 / 4) * ∫ x : ℝ, h₀ x * Complex.exp (s * x) :=
    endpoint_integral_polarFilter_mul_cexp h₀ hh₀ hh₀c s
  have hK' : ∫ x : ℝ, h₀ x * Complex.exp (w₀ * x) = ((∫ x, β x : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ endpoint_bump_mul_exp _ _)
  have hw₀ : w₀ ^ 2 - 1 / 4 ≠ 0 := by
    intro h
    have h' : (w₀ - 1 / 2) * (w₀ + 1 / 2) = 0 := by linear_combination h
    rw [abs_lt] at hw_strip
    rcases mul_eq_zero.mp h' with h'' | h''
    · have := congrArg Complex.re h''
      simp only [Complex.sub_re, Complex.zero_re] at this
      norm_num at this
      linarith [hw_strip.2]
    · have := congrArg Complex.re h''
      simp only [Complex.add_re, Complex.zero_re] at this
      norm_num at this
      linarith [hw_strip.1]
  refine ⟨H₀, hH₀, hH₀c, hH₀v, by rw [hfilt]; norm_num, by rw [hfilt]; norm_num, ?_⟩
  rw [hfilt, hK']
  exact mul_ne_zero hw₀ (Complex.ofReal_ne_zero.mpr β.integral_pos.ne')

open Classical in
private theorem endpoint_exteriorZeros_coeff_eq_zero_of_cesaro (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (α : ℝ) (χ₀ : PontryaginDual C𝔽)
    (hχ₀ : ∀ t, χ₀ (τ t) = 1) (H₀ : ℝ → ℂ)
    (hH₀ : ContDiff ℝ (∞) H₀) (hH₀c : HasCompactSupport H₀)
    (hpol₁ : ∫ x : ℝ, H₀ x * Complex.exp ((1 / 2 : ℂ) * x) = 0)
    (hpol₂ : ∫ x : ℝ, H₀ x * Complex.exp ((-1 / 2 : ℂ) * x) = 0) (D : ℝ → ℝ)
    (hDloc : ∀ Y > 0, IntegrableOn (fun y ↦ D y * Real.exp (-α * y)) (Ioc (0 : ℝ) Y))
    (hces : Tendsto (fun Y : ℝ ↦ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, D y * Real.exp (-α * y))
      atTop (𝓝 0))
    (hT : ∀ y : ℝ, 0 ≤ y → ∀ φ : BruhatCompactSupport C𝔽,
      (∀ x, φ.val x = ((χ₀⁻¹ : PontryaginDual C𝔽) x : ℂ) *
        H₀ (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
      M(φ, twist(1, 1 / 2)) = 0 → M(φ, twist(1, -1 / 2)) = 0 →
      ∃ S : ℂ, HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) S ∧ ‖S‖ ≤ D y)
    (z₀ : exteriorZeros(τ, α)) (hz₀ : z₀.val.1.val = χ₀) (hre₀ : α ≤ z₀.val.2.re - 1 / 2) :
    ∫ x : ℝ, H₀ x * Complex.exp ((z₀.val.2 - 1 / 2) * x) = 0 := by
  have hg (y : ℝ) : ContDiff ℝ (∞) (fun x ↦ H₀ (x - y)) := hH₀.comp (contDiff_id.sub contDiff_const)
  have hgc (y : ℝ) : HasCompactSupport (fun x ↦ H₀ (x - y)) :=
    hH₀c.comp_homeomorph (Homeomorph.subRight y)
  choose φ hφ using fun y : ℝ ↦ exists_characterNormTest (F := F) χ₀⁻¹ _ (hg y) (hgc y)
  let K : ℂ → ℂ := fun w ↦ ∫ x : ℝ, H₀ x * Complex.exp (w * x)
  have hzt (y : ℝ) (z : exteriorZeros(τ, α)) : zeroTerm(φ y, z) =
      if z.val.1.val = χ₀ then ((ord(z.val.1.val, z.val.2) : ℤ) : ℂ) *
        (classVolume * K (z.val.2 - 1 / 2)) * Complex.exp ((z.val.2 - 1 / 2) * y) else 0 := by
    rw [endpoint_characterNormTest_mellin _ (hg y) (hgc y) χ₀⁻¹ (φ y) (hφ y)]
    by_cases hχ : z.val.1.val = χ₀
    · have hone : z.val.1.val * χ₀⁻¹ = 1 := by rw [hχ, mul_inv_cancel]
      rw [ite_eq_left hχ, ite_eq_left (fun u ↦ by rw [hone]; rfl)]
      rw [grh_shift_integral H₀ hH₀.continuous _ (fun t ↦ by rw [hone]; rfl) y]
      ring
    · rw [ite_eq_right hχ, ite_eq_right (fun h1 ↦ hχ (endpoint_character_eq τ hτ z.val.1.property
        hχ₀ h1)), zero_mul, mul_zero]
  have hinv (t) : χ₀⁻¹ (τ t) = 1 := by change (χ₀ (τ t))⁻¹ = 1; rw [hχ₀, inv_one]
  have hpolar (y : ℝ) (s : ℂ) (hs : ∫ x : ℝ, H₀ x * Complex.exp (s * x) = 0) :
      M(φ y, twist(1, s)) = 0 :=
    endpoint_polar_mellin_eq_zero τ hτ χ₀⁻¹ hinv H₀ hH₀ hH₀c y (φ y) (hφ y) s hs
  let ι := {z : exteriorZeros(τ, α) // z.val.1.val = χ₀}
  let w : ι → ℂ := fun i ↦ i.val.val.2 - 1 / 2
  let b : ι → ℂ := fun i ↦
    ((ord(i.val.val.1.val, i.val.val.2) : ℤ) : ℂ) * (classVolume * K (w i))
  have hsum (u : ℝ) (hu : 0 ≤ u) : ∃ S : ℂ,
      HasSum (fun i : ι ↦ b i * Complex.exp (w i * u)) S ∧ ‖S‖ ≤ D u := by
    obtain ⟨S, hS, hSb⟩ := hT u hu (φ u) (hφ u) (hpolar u _ hpol₁) (hpolar u _ hpol₂)
    refine ⟨S, ?_, hSb⟩
    have hsupp : Function.support (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ u, z)) ⊆
        {z | z.val.1.val = χ₀} := by
      intro z hz
      by_contra hχ
      exact hz ((hzt u z).trans (ite_eq_right hχ))
    have h' := (hasSum_subtype_iff_of_support_subset hsupp).mpr hS
    have hf : (fun i : ι ↦ b i * Complex.exp (w i * u)) =
        (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ u, z)) ∘ (Subtype.val : ι → _) := by
      funext i
      rw [Function.comp_apply, hzt u i.val, ite_eq_left i.property]
    rw [hf]
    exact h'
  have hw : Function.Injective w := fun i j hij ↦ by
    have hs : i.val.val.2 = j.val.val.2 := sub_left_inj.mp hij
    exact Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext (i.property.trans j.property.symm)) hs))
  have hdisc : ∀ z : ℂ, ∀ᶠ u in 𝓝[≠] z, u ∉ Set.range w := fun z ↦ by
    filter_upwards [endpoint_zeros_discrete χ₀ z] with u hu
    rintro ⟨i, rfl⟩
    apply hu
    have h := i.val.property.1
    rw [i.property] at h
    rwa [sub_add_cancel]
  have hre : ∀ i, (w i).re ≤ 1 / 2 := fun i ↦ by
    have h := endpoint_zero_re_le_one _ i.val.property.1
    change (i.val.val.2 - 1 / 2).re ≤ 1 / 2
    rw [Complex.sub_re]
    norm_num
    linarith
  have hb : Summable b := by
    obtain ⟨S, hS, -⟩ := hsum 0 le_rfl
    simpa using hS.summable
  have h0 := eq_zero_of_hasSum_exp_of_cesaro_majorant w b hw hdisc hre hb
    (fun u ↦ ∑' i, b i * Complex.exp (w i * u))
    (fun u hu ↦ by obtain ⟨S, hS, -⟩ := hsum u hu; exact hS.summable.hasSum) D
    (fun u hu ↦ by obtain ⟨S, hS, hSb⟩ := hsum u hu; rw [hS.tsum_eq]; exact hSb) hDloc hces
    ⟨z₀, hz₀⟩ (by
      change α ≤ (z₀.val.2 - 1 / 2).re
      rw [Complex.sub_re]
      norm_num
      linarith)
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h (Int.cast_ne_zero.mpr z₀.property.1.ne')
  · exact (mul_eq_zero.mp h).resolve_left endpoint_classVolume_ne_zero

/-- **Zero-saving Cesàro criterion for `exteriorZeros`.**
Paper: Theorem 12.5.1.1, pp. 519–520, and §1.4, p. 30. Fix a norm section `τ` and a half-width `α`.
Suppose that for every unitary character `ψ` and every smooth compactly supported profile `H`
vanishing on `(-∞, 0]` there is a majorant `D` whose `exp(-α y)`-weighted Cesàro mean on `(0, ∞)`
tends to zero (requiring **no** exponent saving `c < α` below the strip edge), bounding the exterior
zero sum of `ψ · H(log|·| - y)` whenever `y ≥ 0` and its two polar Mellin terms vanish. Then no
completed Hecke L-function of a character trivial on `τ` has a zero with `|Re s - 1/2| ≥ α`. -/
theorem isEmpty_exteriorZeros_of_cesaro (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (α : ℝ)
    (hT : ∀ (ψ : PontryaginDual C𝔽) (H : ℝ → ℂ), ContDiff ℝ (∞) H → HasCompactSupport H →
      (∀ x ≤ 0, H x = 0) →
      ∃ D : ℝ → ℝ,
        (∀ Y > 0, IntegrableOn (fun y ↦ D y * Real.exp (-α * y)) (Ioc (0 : ℝ) Y)) ∧
        Tendsto (fun Y : ℝ ↦ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, D y * Real.exp (-α * y)) atTop (𝓝 0) ∧
        ∀ y : ℝ, 0 ≤ y → ∀ φ : BruhatCompactSupport C𝔽,
          (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
          M(φ, twist(1, 1 / 2)) = 0 → M(φ, twist(1, -1 / 2)) = 0 →
          ∃ S : ℂ, HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) S ∧ ‖S‖ ≤ D y) :
    IsEmpty exteriorZeros(τ, α) := by
  by_contra hne
  obtain ⟨z⟩ := not_isEmpty_iff.mp hne
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : exteriorZeros(τ, α), 1 / 2 ≤ z₀.val.2.re := by
    rcases le_or_gt (1 / 2) z.val.2.re with h | h
    · exact ⟨z, h⟩
    · have habs : |(1 - z.val.2).re - 1 / 2| = |z.val.2.re - 1 / 2| := by
        rw [Complex.sub_re, Complex.one_re,
          show 1 - z.val.2.re - 1 / 2 = -(z.val.2.re - 1 / 2) by ring, abs_neg]
      refine ⟨⟨(⟨z.val.1.val⁻¹, fun t ↦ ?_⟩, 1 - z.val.2),
        (endpoint_ord_reflection z.val.1.val z.val.2).symm ▸ z.property.1,
        habs.symm ▸ z.property.2⟩, ?_⟩
      · change (z.val.1.val (τ t))⁻¹ = 1
        rw [z.val.1.property t, inv_one]
      · change 1 / 2 ≤ (1 - z.val.2).re
        rw [Complex.sub_re, Complex.one_re]
        linarith
  have hstrip : |z₀.val.2.re - 1 / 2| < 1 / 2 := lt_of_not_ge fun h ↦
    (endpoint_isEmpty_half_le τ hτ (le_refl (1 / 2 : ℝ))).false ⟨z₀.val, z₀.property.1, h⟩
  have hw_strip : |(z₀.val.2 - 1 / 2).re| < 1 / 2 := by
    rw [Complex.sub_re]; norm_num; simpa using hstrip
  obtain ⟨H₀, hH₀, hH₀c, hH₀v, hpol₁, hpol₂, hKne⟩ := endpoint_exists_detecting_profile hw_strip
  obtain ⟨D, hDloc, hces, hC⟩ := hT (z₀.val.1.val)⁻¹ H₀ hH₀ hH₀c hH₀v
  have hre₀ : α ≤ z₀.val.2.re - 1 / 2 := by
    have h2 := z₀.property.2
    rwa [abs_of_nonneg (by linarith)] at h2
  exact hKne (endpoint_exteriorZeros_coeff_eq_zero_of_cesaro τ hτ α z₀.val.1.val
    z₀.val.1.property H₀ hH₀ hH₀c hpol₁ hpol₂ D hDloc hces hC z₀ rfl hre₀)

/-- **Endpoint `L¹` criterion for `exteriorZeros` (zero exponent saving).**
If `D(y) * exp(-α y)` is integrable on `(0, ∞)` at the single exponent `α` (covering subexponential
savings such as `exp(α y - c' √y)` or `exp(α y) / (1 + y)²`), then `IsEmpty exteriorZeros(τ, α)`. -/
theorem isEmpty_exteriorZeros_of_endpoint_integrable (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (α : ℝ)
    (hT : ∀ (ψ : PontryaginDual C𝔽) (H : ℝ → ℂ), ContDiff ℝ (∞) H → HasCompactSupport H →
      (∀ x ≤ 0, H x = 0) →
      ∃ D : ℝ → ℝ,
        IntegrableOn (fun y ↦ D y * Real.exp (-α * y)) (Ioi (0 : ℝ)) ∧
        ∀ y : ℝ, 0 ≤ y → ∀ φ : BruhatCompactSupport C𝔽,
          (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
          M(φ, twist(1, 1 / 2)) = 0 → M(φ, twist(1, -1 / 2)) = 0 →
          ∃ S : ℂ, HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) S ∧ ‖S‖ ≤ D y) :
    IsEmpty exteriorZeros(τ, α) := by
  refine isEmpty_exteriorZeros_of_cesaro τ hτ α fun ψ H hH hHc hHv ↦ ?_
  obtain ⟨D, hint, hC⟩ := hT ψ H hH hHc hHv
  refine ⟨fun y ↦ max (D y) 0, fun Y _ ↦ ?_, ?_, fun y hy φ hφ hp₁ hp₂ ↦ ?_⟩
  · have h1 : IntegrableOn (fun y ↦ max (D y * Real.exp (-α * y)) 0) (Ioc 0 Y) :=
      (hint.mono_set Ioc_subset_Ioi_self).pos_part
    refine h1.congr_fun (fun y _ ↦ ?_) measurableSet_Ioc
    rw [max_mul_of_nonneg _ _ (Real.exp_pos _).le, zero_mul]
  · have h1 : IntegrableOn (fun y ↦ max (D y * Real.exp (-α * y)) 0) (Ioi 0) := hint.pos_part
    have hint_pos : IntegrableOn (fun y ↦ max (D y) 0 * Real.exp (-α * y)) (Ioi 0) :=
      h1.congr_fun (fun y _ ↦ by rw [max_mul_of_nonneg _ _ (Real.exp_pos _).le, zero_mul])
        measurableSet_Ioi
    set I := ∫ y in Ioi (0 : ℝ), max (D y) 0 * Real.exp (-α * y)
    have hlim : Tendsto (fun Y : ℝ ↦ Y⁻¹ * I) atTop (𝓝 0) := by
      simpa using tendsto_inv_atTop_zero.mul_const I
    refine squeeze_zero' ?_ ?_ hlim
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
      exact mul_nonneg (inv_nonneg.mpr hY.le) (setIntegral_nonneg measurableSet_Ioc fun _ _ ↦
        mul_nonneg (le_max_right _ _) (Real.exp_pos _).le)
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hY.le)
      exact setIntegral_mono_set hint_pos
        (ae_of_all _ fun x : ℝ ↦ mul_nonneg (le_max_right (D x) 0) (Real.exp_pos (-α * x)).le)
        (Eventually.of_forall fun x (hx : x ∈ Ioc (0 : ℝ) Y) ↦ hx.1)
  · obtain ⟨S, hS, hSb⟩ := hC y hy φ hφ hp₁ hp₂
    exact ⟨S, hS, hSb.trans (le_max_left _ _)⟩

open Classical in
/-- **Majorant-free `o(exp(α y))` criterion for `exteriorZeros`.**
If for every unitary `ψ`, smooth compactly supported `H` vanishing on `(-∞, 0]`, and `ε > 0`,
all sufficiently large translations `y ≥ Y` with vanishing polar Mellin terms have exterior sum
at most `ε * exp(α y)`, then `IsEmpty exteriorZeros(τ, α)`. -/
theorem isEmpty_exteriorZeros_of_tendsto_zero (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (α : ℝ)
    (hT : ∀ (ψ : PontryaginDual C𝔽) (H : ℝ → ℂ), ContDiff ℝ (∞) H → HasCompactSupport H →
      (∀ x ≤ 0, H x = 0) →
      ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, max Y 0 ≤ y → ∀ φ : BruhatCompactSupport C𝔽,
        (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
        M(φ, twist(1, 1 / 2)) = 0 → M(φ, twist(1, -1 / 2)) = 0 →
        ∃ S : ℂ, HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) S ∧
          ‖S‖ ≤ ε * Real.exp (α * y)) :
    IsEmpty exteriorZeros(τ, α) := by
  by_contra hne
  obtain ⟨z⟩ := not_isEmpty_iff.mp hne
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : exteriorZeros(τ, α), 1 / 2 ≤ z₀.val.2.re := by
    rcases le_or_gt (1 / 2) z.val.2.re with h | h
    · exact ⟨z, h⟩
    · have habs : |(1 - z.val.2).re - 1 / 2| = |z.val.2.re - 1 / 2| := by
        rw [Complex.sub_re, Complex.one_re,
          show 1 - z.val.2.re - 1 / 2 = -(z.val.2.re - 1 / 2) by ring, abs_neg]
      refine ⟨⟨(⟨z.val.1.val⁻¹, fun t ↦ ?_⟩, 1 - z.val.2),
        (endpoint_ord_reflection z.val.1.val z.val.2).symm ▸ z.property.1,
        habs.symm ▸ z.property.2⟩, ?_⟩
      · change (z.val.1.val (τ t))⁻¹ = 1
        rw [z.val.1.property t, inv_one]
      · change 1 / 2 ≤ (1 - z.val.2).re
        rw [Complex.sub_re, Complex.one_re]
        linarith
  have hstrip : |z₀.val.2.re - 1 / 2| < 1 / 2 := lt_of_not_ge fun h ↦
    (endpoint_isEmpty_half_le τ hτ (le_refl (1 / 2 : ℝ))).false ⟨z₀.val, z₀.property.1, h⟩
  have hw_strip : |(z₀.val.2 - 1 / 2).re| < 1 / 2 := by
    rw [Complex.sub_re]; norm_num; simpa using hstrip
  obtain ⟨H₀, hH₀, hH₀c, hH₀v, hpol₁, hpol₂, hKne⟩ := endpoint_exists_detecting_profile hw_strip
  let χ₀ := z₀.val.1.val
  have hχ₀ := z₀.val.1.property
  have hinv (t) : χ₀⁻¹ (τ t) = 1 := by change (χ₀ (τ t))⁻¹ = 1; rw [hχ₀, inv_one]
  have hg (y : ℝ) : ContDiff ℝ (∞) (fun x ↦ H₀ (x - y)) := hH₀.comp (contDiff_id.sub contDiff_const)
  have hgc (y : ℝ) : HasCompactSupport (fun x ↦ H₀ (x - y)) :=
    hH₀c.comp_homeomorph (Homeomorph.subRight y)
  choose φ hφ using fun y : ℝ ↦ exists_characterNormTest (F := F) χ₀⁻¹ _ (hg y) (hgc y)
  let K : ℂ → ℂ := fun w ↦ ∫ x : ℝ, H₀ x * Complex.exp (w * x)
  have hzt (y : ℝ) (z' : exteriorZeros(τ, α)) : zeroTerm(φ y, z') =
      if z'.val.1.val = χ₀ then ((ord(z'.val.1.val, z'.val.2) : ℤ) : ℂ) *
        (classVolume * K (z'.val.2 - 1 / 2)) * Complex.exp ((z'.val.2 - 1 / 2) * y) else 0 := by
    rw [endpoint_characterNormTest_mellin _ (hg y) (hgc y) χ₀⁻¹ (φ y) (hφ y)]
    by_cases hχ : z'.val.1.val = χ₀
    · have hone : z'.val.1.val * χ₀⁻¹ = 1 := by rw [hχ, mul_inv_cancel]
      rw [ite_eq_left hχ, ite_eq_left (fun u ↦ by rw [hone]; rfl)]
      rw [grh_shift_integral H₀ hH₀.continuous _ (fun t ↦ by rw [hone]; rfl) y]
      ring
    · rw [ite_eq_right hχ, ite_eq_right (fun h1 ↦ hχ (endpoint_character_eq τ hτ z'.val.1.property
        hχ₀ h1)), zero_mul, mul_zero]
  have hpolar (y : ℝ) (s : ℂ) (hs : ∫ x : ℝ, H₀ x * Complex.exp (s * x) = 0) :
      M(φ y, twist(1, s)) = 0 :=
    endpoint_polar_mellin_eq_zero τ hτ χ₀⁻¹ hinv H₀ hH₀ hH₀c y (φ y) (hφ y) s hs
  let ι := {z' : exteriorZeros(τ, α) // z'.val.1.val = χ₀}
  let w : ι → ℂ := fun i ↦ i.val.val.2 - 1 / 2
  let b : ι → ℂ := fun i ↦
    ((ord(i.val.val.1.val, i.val.val.2) : ℤ) : ℂ) * (classVolume * K (w i))
  have hsub_sum (y : ℝ) {S : ℂ} (hS : HasSum (fun z' : exteriorZeros(τ, α) ↦ zeroTerm(φ y, z')) S) :
      HasSum (fun i : ι ↦ b i * Complex.exp (w i * y)) S := by
    have hsupp : Function.support (fun z' : exteriorZeros(τ, α) ↦ zeroTerm(φ y, z')) ⊆
        {z' | z'.val.1.val = χ₀} := by
      intro z' hz'
      by_contra hχ
      exact hz' ((hzt y z').trans (ite_eq_right hχ))
    have h' := (hasSum_subtype_iff_of_support_subset hsupp).mpr hS
    have hf : (fun i : ι ↦ b i * Complex.exp (w i * y)) =
        (fun z' : exteriorZeros(τ, α) ↦ zeroTerm(φ y, z')) ∘ (Subtype.val : ι → _) := by
      funext i
      rw [Function.comp_apply, hzt y i.val, ite_eq_left i.property]
    rwa [hf]
  have hb : Summable b := by
    obtain ⟨Y₁, hY₁⟩ := hT χ₀⁻¹ H₀ hH₀ hH₀c hH₀v 1 zero_lt_one
    set y₁ := max Y₁ 0
    have hy₁0 : 0 ≤ y₁ := le_max_right _ _
    obtain ⟨S₁, hS₁, -⟩ := hY₁ y₁ le_rfl (φ y₁) (hφ y₁) (hpolar y₁ _ hpol₁) (hpolar y₁ _ hpol₂)
    have h1 := (hsub_sum y₁ hS₁).summable.norm
    refine Summable.of_norm (h1.mul_right (Real.exp (y₁ / 2)) |>.of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) fun i ↦ ?_)
    have hre_lb : -1 / 2 ≤ (w i).re := by
      have hrefl : 0 < ord(χ₀⁻¹, 1 - i.val.val.2) := by
        have hi := i.val.property.1
        rw [i.property, ← endpoint_ord_reflection χ₀ i.val.val.2] at hi
        exact hi
      have hle1 := endpoint_zero_re_le_one χ₀⁻¹ hrefl
      change -1 / 2 ≤ (i.val.val.2 - 1 / 2).re
      rw [Complex.sub_re] at hle1 ⊢
      simp only [Complex.one_re] at hle1
      norm_num
      linarith
    rw [norm_mul (b i) (Complex.exp (w i * y₁)), Complex.norm_exp]
    have hwy : (w i * (y₁ : ℂ)).re = (w i).re * y₁ := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hwy, mul_assoc, ← Real.exp_add]
    calc ‖b i‖ = ‖b i‖ * 1 := (mul_one _).symm
      _ ≤ ‖b i‖ * Real.exp ((w i).re * y₁ + y₁ / 2) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          rw [Real.one_le_exp_iff]
          have hmul := mul_le_mul_of_nonneg_right hre_lb hy₁0
          linarith
  have hre : ∀ i, (w i).re ≤ 1 / 2 := fun i ↦ by
    have h := endpoint_zero_re_le_one _ i.val.property.1
    change (i.val.val.2 - 1 / 2).re ≤ 1 / 2
    rw [Complex.sub_re]; norm_num; linarith
  have hw : Function.Injective w := fun i j hij ↦ by
    have hs : i.val.val.2 = j.val.val.2 := sub_left_inj.mp hij
    exact Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext (i.property.trans j.property.symm)) hs))
  have hdisc : ∀ z' : ℂ, ∀ᶠ u in 𝓝[≠] z', u ∉ Set.range w := fun z' ↦ by
    filter_upwards [endpoint_zeros_discrete χ₀ z'] with u hu
    rintro ⟨i, rfl⟩
    apply hu
    have h := i.val.property.1
    rw [i.property] at h
    rwa [sub_add_cancel]
  let Sfun : ℝ → ℂ := fun y ↦ ∑' i, b i * Complex.exp (w i * y)
  have hS_hasSum : ∀ y : ℝ, 0 ≤ y → HasSum (fun i ↦ b i * Complex.exp (w i * y)) (Sfun y) := by
    intro y hy
    refine (Summable.of_norm_bounded (g := fun i ↦ ‖b i‖ * Real.exp (y / 2))
      (hb.norm.mul_right _) fun i ↦ ?_).hasSum
    rw [norm_mul (b i), Complex.norm_exp]
    gcongr
    have hwy : (w i * (y : ℂ)).re = (w i).re * y := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [hwy]
    nlinarith [hre i]
  have ho : Tendsto (fun y : ℝ ↦ ‖Sfun y‖ * Real.exp (-α * y)) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨Y, hY⟩ := hT χ₀⁻¹ H₀ hH₀ hH₀c hH₀v (ε / 2) (half_pos hε)
    filter_upwards [eventually_ge_atTop (max Y 0)] with y hy
    have hy0 : 0 ≤ y := (le_max_right Y 0).trans hy
    obtain ⟨S, hS, hSb⟩ := hY y hy (φ y) (hφ y) (hpolar y _ hpol₁) (hpolar y _ hpol₂)
    have hSeq : Sfun y = S := (hS_hasSum y hy0).unique (hsub_sum y hS)
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le), hSeq]
    calc ‖S‖ * Real.exp (-α * y)
        ≤ (ε / 2 * Real.exp (α * y)) * Real.exp (-α * y) :=
          mul_le_mul_of_nonneg_right hSb (Real.exp_pos _).le
      _ = ε / 2 := by
          rw [mul_assoc, ← Real.exp_add, show α * y + -α * y = 0 by ring, Real.exp_zero, mul_one]
      _ < ε := half_lt_self hε
  have hre₀ : α ≤ (w ⟨z₀, rfl⟩).re := by
    have h2 := z₀.property.2
    rw [abs_of_nonneg (by linarith)] at h2
    change α ≤ (z₀.val.2 - 1 / 2).re
    rw [Complex.sub_re]; norm_num; linarith
  have h0 := eq_zero_of_hasSum_exp_of_tendsto_zero w b hw hdisc hre hb Sfun hS_hasSum ho
    ⟨z₀, rfl⟩ hre₀
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h (Int.cast_ne_zero.mpr z₀.property.1.ne')
  · exact hKne ((mul_eq_zero.mp h).resolve_left endpoint_classVolume_ne_zero)

/-! ### Zero-saving strip-trace defect criteria -/

private theorem endpoint_basepoint (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ χ : PontryaginDual C₁ → PontryaginDual C𝔽, IsSpectralBasepointChoice χ ∧
      (∀ η t, χ η (τ t) = 1) ∧
      ∀ ψ : PontryaginDual C𝔽, (∀ t, ψ (τ t) = 1) → χ (ψ.comp restriction) = ψ := by
  let n : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let P : C𝔽 →ₜ* C𝔽 := ContinuousMonoidHom.id C𝔽 / τ.comp n
  have hP (x : C𝔽) : P x ∈ (ideleClassNorm F).ker := by
    change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
    rw [map_div, hτ, div_self']
  let r : C𝔽 →ₜ* C₁ := ⟨P.toMonoidHom.codRestrict _ hP, P.continuous.subtype_mk _⟩
  have hr (x : C𝔽) : (r x : C𝔽) = x / τ (ideleClassNorm F x) := rfl
  refine ⟨fun η ↦ η.comp r, fun η ↦ ?_, fun η t ↦ ?_, fun ψ hψ ↦ ?_⟩
  · ext x : 1
    change η (r (x : C𝔽)) = η x
    apply congrArg η
    apply Subtype.ext
    rw [hr, show ideleClassNorm F (x : C𝔽) = 1 from x.property, map_one, div_one]
  · change η (r (τ t)) = 1
    have : r (τ t) = 1 := Subtype.ext (by rw [hr, hτ, div_self']; rfl)
    rw [this, map_one]
  · ext x : 1
    change ψ (r x : C𝔽) = ψ x
    rw [hr, map_div, hψ, div_one]

private theorem endpoint_order_ne_top (χ : PontryaginDual C𝔽) (z : ℂ) : order(χ, z) ≠ ⊤ := by
  obtain ⟨hL, heq⟩ := continuedCompletedHeckeL_spec χ
  have hfinite : order(χ, (2 : ℂ)) ≠ ⊤ := by
    intro h
    have hp : 0 < order(χ, (2 : ℂ)) := by rw [h]; exact WithTop.coe_lt_top (0 : ℤ)
    have := completedHeckeL_continuation_zeros χ _ hL heq (by norm_num : 0 < (2 : ℂ).re) hp
    norm_num at this
  exact hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ z) hfinite

private theorem endpoint_ord_eq (χ : PontryaginDual C𝔽) (z : ℂ) :
    ord(χ, z) = (order(χ, z)).untop₀ :=
  MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ z)

private theorem endpoint_ord_pos_iff (χ : PontryaginDual C𝔽) (z : ℂ) :
    0 < ord(χ, z) ↔ 0 < order(χ, z) := by
  rw [endpoint_ord_eq]
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (endpoint_order_ne_top χ z)
  rw [← hk, WithTop.untop₀_coe]
  exact_mod_cast Iff.rfl

private theorem endpoint_exists_width (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {α : ℝ}
    (hα : 0 < α) :
    ∃ β, 0 < β ∧ β ≤ α ∧ ∀ η (z : ℂ), 0 < order(χ η, z) → |z.re - 1 / 2| ≠ β := by
  have hK := IsModulation.isCompact_ker (m := m𝔽) hm𝔽
  let : CompactSpace C₁ := isCompact_iff_compactSpace.mp hK
  let : LocallyCompactSpace C₁ := hK.isClosed.locallyCompactSpace
  let : SecondCountableTopology C₁ := Topology.IsInducing.subtypeVal.secondCountableTopology
  let : SecondCountableTopology Circle :=
    inferInstanceAs (SecondCountableTopology (Metric.sphere (0 : ℂ) 1))
  let : SecondCountableTopology (PontryaginDual C₁) :=
    (ContinuousMonoidHom.isEmbedding_toContinuousMap C₁ Circle).secondCountableTopology
  let : Countable (PontryaginDual C₁) := countable_of_Lindelof_of_discrete
  let zeros (η : PontryaginDual C₁) := {z : ℂ | 0 < order(χ η, z)}
  have hc (η) : (zeros η).Countable := by
    obtain ⟨hL, _⟩ := continuedCompletedHeckeL_spec (χ η)
    have hd : (zeros η)ᶜ ∈ codiscrete ℂ := by
      filter_upwards
        [hL.meromorphicOn.codiscreteWithin_setOfPred_meromorphicOrderAt_eq_zero_or_top] with z hz'
      rcases hz'.2 with h | h
      · simp [zeros, h]
      · exact (endpoint_order_ne_top (χ η) z h).elim
    let : DiscreteTopology (zeros η) := isDiscrete_iff_discreteTopology.mp
      (compl_mem_codiscrete_iff.mp hd).2
    exact Set.countable_coe_iff.mp countable_of_Lindelof_of_discrete
  let S := ⋃ η, (fun z : ℂ ↦ |z.re - 1 / 2|) '' zeros η
  have hS : S.Countable := countable_iUnion fun η ↦ (hc η).image _
  obtain ⟨β, hβI, hβS⟩ : (Ioo 0 α \ S).Nonempty := by
    apply MeasureTheory.nonempty_of_measure_ne_zero (μ := MeasureTheory.volume)
    rw [MeasureTheory.measure_sdiff_null (hS.measure_zero _)]
    simp [Real.volume_Ioo, hα]
  exact ⟨β, hβI.1, hβI.2.le, fun η z hz h ↦ hβS (mem_iUnion.mpr ⟨η, z, hz, h⟩)⟩

private theorem endpoint_hasSum_interior (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (hχτ : ∀ η t, χ η (τ t) = 1)
    (hlift : ∀ ψ : PontryaginDual C𝔽, (∀ t, ψ (τ t) = 1) → χ (ψ.comp restriction) = ψ)
    {β : ℝ} (s : ℝ) (hedge : ∀ η (z : ℂ), 0 < order(χ η, z) → |z.re - 1 / 2| ≠ β)
    (φ : BruhatCompactSupport C𝔽) {T : ℂ}
    (h : HasSum (fun z : {z : PontryaginDual C₁ × ℝ × ℝ // z.2.1 ∈ Icc (-β) β ∧
        0 < order(χ z.1, ((1 / 2 + z.2.1 : ℝ) : ℂ) + (z.2.2 : ℂ) * Complex.I)} ↦
      ((spectralStripMultiplicity β s z.val.2.1
        (order(χ z.val.1, ((1 / 2 + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I)).untop₀.toNat
          : ℕ) : ℂ) *
        M(φ, twist(χ z.val.1, (z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I))) T) :
    HasSum (fun z : interiorZeros(τ, β) ↦ zeroTerm(φ, z)) T := by
  let Z := {z : PontryaginDual C₁ × ℝ × ℝ // z.2.1 ∈ Icc (-β) β ∧
    0 < order(χ z.1, ((1 / 2 + z.2.1 : ℝ) : ℂ) + (z.2.2 : ℂ) * Complex.I)}
  have hre (σ t : ℝ) : ((((1 / 2 + σ : ℝ) : ℂ) + (t : ℂ) * Complex.I).re - 1 / 2) = σ := by simp
  have hin (z : Z) : |z.val.2.1| < β := by
    have h1 := hedge _ _ z.property.2
    rw [hre] at h1
    exact lt_of_le_of_ne (abs_le.mpr z.property.1) h1
  let e : Z → interiorZeros(τ, β) := fun z ↦
    ⟨(⟨χ z.val.1, hχτ z.val.1⟩, ((1 / 2 + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I),
      (endpoint_ord_pos_iff _ _).mpr z.property.2, by rw [hre]; exact hin z⟩
  have he : Bijective e := by
    constructor
    · intro z z' hzz
      have h1 := congrArg (fun y : interiorZeros(τ, β) ↦ y.val.1.val) hzz
      have h2 : ((1 / 2 + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I =
          ((1 / 2 + z'.val.2.1 : ℝ) : ℂ) + (z'.val.2.2 : ℂ) * Complex.I :=
        congrArg (fun y : interiorZeros(τ, β) ↦ y.val.2) hzz
      have hω : z.val.1 = z'.val.1 := by
        rw [← hχ z.val.1, ← hχ z'.val.1]
        exact congrArg (fun ψ : PontryaginDual C𝔽 ↦ ψ.comp restriction) h1
      have hr : z.val.2.1 = z'.val.2.1 := by simpa using congrArg Complex.re h2
      have hi : z.val.2.2 = z'.val.2.2 := by simpa using congrArg Complex.im h2
      exact Subtype.ext (Prod.ext hω (Prod.ext hr hi))
    · rintro ⟨⟨ψ, ρ⟩, hpos, hlt⟩
      have hψ := hlift ψ.val ψ.property
      have hρ : (((1 / 2 + (ρ.re - 1 / 2) : ℝ) : ℂ) + (ρ.im : ℂ) * Complex.I) = ρ := by
        apply Complex.ext <;> simp
      refine ⟨⟨(ψ.val.comp restriction, ρ.re - 1 / 2, ρ.im),
        ⟨⟨by linarith [(abs_lt.mp hlt).1], by linarith [(abs_lt.mp hlt).2]⟩, ?_⟩⟩, ?_⟩
      · change 0 < order(χ (ψ.val.comp restriction), _)
        rw [hψ, hρ]
        exact (endpoint_ord_pos_iff _ _).mp hpos
      · apply Subtype.ext
        change ((⟨χ (ψ.val.comp restriction), _⟩ :
          {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}), _) = (ψ, ρ)
        exact Prod.ext (Subtype.ext hψ) hρ
  have hterm (z : Z) : zeroTerm(φ, e z) =
      ((spectralStripMultiplicity β s z.val.2.1
        (order(χ z.val.1, ((1 / 2 + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I)).untop₀.toNat
          : ℕ) : ℂ) *
        M(φ, twist(χ z.val.1, (z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I)) := by
    have hpt : ((1 / 2 + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I - 1 / 2 =
        (z.val.2.1 : ℂ) + (z.val.2.2 : ℂ) * Complex.I := by push_cast; ring
    have hord : ((ord(χ z.val.1, ((1 / 2 + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I)
        : ℤ) : ℂ) = ((spectralStripMultiplicity β s z.val.2.1
          (order(χ z.val.1,
            ((1 / 2 + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I)).untop₀.toNat
            : ℕ) : ℂ) := by
      rw [spectralStripMultiplicity_interior (abs_lt.mp (hin z)) s, endpoint_ord_eq]
      have hpos := z.property.2
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp (endpoint_order_ne_top (χ z.val.1)
        (((1 / 2 + z.val.2.1 : ℝ) : ℂ) + (z.val.2.2 : ℂ) * Complex.I))
      rw [← hk] at hpos ⊢
      rw [WithTop.untop₀_coe]
      have hk0 : 0 ≤ k := WithTop.coe_le_coe.mp hpos.le
      rw [show ((k.toNat : ℕ) : ℂ) = ((k.toNat : ℤ) : ℂ) from rfl, Int.toNat_of_nonneg hk0]
    exact congrArg₂ (· * ·) hord (congrArg (fun c ↦ M(φ, twist(χ z.val.1, c))) hpt)
  have h' : HasSum (fun z : Z ↦ zeroTerm(φ, e z)) T := by
    rw [funext hterm]
    exact h
  exact ((Equiv.ofBijective e he).hasSum_iff).mp h'

private theorem endpoint_hasSum_sub {X : Type*} (G : X → ℂ) (A I E : Set X)
    (hE : ∀ p, p ∈ E ↔ p ∈ A ∧ p ∉ I) (hIA : I ⊆ A) {TA TI : ℂ}
    (hA : HasSum (fun z : A ↦ G z) TA) (hI : HasSum (fun z : I ↦ G z) TI) :
    HasSum (fun z : E ↦ G z) (TA - TI) := by
  classical
  replace hA := (hasSum_subtype_iff_indicator (f := G) (s := A)).mp hA
  replace hI := (hasSum_subtype_iff_indicator (f := G) (s := I)).mp hI
  refine (hasSum_subtype_iff_indicator (f := G) (s := E)).mpr ?_
  have h : E.indicator G = A.indicator G - I.indicator G := by
    funext p
    by_cases hp : p ∈ I
    · simp [Set.indicator_of_mem hp, Set.indicator_of_mem (hIA hp),
        Set.indicator_of_notMem (fun h ↦ ((hE p).mp h).2 hp)]
    · by_cases ha : p ∈ A
      · simp [Set.indicator_of_mem ((hE p).mpr ⟨ha, hp⟩), Set.indicator_of_mem ha,
          Set.indicator_of_notMem hp]
      · simp [Set.indicator_of_notMem ha, Set.indicator_of_notMem hp,
          Set.indicator_of_notMem (fun h ↦ ha ((hE p).mp h).1)]
  rw [h]
  exact hA.sub hI

private theorem endpoint_hasSum_sub_of_width (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) {β s : ℝ} (hβ : 0 < β) (hs : 1 < s)
    (hedge : ∀ χ : PontryaginDual C𝔽, (∀ t, χ (τ t) = 1) →
      ∀ z : ℂ, 0 < ord(χ, z) → |z.re - 1 / 2| ≠ β)
    (φ : BruhatCompactSupport C𝔽)
    (T : nuclearEndomorphisms stripQuot(hβ.le, hs)) (hT : T.val = stripConv(hβ.le, hs, φ)) :
    ∃ (a : archTest) (b : finiteTest), archRestricts(φ, a) ∧ finiteRestricts(φ, b) ∧
      HasSum (fun z : exteriorZeros(τ, β) ↦ zeroTerm(φ, z))
        (localTerms(φ, a, b) - hilbertTrace T) := by
  obtain ⟨a, b, ha, hb, -, hall⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1 / 2 : ℝ))
  obtain ⟨χ, hχ, hχτ, hlift⟩ := endpoint_basepoint τ hτ
  have ht := (spectralStripConvolution_trace (F := F) (1 / 2) χ hχ hβ.le hs φ T hT).2
  have hint := endpoint_hasSum_interior τ χ hχ hχτ hlift s
    (fun η z hz ↦ hedge (χ η) (hχτ η) z ((endpoint_ord_pos_iff _ _).mpr hz)) φ ht
  have hempty : IsEmpty exteriorZeros(τ, 1 / 2) := endpoint_isEmpty_half_le τ hτ (le_refl _)
  have hhalf (p : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ)
      (hp : 0 < ord(p.1.val, p.2)) : |p.2.re - 1 / 2| < 1 / 2 :=
    lt_of_not_ge fun h ↦ hempty.false ⟨p, hp, h⟩
  exact ⟨a, b, ha, hb, endpoint_hasSum_sub
    (fun p : {χ : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ ↦
      ((ord(p.1.val, p.2) : ℤ) : ℂ) * M(φ, twist(p.1.val, p.2 - 1 / 2)))
    {p | 0 < ord(p.1.val, p.2) ∧ |p.2.re - 1 / 2| < 1 / 2}
    {p | 0 < ord(p.1.val, p.2) ∧ |p.2.re - 1 / 2| < β}
    {p | 0 < ord(p.1.val, p.2) ∧ β ≤ |p.2.re - 1 / 2|}
    (fun p ↦ ⟨fun h ↦ ⟨⟨h.1, hhalf p h.1⟩, fun h' ↦ (not_lt.mpr h.2) h'.2⟩,
      fun h ↦ ⟨h.1.1, not_lt.mp fun h' ↦ h.2 ⟨h.1.1, h'⟩⟩⟩)
    (fun p hp ↦ ⟨hp.1, hhalf p hp.1⟩) hall hint⟩

/-- **Zero-saving Cesàro strip-trace comparison for Theorem 12.5.1.1.**
Suppose that for every positive half-width `β`, unitary character `ψ`, and smooth compactly
supported profile `H` vanishing on `(-∞, 0]`, there is a majorant `D` whose `exp(-β y)`-weighted
Cesàro mean on `(0, ∞)` vanishes (requiring **no** exponent saving `c < β` and no global kernel
`hK`), bounding `‖hilbertTrace T - localTerms(φ_y)‖` on polar-free translated tests. Then the
conclusion of `traceFormula_exteriorZeros` holds at every positive width. -/
theorem traceFormula_exteriorZeros_of_stripTrace_cesaro (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F))
    (hdefect : ∀ {β : ℝ} (hβ : 0 < β) (ψ : PontryaginDual C𝔽) (H : ℝ → ℂ),
      ContDiff ℝ (∞) H → HasCompactSupport H → (∀ x ≤ 0, H x = 0) →
      ∃ D : ℝ → ℝ,
        (∀ Y > 0, IntegrableOn (fun y ↦ D y * Real.exp (-β * y)) (Ioc (0 : ℝ) Y)) ∧
        Tendsto (fun Y : ℝ ↦ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, D y * Real.exp (-β * y)) atTop (𝓝 0) ∧
        ∀ y : ℝ, 0 ≤ y → ∀ φ : BruhatCompactSupport C𝔽,
          (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
          M(φ, twist(1, 1 / 2)) = 0 → M(φ, twist(1, -1 / 2)) = 0 →
          ∃ T : nuclearEndomorphisms stripQuot(hβ.le, three),
            T.val = stripConv(hβ.le, three, φ) ∧
            ∀ (a : archTest) (b : finiteTest), archRestricts(φ, a) → finiteRestricts(φ, b) →
              ‖hilbertTrace T - localTerms(φ, a, b)‖ ≤ D y)
    (φ : BruhatCompactSupport C𝔽) {α : ℝ} (hα : 0 < α) :
    HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0 := by
  obtain ⟨χ, -, -, hlift⟩ := endpoint_basepoint τ hτ
  obtain ⟨β, hβ, hβα, hedge⟩ := endpoint_exists_width χ hα
  have hedge' : ∀ ψ : PontryaginDual C𝔽, (∀ t, ψ (τ t) = 1) →
      ∀ z : ℂ, 0 < ord(ψ, z) → |z.re - 1 / 2| ≠ β := fun ψ hψ z hz ↦
    hedge (ψ.comp restriction) z (by rw [hlift ψ hψ]; exact (endpoint_ord_pos_iff _ _).mp hz)
  have hE := isEmpty_exteriorZeros_of_cesaro τ hτ β fun ψ H hH hHc hHv ↦ by
    obtain ⟨D, hDloc, hces, hC⟩ := hdefect hβ ψ H hH hHc hHv
    refine ⟨D, hDloc, hces, fun y hy φ' hφ' hp₁ hp₂ ↦ ?_⟩
    obtain ⟨T, hT, hTb⟩ := hC y hy φ' hφ' hp₁ hp₂
    obtain ⟨a, b, ha, hb, hsum⟩ :=
      endpoint_hasSum_sub_of_width τ hτ hβ three hedge' φ' T hT
    exact ⟨_, hsum, by rw [norm_sub_rev]; exact hTb a b ha hb⟩
  have : IsEmpty exteriorZeros(τ, α) :=
    ⟨fun z ↦ hE.false ⟨z.val, z.property.1, hβα.trans z.property.2⟩⟩
  exact hasSum_empty

/-- **Endpoint `L¹` strip-trace comparison for Theorem 12.5.1.1 (zero exponent saving).**
If at each positive half-width `β` the trace defect on polar-free translated tests above norm one
is majorized by `D(y)` with `D(y) * exp(-β y)` integrable on `(0, ∞)`, then the conclusion of
`traceFormula_exteriorZeros` holds. -/
theorem traceFormula_exteriorZeros_of_stripTrace_endpoint_integrable (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F))
    (hdefect : ∀ {β : ℝ} (hβ : 0 < β) (ψ : PontryaginDual C𝔽) (H : ℝ → ℂ),
      ContDiff ℝ (∞) H → HasCompactSupport H → (∀ x ≤ 0, H x = 0) →
      ∃ D : ℝ → ℝ,
        IntegrableOn (fun y ↦ D y * Real.exp (-β * y)) (Ioi (0 : ℝ)) ∧
        ∀ y : ℝ, 0 ≤ y → ∀ φ : BruhatCompactSupport C𝔽,
          (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
          M(φ, twist(1, 1 / 2)) = 0 → M(φ, twist(1, -1 / 2)) = 0 →
          ∃ T : nuclearEndomorphisms stripQuot(hβ.le, three),
            T.val = stripConv(hβ.le, three, φ) ∧
            ∀ (a : archTest) (b : finiteTest), archRestricts(φ, a) → finiteRestricts(φ, b) →
              ‖hilbertTrace T - localTerms(φ, a, b)‖ ≤ D y)
    (φ : BruhatCompactSupport C𝔽) {α : ℝ} (hα : 0 < α) :
    HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0 := by
  obtain ⟨χ, -, -, hlift⟩ := endpoint_basepoint τ hτ
  obtain ⟨β, hβ, hβα, hedge⟩ := endpoint_exists_width χ hα
  have hedge' : ∀ ψ : PontryaginDual C𝔽, (∀ t, ψ (τ t) = 1) →
      ∀ z : ℂ, 0 < ord(ψ, z) → |z.re - 1 / 2| ≠ β := fun ψ hψ z hz ↦
    hedge (ψ.comp restriction) z (by rw [hlift ψ hψ]; exact (endpoint_ord_pos_iff _ _).mp hz)
  have hE := isEmpty_exteriorZeros_of_endpoint_integrable τ hτ β fun ψ H hH hHc hHv ↦ by
    obtain ⟨D, hint, hC⟩ := hdefect hβ ψ H hH hHc hHv
    refine ⟨D, hint, fun y hy φ' hφ' hp₁ hp₂ ↦ ?_⟩
    obtain ⟨T, hT, hTb⟩ := hC y hy φ' hφ' hp₁ hp₂
    obtain ⟨a, b, ha, hb, hsum⟩ :=
      endpoint_hasSum_sub_of_width τ hτ hβ three hedge' φ' T hT
    exact ⟨_, hsum, by rw [norm_sub_rev]; exact hTb a b ha hb⟩
  have : IsEmpty exteriorZeros(τ, α) :=
    ⟨fun z ↦ hE.false ⟨z.val, z.property.1, hβα.trans z.property.2⟩⟩
  exact hasSum_empty

/-! ### Exact single-width equivalences with the non-polar signed local terms -/

private theorem endpoint_translatedLocalTerms_hasSum (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1) (H : ℝ → ℂ)
    (hs : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (y : ℝ)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y))
    (a : archTest) (b : finiteTest) (ha : archRestricts(φ, a)) (hb : finiteRestricts(φ, b)) :
    HasSum (fun z : characterZeros(ψ⁻¹) ↦
      translatedCoeff(ψ⁻¹, H, z) * Complex.exp (((z : ℂ) - 1 / 2) * y)) (localTerms(φ, a, b)) := by
  classical
  obtain ⟨a', b', ha', hb', -, hall⟩ := traceFormula_of_half_le τ hτ φ (le_refl (1 / 2 : ℝ))
  rw [endpoint_localTerms_congr φ ha hb ha' hb']
  have hinv (t) : ψ⁻¹ (τ t) = 1 := by change (ψ (τ t))⁻¹ = 1; rw [hψ, inv_one]
  let e : characterZeros(ψ⁻¹) → interiorZeros(τ, 1 / 2) := fun z ↦
    ⟨(⟨ψ⁻¹, hinv⟩, z.val), z.property, lt_of_not_ge fun he ↦
      (endpoint_isEmpty_half_le τ hτ (le_refl (1 / 2 : ℝ))).false
        ⟨(⟨ψ⁻¹, hinv⟩, z.val), z.property, he⟩⟩
  have he : Injective e := fun i j hij ↦
    Subtype.ext (congrArg (fun z : interiorZeros(τ, 1 / 2) ↦ z.val.2) hij)
  have hsy : ContDiff ℝ (∞) (fun x ↦ H (x - y)) := hs.comp (contDiff_id.sub contDiff_const)
  have hcy : HasCompactSupport (fun x ↦ H (x - y)) := hc.comp_homeomorph (Homeomorph.subRight y)
  have hzero (z : interiorZeros(τ, 1 / 2)) (hz : z ∉ Set.range e) : zeroTerm(φ, z) = 0 := by
    rw [endpoint_characterNormTest_mellin _ hsy hcy ψ φ hφ]
    have hoff : ¬ ∀ u : C₁, (z.val.1.val * ψ) u.val = 1 := by
      intro hone
      have hχ : z.val.1.val = ψ⁻¹ :=
        endpoint_character_eq τ hτ z.val.1.property hinv (by simpa [inv_inv] using hone)
      have hm := z.property.1
      rw [hχ] at hm
      exact hz ⟨⟨z.val.2, hm⟩, Subtype.ext (Prod.ext (Subtype.ext hχ.symm) rfl)⟩
    rw [ite_eq_right hoff, zero_mul, mul_zero]
  have h := (he.hasSum_iff (f := fun z : interiorZeros(τ, 1 / 2) ↦ zeroTerm(φ, z)) hzero).mpr hall
  refine h.congr_fun fun z ↦ ?_
  change _ = ((ord(ψ⁻¹, z.val) : ℤ) : ℂ) * M(φ, twist(ψ⁻¹, z.val - 1 / 2))
  symm
  rw [endpoint_characterNormTest_mellin _ hsy hcy ψ φ hφ]
  have hone : (ψ⁻¹ : PontryaginDual C𝔽) * ψ = 1 := inv_mul_cancel _
  rw [ite_eq_left (fun u ↦ by rw [hone]; rfl)]
  rw [grh_shift_integral H hs.continuous _ (fun t ↦ by rw [hone]; rfl) y]
  ring

private theorem endpoint_translatedLocalTerms_tendsto_zero_of_isEmpty (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) {α : ℝ}
    (hE : IsEmpty exteriorZeros(τ, α))
    (ψ : PontryaginDual C𝔽) (hψ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hs : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    Tendsto (fun y : ℝ ↦ ∑' z : characterZeros(ψ⁻¹),
      translatedCoeff(ψ⁻¹, H, z) * Complex.exp (((z : ℂ) - 1 / 2 - α) * y)) atTop (𝓝 0) := by
  have hinv (t) : ψ⁻¹ (τ t) = 1 := by change (ψ (τ t))⁻¹ = 1; rw [hψ, inv_one]
  let c : characterZeros(ψ⁻¹) → ℂ := fun z ↦ translatedCoeff(ψ⁻¹, H, z)
  have hc_sum : Summable (fun z : characterZeros(ψ⁻¹) ↦ ‖c z‖) := by
    obtain ⟨f, hf⟩ := exists_characterNormTest (F := F) ψ H hs hc
    obtain ⟨a, b, ha, hb, -, -⟩ := traceFormula_of_half_le τ hτ f (le_refl (1 / 2 : ℝ))
    have h0 := endpoint_translatedLocalTerms_hasSum τ hτ ψ hψ H hs hc 0 f (by simpa using hf)
      a b ha hb
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
    exact h0.summable.norm
  have hlt (z : characterZeros(ψ⁻¹)) : z.val.re - 1 / 2 - α < 0 := by
    have hin : |z.val.re - 1 / 2| < α :=
      lt_of_not_ge fun hge ↦ hE.false ⟨(⟨ψ⁻¹, hinv⟩, z.val), z.property, hge⟩
    linarith [(abs_lt.mp hin).2]
  let Fterm : ℝ → characterZeros(ψ⁻¹) → ℂ := fun y z ↦
    c z * Complex.exp (((z : ℂ) - 1 / 2 - α) * y)
  have hlim_term (z : characterZeros(ψ⁻¹)) : Tendsto (fun y : ℝ ↦ Fterm y z) atTop (𝓝 0) := by
    have hexp : Tendsto (fun y : ℝ ↦ Real.exp ((z.val.re - 1 / 2 - α) * y)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp
        (Filter.Tendsto.const_mul_atTop_of_neg (hlt z) tendsto_id)
    have hnorm : Tendsto (fun y : ℝ ↦ ‖Fterm y z‖) atTop (𝓝 0) := by
      have h1 := hexp.const_mul ‖c z‖
      rw [mul_zero] at h1
      refine h1.congr fun y ↦ ?_
      symm
      dsimp [Fterm]
      rw [norm_mul (c z), Complex.norm_exp]
      congr 2
      simp [Complex.sub_re]
    exact tendsto_zero_iff_norm_tendsto_zero.mpr hnorm
  have hbound : ∀ᶠ y : ℝ in atTop, ∀ z : characterZeros(ψ⁻¹), ‖Fterm y z‖ ≤ ‖c z‖ := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy z
    dsimp [Fterm]
    rw [norm_mul (c z), Complex.norm_exp]
    have hre_y : (((z : ℂ) - 1 / 2 - α) * (y : ℂ)).re = (z.val.re - 1 / 2 - α) * y := by
      simp [Complex.sub_re]
    rw [hre_y]
    exact mul_le_of_le_one_right (norm_nonneg _)
      (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (hlt z).le hy))
  simpa only [tsum_zero] using tendsto_tsum_of_dominated_convergence hc_sum hlim_term hbound

/-- **Exact fixed-width `o(exp(α y))` local-terms characterization of `traceFormula_exteriorZeros`.**
Paper: Theorem 12.5.1.1, pp. 519–520, and Theorem B.4.4.7, p. 623.
Fix a norm section `τ` and **any single positive half-width `α > 0`**. The exterior-zero sum
vanishes at width `α` for every test vanishing on the norm-one classes **if and only if**, for every
normalized unitary character `ψ` (`∀ t, ψ (τ t) = 1`) and every smooth compactly supported radial
profile `H` supported on `(0, ∞)` with vanishing polar moments `∫ H(x) exp(±x/2) dx = 0`, the pure
non-polar signed local terms `-classVolume * (∑_w archPV + ∑'_v finiteTerm)` of `ψ · H(log|·| - y)`
are `o(exp(α y))` as `y → ∞`. Unlike `c < α` bounds, this equivalence holds width-by-width at each
individual `α > 0`. -/
theorem hasSum_exteriorZeros_iff_localTerms_tendsto_zero (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) {α : ℝ} (_hα : 0 < α) :
    (∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) →
      HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) ↔
      ∀ (ψ : PontryaginDual C𝔽), (∀ t, ψ (τ t) = 1) →
        ∀ (H : ℝ → ℂ), ContDiff ℝ (∞) H → HasCompactSupport H → (∀ x ≤ 0, H x = 0) →
          (∫ x : ℝ, H x * Complex.exp ((1 / 2 : ℂ) * x) = 0) →
          (∫ x : ℝ, H x * Complex.exp ((-1 / 2 : ℂ) * x) = 0) →
          ∀ ε : ℝ, 0 < ε → ∃ Y : ℝ, ∀ y : ℝ, max Y 0 ≤ y → ∀ φ : BruhatCompactSupport C𝔽,
            (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
            ∀ (a : archTest) (b : finiteTest), archRestricts(φ, a) → finiteRestricts(φ, b) →
              ‖nonpolarLocalTerms(a, b)‖ ≤ ε * Real.exp (α * y) := by
  rw [hasSum_exteriorZeros_iff_isEmpty τ hτ α]
  constructor
  · intro hE ψ hψ H hH hHc _ hpol₁ hpol₂ ε hε
    have ht := endpoint_translatedLocalTerms_tendsto_zero_of_isEmpty τ hτ hE ψ hψ H hH hHc
    obtain ⟨Y, hY⟩ := Filter.eventually_atTop.mp
      ((Metric.tendsto_nhds.mp ht) ε hε)
    refine ⟨Y, fun y hy φ hφ a b ha hb ↦ ?_⟩
    have hlt := hY y ((le_max_left Y 0).trans hy)
    rw [dist_zero_right] at hlt
    have hsum := endpoint_translatedLocalTerms_hasSum τ hτ ψ hψ H hH hHc y φ hφ a b ha hb
    have hp₁ := endpoint_polar_mellin_eq_zero τ hτ ψ hψ H hH hHc y φ hφ (1 / 2) hpol₁
    have hp₂ := endpoint_polar_mellin_eq_zero τ hτ ψ hψ H hH hHc y φ hφ (-1 / 2) hpol₂
    have hloc_eq : localTerms(φ, a, b) = nonpolarLocalTerms(a, b) := by
      rw [hp₁, hp₂]; ring
    have hscale : (∑' z : characterZeros(ψ⁻¹),
        translatedCoeff(ψ⁻¹, H, z) * Complex.exp (((z : ℂ) - 1 / 2 - α) * y)) =
        Complex.exp (-((α : ℂ) * y)) * nonpolarLocalTerms(a, b) := by
      rw [← hloc_eq, ← hsum.tsum_eq, ← tsum_mul_left]
      refine tsum_congr fun z ↦ ?_
      have hexp : Complex.exp (((z : ℂ) - 1 / 2 - α) * y) =
          Complex.exp (-((α : ℂ) * y)) * Complex.exp (((z : ℂ) - 1 / 2) * y) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [hexp]
      ring
    rw [hscale, norm_mul, Complex.norm_exp] at hlt
    have hre : (-((α : ℂ) * (y : ℂ))).re = -α * y := by simp
    rw [hre] at hlt
    have hmul := mul_lt_mul_of_pos_right hlt (Real.exp_pos (α * y))
    have hcancel : Real.exp (-α * y) * ‖nonpolarLocalTerms(a, b)‖ * Real.exp (α * y) =
        ‖nonpolarLocalTerms(a, b)‖ := by
      calc Real.exp (-α * y) * ‖nonpolarLocalTerms(a, b)‖ * Real.exp (α * y)
          = ‖nonpolarLocalTerms(a, b)‖ * (Real.exp (-α * y) * Real.exp (α * y)) := by ring
        _ = ‖nonpolarLocalTerms(a, b)‖ := by
            rw [← Real.exp_add, show -α * y + α * y = 0 by ring, Real.exp_zero, mul_one]
    rw [hcancel] at hmul
    exact hmul.le
  · intro hloc
    by_contra hne
    obtain ⟨z⟩ := not_isEmpty_iff.mp hne
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : exteriorZeros(τ, α), 1 / 2 ≤ z₀.val.2.re := by
      rcases le_or_gt (1 / 2) z.val.2.re with h | h
      · exact ⟨z, h⟩
      · have habs : |(1 - z.val.2).re - 1 / 2| = |z.val.2.re - 1 / 2| := by
          rw [Complex.sub_re, Complex.one_re,
            show 1 - z.val.2.re - 1 / 2 = -(z.val.2.re - 1 / 2) by ring, abs_neg]
        refine ⟨⟨(⟨z.val.1.val⁻¹, fun t ↦ ?_⟩, 1 - z.val.2),
          (endpoint_ord_reflection z.val.1.val z.val.2).symm ▸ z.property.1,
          habs.symm ▸ z.property.2⟩, ?_⟩
        · change (z.val.1.val (τ t))⁻¹ = 1
          rw [z.val.1.property t, inv_one]
        · change 1 / 2 ≤ (1 - z.val.2).re
          rw [Complex.sub_re, Complex.one_re]
          linarith
    have hstrip : |z₀.val.2.re - 1 / 2| < 1 / 2 := lt_of_not_ge fun h ↦
      (endpoint_isEmpty_half_le τ hτ (le_refl (1 / 2 : ℝ))).false ⟨z₀.val, z₀.property.1, h⟩
    have hw_strip : |(z₀.val.2 - 1 / 2).re| < 1 / 2 := by
      rw [Complex.sub_re]; norm_num; simpa using hstrip
    obtain ⟨H₀, hH₀, hH₀c, hH₀v, hpol₁, hpol₂, hKne⟩ :=
      endpoint_exists_detecting_profile hw_strip
    let χ₀ := z₀.val.1.val
    have hχ₀ := z₀.val.1.property
    have hinv (t) : χ₀⁻¹ (τ t) = 1 := by change (χ₀ (τ t))⁻¹ = 1; rw [hχ₀, inv_one]
    have hg (y : ℝ) : ContDiff ℝ (∞) (fun x ↦ H₀ (x - y)) :=
      hH₀.comp (contDiff_id.sub contDiff_const)
    have hgc (y : ℝ) : HasCompactSupport (fun x ↦ H₀ (x - y)) :=
      hH₀c.comp_homeomorph (Homeomorph.subRight y)
    choose φ hφ using fun y : ℝ ↦ exists_characterNormTest (F := F) χ₀⁻¹ _ (hg y) (hgc y)
    let ψ₁ : PontryaginDual C𝔽 := χ₀⁻¹
    let ι := characterZeros(ψ₁⁻¹)
    let w : ι → ℂ := fun i ↦ i.val - 1 / 2
    let b : ι → ℂ := fun i ↦ translatedCoeff(ψ₁⁻¹, H₀, i)
    let Sfun : ℝ → ℂ := fun y ↦ ∑' i : ι, b i * Complex.exp (w i * y)
    have hL_hasSum (y : ℝ) : ∃ (a_y : archTest) (b_y : finiteTest),
        archRestricts(φ y, a_y) ∧ finiteRestricts(φ y, b_y) ∧
        HasSum (fun i : ι ↦ b i * Complex.exp (w i * y)) (nonpolarLocalTerms(a_y, b_y)) := by
      obtain ⟨a_y, b_y, ha_y, hb_y, -, -⟩ := traceFormula_of_half_le τ hτ (φ y) (le_refl (1 / 2 : ℝ))
      have hsum := endpoint_translatedLocalTerms_hasSum τ hτ ψ₁ hinv H₀ hH₀ hH₀c y (φ y)
        (hφ y) a_y b_y ha_y hb_y
      have hp₁ := endpoint_polar_mellin_eq_zero τ hτ ψ₁ hinv H₀ hH₀ hH₀c y (φ y) (hφ y)
        (1 / 2) hpol₁
      have hp₂ := endpoint_polar_mellin_eq_zero τ hτ ψ₁ hinv H₀ hH₀ hH₀c y (φ y) (hφ y)
        (-1 / 2) hpol₂
      have hloc_eq : localTerms(φ y, a_y, b_y) = nonpolarLocalTerms(a_y, b_y) := by
        rw [hp₁, hp₂]; ring
      rw [hloc_eq] at hsum
      exact ⟨a_y, b_y, ha_y, hb_y, hsum⟩
    have hb_sum : Summable b := by
      obtain ⟨_, _, _, _, hs0⟩ := hL_hasSum 0
      simp only [w, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hs0
      exact hs0.summable
    have hS_hasSum : ∀ y : ℝ, 0 ≤ y → HasSum (fun i : ι ↦ b i * Complex.exp (w i * y)) (Sfun y) := by
      intro y _
      obtain ⟨_, _, _, _, hsy⟩ := hL_hasSum y
      exact hsy.summable.hasSum
    have hw : Function.Injective w := fun i j hij ↦ Subtype.ext (sub_left_inj.mp hij)
    have hdisc : ∀ z' : ℂ, ∀ᶠ u in 𝓝[≠] z', u ∉ Set.range w := fun z' ↦ by
      filter_upwards [endpoint_zeros_discrete ψ₁⁻¹ z'] with u hu
      rintro ⟨i, rfl⟩
      exact hu (by simpa [w] using i.property)
    have hre : ∀ i : ι, (w i).re ≤ 1 / 2 := fun i ↦ by
      have h := endpoint_zero_re_le_one ψ₁⁻¹ i.property
      change (i.val - 1 / 2).re ≤ 1 / 2
      rw [Complex.sub_re]; norm_num; linarith
    have ho : Tendsto (fun y : ℝ ↦ ‖Sfun y‖ * Real.exp (-α * y)) atTop (𝓝 0) := by
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨Y, hY⟩ := hloc χ₀⁻¹ hinv H₀ hH₀ hH₀c hH₀v hpol₁ hpol₂ (ε / 2) (half_pos hε)
      filter_upwards [eventually_ge_atTop (max Y 0)] with y hy
      have hy0 : 0 ≤ y := (le_max_right Y 0).trans hy
      obtain ⟨a_y, b_y, ha_y, hb_y, hsy⟩ := hL_hasSum y
      have hSeq : Sfun y = nonpolarLocalTerms(a_y, b_y) := (hS_hasSum y hy0).unique hsy
      have hbd := hY y hy (φ y) (hφ y) a_y b_y ha_y hb_y
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (norm_nonneg _) (Real.exp_pos _).le), hSeq]
      calc ‖nonpolarLocalTerms(a_y, b_y)‖ * Real.exp (-α * y)
          ≤ (ε / 2 * Real.exp (α * y)) * Real.exp (-α * y) :=
            mul_le_mul_of_nonneg_right hbd (Real.exp_pos _).le
        _ = ε / 2 := by
            rw [mul_assoc, ← Real.exp_add, show α * y + -α * y = 0 by ring, Real.exp_zero, mul_one]
        _ < ε := half_lt_self hε
    let i₀ : ι := ⟨z₀.val.2, by dsimp [ψ₁]; rw [inv_inv]; exact z₀.property.1⟩
    have hre₀ : α ≤ (w i₀).re := by
      have h2 := z₀.property.2
      rw [abs_of_nonneg (by linarith)] at h2
      change α ≤ (z₀.val.2 - 1 / 2).re
      rw [Complex.sub_re]; norm_num; linarith
    have h0 := eq_zero_of_hasSum_exp_of_tendsto_zero w b hw hdisc hre hb_sum Sfun hS_hasSum ho
      i₀ hre₀
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (Int.cast_ne_zero.mpr i₀.property.ne')
    · exact hKne ((mul_eq_zero.mp h).resolve_left endpoint_classVolume_ne_zero)

/-- **Exact fixed-width Cesàro local-terms characterization of `traceFormula_exteriorZeros`.**
At **every single fixed half-width `α > 0`**, the exterior-zero sum vanishes for all norm-one-vanishing
tests **if and only if** the pure non-polar signed local terms of every polar-free translated profile
supported on `(0, ∞)` admit an `exp(-α y)`-weighted Cesàro-`o(1)` majorant on `(0, ∞)`. -/
theorem hasSum_exteriorZeros_iff_localTerms_cesaro (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) {α : ℝ} (_hα : 0 < α) :
    (∀ φ : BruhatCompactSupport C𝔽, (∀ g : C₁, φ.val g = 0) →
      HasSum (fun z : exteriorZeros(τ, α) ↦ zeroTerm(φ, z)) 0) ↔
      ∀ (ψ : PontryaginDual C𝔽), (∀ t, ψ (τ t) = 1) →
        ∀ (H : ℝ → ℂ), ContDiff ℝ (∞) H → HasCompactSupport H → (∀ x ≤ 0, H x = 0) →
          (∫ x : ℝ, H x * Complex.exp ((1 / 2 : ℂ) * x) = 0) →
          (∫ x : ℝ, H x * Complex.exp ((-1 / 2 : ℂ) * x) = 0) →
          ∃ D : ℝ → ℝ,
            (∀ Y > 0, IntegrableOn (fun y ↦ D y * Real.exp (-α * y)) (Ioc (0 : ℝ) Y)) ∧
            Tendsto (fun Y : ℝ ↦ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, D y * Real.exp (-α * y))
              atTop (𝓝 0) ∧
            ∀ y : ℝ, 0 ≤ y → ∀ φ : BruhatCompactSupport C𝔽,
              (∀ x, φ.val x = (ψ x : ℂ) * H (Real.log ((ideleClassNorm F x : ℝ≥0) : ℝ) - y)) →
              ∀ (a : archTest) (b : finiteTest), archRestricts(φ, a) → finiteRestricts(φ, b) →
                ‖nonpolarLocalTerms(a, b)‖ ≤ D y := by
  constructor
  · intro hX ψ hψ H hH hHc _ hpol₁ hpol₂
    have hE := (hasSum_exteriorZeros_iff_isEmpty τ hτ α).mp hX
    have ht := endpoint_translatedLocalTerms_tendsto_zero_of_isEmpty τ hτ hE ψ hψ H hH hHc
    let g : ℝ → ℝ := fun y ↦ ‖∑' z : characterZeros(ψ⁻¹),
      translatedCoeff(ψ⁻¹, H, z) * Complex.exp (((z : ℂ) - 1 / 2 - α) * y)‖
    let D : ℝ → ℝ := fun y ↦ g y * Real.exp (α * y)
    have hDg : ∀ y : ℝ, D y * Real.exp (-α * y) = g y := fun y ↦ by
      dsimp [D]
      rw [mul_assoc, ← Real.exp_add, show α * y + -α * y = 0 by ring, Real.exp_zero, mul_one]
    have hg_cont : ContinuousOn g (Ici 0) := by
      have hinv (t) : ψ⁻¹ (τ t) = 1 := by change (ψ (τ t))⁻¹ = 1; rw [hψ, inv_one]
      have hc_sum : Summable (fun z : characterZeros(ψ⁻¹) ↦ ‖translatedCoeff(ψ⁻¹, H, z)‖) := by
        obtain ⟨f, hf⟩ := exists_characterNormTest (F := F) ψ H hH hHc
        obtain ⟨a, b, ha, hb, -, -⟩ := traceFormula_of_half_le τ hτ f (le_refl (1 / 2 : ℝ))
        have h0 := endpoint_translatedLocalTerms_hasSum τ hτ ψ hψ H hH hHc 0 f (by simpa using hf)
          a b ha hb
        simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h0
        exact h0.summable.norm
      have hcont_tsum : ContinuousOn (fun y : ℝ ↦ ∑' z : characterZeros(ψ⁻¹),
          translatedCoeff(ψ⁻¹, H, z) * Complex.exp (((z : ℂ) - 1 / 2 - α) * y)) (Ici 0) := by
        refine continuousOn_tsum (u := fun z : characterZeros(ψ⁻¹) ↦ ‖translatedCoeff(ψ⁻¹, H, z)‖)
          (fun z ↦ (by fun_prop : Continuous fun y : ℝ ↦
            translatedCoeff(ψ⁻¹, H, z) * Complex.exp (((z : ℂ) - 1 / 2 - α) * y)).continuousOn)
          hc_sum fun z y hy ↦ ?_
        rw [norm_mul, Complex.norm_exp]
        have hin : |z.val.re - 1 / 2| < α :=
          lt_of_not_ge fun hge ↦ hE.false ⟨(⟨ψ⁻¹, hinv⟩, z.val), z.property, hge⟩
        have hre_y : (((z : ℂ) - 1 / 2 - α) * (y : ℂ)).re = (z.val.re - 1 / 2 - α) * y := by
          simp [Complex.sub_re]
        rw [hre_y]
        exact mul_le_of_le_one_right (norm_nonneg _)
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
            (by linarith [(abs_lt.mp hin).2]) hy))
      exact hcont_tsum.norm
    have hg_loc : ∀ Y ≥ 0, IntegrableOn g (Ioc 0 Y) := fun Y _ ↦
      ((hg_cont.mono Icc_subset_Ici_self).integrableOn_Icc).mono_set
        (Ioc_subset_Icc_self.trans (Icc_subset_Icc_right (le_max_left Y 0)))
    refine ⟨D, fun Y hY ↦ ?_, ?_, fun y _ φ hφ a b ha hb ↦ ?_⟩
    · simp_rw [hDg]
      exact hg_loc Y hY.le
    · simp_rw [hDg]
      have hg_zero : Tendsto g atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.mp
        (by simpa [g] using ht)
      rw [Metric.tendsto_nhds]
      intro ε hε
      obtain ⟨Y₀, hY₀⟩ := Filter.eventually_atTop.mp (hg_zero.eventually (gt_mem_nhds (half_pos hε)))
      set A := max Y₀ 1
      have hA0 : 0 ≤ A := by positivity
      set M₀ := ∫ y in Ioc (0 : ℝ) A, g y
      filter_upwards [eventually_ge_atTop (max A (2 * (M₀ + 1) / ε))] with Y hY
      have hYA : A ≤ Y := (le_max_left _ _).trans hY
      have hYpos : 0 < Y := lt_of_lt_of_le zero_lt_one ((le_max_right Y₀ 1).trans hYA)
      have hnonneg : 0 ≤ Y⁻¹ * ∫ y in Ioc (0 : ℝ) Y, g y :=
        mul_nonneg (inv_nonneg.mpr hYpos.le) (setIntegral_nonneg measurableSet_Ioc fun _ _ ↦
          norm_nonneg _)
      have hdisj : Disjoint (Ioc (0 : ℝ) A) (Ioc A Y) :=
        Set.disjoint_left.mpr fun _ ht1 ht2 ↦ ht1.2.not_gt ht2.1
      have hunion : (∫ y in Ioc (0 : ℝ) Y, g y) = M₀ + ∫ y in Ioc A Y, g y := by
        rw [← Ioc_union_Ioc_eq_Ioc hA0 hYA,
          setIntegral_union hdisj measurableSet_Ioc (hg_loc A hA0)
            ((hg_loc Y hYpos.le).mono_set (Ioc_subset_Ioc_left hA0))]
      have htail : (∫ y in Ioc A Y, g y) ≤ (ε / 2) * Y := by
        calc (∫ y in Ioc A Y, g y)
            ≤ ∫ _ in Ioc A Y, ε / 2 :=
              setIntegral_mono_on ((hg_loc Y hYpos.le).mono_set (Ioc_subset_Ioc_left hA0))
                (integrableOn_const (by simp)) measurableSet_Ioc fun y hy ↦
                  (hY₀ y ((le_max_left Y₀ 1).trans hy.1.le)).le
          _ = (Y - A) * (ε / 2) := by
              rw [setIntegral_const, Real.volume_real_Ioc_of_le hYA, smul_eq_mul]
          _ ≤ (ε / 2) * Y := by nlinarith
      have hM_lt : M₀ < (ε / 2) * Y := by
        have hY2 : 2 * (M₀ + 1) / ε ≤ Y := (le_max_right _ _).trans hY
        have hmul := (div_le_iff₀ hε).mp hY2
        linarith
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg, hunion]
      calc Y⁻¹ * (M₀ + ∫ y in Ioc A Y, g y)
          < Y⁻¹ * ((ε / 2) * Y + (ε / 2) * Y) :=
            mul_lt_mul_of_pos_left (add_lt_add_of_lt_of_le hM_lt htail) (inv_pos.mpr hYpos)
        _ = ε := by field_simp [hYpos.ne']; ring
    · have hsum := endpoint_translatedLocalTerms_hasSum τ hτ ψ hψ H hH hHc y φ hφ a b ha hb
      have hp₁ := endpoint_polar_mellin_eq_zero τ hτ ψ hψ H hH hHc y φ hφ (1 / 2) hpol₁
      have hp₂ := endpoint_polar_mellin_eq_zero τ hτ ψ hψ H hH hHc y φ hφ (-1 / 2) hpol₂
      have hloc_eq : localTerms(φ, a, b) = nonpolarLocalTerms(a, b) := by
        rw [hp₁, hp₂]; ring
      have hscale : (∑' z : characterZeros(ψ⁻¹),
          translatedCoeff(ψ⁻¹, H, z) * Complex.exp (((z : ℂ) - 1 / 2 - α) * y)) =
          Complex.exp (-((α : ℂ) * y)) * nonpolarLocalTerms(a, b) := by
        rw [← hloc_eq, ← hsum.tsum_eq, ← tsum_mul_left]
        refine tsum_congr fun z ↦ ?_
        have hexp : Complex.exp (((z : ℂ) - 1 / 2 - α) * y) =
            Complex.exp (-((α : ℂ) * y)) * Complex.exp (((z : ℂ) - 1 / 2) * y) := by
          rw [← Complex.exp_add]
          congr 1
          ring
        rw [hexp]
        ring
      dsimp [D, g]
      rw [hscale, norm_mul, Complex.norm_exp]
      have hre : (-((α : ℂ) * (y : ℂ))).re = -α * y := by simp
      rw [hre]
      refine le_of_eq ?_
      calc ‖nonpolarLocalTerms(a, b)‖
          = ‖nonpolarLocalTerms(a, b)‖ * (Real.exp (-α * y) * Real.exp (α * y)) := by
              rw [← Real.exp_add, show -α * y + α * y = 0 by ring, Real.exp_zero, mul_one]
        _ = Real.exp (-α * y) * ‖nonpolarLocalTerms(a, b)‖ * Real.exp (α * y) := by ring
  · intro hces_all
    rw [hasSum_exteriorZeros_iff_isEmpty τ hτ α]
    by_contra hne
    obtain ⟨z⟩ := not_isEmpty_iff.mp hne
    obtain ⟨z₀, hz₀⟩ : ∃ z₀ : exteriorZeros(τ, α), 1 / 2 ≤ z₀.val.2.re := by
      rcases le_or_gt (1 / 2) z.val.2.re with h | h
      · exact ⟨z, h⟩
      · have habs : |(1 - z.val.2).re - 1 / 2| = |z.val.2.re - 1 / 2| := by
          rw [Complex.sub_re, Complex.one_re,
            show 1 - z.val.2.re - 1 / 2 = -(z.val.2.re - 1 / 2) by ring, abs_neg]
        refine ⟨⟨(⟨z.val.1.val⁻¹, fun t ↦ ?_⟩, 1 - z.val.2),
          (endpoint_ord_reflection z.val.1.val z.val.2).symm ▸ z.property.1,
          habs.symm ▸ z.property.2⟩, ?_⟩
        · change (z.val.1.val (τ t))⁻¹ = 1
          rw [z.val.1.property t, inv_one]
        · change 1 / 2 ≤ (1 - z.val.2).re
          rw [Complex.sub_re, Complex.one_re]
          linarith
    have hstrip : |z₀.val.2.re - 1 / 2| < 1 / 2 := lt_of_not_ge fun h ↦
      (endpoint_isEmpty_half_le τ hτ (le_refl (1 / 2 : ℝ))).false ⟨z₀.val, z₀.property.1, h⟩
    have hw_strip : |(z₀.val.2 - 1 / 2).re| < 1 / 2 := by
      rw [Complex.sub_re]; norm_num; simpa using hstrip
    obtain ⟨H₀, hH₀, hH₀c, hH₀v, hpol₁, hpol₂, hKne⟩ :=
      endpoint_exists_detecting_profile hw_strip
    let χ₀ := z₀.val.1.val
    have hχ₀ := z₀.val.1.property
    have hinv (t) : χ₀⁻¹ (τ t) = 1 := by change (χ₀ (τ t))⁻¹ = 1; rw [hχ₀, inv_one]
    obtain ⟨D, hDloc, hces, hDbd⟩ := hces_all χ₀⁻¹ hinv H₀ hH₀ hH₀c hH₀v hpol₁ hpol₂
    have hg (y : ℝ) : ContDiff ℝ (∞) (fun x ↦ H₀ (x - y)) :=
      hH₀.comp (contDiff_id.sub contDiff_const)
    have hgc (y : ℝ) : HasCompactSupport (fun x ↦ H₀ (x - y)) :=
      hH₀c.comp_homeomorph (Homeomorph.subRight y)
    choose φ hφ using fun y : ℝ ↦ exists_characterNormTest (F := F) χ₀⁻¹ _ (hg y) (hgc y)
    let ψ₁ : PontryaginDual C𝔽 := χ₀⁻¹
    let ι := characterZeros(ψ₁⁻¹)
    let w : ι → ℂ := fun i ↦ i.val - 1 / 2
    let b : ι → ℂ := fun i ↦ translatedCoeff(ψ₁⁻¹, H₀, i)
    let Sfun : ℝ → ℂ := fun y ↦ ∑' i : ι, b i * Complex.exp (w i * y)
    have hL_hasSum (y : ℝ) : ∃ (a_y : archTest) (b_y : finiteTest),
        archRestricts(φ y, a_y) ∧ finiteRestricts(φ y, b_y) ∧
        HasSum (fun i : ι ↦ b i * Complex.exp (w i * y)) (nonpolarLocalTerms(a_y, b_y)) := by
      obtain ⟨a_y, b_y, ha_y, hb_y, -, -⟩ := traceFormula_of_half_le τ hτ (φ y) (le_refl (1 / 2 : ℝ))
      have hsum := endpoint_translatedLocalTerms_hasSum τ hτ ψ₁ hinv H₀ hH₀ hH₀c y (φ y)
        (hφ y) a_y b_y ha_y hb_y
      have hp₁ := endpoint_polar_mellin_eq_zero τ hτ ψ₁ hinv H₀ hH₀ hH₀c y (φ y) (hφ y)
        (1 / 2) hpol₁
      have hp₂ := endpoint_polar_mellin_eq_zero τ hτ ψ₁ hinv H₀ hH₀ hH₀c y (φ y) (hφ y)
        (-1 / 2) hpol₂
      have hloc_eq : localTerms(φ y, a_y, b_y) = nonpolarLocalTerms(a_y, b_y) := by
        rw [hp₁, hp₂]; ring
      rw [hloc_eq] at hsum
      exact ⟨a_y, b_y, ha_y, hb_y, hsum⟩
    have hb_sum : Summable b := by
      obtain ⟨_, _, _, _, hs0⟩ := hL_hasSum 0
      simp only [w, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hs0
      exact hs0.summable
    have hS_hasSum : ∀ y : ℝ, 0 ≤ y → HasSum (fun i : ι ↦ b i * Complex.exp (w i * y)) (Sfun y) := by
      intro y _
      obtain ⟨_, _, _, _, hsy⟩ := hL_hasSum y
      exact hsy.summable.hasSum
    have hS_le : ∀ y : ℝ, 0 ≤ y → ‖Sfun y‖ ≤ D y := fun y hy ↦ by
      obtain ⟨a_y, b_y, ha_y, hb_y, hsy⟩ := hL_hasSum y
      rw [(hS_hasSum y hy).unique hsy]
      exact hDbd y hy (φ y) (hφ y) a_y b_y ha_y hb_y
    have hw : Function.Injective w := fun i j hij ↦ Subtype.ext (sub_left_inj.mp hij)
    have hdisc : ∀ z' : ℂ, ∀ᶠ u in 𝓝[≠] z', u ∉ Set.range w := fun z' ↦ by
      filter_upwards [endpoint_zeros_discrete ψ₁⁻¹ z'] with u hu
      rintro ⟨i, rfl⟩
      exact hu (by simpa [w] using i.property)
    have hre : ∀ i : ι, (w i).re ≤ 1 / 2 := fun i ↦ by
      have h := endpoint_zero_re_le_one ψ₁⁻¹ i.property
      change (i.val - 1 / 2).re ≤ 1 / 2
      rw [Complex.sub_re]; norm_num; linarith
    let i₀ : ι := ⟨z₀.val.2, by dsimp [ψ₁]; rw [inv_inv]; exact z₀.property.1⟩
    have hre₀ : α ≤ (w i₀).re := by
      have h2 := z₀.property.2
      rw [abs_of_nonneg (by linarith)] at h2
      change α ≤ (z₀.val.2 - 1 / 2).re
      rw [Complex.sub_re]; norm_num; linarith
    have h0 := eq_zero_of_hasSum_exp_of_cesaro_majorant w b hw hdisc hre hb_sum Sfun hS_hasSum
      D hS_le hDloc hces i₀ hre₀
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (Int.cast_ne_zero.mpr i₀.property.ne')
    · exact hKne ((mul_eq_zero.mp h).resolve_left endpoint_classVolume_ne_zero)

end RiemannMasullo
