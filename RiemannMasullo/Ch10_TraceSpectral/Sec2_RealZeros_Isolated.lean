module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch10_TraceSpectral.Sec2_Basepoint
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import RiemannMasullo.Ch09_HardySobolev.Sec2
import RiemannMasullo.Ch13_ZerosHecke.RationalExteriorZeros
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.HeckeLFunction
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.Order.OrderIsoNat

/-! # Real-segment multiple zeros of completed Hecke L-functions (#7485)

This isolation file records standalone characterizations of
`spectralStripJet_multiple_real_zeros_finite` (`Sec2`, Proposition 10.2.2.2, pp. 446–447, #7485)
without modifying any declaration on `main` or adding any `sorry`.

* General number field `F`:
  * `spectralStripJet_multiple_real_zeros_finite_iff_symmetric_finite_cover`:
    upgrades the `#7504` finite cover to a symmetric finite cover `(E, S)` of all multiple zeros
    in `ℂ` (`E = E⁻¹`, `S = 1 - S`, `1 / 2 ∈ S`).
  * `spectralStripJet_multiple_real_zeros_finite_iff_no_monotone_matching`:
    exact infinite-obstruction equivalence in terms of sequences of characters with pairwise
    distinct norm-one restrictions and strictly monotone (or strictly antitone) real multiple zeros
    in `(1 / 2, 1)`.
  * `spectralStripJet_multiple_real_zeros_finite_iff_cofinite_orderOne_upperBound` and
    `spectralStripJet_multiple_real_zeros_finite_iff_cofinite_boundedOrder_upperBound`:
    exact strip-jet norm characterizations of `#7485` alone (independent of `#7220` and `#7453`) via
    boundedness of order-one or bounded-order strip jets outside a finite exceptional component set.

* Rational field `F = ℚ`:
  * `spectralStripJet_multiple_real_zeros_finite_rat_iff_dirichlet`:
    exact classical equivalence over `ℚ` with a conductor threshold `B` and finite set `S` of
    abscissae containing the real parts of all right-half multiple zeros of primitive Dirichlet
    `L`-functions of conductor `N > B`.
  * `dirichletL_uniform_multiple_zero_free_strip_of_multiple_real_zeros_finite_rat`:
    corollary giving a conductor- and height-uniform multiple-zero-free strip `1 - δ < Re z < 1`
    for all Dirichlet characters (primitive or imprimitive) of conductor `> B`.
  * `spectralStripJet_multiple_real_zeros_finite_rat_of_dirichlet_offline_simple` and
    `spectralStripJet_multiple_real_zeros_finite_rat_of_dirichletGRH`:
    sufficiency of cofinite off-line simplicity and of `DirichletLNonvanishingRightOfHalf`.
  * `spectralStripJet_multiple_zero_lines_finite_rat_iff_dirichlet`:
    exact Dirichlet characterization of `#7453 ∧ #7485` over `ℚ`.

Nothing here is imported by the rest of the library. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

section GeneralField

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hm𝔽" =>
  (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "restriction" =>
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "mult(" χ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL χ) z).untop₀.toNat
local notation "stripJet(" χ ", " j ")" =>
  spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "jetLp(" χ ", " hα ", " hs ", " j ")" =>
  (spectralStripJet_memLp χ hα hs₀(hs) j).toLp (stripJet(χ, j))
local notation "L2μ'(" l ", " r ", " s ")" => (μ𝔽 |>.withDensity fun g ↦
  ENNReal.ofReal (intervalSobolevDensity l r s (logNorm g))⁻¹)

/-! ### Private analytic helpers for multiple-zero reflection and strip-jet norms -/

/-- A completed Hecke `L`-function has no zero outside the closed critical strip `[0, 1]`. -/
private theorem realZeros_mult_eq_zero_of_not_mem_Icc
    (ψ : PontryaginDual C𝔽) (z : ℂ) (hz : z.re ∉ Icc (0 : ℝ) 1) : mult(ψ, z) = 0 := by
  have hne (θ : PontryaginDual C𝔽) {w : ℂ} (hw : 1 < w.re) :
      continuedCompletedHeckeL θ w ≠ 0 := by
    rw [show continuedCompletedHeckeL θ w = completedHeckeL θ ⟨w, hw⟩ from
      (continuedCompletedHeckeL_spec θ).2 ⟨w, hw⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos θ (zero_lt_one.trans hw))
      (finiteHeckeL_ne_zero_of_one_lt_re θ ⟨w, hw⟩)
  have hval : continuedCompletedHeckeL ψ z ≠ 0 := by
    rcases lt_or_ge z.re 0 with hneg | hn
    · obtain ⟨ε, _, _, he⟩ := completedHeckeL_continuation_functionalEquation ψ _ _
        (continuedCompletedHeckeL_spec ψ).1 (continuedCompletedHeckeL_spec ψ).2
        (continuedCompletedHeckeL_spec ψ⁻¹).1 (continuedCompletedHeckeL_spec ψ⁻¹).2
      have hw : 1 < (1 - z).re := by
        simp only [Complex.sub_re, Complex.one_re]
        linarith
      intro h0
      exact hne ψ⁻¹ hw (by rw [he z, h0, mul_zero])
    · exact hne ψ (lt_of_not_ge fun h ↦ hz ⟨hn, h⟩)
  rw [((continuedCompletedHeckeL_spec ψ).1 (mem_univ z)).meromorphicOrderAt_eq_zero_iff.mpr hval]
  rfl

/-- Any zero of `continuedCompletedHeckeL ψ` with `1 / 2 < Re z` has `Re z < 1`. -/
private theorem realZeros_re_lt_one (ψ : PontryaginDual C𝔽) {σ t : ℝ}
    (hσ : 1 / 2 < σ) (h : 0 < mult(ψ, shift(σ, t))) : σ < 1 := by
  have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL ψ) (shift(σ, t)) := by
    generalize meromorphicOrderAt (continuedCompletedHeckeL ψ) (shift(σ, t)) = o at *
    cases o with
    | top => simp at h
    | coe k =>
      rw [WithTop.untop₀_coe] at h
      exact_mod_cast (by omega : 0 < k)
  simpa using completedHeckeL_continuation_zeros ψ _ (continuedCompletedHeckeL_spec ψ).1
    (continuedCompletedHeckeL_spec ψ).2 (by simpa using (show 0 < σ by linarith)) hp

/-- Completed functional equation preserves zero multiplicity under `z ↦ 1 - z` and `ψ ↦ ψ⁻¹`. -/
private theorem realZeros_mult_reflect (ψ : PontryaginDual C𝔽) (σ t : ℝ) :
    mult(ψ, shift(σ, t)) = mult(ψ⁻¹, shift(1 - σ, (-t : ℝ))) := by
  obtain ⟨ε, hε, hne, he⟩ := completedHeckeL_continuation_functionalEquation ψ _ _
    (continuedCompletedHeckeL_spec ψ).1 (continuedCompletedHeckeL_spec ψ).2
    (continuedCompletedHeckeL_spec ψ⁻¹).1 (continuedCompletedHeckeL_spec ψ⁻¹).2
  let r (z : ℂ) := 1 - z
  have heq : continuedCompletedHeckeL ψ⁻¹ ∘ r = ε * continuedCompletedHeckeL ψ := funext he
  have hr : HasDerivAt r (-1) (shift(σ, t)) := (hasDerivAt_id _).const_sub 1
  have ho := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL ψ⁻¹)
    (show AnalyticAt ℂ r (shift(σ, t)) by dsimp [r]; fun_prop) (hr.deriv.trans_ne (by norm_num))
  rw [heq, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt _) (hne _)] at ho
  have hz : r (shift(σ, t)) = shift(1 - σ, (-t : ℝ)) := by
    dsimp [r]
    push_cast
    ring
  rw [hz] at ho
  rw [ho]

/-- Recentering a unitary Hecke character by `|·|^{it}` preserves its norm-one restriction and
translates all zero multiplicities vertically to ordinate zero. -/
private theorem realZeros_recenter (ψ : PontryaginDual C𝔽) (t : ℝ) :
    ∃ θ : PontryaginDual C𝔽, θ.comp restriction = ψ.comp restriction ∧ ∀ σ : ℝ,
      mult(θ, (σ : ℂ)) = mult(ψ, shift(σ, t)) := by
  obtain ⟨d, -, hd⟩ :=
    spectralZeroMultiplicity_existsUnique_shift_of_restriction_eq ψ ψ rfl
  let a := (t : ℂ) * Complex.I
  let c := ideleClassNormTwist ψ a
  have hn (g : C𝔽) : ‖c g‖ = 1 := by
    change ‖(ψ g : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ a)‖ = 1
    rw [norm_mul, Circle.norm_coe, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp [a]
  let θ : PontryaginDual C𝔽 :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hn g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun x y ↦ Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hθ0 : ideleClassNormTwist θ 0 = ideleClassNormTwist ψ a := by
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    simp
  have hθs (s : ℂ) : ideleClassNormTwist θ s = ideleClassNormTwist ψ (s + a) := by
    simpa only [zero_add, add_comm a s] using ideleClassNormTwist_add_of_eq hθ0 s
  have hres : θ.comp restriction = ψ.comp restriction := by
    ext g : 1
    apply Subtype.ext
    change (ψ g.val : ℂ) * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ a) = ψ g.val
    rw [show ideleClassNorm F g.val = 1 from g.property]
    simp
  refine ⟨θ, hres, fun σ ↦ ?_⟩
  have horder (f : adelePolarSubspace F) :
      meromorphicOrderAt (fun s ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist θ s))
        (σ : ℂ) =
      meromorphicOrderAt (fun s ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ s))
        (shift(σ, t)) := by
    simp_rw [hθs]
    simpa only [Function.comp_def, a] using meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt
      (f := fun s ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ s)) (c := a)
      (x := (σ : ℂ))
  have hleast := isLeast_globalThetaMellinIntegral_orders θ (σ : ℂ)
  simp_rw [horder] at hleast
  have he := hleast.unique (isLeast_globalThetaMellinIntegral_orders ψ (shift(σ, t)))
  have hclip (o : WithTop ℤ) : (max 0 o).untop₀.toNat = o.untop₀.toNat := by
    cases o with
    | top => simp
    | coe n => simp only [← WithTop.coe_zero, ← WithTop.coe_max, WithTop.untop₀_coe]; omega
  exact (hclip _).symm.trans ((congrArg (fun o : WithTop ℤ ↦ o.untop₀.toNat) he).trans (hclip _))

private theorem realZeros_lp_norm_sq {μ : Measure C𝔽} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂μ := by
  have hre : (inner ℂ u u).re = ‖u‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) u
  rw [← hre, L2.inner_def]
  have hre_int : (∫ g : C𝔽, inner ℂ (u g) (u g) ∂μ).re =
      ∫ g : C𝔽, (inner ℂ (u g) (u g)).re ∂μ :=
    (Complex.reCLM.integral_comp_comm (L2.integrable_inner u u)).symm
  rw [hre_int]
  refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
  exact inner_self_eq_norm_sq (𝕜 := ℂ) (u g)

private theorem realZeros_zeroJet_norm_sq (χ : PontryaginDual C𝔽) (b t : ℝ) (k : ℕ) (g : C𝔽) :
    ‖spectralZeroJet χ b t k g‖ ^ 2 = Real.exp (2 * b * logNorm g) * (logNorm g) ^ (2 * k) := by
  have hpos : 0 < ((ideleClassNorm F g).val : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))
  have htwist : ‖ideleClassNormTwist χ (shift(b, t)) g‖ = Real.exp (b * logNorm g) := by
    change ‖(χ g : ℂ) * (((ideleClassNorm F g).val : ℝ) : ℂ) ^ shift(b, t)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Real.rpow_def_of_pos hpos,
      mul_comm]
  change ‖ideleClassNormTwist χ (shift(b, t)) g * (logNorm g : ℂ) ^ k‖ ^ 2 = _
  rw [norm_mul, htwist, norm_pow, Complex.norm_real, Real.norm_eq_abs, mul_pow]
  have hexp : Real.exp (b * logNorm g) ^ 2 = Real.exp (2 * b * logNorm g) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hpow : (|logNorm g| ^ k) ^ 2 = (logNorm g) ^ (2 * k) := by
    calc (|logNorm g| ^ k) ^ 2 = (|logNorm g| ^ 2) ^ k := by
          rw [← pow_mul, ← pow_mul, Nat.mul_comm k 2]
      _ = ((logNorm g) ^ 2) ^ k := congrArg (fun y : ℝ ↦ y ^ k) (sq_abs (logNorm g))
      _ = (logNorm g) ^ (2 * k) := (pow_mul _ _ _).symm
  rw [hexp, hpow]

private theorem realZeros_symmDensity_eq {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    intervalSobolevDensity (-α) α s x = Real.exp (2 * α * |x|) * (1 + x ^ 2) ^ (s / 2) := by
  unfold intervalSobolevDensity
  congr 1
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, max_eq_right]
    exact Real.exp_le_exp.mpr (by nlinarith)
  · rw [abs_of_nonpos hx, max_eq_left]
    · congr 1
      ring
    · exact Real.exp_le_exp.mpr (by nlinarith)

private theorem realZeros_symmDensity_pos {α : ℝ} (hα : 0 ≤ α) (s x : ℝ) :
    0 < intervalSobolevDensity (-α) α s x := by
  rw [realZeros_symmDensity_eq hα]
  exact mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos (by positivity) _)

private theorem realZeros_continuous_logNorm : Continuous (fun g : C𝔽 ↦ logNorm g) := by
  change Continuous fun g : C𝔽 ↦ Real.log ((ideleClassNorm F g).val : ℝ)
  have hcoe : Continuous fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (continuousIdeleClassNorm F).continuous)
  exact Continuous.log hcoe fun g ↦ (NNReal.coe_pos.mpr (Units.zero_lt (ideleClassNorm F g))).ne'

private theorem realZeros_symmDensity_inv_continuous {α : ℝ} (hα : 0 ≤ α) (s : ℝ) :
    Continuous (fun g : C𝔽 ↦ (intervalSobolevDensity (-α) α s (logNorm g))⁻¹) := by
  have hρ : Continuous (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) := by
    have heq : (fun g : C𝔽 ↦ intervalSobolevDensity (-α) α s (logNorm g)) =
        fun g : C𝔽 ↦ Real.exp (2 * α * |logNorm g|) * (1 + (logNorm g) ^ 2) ^ (s / 2) :=
      funext fun g ↦ realZeros_symmDensity_eq hα s (logNorm g)
    rw [heq]
    exact (Real.continuous_exp.comp (continuous_const.mul realZeros_continuous_logNorm.abs)).mul
      (((continuous_const : Continuous (fun _ : C𝔽 ↦ (1 : ℝ))).add
        (realZeros_continuous_logNorm.pow 2)).rpow_const fun g ↦ Or.inl (by
          change (1 : ℝ) + (logNorm g) ^ 2 ≠ 0
          positivity))
  exact hρ.inv₀ fun g ↦ (realZeros_symmDensity_pos hα s (logNorm g)).ne'

private theorem realZeros_integrable_pow_mul_rpow_inv {k : ℕ} {s : ℝ} (h : 2 * (k : ℝ) + 1 < s) :
    Integrable (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < s - 2 * k := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hr).mono'
    ((measurable_id.pow_const (2 * k)).mul
      ((measurable_const.add (measurable_id.pow_const 2)).pow_const
        (s / 2)).inv).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hy : 0 < 1 + x ^ 2 := by positivity
  have h1 : x ^ (2 * k) ≤ (1 + x ^ 2) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg x) (by linarith) k
  have h2 : (1 + x ^ 2) ^ (-(s - 2 * k) / 2) = (1 + x ^ 2) ^ k * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    rw [← Real.rpow_natCast (1 + x ^ 2) k, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
    congr 1
    ring
  rw [Real.norm_of_nonneg (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
    (inv_nonneg.2 (Real.rpow_nonneg hy.le _))), Real.norm_eq_abs, sq_abs, h2]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (Real.rpow_nonneg hy.le _))

private theorem realZeros_integrable_exp_neg_abs_mul_pow {c : ℝ} (hc : 0 < c) (k : ℕ) :
    Integrable (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) volume := by
  have hcont : Continuous (fun x : ℝ ↦ Real.exp (-c * |x|) * x ^ (2 * k)) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_abs)).mul (continuous_id.pow (2 * k))
  let M : ℝ := ((2 * k).factorial : ℝ) / c ^ (2 * k) +
    ((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)
  have hdom : Integrable (fun x : ℝ ↦ M * (1 + x ^ 2)⁻¹) volume :=
    integrable_inv_one_add_sq.const_mul M
  refine hdom.mono' hcont.aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hnonneg : 0 ≤ Real.exp (-c * |x|) * x ^ (2 * k) :=
    mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x)
  rw [Real.norm_of_nonneg hnonneg]
  have hu : 0 ≤ c * |x| := mul_nonneg hc.le (abs_nonneg x)
  have h1 := Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k)
  have h2 := Real.pow_div_factorial_le_exp (c * |x|) hu (2 * k + 2)
  have hfac1 : (0 : ℝ) < ((2 * k).factorial : ℝ) := by positivity
  have hfac2 : (0 : ℝ) < ((2 * k + 2).factorial : ℝ) := by positivity
  have hc1 : 0 < c ^ (2 * k) := pow_pos hc _
  have hc2 : 0 < c ^ (2 * k + 2) := pow_pos hc _
  have hpow1 : x ^ (2 * k) ≤ (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k) ≤ ((2 * k).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac1).mp h1]
    have hxa : |x| ^ (2 * k) = x ^ (2 * k) := by rw [pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc1]
    linarith
  have hpow2 : x ^ (2 * k) * x ^ 2 ≤
      (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
    have hmul : (c * |x|) ^ (2 * k + 2) ≤ ((2 * k + 2).factorial : ℝ) * Real.exp (c * |x|) := by
      linarith [(div_le_iff₀ hfac2).mp h2]
    have hxa : |x| ^ (2 * k + 2) = x ^ (2 * k) * x ^ 2 := by
      rw [pow_add, pow_mul, sq_abs, ← pow_mul]
    rw [mul_pow, hxa] at hmul
    rw [div_mul_eq_mul_div, le_div_iff₀ hc2]
    linarith
  have hsum : x ^ (2 * k) * (1 + x ^ 2) ≤ M * Real.exp (c * |x|) := by
    have : x ^ (2 * k) * (1 + x ^ 2) = x ^ (2 * k) + x ^ (2 * k) * x ^ 2 := by ring
    rw [this]
    have : M * Real.exp (c * |x|) =
        (((2 * k).factorial : ℝ) / c ^ (2 * k)) * Real.exp (c * |x|) +
        (((2 * k + 2).factorial : ℝ) / c ^ (2 * k + 2)) * Real.exp (c * |x|) := by
      dsimp only [M]
      ring
    linarith
  have hexp_neg : Real.exp (-c * |x|) = (Real.exp (c * |x|))⁻¹ := by
    rw [neg_mul, Real.exp_neg]
  rw [hexp_neg, inv_mul_eq_div, div_le_iff₀ (Real.exp_pos _), mul_comm (M * _), ← mul_assoc]
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : (0 : ℝ) < 1 + x ^ 2)]
  linarith

private theorem realZeros_stripJet_integrand_continuous (α s b : ℝ) (k : ℕ) :
    Continuous (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
  ((Real.continuous_exp.comp
      ((continuous_const.mul continuous_id).sub (continuous_const.mul continuous_abs))).mul
    (continuous_id.pow (2 * k))).mul
    (((continuous_const.add (continuous_id.pow 2)).rpow_const fun x ↦
        Or.inl (by change (1 : ℝ) + x ^ 2 ≠ 0; positivity)).inv₀ fun x ↦
      (Real.rpow_pos_of_pos (by change (0 : ℝ) < 1 + x ^ 2; positivity) _).ne')

private theorem realZeros_stripJet_integrable {α s b : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) {k : ℕ}
    (h : (-α < b ∧ b < α) ∨ ((b = -α ∨ b = α) ∧ 2 * (k : ℝ) + 1 < s)) :
    Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
      ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  rcases h with ⟨hb1, hb2⟩ | ⟨hb, hk⟩
  · have hδ : 0 < α - |b| := by
      have : |b| < α := abs_lt.mpr ⟨hb1, hb2⟩
      linarith
    refine (realZeros_integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * (α - |b|)) k).mono'
      (realZeros_stripJet_integrand_continuous α s b k).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg]
    have hbx : b * x ≤ |b| * |x| := by
      calc b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ Real.exp (-(2 * (α - |b|)) * |x|) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hinv_le : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
    calc Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹
        ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) * 1 :=
          mul_le_mul_of_nonneg_left hinv_le
            (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
      _ = Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) := mul_one _
      _ ≤ Real.exp (-(2 * (α - |b|)) * |x|) * x ^ (2 * k) :=
          mul_le_mul_of_nonneg_right hexp (Even.pow_nonneg (even_two_mul k) x)
  · refine (realZeros_integrable_pow_mul_rpow_inv hk).mono'
      (realZeros_stripJet_integrand_continuous α s b k).aestronglyMeasurable
      (ae_of_all _ fun x ↦ ?_)
    have hnonneg : 0 ≤ Real.exp (2 * b * x - 2 * α * |x|) * x ^ (2 * k) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ :=
      mul_nonneg (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul k) x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
    rw [Real.norm_of_nonneg hnonneg, mul_assoc]
    have hba : |b| = α := by
      rcases hb with rfl | rfl
      · rw [abs_neg, abs_of_nonneg hα]
      · exact abs_of_nonneg hα
    have hbx : b * x ≤ α * |x| := by
      calc b * x ≤ |b * x| := le_abs_self _
        _ = |b| * |x| := abs_mul b x
        _ = α * |x| := by rw [hba]
    have hexp : Real.exp (2 * b * x - 2 * α * |x|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (2 * b * x - 2 * α * |x|) * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
        ≤ 1 * (x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
          mul_le_mul_of_nonneg_right hexp
            (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
              (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
      _ = x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _

private noncomputable def realZeros_logEquiv : ℝ ≃ₜ ℝ≥0ˣ :=
  Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm

private theorem realZeros_logEquiv_symm_eq (y : ℝ≥0ˣ) :
    realZeros_logEquiv.symm y = Real.log (y.val : ℝ) := by
  obtain ⟨x, rfl⟩ := realZeros_logEquiv.surjective y
  rw [Homeomorph.symm_apply_apply]
  change x = Real.log (Real.exp x)
  exact (Real.log_exp x).symm

private theorem realZeros_logEquiv_preserving :
    let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
    MeasurePreserving realZeros_logEquiv volume positiveRealHaar := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  refine ⟨realZeros_logEquiv.continuous.measurable, ?_⟩
  unfold positiveRealHaar
  congr 1
  funext x
  apply Units.ext
  exact Subtype.ext (Real.coe_toNNReal _ (Real.exp_pos x).le).symm

private noncomputable def realZeros_splitEquiv
    {G : Type*} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G]
    (m : G →ₜ* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) :
    ↥(MonoidHom.ker m.toMonoidHom) × ℝ≥0ˣ ≃ₜ G where
  toFun p := (p.1 : G) * τ p.2
  invFun x := (⟨x / τ (m x), show m (x / τ (m x)) = 1 by rw [map_div, hτ _, div_self']⟩, m x)
  left_inv p := by
    have hk : m (p.1 : G) = 1 := p.1.property
    apply Prod.ext
    · apply Subtype.ext
      change (p.1 : G) * τ p.2 / τ (m ((p.1 : G) * τ p.2)) = p.1
      rw [map_mul, hk, one_mul, hτ, mul_div_cancel_right]
    · change m ((p.1 : G) * τ p.2) = p.2
      rw [map_mul, hk, one_mul, hτ]
  right_inv x := by
    change x / τ (m x) * τ (m x) = x
    simp [div_eq_mul_inv, mul_assoc]
  continuous_toFun := (continuous_subtype_val.comp continuous_fst).mul (τ.continuous.comp continuous_snd)
  continuous_invFun := by
    refine Continuous.prodMk ?_ m.continuous
    refine Continuous.subtype_mk ?_ _
    simp only [div_eq_mul_inv]
    exact continuous_id.mul (continuous_inv.comp (τ.continuous.comp m.continuous))

private theorem realZeros_splitEquiv_symm_snd
    {G : Type*} [TopologicalSpace G] [CommGroup G] [IsTopologicalGroup G]
    (m : G →ₜ* ℝ≥0ˣ) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) (x : G) :
    ((realZeros_splitEquiv m τ hτ).symm x).2 = m x :=
  rfl

/-- Pushforward of `canonicalModulatedHaar m hm` along `g ↦ Real.log (m g)` is Lebesgue measure on `ℝ`. -/
private theorem realZeros_log_preserving_of
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m) :
    MeasurePreserving (fun g : G ↦ Real.log ((m g).val : ℝ)) (canonicalModulatedHaar m hm) volume := by
  have : CompactSpace (↥(MonoidHom.ker m.toMonoidHom)) :=
    isCompact_iff_compactSpace.mp (IsModulation.isCompact_ker hm)
  let μ₁ : Measure (↥(MonoidHom.ker m.toMonoidHom)) := Measure.haarMeasure ⊤
  have : IsProbabilityMeasure μ₁ := ⟨Measure.haarMeasure_self⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let e := (realZeros_splitEquiv m τ hτ).toMeasurableEquiv
  have he : MeasurePreserving e (μ₁.prod positiveRealHaar) (canonicalModulatedHaar m hm) :=
    ⟨e.measurable, (canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₁ Measure.haarMeasure_self).symm⟩
  let d := realZeros_logEquiv.toMeasurableEquiv
  have hd : MeasurePreserving d volume positiveRealHaar := realZeros_logEquiv_preserving
  have h : MeasurePreserving (d.symm ∘ Prod.snd ∘ e.symm)
      (canonicalModulatedHaar m hm) volume :=
    ((hd.symm d).comp (measurePreserving_snd (μ := μ₁) (ν := positiveRealHaar))).comp
      (he.symm e)
  have hfun : (fun g : G ↦ Real.log ((m g).val : ℝ)) = (d.symm ∘ Prod.snd ∘ e.symm) := by
    ext g
    change Real.log ((m g).val : ℝ) = realZeros_logEquiv.symm ((realZeros_splitEquiv m τ hτ).symm g).2
    rw [realZeros_splitEquiv_symm_snd, realZeros_logEquiv_symm_eq]
  rwa [hfun]

/-- Pushforward of the canonical modulated Haar measure along `logNorm` is Lebesgue measure on `ℝ`,
using only public declarations from `Ch09` and `AppA`. -/
private theorem realZeros_log_preserving :
    MeasurePreserving (fun g : C𝔽 ↦ logNorm g) (canonicalModulatedHaar m𝔽 hm𝔽) volume := by
  let q : IdeleGroup (𝓞 F) F →ₜ* C𝔽 := ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  let τ : ℝ≥0ˣ →ₜ* C𝔽 := q.comp
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  exact realZeros_log_preserving_of m𝔽 hm𝔽 τ (canonicalIdeleNormSection_rightInverse F)

private theorem realZeros_stripJet_norm_sq (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s) (j : SpectralStripJetIndex χ a α s)
    (ν : Measure C𝔽) [ν.IsHaarMeasure] (hν : ν = canonicalModulatedHaar m𝔽 hm𝔽) :
    ‖(spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))‖ ^ 2 =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
  let u := (spectralStripJet_memLp χ hα hs j).toLp (stripJet(χ, j))
  let f : ℝ → ℝ := fun x ↦
    Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹
  have h1 : ‖u‖ ^ 2 = ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) := realZeros_lp_norm_sq u
  have h2 : ∫ g : C𝔽, ‖u g‖ ^ 2 ∂(L2μ'(-α, α, s)) =
      ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
        ∂(L2μ'(-α, α, s)) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (spectralStripJet_memLp χ hα hs j)] with g hg
    rw [hg, realZeros_zeroJet_norm_sq]
  have h3 : ∫ g : C𝔽, Real.exp (2 * j.val.2.1 * logNorm g) * (logNorm g) ^ (2 * j.val.2.2.2)
      ∂(L2μ'(-α, α, s)) = ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 := by
    rw [integral_withDensity_eq_integral_toReal_smul
      ((realZeros_symmDensity_inv_continuous hα s).measurable.ennreal_ofReal)
      (ae_of_all μ𝔽 fun _ ↦ ENNReal.ofReal_lt_top)]
    refine integral_congr_ae (ae_of_all μ𝔽 fun g ↦ ?_)
    dsimp only [f]
    rw [smul_eq_mul,
      ENNReal.toReal_ofReal (inv_nonneg.mpr (realZeros_symmDensity_pos hα s (logNorm g)).le),
      mul_comm, realZeros_symmDensity_eq hα, mul_inv, Real.exp_sub, div_eq_mul_inv]
    ring
  have hlogm : AEMeasurable (fun g : C𝔽 ↦ logNorm g) ν :=
    realZeros_continuous_logNorm.measurable.aemeasurable
  have hν_eq : ∫ g : C𝔽, f (logNorm g) ∂ν = ∫ x : ℝ, f x ∂volume := by
    subst hν
    rw [← (realZeros_log_preserving (F := F)).map_eq,
      integral_map hlogm (realZeros_stripJet_integrand_continuous α s j.val.2.1
        j.val.2.2.2).aestronglyMeasurable]
  have h4 : ∫ g : C𝔽, f (logNorm g) ∂μ𝔽 =
      (Measure.haarScalarFactor μ𝔽 ν : ℝ) * ∫ x : ℝ, f x ∂volume := by
    conv_lhs => rw [Measure.isMulLeftInvariant_eq_smul μ𝔽 ν]
    rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, hν_eq]
  exact h1.trans (h2.trans (h3.trans h4))

private theorem realZeros_stripJet_upperBound_of_cofinite_margin
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (E : Finset (PontryaginDual C₁))
    {a α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
    (K : ℕ) (δ : ℝ) (hδ : 0 < δ)
    (hmargin : ∀ j : SpectralStripJetIndex χ a α s,
      j.val.1 ∉ E → j.val.2.2.2 ≤ K → (s - 1) / 2 ≤ (j.val.2.2.2 : ℝ) → |j.val.2.1| ≤ α - δ) :
    ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s,
      j.val.1 ∉ E → j.val.2.2.2 ≤ K → ‖jetLp(χ, hα, hs, j)‖ ≤ C := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  let hs₀ : 0 ≤ s := hs₀(hs)
  let N : ℕ := Nat.ceil ((s - 1) / 2)
  let M_bdry : ℝ := ∑ m ∈ Finset.range N,
    ∫ x : ℝ, x ^ (2 * m) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume
  let M_int : ℝ := ∫ x : ℝ, Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) ∂volume
  have hfac_nonneg : 0 ≤ (Measure.haarScalarFactor μ𝔽 ν : ℝ) := NNReal.coe_nonneg _
  have hM_bdry_nonneg : 0 ≤ M_bdry :=
    Finset.sum_nonneg fun m _ ↦ integral_nonneg fun x ↦
      mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have hM_int_nonneg : 0 ≤ M_int :=
    integral_nonneg fun x ↦
      mul_nonneg (Real.exp_pos _).le (add_nonneg zero_le_one (Even.pow_nonneg (even_two_mul K) x))
  have hM_int_integrable : Integrable (fun x : ℝ ↦ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)))
      volume := by
    have h0 := realZeros_integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) 0
    have hK := realZeros_integrable_exp_neg_abs_mul_pow (by linarith : 0 < 2 * δ) K
    refine (h0.add hK).congr (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.add_apply, mul_zero, pow_zero, mul_one]
    ring
  let B : ℝ := 1 + (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int)
  refine ⟨Real.sqrt B, fun j hjE hjK ↦ ?_⟩
  have hcond : (-α < j.val.2.1 ∧ j.val.2.1 < α) ∨
      ((j.val.2.1 = -α ∨ j.val.2.1 = α) ∧ 2 * (j.val.2.2.2 : ℝ) + 1 < s) := by
    have hj := j.property
    unfold spectralStripMultiplicity at hj
    split_ifs at hj with h1 h2
    · exact Or.inl h1
    · refine Or.inr ⟨h2, ?_⟩
      have horder : (j.val.2.2.2 : ℝ) < (s - 1) / 2 :=
        ((lt_spectralBoundaryMultiplicity s _ _).mp hj).2
      linarith
    · omega
  have hf_int := realZeros_stripJet_integrable hα hs₀ hcond
  have hint_bound : ∫ x : ℝ,
      Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
        ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry + M_int := by
    by_cases hk : (j.val.2.2.2 : ℝ) < (s - 1) / 2
    · have hk' : 2 * (j.val.2.2.2 : ℝ) + 1 < s := by linarith
      have hba : |j.val.2.1| ≤ α :=
        abs_le.mpr (SpectralStripJetIndex.mem_strip_order_pos hα j).1
      have h1 : ∫ x : ℝ,
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
          ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume := by
        refine integral_mono hf_int (realZeros_integrable_pow_mul_rpow_inv hk') fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ α * |x| := by
          calc j.val.2.1 * x ≤ |j.val.2.1 * x| := le_abs_self _
            _ = |j.val.2.1| * |x| := abs_mul _ _
            _ ≤ α * |x| := mul_le_mul_of_nonneg_right hba (abs_nonneg x)
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by linarith)
        rw [mul_assoc]
        calc Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) *
              (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
            ≤ 1 * (x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹) :=
              mul_le_mul_of_nonneg_right hexp
                (mul_nonneg (Even.pow_nonneg (even_two_mul _) x)
                  (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le))
          _ = x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := one_mul _
      have hjN : j.val.2.2.2 ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_ceil.mpr hk)
      have h2 : ∫ x : ℝ, x ^ (2 * j.val.2.2.2) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_bdry :=
        Finset.single_le_sum
          (f := fun m ↦ ∫ x : ℝ, x ^ (2 * m) * ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume)
          (fun m _ ↦ integral_nonneg fun x ↦
            mul_nonneg (Even.pow_nonneg (even_two_mul m) x)
              (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))) hjN
      linarith
    · have hmarg : |j.val.2.1| ≤ α - δ := hmargin j hjE hjK (not_lt.mp hk)
      have h1 : ∫ x : ℝ,
          Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
            ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤ M_int := by
        refine integral_mono hf_int hM_int_integrable fun x ↦ ?_
        have hbx : j.val.2.1 * x ≤ (α - δ) * |x| := by
          calc j.val.2.1 * x ≤ |j.val.2.1 * x| := le_abs_self _
            _ = |j.val.2.1| * |x| := abs_mul _ _
            _ ≤ (α - δ) * |x| := mul_le_mul_of_nonneg_right hmarg (abs_nonneg x)
        have hexp : Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) ≤ Real.exp (-(2 * δ) * |x|) :=
          Real.exp_le_exp.mpr (by nlinarith)
        have hpow : x ^ (2 * j.val.2.2.2) ≤ 1 + x ^ (2 * K) := by
          have hxa : x ^ (2 * j.val.2.2.2) = |x| ^ (2 * j.val.2.2.2) := by
            rw [pow_mul, ← sq_abs, ← pow_mul]
          have hxaK : x ^ (2 * K) = |x| ^ (2 * K) := by
            rw [pow_mul, ← sq_abs, ← pow_mul]
          rw [hxa, hxaK]
          rcases le_total |x| 1 with hx1 | hx1
          · have : |x| ^ (2 * j.val.2.2.2) ≤ 1 := pow_le_one₀ (abs_nonneg x) hx1
            linarith [pow_nonneg (abs_nonneg x) (2 * K)]
          · have : |x| ^ (2 * j.val.2.2.2) ≤ |x| ^ (2 * K) :=
              pow_le_pow_right₀ hx1 (Nat.mul_le_mul_left 2 hjK)
            linarith
        have hinv_le : ((1 + x ^ 2) ^ (s / 2))⁻¹ ≤ 1 :=
          inv_le_one_of_one_le₀ (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith))
        calc Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
              ((1 + x ^ 2) ^ (s / 2))⁻¹
            ≤ Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) * 1 :=
              mul_le_mul_of_nonneg_left hinv_le
                (mul_nonneg (Real.exp_pos _).le (Even.pow_nonneg (even_two_mul _) x))
          _ = Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) := mul_one _
          _ ≤ Real.exp (-(2 * δ) * |x|) * (1 + x ^ (2 * K)) :=
              mul_le_mul hexp hpow (Even.pow_nonneg (even_two_mul _) x) (Real.exp_pos _).le
      linarith
  have hsq : ‖jetLp(χ, hα, hs, j)‖ ^ 2 ≤ B := by
    rw [realZeros_stripJet_norm_sq χ hα hs₀ j ν rfl]
    have hmul : (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
        ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * α * |x|) * x ^ (2 * j.val.2.2.2) *
          ((1 + x ^ 2) ^ (s / 2))⁻¹ ∂volume ≤
        (Measure.haarScalarFactor μ𝔽 ν : ℝ) * (M_bdry + M_int) :=
      mul_le_mul_of_nonneg_left hint_bound hfac_nonneg
    dsimp only [B]
    linarith
  calc ‖jetLp(χ, hα, hs, j)‖
      = Real.sqrt (‖jetLp(χ, hα, hs, j)‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt B := Real.sqrt_le_sqrt hsq

private theorem realZeros_stripJet_neg_symm (b : ℝ) :
    ∫ x : ℝ, Real.exp (2 * (-b) * x - 2 * |x|) * x ^ 2 * ((1 + x ^ 2) ^ (1 : ℝ))⁻¹ ∂volume =
      ∫ x : ℝ, Real.exp (2 * b * x - 2 * |x|) * x ^ 2 * ((1 + x ^ 2) ^ (1 : ℝ))⁻¹ ∂volume := by
  rw [← integral_neg_eq_self (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * |x|) * x ^ 2 *
    ((1 + x ^ 2) ^ (1 : ℝ))⁻¹) volume]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  dsimp only
  rw [abs_neg, neg_sq, show 2 * b * -x = 2 * (-b) * x by ring]

private theorem realZeros_stripJet_orderOne_log_lower {b : ℝ} (hb1 : b < 1) (hε : 1 - b < 1)
    (hint : Integrable (fun x : ℝ ↦ Real.exp (2 * b * x - 2 * |x|) * x ^ 2 *
      ((1 + x ^ 2) ^ (1 : ℝ))⁻¹) volume) :
    Real.exp (-2) * 2⁻¹ * Real.log (1 - b)⁻¹ ≤
      ∫ x : ℝ, Real.exp (2 * b * x - 2 * |x|) * x ^ 2 * ((1 + x ^ 2) ^ (1 : ℝ))⁻¹ ∂volume := by
  have hε0 : 0 < 1 - b := sub_pos.mpr hb1
  have hone : 1 ≤ (1 - b)⁻¹ := (one_le_inv₀ hε0).mpr hε.le
  have hg_int : Integrable ((Ioc 1 (1 - b)⁻¹).indicator fun x : ℝ ↦
      Real.exp (-2) * 2⁻¹ * x⁻¹) volume := by
    refine ((ContinuousOn.integrableOn_Icc ?_).mono_set
      Ioc_subset_Icc_self).integrable_indicator measurableSet_Ioc
    exact continuousOn_const.mul
      (continuousOn_inv₀.mono fun x hx ↦ (zero_lt_one.trans_le hx.1).ne')
  have hle : ∀ x : ℝ, (Ioc 1 (1 - b)⁻¹).indicator (fun x : ℝ ↦ Real.exp (-2) * 2⁻¹ * x⁻¹) x ≤
      Real.exp (2 * b * x - 2 * |x|) * x ^ 2 * ((1 + x ^ 2) ^ (1 : ℝ))⁻¹ := by
    intro x
    by_cases hx : x ∈ Ioc 1 (1 - b)⁻¹
    · rw [indicator_of_mem hx]
      have hx1 : 1 ≤ x := hx.1.le
      have hx0 : 0 < x := zero_lt_one.trans hx.1
      have hεx : (1 - b) * x ≤ 1 := by
        have h := mul_le_mul_of_nonneg_left hx.2 hε0.le
        rwa [mul_inv_cancel₀ hε0.ne'] at h
      have hexp : Real.exp (-2) ≤ Real.exp (2 * b * x - 2 * |x|) := by
        rw [abs_of_pos hx0]
        exact Real.exp_le_exp.mpr (by nlinarith)
      have hD : 1 + x ^ 2 ≤ 2 * x ^ 2 := by nlinarith
      have hfrac : 2⁻¹ * x⁻¹ ≤ x ^ 2 * ((1 + x ^ 2) ^ (1 : ℝ))⁻¹ := by
        rw [Real.rpow_one, ← mul_inv, ← div_eq_mul_inv, inv_eq_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        calc 1 * (1 + x ^ 2) ≤ 2 * x ^ 2 := by rw [one_mul]; exact hD
          _ ≤ 2 * (x ^ 2 * x) := by nlinarith [sq_nonneg x]
          _ = x ^ 2 * (2 * x) := by ring
      calc Real.exp (-2) * 2⁻¹ * x⁻¹ = Real.exp (-2) * (2⁻¹ * x⁻¹) := by ring
        _ ≤ Real.exp (2 * b * x - 2 * |x|) * (x ^ 2 * ((1 + x ^ 2) ^ (1 : ℝ))⁻¹) :=
            mul_le_mul hexp hfrac (by positivity) (Real.exp_pos _).le
        _ = _ := by ring
    · rw [indicator_of_notMem hx]
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (sq_nonneg x))
        (inv_nonneg.mpr (Real.rpow_pos_of_pos (by positivity) _).le)
  have h1 := integral_mono hg_int hint hle
  have h2 : ∫ x : ℝ, (Ioc 1 (1 - b)⁻¹).indicator (fun x : ℝ ↦
      Real.exp (-2) * 2⁻¹ * x⁻¹) x ∂volume = Real.exp (-2) * 2⁻¹ * Real.log (1 - b)⁻¹ := by
    rw [integral_indicator measurableSet_Ioc, ← intervalIntegral.integral_of_le hone,
      intervalIntegral.integral_const_mul, integral_inv_of_pos one_pos
        (zero_lt_one.trans_le hone), div_one]
  linarith

private theorem realZeros_stripJet_orderOne_margin_of_bound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (E : Finset (PontryaginDual C₁))
    (a C : ℝ)
    (hC : ∀ j : SpectralStripJetIndex χ a 1 2, j.val.1 ∉ E → j.val.2.2.2 = 1 →
      ‖jetLp(χ, zero_le_one, one_lt_two, j)‖ ≤ C) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ j : SpectralStripJetIndex χ a 1 2, j.val.1 ∉ E → j.val.2.2.2 = 1 →
      |j.val.2.1| ≤ 1 - δ := by
  let ν : Measure C𝔽 := canonicalModulatedHaar m𝔽 hm𝔽
  let : ν.IsHaarMeasure := (existsUnique_canonicalModulatedHaar m𝔽 hm𝔽).exists.choose_spec.1
  have hfac_pos : 0 < (Measure.haarScalarFactor μ𝔽 ν : ℝ) := by
    exact_mod_cast (Measure.haarScalarFactor_pos_of_isHaarMeasure μ𝔽 ν)
  let c₂ : ℝ := Real.exp (-2) * 2⁻¹
  have hc₂ : 0 < c₂ := mul_pos (Real.exp_pos _) (by norm_num)
  let L : ℝ := C ^ 2 / ((Measure.haarScalarFactor μ𝔽 ν : ℝ) * c₂)
  have hL : 0 ≤ L := div_nonneg (sq_nonneg C) (mul_pos hfac_pos hc₂).le
  refine ⟨Real.exp (-L), Real.exp_pos _, fun j hjE hj1 ↦ ?_⟩
  have hj := j.property
  unfold spectralStripMultiplicity at hj
  split_ifs at hj with hb he
  · have habs : |j.val.2.1| < 1 := abs_lt.mpr hb
    by_cases h1 : 1 ≤ 1 - |j.val.2.1|
    · have : Real.exp (-L) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      linarith
    · have hint' : Integrable (fun x : ℝ ↦
          Real.exp (2 * |j.val.2.1| * x - 2 * |x|) * x ^ 2 * ((1 + x ^ 2) ^ (1 : ℝ))⁻¹)
          volume := by
        simpa [hj1] using realZeros_stripJet_integrable zero_le_one zero_le_two (k := 1)
          (Or.inl ⟨by linarith [abs_nonneg j.val.2.1], habs⟩)
      have hlog := realZeros_stripJet_orderOne_log_lower habs (not_le.mp h1) hint'
      have hsym : ∫ x : ℝ, Real.exp (2 * |j.val.2.1| * x - 2 * |x|) * x ^ 2 *
            ((1 + x ^ 2) ^ (1 : ℝ))⁻¹ ∂volume =
          ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * 1 * |x|) * x ^ (2 * 1) *
            ((1 + x ^ 2) ^ ((2 : ℝ) / 2))⁻¹ ∂volume := by
        simp only [mul_one, show (2 : ℝ) / 2 = 1 by norm_num]
        rcases abs_cases j.val.2.1 with ⟨h, _⟩ | ⟨h, _⟩
        · rw [h]
        · rw [h]
          exact realZeros_stripJet_neg_symm _
      rw [hsym] at hlog
      have hsq : (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
          ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * 1 * |x|) * x ^ (2 * 1) *
            ((1 + x ^ 2) ^ ((2 : ℝ) / 2))⁻¹ ∂volume ≤ C ^ 2 := by
        have hsq0 := realZeros_stripJet_norm_sq χ zero_le_one zero_le_two j ν rfl
        have hrhs : ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * 1 * |x|) * x ^ (2 * j.val.2.2.2) *
              ((1 + x ^ 2) ^ ((2 : ℝ) / 2))⁻¹ ∂volume =
            ∫ x : ℝ, Real.exp (2 * j.val.2.1 * x - 2 * 1 * |x|) * x ^ (2 * 1) *
              ((1 + x ^ 2) ^ ((2 : ℝ) / 2))⁻¹ ∂volume := by rw [hj1]
        rw [← hrhs, ← hsq0]
        exact pow_le_pow_left₀ (norm_nonneg _) (hC j hjE hj1) 2
      have h3 : (Measure.haarScalarFactor μ𝔽 ν : ℝ) *
          (c₂ * Real.log (1 - |j.val.2.1|)⁻¹) ≤ C ^ 2 :=
        (mul_le_mul_of_nonneg_left hlog hfac_pos.le).trans hsq
      have h4 : Real.log (1 - |j.val.2.1|)⁻¹ ≤ L := by
        rw [le_div_iff₀ (mul_pos hfac_pos hc₂)]
        linarith
      rw [Real.log_inv] at h4
      have h5 : Real.exp (-L) ≤ 1 - |j.val.2.1| := by
        calc Real.exp (-L) ≤ Real.exp (Real.log (1 - |j.val.2.1|)) :=
              Real.exp_le_exp.mpr (by linarith)
          _ = 1 - |j.val.2.1| := Real.exp_log (sub_pos.mpr habs)
      linarith
  · have hlt := ((lt_spectralBoundaryMultiplicity _ _ _).mp hj).2
    rw [hj1] at hlt
    norm_num at hlt
  · omega

/-! ### Public characterizations of `#7485` over an arbitrary number field `F` -/

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Finiteness of the multiple real zeros for every choice of basepoints is equivalent to a symmetric
finite cover `(E, S)` of all multiple zeros in `ℂ`: `E` is closed under inversion, `S` is closed
under `σ ↦ 1 - σ` and contains `1 / 2`, and every multiple zero of every unitary Hecke character
`ψ` at any height belongs to an exceptional component in `E` or has real part in `S`.
Deviation: The paper does not state this characterization; it upgrades the right-half finite
cover of `spectralStripJet_multiple_real_zeros_finite_iff_finite_cover` (`Sec2`, #7504) using
the functional equation and critical-strip confinement. -/
theorem spectralStripJet_multiple_real_zeros_finite_iff_symmetric_finite_cover :
    (∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁,
        1 < mult(χ ω, (σ : ℂ))}.Finite) ↔
    ∃ (E : Finset (PontryaginDual C₁)) (S : Finset ℝ),
      (∀ ω ∈ E, ω⁻¹ ∈ E) ∧ (∀ σ ∈ S, 1 - σ ∈ S) ∧ (1 / 2 : ℝ) ∈ S ∧
      ∀ (ψ : PontryaginDual C𝔽) (σ t : ℝ),
        1 < mult(ψ, shift(σ, t)) → ψ.comp restriction ∈ E ∨ σ ∈ S := by
  classical
  constructor
  · intro hreal
    obtain ⟨E₀, S₀, hcover⟩ :=
      (spectralStripJet_multiple_real_zeros_finite_iff_finite_cover (F := F)).mp hreal
    let E : Finset (PontryaginDual C₁) := E₀ ∪ E₀.image Inv.inv
    let S : Finset ℝ := insert (1 / 2 : ℝ) (S₀ ∪ S₀.image (fun σ : ℝ ↦ 1 - σ))
    refine ⟨E, S, ?_, ?_, Finset.mem_insert_self _ _, ?_⟩
    · intro ω hω
      rcases Finset.mem_union.mp hω with hω | hω
      · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hω)
      · obtain ⟨ω₀, hω₀, rfl⟩ := Finset.mem_image.mp hω
        exact Finset.mem_union_left (E₀.image Inv.inv) (by simpa using hω₀)
    · intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ
      · convert Finset.mem_insert_self (1 / 2 : ℝ) _ using 1
        norm_num
      · rcases Finset.mem_union.mp hσ with hσ | hσ
        · exact Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hσ))
        · obtain ⟨σ₀, hσ₀, rfl⟩ := Finset.mem_image.mp hσ
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (by simpa using hσ₀))
    · intro ψ σ t hm
      have hσ_Icc : σ ∈ Icc (0 : ℝ) 1 := by
        by_contra hnot
        rw [realZeros_mult_eq_zero_of_not_mem_Icc ψ (shift(σ, t)) (by simpa using hnot)] at hm
        omega
      rcases lt_trichotomy σ (1 / 2) with hlt | heq | hgt
      · have hm' : 1 < mult(ψ⁻¹, shift(1 - σ, (-t : ℝ))) := by
          rwa [← realZeros_mult_reflect ψ σ t]
        have hpos : 0 < mult(ψ⁻¹, shift(1 - σ, (-t : ℝ))) := by omega
        have hr : 1 - σ ∈ Ioo (1 / 2 : ℝ) 1 := ⟨by linarith, realZeros_re_lt_one ψ⁻¹ (by linarith) hpos⟩
        rcases hcover ψ⁻¹ (1 - σ) (-t) hr hm' with hE | hS
        · left
          have hinv : (ψ.comp restriction)⁻¹ = ψ⁻¹.comp restriction := by
            ext g : 1
            rfl
          rw [← inv_inv (ψ.comp restriction), hinv]
          exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hE)
        · right
          exact Finset.mem_insert_of_mem (Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨1 - σ, hS, by ring⟩))
      · exact Or.inr (heq ▸ Finset.mem_insert_self _ _)
      · have hlt1 : σ < 1 := realZeros_re_lt_one ψ (t := t) hgt (by omega)
        rcases hcover ψ σ t ⟨hgt, hlt1⟩ hm with hE | hS
        · exact Or.inl (Finset.mem_union_left _ hE)
        · exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_union_left _ hS))
  · rintro ⟨E, S, -, -, -, hcover⟩
    exact (spectralStripJet_multiple_real_zeros_finite_iff_finite_cover (F := F)).mpr
      ⟨E, S, fun ψ σ t _ hm ↦ hcover ψ σ t hm⟩

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Finiteness of the multiple real zeros for every choice of basepoints holds if and only if there is
no sequence of unitary Hecke characters whose norm-one restrictions are pairwise distinct and
which admit real multiple zeros along a strictly monotone (or strictly antitone) sequence in
`(1 / 2, 1)`.
Deviation: The paper does not state this infinite-obstruction equivalence. -/
theorem spectralStripJet_multiple_real_zeros_finite_iff_no_monotone_matching :
    (∀ (χ : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁,
        1 < mult(χ ω, (σ : ℂ))}.Finite) ↔
    ¬ ∃ (ψ : ℕ → PontryaginDual C𝔽) (σ : ℕ → ℝ),
      Injective (fun n ↦ (ψ n).comp restriction) ∧
      (StrictMono σ ∨ StrictAnti σ) ∧
      (∀ n, σ n ∈ Ioo (1 / 2 : ℝ) 1) ∧
      (∀ n, 1 < mult(ψ n, (σ n : ℂ))) := by
  classical
  constructor
  · intro hreal ⟨ψ, σ, hcomp, hmono, hIoo, hm⟩
    obtain ⟨E, S, hcover⟩ :=
      (spectralStripJet_multiple_real_zeros_finite_iff_finite_cover (F := F)).mp hreal
    have hσ_inj : Injective σ := by
      rcases hmono with h | h
      · exact h.injective
      · exact h.injective
    have hfinE : {n : ℕ | (ψ n).comp restriction ∈ E}.Finite :=
      E.finite_toSet.preimage hcomp.injOn
    have hfinS : {n : ℕ | σ n ∈ S}.Finite :=
      S.finite_toSet.preimage hσ_inj.injOn
    have huniv : (univ : Set ℕ).Finite := (hfinE.union hfinS).subset fun n _ ↦ by
      simpa using hcover (ψ n) (σ n) 0 (hIoo n) (by simpa using hm n)
    exact Set.infinite_univ huniv
  · intro hno
    rw [spectralStripJet_multiple_real_zeros_finite_iff_finite_cover]
    by_contra! hcover
    let component (p : PontryaginDual C𝔽 × ℝ) := p.1.comp restriction
    let P (p : PontryaginDual C𝔽 × ℝ) :=
      p.2 ∈ Ioo (1 / 2 : ℝ) 1 ∧ 1 < mult(p.1, (p.2 : ℂ))
    let r (p q : PontryaginDual C𝔽 × ℝ) := component p ≠ component q ∧ p.2 ≠ q.2
    have : Std.Symm r := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.symm⟩⟩
    obtain ⟨p, hp, hpair⟩ := exists_seq_of_forall_finset_exists' P r (fun K _ ↦ by
      obtain ⟨ψ, σ, t, hσ, hm, hψ, hs⟩ := hcover (K.image component) (K.image Prod.snd)
      obtain ⟨θ, hθ, hmove⟩ := realZeros_recenter ψ t
      have hmθ : 1 < mult(θ, (σ : ℂ)) := by rwa [hmove]
      refine ⟨(θ, σ), ⟨hσ, hmθ⟩, fun q hq ↦ ⟨?_, ?_⟩⟩
      · exact fun he ↦ hψ (Finset.mem_image.mpr ⟨q, hq, he.trans hθ⟩)
      · exact fun he ↦ hs (Finset.mem_image.mpr ⟨q, hq, he⟩))
    have hcomp : Injective (fun n ↦ component (p n)) :=
      injective_iff_pairwise_ne.mpr fun _ _ h ↦ (hpair h).1
    have hparts : Injective (fun n ↦ (p n).2) :=
      injective_iff_pairwise_ne.mpr fun _ _ h ↦ (hpair h).2
    let R : Type _ := Set.range (fun n ↦ (p n).2)
    have : Infinite R := (Set.infinite_range_of_injective hparts).to_subtype
    obtain ⟨f, hf⟩ := Infinite.exists_strictMono_or_strictAnti R
    choose idx hidx using fun n : ℕ ↦ (f n).property
    have hidx_inj : Injective idx := fun m n hmn ↦ by
      have heq : f m = f n := Subtype.ext ((hidx m).symm.trans (by rw [hmn, hidx n]))
      rcases hf with hsm | hsa
      · exact hsm.injective heq
      · exact hsa.injective heq
    refine hno ⟨fun n ↦ (p (idx n)).1, fun n ↦ (f n : ℝ), hcomp.comp hidx_inj, ?_, ?_, ?_⟩
    · rcases hf with hsm | hsa
      · exact Or.inl fun m n hmn ↦ hsm hmn
      · exact Or.inr fun m n hmn ↦ hsa hmn
    · intro n
      simpa only [hidx n] using (hp (idx n)).1
    · intro n
      simpa only [hidx n] using (hp (idx n)).2

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
For any fixed choice of basepoints `χ`, finiteness of the multiple real zeros for every choice
of basepoints holds if and only if there is a finite exceptional set `E` of norm-one characters
such that on every strip of half-width one with `s = 2`, the order-one strip jets outside `E`
have bounded norms.
Deviation: The paper does not state this. Unlike `Sec2_Isolated`, this characterizes `#7485` alone
without assuming `#7220` or `#7453`. -/
theorem spectralStripJet_multiple_real_zeros_finite_iff_cofinite_orderOne_upperBound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ) :
    (∀ (χ' : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ' →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁,
        1 < mult(χ' ω, (σ : ℂ))}.Finite) ↔
    ∃ E : Finset (PontryaginDual C₁), ∀ a : ℝ, ∃ C : ℝ,
      ∀ j : SpectralStripJetIndex χ a 1 2, j.val.1 ∉ E → j.val.2.2.2 = 1 →
        ‖jetLp(χ, zero_le_one, one_lt_two, j)‖ ≤ C := by
  classical
  constructor
  · intro hreal
    obtain ⟨E, S, -, -, -, hcover⟩ :=
      (spectralStripJet_multiple_real_zeros_finite_iff_symmetric_finite_cover (F := F)).mp hreal
    refine ⟨E, fun a ↦ ?_⟩
    let T := S.filter (fun σ : ℝ ↦ |σ - a| < 1)
    let d (σ : ℝ) : ℝ := 1 - |σ - a|
    obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image (insert (1 : ℝ) (T.image d : Set ℝ)) id
      ((T.image d).finite_toSet.insert 1) (Set.insert_nonempty _ _)
    have hδ : 0 < δ := by
      rcases hmem with rfl | h
      · exact one_pos
      · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h
        exact sub_pos.mpr (Finset.mem_filter.mp hσ).2
    obtain ⟨C, hC⟩ := realZeros_stripJet_upperBound_of_cofinite_margin χ E (a := a) zero_le_one
      one_lt_two 1 δ hδ (fun j hjE _ hlow ↦ by
        have hpos : 0 < j.val.2.2.2 := Nat.pos_of_ne_zero fun h0 ↦ by
          rw [h0, Nat.cast_zero] at hlow
          norm_num at hlow
        have hj := j.property
        unfold spectralStripMultiplicity at hj
        split_ifs at hj with hb he
        · have hm : 1 < mult(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1)) := by omega
          have hS : a + j.val.2.1 ∈ S := by
            rcases hcover (χ j.val.1) (a + j.val.2.1) j.val.2.2.1 hm with hE | hS
            · rw [_hχ j.val.1] at hE
              exact (hjE hE).elim
            · exact hS
          have hT : a + j.val.2.1 ∈ T :=
            Finset.mem_filter.mpr ⟨hS, by simpa using abs_lt.mpr hb⟩
          have hdist : δ ≤ d (a + j.val.2.1) := hmin _ (Or.inr (Finset.mem_coe.mpr
            (Finset.mem_image_of_mem d hT)))
          dsimp [d] at hdist
          simp only [add_sub_cancel_left] at hdist
          linarith
        · have hlt := ((lt_spectralBoundaryMultiplicity _ _ _).mp hj).2
          linarith
        · omega)
    exact ⟨C, fun j hjE hj1 ↦ hC j hjE hj1.le⟩
  · rintro ⟨E, hbound⟩
    have hmargin : ∀ a : ℝ, ∃ δ : ℝ, 0 < δ ∧
        ∀ (ω : PontryaginDual C₁) (σ t : ℝ), ω ∉ E → |σ - a| < 1 →
          1 < mult(χ ω, shift(σ, t)) → |σ - a| ≤ 1 - δ := by
      intro a
      obtain ⟨C, hC⟩ := hbound a
      obtain ⟨δ, hδ, hj⟩ := realZeros_stripJet_orderOne_margin_of_bound χ E a C hC
      refine ⟨δ, hδ, fun ω σ t hω hlt hm ↦ ?_⟩
      let j : SpectralStripJetIndex χ a 1 2 := ⟨(ω, σ - a, t, 1), by
        change 1 < spectralStripMultiplicity 1 2 (σ - a) (mult(χ ω, shift(a + (σ - a), t)))
        rw [spectralStripMultiplicity_interior (abs_lt.mp hlt), show a + (σ - a) = σ by ring]
        exact hm⟩
      exact hj j hω rfl
    choose δ hδ hsep using hmargin
    let r (x : ℝ) := min 1 (min (δ (x - 1)) (δ (x + 1)))
    have hr (x : ℝ) : 0 < r x := lt_min one_pos (lt_min (hδ _) (hδ _))
    obtain ⟨T, _, hcover⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).elim_nhds_subcover
      (fun x ↦ Ioo (x - r x) (x + r x))
      (fun x _ ↦ Ioo_mem_nhds (by linarith [hr x]) (by linarith [hr x]))
    refine (spectralStripJet_multiple_real_zeros_finite_iff_finite_cover (F := F)).mpr
      ⟨E, T, fun ψ σ t hσ hm ↦ ?_⟩
    by_cases hω : ψ.comp restriction ∈ E
    · exact Or.inl hω
    · right
      obtain ⟨d, hd, -⟩ :=
        spectralZeroMultiplicity_existsUnique_shift_of_restriction_eq ψ
          (χ (ψ.comp restriction)) (_hχ (ψ.comp restriction)).symm
      have hm' : 1 < mult(χ (ψ.comp restriction), shift(σ, t + d)) := by
        rw [Complex.ofReal_add, ← (hd σ t).2]
        exact hm
      have hIcc : σ ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hσ.1], hσ.2.le⟩
      obtain ⟨x, hxT, hxl, hxr⟩ := mem_iUnion₂.mp (hcover hIcc)
      have hr1 : r x ≤ 1 := min_le_left _ _
      have hrL : r x ≤ δ (x - 1) := (min_le_right _ _).trans (min_le_left _ _)
      have hrR : r x ≤ δ (x + 1) := (min_le_right _ _).trans (min_le_right _ _)
      have heq : σ = x := by
        rcases lt_trichotomy σ x with hlt | heq | hgt
        · have hs1 := hsep (x - 1) (ψ.comp restriction) σ (t + d) hω
            (abs_lt.mpr ⟨by linarith, by linarith⟩) hm'
          linarith [le_abs_self (σ - (x - 1))]
        · exact heq
        · have hs1 := hsep (x + 1) (ψ.comp restriction) σ (t + d) hω
            (abs_lt.mpr ⟨by linarith, by linarith⟩) hm'
          linarith [neg_le_abs (σ - (x + 1))]
      rwa [heq]

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
For any fixed choice of basepoints `χ`, finiteness of the multiple real zeros for every choice
of basepoints holds if and only if there is a finite exceptional set `E` of norm-one characters
such that on every strip `(a, α, s)` (`α ≥ 0, s > 1`) and for every fixed order cap `K`, the strip
jets outside `E` of order at most `K` have bounded norms.
Deviation: The paper does not state this. -/
theorem spectralStripJet_multiple_real_zeros_finite_iff_cofinite_boundedOrder_upperBound
    (χ : PontryaginDual C₁ → PontryaginDual C𝔽) (_hχ : IsSpectralBasepointChoice χ) :
    (∀ (χ' : PontryaginDual C₁ → PontryaginDual C𝔽), IsSpectralBasepointChoice χ' →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁,
        1 < mult(χ' ω, (σ : ℂ))}.Finite) ↔
    ∃ E : Finset (PontryaginDual C₁), ∀ (K : ℕ) (a α s : ℝ) (hα : 0 ≤ α) (hs : 1 < s),
      ∃ C : ℝ, ∀ j : SpectralStripJetIndex χ a α s, j.val.1 ∉ E → j.val.2.2.2 ≤ K →
        ‖jetLp(χ, hα, hs, j)‖ ≤ C := by
  classical
  constructor
  · intro hreal
    obtain ⟨E, S, -, -, -, hcover⟩ :=
      (spectralStripJet_multiple_real_zeros_finite_iff_symmetric_finite_cover (F := F)).mp hreal
    refine ⟨E, fun K a α s hα hs ↦ ?_⟩
    let T := S.filter (fun σ : ℝ ↦ |σ - a| < α)
    let d (σ : ℝ) : ℝ := α - |σ - a|
    obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image (insert (1 : ℝ) (T.image d : Set ℝ)) id
      ((T.image d).finite_toSet.insert 1) (Set.insert_nonempty _ _)
    have hδ : 0 < δ := by
      rcases hmem with rfl | h
      · exact one_pos
      · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h
        exact sub_pos.mpr (Finset.mem_filter.mp hσ).2
    exact realZeros_stripJet_upperBound_of_cofinite_margin χ E hα hs K δ hδ
      (fun j hjE _ hlow ↦ by
        have hpos : 0 < j.val.2.2.2 := by
          have : (0 : ℝ) < j.val.2.2.2 := by linarith
          exact_mod_cast this
        have hj := j.property
        unfold spectralStripMultiplicity at hj
        split_ifs at hj with hb he
        · have hm : 1 < mult(χ j.val.1, shift(a + j.val.2.1, j.val.2.2.1)) := by omega
          have hS : a + j.val.2.1 ∈ S := by
            rcases hcover (χ j.val.1) (a + j.val.2.1) j.val.2.2.1 hm with hE | hS
            · rw [_hχ j.val.1] at hE
              exact (hjE hE).elim
            · exact hS
          have hT : a + j.val.2.1 ∈ T :=
            Finset.mem_filter.mpr ⟨hS, by simpa using abs_lt.mpr hb⟩
          have hdist : δ ≤ d (a + j.val.2.1) := hmin _ (Or.inr (Finset.mem_coe.mpr
            (Finset.mem_image_of_mem d hT)))
          dsimp [d] at hdist
          simp only [add_sub_cancel_left] at hdist
          linarith
        · exact ((not_lt.mpr hlow) ((lt_spectralBoundaryMultiplicity _ _ _).mp hj).2).elim
        · omega)
  · rintro ⟨E, hbound⟩
    rw [spectralStripJet_multiple_real_zeros_finite_iff_cofinite_orderOne_upperBound χ _hχ]
    refine ⟨E, fun a ↦ ?_⟩
    obtain ⟨C, hC⟩ := hbound 1 a 1 2 zero_le_one one_lt_two
    exact ⟨C, fun j hjE hj1 ↦ hC j hjE hj1.le⟩

end GeneralField

section RationalField

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "C₁ℚ" => (ideleClassNorm ℚ).ker
local notation "restrictionℚ" =>
  (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ : C₁ℚ →ₜ* Cℚ)
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "multℚ(" ψ ", " z ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL (F := ℚ) ψ) z).untop₀.toNat

/-- Two primitive Dirichlet characters with the same `LSeries` on `1 < Re s` have the same
conductor and are equal. -/
private theorem rat_primitive_dirichlet_eq_of_LSeries_eq
    {N₁ N₂ : ℕ} [NeZero N₁] [NeZero N₂]
    {χ₁ : DirichletCharacter ℂ N₁} {χ₂ : DirichletCharacter ℂ N₂}
    (h₁ : χ₁.IsPrimitive) (h₂ : χ₂.IsPrimitive)
    (hL : ∀ s : ℂ, 1 < s.re → LSeries (χ₁ ·) s = LSeries (χ₂ ·) s) :
    N₁ = N₂ ∧ HEq χ₁ χ₂ := by
  have hab₁ : LSeries.abscissaOfAbsConv (fun n : ℕ ↦ (χ₁ n : ℂ)) < ⊤ := by
    rw [DirichletCharacter.abscissaOfAbsConv_eq_one (NeZero.ne N₁) χ₁]
    exact EReal.coe_lt_top 1
  have hab₂ : LSeries.abscissaOfAbsConv (fun n : ℕ ↦ (χ₂ n : ℂ)) < ⊤ := by
    rw [DirichletCharacter.abscissaOfAbsConv_eq_one (NeZero.ne N₂) χ₂]
    exact EReal.coe_lt_top 1
  have hcoeff : ∀ n : ℕ, n ≠ 0 → (χ₁ n : ℂ) = χ₂ n := fun n hn ↦
    LSeries.eq_of_LSeries_eventually_eq hab₁ hab₂
      (eventually_atTop.mpr ⟨2, fun x hx ↦ hL (x : ℂ) (by simpa using (by linarith : (1 : ℝ) < x))⟩)
      hn
  let M : ℕ := N₁ * N₂
  have : NeZero M := ⟨mul_ne_zero (NeZero.ne N₁) (NeZero.ne N₂)⟩
  have h1M : N₁ ∣ M := dvd_mul_right N₁ N₂
  have h2M : N₂ ∣ M := dvd_mul_left N₂ N₁
  have hcl : DirichletCharacter.changeLevel h1M χ₁ = DirichletCharacter.changeLevel h2M χ₂ := by
    apply MulChar.ext
    intro u
    let k : ℕ := u.val.val + M
    have hk_ne : k ≠ 0 :=
      Nat.ne_of_gt (Nat.add_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne M)))
    have hk_cast : (k : ZMod M) = (u : ZMod M) := by
      simp [k]
    have hL1 : DirichletCharacter.changeLevel h1M χ₁ (u : ZMod M) = χ₁ k := by
      rw [DirichletCharacter.changeLevel_eq_cast_of_dvd χ₁ h1M u, ← hk_cast, ZMod.cast_natCast h1M k]
    have hL2 : DirichletCharacter.changeLevel h2M χ₂ (u : ZMod M) = χ₂ k := by
      rw [DirichletCharacter.changeLevel_eq_cast_of_dvd χ₂ h2M u, ← hk_cast, ZMod.cast_natCast h2M k]
    rw [hL1, hL2]
    exact hcoeff k hk_ne
  have hN : N₁ = N₂ := by
    have hc := congrArg DirichletCharacter.conductor hcl
    rw [DirichletCharacter.conductor_changeLevel χ₁ h1M,
      DirichletCharacter.conductor_changeLevel χ₂ h2M, h₁, h₂] at hc
    exact hc
  refine ⟨hN, ?_⟩
  subst hN
  refine heq_of_eq (MulChar.ext fun u ↦ ?_)
  let k : ℕ := u.val.val + N₁
  have hk_ne : k ≠ 0 :=
    Nat.ne_of_gt (Nat.add_pos_right _ (Nat.pos_of_ne_zero (NeZero.ne N₁)))
  have hk_cast : (k : ZMod N₁) = (u : ZMod N₁) := by
    simp [k]
  simpa [hk_cast] using hcoeff k hk_ne

/-- If `finiteHeckeL ψ` agrees with `LSeries (χ ·)` on `Re s > 1`, then at any `z` with
`0 < z.re` and `z ≠ 1`, the completed Hecke multiplicity equals `(analyticOrderAt (LFunction χ) z).toNat`
and the analytic order is finite. -/
private theorem rat_mult_eq_analyticOrderAt (ψ : PontryaginDual Cℚ) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hL : ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) :
    analyticOrderAt (DirichletCharacter.LFunction χ) z ≠ ⊤ ∧
      multℚ(ψ, z) = (analyticOrderAt (DirichletCharacter.LFunction χ) z).toNat := by
  have hspec := continuedCompletedHeckeL_spec (F := ℚ) ψ
  have hm := meromorphic_dirichletLFunction χ
  have hcmp (w : ℂ) (hw0 : 0 < w.re) := meromorphicOrderAt_finiteHeckeL_continuation ψ hm
    (fun s ↦ by rw [DirichletCharacter.LFunction_eq_LSeries χ s.2, hL s.1 s.2]) hw0
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {1}ᶜ := fun w hw ↦
    (DirichletCharacter.differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt
  have h2 : meromorphicOrderAt (continuedCompletedHeckeL (F := ℚ) ψ) 2 ≠ ⊤ := by
    have hA2 : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 2 :=
      hd.analyticAt (isOpen_compl_singleton.mem_nhds (by norm_num))
    have hne : DirichletCharacter.LFunction χ 2 ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inr (by norm_num)) (by norm_num)
    rw [← hcmp 2 (by norm_num), hA2.meromorphicOrderAt_eq, hA2.analyticOrderAt_eq_zero.mpr hne]
    exact ENat.map_natCast _ 0 ▸ WithTop.coe_ne_top
  have hfin_mero : meromorphicOrderAt (continuedCompletedHeckeL (F := ℚ) ψ) z ≠ ⊤ :=
    hspec.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ _) (mem_univ _) h2
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z :=
    hd.analyticAt (isOpen_compl_singleton.mem_nhds hz1)
  have hfin_ana : analyticOrderAt (DirichletCharacter.LFunction χ) z ≠ ⊤ := by
    intro htop
    apply hfin_mero
    rw [← hcmp z hz0, hA.meromorphicOrderAt_eq, htop]
    rfl
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin_ana
  refine ⟨hfin_ana, ?_⟩
  rw [← hcmp z hz0, hA.meromorphicOrderAt_eq, ← hk]
  simp

private theorem rat_one_lt_mult_iff_one_lt_analyticOrderAt (ψ : PontryaginDual Cℚ) {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N}
    (hL : ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z ≠ 1) :
    1 < multℚ(ψ, z) ↔ (1 : ℕ∞) < analyticOrderAt (DirichletCharacter.LFunction χ) z := by
  obtain ⟨hfin, heq⟩ := rat_mult_eq_analyticOrderAt ψ hL hz0 hz1
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  rw [heq, ← hk]
  norm_cast

/-- Any two unitary characters of `Cℚ` that are trivial on a section `τ` and have the same
norm-one restriction are equal. -/
private theorem rat_eq_of_trivial_on_section_and_restriction_eq
    (τ : ℝ≥0ˣ →ₜ* Cℚ) (hτ : RightInverse τ (ideleClassNorm ℚ))
    {ψ₁ ψ₂ : PontryaginDual Cℚ}
    (hψ₁ : ∀ t, ψ₁ (τ t) = 1) (hψ₂ : ∀ t, ψ₂ (τ t) = 1)
    (hres : ψ₁.comp restrictionℚ = ψ₂.comp restrictionℚ) : ψ₁ = ψ₂ := by
  ext g : 1
  let t := ideleClassNorm ℚ g
  let g₁ : C₁ℚ := ⟨g / τ t, by
    change ideleClassNorm ℚ (g / τ t) = 1
    rw [map_div, hτ t, div_self']⟩
  have hg : g = (g₁ : Cℚ) * τ t := by
    change g = g / τ t * τ t
    rw [div_mul_cancel]
  have h1 : ψ₁ g₁ = ψ₂ g₁ := DFunLike.congr_fun hres g₁
  rw [hg, map_mul, map_mul, hψ₁ t, hψ₂ t, mul_one, mul_one]
  exact h1

open NumberFieldKB.Chebotarev.RatIdele IsDedekindDomain.HeightOneSpectrum in
private theorem rat_norm_sub_one_le_of_redP_eq_one {p : ℕ} {hp : p.Prime} {e : ℕ} (z : Kp p hp)
    (hz : Valued.v z ≤ 1) (h : redP p hp e z = 1) :
    ‖z - 1‖ ≤ (p : ℝ) ^ (-(e : ℤ)) := by
  have := Fact.mk hp
  let Φ := PadicInt.adicCompletionIntegersEquiv (𝓞 ℚ) (⟨p, hp⟩ : Nat.Primes)
  rw [redP_of_le hz] at h
  have h0 : PadicInt.toZModPow e (Φ.symm ⟨z, hz⟩ - 1) = 0 := by
    rw [map_sub, map_one]
    change PadicInt.toZModPow e (Φ.symm ⟨z, hz⟩) - 1 = 0
    rw [show PadicInt.toZModPow e (Φ.symm ⟨z, hz⟩) = redO p hp e ⟨z, hz⟩ from rfl, h, sub_self]
  have hk : Φ.symm ⟨z, hz⟩ - 1 ∈ Ideal.span {(p : ℤ_[p]) ^ e} := by
    rw [← PadicInt.ker_toZModPow]
    exact RingHom.mem_ker.mpr h0
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp hk
  let w : Op p hp := Φ b
  have h2 : Φ.symm (⟨z, hz⟩ - 1) = b * (p : ℤ_[p]) ^ e := by
    rw [map_sub, map_one]
    exact hb.symm
  have hO : (⟨z, hz⟩ : Op p hp) - 1 = w * (p : Op p hp) ^ e := by
    have h1 : (⟨z, hz⟩ : Op p hp) - 1 = Φ (Φ.symm (⟨z, hz⟩ - 1)) := (Φ.apply_symm_apply _).symm
    rw [h1, h2, map_mul, map_pow, map_natCast]
    rfl
  have hK : z - 1 = (w : Kp p hp) * (p : Kp p hp) ^ e := by
    simpa using congrArg Subtype.val hO
  have hv : Valued.v (z - 1) ≤ WithZero.exp (-(e : ℤ)) := by
    rw [hK, map_mul, map_pow, valued_placeOf]
    calc Valued.v (w : Kp p hp) * WithZero.exp (-1) ^ e
        ≤ 1 * WithZero.exp (-1) ^ e := by gcongr; exact w.2
      _ = WithZero.exp (-(e : ℤ)) := by rw [one_mul, ← WithZero.exp_nsmul]; simp
  have hq : (Ideal.absNorm (placeOf p hp).asIdeal : ℝ≥0) = p := by
    rw [absNorm_asIdeal, pr_placeOf]
  have hq1 : (1 : ℝ≥0) < (Ideal.absNorm (placeOf p hp).asIdeal : ℝ≥0) := by
    rw [hq]
    exact_mod_cast hp.one_lt
  have hmono := (WithZeroMulInt.toNNReal_strictMono hq1).monotone hv
  rw [WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp] at hmono
  have hqN : Ideal.absNorm (placeOf p hp).asIdeal = p := by rw [absNorm_asIdeal, pr_placeOf]
  rw [FinitePlace.norm_def]
  calc ((WithZeroMulInt.toNNReal _ (Valued.v (z - 1)) : ℝ≥0) : ℝ)
      ≤ (((Ideal.absNorm (placeOf p hp).asIdeal : ℝ≥0) ^ (-(e : ℤ)) : ℝ≥0) : ℝ) := by
        exact_mod_cast hmono
    _ = (p : ℝ) ^ (-(e : ℤ)) := by push_cast; rw [hqN]

open NumberFieldKB.Chebotarev.RatIdele IsDedekindDomain.HeightOneSpectrum in
private theorem rat_finsetProd_localEulerFactor_prime_of_notMem
    (χ : HeckeCharacter (𝓞 ℚ) ℚ) (S : Finset Pl) (v : Pl) (hv : v ∉ S) :
    (∏ u ∈ S, χ.localEulerFactor u) (pr v) = 0 := by
  classical
  have hprime := pr_prime v
  induction S using Finset.induction_on with
  | empty => simp [hprime.ne_one]
  | insert u T hu ihT =>
    have hdiv : Nat.divisorsAntidiagonal (pr v) = {(1, pr v), (pr v, 1)} := by
      ext ⟨a, b⟩
      rw [Nat.mem_divisorsAntidiagonal, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hab, _⟩
        rcases hprime.eq_one_or_self_of_dvd a ⟨b, hab.symm⟩ with rfl | rfl
        · left; simp_all
        · right; simp_all [mul_eq_left₀ hprime.ne_zero]
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨by ring, hprime.ne_zero⟩
    rw [Finset.prod_insert hu, ArithmeticFunction.mul_apply, hdiv,
      Finset.sum_pair (by intro h; have := congrArg Prod.fst h; exact hprime.ne_one this.symm)]
    have hu_ne : pr u ≠ pr v := fun he ↦ hv (by
      have : u = v := pr_injective he
      subst this
      exact Finset.mem_insert_self _ _)
    have hmul_one : χ.localEulerFactor u 1 = 1 := by
      rw [HeckeCharacter.localEulerFactor, ArithmeticFunction.ofPowerSeries_apply_one,
        hecke_localPowerSeries_eq_mk]
      simp
    have hu0 : χ.localEulerFactor u (pr v) = 0 := by
      rw [HeckeCharacter.localEulerFactor, card_residueField_adicCompletion,
        absNorm_asIdeal, ArithmeticFunction.ofPowerSeries_apply (pr_prime u).one_lt,
        Function.extend_apply', Pi.zero_apply]
      rintro ⟨k, hk⟩
      rcases k with rfl | k
      · simp at hk; exact hprime.ne_one hk.symm
      · have hd : pr u ∣ pr v := hk ▸ dvd_pow_self _ (Nat.succ_ne_zero k)
        exact hu_ne ((Nat.prime_dvd_prime_iff_eq (pr_prime u) hprime).mp hd)
    have hT1 : (∏ y ∈ T, χ.localEulerFactor y) 1 = 1 := by
      have hmult : ArithmeticFunction.IsMultiplicative (∏ y ∈ T, χ.localEulerFactor y) := by
        refine ArithmeticFunction.isMultiplicative_finsetProd _ T fun y _ ↦ ?_
        rw [HeckeCharacter.localEulerFactor]
        refine ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow _ ?_ _
          (by rw [hecke_localPowerSeries_eq_mk]; simp)
        rw [card_residueField_adicCompletion, absNorm_asIdeal]
        exact (pr_prime y).isPrimePow
      exact hmult.1
    have hT0 : (∏ y ∈ T, χ.localEulerFactor y) (pr v) = 0 :=
      ihT (fun h ↦ hv (Finset.mem_insert_of_mem h))
    rw [hmul_one, hT0, hu0, hT1, mul_zero, zero_mul, add_zero]

open NumberFieldKB.Chebotarev.RatIdele IsDedekindDomain.HeightOneSpectrum in
private theorem rat_finsetProd_localEulerFactor_prime
    (χ : HeckeCharacter (𝓞 ℚ) ℚ) (S : Finset Pl) (v : Pl) (hv : v ∈ S) :
    (∏ w ∈ S, χ.localEulerFactor w) (pr v) = χ.localEulerFactor v (pr v) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact (Finset.notMem_empty v hv).elim
  | insert w S hw ih =>
    rw [Finset.prod_insert hw, ArithmeticFunction.mul_apply]
    have hmul_one : ∀ u : Pl, χ.localEulerFactor u 1 = 1 := fun u ↦ by
      rw [HeckeCharacter.localEulerFactor, ArithmeticFunction.ofPowerSeries_apply_one,
        hecke_localPowerSeries_eq_mk]
      simp
    have hprod_one : (∏ u ∈ S, χ.localEulerFactor u) 1 = 1 := by
      have hmult : ArithmeticFunction.IsMultiplicative (∏ u ∈ S, χ.localEulerFactor u) := by
        refine ArithmeticFunction.isMultiplicative_finsetProd _ S fun u _ ↦ ?_
        rw [HeckeCharacter.localEulerFactor]
        refine ArithmeticFunction.isMultiplicative_ofPowerSeries_of_isPrimePow _ ?_ _
          (by rw [hecke_localPowerSeries_eq_mk]; simp)
        rw [card_residueField_adicCompletion, absNorm_asIdeal]
        exact (pr_prime u).isPrimePow
      exact hmult.1
    have hprime := pr_prime v
    have hdiv : Nat.divisorsAntidiagonal (pr v) = {(1, pr v), (pr v, 1)} := by
      ext ⟨a, b⟩
      rw [Nat.mem_divisorsAntidiagonal, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hab, _⟩
        rcases hprime.eq_one_or_self_of_dvd a ⟨b, hab.symm⟩ with rfl | rfl
        · left; simp_all
        · right; simp_all [mul_eq_left₀ hprime.ne_zero]
      · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> exact ⟨by ring, hprime.ne_zero⟩
    rw [hdiv, Finset.sum_pair (by intro h; have := congrArg Prod.fst h; exact hprime.ne_one this.symm)]
    rcases Finset.mem_insert.mp hv with rfl | hvS
    · have hS0 : (∏ u ∈ S, χ.localEulerFactor u) (pr v) = 0 :=
        rat_finsetProd_localEulerFactor_prime_of_notMem χ S v hw
      rw [hmul_one v, hS0, hprod_one, mul_zero, mul_one, zero_add]
    · have hw_ne : pr w ≠ pr v := fun he ↦ hw (pr_injective he ▸ hvS)
      have hw0 : χ.localEulerFactor w (pr v) = 0 := by
        rw [HeckeCharacter.localEulerFactor, card_residueField_adicCompletion,
          absNorm_asIdeal, ArithmeticFunction.ofPowerSeries_apply (pr_prime w).one_lt,
          Function.extend_apply', Pi.zero_apply]
        rintro ⟨k, hk⟩
        rcases k with rfl | k
        · simp at hk; exact hprime.ne_one hk.symm
        · have hd : pr w ∣ pr v := hk ▸ dvd_pow_self _ (Nat.succ_ne_zero k)
          exact hw_ne ((Nat.prime_dvd_prime_iff_eq (pr_prime w) hprime).mp hd)
      rw [hmul_one w, ih hvS, hw0, one_mul, zero_mul, add_zero]

open NumberFieldKB.Chebotarev.RatIdele IsDedekindDomain.HeightOneSpectrum in
private theorem rat_unramified_localValue_eq_LFunction
    (ψ : PontryaginDual Cℚ) (v : Pl)
    (hunr : (ideleClassNormTwist ψ 0).IsUnramifiedAt v) :
    (ideleClassNormTwist ψ 0).LFunction (pr v) = (ideleClassNormTwist ψ 0).localValue v := by
  classical
  let χ := ideleClassNormTwist ψ 0
  obtain ⟨S, hS⟩ := Filter.eventually_atTop.mp
    (RiemannMasullo.heckeLocalEulerFactor_eventually_prod_eq χ (pr v))
  have hT := hS (insert v S) (Finset.subset_insert v S)
  rw [rat_finsetProd_localEulerFactor_prime χ (insert v S) v (Finset.mem_insert_self v S)] at hT
  rw [← hT, HeckeCharacter.localEulerFactor, card_residueField_adicCompletion,
    absNorm_asIdeal, hecke_localPowerSeries_eq_mk]
  have h1 : pr v = pr v ^ 1 := (pow_one (pr v)).symm
  conv_lhs =>
    arg 2
    rw [h1]
  rw [ArithmeticFunction.ofPowerSeries_apply_pow (pr_prime v).one_lt]
  rw [PowerSeries.coeff_mk, pow_one]
  simp only [χ, hunr, ↓reduceIte]

open NumberFieldKB.Chebotarev.RatIdele IsDedekindDomain.HeightOneSpectrum in
/-- Two unitary characters of `Cℚ` trivial on the decomposition section `t ↦ e (t, 1)` with the
same `finiteHeckeL` on `1 < Re s` are equal. -/
private theorem rat_eq_of_finiteHeckeL_eq_on_decompSection
    (e : (ℝ≥0ˣ × ((v : Pl) → (v.adicCompletionIntegers ℚ)ˣ)) ≃ₜ* Cℚ)
    (he : ∀ t h, ∃ g : IdQ,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (g.val.1 Rat.infinitePlace) = t.val ∧
      (∀ v, g.val.2 v = (h v).val.val) ∧ e (t, h) = QuotientGroup.mk g)
    {ψ₁ ψ₂ : PontryaginDual Cℚ}
    (hψ₁ : ∀ t, ψ₁ (e (t, 1)) = 1) (hψ₂ : ∀ t, ψ₂ (e (t, 1)) = 1)
    (hL : ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ₁ ⟨s, hs⟩ = finiteHeckeL ψ₂ ⟨s, hs⟩) :
    ψ₁ = ψ₂ := by
  classical
  let χ₁ := ideleClassNormTwist ψ₁ 0
  let χ₂ := ideleClassNormTwist ψ₂ 0
  have hab₁ : LSeries.abscissaOfAbsConv χ₁.LFunction < ⊤ :=
    (finiteHeckeL_seriesSummable ψ₁ ⟨2, by norm_num⟩).abscissaOfAbsConv_le.trans_lt
      (by simp)
  have hab₂ : LSeries.abscissaOfAbsConv χ₂.LFunction < ⊤ :=
    (finiteHeckeL_seriesSummable ψ₂ ⟨2, by norm_num⟩).abscissaOfAbsConv_le.trans_lt
      (by simp)
  have hcoeff : ∀ n : ℕ, n ≠ 0 → χ₁.LFunction n = χ₂.LFunction n := fun n hn ↦
    LSeries.eq_of_LSeries_eventually_eq hab₁ hab₂
      (eventually_atTop.mpr ⟨2, fun x hx ↦
        hL (x : ℂ) (by simpa using (by linarith : (1 : ℝ) < x))⟩) hn
  let θ : PontryaginDual Cℚ := ψ₁ * ψ₂⁻¹
  have hθ_real : ∀ t : ℝ≥0ˣ, θ (e (t, 1)) = 1 := fun t ↦ by
    change ψ₁ (e (t, 1)) * (ψ₂ (e (t, 1)))⁻¹ = 1
    rw [hψ₁ t, hψ₂ t, inv_one, mul_one]
  obtain ⟨n₁, hfin₁, hleast₁⟩ := exists_heckeConductorExponents (F := ℚ) ψ₁
  obtain ⟨n₂, hfin₂, hleast₂⟩ := exists_heckeConductorExponents (F := ℚ) ψ₂
  obtain ⟨n, hfin, hleast⟩ := exists_heckeConductorExponents (F := ℚ) θ
  let S : Finset Pl := hfin₁.toFinset ∪ hfin₂.toFinset ∪ hfin.toFinset
  have hunr₁ : ∀ v ∉ S, χ₁.IsUnramifiedAt v := fun v hv ↦ by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro t
    have hv1 : n₁ v = 0 := by
      by_contra hne
      exact hv (Finset.mem_union_left _ (Finset.mem_union_left _
        (hfin₁.mem_toFinset.mpr hne)))
    let u := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom t
    have hval : ‖u.val‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
      (adicCompletionIntegers.isUnit_iff_valued_eq_one.mp t.isUnit)
    have hsub : ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(n₁ v : ℤ)) := by
      rw [hv1, Nat.cast_zero, neg_zero, zpow_zero]
      exact Valued.toNormedField.norm_le_one_iff.mpr
        (Subring.sub_mem (v.adicCompletionIntegers ℚ).toSubring t.val.2 (Subring.one_mem _))
    have h1 := (hleast₁ v).1 u hval hsub
    change (ideleClassNormTwist ψ₁ 0).restrict v u.val = 1
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (ψ₁ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂ) * _ ^ (0 : ℂ) = 1
    rw [Complex.cpow_zero, mul_one, h1, Circle.coe_one]
  have hunr₂ : ∀ v ∉ S, χ₂.IsUnramifiedAt v := fun v hv ↦ by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro t
    have hv2 : n₂ v = 0 := by
      by_contra hne
      exact hv (Finset.mem_union_left _ (Finset.mem_union_right _
        (hfin₂.mem_toFinset.mpr hne)))
    let u := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom t
    have hval : ‖u.val‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
      (adicCompletionIntegers.isUnit_iff_valued_eq_one.mp t.isUnit)
    have hsub : ‖u.val - 1‖ ≤ (v.asIdeal.absNorm : ℝ) ^ (-(n₂ v : ℤ)) := by
      rw [hv2, Nat.cast_zero, neg_zero, zpow_zero]
      exact Valued.toNormedField.norm_le_one_iff.mpr
        (Subring.sub_mem (v.adicCompletionIntegers ℚ).toSubring t.val.2 (Subring.one_mem _))
    have h2 := (hleast₂ v).1 u hval hsub
    change (ideleClassNormTwist ψ₂ 0).restrict v u.val = 1
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (ψ₂ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂ) * _ ^ (0 : ℂ) = 1
    rw [Complex.cpow_zero, mul_one, h2, Circle.coe_one]
  have hpi : ∀ v ∉ S, θ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v
      (Units.mk0 (pr v : v.adicCompletion ℚ) (by
        intro h0
        have := valued_prime v (pr_prime v)
        simp only [h0, map_zero, Rat.cast_natCast, eq_self, ↓reduceIte] at this
        exact WithZero.coe_ne_zero this.symm))) = 1 := by
    intro v hv
    have hv_p := pr_prime v
    have hval := by
      simpa only [Rat.cast_natCast, eq_self, ↓reduceIte] using valued_prime v hv_p
    have hπ : Valued.v.IsUniformizer (pr v : v.adicCompletion ℚ) := by
      rw [Valuation.IsUniformizer.iff,
        Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range ⟨_, hval⟩]
      exact hval
    let π := Units.mk0 (pr v : v.adicCompletion ℚ) hπ.ne_zero
    have heqL := hcoeff (pr v) hv_p.ne_zero
    rw [rat_unramified_localValue_eq_LFunction ψ₁ v (hunr₁ v hv),
      rat_unramified_localValue_eq_LFunction ψ₂ v (hunr₂ v hv),
      (hunr₁ v hv).localValue_eq (π : v.adicCompletion ℚ) hπ,
      (hunr₂ v hv).localValue_eq (π : v.adicCompletion ℚ) hπ] at heqL
    have heqψ : (ψ₁ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π) : ℂ) =
        (ψ₂ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π) : ℂ) := by
      simp only [HeckeCharacter.restrict, MulChar.ofUnitHom_coe, MonoidHom.coe_comp,
        Function.comp_apply, MonoidHom.coe_toHomUnits] at heqL
      have hcp (ψ : PontryaginDual Cℚ) :
          (ideleClassNormTwist ψ 0).toMonoidHom
              (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π) =
            ψ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π) := by
        change (ψ _ : ℂ) * _ ^ (0 : ℂ) = _
        simp
      simpa only [χ₁, χ₂, hcp] using heqL
    apply Circle.ext
    change (ψ₁ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π) : ℂ) *
      ((ψ₂ (IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π) : ℂ))⁻¹ = 1
    rw [heqψ, mul_inv_cancel₀ (Circle.coe_ne_zero _)]
  let Uℚ := (v : Pl) → (v.adicCompletionIntegers ℚ)ˣ
  let φf : Uℚ →* Circle := (θ : Cℚ →* Circle).comp
    ((e : (ℝ≥0ˣ × Uℚ) →* Cℚ).comp (MonoidHom.inr ℝ≥0ˣ Uℚ))
  have hφc : Continuous φf :=
    θ.continuous.comp (e.continuous.comp (continuous_const.prodMk continuous_id))
  have hfinite : ∀ h : Uℚ, (∀ v, ‖(h v).val.val - 1‖ ≤ (pr v : ℝ) ^ (-(n v : ℤ))) →
      φf h = 1 := by
    have hsingle : ∀ (a : Pl) (u : (a.adicCompletionIntegers ℚ)ˣ),
        ‖((u : a.adicCompletionIntegers ℚ) : a.adicCompletion ℚ) - 1‖ ≤
          (pr a : ℝ) ^ (-(n a : ℤ)) →
        φf (Pi.mulSingle a u) = 1 := by
      intro a u hu
      let u' : (a.adicCompletion ℚ)ˣ :=
        Units.map (a.adicCompletionIntegers ℚ).subtype.toMonoidHom u
      obtain ⟨g, hg1, hg2, hge⟩ := he 1 (Pi.mulSingle a u)
      have hgid : IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ a u' = g := by
        apply Units.ext
        apply Prod.ext
        · funext w
          have hw : w = Rat.infinitePlace := Subsingleton.elim _ _
          subst hw
          apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal
            Rat.isReal_infinitePlace).injective
          rw [hg1]
          exact realPart_ofAdicCompletion a u'
        · ext v
          have h1 := coe_compV v (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ a u')
          rw [hg2 v]
          by_cases hv : v = a
          · subst hv
            rw [← h1, compV_ofAdicCompletion_self, Pi.mulSingle_eq_same]
            rfl
          · rw [← h1, compV_ofAdicCompletion_ne hv, Pi.mulSingle_eq_of_ne hv]
            rfl
      have hval : Valued.v ((u : a.adicCompletionIntegers ℚ) : a.adicCompletion ℚ) = 1 :=
        Valuation.Integers.one_of_isUnit' u.isUnit (fun x ↦ x.2)
      have hu' : ‖u'.val - 1‖ ≤ (a.asIdeal.absNorm : ℝ) ^ (-(n a : ℤ)) := by
        change ‖((u : a.adicCompletionIntegers ℚ) : a.adicCompletion ℚ) - 1‖ ≤ _
        rw [absNorm_asIdeal]
        exact hu
      have hc := (hleast a).1 u' (Valued.toNormedField.norm_eq_one_iff.mpr hval) hu'
      change θ (e (1, Pi.mulSingle a u)) = 1
      rw [hge, ← hgid]
      exact hc
    intro h hh
    let tr (T : Finset Pl) : Uℚ := fun v ↦ if v ∈ T then h v else 1
    have htr : ∀ T, φf (tr T) = 1 := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        have : tr ∅ = 1 := by
          funext v
          change (if v ∈ (∅ : Finset Pl) then h v else 1) = 1
          simp
        rw [this, map_one]
      | insert a T ha ih =>
        have : tr (insert a T) = tr T * Pi.mulSingle a (h a) := by
          funext v
          change (if v ∈ insert a T then h v else 1) =
            (if v ∈ T then h v else 1) * (Pi.mulSingle a (h a) : Uℚ) v
          by_cases hv : v = a
          · subst hv; simp [ha]
          · simp [hv]
        rw [this, map_mul, ih, hsingle a (h a) (hh a), mul_one]
    have hlim : Filter.Tendsto tr Filter.atTop (nhds h) := by
      rw [tendsto_pi_nhds]
      intro v
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Filter.eventually_ge_atTop {v}] with T hT
      have : v ∈ T := hT (Finset.mem_singleton_self v)
      simp [tr, this]
    have hconst : Filter.Tendsto (fun T ↦ φf (tr T)) Filter.atTop (nhds 1) := by
      simp only [htr]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique ((hφc.tendsto h).comp hlim) hconst
  have hφ_one : ∀ h : Uℚ, φf h = 1 := by
    intro h
    let M : ℕ := ∏ w ∈ S, pr w ^ (max (n w) 1)
    have hM : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun w _ ↦ pow_ne_zero _ (pr_prime w).ne_zero
    have : NeZero M := ⟨hM⟩
    have hM_fac (w : Pl) (hw : w ∈ S) : M.factorization (pr w) = max (n w) 1 := by
      have hdvd : pr w ^ max (n w) 1 ∣ M := Finset.dvd_prod_of_mem _ hw
      have hrest : M = pr w ^ max (n w) 1 * ∏ u ∈ S.erase w, pr u ^ max (n u) 1 := by
        dsimp only [M]
        rw [← Finset.mul_prod_erase S (fun u ↦ pr u ^ max (n u) 1) hw]
      rw [hrest, Nat.factorization_mul (pow_ne_zero _ (pr_prime w).ne_zero)
        (Finset.prod_ne_zero_iff.mpr fun u _ ↦ pow_ne_zero _ (pr_prime u).ne_zero),
        Finsupp.add_apply, (pr_prime w).factorization_pow, Finsupp.single_eq_same]
      have hnot : (∏ u ∈ S.erase w, pr u ^ max (n u) 1).factorization (pr w) = 0 := by
        rw [Nat.factorization_eq_zero_of_not_dvd]
        exact (pr_prime w).coprime_iff_not_dvd.mp (Nat.Coprime.prod_right fun u hu ↦
          ((Nat.coprime_primes (pr_prime w) (pr_prime u)).mpr fun he ↦
            (Finset.mem_erase.mp hu).1 (pr_injective he.symm)).pow_right _)
      rw [hnot, add_zero]
    have hM_mem (w : Pl) (hw : w ∈ S) : pr w ∈ M.primeFactors :=
      Nat.mem_primeFactors.mpr
        ⟨pr_prime w, (dvd_pow_self (pr w) (by omega)).trans (Finset.dvd_prod_of_mem _ hw), hM⟩
    let b : (q : M.primeFactors) → ZMod (q ^ M.factorization q) := fun q ↦
      let w := placeP M q
      redP q (Nat.prime_of_mem_primeFactors q.2) (M.factorization q) (h w).val.val
    let z : ZMod M := (ZMod.equivPi M hM).symm b
    have hz_unit : IsUnit z := IsUnit.map (ZMod.equivPi M hM).symm (Pi.isUnit_iff.mpr fun q ↦ by
      let w := placeP M q
      have hmul : redP q (Nat.prime_of_mem_primeFactors q.2) (M.factorization q) (h w).val.val *
          redP q (Nat.prime_of_mem_primeFactors q.2) (M.factorization q) ((h w)⁻¹).val.val = 1 := by
        rw [← redP_mul (h w).val.2 ((h w)⁻¹).val.2, ← Subring.coe_mul, ← Units.val_mul,
          mul_inv_cancel, Units.val_one, Subring.coe_one, redP_one]
      exact ⟨⟨_, _, hmul, (mul_comm _ _).trans hmul⟩, rfl⟩)
    let a : ℕ := z.val
    have ha_cop : a.Coprime M := (ZMod.isUnit_iff_coprime a M).mp (by
      simpa [a, ZMod.natCast_zmod_val] using hz_unit)
    obtain ⟨p, hp_gt, hp_prime, hp_mod⟩ :=
      Nat.forall_exists_prime_gt_and_modEq (S.sup pr) hM ha_cop
    let v : Pl := placeOf p hp_prime
    have hv_not : v ∉ S := fun hvS ↦ by
      have hle : pr v ≤ S.sup pr := Finset.le_sup hvS
      rw [pr_placeOf] at hle
      linarith
    have hval_p := by
      simpa only [v, Rat.cast_natCast, eq_self, ↓reduceIte, pr_placeOf] using valued_prime v hp_prime
    let π_v : (v.adicCompletion ℚ)ˣ := Units.mk0 (p : v.adicCompletion ℚ) (fun h0 ↦ by
      have hv := hval_p
      rw [h0, map_zero] at hv
      exact WithZero.coe_ne_zero hv.symm)
    let pU : ℚˣ := Units.mk0 (p : ℚ) (Nat.cast_ne_zero.mpr hp_prime.ne_zero)
    let x_p : IdQ := diag pU⁻¹ * IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π_v
    have hx_mk : (QuotientGroup.mk x_p : Cℚ) =
        QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π_v) := by
      have hd : (QuotientGroup.mk (diag pU⁻¹) : Cℚ) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr ⟨pU⁻¹, rfl⟩
      change (QuotientGroup.mk (diag pU⁻¹) : Cℚ) *
        QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π_v) = _
      rw [hd, one_mul]
    have hθ_xp : θ (QuotientGroup.mk x_p) = 1 := by
      rw [hx_mk]
      simpa [v, pr_placeOf] using hpi v hv_not
    have hw_val : ∀ w : Pl, Valued.v (x_p.val.2 w) = 1 ∧
        (w ≠ v → x_p.val.2 w = ((p : ℚ)⁻¹ : w.adicCompletion ℚ)) := by
      intro w
      rw [show x_p.val.2 w = (diag pU⁻¹).val.2 w *
          (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π_v).val.2 w from rfl]
      have hd : (diag pU⁻¹).val.2 w = ((p : ℚ)⁻¹ : w.adicCompletion ℚ) := by
        rw [← coe_compV, coe_compV_diag]
        simp [pU]
      rw [hd]
      by_cases hwv : w = v
      · subst hwv
        rw [← coe_compV, compV_ofAdicCompletion_self]
        change Valued.v (((p : ℚ)⁻¹ : v.adicCompletion ℚ) * (p : v.adicCompletion ℚ)) = 1 ∧ _
        have hmul : ((p : ℚ)⁻¹ : v.adicCompletion ℚ) * (p : v.adicCompletion ℚ) = 1 := by
          have hp_cast_v : ((p : ℚ)⁻¹ : v.adicCompletion ℚ) = (p : v.adicCompletion ℚ)⁻¹ := by
            push_cast
            rfl
          have hp_ne_v : (p : v.adicCompletion ℚ) ≠ 0 := π_v.ne_zero
          rw [hp_cast_v, inv_mul_cancel₀ hp_ne_v]
        rw [hmul, map_one]
        exact ⟨rfl, fun h ↦ (h rfl).elim⟩
      · have hc : (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π_v).val.2 w = 1 := by
          rw [← coe_compV, compV_ofAdicCompletion_ne hwv]
          rfl
        rw [hc, mul_one]
        refine ⟨?_, fun _ ↦ rfl⟩
        rw [map_inv₀, valued_prime w hp_prime,
          ite_eq_right (fun he ↦ hwv (pr_injective (he.trans (pr_placeOf p hp_prime).symm))),
          inv_one]
    have hx_ne (w : Pl) : x_p.val.2 w ≠ 0 := by
      intro h0
      have := (hw_val w).1
      rw [h0, map_zero] at this
      exact zero_ne_one this
    let h_p : Uℚ := fun w ↦
      ⟨⟨x_p.val.2 w, (hw_val w).1.le⟩,
        ⟨(x_p.val.2 w)⁻¹, show Valued.v (x_p.val.2 w)⁻¹ ≤ 1 from by
          rw [map_inv₀, (hw_val w).1, inv_one]⟩,
        Subtype.ext (mul_inv_cancel₀ (hx_ne w)),
        Subtype.ext (inv_mul_cancel₀ (hx_ne w))⟩
    have hp_pos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hp_prime.pos)
    let t_p : ℝ≥0ˣ := Units.mk0 ⟨(p : ℝ)⁻¹, hp_pos.le⟩ (fun h ↦ hp_pos.ne' (congrArg Subtype.val h))
    obtain ⟨g, hg1, hg2, hge⟩ := he t_p h_p
    have hgx : x_p = g := by
      apply Units.ext
      apply Prod.ext
      · funext w
        have hw : w = Rat.infinitePlace := Subsingleton.elim _ _
        subst hw
        apply (InfinitePlace.Completion.extensionEmbeddingOfIsReal
          Rat.isReal_infinitePlace).injective
        rw [hg1]
        have hxinf : InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
            (x_p.val.1 Rat.infinitePlace) = (t_p : ℝ) := by
          change realPart x_p = (p : ℝ)⁻¹
          rw [show x_p = diag pU⁻¹ * IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π_v from rfl]
          have h1 : x_p.val.1 Rat.infinitePlace = (diag pU⁻¹).val.1 Rat.infinitePlace := by
            change (diag pU⁻¹).val.1 Rat.infinitePlace *
              (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π_v).val.1 Rat.infinitePlace = _
            have hinf1 : (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π_v).val.1 Rat.infinitePlace = 1 := rfl
            rw [hinf1, mul_one]
          change InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
            (x_p.val.1 Rat.infinitePlace) = (p : ℝ)⁻¹
          rw [h1]
          exact (realPart_diag pU⁻¹).trans (by simp [pU])
        exact hxinf
      · exact Subtype.ext (funext fun w ↦ (hg2 w).symm)
    have hθ_hp : φf h_p = 1 := by
      have hsplit : e (t_p, h_p) = e (t_p, 1) * e (1, h_p) := by rw [← map_mul]; simp
      have he1 : θ (e (t_p, h_p)) = 1 := by rw [hge, ← hgx]; exact hθ_xp
      rw [hsplit, map_mul, hθ_real t_p, one_mul] at he1
      exact he1
    have hprod_one : φf (h * h_p) = 1 := by
      refine hfinite (h * h_p) fun w ↦ ?_
      by_cases hwS : w ∈ S
      · have hw_ne : w ≠ v := fun he ↦ hv_not (he ▸ hwS)
        obtain ⟨pw, hpw, rfl⟩ : ∃ (pw : ℕ) (hpw : pw.Prime), w = placeOf pw hpw :=
          ⟨pr w, pr_prime w, (eq_placeOf_iff w (pr w) (pr_prime w)).mpr rfl⟩
        have hqM : pw ∈ M.primeFactors := by
          simpa only [pr_placeOf] using hM_mem (placeOf pw hpw) hwS
        let q : M.primeFactors := ⟨pw, hqM⟩
        have hp_cast : (p : ZMod (pw ^ M.factorization pw)) =
            redP pw hpw (M.factorization pw) (h (placeOf pw hpw)).val.val := by
          have h1 : (p : ZMod M) = z :=
            ((ZMod.natCast_eq_natCast_iff p a M).mpr hp_mod).trans (ZMod.natCast_zmod_val z)
          have h2 := congrFun (congrArg (ZMod.equivPi M hM) h1) q
          rw [map_natCast, RingEquiv.apply_symm_apply] at h2
          exact h2
        have hp_unit : ((h_p (placeOf pw hpw)).val.val) =
            ((p : ℚ)⁻¹ : (placeOf pw hpw).adicCompletion ℚ) :=
          (hw_val (placeOf pw hpw)).2 hw_ne
        have hred : redP pw hpw (M.factorization pw)
            (((h * h_p) (placeOf pw hpw)).val.val) = 1 := by
          have hval_w : Valued.v ((h (placeOf pw hpw)).val.val) ≤ 1 := (h (placeOf pw hpw)).val.2
          have hval_p : Valued.v ((h_p (placeOf pw hpw)).val.val) ≤ 1 := (h_p (placeOf pw hpw)).val.2
          change redP pw hpw (M.factorization pw)
            ((h (placeOf pw hpw)).val.val * (h_p (placeOf pw hpw)).val.val) = 1
          have hp_cast' : redP pw hpw (M.factorization pw) (h (placeOf pw hpw)).val.val =
              redP pw hpw (M.factorization pw) (p : Kp pw hpw) := by
            rw [← hp_cast]
            exact (redP_natCast p).symm
          have hp_cast_w : ((p : ℚ)⁻¹ : Kp pw hpw) = (p : Kp pw hpw)⁻¹ := by
            push_cast
            rfl
          have hp_ne_w : (p : Kp pw hpw) ≠ 0 := fun h0 ↦ by
            have hv := valued_prime (placeOf pw hpw) hp_prime
            have hpc : ((p : ℚ) : Kp pw hpw) = (p : Kp pw hpw) := by push_cast; rfl
            rw [hpc, h0, map_zero,
              ite_eq_right (fun he ↦ hw_ne (pr_injective (he.trans (pr_placeOf p hp_prime).symm)))] at hv
            exact one_ne_zero hv.symm
          rw [redP_mul hval_w hval_p, hp_cast',
            ← redP_mul (valued_natCast_le_one (placeOf pw hpw) p) hval_p,
            hp_unit, hp_cast_w, mul_inv_cancel₀ hp_ne_w, redP_one]
        have hnorm := rat_norm_sub_one_le_of_redP_eq_one (hp := hpw) (e := M.factorization pw)
          (z := ((h * h_p) (placeOf pw hpw)).val.val) ((h * h_p) (placeOf pw hpw)).val.2 hred
        have hfac_pw : M.factorization pw = max (n (placeOf pw hpw)) 1 := by
          simpa only [pr_placeOf] using hM_fac (placeOf pw hpw) hwS
        have hbound_le : (pw : ℝ) ^ (-(M.factorization pw : ℤ)) ≤
            (pr (placeOf pw hpw) : ℝ) ^ (-(n (placeOf pw hpw) : ℤ)) := by
          rw [pr_placeOf, hfac_pw]
          refine zpow_le_zpow_right₀ (by exact_mod_cast hpw.one_lt.le) ?_
          exact neg_le_neg (by exact_mod_cast le_max_left (n (placeOf pw hpw)) 1)
        exact hnorm.trans hbound_le
      · have hnw0 : n w = 0 := by
          by_contra hne
          exact hwS (Finset.mem_union_right _ (hfin.mem_toFinset.mpr hne))
        rw [hnw0, Nat.cast_zero, neg_zero, zpow_zero]
        exact Valued.toNormedField.norm_le_one_iff.mpr
          (Subring.sub_mem (w.adicCompletionIntegers ℚ).toSubring
            ((h * h_p) w).val.2 (Subring.one_mem _))
    rw [map_mul, hθ_hp, mul_one] at hprod_one
    exact hprod_one
  ext g : 1
  obtain ⟨⟨t, h⟩, rfl⟩ := e.surjective g
  have hsplit : e (t, h) = e (t, 1) * e (1, h) := by rw [← map_mul]; simp
  have hθg : θ (e (t, h)) = 1 := by
    rw [hsplit, map_mul]
    change θ (e (t, 1)) * φf h = 1
    rw [hθ_real t, hφ_one h, mul_one]
  apply Circle.ext
  have hθc : (ψ₁ (e (t, h)) : ℂ) * (ψ₂ (e (t, h)) : ℂ)⁻¹ = 1 := by
    have hθg' : ψ₁ (e (t, h)) * (ψ₂ (e (t, h)))⁻¹ = 1 := hθg
    simpa [Circle.coe_mul, Circle.coe_inv] using congrArg (fun z : Circle ↦ (z : ℂ)) hθg'
  exact mul_inv_eq_one₀ (Circle.coe_ne_zero _) |>.mp hθc

/-- Any unitary character `ψ` of `Cℚ` trivial on the decomposition section `t ↦ e (t, 1)` is the
canonical lift of a primitive Dirichlet character, and only finitely many such `ψ` have conductor
at most `B`. -/
private theorem rat_finite_decomp_trivial_le_conductor
    (e : (ℝ≥0ˣ × ((v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) →
      (v.adicCompletionIntegers ℚ)ˣ)) ≃ₜ* Cℚ)
    (he : ∀ t h, ∃ g : NumberFieldKB.Chebotarev.RatIdele.IdQ,
      InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
        (g.val.1 Rat.infinitePlace) = t.val ∧
      (∀ v, g.val.2 v = (h v).val.val) ∧ e (t, h) = QuotientGroup.mk g)
    (B : ℕ) :
    {ω : PontryaginDual C₁ℚ | ∃ (N : ℕ) (_ : NeZero N), N ≤ B ∧
      ∃ (χ : DirichletCharacter ℂ N) (_ : χ.IsPrimitive) (ψ : PontryaginDual Cℚ),
        (∀ t, ψ (e (t, 1)) = 1) ∧ ψ.comp restrictionℚ = ω ∧
        ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s}.Finite := by
  classical
  let S_N (N : ℕ) [NeZero N] :=
    {ω : PontryaginDual C₁ℚ | ∃ (χ : DirichletCharacter ℂ N) (ψ : PontryaginDual Cℚ),
      (∀ t, ψ (e (t, 1)) = 1) ∧ ψ.comp restrictionℚ = ω ∧
      ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s}
  have hfin_N (N : ℕ) [NeZero N] : (S_N N).Finite := by
    let P (χ : DirichletCharacter ℂ N) :=
      {ω : PontryaginDual C₁ℚ | ∃ ψ : PontryaginDual Cℚ,
        (∀ t, ψ (e (t, 1)) = 1) ∧ ψ.comp restrictionℚ = ω ∧
        ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s}
    have hP (χ : DirichletCharacter ℂ N) : (P χ).Subsingleton := by
      rintro ω₁ ⟨ψ₁, hτ₁, rfl, hL₁⟩ ω₂ ⟨ψ₂, hτ₂, rfl, hL₂⟩
      have heq := rat_eq_of_finiteHeckeL_eq_on_decompSection e he hτ₁ hτ₂
        (fun s hs ↦ (hL₁ s hs).trans (hL₂ s hs).symm)
      rw [heq]
    have hP_fin (χ : DirichletCharacter ℂ N) : (P χ).Finite := (hP χ).finite
    have hfin_chars : Finite (DirichletCharacter ℂ N) := inferInstance
    refine ((Set.finite_univ.biUnion fun χ (_ : χ ∈ (Set.univ : Set (DirichletCharacter ℂ N))) ↦
      hP_fin χ)).subset ?_
    rintro ω ⟨χ, ψ, hτ, rfl, hL⟩
    exact Set.mem_iUnion₂.mpr ⟨χ, Set.mem_univ χ, ψ, hτ, rfl, hL⟩
  refine ((Finset.Icc 1 B).finite_toSet.biUnion fun N hN ↦ by
    have : NeZero N := ⟨Nat.pos_iff_ne_zero.mp (Finset.mem_Icc.mp hN).1⟩
    exact hfin_N N).subset ?_
  rintro ω ⟨N, hN0, hNB, χ, -, ψ, hτ, rfl, hL⟩
  exact Set.mem_iUnion₂.mpr ⟨N, Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero (NeZero.ne N), hNB⟩,
    χ, ψ, hτ, rfl, hL⟩

/-- Helper lemma: the norm-1 idele class group over `ℚ` and the decomposition section `τ₀`. -/
private theorem rat_exists_decomp_section :
    ∃ (e : (ℝ≥0ˣ × ((v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) →
      (v.adicCompletionIntegers ℚ)ˣ)) ≃ₜ* Cℚ)
      (τ : ℝ≥0ˣ →ₜ* Cℚ),
      RightInverse τ (ideleClassNorm ℚ) ∧
      (∀ t, τ t = e (t, 1)) ∧
      ∀ t h, ∃ g : NumberFieldKB.Chebotarev.RatIdele.IdQ,
        InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
          (g.val.1 Rat.infinitePlace) = t.val ∧
        (∀ v, g.val.2 v = (h v).val.val) ∧ e (t, h) = QuotientGroup.mk g := by
  classical
  obtain ⟨e, he⟩ := ratIdeleClassGroup_decomposition
  let Uℚ := (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletionIntegers ℚ)ˣ
  let τ : ℝ≥0ˣ →ₜ* Cℚ :=
    ⟨(e : (ℝ≥0ˣ × Uℚ) →* Cℚ).comp (MonoidHom.inl ℝ≥0ˣ Uℚ),
      e.continuous.comp (continuous_id.prodMk (continuous_const : Continuous fun _ : ℝ≥0ˣ ↦
        (1 : Uℚ)))⟩
  refine ⟨e, τ, fun t ↦ ?_, fun _ ↦ rfl, he⟩
  obtain ⟨g, hg1, hg2, hge⟩ := he t 1
  change ideleClassNorm ℚ (e (t, 1)) = t
  rw [hge]
  apply Units.ext
  apply NNReal.coe_injective
  change ((ideleNorm ℚ g : ℝ≥0) : ℝ) = (t : ℝ)
  rw [((ideleNorm_spec ℚ).1 g).2]
  have hval (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
      Valued.v ((1 : (v.adicCompletionIntegers ℚ)ˣ).val.val) = 1 :=
    Valuation.Integers.one_of_isUnit' (1 : (v.adicCompletionIntegers ℚ)ˣ).isUnit (fun x ↦ x.2)
  have hfin : (∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ), ‖g.val.2 v‖) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ by
      rw [hg2 v]
      exact Valued.toNormedField.norm_eq_one_iff.mpr (hval v)
  rw [hfin, mul_one, Fintype.prod_unique]
  have hd : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  rw [hd, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  have hiso := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) (g.val.1 Rat.infinitePlace)
  rw [← hiso, hg1, Real.norm_eq_abs, abs_of_pos (NNReal.coe_pos.mpr (Units.zero_lt t))]

private theorem rat_trivial_on_section_of_isOfFinOrder (ψ : PontryaginDual Cℚ)
    (hψ : IsOfFinOrder ψ) (τ : ℝ≥0ˣ →ₜ* Cℚ) (t : ℝ≥0ˣ) : ψ (τ t) = 1 := by
  obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hψ
  let r := (t : ℝ≥0) ^ ((k : ℝ)⁻¹)
  let u : ℝ≥0ˣ := Units.mk0 r (NNReal.rpow_pos (Units.zero_lt t)).ne'
  have hu : u ^ k = t := Units.ext (NNReal.rpow_inv_natCast_pow _ hk.ne')
  rw [← hu, map_pow, map_pow]
  exact (ContinuousMonoidHom.pow_apply (ψ : Cℚ →ₜ* Circle) k (τ u)).symm.trans
    (congrArg (fun η : PontryaginDual Cℚ ↦ η (τ u)) hpow)

/-! ### Public characterizations of `#7485` over `ℚ` via Dirichlet `L`-functions -/

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Over `ℚ`, finiteness of the multiple real zeros for every choice of basepoints is equivalent to
the existence of a conductor threshold `B : ℕ` and a finite set `S : Finset ℝ` such that every
multiple zero `z` in the open right half of the critical strip (`1 / 2 < Re z < 1`) of every
primitive Dirichlet `L`-function of conductor `N > B` has real part in `S`.
Deviation: The paper does not state this characterization in terms of Dirichlet `L`-functions. -/
theorem spectralStripJet_multiple_real_zeros_finite_rat_iff_dirichlet :
    (∀ (χ : PontryaginDual C₁ℚ → PontryaginDual Cℚ), IsSpectralBasepointChoice (F := ℚ) χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁ℚ,
        1 < multℚ(χ ω, (σ : ℂ))}.Finite) ↔
    ∃ (B : ℕ) (S : Finset ℝ), ∀ (N : ℕ) [NeZero N], B < N →
      ∀ (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
        ∀ (z : ℂ), 1 / 2 < z.re → z.re < 1 →
          (1 : ℕ∞) < analyticOrderAt (DirichletCharacter.LFunction χ) z → z.re ∈ S := by
  classical
  obtain ⟨e, τ, hτ, hτe, he⟩ := rat_exists_decomp_section
  obtain ⟨χ₀, hχ₀, hχ₀τ, -⟩ := exists_spectralBasepointChoice_of_normSection (F := ℚ) τ hτ
  constructor
  · intro hreal
    obtain ⟨E, S, hcover⟩ :=
      (spectralStripJet_multiple_real_zeros_finite_iff_finite_cover (F := ℚ)).mp hreal
    have hcomp : ∀ ω : PontryaginDual C₁ℚ, ∃ (N : ℕ) (_ : NeZero N)
        (χ : DirichletCharacter ℂ N), χ.IsPrimitive ∧
        ∀ s : ℂ, ∀ hs : 1 < s.re, finiteHeckeL (χ₀ ω) ⟨s, hs⟩ = LSeries (χ ·) s :=
      fun ω ↦ exists_primitive_finiteHeckeL_eq_of_trivial_on_section τ hτ (χ₀ ω) (hχ₀τ ω)
    choose cond hcond_ne char hchar_prim hchar_L using hcomp
    let B : ℕ := E.sup cond
    refine ⟨B, S, fun N _ hBN χ hχ z hz_lo hz_hi hz_ord ↦ ?_⟩
    obtain ⟨ψ, hψ_fin, hψ_L⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq hχ
    have hψ_τ : ∀ t : ℝ≥0ˣ, ψ (τ t) = 1 :=
      rat_trivial_on_section_of_isOfFinOrder ψ hψ_fin τ
    have hnotE : ψ.comp restrictionℚ ∉ E := by
      intro hmem
      let ω := ψ.comp restrictionℚ
      have heq_ψ : ψ = χ₀ ω :=
        rat_eq_of_trivial_on_section_and_restriction_eq τ hτ hψ_τ (hχ₀τ ω) (hχ₀ ω).symm
      have hL_eq : ∀ s : ℂ, 1 < s.re → LSeries (χ ·) s = LSeries ((char ω) ·) s := fun s hs ↦ by
        rw [← hψ_L s hs, heq_ψ, hchar_L ω s hs]
      have hN_eq : N = cond ω := by
        have : NeZero (cond ω) := hcond_ne ω
        exact (rat_primitive_dirichlet_eq_of_LSeries_eq hχ (hchar_prim ω) hL_eq).1
      have hle : cond ω ≤ B := Finset.le_sup hmem
      omega
    have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz_hi
    have hm : 1 < multℚ(ψ, shift(z.re, z.im)) := by
      have hz_eq : shift(z.re, z.im) = z := Complex.re_add_im z
      rw [hz_eq]
      exact (rat_one_lt_mult_iff_one_lt_analyticOrderAt ψ hψ_L (by linarith) hz1).mpr hz_ord
    rcases hcover ψ z.re z.im ⟨hz_lo, hz_hi⟩ hm with hE | hS
    · exact (hnotE hE).elim
    · exact hS
  · rintro ⟨B, S, hdir⟩
    have hE_fin := rat_finite_decomp_trivial_le_conductor e he B
    let E : Finset (PontryaginDual C₁ℚ) := hE_fin.toFinset
    refine (spectralStripJet_multiple_real_zeros_finite_iff_finite_cover (F := ℚ)).mpr
      ⟨E, S, fun ψ σ t hσ hm ↦ ?_⟩
    by_cases hω : ψ.comp restrictionℚ ∈ E
    · exact Or.inl hω
    · right
      let ω := ψ.comp restrictionℚ
      obtain ⟨d, hd, -⟩ := spectralZeroMultiplicity_existsUnique_shift_of_restriction_eq
        (F := ℚ) ψ (χ₀ ω) (hχ₀ ω).symm
      have hm' : 1 < multℚ(χ₀ ω, shift(σ, t + d)) := by
        rw [Complex.ofReal_add, ← (hd σ t).2]
        exact hm
      obtain ⟨N, hN, χ, hprim, hL⟩ :=
        exists_primitive_finiteHeckeL_eq_of_trivial_on_section τ hτ (χ₀ ω) (hχ₀τ ω)
      have hBN : B < N := by
        by_contra! hle
        apply hω
        exact (Set.Finite.mem_toFinset hE_fin).mpr
          ⟨N, hN, hle, χ, hprim, χ₀ ω, fun u ↦ by simpa only [← hτe] using hχ₀τ ω u, hχ₀ ω, hL⟩
      have hre : (shift(σ, t + d)).re = σ := by simp
      have hz1 : shift(σ, t + d) ≠ 1 := fun h ↦ by
        have := congrArg Complex.re h
        rw [hre, Complex.one_re] at this
        linarith [hσ.2]
      have hord := (rat_one_lt_mult_iff_one_lt_analyticOrderAt (χ₀ ω) hL
        (by rw [hre]; linarith [hσ.1]) hz1).mp hm'
      simpa only [hre] using hdir N hBN χ hprim (shift(σ, t + d)) (by rw [hre]; exact hσ.1)
        (by rw [hre]; exact hσ.2) hord

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
If `#7485` holds over `ℚ`, then there exist a conductor threshold `B : ℕ` and a uniform width
`δ > 0` such that every Dirichlet `L`-function (primitive or imprimitive) of conductor greater
than `B` has only simple zeros (or is nonvanishing) on the vertical strip `1 - δ < Re z < 1`.
Deviation: The paper does not state this conductor-uniform zero-free-of-multiple-zeros strip. -/
theorem dirichletL_uniform_multiple_zero_free_strip_of_multiple_real_zeros_finite_rat
    (hreal : ∀ (χ : PontryaginDual C₁ℚ → PontryaginDual Cℚ), IsSpectralBasepointChoice (F := ℚ) χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁ℚ,
        1 < multℚ(χ ω, (σ : ℂ))}.Finite) :
    ∃ (B : ℕ) (δ : ℝ), 0 < δ ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      B < χ.conductor → ∀ (z : ℂ), 1 - δ < z.re → z.re < 1 →
        analyticOrderAt (DirichletCharacter.LFunction χ) z ≤ 1 := by
  classical
  obtain ⟨B, S, hdir⟩ := spectralStripJet_multiple_real_zeros_finite_rat_iff_dirichlet.mp hreal
  let S' := S.filter (fun σ : ℝ ↦ σ < 1)
  let d (σ : ℝ) : ℝ := 1 - σ
  obtain ⟨δ, hmem, hmin⟩ := Set.exists_min_image (insert (1 / 2 : ℝ) (S'.image d : Set ℝ)) id
    ((S'.image d).finite_toSet.insert (1 / 2)) (Set.insert_nonempty _ _)
  have hδ : 0 < δ := by
    rcases hmem with rfl | h
    · norm_num
    · obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp h
      exact sub_pos.mpr (Finset.mem_filter.mp hσ).2
  have hδ_half : δ ≤ 1 / 2 := hmin (1 / 2) (Or.inl rfl)
  refine ⟨B, δ, hδ, fun N _ χ hBc z hz_lo hz_hi ↦ ?_⟩
  have hz_half : 1 / 2 < z.re := by linarith
  have hz_pos : 0 < z.re := by linarith
  have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz_hi
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hfac : AnalyticAt ℂ (fun w : ℂ ↦
      ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-w))) z ∧
      (∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-z))) ≠ 0 := by
    refine ⟨?_, Finset.prod_ne_zero_iff.mpr fun p hp he ↦ ?_⟩
    · apply Differentiable.analyticAt
      apply Differentiable.fun_finsetProd
      intro p hp
      have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact (differentiable_const 1).sub
        ((differentiable_const _).mul (differentiable_id.neg.const_cpow (Or.inl hp0)))
    · have h0 := dirichletEulerFactor_zero_re_eq_zero χ.primitiveCharacter
        (Nat.prime_of_mem_primeFactors hp) he
      linarith
  have hL_eq : DirichletCharacter.LFunction χ =ᶠ[𝓝 z] fun w : ℂ ↦
      DirichletCharacter.LFunction χ.primitiveCharacter w *
        ∏ p ∈ N.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-w)) := by
    filter_upwards [(isOpen_compl_singleton.mem_nhds hz1)] with w hw
    have hw1 : w ≠ 1 := hw
    have hcl := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level
      χ.primitiveCharacter (.inr hw1)
    rw [χ.changeLevel_primitiveCharacter] at hcl
    exact hcl
  have hA_prim : AnalyticAt ℂ (DirichletCharacter.LFunction χ.primitiveCharacter) z :=
    DifferentiableOn.analyticAt (fun w hw ↦ (DirichletCharacter.differentiableAt_LFunction
      χ.primitiveCharacter w (.inl hw)).differentiableWithinAt)
      (isOpen_compl_singleton.mem_nhds hz1)
  have hord_eq : analyticOrderAt (DirichletCharacter.LFunction χ) z =
      analyticOrderAt (DirichletCharacter.LFunction χ.primitiveCharacter) z := by
    have hmul := analyticOrderAt_mul hA_prim hfac.1
    rw [hfac.1.analyticOrderAt_eq_zero.mpr hfac.2, add_zero] at hmul
    exact (analyticOrderAt_congr hL_eq).trans hmul
  rw [hord_eq]
  by_contra! hgt
  have hzS : z.re ∈ S := hdir χ.conductor hBc χ.primitiveCharacter
    χ.primitiveCharacter_isPrimitive z hz_half hz_hi hgt
  have hzS' : z.re ∈ S' := Finset.mem_filter.mpr ⟨hzS, hz_hi⟩
  have hle : δ ≤ d z.re := hmin _ (Or.inr (Finset.mem_coe.mpr (Finset.mem_image_of_mem d hzS')))
  dsimp [d] at hle
  linarith

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
If all primitive Dirichlet `L`-functions of conductor greater than some threshold `B` have at
most simple zeros in `1 / 2 < Re z < 1`, then `#7485` holds over `ℚ`.
Deviation: The paper does not state this sufficient condition. -/
theorem spectralStripJet_multiple_real_zeros_finite_rat_of_dirichlet_offline_simple
    (h : ∃ B : ℕ, ∀ (N : ℕ) [NeZero N], B < N → ∀ (χ : DirichletCharacter ℂ N),
      χ.IsPrimitive → ∀ (z : ℂ), 1 / 2 < z.re → z.re < 1 →
        analyticOrderAt (DirichletCharacter.LFunction χ) z ≤ 1) :
    ∀ (χ : PontryaginDual C₁ℚ → PontryaginDual Cℚ), IsSpectralBasepointChoice (F := ℚ) χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁ℚ,
        1 < multℚ(χ ω, (σ : ℂ))}.Finite := by
  obtain ⟨B, hB⟩ := h
  refine spectralStripJet_multiple_real_zeros_finite_rat_iff_dirichlet.mpr ⟨B, ∅, ?_⟩
  intro N _ hBN χ hprim z hz_lo hz_hi hord
  exact (not_le_of_gt hord (hB N hBN χ hprim z hz_lo hz_hi)).elim

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Dirichlet GRH (`DirichletLNonvanishingRightOfHalf` of `Statements.lean`) implies `#7485` over `ℚ`.
Deviation: The paper does not state this corollary. -/
theorem spectralStripJet_multiple_real_zeros_finite_rat_of_dirichletGRH
    (hGRH : ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
      1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0) :
    ∀ (χ : PontryaginDual C₁ℚ → PontryaginDual Cℚ), IsSpectralBasepointChoice (F := ℚ) χ →
      {σ : ℝ | σ ∈ Ioo (1 / 2 : ℝ) 1 ∧ ∃ ω : PontryaginDual C₁ℚ,
        1 < multℚ(χ ω, (σ : ℂ))}.Finite := by
  refine spectralStripJet_multiple_real_zeros_finite_rat_of_dirichlet_offline_simple ⟨0, ?_⟩
  intro N _ _ χ _ z hz_lo hz_hi
  have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz_hi
  have hA : AnalyticAt ℂ (DirichletCharacter.LFunction χ) z := by
    have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {1}ᶜ := fun w hw ↦
      (DirichletCharacter.differentiableAt_LFunction χ w (.inl hw)).differentiableWithinAt
    exact hd.analyticAt (isOpen_compl_singleton.mem_nhds hz1)
  rw [hA.analyticOrderAt_eq_zero.mpr (hGRH N χ z hz_lo (.inr hz1))]
  exact (zero_le : (0 : ℕ∞) ≤ 1)

/-- Paper: Proposition 10.2.2.2, pp. 446–447.
Over `ℚ`, finiteness of all vertical lines carrying multiple zeros of completed Hecke
`L`-functions (`#7453 ∧ #7485`) holds if and only if there is one finite set `S : Finset ℝ`
containing the real parts of all multiple zeros in `1 / 2 < Re z < 1` across all primitive
Dirichlet characters of all conductors `N ≥ 1`.
Deviation: The paper does not state this Dirichlet characterization of `#7453 ∧ #7485` over `ℚ`. -/
theorem spectralStripJet_multiple_zero_lines_finite_rat_iff_dirichlet
    (χ : PontryaginDual C₁ℚ → PontryaginDual Cℚ) (_hχ : IsSpectralBasepointChoice (F := ℚ) χ) :
    {σ : ℝ | ∃ (ω : PontryaginDual C₁ℚ) (t : ℝ), 1 < multℚ(χ ω, shift(σ, t))}.Finite ↔
    ∃ S : Finset ℝ, ∀ (N : ℕ) [NeZero N] (χ₀ : DirichletCharacter ℂ N), χ₀.IsPrimitive →
      ∀ (z : ℂ), 1 / 2 < z.re → z.re < 1 →
        (1 : ℕ∞) < analyticOrderAt (DirichletCharacter.LFunction χ₀) z → z.re ∈ S := by
  classical
  constructor
  · intro hfin
    let S : Finset ℝ := hfin.toFinset
    refine ⟨S, fun N _ χ₀ hprim z hz_lo hz_hi hz_ord ↦ ?_⟩
    obtain ⟨ψ, -, hL⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq hprim
    have hz1 : z ≠ 1 := fun h ↦ by simp [h] at hz_hi
    have hm : 1 < multℚ(ψ, shift(z.re, z.im)) := by
      have hz_eq : shift(z.re, z.im) = z := Complex.re_add_im z
      rw [hz_eq]
      exact (rat_one_lt_mult_iff_one_lt_analyticOrderAt ψ hL (by linarith) hz1).mpr hz_ord
    let ω := ψ.comp restrictionℚ
    obtain ⟨d, hd, -⟩ := spectralZeroMultiplicity_existsUnique_shift_of_restriction_eq
      (F := ℚ) ψ (χ ω) (_hχ ω).symm
    have hm' : 1 < multℚ(χ ω, shift(z.re, z.im + d)) := by
      rw [Complex.ofReal_add, ← (hd z.re z.im).2]
      exact hm
    exact hfin.mem_toFinset.mpr ⟨ω, z.im + d, hm'⟩
  · rintro ⟨S, hdir⟩
    obtain ⟨_, τ, hτ, _, _⟩ := rat_exists_decomp_section
    obtain ⟨χ₀, hχ₀, hχ₀τ, -⟩ := exists_spectralBasepointChoice_of_normSection (F := ℚ) τ hτ
    have hright : ∀ (ψ : PontryaginDual Cℚ) (σ t : ℝ), σ ∈ Ioo (1 / 2 : ℝ) 1 →
        1 < multℚ(ψ, shift(σ, t)) → σ ∈ S := by
      intro ψ σ t hσ hm
      let ω := ψ.comp restrictionℚ
      obtain ⟨d, hd, -⟩ := spectralZeroMultiplicity_existsUnique_shift_of_restriction_eq
        (F := ℚ) ψ (χ₀ ω) (hχ₀ ω).symm
      have hm' : 1 < multℚ(χ₀ ω, shift(σ, t + d)) := by
        rw [Complex.ofReal_add, ← (hd σ t).2]
        exact hm
      obtain ⟨N, _, χ_p, hprim, hL⟩ :=
        exists_primitive_finiteHeckeL_eq_of_trivial_on_section τ hτ (χ₀ ω) (hχ₀τ ω)
      have hre : (shift(σ, t + d)).re = σ := by simp
      have hz1 : shift(σ, t + d) ≠ 1 := fun h ↦ by
        have := congrArg Complex.re h
        rw [hre, Complex.one_re] at this
        linarith [hσ.2]
      have hord := (rat_one_lt_mult_iff_one_lt_analyticOrderAt (χ₀ ω) hL
        (by rw [hre]; linarith [hσ.1]) hz1).mp hm'
      simpa only [hre] using hdir N χ_p hprim (shift(σ, t + d)) (by rw [hre]; exact hσ.1)
        (by rw [hre]; exact hσ.2) hord
    refine ((S.finite_toSet.union ((S.image (fun σ : ℝ ↦ 1 - σ)).finite_toSet)).union
      (Finset.finite_toSet ({0, 1 / 2, 1} : Finset ℝ))).subset ?_
    rintro σ ⟨ω, t, hm⟩
    have hIcc : σ ∈ Icc (0 : ℝ) 1 := by
      by_contra hnot
      rw [realZeros_mult_eq_zero_of_not_mem_Icc (F := ℚ) (χ ω) (shift(σ, t))
        (by simpa using hnot)] at hm
      omega
    rcases eq_or_lt_of_le hIcc.1 with rfl | hpos
    · exact Or.inr (Finset.mem_coe.mpr (by simp))
    rcases eq_or_lt_of_le hIcc.2 with rfl | hlt1
    · exact Or.inr (Finset.mem_coe.mpr (by simp))
    rcases lt_trichotomy σ (1 / 2) with hlt | rfl | hgt
    · have hm' : 1 < multℚ((χ ω)⁻¹, shift(1 - σ, (-t : ℝ))) := by
        rwa [← realZeros_mult_reflect (F := ℚ) (χ ω) σ t]
      have h1σ : 1 - σ ∈ Ioo (1 / 2 : ℝ) 1 := ⟨by linarith, by linarith⟩
      exact Or.inl (Or.inr (Finset.mem_coe.mpr (Finset.mem_image.mpr
        ⟨1 - σ, hright (χ ω)⁻¹ (1 - σ) (-t) h1σ hm', by ring⟩)))
    · exact Or.inr (Finset.mem_coe.mpr (by simp))
    · exact Or.inl (Or.inl (hright (χ ω) σ t ⟨hgt, hlt1⟩ hm))

end RationalField

end RiemannMasullo.Isolated
