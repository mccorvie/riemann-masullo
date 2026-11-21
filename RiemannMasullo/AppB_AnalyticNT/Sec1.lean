module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Convex.Continuous
import RiemannMasullo.ForMathlib.Analysis.Complex.Hadamard

/-!
# Convexity bounds for finite Hecke L-functions

Masullo, §B.1, pp. 588–591. The estimates concern both directions on vertical
lines and are uniform in the real part when stated on a strip.
-/

@[expose] public noncomputable section

open Filter Function NumberField Set
open scoped Asymptotics ENNReal NNReal Topology

namespace RiemannMasullo

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

-- TODO(paper-gap): If the introductory critical-line estimate refers to the
-- finite L-function, its exponent 1/4 + ε omits the degree in (B.1.1.12).

/-- Paper: Equation (B.1.1.2), p. 589. The vertical growth order is the infimum
of the nonnegative exponents that bound the function along `Re(s) = σ`.
Deviation: The infimum takes values in `ℝ≥0∞`, with `⊤` when no polynomial bound exists. -/
def verticalGrowthOrder (f : ℂ → ℂ) (σ : ℝ) : ℝ≥0∞ :=
  sInf ((fun k : ℝ≥0 ↦ (k : ℝ≥0∞)) ''
    {k : ℝ≥0 | f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})] fun s ↦ |s.im| ^ (k : ℝ)})

/-- Paper: Equation (B.1.1.2), p. 589. As a check on the definition, the identity
function has growth order one on every vertical line. -/
theorem verticalGrowthOrder_id (σ : ℝ) : verticalGrowthOrder (id : ℂ → ℂ) σ = 1 := by
  let l := atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ})
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) l atTop := tendsto_inf_left tendsto_comap
  unfold verticalGrowthOrder
  apply le_antisymm
  · refine sInf_le ⟨1, ?_, by simp⟩
    change (id : ℂ → ℂ) =O[l] fun z ↦ |z.im| ^ ((1 : ℝ≥0) : ℝ)
    have hRe : ∀ᶠ z in l, z.re = σ :=
      eventually_inf_principal.mpr (Eventually.of_forall fun _ hz ↦ hz)
    refine Asymptotics.isBigO_iff.mpr ⟨2, ?_⟩
    filter_upwards [hRe, hHeight.eventually_ge_atTop |σ|] with z hre hσz
    simp only [id_eq, NNReal.coe_one, Real.rpow_one, Real.norm_of_nonneg (abs_nonneg _)]
    calc
      ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
      _ ≤ 2 * |z.im| := by
        rw [hre, two_mul]
        exact add_le_add_left hσz _
  · apply le_sInf
    rintro _ ⟨k, hk, rfl⟩
    by_contra! hlt
    have hklt : (k : ℝ) < 1 := by exact_mod_cast hlt
    have hRay : Tendsto (fun t : ℝ ↦ (⟨σ, t⟩ : ℂ)) atTop l := by
      refine tendsto_inf.mpr ⟨tendsto_comap_iff.mpr ?_, tendsto_principal.mpr (by simp)⟩
      exact tendsto_id.congr' <| (eventually_ge_atTop (0 : ℝ)).mono fun t ht ↦
        (abs_of_nonneg ht).symm
    have : NeBot l := hRay.neBot
    change (id : ℂ → ℂ) =O[l] fun z ↦ |z.im| ^ (k : ℝ) at hk
    obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp hk
    have hLarge : ∀ᶠ z in l, C < |z.im| ^ (1 - (k : ℝ)) :=
      ((tendsto_rpow_atTop (sub_pos.mpr hklt)).comp hHeight).eventually_gt_atTop C
    obtain ⟨z, hz, hlarge, hbound⟩ := ((hHeight.eventually_gt_atTop 0).and (hLarge.and hC)).exists
    rw [Real.rpow_sub hz, Real.rpow_one] at hlarge
    rw [id_eq, Real.norm_of_nonneg (Real.rpow_nonneg hz.le _)] at hbound
    exact (not_lt_of_ge ((Complex.abs_im_le_norm z).trans hbound))
      ((lt_div_iff₀ (Real.rpow_pos_of_pos hz _)).mp hlarge)

section GrowthOrder

variable {f : ℂ → ℂ} {a : ℝ}
variable (hf : MeromorphicNFOn f (Complex.re ⁻¹' Ioi a))
  (hFinite : {s : ℂ | a < s.re ∧ meromorphicOrderAt f s < 0}.Finite)
  (hSimple : ∀ s : ℂ, a < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt f s = -1)
  (hGrowth : ∃ ξ : ℝ, 0 < ξ ∧
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a)] fun s ↦ |s.im| ^ ξ)

include hf hFinite hSimple hGrowth

-- Retain the meromorphicity and pole hypotheses in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma B.1.1.1, p. 589. In the open half-plane the vertical growth
order is finite under the uniform polynomial bound.
Deviation: This and the other parts use meromorphic functions in normal form
and omit the unused parameter `b > a`. -/
theorem verticalGrowthOrder_ne_top {σ : ℝ} (hσ : a < σ) :
    verticalGrowthOrder f σ ≠ ⊤ := by
  obtain ⟨ξ, hξ, hBound⟩ := hGrowth
  let k : ℝ≥0 := ⟨ξ, hξ.le⟩
  have hLine : ({σ} : Set ℝ) ⊆ Ioi a := singleton_subset_iff.mpr hσ
  refine lt_top_iff_ne_top.mp (lt_of_le_of_lt ?_ (ENNReal.coe_lt_top (r := k)))
  unfold verticalGrowthOrder
  refine sInf_le ⟨k, ?_, rfl⟩
  exact hBound.mono (inf_le_inf_left _ (principal_mono.mpr (preimage_mono hLine)))

-- TODO(paper-gap): The proof's equality `μ_g = μ + N` fails for `f(s) = 1/s`
-- on `Re(s) > -1`. Clearing its one pole gives `g(s) = 1`, and both orders are zero.

omit hf hFinite hSimple hGrowth in
/-- Simple poles can be removed by factors tending to one at large absolute height.
The resulting holomorphic function has the same asymptotic size on the half-plane. -/
private theorem exists_analyticOnNhd_isTheta_atHeight {f : ℂ → ℂ} {a : ℝ}
    (hf : MeromorphicNFOn f (Complex.re ⁻¹' Ioi a))
    (hFinite : {s : ℂ | a < s.re ∧ meromorphicOrderAt f s < 0}.Finite)
    (hSimple : ∀ s : ℂ, a < s.re → meromorphicOrderAt f s < 0 → meromorphicOrderAt f s = -1) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (Complex.re ⁻¹' Ioi a) ∧
      g =Θ[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a)] f := by
  classical
  let poles := hFinite.toFinset
  let factor (p z : ℂ) := (z - p) / (z - (a : ℂ))
  let multiplier : ℂ → ℂ := ∏ p ∈ poles, factor p
  let product : ℂ → ℂ := multiplier * f
  let U := Complex.re ⁻¹' Ioi a
  have hDen (z : ℂ) (hz : z ∈ U) : z - (a : ℂ) ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hz' : a < z.re := hz
    simp [h] at hz'
  have hFactor (p : ℂ) {z : ℂ} (hz : z ∈ U) : AnalyticAt ℂ (factor p) z :=
    (show AnalyticAt ℂ (fun w : ℂ ↦ w - p) z by fun_prop).div (by fun_prop) (hDen z hz)
  have hMultiplier : AnalyticOnNhd ℂ multiplier U := fun z hz ↦
    Finset.analyticAt_prod _ (fun p _ ↦ hFactor p hz)
  have hProduct : MeromorphicOn product U := fun z hz ↦
    (hMultiplier z hz).meromorphicAt.mul (hf hz).meromorphicAt
  have hOrder (z : ℂ) (hz : z ∈ U) : 0 ≤ meromorphicOrderAt product z := by
    rw [meromorphicOrderAt_mul (hMultiplier z hz).meromorphicAt (hf hz).meromorphicAt]
    by_cases hp : meromorphicOrderAt f z < 0
    · have hmem : z ∈ poles := hFinite.mem_toFinset.mpr ⟨hz, hp⟩
      have hsum : 1 ≤ meromorphicOrderAt multiplier z := by
        change 1 ≤ meromorphicOrderAt (∏ p ∈ poles, factor p) z
        rw [meromorphicOrderAt_prod (fun p _ ↦ (hFactor p hz).meromorphicAt)]
        have hself : meromorphicOrderAt (factor z) z = 1 := by
          have hinv : AnalyticAt ℂ (fun w : ℂ ↦ (w - (a : ℂ))⁻¹) z :=
            (show AnalyticAt ℂ (fun w : ℂ ↦ w - (a : ℂ)) z by fun_prop).inv (hDen z hz)
          have h := meromorphicOrderAt_mul_of_ne_zero (f := fun w ↦ w - z)
            hinv (inv_ne_zero (hDen z hz))
          simpa only [Pi.mul_def, ← div_eq_inv_mul, factor, meromorphicOrderAt_id_sub_const] using h
        rw [← hself]
        exact Finset.single_le_sum (fun p _ ↦ (hFactor p hz).meromorphicOrderAt_nonneg) hmem
      rw [hSimple z hz hp]
      exact (by decide : (0 : WithTop ℤ) ≤ 1 + (-1)).trans (add_le_add_left hsum _)
    · exact add_nonneg (hMultiplier z hz).meromorphicOrderAt_nonneg (le_of_not_gt hp)
  let g := toMeromorphicNFOn product U
  have hg : AnalyticOnNhd ℂ g U := by
    intro z hz
    exact ((meromorphicNFOn_toMeromorphicNFOn product U) hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by simpa only [g, meromorphicOrderAt_toMeromorphicNFOn hProduct hz] using hOrder z hz)
  have hHeight : Tendsto (fun z : ℂ ↦ |z.im|) atHeight atTop := tendsto_comap
  have hNorm : Tendsto (fun z : ℂ ↦ ‖z - (a : ℂ)‖) atHeight atTop :=
    tendsto_atTop_mono (fun z ↦ by simpa using Complex.abs_im_le_norm (z - (a : ℂ))) hHeight
  have hFactorLimit (p : ℂ) : Tendsto (factor p) atHeight (𝓝 1) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hLimit : Tendsto (fun z : ℂ ↦ ‖(a : ℂ) - p‖ * ‖z - (a : ℂ)‖⁻¹)
        atHeight (𝓝 0) := by
      simpa using (tendsto_inv_atTop_zero.comp hNorm).const_mul ‖(a : ℂ) - p‖
    refine hLimit.congr' ?_
    filter_upwards [hNorm.eventually_gt_atTop 0] with z hz
    have hd := norm_pos_iff.mp hz
    have hEq : factor p z - 1 = ((a : ℂ) - p) / (z - (a : ℂ)) := by
      dsimp [factor]
      field_simp
      ring
    rw [hEq, norm_div, div_eq_mul_inv]
  have hLimit : Tendsto multiplier atHeight (𝓝 1) := by
    have h := tendsto_finsetProd poles (a := fun _ ↦ (1 : ℂ)) (fun p _ ↦ hFactorLimit p)
    rw [Finset.prod_const_one] at h
    exact h.congr (fun z ↦ (Finset.prod_apply z poles factor).symm)
  let heightInU := atHeight ⊓ 𝓟 U
  have hEq : g =ᶠ[heightInU] product := by
    have hAvoid : ∀ᶠ z in atHeight, z ∉ poles := by
      have hAvoidEach : ∀ᶠ z in atHeight, ∀ p ∈ poles, z ≠ p := by
        apply (Filter.eventually_all_finset poles).2
        intro p _
        filter_upwards [hHeight.eventually_gt_atTop |p.im|] with z hz
        rintro rfl
        exact (lt_irrefl _ hz)
      exact hAvoidEach.mono fun z hz hp ↦ hz z hp rfl
    change ∀ᶠ z in atHeight ⊓ 𝓟 U, g z = product z
    rw [eventually_inf_principal]
    filter_upwards [hAvoid] with z hz hzU
    have hzNonneg : 0 ≤ meromorphicOrderAt f z :=
      le_of_not_gt (fun hp ↦ hz (hFinite.mem_toFinset.mpr ⟨hzU, hp⟩))
    have hprod : AnalyticAt ℂ product z :=
      (hMultiplier z hzU).mul ((hf hzU).meromorphicOrderAt_nonneg_iff_analyticAt.mp hzNonneg)
    dsimp only [g]
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hProduct hzU,
      toMeromorphicNFAt_eq_self.mpr hprod.meromorphicNFAt]
  have hT : multiplier =Θ[atHeight] (fun _ ↦ (1 : ℂ)) := by
    refine ⟨Asymptotics.isBigO_const_of_tendsto hLimit one_ne_zero, ?_⟩
    refine Asymptotics.IsBigO.of_bound 2 ?_
    have hclose := (tendsto_iff_norm_sub_tendsto_zero.mp hLimit).eventually_lt_const
      (show (0 : ℝ) < 1 / 2 by norm_num)
    filter_upwards [hclose] with z hz
    have H := norm_sub_norm_le (1 : ℂ) (multiplier z)
    rw [norm_sub_rev, norm_one] at H
    rw [norm_one]
    linarith
  refine ⟨g, hg, hEq.isTheta.trans ?_⟩
  have hh := (hT.mono (show heightInU ≤ atHeight from inf_le_left)).mul
    (Asymptotics.isTheta_refl f heightInU)
  exact hh.trans_eventuallyEq (Eventually.of_forall fun z ↦ one_mul (f z))

/-- Paper: Lemma B.1.1.1, p. 589. The finite growth order is convex as a function
of the real part in the open half-plane. -/
theorem convexOn_verticalGrowthOrder :
    ConvexOn ℝ (Ioi a) (fun σ ↦ (verticalGrowthOrder f σ).toReal) := by
  obtain ⟨g, hg, hgf⟩ := exists_analyticOnNhd_isTheta_atHeight hf hFinite hSimple
  obtain ⟨K, hK, hGrowth⟩ := hGrowth
  have line_le_halfPlane {x : ℝ} (hx : a < x) :
      atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x}) ≤ atHeight ⊓ 𝓟 (Complex.re ⁻¹' Ioi a) :=
    inf_le_inf_left _ (Filter.principal_mono.mpr (preimage_mono (singleton_subset_iff.mpr hx)))
  have approx {x ε : ℝ} (hx : a < x) (hε : 0 < ε) :
      ∃ k : ℝ≥0, (k : ℝ) < (verticalGrowthOrder f x).toReal + ε ∧
        f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x})] fun z ↦ |z.im| ^ (k : ℝ) := by
    let k : ℝ≥0 := ⟨K, hK.le⟩
    have hKBound : verticalGrowthOrder f x ≤ (k : ℝ≥0∞) :=
      sInf_le ⟨k, hGrowth.mono (line_le_halfPlane hx), rfl⟩
    have htop : verticalGrowthOrder f x ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.coe_ne_top hKBound
    have hlt : verticalGrowthOrder f x < ENNReal.ofReal ((verticalGrowthOrder f x).toReal + ε) :=
      (ENNReal.lt_ofReal_iff_toReal_lt htop).mpr (lt_add_of_pos_right _ hε)
    unfold verticalGrowthOrder at hlt
    obtain ⟨_, ⟨k, hk, rfl⟩, hlt⟩ := sInf_lt_iff.mp hlt
    exact ⟨k, ENNReal.coe_lt_ofReal.mp hlt, hk⟩
  refine convexOn_iff_pairwise_pos.mpr ⟨convex_Ioi _, ?_⟩
  intro x hx y hy hne p q hp hq hpq
  change (verticalGrowthOrder f (p * x + q * y)).toReal ≤
    p * (verticalGrowthOrder f x).toReal + q * (verticalGrowthOrder f y).toReal
  wlog hxy : x < y generalizing x y p q
  · simpa only [add_comm] using this hy hx hne.symm hq hp (by rwa [add_comm])
      (lt_of_le_of_ne (le_of_not_gt hxy) hne.symm)
  have strip_sub : Complex.re ⁻¹' Icc x y ⊆ Complex.re ⁻¹' Ioi a :=
    fun _ hz ↦ hx.trans_le hz.1
  have hStrip := inf_le_inf_left atHeight (Filter.principal_mono.mpr strip_sub)
  have hInt : a < p * x + q * y := by
    have hx' : a < x := hx
    have hprod : 0 < q * (y - x) := mul_pos hq (sub_pos.mpr hxy)
    nlinarith [congrArg (fun t : ℝ ↦ t * x) hpq]
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨k₀, hk₀, h₀⟩ := approx hx hε
  obtain ⟨k₁, hk₁, h₁⟩ := approx hy hε
  have hInterp := isBigO_rpow_verticalStrip_interpolate hxy hK.le k₀.coe_nonneg k₁.coe_nonneg
    hp.le hq.le hpq (hg.differentiableOn.mono strip_sub)
    ((hgf.mono hStrip).trans_isBigO (hGrowth.mono hStrip))
    ((hgf.mono (line_le_halfPlane hx)).trans_isBigO h₀)
    ((hgf.mono (line_le_halfPlane hy)).trans_isBigO h₁)
  have hBound := (hgf.symm.mono (line_le_halfPlane hInt)).trans_isBigO hInterp
  let k : ℝ≥0 := ⟨p * (k₀ : ℝ) + q * (k₁ : ℝ), by positivity⟩
  have hOrder : verticalGrowthOrder f (p * x + q * y) ≤ (k : ℝ≥0∞) :=
    sInf_le ⟨k, hBound, rfl⟩
  calc
    _ ≤ (k : ℝ) := ENNReal.toReal_mono ENNReal.coe_ne_top hOrder
    _ ≤ p * (verticalGrowthOrder f x).toReal + q * (verticalGrowthOrder f y).toReal + ε := by
      change p * (k₀ : ℝ) + q * (k₁ : ℝ) ≤ _
      nlinarith [mul_le_mul_of_nonneg_left hk₀.le hp.le, mul_le_mul_of_nonneg_left hk₁.le hq.le,
        congrArg (fun t : ℝ ↦ t * ε) hpq]

/-- Paper: Lemma B.1.1.1, p. 589. The finite growth order is continuous in the
open half-plane. -/
theorem continuousOn_verticalGrowthOrder :
    ContinuousOn (fun σ ↦ (verticalGrowthOrder f σ).toReal) (Ioi a) := by sorry

omit hf hFinite hSimple hGrowth

/-- A height bound on a set of real parts is equivalent to a single estimate
past a common height threshold. -/
private theorem isBigO_height_iff {f : ℂ → ℂ} {S : Set ℝ} {p : ℝ → ℝ} :
    (f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' S)] fun z ↦ |z.im| ^ p z.re) ↔
      ∃ C > 0, ∃ T : ℝ, ∀ z : ℂ, z.re ∈ S → T ≤ |z.im| →
        ‖f z‖ ≤ C * |z.im| ^ p z.re := by
  simp only [Asymptotics.isBigO_iff', eventually_inf_principal, eventually_comap, eventually_atTop,
    Function.comp_apply, mem_preimage, Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  constructor
  · rintro ⟨C, hC, T, hT⟩
    exact ⟨C, hC, T, fun z hz h ↦ hT _ h z rfl hz⟩
  · rintro ⟨C, hC, T, hT⟩
    exact ⟨C, hC, T, fun t ht z hz h ↦ hT z h (hz ▸ ht)⟩

/-- A nonnegative affine exponent interpolates the two vertical boundary
bounds on a strip where the function is polynomially bounded and eventually
holomorphic at large absolute height. -/
private theorem isBigO_height_affine {f : ℂ → ℂ} {u v ξ p q : ℝ} (huv : u < v)
    (hξ : 0 ≤ ξ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hAnalytic : ∃ T : ℝ, ∀ z : ℂ, z.re ∈ Icc u v → T ≤ |z.im| →
      AnalyticAt ℂ f z)
    (hGrowth : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc u v)] fun z ↦ |z.im| ^ ξ)
    (hLeft : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {u})] fun z ↦ |z.im| ^ p)
    (hRight : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {v})] fun z ↦ |z.im| ^ q) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc u v)]
      fun z ↦ |z.im| ^ ((1 - (z.re - u) / (v - u)) * p + (z.re - u) / (v - u) * q) := by
  obtain ⟨T, hT⟩ := hAnalytic
  obtain ⟨C₀, hC₀, T₀, hT₀⟩ := (isBigO_height_iff (p := fun _ ↦ ξ)).mp hGrowth
  obtain ⟨C₁, hC₁, T₁, hT₁⟩ := (isBigO_height_iff (p := fun _ ↦ p)).mp hLeft
  obtain ⟨C₂, hC₂, T₂, hT₂⟩ := (isBigO_height_iff (p := fun _ ↦ q)).mp hRight
  let K := max (C₀ * (3 / 2 : ℝ) ^ ξ) (max (C₁ * (3 / 2 : ℝ) ^ p) (C₂ * (3 / 2 : ℝ) ^ q))
  have hK : 0 < K := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  let A : ℂ → ℂ := fun w ↦ (1 - (w - u) / (v - u)) * p + (w - u) / (v - u) * q
  let E : ℝ → ℝ := fun x ↦ (1 - (x - u) / (v - u)) * p + (x - u) / (v - u) * q
  have hA (w : ℂ) : (A w).re = E w.re := by
    simp [A, E, ← Complex.ofReal_sub, Complex.div_ofReal_re, Complex.mul_re]
  have hAu : E u = p := by simp [E]
  have hAv : E v = q := by simp [E, sub_ne_zero.mpr huv.ne']
  have hE {x : ℝ} (hx : x ∈ Icc u v) : 0 ≤ E x := by
    have hθ₀ := div_nonneg (sub_nonneg.mpr hx.1) (sub_nonneg.mpr huv.le)
    have hθ₁ : (x - u) / (v - u) ≤ 1 := by
      rw [div_le_iff₀ (sub_pos.mpr huv), one_mul]
      exact sub_le_sub_right hx.2 _
    exact add_nonneg (mul_nonneg (sub_nonneg.mpr hθ₁) hp) (mul_nonneg hθ₀ hq)
  refine (isBigO_height_iff (p := E)).mpr ⟨K * Real.exp ((v - u) ^ 2), by positivity,
    max 1 (max (4 * ξ) (2 * max (max T T₀) (max T₁ T₂))), ?_⟩
  intro z hz hHeight
  let R := |z.im|
  have hR₁ : 1 ≤ R := (le_max_left _ _).trans hHeight
  have hR : 0 < R := zero_lt_one.trans_le hR₁
  have hRξ : 4 * ξ ≤ R := (le_max_left _ _).trans ((le_max_right _ _).trans hHeight)
  have hRT : max (max T T₀) (max T₁ T₂) ≤ R / 2 := by
    have := (le_max_right _ _).trans ((le_max_right _ _).trans hHeight)
    linarith
  -- The rectangle stays at absolute heights between R / 2 and 3 * R / 2.
  let L := z.im - R / 2
  let U := z.im + R / 2
  have hLU : L < U := by dsimp [L, U]; linarith
  have hHeights {w : ℂ} (hw : w.im ∈ Icc L U) :
      R / 2 ≤ |w.im| ∧ |w.im| ≤ (3 / 2 : ℝ) * R := by
    have hlo : z.im - R / 2 ≤ w.im := hw.1
    have hhi : w.im ≤ z.im + R / 2 := hw.2
    have hclose : |w.im - z.im| ≤ R / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    constructor <;> linarith [abs_sub_abs_le_abs_sub z.im w.im,
      abs_sub_abs_le_abs_sub w.im z.im, abs_sub_comm z.im w.im]
  -- The square in the exponential suppresses the polynomial bound on the horizontal edges.
  let g : ℂ → ℂ := fun w ↦ f w * Complex.exp ((w - z) ^ 2 - A w * (Real.log R : ℂ))
  have hgNorm (w : ℂ) :
      ‖g w‖ = (‖f w‖ * Real.exp (-(w.im - z.im) ^ 2) / R ^ E w.re) *
        Real.exp ((w.re - z.re) ^ 2) := by
    simp only [g, norm_mul, Complex.norm_exp, Complex.sub_re, pow_two, Complex.mul_re,
      Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, hA,
      Real.rpow_def_of_pos hR, div_eq_mul_inv, ← Real.exp_neg, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hg : DiffContOnCl ℂ g (Complex.reProdIm (Ioo u v) (Ioo L U)) := by
    apply DifferentiableOn.diffContOnCl
    rw [Complex.closure_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne]
    intro w hw
    have hw' := Complex.mem_reProdIm.mp hw
    have hfw := hT w hw'.1 ((le_max_left _ _).trans ((le_max_left _ _).trans
      (hRT.trans (hHeights hw'.2).1)))
    have hA' : Differentiable ℂ A := by unfold A; fun_prop
    have hWeight : Differentiable ℂ
        (fun w ↦ Complex.exp ((w - z) ^ 2 - A w * (Real.log R : ℂ))) := by
      fun_prop
    exact (hfw.differentiableAt.mul hWeight.differentiableAt).differentiableWithinAt
  have hPower (w : ℂ) (hw : w.im ∈ Icc L U) {k : ℝ} (hk : 0 ≤ k) :
      |w.im| ^ k ≤ (3 / 2 : ℝ) ^ k * R ^ k := by
    rw [← Real.mul_rpow (by norm_num) hR.le]
    exact Real.rpow_le_rpow (abs_nonneg _) (hHeights hw).2 hk
  have hDamp : R ^ ξ * Real.exp (-(R / 2) ^ 2) ≤ 1 := by
    rw [Real.rpow_def_of_pos hR, ← Real.exp_add, ← Real.exp_zero, Real.exp_le_exp]
    have hlog : Real.log R ≤ R := (Real.log_le_sub_one_of_pos hR).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_right hlog hξ, mul_nonneg (sub_nonneg.mpr hRξ) hR.le]
  have hFront : ∀ w ∈ frontier (Complex.reProdIm (Ioo u v) (Ioo L U)),
      ‖g w‖ ≤ K * Real.exp ((v - u) ^ 2) := by
    intro w hw
    have hw' := frontier_subset_closure hw
    rw [Complex.closure_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne] at hw'
    obtain ⟨hwRe, hwIm⟩ := Complex.mem_reProdIm.mp hw'
    rw [Complex.frontier_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne, frontier_Ioo huv,
      frontier_Ioo hLU] at hw
    rw [hgNorm]
    refine mul_le_mul ?_ ?_ (by positivity) hK.le
    · apply (div_le_iff₀ (Real.rpow_pos_of_pos hR _)).mpr
      rcases hw with hw | hw
      · have hs : w.im = L ∨ w.im = U := hw.2
        have hsq : (w.im - z.im) ^ 2 = (R / 2) ^ 2 := by
          rcases hs with h | h <;> rw [h] <;> dsimp [L, U] <;> ring
        have hBound := hT₀ w hwRe ((le_max_right _ _).trans
          ((le_max_left _ _).trans (hRT.trans (hHeights hwIm).1)))
        rw [hsq]
        calc
          _ ≤ (C₀ * ((3 / 2 : ℝ) ^ ξ * R ^ ξ)) * Real.exp (-(R / 2) ^ 2) :=
            mul_le_mul_of_nonneg_right (hBound.trans
              (mul_le_mul_of_nonneg_left (hPower w hwIm hξ) hC₀.le)) (by positivity)
          _ = (C₀ * (3 / 2 : ℝ) ^ ξ) * (R ^ ξ * Real.exp (-(R / 2) ^ 2)) := by ring
          _ ≤ K := by
            simpa only [mul_one] using mul_le_mul (le_max_left _ _) hDamp (by positivity) hK.le
          _ ≤ K * R ^ E w.re := le_mul_of_one_le_right hK.le
            (Real.one_le_rpow hR₁ (hE hwRe))
      · have hs : w.re = u ∨ w.re = v := hw.1
        have hExp : Real.exp (-(w.im - z.im) ^ 2) ≤ 1 :=
          Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
        have hSide {C k : ℝ} (hC : 0 ≤ C) (hk : 0 ≤ k) (hEk : E w.re = k)
            (hB : ‖f w‖ ≤ C * |w.im| ^ k) (hCK : C * (3 / 2 : ℝ) ^ k ≤ K) :
            ‖f w‖ * Real.exp (-(w.im - z.im) ^ 2) ≤ K * R ^ E w.re := by
          rw [hEk]
          calc
            _ ≤ ‖f w‖ := mul_le_of_le_one_right (norm_nonneg _) hExp
            _ ≤ C * |w.im| ^ k := hB
            _ ≤ C * ((3 / 2 : ℝ) ^ k * R ^ k) :=
              mul_le_mul_of_nonneg_left (hPower w hwIm hk) hC
            _ = (C * (3 / 2 : ℝ) ^ k) * R ^ k := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_right hCK (by positivity)
        rcases hs with h | h
        · exact hSide hC₁.le hp (h ▸ hAu)
            (hT₁ w h ((le_max_left _ _).trans ((le_max_right _ _).trans
              (hRT.trans (hHeights hwIm).1)))) ((le_max_left _ _).trans (le_max_right _ _))
        · exact hSide hC₂.le hq (h ▸ hAv)
            (hT₂ w h ((le_max_right _ _).trans ((le_max_right _ _).trans
              (hRT.trans (hHeights hwIm).1)))) ((le_max_right _ _).trans (le_max_right _ _))
    · apply Real.exp_le_exp.mpr
      have hwidth : |w.re - z.re| ≤ v - u :=
        abs_le.mpr ⟨by linarith [hwRe.1, hz.2], by linarith [hwRe.2, hz.1]⟩
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hwidth 2
  have hz' : z ∈ closure (Complex.reProdIm (Ioo u v) (Ioo L U)) := by
    rw [Complex.closure_reProdIm, closure_Ioo huv.ne, closure_Ioo hLU.ne]
    exact ⟨hz, ⟨by dsimp [L]; linarith, by dsimp [U]; linarith⟩⟩
  have hMax := Complex.norm_le_of_forall_mem_frontier_norm_le
    ((Metric.isBounded_Ioo _ _).reProdIm (Metric.isBounded_Ioo _ _)) hg hFront hz'
  rw [hgNorm, sub_self, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), neg_zero,
    Real.exp_zero, mul_one, mul_one, div_le_iff₀ (Real.rpow_pos_of_pos hR _)] at hMax
  exact hMax

include hf hFinite hSimple hGrowth

/-- Paper: Lemma B.1.1.1, p. 589. On each closed strip inside the half-plane,
the growth order at the real part plus any positive ε gives a uniform exponent. -/
theorem isBigO_verticalGrowthOrder_add (σ₁ σ₂ : ℝ) (h₁ : a < σ₁) (h₂ : σ₁ < σ₂)
    (ε : ℝ) (hε : 0 < ε) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc σ₁ σ₂)]
      fun s ↦ |s.im| ^ ((verticalGrowthOrder f s.re).toReal + ε) := by
  classical
  let μ : ℝ → ℝ := fun x ↦ (verticalGrowthOrder f x).toReal
  have hμ₀ (x : ℝ) : 0 ≤ μ x := ENNReal.toReal_nonneg
  have hμFinite {x : ℝ} (hx : a < x) : verticalGrowthOrder f x ≠ ⊤ :=
    verticalGrowthOrder_ne_top hf hFinite hSimple hGrowth hx
  have hAnalytic : ∃ T : ℝ, ∀ z : ℂ, a < z.re → T ≤ |z.im| → AnalyticAt ℂ f z := by
    obtain ⟨T, hT⟩ := (hFinite.image (fun z ↦ |z.im|)).bddAbove
    refine ⟨T + 1, fun z hz hHeight ↦
      (hf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_⟩
    by_contra! hPole
    have := hT ⟨z, ⟨hz, hPole⟩, rfl⟩
    linarith
  obtain ⟨ξ, hξ, hξBound⟩ := hGrowth
  have hLine {x k : ℝ} (hx : a < x) (hk : μ x < k) :
      f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x})] fun z ↦ |z.im| ^ k := by
    let k' : ℝ≥0 := ⟨k, (lt_of_le_of_lt (hμ₀ x) hk).le⟩
    have hk' : verticalGrowthOrder f x < (k' : ℝ≥0∞) :=
      (ENNReal.toReal_lt_toReal (hμFinite hx) ENNReal.coe_ne_top).mp hk
    rw [verticalGrowthOrder, sInf_lt_iff] at hk'
    obtain ⟨_, ⟨j, hj, rfl⟩, hjk⟩ := hk'
    have hjk' : (j : ℝ) ≤ k := by
      change (j : ℝ) ≤ (k' : ℝ)
      exact NNReal.coe_le_coe.mpr (by simpa only [ENNReal.coe_le_coe] using hjk.le)
    obtain ⟨C, hC, T, hT⟩ := (isBigO_height_iff (p := fun _ ↦ (j : ℝ))).mp hj
    refine (isBigO_height_iff (p := fun _ ↦ k)).mpr
      ⟨C, hC, max T 1, fun z hz hHeight ↦ (hT z hz ((le_max_left _ _).trans hHeight)).trans ?_⟩
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hHeight) hjk') hC.le
  have hInterp {u v δ : ℝ} (hu : a < u) (huv : u < v) (hδ : 0 < δ) :
      f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc u v)]
        fun z ↦ |z.im| ^ ((1 - (z.re - u) / (v - u)) * (μ u + δ) +
          (z.re - u) / (v - u) * (μ v + δ)) := by
    obtain ⟨T, hT⟩ := hAnalytic
    refine isBigO_height_affine huv hξ.le (by linarith [hμ₀ u]) (by linarith [hμ₀ v])
      ⟨T, fun z hz ↦ hT z (hu.trans_le hz.1)⟩ (hξBound.mono ?_)
      (hLine hu (lt_add_of_pos_right _ hδ)) (hLine (hu.trans huv) (lt_add_of_pos_right _ hδ))
    exact inf_le_inf_left _ (principal_mono.mpr (preimage_mono fun _ hx ↦ hu.trans_le hx.1))
  -- Restrict the strip estimate to a single line and let the exponent slack tend to zero.
  have hChord {u v α β : ℝ} (hu : a < u) (huv : u < v) (hα : 0 < α) (hβ : 0 < β)
      (hab : α + β = 1) : μ (α * u + β * v) ≤ α * μ u + β * μ v := by
    let x := α * u + β * v
    have hx : x ∈ Icc u v := (convex_Icc u v) (left_mem_Icc.mpr huv.le)
      (right_mem_Icc.mpr huv.le) hα.le hβ.le hab
    have hθ : (x - u) / (v - u) = β := by
      apply (div_eq_iff (sub_ne_zero.mpr huv.ne')).mpr
      dsimp [x]
      linear_combination u * hab
    apply le_of_forall_pos_le_add
    intro δ hδ
    let k : ℝ≥0 := ⟨α * μ u + β * μ v + δ, by positivity⟩
    have hBound : f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' {x})] fun z ↦ |z.im| ^ (k : ℝ) := by
      have hSub : ({x} : Set ℝ) ⊆ Icc u v := singleton_subset_iff.mpr hx
      have hb := (hInterp hu huv hδ).mono
        (inf_le_inf_left _ (principal_mono.mpr (preimage_mono hSub)))
      refine hb.congr' Filter.EventuallyEq.rfl (eventually_inf_principal.mpr ?_)
      refine Eventually.of_forall fun z hz ↦ ?_
      have hz' : z.re = x := hz
      simp only [hz', hθ]
      congr 1
      change _ = α * μ u + β * μ v + δ
      have hα' : 1 - β = α := by linarith
      rw [hα']
      have hδsum : (α + β) * δ = δ := by rw [hab, one_mul]
      linear_combination hδsum
    exact (ENNReal.toReal_le_toReal (hμFinite (hu.trans_le hx.1)) ENNReal.coe_ne_top).mpr
      (sInf_le ⟨k, hBound, rfl⟩)
  have hConvex : ConvexOn ℝ (Ioi a) μ := by
    refine convexOn_iff_pairwise_pos.mpr ⟨convex_Ioi _, ?_⟩
    intro u hu v hv huv α β hα hβ hab
    simp only [smul_eq_mul]
    rcases lt_or_gt_of_ne huv with h | h
    · exact hChord hu h hα hβ hab
    · simpa only [add_comm] using hChord hv h hβ hα (by rwa [add_comm])
  have hCont := hConvex.continuousOn isOpen_Ioi
  -- On a small interval, both endpoint orders are close to the order at any interior point.
  let S := Icc σ₁ σ₂
  have hLocal (x : S) : ∃ r > 0, ∃ C > 0, ∃ T : ℝ, ∀ z : ℂ,
      z.re ∈ Metric.ball (x : ℝ) r → T ≤ |z.im| →
        ‖f z‖ ≤ C * |z.im| ^ (μ z.re + ε) := by
    have hx : a < (x : ℝ) := h₁.trans_le x.property.1
    have hAt := (hCont (x : ℝ) hx).continuousAt (Ioi_mem_nhds hx)
    obtain ⟨d, hd, hNear⟩ := Metric.continuousAt_iff.mp hAt (ε / 4) (by positivity)
    let r := min (d / 2) (((x : ℝ) - a) / 2)
    have hr : 0 < r := lt_min (by positivity) (by linarith)
    let u := (x : ℝ) - r
    let v := (x : ℝ) + r
    have hu : a < u := by
      have := min_le_right (d / 2) (((x : ℝ) - a) / 2)
      dsimp [u]
      linarith
    have huv : u < v := by dsimp [u, v]; linarith
    have hNear' {y : ℝ} (hy : y ∈ Icc u v) : |μ y - μ (x : ℝ)| < ε / 4 := by
      apply hNear
      rw [Real.dist_eq]
      have hDy : |y - (x : ℝ)| ≤ r := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
      exact hDy.trans_lt ((min_le_left _ _).trans_lt (by linarith))
    obtain ⟨C, hC, T, hT⟩ := (isBigO_height_iff (p := fun y ↦
      (1 - (y - u) / (v - u)) * (μ u + ε / 4) +
        (y - u) / (v - u) * (μ v + ε / 4))).mp (hInterp hu huv (by positivity))
    refine ⟨r, hr, C, hC, max T 1, fun z hz hHeight ↦ ?_⟩
    have hz' : z.re ∈ Icc u v := Ioo_subset_Icc_self (by rwa [Real.ball_eq_Ioo] at hz)
    have hNearLeft := (abs_lt.mp (hNear' (left_mem_Icc.mpr huv.le))).2
    have hNearRight := (abs_lt.mp (hNear' (right_mem_Icc.mpr huv.le))).2
    have hNearPoint := (abs_lt.mp (hNear' hz')).1
    let t := (z.re - u) / (v - u)
    have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hz'.1) (sub_nonneg.mpr huv.le)
    have ht' : t ≤ 1 := by
      dsimp [t]
      rw [div_le_iff₀ (sub_pos.mpr huv), one_mul]
      exact sub_le_sub_right hz'.2 _
    have hExponent : (1 - t) * (μ u + ε / 4) + t * (μ v + ε / 4) ≤ μ z.re + ε := by
      calc
        _ ≤ (1 - t) * (μ z.re + ε) + t * (μ z.re + ε) := add_le_add
          (mul_le_mul_of_nonneg_left (by linarith) (sub_nonneg.mpr ht'))
          (mul_le_mul_of_nonneg_left (by linarith) ht)
        _ = _ := by ring
    exact (hT z hz' ((le_max_left _ _).trans hHeight)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le ((le_max_right _ _).trans hHeight) hExponent) hC.le)
  choose r hr C hC T hT using hLocal
  obtain ⟨J, hJ⟩ := (isCompact_Icc (a := σ₁) (b := σ₂)).elim_finite_subcover
    (fun x : S ↦ Metric.ball (x : ℝ) (r x)) (fun _ ↦ Metric.isOpen_ball)
    (fun x hx ↦ mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hr ⟨x, hx⟩)⟩)
  obtain ⟨C', hC'⟩ := (J.finite_toSet.image C).bddAbove
  obtain ⟨T', hT'⟩ := (J.finite_toSet.image T).bddAbove
  obtain ⟨x₀, hx₀, _⟩ := mem_iUnion₂.mp (hJ (left_mem_Icc.mpr h₂.le))
  refine (isBigO_height_iff (p := fun x ↦ μ x + ε)).mpr
    ⟨C', (hC x₀).trans_le (hC' ⟨x₀, hx₀, rfl⟩), T', fun z hz hHeight ↦ ?_⟩
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.mp (hJ hz)
  exact (hT x z hzx ((hT' ⟨x, hx, rfl⟩).trans hHeight)).trans
    (mul_le_mul_of_nonneg_right (hC' ⟨x, hx, rfl⟩) (Real.rpow_nonneg (abs_nonneg _) _))

end GrowthOrder

section Hecke

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

-- TODO(paper-gap): In Lemma B.1.1.2 the exponent must be allowed to depend on
-- the strip. For ζ on each line σ < 0 the growth order is 1/2 - σ.

/-- Paper: Lemma B.1.1.2, p. 590. The finite L-function of a unitary Hecke
character grows at most polynomially on each fixed closed vertical strip.
Deviation: `M` is chosen after the strip endpoints, as required even for ζ. -/
theorem finiteHeckeL_continuation_isBigO_rpow (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (a b : ℝ) (hab : a < b) :
    ∃ M : ℝ, 0 < M ∧ L =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)] fun s ↦ |s.im| ^ M := by
  sorry

/-- Paper: Equation (B.1.1.10), p. 590. The reflection factor in the functional
equation satisfies the stated power bound on every fixed closed vertical strip. -/
theorem finiteHeckeReflectionFactor_isBigO_on_strip (χ : U[F]) (L Ldual ε : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (hLdual : MeromorphicNFOn Ldual univ)
    (hDualSeries : ∀ s : halfPlane, Ldual s = finiteHeckeL χ⁻¹ s)
    (hε : Differentiable ℂ ε) (hεNe : ∀ s, ε s ≠ 0)
    (hEq : L =ᶠ[codiscreteWithin univ]
      (fun s ↦ finiteHeckeReflectionFactor χ ε s * Ldual (1 - s)))
    (a b : ℝ) (hab : a < b) :
    finiteHeckeReflectionFactor χ ε =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc a b)]
      fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * (1 / 2 - s.re)) := by sorry

-- TODO(paper-gap): After (B.1.1.11), the displayed multiplier is called entire
-- and zero-free. For F = ℚ and χ trivial, its gamma quotient has a pole at 1
-- and a zero at 0. The explicit conductor normalization also needs an ideal conductor API.

/-- Paper: Proposition B.1.1.3, p. 591. On the closed critical strip the
convexity bound has a common constant for all positive ε and all real parts.
The height from which the estimate holds may depend on ε. -/
theorem finiteHeckeL_continuation_convexity_bound (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    ∃ C : ℝ, 0 < C ∧ ∀ ε > (0 : ℝ),
      Asymptotics.IsBigOWith C (atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc (0 : ℝ) 1)) L
        (fun s ↦ |s.im| ^ ((Module.finrank ℚ F : ℝ) * ((1 - s.re) / 2) + ε)) := by sorry

-- TODO(paper-gap): Footnote 2 asks for a bound on [-1, 2] without specifying
-- an exponent there. The exponent in (B.1.1.12) fails at σ = -1 even for ζ.
-- TODO(paper-gap): The bound on the dual L-factor gives an upper bound by
-- the reflection factor on fixed left-hand lines. The printed asymptotic
-- equivalence would require the dual L-factor to tend to one in absolute value.
-- TODO(paper-gap): In (B.1.1.14), the bounds on μ at 0 and 1 give an inequality
-- for the interpolation term. The printed equality needs a separate argument.

/-- Paper: Remark B.1.1.4, p. 591. On each fixed vertical line the continued
finite L-function is eventually holomorphic, and each of its holomorphic
derivatives grows at most polynomially as the absolute height tends to infinity. -/
theorem finiteHeckeL_continuation_iteratedDeriv_isBigO_rpow (χ : U[F]) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (k : ℕ) (σ : ℝ) :
    ∃ M C : ℝ, 0 < M ∧ 0 < C ∧
      ∀ᶠ s in atHeight ⊓ 𝓟 (Complex.re ⁻¹' {σ}),
        AnalyticAt ℂ L s ∧ ‖iteratedDeriv k L s‖ ≤ C * |s.im| ^ M := by sorry

-- TODO(paper-gap): Footnotes 3 and 4 leave the intended uniform derivative
-- bounds on strips open. Proposition 3.3.1.5 is stated on fixed lines with σ > 0.

end Hecke

end RiemannMasullo
