module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

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

/-- Paper: Lemma B.1.1.1, p. 589. In the open half-plane the vertical growth
order is finite under the uniform polynomial bound.
Deviation: This and the other parts use meromorphic functions in normal form
and omit the unused parameter `b > a`. -/
theorem verticalGrowthOrder_ne_top {σ : ℝ} (hσ : a < σ) :
    verticalGrowthOrder f σ ≠ ⊤ := by sorry

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

/-- Paper: Lemma B.1.1.1, p. 589. On each closed strip inside the half-plane,
the growth order at the real part plus any positive ε gives a uniform exponent. -/
theorem isBigO_verticalGrowthOrder_add (σ₁ σ₂ : ℝ) (h₁ : a < σ₁) (h₂ : σ₁ < σ₂)
    (ε : ℝ) (hε : 0 < ε) :
    f =O[atHeight ⊓ 𝓟 (Complex.re ⁻¹' Icc σ₁ σ₂)]
      fun s ↦ |s.im| ^ ((verticalGrowthOrder f s.re).toReal + ε) := by sorry

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
