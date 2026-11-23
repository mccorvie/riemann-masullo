module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
public import RiemannMasullo.Ch06_LocalGlobal.Sec2

import all RiemannMasullo.Ch05_ThetaZSpaces.Sec1
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a

/-!
# §7.2 Poles of the S-idelic zeta functions

The finite set `S` lists the finite places. Every archimedean place is included.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set Topology
open scoped BigOperators NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Places" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "ℬ𝔽" => SchwartzBruhat (Multiplicative (𝔸[F]))
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "m𝔽" => ideleClassNorm F
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "J₁" => (mₛ).ker
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ
local notation "dualₛ" => dualQuasiCharacter (G := Jₛ) mₛ hmₛ
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "onComponent(" c ", " ω ")" =>
  (normOneRestriction mₛ c = (circleToComplex).comp ω)
local notation "Θₛ(" ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "coeff(" c ", " k ")" => (fun f : ℬₛ ↦ sLocalZLaurentCoeff f c (-(k : ℤ)))

-- TODO(paper-gap): The inclusions in (7.2.0.1)–(7.2.0.2) require an effective divisor.
-- This section uses the earlier meromorphic model on the character components.
-- TODO(paper-gap): (7.2.1.3)–(7.2.1.5) repeat the asymptotic expansion with
-- the missing constant term and repeated poles of Theorem 7.1.2.3. Use its
-- pole-free contour cutoff and the corrected complex pole family in §7.1.
-- At finite places the periodic lattice occurs only for unramified characters.
-- TODO(paper-gap): In (7.2.1.8) the contour needs positive orientation and
-- must isolate the chosen pole. The coefficient uses the small-circle residue of §B.3.

/-- On a small punctured disc in the centered norm-twist chart every quasi-character is regular
for the correcting factor, and the chart is continuous on the disc. -/
private theorem sLocalZLaurentCoeff_continuous_linear_disc (c : Xₛ) :
    ∃ R > (0 : ℝ), (∀ z : ℂ, z ≠ 0 → ‖z‖ < R → 0 ≤ sLocalIdelicOrderBound (twistₛ c z)) ∧
      ContinuousOn (fun z : ℂ ↦ twistₛ c z) (Metric.ball 0 R) := by
  obtain ⟨χ, a, hca⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  let ρ : ℂ → ℂ := fun w ↦ sLocalRhoFactor (twistₛ c w)
  have hρ : ρ = (fun s ↦ sLocalRhoFactor (twistₛ ((circleToComplex).comp χ) s)) ∘
      (fun t ↦ t + a) := by
    funext w
    change sLocalRhoFactor (twistₛ c w) = sLocalRhoFactor (twistₛ ((circleToComplex).comp χ) (w + a))
    rw [← hca, normTwist_normTwist]
  have hmer : MeromorphicAt ρ 0 := by
    have hm := sLocalRhoFactor_meromorphic (F := F) (S := S) χ
    have h2 := (hm (0 + a)).comp_analyticAt (g := fun t : ℂ ↦ t + a) (x := 0) (by fun_prop)
    rw [hρ]
    exact h2
  obtain ⟨ε₁, hε₁, h₁⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hmer.eventually_analyticAt
  obtain ⟨e, hc, he, hinv⟩ := sIdeleQuotient_hasNormTwistCharts F S c
  have h0 : (0 : ℂ) ∈ e.target := he ▸ e.map_source hc
  obtain ⟨ε₂, hε₂, h₂⟩ := Metric.isOpen_iff.mp e.open_target 0 h0
  have heq (z : ℂ) (hz : z ∈ e.target) : e.symm z = twistₛ c z :=
    ContinuousMonoidHom.ext fun g ↦ hinv z hz g
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, fun z hz0 hz ↦ ?_, ?_⟩
  · have hA : AnalyticAt ℂ ρ z :=
      h₁ ⟨mem_ball_zero_iff.mpr (hz.trans_le (min_le_left _ _)), hz0⟩
    have e2 : (fun w ↦ sLocalRhoFactor (twistₛ (twistₛ c z) w)) = ρ ∘ (fun w ↦ w + z) := by
      funext w
      exact congrArg sLocalRhoFactor (normTwist_normTwist mₛ hmₛ c z w)
    have hA' : AnalyticAt ℂ (fun w ↦ sLocalRhoFactor (twistₛ (twistₛ c z) w)) 0 := by
      rw [e2]
      exact hA.comp_of_eq (by fun_prop) (zero_add z)
    exact le_min le_rfl hA'.meromorphicOrderAt_nonneg
  · have hsub : Metric.ball (0 : ℂ) (min ε₁ ε₂) ⊆ e.target := fun z hz ↦
      h₂ (Metric.ball_subset_ball (min_le_right _ _) hz)
    exact (e.continuousOn_symm.mono hsub).congr fun z hz ↦ (heq z (hsub hz)).symm

/-- At a regular point of the centered chart, the zeta germ of a test is analytic. -/
private theorem sLocalZLaurentCoeff_continuous_linear_analytic (f : ℬₛ) (c : Xₛ) (z : ℂ)
    (hz : 0 ≤ sLocalIdelicOrderBound (twistₛ c z)) :
    AnalyticAt ℂ (fun w ↦ sLocalIdelicZFunction f (twistₛ c w)) z := by
  have h := (sLocalZ_centered f (twistₛ c z)).2.2 hz
  have e : (fun w ↦ sLocalIdelicZFunction f (twistₛ c w)) =
      (fun w ↦ sLocalIdelicZFunction f (twistₛ (twistₛ c z) w)) ∘ (fun w ↦ w - z) := by
    funext w
    change sLocalIdelicZFunction f (twistₛ c w) =
      sLocalIdelicZFunction f (twistₛ (twistₛ c z) (w - z))
    rw [normTwist_normTwist, sub_add_cancel]
  rw [e]
  exact h.comp_of_eq (by fun_prop) (sub_self z)

/-- For a function analytic on a punctured disc, the residue at the center is the normalized
integral over any circle inside the disc. -/
private theorem sLocalZLaurentCoeff_continuous_linear_circle {g : ℂ → ℂ} {R r : ℝ}
    (hr : 0 < r) (hrR : r < R) (hg : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ g z) :
    complexResidue g 0 = circleIntegral g 0 r / (2 * (Real.pi : ℂ) * Complex.I) := by
  have key (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < R) :
      circleIntegral g 0 b = circleIntegral g 0 a := by
    refine Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable ha hab
      Set.countable_empty (fun z hz ↦ ?_) (fun z hz ↦ ?_)
    · have hz1 : ‖z‖ ≤ b := mem_closedBall_zero_iff.mp hz.1
      have hz2 : a ≤ ‖z‖ := not_lt.mp fun h ↦ hz.2 (mem_ball_zero_iff.mpr h)
      have hz0 : z ≠ 0 := fun h ↦ by rw [h, norm_zero] at hz2; linarith
      exact (hg z hz0 (hz1.trans_lt hb)).continuousAt.continuousWithinAt
    · have hz1 : ‖z‖ < b := mem_ball_zero_iff.mp hz.1.1
      have hz2 : a < ‖z‖ := not_le.mp fun h ↦ hz.1.2 (mem_closedBall_zero_iff.mpr h)
      have hz0 : z ≠ 0 := fun h ↦ by rw [h, norm_zero] at hz2; linarith
      exact (hg z hz0 (hz1.trans hb)).differentiableAt
  unfold complexResidue
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [Ioo_mem_nhdsGT (hr.trans hrR)] with s hs
  congr 1
  rcases le_total r s with h | h
  · exact (key r s hr h hs.2).symm
  · exact key s r hs.1 h hrR

/-- A fixed additive, homogeneous and continuous functional, applied after a continuous linear
map and divided by a constant, is continuous and linear. -/
private theorem sLocalZLaurentCoeff_continuous_linear_abstract {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [TopologicalSpace V] [AddCommGroup W] [Module ℂ W]
    [TopologicalSpace W] (M : V →ₗ[ℂ] W) (hM : Continuous M) (Φ : W → ℂ) (hΦ : Continuous Φ)
    (hadd : ∀ u v, Φ (u + v) = Φ u + Φ v) (hsmul : ∀ (b : ℂ) u, Φ (b • u) = b * Φ u) (K : ℂ)
    (a : V → ℂ) (h : ∀ f, a f = Φ (M f) / K) : Continuous a ∧ IsLinearMap ℂ a := by
  refine ⟨?_, ⟨fun f g ↦ ?_, fun b f ↦ ?_⟩⟩
  · rw [show a = fun f ↦ Φ (M f) / K from funext h]
    exact (hΦ.comp hM).div_const K
  · rw [h, h, h, map_add, hadd, add_div]
  · rw [h, h, map_smul, hsmul, smul_eq_mul, mul_div_assoc]

/-- Paper: Theorem 7.2.1.1(1), p. 334.
Taking a Laurent coefficient in the centered chart is continuous and complex linear.
Deviation: Integer exponents cover both the nonnegative indices of Definition 7.1.2.1
and the polar coefficients extracted by (7.2.1.8). -/
theorem sLocalZLaurentCoeff_continuous_linear (c : Xₛ) (j : ℤ) :
    let a := fun f : ℬₛ ↦ sLocalZLaurentCoeff f c j
    Continuous a ∧ IsLinearMap ℂ a := by
  intro a
  obtain ⟨R, hR, hreg, hcont⟩ := sLocalZLaurentCoeff_continuous_linear_disc (F := F) (S := S) c
  have hr : 0 < R / 2 := by positivity
  have hrR : R / 2 < R := by linarith
  have hθ (θ : ℝ) : circleMap 0 (R / 2) θ ≠ 0 := circleMap_ne_center hr.ne'
  have hθR (θ : ℝ) : ‖circleMap 0 (R / 2) θ‖ < R := by
    rw [norm_circleMap_zero, abs_of_pos hr]
    exact hrR
  let γ : C(ℝ, {d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}) :=
    ⟨fun θ ↦ ⟨twistₛ c (circleMap 0 (R / 2) θ), hreg _ (hθ θ) (hθR θ)⟩,
      (hcont.comp_continuous (continuous_circleMap 0 (R / 2))
        fun θ ↦ mem_ball_zero_iff.mpr (hθR θ)).subtype_mk _⟩
  let k : ℝ → ℂ := fun θ ↦ circleMap 0 (R / 2) θ * Complex.I / circleMap 0 (R / 2) θ ^ (j + 1)
  have hk : Continuous k :=
    ((continuous_circleMap 0 (R / 2)).mul continuous_const).div
      ((continuous_circleMap 0 (R / 2)).zpow₀ (j + 1) fun θ ↦ Or.inl (hθ θ))
      fun θ ↦ zpow_ne_zero _ (hθ θ)
  let Φ : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ) → ℂ :=
    fun u ↦ ∫ θ in (0 : ℝ)..2 * Real.pi, k θ * u (γ θ)
  have hi (u : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ)) :
      IntervalIntegrable (fun θ ↦ k θ * u (γ θ)) MeasureTheory.volume 0 (2 * Real.pi) :=
    (hk.mul (u.continuous.comp γ.continuous)).intervalIntegrable _ _
  have hΦc : Continuous Φ := by
    have h2 : Continuous (fun p : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ) × ℝ ↦
        k p.2 * (p.1.comp γ) p.2) :=
      (hk.comp continuous_snd).mul (continuous_eval.comp
        (((ContinuousMap.continuous_precomp γ).comp continuous_fst).prodMk continuous_snd))
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (u : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ)) (θ : ℝ) ↦ k θ * (u.comp γ) θ)
      h2 0 (2 * Real.pi)
  have hΦadd (u v : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ)) :
      Φ (u + v) = Φ u + Φ v := by
    simp only [Φ, ContinuousMap.add_apply, mul_add]
    exact intervalIntegral.integral_add (hi u) (hi v)
  have hΦsmul (b : ℂ) (u : C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ)) :
      Φ (b • u) = b * Φ u := by
    simp only [Φ, ContinuousMap.smul_apply, smul_eq_mul, mul_left_comm (k _)]
    exact intervalIntegral.integral_const_mul b _
  have hformula (f : ℬₛ) :
      a f = Φ (sLocalIdelicMellin (F := F) (S := S) f).val / (2 * (Real.pi : ℂ) * Complex.I) := by
    change sLocalZLaurentCoeff f c j = _
    unfold sLocalZLaurentCoeff
    rw [sLocalZLaurentCoeff_continuous_linear_circle
      (g := fun z ↦ sLocalIdelicZFunction f (twistₛ c z) / z ^ (j + 1)) hr hrR fun z hz0 hzR ↦
      (sLocalZLaurentCoeff_continuous_linear_analytic f c z (hreg z hz0 hzR)).div
        (analyticAt_id.zpow hz0) (zpow_ne_zero _ hz0)]
    congr 1
    unfold circleIntegral
    refine intervalIntegral.integral_congr fun θ _ ↦ ?_
    change deriv (circleMap 0 (R / 2)) θ • (sLocalIdelicZFunction f
        (twistₛ c (circleMap 0 (R / 2) θ)) / circleMap 0 (R / 2) θ ^ (j + 1)) =
      k θ * sLocalIdelicZFunction f (twistₛ c (circleMap 0 (R / 2) θ))
    generalize sLocalIdelicZFunction f (twistₛ c (circleMap 0 (R / 2) θ)) = Y
    rw [deriv_circleMap, smul_eq_mul]
    simp only [k, zero_add]
    ring
  have hM : Continuous (fun f : ℬₛ ↦ ((sLocalIdelicMellin (F := F) (S := S) f) :
      C({d : Xₛ // 0 ≤ sLocalIdelicOrderBound d}, ℂ))) :=
    sLocalIdelicMellin_continuous.subtype_val
  exact sLocalZLaurentCoeff_continuous_linear_abstract
    ((Submodule.subtype _).comp (sLocalIdelicMellin (F := F) (S := S))) hM Φ hΦc hΦadd hΦsmul
    _ a hformula

/-- Paper: Theorem 7.2.1.1(1), p. 334.
Each Laurent coefficient of nonpositive exponent depends continuously and complex
linearly on the S-adelic test.
Deviation: The coefficient indexed by `k` here has exponent `-k`, as required by
the principal part formula and the Laurent convention of Definition 7.1.2.1. -/
theorem sLocalPrincipalPartCoeff_continuous_linear (c : Xₛ) (k : ℕ) :
    Continuous coeff(c, k) ∧ IsLinearMap ℂ coeff(c, k) :=
  sLocalZLaurentCoeff_continuous_linear c (-(k : ℤ))

/-- Paper: Theorem 7.2.1.1(1)–(2), p. 334.
The coefficient of exponent `-k` is a continuous linear functional on the test space. -/
def sLocalPrincipalPartCoeff (c : Xₛ) (k : ℕ) : StrongDual ℂ ℬₛ :=
  ⟨(sLocalPrincipalPartCoeff_continuous_linear c k).2.mk' coeff(c, k),
    (sLocalPrincipalPartCoeff_continuous_linear c k).1⟩

/-- Paper: Theorem 7.2.1.1(1), p. 334.
The bundled functional evaluates to the coefficient of the Laurent power `-k`. -/
theorem sLocalPrincipalPartCoeff_apply (c : Xₛ) (k : ℕ) (f : ℬₛ) :
    sLocalPrincipalPartCoeff c k f = sLocalZLaurentCoeff f c (-(k : ℤ)) := rfl

-- TODO(paper-gap): In Theorem 7.2.1.1(2), lower coefficients at a multiple
-- pole mix with higher ones under translation. The leading coefficient has
-- the claimed weight, as stated in Theorem 7.2.1.4(1).

/-- Paper: Theorem 7.2.1.1(2), p. 334.
The coefficient annihilates the kernel of homogeneous theta on the component
of its center. This gives continuous descent through both theta quotients.
Deviation: The weight equation for the leading coefficient is stated in
Theorem 7.2.1.4(1). -/
theorem sLocalPrincipalPartCoeff_ker (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (k : ℕ) :
    Kₛ(ω) ≤ (sLocalPrincipalPartCoeff c k).ker := by
  have residue (Z : ℂ → ℂ) (p : ℤ) (hZ : ∀ z, Z z = 0) :
      complexResidue (fun z : ℂ ↦ Z z / z ^ p) 0 = 0 := by
    simp [hZ, complexResidue, circleIntegral]
    exact tendsto_const_nhds.limUnder_eq
  intro f hf
  have hv := (mem_sLocalHomogeneousAdelicTheta_ker_iff (F := F) (S := S) ω f).mp hf
  refine (exists_sLocalNormTwist (F := F) (S := S) c).elim fun χ ha ↦ ha.elim fun a hca ↦ ?_
  let χ₀ : Xₛ := (circleToComplex).comp χ
  have hω := (congrArg (normOneRestriction mₛ) hca).trans hc
  have hr (z : ℂ) (g : J₁) : normOneRestriction mₛ (twistₛ χ₀ z) g = (ω g : ℂ) :=
    (normOneRestriction_unitaryChart mₛ hmₛ χ z g).trans
      ((normOneRestriction_unitaryChart mₛ hmₛ χ a g).symm.trans (DFunLike.congr_fun hω g))
  have hz : (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ χ₀ z)) = 0 := by
    refine eq_of_agree_rightHalf (sLocalIdelicZFunction_meromorphic f χ)
      (fun _ _ ↦ analyticAt_const.meromorphicNFAt) 0 fun z hz ↦ ?_
    let d := (⟨twistₛ χ₀ z, sLocalOrderBound_positive χ hz⟩ :
      {q : Xₛ // 0 ≤ sLocalIdelicOrderBound q})
    exact (sLocalIdelicMellin_apply f d).symm.trans (hv d (hr z))
  change complexResidue (fun z : ℂ ↦
    sLocalIdelicZFunction f (twistₛ c z) / z ^ (-(k : ℤ) + 1)) 0 = 0
  apply residue
  intro z
  have shift := (congrArg (fun b : Xₛ ↦ twistₛ b z) hca.symm).trans
    (normTwist_normTwist mₛ hmₛ χ₀ a z)
  exact (congrArg (sLocalIdelicZFunction f) shift).trans (congrFun hz (z + a))

/-- Paper: Theorem 7.2.1.1(2), p. 334.
The coefficient acts on the homogeneous theta quotient of its norm-one character. -/
def sLocalThetaPrincipalPartCoeff (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (k : ℕ) : StrongDual ℂ (Θₛ(ω)) :=
  (Kₛ(ω)).liftQL (sLocalPrincipalPartCoeff c k) (sLocalPrincipalPartCoeff_ker ω c hc k)

/-- Paper: Theorem 7.2.1.1(2), p. 334.
The descended coefficient recovers the original coefficient on a test representative. -/
theorem sLocalThetaPrincipalPartCoeff_mk (ω : PontryaginDual J₁) (c : Xₛ)
    (hc : onComponent(c, ω)) (k : ℕ) (f : ℬₛ) :
    sLocalThetaPrincipalPartCoeff ω c hc k ((Kₛ(ω)).mkQL f) =
      sLocalZLaurentCoeff f c (-(k : ℤ)) := rfl

/-- Residues at `0` only depend on the germ on a punctured neighbourhood. -/
private theorem sLocalPrincipalPartCoeff_translate_congr {g h : ℂ → ℂ}
    (he : g =ᶠ[𝓝[≠] (0 : ℂ)] h) : complexResidue g 0 = complexResidue h 0 := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
  · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
    exact hr.2
  · rintro rfl
    exact hr.1.ne (by simpa using hz)

/-- A germ agreeing off `0` with a function analytic at `0` has residue zero there. -/
private theorem sLocalPrincipalPartCoeff_translate_residue_zero {W H : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (he : W =ᶠ[𝓝[≠] (0 : ℂ)] H) : complexResidue W 0 = 0 := by
  have he' : W =ᶠ[𝓝[≠] (0 : ℂ)] (fun z ↦ (z * H z) / (z - 0)) := by
    filter_upwards [he, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, mul_div_cancel_left₀ _ hz0']
  rw [sLocalPrincipalPartCoeff_translate_congr he',
    complexResidue_div_sub (g := fun z ↦ z * H z) (analyticAt_id.mul hH), zero_mul]

/-- For functions analytic on a common punctured disc, the residue at the center is additive
and commutes with constant factors. -/
private theorem sLocalPrincipalPartCoeff_translate_add {F G : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ F z)
    (hG : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ G z) (C : ℂ) :
    complexResidue (fun z ↦ C * F z + G z) 0 = C * complexResidue F 0 + complexResidue G 0 := by
  have hr : 0 < R / 2 := by positivity
  have hrR : R / 2 < R := by linarith
  have hc (H : ℂ → ℂ) (hH : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ H z) :
      CircleIntegrable H 0 (R / 2) := by
    refine ContinuousOn.circleIntegrable hr.le fun z hz ↦ ?_
    have hz' : ‖z‖ = R / 2 := mem_sphere_zero_iff_norm.mp hz
    have hz0 : z ≠ 0 := fun h ↦ by rw [h, norm_zero] at hz'; linarith
    exact (hH z hz0 (by rw [hz']; exact hrR)).continuousAt.continuousWithinAt
  have hCF : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ (fun z ↦ C * F z) z :=
    fun z h0 h ↦ analyticAt_const.mul (hF z h0 h)
  rw [sLocalZLaurentCoeff_continuous_linear_circle (g := fun z ↦ C * F z + G z) hr hrR
      fun z h0 h ↦ (hCF z h0 h).add (hG z h0 h),
    sLocalZLaurentCoeff_continuous_linear_circle hr hrR hF,
    sLocalZLaurentCoeff_continuous_linear_circle hr hrR hG,
    circleIntegral.integral_add (hc _ hCF) (hc G hG), circleIntegral.integral_const_mul]
  ring

/-- For functions analytic on a common punctured disc, the residue at the center of a finite
linear combination is the linear combination of the residues. -/
private theorem sLocalPrincipalPartCoeff_translate_sum (n : ℕ) (C : ℕ → ℂ) (G : ℕ → ℂ → ℂ)
    {R : ℝ} (hR : 0 < R) (hG : ∀ j, ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ (G j) z) :
    complexResidue (fun z ↦ ∑ j ∈ Finset.range n, C j * G j z) 0 =
      ∑ j ∈ Finset.range n, C j * complexResidue (G j) 0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty]
    exact sLocalPrincipalPartCoeff_translate_residue_zero (H := fun _ ↦ 0) analyticAt_const
      Filter.EventuallyEq.rfl
  | succ n ih =>
    have hS : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R →
        AnalyticAt ℂ (fun z ↦ ∑ j ∈ Finset.range n, C j * G j z) z := fun z h0 h ↦ by
      have := Finset.analyticAt_sum (Finset.range n) (f := fun j z ↦ C j * G j z) (c := z)
        fun j _ ↦ analyticAt_const.mul (hG j z h0 h)
      convert this using 1
      funext w
      rw [Finset.sum_apply]
    simp only [Finset.sum_range_succ]
    have e : (fun z ↦ ∑ j ∈ Finset.range n, C j * G j z + C n * G n z) =
        fun z ↦ C n * G n z + ∑ j ∈ Finset.range n, C j * G j z := funext fun z ↦ add_comm _ _
    rw [e, sLocalPrincipalPartCoeff_translate_add hR (hG n) hS, ih, add_comm]

/-- The derivatives at `0` of a polynomial `∑ c j * z ^ j` recover its coefficients. -/
private theorem sLocalPrincipalPartCoeff_translate_poly (c : ℕ → ℂ) (n i : ℕ) :
    iteratedDeriv i (fun z : ℂ ↦ ∑ j ∈ Finset.range n, c j * z ^ j) 0 =
      if i < n then c i * (i.factorial : ℂ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : (fun z : ℂ ↦ ∑ j ∈ Finset.range (n + 1), c j * z ^ j) =
        (fun z : ℂ ↦ ∑ j ∈ Finset.range n, c j * z ^ j) + (fun z : ℂ ↦ c n * z ^ n) := by
      funext z
      simp [Finset.sum_range_succ]
    rw [e, iteratedDeriv_add (by fun_prop) (by fun_prop), ih,
      iteratedDeriv_const_mul _ (by fun_prop), iteratedDeriv_pow]
    rcases lt_trichotomy i n with h | rfl | h
    · rw [if_pos h, if_pos (by omega), zero_pow (by omega), mul_zero, mul_zero, add_zero]
    · rw [if_neg (lt_irrefl _), if_pos (by omega), Nat.sub_self, pow_zero, mul_one,
        Nat.descFactorial_self, zero_add]
    · rw [if_neg (by omega), if_neg (by omega), (Nat.descFactorial_eq_zero_iff_lt).mpr h]
      simp

/-- The Laurent coefficient of exponent `-k` of `exp (L z)` times a germ with a pole of order at
most `m ≥ k` is the convolution of the Taylor coefficients of the exponential with the
coefficients of exponents `-k, …, -m` of the germ. -/
private theorem sLocalPrincipalPartCoeff_translate_laurent {Z : ℂ → ℂ} (hZ : MeromorphicAt Z 0)
    {m k : ℕ} (hk : k ≤ m) (hord : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Z 0)
    (C L : ℂ) :
    complexResidue (fun z ↦ C * (Complex.exp (L * z) * Z z / z ^ (-(k : ℤ) + 1))) 0 =
      C * ∑ j ∈ Finset.range (m - k + 1),
        complexResidue (fun z ↦ Z z / z ^ (-((k + j : ℕ) : ℤ) + 1)) 0 * L ^ j /
          (j.factorial : ℂ) := by
  obtain ⟨R, hR, hRZ⟩ : ∃ R > (0 : ℝ), ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ Z z := by
    obtain ⟨ε, hε, h⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp hZ.eventually_analyticAt
    exact ⟨ε, hε, fun z hz0 hz ↦ h ⟨mem_ball_zero_iff.mpr hz, hz0⟩⟩
  let N := m - k
  let c : ℕ → ℂ := fun j ↦ L ^ j / (j.factorial : ℂ)
  let P : ℂ → ℂ := fun z ↦ ∑ j ∈ Finset.range (N + 1), c j * z ^ j
  let D : ℂ → ℂ := fun z ↦ Complex.exp (L * z) - P z
  let G : ℕ → ℂ → ℂ := fun j z ↦ Z z / z ^ (-((k + j : ℕ) : ℤ) + 1)
  let Q : ℂ → ℂ := fun z ↦ D z * Z z / z ^ (-(k : ℤ) + 1)
  have hDa : Differentiable ℂ D := by
    have hP : Differentiable ℂ P := by
      have := Differentiable.sum (u := Finset.range (N + 1)) (A := fun j z ↦ c j * z ^ j)
        fun j _ ↦ by fun_prop
      convert this using 1
      funext w
      rw [Finset.sum_apply]
    exact (by fun_prop : Differentiable ℂ fun z : ℂ ↦ Complex.exp (L * z)).sub hP
  have hG : ∀ j, ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ (G j) z := fun j z hz0 hzR ↦
    (hRZ z hz0 hzR).div (analyticAt_id.zpow hz0) (zpow_ne_zero _ hz0)
  have hQ : ∀ z : ℂ, z ≠ 0 → ‖z‖ < R → AnalyticAt ℂ Q z := fun z hz0 hzR ↦
    ((hDa.analyticAt z).mul (hRZ z hz0 hzR)).div (analyticAt_id.zpow hz0) (zpow_ne_zero _ hz0)
  have hsplit : (fun z ↦ Complex.exp (L * z) * Z z / z ^ (-(k : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z ↦ (1 : ℂ) * Q z + ∑ j ∈ Finset.range (N + 1), c j * G j z) := by
    filter_upwards [self_mem_nhdsWithin] with z hz0
    have hz : z ≠ 0 := hz0
    have hterm (j : ℕ) : c j * G j z = c j * z ^ j * Z z / z ^ (-(k : ℤ) + 1) := by
      simp only [G]
      rw [show -((k + j : ℕ) : ℤ) + 1 = (-(k : ℤ) + 1) - (j : ℤ) by push_cast; ring,
        zpow_sub₀ hz, zpow_natCast, div_div_eq_mul_div]
      ring
    rw [Finset.sum_congr rfl fun j _ ↦ hterm j, ← Finset.sum_div, ← Finset.sum_mul]
    simp only [Q, D, P]
    ring
  have hQ0 : complexResidue Q 0 = 0 := by
    have hD0 : ((N + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt D 0 := by
      refine (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hDa.analyticAt 0)).mpr
        fun i hi ↦ ?_
      have hsub := iteratedDeriv_sub (n := i) (x := (0 : ℂ))
        (f := fun z : ℂ ↦ Complex.exp (L * z)) (g := P) (by fun_prop)
        (by simp only [P]; fun_prop)
      change iteratedDeriv i ((fun z : ℂ ↦ Complex.exp (L * z)) - P) 0 = 0
      rw [hsub, iteratedDeriv_cexp_const_mul, sLocalPrincipalPartCoeff_translate_poly, if_pos hi]
      show L ^ i * Complex.exp (L * 0) - L ^ i / (i.factorial : ℂ) * (i.factorial : ℂ) = 0
      rw [mul_zero, Complex.exp_zero, mul_one, div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)), sub_self]
    obtain ⟨g, hg, hgev⟩ := (natCast_le_analyticOrderAt (hDa.analyticAt 0)).mp hD0
    cases ho : meromorphicOrderAt Z 0 with
    | top =>
      refine sLocalPrincipalPartCoeff_translate_residue_zero (H := fun _ ↦ 0) analyticAt_const ?_
      filter_upwards [meromorphicOrderAt_eq_top_iff.mp ho] with z hz
      simp only [Q, hz, mul_zero, zero_div]
    | coe n =>
      rw [ho] at hord
      have hn : -(m : ℤ) ≤ n := WithTop.coe_le_coe.mp hord
      obtain ⟨h, hh, -, hev⟩ := (meromorphicOrderAt_eq_int_iff hZ).mp ho
      have he : 0 ≤ ((N + 1 : ℕ) : ℤ) + n - (-(k : ℤ) + 1) := by omega
      refine sLocalPrincipalPartCoeff_translate_residue_zero
        (H := fun z ↦ z ^ (((N + 1 : ℕ) : ℤ) + n - (-(k : ℤ) + 1)).toNat * (g z * h z))
        ((analyticAt_id.pow _).mul (hg.mul hh)) ?_
      filter_upwards [hev, hgev.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
        with z hz1 hz2 hz0
      have hz : z ≠ 0 := hz0
      simp only [Q]
      have hpow : z ^ (((N + 1 : ℕ) : ℤ) + n - (-(k : ℤ) + 1)).toNat =
          z ^ (N + 1) * z ^ n / z ^ (-(k : ℤ) + 1) := by
        rw [← zpow_natCast, Int.toNat_of_nonneg he, zpow_sub₀ hz, zpow_add₀ hz, zpow_natCast]
      rw [hz2, hz1, sub_zero, smul_eq_mul, smul_eq_mul, hpow]
      ring
  have hsplit' : (fun z ↦ C * (Complex.exp (L * z) * Z z / z ^ (-(k : ℤ) + 1))) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z ↦ C * Q z + ∑ j ∈ Finset.range (N + 1), (C * c j) * G j z) := by
    filter_upwards [hsplit] with z hz
    rw [hz, mul_add, one_mul, Finset.mul_sum]
    exact congrArg (C * Q z + ·) (Finset.sum_congr rfl fun j _ ↦ (mul_assoc _ _ _).symm)
  rw [sLocalPrincipalPartCoeff_translate_congr hsplit',
    sLocalPrincipalPartCoeff_translate_add hR hQ
      (fun z h0 h ↦ by
        have := Finset.analyticAt_sum (Finset.range (N + 1)) (f := fun j z ↦ C * c j * G j z)
          (c := z) fun j _ ↦ analyticAt_const.mul (hG j z h0 h)
        convert this using 1
        funext w
        rw [Finset.sum_apply]),
    hQ0, mul_zero, zero_add, sLocalPrincipalPartCoeff_translate_sum _ _ _ hR hG, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [c, G]
  ring

/-- Translating a test by a unit multiplies its zeta function by the value of the
quasi-character at the class of the unit. -/
private theorem sLocalPrincipalPartCoeff_translate_zeta (u : Aₛˣ) (f : ℬₛ) (d : Xₛ) :
    sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f) d =
      d (QuotientGroup.mk u) * sLocalIdelicZFunction f d := by
  obtain ⟨χ, s, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) d
  let A : ℂ → ℂ := fun z ↦ (twistₛ ((circleToComplex).comp χ) z) (QuotientGroup.mk u)
  have hM : (((mₛ (QuotientGroup.mk u : Jₛ) : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
  have hA (z : ℂ) : AnalyticAt ℂ A z ∧ A z ≠ 0 := by
    have e : A = fun z ↦ ((χ (QuotientGroup.mk u) : Circle) : ℂ) *
        (((mₛ (QuotientGroup.mk u : Jₛ) : ℝ≥0) : ℝ) : ℂ) ^ z := rfl
    rw [e]
    refine ⟨analyticAt_const.mul ((differentiable_id.const_cpow (Or.inl hM)).analyticAt z),
      mul_ne_zero (Circle.coe_ne_zero _) ?_⟩
    rw [Complex.cpow_def_of_ne_zero hM]
    exact Complex.exp_ne_zero _
  have key := eq_of_agree_rightHalf
    (U := fun z ↦ sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f)
      (twistₛ ((circleToComplex).comp χ) z))
    (V := fun z ↦ A z * sLocalIdelicZFunction f (twistₛ ((circleToComplex).comp χ) z))
    (sLocalIdelicZFunction_meromorphic _ χ)
    (fun z _ ↦ (meromorphicNFAt_mul_iff_right (hA z).1 (hA z).2).mpr
      (sLocalIdelicZFunction_meromorphic f χ (Set.mem_univ z))) 0 fun z hz ↦ ?_
  · exact congrFun key s
  · rw [sLocalIdelicZFunction_eq_integral _ ⟨χ, z, hz, rfl⟩,
      sLocalIdelicZFunction_eq_integral _ ⟨χ, z, hz, rfl⟩]
    letI : MeasurableSpace (SAdeleRing F S) := instMeasurableSpaceSAdeleRing F S
    let : BorelSpace (SAdeleRing F S)ˣ := sIdeleGroup_borelSpace
    let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
    unfold sLocalIdelicZetaIntegral
    rw [← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_mul_left_eq_self (μ := sMultiplicativeTamagawaMeasure F S) _ u]
    refine MeasureTheory.integral_congr_ae (.of_forall fun x ↦ ?_)
    change f (Multiplicative.ofAdd ((↑u⁻¹ : SAdeleRing F S) * (u * x).val)) *
        (twistₛ ((circleToComplex).comp χ) z) (QuotientGroup.mk (u * x)) =
      A z * (f (Multiplicative.ofAdd x.val) *
        (twistₛ ((circleToComplex).comp χ) z) (QuotientGroup.mk x))
    rw [Units.val_mul, ← mul_assoc, Units.inv_mul, one_mul, QuotientGroup.mk_mul, map_mul]
    simp only [A]
    ring

/-- Paper: Theorem 7.2.1.1(2), p. 334.
Translation acts on coefficients of nonpositive exponent by an upper triangular formula.
Deviation: Lower coefficients also receive terms from the higher polar coefficients.
The extra terms vanish on norm-one translations. -/
theorem sLocalPrincipalPartCoeff_translate (c : Xₛ) (k : ℕ) (hk : k ≤ sLocalRhoPoleOrder c)
    (u : Aₛˣ) (f : ℬₛ) :
    let g : Jₛ := QuotientGroup.mk u
    let logNorm : ℂ := Real.log (((mₛ g : ℝ≥0) : ℝ))
    sLocalPrincipalPartCoeff c k (schwartzBruhatUnitTranslate u f) =
      c g * ∑ j ∈ Finset.range (sLocalRhoPoleOrder c - k + 1),
        sLocalPrincipalPartCoeff c (k + j) f * logNorm ^ j / (j.factorial : ℂ) := by
  intro g logNorm
  have hZ := sLocalZ_centered f c
  have hord : ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 :=
    (sLocalIdelicOrderBound_eq_neg_poleOrder c).ge.trans hZ.2.1
  have hM : (((mₛ g : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (Units.ne_zero _))
  have hval (z : ℂ) : (twistₛ c z) g = c g * Complex.exp (logNorm * z) := by
    change c g * (((mₛ g : ℝ≥0) : ℝ) : ℂ) ^ z = _
    rw [Complex.cpow_def_of_ne_zero hM, ← Complex.ofReal_log (NNReal.coe_nonneg _)]
  rw [sLocalPrincipalPartCoeff_apply]
  change complexResidue (fun z ↦ sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f)
    (twistₛ c z) / z ^ (-(k : ℤ) + 1)) 0 = _
  have e : (fun z ↦ sLocalIdelicZFunction (schwartzBruhatUnitTranslate u f) (twistₛ c z) /
      z ^ (-(k : ℤ) + 1)) = fun z ↦ c g * (Complex.exp (logNorm * z) *
        sLocalIdelicZFunction f (twistₛ c z) / z ^ (-(k : ℤ) + 1)) := by
    funext z
    rw [sLocalPrincipalPartCoeff_translate_zeta, hval]
    ring
  rw [e, sLocalPrincipalPartCoeff_translate_laurent hZ.1 hk hord]
  rfl

-- TODO(paper-gap): The universal inequality in Theorem 7.2.1.1(3)
-- fails on the zero test whenever the functional is nonzero and k > 0.

/-- A function agreeing near `0`, off `0`, with a function analytic at `0` has residue zero. -/
private theorem sLocalPrincipalPartCoeff_ne_zero_imp_pole_residue {W H : ℂ → ℂ}
    (hH : AnalyticAt ℂ H 0) (he : W =ᶠ[𝓝[≠] (0 : ℂ)] H) : complexResidue W 0 = 0 := by
  have he' : W =ᶠ[𝓝[≠] (0 : ℂ)] (fun z ↦ (z * H z) / (z - 0)) := by
    filter_upwards [he, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, mul_div_cancel_left₀ _ hz0']
  have hcongr : complexResidue W 0 = complexResidue (fun z ↦ (z * H z) / (z - 0)) 0 := by
    obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he'
    unfold complexResidue limUnder
    refine congrArg lim (Filter.map_congr ?_)
    filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
    rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
    · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
      exact hr.2
    · rintro rfl
      exact hr.1.ne (by simpa using hz)
  rw [hcongr, complexResidue_div_sub (g := fun z ↦ z * H z) (analyticAt_id.mul hH), zero_mul]

/-- If the polar multiplicity is below `k`, the Laurent coefficient of exponent `-k` vanishes. -/
private theorem sLocalPrincipalPartCoeff_ne_zero_imp_pole_vanish {Z : ℂ → ℂ}
    (hZ : MeromorphicAt Z 0) (k : ℕ) (hk : 0 < k)
    (hlt : (-(meromorphicOrderAt Z 0).untop₀).toNat < k) :
    complexResidue (fun z ↦ Z z / z ^ (-(k : ℤ) + 1)) 0 = 0 := by
  cases ho : meromorphicOrderAt Z 0 with
  | top =>
    refine sLocalPrincipalPartCoeff_ne_zero_imp_pole_residue (H := fun _ ↦ 0) analyticAt_const ?_
    filter_upwards [meromorphicOrderAt_eq_top_iff.mp ho] with z hz
    rw [hz, zero_div]
  | coe n =>
    rw [ho] at hlt
    simp only [WithTop.untop₀_coe] at hlt
    obtain ⟨g, hg, -, hev⟩ := (meromorphicOrderAt_eq_int_iff hZ).mp ho
    have hn : 0 ≤ n + (k : ℤ) - 1 := by omega
    refine sLocalPrincipalPartCoeff_ne_zero_imp_pole_residue
      (H := fun z ↦ z ^ (n + (k : ℤ) - 1).toNat * g z) ((analyticAt_id.pow _).mul hg) ?_
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, smul_eq_mul, ← zpow_natCast, Int.toNat_of_nonneg hn,
      show n + (k : ℤ) - 1 = n - (-(k : ℤ) + 1) by ring, zpow_sub₀ hz0']
    ring

/-- Paper: Theorem 7.2.1.1(3), p. 334.
A nonvanishing polar coefficient forces a pole of the test's zeta function of at
least the indicated order, at an allowed pole of the correcting factor.
Deviation: The inequality holds for the test on which the coefficient is nonzero,
and a polar coefficient has strictly negative Laurent exponent. -/
theorem sLocalPrincipalPartCoeff_ne_zero_imp_pole (c : Xₛ) (k : ℕ) (hk : 0 < k)
    (f : ℬₛ) (hf : sLocalPrincipalPartCoeff c k f ≠ 0) :
    0 < sLocalRhoPoleOrder c ∧ k ≤ sLocalPolarMultiplicity f c := by
  have count (m : ℕ) (o : WithTop ℤ) (ho : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ o) :
      (-o.untop₀).toNat ≤ m := by
    induction o using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      have hn : -(m : ℤ) ≤ n := WithTop.coe_le_coe.mp ho
      simp only [WithTop.untop₀_coe]
      omega
  have hbound : sLocalPolarMultiplicity f c ≤ sLocalRhoPoleOrder c :=
    count _ _ ((sLocalIdelicOrderBound_eq_neg_poleOrder c).ge.trans (sLocalZ_centered f c).2.1)
  have hkN : k ≤ sLocalPolarMultiplicity f c := by
    refine Nat.le_of_not_lt fun hlt ↦ hf ?_
    rw [sLocalPrincipalPartCoeff_apply]
    exact sLocalPrincipalPartCoeff_ne_zero_imp_pole_vanish (sLocalZ_centered f c).1 k hk hlt
  exact ⟨by omega, hkN⟩

/-- Paper: Equation (7.2.1.6), p. 334.
The subspace is spanned by homogeneous theta classes whose pole orders on the
chosen component satisfy the given bound.
Deviation: The bound is extended to all quasi-characters. Its values off the
allowed pole divisor do not affect the subspace. -/
def sLocalThetaPoleBound (ω : PontryaginDual J₁) (m : Xₛ → ℕ) : Submodule ℂ (Θₛ(ω)) :=
  Submodule.span ℂ {x | ∃ f : ℬₛ, (Kₛ(ω)).mkQ f = x ∧
    ∀ c : Xₛ, onComponent(c, ω) → sLocalPolarMultiplicity f c ≤ m c}

/-- Residues only depend on the germ on a punctured neighbourhood. -/
private theorem mem_sLocalThetaPoleBound_iff_residue_congr {g h : ℂ → ℂ}
    (he : g =ᶠ[𝓝[≠] (0 : ℂ)] h) : complexResidue g 0 = complexResidue h 0 := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp he
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
  · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
    exact hr.2
  · rintro rfl
    exact hr.1.ne (by simpa using hz)

/-- The leading polar coefficient of a meromorphic germ with a pole of order `N` is nonzero. -/
private theorem mem_sLocalThetaPoleBound_iff_leading {Z : ℂ → ℂ} (hZ : MeromorphicAt Z 0)
    {N : ℕ} (hN : 0 < N) (ho : (-(meromorphicOrderAt Z 0).untop₀).toNat = N) :
    complexResidue (fun z ↦ Z z / z ^ (-(N : ℤ) + 1)) 0 ≠ 0 := by
  have hord : meromorphicOrderAt Z 0 = ((-(N : ℤ) : ℤ) : WithTop ℤ) := by
    generalize meromorphicOrderAt Z 0 = o at ho ⊢
    induction o using WithTop.recTopCoe with
    | top => simp at ho; omega
    | coe n =>
      simp only [WithTop.untop₀_coe] at ho
      congr 1
      omega
  obtain ⟨g, hg, hg0, hev⟩ := (meromorphicOrderAt_eq_int_iff hZ).mp hord
  have he : (fun z ↦ Z z / z ^ (-(N : ℤ) + 1)) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z ↦ g z / (z - 0)) := by
    filter_upwards [hev, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    rw [hz, sub_zero, smul_eq_mul, zpow_add₀ hz0', zpow_one, zpow_neg, zpow_natCast]
    field_simp
  rw [mem_sLocalThetaPoleBound_iff_residue_congr he, complexResidue_div_sub hg]
  exact hg0

/-- Paper: Equation (7.2.1.9), p. 334.
Membership in the pole-bound subspace is equivalent to vanishing of every coefficient
on the component above its allowed pole order. -/
theorem mem_sLocalThetaPoleBound_iff (ω : PontryaginDual J₁) (m : Xₛ → ℕ) (x : Θₛ(ω)) :
    x ∈ sLocalThetaPoleBound ω m ↔
      ∀ (c : Xₛ) (hc : onComponent(c, ω)), 0 < sLocalRhoPoleOrder c →
        ∀ k : ℕ, m c < k → sLocalThetaPrincipalPartCoeff ω c hc k x = 0 := by
  constructor
  · intro hx c hc _ k hk
    have hle : sLocalThetaPoleBound ω m ≤ (sLocalThetaPrincipalPartCoeff ω c hc k).ker := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨f, rfl, hf⟩
      have e : sLocalThetaPrincipalPartCoeff ω c hc k ((Kₛ(ω)).mkQ f) =
          sLocalZLaurentCoeff f c (-(k : ℤ)) := sLocalThetaPrincipalPartCoeff_mk ω c hc k f
      have hz : sLocalZLaurentCoeff f c (-(k : ℤ)) = 0 := by
        by_contra hne
        have hne' : sLocalPrincipalPartCoeff c k f ≠ 0 := by
          exact fun h ↦ hne ((sLocalPrincipalPartCoeff_apply c k f).symm.trans h)
        have h := (sLocalPrincipalPartCoeff_ne_zero_imp_pole c k (by omega) f hne').2
        have := hf c hc
        omega
      exact e.trans hz
    exact hle hx
  · intro hx
    have count (m : ℕ) (o : WithTop ℤ) (ho : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ o) :
        (-o.untop₀).toNat ≤ m := by
      induction o using WithTop.recTopCoe with
      | top => simp
      | coe n =>
        have hn : -(m : ℤ) ≤ n := WithTop.coe_le_coe.mp ho
        simp only [WithTop.untop₀_coe]
        omega
    refine ((Kₛ(ω)).mkQ_surjective x).elim fun f hf ↦ ?_
    refine Submodule.subset_span ⟨f, hf, fun c hc ↦ ?_⟩
    refine Nat.le_of_not_lt fun hlt ↦ ?_
    have hcount : sLocalPolarMultiplicity f c ≤ sLocalRhoPoleOrder c :=
      count _ _ ((sLocalIdelicOrderBound_eq_neg_poleOrder c).ge.trans (sLocalZ_centered f c).2.1)
    have hmer : MeromorphicAt (fun z ↦ sLocalIdelicZFunction f (twistₛ c z)) 0 :=
      (sLocalZ_centered f c).1
    have hpos : 0 < sLocalRhoPoleOrder c := by omega
    have h0 := hx c hc hpos (sLocalPolarMultiplicity f c) hlt
    rw [← hf] at h0
    have e : sLocalThetaPrincipalPartCoeff ω c hc (sLocalPolarMultiplicity f c) ((Kₛ(ω)).mkQ f) =
        sLocalZLaurentCoeff f c (-(sLocalPolarMultiplicity f c : ℤ)) :=
      sLocalThetaPrincipalPartCoeff_mk ω c hc (sLocalPolarMultiplicity f c) f
    have h1 := e.symm.trans h0
    have h2 : complexResidue (fun z ↦ sLocalIdelicZFunction f (twistₛ c z) /
        z ^ (-(sLocalPolarMultiplicity f c : ℤ) + 1)) 0 = 0 := h1
    exact mem_sLocalThetaPoleBound_iff_leading (N := sLocalPolarMultiplicity f c) hmer
      (by omega) rfl h2

/-- Paper: Theorem 7.2.1.1(4), p. 334.
The homogeneous theta classes with the prescribed bounds on pole order form a closed subspace. -/
theorem sLocalThetaPoleBound_isClosed (ω : PontryaginDual J₁) (m : Xₛ → ℕ) :
    IsClosed (sLocalThetaPoleBound ω m : Set (Θₛ(ω))) := by
  let I := {i : Xₛ × ℕ // onComponent(i.1, ω) ∧ 0 < sLocalRhoPoleOrder i.1 ∧ m i.1 < i.2}
  let T (i : I) : StrongDual ℂ (Θₛ(ω)) :=
    sLocalThetaPrincipalPartCoeff (F := F) (S := S) ω i.val.1 i.property.1 i.val.2
  let Z (i : I) : Set (Θₛ(ω)) := {x | T i x = 0}
  have h : (sLocalThetaPoleBound ω m : Set (Θₛ(ω))) = ⋂ i, Z i := by
    refine Set.ext fun x ↦ (mem_sLocalThetaPoleBound_iff (F := F) (S := S) ω m x).trans ?_
    refine Iff.trans ?_ (Set.mem_iInter (s := Z) (x := x)).symm
    exact ⟨fun hx i ↦ hx i.val.1 i.property.1 i.property.2.1 i.val.2 i.property.2.2,
      fun hx c hc hp k hk ↦ hx ⟨(c, k), hc, hp, hk⟩⟩
  exact (congrArg IsClosed h).mpr (isClosed_iInter fun i ↦ (T i).isClosed_ker)

/-- Paper: Theorem 7.2.1.1(4), p. 334.
The annihilator of the pole-bound subspace is the strong closure of the span of the
descended coefficients above the bound.
Deviation: Uses the indices in (7.2.1.7). Lower coefficients can fail the weight
equation, and spanning here means closed linear span in the strong dual. -/
theorem sLocalThetaPoleBound_annihilator (ω : PontryaginDual J₁) (m : Xₛ → ℕ) :
    (sLocalThetaPoleBound ω m).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) =
      (Submodule.span ℂ {T : StrongDual ℂ (Θₛ(ω)) |
        ∃ (c : Xₛ) (hc : onComponent(c, ω)) (k : ℕ),
          0 < sLocalRhoPoleOrder c ∧ m c < k ∧ sLocalThetaPrincipalPartCoeff ω c hc k = T
      }).topologicalClosure := by sorry

local notation "archEuler(" w ", " c ")" =>
  (fun z : ℂ ↦ infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ c z)))
local notation "finEuler(" v ", " c ")" =>
  (fun z : ℂ ↦ finiteLocalEulerFactor (v).val (sLocalFiniteRestriction v (twistₛ c z)))

-- TODO(paper-gap): The coordinate homomorphism into Jₛ can have a kernel.
-- For ℚ with only the real place it kills -1. Restriction uses the
-- homomorphisms of §3.3 without an injectivity condition.

open Classical in
/-- Paper: Equation (7.2.1.11), p. 335.
The archimedean places contributing a pole at a given character are those whose
restricted local Euler factors have a pole in the norm coordinate. -/
def sLocalArchPolePlaces (c : Xₛ) : Finset (InfinitePlace F) :=
  Finset.univ.filter (fun w ↦ meromorphicOrderAt (archEuler(w, c)) 0 < 0)

open Classical in
/-- Paper: Equation (7.2.1.11), p. 335.
The finite places contributing a pole at a given character are those whose
restricted local Euler factors have a pole in the norm coordinate. -/
def sLocalFinitePolePlaces (c : Xₛ) : Finset S :=
  Finset.univ.filter (fun v : S ↦ meromorphicOrderAt (finEuler(v, c)) 0 < 0)

/-- The norm twist of the trivial quasi-character is the chart of the trivial unitary character. -/
private theorem sLocalPolePlaces_one_twist_eq (z : ℂ) :
    twistₛ (1 : Xₛ) z = quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ
      ((circleToComplex).comp (1 : PontryaginDual Jₛ)) z := by
  congr 1

/-- At a real place the twisted trivial character has Euler factor `Γℝ`. -/
private theorem sLocalPolePlaces_one_arch_real (w : InfinitePlace F) (hw : w.IsReal) (z : ℂ) :
    infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z)) =
      Complex.Gammaℝ z := by
  have hval (g : w.Completionˣ) : sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z) g =
      (((((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
        (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) : ℂ) ^ z := by
    rw [sLocalPolePlaces_one_twist_eq]
    exact sLocalInfiniteRestriction_normTwist w z g
  have hshape : ∀ x : ℝˣ, sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z)
      (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) =
      (‖(x : ℝ)‖ : ℂ) ^ (z : ℂ) *
        (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ ((0 : Fin 2) : Fin 2).val := by
    intro x
    have hn : ‖((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (x : ℝ) :
        w.Completion)‖ = ‖(x : ℝ)‖ :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) (x : ℝ)
    rw [hval]
    simp [InfinitePlace.mult, hw, hn]
  have h := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z))).unique
    (realLocalEulerParameters w hw _).exists.choose_spec (y₂ := (z, 0)) hshape
  simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, h, Fin.val_zero,
    Nat.cast_zero, add_zero]

/-- At a complex place the twisted trivial character has Euler factor `Γℂ / 2`. -/
private theorem sLocalPolePlaces_one_arch_complex (w : InfinitePlace F) (hw : ¬ w.IsReal)
    (z : ℂ) :
    infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z)) =
      Complex.Gammaℂ z / 2 := by
  have hval (g : w.Completionˣ) : sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z) g =
      (((((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
        (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) g : ℝ≥0) : ℝ) : ℂ) ^ z := by
    rw [sLocalPolePlaces_one_twist_eq]
    exact sLocalInfiniteRestriction_normTwist w z g
  have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
  have hshape : ∀ x : ℂˣ, sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z)
      (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toMonoidHom x) =
      ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z : ℂ) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ ((0 : ℤ) : ℤ) := by
    intro x
    have hn : ‖((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (x : ℂ) :
        w.Completion)‖ = ‖(x : ℂ)‖ :=
      (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
        (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm) (x : ℂ)
    rw [hval]
    simp [InfinitePlace.mult, hw, hn]
  have h := (complexLocalEulerParameters w hc (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z))).unique
    (complexLocalEulerParameters w hc _).exists.choose_spec (y₂ := (z, 0)) hshape
  simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, h, Int.natAbs_zero,
    Nat.cast_zero, zero_div, add_zero]

/-- The twisted trivial character restricts at a finite place to a power of the norm. -/
private theorem sLocalPolePlaces_one_fin_val (v : S) (z : ℂ) (g : (v.val.adicCompletion F)ˣ) :
    sLocalFiniteRestriction v (twistₛ (1 : Xₛ) z) g = ((‖g.val‖ : ℝ) : ℂ) ^ z := by
  obtain ⟨y, hy⟩ : ∃ y : Jₛ, ∀ c : Xₛ, sLocalFiniteRestriction v c g = c y := ⟨_, fun c ↦ rfl⟩
  have h1 := sLocalFiniteRestriction_norm v g
  rw [hy] at h1
  rw [hy, sLocalPolePlaces_one_twist_eq]
  change (((1 : PontryaginDual Jₛ) y : Circle) : ℂ) * ((((mₛ y : ℝ≥0) : ℝ) : ℂ)) ^ z = _
  change (((1 : PontryaginDual Jₛ) y : Circle) : ℂ) * ((((mₛ y : ℝ≥0) : ℝ) : ℂ)) ^ (1 : ℂ) = _
    at h1
  rw [PontryaginDual.one_apply, Circle.coe_one, one_mul] at h1 ⊢
  rw [Complex.cpow_one] at h1
  rw [h1]
  rfl

/-- At a finite place the twisted trivial character has Euler factor `(1 - q ^ (-z))⁻¹`. -/
private theorem sLocalPolePlaces_one_fin (v : S) (z : ℂ) :
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ (1 : Xₛ) z)) =
      (1 - ((Ideal.absNorm v.val.asIdeal : ℕ) : ℂ) ^ (-z))⁻¹ := by
  have hunr : ∀ u : (HeightOneSpectrum.adicCompletionIntegers F v.val)ˣ,
      sLocalFiniteRestriction v (twistₛ (1 : Xₛ) z)
        (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom u) =
        1 := by
    intro u
    rw [sLocalPolePlaces_one_fin_val]
    have hu : ‖(Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom
        u : (v.val.adicCompletion F)ˣ).val‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u)).mp
          ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow]
  unfold finiteLocalEulerFactor
  rw [ite_eq_left hunr]
  dsimp only
  have harg : (((Ideal.absNorm v.val.asIdeal : ℕ) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  rw [sLocalPolePlaces_one_fin_val, Units.val_mk0, norm_uniformizer_adicCompletion v.val _
    (Valued.v : Valuation (v.val.adicCompletion F)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec,
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.ofReal_natCast]

/-- The reciprocal of an analytic function vanishing at `0`, but not on the positive reals,
has a pole at `0`. -/
private theorem sLocalPolePlaces_one_order (f h : ℂ → ℂ) (hf : ∀ z, f z = (h z)⁻¹)
    (hh : AnalyticAt ℂ h 0) (h0 : h 0 = 0) (hpos : ∀ x : ℝ, 0 < x → h x ≠ 0) :
    meromorphicOrderAt f 0 < 0 := by
  have hne : ¬ ∀ᶠ z in 𝓝 (0 : ℂ), h z = 0 := by
    intro hev
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
    refine hpos (ε / 2) (by linarith) (hball ?_)
    rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  rw [show f = fun z ↦ (h z)⁻¹ from funext hf,
    show meromorphicOrderAt (fun z ↦ (h z)⁻¹) 0 = -meromorphicOrderAt h 0 from
      meromorphicOrderAt_inv, hh.meromorphicOrderAt_eq]
  have h1 : analyticOrderAt h 0 ≠ 0 := by
    rw [Ne, analyticOrderAt_eq_zero]
    simp [hh, h0]
  have h2 : analyticOrderAt h 0 ≠ ⊤ := by rwa [Ne, analyticOrderAt_eq_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp h2
  rw [← hn] at h1 ⊢
  have : (0 : ℕ) < n := Nat.pos_of_ne_zero (by exact_mod_cast h1)
  simp only [ENat.map_natCast]
  exact_mod_cast (by omega : -(n : ℤ) < 0)

/-- Every archimedean Euler factor of the twisted trivial character has a pole at `0`. -/
private theorem sLocalPolePlaces_one_arch (w : InfinitePlace F) :
    meromorphicOrderAt (fun z : ℂ ↦
      infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ (1 : Xₛ) z))) 0 < 0 := by
  by_cases hw : w.IsReal
  · refine sLocalPolePlaces_one_order _ (fun z ↦ (Complex.Gammaℝ z)⁻¹)
      (fun z ↦ by rw [sLocalPolePlaces_one_arch_real w hw z, inv_inv])
      (Complex.differentiable_Gammaℝ_inv.analyticAt 0) (by simp [Complex.Gammaℝ])
      fun x hx ↦ inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by simpa using hx))
  · refine sLocalPolePlaces_one_order _ (fun z ↦ 2 * (Complex.Gammaℂ z)⁻¹)
      (fun z ↦ by rw [sLocalPolePlaces_one_arch_complex w hw z, mul_inv, inv_inv]; ring)
      (analyticAt_const.mul (Complex.differentiable_Gammaℂ_inv.analyticAt 0))
      (by simp [Complex.Gammaℂ]) fun x hx ↦ ?_
    have hr : 0 < (x : ℂ).re := by simpa using hx
    rw [Complex.Gammaℂ]
    exact mul_ne_zero two_ne_zero (inv_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero
      (by simp [Real.pi_ne_zero])) (Complex.Gamma_ne_zero_of_re_pos hr)))

/-- Every finite Euler factor of the twisted trivial character has a pole at `0`. -/
private theorem sLocalPolePlaces_one_finite (v : S) :
    meromorphicOrderAt (fun z : ℂ ↦
      finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ (1 : Xₛ) z))) 0 < 0 := by
  have hq : 1 < Ideal.absNorm v.val.asIdeal := by
    have h1 : Ideal.absNorm v.val.asIdeal ≠ 1 :=
      Ideal.absNorm_eq_one_iff.not.mpr v.val.isPrime.ne_top
    have h0 : Ideal.absNorm v.val.asIdeal ≠ 0 :=
      Ideal.absNorm_eq_zero_iff.not.mpr v.val.ne_bot
    omega
  have hq' : (1 : ℝ) < (Ideal.absNorm v.val.asIdeal : ℝ) := by exact_mod_cast hq
  have hq0 : ((Ideal.absNorm v.val.asIdeal : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega)
  refine sLocalPolePlaces_one_order _
    (fun z ↦ 1 - Complex.exp (Complex.log ((Ideal.absNorm v.val.asIdeal : ℕ) : ℂ) * (-z)))
    (fun z ↦ by rw [sLocalPolePlaces_one_fin v z, Complex.cpow_def_of_ne_zero hq0])
    ((by fun_prop : Differentiable ℂ fun z : ℂ ↦
      1 - Complex.exp (Complex.log ((Ideal.absNorm v.val.asIdeal : ℕ) : ℂ) * (-z))).analyticAt 0)
    (by simp) fun x hx ↦ ?_
  rw [← Complex.cpow_def_of_ne_zero hq0]
  rw [sub_ne_zero, ← Complex.ofReal_natCast, ← Complex.ofReal_neg,
    ← Complex.ofReal_cpow (by positivity)]
  intro h
  have h' : (Ideal.absNorm v.val.asIdeal : ℝ) ^ (-x) = 1 := by exact_mod_cast h.symm
  have := Real.rpow_lt_one_of_one_lt_of_neg hq' (by linarith : -x < 0)
  linarith

/-- Paper: Equation (7.2.1.11), p. 335.
At the trivial quasi-character every archimedean and every selected finite place
contributes a pole. -/
theorem sLocalPolePlaces_one :
    sLocalArchPolePlaces (1 : Xₛ) = Finset.univ ∧
      sLocalFinitePolePlaces (1 : Xₛ) = Finset.univ :=
  ⟨Finset.filter_true_of_mem fun w _ ↦ sLocalPolePlaces_one_arch w,
    Finset.filter_true_of_mem fun v _ ↦ sLocalPolePlaces_one_finite v⟩

/-- The reciprocal of an entire function that is not identically zero has a pole exactly at
the zeros of the function. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_inv {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {y : ℂ} (hy : G y ≠ 0) (s : ℂ) :
    meromorphicOrderAt (fun z ↦ (G z)⁻¹) s < 0 ↔ G s = 0 := by
  have hA : AnalyticAt ℂ G s := hG.analyticAt s
  change meromorphicOrderAt G⁻¹ s < 0 ↔ _
  rw [meromorphicOrderAt_inv, hA.meromorphicOrderAt_eq]
  have htop : analyticOrderAt G s ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    exact hy (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun z _ ↦ hG.analyticAt z) isPreconnected_univ (Set.mem_univ s) h (Set.mem_univ y))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have h0 : G s = 0 ↔ n ≠ 0 := by
    have e : analyticOrderAt G s = 0 ↔ n = 0 := by
      rw [← hn]
      exact_mod_cast Iff.rfl
    rw [Ne, ← e, analyticOrderAt_eq_zero]
    simp [hA]
  rw [h0, ← hn]
  simp only [ENat.map_natCast]
  constructor
  · intro h hn0
    subst hn0
    simp at h
  · intro h
    have : 0 < n := Nat.pos_of_ne_zero h
    exact_mod_cast (by omega : -(n : ℤ) < 0)

/-- At a real place the restricted Euler factor has a pole exactly where the restricted Tate
factor has one. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_real (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsReal) (s : ℂ) :
    meromorphicOrderAt (archEuler(w, (circleToComplex).comp χ)) s < 0 ↔
      meromorphicOrderAt (fun z ↦ infiniteLocalTateFactor w
        (sLocalInfiniteRestriction w (twistₛ ((circleToComplex).comp χ) z))) s < 0 := by
  rw [(sLocalRhoFactor_poles_iff_real χ w hw s).2.1]
  obtain ⟨η, ha, -⟩ := sLocalInfinite_charts χ w
  obtain ⟨t, a, -, hbase⟩ := realPlaceUnitary_shape w hw η
  have hsh := realChart_shape w hw η t a hbase
  have hp (z : ℂ) : (realLocalEulerParameters w hw (sLocalInfiniteRestriction w
      (twistₛ ((circleToComplex).comp χ) z))).exists.choose = (z + t, a) := by
    have h0 := hsh z
    rw [← ha z] at h0
    exact (realLocalEulerParameters w hw _).unique
      (realLocalEulerParameters w hw _).exists.choose_spec h0
  have hE : archEuler(w, (circleToComplex).comp χ) =
      fun z ↦ ((Complex.Gammaℝ (z + t + (a.val : ℂ)))⁻¹)⁻¹ := by
    funext z
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hp, inv_inv]
  have hG : Differentiable ℂ (fun z ↦ (Complex.Gammaℝ (z + t + (a.val : ℂ)))⁻¹) :=
    Complex.differentiable_Gammaℝ_inv.comp (by fun_prop)
  have hy : (Complex.Gammaℝ ((1 - t) + t + (a.val : ℂ)))⁻¹ ≠ 0 := by
    refine inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos ?_)
    simp only [sub_add_cancel, Complex.add_re, Complex.one_re, Complex.natCast_re]
    positivity
  rw [hE, sLocalRhoPoleOrder_eq_card_polePlaces_inv hG hy s, inv_eq_zero,
    Complex.Gammaℝ_eq_zero_iff, hp 0]
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩ <;> push_cast at hn ⊢ <;> linear_combination hn

/-- The complex Gamma factor vanishes exactly at the nonpositive integers. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_Gammaℂ (x : ℂ) :
    Complex.Gammaℂ x = 0 ↔ ∃ m : ℕ, x = -(m : ℂ) := by
  rw [Complex.Gammaℂ_def, mul_eq_zero, mul_eq_zero, Complex.cpow_eq_zero_iff,
    ← Complex.Gamma_eq_zero_iff]
  have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
  have hpi : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  simp [h2, hpi]

/-- At a complex place the restricted Euler factor has a pole exactly where the restricted Tate
factor has one. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_complex (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsComplex) (s : ℂ) :
    meromorphicOrderAt (archEuler(w, (circleToComplex).comp χ)) s < 0 ↔
      meromorphicOrderAt (fun z ↦ infiniteLocalTateFactor w
        (sLocalInfiniteRestriction w (twistₛ ((circleToComplex).comp χ) z))) s < 0 := by
  rw [(sLocalRhoFactor_poles_iff_complex χ w hw s).2.1]
  obtain ⟨η, ha, -⟩ := sLocalInfinite_charts χ w
  obtain ⟨t, r, -, hbase⟩ := complexPlaceUnitary_shape w hw η
  have hsh := complexChart_shape w hw η t r hbase
  have hp (z : ℂ) : (complexLocalEulerParameters w hw (sLocalInfiniteRestriction w
      (twistₛ ((circleToComplex).comp χ) z))).exists.choose = (z + t, r) := by
    have h0 := hsh z
    rw [← ha z] at h0
    exact (complexLocalEulerParameters w hw _).unique
      (complexLocalEulerParameters w hw _).exists.choose_spec h0
  have hnr : ¬ w.IsReal := InfinitePlace.not_isReal_iff_isComplex.mpr hw
  have hE : archEuler(w, (circleToComplex).comp χ) =
      fun z ↦ (2 * (Complex.Gammaℂ (z + t + (r.natAbs : ℂ) / 2))⁻¹)⁻¹ := by
    funext z
    simp only [infiniteLocalEulerFactor, hnr, ↓reduceDIte, hp, mul_inv, inv_inv]
    ring
  have hG : Differentiable ℂ (fun z ↦ 2 * (Complex.Gammaℂ (z + t + (r.natAbs : ℂ) / 2))⁻¹) :=
    (differentiable_const _).mul (Complex.differentiable_Gammaℂ_inv.comp (by fun_prop))
  have hy : 2 * (Complex.Gammaℂ ((1 - t - (r.natAbs : ℂ) / 2) + t + (r.natAbs : ℂ) / 2))⁻¹ ≠ 0 := by
    refine mul_ne_zero two_ne_zero (inv_ne_zero ?_)
    rw [Ne, sLocalRhoPoleOrder_eq_card_polePlaces_Gammaℂ]
    rintro ⟨m, hm⟩
    rw [show 1 - t - (r.natAbs : ℂ) / 2 + t + (r.natAbs : ℂ) / 2 = 1 by ring] at hm
    have h := congrArg Complex.re hm
    simp only [Complex.one_re, Complex.neg_re, Complex.natCast_re] at h
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  rw [hE, sLocalRhoPoleOrder_eq_card_polePlaces_inv hG hy s, mul_eq_zero, inv_eq_zero,
    or_iff_right two_ne_zero, sLocalRhoPoleOrder_eq_card_polePlaces_Gammaℂ, hp 0]
  constructor <;> rintro ⟨n, hn⟩ <;> refine ⟨n, ?_⟩ <;> push_cast at hn ⊢ <;> linear_combination hn

/-- On a unitary chart, the restriction at a finite place is the restriction at the center
times the corresponding power of the local norm. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_fin_val (χ : PontryaginDual Jₛ) (v : S)
    (z : ℂ) (x : (v.val.adicCompletion F)ˣ) :
    sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) z) x =
      sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) 0) x *
        ((‖x.val‖ : ℝ) : ℂ) ^ z := by
  have h1 := sLocalPolePlaces_one_fin_val v z x
  obtain ⟨y, hy⟩ : ∃ y : Jₛ, ∀ c : Xₛ, sLocalFiniteRestriction v c x = c y := ⟨_, fun c ↦ rfl⟩
  rw [← h1, hy, hy, hy]
  change ((χ y : Circle) : ℂ) * (((mₛ y : ℝ≥0) : ℝ) : ℂ) ^ z =
    (((χ y : Circle) : ℂ) * (((mₛ y : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)) *
      (((1 : PontryaginDual Jₛ) y : Circle) * (((mₛ y : ℝ≥0) : ℝ) : ℂ) ^ z)
  rw [Complex.cpow_zero, mul_one, PontryaginDual.one_apply, Circle.coe_one, one_mul]

/-- At a finite place the restricted Euler factor has a pole exactly where the restricted Tate
factor has one. -/
private theorem sLocalRhoPoleOrder_eq_card_polePlaces_finite (χ : PontryaginDual Jₛ) (v : S)
    (s : ℂ) :
    meromorphicOrderAt (finEuler(v, (circleToComplex).comp χ)) s < 0 ↔
      meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val
        (sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) z))) s < 0 := by
  obtain ⟨π, hπ, h⟩ := sLocalRhoFactor_poles_iff_finite χ v
  rw [(h s).2.1]
  let ψ := sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) 0)
  have hψ1 (x : (v.val.adicCompletion F)ˣ) : ‖ψ x‖ = 1 := by
    change ‖((χ _ : Circle) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    rw [Complex.cpow_zero, mul_one, Circle.norm_coe]
  let hπ₀ := (Valued.v : Valuation (v.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π₀ : (v.val.adicCompletion F)ˣ := Units.mk0 hπ₀.choose hπ₀.choose_spec.ne_zero
  have hπ₀n : ‖π₀.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v.val _ hπ₀.choose_spec
  rw [(sLocalRhoFactor_poles_iff_finite_explicit v.val ψ hψ1 π hπ s).trans
    (sLocalRhoFactor_poles_iff_finite_explicit v.val ψ hψ1 π₀ hπ₀n s).symm]
  have hq : (1 : ℝ) < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  by_cases hu : ∀ u : (v.val.adicCompletionIntegers F)ˣ,
      ψ (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1
  · have hunr (z : ℂ) : ∀ u : (v.val.adicCompletionIntegers F)ˣ,
        sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) z)
          (Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u) = 1 := by
      intro u
      have hn : ‖(Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
          u : (v.val.adicCompletion F)ˣ).val‖ = 1 :=
        Valued.toNormedField.norm_eq_one_iff.mpr
          ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
            (a := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u)).mp
            ⟨u.val.property, u.inv.property⟩)
      rw [sLocalRhoPoleOrder_eq_card_polePlaces_fin_val χ v z, hn, Complex.ofReal_one,
        Complex.one_cpow, mul_one]
      exact hu u
    let G : ℂ → ℂ := fun z ↦ 1 - ψ π₀ * ((‖π₀.val‖ : ℝ) : ℂ) ^ z
    have hE : finEuler(v, (circleToComplex).comp χ) = fun z ↦ (G z)⁻¹ := by
      funext z
      unfold finiteLocalEulerFactor
      rw [if_pos (hunr z)]
      show (1 - sLocalFiniteRestriction v (twistₛ ((circleToComplex).comp χ) z) π₀)⁻¹ = (G z)⁻¹
      rw [sLocalRhoPoleOrder_eq_card_polePlaces_fin_val χ v z π₀]
    have hnorm0 : ((‖π₀.val‖ : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr π₀.ne_zero)
    have hG : Differentiable ℂ G :=
      (differentiable_const _).sub ((differentiable_const _).mul
        (differentiable_id.const_cpow (Or.inl hnorm0)))
    have hy : G 1 ≠ 0 := by
      intro h0
      have h1 : ψ π₀ * ((‖π₀.val‖ : ℝ) : ℂ) = 1 := by
        have := sub_eq_zero.mp h0
        rw [Complex.cpow_one] at this
        exact this.symm
      have h2 := congrArg norm h1
      rw [norm_mul, hψ1, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, hπ₀n,
        norm_one] at h2
      have : (v.val.asIdeal.absNorm : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
      linarith
    rw [hE, sLocalRhoPoleOrder_eq_card_polePlaces_inv hG hy s, and_iff_right hu]
    exact sub_eq_zero.trans eq_comm
  · have hE : finEuler(v, (circleToComplex).comp χ) = fun _ ↦ 1 := by
      funext z
      unfold finiteLocalEulerFactor
      refine if_neg fun hz ↦ hu fun u ↦ ?_
      have hn : ‖(Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
          u : (v.val.adicCompletion F)ˣ).val‖ = 1 :=
        Valued.toNormedField.norm_eq_one_iff.mpr
          ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
            (a := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom u)).mp
            ⟨u.val.property, u.inv.property⟩)
      have := hz u
      rwa [sLocalRhoPoleOrder_eq_card_polePlaces_fin_val χ v z, hn, Complex.ofReal_one,
        Complex.one_cpow, mul_one] at this
    rw [hE, iff_false_intro (not_lt.mpr analyticAt_const.meromorphicOrderAt_nonneg),
      false_iff, not_and]
    exact fun h ↦ absurd h hu

/-- Paper: Theorem 7.2.1.4, p. 336.
The allowed pole multiplicity at a character counts the contributing places,
each of which contributes a simple pole. -/
theorem sLocalRhoPoleOrder_eq_card_polePlaces (c : Xₛ) :
    sLocalRhoPoleOrder c = (sLocalArchPolePlaces c).card + (sLocalFinitePolePlaces c).card := by
  classical
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  have H := sLocalRhoFactor_poles_iff_count χ a
  dsimp only at H
  have harch : sLocalArchPolePlaces (twistₛ ((circleToComplex).comp χ) a) =
      Finset.univ.filter (fun w : InfinitePlace F ↦ meromorphicOrderAt (fun z ↦
        infiniteLocalTateFactor w (sLocalInfiniteRestriction w
          (twistₛ ((circleToComplex).comp χ) z))) a < 0) := by
    unfold sLocalArchPolePlaces
    refine Finset.filter_congr fun w _ ↦ ?_
    have e : archEuler(w, twistₛ ((circleToComplex).comp χ) a) =
        archEuler(w, (circleToComplex).comp χ) ∘ (· + a) := by
      funext z
      simp only [Function.comp_apply, normTwist_normTwist]
    rw [e, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
    by_cases hw : w.IsReal
    · exact sLocalRhoPoleOrder_eq_card_polePlaces_real χ w hw a
    · exact sLocalRhoPoleOrder_eq_card_polePlaces_complex χ w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw) a
  have hfin : sLocalFinitePolePlaces (twistₛ ((circleToComplex).comp χ) a) =
      Finset.univ.filter (fun v : S ↦ meromorphicOrderAt (fun z ↦
        finiteLocalTateFactor v.val (sLocalFiniteRestriction v
          (twistₛ ((circleToComplex).comp χ) z))) a < 0) := by
    unfold sLocalFinitePolePlaces
    refine Finset.filter_congr fun v _ ↦ ?_
    have e : finEuler(v, twistₛ ((circleToComplex).comp χ) a) =
        finEuler(v, (circleToComplex).comp χ) ∘ (· + a) := by
      funext z
      simp only [Function.comp_apply, normTwist_normTwist]
    rw [e, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add]
    exact sLocalRhoPoleOrder_eq_card_polePlaces_finite χ v a
  unfold sLocalRhoPoleOrder
  rw [harch, hfin, sLocalOrderBound_chart]
  generalize hN : (Finset.univ.filter (fun w : InfinitePlace F ↦ meromorphicOrderAt (fun z ↦
        infiniteLocalTateFactor w (sLocalInfiniteRestriction w
          (twistₛ ((circleToComplex).comp χ) z))) a < 0)).card +
      (Finset.univ.filter (fun v : S ↦ meromorphicOrderAt (fun z ↦
        finiteLocalTateFactor v.val (sLocalFiniteRestriction v
          (twistₛ ((circleToComplex).comp χ) z))) a < 0)).card = N at H ⊢
  have hmin : min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor
      (twistₛ ((circleToComplex).comp χ) z)) a) = ((-(N : ℤ) : ℤ) : WithTop ℤ) := by
    by_cases hre : a.re ≤ 0
    · rw [H.2.1 hre]
      exact min_eq_right (by exact_mod_cast (by omega : -(N : ℤ) ≤ 0))
    · have hN0 : N = 0 := by
        by_contra hN0
        exact hre (H.1 (Or.inr (Nat.pos_of_ne_zero hN0)))
      have hρ : ¬ meromorphicOrderAt (fun z ↦ sLocalRhoFactor
          (twistₛ ((circleToComplex).comp χ) z)) a < 0 := fun h ↦ hre (H.1 (Or.inl h))
      rw [hN0, min_eq_left (not_lt.mp hρ)]
      rfl
  rw [hmin, WithTop.untop₀_coe]
  omega

open Classical in
/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
The multiplicity counts poles contributed by the selected finite places. The
selected pole locus consists of the points of positive multiplicity.
Deviation: Extends the multiplicity by zero outside the selected pole locus. -/
def sLocalFinitePoleMultiplicity (S₀ : Finset Places) (c : Xₛ) : ℕ :=
  ((sLocalFinitePolePlaces c).filter (fun v ↦ v.val ∈ S₀)).card

/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
The selected divisor at the trivial character has multiplicity equal to the number
of selected finite places. -/
theorem sLocalFinitePoleMultiplicity_one (S₀ : Finset Places) (h₀ : S₀ ⊆ S) :
    sLocalFinitePoleMultiplicity S₀ (1 : Xₛ) = S₀.card := by
  classical
  unfold sLocalFinitePoleMultiplicity
  rw [(sLocalPolePlaces_one (F := F) (S := S)).2]
  apply Finset.card_bij (fun v _ ↦ v.val)
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro _ _ _ _ h
    exact Subtype.ext h
  · intro v hv
    exact ⟨⟨v, h₀ hv⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

open Classical in
/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
The selected divisor counts the contributing places from both the archimedean and the
finite selections. The multiplicity is zero off the selected pole locus. -/
def sLocalSelectedPoleMultiplicity (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places)
    (c : Xₛ) : ℕ :=
  (sLocalArchPolePlaces c ∩ SArch).card + sLocalFinitePoleMultiplicity S₀ c

/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
Selecting just the finite places gives the multiplicity used for principal values. -/
theorem sLocalSelectedPoleMultiplicity_finite (S₀ : Finset Places) (c : Xₛ) :
    sLocalSelectedPoleMultiplicity ∅ S₀ c = sLocalFinitePoleMultiplicity S₀ c := by
  classical
  rw [sLocalSelectedPoleMultiplicity, Finset.inter_empty, Finset.card_empty, zero_add]

/-- Paper: Equations (7.2.2.1)–(7.2.2.2), pp. 338–339.
Selecting every place recovers the full pole order. -/
theorem sLocalSelectedPoleMultiplicity_full (c : Xₛ) :
    sLocalSelectedPoleMultiplicity Finset.univ S c = sLocalRhoPoleOrder c := by
  classical
  simp [sLocalSelectedPoleMultiplicity, sLocalFinitePoleMultiplicity,
    sLocalRhoPoleOrder_eq_card_polePlaces]

-- TODO(paper-gap): For D = U_S and E = U_{S₀}, the sheaf target in Remark 7.2.1.2
-- is O(D)/O(D-E), with stalk length mult(E), whereas the printed P_{X,D-E} has
-- stalk length mult(D-E). The Mellin image imposes strip decay. We use the
-- coefficient map on that image, with the highest coefficients on one component.
-- Already for ℚ and S = {∞, p}, residues along the nonzero points of the p-lattice
-- decay rapidly. A constant nonzero residue sequence is outside the attained range.

local notation "remainingBound(" SArch ", " S₀ ")" =>
  (fun c : Xₛ ↦ sLocalRhoPoleOrder c - sLocalSelectedPoleMultiplicity SArch S₀ c)

local notation "removedIndices(" ω ", " SArch ", " S₀ ")" =>
  {i : Xₛ × ℕ // onComponent(i.1, ω) ∧
    remainingBound(SArch, S₀) i.1 < i.2 ∧ i.2 ≤ sLocalRhoPoleOrder i.1}

/-- Paper: Remark 7.2.1.2, p. 335.
On the chosen component, collect the coefficients removed when the pole bound
is lowered by the multiplicity of the selected divisor.
Deviation: At multiplicities `m` and `n`, the index runs over `m - n < k ≤ m`. -/
def sLocalThetaRemovedPrincipalParts (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) :
    Θₛ(ω) →ₗ[ℂ] (removedIndices(ω, SArch, S₀) → ℂ) :=
  LinearMap.pi fun i ↦ (sLocalThetaPrincipalPartCoeff ω i.val.1 i.property.1 i.val.2).toLinearMap

/-- Paper: Remark 7.2.1.2, p. 335.
On a theta representative the removed principal parts evaluate to the corresponding
Laurent coefficients. -/
theorem sLocalThetaRemovedPrincipalParts_mk (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) (f : ℬₛ)
    (i : removedIndices(ω, SArch, S₀)) :
    sLocalThetaRemovedPrincipalParts ω SArch S₀ ((Kₛ(ω)).mkQ f) i =
      sLocalZLaurentCoeff f i.val.1 (-(i.val.2 : ℤ)) :=
  sLocalThetaPrincipalPartCoeff_mk ω i.val.1 i.property.1 i.val.2 f

/-- Paper: Remark 7.2.1.2, p. 335.
On the Mellin image, the classes with the remaining pole bound are exactly the
kernel of the removed-coefficient map.
Deviation: The remaining bound is `m_S - m_{S₀}`. -/
theorem sLocalThetaRemovedPrincipalParts_ker (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) :
    (sLocalThetaRemovedPrincipalParts ω SArch S₀).ker =
      sLocalThetaPoleBound ω remainingBound(SArch, S₀) := by
  have count (m : ℕ) (o : WithTop ℤ) (ho : ((-(m : ℤ) : ℤ) : WithTop ℤ) ≤ o) :
      (-o.untop₀).toNat ≤ m := by
    induction o using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      have hn : -(m : ℤ) ≤ n := WithTop.coe_le_coe.mp ho
      simp only [WithTop.untop₀_coe]
      omega
  have bound (f : ℬₛ) (c : Xₛ) : sLocalPolarMultiplicity f c ≤ sLocalRhoPoleOrder c :=
    count _ _ ((sLocalIdelicOrderBound_eq_neg_poleOrder c).ge.trans (sLocalZ_centered f c).2.1)
  let ord (c : Xₛ) := sLocalRhoPoleOrder c
  have full (x : Θₛ(ω)) : x ∈ sLocalThetaPoleBound ω ord := by
    refine ((Kₛ(ω)).mkQ_surjective x).elim fun f hf ↦ ?_
    exact Submodule.subset_span ⟨f, hf, fun c _ ↦ bound f c⟩
  let A := sLocalThetaRemovedPrincipalParts (F := F) (S := S) ω SArch S₀
  let m := remainingBound(SArch, S₀)
  refine Submodule.ext fun x ↦ Iff.trans ?_ (mem_sLocalThetaPoleBound_iff (F := F) (S := S) ω m x).symm
  constructor
  · intro hx c hc hp k hk
    by_cases hle : k ≤ sLocalRhoPoleOrder c
    · have hA : A x = 0 := hx
      exact congrFun hA ⟨(c, k), hc, hk, hle⟩
    · exact (mem_sLocalThetaPoleBound_iff (F := F) (S := S) ω ord x).mp (full x)
        c hc hp k (Nat.lt_of_not_ge hle)
  · intro hx
    change A x = 0
    funext i
    exact hx i.val.1 i.property.1 ((Nat.zero_lt_of_lt i.property.2.1).trans_le i.property.2.2)
      i.val.2 i.property.2.1

/-- A coefficient map identifies the quotient by its kernel with the attained values. -/
private theorem sLocalThetaRemovedPrincipalParts_quotient_of_ker {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (A : V →ₗ[ℂ] W)
    (H : Submodule ℂ V) (h : A.ker = H) :
    ∃ e : (V ⧸ H) ≃ₗ[ℂ] A.range, ∀ x, (e (H.mkQ x)).val = A x := by
  subst H
  exact ⟨A.quotKerEquivRange, fun x ↦ A.quotKerEquivRange_apply_mk x⟩

/-- Paper: Remark 7.2.1.2, p. 335.
The quotient by the remaining pole bound is identified by the coefficient map
with the principal parts attained on the chosen Mellin component.
Deviation: The surjective target is the range of the coefficient map. -/
theorem sLocalThetaRemovedPrincipalParts_quotient (ω : PontryaginDual J₁)
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places) :
    let H := sLocalThetaPoleBound ω remainingBound(SArch, S₀)
    let A := sLocalThetaRemovedPrincipalParts ω SArch S₀
    ∃ e : (Θₛ(ω) ⧸ H) ≃ₗ[ℂ] A.range, ∀ x : Θₛ(ω), (e (H.mkQ x)).val = A x := by
  intro H A
  have h := sLocalThetaRemovedPrincipalParts_ker (F := F) (S := S) ω SArch S₀
  let I := removedIndices(ω, SArch, S₀)
  with_reducible
    exact sLocalThetaRemovedPrincipalParts_quotient_of_ker (V := Θₛ(ω)) (W := I → ℂ) A H h

-- TODO(paper-gap): In Remark 7.2.1.3 the full bound H_{m_S} permits all poles.
-- The image of S₀₀ has no poles and corresponds to H with bound zero.
-- TODO(later): needs §7.3.1 for the claimed application of Theorem 7.3.1.2.
-- Theorem 7.3.1.2 includes the archimedean places in S₀, whereas §5.3.1
-- supplies principal values at finite places.

/-- Paper: Remark 7.2.1.3, p. 335.
The theta image of the coordinatewise polar-free tests is the subspace with
entire Mellin transform.
Deviation: The bound is zero. This is the quotient form of Proposition 5.3.4.4. -/
theorem sLocalThetaPoleBound_zero (ω : PontryaginDual J₁)
    (r : (w : {w : InfinitePlace F // w.IsReal}) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : {w : InfinitePlace F // w.IsComplex}) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)}) :
    sLocalThetaPoleBound ω (fun _ ↦ 0) = (sAdelePolarFree S r c).map (Kₛ(ω)).mkQ := by sorry

/-- Paper: Remark 7.2.1.3, p. 335.
Interpreting a polar-free theta class as its theta function identifies the entire
subspace with the exponentially decreasing norm-one isotype, with its topology.
Deviation: The entire subspace is written as the zero pole bound. -/
theorem sLocalThetaPoleBound_zero_equiv_decay (ω : PontryaginDual J₁) :
    ∃ e : ↥(sLocalThetaPoleBound ω (fun _ ↦ 0)) ≃L[ℂ]
        ↥(sLocalDecayIsotype (F := F) (S := S) univ ω),
      ∀ (x : ↥(sLocalThetaPoleBound ω (fun _ ↦ 0))) (f : ℬₛ),
        x.val = (Kₛ(ω)).mkQ f →
          ∀ g : Jₛ, (e x).val.val g = sLocalHomogeneousAdelicThetaLinearMap F S ω f g := by sorry

/-- Paper: Equation (7.2.1.12), p. 336.
The Fourier-transformed Euler product is the Euler product at the dual character
divided by the local epsilon factor.
Deviation: The local tests are normalized so that their original zeta product is
the Euler product. This uses the epsilon normalization of (3.3.1.32). -/
def sLocalFourierEulerProduct (c : Xₛ) : ℂ :=
  sLocalHeckeL (dualₛ c) / sLocalEpsilonFactor c

/-- Paper: Equation (7.2.1.12), p. 336.
If an S-adelic test has the Euler product as its zeta transform on a component,
its Fourier transform on the reflected component gives the Fourier Euler product.
The equality is between meromorphic functions in the norm coordinate. -/
theorem sLocalFourierEulerProduct_eq_zeta (c : Xₛ) (f : ℬₛ)
    (hf : (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ c z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalHeckeL (twistₛ c z))) :
    (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z)))
      =ᶠ[codiscrete ℂ] (fun z ↦ sLocalFourierEulerProduct (twistₛ c z)) := by sorry

local notation "finiteUnitMass" => (∏ v : S,
  (((finiteLocalMultiplicativeTamagawaMeasure F v.val)
    (v.val.adicCompletionIntegers F).units).toReal : ℂ))

/-- Paper: Equation (7.2.1.12), p. 336.
The Fourier transform of the tensor of the standard archimedean and finite tests
has the reflected Fourier Euler product as its Mellin transform, scaled by the
product of the integer-unit masses.
Deviation: The test is the unscaled tensor of §3.4, with its Tamagawa masses. -/
theorem sLocalFourierEulerProduct_eq_zeta_standardGaussian
    (χ : PontryaginDual Jₛ) (χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ)
    (hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ))
    (g : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
    (hg : ∀ x : InfiniteAdeleRing F, g (Multiplicative.ofAdd x) =
      ∏ w, infiniteStandardGaussian w (χArch w) (Multiplicative.ofAdd (x w))) :
    let c : Xₛ := (circleToComplex).comp χ
    let f := sLocalStandardThetaTensor c g
    (fun z : ℂ ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z)))
      =ᶠ[codiscrete ℂ] (fun z ↦ finiteUnitMass * sLocalFourierEulerProduct (twistₛ c z)) := by sorry

/-- Paper: Equations (7.2.1.12) and (7.2.1.17), pp. 336–337.
The ratio of the original Euler product to the Fourier Euler product gives the
local correcting factor as a meromorphic identity.
Deviation: The Fourier Euler product already incorporates the epsilon factor. -/
theorem sLocalRhoFactor_eq_div_fourierEulerProduct (c : Xₛ) :
    (fun z : ℂ ↦ sLocalRhoFactor (twistₛ c z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalHeckeL (twistₛ c z) / sLocalFourierEulerProduct (twistₛ c z)) := by
  have quotient (e x y : ℂ) : e * (x / y) = x / (y / e) := by
    simp [div_eq_mul_inv, mul_left_comm]
  obtain ⟨χ, a, rfl⟩ := exists_sLocalNormTwist (F := F) (S := S) c
  simp only [normTwist_normTwist]
  apply eventually_codiscrete_iff_forall_eventually_nhdsNE.mpr
  intro z
  have ht : Tendsto (fun w : ℂ ↦ w + a) (𝓝[≠] z) (𝓝[≠] (z + a)) :=
    ((Homeomorph.addRight a).map_punctured_nhds_eq z).le
  filter_upwards [ht.eventually (nhdsNE_le_codiscrete _ (sLocalRhoFactor_eq_epsilon_mul χ))] with w hw
  exact hw.trans (quotient _ _ _)

-- TODO(paper-gap): The change of unitary base point on p. 336 is
-- χ' = χ |·|^(it₀). The printed identity omits the original base point χ.

open Classical in
/-- Paper: Theorem 7.2.1.4(1), p. 336.
The coefficient of the highest allowed polar order is the product of local residues
and regular local Euler values times the Fourier-transformed dual eigendistribution.
Deviation: Uses the Laurent exponent `-m`. The epsilon factor and the finite
integer-unit masses account for the normalizations of §3.3 and §5.5. -/
theorem sLocalPrincipalPartCoeff_leading_formula (c : Xₛ) (hc : 0 < sLocalRhoPoleOrder c)
    (f : ℬₛ) :
    let arch := sLocalArchPolePlaces c
    let fin := sLocalFinitePolePlaces c
    sLocalPrincipalPartCoeff c (sLocalRhoPoleOrder c) f =
      (∏ w ∈ arch, complexResidue (archEuler(w, c)) 0) *
      (∏ w ∈ Finset.univ \ arch, archEuler(w, c) 0) *
      (∏ v ∈ fin, complexResidue (finEuler(v, c)) 0) *
      (∏ v ∈ Finset.univ \ fin, finEuler(v, c) 0) *
      (finiteUnitMass * sLocalEpsilonFactor c *
        sLocalNormalizedEigendistribution (dualₛ c) (sAdeleSchwartzFourier f)) := by sorry

/-- Paper: Theorem 7.2.1.4(1), p. 337.
The leading principal-part functional transforms with weight given by the center. -/
theorem sLocalPrincipalPartCoeff_leading_eigendistribution (c : Xₛ)
    (hc : 0 < sLocalRhoPoleOrder c) :
    sLocalPrincipalPartCoeff c (sLocalRhoPoleOrder c) ∈ sLocalEigendistributions c := by
  have leading (m : ℕ) (hm : 0 < m) (a : ℕ → ℂ) (t : ℂ) :
      (∑ j ∈ Finset.range (m - m + 1), a (m + j) * t ^ j / (j.factorial : ℂ)) = a m := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm.ne'
    simp
  apply (mem_sLocalEigendistributions (F := F) (S := S) c _).2
  intro u f
  have h := sLocalPrincipalPartCoeff_translate (F := F) (S := S) c (sLocalRhoPoleOrder c) le_rfl u f
  exact h.trans (congrArg (c (QuotientGroup.mk u) * ·)
    (leading _ hc (fun k ↦ sLocalPrincipalPartCoeff c k f) _))

/-- Paper: Theorem 7.2.1.4(2), p. 337.
Each lower coefficient is a convolution of Laurent coefficients of the correcting
factor with Taylor coefficients of the reflected zeta function of the Fourier test.
Deviation: The coefficient indexed by `k` has exponent `-k`. At `k = 0`, the last
summand of (7.2.1.14) uses the constant Laurent coefficient of the correcting
factor. Differentiation in the original chart includes the sign from reflection. -/
theorem sLocalPrincipalPartCoeff_lower_formula (c : Xₛ) (f : ℬₛ) (k : ℕ)
    (hk : k < sLocalRhoPoleOrder c) :
    let m := sLocalRhoPoleOrder c
    sLocalPrincipalPartCoeff c k f =
      ∑ j ∈ Finset.range (m - k + 1),
        complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ c z) *
          z ^ ((m : ℤ) - (j : ℤ) - 1)) 0 *
        (iteratedDeriv (m - k - j)
          (fun z ↦ sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ c z))) 0 /
          ((m - k - j).factorial : ℂ)) := by sorry

section LocalPolesGlobalZeros

local notation "K𝔽(" ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "globalUnitary(" χ ")" => ((circleToComplex).comp χ : QuasiCharacter C𝔽)
local notation "globalNormOne(" χ ")" =>
  ((χ).comp (⟨(m𝔽).ker.subtype, continuous_subtype_val⟩ : (m𝔽).ker →ₜ* C𝔽)
    : PontryaginDual (m𝔽).ker)
local notation "localChart(" χ ", " h ")" =>
  twistₛ (sIdeleRestriction F S ⟨globalUnitary(χ), h⟩)
local notation "outsideS(" h₀ ", " hχ ")" => (fun v hv ↦ hχ v (fun hv₀ ↦ hv (h₀ hv₀)))

-- TODO(paper-gap): The exact zero orders in Proposition 7.2.2.1(2) and
-- Corollary 7.2.2.2(2) fail even for the zero test. The pole cutoffs give
-- lower bounds. The proof of Proposition 7.2.2.1 also uses a factorization
-- with missing outside Fourier factors. Division by the reciprocal partial
-- Hecke Euler product in (2) implies (4) can retain both simple Tate poles
-- (at the trivial and norm characters). The meromorphic range characterization
-- in §6.3.2.1 is globalConverse_normTwist_meromorphic_exact in Ch06_LocalGlobal.Sec3.
-- For the restricted image, globalPrincipalValueConverse_normTwist_divided_exact
-- in that module detects the original two polar evaluations after division.
-- The range pullback in (4) implies (3) uses the isomorphism of §6.2.1.1(2)
-- and the principal-value commutation of §5.3.1. In the corollary, insertion scales
-- evaluation of the Fourier transform at zero by the nonzero outside additive
-- mass. Together with the unchanged value at zero this identifies the polar
-- subspaces on the trivial component. The two evaluations kill nontrivial isotypes.

open Classical in
/-- Paper: Proposition 7.2.2.1, p. 339.
Eliminating the selected highest local coefficients is equivalent to the global
zero-order bound and to membership in either homogeneous principal-value image.
Deviation: Zero orders are lower bounds on the meromorphic order. The bound drops
by one at the trivial quasi-character when it lies on the selected divisor. -/
theorem sLocalPrincipalValue_tfae {S₀ : Finset Places} (h₀ : S₀ ⊆ S) (_hn : S₀.Nonempty)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (χ : PontryaginDual C𝔽) (hχ : globalUnitary(χ) ∈ unramifiedOutside F S₀)
    (f : ℬₛ) :
    let hS : globalUnitary(χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(ωₛ)).mkQ f
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ), onComponent(c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        ∀ k : ℕ, sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity S₀ c < k →
          k ≤ sLocalRhoPoleOrder c → sLocalPrincipalPartCoeff c k f = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s) →
        let n := sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s)
        ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ) ≤
          meromorphicOrderAt Z s),
      x ∈ (sLocalHomogeneousThetaPrincipalValue h₀ ωₛ).range,
      (∃ g : ℬ𝔽, (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ g) = π x)
    ] := by sorry

local notation "polarValuesₛ" =>
  (fun f : ℬₛ ↦ (f (Multiplicative.ofAdd 0), sAdeleSchwartzFourier f (Multiplicative.ofAdd 0)))

/-- Paper: Equation (7.2.2.3), p. 340.
Evaluation at zero before and after S-adelic Fourier transform is complex linear. -/
theorem sAdelePolarValues_isLinear : IsLinearMap ℂ polarValuesₛ := by sorry

variable (F S) in
/-- Paper: Equation (7.2.2.3), p. 340.
The S-adelic polar subspace is the common kernel of evaluation at zero
and evaluation at zero after Fourier transform. -/
def sAdelePolarSubspace : Submodule ℂ ℬₛ :=
  LinearMap.ker ((sAdelePolarValues_isLinear (F := F) (S := S)).mk' polarValuesₛ)

/-- Paper: Equation (7.2.2.3), p. 340.
Membership requires both the test and its Fourier transform to vanish at zero. -/
theorem mem_sAdelePolarSubspace (f : ℬₛ) :
    f ∈ sAdelePolarSubspace F S ↔
      f (Multiplicative.ofAdd 0) = 0 ∧ sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0 := by
  change (f (Multiplicative.ofAdd 0), sAdeleSchwartzFourier f (Multiplicative.ofAdd 0)) = 0 ↔ _
  exact Prod.mk_eq_zero

/-- Paper: Corollary 7.2.2.2, p. 340.
Insertion with integer indicators outside S preserves the two zero evaluations
that define the polar subspaces. -/
theorem sAdeleSchwartzToGlobal_mem_polarSubspace (f : sAdelePolarSubspace F S) :
    sAdeleSchwartzToGlobal F S f.val ∈ adelePolarSubspace F := by sorry

open Classical in
/-- Paper: Corollary 7.2.2.2, p. 340.
On tests in the common kernel of the two zero evaluations, the global bound has
no exception. At the trivial character the local coefficient range shifts down
by one. The two principal-value images use inputs in the respective polar subspaces.
Deviation: The zero-order condition is a lower bound on meromorphic order. The
homogeneous theta classes of the restricted tests are represented in the ambient quotients. -/
theorem sLocalPolarPrincipalValue_tfae {S₀ : Finset Places} (h₀ : S₀ ⊆ S) (_hn : S₀.Nonempty)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set Places).integer F)))
    (χ : PontryaginDual C𝔽) (hχ : globalUnitary(χ) ∈ unramifiedOutside F S₀)
    (f : sAdelePolarSubspace F S) :
    let hS : globalUnitary(χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(ωₛ)).mkQ f.val
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f.val) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ), onComponent(c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        let m := sLocalRhoPoleOrder c
        let n := sLocalFinitePoleMultiplicity S₀ c
        ∀ k : ℕ, (if c = 1 then m - n ≤ k ∧ k ≤ m - 1 else m - n < k ∧ k ≤ m) →
          sLocalPrincipalPartCoeff c k f.val = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s) →
        (sLocalFinitePoleMultiplicity S₀ (localChart(χ, hS) s) : WithTop ℤ) ≤ meromorphicOrderAt Z s),
      (∃ g : sAdelePolarSubspace F S, (Kₛ(ωₛ)).mkQ (sAdelePrincipalValue F h₀ g.val) = x),
      (∃ g : adelePolarSubspace F, (K𝔽(ω)).mkQ (adelePrincipalValue F S₀ g.val) = π x)
    ] := by sorry

end LocalPolesGlobalZeros

end RiemannMasullo
