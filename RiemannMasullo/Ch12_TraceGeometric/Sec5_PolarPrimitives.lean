module

public import RiemannMasullo.Ch12_TraceGeometric.Sec5
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # The compactly supported range of the two-pole differential filter

Masullo, Theorem 12.5.1.1, pp. 519–520. A section-normalized angular character
annihilates the two polar Mellin values unless it is trivial on the norm-one
classes. On the radial part, their common kernel is the range of the second
logarithmic norm derivative minus one quarter, with the same support interval.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

private theorem polarExp_hasDerivAt (z : ℂ) (x : ℝ) :
    HasDerivAt (fun t : ℝ ↦ Complex.exp (z * t)) (z * Complex.exp (z * x)) x := by
  simpa [mul_comm] using ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul z).cexp

/-- Solve (u' + zu=h) without enlarging a closed support interval when the corresponding
exponential moment vanishes. -/
private theorem polarFirstOrder_primitive (z : ℂ) {a b : ℝ} (h : ℝ → ℂ)
    (hh : ContDiff ℝ (∞) h) (hs : ∀ x ∉ Icc a b, h x = 0)
    (hm : (∫ x : ℝ, h x * Complex.exp (z * x)) = 0) :
    ∃ u : ℝ → ℂ, ContDiff ℝ (∞) u ∧ (∀ x ∉ Icc a b, u x = 0) ∧
      ∀ x, HasDerivAt u (h x - z * u x) x := by
  let w (t : ℝ) := h t * Complex.exp (z * t)
  let J (x : ℝ) := ∫ t in Iic x, w t
  have hhc : HasCompactSupport h :=
    exists_compact_iff_hasCompactSupport.mp ⟨Icc a b, isCompact_Icc, hs⟩
  have hw : ContDiff ℝ (∞) w := hh.mul (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp
  have hi : Integrable w := hw.continuous.integrable_of_hasCompactSupport hhc.mul_right
  have hJ (x : ℝ) : HasDerivAt J (w x) x := by
    have he : J = fun y ↦ (∫ t in (0 : ℝ)..y, w t) + J 0 := by
      funext y
      exact (sub_eq_iff_eq_add.mp (intervalIntegral.integral_Iic_sub_Iic
        (a := 0) (b := y) hi.integrableOn hi.integrableOn))
    rw [he]
    exact (intervalIntegral.integral_hasDerivAt_right (hw.continuous.intervalIntegrable 0 x)
      hw.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter hw.continuous.continuousAt).add_const _
  have hJs : ContDiff ℝ (∞) J := contDiff_infty_iff_deriv.mpr
    ⟨fun x ↦ (hJ x).differentiableAt, (funext fun x ↦ (hJ x).deriv) ▸ hw⟩
  let u (x : ℝ) := Complex.exp (-z * x) * J x
  refine ⟨u, ((contDiff_const.mul Complex.ofRealCLM.contDiff).cexp.mul hJs), ?_, ?_⟩
  · intro x hx
    have hzero : J x = 0 := by
      by_cases hxa : x < a
      · exact setIntegral_eq_zero_of_forall_eq_zero fun t ht ↦ by
          have ht' : t ∉ Icc a b := fun hm ↦ (not_lt.mpr hm.1) (ht.trans_lt hxa)
          simp [w, hs t ht']
      · have hbx : b < x := lt_of_not_ge fun hxb ↦ hx ⟨le_of_not_gt hxa, hxb⟩
        have he : J x = ∫ y, w y := setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht ↦ by
          have ht' : t ∉ Icc a b := fun hm ↦ ht (hm.2.trans hbx.le)
          simp [w, hs t ht']
        exact he.trans hm
    simp [u, hzero]
  · intro x
    have he : Complex.exp (-z * x) * Complex.exp (z * x) = 1 := by
      rw [← Complex.exp_add, neg_mul, neg_add_cancel, Complex.exp_zero]
    convert (polarExp_hasDerivAt (-z) x).mul (hJ x) using 1
    dsimp only [u, w]
    linear_combination -(h x) * he

private theorem polarMoment_deriv (h : ℝ → ℂ) (hh : ContDiff ℝ (∞) h)
    (hs : HasCompactSupport h) (z : ℂ) :
    (∫ x : ℝ, deriv h x * Complex.exp (z * x)) =
      -z * ∫ x : ℝ, h x * Complex.exp (z * x) := by
  let e (x : ℝ) := Complex.exp (z * x)
  have he : Continuous e := by dsimp [e]; fun_prop
  have hd : ContDiff ℝ (∞) (deriv h) := (contDiff_infty_iff_deriv.mp hh).2
  have hd' x : HasDerivAt h (deriv h x) x := (hh.differentiable (by simp) x).hasDerivAt
  have hb := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := h) (u' := deriv h) (v := e) (v' := fun x ↦ z * e x)
    (fun x _ ↦ hd' x) (fun x _ ↦ polarExp_hasDerivAt z x)
    ((hh.continuous.mul (continuous_const.mul he)).integrable_of_hasCompactSupport hs.mul_right)
    ((hd.continuous.mul he).integrable_of_hasCompactSupport hs.deriv.mul_right)
    ((hh.continuous.mul he).integrable_of_hasCompactSupport hs.mul_right)
  have hj : (∫ x, h x * (z * e x)) = z * ∫ x, h x * e x := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by ring)
  rw [hj] at hb
  change (∫ x, deriv h x * e x) = -z * ∫ x, h x * e x
  linear_combination hb

/-- On any fixed closed log-norm interval, a smooth compactly supported profile has both
half-Mellin moments zero precisely when it is the image of a smooth primitive supported in
the same interval under the second derivative minus one quarter. -/
theorem radialPolarMoments_eq_zero_iff_exists_compact_primitive {a b : ℝ}
    (h : ℝ → ℂ) (hh : ContDiff ℝ (∞) h) (hs : ∀ x ∉ Icc a b, h x = 0) :
    ((∫ x : ℝ, h x * Complex.exp ((1 / 2 : ℂ) * x)) = 0 ∧
      (∫ x : ℝ, h x * Complex.exp ((-1 / 2 : ℂ) * x)) = 0) ↔
    ∃ g : ℝ → ℂ, ContDiff ℝ (∞) g ∧ (∀ x ∉ Icc a b, g x = 0) ∧
      ∀ x, deriv (deriv g) x - g x / 4 = h x := by
  constructor
  · rintro ⟨hp, hm⟩
    obtain ⟨p, hps, hpK, hpd⟩ := polarFirstOrder_primitive (1 / 2) h hh hs hp
    obtain ⟨m, hms, hmK, hmd⟩ := polarFirstOrder_primitive (-1 / 2) h hh hs hm
    let g := m - p
    have hg (x : ℝ) : HasDerivAt g ((m x + p x) / 2) x := by
      convert (hmd x).sub (hpd x) using 1
      ring
    have hgd : deriv g = fun x ↦ (m x + p x) / 2 := funext fun x ↦ (hg x).deriv
    refine ⟨g, hms.sub hps, fun x hx ↦ by simp [g, hmK x hx, hpK x hx], fun x ↦ ?_⟩
    rw [hgd]
    change deriv (fun t ↦ (m + p) t / 2) x - g x / 4 = h x
    rw [(((hmd x).add (hpd x)).div_const 2).deriv]
    change (h x - (-1 / 2) * m x + (h x - (1 / 2) * p x)) / 2 - (m x - p x) / 4 = h x
    ring
  · rintro ⟨g, hg, hK, hder⟩
    have hgc : HasCompactSupport g :=
      exists_compact_iff_hasCompactSupport.mp ⟨Icc a b, isCompact_Icc, hK⟩
    have hg' : ContDiff ℝ (∞) (deriv g) := (contDiff_infty_iff_deriv.mp hg).2
    have hg'' : ContDiff ℝ (∞) (deriv (deriv g)) := (contDiff_infty_iff_deriv.mp hg').2
    have hfilter (z : ℂ) :
        (∫ x : ℝ, h x * Complex.exp (z * x)) =
          (z ^ 2 - 1 / 4) * ∫ x : ℝ, g x * Complex.exp (z * x) := by
      let e (x : ℝ) := Complex.exp (z * x)
      have he : Continuous e := by dsimp [e]; fun_prop
      have h1 : Integrable fun x ↦ deriv (deriv g) x * e x :=
        (hg''.continuous.mul he).integrable_of_hasCompactSupport hgc.deriv.deriv.mul_right
      have h2 : Integrable fun x ↦ (1 / 4 : ℂ) * (g x * e x) :=
        ((hg.continuous.mul he).integrable_of_hasCompactSupport hgc.mul_right).const_mul _
      have heq : (fun x ↦ h x * e x) = fun x ↦ deriv (deriv g) x * e x - (1 / 4 : ℂ) * (g x * e x) := by
        funext x
        rw [← hder x]
        ring
      change (∫ x, h x * e x) = _
      rw [heq, integral_sub h1 h2, integral_const_mul]
      dsimp only [e]
      rw [polarMoment_deriv (deriv g) hg' hgc.deriv, polarMoment_deriv g hg hgc]
      ring
    constructor <;> rw [hfilter] <;> norm_num

section GlobalRadialPoles

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "pole(" φ "," v ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm F) univ
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport C𝔽).val (ideleClassNormTwist 1 v)

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For an actual radial Bruhat test on the class
group, the vanishing of both polar Mellin terms is equivalent to the given profile being
the second derivative minus one quarter of a smooth profile in the same log-norm interval.
Reconstruction: This identifies the profiles on which the two corrections vanish. -/
theorem normTest_polarMoments_eq_zero_iff_exists_compact_primitive {a b : ℝ}
    (h : ℝ → ℂ) (hh : ContDiff ℝ (∞) h) (hs : ∀ x ∉ Icc a b, h x = 0)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g, φ.val g = h (Real.log (((ideleClassNorm F g).val : ℝ)))) :
    (pole(φ, (1 / 2)) = 0 ∧ pole(φ, (-1 / 2)) = 0) ↔
      ∃ g : ℝ → ℂ, ContDiff ℝ (∞) g ∧ (∀ x ∉ Icc a b, g x = 0) ∧
        ∀ x, deriv (deriv g) x - g x / 4 = h x := by
  classical
  let V := (((normOneIdeleClassTamagawaMeasure F) univ).toReal : ℂ)
  let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
  have hV : V ≠ 0 := Complex.ofReal_ne_zero.mpr (ENNReal.toReal_ne_zero.mpr
    ⟨isOpen_univ.measure_ne_zero _ univ_nonempty, measure_ne_top _ _⟩)
  have hp (z : ℂ) : pole(φ, z) = V * ∫ x : ℝ, h x * Complex.exp (z * x) := by
    have hunit : ∀ u : (ideleClassNorm F).ker, (1 : PontryaginDual C𝔽) u.val = 1 := fun u ↦
      PontryaginDual.one_apply u.val
    rw [normTest_mellin h hh.continuous φ hφ 1 z, ite_eq_left hunit]
    have hshift := grh_shift_integral h hh.continuous (fun _ ↦ 1) (fun _ ↦ rfl) 0 z
    simpa only [V, PontryaginDual.one_apply, Circle.coe_one, mul_one, sub_zero,
      Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using
      congrArg (fun v : ℂ ↦ V * v) hshift
  rw [hp, hp, ← radialPolarMoments_eq_zero_iff_exists_compact_primitive h hh hs]
  simp [hV]

/-- Integrating an angular character nontrivial on the norm-one group annihilates the
polar Mellin integral of any character times radial profile, at every complex abscissa. -/
private theorem characterNormTest_pole_eq_zero_of_nontrivial
    (ψ : PontryaginDual C𝔽) (hψ : ¬ ∀ u : (ideleClassNorm F).ker, ψ u.val = 1)
    (h : ℝ → ℂ) (hh : ContDiff ℝ (∞) h) (hK : HasCompactSupport h)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g, φ.val g = (ψ g : ℂ) * h (Real.log (((ideleClassNorm F g).val : ℝ))))
    (z : ℂ) : pole(φ, z) = 0 := by
  classical
  obtain ⟨r, hr⟩ := exists_normTest (F := F) h hh hK
  have he : pole(φ, z) = modulatedFourierMellin (continuousIdeleClassNorm F) univ
      ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
      (ideleClassTamagawaMeasure F) r.val (ideleClassNormTwist ψ z) := by
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
    apply integral_congr_ae
    filter_upwards with c
    rw [hφ, hr]
    let n : ℂ := (((ideleClassNorm F c).val : ℝ) : ℂ) ^ z
    let H := h (Real.log (((ideleClassNorm F c).val : ℝ)))
    change (ψ c : ℂ) * H * (1 * n) = H * ((ψ c : ℂ) * n)
    ring
  rw [he, normTest_mellin h hh.continuous r hr ψ z, ite_eq_right hψ, zero_mul]

/-- Paper: Theorem 12.5.1.1, pp. 519–520. For a character times a smooth compact log-norm
profile, with the character trivial on a norm section, vanishing of the two actual global polar
Mellin values is equivalent to one of two alternatives. The character is nontrivial on the
norm-one subgroup, or the profile admits a second-order primitive on the same support interval. -/
private theorem sectionCharacterNormTest_polarMoments_eq_zero_iff_exists_compact_primitive
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : PontryaginDual C𝔽) (hψτ : ∀ t, ψ (τ t) = 1) {a b : ℝ}
    (h : ℝ → ℂ) (hh : ContDiff ℝ (∞) h) (hs : ∀ x ∉ Icc a b, h x = 0)
    (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ g, φ.val g = (ψ g : ℂ) * h (Real.log (((ideleClassNorm F g).val : ℝ)))) :
    (pole(φ, (1 / 2)) = 0 ∧ pole(φ, (-1 / 2)) = 0) ↔
      (¬ ∀ u : (ideleClassNorm F).ker, ψ u.val = 1) ∨
      ∃ g : ℝ → ℂ, ContDiff ℝ (∞) g ∧ (∀ x ∉ Icc a b, g x = 0) ∧
        ∀ x, deriv (deriv g) x - g x / 4 = h x := by
  classical
  by_cases hψ : ∀ u : (ideleClassNorm F).ker, ψ u.val = 1
  · have htriv (c : C𝔽) : ψ c = 1 := by
      have hunit : c / τ (ideleClassNorm F c) ∈ (ideleClassNorm F).ker := by
        rw [MonoidHom.mem_ker, map_div, hτ, div_self']
      have h' := hψ ⟨_, hunit⟩
      change ψ (c / τ (ideleClassNorm F c)) = 1 at h'
      rwa [map_div, hψτ, div_one] at h'
    have hrad := normTest_polarMoments_eq_zero_iff_exists_compact_primitive h hh hs φ
      (fun c ↦ by simpa only [htriv, Circle.coe_one, one_mul] using hφ c)
    exact ⟨fun hz ↦ Or.inr (hrad.mp hz), fun h ↦ hrad.mpr (h.resolve_left (not_not.mpr hψ))⟩
  · have hK : HasCompactSupport h :=
      exists_compact_iff_hasCompactSupport.mp ⟨Icc a b, isCompact_Icc, hs⟩
    have hzero := characterNormTest_pole_eq_zero_of_nontrivial ψ hψ h hh hK φ hφ
    exact ⟨fun _ ↦ Or.inl hψ, fun _ ↦ ⟨hzero _, hzero _⟩⟩

local notation "radialFlow(" τ ")" =>
  (⟨(τ : ℝ≥0ˣ →ₜ* C𝔽).toMonoidHom.comp positiveRealLogEquiv.symm.toMulEquiv.toMonoidHom,
    (τ : ℝ≥0ˣ →ₜ* C𝔽).continuous.comp positiveRealLogEquiv.symm.continuous⟩ : Multiplicative ℝ →ₜ* C𝔽)
local notation "classLog(" c ")" => Real.log (((ideleClassNorm F c).val : ℝ))

private theorem polarFlow_log_exp (t : ℝ) :
    Real.log (((positiveRealLogEquiv.symm (Multiplicative.ofAdd t)).val : ℝ)) = t := by
  rw [← positiveRealLogEquiv_apply, ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd]

/-- The Bruhat directional derivative along the logarithmic norm section differentiates the
profile of a section-normalized character times a radial function. -/
private theorem polarFlow_directionalDeriv
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : PontryaginDual C𝔽) (hψτ : ∀ t, ψ (τ t) = 1)
    (H : ℝ → ℂ) (hH : Differentiable ℝ H)
    (f : C𝔽 → ℂ) (hf : ∀ c, f c = (ψ c : ℂ) * H (classLog(c))) (c : C𝔽) :
    bruhatDirectionalDeriv (radialFlow(τ)) f c = (ψ c : ℂ) * deriv H (classLog(c)) := by
  let x := classLog(c)
  have hcurve : (fun t : ℝ ↦ f (c * (radialFlow(τ)) (Multiplicative.ofAdd t))) =
      fun t : ℝ ↦ (ψ c : ℂ) * H (x + t) := by
    funext t
    rw [hf, map_mul, Circle.coe_mul]
    change (ψ c : ℂ) * (ψ (τ (positiveRealLogEquiv.symm (Multiplicative.ofAdd t))) : ℂ) *
        H (classLog(c * τ (positiveRealLogEquiv.symm (Multiplicative.ofAdd t)))) = _
    rw [hψτ, Circle.coe_one, mul_one, map_mul, hτ, Units.val_mul, NNReal.coe_mul,
      Real.log_mul (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
        (NNReal.coe_pos.mpr (Units.zero_lt _)).ne', polarFlow_log_exp]
  change deriv _ 0 = _
  have hd : DifferentiableAt ℝ (fun t : ℝ ↦ H (x + t)) 0 :=
    (hH.comp (show Differentiable ℝ (fun t : ℝ ↦ x + t) by fun_prop)) 0
  rw [hcurve, deriv_const_mul _ hd, deriv_comp_const_add, add_zero]

/-- Paper: Theorem 12.5.1.1, pp. 519–520, and Definition D.1.6.5, p. 766.
For a section-normalized character times a compact profile, both global polar terms vanish
exactly when the angular character kills them or the actual idèle-class test has a compact
Bruhat primitive under two logarithmic norm derivatives minus one quarter. The primitive
has the same angular character and is supported in the original log-norm interval.
Reconstruction: This gives the range of the polar filter on the tests of the missing comparison. -/
theorem sectionCharacterNormTest_polarMoments_eq_zero_iff_exists_directionalPrimitive
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (ψ : PontryaginDual C𝔽) (hψτ : ∀ t, ψ (τ t) = 1) {a b : ℝ}
    (h : ℝ → ℂ) (hh : ContDiff ℝ (∞) h) (hs : ∀ x ∉ Icc a b, h x = 0)
    (φ : BruhatCompactSupport C𝔽) (hφ : ∀ c, φ.val c = (ψ c : ℂ) * h (classLog(c))) :
    (pole(φ, (1 / 2)) = 0 ∧ pole(φ, (-1 / 2)) = 0) ↔
      (¬ ∀ u : (ideleClassNorm F).ker, ψ u.val = 1) ∨
      ∃ (g : ℝ → ℂ) (G : BruhatCompactSupport C𝔽), ContDiff ℝ (∞) g ∧
        (∀ x ∉ Icc a b, g x = 0) ∧ (∀ c, G.val c = (ψ c : ℂ) * g (classLog(c))) ∧
        ∀ c, bruhatDirectionalDeriv (radialFlow(τ))
          (bruhatDirectionalDeriv (radialFlow(τ)) G.val) c - G.val c / 4 = φ.val c := by
  rw [sectionCharacterNormTest_polarMoments_eq_zero_iff_exists_compact_primitive
    τ hτ ψ hψτ h hh hs φ hφ]
  have hcalc (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g) (G : BruhatCompactSupport C𝔽)
      (hG : ∀ c, G.val c = (ψ c : ℂ) * g (classLog(c))) (c : C𝔽) :
      bruhatDirectionalDeriv (radialFlow(τ))
        (bruhatDirectionalDeriv (radialFlow(τ)) G.val) c - G.val c / 4 =
        (ψ c : ℂ) * (deriv (deriv g) (classLog(c)) - g (classLog(c)) / 4) := by
    have hd := polarFlow_directionalDeriv τ hτ ψ hψτ g
      (contDiff_infty_iff_deriv.mp hg).1 G.val hG
    have hdd := polarFlow_directionalDeriv τ hτ ψ hψτ (deriv g)
      (contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hg).2).1 _ hd c
    rw [hdd, hG]
    ring
  apply or_congr_right
  constructor
  · rintro ⟨g, hg, hgK, heq⟩
    have hgc : HasCompactSupport g :=
      exists_compact_iff_hasCompactSupport.mp ⟨Icc a b, isCompact_Icc, hgK⟩
    obtain ⟨G, hG⟩ := exists_characterNormTest (F := F) ψ g hg hgc
    exact ⟨g, G, hg, hgK, hG, fun c ↦ (hcalc g hg G hG c).trans
      ((congrArg (fun z : ℂ ↦ (ψ c : ℂ) * z) (heq _)).trans (hφ c).symm)⟩
  · rintro ⟨g, G, hg, hgK, hG, heq⟩
    refine ⟨g, hg, hgK, fun x ↦ ?_⟩
    let t := positiveRealLogEquiv.symm (Multiplicative.ofAdd x)
    have hlog : classLog(τ t) = x := by
      rw [hτ]
      exact polarFlow_log_exp x
    have hx := (hcalc g hg G hG (τ t)).symm.trans ((heq _).trans (hφ _))
    simpa only [hψτ, Circle.coe_one, one_mul, hlog] using hx

end GlobalRadialPoles

end RiemannMasullo
