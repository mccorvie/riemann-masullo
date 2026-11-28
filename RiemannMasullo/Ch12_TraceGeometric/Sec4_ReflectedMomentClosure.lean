module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedSmoothCore
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic.Ring

/-! # Exponential moments on the reflected Paley–Wiener level -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)

/-- Pairing with the exponential on the right half-line is a bounded linear functional
on flat L². The cutoff makes the exponential itself square integrable. -/
private theorem exists_reflectedExponentialMoment (c : ℝ) :
    ∃ M : FlatL2 →L[ℂ] ℂ, ∀ v : FlatL2,
      IntegrableOn (fun y ↦ (Real.exp (-y / 2) : ℂ) * v y) (Ici c) volume ∧
      M v = ∫ y in Ici c, (Real.exp (-y / 2) : ℂ) * v y := by
  let w : ℝ → ℂ := (Ici c).indicator (fun y ↦ (Real.exp (-y / 2) : ℂ))
  have hwmeas : Measurable w := by
    have h : Continuous (fun y : ℝ ↦ (Real.exp (-y / 2) : ℂ)) :=
      Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.neg.div_const 2))
    exact h.measurable.indicator measurableSet_Ici
  have hsq (y : ℝ) : ‖w y‖ ^ 2 = (Ici c).indicator (fun t ↦ Real.exp (-t)) y := by
    by_cases hy : y ∈ Ici c
    · have h : -y / 2 + -y / 2 = -y := by ring
      rw [show w y = (Real.exp (-y / 2) : ℂ) from indicator_of_mem hy _,
        indicator_of_mem hy, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
        pow_two, ← Real.exp_add, h]
    · simp only [w, indicator_of_notMem hy, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  have hw : MemLp w 2 (volume : Measure ℝ) := by
    apply (memLp_two_iff_integrable_sq_norm hwmeas.aestronglyMeasurable).2
    simp_rw [hsq]
    rw [integrable_indicator_iff measurableSet_Ici, IntegrableOn, ← restrict_Ioi_eq_restrict_Ici]
    exact integrableOn_exp_neg_Ioi c
  let e : FlatL2 := hw.toLp w
  refine ⟨innerSL ℂ e, fun v ↦ ?_⟩
  have hinner : (fun y ↦ inner ℂ (e y) (v y)) =ᵐ[volume]
      (Ici c).indicator (fun y ↦ (Real.exp (-y / 2) : ℂ) * v y) := by
    filter_upwards [hw.coeFn_toLp] with y hy
    change e y = w y at hy
    rw [RCLike.inner_apply', hy]
    by_cases hym : y ∈ Ici c
    · simp only [w, indicator_of_mem hym, Complex.conj_ofReal]
    · simp only [w, indicator_of_notMem hym, map_zero, zero_mul]
  refine ⟨(integrable_indicator_iff measurableSet_Ici).1
    ((L2.integrable_inner (𝕜 := ℂ) e v).congr hinner), ?_⟩
  change inner ℂ e v = _
  rw [L2.inner_def, integral_congr_ae hinner, integral_indicator measurableSet_Ici]

/-- On a flat L² class supported on the right half-line, the exponential moment
can be paired over the whole real line. -/
private theorem reflectedExponentialMoment_eq_integral_of_supported {c : ℝ}
    {M : FlatL2 →L[ℂ] ℂ}
    (hM : ∀ v : FlatL2,
      IntegrableOn (fun y ↦ (Real.exp (-y / 2) : ℂ) * v y) (Ici c) volume ∧
      M v = ∫ y in Ici c, (Real.exp (-y / 2) : ℂ) * v y)
    (v : FlatL2) (hv : ∀ᵐ y : ℝ ∂volume, y < c → v y = 0) :
    Integrable (fun y ↦ (Real.exp (-y / 2) : ℂ) * v y) ∧
      M v = ∫ y, (Real.exp (-y / 2) : ℂ) * v y := by
  let m (y : ℝ) : ℂ := (Real.exp (-y / 2) : ℂ) * v y
  have hcut : (Ici c).indicator m =ᵐ[volume] m := by
    filter_upwards [hv] with y hy
    by_cases hm : y ∈ Ici c
    · exact indicator_of_mem hm _
    · rw [indicator_of_notMem hm]
      exact (mul_eq_zero_of_right _ (hy (lt_of_not_ge hm))).symm
  refine ⟨((integrable_indicator_iff measurableSet_Ici).2 (hM v).1).congr hcut,
    (hM v).2.trans ?_⟩
  calc
    (∫ y in Ici c, m y) = ∫ y, (Ici c).indicator m y :=
      (integral_indicator measurableSet_Ici).symm
    _ = _ := integral_congr_ae hcut

section SmoothCore

open scoped ContDiff ENNReal

/-- Smooth compact profiles supported strictly inside the reflected half-line
and having zero exponential moment are dense in the supported moment kernel. -/
theorem mem_closure_reflectedExponentialMomentSmoothCore (a : ℝ) (u : FlatL2)
    (hu : ∀ᵐ x : ℝ ∂volume, x < a → u x = 0)
    (hzero : (∫ x, (Real.exp (-x / 2) : ℂ) * u x) = 0) :
    u ∈ closure {v : FlatL2 | ∃ g : ℝ → ℂ,
      (v : ℝ → ℂ) =ᵐ[volume] g ∧ HasCompactSupport g ∧
      ContDiff ℝ (∞ : ℕ∞ω) g ∧ tsupport g ⊆ Ioi a ∧
      (∫ x, (Real.exp (-x / 2) : ℂ) * g x) = 0} := by
  obtain ⟨M, hM⟩ := exists_reflectedExponentialMoment a
  have hMoment (v : FlatL2) (g : ℝ → ℂ)
      (hrep : (v : ℝ → ℂ) =ᵐ[volume] g) (hsupp : tsupport g ⊆ Ioi a) :
      M v = ∫ x, (Real.exp (-x / 2) : ℂ) * g x := by
    have hv : ∀ᵐ x : ℝ ∂volume, x < a → v x = 0 := by
      filter_upwards [hrep] with x hx
      intro hxa
      exact hx.trans (image_eq_zero_of_notMem_tsupport
        (fun h ↦ (not_lt_of_ge hxa.le) (hsupp h)))
    exact (reflectedExponentialMoment_eq_integral_of_supported hM v hv).2.trans
      (integral_congr_ae (hrep.mono fun x hx ↦ congrArg ((Real.exp (-x / 2) : ℂ) * ·) hx))
  have hMu : M u = 0 :=
    (reflectedExponentialMoment_eq_integral_of_supported hM u hu).2.trans hzero
  let β : ContDiffBump (a + 2) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let b₀ (x : ℝ) : ℂ := β x
  have hβS : tsupport (β : ℝ → ℝ) ⊆ Ioi a := by
    rw [β.tsupport_eq, Real.closedBall_eq_Icc]
    intro x hx
    change (a + 2) - 1 ≤ x ∧ x ≤ (a + 2) + 1 at hx
    change a < x
    linarith [hx.1]
  have hbC : HasCompactSupport b₀ := β.hasCompactSupport.comp_left Complex.ofReal_zero
  have hbD : ContDiff ℝ (∞ : ℕ∞ω) b₀ := Complex.ofRealCLM.contDiff.comp β.contDiff
  have hbS : tsupport b₀ ⊆ Ioi a :=
    (tsupport_comp_subset Complex.ofReal_zero (β : ℝ → ℝ)).trans hβS
  have hbLp : MemLp b₀ 2 (volume : Measure ℝ) := hbD.continuous.memLp_of_hasCompactSupport hbC
  let b : FlatL2 := hbLp.toLp b₀
  have hb : b ∈ openHalflineSmoothCore a := ⟨b₀, hbLp.coeFn_toLp, hbC, hbD, hbS⟩
  let p (x : ℝ) : ℝ := Real.exp (-x / 2) * β x
  have hpC : HasCompactSupport p := β.hasCompactSupport.mul_left
  have hpcont : Continuous p :=
    (Real.continuous_exp.comp (continuous_id.neg.div_const 2)).mul β.continuous
  have hβcenter : β (a + 2) = 1 :=
    β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)
  have hpos : 0 < ∫ x, p x := by
    refine hpcont.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := volume) (x := a + 2)
      hpC (fun x ↦ mul_nonneg (Real.exp_pos _).le (β.nonneg' x)) ?_
    change Real.exp (-(a + 2) / 2) * β (a + 2) ≠ 0
    rw [hβcenter, mul_one]
    exact (Real.exp_pos _).ne'
  have hMb : M b ≠ 0 := by
    rw [hMoment b b₀ hbLp.coeFn_toLp hbS]
    change (∫ x, (Real.exp (-x / 2) : ℂ) * (β x : ℂ)) ≠ 0
    simp_rw [← Complex.ofReal_mul, integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr hpos.ne'
  refine closure_mono ?_ (mem_closure_openHalflineSmoothCore_moment a u hu M hMu b hb hMb)
  rintro v ⟨⟨g, hrep, hgc, hgd, hgs⟩, hMv⟩
  exact ⟨g, hrep, hgc, hgd, hgs, (hMoment v g hrep hgs).symm.trans hMv⟩

/-- A norm-preserving map on a closed level has the exact reflected range
once it satisfies the support and moment conditions and realizes their
smooth compact core. The moment is required for the trivial character. -/
theorem range_reflectedInput_eq_of_smoothCore
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (T : E →L[ℂ] FlatL2) (a : ℝ) (momentRequired : Prop)
    (hNorm : ∀ u ∈ V, ‖T u‖ = ‖u‖)
    (hSupport : ∀ u ∈ V, ∀ᵐ x : ℝ ∂volume, x < a → T u x = 0)
    (hMoment : ∀ u ∈ V, momentRequired → (∫ x, (Real.exp (-x / 2) : ℂ) * T u x) = 0)
    (hRealize : ∀ g : ℝ → ℂ, HasCompactSupport g → ContDiff ℝ (∞ : ℕ∞ω) g →
      tsupport g ⊆ Ioi a → (momentRequired → (∫ x, (Real.exp (-x / 2) : ℂ) * g x) = 0) →
      ∃ u ∈ V, (T u : ℝ → ℂ) =ᵐ[volume] g) :
    Set.range (fun u : V ↦ T u.val) =
      {v : FlatL2 | (∀ᵐ x : ℝ ∂volume, x < a → v x = 0) ∧
        (momentRequired → (∫ x, (Real.exp (-x / 2) : ℂ) * v x) = 0)} := by
  classical
  let : CompleteSpace V := hV.completeSpace_coe
  let U : V →ₗᵢ[ℂ] FlatL2 :=
    ⟨(T.comp V.subtypeL).toLinearMap, fun u ↦ hNorm u.val u.property⟩
  have hRangeClosed : IsClosed (Set.range (fun u : V ↦ T u.val)) :=
    U.isometry.isClosedEmbedding.isClosed_range
  let core := {v : FlatL2 | ∃ g : ℝ → ℂ, (v : ℝ → ℂ) =ᵐ[volume] g ∧
    HasCompactSupport g ∧ ContDiff ℝ (∞ : ℕ∞ω) g ∧ tsupport g ⊆ Ioi a ∧
    (momentRequired → (∫ x, (Real.exp (-x / 2) : ℂ) * g x) = 0)}
  have hCore : core ⊆ Set.range (fun u : V ↦ T u.val) := by
    rintro v ⟨g, hrep, hgc, hgd, hgs, hgm⟩
    obtain ⟨u, hu, hrep'⟩ := hRealize g hgc hgd hgs hgm
    exact ⟨⟨u, hu⟩, Lp.ext (hrep'.trans hrep.symm)⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨u, rfl⟩
    exact ⟨hSupport u.val u.property, hMoment u.val u.property⟩
  · rintro v ⟨hv, hvm⟩
    apply closure_minimal hCore hRangeClosed
    by_cases hreq : momentRequired
    · refine (closure_mono ?_) (mem_closure_reflectedExponentialMomentSmoothCore a v hv (hvm hreq))
      rintro z ⟨g, hrep, hgc, hgd, hgs, hgm⟩
      exact ⟨g, hrep, hgc, hgd, hgs, fun _ ↦ hgm⟩
    · refine (closure_mono ?_) (mem_closure_openHalflineSmoothCore a v hv)
      rintro z ⟨g, hrep, hgc, hgd, hgs⟩
      exact ⟨g, hrep, hgc, hgd, hgs, fun h ↦ (hreq h).elim⟩

end SmoothCore

section ClosedLevel

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "W(" s ")" => Lp ℂ 2 (intervalSobolevMeasure μJ (logSIdeleQuotientNorm F S) 0 0 s)
local notation "band(" B ")" =>
  Subtype (fun g : Zₛ ↦ Subtype.val g ∈ sLocalPWTests (F := F) (S := S) (T := S)
    le_rfl (sLocalPWProductRegion S B))

/-- Paper: (11.2.1.6), p. 488, and Theorem 12.4.1.1, p. 515.
If a bounded map to flat L² has reflected support on the invariant level,
its generator moment condition extends to the entire closed level. -/
theorem sLocalInvariantPWSobolev_reflectedExponentialMoment_eq_zero_of_generators
    {s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (ω : PontryaginDual J₁)
    (B c : ℝ) (T : W(s) →L[ℂ] FlatL2) (r : Zₛ → ℝ → ℂ)
    (hrep : ∀ f : Zₛ,
      (T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f) : ℝ → ℂ)
        =ᵐ[volume] r f)
    (hzero : ∀ f : band(B), (∫ y, (Real.exp (-y / 2) : ℂ) * r f.val y) = 0)
    (hsupport : ∀ u ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω B,
      ∀ᵐ y : ℝ ∂volume, y < c → T u y = 0)
    (u : W(s)) (hu : u ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω B) :
    Integrable (fun y ↦ (Real.exp (-y / 2) : ℂ) * T u y) ∧
      (∫ y, (Real.exp (-y / 2) : ℂ) * T u y) = 0 := by
  obtain ⟨M, hM⟩ := exists_reflectedExponentialMoment c
  have hker : sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω B ≤ (M.comp T).ker := by
    unfold sLocalInvariantPWSobolev
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) (M.comp T).isClosed_ker
    rintro _ ⟨f, rfl⟩
    apply LinearMap.mem_ker.mpr
    let g : W(s) := sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f.val
    have hg : g ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω B :=
      sLocalInvariantPWSobolev_mem (F := F) (S := S) hs ha ω B f.val f.property
    have hv : (T g : ℝ → ℂ) =ᵐ[volume] r f.val := hrep f.val
    change M (T g) = 0
    calc
      _ = ∫ y, (Real.exp (-y / 2) : ℂ) * T g y :=
        (reflectedExponentialMoment_eq_integral_of_supported hM (T g) (hsupport g hg)).2
      _ = ∫ y, (Real.exp (-y / 2) : ℂ) * r f.val y :=
        integral_congr_ae (hv.mono fun y hy ↦ congrArg ((Real.exp (-y / 2) : ℂ) * ·) hy)
      _ = 0 := hzero f
  have hum : M (T u) = 0 := LinearMap.mem_ker.mp (hker hu)
  obtain ⟨hi, he⟩ := reflectedExponentialMoment_eq_integral_of_supported hM (T u) (hsupport u hu)
  exact ⟨hi, he.symm.trans hum⟩

end ClosedLevel

end RiemannMasullo
