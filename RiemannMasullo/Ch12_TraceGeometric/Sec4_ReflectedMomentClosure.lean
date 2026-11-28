module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.Ch10_TraceSpectral.Sec1
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
