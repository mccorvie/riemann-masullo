module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.MeasureTheory.Function.Holder

/-! # Almost-everywhere support on the closed invariant Paley–Wiener level -/

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

noncomputable section

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "Zₛ" => sAdelePolarSubspace F S
local notation "W(" s ")" => Lp ℂ 2 (intervalSobolevMeasure μJ (logSIdeleQuotientNorm F S) 0 0 s)
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)

/-- Vanishing below a real cutoff is preserved under passage from a set of
prototypes to its closed linear span. -/
public theorem map_closedSpan_ae_eq_zero_lt_of_generators
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (generators : Set E) (c : ℝ) (T : E →L[ℂ] FlatL2)
    (hgen : ∀ v ∈ generators, ∀ᵐ x : ℝ ∂volume, x < c → T v x = 0)
    (u : E) (hu : u ∈ (Submodule.span ℂ generators).topologicalClosure) :
    ∀ᵐ x : ℝ ∂volume, x < c → T u x = 0 := by
  classical
  let ρ : ℝ → ℂ := (Iio c).indicator (fun _ ↦ 1)
  have hρm : Measurable ρ := measurable_const.indicator measurableSet_Iio
  have hρb (x : ℝ) : ‖ρ x‖ ≤ 1 := by
    by_cases hx : x ∈ Iio c <;> simp [ρ, hx]
  have hρtop : MemLp ρ (⊤ : ℝ≥0∞) (volume : Measure ℝ) :=
    memLp_top_of_bound hρm.aestronglyMeasurable 1 (ae_of_all _ hρb)
  let multiply := ContinuousLinearMap.mul ℂ ℂ
  let M : FlatL2 →L[ℂ] FlatL2 := multiply.holderL volume (⊤ : ℝ≥0∞) 2 2 (hρtop.toLp ρ)
  have hM (w : FlatL2) : (M w : ℝ → ℂ) =ᵐ[volume] fun x ↦ ρ x * w x :=
    (multiply.coeFn_holder (r := 2) (hρtop.toLp ρ) w).trans <|
      hρtop.coeFn_toLp.mono fun x hx ↦ congrArg (· * w x) hx
  have hzeroFn : ∀ᵐ x : ℝ ∂volume, (0 : FlatL2) x = (0 : ℂ) :=
    (Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)).mono fun _ hx ↦ by
      simpa only [Pi.zero_apply] using hx
  have hzero (w : FlatL2) : M w = 0 ↔ ∀ᵐ x : ℝ ∂volume, x < c → w x = 0 := by
    constructor
    · intro h
      have hm := hM w
      rw [h] at hm
      filter_upwards [hm, hzeroFn] with x hx h0
      intro hxc
      have hρ : ρ x = 1 := Set.indicator_of_mem (show x ∈ Iio c from hxc) _
      simpa only [hρ, one_mul] using hx.symm.trans h0
    · intro h
      apply Lp.ext
      filter_upwards [hM w, h, hzeroFn] with x hx hw h0
      rw [hx, h0]
      by_cases hxc : x ∈ Iio c
      · rw [hw (show x < c from hxc), mul_zero]
      · simp [ρ, hxc]
  have hker : (Submodule.span ℂ generators).topologicalClosure ≤ (M.comp T).ker := by
    refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.mpr ?_) (M.comp T).isClosed_ker
    intro v hv
    exact LinearMap.mem_ker.mpr ((hzero _).2 (hgen v hv))
  exact (hzero _).1 (LinearMap.mem_ker.mp (hker hu))

/-- A continuous linear map whose images of the defining generators vanish on
the left open half-line has the same vanishing on the closed invariant level. -/
public theorem sLocalInvariantPWSobolev_map_ae_eq_zero_lt_of_generators
    {s a : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (ω : PontryaginDual J₁)
    (B c : ℝ) (T : W(s) →L[ℂ] FlatL2)
    (hgen : ∀ f : {g : Zₛ // g.val ∈ sLocalPWTests (F := F) (S := S) (T := S)
        le_rfl (sLocalPWProductRegion S B)},
      ∀ᵐ x : ℝ ∂volume, x < c →
        T (sLocalPWThetaSobolevMap (F := F) (S := S) (s := s) ha ω f.val) x = 0)
    (u : W(s)) (hu : u ∈ sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω B) :
    ∀ᵐ x : ℝ ∂volume, x < c → T u x = 0 := by
  unfold sLocalInvariantPWSobolev at hu
  refine map_closedSpan_ae_eq_zero_lt_of_generators _ c T ?_ u hu
  rintro _ ⟨f, rfl⟩
  exact hgen f

end

end RiemannMasullo
