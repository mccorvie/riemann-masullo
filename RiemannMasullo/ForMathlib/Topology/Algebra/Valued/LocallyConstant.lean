module

public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.Support

/-! # Valuation shells of a dilation difference -/

public section

open Filter Function Set Topology

namespace RiemannMasullo

/-- A dilation difference of a radial, locally constant, compactly supported function
on a valued field is a finite sum of valuation-shell indicators. -/
theorem exists_finsupp_valuation_dilation_sub {K Γ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ]
    [TopologicalSpace K] [IsTopologicalRing K] (v : Valuation K Γ)
    (hv : ∀ x : K, x ≠ 0 → ∀ᶠ y in 𝓝 x, v y = v x)
    (f : K → ℂ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f)
    (hr : ∀ x y : K, x ≠ 0 → y ≠ 0 → v x = v y → f x = f y) (c : Kˣ) :
    ∃ b : Γ →₀ ℂ, ∀ x : K, x ≠ 0 → b (v x) = f x - f (c.val * x) := by
  classical
  let d (x : K) := f x - f (c.val * x)
  let a := Homeomorph.mulLeft₀ c.val c.ne_zero
  have hd : HasCompactSupport d := hc.sub (hc.comp_homeomorph a)
  have hloc : IsLocallyConstant d := hf.comp₂ (hf.comp_continuous a.continuous) (· - ·)
  let Z := tsupport d
  have hzero : 0 ∉ Z := by
    have hz : d 0 = 0 := by simp [d]
    have hclose : IsClosed (support d) := (hloc.isClopen_fiber 0).isOpen.isClosed_compl
    exact fun h ↦ (hclose.closure_eq ▸ h : 0 ∈ support d) hz
  let : CompactSpace Z := isCompact_iff_compactSpace.mp hd
  have hfinite : (v '' Z).Finite := by
    rw [image_eq_range]
    apply IsLocallyConstant.range_finite
    exact (IsLocallyConstant.iff_eventually_eq _).mpr fun x ↦
      continuous_subtype_val.continuousAt (hv x.val fun h ↦ hzero (h ▸ x.property))
  let b (r : Γ) := if h : ∃ x : K, x ≠ 0 ∧ v x = r then d h.choose else 0
  have hb (r : Γ) (x : K) (hx : x ≠ 0) (hxr : v x = r) : b r = d x := by
    have h : ∃ y : K, y ≠ 0 ∧ v y = r := ⟨x,hx,hxr⟩
    have he := h.choose_spec.2.trans hxr.symm
    have hh : v (c.val * h.choose) = v (c.val * x) := by simp only [map_mul, he]
    exact (dite_eq_left h).trans (congrArg₂ (· - ·) (hr _ _ h.choose_spec.1 hx he)
      (hr _ _ (mul_ne_zero c.ne_zero h.choose_spec.1) (mul_ne_zero c.ne_zero hx) hh))
  have hs : (support b).Finite := hfinite.subset fun r hr₀ ↦ by
    by_cases h : ∃ x : K, x ≠ 0 ∧ v x = r
    · refine ⟨h.choose, subset_closure ?_, h.choose_spec.2⟩
      exact fun hz ↦ hr₀ ((hb r _ h.choose_spec.1 h.choose_spec.2).trans hz)
    · exact (hr₀ (dite_eq_right h)).elim
  exact ⟨Finsupp.ofSupportFinite b hs, fun x hx ↦ hb _ x hx rfl⟩

end RiemannMasullo
