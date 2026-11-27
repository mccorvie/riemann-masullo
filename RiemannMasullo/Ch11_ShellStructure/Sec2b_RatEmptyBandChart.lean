module

public import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b

/-! # The actual rational empty-finite-place polar Fourier tests

The real coordinate is exact at any radius, including zero. It identifies the
actual reflexive adelic support and polar constraints with those of a real
Schwartz test. This is the test-level chart for the local Sobolev level on p. 488. -/

public noncomputable section

open Function IsDedekindDomain NumberField Set
open scoped NumberField.AdeleRing FourierTransform

namespace RiemannMasullo

local notation "A₀" => SAdeleRing ℚ ∅
local notation "Test₀" => SchwartzBruhat (Multiplicative A₀)
local notation "π₀" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "refl₀" => le_refl (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))

/-- The coordinate used by the rational Fourier comparison, with its inverse topology. -/
@[expose] def ratEmptyFourierCoord : Multiplicative A₀ ≃ₜ ℝ :=
  let D := (v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ
  let _ : Unique D := uniqueOfSubsingleton 0
  let _ : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  (Homeomorph.prodUnique (InfiniteAdeleRing ℚ) D).trans
    ((Homeomorph.piUnique (fun v : InfinitePlace ℚ ↦ v.Completion)).trans
      (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).toHomeomorph)

theorem ratEmptyFourierCoord_apply (x : Multiplicative A₀) :
    ratEmptyFourierCoord x = π₀ (x.toAdd.1 Rat.infinitePlace) := rfl

private theorem ratEmpty_coord_abs (x : Multiplicative A₀) :
    |ratEmptyFourierCoord x| = ‖x.toAdd.1 Rat.infinitePlace‖ := by
  rw [ratEmptyFourierCoord_apply, ← Real.norm_eq_abs, ← dist_zero_right,
    ← dist_zero_right (x.toAdd.1 Rat.infinitePlace), ← map_zero π₀]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).dist_eq _ 0

theorem ratEmpty_box_preimage (B : ℝ) :
    Multiplicative.toAdd ⁻¹' sLocalPWBox (F := ℚ) ∅ B = ratEmptyFourierCoord ⁻¹' Icc (-B) B := by
  ext x
  change ((∀ w : InfinitePlace ℚ, ‖x.toAdd.1 w‖ ^ w.mult ≤ B) ∧ _) ↔
    -B ≤ ratEmptyFourierCoord x ∧ ratEmptyFourierCoord x ≤ B
  rw [← abs_le, ratEmpty_coord_abs]
  constructor
  · intro h
    simpa only [Rat.isReal_infinitePlace.mult_eq_one, pow_one] using h.1 Rat.infinitePlace
  · intro h
    refine ⟨fun w ↦ ?_, fun v ↦ absurd v.2 (Finset.notMem_empty _)⟩
    obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
    simpa only [Rat.isReal_infinitePlace.mult_eq_one, pow_one] using h

theorem ratEmpty_productRegion_eq_box (B : ℝ) :
    sLocalPWProductRegion (F := ℚ) ∅ B = sLocalPWBox (F := ℚ) ∅ B := by
  let _ : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  ext x
  change (∏ w : InfinitePlace ℚ, ‖x.1 w‖ ^ w.mult) *
    (∏ v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))), ‖x.2 v‖) ≤ B ↔
    Multiplicative.ofAdd x ∈ Multiplicative.toAdd ⁻¹' sLocalPWBox (F := ℚ) ∅ B
  rw [Fintype.prod_unique, Finset.univ_eq_empty, Finset.prod_empty, mul_one, ratEmpty_box_preimage]
  change ‖x.1 Rat.infinitePlace‖ ^ Rat.infinitePlace.mult ≤ B ↔
    -B ≤ ratEmptyFourierCoord (Multiplicative.ofAdd x) ∧ ratEmptyFourierCoord (Multiplicative.ofAdd x) ≤ B
  rw [← abs_le, ratEmpty_coord_abs, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  change (‖x.1 Rat.infinitePlace‖ ≤ B) ↔ (‖x.1 Rat.infinitePlace‖ ≤ B)
  exact Iff.rfl

variable (φ : SchwartzMap ℝ ℂ) (f : Test₀)
  (hf : ∀ x : A₀, f (Multiplicative.ofAdd x) = φ (π₀ (x.1 Rat.infinitePlace)))

include hf in
/-- Equality of the actual topological supports, not just a bound on the nonzero set. -/
theorem ratEmpty_fourier_tsupport_eq : tsupport (sAdeleSchwartzFourier f).val =
    ratEmptyFourierCoord ⁻¹' tsupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) := by
  change closure (support _) = _ ⁻¹' closure (support _)
  rw [ratEmptyFourierCoord.isOpenMap.preimage_closure_eq_closure_preimage ratEmptyFourierCoord.continuous]
  congr 1
  ext x
  change (sAdeleSchwartzFourier f (Multiplicative.ofAdd x.toAdd) ≠ 0) ↔ _
  rw [sAdeleSchwartzFourier_ratEmpty_apply φ f hf]
  rfl

private theorem ratEmpty_refl_test (g : Test₀) : sAdeleSchwartzTransition ℚ refl₀ g = g := by
  refine Subtype.ext (funext fun x ↦ ?_)
  change sAdeleSchwartzTransition ℚ refl₀ g (Multiplicative.ofAdd x.toAdd) = g x
  rw [sAdeleSchwartzTransition_apply, ite_eq_left (fun w ↦ absurd w.2 (Finset.notMem_empty _))]
  rfl

include hf in
/-- The polar reflexive Fourier-box tests in real coordinates. This also holds at radius zero. -/
theorem ratEmpty_polar_box_tests_iff (B : ℝ) :
    (f ∈ sAdelePolarSubspace ℚ ∅ ∧ f ∈ sLocalPWTests refl₀ (sLocalPWBox (F := ℚ) ∅ B)) ↔
      φ 0 = 0 ∧ (𝓕 φ : SchwartzMap ℝ ℂ) 0 = 0 ∧ tsupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) ⊆ Icc (-B) B := by
  rw [mem_sAdelePolarSubspace, sAdeleSchwartzFourier_ratEmpty_apply φ f hf, hf,
    show ((0 : A₀).1 Rat.infinitePlace) = 0 from rfl, map_zero, mem_sLocalPWTests]
  simp only [ratEmpty_refl_test]
  have hs := ratEmpty_fourier_tsupport_eq φ f hf
  constructor
  · rintro ⟨⟨h₀, h₁⟩, g, rfl, _, hb⟩
    rw [hs, ratEmpty_box_preimage] at hb
    refine ⟨h₀, h₁, fun r hr ↦ ?_⟩
    obtain ⟨x, rfl⟩ := ratEmptyFourierCoord.surjective r
    exact hb (show x ∈ ratEmptyFourierCoord ⁻¹' tsupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) from hr)
  · rintro ⟨h₀, h₁, hb⟩
    have hsub : tsupport (sAdeleSchwartzFourier f).val ⊆
        Multiplicative.toAdd ⁻¹' sLocalPWBox (F := ℚ) ∅ B := by
      rw [hs, ratEmpty_box_preimage]
      exact preimage_mono hb
    exact ⟨⟨h₀, h₁⟩, f, rfl, (isCompact_sLocalPWBox (F := ℚ) (S := ∅) B).of_isClosed_subset
      (isClosed_tsupport _) hsub, hsub⟩

include hf in
/-- The actual product region used by the invariant Sobolev generators gives exactly the same tests. -/
theorem ratEmpty_polar_product_tests_iff (B : ℝ) :
    (f ∈ sAdelePolarSubspace ℚ ∅ ∧ f ∈ sLocalPWTests refl₀ (sLocalPWProductRegion (F := ℚ) ∅ B)) ↔
      φ 0 = 0 ∧ (𝓕 φ : SchwartzMap ℝ ℂ) 0 = 0 ∧ tsupport ⇑(𝓕 φ : SchwartzMap ℝ ℂ) ⊆ Icc (-B) B := by
  rw [ratEmpty_productRegion_eq_box]
  exact ratEmpty_polar_box_tests_iff φ f hf B

end RiemannMasullo
