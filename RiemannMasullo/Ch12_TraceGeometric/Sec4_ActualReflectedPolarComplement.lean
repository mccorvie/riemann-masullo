module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualFixedBandTraceClass
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_LevelPolarComplement
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ReflectedPolarVector
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # The exact trivial-character polar direction at order zero -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal InnerProductSpace NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "W₀" => CompactIntervalSobolev μJ (logSIdeleQuotientNorm F S) 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "halfPos" => (show (0 : ℝ) < 1 / 2 by norm_num)

/-- The exact supported range and the exponential moment condition pick out
the same normalized complement vector for any supplied common isometry. -/
theorem existsUnique_normalizedPolarDirection_of_reflectedRanges
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Vfull Vpolar : Submodule ℂ H) (hLe : Vpolar ≤ Vfull) (T : H →L[ℂ] FlatL2)
    (hIso : ∀ w ∈ Vfull, ‖T w‖ = ‖w‖) (a : ℝ)
    (hFullRange : Set.range (fun u : Vfull ↦ T u.val) =
      {r : FlatL2 | ∀ᵐ y : ℝ ∂volume, y < a → r y = 0})
    (hPolarRange : Set.range (fun u : Vpolar ↦ T u.val) =
      {r : FlatL2 | (∀ᵐ y : ℝ ∂volume, y < a → r y = 0) ∧
        (∫ y, (Real.exp (-y / 2) : ℂ) * r y) = 0}) :
    ∃! u : Vfull, T u.val = normalizedHalflineExponentialL2 a ∧
      ‖u.val‖ = 1 ∧ Vfull ⊓ Vpolarᗮ = ℂ ∙ u.val := by
  let e := normalizedHalflineExponentialL2 a
  have he : e ∈ Set.range (fun u : Vfull ↦ T u.val) := by
    rw [hFullRange]
    exact normalizedHalflineExponentialL2_ae_zero_lt a
  have hMoment (r : FlatL2) (hr : ∀ᵐ y : ℝ ∂volume, y < a → r y = 0) :
      ⟪e, r⟫_ℂ = 0 ↔ (∫ y, (Real.exp (-y / 2) : ℂ) * r y) = 0 := by
    change inner ℂ (normalizedHalflineExponentialL2 a) r = 0 ↔ _
    rw [(normalizedHalflineExponentialL2_inner_supported a r hr).2]
    have hd : (Real.exp (a / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    exact ⟨fun h ↦ (mul_eq_zero.mp h).resolve_left hd, fun h ↦ mul_eq_zero_of_right _ h⟩
  have hPolar : Set.range (fun u : Vpolar ↦ T u.val) =
      {r : FlatL2 | r ∈ Set.range (fun u : Vfull ↦ T u.val) ∧ ⟪e, r⟫_ℂ = 0} := by
    rw [hPolarRange, hFullRange]
    ext r
    exact ⟨fun ⟨hs, hm⟩ ↦ ⟨hs, (hMoment r hs).2 hm⟩,
      fun ⟨hs, hi⟩ ↦ ⟨hs, (hMoment r hs).1 hi⟩⟩
  exact existsUnique_unit_preimage_span_orthogonalComplement Vfull Vpolar hLe T hIso
    e (norm_normalizedHalflineExponentialL2 a) he hPolar

/-- Paper: Theorem 12.4.1.1, pp. 515–518. At order zero the full band has
exactly one polar direction in the trivial norm-one character. The common
reflected isometry takes its normalized vector to the half-line exponential. -/
theorem exists_sLocalFullPWSobolev_normalizedPolarDirection_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S)) {B : ℝ} (hB : 0 < B) :
    let Vfull : Submodule ℂ W₀ := Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0)
      le_rfl halfPos (1 : PontryaginDual J₁) B
    let Vpolar : Submodule ℂ W₀ := sLocalInvariantPWSobolev (F := F) (S := S) (s := 0)
      le_rfl halfPos (1 : PontryaginDual J₁) B
    ∃ T : W₀ →L[ℂ] FlatL2, (∀ u ∈ Vfull, ‖T u‖ = ‖u‖) ∧
      ∃! u : Vfull, T u.val = normalizedHalflineExponentialL2 (-Real.log B) ∧
        ‖u.val‖ = 1 ∧ Vfull ⊓ Vpolarᗮ = ℂ ∙ u.val := by
  intro Vfull Vpolar
  obtain ⟨χ, Q, L, U, _, _, _, _, _, hRecover, _, _, _, hFullRange, hPolarRange⟩ :=
    exists_sLocalFullReflectedCoordinates_orderZero τ hτ (1 : PontryaginDual J₁) hB
  let T : W₀ →L[ℂ] FlatL2 := U.toLinearIsometry.toContinuousLinearMap.comp Q
  have hIso (w : W₀) (hw : w ∈ Vfull) : ‖T w‖ = ‖w‖ := by
    change ‖U (Q w)‖ = ‖w‖
    rw [U.norm_map, ← L.norm_map (Q w), hRecover w hw]
  have hLe : Vpolar ≤ Vfull :=
    (Isolated.sLocalPWSobolev_polarComplement (F := F) (S := S) (s := 0)
      le_rfl halfPos (1 : PontryaginDual J₁) B).1
  refine ⟨T, hIso, existsUnique_normalizedPolarDirection_of_reflectedRanges
    Vfull Vpolar hLe T hIso (-Real.log B) hFullRange ?_⟩
  have hRange : Set.range (fun u : Vpolar ↦ T u.val) =
      {r : FlatL2 | (∀ᵐ y : ℝ ∂volume, y < -Real.log B → r y = 0) ∧
        ((1 : PontryaginDual J₁) = 1 → (∫ y, (Real.exp (-y / 2) : ℂ) * r y) = 0)} :=
    hPolarRange
  simpa only [true_implies] using hRange

end RiemannMasullo

namespace RiemannMasullo.Isolated

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The trace difference between the full and polar-free compressions is
the diagonal entry on the unit vector spanning their relative complement. -/
theorem hilbertTrace_nuclearCompress_sub_eq_inner_of_complement_line
    (A : nuclearEndomorphisms H) (V B : Submodule ℂ H)
    [V.HasOrthogonalProjection] [B.HasOrthogonalProjection] (hVB : V ≤ B)
    (u : H) (hu : ‖u‖ = 1) (hK : B ⊓ Vᗮ = ℂ ∙ u) :
    hilbertTrace (nuclearCompress B.starProjection A) -
      hilbertTrace (nuclearCompress V.starProjection A) = ⟪u, A.val u⟫_ℂ := by
  have hu0 : u ≠ 0 := fun h ↦ by simp [h] at hu
  have hdim : Module.finrank ℂ ↥(B ⊓ Vᗮ) = 1 := by
    rw [hK, finrank_span_singleton hu0]
  let : FiniteDimensional ℂ ↥(B ⊓ Vᗮ) :=
    FiniteDimensional.of_finrank_eq_succ (n := 0) hdim
  let uK : ↥(B ⊓ Vᗮ) := ⟨u, by
    rw [hK]
    exact Submodule.mem_span_singleton_self u⟩
  let e : OrthonormalBasis Unit ℂ ↥(B ⊓ Vᗮ) :=
    FiniteDimensional.orthonormalBasisSingleton Unit ℂ hdim uK (show ‖uK‖ = 1 from hu)
  have he (i : Unit) : (e i : H) = u := by
    simp [e, uK]
  have hTrace :
      hilbertTrace (nuclearCompress B.starProjection A) =
        hilbertTrace (nuclearCompress V.starProjection A) + ⟪u, A.val u⟫_ℂ := by
    simpa only [Fintype.sum_unique, he] using hilbertTrace_nuclearCompress_eq A V B hVB e
  rw [hTrace, add_sub_cancel_left]

end RiemannMasullo.Isolated
