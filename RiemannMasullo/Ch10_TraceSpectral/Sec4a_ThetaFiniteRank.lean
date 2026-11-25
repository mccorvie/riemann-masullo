module
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a

/-! # Physical cutoff exhaustion at fixed geometric rank

A finite geometric approximation can be lifted from the narrow space to finitely many
wide theta inputs. Every such finite contribution vanishes after physical cutoff
exhaustion, even with arbitrary continuous coordinate functionals.
-/

@[expose] public noncomputable section
open Filter Function MeasureTheory NumberField Set
open scoped Topology NNReal ENNReal NumberField.AdeleRing
namespace RiemannMasullo

private theorem thetaRank_trace_sum {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {ι : Type*} [Fintype ι]
    (ℓ : ι → H →L[ℂ] ℂ) (u : ι → H) :
    ∃ h : IsNuclearOperator (∑ j, (ℓ j).smulRight (u j)),
      hilbertTrace ⟨_,h⟩ = ∑ j, ℓ j (u j) := by
  let T (j : ι) : nuclearEndomorphisms H := ⟨_, smulRight_mem_nuclearEndomorphisms (ℓ j) (u j)⟩
  have he : (∑ j, T j : nuclearEndomorphisms H).val = ∑ j, (ℓ j).smulRight (u j) :=
    Submodule.coe_sum (nuclearEndomorphisms H) T Finset.univ
  refine ⟨he ▸ (∑ j, T j : nuclearEndomorphisms H).property, ?_⟩
  obtain ⟨tr,htr⟩ := hilbertTrace_linear (H := H)
  calc
    _ = hilbertTrace (∑ j, T j) := congrArg hilbertTrace (Subtype.ext he.symm)
    _ = ∑ j, tr (T j) := by rw [← htr, map_sum]
    _ = ∑ j, ℓ j (u j) := Finset.sum_congr rfl fun j _ ↦ (htr _).trans (hilbertTrace_smulRight _ _)

variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => NumberField.IdeleClassGroup (NumberField.RingOfIntegers F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "x𝔽" => logIdeleClassNorm F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" b ", " s ")" => CompactIntervalSobolev μ𝔽 x𝔽 (-b) b s
local notation "ν(" b ", " s ")" => intervalSobolevMeasure μ𝔽 x𝔽 (-b) b s
local notation "Θ(" a ", " h ", " hs ")" => globalThetaSobolev F a (neg_le_self h) hs
local notation "Ps(" a ", " h ", " hs ")" => spectralProjection (F := F) a h hs
local notation "act(" h ", " hs ", " φ ")" => hardySobolevTestAction μ𝔽 m𝔽 _ _ _ (neg_le_self h) hs φ
local notation "mask(" b ", " s ", " hc ")" => modulatedCutoffOperator m𝔽 ν(b,s) hc

/-- Paper: Definition 10.4.1.5 and Theorem 10.4.2.8, pp. 458 and 463–464.
Each fixed finite sum of wide theta inputs gives zero after physical cutoff
exhaustion followed by wide spectral projection. The coordinate functionals may
come from a different Hilbert norm on the same physical representatives. -/
theorem spectralRestriction_trace_tendsto_zero_of_finite_theta_inputs
    (a : ℝ) {β s : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    {ι : Type*} [Fintype ι] (u : ι → W(β,s)) (hu : ∀ j, u j ∈ Θ(a,hβ,hs))
    (ℓ : ι → W(β,s) →L[ℂ] ℂ) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ t : ℝ → ℂ, (∀ᶠ R in atTop, ∃ hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
      let B := ∑ j, ((ℓ j).comp (Ps(a,hβ,hs))).smulRight ((mask(β,s,hc)) ((act(hβ,hs,φ)) (u j)))
      ∃ hB : IsNuclearOperator B, t R = hilbertTrace ⟨B,hB⟩) ∧ Tendsto t atTop (𝓝 0) := by
  obtain ⟨M, _, hM, hm⟩ := exists_stronglyConvergent_modulatedCutoffOperators C𝔽 m𝔽 ν(β,s) ε ρ hε hρ
  let v (j : ι) := (act(hβ,hs,φ)) (u j)
  let l (j : ι) := (ℓ j).comp (Ps(a,hβ,hs))
  have hv (j : ι) : v j ∈ Θ(a,hβ,hs) :=
    (Submodule.Quotient.mk_eq_zero _).mp ((hardySobolevTestAction_preserves_globalTheta
      (F := F) a (neg_le_self hβ) hs φ) (hu j))
  have hz (j : ι) : l j (v j) = 0 := by
    have h : (Ps(a,hβ,hs)) (v j) = 0 :=
      (Submodule.starProjection_apply_eq_zero_iff (K := (Θ(a,hβ,hs)).orthogonal)).mpr
        ((Θ(a,hβ,hs)).le_orthogonal_orthogonal (hv j))
    exact (congrArg (ℓ j) h).trans (map_zero _)
  refine ⟨fun R ↦ ∑ j, l j (M R (v j)), ?_, ?_⟩
  · filter_upwards [hρ] with R hR
    obtain ⟨hn, ht⟩ := thetaRank_trace_sum l (fun j ↦ (mask(β,s,hR.1)) (v j))
    refine ⟨hR.1, hn, ?_⟩
    rw [hm R hR.1]
    exact ht.symm
  · have h (j : ι) : Tendsto (fun R ↦ l j (M R (v j))) atTop (𝓝 0) := by
      rw [← hz j]
      exact ((l j).continuous.tendsto (v j)).comp (hM (v j))
    simpa using tendsto_finsetSum Finset.univ (fun j _ ↦ h j)


/-- Paper: Definition 10.4.1.5, p. 458. A fixed finite-dimensional subspace of narrow
theta representatives that lift into the wide theta space has a bounded lift of its
orthogonal projection. Its physical cutoff trace on wide spectral inputs tends to zero. -/
theorem spectralRestriction_trace_tendsto_zero_of_lifted_theta_projection
    (a : ℝ) {α β s : ℝ} (hβ : 0 ≤ β) (hs : 0 ≤ s) (φ : BruhatCompactSupport C𝔽)
    (I : W(β,s) →L[ℂ] W(α,s)) (E : Submodule ℂ W(α,s)) [FiniteDimensional ℂ E]
    (hE : (E : Set _) ⊆ I '' (Θ(a,hβ,hs) : Set _)) (ε : ℝ → ℝ) (ρ : ℝ → C𝔽 → ℝ)
    (hε : Tendsto (fun R ↦ ε R * R) atTop (𝓝 0))
    (hρ : ∀ᶠ R in atTop, IsModulatedCutoff m𝔽 R (ε R) (ρ R) ∧
      0 < R⁻¹ + ε R ∧ R⁻¹ + ε R < R - ε R) :
    ∃ (L : W(α,s) →L[ℂ] W(β,s)), I.comp L = E.starProjection ∧
      (∀ q, L q ∈ Θ(a,hβ,hs)) ∧
      ∃ t : ℝ → ℂ, (∀ᶠ R in atTop, ∃ hc : IsModulatedCutoff m𝔽 R (ε R) (ρ R),
        let B := (mask(β,s,hc)).comp ((act(hβ,hs,φ)).comp (L.comp (I.comp (Ps(a,hβ,hs)))))
        ∃ hB : IsNuclearOperator B, t R = hilbertTrace ⟨B,hB⟩) ∧ Tendsto t atTop (𝓝 0) := by
  classical
  let b := stdOrthonormalBasis ℂ E
  choose g hg hIg using fun j ↦ hE (b j).property
  let c (j : Fin (Module.finrank ℂ E)) := innerSL ℂ ((b j).val : W(α,s))
  let L : W(α,s) →L[ℂ] W(β,s) := ∑ j, (c j).smulRight (g j)
  have hL (x : W(α,s)) : L x = ∑ j, c j x • g j := by
    simp only [L, sum_apply, ContinuousLinearMap.smulRight_apply]
  refine ⟨L, ?_, fun q ↦ ?_, ?_⟩
  · apply ContinuousLinearMap.ext
    intro q
    rw [ContinuousLinearMap.comp_apply, hL, map_sum, Submodule.starProjection_apply,
      b.orthogonalProjectionOnto_apply_eq_sum, Submodule.coe_sum]
    simp only [map_smul, hIg, Submodule.coe_smul, c, innerSL_apply_apply]
  · rw [hL]
    exact Submodule.sum_mem _ fun j _ ↦ Submodule.smul_mem _ _ (hg j)
  · obtain ⟨t,ht,hlim⟩ := spectralRestriction_trace_tendsto_zero_of_finite_theta_inputs
      a hβ hs φ g hg (fun j ↦ (c j).comp I) ε ρ hε hρ
    refine ⟨t, ?_, hlim⟩
    filter_upwards [ht] with R hR
    obtain ⟨hc,hN,heq⟩ := hR
    refine ⟨hc, ?_⟩
    have he : (mask(β,s,hc)).comp ((act(hβ,hs,φ)).comp (L.comp (I.comp (Ps(a,hβ,hs))))) =
        ∑ j, (((c j).comp I).comp (Ps(a,hβ,hs))).smulRight ((mask(β,s,hc)) ((act(hβ,hs,φ)) (g j))) := by
      apply ContinuousLinearMap.ext
      intro q
      change (mask(β,s,hc)) ((act(hβ,hs,φ)) (L (I ((Ps(a,hβ,hs)) q)))) = _
      simp only [ContinuousLinearMap.comp_apply, hL, map_sum, map_smul, sum_apply,
        ContinuousLinearMap.smulRight_apply]
    rw [he]
    exact ⟨hN,heq⟩


end RiemannMasullo
