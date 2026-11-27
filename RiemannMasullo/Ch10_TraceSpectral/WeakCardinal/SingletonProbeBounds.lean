module

public import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.PolynomialProbeBounds
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a

/-! Fixed-stage necessity for the genuine one-jet geometric readout of §10.4.3.
The probe normalization and the growth of its test seminorms are separate hypotheses.
K-ieren's Theorem 5 in the discussion of [issue #7406](https://github.com/mccorvie/riemann-masullo/issues/7406#issuecomment-7156058239)
gives the earlier polynomial necessity argument. -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set Topology
open scoped NNReal ENNReal NumberField.AdeleRing UniformConvergenceCLM

namespace RiemannMasullo.WeakCardinal

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => continuousIdeleClassNorm F
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "W" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "Q" => spectralSobolevQuotient F a hI hs
local notation "Θ" => globalThetaSobolev F a hI hs
local notation "orbit" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs
local notation "P" => geometricProjection (F := F) a hα hs
local notation "sectionVec(" x ")" => ((Θ).quotientEquivOrthogonal x).val

/-- The native Hardy–Sobolev operator evaluated on one fixed ambient vector depends
continuously and complex-linearly on the full Bruhat input. -/
def hardySobolevTestVectorCLM (u : W) : BruhatCompactSupport C𝔽 →L[ℂ] W where
  toFun φ := orbit φ u
  map_add' φ ψ := by rw [map_add]; rfl
  map_smul' c φ := by rw [map_smul]; rfl
  cont := by
    let B := {t : Set W | Bornology.IsVonNBounded ℂ t}
    let : ContinuousEvalConst (W →Lᵤ[ℂ, B] W) W W :=
      UniformConvergenceCLM.continuousEvalConst (RingHom.id ℂ) W B Bornology.sUnion_isVonNBounded_eq_univ
    exact (continuous_eval_const (F := W →Lᵤ[ℂ, B] W) u).comp (continuous_hardySobolevTestAction μ𝔽 m𝔽 _ _ _ hI hs)

/-- Rank-one native geometric block attached to a single retained jet with quotient
basis vector and coordinate functional. -/
def nativeSingletonBlock (x : Q) (f : StrongDual ℂ Q) (φ : BruhatCompactSupport C𝔽) :
    nuclearEndomorphisms W :=
  ⟨(f.comp (Θ).mkQL).smulRight (P (orbit φ (sectionVec(x)))), smulRight_mem_nuclearEndomorphisms _ _⟩

/-- A Hilbert-valued, continuous and complex-linear realization of the single-block
trace norm. It evaluates the original test action, followed by the geometric projection. -/
def nativeSingletonReadout (x : Q) (f : StrongDual ℂ Q) :
    BruhatCompactSupport C𝔽 →L[ℂ] W :=
  ((‖f.comp (Θ).mkQL‖ : ℝ) : ℂ) • (P).comp (hardySobolevTestVectorCLM hα hs (sectionVec(x)))

theorem norm_nativeSingletonReadout (x : Q) (f : StrongDual ℂ Q) (φ : BruhatCompactSupport C𝔽) :
    ‖nativeSingletonReadout a hα hs x f φ‖ = traceNorm (nativeSingletonBlock a hα hs x f φ) := by
  rw [nativeSingletonBlock, traceNorm_smulRight]
  change ‖((‖f.comp (Θ).mkQL‖ : ℝ) : ℂ) • (P (orbit φ (sectionVec(x))) : W)‖ = _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]

/-- A bound for each fixed test, with no uniformity in the test, suffices for a polynomial
necessity bound on a quantity detected by the moving probes. -/
theorem nativeSingletonCost_polynomial_of_pointwise
    {E J κ : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (p : κ → Seminorm ℂ E) (hp : WithSeminorms p)
    (stage : E →L[ℂ] BruhatCompactSupport C𝔽)
    (x : J → Q) (f : J → StrongDual ℂ Q)
    (hbound : ∀ ψ : E, ∃ M : ℝ, ∀ j, traceNorm (nativeSingletonBlock a hα hs (x j) (f j) (stage ψ)) ≤ M)
    (probe : J → E) (height cost : J → ℝ) (hheight : ∀ j, 0 ≤ height j)
    (hprobe : ∀ k, ∃ C : ℝ≥0, ∃ N : ℕ, ∀ j, p k (probe j) ≤ (C : ℝ) * (1 + height j)^N)
    (hdetect : ∀ j, cost j ≤ traceNorm (nativeSingletonBlock a hα hs (x j) (f j) (stage (probe j)))) :
    ∃ C : ℝ≥0, ∃ N : ℕ, ∀ j, cost j ≤ (C : ℝ) * (1 + height j)^N := by
  let T (j : J) := (nativeSingletonReadout a hα hs (x j) (f j)).comp stage
  have he (j : J) (ψ : E) : ‖T j ψ‖ =
      traceNorm (nativeSingletonBlock a hα hs (x j) (f j) (stage ψ)) :=
    norm_nativeSingletonReadout a hα hs _ _ _
  have hpoint (ψ : E) : ∃ M : ℝ, ∀ j, ‖T j ψ‖ ≤ M := by
    obtain ⟨M, hM⟩ := hbound ψ
    exact ⟨M, fun j ↦ (he j ψ).le.trans (hM j)⟩
  obtain ⟨C, N, h⟩ := polynomial_probe_bound_of_pointwise p hp T hpoint probe height hheight hprobe
  exact ⟨C, N, fun j ↦ (hdetect j).trans ((he j _).symm.le.trans (h j))⟩

/-- The finite-selection hypothesis of §10.4.3.5(2) bounds every individual row at a
one-jet site. Other sites can carry arbitrary numbers of jets. A stage may probe any family
of one-jet sites, and only the chosen test's finite-set bound is needed. -/
theorem nativeSingletonCost_polynomial_of_blockBounds
    {E J Z κ : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [BarrelledSpace ℂ E] (p : κ → Seminorm ℂ E) (hp : WithSeminorms p)
    (stage : E →L[ℂ] BruhatCompactSupport C𝔽)
    (n : Z → ℕ) (x : (z : Z) → Fin (n z) → Q) (f : (z : Z) → Fin (n z) → StrongDual ℂ Q)
    (site : J → Z) (row : (j : J) → Fin (n (site j))) (hone : ∀ j, n (site j) ≤ 1)
    (hbound : ∀ ψ : E, BddAbove (range fun S : Finset Z ↦ traceNorm
      (∑ z ∈ S, ∑ i : Fin (n z), nativeSingletonBlock a hα hs (x z i) (f z i) (stage ψ))))
    (probe : J → E) (height cost : J → ℝ) (hheight : ∀ j, 0 ≤ height j)
    (hprobe : ∀ k, ∃ C : ℝ≥0, ∃ N : ℕ, ∀ j, p k (probe j) ≤ (C : ℝ) * (1 + height j)^N)
    (hdetect : ∀ j, cost j ≤ traceNorm (nativeSingletonBlock a hα hs
      (x (site j) (row j)) (f (site j) (row j)) (stage (probe j)))) :
    ∃ C : ℝ≥0, ∃ N : ℕ, ∀ j, cost j ≤ (C : ℝ) * (1 + height j)^N := by
  classical
  apply nativeSingletonCost_polynomial_of_pointwise a hα hs p hp stage
    (fun j ↦ x (site j) (row j)) (fun j ↦ f (site j) (row j)) _ probe height cost hheight hprobe hdetect
  intro ψ
  obtain ⟨M, hM⟩ := hbound ψ
  refine ⟨M, fun j ↦ ?_⟩
  have : Subsingleton (Fin (n (site j))) := Fin.subsingleton_iff_le_one.mpr (hone j)
  simpa only [Finset.sum_singleton, Fintype.sum_subsingleton _ (row j)] using
    hM (mem_range_self ({site j} : Finset Z))

end RiemannMasullo.WeakCardinal
