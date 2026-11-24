module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # The geometric part of the projective kernel in Theorem 10.4.3.5 -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

/-- Applying a bounded map to every output of convergent projective rectangles gives a Cauchy net. -/
private theorem cauchy_rectangles_map_output {Z J E V : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (jet : (z : Z) → Fin (N z) → J)
    (u : J → E) (v : J → V) (P : V →L[ℂ] V)
    {K : Completion (ProjectiveTensor E V)} (hK : Tendsto (spectralKernelRectangle e N jet u v) atTop (𝓝 K)) :
    Cauchy (Filter.map (spectralKernelRectangle e N jet u (fun i ↦ P (v i))) atTop) := by
  let idE := ContinuousLinearMap.id ℂ E
  let L : ProjectiveTensor E V →L[ℂ] ProjectiveTensor E V :=
    ⟨projectiveTensorMap idE.toLinearMap P.toLinearMap, projectiveTensorMap_continuous idE P⟩
  apply Filter.Tendsto.cauchy_map (a := L.completion K)
  apply ((L.completion.continuous.tendsto K).comp hK).congr
  intro ij
  unfold Function.comp spectralKernelRectangle
  rw [ContinuousLinearMap.completion_apply_coe]
  apply congrArg ((↑) : ProjectiveTensor E V → Completion (ProjectiveTensor E V))
  change projectiveTensorMap idE.toLinearMap P.toLinearMap _ = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact (map_sum (TensorProduct.map idE.toLinearMap P.toLinearMap)
    (fun m : Fin (N z) ↦ u (jet z m) ⊗ₜ[ℂ] v (jet z m)) Finset.univ).trans
    (Finset.sum_congr rfl fun m _ ↦ TensorProduct.map_tmul _ _ _ _)

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)) (ha : 0 < a)
  (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))

local notation "hs₀" => (zero_le_one.trans hs.le)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "Θ₀" => globalThetaSobolev F a hI hs₀
local notation "H(" F ", " a ", " hα ", " hs ")" =>
  spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans (le_of_lt hs))
local notation "Sₐ(" v ")" => ((Θ₀).quotientEquivOrthogonal v).val
local notation "Aφ" => hardySobolevTestAction (ideleClassTamagawaMeasure F) (continuousIdeleClassNorm F)
  (-α) α s hI hs₀ φ
local notation "Gₐ" => geometricProjection (F := F) a hα hs₀
local notation "Pₐ" => spectralProjection (F := F) a hα hs₀
local notation "Dₐ" => spectralSobolevDualEmbedding F a hI hs₀

local notation "order(" χ ", " a ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (χ (z).1))
  (((a + (z).2.1 : ℝ) : ℂ) + ((z).2.2 : ℂ) * Complex.I)
local notation "zeros(" F ", " χ ", " a ", " α ")" => {z : PontryaginDual (ideleClassNorm F).ker × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ, a, z)}
local notation "jetCount(" z ")" => spectralStripMultiplicity α s (z).val.2.1 (order(χ, a, (z).val)).untop₀.toNat
local notation "jets" => SpectralStripJetIndex (F := F) χ a α s

variable (eχ : PontryaginDual (ideleClassNorm F).ker ↪ ℕ) (e : zeros(F, χ, a, α) ↪ ℕ × ℕ)
  (x : SpectralStripJetIndex χ a α s → H(F, a, hα, hs))
  (f : SpectralStripJetIndex χ a α s → StrongDual ℂ H(F, a, hα, hs))
  (hχ : IsSpectralBasepointChoice χ) (he : ∀ z, (e z).1 = eχ z.val.1)
  (horder : ∀ z z' : zeros(F, χ, a, α), z.val.1 = z'.val.1 → (e z).2 ≤ (e z').2 → |z.val.2.2| ≤ |z'.val.2.2|)
  (hb : IsSpectralMarkushevichBasis x f ∧ ∀ j,
    spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans hs.le) (f j) =
    (spectralStripJet_memLp χ hα (zero_le_one.trans hs.le) j).toLp
      (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2))

local notation "rectangles(" output ")" =>
  spectralKernelRectangle e (fun z ↦ jetCount(z))
    (fun z m ↦ (⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩ : jets))
    (fun j ↦ Dₐ (f j)) (output)
local notation "geometricRectangles" => rectangles((fun j ↦ Gₐ (Aφ (Sₐ(x j)))))
local notation "ambientRectangles" => rectangles((fun j ↦ Aφ (Sₐ(x j))))

include ha hχ he horder hb

/-- Paper: Theorem 10.4.3.5(2), p. 472. At positive twist and Sobolev order above one, the
geometric projections of the corrected ambient rectangles are Cauchy in the completed
projective tensor product.
Deviation: For the operator in (10.4.3.45), convolution acts on the orthogonal output lift.
The rectangles use injections of the actual strip zeros and the strict §10.2 boundary cutoff.
Reconstruction: This is the geometric component of the convergence claimed on pp. 472–473,
with the operator order repaired in §10.4.3. The paper gives no separate geometric estimate.
Gap: The quotient estimates control the spectral component only. The bound (10.4.2.34)
on p. 464 gives no bound tending to zero for these projective tails. Nothing in the Lean uses
this statement, and it is not known how it connects with the rest of the proof in Lean; in the
paper it is used on pp. 471–474. -/
theorem spectralStripGeometricKernel_cauchy : Cauchy (Filter.map geometricRectangles atTop) := by
  sorry

/-- Paper: Theorem 10.4.3.5(2)–(3), p. 472. The corrected ambient net converges to a kernel
representing convolution after projection (p. 473) exactly when its geometric rectangles are Cauchy.
Deviation: Both conclusions concern the same ambient rectangles, with convolution on the output
and the repaired indexing of §10.4.3.
Reconstruction: The equivalence identifies exactly what the geometric estimate on pp. 471–473 must supply. -/
theorem spectralStripAmbientKernel_exists_iff_geometric_cauchy :
    (∃ K, Tendsto ambientRectangles atTop (𝓝 K) ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀ K = (Aφ).comp Pₐ) ↔
      Cauchy (Filter.map geometricRectangles atTop) := by
  constructor
  · rintro ⟨K, hK, _⟩
    exact cauchy_rectangles_map_output e _ _ _ (fun j ↦ Aφ (Sₐ(x j))) Gₐ hK
  · intro hgeom
    exact (spectralStripAmbientKernel_tendsto (F := F) a hα hs φ ha χ eχ e x f hχ he horder hb hgeom).imp
      fun K hK ↦ ⟨hK, spectralStripAmbientKernel_operator (F := F) a hα hs φ ha χ eχ e x f hχ he horder hb K hK⟩

/-- Paper: Theorem 10.4.3.5(2)–(3), p. 472. The isolated geometric Cauchy estimate supplies
the limit and the operator identity (10.4.3.45) on p. 473.
Deviation: The ambient tensors use the repaired output action and strip indexing of §10.4.3. -/
theorem spectralStripAmbientKernel_exists :
    ∃ K, Tendsto ambientRectangles atTop (𝓝 K) ∧
      sobolevProjectiveKernelOperator (F := F) hα hs₀ K = (Aφ).comp Pₐ :=
  (spectralStripAmbientKernel_exists_iff_geometric_cauchy a hα hs φ ha χ eχ e x f hχ he horder hb).mpr
    (spectralStripGeometricKernel_cauchy a hα hs φ ha χ eχ e x f hχ he horder hb)

end RiemannMasullo.Isolated
