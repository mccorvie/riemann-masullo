module
public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_GeometricBlocks
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_StripAngularGram
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.FiberProjection
import RiemannMasullo.ForMathlib.Topology.Algebra.InfiniteSum.RectangleRows

/-! # A divisor-product obstruction to geometric rectangle convergence

The prescribed rectangle Cauchy property already controls every fixed angular
row. Orthogonal projection onto that row, followed by the tensor-to-operator map,
bounds its individual blocks. A one-jet block has equal trace and operator norms.

Combining this with the singleton divisor-product estimate of PR #7598 (which
extends PR #7560) and its fixed-support Banach–Steinhaus argument gives a necessary
inverse-polynomial lower bound for the complete neighboring divisor product.
This uses neither unconditional finite-family bounds nor a large angular index.
It does not establish that the Hecke zeros satisfy or violate this condition.
-/

@[expose] public noncomputable section
open Filter Set UniformSpace
open scoped BigOperators InnerProductSpace TensorProduct Topology
namespace RiemannMasullo.Isolated
attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

private theorem projectiveRectangle_fiber_operator_bound
    {X H J Z : Type*}
    [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
    [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H]
    (D : StrongDual ℂ H ≃L[ℂ] X)
    (e : Z ↪ ℕ × ℕ) (N : Z → ℕ) (j : (z : Z) → Fin (N z) → J)
    (u : J → X) (v : J → H) (f : J → StrongDual ℂ H)
    (hD : ∀ k, D (f k) = u k) (row : J → ℕ)
    (hrow : ∀ z m, row (j z m) = (e z).1)
    (horth : ∀ k l, row k ≠ row l → ⟪u k, u l⟫_ℂ = 0)
    (hc : Cauchy (Filter.map (spectralKernelRectangle e N j u v) atTop)) (i : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z, (e z).1 = i →
      ‖∑ m : Fin (N z), (f (j z m)).smulRight (v (j z m))‖ ≤ B := by
  classical
  let term (k : J) : ProjectiveTensor X H := u k ⊗ₜ[ℂ] v k
  let term' (k : J) : ProjectiveTensor (StrongDual ℂ H) H := f k ⊗ₜ[ℂ] v k
  obtain ⟨P, hP⟩ := exists_projection_of_orthogonal_fibers u row horth i
  let Q : ProjectiveTensor X H →L[ℂ] ProjectiveTensor X H :=
    ⟨projectiveTensorMap P.toLinearMap (ContinuousLinearMap.id ℂ H).toLinearMap,
      projectiveTensorMap_continuous P (ContinuousLinearMap.id ℂ H)⟩
  let C : ProjectiveTensor X H →L[ℂ] ProjectiveTensor (StrongDual ℂ H) H :=
    ⟨projectiveTensorMap D.symm.toLinearMap (ContinuousLinearMap.id ℂ H).toLinearMap,
      projectiveTensorMap_continuous D.symm.toContinuousLinearMap (ContinuousLinearMap.id ℂ H)⟩
  let O := (completedProjectiveTensorToOperators (E := H) (F := H)).comp C.completion
  let L := O.comp Q.completion
  have hQ (k : J) : Q (term k) = if row k = i then term k else 0 := by
    change P (u k) ⊗ₜ[ℂ] v k = _
    rw [hP]
    split_ifs
    · rfl
    · change (0 : X) ⊗ₜ[ℂ] v k = (0 : X ⊗[ℂ] H)
      exact TensorProduct.zero_tmul _ _
  have hC (k : J) : C (term k) = term' k := by
    change D.symm (u k) ⊗ₜ[ℂ] v k = _
    rw [← hD k, D.symm_apply_apply]
  have hL (k : J) : L (Completion.toComplL (S := ℂ) (term k)) =
      if row k = i then (f k).smulRight (v k) else 0 := by
    change O (Q.completion (↑(term k))) = _
    rw [ContinuousLinearMap.completion_apply_coe, hQ]
    split_ifs with hk
    · change completedProjectiveTensorToOperators (C.completion (↑(term k))) = _
      rw [ContinuousLinearMap.completion_apply_coe, hC, completedProjectiveTensorToOperators_coe]
      exact ContinuousLinearMap.ext fun x ↦ tensorToFiniteRank_tmul _ _ x
    · simp
  let a (z : Z) : Completion (ProjectiveTensor X H) :=
    Completion.toComplL (S := ℂ) (∑ m : Fin (N z), term (j z m))
  let b (z : Z) : H →L[ℂ] H := ∑ m : Fin (N z), (f (j z m)).smulRight (v (j z m))
  have hrect (p : ℕ × ℕ) : spectralKernelRectangle e N j u v p =
      ∑ z ∈ ((Finset.Iic p.1).product (Finset.Iic p.2)).preimage e e.injective.injOn, a z := by
    exact map_sum (Completion.toComplL (S := ℂ) : ProjectiveTensor X H →L[ℂ] _) _ _
  have hc' : CauchySeq (fun p : ℕ × ℕ ↦
      ∑ z ∈ ((Finset.Iic p.1).product (Finset.Iic p.2)).preimage e e.injective.injOn, a z) := by
    change CauchySeq (spectralKernelRectangle e N j u v) at hc
    rw [funext hrect] at hc
    exact hc
  apply norm_fiber_bounded_of_cauchy_rectangles e a b i L ?_ hc'
  intro z
  change (L.comp (Completion.toComplL (S := ℂ))) (∑ m : Fin (N z), term (j z m)) = _
  rw [map_sum]
  change (∑ m : Fin (N z), L (Completion.toComplL (S := ℂ) (term (j z m)))) = _
  simp only [hL, hrow]
  by_cases hz : (e z).1 = i <;> simp [hz, b]

private theorem geometricSingleton_traceNorm_eq_opNorm
    {H I : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [Fintype I] [Subsingleton I] (i : I) (f : I → StrongDual ℂ H) (v : I → H) :
    traceNorm (∑ k, (⟨(f k).smulRight (v k), smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms H)) =
      ‖∑ k, (f k).smulRight (v k)‖ := by
  rw [Fintype.sum_subsingleton _ i, Fintype.sum_subsingleton _ i, traceNorm_smulRight]
  exact (ContinuousLinearMap.norm_smulRight_apply _ _).symm

open MeasureTheory NumberField
open scoped NNReal NumberField.AdeleRing
set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
variable (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 1 < s)
  (φ : BruhatCompactSupport (IdeleClassGroup (𝓞 F) F))
  (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (x : SpectralStripJetIndex χ a α s →
    spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans hs.le))
  (f : SpectralStripJetIndex χ a α s → StrongDual ℂ
    (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) (zero_le_one.trans hs.le)))

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "hs₀" => (zero_le_one.trans hs.le)
local notation "hI" => (neg_nonpos.mpr hα).trans hα
local notation "W₀" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s
local notation "W₀'" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α s true
local notation "Θ₀" => globalThetaSobolev F a hI hs₀
local notation "H₀" => spectralSobolevQuotient F a hI hs₀
local notation "Sₐ(" v ")" => ((Θ₀).quotientEquivOrthogonal v).val
local notation "Aφ" => hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs₀ φ
local notation "Gₐ" => geometricProjection (F := F) a hα hs₀
local notation "Pₐ" => spectralProjection (F := F) a hα hs₀
local notation "Dₐ" => spectralSobolevDualEmbedding F a hI hs₀
local notation "Tₐ" => (modulatedIntervalSobolev_dual m𝔽
  (⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩ : IsModulation m𝔽)
  μ𝔽 (-α) α s hI hs₀).exists.choose

local notation "order(" χ ", " a ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL (χ (z).1))
  (((a + (z).2.1 : ℝ) : ℂ) + ((z).2.2 : ℂ) * Complex.I)
local notation "zeros(" F ", " χ ", " a ", " α ")" => {z : PontryaginDual (ideleClassNorm F).ker × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ, a, z)}
local notation "jetCount(" z ")" => spectralStripMultiplicity α s (z).val.2.1 (order(χ, a, (z).val)).untop₀.toNat
local notation "jets" => SpectralStripJetIndex (F := F) χ a α s
local notation "jet(" z ", " m ")" =>
  (⟨((z).val.1, (z).val.2.1, (z).val.2.2, (m).val), (m).isLt⟩ : jets)
local notation "stripU(" j ")" => (spectralStripJet_memLp χ hα hs₀ j).toLp
  (spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)
local notation "geometricBlock(" z ")" =>
  (∑ m : Fin (jetCount(z)),
    (⟨((f jet(z, m)).comp (Θ₀).mkQL).smulRight (Gₐ (Aφ (Sₐ(x jet(z, m))))),
      smulRight_mem_nuclearEndomorphisms _ _⟩ : nuclearEndomorphisms _))

variable (eχ : PontryaginDual (ideleClassNorm F).ker ↪ ℕ)
  (e : zeros(F, χ, a, α) ↪ ℕ × ℕ)
  (hχ : IsSpectralBasepointChoice χ) (he : ∀ z : zeros(F, χ, a, α), (e z).1 = eχ z.val.1)

local notation "geometricRectangles" =>
  spectralKernelRectangle e (fun z ↦ jetCount(z)) (fun z m ↦ jet(z, m))
    (fun j ↦ Dₐ (f j)) (fun j ↦ Gₐ (Aφ (Sₐ(x j))))

include hχ he

/-- Paper: Theorem 10.4.3.5(2), pp. 471–473. Cauchy convergence of the prescribed
geometric rectangles bounds the operator norms of all blocks in each fixed angular
character, including characters whose first enumeration index is small.
Reconstruction: An orthogonal angular projection selects that row of the tensor sum. -/
theorem spectralStripGeometricKernel_cauchy_forces_angular_block_opNorm_bound
    (hjets : ∀ j : jets, Dₐ (f j) = stripU(j))
    (hc : Cauchy (Filter.map geometricRectangles atTop))
    (ω : PontryaginDual (ideleClassNorm F).ker) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ z : zeros(F, χ, a, α), z.val.1 = ω →
      ‖(geometricBlock(z)).val‖ ≤ B := by
  have hc' : Cauchy (Filter.map
      (spectralKernelRectangle e (fun z ↦ jetCount(z)) (fun z m ↦ jet(z, m))
        (fun j : jets ↦ stripU(j)) (fun j ↦ Gₐ (Aφ (Sₐ(x j))))) atTop) := by
    exact Eq.mp (congrArg (fun u : jets → W₀' ↦ Cauchy (Filter.map
      (spectralKernelRectangle e (fun z ↦ jetCount(z)) (fun z m ↦ jet(z, m)) u
        (fun j ↦ Gₐ (Aφ (Sₐ(x j))))) atTop)) (funext hjets)) hc
  obtain ⟨B, hB, hbound⟩ := projectiveRectangle_fiber_operator_bound
    (X := W₀') (H := W₀) (J := jets) (Z := zeros(F, χ, a, α)) (Tₐ).toContinuousLinearEquiv
    e (fun z ↦ jetCount(z)) (fun z m ↦ jet(z, m))
    (fun j : jets ↦ stripU(j)) (fun j ↦ Gₐ (Aφ (Sₐ(x j)))) (fun j ↦ (f j).comp (Θ₀).mkQL)
    (fun j ↦ hjets j) (fun j : jets ↦ eχ j.val.1)
    (fun z _ ↦ (he z).symm) (by
      intro j k hjk
      exact spectralStripJet_inner_eq_zero_of_angular_ne (F := F) (a := a) hα hs₀ χ hχ j k
        (fun h ↦ hjk (congrArg eχ h))) hc' (eχ ω)
  refine ⟨B, hB, fun z hz ↦ ?_⟩
  have h := hbound z ((he z).trans (congrArg eχ hz))
  simpa only [Submodule.coe_sum] using h

/-- Paper: Theorem 10.4.3.5(2), pp. 471–473. The prescribed rectangle Cauchy
property bounds the trace norms of every one-jet block of a fixed character.
No unconditional finite-family bound is assumed. -/
theorem spectralStripGeometricKernel_cauchy_forces_simple_blocks_bounded
    (hjets : ∀ j : jets, Dₐ (f j) = stripU(j))
    (hc : Cauchy (Filter.map geometricRectangles atTop))
    (ω : PontryaginDual (ideleClassNorm F).ker) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (z : zeros(F, χ, a, α)), z.val.1 = ω →
      ∀ (_ : Fin (jetCount(z))), jetCount(z) ≤ 1 → traceNorm (geometricBlock(z)) ≤ B := by
  obtain ⟨B, hB, hbound⟩ := spectralStripGeometricKernel_cauchy_forces_angular_block_opNorm_bound
    a hα hs φ χ x f eχ e hχ he hjets hc ω
  refine ⟨B, hB, fun z hz m hcount ↦ ?_⟩
  let : Subsingleton (Fin (jetCount(z))) := Fin.subsingleton_iff_le_one.mpr hcount
  have heq : traceNorm (geometricBlock(z)) = ‖(geometricBlock(z)).val‖ := by
    simpa only [Submodule.coe_sum] using geometricSingleton_traceNorm_eq_opNorm (H := W₀) m
      (fun k : Fin (jetCount(z)) ↦ (f jet(z, k)).comp (Θ₀).mkQL)
      (fun k : Fin (jetCount(z)) ↦ Gₐ (Aφ (Sₐ(x jet(z, k)))))
  rw [heq]
  exact hbound z hz


local notation "Xlog" => logIdeleClassNorm F
local notation "νrec" => intervalSobolevMeasure μ𝔽 Xlog (-α) α s true
local notation "envelope" => (fun g : C𝔽 ↦ (Real.exp (α * |Xlog g|) : ℂ))
local notation "center(" z ")" => (((z).val.2.1 : ℂ) + ((z).val.2.2 : ℂ) * Complex.I)
local notation "ordAt(" η ", " w ")" =>
  (meromorphicOrderAt (continuedCompletedHeckeL η) ((a : ℂ) + w)).untop₀.toNat
local notation "firstJet(" z ")" => spectralZeroJet (F := F) (χ (z).val.1) (z).val.2.1 (z).val.2.2 1

/-- Paper: Theorem 10.4.3.5(2), pp. 471–473. For a fixed angular character,
Cauchy convergence of the prescribed geometric rectangles controls the first
Mellin moment by the complete neighboring divisor product.
Reconstruction: Combine angular row selection with the singleton Schwarz estimate
of PR #7598, which builds on the first-jet obstruction of PR #7560. -/
theorem spectralStripGeometricKernel_cauchy_forces_full_zero_product
    (hjets : ∀ j : jets, Dₐ (f j) = stripU(j))
    (hbasis : IsSpectralMarkushevichBasis x f)
    (hcauchy : Cauchy (Filter.map geometricRectangles atTop))
    (ω : PontryaginDual (ideleClassNorm F).ker) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (z : zeros(F, χ, a, α)), z.val.1 = ω →
      ∀ (_ : Fin (jetCount(z))), jetCount(z) ≤ 1 →
      ∀ r : ℝ, 0 < r → |z.val.2.1| + r ≤ α →
      ‖∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽‖ ≤ (C / r) *
        ∏ w ∈ geometricClusterNeighbors a (χ z.val.1) (center(z)) r,
          (‖w - center(z)‖ / r) ^ ordAt(χ z.val.1, w) := by
  obtain ⟨B, hB, hbound⟩ := spectralStripGeometricKernel_cauchy_forces_simple_blocks_bounded
    a hα hs φ χ x f eχ e hχ he hjets hcauchy ω
  obtain ⟨c, hc, hlow⟩ := spectralStripJet_lowerBound (a := a) χ hχ hα hs
  let D := (eLpNorm envelope 2 νrec).toReal
  have hD : 0 ≤ D := ENNReal.toReal_nonneg
  refine ⟨D * B / c, by positivity, fun z hz m hcount r hr hmargin ↦ ?_⟩
  have hc' : c ≤ ‖(f jet(z, m)).comp (Θ₀).mkQL‖ := by
    calc c ≤ ‖stripU(jet(z, m))‖ := hlow _
         _ = ‖Dₐ (f jet(z, m))‖ := (congrArg norm (hjets _)).symm
         _ = _ := (Tₐ).norm_map _
  let S := geometricClusterNeighbors a (χ z.val.1) (center(z)) r
  let P := ∏ w ∈ S, (‖w - center(z)‖ / r) ^ ordAt(χ z.val.1, w)
  have hP : 0 ≤ P := Finset.prod_nonneg (fun w _ ↦ pow_nonneg (div_nonneg (norm_nonneg _) hr.le) _)
  have hprod := spectralStripGeometricKernel_block_zero_product a hα hs φ χ x f
    ⟨hbasis, hjets⟩ z m hcount hr hmargin S
    (fun w hw ↦ ((mem_geometricClusterNeighbors a _ w _ r).mp hw).1)
    (fun w hw ↦ ((mem_geometricClusterNeighbors a _ w _ r).mp hw).2.1)
  apply (mul_le_mul_iff_left₀ hc).mp
  calc
    _ ≤ ‖∫ g : C𝔽, φ.val g * firstJet(z) g ∂μ𝔽‖ * ‖(f jet(z, m)).comp (Θ₀).mkQL‖ :=
      mul_le_mul_of_nonneg_left hc' (norm_nonneg _)
    _ ≤ (D / r) * traceNorm (geometricBlock(z)) * P := hprod
    _ ≤ (D / r) * B * P := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hbound z hz m hcount) (div_nonneg hD hr.le)) hP
    _ = _ := by dsimp only [P, S]; field_simp

local notation "simpleSites(" η ", " A ")" =>
  {w : ℂ // |w.re| ≤ A ∧ meromorphicOrderAt (continuedCompletedHeckeL η) ((a : ℂ) + w) = 1}
local notation "rectanglesOf(" ψ ")" =>
  spectralKernelRectangle e (fun z ↦ jetCount(z)) (fun z m ↦ jet(z, m))
    (fun j ↦ Dₐ (f j))
    (fun j ↦ Gₐ ((hardySobolevTestAction μ𝔽 m𝔽 (-α) α s hI hs₀ ψ) (Sₐ(x j))))

/-- Paper: Theorem 10.4.3.5(2), pp. 471–473. If the paper's prescribed geometric
rectangles are Cauchy for every compact Bruhat test, then in each fixed character
the complete neighboring divisor product at a simple interior zero is bounded
below by an inverse polynomial in its height.
Reconstruction: This uses the Cauchy property itself, without the stronger
arbitrary-finite-family bound in #7406. The angular projection controls the entire
fixed character row, so no lower bound on its enumeration index is required.
The product and fixed-support modulation argument are from PR #7598. -/
theorem spectralStripGeometricKernel_allTests_cauchy_forces_polynomial_cluster_product
    (hjets : ∀ j : jets, Dₐ (f j) = stripU(j))
    (hbasis : IsSpectralMarkushevichBasis x f)
    (hcauchy : ∀ ψ : BruhatCompactSupport C𝔽, Cauchy (Filter.map rectanglesOf(ψ) atTop))
    (ω : PontryaginDual (ideleClassNorm F).ker) (A R : ℝ) (hR : 0 < R) (hmargin : A + R ≤ α) :
    ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ v : simpleSites(χ ω, A),
      c / (1 + |v.val.im|) ^ N ≤ ∏ w ∈ geometricClusterNeighbors a (χ ω) v.val R,
        (‖w - v.val‖ / R) ^ ordAt(χ ω, w) := by
  apply GeometricBaire.ideleFirstMoment_denominator_lower (χ ω)
    (fun v : simpleSites(χ ω, A) ↦ v.val.re) (fun v ↦ v.val.im)
    (fun v ↦ ∏ w ∈ geometricClusterNeighbors a (χ ω) v.val R, (‖w - v.val‖ / R) ^ ordAt(χ ω, w))
    (fun v ↦ v.property.1)
  · intro v
    refine Finset.prod_pos fun w hw ↦ pow_pos (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr ?_)) hR) _
    exact ((mem_geometricClusterNeighbors a _ _ _ _).mp hw).1
  · intro ψ
    obtain ⟨C, _, hC⟩ := spectralStripGeometricKernel_cauchy_forces_full_zero_product
      a hα hs ψ χ x f eχ e hχ he hjets hbasis (hcauchy ψ) ω
    refine ⟨C / R, fun v ↦ ?_⟩
    have hvR : |v.val.re| + R ≤ α := by linarith [v.property.1]
    have hv : v.val.re ∈ Ioo (-α) α := abs_lt.mp (by linarith)
    have eqv : (((a + v.val.re : ℝ) : ℂ) + (v.val.im : ℂ) * Complex.I) = (a : ℂ) + v.val := by
      rw [Complex.ofReal_add, add_assoc, Complex.re_add_im]
    have ho : meromorphicOrderAt (continuedCompletedHeckeL (χ ω))
        (((a + v.val.re : ℝ) : ℂ) + (v.val.im : ℂ) * Complex.I) = 1 := eqv ▸ v.property.2
    let z : zeros(F, χ, a, α) := ⟨(ω, v.val.re, v.val.im),
      ⟨⟨hv.1.le, hv.2.le⟩, by rw [ho]; norm_num⟩⟩
    have hn : jetCount(z) = 1 := by
      change spectralStripMultiplicity α s v.val.re _ = 1
      rw [spectralStripMultiplicity_interior hv, ho]; rfl
    let m : Fin (jetCount(z)) := ⟨0, by rw [hn]; decide⟩
    simpa only [z, Complex.re_add_im] using hC z rfl m hn.le R hR hvR

end RiemannMasullo.Isolated
