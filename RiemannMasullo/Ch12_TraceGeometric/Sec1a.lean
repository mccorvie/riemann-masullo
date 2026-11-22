module

public import RiemannMasullo.AppA_AlgebraicNT.Sec5b
public import RiemannMasullo.AppC_LCTVS.Sec3b
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Smoothenings along the diagonal

Masullo, §12.1.1, pp. 498–501, through Theorem 12.1.1.2.
Regular points are those of `dSequenceRegularSet` from Appendix A.5.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal NNReal

namespace RiemannMasullo

section Smoothening

variable {G : Type*} [CommGroup G] [MeasurableSpace G]

/-- Paper: Definition 12.1.1.1, p. 498. The smoothening is the limit of the
translated Haar averages at every regular point and zero elsewhere. The paper
applies this formula to locally Haar-integrable functions and Borel D′-sequences. -/
def dSequenceSmootheningOrZero (μ : Measure G) (U : ℕ → Set G) (φ : G → ℂ) (x : G) : ℂ :=
  open Classical in
  if hx : x ∈ dSequenceRegularSet μ U φ then dSequenceSmoothening μ U φ ⟨x, hx⟩ else 0

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Paper: Definition 12.1.1.1, p. 498. A constant function smoothens to the same
constant at every point. -/
theorem dSequenceSmootheningOrZero_const [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {U : ℕ → Set G} (hU : IsDPrimeSequence μ U) (c : ℂ) :
    dSequenceSmootheningOrZero μ U (fun _ ↦ c) = fun _ ↦ c := by
  funext x
  have havg (n : ℕ) : dSequenceAverage μ (U n) (fun _ ↦ c) x = c := by
    obtain ⟨_, _, hpos, hfin⟩ := hU.1.1 n
    unfold dSequenceAverage
    apply setAverage_const <;> rw [measure_smul]
    · exact hpos.ne'
    · exact hfin.ne
  have hlim : Tendsto (fun n ↦ dSequenceAverage μ (U n) (fun _ ↦ c) x) atTop (𝓝 c) := by
    simpa only [havg] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c))
  have hx : x ∈ dSequenceRegularSet μ U (fun _ ↦ c) := ⟨c, hlim⟩
  simpa only [dSequenceSmootheningOrZero, dite_eq_left hx, dSequenceSmoothening] using hlim.limUnder_eq

-- TODO(paper-gap): The Euclidean example on p. 498 needs positive radii tending to zero.

/-- Paper: §12.1.1, p. 499. Smoothen a kernel using the sequence of product
sets and product Haar measure. -/
def dSequenceKernelSmoothening (μ : Measure G) (U : ℕ → Set G) (k : G × G → ℂ) :
    G × G → ℂ :=
  dSequenceSmootheningOrZero (μ.prod μ) (fun n ↦ U n ×ˢ U n) k

/-- Paper: §12.1.1, p. 499. A constant kernel is unchanged by product smoothening. -/
theorem dSequenceKernelSmoothening_const [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {U : ℕ → Set G} (hU : IsDPrimeSequence μ U) (c : ℂ) :
    dSequenceKernelSmoothening μ U (fun _ ↦ c) = fun _ ↦ c := by sorry

end Smoothening

section DiagonalTrace

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
  {U : ℕ → Set G} {f : G → ℝ≥0} {k : Lp ℂ 2 (ν.prod ν)}
  {κ : G × G → ℂ} (hκ : κ =ᵐ[ν.prod ν] k)
  (hU : IsDPrimeSequence μ U) (hBorel : ∀ n, MeasurableSet (U n))
  (hf : Continuous f) (hf_pos : ∀ x, 0 < f x) (hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
  (hT : IsNuclearOperator (integralKernelOperator ν k).val)

include hU hBorel hf hf_pos hν hT hκ

/-- Paper: Theorem 12.1.1.2, p. 499. For Haar-almost every `x`, the product
averages of the chosen kernel representative converge at `(x, x)`. -/
theorem ae_diagonal_mem_dSequenceRegularSet :
    ∀ᵐ x ∂μ, (x, x) ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) κ := by sorry

/-- Paper: Theorem 12.1.1.2(1), p. 499. The smoothened function represents the
same Hilbert-Schmidt kernel in the weighted product measure. -/
theorem dSequenceKernelSmoothening_ae_eq :
    dSequenceKernelSmoothening μ U κ =ᵐ[ν.prod ν] (k : G × G → ℂ) := by sorry

-- TODO(paper-gap): The proof on p. 500 uses projections onto individual eigenspaces
-- as if they exhausted the operator. Cumulative spectral projections are needed.
-- The reduction to positive operators also requires a common full-measure set of
-- diagonal regularity, where linearity of the limit applies.
/-- Paper: Theorem 12.1.1.2(1), p. 499. The smoothened diagonal is absolutely
integrable for the weighted measure, and its integral equals the nuclear trace. -/
theorem integral_dSequenceKernelSmoothening_diagonal :
    Integrable (fun x ↦ dSequenceKernelSmoothening μ U κ (x, x)) ν ∧
      (∫ x, dSequenceKernelSmoothening μ U κ (x, x) ∂ν) =
        hilbertTrace ⟨(integralKernelOperator ν k).val, hT⟩ := by sorry

-- TODO(paper-gap): The proof on p. 501 uses Corollary A.5.4.3 at all regular
-- points. See the rank-one counterexample in Sec1a_Printed.
/-- Paper: Theorem 12.1.1.2(2), p. 499. A compactly supported continuous
multiplier commutes with kernel smoothening almost everywhere for product Haar measure.
Deviation: The printed pointwise identity is restricted to product-almost-everywhere
equality. -/
theorem dSequenceKernelSmoothening_mul_continuous (ρ : G → ℂ)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    let kρ := fun p : G × G ↦ ρ p.1 * κ p
    dSequenceKernelSmoothening μ U kρ =ᵐ[μ.prod μ]
      (fun p ↦ ρ p.1 * dSequenceKernelSmoothening μ U κ p) := by sorry

/-- Paper: Theorem 12.1.1.2(2), p. 499. Along the diagonal, a compactly
supported continuous multiplier commutes with kernel smoothening for Haar-almost every center.
Deviation: The printed pointwise identity is restricted to almost-everywhere equality
in the Haar measure on the diagonal. -/
theorem dSequenceKernelSmoothening_mul_continuous_diagonal (ρ : G → ℂ)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) :
    let kρ := fun p : G × G ↦ ρ p.1 * κ p
    ∀ᵐ x ∂μ, dSequenceKernelSmoothening μ U kρ (x, x) =
      ρ x * dSequenceKernelSmoothening μ U κ (x, x) := by sorry

/-- Paper: Theorem 12.1.1.2(2), p. 499. Multiplying either representative by
the bounded symbol in the target variable gives a kernel of the composed
operator. The multiplier is pointwise multiplication on L² classes. -/
theorem integralKernelOperator_mul_dSequenceKernelSmoothening (ρ : Lp ℂ ∞ ν) :
    let Mρ := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 ρ
    ∃ K : Lp ℂ 2 (ν.prod ν),
      (integralKernelOperator ν K).val = Mρ * (integralKernelOperator ν k).val ∧
        (K : G × G → ℂ) =ᵐ[ν.prod ν] (fun p ↦ ρ p.1 * κ p) ∧
        (K : G × G → ℂ) =ᵐ[ν.prod ν] (fun p ↦ ρ p.1 * dSequenceKernelSmoothening μ U κ p) :=
  by sorry

/-- Paper: Theorem 12.1.1.2(2), p. 499. The weighted integral of the
smoothened diagonal against an essentially bounded symbol equals the trace
of the operator followed by multiplication by that symbol. -/
theorem integral_mul_dSequenceKernelSmoothening_diagonal (ρ : Lp ℂ ∞ ν) :
    let Mρ := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 ρ
    let T : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨(integralKernelOperator ν k).val, hT⟩
    Integrable (fun x ↦ ρ x * dSequenceKernelSmoothening μ U κ (x, x)) ν ∧
      (∫ x, ρ x * dSequenceKernelSmoothening μ U κ (x, x) ∂ν) =
        hilbertTrace ⟨Mρ * T.val, mul_mem_nuclearEndomorphisms_left Mρ T⟩ := by sorry

section FiniteRank

variable (ks : ℕ → Lp ℂ 2 (ν.prod ν)) (κs : ℕ → G × G → ℂ)
  (hκs : ∀ n, κs n =ᵐ[ν.prod ν] ks n)
  (hrank : ∀ n, FiniteDimensional ℂ (integralKernelOperator ν (ks n)).val.toLinearMap.range)
  (hSn : ∀ n, IsNuclearOperator (integralKernelOperator ν (ks n)).val)
  (hS1 : Tendsto (fun n ↦ traceNorm
    ((⟨(integralKernelOperator ν (ks n)).val, hSn n⟩ : nuclearEndomorphisms (Lp ℂ 2 ν)) -
      ⟨(integralKernelOperator ν k).val, hT⟩)) atTop (𝓝 0))
  (hS2 : Tendsto (fun n ↦ schattenNorm
    (integralKernelOperator ν (ks n) - integralKernelOperator ν k)) atTop (𝓝 0))

include hκs hrank hS1 hS2

/-- Paper: Theorem 12.1.1.2(3), p. 499. Under trace-norm and Hilbert-Schmidt
convergence of the finite-rank operators, their kernels converge in weighted
product L². The smoothenings represent the same sequence and limit there. -/
theorem tendsto_dSequenceKernelSmoothening_L2 :
    Tendsto ks atTop (𝓝 k) ∧
      (∀ n, dSequenceKernelSmoothening μ U (κs n) =ᵐ[ν.prod ν] (ks n : G × G → ℂ)) ∧
      dSequenceKernelSmoothening μ U κ =ᵐ[ν.prod ν] (k : G × G → ℂ) := by sorry

/-- Paper: Theorem 12.1.1.2(3), p. 499. The smoothened diagonals converge
weakly in weighted L¹, expressed by testing against all weighted L∞ classes. -/
theorem tendsto_dSequenceKernelSmoothening_diagonal_weak :
    let ds := fun n x ↦ dSequenceKernelSmoothening μ U (κs n) (x, x)
    let d := fun x ↦ dSequenceKernelSmoothening μ U κ (x, x)
    (∀ n, Integrable (ds n) ν) ∧ Integrable d ν ∧
      ∀ ρ : Lp ℂ ∞ ν, Tendsto (fun n ↦ ∫ x, ρ x * ds n x ∂ν) atTop
        (𝓝 (∫ x, ρ x * d x ∂ν)) := by sorry

end FiniteRank

end DiagonalTrace

section Basis

variable {G : Type*} [MeasurableSpace G]

/-- Paper: (12.1.1.4)–(12.1.1.5), p. 499. The bilinear pairing between the
weighted and reciprocal-weighted L² spaces integrates their product against Haar measure. -/
def weightedL2Duality (μ : Measure G) {ν νdual : Measure G} {f : G → ℝ≥0}
    (_hf : Measurable f) (_hf_pos : ∀ x, 0 < f x)
    (_hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
    (_hνdual : νdual = μ.withDensity (fun x ↦ ↑((f x)⁻¹)))
    (u : Lp ℂ 2 ν) (v : Lp ℂ 2 νdual) : ℂ :=
  ∫ x, u x * v x ∂μ

/-- Paper: (12.1.1.5), p. 499. At unit weight the bilinear pairing with a
complex conjugate gives the squared L² norm. -/
theorem weightedL2Duality_conj (μ : Measure G) (u v : Lp ℂ 2 μ)
    (hv : (v : G → ℂ) =ᵐ[μ] fun x ↦ conj (u x)) :
    weightedL2Duality μ (f := fun _ ↦ 1) measurable_const (fun _ ↦ zero_lt_one)
      (by simp) (by simp) u v = (‖u‖ ^ 2 : ℝ) := by sorry

/-- Paper: (12.1.1.4)–(12.1.1.5), p. 499. Each continuous linear functional on
the weighted L² space has a unique representing vector for the reciprocal weight.
Deviation: The isometry implicit in the pairing is explicit here so it can
supply the dual basis and the transpose used in part (4). -/
theorem weightedL2Duality_equiv (μ : Measure G) {ν νdual : Measure G} {f : G → ℝ≥0}
    (hf : Measurable f) (hf_pos : ∀ x, 0 < f x)
    (hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
    (hνdual : νdual = μ.withDensity (fun x ↦ ↑((f x)⁻¹))) :
    ∃! J : StrongDual ℂ (Lp ℂ 2 ν) ≃ₗᵢ[ℂ] Lp ℂ 2 νdual, ∀ ℓ u,
      Integrable (fun x ↦ u x * J ℓ x) μ ∧
        weightedL2Duality μ hf hf_pos hν hνdual u (J ℓ) = ℓ u := by sorry

/-- Paper: (12.1.1.6), p. 499. The partial kernel is the sum through index
`N` of the basis vector in the target variable times the transposed dual
vector divided by the weight in the source variable. -/
def schauderKernelPartialSum {ν νdual : Measure G} (f : G → ℝ≥0)
    (φ : ℕ → Lp ℂ 2 ν) (θ : ℕ → Lp ℂ 2 νdual) (transpose : Lp ℂ 2 νdual →L[ℂ] Lp ℂ 2 νdual)
    (N : ℕ) (p : G × G) : ℂ :=
  ∑ m ∈ Finset.range (N + 1), (transpose (θ m) p.2 / (f p.2 : ℂ)) * φ m p.1

/-- Paper: (12.1.1.6), p. 499. The zeroth partial kernel consists of the
first basis term with its reciprocal weight in the source variable. -/
theorem schauderKernelPartialSum_zero {ν νdual : Measure G} (f : G → ℝ≥0)
    (φ : ℕ → Lp ℂ 2 ν) (θ : ℕ → Lp ℂ 2 νdual) (transpose : Lp ℂ 2 νdual →L[ℂ] Lp ℂ 2 νdual)
    (x y : G) :
    schauderKernelPartialSum f φ θ transpose 0 (x, y) =
      (transpose (θ 0) y / (f y : ℂ)) * φ 0 x := by sorry

end Basis

section SchauderApproximation

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {μ ν : Measure G} [μ.IsHaarMeasure] [IsFiniteMeasureOnCompacts ν] [ν.InnerRegular]
  {U : ℕ → Set G} {f : G → ℝ≥0} {k : Lp ℂ 2 (ν.prod ν)}
  {κ : G × G → ℂ} (hκ : κ =ᵐ[ν.prod ν] k)
  (hU : IsDPrimeSequence μ U) (hBorel : ∀ n, MeasurableSet (U n))
  (hf : Continuous f) (hf_pos : ∀ x, 0 < f x) (hν : ν = μ.withDensity (fun x ↦ ↑(f x)))
  (hT : IsNuclearOperator (integralKernelOperator ν k).val)

variable {νdual : Measure G} (hνdual : νdual = μ.withDensity (fun x ↦ ↑((f x)⁻¹)))
  (b : _root_.SchauderBasis ℂ (Lp ℂ 2 ν)) (θ : ℕ → Lp ℂ 2 νdual)
  (transpose : Lp ℂ 2 νdual →L[ℂ] Lp ℂ 2 νdual)
  (hsimple : ∃ C : ℝ, ∀ N, ‖b.proj (N + 1)‖ ≤ C)
  (hnormalized : RiemannMasullo.SchauderBasis.IsNormalized (fun n ↦ b n))
  (hθ : ∀ (m : ℕ) (u : Lp ℂ 2 ν),
    weightedL2Duality μ hf.measurable hf_pos hν hνdual u (θ m) = b.coord m u)
  (htranspose : ∀ (u : Lp ℂ 2 ν) (v : Lp ℂ 2 νdual),
    weightedL2Duality μ hf.measurable hf_pos hν hνdual ((integralKernelOperator ν k).val u) v =
    weightedL2Duality μ hf.measurable hf_pos hν hνdual u (transpose v))

include hU hBorel hf hf_pos hν hT hκ hνdual hsimple hnormalized hθ htranspose

/-- Paper: Theorem 12.1.1.2(4), p. 499. The partial kernels constructed
from the simple, normalized Schauder basis converge in weighted product L².
The product smoothenings represent the same L² classes and limit.
Deviation: Simplicity is stated as uniform operator-norm boundedness of the
partial projections, equivalent to strong boundedness here. -/
theorem tendsto_schauderKernelPartialSum_L2 :
    let ks := schauderKernelPartialSum f (fun n ↦ b n) θ transpose
    ∃ hk : ∀ N, MemLp (ks N) 2 (ν.prod ν),
      Tendsto (fun N ↦ (hk N).toLp (ks N)) atTop (𝓝 k) ∧
        (∀ N, dSequenceKernelSmoothening μ U (ks N) =ᵐ[ν.prod ν] ks N) ∧
        dSequenceKernelSmoothening μ U κ =ᵐ[ν.prod ν] (k : G × G → ℂ) := by sorry

/-- Paper: Theorem 12.1.1.2(4), p. 499. The diagonals of the smoothened
partial kernels from the Schauder basis converge weakly in weighted L¹. -/
theorem tendsto_schauderKernelPartialSum_diagonal_weak :
    let ks := schauderKernelPartialSum f (fun n ↦ b n) θ transpose
    let ds := fun N x ↦ dSequenceKernelSmoothening μ U (ks N) (x, x)
    let d := fun x ↦ dSequenceKernelSmoothening μ U κ (x, x)
    (∀ N, Integrable (ds N) ν) ∧ Integrable d ν ∧
      ∀ ρ : Lp ℂ ∞ ν, Tendsto (fun N ↦ ∫ x, ρ x * ds N x ∂ν) atTop
        (𝓝 (∫ x, ρ x * d x ∂ν)) := by sorry

end SchauderApproximation

end RiemannMasullo
