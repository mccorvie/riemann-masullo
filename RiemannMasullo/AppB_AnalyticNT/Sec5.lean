module

public import Mathlib.Analysis.Complex.Hadamard
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import RiemannMasullo.Ch03_IdelicZeta.Sec2

/-!
# §B.5 Recurrence and equidistribution

Continuous-time torus equidistribution, vertical self-approximation, and recurrence of
reciprocal finite Euler products.
-/

@[expose] public section

noncomputable section

open Filter Function MeasureTheory Set
open Complex.HadamardThreeLines (verticalStrip)
open scoped ENNReal NNReal Topology

namespace RiemannMasullo

section Torus

variable {N : ℕ}

/-- Paper: Definition B.5.1.1(1), p. 626.
The product torus, represented by Mathlib's `UnitAddTorus (Fin N)`, is compact Hausdorff. -/
theorem unitAddTorus_compactHausdorff (N : ℕ) :
    CompactSpace (UnitAddTorus (Fin N)) ∧ T2Space (UnitAddTorus (Fin N)) := by sorry

/-- Paper: Definition B.5.1.1(2), p. 626.
The torus quotient reduces each real coordinate modulo one. -/
def torusQuotient (N : ℕ) : (Fin N → ℝ) →ₜ+ UnitAddTorus (Fin N) where
  toAddMonoidHom := AddMonoidHom.pi fun i ↦
    (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℝ))).comp (Pi.evalAddMonoidHom _ i)
  continuous_toFun := continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
    (continuous_apply i)

/-- Two real vectors have the same image in the torus precisely when their coordinate
differences are integers. -/
theorem torusQuotient_eq_iff (x y : Fin N → ℝ) :
    torusQuotient N x = torusQuotient N y ↔ ∀ i, ∃ m : ℤ, x i - y i = (m : ℝ) := by sorry

/-- Paper: Definition B.5.1.1(2), p. 626.
The hitting times are the times in the given interval when the projected curve belongs
to the image of the target set modulo one. -/
def torusHittingTimes (γ : ℝ → Fin N → ℝ) (J : Set ℝ) (U : Set (Fin N → ℝ)) : Set ℝ :=
  J ∩ (torusQuotient N ∘ γ) ⁻¹' (torusQuotient N '' U)

/-- The constant zero curve hits a singleton integer vector modulo one at every time. -/
theorem torusHittingTimes_zero_singleton_int (J : Set ℝ) (m : Fin N → ℤ) :
    torusHittingTimes (fun _ ↦ 0) J {fun i ↦ (m i : ℝ)} = J := by sorry

/-- Paper: §B.5.1, p. 627.
The one-parameter torus subgroup of a frequency vector is the projection of its real line. -/
def torusFlow (τ : Fin N → ℝ) : ℝ →ₜ+ UnitAddTorus (Fin N) :=
  (torusQuotient N).comp (↑((ContinuousLinearMap.id ℝ ℝ).smulRight τ))

/-- At time one the flow has the phase given by the frequency vector modulo one. -/
theorem torusFlow_one (τ : Fin N → ℝ) : torusFlow τ 1 = torusQuotient N τ := by sorry

-- TODO(paper-gap): The sentence before §B.5.2 claims injectivity also in dimension one.
-- For N = 1 and τ₁ = 1, times zero and one have the same image.

/-- Paper: §B.5.1, p. 627. Rationally independent frequencies give a dense
one-parameter subgroup of the ambient torus. -/
theorem torusFlow_denseRange_of_linearIndependent [NeZero N] {τ : Fin N → ℝ}
    (hτ : LinearIndependent ℚ τ) : DenseRange (torusFlow τ) := by sorry

/-- Paper: §B.5.1, p. 627. For at least two rationally independent frequencies,
distinct times give distinct phases.
Deviation: Adds the dimension hypothesis used in the proof on p. 628. -/
theorem torusFlow_injective_of_linearIndependent (hN : 2 ≤ N) {τ : Fin N → ℝ}
    (hτ : LinearIndependent ℚ τ) : Injective (torusFlow τ) := by sorry

/-- Paper: Theorem B.5.2.1(1), p. 627.
The orbit closure is the closed additive subgroup obtained by closing the range of the flow. -/
def torusFlowClosure (τ : Fin N → ℝ) : AddSubgroup (UnitAddTorus (Fin N)) :=
  (torusFlow τ).toAddMonoidHom.range.topologicalClosure

/-- The zero frequency vector has the trivial orbit closure. -/
theorem torusFlowClosure_zero : torusFlowClosure (0 : Fin N → ℝ) = ⊥ := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627.
The torus flow takes values in its orbit closure when used in time averages. -/
def torusFlowInClosure (τ : Fin N → ℝ) (t : ℝ) : torusFlowClosure τ :=
  ⟨torusFlow τ t, AddSubgroup.le_topologicalClosure (torusFlow τ).toAddMonoidHom.range
    ⟨t, rfl⟩⟩

/-- In the ambient torus the restricted flow at time one gives the original phases. -/
theorem coe_torusFlowInClosure_one (τ : Fin N → ℝ) :
    (torusFlowInClosure τ 1 : UnitAddTorus (Fin N)) = torusQuotient N τ := by sorry

/-- Paper: §B.5.2.1, p. 627.
The fundamental domain for the torus quotient is the product of the half-open unit intervals. -/
def unitHalfOpenCube (N : ℕ) : Set (Fin N → ℝ) :=
  {x | ∀ i, x i ∈ Ico (0 : ℝ) 1}

/-- The one-dimensional cube includes the lower endpoint and excludes the upper endpoint. -/
theorem mem_unitHalfOpenCube_one (x : Fin 1 → ℝ) :
    x ∈ unitHalfOpenCube 1 ↔ 0 ≤ x 0 ∧ x 0 < 1 := by sorry

/-- Paper: §B.5.2.1, p. 627.
The torus volume is the pushforward of Lebesgue measure on the half-open unit cube. -/
theorem map_volume_unitHalfOpenCube (N : ℕ) :
    (volume.restrict (unitHalfOpenCube N)).map (torusQuotient N) =
      (volume : Measure (UnitAddTorus (Fin N))) := by sorry

/-- Paper: §B.5.2.1, p. 627.
Riemann integrability on a torus with Haar probability is expressed by boundedness and
continuity almost everywhere.
Deviation: Uses the Lebesgue criterion for Riemann integrability on the fundamental cube. -/
def TorusRiemannIntegrable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) (u : X → ℂ) : Prop :=
  (∃ C : ℝ, ∀ x, ‖u x‖ ≤ C) ∧ ∀ᵐ x ∂μ, ContinuousAt u x

/-- The indicator of the identity on the unit circle is Riemann integrable. -/
theorem torusRiemannIntegrable_indicator_zero :
    TorusRiemannIntegrable (volume : Measure UnitAddCircle)
      (({0} : Set UnitAddCircle).indicator (fun _ ↦ (1 : ℂ))) := by sorry

/-- Paper: Theorem B.5.2.1(1), p. 627.
The closed orbit subgroup is topologically isomorphic to the torus of dimension the rational
rank of the frequencies. -/
theorem torusFlowClosure_equiv_torus [NeZero N] (τ : Fin N → ℝ) :
    Nonempty (torusFlowClosure τ ≃ₜ+
      UnitAddTorus (Fin (Module.finrank ℚ (Submodule.span ℚ (range τ))))) := by sorry

-- TODO(paper-gap): Theorem B.5.2.1(2) for arbitrary Riemann-integrable observables.
-- A function supported on a Haar-null orbit arc can pull back to a nonmeasurable time function.
-- TODO(paper-gap): The bound in (B.5.2.14) needs an absolute value around the frequency.

/-- Paper: Theorem B.5.2.1(2), p. 627. Symmetric time averages of a
Riemann-integrable observable converge to its Haar probability integral.
Deviation: Requires Lebesgue measurability up to null sets along the orbit for the time integral. -/
theorem kroneckerWeyl_riemannIntegrable_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ) (hu : TorusRiemannIntegrable μ u)
    (ht : AEStronglyMeasurable (fun t ↦ u (torusFlowInClosure τ t)) volume) :
    Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627. Forward time averages of a
Riemann-integrable observable converge to its Haar probability integral.
Deviation: Requires Lebesgue measurability up to null sets on the forward orbit. -/
theorem kroneckerWeyl_riemannIntegrable_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ) (hu : TorusRiemannIntegrable μ u)
    (ht : AEStronglyMeasurable (fun t ↦ u (torusFlowInClosure τ t))
      (volume.restrict (Ici (0 : ℝ)))) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627.
Symmetric time averages of a continuous observable converge to its Haar probability integral.
Deviation: This is the continuous case singled out in the paper. -/
theorem kroneckerWeyl_continuous_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(torusFlowClosure τ, ℂ)) :
    Tendsto (fun T : ℝ ↦ (2 * T)⁻¹ • ∫ t in -T..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Theorem B.5.2.1(2), p. 627.
Forward time averages of a continuous observable converge to its Haar probability integral.
Deviation: This is the continuous case singled out in the paper. -/
theorem kroneckerWeyl_continuous_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : C(torusFlowClosure τ, ℂ)) :
    Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, u (torusFlowInClosure τ t))
      atTop (𝓝 (∫ x, u x ∂μ)) := by sorry

/-- Paper: Lemma B.5.2.2, p. 627.
The indicator of an open set with null boundary can be sandwiched between continuous
functions into the unit interval whose integrated difference is arbitrarily small. -/
theorem exists_continuous_sandwich_indicator {X : Type*} [TopologicalSpace X] [T2Space X]
    [CompactSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.Regular]
    {U : Set X} (hU : IsOpen U) (hfront : μ (frontier U) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ lower upper : C(X, Icc (0 : ℝ) 1),
      (∀ x, (lower x : ℝ) ≤ U.indicator (fun _ ↦ (1 : ℝ)) x ∧
        U.indicator (fun _ ↦ (1 : ℝ)) x ≤ (upper x : ℝ)) ∧
      (∫ x, ((upper x : ℝ) - (lower x : ℝ)) ∂μ) < ε := by sorry

-- TODO(paper-gap): Neither inclusion in the asserted frontier identity holds in general.
-- Away from the coordinate seams the cube projection is a local homeomorphism, so the
-- torus frontier lies in the image of the relative frontier together with the null seams.

/-- Paper: Remark B.5.2.3(1), p. 628.
A subset of the half-open cube with a null relative frontier has a torus image with null
frontier. The restricted Lebesgue measure identifies relative null sets via their images
in the ambient real vector space. -/
theorem volume_frontier_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (frontier (torusQuotient N '' (Subtype.val '' U))) = 0 := by sorry

/-- Paper: Remark B.5.2.3(2), p. 628.
For a Jordan-measurable subset of the cube, its torus image and the interior of that
image have the same volume. Jordan measurability is expressed by the null relative frontier. -/
theorem volume_interior_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (interior (torusQuotient N '' (Subtype.val '' U))) =
      volume (torusQuotient N '' (Subtype.val '' U)) := by sorry

/-- Paper: Remark B.5.2.3(2), p. 628.
The interior of the torus image of a Jordan-measurable set has null frontier. -/
theorem volume_frontier_interior_torusQuotient_image [NeZero N] (U : Set (unitHalfOpenCube N))
    (hU : volume (Subtype.val '' frontier U) = 0) :
    volume (frontier (interior (torusQuotient N '' (Subtype.val '' U)))) = 0 := by sorry

/-- Paper: Corollary B.5.2.4, p. 631.
For a relatively open subset of the unit cube, the symmetric frequency of visits converges
to Haar probability on the orbit closure when the target has null relative frontier. -/
theorem torusHittingTimes_tendsto_symmetric [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (U : Set (unitHalfOpenCube N)) (hU : IsOpen U) :
    let V : Set (torusFlowClosure τ) := Subtype.val ⁻¹' (torusQuotient N '' (Subtype.val '' U))
    μ (frontier V) = 0 →
      Tendsto (fun T : ℝ ↦
        volume.real (torusHittingTimes (fun t ↦ t • τ) (Icc (-T) T) (Subtype.val '' U)) /
          (2 * T)) atTop (𝓝 (μ.real V)) := by sorry

/-- Paper: Corollary B.5.2.4, p. 631.
For a relatively open subset of the unit cube, the forward frequency of visits converges
to Haar probability on the orbit closure when the target has null relative frontier. -/
theorem torusHittingTimes_tendsto_forward [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (U : Set (unitHalfOpenCube N)) (hU : IsOpen U) :
    let V : Set (torusFlowClosure τ) := Subtype.val ⁻¹' (torusQuotient N '' (Subtype.val '' U))
    μ (frontier V) = 0 →
      Tendsto (fun T : ℝ ↦
        volume.real (torusHittingTimes (fun t ↦ t • τ) (Icc 0 T) (Subtype.val '' U)) /
          T) atTop (𝓝 (μ.real V)) := by sorry

-- TODO(paper-gap): Remark B.5.2.5 does not state the discrete versions. The discrete orbit
-- closure can be disconnected, so the continuous-time dimension claim cannot be reused verbatim.

end Torus

section Recurrence

/-- Paper: Definition B.5.3.1(1), p. 632.
The upper density is the limsup of the fraction of a symmetric interval occupied by the set.
Deviation: For arbitrary subsets the numerator is Lebesgue outer measure. -/
def upperDensity (X : Set ℝ) : ℝ :=
  limsup (fun T : ℝ ↦ volume.real (Icc (-T) T ∩ X) / (2 * T)) atTop

/-- Every right half-line has symmetric upper density one half. -/
theorem upperDensity_Ici (a : ℝ) : upperDensity (Ici a) = 1 / 2 := by sorry

/-- Paper: Definition B.5.3.1(2), p. 632.
The vertical return times are the shifts whose uniform approximation error on the specified set
is less than the tolerance. -/
def verticalReturnTimes (f : ℂ → ℂ) (K : Set ℂ) (ε : ℝ) : Set ℝ :=
  {t | (⨆ z : K, (‖f ((z : ℂ) + (t : ℂ) * Complex.I) - f z‖₊ : ℝ≥0∞)) < ENNReal.ofReal ε}

/-- The return times of the identity on a singleton are the shifts of absolute value
less than the tolerance. -/
theorem verticalReturnTimes_id_singleton (z : ℂ) {ε : ℝ} (hε : 0 < ε) :
    verticalReturnTimes id {z} ε = Ioo (-ε) ε := by sorry

/-- Paper: Definition B.5.3.1(2), p. 632.
Strong recurrence means positive upper density of vertical return times for every positive
tolerance.
Deviation: The domain is represented by a complex function with holomorphy on the strip
and compact containment imposed at use sites. The printed `C_{>R}` is read as `C_I`. -/
def StronglyRecurrentOn (f : ℂ → ℂ) (K : Set ℂ) : Prop :=
  ∀ ε > 0, 0 < upperDensity (verticalReturnTimes f K ε)

/-- On compact sets, the complex exponential is strongly recurrent by its imaginary period. -/
theorem stronglyRecurrentOn_exp {K : Set ℂ} (hK : IsCompact K) :
    StronglyRecurrentOn Complex.exp K := by sorry

-- TODO(paper-gap): Proposition B.5.3.2 forces T₀ = 0. Over ℚ with the trivial character
-- and a finite place above 2, the denominator at T₀ vanishes.

open IsDedekindDomain NumberField

variable {F : Type*} [Field F] [NumberField F]

/-- Paper: Proposition B.5.3.3, p. 632.
The reciprocal partial Euler product multiplies the reciprocals of the finite Euler factors
from §3.2. At a zero of the local Euler polynomial this gives its holomorphic value zero. -/
def reciprocalPartialHeckeEulerProduct (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (s : ℂ) : ℂ :=
  ∏ v ∈ S, (finiteHeckeEulerFactor χ v s)⁻¹

/-- For a singleton unramified place the product is the linear factor with coefficient
given by the value of the character on a local uniformizer. -/
theorem reciprocalPartialHeckeEulerProduct_singleton
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (v : HeightOneSpectrum (𝓞 F))
    (hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (s : ℂ) :
    reciprocalPartialHeckeEulerProduct χ {v} s =
      1 - (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s) := by
  classical
  simp [reciprocalPartialHeckeEulerProduct, finiteHeckeEulerFactor, hv]

/-- Paper: Proposition B.5.3.2, p. 632. There is a nondecreasing sequence
escaping to infinity on both tails on which the reciprocal product is bounded away from zero.
Deviation: Uses the negative sign condition for strictly negative indices. The height at
index zero may then be chosen away from all poles of the Euler factors. -/
theorem exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) :
    ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧ Monotone T ∧
      (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
      Tendsto (fun k ↦ |T k|) (comap (abs : ℤ → ℤ) atTop) atTop ∧
      ∀ k, c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((T k : ℂ) * Complex.I)‖ := by sorry

/-- Paper: Proposition B.5.3.3, p. 632.
The nonnegative vertical shifts that uniformly approximate the reciprocal partial Euler
product on the compact set have positive symmetric upper density. -/
theorem reciprocalPartialHeckeEulerProduct_upperDensity_nonneg
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {a b : ℝ} (hI : (0 : ℝ) ∈ Ioo a b) {K : Set ℂ} (hK : IsCompact K)
    (hKI : K ⊆ verticalStrip a b) (hKint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    0 < upperDensity (Ici 0 ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) :=
  by sorry

/-- Paper: Proposition B.5.3.3, p. 632.
The nonpositive vertical shifts that uniformly approximate the reciprocal partial Euler
product on the compact set have positive symmetric upper density. -/
theorem reciprocalPartialHeckeEulerProduct_upperDensity_nonpos
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hχ : ∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v)
    {a b : ℝ} (hI : (0 : ℝ) ∈ Ioo a b) {K : Set ℂ} (hK : IsCompact K)
    (hKI : K ⊆ verticalStrip a b) (hKint : (interior K).Nonempty)
    {ε : ℝ} (hε : 0 < ε) :
    0 < upperDensity (Iic 0 ∩ verticalReturnTimes (reciprocalPartialHeckeEulerProduct χ S) K ε) :=
  by sorry

-- TODO(paper-gap): The proof of Proposition B.5.3.3 uses the ambient cube to infer Haar
-- nullity on a possibly lower-dimensional orbit closure. The level set must be treated
-- intrinsically on that closure. To apply the area estimate, integrate on an open
-- neighbourhood of the target compact set.

/-- Paper: Lemma B.5.3.4(1), p. 633.
For a holomorphic function on a bounded open strip, strong recurrence on a compact subset
descends to every compact subset of that subset. -/
theorem stronglyRecurrentOn_of_subset {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) {K K' : Set ℂ}
    (hK : IsCompact K) (hKI : K ⊆ verticalStrip a b) (hK' : IsCompact K') (hsub : K' ⊆ K)
    (hrec : StronglyRecurrentOn f K) : StronglyRecurrentOn f K' := by sorry

-- TODO(paper-gap): Lemma B.5.3.4(2) fails. A compact vertical segment need not fit inside
-- any disc contained in the strip, and disc-by-disc recurrence need not give simultaneous return
-- times on that segment. The report gives a Runge approximation counterexample.

/-- Paper: Lemma B.5.3.5, p. 633.
If the squared area error integrated over the closure of the open set is below
`π * δ² * X²`, the uniform error on the compact set is below `X`.
Deviation: The subscript `r` in (B.5.3.6) is read as `2`, as in (B.5.3.8). -/
theorem areaApproximation_subset_verticalReturnTimes {a b : ℝ} (hab : a < b) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (verticalStrip a b)) {K U : Set ℂ}
    (hK : IsCompact K) (hKne : K.Nonempty) (hKI : K ⊆ verticalStrip a b)
    (hU : IsOpen U) (hUcompact : IsCompact (closure U)) (hUI : closure U ⊆ verticalStrip a b)
    (hKU : K ⊆ U) {δ : ℝ} (hδ : δ = ⨅ z : K, Metric.infDist (z : ℂ) Uᶜ)
    (hδpos : 0 < δ) {T X : ℝ} (hT : 0 < T) (hX : 0 < X) :
    {t ∈ Icc (-T) T | (∫ z in closure U, ‖f (z + (t : ℂ) * Complex.I) - f z‖ ^ 2) <
      Real.pi * δ ^ 2 * X ^ 2} ⊆ Icc (-T) T ∩ verticalReturnTimes f K X := by sorry

end Recurrence

end RiemannMasullo
