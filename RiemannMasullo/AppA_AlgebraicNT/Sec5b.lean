module

public import RiemannMasullo.AppA_AlgebraicNT.Sec5a
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Maximal theorems and Lebesgue differentiation on locally compact abelian groups

Masullo, §§A.5.3–A.5.4, pp. 578–586.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal Pointwise

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} {U : ℕ → Set G} {C : ℝ}

-- TODO(paper-gap): Theorem A.5.3.1 claims strictness even for B = ∅, when both sides are zero.

/-- Paper: Theorem A.5.3.1, p. 578. If each point of `B` centers an allowed translate,
one can select finitely many disjoint translates centered in `B` whose total mass
exceeds the mass of `B` divided by the structural constant.
Deviation: The strict comparison requires `B` to be nonempty. The finiteness condition
on `B * U 0` uses outer measure, as in Remark A.5.3.2. -/
theorem exists_disjoint_dSequence_translates [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {F : Set (Set G)} (hF : F ⊆ {V | ∃ (x : G) (k : ℕ), V = x • U k})
    {s : Set G} (hs : NullMeasurableSet s μ) (hsne : s.Nonempty) (hsU : μ (s * U 0) < ∞)
    (hcover : ∀ x ∈ s, ∃ k, x • U k ∈ F) :
    ∃ (n : ℕ) (x : Fin n → G) (k : Fin n → ℕ),
      (∀ i, x i ∈ s ∧ x i • U (k i) ∈ F) ∧
      Pairwise (fun i j ↦ Disjoint (x i • U (k i)) (x j • U (k j))) ∧
      μ s / ENNReal.ofReal C < ∑ i, μ (U (k i)) := by sorry

variable [SecondCountableTopology G]

/-- Paper: Lemma A.5.3.3, p. 579. A set that is negligible on a neighborhood of
every point is negligible and measurable for the completed Haar measure. -/
theorem measure_zero_of_locally_negligible [μ.IsHaarMeasure] {A : Set G}
    (hA : ∀ x : G, ∃ V ∈ 𝓝 x, μ (A ∩ V) = 0) :
    μ A = 0 ∧ NullMeasurableSet A μ := by sorry

/-- Paper: (A.5.3.2), p. 579. Take the limit superior of the masses of the
translates under `ν`, normalized by the Haar masses of the sequence members. -/
def dSequenceMeasureMaximal (μ ν : Measure G) (U : ℕ → Set G) (x : G) : ℝ≥0∞ :=
  limsup (fun k ↦ ν (x • U k) / μ (U k)) atTop

/-- Paper: (A.5.3.2), p. 579. Taking the same Haar measure in both positions
gives the constant maximal function one. -/
theorem dSequenceMeasureMaximal_haar [μ.IsHaarMeasure] (hU : IsDSequence μ U) (x : G) :
    dSequenceMeasureMaximal μ μ U x = 1 := by sorry

/-- Paper: Theorem A.5.3.4(1), p. 579. On `B` the measure maximal function satisfies
the localized weak bound, with the mass on the right measured by `ν`.
Deviation: Products of sets are measured by outer measure. -/
theorem dSequenceMeasureMaximal_weak [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDSequence μ U) (hBorel : ∀ k, MeasurableSet (U k))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {B : Set G} (hB : NullMeasurableSet B μ) (hBU : μ (B * U 0) < ∞)
    {α : ℝ} (hα : 0 < α) :
    let E := B ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}
    μ E ≤ ENNReal.ofReal (C / α) * ν (E * U 0) := by sorry

/-- Paper: Theorem A.5.3.4(1), p. 579. Equality in the localized weak bound
holds exactly when the part of the strict level set in `B` is empty.
Deviation: Products of sets are measured by outer measure. -/
theorem dSequenceMeasureMaximal_weak_eq_iff [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDSequence μ U) (hBorel : ∀ k, MeasurableSet (U k))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {B : Set G} (hB : NullMeasurableSet B μ) (hBU : μ (B * U 0) < ∞)
    {α : ℝ} (hα : 0 < α) :
    let E := B ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}
    μ E = ENNReal.ofReal (C / α) * ν (E * U 0) ↔ E = ∅ := by sorry

/-- Paper: Theorem A.5.3.4(2), p. 580. A Borel D-sequence with relatively
compact first member gives an almost everywhere finite measure maximal function. -/
theorem ae_dSequenceMeasureMaximal_lt_top [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDSequence μ U) (hBorel : ∀ k, MeasurableSet (U k))
    (hcompact : IsCompact (closure (U 0))) :
    ∀ᵐ x ∂μ, dSequenceMeasureMaximal μ ν U x < ∞ := by sorry

/-- Paper: Theorem A.5.3.5, p. 580. For a D′-sequence the weak bound on a
compact set can use the `ν`-mass of that compact set itself.
Deviation: Formula (A.5.3.5) is identical to (A.5.3.2) and uses the same operator. -/
theorem dSequenceMeasureMaximal_weak_compact [μ.IsHaarMeasure] {ν : Measure G} [ν.Regular]
    (hU : IsDPrimeSequence μ U)
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {K : Set G} (hK : IsCompact K) {α : ℝ} (hα : 0 < α) :
    μ (K ∩ {x | ENNReal.ofReal α < dSequenceMeasureMaximal μ ν U x}) ≤
      ENNReal.ofReal (C / α) * ν K := by sorry

/-- Paper: (A.5.3.8), p. 581. Take the limit superior of the averages of the
absolute value over the translates of the sequence members. The averages and
the limit superior take values in the extended nonnegative reals. -/
def dSequenceMaximal (μ : Measure G) (U : ℕ → Set G) (f : G → ℂ) (x : G) : ℝ≥0∞ :=
  limsup (fun k ↦ ⨍⁻ y in x • U k, ‖f y‖ₑ ∂μ) atTop

/-- Paper: (A.5.3.8), p. 581. When the sequence is eventually the identity
singleton of positive finite mass, the maximal function is the pointwise norm. -/
theorem dSequenceMaximal_eventually_singleton [μ.IsHaarMeasure]
    (h₀ : 0 < μ {1}) (hfin : μ {1} < ∞) (hU : ∀ᶠ k in atTop, U k = {1})
    (f : G → ℂ) (x : G) : dSequenceMaximal μ U f x = ‖f x‖ₑ := by sorry

/-- Paper: Theorem A.5.3.6, p. 581. The local function maximal operator gives
a function measurable for the completed Haar measure. -/
theorem dSequenceMaximal_aemeasurable [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hcompact : IsCompact (closure (U 0))) {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    AEMeasurable (dSequenceMaximal μ U f) μ := by sorry

-- TODO(paper-gap): The auxiliary bound (A.5.3.11) fails for f = 1 on any compact
-- set of positive Haar mass, since the log term vanishes and the left side is μ(K).

/-- Paper: Theorem A.5.3.6, p. 581. If `f log⁺ |f|` is also locally
integrable, the extended-valued maximal function is locally integrable. -/
theorem dSequenceMaximal_locallyIntegrable [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hcompact : IsCompact (closure (U 0))) {f : G → ℂ} (hf : LocallyIntegrable f μ)
    (hlog : LocallyIntegrable (fun x ↦ max (Real.log ‖f x‖) 0 • f x) μ) :
    LocallyIntegrable (dSequenceMaximal μ U f) μ := by sorry

/-- Paper: Theorem A.5.3.6, p. 581. Under the local `L log L` hypothesis,
the function maximal operator is finite almost everywhere. -/
theorem ae_dSequenceMaximal_lt_top [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (hcompact : IsCompact (closure (U 0))) {f : G → ℂ} (hf : LocallyIntegrable f μ)
    (hlog : LocallyIntegrable (fun x ↦ max (Real.log ‖f x‖) 0 • f x) μ) :
    ∀ᵐ x ∂μ, dSequenceMaximal μ U f x < ∞ := by sorry

-- TODO(paper-gap): The truncation argument in (A.5.3.15) uses the lower level set of |f|.
-- Passing to the lower level set of M f in (A.5.3.9) needs a justification.

/-- Paper: Theorem A.5.3.6(1), p. 581. The mass of the strict level set on `B`
is bounded by the integral of `|f|` over the lower maximal-function level set in `B * U 0`,
with the factor in (A.5.3.9). -/
theorem dSequenceMaximal_weak_local [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {f : G → ℂ} (hf : LocallyIntegrable f μ) {B : Set G} (hB : NullMeasurableSet B μ)
    (hBU : NullMeasurableSet (B * U 0) μ) (hfin : μ (B * U 0) < ∞)
    {α δ : ℝ} (hα : 0 < α) (hδ₀ : 0 < δ) (hδ₁ : δ < 1) :
    μ (B ∩ {x | ENNReal.ofReal α < dSequenceMaximal μ U f x}) ≤
      ENNReal.ofReal (C / ((1 - δ) * α)) *
        ∫⁻ x in (B * U 0) ∩ {x | ENNReal.ofReal (δ * α) < dSequenceMaximal μ U f x},
          ‖f x‖ₑ ∂μ := by sorry

/-- Paper: Theorem A.5.3.6(2), p. 581. The `p`-th moment on `B` of the maximal
function is bounded by the `p`-th moment of `|f|` on `B * U 0`, with the factor in (A.5.3.10).
Deviation: The conditions on `B` from part (1) are read as applying to part (2) as well. -/
theorem dSequenceMaximal_strong_local [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {f : G → ℂ} (hf : LocallyIntegrable f μ) {B : Set G} (hB : NullMeasurableSet B μ)
    (hBU : NullMeasurableSet (B * U 0) μ) (hfin : μ (B * U 0) < ∞)
    {p : ℝ} (hp : 1 < p) :
    (∫⁻ x in B, dSequenceMaximal μ U f x ^ p ∂μ) ≤
      ENNReal.ofReal (C * p ^ (p + 1) / (p - 1) ^ p) *
        ∫⁻ x in B * U 0, ‖f x‖ₑ ^ p ∂μ := by sorry

/-- Paper: Theorem A.5.3.7(1), p. 582. The mass of the global strict level
set is bounded by the `L¹` norm times `2 * C / α`. -/
theorem dSequenceMaximal_weak_global [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {f : G → ℂ} (hf : Integrable f μ) {α : ℝ} (hα : 0 < α) :
    μ {x | ENNReal.ofReal α < dSequenceMaximal μ U f x} ≤
      ENNReal.ofReal (2 * C / α) * eLpNorm f 1 μ := by sorry

/-- Paper: Theorem A.5.3.7(2), p. 582. An `Lᵖ` input with `p > 1`
has an `Lᵖ` maximal function. -/
theorem dSequenceMaximal_memLp [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    {f : G → ℂ} {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    MemLp (dSequenceMaximal μ U f) (ENNReal.ofReal p) μ := by sorry

/-- Paper: Theorem A.5.3.7(2), p. 582. On the entire group the `p`-th moment
of the maximal function is bounded by the `p`-th power of the `Lᵖ` norm times the printed factor. -/
theorem dSequenceMaximal_strong_global [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    (hcompact : IsCompact (closure (U 0)))
    (hC : 0 < C) (hbound : ∀ k, μ (U k * (U k)⁻¹) < ENNReal.ofReal C * μ (U k))
    {f : G → ℂ} {p : ℝ} (hp : 1 < p) (hf : MemLp f (ENNReal.ofReal p) μ) :
    (∫⁻ x, dSequenceMaximal μ U f x ^ p ∂μ) ≤
      ENNReal.ofReal (C * p ^ (p + 1) / (p - 1) ^ p) *
        eLpNorm f (ENNReal.ofReal p) μ ^ p := by sorry

/-- Paper: (A.5.4.1), p. 582. Average a complex-valued function over the
left translate of a sequence member. Haar invariance equates the mass of the
translate used by the set average with the mass of the original member. -/
def dSequenceAverage (μ : Measure G) (V : Set G) (f : G → ℂ) (x : G) : ℂ :=
  ⨍ y in x • V, f y ∂μ

/-- Paper: (A.5.4.1), p. 582. Averaging a constant over any sequence member
recovers the constant at every point. -/
theorem dSequenceAverage_const [μ.IsHaarMeasure] (hU : IsDSequence μ U)
    (c : ℂ) (k : ℕ) (x : G) : dSequenceAverage μ (U k) (fun _ ↦ c) x = c := by sorry

-- TODO(paper-gap): The uniform continuity in Theorem A.5.4.1(1) fails for f(t) = t²
-- on the additive real line with U k = [−2⁻ᵏ, 2⁻ᵏ]. The average is x² + 2⁻²ᵏ / 3.

/-- Paper: Theorem A.5.4.1(3), p. 582. A point is regular when the sequence of
averages at that point has a complex limit. -/
def dSequenceRegularSet (μ : Measure G) (U : ℕ → Set G) (f : G → ℂ) : Set G :=
  {x | ∃ l : ℂ, Tendsto (fun k ↦ dSequenceAverage μ (U k) f x) atTop (𝓝 l)}

/-- Paper: Theorem A.5.4.1(3), p. 582. Every point is regular for a constant
function. -/
theorem dSequenceRegularSet_const [μ.IsHaarMeasure] (hU : IsDSequence μ U) (c : ℂ) :
    dSequenceRegularSet μ U (fun _ ↦ c) = univ := by sorry

-- TODO(paper-gap): In the proof of Theorem A.5.4.1(2), the boundary of a relatively compact
-- open set can have positive Haar mass, and an indicator's averages can diverge at a point.

/-- Paper: Theorem A.5.4.1(2)–(3), p. 582. The complement of the regular set
is negligible, equivalently the averages converge almost everywhere. -/
theorem measure_compl_dSequenceRegularSet [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    μ (dSequenceRegularSet μ U f)ᶜ = 0 := by sorry

-- TODO(paper-gap): In the proof of Theorem A.5.4.1(3), compact support does not imply Lᵖ
-- integrability, and the Lᑫ norm of the normalized kernel is μ(U k)^(1/q - 1).

/-- Paper: Theorem A.5.4.1(3), p. 583. The averages tend to the value of the
function almost everywhere, which also gives the identity almost everywhere on the regular set. -/
theorem ae_tendsto_dSequenceAverage [μ.IsHaarMeasure] (hU : IsDPrimeSequence μ U)
    {f : G → ℂ} (hf : LocallyIntegrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun k ↦ dSequenceAverage μ (U k) f x) atTop (𝓝 (f x)) := by sorry

/-- Paper: Terminology A.5.4.1, p. 583. The smoothening at a regular point
is the complex limit of the sequence of averages. -/
def dSequenceSmoothening (μ : Measure G) (U : ℕ → Set G) (f : G → ℂ)
    (x : dSequenceRegularSet μ U f) : ℂ :=
  limUnder atTop (fun k ↦ dSequenceAverage μ (U k) f x)

/-- Paper: Terminology A.5.4.1, p. 583. A constant function smoothens to that
same constant on its regular set. -/
theorem dSequenceSmoothening_const [μ.IsHaarMeasure] (hU : IsDSequence μ U) (c : ℂ)
    (x : dSequenceRegularSet μ U (fun _ ↦ c)) :
    dSequenceSmoothening μ U (fun _ ↦ c) x = c := by sorry

-- TODO(paper-gap): Remark A.5.4.2 refers to D_f without specifying it.

-- TODO(paper-gap): Corollary A.5.4.3 fails at x = 0 for symmetric intervals on ℝ.
-- Use f(t) = sgn(t) |t|⁻¹ᐟ² and a compactly supported continuous φ with
-- φ(t) = sgn(t) |t|¹ᐟ⁴ near zero. The averages of f vanish, while those of φ · f diverge.

end RiemannMasullo
