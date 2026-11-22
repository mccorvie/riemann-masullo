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
    dSequenceKernelSmoothening μ U (fun _ ↦ c) = fun _ ↦ c := by
  funext p
  have havg (n : ℕ) :
      dSequenceAverage (μ.prod μ) (U n ×ˢ U n) (fun _ ↦ c) p = c := by
    obtain ⟨_, _, hpos, hfin⟩ := hU.1.1 n
    unfold dSequenceAverage
    apply setAverage_const <;> rw [measure_smul, Measure.prod_prod]
    · exact mul_ne_zero hpos.ne' hpos.ne'
    · exact ENNReal.mul_ne_top hfin.ne hfin.ne
  have hlim : Tendsto
      (fun n ↦ dSequenceAverage (μ.prod μ) (U n ×ˢ U n) (fun _ ↦ c) p) atTop (𝓝 c) := by
    simpa only [havg] using (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ c) atTop (𝓝 c))
  have hp : p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) (fun _ ↦ c) := ⟨c, hlim⟩
  simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hp,
    dSequenceSmoothening] using hlim.limUnder_eq

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
    dSequenceKernelSmoothening μ U κ =ᵐ[ν.prod ν] (k : G × G → ℂ) := by
  let w (p : G × G) := f p.1 * f p.2
  have hw : Continuous w := (hf.comp continuous_fst).mul (hf.comp continuous_snd)
  have hwpos (p : G × G) : 0 < (w p : ℝ) := by
    exact_mod_cast mul_pos (hf_pos p.1) (hf_pos p.2)
  have hprod : ν.prod ν = (μ.prod μ).withDensity (fun p ↦ (w p : ℝ≥0∞)) := by
    rw [hν]
    have hm : Measurable (fun x ↦ (f x : ℝ≥0∞)) := (ENNReal.continuous_coe.comp hf).measurable
    simpa only [w, ENNReal.coe_mul] using (prod_withDensity (μ := μ) (ν := μ) hm hm)
  have hloc := ((Lp.memLp k).locallyIntegrable one_le_two).congr hκ.symm
  have hweighted : LocallyIntegrable (fun p ↦ (w p : ℝ) • κ p) (μ.prod μ) := by
    apply locallyIntegrable_iff.mpr
    intro K hK
    have hi := hloc.integrableOn_isCompact hK
    rw [IntegrableOn, hprod, restrict_withDensity hK.measurableSet] at hi
    exact (integrable_withDensity_iff_integrable_smul hw.measurable).mp hi
  have hinv : Continuous (fun p ↦ (w p : ℝ)⁻¹) :=
    (NNReal.continuous_coe.comp hw).inv₀ (fun p ↦ (hwpos p).ne')
  have hhaar : LocallyIntegrable κ (μ.prod μ) := by
    refine (hweighted.continuous_smul hinv).congr (Filter.Eventually.of_forall fun p ↦ ?_)
    simp only [smul_smul, inv_mul_cancel₀ (hwpos p).ne', one_smul]
  -- The product-sequence theorem uses the Borel measurable structure on the product.
  have rectSeq [m : MeasurableSpace (G × G)] (hm : m = borel _)
      (η : Measure (G × G)) [η.IsHaarMeasure]
      (hrect : ∀ s t : Set G, MeasurableSet s → MeasurableSet t → η (s ×ˢ t) = μ s * μ t) :
      IsDPrimeSequence η (fun n ↦ U n ×ˢ U n) := by
    subst m
    exact IsDPrimeSequence.prod hrect hU hU
  have hseq : IsDPrimeSequence (μ.prod μ) (fun n ↦ U n ×ˢ U n) :=
    rectSeq BorelSpace.measurable_eq _ (fun s t _ _ ↦ Measure.prod_prod s t)
  have hac : ν.prod ν ≪ μ.prod μ := hprod ▸ withDensity_absolutelyContinuous _ _
  refine Filter.EventuallyEq.trans ?_ hκ
  filter_upwards [hac.ae_le (ae_tendsto_dSequenceAverage hseq hhaar)] with p hp
  have hreg : p ∈ dSequenceRegularSet (μ.prod μ) (fun n ↦ U n ×ˢ U n) κ := ⟨κ p, hp⟩
  simpa only [dSequenceKernelSmoothening, dSequenceSmootheningOrZero, dite_eq_left hreg,
    dSequenceSmoothening] using hp.limUnder_eq

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
  by
  intro Mρ
  let a : G × G → ℂ := fun p ↦ ρ p.1
  have ha : MemLp a ∞ (ν.prod ν) := by
    have hmρ := Lp.aestronglyMeasurable ρ
    have hm : AEStronglyMeasurable a (ν.prod ν) := hmρ.comp_fst
    rw [memLp_iff, eLpNorm_exponent_top hm, eLpNormEssSup_lt_top_iff_isBoundedUnder]
    have hb := (Lp.memLp ρ).eLpNorm_lt_top
    rw [eLpNorm_exponent_top hmρ, eLpNormEssSup_lt_top_iff_isBoundedUnder] at hb
    obtain ⟨C, hC⟩ := hb
    exact ⟨C, Measure.quasiMeasurePreserving_fst.ae hC⟩
  let b : G × G → ℂ := fun p ↦ a p * k p
  have hb : MemLp b 2 (ν.prod ν) := ha.mul (Lp.memLp k)
  let K := hb.toLp b
  have hK : (K : G × G → ℂ) =ᵐ[ν.prod ν] b := hb.coeFn_toLp
  refine ⟨K, ?_, ?_, ?_⟩
  · ext1 g
    apply Lp.ext
    have hM : ⇑(Mρ ((integralKernelOperator ν k).val g)) =ᵐ[ν]
        fun x ↦ ρ x * ((integralKernelOperator ν k).val g) x :=
      (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2) ρ _
    filter_upwards [integralKernelOperator_apply ν K g, integralKernelOperator_apply ν k g,
      Measure.ae_ae_of_ae_prod hK, hM] with x hx hx' hrow hmult
    change (integralKernelOperator ν K).val g x = Mρ ((integralKernelOperator ν k).val g) x
    rw [hx.2, hmult, hx'.2, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hrow] with y hy
    exact (congrArg (· * g y) hy).trans (mul_assoc _ _ _)
  · filter_upwards [hK, hκ] with p hp hrep
    exact hp.trans (congrArg (ρ p.1 * ·) hrep.symm)
  · filter_upwards [hK, dSequenceKernelSmoothening_ae_eq hκ hU hBorel hf hf_pos hν hT]
      with p hp hs
    exact hp.trans (congrArg (ρ p.1 * ·) hs.symm)

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
      dSequenceKernelSmoothening μ U κ =ᵐ[ν.prod ν] (k : G × G → ℂ) := by
  refine ⟨tendsto_iff_norm_sub_tendsto_zero.mpr ?_, fun n ↦
    dSequenceKernelSmoothening_ae_eq (hκs n) hU hBorel hf hf_pos hν (hSn n),
    dSequenceKernelSmoothening_ae_eq hκ hU hBorel hf hf_pos hν hT⟩
  let swap := Lp.compMeasurePreservingₗ (E := ℂ) (p := 2) ℂ Prod.swap
    (Measure.measurePreserving_swap (μ := ν) (ν := ν))
  let A := (hilbertSchmidtOperators_equiv_Lp_prod ν ν).choose.toLinearMap.comp swap
  have hsub (n : ℕ) :
      integralKernelOperator ν (ks n - k) = integralKernelOperator ν (ks n) - integralKernelOperator ν k :=
    map_sub A (ks n) k
  simpa only [← hsub, schattenNorm_integralKernelOperator] using hS2

/-- Paper: Theorem 12.1.1.2(3), p. 499. The smoothened diagonals converge
weakly in weighted L¹, expressed by testing against all weighted L∞ classes. -/
theorem tendsto_dSequenceKernelSmoothening_diagonal_weak :
    let ds := fun n x ↦ dSequenceKernelSmoothening μ U (κs n) (x, x)
    let d := fun x ↦ dSequenceKernelSmoothening μ U κ (x, x)
    (∀ n, Integrable (ds n) ν) ∧ Integrable d ν ∧
      ∀ ρ : Lp ℂ ∞ ν, Tendsto (fun n ↦ ∫ x, ρ x * ds n x ∂ν) atTop
        (𝓝 (∫ x, ρ x * d x ∂ν)) := by
  refine ⟨fun n ↦ (integral_dSequenceKernelSmoothening_diagonal
    (hκs n) hU hBorel hf hf_pos hν (hSn n)).1,
    (integral_dSequenceKernelSmoothening_diagonal hκ hU hBorel hf hf_pos hν hT).1, ?_⟩
  intro ρ
  let M := (ContinuousLinearMap.mul ℂ ℂ).holderL ν ∞ 2 2 ρ
  let left (A : nuclearEndomorphisms (Lp ℂ 2 ν)) : nuclearEndomorphisms (Lp ℂ 2 ν) :=
    ⟨M * A.val, mul_mem_nuclearEndomorphisms_left M A⟩
  let Ts (n : ℕ) : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨(integralKernelOperator ν (ks n)).val, hSn n⟩
  let T : nuclearEndomorphisms (Lp ℂ 2 ν) := ⟨(integralKernelOperator ν k).val, hT⟩
  have hleft (n : ℕ) : left (Ts n) - left T = left (Ts n - T) := Subtype.ext (mul_sub ..).symm
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := Lp ℂ 2 ν)
  have hlim : Tendsto (fun n ↦ hilbertTrace (left (Ts n))) atTop (𝓝 (hilbertTrace (left T))) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simp only [← htr, ← map_sub, hleft]
    simp only [htr]
    apply squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦
      (norm_hilbertTrace_le _).trans (traceNorm_mul_left_le M (Ts n - T)))
    simpa only [mul_zero] using hS1.const_mul ‖M‖
  have hn (n : ℕ) := (integral_mul_dSequenceKernelSmoothening_diagonal
    (hκs n) hU hBorel hf hf_pos hν (hSn n) ρ).2
  have h := (integral_mul_dSequenceKernelSmoothening_diagonal hκ hU hBorel hf hf_pos hν hT ρ).2
  simpa only [hn, h] using hlim

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
      (by simp) (by simp) u v = (‖u‖ ^ 2 : ℝ) := by
  calc
    _ = ∫ x, inner ℂ (u x) (u x) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx, RCLike.inner_apply]
    _ = inner ℂ u u := (L2.inner_def u u).symm
    _ = _ := by simp [inner_self_eq_norm_sq_to_K]

private theorem weightedL2Duality_equiv_absCont (μ : Measure G) {g : G → ℝ≥0}
    (hg : Measurable g) (hpos : ∀ x, 0 < g x) :
    μ ≪ μ.withDensity (fun x ↦ (g x : ℝ≥0∞)) :=
  withDensity_absolutelyContinuous' hg.coe_nnreal_ennreal.aemeasurable
    (Filter.Eventually.of_forall fun x ↦ by simpa using (hpos x).ne')

private theorem weightedL2Duality_equiv_rep (μ : Measure G) {g : G → ℝ≥0}
    (hg : Measurable g) (hpos : ∀ x, 0 < g x)
    {ν₁ ν₂ : Measure G} (h₁ : ν₁ = μ.withDensity (fun x ↦ (g x : ℝ≥0∞)))
    (h₂ : ν₂ = μ.withDensity (fun x ↦ (((g x)⁻¹ : ℝ≥0) : ℝ≥0∞))) (v : Lp ℂ 2 ν₂) :
    ∃ W : Lp ℂ 2 ν₁,
      (W : G → ℂ) =ᵐ[μ] (fun x ↦ conj (v x) / (g x : ℂ)) ∧
      ∀ u : Lp ℂ 2 ν₁,
        Integrable (fun x ↦ u x * v x) μ ∧ ∫ x, u x * v x ∂μ = inner ℂ W u := by
  subst h₁ h₂
  have hgi : Measurable fun x ↦ (g x)⁻¹ := hg.inv
  have hac1 := weightedL2Duality_equiv_absCont μ hg hpos
  let w : G → ℂ := fun x ↦ conj (v x) / (g x : ℂ)
  have hwm : StronglyMeasurable w :=
    (Complex.continuous_conj.comp_stronglyMeasurable (Lp.stronglyMeasurable v)).div
      (Complex.measurable_ofReal.comp (measurable_coe_nnreal_real.comp hg)).stronglyMeasurable
  have hmem : MemLp w 2 (μ.withDensity (fun x ↦ (g x : ℝ≥0∞))) := by
    rw [memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable,
      integrable_withDensity_iff_integrable_smul hg]
    have hv2 := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable v)).mp (Lp.memLp v)
    rw [integrable_withDensity_iff_integrable_smul hgi] at hv2
    refine hv2.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    have hx := (hpos x).ne'
    simp only [w, NNReal.smul_def, smul_eq_mul, norm_div, Complex.norm_conj, NNReal.coe_inv,
      Complex.norm_real, Real.norm_eq_abs, NNReal.abs_eq]
    field_simp
  refine ⟨hmem.toLp w, hac1.ae_le hmem.coeFn_toLp, fun u ↦ ?_⟩
  have hpt : (fun x ↦ g x • inner ℂ ((hmem.toLp w) x) (u x)) =ᵐ[μ] fun x ↦ u x * v x := by
    filter_upwards [hac1.ae_le hmem.coeFn_toLp] with x hx
    rw [hx]
    have hx0 : (g x : ℂ) ≠ 0 := by exact_mod_cast (hpos x).ne'
    simp only [w, NNReal.smul_def, RCLike.inner_apply, map_div₀, Complex.conj_conj,
      Complex.conj_ofReal, Complex.real_smul]
    field_simp
  have hint := L2.integrable_inner (𝕜 := ℂ) (hmem.toLp w) u
  rw [integrable_withDensity_iff_integrable_smul hg] at hint
  refine ⟨hint.congr hpt, ?_⟩
  rw [L2.inner_def, integral_withDensity_eq_integral_smul hg]
  exact (integral_congr_ae hpt).symm

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
        weightedL2Duality μ hf hf_pos hν hνdual u (J ℓ) = ℓ u := by
  have hfi_pos : ∀ x, 0 < (f x)⁻¹ := fun x ↦ inv_pos.mpr (hf_pos x)
  have hfi : Measurable fun x ↦ (f x)⁻¹ := hf.inv
  choose M hMae hM using weightedL2Duality_equiv_rep μ hf hf_pos hν hνdual
  subst hν hνdual
  have hac2 := weightedL2Duality_equiv_absCont μ hfi hfi_pos
  have hνac := withDensity_absolutelyContinuous μ (fun x ↦ (f x : ℝ≥0∞))
  have hnorm : ∀ v, ‖M v‖ = ‖v‖ := by
    intro v
    have h1 : inner ℂ (M v) (M v) = inner ℂ v v := by
      rw [← (hM v (M v)).2, L2.inner_def, integral_withDensity_eq_integral_smul hfi]
      refine integral_congr_ae ?_
      filter_upwards [hMae v] with x hx
      rw [hx]
      have hx0 : (f x : ℂ) ≠ 0 := by exact_mod_cast (hf_pos x).ne'
      simp only [NNReal.smul_def, RCLike.inner_apply, NNReal.coe_inv, Complex.real_smul,
        Complex.ofReal_inv]
      field_simp
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h1
    have h3 : ‖M v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h1
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h3
  let R : Lp ℂ 2 (μ.withDensity fun x ↦ ↑((f x)⁻¹)) →ₗ[ℂ]
      StrongDual ℂ (Lp ℂ 2 (μ.withDensity fun x ↦ ↑(f x))) :=
    { toFun := fun v ↦ InnerProductSpace.toDual ℂ _ (M v)
      map_add' := fun v₁ v₂ ↦ by
        ext u
        rw [add_apply]
        simp only [InnerProductSpace.toDual_apply_apply]
        rw [← (hM _ u).2, ← (hM v₁ u).2, ← (hM v₂ u).2, ← integral_add (hM v₁ u).1 (hM v₂ u).1]
        refine integral_congr_ae ?_
        filter_upwards [hac2.ae_le (Lp.coeFn_add v₁ v₂)] with x hx
        rw [hx, Pi.add_apply, mul_add]
      map_smul' := fun c v ↦ by
        ext u
        rw [RingHom.id_apply, smul_apply]
        simp only [InnerProductSpace.toDual_apply_apply]
        rw [← (hM _ u).2, ← (hM v u).2, smul_eq_mul, ← integral_const_mul]
        refine integral_congr_ae ?_
        filter_upwards [hac2.ae_le (Lp.coeFn_smul c v)] with x hx
        rw [hx, Pi.smul_apply, smul_eq_mul]
        ring }
  have hR : ∀ v u, R v u = ∫ x, u x * v x ∂μ := fun v u ↦ (hM v u).2.symm
  let Ri : Lp ℂ 2 (μ.withDensity fun x ↦ ↑((f x)⁻¹)) →ₗᵢ[ℂ]
      StrongDual ℂ (Lp ℂ 2 (μ.withDensity fun x ↦ ↑(f x))) :=
    { toLinearMap := R
      norm_map' := fun v ↦ by
        change ‖InnerProductSpace.toDual ℂ _ (M v)‖ = ‖v‖
        rw [LinearIsometryEquiv.norm_map, hnorm] }
  have hsurj : Function.Surjective Ri := by
    intro ℓ
    let y := (InnerProductSpace.toDual ℂ _).symm ℓ
    obtain ⟨V, hVae, -⟩ := weightedL2Duality_equiv_rep μ (g := fun x ↦ (f x)⁻¹) hfi hfi_pos rfl (by simp) y
    refine ⟨V, ?_⟩
    have hMV : M V = y := by
      refine Lp.ext (hνac.ae_le ?_)
      filter_upwards [hMae V, hVae] with x h1 h2
      rw [h1, h2]
      have hx0 : (f x : ℂ) ≠ 0 := by exact_mod_cast (hf_pos x).ne'
      simp only [map_div₀, Complex.conj_conj, NNReal.coe_inv, Complex.ofReal_inv, map_inv₀,
        Complex.conj_ofReal]
      field_simp
    change InnerProductSpace.toDual ℂ _ (M V) = ℓ
    rw [hMV, LinearIsometryEquiv.apply_symm_apply]
  let J := (LinearIsometryEquiv.ofSurjective Ri hsurj).symm
  have hJ : ∀ ℓ, Ri (J ℓ) = ℓ := fun ℓ ↦
    (LinearIsometryEquiv.ofSurjective Ri hsurj).apply_symm_apply ℓ
  refine ⟨J, fun ℓ u ↦ ⟨(hM _ u).1, ?_⟩, fun J' hJ' ↦ ?_⟩
  · change ∫ x, u x * J ℓ x ∂μ = ℓ u
    rw [← hR]
    exact DFunLike.congr_fun (hJ ℓ) u
  · refine LinearIsometryEquiv.ext fun ℓ ↦ Ri.injective ?_
    rw [hJ ℓ]
    ext u
    change R (J' ℓ) u = ℓ u
    exact (hR _ _).trans (hJ' ℓ u).2

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
      (transpose (θ 0) y / (f y : ℂ)) * φ 0 x := by
  simp [schauderKernelPartialSum]

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
