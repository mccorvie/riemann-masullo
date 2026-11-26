module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalArchimedeanBruhatTest
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalOrderZeroLevel
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalQuotientMaskAction
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealEvenHeatTrace
import RiemannMasullo.AppC_LCTVS.Sec3a_part2
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Gaussian heat traces of the arithmetic rational order-zero level

For the rational stage with no finite places the norm half-twist is unitary.
It carries the cutoff and reciprocal dilations in position space into the norm
cutoff and Hardy–Sobolev convolution on the quotient. The two-sided logarithmic
Gaussian heat of their arithmetic compression therefore has the same Hilbert trace.

The logarithmic heat prescription is due to mrshu in #7354. The proof uses
thierryaaron’s full-line level (#7651), mrshu’s Haar normalization (#7657), and
the real-even heat trace (#7646). Mrshu computes the individual dilation trace in #7671.
Thierryaaron computes the unsmoothed upper-cutoff trace of an interval average in #7681.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField ProbabilityTheory Set
open scoped CompactlySupported NumberField.AdeleRing NNReal ENNReal InnerProductSpace Topology

namespace RiemannMasullo.AnnularBand

open FlatPolar

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- Unitary transport of a nuclear endomorphism between two Hilbert spaces. -/
private def unitaryNuclearTransport (e : E ≃ₗᵢ[ℂ] F) (A : nuclearEndomorphisms E) :
    nuclearEndomorphisms F :=
  ⟨(e : E →L[ℂ] F).comp (A.val.comp (e.symm : F →L[ℂ] E)),
    (traceNorm_sandwich_le A.val A.property (e.symm : F →L[ℂ] E) (e : E →L[ℂ] F)).choose⟩

/-- Computing the diagonal in the transported Hilbert basis preserves the Hilbert trace. -/
private theorem hilbertTrace_unitaryNuclearTransport (e : E ≃ₗᵢ[ℂ] F) (A : nuclearEndomorphisms E) :
    hilbertTrace (unitaryNuclearTransport e A) = hilbertTrace A := by
  classical
  let b := (exists_hilbertBasis (𝕜 := ℂ) (E := E)).choose_spec.choose
  let c := (exists_hilbertBasis (𝕜 := ℂ) (E := F)).choose_spec.choose
  let d : HilbertBasis _ ℂ F := ⟨e.symm.trans b.repr⟩
  let T := unitaryNuclearTransport e A
  change (∑' j, inner ℂ (c j) (T.val (c j))) = ∑' i, inner ℂ (b i) (A.val (b i))
  refine (tsum_hilbertDiagonal_eq c d T.val T.property).trans (tsum_congr fun i ↦ ?_)
  change inner ℂ (e (b i)) (e (A.val (e.symm (e (b i))))) = _
  rw [e.symm_apply_apply, e.inner_map_map]

private theorem mem_nuclearEndomorphisms_of_eq (A : nuclearEndomorphisms E) (B : E →L[ℂ] E)
    (h : B = A.val) : B ∈ nuclearEndomorphisms E :=
  (congrArg (fun T : E →L[ℂ] E ↦ T ∈ nuclearEndomorphisms E) h).mpr A.property

omit [CompleteSpace E] [CompleteSpace F] in
private theorem eq_unitaryConjugate_of_intertwines (e : E ≃ₗᵢ[ℂ] F) (A : F →L[ℂ] F)
    (T : E →L[ℂ] E) (h : ∀ u, A (e u) = e (T u)) :
    A = (e : E →L[ℂ] F).comp (T.comp (e.symm : F →L[ℂ] E)) := by
  apply ContinuousLinearMap.ext
  intro v
  exact (congrArg A (e.apply_symm_apply v)).symm.trans (h (e.symm v))

set_option maxSynthPendingDepth 8
set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

local notation "J" => SIdeleQuotient ℚ ∅
local notation "m" => continuousSIdeleQuotientNorm ℚ ∅
local notation "R(" g ")" => (((m g).val : ℝ))
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "ν₀" => (μ).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (Real.log (R(g)))))
local notation "Hq" => Lp ℂ 2 ν₀
local notation "ν₊" => volume.restrict (Ioi (0 : ℝ))
local notation "H₊" => Lp ℂ 2 ν₊
local notation "posR(" g ")" => NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)

local instance : BorelSpace J := ⟨rfl⟩
local instance : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
local instance : T2Space J := by
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
  exact inferInstanceAs (T2Space (_ ⧸ _))
local instance : SecondCountableTopology J := by
  let (v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) : ProperSpace (v.val.adicCompletion ℚ) :=
    properSpace_adicCompletion v.val
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing ℚ ∅) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ)))
  let : SecondCountableTopology (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).1.secondCountableTopology
  infer_instance
local instance : LocallyCompactSpace J := by
  let : LocallyCompactSpace (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).2.2.1
  exact inferInstanceAs (LocallyCompactSpace (_ ⧸ _))
local instance : (μ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)).1

local notation "U₀" => orderZeroHalfTwist

/-- Centered logarithmic Gaussian heat at variance `τ` on the true rational quotient. -/
def quotientLogHeat (τ : ℝ≥0) : Hq →L[ℂ] Hq :=
  (U₀ : H₊ →L[ℂ] Hq).comp ((logHeat τ).comp ((U₀).symm : Hq →L[ℂ] H₊))

set_option maxHeartbeats 600000 in
/-- Every section of the quotient norm realizes the variance-`τ` heat as the strong
Gaussian average of the actual Hardy–Sobolev group translations of log-norm `-t`. -/
theorem quotientLogHeat_eq_integral_translation (τ : ℝ≥0) (v : Hq)
    (σ : ℝ≥0ˣ → J) (hσ : Function.RightInverse σ (m)) :
    quotientLogHeat τ v =
      ∫ t : ℝ, hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl
        (σ (expRadialUnit (-t))) v ∂gaussianReal 0 τ := by
  change U₀ (logHeat τ ((U₀).symm v)) = _
  rw [logHeat_apply]
  have hh (f : ℝ → H₊) : (∫ t, U₀ (f t) ∂gaussianReal 0 τ) = U₀ (∫ t, f t ∂gaussianReal 0 τ) :=
    (U₀).toLinearIsometry.integral_comp_comm f
  refine (hh _).symm.trans ?_
  apply integral_congr_ae
  filter_upwards with t
  let q := σ (expRadialUnit (-t))
  have hscale : R(q)⁻¹ = Real.exp t := by
    rw [show (m q) = expRadialUnit (-t) from hσ _, expRadialUnit_coe, Real.exp_neg, inv_inv]
  have htr := quotientTranslation_orderZeroHalfTwist q ((U₀).symm v)
  let D (a : {z : ℝ // 0 < z}) := U₀ (positiveRayDilation a.val a.property ((U₀).symm v))
  have hsc : (⟨Real.exp t, Real.exp_pos t⟩ : {z : ℝ // 0 < z}) =
      ⟨R(q)⁻¹, inv_pos.mpr (posR(q))⟩ := Subtype.ext hscale.symm
  have hlast := congrArg (hardySobolevTranslation μ m 0 0 0 le_rfl le_rfl q) ((U₀).apply_symm_apply v)
  exact (congrArg D hsc).trans (htr.symm.trans hlast)

/-- The bounded compression uses both true arithmetic level projections, the actual
norm cutoff and the compact quotient convolution in their operator order. -/
def quotientMeanZeroCompact (B h L : ℝ) (φ : C_c(ℝ≥0ˣ, ℂ)) : Hq →L[ℂ] Hq :=
  (orderZeroLevelProjection B).comp
    ((modulatedAbsoluteCutoffOperator m ν₀ (Ioc h L) measurableSet_Ioc).comp
      ((rationalQuotientRadialConvolution φ).comp (orderZeroLevelProjection B)))

set_option maxHeartbeats 1000000 in
/-- The full arithmetic operator is unitary conjugation of the physical compression. -/
theorem quotientMeanZeroCompact_eq_physical {B : ℝ} (hB : 0 < B) (h L : ℝ)
    (φ : C_c(ℝ≥0ˣ, ℂ)) :
    quotientMeanZeroCompact B h L φ =
      (U₀ : H₊ →L[ℂ] Hq).comp
        ((cosinePhysicalNuclear (meanZeroCompactCosineTraceOperator h L B φ)).val.comp
          ((U₀).symm : Hq →L[ℂ] H₊)) := by
  rw [cosinePhysicalNuclear_meanZeroCompact_val]
  apply eq_unitaryConjugate_of_intertwines
  intro u
  let P := orderZeroLevelProjection B
  let C := (modulatedAbsoluteCutoffOperator m ν₀ (Ioc h L) measurableSet_Ioc).comp
    (rationalQuotientRadialConvolution φ)
  let Q := physicalMeanZeroBandProjection B
  let D := (spatialCutoff h L).comp (compactInverseDilationAction φ)
  change P (C (P (U₀ u))) = U₀ (Q (D (Q u)))
  exact (congrArg (fun v ↦ P (C v)) (orderZeroLevelProjection_halfTwist hB u)).trans
    ((congrArg P (quotientCutoff_radialConvolution_orderZeroHalfTwist h L φ (Q u))).trans
      (orderZeroLevelProjection_halfTwist hB (D (Q u))))

set_option maxHeartbeats 700000 in
/-- The actual finite quotient compression, packaged with its nuclearity proof. -/
def quotientMeanZeroCompactNuclear {B : ℝ} (hB : 0 < B) (h L : ℝ)
    (φ : C_c(ℝ≥0ˣ, ℂ)) : nuclearEndomorphisms Hq :=
  ⟨quotientMeanZeroCompact B h L φ, by
    exact mem_nuclearEndomorphisms_of_eq
      (unitaryNuclearTransport U₀ (cosinePhysicalNuclear (meanZeroCompactCosineTraceOperator h L B φ)))
      (quotientMeanZeroCompact B h L φ) (quotientMeanZeroCompact_eq_physical hB h L φ)⟩

/-- Two genuine quotient Gaussians acting on the left and right of a nuclear operator. -/
def quotientLogHeatSandwich (τ : ℝ≥0) (A : nuclearEndomorphisms Hq) : nuclearEndomorphisms Hq :=
  ⟨(quotientLogHeat τ).comp (A.val.comp (quotientLogHeat τ)),
    mul_mem_nuclearEndomorphisms_left (quotientLogHeat τ)
      ⟨_, mul_mem_nuclearEndomorphisms_right (quotientLogHeat τ) A⟩⟩

/-- Logarithmic radius sends the actual Weil measure on the rational quotient to Lebesgue measure. -/
theorem quotientLogNorm_measurePreserving :
    MeasurePreserving (fun q : J ↦ Real.log (R(q))) μ (volume : Measure ℝ) := by
  let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
  have hH : positiveRealHaar = (volume : Measure ℝ).map E := by
    unfold positiveRealHaar
    apply congrArg (fun f : ℝ → ℝ≥0ˣ ↦ volume.map f)
    funext t
    apply Units.ext
    apply NNReal.eq
    exact Real.coe_toNNReal _ (Real.exp_pos t).le
  have hE : MeasurePreserving E.symm positiveRealHaar (volume : Measure ℝ) := by
    refine ⟨E.symm.continuous.measurable, ?_⟩
    rw [hH, Measure.map_map E.symm.continuous.measurable E.continuous.measurable]
    rw [show (E.symm ∘ E) = id from funext E.symm_apply_apply, Measure.map_id]
  have hN : MeasurePreserving (m) μ positiveRealHaar := ⟨(m).continuous.measurable, RatEmptyNormHaar.map_norm⟩
  have he (a : ℝ≥0ˣ) : E.symm a = Real.log (a.val : ℝ) := by
    have hx (x : ℝ) : ((E x).val : ℝ) = Real.exp x := rfl
    rw [← Real.log_exp (E.symm a), ← hx, E.apply_symm_apply]
  rw [show (fun q : J ↦ Real.log (R(q))) = E.symm ∘ (m) from funext fun q ↦ (he _).symm]
  exact hE.comp hN

private theorem quotientIntegral_logRadius {D : ℝ → ℂ} (hi : Integrable D) :
    Integrable (fun q : J ↦ D (Real.log (R(q)))) μ ∧
      (∫ q : J, D (Real.log (R(q))) ∂μ) = ∫ t : ℝ, D t := by
  let N (q : J) := Real.log (R(q))
  have hn : MeasurePreserving N μ (volume : Measure ℝ) := quotientLogNorm_measurePreserving
  have hmeas : AEStronglyMeasurable D ((μ).map N) := hn.map_eq.symm ▸ hi.aestronglyMeasurable
  refine ⟨hn.integrable_comp_of_integrable hi, ?_⟩
  calc
    (∫ q : J, D (N q) ∂μ) = ∫ t : ℝ, D t ∂(μ).map N := (integral_map hn.measurable.aemeasurable hmeas).symm
    _ = _ := by rw [hn.map_eq]

/-- The continuous physical log-coordinate heat kernel pulled back through both arithmetic
quotient variables. The quotient measure transfers to ordinary logarithmic Lebesgue measure. -/
def quotientLogHaarHeatKernel (τ : ℝ≥0) (A : Hq →L[ℂ] Hq) (q p : J) : ℂ :=
  haarHeatKernel τ (((U₀).symm : Hq →L[ℂ] H₊).comp (A.comp (U₀ : H₊ →L[ℂ] Hq)))
    (Real.log (R(q))) (Real.log (R(p)))

/-- Joint continuity makes the pulled-back quotient diagonal pointwise canonical at positive variance. -/
theorem continuous_quotientLogHaarHeatKernel (τ : ℝ≥0) (A : Hq →L[ℂ] Hq) :
    Continuous (fun p : J × J ↦ quotientLogHaarHeatKernel τ A p.1 p.2) := by
  let T := ((U₀).symm : Hq →L[ℂ] H₊).comp (A.comp (U₀ : H₊ →L[ℂ] Hq))
  have hr : Continuous (fun q : J ↦ R(q)) := NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)
  have hs : Continuous (fun q : J ↦ (Real.sqrt (R(q)) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp hr)
  have hxy : Continuous (fun p : J × J ↦ (R(p.1), R(p.2))) :=
    (hr.comp continuous_fst).prodMk (hr.comp continuous_snd)
  have hK : Continuous (fun p : J × J ↦ heatSandwichKernel τ T (R(p.1), R(p.2))) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (continuousAt_heatSandwichKernel τ T (posR(p.1)) (posR(p.2))).comp (x := p)
      (f := fun z : J × J ↦ (R(z.1), R(z.2))) hxy.continuousAt
  let a (q : J) : ℂ := (Real.sqrt (R(q)) : ℂ)
  let k (p : J × J) := heatSandwichKernel τ T (R(p.1), R(p.2))
  let F (p : J × J) : ℂ := a p.1 * a p.2 * k p
  have hF : Continuous F :=
    ((hs.comp (continuous_fst : Continuous (Prod.fst : J × J → J))).mul
      (hs.comp (continuous_snd : Continuous (Prod.snd : J × J → J)))).mul hK
  have he (p : J × J) : quotientLogHaarHeatKernel τ A p.1 p.2 = F p := by
    simp only [quotientLogHaarHeatKernel, haarHeatKernel, Real.exp_log (posR(_)), T, F, a, k]
  rw [show (fun p : J × J ↦ quotientLogHaarHeatKernel τ A p.1 p.2) = F from funext he]
  exact hF

private theorem quotientHalfTwist_haar_rep (v : H₊) (f : ℝ → ℂ) (hf : Measurable f)
    (hv : (v : ℝ → ℂ) =ᵐ[ν₊] f) :
    (U₀ v : J → ℂ) =ᵐ[μ] fun q ↦ (Real.sqrt (R(q)) : ℂ) * f (R(q)) :=
  (show μ ≤ ν₀ by simp [intervalSobolevDensity]).absolutelyContinuous.ae_eq
    (orderZeroHalfTwist_coeFn_of_ae_eq v f hf hv)

private theorem measurable_heatRepresentative (τ : ℝ≥0) (v : H₊) :
    Measurable (heatRepresentative τ v) := by
  have h : Measurable (fun p : ℝ × ℝ ↦ (Real.sqrt (Real.exp p.1) : ℂ) * v (Real.exp p.1 * p.2)) :=
    ((Complex.measurable_ofReal.comp Real.continuous_sqrt.measurable).comp
      (Real.measurable_exp.comp measurable_fst)).mul ((Lp.stronglyMeasurable v).measurable.comp
        ((Real.measurable_exp.comp measurable_fst).mul measurable_snd))
  exact h.stronglyMeasurable.integral_prod_left'.measurable

set_option maxHeartbeats 1000000 in
/-- With the actual Weil quotient measure, integrating the two-variable kernel against
any quotient `L²` vector represents the doubly Gaussian-smoothed bounded operator. -/
theorem quotientLogHaarHeatKernel_integral {τ : ℝ≥0} (hτ : 0 < τ) (A : Hq →L[ℂ] Hq) (v : Hq) :
    ∀ᵐ q ∂μ, Integrable (fun p : J ↦ quotientLogHaarHeatKernel τ A q p * v p) μ ∧
      (∫ p : J, quotientLogHaarHeatKernel τ A q p * v p ∂μ) =
        (quotientLogHeat τ (A (quotientLogHeat τ v)) : J → ℂ) q := by
  let T := ((U₀).symm : Hq →L[ℂ] H₊).comp (A.comp (U₀ : H₊ →L[ℂ] Hq))
  let f := (U₀).symm v
  let g := T (logHeat τ f)
  have hfv : (v : J → ℂ) =ᵐ[μ] fun q ↦ (Real.sqrt (R(q)) : ℂ) * f (R(q)) := by
    simpa only [f, LinearIsometryEquiv.apply_symm_apply] using
      quotientHalfTwist_haar_rep f f (Lp.stronglyMeasurable f).measurable .rfl
  have hgv := quotientHalfTwist_haar_rep (logHeat τ g) (heatRepresentative τ g)
    (measurable_heatRepresentative τ g) (logHeat_ae_eq_heatRepresentative τ g)
  filter_upwards [hgv] with q hq
  let D (t : ℝ) := haarHeatKernel τ T (Real.log (R(q))) t * ((Real.sqrt (Real.exp t) : ℂ) * f (Real.exp t))
  obtain ⟨hI, hK⟩ := haarHeatKernel_integral hτ T f (Real.log (R(q)))
  obtain ⟨hi, he⟩ := quotientIntegral_logRadius (D := D) hI
  have hp : (fun p : J ↦ D (Real.log (R(p)))) =ᵐ[μ]
      fun p : J ↦ quotientLogHaarHeatKernel τ A q p * v p := by
    filter_upwards [hfv] with p hp
    simp only [D, Real.exp_log (posR(p)), hp, quotientLogHaarHeatKernel, T]
  refine ⟨hi.congr hp, (integral_congr_ae hp.symm).trans (he.trans ?_)⟩
  rw [Real.exp_log (posR(q))] at hK
  exact hK.trans hq.symm

private theorem quotientLogHeatSandwich_transport (τ : ℝ≥0) (A : nuclearEndomorphisms H₊) :
    quotientLogHeatSandwich τ (unitaryNuclearTransport U₀ A) =
      unitaryNuclearTransport U₀ (logHeatSandwich τ A) := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  change U₀ (logHeat τ ((U₀).symm (U₀ (A.val ((U₀).symm (U₀ (logHeat τ ((U₀).symm v)))))))) =
    U₀ (logHeat τ (A.val (logHeat τ ((U₀).symm v))))
  simp only [LinearIsometryEquiv.symm_apply_apply]

private theorem quotientHaarDiagonal_rayTrace {τ : ℝ≥0} (hτ : 0 < τ) (T : nuclearEndomorphisms H₊) :
    Integrable (fun q : J ↦ haarHeatKernel τ T.val (Real.log (R(q))) (Real.log (R(q)))) μ ∧
      (∫ q : J, haarHeatKernel τ T.val (Real.log (R(q))) (Real.log (R(q))) ∂μ) =
        hilbertTrace (logHeatSandwich τ T) := by
  have hh := haarHeatKernel_diagonal_trace hτ T
  have hi := quotientIntegral_logRadius (D := fun t ↦ haarHeatKernel τ T.val t t) hh.1
  exact ⟨hi.1, hi.2.trans hh.2⟩

private theorem unitaryNuclearTransport_inverse (e : E ≃ₗᵢ[ℂ] F) (A : nuclearEndomorphisms F) :
    unitaryNuclearTransport e (unitaryNuclearTransport e.symm A) = A := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  change e (e.symm (A.val (e (e.symm v)))) = A.val v
  simp only [e.apply_symm_apply]

set_option maxHeartbeats 850000 in
/-- Every nuclear quotient operator has an integrable canonical heat-kernel diagonal.
Its integral against the actual rational quotient Haar measure is the Hilbert trace. -/
theorem quotientLogHaarHeatKernel_diagonal_trace {τ : ℝ≥0} (hτ : 0 < τ)
    (A : nuclearEndomorphisms Hq) :
    Integrable (fun q : J ↦ quotientLogHaarHeatKernel τ A.val q q) μ ∧
      (∫ q : J, quotientLogHaarHeatKernel τ A.val q q ∂μ) =
        hilbertTrace (quotientLogHeatSandwich τ A) := by
  let T : nuclearEndomorphisms H₊ := unitaryNuclearTransport (U₀).symm A
  have hAT : unitaryNuclearTransport U₀ T = A := unitaryNuclearTransport_inverse U₀ A
  have hd := quotientHaarDiagonal_rayTrace hτ T
  refine ⟨hd.1, hd.2.trans ?_⟩
  calc
    hilbertTrace (logHeatSandwich τ T) = hilbertTrace (unitaryNuclearTransport U₀ (logHeatSandwich τ T)) :=
      (hilbertTrace_unitaryNuclearTransport U₀ _).symm
    _ = _ := congrArg hilbertTrace ((quotientLogHeatSandwich_transport τ T).symm.trans
      (congrArg (quotientLogHeatSandwich τ) hAT))

set_option maxHeartbeats 700000 in
/-- At every variance, including zero, and all finite endpoints, the Hilbert trace of the
two-sided arithmetic heat compression equals the physical real-even mean-zero trace. -/
theorem hilbertTrace_quotientLogHeatSandwich_meanZeroCompact {B : ℝ} (hB : 0 < B)
    (h L : ℝ) (τ : ℝ≥0) (φ : C_c(ℝ≥0ˣ, ℂ)) :
    hilbertTrace (quotientLogHeatSandwich τ (quotientMeanZeroCompactNuclear hB h L φ)) =
      hilbertTrace (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ)) := by
  let A := cosinePhysicalNuclear (meanZeroCompactCosineTraceOperator h L B φ)
  have hconj : quotientMeanZeroCompactNuclear hB h L φ = unitaryNuclearTransport U₀ A :=
    Subtype.ext (quotientMeanZeroCompact_eq_physical hB h L φ)
  rw [hconj, quotientLogHeatSandwich_transport, hilbertTrace_unitaryNuclearTransport]
  exact (congrArg hilbertTrace
    (logHeatSandwich_cosinePhysicalNuclear τ (meanZeroCompactCosineTraceOperator h L B φ))).trans
    (hilbertTrace_cosinePhysicalNuclear _)

set_option maxHeartbeats 700000 in
/-- On a compact norm window strictly above one, the heat trace of the genuine rational
arithmetic compression converges to the real Connes–Weil principal value minus the negative
half-moment along the simultaneous spatial, frequency and logarithmic heat prescription. -/
theorem tendsto_quotientMeanZeroCompact_heatTrace_realPV {ι : Type*} {l : Filter ι}
    {B h L : ι → ℝ} {τ : ι → ℝ≥0}
    (hB : ∀ i, 0 < B i) (hh : ∀ᶠ i in l, 0 ≤ h i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hτ : Tendsto τ l (𝓝 0)) (hw : Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 0))
    (φ : C_c(ℝ≥0ˣ, ℂ)) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc (1 + η) M)
    (test : BruhatCompactSupport Rat.infinitePlace.Completionˣ)
    (hm : ∀ (u : Rat.infinitePlace.Completionˣ) (a : ℝ≥0ˣ), (a.val : ℝ) = ‖u.val‖ → test.val u = φ a) :
    Tendsto (fun i ↦ hilbertTrace (quotientLogHeatSandwich (τ i)
      (quotientMeanZeroCompactNuclear (hB i) (h i) (L i) φ))) l
      (𝓝 (infiniteConnesWeilPrincipalValue Rat.infinitePlace test -
        ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar)) := by
  have hp := (tendsto_meanZeroCompactCosine_heatTrace hB hh hBh hBL hτ hw φ hη hs).congr
    (fun i ↦ (hilbertTrace_quotientLogHeatSandwich_meanZeroCompact (hB i) (h i) (L i) (τ i) φ).symm)
  have hv := compactCosineOrbitalValue_eq_realPrincipalValue Rat.infinitePlace Rat.isReal_infinitePlace
    φ hη (fun a ha ↦ (hs a ha).1) test hm
  simpa only [hv] using hp

set_option maxHeartbeats 700000 in
/-- The diagonal of the genuine two-variable quotient heat kernel converges after integration
against the quotient Weil measure. Only this diagonal requires eventually positive variance. -/
theorem tendsto_quotientMeanZeroCompact_haarDiagonal_realPV {ι : Type*} {l : Filter ι}
    {B h L : ι → ℝ} {τ : ι → ℝ≥0}
    (hB : ∀ i, 0 < B i) (hh : ∀ᶠ i in l, 0 ≤ h i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hpos : ∀ᶠ i in l, 0 < τ i) (hτ : Tendsto τ l (𝓝 0))
    (hw : Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 0))
    (φ : C_c(ℝ≥0ˣ, ℂ)) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ a ∈ tsupport φ, (a.val : ℝ) ∈ Icc (1 + η) M)
    (test : BruhatCompactSupport Rat.infinitePlace.Completionˣ)
    (hm : ∀ (u : Rat.infinitePlace.Completionˣ) (a : ℝ≥0ˣ), (a.val : ℝ) = ‖u.val‖ → test.val u = φ a) :
    Tendsto (fun i ↦ ∫ q : J, quotientLogHaarHeatKernel (τ i)
      (quotientMeanZeroCompact (B i) (h i) (L i) φ) q q ∂μ) l
      (𝓝 (infiniteConnesWeilPrincipalValue Rat.infinitePlace test -
        ∫ a : ℝ≥0ˣ, φ a / (Real.sqrt a.val : ℂ) ∂positiveRealHaar)) := by
  apply (tendsto_quotientMeanZeroCompact_heatTrace_realPV hB hh hBh hBL hτ hw φ hη hs test hm).congr'
  filter_upwards [hpos] with i hi
  exact (quotientLogHaarHeatKernel_diagonal_trace hi (quotientMeanZeroCompactNuclear (hB i) (h i) (L i) φ)).2.symm

/-- The two native level projections compress the Chapter 9 action of a quotient Bruhat test. -/
def quotientBruhatLevelCompression (B h L : ℝ) (ψ : BruhatCompactSupport J) : Hq →L[ℂ] Hq :=
  (orderZeroLevelProjection B).comp
    ((modulatedAbsoluteCutoffOperator m ν₀ (Ioc h L) measurableSet_Ioc).comp
      ((hardySobolevTestAction μ m 0 0 0 le_rfl le_rfl ψ).comp (orderZeroLevelProjection B)))

set_option maxHeartbeats 900000 in
private theorem quotientBruhatLevelCompression_eq (B h L : ℝ) (ψ : BruhatCompactSupport J)
    (φ : C_c(ℝ≥0ˣ, ℂ))
    (hA : hardySobolevTestAction μ m 0 0 0 le_rfl le_rfl ψ = rationalQuotientRadialConvolution φ) :
    quotientBruhatLevelCompression B h L ψ = quotientMeanZeroCompact B h L φ := by
  exact congrArg (fun A : Hq →L[ℂ] Hq ↦ (orderZeroLevelProjection B).comp
    ((modulatedAbsoluteCutoffOperator m ν₀ (Ioc h L) measurableSet_Ioc).comp
      (A.comp (orderZeroLevelProjection B)))) hA

set_option maxHeartbeats 1000000 in
/-- The native order-zero compression is nuclear for every compact Bruhat test and every finite window. -/
def quotientBruhatLevelCompressionNuclear {B : ℝ} (hB : 0 < B) (h L : ℝ)
    (ψ : BruhatCompactSupport J) : nuclearEndomorphisms Hq :=
  ⟨quotientBruhatLevelCompression B h L ψ, by
    obtain ⟨φ, _, _, hA⟩ := exists_rayTest_support_hardySobolevTestAction_eq ψ univ isClosed_univ
      (fun g _ ↦ mem_univ (R(g)))
    exact mem_nuclearEndomorphisms_of_eq (quotientMeanZeroCompactNuclear hB h L φ) _
      (quotientBruhatLevelCompression_eq B h L ψ φ hA)⟩

set_option maxHeartbeats 1400000 in
/-- For a native Bruhat test away from and above norm one, the actual quotient trace and
integrated Haar diagonal tend to the principal value of its real-place restriction minus
its negative half-moment in quotient Tamagawa measure. The diagonal uses positive variances. -/
theorem tendsto_quotientBruhatLevel_heatTrace_haarDiagonal_realPV {ι : Type*} {l : Filter ι}
    {B h L : ι → ℝ} {τ : ι → ℝ≥0}
    (hB : ∀ i, 0 < B i) (hh : ∀ᶠ i in l, 0 ≤ h i)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hτ : Tendsto τ l (𝓝 0)) (hw : Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 0))
    (ψ : BruhatCompactSupport J) {η M : ℝ} (hη : 0 < η)
    (hs : ∀ g : J, ψ.val g ≠ 0 → R(g) ∈ Icc (1 + η) M) :
    let hminus := ∫ g : J, ψ.val g / (Real.sqrt (R(g)) : ℂ) ∂μ
    ∃ test : BruhatCompactSupport Rat.infinitePlace.Completionˣ,
      (∀ (u : Rat.infinitePlace.Completionˣ) (g : J), R(g) = ‖u.val‖ → test.val u = ψ.val g) ∧
      Tendsto (fun i ↦ hilbertTrace (quotientLogHeatSandwich (τ i)
        (quotientBruhatLevelCompressionNuclear (hB i) (h i) (L i) ψ))) l
          (𝓝 (infiniteConnesWeilPrincipalValue Rat.infinitePlace test - hminus)) ∧
      ((∀ᶠ i in l, 0 < τ i) →
        Tendsto (fun i ↦ ∫ q : J, quotientLogHaarHeatKernel (τ i)
          (quotientBruhatLevelCompression (B i) (h i) (L i) ψ) q q ∂μ) l
            (𝓝 (infiniteConnesWeilPrincipalValue Rat.infinitePlace test - hminus))) := by
  obtain ⟨φ, hφ, hsφ, hA⟩ := exists_rayTest_support_hardySobolevTestAction_eq ψ _ isClosed_Icc hs
  obtain ⟨test, htest⟩ := exists_realPlaceBruhatTest_of_rationalQuotient ψ
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
  have hm (u : Rat.infinitePlace.Completionˣ) (a : ℝ≥0ˣ) (ha : (a.val : ℝ) = ‖u.val‖) :
      test.val u = φ a := by
    have hn : m (σ a) = a := hσ a
    have he := htest u (σ a) (by
      change ((m (σ a)).val : ℝ) = ‖u.val‖
      rwa [hn])
    exact he.trans (by simpa only [hn] using (hφ (σ a)).symm)
  have hmoment := rationalQuotient_negativeHalfMoment_eq_ray ψ.val φ hφ
  have hop (i : ι) := quotientBruhatLevelCompression_eq (B i) (h i) (L i) ψ φ hA
  have hN (i : ι) : quotientBruhatLevelCompressionNuclear (hB i) (h i) (L i) ψ =
      quotientMeanZeroCompactNuclear (hB i) (h i) (L i) φ := Subtype.ext (hop i)
  refine ⟨test, htest, ?_, ?_⟩
  · simpa only [hN, hmoment] using
      tendsto_quotientMeanZeroCompact_heatTrace_realPV hB hh hBh hBL hτ hw φ hη hsφ test hm
  · intro hp
    simpa only [hop, hmoment] using
      tendsto_quotientMeanZeroCompact_haarDiagonal_realPV hB hh hBh hBL hp hτ hw φ hη hsφ test hm

end RiemannMasullo.AnnularBand
