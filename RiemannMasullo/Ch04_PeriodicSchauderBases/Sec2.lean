module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import all RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Baire.CompleteMetrizable
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
import RiemannMasullo.ForMathlib.Analysis.Fourier.PoissonSummation
import RiemannMasullo.ForMathlib.Topology.MetricSpace.CompactQuotient

/-!
# Periodization and Schauder bases on the positive real axis

Masullo, §4.2, pp. 161–174. The logarithmic coordinate is (x = log t).
The circle coordinate is (x / log γ) modulo one.
-/

@[expose] public noncomputable section

open Bornology Function MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff Distributions SchwartzMap

namespace RiemannMasullo

local notation "E" => PositiveRealExponentialDecay (Set.univ : Set ℝ)
local notation "S" => ElementarySchwartz 0 1 0 (PUnit : Type)
local notation "G" => ElementaryLieGroup 0 1 0 (PUnit : Type)
local notation "T" => AddCircle (1 : ℝ)
local notation "point" z => ((0, fun _ : Fin 1 ↦ z, 0, PUnit.unit) : G)
local notation "freq" => Equiv.intEquivNat.symm
local notation "phase[" γ ", " m "]" => (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (Real.log γ : ℂ))

section Periodization

variable (γ : ℝ) (hγ : 1 < γ)

/-- Paper: Definition 4.2.1.1, p. 162. Sum the translates of a logarithmic profile
at a representative of the unit-circle coordinate.
Deviation: The same formula is used on ordinary Schwartz profiles, as in Remark 4.2.2.6. -/
def cyclicPeriodizationValue (_hγ : 1 < γ) (f : 𝓢(ℝ, ℂ)) (g : G) : ℂ :=
  ∑' k : ℤ, f (Real.log γ * ((AddCircle.equivIco 1 0 (g.2.1 0)).val + k))

/-- Paper: Definition 4.2.1.1, p. 162. The sum converges and can be computed at
any real lift of the circle coordinate.
Deviation: This also checks the formula on the ordinary Schwartz space. -/
theorem cyclicPeriodizationValue_hasSum (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f (x + (k : ℝ) * Real.log γ))
      (cyclicPeriodizationValue γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by
  let L := Real.log γ
  have hL : L ≠ 0 := (Real.log_pos hγ).ne'
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL)
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (f.compSubConstCLM ℂ (-x))
  have hs : Summable (fun k : ℤ ↦ F (k : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((F.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  let a (k : ℤ) := f (x + (k : ℝ) * L)
  have ha : Summable a := by
    simpa [a, F, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, add_comm] using hs
  let r := ((AddCircle.equivIco (1 : ℝ) 0) ((x / L : ℝ) : T)).val
  change HasSum a (∑' k : ℤ, f (L * (r + k)))
  have hr : r = x / L - ⌊x / L⌋ := by
    dsimp only [r]
    rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one, ← Int.self_sub_floor]
  convert ha.hasSum using 1
  calc
    (∑' k : ℤ, f (L * (r + k))) = ∑' k : ℤ, a ((Equiv.subRight ⌊x / L⌋) k) := by
      apply tsum_congr
      intro k
      simp only [a, Equiv.subRight_apply, Int.cast_sub, hr]
      congr 1
      field_simp
      ring
    _ = ∑' k : ℤ, a k := (Equiv.subRight ⌊x / L⌋).tsum_eq a

/-- A smooth periodic lift gives an elementary Schwartz function on the circle. -/
private theorem mem_elementarySchwartz_circle_of_contDiff {h : T → ℂ}
    (hs : ContDiff ℝ ∞ (fun x : ℝ ↦ h (x : T))) :
    (fun g : G ↦ h (g.2.1 0)) ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  let X := EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1)
  let φ : G → ℂ := fun g ↦ h (g.2.1 0)
  let L : X →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)
  have hφ (a : Fin 0 → ℤ) (b : PUnit) :
      ContDiff ℝ ∞ (fun xt ↦ φ (elementaryCover xt a b)) := hs.comp L.contDiff
  refine ⟨hφ, fun i ↦ ?_⟩
  let s (x : ℝ) : X := (0, x • EuclideanSpace.single 0 1)
  have hsc : Continuous s := continuous_const.prodMk (continuous_id.smul continuous_const)
  let D := elementaryPartial φ i.2.1 i.2.2.1
  have hD := elementaryPartial_descends φ i.2.1 i.2.2.1 0 PUnit.unit (hφ 0 PUnit.unit)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hD.1.continuous.comp hsc).continuousOn
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = PUnit.unit := Subsingleton.elim _ _
  subst a b
  let r := (AddCircle.equivIco (1 : ℝ) 0) (xt.2 0 : T)
  have hr : (r : ℝ) ∈ Icc 0 1 := Ico_subset_Icc_self (by simpa using r.property)
  have he : elementaryCover (s r) (0 : Fin 0 → ℤ) PUnit.unit =
      elementaryCover xt 0 PUnit.unit := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ rfl)
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (↑((r.val • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0) : T) = _
    trans (r.val : T)
    · simp [PiLp.smul_apply]
    · exact AddCircle.coe_equivIco
  have hbound : ‖D xt 0 PUnit.unit‖ ≤ C := by
    dsimp only [D]
    rw [← hD.2 (s r) xt he]
    exact hC r hr
  simp only [Fin.prod_univ_zero, one_mul, ENNReal.coe_nnreal_eq, coe_nnNorm]
  exact ENNReal.ofReal_le_ofReal hbound

/-- Paper: Lemma 4.2.1.5(1), p. 165. The orbit sum gives a smooth function
on the circle.
Deviation: Smoothness also holds on the ordinary Schwartz source. -/
theorem cyclicPeriodizationValue_mem (f : 𝓢(ℝ, ℂ)) :
    cyclicPeriodizationValue γ hγ f ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  let h (z : T) := cyclicPeriodizationValue γ hγ f (point z)
  change (fun g : G ↦ h (g.2.1 0)) ∈ _
  apply mem_elementarySchwartz_circle_of_contDiff
  let L := Real.log γ
  have hL : L ≠ 0 := (Real.log_pos hγ).ne'
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL)
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have he : (fun x : ℝ ↦ h (x : T)) = fun x : ℝ ↦ ∑' n : ℤ, F (x + n) := by
    funext x
    simpa [h, F, e, L, hL, (Real.log_pos hγ).ne', add_mul] using
      (cyclicPeriodizationValue_hasSum γ hγ f (x * L)).tsum_eq.symm
  rw [he]
  exact schwartz_contDiff_periodization F

/-- Paper: Lemma 4.2.1.5(2), p. 165. The orbit sum is linear and continuous
in the Schwartz profile.
Deviation: The bundled properties also hold on the ordinary Schwartz source. -/
theorem cyclicPeriodizationValue_spec :
    (∀ f g, cyclicPeriodizationValue γ hγ (f + g) =
      cyclicPeriodizationValue γ hγ f + cyclicPeriodizationValue γ hγ g) ∧
    (∀ (c : ℂ) f, cyclicPeriodizationValue γ hγ (c • f) = c • cyclicPeriodizationValue γ hγ f) ∧
    Continuous (Y := S) (fun f ↦ (⟨cyclicPeriodizationValue γ hγ f,
      cyclicPeriodizationValue_mem γ hγ f⟩ : S)) := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  have : (uniformity 𝓢(ℝ, ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero 𝓢(ℝ, ℂ)]
    infer_instance
  have he (g : G) : ∃ L : 𝓢(ℝ, ℂ) →L[ℂ] ℂ, ∀ f, L f = cyclicPeriodizationValue γ hγ f g := by
    let r := ((AddCircle.equivIco (1 : ℝ) 0) (g.2.1 0)).val
    let t (k : ℤ) := Real.log γ * (r + k)
    have ht (k : ℤ) : t k = Real.log γ * r + (k : ℝ) * Real.log γ := by dsimp [t]; ring
    let ev (k : ℤ) := (BoundedContinuousFunction.evalCLM ℂ (t k)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ)
    let P (s : Finset ℤ) : 𝓢(ℝ, ℂ) →L[ℂ] ℂ := ∑ k ∈ s, ev k
    have hlim : Filter.Tendsto (fun s f ↦ P s f) Filter.atTop
        (𝓝 (fun f ↦ cyclicPeriodizationValue γ hγ f g)) := by
      rw [tendsto_pi_nhds]
      intro f
      have hs : Summable fun k : ℤ ↦ f (t k) := by
        simpa only [ht] using (cyclicPeriodizationValue_hasSum γ hγ f (Real.log γ * r)).summable
      have hP (s : Finset ℤ) : P s f = ∑ k ∈ s, f (t k) := by
        simp only [P, sum_apply]
        rfl
      simp_rw [hP]
      exact hs.hasSum
    exact ⟨continuousLinearMapOfTendsto P hlim, fun _ ↦ rfl⟩
  choose L hL using he
  have hadd (f g : 𝓢(ℝ, ℂ)) : cyclicPeriodizationValue γ hγ (f + g) =
      cyclicPeriodizationValue γ hγ f + cyclicPeriodizationValue γ hγ g := by
    funext x
    simpa only [Pi.add_apply, ← hL] using (L x).map_add f g
  have hsmul (c : ℂ) (f : 𝓢(ℝ, ℂ)) : cyclicPeriodizationValue γ hγ (c • f) =
      c • cyclicPeriodizationValue γ hγ f := by
    funext x
    simpa only [Pi.smul_apply, ← hL] using (L x).map_smul c f
  let A : 𝓢(ℝ, ℂ) →ₗ[ℂ] S :=
    { toFun f := ⟨_, cyclicPeriodizationValue_mem γ hγ f⟩
      map_add' f g := Subtype.ext (hadd f g)
      map_smul' c f := Subtype.ext (hsmul c f) }
  exact ⟨hadd, hsmul, continuous_toElementarySchwartz_of_eval A (fun g ↦ ⟨L g, hL g⟩)⟩

/-- Paper: Remark 4.2.2.6, p. 173. The cyclic orbit sum is a continuous linear
map from ordinary Schwartz profiles to smooth functions on the circle. -/
def cyclicSchwartzPeriodization : 𝓢(ℝ, ℂ) →L[ℂ] S where
  toFun f := ⟨cyclicPeriodizationValue γ hγ f, cyclicPeriodizationValue_mem γ hγ f⟩
  map_add' f g := Subtype.ext ((cyclicPeriodizationValue_spec γ hγ).1 f g)
  map_smul' c f := Subtype.ext ((cyclicPeriodizationValue_spec γ hγ).2.1 c f)
  cont := (cyclicPeriodizationValue_spec γ hγ).2.2

/-- Paper: Remark 4.2.2.6, p. 173. On the ordinary Schwartz space, periodization
has the same absolutely convergent orbit sum on a logarithmic lift. -/
theorem cyclicSchwartzPeriodization_hasSum (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f (x + (k : ℝ) * Real.log γ))
      (cyclicSchwartzPeriodization γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by
  exact cyclicPeriodizationValue_hasSum γ hγ f x

/-- Paper: Definition 4.2.1.1, p. 162. Periodization of an exponentially
decaying Schwartz function sums its translates by integer powers of γ.
Deviation: The source is represented by logarithmic profiles and the target
by the elementary Schwartz space on the unit circle. -/
def cyclicPeriodization : E →ₗ[ℂ] S :=
  (cyclicSchwartzPeriodization γ hγ).toLinearMap.comp
    (logExponentialDecayTwist univ ⟨0, mem_univ _⟩)

/-- Paper: (4.2.1.2), p. 162. The periodized value is the sum over the orbit
of any logarithmic lift. The statement records convergence of the series. -/
theorem cyclicPeriodization_hasSum (f : E) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f.val (x + (k : ℝ) * Real.log γ))
      (cyclicPeriodization γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by
  refine (cyclicSchwartzPeriodization_hasSum γ hγ
    (logExponentialDecayTwist univ ⟨0, mem_univ _⟩ f) x).congr_fun fun k ↦ ?_
  simpa only [Subtype.coe_mk, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
    (logExponentialDecayTwist_apply univ ⟨0, mem_univ _⟩ f
      (x + (k : ℝ) * Real.log γ)).symm

end Periodization

section Fourier

/-- Paper: (4.2.1.3), p. 162. The circle Fourier monomial is smooth and
belongs to the elementary Schwartz space. -/
theorem cyclicExponential_mem (m : ℤ) :
    (fun g : G ↦ fourier m (g.2.1 0)) ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  apply mem_elementarySchwartz_circle_of_contDiff
  have hcoe : ContDiff ℝ ∞ ((↑) : ℝ → ℂ) := Complex.ofRealCLM.contDiff
  simp only [fourier_coe_apply]
  fun_prop

/-- Paper: (4.2.1.3), p. 162. The exponential system consists of the usual
Fourier monomials in the normalized circle coordinate. -/
def cyclicExponential (m : ℤ) : S :=
  ⟨fun g ↦ fourier m (g.2.1 0), cyclicExponential_mem m⟩

/-- Paper: (4.2.1.3), p. 162. The monomial pulled back to the positive real
axis is the power with exponent (2πim / log γ).
Deviation: The argument x on the cover is the logarithm of the positive variable. -/
theorem cyclicExponential_apply (γ : ℝ) (hγ : 1 < γ) (m : ℤ) (x : ℝ) :
    cyclicExponential m (point ((x / Real.log γ : ℝ) : T)) =
      Complex.exp (phase[γ, m] * (x : ℂ)) := by
  change fourier m ((x / Real.log γ : ℝ) : T) = _
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp [ne_of_gt (Real.log_pos hγ)]

/-- Paper: (4.2.1.4), p. 162. The normalized circle Fourier coefficient is
linear and continuous for the smooth topology. -/
theorem cyclicFourierCoeff_spec (m : ℤ) :
    (∀ f g : S, fourierCoeff (fun z : T ↦ (f + g) (point z)) m =
      fourierCoeff (fun z : T ↦ f (point z)) m + fourierCoeff (fun z : T ↦ g (point z)) m) ∧
    (∀ (c : ℂ) (f : S), fourierCoeff (fun z : T ↦ (c • f) (point z)) m =
      c * fourierCoeff (fun z : T ↦ f (point z)) m) ∧
    Continuous (fun f : S ↦ fourierCoeff (fun z : T ↦ f (point z)) m) := by
  let ev (f : S) (z : T) := f (point z)
  have hc (f : S) : Continuous (ev f) := by
    apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples (1 : ℝ))).continuous_iff.mpr
    let s (x : ℝ) := ((0, x • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) :
      EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1))
    have hs : Continuous s := continuous_const.prodMk (continuous_id.smul continuous_const)
    have he (x : ℝ) : elementaryCover (s x) (0 : Fin 0 → ℤ) PUnit.unit = point (x : T) := by
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simp [elementaryCover, s, PiLp.smul_apply]
    simpa only [Function.comp_def, ev, he] using ((f.property.1 0 PUnit.unit).continuous.comp hs)
  have hInt (f : S) : Integrable (ev f) AddCircle.haarAddCircle :=
    (hc f).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hadd (f g : S) : fourierCoeff (ev (f + g)) m = fourierCoeff (ev f) m + fourierCoeff (ev g) m :=
    congrFun (fourierCoeff.add (hInt f) (hInt g)) m
  have hsmul (c : ℂ) (f : S) : fourierCoeff (ev (c • f)) m = c * fourierCoeff (ev f) m :=
    fourierCoeff.const_mul (ev f) c m
  let L : S →ₗ[ℂ] ℂ := { toFun f := fourierCoeff (ev f) m, map_add' := hadd, map_smul' := hsmul }
  let i : ElementarySchwartzIndex 0 1 0 := (0, 0, 0, 0)
  have hp : Continuous (fun f : S ↦ elementarySchwartzSeminorm i f) :=
    (withGeneratingSeminorms_spec _ _).continuous_seminorm i
  refine ⟨hadd, hsmul, (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L fun _ ↦
    Seminorm.continuous_of_le (q := (elementarySchwartzSeminorm i : Seminorm ℂ S)) hp ?_⟩
  intro f
  have hb (z : T) : ‖ev f z‖ ≤ elementarySchwartzSeminorm i f := by
    change (‖ev f z‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val i).toReal
    apply ENNReal.toReal_mono (f.property.2 i).ne
    rw [show i = (0, 0, 0, 0) from rfl, elementarySchwartzBound_zero]
    exact le_iSup (fun g ↦ (‖f g‖₊ : ENNReal)) (point z)
  have h := norm_integral_le_of_norm_le_const (μ := (AddCircle.haarAddCircle : Measure T))
    (f := fun z : T ↦ fourier (-m) z • ev f z)
    (ae_of_all _ fun z ↦ by simpa only [norm_smul, fourier_apply, Circle.norm_coe, one_mul] using hb z)
  change ‖fourierCoeff (ev f) m‖ ≤ elementarySchwartzSeminorm i f
  rw [fourierCoeff]
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h

/-- Paper: (4.2.1.4), p. 162. The coefficient uses Mathlib's Fourier integral
with probability Haar measure, which absorbs the factor (1 / log γ). -/
def cyclicFourierCoeff (m : ℤ) : StrongDual ℂ S where
  toFun f := fourierCoeff (fun z : T ↦ f (point z)) m
  map_add' := (cyclicFourierCoeff_spec m).1
  map_smul' := (cyclicFourierCoeff_spec m).2.1
  cont := (cyclicFourierCoeff_spec m).2.2

/-- Paper: Lemma 4.2.1.2, p. 162. A monomial has its own coefficient equal to
one and every other coefficient zero. -/
theorem cyclicFourierCoeff_exponential (m n : ℤ) :
    cyclicFourierCoeff m (cyclicExponential n) = if m = n then 1 else 0 := by
  change fourierCoeff (fourier n : C(T, ℂ)) m = _
  rw [fourierCoeff_fourier]
  by_cases h : m = n <;> simp [h]

local notation "Cover" => EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1)

/-- Pull a circle Schwartz function back to its real periodic lift. -/
private def cyclicLift (f : S) (x : ℝ) : ℂ := f (point (x : T))

private theorem cyclicCover_eq_point (xt : Cover) (a : Fin 0 → ℤ) (b : PUnit) :
    elementaryCover xt a b = point ((xt.2 0 : ℝ) : T) := by
  refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ (Subsingleton.elim _ _))
  funext j
  have : j = 0 := Subsingleton.elim _ _
  subst j
  rfl

private theorem cyclicLift_contDiff (f : S) : ContDiff ℝ ∞ (cyclicLift f) := by
  let s (x : ℝ) : Cover := (0, x • EuclideanSpace.single 0 1)
  have hs : ContDiff ℝ ∞ s := contDiff_const.prodMk (contDiff_id.smul contDiff_const)
  have he (x : ℝ) : elementaryCover (s x) 0 PUnit.unit = point (x : T) := by
    rw [cyclicCover_eq_point]
    simp [s, PiLp.smul_apply]
  unfold cyclicLift
  simpa only [Function.comp_def, he] using (f.property.1 0 PUnit.unit).comp hs

private theorem cyclicLift_periodic (f : S) : Periodic (cyclicLift f) 1 := by
  intro x
  simp [cyclicLift]

/-- The mixed partial in the one-circle case is the ordinary iterated derivative. -/
private theorem cyclicPartial_eq (f : S) (i : ElementarySchwartzIndex 0 1 0)
    (xt : Cover) (a : Fin 0 → ℤ) (b : PUnit) :
    elementaryPartial f.val i.2.1 i.2.2.1 xt a b =
      iteratedDeriv (i.2.2.1 0) (cyclicLift f) (xt.2 0) := by
  let L : Cover →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)
  let v : Cover := (0, EuclideanSpace.single 0 1)
  have hL : L v = 1 := by simp [L, v]
  let directions : List Cover := List.replicate (i.2.2.1 0) v
  have hdirs :
      (List.ofFn (fun j : Fin 0 ↦ List.replicate (i.2.1 j)
        ((EuclideanSpace.single j 1, 0) : Cover))).flatten ++
      (List.ofFn (fun j : Fin 1 ↦ List.replicate (i.2.2.1 j)
        ((0, EuclideanSpace.single j 1) : Cover))).flatten = directions := by
    simp [directions, v, List.ofFn_succ]
  dsimp only [elementaryPartial]
  rw [hdirs]
  simp only [cyclicCover_eq_point]
  change iteratedFDeriv ℝ directions.length (cyclicLift f ∘ L) xt directions.get = _
  rw [L.iteratedFDeriv_comp_right (cyclicLift_contDiff f) xt (by simp)]
  have hget : (fun j : Fin directions.length ↦ L (directions.get j)) = fun _ ↦ 1 := by
    funext j
    simp [directions, List.get_eq_getElem, hL]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, hget,
    ← iteratedDeriv_eq_iteratedFDeriv, show directions.length = i.2.2.1 0 by simp [directions]]
  rfl

/-- Bounding the derivative on a fundamental interval bounds the Schwartz seminorm. -/
private theorem cyclicSeminorm_le (f : S) (i : ElementarySchwartzIndex 0 1 0)
    {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ Ico (0 : ℝ) 1, ‖iteratedDeriv (i.2.2.1 0) (cyclicLift f) x‖ ≤ C) :
    elementarySchwartzSeminorm i f ≤ C := by
  change (elementarySchwartzBound f.val i).toReal ≤ C
  rw [← ENNReal.toReal_ofReal hC]
  apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  obtain ⟨x, hx, he⟩ := AddCircle.eq_coe_Ico ((xt.2 0 : ℝ) : T)
  let s : Cover := (0, x • EuclideanSpace.single 0 1)
  have hs : s.2 0 = x := by simp [s, PiLp.smul_apply]
  have hcover : elementaryCover s a b = elementaryCover xt a b := by
    rw [cyclicCover_eq_point, cyclicCover_eq_point, hs, he]
  have hD := elementaryPartial_descends f.val i.2.1 i.2.2.1 a b (f.property.1 a b)
  simp only [Fin.prod_univ_zero, one_mul, ENNReal.coe_nnreal_eq, coe_nnNorm]
  rw [← hD.2 s xt hcover, cyclicPartial_eq, hs]
  exact ENNReal.ofReal_le_ofReal (h x hx)

private theorem cyclicSeminorm_ge (f : S) (k : ℕ) (x : ℝ) :
    ‖iteratedDeriv k (cyclicLift f) x‖ ≤
      elementarySchwartzSeminorm (0, 0, fun _ ↦ k, 0) f := by
  let i : ElementarySchwartzIndex 0 1 0 := (0, 0, fun _ ↦ k, 0)
  let s : Cover := (0, x • EuclideanSpace.single 0 1)
  have hs : s.2 0 = x := by simp [s, PiLp.smul_apply]
  change (‖iteratedDeriv k (cyclicLift f) x‖₊ : ENNReal).toReal ≤
    (elementarySchwartzBound f.val i).toReal
  apply ENNReal.toReal_mono (f.property.2 i).ne
  refine le_iSup_of_le s (le_iSup_of_le 0 (le_iSup_of_le PUnit.unit ?_))
  simp only [Fin.prod_univ_zero, one_mul, cyclicPartial_eq f i s 0 PUnit.unit, hs, i, le_rfl]

private theorem cyclicFourierCoeff_eq_on (f : S) (m : ℤ) :
    cyclicFourierCoeff m f = fourierCoeffOn zero_lt_one (cyclicLift f) m := by
  change fourierCoeff (fun z : T ↦ f (point z)) m = _
  rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral]
  simp [cyclicLift]

/-- The net of finite Fourier sums converges in the circle Schwartz topology. -/
private theorem cyclicFourier_hasSum (f : S) :
    HasSum (fun m : ℤ ↦ cyclicFourierCoeff m f • cyclicExponential m) f := by
  let P (s : Finset ℤ) : S := ∑ m ∈ s, cyclicFourierCoeff m f • cyclicExponential m
  change Filter.Tendsto P Filter.atTop (𝓝 f)
  rw [elementarySchwartz_withSeminorms.tendsto_nhds]
  intro i ε hε
  have hP (s : Finset ℤ) : cyclicLift (P s) = fun t : ℝ ↦
      ∑ m ∈ s, fourierCoeffOn zero_lt_one (cyclicLift f) m * fourier m (t : T) := by
    funext t
    let ev : S →+ ℂ :=
      (Pi.evalAddMonoidHom (fun _ : G ↦ ℂ) (point (t : T))).comp
        (elementarySchwartzSubmodule 0 1 0 PUnit).subtype.toAddMonoidHom
    change ev (∑ m ∈ s, cyclicFourierCoeff m f • cyclicExponential m) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ ↦ ?_
    rw [← cyclicFourierCoeff_eq_on]
    rfl
  have h := smooth_fourier_series (cyclicLift_contDiff f) (cyclicLift_periodic f) (i.2.2.1 0)
  simp only [← hP, Metric.tendstoUniformlyOn_iff, dist_eq_norm] at h
  filter_upwards [h (ε / 2) (by positivity)] with s hs
  refine lt_of_le_of_lt (cyclicSeminorm_le (P s - f) i (C := ε / 2) (by positivity) fun x hx ↦ ?_)
    (by linarith)
  change ‖iteratedDeriv (i.2.2.1 0) (fun x ↦ cyclicLift (P s) x - cyclicLift f x) x‖ ≤ _
  rw [iteratedDeriv_fun_sub ((cyclicLift_contDiff (P s)).of_le (by simp)).contDiffAt
    ((cyclicLift_contDiff f).of_le (by simp)).contDiffAt]
  rw [norm_sub_rev]
  exact (hs x hx).le

private def cyclicFrequency (m : ℤ) : ℂ := 2 * Real.pi * Complex.I * m

private theorem fourierCoeffOn_iteratedDeriv_cyclic (f : S) (m : ℤ) (k : ℕ) :
    fourierCoeffOn zero_lt_one (iteratedDeriv k (cyclicLift f)) m =
      cyclicFrequency m ^ k * cyclicFourierCoeff m f := by
  have hdiff (j : ℕ) : ContDiff ℝ ∞ (iteratedDeriv j (cyclicLift f)) := by
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using cyclicLift_contDiff f
    | succ j ih =>
      rw [iteratedDeriv_succ]
      exact (contDiff_infty_iff_deriv.mp ih).2
  have hper (j : ℕ) : Periodic (iteratedDeriv j (cyclicLift f)) 1 := by
    induction j with
    | zero => simpa only [iteratedDeriv_zero] using cyclicLift_periodic f
    | succ j ih =>
      rw [iteratedDeriv_succ]
      intro x
      rw [← deriv_comp_add_const, show (fun y ↦ iteratedDeriv j (cyclicLift f) (y + 1)) =
        iteratedDeriv j (cyclicLift f) from funext ih]
  induction k with
  | zero => simp [cyclicFourierCoeff_eq_on]
  | succ k ih =>
    rw [iteratedDeriv_succ, fourierCoeffOn_deriv_one_periodic (hdiff k) (hper k), ih,
      pow_succ', cyclicFrequency]
    ring

private theorem norm_fourierCoeffOn_iteratedDeriv_cyclic (f : S) (m : ℤ) (k : ℕ) :
    ‖fourierCoeffOn zero_lt_one (iteratedDeriv k (cyclicLift f)) m‖ ≤
      elementarySchwartzSeminorm (0, 0, fun _ ↦ k, 0) f := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero, div_one, one_smul]
  have h x (_ : x ∈ uIoc (0 : ℝ) 1) :
      ‖fourier (-m) (x : T) • iteratedDeriv k (cyclicLift f) x‖ ≤
        elementarySchwartzSeminorm (0, 0, fun _ ↦ k, 0) f := by
    rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
    exact cyclicSeminorm_ge f k x
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const h

private theorem cyclicTerm_deriv (f : S) (m : ℤ) (k : ℕ) :
    iteratedDeriv k (cyclicLift (cyclicFourierCoeff m f • cyclicExponential m)) =
      fun x : ℝ ↦ (cyclicFrequency m ^ k * cyclicFourierCoeff m f) * fourier m (x : T) := by
  induction k with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
    rfl
  | succ k ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [((hasDerivAt_fourier 1 m x).const_mul
      (cyclicFrequency m ^ k * cyclicFourierCoeff m f)).deriv]
    simp only [Complex.ofReal_one, div_one, pow_succ', cyclicFrequency]
    ring

private def cyclicWeight (m : ℤ) : ℝ :=
  if m = 0 then 1 else ‖cyclicFrequency m‖⁻¹ ^ 2

private theorem cyclicWeight_nonneg (m : ℤ) : 0 ≤ cyclicWeight m := by
  unfold cyclicWeight
  split_ifs <;> positivity

private theorem cyclicWeight_summable : Summable cyclicWeight := by
  let a : ℂ := 2 * Real.pi * Complex.I
  have h := Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))
  refine (h.mul_left (‖a‖⁻¹ ^ 2)).of_norm_bounded_eventually ?_
  filter_upwards [Filter.eventually_cofinite_ne (0 : ℤ)] with m hm
  rw [cyclicWeight, ite_eq_right hm, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖a * (m : ℂ)‖⁻¹ ^ 2 ≤ ‖a‖⁻¹ ^ 2 * (1 / (m : ℝ) ^ 2)
  rw [norm_mul, mul_inv, mul_pow, Complex.norm_intCast]
  simp only [inv_pow, sq_abs, one_div, le_rfl]

/-- Two extra derivatives give an inverse-square bound for every nonzero Fourier mode. -/
private theorem cyclicTerm_seminorm_le (f : S) (i : ElementarySchwartzIndex 0 1 0) (m : ℤ) :
    elementarySchwartzSeminorm i (cyclicFourierCoeff m f • cyclicExponential m) ≤
      cyclicWeight m * (elementarySchwartzSeminorm (0, 0, 0, 0) f +
        elementarySchwartzSeminorm (0, 0, fun _ ↦ i.2.2.1 0 + 2, 0) f) := by
  let k := i.2.2.1 0
  have hp₀ : 0 ≤ elementarySchwartzSeminorm (0, 0, 0, 0) f := apply_nonneg _ _
  have hp₂ : 0 ≤ elementarySchwartzSeminorm (0, 0, fun _ ↦ k + 2, 0) f := apply_nonneg _ _
  refine cyclicSeminorm_le _ i (mul_nonneg (cyclicWeight_nonneg m) (add_nonneg hp₀ hp₂))
    fun x _ ↦ ?_
  rw [cyclicTerm_deriv, norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  change ‖cyclicFrequency m ^ k * cyclicFourierCoeff m f‖ ≤
    cyclicWeight m * (elementarySchwartzSeminorm (0, 0, 0, 0) f +
      elementarySchwartzSeminorm (0, 0, fun _ ↦ k + 2, 0) f)
  by_cases hm : m = 0
  · subst m
    have h := norm_fourierCoeffOn_iteratedDeriv_cyclic f 0 0
    rw [iteratedDeriv_zero, ← cyclicFourierCoeff_eq_on] at h
    rw [cyclicWeight, ite_eq_left rfl, one_mul]
    by_cases hk : k = 0
    · rw [hk, pow_zero, one_mul]
      exact h.trans (le_add_of_nonneg_right (apply_nonneg _ _))
    · simpa [cyclicFrequency, zero_pow hk] using add_nonneg hp₀ hp₂
  · rw [cyclicWeight, ite_eq_right hm]
    have h := norm_fourierCoeffOn_iteratedDeriv_cyclic f m (k + 2)
    rw [fourierCoeffOn_iteratedDeriv_cyclic, pow_add, mul_right_comm, norm_mul, norm_pow] at h
    have ha : 0 < ‖cyclicFrequency m‖ ^ 2 := by
      have hmc : (m : ℂ) ≠ 0 := by exact_mod_cast hm
      have ha' : cyclicFrequency m ≠ 0 := by simp [cyclicFrequency, Real.pi_ne_zero, hmc]
      exact pow_pos (norm_pos_iff.mpr ha') _
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀ ha]
    exact h.trans (le_add_of_nonneg_left hp₀)

/-- Dominate any continuous seminorm by finitely many of the defining seminorms. -/
private theorem cyclicFourier_isAbsolute :
    SchauderBasis.IsAbsolute (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) := by
  classical
  intro q hq
  let p (i : ElementarySchwartzIndex 0 1 0) : Seminorm ℂ S := elementarySchwartzSeminorm i
  have hp : WithSeminorms p := elementarySchwartz_withSeminorms
  obtain ⟨I, C, _, hdom⟩ := Seminorm.bound_sum_of_continuous hp q hq
  let r (i : ElementarySchwartzIndex 0 1 0) : Seminorm ℂ S :=
    p (0, 0, 0, 0) + p (0, 0, fun _ ↦ i.2.2.1 0 + 2, 0)
  let D : NNReal := ⟨∑' m : ℤ, cyclicWeight m, tsum_nonneg cyclicWeight_nonneg⟩
  have hsum (v : S) (g : ElementarySchwartzIndex 0 1 0 → Seminorm ℂ S) :
      (∑ i ∈ I, g i) v = ∑ i ∈ I, g i v := by
    change FunLike.coeAddMonoidHom (Seminorm ℂ S) S ℝ (∑ i ∈ I, g i) v = _
    rw [map_sum, Finset.sum_apply]
    rfl
  have hr (i) : Continuous (r i) :=
    (hp.continuous_seminorm _).add (hp.continuous_seminorm _)
  have hr' := Seminorm.continuous_finsetSum (s := I) (fun i _ ↦ hr i)
  refine ⟨(D * C) • ∑ i ∈ I, r i, hr'.const_smul (D * C), fun f ↦ ?_⟩
  let term (m : ℤ) := cyclicFourierCoeff m f • cyclicExponential m
  have hle (m : ℤ) : q (term m) ≤ cyclicWeight m * ((C : ℝ) * ∑ i ∈ I, r i f) := by
    calc
      _ ≤ (C : ℝ) * ∑ i ∈ I, p i (term m) := by
        simpa only [smul_apply, NNReal.smul_def, smul_eq_mul, hsum]
          using hdom (term m)
      _ ≤ (C : ℝ) * ∑ i ∈ I, cyclicWeight m * r i f :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum (fun i _ ↦ cyclicTerm_seminorm_le f i m)) C.coe_nonneg
      _ = _ := by rw [← Finset.mul_sum, mul_left_comm]
  have hmajor := cyclicWeight_summable.mul_right ((C : ℝ) * ∑ i ∈ I, r i f)
  have hqsum := hmajor.of_nonneg_of_le (fun m ↦ apply_nonneg q (term m)) hle
  have hbound := hqsum.tsum_le_tsum hle hmajor
  rw [tsum_mul_right] at hbound
  change Summable ((q ∘ term) ∘ freq) ∧
    (∑' n, (q ∘ term) (freq n)) ≤ ((D * C) • ∑ i ∈ I, r i) f
  refine ⟨(freq).summable_iff.mpr hqsum, ?_⟩
  rw [(freq).tsum_eq (q ∘ term), smul_apply, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_mul, hsum, mul_assoc]
  exact hbound

/-- Paper: Lemma 4.2.1.2(1), p. 162. The circle exponentials form an absolute
Schauder basis with the Fourier coefficient functionals.
Deviation: The Schauder basis predicates of §4.1 use the natural-number
enumeration of the integer frequencies. -/
theorem cyclicExponential_absoluteBasis :
    IsSchauderBasis (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) ∧
      SchauderBasis.IsAbsolute (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) := by
  refine ⟨⟨fun m n ↦ ?_, fun f ↦ ?_⟩, cyclicFourier_isAbsolute⟩
  · change cyclicFourierCoeff (freq m) (cyclicExponential (freq n)) = _
    simp [cyclicFourierCoeff_exponential]
  · exact ((freq).hasSum_iff.mpr (cyclicFourier_hasSum f)).mono_left
      (SummationFilter.conditional ℕ).le_atTop

/-- Paper: Lemma 4.2.1.2(2), p. 162. Fourier coefficients are an unconditional
Schauder basis of the strong dual, with coordinates given by evaluation on the monomials.
Deviation: Frequencies are enumerated by the natural numbers. -/
theorem cyclicFourierCoeff_unconditionalBasis :
    let ev := fun n : ℕ ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (cyclicExponential (freq n))
    IsSchauderBasis (cyclicFourierCoeff ∘ freq) ev ∧
      SchauderBasis.IsUnconditional (cyclicFourierCoeff ∘ freq) ev := by
  have hFrechet : IsFrechetTVS S := elementarySchwartz_isFrechet
  let : BarrelledSpace ℂ S := isFrechetTVS_barrelled hFrechet
  let : T2Space S := elementarySchwartz_t2
  obtain ⟨_, _, _, hComplete⟩ := hFrechet
  obtain ⟨e, he⟩ := elementarySchwartz_reflexive (m := 0) (n := 1) (r := 0) (F := PUnit)
  let eval : S →ₗ[ℂ] StrongDual ℂ (StrongDual ℂ S) :=
    ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ)
  have hReflexive : IsHomeomorph eval := by
    have heq : (eval : S → StrongDual ℂ (StrongDual ℂ S)) = e := by
      funext f
      exact DFunLike.ext _ _ fun L ↦ (he f L).symm
    rw [heq]
    exact e.isHomeomorph
  obtain ⟨hb, ha⟩ := cyclicExponential_absoluteBasis
  exact ⟨SchauderBasis.isShrinking_of_isAbsolute hComplete hReflexive hb ha,
    SchauderBasis.strongDual_isUnconditional_of_isAbsolute hComplete hReflexive hb ha⟩

/-- Paper: Lemma 4.2.1.2(3), p. 162. The quotient Fourier coefficient is the
normalized integral of the lift over the multiplicative fundamental interval. -/
theorem cyclicFourierCoeff_interval (γ : ℝ) (hγ : 1 < γ) (f : S) (m : ℤ) :
    cyclicFourierCoeff m f =
      (Real.log γ : ℂ)⁻¹ * ∫ t in (1 : ℝ)..γ,
        f (point ((Real.log t / Real.log γ : ℝ) : T)) *
          Complex.exp (-phase[γ, m] * (Real.log t : ℂ)) / (t : ℂ) := by
  let F (x : ℝ) : ℂ := fourier (-m) (x : T) * cyclicLift f x
  have hF : Continuous F :=
    ((fourier (-m)).continuous.comp (AddCircle.continuous_mk' 1)).mul
      (cyclicLift_contDiff f).continuous
  have hlog : Real.log γ ≠ 0 := (Real.log_pos hγ).ne'
  have ht : ∀ t ∈ uIcc (1 : ℝ) γ, t ≠ 0 := by
    rw [uIcc_of_le hγ.le]
    exact fun t ht ↦ (zero_lt_one.trans_le ht.1).ne'
  have hderiv : ∀ t ∈ uIcc (1 : ℝ) γ,
      HasDerivAt (fun x ↦ Real.log x / Real.log γ) (t⁻¹ / Real.log γ) t :=
    fun t h ↦ (Real.hasDerivAt_log (ht t h)).div_const _
  have hsub : (∫ t in (1 : ℝ)..γ, (t⁻¹ / Real.log γ) • F (Real.log t / Real.log γ)) =
      ∫ x in (0 : ℝ)..1, F x := by
    simpa only [Function.comp_apply, Real.log_one, zero_div, div_self hlog] using
      intervalIntegral.integral_deriv_smul_comp hderiv
        ((continuousOn_id.inv₀ ht).div_const (Real.log γ)) hF
  have hphase (t : ℝ) :
      fourier (-m) ((Real.log t / Real.log γ : ℝ) : T) =
        Complex.exp (-phase[γ, m] * (Real.log t : ℂ)) := by
    change cyclicExponential (-m) (point ((Real.log t / Real.log γ : ℝ) : T)) = _
    rw [cyclicExponential_apply γ hγ]
    simp only [Int.cast_neg, mul_neg, neg_div]
  change fourierCoeff (fun z : T ↦ f (point z)) m = _
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  simp only [div_one, one_smul, zero_add, smul_eq_mul]
  change (∫ x in (0 : ℝ)..1, F x) = _
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [F, cyclicLift, hphase, Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv]
  ring

-- TODO(paper-gap): The estimate (4.2.1.7) uses m^k for negative frequencies.
-- For f = e₋₁ and k = 1 the printed right-hand side is negative.

end Fourier

section QuotientDual

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [T2Space X] [PolynormableSpace ℂ X]

/-- Paper: Lemma 4.2.1.3, p. 163. Pullback along the quotient embeds the weak dual
and has image the continuous functionals vanishing on the closed subspace. -/
theorem quotientDual_weakEmbedding (M : Submodule ℂ X) (hM : IsClosed (M : Set X)) :
    let pull := fun l : WeakDual ℂ (X ⧸ M) ↦ StrongDual.toWeakDual (l.toStrongDual.comp M.mkQL)
    IsEmbedding pull ∧ range pull = {l | ∀ x ∈ M, l x = 0} := by
  dsimp only
  constructor
  · have he : IsEmbedding (fun l : WeakDual ℂ (X ⧸ M) ↦ (l : (X ⧸ M) → ℂ)) :=
      WeakBilin.isEmbedding (B := topDualPairing ℂ (X ⧸ M)) ContinuousLinearMap.coe_injective
    have hπ := M.mkQ_surjective.isEmbedding_comp (X := ℂ) M.mkQ
    apply Topology.IsEmbedding.of_comp (g := fun l : WeakDual ℂ X ↦ (l : X → ℂ))
      (WeakDual.continuous_of_continuous_eval fun x ↦ WeakDual.eval_continuous (M.mkQ x))
      WeakDual.coeFn_continuous
    exact hπ.comp he
  · ext l
    constructor
    · rintro ⟨v, rfl⟩ x hx
      change v (Submodule.Quotient.mk x) = 0
      rw [(Submodule.Quotient.mk_eq_zero M).mpr hx, map_zero]
    · intro h
      refine ⟨StrongDual.toWeakDual (M.liftQL l.toStrongDual (fun x hx ↦ h x hx)), ?_⟩
      exact DFunLike.ext _ _ fun _ ↦ rfl

/-- Paper: Lemma 4.2.1.3, p. 163. The image of the quotient adjoint in the
strong dual consists precisely of the functionals vanishing on the subspace. -/
theorem quotientDual_strongRange (M : Submodule ℂ X) (hM : IsClosed (M : Set X)) :
    range (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) =
      {l : StrongDual ℂ X | ∀ x ∈ M, l x = 0} := by
  exact (quotientDual_weakEmbedding M hM).2

/-- Paper: Lemma 4.2.1.3(1), p. 163. For a nuclear Fréchet space the quotient
adjoint also embeds the strong dual, with image the same annihilator. -/
theorem quotientDual_strongEmbedding_of_nuclear (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (hN : IsNuclearTVS X) (hF : IsFrechetTVS X) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by
  -- Lift the compact closure of each bounded set in the nuclear Fréchet quotient.
  have hlift : LiftsBoundedSets M.mkQL := by
    let : T0Space X := inferInstance
    let : IsClosed (M : Set X) := hM
    let : PolynormableSpace ℂ (X ⧸ M) := polynormableSpace_quotient M
    have hNQ := isNuclearTVS_quotient hN M
    obtain ⟨_, _, _, hcompleteQ⟩ := isFrechetTVS_quotient hF M hM
    obtain ⟨_, _, hmetr, hcomplete⟩ := hF
    let : MetrizableSpace X := hmetr
    let : UniformSpace X := IsTopologicalAddGroup.rightUniformSpace X
    let : CompleteSpace X := hcomplete
    let : (uniformity X).IsCountablyGenerated := Filter.comap.isCountablyGenerated _ _
    let := UniformSpace.metricSpace X
    let : UniformSpace (X ⧸ M) := IsTopologicalAddGroup.rightUniformSpace (X ⧸ M)
    let : IsUniformAddGroup (X ⧸ M) := isUniformAddGroup_of_addCommGroup
    let : CompleteSpace (X ⧸ M) := hcompleteQ
    intro B hB
    have htotal := (isPrecompactInCompletion_iff_totallyBounded B).mp
      (isPrecompactInCompletion_of_isNuclearTVS (X ⧸ M) hNQ hB)
    obtain ⟨A, hA, himage⟩ := exists_isCompact_image_eq_of_isOpenQuotientMap
      M.isOpenQuotientMap_mkQL (htotal.closure.isCompact_of_isClosed isClosed_closure)
    exact ⟨A, hA.isVonNBounded ℂ, himage.symm ▸ subset_closure⟩
  let pull : StrongDual ℂ (X ⧸ M) →L[ℂ] StrongDual ℂ X :=
    ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL
  have hind : IsUniformInducing pull := by
    constructor
    refine le_antisymm ?_ pull.uniformContinuous.le_comap
    have hX := (ContinuousLinearMap.hasBasis_nhds_zero
      (σ := RingHom.id ℂ) («E» := X) (F := ℂ)).uniformity_of_nhds_zero
    have hQ := (ContinuousLinearMap.hasBasis_nhds_zero
      (σ := RingHom.id ℂ) («E» := X ⧸ M) (F := ℂ)).uniformity_of_nhds_zero
    refine ((hX.comap (Prod.map pull pull)).le_basis_iff hQ).mpr ?_
    rintro ⟨B, U⟩ ⟨hB, hU⟩
    obtain ⟨A, hA, hcover⟩ := hlift B hB
    refine ⟨(A, U), ⟨hA, hU⟩, ?_⟩
    intro p hp
    change ∀ x ∈ A, (pull p.2 - pull p.1) x ∈ U at hp
    change ∀ y ∈ B, (p.2 - p.1) y ∈ U
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hcover hy
    exact hp x hx
  refine ⟨hind.isInducing, ?_⟩
  intro f g hfg
  ext y
  obtain ⟨x, rfl⟩ := M.mkQ_surjective y
  exact congrArg (fun l : StrongDual ℂ X ↦ l x) hfg

/-- Paper: Lemma 4.2.1.3(2), p. 164. For a Hilbert space the quotient adjoint
embeds the strong dual, with image the annihilator of the closed subspace. -/
theorem quotientDual_strongEmbedding_of_hilbert {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : Submodule ℂ H) (hM : IsClosed (M : Set H)) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by
  have : CompleteSpace M := hM.completeSpace_coe
  let s : (H ⧸ M) →L[ℂ] H :=
    Mᗮ.subtypeL.comp M.quotientEquivOrthogonal.toLinearIsometry.toContinuousLinearMap
  let r := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ s
  apply Topology.IsEmbedding.of_leftInverse (f := r) _ r.continuous
    (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL).continuous
  intro φ
  ext x
  change φ (M.mkQ ((M.quotientEquivOrthogonal x : Mᗮ) : H)) = φ x
  congr 1
  exact (M.quotientEquivOrthogonal_symm_eq_mk _ (M.quotientEquivOrthogonal x).property).symm.trans
    (M.quotientEquivOrthogonal.symm_apply_apply x)

/-- Paper: Remark 4.2.1.4, p. 164. In a totally reflexive Fréchet space, a
strong embedding of the quotient adjoint implies bounded lifting for the quotient. -/
theorem liftsBoundedSets_of_quotientDual_strongEmbedding (hF : IsFrechetTVS X)
    (hR : ∀ (N : Submodule ℂ X), IsClosed (N : Set X) →
      ∃ e : (X ⧸ N) ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (X ⧸ N)),
        ∀ x l, e x l = l x)
    (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (h : IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL)) :
    LiftsBoundedSets M.mkQL := by sorry

-- TODO(paper-gap): The classification in Remark 4.2.1.4 needs a hypothesis
-- about bounded lifting for all closed-subspace quotients of X.

end QuotientDual

section Kernel

variable (γ : ℝ) (hγ : 1 < γ)

/-- Paper: Lemma 4.2.1.5(2), p. 165. The periodization of exponential profiles
is continuous. Smoothness in part (1) is built into its elementary Schwartz target. -/
theorem cyclicPeriodization_continuous : Continuous (cyclicPeriodization γ hγ) := by
  let a : (univ : Set ℝ) := ⟨0, mem_univ _⟩
  have h : Continuous (fun f : E ↦ logExponentialDecayTwist univ a f) :=
    continuous_pi_iff.mp (positiveRealExponentialDecay_isEmbedding (univ : Set ℝ) univ_nonempty).continuous a
  exact (cyclicSchwartzPeriodization γ hγ).continuous.comp h

/-- Paper: Lemma 4.2.1.5(2), p. 165. Every smooth quotient function has an
exponentially decaying lift under periodization. -/
theorem cyclicPeriodization_surjective : Surjective (cyclicPeriodization γ hγ) := by sorry

/-- Paper: Lemma 4.2.1.5(2), p. 165. Periodization sends open sets to open sets. -/
theorem cyclicPeriodization_isOpenMap : IsOpenMap (cyclicPeriodization γ hγ) := by sorry

/-- Paper: Lemma 4.2.1.5(2), p. 165. Bundle the periodization and its continuity
as a continuous linear map. -/
def cyclicPeriodizationCLM : E →L[ℂ] S :=
  ⟨cyclicPeriodization γ hγ, cyclicPeriodization_continuous γ hγ⟩

/-- Paper: Lemma 4.2.1.5(2), p. 165. The bundled map gives the periodization
with the same value at every logarithmic lift. -/
theorem cyclicPeriodizationCLM_apply (f : E) (x : ℝ) :
    cyclicPeriodizationCLM γ hγ f (point ((x / Real.log γ : ℝ) : T)) =
      ∑' k : ℤ, f.val (x + (k : ℝ) * Real.log γ) := by sorry

local notation "Φ" => cyclicPeriodizationCLM γ hγ
local notation "Mγ" => LinearMap.ker (ContinuousLinearMap.toLinearMap Φ)
local notation "Q" => E ⧸ Mγ
local notation "desc" => Submodule.liftQL Mγ Φ le_rfl

/-- Paper: Lemma 4.2.1.5(3), p. 165. The kernel is the closed linear span of
the differences between a function and its translate by γ.
Deviation: The difference is expressed in logarithmic coordinates. -/
theorem cyclicPeriodization_ker :
    Mγ = (Submodule.span ℂ {g : E | ∃ f : E,
      ∀ x : ℝ, g.val x = f.val x - f.val (x + Real.log γ)}).topologicalClosure := by sorry

/-- Paper: Lemma 4.2.1.5(3), p. 165. The quotient functional is obtained from
the Fourier coefficient by undoing probability Haar normalization.
Its pullback is the Mellin evaluation at the negative Fourier frequency. -/
def cyclicQuotientMellinCoeff (m : ℤ) : StrongDual ℂ Q :=
  (Real.log γ : ℂ) • (cyclicFourierCoeff m).comp desc

/-- Paper: Lemma 4.2.1.5(3), p. 165. On representatives the quotient functional
is the Mellin integral with exponent −2πim/log γ. -/
theorem cyclicQuotientMellinCoeff_mk (m : ℤ) (f : E) :
    cyclicQuotientMellinCoeff γ hγ m (Submodule.mkQL Mγ f) =
      mellin (fun t ↦ f.val (Real.log t)) (-phase[γ, m]) := by sorry

-- TODO(paper-gap): In the continuity proof, (4.2.1.14) cannot hold for fixed T
-- and arbitrary ε. At t = T γⁿ the term k = -n alone equals T⁻ᴺ.
-- The difference quotient in (4.2.1.17) has the opposite derivative sign.

/-- Paper: Lemma 4.2.1.5(3), p. 165. The Mellin evaluations form an unconditional
Schauder basis on the strong quotient dual. Lemma 4.2.1.3 identifies this dual
with the annihilator with its inherited strong topology. -/
theorem cyclicQuotientMellinCoeff_unconditionalBasis :
    let δ := cyclicQuotientMellinCoeff γ hγ ∘ freq
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ Q),
      IsSchauderBasis δ c ∧ SchauderBasis.IsUnconditional δ c := by sorry

/-- Paper: Remark 4.2.1.6, p. 165. Every bounded subset of a Hausdorff
quotient of the exponential decay space has a bounded lift. -/
theorem positiveRealExponentialDecay_liftsBoundedSets (M : Submodule ℂ E)
    (hM : IsClosed (M : Set E)) : LiftsBoundedSets M.mkQL := by sorry

end Kernel

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient basis of the
strong dual is absolute, with coordinates given by evaluation on the monomials. -/
theorem cyclicFourierCoeff_absolute :
    SchauderBasis.IsAbsolute (cyclicFourierCoeff ∘ freq)
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (cyclicExponential (freq n))) := by sorry

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient functionals
are bounded in the strong dual. -/
theorem cyclicFourierCoeff_bounded :
    IsVonNBounded ℂ (range cyclicFourierCoeff) := by sorry

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient functionals are
equicontinuous as maps on the circle Schwartz space. -/
theorem cyclicFourierCoeff_equicontinuous :
    Equicontinuous (fun m : ℤ ↦ (cyclicFourierCoeff m : S → ℂ)) := by sorry

-- TODO(paper-gap): The proof on p. 169 gives the positive Mellin frequency
-- and drops the Haar normalization factor. Formula (4.2.1.5) fixes both.

/-- Paper: Remark 4.2.1.8, p. 170. Periodization identifies the exponential-decay
quotient with the smooth circle Schwartz space.
Deviation: The source is the quotient by the kernel of the periodization. -/
theorem cyclicPeriodization_quotient_equiv (γ : ℝ) (hγ : 1 < γ) :
    let P := cyclicPeriodizationCLM γ hγ
    ∃ e : (E ⧸ P.ker) ≃L[ℂ] S, ∀ f : E, e (P.ker.mkQL f) = P f := by sorry

/-- Paper: Remark 4.2.1.8, p. 170. The exponential system is regular in
the smooth topology. -/
theorem cyclicExponential_regular :
    SchauderBasis.IsRegular (cyclicExponential ∘ freq) := by sorry

/-- Paper: Remark 4.2.1.8, p. 170. The exponential system is unbounded
in the smooth topology. -/
theorem cyclicExponential_not_bounded :
    ¬ IsVonNBounded ℂ (range cyclicExponential) := by sorry

section CompactSupport

local notation "D[" K "]" => 𝓓_{K}(ℝ, ℂ)
local notation "symmInterval[" a ", " b "]" =>
  Compacts.mk (Icc (Real.log b - Real.log a) (Real.log b + Real.log a)) isCompact_Icc

/-- Paper: §4.2.2, p. 170. A smooth logarithmic profile supported in a fixed
compact set satisfies all exponential Schwartz weights. -/
theorem compactLogProfile_mem (K : Compacts ℝ) (f : D[K]) :
    (f : ℝ → ℂ) ∈ logExponentialDecaySubmodule univ := by
  exact mem_logExponentialDecaySubmodule_of_hasCompactSupport univ f.hasCompactSupport f.contDiff

/-- Paper: §4.2.2, p. 170. Including profiles supported in a fixed compact set
into the exponential decay space is continuous for the uniform derivative topology. -/
theorem compactLogProfile_continuous (K : Compacts ℝ) :
    Continuous (Y := E) (fun f : D[K] ↦ ⟨(f : ℝ → ℂ), compactLogProfile_mem K f⟩) := by
  exact (supportedToLogDecayCLM univ univ_nonempty K).continuous

/-- Paper: §4.2.2, p. 170. The inclusion of the fixed-support test space
takes the same function as an exponentially decaying profile.
Deviation: The support set is the logarithmic image of the paper's K. -/
def compactLogProfileInclusion (K : Compacts ℝ) : D[K] →L[ℂ] E where
  toFun f := ⟨(f : ℝ → ℂ), compactLogProfile_mem K f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := compactLogProfile_continuous K

/-- Forgetting the exponential weights is the continuous projection to the zero twist. -/
private def unweightedLogProfile : E →L[ℂ] 𝓢(ℝ, ℂ) :=
  let a : (univ : Set ℝ) := ⟨0, mem_univ _⟩
  ⟨logExponentialDecayTwist univ a, (continuous_apply a).comp
    (positiveRealExponentialDecay_isEmbedding univ univ_nonempty).continuous⟩

private theorem unweightedLogProfile_apply (f : E) (x : ℝ) : unweightedLogProfile f x = f.val x := by
  let a : (univ : Set ℝ) := ⟨0, mem_univ _⟩
  change logExponentialDecayTwist univ a (show logExponentialDecaySubmodule univ from f) x = _
  rw [logExponentialDecayTwist_apply]
  simp [a]

/-- Paper: §4.2.2, p. 170. A decay profile lies in the image of the test
space precisely when its topological support is contained in the designated compact set. -/
theorem compactLogProfileInclusion_range (K : Compacts ℝ) (f : E) :
    f ∈ range (compactLogProfileInclusion K) ↔ tsupport f.val ⊆ (K : Set ℝ) := by
  constructor
  · rintro ⟨g, rfl⟩
    exact g.tsupport_subset
  · intro h
    have hs : ContDiff ℝ ∞ f.val := by
      simpa only [show (unweightedLogProfile f : ℝ → ℂ) = f.val from funext (unweightedLogProfile_apply f)] using
        (unweightedLogProfile f).smooth (⊤ : ℕ∞)
    exact ⟨⟨f.val, hs, support_subset_iff'.mp ((subset_tsupport _).trans h)⟩, rfl⟩

/-- Paper: Theorem 4.2.2.1, p. 170. An entire function is a Fourier integral
of an L² function supported on the indicated interval exactly when it has
the stated exponential type and an L² trace on the real line. -/
theorem paleyWiener_compactInterval (A : ℝ) (hA : 0 < A) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) :
    (∃ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Ioo (-A) A)) ∧
      ∀ z, f z = ∫ x in Ioo (-A) A, F x * Complex.exp (Complex.I * (x : ℂ) * z)) ↔
    ((∃ C : ℝ, 0 < C ∧ ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      MemLp (fun x : ℝ ↦ f x) 2 volume) := by sorry

-- TODO(paper-gap): The multiplicative restatement following 4.2.2.1
-- uses A directly as an interval endpoint. The endpoint for type A is exp A.

variable (γ : ℝ) (hγ : 1 < γ)

local notation "Φ[" K "]" =>
  ContinuousLinearMap.comp (cyclicPeriodizationCLM γ hγ) (compactLogProfileInclusion K)

-- TODO(paper-gap): Proposition 4.2.2.2(1) asserts surjectivity for all compact K
-- mapping onto the quotient. For K = [1, γ], the class of 1 has only endpoint
-- representatives in K, where every smooth test function supported in K vanishes.

include hγ in
/-- Paper: Proposition 4.2.2.2(1), p. 171. The closed multiplicative interval
of radius a about b covers the quotient when its logarithmic length exceeds log γ.
Deviation: The interval and quotient map are in logarithmic coordinates. -/
theorem cyclicQuotient_surjOn_interval (a b : ℝ) (ha : 1 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    SurjOn (fun x : ℝ ↦ ((x / Real.log γ : ℝ) : T))
      (symmInterval[a, b] : Set ℝ) univ := by
  intro z _
  let L := Real.log γ
  let A := Real.log (b / a)
  have hL : 0 < L := Real.log_pos hγ
  have hA : A = Real.log b - Real.log a := Real.log_div hb.ne' (lt_trans zero_lt_one ha).ne'
  let r := (AddCircle.equivIco (1 : ℝ) (A / L)) z
  have hr : (r : ℝ) ∈ Ico (A / L) (A / L + 1) := r.property
  refine ⟨(r : ℝ) * L, ⟨?_, ?_⟩, ?_⟩
  · rw [← hA]
    exact (div_le_iff₀ hL).mp hr.1
  · have hu := mul_lt_mul_of_pos_right hr.2 hL
    rw [add_mul, div_mul_cancel₀ _ hL.ne', one_mul] at hu
    change _ ≤ Real.log b + Real.log a
    dsimp only [L] at hu
    linarith [hA]
  · change ((↑((r : ℝ) * L / L) : T)) = z
    rw [mul_div_cancel_right₀ _ hL.ne']
    exact AddCircle.coe_equivIco

/-- Paper: Proposition 4.2.2.2(1), p. 171. Periodization gives a continuous
linear isomorphism from the fixed-support interval quotient to the smooth circle space.
Deviation: This states the strict-width interval case treated on p. 172. -/
theorem compactIntervalPeriodization_quotient_equiv (a b : ℝ) (ha : 1 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    ∃ e : (D[K] ⧸ P.ker) ≃L[ℂ] S, ∀ f : D[K], e (P.ker.mkQL f) = P f := by sorry

-- TODO(paper-gap): Proposition 4.2.2.2(2) with a = γ, b = 1, and A₀ = γ
-- forces ψ to be supported in {1}. For a nonzero smooth bump u supported
-- in (1, γ), the function x ↦ u(x) - u(γx) is nonzero and in the stated kernel.

include hγ in
/-- Paper: Remark 4.2.2.3, p. 171. A compact set containing a slightly
enlarged translated fundamental interval covers the quotient. -/
theorem cyclicQuotient_surjOn_of_contains (K : Compacts ℝ) (n : ℤ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hK : Icc (n * Real.log γ + Real.log (1 - ε))
      (n * Real.log γ + Real.log (γ + ε)) ⊆ (K : Set ℝ)) :
    SurjOn (fun x : ℝ ↦ ((x / Real.log γ : ℝ) : T)) (K : Set ℝ) univ := by
  intro z _
  let L := Real.log γ
  have hL : 0 < L := Real.log_pos hγ
  let r := (AddCircle.equivIco (1 : ℝ) (n : ℝ)) z
  have hr : (r : ℝ) ∈ Ico (n : ℝ) ((n : ℝ) + 1) := r.property
  refine ⟨(r : ℝ) * L, hK ⟨?_, ?_⟩, ?_⟩
  · have hlog := Real.log_nonpos (by linarith : 0 ≤ 1 - ε) (by linarith : 1 - ε ≤ 1)
    exact (add_le_of_nonpos_right hlog).trans (mul_le_mul_of_nonneg_right hr.1 hL.le)
  · have hlog : L ≤ Real.log (γ + ε) :=
      Real.log_le_log (by linarith) (by linarith)
    have hu := mul_le_mul_of_nonneg_right hr.2.le hL.le
    rw [add_mul, one_mul] at hu
    exact hu.trans (add_le_add (le_refl _) hlog)
  · change (↑((r : ℝ) * L / L) : T) = z
    rw [mul_div_cancel_right₀ _ hL.ne']
    exact AddCircle.coe_equivIco

/-- Paper: Lemma 4.2.2.4, p. 171. The test space with support in a given
compact set is a closed subspace of the exponential decay space. -/
theorem compactLogProfileInclusion_closed (K : Compacts ℝ)
    (hK : (interior (K : Set ℝ)).Nonempty) :
    IsClosed (range (compactLogProfileInclusion K)) := by
  clear hK
  have he : range (compactLogProfileInclusion K) = ⋂ x : ↥((K : Set ℝ)ᶜ), {f : E | f.val x = 0} := by
    ext f
    rw [compactLogProfileInclusion_range, mem_iInter]
    constructor
    · intro h x
      exact support_subset_iff'.mp ((subset_tsupport _).trans h) x x.property
    · intro h
      exact closure_minimal (support_subset_iff'.mpr fun x hx ↦ h ⟨x, hx⟩) K.isCompact.isClosed
  rw [he]
  apply isClosed_iInter
  intro x
  have hc : Continuous (fun f : E ↦ f.val x) := by
    simpa only [Function.comp_def, SchwartzMap.toBoundedContinuousFunctionCLM_apply, unweightedLogProfile_apply] using
      ((continuous_eval_const (F := BoundedContinuousFunction ℝ ℂ) (x : ℝ)).comp
        ((SchwartzMap.toBoundedContinuousFunctionCLM ℂ ℝ ℂ).continuous.comp unweightedLogProfile.continuous))
  exact isClosed_eq hc continuous_const

/-- Paper: Lemma 4.2.2.4, p. 171. The test space's uniform derivative topology
agrees with the topology inherited from the exponential decay space. -/
theorem compactLogProfileInclusion_isEmbedding (K : Compacts ℝ)
    (hK : (interior (K : Set ℝ)).Nonempty) :
    IsEmbedding (compactLogProfileInclusion K) := by
  clear hK
  let P := compactLogProfileInclusion K
  have hi : Injective P := by
    intro f g he
    exact ContDiffMapSupportedIn.ext fun x ↦ congrArg (fun F : E ↦ F.val x) he
  let e := LinearEquiv.ofInjective P.toLinearMap hi
  let U := unweightedLogProfile.comp P.range.subtypeL
  have hfun (f : P.range) : (e.symm f : ℝ → ℂ) = (U f : ℝ → ℂ) := by
    obtain ⟨g, rfl⟩ := e.surjective f
    rw [e.symm_apply_apply]
    exact funext fun x ↦ (unweightedLogProfile_apply (P g) x).symm
  have hc : Continuous e.symm := by
    apply (ContDiffMapSupportedIn.withSeminorms ℂ ℝ ℂ ⊤ K).continuous_of_continuous_comp e.symm.toLinearMap
    intro n
    let q := (SchwartzMap.seminorm ℂ 0 n).comp U.toLinearMap
    apply Seminorm.continuous_of_le (q := q) (((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (0,n)).comp U.continuous)
    intro f
    apply (ContDiffMapSupportedIn.seminorm_top_le_iff ℂ (apply_nonneg q f) n (e.symm f)).2
    intro x _
    rw [hfun]
    exact (U f).norm_iteratedFDeriv_le_seminorm ℂ n x
  let H : D[K] ≃L[ℂ] P.range :=
    { e with continuous_toFun := P.rangeRestrict.continuous, continuous_invFun := hc }
  exact IsEmbedding.subtypeVal.comp H.toHomeomorph.isEmbedding

/-- Paper: Proposition 4.2.2.5(1), p. 173. The Mellin evaluation sequence
is an absolute Schauder basis of the strong quotient dual. This dual is
identified with the annihilator by Lemma 4.2.1.3. -/
theorem cyclicQuotientMellinCoeff_absoluteBasis :
    let δ := cyclicQuotientMellinCoeff γ hγ ∘ freq
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ (cyclicPeriodizationCLM γ hγ).ker)),
      IsSchauderBasis δ c ∧ SchauderBasis.IsAbsolute δ c := by sorry

/-- Paper: Proposition 4.2.2.5(2), p. 173. For an interval wider than a
fundamental interval, all monomials have lifts supported in that same interval,
whose classes are an absolute Schauder basis for the fixed-support quotient. -/
theorem compactIntervalPeriodization_absoluteBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    ∃ u : ℤ → D[K], (∀ m, P (u m) = cyclicExponential m) ∧
      let basis := P.ker.mkQL ∘ u ∘ freq
      let coeff := fun n ↦ (cyclicFourierCoeff (freq n)).comp (P.ker.liftQL P le_rfl)
      IsSchauderBasis basis coeff ∧ SchauderBasis.IsAbsolute basis coeff := by sorry

/-- Paper: Proposition 4.2.2.5(2), p. 173. Descending the restricted Mellin
evaluations gives an absolute Schauder basis of the strong fixed-support quotient dual. -/
theorem compactIntervalPeriodization_dual_absoluteBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    let δ := fun n ↦ (Real.log γ : ℂ) •
      (cyclicFourierCoeff (freq n)).comp (P.ker.liftQL P le_rfl)
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (D[K] ⧸ P.ker)),
      IsSchauderBasis δ c ∧ SchauderBasis.IsAbsolute δ c := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. Periodization on ordinary Schwartz
profiles has a continuous linear right inverse. -/
theorem cyclicSchwartzPeriodization_hasSection :
    ∃ s : S →L[ℂ] 𝓢(ℝ, ℂ), Function.RightInverse s (cyclicSchwartzPeriodization γ hγ) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. Periodization on exponential Schwartz
profiles has a continuous linear right inverse. -/
theorem cyclicPeriodization_hasSection :
    ∃ s : S →L[ℂ] E, Function.RightInverse s (cyclicPeriodizationCLM γ hγ) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. The circle Schwartz space is topologically
and linearly isomorphic to the space of rapidly decreasing integer sequences. -/
theorem cyclicSchwartz_equiv_rapidDecay :
    Nonempty (S ≃L[ℂ] RapidDecaySequence 1) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. The real Schwartz space is topologically
and linearly isomorphic to the space of rapidly decreasing sequences. -/
theorem realSchwartz_equiv_rapidDecay :
    Nonempty (𝓢(ℝ, ℂ) ≃L[ℂ] RapidDecaySequence 1) := by sorry

/-- Paper: Remark 4.2.2.6, p. 174. The kernel of periodization of ordinary
Schwartz functions is topologically and linearly isomorphic to the source. -/
theorem cyclicSchwartzPeriodization_ker_equiv :
    Nonempty ((cyclicSchwartzPeriodization γ hγ).ker ≃L[ℂ] 𝓢(ℝ, ℂ)) := by sorry

/-- Paper: Remark 4.2.2.6, p. 174. The product of two rapid-decay sequence
spaces is topologically and linearly isomorphic to one such space. -/
theorem rapidDecaySequence_prod_equiv :
    Nonempty ((RapidDecaySequence 1 × RapidDecaySequence 1) ≃L[ℂ] RapidDecaySequence 1) := by sorry

end CompactSupport

end RiemannMasullo
