module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWUnweightedLogTerm
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWSincLogConstant
import Mathlib.Topology.Algebra.IsOpenUnits
import RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# The sharp orbital masses of the rationals with no finite place

For `F = ℚ` and the empty set of finite places, the S-adeles are the real line, the S-ideles are
the nonzero reals and the S-units are `±1`. This file computes the sharp orbital masses of §12.4
(`sLocalTraceSharpMass`, p. 518) in that case. Their sum is the trace of an operator on the real
line, the real-place model of `Sec4_RealPWTestTrace`.

In the real coordinate `ratRealCoordEquiv` the additive Tamagawa measure is Lebesgue measure
(`ratIntegral_add`) and the multiplicative one is `dt / |t|` (`ratIntegral_mul`). The standard
character is `exp (2π i t)` (`ratSAdeleStandardCharacter`), and the positive reals form a
fundamental domain for the units (`isFundamentalDomain_ratPos`).

On the skew diagonal the cutoff kernel of Step II (p. 517) is an integral of the lift of the test
against a sinc kernel (`ratCutoffKernel_diag`). Put into `sLocalTraceSharpMass_eq_integral`, this
writes each sharp mass as a double integral on the line (`ratSharpMass_eq`). Folding the two units
and the two signs of the variable onto the positive half-line gives `tsum_ratSharpMass`. The sum
of the sharp masses at radius `L Y` is `∫ ψ(h) T(h) dh`, where `ψ` is the folded test `ratFold`
and `T(h)` is the trace of the sharp cutoff to `[-L, L]` of the dilation by `h⁻¹` on the even
Paley–Wiener band of width `Y` (`realPWSharpTrace`).

By `exists_ratCutoff_nuclear` the sharp cutoff of the action of `ψ` on that band is nuclear, and
its trace is exactly the sum of the sharp masses. So the comparison asked for in
`sLocalTrace_asymptotic_of_sharp_comparison` holds with difference zero for this operator, and
`ratCutoff_trace_asymptotic` is Theorem 12.4.1.1 for it. The limit of the real-place model
(`tendsto_integral_realPWSharpTrace_sub_log`) then fixes the constants of
`sLocalTraceSharpMass_asymptotic` (`ratPrincipalValue_eq`). When `φ(1) ≠ 0` the norm-one volume
is one, and the volume times the real principal value is `φ(1) (log 2π + γ) + ∫ (ψ - φ(1) m) ρ`,
with `m = logTermProfile` and `ρ = realTermDensity`.

The operator here uses sharp cutoffs in both variables and acts on the band of the line. The
operator of Theorem 12.4.1.1 in the paper is a smoothed kernel on the S-idele class group, and
this file does not compare the two.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set NumberField IsDedekindDomain
open scoped Topology NumberField Real ENNReal

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instMeasurableSpaceInfiniteAdeleRing_riemannMasullo

local notation "Sq" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "Aq" => SAdeleRing ℚ Sq
local notation "Iq" => (SAdeleRing ℚ Sq)ˣ
local notation "Hq" => sProjectedDiagonal ℚ Sq
local notation "νq" => sAdditiveTamagawaMeasure ℚ Sq
local notation "μq" => sMultiplicativeTamagawaMeasure ℚ Sq
local notation "normq(" x ")" => (((sIdeleNorm ℚ Sq x).val : ℝ))
local notation "modq(" x ")" => ((∏ w : InfinitePlace ℚ, ‖(x : Aq).1 w‖ ^ w.mult) *
  ∏ v : Sq, ‖(x : Aq).2 v‖)

local instance (w : InfinitePlace ℚ) : MeasurableSpace w.Completion := borel _
local instance (w : InfinitePlace ℚ) : BorelSpace w.Completion := ⟨rfl⟩
local instance (v : HeightOneSpectrum (𝓞 ℚ)) : MeasurableSpace (v.adicCompletion ℚ) := borel _
local instance (w : InfinitePlace ℚ) : SigmaFinite (infiniteLocalAdditiveTamagawaMeasure ℚ w) := by
  have hw : w.IsReal := Subsingleton.elim Rat.infinitePlace w ▸ Rat.isReal_infinitePlace
  rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left hw]
  exact (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.toHomeomorph.toMeasurableEquiv.sigmaFinite_map

local instance instRatSIdeleT2 : T2Space Iq := (sIdeleGroup_description ℚ Sq).2.1
local instance instRatSAdeleT2 : T2Space Aq := inferInstanceAs (T2Space
  (((w : InfinitePlace ℚ) → w.Completion) × ((v : Sq) → v.val.adicCompletion ℚ)))

section Dictionary

/-- The real coordinate of an S-adele of `ℚ` with no finite place. -/
def ratRealCoordEquiv : Aq ≃+* ℝ :=
  (RingEquiv.prodZeroRing (InfiniteAdeleRing ℚ) _).symm.trans
    ((RingEquiv.piUnique (fun w : InfinitePlace ℚ ↦ w.Completion)).trans
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace))

theorem ratRealCoordEquiv_apply (a : Aq) : ratRealCoordEquiv a =
    InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
      (a.1 Rat.infinitePlace) := rfl

/-- The standard character of the S-adeles of `ℚ` with no finite place is `exp (2π i t)` in the
real coordinate. -/
theorem ratSAdeleStandardCharacter (a : Aq) : (sAdeleStandardCharacter ℚ Sq a : ℂ) =
    Circle.exp (2 * Real.pi * ratRealCoordEquiv a) := by
  rw [sAdeleStandardCharacter]
  simp only [Finset.univ_unique, Finset.prod_singleton, Finset.univ_eq_empty, Finset.prod_empty,
    mul_one]
  rw [adeleStandardCharacter_rat, ratAdeleStandardCharacter_real _ rfl]
  change _ = (Circle.exp (2 * Real.pi * InfinitePlace.Completion.extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace (a.1 Rat.infinitePlace)) : ℂ)
  congr 4
  have h : (default : InfinitePlace ℚ) = Rat.infinitePlace := Subsingleton.elim _ _
  rw [h]
  simp

/-- The real coordinate is measurable. -/
theorem measurable_ratRealCoordEquiv : Measurable (ratRealCoordEquiv : Aq → ℝ) := by
  have h1 : Measurable (fun a : Aq ↦ a.1 Rat.infinitePlace) :=
    (measurable_pi_apply _).comp measurable_fst
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace).continuous.measurable.comp h1

/-- The inverse of the real coordinate is measurable. -/
theorem measurable_ratRealCoordEquiv_symm : Measurable (ratRealCoordEquiv.symm : ℝ → Aq) := by
  have hr : Measurable (InfinitePlace.Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace).symm :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal
      Rat.isReal_infinitePlace).symm.continuous.measurable
  have hu : Measurable ((RingEquiv.piUnique (fun w : InfinitePlace ℚ ↦ w.Completion)).symm) :=
    (MeasurableEquiv.piUnique (fun w : InfinitePlace ℚ ↦ w.Completion)).symm.measurable
  exact (hu.comp hr).prodMk measurable_const

/-- The real coordinate as a measurable equivalence. -/
def ratRealMeasurableEquiv : Aq ≃ᵐ ℝ where
  toEquiv := ratRealCoordEquiv.toEquiv
  measurable_toFun := measurable_ratRealCoordEquiv
  measurable_invFun := measurable_ratRealCoordEquiv_symm

/-- The additive Tamagawa measure of `ℚ` with no finite place is Lebesgue measure in the real
coordinate. -/
theorem measurePreserving_ratRealCoord :
    MeasurePreserving ratRealMeasurableEquiv (sAdditiveTamagawaMeasure ℚ Sq) volume := by
  refine ⟨ratRealMeasurableEquiv.measurable, ?_⟩
  rw [sAdditiveTamagawaMeasure,
    Measure.pi_of_empty (fun v : Sq ↦ finiteLocalAdditiveTamagawaMeasure ℚ v.val) isEmptyElim,
    Measure.prod_dirac]
  have hm : Measurable (fun x : InfiniteAdeleRing ℚ ↦
      ((x, fun a => isEmptyElim a) : Aq)) := measurable_prodMk_right
  erw [Measure.map_map ratRealMeasurableEquiv.measurable hm]
  have hcomp : (ratRealMeasurableEquiv ∘ fun x : InfiniteAdeleRing ℚ ↦ (x, isEmptyElim)) =
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) ∘
        (MeasurableEquiv.piUnique (fun w : InfinitePlace ℚ ↦ w.Completion)) := rfl
  have hr : Measurable (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) :=
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      Rat.isReal_infinitePlace).continuous.measurable
  have hrs : Measurable (InfinitePlace.Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace).symm :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal
      Rat.isReal_infinitePlace).symm.continuous.measurable
  rw [hcomp, ← Measure.map_map hr (MeasurableEquiv.piUnique _).measurable,
    (measurePreserving_piUnique
      (fun w : InfinitePlace ℚ ↦ infiniteLocalAdditiveTamagawaMeasure ℚ w)).map_eq]
  change Measure.map _ (infiniteLocalAdditiveTamagawaMeasure ℚ Rat.infinitePlace) = volume
  rw [infiniteLocalAdditiveTamagawaMeasure, dite_eq_left Rat.isReal_infinitePlace,
    Measure.map_map hr hrs]
  have : ((InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace) ∘
      (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm) = id := by
    funext t; simp
  rw [this, Measure.map_id]

local notation "eq" => ratRealCoordEquiv

/-- The product norm of an S-adele of `ℚ` with no finite place is the absolute value of its
real coordinate. -/
theorem ratModq (y : Aq) : modq(y) = |eq y| := by
  rw [Fintype.prod_unique, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  have hm : (default : InfinitePlace ℚ).mult = 1 := by
    rw [show (default : InfinitePlace ℚ) = Rat.infinitePlace from rfl]
    simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
  rw [hm, pow_one, ratRealCoordEquiv_apply, ← Real.norm_eq_abs,
    (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _)]
  rfl

/-- The S-idele norm is the absolute value of the real coordinate. -/
theorem ratNormq (g : Iq) : normq(g) = |eq g.val| := by
  rw [← ratModq]
  simp [sIdeleNorm]

/-- An S-adele is a unit exactly when its real coordinate is nonzero. -/
theorem ratMem_range_units (y : Aq) : y ∈ range (Units.val : Iq → Aq) ↔ eq y ≠ 0 := by
  rw [← isUnit_iff_ne_zero, ← MulEquiv.isUnit_map (ratRealCoordEquiv.toMulEquiv).symm]
  constructor
  · rintro ⟨u, rfl⟩
    simp
  · intro h
    have h' : IsUnit y := by simp at h; exact h
    exact ⟨h'.unit, rfl⟩

/-- The product region of radius `R` is the interval `|t| ≤ R` in the real coordinate. -/
theorem ratMem_band (y : Aq) (R : ℝ) : y ∈ sLocalPWProductRegion (F := ℚ) Sq R ↔ |eq y| ≤ R := by
  rw [← ratModq y]
  rfl

end Dictionary

section Integrals

local notation "eq" => ratRealCoordEquiv

/-- The S-idele of `ℚ` with no finite place whose real coordinate is `t`, and `1` at `t = 0`. -/
def ratUnit (t : ℝ) : Iq :=
  if h : t = 0 then 1 else Units.map (ratRealCoordEquiv.symm : ℝ →* Aq) (Units.mk0 t h)

theorem ratUnit_val {t : ℝ} (ht : t ≠ 0) : (ratUnit t).val = ratRealCoordEquiv.symm t := by
  simp [ratUnit, ht]

theorem eq_ratUnit {t : ℝ} (ht : t ≠ 0) : eq (ratUnit t).val = t := by
  rw [ratUnit_val ht, RingEquiv.apply_symm_apply]

theorem ratUnit_eq (g : Iq) : ratUnit (eq g.val) = g := by
  have h0 : eq g.val ≠ 0 := (ratMem_range_units g.val).1 ⟨g, rfl⟩
  apply Units.ext
  rw [ratUnit_val h0, RingEquiv.symm_apply_apply]

/-- A function on the S-ideles read on the real line, extended by zero at the origin. -/
def ratLift (G : Iq → ℂ) (t : ℝ) : ℂ :=
  Function.extend (Units.val : Iq → Aq) G 0 (ratRealCoordEquiv.symm t)

theorem ratLift_of_ne {G : Iq → ℂ} {t : ℝ} (ht : t ≠ 0) : ratLift G t = G (ratUnit t) := by
  rw [ratLift, ← ratUnit_val ht, Units.val_injective.extend_apply]

theorem ratLift_zero (G : Iq → ℂ) : ratLift G 0 = 0 := by
  rw [ratLift, Function.extend_apply']
  · rfl
  · rintro ⟨u, hu⟩
    have h := (ratMem_range_units (ratRealCoordEquiv.symm 0)).1 ⟨u, hu⟩
    simp at h

theorem ratLift_eq (G : Iq → ℂ) (g : Iq) : ratLift G (eq g.val) = G g := by
  rw [ratLift_of_ne ((ratMem_range_units g.val).1 ⟨g, rfl⟩), ratUnit_eq]

/-- Integration against the additive measure is Lebesgue integration in the real coordinate. -/
theorem ratIntegral_add (H : Aq → ℂ) : ∫ y, H y ∂νq = ∫ t, H (ratRealCoordEquiv.symm t) := by
  have h := (measurePreserving_ratRealCoord.symm ratRealMeasurableEquiv).integral_comp'
    (g := H)
  exact h.symm

/-- Integration against the multiplicative measure is integration against `dt / |t|` in the
real coordinate. This is `sLocalTrace_measure_density`, whose constant is one when there is no
finite place. -/
theorem ratIntegral_mul (G : Iq → ℂ) :
    ∫ g, G g ∂μq = ∫ t, ratLift G t / ((|t| : ℝ) : ℂ) := by
  have : BorelSpace Aq := sAdeleRing_borelSpace
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  have ho : Topology.IsOpenEmbedding (Units.val : Iq → Aq) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace ℚ) → w.Completion) × ((v : Sq) → v.val.adicCompletion ℚ))
  have hval := ho.measurableEmbedding
  let Gz : Aq → ℂ := Function.extend (Units.val : Iq → Aq) G 0
  have hGz (g : Iq) : Gz g.val = G g := Units.val_injective.extend_apply _ _ g
  have hGz0 (y : Aq) (hy : y ∉ range (Units.val : Iq → Aq)) : Gz y = 0 := by
    simp only [Gz, Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ ↦ hy ⟨u, hu⟩)]
    rfl
  let d : Aq → ℝ≥0∞ := fun z ↦ ENNReal.ofReal (sLocalTraceMeasureFactor (F := ℚ) Sq / modq(z))
  have hmod : Continuous fun z : Aq ↦ modq(z) := by
    simp only [ratModq]
    exact continuous_abs.comp ((InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
      Rat.isReal_infinitePlace).continuous.comp ((continuous_apply _).comp continuous_fst))
  have hd : Measurable d := ENNReal.measurable_ofReal.comp (measurable_const.div hmod.measurable)
  calc ∫ g, G g ∂μq = ∫ g, Gz g.val ∂μq := integral_congr_ae (ae_of_all _ fun g ↦ (hGz g).symm)
    _ = ∫ y, Gz y ∂((μq).map (Units.val : Iq → Aq)) := (hval.integral_map Gz).symm
    _ = ∫ y, Gz y ∂(((νq).restrict (range (Units.val : Iq → Aq))).withDensity d) := by
        rw [sLocalTrace_measure_density]
    _ = ∫ y in range (Units.val : Iq → Aq), (d y).toReal • Gz y ∂νq :=
        integral_withDensity_eq_integral_toReal_smul hd (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top) _
    _ = ∫ y, (d y).toReal • Gz y ∂νq := by
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ ?_
        rw [hGz0 y hy, smul_zero]
    _ = ∫ t, (d (ratRealCoordEquiv.symm t)).toReal • Gz (ratRealCoordEquiv.symm t) :=
        ratIntegral_add _
    _ = ∫ t, ratLift G t / ((|t| : ℝ) : ℂ) := by
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        have hf : sLocalTraceMeasureFactor (F := ℚ) Sq = 1 := by simp [sLocalTraceMeasureFactor]
        change (ENNReal.ofReal (sLocalTraceMeasureFactor (F := ℚ) Sq /
          modq(ratRealCoordEquiv.symm t))).toReal • Gz (ratRealCoordEquiv.symm t) = _
        rw [hf, ratModq, RingEquiv.apply_symm_apply, ENNReal.toReal_ofReal (by positivity),
          Complex.real_smul]
        change _ = Gz (ratRealCoordEquiv.symm t) / _
        rw [one_div, Complex.ofReal_inv, div_eq_inv_mul]

end Integrals

section Units

local notation "eq" => ratRealCoordEquiv

theorem ratUnits_ext {g h : Iq} (hgh : eq g.val = eq h.val) : g = h :=
  Units.ext (ratRealCoordEquiv.injective hgh)

/-- The image of a unit of the integers in the S-ideles has the same real coordinate. -/
theorem eq_projectedDiagonal (u : ((Sq : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)ˣ) :
    eq ((Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection ℚ Sq)
      (Subring.subtype (integralAdelesOutside ℚ Sq)))))
      (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal ℚ Sq)) u)).val =
      ((u.val.val : ℚ) : ℝ) := by
  obtain ⟨-, h1, -⟩ := sAdele_diagonal_apply (F := ℚ) (S := Sq) u.val
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
    ((adeleProjection ℚ Sq (integralAdeleDiagonal ℚ Sq u.val).val).1 Rat.infinitePlace) = _
  rw [h1]
  exact eq_ratCast ((InfinitePlace.Completion.extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace).comp (algebraMap ℚ Rat.infinitePlace.Completion)) _

/-- A unit of the integers of `ℚ` is `1` or `-1`. -/
theorem integer_empty_unit (u : ((Sq : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)ˣ) :
    (u.val.val : ℚ) = 1 ∨ (u.val.val : ℚ) = -1 := by
  have hbot : ((Sq : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ) = ⊥ := by
    rw [Finset.coe_empty, IsDedekindDomain.integer_empty]
  have hmem : ∀ x : ((Sq : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ),
      ∃ r : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ r = x.val := by
    intro x
    have hx : x.val ∈ (⊥ : Subalgebra (𝓞 ℚ) ℚ) := hbot ▸ x.property
    obtain ⟨r, hr⟩ := Algebra.mem_bot.mp hx
    exact ⟨r, hr⟩
  obtain ⟨a, ha⟩ := hmem u.val
  obtain ⟨b, hb⟩ := hmem u⁻¹.val
  have hu : (u.val.val : ℚ) * (u⁻¹.val.val : ℚ) = 1 := by
    exact congrArg Subtype.val u.mul_inv
  have hab : a * b = 1 := by
    apply IsFractionRing.injective (𝓞 ℚ) ℚ
    rw [map_mul, ha, hb, map_one]
    exact hu
  have hunit : IsUnit (Rat.ringOfIntegersEquiv a) :=
    (IsUnit.of_mul_eq_one b hab).map Rat.ringOfIntegersEquiv
  rw [← ha, ← Rat.ringOfIntegersEquiv_apply_coe]
  rcases Int.isUnit_iff.mp hunit with h | h <;> simp [h]

/-- The S-units of `ℚ` with no finite place are `±1`. -/
theorem mem_ratProjectedDiagonal_iff (g : Iq) : g ∈ Hq ↔ eq g.val = 1 ∨ eq g.val = -1 := by
  constructor
  · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
    rw [eq_projectedDiagonal]
    rcases integer_empty_unit u with h | h <;> simp [h]
  · intro h
    have hm1 : ∃ u : ((Sq : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)ˣ, (u.val.val : ℚ) = -1 :=
      ⟨-1, by simp⟩
    rcases h with h | h
    · rw [ratUnits_ext (h.trans (by simp) : eq g.val = eq (1 : Iq).val)]
      exact (sProjectedDiagonal ℚ Sq).one_mem
    · obtain ⟨u, hu⟩ := hm1
      refine ⟨_, ⟨u, rfl⟩, ratUnits_ext ?_⟩
      rw [eq_projectedDiagonal, hu, h]
      simp

/-- The element `-1` of the S-units. -/
def ratMinusOne : Hq := ⟨-1, (mem_ratProjectedDiagonal_iff _).2 (Or.inr (by simp))⟩

theorem ratMinusOne_ne_one : ratMinusOne ≠ 1 := by
  intro h
  have h' := congrArg (fun ξ : Hq ↦ eq ξ.val.val) h
  simp [ratMinusOne] at h'
  norm_num at h'

theorem ratProjectedDiagonal_cases (ξ : Hq) : ξ = 1 ∨ ξ = ratMinusOne := by
  rcases (mem_ratProjectedDiagonal_iff ξ.val).1 ξ.property with h | h
  · left
    exact Subtype.ext (ratUnits_ext (h.trans (by simp)))
  · right
    exact Subtype.ext (ratUnits_ext (h.trans (by simp [ratMinusOne])))

open Classical in
/-- The two S-units, as an equivalence with `Bool`. -/
def ratProjectedDiagonalEquiv : Bool ≃ Hq where
  toFun b := if b then 1 else ratMinusOne
  invFun ξ := decide (ξ = 1)
  left_inv b := by cases b <;> simp [ratMinusOne_ne_one]
  right_inv ξ := by
    rcases ratProjectedDiagonal_cases ξ with rfl | rfl <;> simp [ratMinusOne_ne_one]

instance : Finite Hq := Finite.of_equiv _ ratProjectedDiagonalEquiv

/-- A sum over the S-units is the sum of the values at `1` and `-1`. -/
theorem tsum_ratProjectedDiagonal (F : Hq → ℂ) : ∑' ξ, F ξ = F 1 + F ratMinusOne := by
  rw [← ratProjectedDiagonalEquiv.tsum_eq, tsum_fintype, Fintype.sum_bool]
  simp [ratProjectedDiagonalEquiv]

/-- The S-ideles with positive real coordinate are a fundamental domain for the S-units. -/
theorem isFundamentalDomain_ratPos :
    IsFundamentalDomain Hq {x : Iq | 0 < eq x.val} μq := by
  have : BorelSpace Aq := sAdeleRing_borelSpace
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  have hmeas : Measurable fun x : Iq ↦ eq x.val :=
    measurable_ratRealCoordEquiv.comp Units.continuous_val.measurable
  refine IsFundamentalDomain.mk' (measurableSet_lt measurable_const hmeas).nullMeasurableSet
    fun x ↦ ?_
  have hx : eq x.val ≠ 0 := (ratMem_range_units x.val).1 ⟨x, rfl⟩
  have hsmul (ξ : Hq) : eq (ξ • x).val = eq ξ.val.val * eq x.val := by
    change eq ((ξ.val * x : Iq) : Aq) = _
    rw [Units.val_mul, map_mul]
  have hm : eq ratMinusOne.val.val = -1 := by simp [ratMinusOne]
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · refine ⟨ratMinusOne, ?_, fun ξ hξ ↦ ?_⟩
    · change 0 < eq (ratMinusOne • x).val
      rw [hsmul, hm]
      linarith
    · rcases ratProjectedDiagonal_cases ξ with rfl | rfl
      · change 0 < eq ((1 : Hq) • x).val at hξ
        rw [hsmul] at hξ
        simp at hξ
        linarith
      · rfl
  · refine ⟨1, ?_, fun ξ hξ ↦ ?_⟩
    · change 0 < eq ((1 : Hq) • x).val
      rw [hsmul]
      simpa using hpos
    · rcases ratProjectedDiagonal_cases ξ with rfl | rfl
      · rfl
      · change 0 < eq (ratMinusOne • x).val at hξ
        rw [hsmul, hm] at hξ
        linarith

/-- On the positive S-ideles of norm at most `L`, integration against the additive measure
pulled back to the units is Lebesgue integration over `(0, L]`. -/
theorem ratSetIntegral_comap (G : Iq → ℂ) (L : ℝ) :
    ∫ x in {x : Iq | 0 < eq x.val} ∩ {x : Iq | normq(x) ≤ L}, G x ∂((νq).comap Units.val) =
      ∫ t in Ioc 0 L, ratLift G t := by
  have : BorelSpace Aq := sAdeleRing_borelSpace
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  have ho : Topology.IsOpenEmbedding (Units.val : Iq → Aq) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace ℚ) → w.Completion) × ((v : Sq) → v.val.adicCompletion ℚ))
  have hval := ho.measurableEmbedding
  set d := {x : Iq | 0 < eq x.val} ∩ {x : Iq | normq(x) ≤ L} with hd_def
  have hmeas : Measurable fun x : Iq ↦ eq x.val :=
    measurable_ratRealCoordEquiv.comp Units.continuous_val.measurable
  have hd : MeasurableSet d := by
    refine (measurableSet_lt measurable_const hmeas).inter ?_
    have hn : Measurable fun x : Iq ↦ normq(x) := by
      simp only [ratNormq]
      exact continuous_abs.measurable.comp hmeas
    exact measurableSet_le hn measurable_const
  let Gz : Aq → ℂ := Function.extend (Units.val : Iq → Aq) (d.indicator G) 0
  have hGz (g : Iq) : Gz g.val = d.indicator G g := Units.val_injective.extend_apply _ _ g
  have hGz0 (y : Aq) (hy : y ∉ range (Units.val : Iq → Aq)) : Gz y = 0 := by
    simp only [Gz, Function.extend_apply' _ _ _ (fun ⟨u, hu⟩ ↦ hy ⟨u, hu⟩)]
    rfl
  calc ∫ x in d, G x ∂((νq).comap Units.val)
      = ∫ x, d.indicator G x ∂((νq).comap Units.val) := (integral_indicator hd).symm
    _ = ∫ x, Gz x.val ∂((νq).comap Units.val) :=
        integral_congr_ae (ae_of_all _ fun g ↦ (hGz g).symm)
    _ = ∫ y, Gz y ∂(((νq).comap Units.val).map Units.val) := (hval.integral_map Gz).symm
    _ = ∫ y in range (Units.val : Iq → Aq), Gz y ∂νq := by rw [hval.map_comap]
    _ = ∫ y, Gz y ∂νq := setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ hGz0 y hy
    _ = ∫ t, Gz (ratRealCoordEquiv.symm t) := ratIntegral_add Gz
    _ = ∫ t, (Ioc 0 L).indicator (ratLift G) t := by
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        show Gz (ratRealCoordEquiv.symm t) = (Ioc 0 L).indicator (ratLift G) t
        rcases eq_or_ne t 0 with rfl | ht
        · rw [hGz0 _ fun h ↦ (ratMem_range_units _).1 h (by simp)]
          simp
        · rw [← ratUnit_val ht, hGz]
          by_cases hmem : t ∈ Ioc 0 L
          · rw [indicator_of_mem hmem, ratLift_of_ne ht, indicator_of_mem]
            refine ⟨?_, ?_⟩
            · change 0 < eq (ratUnit t).val
              rw [eq_ratUnit ht]
              exact hmem.1
            · change normq(ratUnit t) ≤ L
              rw [ratNormq, eq_ratUnit ht, abs_of_pos hmem.1]
              exact hmem.2
          · rw [indicator_of_notMem hmem, indicator_of_notMem]
            rintro ⟨h1, h2⟩
            change 0 < eq (ratUnit t).val at h1
            change normq(ratUnit t) ≤ L at h2
            rw [eq_ratUnit ht] at h1
            rw [ratNormq, eq_ratUnit ht, abs_of_pos h1] at h2
            exact hmem ⟨h1, h2⟩
    _ = ∫ t in Ioc 0 L, ratLift G t := integral_indicator measurableSet_Ioc

end Units

section LiftedTest

local notation "eq" => ratRealCoordEquiv

theorem continuous_ratRealCoordEquiv : Continuous (ratRealCoordEquiv : Aq → ℝ) :=
  (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace).continuous.comp ((continuous_apply _).comp continuous_fst)

theorem continuous_ratRealCoordEquiv_symm : Continuous (ratRealCoordEquiv.symm : ℝ → Aq) := by
  have hr : Continuous (InfinitePlace.Completion.ringEquivRealOfIsReal
      Rat.isReal_infinitePlace).symm :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.continuous
  have hu : Continuous ((RingEquiv.piUnique (fun w : InfinitePlace ℚ ↦ w.Completion)).symm) :=
    (Homeomorph.piUnique (fun w : InfinitePlace ℚ ↦ w.Completion)).symm.continuous
  exact (hu.comp hr).prodMk continuous_const

/-- Extension by zero along an open embedding keeps continuity of a function with compact
support. -/
theorem continuous_extend_zero_of_isOpenEmbedding {X Z : Type*} [TopologicalSpace X]
    [TopologicalSpace Z] [T2Space Z] {e : X → Z} (he : Topology.IsOpenEmbedding e) {G : X → ℂ}
    (hG : Continuous G) (hs : HasCompactSupport G) : Continuous (Function.extend e G 0) :=
  continuous_of_tsupport fun y hy ↦ by
    obtain ⟨x, -, rfl⟩ := hs.tsupport_extend_zero_subset he.continuous hy
    rw [← he.continuousAt_iff, Function.extend_comp he.injective]
    exact hG.continuousAt

/-- A test on the S-ideles is continuous (`continuous_of_bruhatSmooth`). -/
theorem continuous_bruhatCompactSupport_val (f : BruhatCompactSupport Iq) : Continuous f.val := by
  have : BorelSpace Aq := sAdeleRing_borelSpace
  have : BorelSpace Iq := sIdeleGroup_borelSpace
  let (v : Sq) : ProperSpace (v.val.adicCompletion ℚ) := properSpace_adicCompletion v.val
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology Aq := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : Sq) → v.val.adicCompletion ℚ)))
  let : SecondCountableTopology Iq := (sIdeleGroup_description ℚ Sq).1.secondCountableTopology
  exact continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 f.property.1)

/-- The lift of a test to the real line is continuous. -/
theorem continuous_ratLift (f : BruhatCompactSupport Iq) : Continuous (ratLift f.val) := by
  have ho : Topology.IsOpenEmbedding (Units.val : Iq → Aq) := IsOpenUnits.isOpenEmbedding_unitsVal
    (M := ((w : InfinitePlace ℚ) → w.Completion) × ((v : Sq) → v.val.adicCompletion ℚ))
  exact (continuous_extend_zero_of_isOpenEmbedding ho (continuous_bruhatCompactSupport_val f)
    f.property.2).comp continuous_ratRealCoordEquiv_symm

/-- The lift of a test to the real line vanishes near the origin and far out. -/
theorem exists_ratLift_support (f : BruhatCompactSupport Iq) :
    ∃ a b : ℝ, 0 < a ∧ ∀ s, ratLift f.val s ≠ 0 → a ≤ |s| ∧ |s| ≤ b := by
  have hK := f.property.2
  have hc : Continuous fun g : Iq ↦ eq g.val :=
    continuous_ratRealCoordEquiv.comp Units.continuous_val
  have hne (g : Iq) : eq g.val ≠ 0 := (ratMem_range_units g.val).1 ⟨g, rfl⟩
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn (f := fun g : Iq ↦ eq g.val)
    hc.continuousOn
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn (f := fun g : Iq ↦ (eq g.val)⁻¹)
    (hc.continuousOn.inv₀ fun g _ ↦ hne g)
  refine ⟨(max B 1)⁻¹, b, by positivity, fun s hs ↦ ?_⟩
  have hs0 : s ≠ 0 := fun h ↦ hs (h ▸ ratLift_zero _)
  rw [ratLift_of_ne hs0] at hs
  have hmem : ratUnit s ∈ tsupport f.val := subset_tsupport _ hs
  have h1 := hb _ hmem
  have h2 := hB _ hmem
  simp only [eq_ratUnit hs0, Real.norm_eq_abs, abs_inv] at h1 h2
  refine ⟨?_, h1⟩
  rw [inv_le_comm₀ (by positivity) (abs_pos.mpr hs0)]
  exact h2.trans (le_max_left _ _)

/-- The lift of a test to the real line has compact support. -/
theorem hasCompactSupport_ratLift (f : BruhatCompactSupport Iq) :
    HasCompactSupport (ratLift f.val) := by
  obtain ⟨a, b, -, h⟩ := exists_ratLift_support f
  refine HasCompactSupport.intro (isCompact_Icc (a := -b) (b := b)) fun s hs ↦ ?_
  by_contra hne
  exact hs (abs_le.mp (h s hne).2)

end LiftedTest

section KernelDiagonal

local notation "eq" => ratRealCoordEquiv

/-- The real coordinate of an inverse is the inverse of the real coordinate. -/
theorem eq_inv_val (g : Iq) : eq (g⁻¹).val = (eq g.val)⁻¹ := by
  exact eq_inv_of_mul_eq_one_left (by rw [← map_mul, Units.inv_mul, map_one])

/-- The dilation kernel of a test, evaluated on a character phase, in the real coordinate. -/
theorem ratDilationKernel_phase (f : BruhatCompactSupport Iq) (x : Iq) (y u : Aq) :
    sLocalTraceDilationKernel f (fun z ↦ (sAdeleStandardCharacter ℚ Sq ((z - y) * u) : ℂ)) x.val =
      ∫ s, ratLift f.val s / ((Real.sqrt |s| * |s| : ℝ) : ℂ) *
        (Circle.exp (2 * π * ((s⁻¹ * eq x.val - eq y) * eq u)) : ℂ) := by
  rw [sLocalTraceDilationKernel, ratIntegral_mul]
  refine integral_congr_ae (ae_of_all _ fun s ↦ ?_)
  rcases eq_or_ne s 0 with rfl | hs
  · simp [ratLift_zero]
  · beta_reduce
    rw [ratLift_of_ne hs, ratLift_of_ne hs]
    simp only [ratSAdeleStandardCharacter, ratNormq, eq_ratUnit hs, map_mul, map_sub, eq_inv_val]
    push_cast
    ring

/-- A continuous function vanishing near the origin stays continuous after division by
`|s| ^ (3 / 2)`. -/
theorem continuous_div_sqrt_abs_mul_abs {G : ℝ → ℂ} (hG : Continuous G) {a : ℝ} (ha : 0 < a)
    (hsupp : ∀ s, G s ≠ 0 → a ≤ |s|) :
    Continuous fun s ↦ G s / ((Real.sqrt |s| * |s| : ℝ) : ℂ) := by
  have hw : Continuous fun s : ℝ ↦ (((max (Real.sqrt |s| * |s|) (Real.sqrt a * a))⁻¹ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (((continuous_abs.sqrt.mul continuous_abs).max
      continuous_const).inv₀ fun s ↦ (lt_max_of_lt_right (by positivity)).ne')
  refine (hG.mul hw).congr fun s ↦ ?_
  by_cases h : G s = 0
  · simp [h]
  · have hs := hsupp s h
    have hle : Real.sqrt a * a ≤ Real.sqrt |s| * |s| :=
      mul_le_mul (Real.sqrt_le_sqrt hs) hs ha.le (Real.sqrt_nonneg _)
    rw [Pi.mul_apply, max_eq_left hle, div_eq_mul_inv, Complex.ofReal_inv]

/-- Integrating the phase `exp (2π i c(s) v)` over the band `|v| ≤ Y` gives the sinc kernel. -/
theorem integral_band_mul_integral_phase {G : ℝ → ℂ} (hG : Continuous G)
    (hGc : HasCompactSupport G) (c : ℝ → ℝ) (hc : Measurable c) {Y : ℝ} (hY : 0 ≤ Y) :
    ∫ v, (Icc (-Y) Y).indicator (fun _ ↦ (1 : ℂ)) v *
        ∫ s, G s * (Circle.exp (2 * π * (c s * v)) : ℂ) =
      ∫ s, G s * ((2 * Y * Real.sinc (2 * π * c s * Y) : ℝ) : ℂ) := by
  have hGi : Integrable G := hG.integrable_of_hasCompactSupport hGc
  have hph : Measurable fun p : ℝ × ℝ ↦ (Circle.exp (2 * π * (c p.2 * p.1)) : ℂ) :=
    (continuous_subtype_val.comp Circle.exp.continuous).measurable.comp
      (measurable_const.mul ((hc.comp measurable_snd).mul measurable_fst))
  have hind : Integrable ((Icc (-Y) Y).indicator (fun _ ↦ (1 : ℝ))) :=
    (integrableOn_const (hs := measure_Icc_lt_top.ne) (C := (1 : ℝ))).integrable_indicator
      measurableSet_Icc
  have hint : Integrable (Function.uncurry fun v s ↦
      (Icc (-Y) Y).indicator (fun _ ↦ (1 : ℂ)) v * (G s * (Circle.exp (2 * π * (c s * v)) : ℂ)))
      (volume.prod volume) := by
    refine (hind.mul_prod hGi.norm).mono' ?_ (ae_of_all _ fun p ↦ ?_)
    · exact (((measurable_const.indicator measurableSet_Icc).comp measurable_fst).mul
        ((hG.measurable.comp measurable_snd).mul hph)).aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Circle.norm_coe, mul_one]
      by_cases hv : p.1 ∈ Icc (-Y) Y <;> simp [hv]
  calc ∫ v, (Icc (-Y) Y).indicator (fun _ ↦ (1 : ℂ)) v *
        ∫ s, G s * (Circle.exp (2 * π * (c s * v)) : ℂ)
      = ∫ v, ∫ s, (Icc (-Y) Y).indicator (fun _ ↦ (1 : ℂ)) v *
          (G s * (Circle.exp (2 * π * (c s * v)) : ℂ)) := by
        congr 1
        funext v
        exact (integral_const_mul _ _).symm
    _ = ∫ s, ∫ v, (Icc (-Y) Y).indicator (fun _ ↦ (1 : ℂ)) v *
          (G s * (Circle.exp (2 * π * (c s * v)) : ℂ)) := integral_integral_swap hint
    _ = ∫ s, G s * ((2 * Y * Real.sinc (2 * π * c s * Y) : ℝ) : ℂ) := by
        congr 1
        funext s
        calc ∫ v, (Icc (-Y) Y).indicator (fun _ ↦ (1 : ℂ)) v *
              (G s * (Circle.exp (2 * π * (c s * v)) : ℂ))
            = G s * ∫ v, (Icc (-Y) Y).indicator
                (fun v ↦ (Circle.exp (2 * π * (c s * v)) : ℂ)) v := by
              rw [← integral_const_mul]
              congr 1
              funext v
              by_cases hv : v ∈ Icc (-Y) Y <;> simp [hv]
          _ = G s * ∫ v in (-Y)..Y, Complex.exp (((2 * π * c s * v : ℝ) : ℂ) * Complex.I) := by
              rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
                ← intervalIntegral.integral_of_le (by linarith)]
              congr 1
              refine intervalIntegral.integral_congr fun v _ ↦ ?_
              simp only [Circle.coe_exp]
              congr 2
              push_cast
              ring
          _ = _ := by rw [integral_exp_mul_I_symm]

/-- The real profile of a test: its lift to the line divided by `|s| ^ (3 / 2)`. -/
def ratProfile (f : BruhatCompactSupport Iq) (s : ℝ) : ℂ :=
  ratLift f.val s / ((Real.sqrt |s| * |s| : ℝ) : ℂ)

/-- The real profile of a test is continuous. -/
theorem continuous_ratProfile (f : BruhatCompactSupport Iq) : Continuous (ratProfile f) := by
  obtain ⟨a, b, ha, h⟩ := exists_ratLift_support f
  exact continuous_div_sqrt_abs_mul_abs (continuous_ratLift f) ha fun s hs ↦ (h s hs).1

/-- The real profile of a test has compact support. -/
theorem hasCompactSupport_ratProfile (f : BruhatCompactSupport Iq) :
    HasCompactSupport (ratProfile f) :=
  (hasCompactSupport_ratLift f).mono fun s hs h0 ↦ hs (by simp [ratProfile, h0])

/-- Paper: Step II, p. 517, for `ℚ` with no finite place.
Reconstruction: at the point with real coordinate `0 < t ≤ L`, the cutoff kernel on the skew
diagonal of the unit `σ = ±1` is `∫ ψ(s) |s| ^ (-3/2) 2Y sinc (2π Y (σ t / s - t)) ds`, where `ψ` is
the lift of the test to the line. The frequency integral over `|v| ≤ Y` produces the sinc. -/
theorem ratCutoffKernel_diag (f : BruhatCompactSupport Iq) (ξ : Hq) {L Y t : ℝ} (ht : 0 < t)
    (htL : t ≤ L) (hY : 0 ≤ Y) :
    sLocalTraceCutoffKernel f (indicator {x : Iq | normq(x) ≤ L} (fun _ ↦ 1))
        (indicator (sLocalPWProductRegion (F := ℚ) Sq Y) (fun _ ↦ 1)) (ξ.val * ratUnit t)
        (ratUnit t).val =
      ∫ s, ratProfile f s *
        ((2 * Y * Real.sinc (2 * π * (s⁻¹ * (eq ξ.val.val * t) - t) * Y) : ℝ) : ℂ) := by
  have ht0 : t ≠ 0 := ht.ne'
  have hσ : |eq ξ.val.val| = 1 := by
    rcases (mem_ratProjectedDiagonal_iff _).1 ξ.property with h | h <;> simp [h]
  have hx : eq (ξ.val * ratUnit t).val = eq ξ.val.val * t := by
    rw [Units.val_mul, map_mul, eq_ratUnit ht0]
  have hρ : indicator {x : Iq | normq(x) ≤ L} (fun _ ↦ (1 : ℂ)) (ξ.val * ratUnit t) = 1 := by
    refine indicator_of_mem ?_ _
    change normq(ξ.val * ratUnit t) ≤ L
    rw [ratNormq, hx, abs_mul, hσ, one_mul, abs_of_pos ht]
    exact htL
  rw [sLocalTraceCutoffKernel, hρ, one_mul, ratIntegral_add]
  have hc : Measurable fun s : ℝ ↦ s⁻¹ * (eq ξ.val.val * t) - t := by fun_prop
  refine Eq.trans ?_ (integral_band_mul_integral_phase (continuous_ratProfile f)
    (hasCompactSupport_ratProfile f) (fun s ↦ s⁻¹ * (eq ξ.val.val * t) - t) hc hY)
  refine integral_congr_ae (ae_of_all _ fun v ↦ ?_)
  beta_reduce
  rw [ratDilationKernel_phase]
  simp only [hx, eq_ratUnit ht0, RingEquiv.apply_symm_apply]
  congr 1
  by_cases hv : v ∈ Icc (-Y) Y
  · rw [indicator_of_mem hv, indicator_of_mem]
    rw [ratMem_band, RingEquiv.apply_symm_apply]
    exact abs_le.2 hv
  · rw [indicator_of_notMem hv, indicator_of_notMem]
    rw [ratMem_band, RingEquiv.apply_symm_apply]
    exact fun h ↦ hv (abs_le.1 h)

end KernelDiagonal

section Folding

/-- Swap the spatial and multiplicative integrals of the sinc kernel. -/
theorem integral_Ioc_integral_sinc_swap {G : ℝ → ℂ} (hG : Continuous G)
    (hGc : HasCompactSupport G) (σ Y L : ℝ) :
    Integrable (fun s ↦ G s * ∫ t in Ioc 0 L,
        ((2 * Y * Real.sinc (2 * π * (s⁻¹ * (σ * t) - t) * Y) : ℝ) : ℂ)) ∧
    ∫ t in Ioc 0 L, ∫ s, G s * ((2 * Y * Real.sinc (2 * π * (s⁻¹ * (σ * t) - t) * Y) : ℝ) : ℂ) =
      ∫ s, G s * ∫ t in Ioc 0 L,
        ((2 * Y * Real.sinc (2 * π * (s⁻¹ * (σ * t) - t) * Y) : ℝ) : ℂ) := by
  have hGi : Integrable G := hG.integrable_of_hasCompactSupport hGc
  have hkm : Measurable fun p : ℝ × ℝ ↦
      ((2 * Y * Real.sinc (2 * π * (p.2⁻¹ * (σ * p.1) - p.1) * Y) : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp (measurable_const.mul
      (Real.continuous_sinc.measurable.comp (by fun_prop)))
  have hint : Integrable (Function.uncurry fun t s ↦
      G s * ((2 * Y * Real.sinc (2 * π * (s⁻¹ * (σ * t) - t) * Y) : ℝ) : ℂ))
      ((volume.restrict (Ioc 0 L)).prod volume) := by
    have h1 : Integrable (fun _ : ℝ ↦ (2 * |Y| : ℝ)) (volume.restrict (Ioc 0 L)) :=
      integrable_const _
    refine (h1.mul_prod hGi.norm).mono' ?_ (ae_of_all _ fun p ↦ ?_)
    · exact ((hG.measurable.comp measurable_snd).mul hkm).aestronglyMeasurable
    · simp only [Function.uncurry, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_two]
      have := Real.abs_sinc_le_one (2 * π * (p.2⁻¹ * (σ * p.1) - p.1) * Y)
      have h0 := norm_nonneg (G p.2)
      have h2 := abs_nonneg Y
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg h0 h2)]
  refine ⟨?_, ?_⟩
  · refine hint.integral_prod_right.congr (ae_of_all _ fun s ↦ ?_)
    simp only [Function.uncurry]
    exact integral_const_mul (G s) _
  · rw [integral_integral_swap hint]
    congr 1
    funext s
    exact integral_const_mul (G s) _

/-- An integral over the line is the integral over the positive half-line of the sum of the
values at `h` and `-h`. -/
theorem integral_eq_integral_Ioi_add_neg {F : ℝ → ℂ} (hF : Integrable F) :
    ∫ s, F s = ∫ h in Ioi 0, (F h + F (-h)) := by
  have hFn : Integrable fun h ↦ F (-h) := hF.comp_neg
  rw [integral_add hF.integrableOn hFn.integrableOn, integral_comp_neg_Ioi, neg_zero,
    ← compl_Ioi, integral_add_compl measurableSet_Ioi hF]

/-- The sinc integral over a symmetric interval is twice the integral over the right half. -/
theorem intervalIntegral_sinc_symm (c : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in (-L)..L, Real.sinc (c * x) = 2 * ∫ x in Ioc 0 L, Real.sinc (c * x) := by
  have hc : Continuous fun x : ℝ ↦ Real.sinc (c * x) := Real.continuous_sinc.comp (by fun_prop)
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0) (hc.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _)]
  have h : ∫ x in (-L)..0, Real.sinc (c * x) = ∫ x in (0 : ℝ)..L, Real.sinc (c * x) := by
    rw [← neg_zero, ← intervalIntegral.integral_comp_neg]
    simp only [neg_zero, mul_neg, Real.sinc_neg]
  rw [h, intervalIntegral.integral_of_le hL]
  ring

/-- The constant `2 Y` and the coercion come out of the sinc integral. -/
theorem setIntegral_sinc_ofReal (Y L c : ℝ) (u : ℝ → ℝ)
    (hu : ∀ t, Real.sinc (u t) = Real.sinc (c * t)) :
    ∫ t in Ioc 0 L, ((2 * Y * Real.sinc (u t) : ℝ) : ℂ) =
      ((2 * Y * ∫ t in Ioc 0 L, Real.sinc (c * t) : ℝ) : ℂ) := by
  rw [integral_complex_ofReal, integral_const_mul]
  simp only [hu]

end Folding

section SumIdentity

local notation "eq" => ratRealCoordEquiv

/-- The lift of a test folded onto the positive half-line and divided by `h`. It is the test
function of the dilation on the real line whose cutoff carries the same trace. -/
def ratFold (f : BruhatCompactSupport Iq) (h : ℝ) : ℂ :=
  (Ioi (0 : ℝ)).indicator (fun h ↦ (ratLift f.val h + ratLift f.val (-h)) / h) h

/-- Folding at a point `h > 0`: the two units and the two signs of `s` together give the folded
test times the trace of the single dilation. -/
theorem ratFold_pointwise (f : BruhatCompactSupport Iq) {Y L h : ℝ} (hY : 0 < Y) (hL : 0 ≤ L)
    (hh : 0 < h) :
    (ratProfile f h * (∫ t in Ioc 0 L,
        ((2 * Y * Real.sinc (2 * π * (h⁻¹ * (1 * t) - t) * Y) : ℝ) : ℂ)) +
      ratProfile f (-h) * ∫ t in Ioc 0 L,
        ((2 * Y * Real.sinc (2 * π * ((-h)⁻¹ * (1 * t) - t) * Y) : ℝ) : ℂ)) +
    (ratProfile f h * (∫ t in Ioc 0 L,
        ((2 * Y * Real.sinc (2 * π * (h⁻¹ * (-1 * t) - t) * Y) : ℝ) : ℂ)) +
      ratProfile f (-h) * ∫ t in Ioc 0 L,
        ((2 * Y * Real.sinc (2 * π * ((-h)⁻¹ * (-1 * t) - t) * Y) : ℝ) : ℂ)) =
    ratFold f h * realPWSharpTrace Y 0 0 le_rfl h L := by
  have e1 := setIntegral_sinc_ofReal Y L (2 * π * Y * (h⁻¹ - 1))
    (fun t ↦ 2 * π * (h⁻¹ * (1 * t) - t) * Y) (fun t ↦ by congr 1; ring)
  have e2 := setIntegral_sinc_ofReal Y L (2 * π * Y * (h⁻¹ + 1))
    (fun t ↦ 2 * π * ((-h)⁻¹ * (1 * t) - t) * Y)
    (fun t ↦ by rw [← Real.sinc_neg (2 * π * Y * (h⁻¹ + 1) * t)]; congr 1; ring)
  have e3 := setIntegral_sinc_ofReal Y L (2 * π * Y * (h⁻¹ + 1))
    (fun t ↦ 2 * π * (h⁻¹ * (-1 * t) - t) * Y)
    (fun t ↦ by rw [← Real.sinc_neg (2 * π * Y * (h⁻¹ + 1) * t)]; congr 1; ring)
  have e4 := setIntegral_sinc_ofReal Y L (2 * π * Y * (h⁻¹ - 1))
    (fun t ↦ 2 * π * ((-h)⁻¹ * (-1 * t) - t) * Y) (fun t ↦ by congr 1; ring)
  rw [e1, e2, e3, e4, realPWSharpTrace_zero_zero_eq_sinc Y le_rfl hY h hL,
    intervalIntegral_sinc_symm _ hL, intervalIntegral_sinc_symm _ hL]
  simp only [ratProfile, ratFold, indicator_of_mem (show h ∈ Ioi 0 from hh), abs_neg,
    abs_of_pos hh]
  rw [Real.rpow_neg hh.le, ← Real.sqrt_eq_rpow]
  have hs : (Real.sqrt h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hh).ne'
  have hh' : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hh.ne'
  push_cast
  field_simp
  ring

/-- Paper: (12.4.1.22)–(12.4.1.24), p. 518, for `ℚ` with no finite place.
Reconstruction: one sharp orbital mass as a double integral on the line. This is
`sLocalTraceSharpMass_eq_integral` with the positive reals as fundamental domain, evaluated by
`ratCutoffKernel_diag`. -/
theorem ratSharpMass_eq (f : BruhatCompactSupport Iq) (ξ : Hq) {L Y : ℝ} (hL : 0 < L)
    (hY : 0 < Y) :
    sLocalTraceSharpMass f ξ (L * Y) = ∫ t in Ioc 0 L, ∫ s, ratProfile f s *
        ((2 * Y * Real.sinc (2 * π * (s⁻¹ * (eq ξ.val.val * t) - t) * Y) : ℝ) : ℂ) := by
  have h := (sLocalTraceSharpMass_eq_integral f ξ _ isFundamentalDomain_ratPos L Y hL hY).2
  dsimp only at h
  rw [← h, ratSetIntegral_comap]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ ?_
  rw [ratLift_of_ne ht.1.ne']
  exact ratCutoffKernel_diag f ξ ht.1 ht.2 hY.le

/-- Paper: (12.4.1.24), p. 518, for `ℚ` with no finite place.
Reconstruction: the sum of the sharp orbital masses over the S-units `±1` at radius `L Y` is the
integral of the folded test against the traces of the sharp cutoffs to `[-L, L]` of the single
dilations on the even Paley–Wiener band of width `Y`. -/
theorem tsum_ratSharpMass (f : BruhatCompactSupport Iq) {L Y : ℝ} (hL : 0 < L) (hY : 0 < Y) :
    ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y) =
      ∫ h, ratFold f h * realPWSharpTrace Y 0 0 le_rfl h L := by
  rw [tsum_ratProjectedDiagonal, ratSharpMass_eq f 1 hL hY, ratSharpMass_eq f ratMinusOne hL hY]
  have h1 : eq (1 : Hq).val.val = 1 := by simp
  have hm : eq ratMinusOne.val.val = -1 := by simp [ratMinusOne]
  rw [h1, hm]
  obtain ⟨i1, e1⟩ := integral_Ioc_integral_sinc_swap (continuous_ratProfile f)
    (hasCompactSupport_ratProfile f) 1 Y L
  obtain ⟨i2, e2⟩ := integral_Ioc_integral_sinc_swap (continuous_ratProfile f)
    (hasCompactSupport_ratProfile f) (-1) Y L
  rw [e1, e2, integral_eq_integral_Ioi_add_neg i1, integral_eq_integral_Ioi_add_neg i2,
    ← integral_add (μ := volume.restrict (Ioi (0 : ℝ))) ?_ ?_]
  · have hR : ∫ h, ratFold f h * realPWSharpTrace Y 0 0 le_rfl h L =
        ∫ h in Ioi 0, ratFold f h * realPWSharpTrace Y 0 0 le_rfl h L :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun h hh ↦ by
        simp only [ratFold, indicator_of_notMem hh, zero_mul]).symm
    rw [hR]
    exact setIntegral_congr_fun measurableSet_Ioi fun h (hh : (0 : ℝ) < h) ↦
      ratFold_pointwise f hY hL.le hh
  · exact (i1.add i1.comp_neg).integrableOn
  · exact (i2.add i2.comp_neg).integrableOn

end SumIdentity

section Consequences

local notation "eq" => ratRealCoordEquiv
local notation "Cq" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "classAtq(" g ")" => (QuotientGroup.mk (sIdeleInsertion ℚ Sq g) : Cq)
local notation "volume₁" => ((sLocalNormOneQuotientMeasure ℚ Sq) univ).toReal
local notation "archTest" => ((w : InfinitePlace ℚ) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : Sq) → BruhatCompactSupport (v.val.adicCompletion ℚ)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure ℚ v
    ((HeightOneSpectrum.adicCompletionIntegers ℚ v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace ℚ, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : Sq, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))
local notation "μ₀" => realPWIntervalMeasure 0 0
local notation "V₀(" Y ")" => RealPWBand.space Y (volume_le_realPWIntervalMeasure 0 0 le_rfl)
local notation "ev(" Y ")" => RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure 0 0 le_rfl)

/-- The folded test written as a quotient of continuous functions by `max x a`. -/
theorem ratFold_eq_max (f : BruhatCompactSupport Iq) {a b : ℝ}
    (h : ∀ s, ratLift f.val s ≠ 0 → a ≤ |s| ∧ |s| ≤ b) (x : ℝ) :
    ratFold f x = (ratLift f.val (max x 0) + ratLift f.val (-max x 0)) / (max x a : ℝ) := by
  have h0 (s : ℝ) (hs : |s| < a) : ratLift f.val s = 0 := by
    by_contra hne
    exact (h s hne).1.not_gt hs
  rcases le_or_gt x 0 with hx | hx
  · rw [ratFold, indicator_of_notMem (show x ∉ Ioi 0 from not_lt.2 hx), max_eq_right hx, neg_zero,
      ratLift_zero, add_zero, zero_div]
  · rw [ratFold, indicator_of_mem (show x ∈ Ioi 0 from hx), max_eq_left hx.le]
    rcases le_or_gt a x with hax | hax
    · rw [max_eq_left hax]
    · rw [h0 x (by rwa [abs_of_pos hx]), h0 (-x) (by rwa [abs_neg, abs_of_pos hx])]
      simp

/-- The folded test is continuous. -/
theorem continuous_ratFold (f : BruhatCompactSupport Iq) : Continuous (ratFold f) := by
  obtain ⟨a, b, ha, h⟩ := exists_ratLift_support f
  have hc := continuous_ratLift f
  have hm : Continuous fun x : ℝ ↦ max x 0 := continuous_id.max continuous_const
  refine Continuous.congr ?_ fun x ↦ (ratFold_eq_max f h x).symm
  refine ((hc.comp hm).add (hc.comp hm.neg)).div
    (Complex.continuous_ofReal.comp (continuous_id.max continuous_const)) fun x ↦ ?_
  exact Complex.ofReal_ne_zero.2 (lt_max_of_lt_right ha).ne'

/-- The folded test vanishes outside an interval `[a, b]` with `0 < a`. -/
theorem exists_ratFold_support (f : BruhatCompactSupport Iq) :
    ∃ a b : ℝ, 0 < a ∧ ∀ g ∉ Icc a b, ratFold f g = 0 := by
  obtain ⟨a, b, ha, h⟩ := exists_ratLift_support f
  have h0 (s : ℝ) (hs : ¬ (a ≤ |s| ∧ |s| ≤ b)) : ratLift f.val s = 0 := by
    by_contra hne
    exact hs (h s hne)
  refine ⟨a, b, ha, fun g hg ↦ ?_⟩
  rcases le_or_gt g 0 with hx | hx
  · exact indicator_of_notMem (show g ∉ Ioi 0 from not_lt.2 hx) _
  · rw [ratFold, indicator_of_mem (show g ∈ Ioi 0 from hx)]
    have hn : ¬ (a ≤ |g| ∧ |g| ≤ b) := by rwa [abs_of_pos hx]
    rw [h0 g hn, h0 (-g) (by rwa [abs_neg]), add_zero, zero_div]

/-- The S-integers of `ℚ` with no finite place have trivial Picard group. -/
theorem ratPic_subsingleton :
    Subsingleton (CommRing.Pic ((Sq : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)) := by
  rw [Finset.coe_empty, IsDedekindDomain.integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- No prime of `ℚ` divides its different, which is the unit ideal. -/
theorem ratRamified (v : HeightOneSpectrum (𝓞 ℚ)) (hv : differentIdeal ℤ (𝓞 ℚ) ≤ v.asIdeal) :
    v ∈ Sq := by
  have hd : differentIdeal ℤ (𝓞 ℚ) = 1 := by
    rw [Ideal.one_eq_top, ← Ideal.absNorm_eq_one_iff, NumberField.absNorm_differentIdeal ℚ (𝓞 ℚ),
      NumberField.discr_rat]
    rfl
  rw [hd, Ideal.one_eq_top, top_le_iff] at hv
  exact absurd hv v.isPrime.ne_top

/-- Paper: §12.4, pp. 514–519, for `ℚ` with no finite place.
Reconstruction: the sharp cutoff to `[-L, L]` of the action of the folded test on the even
Paley–Wiener band of width `Y` is nuclear, and its trace is the sum over the S-units of the
sharp orbital masses at radius `L Y`. -/
theorem exists_ratCutoff_nuclear (f : BruhatCompactSupport Iq) {L Y : ℝ} (hL : 0 < L)
    (hY : 0 < Y) :
    ∃ T : nuclearEndomorphisms V₀(Y),
      (∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev(Y) (g⁻¹ * x) v)) ∧
        T.val v = (V₀(Y)).orthogonalProjectionOnto r) ∧
      hilbertTrace T = ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y) := by
  obtain ⟨a, b, ha, hsupp⟩ := exists_ratFold_support f
  obtain ⟨T, hT1, hT2⟩ := exists_realPWTestCutoff_nuclear Y 0 0 le_rfl hY le_rfl ha
    (ratFold f) (continuous_ratFold f) hsupp L
  exact ⟨T, hT1, hT2.trans (tsum_ratSharpMass f hL hY).symm⟩

/-- At `h = 1` the folded test is the sum of the test over the S-units. -/
theorem ratFold_one (f : BruhatCompactSupport Iq) :
    ratFold f 1 = f.val 1 + f.val ratMinusOne.val := by
  have h1 : ratUnit 1 = 1 := by
    rw [← ratUnit_eq 1]
    simp
  have hm : ratUnit (-1) = ratMinusOne.val := by
    rw [← ratUnit_eq ratMinusOne.val]
    simp [ratMinusOne]
  rw [ratFold, indicator_of_mem (show (1 : ℝ) ∈ Ioi 0 from one_pos), ratLift_of_ne one_ne_zero,
    ratLift_of_ne (by norm_num), h1, hm]
  simp

/-- If `f` lifts `φ`, the folded test at `1` is `φ(1)`. -/
theorem ratLift_hasSum_one (φ : BruhatCompactSupport Cq) (f : BruhatCompactSupport Iq)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtq(g)))) :
    φ.val 1 = ratFold f 1 := by
  have h := hLift 1
  simp only [mul_one, map_one, QuotientGroup.mk_one] at h
  rw [← h.tsum_eq, tsum_ratProjectedDiagonal, ratFold_one]
  rfl

/-- Paper: Theorem 12.4.1.1, p. 514, for `ℚ` with no finite place.
Reconstruction: for the sharp cutoffs of the folded test on the even Paley–Wiener bands, the
trace minus the logarithmic term tends to the norm-one volume times the principal value at the
real place. The comparison hypothesis of `sLocalTrace_asymptotic_of_sharp_comparison` holds with
difference zero, by `exists_ratCutoff_nuclear`.
Deviation: The operator acts on the even band of the real line, and the trace is not written as
the diagonal integral of a kernel on the S-idele quotient. The limit is joint, as in
`sLocalTraceSharpMass_asymptotic` with `R = L Y`. -/
theorem ratCutoff_trace_asymptotic (φ : BruhatCompactSupport Cq)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iq)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtq(g)))) :
    ∃ T : (L Y : ℝ) → nuclearEndomorphisms V₀(Y),
      (∀ L Y, 0 < L → 0 < Y →
        (∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
          (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
            ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev(Y) (g⁻¹ * x) v)) ∧
          (T L Y).val v = (V₀(Y)).orthogonalProjectionOnto r) ∧
        hilbertTrace (T L Y) = ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y)) ∧
      ∃ (a : archTest) (b : finiteTest),
        (∀ (w : InfinitePlace ℚ) (u : w.Completionˣ), (a w).val u = φ.val (archClass(w) u)) ∧
        (∀ (v : Sq) (u : (v.val.adicCompletion ℚ)ˣ),
          (b v).val u = φ.val (finiteClass(v.val) u)) ∧
        Tendsto (fun p : ℝ × ℝ ↦ hilbertTrace (T p.1 p.2) -
            (volume₁ : ℂ) * φ.val 1 * (Real.log (p.1 * p.2) : ℂ))
          (atTop ×ˢ atTop) (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) := by
  classical
  let T : (L Y : ℝ) → nuclearEndomorphisms V₀(Y) := fun L Y ↦
    if h : 0 < L ∧ 0 < Y then (exists_ratCutoff_nuclear f h.1 h.2).choose else 0
  have hT (L Y : ℝ) (hL : 0 < L) (hY : 0 < Y) :
      (∀ v : V₀(Y), ∃ r : Lp ℂ 2 μ₀,
        (∀ᵐ x ∂μ₀, r x = sharpIntervalMask L x *
          ∫ g, ratFold f g * (((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) * ev(Y) (g⁻¹ * x) v)) ∧
        (T L Y).val v = (V₀(Y)).orthogonalProjectionOnto r) ∧
      hilbertTrace (T L Y) = ∑' ξ : Hq, sLocalTraceSharpMass f ξ (L * Y) := by
    have hT' : T L Y = (exists_ratCutoff_nuclear f hL hY).choose :=
      dite_eq_left ⟨hL, hY⟩
    rw [hT']
    exact (exists_ratCutoff_nuclear f hL hY).choose_spec
  refine ⟨T, hT, ?_⟩
  obtain ⟨a, b, M, ha, hb, hsum, hlim⟩ := sLocalTraceSharpMass_asymptotic (F := ℚ) (S := Sq) φ
    ratPic_subsingleton ratRamified hOutside f hLift
  refine ⟨a, b, ha, hb, ?_⟩
  have hp : Tendsto (fun p : ℝ × ℝ ↦ p.1 * p.2) (atTop ×ˢ atTop) atTop :=
    tendsto_fst.atTop_mul_atTop₀ tendsto_snd
  refine (hlim.comp hp).congr' ?_
  filter_upwards [tendsto_fst.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_snd.eventually (eventually_gt_atTop (0 : ℝ)), hp.eventually hsum] with p h1 h2 hs
  simp only [Function.comp_apply]
  rw [(hT p.1 p.2 h1 h2).2, hs.tsum_eq]

/-- Reconstruction: for `ℚ` with no finite place, the limit of the real-place model fixes the
constants of `sLocalTraceSharpMass_asymptotic`. The norm-one volume is one as soon as some lift
has `φ(1) ≠ 0`, and the volume times the real principal value is
`φ(1) (log 2π + γ) + ∫ (ψ g - φ(1) m(g)) ρ(g) dg`, where `ψ` is the folded test, `m` is the
comparison profile `logTermProfile` and `ρ` is `realTermDensity`.
Deviation: The folded test is assumed Lipschitz at `1`. -/
theorem ratPrincipalValue_eq (φ : BruhatCompactSupport Cq)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits ℚ Sq) (c : Cq),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iq)
    (hLift : ∀ g : Iq, HasSum (fun ξ : Hq ↦ f.val (ξ.val * g)) (φ.val (classAtq(g))))
    {K : ℝ} (hK : ∀ g, ‖ratFold f g - ratFold f 1‖ ≤ K * |g - 1|) :
    ∃ (a : archTest) (b : finiteTest),
      (∀ (w : InfinitePlace ℚ) (u : w.Completionˣ), (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : Sq) (u : (v.val.adicCompletion ℚ)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      ((volume₁ : ℂ) - 1) * φ.val 1 = 0 ∧
      (volume₁ : ℂ) * principalValues(a, b) =
        φ.val 1 * ((Real.log (2 * π) + Real.eulerMascheroniConstant : ℝ) : ℂ) +
          ∫ g, (ratFold f g - φ.val 1 * ((logTermProfile g : ℝ) : ℂ)) *
            ((realTermDensity g : ℝ) : ℂ) := by
  obtain ⟨a, b, M, ha, hb, hsum, hlim⟩ := sLocalTraceSharpMass_asymptotic (F := ℚ) (S := Sq) φ
    ratPic_subsingleton ratRamified hOutside f hLift
  refine ⟨a, b, ha, hb, ?_⟩
  have hφ := ratLift_hasSum_one φ f hLift
  obtain ⟨a', b', ha', hsupp⟩ := exists_ratFold_support f
  have hmodel := tendsto_integral_realPWSharpTrace_sub_log 1 le_rfl one_pos ha' (ratFold f)
    ((continuous_ratFold f).integrable_of_hasCompactSupport
      (HasCompactSupport.intro isCompact_Icc hsupp)) hsupp (norm_sub_mul_logTermProfile_le hK)
  rw [← hφ, sincLogConstant_div_pi] at hmodel
  generalize hCdef : φ.val 1 * ((Real.eulerMascheroniConstant : ℝ) : ℂ) +
    ∫ g, (ratFold f g - φ.val 1 * ((logTermProfile g : ℝ) : ℂ)) * ((realTermDensity g : ℝ) : ℂ) =
      C at hmodel
  generalize hPdef : (volume₁ : ℂ) * principalValues(a, b) = P at hlim ⊢
  have hML : ∀ᶠ L in atTop, M L = ∫ h, ratFold f h * realPWSharpTrace 1 0 0 le_rfl h L := by
    filter_upwards [hsum, eventually_gt_atTop (0 : ℝ)] with L hs hL
    rw [← hs.tsum_eq, ← tsum_ratSharpMass f hL one_pos, mul_one]
  have hD : Tendsto (fun L : ℝ ↦ ((volume₁ : ℂ) - 1) * φ.val 1 * (Real.log L : ℂ)) atTop
      (𝓝 (C - P + φ.val 1 * (Real.log (2 * π) : ℂ))) := by
    refine ((hmodel.sub hlim).add_const (φ.val 1 * (Real.log (2 * π) : ℂ))).congr' ?_
    filter_upwards [hML, eventually_gt_atTop (0 : ℝ)] with L h hL
    rw [h, mul_one, Real.log_mul (by positivity) hL.ne']
    push_cast
    ring
  have hc : ((volume₁ : ℂ) - 1) * φ.val 1 = 0 := by
    by_contra hc
    have hlog : Tendsto (fun L : ℝ ↦ (Real.log L : ℂ)) atTop
        (𝓝 ((((volume₁ : ℂ) - 1) * φ.val 1)⁻¹ * (C - P + φ.val 1 * (Real.log (2 * π) : ℂ)))) :=
      (hD.const_mul _).congr fun L ↦ by rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    have hre := (Complex.continuous_re.tendsto _).comp hlog
    simp only [Function.comp_def, Complex.ofReal_re] at hre
    exact not_tendsto_nhds_of_tendsto_atTop Real.tendsto_log_atTop _ hre
  refine ⟨hc, ?_⟩
  rw [hc] at hD
  simp only [zero_mul] at hD
  have h0 := tendsto_nhds_unique tendsto_const_nhds hD
  rw [← hCdef] at h0
  push_cast
  linear_combination h0

end Consequences

end RiemannMasullo.Isolated
