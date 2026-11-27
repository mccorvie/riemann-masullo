module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.External.TauCeti.MeasureTheory.Function.Lp.Norm
import Mathlib.MeasureTheory.Measure.Haar.DistribChar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Tactic

/-!
# Fourier transform on primitive p-adic angular shells

A multiplicative angular character of conductor exponent n on the norm-one shell
transforms onto the single sphere of radius p^n, with the inverse angular character.
This is the local finite-place calculation for the rational Paley–Wiener band in
Theorem 12.4.1.1, pp. 515–517.
-/

@[expose] public noncomputable section

open MeasureTheory Set Multiplicative
open scoped Classical Pointwise NNReal ENNReal

namespace RiemannMasullo.PadicConductor

variable (p : ℕ) [Fact p.Prime]
local instance : MeasurableSpace ℚ_[p] := borel _
local instance : BorelSpace ℚ_[p] := ⟨rfl⟩

private theorem standardCharacter_add (x y : ℚ_[p]) :
    padicStandardCharacter p (x+y) = padicStandardCharacter p x * padicStandardCharacter p y := by
  obtain ⟨e, he⟩ := exists_padicPontryaginDualEquiv p
  have h := map_mul (e (ofAdd (1 : ℚ_[p]))) (ofAdd x) (ofAdd y)
  change e (ofAdd (1 : ℚ_[p])) (ofAdd (x+y)) =
    e (ofAdd (1 : ℚ_[p])) (ofAdd x) * e (ofAdd (1 : ℚ_[p])) (ofAdd y) at h
  simpa only [he, one_mul] using h

private theorem standardCharacter_eq_one_iff (y : ℚ_[p]) :
    padicStandardCharacter p y = 1 ↔ ‖y‖ ≤ 1 := by
  constructor
  · intro hy
    obtain ⟨e, he⟩ := exists_padicPontryaginDualEquiv p
    let g (z : ℤ_[p]) := e (ofAdd y) (ofAdd (z : ℚ_[p]))
    have hg : Continuous g := (e (ofAdd y)).continuous.comp continuous_subtype_val
    have hgi (i : ℤ) : g (i : ℤ_[p]) = 1 := by
      have hi : ofAdd ((i : ℤ_[p]) : ℚ_[p]) = (ofAdd (1 : ℚ_[p])) ^ i := by
        apply Multiplicative.toAdd.injective
        simp
      change e (ofAdd y) (ofAdd ((i : ℤ_[p]) : ℚ_[p])) = 1
      rw [hi, map_zpow, he, mul_one, hy, one_zpow]
    have hgc : g = fun _ ↦ 1 :=
      PadicInt.denseRange_intCast.equalizer hg continuous_const (funext hgi)
    let K := Metric.closedBall (0 : ℚ_[p]) 1
    let f := K.indicator (fun _ ↦ (1 : ℂ))
    have hTf : tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) f y = 1 := by
      let μ := padicTamagawaMeasure p
      have hK : MeasurableSet K := Metric.isClosed_closedBall.measurableSet
      have hμ : μ K = 1 := (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).2.2
      change (∫ x, f x * star (padicStandardCharacter p (x*y) : ℂ) ∂μ) = 1
      have heq (x : ℚ_[p]) : f x * star (padicStandardCharacter p (x*y) : ℂ) =
          K.indicator (fun t ↦ star (padicStandardCharacter p (t*y) : ℂ)) x := by
        by_cases hx : x ∈ K <;> simp [f, hx]
      simp_rw [heq]
      rw [integral_indicator hK]
      calc
        _ = ∫ _ in K, (1:ℂ) ∂μ := by
          apply setIntegral_congr_fun hK
          intro x hx
          have h := congrFun hgc (⟨x, by simpa [K, dist_zero_right] using hx⟩ : ℤ_[p])
          change e (ofAdd y) (ofAdd x) = 1 at h
          rw [he, mul_comm] at h
          simp [h]
        _ = 1 := by simp [measureReal_def, hμ]
    have hformula := congrFun (padicTamagawaFourier_scaledIntegers p 0) y
    have hformula' : tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) f y = f y := by
      simpa [f, K, Set.image_id'] using hformula
    by_contra hn
    have hyK : y ∉ K := by simpa [K, dist_zero_right] using hn
    have hf0 : f y = 0 := Set.indicator_of_notMem hyK _
    exact one_ne_zero (hTf.symm.trans (hformula'.trans hf0))
  · intro hy
    have hn : (-y.valuation).toNat = 0 := by
      rcases eq_or_ne y 0 with rfl | h0
      · simp [Padic.valuation_zero]
      · have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
        rw [Padic.norm_eq_zpow_neg_valuation h0, zpow_le_one_iff_right₀ hp] at hy
        omega
    suffices h : ∀ (n : ℕ) (a : ℤ_[p]), n = 0 →
        Circle.exp (-(2 * Real.pi * ((PadicInt.toZModPow n a).val : ℝ) / (p : ℝ)^n)) = 1 from
      h _ _ hn
    intro n a hn
    subst n
    have hz : PadicInt.toZModPow 0 a = 0 := by
      change (_ : ZMod 1) = _
      exact Subsingleton.elim _ _
    have hv : (PadicInt.toZModPow 0 a).val = 0 := by
      rw [show (PadicInt.toZModPow 0 a : ZMod 1) = 0 from hz, ZMod.val_zero]
    rw [hv]
    simp

/-- A norm-one p-adic multiplier preserves the additive measure normalized on the integer ball. -/
private theorem padicTamagawaMeasure_measurePreserving_mul {u : ℚ_[p]} (hu : ‖u‖ = 1) :
    MeasurePreserving (fun x : ℚ_[p] ↦ u * x) (padicTamagawaMeasure p) (padicTamagawaMeasure p) := by
  have hu0 : u ≠ 0 := norm_pos_iff.mp (hu.symm ▸ zero_lt_one)
  let e := Homeomorph.mulLeft₀ u hu0
  let a : ℚ_[p] ≃+ ℚ_[p] := { e.toEquiv with map_add' := mul_add u }
  let μ := padicTamagawaMeasure p
  let B := Metric.closedBall (0 : ℚ_[p]) 1
  have hμ : μ.IsAddHaarMeasure ∧ μ.Regular ∧ μ B = 1 :=
    Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  let : μ.IsAddHaarMeasure := hμ.1
  let : μ.Regular := hμ.2.1
  have hB : e ⁻¹' B = B := by
    ext x
    change u * x ∈ Metric.closedBall (0 : ℚ_[p]) 1 ↔ x ∈ Metric.closedBall (0 : ℚ_[p]) 1
    simp only [Metric.mem_closedBall, dist_zero_right, norm_mul, hu, one_mul]
  refine ⟨e.continuous.measurable, (padicTamagawaMeasure_existsUnique p).unique ?_ hμ⟩
  refine ⟨a.isAddHaarMeasure_map μ e.continuous e.symm.continuous, Measure.Regular.map e, ?_⟩
  change μ.map e B = 1
  rw [Measure.map_apply e.continuous.measurable Metric.isClosed_closedBall.measurableSet, hB]
  exact hμ.2.2

section AngularTest

variable (χ : ℚ_[p]ˣ →* Circle)

private theorem angular_ne_zero {x : ℚ_[p]} (hx : ‖x‖ = 1) : x ≠ 0 := by
  rintro rfl
  simp at hx

/-- Extend the angular character on the norm-one shell by zero. -/
def padicAngularTest (x : ℚ_[p]) : ℂ :=
  if hx : ‖x‖ = 1 then (χ (Units.mk0 x (norm_pos_iff.mp (hx.symm ▸ zero_lt_one))) : ℂ)
  else 0

private theorem padicAngularTest_mul (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1) (x : ℚ_[p]) :
    padicAngularTest p χ (u * x) = (χ u : ℂ) * padicAngularTest p χ x := by
  have hn : ‖(u : ℚ_[p]) * x‖ = ‖x‖ := by rw [norm_mul, hu, one_mul]
  by_cases hx : ‖x‖ = 1
  · have he : Units.mk0 ((u : ℚ_[p]) * x) (angular_ne_zero p (hn.trans hx)) =
        u * Units.mk0 x (angular_ne_zero p hx) := Units.ext rfl
    simp only [padicAngularTest, dite_eq_left hx, dite_eq_left (hn.trans hx), he, map_mul,
      Circle.coe_mul]
  · simp [padicAngularTest, hn, hx]

private theorem padicAngularTest_add {n : ℕ} (hn : 0 < n)
    (hχ : ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) → χ u = 1)
    (x h : ℚ_[p]) (hh : ‖h‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    padicAngularTest p χ (x + h) = padicAngularTest p χ x := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hs : ‖h‖ < 1 := hh.trans_lt (zpow_lt_one_of_neg₀ hp (by omega))
  have stable (a b : ℚ_[p]) (ha : ‖a‖ = 1) (hb : ‖b‖ < 1) : ‖a + b‖ = 1 := by
    have hba : ‖b‖ < ‖a‖ := ha ▸ hb
    rw [Padic.add_eq_max_of_ne hba.ne', max_eq_left hba.le, ha]
  by_cases hx : ‖x‖ = 1
  · have hx0 := angular_ne_zero p hx
    have hxh := stable x h hx hs
    let u := Units.mk0 ((x + h) / x) (div_ne_zero (angular_ne_zero p hxh) hx0)
    have hu : ‖(u : ℚ_[p])‖ = 1 := by change ‖(x + h) / x‖ = 1; rw [norm_div, hxh, hx, div_one]
    have hd : (u : ℚ_[p]) - 1 = h / x := by change (x + h) / x - 1 = h / x; field_simp; ring
    have hc := hχ u (by rw [hd, norm_div, hx, div_one]; exact hh)
    have hm : (u : ℚ_[p]) * x = x + h := div_mul_cancel₀ _ hx0
    simpa only [hm, hc, Circle.coe_one, one_mul] using padicAngularTest_mul p χ u hu x
  · have hx' : ‖x + h‖ ≠ 1 := fun hxh ↦ hx (by
      simpa using stable (x + h) (-h) hxh (by simpa using hs))
    simp [padicAngularTest, hx, hx']

private theorem padicAngularTest_integrable (hχ : Continuous χ) :
    Integrable (padicAngularTest p χ) (padicTamagawaMeasure p) := by
  let S : Set ℚ_[p] := {x | ‖x‖ = 1}
  have hS : S = Metric.sphere 0 1 := by ext x; simp [S]
  have hc : IsClopen S := hS ▸ IsUltrametricDist.isClopen_sphere _ one_ne_zero
  let g (x : S) := Units.mk0 x.val (angular_ne_zero p x.property)
  have hg : Continuous g := Units.isEmbedding_val₀.isInducing.continuous_iff.mpr continuous_subtype_val
  have hOn : ContinuousOn (padicAngularTest p χ) S := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp (hχ.comp hg)).congr (fun x ↦ by
      change (χ (g x) : ℂ) = padicAngularTest p χ x
      unfold padicAngularTest
      rw [dite_eq_left (show ‖(x : ℚ_[p])‖ = 1 from x.property)])
  have hOff : ContinuousOn (padicAngularTest p χ) Sᶜ :=
    (continuousOn_const : ContinuousOn (fun _ : ℚ_[p] ↦ (0 : ℂ)) Sᶜ).congr
      (fun x hx ↦ by simp [padicAngularTest, show ‖x‖ ≠ 1 from hx])
  have hcont : Continuous (padicAngularTest p χ) := by
    simpa using hOn.union_of_isOpen hOff hc.isOpen hc.isClosed.isOpen_compl
  let : (padicTamagawaMeasure p).IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  apply hcont.integrable_of_hasCompactSupport
  refine HasCompactSupport.intro (show IsCompact S from hS ▸ isCompact_sphere _ _) ?_
  intro x hx
  simp [padicAngularTest, show ‖x‖ ≠ 1 from hx]

end AngularTest

private theorem star_circle_ne_one {z : Circle} (hz : z ≠ 1) : star (z : ℂ) ≠ 1 := by
  intro h
  apply hz
  apply Subtype.ext
  have h' := congrArg star h
  change star (star (z : ℂ)) = star (1:ℂ) at h'
  simpa only [star_star, star_one, Circle.coe_one] using h'

private theorem eq_zero_of_mul_fixed {a x : ℂ} (ha : a ≠ 1) (h : x = a*x) : x = 0 := by
  have he : (1-a)*x = 0 := by rw [sub_mul, one_mul, sub_eq_zero]; exact h
  exact (mul_eq_zero.mp he).resolve_left (sub_ne_zero.mpr ha.symm)

/-- A nontrivial phase under an additive period forces a Fourier integral to vanish. -/
private theorem fourier_eq_zero_of_period {f : ℚ_[p] → ℂ} {y h : ℚ_[p]}
    (hplus : ∀ u v, padicStandardCharacter p (u+v) =
      padicStandardCharacter p u * padicStandardCharacter p v)
    (hperiod : ∀ x, f (x+h) = f x) (hphase : padicStandardCharacter p (h*y) ≠ 1) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) f y = 0 := by
  have : (padicTamagawaMeasure p).IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  let k (x : ℚ_[p]) := f x * star (padicStandardCharacter p (x*y) : ℂ)
  let a := star (padicStandardCharacter p (h*y) : ℂ)
  have ha : a ≠ 1 := star_circle_ne_one hphase
  have he (x : ℚ_[p]) : k (x+h) = a * k x := by
    change f (x+h) * star (padicStandardCharacter p ((x+h)*y) : ℂ) =
      a * (f x * star (padicStandardCharacter p (x*y) : ℂ))
    rw [hperiod, add_mul, hplus, Circle.coe_mul, star_mul']
    change _ = star (padicStandardCharacter p (h*y) : ℂ) * _
    ring
  have hf := integral_add_right_eq_self (μ := padicTamagawaMeasure p) k h
  simp_rw [he, integral_const_mul] at hf
  exact eq_zero_of_mul_fixed ha hf.symm

/-- Unit multiplication cancels a nontrivial angular type whenever the additive
phase is invariant on its support. -/
private theorem fourier_eq_zero_of_unit_covariance {f : ℚ_[p] → ℂ} {y u : ℚ_[p]} {c : ℂ}
    (hu : u ≠ 0) (hpres : MeasurePreserving (fun x : ℚ_[p] ↦ u*x)
      (padicTamagawaMeasure p) (padicTamagawaMeasure p))
    (hc : c ≠ 1) (hcov : ∀ x, f (u*x) = c * f x)
    (hphase : ∀ x, f x ≠ 0 → padicStandardCharacter p (u*x*y) = padicStandardCharacter p (x*y)) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) f y = 0 := by
  let k (x : ℚ_[p]) := f x * star (padicStandardCharacter p (x*y) : ℂ)
  have he (x : ℚ_[p]) : k (u*x) = c * k x := by
    change f (u*x) * star (padicStandardCharacter p (u*x*y) : ℂ) =
      c * (f x * star (padicStandardCharacter p (x*y) : ℂ))
    by_cases hx : f x = 0
    · simp only [hcov, hx, mul_zero, zero_mul]
    · rw [hcov, hphase x hx, mul_assoc]
  have hm : MeasurableEmbedding (fun x : ℚ_[p] ↦ u*x) :=
    (Homeomorph.mulLeft₀ u hu).measurableEmbedding
  have hf := hpres.integral_comp hm k
  simp_rw [he, integral_const_mul] at hf
  exact eq_zero_of_mul_fixed hc hf.symm

/-- Under the additive period and primitive unit covariance of conductor `n`,
the actual p-adic Fourier transform vanishes off the conductor sphere. -/
private theorem fourier_eq_zero_off_conductor {f : ℚ_[p] → ℂ} {n : ℕ}
    (hplus : ∀ u v, padicStandardCharacter p (u+v) =
      padicStandardCharacter p u * padicStandardCharacter p v)
    (hker : ∀ x, padicStandardCharacter p x = 1 ↔ ‖x‖ ≤ 1)
    (hsupp : ∀ x, f x ≠ 0 → ‖x‖ = 1)
    (hperiod : ∀ x, f (x+(p : ℚ_[p])^n) = f x)
    {u : ℚ_[p]} (hu : ‖u‖ = 1) (hnear : ‖u-1‖ ≤ (p:ℝ)^(1-(n:ℤ)))
    (hpres : MeasurePreserving (fun x : ℚ_[p] ↦ u*x)
      (padicTamagawaMeasure p) (padicTamagawaMeasure p))
    {c : ℂ} (hc : c ≠ 1) (hcov : ∀ x, f (u*x)=c*f x)
    {y : ℚ_[p]} (hy : ‖y‖ ≠ (p:ℝ)^n) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) f y = 0 := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : 0 < (p:ℝ) := zero_lt_one.trans hp
  rcases lt_or_gt_of_ne hy with hy' | hy'
  · have hyb : ‖y‖ ≤ (p:ℝ)^((n:ℤ)-1) := by
      by_cases h0 : y = 0
      · subst y
        rw [norm_zero]
        exact (zpow_pos hp0 _).le
      · rw [Padic.norm_eq_zpow_neg_valuation h0] at hy' ⊢
        have hh : -(y.valuation) < (n:ℤ) :=
          (zpow_lt_zpow_iff_right₀ hp).mp (by simpa only [zpow_natCast] using hy')
        exact (zpow_le_zpow_iff_right₀ hp).2 (by omega)
    have hun : u ≠ 0 := by rintro rfl; simp at hu
    apply fourier_eq_zero_of_unit_covariance p hun hpres hc hcov
    intro x hx
    have hb : padicStandardCharacter p ((u-1)*x*y) = 1 := by
      apply (hker _).2
      rw [norm_mul, norm_mul, hsupp x hx, mul_one]
      calc
        _ ≤ (p:ℝ)^(1-(n:ℤ)) * (p:ℝ)^((n:ℤ)-1) := mul_le_mul hnear hyb (norm_nonneg _) (zpow_pos hp0 _).le
        _ = 1 := by rw [← zpow_add₀ hp0.ne', show 1-(n:ℤ)+((n:ℤ)-1)=0 by omega, zpow_zero]
    rw [show u*x*y = x*y+((u-1)*x*y) by ring, hplus, hb, mul_one]
  · apply fourier_eq_zero_of_period p hplus hperiod
    intro h
    have hb := (hker _).1 h
    rw [norm_mul, Padic.norm_p_pow, zpow_neg, zpow_natCast] at hb
    have hpN := pow_pos hp0 n
    have hf : ((p:ℝ)^n)⁻¹ * (p:ℝ)^n = 1 := inv_mul_cancel₀ hpN.ne'
    exact (not_lt_of_ge hb) (hf ▸ mul_lt_mul_of_pos_left hy' (inv_pos.mpr hpN))

private theorem fourier_mul_unit {f : ℚ_[p] → ℂ} (u : ℚ_[p]ˣ)
    (hpres : MeasurePreserving (fun x : ℚ_[p] ↦ (u : ℚ_[p])*x)
      (padicTamagawaMeasure p) (padicTamagawaMeasure p))
    (c : Circle) (hcov : ∀ x, f ((u : ℚ_[p])*x) = (c : ℂ)*f x) (y : ℚ_[p]) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) f ((u : ℚ_[p])*y) =
      ((c⁻¹ : Circle) : ℂ) * tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) f y := by
  let k (x : ℚ_[p]) := f x * star (padicStandardCharacter p (x*y) : ℂ)
  have hi := hpres.integral_comp (measurableEmbedding_mulLeft₀ u.ne_zero) k
  have he (x : ℚ_[p]) : k ((u : ℚ_[p])*x) =
      (c : ℂ) * (f x * star (padicStandardCharacter p (x*((u : ℚ_[p])*y)) : ℂ)) := by
    have hx : (u : ℚ_[p])*x*y = x*((u : ℚ_[p])*y) := by ac_rfl
    simp only [k, hcov, hx, mul_assoc]
  simp_rw [he, integral_const_mul] at hi
  change (∫ x, f x * star (padicStandardCharacter p (x*((u : ℚ_[p])*y)) : ℂ) ∂padicTamagawaMeasure p) =
    ((c⁻¹ : Circle) : ℂ) * ∫ x, k x ∂padicTamagawaMeasure p
  rw [← hi, ← mul_assoc, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one, one_mul]

local notation "ZpBall" => Metric.closedBall (0 : ℚ_[p]) 1

/-- The reciprocal dilation pushes the normalized Haar measure forward by the mass
of the dilated integer ball. -/
private theorem map_prime_neg_zpow (k : ℤ) :
    Measure.map (fun x : ℚ_[p] ↦ (p : ℚ_[p]) ^ (-k) * x) (padicTamagawaMeasure p) =
      (p : ℝ≥0) ^ (-k) • padicTamagawaMeasure p := by
  let μ := padicTamagawaMeasure p
  obtain ⟨hhaar, hreg, hone⟩ := Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists
  change μ.IsAddHaarMeasure at hhaar
  change μ.Regular at hreg
  change μ ZpBall = 1 at hone
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let a := (p : ℚ_[p]) ^ k
  have ha : a ≠ 0 := zpow_ne_zero _ hp
  let u := Units.mk0 a ha
  let B := (a * ·) '' ZpBall
  have hB : MeasurableSet B := by
    change MeasurableSet ((a • ·) '' ZpBall)
    rw [Metric.smul_image_closedBall ha]
    exact Metric.isClosed_closedBall.measurableSet
  have hz : (0 : ℚ_[p]) ∈ (((p : ℚ_[p]) ^ (-k) * ·) '' ZpBall) :=
    ⟨0, by simp, mul_zero _⟩
  have hf := congrFun (padicTamagawaFourier_scaledIntegers p k) 0
  change (∫ x, B.indicator (fun _ ↦ (1 : ℂ)) x * star (padicStandardCharacter p (x*0) : ℂ) ∂μ) =
    ((p : ℝ) ^ (-k) : ℂ) * _ at hf
  simp only [mul_zero, padicStandardCharacter_zero, Circle.coe_one, star_one, mul_one,
    Set.indicator_of_mem hz, integral_indicator hB, setIntegral_const, Complex.real_smul] at hf
  have hmass : μ.real B = (p : ℝ) ^ (-k) := by
    apply Complex.ofReal_injective
    simpa only [Complex.ofReal_zpow, Complex.ofReal_natCast, mul_one] using hf
  have hchar := distribHaarChar_mul μ u ZpBall
  rw [hone, mul_one] at hchar
  change (↑(distribHaarChar ℚ_[p] u) : ℝ≥0∞) = μ B at hchar
  have he : distribHaarChar ℚ_[p] u = (p : ℝ≥0) ^ (-k) := by
    apply NNReal.eq
    have hr := congrArg ENNReal.toReal hchar
    rw [ENNReal.coe_toReal, ← measureReal_def, hmass] at hr
    simpa only [NNReal.coe_zpow, NNReal.coe_natCast] using hr
  rw [zpow_neg (p : ℚ_[p])]
  change DomMulAct.mk u • μ = _
  rw [Measure.isAddLeftInvariant_eq_smul_of_regular (DomMulAct.mk u • μ) μ,
    addHaarScalarFactor_smul_eq_distribHaarChar, he]

/-- Fourier dilation on arbitrary p-adic functions; no integrability premise is
needed because the change of variables is a measurable equivalence. -/
private theorem fourier_prime_dilate (k : ℤ) (ψ : ℚ_[p] → Circle) (f : ℚ_[p] → ℂ) (y : ℚ_[p]) :
    tamagawaFourier (padicTamagawaMeasure p) ψ (fun x ↦ f ((p : ℚ_[p]) ^ (-k) * x)) y =
      ((p : ℝ) ^ (-k) : ℂ) * tamagawaFourier (padicTamagawaMeasure p) ψ f ((p : ℚ_[p]) ^ k * y) := by
  let μ := padicTamagawaMeasure p
  let a := (p : ℚ_[p]) ^ k
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have ha : a ≠ 0 := zpow_ne_zero _ hp
  let g (x : ℚ_[p]) := f x * star (ψ (x * (a*y)) : ℂ)
  have he : MeasurableEmbedding (fun x : ℚ_[p] ↦ (p : ℚ_[p]) ^ (-k) * x) :=
    (Homeomorph.mulLeft₀ _ (zpow_ne_zero (-k) hp)).isClosedEmbedding.measurableEmbedding
  have h := he.integral_map (μ := μ) g
  rw [map_prime_neg_zpow, integral_smul_nnreal_measure] at h
  have hxy (x : ℚ_[p]) : ((p : ℚ_[p]) ^ (-k) * x) * (a*y) = x*y := by
    rw [zpow_neg]
    change (a⁻¹*x)*(a*y) = _
    rw [show (a⁻¹*x)*(a*y) = (a⁻¹*a)*(x*y) by ac_rfl, inv_mul_cancel₀ ha, one_mul]
  change (∫ x, f ((p : ℚ_[p]) ^ (-k) * x) * star (ψ (x*y) : ℂ) ∂μ) =
    ((p : ℝ) ^ (-k) : ℂ) * ∫ x, g x ∂μ
  simpa only [g, hxy, NNReal.smul_def, Complex.real_smul, NNReal.coe_zpow,
    NNReal.coe_natCast, Complex.ofReal_zpow, Complex.ofReal_natCast] using h.symm

local notation "μₚ" => padicTamagawaMeasure p
local notation "Tₚ" => tamagawaFourier μₚ (padicStandardCharacter p)

/-- Plancherel for the actual Tamagawa Fourier integral in its frequency coordinate. -/
private theorem padicFourier_plancherel {f : ℚ_[p] → ℂ} (h₁ : Integrable f μₚ)
    (h₂ : MemLp f 2 μₚ) : MemLp (Tₚ f) 2 μₚ ∧ eLpNorm (Tₚ f) 2 μₚ = eLpNorm f 2 μₚ := by
  let G := Multiplicative ℚ_[p]
  let μ : Measure G := μₚ
  let F : G → ℂ := fun x ↦ f x.toAdd
  let : MeasurableSpace (PontryaginDual G) := borel _
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨e, he, hP⟩ := padicTamagawaMeasure_selfDual p
  have hm : MeasurableEmbedding (e : G → PontryaginDual G) := e.toHomeomorph.measurableEmbedding
  have hcomp : lcaFourier μ F ∘ e = fun x : G ↦ Tₚ f x.toAdd := by
    funext x
    exact (tamagawaFourier_eq_lcaFourier μₚ (padicStandardCharacter p) f x.toAdd (e x)
      (fun y ↦ (he x.toAdd y).trans (congrArg _ (mul_comm _ _)))).symm
  obtain ⟨hmem, hnorm⟩ := hP.2.2 F h₁ h₂
  change MemLp (lcaFourier μ F) 2 (μ.map e) at hmem
  change eLpNorm (lcaFourier μ F) 2 (μ.map e) = eLpNorm F 2 μ at hnorm
  rw [hm.memLp_map_measure_iff, hcomp] at hmem
  rw [hm.eLpNorm_map_measure, hcomp] at hnorm
  exact ⟨hmem, hnorm⟩

private theorem shell_energy (f : ℚ_[p] → ℂ) (r a : ℝ)
    (h : ∀ x, ‖f x‖ = if ‖x‖ = r then a else 0) :
    (∫ x, ‖f x‖ ^ 2 ∂μₚ) = (μₚ).real (Metric.sphere 0 r) * a ^ 2 := by
  classical
  have heq : (fun x ↦ ‖f x‖ ^ 2) = (Metric.sphere (0 : ℚ_[p]) r).indicator (fun _ ↦ a ^ 2) := by
    funext x
    by_cases hx : ‖x‖ = r <;> simp [h, Set.indicator, hx]
  rw [heq, integral_indicator Metric.isClosed_sphere.measurableSet, setIntegral_const, smul_eq_mul]

/-- A unit-modulus input on the unit sphere, with transform of constant modulus `g`
precisely on the conductor sphere, has squared coefficient given by the shell mass ratio. -/
private theorem padicFourier_shell_norm_sq {f : ℚ_[p] → ℂ} {g : ℝ} {n : ℕ} (h₁ : Integrable f μₚ)
    (hf : ∀ x, ‖f x‖ = if ‖x‖ = 1 then 1 else 0)
    (hT : ∀ y, ‖Tₚ f y‖ = if ‖y‖ = (p : ℝ)^n then g else 0) :
    g^2 = (μₚ).real (Metric.sphere 0 1) / (μₚ).real (Metric.sphere 0 ((p : ℝ)^n)) := by
  let : (μₚ).IsAddHaarMeasure := (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  have h₂ : MemLp f 2 μₚ := by
    apply (memLp_two_iff_integrable_sq_norm h₁.aestronglyMeasurable).2
    exact h₁.norm.congr (.of_forall fun x ↦ by by_cases hx : ‖x‖ = 1 <;> simp [hf, hx])
  obtain ⟨hT₂, hP⟩ := padicFourier_plancherel p h₁ h₂
  have hE : (∫ x, ‖Tₚ f x‖ ^ 2 ∂μₚ) = ∫ x, ‖f x‖ ^ 2 ∂μₚ := by
    rw [← hT₂.norm_toLp_sq, ← h₂.norm_toLp_sq, Lp.norm_toLp, Lp.norm_toLp, hP]
  rw [shell_energy p _ _ _ hT, shell_energy p _ _ _ hf, one_pow, mul_one] at hE
  have hU : (μₚ).real (Metric.sphere (0 : ℚ_[p]) 1) ≠ 0 := by
    apply (measureReal_ne_zero_iff (isCompact_sphere (0 : ℚ_[p]) 1).measure_lt_top.ne).2
    exact (IsUltrametricDist.isOpen_sphere (0 : ℚ_[p]) one_ne_zero).measure_ne_zero μₚ
      ⟨1, by simp⟩
  have hS : (μₚ).real (Metric.sphere 0 ((p : ℝ)^n)) ≠ 0 := by
    intro hz
    exact hU (by simpa [hz] using hE.symm)
  exact (eq_div_iff hS).2 ((mul_comm _ _).trans hE)

/-- The primitive shell coefficient with the specified Tamagawa sign and measure. -/
def padicGaussCoefficient (χ : ℚ_[p]ˣ →* Circle) (n : ℕ) : ℂ :=
  Tₚ (padicAngularTest p χ) ((p : ℚ_[p]) ^ (-(n : ℤ)))

private theorem angularFourier_off_conductor (χ : ℚ_[p]ˣ →* Circle) {n : ℕ} (hn : 0 < n)
    (hχ : ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) → χ u = 1)
    (hprim : ∃ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 ∧
      ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (1 - (n : ℤ)) ∧ χ u ≠ 1)
    {y : ℚ_[p]} (hy : ‖y‖ ≠ (p : ℝ) ^ n) : Tₚ (padicAngularTest p χ) y = 0 := by
  obtain ⟨u, hu, hnear, hne⟩ := hprim
  have hsupp (x : ℚ_[p]) (hx : padicAngularTest p χ x ≠ 0) : ‖x‖ = 1 := by
    by_contra h; exact hx (by simp [padicAngularTest, h])
  have hperiod (x : ℚ_[p]) : padicAngularTest p χ (x + (p : ℚ_[p]) ^ n) =
      padicAngularTest p χ x :=
    padicAngularTest_add p χ hn hχ _ _ (Padic.norm_p_pow n).le
  exact fourier_eq_zero_off_conductor p (standardCharacter_add p) (standardCharacter_eq_one_iff p)
    hsupp hperiod hu hnear (padicTamagawaMeasure_measurePreserving_mul p hu)
    (fun h ↦ hne (Subtype.ext (h.trans Circle.coe_one.symm))) (padicAngularTest_mul p χ u hu) hy

/-- Paper: Theorem 12.4.1.1, p. 517. A primitive angular character on valuation
shell `k` has additive Fourier transform zero off the conductor sphere. -/
theorem padicAngularShell_fourier_eq_zero (χ : ℚ_[p]ˣ →* Circle) {n : ℕ} (hn : 0 < n)
    (hχ : ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) → χ u = 1)
    (hprim : ∃ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 ∧
      ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (1 - (n : ℤ)) ∧ χ u ≠ 1)
    (k : ℤ) {y : ℚ_[p]} (hy : ‖y‖ ≠ (p : ℝ) ^ (k + (n : ℤ))) :
    Tₚ (fun x ↦ padicAngularTest p χ ((p : ℚ_[p]) ^ (-k) * x)) y = 0 := by
  rw [fourier_prime_dilate, angularFourier_off_conductor p χ hn hχ hprim, mul_zero]
  have hp : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hnrm : ‖(p : ℚ_[p]) ^ k‖ = (p : ℝ) ^ (-k) := Padic.norm_p_zpow k
  rw [norm_mul, hnrm]
  intro h
  apply hy
  rw [zpow_add₀ hp.ne', zpow_natCast]
  rw [zpow_neg, inv_mul_eq_div, div_eq_iff (zpow_ne_zero _ hp.ne')] at h
  exact h.trans (mul_comm _ _)

/-- On its conductor sphere the shell transform is its Gauss coefficient times
the inverse angular character and the exact additive shell scaling. -/
theorem padicAngularShell_fourier_on_conductor (χ : ℚ_[p]ˣ →* Circle) (n : ℕ) (k : ℤ)
    (u : ℚ_[p]ˣ) (hu : ‖(u : ℚ_[p])‖ = 1) :
    Tₚ (fun x ↦ padicAngularTest p χ ((p : ℚ_[p]) ^ (-k) * x))
        ((p : ℚ_[p]) ^ (-(k + (n : ℤ))) * (u : ℚ_[p])) =
      ((p : ℝ) ^ (-k) : ℂ) * ((χ u)⁻¹ : Circle) * padicGaussCoefficient p χ n := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [fourier_prime_dilate, ← mul_assoc, ← zpow_add₀ hp,
    show k + -(k + (n : ℤ)) = -(n : ℤ) by omega, mul_comm _ (u : ℚ_[p]),
    fourier_mul_unit p u (padicTamagawaMeasure_measurePreserving_mul p hu) (χ u)
      (padicAngularTest_mul p χ u hu), mul_assoc]
  rfl

private theorem conductorSphere_mass (n : ℕ) :
    (μₚ).real (Metric.sphere 0 ((p : ℝ)^n)) =
      (p : ℝ)^n * (μₚ).real (Metric.sphere 0 1) := by
  let d : ℚ_[p] → ℚ_[p] := fun x ↦ (p : ℚ_[p]) ^ (-(-(n : ℤ))) * x
  have hpR : 0 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hmeas : Measurable d := (continuous_const.mul continuous_id).measurable
  have hS : d ⁻¹' Metric.sphere 0 1 = Metric.sphere 0 ((p : ℝ)^n) := by
    ext x
    simp only [Set.mem_preimage, d, neg_neg, zpow_natCast, Metric.mem_sphere, dist_zero_right,
      norm_mul, Padic.norm_p_pow, zpow_neg, inv_mul_eq_div, div_eq_iff (pow_ne_zero n hpR.ne'),
      one_mul]
  have h := map_prime_neg_zpow p (-(n : ℤ))
  change Measure.map d μₚ = _ at h
  rw [← hS, measureReal_def, ← Measure.map_apply hmeas Metric.isClosed_sphere.measurableSet,
    h, smul_apply]
  simp only [neg_neg, zpow_natCast, measureReal_def]
  change (↑((p : ℝ≥0)^n) * μₚ (Metric.sphere 0 1)).toReal =
    (p : ℝ)^n * (μₚ (Metric.sphere 0 1)).toReal
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, NNReal.coe_pow, NNReal.coe_natCast]

private theorem normSphere_exists_unit (k : ℤ) (y : ℚ_[p]) (hy : ‖y‖ = (p : ℝ)^k) :
    ∃ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 ∧ (p : ℚ_[p]) ^ (-k) * (u : ℚ_[p]) = y := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  let a := (p : ℚ_[p]) ^ k * y
  have ha : ‖a‖ = 1 := by
    change ‖(p : ℚ_[p]) ^ k * y‖ = 1
    rw [norm_mul, Padic.norm_p_zpow, hy, zpow_neg, inv_mul_cancel₀ (zpow_ne_zero k hpR)]
  refine ⟨Units.mk0 a (angular_ne_zero p ha), ha, ?_⟩
  change (p : ℚ_[p]) ^ (-k) * ((p : ℚ_[p]) ^ k * y) = y
  rw [zpow_neg, ← mul_assoc, inv_mul_cancel₀ (zpow_ne_zero k hp), one_mul]

/-- The squared modulus of a primitive angular Gauss coefficient for normalized
Tamagawa measure is `p⁻ⁿ`. In particular every point of the conductor sphere is
in the nonzero set of the transform. -/
theorem padicGaussCoefficient_norm_sq (χ : ℚ_[p]ˣ →* Circle) (hcont : Continuous χ)
    {n : ℕ} (hn : 0 < n)
    (hχ : ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) → χ u = 1)
    (hprim : ∃ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 ∧
      ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (1 - (n : ℤ)) ∧ χ u ≠ 1) :
    ‖padicGaussCoefficient p χ n‖ ^ 2 = ((p : ℝ)^n)⁻¹ := by
  have hf (x : ℚ_[p]) : ‖padicAngularTest p χ x‖ = if ‖x‖ = 1 then 1 else 0 := by
    by_cases hx : ‖x‖ = 1 <;> simp [padicAngularTest, hx]
  have hT (y : ℚ_[p]) : ‖Tₚ (padicAngularTest p χ) y‖ =
      if ‖y‖ = (p : ℝ)^n then ‖padicGaussCoefficient p χ n‖ else 0 := by
    by_cases hy : ‖y‖ = (p : ℝ)^n
    · obtain ⟨u, ha, huy⟩ := normSphere_exists_unit p (n : ℤ) y (by rwa [zpow_natCast])
      have he := padicAngularShell_fourier_on_conductor p χ n 0 u ha
      simp only [neg_zero, zpow_zero, one_mul, zero_add, huy] at he
      rw [ite_eq_left hy, he, norm_mul]
      simp
    · rw [ite_eq_right hy, angularFourier_off_conductor p χ hn hχ hprim hy, norm_zero]
  rw [padicFourier_shell_norm_sq p (padicAngularTest_integrable p χ hcont) hf hT,
    conductorSphere_mass]
  let : (μₚ).IsAddHaarMeasure := (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  have hU : (μₚ).real (Metric.sphere (0 : ℚ_[p]) 1) ≠ 0 :=
    (measureReal_ne_zero_iff (isCompact_sphere (0 : ℚ_[p]) 1).measure_lt_top.ne).2
      ((IsUltrametricDist.isOpen_sphere (0 : ℚ_[p]) one_ne_zero).measure_ne_zero μₚ
        ⟨1, by simp⟩)
  rw [div_mul_cancel_right₀ hU]

/-- The nonzero set of the primitive shell's Tamagawa Fourier transform is the
entire conductor sphere, for any spatial valuation `k`. -/
theorem padicAngularShell_fourier_ne_zero_iff (χ : ℚ_[p]ˣ →* Circle) (hcont : Continuous χ)
    {n : ℕ} (hn : 0 < n)
    (hχ : ∀ u : ℚ_[p]ˣ, ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (-(n : ℤ)) → χ u = 1)
    (hprim : ∃ u : ℚ_[p]ˣ, ‖(u : ℚ_[p])‖ = 1 ∧
      ‖(u : ℚ_[p]) - 1‖ ≤ (p : ℝ) ^ (1 - (n : ℤ)) ∧ χ u ≠ 1)
    (k : ℤ) (y : ℚ_[p]) :
    Tₚ (fun x ↦ padicAngularTest p χ ((p : ℚ_[p]) ^ (-k) * x)) y ≠ 0 ↔
      ‖y‖ = (p : ℝ) ^ (k + (n : ℤ)) := by
  constructor
  · intro h
    by_contra hy
    exact h (padicAngularShell_fourier_eq_zero p χ hn hχ hprim k hy)
  · intro hy
    obtain ⟨u, hu, rfl⟩ := normSphere_exists_unit p _ y hy
    have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have hG := padicGaussCoefficient_norm_sq p χ hcont hn hχ hprim
    have hG0 : padicGaussCoefficient p χ n ≠ 0 := by
      intro h0
      rw [h0, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hG
      exact (inv_ne_zero (pow_ne_zero n hp)) hG.symm
    rw [padicAngularShell_fourier_on_conductor p χ n k u hu]
    exact mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hpC) (Circle.coe_ne_zero _)) hG0

end RiemannMasullo.PadicConductor
