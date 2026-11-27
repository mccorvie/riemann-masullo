module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Tactic

/-! # A rational mixed-place upper cutoff

The additive mixed symbol on `ℝ × ℚ_[p]` is not assumed integrable. We use
finite valuation-shell truncations and compute their Fourier transforms in the
self-dual Tamagawa normalization (Masullo, p. 517, (12.4.1.8)).
-/

@[expose] public noncomputable section

namespace RiemannMasullo
namespace MixedCutoff

open MeasureTheory Set
open scoped Classical

variable (p : ℕ) [Fact p.Prime]

local instance : MeasurableSpace ℚ_[p] := borel _
local instance : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The closed lattice ball of valuation at least `n`. -/
def padicLatticeBall (n : ℤ) : Set ℚ_[p] :=
  ((p : ℚ_[p]) ^ n * ·) '' Metric.closedBall (0 : ℚ_[p]) 1

private theorem ballCompact (n : ℤ) : IsCompact (padicLatticeBall p n) :=
  (isCompact_closedBall (0 : ℚ_[p]) 1).image (continuous_const.mul continuous_id)

private theorem ballNested (n : ℤ) : padicLatticeBall p (n+1) ⊆ padicLatticeBall p n := by
  rintro _ ⟨x, hx, rfl⟩
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  refine ⟨(p : ℚ_[p]) * x, ?_, ?_⟩
  swap
  · change (p : ℚ_[p]) ^ n * ((p : ℚ_[p]) * x) = (p : ℚ_[p]) ^ (n+1) * x
    rw [zpow_add₀ hp, zpow_one, mul_assoc]
  rw [Metric.mem_closedBall, dist_zero_right] at hx ⊢
  rw [norm_mul, Padic.norm_p]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_le
  exact (mul_le_of_le_one_left (norm_nonneg x) (by simpa [one_div] using (one_div_le_one_div_of_le zero_lt_one hp1))).trans hx

private theorem ballIndicatorIntegrable (n : ℤ) {g : ℚ_[p] → ℂ} (hg : Continuous g) :
    Integrable ((padicLatticeBall p n).indicator g) (padicTamagawaMeasure p) := by
  have : (padicTamagawaMeasure p).IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  have hs := ballCompact p n
  exact (integrable_indicator_iff hs.measurableSet).mpr (hg.continuousOn.integrableOn_compact hs)

/-- Finite Haar integrability on the `n`th valuation shell. -/
theorem padicShellIndicator_integrable (n : ℤ) {g : ℚ_[p] → ℂ} (hg : Continuous g) :
    Integrable ((padicLatticeBall p n \ padicLatticeBall p (n+1)).indicator g)
      (padicTamagawaMeasure p) := by
  rw [Set.indicator_sdiff (ballNested p n)]
  exact (ballIndicatorIntegrable p n hg).sub (ballIndicatorIntegrable p (n+1) hg)

/-- Exact finite-shell transform, including the negative outer frequency layer. -/
theorem padicTamagawaFourier_valuationShell (n : ℤ) :
    tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p)
        ((padicLatticeBall p n \ padicLatticeBall p (n+1)).indicator (fun _ ↦ (1 : ℂ))) =
      ((p : ℝ) ^ (-n) : ℂ) • (padicLatticeBall p (-n)).indicator (fun _ ↦ (1 : ℂ)) -
      ((p : ℝ) ^ (-(n+1)) : ℂ) • (padicLatticeBall p (-(n+1))).indicator (fun _ ↦ (1 : ℂ)) := by
  let B := padicLatticeBall p
  let I (j : ℤ) := (B j).indicator (fun _ ↦ (1 : ℂ))
  have h (j : ℤ) : tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) (I j) =
      ((p : ℝ) ^ (-j) : ℂ) • I (-j) := padicTamagawaFourier_scaledIntegers p j
  rw [Set.indicator_sdiff (ballNested p n)]
  change tamagawaFourier _ _ (I n - I (n+1)) = _ • I (-n) - _ • I (-(n+1))
  rw [← h n, ← h (n+1)]
  funext y
  let g (x : ℚ_[p]) : ℂ := star (padicStandardCharacter p (x*y) : ℂ)
  obtain ⟨e, he⟩ := exists_padicPontryaginDualEquiv p
  have hc : Continuous (fun x : ℚ_[p] ↦ padicStandardCharacter p (x*y)) := by
    have hc' : Continuous (fun x : ℚ_[p] ↦ e (Multiplicative.ofAdd y) (Multiplicative.ofAdd x)) :=
      (e (Multiplicative.ofAdd y)).continuous
    simpa only [he, mul_comm y] using hc'
  have hg : Continuous g := (continuous_subtype_val.comp hc).star
  change (∫ x, (I n x - I (n+1) x) * g x ∂padicTamagawaMeasure p) =
    (∫ x, I n x * g x ∂padicTamagawaMeasure p) - ∫ x, I (n+1) x * g x ∂padicTamagawaMeasure p
  simp only [I, sub_mul, ← indicator_mul_left, one_mul]
  exact integral_sub (ballIndicatorIntegrable p n hg) (ballIndicatorIntegrable p (n+1) hg)

/-- The lattice-ball radius in the self-dual normalization is `p⁻ⁿ`. -/
theorem padicLatticeBall_eq_closedBall (n : ℤ) :
    padicLatticeBall p n = Metric.closedBall (0 : ℚ_[p]) ((p : ℝ)^(-n)) := by
  have hp : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  change (((p : ℚ_[p])^n • ·) '' Metric.closedBall (0 : ℚ_[p]) 1) = _
  rw [Metric.smul_image_closedBall (zpow_ne_zero _ hp), smul_zero, mul_one, norm_zpow,
    Padic.norm_p, inv_zpow, zpow_neg]

/-- The difference of consecutive lattice balls is a single norm shell. -/
theorem padicLatticeShell_iff (n : ℤ) (z : ℚ_[p]) :
    z ∈ padicLatticeBall p n \ padicLatticeBall p (n+1) ↔ ‖z‖ = (p : ℝ)^(-n) := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  simp only [padicLatticeBall_eq_closedBall, mem_sdiff, Metric.mem_closedBall, dist_zero_right]
  by_cases hz : z = 0
  · subst z
    rw [norm_zero]
    exact iff_of_false (fun h ↦ h.2 (zpow_pos (zero_lt_one.trans hp) _).le)
      (zpow_pos (zero_lt_one.trans hp) _).ne
  · rw [Padic.norm_eq_zpow_neg_valuation hz]
    simp only [zpow_le_zpow_iff_right₀ hp,
      zpow_right_inj₀ (zero_lt_one.trans hp) hp.ne', neg_le_neg_iff, not_le, neg_inj]
    omega

/-- The standard real additive character used for the rational mixed cutoff. -/
def realCutoffCharacter (x : ℝ) : Circle := Circle.exp (2 * Real.pi * x)

private theorem real_scaleFourier (b : ℝ → ℂ) {a : ℝ} (ha : 0 < a) (u : ℝ) :
    tamagawaFourier volume realCutoffCharacter (fun t ↦ b (a⁻¹*t)) u =
      (a : ℂ) * tamagawaFourier volume realCutoffCharacter b (a*u) := by
  unfold tamagawaFourier
  let f : ℝ → ℂ := fun t ↦ b t * star (realCutoffCharacter (t*(a*u)) : ℂ)
  have he (t : ℝ) : b (a⁻¹*t) * star (realCutoffCharacter (t*u) : ℂ) = f (a⁻¹*t) := by
    have h : a⁻¹ * t * (a*u) = t*u := by field_simp [ha.ne']
    change _ = b (a⁻¹*t) * star (realCutoffCharacter (a⁻¹ * t * (a*u)) : ℂ)
    rw [h]
  simp_rw [he]
  rw [Measure.integral_comp_inv_mul_left, abs_of_pos ha, Complex.real_smul]

/-- The actual upper product symbol cut to a single finite-place norm shell. -/
def mixedShellSymbol (b : ℝ → ℂ) (n : ℤ) (q : ℝ × ℚ_[p]) : ℂ :=
  b (‖q.2‖ * q.1) * (padicLatticeBall p n \ padicLatticeBall p (n+1)).indicator (fun _ ↦ 1) q.2

/-- Exact finite-shell formula for the rational product cutoff. The archimedean
Jacobian cancels the mass in the first reciprocal-ball term. -/
theorem tamagawaFourier_mixedShellSymbol (b : ℝ → ℂ) (n : ℤ) (u : ℝ) (v : ℚ_[p]) :
    tamagawaFourier (volume.prod (padicTamagawaMeasure p))
      (fun q : ℝ × ℚ_[p] ↦ realCutoffCharacter q.1 * padicStandardCharacter p q.2)
      (mixedShellSymbol p b n) (u,v) =
    tamagawaFourier volume realCutoffCharacter b ((p:ℝ)^n * u) *
      ((padicLatticeBall p (-n)).indicator (fun _ ↦ (1:ℂ)) v -
        ((p:ℝ)⁻¹ : ℂ) * (padicLatticeBall p (-(n+1))).indicator (fun _ ↦ 1) v) := by
  let I : ℚ_[p] → ℂ :=
    (padicLatticeBall p n \ padicLatticeBall p (n+1)).indicator (fun _ ↦ 1)
  let q : ℝ → ℂ := fun t ↦ b ((p:ℝ)^(-n) * t)
  have hsep (z : ℝ × ℚ_[p]) : mixedShellSymbol p b n z = q z.1 * I z.2 := by
    by_cases hz : z.2 ∈ padicLatticeBall p n \ padicLatticeBall p (n+1)
    · simp only [mixedShellSymbol, I, q, (padicLatticeShell_iff p n z.2).1 hz]
    · simp [mixedShellSymbol, I, hz]
  have : (padicTamagawaMeasure p).IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  let μ := padicTamagawaMeasure p
  have hprod : tamagawaFourier (volume.prod μ)
      (fun z : ℝ × ℚ_[p] ↦ realCutoffCharacter z.1 * padicStandardCharacter p z.2)
      (mixedShellSymbol p b n) (u,v) =
      tamagawaFourier volume realCutoffCharacter q u *
        tamagawaFourier μ (padicStandardCharacter p) I v := by
    unfold tamagawaFourier
    rw [← integral_prod_mul]
    refine integral_congr_ae (ae_of_all _ ?_)
    intro z
    simp only [hsep, Prod.fst_mul, Prod.snd_mul, Circle.coe_mul, star_mul']
    ring
  have hp : 0 < (p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).pos
  have hz : (p:ℝ) ≠ 0 := hp.ne'
  have hreal : tamagawaFourier volume realCutoffCharacter q u =
      (((p:ℝ)^n : ℝ) : ℂ) * tamagawaFourier volume realCutoffCharacter b ((p:ℝ)^n * u) := by
    simpa only [q, zpow_neg] using real_scaleFourier b (zpow_pos hp n) u
  have hPadic := congrFun (padicTamagawaFourier_valuationShell p n) v
  rw [hprod, hreal]
  change _ * tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) I v = _
  change tamagawaFourier (padicTamagawaMeasure p) (padicStandardCharacter p) I v = _ at hPadic
  rw [hPadic]
  have h0 : (p:ℝ)^n * (p:ℝ)^(-n) = 1 := by simp [zpow_neg, zpow_ne_zero n hz]
  have h1 : (p:ℝ)^n * (p:ℝ)^(-(n+1)) = (p:ℝ)⁻¹ := by
    rw [← zpow_add₀ hz, show n + -(n+1) = -1 by omega, zpow_neg_one]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub]
  have hc0 : ((p:ℝ) : ℂ)^n * ((p:ℝ) : ℂ)^(-n) = 1 := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_one] using
      congrArg Complex.ofReal h0
  have hc1 : ((p:ℝ) : ℂ)^n * ((p:ℝ) : ℂ)^(-(n+1)) = ((p:ℝ) : ℂ)⁻¹ := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_zpow, Complex.ofReal_inv] using
      congrArg Complex.ofReal h1
  have hpoly (a b c d e f : ℂ) :
      a*b*(c*d) - a*b*(e*f) = b*((a*c)*d) - b*((a*e)*f) := by ring
  simp only [Complex.ofReal_zpow, hpoly, hc0, hc1, one_mul]

/-- The finite-place shell kernel has one negative reciprocal-shell term and a
one-sided lacunary tail. The identity does not require any decay of the real test. -/
theorem tamagawaFourier_mixedShellSymbol_offAxis (b : ℝ → ℂ) (n : ℤ) (u : ℝ)
    {v : ℚ_[p]} (hv : v ≠ 0) :
    tamagawaFourier (volume.prod (padicTamagawaMeasure p))
      (fun q : ℝ × ℚ_[p] ↦ realCutoffCharacter q.1 * padicStandardCharacter p q.2)
      (mixedShellSymbol p b n) (u,v) =
    tamagawaFourier volume realCutoffCharacter b ((p:ℝ)^n * u) *
      (if n + v.valuation = -1 then -((p:ℝ)⁻¹ : ℂ)
      else if 0 ≤ n + v.valuation then 1 - ((p:ℝ)⁻¹ : ℂ) else 0) := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hmem (m : ℤ) : v ∈ padicLatticeBall p m ↔ m ≤ v.valuation := by
    rw [padicLatticeBall_eq_closedBall, Metric.mem_closedBall, dist_zero_right,
      Padic.norm_eq_zpow_neg_valuation hv, zpow_le_zpow_iff_right₀ hp, neg_le_neg_iff]
  rw [tamagawaFourier_mixedShellSymbol]
  apply congrArg (_ * ·)
  simp only [indicator, hmem]
  split_ifs
  all_goals first | omega | ring

/-- A single norm shell makes the mixed cutoff integrable whenever its real profile is. -/
theorem mixedShellSymbol_integrable {b : ℝ → ℂ} (hb : Integrable b) (n : ℤ) :
    Integrable (mixedShellSymbol p b n) (volume.prod (padicTamagawaMeasure p)) := by
  let I : ℚ_[p] → ℂ :=
    (padicLatticeBall p n \ padicLatticeBall p (n+1)).indicator (fun _ ↦ 1)
  let c : ℝ := (p:ℝ)^(-n)
  have hp : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hq : Integrable (fun t ↦ b (c*t)) := hb.comp_mul_left' (zpow_ne_zero _ hp.ne')
  have hi : Integrable I (padicTamagawaMeasure p) :=
    padicShellIndicator_integrable p n continuous_const
  refine (hq.mul_prod hi).congr (ae_of_all _ ?_)
  intro z
  by_cases hz : z.2 ∈ padicLatticeBall p n \ padicLatticeBall p (n+1)
  · simp only [mixedShellSymbol, I, c, (padicLatticeShell_iff p n z.2).1 hz]
  · simp [mixedShellSymbol, I, hz]

/-- The finite-shell truncation of the true mixed product cutoff, with no
integrability hypothesis on the untruncated symbol. -/
def mixedFiniteShellSymbol (b : ℝ → ℂ) (J : Finset ℤ) (z : ℝ × ℚ_[p]) : ℂ :=
  ∑ n ∈ J, mixedShellSymbol p b n z

/-- The actual mixed additive Fourier integral commutes with an arbitrary finite
shell truncation. The one-shell terms are explicit in
`tamagawaFourier_mixedShellSymbol_offAxis`. -/
theorem tamagawaFourier_mixedFiniteShellSymbol {b : ℝ → ℂ} (hb : Integrable b)
    (J : Finset ℤ) (u : ℝ) (v : ℚ_[p]) :
    tamagawaFourier (volume.prod (padicTamagawaMeasure p))
      (fun q : ℝ × ℚ_[p] ↦ realCutoffCharacter q.1 * padicStandardCharacter p q.2)
      (mixedFiniteShellSymbol p b J) (u,v) =
    ∑ n ∈ J, tamagawaFourier (volume.prod (padicTamagawaMeasure p))
      (fun q : ℝ × ℚ_[p] ↦ realCutoffCharacter q.1 * padicStandardCharacter p q.2)
      (mixedShellSymbol p b n) (u,v) := by
  let g (q : ℝ × ℚ_[p]) : ℂ := star ((realCutoffCharacter (q.1*u) * padicStandardCharacter p (q.2*v) :
    Circle) : ℂ)
  have hpc : Continuous (fun x : ℚ_[p] ↦ padicStandardCharacter p (x*v)) := by
    obtain ⟨e, he⟩ := exists_padicPontryaginDualEquiv p
    have hc : Continuous (fun x : ℚ_[p] ↦ e (Multiplicative.ofAdd v) (Multiplicative.ofAdd x)) :=
      (e (Multiplicative.ofAdd v)).continuous
    simpa only [he, mul_comm v] using hc
  have hg : Continuous g := (continuous_subtype_val.comp
    ((Circle.exp.continuous.comp (continuous_const.mul (continuous_fst.mul_const u))).mul
      (hpc.comp continuous_snd))).star
  have hnorm (q : ℝ × ℚ_[p]) : ‖g q‖ ≤ 1 := by
    unfold g
    rw [norm_star, Circle.norm_coe]
  simp only [tamagawaFourier, mixedFiniteShellSymbol, Finset.sum_mul]
  exact integral_finsetSum J (fun n _ ↦
    (mixedShellSymbol_integrable p hb n).mul_bdd hg.aestronglyMeasurable (ae_of_all _ hnorm))

end MixedCutoff
end RiemannMasullo

namespace RiemannMasullo.MixedCutoff

open MeasureTheory
open scoped FourierTransform

/-- The conjugated real Tamagawa character has Mathlib's forward Fourier sign.
For a compactly supported `C²` profile the estimate holds also at frequency zero. -/
theorem norm_real_tamagawaFourier_le (b : ℝ → ℂ) (hb : ContDiff ℝ 2 b)
    (hc : HasCompactSupport b) (u : ℝ) :
    ‖tamagawaFourier volume realCutoffCharacter b u‖ ≤
      ((∫ t, ‖b t‖) + (4 * Real.pi ^ 2)⁻¹ * ∫ t, ‖iteratedDeriv 2 b t‖) / (1 + u ^ 2) := by
  have hs (k : ℕ) : HasCompactSupport (iteratedDeriv k b) := by
    induction k with
    | zero => simpa using hc
    | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hi (k : ℕ) (hk : k ≤ 2) : Integrable (iteratedDeriv k b) :=
    (hb.continuous_iteratedDeriv k (by exact_mod_cast hk)).integrable_of_hasCompactSupport (hs k)
  have he : tamagawaFourier volume realCutoffCharacter b u = 𝓕 b u := by
    rw [tamagawaFourier, Real.fourier_real_eq]
    apply integral_congr_ae
    filter_upwards with t
    rw [AddChar.map_neg_eq_inv, Real.fourierChar_apply', Circle.smul_def, smul_eq_mul,
      Circle.coe_inv_eq_conj, mul_comm]; rfl
  rw [he, le_div_iff₀ (by positivity : 0 < 1 + u ^ 2), mul_comm]
  exact Real.one_add_sq_mul_norm_fourier_le hb hi u

end RiemannMasullo.MixedCutoff

open scoped BigOperators

namespace RiemannMasullo.MixedCutoff.Lacunary

variable {E : Type*} [NormedAddCommGroup E] {B : ℝ → E} {p C r : ℝ}

/-- A quadratic envelope, required only on the positive half line. -/
def Decays (B : ℝ → E) (C : ℝ) : Prop :=
  ∀ x : ℝ, 0 < x → ‖B x‖ ≤ C / (1 + x)^2

private theorem majorant (hp : 1 < p) (hC : 0 ≤ C) (hB : Decays B C)
    (hr : 0 < r) (j : ℕ) : ‖B (p^j*r)‖ ≤ C / r^2 * (p⁻¹)^j := by
  have ht : 1 ≤ p^j := one_le_pow₀ hp.le
  have ht' : 0 < p^j := zero_lt_one.trans_le ht
  have h : p^j * r^2 ≤ (1 + p^j*r)^2 := by
    calc p^j * r^2 ≤ (p^j * p^j) * r^2 :=
           mul_le_mul_of_nonneg_right (le_mul_of_one_le_right ht'.le ht) (sq_nonneg r)
         _ ≤ (1 + p^j*r)^2 := by nlinarith [mul_pos ht' hr]
  calc ‖B (p^j*r)‖ ≤ C / (1 + p^j*r)^2 := hB _ (mul_pos ht' hr)
       _ ≤ C / (p^j*r^2) := div_le_div_of_nonneg_left hC (by positivity) h
       _ = _ := by rw [inv_pow]; field_simp [ht'.ne', hr.ne']

private theorem geom (hp : 1 < p) (a : ℝ) :
    HasSum (fun j : ℕ => a * (p⁻¹)^j) (a * (1-p⁻¹)⁻¹) :=
  (hasSum_geometric_of_lt_one (inv_nonneg.mpr (zero_le_one.trans hp.le))
    (inv_lt_one_of_one_lt₀ hp)).mul_left a

theorem absolute (hp : 1 < p) (hC : 0 ≤ C) (hB : Decays B C) (hr : 0 < r) :
    Summable (fun j : ℕ => ‖B (p^j*r)‖) :=
  .of_nonneg_of_le (fun _ => norm_nonneg _) (majorant hp hC hB hr) (geom hp _).summable

/-- At large radius the whole absolute sum decays quadratically. -/
theorem absolute_sum_le (hp : 1 < p) (hC : 0 ≤ C) (hB : Decays B C) (hr : 0 < r) :
    ∑' j : ℕ, ‖B (p^j*r)‖ ≤ C / r^2 * (1-p⁻¹)⁻¹ :=
  ((absolute hp hC hB hr).tsum_le_tsum (majorant hp hC hB hr) (geom hp _).summable).trans_eq
    (geom hp _).tsum_eq

private theorem far_tail (hp : 1 < p) (hC : 0 ≤ C) (hB : Decays B C) (hr : 1 ≤ r) :
    ∑' j : ℕ, ‖B (p^j*r)‖ ≤ C * (1-p⁻¹)⁻¹ := by
  refine (absolute_sum_le hp hC hB (zero_lt_one.trans_le hr)).trans ?_
  have hh := inv_lt_one_of_one_lt₀ hp
  have hr0 := zero_lt_one.trans_le hr
  apply mul_le_mul_of_nonneg_right _ (inv_nonneg.mpr (sub_nonneg.mpr hh.le))
  exact (div_le_iff₀ (by positivity : 0 < r^2)).2 (le_mul_of_one_le_right hC (by nlinarith [sq_nonneg (r-1)]))

/-- The explicit ceiling split gives an estimate for the full absolute sum, hence
also for every finite subsum (not just initial segments). -/
theorem logarithmic (hp : 1 < p) (hC : 0 ≤ C) (hB : Decays B C) (hr : 0 < r) :
    ∑' j : ℕ, ‖B (p^j*r)‖ ≤
      (1 + max 0 (Real.log r⁻¹) / Real.log p) * C + C * (1-p⁻¹)⁻¹ := by
  let x := max 0 (Real.log r⁻¹) / Real.log p
  let k := ⌈x⌉₊
  have hl := Real.log_pos hp
  have hx : 0 ≤ x := div_nonneg (le_max_left ..) hl.le
  have hk : x ≤ (k : ℝ) := Nat.le_ceil _
  have hk' : (k : ℝ) ≤ 1+x := by linarith [Nat.ceil_lt_add_one hx]
  have hlog : Real.log r⁻¹ ≤ (k:ℝ)*Real.log p :=
    (le_max_right 0 _).trans ((div_le_iff₀ hl).mp hk)
  have hpow : r⁻¹ ≤ p^k := by
    apply (Real.log_le_log_iff (inv_pos.mpr hr) (pow_pos (zero_lt_one.trans hp) _)).mp
    rwa [Real.log_pow]
  have hkr : 1 ≤ p^k*r := by simpa [div_eq_mul_inv] using (div_le_iff₀ hr).mp (show 1/r ≤ p^k by simpa using hpow)
  rw [← (absolute hp hC hB hr).sum_add_tsum_nat_add k]
  apply add_le_add
  · calc ∑ j ∈ Finset.range k, ‖B (p^j*r)‖ ≤ ∑ _j ∈ Finset.range k, C := by
           apply Finset.sum_le_sum; intro j _
           have ht := mul_pos (pow_pos (zero_lt_one.trans hp) j) hr
           exact (hB _ ht).trans ((div_le_iff₀ (by positivity)).mpr
             (le_mul_of_one_le_right hC (by nlinarith [sq_nonneg (p^j*r)])))
         _ = (k : ℝ)*C := by simp
         _ ≤ _ := mul_le_mul_of_nonneg_right hk' hC
  · simpa only [pow_add, mul_assoc] using far_tail hp hC hB hkr

theorem partial_le (hp : 1 < p) (hC : 0 ≤ C) (hB : Decays B C) (hr : 0 < r)
    (s : Finset ℕ) : ‖∑ j ∈ s, B (p^j*r)‖ ≤
      (1 + max 0 (Real.log r⁻¹) / Real.log p) * C + C * (1-p⁻¹)⁻¹ :=
  (norm_sum_le ..).trans (((absolute hp hC hB hr).sum_le_tsum s (fun _ _ => norm_nonneg _)).trans
    (logarithmic hp hC hB hr))

/-- A bounded-error leading term on each logarithmic shell. Here `N+1` differs
from `log(1/r)/log p` by at most one. Only a one-sided Lipschitz bound is needed. -/
theorem shell_leading [CompleteSpace E] (hp : 1 < p) (hC : 0 ≤ C) (hB : Decays B C)
    (hr : 0 < r) {L : ℝ} (hL : 0 ≤ L) (lip : ∀ x : ℝ, 0 < x → x ≤ 1 → ‖B x - B 0‖ ≤ L*x)
    (N : ℕ) (hlo : p^N*r ≤ 1) (hhi : 1 ≤ p^(N+1)*r) :
    ‖(∑' j : ℕ, B (p^j*r)) - (N+1) • B 0‖ ≤ L * (p/(p-1)) + C * (1-p⁻¹)⁻¹ := by
  have hp0 := zero_lt_one.trans hp
  have hsum : Summable (fun j : ℕ => B (p^j*r)) := (absolute hp hC hB hr).of_norm
  rw [← hsum.sum_add_tsum_nat_add (N+1), add_sub_right_comm]
  apply (norm_add_le ..).trans
  apply add_le_add
  · have he : (∑ j ∈ Finset.range (N+1), B (p^j*r)) - (N+1) • B 0 =
        ∑ j ∈ Finset.range (N+1), (B (p^j*r) - B 0) := by simp [Finset.sum_sub_distrib]
    rw [he]
    refine (norm_sum_le ..).trans ((Finset.sum_le_sum (g := fun j : ℕ => L * (p^j*r)) ?_).trans ?_)
    · intro j hj
      exact lip _ (mul_pos (pow_pos hp0 _) hr) ((mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hp.le (by simpa using hj : j ≤ N)) hr.le).trans hlo)
    · have hid : (∑ j ∈ Finset.range (N+1), p^j) * (p-1) = p^(N+1)-1 := geom_sum_mul p _
      rw [← Finset.mul_sum, ← Finset.sum_mul]
      apply mul_le_mul_of_nonneg_left _ hL
      apply (le_div_iff₀ (sub_pos.mpr hp)).mpr
      calc (∑ j ∈ Finset.range (N+1), p^j) * r * (p-1) = (p^(N+1)-1)*r := by rw [← hid]; ring
           _ ≤ p := by rw [pow_succ]; nlinarith [mul_le_mul_of_nonneg_left hlo hp0.le]
  · simpa only [pow_add, mul_assoc] using
      (norm_tsum_le_tsum_norm (absolute hp hC hB (zero_lt_one.trans_le hhi))).trans
        (far_tail hp hC hB hhi)

end RiemannMasullo.MixedCutoff.Lacunary

namespace RiemannMasullo.MixedLogLocal

open MeasureTheory Set
open scoped Classical

/-- The positive part of the reciprocal logarithm (with Lean's value zero at zero). -/
def loss (r : ℝ) : ℝ := max (-Real.log r) 0

theorem loss_eq (r : ℝ) : loss r = max (Real.log (1 / r)) 0 := by
  simp [loss, one_div, Real.log_inv]

theorem real_integrableOn (a b : ℝ) : IntegrableOn (fun u : ℝ ↦ loss |u|) (Icc a b) := by
  rw [integrableOn_Icc_iff_integrableOn_Ioc]
  have h := (intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).1
  change Integrable (fun u : ℝ ↦ loss |u|) ((volume : Measure ℝ).restrict (Ioc a b))
  simpa only [loss, Real.log_abs] using h.neg_part

variable (p : ℕ) [Fact p.Prime]

local instance : MeasurableSpace ℚ_[p] := borel _
local instance : BorelSpace ℚ_[p] := ⟨rfl⟩

theorem continuousAt_off_axes {x : ℝ × ℚ_[p]} (hu : x.1 ≠ 0) (hv : x.2 ≠ 0) :
    ContinuousAt (fun y : ℝ × ℚ_[p] ↦ loss |y.1| + loss ‖y.2‖) x := by
  unfold loss
  apply ContinuousAt.add
  · exact ((continuous_fst.continuousAt.abs.log (abs_ne_zero.mpr hu)).neg).max continuousAt_const
  · exact ((continuous_snd.continuousAt.norm.log (norm_ne_zero_iff.mpr hv)).neg).max continuousAt_const

/-- Read the mass of the lattice ball off its Fourier transform at zero. -/
private theorem ball_mass (n : ℕ) :
    (padicTamagawaMeasure p).real (Metric.closedBall (0 : ℚ_[p]) ((p : ℝ)⁻¹ ^ n)) =
      (p : ℝ)⁻¹ ^ n := by
  let B (k : ℤ) := ((p : ℚ_[p]) ^ k * ·) '' Metric.closedBall (0 : ℚ_[p]) 1
  have hz (k : ℤ) : 0 ∈ B k := ⟨0, by simp, mul_zero _⟩
  have hm (k : ℤ) : MeasurableSet (B k) :=
    ((isCompact_closedBall (0 : ℚ_[p]) 1).image (continuous_const.mul continuous_id)).measurableSet
  have h := congrFun (padicTamagawaFourier_scaledIntegers p (n : ℤ)) 0
  change (∫ x, (B n).indicator (fun _ ↦ (1 : ℂ)) x * star (padicStandardCharacter p (x * 0) : ℂ) ∂padicTamagawaMeasure p) =
    ((p : ℝ) ^ (-(n : ℤ)) : ℂ) * (B (-(n : ℤ))).indicator (fun _ ↦ 1) 0 at h
  have hstar : star ((1 : Circle) : ℂ) = 1 := by
    change star (1 : ℂ) = 1
    exact star_one ℂ
  simp only [mul_zero, padicStandardCharacter_zero, hstar, mul_one,
    indicator_of_mem (hz _)] at h
  rw [integral_indicator (hm _), setIntegral_const, Complex.real_smul, mul_one] at h
  have hp0 : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hB : B n = Metric.closedBall 0 ((p : ℝ)⁻¹ ^ n) := by
    change (((p : ℚ_[p]) ^ (n : ℤ)) • ·) '' _ = _
    rw [zpow_natCast, Metric.smul_image_closedBall (pow_ne_zero n hp0), smul_zero, mul_one,
      Padic.norm_p_pow, zpow_neg, zpow_natCast, inv_pow]
  have hr : (padicTamagawaMeasure p).real (B n) = (p : ℝ) ^ (-(n : ℤ)) := by
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_zpow] using h)
  simpa [hB, zpow_neg, inv_pow] using hr

/-- Global integrability: outside the integer ball the positive part vanishes.
On the sphere of radius `p⁻ⁿ` it costs `n log p` and its mass is at most `p⁻ⁿ`. -/
theorem padic_integrable : Integrable (fun v : ℚ_[p] ↦ loss ‖v‖) (padicTamagawaMeasure p) := by
  let μ := padicTamagawaMeasure p
  have : μ.IsAddHaarMeasure := (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  have hp : 1 < (p : ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hl := Real.log_pos hp
  let S (n : ℕ) := Metric.sphere (0 : ℚ_[p]) ((p : ℝ)⁻¹ ^ n)
  have hS (n : ℕ) : MeasurableSet (S n) := Metric.isClosed_sphere.measurableSet
  have hsub (n : ℕ) : S n ⊆ Metric.closedBall 0 ((p : ℝ)⁻¹ ^ n) := Metric.sphere_subset_closedBall
  have hval (n : ℕ) : EqOn (fun v : ℚ_[p] ↦ loss ‖v‖) (fun _ ↦ (n : ℝ) * Real.log p) (S n) := by
    intro x hx
    have hx' : ‖x‖ = (p : ℝ)⁻¹ ^ n := by simpa [S, Metric.mem_sphere] using hx
    simp [loss, hx', Real.log_pow, Real.log_inv, max_eq_left (mul_nonneg (Nat.cast_nonneg n) hl.le)]
  have hi (n : ℕ) : IntegrableOn (fun v : ℚ_[p] ↦ loss ‖v‖) (S n) μ :=
    (integrableOn_congr_fun (hval n) (hS n)).2 (integrableOn_const
      ((measure_mono (μ := μ) (hsub n)).trans_lt measure_closedBall_lt_top).ne)
  have hb (n : ℕ) : (∫ x in S n, ‖loss ‖x‖‖ ∂μ) ≤
      ((n : ℝ) * (p : ℝ)⁻¹ ^ n) * Real.log p := by
    rw [setIntegral_congr_fun (hS n) (g := fun _ ↦ (n : ℝ) * Real.log p)
      (fun x hx ↦ by
        change ‖loss ‖x‖‖ = (n : ℝ) * Real.log p
        have hx' : loss ‖x‖ = (n : ℝ) * Real.log p := hval n hx
        rw [hx', Real.norm_eq_abs, abs_of_nonneg (by positivity)]), setIntegral_const, smul_eq_mul]
    have hm := measureReal_mono (μ := μ) (hsub n) measure_closedBall_lt_top.ne
    rw [show μ.real (Metric.closedBall 0 ((p : ℝ)⁻¹ ^ n)) = _ from ball_mass p n] at hm
    calc
      _ ≤ ((p : ℝ)⁻¹ ^ n) * ((n : ℝ) * Real.log p) := mul_le_mul_of_nonneg_right hm (by positivity)
      _ = _ := by ring
  have hr : ‖(p : ℝ)⁻¹‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos (by positivity)]; exact inv_lt_one_of_one_lt₀ hp
  have hsum := (summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_right (Real.log p)
  have hu := integrableOn_iUnion_of_summable_integral_norm hi (Summable.of_nonneg_of_le
    (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) hb (by simpa using hsum))
  apply (integrableOn_iff_integrable_of_support_subset (s := ⋃ n, S n) ?_).mp hu
  intro x hx
  change loss ‖x‖ ≠ 0 at hx
  have hx0 : x ≠ 0 := by rintro rfl; simp [loss] at hx
  have hv : 0 ≤ x.valuation := by
    by_contra! h
    have hn : 1 ≤ ‖x‖ := by
      rw [Padic.norm_eq_zpow_neg_valuation hx0]
      exact one_le_zpow₀ hp.le (by omega)
    exact hx (max_eq_right (neg_nonpos.mpr (Real.log_nonneg hn)))
  refine mem_iUnion.mpr ⟨x.valuation.toNat, ?_⟩
  simp only [S, Metric.mem_sphere, dist_zero_right, Padic.norm_eq_zpow_neg_valuation hx0,
    zpow_neg, inv_pow]
  rw [← zpow_natCast, Int.toNat_of_nonneg hv]

/-- Local majorant on a compact real interval times an arbitrary p-adic closed ball. -/
theorem rectangle_integrableOn (a b : ℝ) (z : ℚ_[p]) (R : ℝ) :
    IntegrableOn (fun x : ℝ × ℚ_[p] ↦ loss |x.1| + loss ‖x.2‖)
      (Icc a b ×ˢ Metric.closedBall z R) (volume.prod (padicTamagawaMeasure p)) := by
  let μ := padicTamagawaMeasure p
  have : μ.IsAddHaarMeasure := (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  have : IsFiniteMeasure (μ.restrict (Metric.closedBall z R)) :=
    isFiniteMeasure_restrict.mpr measure_closedBall_lt_top.ne
  change Integrable _ ((volume.prod μ).restrict _)
  rw [← Measure.prod_restrict]
  exact ((real_integrableOn a b).comp_fst _).add (((padic_integrable p).integrableOn (s := Metric.closedBall z R)).comp_snd _)

/-- An a.e. bound suffices, so no values on the singular axes need be specified. -/
theorem integrableOn_of_ae_bound {E : Type*} [NormedAddCommGroup E] (a b : ℝ)
    (z : ℚ_[p]) (R : ℝ) (f : ℝ × ℚ_[p] → E)
    (hf : AEStronglyMeasurable f ((volume.prod (padicTamagawaMeasure p)).restrict
      (Icc a b ×ˢ Metric.closedBall z R)))
    (h : ∀ᵐ x ∂(volume.prod (padicTamagawaMeasure p)).restrict (Icc a b ×ˢ Metric.closedBall z R),
      ‖f x‖ ≤ loss |x.1| + loss ‖x.2‖) :
    IntegrableOn f (Icc a b ×ˢ Metric.closedBall z R) (volume.prod (padicTamagawaMeasure p)) :=
  (rectangle_integrableOn p a b z R).mono' hf h

end RiemannMasullo.MixedLogLocal
