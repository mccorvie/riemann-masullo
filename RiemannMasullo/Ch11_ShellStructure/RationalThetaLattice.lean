module

public import RiemannMasullo.Ch11_ShellStructure.Sec1b
public import RiemannMasullo.Ch03_IdelicZeta.RatEmptyFourier
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Integer sums for rational polar-free theta lifts

With integer indicators at the finite places, a real Schwartz test gives a rational
adelic test. In the trivial character, its homogeneous theta lift is a sum over the
positive integers times twice the norm-one Tamagawa mass. A support bound makes its
evaluation finite, and the substitution from log norm to physical norm gives the
ordinary unit-interval approximation error in Theorem 12.5.1.1 (pp. 519–520).

The standard insertion and the rational theta series proofs are adapted from
Sergii Penner's `RationalThetaSpan` and `RationalThetaSeries` at revision
63ea7fc880fdf27febeea6f5acdef268c506b7b7.
-/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped FourierTransform NumberField.AdeleRing NNReal SchwartzMap

namespace RiemannMasullo

set_option quotPrecheck false

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Bℚ" => SchwartzBruhat (Multiplicative 𝔸)
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "realCoord" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "𝓢ℝ" => SchwartzMap ℝ ℂ
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "U" => (v : V) → (v.adicCompletionIntegers ℚ)ˣ

private theorem real_arch_test_mem (f : 𝓢ℝ) :
    (fun x : Multiplicative (InfiniteAdeleRing ℚ) ↦ f (realCoord (x.toAdd Rat.infinitePlace))) ∈
      schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing ℚ)) := by
  classical
  let : Unique {w : InfinitePlace ℚ // w.IsReal} :=
    uniqueOfSubsingleton ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  let : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
    ⟨fun w ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr w.property) (IsTotallyReal.isReal w.val)⟩
  let e := (ContinuousLinearEquiv.prodUnique ℝ
      ({w : InfinitePlace ℚ // w.IsReal} → ℝ) ({w : InfinitePlace ℚ // w.IsComplex} → ℂ)).trans
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : {w : InfinitePlace ℚ // w.IsReal} ↦ ℝ))
  apply (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun x : InfiniteAdeleRing ℚ ↦ f (realCoord (x Rat.infinitePlace)))).2
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f, fun _ ↦ rfl⟩

private def realArchTest (f : 𝓢ℝ) : B∞ :=
  ⟨_, real_arch_test_mem f⟩

private def realEmptyTest (f : 𝓢ℝ) :=
  sLocalStandardThetaTensor (F := ℚ) (S := ∅) 1 (realArchTest f)

private theorem realEmptyTest_apply (f : 𝓢ℝ) (x : SAdeleRing ℚ ∅) :
    realEmptyTest f (Multiplicative.ofAdd x) = f (realCoord (x.1 Rat.infinitePlace)) := by
  rw [realEmptyTest, sLocalStandardThetaTensor_apply, Fintype.prod_empty, mul_one]
  rfl

/-- A real Schwartz function at infinity, with the integer indicator at each finite place. -/
def ratStandardAdelicTest (f : 𝓢ℝ) : Bℚ :=
  sAdeleSchwartzToGlobal ℚ ∅ (realEmptyTest f)

open Classical in
/-- The finite components restrict the argument to integral finite adeles. -/
theorem ratStandardAdelicTest_apply (f : 𝓢ℝ) (x : 𝔸) :
    ratStandardAdelicTest f (Multiplicative.ofAdd x) =
      if ∀ v : HeightOneSpectrum (𝓞 ℚ), x.2 v ∈ v.adicCompletionIntegers ℚ then
        f (realCoord (x.1 Rat.infinitePlace)) else 0 := by
  rw [ratStandardAdelicTest, sAdeleSchwartzToGlobal_apply, realEmptyTest_apply]
  simp [adeleProjection]
  rfl

/-- Both global polar conditions are exactly the two real conditions for this insertion. -/
theorem ratStandardAdelicTest_polar_iff (f : 𝓢ℝ) :
    ratStandardAdelicTest f ∈ adelePolarSubspace ℚ ↔ f 0 = 0 ∧ 𝓕 f 0 = 0 := by
  rw [ratStandardAdelicTest, sAdeleSchwartzToGlobal_mem_polarSubspace_iff, realEmptyTest_apply,
    sAdeleSchwartzFourier_ratEmpty_apply f (realEmptyTest f) (realEmptyTest_apply f)]
  change (f (realCoord 0) = 0 ∧ 𝓕 f (realCoord 0) = 0) ↔ _
  rw [map_zero]

private theorem finite_integral_iff (x : ℚ) :
    (∀ v : V, (algebraMap ℚ 𝔸 x).2 v ∈ v.adicCompletionIntegers ℚ) ↔ ∃ n : ℤ, (n : ℚ) = x := by
  have h := diagonal_mem_integralAdelesOutside ℚ ∅ x
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty,
    not_false_eq_true, forall_const, Finset.coe_empty, integer_empty, Algebra.mem_bot] at h
  rw [show (∀ v : V, (algebraMap ℚ 𝔸 x).2 v ∈ v.adicCompletionIntegers ℚ) ↔
    ∃ r : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ r = x from h]
  exact ⟨fun ⟨r, hr⟩ ↦ ⟨Rat.ringOfIntegersEquiv r, (Rat.ringOfIntegersEquiv_apply_coe r).trans hr⟩,
    fun ⟨n, hn⟩ ↦ ⟨n, (map_intCast _ n).trans hn⟩⟩

private theorem finite_unit_mul_iff (x : ℚ) (g : 𝔸ˣ) (u : U)
    (hg : ∀ v, g.val.2 v = (u v).val.val) :
    (∀ v : V, ((algebraMap ℚ 𝔸 x) * g.val).2 v ∈ v.adicCompletionIntegers ℚ) ↔
      ∃ n : ℤ, (n : ℚ) = x := by
  rw [← finite_integral_iff]
  constructor
  · intro hm v
    have he : (u v).val.val * (u v).inv.val = 1 := congrArg Subtype.val (u v).val_inv
    have h := (v.adicCompletionIntegers ℚ).toSubring.mul_mem (hm v) (u v).inv.property
    change ((algebraMap ℚ 𝔸 x).2 v * g.val.2 v) * (u v).inv.val ∈ _ at h
    change (algebraMap ℚ 𝔸 x).2 v ∈ (v.adicCompletionIntegers ℚ).toSubring
    simpa only [hg, mul_assoc, he, mul_one] using h
  · intro hm v
    change (algebraMap ℚ 𝔸 x).2 v * g.val.2 v ∈ _
    rw [hg]
    exact (v.adicCompletionIntegers ℚ).toSubring.mul_mem (hm v) (u v).val.property

private theorem norm_of_integral_unit_representative (g : 𝔸ˣ) (u : U)
    (hg : ∀ v, g.val.2 v = (u v).val.val) {t : ℝ≥0ˣ}
    (ht : realCoord (g.val.1 Rat.infinitePlace) = t.val) :
    ((ideleNorm ℚ g).val : ℝ) = t.val := by
  rw [((ideleNorm_spec ℚ).1 _).2, Fintype.prod_subsingleton _ Rat.infinitePlace]
  have hfin (v : V) : ‖g.val.2 v‖ = 1 := by
    rw [hg]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    apply (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom (u v))).mp
    exact ⟨(u v).val.property, (u v).inv.property⟩
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one]
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _) (g.val.1 Rat.infinitePlace)
  change ‖realCoord (g.val.1 Rat.infinitePlace)‖ = _ at h
  rw [← h, ht]
  simp [InfinitePlace.mult, Rat.isReal_infinitePlace]

private theorem hasSum_integer_theta (f : 𝓢ℝ) (hf : f 0 = 0)
    (g : 𝔸ˣ) (u : U) (hg : ∀ v, g.val.2 v = (u v).val.val) {t : ℝ}
    (ht : realCoord (g.val.1 Rat.infinitePlace) = t) :
    HasSum (fun n : ℤ ↦ f ((n : ℝ) * t))
      (adelicTheta (ratStandardAdelicTest f) (QuotientGroup.mk g)) := by
  classical
  let F (r : ℚˣ) := ratStandardAdelicTest f (Multiplicative.ofAdd (algebraMap ℚ 𝔸 (r : ℚ) * g.val))
  let G (n : ℤ) := f ((n : ℝ) * t)
  have hterm (r : ℚˣ) : F r = if ∃ n : ℤ, (n : ℚ) = r.val then f ((r.val : ℝ) * t) else 0 := by
    dsimp only [F]
    rw [ratStandardAdelicTest_apply, finite_unit_mul_iff _ g u hg]
    congr 2
    change realCoord (algebraMap ℚ Rat.infinitePlace.Completion (r : ℚ) * g.val.1 Rat.infinitePlace) = _
    rw [map_mul, ht]
    simp
  have hG0 : G 0 = 0 := by simp [G, hf]
  let i (n : Function.support G) : ℚˣ := Units.mk0 (n.val : ℚ) (by
    exact_mod_cast (show n.val ≠ 0 from fun h ↦ n.property (h ▸ hG0)))
  have hi : Injective i := by
    intro a b h
    apply Subtype.ext
    exact_mod_cast (show (a.val : ℚ) = b.val from congrArg Units.val h)
  have hval (n : Function.support G) : F (i n) = G n.val := by
    rw [hterm, ite_eq_left (show ∃ m : ℤ, (m : ℚ) = (i n).val from ⟨n.val, rfl⟩)]
    change f (((n.val : ℚ) : ℝ) * t) = _
    simp [G]
  have hcov : Function.support F ⊆ Set.range i := by
    intro r hr
    change F r ≠ 0 at hr
    rw [hterm] at hr
    split at hr
    · rename_i h
      obtain ⟨n, hn⟩ := h
      have hG : G n ≠ 0 := by simpa [G, ← hn] using hr
      exact ⟨⟨n, hG⟩, Units.ext hn⟩
    · exact (hr rfl).elim
  rw [adelicTheta_mk]
  apply (hasSum_iff_hasSum_of_ne_zero_bij (f := F) (g := G) i hi hcov hval).mp
  apply Summable.hasSum
  have H := (adelicAverage_summableUniformlyOn (ratStandardAdelicTest f) {(g, (0 : 𝔸))}
    isCompact_singleton).summable (Set.mem_singleton (g, (0 : 𝔸)))
  exact (show Summable (fun r ↦ ‖F r‖) by simpa [F, mul_comm] using H).of_norm

/-- The actual unaveraged adelic theta on rational idele classes is twice the scalar positive
integer theta of an even test vanishing at zero. Its value depends only on the idelic norm. -/
theorem ratStandardAdelicTest_theta (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (x : Cℚ) :
    adelicTheta (ratStandardAdelicTest f) x =
      2 * ∑' n : ℕ, f (((n : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ)) := by
  obtain ⟨e, herep⟩ := ratIdeleClassGroup_decomposition
  obtain ⟨⟨t, u⟩, rfl⟩ := e.surjective x
  obtain ⟨g, harch, hfin, hclass⟩ := herep t u
  rw [hclass]
  have hnorm : ((ideleClassNorm ℚ (QuotientGroup.mk g)).val : ℝ) = t.val :=
    norm_of_integral_unit_representative g u hfin harch
  rw [hnorm]
  have hsum := hasSum_integer_theta f hf g u hfin harch
  rw [← hsum.tsum_eq, tsum_int_eq_zero_add_two_mul_tsum_pnat _ hsum.summable]
  · simp only [Int.cast_zero, zero_mul, hf, zero_add, Int.cast_natCast, nsmul_eq_mul]
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ ↦ f ((n : ℝ) * t.val))]
    simp
  · intro n
    simpa only [Int.cast_neg, neg_mul] using he ((n : ℝ) * t.val)

local instance : MeasurableSpace Cℚ := borel _
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)

/-- The trivial homogeneous average used in Chapter 10 contributes its norm-one Tamagawa
mass to the physical positive-integer theta formula. -/
theorem ratStandardAdelicTest_homogeneousTheta (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (x : Cℚ) :
    homogeneousAdelicTheta 1 (ratStandardAdelicTest f) x =
      mass * (2 * ∑' n : ℕ, f (((n : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ))) := by
  let H := (ideleClassNorm ℚ).ker
  change (∫ k : H, adelicTheta (ratStandardAdelicTest f) (k.val * x) * _ ∂_) = _
  have hr (k : H) : ideleClassNorm ℚ (k.val * x) = ideleClassNorm ℚ x := by
    rw [map_mul, show ideleClassNorm ℚ k.val = 1 from k.property, one_mul]
  simp only [ratStandardAdelicTest_theta f he hf, hr, PontryaginDual.one_apply,
    Circle.coe_one, mul_one, integral_const, Measure.real, Complex.real_smul]

/-- Above a positive norm cutoff, a one-sided support bound on the real test truncates
the actual homogeneous adelic theta to a finite sum with its exact Haar factor. -/
theorem ratStandardAdelicTest_homogeneousTheta_eq_sum (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) {B : ℝ} (hs : ∀ r : ℝ, B < r → f r = 0) (x : Cℚ) (N : ℕ)
    (hN : B < ((N : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ)) :
    homogeneousAdelicTheta 1 (ratStandardAdelicTest f) x =
      mass * (2 * ∑ n ∈ Finset.range N, f (((n : ℝ) + 1) * ((ideleClassNorm ℚ x).val : ℝ))) := by
  rw [ratStandardAdelicTest_homogeneousTheta f he hf x]
  congr 2
  apply tsum_eq_sum
  intro n hn
  apply hs
  apply hN.trans_le
  apply mul_le_mul_of_nonneg_right _ (ideleClassNorm ℚ x).val.property
  exact add_le_add_left (Nat.cast_le.mpr (Nat.le_of_not_gt (by simpa using hn))) 1

/-- A polar-free real test supported on positive norms at most one gives an actual
polar-free adelic source. Its theta vanishes at every class of norm greater than one. -/
theorem ratStandardAdelicTest_polar_of_unit_support (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (hF : 𝓕 f 0 = 0) (hs : ∀ r : ℝ, 1 < r → f r = 0) :
    ratStandardAdelicTest f ∈ adelePolarSubspace ℚ ∧
      ∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) →
        homogeneousAdelicTheta 1 (ratStandardAdelicTest f) x = 0 := by
  refine ⟨(ratStandardAdelicTest_polar_iff f).2 ⟨hf, hF⟩, fun x hx ↦ ?_⟩
  simpa using ratStandardAdelicTest_homogeneousTheta_eq_sum f he hf hs x 0 (by simpa using hx)

/-- In the rational trivial character the centered log-norm error from the indicator
is exactly the ordinary unit-interval error of the real-place positive integer series.
The parametrization can be any family of classes with prescribed norm. -/
theorem ratStandardAdelicTest_halfLine_error (f : 𝓢ℝ) (he : Function.Even (f : ℝ → ℂ))
    (hf : f 0 = 0) (g : ℝ → Cℚ) (hg : ∀ x, ((ideleClassNorm ℚ (g x)).val : ℝ) = Real.exp x) :
    (∫ x in Iic (0 : ℝ), ‖Complex.exp ((x : ℂ) / 2) -
      homogeneousAdelicTheta 1 (ratStandardAdelicTest f) (g x) * Complex.exp ((x : ℂ) / 2)‖ ^ 2) =
      ∫ r in Ioc (0 : ℝ) 1, ‖1 - mass * (2 * ∑' n : ℕ, f (((n : ℝ) + 1) * r))‖ ^ 2 := by
  let d (r : ℝ) : ℝ := ‖1 - mass * (2 * ∑' n : ℕ, f (((n : ℝ) + 1) * r))‖ ^ 2
  have changeVar := integral_image_eq_integral_abs_deriv_smul (s := Iic (0 : ℝ))
    measurableSet_Iic (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn d
  rw [Real.image_exp_Iic, Real.exp_zero] at changeVar
  rw [show (∫ r in Ioc (0 : ℝ) 1, ‖1 - mass * (2 * ∑' n : ℕ, f (((n : ℝ) + 1) * r))‖ ^ 2) =
    ∫ r in Ioc (0 : ℝ) 1, d r from rfl, changeVar]
  apply setIntegral_congr_fun measurableSet_Iic
  intro x _
  dsimp only
  rw [ratStandardAdelicTest_homogeneousTheta f he hf, hg, ← one_sub_mul,
    norm_mul, mul_pow, Complex.norm_exp]
  have hexp : Real.exp (((x : ℂ) / 2).re) ^ 2 = Real.exp x := by
    rw [← Real.exp_nat_mul]
    congr 1
    simp
    ring
  rw [hexp, abs_of_pos (Real.exp_pos x)]
  exact mul_comm _ _

private theorem ratTheta_dilationDifference (b : 𝓢ℝ) (he : Function.Even (b : ℝ → ℂ))
    (hs : ∀ r : ℝ, 1 < r → b r = 0) (k m : ℝ) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    ∃ h : 𝓢ℝ, (∀ r : ℝ, h r = (b r - (k : ℂ) * b (r * k)) -
        (b (r * m) - (k : ℂ) * b (r * m * k))) ∧
      Function.Even (h : ℝ → ℂ) ∧ h 0 = 0 ∧ 𝓕 h 0 = 0 ∧ ∀ r : ℝ, 1 < r → h r = 0 := by
  let D (q : ℝ) (hq : 0 < q) : 𝓢ℝ →L[ℂ] 𝓢ℝ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 q hq.ne'))
  have hD (q : ℝ) (hq : 0 < q) (v : 𝓢ℝ) (x : ℝ) : D q hq v x = v (x * q) := rfl
  have hDF (q : ℝ) (hq : 0 < q) (v : 𝓢ℝ) : 𝓕 (D q hq v) 0 = ((q⁻¹ : ℝ) : ℂ) * 𝓕 v 0 := by
    simp only [SchwartzMap.fourier_coe, Real.fourier_real_eq, mul_zero, neg_zero, AddChar.map_zero_eq_one,
      one_smul]
    simpa only [hD, abs_of_pos (inv_pos.mpr hq), Complex.real_smul] using
      Measure.integral_comp_mul_right (fun x : ℝ ↦ v x) q
  have hk' : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hm' : 0 < m := lt_of_lt_of_le zero_lt_one hm
  let v := b - (k : ℂ) • D k hk' b
  let h := v - D m hm' v
  have hval (r : ℝ) : h r = (b r - (k : ℂ) * b (r * k)) -
      (b (r * m) - (k : ℂ) * b (r * m * k)) := rfl
  have hfv : 𝓕 v 0 = 0 := by
    simp only [v, FourierTransform.fourier_sub, FourierTransform.fourier_smul, sub_apply, smul_apply,
      smul_eq_mul, hDF, Complex.ofReal_inv]
    rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hk'.ne'), one_mul, sub_self]
  refine ⟨h, hval, ?_, ?_, ?_, ?_⟩
  · intro r
    simp only [hval, neg_mul, he _]
  · simp [hval]
  · simp only [h, FourierTransform.fourier_sub, sub_apply, hDF, hfv, mul_zero, sub_zero]
  · intro r hr
    have hg (x q : ℝ) (hx : 1 < x) (hq : 1 ≤ q) : 1 < x * q :=
      hx.trans_le (le_mul_of_one_le_right (zero_lt_one.trans hx).le hq)
    simp [hval, hs r hr, hs _ (hg r k hr hk), hs _ (hg r m hr hm),
      hs _ (hg _ k (hg r m hr hm) hk)]

/-- Finite combinations of two dilation differences of a single even Schwartz cutoff
give genuine polar-free rational adelic tests. Their theta profiles vanish above norm
one. The pointwise formula specifies the source used for integer-dilation approximants. -/
theorem exists_ratStandardAdelicTest_dilationDifferences (b : 𝓢ℝ) (he : Function.Even (b : ℝ → ℂ))
    (hs : ∀ r : ℝ, 1 < r → b r = 0) (m : ℝ) (hm : 1 ≤ m)
    (S : Finset ℕ) (a : ℕ → ℂ) (hk : ∀ k ∈ S, 1 ≤ k) :
    ∃ h : 𝓢ℝ, (∀ r : ℝ, h r = ∑ k ∈ S, a k *
        ((b r - (k : ℂ) * b (r * k)) - (b (r * m) - (k : ℂ) * b (r * m * k)))) ∧
      Function.Even (h : ℝ → ℂ) ∧ h 0 = 0 ∧ (∀ r : ℝ, 1 < r → h r = 0) ∧
      ratStandardAdelicTest h ∈ adelePolarSubspace ℚ ∧
      ∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) → homogeneousAdelicTheta 1 (ratStandardAdelicTest h) x = 0 := by
  classical
  choose v hv hev hz hF hsup using fun (k : S) ↦ ratTheta_dilationDifference b he hs k.val m
    (by exact_mod_cast hk k.val k.property) hm
  let h : 𝓢ℝ := ∑ k : S, a k.val • v k
  have happ (r : ℝ) : h r = ∑ k : S, a k.val * v k r := by simp [h]
  have hhe : Function.Even (h : ℝ → ℂ) := by
    intro r
    simp only [happ, hev _ _]
  have hh0 : h 0 = 0 := by simp [happ, hz]
  have hhF : 𝓕 h 0 = 0 := by simp [h, hF]
  have hhs (r : ℝ) (hr : 1 < r) : h r = 0 := by simp [happ, fun k ↦ hsup k r hr]
  refine ⟨h, fun r ↦ ?_, hhe, hh0, hhs, ratStandardAdelicTest_polar_of_unit_support h hhe hh0 hhF hhs⟩
  rw [happ, ← Finset.sum_attach S]
  simp only [Finset.attach_eq_univ, hv, Complex.ofReal_natCast]

private theorem ratTheta_plateau_sum (b : ℝ → ℂ) {c r : ℝ}
    (hb : ∀ x ∈ Icc 0 c, b x = 1) (hs : ∀ x : ℝ, 1 < x → b x = 0)
    (hr : 0 ≤ r) (n k : ℕ) (hk : 0 < k) (hlo : 1 < ((n : ℝ) + 1) * r) (hhi : (n : ℝ) * r ≤ c) :
    (∑ j ∈ Finset.range n, b ((((j : ℝ) + 1) * r) * k)) = ((n / k : ℕ) : ℂ) := by
  have hcut : (∑ j ∈ Finset.range (n / k), b ((((j : ℝ) + 1) * r) * k)) =
      ∑ j ∈ Finset.range n, b ((((j : ℝ) + 1) * r) * k) := by
    apply Finset.sum_subset (Finset.range_mono (Nat.div_le_self n k))
    intro j _ hj
    apply hs
    have hj' : n / k < j + 1 := by simp only [Finset.mem_range] at hj; omega
    have hnat := (Nat.div_lt_iff_lt_mul hk).mp hj'
    have hh : (n : ℝ) + 1 ≤ ((j : ℝ) + 1) * k := by exact_mod_cast Nat.succ_le_of_lt hnat
    exact hlo.trans_le (by simpa only [mul_right_comm _ r] using mul_le_mul_of_nonneg_right hh hr)
  rw [← hcut]
  calc
    _ = ∑ _j ∈ Finset.range (n / k), (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply hb
      refine ⟨by positivity, ?_⟩
      have hnat := (Nat.le_div_iff_mul_le hk).mp (Nat.succ_le_of_lt (Finset.mem_range.mp hj))
      have hh : ((j : ℝ) + 1) * k ≤ n := by exact_mod_cast hnat
      exact (by simpa only [mul_right_comm _ r] using mul_le_mul_of_nonneg_right hh hr : _ ≤ (n : ℝ) * r).trans hhi
    _ = _ := by simp

/-- A single polar-free adelic test realizes the prescribed remainder combination on
every reciprocal interval where the smooth cutoff agrees with the sharp one. The same
test vanishes identically at norm greater than one. -/
theorem exists_ratTheta_residue_intervals (b : 𝓢ℝ) (he : Function.Even (b : ℝ → ℂ))
    {c : ℝ} (hb : ∀ r ∈ Icc 0 c, b r = 1) (hs : ∀ r : ℝ, 1 < r → b r = 0)
    (m : ℝ) (hm : 1 ≤ m) (S : Finset ℕ) (a : ℕ → ℂ) (hk : ∀ k ∈ S, 1 ≤ k) :
    ∃ f : adelePolarSubspace ℚ,
      (∀ x : Cℚ, 1 < ((ideleClassNorm ℚ x).val : ℝ) → homogeneousAdelicTheta 1 f.val x = 0) ∧
      ∀ (n : ℕ) (x : Cℚ), let r := ((ideleClassNorm ℚ x).val : ℝ)
        1 < r * m → 1 < ((n : ℝ) + 1) * r → (n : ℝ) * r ≤ c →
          homogeneousAdelicTheta 1 f.val x = mass * (2 * ∑ k ∈ S, a k * (n % k : ℕ)) := by
  obtain ⟨h, happ, hhe, hh0, hsup, hpol, hout⟩ :=
    exists_ratStandardAdelicTest_dilationDifferences b he hs m hm S a hk
  refine ⟨⟨ratStandardAdelicTest h, hpol⟩, hout, fun n x ↦ ?_⟩
  intro r hmcut hlo hhi
  rw [ratStandardAdelicTest_homogeneousTheta_eq_sum h hhe hh0 hsup x n hlo]
  congr 2
  change (∑ j ∈ Finset.range n, h (((j : ℝ) + 1) * r)) = _
  simp_rw [happ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hmem
  rw [← Finset.mul_sum]
  congr 1
  have hk' : 1 ≤ (k : ℝ) := by exact_mod_cast hk k hmem
  have hd (j : ℕ) : 1 < (((j : ℝ) + 1) * r) * m := by
    rw [mul_assoc]
    exact hmcut.trans_le (le_mul_of_one_le_left (zero_lt_one.trans hmcut).le (by linarith [Nat.cast_nonneg (α := ℝ) j]))
  have hdk (j : ℕ) : 1 < (((j : ℝ) + 1) * r) * m * k :=
    (hd j).trans_le (le_mul_of_one_le_right (zero_lt_one.trans (hd j)).le hk')
  simp only [hs _ (hd _), hs _ (hdk _), mul_zero, sub_zero]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h1 := ratTheta_plateau_sum b hb hs (ideleClassNorm ℚ x).val.property n 1 (by decide) hlo hhi
  have hkstep := ratTheta_plateau_sum b hb hs (ideleClassNorm ℚ x).val.property n k (hk k hmem) hlo hhi
  simp only [Nat.cast_one, mul_one, Nat.div_one] at h1
  change (∑ j ∈ Finset.range n, b (((j : ℝ) + 1) * r)) = (n : ℂ) at h1
  change (∑ j ∈ Finset.range n, b ((((j : ℝ) + 1) * r) * k)) = ((n / k : ℕ) : ℂ) at hkstep
  rw [h1, hkstep]
  have hnat := Nat.mod_add_div n k
  exact sub_eq_of_eq_add (by exact_mod_cast hnat.symm)

end RiemannMasullo
