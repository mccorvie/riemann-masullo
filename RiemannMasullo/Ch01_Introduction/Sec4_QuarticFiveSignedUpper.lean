module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.QuarticFiveAbel
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeSignedHeight
public import RiemannMasullo.Ch13_ZerosHecke.Targets
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

/-! # A finite signed-prefix upper bound for the quartic character of conductor five

David Platt verified the positive-height windows for the character and its inverse in
*Numerical computations concerning the GRH*, Math. Comp. 85 (2016), Theorem 9.1 of the
accepted manuscript.
The two windows are explicit hypotheses. The real-axis estimates, conjugation and both
finite prime-power prefix bounds are proved here. -/

@[expose] public noncomputable section

open Complex Filter Function Metric NumberField Set
open NumberFieldKB.Chebotarev.RatIdele
open scoped NNReal Topology

namespace RiemannMasullo.QuarticFive
open HeckeHalfPlaneJensen HalfPlaneJensen HeckeDiskNormalization HeckeLaguerre SignedFrequency

local notation "CF" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

/-- The idelic lift given by the value of the quartic character on rational idele classes. -/
def idelicCharacter : PontryaginDual CF :=
  let η : HeckeCharacter (𝓞 ℚ) ℚ := ⟨(Units.coeHom ℂ).comp (ratDirichletChar 5 character).toMonoidHom,
    Units.continuous_val.comp (ratDirichletChar 5 character).continuous⟩
  unitaryHeckeCharacterToPontryaginDual η (by
    intro g
    obtain ⟨y,rfl⟩ := QuotientGroup.mk_surjective g
    change ‖((ideleChar 5 character y : ℂˣ) : ℂ)‖=1
    rw [coe_ideleChar, norm_inv, MulChar.coe_toUnitHom, _root_.DirichletCharacter.unit_norm_eq_one, inv_one])

/-- The rational idelic lift has finite order and the prescribed ordinary Euler series. -/
theorem idelic_input :
    IsOfFinOrder idelicCharacter ∧ ∀ s : Hp, character.LFunction s = finiteHeckeL idelicCharacter s := by
  obtain ⟨ψ,hfin,hval,hEuler⟩ := DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values
    (primitive character character_two)
  have heq : ψ=idelicCharacter := by
    ext1 g
    obtain ⟨y,rfl⟩ := QuotientGroup.mk_surjective g
    exact Circle.ext (hval y)
  subst ψ
  exact ⟨hfin, fun s ↦ (character.LFunction_eq_LSeries s.property).trans (hEuler s s.property).symm⟩

/-- The local uniformizer at two detects the nontrivial idelic character. -/
theorem idelic_ne_one : idelicCharacter ≠ 1 := by
  let v := placeOf 2 Nat.prime_two
  have hp : pr v=2 := pr_placeOf _ _
  have hπ : Valued.v (2 : v.adicCompletion ℚ) = WithZero.exp (-1) := by
    simpa [hp] using valued_prime v Nat.prime_two
  have hn : (2 : v.adicCompletion ℚ) ≠ 0 := by
    intro h
    rw [h, map_zero] at hπ
    exact WithZero.exp_ne_zero hπ.symm
  let π := Units.mk0 (2 : v.adicCompletion ℚ) hn
  have h := ideleChar_uniformizer 5 character (v:=v) (by norm_num [hp]) π hπ
  rw [hp] at h
  change (idelicCharacter (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v π)) : ℂ) = I at h
  intro he
  rw [he] at h
  simpa using congrArg Complex.re h

/-- A finite-order character is trivial on the image of every homomorphism from the positive
real units. This includes every choice of norm section. -/
theorem idelic_normalized (τ : ℝ≥0ˣ →ₜ* CF) (t : ℝ≥0ˣ) : idelicCharacter (τ t) = 1 := by
  obtain ⟨k,hk,h⟩ := idelic_input.1.exists_pow_eq_one
  let y : ℝ≥0ˣ := Units.mk0 ((t : ℝ≥0)^((k:ℝ)⁻¹)) (NNReal.rpow_pos (Units.zero_lt t)).ne'
  have hy : y^k=t := Units.ext (NNReal.rpow_inv_natCast_pow _ hk.ne')
  rw [← hy, map_pow, map_pow]
  exact (ContinuousMonoidHom.pow_apply (idelicCharacter : CF →ₜ* Circle) k (τ y)).symm.trans
    (congrArg (fun ψ : PontryaginDual CF ↦ ψ (τ y)) h)

/-- The normalized ordinary disk used by the finite moment is literally the classical
Dirichlet continuation in Cayley coordinates. -/
theorem cleared_eq (z : ℂ) : clearedDisk idelicCharacter character.LFunction z = character.LFunction (toHalf z) := by
  have hnf : MeromorphicNFOn character.LFunction univ :=
    fun s _ ↦ ((_root_.DirichletCharacter.differentiable_LFunction (ne_one character character_two)).analyticAt s).meromorphicNFAt
  rw [clearedDisk, cleared, show halfFactor idelicCharacter = (1 : ℂ → ℂ) by ext; simp [halfFactor, idelic_ne_one],
    one_mul, toMeromorphicNFOn_eq_self.mpr hnf]

/-- The portion of Platt's published positive-height computation used by the estimate. -/
def PositiveWindow (χ : DirichletCharacter ℂ 5) : Prop :=
  ∀ s : ℂ, 1/2 < s.re → s.re < 1 → 0 < s.im → s.im < 20000000 → χ.LFunction s ≠ 0

private def normSection : ℝ≥0ˣ →ₜ* CF :=
  let quotient : IdeleGroup (𝓞 ℚ) ℚ →ₜ* CF :=
    ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  quotient.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩

private theorem normSection_rightInverse : RightInverse normSection (ideleClassNorm ℚ) :=
  canonicalIdeleNormSection_rightInverse ℚ

private theorem character_meromorphicNF : MeromorphicNFOn character.LFunction univ :=
  fun s _ ↦ ((_root_.DirichletCharacter.differentiable_LFunction
    (ne_one character character_two)).analyticAt s).meromorphicNFAt

private theorem cleared_bound (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
    ‖(1-z)*clearedDisk idelicCharacter character.LFunction z‖ ≤ 9/2 := by
  rw [cleared_eq]
  exact norm_one_sub_mul_LFunction_le character character_two (mem_ball_zero_iff.mp hz)

private theorem cleared_center : 15/16 ≤ ‖clearedDisk idelicCharacter character.LFunction 0‖ := by
  rw [cleared_eq, show toHalf 0=2 by simp [toHalf]]
  exact center_lower character character_two

/-- Two positive-height certificates preclude right-hand zeros for a single fixed character
at both signs of the ordinate. -/
theorem height_of_positive_windows (hχ : PositiveWindow character) (hbar : PositiveWindow character⁻¹) :
    ∀ w : RightSite idelicCharacter, 20000000 ≤ |w.val.im| := by
  intro w
  by_contra! hlo
  have hr := w.property.2
  have hu := (HeckePoisson.positive_divisor_re_mem_Ioo idelicCharacter w.property.1).2
  have hzero := (clearedDisk_eq_zero_iff normSection normSection_rightInverse idelicCharacter
    (idelic_normalized normSection) character.LFunction character_meromorphicNF idelic_input.2 (toDisk_lt hr)).mpr
    (by rw [toHalf_toDisk (disk_den hr)]; exact w.property.1)
  rw [cleared_eq, toHalf_toDisk (disk_den hr)] at hzero
  rcases lt_trichotomy 0 w.val.im with hpos | hz | hneg
  · exact (hχ w.val hr hu hpos (by rwa [abs_of_pos hpos] at hlo)) hzero
  · have hreal : (w.val.re : ℂ) = w.val := Complex.ext rfl (by simpa using hz)
    have hpos := real_part_pos character character_two (r:=w.val.re) (by linarith)
    rw [hreal, hzero] at hpos
    exact (lt_irrefl _) hpos
  · have hconj := inverse_LFunction_conj character character_two (s:=w.val) (by linarith)
    rw [hzero, map_zero] at hconj
    exact (hbar ((starRingEnd ℂ) w.val) hr hu (by simpa using hneg)
      (by rwa [Complex.conj_im, ← abs_of_neg hneg])) hconj

/-- The only external inputs are the published positive-height zero verifications for the
quartic character and its inverse. The raw sum uses exactly the cutoff `25^n`. -/
theorem moments_of_positive_windows (hχ : PositiveWindow character) (hbar : PositiveWindow character⁻¹)
    {n : ℕ} (hn : 0<n) (hN : n≤44444444444444) :
    |actualMoment idelicCharacter character.LFunction n - 1| < (96/25)*n ∧
    |finiteMoment idelicCharacter n (25^n)-1| < (146/25)*n := by
  exact abs_fin25_sub_one_lt_of_quartic_data normSection normSection_rightInverse idelicCharacter
    (idelic_normalized normSection) character.LFunction character_meromorphicNF idelic_input.2
    (height_of_positive_windows hχ hbar) cleared_bound cleared_center hn hN

private theorem prefix_le_of_centered_bound (E e : ℕ → ℝ) {A : ℝ} (hA : 0 ≤ A)
    (he : ∀ j, |e j| ≤ 1) {N : ℕ} (hE : ∀ j, 0 < j → j ≤ N → |E j - 1| ≤ A*j) :
    positivePrefix (fun j ↦ e j * E j) N ≤ 1 + (N : ℝ) + (A/2)*N*((N : ℝ)+1) := by
  induction N with
  | zero => simp [positivePrefix]
  | succ k ih =>
    have prev := ih (fun j hj hjk ↦ hE j hj (Nat.le_succ_of_le hjk))
    have hlast := hE (k+1) (Nat.succ_pos _) le_rfl
    have hmag : |E (k+1)| ≤ 1 + A*((k+1 : ℕ) : ℝ) := by
      have h := abs_add_le (E (k+1)-1) 1
      rw [sub_add_cancel, abs_one] at h
      linarith
    have hpart : max 0 (e (k+1)*E (k+1)) ≤ 1 + A*((k+1 : ℕ) : ℝ) := by
      refine max_le (by positivity) ((le_abs_self _).trans ?_)
      rw [abs_mul]
      exact ((mul_le_mul_of_nonneg_right (he _) (abs_nonneg _)).trans_eq (one_mul _)).trans hmag
    simp only [positivePrefix, Finset.sum_range_succ, Nat.cast_succ] at prev hpart ⊢
    linarith

/-- The coefficient bound gives a polynomial upper bound for either signed raw prefix,
including a sign selected independently at each index. -/
theorem prefix_of_positive_windows (hχ : PositiveWindow character) (hbar : PositiveWindow character⁻¹)
    {N : ℕ} (hN : N≤44444444444444) (e : ℕ → ℝ) (he : ∀ j, |e j|≤1) :
    positivePrefix (fun j ↦ e j * finiteMoment idelicCharacter j (25^j)) N ≤
      1+(N:ℝ)+(73/25)*(N:ℝ)*((N:ℝ)+1) := by
  have h := prefix_le_of_centered_bound (fun j ↦ finiteMoment idelicCharacter j (25^j)) e
    (by norm_num : (0 : ℝ) ≤ 146/25) he (N := N)
    (fun j hj hjN ↦ (moments_of_positive_windows hχ hbar hj (hjN.trans hN)).2.le)
  convert h using 1
  ring

/-- Every positive index has an explicit envelope, without a finite index cutoff. -/
theorem quartic_moment_envelope (hχ : PositiveWindow character) (hbar : PositiveWindow character⁻¹)
    {n : ℕ} (hn : 0<n) :
    |actualMoment idelicCharacter character.LFunction n - 1| ≤
      2*n*Real.log (24/5)*Real.exp (3*n/800000000000000) := by
  have h := abs_actualMoment_sub_one_of_verified_height normSection normSection_rightInverse
    idelicCharacter (idelic_normalized normSection) character.LFunction character_meromorphicNF
    idelic_input.2 (by norm_num : (0 : ℝ) < 20000000) (height_of_positive_windows hχ hbar)
    cleared_bound (by norm_num : (0 : ℝ) < 15/16) cleared_center hn
  norm_num only [show ((9/2)/(15/16):ℝ)=24/5 by norm_num] at h
  exact h

/-- A weaker slope reaches 300 trillion strictly positive indices. -/
theorem abs_raw_lt_twelve (hχ : PositiveWindow character) (hbar : PositiveWindow character⁻¹)
    {n : ℕ} (hn : 0<n) (hnT : n≤300000000000000) :
    |finiteMoment idelicCharacter n (25^n)-1| < 12*n := by
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have hnB : (n:ℝ)≤300000000000000 := by exact_mod_cast hnT
  have hlog : Real.log (24/5) < 8/5 := by
    apply (Real.log_lt_iff_lt_exp (by norm_num : (0:ℝ)<24/5)).mpr
    refine lt_of_lt_of_le ?_ (Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ)≤8/5) 5)
    norm_num [Finset.sum_range_succ,Nat.factorial]
  have he8 : Real.exp (1/8)<8/7 := by
    convert Real.exp_bound_div_one_sub_of_interval' (by norm_num : (0:ℝ)<1/8) (by norm_num : (1:ℝ)/8<1) using 1
    norm_num
  have he : Real.exp (3*(n:ℝ)/800000000000000) < 25/8 := by
    calc
      _ ≤ Real.exp (1+1/8) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp 1*Real.exp (1/8) := Real.exp_add _ _
      _ < (68/25)*(8/7) := mul_lt_mul_of_pos_of_nonneg'
        (Real.exp_one_lt_d9.trans (by norm_num)) he8.le (Real.exp_pos _) (by norm_num)
      _ < _ := by norm_num
  have hm : |actualMoment idelicCharacter character.LFunction n-1| < 10*n := by
    refine (quartic_moment_envelope hχ hbar hn).trans_lt ?_
    calc
      2*(n:ℝ)*Real.log (24/5)*Real.exp (3*(n:ℝ)/800000000000000) <
        (2*(n:ℝ)*(8/5))*(25/8) := mul_lt_mul_of_pos_of_nonneg'
          (mul_lt_mul_of_pos_left hlog (by positivity)) he.le (Real.exp_pos _) (by positivity)
      _ = _ := by ring
  have ht := abs_actualMoment_sub_fin25 idelicCharacter character.LFunction
    character_meromorphicNF idelic_input.2 hn
  rw [Module.finrank_self,abs_sub_comm (actualMoment idelicCharacter character.LFunction n)] at ht
  norm_num at ht
  have hsum := abs_add_le
    (finiteMoment idelicCharacter n (25^n) - actualMoment idelicCharacter character.LFunction n)
    (actualMoment idelicCharacter character.LFunction n - 1)
  rw [sub_add_sub_cancel] at hsum
  linarith

/-- A quadratic bound for an arbitrary signed prefix through 300 trillion. -/
theorem prefix_three_hundred_trillion (hχ : PositiveWindow character) (hbar : PositiveWindow character⁻¹)
    {N : ℕ} (hN : N≤300000000000000) (e : ℕ → ℝ) (he : ∀ j, |e j|≤1) :
    positivePrefix (fun j ↦ e j * finiteMoment idelicCharacter j (25^j)) N ≤
      1+(N:ℝ)+6*(N:ℝ)*((N:ℝ)+1) := by
  have h := prefix_le_of_centered_bound (fun j ↦ finiteMoment idelicCharacter j (25^j)) e
    (by norm_num : (0 : ℝ) ≤ 12) he (N := N)
    (fun j hj hjN ↦ (abs_raw_lt_twelve hχ hbar hj (hjN.trans hN)).le)
  convert h using 1
  ring

end RiemannMasullo.QuarticFive
