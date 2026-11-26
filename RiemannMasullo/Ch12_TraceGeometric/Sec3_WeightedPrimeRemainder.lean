module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_MovingPrimeLevel
import Mathlib.NumberTheory.LSeries.PrimesInAP
import RiemannMasullo.ForMathlib.Analysis.Fourier.SparseLaplaceProbe
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Tactic

/-! # Integrable error after the first prime shell

Prime squares and higher powers have finite translated mass for every positive
width. For a profile supported away from the origin, the archimedean remainder
has bounded mass along the positive translates. -/

@[expose] public noncomputable section
open Classical Filter Function MeasureTheory Set
open scoped ArithmeticFunction ENNReal NNReal Topology
namespace RiemannMasullo

/-- Absolute Dirichlet mass of the higher prime powers at every real exponent strictly
larger than one half. Only prime bases with exponent at least two contribute. -/
theorem summable_higher_primePower_weight {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ ↦ (if n.Prime then 0 else Λ n) * Real.exp (-(1+a)/2*Real.log n)) := by
  let s := (1+a)/2
  have hs : 0 < s := by dsimp [s]; linarith
  let F (n : ℕ) := (if n.Prime then 0 else Λ n)*Real.exp (-s*Real.log n)
  let e (j : Nat.Primes × ℕ) : ℕ := j.1.val^(j.2+2)
  have hi : Injective e := by
    intro i j h
    obtain ⟨hp,hk⟩ := i.1.property.pow_inj j.1.property h
    exact Prod.ext (Subtype.ext hp) (by omega)
  have hup : support F ⊆ range e := by
    intro n hn
    have hnot : ¬n.Prime := fun h ↦ hn (by simp [F,h])
    have hΛ : Λ n ≠ 0 := fun h ↦ hn (by simp [F,h])
    obtain ⟨p,k,hp,hk,rfl⟩ := (isPrimePow_nat_iff n).mp (by_contra fun h ↦ hΛ (ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr h))
    have hk₁ : k ≠ 1 := by rintro rfl; exact hnot (by simpa using hp)
    refine ⟨(⟨p,hp⟩,k-2),?_⟩
    dsimp [e]; congr 1; omega
  rw [show -(1+a)/2 = -s by dsimp [s]; ring]
  change Summable F
  apply (hi.summable_iff (f := F) (fun x hx ↦ notMem_support.mp (fun h ↦ hx (hup h)))).mp
  let r := Real.exp (-s * Real.log 2)
  have hr : 0 < r := Real.exp_pos _
  have hr₁ : r < 1 := Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr hs) (Real.log_pos (by norm_num)))
  let A (p : Nat.Primes) := (p.val:ℝ)^(-1-a/2) / (a/2)
  have hA : Summable A := (Nat.Primes.summable_rpow.mpr (by linarith : -1-a/2 < -1)).div_const _
  have hA₀ (p) : 0 ≤ A p := by dsimp [A]; positivity
  have hprod : Summable (fun j : Nat.Primes × ℕ ↦ A j.1*r^j.2) :=
    (summable_prod_of_nonneg (fun j ↦ mul_nonneg (hA₀ j.1) (pow_nonneg hr.le _))).mpr
      ⟨fun p ↦ (summable_geometric_of_lt_one hr.le hr₁).mul_left (A p),
        (hA.mul_right (∑' k : ℕ, r^k)).congr fun p ↦ by dsimp only; rw [tsum_mul_left]⟩
  apply hprod.of_nonneg_of_le
  · intro j
    dsimp only [Function.comp_apply,F]
    split_ifs <;> positivity [ArithmeticFunction.vonMangoldt_nonneg (n := e j)]
  rintro ⟨p,k⟩
  have hp : 0 < (p.val:ℝ) := by exact_mod_cast p.property.pos
  have hp2 : 2 ≤ (p.val:ℝ) := by exact_mod_cast p.property.two_le
  have hl := Real.log_le_rpow_div hp.le (half_pos ha)
  have hlog : Real.log 2 ≤ Real.log p.val := Real.log_le_log (by norm_num) hp2
  have hmain : (p.val:ℝ)^(a/2) * Real.exp (-s*(2*Real.log p.val)) = (p.val:ℝ)^(-1-a/2) := by
    rw [Real.rpow_def_of_pos hp,Real.rpow_def_of_pos hp,← Real.exp_add]
    congr 1; dsimp [s]; ring
  have htail : Real.exp (-s*(k*Real.log p.val)) ≤ r^k := by
    rw [show r^k = Real.exp ((k:ℝ)*(-s*Real.log 2)) by rw [Real.exp_nat_mul]]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_left hlog (mul_nonneg hs.le (Nat.cast_nonneg k))]
  have hnp : ¬(p.val^(k+2)).Prime := Nat.Prime.not_prime_pow (by omega)
  change F (p.val^(k+2)) ≤ A p * r^k
  simp only [F,hnp,ite_false,ArithmeticFunction.vonMangoldt_apply_pow (by omega : k+2 ≠ 0),
    ArithmeticFunction.vonMangoldt_apply_prime p.property,Nat.cast_pow,Real.log_pow]
  rw [show -s * ((↑(k+2) : ℝ)*Real.log p.val) =
    -s*(2*Real.log p.val) + -s*(k*Real.log p.val) by push_cast; ring, Real.exp_add]
  calc
    _ ≤ ((p.val:ℝ)^(a/2)/(a/2))*(Real.exp (-s*(2*Real.log p.val))*r^k) :=
      mul_le_mul hl (mul_le_mul_of_nonneg_left htail (Real.exp_pos _).le) (by positivity) (by positivity)
    _ = _ := by dsimp [A]; rw [← hmain]; ring

private theorem integrable_translated_series (U : ℝ → ℂ) (hU : Continuous U)
    (hk : HasCompactSupport U) (t c : ℕ → ℝ) (hc : Summable c) (hpos : ∀ n, 0 ≤ c n) :
    Integrable (fun y : ℝ ↦ ∑' n, (c n : ℂ)*U (t n-y)) := by
  obtain ⟨B,hB⟩ := hk.exists_bound_of_continuous hU
  let P (n : ℕ) (y : ℝ) := (c n : ℂ)*U (t n-y)
  have hP (n) : Continuous (P n) := continuous_const.mul (hU.comp (continuous_const.sub continuous_id))
  have hcont : Continuous (fun y ↦ ∑' n, P n y) :=
    continuous_tsum hP (hc.mul_right B) fun n y ↦ by
      change ‖(c n : ℂ)*U (t n-y)‖ ≤ _
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hpos n)]
      exact mul_le_mul_of_nonneg_left (hB _) (hpos n)
  refine ⟨hcont.aestronglyMeasurable,?_⟩
  rw [hasFiniteIntegral_iff_eNorm]
  apply lt_of_le_of_lt (lintegral_mono (fun y ↦ eNorm_tsum_le_tsum_eNorm (f := fun n ↦ P n y)))
  rw [lintegral_tsum (f := fun n y ↦ ‖P n y‖ₑ) (fun n ↦ (hP n).measurable.eNorm.aemeasurable)]
  have he (n) : (∫⁻ y : ℝ, ‖P n y‖ₑ) = ENNReal.ofReal (c n) * ∫⁻ x : ℝ, ‖U x‖ₑ := by
    have hv : ‖(c n : ℂ)‖ₑ = ENNReal.ofReal (c n) := by
      rw [← ofReal_norm,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hpos n)]
    simp only [P,eNorm_mul,hv]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    exact ((volume : Measure ℝ).measurePreserving_sub_left (t n)).lintegral_comp_emb
      (MeasurableEquiv.subLeft (t n)).measurableEmbedding (fun x ↦ ‖U x‖ₑ)
  simp_rw [he]
  rw [ENNReal.tsum_mul_right]
  exact ENNReal.mul_lt_top hc.tsum_ofReal_lt_top (hU.integrable_of_hasCompactSupport hk).hasFiniteIntegral

private theorem sample_eq_exp (n : ℕ) (hn : n ≠ 0) :
    (Real.sqrt (n:ℝ))⁻¹ = Real.exp (-Real.log n/2) := by
  rw [neg_div,Real.exp_neg,Real.exp_half,Real.exp_log (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))]

/-- The higher prime powers of a translated compact test are absolutely integrable
in the critical detector for every positive weight, including weights arbitrarily
close to zero. The prime squares are included. -/
theorem integrable_weighted_higherPrimePowers {a : ℝ} (ha : 0 < a)
    (H : ℝ → ℂ) (hH : Continuous H) (hk : HasCompactSupport H) :
    Integrable (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) *
      ∑' n : ℕ, (((if n.Prime then 0 else Λ n)/Real.sqrt n : ℝ):ℂ) * H (Real.log n-y)) := by
  let U (x : ℝ) := (Real.exp (a*x/2):ℂ)*H x
  let c (n : ℕ) := (if n.Prime then 0 else Λ n)*Real.exp (-(1+a)/2*Real.log n)
  have hpos (n) : 0 ≤ c n := by dsimp [c]; split_ifs <;> positivity [ArithmeticFunction.vonMangoldt_nonneg (n := n)]
  have h := integrable_translated_series U ((by fun_prop : Continuous (fun x : ℝ ↦ (Real.exp (a*x/2):ℂ))).mul hH)
    hk.mul_left (fun n ↦ Real.log n) c (summable_higher_primePower_weight ha) hpos
  apply h.congr
  filter_upwards with y
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  by_cases hn : n = 0
  · subst n; simp [c,U]
  have he : Real.exp (-(1+a)/2*Real.log n) * Real.exp (a*(Real.log n-y)/2) =
      Real.exp (-a*y/2) * (Real.sqrt n)⁻¹ := by
    rw [sample_eq_exp n hn,← Real.exp_add,← Real.exp_add]; congr 1; ring
  simp only [c,U,Complex.ofReal_mul,Complex.ofReal_div]
  have he' := congrArg Complex.ofReal he
  simp only [Complex.ofReal_mul,Complex.ofReal_inv] at he'
  linear_combination ((if n.Prime then 0 else Λ n : ℝ):ℂ)*H (Real.log n-y)*he'

private theorem prime_split (H : ℝ → ℂ) {u : ℝ} (hu : ∀ x, u < x → H x = 0) :
    (∑' n : ℕ, ((Λ n/Real.sqrt n : ℝ):ℂ)*H (Real.log n)) =
      rationalFirstPrimeSum H + ∑' n : ℕ, (((if n.Prime then 0 else Λ n)/Real.sqrt n : ℝ):ℂ)*H (Real.log n) := by
  let f (n : ℕ) := ((Λ n/Real.sqrt n : ℝ):ℂ)*H (Real.log n)
  have hs : (support f).Finite := by
    apply (finite_Iic (⌈Real.exp u⌉₊ : ℕ)).subset
    intro n hn
    rcases eq_or_ne n 0 with rfl|h
    · exact Nat.zero_le _
    have hlog : Real.log n ≤ u := by
      by_contra! hx
      exact hn (by simp [f,hu _ hx])
    exact_mod_cast ((Real.log_le_iff_le_exp (Nat.cast_pos.mpr (Nat.pos_of_ne_zero h))).mp hlog).trans (Nat.le_ceil _)
  let primes : Set ℕ := {n | n.Prime}
  have hsum : Summable f := summable_of_hasFiniteSupport hs
  have hp : (∑' p : primes, f p.val) = rationalFirstPrimeSum H := by
    apply tsum_congr
    intro p
    simp only [f,ArithmeticFunction.vonMangoldt_apply_prime p.property]
  have hr : (∑' j : ↑primesᶜ, f j.val) =
      ∑' n : ℕ, (((if n.Prime then 0 else Λ n)/Real.sqrt n : ℝ):ℂ)*H (Real.log n) := by
    rw [tsum_subtype]
    apply tsum_congr
    intro n
    by_cases hn : n.Prime <;> simp [primes,f,hn]
  exact (hsum.tsum_subtype_add_tsum_subtype_compl primes).symm.trans (congrArg₂ (·+·) hp hr)

private theorem integrable_weighted_arch {a l : ℝ} (ha : 0 < a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : Continuous H) (hk : HasCompactSupport H) (hz : ∀ x, x < l → H x = 0) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) *
      ∫ x in Ioi (0:ℝ), (Real.exp (-x/2):ℂ)*H (x-y)/((Real.exp (2*x):ℂ)-1)) (Ioi 0) := by
  let f (y x : ℝ) : ℂ := (Real.exp (-x/2):ℂ)*H (x-y)/((Real.exp (2*x):ℂ)-1)
  obtain ⟨B,hB⟩ := hk.exists_bound_of_continuous hH
  let d := Real.exp (2*l)-1
  have hd : 0 < d := sub_pos.mpr (Real.one_lt_exp_iff.mpr (by linarith))
  have hB₀ : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let b (x : ℝ) := Real.exp (-(1/2)*x)*(B/d)
  have hb : IntegrableOn b (Ioi 0) := (integrableOn_exp_mul_Ioi (a := -(1/2)) (by norm_num) 0).mul_const _
  have hf : Measurable (Function.uncurry f) := by
    dsimp [f,Function.uncurry]
    fun_prop
  have hbound {y : ℝ} (hy : 0 ≤ y) (x : ℝ) : ‖f y x‖ ≤ b x := by
    dsimp [f,b]
    rw [show -x/2 = -(1/2)*x by ring]
    by_cases hx : x-y < l
    · rw [hz _ hx,mul_zero,zero_div,norm_zero]; positivity
    have hx' : d ≤ Real.exp (2*x)-1 := sub_le_sub_right (Real.exp_le_exp.mpr (by linarith)) _
    rw [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
      ← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hd.trans_le hx')]
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (div_le_div₀ hB₀ (hB _) hd hx') (Real.exp_pos _).le
  let K := ∫ x in Ioi (0:ℝ), b x
  have hh : ∀ y ∈ Ioi (0:ℝ), ‖∫ x in Ioi (0:ℝ), f y x‖ ≤ K := by
    intro y hy
    exact norm_integral_le_of_norm_le hb (ae_of_all _ (hbound (le_of_lt hy)))
  have hmeas := hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Ioi (0:ℝ)))
  refine ((integrableOn_exp_mul_Ioi (a := -a/2) (by linarith) 0).mul_const K).mono' ?_ ?_
  · exact ((by fun_prop : Measurable (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ))).mul hmeas.measurable).aestronglyMeasurable
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),
    show -a*y/2 = -a/2*y by ring]
  exact mul_le_mul_of_nonneg_left (hh y hy) (Real.exp_pos _).le

/-- After subtracting the translated polar term the higher prime powers and real-place
remainder have finite total critical mass for every compact positive-log test. -/
theorem integrable_weighted_centered_add_first_sub_pole {a l u : ℝ} (ha : 0 < a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : Continuous H) (hb : tsupport H ⊆ Icc l u) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) *
      (centeredVonMangoldtValue (fun x ↦ H (x-y)) + rationalFirstPrimeSum (fun x ↦ H (x-y)) -
        bilateralLaplace (fun x ↦ H (x-y)) (1/2))) (Ioi 0) := by
  have hk := isCompact_Icc.of_isClosed_subset (isClosed_tsupport H) hb
  have hz {x} (hx : x < l) : H x = 0 := by
    by_contra hh
    exact hx.not_ge (hb (subset_tsupport H hh)).1
  have hh := (integrable_weighted_higherPrimePowers ha H hH hk).integrableOn (s := Ioi 0)
  have hA := integrable_weighted_arch ha hl H hH hk (fun _ ↦ hz)
  apply (hh.add hA).neg.congr
  filter_upwards with y
  have hi (x : ℝ) (hx : u+y < x) : H (x-y) = 0 := by
    by_contra hn
    linarith [(hb (subset_tsupport H hn)).2]
  dsimp only [Pi.neg_apply,Pi.add_apply]
  rw [centeredVonMangoldtValue,
    prime_split (u := u+y) (fun x ↦ H (x-y)) hi]
  ring

/-- For each positive width, the translated centered explicit formula plus its
first-prime sum has integrable critical weight once the positive pole is killed. -/
theorem integrable_weighted_centered_add_first {a l u : ℝ} (ha : 0 < a) (hl : 0 < l)
    (H : ℝ → ℂ) (hH : Continuous H) (hb : tsupport H ⊆ Icc l u)
    (hp : bilateralLaplace H (1/2) = 0) :
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) *
      (centeredVonMangoldtValue (fun x ↦ H (x-y)) + rationalFirstPrimeSum (fun x ↦ H (x-y)))) (Ioi 0) := by
  simpa only [SparseLaplace.bilateralLaplace_translate,hp,zero_mul,sub_zero] using
    integrable_weighted_centered_add_first_sub_pole ha hl H hH hb


end RiemannMasullo
