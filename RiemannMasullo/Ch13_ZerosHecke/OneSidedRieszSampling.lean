module

public import RiemannMasullo.AppB_AnalyticNT.Sec6

/-!
# Lower bounds for signed prime sums sampled at fourth powers

The linear interpolation of a first Riesz mean between two integer cutoffs is exact
on all earlier terms. At most the intervening coefficients contribute to its error.
For the degree-one Hecke prime coefficients the error on a fourth-power interval
has size at most a constant times `x √x log(2x)`.
-/

@[expose] public noncomputable section

open NumberField Set
open scoped Classical

namespace RiemannMasullo

/-- The first Riesz mean of a real sequence, with positive integer indices. -/
def integerFirstRieszMean (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * (x - n)

private theorem integerFirstRieszMean_eq_sum_max (a : ℕ → ℝ) {x : ℝ} {v : ℕ}
    (hx : 0 ≤ x) (hv : x ≤ v) :
    integerFirstRieszMean a x = ∑ n ∈ Finset.Ioc 0 v, a n * max (x - n) 0 := by
  unfold integerFirstRieszMean
  have hsub : Finset.Ioc 0 ⌊x⌋₊ ⊆ Finset.Ioc 0 v := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1,
      (Finset.mem_Ioc.mp hn).2.trans (Nat.floor_le_of_le hv)⟩
  calc
    _ = ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, a n * max (x - n) 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [max_eq_left (sub_nonneg.mpr ((Nat.le_floor_iff hx).mp (Finset.mem_Ioc.mp hn).2))]
    _ = _ := Finset.sum_subset hsub (by
      intro n hn hn'
      have hnx : ¬ (n : ℝ) ≤ x := fun h ↦ hn' (Finset.mem_Ioc.mpr
        ⟨(Finset.mem_Ioc.mp hn).1, (Nat.le_floor_iff hx).mpr h⟩)
      rw [max_eq_right (sub_nonpos.mpr (le_of_not_ge hnx)), mul_zero])

private theorem integerFirstRieszMean_chord_term {u v n : ℕ} {x t : ℝ}
    (hu : (u : ℝ) ≤ x) (hv : x ≤ v) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hc : x = (1-t)*u + t*v) (hn : n ≤ v) :
    |max (x-n) 0 - ((1-t)*max ((u:ℝ)-n) 0 + t*max ((v:ℝ)-n) 0)| ≤
      if u < n then (v:ℝ)-u else 0 := by
  have hn' : (n : ℝ) ≤ v := by exact_mod_cast hn
  rw [max_eq_left (sub_nonneg.mpr hn')]
  by_cases h : u < n
  · rw [ite_eq_left h, max_eq_right (sub_nonpos.mpr (show (u:ℝ) ≤ n by exact_mod_cast h.le)), mul_zero, zero_add, abs_le]
    have hnu : (u : ℝ) ≤ n := by exact_mod_cast h.le
    have h₁ : max (x-n) 0 ≤ (v:ℝ)-u := max_le (by linarith) (by linarith)
    have h₂ : t*((v:ℝ)-n) ≤ (v:ℝ)-u :=
      (mul_le_of_le_one_left (sub_nonneg.mpr hn') ht').trans (by linarith)
    constructor <;> linarith [le_max_right (x-n) 0, mul_nonneg ht (sub_nonneg.mpr hn')]
  · have hnu : (n : ℝ) ≤ u := by exact_mod_cast le_of_not_gt h
    rw [ite_eq_right h, max_eq_left (sub_nonneg.mpr (hnu.trans hu)), max_eq_left (sub_nonneg.mpr hnu)]
    have he : x-n - ((1-t)*((u:ℝ)-n)+t*((v:ℝ)-n)) = 0 := by rw [hc]; ring
    rw [he, abs_zero]

/-- The interpolation error only uses coefficients strictly between the cutoffs,
including the right endpoint whose weight there is zero. -/
theorem integerFirstRieszMean_chord_error (a : ℕ → ℝ) {u v : ℕ} {x t D : ℝ}
    (hu : (u : ℝ) ≤ x) (hv : x ≤ v) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (hc : x = (1-t)*u + t*v) (hD : 0 ≤ D)
    (ha : ∀ n ∈ Finset.Ioc u v, |a n| ≤ D) :
    |integerFirstRieszMean a x -
      ((1-t)*integerFirstRieszMean a u + t*integerFirstRieszMean a v)| ≤ D*((v:ℝ)-u)^2 := by
  have huv : u ≤ v := by exact_mod_cast hu.trans hv
  rw [integerFirstRieszMean_eq_sum_max a ((Nat.cast_nonneg u).trans hu) hv,
    integerFirstRieszMean_eq_sum_max a (Nat.cast_nonneg u) (show (u:ℝ) ≤ v by exact_mod_cast huv),
    integerFirstRieszMean_eq_sum_max a (Nat.cast_nonneg v) le_rfl,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  let h : ℝ := (v:ℝ)-u
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 v, (if u < n then D*h else 0) := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro n hn
      have hn' := (Finset.mem_Ioc.mp hn).2
      have hterm := integerFirstRieszMean_chord_term hu hv ht ht' hc hn'
      rw [show a n*max (x-n) 0 - ((1-t)*(a n*max ((u:ℝ)-n) 0) + t*(a n*max ((v:ℝ)-n) 0)) =
        a n * (max (x-n) 0 - ((1-t)*max ((u:ℝ)-n) 0 + t*max ((v:ℝ)-n) 0)) by ring, abs_mul]
      by_cases hn'' : u < n
      · rw [ite_eq_left hn''] at hterm ⊢
        exact mul_le_mul (ha n (Finset.mem_Ioc.mpr ⟨hn'', hn'⟩)) hterm (abs_nonneg _) hD
      · rw [ite_eq_right hn''] at hterm ⊢
        exact (mul_le_mul_of_nonneg_left hterm (abs_nonneg _)).trans_eq (mul_zero _)
    _ = _ := by
      rw [← Finset.sum_filter]
      have he : (Finset.Ioc 0 v).filter (u < ·) = Finset.Ioc u v := by
        ext n
        simp only [Finset.mem_filter, Finset.mem_Ioc]
        omega
      rw [he, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub huv]
      dsimp [h]
      ring

private theorem integerFirstRieszMean_fourth_window {x : ℝ} (hx : 1 ≤ x) :
    ∃ j : ℕ, 1 ≤ j ∧ (j:ℝ)^4 ≤ x ∧ x ≤ ((j:ℝ)+1)^4 := by
  let r := Real.sqrt (Real.sqrt x)
  let j := ⌊r⌋₊
  have hr : 1 ≤ r := Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hx)
  have he : r^4 = x := by
    change (Real.sqrt (Real.sqrt x))^4 = x
    rw [show 4 = 2*2 by decide, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by linarith)]
  refine ⟨j, (Nat.le_floor_iff (by linarith : 0 ≤ r)).mpr (by simpa using hr), ?_, ?_⟩
  · exact (pow_le_pow_left₀ (Nat.cast_nonneg j) (Nat.floor_le (by linarith : 0 ≤ r)) 4).trans_eq he
  · exact he.symm.le.trans (pow_le_pow_left₀ (by linarith) (Nat.lt_floor_add_one r).le 4)

private theorem integerFirstRieszMean_fourth_comparisons {j x : ℝ}
    (hj : 1 ≤ j) (hl : j^4 ≤ x) :
    (j+1)^6 ≤ 64*j^6 ∧ j^6 ≤ x*Real.sqrt x ∧
    ((j+1)^4-j^4)^2 ≤ 225*j^6 ∧ Real.log (2*(j+1)^4) ≤ 5*Real.log (2*x) := by
  have hj₀ : 0 ≤ j := by linarith
  have h₂ : j ≤ j^2 := by nlinarith [mul_nonneg hj₀ (sub_nonneg.mpr hj)]
  have h₃ : j^2 ≤ j^3 := by nlinarith [mul_nonneg (sq_nonneg j) (sub_nonneg.mpr hj)]
  have hjx : 1 ≤ x := (one_le_pow₀ hj).trans hl
  have h6 := pow_le_pow_left₀ (by linarith : 0 ≤ j+1) (by linarith : j+1 ≤ 2*j) 6
  have h4 := pow_le_pow_left₀ (by linarith : 0 ≤ j+1) (by linarith : j+1 ≤ 2*j) 4
  have hgap : (j+1)^4-j^4 ≤ 15*j^3 := by nlinarith
  have hgap₀ : 0 ≤ (j+1)^4-j^4 := sub_nonneg.mpr (pow_le_pow_left₀ hj₀ (by linarith) 4)
  have hh := pow_le_pow_left₀ hgap₀ hgap 2
  have hs : j^2 ≤ Real.sqrt x := Real.le_sqrt_of_sq_le (by nlinarith only [hl])
  refine ⟨by linarith only [h6], ?_, by nlinarith only [hh], ?_⟩
  · convert mul_le_mul hl hs (sq_nonneg _) (by linarith : 0 ≤ x) using 1; ring
  · have hx5 : x ≤ x^5 := by simpa using (pow_le_pow_right₀ hjx (by decide : 1 ≤ 5))
    have hu : 2*(j+1)^4 ≤ (2*x)^5 := by nlinarith only [h4, hl, hx5]
    exact (Real.log_le_log (by positivity) hu).trans_eq (by rw [Real.log_pow]; norm_num)

/-- Sampling the centered sum at every positive fourth power suffices for a real lower
bound at every cutoff. The coefficient bound only enters on the intervening integers. -/
theorem integerFirstRieszMean_lower_of_fourth_powers (a : ℕ → ℝ) {c C D : ℝ}
    (hc : 0 ≤ c) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (ha : ∀ n : ℕ, 0 < n → |a n| ≤ D*Real.log (2*n))
    (hsample : ∀ j : ℕ, 1 ≤ j → -(C*(j:ℝ)^6*Real.log (2*(j:ℝ)^4)) ≤
      integerFirstRieszMean a ((j:ℝ)^4) - c*((j:ℝ)^4)^2/2) :
    ∀ x : ℝ, 1 ≤ x → -((320*C+1125*D)*(x*Real.sqrt x)*Real.log (2*x)) ≤
      integerFirstRieszMean a x-c*x^2/2 := by
  intro x hx
  obtain ⟨j, hj, hu, hv⟩ := integerFirstRieszMean_fourth_window hx
  let k : ℝ := j
  let u := k^4
  let v := (k+1)^4
  let t := (x-u)/(v-u)
  have hk : 1 ≤ k := by dsimp only [k]; exact_mod_cast hj
  have huv : u < v := pow_lt_pow_left₀ (by linarith : k < k+1) (by linarith) (by decide)
  change u ≤ x at hu
  change x ≤ v at hv
  have ht : 0 ≤ t := div_nonneg (sub_nonneg.mpr hu) (sub_nonneg.mpr huv.le)
  have ht' : t ≤ 1 := (div_le_one (sub_pos.mpr huv)).mpr (by linarith)
  have hx' : x = (1-t)*u+t*v := by
    dsimp [t]
    field_simp [sub_ne_zero.mpr huv.ne']
    ring
  have hs := integerFirstRieszMean_fourth_comparisons hk hu
  obtain ⟨h6, h6x, hgap, hlog⟩ := hs
  let W := (x*Real.sqrt x)*Real.log (2*x)
  have hlog₀ : 0 ≤ Real.log (2*v) := Real.log_nonneg (by linarith)
  have hweight : k^6*Real.log (2*v) ≤ 5*W := by
    dsimp [W]
    convert mul_le_mul h6x hlog hlog₀ (by positivity : 0 ≤ x*Real.sqrt x) using 1; ring
  have hu₀ : 0 < u := by dsimp [u]; positivity
  have hlogu : Real.log (2*u) ≤ Real.log (2*v) := Real.log_le_log (by positivity) (by linarith)
  have hend₁ := hsample j hj
  have hend₂ := hsample (j+1) (by omega)
  change -(C*k^6*Real.log (2*u)) ≤ integerFirstRieszMean a u-c*u^2/2 at hend₁
  simp only [Nat.cast_add, Nat.cast_one] at hend₂
  change -(C*(k+1)^6*Real.log (2*v)) ≤ integerFirstRieszMean a v-c*v^2/2 at hend₂
  have h1 : -(320*C*W) ≤ integerFirstRieszMean a u-c*u^2/2 := by
    have hle := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogu (by positivity : 0 ≤ k^6)) hC
    have hw := mul_le_mul_of_nonneg_left hweight hC
    have hW : 0 ≤ W := mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    nlinarith only [hle,hw,hend₁,mul_nonneg hC hW]
  have h2 : -(320*C*W) ≤ integerFirstRieszMean a v-c*v^2/2 := by
    have hle := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h6 hlog₀) hC
    have hw := mul_le_mul_of_nonneg_left hweight hC
    nlinarith only [hle,hw,hend₂]
  have hcoeff (n : ℕ) (hn : n ∈ Finset.Ioc (j^4) ((j+1)^4)) : |a n| ≤ D*Real.log (2*v) := by
    have hnv : (n:ℝ) ≤ v := by dsimp only [v,k]; exact_mod_cast (Finset.mem_Ioc.mp hn).2
    have hn₀ := Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hn).1
    exact (ha n hn₀).trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity) (by linarith)) hD)
  have hnatU : ((j^4:ℕ):ℝ) = u := by push_cast; rfl
  have hnatV : (((j+1)^4:ℕ):ℝ) = v := by push_cast; rfl
  have herr := integerFirstRieszMean_chord_error a (u := j^4) (v := (j+1)^4) (x := x) (t := t)
    (hnatU.symm ▸ hu) (hnatV.symm ▸ hv) ht ht' (by rw [hnatU,hnatV]; exact hx')
    (mul_nonneg hD hlog₀) hcoeff
  rw [hnatU,hnatV, abs_le] at herr
  have he := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hgap hlog₀) hD
  have hw := mul_le_mul_of_nonneg_left hweight hD
  have hconv : x^2 ≤ (1-t)*u^2+t*v^2 := by
    calc
      _ ≤ x^2 + (1-t)*t*(v-u)^2 := le_add_of_nonneg_right (by positivity)
      _ = _ := by rw [hx']; ring
  have hcc := mul_le_mul_of_nonneg_left hconv hc
  have h₁ := mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr ht')
  have h₂ := mul_le_mul_of_nonneg_left h2 ht
  rw [mul_assoc (320*C+1125*D)]
  change -((320*C+1125*D)*W) ≤ integerFirstRieszMean a x-c*x^2/2
  change (v-u)^2 ≤ 225*k^6 at hgap
  change D*(((k+1)^4-k^4)^2*Real.log (2*v)) ≤ _ at he
  change D*((v-u)^2*Real.log (2*v)) ≤ _ at he
  nlinarith only [h₁,h₂,hcc,herr.1,he,hw]

private theorem fourth_power_absorb_initial {S : ℕ → ℝ} {C : ℝ}
    (hs : ∀ᶠ j : ℕ in Filter.atTop, -(C*(j:ℝ)^6*Real.log (2*(j:ℝ)^4)) ≤ S j) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ j : ℕ, 1 ≤ j → -(C'*(j:ℝ)^6*Real.log (2*(j:ℝ)^4)) ≤ S j := by
  obtain ⟨J, hJ⟩ := Filter.eventually_atTop.1 hs
  let w (j : ℕ) := (j:ℝ)^6 * Real.log (2*(j:ℝ)^4)
  let t (j : ℕ) := max (-S j / w j) 0
  let B := ∑ j ∈ Finset.Ico 1 J, t j
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ ↦ le_max_right _ _
  refine ⟨max C 0 + B, add_nonneg (le_max_right _ _) hB, fun j hj ↦ ?_⟩
  have hj' : 1 ≤ (j:ℝ) := by exact_mod_cast hj
  have hlog : 0 < Real.log (2*(j:ℝ)^4) := Real.log_pos (by linarith [one_le_pow₀ hj' (n := 4)])
  have hw : 0 < w j := mul_pos (pow_pos (by linarith) _) hlog
  rw [mul_assoc]
  change -((max C 0+B)*w j) ≤ S j
  by_cases h : J ≤ j
  · have hlarge := hJ j h
    rw [mul_assoc] at hlarge
    exact (neg_le_neg (mul_le_mul_of_nonneg_right (by linarith [le_max_left C 0]) hw.le)).trans hlarge
  · have hsmall : t j ≤ B := Finset.single_le_sum (s := Finset.Ico 1 J) (f := t)
      (fun n _ ↦ le_max_right _ _) (Finset.mem_Ico.mpr ⟨hj, lt_of_not_ge h⟩)
    have hquot := (le_max_left (-S j/w j) 0).trans hsmall
    have hbound := (div_le_iff₀ hw).mp hquot
    linarith [mul_le_mul_of_nonneg_right (show B ≤ max C 0+B by linarith [le_max_right C 0]) hw.le]

variable {K : Type*} [Field K] [NumberField K]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 K) K)
local notation "a(" χ ")" => heckeLogDerivCoefficient (ideleClassNormTwist χ 0)

/-- Signed first Riesz mean of the prime rational norms. Its coefficient at a prime
is the contribution from the unramified degree-one places of the field. -/
def degreeOnePrimeFirstRieszMean (χ : U) (x : ℝ) : ℝ :=
  ∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (a(χ) p).re * (x-p)

private theorem degreeOnePrimeFirstRieszMean_eq_integer (χ : U) (x : ℝ) :
    degreeOnePrimeFirstRieszMean χ x =
      integerFirstRieszMean (fun n ↦ if n.Prime then (a(χ) n).re else 0) x := by
  unfold degreeOnePrimeFirstRieszMean integerFirstRieszMean
  rw [Finset.sum_filter]
  exact Finset.sum_congr rfl fun p _ ↦ by by_cases hp : p.Prime <;> simp [hp]

/-- An eventual lower bound at fourth powers gives a lower bound for the signed
degree-one prime sum at every real cutoff, including cutoffs between samples. -/
theorem degreeOnePrimeFirstRieszMean_lower_of_fourth_powers (χ : U) {c C : ℝ} (hc : 0 ≤ c)
    (hs : ∀ᶠ j : ℕ in Filter.atTop, -(C*(j:ℝ)^6*Real.log (2*(j:ℝ)^4)) ≤
      degreeOnePrimeFirstRieszMean χ ((j:ℝ)^4)-c*((j:ℝ)^4)^2/2) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : ℝ, 1 ≤ x → -(M*(x*Real.sqrt x)*Real.log (2*x)) ≤
      degreeOnePrimeFirstRieszMean χ x-c*x^2/2 := by
  obtain ⟨C', hC, hS⟩ := fourth_power_absorb_initial hs
  let D : ℝ := Module.finrank ℚ K
  have hD : 0 ≤ D := Nat.cast_nonneg _
  refine ⟨320*C'+1125*D, by positivity, ?_⟩
  simp only [degreeOnePrimeFirstRieszMean_eq_integer] at hS ⊢
  apply integerFirstRieszMean_lower_of_fourth_powers _ hc hC hD _ hS
  intro n hn
  have hn' : 0 < (n:ℝ) := by exact_mod_cast hn
  have hlog : Real.log (n:ℝ) ≤ Real.log (2*n) := Real.log_le_log hn' (by linarith)
  by_cases hp : n.Prime
  · rw [ite_eq_left hp]
    exact (Complex.abs_re_le_norm _).trans ((heckeLogDerivCoefficient_le_vonMangoldt χ n).trans
      (mul_le_mul_of_nonneg_left (ArithmeticFunction.vonMangoldt_le_log.trans hlog) hD))
  · rw [ite_eq_right hp, abs_zero]
    have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
    exact mul_nonneg hD (Real.log_nonneg (by linarith))

/-- The interpolation weight is absorbed by every power strictly above three halves. -/
theorem firstRieszSamplingWeight_le_rpow {b : ℝ} (hb : 1/2 < b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → (x*Real.sqrt x)*Real.log (2*x) ≤ C*x^(1+b) := by
  let ε := b-1/2
  have hε : 0 < ε := by dsimp [ε]; linarith
  refine ⟨2^ε/ε, by positivity, fun x hx ↦ ?_⟩
  have hx' : 0 < x := by linarith
  have hlog := Real.log_le_rpow_div (show 0 ≤ 2*x by positivity) hε
  have hpow : x*Real.sqrt x*x^ε = x^(1+b) := by
    calc
      _ = x^(1:ℝ)*x^(1/2:ℝ)*x^ε := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
      _ = x^(1+1/2+ε) := by rw [← Real.rpow_add hx', ← Real.rpow_add hx']
      _ = _ := by dsimp only [ε]; congr 1; ring
  calc
    _ ≤ (x*Real.sqrt x)*((2*x)^ε/ε) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num) hx'.le, ← hpow]; ring

end RiemannMasullo
