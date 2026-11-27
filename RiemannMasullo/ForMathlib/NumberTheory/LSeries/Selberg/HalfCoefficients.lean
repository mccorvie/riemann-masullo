module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import Mathlib.RingTheory.Binomial
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Harmonic.Bounds
import RiemannMasullo.External.HardyCriticalLine.LowerIntegralBound

@[expose] public noncomputable section

open HardyCriticalLine
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace RiemannMasullo

private def spectralLineJet_selbergHalfCoeff (k : ℕ) : ℝ :=
  (-1) ^ k * Ring.choose (1/2 : ℝ) k

private theorem spectralLineJet_selbergHalfCoeff_bound (k : ℕ) :
    |spectralLineJet_selbergHalfCoeff k| ≤ 1 := by
  have hrec (k : ℕ) : ((k : ℝ) + 1) * Ring.choose (1/2 : ℝ) (k+1) =
      (1/2 - k) * Ring.choose (1/2 : ℝ) k := by
    have h := Ring.descPochhammer_eq_factorial_smul_choose (1/2 : ℝ) (k+1)
    rw [descPochhammer_succ_right, Polynomial.smeval_mul, Polynomial.smeval_sub,
      Polynomial.smeval_X, Polynomial.smeval_natCast, Ring.descPochhammer_eq_factorial_smul_choose] at h
    simp only [nsmul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at h
    apply mul_left_cancel₀ (show (k.factorial : ℝ) ≠ 0 by positivity)
    linear_combination -h
  have hb (n : ℕ) : |Ring.choose (1/2 : ℝ) n| ≤ 1 := by
    induction n with
    | zero => simp
    | succ i hi =>
      have ha : |1/2 - (i : ℝ)| ≤ i+1 := abs_le.mpr ⟨by linarith, by linarith [Nat.cast_nonneg (α := ℝ) i]⟩
      apply (mul_le_mul_iff_right₀ (show (0 : ℝ) < i+1 by positivity)).mp
      have he := congrArg abs (hrec i)
      rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < i+1)] at he
      rw [mul_one, he]
      exact (mul_le_of_le_one_right (abs_nonneg _) hi).trans ha
  simpa [spectralLineJet_selbergHalfCoeff, abs_mul, abs_pow] using hb k

/-- The local inverse square root has convolution square `1-X`, including the
coefficient at zero. -/
private theorem spectralLineJet_selbergHalfCoeff_square (k : ℕ) :
    ∑ ij ∈ Finset.antidiagonal k, spectralLineJet_selbergHalfCoeff ij.1 *
      spectralLineJet_selbergHalfCoeff ij.2 =
        if k = 0 then (1 : ℝ) else if k = 1 then -1 else 0 := by
  have hv := Ring.add_choose_eq (r := (1/2 : ℝ)) (s := 1/2) k (Commute.refl _)
  have hnat : (1/2 : ℝ) + 1/2 = (1 : ℕ) := by norm_num
  calc _ = (-1 : ℝ)^k * ∑ ij ∈ Finset.antidiagonal k,
           Ring.choose (1/2 : ℝ) ij.1 * Ring.choose (1/2 : ℝ) ij.2 := by
         rw [Finset.mul_sum]
         refine Finset.sum_congr rfl fun ij hij ↦ ?_
         rw [← Finset.mem_antidiagonal.mp hij, pow_add]
         unfold spectralLineJet_selbergHalfCoeff
         ring
       _ = (-1 : ℝ)^k * ((1 : ℕ).choose k : ℝ) := by rw [← hv, hnat, Ring.choose_natCast]
       _ = _ := by
         rcases k with _ | k
         · simp
         rcases k with _ | k
         · simp
         simp [Nat.choose_eq_zero_of_lt (by omega : 1 < k+2)]

/-- The real coefficients of the inverse square root of the zeta Euler product.
Their cutoff gives a single admissible mollifier at every length. -/
def spectralLineJet_selbergHalfMoebius : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else n.factorization.prod fun _ k ↦ (-1)^k * Ring.choose (1/2 : ℝ) k, by simp⟩

/-- The inverse-square-root Möbius coefficients are multiplicative on coprime arguments. -/
theorem spectralLineJet_selbergHalfMoebius_mult :
    spectralLineJet_selbergHalfMoebius.IsMultiplicative := by
  constructor
  · simp [spectralLineJet_selbergHalfMoebius]
  · intro a b hab
    by_cases ha : a = 0
    · simp [ha]
    by_cases hb : b = 0
    · simp [hb]
    change (if a*b = 0 then _ else _) = (if a = 0 then _ else _) * (if b = 0 then _ else _)
    simp only [ha,hb,mul_ne_zero ha hb,ite_false,Nat.factorization_mul_of_coprime hab]
    exact Finsupp.prod_add_index_of_disjoint hab.disjoint_primeFactors _

private theorem spectralLineJet_selbergHalfMoebius_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    spectralLineJet_selbergHalfMoebius (p^k) = spectralLineJet_selbergHalfCoeff k := by
  simp only [spectralLineJet_selbergHalfMoebius, ArithmeticFunction.coe_mk,
    pow_ne_zero _ hp.ne_zero, ite_false, hp.factorization_pow]
  exact Finsupp.prod_single_index (by simp)

/-- Expand one prime-power Dirichlet convolution into the ordinary coefficient
convolution on exponents. -/
private theorem spectralLineJet_dirichlet_prime_power {R : Type*} [CommSemiring R]
    (f g : ArithmeticFunction R) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (f * g) (p ^ k) = ∑ ij ∈ Finset.antidiagonal k, f (p ^ ij.1) * g (p ^ ij.2) := by
  let e : ℕ ↪ ℕ := ⟨(p ^ ·), Nat.pow_right_injective hp.one_lt⟩
  have hset : (p ^ k).divisorsAntidiagonal = (Finset.antidiagonal k).map (e.prodMap e) := by
    apply Finset.Subset.antisymm _ (Nat.antidiagonal_map_subset_divisorsAntidiagonal_pow hp.one_lt k)
    rintro ⟨a,b⟩ hab
    have h := (Nat.mem_divisorsAntidiagonal.mp hab).1
    obtain ⟨i,_,rfl⟩ := (Nat.dvd_prime_pow hp).mp (show a ∣ p^k from ⟨b, h.symm⟩)
    obtain ⟨j,_,rfl⟩ := (Nat.dvd_prime_pow hp).mp (show b ∣ p^k from ⟨p^i, by rw [← h, mul_comm]⟩)
    have hij : i+j = k := Nat.pow_right_injective hp.one_lt (by change p^(i+j) = p^k; rwa [pow_add])
    exact Finset.mem_map.mpr ⟨(i,j),Finset.mem_antidiagonal.mpr hij,rfl⟩
  rw [ArithmeticFunction.mul_apply, hset, Finset.sum_map]
  rfl

/-- The inverse-square-root mollifier is normalized, bounded uniformly in every
coefficient, and its Dirichlet convolution square is exactly the Möbius function. -/
theorem spectralLineJet_selbergHalfMoebius_spec :
    spectralLineJet_selbergHalfMoebius 1 = 1 ∧
    (∀ n, |spectralLineJet_selbergHalfMoebius n| ≤ 1) ∧
    spectralLineJet_selbergHalfMoebius * spectralLineJet_selbergHalfMoebius = (μ : ArithmeticFunction ℝ) := by
  have hm := spectralLineJet_selbergHalfMoebius_mult
  refine ⟨hm.1, ?_, ?_⟩
  · intro n
    by_cases h : n = 0
    · simp [h]
    change |if n = 0 then 0 else n.factorization.prod _| ≤ 1
    simp only [h, ite_false, Finsupp.prod, Finset.abs_prod]
    exact Finset.prod_le_one₀ (fun _ _ ↦ abs_nonneg _) fun p _ ↦ spectralLineJet_selbergHalfCoeff_bound _
  · apply (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hm.mul hm)
      _ ArithmeticFunction.isMultiplicative_moebius.intCast).mpr
    intro p k hp
    rw [spectralLineJet_dirichlet_prime_power _ _ hp]
    simp_rw [spectralLineJet_selbergHalfMoebius_prime_pow hp]
    rw [spectralLineJet_selbergHalfCoeff_square]
    by_cases hk : k = 0
    · simp [hk]
    simp only [hk, ite_false]
    change _ = ((μ (p^k) : ℤ) : ℝ)
    rw [ArithmeticFunction.moebius_apply_prime_pow hp hk]
    split <;> norm_num

/-- Positive square root of the zeta coefficients, obtained by convolving
the untruncated inverse-square-root mollifier with the constant-one series. -/
def spectralLineJet_selbergHalfZeta : ArithmeticFunction ℝ :=
  spectralLineJet_selbergHalfMoebius * ArithmeticFunction.zeta

private theorem spectralLineJet_selberg_half_local_mass (k : ℕ) :
    |spectralLineJet_selbergHalfCoeff k| ≤
      ∑ i ∈ Finset.range (k+1), spectralLineJet_selbergHalfCoeff i := by
  let b := spectralLineJet_selbergHalfCoeff
  let h (n : ℕ) := ∑ i ∈ Finset.range (n+1), b i
  have hrec (i : ℕ) : ((i:ℝ)+1)*b (i+1)=((i:ℝ)-1/2)*b i := by
    have he := Ring.descPochhammer_eq_factorial_smul_choose (1/2 : ℝ) (i+1)
    rw [descPochhammer_succ_right,Polynomial.smeval_mul,Polynomial.smeval_sub,
      Polynomial.smeval_X,Polynomial.smeval_natCast,Ring.descPochhammer_eq_factorial_smul_choose] at he
    simp only [nsmul_eq_mul,Nat.factorial_succ,Nat.cast_mul,Nat.cast_succ] at he
    have hc : ((i:ℝ)+1)*Ring.choose (1/2:ℝ) (i+1)=(1/2-i)*Ring.choose (1/2:ℝ) i := by
      apply mul_left_cancel₀ (show (i.factorial:ℝ)≠0 by positivity)
      linear_combination -he
    dsimp [b,spectralLineJet_selbergHalfCoeff]
    rw [pow_succ]
    linear_combination -((-1:ℝ)^i)*hc
  have hs (i : ℕ) : h (i+1)=h i+b (i+1) := Finset.sum_range_succ _ _
  have hid (i : ℕ) : (2*((i:ℝ)+1))*b (i+1)= -h i := by
    induction i with
    | zero => norm_num [h,b,spectralLineJet_selbergHalfCoeff]
    | succ i ih =>
      have hr := hrec (i+1)
      push_cast at hr ⊢
      rw [hs]
      linear_combination 2*hr+ih
  change |b k| ≤ h k
  induction k with
  | zero => norm_num [h,b,spectralLineJet_selbergHalfCoeff]
  | succ i ih =>
    have hh := (abs_nonneg (b i)).trans ih
    have hp : 0 < 2*((i:ℝ)+1) := by positivity
    have hb : b (i+1) ≤ 0 := nonpos_of_mul_nonpos_right ((hid i).trans_le (neg_nonpos.mpr hh)) hp
    rw [abs_of_nonpos hb,hs]
    nlinarith only [hid i,mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg (α := ℝ) i) hb]

/-- The half-zeta coefficients dominate the absolute half-Möbius coefficients. Their convolution
square is zeta, and their convolution with the half-Möbius coefficients is the unit. -/
theorem spectralLineJet_selbergHalfZeta_spec :
    (∀ n, |spectralLineJet_selbergHalfMoebius n| ≤ spectralLineJet_selbergHalfZeta n) ∧
    spectralLineJet_selbergHalfZeta * spectralLineJet_selbergHalfZeta = (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ∧
    spectralLineJet_selbergHalfZeta * spectralLineJet_selbergHalfMoebius = 1 := by
  let b := spectralLineJet_selbergHalfMoebius
  let h := spectralLineJet_selbergHalfZeta
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  have hZ : h.IsMultiplicative :=
    spectralLineJet_selbergHalfMoebius_mult.mul ArithmeticFunction.isMultiplicative_zeta.natCast
  have hinv : h*b=1 := by
    change (b*Z)*b = 1
    rw [mul_right_comm,show b*b=(ArithmeticFunction.moebius : ArithmeticFunction ℝ) from spectralLineJet_selbergHalfMoebius_spec.2.2,ArithmeticFunction.coe_moebius_mul_coe_zeta]
  refine ⟨?_,?_,hinv⟩
  · intro n
    change |b n| ≤ h n
    induction n using Nat.recOnPosPrimePosCoprime with
    | zero => simp
    | one => simp [b,spectralLineJet_selbergHalfMoebius_spec.1,hZ.1]
    | prime_pow p j hp _ =>
      change |spectralLineJet_selbergHalfMoebius (p^j)| ≤ (spectralLineJet_selbergHalfMoebius*Z) (p^j)
      rw [spectralLineJet_selbergHalfMoebius_prime_pow hp,ArithmeticFunction.coe_mul_zeta_apply,Nat.sum_divisors_prime_pow hp]
      simpa only [spectralLineJet_selbergHalfMoebius_prime_pow hp] using spectralLineJet_selberg_half_local_mass j
    | coprime i j _ _ hij hi hj =>
      rw [hZ.map_mul_of_coprime hij,spectralLineJet_selbergHalfMoebius_mult.map_mul_of_coprime hij,abs_mul]
      exact mul_le_mul hi hj (abs_nonneg _) ((abs_nonneg _).trans hi)
  · change h*(b*Z)=Z
    rw [← mul_assoc,hinv,one_mul]

/-- Summing a Dirichlet convolution through `X` gives an iterated sum over pairs with product at most `X`. -/
theorem spectralLineJet_selberg_hyperbola_sum (X : ℕ) (f g : ArithmeticFunction ℝ) :
    (∑ n ∈ Finset.Icc 1 X, (f*g) n) =
      ∑ d ∈ Finset.Icc 1 X, f d * ∑ j ∈ Finset.Icc 1 (X/d), g j := by
  classical
  let D := Finset.Icc 1 X
  let S := D ×ˢ D
  let idx (p : ℕ × ℕ) := p.1*p.2
  let w (p : ℕ × ℕ) := f p.1*g p.2
  have he (n : ℕ) (hn : n ∈ D) : S.filter (fun p ↦ idx p=n) = n.divisorsAntidiagonal := by
    obtain ⟨hn0,hnX⟩ := Finset.mem_Icc.mp hn
    change 0<n at hn0
    ext p
    rw [Finset.mem_filter,Nat.mem_divisorsAntidiagonal]
    refine ⟨fun h ↦ ⟨h.2,hn0.ne'⟩,fun h ↦ ⟨?_,h.1⟩⟩
    have ha : p.1 ∣ n := h.1 ▸ dvd_mul_right _ _
    have hb : p.2 ∣ n := h.1 ▸ dvd_mul_left _ _
    exact Finset.mem_product.mpr
      ⟨Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos ha hn0,(Nat.le_of_dvd hn0 ha).trans hnX⟩,
       Finset.mem_Icc.mpr ⟨Nat.pos_of_dvd_of_pos hb hn0,(Nat.le_of_dvd hn0 hb).trans hnX⟩⟩
  calc _ = ∑ n ∈ D, ∑ p ∈ S with idx p=n, w p := by
         exact Finset.sum_congr rfl fun n hn ↦ by rw [he n hn]; rfl
       _ = ∑ p ∈ S with idx p ∈ D, w p := Finset.sum_fiberwise_eq_sum_filter S D idx w
       _ = _ := by
         rw [Finset.sum_filter,Finset.sum_product]
         refine Finset.sum_congr rfl fun d hd ↦ ?_
         have hd0 : 0<d := (Finset.mem_Icc.mp hd).1
         have heq : D.filter (fun j ↦ idx (d,j)∈D) = Finset.Icc 1 (X/d) := by
           ext j
           simp only [Finset.mem_filter,D,Finset.mem_Icc,idx,Nat.le_div_iff_mul_le hd0]
           constructor
           · exact fun h ↦ ⟨h.1.1,by simpa only [Nat.mul_comm] using h.2.2⟩
           · exact fun h ↦ ⟨⟨h.1,(Nat.le_mul_of_pos_right j hd0).trans h.2⟩,
               ⟨Nat.mul_pos hd0 h.1,by simpa only [Nat.mul_comm] using h.2⟩⟩
         rw [Finset.mul_sum,← heq,Finset.sum_filter]

private theorem spectralLineJet_selberg_half_harmonic (X : ℕ) :
    (∑ n ∈ Finset.Icc 1 X, spectralLineJet_selbergHalfZeta n/n)^2 ≤ (harmonic (X*X):ℝ) := by
  classical
  let h := spectralLineJet_selbergHalfZeta
  let D := Finset.Icc 1 X
  let S := D ×ˢ D
  let idx (p : ℕ × ℕ) := p.1*p.2
  let w (p : ℕ × ℕ) := h p.1*h p.2/idx p
  have hn (n : ℕ) : 0≤h n := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 n)
  have hmap (p : ℕ × ℕ) (hp : p∈S) : idx p∈Finset.Icc 1 (X*X) := by
    obtain ⟨ha,hb⟩ := Finset.mem_product.mp hp
    exact Finset.mem_Icc.mpr ⟨Nat.mul_pos (Finset.mem_Icc.mp ha).1 (Finset.mem_Icc.mp hb).1,
      Nat.mul_le_mul (Finset.mem_Icc.mp ha).2 (Finset.mem_Icc.mp hb).2⟩
  calc _ = ∑ p ∈ S, w p := by
         rw [sq,Finset.sum_mul_sum,Finset.sum_product]
         exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ by simp [w,idx,h,div_mul_div_comm]
       _ = ∑ m ∈ Finset.Icc 1 (X*X), ∑ p ∈ S with idx p=m, w p := (Finset.sum_fiberwise_of_maps_to hmap w).symm
       _ ≤ ∑ m ∈ Finset.Icc 1 (X*X), (m:ℝ)⁻¹ := by
         refine Finset.sum_le_sum fun m hm ↦ ?_
         have hm0 : 0<m := (Finset.mem_Icc.mp hm).1
         have hsub : S.filter (fun p ↦ idx p=m) ⊆ m.divisorsAntidiagonal := fun p hp ↦
           Nat.mem_divisorsAntidiagonal.mpr ⟨(Finset.mem_filter.mp hp).2,hm0.ne'⟩
         apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦ div_nonneg (mul_nonneg (hn _) (hn _)) (Nat.cast_nonneg _))).trans
         calc (∑ p ∈ m.divisorsAntidiagonal, w p) = (h*h) m/m := by
                rw [ArithmeticFunction.mul_apply,Finset.sum_div]
                exact Finset.sum_congr rfl fun p hp ↦ by simp only [w,idx,(Nat.mem_divisorsAntidiagonal.mp hp).1]
              _ ≤ _ := by rw [show h*h= (ArithmeticFunction.zeta:ArithmeticFunction ℝ) from spectralLineJet_selbergHalfZeta_spec.2.1]
                          simp [ArithmeticFunction.zeta_apply_ne hm0.ne',one_div]
       _ = _ := by simp [harmonic_eq_sum_Icc]

private theorem spectralLineJet_selberg_half_logderiv (n : ℕ) :
    2*(spectralLineJet_selbergHalfZeta n * Real.log n) =
      (spectralLineJet_selbergHalfZeta * ArithmeticFunction.vonMangoldt) n := by
  let D (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := ⟨fun j ↦ f j*Real.log j,by simp⟩
  let h := spectralLineJet_selbergHalfZeta
  let b := spectralLineJet_selbergHalfMoebius
  let Z : ArithmeticFunction ℝ := ArithmeticFunction.zeta
  let Λ := ArithmeticFunction.vonMangoldt
  have hder (f g : ArithmeticFunction ℝ) : D (f*g)= D f*g+f*D g := by
    ext m
    change (f*g) m*Real.log m = (D f*g) m+(f*D g) m
    rw [ArithmeticFunction.mul_apply,Finset.sum_mul,ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    obtain ⟨he,hm⟩ := Nat.mem_divisorsAntidiagonal.mp hp
    have h0 : p.1*p.2≠0 := he ▸ hm
    have hl : Real.log m=Real.log p.1+Real.log p.2 := by
      rw [← he,Nat.cast_mul,Real.log_mul (by exact_mod_cast (left_ne_zero_of_mul h0))
        (by exact_mod_cast (right_ne_zero_of_mul h0))]
    change f p.1*g p.2*Real.log m = f p.1*Real.log p.1*g p.2+f p.1*(g p.2*Real.log p.2)
    rw [hl]; ring
  have hZ : D Z=Λ*Z := by
    rw [ArithmeticFunction.vonMangoldt_mul_zeta]
    ext m
    by_cases hm : m=0
    · simp [hm]
    · change (ArithmeticFunction.zeta m : ℝ)*Real.log m = Real.log m
      simp [ArithmeticFunction.zeta_apply_ne hm]
  have hh : h*h=Z := spectralLineJet_selbergHalfZeta_spec.2.1
  have hi : h*b=1 := spectralLineJet_selbergHalfZeta_spec.2.2
  have he : D h+D h=h*Λ := by
    calc _ = (D h*h+h*D h)*b := by
           rw [add_mul,mul_comm h (D h),mul_assoc,hi,mul_one]
         _ = D Z*b := by rw [← hder,hh]
         _ = _ := by rw [hZ]; change Λ*Z*b=b*Z*Λ; ring
  have hv := congrArg (fun f : ArithmeticFunction ℝ ↦ f n) he
  change h n*Real.log n+h n*Real.log n=(h*Λ) n at hv
  simpa only [two_mul] using hv

/-- Each half-zeta coefficient is at most one. -/
theorem spectralLineJet_selberg_half_le_one (n : ℕ) : spectralLineJet_selbergHalfZeta n ≤ 1 := by
  let h := spectralLineJet_selbergHalfZeta
  by_cases hn : n=0
  · simp [hn]
  have hp : (n,1) ∈ n.divisorsAntidiagonal := Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_one _,hn⟩
  have hpos (i : ℕ) : 0≤h i := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 i)
  have hone : h 1=1 :=
    (spectralLineJet_selbergHalfMoebius_mult.mul ArithmeticFunction.isMultiplicative_zeta.natCast).1
  have hh : (h*h) n=1 := by
    rw [show h*h= (ArithmeticFunction.zeta:ArithmeticFunction ℝ) from spectralLineJet_selbergHalfZeta_spec.2.1]
    simp [ArithmeticFunction.zeta_apply_ne hn]
  rw [ArithmeticFunction.mul_apply] at hh
  have hbound := Finset.single_le_sum (f := fun p : ℕ×ℕ ↦ h p.1*h p.2) (fun p _ ↦ mul_nonneg (hpos _) (hpos _)) hp
  simpa [hone,hh] using hbound

private theorem spectralLineJet_selberg_half_log_sum {X : ℕ} (hX : 0 < X) :
    2*(∑ n ∈ Finset.Icc 1 X, spectralLineJet_selbergHalfZeta n*Real.log n) ≤
      (Real.log 4+4)*(X:ℝ)*Real.sqrt (harmonic (X*X):ℝ) := by
  let h := spectralLineJet_selbergHalfZeta
  let C := Real.log 4+4
  have hC : 0≤C := by dsimp [C]; positivity
  have hpsi (d : ℕ) : (∑ j ∈ Finset.Icc 1 (X/d), ArithmeticFunction.vonMangoldt j) ≤ C*((X:ℝ)/d) := by
    have hp := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) (X/d))
    simp only [Chebyshev.psi,Nat.floor_natCast,← Finset.Icc_succ_left_eq_Ioc] at hp
    exact hp.trans (mul_le_mul_of_nonneg_left Nat.cast_div_le hC)
  calc _ = ∑ n ∈ Finset.Icc 1 X, (h*ArithmeticFunction.vonMangoldt) n := by
         rw [Finset.mul_sum]
         exact Finset.sum_congr rfl fun n _ ↦ spectralLineJet_selberg_half_logderiv n
       _ = _ := spectralLineJet_selberg_hyperbola_sum _ _ _
       _ ≤ ∑ d ∈ Finset.Icc 1 X, h d*(C*((X:ℝ)/d)) := by
         refine Finset.sum_le_sum fun d _ ↦ mul_le_mul_of_nonneg_left (hpsi d) ?_
         exact (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 d)
       _ = (C*X)*(∑ d ∈ Finset.Icc 1 X, h d/d) := by
         rw [Finset.mul_sum]
         exact Finset.sum_congr rfl fun _ _ ↦ by ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (Real.le_sqrt_of_sq_le (spectralLineJet_selberg_half_harmonic X)) (by positivity)

/-- Uniform elementary Chebyshev bound for the positive and absolute coefficients
of the square-root Euler series. It gains a square root of a logarithm in the
actual (unweighted) initial interval. -/
theorem spectralLineJet_selberg_half_sum :
    ∃ C > (0:ℝ), ∀ X : ℕ, 0 < X →
      (∑ n ∈ Finset.Icc 1 X, spectralLineJet_selbergHalfZeta n) ≤ C*X/Real.sqrt (1+Real.log X) := by
  let K := Real.log 4+4
  refine ⟨K+5,by dsimp [K]; positivity,?_⟩
  intro X hX
  let h := spectralLineJet_selbergHalfZeta
  let D := Finset.Icc 1 X
  let H := 1+Real.log X
  have hxp : (0:ℝ)<X := by exact_mod_cast hX
  have hx1 : (1:ℝ)≤X := by exact_mod_cast hX
  have hlog := Real.log_nonneg hx1
  have hH : 1≤H := by dsimp [H]; linarith
  have hroot : 1≤Real.sqrt H := Real.le_sqrt_of_sq_le (by simpa using hH)
  have hs := Real.sq_sqrt (zero_le_one.trans hH)
  have hC : 0≤K := by dsimp [K]; positivity
  have hh (n : ℕ) : 0 ≤ h n := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 n)
  have hsum : (∑ n ∈ D, h n) ≤ (X:ℝ) := by
    calc _ ≤ ∑ _n ∈ D, (1:ℝ) := Finset.sum_le_sum fun n _ ↦ spectralLineJet_selberg_half_le_one n
         _ = _ := by simp [D]
  have hharm : (harmonic (X*X):ℝ) ≤ 2*H := by
    have h := harmonic_le_one_add_log (X*X)
    rw [Nat.cast_mul,Real.log_mul hxp.ne' hxp.ne'] at h
    dsimp [H]; linarith
  have hr : Real.sqrt (harmonic (X*X):ℝ) ≤ 2*Real.sqrt H := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith only [hharm,hs,hH]⟩
  have hweighted : (∑ n ∈ D, h n*Real.log n) ≤ K*X*Real.sqrt H := by
    have hbound := (spectralLineJet_selberg_half_log_sum hX).trans (mul_le_mul_of_nonneg_left hr (by positivity))
    change 2*(∑ n ∈ D, h n*Real.log n) ≤ K*X*(2*Real.sqrt H) at hbound
    linarith
  have hdiff : (∑ n ∈ D, h n*(Real.log X-Real.log n)) ≤ 4*X := by
    calc _ ≤ ∑ n ∈ D, 2*Real.sqrt X*(1/Real.sqrt n) := by
           refine Finset.sum_le_sum fun n hn ↦ ?_
           have hn0 : (0:ℝ)<n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
           have hratio := Real.log_le_rpow_div (div_nonneg hxp.le hn0.le) (by norm_num : (0:ℝ)<1/2)
           rw [Real.log_div hxp.ne' hn0.ne',← Real.sqrt_eq_rpow,Real.sqrt_div hxp.le] at hratio
           have hpos : 0 ≤ Real.log X-Real.log n := sub_nonneg.mpr (Real.log_le_log hn0 (by exact_mod_cast (Finset.mem_Icc.mp hn).2))
           calc _ ≤ Real.log X-Real.log n := mul_le_of_le_one_left hpos (spectralLineJet_selberg_half_le_one n)
                _ ≤ _ := by convert hratio using 1; ring
         _ = (2*Real.sqrt X)*∑ n ∈ D, 1/Real.sqrt n := (Finset.mul_sum ..).symm
         _ ≤ (2*Real.sqrt X)*(2*Real.sqrt X) := mul_le_mul_of_nonneg_left (sum_Icc_one_div_sqrt_le_two_mul_sqrt X) (by positivity)
         _ = _ := by nlinarith only [Real.sq_sqrt hxp.le]
  have hid : H*(∑ n ∈ D, h n) = (∑ n ∈ D, h n)+(∑ n ∈ D, h n*Real.log n)+(∑ n ∈ D, h n*(Real.log X-Real.log n)) := by
    rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ ↦ ?_; dsimp [H]; ring
  have hprod := mul_le_mul_of_nonneg_left hroot hxp.le
  apply (le_div_iff₀ (by positivity : 0 < Real.sqrt H)).mpr
  apply (mul_le_mul_iff_left₀ (by positivity : 0 < Real.sqrt H)).mp
  change (∑ n ∈ D, h n)*Real.sqrt H*Real.sqrt H ≤ (K+5)*X*Real.sqrt H
  nlinarith only [hid,hsum,hweighted,hdiff,hprod,hs,show (∑ n ∈ D,h n)*Real.sqrt H*Real.sqrt H = H*(∑ n ∈ D,h n) by rw [mul_assoc,← sq,hs,mul_comm]]

/-- Cancellation of the actual sharp inverse-square-root mollifier at the
real point one, uniformly in its length. The divisor identity for the positive
half-zeta coefficients bounds the rounding error as well as the main sum. -/
theorem spectralLineJet_selbergHalfMoebius_reciprocal_sum :
    ∃ C > (0:ℝ), ∀ X : ℕ, 0 < X →
      |∑ n ∈ Finset.Icc 1 X, spectralLineJet_selbergHalfMoebius n/n| ≤ C/Real.sqrt (1+Real.log X) := by
  obtain ⟨C,hC,hmean⟩ := spectralLineJet_selberg_half_sum
  refine ⟨2*C,by positivity,?_⟩
  intro X hX
  let D := Finset.Icc 1 X
  let b := spectralLineJet_selbergHalfMoebius
  let h := spectralLineJet_selbergHalfZeta
  let err (d : ℕ) : ℝ := (X:ℝ)/d-(X/d:ℕ)
  have herr (d : ℕ) (hd : d ∈ D) : |err d| ≤ 1 := by
    have hd0 : 0<d := (Finset.mem_Icc.mp hd).1
    have hd' : 0<(d:ℝ) := by exact_mod_cast hd0
    have he : (d:ℝ)*(X/d:ℕ)+(X%d:ℕ)=X := by exact_mod_cast Nat.div_add_mod X d
    have hm : ((X%d:ℕ):ℝ) < d := by exact_mod_cast Nat.mod_lt X hd0
    dsimp [err]
    rw [abs_of_nonneg (sub_nonneg.mpr Nat.cast_div_le)]
    have := (div_le_iff₀ hd').mpr (by nlinarith only [he,hm] : (X:ℝ) ≤ (((X/d:ℕ):ℝ)+1)*d)
    linarith
  have hsum : (∑ n ∈ D, h n) = ∑ d ∈ D, b d*(X/d:ℕ) := by
    rw [show (∑ n ∈ D, h n) = _ from spectralLineJet_selberg_hyperbola_sum X b (ArithmeticFunction.zeta : ArithmeticFunction ℝ)]
    refine Finset.sum_congr rfl fun d _ ↦ congrArg (b d * ·) ?_
    calc _ = ∑ _j ∈ Finset.Icc 1 (X/d), (1:ℝ) := by
           exact Finset.sum_congr rfl fun j hj ↦ by have hj0 : 0<j := (Finset.mem_Icc.mp hj).1; simp [ArithmeticFunction.zeta_apply_ne hj0.ne']
         _ = _ := by simp
  have heq : (X:ℝ)*(∑ n ∈ D, b n/n) = (∑ n ∈ D, h n)+∑ d ∈ D, b d*err d := by
    rw [Finset.mul_sum,hsum,← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun d _ ↦ ?_; dsimp [err]; ring
  have hxp : 0<(X:ℝ) := by exact_mod_cast hX
  have hh (n : ℕ) : 0≤h n := (abs_nonneg _).trans (spectralLineJet_selbergHalfZeta_spec.1 n)
  apply (mul_le_mul_iff_right₀ hxp).mp
  change (X:ℝ)*|∑ n ∈ D,b n/n| ≤ _
  calc _ = |(X:ℝ)*(∑ n ∈ D, b n/n)| := by rw [abs_mul,abs_of_pos hxp]
       _ ≤ |∑ n ∈ D, h n|+|∑ d ∈ D, b d*err d| := heq ▸ abs_add_le _ _
       _ ≤ (∑ n ∈ D, h n)+(∑ n ∈ D, h n) := by
         rw [abs_of_nonneg (Finset.sum_nonneg fun _ _ ↦ hh _)]
         apply add_le_add le_rfl
         apply (Finset.abs_sum_le_sum_abs _ _).trans
         refine Finset.sum_le_sum fun d hd ↦ ?_
         rw [abs_mul]
         exact (mul_le_of_le_one_right (abs_nonneg _) (herr d hd)).trans (spectralLineJet_selbergHalfZeta_spec.1 d)
       _ ≤ C*X/Real.sqrt (1+Real.log X)+C*X/Real.sqrt (1+Real.log X) := add_le_add (hmean X hX) (hmean X hX)
       _ = _ := by ring

end RiemannMasullo
