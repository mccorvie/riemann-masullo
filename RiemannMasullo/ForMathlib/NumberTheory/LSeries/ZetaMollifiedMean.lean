module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.ZetaLinearTruncation
public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.FiniteMobiusPolynomial
import RiemannMasullo.ForMathlib.Analysis.Fourier.DirichletPolynomialMean
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Tactic

/-! # Mollified zeta means at a fixed distance from the critical line -/

@[expose] public noncomputable section

open Classical Filter Complex Finset MeasureTheory
open scoped Topology
namespace RiemannMasullo.ZetaZeroDensity

open ConductorCylinder

private theorem split_vertical_term {n : ℕ} (hn : 0 < n) (σ t : ℝ) :
    (n:ℂ)^(-(⟨σ,t⟩:ℂ)) = (n:ℂ)^(-(σ:ℂ)) * Complex.exp (↑(-Real.log n*t)*Complex.I) := by
  have hn' : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [Complex.cpow_def_of_ne_zero hn',Complex.cpow_def_of_ne_zero hn',← Complex.exp_add]
  congr 1
  rw [show Complex.log (n:ℂ) = (Real.log n:ℂ) by rw [Complex.ofReal_log (Nat.cast_nonneg n),Complex.ofReal_natCast]]
  have he : (⟨σ,t⟩:ℂ) = (σ:ℂ)+(t:ℂ)*Complex.I := (Complex.re_add_im _).symm
  push_cast
  rw [he]; ring

private theorem vertical_polynomial {A : ℕ → ℂ} (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) (σ t : ℝ) :
    conductorPolynomial (1 : DirichletCharacter ℂ 1) ⟨σ,t⟩ A S =
      ∑ n ∈ S, (A n * (n:ℂ)^(-(σ:ℂ))) * Complex.exp (↑(-Real.log n*t)*Complex.I) := by
  unfold conductorPolynomial
  apply sum_congr rfl
  intro n hn
  rw [DirichletCharacter.modOne_eq_one',mul_one,split_vertical_term (hS n hn),mul_assoc]

/-- The two-truncation polynomial gains the lower frequency to the power minus the distance from the critical line. -/
theorem polynomial_vertical_mean {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (K N D X : ℕ) (S : Finset ℕ), 0 < D → D ≤ X →
      (∀ n ∈ S, D ≤ n ∧ n ≤ X) → ∀ σ : ℝ, 1/2+d ≤ σ → ∀ a b : ℝ, a ≤ b →
      (∫ t in a..b, ‖conductorPolynomial (1 : DirichletCharacter ℂ 1) ⟨σ,t⟩ (mollifiedCoeff K N) S‖^2) ≤
        C * max (b-a) X * (D:ℝ)^(-d) := by
  obtain ⟨B,hB,h⟩ := dirichletPolynomial_integral_norm_sq_le
  obtain ⟨A,hA,hcoeff⟩ := exists_mollifiedCoeff_sq_tail_bound hd hd.le
  refine ⟨B*A,by positivity,?_⟩
  intro K N D X S hD hX hS σ hσ a b hab
  simp_rw [vertical_polynomial S (fun n hn ↦ hD.trans_le (hS n hn).1)]
  have hX₀ := hD.trans_le hX
  have hpoly := h X hX₀ S (fun n hn ↦ mem_Icc.mpr ⟨hD.trans_le (hS n hn).1,(hS n hn).2⟩)
    (fun n ↦ mollifiedCoeff K N n*(n:ℂ)^(-(σ:ℂ))) hab
  have ht := hcoeff K N D S hD (fun n hn ↦ (hS n hn).1) (σ:ℂ) (by rw [Complex.ofReal_re]; linarith)
  exact hpoly.trans ((mul_le_mul_of_nonneg_left ht (mul_nonneg hB.le ((Nat.cast_nonneg X).trans (le_max_right ..)))).trans_eq (by ring))

/-- At real part two even an absolute tail bound saves a power of the mollifier length. -/
theorem finite_mollifier_at_two :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (K N : ℕ), 1 ≤ K → K ≤ N → ∀ s : ℂ, s.re = 2 →
      ‖conductorTruncation (1 : DirichletCharacter ℂ 1) N s * mobiusMollifier (1 : DirichletCharacter ℂ 1) K s - 1‖ ≤
        B*(K:ℝ)^(-(1/2):ℝ) := by
  let v (n : ℕ) := (n.divisors.card:ℝ)^2*(n:ℝ)^(-(3/2):ℝ)
  have hv : Summable v := summable_card_divisors_sq_mul_rpow (by norm_num)
  have hn (n : ℕ) : 0 ≤ v n := mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine ⟨∑' n,v n,tsum_nonneg hn,?_⟩
  intro K N hK hN s hs
  rw [conductorTruncation_mul_mollifier_sub_one _ _ hK hN (D := K) le_rfl (hN.trans (Nat.le_mul_of_pos_left _ hK)),
    Ioc_self,conductorPolynomial, sum_empty,zero_add]
  let S := Ioc K (K*N)
  change ‖∑ n ∈ S, _‖ ≤ _
  apply (norm_sum_le ..).trans
  have hr (n : ℕ) (hn : n ∈ S) :
      ‖mollifiedCoeff K N n * (1 : DirichletCharacter ℂ 1) (n:ZMod 1)*(n:ℂ)^(-s)‖ ≤ v n*(K:ℝ)^(-(1/2):ℝ) := by
    have hKn := (mem_Ioc.mp hn).1
    have hn₀ := hK.trans hKn.le
    have hc : (1:ℝ) ≤ n.divisors.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr (by omega)⟩
    have he : ‖(n:ℂ)^(-s)‖ = (n:ℝ)^(-s.re) := Complex.norm_cpow_eq_rpow_re_of_pos (Nat.cast_pos.mpr hn₀) _
    rw [DirichletCharacter.modOne_eq_one',mul_one,norm_mul,he,hs,show -(2:ℝ) = -(3/2)+(-(1/2)) by ring,Real.rpow_add (Nat.cast_pos.mpr hn₀)]
    have hcard : (n.divisors.card:ℝ) ≤ (n.divisors.card:ℝ)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hc) (Nat.cast_nonneg n.divisors.card : (0:ℝ) ≤ n.divisors.card)]
    refine (mul_le_mul ((norm_mollifiedCoeff_le K N n).trans hcard)
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hK) (Nat.cast_le.mpr hKn.le) (by norm_num : -(1/2:ℝ) ≤ 0))
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)) (by positivity) (sq_nonneg _)).trans_eq ?_
    dsimp only [v]; ring
  calc _ ≤ ∑ n ∈ S, v n*(K:ℝ)^(-(1/2):ℝ) := sum_le_sum hr
       _ = (∑ n ∈ S,v n)*(K:ℝ)^(-(1/2):ℝ) := (sum_mul ..).symm
       _ ≤ _ := mul_le_mul_of_nonneg_right (hv.sum_le_tsum _ (fun n _ ↦ hn n)) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end RiemannMasullo.ZetaZeroDensity

open Classical Filter Complex MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.ZetaZeroDensity

open ConductorCylinder

local notation "M(" K ")" => mobiusMollifier (1 : DirichletCharacter ℂ 1) K
local notation "D(" N ")" => conductorTruncation (1 : DirichletCharacter ℂ 1) N
local notation "E(" K ", " s ")" => riemannZeta s * M(K) s - 1

private theorem differentiable_conductor_polynomial {q : ℕ} (χ : DirichletCharacter ℂ q)
    (A : ℕ → ℂ) (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    Differentiable ℂ (fun s ↦ conductorPolynomial χ s A S) := by
  unfold conductorPolynomial
  apply Differentiable.fun_sum
  intro n hn
  have h0 : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (hS n hn).ne'
  exact (differentiable_id.neg.const_cpow (.inl h0)).const_mul _

/-- The finite Möbius polynomial is entire. -/
theorem differentiable_time_mollifier (K : ℕ) : Differentiable ℂ M(K) :=
  differentiable_conductor_polynomial _ _ _ (fun _ hn ↦ (Finset.mem_Icc.mp hn).1)

/-- The ordinary mollified zeta mean square on a height interval inside a dyadic band. -/
theorem time_mollified_mean {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m K : ℕ}, 1 ≤ K → K ≤ m →
      ∀ σ : ℝ, 1/2+d ≤ σ → σ ≤ 4 → ∀ a b : ℝ, a ≤ b → (m:ℝ)/2 ≤ a → b ≤ 3*m →
      (∫ t in a..b, ‖E(K,(⟨σ,t⟩:ℂ))‖^2) ≤
        C*m*((K:ℝ)^2*(m:ℝ)^(-1:ℝ) + (K:ℝ)^(-d) + K*(m:ℝ)^(-d)) := by
  obtain ⟨A,hA,h₁⟩ := zeta_linearTruncation_error
  obtain ⟨B,hB,h₂⟩ := polynomial_vertical_mean hd
  refine ⟨12*(A^2+B),by positivity,?_⟩
  intro m K hK hKm σ hσ hσ' a b hab ha hb
  let T := (m:ℝ)
  let N := 4*m
  let S := Finset.Ioc K m
  let U := Finset.Ioc m (K*N)
  let P (V : Finset ℕ) (t : ℝ) := conductorPolynomial (1 : DirichletCharacter ℂ 1) (⟨σ,t⟩:ℂ) (mollifiedCoeff K N) V
  let H (t : ℝ) := ‖E(K,(⟨σ,t⟩:ℂ))‖^2
  let J := A*T^(-(1/2):ℝ)*(K:ℝ)
  have hm := hK.trans hKm
  have hT : 1 ≤ T := by dsimp [T]; exact_mod_cast hm
  have hT₀ : 0 < T := by linarith
  have hKN : K ≤ N := hKm.trans (by dsimp [N]; omega)
  have hL : m ≤ K*N := (show m ≤ N by dsimp [N]; omega).trans (Nat.le_mul_of_pos_left N hK)
  have hc : Continuous (fun t : ℝ ↦ (⟨σ,t⟩:ℂ)) := by
    have he : (fun t : ℝ ↦ (⟨σ,t⟩:ℂ)) = fun t : ℝ ↦ (σ:ℂ)+(t:ℂ)*Complex.I := funext fun t ↦ (Complex.re_add_im _).symm
    rw [he]; fun_prop
  have hH : ContinuousOn H (Icc a b) := by
    apply ContinuousOn.pow
    apply ContinuousOn.norm
    apply ContinuousOn.sub _ continuousOn_const
    apply ContinuousOn.mul _ ((differentiable_time_mollifier K).continuous.comp hc).continuousOn
    intro t ht
    apply (differentiableAt_riemannZeta _).continuousAt.comp_continuousWithinAt hc.continuousWithinAt
    intro he
    have hi := congrArg Complex.im he
    change t = 0 at hi
    change T/2 ≤ a at ha
    linarith [ht.1]
  have hP (V : Finset ℕ) (hv : ∀ n ∈ V, 0 < n) : Continuous (fun t ↦ ‖P V t‖^2) :=
    (((differentiable_conductor_polynomial _ _ V hv).continuous.comp hc).norm.pow 2)
  have hS := hP S (fun n hn ↦ lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1)
  have hU := hP U (fun n hn ↦ lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1)
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) : H t ≤ 3*(J^2+‖P S t‖^2+‖P U t‖^2) := by
    let s : ℂ := ⟨σ,t⟩
    have he := h₁ m hm s (by change 1/2 ≤ σ; linarith) hσ' (ha.trans ht.1) (ht.2.trans hb)
    have hdt : D(N) s = ∑ n ∈ Finset.Icc 1 (4*m), (n:ℂ)^(-s) := by simp [conductorTruncation,conductorPolynomial,N]
    rw [← hdt] at he
    have hM := norm_mobiusMollifier_le (1 : DirichletCharacter ℂ 1) K (s := s) (by change 0 ≤ σ; linarith)
    have hprod : ‖(riemannZeta s-D(N) s)*M(K) s‖ ≤ J := by
      rw [norm_mul]; exact mul_le_mul he hM (norm_nonneg _) (by positivity)
    have hsplit := conductorTruncation_mul_mollifier_sub_one (1 : DirichletCharacter ℂ 1) s hK hKN hKm hL
    have hid : E(K,s) = (riemannZeta s-D(N) s)*M(K) s + (P S t + P U t) := by
      dsimp only [P,S,U]; rw [← hsplit]; ring
    have hv := (norm_add_le ((riemannZeta s-D(N) s)*M(K) s) (P S t+P U t)).trans
      (add_le_add hprod (norm_add_le (P S t) (P U t)))
    change ‖E(K,s)‖^2 ≤ _
    rw [hid]
    exact (pow_le_pow_left₀ (norm_nonneg _) hv 2).trans (by
      nlinarith [sq_nonneg (J-‖P S t‖),sq_nonneg (J-‖P U t‖),sq_nonneg (‖P S t‖-‖P U t‖)])
  have hInt : (∫ t in a..b, H t) ≤ ∫ t in a..b, 3*(J^2+‖P S t‖^2+‖P U t‖^2) := intervalIntegral.integral_mono_on hab
    (hH.intervalIntegrable_of_Icc hab)
    ((continuous_const.mul ((continuous_const.add hS).add hU)).intervalIntegrable a b) hpoint
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add (f := fun t ↦ J^2+‖P S t‖^2)
    (((show Continuous (fun _ : ℝ ↦ J^2) from continuous_const).add hS).intervalIntegrable a b) (hU.intervalIntegrable a b),
    intervalIntegral.integral_add (f := fun _ ↦ J^2) intervalIntegrable_const (hS.intervalIntegrable ..),
    intervalIntegral.integral_const,smul_eq_mul] at hInt
  have hPS := h₂ K N K m S hK hKm (fun n hn ↦ ⟨(Finset.mem_Ioc.mp hn).1.le,(Finset.mem_Ioc.mp hn).2⟩) σ hσ a b hab
  have hPU := h₂ K N m (K*N) U hm hL (fun n hn ↦ ⟨(Finset.mem_Ioc.mp hn).1.le,(Finset.mem_Ioc.mp hn).2⟩) σ hσ a b hab
  change (∫ t in a..b, ‖P S t‖^2) ≤ _ at hPS
  change (∫ t in a..b, ‖P U t‖^2) ≤ _ at hPU
  change b ≤ 3*T at hb
  change T/2 ≤ a at ha
  have hb₁ : max (b-a) (m:ℝ) ≤ 4*T := max_le (by linarith) (by change T ≤ _; linarith)
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hb₂ : max (b-a) ((K*N:ℕ):ℝ) ≤ 4*(K:ℝ)*T := by
    apply max_le
    · nlinarith [mul_nonneg (sub_nonneg.mpr hK') hT₀.le]
    · dsimp [N,T]; push_cast; ring_nf; exact le_rfl
  have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb₁ hB) (Real.rpow_nonneg (Nat.cast_nonneg K) (-d))
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb₂ hB) (Real.rpow_nonneg hT₀.le (-d))
  have hsq : J^2 = A^2*((K:ℝ)^2*T^(-1:ℝ)) := by
    dsimp only [J]; rw [mul_pow,mul_pow,← Real.rpow_mul_natCast hT₀.le]; norm_num; ring
  have hJ := mul_le_mul_of_nonneg_right (show b-a ≤ 4*T by linarith) (sq_nonneg J)
  rw [hsq] at hJ hInt
  apply hInt.trans
  change _ ≤ 12*(A^2+B)*T*((K:ℝ)^2*T^(-1:ℝ)+(K:ℝ)^(-d)+(K:ℝ)*T^(-d))
  have hv := hPS.trans h1
  have hw := hPU.trans h2
  have hlow : 0 ≤ (K:ℝ)^(-d) := Real.rpow_nonneg (Nat.cast_nonneg K) _
  have hhigh : 0 ≤ (K:ℝ)*T^(-d) := by positivity
  have hterm : 0 ≤ (K:ℝ)^2*T^(-1:ℝ) := by positivity
  nlinarith only [hJ,hv,hw,mul_nonneg (mul_nonneg (sq_nonneg A) hT₀.le) (add_nonneg hlow hhigh),
    mul_nonneg (mul_nonneg hB hT₀.le) hterm]

end RiemannMasullo.ZetaZeroDensity

open Classical Filter Complex MeasureTheory Set
open scoped Topology
namespace RiemannMasullo.ZetaZeroDensity

open ConductorCylinder

local notation "M(" K ")" => mobiusMollifier (1 : DirichletCharacter ℂ 1) K
local notation "D(" N ")" => conductorTruncation (1 : DirichletCharacter ℂ 1) N
local notation "E(" K ", " s ")" => riemannZeta s * M(K) s - 1

private theorem floor_rpow_tail {T k : ℝ} (hT : 1 ≤ T) (hk : 0 ≤ k) {v : ℝ} (hv : 0 ≤ v) (hv' : v ≤ 1) :
    ((⌊T^k⌋₊:ℕ):ℝ)^(-v) ≤ 2*T^(-(k*v)) := by
  let K := ⌊T^k⌋₊
  have hT₀ : 0 < T := by linarith
  have hK : 1 ≤ K := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hT hk)
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hlow : T^k / 2 ≤ K := by linarith [Nat.lt_floor_add_one (T^k)]
  apply (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < T^k/2) hlow (neg_nonpos.mpr hv)).trans
  rw [Real.div_rpow (Real.rpow_nonneg hT₀.le _) (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    div_inv_eq_mul, ← Real.rpow_mul hT₀.le,show k*(-v) = -(k*v) by ring,mul_comm]
  exact mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hv').trans_eq
    (Real.rpow_one 2)) (Real.rpow_nonneg hT₀.le _)

set_option maxHeartbeats 700000 in
/-- A single mollifier is close to one at every disk center and has a power-saving integrated error on every vertical slice. -/
theorem exists_time_mollifier {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ∃ K : ℕ,
      (∀ t : ℝ, (m:ℝ)/2 ≤ t → t ≤ 3*m → ‖E(K,(⟨2,t⟩:ℂ))‖ ≤ 1/2) ∧
      ∀ σ : ℝ, 1/2+d ≤ σ → σ ≤ 4 → ∀ a b : ℝ, a ≤ b → (m:ℝ)/2 ≤ a → b ≤ 3*m →
        (∫ t in a..b, ‖E(K,(⟨σ,t⟩:ℂ))‖) ≤ C*(m:ℝ)^(1-d^2/4) := by
  obtain ⟨A,hA,h₁⟩ := zeta_linearTruncation_error
  obtain ⟨B,hB,h₂⟩ := finite_mollifier_at_two
  obtain ⟨C,hC,hmean⟩ := time_mollified_mean hd
  let k := d/2
  let p := d^2/4
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hp : 0 < p := by dsimp [p]; positivity
  have hquad : d^2 ≤ d := by nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 1-d)]
  have hlim : Tendsto (fun m : ℕ ↦ (A+2*B)*(m:ℝ)^(-p)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply,mul_zero] using
      ((tendsto_rpow_neg_atTop hp).comp tendsto_natCast_atTop_atTop).const_mul (A+2*B)
  refine ⟨3+4*C,by positivity,?_⟩
  filter_upwards [hlim.eventually_le_const (by norm_num : (0:ℝ) < 1/2),eventually_ge_atTop 1] with m hc hm
  let T := (m:ℝ)
  let K := ⌊T^k⌋₊
  have hT : 1 ≤ T := by dsimp [T]; exact_mod_cast hm
  have hT₀ : 0 < T := by linarith
  have hK : 1 ≤ K := (Nat.one_le_floor_iff _).mpr (Real.one_le_rpow hT hk)
  have hup : (K:ℝ) ≤ T^k := Nat.floor_le (Real.rpow_nonneg hT₀.le _)
  have hKm : K ≤ m := by
    have hh := hup.trans ((Real.rpow_le_rpow_of_exponent_le hT (show k ≤ 1 by dsimp [k]; linarith)).trans_eq (Real.rpow_one T))
    change (K:ℝ) ≤ (m:ℝ) at hh
    exact_mod_cast hh
  have hpwr {u v : ℝ} (hu : u ≤ v) : T^u ≤ T^v := Real.rpow_le_rpow_of_exponent_le hT hu
  have hlinear (r : ℝ) : (K:ℝ)*T^r ≤ T^(k+r) := by
    rw [Real.rpow_add hT₀]
    exact mul_le_mul_of_nonneg_right hup (Real.rpow_nonneg hT₀.le _)
  have ht (v : ℝ) (hv : 0 ≤ v) (hv' : v ≤ 1) : (K:ℝ)^(-v) ≤ 2*T^(-(k*v)) :=
    floor_rpow_tail hT hk hv hv'
  refine ⟨K,?_,?_⟩
  · intro t htl htu
    let s : ℂ := ⟨2,t⟩
    have hD := h₁ m hm s (by norm_num [s]) (by norm_num [s]) htl htu
    have hdt : D(4*m) s = ∑ n ∈ Finset.Icc 1 (4*m), (n:ℂ)^(-s) := by simp [conductorTruncation,conductorPolynomial]
    rw [← hdt] at hD
    have hM := norm_mobiusMollifier_le (1 : DirichletCharacter ℂ 1) K (s := s) (by norm_num [s])
    have hprod : ‖(riemannZeta s-D(4*m) s)*M(K) s‖ ≤ A*T^(-p) := by
      rw [norm_mul]
      refine (mul_le_mul hD hM (norm_nonneg _) (by positivity)).trans ?_
      rw [mul_right_comm A, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((hlinear _).trans (hpwr (by dsimp [k,p]; linarith))) hA
    have hcnt := h₂ K (4*m) hK (by omega) s rfl
    have hKK : (K:ℝ)^(-(1/2):ℝ) ≤ 2*T^(-p) := (ht (1/2) (by norm_num) (by norm_num)).trans
      (mul_le_mul_of_nonneg_left (hpwr (by dsimp [k,p]; nlinarith)) (by norm_num))
    change ‖E(K,s)‖ ≤ 1/2
    rw [show E(K,s) = (riemannZeta s-D(4*m) s)*M(K) s+(D(4*m) s*M(K) s-1) by ring]
    apply (norm_add_le _ _).trans
    apply (add_le_add hprod (hcnt.trans (mul_le_mul_of_nonneg_left hKK hB))).trans
    change (A+2*B)*T^(-p) ≤ 1/2 at hc
    linarith only [hc]
  · intro σ hσ hσ' a b hab ha hb
    let F (t : ℝ) := ‖E(K,(⟨σ,t⟩:ℂ))‖
    have ha' : 0 < a := lt_of_lt_of_le (by dsimp [T] at hT₀; positivity : 0 < (m:ℝ)/2) ha
    have hF : ContinuousOn F (Icc a b) := by
      have hz : Continuous (fun t : ℝ ↦ (⟨σ,t⟩:ℂ)) := by
        have he : (fun t : ℝ ↦ (⟨σ,t⟩:ℂ)) = fun t : ℝ ↦ (σ:ℂ)+(t:ℂ)*Complex.I := funext fun _ ↦ (Complex.re_add_im _).symm
        rw [he]; fun_prop
      apply ContinuousOn.norm
      apply ContinuousOn.sub _ continuousOn_const
      apply ContinuousOn.mul _ ((differentiable_time_mollifier K).continuous.comp hz).continuousOn
      intro t ht
      apply (differentiableAt_riemannZeta _).continuousAt.comp_continuousWithinAt hz.continuousWithinAt
      intro he
      have hi := congrArg Complex.im he
      change t = 0 at hi
      linarith [ht.1]
    have hsq : (∫ t in a..b, F t^2) ≤ 4*C*T*T^(-(2*p)) := by
      have h₀ := hmean hK hKm σ hσ hσ' a b hab ha hb
      apply h₀.trans
      change C*T*((K:ℝ)^2*T^(-1:ℝ)+(K:ℝ)^(-d)+(K:ℝ)*T^(-d)) ≤ _
      have hv : (K:ℝ)^2*T^(-1:ℝ) ≤ T^(-(2*p)) := by
        have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hup 2) (Real.rpow_nonneg hT₀.le (-1:ℝ))
        rw [← Real.rpow_mul_natCast hT₀.le,← Real.rpow_add hT₀] at hh
        exact hh.trans (hpwr (by dsimp [k,p]; linarith))
      have hw : (K:ℝ)^(-d) ≤ 2*T^(-(2*p)) := by
        convert ht d hd.le (by linarith) using 2; dsimp only [k,p]; ring
      have hx := (hlinear (-d)).trans (hpwr (show k+-d ≤ -(2*p) by dsimp [k,p]; linarith))
      exact (mul_le_mul_of_nonneg_left (add_le_add (add_le_add hv hw) hx) (mul_nonneg hC hT₀.le)).trans_eq (by ring)
    let L := T^p
    have hL : 0 < L := Real.rpow_pos_of_pos hT₀ _
    have hInv : T^(-p) = L⁻¹ := Real.rpow_neg hT₀.le _
    have hpt (t : ℝ) : F t ≤ T^(-p)+L*F t^2 := by
      rw [hInv,← mul_le_mul_iff_right₀ hL,mul_add,mul_inv_cancel₀ hL.ne']
      nlinarith only [sq_nonneg (2*(L*F t)-1)]
    have hint := hF.intervalIntegrable_of_Icc (μ := volume) hab
    have h : (∫ t in a..b, F t) ≤ ∫ t in a..b, T^(-p)+L*F t^2 := intervalIntegral.integral_mono_on hab hint
      ((continuousOn_const.add (continuousOn_const.mul (hF.pow 2))).intervalIntegrable_of_Icc hab) (fun t _ ↦ hpt t)
    rw [intervalIntegral.integral_add (f := fun _ ↦ T^(-p)) (g := fun t ↦ L*F t^2) intervalIntegrable_const
      (((hF.pow 2).const_mul L).intervalIntegrable_of_Icc hab),
      intervalIntegral.integral_const_mul,intervalIntegral.integral_const,smul_eq_mul] at h
    have hw := mul_le_mul_of_nonneg_left hsq hL.le
    have hprod : L * (4*C*T*T^(-(2*p))) = 4*C*(T*T^(-p)) := by
      dsimp only [L]
      rw [show T^(-p) = T^p*T^(-(2*p)) by rw [← Real.rpow_add hT₀]; congr 1; ring]; ring
    rw [hprod] at hw
    have hz : T^(1-d^2/4) = T*T^(-p) := by rw [sub_eq_add_neg,Real.rpow_add hT₀,Real.rpow_one]
    change _ ≤ (3+4*C)*T^(1-d^2/4)
    rw [hz]
    have hlen : b-a ≤ 3*T := by change b ≤ 3*T at hb; linarith
    linarith only [h,hw,mul_le_mul_of_nonneg_right hlen (Real.rpow_nonneg hT₀.le (-p))]

end RiemannMasullo.ZetaZeroDensity
