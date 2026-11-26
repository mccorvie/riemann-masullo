module

public import RiemannMasullo.Ch13_ZerosHecke.RationalJacobiPrimePowerTail
public import RiemannMasullo.Ch13_ZerosHecke.DirichletJacobiPrimeMoments
import RiemannMasullo.ForMathlib.NumberTheory.DirichletCharacter.PrimitiveCount
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Higher conductor moments of complete rational Jacobi cells

For the fourth-power comparison related to Theorem 12.5.1.1, pp. 519–520, the
primitive Dirichlet large sieve on products of `k` primes controls all four
complete cells. At conductor cutoff `C ≥ J^(2k)`, a single exceptional set
controls every dyadic auxiliary pair and every sequence of signs.
-/

open Finset NumberField Filter
open scoped Classical NNReal Topology

public noncomputable section

namespace RiemannMasullo

private theorem selected_cell_centered_moment {ι : Type*} [DecidableEq ι]
    (X : Finset ι) (i₀ : ι) (J r : ℕ) (hr : 1 ≤ r) (R : ι → ℕ → Bool × Bool → ℂ)
    (s : ι → ℕ → Bool × Bool) (d : ι → ℕ → ℝ) {E B P : ℝ} (hB : 0 ≤ B) (hP : 0 ≤ P)
    (hd : ∀ i ∈ X, ∀ j ∈ Ioc 0 J, 0 ≤ d i j ∧
      d i j ≤ ‖R i j (s i j)‖ + B + (if i = i₀ then P else 0))
    (hE : ∀ j ∈ Ioc 0 J, (∑ i ∈ X, ∑ k : Bool × Bool, ‖R i j k‖^r) ≤ E) :
    (∑ i ∈ X, (∑ j ∈ Ioc 0 J, d i j)^r) ≤
      (J : ℝ)^r * 3^r * (E + X.card * B^r + P^r) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  have hthree (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
      (a+b+c)^(n+1) ≤ 3^(n+1) * (a^(n+1) + b^(n+1) + c^(n+1)) := by
    let v : Fin 3 → ℝ := ![a,b,c]
    have hv : ∀ l ∈ univ, 0 ≤ v l := by
      intro l _
      fin_cases l <;> simp [v, ha, hb, hc]
    have hvpow : (a+b+c)^(n+1) ≤ 3^n * (a^(n+1) + b^(n+1) + c^(n+1)) := by
      simpa [v, Fin.sum_univ_three] using pow_sum_le_card_mul_sum_pow hv n
    exact hvpow.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3) (Nat.le_succ n)) (by positivity))
  have hsample (i : ι) (hi : i ∈ X) (j : ℕ) (hj : j ∈ Ioc 0 J) :
      (d i j)^(n+1) ≤ 3^(n+1) * ((∑ k : Bool × Bool, ‖R i j k‖^(n+1)) +
        B^(n+1) + (if i = i₀ then P^(n+1) else 0)) := by
    have h := (pow_le_pow_left₀ (hd i hi j hj).1 (hd i hi j hj).2 (n+1)).trans
      (hthree _ B _ (norm_nonneg _) hB (by split_ifs <;> positivity))
    have hsingle : ‖R i j (s i j)‖^(n+1) ≤ ∑ k : Bool × Bool, ‖R i j k‖^(n+1) :=
      single_le_sum (f := fun k ↦ ‖R i j k‖^(n+1)) (fun _ _ ↦ by positivity) (mem_univ _)
    have hpow : (if i = i₀ then P else 0)^(n+1) = (if i = i₀ then P^(n+1) else 0) := by
      split_ifs <;> simp
    rw [hpow] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (add_le_add_left (add_le_add_left hsingle _) _) (by positivity))
  have hinner (j : ℕ) (hj : j ∈ Ioc 0 J) :
      (∑ i ∈ X, (d i j)^(n+1)) ≤ 3^(n+1) * (E + X.card * B^(n+1) + P^(n+1)) := by
    calc _ ≤ ∑ i ∈ X, (3^(n+1) * ((∑ k : Bool × Bool, ‖R i j k‖^(n+1)) +
             B^(n+1) + (if i = i₀ then P^(n+1) else 0))) := sum_le_sum (fun i hi ↦ hsample i hi j hj)
         _ ≤ _ := by
           rw [← mul_sum, sum_add_distrib, sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq']
           apply mul_le_mul_of_nonneg_left _ (by positivity)
           apply add_le_add (add_le_add_left (hE j hj) _)
           split_ifs <;> first | exact le_rfl | positivity
  calc _ ≤ ∑ i ∈ X, (J : ℝ)^n * ∑ j ∈ Ioc 0 J, (d i j)^(n+1) := by
            apply sum_le_sum
            intro i hi
            simpa only [Nat.card_Ioc, Nat.sub_zero] using
              pow_sum_le_card_mul_sum_pow (fun j hj ↦ (hd i hi j hj).1) n
       _ = (J : ℝ)^n * ∑ j ∈ Ioc 0 J, ∑ i ∈ X, (d i j)^(n+1) := by rw [← mul_sum, sum_comm]
       _ ≤ (J : ℝ)^n * ∑ _j ∈ Ioc 0 J, (3^(n+1) * (E + X.card * B^(n+1) + P^(n+1))) :=
            mul_le_mul_of_nonneg_left (sum_le_sum hinner) (by positivity)
       _ = _ := by
            simp only [sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
            simp only [pow_succ]
            ring

private theorem primitiveMoment_normalize {J C N H : ℝ} (k : ℕ) {A : ℝ}
    (hJ : 1 ≤ J) (hC : 0 < C) (hA : 0 ≤ A) (hN : C^2 ≤ 1024 * N)
    (hraw : H ≤ J^(2*k) * 3^(2*k) *
      (A * (C^2 + Real.pi * (J^4)^k) * ((J^4)^3 * Real.log (2*J^4))^k +
        N * (84 * J^6)^(2*k) + (J^8)^(2*k))) :
    H / N ≤ (3^(2*k) * (4096*A*4^k + (84^(2*k)+1024)*2^k)) *
      (1 + J^(4*k)/C^2) * J^(14*k) * Real.log (2*J)^k := by
  have hJ₀ : 0 < J := by linarith
  have hN₀ : 0 < N := by nlinarith only [hN, sq_pos_of_pos hC]
  let y := J^k
  let L := Real.log (2*J)
  let Q := 1 + y^4/C^2
  have hy : 0 ≤ y := pow_nonneg hJ₀.le _
  have hhalf : 1/2 ≤ L := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h
    exact h.trans (Real.log_le_log (by norm_num) (by linarith : 2 ≤ 2*J))
  have hL : 0 ≤ L := by linarith
  have hQ : 1 ≤ Q := by dsimp [Q]; linarith only [div_nonneg (pow_nonneg hy 4) (sq_nonneg C)]
  have hQ₀ : 0 ≤ Q := by linarith
  have hs (a : ℕ) : J^(a*k) = y^a := by dsimp [y]; rw [← pow_mul, mul_comm a k]
  have hs' (a : ℕ) : (J^a)^k = y^a := by rw [← pow_mul, hs]
  have he12 : ((J^4)^3)^k = y^12 := by
    calc _ = (J^12)^k := by congr 1; ring
         _ = _ := hs' 12
  have he6 : (J^6)^(2*k) = y^12 := by rw [← pow_mul, show 6*(2*k) = 12*k by omega, hs]
  have he8 : (J^8)^(2*k) = y^16 := by rw [← pow_mul, show 8*(2*k) = 16*k by omega, hs]
  simp only [mul_pow, hs 2, hs' 4, he12, he6, he8] at hraw
  have hmass : C^2 + y^4 ≤ (1024 * N) * Q := by
    calc _ = C^2 * Q := by dsimp [Q]; field_simp
         _ ≤ _ := mul_le_mul_of_nonneg_right hN hQ₀
  have hwidth : C^2 + Real.pi * y^4 ≤ 4096 * (N*Q) := by
    nlinarith only [hmass, sq_nonneg C, mul_le_mul_of_nonneg_right Real.pi_le_four (pow_nonneg hy 4)]
  have hkernel : y^4 ≤ 1024 * (N*Q) := by linarith only [hmass, sq_nonneg C]
  have hlog : Real.log (2*J^4)^k ≤ 4^k * L^k := by
    rw [← mul_pow]
    have hpow : 1 ≤ J^4 := one_le_pow₀ hJ
    apply pow_le_pow_left₀ (Real.log_nonneg (by linarith))
    calc _ ≤ Real.log ((2*J)^4) := Real.log_le_log (by positivity) (by nlinarith only [pow_nonneg hJ₀.le 4])
         _ = _ := Real.log_pow (2*J) 4
  have hunit : (1:ℝ) ≤ 2^k * L^k := by
    rw [← mul_pow]
    exact one_le_pow₀ (by linarith)
  let Z := (N*Q)*(y^12*L^k)
  have hsieve : A * (C^2 + Real.pi * y^4) * (y^12 * Real.log (2*J^4)^k) ≤
      (4096*A*4^k)*Z := by
    calc _ ≤ A * (4096*(N*Q)) * (y^12 * (4^k*L^k)) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_left hwidth hA)
                  (mul_le_mul_of_nonneg_left hlog (pow_nonneg hy _)) _ (by positivity)
                exact mul_nonneg (pow_nonneg hy _) (pow_nonneg
                  (Real.log_nonneg (by linarith [show 1 ≤ J^4 from one_le_pow₀ hJ])) k)
         _ = _ := by dsimp [Z]; ring
  have htail : N * (84^(2*k)*y^12) ≤ (84^(2*k)*2^k) * Z := by
    calc _ = 84^(2*k) * (N*1) * (y^12*1) := by ring
         _ ≤ 84^(2*k) * (N*Q) * (y^12*(2^k*L^k)) := by gcongr
         _ = _ := by dsimp [Z]; ring
  have hpole : y^16 ≤ (1024 * 2^k) * Z := by
    calc _ = y^4 * (y^12*1) := by ring
         _ ≤ (1024*(N*Q)) * (y^12*(2^k*L^k)) := by gcongr
         _ = _ := by dsimp [Z]; ring
  apply (div_le_iff₀ hN₀).mpr
  apply hraw.trans
  rw [hs 4, hs 14]
  calc _ ≤ y^2 * 3^(2*k) * (((4096*A*4^k)*Z + (84^(2*k)*2^k)*Z) + (1024*2^k)*Z) := by
              exact mul_le_mul_of_nonneg_left (add_le_add (add_le_add hsieve htail) hpole) (by positivity)
       _ = _ := by dsimp only [Z, Q, L]; ring

/-- Every even conductor moment of the complete pole-centered deficit has the
large-sieve width factor for products of `k` primes. The two auxiliary integers
are arbitrary and the cell may be chosen separately for each character and sample. -/
theorem rationalPrimitiveCellDeficit_conductor_moment (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ (C J : ℕ), 0 < C → 1 ≤ J → ∀ (u v : ℕ)
      (s : RationalPrimitiveCharacter → ℕ → Bool × Bool),
      (∑ i ∈ rationalPrimitiveCharactersThrough C, (rationalPrimitiveCellDeficit i J u v (s i))^(2*k)) /
        (rationalPrimitiveCharactersThrough C).card ≤
        K * (1 + (J : ℝ)^(4*k)/(C : ℝ)^2) * (J : ℝ)^(14*k) * Real.log (2*J)^k := by
  let A := 4 * (k.factorial : ℝ) * 48^k
  refine ⟨3^(2*k) * (4096*A*4^k + (84^(2*k)+1024)*2^k), by dsimp [A]; positivity, ?_⟩
  intro C J hC hJ u v s
  let X := rationalPrimitiveCharactersThrough C
  let R (i : RationalPrimitiveCharacter) (j : ℕ) (t : Bool × Bool) :=
    dirichletJacobiPrimeCellRow i.2.1 (J^4) ((j : ℝ)^4) u v t.1 t.2
  let W (i : RationalPrimitiveCharacter) (j : ℕ) :=
    quadraticPrimePowerCellRieszSum (rationalPrimitiveHeckeParameter i) (J^4) ((j : ℝ)^4) u v
      (if (s i j).1 then 1 else -1) (if (s i j).2 then 1 else -1)
  let c (i : RationalPrimitiveCharacter) (j : ℕ) : ℝ :=
    if rationalPrimitiveHeckeParameter i = 1 then (j : ℝ)^8/2 else 0
  let d (i : RationalPrimitiveCharacter) (j : ℕ) := max (c i j - W i j) 0
  have he (j : ℕ) (hj : j ∈ Ioc 0 J) :
      (∑ i ∈ X, ∑ t : Bool × Bool, ‖R i j t‖^(2*k)) ≤
        A * ((C : ℝ)^2 + Real.pi * ((J : ℝ)^4)^k) * (((J : ℝ)^4)^3 * Real.log (2*(J : ℝ)^4))^k := by
    have hx : (j : ℝ)^4 ≤ ((J^4 : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_left (mem_Ioc.mp hj).2 4
    have h := dirichletJacobiPrimeCellRow_primitive_moment k C (J^4) hk hC (one_le_pow₀ hJ)
      ((j : ℝ)^4) hx u v
    simp only [X, rationalPrimitiveCharactersThrough, sum_sigma]
    apply le_trans _ (by simpa only [A, Nat.cast_pow] using h)
    apply le_of_eq (sum_congr rfl ?_)
    intro m _
    exact (sum_subtype _ (fun χ : DirichletCharacter ℂ (m+1) ↦ by simp)
      (fun χ ↦ ∑ t : Bool × Bool,
        ‖dirichletJacobiPrimeCellRow χ (J^4) ((j : ℝ)^4) u v t.1 t.2‖^(2*k))).symm
  obtain ⟨i₀, _, hi₀⟩ := rationalPrimitiveHeckeParameter_unique_principal
  have hd (i : RationalPrimitiveCharacter) (_hi : i ∈ X) (j : ℕ) (hj : j ∈ Ioc 0 J) :
      0 ≤ d i j ∧ d i j ≤ ‖R i j (s i j)‖ + 84*(J : ℝ)^6 +
        (if i = i₀ then (J : ℝ)^8 else 0) := by
    have hjJ : (j : ℝ) ≤ J := by exact_mod_cast (mem_Ioc.mp hj).2
    have hx := pow_le_pow_left₀ (Nat.cast_nonneg j) hjJ 4
    have htail : |W i j - (R i j (s i j)).re| ≤ 84*(J : ℝ)^6 :=
      rationalPrimitiveJacobiCell_complete_sub_prime i hJ hx u v (s i j).1 (s i j).2
    have hc : c i j ≤ if i = i₀ then (J : ℝ)^8 else 0 := by
      dsimp only [c]
      split_ifs with hp hi hi
      · linarith [pow_le_pow_left₀ (Nat.cast_nonneg j) hjJ 8,
          pow_nonneg (Nat.cast_nonneg (α := ℝ) j) 8]
      · exact (hi (hi₀ i hp)).elim
      · positivity
      · exact le_rfl
    have hz := (neg_le_abs (R i j (s i j)).re).trans (Complex.abs_re_le_norm _)
    have hp : (0 : ℝ) ≤ (if i = i₀ then (J : ℝ)^8 else 0) := by split_ifs <;> positivity
    exact ⟨le_max_right _ _, max_le (by linarith only [hc, (abs_le.mp htail).1, hz]) (by positivity)⟩
  have h := selected_cell_centered_moment X i₀ J (2*k) (by omega) R s d
    (by positivity : (0:ℝ) ≤ 84*(J : ℝ)^6) (by positivity : (0:ℝ) ≤ (J : ℝ)^8) hd he
  exact primitiveMoment_normalize k (by exact_mod_cast hJ) (by exact_mod_cast hC)
    (by dsimp [A]; positivity) (rationalPrimitiveCharactersThrough_card_lower C) h

private theorem selected_cell_allPairs_tail {α β : Type*} (X : Finset α) (P : Finset β)
    (B : Finset α) (hB : B ⊆ X) (r : ℕ) (H : α → β → (ℕ → Bool × Bool) → ℝ)
    {t E : ℝ} (ht : 0 ≤ t) (hH : ∀ i ∈ X, ∀ p ∈ P, ∀ s, 0 ≤ H i p s)
    (hbad : ∀ i ∈ B, ∃ p ∈ P, ∃ s, t ≤ H i p s)
    (hbound : ∀ p ∈ P, ∀ s : α → ℕ → Bool × Bool, (∑ i ∈ X, (H i p (s i))^r) ≤ (X.card : ℝ) * E) :
    (B.card : ℝ) * t^r ≤ (P.card : ℝ) * X.card * E := by
  let σ (i : α) (p : β) : ℕ → Bool × Bool :=
    if h : ∃ s, t ≤ H i p s then h.choose else fun _ ↦ (false, false)
  have hpoint (i : α) (hi : i ∈ B) : t^r ≤ ∑ p ∈ P, (H i p (σ i p))^r := by
    obtain ⟨p, hp, hs⟩ := hbad i hi
    have hσ : t ≤ H i p (σ i p) := by simpa only [σ, dite_eq_left hs] using hs.choose_spec
    exact (pow_le_pow_left₀ ht hσ r).trans
      (single_le_sum (fun q hq ↦ pow_nonneg (hH i (hB hi) q hq (σ i q)) r) hp)
  calc _ = ∑ _i ∈ B, t^r := by simp
       _ ≤ ∑ i ∈ B, ∑ p ∈ P, (H i p (σ i p))^r := sum_le_sum hpoint
       _ = ∑ p ∈ P, ∑ i ∈ B, (H i p (σ i p))^r := sum_comm
       _ ≤ ∑ p ∈ P, ∑ i ∈ X, (H i p (σ i p))^r := sum_le_sum (fun p hp ↦
         sum_le_sum_of_subset_of_nonneg hB (fun i hi _ ↦ pow_nonneg (hH i hi p hp (σ i p)) r))
       _ ≤ ∑ _p ∈ P, (X.card : ℝ) * E := sum_le_sum (fun p hp ↦ hbound p hp (fun i ↦ σ i p))
       _ = _ := by simp only [sum_const, nsmul_eq_mul]; ring

private theorem dyadicPrimePairs_card_le (J : ℕ) :
    let U := Nat.primesLE (2*J^12) \ Nat.primesLE (J^12)
    (U ×ˢ U).card ≤ J^24 := by
  intro U
  have hU : U ⊆ Ioc (J^12) (2*J^12) := by
    intro p hp
    obtain ⟨hi, lo⟩ := mem_sdiff.mp hp
    exact mem_Ioc.mpr ⟨lt_of_not_ge fun h ↦ lo (Nat.mem_primesLE.mpr ⟨h, Nat.prime_of_mem_primesLE hi⟩),
      Nat.le_of_mem_primesLE hi⟩
  have hc : U.card ≤ J^12 := (card_le_card hU).trans_eq (by rw [Nat.card_Ioc]; omega)
  rw [card_product]
  exact (Nat.mul_le_mul hc hc).trans_eq (by ring)

/-- The primitive characters for which some ordered pair of auxiliary primes and some
sequence of sign choices attain the threshold `J^(7+ε)` for the complete deficit. -/
@[expose] def rationalPrimitiveExceptionalCellCharacters (C J : ℕ) (ε : ℝ) :
    Finset RationalPrimitiveCharacter :=
  let U := Nat.primesLE (2*J^12) \ Nat.primesLE (J^12)
  (rationalPrimitiveCharactersThrough C).filter fun i ↦ ∃ p ∈ U ×ˢ U, ∃ s : ℕ → Bool × Bool,
    (J : ℝ)^(7 + ε) ≤ rationalPrimitiveCellDeficit i J p.1 p.2 s

/-- At conductor cutoff `C ≥ J^(2k)`, a single exceptional set suffices for every
ordered dyadic auxiliary-prime pair, including the diagonal, and for every sequence
of signs chosen for that character and pair. Its proportion is bounded by an
absolute constant depending only on `k` times `J^(24−2kε) log(2J)^k`. -/
theorem rationalPrimitiveCellDeficit_allPairs_exception (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ (C J : ℕ), 1 ≤ J → J^(2*k) ≤ C → ∀ ε : ℝ,
      ((rationalPrimitiveExceptionalCellCharacters C J ε).card : ℝ) /
        (rationalPrimitiveCharactersThrough C).card ≤
        K * (J : ℝ)^(24 - 2*(k : ℝ)*ε) * Real.log (2*J)^k := by
  obtain ⟨M, hM, hm⟩ := rationalPrimitiveCellDeficit_conductor_moment k hk
  refine ⟨2*M, by positivity, ?_⟩
  intro C J hJ hsize ε
  let X := rationalPrimitiveCharactersThrough C
  let U := Nat.primesLE (2*J^12) \ Nat.primesLE (J^12)
  let P := U ×ˢ U
  let B := rationalPrimitiveExceptionalCellCharacters C J ε
  let L := Real.log (2*J)
  let m := 2*(k:ℝ)*ε
  let H (i : RationalPrimitiveCharacter) (p : ℕ × ℕ) (s : ℕ → Bool × Bool) :=
    rationalPrimitiveCellDeficit i J p.1 p.2 s
  have hj : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hc : 0 < C := lt_of_lt_of_le (pow_pos (by omega : 0 < J) (2*k)) hsize
  have hX : (0:ℝ) < X.card := by
    nlinarith only [rationalPrimitiveCharactersThrough_card_lower C, sq_pos_of_pos (by exact_mod_cast hc : (0:ℝ) < C)]
  have hL : 0 ≤ L := Real.log_nonneg (by linarith [show (1:ℝ) ≤ J by exact_mod_cast hJ])
  have hw : (J:ℝ)^(4*k) ≤ (C:ℝ)^2 := by
    calc _ = ((J:ℝ)^(2*k))^2 := by rw [← pow_mul, show (2*k)*2 = 4*k by omega]
         _ ≤ _ := pow_le_pow_left₀ (by positivity) (by exact_mod_cast hsize) _
  have hratio := (div_le_one (pow_pos (by exact_mod_cast hc : (0:ℝ) < C) 2)).mpr hw
  have hbound (p : ℕ × ℕ) (_hp : p ∈ P) (s : RationalPrimitiveCharacter → ℕ → Bool × Bool) :
      (∑ i ∈ X, (H i p (s i))^(2*k)) ≤ X.card * (2*M * (J:ℝ)^(14*k) * L^k) := by
    have h := (div_le_iff₀ hX).mp (hm C J hc hJ p.1 p.2 s)
    apply h.trans
    change M * (1 + (J:ℝ)^(4*k)/(C:ℝ)^2) * (J:ℝ)^(14*k) * L^k * X.card ≤ _
    calc _ ≤ M * (1+1) * (J:ℝ)^(14*k) * L^k * X.card := by gcongr
         _ = _ := by ring
  have hmom := selected_cell_allPairs_tail X P B (filter_subset ..) (2*k) H
    (Real.rpow_pos_of_pos hj (7+ε)).le
    (fun i _ p _ s ↦ sum_nonneg (fun _ _ ↦ le_max_right _ _)) (fun _ hi ↦ (mem_filter.mp hi).2) hbound
  have ht : ((J:ℝ)^(7+ε))^(2*k) = (J:ℝ)^(14*k) * (J:ℝ)^m := by
    calc _ = (J:ℝ)^((7+ε)*((2*k : ℕ):ℝ)) := by rw [Real.rpow_mul hj.le, Real.rpow_natCast]
         _ = (J:ℝ)^(((14*k : ℕ):ℝ) + m) := by dsimp [m]; push_cast; ring_nf
         _ = _ := by rw [Real.rpow_add hj, Real.rpow_natCast]
  rw [ht] at hmom
  have hmass : (B.card : ℝ)*(J:ℝ)^m ≤ P.card * X.card * (2*M * L^k) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hj (14*k))).mp
    calc _ = (B.card : ℝ) * ((J:ℝ)^(14*k) * (J:ℝ)^m) := by ring
         _ ≤ _ := hmom
         _ = _ := by ring
  have hP : (P.card : ℝ) ≤ (J:ℝ)^24 := by exact_mod_cast dyadicPrimePairs_card_le J
  calc (B.card : ℝ) / X.card ≤ (2*M * (J:ℝ)^24 * L^k) / (J:ℝ)^m := by
          apply (div_le_div_iff₀ hX (Real.rpow_pos_of_pos hj m)).mpr
          apply hmass.trans
          calc _ ≤ (J:ℝ)^24 * X.card * (2*M * L^k) := by gcongr
               _ = _ := by ring
       _ = _ := by rw [Real.rpow_sub hj]; norm_num [m, L]; ring

private theorem primitiveMoment_log_power_tendsto (k : ℕ) {a : ℝ} (ha : a < 0) :
    Tendsto (fun J : ℕ ↦ (J : ℝ)^a * Real.log (2*(J:ℝ))^k) atTop (𝓝 0) := by
  have hJ : Tendsto (fun J : ℕ ↦ 2 * (J : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have h := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) (neg_pos.mpr ha)).tendsto_div_nhds_zero.comp
    hJ).const_mul ((2 : ℝ)^(-a))
  rw [mul_zero] at h
  apply h.congr
  intro J
  change (2 : ℝ)^(-a) * (Real.log (2*(J:ℝ))^(k : ℝ) / (2*(J:ℝ))^(-a)) = _
  have h₂ : (2 : ℝ)^(-a) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  rw [Real.rpow_natCast, Real.mul_rpow (by norm_num : 0 ≤ (2 : ℝ)) (Nat.cast_nonneg J),
    Real.rpow_neg (Nat.cast_nonneg J), div_eq_mul_inv, mul_inv_rev, inv_inv]
  field_simp

/-- For `kε > 12`, the proportion of primitive base characters admitting any
bad pair and any bad sign selection tends to zero along every conductor cutoff
eventually at least `J^(2k)`. -/
theorem rationalPrimitiveCellDeficit_allPairs_tendsto {k : ℕ} (hk : 1 ≤ k) {ε : ℝ}
    (hε : 12 < (k : ℝ)*ε) (C : ℕ → ℕ) (hC : ∀ᶠ J : ℕ in atTop, J^(2*k) ≤ C J) :
    Tendsto (fun J : ℕ ↦ ((rationalPrimitiveExceptionalCellCharacters (C J) J ε).card : ℝ) /
      (rationalPrimitiveCharactersThrough (C J)).card) atTop (𝓝 0) := by
  obtain ⟨K, _, hK⟩ := rationalPrimitiveCellDeficit_allPairs_exception k hk
  have ha : 24 - 2*(k : ℝ)*ε < 0 := by linarith
  have hlim := (primitiveMoment_log_power_tendsto k ha).const_mul K
  refine squeeze_zero' (Eventually.of_forall fun J ↦ div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    ?_ (by simpa only [mul_zero, ← mul_assoc] using hlim)
  filter_upwards [hC, eventually_ge_atTop 1] with J hsize hJ
  exact hK (C J) J hJ hsize ε

end RiemannMasullo
