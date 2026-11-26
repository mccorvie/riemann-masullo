module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.NumberTheory.DirichletCharacter.GaussSum
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The Pólya–Vinogradov character sum bound and sharp Euler lower bound at two

For any nonprincipal primitive Dirichlet character `χ` modulo `q`, expanding `χ` against the
standard additive character via `gaussSum_mulShift_of_isPrimitive` and `norm_gaussSum_stdAddChar`
gives the Pólya–Vinogradov inequality `‖∑_{j=1}^n χ j‖ ≤ √q * log q` (note `q ≥ 3`).

We also record the sharp Euler-product lower bound `π ^ 2 / 15 ≤ ‖χ.LFunction c‖` on the vertical
line `Re c = 2`, valid for every Dirichlet character `χ` modulo `q`.
-/

open Filter Real Complex
open scoped BigOperators Topology

public noncomputable section

namespace DirichletCharacter

/-- Every nonprincipal Dirichlet character modulo `q` has modulus `q ≥ 3`, since `(ZMod q)ˣ` is
trivial for `q = 1` and `q = 2`. -/
theorem three_le_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    3 ≤ q := by
  by_contra! hlt
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  interval_cases q
  · exact hχ (Subsingleton.elim χ 1)
  · apply hχ
    refine MulChar.ext fun u ↦ ?_
    have hu1 : u = 1 := by
      apply Units.ext
      have hlt2 : u.val.val < 2 := u.val.val_lt
      interval_cases h0 : u.val.val
      · exfalso
        have hzero : u.val = 0 := by rw [← ZMod.natCast_zmod_val u.val, h0]; simp
        exact not_isUnit_zero (hzero ▸ u.isUnit)
      · rw [← ZMod.natCast_zmod_val u.val, h0]; simp
    rw [hu1]
    simp

/-- Every nonprincipal Dirichlet character has conductor at least `3`. -/
theorem three_le_conductor_of_ne_one {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : 3 ≤ χ.conductor := by
  have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hp_ne : χ.primitiveCharacter ≠ 1 := by
    intro hp1
    apply hχ
    rw [← χ.changeLevel_primitiveCharacter, hp1, changeLevel_one]
  exact three_le_of_ne_one hp_ne

private theorem norm_cexp_two_pi_div_sub_one {q a : ℕ} :
    ‖Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ)) - 1‖ =
      2 * |Real.sin (Real.pi * (a : ℝ) / (q : ℝ))| := by
  set θ : ℝ := Real.pi * (a : ℝ) / (q : ℝ)
  set α : ℝ := 2 * θ
  have hθ : (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ)) = (α : ℂ) * Complex.I := by
    dsimp [α, θ]; push_cast; ring
  rw [hθ, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hsq : ‖(Real.cos α : ℂ) + (Real.sin α : ℂ) * Complex.I - 1‖ ^ 2 =
      (2 * |Real.sin θ|) ^ 2 := by
    have hre : ((Real.cos α : ℂ) + (Real.sin α : ℂ) * Complex.I - 1).re =
        Real.cos α - 1 := by simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
    have him : ((Real.cos α : ℂ) + (Real.sin α : ℂ) * Complex.I - 1).im =
        Real.sin α := by simp [-Complex.ofReal_cos, -Complex.ofReal_sin]
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him, mul_pow, sq_abs]
    have h1 : Real.cos α = Real.cos (2 * θ) := rfl
    have h2 : Real.sin α = Real.sin (2 * θ) := rfl
    rw [h1, h2, Real.cos_two_mul, Real.sin_two_mul]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  exact (sq_eq_sq₀ (norm_nonneg _) (by positivity)).mp hsq

private theorem geom_stdAddChar_bound {q : ℕ} [NeZero q] {a : ℕ} (ha1 : 1 ≤ a) (haq : a < q)
    (n : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 n, ZMod.stdAddChar ((j : ZMod q) * (a : ZMod q))‖ ≤
      (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
  set z : ℂ := Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ))
  have hterm (j : ℕ) : ZMod.stdAddChar ((j : ZMod q) * (a : ZMod q)) = z ^ j := by
    have hcast : ((j : ZMod q) * (a : ZMod q)) = (((j * a : ℕ) : ℤ) : ZMod q) := by push_cast; rfl
    rw [hcast, ZMod.stdAddChar_coe]
    dsimp [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  have hθ0 : 0 < Real.pi * (a : ℝ) / (q : ℝ) := by
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr ha1
    positivity
  have hθpi : Real.pi * (a : ℝ) / (q : ℝ) < Real.pi := by
    have hq0 : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
    rw [div_lt_iff₀ hq0]
    exact mul_lt_mul_of_pos_left (by exact_mod_cast haq) Real.pi_pos
  have hsin_pos : 0 < Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 hθpi
  have hznorm : ‖z‖ = 1 := by
    dsimp [z]
    rw [show 2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ) =
      ((2 * Real.pi * (a : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hsum_id : (∑ j ∈ Finset.Icc 1 n, z ^ j) * (z - 1) = z * (z ^ n - 1) := by
    rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    have hg := geom_sum_mul z n
    have hfactor : (∑ x ∈ Finset.range n, z ^ (1 + x)) = z * ∑ x ∈ Finset.range n, z ^ x := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [pow_add, pow_one]
    rw [hfactor, mul_assoc, hg]
  have hnorm_prod := congrArg norm hsum_id
  rw [norm_mul, norm_cexp_two_pi_div_sub_one, abs_of_pos hsin_pos, norm_mul, hznorm,
    one_mul] at hnorm_prod
  have hnum : ‖z ^ n - 1‖ ≤ 2 := by
    calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, hznorm, one_pow, norm_one]; norm_num
  have h1 : ‖∑ j ∈ Finset.Icc 1 n, z ^ j‖ ≤
      2 / (2 * Real.sin (Real.pi * (a : ℝ) / (q : ℝ))) :=
    (le_div_iff₀ (by positivity)).mpr (hnorm_prod.trans_le hnum)
  refine h1.trans_eq ?_
  field_simp

private theorem exp_rat_le_nat {r s q : ℕ} (hs : 0 < s)
    (hpow : (2.7182818286 : ℝ) ^ r ≤ (q : ℝ) ^ s) :
    (r : ℝ) / (s : ℝ) ≤ Real.log q := by
  have hq0 : (0 : ℝ) < q := by
    by_contra! hle
    have hq_zero : (q : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg q)
    rw [hq_zero, zero_pow hs.ne'] at hpow
    linarith [pow_pos (by norm_num : (0 : ℝ) < 2.7182818286) r]
  rw [Real.le_log_iff_exp_le hq0]
  have hexp : Real.exp ((r : ℝ) / (s : ℝ)) ^ s = Real.exp 1 ^ r := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    congr 1
    have hs' : (s : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hs.ne'
    field_simp
  have hlt : Real.exp ((r : ℝ) / (s : ℝ)) ^ s ≤ (q : ℝ) ^ s := by
    rw [hexp]
    exact (pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le r).trans hpow
  exact le_of_pow_le_pow_left₀ hs.ne' hq0.le hlt

private theorem harmonic_half_le_log {q : ℕ} (hq : 3 ≤ q) :
    (harmonic ((q - 1) / 2) : ℝ) ≤ Real.log q := by
  set m := (q - 1) / 2
  have hm_ge : 1 ≤ m := by omega
  have hqm : 2 * m + 1 ≤ q := by omega
  by_cases hm5 : m < 5
  · interval_cases m
    · have h1 : (harmonic 1 : ℝ) = ((1 : ℕ) : ℝ) / ((1 : ℕ) : ℝ) := by norm_num [harmonic]
      rw [h1]
      exact exp_rat_le_nat (r := 1) (s := 1) (q := q) (by decide) (by
        have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hqm
        simp only [pow_one]
        linarith)
    · have h2 : (harmonic 2 : ℝ) = ((3 : ℕ) : ℝ) / ((2 : ℕ) : ℝ) := by norm_num [harmonic]
      rw [h2]
      exact exp_rat_le_nat (r := 3) (s := 2) (q := q) (by decide) (by
        have hq5 : (5 : ℝ) ≤ q := by exact_mod_cast hqm
        have : (2.7182818286 : ℝ) ^ 3 ≤ 5 ^ 2 := by norm_num
        exact this.trans (pow_le_pow_left₀ (by norm_num) hq5 2))
    · have h3 : (harmonic 3 : ℝ) = ((11 : ℕ) : ℝ) / ((6 : ℕ) : ℝ) := by norm_num [harmonic]
      rw [h3]
      exact exp_rat_le_nat (r := 11) (s := 6) (q := q) (by decide) (by
        have hq7 : (7 : ℝ) ≤ q := by exact_mod_cast hqm
        have : (2.7182818286 : ℝ) ^ 11 ≤ 7 ^ 6 := by norm_num
        exact this.trans (pow_le_pow_left₀ (by norm_num) hq7 6))
    · have h4 : (harmonic 4 : ℝ) = ((25 : ℕ) : ℝ) / ((12 : ℕ) : ℝ) := by norm_num [harmonic]
      rw [h4]
      exact exp_rat_le_nat (r := 25) (s := 12) (q := q) (by decide) (by
        have hq9 : (9 : ℝ) ≤ q := by exact_mod_cast hqm
        have : (2.7182818286 : ℝ) ^ 25 ≤ 9 ^ 12 := by norm_num
        exact this.trans (pow_le_pow_left₀ (by norm_num) hq9 12))
  · have hm5' : 5 ≤ m := Nat.le_of_not_lt hm5
    have htail : ∀ k : ℕ, 5 ≤ k → (harmonic k : ℝ) ≤ (harmonic 5 : ℝ) + Real.log ((k : ℝ) / 5) := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => simp
      | succ k hk ih =>
        rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
        have hkpos : (0 : ℝ) < k := by positivity
        have hlog_step : ((k + 1 : ℕ) : ℝ)⁻¹ ≤ Real.log (((k + 1 : ℕ) : ℝ) / k) := by
          have h1 := Real.one_sub_inv_le_log_of_pos
            (div_pos (by positivity : (0 : ℝ) < (k + 1 : ℕ)) hkpos)
          rw [inv_div] at h1
          have h2 : 1 - (k : ℝ) / ((k + 1 : ℕ) : ℝ) = ((k + 1 : ℕ) : ℝ)⁻¹ := by
            push_cast; field_simp; ring
          rwa [h2] at h1
        have hlog_add : Real.log ((k : ℝ) / 5) + Real.log (((k + 1 : ℕ) : ℝ) / k) =
            Real.log (((k + 1 : ℕ) : ℝ) / 5) := by
          rw [← Real.log_mul (by positivity) (by positivity)]
          congr 1
          field_simp
        linarith
    have h5 : (harmonic 5 : ℝ) = 137 / 60 := by norm_num [harmonic]
    have h10 : ((137 : ℕ) : ℝ) / ((60 : ℕ) : ℝ) ≤ Real.log (10 : ℕ) :=
      exp_rat_le_nat (r := 137) (s := 60) (q := 10) (by decide) (by norm_num)
    push_cast at h10
    have hm_le : (m : ℝ) / 5 ≤ (q : ℝ) / 10 := by
      have : (2 * m : ℝ) ≤ q := by exact_mod_cast (by omega : 2 * m ≤ q)
      linarith
    have hlog_le : Real.log ((m : ℝ) / 5) ≤ Real.log q - Real.log 10 := by
      calc Real.log ((m : ℝ) / 5)
          ≤ Real.log ((q : ℝ) / 10) := Real.log_le_log (by positivity) hm_le
        _ = Real.log q - Real.log 10 := Real.log_div (by positivity) (by norm_num)
    linarith [htail m hm5']

/-- **Pólya–Vinogradov inequality.** For every nonprincipal primitive Dirichlet character `χ`
modulo `q` and every `n : ℕ`, `‖∑_{j=1}^n χ j‖ ≤ √q * log q`. -/
theorem polyaVinogradov_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hne : χ ≠ 1) (n : ℕ) :
    ‖∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)‖ ≤ Real.sqrt q * Real.log q := by
  have hq3 : 3 ≤ q := three_le_of_ne_one hne
  have hq_pos : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have hχinv : χ⁻¹.IsPrimitive := hχ.inv
  set G := gaussSum χ⁻¹ ZMod.stdAddChar
  have hGnorm : ‖G‖ = Real.sqrt q := norm_gaussSum_stdAddChar hχinv
  have hterm (j : ℕ) : χ (j : ZMod q) * G =
      ∑ a : ZMod q, χ⁻¹ a * ZMod.stdAddChar ((j : ZMod q) * a) := by
    have hg := gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hχinv (j : ZMod q)
    rw [inv_inv] at hg
    rw [← hg, gaussSum]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [AddChar.mulShift_apply]
  have hsum_id : (∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)) * G =
      ∑ a ∈ Finset.range q, χ⁻¹ (a : ZMod q) *
        ∑ j ∈ Finset.Icc 1 n, ZMod.stdAddChar ((j : ZMod q) * (a : ZMod q)) := by
    rw [Finset.sum_mul]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    have heq : (∑ x : ZMod q, ∑ j ∈ Finset.Icc 1 n, χ⁻¹ x * ZMod.stdAddChar ((j : ZMod q) * x)) =
        ∑ i : Fin q, ∑ j ∈ Finset.Icc 1 n,
          χ⁻¹ (ZMod.finEquiv q i) * ZMod.stdAddChar ((j : ZMod q) * ZMod.finEquiv q i) :=
      ((ZMod.finEquiv q).toEquiv.sum_comp _).symm
    rw [heq, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Finset.mul_sum]
    have he : ((ZMod.finEquiv q i).val : ℕ) = i.val := by
      cases q with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ q' => rfl
    have hval : ZMod.finEquiv q i = (i.val : ZMod q) := by
      rw [← ZMod.natCast_zmod_val (ZMod.finEquiv q i), he]
    rw [hval]
  let term (a : ℕ) : ℝ := ‖χ⁻¹ (a : ZMod q) *
    ∑ j ∈ Finset.Icc 1 n, ZMod.stdAddChar ((j : ZMod q) * (a : ZMod q))‖
  have ht0 : term 0 = 0 := by
    have hnu : ¬ IsUnit (0 : ZMod q) := by
      rw [show (0 : ZMod q) = ((0 : ℕ) : ZMod q) by simp, ZMod.isUnit_iff_coprime]
      simp [show q ≠ 1 by omega]
    simp [term, MulChar.map_nonunit _ hnu]
  have ht_le (a : ℕ) (ha1 : 1 ≤ a) (haq : a < q) :
      term a ≤ (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
    dsimp [term]
    rw [norm_mul]
    have h1 : ‖χ⁻¹ (a : ZMod q)‖ ≤ 1 := χ⁻¹.norm_le_one _
    exact (mul_le_mul h1 (geom_stdAddChar_bound ha1 haq n) (norm_nonneg _) zero_le_one).trans_eq
      (one_mul _)
  set m := (q - 1) / 2 with hm_def
  have hmid : ∀ a : ℕ, 2 * a = q → term a = 0 := fun a ha ↦ by
    have hnu : ¬ IsUnit (a : ZMod q) := by
      rw [ZMod.isUnit_iff_coprime, ← ha, Nat.coprime_mul_iff_right]
      intro hcop
      have ha1 : a = 1 := Nat.Coprime.eq_one_of_dvd hcop.2 (dvd_refl a)
      omega
    simp [term, MulChar.map_nonunit _ hnu]
  have hsplit_sum : ∑ a ∈ Finset.range q, term a ≤
      2 * ∑ a ∈ Finset.Icc 1 m, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := by
    have hrange : Finset.range q = insert 0 (Finset.Icc 1 (q - 1)) := by
      ext x
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hrange, Finset.sum_insert (by simp), ht0, zero_add]
    by_cases hpar : q = 2 * m + 1
    · have hpart : Finset.Icc 1 (q - 1) = Finset.Icc 1 m ∪ Finset.Icc (m + 1) (2 * m) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 1) (2 * m)) :=
        Finset.disjoint_left.mpr fun x hx1 hx2 ↦ by simp only [Finset.mem_Icc] at hx1 hx2; omega
      rw [hpart, Finset.sum_union hdisj, two_mul (∑ a ∈ Finset.Icc 1 m, _)]
      refine add_le_add (Finset.sum_le_sum fun (a : ℕ) ha ↦ by
        obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
        exact ht_le a ha1 (by omega)) ?_
      have hbij : ∑ b ∈ Finset.Icc (m + 1) (2 * m), term b =
          ∑ a ∈ Finset.Icc 1 m, term (q - a) := by
        refine Finset.sum_bij (fun b _ ↦ q - b) ?_ ?_ ?_ ?_
        · intro b hb; simp only [Finset.mem_Icc] at hb ⊢; omega
        · intro b₁ hb₁ b₂ hb₂ heq
          simp only [Finset.mem_Icc] at hb₁ hb₂
          change q - b₁ = q - b₂ at heq
          omega
        · intro a ha
          obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
          have hqa1 : m + 1 ≤ q - a := by omega
          have hqa2 : q - a ≤ 2 * m := by omega
          have hqqa : q - (q - a) = a := by omega
          exact ⟨q - a, Finset.mem_Icc.mpr ⟨hqa1, hqa2⟩, hqqa⟩
        · intro b hb; simp only [Finset.mem_Icc] at hb; congr 1; omega
      rw [hbij]
      refine Finset.sum_le_sum fun a ha ↦ ?_
      have ha' := Finset.mem_Icc.mp ha
      refine (ht_le (q - a) (by omega) (by omega)).trans_eq ?_
      congr 1
      have hsub : Real.pi * ((q - a : ℕ) : ℝ) / (q : ℝ) = Real.pi - Real.pi * (a : ℝ) / (q : ℝ) := by
        rw [Nat.cast_sub (by omega : a ≤ q)]
        field_simp
      rw [hsub, Real.sin_pi_sub]
    · have hpar' : q = 2 * m + 2 := by omega
      have hpart : Finset.Icc 1 (q - 1) =
          insert (m + 1) (Finset.Icc 1 m ∪ Finset.Icc (m + 2) (2 * m + 1)) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_union]; omega
      have hnot : m + 1 ∉ Finset.Icc 1 m ∪ Finset.Icc (m + 2) (2 * m + 1) := by
        simp only [Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj : Disjoint (Finset.Icc 1 m) (Finset.Icc (m + 2) (2 * m + 1)) :=
        Finset.disjoint_left.mpr fun x hx1 hx2 ↦ by simp only [Finset.mem_Icc] at hx1 hx2; omega
      rw [hpart, Finset.sum_insert hnot, hmid (m + 1) (by omega), zero_add,
        Finset.sum_union hdisj, two_mul (∑ a ∈ Finset.Icc 1 m, _)]
      refine add_le_add (Finset.sum_le_sum fun (a : ℕ) ha ↦ by
        obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
        exact ht_le a ha1 (by omega)) ?_
      have hbij : ∑ b ∈ Finset.Icc (m + 2) (2 * m + 1), term b =
          ∑ a ∈ Finset.Icc 1 m, term (q - a) := by
        refine Finset.sum_bij (fun b _ ↦ q - b) ?_ ?_ ?_ ?_
        · intro b hb; simp only [Finset.mem_Icc] at hb ⊢; omega
        · intro b₁ hb₁ b₂ hb₂ heq
          simp only [Finset.mem_Icc] at hb₁ hb₂
          change q - b₁ = q - b₂ at heq
          omega
        · intro a ha
          obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
          have hqa1 : m + 2 ≤ q - a := by omega
          have hqa2 : q - a ≤ 2 * m + 1 := by omega
          have hqqa : q - (q - a) = a := by omega
          exact ⟨q - a, Finset.mem_Icc.mpr ⟨hqa1, hqa2⟩, hqqa⟩
        · intro b hb; simp only [Finset.mem_Icc] at hb; congr 1; omega
      rw [hbij]
      refine Finset.sum_le_sum fun a ha ↦ ?_
      have ha' := Finset.mem_Icc.mp ha
      refine (ht_le (q - a) (by omega) (by omega)).trans_eq ?_
      congr 1
      have hsub : Real.pi * ((q - a : ℕ) : ℝ) / (q : ℝ) = Real.pi - Real.pi * (a : ℝ) / (q : ℝ) := by
        rw [Nat.cast_sub (by omega : a ≤ q)]
        field_simp
      rw [hsub, Real.sin_pi_sub]
  have hsin_harm : 2 * ∑ a ∈ Finset.Icc 1 m, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤
      (q : ℝ) * (harmonic m : ℝ) := by
    rw [harmonic_eq_sum_Icc, Rat.cast_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun a ha ↦ ?_
    obtain ⟨ha1, ham⟩ := Finset.mem_Icc.mp ha
    have ha_pos : (0 : ℝ) < a := Nat.cast_pos.mpr ha1
    have h2am : 2 * (a : ℝ) ≤ q := by exact_mod_cast (by omega : 2 * a ≤ q)
    have hθ_le : Real.pi * (a : ℝ) / (q : ℝ) ≤ Real.pi / 2 := by
      rw [div_le_div_iff₀ hq_pos two_pos]
      nlinarith [Real.pi_pos]
    have hsin_lb : 2 * (a : ℝ) / (q : ℝ) ≤ Real.sin (Real.pi * (a : ℝ) / (q : ℝ)) := by
      have hm := Real.mul_le_sin (by positivity : 0 ≤ Real.pi * (a : ℝ) / (q : ℝ)) hθ_le
      refine (le_of_eq ?_).trans hm
      field_simp [Real.pi_ne_zero]
    have hinv : (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ ≤ (q : ℝ) / (2 * (a : ℝ)) := by
      rw [← one_div]
      exact (one_div_le_one_div (Real.sin_pos_of_pos_of_lt_pi (by positivity)
        (by linarith [Real.pi_pos])) (by positivity)).mpr hsin_lb |>.trans_eq (by field_simp)
    rw [Rat.cast_inv, Rat.cast_natCast]
    calc 2 * (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹
        ≤ 2 * ((q : ℝ) / (2 * (a : ℝ))) := mul_le_mul_of_nonneg_left hinv two_pos.le
      _ = (q : ℝ) * (a : ℝ)⁻¹ := by field_simp
  have hprod_le : ‖∑ j ∈ Finset.Icc 1 n, χ (j : ZMod q)‖ * Real.sqrt q ≤
      (q : ℝ) * Real.log q := by
    rw [← hGnorm, ← norm_mul, hsum_id]
    calc ‖∑ a ∈ Finset.range q, χ⁻¹ (a : ZMod q) *
            ∑ j ∈ Finset.Icc 1 n, ZMod.stdAddChar ((j : ZMod q) * (a : ZMod q))‖
        ≤ ∑ a ∈ Finset.range q, term a := norm_sum_le _ _
      _ ≤ 2 * ∑ a ∈ Finset.Icc 1 m, (Real.sin (Real.pi * (a : ℝ) / (q : ℝ)))⁻¹ := hsplit_sum
      _ ≤ (q : ℝ) * (harmonic m : ℝ) := hsin_harm
      _ ≤ (q : ℝ) * Real.log q := mul_le_mul_of_nonneg_left (harmonic_half_le_log hq3) hq_pos.le
  have hsqrt_pos : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq_pos
  rw [← le_div_iff₀ hsqrt_pos] at hprod_le
  refine hprod_le.trans_eq ?_
  rw [mul_div_right_comm, Real.div_sqrt]

end DirichletCharacter

namespace RiemannMasullo

/-- On the vertical line `Re c = 2`, the Euler product bounds `‖χ.LFunction c‖` from below by the
exact constant `ζ(4) / ζ(2) = π² / 15` (> 0.6579), improving `1 / 4` uniformly for all Dirichlet
characters. -/
theorem pi_sq_div_fifteen_le_norm_LFunction_of_re_eq_two {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {c : ℂ} (hc : c.re = 2) :
    Real.pi ^ 2 / 15 ≤ ‖χ.LFunction c‖ := by
  have hc1 : 1 < c.re := by linarith
  have h4 : 1 < (4 : ℂ).re := by norm_num
  have h2 : 1 < (2 : ℂ).re := by norm_num
  have hre2 : (-(2 : ℂ)).re = -2 := by norm_num
  have hre4 : (-(4 : ℂ)).re = -4 := by norm_num
  rw [χ.LFunction_eq_LSeries hc1]
  have hlimL := (DirichletCharacter.LSeries_eulerProduct χ hc1).norm
  have hlim4 := (riemannZeta_eulerProduct h4).norm
  have hlim2 := (riemannZeta_eulerProduct h2).norm
  have hz2_ne : ‖riemannZeta 2‖ ≠ 0 := by
    rw [riemannZeta_two]
    have : (Real.pi : ℂ) ^ 2 / 6 ≠ 0 :=
      div_ne_zero (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) (by norm_num)
    exact norm_ne_zero_iff.mpr this
  have hlim_ratio := hlim4.div hlim2 hz2_ne
  have hstep (n : ℕ) :
      ‖∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-(4 : ℂ)))⁻¹‖ /
        ‖∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-(2 : ℂ)))⁻¹‖ ≤
      ‖∏ p ∈ Nat.primesBelow n, (1 - χ p * (p : ℂ) ^ (-c))⁻¹‖ := by
    have hden_pos : 0 < ‖∏ p ∈ Nat.primesBelow n, (1 - (p : ℂ) ^ (-(2 : ℂ)))⁻¹‖ := by
      rw [norm_prod]
      refine Finset.prod_pos fun p hp ↦ ?_
      have hpr := Nat.prime_of_mem_primesBelow hp
      rw [norm_inv, inv_pos, norm_pos_iff, sub_ne_zero]
      intro heq
      have hn := congrArg norm heq
      rw [norm_one, Complex.norm_natCast_cpow_of_pos hpr.pos, hre2] at hn
      have hlt : (p : ℝ) ^ (-2 : ℝ) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpr.one_lt) (by norm_num)
      linarith
    rw [div_le_iff₀ hden_pos, ← norm_mul, ← Finset.prod_mul_distrib, norm_prod, norm_prod]
    gcongr with p hp
    have hpr := Nat.prime_of_mem_primesBelow hp
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hpr.pos
    have hp_gt1 : (1 : ℝ) < p := by exact_mod_cast hpr.one_lt
    have hpc_norm : ‖(p : ℂ) ^ (-c)‖ = (p : ℝ) ^ (-2 : ℝ) := by
      rw [Complex.norm_natCast_cpow_of_pos hpr.pos, Complex.neg_re, hc]
    have hp2_lt : (p : ℝ) ^ (-2 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by norm_num)
    have hp2_nonneg : 0 ≤ (p : ℝ) ^ (-2 : ℝ) := Real.rpow_nonneg hp_pos.le _
    have hp4_eq : (p : ℂ) ^ (-(4 : ℂ)) = ((p : ℂ) ^ (-(2 : ℂ))) ^ 2 := by
      rw [← Complex.cpow_nat_mul]
      congr 1
      norm_num
    have h1p2_ne : (1 : ℂ) - (p : ℂ) ^ (-(2 : ℂ)) ≠ 0 := by
      intro h0
      have hn := congrArg norm (sub_eq_zero.mp h0)
      rw [norm_one, Complex.norm_natCast_cpow_of_pos hpr.pos, hre2] at hn
      linarith
    have h1p4_ne : (1 : ℂ) - (p : ℂ) ^ (-(4 : ℂ)) ≠ 0 := by
      intro h0
      have hn := congrArg norm (sub_eq_zero.mp h0)
      rw [norm_one, Complex.norm_natCast_cpow_of_pos hpr.pos, hre4] at hn
      have : (p : ℝ) ^ (-4 : ℝ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hp_gt1 (by norm_num)
      linarith
    have h1pc_ne : (1 : ℂ) - χ p * (p : ℂ) ^ (-c) ≠ 0 := by
      intro h0
      have hn := congrArg norm (sub_eq_zero.mp h0)
      rw [norm_one, norm_mul, hpc_norm] at hn
      have hle : ‖χ p‖ * (p : ℝ) ^ (-2 : ℝ) ≤ 1 * (p : ℝ) ^ (-2 : ℝ) :=
        mul_le_mul_of_nonneg_right (χ.norm_le_one p) hp2_nonneg
      linarith
    have hp4_fac : (1 : ℂ) - (p : ℂ) ^ (-(4 : ℂ)) =
        (1 - (p : ℂ) ^ (-(2 : ℂ))) * (1 + (p : ℂ) ^ (-(2 : ℂ))) := by
      rw [hp4_eq]; ring
    rw [hp4_fac, norm_inv, norm_mul, mul_inv, norm_mul, norm_inv, norm_inv,
      mul_comm (‖1 - χ p * (p : ℂ) ^ (-c)‖⁻¹)]
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (norm_nonneg _))
    have hpos1 : 0 < ‖1 - χ p * (p : ℂ) ^ (-c)‖ := norm_pos_iff.mpr h1pc_ne
    refine inv_anti₀ hpos1 ?_
    have hreal : (1 : ℂ) + (p : ℂ) ^ (-(2 : ℂ)) = ((1 + (p : ℝ) ^ (-2 : ℝ) : ℝ) : ℂ) := by
      push_cast
      rw [Complex.ofReal_cpow hp_pos.le]
      simp
    rw [hreal, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    calc ‖1 - χ p * (p : ℂ) ^ (-c)‖
        ≤ ‖(1 : ℂ)‖ + ‖χ p * (p : ℂ) ^ (-c)‖ := norm_sub_le _ _
      _ = 1 + ‖χ p‖ * (p : ℝ) ^ (-2 : ℝ) := by rw [norm_one, norm_mul, hpc_norm]
      _ ≤ 1 + 1 * (p : ℝ) ^ (-2 : ℝ) := by gcongr; exact χ.norm_le_one p
      _ = 1 + (p : ℝ) ^ (-2 : ℝ) := by ring
  have hval : ‖riemannZeta 4‖ / ‖riemannZeta 2‖ = Real.pi ^ 2 / 15 := by
    rw [riemannZeta_four, riemannZeta_two]
    have h4r : ((Real.pi : ℂ) ^ 4 / 90) = (((Real.pi ^ 4 / 90 : ℝ)) : ℂ) := by push_cast; ring
    have h2r : ((Real.pi : ℂ) ^ 2 / 6) = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) := by push_cast; ring
    rw [h4r, h2r, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    field_simp [Real.pi_ne_zero]
    ring
  rw [← hval]
  exact le_of_tendsto_of_tendsto hlim_ratio hlimL (Eventually.of_forall hstep)

end RiemannMasullo
