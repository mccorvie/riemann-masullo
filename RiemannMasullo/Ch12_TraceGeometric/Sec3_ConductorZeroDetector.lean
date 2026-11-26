module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ConductorMollifier
import RiemannMasullo.ForMathlib.Analysis.Complex.CircleFamilyBound
import Mathlib.Tactic

/-! # A conductor-aspect zero detector on a polynomial height range

The mean square of the mollified L-functions on one circle bounds the
fraction of characters having even a single zero in the smaller rectangle.
The radius grows quadratically with the height so the entire rectangle can
be enclosed while the circle stays to the right of the critical line.
-/

@[expose] public noncomputable section

open Classical Filter Finset Metric
open scoped Topology

namespace RiemannMasullo.ConductorCylinder

private theorem polynomial_energy {q : ℕ} [NeZero q] (S : Finset ℕ) (A : ℕ → ℂ) (s : ℂ)
    (L : ℕ) (hL : ∀ n ∈ S, n ≤ q*L) :
    ∑ χ : DirichletCharacter ℂ q, ‖conductorPolynomial χ s A S‖^2 ≤
      (q.totient : ℝ) * ((L+1:ℕ) * ∑ n ∈ S, ‖A n * (n:ℂ)^(-s)‖^2) := by
  have he (χ : DirichletCharacter ℂ q) : conductorPolynomial χ s A S =
      ∑ n ∈ S, (A n * (n:ℂ)^(-s))*χ (n : ZMod q) := by
    unfold conductorPolynomial
    exact sum_congr rfl (fun _ _ ↦ mul_right_comm ..)
  simp_rw [he]
  rw [mul_comm,← div_le_iff₀ (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q)))]
  exact character_polynomial_mean_sq_le q S _ L hL

private theorem abel_energy {q : ℕ} [NeZero q] {d : ℝ} (hd : 0 < d) (s : ℂ) (hs : 1/2+d ≤ s.re) :
    ∑ χ ∈ (univ.erase (1 : DirichletCharacter ℂ q)), ‖χ.LFunction s - conductorTruncation χ q s‖^2 ≤
      (q.totient : ℝ) * (8 * ‖s‖^2 * (q:ℝ)^(-2*d)) := by
  let U := univ.erase (1 : DirichletCharacter ℂ q)
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hq₀ : 0 < (q:ℝ) := by linarith
  obtain ⟨A,hA,he⟩ := conductorTruncation_abel_error (q := q) s (by linarith)
  let P (χ : DirichletCharacter ℂ q) := ∑ j ∈ Icc 1 q, A j * χ (j : ZMod q)
  have hbound := character_polynomial_mean_sq_le q (Icc 1 q) A 1 (fun n hn ↦ by simpa using (mem_Icc.mp hn).2)
  have he' (j : ℕ) : ‖A j‖ ≤ 2*‖s‖*(q:ℝ)^(-s.re) := by
    apply (hA j).trans
    rw [← mul_div_assoc,div_le_iff₀ (by linarith)]
    nlinarith [mul_nonneg (mul_nonneg (norm_nonneg s) (Real.rpow_nonneg hq₀.le (-s.re))) (by linarith : 0 ≤ 2*s.re-1)]
  have hsum : ∑ j ∈ Icc 1 q, ‖A j‖^2 ≤ (q:ℝ)*(2*‖s‖*(q:ℝ)^(-s.re))^2 := by
    apply (sum_le_sum (fun j _ ↦ pow_le_pow_left₀ (norm_nonneg _) (he' j) 2)).trans_eq
    simp
  have hpow : (q:ℝ) * ((q:ℝ)^(-s.re))^2 ≤ (q:ℝ)^(-2*d) := by
    calc _ = (q:ℝ)^(1+(-s.re)*2) := by
               rw [Real.rpow_add hq₀,Real.rpow_one,Real.rpow_mul hq₀.le,Real.rpow_two]
         _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  calc _ = ∑ χ ∈ U, ‖P χ‖^2 := sum_congr rfl (fun χ hχ ↦ by rw [he χ (mem_erase.mp hχ).1])
       _ ≤ ∑ χ, ‖P χ‖^2 := sum_le_univ_sum_of_nonneg (fun _ ↦ sq_nonneg _)
       _ ≤ _ := by
         have hb := (div_le_iff₀ (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q)))).mp hbound
         refine hb.trans ?_
         rw [mul_comm _ (q.totient:ℝ)]
         apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
         push_cast
         nlinarith [mul_le_mul_of_nonneg_left hpow (sq_nonneg ‖s‖)]

/-- Averaged error of the actual nonprincipal L-functions times the ordinary
Möbius mollifier. No zero count enters. Splitting the finite product at the
modulus avoids a length loss on all frequencies below the modulus. -/
theorem conductor_mollified_mean {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (K : ℕ), 1 ≤ K → K ≤ q →
      ∀ s : ℂ, 1/2+d ≤ s.re →
        ∑ χ ∈ univ.erase (1 : DirichletCharacter ℂ q), ‖χ.LFunction s * mobiusMollifier χ K s - 1‖^2 ≤
        (q.totient:ℝ)*3*(8*‖s‖^2*(K:ℝ)^2*(q:ℝ)^(-2*d) +
          2*C*(K:ℝ)^(-d) + ((K:ℝ)+1)*C*(q:ℝ)^(-d)) := by
  obtain ⟨C,hC,hB⟩ := exists_mollifiedCoeff_sq_tail_bound (e := d) hd hd.le
  refine ⟨C,hC,?_⟩
  intro q _ K hK hq s hs
  let U := univ.erase (1 : DirichletCharacter ℂ q)
  let A := mollifiedCoeff K q
  let M (χ : DirichletCharacter ℂ q) := mobiusMollifier χ K s
  let E (χ : DirichletCharacter ℂ q) := χ.LFunction s - conductorTruncation χ q s
  let P (S : Finset ℕ) (χ : DirichletCharacter ℂ q) := conductorPolynomial χ s A S
  let S₁ := Ioc K q
  let S₂ := Ioc q (K*q)
  have hrow (χ : DirichletCharacter ℂ q) : ‖χ.LFunction s * M χ - 1‖^2 ≤
      3 * (‖E χ‖^2*(K:ℝ)^2 + ‖P S₁ χ‖^2 + ‖P S₂ χ‖^2) := by
    have h1 := conductorTruncation_mul_mollifier_sub_one χ s hK hq hq (Nat.le_mul_of_pos_left q hK)
    change conductorTruncation χ q s * M χ - 1 = P S₁ χ + P S₂ χ at h1
    have he : χ.LFunction s * M χ - 1 = E χ * M χ + (P S₁ χ + P S₂ χ) := by
      dsimp only [E]; rw [← h1]; ring
    have hM := norm_mobiusMollifier_le χ K (s := s) (by linarith)
    change ‖M χ‖ ≤ _ at hM
    rw [he]
    have ht : ‖E χ*M χ+(P S₁ χ+P S₂ χ)‖ ≤ ‖E χ‖*(K:ℝ)+(‖P S₁ χ‖+‖P S₂ χ‖) :=
      (norm_add_le (E χ*M χ) _).trans (add_le_add (by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left hM (norm_nonneg _)) (norm_add_le (P S₁ χ) (P S₂ χ)))
    apply (pow_le_pow_left₀ (norm_nonneg _) ht 2).trans
    nlinarith only [sq_nonneg (‖E χ‖*(K:ℝ)-‖P S₁ χ‖),sq_nonneg (‖E χ‖*(K:ℝ)-‖P S₂ χ‖),sq_nonneg (‖P S₁ χ‖-‖P S₂ χ‖)]
  have hel : ∑ χ ∈ U, ‖E χ‖^2 ≤ (q.totient:ℝ)*(8*‖s‖^2*(q:ℝ)^(-2*d)) := abel_energy hd s hs
  have hpoly (S : Finset ℕ) (L D : ℕ) (hD : 0 < D) (hm : ∀ n ∈ S, D ≤ n)
      (hL : ∀ n ∈ S, n ≤ q*L) : ∑ χ ∈ U, ‖P S χ‖^2 ≤
        (q.totient:ℝ)*((L+1:ℕ)*(C*(D:ℝ)^(-d))) := by
    apply (sum_le_univ_sum_of_nonneg (fun χ ↦ sq_nonneg ‖P S χ‖)).trans
    apply (polynomial_energy S A s L hL).trans
    gcongr
    exact hB K q D S hD hm s (by linarith)
  have hlow := hpoly S₁ 1 K hK (fun n hn ↦ (mem_Ioc.mp hn).1.le) (fun n hn ↦ by simpa using (mem_Ioc.mp hn).2)
  have hhigh := hpoly S₂ K q (NeZero.pos q) (fun n hn ↦ (mem_Ioc.mp hn).1.le)
    (fun n hn ↦ (mem_Ioc.mp hn).2.trans_eq (Nat.mul_comm ..))
  push_cast at hlow hhigh
  apply (sum_le_sum (fun χ _ ↦ hrow χ)).trans
  simp only [← mul_sum,sum_add_distrib,← sum_mul]
  nlinarith only [mul_le_mul_of_nonneg_right hel (sq_nonneg (K:ℝ)),hlow,hhigh]

end RiemannMasullo.ConductorCylinder

namespace RiemannMasullo.ConductorCylinder

set_option quotPrecheck false
local notation "Zstrip" => {z : ℂ // 0 < z.re ∧ z.re < 1}

/-- Nonprincipal characters having at least one zero in the low right-hand
rectangle. Counting characters suffices since the whole row mass has a
separate logarithmic bound. -/
def lowZeroCharacters (q : ℕ) [NeZero q] (σ T : ℝ) : Finset (DirichletCharacter ℂ q) :=
  univ.filter (fun χ ↦ χ ≠ 1 ∧ ∃ z : Zstrip, σ ≤ z.val.re ∧ |z.val.im| ≤ T ∧ χ.LFunction z.val = 0)

private theorem detector_disk {d T : ℝ} (hd : 0 < d) (hd' : d ≤ 1/4) (hT : 1 ≤ T) :
    let c := 4+2*(1+T)^2/d
    let R := c-(1/2+d)
    let r := R-d/2
    0 ≤ r ∧ r < R ∧ (∀ z : Zstrip, 1/2+2*d ≤ z.val.re → |z.val.im| ≤ T →
      z.val ∈ closedBall (c:ℂ) r) ∧
      (∀ z ∈ sphere (c:ℂ) |R|, 1/2+d ≤ z.re ∧ ‖z‖ ≤ 2*c) := by
  intro c R r
  have he : c*d = 4*d+2*(1+T)^2 := by dsimp [c]; field_simp
  have hc : 4 ≤ c := by dsimp [c]; apply le_add_of_nonneg_right; positivity
  have hR : 0 < R := by dsimp [R]; linarith
  have hr : 0 ≤ r := by dsimp [r,R]; linarith
  refine ⟨hr,by dsimp [r]; linarith,?_,?_⟩
  · intro z hx hy
    have hx₁ := z.property.2
    have hD : ‖z.val-(c:ℂ)‖^2 = (z.val.re-c)^2+z.val.im^2 := by
      simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.ofReal_re,
        Complex.sub_im,Complex.ofReal_im,sub_zero]; ring
    have h₁ : d/2 ≤ z.val.re-(1/2+d+d/2) := by linarith
    have h₂ : c ≤ 2*c-z.val.re-(1/2+d+d/2) := by linarith
    have hm := mul_le_mul h₁ h₂ (by linarith) (by linarith)
    have hs := pow_le_pow_left₀ (abs_nonneg z.val.im) hy 2
    rw [sq_abs] at hs
    rw [mem_closedBall,dist_eq_norm,← sq_le_sq₀ (norm_nonneg _) hr,hD]
    dsimp only [r,R]
    nlinarith only [he,hs,hm,hT,hd]
  · intro z hz
    have he : ‖z-(c:ℂ)‖ = R := (show ‖z-(c:ℂ)‖=|R| by simpa only [mem_sphere,dist_eq_norm] using hz).trans (abs_of_pos hR)
    have hh := (Complex.abs_re_le_norm (z-(c:ℂ))).trans_eq he
    simp only [Complex.sub_re,Complex.ofReal_re,abs_le] at hh
    have hnorm := norm_add_le (z-(c:ℂ)) (c:ℂ)
    rw [sub_add_cancel,he,Complex.norm_real,Real.norm_of_nonneg (by linarith : 0 ≤ c)] at hnorm
    exact ⟨by dsimp [R] at hh; linarith,by dsimp [R] at hnorm; linarith⟩

private theorem differentiable_mollifier {q : ℕ} (χ : DirichletCharacter ℂ q) (K : ℕ) :
    Differentiable ℂ (mobiusMollifier χ K) := by
  unfold mobiusMollifier conductorPolynomial
  apply Differentiable.fun_sum
  intro n hn
  have h0 : (n:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  exact (differentiable_id.neg.const_cpow (.inl h0)).const_mul _

/-- A conductor-aspect zero detector derived from character orthogonality,
Abel summation and the ordinary Möbius mollifier. It controls arbitrarily
chosen positive widths with constants depending only on their lower bound. -/
theorem lowZeroCharacters_bound {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/4) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ (q : ℕ) [NeZero q] (K : ℕ), 1 ≤ K → K ≤ q → ∀ T : ℝ, 1 ≤ T →
      ((lowZeroCharacters q (1/2+2*d) T).card : ℝ) / q.totient ≤
        J*(1+T)^6*((K:ℝ)^2*(q:ℝ)^(-2*d) + (K:ℝ)^(-d) + ((K:ℝ)+1)*(q:ℝ)^(-d)) := by
  obtain ⟨C,hC,hmean⟩ := conductor_mollified_mean hd
  let A := 4+2/d
  let B := 32*A^2+2*C
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨(4*A/d)*3*B,by positivity,?_⟩
  intro q _ K hK hq T hT
  let X := 1+T
  let c := 4+2*X^2/d
  let R := c-(1/2+d)
  let r := R-d/2
  let S := lowZeroCharacters q (1/2+2*d) T
  let f (χ : DirichletCharacter ℂ q) (z : ℂ) := χ.LFunction z * mobiusMollifier χ K z - 1
  let u := (K:ℝ)^2*(q:ℝ)^(-2*d)
  let v := (K:ℝ)^(-d)
  let w := ((K:ℝ)+1)*(q:ℝ)^(-d)
  obtain ⟨hr,hR,hinside,hcircle⟩ := detector_disk hd hd' hT
  have hf (χ : DirichletCharacter ℂ q) (hχ : χ ∈ S) : Differentiable ℂ (f χ) :=
    ((χ.differentiable_LFunction (mem_filter.mp hχ).2.1).mul (differentiable_mollifier χ K)).sub_const 1
  have hlarge (χ : DirichletCharacter ℂ q) (hχ : χ ∈ S) : ∃ z ∈ closedBall (c:ℂ) r, 1 ≤ ‖f χ z‖ := by
    obtain ⟨z,hx,hy,hz⟩ := (mem_filter.mp hχ).2.2
    exact ⟨z.val,hinside z hx hy,by simp [f,hz]⟩
  have hX : 1 ≤ X := by dsimp [X]; linarith
  have hX₂ : 1 ≤ X^2 := one_le_pow₀ hX
  have hX₄ : 1 ≤ X^4 := one_le_pow₀ hX
  have hcb : c ≤ A*X^2 := by dsimp [c,A]; rw [add_mul]; ring_nf; linarith
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hv : 0 ≤ v := by dsimp [v]; positivity
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hU : S ⊆ univ.erase 1 := fun χ hχ ↦ mem_erase.mpr ⟨(mem_filter.mp hχ).2.1,mem_univ _⟩
  let M := (q.totient:ℝ)*3*(B*X^4*(u+v+w))
  have houter (z : ℂ) (hz : z ∈ sphere (c:ℂ) |R|) : ∑ χ ∈ S, ‖f χ z‖^2 ≤ M := by
    obtain ⟨hzr,hzn⟩ := hcircle z hz
    apply (sum_le_sum_of_subset_of_nonneg hU (fun χ _ _ ↦ sq_nonneg ‖f χ z‖)).trans
    apply (hmean q K hK hq z hzr).trans
    dsimp only [M]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hz' := pow_le_pow_left₀ (norm_nonneg z) (hzn.trans (mul_le_mul_of_nonneg_left hcb (by norm_num))) 2
    have hz'' : 8*‖z‖^2 ≤ B*X^4 := by dsimp [B]; nlinarith only [hz',mul_nonneg hC (by positivity : 0 ≤ X^4)]
    have h₂ : 2*C ≤ B*X^4 := by
      calc 2*C ≤ B := by dsimp [B]; nlinarith [sq_nonneg A]
           _ ≤ B*X^4 := le_mul_of_one_le_right hB hX₄
    calc _ = 8*‖z‖^2*u + 2*C*v + C*w := by dsimp only [u,v,w]; ring
         _ ≤ B*X^4*u + B*X^4*v + B*X^4*w := by
           exact add_le_add (add_le_add (mul_le_mul_of_nonneg_right hz'' hu)
             (mul_le_mul_of_nonneg_right h₂ hv)) (mul_le_mul_of_nonneg_right ((by linarith : C ≤ 2*C).trans h₂) hw)
         _ = _ := by ring
  have hratio : (R+r)/(R-r) ≤ (4*A/d)*X^2 := by
    have he : R-r=d/2 := by dsimp [r]; ring
    rw [he,div_le_iff₀ (by linarith)]
    have hh : 4*A/d*X^2*(d/2) = 2*A*X^2 := by field_simp; ring
    rw [hh]; dsimp only [r,R]; linarith
  have hcount := card_large_inside_disk_le S f hf hr hR hlarge houter
  rw [div_le_iff₀ (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q)))]
  exact hcount.trans ((mul_le_mul_of_nonneg_right hratio (by dsimp [M]; positivity)).trans_eq (by dsimp only [M,X,u,v,w]; ring))

/-- Sublinear exceptional set at one modulus and a polynomial height.
For `0 < d ≤ 1/4`, a proportion `O_d(q^(-d²/8))` of the nonprincipal
characters can have a zero to the right of `1/2+2d` below height `q^(d²/64)`. -/
theorem lowZeroCharacters_power_saving {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/4) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ (q : ℕ) [NeZero q],
      ((lowZeroCharacters q (1/2+2*d) ((q:ℝ)^(d^2/64))).card : ℝ) / q.totient ≤
        J*(q:ℝ)^(-(d^2/8)) := by
  obtain ⟨C,hC,h₀⟩ := lowZeroCharacters_bound hd hd'
  refine ⟨320*C, by positivity,?_⟩
  intro q _
  let Q : ℝ := q
  let k := d/4
  let t := d^2/64
  let T := Q^t
  let K := ⌊Q^k⌋₊
  have hq : 1 ≤ Q := by dsimp [Q]; exact_mod_cast NeZero.pos q
  have hq₀ : 0 < Q := by linarith
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hk' : k ≤ 1 := by dsimp [k]; linarith
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hT : 1 ≤ T := Real.one_le_rpow hq ht
  have hx : 1 ≤ Q^k := Real.one_le_rpow hq hk
  have hK : 1 ≤ K := (Nat.one_le_floor_iff _).mpr hx
  have hK' : (1:ℝ) ≤ K := by exact_mod_cast hK
  have hup : (K:ℝ) ≤ Q^k := Nat.floor_le (by positivity)
  have hlow : Q^k / 2 ≤ K := by linarith [Nat.lt_floor_add_one (Q^k)]
  have hKq : K ≤ q := by
    have he : (K:ℝ) ≤ (q:ℝ) := hup.trans ((Real.rpow_le_rpow_of_exponent_le hq hk').trans_eq (Real.rpow_one Q))
    exact_mod_cast he
  let u := (K:ℝ)^2*Q^(-2*d)
  let v := (K:ℝ)^(-d)
  let w := ((K:ℝ)+1)*Q^(-d)
  have h₁ : u ≤ Q^(k*2-2*d) := by
    rw [show k*2-2*d = k*2+(-2*d) by ring, Real.rpow_add hq₀,Real.rpow_mul hq₀.le,Real.rpow_two]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hup 2) (Real.rpow_nonneg hq₀.le _)
  have h₂ : v ≤ 2*Q^(-k*d) := by
    apply (Real.rpow_le_rpow_of_nonpos (by positivity : 0 < Q^k/2) hlow (neg_nonpos.mpr hd.le)).trans
    rw [Real.div_rpow (Real.rpow_nonneg hq₀.le _) (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      div_inv_eq_mul, ← Real.rpow_mul hq₀.le, show k*(-d) = -k*d by ring, mul_comm]
    exact mul_le_mul_of_nonneg_right ((Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2)
      (by linarith : d ≤ 1)).trans_eq (Real.rpow_one 2)) (Real.rpow_nonneg hq₀.le _)
  have h₃ : w ≤ 2*Q^(k-d) := by
    rw [sub_eq_add_neg,Real.rpow_add hq₀,← mul_assoc]
    exact mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hq₀.le _)
  have hquad : d^2 ≤ d := by nlinarith [mul_nonneg hd.le (by linarith : 0 ≤ 1-d)]
  have hin (x : ℝ) (h : t*6+x ≤ -(d^2/8)) : T^6*Q^x ≤ Q^(-(d^2/8)) := by
    rw [show T^6 = Q^(t*6) by simpa [T] using (Real.rpow_mul_natCast hq₀.le t 6).symm]
    rw [← Real.rpow_add hq₀]
    exact Real.rpow_le_rpow_of_exponent_le hq h
  have hu := hin (k*2-2*d) (by dsimp only [k,t]; nlinarith)
  have hv := hin (-k*d) (by dsimp only [k,t]; nlinarith)
  have hw := hin (k-d) (by dsimp only [k,t]; nlinarith)
  have hpow : (1+T)^6 ≤ 64*T^6 := (pow_le_pow_left₀ (by linarith) (by linarith : 1+T ≤ 2*T) 6).trans_eq (by ring)
  have hV : 0 ≤ u+v+w := by dsimp [u,v,w]; positivity
  have hm := h₀ q K hK hKq T hT
  change _ ≤ C*(1+T)^6*(u+v+w) at hm
  apply hm.trans
  calc C*(1+T)^6*(u+v+w) ≤ C*(64*T^6)*(u+v+w) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC) hV
       _ = 64*C*(T^6*u+T^6*v+T^6*w) := by ring
       _ ≤ 64*C*(Q^(-(d^2/8)) + 2*Q^(-(d^2/8)) + 2*Q^(-(d^2/8))) := by
         apply mul_le_mul_of_nonneg_left _ (by positivity)
         have hT₀ := pow_nonneg (by linarith : 0 ≤ T) 6
         exact add_le_add (add_le_add ((mul_le_mul_of_nonneg_left h₁ hT₀).trans hu)
           ((mul_le_mul_of_nonneg_left h₂ hT₀).trans (by linarith only [hv])))
           ((mul_le_mul_of_nonneg_left h₃ hT₀).trans (by linarith only [hw]))
       _ = _ := by dsimp [Q]; ring

end RiemannMasullo.ConductorCylinder
