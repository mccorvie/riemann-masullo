module

public import RiemannMasullo.Ch03_IdelicZeta.Sec2
import Mathlib.Tactic

/-! # Uniform reflected archimedean gamma bound on half-integer lines -/

@[expose] public noncomputable section
open Complex Filter Function NumberField Set IsDedekindDomain
open scoped ComplexConjugate Topology NNReal
namespace RiemannMasullo.PolynomialIdealSamples
variable {F : Type*} [Field F] [NumberField F]
local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)

/-- At twist zero, restriction of the inverse unitary character gives reciprocal values. -/
private theorem infinitePlaceRestriction_inv_twist_zero (χ : U[F]) (v : InfinitePlace F)
    (x : v.Completionˣ) :
    infinitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ 0) x =
      (infinitePlaceRestriction F v (ideleClassNormTwist χ 0) x)⁻¹ := by
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v x
  change ((χ⁻¹ g : Circle) : ℂ) * _ ^ (0 : ℂ) = ((χ g : ℂ) * _ ^ (0 : ℂ))⁻¹
  simp only [Complex.cpow_zero, mul_one]
  rfl

/-- Inversion negates the real place's radial exponent and preserves its sign parity. -/
private theorem realHeckeCharacter_parameters_inv (χ : U[F]) (v : InfinitePlace F)
    (hv : v.IsReal) :
    (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(realHeckeCharacter_parameters χ v hv).exists.choose.1,
        (realHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (realHeckeCharacter_parameters χ⁻¹ v hv).unique
    (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1, fun x ↦ ?_⟩
  dsimp only
  rw [infinitePlaceRestriction_inv_twist_zero, ha.2 x, mul_inv, Complex.cpow_neg]
  congr 1
  rw [← inv_pow]
  split <;> simp

/-- Inversion negates both the radial exponent and the angular weight at a complex place. -/
private theorem complexHeckeCharacter_parameters_inv (χ : U[F]) (v : InfinitePlace F)
    (hv : v.IsComplex) :
    (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(complexHeckeCharacter_parameters χ v hv).exists.choose.1,
        -(complexHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (complexHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (complexHeckeCharacter_parameters χ⁻¹ v hv).unique
    (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1, fun x ↦ ?_⟩
  dsimp only
  rw [infinitePlaceRestriction_inv_twist_zero, ha.2 x, mul_inv, Complex.cpow_neg, zpow_neg]

/-- The raw gamma quotient vanishes when its denominator is at a pole.
At all other inputs the recurrence can be applied for every step. -/
theorem norm_gamma_shift_le (G : ℂ → ℂ) (d : ℕ)
    (step : ∀ z : ℂ, z ≠ 0 → G (z+d) = G z*z/2/Real.pi)
    (zeroes : ∀ i : ℕ, G (-(i:ℂ)*d) = 0) (z : ℂ) (A : ℝ) (hA : 0 ≤ A) (m : ℕ)
    (hle : ∀ i < m, ‖z+(i:ℂ)*d‖ ≤ A) :
    ‖G (z+(m:ℂ)*d)/G z‖ ≤ A^m := by
  by_cases hz : G z = 0
  · simp [hz, pow_nonneg hA]
  have hn (i : ℕ) : z+(i:ℂ)*d ≠ 0 := by
    intro h
    have e : z = -(i:ℂ)*d := by linear_combination h
    exact hz (e ▸ zeroes i)
  induction m with
  | zero => simp [hz]
  | succ m ih =>
    let x := z+(m:ℂ)*d
    have hs : z+((m+1:ℕ):ℂ)*d = x+d := by dsimp [x]; push_cast; ring
    have he : G (z+((m+1:ℕ):ℂ)*d)/G z = (G x/G z)*(x/2/Real.pi) := by
      rw [hs,step x (hn m)]
      ring
    have hf : ‖x/2/(Real.pi:ℂ)‖ ≤ A := by
      rw [norm_div,norm_div,Complex.norm_two,Complex.norm_real,Real.norm_of_nonneg Real.pi_pos.le]
      exact ((div_le_self (by positivity) (by linarith [Real.one_le_pi_div_two])).trans
        (div_le_self (norm_nonneg x) (by norm_num))).trans (hle m (Nat.lt_succ_self _))
    rw [he,norm_mul,pow_succ]
    exact mul_le_mul (ih (fun i hi ↦ hle i (hi.trans (Nat.lt_succ_self m)))) hf (norm_nonneg _)
      (pow_nonneg hA _)

/-- The same constant works for all integer shifts and all heights. The exponent
counts one recurrence per real place and two per complex place. -/
theorem norm_heckeGammaRatio_halfInteger (χ : U[F]) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (m : ℕ) (s : ℂ), s.re = 1/2-(m:ℝ) →
      ‖heckeGammaFactor χ⁻¹ (1-s)/heckeGammaFactor χ s‖ ≤
        (B+3*(m:ℝ)+|s.im|)^(Module.finrank ℚ F*m) := by
  classical
  let β (v : InfinitePlace F) : ℂ :=
    if hv : v.IsReal then
      let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      a.1+(a.2.val:ℂ)
    else
      let a := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      a.1+(a.2.natAbs:ℂ)/2
  let γ (ψ : U[F]) (v : InfinitePlace F) (s : ℂ) : ℂ :=
    if hv : v.IsReal then
      let a := (realHeckeCharacter_parameters ψ v hv).exists.choose
      Gammaℝ (s+a.1+(a.2.val:ℂ))
    else
      let a := (complexHeckeCharacter_parameters ψ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Gammaℂ (s+a.1+(a.2.natAbs:ℂ)/2)/2
  let B := 1+∑ v, ‖β v‖
  have hB : 1 ≤ B := by dsimp only [B]; linarith [Finset.sum_nonneg (s:=Finset.univ) (fun v _ ↦ norm_nonneg (β v))]
  refine ⟨B,hB,fun m s hs ↦ ?_⟩
  let A := B+3*(m:ℝ)+|s.im|
  have hA : 1 ≤ A := by dsimp [A]; linarith [abs_nonneg s.im,Nat.cast_nonneg (α:=ℝ) m]
  have hlin (v : InfinitePlace F) (i d : ℕ) (hi : i*d ≤ 2*m) :
      ‖s+β v+(i:ℂ)*d‖ ≤ A := by
    have hb : ‖β v‖ ≤ ∑ w, ‖β w‖ := Finset.single_le_sum (fun w _ ↦ norm_nonneg (β w)) (Finset.mem_univ v)
    have hm : |s.re| ≤ (m:ℝ)+1 := by rw [hs,abs_le]; constructor <;> linarith [Nat.cast_nonneg (α:=ℝ) m]
    have hi' : (i:ℝ)*d ≤ 2*(m:ℝ) := by exact_mod_cast hi
    have h₁ := norm_add_le (s+β v) ((i:ℂ)*d)
    rw [norm_mul,Complex.norm_natCast,Complex.norm_natCast] at h₁
    dsimp [A,B]
    linarith [norm_add_le s (β v),Complex.norm_le_abs_re_add_abs_im s]
  have shift {a : ℂ} (ha : a.re = 0) (b : ℝ) :
      conj (1-s + -a + (b:ℂ)) = s+(a+(b:ℂ))+2*(m:ℂ) := by
    apply Complex.ext <;> simp [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, ha, hs]; ring
  have localBound (v : InfinitePlace F) : ‖γ χ⁻¹ v (1-s)/γ χ v s‖ ≤ A^(v.mult*m) := by
    by_cases hv : v.IsReal
    · let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      have ha : a.1.re = 0 := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
      have hb : β v = a.1+(a.2.val:ℂ) := by simp [β,hv,a]
      have hh := norm_gamma_shift_le Gammaℝ 2 (fun _ h ↦ Gammaℝ_add_two h)
        (fun i ↦ Gammaℝ_eq_zero_iff.mpr ⟨i,by push_cast; ring⟩) (s+β v) A (zero_le_one.trans hA) m
        (fun i hi ↦ hlin v i 2 (by omega))
      rw [hb,norm_div] at hh
      simp only [γ,dite_eq_left hv,realHeckeCharacter_parameters_inv,norm_div]
      change ‖Gammaℝ (1-s + -a.1+(a.2.val:ℂ))‖/‖Gammaℝ (s+a.1+(a.2.val:ℂ))‖ ≤ _
      rw [← Complex.norm_conj (Gammaℝ _), ← Gammaℝ_conj, ← Complex.ofReal_natCast,shift ha]
      rw [hv.mult_eq_one,one_mul]
      convert hh using 1; push_cast; ring_nf
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let a := (complexHeckeCharacter_parameters χ v hv').exists.choose
      have ha : a.1.re = 0 := (complexHeckeCharacter_parameters χ v hv').exists.choose_spec.1
      have hb : β v = a.1+(a.2.natAbs:ℂ)/2 := by simp [β,hv,a]
      have hh := norm_gamma_shift_le Gammaℂ 1 (fun _ h ↦ by simpa using Gammaℂ_add_one h)
        (fun i ↦ by simp [Gammaℂ_def, Complex.Gamma_neg_nat_eq_zero]) (s+β v) A (zero_le_one.trans hA)
        (2*m) (fun i hi ↦ hlin v i 1 (by omega))
      rw [hb,norm_div] at hh
      simp only [γ,dite_eq_right hv,complexHeckeCharacter_parameters_inv,Int.natAbs_neg,
        div_div_div_cancel_right₀ (two_ne_zero' ℂ),norm_div]
      change ‖Gammaℂ (1-s + -a.1+(a.2.natAbs:ℂ)/2)‖/‖Gammaℂ (s+a.1+(a.2.natAbs:ℂ)/2)‖ ≤ _
      rw [← Complex.norm_conj (Gammaℂ _), ← Gammaℂ_conj,
        show (↑a.2.natAbs:ℂ)/2 = (((a.2.natAbs:ℝ)/2:ℝ):ℂ) by push_cast; rfl,shift ha]
      rw [hv'.mult_eq_two]
      convert hh using 1; push_cast; ring_nf
  change ‖(∏ v, γ χ⁻¹ v (1-s))/(∏ v, γ χ v s)‖ ≤ _
  rw [← Finset.prod_div_distrib,norm_prod]
  calc _ ≤ ∏ v : InfinitePlace F, A^(v.mult*m) :=
            Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun v _ ↦ localBound v)
       _ = _ := by rw [Finset.prod_pow_eq_pow_sum, ← Finset.sum_mul, InfinitePlace.sum_mult_eq]

end RiemannMasullo.PolynomialIdealSamples
