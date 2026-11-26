module

public import RiemannMasullo.AppB_AnalyticNT.HeckePolynomialBounds
public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.PolynomialExtrapolation
import Mathlib.Tactic

/-! # Polynomial-length ordinary ideal samples on the critical line

A finite complex exponential polynomial of the height evaluates the ordinary Hecke
continuation with eventual uniform error less than `2⁻ⁿ` through the last successor of
the critical-line grid. The number of ideal-norm indices is polynomial in the mesh
index, with a degree prescribed by the number field degree alone.
-/

@[expose] public noncomputable section
open Complex Filter Function IsDedekindDomain NumberField Set
open scoped Topology NNReal

namespace RiemannMasullo.PolynomialIdealSamples
open FiniteHeckeSamples FiniteTaylor
variable {F : Type*} [Field F] [NumberField F]
local notation "Cᶠ" => IdeleClassGroup (𝓞 F) F
local notation "Uᶠ" => PontryaginDual Cᶠ
local notation "Hp" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Finite critical-line evaluation with the original corrected ordinary ideal coefficients. -/
def heckeSample (χ : Uᶠ) (D n : ℕ) (t : ℝ) : ℂ :=
  sample (coefficients χ) D (meshBlock n) t / polarFactor (point t)

/-- On each mesh the `m`-sum stops before `(4(n+2))^(D+6)`. -/
theorem heckeSample_eq (χ : Uᶠ) (D n : ℕ) (t : ℝ) :
    let j := meshBlock n
    let a (d : ℕ) := heckeNormCoefficient (ideleClassNormTwist χ 0) (d:ℝ)
    heckeSample χ D n t =
      (∑ m ∈ Finset.range (length D j),
        (a m - (if 2 ∣ m then 4*a (m/2) else 0) + (if 4 ∣ m then 4*a (m/4) else 0)) *
        frequency m (center j t) *
        ∑ k ∈ Finset.range (degree D j),
          ((point t-center j t)*(-(Real.log m : ℂ)))^k/(k.factorial:ℂ)) / polarFactor (point t) := by
  simp only [heckeSample,sample,extrapolate,coefficients_eq_ideal_values]

/-- A bound of `O(R log R)` for the log modulus on the expanding disks gives
the eventual dyadic enclosure over the entire real height range, including the successor. -/
theorem heckeSample_of_disks (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (D : ℕ)
    (hg : ∀ᶠ n : ℕ in atTop, DiskBound (fun w ↦ polarFactor w*L w) D (meshBlock n)) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ (n:ℝ)+1 →
      ‖L (point t)-heckeSample χ D n t‖ ≤ (1/2:ℝ)^n := by
  let b := coefficients χ
  have hsr (w : ℂ) (hw : 1 < w.re) : polarFactor w*L w = LSeries b w := by
    rw [he ⟨w,hw⟩]
    exact (coefficients_hasSum χ ⟨w,hw⟩).LSeries_eq.symm
  have hb : LSeriesSummable b 2 := (coefficients_hasSum χ ⟨2,by norm_num⟩).LSeriesSummable
  let C := (Real.sqrt 2-1)^2
  have hC : 0<C := sq_pos_of_pos (by nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2])
  obtain ⟨N,hN⟩ := exists_nat_ge ((2+coefficientMass b)/C)
  filter_upwards [hg,eventually_ge_atTop (max 1 N)] with n hg hn
  intro t ht
  let j := meshBlock n
  have hbnd := (meshBlock_bounds n).1
  have hs : (2:ℕ) ≤ scale j := by dsimp [j]; omega
  have ht' : |t| ≤ (scale j : ℝ) := ht.trans (by exact_mod_cast hbnd)
  have hpre := norm_sub_sample b hb _ (poleCleared_entire τ hτ χ hχ L hL he) hsr D j hs hg t ht'
  have hden : C ≤ ‖polarFactor (point t)‖ := critical_factor_lower t
  have hne : polarFactor (point t) ≠ 0 := norm_pos_iff.mp (hC.trans_le hden)
  have heq : L (point t) - heckeSample χ D n t =
      (polarFactor (point t)*L (point t)-sample b D j t)/polarFactor (point t) := by
    unfold heckeSample
    field_simp [hne]
    rfl
  rw [heq,norm_div]
  have hpow : (n:ℝ) ≤ (2:ℝ)^n := by exact_mod_cast (Nat.lt_pow_self (by decide : 1<2) (n := n)).le
  have hCN : (2+coefficientMass b)/C ≤ (2:ℝ)^n := by
    apply hN.trans
    exact (show (N:ℝ) ≤ n by exact_mod_cast (le_trans (le_max_right 1 N) hn)).trans hpow
  have he : 2*n ≤ 3*(j+1)*scale j := by
    have hj : 1 ≤ j+1 := by omega
    have hmul := Nat.mul_le_mul_right (scale j) hj
    rw [Nat.mul_assoc]
    change n+1 ≤ scale j at hbnd
    omega
  have hbig : ((2:ℝ)^n)*((2:ℝ)^n) ≤ (2:ℝ)^(3*(j+1)*scale j) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  calc _ ≤ ((2+coefficientMass b)/(2:ℝ)^(3*(j+1)*scale j))/C :=
         (div_le_div_of_nonneg_left (norm_nonneg _) hC hden).trans
           (div_le_div_of_nonneg_right hpre hC.le)
       _ ≤ (1/2:ℝ)^n := by
         rw [one_div, inv_pow, ← one_div, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
         have hcn := (div_le_iff₀ hC).mp hCN
         nlinarith only [mul_le_mul_of_nonneg_right hcn (show 0≤(2:ℝ)^n by positivity),
           mul_le_mul_of_nonneg_right hbig hC.le]

/-- The degree alone prescribes the Taylor order and the polynomial ideal-norm
cutoff. The onset of the error enclosure may depend on the field and character. -/
theorem eventually_polynomial_heckeSample (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ (n:ℝ)+1 →
      ‖L (point t)-heckeSample χ (4*Module.finrank ℚ F+1) n t‖ ≤ (1/2:ℝ)^n := by
  obtain ⟨B,K,hB,hK,hr,hl⟩ := poleCleared_boundary_bounds τ hτ χ hχ L hL he
  apply heckeSample_of_disks τ hτ χ hχ L hL he
  let d := Module.finrank ℚ F
  obtain ⟨N,hN⟩ := exists_nat_ge (K^5*(2*(B+40))^(4*d))
  filter_upwards [eventually_ge_atTop N] with n hn
  exact diskBound_of_boundaries _ (poleCleared_entire τ hτ χ hχ L hL he)
    (fun _ _ hab ↦ poleCleared_polynomial_growth χ L hL he hab) d B K hB hK hr hl
    (meshBlock n) (hN.trans (by exact_mod_cast (show N ≤ scale (meshBlock n) from
      hn.trans (Nat.le_succ n |>.trans (meshBlock_bounds n).1))))

/-- Pure, finitely many exponential frequencies in the real height. The
shifted mesh index supplies a factor of eight of spare precision. -/
def frequencySample (χ : Uᶠ) (n : ℕ) (t : ℝ) : ℂ :=
  sample (coefficients χ) (4*Module.finrank ℚ F+1) (meshBlock (n+3)) t *
    (dyadicFrequency t * ∑ k ∈ Finset.range (8*n), dyadicFrequency t^k)^2

/-- Expand every field-dependent coefficient into the finite sum over ordinary
integral ideals of a single positive integral norm (or zero at index zero). -/
theorem frequencySample_ideal_formula (χ : Uᶠ) (n : ℕ) (t : ℝ) :
    let D := 4*Module.finrank ℚ F+1
    let j := meshBlock (n+3)
    let u := scale j
    let a (m : ℕ) := heckeNormCoefficient (ideleClassNormTwist χ 0) (m:ℝ)
    let v := (2:ℂ)⁻¹ * exp ((Real.log 2:ℂ)*point t)
    frequencySample χ n t =
      (∑ m ∈ Finset.range (length D j),
        (a m-(if 2∣m then 4*a (m/2) else 0)+(if 4∣m then 4*a (m/4) else 0)) *
        (exp (-(Real.log m:ℂ)*(4*(u:ℂ)+1/2)) * exp (-(Real.log m:ℂ)*(t:ℂ)*I)) *
        ∑ k ∈ Finset.range (degree D j),
          (4*(u:ℂ)*(Real.log m:ℂ))^k/(k.factorial:ℂ)) *
      (v*∑ k ∈ Finset.range (8*n), v^k)^2 := by
  dsimp only
  let j := meshBlock (n+3)
  let u := scale j
  have ec : center j t = (4*(u:ℂ)+1/2)+(t:ℂ)*I := by
    apply Complex.ext <;> simp [center,u,Complex.mul_re,Complex.mul_im]
  have ed : point t-center j t = -(4*(u:ℂ)) := by
    apply Complex.ext <;> simp [point,center,u,Complex.sub_re,Complex.sub_im]
  have ef (m : ℕ) : frequency m (center j t) = exp (-(Real.log m:ℂ)*(4*(u:ℂ)+1/2)) *
      exp (-(Real.log m:ℂ)*(t:ℂ)*I) := by
    rw [frequency,ec, ← exp_add]
    congr 1
    ring
  dsimp only [j] at ef ed
  simp only [frequencySample,sample,extrapolate,coefficients_eq_ideal_values,dyadicFrequency,
    ef,ed,neg_mul_neg]
  rfl

/-- Number of distinct ordinary ideal norms that can occur in the pure frequency formula. -/
theorem frequencySample_cutoff (n : ℕ) :
    length (4*Module.finrank ℚ F+1) (meshBlock (n+3)) ≤ (4*(n+5))^(4*Module.finrank ℚ F+7) := by
  simpa only [Nat.add_assoc] using length_meshBlock_le (4*Module.finrank ℚ F+1) (n+3)

theorem frequencySample_eq (χ : Uᶠ) (n : ℕ) (t : ℝ) :
    frequencySample χ n t = heckeSample χ (4*Module.finrank ℚ F+1) (n+3) t *
      (1-dyadicFrequency t^(8*n))^2 := by
  let v := dyadicFrequency t
  let S := ∑ k ∈ Finset.range (8*n), v^k
  have hx : (2:ℂ)*frequency 2 (point t) ≠ 0 := by
    apply norm_pos_iff.mp
    rw [show ‖(2:ℂ)*frequency 2 (point t)‖ = Real.sqrt 2 from norm_twice_frequency_critical t]
    positivity
  have hq : polarRoot (point t)*v = v-1 := by
    have ev : v = ((2:ℂ)*frequency 2 (point t))⁻¹ := dyadicFrequency_eq_inv t
    rw [polarRoot,sub_mul,one_mul,ev,mul_inv_cancel₀ hx]
  have hs : polarRoot (point t)*(v*S) = v^(8*n)-1 := by
    rw [←mul_assoc,hq,mul_comm]
    exact geom_sum_mul v _
  have hδ : 0<(Real.sqrt 2-1)^2 := sq_pos_of_pos (by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2])
  have hne : polarFactor (point t) ≠ 0 := norm_pos_iff.mp (hδ.trans_le (critical_factor_lower t))
  let A := sample (coefficients χ) (4*Module.finrank ℚ F+1) (meshBlock (n+3)) t
  change A*(v*S)^2 = A/polarFactor (point t)*(1-v^(8*n))^2
  field_simp [hne]
  rw [polarFactor,show (1-v^(8*n))^2=(v^(8*n)-1)^2 by ring,←hs]
  ring

private theorem norm_geometric_correction (w a y : ℂ) (hy : ‖y‖ ≤ 1) :
    ‖w-a*(1-y)^2‖ ≤ 4*‖w-a‖+3*‖w‖*‖y‖ := by
  have h₁ : ‖1-y‖ ≤ 2 := (norm_sub_le _ _).trans (by rw [norm_one]; linarith)
  have h₂ : ‖2-y‖ ≤ 3 := (norm_sub_le _ _).trans (by norm_num; linarith)
  have hs : ‖1-y‖^2 ≤ 4 := (pow_le_pow_left₀ (norm_nonneg _) h₁ 2).trans_eq (by norm_num)
  calc _ = ‖(w-a)*(1-y)^2+(w*(2-y))*y‖ := by congr 1; ring
       _ ≤ ‖(w-a)*(1-y)^2‖+‖(w*(2-y))*y‖ := norm_add_le _ _
       _ = ‖w-a‖*‖1-y‖^2+(‖w‖*‖2-y‖)*‖y‖ := by simp only [norm_mul,norm_pow]
       _ ≤ ‖w-a‖*4+(‖w‖*3)*‖y‖ := by gcongr
       _ = _ := by ring

/-- A strict dyadic enclosure on the full height continuum for the finite
exponential polynomial. No inverse height-dependent factor remains in the formula. -/
theorem eventually_frequencySample_error (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, |t| ≤ (n:ℝ)+1 →
      ‖L (point t)-frequencySample χ n t‖ < (1/2:ℝ)^n := by
  obtain ⟨A,hA,p,hp⟩ := critical_norm_polynomial_bound τ hτ χ hχ L hL he
  have hs : Tendsto (fun n : ℕ ↦ n+3) atTop atTop :=
    tendsto_atTop_mono (fun n ↦ Nat.le_add_right n 3) tendsto_id
  have hd := hs.eventually (eventually_polynomial_heckeSample τ hτ χ hχ L hL he)
  have hl := tendsto_pow_const_mul_const_pow_of_lt_one p (by norm_num : 0 ≤ (1/8:ℝ))
    (by norm_num : (1/8:ℝ)<1)
  have hlim : Tendsto (fun n : ℕ ↦ (3*A*3^p)*((n:ℝ)^p*(1/8:ℝ)^n)) atTop (𝓝 0) := by
    simpa using hl.const_mul (3*A*3^p)
  filter_upwards [hd,hlim.eventually_lt_const (by norm_num : (0:ℝ)<1/2), eventually_ge_atTop (1:ℕ)]
    with n hsample hn hn₁
  intro t ht
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn₁
  have hd' := hsample t (by push_cast; linarith : |t|≤((n+3:ℕ):ℝ)+1)
  rw [pow_add] at hd'
  have hF : ‖L (point t)‖ ≤ A*(3^p*(n:ℝ)^p) := by
    refine (hp t).trans (mul_le_mul_of_nonneg_left ?_ hA.le)
    rw [←mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) _
  have hpow : (1/16:ℝ)^n*(2:ℝ)^n = (1/8:ℝ)^n := by rw [←mul_pow]; norm_num
  have hpart : 3*‖L (point t)‖*(1/16:ℝ)^n < (1/2)*(1/2:ℝ)^n := by
    rw [show (1/2:ℝ)*(1/2:ℝ)^n = (1/2)/(2:ℝ)^n by rw [div_pow,one_pow]; ring]
    apply (lt_div_iff₀ (by positivity)).mpr
    calc _ = 3*‖L (point t)‖*(1/8:ℝ)^n := by rw [←hpow]; ring
         _ ≤ 3*(A*(3^p*(n:ℝ)^p))*(1/8:ℝ)^n := by gcongr
         _ = (3*A*3^p)*((n:ℝ)^p*(1/8:ℝ)^n) := by ring
         _ < _ := hn
  have hnorm : ‖dyadicFrequency t^(8*n)‖ ≤ 1 := by
    rw [norm_dyadicFrequency_pow]
    exact pow_le_one₀ (by norm_num) (by norm_num)
  rw [frequencySample_eq]
  refine (norm_geometric_correction _ _ _ hnorm).trans_lt ?_
  rw [norm_dyadicFrequency_pow]
  linarith

end RiemannMasullo.PolynomialIdealSamples
