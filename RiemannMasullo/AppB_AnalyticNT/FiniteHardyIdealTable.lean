module

public import RiemannMasullo.AppB_AnalyticNT.PolynomialIdealSamples
public import RiemannMasullo.ForMathlib.Analysis.Complex.DiskFiniteFourier
import RiemannMasullo.AppB_AnalyticNT.Sec6
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.Tactic

/-!
# Finite ideal tables for the Cayley disk coefficients of an ordinary Hecke L-function

All arithmetic entries are finite sums of ordinary ideal character values. Extending the
expanding-center extrapolate to a closed disk gives exponential accuracy on the radius-one-fifth
Cayley chart. A finite Fourier transform recovers all coefficients through n simultaneously.
The norm cutoff has degree 4[F:ℚ]+7 in n. The same degree suffices for logarithmic-derivative
rows, using two evaluations per angular node and the ordinary Euler nonvanishing theorem.
-/

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain Metric NumberField Set
open scoped NNReal Topology
namespace RiemannMasullo.FiniteHardyIdealTable

open DiskFiniteFourier
open FiniteHeckeSamples FiniteTaylor PolynomialIdealSamples

/-- The moving Taylor polynomial approximates the entire corrected series throughout the target disk. -/
theorem norm_sub_extrapolate_on_disk (b : ArithmeticFunction ℂ) (hb : LSeriesSummable b 2)
    (G : ℂ → ℂ) (hG : Differentiable ℂ G)
    (hseries : ∀ w : ℂ, 1 < w.re → G w = LSeries b w)
    (D j : ℕ) (hj : 2 ≤ scale j) (hbound : DiskBound G D j) {z : ℂ} (hz : ‖z-center j 0‖ ≤ 4*(scale j : ℝ)) :
    ‖G z-extrapolate b (degree D j) (length D j) (center j 0) (z-center j 0)‖ ≤ (2+coefficientMass b)/(2:ℝ)^(3*(j+1)*scale j) := by
  let u := scale j
  let M := length D j
  let K := degree D j
  let U := (2:ℝ)^(D*(j+1)*u)
  let P := dirichletPolynomial b M
  have hu : (2:ℝ) ≤ u := by exact_mod_cast hj
  have hM : 0 < M := by dsimp [M,length]; positivity
  have hS (w : ℂ) (hw : w ∈ sphere (center j 0) (2*(u:ℝ))) :
      ‖G w-P w‖ ≤ coefficientMass b/(M:ℝ)^u := by
    have hr := (Complex.abs_re_le_norm (w-center j 0)).trans (mem_closedBall_iff_norm.mp (sphere_subset_closedBall hw))
    change |w.re-(4*(u:ℝ)+1/2)| ≤ 2*(u:ℝ) at hr
    have hs : 2+(u:ℝ) ≤ w.re := by linarith [(abs_le.mp hr).1]
    rw [hseries w (by linarith)]
    exact dirichlet_tail b hb hM u w hs
  let c := center j 0
  let E := fun w : ℂ ↦ G w-extrapolate b K M c (w-c)
  have hE : Differentiable ℂ E := by
    unfold E extrapolate
    fun_prop
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball c (4*(u:ℝ))) isBounded_ball
    hE.diffContOnCl
  · intro w hw
    rw [frontier_ball c (by positivity : 4*(u:ℝ) ≠ 0)] at hw
    have hT : ‖w-center j 0‖ = 2*(2*(u:ℝ)) := by
      simpa only [c, show 2*(2*(u:ℝ)) = 4*(u:ℝ) by ring] using mem_sphere_iff_norm.mp hw
    have h := two_disks (U := U) (hV₀ := show 0 ≤ coefficientMass b/(M:ℝ)^u by
        unfold coefficientMass; positivity) (by positivity : 0 < 2*(u:ℝ))
        (fun w _ ↦ hG.analyticAt w) (fun w _ ↦ analytic_dirichletPolynomial b M w)
        (fun w hw ↦ hbound 0 (by simp) w (by simpa only [show 4*(2*(u:ℝ)) = 8*(scale j:ℝ) by dsimp [u]; ring] using hw))
        hS hT K
    rw [taylorSum_dirichletPolynomial] at h
    have eK : (2:ℝ)^K = U * (2:ℝ)^(3*(j+1)*u) := by
      rw [← pow_add]
      congr 1
      dsimp [K,degree,u]
      ring
    have eM : (M:ℝ)^u = (2:ℝ)^K * (2:ℝ)^(3*(j+1)*u) := by
      dsimp [M,length]
      push_cast
      rw [← pow_mul, ← pow_mul, ← pow_add]
      congr 1
      dsimp [K,degree,u]
      ring
    refine h.trans ?_
    rw [eM, eK]
    dsimp only [U,u]
    apply le_of_eq
    field_simp
  · rw [closure_ball _ (by positivity : 4*(u:ℝ) ≠ 0)]
    exact mem_closedBall_iff_norm.mpr hz

open FiniteHeckeSamples FiniteTaylor PolynomialIdealSamples

/-- The Cayley coordinate centered at 2 for the right critical half-plane. -/
def toHalf (z : ℂ) : ℂ := (2+z)/(1-z)
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Hp" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- The three ordinary ideal-norm coefficients of the squared pole filter. -/
def corrected (a : ℕ → ℂ) (m : ℕ) : ℂ :=
  a m - (if 2 ∣ m then 4*a (m/2) else 0) + (if 4 ∣ m then 4*a (m/4) else 0)

/-- The sum of the ordinary Hecke character over nonzero ideals of a fixed integral norm. -/
def idealValue (χ : U𝔽) (m : ℕ) : ℂ := heckeNormCoefficient (ideleClassNormTwist χ 0) (m : ℝ)

/-- The elementary local factor that converts a corrected series back to the normalized ordinary series. -/
def multiplier (δ N : ℕ) (z : ℂ) : ℂ :=
  (((1-z)/3)^N * ((1+2*z)/(2+z))^δ) / polarFactor (toHalf z)

/-- A finite formula in the supplied arithmetic coefficients and known scalar functions. -/
def chartValue (a : ℕ → ℂ) (δ d N m : ℕ) (z : ℂ) : ℂ :=
  let D := 4*d+1
  let j := meshBlock m
  let c := center j 0
  multiplier δ N z *
    ∑ h ∈ Finset.range (length D j), corrected a h * frequency h c *
      ∑ k ∈ Finset.range (degree D j),
        ((toHalf z-c) * (-(Real.log h : ℂ)))^k / (k.factorial : ℂ)

open scoped Classical in
/-- The principal-character flag, supplied separately to the finite tables. -/
def principalIndex (χ : U𝔽) : ℕ := if χ = 1 then 1 else 0

/-- The ordinary function with explicitly supplied elementary factors. -/
def weightedChart (δ N : ℕ) (L : ℂ → ℂ) (z : ℂ) : ℂ :=
  ((1-z)/3)^N * ((1+2*z)/(2+z))^δ * L (toHalf z)

/-- The ordinary finite L-function on the chart, with both explicit disk factors. -/
def ordinaryDisk (χ : U𝔽) (L : ℂ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ((1-z)/3)^N * ((1+2*z)/(2+z))^(principalIndex χ) * L (toHalf z)

theorem chart_distance {z : ℂ} (hz : ‖z‖ ≤ 1/5) :
    ‖toHalf z-2‖ ≤ 3/4 := by
  have h1 : 1-z ≠ 0 := by intro e; have := sub_eq_zero.mp e; simp [←this] at hz; norm_num at hz
  have hd : (4/5:ℝ) ≤ ‖1-z‖ := by
    have := norm_sub_norm_le (1:ℂ) z
    rw [norm_one] at this
    linarith
  have he : toHalf z-2 = 3*z/(1-z) := by unfold toHalf; field_simp; ring
  rw [he,norm_div,norm_mul,Complex.norm_ofNat,div_le_iff₀ (by linarith)]
  linarith

theorem chart_inside {z : ℂ} (hz : ‖z‖ ≤ 1/5) (j : ℕ) :
    1 < (toHalf z).re ∧ ‖toHalf z-center j 0‖ ≤ 4*(scale j : ℝ) := by
  have h := chart_distance hz
  have hr := Complex.abs_re_le_norm (toHalf z-2)
  change |(toHalf z).re-2| ≤ ‖toHalf z-2‖ at hr
  have hg : (1:ℝ) ≤ scale j := by
    exact_mod_cast Nat.one_le_pow j 2 (by decide)
  have ec : (2:ℂ)-center j 0 = ((3/2-4*(scale j:ℝ) : ℝ):ℂ) := by
    apply Complex.ext <;> simp [PolynomialIdealSamples.center,Complex.sub_re,Complex.sub_im]; ring
  refine ⟨by linarith [(abs_le.mp (hr.trans h)).1],?_⟩
  calc _ ≤ ‖toHalf z-2‖+‖(2:ℂ)-center j 0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
       _ ≤ _ := by rw [ec,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]; linarith

theorem polarFactor_ne {s : ℂ} (hs : 1<s.re) : polarFactor s ≠ 0 := by
  have hr : 2 < (2:ℝ)^s.re := by
    simpa using Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1:ℝ)<2) hs
  have h : ‖2*frequency 2 s‖ < 1 := by
    rw [frequency_eq_inv_cpow (by decide : 2 ≠ 0),norm_mul,Complex.norm_two,norm_inv]
    have he : ‖(2:ℂ)^s‖=(2:ℝ)^s.re := Complex.norm_cpow_eq_rpow_re_of_pos (x:=2) (by norm_num) s
    rw [show ((2:ℕ):ℂ) = 2 by norm_num,he,← div_eq_mul_inv,div_lt_one (by positivity)]
    exact hr
  unfold polarFactor polarRoot
  apply pow_ne_zero
  intro e
  rw [← sub_eq_zero.mp e,norm_one] at h
  exact (lt_irrefl _ h)

theorem multiplier_bounded (δ N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ 1/5 → ‖multiplier δ N z‖ ≤ C := by
  have hc : ContinuousOn (multiplier δ N) (closedBall 0 (1/5)) := by
    intro z hz
    have hz' : ‖z‖ ≤ 1/5 := by simpa using hz
    have h1 : 1-z ≠ 0 := by intro e; have := sub_eq_zero.mp e; simp [←this] at hz'; norm_num at hz'
    have h2 : 2+z ≠ 0 := by
      intro e
      have hh : z = -2 := by linear_combination e
      norm_num [hh] at hz'
    have hp := polarFactor_ne (chart_inside hz' 0).1
    apply ContinuousAt.continuousWithinAt
    unfold multiplier
    have hc : ContinuousAt toHalf z := by unfold toHalf; fun_prop
    have hpC : ContinuousAt polarFactor (toHalf z) := by unfold polarFactor polarRoot frequency; fun_prop
    exact ((by fun_prop : ContinuousAt (fun w : ℂ ↦ ((1-w)/3)^N * ((1+2*w)/(2+w))^δ) z)).div
      (hpC.comp hc) hp
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:ℂ) (1/5)).exists_bound_of_continuousOn hc
  exact ⟨max 0 C, le_max_left .., fun z hz ↦ (hC _ (by simpa using hz)).trans (le_max_right ..)⟩

theorem ordinaryDisk_analytic (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) (N : ℕ) :
    AnalyticOnNhd ℂ (ordinaryDisk χ L N) (closedBall 0 (1/5)) := by
  let G := fun w : ℂ ↦ polarFactor w*L w
  have hG := poleCleared_entire τ hτ χ hχ L hL he
  intro z hz
  have hz' : ‖z‖≤1/5 := by simpa using hz
  have h1 : 1-z ≠ 0 := by intro e;have := sub_eq_zero.mp e;norm_num [←this] at hz'
  have h2 : 2+z ≠ 0 := by
    intro e
    have hh : z = -2 := by linear_combination e
    norm_num [hh] at hz'
  have hc : AnalyticAt ℂ toHalf z := by unfold toHalf;fun_prop
  have hq : AnalyticAt ℂ polarFactor (toHalf z) := by unfold polarFactor polarRoot frequency;fun_prop
  have hqz := polarFactor_ne (chart_inside hz' 0).1
  have heq : L =ᶠ[𝓝 (toHalf z)] fun s ↦ G s/polarFactor s := by
    filter_upwards [hq.continuousAt.eventually_ne hqz] with s hs
    dsimp only [G]
    field_simp
  have hAL : AnalyticAt ℂ L (toHalf z) := ((hG.analyticAt (toHalf z)).div hq hqz).congr heq.symm
  unfold ordinaryDisk
  exact ((by fun_prop : AnalyticAt ℂ (fun w : ℂ ↦ ((1-w)/3)^N * ((1+2*w)/(2+w))^(principalIndex χ)) z)).mul
    (hAL.comp hc)

theorem eventually_disk_bound (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∀ᶠ m : ℕ in atTop, DiskBound (fun w ↦ polarFactor w*L w)
      (4*Module.finrank ℚ F+1) (meshBlock m) := by
  obtain ⟨B,K,hB,hK,hr,hl⟩ := poleCleared_boundary_bounds τ hτ χ hχ L hL he
  let d := Module.finrank ℚ F
  obtain ⟨A,hA⟩ := exists_nat_ge (K^5*(2*(B+40))^(4*d))
  filter_upwards [eventually_ge_atTop A] with m hm
  exact diskBound_of_boundaries _ (poleCleared_entire τ hτ χ hχ L hL he)
    (fun _ _ hab ↦ poleCleared_polynomial_growth χ L hL he hab) d B K hB hK hr hl
    (meshBlock m) (hA.trans (by exact_mod_cast (show A ≤ scale (meshBlock m) from
      hm.trans (Nat.le_succ m |>.trans (meshBlock_bounds m).1))))

theorem eventually_chartValue_fast_for_factor (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (δ N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ 1/5 →
      ‖chartValue (idealValue χ) δ (Module.finrank ℚ F) N m z -
        weightedChart δ N L z‖ ≤ C*(1/2:ℝ)^(2*m) := by
  classical
  let b := coefficients χ
  let G := fun s : ℂ ↦ polarFactor s*L s
  let D := 4*Module.finrank ℚ F+1
  have hsr (w : ℂ) (hw : 1 < w.re) : G w = LSeries b w := by
    dsimp only [G]
    rw [he ⟨w,hw⟩]
    exact (coefficients_hasSum χ ⟨w,hw⟩).LSeries_eq.symm
  have hb : LSeriesSummable b 2 := (coefficients_hasSum χ ⟨2,by norm_num⟩).LSeriesSummable
  obtain ⟨A,hA,hweight⟩ := multiplier_bounded δ N
  have hmass : 0 ≤ 2+coefficientMass b := by unfold coefficientMass; positivity
  refine ⟨A*(2+coefficientMass b),mul_nonneg hA hmass,?_⟩
  filter_upwards [eventually_disk_bound τ hτ χ hχ L hL he,eventually_ge_atTop 1] with m hg hm
  intro z hz
  let j := meshBlock m
  have hscale := (meshBlock_bounds m).1
  have hs : 2≤scale j := by dsimp [j];omega
  have hi := chart_inside hz j
  have hden := polarFactor_ne hi.1
  have hraw : weightedChart δ N L z = multiplier δ N z * G (toHalf z) := by
    unfold weightedChart multiplier G
    field_simp
  have hv : chartValue (idealValue χ) δ (Module.finrank ℚ F) N m z =
      multiplier δ N z * extrapolate b (degree D j) (length D j) (center j 0)
        (toHalf z-center j 0) := by
    simp only [chartValue,extrapolate,b,coefficients_eq_ideal_values,corrected,idealValue,j,D]
  have herr := norm_sub_extrapolate_on_disk b hb G (poleCleared_entire τ hτ χ hχ L hL he) hsr
    D j hs hg hi.2
  have hx : 2*m ≤ 3*(j+1)*scale j := by
    have hh := Nat.mul_le_mul_right (scale j) (show 2≤3*(j+1) by omega)
    change m+1 ≤ scale j at hscale
    omega
  rw [hraw,hv,← mul_sub,norm_mul,norm_sub_rev]
  calc _ ≤ A*((2+coefficientMass b)/(2:ℝ)^(3*(j+1)*scale j)) :=
         mul_le_mul (hweight z hz) herr (norm_nonneg _) hA
       _ ≤ A*((2+coefficientMass b)/(2:ℝ)^(2*m)) := by
         have hp : (2:ℝ)^(2*m) ≤ (2:ℝ)^(3*(j+1)*scale j) := pow_le_pow_right₀ (by norm_num) hx
         have hp0 : 0 < (2:ℝ)^(2*m) := by positivity
         exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_left hmass hp0 hp) hA
       _ = _ := by rw [one_div,inv_pow,div_eq_mul_inv]; ring

theorem eventually_chartValue_fast (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ 1/5 →
      ‖chartValue (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) N m z -
        ordinaryDisk χ L N z‖ ≤ C*(1/2:ℝ)^(2*m) := by
  exact eventually_chartValue_fast_for_factor τ hτ χ hχ L hL he (principalIndex χ) N

theorem eventually_chartValue_dyadic_for_factor (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (δ N : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ 1/5 →
      ‖chartValue (idealValue χ) δ (Module.finrank ℚ F) N m z -
        weightedChart δ N L z‖ ≤ (1/2:ℝ)^m := by
  obtain ⟨C,hC,h⟩ := eventually_chartValue_fast_for_factor τ hτ χ hχ L hL he δ N
  obtain ⟨B,hB⟩ := exists_nat_ge C
  filter_upwards [h,eventually_ge_atTop B] with m hm hmm
  intro z hz
  have hpow : C ≤ (2:ℝ)^m := hB.trans ((show (B:ℝ) ≤ m by exact_mod_cast hmm).trans
    (by exact_mod_cast (Nat.lt_pow_self (by decide : 1<2) (n:=m)).le))
  calc _ ≤ C*(1/2:ℝ)^(2*m) := hm z hz
       _ ≤ (2:ℝ)^m*(1/2:ℝ)^(2*m) := mul_le_mul_of_nonneg_right hpow (by positivity)
       _ = _ := by rw [two_mul,pow_add,one_div,inv_pow];field_simp

theorem eventually_chartValue_dyadic (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (N : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ 1/5 →
      ‖chartValue (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) N m z -
        ordinaryDisk χ L N z‖ ≤ (1/2:ℝ)^m := by
  exact eventually_chartValue_dyadic_for_factor τ hτ χ hχ L hL he (principalIndex χ) N

/-- Direct ordinary L evaluation on the whole compact chart, including the principal character. -/
theorem eventually_plain_L (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, ‖z‖≤1/5 →
      ‖chartValue (idealValue χ) 0 (Module.finrank ℚ F) 0 m z-L (toHalf z)‖ ≤ (1/2:ℝ)^m := by
  simpa only [weightedChart,pow_zero,mul_one,one_mul] using
    eventually_chartValue_dyadic_for_factor τ hτ χ hχ L hL he 0 0

/-- The finite value formula approximates the ordinary disk function uniformly on the closed chart. -/
theorem eventually_chartValue (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, ‖z‖ ≤ 1/5 →
      ‖chartValue (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) N m z -
        ordinaryDisk χ L N z‖ ≤ C*(1/2:ℝ)^m := by
  refine ⟨1,zero_le_one,?_⟩
  simpa only [one_mul] using eventually_chartValue_dyadic τ hτ χ hχ L hL he N

theorem chartValue_congr {a b : ℕ → ℂ} (δ d N m : ℕ)
    (h : ∀ k < length (4*d+1) (meshBlock m), a k = b k) :
    chartValue a δ d N m = chartValue b δ d N m := by
  funext z
  unfold chartValue
  apply congrArg (fun u : ℂ ↦ multiplier δ N z * u)
  apply Finset.sum_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  have e : corrected a k=corrected b k := by
    unfold corrected
    rw [h k hk',h (k/2) (by omega),h (k/4) (by omega)]
  rw [e]

/-- Number of angular nodes for all coefficients in a row. -/
def nodes (n : ℕ) : ℕ := 12*(n+1)

/-- Input precision for the finite extrapolation. -/
def precision (n : ℕ) : ℕ := 6*(n+1)

/-- The finite complex table, simultaneously measured through degree n. -/
def row (a : ℕ → ℂ) (δ d N n j : ℕ) : ℂ :=
  extract (chartValue a δ d N (precision n)) (nodes n) j

/-- Explicit polynomial upper bound for every norm index used by a row. -/
def cutoff (d n : ℕ) : ℕ := (4*(precision n+2))^(4*d+7)

theorem index_le_cutoff (d n : ℕ) :
    length (4*d+1) (meshBlock (precision n)) ≤ cutoff d n := by
  simpa [cutoff] using length_meshBlock_le (4*d+1) (precision n)

/-- The complete row is unchanged by arbitrary alterations of the ideal data at
or above its explicit polynomial cutoff. -/
theorem row_congr {a b : ℕ → ℂ} (δ d N n : ℕ) (h : ∀ k<cutoff d n, a k=b k) :
    row a δ d N n=row b δ d N n := by
  funext j
  unfold row
  rw [chartValue_congr δ d N (precision n) (fun k hk ↦ h k (hk.trans_le (index_le_cutoff d n)))]

private theorem power_error {n j : ℕ} (hj : j≤n) :
    (8:ℝ)^j*(1/2)^precision n ≤ (1/2)^(3*n+6) := by
  have h8 : (8:ℝ)^j ≤ (2:ℝ)^(3*n) := by
    rw [show (8:ℝ)=(2:ℝ)^3 by norm_num, ←pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hj)
  refine (mul_le_mul_of_nonneg_right h8 (by positivity)).trans_eq ?_
  rw [show precision n=3*n+(3*n+6) by unfold precision;omega,pow_add,one_div,inv_pow,inv_pow]
  field_simp

/-- Exponential pointwise accuracy on the inner circle yields simultaneous dyadic accuracy
through degree n. Arbitrary fixed analytic and pointwise constants affect only the onset. -/
theorem eventually_extract_schedule {f : ℂ → ℂ} {V : ℕ → ℂ → ℂ}
    (ha : AnalyticOnNhd ℂ f (closedBall 0 (1/5)))
    (h : ∃ C : ℝ, 0≤C ∧ ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, ‖z‖=1/8 → ‖V m z-f z‖ ≤ C*(1/2:ℝ)^m) :
    ∀ᶠ n : ℕ in atTop, ∀ j≤n, ‖extract (V (precision n)) (nodes n) j-coeff f j‖ ≤ (1/2:ℝ)^(2*n) := by
  obtain ⟨C,hC,hc⟩ := h
  obtain ⟨A,hA⟩ := eventually_atTop.1 hc
  obtain ⟨B,hB⟩ := (isCompact_closedBall (0:ℂ) (1/5)).exists_bound_of_continuousOn ha.continuousOn
  have hB0 : 0≤B := (norm_nonneg (f 0)).trans (hB _ (by simp))
  obtain ⟨T,hT⟩ := exists_nat_ge (C+3*B)
  filter_upwards [eventually_ge_atTop (max A T)] with n hn
  intro j hj
  have hpn : A ≤ precision n := by unfold precision;omega
  have hq : j<nodes n := by unfold nodes;omega
  have hu := extract_error_of_bound (by norm_num) ha (fun z hz ↦ hB _ (by simpa using hz.le)) hq (hA _ hpn)
  have eq4 : (5/8:ℝ)^nodes n ≤ (1/2:ℝ)^precision n := by
    rw [show nodes n = 2*precision n by unfold nodes precision;omega,pow_mul]
    exact pow_le_pow_left₀ (by positivity) (by norm_num) _
  have hu' : ‖extract (V (precision n)) (nodes n) j-coeff f j‖ ≤
      (8:ℝ)^j*((C+3*B)*(1/2)^precision n) := by
    apply hu.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [show (1/8:ℝ)/(1/5)=5/8 by norm_num]
    have hpow := mul_le_mul_of_nonneg_left eq4 hB0
    have hpos : 0 ≤ B*(1/2:ℝ)^precision n := by positivity
    rw [show 1-(5/8:ℝ)=3/8 by norm_num]
    nlinarith only [hpow,hpos]
  have hb : C+3*B ≤ (2:ℝ)^(n+6) := by
    have hnT : T≤n+6 := by omega
    refine hT.trans ((show (T:ℝ) ≤ (n+6:ℕ) by exact_mod_cast hnT).trans ?_)
    exact_mod_cast (Nat.lt_pow_self (by decide : 1<2) (n:=n+6)).le
  rw [mul_left_comm] at hu'
  calc _ ≤ (C+3*B)*((8:ℝ)^j*(1/2)^precision n) := hu'
       _ ≤ (2:ℝ)^(n+6)*(1/2:ℝ)^(3*n+6) :=
         mul_le_mul hb (power_error hj) (by positivity) (by positivity)
       _ = _ := by
         rw [show 3*n+6=(n+6)+2*n by omega,pow_add,one_div,inv_pow,inv_pow]
         field_simp
         simp only [pow_add]

theorem eventually_row_error (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (N : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ j ≤ n,
      ‖row (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) N n j -
          coeff (ordinaryDisk χ L N) j‖ ≤ (1/2:ℝ)^(2*n) := by
  obtain ⟨C,hC,h⟩ := eventually_chartValue τ hτ χ hχ L hL he N
  apply eventually_extract_schedule (ordinaryDisk_analytic τ hτ χ hχ L hL he N)
  exact ⟨C,hC,h.mono fun m hm z hz ↦ hm z (by linarith)⟩

theorem all_row_error {u : ℕ → ℕ → ℂ} {c : ℕ → ℂ}
    (h : ∀ᶠ n : ℕ in atTop, ∀ j ≤ n, ‖u n j-c j‖ ≤ (1/2:ℝ)^(2*n)) :
    ∃ C : ℝ, 0≤C ∧ ∀ n j, j≤n → ‖u n j-c j‖ ≤ C*(1/2:ℝ)^(2*n) := by
  obtain ⟨A,hA⟩ := eventually_atTop.1 h
  let t := fun n j ↦ ‖u n j-c j‖*(2:ℝ)^(2*n)
  let C := 1+∑ n ∈ Finset.range A, ∑ j ∈ Finset.range (n+1), t n j
  have ht (n j : ℕ) : 0≤t n j := by dsimp [t];positivity
  have hc : 1 ≤ C := by dsimp [C]; exact le_add_of_nonneg_right (Finset.sum_nonneg fun n _ ↦ Finset.sum_nonneg fun j _ ↦ ht n j)
  refine ⟨C,by linarith,fun n j hj ↦ ?_⟩
  by_cases hn : A ≤ n
  · exact (hA n hn j hj).trans ((le_mul_iff_one_le_left (by positivity)).mpr hc)
  · have hE : t n j ≤ C := by
      have h₁ := Finset.single_le_sum (f:=t n) (fun a _ ↦ ht n a) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
      have h₂ := Finset.single_le_sum (f:=fun m ↦ ∑ k ∈ Finset.range (m+1), t m k)
        (fun m _ ↦ Finset.sum_nonneg fun k _ ↦ ht m k) (Finset.mem_range.mpr (lt_of_not_ge hn))
      exact (h₁.trans h₂).trans (by dsimp [C]; linarith)
    rw [one_div,inv_pow,←div_eq_mul_inv,le_div_iff₀ (by positivity)]
    exact hE

/-- The actual ordinary Hecke Taylor coefficients have uniform eventual dyadic enclosures at every exponent. -/
theorem canonical_finite_ideal_coefficients (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    ∀ N : ℕ,
      (∀ᶠ n : ℕ in atTop, ∀ j≤n, ‖row (idealValue χ) (principalIndex χ)
        (Module.finrank ℚ F) N n j - coeff (ordinaryDisk χ L N) j‖ ≤ (1/2:ℝ)^(2*n)) ∧
      ∃ C : ℝ, 0≤C ∧ ∀ n j, j≤n → ‖row (idealValue χ) (principalIndex χ)
        (Module.finrank ℚ F) N n j - coeff (ordinaryDisk χ L N) j‖ ≤ C*(1/2:ℝ)^(2*n) := by
  intro L N
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hh := eventually_row_error τ hτ χ hχ L hL he N
  exact ⟨hh,all_row_error hh⟩

theorem eventually_ideal_count (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ n : ℕ in atTop,
      (Nat.card {I : Ideal (𝓞 F) // (I.absNorm:ℝ) ≤ (cutoff (Module.finrank ℚ F) n : ℝ)} : ℝ) ≤
        C*(cutoff (Module.finrank ℚ F) n : ℝ) := by
  let d := Module.finrank ℚ F
  have hcut (n : ℕ) : n+1 ≤ cutoff d n := by
    have h₁ : n+1 ≤ 4*(precision n+2) := by unfold precision;omega
    refine h₁.trans ?_
    have h₂ := Nat.pow_le_pow_right (show 0<4*(precision n+2) by omega) (show 1≤4*d+7 by omega)
    simpa [cutoff] using h₂
  have ht : Tendsto (fun n : ℕ ↦ (cutoff d n:ℝ)) atTop atTop := by
    apply tendsto_natCast_atTop_atTop.comp
    apply Filter.tendsto_atTop.2
    exact fun n ↦ (eventually_ge_atTop n).mono fun m hm ↦ hm.trans ((Nat.le_succ m).trans (hcut m))
  have H := (Ideal.tendsto_norm_le_div_atTop F).comp ht
  have hi := H.eventually_lt_const (show NumberField.dedekindZeta_residue F < NumberField.dedekindZeta_residue F+1 by linarith)
  refine ⟨NumberField.dedekindZeta_residue F+1,by linarith [NumberField.dedekindZeta_residue_pos F],?_⟩
  filter_upwards [hi] with n hn
  have hpos : 0<(cutoff d n:ℝ) := by exact_mod_cast (show 0<cutoff d n by have := hcut n;omega)
  exact ((div_lt_iff₀ hpos).mp hn).le

/-- The finite type of nonzero integral ideals contributing at a norm index. -/
def normFibre (F : Type*) [Field F] [NumberField F] (m : ℕ) :=
  {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ (I.absNorm : ℝ) = m}

@[instance_reducible] def normFibreFintype (F : Type*) [Field F] [NumberField F] (m : ℕ) : Fintype (normFibre F m) := by
  classical
  let S := {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ (I.absNorm : ℝ) = m}
  have hs : S.Finite := (Ring.HasFiniteQuotients.finite_absNorm_eq (S:=𝓞 F) m).subset
    (fun I h ↦ by change I.absNorm=m;exact_mod_cast h.2)
  exact hs.fintype

theorem idealValue_finite_sum (χ : U𝔽) (m : ℕ) :
    idealValue χ m = (@Finset.univ _ (normFibreFintype F m)).sum
      (fun I ↦ heckeIdealValue (ideleClassNormTwist χ 0) I.val) := by
  let : Fintype (normFibre F m) := normFibreFintype F m
  change (∑ᶠ I : normFibre F m, heckeIdealValue (ideleClassNormTwist χ 0) I.val) = _
  exact finsum_eq_sum_of_fintype _

/-- A field-dependent constant bounds the number of distinct integral ideals in every row. -/
theorem ideal_count (F : Type*) [Field F] [NumberField F] :
    ∃ C : ℝ, 0<C ∧ ∀ n : ℕ,
      (Nat.card {I : Ideal (𝓞 F) // (I.absNorm:ℝ) ≤ (cutoff (Module.finrank ℚ F) n : ℝ)} : ℝ) ≤
        C*(cutoff (Module.finrank ℚ F) n : ℝ) := by
  let d := Module.finrank ℚ F
  let a := fun n : ℕ ↦ (Nat.card {I : Ideal (𝓞 F) // (I.absNorm:ℝ) ≤ (cutoff d n : ℝ)} : ℝ)
  obtain ⟨C,hC,hh⟩ := eventually_ideal_count F
  obtain ⟨A,hA⟩ := eventually_atTop.1 hh
  let M := C+∑ n ∈ Finset.range A, a n
  have ha (n : ℕ) : 0≤a n := Nat.cast_nonneg _
  have hM : C≤M := le_add_of_nonneg_right (Finset.sum_nonneg fun n _ ↦ ha n)
  refine ⟨M,hC.trans_le hM,fun n ↦ ?_⟩
  by_cases hn : A≤n
  · exact (hA n hn).trans (mul_le_mul_of_nonneg_right hM (by positivity))
  · have hx : a n ≤ M := (Finset.single_le_sum (f:=a) (fun k _ ↦ ha k)
        (Finset.mem_range.mpr (lt_of_not_ge hn))).trans (by dsimp [M];linarith)
    have hcut : (1:ℝ) ≤ cutoff d n := by
      exact_mod_cast (show 0<cutoff d n by unfold cutoff;positivity)
    exact hx.trans (le_mul_of_one_le_right (hC.trans_le hM).le hcut)

theorem chart_re_three_halves {z : ℂ} (hz : ‖z‖≤1/5) : 3/2≤(toHalf z).re := by
  have h₁ : 1-z ≠ 0 := by intro e;have := sub_eq_zero.mp e;norm_num [←this] at hz
  have hnorm : 0<Complex.normSq (1-z) := Complex.normSq_pos.mpr h₁
  have hre := (abs_le.mp (Complex.abs_re_le_norm z |>.trans hz)).1
  have hsq : z.re*z.re+z.im*z.im ≤ (1/5:ℝ)^2 := by
    have h := pow_le_pow_left₀ (norm_nonneg z) hz 2
    simpa only [Complex.sq_norm,Complex.normSq_apply] using h
  unfold toHalf
  rw [Complex.div_re,←add_div,le_div_iff₀ hnorm]
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.one_re,Complex.one_im,
    Complex.add_re,Complex.add_im,Complex.re_ofNat,Complex.im_ofNat]
  nlinarith only [hre,hsq]

/-- The principal filter in disk coordinates is the ordinary pole-clearing factor in s. -/
theorem ordinaryDisk_eq_half (χ : U𝔽) (L : ℂ → ℂ) (N : ℕ) {z : ℂ} (hz : ‖z‖≤1/5) :
    ordinaryDisk χ L N z = ((1-z)/3)^N * ((toHalf z-1)/toHalf z)^(principalIndex χ) * L (toHalf z) := by
  have h1 : 1-z ≠ 0 := by intro e;have := sub_eq_zero.mp e;norm_num [←this] at hz
  have h2 : 2+z ≠ 0 := by
    intro e
    have hh : z = -2 := by linear_combination e
    norm_num [hh] at hz
  have hf : (1+2*z)/(2+z)=(toHalf z-1)/toHalf z := by unfold toHalf;field_simp;ring
  simp only [ordinaryDisk,hf]

/-- The finite row of the logarithmic derivative uses two evaluations per angular node. -/
def logRow (a : ℕ → ℂ) (δ d n j : ℕ) : ℂ :=
  extract (ratioDifference (chartValue a δ d 0 (2*(precision n+6))) (step (precision n))) (nodes n) j

theorem logRow_congr {a b : ℕ → ℂ} (δ d n : ℕ) (h : ∀ k<cutoff d (2*n+3), a k=b k) :
    logRow a δ d n=logRow b δ d n := by
  funext j
  unfold logRow
  rw [show 2*(precision n+6)=precision (2*n+3) by unfold precision;omega]
  rw [chartValue_congr δ d 0 (precision (2*n+3)) (fun k hk ↦ h k (hk.trans_le (index_le_cutoff d (2*n+3))))]

theorem ordinaryDisk_nonzero (χ : U𝔽) (L : ℂ → ℂ) (he : ∀ s : Hp, L s=finiteHeckeL χ s)
    (z : ℂ) (hz : ‖z‖≤1/5) : ordinaryDisk χ L 0 z ≠ 0 := by
  have h1 : 1+2*z ≠ 0 := by
    intro e
    have hh : z = -(1/2) := by linear_combination (1/2:ℂ)*e
    norm_num [hh] at hz
  have h2 : 2+z ≠ 0 := by
    intro e
    have hh : z = -2 := by linear_combination e
    norm_num [hh] at hz
  let s : Hp := ⟨toHalf z,(chart_inside hz 0).1⟩
  have hL : L (toHalf z) ≠ 0 := (he s).trans_ne (finiteHeckeL_ne_zero_of_one_lt_re χ s)
  simpa only [ordinaryDisk,pow_zero,one_mul] using
    (mul_ne_zero (pow_ne_zero (principalIndex χ) (div_ne_zero h1 h2)) hL)

theorem eventually_logRow_error (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s=finiteHeckeL χ s) :
    ∀ᶠ n : ℕ in atTop, ∀ j≤n, ‖logRow (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) n j-
      coeff (logDeriv (ordinaryDisk χ L 0)) j‖ ≤ (1/2:ℝ)^(2*n) := by
  have ha := ordinaryDisk_analytic τ hτ χ hχ L hL he 0
  have hn := ordinaryDisk_nonzero χ L he
  let g := ordinaryDisk χ L 0
  let V := chartValue (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) 0
  have hadd : AnalyticOnNhd ℂ (logDeriv g) (closedBall 0 (1/5)) := by
    intro z hz
    exact (ha z hz).deriv.div (ha z hz) (hn _ (by simpa using hz))
  have hd := eventually_ratioDifference (g:=g) (V:=V) ha hn (eventually_chartValue τ hτ χ hχ L hL he 0)
  exact eventually_extract_schedule (f:=logDeriv g)
    (V:=fun m ↦ ratioDifference (V (2*(m+6))) (step m)) hadd hd

/-- Its derivatives give those of any local logarithm; the quotient fixes the center value at zero. -/
def centeredLog (g : ℂ → ℂ) (z : ℂ) : ℂ := Complex.log (g z/g 0)

theorem coeff_logDeriv {g : ℂ → ℂ} (ha : AnalyticAt ℂ g 0) (hn : g 0≠0) (j : ℕ) :
    coeff (logDeriv g) j=((j+1:ℕ):ℂ)*coeff (centeredLog g) (j+1) := by
  have hc : ContinuousAt (fun z : ℂ ↦ g z/g 0) 0 := ha.continuousAt.div_const _
  have hp : g 0/g 0 ∈ Complex.slitPlane := by simp [hn]
  have hs := hc (Complex.isOpen_slitPlane.mem_nhds hp)
  have he : logDeriv g =ᶠ[𝓝 (0:ℂ)] deriv (centeredLog g) := by
    filter_upwards [hs,ha.eventually_analyticAt] with z hz hd
    have hnz : g z ≠ 0 := by
      intro e
      apply Complex.slitPlane_ne_zero hz
      simp [e]
    have hlog := (Complex.hasDerivAt_log hz).comp z (hd.differentiableAt.hasDerivAt.div_const (g 0))
    rw [logDeriv_apply, show deriv (centeredLog g) z = (g z/g 0)⁻¹*(deriv g z/g 0) from hlog.deriv]
    field_simp
  have hj : ((j+1:ℕ):ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
  rw [coeff,coeff,he.iteratedDeriv_eq j,Nat.factorial_succ,Nat.cast_mul,iteratedDeriv_succ']
  field_simp

/-- Finite ideal data give simultaneous enclosures of the logarithmic derivative and the real logarithmic coefficients. -/
theorem canonical_logarithmic_coefficients (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t) = 1) :
    let g := ordinaryDisk χ (finiteHeckeL_exists_continuation χ).choose 0
    (∀ᶠ n : ℕ in atTop, ∀ j≤n, ‖logRow (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) n j-
      coeff (logDeriv g) j‖ ≤ (1/2:ℝ)^(2*n)) ∧
    ∀ᶠ n : ℕ in atTop, ∀ j≤n, |(logRow (idealValue χ) (principalIndex χ) (Module.finrank ℚ F) n j).re-
      (j+1:ℝ)*(coeff (centeredLog g) (j+1)).re| ≤ (1/2:ℝ)^(2*n) := by
  intro g
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hh := eventually_logRow_error τ hτ χ hχ L hL he
  refine ⟨hh,?_⟩
  have hg : AnalyticAt ℂ g 0 := ordinaryDisk_analytic τ hτ χ hχ L hL he 0 0 (by simp)
  have hn : g 0≠0 := ordinaryDisk_nonzero χ L he _ (by norm_num)
  filter_upwards [hh] with n h
  intro j hj
  have hout := (Complex.abs_re_le_norm _).trans (h j hj)
  change |(_-coeff (logDeriv g) j).re| ≤ _ at hout
  rw [coeff_logDeriv hg hn j] at hout
  simpa [Complex.sub_re,Complex.mul_re] using hout

end RiemannMasullo.FiniteHardyIdealTable
