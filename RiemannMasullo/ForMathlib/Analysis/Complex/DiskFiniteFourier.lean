module

public import RiemannMasullo.ForMathlib.Analysis.Complex.FiniteTaylorControl
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# Recovering Taylor and logarithmic-derivative coefficients from finite samples

The discrete Fourier transform on a radius-one-eighth circle extracts polynomial coefficients
exactly through degree Q−1. A Cauchy remainder controls the error for analytic functions.
For a nonvanishing function, quadratic accuracy in a forward step yields linear accuracy in
its logarithmic derivative from just two translated measurements.
-/

@[expose] public noncomputable section

open Complex Filter Function Metric Finset Set
open scoped Topology

namespace RiemannMasullo.DiskFiniteFourier

open FiniteTaylor

/-- The Taylor coefficient at the origin, normalized by the factorial. -/
def coeff (f : ℂ → ℂ) (j : ℕ) : ℂ := (j.factorial : ℂ)⁻¹ * iteratedDeriv j f 0

def root (Q : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / Q)

def node (Q h : ℕ) : ℂ := (1/8 : ℂ) * (root Q)^h

/-- Finite Fourier extraction at index j from the first Q powers of an explicit primitive root. -/
def extract (v : ℂ → ℂ) (Q j : ℕ) : ℂ :=
  ((8:ℂ)^j/(Q:ℂ)) * ∑ h ∈ range Q, v (node Q h) * (((root Q)^j)⁻¹)^h

theorem norm_root {Q : ℕ} (hq : 0<Q) : ‖root Q‖=1 :=
  Complex.norm_eq_one_of_pow_eq_one (Complex.isPrimitiveRoot_exp Q hq.ne').pow_eq_one hq.ne'

theorem norm_node {Q : ℕ} (hq : 0<Q) (h : ℕ) : ‖node Q h‖ = 1/8 := by
  simp [node,norm_pow,norm_root hq]

theorem orthogonality {Q j k : ℕ} (hk : k<Q) (hj : j<Q) :
    ∑ h ∈ range Q, ((root Q)^k*((root Q)^j)⁻¹)^h = if k=j then (Q:ℂ) else 0 := by
  have hq : 0<Q := by omega
  have hp : IsPrimitiveRoot (root Q) Q := Complex.isPrimitiveRoot_exp Q hq.ne'
  have hn : root Q ≠ 0 := (norm_pos_iff.mp (by rw [norm_root hq]; norm_num))
  by_cases e : k=j
  · subst k
    simp [pow_ne_zero _ hn]
  · simp only [ite_eq_right e]
    let x := (root Q)^k*((root Q)^j)⁻¹
    have hx : x ≠ 1 := by
      dsimp [x]
      rw [← div_eq_mul_inv, div_eq_one_iff_eq (pow_ne_zero _ hn)]
      exact fun h ↦ e (hp.pow_inj hk hj h)
    have hxQ : x^Q = 1 := by
      rw [show x^Q = ((root Q)^Q)^k * (((root Q)^Q)^j)⁻¹ by
        dsimp [x]; simp only [mul_pow,inv_pow,←pow_mul,Nat.mul_comm Q]]
      simp [hp.pow_eq_one]
    change ∑ h ∈ range Q, x^h=0
    rw [geom_sum_eq hx,hxQ,sub_self,zero_div]

theorem extract_polynomial (a : ℕ → ℂ) {Q j : ℕ} (hj : j<Q) :
    extract (fun z ↦ ∑ k ∈ range Q, a k*z^k) Q j = a j := by
  have hq : 0<Q := by omega
  have hm (k h : ℕ) : a k*(node Q h)^k * (((root Q)^j)⁻¹)^h =
       a k*(1/8:ℂ)^k * ((root Q)^k*((root Q)^j)⁻¹)^h := by
    have he : ((root Q)^h)^k=((root Q)^k)^h := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
    unfold node
    rw [mul_pow,mul_pow,he]
    ring
  unfold extract
  simp_rw [Finset.sum_mul, hm]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  have hs : ∑ k ∈ range Q, a k*(1/8:ℂ)^k * ∑ h ∈ range Q, ((root Q)^k*((root Q)^j)⁻¹)^h =
      a j*(1/8:ℂ)^j*(Q:ℂ) := by
    rw [Finset.sum_eq_single j]
    · rw [orthogonality hj hj,ite_eq_left rfl]
    · intro k hk hkj
      rw [orthogonality (mem_range.mp hk) hj,ite_eq_right hkj,mul_zero]
    · simp [mem_range.mpr hj]
  rw [hs]
  have hqn : (Q:ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [one_div,inv_pow]
  field_simp

theorem extract_stable {u v : ℂ → ℂ} {Q j : ℕ} (hQ : 0<Q) {E : ℝ}
    (h : ∀ h ∈ range Q, ‖u (node Q h)-v (node Q h)‖ ≤ E) :
    ‖extract u Q j-extract v Q j‖ ≤ (8:ℝ)^j*E := by
  have hw (p : ℕ) : ‖(((root Q)^j)⁻¹)^p‖=1 := by
    simp [norm_pow,norm_inv,norm_root hQ]
  have hs : ‖∑ p ∈ range Q, (u (node Q p)-v (node Q p))*(((root Q)^j)⁻¹)^p‖ ≤ (Q:ℝ)*E := by
    calc _ ≤ ∑ p ∈ range Q, ‖(u (node Q p)-v (node Q p))*(((root Q)^j)⁻¹)^p‖ := norm_sum_le _ _
         _ ≤ ∑ _p ∈ range Q, E := Finset.sum_le_sum fun p hp ↦ by rw [norm_mul,hw,mul_one];exact h p hp
         _ = _ := by simp
  unfold extract
  rw [←mul_sub,←Finset.sum_sub_distrib]
  simp_rw [←sub_mul]
  rw [norm_mul,norm_div,norm_pow,Complex.norm_ofNat,Complex.norm_natCast]
  calc _ ≤ ((8:ℝ)^j/Q)*((Q:ℝ)*E) := mul_le_mul_of_nonneg_left hs (by positivity)
       _ = _ := by field_simp

/-- A quantitative Cauchy remainder controls the contamination from degrees at least Q. -/
theorem extract_error_of_bound {f v : ℂ → ℂ} {R B : ℝ} (hR : 1/8<R)
    (ha : AnalyticOnNhd ℂ f (closedBall 0 R)) (hb : ∀ z, ‖z‖=R → ‖f z‖ ≤ B)
    {Q j : ℕ} (hj : j<Q) {E : ℝ} (hv : ∀ z, ‖z‖=1/8 → ‖v z-f z‖ ≤ E) :
    ‖extract v Q j-coeff f j‖ ≤ (8:ℝ)^j*(E+B*((1/8)/R)^Q/(1-(1/8)/R)) := by
  let p := fun z : ℂ ↦ ∑ k ∈ range Q, coeff f k*z^k
  have hp (z : ℂ) : p z = taylorSum f 0 z Q := by
    unfold p taylorSum
    exact Finset.sum_congr rfl fun k _ ↦ by simp [coeff,term];ring
  rw [←extract_polynomial (coeff f) hj]
  apply extract_stable (by omega)
  intro t ht
  let z := node Q t
  have hz : ‖z‖=1/8 := norm_node (by omega) _
  have hsub := norm_sub_partial_le (c:=0) (z:=z) (by linarith : 0<R) ha
    (fun w hw ↦ hb _ (by simpa using hw)) (by rw [sub_zero,hz];exact hR) Q
  rw [sub_zero,hz] at hsub
  change ‖v z-p z‖ ≤ _
  rw [hp]
  exact (norm_sub_le_norm_sub_add_norm_sub (v z) (f z) _).trans (add_le_add (hv _ hz) hsub)

theorem extract_error {f v : ℂ → ℂ} (ha : AnalyticOnNhd ℂ f (closedBall 0 (1/2)))
    (hb : ∀ z, ‖z‖ = 1/2 → ‖f z‖ ≤ 1) {Q j : ℕ} (hj : j<Q) {E : ℝ}
    (hv : ∀ z, ‖z‖=1/8 → ‖v z-f z‖ ≤ E) :
    ‖extract v Q j-coeff f j‖ ≤ (8:ℝ)^j*(E+2*(1/4:ℝ)^Q) := by
  refine (extract_error_of_bound (by norm_num) ha hb hj hv).trans ?_
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add le_rfl
  norm_num
  nlinarith [show 0 ≤ (1/4:ℝ)^Q by positivity]

/-- The elementary translated two-point quotient. -/
def ratioDifference (v : ℂ → ℂ) (e : ℝ) (z : ℂ) : ℂ :=
  (v (z+(e:ℂ))-v z)/((e:ℂ)*v z)

/-- Positive forward steps, strictly inside the disk at every sample point. -/
def step (m : ℕ) : ℝ := (1/2:ℝ)^(m+6)

theorem step_pos (m : ℕ) : 0<step m := by unfold step;positivity

theorem step_le (m : ℕ) : step m ≤ 1/64 := by
  have h : (1/2:ℝ)^(m+6) ≤ (1/2:ℝ)^6 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  norm_num at h
  exact h

theorem tendsto_step : Tendsto step atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : 0 ≤ (1/2:ℝ)) (by norm_num)).mul_const ((1/2:ℝ)^6)
  change Tendsto (fun m : ℕ ↦ (1/2:ℝ)^(m+6)) atTop (𝓝 0)
  simpa only [pow_add,zero_mul] using h

theorem norm_forward_remainder {g : ℂ → ℂ} {B e : ℝ}
    (ha : AnalyticOnNhd ℂ g (closedBall 0 (1/5)))
    (hB : ∀ z : ℂ, ‖z‖ ≤ 1/5 → ‖g z‖ ≤ B) (he : 0<e) (he' : e≤1/64)
    {z : ℂ} (hz : ‖z‖≤1/8) :
    ‖g (z+(e:ℂ))-g z-(e:ℂ)*deriv g z‖ ≤ (2048*B)*e^2 := by
  have hin (w : ℂ) (hw : w∈closedBall z (1/32)) : ‖w‖ ≤ 1/5 := by
    have hd := mem_closedBall_iff_norm.mp hw
    have hl : ‖w‖ ≤ ‖w-z‖+‖z‖ := by simpa only [sub_add_cancel] using norm_add_le (w-z) z
    linarith
  have hd : ‖z+(e:ℂ)-z‖=e := by simp [Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
  have hh := norm_sub_partial_le (c:=z) (z:=z+(e:ℂ)) (by norm_num : (0:ℝ)<1/32)
    (fun w hw ↦ ha w (by simpa using hin w hw))
    (fun w hw ↦ hB w (hin w (sphere_subset_closedBall hw)))
    (by rw [hd];linarith) 2
  have hp : taylorSum g z (z+(e:ℂ)) 2=g z+(e:ℂ)*deriv g z := by
    simp [taylorSum,Finset.sum_range_succ,term]
  rw [hp,hd] at hh
  have hb0 : 0≤B := (norm_nonneg (g 0)).trans (hB _ (by norm_num))
  have hratio : 0<1-e/(1/32) := by linarith
  have hmul : 0 ≤ (2048*B*e^2) * (1/2-32*e) := by
    exact mul_nonneg (by positivity) (by linarith)
  calc _ = ‖g (z+(e:ℂ))-(g z+(e:ℂ)*deriv g z)‖ := by congr 1;ring
       _ ≤ _ := hh
       _ ≤ _ := by rw [div_le_iff₀ hratio];nlinarith only [hmul]

/-- Conditioning of the two-point logarithmic difference. The lower bound applies to
the exact input. The absolute error sizes of both samples are quadratic in the step. -/
theorem ratioDifference_error {v g : ℂ → ℂ} {z : ℂ} {e C T J μ : ℝ}
    (he : 0<e) (he1 : e≤1) (hC : 0≤C) (hJ : 0≤J) (hμ : 0<μ)
    (hl : μ ≤ ‖g z‖) (hj : ‖logDeriv g z‖ ≤ J) (hs : C*e^2 ≤ μ/2)
    (hv : ‖v z-g z‖ ≤ C*e^2) (hw : ‖v (z+e)-g (z+e)‖ ≤ C*e^2)
    (ht : ‖g (z+e)-g z-e*deriv g z‖ ≤ T*e^2) :
    ‖ratioDifference v e z-logDeriv g z‖ ≤ ((2*C+T+C*J)/(μ/2))*e := by
  have hv0 : μ/2 ≤ ‖v z‖ := by
    have h := norm_sub_norm_le (g z) (v z)
    rw [norm_sub_rev] at h
    linarith
  have hvne : v z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hgne : g z ≠ 0 := norm_pos_iff.mp (by linarith)
  have hce : (e:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr he.ne'
  have hder : deriv g z=g z*logDeriv g z := by change deriv g z = g z*(deriv g z/g z);field_simp
  have hx : ‖(e:ℂ)*(g z-v z)*logDeriv g z‖ ≤ C*J*e^2 := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he,norm_sub_rev]
    calc _ ≤ e*(C*e^2)*J := mul_le_mul (mul_le_mul_of_nonneg_left hv he.le) hj (norm_nonneg _) (by positivity)
         _ ≤ _ := by nlinarith only [mul_nonneg (show 0≤C*J*e^2 by positivity) (sub_nonneg.mpr he1)]
  let w := z+(e:ℂ)
  have id₁ : v w-v z-(e:ℂ)*v z*logDeriv g z =
      (v w-g w) + (g w-g z-(e:ℂ)*deriv g z) + (g z-v z) + (e:ℂ)*(g z-v z)*logDeriv g z := by
    rw [hder];ring
  have hnum : ‖v w-v z-(e:ℂ)*v z*logDeriv g z‖ ≤ (2*C+T+C*J)*e^2 := by
    rw [id₁]
    refine (norm_add_le _ _).trans ?_
    have h₁ := (norm_add_le (v w-g w) (g w-g z-(e:ℂ)*deriv g z)).trans (add_le_add hw ht)
    have h₂ := (norm_add_le ((v w-g w)+(g w-g z-(e:ℂ)*deriv g z)) (g z-v z)).trans
      (add_le_add h₁ ((norm_sub_rev (g z) (v z)).trans_le hv))
    exact (add_le_add h₂ hx).trans_eq (by ring)
  have id₂ : ratioDifference v e z-logDeriv g z =
      (v w-v z-(e:ℂ)*v z*logDeriv g z)/((e:ℂ)*v z) := by
    unfold ratioDifference
    dsimp only [w]
    field_simp
  rw [id₂,norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
  have hm : 0<μ/2 := by linarith
  calc _ ≤ ((2*C+T+C*J)*e^2)/(e*(μ/2)) :=
         (div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos he hm)
           (mul_le_mul_of_nonneg_left hv0 he.le)).trans (div_le_div_of_nonneg_right hnum (by positivity))
       _ = _ := by field_simp

/-- Uniform exponential errors in values give exponential accuracy for the logarithmic derivative. -/
theorem eventually_ratioDifference {g : ℂ → ℂ} {V : ℕ → ℂ → ℂ}
    (ha : AnalyticOnNhd ℂ g (closedBall 0 (1/5))) (hn : ∀ z, ‖z‖≤1/5 → g z ≠ 0)
    (hV : ∃ C : ℝ, 0≤C ∧ ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, ‖z‖≤1/5 → ‖V m z-g z‖ ≤ C*(1/2:ℝ)^m) :
    ∃ D : ℝ, 0≤D ∧ ∀ᶠ m : ℕ in atTop, ∀ z : ℂ, ‖z‖=1/8 →
      ‖ratioDifference (V (2*(m+6))) (step m) z-logDeriv g z‖ ≤ D*(1/2:ℝ)^m := by
  let S := closedBall (0:ℂ) (1/5)
  have hs : IsCompact S := isCompact_closedBall _ _
  have hzS : (0:ℂ) ∈ S := by simp [S]
  have had : AnalyticOnNhd ℂ (logDeriv g) S := fun z hz ↦ (ha z hz).deriv.div (ha z hz) (hn z (by simpa [S] using hz))
  obtain ⟨B,hB⟩ := hs.exists_bound_of_continuousOn ha.continuousOn
  obtain ⟨J,hJ⟩ := hs.exists_bound_of_continuousOn had.continuousOn
  obtain ⟨v,hv,hμ⟩ := hs.exists_isMinOn ⟨0,hzS⟩ ha.continuousOn.norm
  let μ := ‖g v‖
  have hμ0 : 0<μ := norm_pos_iff.mpr (hn v (by simpa [S] using hv))
  have hJ0 : 0≤J := (norm_nonneg _).trans (hJ 0 hzS)
  have hB0 : 0≤B := (norm_nonneg _).trans (hB 0 hzS)
  obtain ⟨C,hC,h⟩ := hV
  obtain ⟨A,hA⟩ := eventually_atTop.1 h
  let D := (2*C+2048*B+C*J)/(μ/2)
  have hD : 0≤D := by dsimp [D];positivity
  have hlim : Tendsto (fun m ↦ C*(step m)^2) atTop (𝓝 0) := by simpa using (tendsto_step.pow 2).const_mul C
  refine ⟨D,hD,?_⟩
  filter_upwards [eventually_ge_atTop A,hlim.eventually_lt_const (show 0<μ/2 by linarith)] with m hm hc
  intro z hz
  have hpow : (1/2:ℝ)^(2*(m+6))=(step m)^2 := by rw [Nat.mul_comm,pow_mul];rfl
  have hav (w : ℂ) (hw : ‖w‖≤1/5) : ‖V (2*(m+6)) w-g w‖ ≤ C*(step m)^2 := by
    rw [←hpow];exact hA _ (by omega) w hw
  have he := step_pos m
  have he' := step_le m
  have hzne : z∈S := by simp only [S,mem_closedBall_iff_norm,sub_zero];linarith
  have hs' : ‖z+(step m:ℂ)‖≤1/5 := by
    have hh := norm_add_le z (step m:ℂ)
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos he,hz] at hh
    linarith
  have H := ratioDifference_error he (by linarith) hC hJ0 hμ0
    (hμ hzne) (hJ z hzne) hc.le (hav z (by linarith)) (hav _ hs')
    (norm_forward_remainder ha (fun y hy ↦ hB y (by simpa [S] using hy)) he he' hz.le)
  exact H.trans (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one (by norm_num) (by norm_num) (show m≤m+6 by omega)) hD)

end RiemannMasullo.DiskFiniteFourier
