module

public import RiemannMasullo.ForMathlib.Analysis.Complex.BoundaryFourierHardy
public import RiemannMasullo.ForMathlib.Analysis.Complex.LogDerivativeCoefficients
import Mathlib.Analysis.Meromorphic.Divisor
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic

/-! # Radial logarithms, holomorphic logarithms and boundary Fourier coefficients -/

@[expose] public noncomputable section
open MeasureTheory AddCircle Complex Filter Metric Set Function
open scoped ComplexConjugate Topology
namespace RiemannMasullo.BoundaryHardy
open DiskLogCoefficient

/-- Scheffé's lemma for nonnegative real integrable functions. -/
theorem tendsto_integral_abs_sub_of_nonneg {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {v : ℕ → Ω → ℝ} {u : Ω → ℝ} (hv : ∀ n, Integrable (v n) μ) (hu : Integrable u μ)
    (hv0 : ∀ n, 0 ≤ᵐ[μ] v n) (hu0 : 0 ≤ᵐ[μ] u)
    (hpt : ∀ᵐ x ∂μ, Tendsto (fun n ↦ v n x) atTop (𝓝 (u x)))
    (hmean : Tendsto (fun n ↦ ∫ x, v n x ∂μ) atTop (𝓝 (∫ x, u x ∂μ))) :
    Tendsto (fun n ↦ ∫ x, |v n x - u x| ∂μ) atTop (𝓝 0) := by
  let m (n : ℕ) (x : Ω) := min (v n x) (u x)
  have hm (n) : AEStronglyMeasurable (m n) μ :=
    ((hv n).aemeasurable.min hu.aemeasurable).aestronglyMeasurable
  have hdom (n) : ∀ᵐ x ∂μ, ‖m n x‖ ≤ u x := by
    filter_upwards [hv0 n, hu0] with x hx hx'
    simp only [m, Real.norm_eq_abs, abs_of_nonneg (le_min hx hx'), min_le_right]
  have hmI (n) := hu.mono' (hm n) (hdom n)
  have hmin := tendsto_integral_of_dominated_convergence (μ := μ) (F := m) (f := u) u hm hu hdom
    (by filter_upwards [hpt] with x hx; simpa [m] using hx.min (tendsto_const_nhds (x := u x)))
  have eq (n) : (∫ x, |v n x-u x| ∂μ) =
      (∫ x, v n x ∂μ) + (∫ x, u x ∂μ) - 2*(∫ x, m n x ∂μ) := by
    rw [← integral_add (hv n) hu, ← integral_const_mul]
    rw [← integral_sub (f:=fun x ↦ v n x+u x) (g:=fun x ↦ 2*m n x) ((hv n).add hu) ((hmI n).const_mul 2)]
    apply integral_congr_ae
    exact ae_of_all _ fun x ↦ by dsimp [m]; rcases le_total (v n x) (u x) with h|h <;> simp [h] <;> grind
  have hl := (hmean.add_const (∫ x, u x ∂μ)).sub (hmin.const_mul 2)
  simpa only [← eq, show (∫ x, u x ∂μ) + (∫ x, u x ∂μ) - 2*(∫ x, u x ∂μ) = 0 by ring] using hl

/-- A holomorphic logarithm on the unit disk. Its derivative is the ordinary logarithmic derivative. -/
theorem exists_analytic_log {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hn : ∀ z ∈ ball (0:ℂ) 1, f z ≠ 0) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (ball 0 1) ∧
      (∀ z ∈ ball (0:ℂ) 1, exp (g z) = f z) ∧ (ball (0:ℂ) 1).EqOn (deriv g) (logDeriv f) := by
  have h0 : (0:ℂ) ∈ ball 0 1 := by simp
  have hd : DifferentiableOn ℂ (logDeriv f) (ball 0 1) :=
    fun z hz ↦ (((hf z hz).deriv.div (hf z hz) (hn z hz)).differentiableAt).differentiableWithinAt
  obtain ⟨g, hg0, hgd⟩ := hd.isExactOn_ball.with_val_at 0 (log (f 0))
  have hg : DifferentiableOn ℂ g (ball 0 1) := fun z hz ↦ (hgd z hz).differentiableAt.differentiableWithinAt
  let p (z : ℂ) := f z * exp (-g z)
  have hdp (z : ℂ) (hz : z ∈ ball (0:ℂ) 1) : HasDerivAt p 0 z := by
    have h := ((hf z hz).differentiableAt.hasDerivAt).mul (hgd z hz).neg.cexp
    convert h using 1
    simp only [logDeriv_apply]
    field_simp [hn z hz]
    ring
  have hep : (ball (0:ℂ) 1).EqOn p (fun _ ↦ 1) :=
    isOpen_ball.eqOn_of_deriv_eq (convex_ball (0:ℂ) 1).isPreconnected
      (fun z hz ↦ (hdp z hz).differentiableAt.differentiableWithinAt) (differentiableOn_const _)
      (fun z hz ↦ by rw [(hdp z hz).deriv, deriv_const]) h0
      (by simp [p, hg0, Complex.exp_neg, Complex.exp_log (hn 0 h0), hn 0 h0])
  refine ⟨g, hg.analyticOnNhd isOpen_ball, fun z hz ↦ ?_, fun z hz ↦ (hgd z hz).deriv⟩
  have h := hep hz
  change f z * exp (-g z) = 1 at h
  rw [Complex.exp_neg, ← div_eq_mul_inv, div_eq_iff (exp_ne_zero _), one_mul] at h
  exact h.symm

variable {T : ℝ} [Fact (0 < T)]

/-- Radial evaluation of a disk function in the unit-circle character. -/
def radial (f : ℂ → ℂ) (r : ℝ) (x : AddCircle T) : ℂ := f ((r:ℂ) * fourier 1 x)

theorem radial_mem_ball {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : AddCircle T) :
    (r:ℂ)*fourier 1 x ∈ ball (0:ℂ) 1 := by
  simpa [mem_ball_zero_iff, norm_mul, abs_of_nonneg hr] using hr1

private theorem fourier_natCast (n : ℕ) (x : AddCircle T) : fourier (n:ℤ) x = (fourier 1 x)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ, fourier_add, ih, pow_succ]

private def radialCoeffs (g : ℂ → ℂ) (r : ℝ) : ℤ → ℂ
  | .ofNat n => (r:ℂ)^n * coeff g n
  | .negSucc _ => 0

private theorem fourier_radial {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (ball 0 1))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    fourierCoeff (radial (T:=T) g r) = radialCoeffs g r := by
  apply fourierCoeff_eq_of_hasSum
  intro x
  have hp := Complex.hasSum_taylorSeries_on_ball hg.differentiableOn (radial_mem_ball hr hr1 x)
  have hpos : HasSum (fun n : ℕ ↦ fourier (n:ℤ) x • radialCoeffs g r (n:ℤ)) (radial g r x) := by
    refine hp.congr_fun (fun n ↦ ?_)
    rw [fourier_natCast]
    simp only [radialCoeffs, coeff, smul_eq_mul, mul_pow, div_eq_mul_inv, sub_zero]
    ring
  have hneg : HasSum (fun n : ℕ ↦ fourier (-(n+1:ℤ)) x • radialCoeffs g r (-(n+1:ℤ))) 0 := by
    convert (hasSum_zero (β := ℕ) (α := ℂ)) using 1
    funext n
    change fourier _ x • (0:ℂ) = 0
    simp
  simpa only [add_zero] using (HasSum.of_nat_of_neg_add_one (f := fun k ↦ fourier k x • radialCoeffs g r k) hpos hneg)

private theorem two_mode_re {φ : AddCircle T → ℂ} (hφ : Integrable φ haarAddCircle) (k : ℤ) :
    2 * mode (fun x ↦ (φ x).re) k = fourierCoeff φ k + conj (fourierCoeff φ (-k)) := by
  have hstar : Integrable (fun x ↦ conj (φ x)) haarAddCircle := Complex.conjCLE.toContinuousLinearMap.integrable_comp hφ
  rw [← fourierCoeff_conj, ← Pi.add_apply, ← fourierCoeff.add hφ hstar]
  change 2 * fourierCoeff (fun x ↦ ((φ x).re : ℂ)) k = _
  rw [← fourierCoeff.const_mul]
  congr 2
  funext x
  simpa using (Complex.add_conj (φ x)).symm

/-- The positive modes of the radial log modulus are the Taylor coefficients of a holomorphic logarithm. -/
theorem logDeriv_eq_two_radial_mode {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hn : ∀ z ∈ ball (0:ℂ) 1, f z ≠ 0) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    2 * mode (T:=T) (fun x ↦ Real.log ‖radial f r x‖) (n+1) =
      (r:ℂ)^(n+1) * (coeff (logDeriv f) n / (n+1:ℂ)) := by
  obtain ⟨g,hg,he,hg'⟩ := exists_analytic_log hf hn
  have harg : (fun x : AddCircle T ↦ Real.log ‖radial f r x‖) = fun x ↦ (radial g r x).re := by
    funext x
    rw [radial, ← he _ (radial_mem_ball hr hr1 x), Complex.norm_exp, Real.log_exp]
    rfl
  have hgI : Integrable (radial (T:=T) g r) haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (.of_compactSpace _)
    change Continuous (g ∘ fun x : AddCircle T ↦ (r:ℂ)*fourier 1 x)
    exact continuous_iff_continuousAt.mpr fun x ↦
      (hg _ (radial_mem_ball hr hr1 x)).continuousAt.comp (x:=x) (f:=fun t : AddCircle T ↦ (r:ℂ)*fourier 1 t) (by fun_prop : ContinuousAt (fun x : AddCircle T ↦ (r:ℂ)*fourier 1 x) x)
  rw [harg, two_mode_re hgI, fourier_radial hg hr hr1]
  change (r:ℂ)^(n+1) * coeff g (n+1) + conj 0 = _
  rw [map_zero, add_zero, coeff, coeff, iteratedDeriv_succ', Nat.factorial_succ,
    (hg'.eventuallyEq_of_mem (isOpen_ball.mem_nhds (by simp : (0:ℂ) ∈ ball 0 1))).iteratedDeriv_eq n]
  push_cast
  rw [div_div, mul_comm (n.factorial:ℂ)]

/-- Fourier coefficients are continuous for real L¹ convergence. -/
theorem tendsto_mode_of_l1 {u : AddCircle T → ℝ} {v : ℕ → AddCircle T → ℝ}
    (hu : Integrable u haarAddCircle) (hv : ∀ n, Integrable (v n) haarAddCircle)
    (hl : Tendsto (fun n ↦ ∫ x, |v n x-u x| ∂haarAddCircle) atTop (𝓝 0)) (k : ℤ) :
    Tendsto (fun n ↦ mode (v n) k) atTop (𝓝 (mode u k)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun n ↦ norm_nonneg _) (fun n ↦ ?_) hl
  have hf := (hv n).ofReal (𝕜 := ℂ)
  have hg := hu.ofReal (𝕜 := ℂ)
  let F (x : AddCircle T) : ℂ := fourier (-k) x * (v n x : ℂ)
  let G (x : AddCircle T) : ℂ := fourier (-k) x * (u x : ℂ)
  have hF : Integrable F haarAddCircle := hf.fourier_smul (-k)
  have hG : Integrable G haarAddCircle := hg.fourier_smul (-k)
  change ‖(∫ x, F x ∂haarAddCircle) - (∫ x, G x ∂haarAddCircle)‖ ≤ _
  rw [← integral_sub hF hG]
  apply le_trans (norm_integral_le_integral_norm _)
  apply le_of_eq
  apply integral_congr_ae
  exact ae_of_all _ fun x ↦ by simp [F, G, ← mul_sub, ← ofReal_sub]

/-- A radial L¹ trace determines every normalized logarithmic derivative coefficient. -/
theorem two_mode_eq_logDeriv_of_radial_L1 {f : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 1))
    (hn : ∀ z ∈ ball (0:ℂ) 1, f z ≠ 0) {r : ℕ → ℝ} (hr : ∀ n, 0 ≤ r n ∧ r n < 1)
    (ht : Tendsto r atTop (𝓝 1)) (u : AddCircle T → ℝ) (hu : Integrable u haarAddCircle)
    (hl : Tendsto (fun j ↦ ∫ x, |Real.log ‖radial f (r j) x‖-u x| ∂haarAddCircle) atTop (𝓝 0))
    (n : ℕ) : 2 * mode u (n+1) = coeff (logDeriv f) n / (n+1:ℂ) := by
  have hi (j) : Integrable (fun x : AddCircle T ↦ Real.log ‖radial f (r j) x‖) haarAddCircle := by
    apply Continuous.integrable_of_hasCompactSupport _ (.of_compactSpace _)
    apply continuous_iff_continuousAt.mpr
    intro x
    have hx := radial_mem_ball (hr j).1 (hr j).2 x
    exact (((hf _ hx).continuousAt.comp (x:=x) (f:=fun t : AddCircle T ↦ (r j:ℂ)*fourier 1 t) (by fun_prop :
      ContinuousAt (fun x : AddCircle T ↦ (r j:ℂ)*fourier 1 x) x)).norm).log (norm_ne_zero_iff.mpr (hn _ hx))
  have hm := (tendsto_mode_of_l1 hu hi hl (n+1)).const_mul (2:ℂ)
  have hT := (((Complex.continuous_ofReal.tendsto 1).comp ht).pow (n+1)).mul_const
    (coeff (logDeriv f) n / (n+1:ℂ))
  simpa only [ofReal_one, one_pow, one_mul] using (tendsto_nhds_unique hm
    (hT.congr (fun j ↦ (logDeriv_eq_two_radial_mode hf hn (hr j).1 (hr j).2 n).symm)))

local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "𝕋" => AddCircle (2*Real.pi)
local notation "μθ" => volume.restrict (Ioc (0:ℝ) (2*Real.pi))

theorem fourier_one_coe (t : ℝ) : fourier 1 (t : 𝕋) = circleMap 0 1 t := by
  rw [fourier_coe_apply, circleMap_zero]
  push_cast
  simp only [one_mul, mul_one]
  congr 1
  field_simp

/-- Probability Haar integral of an angular lift is the usual normalized real angular integral. -/
theorem integral_angle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : 𝕋 → E) :
    (∫ x, h x ∂haarAddCircle) =
      (2*Real.pi)⁻¹ • ∫ t in Ioc (0:ℝ) (2*Real.pi), h (t:𝕋) := by
  rw [integral_haarAddCircle, ← AddCircle.integral_preimage (2*Real.pi) 0 h, zero_add]

/-- The logarithmic modulus on a circle as a function of its real angle. -/
def angleLog (f : ℂ → ℂ) (r θ : ℝ) : ℝ := Real.log ‖f (circleMap 0 r θ)‖

theorem regular_boundary_angles {f : ℂ → ℂ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → AnalyticAt ℂ f z ∧ analyticOrderAt f z ≠ ⊤) :
    ∀ᵐ θ : ℝ, circleMap 0 1 θ ≠ 1 ∧ f (circleMap 0 1 θ) ≠ 0 := by
  let S := closedBall (0:ℂ) 1 \ {1}
  let Z := {z : ℂ | f z = 0} ∩ S
  have hc : Z.Countable := by
    apply (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete
    apply isDiscrete_of_codiscreteWithin
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE]
    intro z hz
    obtain ⟨hza,hzo⟩ := hf z (by simpa using hz.1) (by simpa using hz.2)
    have h := hza.eventually_eq_zero_or_eventually_ne_zero.resolve_left (fun he ↦ hzo (analyticOrderAt_eq_top.mpr he))
    filter_upwards [h] with u hu using Or.inl hu
  have hn := (((countable_singleton (1:ℂ)).union hc).preimage_circleMap 0 one_ne_zero).ae_notMem volume
  filter_upwards [hn] with θ hθ
  have h1 : circleMap 0 1 θ ≠ 1 := fun h ↦ hθ (Or.inl h)
  exact ⟨h1,fun h ↦ hθ (Or.inr ⟨h, by simp [S,norm_circleMap_zero,h1]⟩)⟩

/-- An upper bound and convergence of logarithmic means promote pointwise radial convergence
to L¹ even when the boundary has zeros. The exceptional point is the angle at one. -/
theorem radial_log_L1_of_means {f : ℂ → ℂ} {B : ℝ}
    (hf : ∀ z : ℂ, ‖z‖ ≤ 1 → z ≠ 1 → AnalyticAt ℂ f z ∧ analyticOrderAt f z ≠ ⊤)
    (hB : ∀ z : ℂ, ‖z‖ ≤ 1 → Real.log ‖f z‖ ≤ B)
    (hI : CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 1)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n ∧ r n < 1) (ht : Tendsto r atTop (𝓝 1))
    (hmean : Tendsto (fun n ↦ Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 (r n)) atTop
       (𝓝 (Real.circleAverage (fun z ↦ Real.log ‖f z‖) 0 1))) :
    Tendsto (fun n ↦ ∫ x, |angleLog f (r n) x-angleLog f 1 x| ∂μθ) atTop (𝓝 0) := by
  let U (t : ℝ) := angleLog f t
  have hμ : IsFiniteMeasure μθ := by infer_instance
  have hi : Integrable (U 1) μθ := hI.1
  have hin (n) : Integrable (U (r n)) μθ := by
    apply (show CircleIntegrable (fun z ↦ Real.log ‖f z‖) 0 (r n) from ?_).1
    apply MeromorphicOn.circleIntegrable_log_norm
    intro z hz
    have hz' : ‖z‖ = r n := by simpa only [abs_of_pos (hr n).1] using mem_sphere_zero_iff_norm.mp hz
    exact (hf z (hz' ▸ (hr n).2.le) (fun hh ↦ by rw [hh,norm_one] at hz'; linarith [(hr n).2])).1.meromorphicAt
  have upper t (h0 : 0≤t) (h1 : t≤1) (x : ℝ) : U t x ≤ B :=
    hB _ (by simpa [norm_circleMap_zero,abs_of_nonneg h0] using h1)
  have hpt : ∀ᵐ x ∂μθ, Tendsto (fun n ↦ B-U (r n) x) atTop (𝓝 (B-U 1 x)) := by
    filter_upwards [ae_restrict_of_ae (regular_boundary_angles hf)] with x hx
    have hz : ‖circleMap 0 1 x‖ ≤ 1 := by simp [norm_circleMap_zero]
    have hc : Tendsto (fun n ↦ circleMap 0 (r n) x) atTop (𝓝 (circleMap 0 1 x)) := by
      simpa only [circleMap_zero, Function.comp_apply] using ((continuous_ofReal.tendsto 1).comp ht).mul (tendsto_const_nhds (x := exp ((x:ℂ)*I)))
    exact tendsto_const_nhds.sub ((((hf _ hz hx.1).1.continuousAt.tendsto.comp hc).norm).log
      (norm_ne_zero_iff.mpr hx.2))
  have hm : Tendsto (fun n ↦ ∫ x, U (r n) x ∂μθ) atTop (𝓝 (∫ x, U 1 x ∂μθ)) := by
    have h := hmean.const_mul (2*Real.pi)
    simpa [Real.circleAverage_def,intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi),
      smul_eq_mul, U, angleLog, ←mul_assoc, Real.pi_ne_zero] using h
  have hms := (tendsto_const_nhds (x:=∫ _ : ℝ, B ∂μθ)).sub hm
  have hs := tendsto_integral_abs_sub_of_nonneg (μ:=μθ)
    (v:=fun n x ↦ B-U (r n) x) (u:=fun x ↦ B-U 1 x)
    (fun n ↦ (integrable_const B).sub (hin n)) ((integrable_const B).sub hi)
    (fun n ↦ ae_of_all _ fun x ↦ sub_nonneg.mpr (upper _ (hr n).1.le (hr n).2.le x))
    (ae_of_all _ fun x ↦ sub_nonneg.mpr (upper 1 zero_le_one le_rfl x)) hpt
    (by simpa only [integral_sub (integrable_const B) hi, integral_sub (integrable_const B) (hin _)] using hms)
  simpa only [sub_sub_sub_cancel_left, abs_sub_comm (U 1 _) (U _ _)] using hs

end RiemannMasullo.BoundaryHardy
