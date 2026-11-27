module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! # A shrinking compact profile annihilating four polar moments

Applied to a smooth compact seed in log norm, the normalized fourth - order differential
operator has a bounded physical profile and a rapidly decaying bilateral Laplace transform.
The constants are uniform over translations bounded in units of the shrinking scale.
-/

@[expose] public noncomputable section

open MeasureTheory Set Function
open scoped ContDiff

namespace RiemannMasullo.PrimeShrink

private def L (g : ℝ → ℝ) (z : ℂ) := bilateralLaplace (fun x ↦ (g x : ℂ)) z

private theorem smoothD {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (n : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv n g) := by
  induction n with
  | zero => simpa only [iteratedDeriv_zero] using hg
  | succ n ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

private theorem suppD {g : ℝ → ℝ} (n : ℕ) : tsupport (iteratedDeriv n g) ⊆ tsupport g := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

private theorem compactD {g : ℝ → ℝ} (hc : HasCompactSupport g) (n : ℕ) :
    HasCompactSupport (iteratedDeriv n g) := by
  induction n with
  | zero => simpa using hc
  | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv

private theorem LD {h : ℝ → ℝ} (hs : ContDiff ℝ ∞ h) (hc : HasCompactSupport h) (z : ℂ) :
    L (deriv h) z = -z * L h z := by
  let E := fun x : ℝ ↦ Complex.exp (z * x)
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hE' (x : ℝ) : HasDerivAt E (z * E x) x := by
    change HasDerivAt (fun t : ℝ ↦ Complex.exp (z * t)) (z * Complex.exp (z * x)) x
    convert (((hasDerivAt_id' (x : ℂ)).const_mul z).cexp).comp_ofReal using 1
    ring
  have hH : Continuous (fun x ↦ (h x : ℂ)) := Complex.continuous_ofReal.comp hs.continuous
  have hD : Continuous (fun x ↦ ((deriv h x : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hs.continuous_deriv (by simp))
  have hcH : HasCompactSupport (fun x ↦ (h x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hcD : HasCompactSupport (fun x ↦ ((deriv h x : ℝ) : ℂ)) := hc.deriv.comp_left Complex.ofReal_zero
  have hparts := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := E) (u' := fun x ↦ z * E x) (v := fun x ↦ (h x : ℂ))
    (v' := fun x ↦ ((deriv h x : ℝ) : ℂ)) (fun x _ ↦ hE' x)
    (fun x _ ↦ ((hs.differentiable (by simp)) x).hasDerivAt.ofReal_comp)
    ((hE.mul hD).integrable_of_hasCompactSupport hcD.mul_left)
    (((continuous_const.mul hE).mul hH).integrable_of_hasCompactSupport hcH.mul_left)
    ((hE.mul hH).integrable_of_hasCompactSupport hcH.mul_left)
  change (∫ x : ℝ, ((deriv h x : ℝ) : ℂ) * E x) = -z * ∫ x : ℝ, (h x : ℂ) * E x
  calc ∫ x : ℝ, ((deriv h x : ℝ) : ℂ) * E x
      = ∫ x : ℝ, E x * ((deriv h x : ℝ) : ℂ) := by congr 1; funext x; ring
    _ = -∫ x : ℝ, z * E x * (h x : ℂ) := hparts
    _ = _ := by rw [neg_mul, ← integral_const_mul]; congr 2; funext x; ring

private theorem LDn {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) (z : ℂ) (n : ℕ) :
    L (iteratedDeriv n g) z = (-z) ^ n * L g z := by
  induction n with
  | zero => simp
  | succ n ih => rw [iteratedDeriv_succ, LD (smoothD hg n) (compactD hc n), ih, pow_succ']; ring

private theorem stripBound {g : ℝ → ℝ} (hg : Continuous g) (hc : HasCompactSupport g) (B : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, |w.re| ≤ B → ‖L g w‖ ≤ C := by
  let u := fun x : ℝ ↦ ‖(g x : ℂ)‖ * Real.exp (B * |x|)
  have hs := Complex.continuous_ofReal.comp hg
  have hc' : HasCompactSupport (fun x ↦ (g x : ℂ)) := hc.comp_left Complex.ofReal_zero
  have hu : Integrable u := (hs.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hc'.norm.mul_right
  refine ⟨∫ x : ℝ, u x, integral_nonneg (fun x ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le),
    fun w hw ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  have hi : Integrable (fun x : ℝ ↦ (g x : ℂ) * Complex.exp (w * x)) :=
    (hs.mul (by fun_prop)).integrable_of_hasCompactSupport hc'.mul_right
  apply integral_mono hi.norm hu
  intro x
  change ‖(g x : ℂ) * Complex.exp (w * x)‖ ≤ ‖(g x : ℂ)‖ * Real.exp (B * |x|)
  rw [norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [show (w * x).re = w.re * x by simp]
  exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hw (abs_nonneg x)))

private theorem rapidStrip {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (B : ℝ) (n : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, |z.re| ≤ B → (1 + ‖z‖) ^ n * ‖L g z‖ ≤ K := by
  obtain ⟨C, hC, h0⟩ := stripBound hg.continuous hc B
  obtain ⟨D, hD, hn⟩ := stripBound (smoothD hg n).continuous (compactD hc n) B
  refine ⟨2 ^ n * (C + D), by positivity, ?_⟩
  intro z hz
  have hder := hn z hz
  rw [LDn hg hc z n, norm_mul, norm_pow, norm_neg] at hder
  by_cases h : ‖z‖ ≤ 1
  · calc (1 + ‖z‖) ^ n * ‖L g z‖ ≤ (2 : ℝ) ^ n * C := by gcongr <;> first | linarith | exact h0 z hz
      _ ≤ _ := by gcongr; linarith
  · calc (1 + ‖z‖) ^ n * ‖L g z‖ ≤ (2 * ‖z‖) ^ n * ‖L g z‖ := by gcongr; linarith
      _ = (2 : ℝ) ^ n * (‖z‖ ^ n * ‖L g z‖) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := by gcongr; linarith

/-- The four derivative terms after rescaling the differential operator to the seed variable. -/
def body (g : ℝ → ℝ) (η x : ℝ) : ℝ :=
  iteratedDeriv 4 g x + η * iteratedDeriv 3 g x - η ^ 2 / 4 * iteratedDeriv 2 g x -
    η ^ 3 / 4 * iteratedDeriv 1 g x

/-- The compact physical profile at scale `η` and center `c + η*t`. -/
def profile (g : ℝ → ℝ) (η c t x : ℝ) : ℝ := body g η ((x - (c + η * t)) / η)

private theorem bodyLaplace {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (η : ℝ) (w : ℂ) : L (body g η) w =
      (w ^ 2 - (η : ℂ) ^ 2 / 4) * w * (w - η) * L g w := by
  let F (n : ℕ) (x : ℝ) := ((iteratedDeriv n g x : ℝ) : ℂ) * Complex.exp (w * x)
  have hi (n : ℕ) : Integrable (F n) :=
    ((Complex.continuous_ofReal.comp (smoothD hg n).continuous).mul (by fun_prop)).integrable_of_hasCompactSupport
      (((compactD hc n).comp_left Complex.ofReal_zero).mul_right)
  have he (n : ℕ) : (∫ x : ℝ, F n x) = (-w) ^ n * L g w := LDn hg hc w n
  have hfun : (fun x : ℝ ↦ (body g η x : ℂ) * Complex.exp (w * x)) =
      fun x ↦ F 4 x + (η : ℂ) * F 3 x - ((η : ℂ) ^ 2 / 4) * F 2 x - ((η : ℂ) ^ 3 / 4) * F 1 x := by
    funext x; simp only [body, F]; push_cast; ring
  change (∫ x : ℝ, (body g η x : ℂ) * Complex.exp (w * x)) = _
  have h43 : Integrable (fun x ↦ F 4 x + (η : ℂ) * F 3 x) := (hi 4).add ((hi 3).const_mul _)
  have h432 : Integrable (fun x ↦ F 4 x + (η : ℂ) * F 3 x - ((η : ℂ) ^ 2 / 4) * F 2 x) :=
    h43.sub ((hi 2).const_mul _)
  rw [hfun, integral_sub h432 ((hi 1).const_mul ((η : ℂ) ^ 3 / 4)),
    integral_sub h43 ((hi 2).const_mul ((η : ℂ) ^ 2 / 4)), integral_add (hi 4) ((hi 3).const_mul (η : ℂ))]
  simp only [integral_const_mul, he]
  ring

private theorem Lshift (g : ℝ → ℝ) (u : ℝ) (z : ℂ) :
    L (fun x ↦ g (x - u)) z = Complex.exp (z * u) * L g z := by
  unfold L bilateralLaplace
  calc ∫ x : ℝ, (g (x - u) : ℂ) * Complex.exp (z * x)
      = ∫ x : ℝ, (g (x - u) : ℂ) * Complex.exp (z * (((x - u : ℝ) : ℂ) + u)) := by
        congr 1; funext x; push_cast; ring_nf
    _ = ∫ x : ℝ, (g x : ℂ) * Complex.exp (z * (x + u)) :=
      integral_sub_right_eq_self (μ := volume) (fun x : ℝ ↦ (g x : ℂ) * Complex.exp (z * (x + u))) u
    _ = _ := by rw [← integral_const_mul]; congr 1; funext x; rw [mul_add, Complex.exp_add]; ring

private theorem Lscale (g : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (z : ℂ) :
    L (fun x ↦ g (x / η)) z = (η : ℂ) * L g (η * z) := by
  let F := fun y : ℝ ↦ (g y : ℂ) * Complex.exp ((η * z) * y)
  have hs : (fun x : ℝ ↦ (g (x / η) : ℂ) * Complex.exp (z * x)) = fun x ↦ F (x / η) := by
    funext x; dsimp [F]; congr 2; push_cast; field_simp [hη.ne']
  change (∫ x : ℝ, (g (x / η) : ℂ) * Complex.exp (z * x)) = _
  rw [hs, Measure.integral_comp_div, abs_of_pos hη, Complex.real_smul]
  rfl

/-- Exact transform of the dilated and translated four-moment filter. -/
theorem profile_laplace {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {η : ℝ} (hη : 0 < η) (c t : ℝ) (z : ℂ) :
    bilateralLaplace (fun x ↦ (profile g η c t x : ℂ)) z =
      (η : ℂ) ^ 5 * Complex.exp (z * ((c + η * t : ℝ) : ℂ)) * ((z ^ 2 - 1 / 4) * z * (z - 1)) *
        bilateralLaplace (fun x ↦ (g x : ℂ)) (η * z) := by
  change L (fun x ↦ (fun u ↦ body g η (u / η)) (x - (c + η * t))) z = _
  rw [Lshift (fun u ↦ body g η (u / η)) (c + η * t) z, Lscale (body g η) hη z,
    bodyLaplace hg hc η (η * z)]
  change _ = _ * L g (η * z)
  ring

private theorem scaledPolyBound {η : ℝ} (hη : 0 < η) (h1 : η ≤ 1) (w : ℂ) :
    ‖(w ^ 2 - (η : ℂ) ^ 2 / 4) * w * (w - η)‖ ≤ (1 + ‖w‖) ^ 4 := by
  have he : ‖(η : ℂ)‖ = η := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  have ha : ‖w ^ 2 - (η : ℂ) ^ 2 / 4‖ ≤ (1 + ‖w‖) ^ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_pow, norm_div, norm_pow, he]
    norm_num
    nlinarith [norm_nonneg w, mul_nonneg hη.le (sub_nonneg.mpr h1)]
  have hb : ‖w - (η : ℂ)‖ ≤ 1 + ‖w‖ := (norm_sub_le _ _).trans (by rw [he]; linarith)
  rw [norm_mul, norm_mul]
  calc _ ≤ (1 + ‖w‖) ^ 2 * (1 + ‖w‖) * (1 + ‖w‖) := by gcongr; linarith
    _ = _ := by ring

/-- The actual bilateral transform of the physical profile decays to every order, uniformly in
`0 < η ≤ 1`, all bounded translations `|t| ≤ T`, and every height in a fixed real strip. -/
theorem profile_laplace_decay {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (c T B : ℝ) (A : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (η : ℝ), 0 < η → η ≤ 1 →
      ∀ t : ℝ, |t| ≤ T → ∀ z : ℂ, |z.re| ≤ B →
        ‖bilateralLaplace (fun x ↦ (profile g η c t x : ℂ)) z‖ ≤ K * η / (1 + η * |z.im|) ^ A := by
  obtain ⟨C, hC, hrapid⟩ := rapidStrip hg hc B (4 + A)
  let E := Real.exp (B * (|c| + T))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨E * C, mul_nonneg hE hC, ?_⟩
  intro η hη h1 t ht z hz
  let w : ℂ := η * z
  have hwr : |w.re| ≤ B := by
    simpa [w, abs_mul, abs_of_pos hη] using (mul_le_of_le_one_left (abs_nonneg z.re) h1).trans hz
  have hwi : η * |z.im| ≤ ‖w‖ := by
    simpa [w, abs_mul, abs_of_pos hη] using Complex.abs_im_le_norm w
  have het : |η * t| ≤ T := by
    rw [abs_mul, abs_of_pos hη]; exact (mul_le_of_le_one_left (abs_nonneg t) h1).trans ht
  have hu : |c + η * t| ≤ |c| + T := (abs_add_le _ _).trans (add_le_add le_rfl het)
  have he : ‖Complex.exp (z * ((c + η * t : ℝ) : ℂ))‖ ≤ E := by
    rw [Complex.norm_exp]; apply Real.exp_le_exp.mpr
    rw [show (z * ((c + η * t : ℝ) : ℂ)).re = z.re * (c + η * t) by simp]
    exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul hz hu (abs_nonneg _) ((abs_nonneg _).trans hz)))
  have hs : L (profile g η c t) z = Complex.exp (z * ((c + η * t : ℝ) : ℂ)) *
      ((η : ℂ) * (((w ^ 2 - (η : ℂ) ^ 2 / 4) * w * (w - η)) * L g w)) := by
    change L (fun x ↦ (fun u ↦ body g η (u / η)) (x - (c + η * t))) z = _
    rw [Lshift (fun u ↦ body g η (u / η)) (c + η * t) z, Lscale (body g η) hη z, bodyLaplace hg hc η (η * z)]
  have heη : ‖(η : ℂ)‖ = η := by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  apply (le_div_iff₀ (by positivity)).mpr
  change ‖L (profile g η c t) z‖ * _ ≤ _
  rw [hs, norm_mul, norm_mul, norm_mul, heη]
  calc _ ≤ E * (η * ((1 + ‖w‖) ^ 4 * ‖L g w‖)) * (1 + ‖w‖) ^ A := by
         gcongr; exact scaledPolyBound hη h1 w
    _ = E * ((1 + ‖w‖) ^ (4 + A) * ‖L g w‖) * η := by rw [pow_add]; ring
    _ ≤ _ := by gcongr; exact hrapid w hwr

/-- All four prescribed real moments vanish, including the one at `z=1`. -/
theorem profile_four_moments {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    {η : ℝ} (hη : 0 < η) (c t : ℝ) (z : ℂ) (hz : z = -1 / 2 ∨ z = 0 ∨ z = 1 / 2 ∨ z = 1) :
    bilateralLaplace (fun x ↦ (profile g η c t x : ℂ)) z = 0 := by
  rw [profile_laplace hg hc hη]
  rcases hz with rfl | rfl | rfl | rfl <;> norm_num

/-- Value at the unshifted location `c`, retaining all lower derivative terms. -/
theorem profile_at_center (g : ℝ → ℝ) {η : ℝ} (hη : 0 < η) (c t : ℝ) :
    profile g η c t c = iteratedDeriv 4 g (-t) + η * iteratedDeriv 3 g (-t) -
      η ^ 2 / 4 * iteratedDeriv 2 g (-t) - η ^ 3 / 4 * iteratedDeriv 1 g (-t) := by
  have he : (c - (c + η * t)) / η = -t := by field_simp [hη.ne']; ring
  simp only [profile, he, body]

/-- The physical profile is uniformly bounded. Its value at the unshifted site differs from
the fourth derivative of the seed by at most a constant times the scale. Both constants depend
only on the seed, uniformly over every center and every translation. -/
theorem profile_physical_bounds {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g) :
    ∃ A E : ℝ, 0 ≤ A ∧ 0 ≤ E ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ c t : ℝ,
      (∀ x : ℝ, |profile g η c t x| ≤ A) ∧
      |profile g η c t c - iteratedDeriv 4 g (-t)| ≤ E * η := by
  have bound (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, |iteratedDeriv n g u| ≤ C := by
    have hK : IsCompact (tsupport (iteratedDeriv n g)) := compactD hc n
    obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn (smoothD hg n).continuous.continuousOn
    refine ⟨max b 0, le_max_right _ _, fun u ↦ ?_⟩
    by_cases hu : u ∈ tsupport (iteratedDeriv n g)
    · simpa only [Real.norm_eq_abs] using (hb u hu).trans (le_max_left b 0)
    · rw [image_eq_zero_of_notMem_tsupport hu, abs_zero]; exact le_max_right _ _
  obtain ⟨D₁, h₁, b₁⟩ := bound 1
  obtain ⟨D₂, h₂, b₂⟩ := bound 2
  obtain ⟨D₃, h₃, b₃⟩ := bound 3
  obtain ⟨D₄, h₄, b₄⟩ := bound 4
  let E := D₃ + D₂ + D₁
  have hE : 0 ≤ E := by dsimp [E]; positivity
  refine ⟨E + D₄, E, add_nonneg hE h₄, hE, ?_⟩
  intro η hη h1 c t
  have hs : η ^ 2 ≤ η := by nlinarith [mul_nonneg hη.le (sub_nonneg.mpr h1)]
  have hu : η ^ 3 ≤ η ^ 2 := by simpa only [pow_succ] using mul_le_of_le_one_right (sq_nonneg η) h1
  have hs' : η ^ 2 / 4 ≤ η := by linarith
  have hu' : η ^ 3 / 4 ≤ η := by linarith
  have hbody (u : ℝ) : |body g η u - iteratedDeriv 4 g u| ≤ E * η := by
    let f := fun n : ℕ ↦ iteratedDeriv n g u
    have he : body g η u - iteratedDeriv 4 g u =
        η * f 3 + -(η ^ 2 / 4 * f 2) + -(η ^ 3 / 4 * f 1) := by unfold body; dsimp [f]; ring
    rw [he]
    have htri := (abs_add_le (η * f 3 + -(η ^ 2 / 4 * f 2)) (-(η ^ 3 / 4 * f 1))).trans
      (add_le_add (abs_add_le (η * f 3) (-(η ^ 2 / 4 * f 2))) le_rfl)
    simp only [abs_neg, abs_mul, abs_of_pos hη, abs_of_nonneg (show 0 ≤ η ^ 2 / 4 by positivity),
      abs_of_nonneg (show 0 ≤ η ^ 3 / 4 by positivity)] at htri
    have m₃ : η * |f 3| ≤ η * D₃ := mul_le_mul_of_nonneg_left (b₃ u) hη.le
    have m₂ : η ^ 2 / 4 * |f 2| ≤ η * D₂ := mul_le_mul hs' (b₂ u) (abs_nonneg _) hη.le
    have m₁ : η ^ 3 / 4 * |f 1| ≤ η * D₁ := mul_le_mul hu' (b₁ u) (abs_nonneg _) hη.le
    exact htri.trans ((add_le_add (add_le_add m₃ m₂) m₁).trans_eq (by dsimp [E]; ring))
  constructor
  · intro x
    let u := (x - (c + η * t)) / η
    change |body g η u| ≤ E + D₄
    have htri := abs_add_le (body g η u - iteratedDeriv 4 g u) (iteratedDeriv 4 g u)
    rw [sub_add_cancel] at htri
    exact htri.trans (add_le_add ((hbody u).trans (mul_le_of_le_one_right hE h1)) (b₄ u))
  · have he : (c - (c + η * t)) / η = -t := by field_simp [hη.ne']; ring
    simpa only [profile, he] using hbody (-t)

/-- A seed supported in `[-1,1]` gives precisely the claimed outer support interval. -/
theorem profile_tsupport {g : ℝ → ℝ} (hg : tsupport g ⊆ Icc (-1) 1) {η : ℝ} (hη : 0 < η) (c t : ℝ) :
    tsupport (profile g η c t) ⊆ Icc (c + η * t - η) (c + η * t + η) := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  let u := (x - (c + η * t)) / η
  have hu : u ∈ tsupport g := by
    by_contra hh
    have hzero (n : ℕ) : iteratedDeriv n g u = 0 := image_eq_zero_of_notMem_tsupport (fun hy ↦ hh (suppD n hy))
    exact hx (by change body g η u = 0; simp [body, hzero])
  obtain ⟨hlo,hhi⟩ := hg hu
  change - 1 ≤ (x - (c + η * t)) / η at hlo
  change (x - (c + η * t)) / η ≤ 1 at hhi
  rw [le_div_iff₀ hη] at hlo
  rw [div_le_iff₀ hη] at hhi
  exact ⟨by linarith, by linarith⟩

/-- With bounded translations, every nonzero physical value lies within a common multiple of
the scale from the unshifted center. -/
theorem profile_dist_le_of_ne_zero {g : ℝ → ℝ} (hg : tsupport g ⊆ Icc (-1) 1)
    {η c t T x : ℝ} (hη : 0 < η) (ht : |t| ≤ T) (hx : profile g η c t x ≠ 0) :
    |x - c| ≤ (T + 1) * η := by
  obtain ⟨hl, hr⟩ := profile_tsupport hg hη c t (subset_tsupport _ hx)
  obtain ⟨htl, htr⟩ := abs_le.mp ht
  have hlow := mul_le_mul_of_nonneg_left htl hη.le
  have hhigh := mul_le_mul_of_nonneg_left htr hη.le
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A smooth seed supported in `[-1,1]` gives a smooth compact physical test. -/
theorem profile_smooth_compact {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hs : tsupport g ⊆ Icc (-1) 1)
    {η : ℝ} (hη : 0 < η) (c t : ℝ) : ContDiff ℝ ∞ (profile g η c t) ∧
      HasCompactSupport (profile g η c t) := by
  have hb : ContDiff ℝ ∞ (body g η) :=
    ((((smoothD hg 4).add (contDiff_const.mul (smoothD hg 3))).sub
      (contDiff_const.mul (smoothD hg 2))).sub (contDiff_const.mul (smoothD hg 1)))
  refine ⟨hb.comp ((contDiff_id.sub contDiff_const).div_const η), ?_⟩
  exact isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (profile_tsupport hs hη c t)

/-- Physical differentiations of the actual affine rescaling agree with the expanded profile. -/
theorem profile_eq_differential {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) {η : ℝ} (hη : 0 < η) (c t x : ℝ) :
    let f := fun y : ℝ ↦ g ((y - (c + η * t)) / η)
    profile g η c t x = η ^ 4 * (iteratedDeriv 4 f x + iteratedDeriv 3 f x -
      (1 / 4) * iteratedDeriv 2 f x - (1 / 4) * iteratedDeriv 1 f x) := by
  intro f
  have hscale (n : ℕ) : iteratedDeriv n f x = η⁻¹ ^ n * iteratedDeriv n g ((x - (c + η * t)) / η) := by
    let f₀ := fun y : ℝ ↦ g (η⁻¹ * y)
    have hf : f = fun y : ℝ ↦ f₀ (y - (c + η * t)) := by funext y; simp [f, f₀, div_eq_mul_inv, mul_comm]
    rw [hf, iteratedDeriv_comp_sub_const]
    change iteratedDeriv n (fun y ↦ g (η⁻¹ * y)) _ = _
    rw [iteratedDeriv_comp_const_mul (hg.of_le (by simp))]
    simp only [div_eq_mul_inv, mul_comm (x - (c + η * t))]
  simp only [hscale, profile, body]
  field_simp [hη.ne']

end RiemannMasullo.PrimeShrink
