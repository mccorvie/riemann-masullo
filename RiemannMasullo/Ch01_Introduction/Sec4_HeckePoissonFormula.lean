module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoissonMass
public import RiemannMasullo.AppB_AnalyticNT.HeckeResolventBoxes
import RiemannMasullo.ForMathlib.Analysis.Complex.ReflectedResolvent
import Mathlib.Tactic

/-! # Positive Poisson mass of a section-normalized Hecke character

The real part of the logarithmic derivative of the pole-cleared completed
Hecke function at `σ + t I` equals an absolutely convergent sum of positive
Cauchy kernels, with each completed-divisor site counted with multiplicity.
The library's completed function omits the square-root conductor power;
`logDerivativeMass` supplies half its logarithmic derivative.

The complex two-point residue calculation uses the estimates on expanding
rectangles and the fixed character's functional equation. The translated
Dirichlet case underlies the finite-cell method of Ghaith Hiary, Summer Ireland and
Megan Kyi, *A method for verifying the generalized Riemann hypothesis* (2024),
§5, Theorem 11. [Paper](https://arxiv.org/html/2408.00187v1#S5)
-/

public noncomputable section

open Classical Complex Set Filter Function NumberField Topology
open scoped ComplexConjugate NNReal
namespace RiemannMasullo.HeckePoisson

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual CF
local notation "d(" χ "," u ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ u

/-- Logarithmic derivative with the principal poles at zero and one cleared. -/
private def poleCleared (χ : U) (s : ℂ) : ℂ := by
  classical
  exact logDeriv (continuedCompletedHeckeL χ) s +
    if χ = 1 then 1/s + 1/(s-1) else 0

private theorem weighted_real_resolvent (m : ℝ) (σ t : ℝ) (p : ℂ) :
    ((m : ℂ) / ((σ : ℂ) + (t : ℂ)*I - p)).re = m * poissonWeight σ t p := by
  rw [poissonWeight_eq_re_inv, div_eq_mul_inv]
  simp [Complex.mul_re]

/-- The canonical all-site Poisson mass follows from the corresponding complex resolvent
difference. The arithmetic reflection at the left evaluation point follows independently
by differentiating the completed functional equation. -/
private theorem hasSum_logDerivativeMass_of_reflected_difference (χ : U) (σ t : ℝ) (hσ : 1 < σ)
    (hd : let s := (σ : ℂ) + (t : ℂ)*I
      HasSum (fun p : Site χ ↦ (multiplicity p : ℂ) * (1/(s-p.val)-1/(1-conj s-p.val)))
        (poleCleared χ s - poleCleared χ (1-conj s))) :
    HasSum (fun p : Site χ ↦ (multiplicity p : ℝ) * poissonWeight σ t p.val)
      (logDerivativeMass χ σ t) := by
  let s := (σ : ℂ) + (t : ℂ)*I
  have hs : 1 < s.re := by simpa [s, Complex.mul_re] using hσ
  have hfe : (poleCleared χ (1-conj s)).re = -(poleCleared χ s).re -
      heckeLogDiscriminantConductor χ :=
    re_completedHeckeL_poleCleared_logDeriv_reflection χ s hs
  have hn (p : Site χ) : 0 ≤ (((multiplicity p : ℝ) : ℂ)/(s-p.val)).re := by
    change 0 ≤ (((multiplicity p : ℝ) : ℂ)/((σ : ℂ)+(t : ℂ)*I-p.val)).re
    rw [weighted_real_resolvent]
    exact mul_nonneg (Nat.cast_nonneg _) (poissonWeight_pos_of_site hσ t p).le
  have h := Complex.hasSum_real_resolvent_of_mirror
    (fun p : Site χ ↦ p.val) (fun p ↦ (multiplicity p : ℝ)) (positiveSiteReflection χ)
    (fun _ ↦ rfl) (fun p ↦ by rw [multiplicity_reflection]) s (poleCleared χ)
    (heckeLogDiscriminantConductor χ) hn hfe (by simpa only [Complex.ofReal_natCast] using hd)
  simpa only [s, weighted_real_resolvent, logDerivativeMass, poleCleared, add_comm] using h

private theorem summable_site_reciprocal_sq (χ : U) (s : ℂ) (hs : ∀ z : Site χ, s ≠ z.val) :
    Summable (fun z : Site χ ↦ (multiplicity z : ℝ)*‖(s-z.val)⁻¹‖^2) := by
  let V := {p : ℂ // 0 < d(χ,p) ∧ |p.re-1/2| < (1/2 : ℝ)}
  let e (p : Site χ) : V :=
    ⟨p.val,p.property,completedHecke_positive_divisor_in_critical_strip χ p.val p.property⟩
  have he : Injective e := fun _ _ h ↦ Subtype.ext (congrArg (fun r : V ↦ r.val) h)
  have hsep (r : V) : s-1/2 ≠ r.val-1/2 := by
    intro h
    exact hs ⟨r.val,r.property.1⟩ (sub_left_inj.mp h)
  have hn := (summable_completedHecke_divisor_reciprocal_squares χ (1/2) (s-1/2) hsep).comp_injective he
  apply hn.congr
  intro r
  change (d(χ,r.val) : ℝ)*‖(s-1/2-(r.val-1/2))⁻¹‖^2 =
    ((d(χ,r.val)).toNat : ℝ)*‖(s-r.val)⁻¹‖^2
  rw [show s-1/2-(r.val-1/2) = s-r.val by ring]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg r.property.le).symm

/-- The complex two-point resolvent series over the positive sites is absolutely
summable, including at points in the critical strip that avoid the divisor. -/
theorem summable_site_resolvent_difference (χ : U) (z b : ℂ)
    (hz : ∀ p : Site χ, z ≠ p.val) (hb : ∀ p : Site χ, b ≠ p.val) :
    Summable (fun p : Site χ ↦ (multiplicity p : ℂ)*(1/(z-p.val)-1/(b-p.val))) := by
  have hmaj := ((summable_site_reciprocal_sq χ z hz).add (summable_site_reciprocal_sq χ b hb)).mul_left ‖b-z‖
  apply hmaj.of_norm_bounded
  intro p
  have hz' := sub_ne_zero.mpr (hz p)
  have hb' := sub_ne_zero.mpr (hb p)
  have he : 1/(z-p.val)-1/(b-p.val) = (b-z)*(z-p.val)⁻¹*(b-p.val)⁻¹ := by
    field_simp
    ring
  rw [he]
  simp only [norm_mul, Complex.norm_natCast]
  let a := ‖(z-p.val)⁻¹‖
  let c := ‖(b-p.val)⁻¹‖
  change (multiplicity p : ℝ) * (‖b-z‖*a*c) ≤ ‖b-z‖*((multiplicity p : ℝ)*a^2 + (multiplicity p : ℝ)*c^2)
  have hadd : a*c ≤ a^2+c^2 := by nlinarith [sq_nonneg (a-c),sq_nonneg a,sq_nonneg c]
  calc
    _ = (‖b-z‖*(multiplicity p : ℝ))*(a*c) := by ring
    _ ≤ (‖b-z‖*(multiplicity p : ℝ))*(a^2+c^2) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ = _ := by ring

/-- Normalized characters have simple negative sites only at zero and one for
the principal character. This identity permits an arbitrary absolutely summable
positive-site sample, including one whose polar values are nonzero. -/
theorem hasSum_normalized_signed_divisor
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F)) (χ : U)
    (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (f : ℂ → ℂ)
    (hp : Summable (fun p : Site χ ↦ (multiplicity p : ℂ)*f p.val)) :
    HasSum (fun p : ℂ ↦ (d(χ,p) : ℂ)*f p)
      ((∑' p : Site χ, (multiplicity p : ℂ)*f p.val) -
        (if χ = 1 then f 0+f 1 else 0)) := by
  classical
  by_cases htriv : χ = 1
  · subst χ
    obtain ⟨h₀,h₁⟩ := idelicExplicitFormula_trivial_poles (F := F)
    change d((1 : U),0) = -1 at h₀
    change d((1 : U),1) = -1 at h₁
    have hP (j : ℂ) : j ∈ ({0,1} : Finset ℂ) ↔ d((1 : U),j) < 0 := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (rfl | rfl)
        · rw [h₀]; decide
        · rw [h₁]; decide
      · exact fun h ↦ (idelicExplicitFormula_chart_poles τ hτ (1 : U) hχ j h).2
    have hm (j : ℂ) (hj : j ∈ ({0,1} : Finset ℂ)) : d((1 : U),j) = -1 := by
      rcases Finset.mem_insert.mp hj with h | h
      · exact h ▸ h₀
      · exact (Finset.mem_singleton.mp h) ▸ h₁
    simpa [multiplicity] using Complex.hasSum_signed_simple_poles _ f {0,1} hP hm hp
  · have hP (j : ℂ) : j ∈ (∅ : Finset ℂ) ↔ d(χ,j) < 0 := by
      simp only [Finset.notMem_empty, false_iff]
      exact fun h ↦ htriv (idelicExplicitFormula_chart_poles τ hτ χ hχ j h).1
    simpa [multiplicity,htriv] using
      Complex.hasSum_signed_simple_poles _ f ∅ hP (by simp) hp

/-- The full positive Poisson mass from the functional equation and a sublinear
completed logarithmic-derivative bound on growing rectangles. All divisor tails,
orders, conductor scales, and principal-pole corrections use the actual Hecke data. -/
private theorem hasSum_logDerivativeMass_of_sublinear_boxes
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F)) (χ : U)
    (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (σ t : ℝ) (hσ : 1 < σ)
    (A B M : ℕ → ℝ) (hboxes : ∀ᶠ n : ℕ in atTop,
      ResolventRectangle.RegularLogDerivBox (continuedCompletedHeckeL χ) n (A n) (B n) (M n))
    (hsmall : Tendsto (fun n : ℕ ↦ M n/n) atTop (𝓝 0)) :
    HasSum (fun p : Site χ ↦ (multiplicity p : ℝ)*poissonWeight σ t p.val)
      (logDerivativeMass χ σ t) := by
  classical
  let s := (σ : ℂ)+(t : ℂ)*I
  let b := 1-conj s
  let L := continuedCompletedHeckeL χ
  have hs : s.re = σ := by simp [s,Complex.mul_re]
  have hb : b.re = 1-σ := by simp [b,Complex.sub_re,hs]
  have hb' : 1-conj b = s := by simp [b]
  have hsre : 1 < s.re := by rwa [hs]
  have hΛ := continuedCompletedHeckeL_spec χ
  have hz₀ : meromorphicOrderAt L s = 0 := by
    apply (hΛ.1 (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr
    rw [hΛ.2 ⟨s,hsre⟩]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hsre))
      (finiteHeckeL_ne_zero_of_one_lt_re χ _)
  have hb₀ : meromorphicOrderAt L b = 0 := by
    have h := completedHecke_reflected_order_of_re_lt_one χ b (by linarith [hb,hσ])
    rwa [hb',show meromorphicOrderAt (continuedCompletedHeckeL χ) s = 0 from hz₀, eq_comm] at h
  have hreg (u : ℂ) (hu : meromorphicOrderAt L u = 0) : AnalyticAt ℂ (logDeriv L) u := by
    have hf := hΛ.1 (mem_univ u)
    have ha := hf.meromorphicOrderAt_nonneg_iff_analyticAt.mp hu.ge
    exact ha.deriv.div ha (hf.meromorphicOrderAt_eq_zero_iff.mp hu)
  have hfinite (u : ℂ) : meromorphicOrderAt L u ≠ ⊤ :=
    hΛ.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ s) (mem_univ u) (by rw [hz₀]; exact WithTop.coe_ne_top)
  let f (u : ℂ) := 1/(s-u)-1/(b-u)
  have hpos : Summable (fun p : Site χ ↦ (multiplicity p : ℂ)*f p.val) := by
    apply summable_site_resolvent_difference
    · intro p he
      have := (siteStrip p).2
      linarith [congrArg Complex.re he,hs,hσ]
    · intro p he
      have := (siteStrip p).1
      linarith [congrArg Complex.re he,hb,hσ]
  have htot := hasSum_normalized_signed_divisor τ hτ χ hχ f hpos
  let signed (u : ℂ) := (d(χ,u) : ℂ)*f u
  let D := {u : ℂ | meromorphicOrderAt L u ≠ 0}
  have hsub : support signed ⊆ D := by
    intro u hu hzero
    apply hu
    change meromorphicOrderAt (continuedCompletedHeckeL χ) u = 0 at hzero
    simp [signed,MeromorphicOn.divisor_apply hΛ.1.meromorphicOn (mem_univ u),hzero]
  have hsd := ((hasSum_subtype_iff_of_support_subset hsub).mpr htot)
  have he (u : D) : signed u.val =
      ((meromorphicOrderAt L u.val).untop₀ : ℂ)*(1/(s-u.val)-1/(b-u.val)) := by
    dsimp only [signed, f, L]
    rw [MeromorphicOn.divisor_apply hΛ.1.meromorphicOn (mem_univ u.val)]
  have h₂ := hsd.congr_fun (fun u ↦ (he u).symm)
  have h₃ := ResolventRectangle.hasSum_divisor_resolvent_of_sublinear_boxes L hΛ.1.meromorphicOn
    hfinite s b hz₀ hb₀ (hreg s hz₀) (hreg b hb₀) A B M hboxes hsmall h₂.summable
  have hx := h₂.unique h₃
  apply hasSum_logDerivativeMass_of_reflected_difference χ σ t hσ
  change HasSum (fun p : Site χ ↦ (multiplicity p : ℂ)*f p.val) (poleCleared χ s-poleCleared χ b)
  suffices hp : (∑' p : Site χ, (multiplicity p : ℂ)*f p.val) = poleCleared χ s-poleCleared χ b by
    exact hp ▸ hpos.hasSum
  change (∑' p : Site χ, (multiplicity p : ℂ)*f p.val) - (if χ=1 then f 0+f 1 else 0) =
    logDeriv L s-logDeriv L b at hx
  by_cases hp : χ = 1
  · simp only [poleCleared, ite_eq_left hp] at hx ⊢
    simp only [f, sub_zero] at hx
    change _ = (logDeriv L s+_)-(logDeriv L b+_)
    linear_combination hx
  · simpa only [poleCleared, ite_eq_right hp, add_zero, sub_zero] using hx

/-- Centered arithmetic logarithmic derivative as the positive Poisson sum over
the actual Hecke divisor, with full multiplicity and fixed character. -/
theorem hasSum_logDerivativeMass
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : PontryaginDual CF) (hχ : ∀ r : ℝ≥0ˣ, χ (τ r) = 1)
    (σ t : ℝ) (hσ : 1 < σ) :
    HasSum (fun p : Site χ ↦ (multiplicity p : ℝ) * poissonWeight σ t p.val)
      (logDerivativeMass χ σ t) := by
  obtain ⟨A,B,M,hboxes,hsmall⟩ := ResolventRectangle.exists_sublinear_regularHeckeBoxes χ
  exact hasSum_logDerivativeMass_of_sublinear_boxes τ hτ χ hχ σ t hσ A B M hboxes hsmall

end RiemannMasullo.HeckePoisson
