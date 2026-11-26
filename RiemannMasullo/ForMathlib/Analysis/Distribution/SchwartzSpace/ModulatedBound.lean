module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.LocallyConvex.Barrelled
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete

/-! # Modulated tests and uniform bounds on the Schwartz space of the line

For a smooth compactly supported `ρ`, the Schwartz seminorms of the modulated functions
`ρ(x) e^{-itx}` grow at most polynomially in `t`. With the Banach–Steinhaus theorem on the
Schwartz space, which is a Fréchet space, a family of continuous linear functionals that is
bounded at each Schwartz function therefore grows at most polynomially along these modulated
functions, uniformly in the family. Integration against an integrable function is such a
functional. -/

@[expose] public noncomputable section

open Complex
open scoped SchwartzMap ContDiff

namespace RiemannMasullo

/-- Iterated derivatives of a complex exponential of a real variable. -/
theorem iteratedDeriv_cexp_real_const_mul (c : ℂ) (n : ℕ) :
    iteratedDeriv n (fun x : ℝ ↦ cexp (c * x)) = fun x : ℝ ↦ c ^ n * cexp (c * x) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    have h : HasDerivAt (fun y : ℝ ↦ c ^ n * cexp (c * y)) (c ^ n * (cexp (c * x) * c)) x := by
      have h1 : HasDerivAt (fun y : ℝ ↦ c * (y : ℂ)) c x := by
        simpa using ((hasDerivAt_id x).ofReal_comp).const_mul c
      exact (h1.cexp).const_mul _
    rw [h.deriv]
    ring

/-- The iterated derivatives of the unimodular wave `e^{-itx}` have norm `|t|^j`. -/
theorem norm_iteratedFDeriv_cexp_I_mul (t : ℝ) (j : ℕ) (x : ℝ) :
    ‖iteratedFDeriv ℝ j (fun y : ℝ ↦ cexp (-(t : ℂ) * I * y)) x‖ = |t| ^ j := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cexp_real_const_mul]
  rw [norm_mul, norm_pow]
  have : -(t : ℂ) * I * (x : ℂ) = ((-(t * x) : ℝ) : ℂ) * I := by push_cast; ring
  rw [this, norm_exp_ofReal_mul_I, mul_one]
  simp

/-- The unimodular wave `e^{-itx}` is smooth. -/
theorem contDiff_cexp_I_mul (t : ℝ) :
    ContDiff ℝ ∞ (fun y : ℝ ↦ cexp (-(t : ℂ) * I * y)) :=
  (contDiff_const.mul ofRealCLM.contDiff).cexp

/-- The modulated test `ρ(x) e^{-itx}` as a Schwartz function. -/
noncomputable def modulatedSchwartz (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    (t : ℝ) : SchwartzMap ℝ ℂ :=
  (hc.mul_right (f' := fun y : ℝ ↦ cexp (-(t : ℂ) * I * y))).toSchwartzMap
    (hρ.mul (contDiff_cexp_I_mul t))

/-- The values of the modulated test. -/
theorem modulatedSchwartz_apply (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    (t x : ℝ) : modulatedSchwartz ρ hρ hc t x = ρ x * cexp (-(t : ℂ) * I * x) := rfl

/-- The Schwartz seminorms of the modulated tests grow polynomially in the frequency. -/
theorem modulatedSchwartz_seminorm_le (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ)
    (k n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      SchwartzMap.seminorm ℂ k n (modulatedSchwartz ρ hρ hc t) ≤ C * (1 + |t|) ^ n := by
  let ρS := hc.toSchwartzMap hρ
  let A (i : ℕ) := SchwartzMap.seminorm ℂ k i ρS
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i, by positivity, fun t ↦ ?_⟩
  refine SchwartzMap.seminorm_le_bound ℂ k n _ (by positivity) fun x ↦ ?_
  have hmul := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (n := n) hρ
    (contDiff_cexp_I_mul t) x
    (by exact_mod_cast le_top)
  have h1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  calc ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (modulatedSchwartz ρ hρ hc t) x‖
      ≤ ‖x‖ ^ k * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i ρ x‖ *
          ‖iteratedFDeriv ℝ (n - i) (fun y : ℝ ↦ cexp (-(t : ℂ) * I * y)) x‖ :=
        mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i ρ x‖) *
          |t| ^ (n - i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        rw [norm_iteratedFDeriv_cexp_I_mul]
        ring
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i * (1 + |t|) ^ n := by
        refine Finset.sum_le_sum fun i hi ↦ ?_
        have hA : ‖x‖ ^ k * ‖iteratedFDeriv ℝ i ρ x‖ ≤ A i := SchwartzMap.le_seminorm ℂ k i ρS x
        have ht : |t| ^ (n - i) ≤ (1 + |t|) ^ n :=
          (pow_le_pow_left₀ (abs_nonneg t) (by linarith) _).trans
            (pow_le_pow_right₀ h1 (Nat.sub_le n i))
        have hc0 : (0 : ℝ) ≤ n.choose i := by positivity
        calc (n.choose i : ℝ) * (‖x‖ ^ k * ‖iteratedFDeriv ℝ i ρ x‖) * |t| ^ (n - i)
            ≤ (n.choose i : ℝ) * A i * |t| ^ (n - i) := by gcongr
          _ ≤ (n.choose i : ℝ) * A i * (1 + |t|) ^ n := by gcongr
    _ = (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * A i) * (1 + |t|) ^ n := by
        rw [Finset.sum_mul]


/-- Banach–Steinhaus on the Schwartz space of the line: a pointwise bounded family of
continuous linear functionals is bounded by finitely many Schwartz seminorms. -/
theorem schwartz_uniform_bound {ι : Type*} (L : ι → 𝓢(ℝ, ℂ) →L[ℂ] ℂ) (B : 𝓢(ℝ, ℂ) → ℝ)
    (h : ∀ i ψ, ‖L i ψ‖ ≤ B ψ) :
    ∃ s : Finset (ℕ × ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ i ψ,
      ‖L i ψ‖ ≤ C * ∑ p ∈ s, SchwartzMap.seminorm ℂ p.1 p.2 ψ := by
  have : CompleteSpace 𝓢(ℝ, ℂ) := completeSpace_schwartzMap
  have : (uniformity 𝓢(ℝ, ℂ)).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero 𝓢(ℝ, ℂ)]
    infer_instance
  have : BaireSpace 𝓢(ℝ, ℂ) := by
    let := UniformSpace.metricSpace 𝓢(ℝ, ℂ)
    infer_instance
  let p (i : ι) : Seminorm ℂ 𝓢(ℝ, ℂ) := (normSeminorm ℂ ℂ).comp (L i).toLinearMap
  have hp (i : ι) : Continuous (p i) := continuous_norm.comp (L i).continuous
  have hbdd : BddAbove (Set.range p) := by
    rw [Seminorm.bddAbove_range_iff]
    exact fun ψ ↦ ⟨B ψ, by rintro _ ⟨i, rfl⟩; exact h i ψ⟩
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_sum_of_continuous (schwartz_withSeminorms ℂ ℝ ℂ)
    (⨆ i, p i) (by rw [Seminorm.coe_iSup_eq hbdd]; exact Seminorm.continuous_iSup p hp hbdd)
  refine ⟨s, C, C.coe_nonneg, fun i ψ ↦ ?_⟩
  have h1 : ‖L i ψ‖ ≤ (⨆ i, p i) ψ := by
    rw [Seminorm.iSup_apply hbdd]
    exact le_ciSup (f := fun i ↦ p i ψ)
      ⟨B ψ, by rintro _ ⟨j, rfl⟩; exact h j ψ⟩ i
  refine h1.trans ((hC ψ).trans_eq ?_)
  have hsum (t : Finset (ℕ × ℕ)) : (∑ q ∈ t, schwartzSeminormFamily ℂ ℝ ℂ q) ψ =
      ∑ q ∈ t, SchwartzMap.seminorm ℂ q.1 q.2 ψ := by
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert q t hq ih => rw [Finset.sum_insert hq, Finset.sum_insert hq, add_apply, ih]; rfl
  rw [smul_apply, hsum, NNReal.smul_def, smul_eq_mul]

/-- Along the modulated tests, a pointwise bounded family of functionals grows at most
polynomially in the frequency, uniformly in the family. -/
theorem schwartz_uniform_bound_modulated {ι : Type*} (L : ι → 𝓢(ℝ, ℂ) →L[ℂ] ℂ)
    (B : 𝓢(ℝ, ℂ) → ℝ) (h : ∀ i ψ, ‖L i ψ‖ ≤ B ψ)
    (ρ : ℝ → ℂ) (hρ : ContDiff ℝ ∞ ρ) (hc : HasCompactSupport ρ) :
    ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧ ∀ i t, ‖L i (modulatedSchwartz ρ hρ hc t)‖ ≤ C * (1 + |t|) ^ N := by
  obtain ⟨s, C, hC, hL⟩ := schwartz_uniform_bound L B h
  choose D hD0 hD using fun p : ℕ × ℕ ↦ modulatedSchwartz_seminorm_le ρ hρ hc p.1 p.2
  let N := s.sup Prod.snd
  refine ⟨C * ∑ p ∈ s, D p, N, mul_nonneg hC (Finset.sum_nonneg fun p _ ↦ hD0 p),
    fun i t ↦ (hL i _).trans ?_⟩
  have h1 : (1 : ℝ) ≤ 1 + |t| := by linarith [abs_nonneg t]
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p hp ↦ (hD p t).trans ?_) hC
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ h1 (Finset.le_sup (f := Prod.snd) hp))
    (hD0 p)

/-- Integration against an integrable function is a continuous functional on Schwartz space. -/
noncomputable def schwartzPairing (g : ℝ → ℂ) (hg : MeasureTheory.Integrable g) :
    𝓢(ℝ, ℂ) →L[ℂ] ℂ :=
  SchwartzMap.mkCLMtoNormedSpace (fun ψ ↦ ∫ x, g x * ψ x)
    (fun ψ ψ' ↦ by
      simp only [add_apply, mul_add]
      exact MeasureTheory.integral_add (hg.mul_bdd ψ.continuous.aestronglyMeasurable
        (Filter.Eventually.of_forall (ψ.norm_le_seminorm ℂ)))
        (hg.mul_bdd ψ'.continuous.aestronglyMeasurable
          (Filter.Eventually.of_forall (ψ'.norm_le_seminorm ℂ))))
    (fun c ψ ↦ by
      simp only [smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [← MeasureTheory.integral_const_mul]
      congr 1; funext x; ring)
    ⟨{(0, 0)}, ∫ x, ‖g x‖, MeasureTheory.integral_nonneg fun _ ↦ norm_nonneg _, fun ψ ↦ by
      simp only [Finset.sup_singleton, SchwartzMap.schwartzSeminormFamily_apply]
      calc ‖∫ x, g x * ψ x‖ ≤ ∫ x, ‖g x‖ * SchwartzMap.seminorm ℂ 0 0 ψ := by
            refine MeasureTheory.norm_integral_le_of_norm_le (hg.norm.mul_const _)
              (Filter.Eventually.of_forall fun x ↦ ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (ψ.norm_le_seminorm ℂ x) (norm_nonneg _)
        _ = (∫ x, ‖g x‖) * SchwartzMap.seminorm ℂ 0 0 ψ := MeasureTheory.integral_mul_const _ _⟩

/-- The values of the pairing. -/
theorem schwartzPairing_apply (g : ℝ → ℂ) (hg : MeasureTheory.Integrable g) (ψ : 𝓢(ℝ, ℂ)) :
    schwartzPairing g hg ψ = ∫ x, g x * ψ x := rfl

end RiemannMasullo
