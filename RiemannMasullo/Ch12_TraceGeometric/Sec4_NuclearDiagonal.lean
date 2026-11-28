module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Analysis.Normed.Group.Tannery

/-! # The intrinsic nuclear diagonal on a quotient Hilbert space

Paper: Theorem 12.4.1.1, Step III, pp. 516–517. A nuclear operator on an actual
measure-space L² gives a canonical L¹ trace density. The formula is the absolutely
convergent sum of its rank-one diagonals, not the set-theoretic restriction of an
almost-everywhere product kernel. Measurable spatial cuts recover its local
integrals. Strongly convergent contractive regularizations of both L² legs recover
the density in L¹ at fixed cutoff parameters. This module does not assert the
spatial-frequency cutoff limit or construct the full local projection. -/

public noncomputable section

open MeasureTheory Filter
open scoped ComplexConjugate InnerProductSpace ENNReal Topology

namespace RiemannMasullo.QuotientDiagonal

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

local notation "H " μ:max => Lp ℂ 2 μ

private theorem memLp_rankDiagonal (f g : H μ) :
    MemLp (fun x ↦ f x * conj (g x)) 1 μ := by
  have hg : MemLp (fun x ↦ conj (g x)) 2 μ := by
    apply (Lp.memLp g).of_le
      (Complex.continuous_conj.comp_aestronglyMeasurable (Lp.memLp g).aestronglyMeasurable)
    filter_upwards with x
    exact (Complex.norm_conj (g x)).le
  exact (Lp.memLp f).mul hg

/-- The rank-one diagonal is an actual L¹ element, independent of pointwise representatives. -/
def rankDiagonal (f g : H μ) : Lp ℂ 1 μ :=
  (memLp_rankDiagonal f g).toLp (fun x ↦ f x * conj (g x))

theorem rankDiagonal_ae (f g : H μ) : ⇑(rankDiagonal f g) =ᵐ[μ] fun x ↦ f x * conj (g x) :=
  (memLp_rankDiagonal f g).coeFn_toLp

theorem norm_rankDiagonal_le (f g : H μ) : ‖rankDiagonal f g‖ ≤ ‖f‖ * ‖g‖ := by
  have h : eLpNorm (fun x ↦ f x * conj (g x)) 1 μ ≤
      eLpNorm (⇑f) 2 μ * eLpNorm (⇑g) 2 μ := by
    have hb : ∀ᵐ x ∂μ, ‖f x * conj (g x)‖₊ ≤ 1 * ‖f x‖₊ * ‖g x‖₊ := by
      filter_upwards with x
      exact_mod_cast (show ‖f x * conj (g x)‖ ≤ (1 : ℝ) * ‖f x‖ * ‖g x‖ by
        rw [norm_mul, Complex.norm_conj, one_mul])
    simpa only [ENNReal.coe_one, one_mul] using
      (eLpNorm_le_eLpNorm_mul_eLpNorm (p := 2) (q := 2) (r := 1)
        (fun z w : ℂ ↦ z * conj w) 1
        (continuous_fst.mul (Complex.continuous_conj.comp continuous_snd))
        (Lp.memLp f).aestronglyMeasurable (Lp.memLp g).aestronglyMeasurable hb)
  rw [Lp.norm_def, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (rankDiagonal_ae f g), ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) (Lp.eLpNorm_ne_top g)) h

/-- The two L² legs of a rank-one diagonal can be regularized independently. -/
theorem norm_rankDiagonal_sub_le (f₁ f₀ g₁ g₀ : H μ) :
    ‖rankDiagonal f₁ g₁ - rankDiagonal f₀ g₀‖ ≤
      ‖f₁-f₀‖ * ‖g₁‖ + ‖f₀‖ * ‖g₁-g₀‖ := by
  have h : rankDiagonal f₁ g₁ - rankDiagonal f₀ g₀ =
      rankDiagonal (f₁-f₀) g₁ + rankDiagonal f₀ (g₁-g₀) := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_sub (rankDiagonal f₁ g₁) (rankDiagonal f₀ g₀),
      Lp.coeFn_add (rankDiagonal (f₁-f₀) g₁) (rankDiagonal f₀ (g₁-g₀)),
      rankDiagonal_ae f₁ g₁, rankDiagonal_ae f₀ g₀,
      rankDiagonal_ae (f₁-f₀) g₁, rankDiagonal_ae f₀ (g₁-g₀),
      Lp.coeFn_sub f₁ f₀, Lp.coeFn_sub g₁ g₀] with x h₁ h₂ h₃ h₄ h₅ h₆ hf hg
    rw [h₁, h₂, Pi.sub_apply, Pi.add_apply, h₃, h₄, h₅, h₆, hf, hg, Pi.sub_apply,
      Pi.sub_apply, map_sub]
    ring
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (norm_rankDiagonal_le _ _) (norm_rankDiagonal_le _ _))

theorem tendsto_rankDiagonal {ι : Type*} {l : Filter ι}
    {f g : ι → H μ} {f₀ g₀ : H μ} (hf : Tendsto f l (𝓝 f₀)) (hg : Tendsto g l (𝓝 g₀)) :
    Tendsto (fun i ↦ rankDiagonal (f i) (g i)) l (𝓝 (rankDiagonal f₀ g₀)) := by
  have h := (((hf.sub_const f₀).norm.mul hg.norm).add
    ((tendsto_const_nhds (x := ‖f₀‖)).mul (hg.sub_const g₀).norm))
  have hz : Tendsto (fun i ↦ ‖f i-f₀‖ * ‖g i‖ + ‖f₀‖ * ‖g i-g₀‖) l (𝓝 0) := by
    simpa using h
  exact tendsto_iff_norm_sub_tendsto_zero.2
    (squeeze_zero (fun _ ↦ norm_nonneg _) (fun _ ↦ norm_rankDiagonal_sub_le _ _ _ _) hz)

theorem integral_rankDiagonal (f g : H μ) : (∫ x, rankDiagonal f g x ∂μ) = inner ℂ g f := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rankDiagonal_ae f g] with x hx
  exact hx.trans (RCLike.inner_apply (g x) (f x)).symm

/-- The Riesz vector of a functional in a nuclear presentation. -/
def dualVector {A : H μ →L[ℂ] H μ} (r : NuclearPresentation A) (n : ℕ) : H μ :=
  (InnerProductSpace.toDual ℂ (H μ)).symm (r.functional n)

private theorem dualVector_inner {A : H μ →L[ℂ] H μ} (r : NuclearPresentation A) (n : ℕ) (x : H μ) :
    inner ℂ (dualVector r n) x = r.functional n x := InnerProductSpace.toDual_symm_apply

private theorem nuclearPresentation_summable_density_cost {A : H μ →L[ℂ] H μ}
    (r : NuclearPresentation A) :
    Summable (fun n ↦ ‖r.coeff n‖ * (‖(r.vector n : H μ)‖ * ‖dualVector r n‖)) := by
  obtain ⟨C, hC₀, hC⟩ :=
    ((NormedSpace.equicontinuous_tfae r.functional).out 1 7).mp r.equicontinuous
  obtain ⟨D, hD⟩ :=
    ((NormedSpace.isVonNBounded_iff ℂ).mp r.isBanachDisc.bounded).exists_norm_le
  refine (r.summable_coeff.mul_right (D * C)).of_nonneg_of_le (fun n ↦ by positivity) ?_
  intro n
  exact mul_le_mul_of_nonneg_left (mul_le_mul (hD _ (r.vector_mem n))
    (by simpa [dualVector] using hC n) (norm_nonneg _) (le_trans (norm_nonneg _) (hD _ (r.vector_mem n))))
    (norm_nonneg _)

/-- The L¹ trace diagonal of a nuclear presentation, defined by an absolutely
convergent rank-one series and not by restricting an a.e. two-variable kernel. -/
def presentationDiagonal {A : H μ →L[ℂ] H μ} (r : NuclearPresentation A) : Lp ℂ 1 μ :=
  ∑' n, r.coeff n • rankDiagonal (r.vector n) (dualVector r n)

theorem presentationDiagonal_summable {A : H μ →L[ℂ] H μ} (r : NuclearPresentation A) :
    Summable (fun n ↦ ‖r.coeff n • rankDiagonal (r.vector n) (dualVector r n)‖) := by
  apply (nuclearPresentation_summable_density_cost r).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
  intro n
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_rankDiagonal_le _ _) (norm_nonneg _)

private theorem presentationDiagonal_ae_sum {A : H μ →L[ℂ] H μ} (r : NuclearPresentation A) :
    ⇑(presentationDiagonal r) =ᵐ[μ]
      fun x ↦ ∑' n, (r.coeff n • rankDiagonal (r.vector n) (dualVector r n)) x := by
  apply Lp.coeFn_tsum
  exact ENNReal.tsum_coe_ne_top_iff_summable.2
    (NNReal.summable_coe.1 (presentationDiagonal_summable r))

theorem presentationDiagonal_ae {A : H μ →L[ℂ] H μ} (r : NuclearPresentation A) :
    ⇑(presentationDiagonal r) =ᵐ[μ]
      fun x ↦ ∑' n, r.coeff n * (r.vector n : H μ) x * conj (dualVector r n x) := by
  have h (n : ℕ) : ⇑(r.coeff n • rankDiagonal (r.vector n) (dualVector r n)) =ᵐ[μ]
      fun x ↦ r.coeff n * (r.vector n : H μ) x * conj (dualVector r n x) := by
    filter_upwards [Lp.coeFn_smul (r.coeff n) (rankDiagonal (r.vector n) (dualVector r n)),
      rankDiagonal_ae (r.vector n) (dualVector r n)] with x hx hy
    rw [hx, Pi.smul_apply, hy, smul_eq_mul, mul_assoc]
  filter_upwards [presentationDiagonal_ae_sum r, ae_all_iff.mpr h] with x hx hrep
  rw [hx]
  exact tsum_congr hrep

/-- The full integral of the concrete integrable diagonal is the repository's
Hilbert trace, with no continuity hypothesis on kernel representatives. -/
theorem integral_presentationDiagonal {A : H μ →L[ℂ] H μ} (r : NuclearPresentation A)
    (hA : IsNuclearOperator A) :
    (∫ x, presentationDiagonal r x ∂μ) = hilbertTrace ⟨A, hA⟩ := by
  rw [hilbertTrace_eq_nuclearTrace]
  let J (n : ℕ) := r.coeff n • rankDiagonal (r.vector n) (dualVector r n)
  have hJ (n : ℕ) : Integrable (J n) μ := (memLp_one_iff_integrable).1 (Lp.memLp (J n))
  have hc : Summable (fun n ↦ ∫ x, ‖J n x‖ ∂μ) := by
    simpa only [← L1.norm_eq_integral_norm] using presentationDiagonal_summable r
  have hs := hasSum_integral_of_summable_integral_norm hJ hc
  have htrace := ((exists_nuclearTrace_hasSum hilbert_approximationProperty A hA).exists.choose_spec r).2
  calc
    _ = ∫ x, ∑' n, J n x ∂μ := integral_congr_ae (presentationDiagonal_ae_sum r)
    _ = _ := hs.unique (htrace.congr_fun fun n ↦ ?_)
  calc
    (∫ x, J n x ∂μ) = ∫ x, r.coeff n • rankDiagonal (r.vector n) (dualVector r n) x ∂μ := by
      apply integral_congr_ae
      exact Lp.coeFn_smul _ _
    _ = _ := by rw [integral_smul, smul_eq_mul, integral_rankDiagonal, dualVector_inner]

private def indicatorVector (s : Set X) (hs : MeasurableSet s) (f : H μ) : H μ :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).toLp (s.indicator f)

private theorem indicatorVector_ae (s : Set X) (hs : MeasurableSet s) (f : H μ) :
    ⇑(indicatorVector s hs f) =ᵐ[μ] s.indicator f :=
  ((Lp.memLp f).indicator hs.nullMeasurableSet).coeFn_toLp

/-- Measurable spatial restriction on the ambient L² representing Hilbert space. -/
def spatialMask (s : Set X) (hs : MeasurableSet s) : H μ →L[ℂ] H μ := by
  let M : H μ →ₗ[ℂ] H μ :=
    { toFun := indicatorVector s hs
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [indicatorVector_ae s hs (f+g), indicatorVector_ae s hs f,
          indicatorVector_ae s hs g, Lp.coeFn_add (indicatorVector s hs f) (indicatorVector s hs g),
          Lp.coeFn_add f g] with x h₁ h₂ h₃ h₄ h₅
        change indicatorVector s hs (f+g) x = (indicatorVector s hs f + indicatorVector s hs g) x
        rw [h₁, h₄, Pi.add_apply, h₂, h₃]
        by_cases hx : x ∈ s
        · rw [Set.indicator_of_mem hx, h₅, Pi.add_apply, Set.indicator_of_mem hx,
            Set.indicator_of_mem hx]
        · simp [hx]
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [indicatorVector_ae s hs (c • f), indicatorVector_ae s hs f,
          Lp.coeFn_smul c (indicatorVector s hs f), Lp.coeFn_smul c f] with x h₁ h₂ h₃ h₄
        change indicatorVector s hs (c • f) x = (c • indicatorVector s hs f) x
        rw [h₁, h₃, Pi.smul_apply, h₂]
        by_cases hx : x ∈ s <;> simp [hx, h₄] }
  refine M.mkContinuous 1 fun f ↦ ?_
  change ‖indicatorVector s hs f‖ ≤ 1 * ‖f‖
  rw [one_mul, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (indicatorVector_ae s hs f)]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
  apply eLpNorm_mono_ae ((Lp.memLp f).aestronglyMeasurable.indicator hs)
  filter_upwards with x
  by_cases hx : x ∈ s <;> simp [hx]

theorem spatialMask_ae (s : Set X) (hs : MeasurableSet s) (f : H μ) :
    ⇑(spatialMask s hs f) =ᵐ[μ] s.indicator f :=
  indicatorVector_ae s hs f

private def precomposePresentation {A : H μ →L[ℂ] H μ} (r : NuclearPresentation A)
    (M : H μ →L[ℂ] H μ) : NuclearPresentation (A.comp M) where
  coeff := r.coeff
  functional n := (r.functional n).comp M
  disc := r.disc
  isBanachDisc := r.isBanachDisc
  vector := r.vector
  vector_mem := r.vector_mem
  summable_coeff := r.summable_coeff
  equicontinuous U hU := by
    have h := (M.continuous.tendsto' 0 0 (map_zero M)).eventually (r.equicontinuous U hU)
    simpa only [ContinuousLinearMap.comp_apply, map_zero] using h
  hasSum x := r.hasSum (M x)

theorem localized_nuclear {A : H μ →L[ℂ] H μ} (hA : IsNuclearOperator A)
    (M : H μ →L[ℂ] H μ) : IsNuclearOperator (A.comp M) := by
  obtain ⟨r⟩ := (isNuclearOperator_iff_nonempty_presentation A).mp hA
  exact (isNuclearOperator_iff_nonempty_presentation _).mpr ⟨precomposePresentation r M⟩

private theorem setIntegral_rankDiagonal (s : Set X) (hs : MeasurableSet s) (f g : H μ) :
    (∫ x in s, rankDiagonal f g x ∂μ) = inner ℂ g (spatialMask s hs f) := by
  rw [← integral_indicator hs, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [rankDiagonal_ae f g, spatialMask_ae s hs f] with x hx hy
  rw [RCLike.inner_apply, hy]
  by_cases hxs : x ∈ s <;> simp [hxs, hx]

/-- Localization of the integrable diagonal gives the trace of the actual
measurable-set cut of the nuclear operator. -/
theorem setIntegral_presentationDiagonal {A : H μ →L[ℂ] H μ} (r : NuclearPresentation A)
    (hA : IsNuclearOperator A) (s : Set X) (hs : MeasurableSet s) :
    (∫ x in s, presentationDiagonal r x ∂μ) =
      hilbertTrace ⟨A.comp (spatialMask s hs), localized_nuclear hA (spatialMask s hs)⟩ := by
  rw [hilbertTrace_eq_nuclearTrace]
  let M : H μ →L[ℂ] H μ := spatialMask s hs
  let r' := precomposePresentation r M
  let J (n : ℕ) := r.coeff n • rankDiagonal (r.vector n) (dualVector r n)
  have hJ (n : ℕ) : Integrable (J n) μ := (memLp_one_iff_integrable).1 (Lp.memLp (J n))
  have hc : Summable (fun n ↦ ∫ x in s, ‖J n x‖ ∂μ) := by
    refine (presentationDiagonal_summable r).of_nonneg_of_le (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg _) ?_
    intro n
    change _ ≤ ‖J n‖
    rw [L1.norm_eq_integral_norm]
    exact setIntegral_le_integral (hJ n).norm (ae_of_all _ fun _ ↦ norm_nonneg _)
  have hsum := hasSum_integral_of_summable_integral_norm (fun n ↦ (hJ n).integrableOn (s := s)) hc
  have htrace := ((exists_nuclearTrace_hasSum hilbert_approximationProperty (A.comp M)
    (localized_nuclear hA M)).exists.choose_spec r').2
  calc
    _ = ∫ x in s, ∑' n, J n x ∂μ := integral_congr_ae (ae_restrict_of_ae (presentationDiagonal_ae_sum r))
    _ = _ := hsum.unique (htrace.congr_fun fun n ↦ ?_)
  calc
    (∫ x in s, J n x ∂μ) = ∫ x in s, r.coeff n • rankDiagonal (r.vector n) (dualVector r n) x ∂μ := by
      apply integral_congr_ae
      exact ae_restrict_of_ae (Lp.coeFn_smul _ _)
    _ = r.coeff n * r.functional n (M (r.vector n)) := by
      rw [integral_smul, smul_eq_mul, setIntegral_rankDiagonal, dualVector_inner]
    _ = _ := rfl

/-- The density is independent of the nuclear presentation as an L¹ vector. -/
theorem presentationDiagonal_eq {A : H μ →L[ℂ] H μ}
    (r r' : NuclearPresentation A) : presentationDiagonal r = presentationDiagonal r' := by
  have hA := (isNuclearOperator_iff_nonempty_presentation A).mpr ⟨r⟩
  have h₁ : Integrable (presentationDiagonal r) μ := (memLp_one_iff_integrable).1 (Lp.memLp _)
  have h₂ : Integrable (presentationDiagonal r') μ := (memLp_one_iff_integrable).1 (Lp.memLp _)
  apply Lp.ext
  apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ h₁ h₂
  intro s hs _
  rw [setIntegral_presentationDiagonal r hA s hs, setIntegral_presentationDiagonal r' hA s hs]

/-- Joint strongly convergent contractive regularizations of the two kernel legs
recover the actual diagonal in L¹, with no continuity assumptions on the original kernel. -/
theorem tendsto_regularizedPresentationDiagonal {A : H μ →L[ℂ] H μ}
    (r : NuclearPresentation A) {ι : Type*} {l : Filter ι} (S T : ι → H μ → H μ)
    (hc : ∀ᶠ i in l, ∀ x, ‖S i x‖ ≤ ‖x‖ ∧ ‖T i x‖ ≤ ‖x‖)
    (hS : ∀ x, Tendsto (fun i ↦ S i x) l (𝓝 x))
    (hT : ∀ x, Tendsto (fun i ↦ T i x) l (𝓝 x)) :
    Tendsto (fun i ↦ ∑' n, r.coeff n • rankDiagonal (S i (r.vector n)) (T i (dualVector r n)))
      l (𝓝 (presentationDiagonal r)) := by
  apply tendsto_tsum_of_dominated_convergence (nuclearPresentation_summable_density_cost r)
  · intro n
    exact tendsto_const_nhds.smul (tendsto_rankDiagonal (hS _) (hT _))
  · filter_upwards [hc] with i hi n
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (norm_rankDiagonal_le _ _).trans
      (mul_le_mul (hi _).1 (hi _).2 (norm_nonneg _) (norm_nonneg _))

end RiemannMasullo.QuotientDiagonal
