module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Convolution
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Haar.Unique
import RiemannMasullo.External.FermatDixmierMalliavin.OneParameter
import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Angle
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# The Dixmier–Malliavin factorization on the real line and on `ι → ℝ`

Every smooth compactly supported function `ℝ → ℂ` is a sum of two convolutions of smooth
compactly supported functions (J. Dixmier, P. Malliavin, *Factorisations de fonctions et de
vecteurs indéfiniment différentiables*, Bull. Sci. Math. (2) 102 (1978), 307–330,
Théorème 3.1, in dimension one).

The analytic input is the vendored one-parameter factorization
`DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add`, applied in the algebra `ℝ`
along the flow `x ↦ x * exp t`. The logarithm carries that flow to translation.
-/

@[expose] public noncomputable section

open Filter Function Set MeasureTheory
open scoped ContDiff Topology

namespace RiemannMasullo

/-- Extend a real test to the positive half-line through the logarithm. Its support lies
in the exponential image of the original support, so the zero extension is smooth at zero. -/
private theorem dixmierMalliavin_real_log (f : ℝ → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ Φ : ℝ → ℂ, ContDiff ℝ ∞ Φ ∧ tsupport Φ ⊆ Real.exp '' tsupport f ∧
      ∀ s, Φ (Real.exp s) = f s := by
  let Φ (y : ℝ) := if 0 < y then f (Real.log y) else 0
  have hK := hc.isCompact.image Real.continuous_exp
  have hs : tsupport Φ ⊆ Real.exp '' tsupport f := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_cases h : 0 < y
    · exact ⟨Real.log y, subset_tsupport f (by simpa [Φ, h, mem_support] using hy), Real.exp_log h⟩
    · exact ((mem_support.mp hy) (ite_eq_right h)).elim
  refine ⟨Φ, contDiff_iff_contDiffAt.mpr fun y ↦ ?_, hs, fun s ↦ by simp [Φ, Real.exp_pos]⟩
  by_cases h : 0 < y
  · apply (hf.contDiffAt.comp y (Real.contDiffAt_log.mpr h.ne')).congr_of_eventuallyEq
    filter_upwards [lt_mem_nhds h] with z hz using ite_eq_left hz
  · have hy : y ∉ tsupport Φ := fun hy ↦ by
      obtain ⟨s, _, rfl⟩ := hs hy
      exact h (Real.exp_pos s)
    exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)

/-- A translation integral `s ↦ ∫ φ t * g (s + t)` is the convolution of the reflected kernel
with `g`. -/
private theorem dixmierMalliavin_real_term (φ g : ℝ → ℂ) :
    (fun s : ℝ ↦ ∫ t, φ t * g (s + t)) =
      MeasureTheory.convolution (fun t ↦ φ (-t)) g (ContinuousLinearMap.mul ℝ ℂ) volume := by
  funext s
  change _ = ∫ t : ℝ, φ (-t) * g (s - t)
  simpa only [sub_eq_add_neg] using
    (integral_neg_eq_self (fun t : ℝ ↦ φ t * g (s + t)) volume).symm

/-- Dixmier–Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), 307–330, Théorème 3.1, on the real line.
Every smooth compactly supported function `f : ℝ → ℂ` is a sum of two convolutions
`u₁ ⋆ v₁ + u₂ ⋆ v₂` of smooth compactly supported functions, for Lebesgue measure. The
second summand has `v₂ = f`. -/
theorem dixmierMalliavin_real_two_terms (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    ∃ u₁ v₁ u₂ : ℝ → ℂ, ContDiff ℝ ∞ u₁ ∧ HasCompactSupport u₁ ∧
      ContDiff ℝ ∞ v₁ ∧ HasCompactSupport v₁ ∧ ContDiff ℝ ∞ u₂ ∧ HasCompactSupport u₂ ∧
      f = MeasureTheory.convolution u₁ v₁ (ContinuousLinearMap.mul ℝ ℂ) volume +
        MeasureTheory.convolution u₂ f (ContinuousLinearMap.mul ℝ ℂ) volume := by
  obtain ⟨Φ, hΦ, hΦs, hΦexp⟩ := dixmierMalliavin_real_log f hf hfc
  have hΦc : HasCompactSupport Φ :=
    (hfc.isCompact.image Real.continuous_exp).of_isClosed_subset (isClosed_tsupport _) hΦs
  obtain ⟨Φ₁, φ, ψ, h₁, hs₁, hφ, hψ, hsφ, hsψ, heq⟩ :=
    DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add (1 : ℝ) 1 zero_lt_one Φ hΦ hΦc
  have hc₁ : HasCompactSupport (Φ₁ ∘ Real.exp) := by
    apply HasCompactSupport.intro hfc
    intro s hs
    change Φ₁ (Real.exp s) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro h
    obtain ⟨r, hr, he⟩ := hΦs (hs₁ h)
    exact hs (Real.exp_injective he ▸ hr)
  have hcφ : HasCompactSupport φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ
  have hcψ : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsψ
  refine ⟨fun t ↦ φ (-t), Φ₁ ∘ Real.exp, fun t ↦ ψ (-t), hφ.comp contDiff_neg,
    hcφ.comp_homeomorph (Homeomorph.neg ℝ), h₁.comp Real.contDiff_exp, hc₁,
    hψ.comp contDiff_neg, hcψ.comp_homeomorph (Homeomorph.neg ℝ), ?_⟩
  rw [← dixmierMalliavin_real_term φ (Φ₁ ∘ Real.exp), ← dixmierMalliavin_real_term ψ f]
  funext s
  simpa only [smul_eq_mul, mul_one, ← Real.exp_eq_exp_ℝ, ← Real.exp_add, hΦexp, comp_apply,
    Pi.add_apply] using heq (Real.exp s)

/-- Dixmier–Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), 307–330, Théorème 3.1, on the real line.
Every smooth compactly supported function `f : ℝ → ℂ` lies in the additive closure of the
convolutions of two smooth compactly supported functions, for Lebesgue measure. -/
theorem dixmierMalliavin_real (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    f ∈ AddSubmonoid.closure {θ : ℝ → ℂ | ∃ u v : ℝ → ℂ, ContDiff ℝ ∞ u ∧ HasCompactSupport u ∧
      ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧
      θ = MeasureTheory.convolution u v (ContinuousLinearMap.mul ℝ ℂ) volume} := by
  obtain ⟨u₁, v₁, u₂, hu₁, hcu₁, hv₁, hcv₁, hu₂, hcu₂, h⟩ :=
    dixmierMalliavin_real_two_terms f hf hfc
  rw [h]
  exact add_mem (AddSubmonoid.subset_closure ⟨u₁, v₁, hu₁, hcu₁, hv₁, hcv₁, rfl⟩)
    (AddSubmonoid.subset_closure ⟨u₂, f, hu₂, hcu₂, hf, hfc, rfl⟩)

section Pi

variable {ι : Type*} [Fintype ι]

/-- Extend a test function on `ι → ℝ` to the positive orthant through the coordinatewise
logarithm, by zero elsewhere. The extension is smooth with support in the exponential image. -/
private theorem dixmierMalliavin_pi_log (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    ∃ Φ : (ι → ℝ) → ℂ, ContDiff ℝ ∞ Φ ∧
      tsupport Φ ⊆ (fun s : ι → ℝ ↦ fun j ↦ Real.exp (s j)) '' tsupport f ∧
      ∀ s : ι → ℝ, Φ (fun j ↦ Real.exp (s j)) = f s := by
  classical
  let E (s : ι → ℝ) : ι → ℝ := fun j ↦ Real.exp (s j)
  have hE : Continuous E := continuous_pi fun j ↦ Real.continuous_exp.comp (continuous_apply j)
  let Φ (y : ι → ℝ) := if ∀ j, 0 < y j then f (fun j ↦ Real.log (y j)) else 0
  have hK := hc.isCompact.image hE
  have hs : tsupport Φ ⊆ E '' tsupport f := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_cases h : ∀ j, 0 < y j
    · exact ⟨fun j ↦ Real.log (y j), subset_tsupport f (by simpa [Φ, h, mem_support] using hy),
        funext fun j ↦ Real.exp_log (h j)⟩
    · exact ((mem_support.mp hy) (ite_eq_right h)).elim
  refine ⟨Φ, contDiff_iff_contDiffAt.mpr fun y ↦ ?_, hs, fun s ↦ ?_⟩
  · by_cases h : ∀ j, 0 < y j
    · have hlog : ContDiffAt ℝ ∞ (fun z : ι → ℝ ↦ fun j ↦ Real.log (z j)) y :=
        contDiffAt_pi.mpr fun j ↦
          (Real.contDiffAt_log.mpr (h j).ne').comp y (contDiffAt_pi.mp contDiffAt_id j)
      apply (hf.contDiffAt.comp y hlog).congr_of_eventuallyEq
      have ho : IsOpen {z : ι → ℝ | ∀ j, 0 < z j} := by
        simp only [ofPred_forall]
        exact isOpen_iInter_of_finite fun j ↦ isOpen_lt continuous_const (continuous_apply j)
      filter_upwards [ho.mem_nhds h] with z hz using ite_eq_left hz
    · have hy : y ∉ tsupport Φ := fun hy ↦ by
        obtain ⟨s, _, rfl⟩ := hs hy
        exact h fun j ↦ Real.exp_pos (s j)
      exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
  · have h : ∀ j, 0 < Real.exp (s j) := fun j ↦ Real.exp_pos _
    simp [Φ, h]

/-- Dixmier–Malliavin along one coordinate of `ι → ℝ`. Every smooth compactly supported
`f : (ι → ℝ) → ℂ` is `f = φ ⋆ᵢ f₁ + ψ ⋆ᵢ f`, where `⋆ᵢ` integrates along the `i`-th
coordinate line against a one-variable test function, `f₁` is smooth with support inside the
support of `f`, and the one-variable kernels `φ`, `ψ` are smooth with support in `[-ε, ε]`. -/
theorem dixmierMalliavin_pi_direction [DecidableEq ι] (i : ι) (ε : ℝ) (hε : 0 < ε)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f) :
    ∃ (f₁ : (ι → ℝ) → ℂ) (φ ψ : ℝ → ℂ), ContDiff ℝ ∞ f₁ ∧ tsupport f₁ ⊆ tsupport f ∧
      ContDiff ℝ ∞ φ ∧ ContDiff ℝ ∞ ψ ∧ tsupport φ ⊆ Icc (-ε) ε ∧ tsupport ψ ⊆ Icc (-ε) ε ∧
      ∀ s : ι → ℝ, f s = (∫ t : ℝ, φ t * f₁ (s + t • Pi.single i (1 : ℝ))) +
        ∫ t : ℝ, ψ t * f (s + t • Pi.single i (1 : ℝ)) := by
  let E (s : ι → ℝ) : ι → ℝ := fun j ↦ Real.exp (s j)
  have hE : ContDiff ℝ ∞ E := contDiff_pi.mpr fun j ↦ Real.contDiff_exp.comp (contDiff_pi.mp contDiff_id j)
  have hEi : Injective E := fun s t h ↦ funext fun j ↦ Real.exp_injective (congrFun h j)
  obtain ⟨Φ, hΦ, hΦs, hΦexp⟩ := dixmierMalliavin_pi_log f hf hfc
  have hΦc : HasCompactSupport Φ :=
    (hfc.isCompact.image hE.continuous).of_isClosed_subset (isClosed_tsupport _) hΦs
  obtain ⟨Φ₁, φ, ψ, h₁, hs₁, hφ, hψ, hsφ, hsψ, heq⟩ :=
    DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add
      (Pi.single i (1 : ℝ) : ι → ℝ) ε hε Φ hΦ hΦc
  have hflow (s : ι → ℝ) (t : ℝ) :
      E s * NormedSpace.exp (t • (Pi.single i (1 : ℝ) : ι → ℝ)) = E (s + t • Pi.single i 1) := by
    funext j
    simp only [E, Pi.mul_apply, Pi.coe_exp, Pi.add_apply, Pi.smul_apply, Real.exp_add,
      ← Real.exp_eq_exp_ℝ]
  refine ⟨Φ₁ ∘ E, φ, ψ, h₁.comp hE, ?_, hφ, hψ, hsφ, hsψ, fun s ↦ ?_⟩
  · intro s hs
    obtain ⟨r, hr, he⟩ := hΦs (hs₁ (tsupport_comp_subset_preimage Φ₁ hE.continuous hs))
    exact hEi he ▸ hr
  · have h := heq (E s)
    simp only [hflow] at h
    rw [show Φ (E s) = f s from hΦexp s] at h
    rw [h]
    congr 2
    funext t
    rw [show Φ (E (s + t • Pi.single i 1)) = _ from hΦexp _]

end Pi

section PiFull

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lebesgue measure in the coordinates of `S` and the point mass at zero in the others. -/
private def dmCoordMeasure (S : Finset ι) (i : ι) : Measure ℝ :=
  if i ∈ S then volume else Measure.dirac 0

private instance dmCoordMeasure_sigmaFinite (S : Finset ι) (i : ι) :
    SigmaFinite (dmCoordMeasure S i) := by
  unfold dmCoordMeasure
  split_ifs <;> infer_instance

private instance dmCoordMeasure_finiteOnCompacts (S : Finset ι) (i : ι) :
    IsFiniteMeasureOnCompacts (dmCoordMeasure S i) := by
  unfold dmCoordMeasure
  split_ifs <;> infer_instance

private instance dmCoordMeasure_probability (i : ι) :
    IsProbabilityMeasure (dmCoordMeasure (∅ : Finset ι) i) := by
  simp only [dmCoordMeasure, Finset.notMem_empty, ite_false]
  infer_instance

/-- A coordinate outside `S` vanishes almost everywhere for the partial measure. -/
private theorem dmCoordMeasure_ae_zero (S : Finset ι) (i : ι) (hi : i ∉ S) :
    ∀ᵐ w ∂Measure.pi (dmCoordMeasure S), w i = 0 := by
  have h : ∀ᵐ x ∂dmCoordMeasure S i, x = 0 := by
    rw [dmCoordMeasure, ite_eq_right hi, ae_dirac_eq]
    exact rfl
  exact Measure.tendsto_eval_ae_ae.eventually h

/-- Adding the coordinate `i` to `S` replaces the point mass by Lebesgue measure there. -/
private theorem dmCoordMeasure_map_update (S : Finset ι) (i : ι) (hi : i ∉ S) :
    Measure.map (fun p : (ι → ℝ) × ℝ ↦ update p.1 i p.2)
      ((Measure.pi (dmCoordMeasure S)).prod volume) = Measure.pi (dmCoordMeasure (insert i S)) := by
  symm
  apply Measure.pi_eq
  intro B hB
  have hm : Measurable (fun p : (ι → ℝ) × ℝ ↦ update p.1 i p.2) :=
    (continuous_fst.update i continuous_snd).measurable
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hB)]
  have hpre : (fun p : (ι → ℝ) × ℝ ↦ update p.1 i p.2) ⁻¹' (Set.pi univ B) =
      (Set.pi univ (update B i univ)) ×ˢ (B i) := by
    ext ⟨w, t⟩
    simp only [mem_preimage, Set.mem_pi, mem_univ, true_imp_iff, mem_prod]
    constructor
    · intro h
      refine ⟨fun j ↦ ?_, by simpa using h i⟩
      by_cases hj : j = i
      · subst hj
        simp
      · simpa [Function.update_apply, hj] using h j
    · rintro ⟨h1, h2⟩ j
      by_cases hj : j = i
      · subst hj
        simpa using h2
      · simpa [Function.update_apply, hj] using h1 j
  rw [hpre, Measure.prod_prod, Measure.pi_pi,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i),
    ← Finset.mul_prod_erase Finset.univ (fun j ↦ dmCoordMeasure (insert i S) j (B j))
      (Finset.mem_univ i)]
  have h1 : dmCoordMeasure S i (update B i univ i) = 1 := by simp [dmCoordMeasure, hi]
  have h2 : dmCoordMeasure (insert i S) i (B i) = volume (B i) := by simp [dmCoordMeasure]
  have h3 : ∀ j ∈ Finset.univ.erase i,
      dmCoordMeasure S j (update B i univ j) = dmCoordMeasure (insert i S) j (B j) := by
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [dmCoordMeasure, Finset.mem_insert, hji]
  rw [h1, h2, Finset.prod_congr rfl h3, one_mul, mul_comm]

/-- Smoothing along the coordinate `i ∉ S` after smoothing along the coordinates of `S`
is smoothing along the coordinates of `insert i S` with the product kernel. -/
private theorem dmCoordMeasure_integral_step (S : Finset ι) (i : ι) (hi : i ∉ S)
    (Φ : (ι → ℝ) → ℂ) (φ : ℝ → ℂ) (H : (ι → ℝ) → ℂ) (hΦ : Continuous Φ)
    (hΦc : HasCompactSupport Φ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hH : Continuous H) (s : ι → ℝ) :
    Integrable (fun w ↦ Φ w * ∫ t, φ t * H (s + w + t • Pi.single i (1 : ℝ)))
        (Measure.pi (dmCoordMeasure S)) ∧
      ∫ w, Φ w * (∫ t, φ t * H (s + w + t • Pi.single i (1 : ℝ))) ∂Measure.pi (dmCoordMeasure S) =
        ∫ w, (φ (w i) * Φ (update w i 0)) * H (s + w) ∂Measure.pi (dmCoordMeasure (insert i S)) := by
  let m : (ι → ℝ) × ℝ → (ι → ℝ) := fun p ↦ update p.1 i p.2
  have hm : Continuous m := continuous_fst.update i continuous_snd
  let g : (ι → ℝ) × ℝ → ℂ := fun p ↦ Φ p.1 * (φ p.2 * H (s + p.1 + p.2 • Pi.single i (1 : ℝ)))
  have hg : Continuous g := (hΦ.comp continuous_fst).mul ((hφ.comp continuous_snd).mul
    (hH.comp ((continuous_const.add continuous_fst).add (continuous_snd.smul continuous_const))))
  have hgc : HasCompactSupport g := by
    apply HasCompactSupport.intro (hΦc.isCompact.prod hφc.isCompact)
    intro p hp
    simp only [mem_prod, not_and_or] at hp
    rcases hp with hp | hp
    · simp [g, image_eq_zero_of_notMem_tsupport hp]
    · simp [g, image_eq_zero_of_notMem_tsupport hp]
  have hgi : Integrable g ((Measure.pi (dmCoordMeasure S)).prod volume) :=
    hg.integrable_of_hasCompactSupport hgc
  have he (w : ι → ℝ) : ∫ t, g (w, t) =
      Φ w * ∫ t, φ t * H (s + w + t • Pi.single i (1 : ℝ)) := by
    simp only [g]
    rw [integral_const_mul]
  have hI : Integrable (fun w ↦ Φ w * ∫ t, φ t * H (s + w + t • Pi.single i (1 : ℝ)))
      (Measure.pi (dmCoordMeasure S)) := by
    have h : Integrable (fun w ↦ ∫ t, g (w, t)) (Measure.pi (dmCoordMeasure S)) :=
      hgi.integral_prod_left
    simpa only [he] using h
  refine ⟨hI, ?_⟩
  have hk : Continuous (fun w : ι → ℝ ↦ (φ (w i) * Φ (update w i 0)) * H (s + w)) :=
    ((hφ.comp (continuous_apply i)).mul (hΦ.comp (continuous_id.update i continuous_const))).mul
      (hH.comp (continuous_const.add continuous_id))
  have hae : (fun p ↦ (φ (m p i) * Φ (update (m p) i 0)) * H (s + m p))
      =ᵐ[(Measure.pi (dmCoordMeasure S)).prod volume] g := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (dmCoordMeasure_ae_zero S i hi)]
      with p hp
    have h1 : m p i = p.2 := by simp [m]
    have h2 : update (m p) i 0 = p.1 := by
      simp only [m, update_idem]
      rw [← hp]
      exact update_eq_self i p.1
    have h3 : s + m p = s + p.1 + p.2 • Pi.single i (1 : ℝ) := by
      rw [add_assoc]
      congr 1
      funext j
      by_cases hj : j = i
      · subst hj
        simp [m, hp]
      · simp [m, hj]
    rw [h1, h2, h3]
    simp only [g]
    ring
  rw [← dmCoordMeasure_map_update S i hi,
    integral_map hm.measurable.aemeasurable hk.aestronglyMeasurable, integral_congr_ae hae,
    integral_prod g hgi]
  simp only [he]

/-- The product of a one-variable test function in the coordinate `i` with the restriction
of a test function to the hyperplane where that coordinate vanishes is a test function. -/
private theorem dmCoordMeasure_kernel (i : ι) (Φ : (ι → ℝ) → ℂ) (φ : ℝ → ℂ)
    (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (fun w : ι → ℝ ↦ φ (w i) * Φ (update w i 0)) ∧
      HasCompactSupport (fun w : ι → ℝ ↦ φ (w i) * Φ (update w i 0)) := by
  constructor
  · have hu : ContDiff ℝ ∞ (fun w : ι → ℝ ↦ update w i 0) := by
      apply contDiff_pi.mpr
      intro j
      by_cases hj : j = i
      · subst hj
        simpa using contDiff_const
      · simpa [Function.update_apply, hj] using (contDiff_pi (𝕜 := ℝ)).mp contDiff_id j
    exact (hφ.comp ((contDiff_pi (𝕜 := ℝ)).mp contDiff_id i)).mul (hΦ.comp hu)
  · have hK := (hΦc.isCompact.prod hφc.isCompact).image
      (f := fun p : (ι → ℝ) × ℝ ↦ update p.1 i p.2) (continuous_fst.update i continuous_snd)
    apply HasCompactSupport.intro hK
    intro w hw
    by_contra h
    simp only [mul_eq_zero, not_or] at h
    exact hw ⟨(update w i 0, w i), ⟨subset_tsupport _ h.2, subset_tsupport _ h.1⟩, by simp⟩

/-- Induction over the set of coordinates along which the kernel smooths. -/
private theorem dixmierMalliavin_pi_action_partial {X : Type*} (𝒜 : Set (X → ℂ))
    (τ : (ι → ℝ) → X → X) (h0 : ∀ x, τ 0 x = x)
    (hτ : ∀ (w : ι → ℝ) (i : ι) (t : ℝ) (x : X),
      τ (w + t • Pi.single i (1 : ℝ)) x = τ (t • Pi.single i (1 : ℝ)) (τ w x))
    (hc : ∀ h ∈ 𝒜, ∀ x, Continuous fun w ↦ h (τ w x))
    (hdir : ∀ h ∈ 𝒜, ∀ i : ι, h ∈ AddSubmonoid.closure {θ : X → ℂ | ∃ φ : ℝ → ℂ, ∃ h₁ ∈ 𝒜,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      θ = fun x ↦ ∫ t, φ t * h₁ (τ (t • Pi.single i (1 : ℝ)) x)})
    (S : Finset ι) (f : X → ℂ) (hf : f ∈ 𝒜) :
    f ∈ AddSubmonoid.closure {θ : X → ℂ | ∃ Φ : (ι → ℝ) → ℂ, ∃ h ∈ 𝒜, ContDiff ℝ ∞ Φ ∧
      HasCompactSupport Φ ∧
      θ = fun x ↦ ∫ w, Φ w * h (τ w x) ∂Measure.pi (dmCoordMeasure S)} := by
  induction S using Finset.induction_on generalizing f with
  | empty =>
    apply AddSubmonoid.subset_closure
    let b : ContDiffBump (0 : ι → ℝ) := default
    refine ⟨fun w ↦ (b w : ℂ), f, hf, Complex.ofRealCLM.contDiff.comp b.contDiff,
      b.hasCompactSupport.comp_left Complex.ofReal_zero, funext fun x ↦ ?_⟩
    have hz : ∀ᵐ w ∂Measure.pi (dmCoordMeasure (∅ : Finset ι)), w = 0 := by
      have h := ae_all_iff.mpr fun i ↦
        dmCoordMeasure_ae_zero (∅ : Finset ι) i (Finset.notMem_empty i)
      filter_upwards [h] with w hw using funext hw
    have hb : b 0 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    rw [integral_congr_ae (g := fun _ ↦ f x) (by
      filter_upwards [hz] with w hw
      simp [hw, hb, h0])]
    simp
  | insert i S hi ih =>
    let T := AddSubmonoid.closure {θ : X → ℂ | ∃ Φ : (ι → ℝ) → ℂ, ∃ h ∈ 𝒜, ContDiff ℝ ∞ Φ ∧
      HasCompactSupport Φ ∧
      θ = fun x ↦ ∫ w, Φ w * h (τ w x) ∂Measure.pi (dmCoordMeasure (insert i S))}
    refine AddSubmonoid.closure_induction (motive := fun θ _ ↦ θ ∈ T)
      ?_ (zero_mem _) (fun _ _ _ _ ha hb ↦ add_mem ha hb) (ih f hf)
    rintro θ ⟨Φ, h, hh, hΦ, hΦc, rfl⟩
    have main : (∀ x, Integrable (fun w ↦ Φ w * h (τ w x)) (Measure.pi (dmCoordMeasure S))) ∧
        (fun x ↦ ∫ w, Φ w * h (τ w x) ∂Measure.pi (dmCoordMeasure S)) ∈ T := by
      refine AddSubmonoid.closure_induction (motive := fun ξ _ ↦
        (∀ x, Integrable (fun w ↦ Φ w * ξ (τ w x)) (Measure.pi (dmCoordMeasure S))) ∧
          (fun x ↦ ∫ w, Φ w * ξ (τ w x) ∂Measure.pi (dmCoordMeasure S)) ∈ T) ?_ ?_ ?_ (hdir h hh i)
      · rintro ξ ⟨φ, h₁, hh₁, hφ, hφc, rfl⟩
        have step (x : X) := dmCoordMeasure_integral_step S i hi Φ φ (fun w ↦ h₁ (τ w x))
          hΦ.continuous hΦc hφ.continuous hφc (hc h₁ hh₁ x) 0
        simp only [zero_add, hτ] at step
        refine ⟨fun x ↦ (step x).1, ?_⟩
        obtain ⟨k, kc⟩ := dmCoordMeasure_kernel i Φ φ hΦ hΦc hφ hφc
        exact AddSubmonoid.subset_closure ⟨_, h₁, hh₁, k, kc, funext fun x ↦ (step x).2⟩
      · refine ⟨fun x ↦ by simp, ?_⟩
        have : (fun x ↦ ∫ w, Φ w * (0 : X → ℂ) (τ w x) ∂Measure.pi (dmCoordMeasure S)) = 0 := by
          funext x
          simp
        rw [this]
        exact zero_mem _
      · rintro ξ η _ _ ⟨hξ, hξT⟩ ⟨hη, hηT⟩
        refine ⟨fun x ↦ ?_, ?_⟩
        · have h := (hξ x).add (hη x)
          simp only [Pi.add_apply, mul_add]
          exact h
        · have : (fun x ↦ ∫ w, Φ w * (ξ + η) (τ w x) ∂Measure.pi (dmCoordMeasure S)) =
              (fun x ↦ ∫ w, Φ w * ξ (τ w x) ∂Measure.pi (dmCoordMeasure S)) +
              (fun x ↦ ∫ w, Φ w * η (τ w x) ∂Measure.pi (dmCoordMeasure S)) := by
            funext x
            simp only [Pi.add_apply, mul_add]
            exact integral_add (hξ x) (hη x)
          rw [this]
          exact add_mem hξT hηT
    exact main.2

/-- Dixmier–Malliavin for an action of `ι → ℝ`. Let `τ` be an action of `ι → ℝ` on a set
`X` and `𝒜` a set of functions on `X` that are continuous along orbits. If each `h ∈ 𝒜`
is, for each coordinate `i`, a finite sum of functions
`x ↦ ∫ t, φ t * h₁ (τ (t • eᵢ) x)` with `φ` a test function on `ℝ` and `h₁ ∈ 𝒜`, then each
`f ∈ 𝒜` is a finite sum of functions `x ↦ ∫ w, Φ w * h (τ w x)` with `Φ` a test function
on `ι → ℝ` and `h ∈ 𝒜`, for Lebesgue measure. -/
theorem dixmierMalliavin_pi_action {X : Type*} (𝒜 : Set (X → ℂ))
    (τ : (ι → ℝ) → X → X) (h0 : ∀ x, τ 0 x = x)
    (hτ : ∀ (w : ι → ℝ) (i : ι) (t : ℝ) (x : X),
      τ (w + t • Pi.single i (1 : ℝ)) x = τ (t • Pi.single i (1 : ℝ)) (τ w x))
    (hc : ∀ h ∈ 𝒜, ∀ x, Continuous fun w ↦ h (τ w x))
    (hdir : ∀ h ∈ 𝒜, ∀ i : ι, h ∈ AddSubmonoid.closure {θ : X → ℂ | ∃ φ : ℝ → ℂ, ∃ h₁ ∈ 𝒜,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧
      θ = fun x ↦ ∫ t, φ t * h₁ (τ (t • Pi.single i (1 : ℝ)) x)})
    (f : X → ℂ) (hf : f ∈ 𝒜) :
    f ∈ AddSubmonoid.closure {θ : X → ℂ | ∃ Φ : (ι → ℝ) → ℂ, ∃ h ∈ 𝒜, ContDiff ℝ ∞ Φ ∧
      HasCompactSupport Φ ∧ θ = fun x ↦ ∫ w, Φ w * h (τ w x)} := by
  have h := dixmierMalliavin_pi_action_partial 𝒜 τ h0 hτ hc hdir Finset.univ f hf
  have hm : Measure.pi (dmCoordMeasure (Finset.univ : Finset ι)) = volume := by
    rw [volume_pi]
    congr 1
    funext i
    simp [dmCoordMeasure]
  rwa [hm] at h

/-- Dixmier–Malliavin, *Factorisations de fonctions et de vecteurs indéfiniment
différentiables*, Bull. Sci. Math. (2) 102 (1978), 307–330, Théorème 3.1, on `ι → ℝ`.
Every smooth compactly supported `f : (ι → ℝ) → ℂ` is a finite sum of functions
`s ↦ ∫ w, Φ w * H (s + w)` with `Φ` and `H` smooth of compact support, for Lebesgue measure. -/
theorem dixmierMalliavin_pi (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) :
    f ∈ AddSubmonoid.closure {θ : (ι → ℝ) → ℂ | ∃ Φ H : (ι → ℝ) → ℂ, ContDiff ℝ ∞ Φ ∧
      HasCompactSupport Φ ∧ ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧
      θ = fun s ↦ ∫ w, Φ w * H (s + w)} := by
  let 𝒜 : Set ((ι → ℝ) → ℂ) := {H | ContDiff ℝ ∞ H ∧ HasCompactSupport H}
  have h := dixmierMalliavin_pi_action 𝒜 (fun w s ↦ s + w) (fun s ↦ add_zero s)
    (fun w i t s ↦ (add_assoc s w _).symm)
    (fun H hH s ↦ hH.1.continuous.comp (continuous_const.add continuous_id))
    (fun H hH i ↦ by
      obtain ⟨H₁, φ, ψ, hH₁, hsH₁, hφ, hψ, hsφ, hsψ, heq⟩ :=
        dixmierMalliavin_pi_direction i 1 one_pos H hH.1 hH.2
      have hφc : HasCompactSupport φ :=
        isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ
      have hψc : HasCompactSupport ψ :=
        isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsψ
      have hH₁c : HasCompactSupport H₁ := hH.2.of_isClosed_subset (isClosed_tsupport _) hsH₁
      rw [show H = (fun s ↦ ∫ t, φ t * H₁ (s + t • Pi.single i (1 : ℝ))) +
        (fun s ↦ ∫ t, ψ t * H (s + t • Pi.single i (1 : ℝ))) from funext heq]
      exact add_mem (AddSubmonoid.subset_closure ⟨φ, H₁, ⟨hH₁, hH₁c⟩, hφ, hφc, rfl⟩)
        (AddSubmonoid.subset_closure ⟨ψ, H, hH, hψ, hψc, rfl⟩)) f ⟨hf, hfc⟩
  refine AddSubmonoid.closure_mono ?_ h
  rintro θ ⟨Φ, H, hH, hΦ, hΦc, rfl⟩
  exact ⟨Φ, H, hΦ, hΦc, hH.1, hH.2, rfl⟩

end PiFull

section Module

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-- Dixmier–Malliavin for an action of a finite-dimensional real vector space `W` with Haar
measure `μ`. Let `τ` be an action of `W` on a set `X` and `𝒜` a set of functions on `X` that
are continuous along orbits. If each `h ∈ 𝒜` is, for each vector `v`, a finite sum of
functions `x ↦ ∫ t, φ t * h₁ (τ (t • v) x)` with `φ` a test function on `ℝ` and `h₁ ∈ 𝒜`,
then each `f ∈ 𝒜` is a finite sum of functions `x ↦ ∫ w, Φ w * h (τ w x) ∂μ` with `Φ` a
test function on `W` and `h ∈ 𝒜`. -/
theorem dixmierMalliavin_action (μ : Measure W) [μ.IsAddHaarMeasure] {X : Type*}
    (𝒜 : Set (X → ℂ)) (τ : W → X → X) (h0 : ∀ x, τ 0 x = x)
    (hτ : ∀ (w w' : W) (x : X), τ (w + w') x = τ w' (τ w x))
    (hc : ∀ h ∈ 𝒜, ∀ x, Continuous fun w ↦ h (τ w x))
    (hdir : ∀ h ∈ 𝒜, ∀ v : W, h ∈ AddSubmonoid.closure {θ : X → ℂ | ∃ φ : ℝ → ℂ, ∃ h₁ ∈ 𝒜,
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ θ = fun x ↦ ∫ t, φ t * h₁ (τ (t • v) x)})
    (f : X → ℂ) (hf : f ∈ 𝒜) :
    f ∈ AddSubmonoid.closure {θ : X → ℂ | ∃ Φ : W → ℂ, ∃ h ∈ 𝒜, ContDiff ℝ ∞ Φ ∧
      HasCompactSupport Φ ∧ θ = fun x ↦ ∫ w, Φ w * h (τ w x) ∂μ} := by
  classical
  let L : (Fin (Module.finrank ℝ W) → ℝ) ≃L[ℝ] W :=
    (Module.finBasis ℝ W).equivFun.symm.toContinuousLinearEquiv
  have : SecondCountableTopology W := L.symm.toHomeomorph.secondCountableTopology
  have key := dixmierMalliavin_pi_action 𝒜 (fun w x ↦ τ (L w) x)
    (fun x ↦ by simp [h0]) (fun w i t x ↦ by simp only [map_add, hτ])
    (fun h hh x ↦ (hc h hh x).comp L.continuous)
    (fun h hh i ↦ by
      refine AddSubmonoid.closure_mono ?_ (hdir h hh (L (Pi.single i (1 : ℝ))))
      rintro θ ⟨φ, h₁, hh₁, hφ, hφc, rfl⟩
      refine ⟨φ, h₁, hh₁, hφ, hφc, funext fun x ↦ ?_⟩
      simp only [map_smul])
    f hf
  let μ' : Measure W := Measure.map L volume
  have hμ'h : μ'.IsAddHaarMeasure := L.isAddHaarMeasure_map volume
  let c := Measure.addHaarScalarFactor μ' μ
  have hμ' : μ' = c • μ := Measure.isAddLeftInvariant_eq_smul μ' μ
  refine AddSubmonoid.closure_mono ?_ key
  rintro θ ⟨Φ, h, hh, hΦ, hΦc, rfl⟩
  refine ⟨fun v ↦ ((c : ℝ) : ℂ) * Φ (L.symm v), h, hh,
    contDiff_const.mul (hΦ.comp L.symm.contDiff),
    (hΦc.comp_homeomorph L.symm.toHomeomorph).mul_left, funext fun x ↦ ?_⟩
  have e1 : ∫ w, Φ w * h (τ (L w) x) = ∫ v, Φ (L.symm v) * h (τ v x) ∂μ' := by
    change _ = ∫ v, Φ (L.symm v) * h (τ v x)
      ∂(Measure.map L.toHomeomorph.toMeasurableEquiv volume)
    rw [integral_map_equiv]
    simp
  change ∫ w, Φ w * h (τ (L w) x) = ∫ v, ((c : ℝ) : ℂ) * Φ (L.symm v) * h (τ v x) ∂μ
  rw [e1, hμ', integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
    ← integral_const_mul]
  simp only [mul_assoc]

/-- A Haar measure on a finite-dimensional real vector space is invariant under `w ↦ -w`. -/
theorem integral_comp_neg_of_isAddHaarMeasure (μ : Measure W) [μ.IsAddHaarMeasure]
    (f : W → ℂ) : ∫ w, f (-w) ∂μ = ∫ w, f w ∂μ := by
  have : SecondCountableTopology W :=
    (Module.finBasis ℝ W).equivFun.toContinuousLinearEquiv.toHomeomorph.secondCountableTopology
  exact integral_neg_eq_self f μ

end Module

section Periodic

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The argument of a quotient, as a real number modulo the integers. -/
private theorem dixmierMalliavin_arg_div (ζ ζ₀ : ℂ) (hζ : ζ ≠ 0) (hζ₀ : ζ₀ ≠ 0) :
    ∃ k : ℤ, Complex.arg ζ / (2 * Real.pi) =
      Complex.arg ζ₀ / (2 * Real.pi) + (Complex.log (ζ / ζ₀)).im / (2 * Real.pi) + k := by
  have h := Complex.arg_div_coe_angle hζ hζ₀
  rw [← Real.Angle.coe_sub, Real.Angle.angle_eq_iff_two_pi_dvd_sub] at h
  obtain ⟨k, hk⟩ := h
  refine ⟨-k, ?_⟩
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  rw [Complex.log_im]
  push_cast
  field_simp
  linarith

/-- The argument of a point of the unit circle, as a real number modulo the integers. -/
private theorem dixmierMalliavin_arg_exp (s : ℝ) :
    ∃ k : ℤ, Complex.arg (Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I)) / (2 * Real.pi) =
      s + k := by
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  have h2 := Complex.norm_mul_exp_arg_mul_I
    (Complex.exp (((2 * Real.pi * s : ℝ) : ℂ) * Complex.I))
  rw [Complex.norm_exp_ofReal_mul_I, Complex.ofReal_one, one_mul,
    Complex.exp_eq_exp_iff_exists_int] at h2
  obtain ⟨k, hk⟩ := h2
  refine ⟨k, ?_⟩
  have h3 := congrArg Complex.im hk
  simp at h3
  push_cast
  rw [h3]
  field_simp

/-- Dixmier–Malliavin along a line for functions on `ℝ^ι × ℝ^κ` that are periodic in the
second variable and compactly supported in the first. Such a smooth `F` is
`φ ⋆ᵥ F₁ + ψ ⋆ᵥ F`, where `⋆ᵥ` integrates along the direction `v = (v₁, v₂)` against a
one-variable test function and `F₁` is smooth, periodic, and supported over the same compact
set. The group `ℝ^ι × (ℝ/ℤ)^κ` is realized in the Banach algebra `ℝ^ι × ℂ^κ` by
`(x, s) ↦ (exp x, exp (2πi s))`, where the line becomes an exponential flow. -/
theorem dixmierMalliavin_periodic_direction (v₁ : ι → ℝ) (v₂ : κ → ℝ)
    (F : (ι → ℝ) × (κ → ℝ) → ℂ) (hF : ContDiff ℝ ∞ F)
    (hper : ∀ (x : ι → ℝ) (t : κ → ℝ) (k : κ → ℤ), F (x, fun j ↦ t j + k j) = F (x, t))
    (K : Set (ι → ℝ)) (hK : IsCompact K) (hFK : ∀ x t, x ∉ K → F (x, t) = 0) :
    ∃ (F₁ : (ι → ℝ) × (κ → ℝ) → ℂ) (φ ψ : ℝ → ℂ), ContDiff ℝ ∞ F₁ ∧
      (∀ (x : ι → ℝ) (t : κ → ℝ) (k : κ → ℤ), F₁ (x, fun j ↦ t j + k j) = F₁ (x, t)) ∧
      (∀ x t, x ∉ K → F₁ (x, t) = 0) ∧
      ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      ∀ w, F w = (∫ t : ℝ, φ t * F₁ (w + t • (v₁, v₂))) + ∫ t : ℝ, ψ t * F (w + t • (v₁, v₂)) := by
  classical
  have hπ : (2 * Real.pi) ≠ 0 := by positivity
  let b : ContDiffBump (1 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  let N : ℂ → ℝ := fun ζ ↦ ζ.re * ζ.re + ζ.im * ζ.im
  have hN : ContDiff ℝ ∞ N := (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
    (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  let ρ : (κ → ℂ) → ℂ := fun ζ ↦ ∏ j, ((b (N (ζ j)) : ℝ) : ℂ)
  have hρ : ContDiff ℝ ∞ ρ := contDiff_prod fun j _ ↦ Complex.ofRealCLM.contDiff.comp
    (b.contDiff.comp (hN.comp ((contDiff_pi (𝕜 := ℝ)).mp contDiff_id j)))
  let Θ : (κ → ℂ) → (κ → ℝ) := fun ζ j ↦ Complex.arg (ζ j) / (2 * Real.pi)
  let Lg : (ι → ℝ) → (ι → ℝ) := fun y i ↦ Real.log (y i)
  let Ex : (ι → ℝ) → (ι → ℝ) := fun x i ↦ Real.exp (x i)
  have hEx : ContDiff ℝ ∞ Ex :=
    contDiff_pi.mpr fun i ↦ Real.contDiff_exp.comp ((contDiff_pi (𝕜 := ℝ)).mp contDiff_id i)
  have hExi : Injective Ex := fun s t h ↦ funext fun j ↦ Real.exp_injective (congrFun h j)
  have hLE (x : ι → ℝ) : Lg (Ex x) = x := funext fun i ↦ Real.log_exp (x i)
  let Φ : (ι → ℝ) × (κ → ℂ) → ℂ := fun p ↦
    if ∀ i, 0 < p.1 i then ρ p.2 * F (Lg p.1, Θ p.2) else 0
  let C : Set ℂ := {ζ : ℂ | N ζ ∈ Metric.closedBall (1 : ℝ) (1 / 2)}
  have hC : IsCompact C := by
    refine (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset
      (Metric.isClosed_closedBall.preimage hN.continuous) fun ζ hζ ↦ ?_
    have h1 : N ζ ≤ 3 / 2 := by
      have := (abs_le.mp (Real.dist_eq (N ζ) 1 ▸ Metric.mem_closedBall.mp hζ)).2
      linarith
    have h2 := Complex.sq_norm ζ
    rw [Complex.normSq_apply] at h2
    rw [mem_closedBall_zero_iff]
    nlinarith [norm_nonneg ζ]
  have hC0 {ζ : ℂ} (hζ : ζ ∈ C) : ζ ≠ 0 := by
    rintro rfl
    have := Metric.mem_closedBall.mp hζ
    simp [N, Real.dist_eq] at this
    norm_num at this
  let KA : Set ((ι → ℝ) × (κ → ℂ)) := (Ex '' K) ×ˢ (Set.pi univ fun _ ↦ C)
  have hKA : IsCompact KA := (hK.image hEx.continuous).prod (isCompact_univ_pi fun _ ↦ hC)
  have hsupp : tsupport Φ ⊆ KA := by
    apply closure_minimal _ hKA.isClosed
    intro p hp
    have hp' : Φ p ≠ 0 := hp
    by_cases hpos : ∀ i, 0 < p.1 i
    · simp only [Φ, ite_eq_left hpos, mul_ne_zero_iff] at hp'
      refine ⟨⟨Lg p.1, ?_, funext fun i ↦ Real.exp_log (hpos i)⟩, fun j _ ↦ ?_⟩
      · by_contra hk
        exact hp'.2 (hFK _ _ hk)
      · have hj : (b (N (p.2 j)) : ℝ) ≠ 0 := by
          intro h0
          exact hp'.1 (Finset.prod_eq_zero (Finset.mem_univ j) (by simp [h0]))
        have hmem : N (p.2 j) ∈ Function.support b := hj
        rw [b.support_eq] at hmem
        exact Metric.ball_subset_closedBall hmem
    · exact (hp' (ite_eq_right hpos)).elim
  have hΦc : HasCompactSupport Φ := hKA.of_isClosed_subset (isClosed_tsupport _) hsupp
  have hΦ : ContDiff ℝ ∞ Φ := by
    refine contDiff_iff_contDiffAt.mpr fun p ↦ ?_
    by_cases hp : p ∈ tsupport Φ
    · obtain ⟨⟨x, -, hx⟩, hp2⟩ := hsupp hp
      have hpos : ∀ i, 0 < p.1 i := fun i ↦ by
        rw [← hx]
        exact Real.exp_pos _
      have hne : ∀ j, p.2 j ≠ 0 := fun j ↦ hC0 (hp2 j (mem_univ j))
      let G : (ι → ℝ) × (κ → ℂ) → ℂ := fun q ↦ ρ q.2 * F (Lg q.1, fun j ↦
        Complex.arg (p.2 j) / (2 * Real.pi) + (Complex.log (q.2 j / p.2 j)).im / (2 * Real.pi))
      have hG : ContDiffAt ℝ ∞ G p := by
        refine (hρ.contDiffAt.comp p contDiffAt_snd).mul (hF.contDiffAt.comp p ?_)
        refine ContDiffAt.prodMk (contDiffAt_pi.mpr fun i ↦ ?_) (contDiffAt_pi.mpr fun j ↦ ?_)
        · exact (Real.contDiffAt_log.mpr (hpos i).ne').comp p
            ((contDiffAt_pi (𝕜 := ℝ)).mp contDiffAt_fst i)
        · refine contDiffAt_const.add (ContDiffAt.div_const ?_ _)
          have hq : ContDiffAt ℝ ∞ (fun q : (ι → ℝ) × (κ → ℂ) ↦ q.2 j / p.2 j) p :=
            ((contDiffAt_pi (𝕜 := ℝ)).mp contDiffAt_snd j).div_const _
          have hl : ContDiffAt ℝ ∞ Complex.log (p.2 j / p.2 j) := by
            rw [div_self (hne j)]
            exact (Complex.contDiffAt_log Complex.one_mem_slitPlane).restrict_scalars ℝ
          exact Complex.imCLM.contDiff.contDiffAt.comp p (hl.comp p hq)
      refine hG.congr_of_eventuallyEq ?_
      have ho1 : IsOpen {q : (ι → ℝ) × (κ → ℂ) | ∀ i, 0 < q.1 i} := by
        simp only [ofPred_forall]
        exact isOpen_iInter_of_finite fun i ↦
          isOpen_lt continuous_const ((continuous_apply i).comp continuous_fst)
      have ho2 : IsOpen {q : (ι → ℝ) × (κ → ℂ) | ∀ j, q.2 j ≠ 0} := by
        simp only [ofPred_forall]
        exact isOpen_iInter_of_finite fun j ↦
          isOpen_ne_fun ((continuous_apply j).comp continuous_snd) continuous_const
      filter_upwards [ho1.mem_nhds hpos, ho2.mem_nhds hne] with q hq1 hq2
      choose k hk using fun j ↦ dixmierMalliavin_arg_div (q.2 j) (p.2 j) (hq2 j) (hne j)
      have hΘ : Θ q.2 = fun j ↦ (Complex.arg (p.2 j) / (2 * Real.pi) +
          (Complex.log (q.2 j / p.2 j)).im / (2 * Real.pi)) + k j := funext hk
      simp only [Φ, G, ite_eq_left hq1, hΘ, hper]
    · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hp)
  let X₂ : κ → ℂ := fun j ↦ ((2 * Real.pi * v₂ j : ℝ) : ℂ) * Complex.I
  let X : (ι → ℝ) × (κ → ℂ) := (v₁, X₂)
  obtain ⟨Φ₁, φ, ψ, h₁, hs₁, hφ, hψ, hsφ, hsψ, heq⟩ :=
    DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add X 1 one_pos Φ hΦ hΦc
  have hφc : HasCompactSupport φ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsφ
  have hψc : HasCompactSupport ψ := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hsψ
  let ε : (ι → ℝ) × (κ → ℝ) → (ι → ℝ) × (κ → ℂ) := fun w ↦
    (Ex w.1, fun j ↦ Complex.exp (((2 * Real.pi * w.2 j : ℝ) : ℂ) * Complex.I))
  have hε : ContDiff ℝ ∞ ε := by
    refine (hEx.comp contDiff_fst).prodMk (contDiff_pi.mpr fun j ↦ ?_)
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
      (contDiff_const.mul ((contDiff_pi (𝕜 := ℝ)).mp contDiff_snd j))).mul contDiff_const)
  have hflow (w : (ι → ℝ) × (κ → ℝ)) (t : ℝ) :
      ε w * NormedSpace.exp (t • X) = ε (w + t • (v₁, v₂)) := by
    have hfst : (NormedSpace.exp (t • X)).1 = NormedSpace.exp (t • v₁) :=
      NormedSpace.map_exp (RingHom.fst (ι → ℝ) (κ → ℂ)) continuous_fst _
    have hsnd : (NormedSpace.exp (t • X)).2 = NormedSpace.exp (t • X₂) :=
      NormedSpace.map_exp (RingHom.snd (ι → ℝ) (κ → ℂ)) continuous_snd _
    refine Prod.ext (funext fun i ↦ ?_) (funext fun j ↦ ?_)
    · have hi : NormedSpace.exp (t • v₁) i = NormedSpace.exp (t * v₁ i) :=
        NormedSpace.map_exp (Pi.evalRingHom (fun _ : ι ↦ ℝ) i) (continuous_apply i) _
      change Real.exp (w.1 i) * (NormedSpace.exp (t • X)).1 i = Real.exp (w.1 i + t * v₁ i)
      rw [hfst, hi, Real.exp_add, ← Real.exp_eq_exp_ℝ]
    · have hj : NormedSpace.exp (t • X₂) j = NormedSpace.exp (t • X₂ j) :=
        NormedSpace.map_exp (Pi.evalRingHom (fun _ : κ ↦ ℂ) j) (continuous_apply j) _
      change Complex.exp (((2 * Real.pi * w.2 j : ℝ) : ℂ) * Complex.I) *
          (NormedSpace.exp (t • X)).2 j =
        Complex.exp (((2 * Real.pi * (w.2 j + t * v₂ j) : ℝ) : ℂ) * Complex.I)
      rw [hsnd, hj, ← Complex.exp_eq_exp_ℂ, ← Complex.exp_add]
      congr 1
      simp only [X₂, Complex.real_smul]
      push_cast
      ring
  have hΦε (w : (ι → ℝ) × (κ → ℝ)) : Φ (ε w) = F w := by
    have hpos : ∀ i, 0 < (ε w).1 i := fun i ↦ Real.exp_pos _
    have hN1 (j : κ) : N ((ε w).2 j) = 1 := by
      simp only [ε, N, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
      nlinarith [Real.cos_sq_add_sin_sq (2 * Real.pi * w.2 j)]
    have hb1 : b 1 = 1 := b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)
    have hρ1 : ρ (ε w).2 = 1 := by simp [ρ, hN1, hb1]
    choose k hk using fun j ↦ dixmierMalliavin_arg_exp (w.2 j)
    have hΘ : Θ (ε w).2 = fun j ↦ w.2 j + k j := funext hk
    simp only [Φ, ite_eq_left hpos, hρ1, one_mul, hΘ, hper]
    exact congrArg F (Prod.ext (hLE w.1) rfl)
  refine ⟨Φ₁ ∘ ε, φ, ψ, h₁.comp hε, fun x t k ↦ ?_, fun x t hx ↦ ?_, hφ, hφc, hψ, hψc,
    fun w ↦ ?_⟩
  · have he : ε (x, fun j ↦ t j + k j) = ε (x, t) := by
      refine Prod.ext rfl (funext fun j ↦ ?_)
      refine Complex.exp_eq_exp_iff_exists_int.mpr ⟨k j, ?_⟩
      push_cast
      ring
    exact congrArg Φ₁ he
  · change Φ₁ (ε (x, t)) = 0
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    obtain ⟨⟨y, hy, hxy⟩, -⟩ := hsupp (hs₁ hmem)
    have hyx : y = x := hExi hxy
    exact hx (hyx ▸ hy)
  · have h := heq (ε w)
    simp only [hflow, hΦε] at h
    exact h

end Periodic

section Periodization

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- A sum of translates of a smooth compactly supported function along a family of vectors
with finitely many members in each ball is smooth: near each point the sum is finite. -/
theorem contDiff_tsum_translates {Z : Type*} (ζ : Z → V)
    (hζ : ∀ R : ℝ, {z | ‖ζ z‖ ≤ R}.Finite) (Φ : V → ℂ) (hΦ : ContDiff ℝ ∞ Φ)
    (hΦc : HasCompactSupport Φ) : ContDiff ℝ ∞ (fun w ↦ ∑' z, Φ (w + ζ z)) := by
  classical
  obtain ⟨R₀, hR₀⟩ := hΦc.isCompact.isBounded.subset_closedBall (0 : V)
  refine contDiff_iff_contDiffAt.mpr fun w₀ ↦ ?_
  let Z₀ := (hζ (R₀ + ‖w₀‖ + 1)).toFinset
  have hfs : ContDiff ℝ ∞ (fun w ↦ ∑ z ∈ Z₀, Φ (w + ζ z)) :=
    ContDiff.sum fun z _ ↦ hΦ.comp (contDiff_id.add contDiff_const)
  refine hfs.contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [Metric.ball_mem_nhds w₀ one_pos] with w hw
  refine tsum_eq_sum fun z hz ↦ ?_
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have h1 : ‖w + ζ z‖ ≤ R₀ := mem_closedBall_zero_iff.mp (hR₀ hmem)
  have h2 : ‖w‖ < ‖w₀‖ + 1 := by
    have hd : ‖w - w₀‖ < 1 := by
      rw [← dist_eq_norm]
      exact Metric.mem_ball.mp hw
    calc ‖w‖ = ‖(w - w₀) + w₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖w - w₀‖ + ‖w₀‖ := norm_add_le _ _
      _ < ‖w₀‖ + 1 := by linarith
  have h3 : ‖ζ z‖ ≤ R₀ + ‖w₀‖ + 1 := by
    calc ‖ζ z‖ = ‖(w + ζ z) - w‖ := by rw [add_sub_cancel_left]
      _ ≤ ‖w + ζ z‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ R₀ + ‖w₀‖ + 1 := by linarith
  exact hz ((hζ _).mem_toFinset.mpr h3)

end Periodization

section Unfolding

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Unfolding for the covering `ℝ^ι × ℝ^κ → ℝ^ι × (ℝ/ℤ)^κ`. If a continuous function `R`
on `ℝ^ι × (ℝ/ℤ)^κ` is the sum over the fibres of a continuous compactly supported function
`Ψ` on `ℝ^ι × ℝ^κ`, then the two have the same integral. -/
theorem integral_eq_integral_of_tsum_int_translates
    (Ψ : (ι → ℝ) × (κ → ℝ) → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ)
    (R : (ι → ℝ) × (κ → AddCircle (1 : ℝ)) → ℂ) (hR : Continuous R)
    (hRΨ : ∀ (x : ι → ℝ) (t : κ → ℝ), R (x, fun j ↦ (t j : AddCircle (1 : ℝ))) =
      ∑' z : κ → ℤ, Ψ (x, fun j ↦ t j + z j)) :
    ∫ p, R p = ∫ w, Ψ w := by
  classical
  let q : (κ → ℝ) → (κ → AddCircle (1 : ℝ)) := fun t j ↦ (t j : AddCircle (1 : ℝ))
  let Box : Set (κ → ℝ) := Set.pi univ fun _ ↦ Ioc (0 : ℝ) (0 + 1)
  have hq : MeasurePreserving q (volume.restrict Box) volume := by
    have h := measurePreserving_pi (fun _ : κ ↦ (volume : Measure ℝ).restrict (Ioc (0 : ℝ) (0 + 1)))
      (fun _ : κ ↦ (volume : Measure (AddCircle (1 : ℝ))))
      (fun _ ↦ AddCircle.measurePreserving_mk (1 : ℝ) 0)
    rwa [← Measure.restrict_pi_pi] at h
  have hQ : MeasurePreserving (Prod.map (id : (ι → ℝ) → (ι → ℝ)) q)
      ((volume : Measure (ι → ℝ)).prod (volume.restrict Box)) (volume.prod volume) :=
    (MeasurePreserving.id volume).prod hq
  let a : (κ → ℤ) → (ι → ℝ) × (κ → ℝ) := fun z ↦ (0, fun j ↦ (z j : ℝ))
  let s : (κ → ℤ) → Set ((ι → ℝ) × (κ → ℝ)) := fun z ↦
    {w | ∀ j, w.2 j ∈ Ioc (z j : ℝ) (z j + 1)}
  have hsm (z : κ → ℤ) : MeasurableSet (s z) := by
    simp only [s, ofPred_forall]
    exact MeasurableSet.iInter fun j ↦
      measurableSet_preimage ((measurable_pi_apply j).comp measurable_snd) measurableSet_Ioc
  have hs0 : s 0 = (univ : Set (ι → ℝ)) ×ˢ Box := by
    ext w
    simp [s, Box]
  have e1 : ∫ p, R p = ∫ w in s 0, R (w.1, q w.2) := by
    change ∫ p, R p ∂((volume : Measure (ι → ℝ)).prod volume) = _
    have hν : (volume : Measure (ι → ℝ)).prod (volume.restrict Box) =
        (volume.prod volume).restrict (univ ×ˢ Box) := by
      have h := Measure.prod_restrict (μ := (volume : Measure (ι → ℝ)))
        (ν := (volume : Measure (κ → ℝ))) univ Box
      rwa [Measure.restrict_univ] at h
    rw [← hQ.map_eq, integral_map hQ.measurable.aemeasurable hR.aestronglyMeasurable, hs0, hν]
    rfl
  have : (volume : Measure ((ι → ℝ) × (κ → ℝ))).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  have hΨi : Integrable Ψ := hΨ.integrable_of_hasCompactSupport hΨc
  have hsd : Pairwise (Disjoint on s) := by
    intro z z' hzz
    refine Set.disjoint_left.mpr fun w hw hw' ↦ hzz (funext fun j ↦ ?_)
    have h1 := hw j
    have h2 := hw' j
    have h3 : (z j : ℝ) < z' j + 1 := lt_of_lt_of_le h1.1 h2.2
    have h4 : (z' j : ℝ) < z j + 1 := lt_of_lt_of_le h2.1 h1.2
    have h5 : z j < z' j + 1 := by exact_mod_cast h3
    have h6 : z' j < z j + 1 := by exact_mod_cast h4
    omega
  have hsu : ⋃ z, s z = univ := by
    refine eq_univ_of_forall fun w ↦ mem_iUnion.mpr ⟨fun j ↦ ⌈w.2 j⌉ - 1, fun j ↦ ⟨?_, ?_⟩⟩
    · push_cast
      linarith [Int.ceil_lt_add_one (w.2 j)]
    · push_cast
      linarith [Int.le_ceil (w.2 j)]
  have e2 : ∫ w, Ψ w = ∑' z, ∫ w in s z, Ψ w := by
    rw [← integral_iUnion hsm hsd (by rw [hsu]; exact hΨi.integrableOn), hsu,
      Measure.restrict_univ]
  have e3 (z : κ → ℤ) : ∫ w in s z, Ψ w = ∫ w in s 0, Ψ (w + a z) := by
    rw [← integral_indicator (hsm z), ← integral_indicator (hsm 0),
      ← integral_add_right_eq_self _ (a z)]
    refine integral_congr_ae (Eventually.of_forall fun w ↦ ?_)
    have hiff : w + a z ∈ s z ↔ w ∈ s 0 := by
      simp only [s, mem_ofPred_eq, a, Prod.snd_add, Pi.add_apply, mem_Ioc, Pi.zero_apply,
        Int.cast_zero, zero_add]
      refine forall_congr' fun j ↦ ⟨fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩,
        fun h ↦ ⟨by linarith [h.1], by linarith [h.2]⟩⟩
    by_cases hw : w ∈ s 0
    · simp only [indicator_of_mem hw, indicator_of_mem (hiff.mpr hw)]
    · simp only [indicator_of_notMem hw, indicator_of_notMem (fun h ↦ hw (hiff.mp h))]
  obtain ⟨R₀, hR₀⟩ := hΨc.isCompact.isBounded.subset_closedBall (0 : (ι → ℝ) × (κ → ℝ))
  have hfin : {z : κ → ℤ | ∀ j, z j ∈ Icc (-⌈R₀ + 1⌉) ⌈R₀ + 1⌉}.Finite := by
    have := Set.Finite.pi fun _ : κ ↦ Set.finite_Icc (-⌈R₀ + 1⌉) ⌈R₀ + 1⌉
    refine this.subset fun z hz j _ ↦ hz j
  have hzero (z : κ → ℤ) (hz : z ∉ hfin.toFinset) (w : (ι → ℝ) × (κ → ℝ)) (hw : w ∈ s 0) :
      Ψ (w + a z) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hmem
    have hn : ‖w + a z‖ ≤ R₀ := mem_closedBall_zero_iff.mp (hR₀ hmem)
    apply hz
    rw [Set.Finite.mem_toFinset]
    intro j
    have h1 : ‖(w + a z).2 j‖ ≤ R₀ :=
      ((norm_le_pi_norm (w + a z).2 j).trans (norm_snd_le _)).trans hn
    have h2 : |w.2 j + (z j : ℝ)| ≤ R₀ := h1
    have h3 := hw j
    simp only [Pi.zero_apply, Int.cast_zero, zero_add, mem_Ioc] at h3
    have h4 := abs_le.mp h2
    constructor
    · have : ((-⌈R₀ + 1⌉ : ℤ) : ℝ) ≤ (z j : ℝ) := by
        push_cast
        linarith [Int.le_ceil (R₀ + 1)]
      exact_mod_cast this
    · have : (z j : ℝ) ≤ ((⌈R₀ + 1⌉ : ℤ) : ℝ) := by linarith [Int.le_ceil (R₀ + 1)]
      exact_mod_cast this
  have hint (z : κ → ℤ) : IntegrableOn (fun w ↦ Ψ (w + a z)) (s 0) :=
    ((hΨ.comp (continuous_id.add continuous_const)).integrable_of_hasCompactSupport
      (hΨc.comp_homeomorph (Homeomorph.addRight (a z)))).integrableOn
  rw [e1, e2]
  simp only [e3]
  rw [tsum_eq_sum (s := hfin.toFinset) fun z hz ↦
    setIntegral_eq_zero_of_forall_eq_zero fun w hw ↦ hzero z hz w hw,
    ← integral_finsetSum _ fun z _ ↦ hint z]
  refine setIntegral_congr_fun (hsm 0) fun w hw ↦ ?_
  change R (w.1, fun j ↦ (w.2 j : AddCircle (1 : ℝ))) = _
  rw [hRΨ, tsum_eq_sum (s := hfin.toFinset) fun z hz ↦ ?_]
  · refine Finset.sum_congr rfl fun z _ ↦ congrArg Ψ (Prod.ext (add_zero _).symm rfl)
  · have := hzero z hz w hw
    rwa [show w + a z = (w.1, fun j ↦ w.2 j + z j) from Prod.ext (add_zero _) rfl] at this

end Unfolding

end RiemannMasullo
