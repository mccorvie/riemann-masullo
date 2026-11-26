module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Closed spans of vector-valued Fourier coefficients -/

public section

open AddCircle MeasureTheory Set

namespace RiemannMasullo

/-- If all Fourier coefficients of a continuous Banach-valued function on a circle
lie in a closed complex submodule, so does every value of the function. -/
theorem mem_closedSubmodule_of_fourierCoeff_mem {L : ℝ} [Fact (0 < L)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : ClosedSubmodule ℂ E) {f : AddCircle L → E} (hf : Continuous f)
    (hcoeff : ∀ n : ℤ, fourierCoeff f n ∈ S) (t : AddCircle L) : f t ∈ S := by
  by_contra h
  let N := S.toSubmodule
  let _ : IsClosed (N : Set E) := S.isClosed
  have hn : N.mkQL (f t) ≠ 0 :=
    fun hz ↦ h ((Submodule.Quotient.mk_eq_zero N).mp hz)
  obtain ⟨g, _, hg⟩ := exists_dual_vector ℂ _ (norm_ne_zero_iff.mpr hn)
  let ℓ := g.comp N.mkQL
  let F : C(AddCircle L, ℂ) := ⟨fun u ↦ ℓ (f u), ℓ.continuous.comp hf⟩
  have hi : Integrable f haarAddCircle :=
    hf.integrable_of_hasCompactSupport (.of_compactSpace _)
  have hF (n : ℤ) : fourierCoeff F n = 0 := by
    have hz : N.mkQL (fourierCoeff f n) = 0 :=
      (Submodule.Quotient.mk_eq_zero N).mpr (hcoeff n)
    calc
      fourierCoeff F n = ℓ (fourierCoeff f n) := by
        simp only [fourierCoeff, F, ContinuousMap.coe_mk, ← map_smul]
        exact ℓ.integral_comp_comm (hi.fourier_smul (-n))
      _ = 0 := by simp [ℓ, hz]
  have hsum := has_pointwise_sum_fourier_series_of_summable (f := F)
    (by rw [show fourierCoeff F = fun _ ↦ 0 from funext hF]; exact summable_zero) t
  have hFt : F t = 0 := by
    simpa only [hF, zero_smul, tsum_zero] using hsum.tsum_eq.symm
  change g (N.mkQL (f t)) = 0 at hFt
  exact hn (norm_eq_zero.mp (Complex.ofReal_eq_zero.mp (hg.symm.trans hFt)))

/-- The Fourier coefficients of continuous orbits of a family of complex linear
operators containing the identity at time zero have dense linear span. -/
theorem closure_span_fourierCoeff_orbits_eq_top {L : ℝ} [Fact (0 < L)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : AddCircle L → E →L[ℂ] E) (hzero : ∀ x, A 0 x = x)
    (hcont : ∀ x, Continuous (fun c ↦ A c x)) :
    (Submodule.span ℂ (range fun nx : ℤ × E ↦
      fourierCoeff (fun c ↦ A c nx.2) nx.1)).topologicalClosure = ⊤ := by
  let S := Submodule.span ℂ (range fun nx : ℤ × E ↦
    fourierCoeff (fun c ↦ A c nx.2) nx.1)
  apply top_unique
  intro x _
  change x ∈ S.topologicalClosure
  rw [← hzero x]
  exact mem_closedSubmodule_of_fourierCoeff_mem S.closure (hcont x)
    (fun n ↦ S.le_topologicalClosure (Submodule.subset_span ⟨(n, x), rfl⟩)) 0


/-- Fourier averaging of a continuous circle action produces a character eigenvector. -/
theorem apply_fourierCoeff_orbit {L : ℝ} [Fact (0 < L)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : AddCircle L → E →L[ℂ] E)
    (hadd : ∀ c d x, A (c + d) x = A c (A d x))
    (hcont : ∀ x, Continuous (fun c ↦ A c x))
    (c : AddCircle L) (n : ℤ) (x : E) :
    A c (fourierCoeff (fun u ↦ A u x) n) =
      fourier n c • fourierCoeff (fun u ↦ A u x) n := by
  have hi : Integrable (fun u ↦ A u x) haarAddCircle :=
    (hcont x).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hu (u : AddCircle L) :
      fourier n c * fourier (-n) (c + u) = fourier (-n) u := by
    have hc : fourier n c * fourier (-n) c = 1 := by
      rw [← fourier_add, add_neg_cancel]
      simp
    have hshift : fourier (-n) (c + u) = fourier (-n) c * fourier (-n) u := by
      simp only [fourier_apply, zsmul_add, toCircle_add, Circle.coe_mul]
    rw [hshift, ← mul_assoc, hc, one_mul]
  calc
    A c (fourierCoeff (fun u ↦ A u x) n) =
        ∫ u, fourier (-n) u • A (c + u) x ∂haarAddCircle := by
      rw [fourierCoeff, ← (A c).integral_comp_comm (hi.fourier_smul (-n))]
      simp only [map_smul, ← hadd]
    _ = ∫ u, fourier n c • (fourier (-n) (c + u) • A (c + u) x) ∂haarAddCircle := by
      exact integral_congr_ae (ae_of_all _ fun u ↦ by dsimp only; rw [smul_smul, hu])
    _ = _ := by
      rw [fourierCoeff, integral_smul]
      congr 1
      exact integral_add_left_eq_self (μ := haarAddCircle)
        (fun u ↦ fourier (-n) u • A u x) c

/-- Character eigenvectors of a strongly continuous circle action have dense linear span. -/
theorem closure_span_characterEigenvectors_eq_top {L : ℝ} [Fact (0 < L)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (A : AddCircle L → E →L[ℂ] E) (hzero : ∀ x, A 0 x = x)
    (hadd : ∀ c d x, A (c + d) x = A c (A d x))
    (hcont : ∀ x, Continuous (fun c ↦ A c x)) :
    (Submodule.span ℂ {x : E | ∃ n : ℤ, ∀ c, A c x = fourier n c • x}).topologicalClosure =
      ⊤ := by
  apply top_unique
  rw [← closure_span_fourierCoeff_orbits_eq_top A hzero hcont]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_mono
  rintro _ ⟨⟨n, x⟩, rfl⟩
  exact ⟨n, fun c ↦ apply_fourierCoeff_orbit A hadd hcont c n x⟩

end RiemannMasullo
