module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxFiniteTower

/-! # The exact triangular central-jet action of positive-time tests -/

public noncomputable section
open Set Filter Function MeasureTheory
open scoped Topology FourierTransform
namespace RiemannMasullo.RationalPacket

private theorem centralMoment_integral (a : ℝ) (j : ℕ) (F : LogL2)
    (hF : ∀ᵐ x ∂volume, x < a → F x = 0) :
    halfLineMellinJet a 0 j F = ∫ x : ℝ, (x : ℂ)^j * (Real.exp (-x/2) : ℂ) * F x := by
  rw [halfLineMellinJet_apply a 0 j F hF, Real.fourier_real_eq]
  simp

/-- Exact triangular translation law for every bounded central Mellin jet on
an actual completed theta stage. -/
theorem halfLineMellinJet_halfShift_zero {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q) (j : ℕ) (h : ℝ) (hh : 0 ≤ h)
    (F : LogL2) (hF : F ∈ closedStageSubmodule X T hT1) :
    halfLineMellinJet (-Real.log X) 0 j (halfShift h F) =
      ∑ i ∈ Finset.range (j+1), ((j.choose i : ℂ) * (h : ℂ)^(j-i)) *
        halfLineMellinJet (-Real.log X) 0 i F := by
  have hs := closedStageSubmodule_supported hX T hT1 hF
  have hs' := closedStageSubmodule_supported hX T hT1
    (halfShift_mem_closedStage hX T hT1 hh hF)
  rw [centralMoment_integral _ j _ hs']
  let G (x : ℝ) := (x : ℂ)^j * (Real.exp (-x/2) : ℂ) * halfShift h F x
  calc
    _ = ∫ x : ℝ, (↑(x+h) : ℂ)^j * (Real.exp (-x/2) : ℂ) * F x := by
      rw [← integral_add_left_eq_self G h]
      apply integral_congr_ae
      have ha := (measurePreserving_add_left volume h).quasiMeasurePreserving.ae_eq_comp (halfShift_ae h F)
      filter_upwards [ha] with x hx
      dsimp only [Function.comp_def] at hx
      dsimp only [G]
      change (↑(h+x) : ℂ)^j * (Real.exp (-(h+x)/2) : ℂ) * halfShift h F (h+x) = _
      rw [hx, add_sub_cancel_left]
      have he : (Real.exp (-(h+x)/2) : ℂ) * (Real.exp (h/2) : ℂ) = (Real.exp (-x/2) : ℂ) := by
        rw [← Complex.ofReal_mul, ← Real.exp_add]
        congr 2
        ring
      rw [← mul_assoc, mul_assoc ((↑(h+x) : ℂ)^j), he, add_comm h x]
    _ = ∫ x : ℝ, ∑ i ∈ Finset.range (j+1), ((j.choose i : ℂ) * (h : ℂ)^(j-i)) *
          ((x : ℂ)^i * (Real.exp (-x/2) : ℂ) * F x) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [Complex.ofReal_add, add_pow, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i ∈ Finset.range (j+1), ∫ x : ℝ, ((j.choose i : ℂ) * (h : ℂ)^(j-i)) *
          ((x : ℂ)^i * (Real.exp (-x/2) : ℂ) * F x) := by
      apply integral_finsetSum
      intro i _
      exact (halfLineMellin_moment_integrable (-Real.log X) i F hs).const_mul _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, ← centralMoment_integral _ i _ hs]


/-- The scalar moments of a compact positive-time test. -/
def positiveTestMoment (f : PositiveTimeTest) (r : ℕ) : ℂ := ∫ t : ℝ, f t * (t : ℂ)^r

theorem positiveTestMoment_zero (f : PositiveTimeTest) :
    positiveTestMoment f 0 = ∫ t : ℝ, f t := by simp [positiveTestMoment]

/-- The actual test action acts triangularly on every finite central jet flag. -/
theorem halfLineMellinJet_ambientTest_zero {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q) (j : ℕ)
    (f : PositiveTimeTest) (F : LogL2) (hF : F ∈ closedStageSubmodule X T hT1) :
    halfLineMellinJet (-Real.log X) 0 j (fixedBoxAmbientTestAction f F) =
      ∑ i ∈ Finset.range (j+1), ((j.choose i : ℂ) * positiveTestMoment f (j-i)) *
        halfLineMellinJet (-Real.log X) 0 i F := by
  have hi : Integrable (fun t : ℝ ↦ f t • halfShift (t.toNNReal : ℝ) F) volume :=
    (f.continuous.smul ((continuous_halfShift F).comp (by fun_prop))).integrable_of_hasCompactSupport
      f.hasCompactSupport.smul_right
  rw [fixedBoxAmbientTestAction_apply, ← (halfLineMellinJet (-Real.log X) 0 j).integral_comp_comm hi]
  calc
    _ = ∫ t : ℝ, ∑ i ∈ Finset.range (j+1),
        (f t * ((j.choose i : ℂ) * (t : ℂ)^(j-i))) * halfLineMellinJet (-Real.log X) 0 i F := by
      apply integral_congr_ae
      filter_upwards with t
      rw [map_smul, smul_eq_mul]
      by_cases ht : f t = 0
      · simp only [ht, zero_mul, Finset.sum_const_zero]
      have ht0 : 0 < t := f.tsupport_subset (subset_tsupport f ht)
      rw [Real.coe_toNNReal t ht0.le, halfLineMellinJet_halfShift_zero hX T hT1 j t ht0.le F hF,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i ∈ Finset.range (j+1), ∫ t : ℝ,
        (f t * ((j.choose i : ℂ) * (t : ℂ)^(j-i))) * halfLineMellinJet (-Real.log X) 0 i F := by
      apply integral_finsetSum
      intro i _
      apply Continuous.integrable_of_hasCompactSupport
      · exact ((f.continuous.mul (continuous_const.mul (Complex.continuous_ofReal.pow _))).mul continuous_const)
      · exact (f.hasCompactSupport.mul_right).mul_right
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_mul_const]
      congr 1
      change (∫ t : ℝ, f t * ((j.choose i : ℂ) * (t : ℂ)^(j-i))) =
        (j.choose i : ℂ) * ∫ t : ℝ, f t * (t : ℂ)^(j-i)
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring

/-- The finite matrix of the actual test action on central Mellin jets. -/
def centralJetTestMatrix (m : ℕ) (f : PositiveTimeTest) :
    (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ) :=
  LinearMap.pi (fun j ↦ ∑ i : Fin m,
    ((j.val.choose i.val : ℂ) * positiveTestMoment f (j.val-i.val)) • LinearMap.proj i)

theorem centralJetTestMatrix_apply (m : ℕ) (f : PositiveTimeTest) (y : Fin m → ℂ) (j : Fin m) :
    centralJetTestMatrix m f y j = ∑ i : Fin m,
      ((j.val.choose i.val : ℂ) * positiveTestMoment f (j.val-i.val)) * y i := by
  simp only [centralJetTestMatrix, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

/-- Every diagonal entry is the zeroth moment of the test. -/
theorem centralJetTestMatrix_diagonal (m : ℕ) (f : PositiveTimeTest) (j : Fin m) :
    centralJetTestMatrix m f (Pi.single j 1) j = ∫ t : ℝ, f t := by
  classical
  rw [centralJetTestMatrix_apply]
  simp [Pi.single_apply, positiveTestMoment_zero]

end RiemannMasullo.RationalPacket
