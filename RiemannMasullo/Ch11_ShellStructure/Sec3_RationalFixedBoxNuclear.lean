module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxBasis
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.NuclearRankOneSeries
public import Mathlib.Analysis.Fourier.PoissonSummation

/-! # Nuclear test actions and traces on actual rational packets

Paper: the packet trace calculation following (11.3.1.3), p. 494.
The actual completed quotient circle action is integrated against a Schwartz
function in logarithmic time. Uniformly bounded rank-one circle projections
give a nuclear spectral multiplier, and Poisson summation computes its trace.
Tests supported strictly inside the first period have zero trace.

This concerns the rational trivial-angular channel in unweighted logarithmic
`L²`. Identification with the physical geometric shell remains a separate step.
-/

public noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace RiemannMasullo.RationalPacket

private theorem nuclear_trace_of_eq {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (A B : H →L[ℂ] H) (heq : A = B) (M : ℝ) (c : ℤ → ℂ)
    (h : ∃ hB : IsNuclearOperator B,
      traceNorm ⟨B, hB⟩ ≤ M ∧ HasSum c (hilbertTrace ⟨B, hB⟩)) :
    ∃ hA : IsNuclearOperator A,
      traceNorm ⟨A, hA⟩ ≤ M ∧ HasSum c (hilbertTrace ⟨A, hA⟩) := by
  subst B
  exact h

variable {X : ℝ} (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q)
variable (p : ℕ) (hTp1 : ∀ q ∈ insert p T, 1 ≤ q) (hX : 0 < X)
variable (hp : p.Prime) (hpT : p ∉ T)
local notation "L" => Real.log (p : ℝ)
local notation "Q" => FixedBoxQuotient[X,T,hT1,p,hTp1]
local instance : NormedSpace ℂ Q := Submodule.Quotient.normedSpace _ ℂ
local instance : NormedSpace ℝ Q := Submodule.Quotient.normedSpace _ ℝ
local notation "ρ" => fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt
local notation "P" => fixedBoxFourierProjection T hT1 p hTp1 hX hp hpT

/-- Each one-dimensional circle projection is bounded uniformly in the mode. -/
theorem norm_fixedBoxFourierProjection_le (n : ℤ) : ‖P n‖ ≤ Real.sqrt p := by
  let : Fact (0 < L) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro u
  rw [fixedBoxFourierProjection_apply, _root_.fourierCoeff]
  have hb : ∀ᵐ s : AddCircle L ∂AddCircle.haarAddCircle,
      ‖_root_.fourier (- -n) s • ρ s u‖ ≤ Real.sqrt p * ‖u‖ := by
    filter_upwards with s
    rw [norm_smul, _root_.fourier_apply, Circle.norm_coe, one_mul]
    exact ((ρ s).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_fixedBoxCircleAction_le T hT1 p hTp1 hX hp.one_lt s) (norm_nonneg u))
  simpa using! norm_integral_le_of_norm_le_const hb

/-- The spectral multiplier formed from the actual packet projections. -/
def fixedBoxSpectralMultiplier (c : ℤ → ℂ) : Q →L[ℂ] Q := ∑' n, c n • P n

/-- Summable symbols give operator-norm convergent spectral expansions. -/
theorem fixedBoxSpectralMultiplier_hasSum (c : ℤ → ℂ) (hc : Summable (fun n ↦ ‖c n‖)) :
    HasSum (fun n : ℤ ↦ c n • P n) (fixedBoxSpectralMultiplier T hT1 p hTp1 hX hp hpT c) := by
  apply Summable.hasSum
  apply Summable.of_norm
  apply (hc.mul_right (Real.sqrt p)).of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_)
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left (norm_fixedBoxFourierProjection_le T hT1 p hTp1 hX hp hpT n) (norm_nonneg _)

/-- Every absolutely summable symbol gives a nuclear operator on the actual
completed packet. Its trace is the sum of the symbol, including the zero mode. -/
theorem fixedBoxSpectralMultiplier_nuclear_trace (hT : ∀ q ∈ T, q.Prime)
    (c : ℤ → ℂ) (hc : Summable (fun n ↦ ‖c n‖)) :
    ∃ h : IsNuclearOperator (fixedBoxSpectralMultiplier T hT1 p hTp1 hX hp hpT c),
      traceNorm ⟨_, h⟩ ≤ Real.sqrt p * (∑' n, ‖c n‖) ∧
      HasSum c (hilbertTrace ⟨_, h⟩) := by
  have hex := exists_fixedBox_rankOne_projections T hT1 p hTp1 hX hp hpT hT
  rcases hex with ⟨v, hrow, hproj⟩
  let ℓ := fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT
  have heq (n : ℤ) : (ℓ n).smulRight (v n) = P n := by
    apply ContinuousLinearMap.ext
    intro u
    exact (hproj n u).symm
  exact nuclear_tsum_smul_rankOne (H := Q) P ℓ v heq
    (fun n ↦ by simpa only [ite_true] using hrow n n)
    (Real.sqrt p) (norm_fixedBoxFourierProjection_le T hT1 p hTp1 hX hp hpT) c hc

open scoped FourierTransform SchwartzMap

include hpT in
private theorem fixedBoxTest_integrable (w : 𝓢(ℝ, ℂ)) (u : Q) :
    Integrable (fun t : ℝ ↦ w t • ρ (t : AddCircle L) u) volume := by
  have hcont : Continuous (fun t : ℝ ↦ w t • ρ (t : AddCircle L) u) :=
    w.continuous.smul ((continuous_fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt hpT u).comp
      (AddCircle.continuous_mk' L))
  apply (w.integrable.norm.mul_const (Real.sqrt p * ‖u‖)).mono' hcont.aestronglyMeasurable
  filter_upwards with t
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_left
    (((ρ (t : AddCircle L)).le_opNorm u).trans
      (mul_le_mul_of_nonneg_right (norm_fixedBoxCircleAction_le T hT1 p hTp1 hX hp.one_lt _) (norm_nonneg u)))
    (norm_nonneg _)

private theorem norm_fixedBoxTest_integral_le (w : 𝓢(ℝ, ℂ)) (u : Q) :
    ‖∫ t : ℝ, w t • ρ (t : AddCircle L) u‖ ≤
      (Real.sqrt p * (∫ t : ℝ, ‖w t‖)) * ‖u‖ := by
  have hb : ∀ᵐ t : ℝ ∂volume, ‖w t • ρ (t : AddCircle L) u‖ ≤
      ‖w t‖ * (Real.sqrt p * ‖u‖) := by
    filter_upwards with t
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left
      (((ρ (t : AddCircle L)).le_opNorm u).trans
        (mul_le_mul_of_nonneg_right (norm_fixedBoxCircleAction_le T hT1 p hTp1 hX hp.one_lt _) (norm_nonneg u)))
      (norm_nonneg _)
  calc
    _ ≤ ∫ t : ℝ, ‖w t‖ * (Real.sqrt p * ‖u‖) :=
      norm_integral_le_of_norm_le (w.integrable.norm.mul_const _) hb
    _ = _ := by rw [integral_mul_const]; ring

/-- The actual completed dilation action integrated against a logarithmic
Schwartz test. This is defined by vector integrals, using strong continuity. -/
def fixedBoxTestAction (hpT : p ∉ T) (w : 𝓢(ℝ, ℂ)) : Q →L[ℂ] Q := by
  let A : Q →ₗ[ℂ] Q := {
    toFun u := ∫ t : ℝ, w t • ρ (t : AddCircle L) u
    map_add' u v := by
      simp only [map_add, smul_add]
      exact integral_add (fixedBoxTest_integrable T hT1 p hTp1 hX hp hpT w u)
        (fixedBoxTest_integrable T hT1 p hTp1 hX hp hpT w v)
    map_smul' c u := by
      simp only [map_smul, RingHom.id_apply]
      simp_rw [smul_comm (w _) c]
      exact integral_smul c _ }
  exact A.mkContinuous (Real.sqrt p * (∫ t : ℝ, ‖w t‖))
    (norm_fixedBoxTest_integral_le T hT1 p hTp1 hX hp w)

/-- Evaluation of the integrated action on an actual quotient vector. -/
theorem fixedBoxTestAction_apply (w : 𝓢(ℝ, ℂ)) (u : Q) :
    fixedBoxTestAction T hT1 p hTp1 hX hp hpT w u =
      ∫ t : ℝ, w t • ρ (t : AddCircle L) u := by rfl

private theorem integral_test_circle_character (w : 𝓢(ℝ, ℂ)) (n : ℤ) :
    (∫ t : ℝ, w t * _root_.fourier (-n) (t : AddCircle L)) =
      (𝓕 w) ((n : ℝ) / L) := by
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with t
  rw [_root_.fourier_coe_apply, smul_eq_mul, mul_comm (w t)]
  congr 2
  push_cast
  ring

include hpT in
/-- A genuine circle eigenvector has the expected Fourier-test eigenvalue. -/
theorem fixedBoxTestAction_eigen (w : 𝓢(ℝ, ℂ)) (n : ℤ) (u : Q)
    (hu : ∀ s : AddCircle L, ρ s u = _root_.fourier (-n) s • u) :
    fixedBoxTestAction T hT1 p hTp1 hX hp hpT w u = (𝓕 w) ((n : ℝ) / L) • u := by
  rw [fixedBoxTestAction_apply]
  simp_rw [hu, ← smul_assoc, smul_eq_mul]
  rw [integral_smul_const, integral_test_circle_character]

include hp in
/-- Schwartz Fourier samples are absolutely summable on the prime logarithmic mesh. -/
theorem summable_fixedBox_test_symbol (w : 𝓢(ℝ, ℂ)) :
    Summable (fun n : ℤ ↦ ‖(𝓕 w) ((n : ℝ) / L)‖) := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let g := dilate L⁻¹ (inv_pos.mpr hL) (𝓕 w)
  have hs : Summable (fun n : ℤ ↦ ‖g n‖) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((g.isBigO_cocompact_rpow (-2)).norm_left.comp_tendsto Int.tendsto_coe_cofinite)
  simpa only [g, dilate_apply, div_eq_mul_inv, mul_comm L⁻¹] using hs

/-- The integrated actual circle action agrees with the Fourier spectral
multiplier; equality is proved on the total family of genuine packet modes. -/
theorem fixedBoxTestAction_eq_spectralMultiplier (hT : ∀ q ∈ T, q.Prime)
    (w : 𝓢(ℝ, ℂ)) :
    fixedBoxTestAction T hT1 p hTp1 hX hp hpT w =
      fixedBoxSpectralMultiplier T hT1 p hTp1 hX hp hpT (fun n ↦ (𝓕 w) ((n : ℝ) / L)) := by
  classical
  have hex := exists_fixedBox_total_eigen_cardinals T hT1 p hTp1 hX hp hpT hT
  rcases hex with ⟨v, hrow, heigen, hproj, hd, _⟩
  apply ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.mpr hd)
  rintro _ ⟨n, rfl⟩
  rw [fixedBoxTestAction_eigen T hT1 p hTp1 hX hp hpT w n (v n) (fun s ↦ heigen s n)]
  let c (k : ℤ) := (𝓕 w) ((k : ℝ) / L)
  have hs := (ContinuousLinearMap.apply ℂ Q (v n)).hasSum
    (fixedBoxSpectralMultiplier_hasSum T hT1 p hTp1 hX hp hpT c (summable_fixedBox_test_symbol p hp w))
  have he (k : ℤ) : (c k • P k) (v n) = if k = n then c n • v n else 0 := by
    rw [smul_apply, hproj, hrow]
    by_cases hk : k = n
    · subst k
      simp only [ite_true, one_smul]
    · simp only [hk, ite_false, zero_smul, smul_zero]
  have hs' := hs.congr_fun (fun k ↦ (he k).symm)
  exact (hs'.unique (hasSum_ite_eq n (c n • v n))).symm

/-- Paper: §11.3.1.1(2), p. 494. The Hilbert trace of the integrated test
is the absolutely convergent sum of Fourier samples at `n / log p`,
including frequency zero.
Deviation: The action is on the rational fixed-box quotient with trivial
angular character in unweighted logarithmic `L²`. The logarithmic test is
given directly. The theorem also proves nuclearity and bounds the trace norm. -/
theorem fixedBoxTestAction_nuclear_trace (hT : ∀ q ∈ T, q.Prime)
    (w : 𝓢(ℝ, ℂ)) :
    ∃ h : IsNuclearOperator (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w),
      traceNorm ⟨_, h⟩ ≤ Real.sqrt p * (∑' n : ℤ, ‖(𝓕 w) ((n : ℝ) / L)‖) ∧
      HasSum (fun n : ℤ ↦ (𝓕 w) ((n : ℝ) / L)) (hilbertTrace ⟨_, h⟩) := by
  have heq := fixedBoxTestAction_eq_spectralMultiplier T hT1 p hTp1 hX hp hpT hT w
  have hn := fixedBoxSpectralMultiplier_nuclear_trace T hT1 p hTp1 hX hp hpT hT _
    (summable_fixedBox_test_symbol p hp w)
  exact nuclear_trace_of_eq _ _ heq _ _ hn

include hp in
/-- Paper: (B.4.1.7), p. 608. Poisson summation converts the Fourier sum on
the reciprocal logarithmic mesh into `log p` times the sum on the logarithmic
lattice.
Deviation: This uses a Schwartz test in logarithmic coordinates and the
trivial lattice character. -/
theorem fixedBox_test_symbol_poisson (w : 𝓢(ℝ, ℂ)) :
    (∑' n : ℤ, (𝓕 w) ((n : ℝ) / L)) = (L : ℂ) * ∑' k : ℤ, w (L * k) := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  let g := dilate L hL w
  have h := g.tsum_eq_tsum_fourier 0
  simp only [zero_add, AddCircle.coe_zero, _root_.fourier_eval_zero, mul_one, g, dilate_apply,
    fourier_dilate hL, Complex.real_smul, tsum_mul_left] at h
  have hn : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  calc
    _ = (L : ℂ) * ((L⁻¹ : ℝ) : ℂ) * (∑' n : ℤ, (𝓕 w) ((n : ℝ) / L)) := by rw [Complex.ofReal_inv, mul_inv_cancel₀ hn, one_mul]
    _ = (L : ℂ) * (∑' k : ℤ, w (L * k)) := by rw [mul_assoc, ← h]

/-- Paper: §11.3.1.1(2), p. 494. The Hilbert trace of the integrated packet
action is `log p` times the sum of the logarithmic test on the period lattice.
Deviation: The action is on the rational fixed-box quotient with trivial
angular character in unweighted logarithmic `L²`. The lattice samples are
of the supplied logarithmic test `w`. A comparison with the printed
spectral sum must incorporate its half-shift weight into the test. -/
theorem fixedBoxTestAction_poisson_trace (hT : ∀ q ∈ T, q.Prime)
    (w : 𝓢(ℝ, ℂ)) :
    ∃ h : IsNuclearOperator (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w),
      hilbertTrace ⟨_, h⟩ = (L : ℂ) * ∑' k : ℤ, w (L * k) := by
  have hex := fixedBoxTestAction_nuclear_trace T hT1 p hTp1 hX hp hpT hT w
  rcases hex with ⟨h, _, ht⟩
  exact ⟨h, ht.tsum_eq.symm.trans (fixedBox_test_symbol_poisson p hp w)⟩

/-- Tests supported at nonnegative times integrate the actual forward shifts.
This relates the circle construction to the original completed semigroup. -/
theorem fixedBoxTestAction_eq_forward_integral (w : 𝓢(ℝ, ℂ))
    (hw : Function.support w ⊆ Ici 0) (u : Q) :
    fixedBoxTestAction T hT1 p hTp1 hX hp hpT w u =
      ∫ t : ℝ, w t • fixedBoxForwardShift T hT1 p hTp1 hX t.toNNReal u := by
  rw [fixedBoxTestAction_apply]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : w t = 0
  · simp only [ht, zero_smul]
  · rw [fixedBoxCircleAction_coe T hT1 p hTp1 hX hp.one_lt hpT (hw ht)]

include hp in
private theorem fixedBox_lattice_test_eq_zero (w : 𝓢(ℝ, ℂ))
    (hw : Function.support w ⊆ Ioo 0 L) (k : ℤ) : w (L * k) = 0 := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hp.one_lt)
  by_contra hk
  have hs := hw hk
  have hpos : 0 < (k : ℝ) := (mul_lt_mul_iff_right₀ hL).mp (by simpa only [mul_zero] using hs.1)
  have hlt : (k : ℝ) < 1 := (mul_lt_mul_iff_right₀ hL).mp (by simpa only [mul_one] using hs.2)
  have hkpos : 0 < k := by exact_mod_cast hpos
  have hklt : k < 1 := by exact_mod_cast hlt
  omega

/-- Paper: §11.3.1.1(2), p. 494. A test supported strictly between zero and
the first logarithmic period has zero nuclear packet trace.
Deviation: The action is on the rational fixed-box quotient with trivial
angular character in unweighted logarithmic `L²`. The support condition
is on the logarithmic test, and the trace includes frequency zero. -/
theorem fixedBoxTestAction_trace_eq_zero (hT : ∀ q ∈ T, q.Prime)
    (w : 𝓢(ℝ, ℂ)) (hw : Function.support w ⊆ Ioo 0 L) :
    ∃ h : IsNuclearOperator (fixedBoxTestAction T hT1 p hTp1 hX hp hpT w),
      hilbertTrace ⟨_, h⟩ = 0 := by
  have hex := fixedBoxTestAction_poisson_trace T hT1 p hTp1 hX hp hpT hT w
  rcases hex with ⟨h, ht⟩
  refine ⟨h, ht.trans ?_⟩
  simp only [fixedBox_lattice_test_eq_zero p hp w hw, tsum_zero, mul_zero]

end RiemannMasullo.RationalPacket
