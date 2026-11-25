module

public import RiemannMasullo.AppB_AnalyticNT.FiniteHardyIdealTable
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeSignedCoefficients
import Mathlib.Tactic

/-! # Signed growth measured by finite ideal sums

The coefficient at index zero is zero. At index `j+1` the measurement uses the real part of
entry `j` in logarithmic-derivative row `j`. Through index `N` all rows use the same finite
input of norm below a polynomial in `N`. The unrounded measurements and their integer floors
recover the nearest right-hand site's Green logarithm from either signed prefix. -/

@[expose] public noncomputable section

open Complex Filter Function Metric NumberField Set
open scoped NNReal Topology
namespace RiemannMasullo.FiniteIdealSigned

open FiniteHardyIdealTable HeckeHalfPlaneJensen HeckeLaguerre SignedFrequency

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

/-- The signed measurement with prescribed norm coefficients, principal indicator and field degree. -/
def tableCoeff (a : ℕ → ℂ) (δ d : ℕ) : ℕ → ℝ
  | 0 => 0
  | j+1 => (logRow a δ d j j).re

/-- The coefficients used in the unrounded finite-ideal prefix. -/
def finiteCoeff (χ : U𝔽) : ℕ → ℝ :=
  tableCoeff (idealValue χ) (principalIndex χ) (Module.finrank ℚ F)

/-- An integer-valued measurement of the same finite sum. -/
def integerCoeff (χ : U𝔽) (n : ℕ) : ℤ := ⌊finiteCoeff χ n⌋

/-- The real sequence used in a prefix, with optional integer flooring. -/
def prefixCoeff (χ : U𝔽) (useFloor : Bool) (n : ℕ) : ℝ :=
  if useFloor then (integerCoeff χ n : ℝ) else finiteCoeff χ n

/-- At every index through `N`, the complete table depends only on norm coefficients below
`cutoff d (2*N+1)`. Index zero needs no input. -/
theorem tableCoeff_congr {a b : ℕ → ℂ} (δ d N : ℕ)
    (h : ∀ k < cutoff d (2*N+1), a k = b k) :
    ∀ n ≤ N, tableCoeff a δ d n = tableCoeff b δ d n := by
  intro n hn
  cases n with
  | zero => rfl
  | succ j =>
    apply congrArg Complex.re
    apply congrFun (logRow_congr δ d j ?_) j
    intro k hk
    apply h k
    refine hk.trans_le (Nat.pow_le_pow_left ?_ _)
    unfold precision
    omega

/-- One polynomial-size set of distinct integral ideals suffices for the whole prefix,
even when the sign is chosen after computing it. -/
theorem prefix_ideal_count (χ : U𝔽) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      (Nat.card {I : Ideal (𝓞 F) //
        (I.absNorm : ℝ) ≤ (cutoff (Module.finrank ℚ F) (2*N+1) : ℝ)} : ℝ) ≤
        C * (cutoff (Module.finrank ℚ F) (2*N+1) : ℝ) ∧
      ∀ a : ℕ → ℂ, (∀ k < cutoff (Module.finrank ℚ F) (2*N+1), a k = idealValue χ k) →
        ∀ j ≤ N, tableCoeff a (principalIndex χ) (Module.finrank ℚ F) j = finiteCoeff χ j := by
  obtain ⟨C, hC, hcount⟩ := ideal_count F
  exact ⟨C, hC, fun N ↦ ⟨hcount (2*N+1), fun _ ha ↦ tableCoeff_congr _ _ N ha⟩⟩

private theorem chosenPrefix_congr {x y : ℕ → ℝ} (N : ℕ) (neg : ℕ → Bool)
    (he : ∀ j ≤ N, x j = y j) : chosenPrefix x neg N = chosenPrefix y neg N := by
  have pos {u v : ℕ → ℝ} (h : ∀ j ≤ N, u j = v j) : positivePrefix u N = positivePrefix v N := by
    apply congrArg (fun r : ℝ ↦ 1 + r)
    apply Finset.sum_congr rfl
    intro j hj
    rw [h _ (Finset.mem_range.mp hj)]
  unfold chosenPrefix
  cases neg N
  · exact pos he
  · exact pos (fun j hj ↦ congrArg Neg.neg (he j hj))

/-- Every selected signed prefix has the same value with any norm data agreeing below the
stated cutoff. In particular the data can be extended by zero above it. -/
theorem chosenPrefix_from_finite_input (χ : U𝔽) (N : ℕ) (useFloor : Bool) (negative : ℕ → Bool)
    (a : ℕ → ℂ) (ha : ∀ k < cutoff (Module.finrank ℚ F) (2*N+1), a k = idealValue χ k) :
    chosenPrefix (prefixCoeff χ useFloor) negative N =
      chosenPrefix (fun j ↦
        let y := tableCoeff a (principalIndex χ) (Module.finrank ℚ F) j
        if useFloor then ((⌊y⌋ : ℤ) : ℝ) else y) negative N := by
  apply chosenPrefix_congr
  intro j hj
  have he := tableCoeff_congr (principalIndex χ) (Module.finrank ℚ F) N ha j hj
  change tableCoeff a _ _ j = finiteCoeff χ j at he
  simp only [he, prefixCoeff, integerCoeff]

/-- The Euler-region chart used in the finite table agrees near zero with the globally
pole-cleared analytic disk. -/
theorem ordinaryDisk_germ (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ordinaryDisk χ L 0 =ᶠ[𝓝 0] clearedDisk χ L := by
  filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1/5)] with z hz
  have hnorm : ‖z‖ ≤ 1/5 := mem_closedBall_zero_iff.mp hz
  let s := FiniteHardyIdealTable.toHalf z
  have hs : 3/2 ≤ s.re := chart_re_three_halves hnorm
  have hreg : ¬(χ = 1 ∧ s = 1) := by
    rintro ⟨_, h⟩
    rw [h] at hs
    norm_num at hs
  rw [ordinaryDisk_eq_half χ L 0 hnorm]
  change _ = HeckeDiskNormalization.cleared χ L s
  rw [HeckeDiskNormalization.cleared_agrees τ hτ χ hχ L hL he (by linarith) hreg]
  by_cases h : χ = 1 <;> simp [principalIndex, HeckeDiskNormalization.halfFactor, h, s]

private theorem logCoeff_eq (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (j : ℕ) :
    (DiskFiniteFourier.coeff (logDeriv
      (ordinaryDisk χ (finiteHeckeL_exists_continuation χ).choose 0)) j).re =
      measuredCoeff χ (j+1) := by
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have hd := (logDeriv_congr_nhds (ordinaryDisk_germ τ hτ χ hχ _ hL he)).iteratedDeriv_eq j
  change _ = (DiskLogCoefficient.coeff (logDeriv (clearedDisk χ _)) j).re
  simp only [DiskFiniteFourier.coeff, DiskLogCoefficient.coeff, hd, div_eq_mul_inv, mul_comm]

/-- The diagonal log row has eventual error at most `4⁻ʲ` for coefficient `j+1`. -/
theorem eventually_finiteCoeff_error (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) :
    ∀ᶠ j : ℕ in atTop, |finiteCoeff χ (j+1) - measuredCoeff χ (j+1)| ≤ (1/2 : ℝ)^(2*j) := by
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  filter_upwards [eventually_logRow_error τ hτ χ hχ _ hL he] with j hj
  rw [← logCoeff_eq τ hτ χ hχ j]
  exact (Complex.abs_re_le_norm _).trans (hj j le_rfl)

/-- A linear bound holds at every index for either form of the finite measurement, including
the unused index zero. Integer flooring contributes strictly less than one at positive indices. -/
theorem prefixCoeff_linear_error (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (useFloor : Bool) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, |prefixCoeff χ useFloor n - measuredCoeff χ n| ≤ C*n := by
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨C, hC, h⟩ := all_row_error (eventually_logRow_error τ hτ χ hχ _ hL he)
  refine ⟨C+1, by linarith, ?_⟩
  intro n
  cases n with
  | zero => cases useFloor <;> simp [prefixCoeff, integerCoeff, finiteCoeff, tableCoeff,
      measuredCoeff, DiskLogCoefficient.signedCoeff]
  | succ j =>
    have hraw : |finiteCoeff χ (j+1) - measuredCoeff χ (j+1)| ≤ C := by
      rw [← logCoeff_eq τ hτ χ hχ j]
      exact (Complex.abs_re_le_norm _).trans ((h j j le_rfl).trans
        (mul_le_of_le_one_right hC (pow_le_one₀ (by norm_num) (by norm_num))))
    have hround : |prefixCoeff χ useFloor (j+1) - finiteCoeff χ (j+1)| ≤ 1 := by
      cases useFloor with
      | false => simp [prefixCoeff]
      | true =>
        simp only [prefixCoeff, ite_true, integerCoeff]
        rw [abs_of_nonpos (sub_nonpos.mpr (Int.floor_le _))]
        linarith [Int.lt_floor_add_one (finiteCoeff χ (j+1))]
    calc |prefixCoeff χ useFloor (j+1) - measuredCoeff χ (j+1)|
        ≤ |prefixCoeff χ useFloor (j+1) - finiteCoeff χ (j+1)| +
          |finiteCoeff χ (j+1) - measuredCoeff χ (j+1)| := abs_sub_le _ _ _
      _ ≤ C+1 := by linarith
      _ ≤ (C+1)*(j+1 : ℕ) := le_mul_of_one_le_right (by linarith)
        (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j))

private theorem transfer_rates {x y : ℕ → ℝ} {l C : ℝ} (hC : 0 ≤ C)
    (herr : ∀ n : ℕ, |y n-x n| ≤ C*n)
    (hp : Tendsto (fun N : ℕ ↦ Real.log (positivePrefix x N)/(N:ℝ)) atTop (𝓝 l))
    (hn : Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -x n) N)/(N:ℝ)) atTop (𝓝 l)) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix y N)/(N:ℝ)) atTop (𝓝 l) ∧
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -y n) N)/(N:ℝ)) atTop (𝓝 l) := by
  refine ⟨tendsto_log_prefix_of_linear_error hC herr hp, tendsto_log_prefix_of_linear_error hC ?_ hn⟩
  intro n
  simpa only [neg_sub_neg, abs_sub_comm (x n) (y n)] using herr n

/-- Both ordinary signed prefix limits from finite ideal sums measure the nearest positive-order
site to the right of the critical line, in the Cayley disk metric. -/
theorem signed_rate_measures_nearest (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (w : RightSite χ) :
    ∃ z : RightSite χ,
      (∀ v : RightSite χ, ‖HalfPlaneJensen.toDisk z.val‖ ≤ ‖HalfPlaneJensen.toDisk v.val‖) ∧
      0 < HalfPlaneJensen.greenKernel z.val ∧ ∀ useFloor : Bool,
        Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (prefixCoeff χ useFloor) N)/(N:ℝ))
          atTop (𝓝 (HalfPlaneJensen.greenKernel z.val)) ∧
        Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -prefixCoeff χ useFloor n) N)/(N:ℝ))
          atTop (𝓝 (HalfPlaneJensen.greenKernel z.val)) := by
  obtain ⟨z, hz, hpos, hp, hn⟩ := HeckeLaguerre.signed_rate_measures_nearest τ hτ χ hχ w
  refine ⟨z, hz, hpos, fun useFloor ↦ ?_⟩
  obtain ⟨C, hC, herr⟩ := prefixCoeff_linear_error τ hτ χ hχ useFloor
  exact transfer_rates hC herr hp hn

/-- With no right-hand site, both finite-ideal signed prefix rates converge to zero. -/
theorem signed_rate_zero_of_empty (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (hempty : IsEmpty (RightSite χ)) (useFloor : Bool) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (prefixCoeff χ useFloor) N)/(N:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -prefixCoeff χ useFloor n) N)/(N:ℝ))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, herr⟩ := prefixCoeff_linear_error τ hτ χ hχ useFloor
  obtain ⟨hp, hn⟩ := HeckeLaguerre.signed_rate_zero_of_empty τ hτ χ hχ hempty
  exact transfer_rates hC herr hp hn

/-- A sign selected separately at every cutoff gives the same cofinal zero criterion. -/
theorem isEmpty_rightSite_iff_cofinal (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) (useFloor : Bool) (negative : ℕ → Bool) :
    IsEmpty (RightSite χ) ↔ ∀ ε : ℝ, 0 < ε → ∀ J : ℕ, ∃ N ≥ J,
      Real.log (chosenPrefix (prefixCoeff χ useFloor) negative N)/(N:ℝ) ≤ ε := by
  obtain ⟨C, hC, herr⟩ := prefixCoeff_linear_error τ hτ χ hχ useFloor
  exact isEmpty_rightSite_iff_cofinal_signed_of_linear_error τ hτ χ hχ _ hC herr negative

end RiemannMasullo.FiniteIdealSigned
