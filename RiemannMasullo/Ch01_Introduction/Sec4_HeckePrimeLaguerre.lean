module

public import RiemannMasullo.AppB_AnalyticNT.Sec7b_HeckeLaguerre
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeSignedCoefficients
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # Signed growth of finite prime-power measurements of the ordinary Hecke L-function -/

@[expose] public noncomputable section

open Complex Filter Function NumberField
open scoped Topology
open scoped NNReal
namespace RiemannMasullo.HeckeLaguerre

open HeckeHalfPlaneJensen HalfPlaneJensen SignedFrequency
variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF

/-- The arithmetic and divisor constructions use the same ordinary logarithmic jet. -/
theorem actualMoment_eq_measuredCoeff (χ : U𝔽) :
    actualMoment χ (finiteHeckeL_exists_continuation χ).choose = measuredCoeff χ := by
  funext n
  cases n <;> rfl

/-- Transfer either orientation between the finite and the true-value normalized prefixes. -/
theorem raw_ideal_prefix_limit_iff (χ : U𝔽) (X : ℕ → ℕ)
    (hX : ∀ n, 0 < n → 25^n ≤ X n) (e : ℝ) (hes : |e| ≤ 1) (G : ℝ) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ e*finiteMoment χ n (X n)) N)/(N:ℝ)) atTop (𝓝 G) ↔
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ e*measuredCoeff χ n) N)/(N:ℝ)) atTop (𝓝 G) := by
  let C := 2*(Module.finrank ℚ F:ℝ)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have h (n : ℕ) : |e*finiteMoment χ n (X n)-e*measuredCoeff χ n| ≤ C*n := by
    rw [← actualMoment_eq_measuredCoeff]
    exact abs_canonical_signed_error χ X hX e hes n
  constructor
  · exact tendsto_log_prefix_of_linear_error (x := fun n ↦ e*finiteMoment χ n (X n))
      (y := fun n ↦ e*measuredCoeff χ n) hC (fun n ↦ (abs_sub_comm _ _).le.trans (h n))
  · exact tendsto_log_prefix_of_linear_error (x := fun n ↦ e*measuredCoeff χ n)
      (y := fun n ↦ e*finiteMoment χ n (X n)) hC h

/-- For a genuine right-hand site the positive and negative raw finite-ideal
prefixes have the common attained nearest-site Green weight as ordinary limit. -/
theorem raw_ideal_prefixes_measure_nearest (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (w : RightSite χ)
    (X : ℕ → ℕ) (hX : ∀ n, 0 < n → 25^n ≤ X n) :
    ∃ z : RightSite χ, (∀ v : RightSite χ, ‖toDisk z.val‖ ≤ ‖toDisk v.val‖) ∧
      0 < greenKernel z.val ∧
      Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ finiteMoment χ n (X n)) N)/(N:ℝ))
        atTop (𝓝 (greenKernel z.val)) ∧
      Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -finiteMoment χ n (X n)) N)/(N:ℝ))
        atTop (𝓝 (greenKernel z.val)) := by
  obtain ⟨z,hmin,hpos,hp,hn⟩ := signed_rate_measures_nearest τ hτ χ hχ w
  refine ⟨z,hmin,hpos,?_,?_⟩
  · simpa only [one_mul] using (raw_ideal_prefix_limit_iff χ X hX 1 (by norm_num) _).2
      (by simpa only [one_mul] using hp)
  · simpa only [neg_one_mul] using (raw_ideal_prefix_limit_iff χ X hX (-1) (by norm_num) _).2
      (by simpa only [neg_one_mul] using hn)

/-- If there are no genuine right-hand sites, both raw finite-ideal prefixes
have ordinary logarithmic growth rate zero. -/
theorem raw_ideal_prefixes_zero_of_empty (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (hR : IsEmpty (RightSite χ))
    (X : ℕ → ℕ) (hX : ∀ n, 0 < n → 25^n ≤ X n) :
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ finiteMoment χ n (X n)) N)/(N:ℝ)) atTop (𝓝 0) ∧
    Tendsto (fun N : ℕ ↦ Real.log (positivePrefix (fun n ↦ -finiteMoment χ n (X n)) N)/(N:ℝ)) atTop (𝓝 0) := by
  obtain ⟨hp,hn⟩ := signed_rate_zero_of_empty τ hτ χ hχ hR
  constructor
  · simpa only [one_mul] using (raw_ideal_prefix_limit_iff χ X hX 1 (by norm_num) _).2
      (by simpa only [one_mul] using hp)
  · simpa only [neg_one_mul] using (raw_ideal_prefix_limit_iff χ X hX (-1) (by norm_num) _).2
      (by simpa only [neg_one_mul] using hn)

/-- The sign can be chosen anew at every cutoff. Arbitrarily small normalized log
prefixes at arbitrarily large cutoffs characterize absence of right-hand sites. -/
theorem isEmpty_rightSite_iff_cofinal_raw_ideal
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (X : ℕ → ℕ) (hX : ∀ n, 0 < n → 25^n ≤ X n)
    (negative : ℕ → Bool) :
    IsEmpty (RightSite χ) ↔ ∀ ε : ℝ, 0 < ε → ∀ J : ℕ, ∃ N ≥ J,
      Real.log (chosenPrefix (fun n ↦ finiteMoment χ n (X n)) negative N)/(N:ℝ) ≤ ε := by
  apply isEmpty_rightSite_iff_cofinal_signed_of_linear_error τ hτ χ hχ _
    (C := 2*(Module.finrank ℚ F:ℝ)) (by positivity) _ negative
  intro n
  simpa only [one_mul, actualMoment_eq_measuredCoeff] using
    abs_canonical_signed_error χ X hX 1 (by norm_num) n

/-- Reflection gives the corresponding equivalence with centrality of every actual site. -/
theorem all_sites_central_iff_cofinal_raw_ideal
    (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u)=1) (X : ℕ → ℕ) (hX : ∀ n, 0 < n → 25^n ≤ X n)
    (negative : ℕ → Bool) :
    (∀ z : HeckePoisson.Site χ, z.val.re=1/2) ↔ ∀ ε : ℝ, 0 < ε → ∀ J : ℕ, ∃ N ≥ J,
      Real.log (chosenPrefix (fun n ↦ finiteMoment χ n (X n)) negative N)/(N:ℝ) ≤ ε :=
  (isEmpty_rightSite_iff_central χ).symm.trans
    (isEmpty_rightSite_iff_cofinal_raw_ideal τ hτ χ hχ X hX negative)

end RiemannMasullo.HeckeLaguerre
