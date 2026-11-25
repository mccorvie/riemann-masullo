module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeHardyArithmetic
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeFiniteSignedCoefficients
import Mathlib.Analysis.PSeries
import Mathlib.Tactic

/-! # Signed Hardy energies from finite polynomial ideal tables and their integer floors -/

@[expose] public noncomputable section
open Filter Function NumberField Set
open scoped NNReal Topology
namespace RiemannMasullo.FiniteIdealSigned
open HeckeLaguerre
variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF

/-- Both the finite tables and their integer floors have square-summable errors after
division by the positive index. -/
theorem summable_prefixCoeff_normalized_error (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (useFloor : Bool) :
    Summable fun n : ℕ ↦ ((prefixCoeff χ useFloor (n+1)-measuredCoeff χ (n+1))/(n+1:ℝ))^2 := by
  have hinv : Summable (fun n : ℕ ↦ 1/(n+1:ℝ)^2) := by
    simpa only [Real.rpow_two, sq_abs] using (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  apply (hinv.mul_left 4).of_norm_bounded_eventually_nat
  filter_upwards [eventually_finiteCoeff_error τ hτ χ hχ] with n hn
  have hround : |prefixCoeff χ useFloor (n+1) - finiteCoeff χ (n+1)| ≤ 1 := by
    cases useFloor
    · simp [prefixCoeff]
    · simp only [prefixCoeff,ite_true,integerCoeff]
      rw [abs_of_nonpos (sub_nonpos.mpr (Int.floor_le _))]
      linarith [Int.lt_floor_add_one (finiteCoeff χ (n+1))]
  have hb : |prefixCoeff χ useFloor (n+1)-measuredCoeff χ (n+1)| ≤ 2 :=
    (abs_sub_le _ (finiteCoeff χ (n+1)) _).trans (by
      linarith [pow_le_one₀ (by norm_num : 0≤(1/2:ℝ)) (by norm_num : (1/2:ℝ)≤1) (n:=2*n)])
  rw [Real.norm_of_nonneg (sq_nonneg _),div_pow]
  have hh := div_le_div_of_nonneg_right (sq_le_sq.mpr (by simpa using hb : |prefixCoeff χ useFloor (n+1)-measuredCoeff χ (n+1)| ≤ |(2:ℝ)|)) (sq_nonneg (n+1:ℝ))
  convert hh using 1
  ring

/-- For each fixed sign, either version of the polynomially many finite-ideal inputs, including
integer flooring, detects critical confinement by boundedness of the square-energy prefixes. -/
theorem central_iff_bounded_table_energy (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (useFloor negative : Bool) :
    (∀ z : HeckePoisson.Site χ, z.val.re=1/2) ↔
      ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ Finset.range N, signedSquare (prefixCoeff χ useFloor) negative n ≤ C :=
  central_iff_bounded_signedSquare_of_error τ hτ χ hχ (criticalTrace_memLp τ hτ χ hχ)
    (prefixCoeff χ useFloor) (summable_prefixCoeff_normalized_error τ hτ χ hχ useFloor) negative

/-- A prefix can be evaluated from an arbitrary finite-input norm table with the correct
values below the indicated cutoff. Flooring and the sign are independent choices. -/
theorem signedSquare_prefix_from_finite_input (χ : U𝔽) (N : ℕ) (useFloor negative : Bool)
    (a : ℕ → ℂ) (ha : ∀ k < FiniteHardyIdealTable.cutoff (Module.finrank ℚ F) (2*N+1),
      a k = FiniteHardyIdealTable.idealValue χ k) :
    ∑ n ∈ Finset.range N, signedSquare (prefixCoeff χ useFloor) negative n =
    ∑ n ∈ Finset.range N, signedSquare (fun j ↦
      let y := tableCoeff a (FiniteHardyIdealTable.principalIndex χ) (Module.finrank ℚ F) j
      if useFloor then ((⌊y⌋ : ℤ) : ℝ) else y) negative n := by
  apply Finset.sum_congr rfl
  intro n hn
  have he := tableCoeff_congr (FiniteHardyIdealTable.principalIndex χ) (Module.finrank ℚ F) N ha
    (n+1) (Finset.mem_range.mp hn)
  change tableCoeff a _ _ (n+1) = finiteCoeff χ (n+1) at he
  simp only [signedSquare, he, prefixCoeff, integerCoeff]

end RiemannMasullo.FiniteIdealSigned
