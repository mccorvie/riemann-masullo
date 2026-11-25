module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeSignedHardy
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePrimeLaguerre
import Mathlib.Tactic

/-! # Signed Hardy criteria from literal raw prime-power data -/

@[expose] public noncomputable section
open Complex Filter Function NumberField MeasureTheory AddCircle
open scoped NNReal Topology
namespace RiemannMasullo.HeckeLaguerre
variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF
local instance : Fact (0 < 2*Real.pi) := ⟨by positivity⟩

/-- The normalized raw prime-power errors at cutoff `100^(n+1)` have total squared
magnitude at most `4d²/3`, for degree `d`. -/
theorem raw100_square_error (χ : U𝔽) :
    ∃ S : ℝ, HasSum (fun n : ℕ ↦ ((finiteMoment χ (n+1) (100^(n+1)) -
      measuredCoeff χ (n+1))/(n+1:ℝ))^2) S ∧ S ≤ (4/3)*(Module.finrank ℚ F:ℝ)^2 := by
  let d := (Module.finrank ℚ F : ℝ)
  let e (n : ℕ) := (finiteMoment χ (n+1) (100^(n+1)) - measuredCoeff χ (n+1))/(n+1:ℝ)
  have hd : 0≤d := Nat.cast_nonneg _
  obtain ⟨hL, he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have B (n : ℕ) : |e n| ≤ 2*d*(2:ℝ)⁻¹^(n+1) := by
    have hr := abs_actualMoment_sub_fin100 χ _ hL he (n:=n+1) (Nat.succ_pos _)
    rw [actualMoment_eq_measuredCoeff, abs_sub_comm, Nat.cast_succ] at hr
    change |(_-_)/(n+1:ℝ)| ≤ _
    rw [abs_div, abs_of_pos (by positivity : 0<(n+1:ℝ)), div_le_iff₀ (by positivity : 0<(n+1:ℝ))]
    convert hr using 1
    ring
  have hsum : HasSum (fun n : ℕ ↦ d^2*(1/4:ℝ)^n) ((4/3)*d^2) := by
    convert (hasSum_geometric_of_lt_one (by norm_num : 0≤(1/4:ℝ)) (by norm_num)).mul_left (d^2) using 1
    ring
  have hbd (n) : e n^2 ≤ d^2*(1/4:ℝ)^n := by
    calc
      e n^2 ≤ (2*d*(2:ℝ)⁻¹^(n+1))^2 := sq_le_sq.mpr (by simpa only [abs_of_nonneg (show 0≤2*d*(2:ℝ)⁻¹^(n+1) by positivity)] using B n)
      _ = _ := by rw [pow_succ (2:ℝ)⁻¹, mul_pow, mul_pow, mul_pow, pow_right_comm _ n 2]
                  norm_num
                  ring
  have hs := hsum.summable.of_nonneg_of_le (fun n ↦ sq_nonneg (e n)) hbd
  exact ⟨_,hs.hasSum,hasSum_le hbd hs.hasSum hsum⟩

/-- Each fixed sign of the finite raw prime-power table gives an independent bounded-square-sum
criterion for all sites of this character to be central. -/
theorem central_iff_bounded_raw100_signedSquare (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hu : MemLp (criticalTrace χ) 2 haarAddCircle) (negative : Bool) :
    (∀ z : HeckePoisson.Site χ, z.val.re=1/2) ↔
      ∃ C : ℝ, ∀ N : ℕ, ∑ n ∈ Finset.range N, signedSquare (fun j ↦ finiteMoment χ j (100^j)) negative n ≤ C := by
  obtain ⟨_,hs,_⟩ := raw100_square_error χ
  exact central_iff_bounded_signedSquare_of_error τ hτ χ hχ hu (fun j : ℕ ↦ finiteMoment χ j (100^j)) hs.summable negative

/-- With all sites central, the finite raw energies have a uniform upper bound in terms of
the true arithmetic second moment and the degree of the field. -/
theorem raw100_prefix_le_second_moment (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t, χ (τ t)=1) (hR : IsEmpty (HeckeHalfPlaneJensen.RightSite χ))
    (hu : MemLp (criticalTrace χ) 2 haarAddCircle) (negative : Bool) (N : ℕ) :
    ∑ n ∈ Finset.range N, signedSquare (fun j ↦ finiteMoment χ j (100^j)) negative n ≤
      4*(∫ t : ℝ, ((3/2)/(Real.pi*((3/2)^2+t^2))) *
        (Real.log ‖(finiteHeckeL_exists_continuation χ).choose ((1/2:ℂ)+t*I)‖)^2) +
      (8/3)*(Module.finrank ℚ F:ℝ)^2 := by
  let x := measuredCoeff χ
  let y (j : ℕ) := finiteMoment χ j (100^j)
  let err (n : ℕ) := ((y (n+1)-x (n+1))/(n+1:ℝ))^2
  obtain ⟨S,hS,hcap⟩ := raw100_square_error χ
  have hs : HasSum err S := hS
  have he : ∑ n ∈ Finset.range N, err n ≤ S := hs.tsum_eq ▸ hs.summable.sum_le_tsum _ (fun _ _ ↦ sq_nonneg _)
  have hx := signedSquare_prefix_le_second_moment τ hτ χ hχ hR hu negative N
  have hxy : ∑ n ∈ Finset.range N, signedSquare y negative n ≤
      ∑ n ∈ Finset.range N, (2*signedSquare x negative n+2*err n) :=
    Finset.sum_le_sum fun n _ ↦ perturb_square_le x y negative n
  rw [Finset.sum_add_distrib, ←Finset.mul_sum, ←Finset.mul_sum] at hxy
  change ∑ n ∈ Finset.range N, signedSquare y negative n ≤ _
  dsimp only [x] at hxy
  linarith

end RiemannMasullo.HeckeLaguerre
