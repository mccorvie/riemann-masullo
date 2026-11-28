module

public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Uniform strip bound from weighted boundary estimates -/
@[expose] public noncomputable section
open Complex Filter Function Set
open scoped Topology Asymptotics
namespace RiemannMasullo.PolynomialIdealSamples

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

/-- The constants and exponent in the a-priori growth condition may depend
arbitrarily on the strip. Only its explicit boundary estimates survive. -/
theorem weighted_vertical_strip (G : ℂ → ℂ) (hG : Differentiable ℂ G) {a b h K : ℝ}
    (hab : a < b) (hbase : 1 ≤ a+h) (hK : 0 ≤ K) (d : ℕ)
    (hpoly : ∃ M : ℝ, G =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im| ^ M)
    (hleft : ∀ s : ℂ, s.re = a → ‖G s‖ ≤ K*(2*‖s+(h:ℂ)‖)^d)
    (hright : ∀ s : ℂ, s.re = b → ‖G s‖ ≤ K)
    (z : ℂ) (hza : a ≤ z.re) (hzb : z.re ≤ b) :
    ‖G z‖ ≤ K*2^d*‖z+(h:ℂ)‖^d := by
  let Q (s : ℂ) := G s/(s+(h:ℂ))^d
  have hb₁ (s : ℂ) (hs : a ≤ s.re) : 1 ≤ ‖s+(h:ℂ)‖ := by
    have ht := Complex.re_le_norm (s+(h:ℂ))
    simp only [Complex.add_re,Complex.ofReal_re] at ht
    linarith
  have hne (s : ℂ) (hs : a ≤ s.re) : s+(h:ℂ) ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le (hb₁ s hs))
  have hpos (s : ℂ) (hs : a ≤ s.re) : 0 < ‖s+(h:ℂ)‖^d := pow_pos (norm_pos_iff.mpr (hne s hs)) _
  have hnQ (s : ℂ) : ‖Q s‖ = ‖G s‖/‖s+(h:ℂ)‖^d := by simp only [Q,norm_div,norm_pow]
  have hQg (s : ℂ) (hs : a ≤ s.re) : ‖Q s‖ ≤ ‖G s‖ := by
    rw [hnQ]
    exact div_le_self (norm_nonneg _) (one_le_pow₀ (hb₁ s hs))
  have hdf : DiffContOnCl ℂ Q (re ⁻¹' Ioo a b) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_preimage_re,closure_Ioo hab.ne]
    intro s hs
    exact ((hG s).div (((differentiableAt_id.add_const _).pow d))
      (pow_ne_zero d (hne s hs.1))).differentiableWithinAt
  let l := atHeight ⊓ 𝓟 (re ⁻¹' Ioo a b)
  have hheight : Tendsto (fun z : ℂ ↦ |z.im|) l atTop := tendsto_inf_left tendsto_comap
  have hQG : Q =O[l] G := by
    apply Asymptotics.IsBigO.of_bound 1
    rw [eventually_inf_principal]
    exact Eventually.of_forall (fun s hs ↦ by simpa using hQg s hs.1.le)
  obtain ⟨M,hM⟩ := hpoly
  have hM' := hM.mono (show l ≤ atHeight ⊓ 𝓟 (re ⁻¹' Icc a b) from
    inf_le_inf_left _ (principal_mono.mpr (preimage_mono Ioo_subset_Icc_self)))
  let c := Real.pi/(b-a)/2
  have h₀ : 0 < Real.pi/(b-a) := div_pos Real.pi_pos (sub_pos.mpr hab)
  have hc : 0 < c := by dsimp [c]; positivity
  have h := (isLittleO_rpow_exp_pos_mul_atTop M hc).isBigO.comp_tendsto hheight
  have hexp : (fun s : ℂ ↦ Real.exp (c*|s.im|)) =O[l] fun s ↦ Real.exp (1*Real.exp (c*|s.im|)) := by
    apply Asymptotics.IsBigO.of_bound 1 (Eventually.of_forall ?_)
    intro s
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),one_mul]
    exact Real.exp_le_exp.mpr (by linarith [Real.add_one_le_exp (c*|s.im|)])
  have hp := PhragmenLindelof.vertical_strip (a:=a) (b:=b) (f:=Q) (C:=K*2^d) (z:=z) hdf
    ⟨c,by dsimp [c]; linarith,1, ((hQG.trans hM').trans h).trans hexp⟩
  have hl (s : ℂ) (hs : s.re=a) : ‖Q s‖ ≤ K*2^d := by
    rw [hnQ,div_le_iff₀ (hpos s hs.ge)]
    simpa only [mul_pow,mul_assoc] using hleft s hs
  have hr (s : ℂ) (hs : s.re=b) : ‖Q s‖ ≤ K*2^d := by
    exact ((hQg s (hs ▸ hab.le)).trans (hright s hs)).trans
      (le_mul_of_one_le_right hK (one_le_pow₀ (by norm_num : (1:ℝ)≤2)))
  have hz := hp hl hr hza hzb
  rwa [hnQ,div_le_iff₀ (hpos z hza)] at hz

end RiemannMasullo.PolynomialIdealSamples
