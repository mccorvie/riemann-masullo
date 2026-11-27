module

public import RiemannMasullo.AppB_AnalyticNT.Sec6
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_HeckeReflection
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.DigammaGrowth

/-! # Growth of the completed Hecke logarithmic derivative in the outer half-planes -/

public noncomputable section

open Classical Filter NumberField Set
open scoped ComplexConjugate Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => (Complex.re ⁻¹' Ioi (1 : ℝ))

private def outerLogWeight (z : ℂ) : ℝ := 1 + Real.log (2 + ‖z‖)

private theorem one_le_outerLogWeight (z : ℂ) : 1 ≤ outerLogWeight z := by
  have h := Real.log_nonneg (by linarith [norm_nonneg z] : 1 ≤ 2 + ‖z‖)
  dsimp only [outerLogWeight]
  linarith

/-- A fixed shift in the argument is absorbed by a constant depending only on its norm. -/
private theorem outerLogWeight_shift (s b z : ℂ) (hz : ‖z‖ ≤ ‖s‖ + ‖b‖) :
    outerLogWeight z ≤ (1 + Real.log (1 + ‖b‖)) * outerLogWeight s := by
  have hb : 0 ≤ Real.log (1 + ‖b‖) := Real.log_nonneg (by linarith [norm_nonneg b])
  have hs : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
  have hle : 2 + ‖z‖ ≤ (2 + ‖s‖) * (1 + ‖b‖) := by
    nlinarith only [hz, norm_nonneg b, mul_nonneg (norm_nonneg s) (norm_nonneg b)]
  have hlog := Real.log_le_log (by positivity) hle
  rw [Real.log_mul (by positivity) (by positivity)] at hlog
  dsimp only [outerLogWeight]
  nlinarith only [hlog, mul_nonneg hb hs]

/-- The single absolutely converging ideal series at two dominates the modulus
of the finite logarithmic derivative throughout the closed Euler half-plane. -/
private theorem finiteHeckeL_logDeriv_uniform_two (χ : U𝔽) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ) (hSeries : ∀ z : halfPlane, L z = finiteHeckeL χ z) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, 2 ≤ s.re → ‖logDeriv L s‖ ≤ M := by
  let term (s : ℂ) (I : {a : Ideal (𝓞 F) // a ≠ ⊥}) : ℂ :=
    -heckeIdealVonMangoldt (ideleClassNormTwist χ 0) I.val / (I.val.absNorm : ℂ) ^ s
  have hsum (s : ℂ) (hs : 1 < s.re) : HasSum (term s) (logDeriv L s) :=
    (finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨s, hs⟩).2.2
  have absTwo := (hsum 2 (by norm_num)).summable.norm
  refine ⟨∑' I, ‖term 2 I‖, tsum_nonneg fun _ ↦ norm_nonneg _, ?_⟩
  intro s hs
  rw [← (hsum s (one_lt_two.trans_le hs)).tsum_eq]
  apply tsum_of_norm_bounded absTwo.hasSum
  intro I
  let q : ℝ := I.val.absNorm
  have hqN : 1 ≤ I.val.absNorm := Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
  have hq : 1 ≤ q := by
    dsimp only [q]
    exact_mod_cast hqN
  have hqpos := zero_lt_one.trans_le hq
  change ‖-heckeIdealVonMangoldt _ I.val / (q : ℂ) ^ s‖ ≤
    ‖-heckeIdealVonMangoldt _ I.val / (q : ℂ) ^ (2 : ℂ)‖
  rw [norm_div, norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hqpos,
    Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
  apply div_le_div_of_nonneg_left (norm_nonneg _) (Real.rpow_pos_of_pos hqpos _)
  exact Real.rpow_le_rpow_of_exponent_le hq (by simpa using hs)

/-- Both local Gamma factors have the form `exp(c z) Γ(z)` at an affine argument. -/
private def affineGamma (k : ℝ) (b c s : ℂ) : ℂ :=
  let z := (k : ℂ) * (s + b)
  Complex.exp (c * z) * Complex.Gamma z

private theorem affineGamma_logDeriv_bound (δ k : ℝ) (hδ : 0 < δ) (hk : 0 < k)
    (hk₁ : k ≤ 1) (b c : ℂ) (hb : 0 ≤ b.re) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, δ ≤ s.re →
      affineGamma k b c s ≠ 0 ∧ DifferentiableAt ℂ (affineGamma k b c) s ∧
      ‖logDeriv (affineGamma k b c) s‖ ≤ C * outerLogWeight s := by
  obtain ⟨D, hD, hψ⟩ := Complex.exists_pos_norm_digamma_le_log (k * δ) (mul_pos hk hδ)
  let A := 1 + Real.log (1 + ‖b‖)
  have hA : 0 ≤ A := by
    dsimp only [A]
    linarith [Real.log_nonneg (by linarith [norm_nonneg b] : 1 ≤ 1 + ‖b‖)]
  refine ⟨‖c‖ + D * A, add_nonneg (norm_nonneg _) (mul_nonneg hD.le hA), ?_⟩
  intro s hs
  let z (w : ℂ) := (k : ℂ) * (w + b)
  let E (w : ℂ) := Complex.exp (c * z w)
  have hz : k * δ ≤ (z s).re := by
    simp only [z, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      Complex.add_re]
    exact mul_le_mul_of_nonneg_left (by linarith) hk.le
  have hpos : 0 < (z s).re := (mul_pos hk hδ).trans_le hz
  have hz' : HasDerivAt z (k : ℂ) s := by
    simpa only [mul_one] using ((hasDerivAt_id' s).add_const b).const_mul (k : ℂ)
  have hE := (hz'.const_mul c).cexp
  have hG := (Complex.hasDerivAt_Gamma_of_re_pos hpos).differentiableAt
  have hE₀ : E s ≠ 0 := Complex.exp_ne_zero _
  have hG₀ := Complex.Gamma_ne_zero_of_re_pos hpos
  have hG' : DifferentiableAt ℂ (Complex.Gamma ∘ z) s := hG.comp s hz'.differentiableAt
  refine ⟨mul_ne_zero hE₀ hG₀, hE.differentiableAt.mul hG', ?_⟩
  have hlog : logDeriv (affineGamma k b c) s = (c + Complex.digamma (z s)) * k := by
    change logDeriv (fun w ↦ E w * (Complex.Gamma ∘ z) w) s = _
    rw [logDeriv_fun_mul s hE₀ hG₀ hE.differentiableAt hG',
      logDeriv_comp hG hz'.differentiableAt, hz'.deriv]
    have hE' : deriv E s = E s * (c * (k : ℂ)) := hE.deriv
    rw [logDeriv_apply E, hE', mul_div_cancel_left₀ _ hE₀]
    change c * _ + Complex.digamma (z s) * _ = _
    ring
  have hnorm : ‖z s‖ ≤ ‖s‖ + ‖b‖ := by
    change ‖(k : ℂ) * (s + b)‖ ≤ _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
    exact (mul_le_of_le_one_left (norm_nonneg _) hk₁).trans (norm_add_le _ _)
  have hψ' : ‖Complex.digamma (z s)‖ ≤ D * (A * outerLogWeight s) :=
    (hψ (z s) hz).trans
      (mul_le_mul_of_nonneg_left (outerLogWeight_shift s b (z s) hnorm) hD.le)
  rw [hlog, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk]
  calc
    _ ≤ ‖c + Complex.digamma (z s)‖ := mul_le_of_le_one_right (norm_nonneg _) hk₁
    _ ≤ ‖c‖ + ‖Complex.digamma (z s)‖ := norm_add_le _ _
    _ ≤ ‖c‖ * outerLogWeight s + D * (A * outerLogWeight s) :=
      add_le_add (le_mul_of_one_le_right (norm_nonneg _) (one_le_outerLogWeight s)) hψ'
    _ = (‖c‖ + D * A) * outerLogWeight s := by ring

/-- For a unitary idèle class character, the logarithmic derivative of the full archimedean
factor grows logarithmically on every closed half-plane with positive lower real part. -/
theorem heckeGammaFactor_logDeriv_bound_of_re_ge (χ : U𝔽) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, δ ≤ s.re →
      ‖logDeriv (heckeGammaFactor χ) s‖ ≤ C * (1 + Real.log (2 + ‖s‖)) := by
  let G (v : InfinitePlace F) (s : ℂ) : ℂ :=
    if hv : v.IsReal then
      let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      Complex.Gammaℝ (s + a.1 + (a.2.val : ℂ))
    else
      let a := (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose
      Complex.Gammaℂ (s + a.1 + (a.2.natAbs : ℂ) / 2) / 2
  have local_bound (v : InfinitePlace F) : ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, δ ≤ s.re →
      G v s ≠ 0 ∧ DifferentiableAt ℂ (G v) s ∧ ‖logDeriv (G v) s‖ ≤ C * outerLogWeight s := by
    by_cases hv : v.IsReal
    · let a := (realHeckeCharacter_parameters χ v hv).exists.choose
      let b := a.1 + (a.2.val : ℂ)
      have hb : 0 ≤ b.re := by
        have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
        change a.1.re = 0 at ha
        simp only [b, Complex.add_re, Complex.natCast_re, ha, zero_add]
        positivity
      have he : G v = fun z ↦ Complex.Gammaℝ (z + b) := by
        funext z
        simp only [G, dite_eq_left hv, b, a, add_assoc]
      rw [he]
      have hΓ : (fun z ↦ Complex.Gammaℝ (z + b)) =
          affineGamma (1 / 2) b (-Complex.log (Real.pi : ℂ)) := by
        funext z
        rw [Complex.Gammaℝ_def,
          Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)]
        simp only [affineGamma, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
        congr 1 <;> congr 1 <;> ring
      rw [hΓ]
      exact affineGamma_logDeriv_bound δ (1 / 2) hδ (by norm_num) (by norm_num) b _ hb
    · let hw := InfinitePlace.not_isReal_iff_isComplex.mp hv
      let a := (complexHeckeCharacter_parameters χ v hw).exists.choose
      let b := a.1 + (a.2.natAbs : ℂ) / 2
      have hb : 0 ≤ b.re := by
        have ha := (complexHeckeCharacter_parameters χ v hw).exists.choose_spec.1
        change a.1.re = 0 at ha
        simp only [b, Complex.add_re, Complex.div_ofNat_re, Complex.natCast_re, ha, zero_add]
        positivity
      have he : G v = fun z ↦ Complex.Gammaℂ (z + b) / 2 := by
        funext z
        simp only [G, dite_eq_right hv, b, a, add_assoc]
      have hΓ : (fun z ↦ Complex.Gammaℂ (z + b) / 2) =
          affineGamma 1 b (-Complex.log (2 * (Real.pi : ℂ))) := by
        funext z
        rw [Complex.Gammaℂ_def, Complex.cpow_def_of_ne_zero
          (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))]
        simp only [affineGamma, Complex.ofReal_one, one_mul, neg_mul, mul_neg]
        ring
      rw [he, hΓ]
      exact affineGamma_logDeriv_bound δ 1 hδ zero_lt_one le_rfl b _ hb
  choose C hC hb using local_bound
  have hsum : 0 ≤ ∑ v, C v := Finset.sum_nonneg fun v _ ↦ hC v
  refine ⟨1 + ∑ v, C v, by linarith, ?_⟩
  intro s hs
  have hprod : ‖logDeriv (heckeGammaFactor χ) s‖ ≤ (∑ v, C v) * outerLogWeight s := by
    change ‖logDeriv (fun z ↦ ∏ v, G v z) s‖ ≤ _
    rw [logDeriv_fun_prod (fun v _ ↦ (hb v s hs).1) (fun v _ ↦ (hb v s hs).2.1), Finset.sum_mul]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun v _ ↦ (hb v s hs).2.2)
  exact hprod.trans (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans (one_le_outerLogWeight s)))

private theorem norm_inverse_pair_le_two (s : ℂ) (hs : 2 ≤ s.re) :
    ‖1 / s + 1 / (s - 1)‖ ≤ 2 := by
  have hinv (z : ℂ) (hz : 1 ≤ z.re) : ‖1 / z‖ ≤ 1 := by
    have hn := hz.trans (Complex.re_le_norm z)
    rw [norm_div, norm_one]
    exact (div_le_one (zero_lt_one.trans_le hn)).mpr hn
  have h1 := hinv s (by linarith)
  have h2 := hinv (s - 1) (by rw [Complex.sub_re, Complex.one_re]; linarith)
  linarith [norm_add_le (1 / s) (1 / (s - 1))]

/-- For every unitary idèle class character, the pole-corrected logarithmic derivative
of its actual completed Hecke continuation has uniform logarithmic growth on `Re s ≥ 2`. -/
theorem completedHeckeL_poleCleared_logDeriv_bound_right (χ : U𝔽) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 2 ≤ s.re →
      ‖logDeriv (continuedCompletedHeckeL χ) s + (if χ = 1 then 1 / s + 1 / (s - 1) else 0)‖ ≤
        C * (1 + Real.log (2 + ‖s‖)) := by
  obtain ⟨L, hL, hSeries⟩ := finiteHeckeL_exists_continuation χ
  obtain ⟨M, hM, hm⟩ := finiteHeckeL_logDeriv_uniform_two χ L hL hSeries
  obtain ⟨A, hA, ha⟩ := heckeGammaFactor_logDeriv_bound_of_re_ge χ 2 (by norm_num)
  refine ⟨A + (M + 2), by linarith, ?_⟩
  intro s hs
  have hright : 1 < s.re := one_lt_two.trans_le hs
  have hpos := zero_lt_one.trans hright
  have heq : continuedCompletedHeckeL χ =ᶠ[𝓝 s] fun w ↦ heckeGammaFactor χ w * L w := by
    have hopen : IsOpen halfPlane := isOpen_Ioi.preimage Complex.continuous_re
    filter_upwards [hopen.mem_nhds (show s ∈ halfPlane from hright)] with w hw
    have h : L w = finiteHeckeL χ ⟨w, hw⟩ := hSeries ⟨w, hw⟩
    rw [h]
    exact (continuedCompletedHeckeL_spec χ).2 ⟨w, hw⟩
  have hf := finiteHeckeL_logDeriv_hasSum_ideals χ L hL hSeries ⟨s, hright⟩
  have hprod : logDeriv (continuedCompletedHeckeL χ) s =
      logDeriv (heckeGammaFactor χ) s + logDeriv L s := by
    exact (logDeriv_congr_nhds heq).eq_of_nhds.trans (logDeriv_fun_mul s
      (heckeGammaFactor_ne_zero_of_re_pos χ hpos) hf.2.1
      (differentiableAt_heckeGammaFactor_of_re_pos χ hpos) hf.1.differentiableAt)
  have hcorr : ‖(if χ = 1 then 1 / s + 1 / (s - 1) else 0 : ℂ)‖ ≤ 2 := by
    split_ifs
    · exact norm_inverse_pair_le_two s hs
    · norm_num
  rw [hprod]
  calc
    _ ≤ (‖logDeriv (heckeGammaFactor χ) s‖ + ‖logDeriv L s‖) +
          ‖(if χ = 1 then 1 / s + 1 / (s - 1) else 0 : ℂ)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))
    _ ≤ A * outerLogWeight s + M + 2 := add_le_add (add_le_add (ha s hs) (hm s hs)) hcorr
    _ ≤ A * outerLogWeight s + (M + 2) * outerLogWeight s := by
      linarith [le_mul_of_one_le_right (by linarith : 0 ≤ M + 2) (one_le_outerLogWeight s)]
    _ = (A + (M + 2)) * (1 + Real.log (2 + ‖s‖)) := (add_mul A (M + 2) (outerLogWeight s)).symm

/-- Reflection in the functional equation transfers the same growth estimate to
`Re s ≤ -1`; the conductor logarithm contributes a constant depending on the character. -/
theorem completedHeckeL_poleCleared_logDeriv_bound_left (χ : U𝔽) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ≤ -1 →
      ‖logDeriv (continuedCompletedHeckeL χ) s + (if χ = 1 then 1 / s + 1 / (s - 1) else 0)‖ ≤
        C * (1 + Real.log (2 + ‖s‖)) := by
  let P (w : ℂ) := logDeriv (continuedCompletedHeckeL χ) w +
    (if χ = 1 then 1 / w + 1 / (w - 1) else 0)
  let A := 1 + Real.log (1 + ‖(1 : ℂ)‖)
  let B := ‖(heckeLogDiscriminantConductor χ : ℂ)‖
  have hA : 0 < A := by
    dsimp only [A]
    linarith [Real.log_nonneg (by norm_num : 1 ≤ 1 + ‖(1 : ℂ)‖)]
  obtain ⟨C, hC, hbound⟩ := completedHeckeL_poleCleared_logDeriv_bound_right χ
  refine ⟨C * A + B, add_pos_of_pos_of_nonneg (mul_pos hC hA) (norm_nonneg _), ?_⟩
  intro s hs
  let z := 1 - conj s
  have hz : 2 ≤ z.re := by
    simp only [z, Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith
  have hmirror : 1 - conj z = s := by simp [z]
  have href := completedHeckeL_poleCleared_logDeriv_reflection χ z (one_lt_two.trans_le hz)
  change P (1 - conj z) = -conj (P z) - (heckeLogDiscriminantConductor χ : ℂ) at href
  rw [hmirror] at href
  have hnorm : ‖z‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := by
    simpa only [z, Complex.norm_conj, add_comm] using norm_sub_le (1 : ℂ) (conj s)
  have hw : outerLogWeight z ≤ A * outerLogWeight s := outerLogWeight_shift s 1 z hnorm
  have hB : B ≤ B * outerLogWeight s := le_mul_of_one_le_right (norm_nonneg _) (one_le_outerLogWeight s)
  change ‖P s‖ ≤ (C * A + B) * outerLogWeight s
  calc
    ‖P s‖ ≤ ‖P z‖ + B := by
      rw [href]
      simpa only [norm_neg, Complex.norm_conj, B] using
        norm_sub_le (-conj (P z)) (heckeLogDiscriminantConductor χ : ℂ)
    _ ≤ C * (A * outerLogWeight s) + B * outerLogWeight s :=
      add_le_add ((hbound z hz).trans (mul_le_mul_of_nonneg_left hw hC.le)) hB
    _ = (C * A + B) * outerLogWeight s := by ring

/-- One character-dependent constant works on the union of the two closed outer half-planes. -/
theorem completedHeckeL_poleCleared_logDeriv_bound_outer (χ : U𝔽) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ≤ -1 ∨ 2 ≤ s.re →
      ‖logDeriv (continuedCompletedHeckeL χ) s + (if χ = 1 then 1 / s + 1 / (s - 1) else 0)‖ ≤
        C * (1 + Real.log (2 + ‖s‖)) := by
  obtain ⟨A, hA, ha⟩ := completedHeckeL_poleCleared_logDeriv_bound_left χ
  obtain ⟨B, _, hb⟩ := completedHeckeL_poleCleared_logDeriv_bound_right χ
  refine ⟨max A B, hA.trans_le (le_max_left _ _), ?_⟩
  intro s hs
  have hw : 0 ≤ 1 + Real.log (2 + ‖s‖) := zero_le_one.trans (one_le_outerLogWeight s)
  rcases hs with hs | hs
  · exact (ha s hs).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hw)
  · exact (hb s hs).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hw)

end RiemannMasullo
