module

public import RiemannMasullo.AppB_AnalyticNT.FiniteHeckeSampleData
public import RiemannMasullo.AppB_AnalyticNT.HeckeGammaShiftBound
import RiemannMasullo.AppB_AnalyticNT.Sec6
import Mathlib.Tactic

/-! # Analytic continuation and uniform boundary estimates for pole-cleared Hecke series -/

@[expose] public noncomputable section
open Complex Filter Function Set IsDedekindDomain NumberField
open scoped Topology NNReal Asymptotics

namespace RiemannMasullo.PolynomialIdealSamples
open FiniteHeckeSamples FiniteTaylor

variable {F : Type*} [Field F] [NumberField F]
local notation "Cᶠ" => IdeleClassGroup (𝓞 F) F
local notation "Uᶠ" => PontryaginDual Cᶠ
local notation "Hp" => Complex.re ⁻¹' Ioi (1 : ℝ)

private theorem finite_nf_eq_completed (χ : Uᶠ) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    toMeromorphicNFOn L univ = toMeromorphicNFOn
      (fun w ↦ (heckeGammaFactor χ w)⁻¹ * explicitFormulaCompletedHeckeL χ w) univ := by
  let Λ := explicitFormulaCompletedHeckeL χ
  let R (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let H (z : ℂ) := R z*Λ z
  obtain ⟨hΛ,hΛe⟩ := explicitFormulaCompletedHeckeL_spec χ
  have hR := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun z hz ↦ (hR.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  exact heckeEulerProductOutside_eq_finite_nf_eq L H hL.meromorphicOn hH (fun z hz ↦ by
    rw [he ⟨z,hz⟩]
    dsimp only [H,R,Λ]
    rw [hΛe ⟨z,hz⟩, completedHeckeL, finiteHeckeL,
      inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz))])

/-- At every complex point the normal-form finite function has the order of
the completed function plus the order of the entire reciprocal gamma factor. -/
theorem finite_order (χ : Uᶠ) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (s : ℂ) :
    meromorphicOrderAt L s = meromorphicOrderAt (fun w ↦ (heckeGammaFactor χ w)⁻¹) s +
      meromorphicOrderAt (explicitFormulaCompletedHeckeL χ) s := by
  let Λ := explicitFormulaCompletedHeckeL χ
  let R (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let H (z : ℂ) := R z*Λ z
  have hΛ := (explicitFormulaCompletedHeckeL_spec χ).1
  have hR := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun z hz ↦ (hR.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  have hEq : toMeromorphicNFOn L univ = toMeromorphicNFOn H univ := finite_nf_eq_completed χ L hL he
  have h := congrArg (fun f ↦ meromorphicOrderAt f s) hEq
  rw [meromorphicOrderAt_toMeromorphicNFOn hL.meromorphicOn (mem_univ _),
    meromorphicOrderAt_toMeromorphicNFOn hH (mem_univ _)] at h
  exact h.trans (meromorphicOrderAt_mul (hR.analyticAt s).meromorphicAt (hΛ (mem_univ _)).meromorphicAt)

private theorem trivial_gamma_zero : heckeGammaFactor (1 : Uᶠ) 0 = 0 := by
  have hCard := Fintype.card_pos (α := InfinitePlace F)
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces] at hCard
  have hR : Gammaℝ 0 = 0 := Gammaℝ_eq_zero_iff.mpr ⟨0, by simp⟩
  have hC : Gammaℂ 0 = 0 := by simp [Complex.Gammaℂ]
  rw [heckeGammaFactor_one,hR,hC,zero_div]
  by_cases h₁ : InfinitePlace.nrRealPlaces F = 0
  · have h₂ : InfinitePlace.nrComplexPlaces F ≠ 0 := by omega
    simp [h₂]
  · simp [h₁]

/-- The original finite normal form is analytic throughout `Re s ≤ 0`, including
the cancellation between the simple principal completed pole and a gamma pole at zero. -/
theorem finite_analytic_left (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (s : ℂ) (hs : s.re ≤ 0) : AnalyticAt ℂ L s := by
  let Λ := explicitFormulaCompletedHeckeL χ
  have hΛ := (explicitFormulaCompletedHeckeL_spec χ).1
  apply (hL (mem_univ _)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [finite_order χ L hL he s]
  by_cases hp : 0 ≤ meromorphicOrderAt Λ s
  · exact add_nonneg ((differentiable_inv_heckeGammaFactor χ).analyticAt s).meromorphicOrderAt_nonneg hp
  have hneg : meromorphicOrderAt Λ s < 0 := lt_of_not_ge hp
  have hdiv : MeromorphicOn.divisor Λ univ s < 0 := by
    rw [MeromorphicOn.divisor_apply hΛ.meromorphicOn (mem_univ _)]
    generalize meromorphicOrderAt Λ s = v at hneg ⊢
    cases v with
    | top => simp at hneg
    | coe m => exact WithTop.coe_lt_coe.mp hneg
  obtain ⟨h₁,h₂⟩ := idelicExplicitFormula_chart_poles τ hτ χ hχ s hdiv
  have hs₀ := h₂.resolve_right (fun h ↦ by norm_num [h] at hs)
  subst s
  subst χ
  have hd := (idelicExplicitFormula_trivial_poles (F := F)).1
  rw [MeromorphicOn.divisor_apply hΛ.meromorphicOn (mem_univ _)] at hd
  have hv : meromorphicOrderAt (explicitFormulaCompletedHeckeL (1:Uᶠ)) 0 = (-1 : WithTop ℤ) := by
    generalize meromorphicOrderAt (explicitFormulaCompletedHeckeL (1:Uᶠ)) 0 = v at hd ⊢
    cases v with
    | top => simp at hd
    | coe m =>
      have h : m = -1 := by simpa using hd
      rw [h]
      rfl
  have hR := (differentiable_inv_heckeGammaFactor (1:Uᶠ)).analyticAt 0
  have hpos : 0 < meromorphicOrderAt (fun w ↦ (heckeGammaFactor (1:Uᶠ) w)⁻¹) 0 :=
    lt_of_le_of_ne hR.meromorphicOrderAt_nonneg (fun h ↦
      (hR.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h.symm) (by simp [trivial_gamma_zero]))
  rw [hv]
  generalize meromorphicOrderAt (fun w ↦ (heckeGammaFactor (1:Uᶠ) w)⁻¹) 0 = v at hpos ⊢
  cases v with
  | top => simp
  | coe m =>
    have hp' := WithTop.coe_lt_coe.mp hpos
    exact WithTop.coe_le_coe.mpr (show (0:ℤ) ≤ m + (-1) by omega)

/-- The same two-term squared Dirichlet factor used on the fixed disk clears the
finite normal form on the entire plane. -/
theorem poleCleared_entire (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    Differentiable ℂ (fun w ↦ polarFactor w*L w) := by
  intro s
  by_cases hs : 0 < s.re
  · exact (analyticAt_polarFactor_mul τ hτ χ hχ L hL he s hs).differentiableAt
  have hroot : AnalyticAt ℂ polarFactor s := by
    unfold polarFactor polarRoot frequency
    fun_prop
  exact (hroot.mul (finite_analytic_left τ hτ χ hχ L hL he s (le_of_not_gt hs))).differentiableAt

local notation "atHeight" => comap (abs ∘ Complex.im) atTop

/-- Pointwise division by the completed gamma factor is legitimate on the
open left half-plane, even when a reciprocal gamma factor itself vanishes. -/
theorem finite_eq_completed_left (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (s : ℂ) (hs : s.re < 0) :
    L s = (heckeGammaFactor χ s)⁻¹*explicitFormulaCompletedHeckeL χ s := by
  let Λ := explicitFormulaCompletedHeckeL χ
  let R (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let H (z : ℂ) := R z*Λ z
  have hΛ := (explicitFormulaCompletedHeckeL_spec χ).1
  have hR := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun z hz ↦ (hR.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  have hEq : toMeromorphicNFOn L univ = toMeromorphicNFOn H univ := finite_nf_eq_completed χ L hL he
  have han : AnalyticAt ℂ Λ s := by
    apply (hΛ (mem_univ _)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_contra! hneg
    have hdiv : MeromorphicOn.divisor Λ univ s < 0 := by
      rw [MeromorphicOn.divisor_apply hΛ.meromorphicOn (mem_univ _)]
      generalize meromorphicOrderAt (explicitFormulaCompletedHeckeL χ) s = v at *
      cases v with
      | top => simp_all
      | coe m => simpa [Λ] using hneg
    rcases (idelicExplicitFormula_chart_poles τ hτ χ hχ s hdiv).2 with rfl | rfl <;> norm_num at hs
  have hAt : MeromorphicNFAt H s := ((hR.analyticAt s).mul han).meromorphicNFAt
  have e := congrFun hEq s
  rw [toMeromorphicNFOn_eq_self.mpr hL, toMeromorphicNFOn_eq_toMeromorphicNFAt hH (mem_univ s),
    toMeromorphicNFAt_eq_self.mpr hAt] at e
  exact e

theorem polarFactor_bound {a : ℝ} {s : ℂ} (hs : a ≤ s.re) :
    ‖polarFactor s‖ ≤ (1+2*Real.exp (-(Real.log 2)*a))^2 := by
  have hfreq : ‖frequency 2 s‖ ≤ Real.exp (-(Real.log 2)*a) := by
    rw [frequency,Complex.norm_exp]
    simp only [Nat.cast_ofNat,Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.ofReal_re,
      Complex.ofReal_im,neg_zero,zero_mul,sub_zero]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hs (neg_nonpos.mpr (Real.log_nonneg (by norm_num))))
  rw [polarFactor,norm_pow,polarRoot]
  apply pow_le_pow_left₀ (norm_nonneg _)
  exact (norm_sub_le _ _).trans (by simp only [norm_one,norm_mul,Complex.norm_two]; linarith)

theorem polarFactor_halfInteger {m : ℕ} {s : ℂ} (hs : 1/2-(m:ℝ) ≤ s.re) :
    ‖polarFactor s‖ ≤ 9*(4:ℝ)^m := by
  have h := polarFactor_bound (a:= -(m:ℝ)) (s:=s) (by linarith)
  rw [show -(Real.log 2)*(-(m:ℝ)) = (m:ℝ)*Real.log 2 by ring,
    Real.exp_nat_mul,Real.exp_log (by norm_num)] at h
  have hh : 1 ≤ (2:ℝ)^m := one_le_pow₀ (by norm_num)
  have e : (4:ℝ)^m = ((2:ℝ)^m)^2 := by rw [← pow_mul, Nat.mul_comm, pow_mul]; norm_num
  rw [e]
  exact h.trans (by nlinarith [mul_nonneg (sub_nonneg.mpr hh) (show 0 ≤ 5*(2:ℝ)^m+1 by positivity)])

theorem poleCleared_polynomial_growth (χ : Uᶠ) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {a b : ℝ} (hab : a < b) :
    ∃ M : ℝ, (fun s ↦ polarFactor s*L s) =O[atHeight ⊓ 𝓟 (re ⁻¹' Icc a b)] fun s ↦ |s.im|^M := by
  obtain ⟨M,_,hm⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL he a b hab
  refine ⟨M,Asymptotics.IsBigO.trans (g:=L) ?_ hm⟩
  apply Asymptotics.IsBigO.of_bound ((1+2*Real.exp (-(Real.log 2)*a))^2)
  rw [eventually_inf_principal]
  exact Eventually.of_forall (fun s hs ↦ by rw [norm_mul]; gcongr; exact polarFactor_bound hs.1)

/-- Constants precede both the half-integer width and the height. The right
bound is on the whole right half-plane. -/
theorem poleCleared_boundary_bounds (τ : ℝ≥0ˣ →ₜ* Cᶠ) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Uᶠ) (hχ : ∀ t, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    ∃ B K : ℝ, 1 ≤ B ∧ 1 ≤ K ∧
      (∀ s : ℂ, 2 ≤ s.re → ‖polarFactor s*L s‖ ≤ K) ∧
      ∀ (m : ℕ), 1 ≤ m → ∀ s : ℂ, s.re = 1/2-(m:ℝ) →
        ‖polarFactor s*L s‖ ≤ K^(m+1)*(B+3*(m:ℝ)+|s.im|)^(Module.finrank ℚ F*m) := by
  let Λ := explicitFormulaCompletedHeckeL χ
  let Λd := explicitFormulaCompletedHeckeL χ⁻¹
  obtain ⟨hl,hd⟩ := explicitFormulaCompletedHeckeL_spec χ
  obtain ⟨hl',hd'⟩ := explicitFormulaCompletedHeckeL_spec χ⁻¹
  obtain ⟨c,hc,hfe⟩ := completedHeckeL_functionalEquation_conductorScale χ Λ Λd hl hd hl' hd'
  obtain ⟨B,hB,hγ⟩ := norm_heckeGammaRatio_halfInteger χ
  let Q := Real.exp (heckeLogDiscriminantConductor χ)
  let Z := ‖dedekindZeta F (3/2:ℝ)‖
  let K := max (max 1 (9*Z)) (max (9*‖c⁻¹‖*Z) (4*Q))
  have k1 : 1 ≤ K := (le_max_left ..).trans (le_max_left ..)
  have k2 : 9*Z ≤ K := (le_max_right ..).trans (le_max_left ..)
  have k3 : 9*‖c⁻¹‖*Z ≤ K := (le_max_left ..).trans (le_max_right ..)
  have k4 : 4*Q ≤ K := (le_max_right ..).trans (le_max_right ..)
  have euler (η : Uᶠ) (s : Hp) (hs : 3/2 ≤ (s:ℂ).re) : ‖finiteHeckeL η s‖ ≤ Z :=
    (finiteHeckeL_zeroFreeRegion_euler F η s (by norm_num) hs).1
  refine ⟨B,K,hB,k1,?_,?_⟩
  · intro s hs
    have hz : 1 < s.re := by linarith
    rw [he ⟨s,hz⟩,norm_mul]
    refine (mul_le_mul ?_ (euler χ ⟨s,hz⟩ (by dsimp; linarith)) (norm_nonneg _) (by norm_num : (0:ℝ)≤9)).trans k2
    simpa using (polarFactor_halfInteger (m:=0) (s:=s) (by norm_num; linarith))
  · intro m hm s hs
    have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
    have hz : 1 < (1-s).re := by rw [Complex.sub_re,Complex.one_re,hs]; linarith
    let v : Hp := ⟨1-s,hz⟩
    have hv : (3:ℝ)/2 ≤ (v:ℂ).re := by change 3/2 ≤ 1-s.re; linarith
    let E := Complex.exp ((heckeLogDiscriminantConductor χ:ℂ)*(s-1/2))
    have eE : E ≠ 0 := Complex.exp_ne_zero _
    have ef : Λ s = (c⁻¹*E⁻¹)*Λd (1-s) := by
      rw [hfe]
      change _ = (c⁻¹*E⁻¹)*(c*E*_)
      field_simp
    have lv : Λd (1-s) = heckeGammaFactor χ⁻¹ (1-s)*finiteHeckeL χ⁻¹ v := hd' v
    have eL : L s = c⁻¹*E⁻¹ * finiteHeckeL χ⁻¹ v * (heckeGammaFactor χ⁻¹ (1-s)/heckeGammaFactor χ s) := by
      rw [finite_eq_completed_left τ hτ χ hχ L hL he s (by linarith)]
      change _ * Λ s = _
      rw [ef,lv,div_eq_mul_inv]
      ring
    have eQ : ‖E⁻¹‖ = Q^m := by
      rw [norm_inv,show ‖E‖ = Real.exp (-(m:ℝ)*heckeLogDiscriminantConductor χ) by
        dsimp only [E]
        rw [Complex.norm_exp]
        congr 1
        simp [Complex.mul_re, Complex.sub_re, hs]; ring,
        ← Real.exp_neg]
      dsimp [Q]
      rw [neg_mul,neg_neg,Real.exp_nat_mul]
    have eZ : 0 ≤ Z := norm_nonneg _
    have eQ' : 0 ≤ Q := (Real.exp_pos _).le
    have hzq : 0 ≤ B+3*(m:ℝ)+|s.im| := by linarith [abs_nonneg s.im]
    rw [eL,norm_mul,norm_mul,norm_mul,norm_mul,eQ]
    calc _ ≤ (9*4^m) * (‖c⁻¹‖*Q^m*Z*(B+3*(m:ℝ)+|s.im|)^(Module.finrank ℚ F*m)) := by
                gcongr
                · exact polarFactor_halfInteger hs.ge
                · exact euler _ _ hv
                · exact hγ m s hs
         _ = ((9*‖c⁻¹‖*Z)*(4*Q)^m)*(B+3*(m:ℝ)+|s.im|)^(Module.finrank ℚ F*m) := by
                rw [mul_pow]; ring
         _ ≤ _ := by rw [pow_succ']; gcongr

end RiemannMasullo.PolynomialIdealSamples
