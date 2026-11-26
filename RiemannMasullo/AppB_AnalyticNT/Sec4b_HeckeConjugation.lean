module

public import RiemannMasullo.Ch06_LocalGlobal.Sec3
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # Conjugation of the completed Hecke Euler product -/

public noncomputable section
open Filter Function IsDedekindDomain NumberField Set
open scoped ComplexConjugate NNReal Topology
namespace RiemannMasullo
variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽

private theorem finiteEulerFactor_conj_inverse (χ : U𝔽) (v : HeightOneSpectrum (𝓞 F)) (s : ℂ) :
    finiteHeckeEulerFactor χ⁻¹ v (conj s) = conj (finiteHeckeEulerFactor χ v s) := by
  have hres (x : v.adicCompletion F) :
      (ideleClassNormTwist χ⁻¹ 0).restrict v x = conj ((ideleClassNormTwist χ 0).restrict v x) := by
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    let u := Units.mk0 x hx
    change (ideleClassNormTwist χ⁻¹ 0).restrict v (u : v.adicCompletion F) =
      conj ((ideleClassNormTwist χ 0).restrict v (u : v.adicCompletion F))
    simp only [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (((χ _)⁻¹ : Circle) : ℂ) * _ ^ (0 : ℂ) = conj ((χ _ : ℂ) * _ ^ (0 : ℂ))
    simp only [Complex.cpow_zero,mul_one,Circle.coe_inv_eq_conj]
  have hu : (ideleClassNormTwist χ⁻¹ 0).IsUnramifiedAt v ↔ (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
    simp only [HeckeCharacter.isUnramifiedAt_iff,hres,map_eq_one_iff _ (starRingEnd ℂ).injective]
  have hv : (ideleClassNormTwist χ⁻¹ 0).localValue v = conj ((ideleClassNormTwist χ 0).localValue v) := hres _
  have hpow : conj ((v.asIdeal.absNorm : ℂ)^(-s)) = (v.asIdeal.absNorm : ℂ)^(-conj s) := by
    have h := Complex.cpow_conj (v.asIdeal.absNorm : ℂ) (-s) (by rw [Complex.natCast_arg]; exact Real.pi_ne_zero.symm)
    simpa only [map_neg,Complex.conj_natCast] using h.symm
  unfold finiteHeckeEulerFactor
  rw [hu]
  split_ifs <;> simp only [map_inv₀,map_sub,map_mul,map_one,hpow,hv]

/-- The finite right-half-plane Euler value commutes with conjugation of the argument
and inversion of a unitary character. -/
theorem finiteHeckeL_inv_conj_right (χ : U𝔽) (s : ℂ) (hs : 1 < s.re) :
    finiteHeckeL χ⁻¹ ⟨conj s,hs⟩ = conj (finiteHeckeL χ ⟨s,hs⟩) := by
  apply (finiteHeckeL_hasProd χ⁻¹ ⟨conj s,hs⟩).unique
  exact ((finiteHeckeL_hasProd χ ⟨s,hs⟩).map conj Complex.continuous_conj).congr_fun
    (fun v ↦ finiteEulerFactor_conj_inverse χ v s)

private theorem inverse_infinite_restriction (χ : U𝔽) (v : InfinitePlace F) (x : v.Completionˣ) :
    infinitePlaceRestriction F v (ideleClassNormTwist χ⁻¹ 0) x =
      (infinitePlaceRestriction F v (ideleClassNormTwist χ 0) x)⁻¹ := by
  let g := IdeleClassGroup.ofCompletion (𝓞 F) F v x
  change ((χ⁻¹ g : Circle) : ℂ) * _ ^ (0 : ℂ) = ((χ g : ℂ) * _ ^ (0 : ℂ))⁻¹
  simp only [Complex.cpow_zero,mul_one]
  rfl

private theorem real_inverse_parameters (χ : U𝔽) (v : InfinitePlace F) (hv : v.IsReal) :
    (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(realHeckeCharacter_parameters χ v hv).exists.choose.1,
        (realHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (realHeckeCharacter_parameters χ⁻¹ v hv).unique (realHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1,fun x ↦ ?_⟩
  dsimp only
  rw [inverse_infinite_restriction,ha.2 x,mul_inv,Complex.cpow_neg]
  congr 1
  rw [← inv_pow]
  split <;> simp

private theorem complex_inverse_parameters (χ : U𝔽) (v : InfinitePlace F) (hv : v.IsComplex) :
    (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose =
      (-(complexHeckeCharacter_parameters χ v hv).exists.choose.1,
        -(complexHeckeCharacter_parameters χ v hv).exists.choose.2) := by
  have ha := (complexHeckeCharacter_parameters χ v hv).exists.choose_spec
  apply (complexHeckeCharacter_parameters χ⁻¹ v hv).unique (complexHeckeCharacter_parameters χ⁻¹ v hv).exists.choose_spec
  refine ⟨by simpa using ha.1,fun x ↦ ?_⟩
  dsimp only
  rw [inverse_infinite_restriction,ha.2 x,mul_inv,Complex.cpow_neg,zpow_neg]

/-- Conjugating the global archimedean factor inverts the character and conjugates the
argument. Its complex-place degree uses the absolute angular weight. -/
theorem heckeGammaFactor_inv_conj (χ : U𝔽) (s : ℂ) :
    heckeGammaFactor χ⁻¹ (conj s) = conj (heckeGammaFactor χ s) := by
  classical
  unfold heckeGammaFactor
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro v _
  have hp {a : ℂ} (ha : a.re = 0) : conj a = -a := by
    apply Complex.ext <;> simp [ha]
  by_cases hv : v.IsReal
  · have ha := (realHeckeCharacter_parameters χ v hv).exists.choose_spec.1
    simp only [dite_eq_left hv,real_inverse_parameters,← Complex.Gammaℝ_conj,map_add,
      hp ha,Complex.conj_natCast]
  · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    have ha := (complexHeckeCharacter_parameters χ v hv').exists.choose_spec.1
    simp only [dite_eq_right hv,complex_inverse_parameters,Int.natAbs_neg,map_div₀,map_ofNat,
      ← Complex.Gammaℂ_conj,map_add,hp ha,Complex.conj_natCast]

/-- The actual completed continuations on the Euler half-plane are conjugate for inverse
unitary characters, including all finite and archimedean factors. -/
theorem continuedCompletedHeckeL_inv_conj_right (χ : U𝔽) (s : ℂ) (hs : 1<s.re) :
    continuedCompletedHeckeL χ⁻¹ (conj s) = conj (continuedCompletedHeckeL χ s) := by
  rw [(continuedCompletedHeckeL_spec χ⁻¹).2 ⟨conj s,hs⟩,(continuedCompletedHeckeL_spec χ).2 ⟨s,hs⟩]
  change heckeGammaFactor χ⁻¹ (conj s)*finiteHeckeL χ⁻¹ ⟨conj s,hs⟩ =
    conj (heckeGammaFactor χ s * finiteHeckeL χ ⟨s,hs⟩)
  rw [heckeGammaFactor_inv_conj,finiteHeckeL_inv_conj_right χ s hs,map_mul]

/-- The same right-half-plane conjugation identity holds for the complex logarithmic
derivatives of the completed continuations. -/
theorem logDeriv_continuedCompletedHeckeL_inv_conj_right (χ : U𝔽) (s : ℂ) (hs : 1<s.re) :
    logDeriv (continuedCompletedHeckeL χ⁻¹) (conj s) = conj (logDeriv (continuedCompletedHeckeL χ) s) := by
  have hopen : ∀ᶠ w : ℂ in 𝓝 (conj s), 1 < w.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (show 1 < (conj s).re from hs)
  have he : continuedCompletedHeckeL χ⁻¹ =ᶠ[𝓝 (conj s)] conj ∘ continuedCompletedHeckeL χ ∘ conj := by
    filter_upwards [hopen] with w hw
    simpa only [Function.comp_apply,Complex.conj_conj] using
      continuedCompletedHeckeL_inv_conj_right χ (conj w) hw
  simp only [logDeriv_apply,he.deriv_eq,he.eq_of_nhds,deriv_conj_conj,Function.comp_apply,Complex.conj_conj,map_div₀]

end RiemannMasullo
