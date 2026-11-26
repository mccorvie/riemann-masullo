module

public import RiemannMasullo.Ch01_Introduction.Sec4_RationalPoissonBounds
public import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero

/-! # A rational principal zero in the unit cell centered at fourteen

Thomas Lince's ZetaLab sign certificate supplies the critical-line witness
between 14.13 and 14.14. The bracket deficit of Hiary, Ireland and Kyi
(2024, §5) then tests for other divisor copies in the whole closed cell.
-/

public section

open NumberField Set

namespace RiemannMasullo

local notation "χ₀" => (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
local notation "Sites" => {z : ℂ // 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ₀) univ z}
local notation "point(" t ")" => (1 / 2 + (t : ℂ) * Complex.I : ℂ)

/-- A certified ordinary zeta zero on the critical line is a positive integer divisor site
for the completed rational principal Hecke function. -/
theorem rational_principal_divisor_pos_of_critical_zeta_zero (t : ℝ)
    (hz : riemannZeta point(t) = 0) :
    0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ₀) univ point(t) := by
  let z := point(t)
  have hre : z.re = 1 / 2 := by norm_num [z, Complex.div_ofNat_re]
  have hne : z ≠ 1 := fun he ↦ by norm_num [he] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hcmp := meromorphicOrderAt_finiteHeckeL_continuation χ₀ hm (fun s ↦ by
    rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property])
    (s := z) (by rw [hre]; norm_num)
  have ha := analyticOn_riemannZeta z hne
  have hpos : 0 < meromorphicOrderAt riemannZeta z := lt_of_le_of_ne ha.meromorphicOrderAt_nonneg
    (fun h ↦ ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h.symm hz)
  have htwo : meromorphicOrderAt riemannZeta 2 = 0 :=
    (analyticOn_riemannZeta _ (by norm_num : (2 : ℂ) ≠ 1)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by simp [htwo])
  change 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ₀) univ z
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec χ₀).1.meromorphicOn (mem_univ _), ← hcmp]
  exact WithTop.coe_lt_coe.mp (by simpa only [WithTop.coe_untop₀_of_ne_top hfin, WithTop.coe_zero] using hpos)

/-- The ZetaLab sign bracket gives an actual central site with ordinate strictly
between 14.13 and 14.14. -/
theorem exists_rational_principal_central_site_in_first_bracket :
    ∃ z : Sites, z.val.re = 1 / 2 ∧ z.val.im ∈ Ioo (1413 / 100 : ℝ) (707 / 50) := by
  obtain ⟨t, ht, hz⟩ := HardyFirstZero.first_zero_on_line
  refine ⟨⟨point(t), rational_principal_divisor_pos_of_critical_zeta_zero t hz⟩, ?_, ?_⟩
  · norm_num [Complex.div_ofNat_re]
  · simpa [Complex.div_ofNat_im] using ht

end RiemannMasullo

namespace RiemannMasullo.HeckePoisson

local notation "χ₀" => (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))

/-- A strict one-copy budget for the normalized logarithmic derivative at `2 + 14i`
certifies that the completed rational principal function has exactly one site in the
closed cell `[13.5,14.5]`. It is central, has multiplicity one, and lies in the certified
open bracket `(14.13,14.14)`. -/
private theorem rational_first_cell_unique_simple_of_logDerivative_lt
    (hformula : HasSum (siteWeight (F := ℚ) (χ := χ₀) 14) (normalizedLogDerivative χ₀ 14))
    (hupper : normalizedLogDerivative χ₀ 14 < bracketLowerBound 14 (1413 / 100) (707 / 50) + 3 / 5) :
    ∃ z : Site (F := ℚ) χ₀, z.val.re = 1 / 2 ∧ z.val.im ∈ Ioo (1413 / 100 : ℝ) (707 / 50) ∧
      multiplicity (χ := χ₀) z = 1 ∧
      ∀ w : Site (F := ℚ) χ₀, w.val.im ∈ Icc (27 / 2 : ℝ) (29 / 2) ↔ w = z := by
  classical
  obtain ⟨z, hcentral, hbr⟩ := exists_rational_principal_central_site_in_first_bracket
  let B : CentralBrackets (F := ℚ) χ₀ :=
    { copies := Finsupp.single z 1
      left := fun _ ↦ 1413 / 100
      right := fun _ ↦ 707 / 50
      copies_le := by
        intro w
        by_cases he : w = z
        · subst w
          simpa only [Finsupp.single_eq_same] using one_le_multiplicity z
        · simp [Finsupp.single_eq_of_ne he]
      verified := by
        intro w hw
        have he : w = z := Finset.mem_singleton.mp (Finsupp.support_single_subset hw)
        subst w
        exact ⟨hcentral, hbr.1.le, hbr.2.le⟩ }
  have hcredit : B.lowerMass 14 = bracketLowerBound 14 (1413 / 100) (707 / 50) := by
    simp [CentralBrackets.lowerMass, B]
  have hb : normalizedLogDerivative χ₀ 14 - B.lowerMass 14 < 3 / 5 := by
    rw [hcredit]
    linarith
  have hcell : z.val.im ∈ Icc (27 / 2 : ℝ) (29 / 2) :=
    ⟨by linarith [hbr.1], by linarith [hbr.2]⟩
  have hmul (w : Site (F := ℚ) χ₀) (hw : w.val.im ∈ Icc (27 / 2 : ℝ) (29 / 2)) :
      multiplicity (χ := χ₀) w = B.copies w :=
    cell_multiplicity_of_brackets B hformula hb w (abs_le.mpr ⟨by linarith [hw.1], by linarith [hw.2]⟩)
  refine ⟨z, hcentral, hbr, ?_, fun w ↦ ⟨fun hw ↦ ?_, fun he ↦ he.symm ▸ hcell⟩⟩
  · simpa [B] using hmul z hcell
  · by_contra hne
    have hz : multiplicity (χ := χ₀) w = 0 := by
      simpa [B, Finsupp.single_eq_of_ne hne] using hmul w hw
    have := one_le_multiplicity w
    omega

/-- The single translated zero-sum identity at `2 + 14i` certifies the whole
closed cell `[13.5,14.5]`: it contains exactly one positive divisor site of the
completed rational principal function, in `(14.13,14.14)`, and that site is simple. -/
theorem rational_first_cell_unique_simple
    (hformula : HasSum (siteWeight (F := ℚ) (χ := χ₀) 14) (normalizedLogDerivative χ₀ 14)) :
    ∃ z : Site (F := ℚ) χ₀, z.val.re = 1 / 2 ∧ z.val.im ∈ Ioo (1413 / 100 : ℝ) (707 / 50) ∧
      multiplicity (χ := χ₀) z = 1 ∧
      ∀ w : Site (F := ℚ) χ₀, w.val.im ∈ Icc (27 / 2 : ℝ) (29 / 2) ↔ w = z := by
  apply rational_first_cell_unique_simple_of_logDerivative_lt hformula
  apply rational_normalizedLogDerivative_fourteen_le.trans_lt
  norm_num [bracketLowerBound]

end RiemannMasullo.HeckePoisson
