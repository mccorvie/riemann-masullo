module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b_HalfPlaneJensen
public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoisson
import Mathlib.Tactic

/-! # Compact Hecke circle means and the absolute exterior contribution

A fixed character's corrected circle means increase to its right-half-plane Green mass.
Reflection and a quadratic Mellin bound control the absolute contribution of the two
closed exterior half-strips by this same measured limit.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set
open scoped Topology NNReal

namespace RiemannMasullo.HeckePoisson

variable {F : Type*} [Field F] [NumberField F]
local notation "CF" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual CF

/-- The sum of the genuine completed-divisor Green logarithms strictly to the right
of one half, with multiplicity, at the reference point two. -/
def rightGreenMass (χ : U𝔽) : ℝ :=
  ∑' z : HeckeHalfPlaneJensen.RightSite χ,
    (HeckeHalfPlaneJensen.order χ z.val : ℝ) * HalfPlaneJensen.greenKernel z.val

private def rightGreen {χ : U𝔽} (z : Site χ) : ℝ :=
  if 1/2 < z.val.re then (multiplicity z : ℝ) * HalfPlaneJensen.greenKernel z.val else 0

private theorem rightGreen_nonneg {χ : U𝔽} (z : Site χ) : 0 ≤ rightGreen z := by
  unfold rightGreen
  split_ifs with h
  · have hx : 0 ≤ z.val.re-1/2 := by linarith
    have hl := (HalfPlaneJensen.greenKernel_bounds (s := z.val) h.le (siteStrip z).2).1
    exact mul_nonneg (Nat.cast_nonneg _) (le_trans (by positivity) hl)
  · rfl

private theorem hasSum_rightGreen (χ : U𝔽) :
    HasSum (fun z : Site χ ↦ rightGreen z) (rightGreenMass χ) := by
  classical
  let inc (z : HeckeHalfPlaneJensen.RightSite χ) : Site χ := ⟨z.val,z.property.1⟩
  have hinj : Injective inc := fun a b h ↦ Subtype.ext (congrArg (fun z : Site χ ↦ z.val) h)
  apply (hinj.hasSum_iff (f := fun z : Site χ ↦ rightGreen z) (by
    intro z hz
    have hn : ¬1/2 < z.val.re := fun h ↦ hz ⟨⟨z.val,z.property,h⟩, Subtype.ext rfl⟩
    rw [rightGreen, ite_eq_right hn])).1
  apply (HeckeHalfPlaneJensen.summable_greenKernel χ).hasSum.congr_fun
  intro z
  have hm : (multiplicity (inc z) : ℝ) = (HeckeHalfPlaneJensen.order χ z.val : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg z.property.1.le
  simp only [Function.comp_apply, rightGreen, show (inc z).val = z.val from rfl,
    ite_eq_left z.property.2, hm]

/-- A genuine normalized finite Hecke continuation has nondecreasing corrected means
on compact radii, tending to its nonnegative Green mass. -/
theorem tendsto_corrected_circle_mean_rightGreenMass (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ r, χ (τ r) = 1) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    MonotoneOn (HeckeHalfPlaneJensen.correctedMean χ L) (Ioo 0 1) ∧
    Tendsto (HeckeHalfPlaneJensen.correctedMean χ L) (𝓝[<] (1:ℝ)) (𝓝 (rightGreenMass χ)) := by
  have h := HeckeHalfPlaneJensen.canonical_compact_green τ hτ χ hχ
  exact ⟨h.2.1,h.2.2.1⟩

/-- The full Green logarithm is nonnegative for any ordinary unitary character. -/
theorem rightGreenMass_nonneg (χ : U𝔽) : 0 ≤ rightGreenMass χ := by
  rw [← (hasSum_rightGreen χ).tsum_eq]
  exact tsum_nonneg rightGreen_nonneg

/-- Every compact corrected circle mean lies between zero and the full Green mass. -/
theorem correctedMean_mem_Icc (τ : ℝ≥0ˣ →ₜ* CF) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) 1) :
    HeckeHalfPlaneJensen.correctedMean χ (finiteHeckeL_exists_continuation χ).choose r ∈
      Icc 0 (rightGreenMass χ) := by
  have hc := HeckeHalfPlaneJensen.canonical_compact_green τ hτ χ hχ
  constructor
  · rw [← (hc.1 r hr.1 hr.2).2.2.tsum_eq]
    exact tsum_nonneg fun z ↦ mul_nonneg (by exact_mod_cast z.property.1.le) (HalfPlaneJensen.weight_nonneg _ _)
  · apply ge_of_tendsto (tendsto_corrected_circle_mean_rightGreenMass τ hτ χ hχ).2
    filter_upwards [Ioo_mem_nhdsLT hr.2] with R hR
    exact hc.2.1 hr ⟨hr.1.trans hR.1,hR.2⟩ hR.1.le

private theorem sample_le_rightGreen {χ : U𝔽} (z : Site χ) {α W Y : ℝ}
    (hα : 0 < α) (hW : 0 ≤ W) (hx : α ≤ z.val.re-1/2)
    (hY : Y ≤ W/(1+z.val.im^2)) :
    (multiplicity z : ℝ) * Y ≤ (3*W/(4*α)) * rightGreen z := by
  have hp : 1/2 < z.val.re := by linarith
  have hl := (HalfPlaneJensen.greenKernel_bounds (s := z.val) (by linarith) (siteStrip z).2).1
  have hD : 0 < 1+z.val.im^2 := by positivity
  have hαgreen : α / (1+z.val.im^2) ≤ (3/4) * HalfPlaneJensen.greenKernel z.val := by
    have h := div_le_div_of_nonneg_right hx hD.le
    linarith only [hl,h,show (4/3 : ℝ)*(z.val.re-1/2)/(1+z.val.im^2) =
      (4/3)*((z.val.re-1/2)/(1+z.val.im^2)) by ring]
  have hAlgebra : Y ≤ (3*W/(4*α))*HalfPlaneJensen.greenKernel z.val := by
    calc Y ≤ W/(1+z.val.im^2) := hY
         _ = (W/α)*(α/(1+z.val.im^2)) := by field_simp
         _ ≤ (W/α)*((3/4)*HalfPlaneJensen.greenKernel z.val) :=
           mul_le_mul_of_nonneg_left hαgreen (div_nonneg hW hα.le)
         _ = _ := by ring
  rw [rightGreen, ite_eq_left hp]
  nlinarith [mul_le_mul_of_nonneg_left hAlgebra (Nat.cast_nonneg (multiplicity z) : (0:ℝ) ≤ _)]

/-- A logarithmic defect controls the absolute omitted trace, including both edges of
the closed exterior region. The envelope is required only at occupied sites. -/
theorem exterior_absolute_le_rightGreenMass (χ : U𝔽) (M : ℂ → ℂ) {α W : ℝ}
    (hα : 0 < α) (hW : 0 ≤ W) (hM : ∀ z : Site χ, ‖M z.val‖ ≤ W / (1+z.val.im^2)) :
    Summable (fun z : Site χ ↦ if α ≤ |z.val.re-1/2| then (multiplicity z : ℝ) * ‖M z.val‖ else 0) ∧
    (∑' z : Site χ, if α ≤ |z.val.re-1/2| then (multiplicity z : ℝ) * ‖M z.val‖ else 0) ≤
      (3*W/(2*α)) * rightGreenMass χ := by
  classical
  let e := positiveSiteReflection χ
  let C := 3*W/(4*α)
  let x (z : Site χ) : ℝ := if α ≤ |z.val.re-1/2| then (multiplicity z : ℝ) * ‖M z.val‖ else 0
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hx (z : Site χ) : 0 ≤ x z := by dsimp [x]; split_ifs <;> positivity
  have hy (z : Site χ) : x z ≤ C * (rightGreen z + rightGreen (e z)) := by
    dsimp [x]
    split_ifs with h
    · by_cases hsign : 0 ≤ z.val.re-1/2
      · rw [abs_of_nonneg hsign] at h
        exact (sample_le_rightGreen z hα hW h (hM z)).trans
          (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (rightGreen_nonneg (e z))) hC)
      · rw [abs_of_neg (lt_of_not_ge hsign)] at h
        have hsub : (e z).val.re = 1-z.val.re := by rfl
        have hre : α ≤ (e z).val.re-1/2 := by rw [hsub]; linarith
        have hw := sample_le_rightGreen (e z) (Y := ‖M z.val‖) hα hW hre (by
          simpa only [e,positiveSiteReflection_im] using hM z)
        simp only [e,multiplicity_reflection] at hw
        exact hw.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (rightGreen_nonneg z)) hC)
    · positivity [rightGreen_nonneg z, rightGreen_nonneg (e z)]
  have hs := hasSum_rightGreen χ
  have hs' : HasSum (fun z : Site χ ↦ rightGreen (e z)) (rightGreenMass χ) :=
    e.hasSum_iff.2 hs
  have ht := (hs.add hs').mul_left C
  have hw := (Summable.of_nonneg_of_le hx hy ht.summable).hasSum
  refine ⟨hw.summable, ?_⟩
  change ∑' z, x z ≤ _
  calc ∑' z, x z ≤ C * (rightGreenMass χ + rightGreenMass χ) := hasSum_le hy hw ht
       _ = _ := by dsimp [C]; ring

/-- Any particular strict right-hand divisor site has the indicated positive mass
in the Green sum, including all its copies. -/
theorem horizontal_distance_le_rightGreenMass {χ : U𝔽} (z : Site χ) (hz : 1/2 < z.val.re) :
    (multiplicity z : ℝ) * ((4/3) * (z.val.re-1/2) / (1+z.val.im^2)) ≤ rightGreenMass χ := by
  have hL := (HalfPlaneJensen.greenKernel_bounds (s := z.val) hz.le (siteStrip z).2).1
  have hb := (hasSum_rightGreen χ).summable.le_tsum z (fun i _ ↦ rightGreen_nonneg i)
  rw [(hasSum_rightGreen χ).tsum_eq] at hb
  rw [rightGreen, ite_eq_left hz] at hb
  exact (mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg _)).trans hb

/-- The arithmetic formula for this Green sum is one way to test centrality. Its
positive divisor interpretation alone already characterizes all heights, with
both sides of the line covered by the same-character functional equation. -/
theorem rightGreenMass_eq_zero_iff (χ : U𝔽) :
    rightGreenMass χ = 0 ↔ ∀ z : Site χ, z.val.re = 1/2 := by
  constructor
  · intro mass
    have hle (z : Site χ) : z.val.re ≤ 1/2 := by
      by_contra! h
      have hz := horizontal_distance_le_rightGreenMass z h
      rw [mass] at hz
      have hm : 0 < (multiplicity z : ℝ) := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one (one_le_multiplicity z)
      have hx : 0 < z.val.re-1/2 := by linarith
      exact (by positivity : 0 < (multiplicity z : ℝ) * ((4/3) * (z.val.re-1/2) / (1+z.val.im^2))).not_ge hz
    intro z
    have h := hle (positiveSiteReflection χ z)
    change 1-z.val.re ≤ 1/2 at h
    exact le_antisymm (hle z) (by linarith)
  · intro h
    rw [← (hasSum_rightGreen χ).tsum_eq]
    simp [rightGreen, h]

set_option quotPrecheck false

attribute [local instance] instIdeleClassT2Sec4b instIdeleClassLocallyCompactSec4b
  instIdeleClassMeasurableSec4b

local notation "ord(" χ ", " z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := F) χ) univ z
local notation "M(" φ ", " χ ", " z ")" =>
  modulatedFourierMellin (continuousIdeleClassNorm F) univ
    ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
    (ideleClassTamagawaMeasure F) (φ : BruhatCompactSupport CF).val
    (ideleClassNormTwist (F := F) χ ((z : ℂ) - 1 / 2))

/-- Every power of the height times the centered Fourier–Mellin transform of a
compact Bruhat test is bounded on the closed critical strip for a fixed unitary character. -/
theorem exists_centeredMellin_strip_pow_envelope (φ : BruhatCompactSupport CF)
    (χ : PontryaginDual CF) (k : ℕ) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ z : ℂ, z.re ∈ Icc (0 : ℝ) 1 →
      (1 + |z.im|) ^ k * ‖M(φ,χ,z)‖ ≤ W := by
  obtain ⟨W, hW, h⟩ := idelicExplicitFormula_mellin_pow_envelope φ χ k
  refine ⟨W, hW, fun z hz ↦ ?_⟩
  have hshift : M(φ,χ,z) =
      ∫ g, φ.val g * ideleClassNormTwist χ z g *
        ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (-1/2 : ℂ)) ∂ideleClassTamagawaMeasure F := by
    simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ]
    apply integral_congr_ae
    filter_upwards [] with g
    let u : ℂ := (((ideleClassNorm F g).val : ℝ) : ℂ)
    have hu : u ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    change φ.val g * ((χ g : ℂ) * u ^ (z - 1/2)) =
      φ.val g * ((χ g : ℂ) * u ^ z) * u ^ (-1/2 : ℂ)
    rw [show z - 1/2 = z + (-1/2) by ring, Complex.cpow_add _ _ hu]
    ring
  rw [hshift]
  exact h z hz

/-- The fixed compact test has a polynomial height envelope on all occupied sites,
without restricting the unitary character by a choice of section. -/
theorem exists_centeredMellin_site_pow_envelope (φ : BruhatCompactSupport CF)
    (χ : PontryaginDual CF) (k : ℕ) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ z : Site χ, |z.val.im| ^ k * ‖M(φ,χ,z.val)‖ ≤ W := by
  obtain ⟨W, hW, h⟩ := exists_centeredMellin_strip_pow_envelope φ χ k
  refine ⟨W, hW, fun z ↦ ?_⟩
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (by linarith) k)
    (norm_nonneg _)).trans (h z.val (siteStrip z))

/-- The centered Fourier–Mellin transform of a compact Bruhat test has a quadratic
height envelope throughout the closed critical strip, for every fixed unitary character. -/
private theorem exists_centeredMellin_strip_envelope (φ : BruhatCompactSupport CF)
    (χ : PontryaginDual CF) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ z : ℂ, z.re ∈ Icc (0 : ℝ) 1 →
      (1 + z.im ^ 2) * ‖M(φ,χ,z)‖ ≤ W := by
  obtain ⟨W, hW, h⟩ := exists_centeredMellin_strip_pow_envelope φ χ 2
  refine ⟨W, hW, fun z hz ↦ ?_⟩
  have hw : 1 + z.im ^ 2 ≤ (1 + |z.im|) ^ 2 := by
    nlinarith [abs_nonneg z.im, sq_abs z.im]
  exact (mul_le_mul_of_nonneg_right hw (norm_nonneg _)).trans (h z hz)

set_option maxHeartbeats 800000 in
/-- The absolute Mellin contribution of both closed exterior half-strips in a single
character is bounded by a fixed test constant times the limit of the corrected circle means of the ordinary finite Hecke function. -/
theorem exists_hasSum_absolute_exterior_le_circleLimit (τ : ℝ≥0ˣ →ₜ* CF)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : U𝔽) (hχ : ∀ u, χ (τ u) = 1)
    (φ : BruhatCompactSupport CF) :
    ∃ W : ℝ, 0 ≤ W ∧ ∀ α : ℝ, 0 < α → ∃ A : ℝ,
      HasSum (fun z : {p : ℂ // 0 < ord(χ, p) ∧ α ≤ |p.re-1/2|} ↦
        ‖((ord(χ, z.val) : ℤ) : ℂ) * M(φ,χ,z.val)‖) A ∧ A ≤ (3*W/(2*α)) *
        Filter.limUnder (𝓝[<] (1 : ℝ)) (HeckeHalfPlaneJensen.correctedMean χ (finiteHeckeL_exists_continuation χ).choose) := by
  classical
  rw [(tendsto_corrected_circle_mean_rightGreenMass τ hτ χ hχ).2.limUnder_eq]
  obtain ⟨W,hW,henv⟩ := exists_centeredMellin_strip_envelope φ χ
  refine ⟨W,hW,fun α hα ↦ ?_⟩
  let Fz (z : ℂ) := M(φ,χ,z)
  let f (z : Site χ) : ℝ := (multiplicity z : ℝ) * ‖Fz z.val‖
  let E : Set (Site χ) := {z | α ≤ |z.val.re-1/2|}
  obtain ⟨hs,hbound⟩ := exterior_absolute_le_rightGreenMass χ Fz hα hW (fun z ↦
    (le_div_iff₀ (by positivity)).2 (by simpa only [mul_comm] using henv z.val (siteStrip z)))
  let A := ∑' z : Site χ, if α ≤ |z.val.re-1/2| then (multiplicity z : ℝ) * ‖Fz z.val‖ else 0
  refine ⟨A,?_,hbound⟩
  have hsf : HasSum (E.indicator f) A := hs.hasSum
  have hsum : HasSum (fun z : E ↦ f z.val) A := (hasSum_subtype_iff_indicator (s := E) (f := f)).2 hsf
  let e := Equiv.subtypeSubtypeEquivSubtypeInter (fun p : ℂ ↦ 0 < ord(χ,p)) (fun p : ℂ ↦ α ≤ |p.re-1/2|)
  let G (z : {z : ℂ // 0 < ord(χ,z) ∧ α ≤ |z.re-1/2|}) : ℝ := ‖((ord(χ,z.val) : ℤ) : ℂ) * Fz z.val‖
  change HasSum G A
  apply (e.hasSum_iff (f := G)).1
  apply hsum.congr_fun
  intro z
  have hm : 0 < ord(χ,z.val.val) := z.val.property
  change ‖((ord(χ,z.val.val) : ℤ) : ℂ) * Fz z.val.val‖ = ((ord(χ,z.val.val)).toNat : ℝ) * ‖Fz z.val.val‖
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg (by exact_mod_cast hm.le)]
  congr 1
  exact_mod_cast (Int.toNat_of_nonneg hm.le).symm

end RiemannMasullo.HeckePoisson
