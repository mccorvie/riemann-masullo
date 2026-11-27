module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.AppB_AnalyticNT.Sec4b

/-! # A summable majorant on the actual fixed-level Hecke zero set

A change of norm section or of the chosen angular basepoint translates the physical ordinate.
Transporting the joint character-zero count through this translation bounds all the indexed
sites on one fixed level of locally constant data.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set Function
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.WeakCardinal

set_option quotPrecheck false
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "K𝔽" => (ideleClassNorm F).ker
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Ω𝔽" => PontryaginDual K𝔽
local notation "incl" => (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : K𝔽 →ₜ* C𝔽)
local notation "UnitChars(" τ ")" => {η : U𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
local notation "PZeros(" τ ")" => {q : UnitChars(τ) × ℂ //
  0 < MeromorphicOn.divisor (explicitFormulaCompletedHeckeL q.1.val) univ q.2}
local notation "pt(" σ ", " t ")" => ((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "ord(" η ", " u ")" => meromorphicOrderAt (continuedCompletedHeckeL η) u
local notation "order(" χ ", " a ", " z ")" => ord(χ (z).1, pt(a + (z).2.1, (z).2.2))
local notation "zeros(" F ", " χ ", " a ", " α ")" => {z : PontryaginDual (ideleClassNorm F).ker × ℝ × ℝ //
  z.2.1 ∈ Icc (-α) α ∧ 0 < order(χ, a, z)}

/-- Remove the restriction of a unitary character on the norm section. -/
def spectralSectionNormalizedChar (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (η : U𝔽) : UnitChars(τ) := by
  let θ : U𝔽 := η.comp (τ.comp (continuousIdeleClassNorm F))
  let ψ : U𝔽 := η / θ
  exact ⟨ψ, fun u ↦ by
    change η (τ u) / η (τ (ideleClassNorm F (τ u))) = 1
    rw [hτ u, div_self']⟩

private theorem spectralSectionNormalizedChar_restrict (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (η : U𝔽) :
    (spectralSectionNormalizedChar τ hτ η).val.comp incl = η.comp incl := by
  ext u : 1
  change η u.val / η (τ (ideleClassNorm F u.val)) = η u.val
  rw [show ideleClassNorm F u.val = 1 from u.property, map_one, map_one, div_one]

/-- Physical ordinate for a native spectral basepoint, with the normalized character
trivial on the chosen norm section. The subtraction inverts the pinned chart-shift theorem. -/
def spectralSectionPhysicalOrdinate (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Ω𝔽 → U𝔽) (hχ : IsSpectralBasepointChoice χ) (ω : Ω𝔽) (t : ℝ) : ℝ :=
  t - (hχ.existsUnique_ordinate_shift (spectralSectionNormalizedChar τ hτ (χ ω)).val).choose

private theorem shift_coe_cancel (t d : ℝ) : ((t-d : ℝ) : ℂ) + (d : ℂ) = (t : ℂ) := by
  rw [Complex.ofReal_sub, sub_add_cancel]

theorem spectralSectionPhysicalOrdinate_spec (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (χ : Ω𝔽 → U𝔽) (hχ : IsSpectralBasepointChoice χ)
    (ω : Ω𝔽) (σ t : ℝ) :
    let η := (spectralSectionNormalizedChar τ hτ (χ ω)).val
    let w := spectralSectionPhysicalOrdinate τ hτ χ hχ ω t
    ideleClassNormTwist η (pt(σ, w)) = ideleClassNormTwist (χ ω) (pt(σ, t)) ∧
    (ord(η, pt(σ, w))).untop₀.toNat = (ord(χ ω, pt(σ, t))).untop₀.toNat := by
  let η := (spectralSectionNormalizedChar τ hτ (χ ω)).val
  let d := (hχ.existsUnique_ordinate_shift η).choose
  have hr : η.comp incl = ω := (spectralSectionNormalizedChar_restrict τ hτ (χ ω)).trans (hχ ω)
  have h := (hχ.existsUnique_ordinate_shift η).choose_spec.1 σ (t-d)
  change ideleClassNormTwist η (pt(σ,t-d)) = ideleClassNormTwist (χ (η.comp incl))
    ((σ:ℂ) + (((t-d : ℝ):ℂ) + (d:ℂ))*Complex.I) ∧
    (ord(η, pt(σ,t-d))).untop₀.toNat = (ord(χ (η.comp incl),
      (σ:ℂ) + (((t-d:ℝ):ℂ) + (d:ℂ))*Complex.I)).untop₀.toNat at h
  rw [shift_coe_cancel, hr] at h
  exact h

private theorem positiveCompletedOrder_toNat {η : U𝔽} {u : ℂ}
    (hu : 0 < ord(η, u)) : 0 < (ord(η, u)).untop₀.toNat := by
  obtain ⟨hL,hspec⟩ := continuedCompletedHeckeL_spec η
  have hf : ord(η, u) ≠ ⊤ := by
    apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (x := 2) (mem_univ _) (mem_univ _)
    intro he
    have hp : 0 < ord(η, (2:ℂ)) := he ▸ WithTop.coe_lt_top (0:ℤ)
    have hz := completedHeckeL_continuation_zeros η _ hL hspec (by norm_num : 0 < (2:ℂ).re) hp
    norm_num at hz
  cases h : ord(η, u) with
  | top => exact (hf h).elim
  | coe n =>
    have hn : (0:ℤ) < n := by simpa only [h, ← WithTop.coe_zero, WithTop.coe_lt_coe] using hu
    rw [WithTop.untop₀_coe]
    omega

private def physicalSpectralSiteEmbedding (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : Ω𝔽 → U𝔽) (hχ : IsSpectralBasepointChoice χ) (a α : ℝ) : zeros(F, χ, a, α) ↪ PZeros(τ) where
  toFun z := ⟨(spectralSectionNormalizedChar τ hτ (χ z.val.1),
    pt(a+z.val.2.1, spectralSectionPhysicalOrdinate τ hτ χ hχ z.val.1 z.val.2.2)), by
      rw [MeromorphicOn.divisor_apply (explicitFormulaCompletedHeckeL_spec _).1.meromorphicOn (mem_univ _)]
      have hp := positiveCompletedOrder_toNat z.property.2
      rw [← (spectralSectionPhysicalOrdinate_spec τ hτ χ hχ z.val.1 (a+z.val.2.1) z.val.2.2).2] at hp
      change 0 < (ord((spectralSectionNormalizedChar τ hτ (χ z.val.1)).val,
        pt(a+z.val.2.1, spectralSectionPhysicalOrdinate τ hτ χ hχ z.val.1 z.val.2.2))).untop₀
      omega⟩
  inj' := by
    intro x y he
    have hn : spectralSectionNormalizedChar τ hτ (χ x.val.1) =
        spectralSectionNormalizedChar τ hτ (χ y.val.1) :=
      congrArg (fun e : PZeros(τ) ↦ e.val.1) he
    have hw : x.val.1 = y.val.1 := ((spectralSectionNormalizedChar_restrict τ hτ (χ x.val.1)).trans (hχ _)).symm.trans
      ((congrArg (fun η : UnitChars(τ) ↦ η.val.comp incl) hn).trans
       ((spectralSectionNormalizedChar_restrict τ hτ (χ y.val.1)).trans (hχ _)))
    have hp := congrArg (fun e : PZeros(τ) ↦ e.val.2) he
    change pt(a+x.val.2.1, spectralSectionPhysicalOrdinate τ hτ χ hχ x.val.1 x.val.2.2) =
      pt(a+y.val.2.1, spectralSectionPhysicalOrdinate τ hτ χ hχ y.val.1 y.val.2.2) at hp
    apply Subtype.ext
    refine Prod.ext hw (Prod.ext ?_ ?_)
    · simpa using congrArg Complex.re hp
    · simpa [spectralSectionPhysicalOrdinate, hw] using congrArg Complex.im hp

/-- Fixed-level angular height measured by the same norm-one flows as the joint
arithmetic zero count. -/
def spectralAngularFlowHeight {r : ℕ} (Y : Fin r → LCATopologicalLie K𝔽) (η : U𝔽) : ℝ :=
  ∑ i, ‖bruhatDirectionalDeriv (Y i) (fun u : K𝔽 ↦ (η u.val : ℂ)) 1‖

private theorem summable_inverse_weight_of_count {Z : Type*} (height : Z → ℝ)
    (hheight : ∀ z, 0 ≤ height z) (active : Z → Prop) [DecidablePred active]
    (C : ℝ) (d : ℕ)
    (hc : ∀ n : ℕ, ∀ S : Finset Z, (∀ z ∈ S, active z ∧ height z < (n:ℝ)+1) →
      (S.card : ℝ) ≤ C*((n:ℝ)+1)^d) :
    Summable (fun z ↦ if active z then 1/(1+height z)^(d+2) else 0) := by
  classical
  let f (z : Z) := if active z then 1/(1+height z)^(d+2) else 0
  have hseries : Summable (fun n : ℕ ↦ 1/((n:ℝ)+1)^2) := by
    simpa using (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr one_lt_two)
  have hC : 0 ≤ C := by simpa using hc 0 ∅ (by simp)
  apply summable_of_sum_le (f := f) (fun z ↦ by have hh := hheight z; dsimp [f]; split_ifs <;> positivity)
    (c := C * ∑' n : ℕ, 1/((n:ℝ)+1)^2)
  intro S
  let A := S.filter active
  have hA : ∑ z ∈ A, f z = ∑ z ∈ S, f z :=
    Finset.sum_subset (Finset.filter_subset ..) fun z hz hn ↦ by simp_all [A, f]
  rw [← hA]
  let level (z : Z) := ⌊height z⌋₊
  rw [← Finset.sum_fiberwise_of_maps_to (t := A.image level) (g := level) (fun z hz ↦ Finset.mem_image_of_mem _ hz)]
  calc
    _ ≤ ∑ n ∈ A.image level, C*(1/((n:ℝ)+1)^2) := by
      apply Finset.sum_le_sum
      intro n _
      let V := A.filter (fun z ↦ level z = n)
      have hv (z) (hz : z ∈ V) : active z ∧ level z = n :=
        ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2,(Finset.mem_filter.mp hz).2⟩
      have hn (z) (hz : z ∈ V) : height z < (n:ℝ)+1 :=
        (hv z hz).2 ▸ Nat.lt_floor_add_one (height z)
      calc
        _ ≤ ∑ _z ∈ V, 1/((n:ℝ)+1)^(d+2) := by
          apply Finset.sum_le_sum
          intro z hz
          have hz' : (n:ℝ) ≤ height z := (hv z hz).2 ▸ Nat.floor_le (hheight z)
          change f z ≤ _
          dsimp only [f]
          rw [ite_eq_left (hv z hz).1]
          exact one_div_le_one_div_of_le (by positivity)
            (pow_le_pow_left₀ (by positivity) (by linarith) _)
        _ = (V.card : ℝ)*(1/((n:ℝ)+1)^(d+2)) := by simp
        _ ≤ (C*((n:ℝ)+1)^d)*(1/((n:ℝ)+1)^(d+2)) :=
          mul_le_mul_of_nonneg_right (hc n V fun z hz ↦ ⟨(hv z hz).1,hn z hz⟩) (by positivity)
        _ = _ := by rw [pow_add]; field_simp
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hseries.sum_le_tsum _ fun n _ ↦ by positivity) hC

/-- The actual inverse-power majorant on a fixed Bruhat level has exactly zero weight
outside its annihilator. The height uses the normalized physical ordinate. -/
def spectralFixedLevelWeight {r : ℕ} (Y : Fin r → LCATopologicalLie K𝔽)
    (k : Subgroup C𝔽) (N : ℕ) (η : U𝔽) (w : ℝ) : ℝ := by
  classical
  exact if ∀ u : k, η u.val = 1 then 1 / (1 + (|w| + spectralAngularFlowHeight Y η))^N else 0

theorem spectralFixedLevelWeight_nonneg {r : ℕ} (Y : Fin r → LCATopologicalLie K𝔽)
    (k : Subgroup C𝔽) (N : ℕ) (η : U𝔽) (w : ℝ) : 0 ≤ spectralFixedLevelWeight Y k N η w := by
  classical
  unfold spectralFixedLevelWeight spectralAngularFlowHeight
  split_ifs <;> positivity

/-- The joint Hecke divisor count supplies the flows and a summable inverse power on
all normalized physical zero sites of one fixed level. The count includes multiplicities. -/
theorem exists_summable_spectralFixedLevelWeight (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (k : Subgroup C𝔽) (hk : IsBruhatGoodSubgroup k) :
    ∃ (r : ℕ) (Y : Fin r → LCATopologicalLie K𝔽) (d : ℕ),
      Summable (fun z : PZeros(τ) ↦ spectralFixedLevelWeight Y k (d+2) z.val.1.val z.val.2.im) := by
  classical
  obtain ⟨r, Y, C, d, hcount⟩ := idelicExplicitFormula_summable_spectral_characters_polynomialCount τ hτ k hk
  refine ⟨r, Y, d, ?_⟩
  let height (z : PZeros(τ)) := |z.val.2.im| + spectralAngularFlowHeight Y z.val.1.val
  let active (z : PZeros(τ)) := ∀ u : k, z.val.1.val u.val = 1
  have hn (z : PZeros(τ)) : 0 ≤ spectralAngularFlowHeight Y z.val.1.val :=
    Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  apply summable_inverse_weight_of_count height (fun z ↦ add_nonneg (abs_nonneg _) (hn z)) active C d
  intro n S hS
  have hc := hcount n S (by
    intro z hz
    obtain ⟨hs, hb⟩ := hS z hz
    change |z.val.2.im| + spectralAngularFlowHeight Y z.val.1.val < (n:ℝ)+1 at hb
    refine ⟨hs, by linarith [hn z], fun i ↦ ?_⟩
    have hi : ‖bruhatDirectionalDeriv (Y i) (fun u : K𝔽 ↦ (z.val.1.val u.val : ℂ)) 1‖ ≤
        spectralAngularFlowHeight Y z.val.1.val :=
      Finset.single_le_sum (f := fun j ↦ ‖bruhatDirectionalDeriv (Y j)
        (fun u : K𝔽 ↦ (z.val.1.val u.val : ℂ)) 1‖) (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
    linarith [abs_nonneg z.val.2.im])
  refine le_trans ?_ hc
  calc
    (S.card : ℝ) = ∑ _z ∈ S, (1 : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun z _ ↦ by
      rw [Complex.norm_intCast, abs_of_pos (by exact_mod_cast z.property)]
      exact_mod_cast (show (1:ℤ) ≤ _ from z.property)

/-- Restrict the same summable weight to the actual indexed sites on any native strip.
The physical imaginary part shifts with the basepoint in each component. -/
theorem exists_summable_spectralStripSiteWeight (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (k : Subgroup C𝔽) (hk : IsBruhatGoodSubgroup k)
    (χ : Ω𝔽 → U𝔽) (hχ : IsSpectralBasepointChoice χ) (a α : ℝ) :
    ∃ (r : ℕ) (Y : Fin r → LCATopologicalLie K𝔽) (d : ℕ),
      Summable (fun z : zeros(F, χ, a, α) ↦ spectralFixedLevelWeight Y k (d+2)
        (spectralSectionNormalizedChar τ hτ (χ z.val.1)).val
        (spectralSectionPhysicalOrdinate τ hτ χ hχ z.val.1 z.val.2.2)) := by
  obtain ⟨r,Y,d,hw⟩ := exists_summable_spectralFixedLevelWeight τ hτ k hk
  let e := physicalSpectralSiteEmbedding τ hτ χ hχ a α
  refine ⟨r,Y,d,(hw.comp_injective e.injective).congr fun z ↦ ?_⟩
  let η := (spectralSectionNormalizedChar τ hτ (χ z.val.1)).val
  let t := spectralSectionPhysicalOrdinate τ hτ χ hχ z.val.1 z.val.2.2
  change spectralFixedLevelWeight Y k (d+2) η (pt(a + z.val.2.1,t)).im =
    spectralFixedLevelWeight Y k (d+2) η t
  exact congrArg (spectralFixedLevelWeight Y k (d+2) η) (by simp)

end RiemannMasullo.WeakCardinal
