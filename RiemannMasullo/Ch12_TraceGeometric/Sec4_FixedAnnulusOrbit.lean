module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_OrbitSeries
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_WeightedOrbitKernel
import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Topology.Algebra.IsOpenUnits

/-! # The concrete half-density orbit kernel on a fixed annulus -/

public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "Hₛ" => sProjectedDiagonal F S
set_option quotPrecheck false in
local notation "A∞" => ((w : InfinitePlace F) → w.Completion)
set_option quotPrecheck false in
local notation "A𝒻" => ((v : S) → v.val.adicCompletion F)
local notation "Eₛ" => A∞ × A𝒻
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ InfinitePlace.mult w) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
set_option quotPrecheck false in
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "ψₛ" => sAdeleStandardCharacter F S
local notation "fourierₛ" => tamagawaFourier νₛ ψₛ

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSAdeleMeasurableSpaceSec1 instSIdeleLocallyCompactSec1

local instance : T2Space Iₛ := (sIdeleGroup_description F S).2.1

/-- The S-idelic norm is continuous. -/
private theorem sLocalTrace_sIdeleNorm_continuous : Continuous (sIdeleNorm F S) := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun g : Iₛ ↦ ((sIdeleNorm F S g).val))
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]
  change Continuous (fun g : Iₛ ↦ (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) *
    ∏ v : S, ‖g.val.2 v‖₊)
  fun_prop

private theorem sLocalTrace_unit_norm (ξ : Hₛ) : sIdeleNorm F S ξ.val = 1 := by
  obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ξ.property
  exact he ▸ (sIdeleNorm_spec F S).2 hγ

private theorem sLocalTrace_max_one_norm_mul_le (x y : Eₛ) :
    max 1 ‖x * y‖ ≤ max 1 ‖x‖ * max 1 ‖y‖ := by
  refine max_le ?_ ?_
  · exact (le_max_left 1 ‖x‖).trans
      (le_mul_of_one_le_right (zero_le_one.trans (le_max_left 1 ‖x‖)) (le_max_left 1 ‖y‖))
  · exact (norm_mul_le x y).trans
      (mul_le_mul (le_max_right 1 ‖x‖) (le_max_right 1 ‖y‖) (norm_nonneg _) (by positivity))

private def sLocalTrace_orbHeight (u : Eₛ) : ℝ := max 1 ‖u‖

local notation "orbHeight(" u ")" => sLocalTrace_orbHeight u

private theorem sLocalTrace_orbHeight_nonneg (u : Eₛ) : 0 ≤ orbHeight(u) :=
  zero_le_one.trans (le_max_left _ _)

private def sLocalTrace_projectedCanonicalSection : ℝ≥0ˣ →* Iₛ :=
  (Units.map (adeleProjection F S).toMonoidHom).comp (canonicalIdeleNormSection F)

private theorem sLocalTrace_projectedCanonicalSection_height (t : ℝ≥0ˣ) :
    orbHeight((sLocalTrace_projectedCanonicalSection (F := F) (S := S) t).val) ≤
      max 1 (t.val : ℝ) := by
  let e := (Module.finrank ℚ F : ℝ)⁻¹
  have hdeg : 1 ≤ (Module.finrank ℚ F : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt (Module.finrank_pos (R := ℚ) (M := F))
  have he₀ : 0 ≤ e := inv_nonneg.mpr (Nat.cast_nonneg _)
  have he₁ : e ≤ 1 := inv_le_one_of_one_le₀ hdeg
  have hroot : (t.val : ℝ) ^ e ≤ max 1 (t.val : ℝ) := by
    rcases le_total (t.val : ℝ) 1 with ht | ht
    · exact (Real.rpow_le_one (NNReal.coe_nonneg _) ht he₀).trans (le_max_left _ _)
    · exact ((Real.rpow_le_rpow_of_exponent_le ht he₁).trans_eq
        (Real.rpow_one _)).trans (le_max_right _ _)
  let zS : Eₛ := (sLocalTrace_projectedCanonicalSection (F := F) (S := S) t).val
  change max 1 ‖zS‖ ≤ max 1 (t.val : ℝ)
  apply max_le (le_max_left _ _)
  apply (norm_prod_le_iff (x := zS)).mpr
  have hnonneg : 0 ≤ max 1 (t.val : ℝ) := zero_le_one.trans (le_max_left _ _)
  refine ⟨(pi_norm_le_iff_of_nonneg (x := zS.1) hnonneg).mpr fun w ↦ ?_,
    (pi_norm_le_iff_of_nonneg (x := zS.2) hnonneg).mpr fun v ↦ ?_⟩
  · let z := (canonicalIdeleNormSection F t).val.1 w
    change ‖z‖ ≤ max 1 (t.val : ℝ)
    have hz := ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
      (map_zero _) z)
    change ‖InfinitePlace.Completion.extensionEmbedding w
      ((canonicalIdeleNormSection F t).val.1 w)‖ = ‖z‖ at hz
    rw [canonicalIdeleNormSection_infinite F t w, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (NNReal.coe_nonneg _) _)] at hz
    exact hz ▸ hroot
  · change ‖(canonicalIdeleNormSection F t).val.2 v.val‖ ≤ max 1 (t.val : ℝ)
    rw [canonicalIdeleNormSection_finite]
    change ‖(1 : v.val.adicCompletion F)‖ ≤ max 1 (t.val : ℝ)
    rw [norm_one]
    exact le_max_left _ _

private theorem sLocalTrace_projectedCanonicalSection_inv_height (t : ℝ≥0ˣ) :
    orbHeight(((sLocalTrace_projectedCanonicalSection (F := F) (S := S) t)⁻¹).val) ≤
      max 1 ((t.val : ℝ)⁻¹) := by
  rw [← map_inv]
  simpa only [Units.val_inv_eq_inv_val, NNReal.coe_inv] using
    sLocalTrace_projectedCanonicalSection_height (F := F) (S := S) t⁻¹

private theorem sLocalTrace_modulus_le_orbitHeight_pow (z : Eₛ) :
    modS(z) ≤ orbHeight(z) ^ ((∑ w : InfinitePlace F, w.mult) + Fintype.card S) := by
  let U := orbHeight(z)
  have harch (w : InfinitePlace F) : ‖z.1 w‖ ≤ U :=
    (norm_le_pi_norm (z.1 : A∞) w).trans ((norm_fst_le z).trans (le_max_right _ _))
  have hfin (v : S) : ‖z.2 v‖ ≤ U :=
    (norm_le_pi_norm z.2 v).trans ((norm_snd_le z).trans (le_max_right _ _))
  change (∏ w : InfinitePlace F, ‖z.1 w‖ ^ w.mult) * (∏ v : S, ‖z.2 v‖) ≤ _
  calc
    _ ≤ (∏ w : InfinitePlace F, U ^ w.mult) * (∏ _v : S, U) := by
      refine mul_le_mul (Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun w _ ↦
        pow_le_pow_left₀ (norm_nonneg _) (harch w) _)
        (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦ hfin v)
        (Finset.prod_nonneg fun _ _ ↦ norm_nonneg _)
        (Finset.prod_nonneg fun _ _ ↦ pow_nonneg (sLocalTrace_orbHeight_nonneg z) _)
    _ = _ := by rw [Finset.prod_pow_eq_pow_sum, Finset.prod_const, Finset.card_univ, pow_add]

/-- The input radius and S-unit height are both controlled by the same
frequency norm in the scaled off-diagonal formula. -/
private theorem sLocalTrace_radialOrbit_growth (x y₀ : Iₛ)
    (hy₀ : sIdeleNorm F S y₀ = 1) (t : ℝ≥0ˣ) (ξ : Hₛ) :
    let τ := sLocalTrace_projectedCanonicalSection (F := F) (S := S)
    let y := y₀ * τ t
    let u := x⁻¹ * (ξ.val * y)
    let D := (∑ w : InfinitePlace F, w.mult) + Fintype.card S
    (t.val : ℝ) ≤ normS(x) * orbHeight(u.val) ^ D ∧
      orbHeight(ξ.val.val) ≤ orbHeight(x.val * (y₀⁻¹).val) *
        max 1 ((t.val : ℝ)⁻¹) * orbHeight(u.val) := by
  intro τ y u D
  have hτ : sIdeleNorm F S (τ t) = t := sIdeleNorm_project_canonicalSection F S t
  have hy : sIdeleNorm F S y = t := by rw [show y = y₀ * τ t from rfl, map_mul, hy₀, hτ, one_mul]
  have hNorm : sIdeleNorm F S x * sIdeleNorm F S u = t := by
    rw [← map_mul, show x * u = ξ.val * y by simp only [u, mul_inv_cancel_left],
      map_mul, sLocalTrace_unit_norm, one_mul, hy]
  have hre : normS(x) * normS(u) = (t.val : ℝ) := by
    simpa only [Units.val_mul, NNReal.coe_mul] using
      congrArg (fun v : ℝ≥0ˣ ↦ (v.val : ℝ)) hNorm
  have hu : modS(u.val) = normS(u) := by simp [sIdeleNorm, Units.coe_prod]
  constructor
  · rw [← hre, ← hu]
    exact mul_le_mul_of_nonneg_left (sLocalTrace_modulus_le_orbitHeight_pow (show Eₛ from u.val))
      (NNReal.coe_nonneg _)
  · have hrec : ξ.val = ((x * y₀⁻¹) * (τ t)⁻¹) * u := by
      calc
        _ = (x * x⁻¹) * (y₀⁻¹ * y₀) * ((τ t)⁻¹ * τ t) * ξ.val := by simp
        _ = _ := by dsimp only [u, y]; ac_rfl
    have hre' : (ξ.val.val : Eₛ) = ((x.val * (y₀⁻¹).val) * ((τ t)⁻¹).val) * u.val := by
      simpa only [Units.val_mul] using congrArg (fun a : Iₛ ↦ a.val) hrec
    rw [hre']
    calc
      _ ≤ orbHeight((x.val * (y₀⁻¹).val) * ((τ t)⁻¹).val) * orbHeight(u.val) :=
        sLocalTrace_max_one_norm_mul_le _ _
      _ ≤ (orbHeight(x.val * (y₀⁻¹).val) * orbHeight(((τ t)⁻¹).val)) * orbHeight(u.val) :=
        mul_le_mul_of_nonneg_right (sLocalTrace_max_one_norm_mul_le _ _)
          (sLocalTrace_orbHeight_nonneg u.val)
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (sLocalTrace_projectedCanonicalSection_inv_height (F := F) (S := S) t)
          (sLocalTrace_orbHeight_nonneg (x.val * (y₀⁻¹).val))) (sLocalTrace_orbHeight_nonneg u.val)

/-- Two compact sets supply the output norm bound and the uniform height of
the product of an output representative and an inverse angular representative. -/
private theorem sLocalTrace_compact_orbit_geometry {X Y : Set Iₛ}
    (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ A ≥ 1, ∃ B ≥ 1, (∀ x ∈ X, normS(x) ≤ A) ∧
      ∀ x ∈ X, ∀ y₀ ∈ Y, orbHeight(x.val * (y₀⁻¹).val) ≤ B := by
  have hN : Continuous (fun x : Iₛ ↦ normS(x)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp sLocalTrace_sIdeleNorm_continuous)
  obtain ⟨A, hA⟩ := (hX.image hN).bddAbove
  have hval : Continuous (fun x : Iₛ ↦ (show Eₛ from x.val)) := Units.continuous_val
  have hprod : Continuous (fun p : Iₛ × Iₛ ↦ (show Eₛ from p.1.val * (p.2⁻¹).val)) :=
    (hval.comp continuous_fst).mul (hval.comp (continuous_inv.comp continuous_snd))
  obtain ⟨B, hB⟩ := ((hX.prod hY).image (continuous_const.max hprod.norm)).bddAbove
  refine ⟨max 1 A, le_max_left _ _, max 1 B, le_max_left _ _, ?_, ?_⟩
  · exact fun x hx ↦ (hA (mem_image_of_mem _ hx)).trans (le_max_right _ _)
  · intro x hx y₀ hy₀
    unfold sLocalTrace_orbHeight
    exact (hB (mem_image_of_mem _ (show (x, y₀) ∈ X ×ˢ Y from ⟨hx, hy₀⟩))).trans (le_max_right _ _)

/-- A compact set of norm-one idèles supplies angular representatives for
all S-idele classes after multiplying by the projected canonical section. -/
private theorem sLocalTrace_exists_compact_angular_representatives :
    ∃ Y : Set Iₛ, IsCompact Y ∧ (∀ y₀ ∈ Y, sIdeleNorm F S y₀ = 1) ∧
      ∀ q : Jₛ, ∃ y₀ ∈ Y, (QuotientGroup.mk (y₀ *
        sLocalTrace_projectedCanonicalSection (F := F) (S := S) (sIdeleQuotientNorm F S q)) : Jₛ) = q := by
  classical
  let π : Iₛ → Jₛ := QuotientGroup.mk
  let Q : Set Jₛ := {q | sIdeleQuotientNorm F S q = 1}
  let N₁ : Set Iₛ := {x | sIdeleNorm F S x = 1}
  have hQ : IsCompact Q :=
    (isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (isCompact_singleton (x := 1))
  have hN₁ : IsClosed N₁ := isClosed_eq sLocalTrace_sIdeleNorm_continuous continuous_const
  choose U hUc hU using fun x : Iₛ ↦ exists_compact_mem_nhds x
  let Uimg (x : Iₛ) : Set Jₛ := π '' interior (U x)
  have hV (x : Iₛ) : IsOpen (Uimg x) := QuotientGroup.isOpenMap_coe _ isOpen_interior
  have hCover : Q ⊆ ⋃ x, Uimg x := by
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact mem_iUnion.mpr ⟨x, mem_image_of_mem _ (mem_interior_iff_mem_nhds.mpr (hU x))⟩
  obtain ⟨s, hs⟩ := hQ.elim_finite_subcover Uimg hV hCover
  let L : Set Iₛ := ⋃ x : s, U x
  let Y : Set Iₛ := L ∩ N₁
  have hL : IsCompact L := isCompact_iUnion (fun x ↦ hUc x)
  have hLift (q : Jₛ) (hq : q ∈ Q) : ∃ y₀ ∈ Y, π y₀ = q := by
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hs hq)
    obtain ⟨hi', x, hx, rfl⟩ := mem_iUnion.mp hi
    refine ⟨x, ⟨mem_iUnion.mpr ⟨⟨i, hi'⟩, interior_subset hx⟩, ?_⟩, rfl⟩
    exact (sIdeleQuotientNorm_mk F S x).symm.trans hq
  refine ⟨Y, hL.inter_right hN₁, fun y hy ↦ hy.2, fun q ↦ ?_⟩
  let τ := sLocalTrace_projectedCanonicalSection (F := F) (S := S)
  let t := sIdeleQuotientNorm F S q
  have ha : q / π (τ t) ∈ Q := by
    change sIdeleQuotientNorm F S (q / QuotientGroup.mk (τ t)) = 1
    rw [map_div, sIdeleQuotientNorm_mk, show sIdeleNorm F S (τ t) = t from
      sIdeleNorm_project_canonicalSection F S t]
    exact div_self' _
  obtain ⟨y₀, hy₀, hq⟩ := hLift _ ha
  refine ⟨y₀, hy₀, ?_⟩
  change (QuotientGroup.mk (y₀ * τ t) : Jₛ) = q
  rw [QuotientGroup.mk_mul, show (QuotientGroup.mk y₀ : Jₛ) = q / π (τ t) from hq]
  exact div_mul_cancel _ _


/-- The radial bound uses `D` powers of the local sup norm and the height bound
uses one additional power. -/
private theorem sLocalTrace_inv_pow_succ_le_of_height {D : ℕ} {z t H A B : ℝ}
    (hz : 0 < z) (ht : 0 < t) (hH : 0 < H)
    (hrad : t ≤ A * z ^ D) (hheight : H ≤ B * z) :
    (z ^ (D + 1))⁻¹ ≤ (A * B / t) * H⁻¹ := by
  have hab : t * H ≤ (A * B) * z ^ (D + 1) := calc
    _ ≤ (A * z ^ D) * (B * z) := mul_le_mul hrad hheight hH.le (ht.le.trans hrad)
    _ = _ := by rw [pow_succ]; ring
  calc
    _ = 1 / z ^ (D + 1) := (one_div _).symm
    _ ≤ A * B / (t * H) := (div_le_div_iff₀ (pow_pos hz _) (mul_pos ht hH)).mpr
      (by simpa only [one_mul] using hab)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring

/-- The same split from a root bound on the normalized radial variable. -/
private theorem sLocalTrace_inv_pow_succ_le_of_root_height {D : ℕ} {z t H A B : ℝ}
    (hD : D ≠ 0) (hz : 0 < z) (ht : 0 < t) (hH : 0 < H) (hA : 0 < A)
    (hroot : (t / A) ^ ((D : ℝ)⁻¹) ≤ z) (hheight : H ≤ B * z) :
    (z ^ (D + 1))⁻¹ ≤ (A * B / t) * H⁻¹ := by
  have hratio : 0 ≤ t / A := div_nonneg ht.le hA.le
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hratio _) hroot D
  rw [Real.rpow_inv_natCast_pow hratio hD] at hpow
  exact sLocalTrace_inv_pow_succ_le_of_height hz ht hH
    (by simpa only [mul_comm (z ^ D) A] using (div_le_iff₀ hA).mp hpow) hheight

/-- A square-root decay estimate controls the small-radius orbit terms with
any height exponent at most one half. -/
private theorem sLocalTrace_inv_sqrt_le_of_height {z t H B q : ℝ}
    (hz : 1 ≤ z) (ht : 0 < t) (hH : 0 < H) (hB : 0 ≤ B)
    (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) (hheight : H ≤ (B / t) * z) :
    (Real.sqrt z)⁻¹ ≤ (B ^ q / t ^ q) * (H ^ q)⁻¹ := by
  have hz₀ : 0 < z := zero_lt_one.trans_le hz
  have hinv : z⁻¹ ≤ (B / t) / H := by
    rw [← one_div]
    exact (div_le_div_iff₀ hz₀ hH).mpr (by simpa only [one_mul] using hheight)
  calc
    _ = z ^ (-(1 / 2 : ℝ)) := by rw [Real.sqrt_eq_rpow, Real.rpow_neg hz₀.le]
    _ ≤ z ^ (-q) := Real.rpow_le_rpow_of_exponent_le hz (neg_le_neg hq')
    _ = z⁻¹ ^ q := Real.rpow_neg_eq_inv_rpow _ _
    _ ≤ ((B / t) / H) ^ q := Real.rpow_le_rpow (inv_nonneg.mpr hz₀.le) hinv hq
    _ = _ := by rw [Real.div_rpow (div_nonneg hB ht.le) hH.le, Real.div_rpow hB ht.le,
        div_eq_mul_inv]

/-- A scalar bound times a summable height dominates the orbit series and its
absolute sum. -/
private theorem sLocalTrace_summable_norm_of_radial_height {ι E : Type*} [SeminormedAddCommGroup E]
    {u : ι → E} {w : ι → ℝ} (hw : Summable w) {C : ℝ}
    (h : ∀ i, ‖u i‖ ≤ C * w i) :
    Summable (fun i ↦ ‖u i‖) ∧ (∑' i, ‖u i‖) ≤ C * ∑' i, w i := by
  have hs := hw.mul_left C
  have habs := Summable.of_nonneg_of_le (fun i ↦ norm_nonneg (u i)) h hs
  refine ⟨habs, ?_⟩
  rw [← tsum_mul_left]
  exact habs.tsum_le_tsum h hs

/-- Decay of order `D + 1` in local sup height gives summable orbit majorants
with the required small- and large-radius exponents. The prefactor bound is
the same compact-output estimate used for the local orbit bound. -/
private theorem sLocalTraceCutoffKernel_radial_orbit_majorant_of_decay
    (f : BruhatCompactSupport Iₛ) (ρ : Iₛ → ℂ) (b : ℝ → ℂ) {X Y : Set Iₛ}
    (hX : IsCompact X) (hY : IsCompact Y) (hYnorm : ∀ y₀ ∈ Y, sIdeleNorm F S y₀ = 1)
    {δ P₀ : ℝ} (hδ : 0 < δ) (hP₀ : 0 ≤ P₀)
    (hpre : ∀ x ∈ X, δ ≤ normS(x) ∧
      ‖ρ x * (sLocalTraceMeasureFactor S : ℂ) / (normS(x) : ℂ)‖ ≤ P₀)
    (hFourier : 0 < δ → ∃ B ≥ 0, ∀ t : ℝ, δ ≤ t → ∀ r : Eₛ,
      ‖∫ w : Eₛ, b (modS(w) / t) * fourierₛ (sLocalTraceEta f 1) w *
        (ψₛ (w * r) : ℂ) ∂νₛ‖ ≤ B / orbHeight(r + 1) ^
          (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1)) :
    ∃ C ≥ 0, ∀ x ∈ X, ∀ y₀ ∈ Y, ∀ (t : ℝ≥0ˣ) (ξ : Hₛ),
      let y := y₀ * sLocalTrace_projectedCanonicalSection (F := F) (S := S) t
      let k := ‖sLocalTraceCutoffKernel f ρ (fun v ↦ b (modS(v))) x (ξ.val * y).val‖
      let H := orbHeight(ξ.val.val)
      ((t.val : ℝ) ≤ 1 → k ≤ C * (t.val : ℝ) ^ (-(1 / 4 : ℝ)) * (H ^ (1 / 4 : ℝ))⁻¹) ∧
      (1 ≤ (t.val : ℝ) → k ≤ C * (t.val : ℝ)⁻¹ * H⁻¹) := by
  obtain ⟨A, hA, B, hB, hAN, hBH⟩ := sLocalTrace_compact_orbit_geometry hX hY
  obtain ⟨P₁, hP₁, hdecay⟩ := hFourier hδ
  let P := P₀ * P₁
  let D := (∑ w : InfinitePlace F, w.mult) + Fintype.card S
  let G := max (B ^ (1 / 4 : ℝ)) (A * B)
  let C := P * G
  have hP : 0 ≤ P := mul_nonneg hP₀ hP₁
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  have hC : 0 ≤ C := mul_nonneg hP ((Real.rpow_nonneg hB₀ _).trans (le_max_left _ _))
  refine ⟨C, hC, fun x hx y₀ hy₀ t ξ ↦ ?_⟩
  intro y k H
  let u := x⁻¹ * (ξ.val * y)
  let uVal : Eₛ := u.val
  let r := uVal - 1
  let U := orbHeight(uVal)
  have hr : r + 1 = uVal := sub_add_cancel uVal (1 : Eₛ)
  have ht : 0 < (t.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
  have hU₁ : 1 ≤ U := le_max_left _ _
  have hU : 0 < U := zero_lt_one.trans_le hU₁
  have hH : 0 < H := zero_lt_one.trans_le (le_max_left _ _)
  have hker : k ≤ P * (U ^ (D + 1))⁻¹ := by
    have hdec := hdecay (normS(x)) (hpre x hx).1 r
    rw [hr] at hdec
    dsimp only [k]
    rw [sLocalTraceCutoffKernel_scaled_radial_fourier, norm_mul]
    exact (mul_le_mul (hpre x hx).2 hdec (norm_nonneg _) hP₀).trans_eq
      (by change P₀ * (P₁ / U ^ (D + 1)) = _; dsimp only [P]; rw [div_eq_mul_inv, mul_assoc])
  have hgrowth := sLocalTrace_radialOrbit_growth x y₀ (hYnorm y₀ hy₀) t ξ
  dsimp only at hgrowth
  have hRad : (t.val : ℝ) ≤ A * U ^ D :=
    hgrowth.1.trans (mul_le_mul_of_nonneg_right (hAN x hx) (by positivity))
  have hHt : H ≤ B * max 1 ((t.val : ℝ)⁻¹) * U :=
    hgrowth.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hBH x hx y₀ hy₀) (by positivity)) hU.le)
  constructor
  · intro hsmall
    have hti : 1 ≤ (t.val : ℝ)⁻¹ := (one_le_inv₀ ht).mpr hsmall
    have hHt' : H ≤ (B / (t.val : ℝ)) * U := by
      simpa only [max_eq_right hti, div_eq_mul_inv] using hHt
    have hweak : (U ^ (D + 1))⁻¹ ≤ (Real.sqrt U)⁻¹ := by
      apply inv_anti₀ (Real.sqrt_pos.mpr hU)
      refine ((Real.sqrt_le_self_iff).2 (Or.inr hU₁)).trans ?_
      simpa only [pow_one] using pow_le_pow_right₀ hU₁ (Nat.succ_le_succ (Nat.zero_le D))
    have hs := sLocalTrace_inv_sqrt_le_of_height (q := (1 / 4 : ℝ)) hU₁ ht hH
      hB₀ (by norm_num) (by norm_num) hHt'
    calc
      _ ≤ P * ((B ^ (1 / 4 : ℝ) / (t.val : ℝ) ^ (1 / 4 : ℝ)) * (H ^ (1 / 4 : ℝ))⁻¹) :=
        hker.trans (mul_le_mul_of_nonneg_left (hweak.trans hs) hP)
      _ = (P * B ^ (1 / 4 : ℝ)) * (t.val : ℝ) ^ (-(1 / 4 : ℝ)) * (H ^ (1 / 4 : ℝ))⁻¹ := by
        rw [Real.rpow_neg ht.le, div_eq_mul_inv]
        ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_left _ _) hP) (by positivity)) (by positivity)
  · intro hlarge
    have hti : (t.val : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hlarge
    have hHt' : H ≤ B * U := by simpa only [max_eq_left hti, mul_one] using hHt
    have hs := sLocalTrace_inv_pow_succ_le_of_height hU ht hH hRad hHt'
    calc
      _ ≤ P * ((A * B / (t.val : ℝ)) * H⁻¹) :=
        hker.trans (mul_le_mul_of_nonneg_left hs hP)
      _ = (P * (A * B)) * (t.val : ℝ)⁻¹ * H⁻¹ := by rw [div_eq_mul_inv]; ring
      _ ≤ _ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (le_max_right _ _) hP) (by positivity)) (by positivity)

private theorem sLocalTraceCutoffKernel_radial_orbit_majorant
    (f : BruhatCompactSupport Iₛ) (ρ : Iₛ → ℂ) (b : ℝ → ℂ) {X Y : Set Iₛ}
    (hX : IsCompact X) (hY : IsCompact Y) (hYnorm : ∀ y₀ ∈ Y, sIdeleNorm F S y₀ = 1)
    {δ P₀ ε C₀ : ℝ} (hδ : 0 < δ) (hP₀ : 0 ≤ P₀)
    (hpre : ∀ x ∈ X, δ ≤ normS(x) ∧
      ‖ρ x * (sLocalTraceMeasureFactor S : ℂ) / (normS(x) : ℂ)‖ ≤ P₀)
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < ε) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 ε))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ y, 0 ≤ y → ‖iteratedDeriv j b y‖ ≤ C₀) :
    ∃ C ≥ 0, ∀ x ∈ X, ∀ y₀ ∈ Y, ∀ (t : ℝ≥0ˣ) (ξ : Hₛ),
      let y := y₀ * sLocalTrace_projectedCanonicalSection (F := F) (S := S) t
      let k := ‖sLocalTraceCutoffKernel f ρ (fun v ↦ b (modS(v))) x (ξ.val * y).val‖
      let H := orbHeight(ξ.val.val)
      ((t.val : ℝ) ≤ 1 → k ≤ C * (t.val : ℝ) ^ (-(1 / 4 : ℝ)) * (H ^ (1 / 4 : ℝ))⁻¹) ∧
      (1 ≤ (t.val : ℝ) → k ≤ C * (t.val : ℝ)⁻¹ * H⁻¹) := by
  apply sLocalTraceCutoffKernel_radial_orbit_majorant_of_decay f ρ b hX hY hYnorm hδ hP₀ hpre
  intro hδ'
  exact sLocalTrace_radialProfile_fourier_decay_nat f _ b hb hδ' hε hplateau hderiv

/-- The pointwise radial bounds give a jointly uniform absolutely summable
orbit series, with the same powers of the input radius as for one orbit. -/
private theorem sLocalTraceCutoffKernel_radial_orbit_sum
    (f : BruhatCompactSupport Iₛ) (ρ : Iₛ → ℂ) (b : ℝ → ℂ) {X Y : Set Iₛ}
    (hX : IsCompact X) (hY : IsCompact Y) (hYnorm : ∀ y₀ ∈ Y, sIdeleNorm F S y₀ = 1)
    {δ P₀ ε C₀ : ℝ} (hδ : 0 < δ) (hP₀ : 0 ≤ P₀)
    (hpre : ∀ x ∈ X, δ ≤ normS(x) ∧
      ‖ρ x * (sLocalTraceMeasureFactor S : ℂ) / (normS(x) : ℂ)‖ ≤ P₀)
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < ε) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 ε))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ y, 0 ≤ y → ‖iteratedDeriv j b y‖ ≤ C₀)
    :
    ∃ C ≥ 0, ∀ x ∈ X, ∀ y₀ ∈ Y, ∀ (t : ℝ≥0ˣ),
      let y := y₀ * sLocalTrace_projectedCanonicalSection (F := F) (S := S) t
      let k := fun ξ : Hₛ ↦ sLocalTraceCutoffKernel f ρ (fun v ↦ b (modS(v))) x (ξ.val * y).val
      Summable (fun ξ ↦ ‖k ξ‖) ∧
      ((t.val : ℝ) ≤ 1 → (∑' ξ, ‖k ξ‖) ≤ C * (t.val : ℝ) ^ (-(1 / 4 : ℝ))) ∧
      (1 ≤ (t.val : ℝ) → (∑' ξ, ‖k ξ‖) ≤ C * (t.val : ℝ)⁻¹) := by
  obtain ⟨P, hP, hbound⟩ := sLocalTraceCutoffKernel_radial_orbit_majorant
    f ρ b hX hY hYnorm hδ hP₀ hpre hb hε hplateau hderiv
  let W (ξ : Hₛ) := (orbHeight(ξ.val.val) ^ (1 / 4 : ℝ))⁻¹
  have hheight : Summable W :=
    sLocalTrace_height_rpow_summable (F := F) (S := S) (q := 1 / 4) (by norm_num)
  have hW : ∀ ξ, 0 ≤ W ξ := fun ξ ↦
    inv_nonneg.mpr (Real.rpow_nonneg (sLocalTrace_orbHeight_nonneg ξ.val.val) _)
  have hcmp (ξ : Hₛ) : (orbHeight(ξ.val.val))⁻¹ ≤ W ξ := by
    have hξ : 1 ≤ orbHeight(ξ.val.val) := le_max_left _ _
    apply inv_anti₀ (Real.rpow_pos_of_pos (zero_lt_one.trans_le hξ) _)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hξ (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have hsumW : 0 ≤ ∑' ξ, W ξ := tsum_nonneg hW
  refine ⟨P * (∑' ξ, W ξ), mul_nonneg hP hsumW, fun x hx y₀ hy₀ t ↦ ?_⟩
  intro y k
  have ht : 0 ≤ (t.val : ℝ) := NNReal.coe_nonneg _
  have hsmall (hs : (t.val : ℝ) ≤ 1) :=
    sLocalTrace_summable_norm_of_radial_height (u := k) hheight
      (C := P * (t.val : ℝ) ^ (-(1 / 4 : ℝ))) fun ξ ↦ (hbound x hx y₀ hy₀ t ξ).1 hs
  have hlarge (hl : 1 ≤ (t.val : ℝ)) :=
    sLocalTrace_summable_norm_of_radial_height (u := k) hheight
      (C := P * (t.val : ℝ)⁻¹) fun ξ ↦
        ((hbound x hx y₀ hy₀ t ξ).2 hl).trans
          (mul_le_mul_of_nonneg_left (hcmp ξ) (mul_nonneg hP (inv_nonneg.mpr ht)))
  refine ⟨(le_total (t.val : ℝ) 1).elim (fun h ↦ (hsmall h).1) (fun h ↦ (hlarge h).1), ?_, ?_⟩
  · exact fun h ↦ (hsmall h).2.trans_eq (by change (P * _) * (∑' ξ, W ξ) = _; ring)
  · exact fun h ↦ (hlarge h).2.trans_eq (by change (P * _) * (∑' ξ, W ξ) = _; ring)

/-- Fourier decay of order one suffices for a single summable majorant of the
unmasked orbit kernel on a product of compact S-idèle sets. -/
private theorem sLocalTraceCutoffKernel_raw_radial_compact_majorant
    (f : BruhatCompactSupport Iₛ) (b : ℝ → ℂ) (hb : ContDiff ℝ (2 : ℕ) b)
    {ε C₀ : ℝ} (hε : 0 < ε) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 ε))
    (hderiv : ∀ j ≤ (2 : ℕ), ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ C₀)
    {X Y : Set Iₛ} (hX : IsCompact X) (hY : IsCompact Y) :
    ∃ W : Hₛ → ℝ, Summable W ∧ ∀ ξ x, x ∈ X → ∀ y ∈ Y,
      ‖sLocalTraceCutoffKernel f (fun _ ↦ 1) (fun w ↦ b (modS(w))) x (ξ.val * y).val‖ ≤ W ξ := by
  have hpos (x : Iₛ) : 0 < normS(x) := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S x))
  have hN : Continuous (fun x : Iₛ ↦ normS(x)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp sLocalTrace_sIdeleNorm_continuous)
  obtain ⟨D, hD⟩ := (hX.image (hN.inv₀ fun x ↦ (hpos x).ne')).bddAbove
  let δ := (max 1 D)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))
  have hδx (x : Iₛ) (hx : x ∈ X) : δ ≤ normS(x) := by
    have hbound : normS(x)⁻¹ ≤ max 1 D :=
      (hD (mem_image_of_mem _ hx)).trans (le_max_right _ _)
    simpa only [δ, inv_inv] using inv_anti₀ (inv_pos.mpr (hpos x)) hbound
  let P := ‖(sLocalTraceMeasureFactor S : ℂ)‖ / δ
  have hP : 0 ≤ P := div_nonneg (norm_nonneg _) hδ.le
  have hpre (x : Iₛ) (hx : x ∈ X) :
      ‖(sLocalTraceMeasureFactor S : ℂ) / (normS(x) : ℂ)‖ ≤ P := by
    rw [norm_div, Complex.norm_real (normS(x)), Real.norm_eq_abs (normS(x)), abs_of_pos (hpos x)]
    exact div_le_div_of_nonneg_left (norm_nonneg _) hδ (hδx x hx)
  obtain ⟨K, hK, hdecay⟩ :=
    sLocalTrace_radialProfile_fourier_decay_nat f 1 b hb hδ hε hplateau hderiv
  obtain ⟨_, _, B, hB, _, hgeom⟩ := sLocalTrace_compact_orbit_geometry hX hY
  let W (ξ : Hₛ) := (orbHeight(ξ.val.val) ^ (1 / 4 : ℝ))⁻¹
  have hW : Summable W :=
    sLocalTrace_height_rpow_summable (F := F) (S := S) (q := 1 / 4) (by norm_num)
  refine ⟨fun ξ ↦ P * K * B * W ξ, hW.mul_left (P * K * B), ?_⟩
  intro ξ x hx y hy
  let u := x⁻¹ * (ξ.val * y)
  let U := orbHeight(u.val)
  let H := orbHeight(ξ.val.val)
  have hU : 0 < U := zero_lt_one.trans_le (le_max_left _ _)
  have hH₁ : 1 ≤ H := le_max_left _ _
  have hH : 0 < H := zero_lt_one.trans_le hH₁
  have hrec : ξ.val = (x * y⁻¹) * u := by
    calc
      _ = (x * x⁻¹) * (y⁻¹ * y) * ξ.val := by simp
      _ = _ := by dsimp only [u]; ac_rfl
  have hval : (ξ.val.val : Eₛ) = (x.val * (y⁻¹).val) * u.val := by
    simpa only [Units.val_mul] using congrArg (fun a : Iₛ ↦ a.val) hrec
  have hHU : H ≤ B * U := by
    change orbHeight(ξ.val.val) ≤ B * U
    rw [hval]
    exact (sLocalTrace_max_one_norm_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right (hgeom x hx y hy) hU.le)
  have hinv : U⁻¹ ≤ B * H⁻¹ := by
    rw [← one_div U, ← div_eq_mul_inv]
    exact (div_le_div_iff₀ hU hH).2 (by simpa only [one_mul] using hHU)
  have hcmp : H⁻¹ ≤ W ξ := by
    apply inv_anti₀ (Real.rpow_pos_of_pos hH _)
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hH₁ (show (1 / 4 : ℝ) ≤ 1 by norm_num)
  have hker : ‖sLocalTraceCutoffKernel f (fun _ ↦ 1) (fun w ↦ b (modS(w))) x (ξ.val * y).val‖ ≤
      P * (K / U) := by
    let uVal : Eₛ := (x⁻¹).val * (ξ.val * y).val
    let r := uVal - (1 : Eₛ)
    have hval' : uVal = (u.val : Eₛ) := by simp only [uVal, u, Units.val_mul]
    have hr : r + 1 = (u.val : Eₛ) := (sub_add_cancel uVal (1 : Eₛ)).trans hval'
    have hdec := hdecay (normS(x)) (hδx x hx) r
    rw [hr, pow_one] at hdec
    rw [sLocalTraceCutoffKernel_scaled_radial_fourier, one_mul, norm_mul]
    exact mul_le_mul (hpre x hx) hdec (norm_nonneg _) hP
  calc
    _ ≤ P * (K / U) := hker
    _ = (P * K) * U⁻¹ := by rw [div_eq_mul_inv, mul_assoc]
    _ ≤ (P * K) * (B * H⁻¹) := mul_le_mul_of_nonneg_left hinv (mul_nonneg hP hK)
    _ = (P * K * B) * H⁻¹ := (mul_assoc _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hcmp (mul_nonneg (mul_nonneg hP hK) (zero_le_one.trans hB))

/-- Compact angular representatives and the canonical norm section give one
compact set of idèles representing all classes of a compact output set. The
same angular set serves every input radius. -/
private theorem sLocalTrace_exists_compact_output_lifts {Z : Set Jₛ} (hZ : IsCompact Z) :
    ∃ X Y : Set Iₛ, IsCompact X ∧ IsCompact Y ∧
      (∀ y₀ ∈ Y, sIdeleNorm F S y₀ = 1) ∧
      (∀ q ∈ Z, ∃ x ∈ X, (QuotientGroup.mk x : Jₛ) = q) ∧
      ∀ q : Jₛ, ∃ y₀ ∈ Y, (QuotientGroup.mk (y₀ *
        sLocalTrace_projectedCanonicalSection (F := F) (S := S) (sIdeleQuotientNorm F S q)) : Jₛ) = q := by
  obtain ⟨Y, hY, hYnorm, hYrep⟩ :=
    sLocalTrace_exists_compact_angular_representatives (F := F) (S := S)
  let τ := sLocalTrace_projectedCanonicalSection (F := F) (S := S)
  have hτ : Continuous τ :=
    ((continuous_adeleProjection F S).units_map _).comp (canonicalIdeleNormSection_continuous F)
  let N := sIdeleQuotientNorm F S
  have hN : Continuous N := (continuousSIdeleQuotientNorm F S).continuous
  let mulRep (p : Iₛ × Jₛ) : Iₛ := p.1 * τ (N p.2)
  have hmulRep : Continuous mulRep := continuous_fst.mul ((hτ.comp hN).comp continuous_snd)
  let X := mulRep '' (Y ×ˢ Z)
  refine ⟨X, Y, (hY.prod hZ).image hmulRep, hY, hYnorm, ?_, hYrep⟩
  intro q hq
  obtain ⟨y₀, hy₀, hrep⟩ := hYrep q
  exact ⟨mulRep (y₀, q), mem_image_of_mem _ ⟨hy₀, hq⟩, hrep⟩

/-- Absolute summability and the sum of the norms of a kernel orbit are
independent of both quotient representatives under simultaneous subgroup
covariance. If the representatives change by left multiplication by `η`
and `ζ`, respectively, the reindexing is `ξ ↦ η⁻¹ * ξ * ζ`. -/
theorem sLocalTrace_absoluteOrbit_congr_of_mk_eq
    {G E : Type*} [CommGroup G] [SeminormedAddCommGroup E]
    (H : Subgroup G) (K : G → G → E)
    (hcov : ∀ (η : H) x y, K (η.val * x) (η.val * y) = K x y)
    {x y x' y' : G} (hx : (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk x')
    (hy : (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk y') :
    (Summable (fun ξ : H ↦ ‖K x' (ξ.val * y')‖) ↔
      Summable (fun ξ : H ↦ ‖K x (ξ.val * y)‖)) ∧
    (∑' ξ : H, ‖K x' (ξ.val * y')‖) = ∑' ξ : H, ‖K x (ξ.val * y)‖ := by
  have hrep {a a' : G} (h : (QuotientGroup.mk a : G ⧸ H) = QuotientGroup.mk a') :
      ∃ η : H, η.val * a = a' := by
    refine ⟨⟨a⁻¹ * a', QuotientGroup.eq.mp h⟩, ?_⟩
    change (a⁻¹ * a') * a = a'
    rw [mul_comm (a⁻¹ * a') a, mul_inv_cancel_left]
  obtain ⟨η, rfl⟩ := hrep hx
  obtain ⟨ζ, rfl⟩ := hrep hy
  let a (ξ : H) : ℝ := ‖K x (ξ.val * y)‖
  let e : H ≃ H := (Equiv.mulRight ζ).trans (Equiv.mulLeft η⁻¹)
  have hreindex : (fun ξ : H ↦ ‖K (η.val * x) (ξ.val * (ζ.val * y))‖) = a ∘ e := by
    funext ξ
    apply congrArg norm
    change K (η.val * x) (ξ.val * (ζ.val * y)) =
      K x ((η.val⁻¹ * (ξ.val * ζ.val)) * y)
    have h := hcov η x ((η.val⁻¹ * (ξ.val * ζ.val)) * y)
    simpa only [mul_assoc, mul_inv_cancel_left] using h
  rw [hreindex]
  exact ⟨e.summable_iff, e.tsum_eq a⟩

/-- The fixed-annulus estimates on compact lifts also bound the sum of the
absolute raw orbit terms at arbitrary idelic representatives. -/
private theorem sLocalTrace_rawOrbit_radial_bound_on_compact
    (f : BruhatCompactSupport Iₛ) (ρ : Jₛ → ℂ) (hρ : ∀ q, ‖ρ q‖ ≤ 1) (b : ℝ → ℂ)
    (hcov : ∀ (ξ : Hₛ) (x y : Iₛ),
      sLocalTraceCutoffKernel f (fun a ↦ ρ (QuotientGroup.mk a))
        (fun v ↦ b (modS(v))) (ξ.val * x) (ξ.val * y).val =
      sLocalTraceCutoffKernel f (fun a ↦ ρ (QuotientGroup.mk a))
        (fun v ↦ b (modS(v))) x y.val)
    {Z : Set Jₛ} (hZ : IsCompact Z) {ε C₀ : ℝ}
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < ε) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 ε))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ C₀)
    (hheight : Summable fun ξ : Hₛ ↦ (orbHeight(ξ.val.val) ^ (1 / 4 : ℝ))⁻¹) :
    ∃ C ≥ 0, ∀ x : Iₛ, (QuotientGroup.mk x : Jₛ) ∈ Z → ∀ y : Iₛ,
      let t := normS(y)
      let a (ξ : Hₛ) := ‖sLocalTraceCutoffKernel f (fun z ↦ ρ (QuotientGroup.mk z))
        (fun v ↦ b (modS(v))) x (ξ.val * y).val‖
      Summable a ∧
      (t ≤ 1 → (∑' ξ, a ξ) ≤ C * t ^ (-(1 / 4 : ℝ))) ∧
      (1 ≤ t → (∑' ξ, a ξ) ≤ C * t⁻¹) := by
  obtain ⟨X, Y, hX, hY, hYnorm, hXrep, hYrep⟩ := sLocalTrace_exists_compact_output_lifts hZ
  let ρI : Iₛ → ℂ := fun a ↦ ρ (QuotientGroup.mk a)
  have hpos (x : Iₛ) : 0 < normS(x) := NNReal.coe_pos.mpr (Units.zero_lt (sIdeleNorm F S x))
  have hN : Continuous (fun x : Iₛ ↦ normS(x)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp sLocalTrace_sIdeleNorm_continuous)
  obtain ⟨D, hD⟩ := (hX.image (hN.inv₀ fun x ↦ (hpos x).ne')).bddAbove
  let δ := (max 1 D)⁻¹
  have hδ : 0 < δ := inv_pos.mpr (zero_lt_one.trans_le (le_max_left _ _))
  let P₀ := ‖(sLocalTraceMeasureFactor S : ℂ)‖ / δ
  have hP₀ : 0 ≤ P₀ := div_nonneg (norm_nonneg _) hδ.le
  have hpre (x : Iₛ) (hx : x ∈ X) : δ ≤ normS(x) ∧
      ‖ρI x * (sLocalTraceMeasureFactor S : ℂ) / (normS(x) : ℂ)‖ ≤ P₀ := by
    have hbound : normS(x)⁻¹ ≤ max 1 D :=
      (hD (mem_image_of_mem _ hx)).trans (le_max_right _ _)
    have hδx : δ ≤ normS(x) := by
      simpa only [δ, inv_inv] using inv_anti₀ (inv_pos.mpr (hpos x)) hbound
    refine ⟨hδx, ?_⟩
    rw [norm_div, norm_mul, Complex.norm_real (normS(x)), Real.norm_eq_abs (normS(x)), abs_of_pos (hpos x)]
    calc
      _ ≤ ‖(sLocalTraceMeasureFactor S : ℂ)‖ / normS(x) := by
        apply (div_le_div_iff_of_pos_right (hpos x)).2
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (hρ (QuotientGroup.mk x)) (norm_nonneg _)
      _ ≤ P₀ := div_le_div_of_nonneg_left (norm_nonneg _) hδ hδx
  obtain ⟨C, hC, hOrb⟩ := sLocalTraceCutoffKernel_radial_orbit_sum
    f ρI b hX hY hYnorm hδ hP₀ hpre hb hε hplateau hderiv
  refine ⟨C, hC, fun x hx y ↦ ?_⟩
  obtain ⟨x₀, hx₀, hqx⟩ := hXrep (QuotientGroup.mk x) hx
  obtain ⟨y₀, hy₀, hqy⟩ := hYrep (QuotientGroup.mk y)
  let t := sIdeleQuotientNorm F S (QuotientGroup.mk y)
  let z := y₀ * sLocalTrace_projectedCanonicalSection (F := F) (S := S) t
  let K (x y : Iₛ) := sLocalTraceCutoffKernel f ρI (fun v ↦ b (modS(v))) x y.val
  have hreindex := sLocalTrace_absoluteOrbit_congr_of_mk_eq Hₛ K hcov
    (x := x₀) (y := z) (x' := x) (y' := y) hqx hqy
  obtain ⟨hSum, hsmall, hlarge⟩ := hOrb x₀ hx₀ y₀ hy₀ t
  refine ⟨hreindex.1.mpr hSum, ?_, ?_⟩
  · intro ht
    rw [hreindex.2]
    simpa only [K, z, t, sIdeleQuotientNorm_mk] using
      hsmall (by simpa only [t, sIdeleQuotientNorm_mk] using ht)
  · intro ht
    rw [hreindex.2]
    simpa only [K, z, t, sIdeleQuotientNorm_mk] using
      hlarge (by simpa only [t, sIdeleQuotientNorm_mk] using ht)

private theorem continuous_uncurry_of_compact_orbit_tsum {X Y ι : Type*}
    [TopologicalSpace X] [LocallyCompactSpace X] [TopologicalSpace Y]
    (π : X → Y) (hπ : IsOpenQuotientMap π) (κ : Y → Y → ℂ) (term : ι → X × X → ℂ)
    (ht : ∀ i, Continuous (term i))
    (hmajor : ∀ K L : Set X, IsCompact K → IsCompact L →
      ∃ W : ι → ℝ, Summable W ∧ ∀ i p, p ∈ K ×ˢ L → ‖term i p‖ ≤ W i)
    (hrep : ∀ x y, κ (π x) (π y) = ∑' i, term i (x, y)) :
    Continuous (Function.uncurry κ) := by
  have hsum : Continuous (fun p : X × X ↦ ∑' i, term i p) := by
    rw [continuous_iff_continuousAt]
    intro p
    obtain ⟨K, hK, hx⟩ := exists_compact_mem_nhds p.1
    obtain ⟨L, hL, hy⟩ := exists_compact_mem_nhds p.2
    obtain ⟨W, hW, hbound⟩ := hmajor K L hK hL
    have hc : ContinuousOn (fun p : X × X ↦ ∑' i, term i p) (K ×ˢ L) :=
      continuousOn_tsum (fun i ↦ (ht i).continuousOn) hW hbound
    exact hc.continuousAt (prod_mem_nhds hx hy)
  apply (hπ.prodMap hπ).continuous_comp_iff.mp
  change Continuous (fun p : X × X ↦ κ (π p.1) (π p.2))
  exact hsum.congr fun p ↦ (hrep p.1 p.2).symm


local notation "A" => Aₛ
local notation "I" => Iₛ
local notation "H" => Hₛ
local notation "J" => Jₛ
local notation "Q" => continuousSIdeleQuotientNorm F S
local notation "M(" z ")" => modS(z)

/-- Joint continuity descends from compact-local uniform convergence of the
unmasked additive orbit series. -/
theorem exists_continuous_sLocalTraceOrbitSeries_of_localBounds
    (f : BruhatCompactSupport I) (σ : A → ℂ)
    (hσ : ∀ (η : H) z, σ (η.val.val * z) = σ z)
    (hK : Continuous fun p : I × I ↦ sLocalTraceCutoffKernel f (fun _ ↦ 1) σ p.1 p.2.val)
    (hmajor : ∀ X Y : Set I, IsCompact X → IsCompact Y →
      ∃ W : H → ℝ, Summable W ∧ ∀ ξ x, x ∈ X → ∀ y ∈ Y,
        ‖sLocalTraceCutoffKernel f (fun _ ↦ 1) σ x (ξ.val * y).val‖ ≤ W ξ) :
    ∃ κ : J → J → ℂ, Continuous (Function.uncurry κ) ∧ ∀ x y : I,
      κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f (fun _ ↦ 1) σ x (ξ.val * y).val := by
  obtain ⟨κ, hκ⟩ := exists_sLocalTraceOrbitSeries f (fun _ ↦ 1) σ (fun _ _ ↦ rfl) hσ
  let raw (p : I × I) : ℂ := sLocalTraceCutoffKernel f (fun _ ↦ 1) σ p.1 p.2.val
  change Continuous raw at hK
  let translate (ξ : H) (p : I × I) : I × I := (p.1, ξ.val * p.2)
  let term (ξ : H) := raw ∘ translate ξ
  have hterm (ξ : H) : Continuous (term ξ) := by
    have hT : Continuous (translate ξ) := continuous_fst.prodMk (continuous_const.mul continuous_snd)
    exact Continuous.comp (g := raw) (f := translate ξ) hK hT
  let π : I → J := QuotientGroup.mk
  have hπ : IsOpenQuotientMap π := QuotientGroup.isOpenQuotientMap_mk
  refine ⟨κ, continuous_uncurry_of_compact_orbit_tsum π hπ κ term hterm ?_ hκ, hκ⟩
  intro K L hK' hL
  obtain ⟨W, hW, hWbound⟩ := hmajor K L hK' hL
  exact ⟨W, hW, fun ξ p hp ↦ hWbound ξ p.1 hp.1 p.2 hp.2⟩

/-- A modulated cutoff acts on the output row of the continuous unmasked
orbit kernel. The resulting kernel is measurable and vanishes off the
compact output annulus, even for a cutoff with jumps. -/
theorem sLocalTrace_maskedOrbitSeries_measurable_and_output_support
    (f : BruhatCompactSupport I) (σ : A → ℂ)
    (κ : J → J → ℂ) (hκ : Continuous (Function.uncurry κ))
    (hrep : ∀ x y : I, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
      ∑' ξ : H, sLocalTraceCutoffKernel f (fun _ ↦ 1) σ x (ξ.val * y).val)
    {Λ ε : ℝ} {ρ : J → ℝ} (hρ : IsModulatedCutoff (continuousSIdeleQuotientNorm F S) Λ ε ρ) :
    let N := continuousSIdeleQuotientNorm F S
    let Z : Set J := {x | ((N x).val : ℝ) ∈ Icc Λ⁻¹ Λ}
    let K (x y : J) := (ρ x : ℂ) * κ x y
    IsCompact Z ∧ Measurable (Function.uncurry K) ∧
      (∀ x ∉ Z, ∀ y, K x y = 0) ∧
      ∀ x y : I, K (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f
          (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ)) σ x (ξ.val * y).val := by
  intro N Z K
  have hΛ : 0 < Λ⁻¹ := inv_pos.mpr hρ.radius_pos
  let e := Nonneg.unitsHomeomorphPos ℝ
  have hS : IsCompact ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc Λ⁻¹ Λ) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe,
      inter_eq_right.mpr fun t (ht : t ∈ Icc Λ⁻¹ Λ) ↦ mem_Ioi.mpr (hΛ.trans_le ht.1)]
    exact isCompact_Icc
  have hZ : IsCompact Z :=
    (isProperMap_sIdeleQuotientNorm F S).isCompact_preimage (e.isCompact_preimage.mpr hS)
  have hmask : Measurable (fun p : J × J ↦ (ρ p.1 : ℂ)) :=
    Complex.measurable_ofReal.comp (hρ.measurable.comp measurable_fst)
  refine ⟨hZ, hmask.mul hκ.measurable, ?_, ?_⟩
  · intro x hx y
    have hz : ρ x = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρ.support_subset h))
    simp only [K, hz, Complex.ofReal_zero, zero_mul]
  · intro x y
    have hfactor (v : A) : sLocalTraceCutoffKernel f
        (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ)) σ x v =
        (ρ (QuotientGroup.mk x) : ℂ) * sLocalTraceCutoffKernel f (fun _ ↦ 1) σ x v := by
      simp only [sLocalTraceCutoffKernel, one_mul]
    simp only [K, hrep, hfactor, tsum_mul_left]

/-- Simultaneous norm-one translation preserves a descended orbit series whenever
it preserves the idelic kernel. The transfer is termwise in the projected S-units. -/
public theorem sLocalTraceOrbitSeries_covariant_of_normOne
    (K : I → I → ℂ) (κ : J → J → ℂ)
    (hRep : ∀ x y : I, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
      ∑' ξ : H, K x (ξ.val * y))
    (hCov : ∀ a : I, sIdeleNorm F S a = 1 →
      ∀ x y : I, K (a * x) (a * y) = K x y)
    (q y : J) (h : (sIdeleQuotientNorm F S).ker) :
    κ (q * h.val) (y * h.val) = κ q y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
  let a : I := h.val.out
  have haClass : (QuotientGroup.mk a : J) = h.val := QuotientGroup.out_eq' h.val
  have ha : sIdeleNorm F S a = 1 := by
    rw [← sIdeleQuotientNorm_mk F S a, haClass]
    exact MonoidHom.mem_ker.mp h.property
  have hLift :
      κ (QuotientGroup.mk (x * a)) (QuotientGroup.mk (z * a)) =
        κ (QuotientGroup.mk x) (QuotientGroup.mk z) := by
    rw [hRep (x * a) (z * a), hRep x z]
    apply tsum_congr
    intro ξ
    calc
      K (x * a) (ξ.val * (z * a)) = K (a * x) (a * (ξ.val * z)) := by
        rw [mul_comm x a, mul_comm z a, mul_left_comm ξ.val a z]
      _ = K x (ξ.val * z) := hCov a ha x (ξ.val * z)
  simpa only [QuotientGroup.mk_mul, haClass] using hLift

/-- The fixed-annulus half-density kernel has a jointly measurable quotient
representative, simultaneous norm-one covariance, and absolute radial orbit
bounds on every pair of idelic representatives. -/
public theorem exists_sLocalTrace_halfDensityOrbitKernel_fixed_annulus_data
    (f : BruhatCompactSupport I) (b : ℝ → ℂ) {Λ ερ εb Cb s : ℝ} {ρ : J → ℝ}
    (hρ : IsModulatedCutoff Q Λ ερ ρ) (hs : 0 ≤ s)
    (hb : ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) b)
    (hε : 0 < εb) (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 εb))
    (hderiv : ∀ j ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1),
      ∀ r, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ Cb) :
    let N (q : J) : ℝ := (Q q).val
    let Z : Set J := {q | N q ∈ Icc Λ⁻¹ Λ}
    let ν := intervalSobolevMeasure (sLocalQuotientTamagawaMeasure F S)
      (logSIdeleQuotientNorm F S) 0 0 s
    let K : I → A → ℂ := sLocalTraceCutoffKernel f
      (fun a ↦ (ρ (QuotientGroup.mk a) : ℂ)) (fun v ↦ b (M(v)))
    IsCompact Z ∧ ∃ (κ : J → J → ℂ) (C : ℝ), 0 ≤ C ∧
      Measurable (Function.uncurry κ) ∧
      (∀ q ∉ Z, ∀ y, κ q y = 0) ∧
      (∀ x y : I, κ (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, K x (ξ.val * y).val) ∧
      (∀ a : I, sIdeleNorm F S a = 1 → ∀ x y : I,
        K (a * x) (a * y).val = K x y.val) ∧
      (∀ (q y : J) (h : (sIdeleQuotientNorm F S).ker),
        κ (q * h.val) (y * h.val) = κ q y) ∧
      (∀ x y : I,
        let t : ℝ := (sIdeleNorm F S y).val
        let a (ξ : H) := ‖K x (ξ.val * y).val‖
        Summable a ∧
        (t ≤ 1 → (∑' ξ, a ξ) ≤ C * t ^ (-(1 / 4 : ℝ))) ∧
        (1 ≤ t → (∑' ξ, a ξ) ≤ C * t⁻¹)) ∧
      MemLp (fun p : J × J ↦ (Real.sqrt (N p.1 * N p.2) : ℂ) * κ p.1 p.2 /
        ((sLocalTraceMeasureFactor S : ℂ) *
          (intervalSobolevDensity 0 0 s (Real.log (N p.2)) : ℂ))) 2 (ν.prod ν) := by
  intro N Z ν K
  let π : I → J := QuotientGroup.mk
  let σ (z : A) := b (M(z))
  let ρI (x : I) : ℂ := ρ (π x)
  have hσInv (a : I) (ha : sIdeleNorm F S a = 1) (z : A) : σ (a.val * z) = σ z := by
    have hMa : M(a.val) = ((sIdeleNorm F S a).val : ℝ) := by
      simp [sIdeleNorm, Units.coe_prod]
    rw [ha] at hMa
    change M(a.val) = 1 at hMa
    apply congrArg b
    change (∏ w : InfinitePlace F, ‖a.val.1 w * z.1 w‖ ^ w.mult) *
      (∏ v : S, ‖a.val.2 v * z.2 v‖) = M(z)
    simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]
    calc
      _ = M(a.val) * M(z) := by ring
      _ = _ := by rw [hMa, one_mul]
  obtain ⟨p, _, hp, _⟩ := hρ.profile
  have hρInv (a : I) (ha : sIdeleNorm F S a = 1) (x : I) : ρI (a * x) = ρI x := by
    have hnorm : Q (π (a * x)) = Q (π x) := by
      change sIdeleQuotientNorm F S (QuotientGroup.mk (a * x)) =
        sIdeleQuotientNorm F S (QuotientGroup.mk x)
      rw [sIdeleQuotientNorm_mk, sIdeleQuotientNorm_mk, map_mul, ha, one_mul]
    have hρeq := (hp (π (a * x))).trans
      ((congrArg (fun t : ℝ≥0ˣ ↦ p (t.val : ℝ)) hnorm).trans (hp (π x)).symm)
    exact congrArg Complex.ofReal hρeq
  have hRawCov (a : I) (ha : sIdeleNorm F S a = 1) (x y : I) :
      K (a * x) (a * y).val = K x y.val := by
    simpa only [Units.val_mul] using
      sLocalTraceCutoffKernel_covariant_of_normOne f ρI σ a ha (hρInv a ha)
        (hσInv a ha) x y.val
  have horder : (2 : ℕ) ≤ 2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) := by
    omega
  have hb₂ : ContDiff ℝ (2 : ℕ) b := hb.of_le (by exact_mod_cast horder)
  have hderiv₂ (j : ℕ) (hj : j ≤ (2 : ℕ)) := hderiv j (hj.trans horder)
  have hbound (r : ℝ) (hr : 0 ≤ r) : ‖b r‖ ≤ Cb := by
    simpa only [iteratedDeriv_zero] using hderiv₂ 0 (by decide) r hr
  obtain ⟨κ, hκ, hrep⟩ := exists_continuous_sLocalTraceOrbitSeries_of_localBounds
    f σ (fun ξ z ↦ hσInv ξ.val (sLocalTrace_unit_norm ξ) z)
    (sLocalTraceCutoffKernel_continuous_radial f _ continuous_const b hb.continuous hbound)
    (fun X Y hX hY ↦ sLocalTraceCutoffKernel_raw_radial_compact_majorant
      f b hb₂ hε hplateau hderiv₂ hX hY)
  obtain ⟨hZ, hK, hzero, hrepK⟩ :=
    sLocalTrace_maskedOrbitSeries_measurable_and_output_support f σ κ hκ hrep hρ
  let κρ (x y : J) := (ρ x : ℂ) * κ x y
  have hρb (q : J) : ‖(ρ q : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hρ.abs_le_one q
  obtain ⟨C, hC, htails⟩ := sLocalTrace_rawOrbit_radial_bound_on_compact
    f (fun q ↦ (ρ q : ℂ)) hρb b (fun ξ ↦ hRawCov ξ.val (sLocalTrace_unit_norm ξ))
    (show IsCompact Z from hZ) hb hε hplateau hderiv
    (sLocalTrace_height_rpow_summable (F := F) (S := S) (q := 1 / 4) (by norm_num))
  have hAll (x y : I) :
      let t : ℝ := (sIdeleNorm F S y).val
      let a (ξ : H) := ‖K x (ξ.val * y).val‖
      Summable a ∧
      (t ≤ 1 → (∑' ξ, a ξ) ≤ C * t ^ (-(1 / 4 : ℝ))) ∧
      (1 ≤ t → (∑' ξ, a ξ) ≤ C * t⁻¹) := by
    intro t a
    by_cases hx : π x ∈ Z
    · exact htails x hx y
    have hz : ρ (π x) = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h ↦ hx (hρ.support_subset h))
    have hzC : ρI x = 0 := by
      change (ρ (π x) : ℂ) = 0
      rw [hz, Complex.ofReal_zero]
    have ha : a = fun _ ↦ 0 := by
      funext ξ
      change ‖sLocalTraceCutoffKernel f ρI σ x (ξ.val * y).val‖ = 0
      simp only [sLocalTraceCutoffKernel, hzC, zero_mul, norm_zero]
    have ht : 0 ≤ t := NNReal.coe_nonneg _
    simp only [ha, summable_zero, tsum_zero, true_and]
    exact ⟨fun _ ↦ mul_nonneg hC (Real.rpow_nonneg ht _),
      fun _ ↦ mul_nonneg hC (inv_nonneg.mpr ht)⟩
  have hQuotCov (q y : J) (h : (sIdeleQuotientNorm F S).ker) :
      κρ (q * h.val) (y * h.val) = κρ q y :=
    sLocalTraceOrbitSeries_covariant_of_normOne (fun x y : I ↦ K x y.val)
      κρ hrepK hRawCov q y h
  have hQuotTails (q y : J) :
      (N y ≤ 1 → ‖κρ q y‖ ≤ C * N y ^ (-(1 / 4 : ℝ))) ∧
      (1 ≤ N y → ‖κρ q y‖ ≤ C * (N y)⁻¹) := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hNz : N (π z) = ((sIdeleNorm F S z).val : ℝ) :=
      congrArg (fun t : ℝ≥0ˣ ↦ (t.val : ℝ)) (sIdeleQuotientNorm_mk F S z)
    have hNorm : ‖κρ (π x) (π z)‖ ≤ ∑' ξ : H, ‖K x (ξ.val * z).val‖ := by
      rw [show κρ (π x) (π z) = ∑' ξ : H, K x (ξ.val * z).val from hrepK x z]
      exact norm_tsum_le_tsum_norm (hAll x z).1
    change (N (π z) ≤ 1 → _) ∧ (1 ≤ N (π z) → _)
    rw [hNz]
    exact ⟨fun ht ↦ hNorm.trans ((hAll x z).2.1 ht),
      fun ht ↦ hNorm.trans ((hAll x z).2.2 ht)⟩
  refine ⟨hZ, κρ, C, hC, hK, hzero, hrepK, hRawCov, hQuotCov, hAll, ?_⟩
  exact sLocalTrace_halfDensityKernel_memLp_of_radial_bounds (show IsCompact Z from hZ) hK
    (fun p hp ↦ hzero p.1 hp p.2) hs
    (fun p _ ht ↦ (hQuotTails p.1 p.2).1 ht) (fun p _ ht ↦ (hQuotTails p.1 p.2).2 ht)

end RiemannMasullo
