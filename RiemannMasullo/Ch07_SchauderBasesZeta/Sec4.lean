module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
public import RiemannMasullo.Ch06_LocalGlobal.Sec3
public import RiemannMasullo.AppC_LCTVS.Sec3a

import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Holomorphic
import all RiemannMasullo.AppD_SchwartzBruhat.Sec2b
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3b

import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import all RiemannMasullo.Ch06_LocalGlobal.Sec3
import all RiemannMasullo.AppA_AlgebraicNT.Sec3
import all RiemannMasullo.Ch03_IdelicZeta.Sec3b
import all RiemannMasullo.Ch05_ThetaZSpaces.Sec3b

/-! # §7.4 Nuclearity

The spectral quotient is in Schwartz–Bergman coordinates. The orbital quotients
use the quotient topology of the zero-moment homogeneous theta space.
-/

@[expose] public noncomputable section

open Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing TensorProduct

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 150000
set_option Elab.async false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "ω(" χ ")" => (χ : U).comp
  (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : (ideleClassNorm F).ker →ₜ* C𝔽)
local notation "P" => adelePolarSubspace F
local notation "B" => SchwartzBergman (univ : Set ℝ)
local notation "Entire" => entireContinuousMapSubalgebra

local instance instIdeleClassT2Sec4 : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1

local instance instIdeleClassLocallyCompactSec4 : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

local instance instIdeleClassMeasurableSec4 (F : Type*) [Field F] [NumberField F] :
    MeasurableSpace (IdeleClassGroup (𝓞 F) F) := borel _
local instance instNuclearitySecondCountable : SecondCountableTopology C𝔽 :=
  letI := idele_secondCountable F
  inferInstanceAs (SecondCountableTopology
    (IdeleGroup (𝓞 F) F ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))

local notation "𝒟" => BruhatCompactSupport (IdeleClassGroup (𝓞 F) F)
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "Π(" χ ")" => LinearMap.ker ((homogeneousAdelicThetaLinearMap F (ω(χ))).domRestrict P)
local notation "Θ₀(" χ ")" => ↥P ⧸ Π(χ)
local notation "mkΘ(" χ ", " f ")" => (Submodule.Quotient.mk f : Θ₀(χ))
local notation "Z(" χ ", " τ ", " hτ ")" => (exists_globalPolarThetaMellin χ τ hτ).choose
local notation "testIntegrand(" χ ", " φ ", " s ")" =>
  (fun g : C𝔽 ↦ (φ : 𝒟).val g * (ideleClassNormTwist χ s) g)

/-- Paper: Equation (7.4.1.1), p. 366.
The class-group Mellin transform of a Bruhat test uses the norm twist of the given character
and the idèle-class Tamagawa measure. -/
def nuclearityTestMellin (χ : U) (φ : 𝒟) (s : ℂ) : ℂ :=
  ∫ g, testIntegrand(χ, φ, s) g ∂μ𝔽

/-- Paper: Equation (7.4.1.1), p. 366.
The test integral converges absolutely throughout the norm chart.
At the trivial quasi-character it gives the integral of the test. -/
theorem nuclearityTestMellin_integrable (χ : U) (φ : 𝒟) :
    (∀ s : ℂ, Integrable (testIntegrand(χ, φ, s)) μ𝔽) ∧
      nuclearityTestMellin 1 φ 0 = ∫ g, φ.val g ∂μ𝔽 := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let : (ideleClassTamagawaMeasure F).IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil F).1
  have hc : Continuous φ.val :=
    continuous_schwartzBruhat (⟨φ.val, bruhatCompactSupport_mem_schwartz φ.property⟩ : SchwartzBruhat C𝔽)
  constructor
  · intro s
    exact (hc.mul (ideleClassNormTwist χ s).continuous).integrable_of_hasCompactSupport
      (show HasCompactSupport φ.val from φ.property.2).mul_right
  · apply integral_congr_ae
    filter_upwards with g
    change φ.val g * (1 * _ ^ (0 : ℂ)) = φ.val g
    simp

/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
An operator of order zero admits a nuclear presentation with rapidly decreasing
coefficients. The presentation includes equicontinuity and a common Banach disc. -/
def IsStronglyNuclearOperator {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
    (A : E →L[ℂ] E) : Prop :=
  ∃ r : NuclearPresentation A, ∀ k : ℕ, ∃ C : ℝ, ∀ n : ℕ,
    ‖r.coeff n‖ * ((n : ℝ) + 1) ^ k ≤ C

/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
Every continuous rank-one operator is of order zero. -/
theorem isStronglyNuclearOperator_rankOne {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [T2Space E]
    (ℓ : StrongDual ℂ E) (x : E) : IsStronglyNuclearOperator (ℓ.smulRight x) := by
  obtain ⟨r, hr, _, _, htail⟩ := nuclearPresentation_smulRight ℓ x 1 one_ne_zero
  refine ⟨r, fun k ↦ ⟨1, ?_⟩⟩
  intro n
  cases n with
  | zero => simp [hr]
  | succ n => simp [htail n]

private theorem specDenom_mem_div (g : Entire) (φ : B) :
    φ ∈ schwartzBergmanDivisible g ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = g.val s * u s := by
  rw [schwartzBergmanDivisible, Submodule.mem_comap, Submodule.restrictScalars_mem,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨a.val, a.property, fun s ↦ ?_⟩
    have h := congrArg (fun e : Entire ↦ e.val s) ha
    change a.val s * g.val s = (schwartzBergmanEntireInclusion φ).val s at h
    rw [schwartzBergmanEntireInclusion_apply] at h
    rw [← h, mul_comm]
  · rintro ⟨u, hu, h⟩
    refine ⟨⟨⟨u, hu.continuous⟩, hu⟩, ?_⟩
    apply Subtype.ext
    ext s
    change u s * g.val s = (schwartzBergmanEntireInclusion φ).val s
    rw [schwartzBergmanEntireInclusion_apply, h, mul_comm]

private theorem specDenom_B_ext (φ ψ : B) (h : ∀ s, φ.val s = ψ.val s) : φ = ψ :=
  Subtype.ext (funext h)

private theorem specDenom_shift_mem (φ : B) (c : ℂ) :
    (fun w ↦ φ.val (w - c)) ∈ schwartzBergmanSubmodule (univ : Set ℝ) := by
  obtain ⟨-, hd, hb⟩ := φ.property
  refine ⟨fun z hz ↦ absurd (mem_univ _) hz, ?_, ?_⟩
  · have hd' : Differentiable ℂ φ.val := fun z ↦
      (hd z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    exact (hd'.comp (differentiable_id.sub_const c)).differentiableOn
  · intro a b hab _ N
    obtain ⟨A, hA⟩ := hb (a - c.re) (b - c.re) (by linarith) (subset_univ _) N
    obtain ⟨A₀, hA₀⟩ := hb (a - c.re) (b - c.re) (by linarith) (subset_univ _) 0
    refine ⟨2 ^ N * (A + ‖c‖ ^ N * A₀), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    have hz : w - c ∈ Complex.re ⁻¹' Icc (a - c.re) (b - c.re) := by
      simp only [mem_preimage, mem_Icc, Complex.sub_re] at hw ⊢
      constructor <;> linarith [hw.1, hw.2]
    have h1 := hA ⟨w - c, hz, rfl⟩
    have h0 := hA₀ ⟨w - c, hz, rfl⟩
    simp only [pow_zero, one_mul] at h0
    change ‖(w - c) ^ N * φ.val (w - c)‖ ≤ A at h1
    change ‖w ^ N * φ.val (w - c)‖ ≤ _
    set z := w - c
    have hwz : w = z + c := by simp [z]
    rw [hwz, norm_mul, norm_pow]
    rw [norm_mul, norm_pow] at h1
    have hn : ‖z + c‖ ^ N ≤ 2 ^ N * (‖z‖ ^ N + ‖c‖ ^ N) := by
      calc ‖z + c‖ ^ N ≤ (‖z‖ + ‖c‖) ^ N := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) N
        _ ≤ (2 * max ‖z‖ ‖c‖) ^ N := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [le_max_left ‖z‖ ‖c‖, le_max_right ‖z‖ ‖c‖]
        _ = 2 ^ N * max ‖z‖ ‖c‖ ^ N := mul_pow _ _ _
        _ ≤ 2 ^ N * (‖z‖ ^ N + ‖c‖ ^ N) := by
          gcongr
          rcases le_total ‖z‖ ‖c‖ with h | h
          · rw [max_eq_right h]; linarith [pow_nonneg (norm_nonneg z) N]
          · rw [max_eq_left h]; linarith [pow_nonneg (norm_nonneg c) N]
    calc ‖z + c‖ ^ N * ‖φ.val z‖ ≤ 2 ^ N * (‖z‖ ^ N + ‖c‖ ^ N) * ‖φ.val z‖ :=
          mul_le_mul_of_nonneg_right hn (norm_nonneg _)
      _ = 2 ^ N * (‖z‖ ^ N * ‖φ.val z‖ + ‖c‖ ^ N * ‖φ.val z‖) := by ring
      _ ≤ 2 ^ N * (A + ‖c‖ ^ N * A₀) := by
          gcongr

private theorem specDenom_gen_bwd {X Y Q Bm : Type*} (ι : X → Y) (q : Y → Q) (c : X → Q)
    (hc : Surjective c) (hcq : ∀ x, c x = q (ι x)) (ZB : Q → Bm) (S : Set Bm)
    (hr : Set.range ZB = S) (φ : Bm) (hφ : φ ∈ S) : ∃ x : X, ZB (q (ι x)) = φ := by
  rw [← hr] at hφ
  obtain ⟨y, rfl⟩ := hφ
  obtain ⟨x, rfl⟩ := hc y
  exact ⟨x, by rw [hcq]⟩

private theorem specDenom_gen_mem {M Q Bm : Type*} (mk : M → Q) (hmk : Surjective mk) (Zf : Q → Bm)
    (ev : Bm → ℂ → ℂ) (hev : Injective ev) (zf : M → ℂ → ℂ)
    (hspec : ∀ f s, ev (Zf (mk f)) s = zf f s) (G' : ℂ → ℂ)
    (hv : ∃ G : ℂ → ℂ, G' = G ∧
      (∀ f : M, ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, zf f s = G s * u s) ∧
      (∀ φ : Bm, (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev φ s = G s * u s) →
        ∃ f : M, ∀ s, ev φ s = zf f s)) (φ : Bm) :
    (∃ x, Zf x = φ) ↔ ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev φ s = G' s * u s := by
  obtain ⟨G, rfl, hfwd, hbwd⟩ := hv
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := hmk x
    obtain ⟨u, hu, h⟩ := hfwd f
    exact ⟨u, hu, fun s ↦ (hspec f s).trans (h s)⟩
  · intro h
    obtain ⟨f, hf⟩ := hbwd φ h
    exact ⟨mk f, hev (funext fun s ↦ (hspec f s).trans (hf s).symm)⟩

private theorem specDenom_gen_range_eq {Q Bm : Type*} {_ : AddCommGroup Q} {_ : Module ℂ Q}
    {_ : TopologicalSpace Q} {_ : AddCommGroup Bm} {_ : Module ℂ Bm} {_ : TopologicalSpace Bm}
    (Zc : Q →L[ℂ] Bm) (D : Submodule ℂ Bm) (h : ∀ φ, (∃ x, Zc x = φ) ↔ φ ∈ D) :
    Zc.toLinearMap.range = D := by
  ext φ
  rw [LinearMap.mem_range]
  exact h φ

private theorem specDenom_gen_shift {Q Bm : Type*} (Zf : Q → Bm) (ev : Bm → ℂ → ℂ) (L : ℂ → ℂ)
    (c : ℂ)
    (hrange : ∀ φ : Bm, (∃ x, Zf x = φ) ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev φ s = L s * u s)
    (hshift : ∀ φ : Bm, ∃ ψ : Bm, ∀ w, ev ψ w = ev φ (w - c)) (f : Bm) :
    (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, ev f s = L (s + c) * u s) ↔
      ∃ x : Q, ∀ s, ev f s = ev (Zf x) (s + c) := by
  constructor
  · rintro ⟨u, hu, h⟩
    obtain ⟨ψ, hψ⟩ := hshift f
    obtain ⟨x, hx⟩ := (hrange ψ).mpr ⟨fun w ↦ u (w - c), hu.comp (differentiable_id.sub_const c),
      fun w ↦ by rw [hψ, h, sub_add_cancel]⟩
    exact ⟨x, fun s ↦ by rw [hx, hψ, add_sub_cancel_right]⟩
  · rintro ⟨x, hx⟩
    obtain ⟨u, hu, h⟩ := (hrange (Zf x)).mp ⟨x, rfl⟩
    exact ⟨fun s ↦ u (s + c), hu.comp (differentiable_id.add_const c), fun s ↦ by rw [hx, h]⟩

section Spectral

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

local notation "Λ(" χ ", " τ ", " hτ ")" => regularizedCompletedHeckeL χ τ hτ
  (continuedCompletedHeckeL χ) (continuedCompletedHeckeL_spec χ).1 (continuedCompletedHeckeL_spec χ).2

/-- Paper: Equation (7.4.0.1), p. 366.
In Mellin coordinates the norm-power twist shifts the regularized completed generator
by translation of the argument by a. The shifted generator is entire. -/
theorem spectralNuclearityGenerator_differentiable (a : ℝ) :
    Differentiable ℂ (fun s ↦ (Λ(χ, τ, hτ)).val (s + (a : ℂ))) := by
  exact (Λ(χ, τ, hτ)).property.comp (differentiable_id.add_const (a : ℂ))

/-- Paper: Equation (7.4.0.1), p. 366.
The denominator is the shifted theta image in the Schwartz–Bergman model of the
exponentially decaying isotype. -/
def spectralNuclearityDenominator (a : ℝ) : Submodule ℂ B :=
  let h := spectralNuclearityGenerator_differentiable χ τ hτ a
  schwartzBergmanDivisible ⟨⟨_, h.continuous⟩, h⟩

/-- Paper: Equation (7.4.0.1), p. 366.
This is the spectral quotient with its quotient topology, in Mellin coordinates. -/
abbrev SpectralNuclearityQuotient (a : ℝ) := B ⧸ spectralNuclearityDenominator χ τ hτ a

open Classical in
private theorem specDenom_Lambda_val :
    ⇑(Λ(χ, τ, hτ)).val = toMeromorphicNFOn (fun s ↦
      (s + ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ) *
        Complex.I) ^ (if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0) *
      (1 - s - ((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℂ) *
        Complex.I) ^ (if χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then 1 else 0) *
      continuedCompletedHeckeL χ s) univ := rfl


private theorem specDenom_hδ (hω : ¬ ω(χ) = 1) :
    ¬ χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
  intro h
  apply hω
  ext g
  exact congrArg Subtype.val (DFunLike.congr_fun h g)

private theorem specDenom_hδ' (hω : ω(χ) = 1) :
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
  ext g
  exact congrArg Subtype.val (DFunLike.congr_fun hω g)

open Classical in
private theorem specDenom_L0 (hδ : ¬ χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1) :
    ⇑(Λ(χ, τ, hτ)).val = continuedCompletedHeckeL χ := by
  rw [specDenom_Lambda_val, ite_eq_right_of_eq_false _ _ (eq_false hδ)]
  simp only [pow_zero, one_mul]
  exact toMeromorphicNFOn_eq_self.mpr (continuedCompletedHeckeL_spec χ).1

open Classical in
private theorem specDenom_L1 (t : ℝ) (hω : ω(χ) = 1)
    (ht : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U) (((t : ℝ) : ℂ) * Complex.I)) :
    ⇑(Λ(χ, τ, hτ)).val = toMeromorphicNFOn (fun s ↦ ((s + (t : ℂ) * Complex.I) *
      (1 - s - (t : ℂ) * Complex.I)) * continuedCompletedHeckeL χ s) univ := by
  have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
  have ht' : ∀ u : ℝ≥0ˣ, (χ (QuotientGroup.mk (τ u)) : ℂ) =
      (((u : ℝ≥0) : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) := by
    intro u
    have he := DFunLike.congr_fun ht (QuotientGroup.mk (τ u))
    change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
      1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) at he
    rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
    exact he
  have hx : hphase.exists.choose = t := hphase.unique hphase.exists.choose_spec ht'
  rw [specDenom_Lambda_val, hx, ite_eq_left_of_eq_true _ _ (eq_true (specDenom_hδ' χ hω))]
  simp only [pow_one]

open Classical in
private theorem specDenom_values :
    ∃ G : ℂ → ℂ, ⇑(Λ(χ, τ, hτ)).val = G ∧
      (∀ f : P, ∃ u : ℂ → ℂ, Differentiable ℂ u ∧
        ∀ s, globalIdelicZFunction f.val (ideleClassNormTwist χ s) = G s * u s) ∧
      (∀ φ : B, (∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = G s * u s) →
        ∃ f : P, ∀ s, φ.val s = globalIdelicZFunction f.val (ideleClassNormTwist χ s)) := by
  by_cases hω : ω(χ) = 1
  · have h1 := (globalConverse_existsUnique_normTwist χ hω).exists
    obtain ⟨t, ht⟩ := h1
    have h2 := globalConverse_normTwist χ t ht
    obtain ⟨ZB, h3⟩ := h2
    have hZB := h3.2.2.1
    have hrange := h3.2.2.2.1
    refine ⟨_, specDenom_L1 χ τ hτ t hω ht, ?_, ?_⟩
    · intro f
      have hm : ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, (ZB f).val s =
          toMeromorphicNFOn (fun s ↦ ((s + (t : ℂ) * Complex.I) *
            (1 - s - (t : ℂ) * Complex.I)) * continuedCompletedHeckeL χ s) univ s * u s :=
        (Set.ext_iff.mp hrange (ZB f)).mp ⟨f, rfl⟩
      obtain ⟨u, hu, h⟩ := hm
      exact ⟨u, hu, fun s ↦ (hZB f s).symm.trans (h s)⟩
    · intro φ hφ
      have hm : φ ∈ Set.range ZB := (Set.ext_iff.mp hrange φ).mpr hφ
      obtain ⟨f, hf⟩ := hm
      refine ⟨f, fun s ↦ ?_⟩
      rw [← hf]
      exact hZB f s
  · have h2 := globalConverse_nontrivial χ hω
    obtain ⟨ZB, h3⟩ := h2
    have hZB := h3.2.1
    have hrange := h3.2.2
    refine ⟨_, specDenom_L0 χ τ hτ (specDenom_hδ χ hω), ?_, ?_⟩
    · intro f
      have hm : ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s,
          (ZB ((LinearMap.ker (homogeneousAdelicThetaLinearMap F (ω(χ)))).mkQ f.val)).val s =
          continuedCompletedHeckeL χ s * u s :=
        (Set.ext_iff.mp hrange _).mp ⟨_, rfl⟩
      obtain ⟨u, hu, h⟩ := hm
      exact ⟨u, hu, fun s ↦ (hZB f.val s).symm.trans (h s)⟩
    · intro φ hφ
      have hs0 := globalConverse_nontrivial_exact (F := F) _ hω
      have hs := hs0.surjective
      have hx := specDenom_gen_bwd (fun f : P ↦ f.val) _ _ hs (fun _ ↦ rfl) ZB _ hrange φ hφ
      obtain ⟨f, hf⟩ := hx
      refine ⟨f, fun s ↦ ?_⟩
      rw [← hf]
      exact hZB f.val s


private theorem specDenom_range_mem (φ : B) :
    (∃ x : Θ₀(χ), (Z(χ, τ, hτ)) x = φ) ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, φ.val s = (Λ(χ, τ, hτ)).val s * u s :=
  specDenom_gen_mem (fun f : P ↦ (Submodule.Quotient.mk f : Θ₀(χ)))
    (Submodule.Quotient.mk_surjective _) (fun x ↦ (Z(χ, τ, hτ)) x) (fun φ : B ↦ φ.val)
    (fun φ ψ h ↦ specDenom_B_ext φ ψ fun s ↦ congrFun h s)
    (fun (f : P) s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s))
    (fun f s ↦ ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2)
    (⇑(Λ(χ, τ, hτ)).val) (specDenom_values χ τ hτ) φ

private theorem specDenom_mem_D (a : ℝ) (f : B) :
    f ∈ spectralNuclearityDenominator χ τ hτ a ↔
      ∃ u : ℂ → ℂ, Differentiable ℂ u ∧ ∀ s, f.val s = (Λ(χ, τ, hτ)).val (s + (a : ℂ)) * u s :=
  specDenom_mem_div _ f

/-- Paper: Equation (7.4.0.1), p. 366.
The unshifted denominator is precisely the image of the pole-free theta Mellin map. -/
theorem spectralNuclearityDenominator_zero :
    spectralNuclearityDenominator χ τ hτ 0 = (Z(χ, τ, hτ)).toLinearMap.range :=
  (specDenom_gen_range_eq (Z(χ, τ, hτ)) (spectralNuclearityDenominator χ τ hτ 0) fun φ ↦
    (specDenom_range_mem χ τ hτ φ).trans ((specDenom_mem_D χ τ hτ 0 φ).trans
      (exists_congr fun u ↦ and_congr_right fun _ ↦ forall_congr' fun s ↦ by
        rw [Complex.ofReal_zero, add_zero])).symm).symm

/-- Paper: Equation (7.4.0.1), p. 366.
The denominator consists precisely of the Mellin transforms of norm-twisted theta classes. -/
theorem mem_spectralNuclearityDenominator_iff (a : ℝ) (f : B) :
    f ∈ spectralNuclearityDenominator χ τ hτ a ↔
      ∃ x : Θ₀(χ), ∀ s : ℂ, f.val s = ((Z(χ, τ, hτ)) x).val (s + (a : ℂ)) :=
  (specDenom_mem_D χ τ hτ a f).trans
    (specDenom_gen_shift (fun x : Θ₀(χ) ↦ (Z(χ, τ, hτ)) x) (fun φ : B ↦ φ.val) (⇑(Λ(χ, τ, hτ)).val)
      (a : ℂ) (specDenom_range_mem χ τ hτ)
      (fun φ ↦ ⟨⟨_, specDenom_shift_mem φ (a : ℂ)⟩, fun _ ↦ rfl⟩) f)

/-- Paper: Equation (7.4.0.1), p. 366.
The section Mellin transform identifies the decay isotype with the full
Schwartz–Bergman space and takes the norm-twisted theta image to the denominator.
The section integral uses the quotient Haar measure dt/t of §3.2. -/
theorem spectralNuclearityDenominator_isotypeModel (a : ℝ) :
    let m : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
    let E := modulatedDecayIsotype m (Set.univ : Set ℝ) (Set.mem_univ 0) (ω(χ))
    ∃ M : ↥E ≃L[ℂ] B,
      (∀ (u : E) s, (M u).val s = ∫ t : ℝ≥0ˣ,
        u.val.val (QuotientGroup.mk (τ t)) *
          ideleClassNormTwist χ s (QuotientGroup.mk (τ t)) ∂positiveRealHaar) ∧
      ∀ u : E, M u ∈ spectralNuclearityDenominator χ τ hτ a ↔
        ∃ f : P, ∀ g : C𝔽, u.val.val g =
          ((((ideleClassNorm F g).val : ℝ) ^ a : ℝ) : ℂ) *
            homogeneousAdelicTheta (ω(χ)) f.val g := by sorry

/-- Paper: Theorem 7.4.1.1(1), p. 366.
The twisted theta image is closed. Compactly supported Bruhat tests act by continuous
Mellin multiplication, which preserves that image. -/
theorem spectralNuclearityDenominator_closed_invariant (a : ℝ) (φ : 𝒟) :
    let D := spectralNuclearityDenominator χ τ hτ a
    IsClosed (D : Set B) ∧
      ∃ A : B →L[ℂ] B,
        (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
        Set.MapsTo A (D : Set B) D := by sorry

local notation "zeros(" χ ", " τ ", " hτ ")" =>
  {z : ℂ // 0 < analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) z}
local notation "multiplicity(" χ ", " τ ", " hτ ", " z ")" =>
  (analyticOrderAt ((Λ(χ, τ, hτ)).val : ℂ → ℂ) (z : ℂ)).toNat
local notation "jets(" χ ", " τ ", " hτ ")" =>
  Σ z : zeros(χ, τ, hτ), Fin (multiplicity(χ, τ, hτ, z))
local notation "Q(" a ")" => SpectralNuclearityQuotient χ τ hτ a
local notation "D(" a ")" => spectralNuclearityDenominator χ τ hτ a

open Classical in
/-- Paper: Theorem 7.4.1.1(2), p. 366, using Theorem 7.1.4.2(3).
The jet functionals and their full biorthogonal families transport to the shifted
quotient. A zero z of the unshifted generator has its jets at z − a. -/
theorem exists_spectralNuclearityBiorthogonal (a : ℝ) :
    ∃ (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a))) (b : jets(χ, τ, hτ) → Q(a)),
      (∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) ∧
      ∀ i j, d i (b j) = if i = j then 1 else 0 := by sorry

-- TODO(paper-gap): The proof on p. 367 gives no uniform boundedness estimate for
-- the rescaled biorthogonal vectors. Discreteness does not control zero counts,
-- enumeration order, or separation. It also does not imply N(z)! = O(|Im z|).

open Classical in
/-- Paper: Theorem 7.4.1.1(2), pp. 366–367.
Compactly supported tests act on the quotient determined by the first N derivatives
in each block. Every nuclear presentation of the order-zero action has the stated trace.
Deviation: The printed span of the first N primal vectors can fail to be invariant.
Quotient by the common kernel of the retained derivative functionals. The multiplier
is evaluated at z − a for each unshifted zero z. -/
theorem spectralNuclearity_trace (a : ℝ) (N : ℕ) (_hN : 0 < N) (φ : 𝒟)
    (d : jets(χ, τ, hτ) → StrongDual ℂ (Q(a)))
    (_hd : ∀ i f, d i ((D(a)).mkQ f) = iteratedDeriv i.2.val f.val (i.1.val - (a : ℂ))) :
    let K := ⨅ i : {i : jets(χ, τ, hτ) // i.2.val < N}, (d i.val).toLinearMap.ker
    let E := Q(a) ⧸ K
    letI instSpectralUniformSec4 : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
    let term := fun z : zeros(χ, τ, hτ) ↦
      ((min N (multiplicity(χ, τ, hτ, z)) : ℕ) : ℂ) * nuclearityTestMellin χ φ (z.val - (a : ℂ))
    ∃ (A : B →L[ℂ] B) (T : E →L[ℂ] E),
      (∀ f s, (A f).val s = nuclearityTestMellin χ φ s * f.val s) ∧
      (∃ Aq : Q(a) →L[ℂ] Q(a),
        (∀ f, Aq ((D(a)).mkQ f) = (D(a)).mkQ (A f)) ∧
        ∀ x : Q(a), T (K.mkQ x) = K.mkQ (Aq x)) ∧
      IsStronglyNuclearOperator T ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by sorry

end Spectral

section Orbital

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- Paper: Theorem 7.4.2.1(1)–(2), p. 367, and Theorem 7.4.3.2, pp. 372–373.
In global Mellin coordinates the regularized theta action is multiplication by
the transform of the test. The induced map on theta functions is Haar convolution. -/
theorem exists_polarThetaNuclearityAction (φ : 𝒟) :
    ∃ A : Θ₀(χ) →L[ℂ] Θ₀(χ),
      (∀ f s, ((Z(χ, τ, hτ)) (A f)).val s =
        nuclearityTestMellin χ φ s * ((Z(χ, τ, hτ)) f).val s) ∧
      ∀ f g : P, A mkΘ(χ, f) = mkΘ(χ, g) ↔
        (homogeneousAdelicTheta (ω(χ)) g.val : C𝔽 → ℂ) =
          lcaConvolution μ𝔽 φ.val (homogeneousAdelicTheta (ω(χ)) f.val) := by sorry

local notation "Aθ(" φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Paper: Equation (7.4.0.2), p. 366.
The finite places of a number field lying above one rational prime form a finite set. -/
theorem finite_nuclearityPlacesAbove (p : HeightOneSpectrum (𝓞 ℚ)) :
    {v : V | v.under (𝓞 ℚ) = p}.Finite := by
  apply Set.Finite.of_finite_image (f := HeightOneSpectrum.asIdeal)
    (hi := HeightOneSpectrum.asIdeal_injective.injOn)
  apply (IsDedekindDomain.primesOver_finite p.asIdeal (𝓞 F)).subset
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨w.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal (show w.under (𝓞 ℚ) = p from hw).symm⟩⟩

local notation "Sₚ(" p ")" => (finite_nuclearityPlacesAbove (F := F) p).toFinset

/-- Paper: Equation (7.4.0.2), p. 366.
Principal value preserves the common kernel of the two global polar evaluations. -/
theorem nuclearityPrincipalValue_mem_polar (p : HeightOneSpectrum (𝓞 ℚ)) (f : P) :
    adelePrincipalValue F (Sₚ(p)) f.val ∈ P := by
  classical
  have hn : (Sₚ(p)).Nonempty := by
    have := p.isMaximal
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 F) p.asIdeal
    let v : V := ⟨q, hq.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot p.ne_bot q⟩
    exact ⟨v, (finite_nuclearityPlacesAbove p).mem_toFinset.mpr (HeightOneSpectrum.ext hqp.over.symm)⟩
  let E := SchwartzBruhat (Multiplicative 𝔸[F])
  let pv : E →L[ℂ] E :=
    ⟨adelePrincipalValue F (Sₚ(p)), (adelePrincipalValue_isClosedEmbedding (Sₚ(p))).continuous⟩
  let vals : E →L[ℂ] ℂ × ℂ := ⟨adelePolarValues, adelePolarValues_continuous⟩
  obtain ⟨y, hy⟩ := adelePolarValues_surjective (F := F) ((1, 1) : ℂ × ℂ)
  change vals y = (1, 1) at hy
  have hx : vals f.val = 0 := f.property
  -- Pullback by principal value preserves the eigenspace of each polar functional.
  have coord (L : ℂ × ℂ →L[ℂ] ℂ) (c : QuasiCharacter C𝔽)
      (hL : L.comp vals ∈ adelicEigendistributions c) (h1 : L (1, 1) = 1) :
      L (vals (pv f.val)) = 0 := by
    let l := L.comp vals
    have hk : l.comp pv ∈ adelicEigendistributions c := by
      intro u t
      have he := congrArg (fun q : GlobalAdelicThetaSpace F ↦ L (globalThetaPolarValues q))
        (globalThetaPrincipalValue_equivariant hn u t)
      exact he.trans (hL u (pv t))
    have hl : l ≠ 0 := by
      intro hz
      have hy' : l y = 1 := (congrArg L hy).trans h1
      rw [hz] at hy'
      exact zero_ne_one hy'
    have hdim := Module.rank_eq_one_iff_finrank_eq_one.mp (adelicEigendistributions_rank c)
    rw [eq_span_singleton_of_mem_of_finrank_eq_one hdim hL hl, Submodule.mem_span_singleton] at hk
    obtain ⟨a, ha⟩ := hk
    have he := congrArg (fun k : E →L[ℂ] ℂ ↦ k f.val) ha.symm
    change L (vals (pv f.val)) = a * L (vals f.val) at he
    simpa only [hx, map_zero, mul_zero] using he
  apply (mem_adelePolarSubspace _).2
  constructor
  · apply coord (ContinuousLinearMap.fst ℂ ℂ ℂ) 1 _ rfl
    intro u t
    change t (Multiplicative.ofAdd ((↑u⁻¹ : 𝔸[F]) * 0)) = 1 * t (Multiplicative.ofAdd 0)
    rw [mul_zero, one_mul]
  · apply coord (ContinuousLinearMap.snd ℂ ℂ ℂ) (ideleClassNormTwist (1 : U) 1) _ rfl
    intro u t
    have h := globalThetaPolarValues_snd_translate (QuotientGroup.mk u) (Submodule.Quotient.mk t)
    rw [(existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 u t] at h
    change (adelePolarValues (schwartzBruhatUnitTranslate u t)).2 =
      ((1 : ℂ) * (((ideleNorm F u).val : ℝ) : ℂ) ^ (1 : ℂ)) * (adelePolarValues t).2
    rw [Complex.cpow_one, one_mul]
    exact h

/-- Paper: Equation (7.4.0.2), p. 366.
The finite-place denominator is the theta image of principal values of zero-moment
tests, with the principal value taken at all places above the rational prime. -/
def finiteNuclearityDenominator (p : HeightOneSpectrum (𝓞 ℚ)) : Submodule ℂ (Θ₀(χ)) :=
  Submodule.span ℂ (Set.range (fun f : P ↦
    (Submodule.Quotient.mk ⟨adelePrincipalValue F (Sₚ(p)) f.val,
      nuclearityPrincipalValue_mem_polar (F := F) p f⟩ : Θ₀(χ))))

/-- Paper: Equation (7.4.0.2), p. 366.
The finite orbital quotient is taken by the principal-value image.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def FiniteNuclearityQuotient (p : HeightOneSpectrum (𝓞 ℚ)) :=
  Θ₀(χ) ⧸ finiteNuclearityDenominator χ p

namespace FiniteNuclearityQuotient

instance instAddCommGroup (p : HeightOneSpectrum (𝓞 ℚ)) :
    AddCommGroup (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (AddCommGroup (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instModule (p : HeightOneSpectrum (𝓞 ℚ)) : Module ℂ (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (Module ℂ (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instTopologicalSpace (p : HeightOneSpectrum (𝓞 ℚ)) :
    TopologicalSpace (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (TopologicalSpace (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instIsTopologicalAddGroup (p : HeightOneSpectrum (𝓞 ℚ)) :
    IsTopologicalAddGroup (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (IsTopologicalAddGroup (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

instance instContinuousSMul (p : HeightOneSpectrum (𝓞 ℚ)) :
    ContinuousSMul ℂ (FiniteNuclearityQuotient χ p) :=
  inferInstanceAs (ContinuousSMul ℂ (Θ₀(χ) ⧸ finiteNuclearityDenominator χ p))

end FiniteNuclearityQuotient

private theorem mkQ_span_range_eq_zero {E M : Type*} [AddCommGroup E] [AddCommGroup M]
    [Module ℂ E] [Module ℂ M] (L : E →ₗ[ℂ] M) (x : M) :
    (Submodule.span ℂ (Set.range L)).mkQ x = 0 ↔ ∃ y, x = L y := by
  have hle : Submodule.span ℂ (Set.range L) ≤ LinearMap.range L :=
    Submodule.span_le.mpr Set.Subset.rfl
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, hy⟩
    exact Submodule.subset_span ⟨y, hy.symm⟩

private theorem mkQ_principal_range_eq_zero {E : Type*} [AddCommGroup E] [Module ℂ E]
    (S : Submodule ℂ E) (Q : Submodule ℂ S) (A : E →ₗ[ℂ] E)
    (h : ∀ g : S, A g.val ∈ S) (f : S) :
    (Submodule.span ℂ (Set.range (fun g : S ↦
      (Submodule.Quotient.mk ⟨A g.val, h g⟩ : S ⧸ Q)))).mkQ
        (Submodule.Quotient.mk f) = 0 ↔
      ∃ g : S, (Submodule.Quotient.mk f : S ⧸ Q) = Submodule.Quotient.mk ⟨A g.val, h g⟩ :=
  mkQ_span_range_eq_zero (Q.mkQ.comp ((A.domRestrict S).codRestrict S h)) (Q.mkQ f)

/-- Paper: Equation (7.4.0.2), p. 366.
The class of a test is zero in the finite quotient exactly when its theta class
is represented by a principal value. -/
theorem finiteNuclearityQuotient_mk_eq_zero (p : HeightOneSpectrum (𝓞 ℚ)) (f : P) :
    (finiteNuclearityDenominator χ p).mkQ mkΘ(χ, f) = 0 ↔
      ∃ g : P, mkΘ(χ, f) =
        mkΘ(χ, ⟨adelePrincipalValue F (Sₚ(p)) g.val, nuclearityPrincipalValue_mem_polar (F := F) p g⟩) :=
  by
    unfold finiteNuclearityDenominator
    have hz := mkQ_principal_range_eq_zero P (Π(χ)) (adelePrincipalValue F (Sₚ(p)))
      (nuclearityPrincipalValue_mem_polar (F := F) p) f
    with_reducible exact hz

/-- Paper: Theorem 7.4.2.1(1), p. 367.
The finite-place denominator is closed and is stable under each regularized action. -/
theorem finiteNuclearityDenominator_closed_invariant (p : HeightOneSpectrum (𝓞 ℚ)) (φ : 𝒟) :
    let D := finiteNuclearityDenominator χ p
    IsClosed (D : Set (Θ₀(χ))) ∧ Set.MapsTo (Aθ(φ)) (D : Set (Θ₀(χ))) D := by sorry

-- TODO(paper-gap): The cited §7.1.4.3 concerns the entire comparison space.
-- To apply the rapid-decay argument on this quotient, one needs bounds in its
-- own topology for the functionals and the biorthogonal vectors.

/-- Paper: Theorem 7.4.2.1(2), p. 367.
The operator induced on the finite orbital quotient is of order zero. Its trace sums
the test Mellin transform over the zeros of the reciprocal partial Euler product,
counting collisions with their full order. -/
theorem finiteNuclearity_trace (p : HeightOneSpectrum (𝓞 ℚ)) (φ : 𝒟) :
    let D := finiteNuclearityDenominator χ p
    let Q := Θ₀(χ) ⧸ D
    letI instFiniteUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    let R := reciprocalPartialHeckeEulerProduct χ (Sₚ(p))
    let zeros := {z : ℂ // 0 < analyticOrderAt R z}
    let term := fun z : zeros ↦
      ((analyticOrderAt R z.val).toNat : ℂ) * nuclearityTestMellin χ φ z.val
    ∃ T : Q →L[ℂ] Q,
      (∀ f : Θ₀(χ), T (D.mkQ f) = D.mkQ (Aθ(φ) f)) ∧
      IsStronglyNuclearOperator T ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ r : NuclearPresentation T,
        HasSum (fun n ↦ r.coeff n * r.functional n (r.vector n).val) (∑' z, term z) := by sorry

end Orbital

section Archimedean

open Classical

local notation "RealPlaces" => {v : InfinitePlace F // v.IsReal}
local notation "ComplexPlaces" => {v : InfinitePlace F // v.IsComplex}
local notation "Coordinates" => (RealPlaces → ℝ) × (ComplexPlaces → ℂ)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)

variable (F) in
/-- Paper: Equation (7.4.3.1), p. 368.
Finite sums of adelic tensors have flat archimedean factors and arbitrary finite
factors. When required, each archimedean factor has additive integral zero.
Deviation: Uses the adelic tensor realization of §2.1.3 and the flat jet
conditions from §5.3.3. The tensor image carries the subspace topology from the
adelic Schwartz space. The display on p. 368 writes the projective tensor topology. -/
def globalArchimedeanFlatTests (requireArchMoment : Prop := False) : Submodule ℂ ℬ(𝔸[F]) :=
  let coordinates (x : InfiniteAdeleRing F) : Coordinates :=
    (fun v ↦ InfinitePlace.Completion.ringEquivRealOfIsReal v.property (x v.val),
      fun v ↦ InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property (x v.val))
  let tensor := (adeleSchwartz_inductiveTensor_equiv F).choose
  Submodule.span ℂ {test | ∃ (f : ℬ(InfiniteAdeleRing F))
    (g : ℬ(FiniteAdeleRing (𝓞 F) F))
    (h : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)),
    (∀ x : InfiniteAdeleRing F, f (Multiplicative.ofAdd x) = h.val (coordinates x)) ∧
      (requireArchMoment → (∫ u : Coordinates, h.val u) = 0) ∧
      tensor (f ⊗ₜ[ℂ] g) = test}

variable (F) in
/-- Paper: Equation (7.4.3.1), p. 368.
The archimedean-flat tensor image is closed in the adelic Schwartz topology,
including when the archimedean integral of each tensor factor must vanish. -/
theorem globalArchimedeanFlatTests_isClosed (requireArchMoment : Prop) :
    IsClosed (globalArchimedeanFlatTests F requireArchMoment : Set ℬ(𝔸[F])) := by sorry

/-- A flat archimedean Schwartz function vanishes at the origin, which meets a wall. -/
private theorem globalArchimedeanFlatTests_zero_moments_flat
    (h : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)) :
    h.val (0 : Coordinates) = 0 := by
  have hw : (∃ i, (0 : Coordinates).1 i = 0) ∨ (∃ j, (0 : Coordinates).2 j = 0) := by
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
    rcases w.isReal_or_isComplex with hr | hc
    · exact Or.inl ⟨⟨w, hr⟩, rfl⟩
    · exact Or.inr ⟨⟨w, hc⟩, rfl⟩
  have hk := Submodule.mem_iInf _ |>.mp h.property ⟨0, hw⟩
  have hk := Submodule.mem_iInf _ |>.mp hk 0
  have hk := Submodule.mem_iInf _ |>.mp hk (fun i => Fin.elim0 i)
  have := LinearMap.mem_ker.mp hk
  simpa using this

/-- Paper: Equation (7.4.3.1), p. 368.
Archimedean flatness kills evaluation at the adelic origin. Within the flat space,
the other zero-moment condition is the vanishing of the Fourier value at the origin. -/
theorem globalArchimedeanFlatTests_zero_moments (f : ℬ(𝔸[F]))
    (_hf : f ∈ globalArchimedeanFlatTests F) :
    f (Multiplicative.ofAdd 0) = 0 ∧
      (f ∈ adelePolarSubspace F ↔ adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0) := by
  have h0 : f (Multiplicative.ofAdd 0) = 0 := by
    let ev : ℬ(𝔸[F]) →ₗ[ℂ] ℂ :=
      { toFun := fun f ↦ f (Multiplicative.ofAdd 0)
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    change ev f = 0
    have hf : f ∈ LinearMap.ker ev := by
      refine (Submodule.span_le.mpr ?_) _hf
      rintro _ ⟨g₁, g₂, h, hx, -, rfl⟩
      change (adeleSchwartz_inductiveTensor_equiv F).choose (g₁ ⊗ₜ[ℂ] g₂) (Multiplicative.ofAdd 0) = 0
      rw [(adeleSchwartz_inductiveTensor_equiv F).choose_spec g₁ g₂ 0]
      have : g₁ (Multiplicative.ofAdd (0 : InfiniteAdeleRing F)) = 0 := by
        rw [hx 0]
        convert globalArchimedeanFlatTests_zero_moments_flat h using 2
        refine Prod.ext (funext fun v ↦ ?_) (funext fun v ↦ ?_)
        · exact map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal v.property)
        · exact map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex v.property)
      exact mul_eq_zero_of_left this _
    exact LinearMap.mem_ker.mp hf
  refine ⟨h0, ?_⟩
  rw [mem_adelePolarSubspace]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨h0, h⟩⟩

variable (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
  (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))

/-- Paper: Equation (7.4.3.1), p. 368.
The denominator uses archimedean-flat factors. On the trivial norm-one component
each factor has zero additive integral, equivalently zero local Fourier value at zero.
Deviation: Implements the prose Fourier-moment condition. On a nontrivial norm-one
isotype the moment restriction can be imposed on representatives, since the two
polar functionals are trivial-isotypic. -/
def archNuclearityDenominator : Submodule ℂ (Θ₀(χ)) :=
  Submodule.span ℂ {x : Θ₀(χ) | ∃ f : P,
    f.val ∈ globalArchimedeanFlatTests F (ω(χ) = 1) ∧ x = Submodule.Quotient.mk f}

/-- Paper: Equations (7.4.3.1) and (7.4.3.12), pp. 368 and 371.
In the homogeneous theta image the factorwise moment condition agrees with
imposing the two global polar conditions on the unrestricted flat tensors. -/
theorem mem_archNuclearityDenominator_iff_flatPolarImage (x : Θ₀(χ)) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ globalArchimedeanFlatTests F ∧ x = mkΘ(χ, f) := by sorry

/-- Paper: Equation (7.4.3.13), p. 372.
The archimedean orbital quotient divides the zero-moment theta space by its flat image.

This is a `def` with its own instances, not an `abbrev`, so that instance terms over it do
not spell out its definition (#5398). -/
def ArchNuclearityQuotient := Θ₀(χ) ⧸ archNuclearityDenominator χ

namespace ArchNuclearityQuotient

instance instAddCommGroup : AddCommGroup (ArchNuclearityQuotient χ) :=
  inferInstanceAs (AddCommGroup (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instModule : Module ℂ (ArchNuclearityQuotient χ) :=
  inferInstanceAs (Module ℂ (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instTopologicalSpace : TopologicalSpace (ArchNuclearityQuotient χ) :=
  inferInstanceAs (TopologicalSpace (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instIsTopologicalAddGroup : IsTopologicalAddGroup (ArchNuclearityQuotient χ) :=
  inferInstanceAs (IsTopologicalAddGroup (Θ₀(χ) ⧸ archNuclearityDenominator χ))

instance instContinuousSMul : ContinuousSMul ℂ (ArchNuclearityQuotient χ) :=
  inferInstanceAs (ContinuousSMul ℂ (Θ₀(χ) ⧸ archNuclearityDenominator χ))

end ArchNuclearityQuotient

/-- Paper: Equation (7.4.3.13), p. 372.
A test represents zero in the archimedean quotient exactly when its theta class
has an archimedean-flat zero-moment representative. -/
theorem archNuclearityQuotient_mk_eq_zero (f : P) :
    (archNuclearityDenominator χ).mkQ mkΘ(χ, f) = 0 ↔
      ∃ g : P, g.val ∈ globalArchimedeanFlatTests F (ω(χ) = 1) ∧ mkΘ(χ, g) = mkΘ(χ, f) := by
  let A : Submodule ℂ P := (globalArchimedeanFlatTests F (ω(χ) = 1)).comap (P).subtype
  let q : P →ₗ[ℂ] Θ₀(χ) := (Π(χ)).mkQ
  have hle : archNuclearityDenominator χ ≤ A.map q :=
    Submodule.span_le.mpr (by
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨g, hg, rfl⟩)
  constructor
  · intro hf
    exact hle ((Submodule.Quotient.mk_eq_zero (archNuclearityDenominator χ)).mp hf)
  · rintro ⟨g, hg, he⟩
    exact (Submodule.Quotient.mk_eq_zero (archNuclearityDenominator χ)).mpr
      (Submodule.subset_span ⟨g, hg, he.symm⟩)

-- The finite factors of (7.4.3.6) on p. 369 also carry their integer-unit
-- Tamagawa masses. A positive archimedean bump on the trivial isotype needs a
-- difference of dilates to give zero additive integral.

/-- Paper: Theorem 7.4.3.1(1), p. 368.
The zero-moment archimedean-flat theta image is nonzero and closed.
Deviation: Uses the Fourier-moment correction from the prose after (7.4.3.1).
Without it the printed image need not be contained in the zero-moment theta space. -/
theorem archNuclearityDenominator_nonzero_closed :
    archNuclearityDenominator χ ≠ ⊥ ∧
      IsClosed (archNuclearityDenominator χ : Set (Θ₀(χ))) := by sorry

local notation "gammaOrder(" χ ", " s ")" =>
  (analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s).toNat
local notation "atZeroPole(" χ ", " τ ", " hτ ")" =>
  (-(((existsUnique_ideleNormSection_character_phase χ τ hτ).exists.choose : ℝ) : ℂ) * Complex.I)

/-- Paper: Equations (7.4.3.2)–(7.4.3.3), p. 368.
In the fixed norm chart the archimedean pole set is the zero set of the reciprocal gamma
product. The pole set in that chart is discrete and closed. -/
theorem archNuclearityPoleSet_discrete :
    let S := {s : ℂ | 0 < gammaOrder(χ, s)}
    IsClosed S ∧ IsDiscrete S := by
  apply compl_mem_codiscrete_iff.mp
  have ha : AnalyticOnNhd ℂ (fun z ↦ (heckeGammaFactor χ z)⁻¹) univ :=
    fun z _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt z
  filter_upwards [ha.codiscreteWithin_setOfPred_analyticOrderAt_eq_zero_or_top] with z hz
  rcases hz with hz | hz <;> simp [Set.mem_compl_iff, hz]

/-- Paper: Equations (7.4.3.2)–(7.4.3.3), p. 368.
The raw order in the global chart counts the same places as the local
multiplicity of Proposition 5.3.4.5 for the restricted character. -/
theorem archNuclearityGammaOrder_eq_sLocal (S : Finset V)
    (η : PontryaginDual (SIdeleQuotient F S))
    (h : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    (_hη : sIdeleRestriction F S ⟨ideleClassNormTwist χ 0, h⟩ =
      (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) (s : ℂ) :
    gammaOrder(χ, s) = sLocalArchimedeanPoleMultiplicity η s := by
  classical
  let c : ℂ → QuasiCharacter (SIdeleQuotient F S) := fun z ↦
    quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
      (isProperMap_sIdeleQuotientNorm F S).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp η) z
  let E : InfinitePlace F → ℂ → ℂ := fun w z ↦
    infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (c z))
  -- The chart through `η` evaluates the global twist on inserted S-ideles.
  have htwist (z : ℂ) (g : (SAdeleRing F S)ˣ) :
      c z (QuotientGroup.mk g) =
        ideleClassNormTwist χ z (QuotientGroup.mk (sIdeleInsertion F S g)) := by
    have hbase := DFunLike.congr_fun _hη (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at hbase
    change (χ (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ (0 : ℂ) =
      (η (QuotientGroup.mk g) : ℂ) at hbase
    simp only [Complex.cpow_zero, mul_one] at hbase
    change (η (QuotientGroup.mk g) : ℂ) *
        (((sIdeleQuotientNorm F S (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ z =
      (χ (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ z
    rw [← hbase, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  have hinf (w : InfinitePlace F) (z : ℂ) : sLocalInfiniteRestriction w (c z) =
      infinitePlaceRestriction F w (ideleClassNormTwist χ z) := by
    ext1 x
    refine (htwist z _).trans ?_
    rw [sIdeleInsertion_infiniteUnit]
    rfl
  have hprod : (fun z ↦ heckeGammaFactor χ z) = ∏ w, E w := by
    funext z
    rw [Finset.prod_apply, ← prod_infiniteLocalEulerFactor_eq_heckeGammaFactor]
    simp only [E, hinf]
  -- Each local factor is a translate of a gamma factor, with entire reciprocal.
  have hEinv (w : InfinitePlace F) : Differentiable ℂ fun z ↦ (E w z)⁻¹ := by
    by_cases hw : w.IsReal
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real η w hw
      simp only [E, c, hb]
      exact Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const b)
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex η w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
      simp only [E, c, hb]
      convert (Complex.differentiable_Gammaℂ_inv.comp (differentiable_id.add_const b)).const_mul
        (2 : ℂ) using 1
      funext z
      rw [inv_div, div_eq_mul_inv]
      rfl
  have hEval (w : InfinitePlace F) : ∃ z₁, (E w z₁)⁻¹ ≠ 0 := by
    by_cases hw : w.IsReal
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_real η w hw
      refine ⟨1 - b, ?_⟩
      simp only [E, c, hb, sub_add_cancel]
      exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos (by norm_num))
    · obtain ⟨b, hb⟩ := infiniteLocalEulerFactor_chart_complex η w
        (InfinitePlace.not_isReal_iff_isComplex.mp hw)
      refine ⟨1 - b, ?_⟩
      simp only [E, c, hb, sub_add_cancel]
      simp [Complex.Gammaℂ_def, Real.pi_ne_zero]
  have hmer (w : InfinitePlace F) : MeromorphicAt (E w) s := by
    convert ((hEinv w).analyticAt s).meromorphicAt.inv using 1
    funext z
    simp
  have hntop (w : InfinitePlace F) : meromorphicOrderAt (E w) s ≠ ⊤ := by
    intro htop
    have h1 : meromorphicOrderAt (fun z ↦ (E w z)⁻¹) s = ⊤ := by
      rw [show meromorphicOrderAt (fun z ↦ (E w z)⁻¹) s = -meromorphicOrderAt (E w) s from
        meromorphicOrderAt_inv, htop]
      rfl
    rw [((hEinv w).analyticAt s).meromorphicOrderAt_eq] at h1
    have h2 : analyticOrderAt (fun z ↦ (E w z)⁻¹) s = ⊤ := by
      cases hn : analyticOrderAt (fun z ↦ (E w z)⁻¹) s with
      | top => rfl
      | coe n => rw [hn] at h1; simp at h1
    have hA : AnalyticOnNhd ℂ (fun z ↦ (E w z)⁻¹) univ := fun z _ ↦ (hEinv w).analyticAt z
    obtain ⟨z₁, hz₁⟩ := hEval w
    exact hz₁ (hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ s) (analyticOrderAt_eq_top.1 h2) (mem_univ z₁))
  have hle (w : InfinitePlace F) : meromorphicOrderAt (E w) s ≤ 0 := by
    have h0 := ((hEinv w).analyticAt s).meromorphicOrderAt_nonneg
    rw [show meromorphicOrderAt (fun z ↦ (E w z)⁻¹) s = -meromorphicOrderAt (E w) s from
      meromorphicOrderAt_inv] at h0
    cases hn : meromorphicOrderAt (E w) s with
    | top => exact absurd hn (hntop w)
    | coe n =>
      rw [hn] at h0
      have h0' : (0 : ℤ) ≤ -n := by exact_mod_cast h0
      exact_mod_cast (by omega : n ≤ 0)
  have key := sLocalArchimedeanPoleMultiplicity_eq_sum η s
  have hG : meromorphicOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s =
      ((sLocalArchimedeanPoleMultiplicity η s : ℤ) : WithTop ℤ) := by
    rw [show meromorphicOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s =
        -meromorphicOrderAt (fun z ↦ heckeGammaFactor χ z) s from meromorphicOrderAt_inv,
      hprod, meromorphicOrderAt_prod fun w _ ↦ hmer w,
      Finset.sum_congr rfl fun w _ ↦ (min_eq_right (hle w)).symm]
    change -(∑ w, min 0 (meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (c z))) s)) = _
    rw [← key]
    exact_mod_cast neg_neg (sLocalArchimedeanPoleMultiplicity η s : ℤ)
  rw [((differentiable_inv_heckeGammaFactor χ).analyticAt s).meromorphicOrderAt_eq] at hG
  cases hn : analyticOrderAt (fun z ↦ (heckeGammaFactor χ z)⁻¹) s with
  | top => rw [hn] at hG; simp at hG
  | coe n =>
    rw [hn] at hG
    have hn' : (n : ℤ) = (sLocalArchimedeanPoleMultiplicity η s : ℤ) := by simpa using hG
    simpa using hn'

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The raw total pole order is reduced by one at the trivial quasi-character,
when it lies on the chosen component.
Deviation: Page 368 names the quasi-character |·|^(it₀). The chart parameter it₀
corresponds to the trivial quasi-character when χ = |·|^(−it₀). -/
def archNuclearityMultiplicity (s : ℂ) : ℕ :=
  gammaOrder(χ, s) - if ω(χ) = 1 ∧ s = atZeroPole(χ, τ, hτ) then 1 else 0

/-- Paper: Theorem 7.4.3.1(2), p. 368.
For the trivial rational character, the adjusted order at zero vanishes and the
simple gamma pole at minus two remains. -/
theorem archNuclearityMultiplicity_rat_one
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 ℚ) ℚ) (hτ : RightInverse τ (ideleNorm ℚ)) :
    archNuclearityMultiplicity (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ 0 = 0 ∧
      archNuclearityMultiplicity (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ (-2) = 1 :=
  by
  have hphase := existsUnique_ideleNormSection_character_phase
    (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) τ hτ
  have hx : hphase.exists.choose = 0 :=
    hphase.unique hphase.exists.choose_spec fun t ↦ by simp
  have hω : (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)).comp
      (⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩ :
        (ideleClassNorm ℚ).ker →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) = 1 :=
    ContinuousMonoidHom.ext fun _ ↦ rfl
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hπz (z : ℂ) : (Real.pi : ℂ) ^ (z / 2) ≠ 0 := Complex.cpow_ne_zero_iff.2 (Or.inl hπ)
  have hG (z : ℂ) : (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹ =
      (Real.pi : ℂ) ^ (z / 2) * (z / 2 * ((z / 2 + 1) * (Complex.Gamma (z / 2 + 1 + 1))⁻¹)) := by
    rw [heckeGammaFactor_one,
      InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (Module.finrank_self ℚ),
      InfinitePlace.nrComplexPlaces_eq_zero_of_finrank_eq_one (Module.finrank_self ℚ),
      pow_one, pow_zero, mul_one, Complex.Gammaℝ, mul_inv, neg_div, Complex.cpow_neg, inv_inv,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one,
      Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (z / 2 + 1)]
  have hpow : Differentiable ℂ fun z : ℂ ↦ (Real.pi : ℂ) ^ (z / 2) :=
    (differentiable_id.div_const 2).const_cpow (Or.inl hπ)
  have hΓ : Differentiable ℂ fun z : ℂ ↦ (Complex.Gamma (z / 2 + 1 + 1))⁻¹ :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have hf : Differentiable ℂ fun z ↦
      (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹ := by
    simp only [hG]
    exact hpow.mul ((differentiable_id.div_const 2).mul
      (((differentiable_id.div_const 2).add_const 1).mul hΓ))
  have hΓne (z : ℂ) (hz : 0 < z.re) : (Complex.Gamma z)⁻¹ ≠ 0 :=
    inv_ne_zero (Complex.Gamma_ne_zero_of_re_pos hz)
  have h0 : (analyticOrderAt (fun z ↦
      (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹) 0).toNat = 1 := by
    rw [((hf.analyticAt 0).analyticOrderAt_eq_natCast (n := 1)).2 ⟨fun z ↦
      (Real.pi : ℂ) ^ (z / 2) * (1 / 2 * ((z / 2 + 1) * (Complex.Gamma (z / 2 + 1 + 1))⁻¹)),
      (hpow.mul ((differentiable_const _).mul
        (((differentiable_id.div_const 2).add_const 1).mul hΓ))).analyticAt 0, ?_,
      Filter.Eventually.of_forall fun z ↦ ?_⟩]
    · rfl
    · refine mul_ne_zero (hπz 0) (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
        (hΓne _ (by norm_num))))
    · rw [hG, smul_eq_mul]
      ring
  have h2 : (analyticOrderAt (fun z ↦
      (heckeGammaFactor (1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)) z)⁻¹) (-2)).toNat = 1 := by
    rw [((hf.analyticAt (-2)).analyticOrderAt_eq_natCast (n := 1)).2 ⟨fun z ↦
      (Real.pi : ℂ) ^ (z / 2) * (z / 2 * (1 / 2 * (Complex.Gamma (z / 2 + 1 + 1))⁻¹)),
      (hpow.mul ((differentiable_id.div_const 2).mul
        ((differentiable_const _).mul hΓ))).analyticAt (-2), ?_,
      Filter.Eventually.of_forall fun z ↦ ?_⟩]
    · rfl
    · refine mul_ne_zero (hπz _) (mul_ne_zero (by norm_num) (mul_ne_zero (by norm_num)
        (hΓne _ (by norm_num))))
    · rw [hG, smul_eq_mul]
      ring
  refine ⟨?_, ?_⟩ <;> unfold archNuclearityMultiplicity
  · rw [h0, hx]
    simp [hω]
  · rw [h2, hx]
    simp

/-- Paper: Theorem 7.4.3.1(2), p. 368.
Each pole contributes derivative indices from zero up to its adjusted order. -/
abbrev ArchNuclearityJetIndex := {j : ℂ × ℕ // j.2 < archNuclearityMultiplicity χ τ hτ j.1}

/-- Paper: Equation (7.4.3.4), p. 368.
The orbital jet applies a continuous entire derivative to the Mellin transform of
a zero-moment theta class. -/
def archNuclearityJet (j : ArchNuclearityJetIndex χ τ hτ) : StrongDual ℂ (Θ₀(χ)) :=
  ((entireJet j.val.1 j.val.2).comp schwartzBergmanEntireInclusion).comp (Z(χ, τ, hτ))

/-- Paper: Equation (7.4.3.4), p. 368.
On a representative the orbital jet is the derivative of the idelic zeta integral.
Its inverse Mellin formula is the convergent logarithmic moment.
Deviation: Uses the normalized inverse Mellin transform, including the missing
factor 1/(2πi) in the printed vertical integral. -/
theorem archNuclearityJet_apply (j : ArchNuclearityJetIndex χ τ hτ) (f : P) :
    let u : ℂ → ℂ := ((Z(χ, τ, hτ)) mkΘ(χ, f)).val
    let moment := fun t : ℝ ↦ (Real.log t : ℂ) ^ j.val.2 * mellinInv 0 u t
    Complex.VerticalIntegrable u 0 ∧ MellinConvergent moment j.val.1.re ∧
      archNuclearityJet χ τ hτ j mkΘ(χ, f) =
        iteratedDeriv j.val.2 (fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)) j.val.1 ∧
      archNuclearityJet χ τ hτ j mkΘ(χ, f) = mellin moment j.val.1 := by
  let v : B := (Z(χ, τ, hτ)) mkΘ(χ, f)
  have hmoment := schwartzBergman_jet_eq_mellinInv_moment v j.val.1 j.val.2
  have hz : (v.val : ℂ → ℂ) = (fun s ↦ globalIdelicZFunction f.val (ideleClassNormTwist χ s)) :=
    funext fun s ↦ ((exists_globalPolarThetaMellin χ τ hτ).choose_spec f s).2
  have hjet : archNuclearityJet χ τ hτ j mkΘ(χ, f) = iteratedDeriv j.val.2 v.val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply v))
  exact ⟨hmoment.1, hmoment.2.1, hjet.trans (congrArg (fun g : ℂ → ℂ ↦
    iteratedDeriv j.val.2 g j.val.1) hz), hjet.trans hmoment.2.2⟩

/-- Paper: Theorem 7.4.3.1(2), p. 368.
The closure of the linear span of the jets in the strong dual is the annihilator
of the archimedean-flat image. -/
theorem archNuclearityJet_span :
    ((Submodule.span ℂ (Set.range (archNuclearityJet χ τ hτ))).topologicalClosure :
        Set (StrongDual ℂ (Θ₀(χ)))) =
      {ℓ | ∀ x : archNuclearityDenominator χ, ℓ x.val = 0} := by sorry

/-- At one infinite place the gamma factor vanishes, by Mathlib's convention at the poles
of `Γ`, along an arithmetic progression. So the reciprocal gamma product has a zero of
positive finite order at infinitely many points. -/
private theorem archNuclearityJet_basis_poles_infinite
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    {s : ℂ | 0 < gammaOrder(χ, s)}.Infinite := by
  classical
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let c : ℂ := if hv : v.IsReal then
      (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ)
    else
      (complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2
  let s : ℕ → ℂ := fun n ↦ -c - 2 * n
  have hzero (n : ℕ) : heckeGammaFactor χ (s n) = 0 := by
    unfold heckeGammaFactor
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    by_cases hv : v.IsReal
    · simp only [s, c, hv, ↓reduceDIte]
      rw [Complex.Gammaℝ_eq_zero_iff]
      exact ⟨n, by ring⟩
    · simp only [s, c, hv, ↓reduceDIte]
      rw [div_eq_zero_iff]
      left
      rw [show -(_ + _) - 2 * (n : ℂ) + _ + _ = -((2 * n : ℕ) : ℂ) by push_cast; ring,
        Complex.Gammaℂ_def, Complex.Gamma_neg_nat_eq_zero, mul_zero]
  let f := fun z ↦ (heckeGammaFactor χ z)⁻¹
  have hA : AnalyticOnNhd ℂ f univ :=
    fun z _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt z
  have hpos (n : ℕ) : s n ∈ {s : ℂ | 0 < gammaOrder(χ, s)} := by
    have h0 : analyticOrderAt f (s n) ≠ 0 :=
      analyticOrderAt_ne_zero.mpr ⟨hA _ (mem_univ _), by simp [f, hzero n]⟩
    have htop : analyticOrderAt f (s n) ≠ ⊤ := by
      intro htop
      have h1 := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
        (mem_univ (s n)) (analyticOrderAt_eq_top.1 htop) (mem_univ 1)
      exact inv_ne_zero
        (heckeGammaFactor_ne_zero_of_re_pos χ (by norm_num : (0 : ℝ) < (1 : ℂ).re)) h1
    change 0 < (analyticOrderAt f (s n)).toNat
    cases hn : analyticOrderAt f (s n) with
    | top => exact absurd hn htop
    | coe m =>
      rw [hn] at h0
      simpa [Nat.pos_iff_ne_zero] using h0
  refine Set.infinite_of_injective_forall_mem (fun n m h ↦ ?_) hpos
  have := congrArg Complex.re h
  simp only [s, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im] at this
  norm_num at this
  exact_mod_cast this

/-- The adjusted jet indices are countably infinite: they lie over the closed discrete
pole set, and the adjustment removes at most one index from an infinite pole set. -/
private theorem archNuclearityJet_basis_index_equiv
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F)) :
    Nonempty (ℕ ≃ ArchNuclearityJetIndex χ τ hτ) := by
  let S := {s : ℂ | 0 < gammaOrder(χ, s)}
  have hS : S.Countable := by
    have hd := (archNuclearityPoleSet_discrete χ).2
    have : DiscreteTopology S := hd.to_subtype
    exact Set.countable_coe_iff.mp
      (TopologicalSpace.separableSpace_iff_countable.mp inferInstance)
  have hmem (j : ArchNuclearityJetIndex χ τ hτ) : j.val.1 ∈ S := by
    have h := j.property
    unfold archNuclearityMultiplicity at h
    show 0 < gammaOrder(χ, j.val.1)
    omega
  have : Countable (ArchNuclearityJetIndex χ τ hτ) := by
    have := hS.to_subtype
    refine Function.Injective.countable
      (f := fun j : ArchNuclearityJetIndex χ τ hτ ↦ ((⟨j.val.1, hmem j⟩ : S), j.val.2)) ?_
    intro a b h
    simp only [Prod.mk.injEq, Subtype.mk.injEq] at h
    exact Subtype.ext (Prod.ext h.1 h.2)
  have : Infinite (ArchNuclearityJetIndex χ τ hτ) := by
    have := ((archNuclearityJet_basis_poles_infinite χ).sdiff
      (Set.finite_singleton (atZeroPole(χ, τ, hτ)))).to_subtype
    refine Infinite.of_injective
      (fun s : ↥(S \ {atZeroPole(χ, τ, hτ)}) ↦
        (⟨(s.val, 0), ?_⟩ : ArchNuclearityJetIndex χ τ hτ)) ?_
    · have hs := s.property
      simp only [Set.mem_sdiff, Set.mem_singleton_iff] at hs
      change 0 < archNuclearityMultiplicity χ τ hτ s.val
      unfold archNuclearityMultiplicity
      have hne : ¬(ω(χ) = 1 ∧ s.val = atZeroPole(χ, τ, hτ)) := fun h ↦ hs.2 h.2
      simp only [hne, ↓reduceIte, Nat.sub_zero]
      simpa [S] using hs.1
    · intro a b h
      exact Subtype.ext (congrArg (fun j : ArchNuclearityJetIndex χ τ hτ ↦ j.val.1) h)
  exact ⟨(nonempty_equiv_of_countable (α := ArchNuclearityJetIndex χ τ hτ)).some.symm⟩

/-- Paper: Theorem 7.4.3.1(3), p. 368.
For a fixed enumeration of the adjusted jets, the descended jets form a Schauder basis
of the strong dual of the archimedean quotient, with continuous coefficient functionals
on that strong dual. Pullback along the quotient map recovers the original jets.
This is the second half of `archNuclearityJet_basis`; the first half, that the adjusted
jet indices are countably infinite, is proved above. Given the jet-coordinate isomorphism
of the quotient with `ArchNuclearityJetIndex χ τ hτ → ℂ` (the statement of
`archNuclearityQuotient_jetEquiv`, which comes later in this file and so cannot be used
here), take `d n` to be the coordinate at `σ n`, take `b m` to be evaluation at the vector
with coordinate one at `σ m` and zero elsewhere, and use that a continuous functional on a
product of copies of `ℂ` depends on finitely many coordinates. -/
private theorem archNuclearityJet_basis_schauder
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F) (hτ : RightInverse τ (ideleNorm F))
    (σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ) :
    ∃ (d : ℕ → StrongDual ℂ (ArchNuclearityQuotient χ))
      (b : ℕ → StrongDual ℂ (StrongDual ℂ (ArchNuclearityQuotient χ))),
      (∀ n x, d n ((archNuclearityDenominator χ).mkQ x) = archNuclearityJet χ τ hτ (σ n) x) ∧
        IsSchauderBasis d b := by sorry

/-- Paper: Theorem 7.4.3.1(3), p. 368.
Every enumeration of the adjusted jets gives a Schauder basis on the quotient strong
dual. Pullback along the quotient map recovers the original jets. -/
theorem archNuclearityJet_basis :
    let Q := ArchNuclearityQuotient χ
    let J := ArchNuclearityJetIndex χ τ hτ
    Nonempty (ℕ ≃ J) ∧
      ∀ σ : ℕ ≃ J, ∃ (d : ℕ → StrongDual ℂ Q) (b : ℕ → StrongDual ℂ (StrongDual ℂ Q)),
        (∀ n x, d n ((archNuclearityDenominator χ).mkQ x) = archNuclearityJet χ τ hτ (σ n) x) ∧
        IsSchauderBasis d b :=
  ⟨archNuclearityJet_basis_index_equiv χ τ hτ, archNuclearityJet_basis_schauder χ τ hτ⟩

local notation "finiteL(" χ ")" => (finiteHeckeL_exists_continuation χ).choose
local notation "poleFactor(" χ ", " τ ", " hτ ", " s ")" =>
  ((s : ℂ) - 1 - atZeroPole(χ, τ, hτ)) ^ (if ω(χ) = 1 then (1 : ℕ) else 0)

private theorem archRegularizedFiniteHeckeL_cancel_simplePole {A Z : ℂ → ℂ} {z : ℂ}
    (ha : AnalyticAt ℂ A z) (hvan : A z = 0)
    (hZ : MeromorphicAt Z z) (hpole : meromorphicOrderAt Z z = -1) :
    0 ≤ meromorphicOrderAt (A * Z) z := by
  have hpos : 0 < meromorphicOrderAt A z := lt_of_le_of_ne ha.meromorphicOrderAt_nonneg
    (fun he ↦ ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp he.symm hvan)
  rw [meromorphicOrderAt_mul ha.meromorphicAt hZ, hpole]
  cases ho : meromorphicOrderAt A z with
  | top => simp
  | coe k =>
    rw [ho] at hpos
    have hk : (0 : ℤ) < k := WithTop.coe_lt_coe.mp hpos
    exact WithTop.coe_le_coe.mpr (show (0 : ℤ) ≤ k + (-1) by omega)

/-- Paper: Equation (7.4.3.5), p. 368.
After cancellation of the pole on the trivial norm-one component, the continued
finite Hecke function is entire. -/
theorem archRegularizedFiniteHeckeL_differentiable :
    Differentiable ℂ (toMeromorphicNFOn
      (fun s ↦ poleFactor(χ, τ, hτ, s) * finiteL(χ) s) univ) := by
  let p : ℂ → ℂ := fun z ↦ poleFactor(χ, τ, hτ, z)
  let R : ℂ → ℂ := fun z ↦ (heckeGammaFactor χ z)⁻¹
  let L := finiteL(χ)
  let Z := continuedCompletedHeckeL χ
  obtain ⟨hL, heL⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨hZ, heZ⟩ := continuedCompletedHeckeL_spec χ
  have hp : Differentiable ℂ p := by
    dsimp only [p]
    fun_prop
  have hR : Differentiable ℂ R := differentiable_inv_heckeGammaFactor χ
  have hA : Differentiable ℂ (p * R) := hp.mul hR
  have hm : MeromorphicOn ((p * R) * Z) univ := fun z _ ↦
    (hA.analyticAt z).meromorphicAt.mul (hZ (mem_univ z)).meromorphicAt
  change Differentiable ℂ (toMeromorphicNFOn (p * L) univ)
  rw [heckeEulerProductOutside_eq_finite_nf_eq (p * L) ((p * R) * Z)
    (fun z _ ↦ (hp.analyticAt z).meromorphicAt.mul (hL (mem_univ z)).meromorphicAt) hm (by
      intro z hz
      change p z * L z = p z * (heckeGammaFactor χ z)⁻¹ * Z z
      rw [show L z = _ from heL ⟨z, hz⟩, show Z z = _ from heZ ⟨z, hz⟩]
      change _ = p z * (heckeGammaFactor χ z)⁻¹ * (heckeGammaFactor χ z * _)
      rw [mul_assoc, inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz))]
      rfl)]
  by_cases hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1
  · have hω : ω(χ) = 1 := by
      ext1 u
      exact DFunLike.congr_fun hk u
    obtain ⟨t, ⟨hc, hzero, hone, haway⟩, -⟩ := completedHeckeL_continuation_simplePoles χ Z hZ heZ hk
    let b : ℂ := Complex.I * (t : ℂ)
    have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
    have hx : -t = hphase.exists.choose := by
      apply hphase.unique _ hphase.exists.choose_spec
      intro u
      have he := DFunLike.congr_fun hc (QuotientGroup.mk (τ u))
      change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
        1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ))) at he
      rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
      simpa only [Complex.ofReal_neg, neg_mul, mul_comm (t : ℂ) Complex.I] using he
    have hpole : atZeroPole(χ, τ, hτ) = b := by
      change -(hphase.exists.choose : ℂ) * Complex.I = b
      rw [← hx, Complex.ofReal_neg, neg_neg, mul_comm]
    have hz₀ : (p * R) b = 0 := by
      have hshift := heckeGammaFactor_of_normTwist χ (-Complex.I * (t : ℂ)) (by simp [Complex.mul_re]) hc b
      have hneg : b + -Complex.I * (t : ℂ) = 0 := by
        dsimp [b]
        ring
      have hg : R b = 0 := by
        change (heckeGammaFactor χ b)⁻¹ = 0
        rw [hshift, hneg]
        simpa using inv_heckeGammaFactor_one_neg_even (F := F) 0
      simp [hg]
    have hz₁ : (p * R) (1 + b) = 0 := by simp [p, hω, hpole]
    intro z
    apply AnalyticAt.differentiableAt
    apply (meromorphicNFOn_toMeromorphicNFOn _ _ (mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _)]
    by_cases hz : z = b ∨ z = 1 + b
    · rcases hz with rfl | rfl
      · exact archRegularizedFiniteHeckeL_cancel_simplePole (hA.analyticAt _) hz₀
          (hZ (mem_univ _)).meromorphicAt hzero
      · exact archRegularizedFiniteHeckeL_cancel_simplePole (hA.analyticAt _) hz₁
          (hZ (mem_univ _)).meromorphicAt hone
    · exact ((hA.analyticAt z).mul (haway z (by simpa [b] using hz))).meromorphicOrderAt_nonneg
  · have hd := hA.mul (completedHeckeL_continuation_entire χ Z hZ heZ hk)
    rwa [toMeromorphicNFOn_eq_self.mpr (fun z _ ↦ (hd.analyticAt z).meromorphicNFAt)]

/-- Paper: Equation (7.4.3.5), p. 368.
The generator of the archimedean ideal is the pole-removed finite Hecke function.
Normal form supplies the removable value at its canceled pole. -/
def archRegularizedFiniteHeckeL : Entire :=
  let h := archRegularizedFiniteHeckeL_differentiable χ τ hτ
  ⟨⟨_, h.continuous⟩, h⟩

/-- Paper: Equation (7.4.3.5), p. 368.
On the half-plane of absolute convergence the generator equals the Euler product
times the pole-removing factor. -/
theorem archRegularizedFiniteHeckeL_apply (s : {s : ℂ // 1 < s.re}) :
    (archRegularizedFiniteHeckeL χ τ hτ).val s.val =
      poleFactor(χ, τ, hτ, s.val) * finiteHeckeL χ s := by
  let pole : ℂ → ℂ := fun z ↦ poleFactor(χ, τ, hτ, z)
  have hP (z : ℂ) : AnalyticAt ℂ pole z := by
    dsimp only [pole]
    fun_prop
  have hne : pole s ≠ 0 := by
    apply pow_ne_zero
    intro h
    have hr := congrArg Complex.re h
    have hs := s.property
    simp at hr
    linarith
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hm : MeromorphicOn (fun z ↦ pole z * finiteL(χ) z) univ :=
    fun z hz ↦ (hP z).meromorphicAt.mul (hL.1 hz).meromorphicAt
  have hNF : MeromorphicNFAt (fun z ↦ pole z * finiteL(χ) z) s :=
    (meromorphicNFAt_mul_iff_right (hP s) hne).2 (hL.1 (mem_univ _))
  change toMeromorphicNFOn (fun z ↦ pole z * finiteL(χ) z) univ s = pole s * finiteHeckeL χ s
  rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
    toMeromorphicNFAt_eq_self.mpr hNF]
  exact congrArg (pole s * ·) (hL.2 s)

-- TODO(paper-gap): Before (7.4.3.12) on p. 371, not every numerator class
-- comes from a flat test. For ℚ, S = {∞}, χ = 1, finite PV is the identity.
-- The real Gaussian combination in Printed.archNuclearityJet_apply_false has
-- nonzero global Z(-2), whereas a flat real test times the finite integer
-- indicator has Z(-2) = 0. Also, odd flat bumps have zero trivial theta class.
-- Apply §6.2 to homogeneous classes of polar tests, then identify the image
-- of the flat denominator under insertion. Uniqueness is a quotient assertion.
-- TODO(paper-gap): On p. 371, injectivity of the comparison quotient map requires
-- the range identification below. Density of the inclusion into entire functions
-- does not give that identification. Evaluations at nontrivial completed zeros
-- lie in the kernel of the printed adjoint to the theta annihilator. Pass to
-- the relative quotient of the completed ideal by the finite ideal.

/-- Paper: Theorem 7.4.3.1(4), p. 368.
The Mellin image of the flat denominator is the intersection of the entire
principal ideal generated by the regularized finite Hecke function with the
Schwartz–Bergman space. That image is closed. -/
theorem archNuclearityMellin_range :
    let D := (Z(χ, τ, hτ)) '' (archNuclearityDenominator χ : Set (Θ₀(χ)))
    D = (schwartzBergmanDivisible (archRegularizedFiniteHeckeL χ τ hτ) : Set B) ∧ IsClosed D := by sorry

/-- Paper: Equation (7.4.3.13), p. 372.
Each adjusted jet annihilates the archimedean orbital denominator, so the jets are
well defined on the quotient by it. -/
theorem archNuclearityQuotient_jetEquiv_annihilate (j : ArchNuclearityJetIndex χ τ hτ)
    (x : archNuclearityDenominator χ) :
    archNuclearityJet χ τ hτ j x.val = 0 := by sorry

/-- Paper: Equation (7.4.3.13), p. 372.
The adjusted jets assemble into a single continuous linear map from the archimedean
orbital quotient to the product of the coefficient spaces. -/
theorem archNuclearityQuotient_jetEquiv_coefficients :
    ∃ L : ArchNuclearityQuotient χ →L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ),
      ∀ (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ),
        L ((archNuclearityDenominator χ).mkQ x) j = archNuclearityJet χ τ hτ j x := by
  have hker : ∀ j : ArchNuclearityJetIndex χ τ hτ,
      archNuclearityDenominator χ ≤ (archNuclearityJet χ τ hτ j).ker :=
    fun j _ hy ↦ archNuclearityQuotient_jetEquiv_annihilate (χ := χ) (τ := τ) (hτ := hτ) j ⟨_, hy⟩
  refine ⟨ContinuousLinearMap.pi fun j ↦ (archNuclearityDenominator χ).liftQL
    (archNuclearityJet χ τ hτ j) (hker j), ?_⟩
  intro x j
  exact Submodule.liftQ_apply (p := archNuclearityDenominator χ)
    (f := (archNuclearityJet χ τ hτ j).toLinearMap) (h := hker j) (x := x)

/-- Paper: Equation (7.4.3.13), p. 372.
The adjusted jets separate the classes of the archimedean orbital quotient: a class
on which every jet vanishes is the class of a flat test, that is, it lies in the
denominator. -/
theorem archNuclearityQuotient_jetEquiv_separating (x : Θ₀(χ))
    (hx : ∀ j, archNuclearityJet χ τ hτ j x = 0) : x ∈ archNuclearityDenominator χ := by
  sorry

/-- Paper: Equation (7.4.3.13), p. 372.
Every family of coefficient values is realized by a class of the archimedean
orbital quotient: the coefficient map is onto the whole product. -/
theorem archNuclearityQuotient_jetEquiv_realization
    (y : ArchNuclearityJetIndex χ τ hτ → ℂ) :
    ∃ x : Θ₀(χ), ∀ j, archNuclearityJet χ τ hτ j x = y j := by sorry

/-- Paper: Equation (7.4.3.13), p. 372.
The coefficient map of the archimedean orbital quotient is a topological isomorphism:
the inverse of the bijective coefficient map is continuous. -/
theorem archNuclearityQuotient_jetEquiv_inverse_continuous
    (L : ArchNuclearityQuotient χ →L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ))
    (hL : ∀ (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ),
      L ((archNuclearityDenominator χ).mkQ x) j = archNuclearityJet χ τ hτ j x)
    (h : Function.Bijective L) :
    Continuous ((LinearEquiv.ofBijective L.toLinearMap h).symm :
      (ArchNuclearityJetIndex χ τ hτ → ℂ) → ArchNuclearityQuotient χ) := by sorry

/-- Paper: Equation (7.4.3.13) and the following paragraph, p. 372.
The coefficients of a quotient class are its adjusted jets, with the product topology.
The map includes simultaneous realization of every family of coefficients. -/
theorem archNuclearityQuotient_jetEquiv :
    ∃ e : ArchNuclearityQuotient χ ≃L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ),
      ∀ (x : Θ₀(χ)) j, e ((archNuclearityDenominator χ).mkQ x) j =
        archNuclearityJet χ τ hτ j x := by
  obtain ⟨L, hL⟩ := archNuclearityQuotient_jetEquiv_coefficients (χ := χ) (τ := τ) (hτ := hτ)
  have hinj : Function.Injective L := by
    intro a b hab
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (archNuclearityDenominator χ) a
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective (archNuclearityDenominator χ) b
    have hzero : x - y ∈ archNuclearityDenominator χ := by
      refine archNuclearityQuotient_jetEquiv_separating (χ := χ) (τ := τ) (hτ := hτ)
        (x - y) fun j ↦ ?_
      rw [map_sub, ← hL x j, ← hL y j]
      exact sub_eq_zero.mpr (congrArg (fun f : (ArchNuclearityJetIndex χ τ hτ → ℂ) ↦ f j) hab)
    have hsub : (archNuclearityDenominator χ).mkQ x - (archNuclearityDenominator χ).mkQ y = 0 := by
      rw [← map_sub, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hzero
    exact sub_eq_zero.mp hsub
  have hsurj : Function.Surjective L := by
    intro y
    obtain ⟨x, hx⟩ := archNuclearityQuotient_jetEquiv_realization (χ := χ) (τ := τ) (hτ := hτ) y
    exact ⟨(archNuclearityDenominator χ).mkQ x, funext fun j ↦ (hL x j).trans (hx j)⟩
  refine ⟨⟨LinearEquiv.ofBijective L.toLinearMap ⟨hinj, hsurj⟩, L.continuous, ?_⟩, hL⟩
  exact archNuclearityQuotient_jetEquiv_inverse_continuous (χ := χ) (τ := τ) (hτ := hτ)
    L hL ⟨hinj, hsurj⟩

/-- Transport the topology generated by all seminorms across a continuous linear equivalence. -/
private theorem archNuclearityStrongDual_finest_of_equiv {A E : Type*}
    [AddCommGroup A] [Module ℂ A] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (e : FinestLocallyConvex A ≃L[ℂ] E) :
    (inferInstance : TopologicalSpace E) = (inferInstance : TopologicalSpace (FinestLocallyConvex E)) := by
  let := finestLocallyConvex_t2 A
  let := finestLocallyConvex_t2 E
  have h := continuous_of_finestLocallyConvex A
    (show FinestLocallyConvex A →ₗ[ℂ] FinestLocallyConvex E from e.toLinearMap)
  have h' := continuous_of_finestLocallyConvex E
    (show FinestLocallyConvex E →ₗ[ℂ] FinestLocallyConvex A from e.symm.toLinearMap)
  apply le_antisymm <;> apply continuous_id_iff_le.mp
  · exact (h.comp e.symm.continuous).congr (fun x ↦ e.apply_symm_apply x)
  · exact (e.continuous.comp h').congr (fun x ↦ e.apply_symm_apply x)

/-- Enumerating the adjusted jets identifies the quotient with the space of complex sequences. -/
private theorem archNuclearityStrongDual_finest_sequenceEquiv
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) :
    Nonempty (ArchNuclearityQuotient χ ≃L[ℂ] (ℕ → ℂ)) := by
  let τ : ℝ≥0ˣ →ₜ* IdeleGroup (𝓞 F) F :=
    ⟨canonicalIdeleNormSection F, canonicalIdeleNormSection_continuous F⟩
  have hτ : RightInverse τ (ideleNorm F) := canonicalIdeleNormSection_rightInverse F
  obtain ⟨q, _⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  obtain ⟨σ⟩ := (archNuclearityJet_basis χ τ hτ).1
  exact ⟨q.trans (ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : ℕ ↦ ℂ) σ.symm)⟩

/-- Paper: Theorem 7.4.3.1(5), pp. 368–369.
The strong dual of the archimedean quotient carries the finest locally convex topology. -/
theorem archNuclearityStrongDual_finest :
    let E := StrongDual ℂ (ArchNuclearityQuotient χ)
    (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)) := by
  obtain ⟨q⟩ := archNuclearityStrongDual_finest_sequenceEquiv χ
  obtain ⟨t, _⟩ := realSchwartzTaylor_equiv
  obtain ⟨p, _⟩ := realDiracDerivatives_polynomialEquiv
  let : TopologicalSpace (PowerSeries ℂ) := inferInstanceAs (TopologicalSpace ((Unit →₀ ℕ) → ℂ))
  let idx := (Finsupp.uniqueLinearEquiv ℕ ℕ ()).symm.toEquiv
  let series := ContinuousLinearEquiv.piCongrLeft ℂ (fun _ : Unit →₀ ℕ ↦ ℂ) idx
  let e := (q.trans series).trans t.symm
  exact archNuclearityStrongDual_finest_of_equiv
    (p.trans (e.symm.arrowCongr (ContinuousLinearEquiv.refl ℂ ℂ)))

local notation "Aθ(" φ ")" => (exists_polarThetaNuclearityAction χ τ hτ φ).choose

/-- Absolute convergence on every norm line makes the Mellin multiplier entire. -/
private theorem archNuclearityDenominator_closed_invariant_multiplier
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (φ : 𝒟) :
    Differentiable ℂ (nuclearityTestMellin χ φ) := by
  let : BorelSpace C𝔽 := ⟨rfl⟩
  let n := fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)
  let f := fun g : C𝔽 ↦ φ.val g * (χ g : ℂ)
  have hn : Continuous n :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have heq (s : ℂ) (g : C𝔽) : f g * (n g : ℂ) ^ s = testIntegrand(χ, φ, s) g :=
    mul_assoc _ _ _
  have h := analyticOnNhd_integral_mul_cpow_of_integrable μ𝔽 f n hn.measurable
    (fun g ↦ NNReal.coe_pos.mpr (Units.zero_lt _)) isOpen_univ
    (fun s _ ↦ by simpa only [heq] using (nuclearityTestMellin_integrable χ φ).1 s)
  have hfun : nuclearityTestMellin χ φ = fun s ↦ ∫ g, f g * (n g : ℂ) ^ s ∂μ𝔽 := by
    funext s
    simp only [heq, nuclearityTestMellin]
  rw [hfun]
  exact fun s ↦ (h s (mem_univ _)).differentiableAt

/-- Paper: Theorem 7.4.3.2(1), p. 372.
The archimedean-flat theta denominator is a closed subspace stable under the
regularized action of every Bruhat test. -/
theorem archNuclearityDenominator_closed_invariant (φ : 𝒟) :
    let D := archNuclearityDenominator χ
    IsClosed (D : Set (Θ₀(χ))) ∧ Set.MapsTo (Aθ(φ)) (D : Set (Θ₀(χ))) D := by
  let D := archNuclearityDenominator χ
  obtain ⟨e, he⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  have hmem (x : Θ₀(χ)) : x ∈ D ↔ ∀ j, archNuclearityJet χ τ hτ j x = 0 := by
    rw [← Submodule.Quotient.mk_eq_zero D]
    change (archNuclearityDenominator χ).mkQ x = (0 : ArchNuclearityQuotient χ) ↔ _
    constructor
    · intro hx j
      rw [← he x j, hx, map_zero, Pi.zero_apply]
    · intro hx
      apply e.injective
      funext j
      rw [he x j, hx j, map_zero, Pi.zero_apply]
  have hjet (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x = iteratedDeriv j.val.2 ((Z(χ, τ, hτ)) x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply _))
  constructor
  · rw [show (D : Set (Θ₀(χ))) = ⋂ j, (archNuclearityJet χ τ hτ j) ⁻¹' {0} by
      apply Set.ext
      intro x
      rw [mem_iInter]
      exact hmem x]
    exact isClosed_iInter fun j ↦ isClosed_singleton.preimage (archNuclearityJet χ τ hτ j).continuous
  · intro x hx
    apply (hmem _).mpr
    intro j
    let v := (Z(χ, τ, hτ)) x
    have hv : Differentiable ℂ v.val := fun z ↦
      (v.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : ((Z(χ, τ, hτ)) (Aθ(φ) x)).val = nuclearityTestMellin χ φ * v.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x)
    rw [hjet, hprod, iteratedDeriv_mul
      ((archNuclearityDenominator_closed_invariant_multiplier χ φ).contDiff.contDiffAt)
      hv.contDiff.contDiffAt]
    apply Finset.sum_eq_zero
    intro i _
    have hk := (hmem x).mp hx ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩
    rw [hjet] at hk
    exact mul_eq_zero_of_right _ hk

/-- The reciprocal Gamma function vanishes to order at most one everywhere, by the
recursion `1/Γ(s) = s · 1/Γ(s + 1)`. -/
private theorem archNuclearity_trace_gammaInv_order_le (w : ℂ) :
    analyticOrderAt (fun s ↦ (Complex.Gamma s)⁻¹) w ≤ 1 := by
  have han (z : ℂ) : AnalyticAt ℂ (fun s ↦ (Complex.Gamma s)⁻¹) z :=
    Complex.differentiable_one_div_Gamma.analyticAt z
  by_cases hw : (Complex.Gamma w)⁻¹ = 0
  · obtain ⟨n, rfl⟩ := (Complex.Gamma_eq_zero_iff w).mp (inv_eq_zero.mp hw)
    induction n with
    | zero =>
      have hrec : (fun s ↦ (Complex.Gamma s)⁻¹) =
          (fun s : ℂ ↦ s - 0) * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ s + 1)) := by
        funext s
        simp [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
      rw [hrec, analyticOrderAt_mul (by fun_prop) ((han _).comp (by fun_prop)),
        analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
      simp only [Nat.cast_zero, neg_zero]
      rw [analyticOrderAt_id_sub_const_self, zero_add,
        ((han 1).analyticOrderAt_eq_zero).mpr (by simp)]
      simp
    | succ n ih =>
      have hrec : (fun s ↦ (Complex.Gamma s)⁻¹) =
          (fun s : ℂ ↦ s) * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ s + 1)) := by
        funext s
        simp [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one s]
      rw [hrec, analyticOrderAt_mul (by fun_prop) ((han _).comp (by fun_prop)),
        analyticOrderAt_comp_of_deriv_ne_zero (by fun_prop) (by simp)]
      have h0 : analyticOrderAt (fun s : ℂ ↦ s) (-((n + 1 : ℕ) : ℂ)) = 0 :=
        (analyticAt_id.analyticOrderAt_eq_zero).mpr (by
          show -(((n + 1 : ℕ) : ℂ)) ≠ 0
          rw [neg_ne_zero, Nat.cast_ne_zero]
          exact Nat.succ_ne_zero n)
      have h1 : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
      rw [h0, zero_add, h1]
      exact ih (by
        rw [inv_eq_zero]
        exact Complex.Gamma_neg_nat_eq_zero n)
  · rw [((han w).analyticOrderAt_eq_zero).mpr hw]
    exact zero_le

/-- A nonvanishing analytic factor times the reciprocal Gamma function at an affine
argument vanishes to order at most one. -/
private theorem archNuclearity_trace_affine_order_le (u : ℂ → ℂ) (a c z : ℂ) (ha : a ≠ 0)
    (hu : AnalyticAt ℂ u z) (hu0 : u z ≠ 0) :
    analyticOrderAt (fun s ↦ u s * (Complex.Gamma (a * s + c))⁻¹) z ≤ 1 := by
  have hg : AnalyticAt ℂ (fun s : ℂ ↦ a * s + c) z := by fun_prop
  have hΓ : AnalyticAt ℂ ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ a * s + c)) z :=
    (Complex.differentiable_one_div_Gamma.analyticAt _).comp hg
  change analyticOrderAt (u * ((fun s ↦ (Complex.Gamma s)⁻¹) ∘ (fun s : ℂ ↦ a * s + c))) z ≤ 1
  rw [analyticOrderAt_mul hu hΓ, (hu.analyticOrderAt_eq_zero).mpr hu0, zero_add,
    analyticOrderAt_comp_of_deriv_ne_zero hg (by
      rw [deriv_add_const, deriv_const_mul _ differentiableAt_id, deriv_id'']
      simpa using ha)]
  exact archNuclearity_trace_gammaInv_order_le _

/-- The reciprocal of an archimedean Gamma factor is entire, vanishes to order at most
one, and vanishes only at `-c - k` for natural `k`. -/
private theorem archNuclearity_trace_factor (f : ℂ → ℂ) (c : ℂ)
    (hf : (∀ s, f s = Complex.Gammaℝ (s + c)) ∨ (∀ s, f s = Complex.Gammaℂ (s + c) / 2))
    (z : ℂ) :
    AnalyticAt ℂ (fun s ↦ (f s)⁻¹) z ∧ analyticOrderAt (fun s ↦ (f s)⁻¹) z ≤ 1 ∧
      ((f z)⁻¹ = 0 → ∃ k : ℕ, z = -c - k) := by
  rcases hf with hf | hf
  · have he : (fun s ↦ (f s)⁻¹) = fun s ↦ ((Real.pi : ℂ) ^ (-(s + c) / 2))⁻¹ *
        (Complex.Gamma ((1 / 2 : ℂ) * s + c / 2))⁻¹ := by
      funext s
      rw [hf, Complex.Gammaℝ_def, mul_inv, show (s + c) / 2 = 1 / 2 * s + c / 2 by ring]
    have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hu : Differentiable ℂ fun s : ℂ ↦ ((Real.pi : ℂ) ^ (-(s + c) / 2))⁻¹ :=
      fun s ↦ ((((differentiable_id.add_const c).neg.div_const 2) s).const_cpow
        (Or.inl hπ)).inv (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ))
    refine ⟨?_, ?_, fun h0 ↦ ?_⟩
    · rw [he]
      exact (hu.analyticAt z).mul ((Complex.differentiable_one_div_Gamma.analyticAt _).comp
        (by fun_prop))
    · rw [he]
      exact archNuclearity_trace_affine_order_le _ _ _ z (by norm_num) (hu.analyticAt z)
        (inv_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl hπ)))
    · rw [hf] at h0
      obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp (inv_eq_zero.mp h0)
      exact ⟨2 * n, by push_cast; linear_combination hn⟩
  · have he : (fun s ↦ (f s)⁻¹) = fun s ↦ (2 * (2 * (2 * Real.pi : ℂ) ^ (-(s + c)))⁻¹) *
        (Complex.Gamma (1 * s + c))⁻¹ := by
      funext s
      rw [hf, Complex.Gammaℂ_def, one_mul]
      simp only [div_eq_mul_inv, mul_inv, inv_inv]
      ring
    have h2π : (2 * Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hpow (s : ℂ) : (2 * Real.pi : ℂ) ^ (-(s + c)) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl h2π)
    have hu : Differentiable ℂ fun s : ℂ ↦ 2 * (2 * (2 * Real.pi : ℂ) ^ (-(s + c)))⁻¹ :=
      fun s ↦ ((((differentiable_id.add_const c).neg s).const_cpow (Or.inl h2π)).const_mul
        2).inv (mul_ne_zero two_ne_zero (hpow s)) |>.const_mul 2
    refine ⟨?_, ?_, fun h0 ↦ ?_⟩
    · rw [he]
      exact (hu.analyticAt z).mul ((Complex.differentiable_one_div_Gamma.analyticAt _).comp
        (by fun_prop))
    · rw [he]
      exact archNuclearity_trace_affine_order_le _ _ _ z one_ne_zero (hu.analyticAt z)
        (mul_ne_zero two_ne_zero (inv_ne_zero (mul_ne_zero two_ne_zero (hpow z))))
    · rw [hf, inv_eq_zero, div_eq_zero_iff, Complex.Gammaℂ_def] at h0
      have hΓ : Complex.Gamma (z + c) = 0 := by
        rcases h0 with h0 | h0
        · rcases mul_eq_zero.mp h0 with h | h
          · exact absurd h (mul_ne_zero two_ne_zero (hpow z))
          · exact h
        · exact absurd h0 two_ne_zero
      obtain ⟨n, hn⟩ := (Complex.Gamma_eq_zero_iff _).mp hΓ
      exact ⟨n, by linear_combination hn⟩

/-- The reciprocal of a finite product of archimedean Gamma factors vanishes to order at
most the number of factors, and only at points `-c i - k`. -/
private theorem archNuclearity_trace_prod {ι : Type*} [Fintype ι] (f : ι → ℂ → ℂ)
    (c : ι → ℂ) (hf : ∀ i, (∀ s, f i s = Complex.Gammaℝ (s + c i)) ∨
      (∀ s, f i s = Complex.Gammaℂ (s + c i) / 2)) (z : ℂ) :
    analyticOrderAt (fun s ↦ (∏ i, f i s)⁻¹) z ≤ Fintype.card ι ∧
      ((∏ i, f i z)⁻¹ = 0 → ∃ i, ∃ k : ℕ, z = -c i - k) := by
  classical
  have hinv : (fun s ↦ (∏ i, f i s)⁻¹) = fun s ↦ ∏ i, (f i s)⁻¹ := by
    funext s
    rw [Finset.prod_inv_distrib]
  refine ⟨?_, fun h0 ↦ ?_⟩
  · rw [hinv, ← Finset.card_univ]
    have key : ∀ s : Finset ι, AnalyticAt ℂ (fun w ↦ ∏ i ∈ s, (f i w)⁻¹) z ∧
        analyticOrderAt (fun w ↦ ∏ i ∈ s, (f i w)⁻¹) z ≤ s.card := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        refine ⟨by simpa using analyticAt_const, ?_⟩
        simp only [Finset.prod_empty, Finset.card_empty, Nat.cast_zero]
        exact ((analyticAt_const).analyticOrderAt_eq_zero.mpr one_ne_zero).le
      | insert a s ha ih =>
        obtain ⟨hfa, hoa, -⟩ := archNuclearity_trace_factor (f a) (c a) (hf a) z
        have he : (fun w ↦ ∏ i ∈ insert a s, (f i w)⁻¹) =
            (fun w ↦ (f a w)⁻¹) * fun w ↦ ∏ i ∈ s, (f i w)⁻¹ := by
          funext w
          rw [Finset.prod_insert ha]
          rfl
        rw [he]
        refine ⟨hfa.mul ih.1, ?_⟩
        rw [analyticOrderAt_mul hfa ih.1, Finset.card_insert_of_notMem ha, Nat.cast_add,
          Nat.cast_one, add_comm (s.card : ℕ∞)]
        exact add_le_add hoa ih.2
    exact (key Finset.univ).2
  · rw [← Finset.prod_inv_distrib, Finset.prod_eq_zero_iff] at h0
    obtain ⟨i, -, hi⟩ := h0
    obtain ⟨k, hk⟩ := (archNuclearity_trace_factor (f i) (c i) (hf i) z).2.2 hi
    exact ⟨i, k, hk⟩

/-- A test supported where the modulus lies in `[r, R]` has Mellin transform bounded by
`(r^σ + R^σ) ∫ ‖φ‖` on the line of real part `σ`. -/
private theorem archNuclearity_trace_mellin_bound {G : Type*} [MeasurableSpace G]
    (μ : Measure G) (φ : G → ℂ) (hφ : Integrable (fun g ↦ ‖φ g‖) μ) (n : G → ℝ) (r R : ℝ)
    (hr : 0 < r) (hsupp : ∀ g, φ g ≠ 0 → r ≤ n g ∧ n g ≤ R) (w : G → ℂ) (σ : ℝ)
    (hw : ∀ g, φ g ≠ 0 → ‖w g‖ = n g ^ σ) :
    ‖∫ g, φ g * w g ∂μ‖ ≤ (r ^ σ + R ^ σ) * ∫ g, ‖φ g‖ ∂μ := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (hφ.const_mul _) (ae_of_all _ fun g ↦ ?_)
  by_cases h0 : φ g = 0
  · simp only [h0, zero_mul, norm_zero, mul_zero, le_refl]
  obtain ⟨hlo, hhi⟩ := hsupp g h0
  have hn : 0 < n g := hr.trans_le hlo
  rw [norm_mul, hw g h0, mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  rcases le_total 0 σ with hσ | hσ
  · exact (Real.rpow_le_rpow hn.le hhi hσ).trans
      (le_add_of_nonneg_left (Real.rpow_nonneg hr.le σ))
  · exact (Real.rpow_le_rpow_of_nonpos hr hlo hσ).trans
      (le_add_of_nonneg_right (Real.rpow_nonneg (hn.trans_le hhi).le σ))

/-- Poles at `-c v - k` with bounded orders, and transforms bounded by `r^σ + R^σ` with
`1 < r ≤ R`, give an absolutely convergent pole sum. -/
private theorem archNuclearity_trace_pole_summable {W : Type*} [Finite W] (c : W → ℂ)
    (ord : ℂ → ℕ) (N : ℕ) (hord : ∀ z, ord z ≤ N)
    (hpole : ∀ z, 0 < ord z → ∃ v, ∃ k : ℕ, z = -c v - k) (M : ℂ → ℂ) (K r R : ℝ)
    (hK : 0 ≤ K) (hr : 1 < r) (hR : 1 < R)
    (hM : ∀ z, ‖M z‖ ≤ (r ^ z.re + R ^ z.re) * K) :
    Summable fun z : ℂ ↦ (ord z : ℝ) * ‖M z‖ := by
  classical
  let Pz := {z : ℂ // 0 < ord z}
  have hsub : ∀ x ∉ Set.range (Subtype.val : Pz → ℂ), (ord x : ℝ) * ‖M x‖ = 0 := by
    intro x hx
    have : ord x = 0 := by
      by_contra h
      exact hx ⟨⟨x, Nat.pos_of_ne_zero h⟩, rfl⟩
    simp [this]
  rw [← Function.Injective.summable_iff Subtype.val_injective hsub]
  choose v k hvk using fun z : Pz ↦ hpole z.val z.property
  let ι : Pz → W × ℕ := fun z ↦ (v z, k z)
  have hι : Function.Injective ι := by
    intro a b h
    apply Subtype.ext
    rw [hvk a, hvk b]
    simp only [ι, Prod.mk.injEq] at h
    rw [h.1, h.2]
  let g : W × ℕ → ℝ := fun p ↦ N * K * (r ^ (-(c p.1).re) * (r⁻¹) ^ p.2 +
    R ^ (-(c p.1).re) * (R⁻¹) ^ p.2)
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hR0 : 0 < R := zero_lt_one.trans hR
  have hNK : 0 ≤ (N : ℝ) * K := mul_nonneg (Nat.cast_nonneg _) hK
  have hg0 (p : W × ℕ) : 0 ≤ g p :=
    mul_nonneg hNK (add_nonneg
      (mul_nonneg (Real.rpow_nonneg hr0.le _) (pow_nonneg (inv_nonneg.mpr hr0.le) _))
      (mul_nonneg (Real.rpow_nonneg hR0.le _) (pow_nonneg (inv_nonneg.mpr hR0.le) _)))
  have hg : Summable g := by
    refine (summable_prod_of_nonneg hg0).mpr ⟨fun x ↦ ?_, Summable.of_finite⟩
    have h1 : Summable fun y : ℕ ↦ r ^ (-(c x).re) * (r⁻¹) ^ y :=
      Summable.mul_left (r ^ (-(c x).re))
        (summable_geometric_of_lt_one (inv_nonneg.mpr hr0.le) (inv_lt_one_of_one_lt₀ hr))
    have h2 : Summable fun y : ℕ ↦ R ^ (-(c x).re) * (R⁻¹) ^ y :=
      Summable.mul_left (R ^ (-(c x).re))
        (summable_geometric_of_lt_one (inv_nonneg.mpr hR0.le) (inv_lt_one_of_one_lt₀ hR))
    have h3 := Summable.mul_left ((N : ℝ) * K) (h1.add h2)
    exact h3
  refine Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
    (fun z ↦ ?_) (hg.comp_injective hι)
  have hz : (z.val).re = -(c (v z)).re - k z := by
    rw [hvk z]
    simp
  have hpow (a : ℝ) (ha : 0 < a) : a ^ (z.val).re = a ^ (-(c (v z)).re) * (a⁻¹) ^ k z := by
    rw [hz, Real.rpow_sub ha, Real.rpow_natCast, div_eq_mul_inv, inv_pow]
  change (ord z.val : ℝ) * ‖M z.val‖ ≤ N * K * (r ^ (-(c (v z)).re) * (r⁻¹) ^ k z +
    R ^ (-(c (v z)).re) * (R⁻¹) ^ k z)
  rw [← hpow r hr0, ← hpow R hR0, mul_assoc, mul_comm K]
  exact mul_le_mul (by exact_mod_cast hord _) (hM _) (norm_nonneg _) (Nat.cast_nonneg _)

/-- Summing a function of the center over all jet indices counts each center with its
multiplicity, in any enumeration of the indices. -/
private theorem archNuclearity_trace_reindex (m : ℂ → ℕ) (M : ℂ → ℂ)
    (σ : ℕ ≃ {j : ℂ × ℕ // j.2 < m j.1})
    (h : Summable fun z : ℂ ↦ (m z : ℝ) * ‖M z‖) :
    Summable (fun n ↦ ‖M (σ n).val.1‖) ∧
      HasSum (fun n ↦ M (σ n).val.1) (∑' z, (m z : ℂ) * M z) := by
  let J := {j : ℂ × ℕ // j.2 < m j.1}
  let e : J ≃ Σ z : ℂ, Fin (m z) :=
    { toFun := fun j ↦ ⟨j.val.1, ⟨j.val.2, j.property⟩⟩
      invFun := fun p ↦ ⟨(p.1, p.2.val), p.2.isLt⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let f : (Σ z : ℂ, Fin (m z)) → ℂ := fun p ↦ M p.1
  have hfib (z : ℂ) : ∑' _ : Fin (m z), ‖M z‖ = (m z : ℝ) * ‖M z‖ := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnorm : Summable fun p ↦ ‖f p‖ :=
    (summable_sigma_of_nonneg fun _ ↦ norm_nonneg _).mpr
      ⟨fun _ ↦ Summable.of_finite, by simpa only [f, hfib] using h⟩
  have hf : Summable f := hnorm.of_norm
  have hsum : ∑' p, f p = ∑' z, (m z : ℂ) * M z := by
    rw [hf.tsum_sigma' fun _ ↦ Summable.of_finite]
    refine tsum_congr fun z ↦ ?_
    rw [tsum_fintype]
    change ∑ _b : Fin (m z), M z = _
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hcomp : (fun n ↦ M (σ n).val.1) = f ∘ (σ.trans e) := rfl
  have hcompn : (fun n ↦ ‖M (σ n).val.1‖) = (fun p ↦ ‖f p‖) ∘ (σ.trans e) := rfl
  refine ⟨?_, ?_⟩
  · rw [hcompn]
    exact (σ.trans e).summable_iff.mpr hnorm
  · rw [hcomp, ← hsum]
    exact (σ.trans e).hasSum_iff.mpr hf.hasSum

/-- A biorthogonal coefficient functional picks out the coefficient of its own vector
from a finite combination in which that vector occurs exactly once. -/
private theorem archNuclearity_trace_diag {E ι : Type*} [AddCommGroup E] [Module ℂ E]
    (d : ℕ → E) (b : ℕ → E →ₗ[ℂ] ℂ) (hb : ∀ m n, b m (d n) = if m = n then 1 else 0)
    (n : ℕ) (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∈ s) (coef : ι → ℂ) (idx : ι → ℕ)
    (h₀ : idx i₀ = n) (hne : ∀ i ∈ s, i ≠ i₀ → idx i ≠ n) :
    b n (∑ i ∈ s, coef i • d (idx i)) = coef i₀ := by
  rw [map_sum, Finset.sum_eq_single i₀]
  · simp [hb, h₀]
  · intro i hi hi'
    have hn : ¬ n = idx i := fun h ↦ hne i hi hi' h.symm
    simp [hb, hn]
  · intro h
    exact absurd hi₀ h

/-- The reciprocal archimedean gamma factor of `χ` vanishes to order at most the number of
infinite places, and only at points `-c v - k` with `k` a natural number. -/
private theorem archNuclearity_trace_gammaOrder :
    ∃ c : InfinitePlace F → ℂ, ∀ z : ℂ, gammaOrder(χ, z) ≤ Fintype.card (InfinitePlace F) ∧
      (0 < gammaOrder(χ, z) → ∃ v, ∃ k : ℕ, z = -c v - k) := by
  let G : InfinitePlace F → ℂ → ℂ := fun v s ↦ if hv : v.IsReal then
      Complex.Gammaℝ (s + (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ))
    else Complex.Gammaℂ (s + (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2) / 2
  let c : InfinitePlace F → ℂ := fun v ↦ if hv : v.IsReal then
      (realHeckeCharacter_parameters χ v hv).exists.choose.1 +
        ((realHeckeCharacter_parameters χ v hv).exists.choose.2.val : ℂ)
    else (complexHeckeCharacter_parameters χ v
        (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.1 +
        ((complexHeckeCharacter_parameters χ v
          (InfinitePlace.not_isReal_iff_isComplex.mp hv)).exists.choose.2.natAbs : ℂ) / 2
  have hG (s : ℂ) : heckeGammaFactor χ s = ∏ v, G v s := by
    unfold heckeGammaFactor
    rfl
  have hc (v : InfinitePlace F) : (∀ s, G v s = Complex.Gammaℝ (s + c v)) ∨
      (∀ s, G v s = Complex.Gammaℂ (s + c v) / 2) := by
    by_cases hv : v.IsReal
    · exact Or.inl fun s ↦ by simp only [G, c, hv, ↓reduceDIte, add_assoc]
    · exact Or.inr fun s ↦ by simp only [G, c, hv, ↓reduceDIte, add_assoc]
  refine ⟨c, fun z ↦ ?_⟩
  have hfun : (fun s ↦ (heckeGammaFactor χ s)⁻¹) = fun s ↦ (∏ v, G v s)⁻¹ :=
    funext fun s ↦ by rw [hG]
  obtain ⟨hord, hzero⟩ := archNuclearity_trace_prod G c hc z
  have han := (differentiable_inv_heckeGammaFactor χ).analyticAt z
  constructor
  · rw [hfun]
    cases h : analyticOrderAt (fun s ↦ (∏ v, G v s)⁻¹) z with
    | top => simp
    | coe n =>
      rw [h] at hord
      simpa using hord
  · intro hpos
    apply hzero
    rw [← hG]
    by_contra hne
    rw [(han.analyticOrderAt_eq_zero).mpr hne] at hpos
    simp at hpos

/-- A Bruhat test supported where the norm exceeds one has Mellin transform bounded by
`(r^σ + R^σ) K` on the line of real part `σ`, for some `1 < r` and `1 < R`: the norm is
bounded above and below on the compact support. -/
private theorem archNuclearity_trace_mellin (φ : 𝒟)
    (hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    ∃ K r R : ℝ, 0 ≤ K ∧ 1 < r ∧ 1 < R ∧
      ∀ z, ‖nuclearityTestMellin χ φ z‖ ≤ (r ^ z.re + R ^ z.re) * K := by
  let n : C𝔽 → ℝ := fun g ↦ ((ideleClassNorm F g).val : ℝ)
  have hn : Continuous n := NNReal.continuous_coe.comp
    (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hK : IsCompact (tsupport φ.val) := φ.property.2
  obtain ⟨r, R, hr, hR, hrR⟩ : ∃ r R : ℝ, 1 < r ∧ 1 < R ∧
      ∀ g ∈ tsupport φ.val, r ≤ n g ∧ n g ≤ R := by
    rcases (tsupport φ.val).eq_empty_or_nonempty with he | hne
    · exact ⟨2, 2, by norm_num, by norm_num, fun g hg ↦ by simp [he] at hg⟩
    · obtain ⟨a, ha, hamin⟩ := hK.exists_isMinOn hne hn.continuousOn
      obtain ⟨b, hb, hbmax⟩ := hK.exists_isMaxOn hne hn.continuousOn
      exact ⟨n a, n b, hφ ha, hφ hb, fun g hg ↦
        ⟨isMinOn_iff.mp hamin g hg, isMaxOn_iff.mp hbmax g hg⟩⟩
  have htw (s : ℂ) (g : C𝔽) : ‖ideleClassNormTwist χ s g‖ = n g ^ s.re := by
    change ‖(χ g : ℂ) * ((n g : ℝ) : ℂ) ^ s‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
  have hint : Integrable (fun g ↦ ‖φ.val g‖) μ𝔽 := by
    refine ((nuclearityTestMellin_integrable χ φ).1 0).norm.congr (ae_of_all _ fun g ↦ ?_)
    change ‖φ.val g * ideleClassNormTwist χ 0 g‖ = ‖φ.val g‖
    rw [norm_mul, htw, Complex.zero_re, Real.rpow_zero, mul_one]
  refine ⟨∫ g, ‖φ.val g‖ ∂μ𝔽, r, R, integral_nonneg fun _ ↦ norm_nonneg _, hr, hR,
    fun z ↦ ?_⟩
  exact archNuclearity_trace_mellin_bound μ𝔽 φ.val hint n r R (zero_lt_one.trans hr)
    (fun g hg ↦ hrR g (subset_tsupport _ hg)) (ideleClassNormTwist χ z) z.re
    (fun g _ ↦ htw z g)

/-- On a trivial norm-one isotype the omitted jet sits at a gamma pole, and the
norm twist of `χ` there is the trivial quasi-character. -/
private theorem archNuclearity_trace_trivial (hω : ω(χ) = 1) :
    1 ≤ gammaOrder(χ, atZeroPole(χ, τ, hτ)) ∧
      ∀ g, ideleClassNormTwist χ atZeroPole(χ, τ, hτ) g = ideleClassNormTwist 1 0 g := by
  have hk : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
    ext1 u
    exact DFunLike.congr_fun hω u
  obtain ⟨hZ, heZ⟩ := continuedCompletedHeckeL_spec χ
  obtain ⟨t, ⟨hc, -, -, -⟩, -⟩ := completedHeckeL_continuation_simplePoles χ _ hZ heZ hk
  let b : ℂ := Complex.I * (t : ℂ)
  have hphase := existsUnique_ideleNormSection_character_phase χ τ hτ
  have hx : -t = hphase.exists.choose := by
    apply hphase.unique _ hphase.exists.choose_spec
    intro u
    have he := DFunLike.congr_fun hc (QuotientGroup.mk (τ u))
    change (χ (QuotientGroup.mk (τ u)) : ℂ) * _ ^ (0 : ℂ) =
      1 * ((((ideleNorm F (τ u)).val : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ))) at he
    rw [Complex.cpow_zero, mul_one, one_mul, hτ u] at he
    simpa only [Complex.ofReal_neg, neg_mul, mul_comm (t : ℂ) Complex.I] using he
  have hpole : atZeroPole(χ, τ, hτ) = b := by
    change -(hphase.exists.choose : ℂ) * Complex.I = b
    rw [← hx, Complex.ofReal_neg, neg_neg, mul_comm]
  rw [hpole]
  have hR0 : (heckeGammaFactor χ b)⁻¹ = 0 := by
    have hshift := heckeGammaFactor_of_normTwist χ (-Complex.I * (t : ℂ))
      (by simp [Complex.mul_re]) hc b
    have hneg : b + -Complex.I * (t : ℂ) = 0 := by
      dsimp [b]
      ring
    rw [hshift, hneg]
    simpa using inv_heckeGammaFactor_one_neg_even (F := F) 0
  have han : AnalyticOnNhd ℂ (fun s ↦ (heckeGammaFactor χ s)⁻¹) univ :=
    fun s _ ↦ (differentiable_inv_heckeGammaFactor χ).analyticAt s
  have hne0 : analyticOrderAt (fun s ↦ (heckeGammaFactor χ s)⁻¹) b ≠ 0 := by
    rw [Ne, (han b (mem_univ _)).analyticOrderAt_eq_zero, not_not]
    exact hR0
  have hnetop : analyticOrderAt (fun s ↦ (heckeGammaFactor χ s)⁻¹) b ≠ ⊤ := by
    intro htop
    have h1 : (heckeGammaFactor χ 1)⁻¹ ≠ 0 :=
      inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (by norm_num))
    exact h1 (han.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ b) (analyticOrderAt_eq_top.1 htop) (mem_univ 1))
  refine ⟨?_, fun g ↦ ?_⟩
  · obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp hnetop
    rw [← hm] at hne0 ⊢
    rw [ENat.toNat_natCast]
    exact Nat.one_le_iff_ne_zero.mpr (by exact_mod_cast hne0)
  · have hx0 : ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    have he := DFunLike.congr_fun hc g
    change (χ g : ℂ) * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) =
      1 * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (-Complex.I * (t : ℂ)) at he
    change (χ g : ℂ) * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ b =
      1 * ((((ideleClassNorm F g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ)
    rw [Complex.cpow_zero, mul_one, one_mul] at he
    rw [he, ← Complex.cpow_add _ _ hx0, show -Complex.I * (t : ℂ) + b = 0 by dsimp [b]; ring,
      Complex.cpow_zero, mul_one]

/-- Continuous functionals on a quotient agree once they agree on representatives. -/
private theorem archNuclearity_trace_qext {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (D : Submodule ℂ E) (f g : StrongDual ℂ (E ⧸ D))
    (h : ∀ x, f (D.mkQ x) = g (D.mkQ x)) : f = g :=
  ContinuousLinearMap.ext fun q ↦ by
    obtain ⟨x, rfl⟩ := D.mkQ_surjective q
    exact h x

/-- Abstract form of the diagonal computation: if an operator `A` acts on jet coordinates by
the Leibniz rule with multiplier derivatives `Md i`, then for biorthogonal coefficient
functionals the diagonal entry of the induced quotient operator is the multiplier at the
center of the jet. -/
private theorem archNuclearity_trace_diagonal {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (D : Submodule ℂ E) (A : E →ₗ[ℂ] E) (T : (E ⧸ D) →L[ℂ] (E ⧸ D))
    (hT : ∀ x, T (D.mkQ x) = D.mkQ (A x)) (m : ℂ → ℕ)
    (σ : ℕ ≃ {j : ℂ × ℕ // j.2 < m j.1}) (jet : {j : ℂ × ℕ // j.2 < m j.1} → E → ℂ)
    (Md : ℕ → ℂ → ℂ) (M₀ : ℂ → ℂ) (hMd₀ : ∀ z, Md 0 z = M₀ z)
    (hjetA : ∀ x (j : {j : ℂ × ℕ // j.2 < m j.1}), jet j (A x) =
      ∑ i ∈ Finset.range (j.val.2 + 1), (j.val.2.choose i : ℂ) * Md i j.val.1 *
        jet ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩ x)
    (d : ℕ → StrongDual ℂ (E ⧸ D)) (b : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ D)))
    (hd : ∀ n x, d n (D.mkQ x) = jet (σ n) x)
    (hb : ∀ m n, b m (d n) = if m = n then 1 else 0) (n : ℕ) :
    b n ((d n).comp T) = M₀ (σ n).val.1 := by
  have hcomp : (d n).comp T = ∑ i ∈ Finset.range ((σ n).val.2 + 1),
      (((σ n).val.2.choose i : ℂ) * Md i (σ n).val.1) •
        d (σ.symm ⟨((σ n).val.1, (σ n).val.2 - i),
          (Nat.sub_le _ _).trans_lt (σ n).property⟩) := by
    refine archNuclearity_trace_qext D _ _ fun x ↦ ?_
    rw [ContinuousLinearMap.comp_apply, hT, hd, hjetA, ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [ContinuousLinearMap.smul_apply, hd, Equiv.apply_symm_apply, smul_eq_mul]
  rw [hcomp]
  refine (archNuclearity_trace_diag d (fun m ↦ (b m).toLinearMap) hb n
    (Finset.range ((σ n).val.2 + 1)) 0 (by simp)
    (fun i ↦ ((σ n).val.2.choose i : ℂ) * Md i (σ n).val.1)
    (fun i ↦ σ.symm ⟨((σ n).val.1, (σ n).val.2 - i),
      (Nat.sub_le _ _).trans_lt (σ n).property⟩) ?_ ?_).trans ?_
  · rw [Equiv.symm_apply_eq]
    exact Subtype.ext (Prod.ext rfl (Nat.sub_zero _))
  · intro i hi hi0 heq
    rw [Equiv.symm_apply_eq] at heq
    have h2 := congrArg (fun j : {j : ℂ × ℕ // j.2 < m j.1} ↦ j.val.2) heq
    have hik := Finset.mem_range.mp hi
    simp only at h2
    omega
  · simp [hMd₀]

/-- The scalar half of Theorem 7.4.3.2(2): the gamma-pole series converges absolutely, and
for every enumeration of the jets the Mellin values at the jet centers sum absolutely to
the pole series minus the omitted trivial jet. -/
private theorem archNuclearity_trace_scalar (φ : 𝒟)
    (hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    let poles := {z : ℂ // 0 < gammaOrder(χ, z)}
    let term := fun z : poles ↦ (gammaOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ z.val
    let correction := if ω(χ) = 1 then nuclearityTestMellin 1 φ 0 else 0
    Summable (fun z ↦ ‖term z‖) ∧ ∀ σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ,
      Summable (fun n ↦ ‖nuclearityTestMellin χ φ (σ n).val.1‖) ∧
      HasSum (fun n ↦ nuclearityTestMellin χ φ (σ n).val.1) ((∑' z, term z) - correction) := by
  intro poles term correction
  classical
  let M := nuclearityTestMellin χ φ
  obtain ⟨c, hc⟩ := archNuclearity_trace_gammaOrder χ
  obtain ⟨K, r, R, hK, hr, hR, hM⟩ := archNuclearity_trace_mellin χ φ hφ
  have hsum : Summable fun z : ℂ ↦ (gammaOrder(χ, z) : ℝ) * ‖M z‖ :=
    archNuclearity_trace_pole_summable c (fun z ↦ gammaOrder(χ, z)) _ (fun z ↦ (hc z).1)
      (fun z ↦ (hc z).2) M K r R hK hr hR hM
  refine ⟨(hsum.subtype fun z ↦ 0 < gammaOrder(χ, z)).congr fun z ↦ ?_, fun σ ↦ ?_⟩
  · simp only [Function.comp_apply, term, norm_mul, Complex.norm_natCast]
    rfl
  let mult := archNuclearityMultiplicity χ τ hτ
  have hmult : Summable fun z : ℂ ↦ (mult z : ℝ) * ‖M z‖ :=
    Summable.of_nonneg_of_le (fun _ ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
      (fun z ↦ mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le _ _) (norm_nonneg _))
      hsum
  obtain ⟨h1, h2⟩ := archNuclearity_trace_reindex mult M σ hmult
  refine ⟨h1, ?_⟩
  convert h2 using 1
  have hsupp : Function.support (fun z : ℂ ↦ (gammaOrder(χ, z) : ℂ) * M z) ⊆
      {z | 0 < gammaOrder(χ, z)} := by
    intro z hz
    by_contra h
    simp only [Set.mem_ofPred_eq, not_lt, Nat.le_zero] at h
    exact hz (by simp [h])
  have htsum : ∑' z : poles, term z = ∑' z : ℂ, (gammaOrder(χ, z) : ℂ) * M z :=
    tsum_subtype_eq_of_support_subset (s := {z | 0 < gammaOrder(χ, z)}) hsupp
  have hsumC : Summable fun z : ℂ ↦ (gammaOrder(χ, z) : ℂ) * M z :=
    Summable.of_norm (by simpa only [norm_mul, Complex.norm_natCast] using hsum)
  rw [htsum]
  by_cases hω : ω(χ) = 1
  · obtain ⟨hord1, htw⟩ := archNuclearity_trace_trivial χ τ hτ hω
    have hm (z : ℂ) : (mult z : ℂ) * M z = (gammaOrder(χ, z) : ℂ) * M z -
        if z = atZeroPole(χ, τ, hτ) then M atZeroPole(χ, τ, hτ) else 0 := by
      simp only [mult, archNuclearityMultiplicity, hω, true_and]
      split_ifs with h
      · subst h
        rw [Nat.cast_sub hord1]
        ring
      · simp
    have hcorr : correction = M atZeroPole(χ, τ, hτ) := by
      simp only [correction, hω, ↓reduceIte]
      refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
      change φ.val g * ideleClassNormTwist 1 0 g = φ.val g * ideleClassNormTwist χ _ g
      rw [htw g]
    rw [tsum_congr hm, hsumC.tsum_sub (hasSum_ite_eq _ _).summable, tsum_ite_eq, hcorr]
  · have hm (z : ℂ) : (mult z : ℂ) * M z = (gammaOrder(χ, z) : ℂ) * M z := by
      simp [mult, archNuclearityMultiplicity, hω]
    simp only [correction, hω, ↓reduceIte, sub_zero]
    exact (tsum_congr hm).symm


-- TODO(paper-gap): The contour identity (7.4.3.15) uses positive pole orders
-- on the right, but the logarithmic derivative has their negatives as residues.
-- Both boundary lines must avoid the poles. With χ = 1 over ℚ and a = 2,
-- the left line passes through the simple pole at -2.

/-- Paper: Theorem 7.4.3.2(2), pp. 372–373.
For tests supported where the norm is greater than one, the quotient operator has
an absolutely convergent matrix trace in every enumeration of the specified
basis of the strong dual. The gamma-pole series is also absolutely convergent.
Deviation: On a trivial norm-one isotype the omitted jet is at the trivial
quasi-character, so its weight is the integral of the test with no character factor. -/
theorem archNuclearity_trace (φ : 𝒟)
    (_hφ : tsupport φ.val ⊆ {g : C𝔽 | 1 < ((ideleClassNorm F g).val : ℝ)}) :
    let D := archNuclearityDenominator χ
    let Q := Θ₀(χ) ⧸ D
    let poles := {z : ℂ // 0 < gammaOrder(χ, z)}
    let term := fun z : poles ↦ (gammaOrder(χ, z.val) : ℂ) * nuclearityTestMellin χ φ z.val
    let correction := if ω(χ) = 1 then nuclearityTestMellin 1 φ 0 else 0
    ∃ T : Q →L[ℂ] Q,
      (∀ f, T (D.mkQ f) = D.mkQ (Aθ(φ) f)) ∧ Summable (fun z ↦ ‖term z‖) ∧
      ∀ (σ : ℕ ≃ ArchNuclearityJetIndex χ τ hτ) (d : ℕ → StrongDual ℂ Q)
        (b : ℕ → StrongDual ℂ (StrongDual ℂ Q)),
        (∀ n x, d n (D.mkQ x) = archNuclearityJet χ τ hτ (σ n) x) →
        IsSchauderBasis d b →
        let diagonal := fun n ↦ b n ((d n).comp T)
        Summable (fun n ↦ ‖diagonal n‖) ∧ HasSum diagonal ((∑' z, term z) - correction) := by
  intro D Q poles term correction
  obtain ⟨hterm, hσ⟩ := archNuclearity_trace_scalar χ τ hτ φ _hφ
  let M := nuclearityTestMellin χ φ
  have hmaps := (archNuclearityDenominator_closed_invariant χ τ hτ φ).2
  let T₀ : Q →ₗ[ℂ] Q := D.mapQ D (Aθ(φ)).toLinearMap fun x hx ↦ hmaps hx
  have hT₀ : Continuous T₀ := by
    apply (Submodule.isQuotientMap_mkQ D).continuous_iff.mpr
    exact (Submodule.isQuotientMap_mkQ D).continuous.comp (Aθ(φ)).continuous
  let T : Q →L[ℂ] Q := ⟨T₀, hT₀⟩
  have hT (x : Θ₀(χ)) : T (D.mkQ x) = D.mkQ (Aθ(φ) x) := rfl
  refine ⟨T, hT, hterm, ?_⟩
  intro σ d b hd hb diagonal
  have hjet (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x = iteratedDeriv j.val.2 ((Z(χ, τ, hτ)) x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply _))
  have hjetA (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j (Aθ(φ) x) = ∑ i ∈ Finset.range (j.val.2 + 1),
        (j.val.2.choose i : ℂ) * iteratedDeriv i M j.val.1 *
          archNuclearityJet χ τ hτ ⟨(j.val.1, j.val.2 - i),
            (Nat.sub_le _ _).trans_lt j.property⟩ x := by
    let v := (Z(χ, τ, hτ)) x
    have hv : Differentiable ℂ v.val := fun z ↦
      (v.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : ((Z(χ, τ, hτ)) (Aθ(φ) x)).val = M * v.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x)
    rw [hjet, hprod, iteratedDeriv_mul
      ((archNuclearityDenominator_closed_invariant_multiplier χ φ).contDiff.contDiffAt)
      hv.contDiff.contDiffAt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [hjet]
  have hdiag (n : ℕ) : diagonal n = M (σ n).val.1 := by
    have h := archNuclearity_trace_diagonal D (Aθ(φ)).toLinearMap T hT
      (archNuclearityMultiplicity χ τ hτ) σ (fun j x ↦ archNuclearityJet χ τ hτ j x)
      (fun i z ↦ iteratedDeriv i M z) M (fun z ↦ by simp) hjetA d b hd (fun m n ↦ hb.1 m n) n
    exact h
  have hdiagfun : diagonal = fun n ↦ M (σ n).val.1 := funext hdiag
  rw [hdiagfun]
  exact hσ σ

/-- A von Neumann bounded set in a space carrying the finest locally convex topology
spans a finite-dimensional subspace: otherwise a linear functional unbounded on it
would be continuous. -/
private theorem archNuclearityStrongDual_finiteRank_bounded {E : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E]
    (h : (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (S : Set E) (hS : Bornology.IsVonNBounded ℂ S) :
    FiniteDimensional ℂ (Submodule.span ℂ S) := by
  by_contra hfin
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ S
  have hinf : b.Infinite := by
    intro hb
    apply hfin
    rw [← hspan]
    exact FiniteDimensional.span_of_finite ℂ hb
  let f := hinf.natEmbedding
  let v : ℕ → E := fun n ↦ (f n).val
  have hv : LinearIndependent ℂ v := hli.comp f f.injective
  let ℓ₀ : Submodule.span ℂ (Set.range v) →ₗ[ℂ] ℂ :=
    (Finsupp.linearCombination ℂ (fun n : ℕ ↦ (n : ℂ))).comp hv.repr
  obtain ⟨ℓ, hℓ⟩ := LinearMap.exists_extend ℓ₀
  have hℓv (n : ℕ) : ℓ (v n) = n := by
    have h1 := congrArg (fun g ↦ g ⟨v n, Submodule.subset_span ⟨n, rfl⟩⟩) hℓ
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h1
    rw [h1]
    simp [ℓ₀, hv.repr_eq_single n ⟨v n, Submodule.subset_span ⟨n, rfl⟩⟩ rfl]
  have hcont' : Continuous (show FinestLocallyConvex E →ₗ[ℂ] ℂ from ℓ) := by
    apply WithSeminorms.continuous_normedSpace_rng ℂ (finestLocallyConvex_withSeminorms (E := E))
    refine ⟨{(normSeminorm ℂ ℂ).comp ℓ}, 1, ?_⟩
    rw [one_smul]
    exact Finset.le_sup (f := id) (Finset.mem_singleton_self _)
  have hcont : Continuous ℓ := by
    have : @Continuous E ℂ (inferInstance : TopologicalSpace (FinestLocallyConvex E)) _ ℓ :=
      hcont'
    rwa [← h] at this
  let L : E →L[ℂ] ℂ := ⟨ℓ, hcont⟩
  have hb := (hS.image L)
  rw [NormedSpace.isVonNBounded_iff] at hb
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hb
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have := hC (L (v n)) ⟨v n, hbS (f n).property, rfl⟩
  change ‖ℓ (v n)‖ ≤ C at this
  rw [hℓv, Complex.norm_natCast] at this
  linarith

/-- In a Hausdorff space with the finest locally convex topology, an operator with a
nuclear presentation has range inside the span of its Banach disc, which is
finite-dimensional. -/
private theorem archNuclearityStrongDual_finiteRank_gen {E : Type*} [AddCommGroup E]
    [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E] [ContinuousSMul ℂ E]
    (h : (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (T : E →L[ℂ] E) (hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range := by
  obtain ⟨r⟩ := hT
  let W := Submodule.span ℂ r.disc
  have hW : FiniteDimensional ℂ W :=
    archNuclearityStrongDual_finiteRank_bounded h r.disc r.isBanachDisc.bounded
  have hWc : IsClosed (W : Set E) := W.isClosed_of_finiteDimensional
  have hle : T.toLinearMap.range ≤ W := by
    rintro _ ⟨x, rfl⟩
    apply hWc.mem_of_tendsto (r.hasSum x)
    filter_upwards with s
    exact W.sum_mem fun n _ ↦ W.smul_mem _ (r.vector n).property
  exact Submodule.finiteDimensional_of_le hle

private theorem archNuclearityStrongDual_finiteRank_dual {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] [TopologicalSpace Q] [IsTopologicalAddGroup Q] [ContinuousSMul ℂ Q]
    (h : (inferInstance : TopologicalSpace (StrongDual ℂ Q)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (StrongDual ℂ Q))))
    (T : StrongDual ℂ Q →L[ℂ] StrongDual ℂ Q) (hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range :=
  archNuclearityStrongDual_finiteRank_gen h T hT

-- Stated over the same tower of quotients as `ArchNuclearityQuotient`, and concluding `FG`,
-- so that applying it to the concrete space needs only syntactic unification (#5398).
private theorem archNuclearityStrongDual_finiteRank_tower {X : Type*} {_ : AddCommGroup X}
    {_ : Module ℂ X} {_ : TopologicalSpace X} [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    (P0 : Submodule ℂ X) (k : Submodule ℂ P0) (p : Submodule ℂ (P0 ⧸ k))
    (h : let E := StrongDual ℂ ((P0 ⧸ k) ⧸ p)
      (inferInstance : TopologicalSpace E) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex E)))
    (T : StrongDual ℂ ((P0 ⧸ k) ⧸ p) →L[ℂ] StrongDual ℂ ((P0 ⧸ k) ⧸ p))
    (hT : Nonempty (NuclearPresentation T)) :
    (LinearMap.range T.toLinearMap).FG :=
  Module.Finite.iff_fg.mp (archNuclearityStrongDual_finiteRank_dual h T hT)

private theorem archNuclearityStrongDual_finiteRank_fd {E : Type*} {_ : AddCommGroup E}
    {_ : Module ℂ E} {S : Submodule ℂ E} (h : S.FG) : FiniteDimensional ℂ S :=
  Module.Finite.iff_fg.mpr h

/-- Paper: Remark 7.4.3.3, p. 373.
Nuclear endomorphisms of the strong dual of the archimedean quotient have finite rank.
Deviation: The printed universal nonnuclearity conclusion needs infinite rank,
which fails for the zero test. -/
theorem archNuclearityStrongDual_finiteRank
    (T : StrongDual ℂ (ArchNuclearityQuotient χ) →L[ℂ] StrongDual ℂ (ArchNuclearityQuotient χ))
    (_hT : Nonempty (NuclearPresentation T)) :
    FiniteDimensional ℂ T.toLinearMap.range :=
  archNuclearityStrongDual_finiteRank_fd
    (archNuclearityStrongDual_finiteRank_tower _ _ _ (archNuclearityStrongDual_finest χ) T _hT)

/-- An equicontinuous family of linear functionals on a sequence space sees only
a common finite set of coordinates. Otherwise rescaled tails tend to zero while
some member of the family still takes the value one. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_tail {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (e : E ≃L[ℂ] (ℕ → ℂ))
    (φ : ℕ → StrongDual ℂ E) (hφ : EquicontinuousAt (fun k x ↦ φ k x) 0) :
    ∃ N : ℕ, ∀ x : E, (∀ j < N, e x j = 0) → ∀ k, φ k x = 0 := by
  by_contra! h
  choose x hx k hk using h
  let y (n : ℕ) : E := (φ (k n) (x n))⁻¹ • x n
  have he : Filter.Tendsto (fun n ↦ e (y n)) Filter.atTop (𝓝 0) := by
    apply tendsto_pi_nhds.mpr
    intro j
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop j] with n hn
    simp [y, hx n j hn]
  have hy : Filter.Tendsto y Filter.atTop (𝓝 0) := by
    simpa only [Function.comp_def, e.symm_apply_apply, map_zero] using
      (e.symm.continuous.tendsto 0).comp he
  obtain ⟨n, hn⟩ := (hy.eventually (Metric.equicontinuousAt_iff_right.mp hφ 1 one_pos)).exists
  simpa [y, hk n, dist_zero_left] using hn (k n)

/-- A nuclear presentation factors through the finite coordinates detected by its
equicontinuous functionals. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_range {E : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E] [T2Space E]
    [ContinuousSMul ℂ E] (e : E ≃L[ℂ] (ℕ → ℂ)) (T : E →L[ℂ] E) (r : NuclearPresentation T) :
    FiniteDimensional ℂ T.toLinearMap.range := by
  obtain ⟨N, hN⟩ := archNuclearityQuotient_nuclear_iff_finiteRank_tail e r.functional r.equicontinuous
  let a : E →ₗ[ℂ] (Fin N → ℂ) := LinearMap.pi fun j ↦ (LinearMap.proj j.val).comp e.toLinearMap
  have hker : a.ker ≤ T.toLinearMap.ker := by
    intro x hx
    have hφ := hN x fun j hj ↦ congrFun (LinearMap.mem_ker.mp hx) ⟨j, hj⟩
    have hsum := r.hasSum x
    simp only [hφ, mul_zero, zero_smul] at hsum
    exact hsum.unique hasSum_zero
  let : FiniteDimensional ℂ (E ⧸ a.ker) :=
    FiniteDimensional.of_injective a.quotKerEquivRange.toLinearMap a.quotKerEquivRange.injective
  apply FiniteDimensional.of_surjective (a.ker.liftQ T.toLinearMap.rangeRestrict
    (by rwa [LinearMap.ker_rangeRestrict]))
  rw [← LinearMap.range_eq_top, Submodule.range_liftQ, LinearMap.range_rangeRestrict]

/-- A map to finitely many complex coordinates has a finite nuclear presentation,
using the coordinate vectors in the closed unit ball. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_coordinates {E : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] {d : ℕ} (A : E →L[ℂ] (Fin d → ℂ)) :
    IsNuclearOperator A := by
  classical
  let ball := Metric.closedBall (0 : Fin d → ℂ) 1
  let b (i : Fin d) : Fin d → ℂ := Pi.single i 1
  have hb (i : Fin d) : b i ∈ ball := by simp [ball, b, Metric.mem_closedBall, Pi.norm_single]
  have hz : (0 : Fin d → ℂ) ∈ ball := by simp [ball]
  let c (n : ℕ) : ℂ := if n < d then 1 else 0
  have hc (n : ℕ) (hn : n ∉ Finset.range d) : c n = 0 := ite_eq_right (fun h ↦ hn (Finset.mem_range.mpr h))
  let φ : Option (Fin d) → StrongDual ℂ E := fun i ↦
    i.elim 0 (fun j ↦ (ContinuousLinearMap.proj j).comp A)
  let idx (n : ℕ) : Option (Fin d) := if hn : n < d then some ⟨n, hn⟩ else none
  let y (n : ℕ) : Fin d → ℂ := if hn : n < d then b ⟨n, hn⟩ else 0
  have hy (n : ℕ) : y n ∈ ball := by
    by_cases hn : n < d
    · simpa only [y, dite_eq_left hn] using hb ⟨n, hn⟩
    · simpa only [y, dite_eq_right hn] using hz
  apply (isNuclearOperator_iff_nonempty_presentation A).mpr
  refine ⟨⟨c, fun n ↦ φ (idx n), ball, isBanachDisc_closedUnitBall,
    fun n ↦ ⟨y n, Submodule.subset_span (hy n)⟩, hy, ?_, ?_, fun x ↦ ?_⟩⟩
  · exact (hasSum_sum_of_ne_finset_zero (s := Finset.range d) fun n hn ↦ by
      simp only [hc n hn, norm_zero]).summable
  · exact (equicontinuousAt_finite.mpr (fun i ↦ (φ i).continuous.continuousAt)).comp idx
  · let term (n : ℕ) := (c n * φ (idx n) x) • y n
    have hsum : ∑ n ∈ Finset.range d, term n = A x := by
      rw [← Fin.sum_univ_eq_sum_range term]
      ext j
      simp [term, c, φ, idx, y, b, Pi.single_apply, Finset.sum_apply]
    change HasSum term (A x)
    rw [← hsum]
    exact hasSum_sum_of_ne_finset_zero fun n hn ↦ by simp only [term, hc n hn, zero_mul, zero_smul]

/-- Factor a finite-rank map through coordinates on its range and then include the
range back into the ambient space. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_of_finite {E : Type*}
    [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [PolynormableSpace ℂ E] [T2Space E] (T : E →L[ℂ] E) (hf : FiniteDimensional ℂ T.toLinearMap.range) :
    Nonempty (NuclearPresentation T) := by
  let b := (Module.finBasis ℂ T.toLinearMap.range).equivFun.toContinuousLinearEquiv
  let A := b.toContinuousLinearMap.comp T.rangeRestrict
  let i := T.toLinearMap.range.subtypeL.comp b.symm.toContinuousLinearMap
  have h := (isNuclearOperator_factor_comps i (Subtype.val_injective.comp b.symm.injective) A
    (archNuclearityQuotient_nuclear_iff_finiteRank_coordinates A)).2
  have he : i.comp A = T := by ext x; exact congrArg Subtype.val (b.symm_apply_apply (T.rangeRestrict x))
  exact (isNuclearOperator_iff_nonempty_presentation T).mp (he ▸ h)

/-- Apply the sequence-space rank criterion with the uniformity of the given
topological additive group. -/
private theorem archNuclearityQuotient_nuclear_iff_finiteRank_sequence {E : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] (e : E ≃L[ℂ] (ℕ → ℂ)) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    ∀ T : E →L[ℂ] E, Nonempty (NuclearPresentation T) ↔
      FiniteDimensional ℂ T.toLinearMap.range := by
  let : UniformSpace E := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  let : T2Space E := e.symm.toHomeomorph.t2Space
  let : PolynormableSpace ℂ E := e.PolynormableSpace
  intro T
  exact ⟨fun ⟨r⟩ ↦ archNuclearityQuotient_nuclear_iff_finiteRank_range e T r,
    archNuclearityQuotient_nuclear_iff_finiteRank_of_finite T⟩

/-- Paper: Remark 7.4.3.3, p. 373.
A nuclear endomorphism of the archimedean quotient has finite-dimensional range,
and every continuous finite-rank endomorphism admits a nuclear presentation.
Deviation: This gives the rank criterion on the space carrying the test action. -/
theorem archNuclearityQuotient_nuclear_iff_finiteRank :
    let Q := ArchNuclearityQuotient χ
    letI instArchUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    ∀ T : Q →L[ℂ] Q, Nonempty (NuclearPresentation T) ↔
      FiniteDimensional ℂ T.toLinearMap.range := by
  obtain ⟨e⟩ := archNuclearityStrongDual_finest_sequenceEquiv χ
  exact archNuclearityQuotient_nuclear_iff_finiteRank_sequence (E := ArchNuclearityQuotient χ) e

/-- In block coordinates, an operator acting on each block by a lower-triangular
Toeplitz matrix with entries `d i z` has values zero on the blocks where all those
entries vanish. -/
private theorem archNuclearityAction_nuclear_iff_vanish {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] (m : ℂ → ℕ) (d : ℕ → ℂ → ℂ)
    (e : Q ≃ₗ[ℂ] ({j : ℂ × ℕ // j.2 < m j.1} → ℂ)) (T : Q →ₗ[ℂ] Q)
    (hT : ∀ q (j : {j : ℂ × ℕ // j.2 < m j.1}), e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
      (j.val.2.choose i : ℂ) * d i j.val.1 *
        e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩)
    (q : Q) (j : {j : ℂ × ℕ // j.2 < m j.1})
    (hj : j.val.1 ∉ {z : ℂ | ∃ k : Fin (m z), d k.val z ≠ 0}) :
    e (T q) j = 0 := by
  rw [hT]
  refine Finset.sum_eq_zero fun i hi ↦ ?_
  have hi' : i < m j.val.1 :=
    (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans_lt j.property
  have h0 : d i j.val.1 = 0 := by
    by_contra h
    exact hj ⟨⟨i, hi'⟩, h⟩
  rw [h0, mul_zero, zero_mul]

/-- Applying the operator to the first basis vector of the block at `z` gives the
column of entries `d k z` in that block, and zero in the other blocks. -/
private theorem archNuclearityAction_nuclear_iff_column {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] (m : ℂ → ℕ) (d : ℕ → ℂ → ℂ)
    (e : Q ≃ₗ[ℂ] ({j : ℂ × ℕ // j.2 < m j.1} → ℂ)) (T : Q →ₗ[ℂ] Q)
    (hT : ∀ q (j : {j : ℂ × ℕ // j.2 < m j.1}), e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
      (j.val.2.choose i : ℂ) * d i j.val.1 *
        e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩)
    (z : ℂ) (hz : 0 < m z) (j : {j : ℂ × ℕ // j.2 < m j.1}) :
    e (T (e.symm (Pi.single ⟨(z, 0), hz⟩ 1))) j = if j.val.1 = z then d j.val.2 z else 0 := by
  classical
  rw [hT]
  simp only [LinearEquiv.apply_symm_apply]
  split_ifs with hjz
  · rw [Finset.sum_eq_single j.val.2]
    · have : (⟨(j.val.1, j.val.2 - j.val.2), (Nat.sub_le _ _).trans_lt j.property⟩ :
          {j : ℂ × ℕ // j.2 < m j.1}) = ⟨(z, 0), hz⟩ := Subtype.ext (by simp [hjz])
      rw [this, Pi.single_eq_same, mul_one, Nat.choose_self, Nat.cast_one, one_mul, hjz]
    · intro i hi hne
      have hlt : i < j.val.2 :=
        lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
      rw [Pi.single_eq_of_ne, mul_zero]
      intro h
      have := congrArg (fun x : {j : ℂ × ℕ // j.2 < m j.1} ↦ x.val.2) h
      simp only at this
      omega
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h
  · refine Finset.sum_eq_zero fun i _ ↦ ?_
    rw [Pi.single_eq_of_ne, mul_zero]
    intro h
    exact hjz (congrArg (fun x : {j : ℂ × ℕ // j.2 < m j.1} ↦ x.val.1) h)

/-- Linear-algebra core of Remark 7.4.3.3: a block lower-triangular operator on the
product of the jet blocks has finite rank exactly when only finitely many blocks
carry a nonzero entry. -/
private theorem archNuclearityAction_nuclear_iff_blocks {Q : Type*} [AddCommGroup Q]
    [Module ℂ Q] (m : ℂ → ℕ) (d : ℕ → ℂ → ℂ)
    (e : Q ≃ₗ[ℂ] ({j : ℂ × ℕ // j.2 < m j.1} → ℂ)) (T : Q →ₗ[ℂ] Q)
    (hT : ∀ q (j : {j : ℂ × ℕ // j.2 < m j.1}), e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
      (j.val.2.choose i : ℂ) * d i j.val.1 *
        e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩) :
    FiniteDimensional ℂ (LinearMap.range T) ↔
      {z : ℂ | ∃ k : Fin (m z), d k.val z ≠ 0}.Finite := by
  classical
  let J := {j : ℂ × ℕ // j.2 < m j.1}
  let Z := {z : ℂ | ∃ k : Fin (m z), d k.val z ≠ 0}
  constructor
  · intro hfin
    choose k hk using fun z : Z ↦ z.property
    have hpos (z : Z) : 0 < m z.val := (Nat.zero_le _).trans_lt (k z).isLt
    let w (z : Z) : LinearMap.range T :=
      ⟨T (e.symm (Pi.single ⟨(z.val, 0), hpos z⟩ 1)), LinearMap.mem_range_self _ _⟩
    let Φ : (J → ℂ) →ₗ[ℂ] (Z → ℂ) :=
      LinearMap.pi fun z ↦ LinearMap.proj (⟨(z.val, (k z).val), (k z).isLt⟩ : J)
    let L : LinearMap.range T →ₗ[ℂ] (Z → ℂ) :=
      Φ.comp (e.toLinearMap.comp (LinearMap.range T).subtype)
    have hL (z : Z) : L (w z) = Pi.single z (d (k z).val z.val) := by
      funext z'
      change e (T (e.symm (Pi.single ⟨(z.val, 0), hpos z⟩ 1)))
        ⟨(z'.val, (k z').val), (k z').isLt⟩ = _
      rw [archNuclearityAction_nuclear_iff_column m d e T hT z.val (hpos z)]
      by_cases h : z' = z
      · subst h
        simp
      · have h' : z'.val ≠ z.val := fun he ↦ h (Subtype.ext he)
        simp [h', Pi.single_eq_of_ne h]
    have hli : LinearIndependent ℂ (L ∘ w) := by
      have : L ∘ w = fun z ↦ Pi.single z (d (k z).val z.val) := funext hL
      rw [this]
      exact Pi.linearIndependent_single_of_ne_zero hk
    have := (LinearIndependent.of_comp L hli).finite_of_isNoetherian
    exact Set.toFinite Z
  · intro hZ
    have : Finite Z := hZ.to_subtype
    let JZ := {j : J // j.val.1 ∈ Z}
    have : Finite JZ := by
      refine Finite.of_injective (β := Σ z : Z, Fin (m z.val))
        (fun j ↦ ⟨⟨j.val.val.1, j.property⟩, ⟨j.val.val.2, j.val.property⟩⟩) ?_
      intro a b h
      simp only [Sigma.mk.inj_iff] at h
      obtain ⟨h1, h2⟩ := h
      have h1' : a.val.val.1 = b.val.val.1 := congrArg Subtype.val h1
      apply Subtype.ext
      apply Subtype.ext
      refine Prod.ext h1' ?_
      have := (Fin.heq_ext_iff (by rw [h1'])).mp h2
      exact this
    let R : LinearMap.range T →ₗ[ℂ] (JZ → ℂ) :=
      (LinearMap.pi fun j : JZ ↦ LinearMap.proj (R := ℂ) (φ := fun _ : J ↦ ℂ) j.val).comp
        (e.toLinearMap.comp (LinearMap.range T).subtype)
    refine Module.Finite.of_injective R ?_
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨_, q, rfl⟩ hx
    apply Subtype.ext
    change T q = 0
    apply e.injective
    funext j
    rw [map_zero, Pi.zero_apply]
    by_cases hj : j.val.1 ∈ Z
    · exact congrFun hx ⟨j, hj⟩
    · exact archNuclearityAction_nuclear_iff_vanish m d e T hT q j hj

/-- Paper: Remark 7.4.3.3, p. 373.
The quotient action is nuclear exactly when it is nonzero on finitely many jet blocks.
Deviation: A block of length m vanishes when all multiplier derivatives of orders
strictly below m vanish at its center. This allows tests whose induced action is zero. -/
theorem archNuclearityAction_nuclear_iff (φ : 𝒟) :
    let D := archNuclearityDenominator χ
    let Q := ArchNuclearityQuotient χ
    letI instArchActionUniformSec4 : UniformSpace Q := IsTopologicalAddGroup.rightUniformSpace Q
    ∀ T : Q →L[ℂ] Q, (∀ x : Θ₀(χ), T (D.mkQ x) = D.mkQ (Aθ(φ) x)) →
      (Nonempty (NuclearPresentation T) ↔
        {z : ℂ | ∃ k : Fin (archNuclearityMultiplicity χ τ hτ z),
          iteratedDeriv k.val (nuclearityTestMellin χ φ) z ≠ 0}.Finite) := by
  intro D Q T hT
  obtain ⟨e, he⟩ := archNuclearityQuotient_jetEquiv χ τ hτ
  have hjet (x : Θ₀(χ)) (j : ArchNuclearityJetIndex χ τ hτ) :
      archNuclearityJet χ τ hτ j x = iteratedDeriv j.val.2 ((Z(χ, τ, hτ)) x).val j.val.1 := by
    unfold archNuclearityJet
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, entireJet_apply]
    exact congrArg (fun g : ℂ → ℂ ↦ iteratedDeriv j.val.2 g j.val.1)
      (funext (schwartzBergmanEntireInclusion_apply _))
  have hblock (q : Q) (j : ArchNuclearityJetIndex χ τ hτ) :
      e (T q) j = ∑ i ∈ Finset.range (j.val.2 + 1),
        (j.val.2.choose i : ℂ) * iteratedDeriv i (nuclearityTestMellin χ φ) j.val.1 *
          e q ⟨(j.val.1, j.val.2 - i), (Nat.sub_le _ _).trans_lt j.property⟩ := by
    obtain ⟨x, rfl⟩ := D.mkQ_surjective q
    let v := (Z(χ, τ, hτ)) x
    have hv : Differentiable ℂ v.val := fun z ↦
      (v.property.2.1 z (mem_univ _)).differentiableAt (Filter.univ_mem' fun _ ↦ mem_univ _)
    have hprod : ((Z(χ, τ, hτ)) (Aθ(φ) x)).val = nuclearityTestMellin χ φ * v.val :=
      funext ((exists_polarThetaNuclearityAction χ τ hτ φ).choose_spec.1 x)
    rw [hT x, he, hjet, hprod, iteratedDeriv_mul
      ((archNuclearityDenominator_closed_invariant_multiplier χ φ).contDiff.contDiffAt)
      hv.contDiff.contDiffAt]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [he, hjet]
  rw [archNuclearityQuotient_nuclear_iff_finiteRank χ T]
  exact archNuclearityAction_nuclear_iff_blocks (archNuclearityMultiplicity χ τ hτ)
    (fun i z ↦ iteratedDeriv i (nuclearityTestMellin χ φ) z) e.toLinearEquiv T.toLinearMap hblock

end Archimedean

end RiemannMasullo
