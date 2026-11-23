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

section FlatPolarImage

local notation "Coord" =>
  ({v : InfinitePlace F // v.IsReal} → ℝ) × ({v : InfinitePlace F // v.IsComplex} → ℂ)
local notation "Flat" =>
  archimedeanFlatSchwartz (ι := {v : InfinitePlace F // v.IsReal}) (κ := {v : InfinitePlace F // v.IsComplex})
local notation "coord" => InfiniteAdeleRing.ringEquiv_mixedSpace F

/-- The archimedean Schwartz functions with flat coordinate realizations. -/
private def archNuclearity_flatFactors : Submodule ℂ ℬ(InfiniteAdeleRing F) where
  carrier := {a | ∃ h : Flat, ∀ x : InfiniteAdeleRing F, a (Multiplicative.ofAdd x) = h.val (coord x)}
  zero_mem' := ⟨0, fun _ ↦ rfl⟩
  add_mem' := by
    rintro a b ⟨h, hh⟩ ⟨k, hk⟩
    refine ⟨h + k, fun x ↦ ?_⟩
    exact congrArg₂ (· + ·) (hh x) (hk x)
  smul_mem' := by
    rintro r a ⟨h, hh⟩
    exact ⟨r • h, fun x ↦ congrArg (r • ·) (hh x)⟩

/-- Coordinatewise multiplication by units preserves every archimedean wall
and hence also the vanishing of every jet along those walls. -/
private theorem archNuclearity_flatFactors_translate (u : (InfiniteAdeleRing F)ˣ)
    (a : ℬ(InfiniteAdeleRing F)) (ha : a ∈ archNuclearity_flatFactors) :
    schwartzBruhatUnitTranslate u a ∈ archNuclearity_flatFactors := by
  obtain ⟨h, hh⟩ := ha
  let d := Units.map (coord).toMonoidHom u⁻¹
  let L₀ : Coord ≃ₗ[ℝ] Coord :=
    { LinearMap.mulLeft ℝ (d : Coord) with
      invFun := fun x ↦ (↑d⁻¹ : Coord) * x
      left_inv := fun x ↦ by
        change (↑d⁻¹ : Coord) * ((d : Coord) * x) = x
        rw [← mul_assoc, Units.inv_mul, one_mul]
      right_inv := fun x ↦ by
        change (d : Coord) * ((↑d⁻¹ : Coord) * x) = x
        rw [← mul_assoc, Units.mul_inv, one_mul] }
  let L := L₀.toContinuousLinearEquiv
  let k := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L h.val
  have hk : k ∈ Flat := by
    have hf := h.property
    simp only [archimedeanFlatSchwartz, Submodule.mem_iInf, LinearMap.mem_ker, IsLinearMap.mk'_apply] at hf ⊢
    rintro ⟨x, hx⟩ n v
    have hx' : (∃ i, (L x).1 i = 0) ∨ ∃ j, (L x).2 j = 0 := by
      rcases hx with ⟨i, hi⟩ | ⟨j, hj⟩
      · exact Or.inl ⟨i, by change (d : Coord).1 i * x.1 i = 0; rw [hi, mul_zero]⟩
      · exact Or.inr ⟨j, by change (d : Coord).2 j * x.2 j = 0; rw [hj, mul_zero]⟩
    change iteratedFDeriv ℝ n ((h.val : Coord → ℂ) ∘ L) x v = 0
    erw [L.toContinuousLinearMap.iteratedFDeriv_comp_right (h.val.smooth ⊤) x (i := n)
      (mod_cast le_top)]
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
    exact hf ⟨L x, hx'⟩ n (fun i ↦ L (v i))
  refine ⟨⟨k, hk⟩, fun x ↦ ?_⟩
  rw [schwartzBruhatUnitTranslate_apply, hh]
  change h.val (coord ((↑u⁻¹ : InfiniteAdeleRing F) * x)) = h.val ((d : Coord) * coord x)
  rw [map_mul]
  rfl


/-- Once finite mass-zero factors may be discarded modulo a submodule, the total
moment of a flat tensor sum can be imposed on one archimedean representative. -/
private theorem tensor_mem_flat_moment_sup
    {E W X : Type*} [AddCommGroup E] [AddCommGroup W] [AddCommGroup X]
    [Module ℂ E] [Module ℂ W] [Module ℂ X]
    (e : E ⊗[ℂ] W →ₗ[ℂ] X) (Uflat : Submodule ℂ E) (A K : Submodule ℂ X)
    (i : E →ₗ[ℂ] ℂ) (j : W →ₗ[ℂ] ℂ) (L : X →ₗ[ℂ] ℂ)
    (b₀ : W) (hb₀ : j b₀ = 1)
    (hL : ∀ a b, L (e (a ⊗ₜ[ℂ] b)) = i a * j b)
    (hA : ∀ a ∈ Uflat, i a = 0 → ∀ b, e (a ⊗ₜ[ℂ] b) ∈ A)
    (hK : ∀ a ∈ Uflat, ∀ b, j b = 0 → e (a ⊗ₜ[ℂ] b) ∈ A ⊔ K)
    {x : X} (hx : x ∈ Submodule.span ℂ {v | ∃ a ∈ Uflat, ∃ b, e (a ⊗ₜ[ℂ] b) = v})
    (hx₀ : L x = 0) : x ∈ A ⊔ K := by
  let u : E →ₗ[ℂ] X := e.comp ((TensorProduct.mk ℂ E W).flip b₀)
  have hu (a : E) : u a = e (a ⊗ₜ[ℂ] b₀) := rfl
  have H (x : X) (hx : x ∈ Submodule.span ℂ {v | ∃ a ∈ Uflat, ∃ b, e (a ⊗ₜ[ℂ] b) = v}) :
      ∃ a ∈ Uflat, i a = L x ∧ x - u a ∈ A ⊔ K := by
    refine Submodule.span_induction (p := fun x _ ↦ ∃ a ∈ Uflat, i a = L x ∧ x - u a ∈ A ⊔ K)
      ?_ ?_ ?_ ?_ hx
    · rintro _ ⟨a, ha, b, rfl⟩
      refine ⟨j b • a, Uflat.smul_mem _ ha, ?_, ?_⟩
      · rw [map_smul, smul_eq_mul, hL, mul_comm]
      · have hj : j (b - j b • b₀) = 0 := by
          rw [map_sub, map_smul, hb₀, smul_eq_mul, mul_one, sub_self]
        have h := hK a ha (b - j b • b₀) hj
        simpa only [TensorProduct.tmul_sub, TensorProduct.tmul_smul, TensorProduct.smul_tmul', map_sub, hu] using h
    · exact ⟨0, Uflat.zero_mem, by rw [map_zero, map_zero], by simp⟩
    · rintro x y _ _ ⟨a, ha, hia, hxa⟩ ⟨b, hb, hib, hyb⟩
      refine ⟨a + b, Uflat.add_mem ha hb, by rw [map_add, map_add, hia, hib], ?_⟩
      rw [map_add, add_sub_add_comm]
      exact Submodule.add_mem _ hxa hyb
    · rintro c x _ ⟨a, ha, hia, hxa⟩
      refine ⟨c • a, Uflat.smul_mem c ha, by rw [map_smul, map_smul, hia], ?_⟩
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ c hxa
  obtain ⟨a, ha, hi, he⟩ := H x hx
  have haux : u a ∈ A ⊔ K := (show A ≤ A ⊔ K from le_sup_left) (hA a ha (hi.trans hx₀) b₀)
  have hsum := Submodule.add_mem _ he haux
  rwa [sub_add_cancel] at hsum


local notation "Aflat" => archNuclearity_flatFactors (F := F)
local notation "A₀(" χ ")" => globalArchimedeanFlatTests F (ω(χ) = 1)
local notation "A" => globalArchimedeanFlatTests F
local notation "K(" χ ")" => (homogeneousAdelicThetaLinearMap F (ω(χ))).ker
local notation "ArchTests" => ℬ(InfiniteAdeleRing F)
local notation "FiniteTests" => ℬ(FiniteAdeleRing (𝓞 F) F)
local notation "tensor" => (adeleSchwartz_inductiveTensor_equiv F).choose
local notation "hatL" => (ContinuousLinearMap.snd ℂ ℂ ℂ).toLinearMap.comp
  ((adelePolarValues_isLinear (F := F)).mk' adelePolarValues)

private theorem archNuclearityDenominator_mem_restricted
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (x : Θ₀(χ)) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ A₀(χ) ∧ x = mkΘ(χ, f) := by
  let D : Submodule ℂ P := (A₀(χ)).comap (P).subtype
  let q : P →ₗ[ℂ] Θ₀(χ) := (Π(χ)).mkQ
  have hEq : archNuclearityDenominator χ = D.map q := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨f, hf, rfl⟩
      exact ⟨f, hf, rfl⟩
    · rintro _ ⟨f, hf, rfl⟩
      exact Submodule.subset_span ⟨f, hf, rfl⟩
  rw [hEq]
  exact exists_congr fun f ↦ and_congr_right fun _ ↦ eq_comm

private theorem archNuclearity_flatTests_mono {Q R : Prop} (h : Q → R) :
    globalArchimedeanFlatTests F R ≤ globalArchimedeanFlatTests F Q := by
  apply Submodule.span_mono
  rintro _ ⟨a, b, f, hf, hR, rfl⟩
  exact ⟨a, b, f, hf, hR ∘ h, rfl⟩

/-- Reduction to additive moment factorization and the vanishing of weighted finite
coinvariants modulo the restricted flat space and the theta kernel. -/
private theorem archNuclearity_of_finiteMassReduction
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (x : Θ₀(χ))
    (H : ω(χ) = 1 → ∃ (i : ArchTests →ₗ[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (b₀ : FiniteTests),
      j b₀ = 1 ∧
      (∀ a b, hatL (tensor (a ⊗ₜ[ℂ] b)) = i a * j b) ∧
      (∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
        (i a = 0 ↔ (∫ y : Coord, h.val y) = 0)) ∧
      (∀ a ∈ Aflat, ∀ b, j b = 0 → tensor (a ⊗ₜ[ℂ] b) ∈ A₀(χ) ⊔ K(χ))) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ A ∧ x = mkΘ(χ, f) := by
  rw [archNuclearityDenominator_mem_restricted]
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f, archNuclearity_flatTests_mono (False.elim : False → ω(χ) = 1) hf, rfl⟩
  · rintro ⟨f, hf, rfl⟩
    by_cases hω : ω(χ) = 1
    swap
    · exact ⟨f, archNuclearity_flatTests_mono hω hf, rfl⟩
    obtain ⟨i, j, b₀, hb, hL, hi, hK⟩ := H hω
    have hA (a : ArchTests) (ha : a ∈ Aflat) (h0 : i a = 0) (b : FiniteTests) :
        tensor (a ⊗ₜ[ℂ] b) ∈ A₀(χ) := by
      obtain ⟨h, hh⟩ := ha
      exact Submodule.subset_span ⟨a, b, h, hh, fun _ ↦ (hi a h hh).mp h0, rfl⟩
    have hspan : A ≤ Submodule.span ℂ {v | ∃ a ∈ Aflat, ∃ b, tensor (a ⊗ₜ[ℂ] b) = v} := by
      apply Submodule.span_mono
      rintro _ ⟨a, b, h, hh, _, rfl⟩
      exact ⟨a, ⟨h, hh⟩, b, rfl⟩
    have hsum := tensor_mem_flat_moment_sup (tensor).toLinearMap Aflat (A₀(χ)) (K(χ)) i j hatL b₀
      hb hL hA hK (hspan hf) ((mem_adelePolarSubspace f.val).mp f.property).2
    obtain ⟨g, hg, k, hk, hgf⟩ := Submodule.mem_sup.mp hsum
    have hg0 : g ∈ P := by
      have hgflat : g ∈ A := archNuclearity_flatTests_mono (False.elim : False → ω(χ) = 1) hg
      apply (globalArchimedeanFlatTests_zero_moments g hgflat).2.mpr
      suffices hatL g = 0 from this
      refine Submodule.span_induction (p := fun y _ ↦ hatL y = 0) ?_ ?_ ?_ ?_ hg
      · rintro _ ⟨a, b, h, hh, hM, rfl⟩
        exact (hL a b).trans (mul_eq_zero_of_left ((hi a h hh).mpr (hM hω)) _)
      · exact map_zero _
      · intro a b _ _ ha hb'
        rw [map_add, ha, hb', add_zero]
      · intro c y _ hy
        rw [map_smul, hy, smul_zero]
    refine ⟨⟨g, hg0⟩, hg, (Submodule.Quotient.eq (Π(χ))).mpr ?_⟩
    change f.val - g ∈ K(χ)
    have he : f.val - g = k := by rw [← hgf, add_comm g k, add_sub_cancel_right]
    rwa [he]

open scoped RestrictedProduct
local notation "AF" => FiniteAdeleRing (𝓞 F) F
/-- In mixed archimedean coordinates the global Fourier value at zero factors
as ordinary archimedean volume integration against a fixed finite functional. -/
private theorem archNuclearity_productMoment :
    ∃ J : FiniteTests → ℂ, ∀ (a : ℬ(InfiniteAdeleRing F)) (b : FiniteTests),
      adeleSchwartzFourier (F := F) (tensor (a ⊗ₜ[ℂ] b)) (Multiplicative.ofAdd 0) =
        (∫ y : Coord, a (Multiplicative.ofAdd ((coord).symm y))) * J b := by
  let (v : V) : CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let (v : V) : LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let : Fact (∀ v : V, IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : LocallyCompactSpace AF := inferInstanceAs
    (LocallyCompactSpace (Πʳ v : V, [v.adicCompletion F, v.adicCompletionIntegers F]))
  let : LocallyCompactSpace 𝔸[F] := inferInstanceAs
    (LocallyCompactSpace (InfiniteAdeleRing F × AF))
  let := ratAdele_secondCountable
  obtain ⟨e, _, _⟩ := exists_adeleTrace_dualCoordinates F
  let : SecondCountableTopology 𝔸[F] := e.symm.toHomeomorph.isEmbedding.secondCountableTopology
  let : SecondCountableTopology (InfiniteAdeleRing F × AF) := inferInstanceAs (SecondCountableTopology 𝔸[F])
  let : SecondCountableTopology AF :=
    (isEmbedding_prodMkRight (X := InfiniteAdeleRing F) (Y := AF) 0).secondCountableTopology
  let : IsTopologicalAddGroup AF := inferInstanceAs
    (IsTopologicalAddGroup (Πʳ v : V, [v.adicCompletion F, v.adicCompletionIntegers F]))
  let : IsTopologicalAddGroup 𝔸[F] := inferInstanceAs
    (IsTopologicalAddGroup (InfiniteAdeleRing F × AF))
  let : MeasurableSpace AF := borel _
  let : BorelSpace AF := ⟨rfl⟩
  let : MeasurableSpace 𝔸[F] := borel _
  let : BorelSpace 𝔸[F] := ⟨rfl⟩
  let d : (Coord × AF) ≃ₜ+ 𝔸[F] :=
    { toAddEquiv := (coord).symm.toAddEquiv.prodCongr (AddEquiv.refl _)
      continuous_toFun := ((continuous_infiniteAdeleRingEquivMixedSpace_symm F).comp continuous_fst).prodMk
        continuous_snd
      continuous_invFun := ((continuous_infiniteAdeleRingEquivMixedSpace F).comp continuous_fst).prodMk
        continuous_snd }
  let μf := Measure.addHaar (G := AF)
  let μ : Measure (Coord × AF) := (volume : Measure Coord).prod μf
  let : μ.IsAddHaarMeasure := Measure.prod.instIsAddHaarMeasure _ _
  let ν : Measure 𝔸[F] := μ.map d
  let : ν.IsAddHaarMeasure := d.isAddHaarMeasure_map μ
  let m := additiveTamagawaMeasure F
  let : m.IsAddHaarMeasure := (additiveTamagawaMeasure_existsUnique F).exists.choose_spec.1
  let c := m.addHaarScalarFactor ν
  have hc : m = c • ν := Measure.isAddLeftInvariant_eq_smul m ν
  refine ⟨fun b ↦ (c : ℂ) * ∫ x, b (Multiplicative.ofAdd x) ∂μf, fun a b ↦ ?_⟩
  rw [(adeleSchwartzFourier_apply_zero _).2]
  change (∫ x : 𝔸[F], tensor (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x) ∂m) = _
  rw [hc, integral_smul_nnreal_measure]
  change (c : ℂ) * ∫ x : 𝔸[F], tensor (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd x) ∂ν = _
  rw [show ν = μ.map d.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
  have h (x : Coord × AF) :
      tensor (a ⊗ₜ[ℂ] b) (Multiplicative.ofAdd (d.toHomeomorph.toMeasurableEquiv x)) =
        a (Multiplicative.ofAdd ((coord).symm x.1)) * b (Multiplicative.ofAdd x.2) :=
    (adeleSchwartz_inductiveTensor_equiv F).choose_spec a b (d x)
  simp_rw [h]
  exact (congrArg ((c : ℂ) * ·) (integral_prod_mul (μ := (volume : Measure Coord)) (ν := μf)
    (fun y ↦ a (Multiplicative.ofAdd ((coord).symm y))) (fun y ↦ b (Multiplicative.ofAdd y)))).trans
      (mul_left_comm _ _ _)

local notation "hatC" => (ContinuousLinearMap.snd ℂ ℂ ℂ).comp
  (⟨(adelePolarValues_isLinear (F := F)).mk' adelePolarValues,
    adelePolarValues_continuous⟩ : ℬ(𝔸[F]) →L[ℂ] ℂ × ℂ)

private theorem archNuclearity_nonzero_pure_moment :
    ∃ (a : ArchTests) (b : FiniteTests), hatC (tensor (a ⊗ₜ[ℂ] b)) ≠ 0 := by
  by_contra! h
  have hz : (hatC).toLinearMap.comp (tensor).toLinearMap = 0 :=
    TensorProduct.ext' fun a b ↦ h a b
  obtain ⟨f, hf⟩ := adelePolarValues_surjective (F := F) ((0, 1) : ℂ × ℂ)
  have hf' : hatC f = 1 := congrArg Prod.snd hf
  have ht := LinearMap.congr_fun hz ((tensor).symm f)
  change hatC (tensor ((tensor).symm f)) = 0 at ht
  rw [(tensor).apply_symm_apply, hf'] at ht
  exact one_ne_zero ht

private theorem archNuclearity_normalized_moment :
    ∃ (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (a₀ : ArchTests) (b₀ : FiniteTests),
      i a₀ ≠ 0 ∧ j b₀ = 1 ∧
      (∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b) ∧
      (∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
        (i a = 0 ↔ (∫ y : Coord, h.val y) = 0)) := by
  obtain ⟨a₀, b₀, hab₀⟩ := archNuclearity_nonzero_pure_moment (F := F)
  obtain ⟨rawJ, hraw⟩ := archNuclearity_productMoment (F := F)
  let rawI (a : ArchTests) := ∫ y : Coord, a (Multiplicative.ofAdd ((coord).symm y))
  have hL (a : ArchTests) (b : FiniteTests) : hatC (tensor (a ⊗ₜ[ℂ] b)) = rawI a * rawJ b := hraw a b
  have hj₀ : rawJ b₀ ≠ 0 := right_ne_zero_of_mul (fun hz ↦ hab₀ ((hL a₀ b₀).trans hz))
  have hi₀ : rawI a₀ ≠ 0 := left_ne_zero_of_mul (fun hz ↦ hab₀ ((hL a₀ b₀).trans hz))
  let T := InductiveTensor ArchTests FiniteTests
  let eb : ArchTests →ₗ[ℂ] T := (TensorProduct.mk ℂ ArchTests FiniteTests).flip b₀
  have heb : Continuous eb := by
    let h := withGeneratingSeminorms_spec (ArchTests ⊗[ℂ] FiniteTests)
      (fun p : {p : Seminorm ℂ (ArchTests ⊗[ℂ] FiniteTests) //
        (∀ a : ArchTests, Continuous (fun b : FiniteTests ↦ p (a ⊗ₜ[ℂ] b))) ∧
        (∀ b : FiniteTests, Continuous (fun a : ArchTests ↦ p (a ⊗ₜ[ℂ] b)))} ↦ p.val)
    exact h.continuous_of_continuous_comp eb fun p ↦ p.property.2 b₀
  let i : ArchTests →L[ℂ] ℂ := (hatC).comp ((tensor).toContinuousLinearMap.comp ⟨eb, heb⟩)
  let j : FiniteTests →ₗ[ℂ] ℂ := (hatC (tensor (a₀ ⊗ₜ[ℂ] b₀)))⁻¹ •
    ((hatC).toLinearMap.comp ((tensor).toLinearMap.comp (TensorProduct.mk ℂ ArchTests FiniteTests a₀)))
  have hi (a : ArchTests) : i a = rawI a * rawJ b₀ := hL a b₀
  have hj (b : FiniteTests) : j b = (rawI a₀ * rawJ b₀)⁻¹ * (rawI a₀ * rawJ b) := by
    change (hatC (tensor (a₀ ⊗ₜ[ℂ] b₀)))⁻¹ * hatC (tensor (a₀ ⊗ₜ[ℂ] b)) = _
    rw [hL, hL]
  refine ⟨i, j, a₀, b₀, hab₀, ?_, ?_, ?_⟩
  · rw [hj, inv_mul_cancel₀ (mul_ne_zero hi₀ hj₀)]
  · intro a b
    rw [hL, hi, hj]
    field_simp
  · intro a h hh
    rw [hi, mul_eq_zero, or_iff_left hj₀]
    have hh' (y : Coord) : a (Multiplicative.ofAdd ((coord).symm y)) = h.val y := by
      rw [hh, RingEquiv.apply_symm_apply]
    have hI : rawI a = ∫ y : Coord, h.val y :=
      congrArg (fun f : Coord → ℂ ↦ ∫ y, f y) (funext hh')
    rw [hI]

local notation "A∞" => InfiniteAdeleRing F
local notation "𝕀" => IdeleGroup (𝓞 F) F

private def archNuclearity_archUnit (u : A∞ˣ) : 𝕀 where
  val := (u.val, 1)
  inv := (u.inv, 1)
  val_inv := Prod.ext u.val_inv (one_mul 1)
  inv_val := Prod.ext u.inv_val (one_mul 1)

private def archNuclearity_finiteUnit (u : AFˣ) : 𝕀 where
  val := (1, u.val)
  inv := (1, u.inv)
  val_inv := Prod.ext (one_mul 1) u.val_inv
  inv_val := Prod.ext (one_mul 1) u.inv_val

private def archNuclearity_translateLinear {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (u : Rˣ) : ℬ(R) →ₗ[ℂ] ℬ(R) where
  toFun := schwartzBruhatUnitTranslate u
  map_add' := fun _ _ ↦ Subtype.ext rfl
  map_smul' := fun _ _ ↦ Subtype.ext rfl

private theorem archNuclearity_translate_pure (u : A∞ˣ) (v : AFˣ) (a : ArchTests) (b : FiniteTests) :
    schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
      (tensor (a ⊗ₜ[ℂ] b)) =
    tensor (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] schwartzBruhatUnitTranslate v b) := by
  apply Subtype.ext
  funext x
  change schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
      (tensor (a ⊗ₜ[ℂ] b)) (Multiplicative.ofAdd x.toAdd) =
    tensor (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] schwartzBruhatUnitTranslate v b)
      (Multiplicative.ofAdd x.toAdd)
  rw [schwartzBruhatUnitTranslate_apply,
    (adeleSchwartz_inductiveTensor_equiv F).choose_spec,
    (adeleSchwartz_inductiveTensor_equiv F).choose_spec,
    schwartzBruhatUnitTranslate_apply, schwartzBruhatUnitTranslate_apply]
  change a (Multiplicative.ofAdd ((1 * (↑u⁻¹ : A∞)) * x.toAdd.1)) *
    b (Multiplicative.ofAdd (((↑v⁻¹ : AF) * 1) * x.toAdd.2)) = _
  rw [mul_one, one_mul]

private theorem archNuclearity_translate_one {R : Type*} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] (a : ℬ(R)) : schwartzBruhatUnitTranslate 1 a = a := by
  apply Subtype.ext
  funext x
  change schwartzBruhatUnitTranslate 1 a (Multiplicative.ofAdd x.toAdd) = _
  rw [schwartzBruhatUnitTranslate_apply, inv_one, Units.val_one, one_mul]
  rfl

private theorem archNuclearity_unit_arch_finite (w : 𝕀) :
    ∃ u : A∞ˣ, ∃ v : AFˣ, w = archNuclearity_archUnit u * archNuclearity_finiteUnit v := by
  refine ⟨Units.map (RingHom.fst A∞ AF).toMonoidHom w,
    Units.map (RingHom.snd A∞ AF).toMonoidHom w, ?_⟩
  apply Units.ext
  exact Prod.ext (mul_one _).symm (one_mul _).symm

local notation "absValue(" u ")" => ((((ideleNorm F u).val : ℝ) : ℂ))

private theorem archNuclearity_hatC_translate (u : 𝕀) (f : ℬ(𝔸[F])) :
    hatC (schwartzBruhatUnitTranslate u f) = absValue(u) * hatC f := by
  have h := globalThetaPolarValues_snd_translate (QuotientGroup.mk u) (Submodule.Quotient.mk f)
  rw [(existsUnique_globalThetaAction (F := F)).exists.choose_spec.2 u f] at h
  exact h

private theorem archNuclearity_moment_arch_translate (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ)
    (b₀ : FiniteTests) (hb : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (u : A∞ˣ) (a : ArchTests) :
    i (schwartzBruhatUnitTranslate u a) = absValue(archNuclearity_archUnit u) * i a := by
  have h := archNuclearity_hatC_translate
    (archNuclearity_archUnit u * archNuclearity_finiteUnit (F := F) 1) (tensor (a ⊗ₜ[ℂ] b₀))
  rw [archNuclearity_translate_pure, archNuclearity_translate_one, hL, hL, hb, mul_one, mul_one,
    show archNuclearity_finiteUnit (F := F) 1 = 1 from Units.ext rfl, mul_one] at h
  exact h

private theorem archNuclearity_moment_finite_translate (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ)
    (a₀ : ArchTests) (ha : i a₀ ≠ 0) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (v : AFˣ) (b : FiniteTests) :
    j (schwartzBruhatUnitTranslate v b) = absValue(archNuclearity_finiteUnit v) * j b := by
  have h := archNuclearity_hatC_translate
    (archNuclearity_archUnit (F := F) 1 * archNuclearity_finiteUnit v) (tensor (a₀ ⊗ₜ[ℂ] b))
  rw [archNuclearity_translate_pure, archNuclearity_translate_one, hL, hL,
    show archNuclearity_archUnit (F := F) 1 = 1 from Units.ext rfl, one_mul,
    mul_left_comm] at h
  exact mul_left_cancel₀ ha h

private theorem archNuclearity_translate_mul (u v : 𝕀) (f : ℬ(𝔸[F])) :
    schwartzBruhatUnitTranslate u (schwartzBruhatUnitTranslate v f) =
    schwartzBruhatUnitTranslate (u * v) f := by
  apply Subtype.ext
  funext x
  change f (Multiplicative.ofAdd (v.inv * (u.inv * x.toAdd))) =
    f (Multiplicative.ofAdd ((u * v).inv * x.toAdd))
  exact congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (mul_assoc v.inv u.inv x.toAdd).symm

private theorem archNuclearity_archLift (v : AFˣ) :
    ∃ u : A∞ˣ, ideleNorm F (archNuclearity_archUnit u) = ideleNorm F (archNuclearity_finiteUnit v) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let t := ideleNorm F (archNuclearity_finiteUnit v)
  let g := singlePlaceIdeleNormSection F w t
  let u := Units.map (RingHom.fst A∞ AF).toMonoidHom g
  have hu : archNuclearity_archUnit u = g := Units.ext (Prod.ext rfl rfl)
  exact ⟨u, hu ▸ singlePlaceIdeleNormSection_rightInverse F w t⟩

private theorem archNuclearity_theta_translate_sameNorm
    (χ : PontryaginDual C𝔽) (hω : ω(χ) = 1) (u v : 𝕀) (h : ideleNorm F u = ideleNorm F v)
    (f : ℬ(𝔸[F])) :
    homogeneousAdelicThetaLinearMap F (ω(χ)) (schwartzBruhatUnitTranslate u f) =
    homogeneousAdelicThetaLinearMap F (ω(χ)) (schwartzBruhatUnitTranslate v f) := by
  let g := u * v⁻¹
  have hg : ideleNorm F g = 1 := by
    change ideleNorm F (u * v⁻¹) = _
    rw [map_mul, map_inv, h, mul_inv_cancel]
  let k : (ideleClassNorm F).ker :=
    ⟨QuotientGroup.mk g, MonoidHom.mem_ker.mpr (show ideleNorm F g = 1 from hg)⟩
  have he := globalConverse_nontrivial_exact_theta_translate (ω(χ)) k g rfl
    (schwartzBruhatUnitTranslate v f)
  have hw : (ω(χ) k : ℂ) = 1 :=
    (congrArg (fun χ' : PontryaginDual (ideleClassNorm F).ker ↦ (χ' k : ℂ)) hω).trans rfl
  let M := homogeneousAdelicThetaLinearMap F (ω(χ))
  have htrans : schwartzBruhatUnitTranslate g (schwartzBruhatUnitTranslate v f) =
      schwartzBruhatUnitTranslate u f :=
    (archNuclearity_translate_mul g v f).trans
      (congrArg (fun s : 𝕀 ↦ schwartzBruhatUnitTranslate s f) (inv_mul_cancel_right u v))
  exact ((congrArg M htrans).symm.trans he).trans
    ((congrArg (fun c : ℂ ↦ c • M (schwartzBruhatUnitTranslate v f)) hw).trans (one_smul _ _))

/-- A finite eigendistribution of additive weight extends by tensoring with the
archimedean moment. Global rank one then determines it uniquely. -/
private theorem archNuclearity_finiteEigen_unique
    (hcont : ∀ L : FiniteTests →ₗ[ℂ] ℂ, Continuous L)
    (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (a₀ : ArchTests) (b₀ : FiniteTests)
    (ha : i a₀ ≠ 0) (hb : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (L : FiniteTests →ₗ[ℂ] ℂ)
    (hLcov : ∀ (u : AFˣ) b, L (schwartzBruhatUnitTranslate u b) = absValue(archNuclearity_finiteUnit u) * L b) :
    ∃ c : ℂ, L = c • j := by
  let T := InductiveTensor ArchTests FiniteTests
  let Q : T →ₗ[ℂ] ℂ := (LinearMap.mul' ℂ ℂ).comp (TensorProduct.map i.toLinearMap L)
  have hQ (a : ArchTests) (b : FiniteTests) : Q (a ⊗ₜ[ℂ] b) = i a * L b := by
    change (LinearMap.mul' ℂ ℂ) (TensorProduct.map i.toLinearMap L (a ⊗ₜ[ℂ] b)) = _
    rw [TensorProduct.map_tmul, LinearMap.mul'_apply]
    rfl
  have hcQ : Continuous Q := by
    let hS := withGeneratingSeminorms_spec (ArchTests ⊗[ℂ] FiniteTests)
      (fun p : {p : Seminorm ℂ (ArchTests ⊗[ℂ] FiniteTests) //
        (∀ a : ArchTests, Continuous (fun b : FiniteTests ↦ p (a ⊗ₜ[ℂ] b))) ∧
        (∀ b : FiniteTests, Continuous (fun a : ArchTests ↦ p (a ⊗ₜ[ℂ] b)))} ↦ p.val)
    refine (PolynormableSpace.withSeminorms ℂ ℂ).continuous_of_continuous_comp Q fun q ↦ ?_
    refine hS.continuous_seminorm ⟨q.val.comp Q, fun a ↦ q.property.comp ?_, fun b ↦ q.property.comp ?_⟩
    · exact (continuous_const.mul (hcont L)).congr fun b ↦ (hQ a b).symm
    · exact (i.continuous.mul continuous_const).congr fun a ↦ (hQ a b).symm
  let D : StrongDual ℂ ℬ(𝔸[F]) := (⟨Q, hcQ⟩ : T →L[ℂ] ℂ).comp (tensor).symm.toContinuousLinearMap
  have hD (a : ArchTests) (b : FiniteTests) : D (tensor (a ⊗ₜ[ℂ] b)) = i a * L b :=
    (congrArg Q ((tensor).symm_apply_apply (a ⊗ₜ[ℂ] b))).trans (hQ a b)
  let c := ideleClassNormTwist (1 : U) 1
  have hDcov (w : 𝕀) (f : ℬ(𝔸[F])) :
      D (schwartzBruhatUnitTranslate w f) = absValue(w) * D f := by
    obtain ⟨u, v, rfl⟩ := archNuclearity_unit_arch_finite w
    let w := archNuclearity_archUnit u * archNuclearity_finiteUnit v
    let L₁ := (D.toLinearMap.comp (archNuclearity_translateLinear w)).comp (tensor).toLinearMap
    let L₂ := absValue(w) • D.toLinearMap.comp (tensor).toLinearMap
    have he : L₁ = L₂ := by
      refine TensorProduct.ext' fun a b ↦ ?_
      change D (schwartzBruhatUnitTranslate (archNuclearity_archUnit u * archNuclearity_finiteUnit v)
        (tensor (a ⊗ₜ[ℂ] b))) = absValue(archNuclearity_archUnit u * archNuclearity_finiteUnit v) *
          D (tensor (a ⊗ₜ[ℂ] b))
      rw [archNuclearity_translate_pure, hD, hD, archNuclearity_moment_arch_translate i j b₀ hb hL,
        hLcov, map_mul, Units.val_mul, NNReal.coe_mul, Complex.ofReal_mul, mul_mul_mul_comm]
    obtain ⟨x, rfl⟩ := (tensor).surjective f
    exact LinearMap.congr_fun he x
  have hmem : D ∈ adelicEigendistributions c := by
    intro w f
    change _ = ((1 : ℂ) * absValue(w) ^ (1 : ℂ)) * D f
    rw [Complex.cpow_one, one_mul]
    exact hDcov w f
  let H : StrongDual ℂ ℬ(𝔸[F]) := hatC
  have hH : H ∈ adelicEigendistributions c := by
    intro w f
    change _ = ((1 : ℂ) * absValue(w) ^ (1 : ℂ)) * H f
    rw [Complex.cpow_one, one_mul]
    exact archNuclearity_hatC_translate w f
  have hnH : H ≠ 0 := by
    intro he
    have hh := hL a₀ b₀
    change H (tensor (a₀ ⊗ₜ[ℂ] b₀)) = _ at hh
    rw [he, zero_apply, hb, mul_one] at hh
    exact ha hh.symm
  have hr := Module.rank_eq_one_iff_finrank_eq_one.mp (adelicEigendistributions_rank c)
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hr hH hnH, Submodule.mem_span_singleton] at hmem
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, LinearMap.ext fun b ↦ ?_⟩
  have he := congrArg (fun d : StrongDual ℂ ℬ(𝔸[F]) ↦ d (tensor (a₀ ⊗ₜ[ℂ] b))) hz
  change z * hatC (tensor (a₀ ⊗ₜ[ℂ] b)) = D (tensor (a₀ ⊗ₜ[ℂ] b)) at he
  rw [hL, hD, mul_left_comm] at he
  exact (mul_left_cancel₀ ha he).symm

/-- If the additive-mass functional spans the algebraic eigenfunctionals,
the weighted translation differences generate its kernel. -/
private theorem span_weightedDifferences_eq_ker
    {W G : Type*} [AddCommGroup W] [Module ℂ W] (T : G → W → W) (c : G → ℂ)
    (J : W →ₗ[ℂ] ℂ) (hJ : ∀ u w, J (T u w) = c u * J w)
    (huniq : ∀ L : W →ₗ[ℂ] ℂ, (∀ u w, L (T u w) = c u * L w) → ∃ z : ℂ, L = z • J) :
    Submodule.span ℂ {x | ∃ u w, x = T u w - c u • w} = J.ker := by
  let D := Submodule.span ℂ {x | ∃ u w, x = T u w - c u • w}
  have hD : D ≤ J.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, w, rfl⟩
    change J (T u w - c u • w) = 0
    rw [map_sub, map_smul, smul_eq_mul, hJ, sub_self]
  apply Subspace.dualAnnihilator_inj.mp
  apply le_antisymm
  · intro l hl
    have hL (u : G) (w : W) : l (T u w) = c u * l w := by
      have hm : T u w - c u • w ∈ D := Submodule.subset_span ⟨u, w, rfl⟩
      have hz := (D.mem_dualAnnihilator l).mp hl _ hm
      rw [map_sub, map_smul, smul_eq_mul] at hz
      exact sub_eq_zero.mp hz
    obtain ⟨z, rfl⟩ := huniq l hL
    exact (J.ker.mem_dualAnnihilator _).mpr fun w hw ↦ by
      change z * J w = 0
      rw [LinearMap.mem_ker.mp hw, mul_zero]
  · intro l hl
    exact (D.mem_dualAnnihilator _).mpr fun w hw ↦ (J.ker.mem_dualAnnihilator _).mp hl _ (hD hw)


private theorem archNuclearity_weightedDifference
    (χ : PontryaginDual C𝔽) (hω : ω(χ) = 1)
    (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (b₀ : FiniteTests)
    (hb₀ : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (hi : ∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
      (i a = 0 ↔ (∫ y : Coord, h.val y) = 0))
    (a : ArchTests) (ha : a ∈ Aflat) (b : FiniteTests) (v : AFˣ) :
    tensor (a ⊗ₜ[ℂ] (schwartzBruhatUnitTranslate v b - absValue(archNuclearity_finiteUnit v) • b)) ∈
      A₀(χ) ⊔ K(χ) := by
  obtain ⟨u, hu⟩ := archNuclearity_archLift v
  let c := absValue(archNuclearity_finiteUnit v)
  let a' := schwartzBruhatUnitTranslate u a - c • a
  have ha' : a' ∈ Aflat :=
    Submodule.sub_mem _ (archNuclearity_flatFactors_translate u a ha) (Submodule.smul_mem _ _ ha)
  have hia : i a' = 0 := by
    change i (schwartzBruhatUnitTranslate u a - c • a) = 0
    rw [map_sub, map_smul, archNuclearity_moment_arch_translate i j b₀ hb₀ hL, hu, smul_eq_mul, sub_self]
  let p := tensor (a' ⊗ₜ[ℂ] b)
  have hp : p ∈ A₀(χ) := by
    obtain ⟨h, hh⟩ := ha'
    exact Submodule.subset_span ⟨a', b, h, hh, fun _ ↦ (hi a' h hh).mp hia, rfl⟩
  let q := tensor (a ⊗ₜ[ℂ] (schwartzBruhatUnitTranslate v b - c • b))
  have hq : q - p ∈ K(χ) := by
    let M := homogeneousAdelicThetaLinearMap F (ω(χ))
    have htheta := archNuclearity_theta_translate_sameNorm χ hω
      (archNuclearity_finiteUnit v) (archNuclearity_archUnit u) hu.symm
      (tensor (a ⊗ₜ[ℂ] b))
    have htF := archNuclearity_translate_pure (1 : A∞ˣ) v a b
    have htA := archNuclearity_translate_pure u (1 : AFˣ) a b
    rw [archNuclearity_translate_one, show archNuclearity_archUnit (F := F) 1 = 1 from Units.ext rfl,
      one_mul] at htF
    rw [archNuclearity_translate_one, show archNuclearity_finiteUnit (F := F) 1 = 1 from Units.ext rfl,
      mul_one] at htA
    let H := M.comp (tensor).toLinearMap
    have he : H (a ⊗ₜ[ℂ] schwartzBruhatUnitTranslate v b) =
        H (schwartzBruhatUnitTranslate u a ⊗ₜ[ℂ] b) :=
      ((congrArg M htF).symm.trans htheta).trans (congrArg M htA)
    have heq : M q = M p := by
      change H (a ⊗ₜ[ℂ] (schwartzBruhatUnitTranslate v b - c • b)) =
        H ((schwartzBruhatUnitTranslate u a - c • a) ⊗ₜ[ℂ] b)
      rw [TensorProduct.tmul_sub, TensorProduct.sub_tmul, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
      exact (map_sub H _ _).trans ((congrArg (· - H ((c • a) ⊗ₜ[ℂ] b)) he).trans
        (map_sub H _ _).symm)
    exact (map_sub M q p).trans (sub_eq_zero.mpr heq)
  refine Submodule.mem_sup.mpr ⟨p, hp, q - p, hq, ?_⟩
  change p + (q - p) = q
  rw [add_comm, sub_add_cancel]

private theorem archNuclearity_discard_massZero
    (χ : PontryaginDual C𝔽) (hω : ω(χ) = 1)
    (hcont : ∀ L : FiniteTests →ₗ[ℂ] ℂ, Continuous L)
    (i : ArchTests →L[ℂ] ℂ) (j : FiniteTests →ₗ[ℂ] ℂ) (a₀ : ArchTests) (b₀ : FiniteTests)
    (ha₀ : i a₀ ≠ 0) (hb₀ : j b₀ = 1) (hL : ∀ a b, hatC (tensor (a ⊗ₜ[ℂ] b)) = i a * j b)
    (hi : ∀ (a : ArchTests) (h : Flat), (∀ z, a (Multiplicative.ofAdd z) = h.val (coord z)) →
      (i a = 0 ↔ (∫ y : Coord, h.val y) = 0))
    (a : ArchTests) (ha : a ∈ Aflat) (b : FiniteTests) (hb : j b = 0) :
    tensor (a ⊗ₜ[ℂ] b) ∈ A₀(χ) ⊔ K(χ) := by
  let wt := fun v : AFˣ ↦ absValue(archNuclearity_finiteUnit v)
  have heq := span_weightedDifferences_eq_ker (schwartzBruhatUnitTranslate (R := AF)) wt j
    (archNuclearity_moment_finite_translate i j a₀ ha₀ hL)
    (archNuclearity_finiteEigen_unique hcont i j a₀ b₀ ha₀ hb₀ hL)
  let M : FiniteTests →ₗ[ℂ] ℬ(𝔸[F]) := (tensor).toLinearMap.comp (TensorProduct.mk ℂ ArchTests FiniteTests a)
  have H : Submodule.span ℂ {x | ∃ u w, x = schwartzBruhatUnitTranslate u w - wt u • w} ≤
      (A₀(χ) ⊔ K(χ)).comap M := by
    apply Submodule.span_le.mpr
    rintro _ ⟨u, w, rfl⟩
    exact archNuclearity_weightedDifference χ hω i j b₀ hb₀ hL hi a ha w u
  exact (heq ▸ H) hb

/-- Transport the finest topology of the empty tail without changing the
representation of the finite adelic test functions. -/
private theorem archNuclearity_finiteFunctionals_continuous (L : FiniteTests →ₗ[ℂ] ℂ) :
    Continuous L := by
  obtain ⟨e, he, _⟩ := finiteAdeleTail_empty F
  let : Fact (∀ w : {w : V // w ∉ (∅ : Finset V)},
      IsOpen (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F))) :=
    ⟨fun w ↦ Valued.isOpen_valuationSubring (w.val.adicCompletion F)⟩
  let : IsTopologicalRing (FiniteAdeleTail F ∅) := RestrictedProduct.isTopologicalRing _
  let : IsTopologicalGroup (Multiplicative (FiniteAdeleTail F ∅)) := inferInstance
  let d : Multiplicative (FiniteAdeleTail F ∅) ≃ₜ* Multiplicative AF :=
    ⟨e.toAddEquiv.toMultiplicative, he.continuous, he.homeomorph.symm.continuous.congr
      fun x ↦ e.injective (he.homeomorph.apply_symm_apply x |>.trans (e.apply_symm_apply x).symm)⟩
  let (v : V) : CompactSpace (v.adicCompletionIntegers F) := compactSpace_adicCompletionIntegers v
  let (v : V) : LocallyCompactSpace (v.adicCompletion F) := locallyCompactSpace_adicCompletion v
  let : Fact (∀ v : V, IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun v ↦ Valued.isOpen_valuationSubring _⟩
  let : T2Space (Multiplicative AF) := inferInstanceAs
    (T2Space (Πʳ w : V, [w.adicCompletion F, w.adicCompletionIntegers F]))
  let : LocallyCompactSpace (Multiplicative AF) := inferInstanceAs
    (LocallyCompactSpace (Πʳ w : V, [w.adicCompletion F, w.adicCompletionIntegers F]))
  let : T2Space (Multiplicative (FiniteAdeleTail F ∅)) := d.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (FiniteAdeleTail F ∅)) :=
    d.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  obtain ⟨T, hT⟩ := schwartzBruhat_transport d
  obtain ⟨S, hS⟩ := schwartzBruhat_transport d.symm
  let W := ℬ(FiniteAdeleTail F ∅)
  let Q : W →ₗ[ℂ] ℂ := L.comp T.toLinearMap
  have ht := (finiteProduct_tailSchwartz_finestTopology F ∅ ∅).2
  have hQ : Continuous Q :=
    Eq.mpr (congrArg (fun t : TopologicalSpace W ↦ @Continuous W ℂ t _ Q) ht)
      (continuous_of_finestLocallyConvex W Q)
  have hinv (f : FiniteTests) : T (S f) = f := by
    apply Subtype.ext
    funext x
    change T (S f) x = f x
    rw [hT, hS, ContinuousMulEquiv.symm_symm, d.apply_symm_apply]
  exact (hQ.comp S.continuous).congr fun f ↦ congrArg L (hinv f)

/-- Paper: Equations (7.4.3.1) and (7.4.3.12), pp. 368 and 371.
In the homogeneous theta image the factorwise moment condition agrees with
imposing the two global polar conditions on the unrestricted flat tensors. -/
theorem mem_archNuclearityDenominator_iff_flatPolarImage (x : Θ₀(χ)) :
    x ∈ archNuclearityDenominator χ ↔
      ∃ f : P, f.val ∈ globalArchimedeanFlatTests F ∧ x = mkΘ(χ, f) := by
  refine archNuclearity_of_finiteMassReduction χ x fun hω ↦ ?_
  obtain ⟨i, j, a₀, b₀, ha₀, hb₀, hL, hi⟩ := archNuclearity_normalized_moment (F := F)
  exact ⟨i.toLinearMap, j, b₀, hb₀, hL, hi,
    archNuclearity_discard_massZero χ hω archNuclearity_finiteFunctionals_continuous
      i j a₀ b₀ ha₀ hb₀ hL hi⟩

end FlatPolarImage

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

/-- Paper: Theorem 7.4.3.1(3), p. 368.
Every enumeration of the adjusted jets gives a Schauder basis on the quotient strong
dual. Pullback along the quotient map recovers the original jets. -/
theorem archNuclearityJet_basis :
    let Q := ArchNuclearityQuotient χ
    let J := ArchNuclearityJetIndex χ τ hτ
    Nonempty (ℕ ≃ J) ∧
      ∀ σ : ℕ ≃ J, ∃ (d : ℕ → StrongDual ℂ Q) (b : ℕ → StrongDual ℂ (StrongDual ℂ Q)),
        (∀ n x, d n ((archNuclearityDenominator χ).mkQ x) = archNuclearityJet χ τ hτ (σ n) x) ∧
        IsSchauderBasis d b := by sorry

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

/-- Paper: Equation (7.4.3.13) and the following paragraph, p. 372.
The coefficients of a quotient class are its adjusted jets, with the product topology.
The map includes simultaneous realization of every family of coefficients. -/
theorem archNuclearityQuotient_jetEquiv :
    ∃ e : ArchNuclearityQuotient χ ≃L[ℂ] (ArchNuclearityJetIndex χ τ hτ → ℂ),
      ∀ (x : Θ₀(χ)) j, e ((archNuclearityDenominator χ).mkQ x) j =
        archNuclearityJet χ τ hτ j x := by sorry

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
        Summable (fun n ↦ ‖diagonal n‖) ∧ HasSum diagonal ((∑' z, term z) - correction) := by sorry

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
