module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a_AngularCompanion
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a_QuantitativeStrip

/-! # Uniform arithmetic tails for finite positive-width quotient columns

Every finite set of angular modes can use a different strip center, positive half-width,
and finite predecessor-closed set of actual jets in each mode. Their squared orthogonal
column norms are dominated by one summable function on the true positive completed
Hecke divisor. This uses the arithmetic angular summability of PR 7547, based on the
unit-window arguments of fpet19 and anadodik in the discussion of Theorem 10.4.2.1.
-/

@[expose] public noncomputable section

open Classical Complex MeasureTheory Set IsDedekindDomain NumberField
open scoped ComplexConjugate NNReal NumberField.AdeleRing InnerProductSpace

namespace RiemannMasullo.SpectralStripJetIndex

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "D(" ψ ")" => MeromorphicOn.divisor (explicitFormulaCompletedHeckeL (F := F) ψ) univ
variable {a α s : ℝ}

/-- The point at which the completed Hecke L-function is evaluated for this strip jet. -/
def heckePoint
    {χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽} (j : SpectralStripJetIndex χ a α s) : ℂ :=
  ((a + j.val.2.1 : ℝ) : ℂ) + (j.val.2.2.1 : ℂ) * Complex.I

/-- The order of every admitted strip jet is strictly below the signed divisor multiplicity
of the continued Hecke L-function at its evaluation point. -/
private theorem order_lt_heckePoint_divisor
    {χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽} (j : SpectralStripJetIndex χ a α s) :
    (j.val.2.2.2 : ℤ) < D(χ j.val.1) j.heckePoint := by
  apply Int.lt_toNat.mp
  rw [(explicitFormulaCompletedHeckeL_spec (χ j.val.1)).1.meromorphicOn.divisor_apply (mem_univ _)]
  have h := j.property
  unfold spectralStripMultiplicity at h
  split_ifs at h with h₁ h₂
  · exact h
  · exact ((lt_spectralBoundaryMultiplicity _ _ _).mp h).1
  · omega

/-- Every evaluation point in a one-character jet family has positive Hecke divisor. -/
theorem divisor_pos_of_mem_image_heckePoint
    {χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽}
    (S : Finset (SpectralStripJetIndex χ a α s)) (ω : PontryaginDual C₁)
    (hω : ∀ j ∈ S, j.val.1 = ω) {ρ : ℂ} (hρ : ρ ∈ S.image heckePoint) :
    0 < D(χ ω) ρ := by
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hρ
  have hd := j.order_lt_heckePoint_divisor
  rw [hω j hj] at hd
  exact (Int.natCast_nonneg _).trans_lt hd

/-- At a fixed character and evaluation point, distinct admitted jets have distinct orders. -/
private theorem card_heckePoint_fiber_le
    {χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽}
    (S : Finset (SpectralStripJetIndex χ a α s)) (ω : PontryaginDual C₁)
    (hω : ∀ j ∈ S, j.val.1 = ω) (ρ : ℂ) :
    (S.filter (fun j ↦ j.heckePoint = ρ)).card ≤ (D(χ ω) ρ).toNat := by
  classical
  let fiber := S.filter (fun j ↦ j.heckePoint = ρ)
  let N := (D(χ ω) ρ).toNat
  have hmem {j : SpectralStripJetIndex χ a α s} (hj : j ∈ fiber) :
      j ∈ S ∧ j.heckePoint = ρ := Finset.mem_filter.mp hj
  have hmaps : MapsTo (fun j : SpectralStripJetIndex χ a α s ↦ j.val.2.2.2)
      (fiber : Set _) (Finset.range N : Set _) := by
    intro j hj
    obtain ⟨hjS, hjρ⟩ := hmem hj
    have hd := j.order_lt_heckePoint_divisor
    rw [hω j hjS, hjρ] at hd
    exact Finset.mem_range.mpr (Int.lt_toNat.mpr hd)
  have hinj : (fiber : Set (SpectralStripJetIndex χ a α s)).InjOn (fun j ↦ j.val.2.2.2) := by
    intro i hi j hj hk
    obtain ⟨hiS, hiρ⟩ := hmem hi
    obtain ⟨hjS, hjρ⟩ := hmem hj
    have hp := hiρ.trans hjρ.symm
    refine Subtype.ext (Prod.ext ((hω i hiS).trans (hω j hjS).symm) (Prod.ext ?_ (Prod.ext ?_ hk)))
    · simpa [heckePoint] using congrArg Complex.re hp
    · simpa [heckePoint] using congrArg Complex.im hp
  simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hmaps hinj

/-- Group a finite family by its Hecke evaluation point and bound its weighted count
by the signed divisor multiplicities. This applies to any selection of admitted orders. -/
theorem sum_heckePoint_le_divisor
    {χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽}
    (S : Finset (SpectralStripJetIndex χ a α s)) (ω : PontryaginDual C₁)
    (hω : ∀ j ∈ S, j.val.1 = ω) (f : ℂ → ℝ) (hf : ∀ ρ, 0 ≤ f ρ) :
    (∑ j : S, f j.val.heckePoint) ≤
      ∑ ρ ∈ S.image heckePoint, (D(χ ω) ρ : ℝ) * f ρ := by
  classical
  let p : SpectralStripJetIndex χ a α s → ℂ := heckePoint
  have hMaps (j : SpectralStripJetIndex χ a α s) (hj : j ∈ S) : p j ∈ S.image p :=
    Finset.mem_image_of_mem p hj
  calc
    _ = ∑ j ∈ S, f (p j) := Finset.sum_coe_sort S (fun j ↦ f (p j))
    _ = ∑ ρ ∈ S.image p, ∑ _j ∈ S.filter (fun j ↦ p j = ρ), f ρ :=
      (Finset.sum_fiberwise_of_maps_to' hMaps f).symm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hpos := divisor_pos_of_mem_image_heckePoint S ω hω hρ
      have hc := card_heckePoint_fiber_le S ω hω ρ
      have hi : ((S.filter (fun j ↦ p j = ρ)).card : ℤ) ≤ D(χ ω) ρ := by
        change ((S.filter (fun j ↦ j.heckePoint = ρ)).card : ℤ) ≤ _
        omega
      have hr : ((S.filter (fun j ↦ p j = ρ)).card : ℝ) ≤ (D(χ ω) ρ : ℝ) := by exact_mod_cast hi
      simpa only [Finset.sum_const, nsmul_eq_mul] using mul_le_mul_of_nonneg_right hr (hf ρ)

end RiemannMasullo.SpectralStripJetIndex

namespace RiemannMasullo

open Isolated
set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "K𝔽" => (ideleClassNorm F).ker
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "W(" α ")" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) (-α) α 0
local notation "rows(" τ ")" => {η : PontryaginDual C𝔽 // ∀ t : ℝ≥0ˣ, η (τ t) = 1}
local notation "D(" η ")" => MeromorphicOn.divisor (explicitFormulaCompletedHeckeL η) Set.univ
local notation "pairs(" τ ")" => (Σ η : rows(τ), {z : ℂ // 0 < D(η.val) z})
local notation "lift(" τ "," hτ ")" => spectralAngularNormalizedLift τ hτ
local notation "mode(" η ")" => spectralAngularChartMode (η).val

/-- A finite predecessor-closed family of actual strip jets at order zero in one angular
mode, with any orthonormal basis of its canonical Riesz span. -/
structure SpectralStripColumnBlock
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽) (ω : PontryaginDual K𝔽) where
  center : ℝ
  width : ℝ
  width_pos : 0 < width
  jets : Finset (SpectralStripJetIndex χ center width 0)
  sameMode : ∀ j ∈ jets, j.val.1 = ω
  lowerClosed : ∀ j ∈ jets, j.lowerOne ∈ jets
  basis : OrthonormalBasis jets ℂ (Submodule.span ℂ (Set.range fun i : jets ↦
    spectralAngularJetRiesz center width_pos.le (le_rfl : 0 ≤ (0 : ℝ)) χ i.val))

/-- Sum of squared norms of the actual Chapter 10 quotient adjoint on this block. -/
def SpectralStripColumnBlock.energy {χ : PontryaginDual K𝔽 → PontryaginDual C𝔽}
    {ω : PontryaginDual K𝔽} (b : SpectralStripColumnBlock χ ω)
    (φ : BruhatCompactSupport C𝔽) : ℝ :=
  let Θ := globalThetaSobolev F b.center (neg_le_self b.width_pos.le) (le_rfl : 0 ≤ (0 : ℝ))
  let T := spectralConvolution (F := F) b.center (neg_le_self b.width_pos.le)
    (le_rfl : 0 ≤ (0 : ℝ)) φ
  ∑ i, ‖T.adjoint (Θ.mkQ (b.basis i : W(b.width)))‖^2

/-- Every finite one-mode predecessor-closed set of genuine jets determines such a
block. The normalized finite Hilbert basis exists by linear independence of its
canonical Riesz vectors. -/
def SpectralStripColumnBlock.ofJets
    (χ : PontryaginDual K𝔽 → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (a α : ℝ) (hα : 0 < α) (ω : PontryaginDual K𝔽)
    (S : Finset (SpectralStripJetIndex χ a α 0)) (hS : ∀ j ∈ S, j.val.1 = ω)
    (hpred : ∀ j ∈ S, j.lowerOne ∈ S) : SpectralStripColumnBlock χ ω := by
  classical
  let v (j : S) := spectralAngularJetRiesz a hα.le (le_rfl : 0 ≤ (0 : ℝ)) χ j.val
  have hi : LinearIndependent ℂ v :=
    (spectralAngularJetRiesz_linearIndependent a hα.le le_rfl χ hχ).comp _ Subtype.val_injective
  let V := Submodule.span ℂ (Set.range v)
  letI : FiniteDimensional ℂ V := Module.Finite.of_basis (Module.Basis.span hi)
  have hc : Fintype.card S = Module.finrank ℂ V := (finrank_span_eq_card hi).symm
  let e := (stdOrthonormalBasis ℂ V).reindex (Fintype.equivFinOfCardEq hc).symm
  exact ⟨a,α,hα,S,hS,hpred,e⟩

variable (τ : ℝ≥0ˣ →ₜ* (IdeleClassGroup (𝓞 F) F)) (hτ : Function.RightInverse τ (ideleClassNorm F))
/-- A block at a chart character normalized with respect to the indicated norm section. -/
abbrev NormalizedStripColumnBlock (η : rows(τ)) :=
  SpectralStripColumnBlock (spectralAngularNormalizedLift τ hτ) (spectralAngularChartMode η.val)

/-- All positive-divisor labels touched by a finite block. Different orders at the same
zero share a label, whose arithmetic weight contains the full positive divisor order. -/
def SpectralStripColumnBlock.divisorSupport (η : rows(τ)) (b : NormalizedStripColumnBlock τ hτ η) : Finset pairs(τ) := by
  classical
  let points := b.jets.image fun j ↦ j.heckePoint
  let e : (↑points) ↪ pairs(τ) := {
    toFun := fun z ↦ ⟨η, ⟨z.val, by
      rw [← spectralAngularNormalizedLift_chartMode τ hτ η]
      exact SpectralStripJetIndex.divisor_pos_of_mem_image_heckePoint b.jets _ b.sameMode z.property⟩⟩
    inj' := fun _ _ h ↦ Subtype.ext (congrArg (fun p : pairs(τ) ↦ p.2.val) h) }
  exact points.attach.map e

private theorem spectralStripBlock_support_fst (η : rows(τ)) (b : NormalizedStripColumnBlock τ hτ η)
    (p : pairs(τ)) (hp : p ∈ b.divisorSupport τ hτ η) : p.1 = η := by
  classical
  unfold SpectralStripColumnBlock.divisorSupport at hp
  obtain ⟨z, _, rfl⟩ := Finset.mem_map.mp hp
  rfl

/-- The common width-independent mass at a normalized chart character and a true zero. -/
def spectralStripColumnDivisorMass (A : ℝ) (ψ : BruhatCompactSupport C𝔽)
    (p : pairs(τ)) : ℝ :=
  (spectralAngularWidthEnvelope A ψ p.1.val)^2 *
    spectralAngularDivisorHeightWeight p.1.val p.2.val

private theorem spectralStripBlock_support_mass (η : rows(τ)) (b : NormalizedStripColumnBlock τ hτ η)
    (A : ℝ) (ψ : BruhatCompactSupport C𝔽) :
    ∑ p ∈ b.divisorSupport τ hτ η, spectralStripColumnDivisorMass τ A ψ p =
      (spectralAngularWidthEnvelope A ψ η.val)^2 *
        ∑ z ∈ b.jets.image (fun j ↦ j.heckePoint), (D(η.val) z : ℝ) * (1+z.im^2)⁻¹ := by
  classical
  unfold SpectralStripColumnBlock.divisorSupport
  rw [Finset.sum_map]
  let points := b.jets.image (fun j ↦ j.heckePoint)
  let K := spectralAngularWidthEnvelope A ψ η.val
  change (∑ z ∈ points.attach, K^2 * ((D(η.val) z.val : ℝ)/(1+z.val.im^2))) = _
  rw [Finset.sum_attach points (fun z : ℂ ↦ K^2*((D(η.val) z : ℝ)/(1+z.im^2))), Finset.mul_sum]
  simp only [div_eq_mul_inv, K, points]

private theorem spectralStripBlock_algebraicNorm_le (η : rows(τ)) (b : NormalizedStripColumnBlock τ hτ η)
    (A : ℝ) (hwidth : b.width ≤ A) (ψ : BruhatCompactSupport C𝔽) :
    let r := spectralAngularJetRiesz b.center b.width_pos.le (le_rfl : 0 ≤ (0 : ℝ)) (lift(τ,hτ))
    let V := Submodule.span ℂ (r '' {j | j.val.1 = mode(η)})
    let U := (hardySobolevTestAction μ𝔽 m𝔽 (-b.width) b.width 0
      (neg_le_self b.width_pos.le) le_rfl ψ).adjoint.comp V.subtypeL
    ‖U‖ ≤ spectralAngularWidthEnvelope A ψ η.val := by
  let χ := lift(τ,hτ)
  let r := spectralAngularJetRiesz b.center b.width_pos.le (le_rfl : 0 ≤ (0 : ℝ)) χ
  let V := Submodule.span ℂ (r '' {j | j.val.1 = mode(η)})
  let T := (hardySobolevTestAction μ𝔽 m𝔽 (-b.width) b.width 0
    (neg_le_self b.width_pos.le) le_rfl ψ).adjoint
  have hK : ‖T.comp V.subtypeL‖ ≤ spectralAngularChartNorm b.center b.width b.width_pos.le χ ψ η.val := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) ?_
    intro x
    let xc : spectralAngularJetSpace b.center χ r (mode(η)) := ⟨x.val, subset_closure x.property⟩
    exact (spectralAngularJetAdjoint b.center b.width_pos.le le_rfl χ r ψ (mode(η))).le_opNorm xc
  exact hK.trans (spectralAngularChartNorm_le_widthEnvelope A b.center b.width b.width_pos.le
    hwidth χ (spectralAngularNormalizedLift_basepoint τ hτ) ψ η.val)

private theorem spectralStripBlock_energy_le_support (A : ℝ) (hA : 0 ≤ A)
    (φ ψ : BruhatCompactSupport C𝔽)
    (hψ : ∀ η : rows(τ), ∀ z : ℂ, (∫ g : C𝔽, ψ.val g * ideleClassNormTwist η.val z g ∂μ𝔽) =
      (((A+1 : ℝ):ℂ)-z) * ∫ g : C𝔽, φ.val g * ideleClassNormTwist η.val z g ∂μ𝔽)
    (η : rows(τ)) (b : NormalizedStripColumnBlock τ hτ η) (hw : b.width ≤ A) :
    b.energy φ ≤ (1+2*A) * ∑ p ∈ b.divisorSupport τ hτ η, spectralStripColumnDivisorMass τ A ψ p := by
  classical
  let χ := lift(τ,hτ)
  let ω := mode(η)
  let r := spectralAngularJetRiesz b.center b.width_pos.le (le_rfl : 0 ≤ (0 : ℝ)) χ
  let V := Submodule.span ℂ (r '' {j | j.val.1 = ω})
  let U := (hardySobolevTestAction μ𝔽 m𝔽 (-b.width) b.width 0
    (neg_le_self b.width_pos.le) le_rfl ψ).adjoint.comp V.subtypeL
  let K := spectralAngularWidthEnvelope A ψ η.val
  let weights := ∑ i : b.jets, (1+i.val.val.2.2.1^2)⁻¹
  have hχ : IsSpectralBasepointChoice χ := spectralAngularNormalizedLift_basepoint τ hτ
  have hη : χ ω = η.val := spectralAngularNormalizedLift_chartMode τ hτ η
  have hraw : b.energy φ ≤ (1+2*A)*‖U‖^2*weights :=
    spectralStripConvolution_finite_jet_bound_uniform_width χ b.center A b.width_pos hw φ ψ ω
      (hη.symm ▸ hψ η) r (spectralAngularJetRiesz_linearIndependent b.center b.width_pos.le le_rfl χ hχ)
      (spectralAngularJetRiesz_inner _ _ _ _) b.jets b.sameMode b.lowerClosed b.basis
  have hK : ‖U‖ ≤ K := spectralStripBlock_algebraicNorm_le τ hτ η b A hw ψ
  have hC : 0 ≤ 1+2*A := by linarith
  have hweights : 0 ≤ weights := Finset.sum_nonneg fun _ _ ↦ by positivity
  let f (z : ℂ) := (1+z.im^2)⁻¹
  have hdiv : weights ≤ ∑ z ∈ b.jets.image (fun j ↦ j.heckePoint), (D(η.val) z : ℝ) * f z := by
    have h := SpectralStripJetIndex.sum_heckePoint_le_divisor b.jets ω b.sameMode f
      (fun z ↦ by dsimp [f]; positivity)
    rw [show (spectralAngularNormalizedLift τ hτ) ω = η.val from hη] at h
    have him (j : SpectralStripJetIndex χ b.center b.width 0) : j.heckePoint.im = j.val.2.2.1 := by
      simp [SpectralStripJetIndex.heckePoint]
    simpa only [weights, f, him] using h
  rw [spectralStripBlock_support_mass]
  calc
    b.energy φ ≤ (1+2*A)*‖U‖^2*weights := hraw
    _ ≤ (1+2*A)*K^2*weights := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hK 2) hC) hweights
    _ ≤ (1+2*A)*K^2*∑ z ∈ b.jets.image (fun j ↦ j.heckePoint), (D(η.val) z : ℝ)*f z :=
      mul_le_mul_of_nonneg_left hdiv (mul_nonneg hC (sq_nonneg _))
    _ = _ := mul_assoc _ _ _

/-- Divisor labels touched by a finite collection of different normalized angular modes. -/
def spectralStripColumnSupport (Q : Finset rows(τ))
    (b : ∀ η : Q, NormalizedStripColumnBlock τ hτ η.val) : Finset pairs(τ) := by
  classical
  exact Finset.univ.biUnion (fun η : Q ↦ (b η).divisorSupport τ hτ η.val)

private theorem spectralStripMode_sum_le (A : ℝ) (hA : 0 ≤ A)
    (φ ψ : BruhatCompactSupport C𝔽)
    (hψ : ∀ η : rows(τ), ∀ z : ℂ, (∫ g : C𝔽, ψ.val g * ideleClassNormTwist η.val z g ∂μ𝔽) =
      (((A+1 : ℝ):ℂ)-z) * ∫ g : C𝔽, φ.val g * ideleClassNormTwist η.val z g ∂μ𝔽)
    (Q : Finset rows(τ)) (b : ∀ η : Q, NormalizedStripColumnBlock τ hτ η.val) (hw : ∀ η, (b η).width ≤ A) :
    ∑ η : Q, (b η).energy φ ≤ (1+2*A) *
      ∑ p ∈ spectralStripColumnSupport τ hτ Q b, spectralStripColumnDivisorMass τ A ψ p := by
  classical
  let support (η : Q) := (b η).divisorSupport τ hτ η.val
  let mass := spectralStripColumnDivisorMass τ A ψ
  have hdis : (↑(Finset.univ : Finset Q) : Set Q).PairwiseDisjoint support := by
    intro i _ j _ hne
    apply Finset.disjoint_left.mpr
    intro p hi hj
    exact hne (Subtype.ext ((spectralStripBlock_support_fst τ hτ i.val (b i) p hi).symm.trans
      (spectralStripBlock_support_fst τ hτ j.val (b j) p hj)))
  change ∑ η : Q, (b η).energy φ ≤ (1+2*A) * ∑ p ∈ Finset.univ.biUnion support, mass p
  rw [Finset.sum_biUnion hdis, Finset.mul_sum]
  exact Finset.sum_le_sum fun η _ ↦ spectralStripBlock_energy_le_support τ hτ A hA φ ψ hψ η.val (b η) (hw η)

/-- Paper: Theorem 10.4.2.1, p. 459. A single summable positive-divisor mass controls the
squared quotient columns in every finite family of distinct angular characters. Each mode may
have its own strip center, positive half-width up to A, predecessor-closed finite jet set and
orthonormal basis. Reconstruction: the estimate at Sobolev order zero also gives one finite
tail cutoff for every such choice. -/
theorem exists_spectralStripConvolution_uniform_divisor_tails
    (A : ℝ) (hA : 0 ≤ A) (φ : BruhatCompactSupport C𝔽) :
    ∃ ψ : BruhatCompactSupport C𝔽,
      Summable (spectralStripColumnDivisorMass τ A ψ) ∧
      (∀ (Q : Finset rows(τ)) (b : ∀ η : Q, NormalizedStripColumnBlock τ hτ η.val), (∀ η, (b η).width ≤ A) →
        ∑ η : Q, (b η).energy φ ≤ (1+2*A) *
          ∑ p ∈ spectralStripColumnSupport τ hτ Q b, spectralStripColumnDivisorMass τ A ψ p) ∧
      (∀ (Q : Finset rows(τ)) (b : ∀ η : Q, NormalizedStripColumnBlock τ hτ η.val),
        (∀ η, (b η).width ≤ A) → ∑ η : Q, (b η).energy φ ≤
          (1+2*A) * ∑' p, spectralStripColumnDivisorMass τ A ψ p) ∧
      ∀ ε : ℝ, 0 < ε → ∃ cutoff : Finset pairs(τ),
        ∀ (Q : Finset rows(τ)) (b : ∀ η : Q, NormalizedStripColumnBlock τ hτ η.val), (∀ η, (b η).width ≤ A) →
          Disjoint (spectralStripColumnSupport τ hτ Q b) cutoff →
          ∑ η : Q, (b η).energy φ < ε := by
  obtain ⟨ψ,hψ⟩ := exists_normalized_heckeTest_mellin_affine_companion τ hτ φ (A+1)
  let mass := spectralStripColumnDivisorMass τ A ψ
  have hs : Summable mass := spectralAngularWidthEnvelope_summable_fullDivisor A ψ τ hτ
  have hrow := spectralStripMode_sum_le τ hτ A hA φ ψ (fun η ↦ hψ η.val η.property)
  have hfull (Q : Finset rows(τ)) (b : ∀ η : Q, NormalizedStripColumnBlock τ hτ η.val)
      (hw : ∀ η, (b η).width ≤ A) :
      ∑ η : Q, (b η).energy φ ≤ (1+2*A) * ∑' p, mass p := by
    refine (hrow Q b hw).trans (mul_le_mul_of_nonneg_left ?_ (by linarith))
    apply hs.sum_le_tsum
    intro p _
    exact mul_nonneg (sq_nonneg _) (div_nonneg (by exact_mod_cast p.2.property.le) (by positivity))

  refine ⟨ψ, hs, hrow, hfull, ?_⟩
  intro ε hε
  have hs' : Summable (fun p ↦ (1+2*A)*mass p) := hs.mul_left _
  obtain ⟨cutoff,hcut⟩ := summable_iff_vanishing_norm.mp hs' ε hε
  refine ⟨cutoff, ?_⟩
  intro Q b hw hdis
  let T := spectralStripColumnSupport τ hτ Q b
  calc
    ∑ η : Q, (b η).energy φ ≤ (1+2*A)*∑ p ∈ T, mass p := hrow Q b hw
    _ = ∑ p ∈ T, (1+2*A)*mass p := Finset.mul_sum _ _ _
    _ ≤ |∑ p ∈ T, (1+2*A)*mass p| := le_abs_self _
    _ < ε := hcut T hdis

end RiemannMasullo
end
