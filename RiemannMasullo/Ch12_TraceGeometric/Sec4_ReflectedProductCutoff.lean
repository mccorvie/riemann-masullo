module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FullReflectedProjection
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ProductFrequencyCutoff
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3_CompactFourierBand
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.Projection.Contraction
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Tactic.Ring

/-! # The actual smooth frequency cutoff in reflected coordinates -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Jₛ" => SIdeleQuotient F S
local notation "N" => sIdeleQuotientNorm F S
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "W₀" => CompactIntervalSobolev (sLocalQuotientTamagawaMeasure F S)
  (logSIdeleQuotientNorm F S) 0 0 0
local notation "FlatL2" => Lp ℂ 2 (volume : Measure ℝ)
local notation "prodNorm(" u ")" =>
  (∏ w : InfinitePlace F, ‖(u : Aₛ).1 w‖ ^ InfinitePlace.mult w) * ∏ v : S, ‖(u : Aₛ).2 v‖
local notation "include₁" =>
  (ContinuousMonoidHom.mk (Subgroup.subtype (MonoidHom.ker (sIdeleQuotientNorm F S)))
    continuous_subtype_val : J₁ →ₜ* Jₛ)
local notation "gen(" angular ")" => Isolated.sLocalFullPWThetaSobolevMap (F := F) (S := S)
  (s := 0) (a := 1 / 2) (by norm_num) angular

private theorem fullTheta_mul_productNorm_frequency
    (b : ℝ → ℂ) (f g : Bₛ)
    (hF : ∀ u : Aₛ, sAdeleSchwartzFourier g (Multiplicative.ofAdd u) =
      b (prodNorm(u)) * sAdeleSchwartzFourier f (Multiplicative.ofAdd u))
    (angular : PontryaginDual J₁) (q : Jₛ) :
    sLocalHomogeneousAdelicThetaLinearMap F S angular (sAdeleSchwartzFourier g) q =
      b ((N q).val : ℝ) *
        sLocalHomogeneousAdelicThetaLinearMap F S angular (sAdeleSchwartzFourier f) q := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply, sLocalHomogeneousAdelicThetaLinearMap_apply,
    ← integral_const_mul]
  apply integral_congr_ae
  refine ae_of_all _ fun h ↦ ?_
  have hn : N (q * h.val) = N q := by
    rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
  change sLocalAdelicThetaOnClasses F S (sAdeleSchwartzFourier g) (q * h.val) * (angular h : ℂ) =
    b ((N q).val : ℝ) *
      (sLocalAdelicThetaOnClasses F S (sAdeleSchwartzFourier f) (q * h.val) * (angular h : ℂ))
  rw [sLocalAdelicThetaOnClasses_mul_productNorm b _ _ hF, hn, mul_assoc]

/-- The genuine adelic smooth frequency cutoff becomes a multiplier on the
reflected real coordinate, including on generators outside the output band. -/
theorem exists_sLocalFullReflectedGenAE_productCutoff_transfer
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (angular : PontryaginDual J₁) (χ : PontryaginDual Jₛ)
    (T : W₀ →L[ℂ] FlatL2) (hGen : sLocalFullReflectedGenAE τ angular χ T)
    (b : ℝ → ℂ) (hb : ContDiff ℝ (∞ : ℕ∞ω) b) {δ : ℝ} (hδ : 0 < δ)
    (hplateau : EqOn b (fun _ ↦ b 0) (Icc 0 δ))
    (M : FlatL2 →L[ℂ] FlatL2)
    (hM : ∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x)
    (f : Bₛ) (hf : HasCompactSupport (sAdeleSchwartzFourier f).val) :
    ∃ g : Bₛ, HasCompactSupport (sAdeleSchwartzFourier g).val ∧
      sLocalTraceFourierCutoff (fun u : Aₛ ↦ b (prodNorm(u))) f =
        (fun u : Aₛ ↦ g (Multiplicative.ofAdd u)) ∧
      T (gen(angular) g) = M (T (gen(angular) f)) := by
  obtain ⟨g, hcut, hF, hsubset⟩ := sLocalTraceFourierCutoff_realize_compact_band b hb hδ hplateau f hf
  have hgc : HasCompactSupport (sAdeleSchwartzFourier g).val :=
    hf.of_isClosed_subset isClosed_closure hsubset
  refine ⟨g, hgc, funext hcut, ?_⟩
  have hRad (x : ℝ) :
      sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier g) (-x) =
        b (Real.exp (-x)) * sLocalRadialThetaHalfDensity τ χ⁻¹ (sAdeleSchwartzFourier f) (-x) := by
    let t : ℝ≥0ˣ := Units.mk0 (Real.exp (-x)).toNNReal (by positivity)
    let q : Jₛ := QuotientGroup.mk (τ t)
    have hn : ((N q).val : ℝ) = Real.exp (-x) := by
      dsimp only [q]
      rw [sIdeleQuotientNorm_mk, hτ]
      exact Real.coe_toNNReal _ (Real.exp_pos _).le
    let ψ : PontryaginDual J₁ := (χ⁻¹).comp include₁
    change (sLocalHomogeneousAdelicThetaLinearMap F S ψ (sAdeleSchwartzFourier g) q *
      ((χ⁻¹) q : ℂ)) * (Real.exp ((-x) / 2) : ℂ) = b (Real.exp (-x)) *
      ((sLocalHomogeneousAdelicThetaLinearMap F S ψ (sAdeleSchwartzFourier f) q *
        ((χ⁻¹) q : ℂ)) * (Real.exp ((-x) / 2) : ℂ))
    rw [fullTheta_mul_productNorm_frequency b f g hF ψ q, hn]
    ring
  apply Lp.ext
  filter_upwards [hGen g, hGen f, hM (T (gen(angular) f))] with x hg hx hm
  rw [hg, hm, hx, hRad]
  ring

/-- Paper: (12.4.1.8), p. 517. The reflected real multiplier followed by
the adjoint of the coordinate map realizes the actual smooth adelic
frequency cutoff on every generator with compact Fourier support.
Deviation: This identifies the order-zero input cutoff in each angular
type. A single reflected map works for all these generators and profiles. -/
theorem exists_sLocalFullReflectedProductCutoff_orderZero
    (τ : ℝ≥0ˣ →ₜ* Iₛ) (hτ : RightInverse τ (sIdeleNorm F S))
    (angular : PontryaginDual J₁) :
    ∃ (χ : PontryaginDual Jₛ) (T : W₀ →L[ℂ] FlatL2),
      χ.comp include₁ = angular ∧ (∀ t, χ (QuotientGroup.mk (τ t)) = 1) ∧
      ‖T‖ ≤ 1 ∧ sLocalFullReflectedGenAE τ angular χ T ∧
      ∀ (b : ℝ → ℂ), ContDiff ℝ (∞ : ℕ∞ω) b → (∀ t, ‖b t‖ ≤ 1) →
        ∀ δ, 0 < δ → EqOn b (fun _ ↦ b 0) (Icc 0 δ) →
        ∃ M : FlatL2 →L[ℂ] FlatL2,
          (∀ r, (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x) ∧
          ∀ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val →
            ∃ g : Bₛ, HasCompactSupport (sAdeleSchwartzFourier g).val ∧
              sLocalTraceFourierCutoff (fun u : Aₛ ↦ b (prodNorm(u))) f =
                (fun u : Aₛ ↦ g (Multiplicative.ofAdd u)) ∧
              gen(angular) g = T.adjoint (M (T (gen(angular) f))) := by
  obtain ⟨χ, Q, _, U, hχ, hsec, hT, hGen, hBand⟩ :=
    exists_sLocalFullReflectedProjection_uniform_orderZero (F := F) (S := S) τ hτ angular
  let T : W₀ →L[ℂ] FlatL2 := U.toLinearIsometry.toContinuousLinearMap.comp Q
  refine ⟨χ, T, hχ, hsec, hT, hGen, ?_⟩
  intro b hb hbdd δ hδ hplateau
  let symbol (x : ℝ) := b (Real.exp (-x))
  have hs : MemLp symbol (⊤ : ℝ≥0∞) (volume : Measure ℝ) := memLp_top_of_bound
    (hb.continuous.comp (Real.continuous_exp.comp continuous_neg)).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ hbdd (Real.exp (-x)))
  let mulCLM := ContinuousLinearMap.mul ℂ ℂ
  let M := mulCLM.holderL volume (⊤ : ℝ≥0∞) 2 2 (hs.toLp symbol)
  have hM (r : FlatL2) : (M r : ℝ → ℂ) =ᵐ[volume] fun x ↦ b (Real.exp (-x)) * r x :=
    (mulCLM.coeFn_holder (r := 2) (hs.toLp symbol) r).trans
      (hs.coeFn_toLp.mono fun x hx ↦ congrArg (· * r x) hx)
  refine ⟨M, hM, ?_⟩
  intro f hf
  obtain ⟨g, hg, hCut, hMul⟩ :=
    @exists_sLocalFullReflectedGenAE_productCutoff_transfer F _ _ S
      τ hτ angular χ T hGen b hb δ hδ hplateau M hM f hf
  obtain ⟨B, hB, hgBand⟩ :=
    @exists_sLocalPWTests_sameStage_productRegion_of_hasCompactSupport_fourier F _ _ S g hg
  let V : Submodule ℂ W₀ :=
    Isolated.sLocalFullPWSobolev (F := F) (S := S) (s := 0)
      le_rfl (show (0 : ℝ) < 1 / 2 by norm_num) angular B
  have hmem : gen(angular) g ∈ V := by
    change gen(angular) g ∈
      ((sLocalPWTests (F := F) (S := S) (T := S) le_rfl
        (sLocalPWProductRegion S B)).map gen(angular)).topologicalClosure
    exact Submodule.le_topologicalClosure _ (Submodule.mem_map.mpr ⟨g, hgBand, rfl⟩)
  have hIso : ‖T (gen(angular) g)‖ = ‖gen(angular) g‖ := (hBand B hB).1 _ hmem
  refine ⟨g, hg, hCut, ?_⟩
  calc
    _ = T.adjoint (T (gen(angular) g)) :=
      (adjoint_apply_apply_eq_of_norm_preserved T hT (gen(angular) g) hIso).symm
    _ = _ := congrArg T.adjoint hMul

/-- An orbit operator with the cutoff rows of one angular type agrees with
the reflected multiplier followed by the given bounded action on the closed
span of the compact-Fourier generators in that type. The realization
hypothesis is provided by `exists_sLocalFullReflectedProductCutoff_orderZero`. -/
theorem eqOn_orbit_reflectedProductCutoff_compactGenClosure_orderZero
    (angular : PontryaginDual J₁) (b : ℝ → ℂ)
    (T : W₀ →L[ℂ] FlatL2) (M : FlatL2 →L[ℂ] FlatL2) (K C : W₀ →L[ℂ] W₀)
    (hRealize : ∀ f : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val →
      ∃ g : Bₛ, HasCompactSupport (sAdeleSchwartzFourier g).val ∧
        sLocalTraceFourierCutoff (fun u : Aₛ ↦ b (prodNorm(u))) f = (fun u : Aₛ ↦ g (Multiplicative.ofAdd u)) ∧
        gen(angular) g = T.adjoint (M (T (gen(angular) f))))
    (hK : ∀ f g : Bₛ, HasCompactSupport (sAdeleSchwartzFourier f).val →
      HasCompactSupport (sAdeleSchwartzFourier g).val →
      sLocalTraceFourierCutoff (fun u : Aₛ ↦ b (prodNorm(u))) f = (fun u : Aₛ ↦ g (Multiplicative.ofAdd u)) →
      K (gen(angular) f) = C (gen(angular) g)) :
    EqOn K (C.comp (T.adjoint.comp (M.comp T)))
      (closure (Submodule.span ℂ {u : W₀ | ∃ f : Bₛ,
        HasCompactSupport (sAdeleSchwartzFourier f).val ∧ gen(angular) f = u} : Set W₀)) := by
  apply ContinuousLinearMap.eqOn_closure_span
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨g, hg, hcut, hT⟩ := hRealize f hf
  exact (hK f g hf hg hcut).trans (congrArg C hT)

end RiemannMasullo
