module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_ActualAnnularKernelSharpLimit
import RiemannMasullo.Ch12_TraceGeometric.Sec4_SmoothRadiusLawCofinal
import RiemannMasullo.Ch12_TraceGeometric.Sec4_InverseRadiusModulatedCutoff
import Mathlib.Tactic.Choose

/-! # An explicit cofinal annular family for the sharp orbit comparison -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators ContDiff ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "A" => SAdeleRing F S
local notation "I" => (SAdeleRing F S)ˣ
local notation "H" => sProjectedDiagonal F S
local notation "J" => SIdeleQuotient F S
local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Q" => continuousSIdeleQuotientNorm F S
local notation "μJ" => sLocalQuotientTamagawaMeasure F S
local notation "μI" => sMultiplicativeTamagawaMeasure F S
local notation "modS(" z ")" => ((∏ w : InfinitePlace F, ‖(z : A).1 w‖ ^ InfinitePlace.mult w) *
  ∏ v : S, ‖(z : A).2 v‖)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassT2Sec1
  instIdeleClassLocallyCompactSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instSIdeleLocallyCompactSec1 instFiniteCompletionUnitsLocallyCompactSec4b
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1

local instance instSIdeleT2ConcreteCofinalAnnularFamily : T2Space I :=
  (sIdeleGroup_description F S).2.1

private theorem bounded_annularWidth_ratio_tendsto_zero {ι : Type*} {l : Filter ι}
    {u e : ι → ℝ} (hu : Tendsto u l atTop) (he : ∀ p, e p ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun p ↦ e p / u p) l (𝓝 0) := by
  have hp : ∀ᶠ p in l, 0 < u p := hu.eventually (eventually_gt_atTop (0 : ℝ))
  refine squeeze_zero' (hp.mono fun p hp₀ ↦ div_nonneg (he p).1 hp₀.le) ?_
    (show Tendsto (fun p ↦ (u p)⁻¹) l (𝓝 0) from hu.inv_tendsto_atTop)
  filter_upwards [hp] with p hp₀
  rw [← one_div (u p)]
  exact div_le_div_of_nonneg_right (he p).2 hp₀.le

/-- Paper: Theorem 12.4.1.1, pp. 515–519. Smooth radius laws give an actual
inversion-symmetric modulated annulus along the cofinal upper path
(L, √L). Its weighted raw orbit diagonal differs from the sharp
orbital sum by a quantity tending to zero, assuming the small-radius
sharp bound.
Deviation: The result uses the raw diagonal and the square-root cutoff path. -/
theorem exists_sLocalTrace_sqrtPath_annularOrbitKernelFamily
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (g : C𝔽),
      φ.val (QuotientGroup.mk a.val * g) = φ.val g)
    (f : BruhatCompactSupport I)
    (hLift : ∀ g : I, HasSum (fun ξ : H ↦ f.val (ξ.val * g))
      (φ.val (QuotientGroup.mk (sIdeleInsertion F S g))))
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (D : Set I) (hD : IsFundamentalDomain H D μI) {s : ℝ} (hs : 0 ≤ s)
    (hSharp : ∃ C ≥ 0, ∀ {R : ℝ}, 0 < R → R ≤ 1 →
      Summable (fun ξ : H ↦ ‖sLocalTraceSharpMass f ξ R‖) ∧
      (∑' ξ : H, ‖sLocalTraceSharpMass f ξ R‖) ≤ C * R ^ (1 / 2 : ℝ)) :
    let ε (p : ℝ × ℝ) := (1 + |p.1|)⁻¹
    let path (L : ℝ) := (L, Real.sqrt L)
    let N (q : J) : ℝ := (Q q).val
    let ℓ := logSIdeleQuotientNorm F S
    let ν := intervalSobolevMeasure μJ ℓ 0 0 s
    ∃ (σ γ : ℝ × ℝ → Measure ℝ) (κ : ℝ × ℝ → J → J → ℂ),
      (∀ p, IsProbabilityMeasure (σ p) ∧ IsProbabilityMeasure (γ p) ∧
        σ p (Icc (p.1 - ε p) p.1)ᶜ = 0 ∧ γ p (Icc (p.2 - ε p) p.2)ᶜ = 0) ∧
      let ρ (p : ℝ × ℝ) (q : J) := Isolated.avgCutoff (σ p) (N q) -
        Isolated.avgCutoff ((σ p).map (Inv.inv : ℝ → ℝ)) (N q)
      let b (p : ℝ × ℝ) (r : ℝ) : ℂ := Isolated.avgCutoff (γ p) r
      let diag (p : ℝ × ℝ) (q : J) := (Real.sqrt (N q * N q) : ℂ) * κ p q q /
        ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 s (ℓ q) : ℂ))
      (∀ p, ContDiff ℝ (∞ : ℕ∞ω) (Isolated.avgCutoff (σ p)) ∧
        ContDiff ℝ (∞ : ℕ∞ω) (b p)) ∧
      (∀ p (x y : I), κ p (QuotientGroup.mk x) (QuotientGroup.mk y) =
        ∑' ξ : H, sLocalTraceCutoffKernel f (fun z ↦ (ρ p (QuotientGroup.mk z) : ℂ))
          (fun z ↦ b p (modS(z))) x (ξ.val * y).val) ∧
      (∀ᶠ L : ℝ in atTop, IsModulatedCutoff Q L (ε (path L)) (ρ (path L)) ∧
        L⁻¹ + ε (path L) < L - ε (path L) ∧ Continuous (ρ (path L)) ∧
        0 < Real.sqrt L - ε (path L) ∧ Integrable (diag (path L)) ν) ∧
      Tendsto (fun L : ℝ ↦ (∫ q, diag (path L) q ∂ν) -
        ∑' ξ : H, sLocalTraceSharpMass f ξ (L * Real.sqrt L)) atTop (𝓝 0) := by
  classical
  intro ε path N ℓ ν
  have hεPos (p : ℝ × ℝ) : 0 < ε p := inv_pos.mpr (by positivity)
  have hεBound (p : ℝ × ℝ) : ε p ∈ Icc (0 : ℝ) 1 := by
    refine ⟨(hεPos p).le, ?_⟩
    change (1 + |p.1|)⁻¹ ≤ (1 : ℝ)
    exact (inv_le_one₀ (by positivity : 0 < 1 + |p.1|)).mpr (by linarith [abs_nonneg p.1])
  have hε₁ : Tendsto (fun p : ℝ × ℝ ↦ ε p / p.1) (atTop ×ˢ atTop) (𝓝 0) :=
    bounded_annularWidth_ratio_tendsto_zero tendsto_fst hεBound
  have hε₂ : Tendsto (fun p : ℝ × ℝ ↦ ε p / p.2) (atTop ×ˢ atTop) (𝓝 0) :=
    bounded_annularWidth_ratio_tendsto_zero tendsto_snd hεBound
  choose σ hσprob hσatom hσ hσsmooth using fun p : ℝ × ℝ ↦
    exists_smoothRadiusLaw (sub_lt_self p.1 (hεPos p))
  choose γ hγprob _ hγ hγsmooth using fun p : ℝ × ℝ ↦
    exists_smoothRadiusLaw (sub_lt_self p.2 (hεPos p))
  let : ∀ p, IsProbabilityMeasure (σ p) := hσprob
  let : ∀ p, IsProbabilityMeasure (γ p) := hγprob
  let : ∀ p, NullSingletonClass (σ p) := hσatom
  let σFloor (p : ℝ × ℝ) := (σ p).map (Inv.inv : ℝ → ℝ)
  let : ∀ p, IsProbabilityMeasure (σFloor p) := fun p ↦
    inverseRadiusLaw_isProbabilityMeasure (σ p)
  let aFloor (p : ℝ × ℝ) := p.1⁻¹
  let floor (p : ℝ × ℝ) := (p.1 - ε p)⁻¹
  let ρ (p : ℝ × ℝ) (q : J) := Isolated.avgCutoff (σ p) (N q) -
    Isolated.avgCutoff (σFloor p) (N q)
  let b (p : ℝ × ℝ) (r : ℝ) : ℂ := Isolated.avgCutoff (γ p) r
  let l := Filter.map path (atTop : Filter ℝ)
  have hPath : Tendsto path atTop (atTop ×ˢ atTop) := symmetricRadiusPath_cofinal
  have hl : l ≤ atTop ×ˢ atTop := hPath
  have hLarge : ∀ᶠ p in l, (2 : ℝ) ≤ p.1 :=
    (tendsto_fst.mono_left hl).eventually (eventually_ge_atTop 2)
  have hCore {p : ℝ × ℝ} (hp : 2 ≤ p.1) : 1 ≤ p.1 - ε p := by
    linarith [(hεBound p).2]
  have hFrequencyCore : ∀ᶠ p in l, 0 < p.2 - ε p := by
    filter_upwards [(tendsto_snd.mono_left hl).eventually (eventually_ge_atTop (2 : ℝ))]
      with p hp
    linarith [(hεBound p).2]
  have hRadiusContinuous : Continuous N :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp
      (continuousSIdeleQuotientNorm F S).continuous)
  have hRadiusPos (q : J) : 0 < N q := NNReal.coe_pos.mpr (Units.zero_lt (Q q))
  have hMaskData : ∀ᶠ p in l, IsModulatedCutoff Q p.1 (ε p) (ρ p) ∧
      p.1⁻¹ + ε p < p.1 - ε p ∧ Continuous (ρ p) := by
    filter_upwards [hLarge] with p hp
    have hp₀ : 0 < p.1 := (by norm_num : (0 : ℝ) < 2).trans_le hp
    have hw : ε p < p.1⁻¹ := by
      change (1 + |p.1|)⁻¹ < p.1⁻¹
      exact (inv_lt_inv₀ (by positivity) hp₀).mpr (by linarith [le_abs_self p.1])
    refine ⟨isModulatedCutoff_avgCutoff_sub_inverseRadiusLaw Q (σ p)
      (hεPos p) hw (hCore hp) (hσ p) (hσsmooth p), ?_, ?_⟩
    · have hInv : p.1⁻¹ ≤ (2 : ℝ)⁻¹ :=
        (inv_le_inv₀ hp₀ (by norm_num : (0 : ℝ) < 2)).mpr hp
      norm_num at hInv
      linarith [hCore hp]
    · have hS := (hσsmooth p).continuous
      have hContinuous : Continuous (fun q : J ↦ Isolated.avgCutoff (σ p) (N q) -
          (1 - Isolated.avgCutoff (σ p) (N q)⁻¹)) :=
        (hS.comp hRadiusContinuous).sub (continuous_const.sub
          (hS.comp (hRadiusContinuous.inv₀ fun q ↦ (hRadiusPos q).ne')))
      have hEq : ρ p = fun q : J ↦ Isolated.avgCutoff (σ p) (N q) -
          (1 - Isolated.avgCutoff (σ p) (N q)⁻¹) := by
        funext q
        dsimp only [ρ, σFloor]
        rw [avgCutoff_inverseRadiusLaw (σ p) (zero_lt_one.trans_le (hCore hp))
          (hσ p) (hRadiusPos q)]
      rw [hEq]
      exact hContinuous
  have hMask : ∀ᶠ p in l, IsModulatedCutoff Q p.1 (ε p) (ρ p) :=
    hMaskData.mono fun _ h ↦ h.1
  have hFloor : ∀ᶠ p in l, 0 < aFloor p ∧ σFloor p (Icc (aFloor p) (floor p))ᶜ = 0 := by
    filter_upwards [hLarge] with p hp
    have hp₀ : 0 < p.1 := (by norm_num : (0 : ℝ) < 2).trans_le hp
    exact ⟨inv_pos.mpr hp₀, inverseRadiusLaw_support (σ p) (zero_lt_one.trans_le (hCore hp)) (hσ p)⟩
  have hSmall : Tendsto (fun p ↦ floor p * p.2) l (𝓝 0) := by
    have hεpath : Tendsto (fun L : ℝ ↦ ε (path L) / L) atTop (𝓝 0) := hε₁.comp hPath
    apply tendsto_map'
    exact tendsto_sqrt_mul_inverseRadius hεpath
  have hbCont (p : ℝ × ℝ) : ContDiff ℝ (∞ : ℕ∞ω) (b p) :=
    Complex.ofRealCLM.contDiff.comp (hγsmooth p)
  have hModUnit (η : H) (z : A) : modS(η.val.val * z) = modS(z) := by
    have hη : modS(η.val.val) = ((sIdeleNorm F S η.val).val : ℝ) := by
      simp [sIdeleNorm, Units.coe_prod]
    rw [Isolated.sIdeleNorm_projectedDiagonal η] at hη
    change modS(η.val.val) = 1 at hη
    change (∏ w : InfinitePlace F, ‖η.val.val.1 w * z.1 w‖ ^ w.mult) *
      (∏ v : S, ‖η.val.val.2 v * z.2 v‖) = modS(z)
    simp only [norm_mul, mul_pow, Finset.prod_mul_distrib]
    calc
      _ = modS(η.val.val) * modS(z) := by ring
      _ = _ := by rw [hη, one_mul]
  have hKernel (p : ℝ × ℝ) := exists_sLocalTraceOrbitSeries f
    (fun z ↦ (ρ p (QuotientGroup.mk z) : ℂ)) (fun z ↦ b p (modS(z)))
    (fun η x ↦ by
      rw [show (QuotientGroup.mk (η.val * x) : J) = QuotientGroup.mk x by
        rw [mul_comm η.val x, QuotientGroup.mk_mul_of_mem x η.property]])
    (fun η z ↦ congrArg (b p) (hModUnit η z))
  choose κ hRep using hKernel
  have hLimit := sLocalTrace_annularOrbitKernelFamily_sub_sharpMass_tendsto_zero
    φ hPic hRam hOutside f hLift τ hτ D hD σ γ σFloor ε aFloor floor hs ρ b κ l hl
    hσ hγ hε₁ hε₂ hFloor
    (hMask.mono fun p hp ↦
      ⟨⟨p.1, ε p, hp⟩, fun _ ↦ rfl, fun _ _ ↦ rfl, (contDiff_infty.mp (hbCont p)) _⟩)
    (Eventually.of_forall hRep) hSharp hSmall
  refine ⟨σ, γ, κ, fun p ↦ ⟨hσprob p, hγprob p, hσ p, hγ p⟩,
    fun p ↦ ⟨hσsmooth p, hbCont p⟩, hRep, ?_, ?_⟩
  · have hData := hMaskData.and (hFrequencyCore.and hLimit.1)
    have hDataPath := eventually_map.mp hData
    filter_upwards [hDataPath] with L hL
    exact ⟨hL.1.1, hL.1.2.1, hL.1.2.2, hL.2.1, hL.2.2⟩
  · exact tendsto_map'_iff.mp hLimit.2

end RiemannMasullo
