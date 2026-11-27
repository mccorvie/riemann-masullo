module

public import RiemannMasullo.AppC_LCTVS.Sec3a_StrongTraceNorm
public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a
import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Trace-norm limits on a fixed spatial annulus -/

@[expose] public noncomputable section

open Filter MeasureTheory Topology

namespace RiemannMasullo

/-- Uniformly bounded measurable cutoff symbols converging almost everywhere give
strong convergence of their multiplication operators on weighted L². -/
private theorem tendsto_cutoffMultiplier_apply_of_ae {X ι : Type*} [MeasurableSpace X]
    (ν : Measure X) {l : Filter ι} [l.IsCountablyGenerated]
    (ρ : ι → X → ℝ) (q : X → ℝ) (hm : ∀ i, Measurable (ρ i)) (hqm : Measurable q)
    (hb : ∀ i x, |ρ i x| ≤ 1) (hqb : ∀ x, |q x| ≤ 1)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun i ↦ ρ i x) l (𝓝 (q x)))
    (M : ι → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (Q : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hM : ∀ i u, (M i u : X → ℂ) =ᵐ[ν] fun x ↦ (ρ i x : ℂ) * u x)
    (hQ : ∀ u, (Q u : X → ℂ) =ᵐ[ν] fun x ↦ (q x : ℂ) * u x) (u : Lp ℂ 2 ν) :
    Tendsto (fun i ↦ M i u) l (𝓝 (Q u)) := by
  let f (i : ι) (x : X) := ((ρ i x : ℂ) - (q x : ℂ)) * u x
  have hu := Lp.aestronglyMeasurable u
  have hmeas (i : ι) : AEStronglyMeasurable (f i) ν :=
    (((Complex.measurable_ofReal.comp (hm i)).aestronglyMeasurable.sub
      ((Complex.measurable_ofReal.comp hqm).aestronglyMeasurable)).mul hu)
  have hbound (i : ι) (x : X) : ‖f i x‖ ≤ 2 * ‖u x‖ := by
    change ‖((ρ i x : ℂ) - (q x : ℂ)) * u x‖ ≤ _
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (norm_sub_le _ _).trans (by
      simpa only [Complex.norm_real, Real.norm_eq_abs, one_add_one_eq_two] using
        add_le_add (hb i x) (hqb x))
  have hint : Integrable (fun x ↦ 4 * ‖u x‖ ^ 2) ν :=
    ((Lp.memLp u).integrable_norm_pow (by decide : 2 ≠ 0)).const_mul 4
  have hconv : Tendsto (fun i ↦ ∫ x, ‖f i x‖ ^ 2 ∂ν) l (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (l := l) (F := fun i x ↦ ‖f i x‖ ^ 2) (f := fun _ : X ↦ (0 : ℝ))
      (fun x ↦ 4 * ‖u x‖ ^ 2) (.of_forall fun i ↦ (hmeas i).norm.pow 2)
      (.of_forall fun i ↦ .of_forall fun x ↦ ?_) hint ?_
    · simpa using h
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      nlinarith [hbound i x, norm_nonneg (f i x), norm_nonneg (u x)]
    · filter_upwards [hlim] with x hx
      have hcast : Tendsto (fun i ↦ (ρ i x : ℂ)) l (𝓝 (q x : ℂ)) :=
        (Complex.continuous_ofReal.tendsto (q x)).comp hx
      simpa [f] using
        (((hcast.sub (tendsto_const_nhds (x := (q x : ℂ)))).mul_const (u x)).norm.pow 2)
  have heq (i : ι) : ∫ x, ‖f i x‖ ^ 2 ∂ν = ‖M i u - Q u‖ ^ 2 := by
    rw [← L2.integral_sq_norm (𝕜 := ℂ)]
    apply integral_congr_ae
    filter_upwards [hM i u, hQ u, Lp.coeFn_sub (M i u) (Q u)] with x hi hq hsub
    change M i u x = _ at hi
    change Q u x = _ at hq
    change ‖f i x‖ ^ 2 = ‖(M i u - Q u) x‖ ^ 2
    rw [hsub]
    change ‖f i x‖ ^ 2 = ‖M i u x - Q u x‖ ^ 2
    rw [hi, hq, show f i x = _ from sub_mul _ _ _]
  have hsq : Tendsto (fun i ↦ ‖M i u - Q u‖ ^ 2) l (𝓝 0) := by
    simpa only [heq] using hconv
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa using hsq.sqrt)

end RiemannMasullo

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "J" => SIdeleQuotient F S
local notation "N" => continuousSIdeleQuotientNorm F S
local notation "μ" => sLocalQuotientTamagawaMeasure F S

/-- One closed-band cutoff of the S-local weighted test action is a nuclear factor for
all bounded measurable spatial masks supported in a common positive norm annulus. -/
private theorem exists_sLocalAnnularNuclearTestActionFactor
    {s : ℝ} (hs : 0 ≤ s) (φ : BruhatCompactSupport J)
    {lower upper : ℝ} (hlower : 0 < lower) :
    let ν := intervalSobolevMeasure μ (logSIdeleQuotientNorm F S) 0 0 s
    let A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := hardySobolevTestAction μ N 0 0 s le_rfl hs φ
    ∃ Q : nuclearEndomorphisms (Lp ℂ 2 ν),
      ∀ (ρ : J → ℝ) (hm : Measurable ρ) (hb : ∀ x, |ρ x| ≤ 1),
        (∀ x, ρ x ≠ 0 → lower ≤ ((N x).val : ℝ) ∧ ((N x).val : ℝ) ≤ upper) →
        let M := lpCutoffMultiplier ν ρ hm hb
        M.comp Q.val = M.comp A := by
  intro ν A
  let Λ : ℝ := max 2 (max upper lower⁻¹)
  let c : J → ℝ := fun x ↦ if ((N x).val : ℝ) ∈ Icc Λ⁻¹ Λ then 1 else 0
  have hΛ : 2 ≤ Λ := le_max_left _ _
  have hupper : upper ≤ Λ := (le_max_left _ _).trans (le_max_right _ _)
  have hinv : Λ⁻¹ ≤ lower := by
    have h : lower⁻¹ ≤ Λ := (le_max_right _ _).trans (le_max_right _ _)
    simpa only [inv_inv] using inv_anti₀ (inv_pos.mpr hlower) h
  obtain ⟨hc, hband⟩ := isModulatedCutoff_closedBand N Λ hΛ
  have hNsurj : Surjective (N : J → ℝ≥0ˣ) := by
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
    exact hσ.surjective
  have hNmod : IsModulation N := by
    refine ⟨isProperMap_sIdeleQuotientNorm F S, ?_⟩
    obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
    obtain ⟨x, hx⟩ := hNsurj t
    exact ⟨x, fun h ↦ ht (hx.symm.trans h)⟩
  have hφsmooth : IsBruhatSmooth φ.val := (mem_bruhatSmoothSubmodule_iff _).mp φ.property.1
  have hφc := continuous_of_bruhatSmooth hφsmooth
  have hφb := hφc.bounded_above_of_compact_support
    (show HasCompactSupport φ.val from φ.property.2)
  let C := modulatedCutoffOperator N ν hc
  have hQ : IsNuclearOperator (C.comp A) := by
    obtain ⟨hn, _, _⟩ := truncatedHardySobolevConvolution_trace μ N 0 0 s le_rfl hs φ.val
      hφc.aemeasurable φ.property.2 hφb hNmod hNsurj hφsmooth hc hband
    rw [hardySobolevConvolution_eq_testAction μ N 0 0 s le_rfl hs φ hφc.aemeasurable hφb] at hn
    exact hn
  refine ⟨⟨C.comp A, hQ⟩, ?_⟩
  intro ρ hm hb hρ M
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [lpCutoffMultiplier_apply ν ρ hm hb (C (A u)),
    modulatedCutoffOperator_apply N ν hc (A u), lpCutoffMultiplier_apply ν ρ hm hb (A u)]
    with x h₁ h₂ h₃
  change C (A u) x = (c x : ℂ) * (A u) x at h₂
  change M (C (A u)) x = M (A u) x
  rw [h₁, h₂, h₃]
  by_cases hx : ρ x = 0
  · simp [hx]
  · obtain ⟨hl, hu⟩ := hρ x hx
    have hmem : ((N x).val : ℝ) ∈ Icc Λ⁻¹ Λ := ⟨hinv.trans hl, hu.trans hupper⟩
    have hc₁ : c x = 1 := ite_eq_left hmem
    simp [hc₁]

end RiemannMasullo

namespace RiemannMasullo

section AnnularTraceNorm

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1 instSIdeleQuotientLocallyCompactSec1
  instSIdeleQuotientSecondCountableSec1 instSIdeleQuotientHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))} {s : ℝ}

local notation "J" => SIdeleQuotient F S
local notation "N" => continuousSIdeleQuotientNorm F S
local notation "μ" => sLocalQuotientTamagawaMeasure F S
local notation "ν" => intervalSobolevMeasure μ (logSIdeleQuotientNorm F S) 0 0 s
local notation "H" => Lp ℂ 2 ν
local notation "E" => (H →L[ℂ] H)

/-- Paper: Theorem 12.4.1.1, Step II, pp. 515–517.
On the invariant Paley–Wiener level, a uniformly bounded family of spatial cutoffs
in a common positive annulus can be passed to its almost-everywhere limit in trace
norm, provided the bounded right factors have strongly convergent adjoints.
Deviation: State convergence for the ambient extension by the orthogonal
projection, with the right endomorphisms as parameters. -/
theorem sLocalInvariantPWSobolev_annularCompression_traceNorm_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {a : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (ω : PontryaginDual (sIdeleQuotientNorm F S).ker) (B : ℝ) (φ : BruhatCompactSupport J)
    {lower upper : ℝ} (hlower : 0 < lower)
    (ρ : ι → J → ℝ) (q : J → ℝ)
    (hm : ∀ i, Measurable (ρ i)) (hqm : Measurable q)
    (hb : ∀ i x, |ρ i x| ≤ 1) (hqb : ∀ x, |q x| ≤ 1)
    (hρ : ∀ i x, ρ i x ≠ 0 → lower ≤ ((N x).val : ℝ) ∧ ((N x).val : ℝ) ≤ upper)
    (hq : ∀ x, q x ≠ 0 → lower ≤ ((N x).val : ℝ) ∧ ((N x).val : ℝ) ≤ upper)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun i ↦ ρ i x) l (𝓝 (q x)))
    (K : ι → E) (K₀ : E) {D : ℝ} (hKbound : ∀ᶠ i in l, ‖K i‖ ≤ D)
    (hK : ∀ u, Tendsto (fun i ↦ (K i).adjoint u) l (𝓝 (K₀.adjoint u))) :
    let V : Submodule ℂ H := sLocalInvariantPWSobolev (F := F) (S := S) hs ha ω B
    letI : CompleteSpace V := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
    let P : E := V.starProjection
    let A : E := hardySobolevTestAction μ N 0 0 s le_rfl hs φ
    let M (i : ι) : E := lpCutoffMultiplier ν (ρ i) (hm i) (hb i)
    let M₀ : E := lpCutoffMultiplier ν q hqm hqb
    ∃ (T : ι → nuclearEndomorphisms H) (T₀ : nuclearEndomorphisms H),
      (∀ i, (T i).val = P * ((M i * A) * (K i * P))) ∧
      T₀.val = P * ((M₀ * A) * (K₀ * P)) ∧
      Tendsto (fun i ↦ traceNorm (T i - T₀)) l (𝓝 0) := by
  intro V P A M M₀
  obtain ⟨Q, hQ⟩ :=
    exists_sLocalAnnularNuclearTestActionFactor (upper := upper) hs φ hlower
  let wrap (L R : E) : nuclearEndomorphisms H :=
    ⟨(L * Q.val) * R, mul_mem_nuclearEndomorphisms_right R
      ⟨L * Q.val, mul_mem_nuclearEndomorphisms_left L Q⟩⟩
  have hfactor (i : ι) : M i * Q.val = M i * A :=
    hQ (ρ i) (hm i) (hb i) (hρ i)
  have hfactor₀ : M₀ * Q.val = M₀ * A := hQ q hqm hqb hq
  have hM (i : ι) : ‖M i‖ ≤ 1 :=
    (exists_lpCutoffMultiplier ν (ρ i) (hm i) (hb i)).choose_spec.1
  have hLbound : ∀ᶠ i in l, ‖P * M i‖ ≤ ‖P‖ := .of_forall fun i ↦
    (ContinuousLinearMap.opNorm_comp_le P (M i)).trans
      (mul_le_of_le_one_right (norm_nonneg P) (hM i))
  have hRbound : ∀ᶠ i in l, ‖K i * P‖ ≤ D * ‖P‖ := hKbound.mono fun i hi ↦
    (ContinuousLinearMap.opNorm_comp_le (K i) P).trans
      (mul_le_mul_of_nonneg_right hi (norm_nonneg P))
  have hL (u : H) : Tendsto (fun i ↦ (P * M i) u) l (𝓝 ((P * M₀) u)) :=
    (P.continuous.tendsto (M₀ u)).comp
      (tendsto_cutoffMultiplier_apply_of_ae ν ρ q hm hqm hb hqb hlim M M₀
        (fun i ↦ lpCutoffMultiplier_apply ν (ρ i) (hm i) (hb i))
        (lpCutoffMultiplier_apply ν q hqm hqb) u)
  have hR (u : H) : Tendsto (fun i ↦ (K i * P).adjoint u) l
      (𝓝 ((K₀ * P).adjoint u)) := by
    change Tendsto (fun i ↦ ((K i).comp P).adjoint u) l
      (𝓝 ((K₀.comp P).adjoint u))
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
    exact (P.adjoint.continuous.tendsto (K₀.adjoint u)).comp (hK u)
  have hlimit := tendsto_traceNorm_sandwich_of_strong_left_adjoint_right Q
    (fun i ↦ P * M i) (fun i ↦ K i * P) (P * M₀) (K₀ * P) hLbound hRbound hL hR
  have hwrap (B C : E) (h : B * Q.val = B * A) :
      (wrap (P * B) (C * P)).val = P * ((B * A) * (C * P)) := by
    change ((P * B) * Q.val) * (C * P) = _
    calc
      _ = P * ((B * Q.val) * (C * P)) := by simp only [mul_assoc]
      _ = _ := by rw [h]
  exact ⟨fun i ↦ wrap (P * M i) (K i * P), wrap (P * M₀) (K₀ * P),
    fun i ↦ hwrap (M i) (K i) (hfactor i), hwrap M₀ K₀ hfactor₀, hlimit⟩

end AnnularTraceNorm

end RiemannMasullo
