module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_AnnularSmoothSharpLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Choose

/-! # Sharp orbital comparison for a family of raw quotient kernels -/

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

local instance instSIdeleT2ActualAnnularKernelSharpLimit : T2Space I :=
  (sIdeleGroup_description F S).2.1

private theorem upperProfile_derivatives_bounded {b : ℝ → ℂ} {n : ℕ} (hb : ContDiff ℝ n b)
    {B : ℝ} (hz : ∀ r, B < r → b r = 0) :
    ∃ C : ℝ, ∀ j : ℕ, j ≤ n → ∀ r : ℝ, 0 ≤ r → ‖iteratedDeriv j b r‖ ≤ C := by
  classical
  have hp (j : Fin (n + 1)) : ∃ C ≥ 0, ∀ r : ℝ, 0 ≤ r →
      ‖iteratedDeriv (j : ℕ) b r‖ ≤ C := by
    have hj : (j : ℕ) ≤ n := Nat.le_of_lt_succ j.isLt
    have hcont : Continuous (iteratedDeriv (j : ℕ) b) :=
      hb.continuous_iteratedDeriv (j : ℕ) (by exact_mod_cast hj)
    have hCompact : IsCompact (Icc (0 : ℝ) B) := isCompact_Icc
    obtain ⟨C, hC⟩ := hCompact.exists_bound_of_continuousOn hcont.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun r hr ↦ ?_⟩
    by_cases h : r ≤ B
    · exact (hC r ⟨hr, h⟩).trans (le_max_left _ _)
    · have hEq : b =ᶠ[𝓝 r] (fun _ ↦ (0 : ℂ)) := by
        filter_upwards [Ioi_mem_nhds (lt_of_not_ge h)] with t ht
        exact hz t ht
      rw [hEq.iteratedDeriv_eq (j : ℕ)]
      simpa only [iteratedDeriv_fun_const_zero, norm_zero] using (le_max_right C (0 : ℝ))
  choose C hC₀ hC using hp
  refine ⟨∑ j, C j, fun j hj r hr ↦ ?_⟩
  let i : Fin (n + 1) := ⟨j, Nat.lt_succ_of_le hj⟩
  exact (hC i r hr).trans (Finset.single_le_sum (fun k _ ↦ hC₀ k) (Finset.mem_univ i))

/-- Paper: Theorem 12.4.1.1, Steps II–III, pp. 515–519.
For the given orbit kernel family, the integral of its weighted raw diagonal
agrees asymptotically with the summed sharp masses as the upper cutoffs
diverge and the lower spatial radius times the upper frequency radius
tends to zero. The small positive radius bound is an explicit input.
Deviation: The spatial masks are modulated cutoffs, including inversion
symmetry, and the limit is taken along the specified path. -/
theorem sLocalTrace_annularOrbitKernelFamily_sub_sharpMass_tendsto_zero
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRam : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (g : C𝔽),
      φ.val (QuotientGroup.mk a.val * g) = φ.val g)
    (f : BruhatCompactSupport I)
    (hLift : ∀ g : I, HasSum (fun ξ : H ↦ f.val (ξ.val * g))
      (φ.val (QuotientGroup.mk (sIdeleInsertion F S g))))
    (τ : ℝ≥0ˣ →ₜ* I) (hτ : RightInverse τ (sIdeleNorm F S))
    (D : Set I) (hD : IsFundamentalDomain H D μI)
    (σ γ σFloor : ℝ × ℝ → Measure ℝ)
    [∀ p, IsProbabilityMeasure (σ p)] [∀ p, IsProbabilityMeasure (γ p)]
    [∀ p, IsProbabilityMeasure (σFloor p)]
    (ε aFloor floor : ℝ × ℝ → ℝ) {s : ℝ} (hs : 0 ≤ s)
    (ρ : ℝ × ℝ → J → ℝ) (b : ℝ × ℝ → ℝ → ℂ)
    (κ : ℝ × ℝ → J → J → ℂ)
    (l : Filter (ℝ × ℝ)) (hl : l ≤ atTop ×ˢ atTop)
    (hσ : ∀ p, σ p (Icc (p.1 - ε p) p.1)ᶜ = 0)
    (hγ : ∀ p, γ p (Icc (p.2 - ε p) p.2)ᶜ = 0)
    (hε₁ : Tendsto (fun p ↦ ε p / p.1) (atTop ×ˢ atTop) (𝓝 0))
    (hε₂ : Tendsto (fun p ↦ ε p / p.2) (atTop ×ˢ atTop) (𝓝 0))
    (hFloor : ∀ᶠ p in l,
      0 < aFloor p ∧ σFloor p (Icc (aFloor p) (floor p))ᶜ = 0)
    (hCutoffs : ∀ᶠ p in l, (∃ Λ ερ, IsModulatedCutoff Q Λ ερ (ρ p)) ∧
      (∀ q : J, ρ p q = Isolated.avgCutoff (σ p) ((Q q).val : ℝ) -
        Isolated.avgCutoff (σFloor p) ((Q q).val : ℝ)) ∧
      (∀ r : ℝ, 0 ≤ r → b p r = (Isolated.avgCutoff (γ p) r : ℂ)) ∧
      ContDiff ℝ (2 * (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) + 1) : ℕ) (b p))
    (hRep : ∀ᶠ p in l, ∀ x y : I, κ p (QuotientGroup.mk x) (QuotientGroup.mk y) =
      ∑' ξ : H, sLocalTraceCutoffKernel f (fun z ↦ (ρ p (QuotientGroup.mk z) : ℂ))
        (fun z ↦ b p (modS(z))) x (ξ.val * y).val)
    (hSharp : ∃ C ≥ 0, ∀ {R : ℝ}, 0 < R → R ≤ 1 →
      Summable (fun ξ : H ↦ ‖sLocalTraceSharpMass f ξ R‖) ∧
      (∑' ξ : H, ‖sLocalTraceSharpMass f ξ R‖) ≤ C * R ^ (1 / 2 : ℝ))
    (hSmall : Tendsto (fun p ↦ floor p * p.2) l (𝓝 0)) :
    let N (q : J) : ℝ := (Q q).val
    let ℓ := logSIdeleQuotientNorm F S
    let ν := intervalSobolevMeasure μJ ℓ 0 0 s
    let diag (p : ℝ × ℝ) (q : J) := (Real.sqrt (N q * N q) : ℂ) * κ p q q /
      ((sLocalTraceMeasureFactor S : ℂ) * (intervalSobolevDensity 0 0 s (ℓ q) : ℂ))
    (∀ᶠ p in l, Integrable (diag p) ν) ∧
      Tendsto (fun p ↦ (∫ q, diag p q ∂ν) -
        ∑' ξ : H, sLocalTraceSharpMass f ξ (p.1 * p.2)) l (𝓝 0) := by
  intro N ℓ ν diag
  have hL : Tendsto (Prod.fst : ℝ × ℝ → ℝ) l atTop := tendsto_fst.mono_left hl
  have hB : Tendsto (Prod.snd : ℝ × ℝ → ℝ) l atTop := tendsto_snd.mono_left hl
  have hPos : ∀ᶠ p in l, 0 < p.1 - ε p ∧ 0 < p.2 - ε p := by
    filter_upwards [hL.eventually (eventually_gt_atTop (0 : ℝ)),
      hB.eventually (eventually_gt_atTop (0 : ℝ)),
      (hε₁.mono_left hl).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)),
      (hε₂.mono_left hl).eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))]
      with p h₁ h₂ hεp₁ hεp₂
    have hεp₁' := (div_le_iff₀ h₁).mp hεp₁
    have hεp₂' := (div_le_iff₀ h₂).mp hεp₂
    exact ⟨by linarith, by linarith⟩
  have hSum : ∀ᶠ p in l, Integrable (diag p) ν ∧
      HasSum (fun ξ : H ↦ Isolated.sLocalSmoothMass f ξ D (σ p) (γ p) p.1 -
        Isolated.sLocalSmoothMass f ξ D (σFloor p) (γ p) (floor p))
        (∫ q, diag p q ∂ν) := by
    filter_upwards [hPos, hFloor, hCutoffs, hRep] with p hp hf hcut hRepP
    obtain ⟨⟨Λ, ερ, hρ⟩, hρLaw, hbLaw, hb⟩ := hcut
    have hBPos : 0 < p.2 := hp.2.trans_le (Isolated.le_of_prob_support (hγ p))
    have hz (r : ℝ) (hr : p.2 < r) : b p r = 0 := by
      rw [hbLaw r (hBPos.trans hr).le, Isolated.avgCutoff_eq_zero (γ p) (hγ p) hr,
        Complex.ofReal_zero]
    obtain ⟨_, hderiv⟩ := upperProfile_derivatives_bounded hb hz
    have hplateau : EqOn (b p) (fun _ ↦ b p 0) (Icc 0 (p.2 - ε p)) := by
      intro r hr
      change b p r = b p 0
      rw [hbLaw r hr.1, hbLaw 0 le_rfl, Isolated.avgCutoff_eq_one (γ p) (hγ p) hr.2,
        Isolated.avgCutoff_eq_one (γ p) (hγ p) hp.2.le]
    obtain ⟨κ', hRep', hDiag', hSum'⟩ :=
      exists_sLocalTrace_fixedAnnulus_smoothMass_difference_hasSum τ hτ f D hD
        (σ p) (σFloor p) (γ p) hp.1 hf.1 hp.2 (hσ p) hf.2 (hγ p)
        (b p) hρ hs hρLaw hbLaw hb hp.2 hplateau hderiv
    have hκ : κ' = κ p := by
      funext q r
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
      exact (hRep' x y).trans (hRepP x y).symm
    subst κ'
    exact ⟨hDiag', hSum'⟩
  refine ⟨hSum.mono (fun _ hp ↦ hp.1), ?_⟩
  refine sLocalAnnularRawDiagonal_sub_sharpMass_tendsto_zero φ hPic hRam hOutside f hLift D hD
    σ γ σFloor ε aFloor floor (fun p ↦ ∫ q, diag p q ∂ν) l hl
    hσ hγ hε₁ hε₂ hFloor hSharp hSmall ?_
  exact hSum.mono fun _ hp ↦ ⟨hp.2.summable, hp.2.tsum_eq.symm⟩

end RiemannMasullo
