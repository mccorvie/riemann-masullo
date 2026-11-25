module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineWindows
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineQuarticActions
public import RiemannMasullo.AppC_LCTVS.Sec3a_SchwartzWindows
public import RiemannMasullo.AppB_AnalyticNT.Sec4b
import all RiemannMasullo.Ch09_HardySobolev.Sec3
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-! # Homogeneous convolution on the line quotient

At width zero the quotient is separated by the retained Mellin jets. A multiplier
supported in one bounded frequency interval has quotient rank at most the number
of these jets in that interval. The full positive divisor controls this count in
every Sobolev order, including at its strict cutoffs.

The integrated jet formula is from #7474. The homogeneous Schwartz profile chart
and the nuclearity criterion for quadratic window ranks are from #7641.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped Classical NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1 instSpectralQuotientPolynormableSec3

set_option quotPrecheck false
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "Ω" => PontryaginDual C₁
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "h₀" => le_rfl (a := (0 : ℝ))
local notation "hs₀(" hs ")" => le_of_lt (zero_lt_one.trans hs)
local notation "W(" s ")" => CompactIntervalSobolev μ𝔽 (logIdeleClassNorm F) 0 0 s
local notation "Θ(" a ", " hs ")" => globalThetaSobolev F a h₀ hs₀(hs)
local notation "Q(" a ", " hs ")" => spectralSobolevQuotient F a h₀ hs₀(hs)
local notation "τ(" s ", " hs ")" => hardySobolevTranslation μ𝔽 m𝔽 0 0 s h₀ hs₀(hs)
local notation "shift(" a ", " t ")" => ((a : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I

/-- The actual line jets in one angular row and `[-R,R]` have quadratic count.
The constant is uniform in the real part of the line and in the Sobolev order. -/
theorem spectralLine_jets_quadratic_count (χ : Ω → PontryaginDual C𝔽) (ω : Ω) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a s R : ℝ), 0 ≤ R →
      let S := {j : SpectralLineJetIndex χ a s | j.val.1 = ω ∧ |j.val.2.1| ≤ R}
      S.Finite ∧ (S.ncard : ℝ) ≤ C * (1 + R) ^ 2 := by
  classical
  let D := MeromorphicOn.divisor (continuedCompletedHeckeL (χ ω)) univ
  let Z := {z : ℂ // 0 < D z}
  let I := (z : Z) × Fin (D z.val).toNat
  let w (p : I) : ℝ := 1 / (1 + |p.1.val.im|) ^ 2
  have hw₀ (p : I) : 0 ≤ w p := by dsimp [w]; positivity
  have hw : Summable w := by
    apply (summable_sigma_of_nonneg hw₀).mpr
    refine ⟨fun _ ↦ Summable.of_finite, ?_⟩
    have hD : Summable (fun z : Z ↦ (D z.val : ℝ) / (1 + |z.val.im|) ^ 2) :=
      explicitFormulaCompletedHeckeL_summable_divisor_div_sq (χ ω)
    refine hD.congr fun z ↦ ?_
    simp only [w, tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [show ((D z.val).toNat : ℝ) = (D z.val : ℝ) by exact_mod_cast Int.toNat_of_nonneg z.property.le]
    ring
  refine ⟨∑' p, w p, tsum_nonneg hw₀, fun a s R hR ↦ ?_⟩
  let S := {j : SpectralLineJetIndex χ a s | j.val.1 = ω ∧ |j.val.2.1| ≤ R}
  have bound (K : Finset (SpectralLineJetIndex χ a s)) (hK : (K : Set _) ⊆ S) :
      (K.card : ℝ) ≤ (∑' p, w p) * (1 + R) ^ 2 := by
    have hj (j : K) : j.val.val.2.2 < (D (shift(a,j.val.val.2.1))).toNat := by
      have h := ((lt_spectralBoundaryMultiplicity s _ _).mp j.val.property).1
      have he := (hK j.property).1
      rw [he] at h
      rwa [show D (shift(a,j.val.val.2.1)) =
        (meromorphicOrderAt (continuedCompletedHeckeL (χ ω)) (shift(a,j.val.val.2.1))).untop₀ from
          (continuedCompletedHeckeL_spec (χ ω)).1.meromorphicOn.divisor_apply (mem_univ _)]
    let e (j : K) : I := ⟨⟨shift(a,j.val.val.2.1), by have h := hj j; omega⟩, ⟨_,hj j⟩⟩
    have he : Injective e := by
      intro j k h
      have ht := congrArg (fun p : I ↦ p.1.val.im) h
      have hn := congrArg (fun p : I ↦ p.2.val) h
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext ((hK j.property).1.trans (hK k.property).1.symm)
      exact Prod.ext (by simpa [e, Complex.add_im, Complex.mul_im] using ht) hn
    have hsum : ∑ j : K, w (e j) ≤ ∑' p, w p := by
      simpa only [tsum_fintype] using
        (show Summable (fun j : K ↦ w (e j)) from .of_finite).tsum_le_tsum_of_inj
          e he (fun p _ ↦ hw₀ p) (fun _ ↦ le_rfl) hw
    have hpoint (j : K) : 1 ≤ w (e j) * (1 + R) ^ 2 := by
      have ht : |(e j).1.val.im| ≤ R := by
        simpa only [e, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, zero_mul, mul_one, add_zero, zero_add] using (hK j.property).2
      dsimp only [w]
      rw [one_div_mul_eq_div, le_div_iff₀ (by positivity), one_mul]
      gcongr
    calc
      (K.card : ℝ) = ∑ _j : K, (1 : ℝ) := by simp
      _ ≤ ∑ j : K, w (e j) * (1 + R) ^ 2 := Finset.sum_le_sum fun j _ ↦ hpoint j
      _ = (∑ j : K, w (e j)) * (1 + R) ^ 2 := (Finset.sum_mul ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
  have hS : S.Finite := by
    by_contra h
    obtain ⟨n, hn⟩ := exists_nat_gt ((∑' p, w p) * (1 + R) ^ 2)
    obtain ⟨U, hU, hf, hc⟩ := (show S.Infinite from h).exists_subset_ncard_eq n
    have hb := bound hf.toFinset (by simpa using hU)
    rw [← Set.ncard_eq_toFinset_card U hf, hc] at hb
    exact hn.not_ge hb
  refine ⟨hS, ?_⟩
  change (S.ncard : ℝ) ≤ _
  rw [Set.ncard_eq_toFinset_card S hS]
  exact bound hS.toFinset (by simp)

private theorem quotientWindowRank {E H J : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup H] [NormedSpace ℂ H]
    (T : E →L[ℂ] H) (x : J → H) (Λ : J → StrongDual ℂ H)
    (hb : IsSpectralMarkushevichBasis x Λ) (K : Finset J)
    (hvan : ∀ j ∉ K, ∀ v, Λ j (T v) = 0) :
    FiniteDimensional ℂ T.toLinearMap.range ∧ Module.finrank ℂ T.toLinearMap.range ≤ K.card := by
  classical
  let e : T.toLinearMap.range →ₗ[ℂ] (K → ℂ) :=
    LinearMap.pi fun j ↦ (Λ j.val).toLinearMap.comp T.toLinearMap.range.subtype
  have he : Injective e := by
    intro p q hpq
    apply Subtype.ext
    apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
    have h : ContinuousLinearMap.apply ℂ ℂ p.val = ContinuousLinearMap.apply ℂ ℂ q.val := by
      apply ContinuousLinearMap.ext_on hb.2.2.2
      rintro _ ⟨j,rfl⟩
      by_cases hj : j ∈ K
      · exact congrFun hpq ⟨j,hj⟩
      · obtain ⟨v,hv⟩ := p.property
        obtain ⟨u,hu⟩ := q.property
        change Λ j p.val = Λ j q.val
        rw [← hv, ← hu]
        exact (hvan j hj v).trans (hvan j hj u).symm
    exact fun δ ↦ DFunLike.congr_fun h δ
  exact ⟨Module.Finite.of_injective e he, by
    simpa only [Module.finrank_pi, Fintype.card_coe] using LinearMap.finrank_le_finrank_of_injective he⟩

/-- The output quotient of a single frequency window has rank at most the number
of retained jets where the symbol is not locally zero. This also holds after
precomposition with any bounded choice of representatives. -/
theorem spectralLineQuotient_window_rank_le (a : ℝ) {s : ℝ} (hs : 1 < s)
    (χ : Ω → PontryaginDual C𝔽) (hχ : IsSpectralBasepointChoice χ)
    (k : SchwartzBruhat C𝔽) (A : W(s) →L[ℂ] W(s))
    (hA : ∀ u, HasPettisIntegral (.positive μ𝔽) (fun g ↦ k g • τ(s,hs) g u) (A u))
    (J : Q(a,hs) →L[ℂ] W(s)) (K : Finset (SpectralLineJetIndex χ a s))
    (hoff : ∀ j ∉ K, Isolated.spectralLineWindowMultiplier k (χ j.val.1) =ᶠ[𝓝 j.val.2.1] 0) :
    let T := (Θ(a,hs)).mkQL.comp (A.comp J)
    FiniteDimensional ℂ T.toLinearMap.range ∧ Module.finrank ℂ T.toLinearMap.range ≤ K.card := by
  classical
  obtain ⟨_, x, Λ, hb, hj⟩ := spectralLineMarkushevichBasis (a := a) χ hχ hs
  apply quotientWindowRank _ x Λ hb K
  intro j hjK u
  let z := (⟨(j.val.1,j.val.2.1),SpectralLineJetIndex.order_pos j⟩ :
    {z : Ω × ℝ // 0 < meromorphicOrderAt (continuedCompletedHeckeL (χ z.1)) (shift(a,z.2))})
  let m : Fin (spectralBoundaryMultiplicity s
      (meromorphicOrderAt (continuedCompletedHeckeL (χ z.val.1)) (shift(a,z.val.2))).untop₀.toNat) :=
    ⟨j.val.2.2,j.property⟩
  have hpol := integrable_schwartz_log_weight μ𝔽 m𝔽 k (s / 2)
  have hk := (continuous_schwartzBruhat k).aemeasurable (μ := μ𝔽)
  have hscalar (δ : StrongDual ℂ W(s)) v :
      δ (A v) = ∫ g, k g * δ (τ(s,hs) g v) ∂μ𝔽 := by
    have h := congrArg (fun p : PettisWeakCompletion W(s) ↦
      (show Module.Dual ℂ (StrongDual ℂ W(s)) from p) δ) (hA v).2
    exact h.trans (integral_congr_ae (.of_forall fun g ↦ map_smul δ _ _))
  refine (Isolated.spectralLineWindow_all_jet_coefficients χ hs Λ hj k hk hpol A hscalar z m (J u)).trans ?_
  apply Finset.sum_eq_zero
  intro i _
  let n := m.val - i.val
  have hnm : (n : ℝ) ≤ (m.val : ℝ) := by exact_mod_cast Nat.sub_le m.val i.val
  have hm := ((lt_spectralBoundaryMultiplicity s _ _).mp m.isLt).2
  have hd := Isolated.spectralLineWindowMultiplier_iteratedDeriv k hk hpol (χ j.val.1)
    j.val.2.1 n (by linarith : (n : ℝ) ≤ s / 2)
  have hzero := (hoff j hjK).iteratedDeriv_eq n
  have hmoment : (∫ g, k g * spectralZeroJet (χ j.val.1) 0 j.val.2.1 n g ∂μ𝔽) = 0 := by
    apply (mul_eq_zero.mp _).resolve_left (pow_ne_zero n Complex.I_ne_zero)
    exact hd.symm.trans (hzero.trans (by simp))
  change ((_ : ℂ) * (∫ g, k g * spectralZeroJet (χ j.val.1) 0 j.val.2.1 n g ∂μ𝔽)) * _ = 0
  rw [hmoment, mul_zero, zero_mul]

set_option maxHeartbeats 800000 in
/-- A homogeneous compact Bruhat test acts by a nuclear operator on the actual
line quotient at every real Sobolev order above one (Theorem 10.3.1.1(2),
p. 448). Smooth windows approximate its symbol in the Schwartz topology. -/
theorem spectralLineConvolution_homogeneous_nuclear (a : ℝ) {s : ℝ} (hs : 1 < s)
    (ω : Ω) (φ : BruhatCompactSupport C𝔽)
    (hφ : ∀ (k : C₁) x, φ.val (k.val⁻¹ * x) = (ω k : ℂ) * φ.val x) :
    IsNuclearOperator (spectralConvolution (F := F) a h₀ hs₀(hs) φ) := by
  classical
  obtain ⟨χ,hχ⟩ := exists_spectralBasepointChoice F
  obtain ⟨P,hP,honto⟩ := Isolated.exists_spectralLineWaveProfile χ hχ ω
  obtain ⟨A,hA⟩ := (existsUnique_schwartzBruhat_zeroLineAction μ𝔽 m𝔽 s hs₀(hs)).exists
  let θ : Submodule ℂ W(s) := Θ(a,hs)
  let q := θ.mkQL
  let J : Q(a,hs) →L[ℂ] W(s) := θ.orthogonal.subtypeL.comp
    θ.quotientEquivOrthogonal.toContinuousLinearEquiv.toContinuousLinearMap
  have hqJ (v : Q(a,hs)) : q (J v) = v := θ.quotientEquivOrthogonal.symm_apply_apply v
  let T : 𝓢(ℝ,ℂ) →L[ℂ] (Q(a,hs) →L[ℂ] Q(a,hs)) :=
    ((ContinuousLinearMap.compL ℂ Q(a,hs) W(s) Q(a,hs)) q).comp
      (((ContinuousLinearMap.compL ℂ Q(a,hs) W(s) W(s)).flip J).comp (A.comp P))
  obtain ⟨C,hC,hcount⟩ := spectralLine_jets_quadratic_count χ ω
  have hsmall (p : 𝓢(ℝ,ℂ)) : IsNuclearOperator (T p) := by
    apply isNuclearOperator_schwartz_of_quadratic_window_rank (T.restrictScalars ℝ) C hC _ p
    intro R hR f hf
    let S := {j : SpectralLineJetIndex χ a s | j.val.1 = ω ∧ |j.val.2.1| ≤ R}
    have hSR : S.Finite ∧ (S.ncard : ℝ) ≤ C * (1 + R) ^ 2 := hcount a s R hR
    obtain ⟨hS,hr⟩ := hSR
    have hpol := integrable_schwartz_log_weight μ𝔽 m𝔽 (P f) (s / 2)
    have hk := (continuous_schwartzBruhat (P f)).aemeasurable (μ := μ𝔽)
    have hm (ζ : Ω) (t : ℝ) :
        Isolated.spectralLineWindowMultiplier (P f) (χ ζ) t = if ζ = ω then f t else 0 := by
      have hd := Isolated.spectralLineWindowMultiplier_iteratedDeriv (P f) hk hpol (χ ζ) t 0
        (by rw [Nat.cast_zero]; linarith)
      simpa only [iteratedDeriv_zero, pow_zero, one_mul] using hd.trans (by simpa using hP f ζ t)
    have hK := spectralLineQuotient_window_rank_le a hs χ hχ (P f) (A (P f)) (hA (P f)) J hS.toFinset
    have hvan (j : SpectralLineJetIndex χ a s) (hj : j ∉ hS.toFinset) :
        Isolated.spectralLineWindowMultiplier (P f) (χ j.val.1) =ᶠ[𝓝 j.val.2.1] 0 := by
      by_cases hω : j.val.1 = ω
      · have ht : R < |j.val.2.1| := lt_of_not_ge fun h ↦ hj (hS.mem_toFinset.mpr ⟨hω,h⟩)
        filter_upwards [continuous_abs.continuousAt (Ioi_mem_nhds ht)] with v hv
        rw [hm, ite_eq_left hω]
        exact Classical.byContradiction <| fun hn ↦ (hf v hn).not_ge (le_of_lt hv)
      · exact .of_forall fun t ↦ (hm j.val.1 t).trans (ite_eq_right hω)
    have hr' : ((hS.toFinset.card : ℕ) : ℝ) ≤ C * (1 + R) ^ 2 := by
      rwa [← Set.ncard_eq_toFinset_card S hS]
    exact ⟨(hK hvan).1, (Nat.cast_le.mpr (hK hvan).2).trans hr'⟩
  let hm𝔽 : IsModulation m𝔽 := ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩
  let hms := (ideleGroup_quotient.{_,0} F).2.2.2.2.2.2.2.2.2.1
  let ι := bruhatCompactSupportToModulatedExponentialDecay m𝔽 ({0} : Set ℝ) hm𝔽 hms
  obtain ⟨e,he⟩ := modulatedExponentialDecay_singleton_schwartz m𝔽 hm𝔽 hms 0
  let ψ := e (ι φ)
  have hψ : (ψ : C𝔽 → ℂ) = φ.val :=
    (he (ι φ)).trans ((modulationWeight_zero m𝔽 (ι φ).val).trans
      (funext (bruhatCompactSupportToModulatedExponentialDecay_apply m𝔽 {0} hm𝔽 hms φ)))
  obtain ⟨p,hp⟩ := honto ψ (by simpa only [hψ] using hφ)
  have hact : A ψ = hardySobolevTestAction μ𝔽 m𝔽 0 0 s h₀ hs₀(hs) φ := by
    apply ContinuousLinearMap.ext
    intro u
    have hPettis : HasPettisIntegral (.positive μ𝔽) (fun g ↦ φ.val g • τ(s,hs) g u) (A ψ u) := by
      simpa only [hψ] using hA ψ u
    exact hPettis.unique (bruhatRegularizedAction_apply μ𝔽 τ(s,hs) _ φ u)
  have hT : T p = spectralConvolution (F := F) a h₀ hs₀(hs) φ := by
    ext v
    change q (A (P p) (J v)) = _
    rw [hp, hact]
    exact (spectralConvolution_mkQ (F := F) a h₀ hs₀(hs) φ (J v)).symm.trans
      (congrArg (spectralConvolution (F := F) a h₀ hs₀(hs) φ) (hqJ v))
  exact hT ▸ hsmall p

end RiemannMasullo
