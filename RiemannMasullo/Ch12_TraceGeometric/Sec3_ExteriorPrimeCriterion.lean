module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ExteriorPrimeTrace
import RiemannMasullo.ForMathlib.Analysis.Fourier.SparseLaplaceProbe
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic

/-! # A fixed-window criterion for the signed exterior comparison

Even with both poles killed and a finite list of critical Mellin values prescribed,
one may test each missing right-hand order in any positive log window. -/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.RationalWidthLoss
set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Z" => {ρ : ℂ // 0 < MeromorphicOn.divisor completedRiemannZeta univ ρ}
local notation "w(" ρ ")" => ((ρ : Z).val - (1/2 : ℂ))
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  (H : ℝ → ℂ) (logIdeleClassNorm ℚ x)
local notation "freq(" t ")" => (((t : ℝ) : ℂ)*Complex.I)
local notation "B(" H ", " z ")" => bilateralLaplace H z

/-- The physical prime comparison for all normalized polar-free probes in one
fixed log window with a prescribed finite list of critical Mellin samples. -/
def UniversalExteriorPrimeMatch {ι : Type*} [Fintype ι] (γ : ι → ℝ) (v : ι → ℂ)
    {a : ℝ} (ha : 0 ≤ a) (c ε : ℝ) : Prop :=
  ∀ (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ), ContDiff ℝ (∞) H →
    tsupport H ⊆ Icc (c-ε) (c+ε) → H c = 1 → radial(φ,H) →
    B(H,1/2) = 0 → B(H,-(1/2)) = 0 → (∀ j, B(H,freq(γ j)) = v j) →
    IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2):ℂ) *
      (exteriorStripTrace ha φ y + V*rationalFirstPrimeSum (fun x ↦ H (x-y)))) (Ioi 0)

private theorem zero_re_lt_one (ρ : Z) : ρ.val.re < 1 := by
  apply (re_mem_Ioo ⟨ρ.val,?_⟩).2
  change 0 < MeromorphicOn.divisor _ _ _
  rw [principal_divisor_eq_completedRiemannZeta]
  exact ρ.property

private theorem exists_isolating_probe {ι : Type*} [Fintype ι] (γ : ι → ℝ) (hγ : Injective γ)
    (v : ι → ℂ) (ρ : Z) (hρ : 1/2 < ρ.val.re) {δ : ℝ} (hδ : 0 < δ) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ tsupport H ⊆ Icc (c-ε) (c+ε) ∧ H c = 1 ∧
      B(H,1/2) = 0 ∧ B(H,-(1/2)) = 0 ∧ (∀ j, B(H,freq(γ j)) = v j) ∧ B(H,w(ρ)) = 1 ∧
      ∀ z : Z, δ ≤ |z.val.re-1/2| → z ≠ ρ → B(H,w(z)) = 0 := by
  let r : Option ι → ℂ := fun j ↦ j.elim w(ρ) (fun k ↦ freq(γ k))
  let E := {z : Z // δ ≤ |z.val.re-1/2| ∧ z ≠ ρ}
  let p : E ⊕ Bool → ℂ := Sum.elim (fun z ↦ w(z.val)) (fun b ↦ if b then 1/2 else -(1/2))
  have hs : Summable fun i ↦ 1/(1+|(p i).im|) := by
    apply Summable.sum _
    · let j (z : E) : {s : zeroSites // δ ≤ |s.val.re-1/2|} :=
        ⟨⟨z.val.val,by
          change 0 < MeromorphicOn.divisor _ _ _
          rw [principal_divisor_eq_completedRiemannZeta]
          exact z.val.property⟩,z.property.1⟩
      have hj : Injective j := fun _ _ he ↦ Subtype.ext (Subtype.ext (congrArg (fun t ↦ t.val.val) he))
      simpa [Function.comp_def,p,j] using
        (summable_exterior_inverse_height_unconditional hδ).comp_injective hj
    · exact (hasSum_fintype _).summable
  have hre : w(ρ).re = ρ.val.re-1/2 := by norm_num
  have hpos : 0 < w(ρ).re := by linarith
  have hlt : w(ρ).re < 1/2 := by linarith [zero_re_lt_one ρ]
  have sep (j : ι) : w(ρ) ≠ freq(γ j) := by
    intro he
    have h := congrArg Complex.re he
    norm_num at h
    linarith
  have hr : Injective r := by
    intro i j he
    cases i with
    | none =>
      cases j with
      | none => rfl
      | some j => exact (sep j he).elim
    | some i =>
      cases j with
      | none => exact (sep i he.symm).elim
      | some j =>
        have h : γ i = γ j := by simpa [r] using congrArg Complex.im he
        exact congrArg some (hγ h)
  have hw (i) (j : Option ι) : p i ≠ r j := by
    rcases i with z | b
    · cases j with
      | none =>
        intro he
        exact z.property.2 (Subtype.ext (sub_left_inj.mp he))
      | some k =>
        intro he
        have hre := congrArg Complex.re he
        norm_num [p,r] at hre
        have hz := z.property.1
        rw [show z.val.val.re-1/2 = 0 by linarith, abs_zero] at hz
        exact hδ.not_ge hz
    · intro he
      have h := congrArg Complex.re he
      cases b <;> cases j <;> norm_num [p,r] at h <;> linarith
  have hw₀ (i) : p i ≠ (2 : ℝ) := by
    rcases i with z | b
    · intro he
      have h := congrArg Complex.re he
      norm_num [p] at h
      linarith [zero_re_lt_one z.val]
    · cases b <;> norm_num [p]
  have hr₀ (j : Option ι) : r j ≠ (2 : ℝ) := by
    intro he
    have h := congrArg Complex.re he
    cases j <;> norm_num [r] at h; linarith
  obtain ⟨H,hH,hb,hc,hp,hrv⟩ := SparseLaplace.exists_complex_interpolating_probe p
    hs r hr hw 2 hw₀ hr₀ (fun j : Option ι ↦ j.elim 1 v) c hε
  exact ⟨H,hH,hb,hc,by simpa [p] using hp (.inr true),by simpa [p] using hp (.inr false),
    fun j ↦ hrv (some j),hrv none,fun z hz hn ↦ hp (.inl ⟨z,hz,hn⟩)⟩

/-- The signed exponential coefficient of a trace can be recovered by averaging
against the inverse character whenever its real exponent dominates the detector. -/
theorem tendsto_demodulated_trace_average {F : ℝ → ℂ} {a : ℝ} {w k : ℂ}
    (hw : a/2 ≤ w.re)
    (h : IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2) : ℂ) *
      (F y + k * Complex.exp (w*y))) (Ioi 0)) :
    Tendsto (fun Y : ℝ ↦ (∫ y in (0:ℝ)..Y, Complex.exp (-w*y) * F y) / (Y:ℂ))
      atTop (𝓝 (-k)) := by
  let d (y : ℝ) : ℂ := Complex.exp (((a/2:ℝ):ℂ)*y-w*y)
  let G (y : ℝ) := Complex.exp (-w*y)*F y + k
  have hd : Continuous d := by unfold d; fun_prop
  have hb : ∀ᵐ y ∂volume.restrict (Ioi (0:ℝ)), ‖d y‖ ≤ 1 := by
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with y hy
    change ‖Complex.exp _‖ ≤ 1
    rw [Complex.norm_exp,Real.exp_le_one_iff]
    simp only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    nlinarith [mul_nonneg (sub_nonneg.mpr hw) (le_of_lt hy)]
  have hG : IntegrableOn G (Ioi 0) := by
    apply (h.bdd_mul hd.aestronglyMeasurable hb).congr
    filter_upwards with y
    dsimp [d,G]
    rw [← mul_assoc,Complex.ofReal_exp,← Complex.exp_add]
    push_cast
    rw [show (a:ℂ)/2*y-w*y+(-(a:ℂ)*y/2) = -w*y by ring, mul_add]
    rw [show Complex.exp (-w*y)*(k*Complex.exp (w*y)) =
      k*(Complex.exp (-w*y)*Complex.exp (w*y)) by ring, ← Complex.exp_add]
    simp
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hG (show Tendsto (fun x : ℝ ↦ x) atTop atTop from tendsto_id)
  have hinv : Tendsto (fun Y : ℝ ↦ ((Y : ℂ)⁻¹)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp (tendsto_inv_atTop_zero (𝕜 := ℝ))
  have hzero := (hlim.mul hinv).sub_const k
  simp only [mul_zero,zero_sub] at hzero
  apply hzero.congr'
  filter_upwards [eventually_gt_atTop (0:ℝ)] with Y hY
  have hloc : IntervalIntegrable G volume 0 Y :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hY.le).mpr (hG.mono_set Ioc_subset_Ioi_self)
  have he : (fun y : ℝ ↦ Complex.exp (-w*y)*F y) = (fun y ↦ G y - k) := by
    funext y; simp [G]
  change _ = (∫ y in (0:ℝ)..Y, (fun y : ℝ ↦ Complex.exp (-w*y)*F y) y)/(Y:ℂ)
  rw [he,intervalIntegral.integral_sub hloc intervalIntegrable_const,intervalIntegral.integral_const,sub_zero,
    Complex.real_smul]
  have hn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  field_simp

/-- A single compact test isolates the signed contribution of a chosen right-hand
zero in the actual exterior trace. All other omitted orders disappear simultaneously
at every half-width above the chosen threshold. -/
theorem exists_exterior_single_zero_trace {ι : Type*} [Fintype ι] (γ : ι → ℝ)
    (hγ : Injective γ) (v : ι → ℂ) (ρ : Z) (hρ : 1/2 < ρ.val.re) {δ c ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) (hl : ε < c) :
    ∃ (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ), ContDiff ℝ (∞) H ∧
      tsupport H ⊆ Icc (c-ε) (c+ε) ∧ H c = 1 ∧ radial(φ,H) ∧
      B(H,1/2) = 0 ∧ B(H,-(1/2)) = 0 ∧ (∀ j, B(H,freq(γ j)) = v j) ∧ B(H,w(ρ)) = 1 ∧
      ∀ {a : ℝ} (ha : δ ≤ a),
        let E := fun y : ℝ ↦ exteriorStripTrace (hδ.le.trans ha) φ y + V*rationalFirstPrimeSum (fun x ↦ H (x-y))
        let k := V * (omittedOrder a ρ : ℂ)
        IntegrableOn (fun y : ℝ ↦ (Real.exp (-a*y/2) : ℂ) * (E y + k * Complex.exp (w(ρ)*y))) (Ioi 0) ∧
          (a/2 ≤ w(ρ).re → Tendsto (fun Y : ℝ ↦ (∫ y in (0:ℝ)..Y, Complex.exp (-w(ρ)*y) * E y)/(Y:ℂ))
            atTop (𝓝 (-k))) := by
  obtain ⟨H,hH,hb,hc,hp,hm,hv,hone,hkill⟩ := exists_isolating_probe γ hγ v ρ hρ hδ c hε
  obtain ⟨φ,hφ⟩ := exists_normTest (F := ℚ) H hH (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hb)
  refine ⟨H,φ,hH,hb,hc,hφ,hp,hm,hv,hone,?_⟩
  intro a ha
  have he (y : ℝ) : omittedMellinTrace a H y =
      V * (omittedOrder a ρ : ℂ) * Complex.exp (w(ρ)*y) := by
    unfold omittedMellinTrace
    rw [tsum_eq_single ρ]
    · rw [SparseLaplace.bilateralLaplace_translate,hone,one_mul,mul_assoc]
    · intro z hz
      rw [SparseLaplace.bilateralLaplace_translate]
      by_cases h : δ ≤ |z.val.re-1/2|
      · rw [hkill z h hz]; simp
      · have hmid := abs_lt.mp (lt_of_lt_of_le (lt_of_not_ge h) ha)
        rw [omittedOrder,spectralStripMultiplicity_interior (show z.val.re-1/2 ∈ Ioo (-a) a from hmid),Nat.sub_self]
        simp
  have h := integrable_exterior_first_add_omitted (hδ.trans_le ha) (sub_pos.mpr hl) H hH hb hp φ hφ
  simp only [he] at h
  exact ⟨h,fun hw ↦ tendsto_demodulated_trace_average hw h⟩

/-- Universal matching at one width, in any one positive log window, is equivalent
to full retention of the order of every right-hand zeta zero. The statement
includes the partially retained boundary orders. -/
theorem universalExteriorPrimeMatch_iff {ι : Type*} [Fintype ι] (γ : ι → ℝ) (hγ : Injective γ) (v : ι → ℂ)
    {a c ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (hl : ε < c) :
    UniversalExteriorPrimeMatch γ v ha.le c ε ↔ ∀ ρ : Z, 1/2 < ρ.val.re → omittedOrder a ρ = 0 := by
  constructor
  · intro hall ρ hρ
    by_contra! hm
    obtain ⟨H,hH,hb,hc,hp,hm',hv,hone,_⟩ := exists_isolating_probe γ hγ v ρ hρ ha c hε
    obtain ⟨φ,hφ⟩ := exists_normTest (F := ℚ) H hH (isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hb)
    have h := (exterior_firstPrime_iff_right_samples ha (sub_pos.mpr hl) H hH hb hp φ hφ).mp
      (hall H φ hH hb hc hφ hp hm' hv) ρ hρ (Nat.pos_of_ne_zero hm)
    exact one_ne_zero (hone.symm.trans h)
  · intro hall H φ hH hb _ hφ hp _ _
    apply (exterior_firstPrime_iff_right_samples ha (sub_pos.mpr hl) H hH hb hp φ hφ).mpr
    intro ρ hρ hpos
    exact (hpos.ne' (hall ρ hρ)).elim

/-- Universal signed matching on arbitrarily narrow strips, in one fixed positive
log window and with fixed critical samples, is equivalent to Mathlib's Riemann
hypothesis. The widths may depend on the requested upper bound. -/
theorem riemannHypothesis_iff_arbitrarilyNarrow_exteriorPrimeMatch {ι : Type*} [Fintype ι]
    (γ : ι → ℝ) (hγ : Injective γ) (v : ι → ℂ) {c ε : ℝ} (hε : 0 < ε) (hl : ε < c) :
    RiemannHypothesis ↔ ∀ η : ℝ, 0 < η → ∃ a : ℝ, ∃ ha : 0 < a,
      a < η ∧ UniversalExteriorPrimeMatch γ v ha.le c ε := by
  rw [riemannHypothesis_iff_right_divisor]
  constructor
  · intro hz η hη
    refine ⟨η/2,half_pos hη,half_lt_self hη,
      (universalExteriorPrimeMatch_iff γ hγ v (half_pos hη) hε hl).mpr ?_⟩
    intro ρ hρ
    exact (hρ.not_ge (hz ρ.val ρ.property)).elim
  · intro h z hz
    by_contra! hr
    obtain ⟨a,ha,hlt,hm⟩ := h (z.re-1/2) (sub_pos.mpr hr)
    let ρ : Z := ⟨z,hz⟩
    have he := (universalExteriorPrimeMatch_iff γ hγ v ha hε hl).mp hm ρ hr
    have ho : spectralStripMultiplicity a 3 (z.re-1/2)
        (MeromorphicOn.divisor completedRiemannZeta univ z).toNat = 0 := by
      unfold spectralStripMultiplicity
      split_ifs <;> grind
    change (MeromorphicOn.divisor completedRiemannZeta univ z).toNat - _ = 0 at he
    rw [show ρ.val = z from rfl,ho,Nat.sub_zero] at he
    exact (Int.pos_iff_toNat_pos.mp hz).ne' he

end RiemannMasullo.RationalWidthLoss
