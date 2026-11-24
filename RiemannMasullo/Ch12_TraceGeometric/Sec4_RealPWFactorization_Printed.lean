module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-! # The factor through the flat Schwartz space in §12.4, for the cutoff of Step II

A necessary range condition for the factor through `E` that p. 515 asserts, tested in the model
`F = ℚ`, `S = {∞}` with the spatial cutoff that Step II describes on p. 516, a smoothed ball
equal to one near zero. The condition fails. It is the project's reconstruction of one reading
of the proof, not a statement the paper prints: Definition 9.3.3.1(4)–(6), p. 427, gives the
cutoff annular support, and footnote 2 on p. 514 asks for an inner radius; with a cutoff that
vanishes near zero the counterexample here disappears. See errata entries I218 and I395. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff FourierTransform LineDeriv SchwartzMap Topology

namespace RiemannMasullo

/-- A flat Schwartz function has zero quadratic coefficient even along the positive ray. -/
private theorem realPW_not_flat_of_quadratic_germ (h : 𝓢(ℝ, ℂ))
    (hh : h ∈ realSchwartzFlatAtOrigin) (q : ℝ → ℂ) (hq : ContinuousAt q 0)
    (hq₀ : q 0 ≠ 0) (he : ∀ᶠ x in 𝓝[>] (0 : ℝ), h x = (x ^ 2) • q x) : False := by
  have hd := (mem_realSchwartzFlatAtOrigin_iff h).mp hh
  have ht := taylor_tendsto (s := univ) (x₀ := (0 : ℝ)) (n := 2)
    convex_univ (mem_univ 0) (h.smooth 2).contDiffOn
  have ht₀ : Tendsto (fun x : ℝ ↦ (x ^ 2)⁻¹ • h x) (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simpa [taylor_within_apply, iteratedDerivWithin_univ, hd] using ht
  have heq : (fun x : ℝ ↦ (x ^ 2)⁻¹ • h x) =ᶠ[𝓝[>] (0 : ℝ)] q := by
    filter_upwards [he, eventually_mem_nhdsWithin] with x hx hxpos
    have hx₀ : x ≠ 0 := (mem_Ioi.mp hxpos).ne'
    change (x ^ 2)⁻¹ • h x = q x
    rw [hx, ← mul_smul, inv_mul_cancel₀ (pow_ne_zero _ hx₀), one_smul]
  exact hq₀ (tendsto_nhds_unique (hq.mono_left nhdsWithin_le_nhds)
    ((ht₀.mono_left nhdsWithin_le_nhds).congr' heq))

/-- Paper: Theorem 12.4.1.1, proof, pp. 515–517. In the rational real-place model, the
polar-free invariant Paley–Wiener tests have flat representatives after the cutoff–dilation
composite and removal of the half-twist.
Reconstruction: The paper does not state this. It is a necessary range condition for the
factor through `E` asserted on p. 515, with the upper-ball multipliers that Step II describes
on p. 516. It is not known whether that cutoff is what the author intends: Definition
9.3.3.1(4)–(6), p. 427, and footnote 2 on p. 514 put a positive inner radius, and a spatial
cutoff that vanishes near zero removes the counterexample below.
Deviation: Use positive representatives for the quotient by `±1`, so even Schwartz tests
give the level by sign averaging, up to a scalar. The two upper cutoffs are radial bumps, and
the spatial one equals one near zero.
The real dilation test `φ` absorbs the factor `g⁻³ᐟ²` from untwisting and Haar measure.
Any factor through `E` would supply a flat representative almost everywhere on the positive
ray, where the weighted measure and Lebesgue measure have the same null sets. -/
def sLocalTrace_realUpperBallPWFlatRange : Prop :=
  ∀ (ρ m : ContDiffBump (0 : ℝ)) (φ : 𝓢(ℝ, ℝ)), tsupport (φ : ℝ → ℝ) ⊆ Icc 1 2 →
    (∀ g, 0 ≤ φ g) →
    ∀ (f : 𝓢(ℝ, ℂ)), Function.Even f → f 0 = 0 → (𝓕 f) 0 = 0 →
      tsupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ⊆ Icc (-m.rIn) m.rIn →
      ∃ h : 𝓢(ℝ, ℂ), h ∈ realSchwartzFlatAtOrigin ∧
        ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))),
        h x = ρ x • ∫ g in Icc (1 : ℝ) 2,
          φ g • (𝓕⁻ (fun ξ : ℝ ↦ m ξ • (𝓕 f) ξ)) (x / g)

/-- The input Fourier cutoff fixes every test supported in its plateau. -/
private theorem realPW_fourierCutoff_eq (m : ContDiffBump (0 : ℝ)) (f : 𝓢(ℝ, ℂ))
    (hf : tsupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ⊆ Icc (-m.rIn) m.rIn) :
    (𝓕⁻ (fun ξ : ℝ ↦ m ξ • (𝓕 f : 𝓢(ℝ, ℂ)) ξ) : ℝ → ℂ) = (f : ℝ → ℂ) := by
  have hm : (fun ξ : ℝ ↦ m ξ • (𝓕 f : 𝓢(ℝ, ℂ)) ξ) = ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) := by
    funext ξ
    by_cases hξ : ξ ∈ tsupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ)
    · have hball : ξ ∈ Metric.closedBall 0 m.rIn := by
        rw [Real.closedBall_eq_Icc, zero_sub, zero_add]
        exact hf hξ
      rw [m.one_of_mem_closedBall hball, one_smul]
    · have hz := image_eq_zero_of_notMem_tsupport hξ
      rw [hz, smul_zero]
  rw [hm, ← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_fourier_eq]

/-- The inverse transform of the second derivative of an even frequency bump is polar-free
and begins with a nonzero quadratic coefficient. -/
private theorem realPW_bandlimited_quadratic_witness :
    ∃ f q : 𝓢(ℝ, ℂ), tsupport (𝓕 f : 𝓢(ℝ, ℂ)) ⊆ Icc (-1) 1 ∧
      (𝓕 f) 0 = 0 ∧ q 0 ≠ 0 ∧
      (∀ x : ℝ, f x = (x : ℂ) ^ 2 * q x) ∧ (∀ x : ℝ, f (-x) = f x) := by
  let B : ContDiffBump (0 : ℝ) := ⟨1 / 2, 1, by norm_num, by norm_num⟩
  let b : 𝓢(ℝ, ℂ) := (B.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp B.contDiff)
  have hb (x : ℝ) : b x = (B x : ℂ) := rfl
  have hsupport : tsupport (b : ℝ → ℂ) ⊆ Icc (-1) 1 := by
    have hts : tsupport (b : ℝ → ℂ) = tsupport (B : ℝ → ℝ) := by
      apply congrArg closure
      ext x
      simp [Function.mem_support, hb]
    rw [hts, B.tsupport_eq, Real.closedBall_eq_Icc]
    norm_num [B]
  have hb_one : (b : ℝ → ℂ) =ᶠ[𝓝 0] (fun _ : ℝ ↦ (1 : ℂ)) := by
    filter_upwards [B.eventuallyEq_one_of_mem_ball (Metric.mem_ball_self B.rIn_pos)] with x hx
    rw [hb, show B x = 1 from hx]
    norm_num
  have hD (a : 𝓢(ℝ, ℂ)) : ((∂_{(1 : ℝ)} a : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = deriv a := by
    funext x
    rw [SchwartzMap.lineDerivOp_apply_eq_fderiv, fderiv_apply_one_eq_deriv]
  let c : ℂ := -(2 * (Real.pi : ℂ) * Complex.I)
  let f : 𝓢(ℝ, ℂ) := 𝓕⁻ (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} b))
  let q : 𝓢(ℝ, ℂ) := c ^ 2 • 𝓕⁻ b
  have hF : 𝓕 f = (∂_{(1 : ℝ)} (∂_{(1 : ℝ)} b) : 𝓢(ℝ, ℂ)) := FourierTransform.fourier_fourierInv_eq _
  have hi : (fun x : ℝ ↦ x).HasTemperateGrowth := by fun_prop
  have hStep (z : 𝓢(ℝ, ℂ)) (x : ℝ) :
      (𝓕⁻ (∂_{(1 : ℝ)} z) : 𝓢(ℝ, ℂ)) x = c * (x : ℂ) * (𝓕⁻ z) x := by
    rw [SchwartzMap.fourierInv_lineDerivOp_eq]
    simp [c, hi, smul_eq_mul, mul_assoc]
  have hshape (x : ℝ) : f x = (x : ℂ) ^ 2 * q x := by
    dsimp only [f, q]
    rw [hStep, hStep]
    rw [smul_apply, smul_eq_mul]
    ring
  have hbg (x : ℝ) : b (-x) = b x := by simp only [hb, B.neg]
  have hinv : 𝓕⁻ (b : ℝ → ℂ) = 𝓕 (b : ℝ → ℂ) := by
    rw [Real.fourierInv_eq_fourier_comp_neg, show (fun x ↦ b (-x)) = (b : ℝ → ℂ) from funext hbg]
  have hq_even (x : ℝ) : q (-x) = q x := by
    dsimp only [q]
    simp only [smul_apply, SchwartzMap.fourierInv_coe]
    rw [Real.fourierInv_eq_fourier_neg, neg_neg, hinv]
  have hc : c ≠ 0 := neg_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero)
  have hInt : 0 < ∫ x : ℝ, B x :=
    B.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero B.hasCompactSupport
      (fun x ↦ B.nonneg) (show B 0 ≠ 0 by
        rw [B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)]; norm_num)
  have hb_zero : (𝓕⁻ b : 𝓢(ℝ, ℂ)) 0 ≠ 0 := by
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq_fourier_neg, neg_zero,
      Real.fourier_real_eq]
    simp only [mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul, hb, integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr hInt.ne'
  refine ⟨f, q, ?_, ?_, ?_, hshape, ?_⟩
  · rw [hF]
    exact (SchwartzMap.tsupport_lineDerivOp_subset _ _).trans
      ((SchwartzMap.tsupport_lineDerivOp_subset _ _).trans hsupport)
  · rw [hF]
    change ((∂_{(1 : ℝ)} (∂_{(1 : ℝ)} b) : 𝓢(ℝ, ℂ)) : ℝ → ℂ) 0 = 0
    rw [hD, hD]
    simpa using hb_one.deriv.deriv_eq
  · exact mul_ne_zero (pow_ne_zero _ hc) hb_zero
  · intro x
    rw [hshape, hshape, hq_even]
    push_cast
    rw [neg_sq]

/-- A nonnegative dilation test gives a continuous quadratic factor nonzero at the origin. -/
private theorem realPW_dilationTest (q : 𝓢(ℝ, ℂ)) (hq : q 0 ≠ 0) :
    ∃ φ : 𝓢(ℝ, ℝ), tsupport (φ : ℝ → ℝ) ⊆ Icc 1 2 ∧ (∀ t, 0 ≤ φ t) ∧
      let C (x : ℝ) := ∫ t in Icc (1 : ℝ) 2, ((φ t : ℂ) / (t : ℂ) ^ 2) * q (x / t)
      Continuous C ∧ C 0 ≠ 0 := by
  let B : ContDiffBump (3 / 2 : ℝ) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩
  let φ : 𝓢(ℝ, ℝ) := (B.hasCompactSupport.mul_left :
    HasCompactSupport (fun t : ℝ ↦ t ^ 2 * B t)).toSchwartzMap
    ((contDiff_id.pow 2).mul B.contDiff)
  have hBsupport : tsupport (B : ℝ → ℝ) ⊆ Icc 1 2 := by
    rw [B.tsupport_eq, Real.closedBall_eq_Icc]
    refine Icc_subset_Icc ?_ ?_ <;> norm_num [B]
  have hφsupport : tsupport (φ : ℝ → ℝ) ⊆ Icc 1 2 := by
    change tsupport ((fun t : ℝ ↦ t ^ 2) * (B : ℝ → ℝ)) ⊆ Icc 1 2
    exact tsupport_mul_subset_right.trans hBsupport
  refine ⟨φ, hφsupport, fun t ↦ mul_nonneg (sq_nonneg t) B.nonneg, ?_⟩
  let C (x : ℝ) : ℂ := ∫ t in Icc (1 : ℝ) 2, ((B t : ℝ) : ℂ) * q (x / max 1 t)
  have heq (x : ℝ) : (∫ t in Icc (1 : ℝ) 2, ((φ t : ℂ) / (t : ℂ) ^ 2) * q (x / t)) = C x := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    change ((↑(t ^ 2 * B t) : ℂ) / (t : ℂ) ^ 2) * q (x / t) =
      (B t : ℂ) * q (x / max 1 t)
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [ht.1])
    push_cast
    rw [max_eq_right ht.1, mul_div_cancel_left₀ _ (pow_ne_zero 2 ht0)]
  simp only [heq]
  constructor
  · have hden : Continuous (fun p : ℝ × ℝ ↦ max (1 : ℝ) p.2) :=
      continuous_const.max continuous_snd
    have harg : Continuous (fun p : ℝ × ℝ ↦ p.1 / max 1 p.2) :=
      continuous_fst.div hden fun p ↦ ne_of_gt (zero_lt_one.trans_le (le_max_left (1 : ℝ) p.2))
    exact continuous_parametric_integral_of_continuous
      (f := fun x t : ℝ ↦ ((B t : ℝ) : ℂ) * q (x / max 1 t))
      ((Complex.continuous_ofReal.comp (B.continuous.comp continuous_snd)).mul
        (q.continuous.comp harg)) isCompact_Icc
  · have hfull : (∫ t in Icc (1 : ℝ) 2, B t) = ∫ t, B t := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      exact Function.notMem_support.mp (fun hn ↦ ht (hBsupport (subset_tsupport _ hn)))
    change (∫ t in Icc (1 : ℝ) 2, ((B t : ℝ) : ℂ) * q (0 / max 1 t)) ≠ 0
    simp only [zero_div, integral_mul_const, integral_complex_ofReal, hfull]
    have hpos : 0 < ∫ t : ℝ, B t :=
      B.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero B.hasCompactSupport
        (fun _ ↦ B.nonneg) (by
          rw [B.one_of_mem_closedBall (Metric.mem_closedBall_self B.rIn_pos.le)]
          norm_num)
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne') hq

/-- Paper: Theorem 12.4.1.1, proof, pp. 515–517. A polar-free test supported in the Fourier
plateau has a nonzero quadratic term after convolution. The spatial upper cutoff is one near
zero, so its output has no flat representative, even up to almost-everywhere equality. This
refutes the reconstruction `sLocalTrace_realUpperBallPWFlatRange`, that is, the factor through
`E` for the upper-ball cutoff of Step II; it does not concern a cutoff with an inner radius. -/
theorem sLocalTrace_realUpperBallPWFlatRange_false :
    ¬ sLocalTrace_realUpperBallPWFlatRange := by
  intro hfactor
  obtain ⟨f, q, hband, hfreq, hq₀, hf, hfe⟩ := realPW_bandlimited_quadratic_witness
  obtain ⟨φ, hφ, hφnonneg, hC, hC₀⟩ := realPW_dilationTest q hq₀
  let B : ContDiffBump (0 : ℝ) := ⟨7 / 4, 2, by norm_num, by norm_num⟩
  have hband' : tsupport ((𝓕 f : 𝓢(ℝ, ℂ)) : ℝ → ℂ) ⊆ Icc (-B.rIn) B.rIn :=
    hband.trans (Icc_subset_Icc (by norm_num [B]) (by norm_num [B]))
  obtain ⟨h, hflat, he⟩ := hfactor B B φ hφ hφnonneg f hfe (by simp [hf]) hfreq hband'
  let C (x : ℝ) : ℂ := ∫ g in Icc (1 : ℝ) 2, ((φ g : ℂ) / (g : ℂ) ^ 2) * q (x / g)
  have hd (x : ℝ) : (∫ g in Icc (1 : ℝ) 2, φ g • f (x / g)) = (x ^ 2) • C x := by
    dsimp only [C]
    rw [← integral_smul]
    apply setIntegral_congr_fun measurableSet_Icc
    intro g hg
    have hg₀ : (g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [hg.1])
    simp only [hf, Complex.real_smul, Complex.ofReal_pow, Complex.ofReal_div]
    field_simp
  have hae : (h : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x : ℝ ↦ B x • ((x ^ 2) • C x)) := by
    change ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), h x = B x • ((x ^ 2) • C x)
    simpa only [realPW_fourierCutoff_eq B f hband', hd] using he
  have hout : Continuous (fun x : ℝ ↦ B x • ((x ^ 2) • C x)) :=
    B.continuous.smul ((continuous_id.pow 2).smul hC)
  have heq := Measure.eqOn_open_of_ae_eq hae isOpen_Ioi h.continuous.continuousOn
    hout.continuousOn
  apply realPW_not_flat_of_quadratic_germ h hflat C hC.continuousAt hC₀
  filter_upwards [B.eventuallyEq_one.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin]
    with x hx hxpos
  rw [heq hxpos]
  change B x • ((x ^ 2) • C x) = (x ^ 2) • C x
  rw [show B x = 1 from hx, one_smul]

end RiemannMasullo
