module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWCompression
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWSmoothedAction
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Data.Nat.Find

/-! # Nuclear sharp and smoothed compressions for the rational real weighted band -/

public noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal FourierTransform InnerProductSpace SchwartzMap Topology

namespace RiemannMasullo.Isolated

private theorem firstJet_lower {u : ℝ → ℂ} {k : ℕ} (hu : ContDiff ℝ k u)
    (hprev : ∀ i < k, iteratedDeriv i u 0 = 0) (hk : iteratedDeriv k u 0 ≠ 0) :
    ∃ c > 0, ∃ δ > 0, ∀ x ∈ Ioo 0 δ, c * x ^ k ≤ ‖u x‖ := by
  let a := (k.factorial : ℝ)⁻¹ • iteratedDeriv k u 0
  have ha : 0 < ‖a‖ := norm_pos_iff.mpr (smul_ne_zero (by positivity) hk)
  have ht (x : ℝ) : taylorWithinEval u k univ 0 x = x ^ k • a := by
    rw [taylor_within_apply, Finset.sum_range_succ]
    simp only [iteratedDerivWithin_univ, sub_zero]
    rw [Finset.sum_eq_zero (fun i hi ↦ by rw [hprev i (Finset.mem_range.mp hi), smul_zero]), zero_add]
    simp only [a, smul_smul, mul_comm]
  have hrem := (taylor_isLittleO_univ (x₀ := 0) hu).bound (half_pos ha)
  obtain ⟨δ, hδ, hb⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp
    (hrem.filter_mono nhdsWithin_le_nhds)
  refine ⟨‖a‖ / 2, half_pos ha, δ, hδ, fun x hx ↦ ?_⟩
  have h := hb hx
  change ‖u x - taylorWithinEval u k univ 0 x‖ ≤ ‖a‖ / 2 * ‖(x - 0) ^ k‖ at h
  rw [ht, sub_zero, Real.norm_of_nonneg (pow_nonneg hx.1.le k)] at h
  have htri := norm_sub_le (u x) (u x - x ^ k • a)
  rw [sub_sub_cancel, norm_smul, Real.norm_of_nonneg (pow_nonneg hx.1.le k)] at htri
  nlinarith

private theorem weighted_firstJet_exponent {α s : ℝ} (hs : 0 ≤ s) {u : ℝ → ℂ} {k : ℕ}
    (hu : ContDiff ℝ k u) (hprev : ∀ i < k, iteratedDeriv i u 0 = 0)
    (hk : iteratedDeriv k u 0 ≠ 0)
    (hi : Integrable (fun x ↦ realPWIntervalWeight α s x * ‖u x‖ ^ 2)) :
    -1 < 2 * (k : ℝ) - 2 * α := by
  obtain ⟨c, hc, δ, hδ, hb⟩ := firstJet_lower hu hprev hk
  apply (intervalIntegral.integrableOn_Ioo_rpow_iff hδ).mp
  apply ((hi.const_mul ((c ^ 2)⁻¹)).integrableOn).mono'
    ((measurable_id.pow_const (_ : ℝ)).aestronglyMeasurable)
  filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with x hx
  have hx0 : 0 < x := hx.1
  have hw : x ^ (-(2 * α)) ≤ realPWIntervalWeight α s x := by
    rw [realPWIntervalWeight_eq α s hx0.ne', abs_of_pos hx0]
    calc
      _ = x ^ (-(2 * α)) * 1 := (mul_one _).symm
      _ ≤ _ := mul_le_mul (le_max_right _ _) (Real.one_le_rpow (by nlinarith [sq_nonneg (Real.log x)]) (by positivity)) zero_le_one ((Real.rpow_nonneg hx0.le _).trans (le_max_right _ _))
  have hsquare := pow_le_pow_left₀ (mul_nonneg hc.le (pow_nonneg hx0.le k)) (hb x hx) 2
  rw [mul_pow] at hsquare
  change ‖x ^ (2 * (k : ℝ) - 2 * α)‖ ≤
    (c ^ 2)⁻¹ * (realPWIntervalWeight α s x * ‖u x‖ ^ 2)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), ← div_eq_inv_mul, le_div_iff₀ (sq_pos_of_pos hc)]
  calc
    x ^ (2 * (k : ℝ) - 2 * α) * c ^ 2 = x ^ (-(2 * α)) * (c ^ 2 * (x ^ k) ^ 2) := by
      rw [sub_eq_add_neg, Real.rpow_add hx0, mul_comm (2 : ℝ) (k : ℝ), Real.rpow_mul hx0.le, Real.rpow_natCast, Real.rpow_two]
      ring
    _ ≤ _ := mul_le_mul hw hsquare (by positivity) ((Real.rpow_nonneg hx0.le _).trans hw)

/-- Singular weighted square integrability forces all jets below `2*n` to vanish. -/
theorem realPWInterval_forcedOriginJets (Y α s : ℝ) (_ha : 0 ≤ α) (hs : 0 ≤ s)
    (n : ℕ) (hexp : ∀ j < n, 4 * (j : ℝ) - 2 * α ≤ -1)
    (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) :
    ∀ k < 2 * n, iteratedDeriv k (fun x ↦ RealPWBand.evaluation Y
      (volume_le_realPWIntervalMeasure α s hs) x f) 0 = 0 := by
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let u := fun x ↦ RealPWBand.evaluation Y hμ x f
  have hsq : Integrable (fun x ↦ ‖u x‖ ^ 2) (realPWIntervalMeasure α s) := by
    apply ((Lp.memLp f.val).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).congr
    exact (RealPWBand.evaluation_ae Y hμ (realPWIntervalMeasure_absolutelyContinuous α s) f).symm.mono
      fun _ h ↦ congrArg (fun z : ℂ ↦ ‖z‖ ^ 2) h
  let ρ := fun x ↦ ENNReal.ofReal (realPWIntervalWeight α s x)
  have hρ : Measurable ρ := ENNReal.measurable_ofReal.comp (measurable_realPWIntervalWeight α s)
  have hw (x : ℝ) : (ρ x).toReal = realPWIntervalWeight α s x :=
    ENNReal.toReal_ofReal (zero_le_one.trans (one_le_realPWIntervalWeight α s hs x))
  have hi : Integrable (fun x ↦ realPWIntervalWeight α s x * ‖u x‖ ^ 2) := by
    simpa only [hw, smul_eq_mul] using (integrable_withDensity_iff_integrable_smul' hρ
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).mp hsq
  change ∀ k < 2 * n, iteratedDeriv k u 0 = 0
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hkn
    let j := k / 2
    by_cases he : k = 2 * j
    · by_contra hk
      have h := weighted_firstJet_exponent hs (RealPWBand.contDiff_evaluation Y hμ f k)
        (fun i hi' ↦ ih i hi' (hi'.trans hkn)) hk hi
      have hj : j < n := by omega
      have hbad := hexp j hj
      rw [he, Nat.cast_mul, Nat.cast_ofNat] at h
      linarith
    · have hodd : k = 2 * j + 1 := by dsimp [j] at *; omega
      have heven : (fun x ↦ u (-x)) = u := funext (RealPWBand.evaluation_even Y hμ f)
      have h := iteratedDeriv_comp_neg (2 * j + 1) u 0
      rw [heven, neg_zero, pow_add, pow_mul] at h
      norm_num [neg_smul] at h
      rw [hodd]
      linear_combination h / 2

private theorem exists_realPWOrigin_power (α : ℝ) : ∃ n : ℕ, -1 < 4 * (n : ℝ) - 2 * α := by
  obtain ⟨n, hn⟩ := exists_nat_gt (α / 2)
  exact ⟨n, by linarith⟩

/-- The number of even jets excluded by the real interval density at the origin. -/
def realPWOriginJetCount (α : ℝ) : ℕ := Nat.find (exists_realPWOrigin_power α)

theorem realPWOriginJetCount_spec (α : ℝ) :
    -1 < 4 * (realPWOriginJetCount α : ℝ) - 2 * α :=
  Nat.find_spec (exists_realPWOrigin_power α)

theorem realPWOriginJetCount_min (α : ℝ) {j : ℕ} (hj : j < realPWOriginJetCount α) :
    4 * (j : ℝ) - 2 * α ≤ -1 :=
  le_of_not_gt (Nat.find_min (exists_realPWOrigin_power α) hj)

/-- At infinity the density times the squared evaluation norm stays bounded. -/
theorem exists_bound_realPWIntervalWeight_mul_eval_norm_sq (Y α s : ℝ)
    (hY : 0 ≤ Y) (ha : 0 ≤ α) (hs : 0 ≤ s) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 4 ≤ |x| →
      realPWIntervalWeight α s x *
        ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) x‖ ^ 2 ≤ C := by
  let w := realPWIntervalWeight α s
  let e := RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs)
  obtain ⟨φ, _, hone, _⟩ := exists_evenSchwartz_fourierInv_plateau Y 1 hY zero_lt_one
  obtain ⟨B, hB, henv⟩ := schwartz_realPWIntervalWeight_L2_envelope
    (realPWIntervalWeight_translation_envelope ha hs) φ
  let G (t : ℝ) := B * (1 + |t|)⁻¹
  refine ⟨∫ t, G t ^ 2, integral_nonneg fun _ ↦ sq_nonneg _, fun x hx ↦ ?_⟩
  have h := realPWIntervalWeight_mul_evaluationVector_norm_sq_le Y α s hs φ hone G hB |x|
    (ae_of_all _ fun t ↦ by rw [mul_comm]; exact henv |x| hx t)
  change w |x| * ‖e |x|‖ ^ 2 ≤ _ at h
  change w x * ‖e x‖ ^ 2 ≤ _
  rcases le_total 0 x with h₁ | h₁
  · rwa [abs_of_nonneg h₁] at h
  · rw [abs_of_nonpos h₁] at h
    dsimp only [w, e] at h ⊢
    simpa only [realPWIntervalWeight_even, RealPWBand.evaluationVector_even] using h

/-- For any bounded integrable mask and any fixed contraction of the evaluation
argument, the weighted squared evaluation energy is integrable. The origin uses
its Taylor order; the tail only needs the ordinary L¹ norm of the mask. -/
theorem integrable_realPWIntervalWeight_mask_eval_norm_sq
    (Y α s : ℝ) (hY : 0 ≤ Y) (ha : 0 ≤ α) (hs : 0 ≤ s) (k : ℕ)
    (hk : -1 < (↑(2 * k) : ℝ) - 2 * α)
    (hjet : ∀ (f : RealPWBand.space Y (volume_le_realPWIntervalMeasure α s hs)) (j : ℕ), j < k →
      iteratedDeriv j (fun x ↦ RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs) x f) 0 = 0)
    {a : ℝ} (ha₀ : 0 < a) (ha₁ : a ≤ 1) {m : ℝ → ℂ} (hm : Integrable m)
    (hmb : ∃ M : ℝ, ∀ x, ‖m x‖ ≤ M) :
    Integrable (fun x ↦ ‖m x‖ * (realPWIntervalWeight α s x *
      ‖RealPWBand.evaluationVector Y (volume_le_realPWIntervalMeasure α s hs) (a * x)‖ ^ 2)) := by
  let w := realPWIntervalWeight α s
  let hμ := volume_le_realPWIntervalMeasure α s hs
  let e := RealPWBand.evaluationVector Y hμ
  let F (x : ℝ) := ‖m x‖ * (w x * ‖e (a * x)‖ ^ 2)
  have hw (x : ℝ) : 0 ≤ w x := zero_le_one.trans (one_le_realPWIntervalWeight α s hs x)
  have hF₀ (x : ℝ) : 0 ≤ F x := mul_nonneg (norm_nonneg _) (mul_nonneg (hw x) (sq_nonneg _))
  have hme : AEStronglyMeasurable F volume := by
    have he : Continuous (fun x : ℝ ↦ ‖e (a * x)‖ ^ 2) :=
      ((RealPWBand.continuous_evaluationVector Y hμ).comp (continuous_const.mul continuous_id)).norm.pow 2
    exact hm.norm.aestronglyMeasurable.mul
      ((measurable_realPWIntervalWeight α s).aestronglyMeasurable.mul he.aestronglyMeasurable)
  obtain ⟨M, hM⟩ := hmb
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  obtain ⟨C, hC, hlocal⟩ := RealPWBand.exists_norm_evaluationVector_le_abs_pow Y hY hμ k hjet
  let B := max C (Real.sqrt (2 * Y))
  have hB : 0 ≤ B := hC.trans (le_max_left _ _)
  have hglob (x : ℝ) : ‖e (a * x)‖ ≤ B * |x| ^ k := by
    rcases le_or_gt |x| 1 with hx | hx
    · have habs : |a * x| ≤ |x| := by
        rw [abs_mul, abs_of_pos ha₀]
        exact mul_le_of_le_one_left (abs_nonneg x) ha₁
      exact (hlocal (a * x) (habs.trans hx)).trans
        (mul_le_mul (le_max_left _ _) (pow_le_pow_left₀ (abs_nonneg _) habs _) (by positivity) hB)
    · exact (RealPWBand.norm_evaluationVector_le Y hY hμ (a * x)).trans <|
        (le_max_right _ _).trans (le_mul_of_one_le_right hB (one_le_pow₀ hx.le))
  let L := 4 / a
  let S := Icc (-L) L
  have hS : MeasurableSet S := measurableSet_Icc
  have hI : IntegrableOn F S := by
    have hg : IntegrableOn (fun x : ℝ ↦ |x| ^ (2*k) * w x) S := by
      simpa only [Real.rpow_natCast] using
        (integrableOn_abs_rpow_mul_realPWIntervalWeight (R := L) ha hs hk)
    apply (hg.const_mul (M * B ^ 2)).mono' (hme.mono_measure Measure.restrict_le_self)
    filter_upwards with x
    rw [Real.norm_of_nonneg (hF₀ x)]
    calc
      F x ≤ M * (w x * (B * |x| ^ k) ^ 2) := mul_le_mul (hM x)
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hglob x) 2) (hw x))
        (mul_nonneg (hw x) (sq_nonneg _)) hM₀
      _ = _ := by rw [mul_pow, ← pow_mul, mul_comm k 2]; ring
  obtain ⟨E, _, hE⟩ := exists_bound_realPWIntervalWeight_mul_eval_norm_sq Y α s hY ha hs
  let D := Real.exp (2 * |α * Real.log a|) * (1 + |Real.log a| + Real.log a ^ 2) ^ (s / 2)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hT : IntegrableOn F Sᶜ := by
    apply (hm.norm.const_mul (D * E)).integrableOn.mono' (hme.mono_measure Measure.restrict_le_self)
    filter_upwards [ae_restrict_mem hS.compl] with x hx
    have hL : L < |x| := by by_contra! h; exact hx (abs_le.mp h)
    have hax : 4 ≤ |a * x| := by
      rw [abs_mul, abs_of_pos ha₀, mul_comm a |x|]
      exact ((div_lt_iff₀ ha₀).mp hL).le
    have hxe : w x * ‖e (a * x)‖ ^ 2 ≤ D * E := calc
      _ ≤ (D * w (a * x)) * ‖e (a * x)‖ ^ 2 := mul_le_mul_of_nonneg_right
        (realPWIntervalWeight_le_dilation hs ha₀ x) (sq_nonneg _)
      _ = D * (w (a * x) * ‖e (a * x)‖ ^ 2) := by rw [mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hE (a * x) hax) hD
    rw [Real.norm_of_nonneg (hF₀ x)]
    exact (mul_le_mul_of_nonneg_left hxe (norm_nonneg _)).trans_eq (mul_comm _ _)
  simpa only [union_compl_self, integrableOn_univ] using (integrableOn_union.mpr ⟨hI, hT⟩)

section

variable (Y α s : ℝ) (hs : 0 ≤ s)
local notation "μw" => realPWIntervalMeasure α s
local notation "hμ" => volume_le_realPWIntervalMeasure α s hs
local notation "V" => RealPWBand.space Y hμ
local notation "ev" => RealPWBand.evaluation Y hμ
local notation "eV" => RealPWBand.evaluationVector Y hμ

private theorem memLp_scaled_cutoff_evaluation {a c : ℝ} {m p : ℝ → ℂ}
    (hp : AEStronglyMeasurable p volume) (hpn : ∀ x, ‖p x‖ ^ 2 = c * ‖m x‖)
    (henergy : Integrable (fun x ↦ ‖m x‖ * (realPWIntervalWeight α s x * ‖eV (a * x)‖ ^ 2))) :
    MemLp (fun x ↦ p x • eV (a * x)) 2 μw := by
  have hme : AEStronglyMeasurable (fun x ↦ p x • eV (a * x)) μw :=
    (hp.mono_ac (realPWIntervalMeasure_absolutelyContinuous α s)).smul
      ((RealPWBand.continuous_evaluationVector Y hμ).comp
        (continuous_const.mul continuous_id)).aestronglyMeasurable
  let w (x : ℝ) := ENNReal.ofReal (realPWIntervalWeight α s x)
  have hw : Measurable w := (measurable_realPWIntervalWeight α s).ennreal_ofReal
  have hw' : ∀ᵐ x ∂volume, w x < ⊤ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  refine (memLp_two_iff_integrable_sq_norm hme).2 ((integrable_withDensity_iff hw hw').2 ?_)
  apply (henergy.const_mul c).congr
  exact ae_of_all _ fun x ↦ by
    have h0 := zero_le_one.trans (one_le_realPWIntervalWeight α s hs x)
    change c * (‖m x‖ * (realPWIntervalWeight α s x * ‖eV (a*x)‖ ^ 2)) =
      ‖p x • eV (a*x)‖ ^ 2 * (w x).toReal
    rw [norm_smul, mul_pow, hpn, show (w x).toReal = realPWIntervalWeight α s x from ENNReal.toReal_ofReal h0]
    ring

/-- The actual compression of any bounded integrable mask is nuclear, including
when the interval density is singular at zero. Its trace is the single weighted
evaluation diagonal integrated against Lebesgue measure. -/
theorem realPWCutoff_exists_nuclear_of_integrable_mask
    (hY : 0 ≤ Y) (ha : 0 ≤ α) (g : ℝ) (hg : 1 < g)
    {m : ℝ → ℂ} (hm : Integrable m) (hmb : ∃ M : ℝ, ∀ x, ‖m x‖ ≤ M) :
    let c := ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    ∃ T : nuclearEndomorphisms V,
      Integrable (fun x ↦ m x * realPWSharpDensity Y α s hs g x) ∧
      hilbertTrace T = (∫ x, m x * realPWSharpDensity Y α s hs g x) ∧
      (∀ f : V, ∃ r : Lp ℂ 2 μw,
        (∀ᵐ x ∂μw, r x = c * m x * ev (g⁻¹ * x) f) ∧ T.val f = (V).orthogonalProjectionOnto r) ∧
      (∀ (f r : V), (∀ x, ev x r = c * m x * ev (g⁻¹ * x) f) →
        ∀ x, ev x (T.val f) = c * m x * ev (g⁻¹ * x) f) := by
  let c := ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  change ∃ T, _
  let n := realPWOriginJetCount α
  let k := 2 * n
  have hk : -1 < (↑(2 * k) : ℝ) - 2 * α := by
    dsimp only [k, n]
    push_cast
    nlinarith only [realPWOriginJetCount_spec α]
  have hjet (f : V) : ∀ j < k, iteratedDeriv j (fun x ↦ ev x f) 0 = 0 :=
    realPWInterval_forcedOriginJets Y α s ha hs n (fun j hj ↦ realPWOriginJetCount_min α hj) f
  let p (x : ℝ) : ℂ := (Real.sqrt ‖m x‖ : ℂ)
  let q (x : ℝ) := m x / p x
  have hgp : 0 < g := zero_lt_one.trans hg
  have ha₀ : 0 < g⁻¹ := inv_pos.mpr hgp
  have ha₁ : g⁻¹ ≤ 1 := (inv_le_one₀ hgp).mpr hg.le
  have hp : AEStronglyMeasurable p volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (Real.continuous_sqrt.comp_aestronglyMeasurable hm.norm.aestronglyMeasurable)
  have hq : AEStronglyMeasurable q volume := hm.aestronglyMeasurable.div₀ hp
  have hpn (x : ℝ) : ‖p x‖ ^ 2 = ‖m x‖ := by
    change ‖(Real.sqrt ‖m x‖ : ℂ)‖ ^ 2 = _
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sq_sqrt (norm_nonneg _)]
  have hpq (x : ℝ) : p x * q x = m x := by
    by_cases hz : m x = 0
    · simp [q, hz]
    · have hn : p x ≠ 0 := by
        intro h
        have hz' := hpn x
        rw [h, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hz'
        exact hz (norm_eq_zero.mp hz'.symm)
      exact (mul_div_cancel₀ (m x) hn)
  have hqn (x : ℝ) : ‖q x‖ ^ 2 = ‖m x‖ := by
    change ‖m x / p x‖ ^ 2 = _
    rw [norm_div, div_pow, hpn]
    by_cases hz : ‖m x‖ = 0
    · simp [hz]
    · field_simp
  have hL : MemLp (realPWCutoffLeftFamily Y α s hs p) 2 μw := by
    have h := memLp_scaled_cutoff_evaluation Y α s hs (a := 1) (c := 1) hp
      (fun x ↦ by rw [hpn, one_mul])
      (integrable_realPWIntervalWeight_mask_eval_norm_sq Y α s hY ha hs k hk hjet
        zero_lt_one le_rfl hm hmb)
    change MemLp (fun x ↦ realPWCutoffLeftFamily Y α s hs p x) 2 μw
    simpa only [realPWCutoffLeftFamily_apply, one_mul] using h
  have hR : MemLp (realPWCutoffRightFamily Y α s hs g q) 2 μw := by
    have h := memLp_scaled_cutoff_evaluation Y α s hs (a := g⁻¹) (c := ‖c‖^2)
      (p := fun x ↦ star (c * q x)) ((hq.const_mul c).star)
      (fun x ↦ by rw [norm_star, norm_mul, mul_pow, hqn])
      (integrable_realPWIntervalWeight_mask_eval_norm_sq Y α s hY ha hs k hk hjet
        ha₀ ha₁ hm hmb)
    change MemLp (fun x ↦ realPWCutoffRightFamily Y α s hs g q x) 2 μw
    simpa only [realPWCutoffRightFamily_apply] using h
  obtain ⟨T, ht, hpj, he⟩ := realPWCutoff_exists_compression Y α s hs g p q m hpq hL hR
  refine ⟨T, realPWCutoff_integrable_diagonal Y α s hs g p q m hpq hL hR, ht, ?_, he⟩
  intro f
  have hf : MemLp (fun x ↦ ev x f) 2 μw :=
    (memLp_congr_ae (RealPWBand.evaluation_ae Y hμ
      (realPWIntervalMeasure_absolutelyContinuous α s) f)).mpr (Lp.memLp f.val)
  have hd := memLp_realPWIntervalMeasure_dilation hs ha₀ hf
  obtain ⟨M, hM⟩ := hmb
  let F (x : ℝ) := c * m x * ev (g⁻¹ * x) f
  have hF : MemLp F 2 μw := by
    have hMe : AEStronglyMeasurable F μw :=
      ((hm.aestronglyMeasurable.mono_ac (realPWIntervalMeasure_absolutelyContinuous α s)).const_mul c).mul
        hd.aestronglyMeasurable
    apply (hd.norm.const_mul (‖c‖ * M)).mono' hMe
    exact ae_of_all _ fun x ↦ by
      dsimp only [F]
      rw [norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hM x) (norm_nonneg _)) (norm_nonneg _)
  exact ⟨hF.toLp F, hF.coeFn_toLp, hpj f _ hF.coeFn_toLp⟩

end

/-- Construct the actual nuclear sharp and smoothed compressions simultaneously.
The trace difference is the weighted diagonal integrated against the mask
difference, and the smoothed operator acts without projection. -/
theorem exists_realPWSharpSmoothCompressions (Y α s : ℝ)
    (hY : 0 < Y) (ha : 0 ≤ α) (hs : 0 ≤ s) (g : ℝ) (hg : 1 < g)
    (η : 𝓢(ℝ, ℂ)) (heven : Function.Even (η : ℝ → ℂ)) {c : ℝ} (hc : 0 ≤ c)
    (hmargin : c ≤ (1 - g⁻¹) * Y)
    (hη : Function.support (𝓕 (η : ℝ → ℂ)) ⊆ Icc (-c) c) :
    let μ := realPWIntervalMeasure α s
    let hμ := volume_le_realPWIntervalMeasure α s hs
    let V := RealPWBand.space Y hμ
    let ev := RealPWBand.evaluation Y hμ
    let b := ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
    ∃ sharp smooth : ℝ → nuclearEndomorphisms V,
      (∀ L (f : V), ∃ r : Lp ℂ 2 μ,
        (∀ᵐ x ∂μ, r x = b * sharpIntervalMask L x * ev (g⁻¹ * x) f) ∧
          (sharp L).val f = V.orthogonalProjectionOnto r) ∧
      (∀ R ≥ 0, IntegrableOn (realPWSharpDensity Y α s hs g) (Icc (-R) R)) ∧
      (∀ L, hilbertTrace (sharp L) - hilbertTrace (smooth L) =
        ∫ x, (sharpIntervalMask L x - smoothIntervalMask η L x) *
          realPWSharpDensity Y α s hs g x) ∧
      ∀ L f x, ev x ((smooth L).val f) = b * smoothIntervalMask η L x * ev (g⁻¹ * x) f := by
  let b := ((g ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  let e := RealPWBand.evaluation Y (volume_le_realPWIntervalMeasure α s hs)
  let d := realPWSharpDensity Y α s hs g
  let A (L : ℝ) := realPWCutoff_exists_nuclear_of_integrable_mask Y α s hs hY.le ha g hg
    (integrable_sharpIntervalMask L) ⟨1, fun x ↦ by
      by_cases hx : x ∈ Icc (-L) L <;> simp [sharpIntervalMask, hx]⟩
  let B (L : ℝ) := realPWCutoff_exists_nuclear_of_integrable_mask Y α s hs hY.le ha g hg
    (integrable_smoothIntervalMask η η.integrable L)
    ⟨∫ t, ‖η t‖, norm_smoothIntervalMask_le η.integrable L⟩
  refine ⟨fun L ↦ (A L).choose, fun L ↦ (B L).choose, ?_, ?_, ?_, ?_⟩
  · exact fun L ↦ (A L).choose_spec.2.2.1
  · intro R _
    have hi := (A R).choose_spec.1
    have he : (fun x ↦ sharpIntervalMask R x * d x) = (Icc (-R) R).indicator d := by
      funext x
      by_cases hx : x ∈ Icc (-R) R <;> simp [sharpIntervalMask, hx]
    change Integrable (fun x ↦ sharpIntervalMask R x * d x) at hi
    rw [he, integrable_indicator_iff measurableSet_Icc] at hi
    exact hi
  · intro L
    change hilbertTrace (A L).choose - hilbertTrace (B L).choose = _
    rw [(A L).choose_spec.2.1, (B L).choose_spec.2.1,
      ← integral_sub (A L).choose_spec.1 (B L).choose_spec.1]
    simp only [sub_mul]
  · intro L f x
    obtain ⟨r, hr⟩ := exists_realPW_smoothIntervalMask_mul_dilate_evaluation
      hY hs (inv_pos.mpr (zero_lt_one.trans hg)) hc hmargin η heven hη L b f
    exact (B L).choose_spec.2.2.2 f r hr x

end RiemannMasullo.Isolated
