module

public import Mathlib.Analysis.Complex.Poisson
public import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Boundary transport from Poisson control at one exceptional point -/

public noncomputable section

open Complex Filter MeasureTheory Set
open scoped Topology

namespace RiemannMasullo.PoissonBoundary

/-- On a chordal arc about one, the disk Poisson kernel is at least
`1 / (8 * (1 - q))`. The first bound holds on the whole circle. -/
theorem poissonKernel_radial_lower {q r : ℝ} (hq : 1/2 ≤ q) (hq1 : q < 1)
    (hqr : (1+q)/2 ≤ r) (hr : r ≤ 1) (θ : ℝ) :
    (1-q)/8 ≤ poissonKernel 0 (q : ℂ) (circleMap 0 r θ) ∧
    (‖circleMap 0 1 θ - 1‖ ≤ 1-q →
      1/(8*(1-q)) ≤ poissonKernel 0 (q : ℂ) (circleMap 0 r θ)) := by
  have hq0 : 0 ≤ q := by linarith
  have hlt : q < r := by linarith
  have hr0 : 0 ≤ r := hq0.trans hlt.le
  have hn : ‖circleMap 0 r θ - (q : ℂ)‖ ≠ 0 := by
    intro he
    have hh := congrArg norm (sub_eq_zero.mp (norm_eq_zero.mp he))
    simp only [norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, abs_of_nonneg hq0] at hh
    linarith
  have hd : 0 < ‖circleMap 0 r θ - (q : ℂ)‖ ^ 2 := sq_pos_of_pos (lt_of_le_of_ne (norm_nonneg _) hn.symm)
  have hnum : (1-q)/2 ≤ r^2-q^2 := by
    calc (1-q)/2 ≤ r-q := by linarith
         _ ≤ (r-q)*(r+q) := le_mul_of_one_le_right (by linarith) (by linarith)
         _ = _ := by ring
  have hD : ‖circleMap 0 r θ - (q : ℂ)‖ ≤ 2 := by
    calc _ ≤ ‖circleMap 0 r θ‖ + ‖(q : ℂ)‖ := norm_sub_le _ _
         _ ≤ _ := by simp only [norm_circleMap_zero, Complex.norm_real, Real.norm_eq_abs,
                       abs_of_nonneg hq0, abs_of_nonneg hr0]; linarith
  simp only [poissonKernel_def, sub_zero, norm_circleMap_zero, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hq0, abs_of_nonneg hr0]
  constructor
  · apply (le_div_iff₀ hd).mpr
    calc (1-q)/8 * ‖circleMap 0 r θ - (q : ℂ)‖ ^ 2 ≤ (1-q)/8 * 2^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hD 2) (by linarith)
         _ = (1-q)/2 := by ring
         _ ≤ _ := hnum
  · intro ha
    have he : circleMap 0 r θ - (q : ℂ) =
        (r : ℂ) * (circleMap 0 1 θ - 1) + ((r-q : ℝ) : ℂ) := by
      simp only [circleMap_zero, Complex.ofReal_one, one_mul, Complex.ofReal_sub]
      ring
    have hdist : ‖circleMap 0 r θ - (q : ℂ)‖ ≤ 2*(1-q) := by
      rw [he]
      calc _ ≤ ‖(r : ℂ)*(circleMap 0 1 θ - 1)‖ + ‖((r-q : ℝ) : ℂ)‖ := norm_add_le _ _
           _ = r * ‖circleMap 0 1 θ - 1‖ + (r-q) := by
             simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
               abs_of_nonneg (sub_nonneg.mpr hlt.le)]
           _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ha hr0,
             mul_le_mul_of_nonneg_right hr (sub_nonneg.mpr hq1.le)]
    apply (div_le_div_iff₀ (by linarith) hd).mpr
    nlinarith [pow_le_pow_left₀ (norm_nonneg _) hdist 2,
      mul_le_mul_of_nonneg_left hnum (by linarith : 0 ≤ 8*(1-q))]

/-- A finite upper bound for the nonnegative Lebesgue integral gives exactly
the integrability and real integral bound appearing in a Poisson budget. -/
theorem finite_nonnegative_budget_iff {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {B : ℝ} (hm : AEStronglyMeasurable f μ) (hp : 0 ≤ᵐ[μ] f) (hB : 0 ≤ B) :
    (Integrable f μ ∧ (∫ x, f x ∂μ) ≤ B) ↔
      (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal B := by
  constructor
  · rintro ⟨hi,hle⟩
    rw [← ofReal_integral_eq_lintegral_ofReal hi hp]
    exact ENNReal.ofReal_le_ofReal hle
  · intro h
    have hi : Integrable f μ := ⟨hm,(hasFiniteIntegral_iff_ofReal hp).mpr (h.trans_lt ENNReal.ofReal_lt_top)⟩
    refine ⟨hi, (ENNReal.ofReal_le_ofReal_iff hB).mp ?_⟩
    rwa [ofReal_integral_eq_lintegral_ofReal hi hp]

private theorem integral_tendsto_of_abs_sub {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {v : ℕ → X → ℝ} {u : X → ℝ} (hu : Integrable u μ)
    (hv : ∀ᶠ n in atTop, Integrable (v n) μ)
    (h : Tendsto (fun n ↦ ∫ x, |v n x - u x| ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ x, v n x ∂μ) atTop (𝓝 (∫ x, u x ∂μ)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) _ h
  filter_upwards [hv] with n hn
  rw [← integral_sub hn hu]
  exact norm_integral_le_integral_norm _

/-- Local `L¹` convergence on an increasing exhaustion transfers to global `L¹`
convergence when the nonnegative approximants have bounded mass and their masses
on the complements tend uniformly to zero in the stated iterated sense. -/
theorem integrable_tendsto_of_exhaustion {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (S : ℕ → Set X) (hs : ∀ j, MeasurableSet (S j)) (hmono : Monotone S)
    (hcover : ∀ᵐ x ∂μ, x ∈ ⋃ j, S j)
    (v : ℕ → X → ℝ) (u : X → ℝ) (hv0 : ∀ n, 0 ≤ᵐ[μ] v n) (hu0 : 0 ≤ᵐ[μ] u)
    (hbound : ∃ B : ℝ, ∀ᶠ n in atTop, Integrable (v n) μ ∧ (∫ x, v n x ∂μ) ≤ B)
    (hlocal : ∀ j, IntegrableOn u (S j) μ ∧
      Tendsto (fun n ↦ ∫ x in S j, |v n x - u x| ∂μ) atTop (𝓝 0))
    (c : ℕ → ℝ) (hc : Tendsto c atTop (𝓝 0))
    (htail : ∀ j, ∀ᶠ n in atTop, (∫ x in (S j)ᶜ, v n x ∂μ) ≤ c j) :
    Integrable u μ ∧ Tendsto (fun n ↦ ∫ x, |v n x - u x| ∂μ) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ x, v n x ∂μ) atTop (𝓝 (∫ x, u x ∂μ)) := by
  obtain ⟨B,hB⟩ := hbound
  have hU : μ.restrict (⋃ j, S j) = μ := Measure.restrict_eq_self_of_ae_mem hcover
  have hsmall (j : ℕ) : (∫ x in S j, u x ∂μ) ≤ B := by
    have h := integral_tendsto_of_abs_sub (hlocal j).1
      (hB.mono fun n hn ↦ hn.1.integrableOn) (hlocal j).2
    apply le_of_tendsto h
    filter_upwards [hB] with n hn
    exact (setIntegral_le_integral hn.1 (hv0 n)).trans hn.2
  have hu : Integrable u μ := by
    refine ⟨?_, (hasFiniteIntegral_iff_ofReal hu0).mpr ?_⟩
    · rw [← hU]
      exact AEStronglyMeasurable.iUnion fun j ↦ (hlocal j).1.aestronglyMeasurable
    · calc (∫⁻ x, ENNReal.ofReal (u x) ∂μ) =
             ⨆ j, ∫⁻ x in S j, ENNReal.ofReal (u x) ∂μ := by
                rw [← setLIntegral_iUnion_of_directed _ hmono.directed_le, hU]
           _ ≤ ENNReal.ofReal B := by
             apply iSup_le
             intro j
             rw [← ofReal_integral_eq_lintegral_ofReal (hlocal j).1 (ae_restrict_of_ae hu0)]
             exact ENNReal.ofReal_le_ofReal (hsmall j)
           _ < ⊤ := ENNReal.ofReal_lt_top
  have htu : Tendsto (fun j ↦ ∫ x in (S j)ᶜ, u x ∂μ) atTop (𝓝 0) := by
    have h := tendsto_setIntegral_of_monotone hs hmono hu.integrableOn
    rw [hU] at h
    simp only [setIntegral_compl (hs _) hu]
    simpa only [sub_self] using
      (tendsto_const_nhds (x := ∫ x, u x ∂μ)).sub h
  have habs : Tendsto (fun n ↦ ∫ x, |v n x - u x| ∂μ) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hjlim : Tendsto (fun j ↦ c j + ∫ x in (S j)ᶜ, u x ∂μ) atTop (𝓝 0) := by
      simpa only [add_zero] using hc.add htu
    obtain ⟨j,hj⟩ := (hjlim.eventually (eventually_lt_nhds (half_pos hε))).exists
    filter_upwards [hB, htail j, (hlocal j).2.eventually (eventually_lt_nhds (half_pos hε))] with n hn ht hnloc
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun _ ↦ abs_nonneg _)]
    have hdiff : Integrable (fun x ↦ |v n x-u x|) μ := (hn.1.sub hu).abs
    have hrem : (∫ x in (S j)ᶜ, |v n x-u x| ∂μ) ≤
        (∫ x in (S j)ᶜ, v n x ∂μ) + ∫ x in (S j)ᶜ, u x ∂μ := by
      rw [← integral_add hn.1.integrableOn hu.integrableOn]
      apply integral_mono_ae hdiff.integrableOn (hn.1.add hu).integrableOn
      filter_upwards [ae_restrict_of_ae (hv0 n), ae_restrict_of_ae hu0] with x hx hy
      change 0 ≤ v n x at hx
      change 0 ≤ u x at hy
      change |v n x - u x| ≤ v n x + u x
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    rw [← integral_add_compl (hs j) hdiff]
    linarith
  exact ⟨hu,habs,integral_tendsto_of_abs_sub hu (hB.mono fun _ hn ↦ hn.1) habs⟩

local notation "μθ" => volume.restrict (Ioc (0 : ℝ) (2*Real.pi))
local notation "dθ(" θ ")" => ‖circleMap 0 1 θ - 1‖
local notation "P(" r ", " q ", " θ ")" => poissonKernel 0 ((q : ℝ) : ℂ) (circleMap 0 r θ)

/-- The mass of every nonnegative integrable density on a chordal arc is
controlled by its full Poisson integral. This works for any angular measure. -/
theorem integral_chordArc_le (μ : Measure ℝ) {q r : ℝ} (hq : 1/2 ≤ q)
    (hq1 : q < 1) (hqr : (1+q)/2 ≤ r) (hr : r ≤ 1) (v : ℝ → ℝ)
    (hv : Integrable v μ) (hv0 : 0 ≤ᵐ[μ] v)
    (hw : Integrable (fun θ ↦ P(r,q,θ)*v θ) μ) :
    (∫ θ in {θ | dθ(θ) ≤ 1-q}, v θ ∂μ) ≤
      8*(1-q) * ∫ θ, P(r,q,θ)*v θ ∂μ := by
  let A := {θ : ℝ | dθ(θ) ≤ 1-q}
  let K (θ : ℝ) := P(r,q,θ)*v θ
  let a := 8*(1-q)
  have ha : 0 < a := by dsimp [a]; linarith
  have hA : MeasurableSet A :=
    measurableSet_le ((measurable_circleMap 0 1).sub_const 1).norm measurable_const
  have hK : 0 ≤ᵐ[μ] K := by
    filter_upwards [hv0] with θ hθ
    have hk := (poissonKernel_radial_lower hq hq1 hqr hr θ).1
    exact mul_nonneg ((by linarith : 0 ≤ (1-q)/8).trans hk) hθ
  have hd : ∀ᵐ θ ∂μ.restrict A, v θ ≤ a*K θ := by
    filter_upwards [ae_restrict_mem hA, ae_restrict_of_ae hv0] with θ hθ hnon
    have hk := (poissonKernel_radial_lower hq hq1 hqr hr θ).2 hθ
    have hone : 1 ≤ a*P(r,q,θ) := by simpa only [mul_comm] using (div_le_iff₀ ha).mp hk
    simpa only [a,K,one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hone hnon
  calc (∫ θ in A, v θ ∂μ) ≤ ∫ θ in A, a*K θ ∂μ :=
         integral_mono_ae hv.integrableOn (hw.const_mul a).integrableOn hd
       _ = a * ∫ θ in A, K θ ∂μ := integral_const_mul _ _
       _ ≤ a * ∫ θ, K θ ∂μ := mul_le_mul_of_nonneg_left (setIntegral_le_integral hw hK) ha.le

/-- Finite Poisson budgets approaching the exceptional boundary point transport
local `L¹` convergence to the full angular interval `(0, 2π]`. All limits and
integrals use Lebesgue angular measure. The finite budgets include integrability
of the weighted densities, and integrability of the full limit is a conclusion. -/
theorem radial_log_density_transport
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 1)) (hr1 : ∀ᶠ n in atTop, r n ≤ 1)
    (v : ℕ → ℝ → ℝ) (u U : ℝ → ℝ)
    (hvm : ∀ n, AEStronglyMeasurable (v n) μθ) (hv0 : ∀ n, 0 ≤ᵐ[μθ] v n)
    (hu0 : 0 ≤ᵐ[μθ] u)
    (hlocal : ∀ δ : ℝ, 0 < δ → IntegrableOn u {θ | δ < dθ(θ)} μθ ∧
      Tendsto (fun n ↦ ∫ θ in {θ | δ < dθ(θ)}, |v n θ-u θ| ∂μθ) atTop (𝓝 0))
    (hbudget : ∀ q : ℝ, 1/2 ≤ q → q < 1 → ∀ᶠ n in atTop,
      Integrable (fun θ ↦ P(r n,q,θ) * v n θ) μθ ∧
        (∫ θ, P(r n,q,θ) * v n θ ∂μθ) ≤ U q)
    (hU : Tendsto (fun q ↦ (1-q)*U q) (𝓝[<] 1) (𝓝 0)) :
    (∀ᶠ n in atTop, Integrable (v n) μθ) ∧ Integrable u μθ ∧
      Tendsto (fun n ↦ ∫ θ in Ioc (0 : ℝ) (2*Real.pi), |v n θ-u θ|) atTop (𝓝 0) ∧
      Tendsto (fun n ↦ ∫ θ in Ioc (0 : ℝ) (2*Real.pi), v n θ) atTop
        (𝓝 (∫ θ in Ioc (0 : ℝ) (2*Real.pi), u θ)) := by
  have hrad (q : ℝ) (hq : q < 1) : ∀ᶠ n in atTop, (1+q)/2 ≤ r n ∧ r n ≤ 1 :=
    (hr.eventually (eventually_ge_nhds (show (1+q)/2 < 1 by linarith))).and hr1
  have hglob : ∀ᶠ n in atTop, Integrable (v n) μθ ∧ (∫ θ, v n θ ∂μθ) ≤ 16*U (1/2) := by
    filter_upwards [hrad (1/2) (by norm_num), hbudget (1/2) le_rfl (by norm_num)] with n hn hb
    have hdom : ∀ᵐ θ ∂μθ, v n θ ≤ 16*(P(r n,1/2,θ)*v n θ) := by
      filter_upwards [hv0 n] with θ hθ
      change 0 ≤ v n θ at hθ
      have hk := (poissonKernel_radial_lower (q := 1/2) le_rfl (by norm_num) hn.1 hn.2 θ).1
      nlinarith [mul_le_mul_of_nonneg_right hk hθ]
    have hi : Integrable (v n) μθ := (hb.1.const_mul 16).mono_nonneg (hvm n) (hv0 n) hdom
    have h := integral_mono_ae hi (hb.1.const_mul 16) hdom
    rw [integral_const_mul] at h
    exact ⟨hi,h.trans (mul_le_mul_of_nonneg_left hb.2 (by norm_num))⟩
  let δ (j : ℕ) : ℝ := (1/2)^j * (1/2)
  let q (j : ℕ) := 1 - δ j
  let S (j : ℕ) := {θ : ℝ | δ j < dθ(θ)}
  have hδpos (j : ℕ) : 0 < δ j := by dsimp [δ]; positivity
  have hδanti : Antitone δ := by
    apply antitone_nat_of_succ_le
    intro j
    dsimp [δ]
    rw [pow_succ]
    nlinarith [show (0 : ℝ) ≤ (1/2)^j by positivity]
  have hq (j : ℕ) : 1/2 ≤ q j ∧ q j < 1 := by
    have hle := hδanti (Nat.zero_le j)
    have hzero : δ 0 = 1/2 := by norm_num [δ]
    rw [hzero] at hle
    dsimp only [q]
    exact ⟨by linarith only [hle],by linarith only [hδpos j]⟩
  have hδlim : Tendsto δ atTop (𝓝 0) := by
    simpa only [δ, zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)<1)).mul_const (1/2)
  have hqlim : Tendsto q atTop (𝓝[<] 1) := tendsto_nhdsWithin_iff.mpr
    ⟨by simpa only [q,sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub hδlim,
     .of_forall fun j ↦ (hq j).2⟩
  have hS (j : ℕ) : MeasurableSet (S j) :=
    measurableSet_lt measurable_const ((measurable_circleMap 0 1).sub_const 1).norm
  have hmono : Monotone S := fun i j hij θ hθ ↦ lt_of_le_of_lt (hδanti hij) hθ
  have hcover : ∀ᵐ θ ∂μθ, θ ∈ ⋃ j, S j := by
    have hnull := ((countable_singleton (1:ℂ)).preimage_circleMap 0 (one_ne_zero : (1:ℝ)≠0)).ae_notMem
      (volume : Measure ℝ)
    filter_upwards [ae_restrict_of_ae hnull] with θ hθ
    have hn : circleMap 0 1 θ ≠ 1 := hθ
    obtain ⟨j,hj⟩ := (hδlim.eventually (eventually_lt_nhds (norm_pos_iff.mpr (sub_ne_zero.mpr hn)))).exists
    exact mem_iUnion.mpr ⟨j,hj⟩
  let c (j : ℕ) := 8*((1-q j)*U (q j))
  have hc : Tendsto c atTop (𝓝 0) := by
    simpa only [c,mul_zero,Function.comp_apply] using (hU.comp hqlim).const_mul 8
  have htail (j : ℕ) : ∀ᶠ n in atTop, (∫ θ in (S j)ᶜ, v n θ ∂μθ) ≤ c j := by
    filter_upwards [hglob,hrad (q j) (hq j).2,hbudget (q j) (hq j).1 (hq j).2] with n hni hn hb
    have he : (S j)ᶜ = {θ : ℝ | dθ(θ) ≤ 1-q j} := by
      ext θ
      change (¬δ j < dθ(θ)) ↔ dθ(θ) ≤ 1-(1-δ j)
      rw [sub_sub_cancel, not_lt]
    rw [he]
    calc _ ≤ 8*(1-q j) * ∫ θ, P(r n,q j,θ)*v n θ ∂μθ :=
           integral_chordArc_le μθ (hq j).1 (hq j).2 hn.1 hn.2 (v n) hni.1 (hv0 n) hb.1
         _ ≤ 8*(1-q j)*U (q j) := mul_le_mul_of_nonneg_left hb.2 (by linarith [(hq j).2])
         _ = c j := by dsimp [c]; ring
  exact ⟨hglob.mono fun _ hn ↦ hn.1, integrable_tendsto_of_exhaustion μθ S hS hmono hcover
    v u hv0 hu0 ⟨_,hglob⟩ (fun j ↦ hlocal _ (hδpos j)) c hc htail⟩

/-- Normalized circle-average form. The input is a single real-valued function on
the circles, for instance `g z = -Real.log ‖f z‖`. The budget is in the same
angular-average normalization as Mathlib's Poisson formula. -/
theorem circleAverage_tendsto_of_poisson_budget
    (r : ℕ → ℝ) (hr : Tendsto r atTop (𝓝 1)) (hr1 : ∀ᶠ n in atTop, r n ≤ 1)
    (g : ℂ → ℝ) (u U : ℝ → ℝ)
    (hm : ∀ n, AEStronglyMeasurable (fun θ ↦ g (circleMap 0 (r n) θ)) μθ)
    (h0 : ∀ n, ∀ᵐ θ ∂μθ, 0 ≤ g (circleMap 0 (r n) θ)) (hu0 : 0 ≤ᵐ[μθ] u)
    (hlocal : ∀ δ : ℝ, 0 < δ → IntegrableOn u {θ | δ < dθ(θ)} μθ ∧
      Tendsto (fun n ↦ ∫ θ in {θ | δ < dθ(θ)}, |g (circleMap 0 (r n) θ)-u θ| ∂μθ)
        atTop (𝓝 0))
    (hbudget : ∀ q : ℝ, 1/2 ≤ q → q < 1 → ∀ᶠ n in atTop,
      CircleIntegrable (fun z ↦ poissonKernel 0 (q : ℂ) z * g z) 0 (r n) ∧
      Real.circleAverage (fun z ↦ poissonKernel 0 (q : ℂ) z * g z) 0 (r n) ≤ U q)
    (hU : Tendsto (fun q ↦ (1-q)*U q) (𝓝[<] 1) (𝓝 0)) :
    IntegrableOn u (Ioc (0 : ℝ) (2*Real.pi)) ∧
      Tendsto (fun n ↦ ∫ θ in Ioc (0 : ℝ) (2*Real.pi), |g (circleMap 0 (r n) θ)-u θ|)
        atTop (𝓝 0) ∧
      Tendsto (fun n ↦ Real.circleAverage g 0 (r n)) atTop
        (𝓝 ((2*Real.pi)⁻¹ * ∫ θ in Ioc (0 : ℝ) (2*Real.pi), u θ)) := by
  let T := 2*Real.pi
  have hT : 0 < T := Real.two_pi_pos
  have hB (q : ℝ) (hq : 1/2 ≤ q) (hq' : q < 1) : ∀ᶠ n in atTop,
      Integrable (fun θ ↦ P(r n,q,θ)*g (circleMap 0 (r n) θ)) μθ ∧
      (∫ θ, P(r n,q,θ)*g (circleMap 0 (r n) θ) ∂μθ) ≤ T*U q := by
    filter_upwards [hbudget q hq hq'] with n hn
    refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le Real.two_pi_pos.le).mp hn.1, ?_⟩
    have hb : (∫ θ, P(r n,q,θ)*g (circleMap 0 (r n) θ) ∂μθ) / T ≤ U q := by
      simpa only [Real.circleAverage_def, smul_eq_mul, T, div_eq_inv_mul,
        intervalIntegral.integral_of_le Real.two_pi_pos.le] using hn.2
    simpa only [mul_comm T] using (div_le_iff₀ hT).mp hb
  have hscale : Tendsto (fun q ↦ (1-q)*(T*U q)) (𝓝[<] 1) (𝓝 0) := by
    simpa only [mul_left_comm (1-_) T, mul_zero] using hU.const_mul T
  obtain ⟨_,hu,hL,hmean⟩ := radial_log_density_transport r hr hr1
    (fun n θ ↦ g (circleMap 0 (r n) θ)) u (fun q ↦ T*U q) hm h0 hu0 hlocal hB hscale
  refine ⟨hu,hL,?_⟩
  simpa only [Real.circleAverage_def, smul_eq_mul, intervalIntegral.integral_of_le Real.two_pi_pos.le]
    using hmean.const_mul (2*Real.pi)⁻¹

end RiemannMasullo.PoissonBoundary
