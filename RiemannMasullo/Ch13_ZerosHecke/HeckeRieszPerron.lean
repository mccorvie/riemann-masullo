module

public import Mathlib.Analysis.MellinInversion
public import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszMellin
public import RiemannMasullo.Ch13_ZerosHecke.HeckeRieszZeroDetection
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import RiemannMasullo.ForMathlib.Analysis.Complex.LandauLemma

/-!
# An upper bound for the once-integrated Hecke ideal sum

A zero-free half-plane bounds the centered first Riesz mean by an absolute Mellin
contour shift. The continuous center gives an integrable vertical kernel even
for the principal character.

## Logarithmic derivative on a fixed interior strip

With a zero-free half-plane for one character, Landau's lemma on fixed discs
centered at `2 + it` gives logarithmic growth on an interior strip. The Euler
product bounds the reciprocal at the center uniformly in its height.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

section FixedStrip


open Filter Function MeasureTheory NumberField Set
open scoped Asymptotics Topology

private theorem bounded_order_analyticAt {L : ℂ → ℂ} {z : ℂ} (hL : MeromorphicNFAt L z)
    {M : ℝ} (hM : ∀ᶠ w in 𝓝 z, ‖L w‖ ≤ M) : AnalyticAt ℂ L z := by
  apply hL.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  by_contra! hp
  have hp' := (tendsto_norm_cobounded_atTop.comp
    (tendsto_cobounded_of_meromorphicOrderAt_neg hp)).eventually_gt_atTop M
  obtain ⟨_, h, h'⟩ := ((hM.filter_mono nhdsWithin_le_nhds).and hp').exists
  exact h'.not_ge h

/-- On any fixed strip strictly inside its zero-free half-plane, up to
`Re s = 2`, the logarithmic derivative of an individual finite Hecke
L-function is `O(log |Im s|)` uniformly at large height. -/
theorem finiteHeckeL_logDeriv_fixedStrip_of_zeroFree
    {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), L s = finiteHeckeL χ s)
    {b d : ℝ} (hb : 0 ≤ b) (hbd : b < d) (hd : d < 2)
    (hzero : ∀ z : ℂ, b < z.re → meromorphicOrderAt L z ≤ 0) :
    ∃ C T : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc d 2 → T ≤ |s.im| →
      AnalyticAt ℂ L s ∧ L s ≠ 0 ∧ ‖logDeriv L s‖ ≤ C * Real.log |s.im| := by
  let r₀ := 2 - d
  let h := (d - b) / 4
  let r₁ := r₀ + h
  let r₂ := r₀ + 2 * h
  let r₃ := r₀ + 3 * h
  have hr₀ : 0 < r₀ := by dsimp [r₀]; linarith
  have hh : 0 < h := by dsimp [h]; linarith
  have h₀₁ : r₀ < r₁ := by dsimp [r₁]; linarith
  have h₁₂ : r₁ < r₂ := by dsimp [r₁, r₂]; linarith
  have h₂₃ : r₂ < r₃ := by dsimp [r₂, r₃]; linarith
  have hr₃ : r₃ < 2 - b := by dsimp [r₃, r₀, h]; linarith
  let K := landauConstant r₀ r₁ r₂ r₃
  have hK : 0 < K := landauConstant_pos hr₀ h₀₁ h₁₂ h₂₃
  let Z := ‖dedekindZeta F (2 : ℂ)‖
  obtain ⟨M, hM, hO⟩ := finiteHeckeL_continuation_isBigO_rpow χ L hL hSeries
    0 4 (by norm_num)
  obtain ⟨n, hn⟩ := exists_nat_gt M
  obtain ⟨A, hA⟩ := Asymptotics.isBigO_iff.mp hO
  simp only [eventually_inf_principal, eventually_comap, eventually_atTop] at hA
  obtain ⟨T, hT⟩ := hA
  have hbound {u : ℂ} (hu : u.re ∈ Icc 0 4) (huT : max T (max 1 A) ≤ |u.im|) :
      ‖L u‖ ≤ |u.im| ^ (n + 1) := by
    have ht := (le_max_left T (max 1 A)).trans huT
    have hu₁ := (le_max_left 1 A).trans ((le_max_right ..).trans huT)
    have huA := (le_max_right 1 A).trans ((le_max_right ..).trans huT)
    have hs := hT |u.im| ht u rfl hu
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at hs
    calc
      ‖L u‖ ≤ A * |u.im| ^ M := hs
      _ ≤ |u.im| * |u.im| ^ M := by gcongr
      _ ≤ |u.im| * |u.im| ^ (n : ℝ) := by gcongr
      _ = _ := by rw [Real.rpow_natCast, pow_succ, mul_comm]
  let e := 2 * (n + 1) + 1
  refine ⟨K * (e : ℝ), max (max T (max 1 A) + 3) (max 3 Z),
    mul_pos hK (by dsimp [e]; positivity), ?_⟩
  intro s hs hsize
  let c : ℂ := ⟨2, s.im⟩
  let t := |s.im|
  have hTt : max T (max 1 A) + 3 ≤ t := (le_max_left ..).trans hsize
  have ht3 : 3 ≤ t := (le_max_left 3 Z).trans ((le_max_right ..).trans hsize)
  have htZ : Z ≤ t := (le_max_right 3 Z).trans ((le_max_right ..).trans hsize)
  have geom {u : ℂ} (hu : u ∈ Metric.closedBall c r₃) :
      u.re ∈ Ioo (0 : ℝ) 4 ∧ b < u.re ∧ max T (max 1 A) < |u.im| ∧ |u.im| ≤ t + 2 := by
    have hdist := mem_closedBall_iff_norm.mp hu
    have hre := abs_le.mp ((Complex.abs_re_le_norm (u-c)).trans hdist)
    have him := (Complex.abs_im_le_norm (u-c)).trans hdist
    change -r₃ ≤ u.re - 2 ∧ u.re - 2 ≤ r₃ at hre
    change |u.im - s.im| ≤ r₃ at him
    have hdiff := abs_le.mp ((abs_abs_sub_abs_le_abs_sub _ _).trans him)
    change -r₃ ≤ |u.im| - t ∧ |u.im| - t ≤ r₃ at hdiff
    exact ⟨⟨by linarith [hre.1], by linarith [hre.2]⟩, by linarith [hre.1],
      by linarith [hdiff.1], by linarith [hdiff.2]⟩
  have reg {u : ℂ} (hu : u ∈ Metric.closedBall c r₃) : AnalyticAt ℂ L u ∧ L u ≠ 0 := by
    obtain ⟨hre, hz, hlo, _⟩ := geom hu
    have hre' := (isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hre
    have him' := (isOpen_Ioo.preimage Complex.continuous_im.abs).mem_nhds
      (show u ∈ (fun w : ℂ ↦ |w.im|) ⁻¹' Ioo (max T (max 1 A)) (|u.im| + 1)
        from ⟨hlo, by linarith⟩)
    have han : AnalyticAt ℂ L u := by
      apply bounded_order_analyticAt (hL (mem_univ u)) (M := (|u.im| + 1) ^ (n+1))
      filter_upwards [hre', him'] with w hw hw'
      exact (hbound (Ioo_subset_Icc_self hw) hw'.1.le).trans
        (pow_le_pow_left₀ (abs_nonneg _) hw'.2.le _)
    exact ⟨han, (hL (mem_univ u)).meromorphicOrderAt_eq_zero_iff.mp
      (le_antisymm (hzero u hz) han.meromorphicOrderAt_nonneg)⟩
  have hcm : c ∈ Metric.closedBall c r₃ :=
    Metric.mem_closedBall_self (by linarith)
  have hs₀ : s ∈ Metric.closedBall c r₀ := by
    rw [mem_closedBall_iff_norm]
    have he : s - c = ((s.re - 2 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [c]
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_le]
    dsimp [r₀]
    constructor <;> linarith [hs.1, hs.2]
  have hcinv : ‖(L c)⁻¹‖ ≤ Z := by
    let sc : Complex.re ⁻¹' Ioi (1 : ℝ) := ⟨c, by change (1:ℝ) < 2; norm_num⟩
    have h := (finiteHeckeL_zeroFreeRegion_euler F χ sc (by norm_num : (1:ℝ) < 2)
      (show (2:ℝ) ≤ (sc:ℂ).re from le_rfl)).2
    rw [← hSeries sc] at h
    rw [norm_inv, inv_eq_one_div, div_le_iff₀ (norm_pos_iff.mpr (reg hcm).2)]
    simpa [Z, sc, mul_comm] using h
  have hratio (u : ℂ) (hu : u ∈ Metric.closedBall c r₃) : ‖L u / L c‖ ≤ t ^ e := by
    obtain ⟨hre, _, hlo, hhi⟩ := geom hu
    have ht : t + 2 ≤ t ^ 2 := by nlinarith
    have hu' := (hbound (Ioo_subset_Icc_self hre) hlo.le).trans
      (pow_le_pow_left₀ (abs_nonneg _) (hhi.trans ht) _)
    calc
      ‖L u / L c‖ = ‖L u‖ * ‖(L c)⁻¹‖ := by rw [div_eq_mul_inv, norm_mul]
      _ ≤ (t ^ 2) ^ (n + 1) * t := by
        exact mul_le_mul hu' (hcinv.trans htZ) (norm_nonneg _) (by positivity)
      _ = t ^ e := by dsimp [e]; ring
  have hepos : 0 < e := by dsimp [e]; omega
  have ht1 : 1 < t ^ e := one_lt_pow₀ (by linarith) hepos.ne'
  have hm {r : ℝ} (hr : r ≤ r₃) {w : ℂ} (hw : w ∈ Metric.closedBall c r) :
      w ∈ Metric.closedBall c r₃ := Metric.closedBall_subset_closedBall hr hw
  have hsum : ∑ᶠ ρ ∈ Metric.closedBall c r₁, (analyticOrderNatAt L ρ : ℂ) / (s - ρ) = 0 := by
    apply finsum_mem_eq_zero_of_forall_eq_zero
    intro ρ hρ
    have hne := (reg (hm (by linarith) hρ)).2
    have ho : analyticOrderAt L ρ = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hne)
    simp [analyticOrderNatAt, ho]
  have hreg := reg (hm (by linarith) hs₀)
  refine ⟨hreg.1, hreg.2, ?_⟩
  have hlandau := landau_norm_logDeriv_sub_le ht1 hr₀ h₀₁ h₁₂ h₂₃
    (fun _ hu ↦ (reg hu).1) (reg hcm).2 hratio hs₀ hreg.2
  rw [hsum, sub_zero, Real.log_pow] at hlandau
  simpa only [K, t, mul_assoc] using hlandau

/-- Pointwise absolute envelope for the causal first Riesz kernel with a
logarithmic numerator. -/
theorem norm_causalRieszKernel_of_log {s A c : ℂ} {C : ℝ} (hC : 0 ≤ C)
    (ht : 1 ≤ |s.im|) (hA : ‖A‖ ≤ C * Real.log |s.im|) :
    ‖(A - c / (s-1)) / (s * (s+1))‖ ≤
      (4 * (2*C + ‖c‖)) * (1 + |s.im|) ^ (-(3/2 : ℝ)) := by
  let t := |s.im|
  have ht₀ : 0 < t := zero_lt_one.trans_le ht
  have hplus : t ≤ ‖s+1‖ := by simpa [t] using Complex.abs_im_le_norm (s+1)
  have hminus : t ≤ ‖s-1‖ := by simpa [t] using Complex.abs_im_le_norm (s-1)
  have hp : 0 < 1+t := by positivity
  have hrt : 1 ≤ Real.sqrt (1+t) := by
    rw [Real.one_le_sqrt]
    linarith
  have hlog : Real.log t ≤ 2 * Real.sqrt (1+t) := by
    have h := Real.log_le_self (Real.sqrt_nonneg t)
    rw [Real.log_sqrt ht₀.le] at h
    linarith [Real.sqrt_le_sqrt (show t ≤ 1+t by linarith)]
  have hnum : ‖A - c / (s-1)‖ ≤ (2*C + ‖c‖) * Real.sqrt (1+t) := by
    calc
      _ ≤ ‖A‖ + ‖c‖ / ‖s-1‖ := by simpa only [norm_div] using norm_sub_le A (c/(s-1))
      _ ≤ C * (2 * Real.sqrt (1+t)) + ‖c‖ :=
        add_le_add (hA.trans (mul_le_mul_of_nonneg_left hlog hC))
          (div_le_self (norm_nonneg _) (ht.trans hminus))
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hrt (norm_nonneg c)]
  have htden : t^2 ≤ ‖s * (s+1)‖ := by
    rw [norm_mul, sq]
    exact mul_le_mul (Complex.abs_im_le_norm s) hplus ht₀.le (norm_nonneg _)
  have hexp : Real.sqrt (1+t) / (1+t)^2 = (1+t)^(-(3/2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_two, ← Real.rpow_sub hp]
    norm_num
  rw [norm_div]
  calc
    _ ≤ ((2*C + ‖c‖) * Real.sqrt (1+t)) / t^2 :=
      div_le_div₀ (by positivity) hnum (by positivity) htden
    _ ≤ (4 * (2*C + ‖c‖)) * (Real.sqrt (1+t) / (1+t)^2) := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
      have hbase : (1 + t)^2 ≤ 4*t^2 := by nlinarith [sq_nonneg (t-1)]
      nlinarith [mul_le_mul_of_nonneg_left hbase
        (show 0 ≤ (2*C + ‖c‖) * Real.sqrt (1+t) by positivity)]
    _ = _ := by rw [hexp]

/-- The symmetrized logarithmic derivative with its continuous causal main
term admits an integrable `(1+|t|)^{-3/2}` envelope on the whole interior
strip. The constant can depend on the character, strip and main term. -/
theorem finiteHeckeL_causalRieszKernel_fixedStrip
    {F : Type*} [Field F] [NumberField F]
    (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)) (L : ℂ → ℂ)
    (hL : MeromorphicNFOn L univ)
    (hSeries : ∀ s : Complex.re ⁻¹' Ioi (1 : ℝ), L s = finiteHeckeL χ s)
    {b d : ℝ} (hb : 0 ≤ b) (hbd : b < d) (hd : d < 2)
    (hzero : ∀ z : ℂ, b < z.re → meromorphicOrderAt L z ≤ 0) (c : ℂ) :
    ∃ C T : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc d 2 → T ≤ |s.im| →
      ‖((-logDeriv L s - star (logDeriv L (star s))) / 2 - c / (s-1)) /
        (s*(s+1))‖ ≤ C * (1 + |s.im|) ^ (-(3/2 : ℝ)) := by
  obtain ⟨K, T, hK, hbound⟩ :=
    finiteHeckeL_logDeriv_fixedStrip_of_zeroFree χ L hL hSeries hb hbd hd hzero
  refine ⟨4 * (2*K + ‖c‖), max T 1, by positivity, ?_⟩
  intro s hs ht
  have hsT := (le_max_left T 1).trans ht
  apply norm_causalRieszKernel_of_log hK.le ((le_max_right T 1).trans ht)
  have h := (hbound s hs hsT).2.2
  have h' : ‖logDeriv L (star s)‖ ≤ K * Real.log |s.im| := by
    simpa only [Complex.star_def, Complex.conj_im, abs_neg] using
      (hbound (star s) (by simpa using hs) (by simpa using hsT)).2.2
  rw [norm_div, show ‖(2 : ℂ)‖ = 2 by norm_num, div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
  calc
    _ ≤ ‖-logDeriv L s‖ + ‖star (logDeriv L (star s))‖ := norm_sub_le _ _
    _ ≤ _ := by rw [norm_neg, norm_star, mul_two]; exact add_le_add h h'

end FixedStrip

/-! ## The continuous causal center for the first Riesz kernel -/

section CausalCenter


open MeasureTheory Set

/-- The principal main term which starts with value and derivative zero at one
has an absolutely integrable Mellin symbol on each Euler line. -/
theorem mellin_causalRieszCenter {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun x : ℝ ↦ ((x : ℂ) - 1)^2 / 2 * (x : ℂ)^(-s-2)) (Ioi 1) ∧
    (∫ x in Ioi (1 : ℝ), ((x : ℂ)-1)^2 / 2 * (x : ℂ)^(-s-2)) =
      1 / (s * (s-1) * (s+1)) := by
  have h₀ : (-s).re < -1 := by simp; linarith
  have h₁ : (-s-1).re < -1 := by simp; linarith
  have h₂ : (-s-2).re < -1 := by simp; linarith
  have I₀ := integrableOn_Ioi_cpow_of_lt h₀ zero_lt_one
  have I₁ := integrableOn_Ioi_cpow_of_lt h₁ zero_lt_one
  have I₂ := integrableOn_Ioi_cpow_of_lt h₂ zero_lt_one
  have eq : ∀ᵐ x : ℝ ∂volume.restrict (Ioi (1 : ℝ)),
      ((x : ℂ)-1)^2 / 2 * (x : ℂ)^(-s-2) =
        (1/2:ℂ) * ((x:ℂ)^(-s) - 2 * (x:ℂ)^(-s-1) + (x:ℂ)^(-s-2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx' : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ((zero_lt_one.trans hx).ne')
    have e₀ : (x:ℂ)^(-s) = (x:ℂ)^(-s-2) * (x:ℂ)^2 := by
      calc
        _ = (x:ℂ)^((-s-2)+2) := by congr 1; ring
        _ = _ := by rw [Complex.cpow_add _ _ hx', Complex.cpow_ofNat]
    have e₁ : (x:ℂ)^(-s-1) = (x:ℂ)^(-s-2) * x := by
      calc
        _ = (x:ℂ)^((-s-2)+1) := by congr 1; ring
        _ = _ := by rw [Complex.cpow_add _ _ hx', Complex.cpow_one]
    rw [e₀, e₁]
    ring
  have I₁' : IntegrableOn (fun x : ℝ ↦ (2:ℂ) * (x:ℂ)^(-s-1)) (Ioi 1) := I₁.const_mul 2
  have I₀₁ : IntegrableOn (fun x : ℝ ↦ (x:ℂ)^(-s) - 2 * (x:ℂ)^(-s-1)) (Ioi 1) := I₀.sub I₁'
  refine ⟨((I₀₁.add I₂).const_mul (1/2:ℂ)).congr (eq.mono fun x h ↦ h.symm), ?_⟩
  rw [integral_congr_ae eq, integral_const_mul, integral_add I₀₁ I₂,
    integral_sub I₀ I₁', integral_const_mul,
    integral_Ioi_cpow_of_lt h₀ zero_lt_one, integral_Ioi_cpow_of_lt h₁ zero_lt_one,
    integral_Ioi_cpow_of_lt h₂ zero_lt_one]
  simp only [Complex.ofReal_one, Complex.one_cpow]
  have ns : s ≠ 0 := by rintro rfl; norm_num at hs
  have ns₁ : s-1 ≠ 0 := by intro h; have he := congrArg Complex.re h; simp at he; linarith
  have ns₂ : s+1 ≠ 0 := by intro h; have he := congrArg Complex.re h; simp at he; linarith
  rw [show -s+1 = -(s-1) by ring, show -s-1+1 = -s by ring, show -s-2+1 = -(s+1) by ring]
  field_simp
  ring

/-- The sharp principal centering and the continuous causal centering differ
by a rational function holomorphic on `Re s > 0`. -/
theorem causalRieszCenter_symbol_eq {s A c : ℂ} (hs : s ≠ 0) (h₁ : s ≠ 1) (h₂ : s ≠ -1) :
    A / (s * (s+1)) - c / (s*(s-1)*(s+1)) =
      (A / (s*(s+1)) - c/(2*(s-1))) + c*(s+2)/(2*s*(s+1)) := by
  have hsub : s-1 ≠ 0 := sub_ne_zero.mpr h₁
  have hadd : s+1 ≠ 0 := by intro h; apply h₂; linear_combination h
  field_simp
  ring

end CausalCenter

/-! ## An absolute contour shift for a first Riesz integral -/

section ContourShift


open Complex Filter Function MeasureTheory Set
open scoped Asymptotics Interval Topology

local notation "vpt" => (fun (x y : ℝ) ↦ (x : ℂ) + y * Complex.I)
local notation "atAbs" => comap (abs : ℝ → ℝ) atTop

private theorem riesz_verticalIntegrable_of_envelope {F : ℂ → ℂ} {a b σ : ℝ} {g : ℝ → ℝ}
    (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc a b)) (hσ : σ ∈ Icc a b)
    (hg : Integrable g)
    (hG : ∀ᶠ y : ℝ in atAbs, ∀ r ∈ Icc a b, ‖F (vpt r y)‖ ≤ g y) :
    Complex.VerticalIntegrable F σ := by
  have hcont : Continuous (fun y : ℝ ↦ F (vpt σ y)) := by
    refine hF.continuousOn.comp_continuous (by fun_prop) fun y ↦ ?_
    simpa using hσ
  apply hcont.locallyIntegrable.integrable_of_isBigO_cocompact _ (hg.integrableAtFilter _)
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨1, ?_⟩
  rw [cocompact_eq_atBot_atTop, ← comap_abs_atTop]
  filter_upwards [hG] with y hy
  simpa only [one_mul, Real.norm_eq_abs] using (hy σ hσ).trans (le_abs_self _)

/-- A holomorphic Mellin symbol with one integrable envelope, uniform at large
heights on the closed strip, can be inverted on either boundary.
No differentiability of the physical function is required. -/
theorem mellinInv_shift_of_integrable_envelope {F : ℂ → ℂ} {a b : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b) (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc a b))
    (hg : Integrable g) (hg₀ : Tendsto g atAbs (𝓝 0))
    (hG : ∀ᶠ y : ℝ in atAbs, ∀ r ∈ Icc a b, ‖F (vpt r y)‖ ≤ g y)
    {x : ℝ} (hx : 1 ≤ x) :
    mellinInv a F x = mellinInv b F x := by
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  let P (s : ℂ) := (x : ℂ) ^ (-s)
  let H (s : ℂ) := P s * F s
  have hP : Differentiable ℂ P :=
    differentiable_id.neg.const_cpow (.inl (Complex.ofReal_ne_zero.mpr hx₀.ne'))
  have hnorm (r y : ℝ) : ‖P (vpt r y)‖ = x ^ (-r) := by
    simp [P, Complex.norm_cpow_eq_rpow_re_of_pos hx₀]
  have hInt {r : ℝ} (hr : r ∈ Icc a b) : Complex.VerticalIntegrable H r := by
    have h := riesz_verticalIntegrable_of_envelope hF hr hg hG
    have hp : Continuous (fun y : ℝ ↦ P (vpt r y)) := hP.continuous.comp (by fun_prop)
    exact h.bdd_mul hp.aestronglyMeasurable (Eventually.of_forall fun y ↦ (hnorm r y).le)
  have hH : DifferentiableOn ℂ H (Complex.re ⁻¹' Icc a b) := hP.differentiableOn.mul hF
  have horiz : Tendsto (fun y : ℝ ↦ ∫ r in a..b, H (vpt r y)) atAbs (𝓝 0) := by
    apply squeeze_zero_norm'
    · filter_upwards [hG] with y hy
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro r hr
      have hrs := Ioc_subset_Icc_self ((uIoc_of_le hab) ▸ hr)
      have hpos : 0 ≤ g y := (norm_nonneg _).trans (hy r hrs)
      change ‖P (vpt r y) * F (vpt r y)‖ ≤ x ^ (-a) * g y
      rw [norm_mul, hnorm]
      exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le hx (neg_le_neg hrs.1))
        (hy r hrs) (norm_nonneg _) (Real.rpow_nonneg hx₀.le _)
    · simpa using (hg₀.const_mul (x^(-a))).mul_const |b-a|
  have rect (t : ℝ) :
      (∫ r in a..b, H (vpt r (-t))) - (∫ r in a..b, H (vpt r t)) +
      Complex.I • (∫ y in -t..t, H (vpt b y)) -
      Complex.I • (∫ y in -t..t, H (vpt a y)) = 0 := by
    apply Complex.integral_boundary_rect_eq_zero_of_differentiableOn H (⟨a,-t⟩ : ℂ) (⟨b,t⟩ : ℂ)
    apply hH.mono
    intro w hw
    simpa only [uIcc_of_le hab] using hw.1
  have ht : Tendsto (fun t : ℝ ↦ t) atTop atAbs := tendsto_comap_iff.mpr tendsto_abs_atTop_atTop
  have hn : Tendsto (fun t : ℝ ↦ -t) atTop atAbs := by
    apply tendsto_comap_iff.mpr
    simpa [Function.comp_def] using tendsto_abs_atTop_atTop
  have hv (r : ℝ) (hr : r ∈ Icc a b) := intervalIntegral_tendsto_integral (hInt hr)
    tendsto_neg_atTop_atBot (tendsto_id : Tendsto id atTop (atTop : Filter ℝ))
  have hlim := (((horiz.comp hn).sub (horiz.comp ht)).add
    ((hv b ⟨hab, le_rfl⟩).const_smul Complex.I)).sub ((hv a ⟨le_rfl, hab⟩).const_smul Complex.I)
  have eq := tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun t ↦ (rect t).symm)
  simp only [sub_zero, zero_add, sub_eq_zero, smul_eq_mul] at eq
  exact congrArg ((1 / (2 * Real.pi) : ℝ) • ·) (mul_left_cancel₀ Complex.I_ne_zero eq).symm

/-- A physical function whose Mellin transform agrees with a holomorphic strip
symbol on the initial line is `O(x^{-b})` for `x ≥ 1`. -/
theorem norm_le_rpow_of_mellin_strip {f : ℝ → ℂ} {F : ℂ → ℂ} {a b : ℝ} {g : ℝ → ℝ}
    (hab : a ≤ b) (hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc a b))
    (hg : Integrable g) (hg₀ : Tendsto g atAbs (𝓝 0))
    (hG : ∀ᶠ y : ℝ in atAbs, ∀ r ∈ Icc a b, ‖F (vpt r y)‖ ≤ g y)
    (hfa : MellinConvergent f a) (heq : ∀ y : ℝ, mellin f (vpt a y) = F (vpt a y))
    (hc : ∀ x : ℝ, 1 ≤ x → ContinuousAt f x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖f x‖ ≤ C * x ^ (-b) := by
  let N := ∫ y : ℝ, ‖F (vpt b y)‖
  refine ⟨(1 / (2 * Real.pi)) * N, mul_nonneg (by positivity)
    (integral_nonneg fun _ ↦ norm_nonneg _), ?_⟩
  intro x hx
  have hx₀ := zero_lt_one.trans_le hx
  have hia := riesz_verticalIntegrable_of_envelope hF ⟨le_rfl, hab⟩ hg hG
  have hif : Complex.VerticalIntegrable (mellin f) a := hia.congr (Eventually.of_forall fun y ↦ (heq y).symm)
  have hi := mellinInv_mellin_eq a f hx₀ hfa hif (hc x hx)
  have hi' : mellinInv a (mellin f) x = mellinInv a F x := by
    unfold mellinInv
    simp_rw [heq]
  rw [← hi, hi', mellinInv_shift_of_integrable_envelope hab hF hg hg₀ hG hx, mellinInv, norm_smul]
  have nn : 0 ≤ 1 / (2 * Real.pi) := by positivity
  rw [Real.norm_of_nonneg nn]
  calc (1 / (2 * Real.pi)) * ‖∫ y : ℝ, (x:ℂ)^(-(vpt b y)) • F (vpt b y)‖
    _ ≤ (1 / (2 * Real.pi)) * ∫ y : ℝ, ‖(x:ℂ)^(-(vpt b y)) • F (vpt b y)‖ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) nn
    _ = (1 / (2 * Real.pi) * N) * x ^ (-b) := by
      simp only [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos hx₀, Complex.neg_re,
        Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im, neg_zero, add_zero,
        integral_const_mul, N]
      ring

end ContourShift

/-! ## The Euler-line transform of the continuously centered ideal ramp -/

section PhysicalMellin

open Filter Function MeasureTheory NumberField Set
open scoped Topology Classical

variable {K : Type*} [Field K] [NumberField K]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 K) K)
local notation "Euler" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- The physical principal center vanishes below the first possible norm and
starts continuously with zero derivative at one. -/
def heckeCausalRiesz (χ : U) (c x : ℝ) : ℂ :=
  ((heckeFirstRieszMean χ x).re : ℂ) - (c : ℂ) * ((max (x-1) 0 : ℝ) : ℂ)^2 / 2

theorem continuous_heckeCausalRiesz (χ : U) (c : ℝ) : Continuous (heckeCausalRiesz χ c) := by
  unfold heckeCausalRiesz
  have h := continuous_heckeFirstRieszMean χ
  fun_prop

private theorem heckeCausalRiesz_of_le_one (χ : U) {c x : ℝ} (hx : x ≤ 1) :
    heckeCausalRiesz χ c x = 0 := by
  have h : heckeFirstRieszMean χ x = 0 := by
    apply finsum_eq_zero_of_forall_eq_zero
    intro I
    have hn : (1 : ℝ) ≤ I.val.absNorm := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
    simp [max_eq_right (sub_nonpos.mpr (hx.trans hn))]
  simp [heckeCausalRiesz, h, max_eq_right (sub_nonpos.mpr hx)]

/-- The actual finite ideal ramp admits an absolutely convergent forward
Mellin integral on the Euler half-plane after continuous causal centering. -/
theorem heckeCausalRiesz_mellin (χ : U) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ z : Euler, L z = finiteHeckeL χ z) (c : ℝ)
    {s : ℂ} (hs : 1 < s.re) :
    MellinConvergent (heckeCausalRiesz χ c) (-s-1) ∧
    mellin (heckeCausalRiesz χ c) (-s-1) =
      ((-logDeriv L s - star (logDeriv L (star s))) / 2 - c/(s-1)) / (s*(s+1)) := by
  let A (x : ℝ) := ((heckeFirstRieszMean χ x).re : ℂ) * (x:ℂ)^(-s-2)
  let B (x : ℝ) := ((x:ℂ)-1)^2 / 2 * (x:ℂ)^(-s-2)
  let W (x : ℝ) := (x:ℂ)^((-s-1)-1) • heckeCausalRiesz χ c x
  have hA : IntegrableOn A (Ioi 1) := by
    apply ((heckeFirstRieszMean_centered_laplace χ L hL he 0 hs).1).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx₀ := zero_lt_one.trans hx
    have he₀ : Complex.exp (-s * (Real.log x : ℂ)) = (x : ℂ) ^ (-s) := by
      rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx₀.ne'),
        Complex.ofReal_log hx₀.le, mul_comm]
    dsimp [A]
    rw [he₀, Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx₀.ne'), Complex.cpow_ofNat]
    push_cast
    ring
  have hB : IntegrableOn B (Ioi 1) := (mellin_causalRieszCenter hs).1
  have heq (x : ℝ) (hx : 1 < x) : W x = A x - (c:ℂ)*B x := by
    dsimp [W, A, B, heckeCausalRiesz]
    rw [max_eq_left (sub_nonneg.mpr hx.le), Complex.ofReal_sub, Complex.ofReal_one,
      show -s-1-1 = -s-2 by ring]
    ring
  have hI : IntegrableOn W (Ioi 1) :=
    (hA.sub (hB.const_mul (c:ℂ))).congr_fun (fun x hx ↦ (heq x hx).symm) measurableSet_Ioi
  have hind : (Ioi (1:ℝ)).indicator W = W := by
    funext x
    by_cases hx : 1 < x
    · simp [hx]
    · rw [indicator_of_notMem (show x ∉ Ioi (1:ℝ) from hx)]
      simp [W, heckeCausalRiesz_of_le_one χ (c := c) (le_of_not_gt hx)]
  have hglobal := hI.integrable_indicator measurableSet_Ioi
  rw [hind] at hglobal
  refine ⟨hglobal.integrableOn, ?_⟩
  change (∫ x in Ioi 0, W x) = _
  calc
    _ = ∫ x in Ioi 0, (Ioi (1:ℝ)).indicator W x := by rw [hind]
    _ = ∫ x in Ioi 1, W x := by
      rw [setIntegral_indicator measurableSet_Ioi, inter_eq_right.mpr (Ioi_subset_Ioi zero_le_one)]
    _ = ∫ x in Ioi 1, A x - (c:ℂ)*B x :=
      setIntegral_congr_fun measurableSet_Ioi heq
    _ = _ := by
      rw [integral_sub hA (hB.const_mul (c:ℂ)), integral_const_mul,
        show (∫ x in Ioi 1, A x) = _ from heckeFirstRieszMean_re_mellin χ L hL he hs,
        show (∫ x in Ioi 1, B x) = _ from (mellin_causalRieszCenter hs).2]
      have hn₀ : s ≠ 0 := by rintro rfl; norm_num at hs
      have hn₁ : s-1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
      have hn₂ : s+1 ≠ 0 := by intro h; have hh := congrArg Complex.re h; simp at hh; linarith
      field_simp

end PhysicalMellin

/-! ## Continuation and large-height envelope of the corrected real Hecke symbol -/

section Continuation

open Complex Filter Function Set NumberField
open scoped Topology Classical ComplexConjugate NNReal

variable {K : Type*} [Field K] [NumberField K]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 K) K)
local notation "Euler" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "Lfin(" χ ")" => Classical.choose (finiteHeckeL_exists_continuation χ)

/-- The symmetrized first Riesz symbol after continuous causal centering. -/
def causalHeckeRieszSymbol (L : ℂ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  ((-logDeriv L s - star (logDeriv L (star s))) / 2 - c/(s-1)) / (s*(s+1))

private theorem causal_analyticAt_reflection {H : ℂ → ℂ} {p : ℂ} (h : AnalyticAt ℂ H (conj p)) :
    AnalyticAt ℂ (conj ∘ H ∘ conj) p := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [((Complex.continuous_conj.tendsto p).eventually
    (Complex.analyticAt_iff_eventually_differentiableAt.mp h))] with z hz
  exact differentiableAt_conj_conj_iff.mpr hz

private theorem causal_meromorphicAt_reflection {H : ℂ → ℂ} {p : ℂ} (h : MeromorphicAt H (conj p)) :
    MeromorphicAt (fun z ↦ conj (H (conj z))) p := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  simpa [Function.comp_def, smul_eq_mul, map_sub, map_mul] using causal_analyticAt_reflection hn

private theorem causalHeckeRieszSymbol_meromorphic {L : ℂ → ℂ} (hL : MeromorphicOn L univ) (c : ℝ) :
    MeromorphicOn (causalHeckeRieszSymbol L c) univ := by
  intro z _
  have h (p : ℂ) := (hL p (mem_univ p)).deriv.div (hL p (mem_univ p))
  have hc : MeromorphicAt (fun w ↦ (c:ℂ)/(w-1)) z :=
    (MeromorphicAt.const _ _).div ((MeromorphicAt.id _).sub (MeromorphicAt.const _ _))
  have hn := ((h z).neg.sub (causal_meromorphicAt_reflection (H := logDeriv L) (h (conj z)))).div
    (MeromorphicAt.const (2:ℂ) z)
  exact (hn.sub hc).div ((MeromorphicAt.id _).mul ((MeromorphicAt.id _).add (MeromorphicAt.const _ _)))

private theorem causalHeckeRieszSymbol_analyticAt {L : ℂ → ℂ} {s : ℂ} (c : ℝ)
    (h : AnalyticAt ℂ L s) (hn : L s ≠ 0)
    (h' : AnalyticAt ℂ L (conj s)) (hn' : L (conj s) ≠ 0)
    (h₀ : s ≠ 0) (h₁ : s - 1 ≠ 0) (h₂ : s + 1 ≠ 0) :
    AnalyticAt ℂ (causalHeckeRieszSymbol L c) s := by
  have hlog : AnalyticAt ℂ (logDeriv L) s := h.deriv.div h hn
  have hlog' : AnalyticAt ℂ (logDeriv L) (conj s) := h'.deriv.div h' hn'
  have hc : AnalyticAt ℂ (fun w ↦ (c:ℂ)/(w-1)) s :=
    analyticAt_const.div (analyticAt_id.sub analyticAt_const) h₁
  have hnum := (hlog.neg.sub (causal_analyticAt_reflection hlog')).div analyticAt_const (by norm_num : (2:ℂ) ≠ 0)
  exact (hnum.sub hc).div (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ h₂)

private theorem causal_symbol_agrees_at_regular {b : ℝ} (hb : b ≤ 1) {H G : ℂ → ℂ}
    (hH : AnalyticOnNhd ℂ H {z | b < z.re}) (hG : MeromorphicOn G univ)
    (he : EqOn H G Euler) {s : ℂ} (hs : b < s.re) (hr : AnalyticAt ℂ G s) : H s = G s := by
  have hm : MeromorphicOn (H-G) {z : ℂ | b<z.re} := fun z hz ↦
    (hH z hz).meromorphicAt.sub (hG z (mem_univ _))
  have near : ∀ᶠ z : ℂ in 𝓝 (2:ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  have htop : meromorphicOrderAt (H-G) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr ((near.filter_mono nhdsWithin_le_nhds).mono
      fun z hz ↦ sub_eq_zero.mpr (he hz))
  have hsTop := hm.meromorphicOrderAt_eq_top_of_isPreconnected (convex_halfSpace_re_gt b).isPreconnected
    (show (2 : ℂ) ∈ {z : ℂ | b < z.re} by change b < 2; linarith) hs htop
  exact tendsto_nhds_unique_of_eventuallyEq (hH s hs).continuousAt.continuousWithinAt
    hr.continuousAt.continuousWithinAt ((meromorphicOrderAt_eq_top_iff.mp hsTop).mono
      fun _ h ↦ sub_eq_zero.mp h)

/-- Removing only the continuous causal principal term gives a holomorphic
extension with an integrable envelope on every interior strip. -/
theorem exists_causalHeckeRieszSymbol_of_zeroFree
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1)
    {b d : ℝ} (hb : 1/2 ≤ b) (hb₁ : b ≤ 1) (hbd : b < d) (hd : d < 2)
    (hzero : ∀ p : ℂ, b < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p) :
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {s | b < s.re} ∧
      EqOn H (causalHeckeRieszSymbol Lfin(χ) (if χ = 1 then 1 else 0)) Euler ∧
      ∃ C T : ℝ, 0 < C ∧ ∀ s : ℂ, s.re ∈ Icc d 2 → T ≤ |s.im| →
        ‖H s‖ ≤ C * (1 + |s.im|)^(-(3/2 : ℝ)) := by
  let c : ℝ := if χ = 1 then 1 else 0
  let L := Lfin(χ)
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hz' : ∀ z : ℂ, b < z.re → meromorphicOrderAt L z ≤ 0 := by
    intro z hz
    rw [meromorphicOrderAt_finiteHeckeL_continuation χ hL.1.meromorphicOn hL.2 (by linarith)]
    exact le_of_not_gt (hzero z hz)
  obtain ⟨J, hJ, hJE⟩ :=
    (hecke_centeredRealRieszLogDeriv_continuation_iff τ hτ χ hχ (a := b-1/2)
      (by linarith) (by linarith)).mpr (by simpa only [sub_add_cancel] using hzero)
  simp only [sub_add_cancel] at hJ
  let H (s : ℂ) := J s + (c:ℂ)*(s+2)/(2*s*(s+1))
  have han : AnalyticOnNhd ℂ H {s | b < s.re} := by
    intro s hs
    change b < s.re at hs
    have h₀ : s ≠ 0 := by intro e; simp [e] at hs; linarith
    have h₂ : s+1 ≠ 0 := by intro e; have h := congrArg Complex.re e; simp at h; linarith
    exact (hJ s hs).add ((analyticAt_const.mul (analyticAt_id.add analyticAt_const)).div
      ((analyticAt_const.mul analyticAt_id).mul (analyticAt_id.add analyticAt_const))
      (mul_ne_zero (mul_ne_zero two_ne_zero h₀) h₂))
  have he : EqOn H (causalHeckeRieszSymbol L c) Euler := by
    intro s hs
    have hre : 1 < s.re := hs
    have h₀ : s ≠ 0 := by rintro rfl; norm_num at hre
    have h₁ : s-1 ≠ 0 := by intro e; have h := congrArg Complex.re e; simp at h; linarith
    have h₂ : s+1 ≠ 0 := by intro e; have h := congrArg Complex.re e; simp at h; linarith
    dsimp only [H]
    rw [hJE hs]
    change ((-logDeriv L s - star (logDeriv L (star s))) / 2)/(s*(s+1)) -
      (c:ℂ)/(2*(s-1)) + (c:ℂ)*(s+2)/(2*s*(s+1)) = _
    unfold causalHeckeRieszSymbol
    field_simp
    ring
  obtain ⟨C, T, hC, hB⟩ :=
    finiteHeckeL_causalRieszKernel_fixedStrip χ L hL.1 hL.2 (by linarith) hbd hd hz' (c:ℂ)
  obtain ⟨_, T', _, hR⟩ :=
    finiteHeckeL_logDeriv_fixedStrip_of_zeroFree χ L hL.1 hL.2 (by linarith) hbd hd hz'
  refine ⟨H, han, he, C, max T (max T' 1), hC, ?_⟩
  intro s hs ht
  have ht' := (le_max_left T' 1).trans ((le_max_right ..).trans ht)
  obtain ⟨hr, hn, _⟩ := hR s hs ht'
  obtain ⟨hr', hn', _⟩ := hR (conj s) (by simpa using hs) (by simpa using ht')
  have him : 1 ≤ |s.im| := (le_max_right T' 1).trans ((le_max_right ..).trans ht)
  have h₀ : s ≠ 0 := by rintro rfl; norm_num at him
  have h₁ : s-1 ≠ 0 := by intro e; have hh := congrArg Complex.im e; simp at hh; norm_num [hh] at him
  have h₂ : s+1 ≠ 0 := by intro e; have hh := congrArg Complex.im e; simp at hh; norm_num [hh] at him
  rw [causal_symbol_agrees_at_regular hb₁ han (causalHeckeRieszSymbol_meromorphic hL.1.meromorphicOn c)
    he (hbd.trans_le hs.1) (causalHeckeRieszSymbol_analyticAt c hr hn hr' hn' h₀ h₁ h₂)]
  exact hB s hs ((le_max_left ..).trans ht)

end Continuation

/-! ## A zero-free half-plane bounds the first Hecke Riesz mean -/

section HeckeBound

open Complex Filter Function MeasureTheory NumberField Set
open scoped Topology NNReal Classical

variable {K : Type*} [Field K] [NumberField K]
local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 K) K)
local notation "vpt" => (fun (x y : ℝ) ↦ (x : ℂ) + y * Complex.I)
local notation "atAbs" => comap (abs : ℝ → ℝ) atTop

/-- If the completed Hecke function has no zero to the right of `b`,
the genuine, once-integrated real ideal sum, with its principal main term
subtracted, is bounded pointwise by `C X^(1+d)` for every `b < d < 2`. -/
theorem heckeFirstRieszMean_bound_of_zeroFree
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1)
    {b d : ℝ} (hb : 1/2 ≤ b) (hb₁ : b ≤ 1) (hbd : b < d) (hd : d < 2)
    (hzero : ∀ p : ℂ, b < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |(heckeFirstRieszMean χ x).re - (if χ=1 then 1 else 0) * x^2 / 2| ≤
        C * x ^ (1+d) := by
  let c : ℝ := if χ=1 then 1 else 0
  let L := Classical.choose (finiteHeckeL_exists_continuation χ)
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  obtain ⟨H, hH, he, D, T, hD, hB⟩ := exists_causalHeckeRieszSymbol_of_zeroFree τ hτ χ hχ hb hb₁ hbd hd hzero
  let F (z : ℂ) := H (-z-1)
  let g (y : ℝ) := D * (1+|y|)^(-(3/2 : ℝ))
  have hstr {z : ℂ} (hz : z.re ∈ Icc (-3:ℝ) (-(1+d))) :
      (-z-1).re ∈ Icc d 2 := by
    simp only [sub_re, neg_re, one_re]
    constructor <;> linarith [hz.1, hz.2]
  have hF : DifferentiableOn ℂ F (Complex.re ⁻¹' Icc (-3:ℝ) (-(1+d))) := by
    intro z hz
    exact ((hH (-z-1) (hbd.trans_le (hstr hz).1)).differentiableAt.comp z
      (differentiableAt_id.neg.sub_const 1)).differentiableWithinAt
  have hg : Integrable g := by
    have hi : Integrable (fun y : ℝ ↦ (1+‖y‖)^(-(3/2 : ℝ))) := integrable_one_add_norm (by norm_num)
    simpa [g, Real.norm_eq_abs] using hi.const_mul D
  have hg₀ : Tendsto g atAbs (𝓝 0) := by
    have hu := tendsto_atTop_add_const_left atAbs (1:ℝ) (tendsto_comap :
      Tendsto (abs : ℝ → ℝ) atAbs atTop)
    simpa [g, Function.comp_def] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0:ℝ) < 3/2)).comp hu).const_mul D
  have heuv : ∀ᶠ y : ℝ in atAbs, ∀ r ∈ Icc (-3:ℝ) (-(1+d)), ‖F (vpt r y)‖ ≤ g y := by
    filter_upwards [(tendsto_comap : Tendsto (abs : ℝ → ℝ) atAbs atTop).eventually_ge_atTop T]
      with y hy r hr
    have hz : (vpt r y).re ∈ Icc (-3:ℝ) (-(1+d)) := by simpa using hr
    simpa [F, g] using hB (-(vpt r y)-1) (hstr hz) (by simpa using hy)
  have hforward (z : ℂ) (hz : z.re = -3) :
      MellinConvergent (heckeCausalRiesz χ c) z ∧ mellin (heckeCausalRiesz χ c) z = F z := by
    let s := -z-1
    have hs : 1 < s.re := by norm_num [s, hz]
    have ht := heckeCausalRiesz_mellin χ L hL.1 hL.2 c hs
    have hz' : -s-1 = z := by dsimp [s]; ring
    rw [hz'] at ht
    exact ⟨ht.1, ht.2.trans (he hs).symm⟩
  have ha : MellinConvergent (heckeCausalRiesz χ c) ((-3 : ℝ) : ℂ) :=
    (hforward _ (by norm_num)).1
  have hline (y : ℝ) : mellin (heckeCausalRiesz χ c) (vpt (-3) y) = F (vpt (-3) y) :=
    (hforward _ (by simp)).2
  obtain ⟨A, hA, hbound⟩ := norm_le_rpow_of_mellin_strip (by linarith : (-3:ℝ) ≤ -(1+d)) hF
    hg hg₀ heuv ha hline (fun x _ ↦ (continuous_heckeCausalRiesz χ c).continuousAt (x := x))
  refine ⟨A+1, by linarith, ?_⟩
  intro x hx
  have ht := hbound x hx
  have pow : x ≤ x^(1+d) := by
    calc
      _ = x^(1:ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  have hnorm : ‖heckeCausalRiesz χ c x‖ = |(heckeFirstRieszMean χ x).re - c*(x-1)^2/2| := by
    unfold heckeCausalRiesz
    rw [max_eq_left (sub_nonneg.mpr hx)]
    norm_cast
  rw [hnorm, neg_neg] at ht
  have csmall : |c*(x-1/2)| ≤ x := by
    rw [abs_mul, abs_of_nonneg (show 0 ≤ x-1/2 by linarith)]
    by_cases hc : χ=1
    · simp [c, hc]
    · simpa [c, hc] using zero_le_one.trans hx
  change |(heckeFirstRieszMean χ x).re - c*x^2/2| ≤ _
  rw [show (heckeFirstRieszMean χ x).re - c*x^2/2 =
    ((heckeFirstRieszMean χ x).re - c*(x-1)^2/2) - c*(x-1/2) by ring]
  exact (abs_sub _ _).trans ((add_le_add ht (csmall.trans pow)).trans_eq (by ring))

/-- Epsilon formulation of the integrated Hecke error bound, including
exponents larger than the fixed contour range. -/
theorem heckeFirstRieszMean_bound_of_zeroFree_epsilon
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1)
    {b : ℝ} (hb : 1/2 ≤ b) (hb₁ : b ≤ 1)
    (hzero : ∀ p : ℂ, b < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |(heckeFirstRieszMean χ x).re - (if χ=1 then 1 else 0) * x^2 / 2| ≤
        C * x ^ (1+b+ε) := by
  let d := min (b+ε) ((b+2)/2)
  have hbd : b < d := lt_min (by linarith) (by linarith)
  have hd : d < 2 := (min_le_right ..).trans_lt (by linarith)
  obtain ⟨C, hC, h⟩ := heckeFirstRieszMean_bound_of_zeroFree τ hτ χ hχ hb hb₁ hbd hd hzero
  refine ⟨C, hC, fun x hx ↦ (h x hx).trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hx ?_) hC)⟩
  linarith [show d ≤ b+ε from min_le_left ..]

end HeckeBound

end RiemannMasullo
