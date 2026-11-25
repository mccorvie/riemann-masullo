module

public import RiemannMasullo.Ch13_ZerosHecke.Targets
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Detecting Hecke zeros from the real first Riesz transform

The reflected logarithmic derivative occurring in the Mellin transform of the real
first Riesz mean detects both members of a conjugate pair. Their orders add. A real
zero has a negative residue in the resulting transform. These facts apply in the
open critical strip to every number field and unitary Hecke character.
-/

@[expose] public noncomputable section

open Complex Filter Function Set NumberField
open scoped Topology ComplexConjugate NNReal Classical

namespace RiemannMasullo

private theorem riesz_mul_logDeriv_tendsto {L : ℂ → ℂ} {p : ℂ} (hL : MeromorphicAt L p) :
    Tendsto (fun z ↦ (z - p) * logDeriv L z) (𝓝[≠] p)
      (𝓝 ((meromorphicOrderAt L p).untop₀ : ℂ)) := by
  by_cases ht : meromorphicOrderAt L p = ⊤
  · have he := logDeriv_congr_nhdsNE (meromorphicOrderAt_eq_top_iff.mp ht)
    apply (tendsto_const_nhds (x := ((meromorphicOrderAt L p).untop₀ : ℂ))).congr'
    filter_upwards [he] with z hz
    simp [ht, hz, logDeriv_apply]
  obtain ⟨g, hg, hgp, he⟩ := (meromorphicOrderAt_ne_top_iff hL).mp ht
  let n := (meromorphicOrderAt L p).untop₀
  have hc : ContinuousAt (logDeriv g) p := hg.deriv.continuousAt.div hg.continuousAt hgp
  have hlin : Tendsto (fun z : ℂ ↦ z - p) (𝓝[≠] p) (𝓝 0) := by
    rw [← sub_self p]
    exact (show ContinuousAt (fun z : ℂ ↦ z - p) p by fun_prop).continuousWithinAt
  have hlim := tendsto_const_nhds (x := (n : ℂ)) |>.add (hlin.mul hc.continuousWithinAt)
  apply (by simpa only [zero_mul, add_zero] using hlim :
    Tendsto (fun z ↦ (n : ℂ) + (z - p) * logDeriv g z) (𝓝[≠] p) (𝓝 (n : ℂ))).congr'
  filter_upwards [logDeriv_congr_nhdsNE he, hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
    (hg.continuousAt.eventually_ne hgp).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with z hz hga hgz hzp
  have hd : z - p ≠ 0 := sub_ne_zero.mpr hzp
  have hdiff : DifferentiableAt ℂ (fun w : ℂ ↦ w - p) z := by fun_prop
  change logDeriv L z = logDeriv ((fun w : ℂ ↦ (w - p) ^ n) * g) z at hz
  rw [hz, logDeriv_mul (f := fun w : ℂ ↦ (w - p) ^ n) (g := g) z (zpow_ne_zero n hd) hgz (hdiff.zpow (Or.inl hd)) hga.differentiableAt,
    logDeriv_fun_zpow hdiff n]
  simp only [logDeriv_apply, deriv_sub_const, deriv_id'', one_div]
  field_simp [hd]

/-- Multiplication by the local coordinate extracts the sum of the two orders in the
real first Riesz transform. The formula holds even for a meromorphic pole of the input. -/
theorem tendsto_mul_reflected_logDeriv_riesz {L : ℂ → ℂ} {p : ℂ}
    (hL : MeromorphicAt L p) (hLc : MeromorphicAt L (conj p))
    (hp : p ≠ 0) (hp' : p + 1 ≠ 0) :
    Tendsto (fun z ↦ (z - p) * (((-logDeriv L z - conj (logDeriv L (conj z))) / 2) /
      (z * (z + 1)))) (𝓝[≠] p)
      (𝓝 (((-((meromorphicOrderAt L p).untop₀ : ℂ) -
        ((meromorphicOrderAt L (conj p)).untop₀ : ℂ)) / 2) / (p * (p + 1)))) := by
  have hconj : Tendsto conj (𝓝[≠] p) (𝓝[≠] (conj p)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(Complex.continuous_conj.continuousAt).continuousWithinAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact fun e ↦ hz ((starRingEnd ℂ).injective e)
  have h := Complex.continuous_conj.continuousAt.tendsto.comp
    ((riesz_mul_logDeriv_tendsto hLc).comp hconj)
  have h₂ : Tendsto (fun z ↦ (z - p) * conj (logDeriv L (conj z))) (𝓝[≠] p)
      (𝓝 ((meromorphicOrderAt L (conj p)).untop₀ : ℂ)) := by
    simpa [Function.comp_def, map_sub, map_mul] using h
  have hd : Tendsto (fun z : ℂ ↦ z * (z + 1)) (𝓝[≠] p) (𝓝 (p * (p + 1))) :=
    (show ContinuousAt (fun z : ℂ ↦ z * (z + 1)) p by fun_prop).continuousWithinAt
  have he := (((riesz_mul_logDeriv_tendsto hL).neg.sub h₂).div_const 2).div hd (mul_ne_zero hp hp')
  apply he.congr' (Eventually.of_forall fun z ↦ ?_)
  simp only [Pi.div_apply]
  ring

/-- Meromorphic continuation predicted by the Euler-half-plane Mellin identity for
the centered real first Riesz mean. The parameter is one for the principal
character and zero otherwise. -/
def centeredRealRieszLogDeriv (L : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℂ :=
  ((-logDeriv L z - conj (logDeriv L (conj z))) / 2) / (z * (z + 1)) - c / (2 * (z - 1))

private theorem riesz_analyticAt_reflect {H : ℂ → ℂ} {p : ℂ} (h : AnalyticAt ℂ H (conj p)) :
    AnalyticAt ℂ (conj ∘ H ∘ conj) p := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [((Complex.continuous_conj.tendsto p).eventually
    (Complex.analyticAt_iff_eventually_differentiableAt.mp h))] with z hz
  exact differentiableAt_conj_conj_iff.mpr hz

private theorem riesz_meromorphicAt_reflect {H : ℂ → ℂ} {p : ℂ} (h : MeromorphicAt H (conj p)) :
    MeromorphicAt (fun z ↦ conj (H (conj z))) p := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n, ?_⟩
  simpa [Function.comp_def, smul_eq_mul, map_sub, map_mul] using riesz_analyticAt_reflect hn

private theorem centeredRealRieszLogDeriv_meromorphic {L : ℂ → ℂ}
    (hL : MeromorphicOn L univ) (c : ℝ) : MeromorphicOn (centeredRealRieszLogDeriv L c) univ := by
  intro p _
  have h (z : ℂ) : MeromorphicAt (logDeriv L) z :=
    (hL z (mem_univ _)).deriv.div (hL z (mem_univ _))
  have href := riesz_meromorphicAt_reflect (p := p) (h (conj p))
  unfold centeredRealRieszLogDeriv
  apply MeromorphicAt.sub
  · exact ((h p).neg.sub href |>.div (MeromorphicAt.const 2 p)).div
      ((MeromorphicAt.id p).mul ((MeromorphicAt.id p).add (MeromorphicAt.const 1 p)))
  · fun_prop

/-- Holomorphic continuation of the centered Euler expression forces the sum of the
orders at a conjugate pair to vanish in its half-plane, away from the polar
centering point and the two kernel poles. Agreement is required only on the
original Euler half-plane. -/
theorem centeredRealRieszLogDeriv_order_add_eq_zero {L H : ℂ → ℂ} {c b : ℝ}
    (hL : MeromorphicOn L univ) (hH : AnalyticOnNhd ℂ H {z | b < z.re})
    (hb : b ≤ 1) (he : EqOn H (centeredRealRieszLogDeriv L c) {z | 1 < z.re})
    {p : ℂ} (hbp : b < p.re) (hp : p ≠ 0) (hp' : p + 1 ≠ 0) (hp₁ : p ≠ 1) :
    (meromorphicOrderAt L p).untop₀ + (meromorphicOrderAt L (conj p)).untop₀ = 0 := by
  let F := centeredRealRieszLogDeriv L c
  have hm : MeromorphicOn (H - F) {z : ℂ | b < z.re} := fun z hz ↦
    (hH z hz).meromorphicAt.sub (centeredRealRieszLogDeriv_meromorphic hL c z (mem_univ _))
  have h₂ : (2 : ℂ) ∈ {z : ℂ | 1 < z.re} := by norm_num
  have hn : ∀ᶠ z : ℂ in 𝓝 (2 : ℂ), 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds h₂
  have ht : meromorphicOrderAt (H - F) 2 = ⊤ :=
    meromorphicOrderAt_eq_top_iff.mpr ((hn.filter_mono nhdsWithin_le_nhds).mono
      fun z hz ↦ sub_eq_zero.mpr (he hz))
  have htp := hm.meromorphicOrderAt_eq_top_of_isPreconnected (convex_halfSpace_re_gt b).isPreconnected
    (show (2 : ℂ) ∈ {z : ℂ | b < z.re} from hb.trans_lt h₂) hbp ht
  have hnear := meromorphicOrderAt_eq_top_iff.mp htp
  let C (z : ℂ) := (c : ℂ) / (2 * (z - 1))
  have hC : ContinuousAt C p :=
    continuousAt_const.div (continuousAt_const.mul (continuousAt_id.sub continuousAt_const))
      (mul_ne_zero two_ne_zero (sub_ne_zero.mpr hp₁))
  have hlim : Tendsto (fun z : ℂ ↦ (z - p) * (H z + C z)) (𝓝[≠] p) (𝓝 0) := by
    have h := (show ContinuousAt (fun z : ℂ ↦ (z - p) * (H z + C z)) p from
      (continuousAt_id.sub continuousAt_const).mul ((hH p hbp).continuousAt.add hC)).continuousWithinAt
        (s := {p}ᶜ)
    simpa only [ContinuousWithinAt, sub_self, zero_mul] using h
  have hv := tendsto_nhds_unique_of_eventuallyEq
    (tendsto_mul_reflected_logDeriv_riesz (hL p (mem_univ _)) (hL (conj p) (mem_univ _)) hp hp')
    hlim (by
      filter_upwards [hnear] with z hz
      have hz' : H z = F z := sub_eq_zero.mp hz
      rw [hz']
      simp [F, centeredRealRieszLogDeriv, C])
  have hnum := (div_eq_zero_iff.mp hv).resolve_right (mul_ne_zero hp hp')
  have hnum' := (div_eq_zero_iff.mp hnum).resolve_right two_ne_zero
  have hv' : ((meromorphicOrderAt L p).untop₀ : ℂ) + ((meromorphicOrderAt L (conj p)).untop₀ : ℂ) = 0 := by
    linear_combination -hnum'
  exact_mod_cast hv'

variable {K : Type*} [Field K] [NumberField K]

local notation "U" => PontryaginDual (IdeleClassGroup (𝓞 K) K)
local notation "Euler" => Complex.re ⁻¹' Ioi (1 : ℝ)
local notation "Lfin(" χ ")" => Classical.choose (finiteHeckeL_exists_continuation χ)

private theorem riesz_hecke_order_in_strip (χ : U) {L : ℂ → ℂ} (hL : MeromorphicNFOn L univ)
    (h : ∀ s : Euler, L s = finiteHeckeL χ s) {p : ℂ} (hp₀ : 0 < p.re) (hp₁ : p.re < 1) :
    0 ≤ meromorphicOrderAt L p ∧ meromorphicOrderAt L p ≠ ⊤ := by
  have hC := (completedHeckeL_exists_continuation χ).choose_spec
  have hcmp := meromorphicOrderAt_finiteHeckeL_continuation χ hL.meromorphicOn h hp₀
  have ha : AnalyticAt ℂ (continuedCompletedHeckeL χ) p := by
    by_cases hχ : χ.toMonoidHom.comp (ideleClassNorm K).ker.subtype = 1
    · obtain ⟨t, ⟨_, _, _, han⟩, _⟩ :=
        completedHeckeL_continuation_simplePoles χ _ hC.1 hC.2 hχ
      apply han p
      simp only [mem_compl_iff, mem_insert_iff, mem_singleton_iff, not_or]
      constructor
      · intro e
        have : p.re = 0 := by simp [e, Complex.mul_re]
        linarith
      · intro e
        have : p.re = 1 := by simp [e, Complex.mul_re]
        linarith
    · exact (completedHeckeL_continuation_entire χ _ hC.1 hC.2 hχ).analyticAt p
  refine ⟨hcmp.trans_ge ha.meromorphicOrderAt_nonneg, ?_⟩
  have h₂ : meromorphicOrderAt L 2 = 0 := (hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr (by
    rw [show L 2 = finiteHeckeL χ ⟨2, by norm_num⟩ from h ⟨2, by norm_num⟩]
    exact finiteHeckeL_ne_zero_of_one_lt_re χ _)
  exact hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ p) (by simp [h₂])

/-- A holomorphic continuation of the real Riesz expression excludes every completed
Hecke zero in the part of the open critical strip it reaches. No self-duality of the
character or hypothesis on possible real exceptional zeros is required. -/
theorem hecke_no_zero_of_centeredRealRieszLogDeriv (χ : U) {L H : ℂ → ℂ}
    (hL : MeromorphicNFOn L univ) (h : ∀ s : Euler, L s = finiteHeckeL χ s)
    {c b : ℝ} (hb : b ≤ 1) (hH : AnalyticOnNhd ℂ H {z | b < z.re})
    (he : EqOn H (centeredRealRieszLogDeriv L c) Euler)
    {p : ℂ} (hbp : b < p.re) (hp₀ : 0 < p.re) (hp₁ : p.re < 1) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) p = 0 := by
  rw [← meromorphicOrderAt_finiteHeckeL_continuation χ hL.meromorphicOn h hp₀]
  have hp : p ≠ 0 := fun e ↦ by simp [e] at hp₀
  have hp' : p + 1 ≠ 0 := fun e ↦ by
    have := congrArg Complex.re e
    simp at this
    linarith
  have hp₁' : p ≠ 1 := fun e ↦ by simp [e] at hp₁
  have hs := centeredRealRieszLogDeriv_order_add_eq_zero hL.meromorphicOn hH hb he hbp hp hp' hp₁'
  obtain ⟨ha, hat⟩ := riesz_hecke_order_in_strip χ hL h hp₀ hp₁
  obtain ⟨hd, hdt⟩ := riesz_hecke_order_in_strip χ hL h (p := conj p) hp₀ hp₁
  lift meromorphicOrderAt L p to ℤ using hat with n hn
  lift meromorphicOrderAt L (conj p) to ℤ using hdt with m hm
  simp only [WithTop.untop₀_coe] at hs
  have hn₀ : (0 : ℤ) ≤ n := WithTop.coe_le_coe.mp ha
  have hm₀ : (0 : ℤ) ≤ m := WithTop.coe_le_coe.mp hd
  exact_mod_cast (show n = 0 by omega)

/-- At an actual real Hecke zero in the open strip, the residue of the real Riesz
transform is strictly negative. Thus it cannot be the boundary pole of a positive
Mellin integral approached from the right. -/
theorem hecke_realRiesz_residue_negative (χ : U) {L : ℂ → ℂ}
    (hL : MeromorphicNFOn L univ) (h : ∀ s : Euler, L s = finiteHeckeL χ s) {x : ℝ}
    (hx₀ : 0 < x) (hx₁ : x < 1) (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (x : ℂ))
    (c : ℝ) : ∃ r : ℝ, r < 0 ∧ Tendsto
      (fun z : ℂ ↦ (z - x) * centeredRealRieszLogDeriv L c z) (𝓝[≠] (x : ℂ)) (𝓝 (r : ℂ)) := by
  have hcmp := meromorphicOrderAt_finiteHeckeL_continuation χ hL.meromorphicOn h (s := (x : ℂ)) hx₀
  have htop := (riesz_hecke_order_in_strip χ hL h (p := (x : ℂ)) hx₀ hx₁).2
  have hpos : 0 < meromorphicOrderAt L (x : ℂ) := by rwa [hcmp]
  let m := (meromorphicOrderAt L (x : ℂ)).untop₀
  have hm : 0 < m := by
    lift meromorphicOrderAt L (x : ℂ) to ℤ using htop with n hn
    dsimp [m]
    rw [← hn, WithTop.untop₀_coe]
    exact WithTop.coe_lt_coe.mp hpos
  refine ⟨-(m : ℝ) / (x * (x + 1)), div_neg_of_neg_of_pos (by exact neg_neg_of_pos (by exact_mod_cast hm)) (by positivity), ?_⟩
  have hx : (x : ℂ) ≠ 0 := by exact_mod_cast hx₀.ne'
  have hx' : (x : ℂ) + 1 ≠ 0 := by exact_mod_cast (show x + 1 ≠ 0 by linarith)
  have hx₁' : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx₁.ne)
  have hres := tendsto_mul_reflected_logDeriv_riesz (hL (mem_univ (x : ℂ))).meromorphicAt
    (hL (mem_univ (conj (x : ℂ)))).meromorphicAt hx hx'
  have hzero : Tendsto (fun z : ℂ ↦ (z - x) * (c / (2 * (z - 1)))) (𝓝[≠] (x : ℂ)) (𝓝 0) := by
    have hh : ContinuousAt (fun z : ℂ ↦ (z - x) * (c / (2 * (z - 1)))) (x : ℂ) :=
      (continuousAt_id.sub continuousAt_const).mul (continuousAt_const.div
        (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)) (mul_ne_zero two_ne_zero hx₁'))
    simpa only [ContinuousWithinAt, sub_self, zero_mul] using hh.continuousWithinAt (s := {(x : ℂ)}ᶜ)
  convert hres.sub hzero using 1
  · funext z
    simp [centeredRealRieszLogDeriv, mul_sub]
  · simp [m]
    ring

private theorem centeredRealRieszLogDeriv_analytic_euler (χ : U) (c : ℝ) :
    AnalyticOnNhd ℂ (centeredRealRieszLogDeriv Lfin(χ) c) Euler := by
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hlog {w : ℂ} (hw : 1 < w.re) : AnalyticAt ℂ (logDeriv Lfin(χ)) w := by
    have hn := hL.1 (mem_univ w)
    have hne : Lfin(χ) w ≠ 0 := by
      rw [show Lfin(χ) w = finiteHeckeL χ ⟨w, hw⟩ from hL.2 ⟨w, hw⟩]
      exact finiteHeckeL_ne_zero_of_one_lt_re χ _
    have ha := hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (hn.meromorphicOrderAt_eq_zero_iff.mpr hne).ge
    exact ha.deriv.div ha hne
  intro z hz
  change 1 < z.re at hz
  have h₀ : z ≠ 0 := fun e ↦ by norm_num [e] at hz
  have h₁ : z - 1 ≠ 0 := sub_ne_zero.mpr (fun e ↦ by norm_num [e] at hz)
  have hp : z + 1 ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp at this
    linarith
  unfold centeredRealRieszLogDeriv
  apply AnalyticAt.sub
  · exact (((hlog hz).neg.sub (riesz_analyticAt_reflect (p := z) (hlog hz))).div analyticAt_const two_ne_zero).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ hp)
  · exact analyticAt_const.div (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)) (mul_ne_zero two_ne_zero h₁)

/-- For a normalized unitary character, holomorphic continuation of the centered real
Riesz expression to a fixed open half-plane is equivalent to absence of completed
zeros there. The condition on the continuation is tested solely on the Euler half-plane. -/
theorem hecke_centeredRealRieszLogDeriv_continuation_iff
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1 / 2) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {z | a + 1 / 2 < z.re} ∧
      EqOn H (centeredRealRieszLogDeriv Lfin(χ) (if χ = 1 then 1 else 0)) Euler) ↔
    ∀ p : ℂ, a + 1 / 2 < p.re → ¬ 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) p := by
  classical
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  constructor
  · rintro ⟨H, hH, he⟩ p hp hz
    have hC := (completedHeckeL_exists_continuation χ).choose_spec
    have hpos : 0 < p.re := by linarith
    have hp₁ := completedHeckeL_continuation_zeros χ _ hC.1 hC.2 hpos hz
    have ho := hecke_no_zero_of_centeredRealRieszLogDeriv χ hL.1 hL.2 (by linarith) hH he hp hpos hp₁
    exact hz.ne' ho
  · intro hzero
    obtain ⟨J, hJ, he⟩ := (introTrace_normalized_continuation_iff_no_right_zeros τ hτ χ hχ a ha).mpr hzero
    let c : ℝ := if χ = 1 then 1 else 0
    let T (z : ℂ) := J (z - 1 / 2)
    let G (z : ℂ) := (-(T z + conj (T (conj z))) / 2) / (z * (z+1)) +
      c * (1 / (z^2 * (z+1)) - (z+2)/(2*z*(z+1)))
    have hT (z : ℂ) (hz : a + 1 / 2 < z.re) : AnalyticAt ℂ T z := by
      apply (hJ (z - 1 / 2) ?_).comp (f := fun w : ℂ ↦ w - 1 / 2) (x := z) (analyticAt_id.sub analyticAt_const)
      change a < (z - 1 / 2).re
      simp only [sub_re, div_ofNat_re, one_re]
      linarith
    have hG : AnalyticOnNhd ℂ G {z : ℂ | a + 1 / 2 < z.re} := by
      intro z hz
      change a + 1 / 2 < z.re at hz
      have h₀ : z ≠ 0 := fun e ↦ by simp [e] at hz; linarith
      have hp : z + 1 ≠ 0 := by
        intro e
        have := congrArg Complex.re e
        simp at this
        linarith
      have ht := hT z hz
      have htc := riesz_analyticAt_reflect (p := z) (hT (conj z) hz)
      unfold G
      apply AnalyticAt.add
      · exact ((ht.add htc).neg.div analyticAt_const two_ne_zero).div
          (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ hp)
      · fun_prop (disch := simp [h₀, hp])
    refine ⟨G, hG, ?_⟩
    apply (hG.mono (show Euler ⊆ {z : ℂ | a + 1 / 2 < z.re} from
      fun z hz ↦ lt_of_le_of_lt (by linarith) hz)).eqOn_of_preconnected_of_eventuallyEq
      (centeredRealRieszLogDeriv_analytic_euler χ c) (convex_halfSpace_re_gt 1).isPreconnected
      (show (3 : ℂ) ∈ Euler by norm_num)
    have hev : ∀ᶠ z : ℂ in 𝓝 3, 2 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hev] with z hz
    have hval {w : ℂ} (hw : 2 < w.re) :
        T w = logDeriv Lfin(χ) w + if χ = 1 then 1 / w + 1 / (w - 1) else 0 := by
      have hw' : max a 1 < (w - 1 / 2).re := by
        simp only [sub_re, div_ofNat_re, one_re, max_lt_iff]
        constructor <;> linarith
      have htt := he (x := w - 1 / 2) hw'
      simpa only [T, sub_add_cancel, sub_sub, show (1/2 : ℂ) + 1/2 = 1 by norm_num] using htt
    have hn : z ≠ 0 := fun e ↦ by norm_num [e] at hz
    have hsub : z - 1 ≠ 0 := sub_ne_zero.mpr (fun e ↦ by norm_num [e] at hz)
    have hadd : z + 1 ≠ 0 := by
      intro e
      have := congrArg Complex.re e
      simp at this
      linarith
    dsimp only [G, centeredRealRieszLogDeriv]
    rw [hval hz, hval (w := conj z) hz]
    by_cases h1 : χ = 1
    · simp [c, h1, map_add, map_sub]
      field_simp [hn, hsub, hadd]
      ring
    · simp [c, h1]
      ring

/-- Continuation of the single centered real Riesz transform to the open half-plane
right of one half detects the full critical-line assertion for that character.
Reflection and the change from finite to completed zeros use the existing formal
continuation criterion of §1.4.5. -/
theorem hecke_centeredRealRieszLogDeriv_iff_critical_line
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H {z | 1 / 2 < z.re} ∧
      EqOn H (centeredRealRieszLogDeriv Lfin(χ) (if χ = 1 then 1 else 0)) Euler) ↔
    ∀ p : ℂ, 0 < MeromorphicOn.divisor (continuedCompletedHeckeL χ) univ p → p.re = 1 / 2 := by
  have hf := hecke_centeredRealRieszLogDeriv_continuation_iff τ hτ χ hχ (a := 0) le_rfl (by norm_num)
  simp only [zero_add] at hf
  rw [hf, ← introTrace_single_character_all_continuations_iff_critical_line τ hτ χ hχ]
  constructor
  · intro h a ha
    apply (introTrace_normalized_continuation_iff_no_right_zeros τ hτ χ hχ a ha.le).mpr
    exact fun p hp ↦ h p (by linarith)
  · intro h p hp
    let a := (p.re - 1 / 2) / 2
    have ha : 0 < a := by dsimp [a]; linarith
    exact (introTrace_normalized_continuation_iff_no_right_zeros τ hτ χ hχ a ha.le).mp
      (h a ha) p (by dsimp [a]; linarith)

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1

local notation "ord(" χ ", " p ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (F := K) χ) univ p
/-- Theorem 12.5.1.1, pp. 519–520, for every positive width over one number field
is equivalent to continuation of the centered real Riesz transform for each normalized
character in the chosen chart. The integral below is the manuscript's actual zero term. -/
theorem hasSum_exteriorZeros_iff_centeredRealRieszLogDeriv
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K)) :
    (∀ a : ℝ, 0 < a → ∀ φ : BruhatCompactSupport (IdeleClassGroup (𝓞 K) K),
      (∀ g : (ideleClassNorm K).ker, φ.val g = 0) →
      HasSum (fun z : {p : {χ : U // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
          0 < ord(p.1.val, p.2) ∧ a ≤ |p.2.re - 1 / 2|} ↦ (ord(z.val.1.val, z.val.2) : ℂ) *
        ∫ g, φ.val g * ideleClassNormTwist z.val.1.val (z.val.2 - 1 / 2) g
          ∂ideleClassTamagawaMeasure K) 0) ↔
    ∀ (χ : U), (∀ t, χ (τ t) = 1) → ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H {z | 1 / 2 < z.re} ∧
      EqOn H (centeredRealRieszLogDeriv Lfin(χ) (if χ = 1 then 1 else 0)) Euler := by
  have htest (a : ℝ) := hasSum_exteriorZeros_iff_isEmpty τ hτ a
  simp only [modulatedFourierMellin, relativeVerticalStrip, preimage_univ, indicator_univ] at htest
  constructor
  · intro h χ hχ
    apply (hecke_centeredRealRieszLogDeriv_iff_critical_line τ hτ χ hχ).mpr
    intro p hp
    by_contra hn
    let a := |p.re - 1 / 2|
    have ha : 0 < a := abs_pos.mpr (sub_ne_zero.mpr hn)
    exact ((htest a).mp (h a ha)).false ⟨(⟨χ, hχ⟩, p), hp, le_rfl⟩
  · intro h a ha
    apply (htest a).mpr
    constructor
    rintro ⟨⟨⟨χ, hχ⟩, p⟩, hp, hdist⟩
    have hp' := (hecke_centeredRealRieszLogDeriv_iff_critical_line τ hτ χ hχ).mp (h χ hχ) p hp
    change a ≤ |p.re - 1 / 2| at hdist
    rw [hp', sub_self, abs_zero] at hdist
    exact ha.not_ge hdist


private theorem riesz_finite_order_at_one
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) :
    meromorphicOrderAt Lfin(χ) 1 = if χ = 1 then -1 else 0 := by
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hC := continuedCompletedHeckeL_spec χ
  rw [meromorphicOrderAt_finiteHeckeL_continuation χ hL.1.meromorphicOn hL.2 (by norm_num)]
  split_ifs with h
  · subst χ
    obtain ⟨t, ⟨_, h₀, h₁, _⟩, _⟩ := completedHeckeL_continuation_simplePoles
      (1 : U) _ hC.1 hC.2 (by ext; rfl)
    have ht : Complex.I * (t : ℂ) = 0 := by
      by_contra hne
      have hn₁ : Complex.I * (t : ℂ) ≠ 1 := by
        intro he
        have := congrArg Complex.re he
        simp [Complex.mul_re] at this
      have han := completedHeckeL_one_analyticOnNhd (F := K) _ hC.1 hC.2 (Complex.I * (t : ℂ))
        (by simpa using And.intro hne hn₁)
      have hnon := han.meromorphicOrderAt_nonneg
      rw [h₀] at hnon
      exact (WithTop.coe_lt_coe.mpr (show (-1 : ℤ) < 0 by decide)).not_ge hnon
    simpa [ht] using h₁
  · have hk : χ.toMonoidHom.comp (ideleClassNorm K).ker.subtype ≠ 1 := by
      intro he
      apply h
      ext1 g
      let u := g / τ (ideleClassNorm K g)
      have hu : u ∈ (ideleClassNorm K).ker := by
        change ideleClassNorm K (g / τ _) = 1
        rw [map_div, hτ, div_self']
      have hv := DFunLike.congr_fun he (⟨u, hu⟩ : (ideleClassNorm K).ker)
      change χ u = 1 at hv
      simpa [u, hχ] using hv
    exact le_antisymm (le_of_not_gt (fun hp ↦ (lt_irrefl (1 : ℝ))
      (completedHeckeL_continuation_zeros χ _ hC.1 hC.2 (by norm_num) hp)))
      ((completedHeckeL_continuation_entire χ _ hC.1 hC.2 hk).analyticAt 1).meromorphicOrderAt_nonneg

private theorem riesz_normal_analytic_of_zero_residue {G : ℂ → ℂ} {p : ℂ} (hG : MeromorphicOn G univ)
    (hz : Tendsto (fun z ↦ (z-p)*G z) (𝓝[≠] p) (𝓝 0)) :
    AnalyticAt ℂ (toMeromorphicNFOn G univ) p := by
  have hlin : MeromorphicAt (fun z : ℂ ↦ z-p) p := (analyticAt_id.sub analyticAt_const).meromorphicAt
  have ho := (tendsto_zero_iff_meromorphicOrderAt_pos (hlin.mul (hG p (mem_univ _)))).mp hz
  rw [meromorphicOrderAt_mul hlin (hG p (mem_univ _)), meromorphicOrderAt_id_sub_const] at ho
  apply ((meromorphicNFOn_toMeromorphicNFOn G univ) (mem_univ p)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hG (mem_univ _)]
  by_cases ht : meromorphicOrderAt G p = ⊤
  · simp [ht]
  lift meromorphicOrderAt G p to ℤ using ht with n
  have hn : (0 : ℤ) < 1 + n := by exact_mod_cast ho
  exact_mod_cast (show 0 ≤ n by omega)

private theorem riesz_normal_analytic_at_one
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) :
    AnalyticAt ℂ (toMeromorphicNFOn (centeredRealRieszLogDeriv Lfin(χ) (if χ = 1 then 1 else 0)) univ) 1 := by
  let c : ℝ := if χ = 1 then 1 else 0
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec.1
  apply riesz_normal_analytic_of_zero_residue (centeredRealRieszLogDeriv_meromorphic hL.meromorphicOn c)
  have h := tendsto_mul_reflected_logDeriv_riesz (L := Lfin(χ)) (p := 1) (hL (mem_univ _)).meromorphicAt
    (hL (mem_univ _)).meromorphicAt one_ne_zero (by norm_num)
  have ho := riesz_finite_order_at_one τ hτ χ hχ
  have hlim : Tendsto (fun z : ℂ ↦ (z-1) * (((-logDeriv Lfin(χ) z -
      conj (logDeriv Lfin(χ) (conj z))) / 2) / (z*(z+1)))) (𝓝[≠] 1) (𝓝 ((c : ℂ)/2)) := by
    convert h using 2
    simp only [map_one, ho]
    by_cases hχ' : χ = 1 <;> norm_num [c, hχ']
  have hzero := hlim.sub (tendsto_const_nhds (x := (c : ℂ)/2))
  rw [sub_self] at hzero
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with z hz
  unfold centeredRealRieszLogDeriv
  rw [mul_sub]
  congr 1
  field_simp [sub_ne_zero.mpr (show z ≠ 1 from hz)]

/-- The centered real Riesz expression has a normal-form meromorphic representative.
It agrees with the Euler formula on its entire half-plane. At every real point in
the positive half-line up to one, it is regular or has strictly negative residue.
The unshifted principal pole at one is removable after centering. -/
theorem hecke_centeredRealRieszLogDeriv_real_germs
    (τ : ℝ≥0ˣ →ₜ* IdeleClassGroup (𝓞 K) K) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ t, χ (τ t) = 1) :
    let G := centeredRealRieszLogDeriv Lfin(χ) (if χ = 1 then 1 else 0)
    ∃ H : ℂ → ℂ, MeromorphicNFOn H univ ∧ EqOn H G Euler ∧
      ∀ x : ℝ, 0 < x → x ≤ 1 → AnalyticAt ℂ H (x : ℂ) ∨ ∃ r : ℝ, r < 0 ∧
        Tendsto (fun z : ℂ ↦ (z-x) * H z) (𝓝[≠] (x : ℂ)) (𝓝 (r : ℂ)) := by
  intro G
  let c : ℝ := if χ = 1 then 1 else 0
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hm : MeromorphicOn G univ := centeredRealRieszLogDeriv_meromorphic hL.1.meromorphicOn c
  refine ⟨toMeromorphicNFOn G univ, meromorphicNFOn_toMeromorphicNFOn _ _, ?_, ?_⟩
  · intro z hz
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr ((centeredRealRieszLogDeriv_analytic_euler χ c z hz).meromorphicNFAt)]
  intro x hx hx'
  rcases hx'.eq_or_lt with rfl | hx₁
  · exact Or.inl (by simpa [G] using riesz_normal_analytic_at_one τ hτ χ hχ)
  have hcmp := meromorphicOrderAt_finiteHeckeL_continuation χ hL.1.meromorphicOn hL.2 (s := (x : ℂ)) hx
  by_cases hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL χ) (x : ℂ)
  · obtain ⟨r, hr, ht⟩ := hecke_realRiesz_residue_negative χ (L := Lfin(χ)) hL.1 hL.2 hx hx₁ hp c
    refine Or.inr ⟨r, hr, ht.congr' ?_⟩
    filter_upwards [hm.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ (x : ℂ))] with z hz
    rw [hz]
  left
  have ho : meromorphicOrderAt Lfin(χ) (x : ℂ) = 0 := le_antisymm (hcmp.trans_le (not_lt.mp hp))
    (riesz_hecke_order_in_strip χ hL.1 hL.2 hx hx₁).1
  have hn := hL.1 (mem_univ (x : ℂ))
  have hA := hn.meromorphicOrderAt_nonneg_iff_analyticAt.mp ho.ge
  have hlog : AnalyticAt ℂ (logDeriv Lfin(χ)) (x : ℂ) := hA.deriv.div hA (hn.meromorphicOrderAt_eq_zero_iff.mp ho)
  have hrc := riesz_analyticAt_reflect (H := logDeriv Lfin(χ)) (p := (x : ℂ)) (by simpa using hlog)
  have hG : AnalyticAt ℂ G (x : ℂ) := by
    change AnalyticAt ℂ (centeredRealRieszLogDeriv Lfin(χ) c) (x : ℂ)
    unfold centeredRealRieszLogDeriv
    have h₀ : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
    have h₁ : (x : ℂ) + 1 ≠ 0 := by exact_mod_cast (show x+1 ≠ 0 by linarith)
    have hsub : (x : ℂ) - 1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hx₁.ne)
    exact ((((hlog.neg.sub hrc).div analyticAt_const two_ne_zero).div
      (analyticAt_id.mul (analyticAt_id.add analyticAt_const)) (mul_ne_zero h₀ h₁))).sub
      (analyticAt_const.div (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)) (mul_ne_zero two_ne_zero hsub))
  apply ((meromorphicNFOn_toMeromorphicNFOn G univ) (mem_univ _)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn hm (mem_univ _)]
  exact hG.meromorphicOrderAt_nonneg

end RiemannMasullo
