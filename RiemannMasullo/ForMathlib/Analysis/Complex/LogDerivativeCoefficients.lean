module

public import Mathlib.Analysis.Complex.JensenFormula
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Meromorphic.LogDeriv
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Tactic

/-! # Taylor coefficients of a logarithmic derivative on a disk

The divisor on a closed disk gives a finite sum of simple poles for the logarithmic derivative.
Removing those poles leaves coefficients bounded by the Cauchy estimate at the disk radius. -/

@[expose] public noncomputable section

open Complex Filter Function Metric Set
open scoped Topology

namespace RiemannMasullo.DiskLogCoefficient

/-- The factorial-normalized Taylor coefficient at zero. -/
def coeff (f : ℂ → ℂ) (n : ℕ) : ℂ := iteratedDeriv n f 0 / n.factorial

/-- A compact-disk bound for every Taylor coefficient. -/
theorem cauchy_coeff {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖coeff f n‖ ≤ C / R^n := by
  obtain ⟨v, _, hv⟩ := (isCompact_closedBall (0 : ℂ) R).exists_isMaxOn
    ⟨0, mem_closedBall_self hR.le⟩ hf.continuousOn.norm
  refine ⟨‖f v‖, norm_nonneg _, fun n ↦ ?_⟩
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hR
    (hf.differentiableOn.diffContOnCl_ball subset_rfl) (fun z hz ↦ hv (sphere_subset_closedBall hz))
  rw [coeff, norm_div, Complex.norm_natCast]
  exact (div_le_iff₀ (by positivity : 0 < (n.factorial : ℝ))).mpr (by convert h using 1; ring)

/-- Taylor coefficients of an individual pole, with its prescribed residue. -/
theorem coeff_pole (a c : ℂ) (n : ℕ) :
    coeff (fun z : ℂ ↦ c / (z-a)) n = -c / a^(n+1) := by
  rw [show (fun z : ℂ ↦ c/(z-a)) = fun z : ℂ ↦ c*(z-a)⁻¹ by funext; simp [div_eq_mul_inv]]
  rw [coeff, iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate]
  have h := congrFun (iter_deriv_inv_linear_sub n (1 : ℂ) a) 0
  simp only [one_mul, one_pow, zero_sub, mul_one] at h
  rw [h, show (-1 - (n : ℤ)) = -((n+1 : ℕ):ℤ) by omega, zpow_neg, zpow_natCast]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  by_cases ha : a = 0
  · simp [ha]
  rw [neg_eq_neg_one_mul a, mul_pow, pow_succ (-1 : ℂ) n]
  have hm : (-1 : ℂ)^n ≠ 0 := pow_ne_zero _ (by norm_num)
  field_simp

private theorem germ_factor_sum {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0) :
    let B := closedBall (0 : ℂ) R
    let D := MeromorphicOn.divisor f B
    let S := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h B ∧
      logDeriv f =ᶠ[𝓝 0] fun z ↦ (∑ a ∈ S, (D a : ℂ)/(z-a)) + h z := by
  classical
  let B := closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor f B
  let S := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
  change ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h B ∧
    logDeriv f =ᶠ[𝓝 0] fun z ↦ (∑ a ∈ S, (D a : ℂ)/(z-a))+h z
  have hB : 0 ∈ B := mem_closedBall_self hR.le
  have htop : ∀ t : B, meromorphicOrderAt f t ≠ ⊤ := fun t ↦
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected (convex_closedBall (0 : ℂ) R).isPreconnected
      hB t.property (by rw [(hf 0 hB).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]; simp)
  have hD0 : D 0 = 0 := by
    rw [show D 0 = (meromorphicOrderAt f 0).untop₀ from hf.meromorphicOn.divisor_apply hB,
      (hf 0 hB).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]; rfl
  have hS (a : ℂ) : a ∈ S ↔ D a ≠ 0 := Set.Finite.mem_toFinset _
  have hne (a : ℂ) (ha : a ∈ S) : 0-a ≠ 0 := by
    intro he
    have : a = 0 := by simpa using (sub_eq_zero.mp he).symm
    exact (hS a).mp ha (this ▸ hD0)
  obtain ⟨g, hg, hg0, hfg⟩ := hf.meromorphicOn.extract_zeros_poles htop (D.finiteSupport (isCompact_closedBall 0 R))
  let P (z : ℂ) := ∏ a ∈ S, (z-a)^(D a)
  have hprod : (∏ᶠ (a : ℂ), (·-a)^(D a)) = fun z ↦ P z := by
    rw [finprod_eq_prod_of_mulSupport_subset _ (s := S)]
    · ext z
      simp [P]
    · intro a ha
      apply (hS a).mpr
      intro h
      exact ha (by simp [h])
  have hfact : f =ᶠ[codiscreteWithin B] P*g := by
    change f =ᶠ[codiscreteWithin B] (∏ᶠ (u : ℂ), (·-u)^D u) • g at hfg
    rwa [hprod, smul_eq_mul] at hfg
  have hG : AnalyticOnNhd ℂ (logDeriv g) B := fun z hz ↦ (hg z hz).deriv.div (hg z hz) (hg0 ⟨z,hz⟩)
  refine ⟨logDeriv g,hG,?_⟩
  have hP : AnalyticAt ℂ P 0 := by
    dsimp [P]
    exact S.analyticAt_fun_prod (f := fun a z ↦ (z-a)^D a)
      (fun a ha ↦ (analyticAt_id.sub analyticAt_const).zpow (hne a ha))
  have hP0 : P 0 ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun a ha ↦ zpow_ne_zero _ (hne a ha))
  have hBmem : B ∈ 𝓝 (0 : ℂ) := closedBall_mem_nhds _ hR
  have heq : f =ᶠ[𝓝 0] P*g := by
    apply ((hf 0 hB).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE (hP.mul (hg 0 hB)).continuousAt).mp
    filter_upwards [eventuallyEq_codiscreteWithin_iff_forall_eventually_nhdsNE.mp hfact 0 hB,
      nhdsWithin_le_nhds hBmem] with z hzf hz
    exact hzf hz
  have havo : ∀ᶠ z in 𝓝 (0 : ℂ), ∀ a ∈ S, z-a ≠ 0 :=
    (eventually_all_finset S).mpr fun a ha ↦ (continuousAt_id.sub continuousAt_const).eventually_ne (hne a ha)
  filter_upwards [logDeriv_congr_nhds heq, havo, hBmem, hP.eventually_analyticAt,
                  hP.continuousAt.eventually_ne hP0] with z hz hn hzb hPz hPzn
  rw [hz, logDeriv_mul z hPzn (hg0 ⟨z,hzb⟩) hPz.differentiableAt (hg z hzb).differentiableAt]
  congr 1
  change logDeriv (fun q ↦ ∏ a ∈ S, (q-a)^D a) z = _
  rw [logDeriv_fun_prod (f := fun i q ↦ (q-i)^D i) (s := S) (x := z) (fun i hi ↦ zpow_ne_zero _ (hn i hi))
    (fun a ha ↦ (differentiableAt_id.sub_const a).zpow (.inl (hn a ha)))]
  apply Finset.sum_congr rfl
  intro a ha
  rw [logDeriv_fun_zpow (f := fun q : ℂ ↦ q-a) (x := z) (differentiableAt_id.sub_const a) (D a)]
  simp [logDeriv, div_eq_mul_inv]

/-- Removing all finite poles in a compact disk leaves Taylor coefficients with its Cauchy rate.
The pole contribution at order n uses the reciprocal power n+1. -/
theorem logDeriv_coeff_principalParts {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (h0 : f 0 ≠ 0) :
    let D := MeromorphicOn.divisor f (closedBall 0 R)
    let S := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖coeff (logDeriv f) n + ∑ a ∈ S, (D a : ℂ)/a^(n+1)‖ ≤ C/R^n := by
  classical
  let B := closedBall (0 : ℂ) R
  let D := MeromorphicOn.divisor f B
  let S := (D.finiteSupport (isCompact_closedBall 0 R)).toFinset
  have hB : 0 ∈ B := mem_closedBall_self hR.le
  have hD0 : D 0 = 0 := by
    rw [show D 0 = (meromorphicOrderAt f 0).untop₀ from hf.meromorphicOn.divisor_apply hB,
      (hf 0 hB).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr h0]; rfl
  have hS (a : ℂ) : a ∈ S ↔ D a ≠ 0 := Set.Finite.mem_toFinset _
  have hterms (a : ℂ) (ha : a ∈ S) : AnalyticAt ℂ (fun z : ℂ ↦ (D a : ℂ)/(z-a)) 0 := by
    have hne : (0 : ℂ)-a ≠ 0 := by
      intro he
      have ha0 : a=0 := (sub_eq_zero.mp he).symm
      exact (hS a).mp ha (ha0 ▸ hD0)
    have h1 : AnalyticAt ℂ (fun _ : ℂ ↦ (D a : ℂ)) (0 : ℂ) := analyticAt_const
    have h2 : AnalyticAt ℂ (fun z : ℂ ↦ z-a) (0 : ℂ) := by fun_prop
    exact h1.div h2 hne
  obtain ⟨h, hh, he⟩ := germ_factor_sum hR hf h0
  obtain ⟨C, hC, H⟩ := cauchy_coeff hR hh
  refine ⟨C, hC, fun n ↦ ?_⟩
  change ‖coeff (logDeriv f) n + ∑ a ∈ S, (D a : ℂ)/a^(n+1)‖ ≤ C / R^n
  have hid : coeff (logDeriv f) n = (∑ a ∈ S, coeff (fun z : ℂ ↦ (D a : ℂ)/(z-a)) n) + coeff h n := by
    unfold coeff
    rw [he.iteratedDeriv_eq n]
    change iteratedDeriv n (fun z ↦ (∑ a ∈ S, (D a : ℂ)/(z-a))+h z) 0 / n.factorial = _
    rw [iteratedDeriv_fun_add ((S.analyticAt_fun_sum hterms).contDiffAt) ((hh _ hB).contDiffAt),
      iteratedDeriv_fun_sum (fun a ha ↦ (hterms a ha).contDiffAt), add_div, Finset.sum_div]
  rw [hid]
  simp_rw [coeff_pole, neg_div, Finset.sum_neg_distrib]
  convert H n using 2
  abel


end RiemannMasullo.DiskLogCoefficient
