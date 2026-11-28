module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import RiemannMasullo.ForMathlib.Analysis.Complex.HalfPlaneJensen
import RiemannMasullo.Ch06_LocalGlobal.Sec3
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Compact Green formula for the ordinary finite Hecke L-function

On the half-plane to the right of the critical line, removing the gamma factors preserves
all orders. The only negative order for a character trivial on the norm section is the
principal simple pole at 1, whose inverse Cayley coordinate is −1/2. Jensen's finite-radius
identity and the completed-divisor quadratic estimate yield the full Green sum.
-/

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain Metric NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo.HeckeHalfPlaneJensen

open HalfPlaneJensen

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

/-- Signed order of the canonical completed Hecke continuation. -/
abbrev order (χ : U𝔽) (z : ℂ) : ℤ := MeromorphicOn.divisor (explicitFormulaCompletedHeckeL χ) univ z

/-- Positive completed-divisor sites whose real part is strictly greater than one half. -/
abbrev RightSite (χ : U𝔽) := {z : ℂ // 0 < order χ z ∧ 1/2 < z.re}

open scoped Classical in
/-- Compensation for the unique possible pole inside the Cayley disk. -/
def poleTerm (χ : U𝔽) (r : ℝ) : ℝ := if χ = 1 then max 0 (Real.log (2*r)) else 0

/-- The circle mean with its central Euler value subtracted and its principal pole restored. -/
def correctedMean (χ : U𝔽) (L : ℂ → ℂ) (r : ℝ) : ℝ :=
  circleMean L r - Real.log ‖L 2‖ + poleTerm χ r

private theorem principalWeight (r : ℝ) : weight r 1 = max 0 (Real.log (2*r)) := by
  rw [weight, disk_one, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
  congr 2
  ring

/-- The reciprocal gamma product is a holomorphic unit on the right half-plane. -/
theorem finite_order_eq_completed (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) (s : ℂ) (hs : 0 < s.re) :
    meromorphicOrderAt L s = meromorphicOrderAt (explicitFormulaCompletedHeckeL χ) s := by
  let Λ := explicitFormulaCompletedHeckeL χ
  let G (z : ℂ) := (heckeGammaFactor χ z)⁻¹
  let H (z : ℂ) := G z * Λ z
  obtain ⟨hΛ, hΛe⟩ := explicitFormulaCompletedHeckeL_spec χ
  have hga := differentiable_inv_heckeGammaFactor χ
  have hH : MeromorphicOn H univ := fun z hz ↦
    (hga.analyticAt z).meromorphicAt.mul (hΛ hz).meromorphicAt
  have hEq := heckeEulerProductOutside_eq_finite_nf_eq L H hL.meromorphicOn hH (fun z hz ↦ by
    rw [he ⟨z, hz⟩]
    dsimp only [H, G, Λ]
    rw [hΛe ⟨z, hz⟩, completedHeckeL, finiteHeckeL,
      inv_mul_cancel_left₀ (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hz))])
  have h := congrArg (fun f ↦ meromorphicOrderAt f s) hEq
  rw [meromorphicOrderAt_toMeromorphicNFOn hL.meromorphicOn (mem_univ _),
    meromorphicOrderAt_toMeromorphicNFOn hH (mem_univ _)] at h
  exact h.trans (meromorphicOrderAt_mul_of_ne_zero (hga.analyticAt s)
    (inv_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ hs)))

private theorem finite_two (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) : AnalyticAt ℂ L 2 ∧ L 2 ≠ 0 := by
  let z : Hp := ⟨2, by norm_num⟩
  have hn : L 2 ≠ 0 := (he z).trans_ne (finiteHeckeL_ne_zero_of_one_lt_re χ z)
  have hN := hL (mem_univ (2:ℂ))
  exact ⟨hN.meromorphicOrderAt_nonneg_iff_analyticAt.mp
    (hN.meromorphicOrderAt_eq_zero_iff.mpr hn).ge, hn⟩

/-- At every inside radius, the pole-corrected ordinary finite L mean counts the actual
positive sites strictly right of the critical line, with their full completed multiplicities. -/
theorem hasSum_correctedMean (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    HasSum (fun z : RightSite χ ↦ (order χ z.val : ℝ) * weight r z.val)
      (correctedMean χ L r) := by
  classical
  obtain ⟨ha, h₂⟩ := finite_two χ L hL he
  have h := right_circle_hasSum L hL.meromorphicOn ha h₂ hr hr1
  have ho (s : Right) : (meromorphicOrderAt L s.val).untop₀ = order χ s.val := by
    rw [order, finite_order_eq_completed χ L hL he s.val (by linarith [s.property]),
      MeromorphicOn.divisor_apply (explicitFormulaCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ _)]
  let oneR : Right := ⟨1, by norm_num⟩
  let c := if χ = 1 then weight r 1 else 0
  let p (s : Right) := if s=oneR then c else 0
  have hp : HasSum p c := hasSum_ite_eq oneR _
  have hc : c = poleTerm χ r := by simp [c, poleTerm, principalWeight]
  let mass (s : Right) := if 0 < order χ s.val then (order χ s.val : ℝ) * weight r s.val else 0
  have hpos : HasSum mass (correctedMean χ L r) := by
    rw [correctedMean, ← hc]
    apply (h.add hp).congr_fun
    intro s
    change mass s = ((meromorphicOrderAt L s.val).untop₀:ℝ) * weight r s.val + p s
    rw [ho]
    by_cases hpole : χ=1 ∧ s=oneR
    · obtain ⟨rfl,rfl⟩ := hpole
      have hord := (idelicExplicitFormula_trivial_poles (F := F)).2
      simp [mass, p, c, oneR, order, hord]
    · have hpp : p s = 0 := by
        by_cases hs : s = oneR
        · have hn : χ ≠ 1 := fun hc ↦ hpole ⟨hc,hs⟩
          simp [p,c,hn]
        · simp [p,hs]
      have hnon : 0 ≤ order χ s.val := by
        by_contra hh
        obtain ⟨htr, hzero | hone⟩ := idelicExplicitFormula_chart_poles τ hτ χ hχ s.val (lt_of_not_ge hh)
        · have hs := s.property
          rw [hzero] at hs
          norm_num at hs
        · exact hpole ⟨htr, Subtype.ext hone⟩
      rcases hnon.eq_or_lt with hz | hstrict
      · simp [mass,hpp,← hz]
      · simp [mass,hstrict,hpp]
  let inc (z : RightSite χ) : Right := ⟨z.val,z.property.2⟩
  have hinj : Injective inc := fun a b hh ↦ Subtype.ext (congrArg (fun x : Right ↦ x.val) hh)
  have hrest := (hinj.hasSum_iff (f := mass) (by
    intro s hs
    by_cases hsite : 0 < order χ s.val
    · exact (hs ⟨⟨s.val, hsite, s.property⟩, Subtype.ext rfl⟩).elim
    · simp [mass,hsite])).mpr hpos
  apply hrest.congr_fun
  intro z
  simp [mass, inc, z.property.1]

/-- The actual right-site Green weights form an absolutely convergent real series. -/
theorem summable_green (χ : U𝔽) :
    Summable (fun z : RightSite χ ↦ (order χ z.val : ℝ) * weight 1 z.val) := by
  let inc (z : RightSite χ) : {s : ℂ // 0 < order χ s} := ⟨z.val,z.property.1⟩
  have hinj : Injective inc := fun a b hh ↦ Subtype.ext (congrArg (fun x : {s : ℂ // 0 < order χ s} ↦ x.val) hh)
  have hsum := (explicitFormulaCompletedHeckeL_summable_divisor_div_sq χ).comp_injective hinj
  apply (hsum.mul_left 3).of_norm_bounded
  intro z
  have hm : 0 ≤ (order χ z.val : ℝ) := by exact_mod_cast z.property.1.le
  have hw := weight_one_le z.property.2 (explicitFormulaCompletedHeckeL_zero_re_mem χ z.property.1).2
  rw [Real.norm_of_nonneg (mul_nonneg hm (weight_nonneg _ _))]
  calc
    _ ≤ (order χ z.val : ℝ) * (3/(1+|z.val.im|)^2) := mul_le_mul_of_nonneg_left hw hm
    _ = _ := by dsimp [inc]; ring

/-- Monotonicity holds for the exact corrected means on the open interval of disk radii. -/
theorem monotone_correctedMean (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    MonotoneOn (correctedMean χ L) (Ioo 0 1) := by
  intro r hr R hR hrR
  have ha := hasSum_correctedMean τ hτ χ hχ L hL he hr.1 hr.2
  have hb := hasSum_correctedMean τ hτ χ hχ L hL he hR.1 hR.2
  rw [← ha.tsum_eq, ← hb.tsum_eq]
  exact ha.summable.tsum_le_tsum (fun z ↦ mul_le_mul_of_nonneg_left (weight_mono hr.1 hrR z.val)
    (by exact_mod_cast z.property.1.le)) hb.summable

/-- The increasing compact circle means tend to the full ordinary right-half-plane Green sum. -/
theorem tendsto_correctedMean (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    Tendsto (correctedMean χ L) (𝓝[<] (1:ℝ))
      (𝓝 (∑' z : RightSite χ, (order χ z.val : ℝ) * weight 1 z.val)) := by
  have hr : ∀ᶠ r : ℝ in 𝓝[<] 1, r ∈ Ioo (0:ℝ) 1 :=
    (eventually_nhdsWithin_of_eventually_nhds (lt_mem_nhds (by norm_num : (0:ℝ)<1))).and self_mem_nhdsWithin
  have hl :=
    tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[<] (1:ℝ))
      (f := fun r (z : RightSite χ) ↦ (order χ z.val : ℝ)*weight r z.val)
      (summable_green χ) (fun z ↦
        tendsto_const_nhds.mul ((weight_continuousAt_one (s := z.val) (by
          intro heq
          have hp := (explicitFormulaCompletedHeckeL_zero_re_mem χ z.property.1).2
          rw [heq] at hp
          norm_num at hp) (disk_den z.property.2)).continuousWithinAt.tendsto)) (by
            filter_upwards [hr] with r h z
            have hm : 0 ≤ (order χ z.val : ℝ) := by exact_mod_cast z.property.1.le
            rw [Real.norm_of_nonneg (mul_nonneg hm (weight_nonneg _ _))]
            exact mul_le_mul_of_nonneg_left (weight_mono h.1 h.2.le _) hm)
  apply hl.congr'
  filter_upwards [hr] with r h
  exact (hasSum_correctedMean τ hτ χ hχ L hL he h.1 h.2).tsum_eq

/-- Each strict inside radius sees only finitely many nonzero divisor contributions. -/
theorem finiteSupport_circle (χ : U𝔽) {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    (support (fun z : RightSite χ ↦ (order χ z.val : ℝ) * weight r z.val)).Finite := by
  let K := toHalf '' closedBall 0 r
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) r).image_of_continuousOn (by
    intro u hu
    have hn : ‖u‖ < 1 := (show ‖u‖ ≤ r by simpa [Metric.mem_closedBall] using hu).trans_lt hr1
    exact (chart_analytic hn).continuousAt.continuousWithinAt)
  let Λ := explicitFormulaCompletedHeckeL χ
  let D := MeromorphicOn.divisor Λ K
  have hpre : ((fun z : RightSite χ ↦ z.val) ⁻¹' D.support).Finite :=
    (D.finiteSupport hK).preimage Subtype.val_injective.injOn
  refine hpre.subset ?_
  intro z hz
  have hm := right_ne_zero_of_mul hz
  have hball : ‖toDisk z.val‖ ≤ r := by
    by_contra hn
    have hlt := lt_of_not_ge hn
    have hpos := hr.trans hlt
    exact hm (max_eq_left (Real.log_nonpos (div_nonneg hr.le hpos.le) ((div_le_one hpos).mpr hlt.le)))
  have hzK : z.val ∈ K := ⟨toDisk z.val, by simpa [Metric.mem_closedBall] using hball,
    toHalf_toDisk (disk_den z.property.2)⟩
  have hΛ := (explicitFormulaCompletedHeckeL_spec χ).1.meromorphicOn
  have hΛK : MeromorphicOn Λ K := fun x _ ↦ hΛ x (mem_univ _)
  change MeromorphicOn.divisor Λ K z.val ≠ 0
  rw [MeromorphicOn.divisor_apply hΛK hzK, ← MeromorphicOn.divisor_apply hΛ (mem_univ z.val)]
  exact z.property.1.ne'

private theorem actual_green_eq (χ : U𝔽) (z : RightSite χ) : weight 1 z.val = greenKernel z.val := by
  apply weight_one_eq_green z.property.2
  rintro he
  have hz := (explicitFormulaCompletedHeckeL_zero_re_mem χ z.property.1).2
  rw [he] at hz
  norm_num at hz

theorem summable_greenKernel (χ : U𝔽) :
    Summable (fun z : RightSite χ ↦ (order χ z.val : ℝ) * greenKernel z.val) :=
  (summable_green χ).congr (fun z ↦ by rw [actual_green_eq χ z])

open scoped Classical in
theorem tendsto_poleTerm (χ : U𝔽) :
    Tendsto (poleTerm χ) (𝓝[<] (1:ℝ)) (𝓝 (if χ = 1 then Real.log 2 else 0)) := by
  change Tendsto (fun r : ℝ ↦ if χ = 1 then max 0 (Real.log (2*r)) else 0) _ _
  by_cases h : χ=1
  · have hc : ContinuousAt (fun r : ℝ ↦ max 0 (Real.log (2*r))) 1 := by
      have hm : ContinuousAt (fun r : ℝ ↦ 2*r) 1 := by fun_prop
      exact continuousAt_const.max (hm.log (by norm_num : (2:ℝ)*1 ≠ 0))
    simpa [poleTerm, h, max_eq_right (Real.log_nonneg (by norm_num : 1 ≤ (2:ℝ)))] using
      hc.continuousWithinAt (s := Iio 1) |>.tendsto
  · simp [h]

/-- The same corrected family that is monotone has the Green sum as its finite limit. -/
theorem tendsto_correctedMean_greenKernel (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    Tendsto (correctedMean χ L) (𝓝[<] (1 : ℝ))
      (𝓝 (∑' z : RightSite χ, (order χ z.val : ℝ) * greenKernel z.val)) := by
  simpa only [actual_green_eq χ] using tendsto_correctedMean τ hτ χ hχ L hL he

open scoped Classical in
/-- Compact Cayley-circle version of the critical-line log-modulus formula, with the
limiting correction log 2 for precisely the principal normalized character. -/
theorem tendsto_circleMean_logTwo (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) :
    Tendsto (fun r ↦ circleMean L r - Real.log ‖L 2‖ + (if χ = 1 then Real.log 2 else 0))
      (𝓝[<] (1:ℝ)) (𝓝 (∑' z : RightSite χ, (order χ z.val : ℝ) * greenKernel z.val)) := by
  let c : ℝ := if χ = 1 then Real.log 2 else 0
  have G := tendsto_correctedMean τ hτ χ hχ L hL he
  simp_rw [actual_green_eq χ] at G
  have hc := tendsto_poleTerm χ
  have hc' : Tendsto (fun _ : ℝ ↦ c) (𝓝[<] (1:ℝ)) (𝓝 c) := tendsto_const_nhds
  have h := (G.sub hc).add hc'
  change Tendsto (fun r ↦ correctedMean χ L r - poleTerm χ r + c) _
    (𝓝 ((∑' z : RightSite χ, (order χ z.val : ℝ) * greenKernel z.val) - c + c)) at h
  rw [sub_add_cancel] at h
  exact h.congr (fun r ↦ by simp [correctedMean, c])

open scoped Classical in
/-- Any identified boundary value of the raw circle means satisfies the same Green identity. -/
theorem green_identity_of_tendsto_circleMean (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {b : ℝ}
    (hb : Tendsto (circleMean L) (𝓝[<] (1 : ℝ)) (𝓝 b)) :
    b - Real.log ‖L 2‖ + (if χ = 1 then Real.log 2 else 0) =
      ∑' z : RightSite χ, (order χ z.val : ℝ) * greenKernel z.val :=
  tendsto_nhds_unique ((hb.sub_const (Real.log ‖L 2‖)).add_const _) <|
    tendsto_circleMean_logTwo τ hτ χ hχ L hL he

open scoped Classical in
/-- A fixed genuine character and its canonical finite Euler continuation satisfy the finite
circle formulas, the monotonicity and the full limiting Green formula simultaneously. -/
theorem canonical_compact_green (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    (∀ r : ℝ, 0 < r → r < 1 →
      CircleIntegrable (fun u ↦ Real.log ‖L (toHalf u)‖) 0 r ∧
      (support (fun z : RightSite χ ↦ (order χ z.val : ℝ) * weight r z.val)).Finite ∧
      HasSum (fun z : RightSite χ ↦ (order χ z.val : ℝ) * weight r z.val) (correctedMean χ L r)) ∧
    MonotoneOn (correctedMean χ L) (Ioo 0 1) ∧
    Tendsto (correctedMean χ L) (𝓝[<] (1 : ℝ))
      (𝓝 (∑' z : RightSite χ, (order χ z.val : ℝ) * greenKernel z.val)) ∧
    Summable (fun z : RightSite χ ↦ (order χ z.val : ℝ) * greenKernel z.val) ∧
    Tendsto (fun r ↦ circleMean L r - Real.log ‖L 2‖ + (if χ = 1 then Real.log 2 else 0))
      (𝓝[<] (1:ℝ)) (𝓝 (∑' z : RightSite χ, (order χ z.val : ℝ) * greenKernel z.val)) := by
  intro L
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  exact ⟨fun _ hr hr1 ↦ ⟨circle_integrable L hL.meromorphicOn hr hr1, finiteSupport_circle χ hr hr1,
      hasSum_correctedMean τ hτ χ hχ L hL he hr hr1⟩, monotone_correctedMean τ hτ χ hχ L hL he,
    tendsto_correctedMean_greenKernel τ hτ χ hχ L hL he,
    summable_greenKernel χ, tendsto_circleMean_logTwo τ hτ χ hχ L hL he⟩

end RiemannMasullo.HeckeHalfPlaneJensen
