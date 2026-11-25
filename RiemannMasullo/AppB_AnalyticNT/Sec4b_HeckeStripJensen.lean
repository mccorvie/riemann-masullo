module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b_NormalizedHeckeDisk
public import RiemannMasullo.ForMathlib.Analysis.Complex.StripJensen
import RiemannMasullo.AppB_AnalyticNT.Sec1
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The ordinary Hecke logarithm on both sides of a strip

The left edge is the critical line. The right edge and the evaluation point lie in the
Euler product half-plane. A vertical there can be chosen independently of the evaluation
point to control both infinite ends. Only the principal simple pole contributes a correction.

The midpoint specialization for the Riemann zeta-function is due to S. K. Sekatskii,
S. Beltraminelli and D. Merlini, Ukrainian Math. J. 64 (2012), p. 227, (10)–(11).
-/

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped Classical NNReal Topology

namespace RiemannMasullo.HeckeStripJensen

open HeckeDiskNormalization HeckeHalfPlaneJensen StripJensen

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "U𝔽" => PontryaginDual C𝔽
local notation "Hp" => (Complex.re ⁻¹' Ioi (1 : ℝ))

private def damp (K : ℝ) (N : ℕ) (z : ℂ) : ℂ := ((K : ℂ) * (z + 1)^N)⁻¹

private theorem shift_one {z : ℂ} (hz : 0 ≤ z.re) : 1 ≤ ‖z+1‖ := by
  have h := Complex.re_le_norm (z+1)
  simp only [Complex.add_re,Complex.one_re] at h
  linarith

private theorem damp_unit {K : ℝ} (hK : 0 < K) (N : ℕ) {z : ℂ} (hz : 0 ≤ z.re) :
    AnalyticAt ℂ (damp K N) z ∧ damp K N z ≠ 0 := by
  have hz' : z+1 ≠ 0 := norm_pos_iff.mp (zero_lt_one.trans_le (shift_one hz))
  have hn : (K : ℂ) * (z + 1)^N ≠ 0 := mul_ne_zero (by exact_mod_cast hK.ne') (pow_ne_zero _ hz')
  exact ⟨(show AnalyticAt ℂ (fun u : ℂ ↦ (K : ℂ) * (u+1)^N) z by fun_prop).inv hn, inv_ne_zero hn⟩

private theorem norm_damp {K : ℝ} (hK : 0 ≤ K) (N : ℕ) (z : ℂ) :
    ‖damp K N z‖ = (K*‖z+1‖^N)⁻¹ := by simp [damp,abs_of_nonneg hK]

private theorem halfFactor_analytic {χ : U𝔽} {z : ℂ} (hz : 0 < z.re) :
    AnalyticAt ℂ (halfFactor χ) z := by
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  change AnalyticAt ℂ (fun u : ℂ ↦ if χ = 1 then (u-1)/u else 1) z
  by_cases h : χ = 1
  · simp only [h,ite_true]
    exact (show AnalyticAt ℂ (fun u : ℂ ↦ u-1) z by fun_prop).div analyticAt_id hz0
  · simp only [h,ite_false]
    exact analyticAt_const

private theorem halfFactor_ne {χ : U𝔽} {z : ℂ} (hz : 0 < z.re) (hp : ¬(χ = 1 ∧ z = 1)) :
    halfFactor χ z ≠ 0 := by
  have hz0 : z ≠ 0 := fun h ↦ by simp [h] at hz
  by_cases h : χ = 1
  · exact (ite_eq_left h : halfFactor χ z = (z-1)/z).trans_ne
      (div_ne_zero (sub_ne_zero.mpr fun e ↦ hp ⟨h,e⟩) hz0)
  · simp [halfFactor,h]

private theorem halfFactor_lower (χ : U𝔽) {σ : ℝ} (hσ : 1 < σ) {z : ℂ} (hz : z.re = σ) :
    (σ-1)/σ ≤ ‖halfFactor χ z‖ := by
  have hσ0 := zero_lt_one.trans hσ
  by_cases h : χ = 1
  · have hn : 0 < ‖z‖ := hσ0.trans_le (hz ▸ Complex.re_le_norm z)
    have h₁ : σ-1 ≤ ‖z-1‖ := by simpa [hz] using Complex.re_le_norm (z-1)
    have h₂ : ‖z‖ ≤ ‖z-1‖+1 := by simpa using norm_add_le (z-1) (1:ℂ)
    rw [halfFactor,ite_eq_left h,norm_div,div_le_div_iff₀ hσ0 hn]
    nlinarith [mul_le_mul_of_nonneg_left h₂ (sub_nonneg.mpr hσ.le)]
  · simp only [halfFactor,h,ite_false,norm_one,div_le_one hσ0]
    linarith

/-- A uniform positive lower bound, simultaneously for the pole factor and for the
pole-cleared ordinary finite continuation, on any fixed Euler vertical. -/
theorem exists_pos_le_norm_on_euler_vertical (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {σ : ℝ} (hσ : 1 < σ) :
    ∃ m > 0, ∀ z : ℂ, z.re = σ → m ≤ ‖halfFactor χ z‖ ∧ m ≤ ‖cleared χ L z‖ := by
  let Z := max 1 ‖dedekindZeta F (σ : ℂ)‖
  have hZ : 1 ≤ Z := le_max_left _ _
  have hZ0 := zero_lt_one.trans_le hZ
  let g := (σ-1)/σ
  have hg : 0 < g := div_pos (sub_pos.mpr hσ) (zero_lt_one.trans hσ)
  refine ⟨g/Z,div_pos hg hZ0,fun z hz ↦ ?_⟩
  have hz' : 1 < z.re := hz ▸ hσ
  have hE := one_le_norm_finiteHeckeL_mul_dedekindZeta χ ⟨z,hz'⟩
  have hE' : 1 ≤ ‖L z‖*Z := by
    rw [show L z = finiteHeckeL χ ⟨z,hz'⟩ from he ⟨z,hz'⟩]
    exact hE.trans (mul_le_mul_of_nonneg_left (by simp [hz,Z])
      (norm_nonneg _))
  have hF := halfFactor_lower χ hσ hz
  have hp : z ≠ 1 := fun h ↦ by simp [h] at hz'
  refine ⟨(div_le_self hg.le hZ).trans hF,?_⟩
  rw [cleared_agrees τ hτ χ hχ L hL he (zero_lt_one.trans hz') (fun h ↦ hp h.2),norm_mul,div_eq_mul_inv]
  exact mul_le_mul hF (by simpa only [one_div] using ((div_le_iff₀ hZ0).mpr hE' : 1/Z ≤ ‖L z‖)) (inv_nonneg.mpr hZ0.le) (norm_nonneg _)

private theorem probe_damp {σ K m : ℝ} (hσ : 1 < σ) (hK : 0 < K) (hm : 0 < m) (N : ℕ) :
    ∃ A : ℝ, ∀ (n : ℕ) (t : ℝ), |t| ≤ n →
      Real.exp (-(A*((n:ℝ)+1))) ≤ ‖damp K N ((σ:ℂ)+(t:ℂ)*I)‖ * m := by
  let A := |Real.log (m/K)| + (N:ℝ)*(σ+2)
  refine ⟨A,fun n t ht ↦ ?_⟩
  let z := (σ:ℂ)+(t:ℂ)*I
  let r := ‖z+1‖
  have hu : 1 ≤ r := shift_one (z:=z) (by simp [z]; linarith)
  have hr := zero_lt_one.trans_le hu
  have ht' : r ≤ σ+1+|t| := by
    have eq : z+1 = ((σ+1:ℝ):ℂ)+(t:ℂ)*I := by simp [z]; ring
    rw [show r=‖((σ+1:ℝ):ℂ)+(t:ℂ)*I‖ by dsimp only [r]; rw [eq]]
    have h := norm_add_le (((σ+1:ℝ):ℂ)) ((t:ℂ)*I)
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (show 0<σ+1 by linarith),norm_mul,Complex.norm_I,mul_one] using h
  have hr' : Real.log r ≤ (σ+2)*((n:ℝ)+1) := by
    have h := Real.log_le_sub_one_of_pos hr
    nlinarith [mul_nonneg (show 0≤σ+1 by linarith) (Nat.cast_nonneg (α:=ℝ) n)]
  have hl : -(A*((n:ℝ)+1)) ≤ Real.log (m/K) - N*Real.log r := by
    have h := neg_abs_le (Real.log (m/K))
    have h' := mul_nonneg (abs_nonneg (Real.log (m/K))) (Nat.cast_nonneg (α:=ℝ) n)
    have h'' := mul_le_mul_of_nonneg_left hr' (Nat.cast_nonneg (α:=ℝ) N)
    dsimp only [A]
    linarith only [h,h',h'']
  have hEq : (K*r^N)⁻¹*m = (m/K)/r^N := by ring
  rw [norm_damp hK.le,show ‖(σ:ℂ)+(t:ℂ)*I+1‖=r from rfl,hEq,← Real.exp_log (div_pos (div_pos hm hK) (pow_pos hr N)),
    Real.exp_le_exp,Real.log_div (div_ne_zero hm.ne' hK.ne') (pow_ne_zero _ hr.ne'), Real.log_pow]
  exact hl

/-- The left edge uses the minus sign in the Poisson denominator. -/
def leftTrace (L : ℂ → ℂ) (w b t : ℝ) : ℝ :=
  Real.sin (Real.pi*b/w)/(2*w*(Real.cosh (Real.pi*t/w)-Real.cos (Real.pi*b/w))) *
    Real.log ‖L ((1/2:ℝ)+(t:ℂ)*I)‖

/-- The right edge uses the plus sign in the Poisson denominator. -/
def rightTrace (L : ℂ → ℂ) (w b t : ℝ) : ℝ :=
  Real.sin (Real.pi*b/w)/(2*w*(Real.cosh (Real.pi*t/w)+Real.cos (Real.pi*b/w))) *
    Real.log ‖L ((1/2+w:ℝ)+(t:ℂ)*I)‖

private def StripLaw (G : ℂ → ℂ) (w b : ℝ) : Prop :=
  Integrable (leftTrace G w b) ∧ Integrable (rightTrace G w b) ∧
  HasSum (fun z : Strip (1/2) (Real.pi/w) ↦ ((meromorphicOrderAt G z.val).untop₀ : ℝ) *
    physicalGreen (1/2) w b z.val) (boundaryMean G (1/2) w b-Real.log ‖G ((1/2+b:ℝ):ℂ)‖)

private theorem exists_damp_laws (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {w b e : ℝ} (hb : 1/2 < b) (hbw : b < w)
    (he₀ : 1/2 < e) (hew : e < w) :
    ∃ D : ℂ → ℂ, (∀ z : ℂ, 1/2 ≤ z.re → AnalyticAt ℂ D z ∧ D z ≠ 0) ∧
      StripLaw (D * cleared χ L) w b ∧ StripLaw (D * halfFactor χ) w b := by
  obtain ⟨N,K,_,hK,hbound⟩ := cleared_polynomial_bound τ hτ χ hχ L hL he
  have hK₀ := zero_lt_one.trans_le hK
  let D := damp K N
  have hD (z : ℂ) (hz : 1/2 ≤ z.re) := damp_unit hK₀ N (z:=z) (by linarith)
  obtain ⟨m,hm,hel⟩ := exists_pos_le_norm_on_euler_vertical τ hτ χ hχ L hL he (σ:=1/2+e) (by linarith)
  obtain ⟨v,hv,hat⟩ := exists_pos_le_norm_on_euler_vertical τ hτ χ hχ L hL he (σ:=1/2+b) (by linarith)
  obtain ⟨A,hA⟩ := probe_damp (σ:=1/2+e) (by linarith) hK₀ hm N
  have law (G : ℂ → ℂ) (ha : ∀ z : ℂ, 1/2 ≤ z.re → AnalyticAt ℂ G z)
      (hB : ∀ z : ℂ, 1/2 ≤ z.re → ‖G z‖ ≤ K*‖z+1‖^N)
      (hn : v ≤ ‖G ((1/2+b:ℝ):ℂ)‖) (hE : ∀ t : ℝ, m ≤ ‖G (site (1/2) e t)‖) :
      StripLaw (D*G) w b := by
    apply two_boundary_of_exponential_lower (A:=A) (x:=e) (by linarith) (by linarith) hbw
      (by linarith) hew (D*G)
    · exact fun z hz _ ↦ (hD z hz).1.mul (ha z hz)
    · intro z hz _
      have hr := (shift_one (z:=z) (by linarith))
      have hR : 0 < K*‖z+1‖^N := mul_pos hK₀ (pow_pos (zero_lt_one.trans_le hr) _)
      rw [Pi.mul_apply,norm_mul,show ‖D z‖=(K*‖z+1‖^N)⁻¹ from norm_damp hK₀.le _ _]
      exact (inv_mul_le_one₀ hR).mpr (hB z hz)
    · exact mul_ne_zero (hD _ (by simp; linarith)).2 (norm_pos_iff.mp (hv.trans_le hn))
    · apply Eventually.of_forall
      intro n
      have bound (t : ℝ) (ht : |t| ≤ n) : Real.exp (-(A*((n:ℝ)+1))) ≤ ‖(D*G) (site (1/2) e t)‖ :=
        (hA n t ht).trans (by rw [Pi.mul_apply,norm_mul]; exact mul_le_mul_of_nonneg_left (hE t) (norm_nonneg _))
      exact ⟨bound _ (by simp),bound _ (by simp)⟩
  refine ⟨D,hD,law _ (fun z hz ↦ cleared_analytic τ hτ χ hχ L hL he (by linarith)) hbound
    (hat _ rfl).2 (fun t ↦ (hel _ (by simp [site])).2),
    law _ (fun z hz ↦ halfFactor_analytic (by linarith)) (fun z hz ↦ ?_)
      (hat _ rfl).1 (fun t ↦ (hel _ (by simp [site])).1)⟩
  exact (norm_halfFactor_le χ hz).trans (one_le_mul_of_one_le_of_one_le hK
    (one_le_pow₀ (shift_one (z:=z) (by linarith))))

private theorem ae_regular_vertical {L : ℂ → ℂ} (hL : MeromorphicNFOn L univ) {v : ℂ}
    (hv : L v ≠ 0) (σ : ℝ) : ∀ᵐ t : ℝ, L ((σ:ℂ)+(t:ℂ)*I) ≠ 0 := by
  let d := MeromorphicOn.divisor L univ
  have hc : d.support.Countable := (HereditarilyLindelofSpace.isLindelof _).countable_of_isDiscrete d.discreteSupport
  let line (t : ℝ) := (σ:ℂ)+(t:ℂ)*I
  have hi : Injective line := fun t s e ↦ by simpa [line] using congrArg Complex.im e
  have h₀ := (hL (mem_univ v)).meromorphicOrderAt_eq_zero_iff.mpr hv
  filter_upwards [(hc.preimage hi).ae_notMem volume] with t ht
  have htop : meromorphicOrderAt L (line t) ≠ ⊤ :=
    hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ v) (mem_univ (line t)) (by simp [h₀])
  have hzero : d (line t) = 0 := not_ne_iff.mp ht
  rw [show d (line t) = (meromorphicOrderAt L (line t)).untop₀ from hL.meromorphicOn.divisor_apply (mem_univ _),
    WithTop.untop₀_eq_zero] at hzero
  exact (hL (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mp (hzero.resolve_right htop)

private theorem sub_orders (χ : U𝔽) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {z : ℂ} (hz : 0 < z.re)
    {D : ℂ → ℂ} (hD : AnalyticAt ℂ D z) (hn : D z ≠ 0) :
    (meromorphicOrderAt (D*cleared χ L) z).untop₀ -
      (meromorphicOrderAt (D*halfFactor χ) z).untop₀ = order χ z := by
  rw [meromorphicOrderAt_mul_of_ne_zero hD hn,meromorphicOrderAt_mul_of_ne_zero hD hn]
  by_cases hp : χ=1 ∧ z=1
  · obtain ⟨rfl,rfl⟩ := hp
    have hf : halfFactor (1 : U𝔽) = (fun u : ℂ ↦ u-1)/id := by funext u; simp [halfFactor]
    have hi : meromorphicOrderAt (id : ℂ → ℂ) 1 = 0 :=
      (analyticAt_id (𝕜:=ℂ)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr one_ne_zero
    rw [cleared_order_one L hL he,hf,meromorphicOrderAt_div (f:=fun u : ℂ ↦ u-1) (g:=id) (by fun_prop) (by fun_prop),
      meromorphicOrderAt_id_sub_const,hi,show order (1 : U𝔽) 1 = -1 from (idelicExplicitFormula_trivial_poles (F:=F)).2]
    norm_num
  · have ha := halfFactor_analytic (χ:=χ) hz
    have hf := halfFactor_ne (χ:=χ) hz hp
    rw [cleared,meromorphicOrderAt_toMeromorphicNFOn (meromorphic_product χ L hL) (mem_univ _),
      meromorphicOrderAt_mul_of_ne_zero ha hf,ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf,
      finite_order_eq_completed χ L hL he z hz,order,MeromorphicOn.divisor_apply (explicitFormulaCompletedHeckeL_spec χ).1.meromorphicOn (mem_univ _)]
    simp

private theorem log_sub_at (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {z : ℂ} (hz : 0 < z.re) (hz₁ : z ≠ 1)
    {D : ℂ → ℂ} (hD : D z ≠ 0) (hn : L z ≠ 0) :
    Real.log ‖(D * cleared χ L) z‖-Real.log ‖(D * halfFactor χ) z‖ = Real.log ‖L z‖ := by
  have hp : ¬(χ=1 ∧ z=1) := fun h ↦ hz₁ h.2
  simp only [Pi.mul_apply,cleared_agrees τ hτ χ hχ L hL he hz hp,← mul_assoc,norm_mul]
  rw [Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr hD) (norm_ne_zero_iff.mpr (halfFactor_ne hz hp))) (norm_ne_zero_iff.mpr hn)]
  ring

private theorem signed_strip (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (he : ∀ s : Hp, L s = finiteHeckeL χ s) {w b : ℝ} (hb : 1/2 < b) (hbw : b < w) :
    Integrable (leftTrace L w b) ∧ Integrable (rightTrace L w b) ∧
      HasSum (fun z : Strip (1/2) (Real.pi/w) ↦ (order χ z.val : ℝ) * physicalGreen (1/2) w b z.val)
        (boundaryMean L (1/2) w b-Real.log ‖L ((1/2+b:ℝ):ℂ)‖) := by
  obtain ⟨D,hD,hP,hQ⟩ := exists_damp_laws τ hτ χ hχ L hL he hb hbw hb hbw
  let P := D * cleared χ L
  let Q := D * halfFactor χ
  let s : ℂ := ((1/2+b:ℝ):ℂ)
  have hs : 1 < s.re := by dsimp [s]; linarith
  have hL₀ : L s ≠ 0 := (he ⟨s,hs⟩).trans_ne (finiteHeckeL_ne_zero_of_one_lt_re χ ⟨s,hs⟩)
  have hminus {z : ℂ} (hz : 1/2 ≤ z.re) (hp : z ≠ 1) (hn : L z ≠ 0) :
      Real.log ‖P z‖ - Real.log ‖Q z‖ = Real.log ‖L z‖ :=
    log_sub_at τ hτ χ hχ L hL he (by linarith) hp (hD z hz).2 hn
  have heval := hminus (z:=s) (by linarith) (fun e ↦ by simp [e] at hs) hL₀
  have edge (σ : ℝ) (hσ : 1/2 ≤ σ) (hσ₁ : σ ≠ 1) :
      ∀ᵐ t : ℝ, Real.log ‖P ((σ:ℂ)+(t:ℂ)*I)‖-Real.log ‖Q ((σ:ℂ)+(t:ℂ)*I)‖ =
        Real.log ‖L ((σ:ℂ)+(t:ℂ)*I)‖ := by
    filter_upwards [ae_regular_vertical hL hL₀ σ] with t ht
    exact hminus (by simpa using hσ) (fun e ↦ hσ₁ (by simpa using congrArg Complex.re e)) ht
  have hₗ : (leftTrace P w b - leftTrace Q w b) =ᵐ[volume] leftTrace L w b := by
    filter_upwards [edge (1/2) le_rfl (by norm_num)] with t ht
    dsimp only [Pi.sub_apply,leftTrace]
    rw [← mul_sub,ht]
  have hᵣ : (rightTrace P w b - rightTrace Q w b) =ᵐ[volume] rightTrace L w b := by
    filter_upwards [edge (1/2+w) (by linarith) (by linarith)] with t ht
    dsimp only [Pi.sub_apply,rightTrace]
    rw [← mul_sub,ht]
  refine ⟨(hP.1.sub hQ.1).congr hₗ,(hP.2.1.sub hQ.2.1).congr hᵣ,?_⟩
  have hmean : boundaryMean P (1/2) w b-boundaryMean Q (1/2) w b = boundaryMean L (1/2) w b := by
    have hl := integral_congr_ae hₗ
    have hr := integral_congr_ae hᵣ
    simp only [Pi.sub_apply] at hl hr
    change StripLaw P w b at hP
    change StripLaw Q w b at hQ
    rw [integral_sub hP.1 hQ.1] at hl
    rw [integral_sub hP.2.1 hQ.2.1] at hr
    change (∫ t, leftTrace P w b t)+(∫ t, rightTrace P w b t) -
      ((∫ t, leftTrace Q w b t)+(∫ t, rightTrace Q w b t)) =
      (∫ t, leftTrace L w b t)+(∫ t, rightTrace L w b t)
    linarith
  have hsum := hP.2.2.sub hQ.2.2
  have hv : (boundaryMean P (1/2) w b-Real.log ‖P s‖) -
        (boundaryMean Q (1/2) w b-Real.log ‖Q s‖) = boundaryMean L (1/2) w b-Real.log ‖L s‖ := by linarith
  rw [← hv]
  apply hsum.congr_fun
  intro z
  have hz := ((inStrip_iff (by linarith : 0<w) z.val).mp z.property).1
  have ho := sub_orders χ L hL he (z:=z.val) (by linarith) (hD z.val hz.le).1 (hD z.val hz.le).2
  simp only [← sub_mul]
  rw [← ho, Int.cast_sub]

/-- The correction for the principal pole restores its positive strip Green weight. -/
def logDifference (χ : U𝔽) (w b : ℝ) : ℝ :=
  let L := (finiteHeckeL_exists_continuation χ).choose
  boundaryMean L (1/2) w b-Real.log ‖L ((1/2+b:ℝ):ℂ)‖ +
    if χ=1 then physicalGreen (1/2) w b 1 else 0

/-- The two ordinary finite-Hecke boundary logarithms are absolutely integrable. -/
theorem integrable_traces (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) {w b : ℝ} (hb : 1/2 < b) (hbw : b < w) :
    let L := (finiteHeckeL_exists_continuation χ).choose
    Integrable (leftTrace L w b) ∧ Integrable (rightTrace L w b) := by
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have h := signed_strip τ hτ χ hχ _ hL he hb hbw
  exact ⟨h.1,h.2.1⟩

/-- The two ordinary finite-Hecke boundary integrals minus the interior Euler logarithm,
with the principal pole restored, equal the unordered sum of the genuine right-hand
completed-divisor orders times their strip Green weights. -/
theorem hasSum_green_logDifference (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) {w b : ℝ} (hb : 1/2 < b) (hbw : b < w) :
    HasSum (fun z : RightSite χ ↦ (order χ z.val : ℝ)*physicalGreen (1/2) w b z.val)
      (logDifference χ w b) := by
  let L := (finiteHeckeL_exists_continuation χ).choose
  obtain ⟨hL,he⟩ := (finiteHeckeL_exists_continuation χ).choose_spec
  have raw := (signed_strip τ hτ χ hχ L hL he hb hbw).2.2
  let S := Strip (1/2) (Real.pi/w)
  have hw : 0 < w := by linarith
  have hsite (z : S) := (inStrip_iff hw z.val).mp z.property
  let G := physicalGreen (1/2) w b
  let u : S := ⟨1,(inStrip_iff hw _).mpr (by norm_num; linarith)⟩
  let C := if χ=1 then G 1 else 0
  let p (z : S) := if z=u then C else 0
  have hp : HasSum p C := hasSum_ite_eq u _
  let mass (z : S) := if 0 < order χ z.val then (order χ z.val : ℝ)*G z.val else 0
  have hpos : HasSum mass (logDifference χ w b) := by
    apply (raw.add hp).congr_fun
    intro z
    change mass z = (order χ z.val : ℝ)*G z.val + p z
    by_cases h : χ=1 ∧ z=u
    · obtain ⟨rfl,rfl⟩ := h
      have ho := (idelicExplicitFormula_trivial_poles (F:=F)).2
      simp [mass,p,C,u,order,ho]
    · have hp₀ : p z = 0 := by
        by_cases hz : z=u
        · have hn : χ≠1 := fun he ↦ h ⟨he,hz⟩
          simp [p,C,hn]
        · simp [p,hz]
      have hn : 0 ≤ order χ z.val := by
        by_contra! hh
        obtain ⟨hc,h₀|h₁⟩ := idelicExplicitFormula_chart_poles τ hτ χ hχ z.val hh
        · have hz := (hsite z).1
          rw [h₀] at hz
          norm_num at hz
        · exact h ⟨hc,Subtype.ext h₁⟩
      rcases hn.eq_or_lt with hz | hz
      · simp [mass,hp₀,← hz]
      · simp [mass,hp₀,hz]
  let inc (z : RightSite χ) : S := ⟨z.val,(inStrip_iff hw _).mpr
    ⟨z.property.2,(explicitFormulaCompletedHeckeL_zero_re_mem χ z.property.1).2.trans_lt (by linarith)⟩⟩
  have hi : Injective inc := fun _ _ eq ↦ Subtype.ext (congrArg (fun z : S ↦ z.val) eq)
  have h := (hi.hasSum_iff (f:=mass) (by
    intro z hz
    by_cases h : 0 < order χ z.val
    · exact (hz ⟨⟨z.val,h,(hsite z).1⟩,Subtype.ext rfl⟩).elim
    · simp [mass,h])).mpr hpos
  exact h.congr_fun fun z ↦ by simp [mass,inc,G,z.property.1]

private theorem green_mass_pos {χ : U𝔽} (z : RightSite χ) {w b : ℝ} (hb : 1/2 < b) (hbw : b < w) :
    0 < (order χ z.val : ℝ)*physicalGreen (1/2) w b z.val := by
  have hw : 0 < w := by linarith
  have hr := (explicitFormulaCompletedHeckeL_zero_re_mem χ z.property.1).2
  have hs : InStrip (1/2) (Real.pi/w) (((1/2)+b:ℝ):ℂ) := (inStrip_iff hw _).mpr (by simp; constructor <;> linarith)
  have hz := (inStrip_iff (c:=1/2) hw z.val).mpr ⟨z.property.2,by linarith⟩
  have hn : z.val ≠ (((1/2)+b:ℝ):ℂ) := by
    intro he
    rw [he] at hr
    simp only [Complex.ofReal_re] at hr
    linarith
  exact mul_pos (by exact_mod_cast z.property.1) (physicalGreen_pos hw hs hz hn)

/-- A nonpositive strip difference excludes every positive site strictly right of the
critical line, including real sites. Conversely an empty right divisor gives difference zero. -/
theorem logDifference_nonpos_iff (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : RightInverse τ (ideleClassNorm F))
    (χ : U𝔽) (hχ : ∀ u : ℝ≥0ˣ, χ (τ u) = 1) {w b : ℝ} (hb : 1/2 < b) (hbw : b < w) :
    logDifference χ w b ≤ 0 ↔ IsEmpty (RightSite χ) := by
  have h := hasSum_green_logDifference τ hτ χ hχ hb hbw
  constructor
  · intro hn
    refine ⟨fun z ↦ ?_⟩
    have hle := h.summable.le_tsum z (fun j _ ↦ (green_mass_pos j hb hbw).le)
    rw [h.tsum_eq] at hle
    exact (green_mass_pos z hb hbw).not_ge (hle.trans hn)
  · intro h₀
    let := h₀
    rw [← h.tsum_eq]
    simp

end RiemannMasullo.HeckeStripJensen
