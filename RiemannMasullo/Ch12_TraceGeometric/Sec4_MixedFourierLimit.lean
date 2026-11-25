module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_MixedFourier
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Tactic

/-! # The locally integrable mixed product cutoff kernel

The one-prime shell transforms sum unconditionally away from the coordinate
axes. The finite symbols stabilize off their null zero fiber, which makes the
limit a Fourier distribution even when the full symbol is not integrable.
-/

@[expose] public noncomputable section

namespace RiemannMasullo.MixedCutoff
open MeasureTheory
open scoped Classical

private theorem shellReindex {E : Type*} [NormedAddCommGroup E]
    (k : ℤ) (f : ℤ → E) {g : ℕ → E} {s : E} (hg : HasSum g s)
    (ht : ∀ j : ℕ, f ((j : ℤ) - k) = g j)
    (hz : ∀ n, n + k < -1 → f n = 0) : HasSum f (f (-1-k) + s) := by
  let i : ℕ → ℤ := fun j => (j : ℤ) - k
  let t : ℤ → E := fun n => if 0 ≤ n+k then f n else 0
  have hi : Function.Injective i := by intro a b h; dsimp [i] at h; omega
  have hsum : HasSum t s := by
    apply (hi.hasSum_iff (f := t) ?_).mp
    · apply hg.congr_fun
      intro j
      simpa [Function.comp_def, t, i] using ht j
    · intro n hn
      have h : ¬ 0 ≤ n+k := by
        intro h
        apply hn
        exact ⟨(n+k).toNat, by dsimp [i]; omega⟩
      simp [t, h]
  apply ((hasSum_ite_eq (-1-k) (f (-1-k))).add hsum).congr_fun
  intro n
  by_cases he : n = -1-k
  · subst n; simp [t]
  · by_cases h : 0 ≤ n+k
    · simp [he, t, h]
    · simp [he, t, h, hz n (by omega)]

variable (p : ℕ) [Fact p.Prime]
local instance : MeasurableSpace ℚ_[p] := borel _
local instance : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The actual Fourier transform of one valuation shell at a mixed frequency. -/
abbrev mixedShellFourier (b : ℝ → ℂ) (u : ℝ) (v : ℚ_[p]) (n : ℤ) : ℂ :=
  tamagawaFourier (volume.prod (padicTamagawaMeasure p))
    (fun q : ℝ × ℚ_[p] ↦ realCutoffCharacter q.1 * padicStandardCharacter p q.2)
    (mixedShellSymbol p b n) (u,v)

local notation "shellB" => tamagawaFourier volume realCutoffCharacter

private theorem shellRadial (b : ℝ → ℂ) (he : ∀ x, shellB b (-x) = shellB b x)
    (u : ℝ) {v : ℚ_[p]} (hv : v ≠ 0) (j : ℤ) :
    shellB b ((p:ℝ)^(j-v.valuation)*u) = shellB b ((p:ℝ)^j*(|u| * ‖v‖)) := by
  have hp : (0:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [Padic.norm_eq_zpow_neg_valuation hv, sub_eq_add_neg, zpow_add₀ hp.ne']
  rcases le_total 0 u with h | h
  · rw [abs_of_nonneg h]; congr 1; ring
  · rw [abs_of_nonpos h, show (p:ℝ)^j * (-u * (p:ℝ)^(-v.valuation)) =
        -(((p:ℝ)^j*(p:ℝ)^(-v.valuation))*u) by ring, he]

private theorem shellReindexFourier {E : Type*} [NormedAddCommGroup E]
    (b : ℝ → ℂ) (he : ∀ x, shellB b (-x) = shellB b x) (u : ℝ) {v : ℚ_[p]} (hv : v ≠ 0)
    (F : ℂ → E) (hF : F 0 = 0) {s : E}
    (hs : HasSum (fun j : ℕ => F (shellB b ((p:ℝ)^j*(|u| * ‖v‖)) * (1-((p:ℝ)⁻¹ : ℂ)))) s) :
    HasSum (fun n => F (mixedShellFourier p b u v n))
      (F (shellB b ((p:ℝ)^(-1:ℤ)*(|u| * ‖v‖)) * (-((p:ℝ)⁻¹ : ℂ))) + s) := by
  have ht (j : ℤ) : mixedShellFourier p b u v (j-v.valuation) =
      shellB b ((p:ℝ)^j*(|u| * ‖v‖)) * (if j = -1 then -((p:ℝ)⁻¹ : ℂ)
        else if 0 ≤ j then 1-((p:ℝ)⁻¹ : ℂ) else 0) := by
    rw [mixedShellFourier, tamagawaFourier_mixedShellSymbol_offAxis p b _ u hv,
      sub_add_cancel, ← shellRadial p b he u hv j]
  have h := shellReindex v.valuation (fun n => F (mixedShellFourier p b u v n)) hs
    (fun j => by rw [ht]; simp [show (j:ℤ) ≠ -1 by omega])
    (fun n hn => by rw [mixedShellFourier, tamagawaFourier_mixedShellSymbol_offAxis p b n u hv];
                     simp [show n+v.valuation ≠ -1 by omega, show ¬0 ≤ n+v.valuation by omega, hF])
  have houter : mixedShellFourier p b u v (-1-v.valuation) =
      shellB b ((p:ℝ)^(-1:ℤ)*(|u| * ‖v‖)) * (-((p:ℝ)⁻¹ : ℂ)) := by
    simpa using ht (-1)
  simpa only [houter] using h

/-- Unconditional pointwise Fourier sum: the reciprocal shell and the lacunary tail. -/
theorem mixedShellFourier_hasSum (b : ℝ → ℂ) (he : ∀ x, shellB b (-x) = shellB b x)
    {C : ℝ} (hC : 0 ≤ C) (hd : Lacunary.Decays (shellB b) C)
    {u : ℝ} (hu : u ≠ 0) {v : ℚ_[p]} (hv : v ≠ 0) :
    HasSum (mixedShellFourier p b u v)
      (shellB b ((p:ℝ)^(-1:ℤ)*(|u| * ‖v‖)) * (-((p:ℝ)⁻¹ : ℂ)) +
        (∑' j : ℕ, shellB b ((p:ℝ)^j*(|u| * ‖v‖))) * (1-((p:ℝ)⁻¹ : ℂ))) := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  exact shellReindexFourier p b he u hv id rfl
    ((Lacunary.absolute hp hC hd (mul_pos (abs_pos.mpr hu) (norm_pos_iff.mpr hv))).of_norm.hasSum.mul_right _)

/-- Absolute convergence and a logarithmic bound for every finite subsum of norms. -/
theorem mixedShellFourier_absolute_partial (b : ℝ → ℂ) (he : ∀ x, shellB b (-x) = shellB b x)
    {C : ℝ} (hC : 0 ≤ C) (hd : Lacunary.Decays (shellB b) C)
    {u : ℝ} (hu : u ≠ 0) {v : ℚ_[p]} (hv : v ≠ 0) :
    Summable (fun n => ‖mixedShellFourier p b u v n‖) ∧
    ∀ s : Finset ℤ, ∑ n ∈ s, ‖mixedShellFourier p b u v n‖ ≤
      C * ‖(-((p:ℝ)⁻¹ : ℂ))‖ +
      ((1 + max 0 (-Real.log (|u| * ‖v‖)) / Real.log p)*C + C*(1-(p:ℝ)⁻¹)⁻¹) *
      ‖(1-((p:ℝ)⁻¹ : ℂ))‖ := by
  have hp : (1:ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hr := mul_pos (abs_pos.mpr hu) (norm_pos_iff.mpr hv)
  have ha := Lacunary.absolute hp hC hd hr
  have h := shellReindexFourier p b he u hv (fun z => ‖z‖) (norm_zero : ‖(0 : ℂ)‖ = 0) (by
    simpa only [norm_mul] using ha.hasSum.mul_right ‖(1-((p:ℝ)⁻¹ : ℂ))‖)
  refine ⟨h.summable, fun s => (h.summable.sum_le_tsum s (fun _ _ => norm_nonneg _)).trans ?_⟩
  rw [h.tsum_eq, norm_mul]
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hx : 0 < (p:ℝ)^(-1:ℤ)*(|u| * ‖v‖) := mul_pos (zpow_pos (zero_lt_one.trans hp) _) hr
    exact (hd _ hx).trans ((div_le_iff₀ (by positivity)).2
      (le_mul_of_one_le_right hC (by nlinarith [sq_nonneg ((p:ℝ)^(-1:ℤ)*(|u| * ‖v‖))])))
  · apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    simpa only [Real.log_inv] using Lacunary.logarithmic hp hC hd hr

end RiemannMasullo.MixedCutoff

namespace RiemannMasullo.MixedCutoff
open MeasureTheory Filter Set
open scoped Topology Classical
set_option quotPrecheck false
variable (p : ℕ) [Fact p.Prime]
local instance : MeasurableSpace ℚ_[p] := borel _
local instance : BorelSpace ℚ_[p] := ⟨rfl⟩

local notation "M" => (volume : Measure ℝ).prod (padicTamagawaMeasure p)
local notation "χ" => (fun q : ℝ × ℚ_[p] ↦ realCutoffCharacter q.1 * padicStandardCharacter p q.2)

private theorem finiteSymbolIntegrable {b : ℝ → ℂ} (hb : Integrable b) (J : Finset ℤ) :
    Integrable (mixedFiniteShellSymbol p b J) M :=
  integrable_finsetSum J fun n _ ↦ mixedShellSymbol_integrable p hb n

/-- Bilinear Fourier duality: both transforms use the same forward character. -/
theorem mixedFiniteShellSymbol_pairing {b : ℝ → ℂ} (hb : Integrable b) (J : Finset ℤ)
    {g : ℝ × ℚ_[p] → ℂ} (hg : Continuous g) (hc : HasCompactSupport g) :
    (∫ y, tamagawaFourier M χ (mixedFiniteShellSymbol p b J) y * g y ∂M) =
      ∫ x, mixedFiniteShellSymbol p b J x * tamagawaFourier M χ g x ∂M := by
  have : (padicTamagawaMeasure p).IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  let f := mixedFiniteShellSymbol p b J
  let K (x y : ℝ × ℚ_[p]) : ℂ := star (χ (x*y) : ℂ)
  obtain ⟨e, he⟩ := exists_padicPontryaginDualEquiv p
  have hpc : Continuous (padicStandardCharacter p) := by
    simpa only [he, one_mul, mul_one] using (show Continuous (fun x : ℚ_[p] ↦
      e (Multiplicative.ofAdd (1 : ℚ_[p])) (Multiplicative.ofAdd x)) from
        (e (Multiplicative.ofAdd (1 : ℚ_[p]))).continuous)
  have hχ : Continuous χ :=
    ((Circle.exp.continuous.comp (continuous_const.mul continuous_fst))).mul (hpc.comp continuous_snd)
  have hK : Continuous (fun z : (ℝ × ℚ_[p]) × (ℝ × ℚ_[p]) ↦ K z.1 z.2) :=
    (continuous_subtype_val.comp (hχ.comp (continuous_fst.mul continuous_snd))).star
  have h := (finiteSymbolIntegrable p hb J).mul_prod (hg.integrable_of_hasCompactSupport hc (μ := M))
  have hF : Integrable (Function.uncurry (fun x y ↦ (f x * g y) * K x y)) ((M).prod M) :=
    h.mul_bdd hK.aestronglyMeasurable (c := 1) (ae_of_all _ fun z ↦ by
      unfold K
      rw [norm_star, Circle.norm_coe])
  calc
    _ = ∫ y, ∫ x, (f x * g y) * K x y ∂M ∂M := by
      apply integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      rw [tamagawaFourier, ← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun x ↦ by dsimp [f, K]; ring)
    _ = ∫ x, ∫ y, (f x * g y) * K x y ∂M ∂M := (integral_integral_swap hF).symm
    _ = _ := by
      apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      rw [tamagawaFourier, ← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun y ↦ by dsimp only [K, f]; rw [mul_comm y x, mul_assoc])

private theorem mixedFiniteShellSymbol_eval {b : ℝ → ℂ} (J : Finset ℤ)
    (z : ℝ × ℚ_[p]) (hz : z.2 ≠ 0) : mixedFiniteShellSymbol p b J z =
      if z.2.valuation ∈ J then b (‖z.2‖ * z.1) else 0 := by
  classical
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hm (n : ℤ) : z.2 ∈ padicLatticeBall p n \ padicLatticeBall p (n+1) ↔ n = z.2.valuation := by
    rw [padicLatticeShell_iff, Padic.norm_eq_zpow_neg_valuation hz,
      zpow_right_inj₀ (zero_lt_one.trans hp) hp.ne', neg_inj, eq_comm]
  simp [mixedFiniteShellSymbol, mixedShellSymbol, Set.indicator, hm, mul_ite]

/-- The finite symbols stabilize off the null zero fiber. Only the transform
of the test needs an integrable majorant, not the full product symbol. -/
theorem tendsto_mixedFiniteShellSymbol_pairing {b : ℝ → ℂ} (hb : Integrable b)
    {C : ℝ} (hC : ∀ t, ‖b t‖ ≤ C) {g : ℝ × ℚ_[p] → ℂ}
    (hg : Integrable (tamagawaFourier M χ g) M) :
    Tendsto (fun J : Finset ℤ ↦ ∫ x, mixedFiniteShellSymbol p b J x * tamagawaFourier M χ g x ∂M)
      atTop (𝓝 (∫ x, b (‖x.2‖ * x.1) * tamagawaFourier M χ g x ∂M)) := by
  classical
  have : (padicTamagawaMeasure p).IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  have hne : ∀ᵐ z : ℝ × ℚ_[p] ∂M, z.2 ≠ 0 :=
    Measure.quasiMeasurePreserving_snd.ae ((padicTamagawaMeasure p).ae_ne 0)
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ C * ‖tamagawaFourier M χ g x‖)
  · exact Eventually.of_forall fun J ↦ (finiteSymbolIntegrable p hb J).aestronglyMeasurable.mul hg.aestronglyMeasurable
  · apply Eventually.of_forall
    intro J
    filter_upwards [hne] with z hz
    rw [norm_mul, mixedFiniteShellSymbol_eval p J z hz]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    split_ifs
    · exact hC _
    · simpa using (norm_nonneg (b 0)).trans (hC 0)
  · exact hg.norm.const_mul C
  · filter_upwards [hne] with z hz
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop ({z.2.valuation} : Finset ℤ)] with J hJ
    have hm : z.2.valuation ∈ J := hJ (Finset.mem_singleton_self _)
    rw [mixedFiniteShellSymbol_eval p J z hz, ite_eq_left hm]

/-- The local representative of the Fourier distribution, defined by the
unconditional shell sum. Its values on the two null axes are immaterial. -/
def mixedCutoffKernel (b : ℝ → ℂ) (x : ℝ × ℚ_[p]) : ℂ :=
  ∑' n, mixedShellFourier p b x.1 x.2 n

private theorem mixedFiniteFourier_measurable {b : ℝ → ℂ} (hb : Measurable b)
    (J : Finset ℤ) : Measurable (tamagawaFourier M χ (mixedFiniteShellSymbol p b J)) := by
  have : (padicTamagawaMeasure p).IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  obtain ⟨e, he⟩ := exists_padicPontryaginDualEquiv p
  have hpc : Continuous (padicStandardCharacter p) := by
    simpa only [he, one_mul, mul_one] using (show Continuous (fun x : ℚ_[p] ↦
      e (Multiplicative.ofAdd (1 : ℚ_[p])) (Multiplicative.ofAdd x)) from
        (e (Multiplicative.ofAdd (1 : ℚ_[p]))).continuous)
  have hc : Continuous χ := (Circle.exp.continuous.comp
    (continuous_const.mul continuous_fst)).mul (hpc.comp continuous_snd)
  have hf : Measurable (mixedFiniteShellSymbol p b J) := by
    unfold mixedFiniteShellSymbol
    apply Finset.measurable_sum
    intro n _
    apply (hb.comp (measurable_snd.norm.mul measurable_fst)).mul
    have hS : MeasurableSet (padicLatticeBall p n \ padicLatticeBall p (n+1)) := by
      rw [padicLatticeBall_eq_closedBall, padicLatticeBall_eq_closedBall]
      exact MeasurableSet.diff (IsClosed.measurableSet Metric.isClosed_closedBall)
        (IsClosed.measurableSet Metric.isClosed_closedBall)
    exact ((measurable_const : Measurable (fun _ : ℚ_[p] ↦ (1 : ℂ))).indicator hS).comp measurable_snd
  have hk : Continuous (fun z : (ℝ × ℚ_[p]) × (ℝ × ℚ_[p]) ↦
      star (χ (z.2 * z.1) : ℂ)) :=
    (continuous_subtype_val.comp (hc.comp (continuous_snd.mul continuous_fst))).star
  exact (((hf.comp measurable_snd).mul hk.measurable).stronglyMeasurable.integral_prod_right'
    (ν := M)).measurable

/-- On any compact product rectangle the limit is integrable and finite
Fourier-shell sums converge under integration against a bounded measurable test. -/
theorem mixedCutoffKernel_integrableOn_and_tendsto {b : ℝ → ℂ} (hbm : Measurable b)
    (hbi : Integrable b)
    (he : ∀ x, tamagawaFourier volume realCutoffCharacter b (-x) =
      tamagawaFourier volume realCutoffCharacter b x)
    {C : ℝ} (hC : 0 ≤ C) (hdecay : Lacunary.Decays (tamagawaFourier volume realCutoffCharacter b) C)
    (a d : ℝ) (z : ℚ_[p]) (R : ℝ) {g : ℝ × ℚ_[p] → ℂ} (hg : Measurable g)
    {G : ℝ} (hG : ∀ x, ‖g x‖ ≤ G) :
    let box := Icc a d ×ˢ Metric.closedBall z R
    IntegrableOn (mixedCutoffKernel p b) box M ∧
      Tendsto (fun J : Finset ℤ ↦ ∫ x in box,
        tamagawaFourier M χ (mixedFiniteShellSymbol p b J) x * g x ∂M)
        atTop (𝓝 (∫ x in box, mixedCutoffKernel p b x * g x ∂M)) := by
  intro box
  have : (padicTamagawaMeasure p).IsAddHaarMeasure :=
    (Classical.choose_spec (padicTamagawaMeasure_existsUnique p).exists).1
  let μ := (M).restrict box
  have : IsFiniteMeasure μ := by
    apply isFiniteMeasure_restrict.mpr
    change (M) (Icc a d ×ˢ Metric.closedBall z R) ≠ ⊤
    rw [Measure.prod_prod]
    exact (ENNReal.mul_lt_top isCompact_Icc.measure_lt_top measure_closedBall_lt_top).ne
  have hNA : ∀ᵐ x : ℝ × ℚ_[p] ∂μ, x.1 ≠ 0 ∧ x.2 ≠ 0 :=
    (ae_mono Measure.restrict_le_self) ((Measure.quasiMeasurePreserving_fst.ae
      ((volume : Measure ℝ).ae_ne 0)).and
      (Measure.quasiMeasurePreserving_snd.ae ((padicTamagawaMeasure p).ae_ne 0)))
  let T (J : Finset ℤ) := tamagawaFourier M χ (mixedFiniteShellSymbol p b J)
  let P : ℝ := p
  let A := C * ‖((-((p:ℝ)⁻¹ : ℂ)))‖ + (C + C * (1-P⁻¹)⁻¹) * ‖(1-((p:ℝ)⁻¹ : ℂ))‖
  let D := C / Real.log P * ‖(1-((p:ℝ)⁻¹ : ℂ))‖
  let W (x : ℝ × ℚ_[p]) := A + D * (MixedLogLocal.loss |x.1| + MixedLogLocal.loss ‖x.2‖)
  have hW : Integrable W μ := (integrable_const A).add
    ((MixedLogLocal.rectangle_integrableOn p a d z R).const_mul D)
  have hD : 0 ≤ D := by
    unfold D P
    exact mul_nonneg (div_nonneg hC (Real.log_nonneg
      (by exact_mod_cast (Fact.out : p.Prime).one_lt.le))) (norm_nonneg _)
  have hsum (J : Finset ℤ) (x : ℝ × ℚ_[p]) :
      T J x = ∑ n ∈ J, mixedShellFourier p b x.1 x.2 n :=
    tamagawaFourier_mixedFiniteShellSymbol p hbi J x.1 x.2
  have hbound (x : ℝ × ℚ_[p]) (h1 : x.1 ≠ 0) (h2 : x.2 ≠ 0) (J : Finset ℤ) :
      ‖T J x‖ ≤ W x := by
    have h := (mixedShellFourier_absolute_partial p b he hC hdecay h1 h2).2 J
    rw [hsum]
    refine (norm_sum_le ..).trans (h.trans ?_)
    have hlog : max 0 (-Real.log (|x.1| * ‖x.2‖)) ≤
        MixedLogLocal.loss |x.1| + MixedLogLocal.loss ‖x.2‖ := by
      rw [Real.log_mul (abs_ne_zero.mpr h1) (norm_ne_zero_iff.mpr h2)]
      unfold MixedLogLocal.loss
      apply max_le
      · exact add_nonneg (le_max_right ..) (le_max_right ..)
      · linarith [le_max_left (-Real.log |x.1|) 0, le_max_left (-Real.log ‖x.2‖) 0]
    calc
      _ = A + D * max 0 (-Real.log (|x.1| * ‖x.2‖)) := by dsimp [A, D, P]; ring
      _ ≤ W x := add_le_add le_rfl (mul_le_mul_of_nonneg_left hlog hD)
  have hT (x : ℝ × ℚ_[p]) (h1 : x.1 ≠ 0) (h2 : x.2 ≠ 0) :
      Tendsto (fun J : Finset ℤ ↦ T J x) atTop (𝓝 (mixedCutoffKernel p b x)) := by
    have h := (mixedShellFourier_hasSum p b he hC hdecay h1 h2).summable.hasSum
    simpa only [hsum, mixedCutoffKernel, HasSum, SummationFilter.unconditional_filter] using h
  have hmeas : Measurable (mixedCutoffKernel p b) := by
    apply Measurable.tsum
    intro n
    have h : (fun x : ℝ × ℚ_[p] ↦ mixedShellFourier p b x.1 x.2 n) = T {n} := by
      funext x
      rw [hsum]
      simp
    rw [h]
    exact mixedFiniteFourier_measurable p hbm {n}
  refine ⟨hW.mono' hmeas.aestronglyMeasurable ?_, ?_⟩
  · filter_upwards [hNA] with x hx
    exact le_of_tendsto (hT x hx.1 hx.2).norm (Eventually.of_forall (hbound x hx.1 hx.2))
  · apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ W x * G)
    · exact Eventually.of_forall fun J ↦ ((mixedFiniteFourier_measurable p hbm J).mul hg).aestronglyMeasurable
    · apply Eventually.of_forall
      intro J
      filter_upwards [hNA] with x hx
      rw [norm_mul]
      exact mul_le_mul (hbound x hx.1 hx.2 J) (hG x) (norm_nonneg _)
        ((norm_nonneg (T J x)).trans (hbound x hx.1 hx.2 J))
    · exact hW.mul_const G
    · filter_upwards [hNA] with x hx
      exact (hT x hx.1 hx.2).mul tendsto_const_nhds

/-- The locally integrable shell sum represents the Fourier distribution of
the actual product cutoff: there is no residual distribution on the axes. -/
theorem mixedCutoffKernel_pairing {b : ℝ → ℂ} (hbm : Measurable b)
    (hbi : Integrable b) {C₀ : ℝ} (hb : ∀ t, ‖b t‖ ≤ C₀)
    (he : ∀ x, tamagawaFourier volume realCutoffCharacter b (-x) =
      tamagawaFourier volume realCutoffCharacter b x)
    {C : ℝ} (hC : 0 ≤ C) (hdecay : Lacunary.Decays (tamagawaFourier volume realCutoffCharacter b) C)
    {g : ℝ × ℚ_[p] → ℂ} (hg : Continuous g) (hc : HasCompactSupport g)
    (hgF : Integrable (tamagawaFourier M χ g) M) :
    (∫ x, mixedCutoffKernel p b x * g x ∂M) =
      ∫ x, b (‖x.2‖ * x.1) * tamagawaFourier M χ g x ∂M := by
  obtain ⟨R, hR⟩ := hc.isBounded.subset_closedBall (0 : ℝ × ℚ_[p])
  obtain ⟨G, hG⟩ := (hc.image hg).isBounded.subset_closedBall (0 : ℂ)
  let box := Icc (-R) R ×ˢ Metric.closedBall (0 : ℚ_[p]) R
  have hbmeas : MeasurableSet box := measurableSet_Icc.prod
    (IsClosed.measurableSet Metric.isClosed_closedBall)
  have hsupp : Function.support g ⊆ box := by
    intro x hx
    have hr : x ∈ Metric.closedBall (0 : ℝ × ℚ_[p]) R := hR (subset_closure hx)
    have h : ‖x‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hr
    have h1 : |x.1| ≤ R := by simpa only [Real.norm_eq_abs] using (norm_fst_le x).trans h
    refine ⟨abs_le.mp h1, ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_snd_le x).trans h
  have hbd (x : ℝ × ℚ_[p]) : ‖g x‖ ≤ max 0 G := by
    by_cases hx : g x = 0
    · rw [hx, norm_zero]
      exact le_max_left _ _
    · have hr : g x ∈ Metric.closedBall (0 : ℂ) G := hG ⟨x, subset_closure hx, rfl⟩
      have h : ‖g x‖ ≤ G := by simpa only [Metric.mem_closedBall, dist_zero_right] using hr
      exact h.trans (le_max_right _ _)
  have hrestrict (F : ℝ × ℚ_[p] → ℂ) :
      (∫ x, F x * g x ∂M) = ∫ x in box, F x * g x ∂M := by
    rw [← integral_indicator hbmeas]
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    by_cases hx : x ∈ box
    · rw [indicator_of_mem hx]
    · have hz : g x = 0 := by by_contra hn; exact hx (hsupp hn)
      rw [indicator_of_notMem hx]
      change F x * g x = 0
      rw [hz, mul_zero]
  have hleft := (mixedCutoffKernel_integrableOn_and_tendsto p hbm hbi he hC hdecay
    (-R) R 0 R hg.measurable hbd).2
  have hright := tendsto_mixedFiniteShellSymbol_pairing p hbi hb hgF
  rw [hrestrict (mixedCutoffKernel p b)]
  refine tendsto_nhds_unique (hleft.congr' (Eventually.of_forall fun J ↦ ?_)) hright
  exact (hrestrict _).symm.trans (mixedFiniteShellSymbol_pairing p hbi J hg hc)

/-- An even compactly supported `C²` upper profile meets the hypotheses of
the distribution pairing without any auxiliary bounds on its Fourier transform. -/
theorem mixedCutoffKernel_pairing_of_contDiff {b : ℝ → ℂ}
    (hbc : ContDiff ℝ 2 b) (hbs : HasCompactSupport b) (hbe : Function.Even b)
    {g : ℝ × ℚ_[p] → ℂ} (hg : Continuous g) (hc : HasCompactSupport g)
    (hgF : Integrable (tamagawaFourier M χ g) M) :
    (∫ x, mixedCutoffKernel p b x * g x ∂M) =
      ∫ x, b (‖x.2‖ * x.1) * tamagawaFourier M χ g x ∂M := by
  obtain ⟨U, hU⟩ := (hbs.image hbc.continuous).isBounded.subset_closedBall (0 : ℂ)
  have hb (t : ℝ) : ‖b t‖ ≤ max 0 U := by
    by_cases ht : b t = 0
    · rw [ht, norm_zero]
      exact le_max_left _ _
    · have hm : b t ∈ Metric.closedBall (0 : ℂ) U := hU ⟨t, subset_closure ht, rfl⟩
      have h : ‖b t‖ ≤ U := by simpa only [Metric.mem_closedBall, dist_zero_right] using hm
      exact h.trans (le_max_right _ _)
  have he (x : ℝ) : tamagawaFourier volume realCutoffCharacter b (-x) =
      tamagawaFourier volume realCutoffCharacter b x := by
    let f (t : ℝ) := b t * star (realCutoffCharacter (t*x) : ℂ)
    change (∫ t, b t * star (realCutoffCharacter (t*(-x)) : ℂ)) = ∫ t, f t
    rw [← integral_neg_eq_self f]
    refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
    change b t * star (realCutoffCharacter (t*(-x)) : ℂ) =
      b (-t) * star (realCutoffCharacter ((-t)*x) : ℂ)
    rw [hbe t, neg_mul, mul_neg]
  let A : ℝ := (∫ t, ‖b t‖) +
    (4 * Real.pi ^ 2)⁻¹ * ∫ t, ‖iteratedDeriv 2 b t‖
  have hA : 0 ≤ A := add_nonneg (integral_nonneg fun _ ↦ norm_nonneg _)
    (mul_nonneg (by positivity) (integral_nonneg fun _ ↦ norm_nonneg _))
  refine mixedCutoffKernel_pairing p hbc.continuous.measurable
    (hbc.continuous.integrable_of_hasCompactSupport hbs) hb he (C := 2*A)
    (mul_nonneg (by norm_num : 0 ≤ (2:ℝ)) hA) ?_ hg hc hgF
  intro x hx
  refine (norm_real_tamagawaFourier_le b hbc hbs x).trans ?_
  apply (div_le_div_iff₀ (by positivity : 0 < 1+x^2) (by positivity : 0 < (1+x)^2)).2
  have hl : (1+x)^2 ≤ 2*(1+x^2) := by nlinarith [sq_nonneg (x-1)]
  nlinarith [mul_le_mul_of_nonneg_left hl hA]

end RiemannMasullo.MixedCutoff
