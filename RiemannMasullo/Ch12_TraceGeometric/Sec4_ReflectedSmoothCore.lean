module

public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Topology.CompactOpen

/-! # Smooth density on the supported reflected half-line -/

public noncomputable section

open Filter Function MeasureTheory Set
open scoped ContDiff ENNReal Topology

namespace RiemannMasullo

local notation "L₂ℝ" => Lp ℂ 2 (volume : Measure ℝ)

/-- The flat L² classes with a smooth compact representative supported in the
open right half-line. -/
@[expose] def openHalflineSmoothCore (a : ℝ) : Set L₂ℝ :=
  {v | ∃ g : ℝ → ℂ, (v : ℝ → ℂ) =ᵐ[volume] g ∧ HasCompactSupport g ∧
    ContDiff ℝ (∞ : ℕ∞ω) g ∧ tsupport g ⊆ Ioi a}

/-- Right-half-line-supported L² classes are approximable by smooth compact
profiles supported strictly inside the half-line. -/
theorem mem_closure_openHalflineSmoothCore (a : ℝ) (u : L₂ℝ)
    (hu : ∀ᵐ x : ℝ ∂volume, x < a → u x = 0) :
    u ∈ closure (openHalflineSmoothCore a) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hε₂ : 0 < ε / 2 := half_pos hε
  let translation : C(ℝ, C(ℝ, ℝ)) :=
    (⟨fun p : ℝ × ℝ ↦ p.2 + p.1, continuous_snd.add continuous_fst⟩ : C(ℝ × ℝ, ℝ)).curry
  let hmeasure (h : ℝ) : MeasurePreserving (translation h) (volume : Measure ℝ) volume :=
    measurePreserving_add_right volume h
  let shift (h : ℝ) : L₂ℝ := Lp.compMeasurePreserving (translation h) (hmeasure h) u
  have hcont : ContinuousAt shift 0 :=
    (Continuous.compMeasurePreservingLp (f := fun _ : ℝ ↦ u) continuous_const translation.continuous
      hmeasure ENNReal.ofNat_ne_top).continuousAt
  obtain ⟨d, hd, hnear⟩ := Metric.continuousAt_iff.mp hcont (ε / 2) hε₂
  let δ := d / 2
  have hδ : 0 < δ := half_pos hd
  let uδ := shift (-δ)
  have hsmall : dist (-δ : ℝ) 0 < d := by
    rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos hδ]
    exact half_lt_self hd
  have huδ : dist u uδ < ε / 2 := by
    have h := hnear hsmall
    have hzero : shift 0 = u := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_compMeasurePreserving u (hmeasure 0)] with x hx
      change shift 0 x = u (x + 0) at hx
      simpa only [add_zero] using hx
    rw [hzero, dist_comm] at h
    exact h
  have hshift : ∀ᵐ x : ℝ ∂volume, x < a + δ → uδ x = 0 := by
    filter_upwards [Lp.coeFn_compMeasurePreserving u (hmeasure (-δ)),
      (hmeasure (-δ)).quasiMeasurePreserving.tendsto_ae.eventually hu]
      with x hx hy
    intro hlt
    change uδ x = u (x + -δ) at hx
    change x + -δ < a → u (x + -δ) = 0 at hy
    exact hx.trans (hy (by linarith))
  let ρ (x : ℝ) := Real.smoothTransition ((x - (a + δ / 2)) / (δ / 2))
  have hρ : ContDiff ℝ (∞ : ℕ∞ω) ρ :=
    Real.smoothTransition.contDiff.comp ((contDiff_id.sub contDiff_const).div_const _)
  have hρbd (x : ℝ) : |ρ x| ≤ 1 := by
    have hnonneg : 0 ≤ ρ x := Real.smoothTransition.nonneg _
    rw [abs_of_nonneg hnonneg]
    exact Real.smoothTransition.le_one _
  have hρzero (x : ℝ) (hx : x ≤ a + δ / 2) : ρ x = 0 :=
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx)
      (half_pos hδ).le)
  have hρone (x : ℝ) (hx : a + δ ≤ x) : ρ x = 1 :=
    Real.smoothTransition.one_of_one_le ((le_div_iff₀ (half_pos hδ)).2 (by linarith))
  let σ (x : ℝ) : ℂ := ρ x
  have hσbound (x : ℝ) : ‖σ x‖ ≤ 1 := by
    simpa only [σ, Complex.norm_real, Real.norm_eq_abs] using hρbd x
  have hσ : MemLp σ ∞ (volume : Measure ℝ) :=
    memLp_top_of_bound (Complex.measurable_ofReal.comp hρ.continuous.measurable).aestronglyMeasurable
      1 (ae_of_all _ hσbound)
  let mul := ContinuousLinearMap.mul ℂ ℂ
  let P : L₂ℝ →L[ℂ] L₂ℝ := mul.holderL volume ∞ 2 2 (hσ.toLp σ)
  have hP (v : L₂ℝ) : (P v : ℝ → ℂ) =ᵐ[volume] fun x ↦ σ x * v x :=
    (mul.coeFn_holder (r := 2) (hσ.toLp σ) v).trans
      (hσ.coeFn_toLp.mono fun x hx ↦ congrArg (· * v x) hx)
  have hPnorm : ‖P‖ ≤ 1 := by
    refine P.opNorm_le_bound zero_le_one fun v ↦ ?_
    rw [one_mul]
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hP v] with x hx
    rw [hx, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hσbound x)
  have hPfix : P uδ = uδ := by
    apply Lp.ext
    filter_upwards [hP uδ, hshift] with x hx hxzero
    by_cases h : x < a + δ
    · rw [hx, hxzero h, mul_zero]
    · rw [hx, show σ x = (ρ x : ℂ) from rfl, hρone x (le_of_not_gt h), Complex.ofReal_one, one_mul]
  obtain ⟨v, ⟨g, hgRep, hgC, hgD⟩, hgv⟩ := (Metric.mem_closure_iff.mp
    ((Lp.dense_hasCompactSupport_contDiff (μ := (volume : Measure ℝ)) (F := ℂ)
      (p := 2) ENNReal.ofNat_ne_top) uδ)) (ε / 2) hε₂
  let k (x : ℝ) := (ρ x : ℂ) * g x
  have hkRep : (P v : ℝ → ℂ) =ᵐ[volume] k :=
    (hP v).trans (hgRep.mono fun x hx ↦ congrArg (fun z ↦ (ρ x : ℂ) * z) hx)
  have hkC : HasCompactSupport k := hgC.mul_left
  have hkD : ContDiff ℝ (∞ : ℕ∞ω) k := (Complex.ofRealCLM.contDiff.comp hρ).mul hgD
  have hkS : tsupport k ⊆ Ici (a + δ / 2) := by
    apply closure_minimal _ isClosed_Ici
    intro x hx
    change a + δ / 2 ≤ x
    apply le_of_not_gt
    intro hlt
    exact hx (by simp [k, hρzero x hlt.le])
  have hkS' : tsupport k ⊆ Ioi a := fun x hx ↦ by
    have h := hkS hx
    change a + δ / 2 ≤ x at h
    change a < x
    linarith
  have hPdist : dist (P uδ) (P v) ≤ dist uδ v := by
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    refine (P.le_opNorm _).trans ?_
    simpa only [one_mul] using (mul_le_mul_of_nonneg_right hPnorm (norm_nonneg (uδ - v)))
  rw [hPfix] at hPdist
  refine ⟨P v, ⟨k, hkRep, hkC, hkD, hkS'⟩, ?_⟩
  exact (dist_triangle u uδ (P v)).trans_lt (by linarith)

/-- If a continuous moment is nonzero on one compact smooth profile,
its zero-moment smooth core is dense in its supported kernel. -/
theorem mem_closure_openHalflineSmoothCore_moment (a : ℝ) (u : L₂ℝ)
    (hu : ∀ᵐ x : ℝ ∂volume, x < a → u x = 0)
    (M : L₂ℝ →L[ℂ] ℂ) (hMu : M u = 0)
    (b : L₂ℝ) (hb : b ∈ openHalflineSmoothCore a) (hMb : M b ≠ 0) :
    u ∈ closure {v | v ∈ openHalflineSmoothCore a ∧ M v = 0} := by
  let c (v : L₂ℝ) := M v / M b
  let T (v : L₂ℝ) := v - c v • b
  have hc : Continuous c := M.continuous.div_const _
  have hT : Continuous T := continuous_id.sub (hc.smul continuous_const)
  obtain ⟨β, hβRep, hβC, hβD, hβS⟩ := hb
  have hMap : MapsTo T (openHalflineSmoothCore a)
      {v | v ∈ openHalflineSmoothCore a ∧ M v = 0} := by
    intro v hv
    obtain ⟨g, hgRep, hgC, hgD, hgS⟩ := hv
    let k (x : ℝ) := g x - c v * β x
    have hkRep : (T v : ℝ → ℂ) =ᵐ[volume] k := by
      filter_upwards [Lp.coeFn_sub v (c v • b), Lp.coeFn_smul (c v) b, hgRep, hβRep]
        with x hsub hsmul hg hβ
      simp only [T, k, hsub, Pi.sub_apply, hsmul, Pi.smul_apply, smul_eq_mul, hg, hβ]
    have hkS : tsupport k ⊆ tsupport g ∪ tsupport β := by
      apply closure_minimal _ (isClosed_closure.union isClosed_closure)
      intro x hx
      by_contra h
      have hg : g x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' ↦ h (Or.inl hx'))
      have hβ : β x = 0 := image_eq_zero_of_notMem_tsupport (fun hx' ↦ h (Or.inr hx'))
      exact hx (by simp [k, hg, hβ])
    have hK : IsCompact (tsupport g ∪ tsupport β) := IsCompact.union hgC hβC
    have hkC : HasCompactSupport k := hK.of_isClosed_subset isClosed_closure hkS
    have hkD : ContDiff ℝ (∞ : ℕ∞ω) k := hgD.sub (contDiff_const.mul hβD)
    refine ⟨⟨k, hkRep, hkC, hkD, hkS.trans (union_subset hgS hβS)⟩, ?_⟩
    change M (v - c v • b) = 0
    rw [map_sub, map_smul, smul_eq_mul, show c v * M b = M v from div_mul_cancel₀ _ hMb,
      sub_self]
  have h := hMap.closure hT (mem_closure_openHalflineSmoothCore a u hu)
  simpa [T, c, hMu] using h

end RiemannMasullo
