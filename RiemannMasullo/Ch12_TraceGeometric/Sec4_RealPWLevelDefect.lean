module

public import RiemannMasullo.AppC_LCTVS.Sec3a
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

/-! # The trace on the polar-free Paley–Wiener level in §12.4: a rank-one defect

Theorem 12.4.1.1, pp. 514–519, computes a regularized trace by the method of Connes: the
cut-off convolution is composed with a cutoff in Fourier space and the diagonal of the kernel is
integrated (pp. 516–519). The theorem is stated, and used on p. 520, for the convolution acting on
the invariant Paley–Wiener level, a closed subspace cut out by the polar conditions. Errata I365
and I398 record that the two regularized traces are not identified.

This file computes their difference in the model `F = ℚ`, `S = {∞}`, order `s = 0`. There the
level is the band of the Fourier cutoff less one unit vector `e`, so the two compressions differ
by a rank-one operator (`comp_sub_comp_sub_rankOne`), and their traces by `⟪e, T e⟫`
(`hilbertTrace_comp_sub_rankOne`). For the dilation by `g` this number is
`min (g ^ (1/2)) (g ^ (-1/2))` (`inner_realPWLevelPolarVector_translation`), whatever the band.
So for a test `φ` the level trace falls short of the Connes trace, in the limit of the spatial
cutoffs, by `∫ φ(g) min (g ^ (1/2)) (g ^ (-1/2)) d×g` (`sLocalTrace_realPWLevel_defect`). This is
not zero, as (12.4.1.1)–(12.4.1.3) would need on the level, and it is not the sum
`M(φ)(|·|^(1/2)) + M(φ)(|·|^(-1/2))` of the two polar Mellin terms that p. 520 subtracts: for
`φ ≥ 0` it is strictly smaller.

## The model and the coordinate

Even functions `f` on `ℝ` with Fourier transform supported in `[-Y, Y]` form the band; the level
is the closure of those with `f(0) = 0` and `∫ f = 0`. In `L²` the second condition is not closed,
so the level is the band with `f(0) = 0`, the orthogonal complement in the band of the
reproducing kernel at `0`. The dilation of p. 515 is `f ↦ g ^ (-1/2) f(x / g)`. Write
`Ψ(u) = √2 e^(u/2) (𝓕 f)(e^u)`. This is a unitary map from even `L²` functions onto `L²(ℝ, du)`
under which
* the dilation by `g` becomes the translation `Ψ ↦ Ψ(u + log g)` (`realLogTranslation`),
* the band becomes the functions supported in `u ≤ c`, `c = log Y`,
* `f(0) = 0` becomes orthogonality to `e(u) = e^((u - c)/2)` on `u ≤ c`
  (`realPWLevelPolarVector`).
The spatial cutoff becomes a bounded operator that tends strongly to the identity as the cutoff
is removed; only that property is used. The dictionary itself is not formalized here.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped InnerProductSpace

namespace RiemannMasullo

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Removing the direction `e` from the right factor `P` changes `T ∘ P` by the rank-one
operator `x ↦ ⟪e, x⟫ T e`. -/
theorem comp_sub_comp_sub_rankOne (T P : H →L[ℂ] H) (e : H) :
    T.comp P - T.comp (P - (innerSL ℂ e).smulRight e) = (innerSL ℂ e).smulRight (T e) := by
  ext x
  simp only [sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smulRight_apply, map_sub, map_smul]
  abel

/-- The trace of the rank-one operator `x ↦ ⟪e, x⟫ T e` is `⟪e, T e⟫`. -/
theorem hilbertTrace_rankOne_apply (T : H →L[ℂ] H) (e : H) :
    hilbertTrace ⟨(innerSL ℂ e).smulRight (T e), smulRight_mem_nuclearEndomorphisms _ _⟩ =
      ⟪e, T e⟫_ℂ := by
  rw [hilbertTrace_smulRight]
  rfl

/-- If `T ∘ P` is nuclear, so is `T ∘ (P - ⟪e, ·⟫ e)`, and the traces differ by `⟪e, T e⟫`. -/
theorem hilbertTrace_comp_sub_rankOne (T P : H →L[ℂ] H) (e : H)
    (hTP : T.comp P ∈ nuclearEndomorphisms H) :
    ∃ hQ : T.comp (P - (innerSL ℂ e).smulRight e) ∈ nuclearEndomorphisms H,
      hilbertTrace ⟨_, hQ⟩ = hilbertTrace ⟨_, hTP⟩ - ⟪e, T e⟫_ℂ := by
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := H)
  have hR := smulRight_mem_nuclearEndomorphisms (innerSL ℂ e) (T e)
  have hdiff : T.comp (P - (innerSL ℂ e).smulRight e) =
      T.comp P - (innerSL ℂ e).smulRight (T e) := by
    rw [← comp_sub_comp_sub_rankOne T P e, sub_sub_cancel]
  have hQ : T.comp (P - (innerSL ℂ e).smulRight e) ∈ nuclearEndomorphisms H := by
    rw [hdiff]
    exact (nuclearEndomorphisms H).sub_mem hTP hR
  refine ⟨hQ, ?_⟩
  have heq : (⟨_, hQ⟩ : nuclearEndomorphisms H) = ⟨_, hTP⟩ - ⟨_, hR⟩ := Subtype.ext hdiff
  rw [← htr, heq, map_sub, htr, htr, hilbertTrace_rankOne_apply]

end Abstract

section Model

/-- Translation by `t` on `L²(ℝ)`: the dilation by `g = e^t` of p. 515 in the logarithmic
frequency coordinate. -/
def realLogTranslation (t : ℝ) : Lp ℂ 2 (volume (α := ℝ)) →L[ℂ] Lp ℂ 2 (volume (α := ℝ)) :=
  (Lp.compMeasurePreservingₗᵢ ℂ (fun u : ℝ ↦ u + t)
    (measurePreserving_add_right volume t)).toContinuousLinearMap

/-- The profile `e^((u - c)/2)` on `u ≤ c`, zero elsewhere. -/
def realPWLevelPolarFun (c u : ℝ) : ℂ :=
  ((Iic c).indicator (fun u : ℝ ↦ Real.exp ((u - c) / 2)) u : ℝ)

/-- The profile is square integrable. -/
theorem realPWLevelPolarFun_memLp (c : ℝ) :
    MemLp (realPWLevelPolarFun c) 2 (volume (α := ℝ)) := by
  have hmeas : Measurable (realPWLevelPolarFun c) :=
    Complex.measurable_ofReal.comp
      ((Real.measurable_exp.comp ((measurable_id.sub_const c).div_const 2)).indicator
        measurableSet_Iic)
  rw [memLp_two_iff_integrable_sq_norm hmeas.aestronglyMeasurable]
  have hint : IntegrableOn (fun u : ℝ ↦ Real.exp u * Real.exp (-c)) (Iic c) :=
    (integrableOn_exp_Iic c).mul_const _
  refine (integrable_indicator_iff measurableSet_Iic).mpr hint |>.congr (ae_of_all _ fun u ↦ ?_)
  by_cases hu : u ∈ Iic c
  · simp only [realPWLevelPolarFun, indicator_of_mem hu, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
    rw [← Real.exp_add, ← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  · simp [realPWLevelPolarFun, indicator_of_notMem hu]

/-- The unit vector of the band `u ≤ c` to which the level is orthogonal: the image of the
reproducing kernel at `0` of the band-limited functions, normalized. -/
def realPWLevelPolarVector (c : ℝ) : Lp ℂ 2 (volume (α := ℝ)) :=
  (realPWLevelPolarFun_memLp c).toLp _

/-- The translate of the polar vector is represented by the translated profile. -/
private theorem realLogTranslation_polarVector_ae (c t : ℝ) :
    (realLogTranslation t (realPWLevelPolarVector c) : ℝ → ℂ) =ᵐ[volume]
      fun u ↦ realPWLevelPolarFun c (u + t) := by
  have h1 := Lp.coeFn_compMeasurePreserving (realPWLevelPolarVector c)
    (measurePreserving_add_right (volume (α := ℝ)) t)
  have h2 : (realPWLevelPolarVector c : ℝ → ℂ) =ᵐ[volume] realPWLevelPolarFun c :=
    (realPWLevelPolarFun_memLp c).coeFn_toLp
  exact h1.trans
    ((measurePreserving_add_right (volume (α := ℝ)) t).quasiMeasurePreserving.ae_eq_comp h2)

/-- Paper: Theorem 12.4.1.1, proof, pp. 515–517. The diagonal coefficient of the dilation by
`g = e^t` at the polar vector of the band is `e^(-|t|/2) = min (g^(1/2)) (g^(-1/2))`, for every
band.
Reconstruction: The paper does not state this. It is the trace of the rank-one difference
between the dilation compressed to the band of the Fourier cutoff and compressed to the level
with `f(0) = 0`, in the rational real-place model at order zero. -/
theorem inner_realPWLevelPolarVector_translation (c t : ℝ) :
    ⟪realPWLevelPolarVector c, realLogTranslation t (realPWLevelPolarVector c)⟫_ℂ =
      (Real.exp (-|t| / 2) : ℂ) := by
  rw [L2.inner_def]
  have hint : ∫ u, ⟪(realPWLevelPolarVector c : ℝ → ℂ) u,
        (realLogTranslation t (realPWLevelPolarVector c) : ℝ → ℂ) u⟫_ℂ =
      ∫ u, (((Iic (c - max t 0)).indicator
        (fun u : ℝ ↦ Real.exp u * Real.exp (t / 2 - c)) u : ℝ) : ℂ) := by
    refine integral_congr_ae ?_
    filter_upwards [(realPWLevelPolarFun_memLp c).coeFn_toLp,
      realLogTranslation_polarVector_ae c t] with u h1 h2
    have h1' : (realPWLevelPolarVector c : ℝ → ℂ) u = realPWLevelPolarFun c u := h1
    rw [h1', h2, RCLike.inner_apply]
    simp only [realPWLevelPolarFun, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul]
    congr 1
    by_cases h : u ≤ c - max t 0
    · have hu : u ≤ c := h.trans (by linarith [le_max_right t 0])
      have hut : u + t ≤ c := by linarith [le_max_left t 0]
      rw [indicator_of_mem (mem_Iic.mpr hut), indicator_of_mem (mem_Iic.mpr hu),
        indicator_of_mem (mem_Iic.mpr h), ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    · rw [indicator_of_notMem (fun h' ↦ h (mem_Iic.mp h'))]
      by_cases hu : u ≤ c
      · have hut : ¬ u + t ≤ c := fun hut ↦ h (by
          rcases le_total 0 t with ht | ht
          · rw [max_eq_left ht]; linarith
          · rw [max_eq_right ht]; linarith)
        rw [indicator_of_notMem (fun h' ↦ hut (mem_Iic.mp h')), zero_mul]
      · rw [indicator_of_notMem (s := Iic c) (fun h' ↦ hu (mem_Iic.mp h')), mul_zero]
  rw [hint, integral_complex_ofReal, integral_indicator measurableSet_Iic, integral_mul_const,
    integral_exp_Iic, ← Real.exp_add]
  congr 2
  rcases le_total 0 t with ht | ht
  · rw [max_eq_left ht, abs_of_nonneg ht]; ring
  · rw [max_eq_right ht, abs_of_nonpos ht]; ring

/-- Translation by zero is the identity. -/
theorem realLogTranslation_zero :
    realLogTranslation 0 = ContinuousLinearMap.id ℂ (Lp ℂ 2 (volume (α := ℝ))) := by
  ext1 x
  apply Lp.ext
  have h := Lp.coeFn_compMeasurePreserving x (measurePreserving_add_right (volume (α := ℝ)) 0)
  refine h.trans (ae_of_all _ fun u ↦ ?_)
  simp

/-- The polar vector is a unit vector. -/
theorem norm_realPWLevelPolarVector (c : ℝ) : ‖realPWLevelPolarVector c‖ = 1 := by
  have h := inner_realPWLevelPolarVector_translation c 0
  rw [realLogTranslation_zero, ContinuousLinearMap.id_apply, inner_self_eq_norm_sq_to_K] at h
  have h2 : (‖realPWLevelPolarVector c‖ : ℂ) ^ 2 = 1 := by simpa using h
  have h3 : ‖realPWLevelPolarVector c‖ ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg (realPWLevelPolarVector c)]

/-- The defect weight is strictly smaller than the sum of the two polar weights
`g^(1/2) + g^(-1/2)`, `g = e^t`. -/
theorem exp_neg_abs_half_lt (t : ℝ) :
    Real.exp (-|t| / 2) < Real.exp (t / 2) + Real.exp (-t / 2) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    linarith [Real.exp_pos (t / 2)]
  · rw [abs_of_nonpos ht, neg_neg]
    linarith [Real.exp_pos (-t / 2)]

/-- If `T` is the average of the dilations against `φ`, in the weak sense, its diagonal
coefficient at the polar vector is `∫ φ(t) e^(-|t|/2) dt`: in the multiplicative variable
`g = e^t`, the integral of `φ(g) min (g^(1/2)) (g^(-1/2))` against `d×g`. -/
theorem inner_realPWLevelPolarVector_average (c : ℝ) (φ : ℝ → ℂ)
    (T : Lp ℂ 2 (volume (α := ℝ)) →L[ℂ] Lp ℂ 2 (volume (α := ℝ)))
    (hT : ∀ h k : Lp ℂ 2 (volume (α := ℝ)),
      ⟪k, T h⟫_ℂ = ∫ t, φ t * ⟪k, realLogTranslation t h⟫_ℂ) :
    ⟪realPWLevelPolarVector c, T (realPWLevelPolarVector c)⟫_ℂ =
      ∫ t, φ t * (Real.exp (-|t| / 2) : ℂ) := by
  rw [hT]
  simp_rw [inner_realPWLevelPolarVector_translation]

/-- Paper: Theorem 12.4.1.1, pp. 514–519, as used on p. 520. In the rational real-place model at
order zero, let `T` be the convolution by `φ` (the average of the dilations), `C i` the spatial
cutoffs, tending strongly to the identity, and `P` the projection on the band of the Fourier
cutoff. The compression to the band and the compression to the polar-free level
`P - ⟪e, ·⟫ e` differ by a rank-one operator, and its trace tends to
`∫ φ(t) e^(-|t|/2) dt`.
Reconstruction: The paper does not state this. It measures the difference between the trace
that the proof computes (pp. 516–519, with the Fourier cutoff) and the trace on the invariant
Paley–Wiener level that the statement and p. 520 name (errata I365, I398, M25), in the model
described at the head of this file; that this is the model of the paper's level is not
formalized. The limit is neither zero nor the two polar Mellin terms
(`exp_neg_abs_half_lt`). -/
theorem sLocalTrace_realPWLevel_defect {ι : Type*} {l : Filter ι} (c : ℝ) (φ : ℝ → ℂ)
    (T : Lp ℂ 2 (volume (α := ℝ)) →L[ℂ] Lp ℂ 2 (volume (α := ℝ)))
    (hT : ∀ h k : Lp ℂ 2 (volume (α := ℝ)),
      ⟪k, T h⟫_ℂ = ∫ t, φ t * ⟪k, realLogTranslation t h⟫_ℂ)
    (C : ι → Lp ℂ 2 (volume (α := ℝ)) →L[ℂ] Lp ℂ 2 (volume (α := ℝ)))
    (hC : ∀ h, Tendsto (fun i ↦ C i h) l (𝓝 h))
    (P : Lp ℂ 2 (volume (α := ℝ)) →L[ℂ] Lp ℂ 2 (volume (α := ℝ))) :
    (∀ i, ((C i).comp T).comp P - ((C i).comp T).comp
        (P - (innerSL ℂ (realPWLevelPolarVector c)).smulRight (realPWLevelPolarVector c)) =
      (innerSL ℂ (realPWLevelPolarVector c)).smulRight (C i (T (realPWLevelPolarVector c)))) ∧
    Tendsto (fun i ↦ hilbertTrace
        ⟨(innerSL ℂ (realPWLevelPolarVector c)).smulRight (C i (T (realPWLevelPolarVector c))),
          smulRight_mem_nuclearEndomorphisms _ _⟩) l
      (𝓝 (∫ t, φ t * (Real.exp (-|t| / 2) : ℂ))) := by
  refine ⟨fun i ↦ comp_sub_comp_sub_rankOne ((C i).comp T) P (realPWLevelPolarVector c), ?_⟩
  have h1 (i : ι) : hilbertTrace
      ⟨(innerSL ℂ (realPWLevelPolarVector c)).smulRight (C i (T (realPWLevelPolarVector c))),
        smulRight_mem_nuclearEndomorphisms _ _⟩ =
      ⟪realPWLevelPolarVector c, C i (T (realPWLevelPolarVector c))⟫_ℂ :=
    hilbertTrace_rankOne_apply ((C i).comp T) (realPWLevelPolarVector c)
  simp_rw [h1]
  rw [← inner_realPWLevelPolarVector_average c φ T hT]
  exact tendsto_const_nhds.inner (hC _)

/-- Paper: Theorem 12.4.1.1, pp. 514–519, as used on p. 520. In the model of
`sLocalTrace_realPWLevel_defect`: if the compressions to the band are nuclear and their traces,
less a counterterm `κ`, tend to `L`, then the compressions to the polar-free level are nuclear
and their traces, less the same counterterm, tend to `L - ∫ φ(t) e^(-|t|/2) dt`.
Reconstruction: The paper does not state this. With `L` the local principal values and `κ` the
logarithmic term, the first limit is what the calculation of pp. 516–519 gives; the second is
then the trace on the level, which (12.4.1.1)–(12.4.1.3) state without the last term and p. 520
uses with `M(φ)(|·|^(1/2)) + M(φ)(|·|^(-1/2))` in its place. -/
theorem sLocalTrace_realPWLevel_trace_tendsto {ι : Type*} {l : Filter ι} (c : ℝ) (φ : ℝ → ℂ)
    (T : Lp ℂ 2 (volume (α := ℝ)) →L[ℂ] Lp ℂ 2 (volume (α := ℝ)))
    (hT : ∀ h k : Lp ℂ 2 (volume (α := ℝ)),
      ⟪k, T h⟫_ℂ = ∫ t, φ t * ⟪k, realLogTranslation t h⟫_ℂ)
    (C : ι → Lp ℂ 2 (volume (α := ℝ)) →L[ℂ] Lp ℂ 2 (volume (α := ℝ)))
    (hC : ∀ h, Tendsto (fun i ↦ C i h) l (𝓝 h))
    (P : Lp ℂ 2 (volume (α := ℝ)) →L[ℂ] Lp ℂ 2 (volume (α := ℝ)))
    (hTP : ∀ i, ((C i).comp T).comp P ∈ nuclearEndomorphisms (Lp ℂ 2 (volume (α := ℝ))))
    (κ : ι → ℂ) {L : ℂ}
    (hband : Tendsto (fun i ↦ hilbertTrace ⟨_, hTP i⟩ - κ i) l (𝓝 L)) :
    ∃ hQ : ∀ i, ((C i).comp T).comp
        (P - (innerSL ℂ (realPWLevelPolarVector c)).smulRight (realPWLevelPolarVector c)) ∈
          nuclearEndomorphisms (Lp ℂ 2 (volume (α := ℝ))),
      Tendsto (fun i ↦ hilbertTrace ⟨_, hQ i⟩ - κ i) l
        (𝓝 (L - ∫ t, φ t * (Real.exp (-|t| / 2) : ℂ))) := by
  have hex (i : ι) := hilbertTrace_comp_sub_rankOne ((C i).comp T) P
    (realPWLevelPolarVector c) (hTP i)
  refine ⟨fun i ↦ (hex i).choose, ?_⟩
  have hlim : Tendsto (fun i ↦ ⟪realPWLevelPolarVector c,
      C i (T (realPWLevelPolarVector c))⟫_ℂ) l
      (𝓝 (∫ t, φ t * (Real.exp (-|t| / 2) : ℂ))) := by
    rw [← inner_realPWLevelPolarVector_average c φ T hT]
    exact tendsto_const_nhds.inner (hC _)
  refine (hband.sub hlim).congr fun i ↦ ?_
  rw [(hex i).choose_spec]
  simp only [ContinuousLinearMap.comp_apply]
  ring

/-- Translations act continuously on each vector of `L²(ℝ)`. -/
private theorem continuous_realLogTranslation_apply (h : Lp ℂ 2 (volume (α := ℝ))) :
    Continuous fun t : ℝ ↦ realLogTranslation t h := by
  let g : C(ℝ, C(ℝ, ℝ)) :=
    (ContinuousMap.mk (fun p : ℝ × ℝ ↦ p.2 + p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp (μ := volume (α := ℝ)) (ν := volume (α := ℝ))
    (f := fun _ : ℝ ↦ h) (g := fun t ↦ g t) g.continuous
    (fun t ↦ measurePreserving_add_right (volume (α := ℝ)) t) (by norm_num)

/-- For an integrable `φ` the average of the dilations against `φ` exists as a bounded operator
on `L²(ℝ)`: the hypothesis on `T` in `sLocalTrace_realPWLevel_defect` can be met. -/
theorem exists_realLogTranslation_average (φ : ℝ → ℂ) (hφ : Integrable φ) :
    ∃ T : Lp ℂ 2 (volume (α := ℝ)) →L[ℂ] Lp ℂ 2 (volume (α := ℝ)),
      ∀ h k : Lp ℂ 2 (volume (α := ℝ)),
        ⟪k, T h⟫_ℂ = ∫ t, φ t * ⟪k, realLogTranslation t h⟫_ℂ := by
  have hnorm (t : ℝ) (h : Lp ℂ 2 (volume (α := ℝ))) : ‖realLogTranslation t h‖ = ‖h‖ :=
    (Lp.compMeasurePreservingₗᵢ ℂ (fun u : ℝ ↦ u + t)
      (measurePreserving_add_right volume t)).norm_map h
  have hint (h : Lp ℂ 2 (volume (α := ℝ))) :
      Integrable (fun t ↦ φ t • realLogTranslation t h) :=
    hφ.smul_bdd ‖h‖ (continuous_realLogTranslation_apply h).aestronglyMeasurable
      (ae_of_all _ fun t ↦ (hnorm t h).le)
  let T₀ : Lp ℂ 2 (volume (α := ℝ)) →ₗ[ℂ] Lp ℂ 2 (volume (α := ℝ)) :=
    { toFun := fun h ↦ ∫ t, φ t • realLogTranslation t h
      map_add' := fun h h' ↦ by
        simp only [map_add, smul_add]
        exact integral_add (hint h) (hint h')
      map_smul' := fun a h ↦ by
        simp only [map_smul, RingHom.id_apply]
        rw [← integral_smul]
        refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
        exact smul_comm _ _ _ }
  have hbound (h : Lp ℂ 2 (volume (α := ℝ))) : ‖T₀ h‖ ≤ (∫ t, ‖φ t‖) * ‖h‖ := by
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    rw [← integral_mul_const]
    refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
    change ‖φ t • realLogTranslation t h‖ = ‖φ t‖ * ‖h‖
    rw [norm_smul, hnorm]
  refine ⟨T₀.mkContinuous _ hbound, fun h k ↦ ?_⟩
  change ⟪k, ∫ t, φ t • realLogTranslation t h⟫_ℂ = _
  rw [← integral_inner (hint h) k]
  simp_rw [inner_smul_right]

end Model

end RiemannMasullo
