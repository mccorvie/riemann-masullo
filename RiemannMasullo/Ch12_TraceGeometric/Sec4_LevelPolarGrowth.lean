module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
public import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.AppA_AlgebraicNT.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec3
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# The polar term on the level is not the pair of polar Mellin values

The proof of Theorem 12.5.1.1 (p. 520) uses Theorem 12.4.1.1 with the two polar Mellin values of
the test subtracted, `M(φ)(|·|^(1/2))` and `M(φ)(|·|^(-1/2))`. On `main`'s polar-free level
`sLocalInvariantPWSobolev` the trace asymptotic carries another correction. Pull request #7791
(`sLocalLevel_trace_asymptotic_of_full_comparison`) shows that it is the sum of the diagonal
entries `⟪e i, A (e i)⟫` of a limiting operator `A` over an orthonormal basis `e` of the
complement of the level in the full band. For operators built from the action of the test, `A` is
that action. This file shows that such a correction is never a fixed nonzero multiple of the two
polar Mellin values, for every number field and every finite set of places. It does not depend on
#7791. The two lemmas it shares with #7791 are repeated here under new names.

* `norm_inner_hardySobolevTestAction_le`. A diagonal entry of the action of a test `φ` on the
  local Sobolev space is at most `∫ |φ| (1 + |log N|) ^ (s/2)` times the squared norm of the
  vector, where `N` is the norm on the S-idele class group. The action averages translations, and
  translating by a class of norm `N` stretches the Sobolev norm by at most
  `(1 + |log N|) ^ (s/2)` (`norm_hardySobolevTranslation_le`).
* `exists_levelGrowth_bumpTest`. For every `T` there is a nonnegative test of positive mass that
  vanishes outside the classes with `T < N < e T`. It is a smooth bump in `log N`, and it is
  smooth on the class group by the argument of `Sec5`, whose private lemmas are repeated here
  under new names.
* `norm_sum_inner_levelGrowth_le` and `levelGrowth_polarMellin_ge`. For that test the diagonal
  entries add up to at most its mass times `(2 + log T) ^ (s/2)` times a constant, while the two
  polar Mellin values add up to at least `T ^ (1/2)` times its mass.
* `polarTerm_ne_const_mul_polarMellin`. Since `T ^ (-1/2) (2 + log T) ^ (s/2)` tends to zero, no
  constant `c ≠ 0` makes the sum of the diagonal entries equal `c` times the two polar Mellin
  values for every test. `sLocalLevel_polarTerm_ne_const_mul_polarMellin` states this for vectors
  orthogonal to `main`'s level, where the complement of #7791 lies.

So no normalization makes the level supply the correction that p. 520 subtracts. The Mellin values
here are integrals over the S-idele class group, while the paper's are global. Relating the two is
the missing §12.3 (`ERRATA.md`, M25), and any relation by a fixed constant is covered, since `c` is
arbitrary.

Not shown here: the comparison on the full band, a hypothesis in #7791, and that the paper's
cutoff operators have the action of the test as their limit on the complement of the level.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology InnerProductSpace ContDiff

namespace RiemannMasullo.Isolated

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

/-- `x ^ b (2 (1 + log² x)) ^ c` tends to zero at infinity when `b < 0`. The same statement as
`tendsto_rpow_mul_logWeight` of #7791. -/
theorem levelGrowth_tendsto_rpow_mul_logWeight {b c : ℝ} (hb : b < 0) (hc : 0 ≤ c) :
    Tendsto (fun x : ℝ ↦ x ^ b * (2 * (1 + Real.log x ^ 2)) ^ c) atTop (𝓝 0) := by
  have ho := isLittleO_log_rpow_rpow_atTop (2 * c) (neg_pos.mpr hb)
  have h1 : Tendsto (fun x ↦ Real.log x ^ (2 * c) / x ^ (-b)) atTop (𝓝 0) :=
    ho.tendsto_div_nhds_zero
  have h2 := h1.const_mul (4 ^ c)
  rw [mul_zero] at h2
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_gt_atTop 0] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg (by positivity) _)
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with x hx
    have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
    have hlog : 1 ≤ Real.log x := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hx
    have hl0 : 0 ≤ Real.log x := zero_le_one.trans hlog
    have hbase : 2 * (1 + Real.log x ^ 2) ≤ 4 * Real.log x ^ 2 := by nlinarith
    have hpow : (2 * (1 + Real.log x ^ 2)) ^ c ≤ 4 ^ c * Real.log x ^ (2 * c) := by
      calc (2 * (1 + Real.log x ^ 2)) ^ c ≤ (4 * Real.log x ^ 2) ^ c :=
            Real.rpow_le_rpow (by positivity) hbase hc
        _ = 4 ^ c * Real.log x ^ (2 * c) := by
            rw [Real.mul_rpow (by norm_num) (by positivity), Real.rpow_mul hl0,
              Real.rpow_two]
    have hxb : x ^ b = (x ^ (-b))⁻¹ := by rw [Real.rpow_neg hx0.le, inv_inv]
    calc x ^ b * (2 * (1 + Real.log x ^ 2)) ^ c ≤ x ^ b * (4 ^ c * Real.log x ^ (2 * c)) :=
          mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hx0.le _)
      _ = 4 ^ c * (Real.log x ^ (2 * c) / x ^ (-b)) := by rw [hxb]; ring

section NormSection

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

/-- A continuous section of the S-idelic norm, through one infinite place. The same statement as
`levelDilation_exists_normSection` of #7791, itself a copy of a private lemma of `Sec4`. -/
theorem levelGrowth_exists_normSection :
    ∃ τ : ℝ≥0ˣ →ₜ* (SAdeleRing F S)ˣ, RightInverse τ (sIdeleNorm F S) := by
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace F))
  let s := singlePlaceIdeleNormSection F w
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  refine ⟨⟨p.comp s, hp.comp (singlePlaceIdeleNormSection_continuous F w)⟩, fun t ↦ ?_⟩
  let A := integralAdelesOutside F S
  have hmem (u : ℝ≥0ˣ) : (s u).val ∈ A := by
    simp only [A, integralAdelesOutside, Subring.mem_iInf]
    intro v _
    exact (v.adicCompletionIntegers F).one_mem
  have ht : s t ∈ A.toSubmonoid.units :=
    ⟨hmem t, by
      change ((s t)⁻¹).val ∈ A
      rw [← map_inv]
      exact hmem t⁻¹⟩
  let g := A.toSubmonoid.unitsEquivUnitsType ⟨s t, ht⟩
  exact ((sIdeleNorm_spec F S).1 g).symm.trans (singlePlaceIdeleNormSection_rightInverse F w t)

end NormSection

section GrowthSmooth

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  [LocallyCompactSpace G]

/-- A continuous homomorphism into the reals kills every compact subgroup. -/
theorem levelGrowth_compact_subgroup_le_ker (L : G →* Multiplicative ℝ) (hL : Continuous L)
    {k : Subgroup G} (hk : IsCompact (k : Set G)) : k ≤ L.ker := by
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp ((hk.image
    ((show Continuous (Multiplicative.toAdd : Multiplicative ℝ → ℝ) from continuous_id).comp
      hL)).isBounded)
  intro x hx
  rw [MonoidHom.mem_ker]
  by_contra h
  have hne : (L x).toAdd ≠ 0 := h
  have hxpos : 0 < |(L x).toAdd| := abs_pos.mpr hne
  obtain ⟨n, hn⟩ := exists_nat_gt (C / |(L x).toAdd|)
  have hbound := hC (L (x ^ n)).toAdd ⟨x ^ n, k.pow_mem hx n, rfl⟩
  rw [map_pow, toAdd_pow, nsmul_eq_mul, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Nat.cast_nonneg n)] at hbound
  exact (not_lt_of_ge hbound) ((div_lt_iff₀ hxpos).mp hn)

def levelGrowthCoverZeroHom {m n r : ℕ} {F : Type*} [AddCommGroup F] :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ElementaryLieGroup m n r F where
  toFun := fun xt ↦ elementaryCover xt 0 0
  map_zero' := Prod.ext rfl (Prod.ext (funext fun _ ↦ AddCircle.coe_zero (1 : ℝ)) rfl)
  map_add' x y := Prod.ext rfl
    (Prod.ext (funext fun i ↦ AddCircle.coe_add (1 : ℝ) (x.2 i) (y.2 i)) (zero_add _).symm)

theorem levelGrowthCoverZeroHom_continuous {m n r : ℕ} {F : Type*}
    [AddCommGroup F] [TopologicalSpace F] :
    Continuous (levelGrowthCoverZeroHom (m := m) (n := n) (r := r) (F := F)) :=
  continuous_fst.prodMk
    ((continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd)).prodMk continuous_const)

/-- On each fiber of an elementary group, a smooth function of a real-valued
continuous homomorphism is smooth in the cover coordinates. -/
theorem levelGrowth_contDiff_elementary_realHom {m n r : ℕ} {F : Type*} [AddCommGroup F]
    [TopologicalSpace F] [DiscreteTopology F]
    (ψ : Multiplicative (ElementaryLieGroup m n r F) →* Multiplicative ℝ) (hψ : Continuous ψ)
    {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) (z : Fin r → ℤ) (b : F) {p : ℕ∞} :
    ContDiff ℝ p (fun u ↦ H (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd) := by
  let c := levelGrowthCoverZeroHom (m := m) (n := n) (r := r) (F := F)
  let ℓ : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n) →+ ℝ :=
    (MonoidHom.toAdditive ψ).comp c
  have hℓ : Continuous ℓ := hψ.comp levelGrowthCoverZeroHom_continuous
  have hshift u : c u + elementaryCover 0 z b = elementaryCover u z b := by
    change elementaryCover u 0 0 + elementaryCover 0 z b = elementaryCover u z b
    refine Prod.ext (add_zero _) (Prod.ext (funext fun i ↦ ?_) (Prod.ext (zero_add _) (zero_add _)))
    change ((u.2 i : ℝ) : AddCircle (1 : ℝ)) + (((0 : EuclideanSpace ℝ (Fin n)) i : ℝ) :
      AddCircle (1 : ℝ)) = ((u.2 i : ℝ) : AddCircle (1 : ℝ))
    rw [show ((0 : EuclideanSpace ℝ (Fin n)) i : ℝ) = 0 from rfl, AddCircle.coe_zero, add_zero]
  have heq u : (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd =
      ℓ u + (ψ (Multiplicative.ofAdd (elementaryCover 0 z b))).toAdd := by
    rw [← hshift u, ofAdd_add, map_mul, toAdd_mul]
    rfl
  rw [show (fun u ↦ H (ψ (Multiplicative.ofAdd (elementaryCover u z b))).toAdd) =
      fun u ↦ H (ℓ u + (ψ (Multiplicative.ofAdd (elementaryCover 0 z b))).toAdd) from
    funext fun u ↦ by rw [heq u]]
  have : ContinuousSMul ℝ (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    Prod.continuousSMul
  have hlin : ContDiff ℝ p (fun u ↦ ℓ u) := (ℓ.toRealLinearMap hℓ).contDiff
  exact (hH.of_le (by exact_mod_cast le_top)).comp (hlin.add contDiff_const)

/-- A smooth function of a continuous real-valued homomorphism is Bruhat smooth. -/
theorem levelGrowth_isBruhatSmooth_comp_realHom (L : G →* Multiplicative ℝ) (hL : Continuous L)
    {H : ℝ → ℂ} (hH : ContDiff ℝ (∞) H) :
    IsBruhatSmooth (fun g ↦ H (L g).toAdd) := by
  obtain ⟨k, hk, -, -⟩ := isBruhatContDiff_zero (G := G) 0
  have hker : k ≤ L.ker := levelGrowth_compact_subgroup_le_ker L hL hk.isCompact
  intro p
  refine ⟨k, hk, fun h x ↦ ?_, fun a ha ↦ ?_⟩
  · show H (L (h.val * x)).toAdd = H (L x).toAdd
    rw [map_mul, MonoidHom.mem_ker.mp (hker h.property), one_mul]
  · let N := (OrderDual.ofDual a.val.2).comap a.val.1.subtype
    let q : a.quotient →* Multiplicative ℝ :=
      QuotientGroup.lift N (L.comp a.val.1.subtype) (fun x hx ↦ hker (ha ▸ hx))
    have hq : Continuous q := (QuotientGroup.isQuotientMap_mk N).continuous_iff.mpr
      (hL.comp continuous_subtype_val)
    refine ⟨fun x ↦ H (q x).toAdd, fun x ↦ rfl, fun e z b ↦ ?_⟩
    exact levelGrowth_contDiff_elementary_realHom (q.comp e.equiv.symm.toMulEquiv.toMonoidHom)
      (hq.comp e.equiv.symm.continuous) hH z b

end GrowthSmooth

section Growth

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))} {s : ℝ}

attribute [local instance] instSIdeleQuotientMeasurableSpaceSec1
  instSIdeleQuotientBorelSpaceSec1 instSIdeleQuotientT2Sec1
  instSIdeleQuotientLocallyCompactSec1 instSIdeleQuotientSecondCountableSec1
  instSIdeleQuotientHaarMeasureSec1

local notation "Jₛ" => SIdeleQuotient F S
local notation "μ" => sLocalQuotientTamagawaMeasure F S
local notation "m" => continuousSIdeleQuotientNorm F S
local notation "Nm(" x ")" => (((m x).val : ℝ))
local notation "W" => CompactIntervalSobolev μ (fun x ↦ Real.log (((m x).val : ℝ))) 0 0 s

theorem levelGrowth_norm_pos (x : Jₛ) : 0 < Nm(x) := NNReal.coe_pos.mpr (Units.zero_lt _)

/-- The logarithm of the S-idele quotient norm, as a continuous homomorphism to the reals. -/
def sIdeleQuotientLogNorm : Jₛ →* Multiplicative ℝ where
  toFun x := Multiplicative.ofAdd (Real.log Nm(x))
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, Units.val_mul, NNReal.coe_mul,
      Real.log_mul (levelGrowth_norm_pos x).ne' (levelGrowth_norm_pos y).ne', ofAdd_add]

theorem continuous_sIdeleQuotientLogNorm :
    Continuous (sIdeleQuotientLogNorm (F := F) (S := S)) := by
  have hc : Continuous (fun x : Jₛ ↦ Nm(x)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)
  exact continuous_ofAdd.comp (hc.log fun x ↦ (levelGrowth_norm_pos x).ne')

/-- Paper: Definition D.1.5.3, p. 762, for the S-idele quotient. A smooth compactly supported
function of the logarithm of the norm is a test function on the S-idele quotient. -/
theorem exists_sIdeleQuotientNormTest (g : ℝ → ℂ) (hg : ContDiff ℝ (∞) g)
    (hgc : HasCompactSupport g) :
    ∃ φ : BruhatCompactSupport Jₛ, ∀ x, φ.val x = g (Real.log Nm(x)) := by
  have hs := levelGrowth_isBruhatSmooth_comp_realHom (sIdeleQuotientLogNorm (F := F) (S := S))
    continuous_sIdeleQuotientLogNorm hg
  have hcs :
      HasCompactSupport (fun x : Jₛ ↦ g (sIdeleQuotientLogNorm (F := F) (S := S) x).toAdd) := by
    let E : ℝ → ℝ≥0ˣ := fun t ↦
      Units.mk0 (Real.exp t).toNNReal (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'
    have hE : Continuous E := Units.continuous_iff.mpr
      ⟨continuous_real_toNNReal.comp Real.continuous_exp,
        (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun t ↦
          (Real.toNNReal_pos.mpr (Real.exp_pos t)).ne'⟩
    have hK : IsCompact (E '' tsupport g) := hgc.isCompact.image hE
    refine HasCompactSupport.intro ((isProperMap_sIdeleQuotientNorm F S).isCompact_preimage hK)
      fun x hx ↦ image_eq_zero_of_notMem_tsupport fun hmem ↦ hx ⟨_, hmem, ?_⟩
    apply Units.ext
    change (Real.exp (Real.log Nm(x))).toNNReal = _
    rw [Real.exp_log (levelGrowth_norm_pos x), Real.toNNReal_coe]
    rfl
  exact ⟨(⟨_, (mem_bruhatSmoothSubmodule_iff _).mpr hs, hcs⟩ :
    bruhatCompactSupportSubmodule Jₛ), fun _ ↦ rfl⟩

/-- Paper: Definition 9.3.1.1, p. 419, with (9.3.1.2). A diagonal entry of the test action on
the local Sobolev space is at most `∫ |φ(g)| (1 + |log |g||) ^ (s/2) dg` times the squared norm
of the vector, because the action integrates the translations against the test and a
translation by `g` has norm at most `(1 + |log |g||) ^ (s/2)`. -/
theorem norm_inner_hardySobolevTestAction_le (hs : 0 ≤ s) (φ : BruhatCompactSupport Jₛ)
    (u : W) :
    ‖⟪u, (hardySobolevTestAction μ m 0 0 s le_rfl hs φ : W →L[ℂ] W) u⟫_ℂ‖ ≤
      (∫ x, ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2) ∂μ) * ‖u‖ ^ 2 := by
  let τ := hardySobolevTranslation μ m 0 0 s le_rfl hs
  have hτc : Continuous (fun p : Jₛ × W ↦ τ p.1 p.2) :=
    (exists_hardySobolevTranslation μ m 0 0 s le_rfl hs).choose_spec.2
  have hφc : Continuous φ.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).1 φ.property.1)
  have hi : Integrable φ.val μ := hφc.integrable_of_hasCompactSupport φ.property.2
  let A : W →L[ℂ] W := hardySobolevTestAction μ m 0 0 s le_rfl hs φ
  have hrep : A u = ∫ g, φ.val g • τ g u ∂μ :=
    hardySobolev_eq_integral_translation_of_convolution μ m 0 0 s le_rfl hs hi φ.property.2 A
      (fun v ↦ hardySobolevTestAction_apply μ m 0 0 s le_rfl hs φ v) u
  have hwc : Continuous (fun x : Jₛ ↦ (1 + |Real.log Nm(x)|) ^ (s / 2)) := by
    have hc : Continuous (fun x : Jₛ ↦ Nm(x)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)
    exact (continuous_const.add (hc.log fun x ↦ (levelGrowth_norm_pos x).ne').abs).rpow_const
      fun _ ↦ Or.inr (div_nonneg hs zero_le_two)
  have hτn (g : Jₛ) : ‖τ g‖ ≤ (1 + |Real.log Nm(g)|) ^ (s / 2) := by
    have h := norm_hardySobolevTranslation_le μ m 0 0 s le_rfl hs g
    simpa only [zero_mul, Real.exp_zero, max_self, one_mul] using h
  have hbint' : Integrable (fun x ↦ ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2) * ‖u‖) μ :=
    ((hφc.norm.mul hwc).mul continuous_const).integrable_of_hasCompactSupport
      ((φ.property.2.norm.mul_right).mul_right)
  have hAu : ‖A u‖ ≤ (∫ x, ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2) ∂μ) * ‖u‖ := by
    rw [hrep]
    have hb : (∫ x, ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2) ∂μ) * ‖u‖ =
        ∫ x, ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2) * ‖u‖ ∂μ :=
      (integral_mul_const _ _).symm
    rw [hb]
    have hpt (g : Jₛ) : ‖φ.val g • τ g u‖ ≤ ‖φ.val g‖ * (1 + |Real.log Nm(g)|) ^ (s / 2) * ‖u‖ := by
      have h2 : ‖τ g u‖ ≤ (1 + |Real.log Nm(g)|) ^ (s / 2) * ‖u‖ :=
        ((τ g).le_opNorm u).trans (mul_le_mul_of_nonneg_right (hτn g) (norm_nonneg _))
      calc ‖φ.val g • τ g u‖ ≤ ‖φ.val g‖ * ‖τ g u‖ := norm_smul_le _ _
        _ ≤ ‖φ.val g‖ * ((1 + |Real.log Nm(g)|) ^ (s / 2) * ‖u‖) :=
            mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = _ := by ring
    exact (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (ae_of_all _ fun _ ↦ norm_nonneg _) hbint' (ae_of_all _ hpt))
  change ‖⟪u, A u⟫_ℂ‖ ≤ _
  calc ‖⟪u, A u⟫_ℂ‖ ≤ ‖u‖ * ‖A u‖ := norm_inner_le_norm _ _
    _ ≤ ‖u‖ * ((∫ x, ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2) ∂μ) * ‖u‖) :=
        mul_le_mul_of_nonneg_left hAu (norm_nonneg _)
    _ = _ := by ring

/-- `T ^ (-1/2) (2 + log T) ^ (s/2)` tends to zero. -/
theorem tendsto_rpow_neg_half_mul_two_add_log {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun T : ℝ ↦ T ^ (-(1 / 2 : ℝ)) * (2 + Real.log T) ^ (s / 2)) atTop (𝓝 0) := by
  have h := levelGrowth_tendsto_rpow_mul_logWeight (b := -(1 / 2)) (c := s / 2) (by norm_num)
    (by positivity)
  have h2 := h.const_mul ((3 / 2 : ℝ) ^ (s / 2))
  rw [mul_zero] at h2
  refine squeeze_zero' ?_ ?_ h2
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hl : 0 ≤ Real.log T := Real.log_nonneg hT
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (by linarith) _)
  · filter_upwards [eventually_ge_atTop 1] with T hT
    have hl : 0 ≤ Real.log T := Real.log_nonneg hT
    have hbase : 2 + Real.log T ≤ 3 / 2 * (2 * (1 + Real.log T ^ 2)) := by
      nlinarith [sq_nonneg (Real.log T - 1 / 2)]
    have hpow : (2 + Real.log T) ^ (s / 2) ≤
        (3 / 2) ^ (s / 2) * (2 * (1 + Real.log T ^ 2)) ^ (s / 2) := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]
      exact Real.rpow_le_rpow (by linarith) hbase (by positivity)
    calc T ^ (-(1 / 2 : ℝ)) * (2 + Real.log T) ^ (s / 2)
        ≤ T ^ (-(1 / 2 : ℝ)) * ((3 / 2) ^ (s / 2) * (2 * (1 + Real.log T ^ 2)) ^ (s / 2)) :=
          mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg (by linarith) _)
      _ = _ := by ring

/-- Reconstruction: for every real `T` there is a test on the S-idele class group which is real,
nonnegative and of positive mass, and which vanishes outside the classes whose norm `N` has
`log T < log N < log T + 1`. -/
theorem exists_levelGrowth_bumpTest (T : ℝ) :
    ∃ φ : BruhatCompactSupport Jₛ, ∃ b : Jₛ → ℝ, (∀ x, φ.val x = (b x : ℂ)) ∧
      (∀ x, 0 ≤ b x) ∧ Continuous b ∧ HasCompactSupport b ∧ 0 < ∫ x, b x ∂μ ∧
      ∀ x, b x ≠ 0 → Real.log T < Real.log Nm(x) ∧ Real.log Nm(x) < Real.log T + 1 := by
  let β : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hβr : β.rOut = 1 / 2 := rfl
  have hβi : β.rIn = 1 / 4 := rfl
  let g : ℝ → ℂ := fun y ↦ ((β (y - Real.log T) : ℝ) : ℂ)
  have hg : ContDiff ℝ (∞) g :=
    Complex.ofRealCLM.contDiff.comp (β.contDiff.comp (contDiff_id.sub contDiff_const))
  have hgc : HasCompactSupport g :=
    (β.hasCompactSupport.comp_homeomorph (Homeomorph.subRight (Real.log T))).comp_left
      Complex.ofReal_zero
  obtain ⟨φ, hφ⟩ := exists_sIdeleQuotientNormTest (F := F) (S := S) g hg hgc
  let b : Jₛ → ℝ := fun x ↦ β (Real.log Nm(x) - Real.log T)
  have hφb (x : Jₛ) : φ.val x = (b x : ℂ) := hφ x
  have hb0 (x : Jₛ) : 0 ≤ b x := β.nonneg
  have hNc : Continuous (fun x : Jₛ ↦ Nm(x)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)
  have hlogc : Continuous (fun x : Jₛ ↦ Real.log Nm(x)) :=
    hNc.log fun x ↦ (levelGrowth_norm_pos x).ne'
  have hbc : Continuous b := β.continuous.comp (hlogc.sub continuous_const)
  have hbcs : HasCompactSupport b := by
    refine φ.property.2.norm.mono fun x hx ↦ ?_
    simp only [Function.mem_support, ne_eq, hφb, Complex.norm_real, Real.norm_eq_abs,
      abs_eq_zero] at hx ⊢
    exact hx
  have hsupp (x : Jₛ) (hx : b x ≠ 0) :
      Real.log T < Real.log Nm(x) ∧ Real.log Nm(x) < Real.log T + 1 := by
    have hmem : Real.log Nm(x) - Real.log T ∈ Function.support β := hx
    rw [β.support_eq, Metric.mem_ball, Real.dist_eq, hβr] at hmem
    obtain ⟨h1, h2⟩ := abs_lt.mp hmem
    constructor <;> linarith
  obtain ⟨τ, hτ⟩ := levelGrowth_exists_normSection (F := F) (S := S)
  let t₀ : ℝ≥0ˣ := Units.mk0 (Real.exp (Real.log T + 1 / 2)).toNNReal
    (Real.toNNReal_pos.mpr (Real.exp_pos _)).ne'
  let x₀ : Jₛ := QuotientGroup.mk (τ t₀)
  have hx₀ : Real.log Nm(x₀) = Real.log T + 1 / 2 := by
    have h1 : (m x₀) = t₀ := (sIdeleQuotientNorm_mk F S (τ t₀)).trans (hτ t₀)
    rw [h1]
    simp only [t₀, Units.val_mk0, Real.coe_toNNReal _ (Real.exp_pos _).le, Real.log_exp]
  have hbx₀ : b x₀ = 1 := by
    apply β.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq, hx₀, hβi,
      show Real.log T + 1 / 2 - Real.log T - 1 / 2 = 0 by ring, abs_zero]
    norm_num
  have hbint : Integrable b μ := hbc.integrable_of_hasCompactSupport hbcs
  have hI : 0 < ∫ x, b x ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hb0 hbint]
    have hU : IsOpen {x : Jₛ | 0 < b x} := isOpen_lt continuous_const hbc
    have hx₀U : x₀ ∈ {x : Jₛ | 0 < b x} := by
      change 0 < b x₀
      rw [hbx₀]
      exact one_pos
    exact (hU.measure_pos μ ⟨x₀, hx₀U⟩).trans_le
      (measure_mono fun x hx ↦ (show 0 < b x from hx).ne')
  exact ⟨φ, b, hφb, hb0, hbc, hbcs, hI, hsupp⟩

/-- Reconstruction: for a test `φ = b` concentrated where `log T < log N < log T + 1`, the sum of
the diagonal entries of its action over a finite family `e` is at most
`(∫ b) (2 + log T) ^ (s/2) ∑ ‖e i‖²`. -/
theorem norm_sum_inner_levelGrowth_le (hs : 0 ≤ s) {ι : Type*} [Fintype ι] (e : ι → W)
    {T : ℝ} (hT1 : 1 ≤ T) (φ : BruhatCompactSupport Jₛ) (b : Jₛ → ℝ)
    (hφb : ∀ x, φ.val x = (b x : ℂ)) (hb0 : ∀ x, 0 ≤ b x) (hbc : Continuous b)
    (hbcs : HasCompactSupport b)
    (hsupp : ∀ x, b x ≠ 0 → Real.log T < Real.log Nm(x) ∧ Real.log Nm(x) < Real.log T + 1) :
    ‖∑ i, ⟪e i, (hardySobolevTestAction μ m 0 0 s le_rfl hs φ : W →L[ℂ] W) (e i)⟫_ℂ‖ ≤
      (∫ x, b x ∂μ) * (2 + Real.log T) ^ (s / 2) * ∑ i, ‖e i‖ ^ 2 := by
  have hlT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hNc : Continuous (fun x : Jₛ ↦ Nm(x)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)
  have hlogc : Continuous (fun x : Jₛ ↦ Real.log Nm(x)) :=
    hNc.log fun x ↦ (levelGrowth_norm_pos x).ne'
  have hnorm (x : Jₛ) : ‖φ.val x‖ = b x := by
    rw [hφb, Complex.norm_real, Real.norm_of_nonneg (hb0 x)]
  have hw (x : Jₛ) : ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2) ≤
      b x * (2 + Real.log T) ^ (s / 2) := by
    rw [hnorm]
    by_cases hx : b x = 0
    · rw [hx, zero_mul, zero_mul]
    · obtain ⟨h1, h2⟩ := hsupp x hx
      have habs : |Real.log Nm(x)| < Real.log T + 1 := by
        rw [abs_of_nonneg (by linarith)]
        exact h2
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (by linarith)
        (by positivity)) (hb0 x)
  have hbint : Integrable b μ := hbc.integrable_of_hasCompactSupport hbcs
  have hwc : Continuous (fun x : Jₛ ↦ (1 + |Real.log Nm(x)|) ^ (s / 2)) :=
    (continuous_const.add hlogc.abs).rpow_const fun _ ↦ Or.inr (div_nonneg hs zero_le_two)
  have hwint : Integrable (fun x ↦ ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2)) μ := by
    have heq : (fun x ↦ ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2)) =
        fun x ↦ b x * (1 + |Real.log Nm(x)|) ^ (s / 2) := funext fun x ↦ by rw [hnorm]
    rw [heq]
    exact (hbc.mul hwc).integrable_of_hasCompactSupport hbcs.mul_right
  have hwI : (∫ x, ‖φ.val x‖ * (1 + |Real.log Nm(x)|) ^ (s / 2) ∂μ) ≤
      (∫ x, b x ∂μ) * (2 + Real.log T) ^ (s / 2) := by
    rw [← integral_mul_const]
    exact integral_mono hwint (hbint.mul_const _) hw
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum fun i _ ↦ ?_).trans_eq
    (Finset.mul_sum _ _ _).symm)
  exact (norm_inner_hardySobolevTestAction_le hs φ (e i)).trans
    (mul_le_mul_of_nonneg_right hwI (by positivity))

/-- Reconstruction: for a nonnegative `b` vanishing where `log N ≤ log T`, the two polar Mellin
values of `b` add up to at least `T ^ (1/2) ∫ b`. -/
theorem levelGrowth_polarMellin_ge {T : ℝ} (hT1 : 1 ≤ T) (b : Jₛ → ℝ) (hb0 : ∀ x, 0 ≤ b x)
    (hbc : Continuous b) (hbcs : HasCompactSupport b)
    (hsupp : ∀ x, b x ≠ 0 → Real.log T < Real.log Nm(x)) :
    T ^ (1 / 2 : ℝ) * (∫ x, b x ∂μ) ≤
      (∫ x, b x * Nm(x) ^ (1 / 2 : ℝ) ∂μ) + ∫ x, b x * Nm(x) ^ (-(1 / 2) : ℝ) ∂μ := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  have hNc : Continuous (fun x : Jₛ ↦ Nm(x)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)
  have hbint : Integrable b μ := hbc.integrable_of_hasCompactSupport hbcs
  have hrint (r : ℝ) : Integrable (fun x ↦ b x * Nm(x) ^ r) μ :=
    (hbc.mul (hNc.rpow_const fun x ↦ Or.inl (levelGrowth_norm_pos x).ne')
      ).integrable_of_hasCompactSupport hbcs.mul_right
  have h1 : T ^ (1 / 2 : ℝ) * (∫ x, b x ∂μ) ≤ ∫ x, b x * Nm(x) ^ (1 / 2 : ℝ) ∂μ := by
    rw [← integral_const_mul]
    refine integral_mono (hbint.const_mul _) (hrint _) fun x ↦ ?_
    by_cases hx : b x = 0
    · simp [hx]
    · rw [mul_comm]
      refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hT0.le ?_ (by norm_num)) (hb0 x)
      have h := hsupp x hx
      rw [Real.log_lt_log_iff hT0 (levelGrowth_norm_pos x)] at h
      exact h.le
  have h2 : 0 ≤ ∫ x, b x * Nm(x) ^ (-(1 / 2) : ℝ) ∂μ :=
    integral_nonneg fun x ↦ mul_nonneg (hb0 x) (Real.rpow_nonneg (levelGrowth_norm_pos x).le _)
  linarith

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and the proof of Theorem 12.5.1.1, p. 520, for every
number field and every finite set of places.
Reconstruction: a sum of diagonal entries of the test action on the local Sobolev space, over
any finite family of vectors, is never a fixed nonzero multiple `c` of the two polar Mellin values
`∫ φ |·|^(1/2) + ∫ φ |·|^(-1/2)` for every test `φ`. A test concentrated at norm about `T` has
diagonal entries of size at most a power of `log T` times its mass, while its polar Mellin values
are at least `T ^ (1/2)` times its mass. By `sLocalLevel_trace_asymptotic_of_full_comparison` and
`tendsto_inner_mul_mul` of #7791 the polar term of the level is such a sum, over an orthonormal
basis of the polar complement, so the level never yields the form that p. 520 subtracts, whatever
the normalization `c` relating the S-local and the global Mellin values. -/
theorem polarTerm_ne_const_mul_polarMellin (hs : 0 ≤ s) {ι : Type*} [Fintype ι] (e : ι → W)
    {c : ℂ} (hc : c ≠ 0) :
    ∃ φ : BruhatCompactSupport Jₛ,
      ∑ i, ⟪e i, (hardySobolevTestAction μ m 0 0 s le_rfl hs φ : W →L[ℂ] W) (e i)⟫_ℂ ≠
        c * ((∫ x, φ.val x * ((Nm(x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ∂μ) +
          ∫ x, φ.val x * ((Nm(x) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) ∂μ) := by
  by_contra! hall
  have hlim := (tendsto_rpow_neg_half_mul_two_add_log hs).const_mul (∑ i, ‖e i‖ ^ 2)
  rw [mul_zero] at hlim
  obtain ⟨T, hTsmall, hT1⟩ := ((hlim.eventually (gt_mem_nhds (norm_pos_iff.mpr hc))).and
    (eventually_ge_atTop (1 : ℝ))).exists
  have hT0 : 0 < T := zero_lt_one.trans_le hT1
  obtain ⟨φ, b, hφb, hb0, hbc, hbcs, hI, hsupp⟩ :=
    exists_levelGrowth_bumpTest (F := F) (S := S) T
  have hQ := norm_sum_inner_levelGrowth_le hs e hT1 φ b hφb hb0 hbc hbcs hsupp
  have hR := levelGrowth_polarMellin_ge hT1 b hb0 hbc hbcs fun x hx ↦ (hsupp x hx).1
  have hLeq : (∫ x, φ.val x * ((Nm(x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ∂μ) +
      ∫ x, φ.val x * ((Nm(x) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) ∂μ =
        (((∫ x, b x * Nm(x) ^ (1 / 2 : ℝ) ∂μ) +
          ∫ x, b x * Nm(x) ^ (-(1 / 2) : ℝ) ∂μ : ℝ) : ℂ) := by
    simp only [hφb, ← Complex.ofReal_mul, integral_complex_ofReal, Complex.ofReal_add]
  have heq := (hall φ).trans (congrArg (c * ·) hLeq)
  have hRpos : 0 ≤ (∫ x, b x * Nm(x) ^ (1 / 2 : ℝ) ∂μ) +
      ∫ x, b x * Nm(x) ^ (-(1 / 2) : ℝ) ∂μ :=
    le_trans (mul_nonneg (Real.rpow_nonneg hT0.le _) hI.le) hR
  have hnorm : ‖c‖ * ((∫ x, b x * Nm(x) ^ (1 / 2 : ℝ) ∂μ) +
      ∫ x, b x * Nm(x) ^ (-(1 / 2) : ℝ) ∂μ) ≤
        (∫ x, b x ∂μ) * (2 + Real.log T) ^ (s / 2) * ∑ i, ‖e i‖ ^ 2 := by
    calc ‖c‖ * ((∫ x, b x * Nm(x) ^ (1 / 2 : ℝ) ∂μ) + ∫ x, b x * Nm(x) ^ (-(1 / 2) : ℝ) ∂μ)
        = ‖c * ((((∫ x, b x * Nm(x) ^ (1 / 2 : ℝ) ∂μ) +
            ∫ x, b x * Nm(x) ^ (-(1 / 2) : ℝ) ∂μ : ℝ)) : ℂ)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hRpos]
      _ = _ := congrArg norm heq.symm
      _ ≤ _ := hQ
  have hTh : 0 < T ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hT0 _
  have h3 : ‖c‖ * T ^ (1 / 2 : ℝ) ≤ (2 + Real.log T) ^ (s / 2) * ∑ i, ‖e i‖ ^ 2 := by
    refine le_of_mul_le_mul_left ?_ hI
    calc (∫ x, b x ∂μ) * (‖c‖ * T ^ (1 / 2 : ℝ))
        = ‖c‖ * (T ^ (1 / 2 : ℝ) * ∫ x, b x ∂μ) := by ring
      _ ≤ ‖c‖ * ((∫ x, b x * Nm(x) ^ (1 / 2 : ℝ) ∂μ) +
          ∫ x, b x * Nm(x) ^ (-(1 / 2) : ℝ) ∂μ) :=
          mul_le_mul_of_nonneg_left hR (norm_nonneg _)
      _ ≤ _ := hnorm
      _ = _ := by ring
  have hfin : ‖c‖ ≤ (∑ i, ‖e i‖ ^ 2) * (T ^ (-(1 / 2 : ℝ)) * (2 + Real.log T) ^ (s / 2)) := by
    have hrw : (∑ i, ‖e i‖ ^ 2) * (T ^ (-(1 / 2 : ℝ)) * (2 + Real.log T) ^ (s / 2)) =
        (2 + Real.log T) ^ (s / 2) * (∑ i, ‖e i‖ ^ 2) / T ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_neg hT0.le, div_eq_mul_inv]
      ring
    rw [hrw, le_div_iff₀ hTh]
    exact h3
  exact absurd hTsmall (not_lt.mpr hfin)

/-- Paper: Theorem 12.4.1.1, pp. 514–519, and the proof of Theorem 12.5.1.1, p. 520, for every
number field, every finite set of places, every twist, Sobolev index, norm-one character and
bandwidth.
Reconstruction: `polarTerm_ne_const_mul_polarMellin` for a finite family `e` of vectors orthogonal
to `main`'s polar-free level `sLocalInvariantPWSobolev`, which contains every orthonormal basis of
the complement of the level in the full band of #7791. With `A` the action of a test, the sum
`∑ ⟪e i, A (e i)⟫` is not a fixed nonzero multiple of the two polar Mellin values of the test, for
some test. -/
theorem sLocalLevel_polarTerm_ne_const_mul_polarMellin (hs : 0 ≤ s) {a : ℝ} (ha : 0 < a)
    (χ : PontryaginDual (sIdeleQuotientNorm F S).ker) (Λ : ℝ) {ι : Type*} [Fintype ι]
    (e : ι → ↥(sLocalInvariantPWSobolev (F := F) (S := S) hs ha χ Λ)ᗮ) {c : ℂ} (hc : c ≠ 0) :
    ∃ φ : BruhatCompactSupport Jₛ,
      ∑ i, ⟪((e i).1 : W),
          (hardySobolevTestAction μ m 0 0 s le_rfl hs φ : W →L[ℂ] W) ((e i).1 : W)⟫_ℂ ≠
        c * ((∫ x, φ.val x * ((Nm(x) ^ (1 / 2 : ℝ) : ℝ) : ℂ) ∂μ) +
          ∫ x, φ.val x * ((Nm(x) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) ∂μ) :=
  polarTerm_ne_const_mul_polarMellin hs (fun i ↦ ((e i).1 : W)) hc

end Growth

end RiemannMasullo.Isolated
