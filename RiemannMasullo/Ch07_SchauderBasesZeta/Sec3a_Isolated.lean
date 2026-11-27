module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a

import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1b
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.AppC_LCTVS.Sec1
import RiemannMasullo.AppC_LCTVS.Sec2a
import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
import RiemannMasullo.AppB_AnalyticNT.Sec3
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-! # Necessity of Laurent and outside-prime Euler bounds for the polar orbital basis

This isolated module records the exact converse of `sLocalPolarOrbital_bases_of_laurent_bounds`
and its consequence for the outside-prime Euler factors appearing in Theorem 7.3.3.4 (#7336).

Main results:
* `sLocalPolarOrbital_laurent_bounds_of_basis`: if any enumeration of the primary polar
  orbital system forms a Schauder basis of the primary quotient `Q(p, ω)` (without assuming
  absoluteness or unconditionality), then the polynomial Laurent-ratio bound
  `‖rhoCoeff(c, r)‖ ≤ C * (1 + ‖s‖)^d * ‖rhoCoeff(c, 0)‖` holds on every unitary chart.
* `sLocalPolarOrbital_basis_iff_laurent_bounds`: exact equivalence between existence of a
  polar orbital Schauder basis on `Q(p, ω)` and the polynomial Laurent-ratio bound.
* `sLocalPolarOrbital_basis_isAbsolute_and_dual_isUnconditional`: any polar orbital Schauder
  basis on `Q(p, ω)` is automatically absolute (in every enumeration) and its dual is
  automatically unconditional.
* `sLocalRho_firstLaurentRatio_eq_logDeriv_add_eulerSum`: exact logarithmic-derivative
  decomposition of `rhoCoeff(c, 1) / rhoCoeff(c, 0)` into the cleared germ derivative
  `G'(0) / G(0)` plus the weighted finite Euler sum `∑ v : S, log(N v) * b(c, v)`.
* `sLocalRho_firstLaurentRatio_sub_eulerSum_poly_bound`: unconditional polynomial bound on
  the cleared archimedean/pole error `rhoCoeff(c, 1) / rhoCoeff(c, 0) - ∑ v, log(N v) * b(c, v)`.
* `sLocalPolarOrbital_outsideEulerSum_bound_of_basis`: existence of a polar Schauder basis
  on `Q(p, ω)` forces a polynomial upper bound on the weighted outside-place Euler sum at
  every repeated primary pole.
* `sLocalPolarOrbital_singleOutsideEuler_bound_of_basis` and
  `sLocalPolarOrbital_singleOutsideDistance_bound_of_basis`: whenever a single outside place
  `v₀ ∉ Sₚ(p)` is isolated (or all other outside places are polynomially bounded), existence
  of a polar Schauder basis on `Q(p, ω)` forces the individual outside-place Euler bound and
  uniformizer distance lower bound `1 ≤ C * (1 + ‖s‖)^d * ‖1 - z_{v₀}(c)‖` of #7336.
-/

@[expose] public noncomputable section

open Asymptotics Bornology Filter Function IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo.Isolated

set_option quotPrecheck false
set_option maxHeartbeats 600000

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "dualₛ" => dualQuasiCharacter (G := Jₛ) mₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chart(" χ ")" => twistₛ ((circleToComplex).comp (χ))
local notation "restrict₁(" χ ")" => ((χ : PontryaginDual Jₛ).comp
  (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ))
local notation "Θₛ(" ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "PicTrivial" => Subsingleton (CommRing.Pic ((S : Set V).integer F))
local notation "Sₚ(" p ")" => sLocalPrimaryPlaces (F := F) S p
local notation "hₚ(" p ")" => sLocalPrimaryPlaces_subset (F := F) (S := S) p
local notation "Idx(" p ", " ω ")" => SLocalOrbitalIndex (F := F) (S := S) (Sₚ(p)) ω
local notation "Rₚ(" p ", " ω ")" => sLocalPrimaryOrbitalSubmodule (F := F) (S := S) p ω
local notation "Q(" p ", " ω ")" => SLocalPrimaryOrbitalQuotient (F := F) (S := S) p ω
local notation "π(" p ", " ω ")" => (Rₚ(p, ω)).mkQ
local notation "fourierZeta(" c ")" => fun (f : ℬₛ) (z : ℂ) ↦
  sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (twistₛ (c) z))
local notation "period(" v ")" =>
  2 * Real.pi / Real.log (((v : S).val.asIdeal.absNorm : ℕ) : ℝ)
local notation "uniformizerNorm(" v ", " u ")" =>
  (‖(↑(u) : (v : S).val.adicCompletion F)‖ = ((v : S).val.asIdeal.absNorm : ℝ)⁻¹)
local notation "phase(" χ ", " v ", " u ", " t ")" =>
  (t ∈ Ico 0 (period(v)) ∧
    sLocalFiniteRestriction v (chart(χ) (-(t : ℂ) * Complex.I)) u = 1)
local notation "lattice(" χ ", " v ", " t ", " n ")" =>
  chart(χ) (((((n : ℤ) : ℝ) * period(v) - t : ℝ) : ℂ) * Complex.I)
local notation "rhoCoeff(" c ", " r ")" =>
  complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ (c) z) *
    z ^ ((sLocalRhoPoleOrder (c) : ℤ) - ((r : ℕ) : ℤ) - 1)) 0

section PureHelpers

/-- If a nonnegative sequence on `ℤ` multiplied by every rapidly decreasing sequence tends
to zero along the cofinite filter, then it has polynomial growth. -/
private theorem poly_bound_of_rapidDecay_mul_tendsto_zero (b : ℤ → ℝ) (hb : ∀ n, 0 ≤ b n)
    (htend : ∀ a : ℤ → ℂ,
      (∀ N : ℕ, ∃ B : ℝ, ∀ n : ℤ, (1 + |(n : ℝ)|) ^ N * ‖a n‖ ≤ B) →
      Tendsto (fun n : ℤ ↦ b n * ‖a n‖) cofinite (𝓝 0)) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ n : ℤ, b n ≤ C * (1 + |(n : ℝ)|) ^ d := by
  classical
  by_contra hnot
  push Not at hnot
  have hstep : ∀ (k : ℕ) (S₀ : Finset ℤ),
      ∃ m : ℤ, m ∉ S₀ ∧ (1 + |(m : ℝ)|) ^ k ≤ b m := by
    intro k S₀
    let C : ℝ := 1 + ∑ n ∈ S₀, b n
    have hC : 0 < C := by
      dsimp [C]
      linarith [Finset.sum_nonneg (fun n (_ : n ∈ S₀) ↦ hb n)]
    have hC1 : 1 ≤ C := by
      dsimp [C]
      linarith [Finset.sum_nonneg (fun n (_ : n ∈ S₀) ↦ hb n)]
    obtain ⟨m, hm⟩ := hnot k C hC
    refine ⟨m, ?_, ?_⟩
    · intro hmS
      have hbm : b m ≤ C := by
        dsimp [C]
        linarith [Finset.single_le_sum (fun n (_ : n ∈ S₀) ↦ hb n) hmS]
      have hpow : 1 ≤ (1 + |(m : ℝ)|) ^ k :=
        one_le_pow₀ (le_add_of_nonneg_right (abs_nonneg _))
      nlinarith
    · have hpow : 0 ≤ (1 + |(m : ℝ)|) ^ k := by positivity
      nlinarith
  let seq : ℕ → Σ' (S₀ : Finset ℤ), ℤ := Nat.rec
    ⟨∅, (hstep 0 ∅).choose⟩
    (fun k prev ↦
      let S₁ := insert prev.2 prev.1
      ⟨S₁, (hstep (k + 1) S₁).choose⟩)
  let seqIdx (k : ℕ) : ℤ := (seq k).2
  have hseq_mem (k : ℕ) : ∀ j < k, seqIdx j ∈ (seq k).1 := by
    induction k with
    | zero => intro j hj; omega
    | succ k ih =>
      intro j hj
      change seqIdx j ∈ insert (seq k).2 (seq k).1
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hlt | rfl
      · exact Finset.mem_insert_of_mem (ih j hlt)
      · exact Finset.mem_insert_self _ _
  have hseq_notMem (k : ℕ) : seqIdx k ∉ (seq k).1 := by
    cases k with
    | zero => exact (hstep 0 ∅).choose_spec.1
    | succ k => exact (hstep (k + 1) (insert (seq k).2 (seq k).1)).choose_spec.1
  have hseq_bound (k : ℕ) : (1 + |(seqIdx k : ℝ)|) ^ k ≤ b (seqIdx k) := by
    cases k with
    | zero => exact (hstep 0 ∅).choose_spec.2
    | succ k => exact (hstep (k + 1) (insert (seq k).2 (seq k).1)).choose_spec.2
  have hinj : Injective seqIdx := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact hseq_notMem j (hij ▸ hseq_mem j i hlt)
    · exact hseq_notMem i (hij.symm ▸ hseq_mem i j hgt)
  let a (m : ℤ) : ℂ :=
    if h : ∃ k : ℕ, seqIdx k = m then
      ((((1 + |(m : ℝ)|) ^ h.choose : ℝ)⁻¹ : ℝ) : ℂ)
    else 0
  have ha_val (k : ℕ) : ‖a (seqIdx k)‖ = ((1 + |(seqIdx k : ℝ)|) ^ k)⁻¹ := by
    have hex : ∃ j : ℕ, seqIdx j = seqIdx k := ⟨k, rfl⟩
    have hch : hex.choose = k := hinj hex.choose_spec
    simp only [a, dite_eq_left hex, hch, Complex.norm_real]
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg (by positivity) _))]
  have hrapid : ∀ N : ℕ, ∃ B : ℝ, ∀ m : ℤ, (1 + |(m : ℝ)|) ^ N * ‖a m‖ ≤ B := by
    intro N
    let B : ℝ := 1 + ∑ k ∈ Finset.range N, (1 + |(seqIdx k : ℝ)|) ^ N * ‖a (seqIdx k)‖
    refine ⟨B, fun m ↦ ?_⟩
    by_cases hex : ∃ k : ℕ, seqIdx k = m
    · obtain ⟨k, rfl⟩ := hex
      by_cases hk : k < N
      · have hle := Finset.single_le_sum
          (fun j (_ : j ∈ Finset.range N) ↦
            show 0 ≤ (1 + |(seqIdx j : ℝ)|) ^ N * ‖a (seqIdx j)‖ by positivity)
          (Finset.mem_range.mpr hk)
        dsimp [B]
        linarith
      · rw [ha_val k]
        have hbase : 1 ≤ 1 + |(seqIdx k : ℝ)| := le_add_of_nonneg_right (abs_nonneg _)
        have hpow : (1 + |(seqIdx k : ℝ)|) ^ N ≤ (1 + |(seqIdx k : ℝ)|) ^ k :=
          pow_le_pow_right₀ hbase (Nat.le_of_not_lt hk)
        have hpos : 0 < (1 + |(seqIdx k : ℝ)|) ^ k := by positivity
        have hle1 : (1 + |(seqIdx k : ℝ)|) ^ N * ((1 + |(seqIdx k : ℝ)|) ^ k)⁻¹ ≤ 1 := by
          rw [← div_eq_mul_inv, div_le_one hpos]
          exact hpow
        have hsum_nn : 0 ≤ ∑ j ∈ Finset.range N, (1 + |(seqIdx j : ℝ)|) ^ N * ‖a (seqIdx j)‖ :=
          Finset.sum_nonneg (fun j _ ↦ by positivity)
        dsimp [B]
        linarith
    · simp only [a, dite_eq_right hex, norm_zero, mul_zero]
      have hsum_nn : 0 ≤ ∑ j ∈ Finset.range N, (1 + |(seqIdx j : ℝ)|) ^ N * ‖a (seqIdx j)‖ :=
        Finset.sum_nonneg (fun j _ ↦ by positivity)
      dsimp [B]
      linarith
  have hlim : Tendsto (fun k : ℕ ↦ b (seqIdx k) * ‖a (seqIdx k)‖) atTop (𝓝 0) :=
    (htend a hrapid).comp (hinj.tendsto_cofinite.mono_left Nat.cofinite_eq_atTop.ge)
  obtain ⟨K, hK⟩ := (Metric.tendsto_atTop.mp hlim) (1 / 2) (by norm_num)
  have hlt := hK K le_rfl
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (hb _) (norm_nonneg _))] at hlt
  have hge1 : 1 ≤ b (seqIdx K) * ‖a (seqIdx K)‖ := by
    rw [ha_val K, ← div_eq_mul_inv, one_le_div (by positivity)]
    exact hseq_bound K
  linarith

/-- The terms of a conditionally convergent series in a topological additive group
tend to zero. -/
private theorem hasSum_conditional_tendsto_zero {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] {f : ℕ → E} {u : E}
    (hf : HasSum f u (SummationFilter.conditional ℕ)) :
    Tendsto f atTop (𝓝 0) := by
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at hf
  have hsum : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range n, f k) atTop (𝓝 u) := hf
  have hshift : Tendsto (fun n : ℕ ↦ ∑ k ∈ Finset.range (n + 1), f k) atTop (𝓝 u) :=
    hsum.comp (tendsto_add_atTop_nat 1)
  have hsub : Tendsto (fun n : ℕ ↦ (∑ k ∈ Finset.range (n + 1), f k) -
      (∑ k ∈ Finset.range n, f k)) atTop (𝓝 (u - u)) :=
    hshift.sub hsum
  simpa only [Finset.sum_range_succ, add_sub_cancel_left, sub_self] using hsub

/-- In a complete polynormable complex vector space, a sequence whose seminorm series
converge for every continuous seminorm is unconditionally summable. -/
private theorem summable_of_seminorm_summable {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [PolynormableSpace ℂ E] [CompleteSpace E]
    {ι : Type*} (u : ι → E)
    (hu : ∀ q : Seminorm ℂ E, Continuous q → Summable (fun n ↦ q (u n))) :
    Summable u := by
  apply summable_iff_cauchySeq_finset.mpr
  rw [CauchySeq, cauchy_map_iff', uniformity_eq_comap_nhds_zero, Filter.tendsto_comap_iff,
    (PolynormableSpace.withSeminorms ℂ E).tendsto_nhds]
  intro q ε hε
  let p : Seminorm ℂ E := q.val
  have hp : Continuous p := q.property
  let j : E →ₗ[ℂ] LocalBanach p :=
    UniformSpace.Completion.toComplL.toLinearMap.comp LinearMap.id
  have hj (x : E) : ‖j x‖ = p x := localBanach_norm_coe p x
  have hsum : Summable (fun n ↦ j (u n)) :=
    Summable.of_norm (by simpa only [hj] using hu p hp)
  have ht := cauchy_map_iff'.mp (summable_iff_cauchySeq_finset.mp hsum)
  rw [tendsto_uniformity_iff_dist_tendsto_zero, Metric.tendsto_nhds] at ht
  filter_upwards [ht ε hε] with z hz
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg, dist_eq_norm', ← map_sum, ← map_sum,
    ← map_sub, hj] at hz
  simpa only [sub_zero, Function.comp_apply] using hz

/-- Inverting a finite lower-triangular Laurent convolution against a coordinate vector yields
the reciprocal leading coefficient times the factorial on the diagonal. -/
private theorem triangular_fourier_of_polar_biorthogonal (a P D : ℕ → ℂ) (m r : ℕ)
    (ha : a 0 ≠ 0) (hr : r < m)
    (hrow : ∀ k < m, P k = ∑ l ∈ Finset.range (k + 1), a l * (D (k - l) / ((k - l).factorial : ℂ)))
    (horth : ∀ k ≤ r, P k = if k = r then 1 else 0) :
    D r = (r.factorial : ℂ) / a 0 := by
  have hlt : ∀ k < r, D k = 0 := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hkr
      have hk0 : 0 ∈ Finset.range (k + 1) := by simp
      have hrest : ∑ l ∈ (Finset.range (k + 1)).erase 0,
          a l * (D (k - l) / ((k - l).factorial : ℂ)) = 0 := by
        refine Finset.sum_eq_zero fun l hl ↦ ?_
        obtain ⟨hl0, hlk⟩ := Finset.mem_erase.mp hl
        have hlk' := Finset.mem_range.mp hlk
        rw [ih (k - l) (by omega) (by omega), zero_div, mul_zero]
      have hPk := hrow k (hkr.trans hr)
      rw [horth k hkr.le, ite_eq_right hkr.ne, ← Finset.sum_erase_add _ _ hk0, hrest, zero_add,
        Nat.sub_zero] at hPk
      have hdiv : D k / (k.factorial : ℂ) = 0 := (mul_eq_zero.mp hPk.symm).resolve_left ha
      exact (div_eq_zero_iff.mp hdiv).resolve_right (by exact_mod_cast k.factorial_ne_zero)
  have hr0 : 0 ∈ Finset.range (r + 1) := by simp
  have hrest : ∑ l ∈ (Finset.range (r + 1)).erase 0,
      a l * (D (r - l) / ((r - l).factorial : ℂ)) = 0 := by
    refine Finset.sum_eq_zero fun l hl ↦ ?_
    obtain ⟨hl0, hlr⟩ := Finset.mem_erase.mp hl
    have hlr' := Finset.mem_range.mp hlr
    rw [hlt (r - l) (by omega), zero_div, mul_zero]
  have hPr := hrow r hr
  rw [horth r le_rfl, ite_eq_left rfl, ← Finset.sum_erase_add _ _ hr0, hrest, zero_add,
    Nat.sub_zero] at hPr
  have hfac : (r.factorial : ℂ) ≠ 0 := by exact_mod_cast r.factorial_ne_zero
  rw [eq_div_iff ha]
  have hmul := congrArg (· * (r.factorial : ℂ)) hPr
  rw [one_mul, mul_assoc, div_mul_cancel₀ _ hfac, mul_comm] at hmul
  exact hmul.symm

end PureHelpers

section PolarLaurentRelation

/-- The unitary norm-twist chart is injective in the complex exponent. -/
private theorem chart_injective (χ : PontryaginDual Jₛ) :
    Injective (fun s : ℂ ↦ chart(χ) s) := by
  intro s₁ s₂ h
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  have hpow (t : ℝ≥0ˣ) : ((t.val : ℝ) : ℂ) ^ s₁ = ((t.val : ℝ) : ℂ) ^ s₂ := by
    have hval := DFunLike.congr_fun h (τ t)
    change (χ (τ t) : ℂ) * (((mₛ (τ t)).val : ℝ) : ℂ) ^ s₁ =
      (χ (τ t) : ℂ) * (((mₛ (τ t)).val : ℝ) : ℂ) ^ s₂ at hval
    rw [hτ] at hval
    exact mul_left_cancel₀ (Circle.coe_ne_zero _) hval
  let f : QuasiCharacter ℝ≥0ˣ :=
    ⟨{ toFun := fun t ↦ ((t.val : ℝ) : ℂ) ^ s₁
       map_one' := by simp
       map_mul' := fun a b ↦ by
         change (((a.val : ℝ) * (b.val : ℝ) : ℝ) : ℂ) ^ s₁ = _
         rw [Complex.ofReal_mul]
         exact Complex.mul_cpow_ofReal_nonneg (NNReal.coe_nonneg a.val) (NNReal.coe_nonneg b.val) s₁ },
      Continuous.cpow (Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp Units.continuous_val))
        continuous_const
        (fun t ↦ Or.inl (by
          rw [Complex.ofReal_re]
          exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr t.ne_zero)))⟩
  exact (existsUnique_complexPower f).unique (fun _ ↦ rfl) (fun t ↦ hpow t)

/-- Restriction of a unitary norm-twist chart to the norm-one kernel recovers the
restriction of its unitary base character. -/
private theorem chart_normOneRestriction (χ : PontryaginDual Jₛ) (s : ℂ) :
    normOneRestriction mₛ (chart(χ) s) = (circleToComplex).comp (restrict₁(χ)) := by
  ext x
  change (χ x.val : ℂ) * (((mₛ x.val).val : ℝ) : ℂ) ^ s = (χ x.val : ℂ)
  rw [x.property, Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]

/-- Every quasi-character on the S-idele quotient lies on some unitary norm-twist chart. -/
private theorem exists_unitary_chart (c : Xₛ) :
    ∃ (χ : PontryaginDual Jₛ) (a : ℂ), chart(χ) a = c := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨e, he⟩ := sIdeleQuotient_quasiCharacterParametrization F S τ hτ
  let ω := (e c).2
  let a := (e c).1
  obtain ⟨χ, ⟨hχ, hχτ⟩, _⟩ := existsUnique_sLocalNormSectionCharacter τ hτ ω
  refine ⟨χ, a, e.injective ?_⟩
  apply Prod.ext
  · refine (existsUnique_complexPower ((chart(χ) a).comp τ)).unique (he (chart(χ) a)).1 fun t ↦ ?_
    change (χ (τ t) : ℂ) * (((mₛ (τ t)).val : ℝ) : ℂ) ^ a = ((t.val : ℝ) : ℂ) ^ a
    rw [hχτ, hτ, Circle.coe_one, one_mul]
  · exact ContinuousMonoidHom.ext fun u ↦ Circle.ext <| ((he _).2 u).trans <|
      (DFunLike.congr_fun (chart_normOneRestriction χ a) u).trans
        (congrArg Subtype.val (DFunLike.congr_fun hχ u))

/-- Twisting a quasi-character twice adds the complex exponents. -/
private theorem twist_twist (c : Xₛ) (a b : ℂ) :
    twistₛ (twistₛ c a) b = twistₛ c (a + b) := by
  ext1 x
  change (c x * (((mₛ x).val : ℝ) : ℂ) ^ a) * (((mₛ x).val : ℝ) : ℂ) ^ b =
    c x * (((mₛ x).val : ℝ) : ℂ) ^ (a + b)
  rw [mul_assoc, ← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ x).ne_zero))]

/-- The functional equation on a unitary norm-twist chart holds away from a discrete set. -/
private theorem local_functional_equation (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    (fun z ↦ sLocalIdelicZFunction f (chart(χ) z)) =ᶠ[codiscrete ℂ]
      (fun z ↦ sLocalRhoFactor (chart(χ) z) *
        sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ (chart(χ) z))) := by
  let Z (g : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) := sLocalIdelicZFunction g (chart(η) z)
  let R (z : ℂ) := sLocalRhoFactor (chart(χ) z)
  let D (z : ℂ) := Z (sAdeleSchwartzFourier f) χ⁻¹ (1 - z)
  have hZ (g : ℬₛ) (η : PontryaginDual Jₛ) (z : ℂ) : MeromorphicAt (Z g η) z :=
    ((sLocalIdelicZFunction_meromorphic g η) (mem_univ z)).meromorphicAt
  have hD (z : ℂ) : MeromorphicAt D z :=
    (hZ (sAdeleSchwartzFourier f) χ⁻¹ (1 - z)).comp_analyticAt
      (analyticAt_const.sub analyticAt_id)
  have hEq : Z f χ =ᶠ[codiscrete ℂ] R * D := by
    let Δ := Z f χ - R * D
    have hΔ : MeromorphicOn Δ univ :=
      fun z _ ↦ (hZ f χ z).sub ((sLocalRhoFactor_meromorphic χ z).mul (hD z))
    have hopen : IsOpen {z : ℂ | 0 < z.re ∧ z.re < 1} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hzero_on : EqOn Δ 0 {z : ℂ | 0 < z.re ∧ z.re < 1} := by
      intro z hz
      have hd : 0 < (1 - z).re := by simp; linarith [hz.2]
      have hLHS : Z f χ z = sLocalIdelicZetaIntegral f (chart(χ) z) :=
        sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz.1, rfl⟩
      have hFE := sLocalIdelicZetaIntegral_functionalEquation f χ z hz
      have hRHS : D z = sLocalIdelicZetaIntegral (sAdeleSchwartzFourier f) (dualₛ (chart(χ) z)) := by
        have hdual : dualₛ (chart(χ) z) = chart(χ⁻¹) (1 - z) := sLocalNormTwistChart_dual χ z
        rw [hdual]
        exact sLocalIdelicZFunction_eq_integral (sAdeleSchwartzFourier f) ⟨χ⁻¹, 1 - z, hd, rfl⟩
      simp only [Δ, Pi.sub_apply, Pi.mul_apply, Pi.zero_apply]
      rw [hLHS, hFE, ← hRHS, sub_self]
    have hmem : (1 / 2 : ℂ) ∈ {z : ℂ | 0 < z.re ∧ z.re < 1} := by norm_num
    have h₀ : meromorphicOrderAt Δ (1 / 2 : ℂ) = ⊤ := by
      apply meromorphicOrderAt_eq_top_iff.mpr
      filter_upwards [mem_nhdsWithin_of_mem_nhds (hopen.mem_nhds hmem)] with z hz
      exact hzero_on hz
    apply eventuallyEq_codiscrete_iff_forall_eventuallyEq_nhdsNE.2
    intro x
    exact (meromorphicOrderAt_eq_top_iff.mp
      (hΔ.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
        (mem_univ _) (mem_univ x) h₀)).mono fun z hz ↦ sub_eq_zero.mp hz
  filter_upwards [hEq] with z hz
  change Z f χ z = R z * D z at hz
  rw [sLocalNormTwistChart_dual]
  exact hz

/-- At any primary orbital index, the leading Laurent coefficient of `sLocalRhoFactor` is
nonzero, and the top polar functional multiplies the value of the reflected zeta transform
by that leading coefficient. -/
private theorem polar_leading_formula {p : Vℚ} {ω : PontryaginDual J₁}
    (j : Idx(p, ω)) (f : ℬₛ) :
    rhoCoeff(j.val.1, 0) ≠ 0 ∧
    sLocalPrincipalPartCoeff j.val.1 (sLocalRhoPoleOrder j.val.1) f =
      rhoCoeff(j.val.1, 0) * fourierZeta(j.val.1) f 0 := by
  classical
  let c := j.val.1
  let m := sLocalRhoPoleOrder c
  let ρ (z : ℂ) := sLocalRhoFactor (twistₛ c z)
  let H := fourierZeta(c) f
  have hm : 0 < m := by
    have hb : sLocalFinitePoleMultiplicity (Sₚ(p)) c ≤ m := by
      dsimp [m]
      rw [sLocalRhoPoleOrder_eq_card_polePlaces]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
    exact (Nat.zero_le _).trans_lt (j.property.2.trans_le hb)
  have hord : meromorphicOrderAt ρ 0 = ((-(m : ℤ) : ℤ) : WithTop ℤ) := by
    have ht := sLocalIdelicOrderBound_eq_neg_poleOrder c
    change min 0 (meromorphicOrderAt ρ 0) = _ at ht
    have hn : ((-(m : ℤ) : ℤ) : WithTop ℤ) < 0 := by exact_mod_cast (show -(m : ℤ) < 0 by omega)
    have hlt := (min_lt_iff.mp (ht.trans_lt hn)).resolve_left (lt_irrefl _)
    exact (min_eq_right hlt.le).symm.trans ht
  obtain ⟨χ, a, hc⟩ := exists_unitary_chart c
  have shift (z : ℂ) : twistₛ c z = chart(χ) (a + z) := by
    rw [← hc, twist_twist]
  have hρ : MeromorphicAt ρ 0 := by
    have heq : ρ = (fun u ↦ sLocalRhoFactor (chart(χ) u)) ∘ (fun z ↦ a + z) :=
      funext fun z ↦ congrArg sLocalRhoFactor (shift z)
    rw [heq]
    exact (sLocalRhoFactor_meromorphic χ (a + 0)).comp_analyticAt (by fun_prop)
  obtain ⟨A, hA, hA0, hrep⟩ := (meromorphicOrderAt_eq_int_iff hρ).mp hord
  have hr (z : ℂ) (hz : z ≠ 0) (h : ρ z = (z - 0) ^ (-(m : ℤ)) • A z) :
      ρ z * z ^ ((m : ℤ) - 0 - 1) = A z / (z - 0) := by
    simp only [h, sub_zero, smul_eq_mul]
    rw [mul_right_comm, ← zpow_add₀ hz, show -(m : ℤ) + ((m : ℤ) - 1) = -1 by ring]
    simp [div_eq_mul_inv, mul_comm]
  have hc0 : rhoCoeff(c, 0) = A 0 := by
    refine (mem_sLocalThetaPoleBound_iff_residue_congr (h := fun z ↦ A z / (z - 0)) ?_).trans
      (complexResidue_div_sub hA)
    filter_upwards [hrep, self_mem_nhdsWithin] with z hz hn
    exact hr z hn hz
  refine ⟨hc0.trans_ne hA0, ?_⟩
  change complexResidue (fun z ↦ sLocalIdelicZFunction f (twistₛ c z) / z ^ (-(m : ℤ) + 1)) 0 = _
  have ht : Tendsto (fun z : ℂ ↦ a + z) (𝓝[≠] 0) (𝓝[≠] (a + 0)) :=
    ((Homeomorph.addLeft a).map_punctured_nhds_eq 0).le
  have hH : AnalyticAt ℂ H 0 := sLocalOrbitalFourierZeta_analyticAt j f
  refine (mem_sLocalThetaPoleBound_iff_residue_congr (h := fun z ↦ (A z * H z) / (z - 0)) ?_).trans
    ((complexResidue_div_sub (g := fun z ↦ A z * H z) (hA.mul hH)).trans
      (congrArg (· * H 0) hc0.symm))
  filter_upwards [ht.eventually (nhdsNE_le_codiscrete _ (local_functional_equation χ f)), hrep,
    self_mem_nhdsWithin] with z he ha hn
  have hn' : z ≠ 0 := hn
  have heq : sLocalIdelicZFunction f (twistₛ c z) = ρ z * H z := by
    simpa only [ρ, H, shift] using he
  rw [heq, ha]
  simp only [sub_zero, smul_eq_mul, zpow_add₀ hn', zpow_one, zpow_neg, zpow_natCast]
  field_simp [hn']

/-- Every primary polar functional is the lower-triangular convolution of the Laurent
coefficients of `sLocalRhoFactor` with the primary Fourier jet functionals at the same center. -/
private theorem polar_row_formula {p : Vℚ} {ω : PontryaginDual J₁}
    (j : Idx(p, ω)) (f : ℬₛ) :
    sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j ((Kₛ(ω)).mkQ f) =
      ∑ k ∈ Finset.range (j.val.2 + 1), rhoCoeff(j.val.1, k) *
        (iteratedDeriv (j.val.2 - k) (fourierZeta(j.val.1) f) 0 / ((j.val.2 - k).factorial : ℂ)) := by
  classical
  have hmult : sLocalFinitePoleMultiplicity (Sₚ(p)) j.val.1 ≤ sLocalRhoPoleOrder j.val.1 := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces]
    exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
  have hbound := j.property.2.trans_le hmult
  change sLocalThetaPrincipalPartCoeff ω j.val.1 j.property.1 _ ((Kₛ(ω)).mkQL f) = _
  rw [sLocalThetaPrincipalPartCoeff_mk, ← sLocalPrincipalPartCoeff_apply]
  by_cases hj : j.val.2 = 0
  · simpa [hj] using (polar_leading_formula j f).2
  · have he := sLocalPrincipalPartCoeff_lower_formula j.val.1 f (sLocalRhoPoleOrder j.val.1 - j.val.2)
      (by omega)
    simpa only [show sLocalRhoPoleOrder j.val.1 - (sLocalRhoPoleOrder j.val.1 - j.val.2) = j.val.2
      by omega] using he

/-- Quotient-level row relation between primary polar functionals and primary Fourier jets. -/
private theorem polar_row_quotient {p : Vℚ} {ω : PontryaginDual J₁}
    (D Fdual : Idx(p, ω) → StrongDual ℂ (Q(p, ω)))
    (hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hFdual : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), Fdual j (π(p, ω) x) =
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (j : Idx(p, ω)) (y : Q(p, ω)) :
    D j y = ∑ k ∈ Finset.range (j.val.2 + 1),
      rhoCoeff(j.val.1, k) *
        (Fdual ⟨(j.val.1, j.val.2 - k), j.property.1,
          Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.property.2⟩ y /
          ((j.val.2 - k).factorial : ℂ)) := by
  obtain ⟨x, rfl⟩ := (Rₚ(p, ω)).mkQ_surjective y
  obtain ⟨f, rfl⟩ := (Kₛ(ω)).mkQ_surjective x
  rw [hD j ((Kₛ(ω)).mkQ f), polar_row_formula j f]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  let j' : Idx(p, ω) := ⟨(j.val.1, j.val.2 - k), j.property.1,
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.property.2⟩
  congr 2
  rw [hFdual j' ((Kₛ(ω)).mkQ f)]
  exact (sLocalOrbitalFourierJet_mk j' f).symm

open Classical in
/-- Diagonal Fourier jet evaluation on a polar biorthogonal vector. -/
private theorem fourier_diag_of_polar_biorthogonal {p : Vℚ} {ω : PontryaginDual J₁}
    (D Fdual : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
    (hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hFdual : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), Fdual j (π(p, ω) x) =
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hD_biorth : ∀ i j : Idx(p, ω), D i (ψ j) = if i = j then 1 else 0)
    (j : Idx(p, ω)) :
    Fdual j (ψ j) = (j.val.2.factorial : ℂ) / rhoCoeff(j.val.1, 0) := by
  classical
  let m := sLocalFinitePoleMultiplicity (Sₚ(p)) j.val.1
  let P_fn (k : ℕ) : ℂ :=
    if hk : k < m then D ⟨(j.val.1, k), j.property.1, hk⟩ (ψ j) else 0
  let D_fn (k : ℕ) : ℂ :=
    if hk : k < m then Fdual ⟨(j.val.1, k), j.property.1, hk⟩ (ψ j) else 0
  have hres := triangular_fourier_of_polar_biorthogonal
    (fun l ↦ rhoCoeff(j.val.1, l)) P_fn D_fn m j.val.2
    (polar_leading_formula j 0).1 j.property.2
    (fun k hk ↦ by
      dsimp only [P_fn]
      rw [dite_eq_left hk, polar_row_quotient D Fdual hD hFdual ⟨(j.val.1, k), j.property.1, hk⟩ (ψ j)]
      refine Finset.sum_congr rfl fun l _ ↦ ?_
      dsimp only [D_fn]
      rw [dite_eq_left (Nat.lt_of_le_of_lt (Nat.sub_le k l) hk)])
    (fun k hkr ↦ by
      have hk : k < m := lt_of_le_of_lt hkr j.property.2
      dsimp only [P_fn]
      rw [dite_eq_left hk]
      refine (hD_biorth ⟨(j.val.1, k), j.property.1, hk⟩ j).trans ?_
      have hiff : (⟨(j.val.1, k), j.property.1, hk⟩ : Idx(p, ω)) = j ↔ k = j.val.2 :=
        ⟨fun h ↦ congrArg (fun idx : Idx(p, ω) ↦ idx.val.2) h,
         fun h ↦ Subtype.ext (Prod.ext rfl h)⟩
      split_ifs with h1 h2 h2
      · rfl
      · exact (h2 (hiff.mp h1)).elim
      · exact (h1 (hiff.mpr h2)).elim
      · rfl)
  dsimp only [D_fn] at hres
  rw [dite_eq_left j.property.2] at hres
  have hself : (⟨(j.val.1, j.val.2), j.property.1, j.property.2⟩ : Idx(p, ω)) = j := Subtype.ext rfl
  rw [hself] at hres
  exact hres

end PolarLaurentRelation

section PolarBasisNecessity

open Classical in
/-- Along a single primary pole lattice and fixed jet order `r`, existence of a polar
Schauder basis of `Q(p, ω)` forces polynomial growth of `‖rhoCoeff(c_n, r)‖ / ‖rhoCoeff(c_n, 0)‖`. -/
private theorem polar_laurent_lattice_bound
    (p : Vℚ) (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ)
    (v : S) (u : (v.val.adicCompletion F)ˣ) (t : ℝ) (r : ℕ)
    (hS : IsSaturatedPlaceSet S) (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial)
    (hω : ω = restrict₁(χ)) (hv : v.val ∈ Sₚ(p)) (hu : uniformizerNorm(v, u))
    (ht : phase(χ, v, u, t)) (σ : ℕ ≃ Idx(p, ω))
    (D Fdual : Idx(p, ω) → StrongDual ℂ (Q(p, ω)))
    (ψ η : Idx(p, ω) → Q(p, ω))
    (hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hFdual : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), Fdual j (π(p, ω) x) =
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hD_biorth : ∀ i j : Idx(p, ω), D i (ψ j) = if i = j then 1 else 0)
    (hFdual_biorth : ∀ i j : Idx(p, ω), Fdual i (η j) = if i = j then 1 else 0)
    (hη_biorth : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = η j →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x =
        if i = j then 1 else 0)
    (hbasis : IsSchauderBasis (ψ ∘ σ) (D ∘ σ)) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (n : ℤ) (j : Idx(p, ω)),
      j.val = (lattice(χ, v, t, n), r) →
      v ∈ sLocalFinitePolePlaces (F := F) (S := S) j.val.1 →
      ‖rhoCoeff(j.val.1, r)‖ / ‖rhoCoeff(j.val.1, 0)‖ ≤ C * (1 + |(n : ℝ)|) ^ d := by
  classical
  -- Fréchet / barrelled setup on `Q(p, ω)`.
  have hR : IsClosed (Rₚ(p, ω) : Set (Θₛ(ω))) := by
    change IsClosed ((sLocalHomogeneousThetaPrincipalValue (F := F) (S := S) hₚ(p) ω).range : Set (Θₛ(ω)))
    rw [sLocalOrbitalPrincipalValue_eq_poleBound (F := F) (S := S) hₚ(p) hp hS hPic ω]
    exact sLocalThetaPoleBound_isClosed (F := F) (S := S) ω _
  have hF : IsFrechetTVS (Q(p, ω)) :=
    isFrechetTVS_quotient (sLocalHomogeneousThetaSpace_frechet ω) _ hR
  have hFcopy := hF
  obtain ⟨_, hpoly, _, hcomp⟩ := hFcopy
  let : UniformSpace (Q(p, ω)) := IsTopologicalAddGroup.rightUniformSpace _
  let : IsUniformAddGroup (Q(p, ω)) := isUniformAddGroup_of_addCommGroup
  let : BarrelledSpace ℂ (Q(p, ω)) := isFrechetTVS_barrelled hF
  let c (n : ℤ) := lattice(χ, v, t, n)
  have hc_inj : Injective c := by
    intro n₁ n₂ heq
    have hs := congrArg Complex.im (chart_injective χ heq)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one,
      Complex.ofReal_im, Complex.I_re, mul_zero, add_zero] at hs
    have hper : 0 < period(v) := div_pos (by positivity)
      (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val))
    have hsub : ((n₁ : ℝ) - (n₂ : ℝ)) * period(v) = 0 := by linarith
    have hreal : (n₁ : ℝ) = (n₂ : ℝ) :=
      sub_eq_zero.mp ((mul_eq_zero.mp hsub).resolve_right hper.ne')
    exact_mod_cast hreal
  -- Equicontinuity of the `r`-th Fourier jet family along `v`'s lattice.
  let g (n : ℤ) : StrongDual ℂ (Q(p, ω)) :=
    if h : v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n) ∧
        ∃ j : Idx(p, ω), j.val = (c n, r) then
      Fdual h.2.choose
    else 0
  have hg_pointwise (y : Q(p, ω)) : IsVonNBounded ℂ (range fun n : ℤ ↦ g n y) := by
    obtain ⟨x, rfl⟩ := (Rₚ(p, ω)).mkQ_surjective y
    obtain ⟨f, rfl⟩ := (Kₛ(ω)).mkQ_surjective x
    obtain ⟨a, ha⟩ := sLocalOrbitalFourierJet_lattice_schwartz p χ v u t
      hS hp hPic hv hu ht f r
    obtain ⟨pair, e, s₀, hs₀⟩ :=
      (mem_schwartzBruhatSubmodule_iff (a : Multiplicative ℤ → ℂ)).mp a.property
    obtain ⟨C₀, hC₀⟩ : ∃ C₀ : ℝ, ∀ n : ℤ, ‖g n (π(p, ω) ((Kₛ(ω)).mkQ f))‖ ≤ C₀ := by
      refine ⟨elementarySchwartzSeminorm (0, 0, 0, 0) s₀, fun n ↦ ?_⟩
      have hgn : g n (π(p, ω) ((Kₛ(ω)).mkQ f)) = a (Multiplicative.ofAdd n) := by
        rw [ha n]
        dsimp only [g]
        by_cases h1 : v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n) ∧
            ∃ j : Idx(p, ω), j.val = (c n, r)
        · have hspec := h1.2.choose_spec
          have h1eq : h1.2.choose.val.1 = c n := congrArg Prod.fst hspec
          have h2eq : h1.2.choose.val.2 = r := congrArg Prod.snd hspec
          have h2 : v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n) ∧
              r < sLocalPrimaryPoleMultiplicity (F := F) (S := S) p (c n) := by
            refine ⟨h1.1, ?_⟩
            dsimp only [sLocalPrimaryPoleMultiplicity]
            have hlt := h1.2.choose.property.2
            rw [h1eq, h2eq] at hlt
            exact hlt
          rw [dite_eq_left h1, ite_eq_left h2, hFdual]
          change sLocalOrbitalFourierJet h1.2.choose ((Kₛ(ω)).mkQL f) = _
          rw [sLocalOrbitalFourierJet_mk h1.2.choose f, h1eq, h2eq]
        · have hnot2 : ¬ (v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n) ∧
              r < sLocalPrimaryPoleMultiplicity (F := F) (S := S) p (c n)) := by
            rintro ⟨hvp, hrm⟩
            refine h1 ⟨hvp, ⟨⟨(c n, r), ?_, hrm⟩, rfl⟩⟩
            rw [chart_normOneRestriction, ← hω]
          rw [dite_eq_right h1, ite_eq_right hnot2]
          rfl
      rw [hgn]
      exact hs₀ ▸ norm_stage_realization_le pair e s₀ (Multiplicative.ofAdd n)
    exact (NormedSpace.isVonNBounded_iff ℂ).mpr
      ((Metric.isBounded_iff_subset_closedBall 0).mpr
        ⟨max C₀ 0, by
          rintro _ ⟨n, rfl⟩
          simp only [Metric.mem_closedBall, dist_zero_right]
          exact (hC₀ n).trans (le_max_left _ _)⟩)
  have hg_equi : EquicontinuousAt (fun n : ℤ ↦ (g n : Q(p, ω) → ℂ)) 0 :=
    (PolynormableSpace.banach_steinhaus (𝓕 := g) hg_pointwise).equicontinuous 0
  -- Define the nonnegative ratio sequence `b` on `ℤ`.
  let b (n : ℤ) : ℝ :=
    if h : v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n) ∧
        ∃ j : Idx(p, ω), j.val = (c n, r) then
      ‖rhoCoeff(c n, r)‖ / ‖rhoCoeff(c n, 0)‖
    else 0
  have hb_nn (n : ℤ) : 0 ≤ b n := by dsimp [b]; split_ifs <;> positivity
  obtain ⟨d, C, hC, hb_bound⟩ := poly_bound_of_rapidDecay_mul_tendsto_zero b hb_nn (by
    intro a hrapid
    let uvec (n : ℤ) : Q(p, ω) :=
      if h : v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n) ∧
          ∃ j : Idx(p, ω), j.val = (c n, 0) then
        a n • η h.2.choose
      else 0
    have hu_sum : Summable uvec := by
      apply summable_of_seminorm_summable
      intro q hq
      obtain ⟨e, A, hA, hgrowth⟩ := sLocalFourierOrbital_biorthogonal_growth
        p χ ω v u t hS hp hPic hω hv hu ht η hη_biorth q hq
      obtain ⟨B, hB⟩ := hrapid (e + 2)
      have hB_nn : 0 ≤ B := (mul_nonneg (by positivity) (norm_nonneg (a 0))).trans (hB 0)
      have hinv_sq : Summable (fun n : ℤ ↦ 1 / (1 + |(n : ℝ)|) ^ 2) := by
        apply Summable.of_nat_of_neg
        all_goals
          simpa only [Int.cast_neg, abs_neg, Int.cast_natCast, Nat.abs_cast,
            add_comm (1 : ℝ), Nat.cast_add_one] using
            (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
      refine (hinv_sq.mul_left (A * B)).of_nonneg_of_le (fun _ ↦ apply_nonneg _ _) fun n ↦ ?_
      dsimp only [uvec]
      split_ifs with h
      · rw [map_smul_eq_mul]
        have h1eq : h.2.choose.val.1 = c n := congrArg Prod.fst h.2.choose_spec
        have hvpole' : v ∈ sLocalFinitePolePlaces (F := F) (S := S) h.2.choose.val.1 := by
          rw [h1eq]
          exact h.1
        have hηq : q (η h.2.choose) ≤ A * (1 + |(n : ℝ)|) ^ e :=
          hgrowth n h.2.choose h1eq hvpole'
        have hLpos : 0 < 1 + |(n : ℝ)| := by positivity
        have ha_bd : ‖a n‖ ≤ B / (1 + |(n : ℝ)|) ^ (e + 2) :=
          (le_div_iff₀ (by positivity)).mpr (by linarith [hB n])
        calc
          ‖a n‖ * q (η h.2.choose)
              ≤ (B / (1 + |(n : ℝ)|) ^ (e + 2)) * (A * (1 + |(n : ℝ)|) ^ e) :=
                mul_le_mul ha_bd hηq (apply_nonneg _ _) (by positivity)
          _ = A * B * (1 / (1 + |(n : ℝ)|) ^ 2) := by
                rw [pow_add]
                field_simp [hLpos.ne']
      · rw [map_zero]
        exact mul_nonneg (mul_nonneg hA.le hB_nn) (div_nonneg zero_le_one (sq_nonneg _))
    let x₀ : Q(p, ω) := ∑' n : ℤ, uvec n
    have hFdual_x₀ (i : Idx(p, ω)) :
        Fdual i x₀ = ∑' n : ℤ, Fdual i (uvec n) :=
      ((Fdual i).hasSum hu_sum.hasSum).tsum_eq.symm
    have hFdual_x₀_zero (i : Idx(p, ω)) (hi : i.val.2 ≠ 0) : Fdual i x₀ = 0 := by
      rw [hFdual_x₀]
      have hzero_fn : ∀ n : ℤ, Fdual i (uvec n) = 0 := by
        intro n
        dsimp only [uvec]
        split_ifs with h
        · rw [map_smul, hFdual_biorth, ite_eq_right, smul_zero]
          intro heq
          have h2 : i.val.2 = 0 := (congrArg (fun j : Idx(p, ω) ↦ j.val.2) heq).trans
            (congrArg Prod.snd h.2.choose_spec)
          exact hi h2
        · exact map_zero _
      simp only [hzero_fn, tsum_zero]
    have hFdual_x₀_top (n : ℤ) (j : Idx(p, ω)) (hj : j.val = (c n, 0))
        (hv_pole : v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n)) :
        Fdual j x₀ = a n := by
      rw [hFdual_x₀, tsum_eq_single n]
      · have hex : v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n) ∧
            ∃ j' : Idx(p, ω), j'.val = (c n, 0) := ⟨hv_pole, j, hj⟩
        simp only [uvec, dite_eq_left hex, map_smul, hFdual_biorth]
        have hjeq : j = hex.2.choose := Subtype.ext (hj.trans hex.2.choose_spec.symm)
        rw [ite_eq_left hjeq, smul_eq_mul, mul_one]
      · intro m hmn
        dsimp only [uvec]
        split_ifs with h
        · rw [map_smul, hFdual_biorth, ite_eq_right, smul_zero]
          intro heq
          have hceq : c n = c m := (congrArg Prod.fst hj).symm.trans
            ((congrArg (fun idx : Idx(p, ω) ↦ idx.val.1) heq).trans
              (congrArg Prod.fst h.2.choose_spec))
          exact hmn (hc_inj hceq).symm
        · exact map_zero _
    have hterm0 : Tendsto (fun m : ℕ ↦ D (σ m) x₀ • ψ (σ m)) atTop (𝓝 0) :=
      hasSum_conditional_tendsto_zero (hbasis.2 x₀)
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hU : {y : Q(p, ω) | ∀ n : ℤ, ‖g n y‖ < ε} ∈ 𝓝 (0 : Q(p, ω)) := by
      have hmem := hg_equi _ (Metric.dist_mem_uniformity hε)
      filter_upwards [hmem] with y hy n
      have hyn : dist (g n 0) (g n y) < ε := hy n
      rw [map_zero, dist_zero_left] at hyn
      exact hyn
    obtain ⟨M, hM⟩ := eventually_atTop.mp (hterm0.eventually hU)
    let bad : Finset ℤ := (Finset.range M).biUnion fun m ↦
      if h : ∃ n : ℤ, c n = (σ m).val.1 then {h.choose} else ∅
    rw [Filter.Eventually, mem_cofinite]
    refine (bad.finite_toSet).subset fun n hn ↦ ?_
    have hge_eps : ε ≤ b n * ‖a n‖ := by
      have hnotlt : ¬ dist (b n * ‖a n‖) 0 < ε := hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (hb_nn n) (norm_nonneg _))] at hnotlt
      exact le_of_not_gt hnotlt
    by_cases hcond : v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n) ∧
        ∃ j : Idx(p, ω), j.val = (c n, r)
    · let j := hcond.2.choose
      let m := σ.symm j
      have hj1 : j.val.1 = c n := congrArg Prod.fst hcond.2.choose_spec
      have hj2 : j.val.2 = r := congrArg Prod.snd hcond.2.choose_spec
      by_contra hnbad
      have hmge : M ≤ m := by
        by_contra hlt
        push Not at hlt
        apply hnbad
        refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr hlt, ?_⟩)
        have hex : ∃ n' : ℤ, c n' = (σ m).val.1 :=
          ⟨n, by rw [Equiv.apply_symm_apply]; exact hj1.symm⟩
        rw [dite_eq_left hex, Finset.mem_singleton]
        exact hc_inj (by rw [hex.choose_spec, Equiv.apply_symm_apply]; exact hj1.symm)
      have hlt_eps : ‖g n (D (σ m) x₀ • ψ (σ m))‖ < ε := hM m hmge n
      have hDj : D j x₀ = rhoCoeff(c n, r) * a n := by
        rw [polar_row_quotient D Fdual hD hFdual j x₀, Finset.sum_eq_single j.val.2]
        · simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, div_one]
          exact congrArg₂ (· * ·) (by rw [hj1, hj2])
            (hFdual_x₀_top n
              ⟨(j.val.1, 0), j.property.1, lt_of_le_of_lt (Nat.zero_le _) j.property.2⟩
              (Prod.ext hj1 rfl) hcond.1)
        · intro k hk hne
          have hk' := Finset.mem_range.mp hk
          have hsub_ne : j.val.2 - k ≠ 0 := by omega
          have hzero : Fdual ⟨(j.val.1, j.val.2 - k), j.property.1,
              Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.property.2⟩ x₀ = 0 :=
            hFdual_x₀_zero _ hsub_ne
          rw [hzero, zero_div, mul_zero]
        · intro hmem
          exact (hmem (Finset.mem_range.mpr (Nat.lt_succ_self _))).elim
      have hgn_val : g n (D (σ m) x₀ • ψ (σ m)) =
          (r.factorial : ℂ) * (rhoCoeff(c n, r) / rhoCoeff(c n, 0)) * a n := by
        simp only [g, dite_eq_left hcond, m, Equiv.apply_symm_apply, map_smul, smul_eq_mul]
        rw [hDj, fourier_diag_of_polar_biorthogonal D Fdual ψ hD hFdual hD_biorth j, hj1, hj2]
        ring
      rw [hgn_val, norm_mul, norm_mul, Complex.norm_natCast, norm_div] at hlt_eps
      have hbn_eq : b n = ‖rhoCoeff(c n, r)‖ / ‖rhoCoeff(c n, 0)‖ := by
        simp only [b, dite_eq_left hcond]
      have hfac1 : (1 : ℝ) ≤ (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
      have hle : b n * ‖a n‖ ≤
          (r.factorial : ℝ) * (‖rhoCoeff(c n, r)‖ / ‖rhoCoeff(c n, 0)‖) * ‖a n‖ := by
        rw [hbn_eq, mul_assoc]
        exact le_mul_of_one_le_left (by positivity) hfac1
      linarith
    · have hbn0 : b n = 0 := by simp only [b, dite_eq_right hcond]
      rw [hbn0, zero_mul] at hge_eps
      linarith)
  refine ⟨d, C, hC, fun n j hj hvpole ↦ ?_⟩
  have hj1 : j.val.1 = c n := congrArg Prod.fst hj
  have hcond : v ∈ sLocalFinitePolePlaces (F := F) (S := S) (c n) ∧
      ∃ j' : Idx(p, ω), j'.val = (c n, r) :=
    ⟨by rw [← hj1]; exact hvpole, j, hj⟩
  have hspec := hb_bound n
  simp only [b, dite_eq_left hcond] at hspec
  rw [hj1]
  exact hspec

/-- Paper: Theorem 7.3.1.6(2)–(3), pp. 345, 349–350.
Exact converse of `sLocalPolarOrbital_bases_of_laurent_bounds`: if any enumeration of the
primary polar orbital functionals and biorthogonal vectors forms a Schauder basis of the
primary quotient `Q(p, ω)` (without assuming absoluteness or unconditionality), then the
normalized lower Laurent coefficients of `sLocalRhoFactor` have polynomial growth along every
unitary norm-twist chart. -/
theorem sLocalPolarOrbital_laurent_bounds_of_basis
    (p : Vℚ) (ω : PontryaginDual J₁)
    (hS : IsSaturatedPlaceSet S) (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω))
    (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
    (hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hbasis : IsSchauderBasis (ψ ∘ σ) (D ∘ σ)) :
    ∀ χ : PontryaginDual Jₛ, ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖rhoCoeff(j.val.1, j.val.2)‖ ≤ C * (1 + ‖s‖) ^ d * ‖rhoCoeff(j.val.1, 0)‖ := by
  classical
  obtain ⟨Fdual, η, _, _, hFdual, _, _, hFbasis, _⟩ :=
    sLocalFourierOrbital_bases (F := F) (S := S) p ω hS hp hPic σ
  have hη_biorth : ∀ (i j : Idx(p, ω)) (x : Θₛ(ω)), π(p, ω) x = η j →
      sLocalOrbitalFourierJet (F := F) (S := S) (T := Sₚ(p)) (ω := ω) i x =
        if i = j then 1 else 0 := by
    intro i j x hx
    rw [← hFdual i x, hx]
    have h := hFbasis.1 (σ.symm i) (σ.symm j)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq,
      ContinuousLinearMap.coe_coe] using h
  have hD_biorth (i j : Idx(p, ω)) : D i (ψ j) = if i = j then 1 else 0 := by
    have h := hbasis.1 (σ.symm i) (σ.symm j)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq,
      ContinuousLinearMap.coe_coe] using h
  have hFdual_biorth (i j : Idx(p, ω)) : Fdual i (η j) = if i = j then 1 else 0 := by
    have h := hFbasis.1 (σ.symm i) (σ.symm j)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq,
      ContinuousLinearMap.coe_coe] using h
  intro χ
  by_cases hω : ω = restrict₁(χ)
  case neg =>
    refine ⟨0, 1, zero_lt_one, fun j s _ hs ↦ (hω ?_).elim⟩
    have hcomp := j.property.1
    rw [hs, chart_normOneRestriction] at hcomp
    ext x
    exact (DFunLike.congr_fun hcomp x).symm
  have hunif (v : S) : ∃ u : (v.val.adicCompletion F)ˣ, uniformizerNorm(v, u) := by
    obtain ⟨π, hπ⟩ := (Valued.v : Valuation (v.val.adicCompletion F)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    exact ⟨Units.mk0 _ hπ.ne_zero, norm_uniformizer_adicCompletion v.val _ hπ⟩
  choose u hu using hunif
  choose t ht using fun v : S ↦ (existsUnique_sLocalOrbitalPhase χ v (u v) (hu v)).exists
  let P := {v : S // v.val ∈ Sₚ(p)}
  let R := {r : Fin (Fintype.card S) // r.val ≠ 0}
  choose d_pair C_pair hC_pair hbd_pair using fun pr : P × R ↦
    polar_laurent_lattice_bound p ω χ pr.1.val (u pr.1.val) (t pr.1.val) pr.2.val.val
      hS hp hPic hω pr.1.property (hu pr.1.val) (ht pr.1.val) σ D Fdual ψ η
      hD hFdual hD_biorth hFdual_biorth hη_biorth hbasis
  let K_place (v : S) : ℝ := 1 + (1 + |t v|) / period(v)
  have hper_pos (v : S) : 0 < period(v) := div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val))
  have hK_ge1 (v : S) : 1 ≤ K_place v := by
    dsimp [K_place]
    exact le_add_of_nonneg_right (div_nonneg (by positivity) (hper_pos v).le)
  let d_max : ℕ := Finset.univ.sup d_pair
  let C_max : ℝ := 1 + ∑ pr : P × R, C_pair pr * (K_place pr.1.val) ^ d_max
  have hC_max_pos : 0 < C_max := by
    have hsum_nn : 0 ≤ ∑ pr : P × R, C_pair pr * (K_place pr.1.val) ^ d_max :=
      Finset.sum_nonneg fun pr _ ↦
        mul_nonneg (hC_pair pr).le (pow_nonneg (zero_le_one.trans (hK_ge1 pr.1.val)) _)
    dsimp [C_max]
    linarith
  refine ⟨d_max, C_max, hC_max_pos, fun j s hjne hs ↦ ?_⟩
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) j.property.2)
  obtain ⟨hv_pole, hv_prim⟩ := Finset.mem_filter.mp hv
  obtain ⟨n, hn⟩ := (existsUnique_sLocalOrbitalLatticeIndex χ v (u v) (hu v) (t v) (ht v)
    j.val.1 ⟨s, hs⟩ hv_pole).exists
  have hs_eq : s = (((n : ℝ) * period(v) - t v : ℝ) : ℂ) * Complex.I :=
    chart_injective χ (hs.symm.trans hn)
  have hnorm_s : ‖s‖ = |(n : ℝ) * period(v) - t v| := by
    rw [hs_eq, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
  have hn_le : 1 + |(n : ℝ)| ≤ K_place v * (1 + ‖s‖) := by
    have htri : |(n : ℝ)| * period(v) ≤ ‖s‖ + |t v| := by
      have h1 : |(n : ℝ) * period(v)| ≤ |(n : ℝ) * period(v) - t v| + |t v| := by
        simpa only [sub_add_cancel] using abs_add_le ((n : ℝ) * period(v) - t v) (t v)
      rw [abs_mul, abs_of_pos (hper_pos v), ← hnorm_s] at h1
      exact h1
    have hdiv : |(n : ℝ)| ≤ (‖s‖ + |t v|) / period(v) := (le_div_iff₀ (hper_pos v)).mpr htri
    have h1 : (‖s‖ + |t v|) / period(v) ≤ ((1 + |t v|) / period(v)) * (1 + ‖s‖) := by
      rw [div_mul_eq_mul_div]
      apply div_le_div_of_nonneg_right _ (hper_pos v).le
      nlinarith [norm_nonneg s, abs_nonneg (t v)]
    dsimp [K_place]
    nlinarith [norm_nonneg s]
  have hj_lt : j.val.2 < Fintype.card S :=
    j.property.2.trans_le (Finset.card_le_univ _)
  let pr : P × R := (⟨v, hv_prim⟩, ⟨⟨j.val.2, hj_lt⟩, hjne⟩)
  have hratio := hbd_pair pr n j (Prod.ext hn rfl) hv_pole
  have hrho0 : 0 < ‖rhoCoeff(j.val.1, 0)‖ := norm_pos_iff.mpr (polar_leading_formula j 0).1
  rw [div_le_iff₀ hrho0] at hratio
  refine hratio.trans (mul_le_mul_of_nonneg_right ?_ hrho0.le)
  have hpow1 : (1 + |(n : ℝ)|) ^ d_pair pr ≤ (1 + |(n : ℝ)|) ^ d_max :=
    pow_le_pow_right₀ (le_add_of_nonneg_right (abs_nonneg _)) (Finset.le_sup (Finset.mem_univ pr))
  have hpow2 : (1 + |(n : ℝ)|) ^ d_max ≤ (K_place v) ^ d_max * (1 + ‖s‖) ^ d_max := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) hn_le _
  have hC_le : C_pair pr * (K_place v) ^ d_max ≤ C_max := by
    dsimp [C_max]
    have hmem : C_pair pr * (K_place pr.1.val) ^ d_max ≤
        ∑ q : P × R, C_pair q * (K_place q.1.val) ^ d_max :=
      Finset.single_le_sum
        (fun q (_ : q ∈ Finset.univ) ↦
          mul_nonneg (hC_pair q).le (pow_nonneg (zero_le_one.trans (hK_ge1 q.1.val)) d_max))
        (Finset.mem_univ pr)
    linarith
  calc
    C_pair pr * (1 + |(n : ℝ)|) ^ d_pair pr
        ≤ C_pair pr * ((K_place v) ^ d_max * (1 + ‖s‖) ^ d_max) :=
          mul_le_mul_of_nonneg_left (hpow1.trans hpow2) (hC_pair pr).le
    _ = (C_pair pr * (K_place v) ^ d_max) * (1 + ‖s‖) ^ d_max := by ring
    _ ≤ C_max * (1 + ‖s‖) ^ d_max :=
          mul_le_mul_of_nonneg_right hC_le (by positivity)

/-- Paper: Theorem 7.3.1.6(2)–(3), pp. 345, 349–350.
Exact characterization: the primary polar orbital system admits a Schauder basis of the
primary quotient `Q(p, ω)` if and only if the normalized lower Laurent coefficients of
`sLocalRhoFactor` satisfy the polynomial growth bound along every unitary chart. -/
theorem sLocalPolarOrbital_basis_iff_laurent_bounds
    (p : Vℚ) (ω : PontryaginDual J₁)
    (hS : IsSaturatedPlaceSet S) (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω)) :
    (∃ (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω)),
      (∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
        sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x) ∧
      IsSchauderBasis (ψ ∘ σ) (D ∘ σ)) ↔
    (∀ χ : PontryaginDual Jₛ, ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖rhoCoeff(j.val.1, j.val.2)‖ ≤ C * (1 + ‖s‖) ^ d * ‖rhoCoeff(j.val.1, 0)‖) := by
  constructor
  · rintro ⟨D, ψ, hD, hbasis⟩
    exact sLocalPolarOrbital_laurent_bounds_of_basis p ω hS hp hPic σ D ψ hD hbasis
  · intro hcoeff
    obtain ⟨D, ψ, _, _, hD, _, _, hbasis, _⟩ :=
      sLocalPolarOrbital_bases_of_laurent_bounds p ω hS hp hPic σ hcoeff
    exact ⟨D, ψ, hD, hbasis⟩

/-- Paper: Theorem 7.3.1.6(2)–(3), pp. 345, 349–350.
Automatic absoluteness and unconditionality: if some enumeration of the primary polar
orbital system forms a Schauder basis of `Q(p, ω)`, then every enumeration gives an absolute
Schauder basis of `Q(p, ω)` and an unconditional Schauder basis of `StrongDual ℂ (Q(p, ω))`. -/
theorem sLocalPolarOrbital_basis_isAbsolute_and_dual_isUnconditional
    (p : Vℚ) (ω : PontryaginDual J₁)
    (hS : IsSaturatedPlaceSet S) (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial)
    (σ σ' : ℕ ≃ Idx(p, ω))
    (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
    (hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hbasis : IsSchauderBasis (ψ ∘ σ) (D ∘ σ)) :
    let e := ψ ∘ σ'
    let d := D ∘ σ'
    let ev : ℕ → StrongDual ℂ (StrongDual ℂ (Q(p, ω))) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (ψ (σ' n))
    IsSchauderBasis d ev ∧ SchauderBasis.IsUnconditional d ev ∧
      IsSchauderBasis e d ∧ SchauderBasis.IsAbsolute e d := by
  classical
  have hR : IsClosed (Rₚ(p, ω) : Set (Θₛ(ω))) := by
    change IsClosed ((sLocalHomogeneousThetaPrincipalValue (F := F) (S := S) hₚ(p) ω).range : Set (Θₛ(ω)))
    rw [sLocalOrbitalPrincipalValue_eq_poleBound (F := F) (S := S) hₚ(p) hp hS hPic ω]
    exact sLocalThetaPoleBound_isClosed (F := F) (S := S) ω _
  have hF : IsFrechetTVS (Q(p, ω)) :=
    isFrechetTVS_quotient (sLocalHomogeneousThetaSpace_frechet ω) _ hR
  have : TopologicalSpace.MetrizableSpace (Q(p, ω)) := hF.2.2.1
  have hcoeff := sLocalPolarOrbital_laurent_bounds_of_basis p ω hS hp hPic σ D ψ hD hbasis
  obtain ⟨D', ψ', ev', hev', hD', hdual, hunc, hprim, habs⟩ :=
    sLocalPolarOrbital_bases_of_laurent_bounds p ω hS hp hPic σ' hcoeff
  have hDeq : D' = D := by
    funext j
    ext y
    obtain ⟨x, rfl⟩ := (Rₚ(p, ω)).mkQ_surjective y
    exact (hD' j x).trans (hD j x).symm
  have hψeq : ψ' = ψ := by
    funext j
    have hsep : ∀ y : Q(p, ω), (∀ i : Idx(p, ω), D i y = 0) → y = 0 := by
      intro y hy
      have hsum : HasSum (fun m ↦ D (σ m) y • ψ (σ m)) y (SummationFilter.conditional ℕ) :=
        hbasis.2 y
      have hzero : (fun m ↦ D (σ m) y • ψ (σ m)) = fun _ ↦ 0 :=
        funext fun m ↦ by rw [hy (σ m), zero_smul]
      rw [hzero] at hsum
      exact ((hasSum_zero (L := SummationFilter.conditional ℕ)).unique hsum).symm
    apply sub_eq_zero.mp
    apply hsep
    intro i
    rw [map_sub]
    have h1 : D i (ψ' j) = if i = j then 1 else 0 := by
      rw [← hDeq]
      have h := hprim.1 (σ'.symm i) (σ'.symm j)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq,
        ContinuousLinearMap.coe_coe] using h
    have h2 : D i (ψ j) = if i = j then 1 else 0 := by
      have h := hbasis.1 (σ.symm i) (σ.symm j)
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, EmbeddingLike.apply_eq_iff_eq,
        ContinuousLinearMap.coe_coe] using h
    rw [h1, h2, sub_self]
  have heveq : ev' = fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (ψ (σ' n)) := by
    funext n
    ext ℓ
    exact (hev' n ℓ).trans (by rw [hψeq]; rfl)
  subst hDeq
  subst hψeq
  subst heveq
  exact ⟨hdual, hunc, hprim, habs⟩

end PolarBasisNecessity

section OutsideEulerNecessity

/-- The residue of `F z / z^2` at zero equals `deriv F 0` for any function analytic at zero. -/
private theorem complexResidue_div_sq {F₀ : ℂ → ℂ} (hF₀ : AnalyticAt ℂ F₀ 0) :
    complexResidue (fun z : ℂ ↦ F₀ z / z ^ 2) 0 = deriv F₀ 0 := by
  have h1 : complexResidue (fun z : ℂ ↦ dslope F₀ 0 z / (z - 0)) 0 = dslope F₀ 0 0 :=
    complexResidue_div_sub (hF₀.dslope 0)
  rw [dslope_same] at h1
  rw [← h1]
  -- Compare circle integrals on small positive radii: the constant `F₀ 0 / z^2` integrates to zero.
  obtain ⟨δ, hδ, hAn⟩ := Metric.nhds_basis_ball.eventually_iff.mp
    (hF₀.eventually_analyticAt.and (hF₀.dslope 0).eventually_analyticAt)
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  congr 1
  have hzero : ∮ z in C(0, r), F₀ 0 * (z - 0) ^ (-2 : ℤ) = 0 := by
    rw [circleIntegral.integral_const_mul]
    have hpow := circleIntegral.integral_sub_zpow_of_ne (n := (-2 : ℤ)) (by norm_num)
      (0 : ℂ) (0 : ℂ) r
    rw [hpow, mul_zero]
  have hint1 : CircleIntegrable (fun z : ℂ ↦ F₀ 0 * (z - 0) ^ (-2 : ℤ)) 0 r := by
    refine ContinuousOn.circleIntegrable hr.1.le ?_
    intro z hz
    have hne : z ≠ 0 := by
      rintro rfl
      rw [Metric.mem_sphere, dist_self] at hz
      exact hr.1.ne hz
    exact (continuousAt_const.mul ((continuousAt_id.sub continuousAt_const).zpow₀ (-2)
      (Or.inl (by simpa using hne)))).continuousWithinAt
  have hint2 : CircleIntegrable (fun z : ℂ ↦ dslope F₀ 0 z / (z - 0)) 0 r := by
    refine ContinuousOn.circleIntegrable hr.1.le ?_
    intro z hz
    have hne : z ≠ 0 := by
      rintro rfl
      rw [Metric.mem_sphere, dist_self] at hz
      exact hr.1.ne hz
    have hball : z ∈ Metric.ball (0 : ℂ) δ := by
      rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
      exact hr.2
    exact ((hAn hball).2.continuousAt.div (continuousAt_id.sub continuousAt_const)
      (by simpa using hne)).continuousWithinAt
  have hsplit : ∮ z in C(0, r), F₀ z / z ^ 2 =
      (∮ z in C(0, r), F₀ 0 * (z - 0) ^ (-2 : ℤ)) +
      (∮ z in C(0, r), dslope F₀ 0 z / (z - 0)) := by
    rw [← circleIntegral.integral_add hint1 hint2]
    refine circleIntegral.integral_congr hr.1.le fun z hz ↦ ?_
    have hne : z ≠ 0 := by
      rintro rfl
      rw [Metric.mem_sphere, dist_self] at hz
      exact hr.1.ne hz
    have hd : dslope F₀ 0 z = (F₀ z - F₀ 0) / z := by
      rw [dslope_of_ne _ hne, slope_def_field, sub_zero]
    rw [hd, sub_zero, zpow_neg, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    field_simp [hne]
    ring
  rw [hsplit, hzero, zero_add]

/-- Paper: Theorem 7.3.1.6, p. 349, and Theorem 7.3.3.4, pp. 360–363.
Exact logarithmic-derivative identity for the first Laurent ratio of `sLocalRhoFactor`:
for any center `c` with `0 < sLocalRhoPoleOrder c` and any analytic cleared germ `G` near
zero with `G 0 ≠ 0`, `rhoCoeff(c, 1) / rhoCoeff(c, 0)` equals `G'(0) / G(0)` plus the
weighted sum of finite Euler terms `log(N v) * b(c, v)`. -/
theorem sLocalRho_firstLaurentRatio_eq_logDeriv_add_eulerSum
    (c : Xₛ) (G : ℂ → ℂ) (hG : AnalyticAt ℂ G 0) (hG0 : G 0 ≠ 0)
    (hGe : G =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦
      z ^ sLocalRhoPoleOrder c * sLocalRhoFactor (twistₛ c z) *
        ∏ v : S, (1 + (if finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c) = 0 then 0
          else 1 - finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)) *
          (Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z) - 1))) :
    rhoCoeff(c, 1) / rhoCoeff(c, 0) =
      deriv G 0 / G 0 +
        ∑ v : S, (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) *
          (if finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c) = 0 then 0
           else 1 - finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)) := by
  classical
  let m := sLocalRhoPoleOrder c
  let b (v : S) : ℂ :=
    if finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c) = 0 then 0
    else 1 - finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)
  let L (v : S) : ℂ := -(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)
  let dfac (v : S) (z : ℂ) : ℂ := 1 + b v * (Complex.exp (L v * z) - 1)
  let D (z : ℂ) : ℂ := ∏ v : S, dfac v z
  have hD0 : D 0 = 1 := by simp [D, dfac]
  have hD_an : AnalyticAt ℂ D 0 :=
    Finset.univ.analyticAt_fun_prod fun v _ ↦ by dsimp [dfac]; fun_prop
  have hdfac_deriv (v : S) : HasDerivAt (dfac v) (b v * L v) 0 := by
    have h1 : HasDerivAt (fun z : ℂ ↦ L v * z) (L v) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul (L v)
    have h2 : HasDerivAt (fun z : ℂ ↦ Complex.exp (L v * z) - 1) (L v) 0 := by
      simpa [mul_zero, Complex.exp_zero] using h1.cexp.sub_const 1
    simpa [dfac] using (h2.const_mul (b v)).const_add 1
  have hD_deriv : HasDerivAt D (∑ v : S, b v * L v) 0 := by
    have hprod : ∀ s : Finset S,
        HasDerivAt (fun z ↦ ∏ v ∈ s, dfac v z) (∑ v ∈ s, b v * L v) 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        simpa using hasDerivAt_const (0 : ℂ) (1 : ℂ)
      | @insert a s ha ih =>
        have hmul : HasDerivAt (fun z ↦ dfac a z * ∏ v ∈ s, dfac v z)
            (b a * L a * (∏ v ∈ s, dfac v 0) + dfac a 0 * (∑ v ∈ s, b v * L v)) 0 :=
          (hdfac_deriv a).mul ih
        have hda0 : dfac a 0 = 1 := by simp [dfac]
        have hs0 : (∏ v ∈ s, dfac v 0) = 1 := Finset.prod_eq_one fun v _ ↦ by simp [dfac]
        simp only [Finset.prod_insert ha, Finset.sum_insert ha]
        simpa only [hda0, hs0, mul_one, one_mul] using hmul
    exact hprod Finset.univ
  let F₀ (z : ℂ) : ℂ := G z / D z
  have hF₀_an : AnalyticAt ℂ F₀ 0 := hG.div hD_an (by rw [hD0]; exact one_ne_zero)
  have hF₀_germ : F₀ =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ z ^ m * sLocalRhoFactor (twistₛ c z) := by
    have hDne : ∀ᶠ z in 𝓝 (0 : ℂ), D z ≠ 0 :=
      hD_an.continuousAt.eventually_ne (by rw [hD0]; exact one_ne_zero)
    filter_upwards [hGe, nhdsWithin_le_nhds hDne] with z hgz hdz
    change G z / D z = z ^ m * sLocalRhoFactor (twistₛ c z)
    rw [hgz, mul_div_cancel_right₀ _ hdz]
  have hrho0 : rhoCoeff(c, 0) = F₀ 0 := by
    refine (mem_sLocalThetaPoleBound_iff_residue_congr (h := fun z ↦ F₀ z / (z - 0)) ?_).trans
      (complexResidue_div_sub hF₀_an)
    filter_upwards [hF₀_germ, self_mem_nhdsWithin] with z hfz hne
    have hn : z ≠ 0 := hne
    rw [hfz, sub_zero, ← zpow_natCast z m, mul_comm (z ^ (m : ℤ)), mul_div_assoc,
      div_eq_mul_inv, ← zpow_neg_one, ← zpow_add₀ hn]
    congr 2
  have hrho1 : rhoCoeff(c, 1) = deriv F₀ 0 := by
    refine (mem_sLocalThetaPoleBound_iff_residue_congr (h := fun z ↦ F₀ z / z ^ 2) ?_).trans
      (complexResidue_div_sq hF₀_an)
    filter_upwards [hF₀_germ, self_mem_nhdsWithin] with z hfz hne
    have hn : z ≠ 0 := hne
    rw [hfz, ← zpow_natCast z m, show z ^ 2 = z ^ (2 : ℤ) from (zpow_natCast z 2).symm,
      mul_comm (z ^ (m : ℤ)), mul_div_assoc, ← zpow_sub₀ hn]
    congr 2
    dsimp only [m]
    omega
  have hF₀_0 : F₀ 0 = G 0 := by simp [F₀, hD0]
  have hF₀_deriv : deriv F₀ 0 = deriv G 0 - G 0 * (∑ v : S, b v * L v) := by
    have hq : HasDerivAt F₀ ((deriv G 0 * D 0 - G 0 * ∑ v : S, b v * L v) / D 0 ^ 2) 0 :=
      hG.differentiableAt.hasDerivAt.div hD_deriv (by rw [hD0]; exact one_ne_zero)
    simpa only [hD0, mul_one, one_pow, div_one] using hq.deriv
  rw [hrho1, hrho0, hF₀_0, hF₀_deriv, sub_div, mul_div_cancel_left₀ _ hG0]
  have hsum_neg : -(∑ v : S, b v * L v) =
      ∑ v : S, (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * b v := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun v _ ↦ ?_
    dsimp [L]
    ring
  rw [sub_eq_add_neg, hsum_neg]

/-- Geometric representation of a finite local Euler factor along a norm-twist chart. -/
private theorem finite_euler_geometric (v : S) (c : Xₛ) :
    ∃ a : ℂ, ∀ z : ℂ, finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ c z)) =
      (1 - a * Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z))⁻¹ := by
  have hval (x : (v.val.adicCompletion F)ˣ) (z : ℂ) :
      sLocalFiniteRestriction v (twistₛ c z) x =
        sLocalFiniteRestriction v c x * (‖x.val‖ : ℂ) ^ z := by
    obtain ⟨g, hg⟩ : ∃ g : Jₛ, ∀ d : Xₛ, sLocalFiniteRestriction v d x = d g := ⟨_, fun _ ↦ rfl⟩
    have hm := sLocalFiniteRestriction_norm (F := F) (S := S) v x
    rw [hg] at hm
    change ((1 : PontryaginDual Jₛ) g : ℂ) * _ ^ (1 : ℂ) = _ at hm
    simp only [PontryaginDual.one_apply, Circle.coe_one, Complex.cpow_one, one_mul] at hm
    rw [hg, hg]
    exact congrArg (fun t : ℂ ↦ c g * t ^ z) hm
  let ι := Units.map (v.val.adicCompletionIntegers F).subtype.toMonoidHom
  have hu (z : ℂ) : (∀ u, sLocalFiniteRestriction v (twistₛ c z) (ι u) = 1) ↔
      ∀ u, sLocalFiniteRestriction v c (ι u) = 1 := by
    refine forall_congr' fun u ↦ ?_
    have hn : ‖(ι u).val‖ = 1 := Valued.toNormedField.norm_eq_one_iff.mpr
      ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := ι u)).mp
        ⟨u.val.property, u.inv.property⟩)
    rw [hval, hn, Complex.ofReal_one, Complex.one_cpow, mul_one]
  by_cases h : ∀ u, sLocalFiniteRestriction v c (ι u) = 1
  · let hπ := (Valued.v : Valuation (v.val.adicCompletion F)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    let π : (v.val.adicCompletion F)ˣ := Units.mk0 hπ.choose hπ.choose_spec.ne_zero
    refine ⟨sLocalFiniteRestriction v c π, fun z ↦ ?_⟩
    rw [finiteLocalEulerFactor, ite_eq_left ((hu z).mpr h)]
    change (1 - sLocalFiniteRestriction v (twistₛ c z) π)⁻¹ = _
    rw [hval, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr π.ne_zero)),
      ← Complex.ofReal_log (norm_nonneg _),
      show ‖π.val‖ = _ from norm_uniformizer_adicCompletion v.val _ hπ.choose_spec,
      Real.log_inv, Complex.ofReal_neg]
  · exact ⟨0, fun z ↦ by rw [finiteLocalEulerFactor, ite_eq_right (mt (hu z).mp h)]; simp⟩

/-- Primary finite Euler factors take only finitely many values across all primary poles on
a fixed unitary chart, hence are uniformly bounded. -/
private theorem primary_euler_bounded (p : Vℚ) (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ)
    (v : S) (hv : v.val ∈ Sₚ(p)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (j : Idx(p, ω)) (s : ℂ), j.val.1 = chart(χ) s →
      ‖finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1)‖ ≤ C := by
  classical
  let E (w : S) (d : Xₛ) := finiteLocalEulerFactor w.val (sLocalFiniteRestriction w d)
  let f (w : S) := w.val.asIdeal.inertiaDeg (𝓞 ℚ)
  let X (z : ℂ) := Complex.exp (-(Real.log (p.asIdeal.absNorm : ℝ) : ℂ) * z)
  choose a ha using fun w : S ↦ finite_euler_geometric w ((circleToComplex).comp χ)
  have hpow (w : S) (hw : w.val ∈ Sₚ(p)) (z : ℂ) :
      E w (chart(χ) z) = (1 - a w * X z ^ f w)⁻¹ := by
    let : w.val.asIdeal.IsPrime := w.val.isPrime
    let : w.val.asIdeal.LiesOver p.asIdeal :=
      ⟨(congrArg HeightOneSpectrum.asIdeal ((mem_sLocalPrimaryPlaces p w.val).mp hw).2).symm⟩
    rw [show E w (chart(χ) z) = _ from ha w z,
      ← Ideal.absNorm_pow_inertiaDeg p.asIdeal w.val.asIdeal, Nat.cast_pow, Real.log_pow]
    dsimp only [X, f]
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  let P (w : S) : Polynomial ℂ := 1 - Polynomial.C (a w) * Polynomial.X ^ f w
  have hn (w : S) (hw : w.val ∈ Sₚ(p)) : P w ≠ 0 := by
    let : w.val.asIdeal.IsPrime := w.val.isPrime
    have hd : f w ≠ 0 := (Ideal.inertiaDeg_pos w.val.asIdeal (𝓞 ℚ)).ne'
    intro h
    have := congrArg (Polynomial.eval 0) h
    simp [P, zero_pow hd] at this
  let W := Finset.univ.filter fun w : S ↦ w.val ∈ Sₚ(p)
  let K := W.biUnion fun w ↦ (P w).roots.toFinset
  have hK (j : Idx(p, ω)) (s : ℂ) (hs : j.val.1 = chart(χ) s) : X s ∈ K := by
    obtain ⟨w, hw⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) j.property.2)
    obtain ⟨hpole, hw⟩ := Finset.mem_filter.mp hw
    have hm := (sLocalPrincipalPartCoeff_leading_formula_fin_factor j.val.1 w).1
    have ho : meromorphicOrderAt (fun z ↦ E w (twistₛ j.val.1 z)) 0 < 0 :=
      (Finset.mem_filter.mp hpole).2
    have he0 : E w j.val.1 = 0 := by
      by_contra h
      have hz : twistₛ j.val.1 0 = j.val.1 := by
        ext1 x; exact (congrArg (j.val.1 x * ·) (Complex.cpow_zero _)).trans (mul_one _)
      exact ho.ne (hm.meromorphicOrderAt_eq_zero_iff.mpr (by simpa only [hz] using h))
    rw [hs, hpow w hw, inv_eq_zero] at he0
    exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩,
      Multiset.mem_toFinset.mpr ((Polynomial.mem_roots (hn w hw)).mpr
        (by simpa [P, Polynomial.IsRoot] using he0))⟩
  refine ⟨∑ x ∈ K, ‖(1 - a v * x ^ f v)⁻¹‖, Finset.sum_nonneg fun _ _ ↦ norm_nonneg _,
    fun j s hs ↦ ?_⟩
  change ‖E v j.val.1‖ ≤ _
  rw [hs, hpow v hv]
  exact Finset.single_le_sum (fun x _ ↦ norm_nonneg ((1 - a v * x ^ f v)⁻¹)) (hK j s hs)

/-- Removing a simple zero at the origin of an entire function gives a negative meromorphic
order for its reciprocal. -/
private theorem meromorphicOrderAt_inv_lt_zero_of_zero {G : ℂ → ℂ} (hG : Differentiable ℂ G)
    {y : ℂ} (hy : G y ≠ 0) (z : ℂ) (hz : G z = 0) :
    meromorphicOrderAt (fun w ↦ (G w)⁻¹) z < 0 := by
  have hAn : AnalyticAt ℂ G z := hG.analyticAt z
  change meromorphicOrderAt G⁻¹ z < 0
  rw [meromorphicOrderAt_inv, hAn.meromorphicOrderAt_eq]
  have htop : analyticOrderAt G z ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    exact hy (AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      (fun w _ ↦ hG.analyticAt w) isPreconnected_univ (mem_univ z) h (mem_univ y))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  have hne0 : n ≠ 0 := by
    intro hn0
    have h0 : analyticOrderAt G z = 0 := by rw [← hn, hn0]; rfl
    rw [analyticOrderAt_eq_zero] at h0
    exact (by simpa [hAn] using h0 : G z ≠ 0) hz
  rw [← hn, ENat.map_natCast]
  have : 0 < n := Nat.pos_of_ne_zero hne0
  exact_mod_cast (by omega : -(n : ℤ) < 0)

/-- Clearing all finite Euler factors on a fixed disk around zero produces an analytic germ
whose ratio to its value at zero is bounded by `2 ^ |S|`. -/
private theorem cleared_finite_germ :
    let E (v : S) (c : Xₛ) := finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)
    let b (v : S) (c : Xₛ) := if E v c = 0 then 0 else 1 - E v c
    let D (v : S) (c : Xₛ) (z : ℂ) :=
      1 + b v c * (Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z) - 1)
    ∃ R > (0 : ℝ), ∀ c : Xₛ, ∃ K : ℂ → ℂ,
      AnalyticOnNhd ℂ K (Metric.closedBall 0 R) ∧
      (K =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ z ^ (sLocalFinitePolePlaces c).card *
        (∏ v : S, E v (twistₛ c z)) * ∏ v : S, D v c z) ∧
      ∀ z ∈ Metric.closedBall 0 R, ‖K z / K 0‖ ≤ 2 ^ Fintype.card S := by
  classical
  intro E b D
  let L (v : S) : ℂ := -(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)
  let g (v : S) (z : ℂ) := 1 - Complex.exp (L v * z)
  let U (v : S) := (dslope (g v) 0)⁻¹
  have hU (v : S) : AnalyticAt ℂ (U v) 0 ∧ U v 0 ≠ 0 := by
    have hder : HasDerivAt (g v) (-L v) 0 := by
      simpa [g] using (((hasDerivAt_id (0 : ℂ)).const_mul (L v)).cexp.const_sub 1)
    have hne : deriv (g v) 0 ≠ 0 := by
      rw [hder.deriv, neg_ne_zero, show L v = _ from rfl, neg_ne_zero, Complex.ofReal_ne_zero]
      exact (Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val)).ne'
    have hd : dslope (g v) 0 0 ≠ 0 := by rwa [dslope_same]
    exact ⟨((by dsimp [g]; fun_prop : AnalyticAt ℂ (g v) 0).dslope 0).inv hd, inv_ne_zero hd⟩
  obtain ⟨R, hR, hball⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp
    (eventually_all.mpr fun v : S ↦ (hU v).1.eventually_analyticAt.and
      (((hU v).1.continuousAt.div_const (U v 0)).norm.eventually_lt continuousAt_const
        (show ‖U v 0 / U v 0‖ < 2 by rw [div_self (hU v).2, norm_one]; norm_num)))
  refine ⟨R, hR, fun c ↦ ?_⟩
  have hz0 : twistₛ c 0 = c := by
    ext1 x; exact (congrArg (c x * ·) (Complex.cpow_zero _)).trans (mul_one _)
  let P := sLocalFinitePolePlaces c
  let k (v : S) (z : ℂ) := if v ∈ P then U v z else E v c
  have he (v : S) : k v =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦
      (if v ∈ P then z else 1) * E v (twistₛ c z) * D v c z := by
    obtain ⟨a, ha⟩ := finite_euler_geometric v c
    have hE (z : ℂ) : E v (twistₛ c z) = (1 - a * Complex.exp (L v * z))⁻¹ := ha z
    have h0 : E v c = (1 - a)⁻¹ := by
      simpa only [hz0, mul_zero, Complex.exp_zero, mul_one] using hE 0
    have hA : AnalyticAt ℂ (fun z : ℂ ↦ 1 - a * Complex.exp (L v * z)) 0 := by fun_prop
    have hp : v ∈ P ↔ a = 1 := by
      change v ∈ (Finset.univ.filter _) ↔ _
      rw [Finset.mem_filter, and_iff_right (Finset.mem_univ _)]
      change meromorphicOrderAt (fun z ↦ E v (twistₛ c z)) 0 < 0 ↔ _
      rw [funext hE]
      by_cases h : a = 1
      · subst a
        have hy : g v 1 ≠ 0 := by
          have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
            exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
          have hlt := Real.exp_lt_one_iff.mpr (neg_lt_zero.mpr (Real.log_pos hq))
          change 1 - Complex.exp (L v * 1) ≠ 0
          rw [mul_one, sub_ne_zero,
            show L v = ((-Real.log (v.val.asIdeal.absNorm : ℝ) : ℝ) : ℂ) by simp [L],
            ← Complex.ofReal_exp, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
          exact hlt.ne'
        simp only [one_mul, iff_true]
        exact meromorphicOrderAt_inv_lt_zero_of_zero (G := g v) (by dsimp [g]; fun_prop) hy 0
          (by simp [g])
      · have hn : 1 - a * Complex.exp (L v * 0) ≠ 0 := by simpa [sub_ne_zero] using Ne.symm h
        exact iff_of_false (not_lt.mpr (hA.inv hn).meromorphicOrderAt_nonneg) h
    by_cases h : v ∈ P
    · have ha1 := hp.mp h
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hn : z ≠ 0 := hz
      simp [k, h, D, b, h0, ha1, hE, L, U, dslope_of_ne _ hn, slope_def_field, g,
        div_eq_mul_inv, mul_comm]
    · have hne : 1 - a ≠ 0 := sub_ne_zero.mpr (Ne.symm (mt hp.mpr h))
      have hn := hA.continuousAt.eventually_ne (by simpa using hne)
      filter_upwards [hn.filter_mono nhdsWithin_le_nhds] with z hz
      simp only [k, h, ↓reduceIte, one_mul, D, b, h0, inv_ne_zero hne, hE]
      change (1 - a)⁻¹ = (1 - a * Complex.exp (L v * z))⁻¹ *
        (1 + (1 - (1 - a)⁻¹) * (Complex.exp (L v * z) - 1))
      field_simp
      ring
  refine ⟨fun z ↦ ∏ v, k v z, fun z hz ↦ Finset.univ.analyticAt_fun_prod (fun v _ ↦ ?_),
    ?_, fun z hz ↦ ?_⟩
  · by_cases h : v ∈ P
    · simpa only [k, ite_eq_left h] using (hball hz v).1
    · simpa only [k, ite_eq_right h] using (analyticAt_const (v := E v c) (x := z) (𝕜 := ℂ))
  · filter_upwards [eventually_all.mpr he] with z hz
    simp only [hz, Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_const, P]
  · rw [← Finset.prod_div_distrib, norm_prod]
    change _ ≤ (2 : ℝ) ^ (Finset.univ : Finset S).card
    rw [← Finset.prod_const]
    apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
    intro v _
    by_cases h : v ∈ P
    · simpa only [k, ite_eq_left h] using (hball hz v).2.le
    · simp only [k, ite_eq_right h]
      by_cases he0 : E v c = 0 <;> simp [he0]

/-- Local finite norm-twist chart periodicity in the imaginary direction. -/
private theorem finite_local_chart_periodic (v : V)
    (η : PontryaginDual (v.adicCompletion F)ˣ) :
    let m𝔭 : (v.adicCompletion F)ˣ →* ℝ≥0ˣ := Units.map nnNormHom.toMonoidHom
    let chart𝔭 := quasiCharacterNormTwist m𝔭 (continuous_finiteLocalModule v)
      ((circleToComplex).comp η)
    ∃ T : ℝ, 0 < T ∧ Periodic chart𝔭 ((T : ℂ) * Complex.I) := by
  intro m𝔭 chart𝔭
  let q := (v.asIdeal.absNorm : ℝ)
  have hq : 1 < q := by dsimp [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  let T := 2 * Real.pi / Real.log q
  refine ⟨T, div_pos (by positivity) (Real.log_pos hq), fun z ↦ ?_⟩
  ext1 u
  let k := WithZero.log (Valued.v u.val)
  have hnorm : ‖u.val‖ = q ^ k := by
    rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _
      ((Valuation.ne_zero_iff _).mpr u.ne_zero)]
    push_cast
    rfl
  have hu : 0 < ‖u.val‖ := norm_pos_iff.mpr u.ne_zero
  have hlog : Complex.log (‖u.val‖ : ℂ) = (k : ℂ) * (Real.log q : ℂ) := by
    rw [← Complex.ofReal_log hu.le, hnorm, Real.log_zpow, Complex.ofReal_mul,
      Complex.ofReal_intCast]
  have hprod : (Real.log q : ℂ) * ((T : ℂ) * Complex.I) =
      2 * (Real.pi : ℂ) * Complex.I := by
    dsimp only [T]
    push_cast
    field_simp [(Real.log_pos hq).ne']
  have hpow : (‖u.val‖ : ℂ) ^ ((T : ℂ) * Complex.I) = 1 := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hu.ne'), hlog, mul_assoc, hprod,
      Complex.exp_int_mul_two_pi_mul_I]
  change (η u : ℂ) * (‖u.val‖ : ℂ) ^ (z + (T : ℂ) * Complex.I) =
    (η u : ℂ) * (‖u.val‖ : ℂ) ^ z
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.ne'), hpow, mul_one]

/-- A continuous function periodic in the imaginary direction is bounded on every closed strip. -/
private theorem norm_bounded_on_strip_of_imag_periodic {f : ℂ → ℂ} {T : ℝ}
    (hT : 0 < T) (hperiod : Periodic f ((T : ℂ) * Complex.I))
    (hf : Continuous f) (a b : ℝ) :
    ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc a b → ‖f z‖ ≤ C := by
  let K := Complex.reProdIm (Icc a b) (Icc 0 T)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨C, hC⟩ := hK.bddAbove_image hf.norm.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z hz ↦ ?_⟩
  let n := ⌊z.im / T⌋
  let shift := (n : ℂ) * ((T : ℂ) * Complex.I)
  have hre : shift.re = 0 := by simp [shift, Complex.mul_re, Complex.mul_im]
  have him : shift.im = (n : ℝ) * T := by simp [shift, Complex.mul_re, Complex.mul_im]
  have hzK : z - shift ∈ K := by
    have hfloor := (le_div_iff₀ hT).mp (Int.floor_le (z.im / T))
    have hceil := (div_lt_iff₀ hT).mp (Int.lt_floor_add_one (z.im / T))
    change (z - shift).re ∈ Icc a b ∧ (z - shift).im ∈ Icc 0 T
    rw [Complex.sub_re, hre, sub_zero, Complex.sub_im, him]
    exact ⟨hz, ⟨by dsimp [n]; linarith, by dsimp [n]; linarith⟩⟩
  have hper : f z = f (z - shift) := by
    simpa only [shift, zsmul_eq_mul, sub_add_cancel] using (hperiod.zsmul n (z - shift))
  rw [hper]
  exact (hC ⟨z - shift, hzK, rfl⟩).trans (le_max_left _ _)

/-- The S-local epsilon factor is bounded on every closed vertical strip, and its reciprocal
is bounded on the imaginary axis. -/
private theorem epsilon_strip_and_axis_bounds (χ : PontryaginDual Jₛ) :
    (∃ E ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc (-1 : ℝ) (1 / 2) → ‖sLocalEpsilonFactor (chart(χ) z)‖ ≤ E) ∧
    (∃ E' ≥ (0 : ℝ), ∀ z : ℂ, z.re = 0 → ‖(sLocalEpsilonFactor (chart(χ) z))⁻¹‖ ≤ E') := by
  classical
  have harch (w : InfinitePlace F) (z : ℂ) :
      ‖infiniteLocalEpsilonFactor w (sLocalInfiniteRestriction w (chart(χ) z))‖ = 1 := by
    unfold infiniteLocalEpsilonFactor
    split <;> rw [norm_pow, Complex.norm_I, one_pow]
  have hfin_fwd (v : S) : ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc (-1 : ℝ) (1 / 2) →
      ‖finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chart(χ) z))‖ ≤ C := by
    obtain ⟨η, hη, _⟩ := sLocalFiniteRestriction_exists_normTwistChart χ v
    obtain ⟨T, hT, hper⟩ := finite_local_chart_periodic v.val η
    have hE : Periodic (fun z ↦ finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chart(χ) z)))
        ((T : ℂ) * Complex.I) := fun z ↦ by
      dsimp only
      rw [hη, hη, hper]
    refine norm_bounded_on_strip_of_imag_periodic hT hE ?_ (-1) (1 / 2)
    refine continuous_iff_continuousAt.mpr fun z ↦ ?_
    simp_rw [hη]
    exact ((finiteLocalEpsilonFactor_entire v.val η) z trivial).continuousAt
  have hfin_inv (v : S) : ∃ C ≥ (0 : ℝ), ∀ z : ℂ, z.re ∈ Icc (0 : ℝ) 0 →
      ‖(finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chart(χ) z)))⁻¹‖ ≤ C := by
    obtain ⟨η, hη, _⟩ := sLocalFiniteRestriction_exists_normTwistChart χ v
    obtain ⟨T, hT, hper⟩ := finite_local_chart_periodic v.val η
    have hne (z : ℂ) : finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chart(χ) z)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul (sLocalEpsilonFactor_ne_zero (chart(χ) z)))
        v (Finset.mem_univ v)
    have hE : Periodic (fun z ↦ (finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chart(χ) z)))⁻¹)
        ((T : ℂ) * Complex.I) := fun z ↦ by
      dsimp only
      rw [hη, hη, hper]
    refine norm_bounded_on_strip_of_imag_periodic hT hE ?_ 0 0
    refine (continuous_iff_continuousAt.mpr fun z ↦ ?_).inv₀ hne
    simp_rw [hη]
    exact ((finiteLocalEpsilonFactor_entire v.val η) z trivial).continuousAt
  choose Cf hCf hbf using hfin_fwd
  choose Ci hCi hbi using hfin_inv
  refine ⟨⟨∏ v : S, Cf v, Finset.prod_nonneg fun v _ ↦ hCf v, fun z hz ↦ ?_⟩,
    ⟨∏ v : S, Ci v, Finset.prod_nonneg fun v _ ↦ hCi v, fun z hz ↦ ?_⟩⟩
  · rw [sLocalEpsilonFactor, norm_mul, norm_prod, norm_prod]
    simp only [harch, Finset.prod_const_one, one_mul]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦ hbf v z hz
  · rw [sLocalEpsilonFactor, mul_inv, norm_mul, norm_inv, norm_prod]
    simp only [harch, Finset.prod_const_one, inv_one, one_mul, ← Finset.prod_inv_distrib, norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun v _ ↦ hbi v z ⟨hz.ge, hz.le⟩

/-- The product of archimedean local Euler factors along a unitary norm-twist chart agrees
with the global Hecke gamma factor of any unramified-outside-`S` extension. -/
private theorem arch_euler_prod_eq_heckeGamma (χ : PontryaginDual Jₛ)
    (ξ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hr : ideleClassNormTwist ξ 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist ξ 0, hr⟩ = chart(χ) 0) (z : ℂ) :
    (∏ w : InfinitePlace F, infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chart(χ) z))) =
      heckeGammaFactor ξ z := by
  classical
  have hres (w : InfinitePlace F) :
      sLocalInfiniteRestriction w (chart(χ) z) =
        infinitePlaceRestriction F w (ideleClassNormTwist ξ z) := by
    ext1 x
    let i : (SAdeleRing F S)ˣ := (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
      ((v : S) → v.val.adicCompletion F)).symm
      (ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w x), 1)
    have hi : sIdeleInsertion F S i = IdeleGroup.ofCompletion (𝓞 F) F w x := by
      obtain ⟨ha, hf, ho⟩ := sIdeleInsertion_apply F S i
      apply Units.ext
      apply Prod.ext
      · rw [ha]
        funext u
        change ((Pi.mulSingle (M := fun t : InfinitePlace F ↦ t.Completionˣ) w x u :
          u.Completionˣ) : u.Completion) =
          Pi.mulSingle (M := fun t : InfinitePlace F ↦ t.Completion) w (x : w.Completion) u
        by_cases hu : u = w
        · subst u; simp
        · simp [Pi.mulSingle_eq_of_ne hu]
      · apply RestrictedProduct.ext
        intro v
        change (sIdeleInsertion F S i).val.2 v = 1
        by_cases hv : v ∈ S
        · exact hf ⟨v, hv⟩
        · exact ho v hv
    have hbase := DFunLike.congr_fun he (QuotientGroup.mk i)
    rw [sIdeleRestriction_mk] at hbase
    change (ξ (QuotientGroup.mk (sIdeleInsertion F S i)) : ℂ) * _ ^ (0 : ℂ) =
      (χ (QuotientGroup.mk i) : ℂ) * _ ^ (0 : ℂ) at hbase
    simp only [Complex.cpow_zero, mul_one] at hbase
    change (χ (QuotientGroup.mk i) : ℂ) * (((mₛ (QuotientGroup.mk i) : ℝ≥0) : ℝ) : ℂ) ^ z =
      (ξ (QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 F) F w x)) : ℂ) *
        (((ideleClassNorm F (QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 F) F w x)) : ℝ≥0) : ℝ) : ℂ) ^ z
    rw [← hi, ← hbase, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  unfold heckeGammaFactor
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  rw [hres w]
  let c := infinitePlaceRestriction F w (ideleClassNormTwist ξ z)
  let c₀ := infinitePlaceRestriction F w (ideleClassNormTwist ξ 0)
  have htwist (x : w.Completionˣ) : c x = c₀ x * ((‖x.val‖ ^ w.mult : ℝ) : ℂ) ^ z := by
    let g := IdeleClassGroup.ofCompletion (𝓞 F) F w x
    change (ξ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ z =
      (ξ g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) * _
    rw [Complex.cpow_zero, mul_one, ideleClassNorm_ofCompletion]
    rfl
  change infiniteLocalEulerFactor w c = _
  by_cases hw : w.IsReal
  · let a := (realHeckeCharacter_parameters ξ w hw).exists.choose
    have ha := (realHeckeCharacter_parameters ξ w hw).exists.choose_spec.2
    have hshape : ∀ x : ℝˣ,
        c (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom x) =
          ((‖(x : ℝ)‖ : ℝ) : ℂ) ^ (z + a.1) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ a.2.val := by
      intro x
      have hn : ‖((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (x : ℝ) : w.Completion)‖ =
          ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm) (x : ℝ)
      have hx : (‖(x : ℝ)‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
      rw [htwist, ha, Complex.cpow_add _ _ hx]
      change _ * ((‖((InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm (x : ℝ) : w.Completion)‖ ^
        w.mult : ℝ) : ℂ) ^ z = _
      simp only [hn, InfinitePlace.mult, hw, ite_true, pow_one]
      ac_rfl
    have hp := (realLocalEulerParameters w hw c).unique
      (realLocalEulerParameters w hw c).exists.choose_spec (y₂ := (z + a.1, a.2)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hp, a]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let a := (complexHeckeCharacter_parameters ξ w hc).exists.choose
    have ha := (complexHeckeCharacter_parameters ξ w hc).exists.choose_spec.2
    have hshape : ∀ x : ℂˣ,
        c (Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toMonoidHom x) =
          ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z + a.1) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ a.2 := by
      intro x
      have hn : ‖((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (x : ℂ) : w.Completion)‖ =
          ‖(x : ℂ)‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm) (x : ℂ)
      have hx : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero))
      rw [htwist, ha, Complex.cpow_add _ _ hx]
      change _ * ((‖((InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm (x : ℂ) : w.Completion)‖ ^
        w.mult : ℝ) : ℂ) ^ z = _
      simp only [hn, InfinitePlace.mult, hw, ite_false]
      ac_rfl
    have hp := (complexLocalEulerParameters w hc c).unique
      (complexLocalEulerParameters w hc c).exists.choose_spec (y₂ := (z + a.1, a.2)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hp, a]

/-- Inverse partial Euler product identity for the conjugate extension `ξ⁻¹`. -/
private theorem inv_partialEulerProduct (χ : PontryaginDual Jₛ)
    (ξ : PontryaginDual (IdeleClassGroup (𝓞 F) F))
    (hr : ideleClassNormTwist ξ 0 ∈ unramifiedOutside F S)
    (he : sIdeleRestriction F S ⟨ideleClassNormTwist ξ 0, hr⟩ = chart(χ) 0) (w : ℂ) :
    sLocalHeckeL (chart(χ⁻¹) w) =
      heckeGammaFactor ξ⁻¹ w * ∏ v : S, finiteHeckeEulerFactor ξ⁻¹ v.val w := by
  have hξ (g : IdeleClassGroup (𝓞 F) F) :
      ideleClassNormTwist ξ⁻¹ 0 g = (ideleClassNormTwist ξ 0 g)⁻¹ := by
    change (((ξ g)⁻¹ : Circle) : ℂ) * _ ^ (0 : ℂ) = ((ξ g : ℂ) * _ ^ (0 : ℂ))⁻¹
    simp
  have hr' : ideleClassNormTwist ξ⁻¹ 0 ∈ unramifiedOutside F S := by
    rw [mem_unramifiedOutside_iff] at hr ⊢
    intro v hv u
    exact (hξ _).trans ((congrArg Inv.inv (hr v hv u)).trans inv_one)
  apply sLocalHeckeL_eq_partialEulerProduct χ⁻¹ ξ⁻¹ hr' _ w
  ext1 x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [sIdeleRestriction_mk, hξ]
  have hb := DFunLike.congr_fun he (QuotientGroup.mk g)
  rw [sIdeleRestriction_mk] at hb
  rw [hb]
  change ((χ (QuotientGroup.mk g) : ℂ) * _ ^ (0 : ℂ))⁻¹ =
    (((χ (QuotientGroup.mk g))⁻¹ : Circle) : ℂ) * _ ^ (0 : ℂ)
  simp

/-- Removing simple poles from a finite product of meromorphic functions produces an
analytic germ near zero. -/
private theorem clear_simple_poles_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : Finset ι) (L : ι → ℂ → ℂ)
    (hP : ∀ i, i ∈ P ↔ meromorphicOrderAt (L i) 0 < 0)
    (hL : ∀ i, MeromorphicNFAt (L i) 0 ∧ ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (L i) 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), H z = z ^ P.card * ∏ i, L i z := by
  classical
  have reg (i : ι) : ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), G z = (if i ∈ P then z else 1) * L i z := by
    by_cases hi : i ∈ P
    · have hp := (hP i).mp hi
      have ho : meromorphicOrderAt (L i) 0 = ((-1 : ℤ) : WithTop ℤ) := by
        apply le_antisymm _ (hL i).2
        generalize heq : meromorphicOrderAt (L i) 0 = o at hp ⊢
        induction o using WithTop.recTopCoe with
        | top => simp at hp
        | coe n =>
          have hn : n < 0 := by exact_mod_cast hp
          exact_mod_cast (by omega : n ≤ -1)
      obtain ⟨G, hG, _, he⟩ := (meromorphicOrderAt_eq_int_iff (hL i).1.meromorphicAt).mp ho
      refine ⟨G, hG, ?_⟩
      filter_upwards [he, self_mem_nhdsWithin] with z hz hz0
      have hne : z ≠ 0 := hz0
      rw [ite_eq_left hi, hz, sub_zero, smul_eq_mul, zpow_neg_one]
      field_simp [hne]
    · exact ⟨L i, (hL i).1.meromorphicOrderAt_nonneg_iff_analyticAt.mp
        (not_lt.mp (mt (hP i).mpr hi)), .of_forall fun z ↦ by simp [hi]⟩
  choose G hA he using reg
  refine ⟨fun z ↦ ∏ i, G i z, Finset.univ.analyticAt_fun_prod (fun i _ ↦ hA i), ?_⟩
  filter_upwards [eventually_all.mpr he] with z hz
  simp only [hz, Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_const]

/-- Unconditional polynomial bound on the cleared archimedean/reflected factor along a fixed
unitary chart `χ`. -/
private theorem cleared_arch_germ (p : Vℚ) (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) :
    let A (c : Xₛ) := sLocalEpsilonFactor c *
      ((∏ w : InfinitePlace F, infiniteLocalEulerFactor w (sLocalInfiniteRestriction w c)) /
        sLocalHeckeL (dualₛ c))
    ∃ R > (0 : ℝ), ∃ e : ℕ, ∃ B ≥ (0 : ℝ), ∀ (j : Idx(p, ω)) (s : ℂ), j.val.1 = chart(χ) s →
      ∃ G : ℂ → ℂ, AnalyticOnNhd ℂ G (Metric.closedBall 0 R) ∧
        (G =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦ z ^ (sLocalArchPolePlaces j.val.1).card * A (twistₛ j.val.1 z)) ∧
        ∀ z ∈ Metric.closedBall 0 R, ‖G z / G 0‖ ≤ B * (1 + ‖s‖) ^ e := by
  classical
  intro A
  obtain ⟨ξ, hr, he, _⟩ := sLocal_character_extension χ
  have hshift (t z : ℂ) : twistₛ (chart(χ) t) z = chart(χ) (t + z) := twist_twist _ t z
  -- Every primary pole center on `chart(χ)` lies on the imaginary axis.
  have hre (j : Idx(p, ω)) (s : ℂ) (hs : j.val.1 = chart(χ) s) : s.re = 0 := by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le _) j.property.2)
    have hneg := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
    let E (z : ℂ) := finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chart(χ) z))
    have ht : meromorphicOrderAt E s < 0 := by
      have heq : (fun z ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ j.val.1 z))) =
          E ∘ (· + s) := by
        funext z
        dsimp only [Function.comp_apply, E]
        rw [hs, hshift, add_comm]
      rw [heq, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add] at hneg
      exact hneg
    obtain ⟨π, hπ, h⟩ := sLocalRhoFactor_poles_iff_finite χ v
    obtain ⟨_, heq⟩ := ((h s).2.1).mp ((sLocalRhoPoleOrder_eq_card_polePlaces_finite χ v s).mp ht)
    have hn := congrArg norm heq
    change ‖(((χ _ : Circle) : ℂ) * (_ : ℂ) ^ (0 : ℂ)) * (‖π.val‖ : ℂ) ^ s‖ = ‖(1 : ℂ)‖ at hn
    have hreal := norm_pos_iff.mpr π.ne_zero
    rw [Complex.cpow_zero, mul_one, norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos hreal, norm_one] at hn
    have hlt : ‖π.val‖ < 1 :=
      hπ.trans_lt (inv_lt_one_of_one_lt₀ (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val))
    have hl := congrArg Real.log hn
    rw [Real.log_rpow hreal, Real.log_one, mul_eq_zero] at hl
    exact hl.resolve_right (Real.log_neg hreal hlt).ne
  -- Only finitely many centers lie in any bounded disk.
  have hfinite (B : ℝ) : ({s : ℂ | ∃ j : Idx(p, ω), j.val.1 = chart(χ) s} ∩
      Metric.closedBall 0 B).Finite := by
    let K := Metric.closedBall (0 : ℂ) B
    let f := sLocalRhoFactor ∘ (fun z ↦ chart(χ) z)
    refine ((MeromorphicOn.divisor f K).finiteSupport (isCompact_closedBall _ _)).subset ?_
    rintro s ⟨⟨j, hs⟩, hj⟩
    change MeromorphicOn.divisor f K s ≠ 0
    have hmer : MeromorphicOn f K := fun z _ ↦ sLocalRhoFactor_meromorphic χ z
    rw [MeromorphicOn.divisor_apply hmer hj]
    change (meromorphicOrderAt f s).untop₀ ≠ 0
    have hpole : 0 < sLocalRhoPoleOrder j.val.1 :=
      lt_of_le_of_lt (Nat.zero_le _) (j.property.2.trans_le (by
        rw [sLocalRhoPoleOrder_eq_card_polePlaces]
        exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)))
    have hord : meromorphicOrderAt f s = ((-(sLocalRhoPoleOrder j.val.1 : ℤ) : ℤ) : WithTop ℤ) := by
      have h := sLocalIdelicOrderBound_eq_neg_poleOrder j.val.1
      have heq : (fun z ↦ sLocalRhoFactor (twistₛ j.val.1 z)) = f ∘ (· + s) := by
        funext z; dsimp [f]; rw [hs, hshift, add_comm]
      change min 0 (meromorphicOrderAt (fun z ↦ sLocalRhoFactor (twistₛ j.val.1 z)) 0) = _ at h
      rw [heq, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add] at h
      have hn : ((-(sLocalRhoPoleOrder j.val.1 : ℤ) : ℤ) : WithTop ℤ) < 0 := by
        exact_mod_cast (neg_neg_of_pos (Int.natCast_pos.mpr hpole))
      exact (min_eq_right ((min_lt_iff.mp (h.trans_lt hn)).resolve_left (lt_irrefl _)).le).symm.trans h
    rw [hord]
    simpa using hpole.ne'
  -- Large-height strip estimate on `Metric.closedBall 0 (1/2)`.
  have hstrip : ∃ Y : ℝ, ∃ e : ℕ, ∃ B ≥ (0 : ℝ), ∀ s : ℂ, s.re = 0 → Y ≤ |s.im| →
      (sLocalArchPolePlaces (chart(χ) s)).card = 0 ∧
      AnalyticOnNhd ℂ (fun z ↦ A (chart(χ) (s + z))) (Metric.closedBall 0 (1 / 2)) ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) (1 / 2),
        ‖A (chart(χ) (s + z)) / A (chart(χ) s)‖ ≤ B * (1 + ‖s‖) ^ e := by
    let eps (z : ℂ) := sLocalEpsilonFactor (chart(χ) z)
    let Γ := heckeGammaFactor ξ
    let Γ' (z : ℂ) := heckeGammaFactor ξ⁻¹ (1 - z)
    let Dfin (z : ℂ) := ∏ v : S, finiteHeckeEulerFactor ξ⁻¹ v.val (1 - z)
    have hval (z : ℂ) : A (chart(χ) z) = eps z * (Γ z / Γ' z) * (Dfin z)⁻¹ := by
      dsimp only [A, eps, Γ, Γ', Dfin]
      rw [arch_euler_prod_eq_heckeGamma χ ξ hr he z, sLocalNormTwistChart_dual,
        inv_partialEulerProduct χ ξ hr he]
      simp only [div_eq_mul_inv, mul_inv]
      ring
    obtain ⟨⟨E, hE, hε⟩, ⟨E', hE', hε'⟩⟩ := epsilon_strip_and_axis_bounds χ
    obtain ⟨G, Y, hG, _, hγ_ref⟩ := heckeGamma_reflection_bound ξ⁻¹ (1 / 2) 2
    have hγ : ∀ z : ℂ, -1 ≤ z.re → z.re ≤ 1 / 2 → max Y 1 ≤ |z.im| → ‖Γ z / Γ' z‖ ≤ G := by
      intro z ha hb ht
      have hre1 : (1 - z).re = 1 - z.re := by simp
      have him1 : |(1 - z).im| = |z.im| := by simp
      have hh := hγ_ref (1 - z) (by rw [hre1]; linarith) (by rw [hre1]; linarith)
        (him1 ▸ (le_max_left _ _).trans ht)
      rw [inv_inv, sub_sub_cancel, him1, hre1] at hh
      refine hh.trans (mul_le_of_le_one_right hG.le ?_)
      exact Real.rpow_le_one_of_one_le_of_nonpos ((le_max_right _ _).trans ht)
        (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith))
    obtain ⟨G', Y', hG', _, hγ'⟩ := heckeGamma_reflection_bound ξ 0 0
    -- Positive-half-plane bound on `Dfin(z)⁻¹`.
    let Vb (v : S) := 1 + ‖(ideleClassNormTwist ξ⁻¹ 0).localValue v.val‖
    let D₀ : ℝ := ∏ v : S, Vb v
    have hD₀ : 0 ≤ D₀ := Finset.prod_nonneg fun v _ ↦ by dsimp [Vb]; positivity
    have hD_inv (w : ℂ) (hw : 0 ≤ w.re) : ‖∏ v : S, (finiteHeckeEulerFactor ξ⁻¹ v.val w)⁻¹‖ ≤ D₀ := by
      rw [norm_prod]
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro v _
      unfold finiteHeckeEulerFactor
      split_ifs
      · rw [inv_inv]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_one, norm_mul]
        have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
          exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
        have hpow : ‖(v.val.asIdeal.absNorm : ℂ) ^ (-w)‖ ≤ 1 := by
          rw [← Complex.ofReal_natCast,
            Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hq)]
          exact Real.rpow_le_one_of_one_le_of_nonpos hq.le (by simpa using hw)
        exact add_le_add_right (mul_le_of_le_one_right (norm_nonneg _) hpow) _
      · simp [Vb]
    have hD_fwd (w : ℂ) (hw : w.re = 1) : ‖∏ v : S, finiteHeckeEulerFactor ξ⁻¹ v.val w‖ ≤ 2 ^ Fintype.card S := by
      rw [norm_prod]
      change _ ≤ (2 : ℝ) ^ (Finset.univ : Finset S).card
      rw [← Finset.prod_const]
      apply Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _)
      intro v _
      unfold finiteHeckeEulerFactor
      split_ifs
      · let q : ℝ := v.val.asIdeal.absNorm
        have hq : 2 ≤ q := by
          dsimp [q]
          exact_mod_cast NumberField.HeightOneSpectrum.two_le_absNorm_nnreal v.val
        let u := (ideleClassNormTwist ξ⁻¹ 0).localValue v.val * (q : ℂ) ^ (-w)
        have hu : ‖u‖ ≤ 1 / 2 := by
          rw [show ‖u‖ = _ from norm_mul _ _, norm_ideleClassNormTwist_zero_localValue, one_mul,
            Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < q), Complex.neg_re, hw,
            Real.rpow_neg_one]
          exact (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by simpa using hq)
        change ‖(1 - u)⁻¹‖ ≤ 2
        have h := norm_sub_norm_le (1 : ℂ) u
        rw [norm_one] at h
        rw [norm_inv]
        exact (inv_le_comm₀ (by linarith) (by norm_num)).mpr (by linarith)
      · norm_num
    -- Gamma is nonzero at large imaginary part.
    have hΓ_ne : ∀ᶠ z in comap (fun z : ℂ ↦ |z.im|) atTop, Γ z ≠ 0 := by
      have hgam {z : ℂ} (h : z.im ≠ 0) : Complex.Gammaℝ z ≠ 0 := by
        intro hz
        obtain ⟨n, rfl⟩ := Complex.Gammaℝ_eq_zero_iff.mp hz
        exact h (by simp)
      have him (a : ℂ) : ∀ᶠ z in comap (fun z : ℂ ↦ |z.im|) atTop, z.im + a.im ≠ 0 := by
        filter_upwards [tendsto_comap.eventually_gt_atTop |a.im|] with z hz heq
        rw [eq_neg_of_add_eq_zero_left heq, abs_neg] at hz
        exact lt_irrefl _ hz
      unfold Γ heckeGammaFactor
      simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_const, eventually_all]
      intro w
      by_cases hw : w.IsReal
      · simp only [dite_eq_left hw]
        exact (him (realHeckeCharacter_parameters ξ w hw).exists.choose.1).mono fun z hz ↦
          hgam (by simpa using hz)
      · let a := (complexHeckeCharacter_parameters ξ w
          (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
        filter_upwards [him a.1] with z hz
        simp only [dite_eq_right hw]
        change Complex.Gammaℂ (z + a.1 + (a.2.natAbs : ℂ) / 2) / 2 ≠ 0
        rw [← Complex.Gammaℝ_mul_Gammaℝ_add_one]
        exact div_ne_zero (mul_ne_zero (hgam (by simpa using hz)) (hgam (by simpa using hz)))
          two_ne_zero
    obtain ⟨Y₀, hY₀⟩ := eventually_atTop.mp
      ((eventually_comap (f := fun z : ℂ ↦ |z.im|) (p := fun z ↦ Γ z ≠ 0)).mp hΓ_ne)
    let n := Module.finrank ℚ F
    refine ⟨max (max (max Y 1) Y') (max Y₀ 1) + 1, n, (E * G * D₀) * (E' * G' * 2 ^ Fintype.card S),
      by positivity, fun s hs hys ↦ ?_⟩
    have hy : max Y 1 + 1 ≤ |s.im| ∧ Y' ≤ |s.im| ∧ Y₀ + 1 ≤ |s.im| ∧ 1 ≤ |s.im| := by
      have h1 := le_max_left (max (max Y 1) Y') (max Y₀ 1)
      have h2 := le_max_right (max (max Y 1) Y') (max Y₀ 1)
      have h3 := le_max_left (max Y 1) Y'
      have h4 := le_max_right (max Y 1) Y'
      have h5 := le_max_left Y₀ 1
      have h6 := le_max_right Y₀ 1
      exact ⟨by linarith, by linarith, by linarith, by linarith⟩
    have near (z : ℂ) (hz : z ∈ Metric.closedBall 0 (1 / 2)) :
        (s + z).re ∈ Icc (-1 : ℝ) (1 / 2) ∧ max Y 1 ≤ |(s + z).im| ∧ Γ (s + z) ≠ 0 := by
      have hn := mem_closedBall_zero_iff.mp hz
      have hb := abs_le.mp ((Complex.abs_re_le_norm z).trans hn)
      have hi := (Complex.abs_im_le_norm z).trans hn
      have ht : |s.im| ≤ |(s + z).im| + |z.im| := by
        simpa [Complex.add_im] using abs_sub (s.im + z.im) z.im
      refine ⟨by rw [Complex.add_re, hs, zero_add]; constructor <;> linarith,
        by linarith [hy.1], hY₀ |(s + z).im| (by linarith [hy.2.2.1]) (s + z) rfl⟩
    have hΓs : Γ s ≠ 0 := hY₀ |s.im| (by linarith [hy.2.2.1]) s rfl
    have hzero : sLocalArchPolePlaces (chart(χ) s) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      have hwne := Finset.prod_ne_zero_iff.mp
        ((arch_euler_prod_eq_heckeGamma χ ξ hr he s).trans_ne hΓs) w (Finset.mem_univ w)
      have ht : twistₛ (chart(χ) s) 0 = chart(χ) s := by
        ext1 x; exact (congrArg (chart(χ) s x * ·) (Complex.cpow_zero _)).trans (mul_one _)
      exact (Finset.mem_filter.mp hw).2.ne
        ((sLocalPrincipalPartCoeff_leading_formula_arch_factor (chart(χ) s) w).1.meromorphicOrderAt_eq_zero_iff.mpr
          (by simpa only [ht] using hwne))
    refine ⟨by rw [hzero, Finset.card_empty], fun z hz ↦ ?_, fun z hz ↦ ?_⟩
    · have hGz : AnalyticAt ℂ Γ (s + z) := by
        simpa only [Pi.inv_def, inv_inv, Γ] using
          ((differentiable_inv_heckeGammaFactor ξ).analyticAt (s + z)).inv
            (inv_ne_zero (near z hz).2.2)
      have hzeta := ((sLocalHeckeL_inv_differentiable χ⁻¹).analyticAt (1 - (s + z))).comp
        (f := fun w : ℂ ↦ 1 - w) (analyticAt_const.sub analyticAt_id)
      have hA_at : AnalyticAt ℂ (fun w ↦ A (chart(χ) w)) (s + z) := by
        dsimp only [A]
        simp only [arch_euler_prod_eq_heckeGamma χ ξ hr he, sLocalNormTwistChart_dual, div_eq_mul_inv]
        exact ((sLocalEpsilonFactor_entire χ) (s + z) trivial).mul (hGz.mul hzeta)
      exact hA_at.comp (f := fun w : ℂ ↦ s + w) (analyticAt_const.add analyticAt_id)
    · obtain ⟨hzr, hzy, _⟩ := near z hz
      have hf : ‖(Dfin (s + z))⁻¹‖ ≤ D₀ := by
        simpa only [Dfin, Finset.prod_inv_distrib] using
          hD_inv (1 - (s + z)) (by rw [Complex.sub_re, Complex.one_re]; linarith [hzr.2])
      have hF : ‖Dfin s‖ ≤ 2 ^ Fintype.card S := hD_fwd (1 - s) (by simp [hs])
      have hforward : ‖A (chart(χ) (s + z))‖ ≤ E * G * D₀ := by
        rw [hval, norm_mul, norm_mul]
        exact mul_le_mul (mul_le_mul (hε _ hzr) (hγ _ hzr.1 hzr.2 hzy) (norm_nonneg _) hE)
          hf (norm_nonneg _) (by positivity)
      have hinverse : ‖(A (chart(χ) s))⁻¹‖ ≤ E' * (G' * (1 + ‖s‖) ^ n) * 2 ^ Fintype.card S := by
        rw [hval, mul_inv, mul_inv, inv_inv, inv_div, norm_mul, norm_mul]
        apply mul_le_mul _ hF (norm_nonneg _) (by positivity)
        apply mul_le_mul (hε' s hs) _ (norm_nonneg _) hE'
        have h := hγ' s hs.ge hs.le hy.2.1
        refine h.trans (mul_le_mul_of_nonneg_left ?_ hG'.le)
        rw [hs, sub_zero]
        have hexp : (n : ℝ) * (1 / 2) ≤ (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
        refine (Real.rpow_le_rpow_of_exponent_le hy.2.2.2 hexp).trans ?_
        rw [Real.rpow_natCast]
        exact pow_le_pow_left₀ (abs_nonneg _)
          ((Complex.abs_im_le_norm s).trans (le_add_of_nonneg_left zero_le_one)) _
      rw [div_eq_mul_inv, norm_mul]
      exact (mul_le_mul hforward hinverse (norm_nonneg _) (by positivity)).trans_eq (by ring)
  -- Patch the finitely many low-height centers with the large-height strip bound.
  obtain ⟨Y, e, B, hB, hstrip⟩ := hstrip
  let J := {s : ℂ | ∃ j : Idx(p, ω), j.val.1 = chart(χ) s} ∩ Metric.closedBall 0 Y
  let : Finite J := (hfinite Y).to_subtype
  have low (t : J) :
      ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦
        z ^ (sLocalArchPolePlaces (chart(χ) t)).card * A (twistₛ (chart(χ) t) z) := by
    let c := chart(χ) t
    let P := sLocalArchPolePlaces c
    let L (w : InfinitePlace F) (z : ℂ) :=
      infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ c z))
    obtain ⟨K, hK, heK⟩ := clear_simple_poles_product P L
      (fun w ↦ by simp [P, sLocalArchPolePlaces, L])
      (sLocalPrincipalPartCoeff_leading_formula_arch_factor c)
    let ε (z : ℂ) := sLocalEpsilonFactor (chart(χ) (t + z))
    let D (z : ℂ) := (sLocalHeckeL (dualₛ (chart(χ) (t + z))))⁻¹
    have hε : AnalyticAt ℂ ε 0 :=
      ((sLocalEpsilonFactor_entire χ) _ trivial).comp (analyticAt_const.add analyticAt_id)
    have hD : AnalyticAt ℂ D 0 := by
      dsimp only [D]
      simp only [sLocalNormTwistChart_dual]
      exact ((sLocalHeckeL_inv_differentiable χ⁻¹).analyticAt _).comp
        (analyticAt_const.sub (analyticAt_const.add analyticAt_id))
    refine ⟨fun z ↦ ε z * K z * D z, (hε.mul hK).mul hD, ?_⟩
    filter_upwards [heK] with z hz
    rw [hz]
    dsimp only [A, ε, D, L, P, c]
    rw [hshift, div_eq_mul_inv]
    ring
  choose G hG hGe using low
  have hnear (t : J) : ∀ᶠ z in 𝓝 (0 : ℂ), AnalyticAt ℂ (G t) z ∧ ‖G t z / G t 0‖ < 2 := by
    apply (hG t).eventually_analyticAt.and
    apply ((hG t).continuousAt.div_const _).norm.eventually_lt continuousAt_const
    by_cases h : G t 0 = 0 <;> simp [h]
  obtain ⟨R, hR, hlow⟩ := Metric.nhds_basis_closedBall.eventually_iff.mp (eventually_all.mpr hnear)
  refine ⟨min R (1 / 2), lt_min hR (by norm_num), e, max 2 B, by positivity, fun j s hs ↦ ?_⟩
  rw [hs]
  by_cases h : Y ≤ |s.im|
  · obtain ⟨hm, ha, hb⟩ := hstrip s (hre j s hs) h
    refine ⟨fun z ↦ A (chart(χ) (s + z)),
      ha.mono (Metric.closedBall_subset_closedBall (min_le_right _ _)),
      .of_forall (fun z ↦ by simp only [hm, pow_zero, one_mul, hshift]), fun z hz ↦ ?_⟩
    simp only [add_zero]
    exact (hb z (Metric.closedBall_subset_closedBall (min_le_right _ _) hz)).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  · have ht : s ∈ J := ⟨⟨j, hs⟩, mem_closedBall_zero_iff.mpr (by
      have hb := Complex.norm_le_abs_re_add_abs_im s
      rw [hre j s hs, abs_zero, zero_add] at hb
      exact hb.trans (le_of_not_ge h))⟩
    let t : J := ⟨s, ht⟩
    refine ⟨G t, fun z hz ↦ (hlow (Metric.closedBall_subset_closedBall (min_le_left _ _) hz) t).1,
      hGe t, fun z hz ↦ ?_⟩
    exact (hlow (Metric.closedBall_subset_closedBall (min_le_left _ _) hz) t).2.le.trans
      ((le_max_left _ _).trans
        (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))))

/-- Paper: Theorem 7.3.1.6, p. 349, and Theorem 7.3.3.4, pp. 360–363.
Unconditional polynomial bound on the difference between the first Laurent ratio
`rhoCoeff(c, 1) / rhoCoeff(c, 0)` and the weighted finite Euler sum `∑ v : S, log(N v) * b(c, v)`
along every unitary norm-twist chart. -/
theorem sLocalRho_firstLaurentRatio_sub_eulerSum_poly_bound
    (p : Vℚ) (ω : PontryaginDual J₁) (χ : PontryaginDual Jₛ) :
    ∃ e : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ (j : Idx(p, ω)) (s : ℂ), j.val.1 = chart(χ) s →
      ‖rhoCoeff(j.val.1, 1) / rhoCoeff(j.val.1, 0) -
        ∑ v : S, (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) *
          (if finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1) = 0 then 0
           else 1 - finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1))‖
        ≤ B * (1 + ‖s‖) ^ e := by
  classical
  obtain ⟨R₁, hR₁, e, B₁, hB₁, harch⟩ := cleared_arch_germ (F := F) (S := S) p ω χ
  obtain ⟨R₂, hR₂, hfin⟩ := cleared_finite_germ (F := F) (S := S)
  let R := min R₁ R₂
  have hR : 0 < R := lt_min hR₁ hR₂
  let M : ℝ := B₁ * 2 ^ Fintype.card S
  refine ⟨e, M / R, by positivity, fun j s hs ↦ ?_⟩
  obtain ⟨Ga, hGa, hGae, hGab⟩ := harch j s hs
  obtain ⟨Kf, hKf, hKfe, hKfb⟩ := hfin j.val.1
  let G (z : ℂ) := Ga z * Kf z
  have hG : AnalyticOnNhd ℂ G (Metric.closedBall 0 R) :=
    (hGa.mono (Metric.closedBall_subset_closedBall (min_le_left _ _))).mul
      (hKf.mono (Metric.closedBall_subset_closedBall (min_le_right _ _)))
  have hGe : G =ᶠ[𝓝[≠] (0 : ℂ)] fun z ↦
      z ^ sLocalRhoPoleOrder j.val.1 * sLocalRhoFactor (twistₛ j.val.1 z) *
        ∏ v : S, (1 + (if finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1) = 0 then 0
          else 1 - finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1)) *
          (Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z) - 1)) := by
    have ht : Tendsto (fun z : ℂ ↦ s + z) (𝓝[≠] 0) (𝓝[≠] (s + 0)) :=
      ((Homeomorph.addLeft s).map_punctured_nhds_eq 0).le
    filter_upwards [hGae, hKfe, ht.eventually (nhdsNE_le_codiscrete (s + 0)
      (sLocalRhoFactor_eq_epsilon_mul χ))] with z h₁ h₂ h₃
    have hρ : sLocalRhoFactor (twistₛ j.val.1 z) = sLocalEpsilonFactor (twistₛ j.val.1 z) *
        (sLocalHeckeL (twistₛ j.val.1 z) / sLocalHeckeL (dualₛ (twistₛ j.val.1 z))) := by
      simpa only [hs, twist_twist] using h₃
    change Ga z * Kf z = _
    rw [h₁, h₂, hρ, sLocalRhoPoleOrder_eq_card_polePlaces, pow_add]
    dsimp only [sLocalHeckeL]
    ring
  -- Show `G 0 = rhoCoeff(j.val.1, 0) ≠ 0`.
  have hG0 : G 0 ≠ 0 := by
    let b (v : S) : ℂ :=
      if finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1) = 0 then 0
      else 1 - finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1)
    let D (z : ℂ) : ℂ :=
      ∏ v : S, (1 + b v * (Complex.exp (-(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * z) - 1))
    have hD0 : D 0 = 1 := by simp [D]
    have hD_an : AnalyticAt ℂ D 0 :=
      Finset.univ.analyticAt_fun_prod fun v _ ↦ by fun_prop
    have hF_an : AnalyticAt ℂ (fun z ↦ G z / D z) 0 :=
      (hG 0 (Metric.mem_closedBall_self hR.le)).div hD_an (by rw [hD0]; exact one_ne_zero)
    have hrho0 : rhoCoeff(j.val.1, 0) = G 0 := by
      have h1 : rhoCoeff(j.val.1, 0) = (G 0 / D 0) :=
        (mem_sLocalThetaPoleBound_iff_residue_congr (h := fun z ↦ (G z / D z) / (z - 0)) (by
          have hDne : ∀ᶠ z in 𝓝 (0 : ℂ), D z ≠ 0 :=
            hD_an.continuousAt.eventually_ne (by rw [hD0]; exact one_ne_zero)
          filter_upwards [hGe, nhdsWithin_le_nhds hDne, self_mem_nhdsWithin] with z hgz hdz hne
          have hn : z ≠ 0 := hne
          rw [hgz, mul_div_cancel_right₀ _ hdz, sub_zero, ← zpow_natCast z (sLocalRhoPoleOrder j.val.1),
            mul_comm (z ^ (sLocalRhoPoleOrder j.val.1 : ℤ)), mul_div_assoc, div_eq_mul_inv,
            ← zpow_neg_one, ← zpow_add₀ hn]
          congr 2)).trans (complexResidue_div_sub hF_an)
      simpa only [hD0, div_one] using h1
    rw [← hrho0]
    exact (polar_leading_formula j 0).1
  rw [sLocalRho_firstLaurentRatio_eq_logDeriv_add_eulerSum j.val.1 G
    (hG 0 (Metric.mem_closedBall_self hR.le)) hG0 hGe, add_sub_cancel_right]
  -- Apply Cauchy's derivative estimate to `z ↦ G z / G 0` on `sphere 0 R`.
  have hdiff : DiffContOnCl ℂ (fun z ↦ G z / G 0) (Metric.ball 0 R) :=
    (hG.differentiableOn.div_const _).diffContOnCl_ball Subset.rfl
  have hsphere : ∀ z ∈ Metric.sphere (0 : ℂ) R, ‖G z / G 0‖ ≤ M * (1 + ‖s‖) ^ e := by
    intro z hz
    have hzb : z ∈ Metric.closedBall (0 : ℂ) R := Metric.sphere_subset_closedBall hz
    change ‖(Ga z * Kf z) / (Ga 0 * Kf 0)‖ ≤ _
    rw [mul_div_mul_comm, norm_mul]
    have h1 := hGab z (Metric.closedBall_subset_closedBall (min_le_left _ _) hzb)
    have h2 := hKfb z (Metric.closedBall_subset_closedBall (min_le_right _ _) hzb)
    exact (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)).trans_eq (by dsimp [M]; ring)
  have hcauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hdiff hsphere
  have hderiv_div : deriv (fun z ↦ G z / G 0) 0 = deriv G 0 / G 0 :=
    deriv_div_const (G 0)
  rw [hderiv_div] at hcauchy
  exact hcauchy.trans_eq (by ring)

open Classical in
/-- Paper: Theorem 7.3.1.6(2)–(3), p. 349, and Theorem 7.3.3.4, pp. 360–363.
If the primary polar orbital system forms a Schauder basis of `Q(p, ω)`, then the weighted
sum of outside-place Euler terms `∑_{v ∉ Sₚ(p)} log(N v) * b(c, v)` is polynomially bounded
in `1 + ‖s‖` at every repeated primary pole `c = chart(χ) s`. -/
theorem sLocalPolarOrbital_outsideEulerSum_bound_of_basis
    (p : Vℚ) (ω : PontryaginDual J₁)
    (hS : IsSaturatedPlaceSet S) (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω))
    (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
    (hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hbasis : IsSchauderBasis (ψ ∘ σ) (D ∘ σ))
    (χ : PontryaginDual Jₛ) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖∑ v ∈ Finset.univ.filter (fun v : S ↦ v.val ∉ Sₚ(p)),
          (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) *
            (if finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1) = 0 then 0
             else 1 - finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1))‖
          ≤ C * (1 + ‖s‖) ^ d := by
  classical
  obtain ⟨d₁, C₁, hC₁, hcoeff⟩ :=
    sLocalPolarOrbital_laurent_bounds_of_basis p ω hS hp hPic σ D ψ hD hbasis χ
  obtain ⟨d₂, C₂, hC₂, herr⟩ :=
    sLocalRho_firstLaurentRatio_sub_eulerSum_poly_bound (F := F) (S := S) p ω χ
  let P := Finset.univ.filter (fun v : S ↦ v.val ∈ Sₚ(p))
  let O := Finset.univ.filter (fun v : S ↦ v.val ∉ Sₚ(p))
  choose Cp hCp hprim using fun v : {w : S // w.val ∈ Sₚ(p)} ↦
    primary_euler_bounded (F := F) (S := S) p ω χ v.val v.property
  let Cprim : ℝ := ∑ v ∈ P, ‖(Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ)‖ *
    (1 + if hv : v.val ∈ Sₚ(p) then Cp ⟨v, hv⟩ else 0)
  have hCprim_nn : 0 ≤ Cprim := Finset.sum_nonneg fun v _ ↦ by
    apply mul_nonneg (norm_nonneg _)
    split_ifs with hv
    · linarith [hCp ⟨v, hv⟩]
    · norm_num
  let d := max d₁ d₂
  let C := C₁ + C₂ + Cprim
  refine ⟨d, C, by linarith, fun j s hjne hs ↦ ?_⟩
  let b (v : S) : ℂ :=
    if finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1) = 0 then 0
    else 1 - finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1)
  let term (v : S) : ℂ := (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * b v
  have hsplit : ∑ v : S, term v = (∑ v ∈ P, term v) + (∑ v ∈ O, term v) :=
    (Finset.sum_filter_add_sum_filter_not Finset.univ (fun v : S ↦ v.val ∈ Sₚ(p)) term).symm
  have h1 : ‖rhoCoeff(j.val.1, 1) / rhoCoeff(j.val.1, 0)‖ ≤ C₁ * (1 + ‖s‖) ^ d₁ := by
    have hj1_lt : 1 < sLocalFinitePoleMultiplicity (Sₚ(p)) j.val.1 := by
      have := j.property.2
      omega
    let j₁ : Idx(p, ω) := ⟨(j.val.1, 1), j.property.1, hj1_lt⟩
    have hbd := hcoeff j₁ s one_ne_zero hs
    have hrho0 : 0 < ‖rhoCoeff(j.val.1, 0)‖ := norm_pos_iff.mpr (polar_leading_formula j 0).1
    rw [norm_div, div_le_iff₀ hrho0]
    exact hbd
  have h2 : ‖rhoCoeff(j.val.1, 1) / rhoCoeff(j.val.1, 0) - ∑ v : S, term v‖ ≤
      C₂ * (1 + ‖s‖) ^ d₂ := herr j s hs
  have h3 : ‖∑ v ∈ P, term v‖ ≤ Cprim := by
    refine (norm_sum_le P term).trans (Finset.sum_le_sum fun v hv ↦ ?_)
    have hv' : v.val ∈ Sₚ(p) := (Finset.mem_filter.mp hv).2
    rw [dite_eq_left hv']
    dsimp only [term]
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    dsimp only [b]
    split_ifs
    · rw [norm_zero]; linarith [hCp ⟨v, hv'⟩]
    · exact (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hprim ⟨v, hv'⟩ j s hs])
  have hsum_eq : ∑ v ∈ O, term v =
      rhoCoeff(j.val.1, 1) / rhoCoeff(j.val.1, 0) -
      (rhoCoeff(j.val.1, 1) / rhoCoeff(j.val.1, 0) - ∑ v : S, term v) -
      ∑ v ∈ P, term v := by
    rw [hsplit]
    ring
  have hW : 1 ≤ 1 + ‖s‖ := le_add_of_nonneg_right (norm_nonneg s)
  have hpow1 : (1 + ‖s‖) ^ d₁ ≤ (1 + ‖s‖) ^ d := pow_le_pow_right₀ hW (le_max_left _ _)
  have hpow2 : (1 + ‖s‖) ^ d₂ ≤ (1 + ‖s‖) ^ d := pow_le_pow_right₀ hW (le_max_right _ _)
  have hpow0 : 1 ≤ (1 + ‖s‖) ^ d := one_le_pow₀ hW
  calc
    ‖∑ v ∈ O, term v‖
        ≤ ‖rhoCoeff(j.val.1, 1) / rhoCoeff(j.val.1, 0)‖ +
          ‖rhoCoeff(j.val.1, 1) / rhoCoeff(j.val.1, 0) - ∑ v : S, term v‖ +
          ‖∑ v ∈ P, term v‖ := by
          rw [hsum_eq]
          exact (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
    _ ≤ C₁ * (1 + ‖s‖) ^ d₁ + C₂ * (1 + ‖s‖) ^ d₂ + Cprim := add_le_add (add_le_add h1 h2) h3
    _ ≤ C₁ * (1 + ‖s‖) ^ d + C₂ * (1 + ‖s‖) ^ d + Cprim * (1 + ‖s‖) ^ d := by
          refine add_le_add (add_le_add
            (mul_le_mul_of_nonneg_left hpow1 hC₁.le)
            (mul_le_mul_of_nonneg_left hpow2 hC₂))
            (le_mul_of_one_le_right hCprim_nn hpow0)
    _ = C * (1 + ‖s‖) ^ d := by dsimp [C]; ring

/-- Paper: Theorem 7.3.3.4, pp. 360–363 (necessity of the single-outside-place Euler bound #7336).
If the primary polar orbital system forms a Schauder basis of `Q(p, ω)`, `v₀ ∉ Sₚ(p)` is an
outside place, and every other outside place in `S \ Sₚ(p)` satisfies a polynomial Euler bound
on chart `χ` (vacuously true when `S \ Sₚ(p) = {v₀}`), then `v₀` itself must satisfy a
polynomial Euler bound at every repeated primary pole on chart `χ`. -/
theorem sLocalPolarOrbital_singleOutsideEuler_bound_of_basis
    (p : Vℚ) (ω : PontryaginDual J₁)
    (hS : IsSaturatedPlaceSet S) (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω))
    (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
    (hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hbasis : IsSchauderBasis (ψ ∘ σ) (D ∘ σ))
    (χ : PontryaginDual Jₛ) (v₀ : S) (hv₀ : v₀.val ∉ Sₚ(p))
    (hother : ∀ v : S, v.val ∉ Sₚ(p) → v ≠ v₀ →
      ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1)‖ ≤ C * (1 + ‖s‖) ^ d) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖finiteLocalEulerFactor v₀.val (sLocalFiniteRestriction v₀ j.val.1)‖ ≤ C * (1 + ‖s‖) ^ d := by
  classical
  obtain ⟨d₀, C₀, hC₀, hsum⟩ :=
    sLocalPolarOrbital_outsideEulerSum_bound_of_basis p ω hS hp hPic σ D ψ hD hbasis χ
  let O := Finset.univ.filter (fun v : S ↦ v.val ∉ Sₚ(p))
  let O' := O.erase v₀
  have hv₀_mem : v₀ ∈ O := Finset.mem_filter.mpr ⟨Finset.mem_univ v₀, hv₀⟩
  choose dv Cv hCv hbdv using fun v : {w : S // w ∈ O'} ↦
    hother v.val (Finset.mem_filter.mp (Finset.mem_of_mem_erase v.property)).2
      (Finset.ne_of_mem_erase v.property)
  let d_other : ℕ := Finset.univ.sup dv
  let d := max d₀ d_other
  let C_other : ℝ := ∑ v : {w : S // w ∈ O'},
    ‖(Real.log (v.val.val.asIdeal.absNorm : ℝ) : ℂ)‖ * (1 + Cv v)
  have hC_other_nn : 0 ≤ C_other := Finset.sum_nonneg fun v _ ↦
    mul_nonneg (norm_nonneg _) (by linarith [hCv v])
  have hlog_pos : 0 < Real.log (v₀.val.asIdeal.absNorm : ℝ) :=
    Real.log_pos (by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v₀.val)
  let C := 1 + (C₀ + C_other) / Real.log (v₀.val.asIdeal.absNorm : ℝ)
  refine ⟨d, C, by dsimp [C]; positivity, fun j s hjne hs ↦ ?_⟩
  let E (v : S) := finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1)
  let b (v : S) : ℂ := if E v = 0 then 0 else 1 - E v
  let term (v : S) : ℂ := (Real.log (v.val.asIdeal.absNorm : ℝ) : ℂ) * b v
  have hW : 1 ≤ 1 + ‖s‖ := le_add_of_nonneg_right (norm_nonneg s)
  have hWd : 1 ≤ (1 + ‖s‖) ^ d := one_le_pow₀ hW
  have hterm_eq : term v₀ = (∑ v ∈ O, term v) - (∑ v ∈ O', term v) :=
    eq_sub_of_add_eq (Finset.add_sum_erase O term hv₀_mem)
  have hbound_O : ‖∑ v ∈ O, term v‖ ≤ C₀ * (1 + ‖s‖) ^ d :=
    (hsum j s hjne hs).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hW (le_max_left _ _)) hC₀.le)
  have hbound_O' : ‖∑ v ∈ O', term v‖ ≤ C_other * (1 + ‖s‖) ^ d := by
    have hattach : ∑ v ∈ O', term v = ∑ v : {w : S // w ∈ O'}, term v.val :=
      (Finset.sum_attach O' term).symm
    rw [hattach]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun v _ ↦ ?_
    dsimp only [term]
    rw [norm_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hEv : ‖E v.val‖ ≤ Cv v * (1 + ‖s‖) ^ d :=
      (hbdv v j s hjne hs).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hW ((Finset.le_sup (Finset.mem_univ v)).trans (le_max_right _ _)))
        (hCv v).le)
    dsimp only [b]
    split_ifs
    · rw [norm_zero]
      exact mul_nonneg (by linarith [hCv v]) (by positivity)
    · exact (norm_sub_le _ _).trans (by
        rw [norm_one]
        nlinarith [hWd, hEv])
  have hterm_v₀ : ‖term v₀‖ ≤ (C₀ + C_other) * (1 + ‖s‖) ^ d := by
    rw [hterm_eq]
    exact (norm_sub_le _ _).trans ((add_le_add hbound_O hbound_O').trans_eq (by ring))
  have hbv₀ : ‖b v₀‖ ≤ ((C₀ + C_other) / Real.log (v₀.val.asIdeal.absNorm : ℝ)) * (1 + ‖s‖) ^ d := by
    dsimp only [term] at hterm_v₀
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hlog_pos] at hterm_v₀
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog_pos, mul_comm]
    exact hterm_v₀
  by_cases hE0 : E v₀ = 0
  · rw [show finiteLocalEulerFactor v₀.val (sLocalFiniteRestriction v₀ j.val.1) = 0 from hE0,
      norm_zero]
    dsimp [C]
    positivity
  · have hb_eq : b v₀ = 1 - E v₀ := ite_eq_right hE0
    have hE_le : ‖E v₀‖ ≤ 1 + ‖b v₀‖ := by
      have hsub : E v₀ = 1 - b v₀ := by rw [hb_eq]; ring
      rw [hsub]
      exact (norm_sub_le _ _).trans (by rw [norm_one])
    calc
      ‖E v₀‖ ≤ 1 + ‖b v₀‖ := hE_le
      _ ≤ 1 * (1 + ‖s‖) ^ d +
          ((C₀ + C_other) / Real.log (v₀.val.asIdeal.absNorm : ℝ)) * (1 + ‖s‖) ^ d :=
            add_le_add (by linarith) hbv₀
      _ = C * (1 + ‖s‖) ^ d := by dsimp [C]; ring

/-- Paper: Theorem 7.3.3.4, pp. 360–363 (exact uniformizer-distance form of #7336).
Under the hypotheses of `sLocalPolarOrbital_singleOutsideEuler_bound_of_basis`, for any
local uniformizer `u` of the outside place `v₀`, whenever `sLocalFiniteRestriction v₀ c` is
unramified and regular at a repeated primary pole `c = chart(χ) s`, the shifted distance
`‖1 - sLocalFiniteRestriction v₀ c u‖` obeys the polynomial lower bound
`1 ≤ C * (1 + ‖s‖)^d * ‖1 - sLocalFiniteRestriction v₀ c u‖`. -/
theorem sLocalPolarOrbital_singleOutsideDistance_bound_of_basis
    (p : Vℚ) (ω : PontryaginDual J₁)
    (hS : IsSaturatedPlaceSet S) (hp : (Sₚ(p)).Nonempty) (hPic : PicTrivial) (σ : ℕ ≃ Idx(p, ω))
    (D : Idx(p, ω) → StrongDual ℂ (Q(p, ω))) (ψ : Idx(p, ω) → Q(p, ω))
    (hD : ∀ (j : Idx(p, ω)) (x : Θₛ(ω)), D j (π(p, ω) x) =
      sLocalOrbitalPrincipalPart (F := F) (S := S) (T := Sₚ(p)) (ω := ω) j x)
    (hbasis : IsSchauderBasis (ψ ∘ σ) (D ∘ σ))
    (χ : PontryaginDual Jₛ) (v₀ : S) (hv₀ : v₀.val ∉ Sₚ(p))
    (u : (v₀.val.adicCompletion F)ˣ) (hu : uniformizerNorm(v₀, u))
    (hother : ∀ v : S, v.val ∉ Sₚ(p) → v ≠ v₀ →
      ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        ‖finiteLocalEulerFactor v.val (sLocalFiniteRestriction v j.val.1)‖ ≤ C * (1 + ‖s‖) ^ d) :
    ∃ d : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ (j : Idx(p, ω)) (s : ℂ), j.val.2 ≠ 0 → j.val.1 = chart(χ) s →
        (∀ y : (HeightOneSpectrum.adicCompletionIntegers F v₀.val)ˣ,
          sLocalFiniteRestriction v₀ j.val.1
            (Units.map (HeightOneSpectrum.adicCompletionIntegers F v₀.val).subtype.toMonoidHom y) = 1) →
        sLocalFiniteRestriction v₀ j.val.1 u ≠ 1 →
        1 ≤ C * (1 + ‖s‖) ^ d * ‖1 - sLocalFiniteRestriction v₀ j.val.1 u‖ := by
  classical
  obtain ⟨d, C, hC, hE⟩ :=
    sLocalPolarOrbital_singleOutsideEuler_bound_of_basis p ω hS hp hPic σ D ψ hD hbasis
      χ v₀ hv₀ hother
  refine ⟨d, C, hC, fun j s hjne hs hunr hne1 ↦ ?_⟩
  have hbd := hE j s hjne hs
  -- Identify `finiteLocalEulerFactor` at the unramified character using the chosen uniformizer `u`.
  let hπ := (Valued.v : Valuation (v₀.val.adicCompletion F)
    (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let π : (v₀.val.adicCompletion F)ˣ := Units.mk0 hπ.choose hπ.choose_spec.ne_zero
  have hπ_norm : ‖π.val‖ = (v₀.val.asIdeal.absNorm : ℝ)⁻¹ :=
    norm_uniformizer_adicCompletion v₀.val _ hπ.choose_spec
  have hratio_norm : ‖(u * π⁻¹).val‖ = 1 := by
    rw [Units.val_mul, norm_mul, Units.val_inv_eq_inv_val, norm_inv, hu, hπ_norm]
    have hq : (v₀.val.asIdeal.absNorm : ℝ) ≠ 0 := by
      exact_mod_cast (Ideal.absNorm_eq_zero_iff.not.mpr v₀.val.ne_bot)
    field_simp [hq]
  have hratio_val : Valued.v (u * π⁻¹).val = 1 :=
    Valued.toNormedField.norm_eq_one_iff.mp hratio_norm
  have hratio_inv_val : Valued.v (u * π⁻¹)⁻¹.val = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, hratio_val, inv_one]
  let y : (HeightOneSpectrum.adicCompletionIntegers F v₀.val)ˣ :=
    ⟨⟨(u * π⁻¹).val, le_of_eq hratio_val⟩, ⟨(u * π⁻¹)⁻¹.val, le_of_eq hratio_inv_val⟩,
      Subtype.ext (u * π⁻¹).mul_inv, Subtype.ext (u * π⁻¹).inv_mul⟩
  have hy_eq : Units.map (HeightOneSpectrum.adicCompletionIntegers F v₀.val).subtype.toMonoidHom y =
      u * π⁻¹ := Units.ext rfl
  have hcu_eq : sLocalFiniteRestriction v₀ j.val.1 π = sLocalFiniteRestriction v₀ j.val.1 u := by
    have h1 := hunr y
    rw [hy_eq, map_mul, map_inv] at h1
    exact (eq_of_mul_inv_eq_one h1).symm
  have hE_eq : finiteLocalEulerFactor v₀.val (sLocalFiniteRestriction v₀ j.val.1) =
      (1 - sLocalFiniteRestriction v₀ j.val.1 u)⁻¹ := by
    unfold finiteLocalEulerFactor
    rw [ite_eq_left hunr]
    change (1 - sLocalFiniteRestriction v₀ j.val.1 π)⁻¹ = _
    rw [hcu_eq]
  rw [hE_eq, norm_inv] at hbd
  have hpos : 0 < ‖1 - sLocalFiniteRestriction v₀ j.val.1 u‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne1))
  rw [inv_le_iff_one_le_mul₀' hpos, mul_comm] at hbd
  exact hbd

end OutsideEulerNecessity

end RiemannMasullo.Isolated
