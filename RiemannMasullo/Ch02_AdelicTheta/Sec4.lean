module

public import RiemannMasullo.Ch02_AdelicTheta.Sec3
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
import RiemannMasullo.ForMathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# Small-norm estimates for S-local adelic theta

Masullo, §2.4, pp. 106–116. As in §2.3, the Lean place set records the
finite places only. All archimedean places are included in `SAdeleRing`.
-/

@[expose] public noncomputable section

open Asymptotics Bornology Filter IsDedekindDomain MeasureTheory NumberField Topology
open scoped NNReal

namespace RiemannMasullo

variable (F : Type*) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))

local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "J₁" => MonoidHom.ker (sIdeleQuotientNorm F S)
local notation "classOf" => (QuotientGroup.mk : Iₛ → SIdeleQuotient F S)
local notation "normℝ[" K "," V "]" =>
  fun (g : (SAdeleRing K V)ˣ) ↦ ((Units.val (sIdeleNorm K V g) : ℝ≥0) : ℝ)
local notation "smallNorm[" K "," V "]" => comap normℝ[K, V] (𝓝[>] (0 : ℝ))

-- As in §2.3, the homogeneous operator takes its Haar measure as a parameter.
local instance : MeasurableSpace J₁ := borel _

-- TODO(paper-gap): Lemma 2.4.1.2 prints C in (2.4.1.3) after quantifying Cφ.
-- A coefficient depending only on T, M, N and the bases fails for
-- M = 1, N = 2, a₁ = 2, T = 1 and φ(t) = K on (0, 1), zero for t ≥ 1.
-- At t = 2⁻ⁿ the sum is K n, so the coefficient must be at least K / log 2.

/-- A bounded function with power decay has a single majorant for all decay exponents
between zero and one. -/
private theorem geometric_grid_decay_majorant {N : ℕ} (hN : 1 ≤ N) {φ : ℝ → ℂ}
    {C A T : ℝ} (hC : 0 < C) (hb : ∀ y, 0 < y → ‖φ y‖ ≤ C)
    (hd : ∀ y, T ≤ y → ‖φ y‖ ≤ A * (y ^ N)⁻¹) :
    ∃ D : ℝ, 0 < D ∧ ∀ y, 0 < y → ∀ L : ℝ, 1 ≤ L →
      ‖φ y‖ ≤ D * Real.exp (-Real.log y / L) := by
  let D := max (C * max 1 T) A
  have hCD : C ≤ D :=
    (le_mul_of_one_le_right hC.le (le_max_left 1 T)).trans (le_max_left _ _)
  refine ⟨D, hC.trans_le hCD, ?_⟩
  intro y hy L hL
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  rcases le_total y 1 with hy₁ | hy₁
  · have hlog := Real.log_nonpos hy.le hy₁
    exact ((hb y hy).trans hCD).trans (le_mul_of_one_le_right (hC.le.trans hCD)
      (Real.one_le_exp (div_nonneg (neg_nonneg.mpr hlog) hL0.le)))
  · have hlinear : ‖φ y‖ * y ≤ D := by
      by_cases hT : T ≤ y
      · have hpow : y ≤ y ^ N := by simpa using pow_le_pow_right₀ hy₁ hN
        have hdec : ‖φ y‖ ≤ A / y ^ N := by simpa only [div_eq_mul_inv] using hd y hT
        exact (mul_le_mul_of_nonneg_left hpow (norm_nonneg _)).trans
          (((le_div_iff₀ (pow_pos hy N)).mp hdec).trans (le_max_right _ _))
      · exact (mul_le_mul (hb y hy) ((le_of_not_ge hT).trans (le_max_right _ _)) hy.le hC.le).trans
          (le_max_left _ _)
    calc
      ‖φ y‖ ≤ D * Real.exp (-Real.log y) := by
        rw [Real.exp_neg, Real.exp_log hy, ← div_eq_mul_inv]
        exact (le_div_iff₀ hy).mpr hlinear
      _ ≤ D * Real.exp (-Real.log y / L) := by
        gcongr
        apply (le_div_iff₀ hL0).mpr
        nlinarith [mul_nonneg (Real.log_nonneg hy₁) (sub_nonneg.mpr hL)]

/-- The mass of a geometric series with ratio exp(-b/L) is at most linear in L. -/
private theorem geometric_grid_factor_bound {b L : ℝ} (hb : 0 < b) (hL : 1 ≤ L) :
    (1 - Real.exp (-b / L))⁻¹ ≤ (1 + b⁻¹) * L := by
  have hL0 := zero_lt_one.trans_le hL
  let x := b / L
  have hx : 0 < x := div_pos hb hL0
  have hex : 0 < Real.exp x - 1 := sub_pos.mpr (Real.one_lt_exp_iff.mpr hx)
  calc
    (1 - Real.exp (-b / L))⁻¹ = 1 + (Real.exp x - 1)⁻¹ := by
      rw [neg_div, Real.exp_neg]
      change (1 - (Real.exp x)⁻¹)⁻¹ = _
      field_simp [hex.ne', (Real.exp_pos x).ne']
      ring
    _ ≤ 1 + x⁻¹ := by
      gcongr
      linarith [Real.add_one_le_exp x]
    _ ≤ (1 + b⁻¹) * L := by
      dsimp [x]
      rw [inv_div, one_add_mul, div_eq_inv_mul]
      linarith

/-- The geometric grid estimate, including the zero-dimensional grid. -/
private theorem geometric_grid_log_bound (M N : ℕ) (hN : 1 < N)
    (a : Fin M → ℝ) (ha : ∀ i, 1 < a i) (φ : ℝ → ℂ)
    (hbounded : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ C)
    (hdecay : ∃ A T : ℝ, 0 < A ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t → ‖φ t‖ ≤ A * (t ^ N)⁻¹) :
    ∃ T₀ Cφ : ℝ, 0 < T₀ ∧ 0 < Cφ ∧ ∀ t : ℝ, 0 < t → t < T₀ →
      let term : (Fin M → ℕ) → ℝ := fun k ↦ ‖φ ((∏ i, a i ^ k i) * t)‖
      Summable term ∧ (∑' k, term k) ≤ Cφ * |Real.log t| ^ M := by
  obtain ⟨C, hC, hb⟩ := hbounded
  obtain ⟨A, T, -, -, hd⟩ := hdecay
  obtain ⟨D, hD, hmajor⟩ := geometric_grid_decay_majorant hN.le hC hb hd
  let b (i : Fin M) := Real.log (a i)
  have hbpos (i : Fin M) : 0 < b i := Real.log_pos (ha i)
  have hapos (i : Fin M) : 0 < a i := zero_lt_one.trans (ha i)
  let P := ∏ i, (1 + (b i)⁻¹)
  have hP : 0 < P := Finset.prod_pos fun i _ ↦ by have := hbpos i; positivity
  refine ⟨Real.exp (-1), D * Real.exp 1 * P, Real.exp_pos _, by positivity, ?_⟩
  intro t ht ht₀
  -- Choose the decay exponent 1/L so that the factor from t is exactly exp(1).
  let L := -Real.log t
  have hL : 1 ≤ L := by
    have h := (Real.log_lt_iff_lt_exp ht).mpr ht₀
    dsimp [L]
    linarith
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  let q (i : Fin M) := Real.exp (-b i / L)
  let w (k : Fin M → ℕ) := ∏ i, (q i) ^ k i
  have hq (i : Fin M) : q i < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (neg_lt_zero.mpr (hbpos i)) hL0)
  have hw : HasSum w (∏ i, (1 - q i)⁻¹) :=
    hasSum_prod_fin_of_nonneg (fun i n ↦ q i ^ n) _
      (fun i n ↦ pow_nonneg (Real.exp_nonneg _) _)
      (fun i ↦ hasSum_geometric_of_lt_one (Real.exp_nonneg _) (hq i))
  have hpoint (k : Fin M → ℕ) :
      ‖φ ((∏ i, a i ^ k i) * t)‖ ≤ D * Real.exp 1 * w k := by
    have hp : 0 < ∏ i, a i ^ k i := Finset.prod_pos fun i _ ↦ pow_pos (hapos i) _
    refine (hmajor _ (mul_pos hp ht) L hL).trans_eq ?_
    have hlog : -Real.log ((∏ i, a i ^ k i) * t) / L = 1 + ∑ i, (k i : ℝ) * (-b i / L) := by
      rw [Real.log_mul hp.ne' ht.ne', Real.log_prod (fun i _ ↦ (pow_pos (hapos i) _).ne')]
      simp only [Real.log_pow]
      have hterm (i : Fin M) : (k i : ℝ) * (-b i / L) = -((k i : ℝ) * b i) / L := by ring
      simp_rw [hterm]
      simp only [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_neg_distrib]
      change -((∑ i, (k i : ℝ) * b i) + Real.log t) / L = _
      have htL : Real.log t = -L := (neg_neg _).symm
      rw [htL]
      field_simp [hL0.ne']
      ring
    rw [hlog, Real.exp_add, Real.exp_sum, mul_assoc]
    simp only [Real.exp_nat_mul, w, q]
  have hsum := hw.mul_left (D * Real.exp 1)
  have hs := hsum.summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hpoint
  refine ⟨hs, (hs.tsum_le_tsum hpoint hsum.summable).trans ?_⟩
  rw [hsum.tsum_eq, abs_of_nonpos (by change Real.log t ≤ 0; dsimp [L] at hL; linarith)]
  change D * Real.exp 1 * (∏ i, (1 - q i)⁻¹) ≤ D * Real.exp 1 * P * L ^ M
  rw [mul_assoc (D * Real.exp 1)]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hD.le (Real.exp_nonneg _))
  calc
    (∏ i, (1 - q i)⁻¹) ≤ ∏ i, ((1 + (b i)⁻¹) * L) :=
      Finset.prod_le_prod₀ (fun i _ ↦ inv_nonneg.mpr (sub_nonneg.mpr (hq i).le))
        (fun i _ ↦ geometric_grid_factor_bound (hbpos i) hL)
    _ = P * L ^ M := by simp [P, Finset.prod_mul_distrib]

/-- Paper: Lemma 2.4.1.2, p. 107. For a bounded function with power decay
at infinity, the sum of the norms over the multiplicative grid with M bases
greater than one converges and is bounded by a constant times the Mth power
of the absolute log near zero.
Deviation: Equation (2.4.1.3) uses the existentially quantified constant
`Cφ`. The real-domain function is used only at positive arguments, and
summability is explicit. -/
theorem summable_geometric_grid_log_bound (M N : ℕ) (hM : 1 ≤ M) (hN : 1 < N)
    (a : Fin M → ℝ) (ha : ∀ i, 1 < a i) (φ : ℝ → ℂ)
    (hbounded : ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ‖φ t‖ ≤ C)
    (hdecay : ∃ A T : ℝ, 0 < A ∧ 0 < T ∧ ∀ t : ℝ, T ≤ t → ‖φ t‖ ≤ A * (t ^ N)⁻¹) :
    ∃ T₀ Cφ : ℝ, 0 < T₀ ∧ 0 < Cφ ∧ ∀ t : ℝ, 0 < t → t < T₀ →
      let term : (Fin M → ℕ) → ℝ := fun k ↦ ‖φ ((∏ i, a i ^ k i) * t)‖
      Summable term ∧ (∑' k, term k) ≤ Cφ * |Real.log t| ^ M := by
  clear hM
  exact geometric_grid_log_bound M N hN a ha φ hbounded hdecay

/-! ## The rational number field -/

section Rat

variable (S : Finset (HeightOneSpectrum (𝓞 ℚ)))

local notation "A" => SAdeleRing ℚ S
local notation "U" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 ℚ))) ℚ)ˣ
local notation "unitAtS" =>
  MonoidHom.comp (Units.map (RingHom.toMonoidHom (RingHom.comp (adeleProjection ℚ S)
    (Subring.subtype (integralAdelesOutside ℚ S)))))
    (Units.map (RingHom.toMonoidHom (integralAdeleDiagonal ℚ S)))
local notation "ratNorm" => fun (g : Aˣ) ↦ ((Units.val (sIdeleNorm ℚ S g) : ℝ≥0) : ℝ)
local notation "w" => Rat.infinitePlace

/-- The rational S-idelic norm uses the single real place and all finite places in S. -/
private theorem rat_sIdeleNorm_eq (g : Aˣ) :
    ratNorm g = ‖g.val.1 w‖ * ∏ v : S, ‖g.val.2 v‖ := by
  classical
  let eval : (Aˣ →* ℝ≥0ˣ) →* ℝ :=
    NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval g))
  change eval (sIdeleNorm ℚ S) = _
  simp only [sIdeleNorm, map_mul, map_prod]
  rw [Fintype.prod_subsingleton _ w]
  simp only [Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  rfl

open scoped Classical in
/-- The archimedean norm of a rational adele is the norm of its unique real coordinate. -/
private theorem rat_arch_norm_eq (x : InfiniteAdeleRing ℚ) :
    ‖InfiniteAdeleRing.ringEquiv_mixedSpace ℚ x‖ = ‖x w‖ := by
  classical
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace, Finset.sup'_univ_eq_ciSup, ciSup_unique]
  change mixedEmbedding.normAtPlace w _ = _
  rw [mixedEmbedding.normAtPlace_apply_of_isReal Rat.isReal_infinitePlace,
    InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _) _

/-- Multiplying by a diagonal S-unit preserves the S-idelic norm. -/
private theorem rat_sIdeleNorm_unit_mul (g : Aˣ) (u : U) :
    ratNorm (unitAtS u * g) = ratNorm g := by
  have hu : sIdeleNorm ℚ S (unitAtS u) = 1 :=
    MonoidHom.mem_ker.mp ((sIdeleNorm_spec ℚ S).2 ⟨u, rfl⟩)
  change ((↑↑(sIdeleNorm ℚ S (unitAtS u * g))) : ℝ) = _
  rw [map_mul, hu, one_mul]

/-- Every finite coordinate of an S-idele is nonzero. -/
private theorem rat_sIdele_finite_ne_zero (g : Aˣ) (v : S) : g.val.2 v ≠ 0 := by
  let ev : A →+* v.val.adicCompletion ℚ :=
    (Pi.evalRingHom _ v).comp (RingHom.snd _ _)
  exact (g.isUnit.map ev).ne_zero

/-- Among diagonal S-unit multiples, the finite norms and the sign of the
rational multiplier determine the multiplier. -/
private theorem rat_sUnit_eq_of_norms (g : Aˣ) {u z : U}
    (hfin : ∀ v : S, ‖(unitAtS u * g).val.2 v‖ = ‖(unitAtS z * g).val.2 v‖)
    (hsign : (0 ≤ (u.val.val : ℚ)) ↔ (0 ≤ (z.val.val : ℚ))) : u = z := by
  have hnorm := (rat_sIdeleNorm_unit_mul S g u).trans (rat_sIdeleNorm_unit_mul S g z).symm
  rw [rat_sIdeleNorm_eq, rat_sIdeleNorm_eq] at hnorm
  simp_rw [hfin] at hnorm
  have hprod := Finset.prod_pos (s := Finset.univ) fun v _ ↦
    norm_pos_iff.mpr (rat_sIdele_finite_ne_zero S (unitAtS z * g) v)
  have hinf := (mul_right_cancel₀ hprod.ne') hnorm
  have harch (ξ : U) :
      ‖(unitAtS ξ * g).val.1 w‖ = |(ξ.val.val : ℚ)| * ‖g.val.1 w‖ := by
    change ‖algebraMap ℚ Rat.infinitePlace.Completion ξ.val.val * g.val.1 w‖ = _
    rw [norm_mul, eq_ratCast (algebraMap ℚ Rat.infinitePlace.Completion),
      InfinitePlace.Completion.Rat.norm_infinitePlace_completion]
  rw [harch, harch] at hinf
  let ev : A →+* Rat.infinitePlace.Completion :=
    (Pi.evalRingHom _ w).comp (RingHom.fst _ _)
  have hne : g.val.1 w ≠ 0 := (g.isUnit.map ev).ne_zero
  have habs : |u.val.val| = |z.val.val| :=
    Rat.cast_injective (mul_right_cancel₀ (norm_ne_zero_iff.mpr hne) hinf)
  apply Units.ext
  apply Subtype.ext
  by_cases hu : 0 ≤ u.val.val
  · rwa [abs_of_nonneg hu, abs_of_nonneg (hsign.mp hu)] at habs
  · have hz : ¬ 0 ≤ z.val.val := mt hsign.mpr hu
    simpa [abs_of_neg (lt_of_not_ge hu), abs_of_neg (lt_of_not_ge hz)] using habs

/-- A nonzero finite coordinate has norm given by an integer power of its
residue field cardinality. -/
private theorem rat_finite_norm_eq_zpow (v : S) (x : v.val.adicCompletion ℚ)
    (hx : x ≠ 0) : ∃ e : ℤ, ‖x‖ = (v.val.asIdeal.absNorm : ℝ) ^ e := by
  refine ⟨WithZero.log (Valued.v x), ?_⟩
  rw [FinitePlace.norm_def, WithZeroMulInt.toNNReal_neg_apply _
    (Valued.v.ne_zero_iff.mpr hx)]
  simp


/-- Finite norm cutoffs put the translated rational S-units into an integer
grid with a shift independent of the idele. The sign distinguishes opposite units. -/
private theorem rat_sUnit_grid (R : S → ℝ) (e : Fin S.card ≃ S) :
    let q : Fin S.card → ℝ := fun i ↦ (e i).val.asIdeal.absNorm
    ∃ Q : ℝ, 0 < Q ∧ ∀ g : Aˣ,
      let P : Set U := {u | ∀ v, ‖(unitAtS u * g).val.2 v‖ ≤ R v}
      ∃ index : P ↪ Bool × (Fin S.card → ℕ), ∀ u : P,
        ‖(unitAtS u.val * g).val.1 w‖ * Q =
          (∏ i, q i ^ (index u).2 i) * ratNorm g := by
  classical
  let q : Fin S.card → ℝ := fun i ↦ (e i).val.asIdeal.absNorm
  have hq (i) : 1 < q i := by
    simpa only [q, Nat.one_lt_cast] using NumberField.HeightOneSpectrum.one_lt_absNorm (e i).val
  have hqpos (i) : 0 < q i := zero_lt_one.trans (hq i)
  choose N hN using fun i ↦ pow_unbounded_of_one_lt (R (e i)) (hq i)
  let Q := ∏ i, q i ^ N i
  refine ⟨Q, Finset.prod_pos (fun i _ ↦ pow_pos (hqpos i) _), fun g ↦ ?_⟩
  let P : Set U := {u | ∀ v, ‖(unitAtS u * g).val.2 v‖ ≤ R v}
  let y (u : P) := unitAtS u.val * g
  have hdiscrete (u : P) (i : Fin S.card) :
      ∃ a : ℤ, ‖(y u).val.2 (e i)‖ = q i ^ a :=
    rat_finite_norm_eq_zpow S (e i) _ (rat_sIdele_finite_ne_zero S (y u) (e i))
  choose a ha using hdiscrete
  let n (u : P) (i : Fin S.card) : ℕ := (↑(N i) - a u i).toNat
  have hshift (u : P) (i : Fin S.card) :
      ‖(y u).val.2 (e i)‖ * q i ^ n u i = q i ^ N i := by
    have hle : a u i ≤ (N i : ℤ) := by
      apply (zpow_right_strictMono₀ (hq i)).le_iff_le.mp
      rw [← ha u i, zpow_natCast]
      exact (u.property (e i)).trans (hN i).le
    rw [ha, ← zpow_natCast (q i) (n u i), ← zpow_add₀ (hqpos i).ne',
      Int.toNat_sub_of_le hle, add_sub_cancel, zpow_natCast]
  let index : P ↪ Bool × (Fin S.card → ℕ) :=
    ⟨fun u ↦ (decide (0 ≤ (u.val.val.val : ℚ)), n u), by
      intro u z h
      apply Subtype.ext
      apply rat_sUnit_eq_of_norms S g
      · intro v
        obtain ⟨i, rfl⟩ := e.surjective v
        have hn : n u i = n z i := congrFun (congrArg Prod.snd h) i
        apply mul_right_cancel₀ (pow_ne_zero (n u i) (hqpos i).ne')
        rw [hshift u i, hn, hshift z i]
      · exact decide_eq_decide.mp (congrArg Prod.fst h)⟩
  refine ⟨index, fun u ↦ ?_⟩
  have hQ : (∏ v : S, ‖(y u).val.2 v‖) * (∏ i, q i ^ n u i) = Q := by
    rw [← e.prod_comp (fun v ↦ ‖(y u).val.2 v‖), ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ ↦ hshift u i)
  change ‖(y u).val.1 w‖ * Q = (∏ i, q i ^ n u i) * ratNorm g
  rw [← hQ, ← mul_assoc, ← rat_sIdeleNorm_eq, rat_sIdeleNorm_unit_mul, mul_comm]

/-- Compact finite support and quadratic archimedean decay suffice for the
logarithmic growth bound on the sum over rational S-units. -/
private theorem rat_sUnit_sum_log_growth (f : A → ℂ) (R : S → ℝ) (B₀ B₂ : ℝ)
    (hR : ∀ x, (¬ ∀ v, ‖x.2 v‖ ≤ R v) → f x = 0)
    (h₀ : ∀ x, ‖f x‖ ≤ B₀)
    (h₂ : ∀ x, ‖f x‖ * ‖x.1 w‖ ^ 2 ≤ B₂) :
    (fun g : Aˣ ↦ ∑' u : U, f (unitAtS u * g).val) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (ratNorm g)| ^ S.card) := by
  classical
  let e : Fin S.card ≃ S := S.equivFin.symm
  let q : Fin S.card → ℝ := fun i ↦ (e i).val.asIdeal.absNorm
  have hq (i) : 1 < q i := by
    simpa only [q, Nat.one_lt_cast] using NumberField.HeightOneSpectrum.one_lt_absNorm (e i).val
  obtain ⟨Q, _, hgrid⟩ := rat_sUnit_grid S R e
  let D := max 1 (max B₀ (B₂ * Q ^ 2))
  have hD : 0 < D := zero_lt_one.trans_le (le_max_left _ _)
  let φ (t : ℝ) : ℂ := (D * ((max 1 t) ^ 2)⁻¹ : ℝ)
  have hφ (t : ℝ) : ‖φ t‖ = D * ((max 1 t) ^ 2)⁻¹ := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  obtain ⟨T, C, hT, _, hseries⟩ := geometric_grid_log_bound S.card 2 (by decide) q hq φ
    ⟨D, hD, fun t _ ↦ by
      rw [hφ]
      have hp : 1 ≤ (max 1 t) ^ 2 := one_le_pow₀ (le_max_left _ _)
      exact mul_le_of_le_one_right hD.le ((inv_le_one₀ (zero_lt_one.trans_le hp)).mpr hp)⟩
    ⟨D, 1, hD, zero_lt_one, fun t ht ↦ by rw [hφ, max_eq_right ht]⟩
  refine IsBigO.of_bound (2 * C) (mem_comap.mpr ⟨Set.Ioo 0 T, Ioo_mem_nhdsGT hT, ?_⟩)
  intro g hg
  have hg' : ratNorm g ∈ Set.Ioo 0 T := hg
  obtain ⟨hseriesSummable, hseriesBound⟩ := hseries (ratNorm g) hg'.1 hg'.2
  let P : Set U := {u | ∀ v, ‖(unitAtS u * g).val.2 v‖ ≤ R v}
  obtain ⟨index, hindex⟩ := hgrid g
  let term (u : U) := f (unitAtS u * g).val
  let majorant (k : Fin S.card → ℕ) := ‖φ ((∏ i, q i ^ k i) * ratNorm g)‖
  have hpoint (u : P) : ‖term u.val‖ ≤ majorant (index u).2 := by
    let x := (unitAtS u.val * g).val
    change ‖f x‖ ≤ _
    dsimp only [majorant]
    rw [← hindex u, hφ]
    change ‖f x‖ ≤ D * ((max 1 (‖x.1 w‖ * Q)) ^ 2)⁻¹
    rcases le_total (‖x.1 w‖ * Q) 1 with hx | hx
    · rw [max_eq_left hx, one_pow, inv_one, mul_one]
      exact (h₀ x).trans
        ((le_max_left B₀ (B₂ * Q ^ 2)).trans (le_max_right 1 _))
    · rw [max_eq_right hx, ← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (zero_lt_one.trans_le hx) _)).mpr
      rw [mul_pow, ← mul_assoc]
      exact (mul_le_mul_of_nonneg_right (h₂ x) (sq_nonneg Q)).trans
        ((le_max_right B₀ (B₂ * Q ^ 2)).trans (le_max_right 1 _))
  have hs : Summable majorant := hseriesSummable
  have hp : Summable (fun p : Bool × (Fin S.card → ℕ) ↦ majorant p.2) := by
    exact (summable_prod_of_nonneg (fun _ ↦ norm_nonneg _)).mpr
      ⟨fun _ ↦ hs, Summable.of_finite⟩
  have hsub : Summable (fun u : P ↦ ‖term u.val‖) :=
    (hp.comp_injective index.injective).of_nonneg_of_le (fun _ ↦ norm_nonneg _) hpoint
  have hsupport : Function.support (fun u ↦ ‖term u‖) ⊆ P :=
    Function.support_subset_iff'.mpr fun u hu ↦
      norm_eq_zero.mpr (hR _ hu)
  have hall : Summable (fun u ↦ ‖term u‖) := by
    have h := (summable_subtype_iff_indicator (s := P) (f := fun u ↦ ‖term u‖)).mp hsub
    rwa [Set.indicator_eq_self.mpr hsupport] at h
  change ‖∑' u, term u‖ ≤ (2 * C) * ‖|Real.log (ratNorm g)| ^ S.card‖
  rw [Real.norm_of_nonneg (pow_nonneg (abs_nonneg _) _)]
  calc
    ‖∑' u, term u‖ ≤ ∑' u, ‖term u‖ := norm_tsum_le_tsum_norm hall
    _ = ∑' u : P, ‖term u.val‖ := (tsum_subtype_eq_of_support_subset hsupport).symm
    _ ≤ ∑' p : Bool × (Fin S.card → ℕ), majorant p.2 :=
      hsub.tsum_le_tsum_of_inj index index.injective (fun _ _ ↦ norm_nonneg _) hpoint hp
    _ = 2 * (∑' k, majorant k) := by
      rw [hp.tsum_prod, tsum_fintype]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, two_nsmul, two_mul]
    _ ≤ (2 * C) * |Real.log (ratNorm g)| ^ S.card := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hseriesBound (by positivity)

/-- Paper: Proposition 2.4.1.1, p. 107. Over the rationals the theta
function grows at most as the absolute log norm to the number of finite
places in S, uniformly as the S-idelic norm tends to zero from above. -/
theorem sLocalAdelicTheta_rat_log_growth (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    (fun g ↦ sLocalAdelicTheta ℚ S f g) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (normℝ[ℚ, S] g)| ^ S.card) := by
  have htheta : (fun g : Aˣ ↦ sLocalAdelicTheta ℚ S f g) =
      (fun g : Aˣ ↦ ∑' u : U, f (Multiplicative.ofAdd (unitAtS u * g).val)) :=
    funext (sLocalAdelicTheta_apply ℚ S f)
  rw [htheta]
  obtain ⟨K, hK, hsupport, hdecay⟩ := sAdeleSchwartz_exists_decay_bound ℚ S f
  have hcoord (v : S) : ∃ r : ℝ, ∀ x ∈ K, ‖x v‖ ≤ r :=
    hK.exists_bound_of_continuousOn (continuous_apply v).continuousOn
  choose R hR using hcoord
  obtain ⟨B₀, _, h₀⟩ := hdecay 0
  obtain ⟨B₂, _, h₂⟩ := hdecay 2
  refine rat_sUnit_sum_log_growth S (fun x ↦ f (Multiplicative.ofAdd x)) R B₀ B₂ ?_ ?_ ?_
  · exact fun x hx ↦ hsupport x (fun hxK ↦ hx (fun v ↦ hR v x.2 hxK))
  · intro x
    simpa only [pow_zero, mul_one] using h₀ x
  · intro x
    simpa only [rat_arch_norm_eq x.1] using h₂ x

/-- Paper: Proposition 2.4.1.1, pp. 107, 110. Over the rationals the same
logarithmic growth bound holds for homogeneous theta for each continuous
character of the norm-one S-idele classes.
Deviation: As in §2.3, the Haar measure on those classes is explicit. -/
theorem sLocalHomogeneousAdelicTheta_rat_log_growth
    (μ : Measure ↥(MonoidHom.ker (sIdeleQuotientNorm ℚ S))) [Measure.IsHaarMeasure μ]
    (ω : PontryaginDual ↥(MonoidHom.ker (sIdeleQuotientNorm ℚ S)))
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    (fun g ↦ sLocalHomogeneousAdelicTheta ℚ S μ ω f (QuotientGroup.mk g)) =O[smallNorm[ℚ, S]]
      (fun g ↦ |Real.log (normℝ[ℚ, S] g)| ^ S.card) := by sorry

end Rat

-- TODO(paper-gap): The geometric series in (2.4.1.5) has an unrounded
-- lower endpoint, and (2.4.1.8) loses a factor in the power of T. The
-- reduction in (2.4.1.14) changes the local support condition. The
-- application on p. 109 omits S = {∞}, where the S-units are {±1}.
-- TODO(paper-gap): The p. 110 ergodicity assertion fails for S = {∞, p} over ℚ.
-- On Hₚ with nonzero real coordinate, log |x| modulo log p is invariant.
-- Theta can be bounded at zero, for instance when S = {∞} over ℚ. Its
-- Mellin integral there fails to converge uniformly on the entire open
-- right half-plane, even for the real Gaussian with trivial character.

/-! ## The general case -/

local notation "normℝ" => normℝ[F, S]
local notation "smallNorm" => smallNorm[F, S]

-- TODO(paper-gap): In the proof of Theorem 2.4.2.1, (2.4.2.2) leaves x∞
-- free on the right after taking the supremum on the left. Equation
-- (2.4.2.3) fails for the real Gaussian times the local integer indicators
-- at 2 and 3. The count of S-unit multiples in a fixed real annulus
-- outside the ball can grow without bound. The averaged estimate
-- (2.4.2.4) alone does not give a pointwise bound.

/-- Paper: Theorem 2.4.2.1, p. 111. Below S-idelic norm one, the theta
function is bounded by a constant times the absolute log norm to the
power `|S| - 1`, plus an additive constant. Both constants are uniform
on a bounded set of Schwartz–Bruhat functions. -/
theorem sLocalAdelicTheta_log_growth_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖sLocalAdelicTheta F S f g‖ ≤
        C₁ * |Real.log (normℝ g)| ^ (Fintype.card (InfinitePlace F) + S.card - 1) + C₂ := by sorry

/-! ## Order of growth -/

variable (ε : ℝ) (hε : 0 < ε)

include hε

-- TODO(paper-gap): The derivative of φ(t, g) on p. 113 drops g and ω(g).
-- In (2.4.3.3) the supremum is unweighted since |g′| = 1. It can be
-- infinite, as for the Gaussian example at (2.4.2.3).

/-- Paper: Proposition 2.4.3.1(1), p. 113. Multiplying S-local theta by
any positive real power of the S-idelic norm gives a bounded function
as the norm tends to zero from above. -/
theorem sLocalAdelicTheta_norm_pow_isBigO (f : ℬₛ) :
    (fun g ↦ (normℝ g ^ ε) • sLocalAdelicTheta F S f g) =O[smallNorm]
      (fun _ : Iₛ ↦ (1 : ℝ)) := by sorry

/-- Paper: Proposition 2.4.3.1(1), p. 113. The same small-norm bound
holds for homogeneous theta multiplied by a positive norm power.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_isBigO
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁) (f : ℬₛ) :
    (fun g ↦ (normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)) =O[smallNorm]
      (fun _ : Iₛ ↦ (1 : ℝ)) := by sorry

/-- Paper: Proposition 2.4.3.1(2), p. 113. Below a positive norm cutoff
the bound for theta times a positive norm power is uniform on a bounded
set of test functions. -/
theorem sLocalAdelicTheta_norm_pow_bounded (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < T →
      ‖(normℝ g ^ ε) • sLocalAdelicTheta F S f g‖ ≤ C := by sorry

/-- Paper: Proposition 2.4.3.1(2), p. 113. Below a positive norm cutoff
the corresponding homogeneous bound is uniform on a bounded set of test functions.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_bounded
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < T →
      ‖(normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C := by sorry

/-- Paper: Proposition 2.4.3.1(3), p. 113. The uniform bound for theta
times a positive norm power holds below S-idelic norm one. -/
theorem sLocalAdelicTheta_norm_pow_bounded_threshold_one
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖(normℝ g ^ ε) • sLocalAdelicTheta F S f g‖ ≤ C := by sorry

/-- Paper: Proposition 2.4.3.1(3), p. 113. The corresponding uniform
homogeneous bound holds below S-idelic norm one.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_bounded_threshold_one
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁)
    (B : Set ℬₛ) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : Iₛ, normℝ g < 1 →
      ‖(normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g)‖ ≤ C := by sorry

/-- Paper: Corollary 2.4.3.2, p. 115. Theta multiplied by any positive
real power of the S-idelic norm tends to zero as that norm tends to zero. -/
theorem sLocalAdelicTheta_norm_pow_tendsto_zero (f : ℬₛ) :
    Tendsto (fun g ↦ (normℝ g ^ ε) • sLocalAdelicTheta F S f g) smallNorm (𝓝 0) := by sorry

/-- Paper: Corollary 2.4.3.2, p. 115. The same vanishing holds for
homogeneous theta for every continuous character of the norm-one classes.
Deviation: As in §2.3, the norm-one class Haar measure is explicit. -/
theorem sLocalHomogeneousAdelicTheta_norm_pow_tendsto_zero
    (μ : Measure ↥J₁) [Measure.IsHaarMeasure μ] (ω : PontryaginDual J₁) (f : ℬₛ) :
    Tendsto (fun g ↦ (normℝ g ^ ε) • sLocalHomogeneousAdelicTheta F S μ ω f (classOf g))
      smallNorm (𝓝 0) := by sorry

end RiemannMasullo
