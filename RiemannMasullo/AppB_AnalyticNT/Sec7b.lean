module

public import RiemannMasullo.AppB_AnalyticNT.Sec7a
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Norm-ordered Euler products on the 1-line

Masullo, §B.7.2, pp. 648–653. The logarithmic series is grouped by prime-power
norm. The Euler products and the prime sum use a strict cutoff on prime norm.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Equation (B.7.2.2), p. 649. The function `g_n` uses the
oscillatory pole term with its constant term subtracted.
Deviation: At the removable singularity we use the limiting value `log n`
for positive `n`. -/
def heckePrimePowerTailOscillation (t₀ : ℝ) (n : ℕ) (s : ℂ) : ℂ :=
  if s = ⟨1, t₀⟩ then (Real.log n : ℂ)
  else ((n : ℂ) ^ ((⟨1, t₀⟩ : ℂ) - s) - 1) / ((⟨1, t₀⟩ : ℂ) - s)

/-- Paper: Equations (B.7.2.2) and (B.7.2.12), pp. 649–650.
For positive `n`, the oscillatory term tends to `log n` at the pole ordinate.
Deviation: The printed proof gives the opposite sign for `g_n / log n`. -/
theorem heckePrimePowerTailOscillation_tendsto_at_pole
    (t₀ : ℝ) {n : ℕ} (hn : 0 < n) :
    Tendsto (heckePrimePowerTailOscillation t₀ n)
      (𝓝[≠] (⟨1, t₀⟩ : ℂ)) (𝓝 (Real.log n : ℂ)) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hd : HasDerivAt (fun z : ℂ ↦ (n : ℂ) ^ z) (Real.log n : ℂ) 0 := by
    have h := (hasDerivAt_id (0 : ℂ)).const_cpow (c := (n : ℂ)) (Or.inl hn')
    simpa [Complex.natCast_log] using h
  have hmap : Tendsto (fun s : ℂ ↦ (⟨1, t₀⟩ : ℂ) - s) (𝓝[≠] (⟨1, t₀⟩ : ℂ)) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun s : ℂ ↦ (⟨1, t₀⟩ : ℂ) - s) (𝓝 (⟨1, t₀⟩ : ℂ)) (𝓝 0) := by
        have h' :=
          (tendsto_const_nhds (x := (⟨1, t₀⟩ : ℂ)) (f := 𝓝 (⟨1, t₀⟩ : ℂ))).sub tendsto_id
        rw [sub_self] at h'
        exact h'
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.mpr (Ne.symm hs)
  refine ((hasDerivAt_iff_tendsto_slope.mp hd).comp hmap).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s ≠ ⟨1, t₀⟩ := hs
  simp [heckePrimePowerTailOscillation, hs', slope_def_field]

/-- Paper: Remark B.7.2.2, p. 649. Index `k` represents the positive
exponent `k + 1`. The ideal character is zero on ramified prime powers. -/
def heckePrimePowerLogTerm (χ : U[F]) (v : V[F]) (k : ℕ) (s : ℂ) : ℂ :=
  heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1)) /
    ((k + 1 : ℕ) * ((v.asIdeal ^ (k + 1)).absNorm : ℂ) ^ s)

/-- Paper: Equation (B.7.2.15), p. 651. The exponent-one logarithmic term is
the ordinary prime term of the Hecke Dirichlet series. -/
theorem heckePrimePowerLogTerm_zero (χ : U[F]) (v : V[F]) (s : ℂ) :
    heckePrimePowerLogTerm χ v 0 s =
      heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal / (v.asIdeal.absNorm : ℂ) ^ s := by
  simp [heckePrimePowerLogTerm]

/-- Paper: Remark B.7.2.2 and Equation (B.7.2.4), p. 649. Dividing the
norm-grouped von Mangoldt coefficient by the logarithm of the norm gives
the coefficient of the logarithmic Euler series. The norms zero and one
have coefficient zero. -/
def heckePrimePowerLogCoefficient (χ : U[F]) (n : ℕ) : ℂ :=
  heckeLogDerivCoefficient (ideleClassNormTwist χ 0) n / (Real.log n : ℂ)

/-- Paper: Remark B.7.2.2, p. 649. The coefficient at `n` sums
`χ(𝔭^m) / m` over the positive prime powers of norm exactly `n`. -/
theorem heckePrimePowerLogCoefficient_eq_sum (χ : U[F]) (n : ℕ) :
    heckePrimePowerLogCoefficient χ n =
      ∑ᶠ a : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckeIdealValue (ideleClassNormTwist χ 0) (a.val.1.asIdeal ^ (a.val.2 + 1)) /
          ((a.val.2 + 1 : ℕ) : ℂ) := by
  classical
  have hpow (a : V[F] × ℕ) :
      (a.1.asIdeal ^ (a.2 + 1)).absNorm = a.1.asIdeal.absNorm ^ (a.2 + 1) := map_pow _ _ _
  let e : {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} →
      {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} := fun a ↦
    ⟨a.val.1.asIdeal ^ (a.val.2 + 1), pow_ne_zero _ a.val.1.ne_bot, (hpow a.val).trans a.property⟩
  have he : Function.Injective e := by
    rintro ⟨⟨v, k⟩, _⟩ ⟨⟨w, j⟩, _⟩ h
    have heq : v.asIdeal ^ (k + 1) = w.asIdeal ^ (j + 1) := congrArg Subtype.val h
    obtain rfl := HeightOneSpectrum.eq_of_dvd_pow ((dvd_pow_self _ k.succ_ne_zero).trans heq.dvd)
    exact Subtype.ext (Prod.ext rfl
      (Nat.succ.inj (pow_injective_of_not_isUnit v.prime.not_isUnit v.ne_bot heq)))
  have : Finite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n} :=
    Set.Finite.to_subtype (s := {I : Ideal (𝓞 F) | I ≠ ⊥ ∧ I.absNorm = n})
      ((Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 F) n).subset fun _ hI ↦ hI.2)
  have : Finite {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n} := Finite.of_injective e he
  have := Fintype.ofFinite {I : Ideal (𝓞 F) // I ≠ ⊥ ∧ I.absNorm = n}
  have := Fintype.ofFinite {a : V[F] × ℕ // a.1.asIdeal.absNorm ^ (a.2 + 1) = n}
  rw [heckePrimePowerLogCoefficient, heckeLogDerivCoefficient, finsum_eq_sum_of_fintype,
    finsum_eq_sum_of_fintype, Finset.sum_div]
  symm
  refine Finset.sum_bij_ne_zero (fun a _ _ ↦ e a) (fun _ _ _ ↦ Finset.mem_univ _)
    (fun _ _ _ _ _ _ h ↦ he h) ?_ ?_
  · intro I _ hI
    have hΛ : idealVonMangoldt I.val ≠ 0 := by
      intro h0
      apply hI
      simp [heckeIdealVonMangoldt, h0]
    unfold idealVonMangoldt at hΛ
    split_ifs at hΛ with hex
    · obtain ⟨v, k, hk, hI'⟩ := hex
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hn : v.asIdeal.absNorm ^ (j + 1) = n := by
        rw [← I.property.2, hI', map_pow]
      have hval : heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (j + 1)) ≠ 0 := by
        intro h0
        apply hI
        simp [heckeIdealVonMangoldt, hI', h0]
      exact ⟨⟨(v, j), hn⟩, Finset.mem_univ _,
        div_ne_zero hval (by exact_mod_cast j.succ_ne_zero), Subtype.ext hI'.symm⟩
    · exact absurd rfl hΛ
  · rintro ⟨⟨v, k⟩, rfl⟩ _ _
    have hv : (1 : ℝ) < v.asIdeal.absNorm := by
      exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
    have hlog : Real.log (v.asIdeal.absNorm : ℝ) ≠ 0 := (Real.log_pos hv).ne'
    change _ = heckeIdealVonMangoldt _ (v.asIdeal ^ (k + 1)) / _
    rw [heckeIdealVonMangoldt, idealVonMangoldt_prime_pow v k.succ_pos]
    push_cast
    rw [Real.log_pow]
    push_cast
    have hlogC : Complex.log (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      rw [← Complex.natCast_log]
      exact_mod_cast hlog
    field_simp

/-- Paper: Remark B.7.2.2, p. 649. This is the Dirichlet term for each
integer norm, with the terms below the cutoff replaced by zero. -/
def heckePrimePowerLogTailTerm (χ : U[F]) (x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if x ≤ (n : ℝ) then LSeries.term (heckePrimePowerLogCoefficient χ) s n else 0

/-- Paper: Remark B.7.2.2, p. 649. At a positive integer norm equal to the
cutoff, the tail includes the full Dirichlet term for that norm. -/
theorem heckePrimePowerLogTailTerm_at_cutoff (χ : U[F]) (s : ℂ) {n : ℕ} (hn : 0 < n) :
    heckePrimePowerLogTailTerm χ n s n =
      heckePrimePowerLogCoefficient χ n / (n : ℂ) ^ s := by
  simp only [heckePrimePowerLogTailTerm, le_refl, ↓reduceIte]
  rw [LSeries.term_of_ne_zero hn.ne']

/-- Paper: Remark B.7.2.2, p. 649. The logarithmic tail sums the norm-grouped
terms in increasing order of integer norm, starting at the first norm at least `x`. -/
def heckePrimePowerLogTail (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  tsum (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ)

/-- Paper: Remark B.7.2.2, p. 649, and the absolute convergence on p. 653.
To the right of one the same tail is the absolute sum over prime powers
whose norms are at least the cutoff. -/
theorem heckePrimePowerLogTail_hasSum_of_one_lt_re (χ : U[F]) (x : ℝ) (s : halfPlane) :
    HasSum (fun a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 1) : ℕ) : ℝ)} ↦
      heckePrimePowerLogTerm χ a.val.1 a.val.2 s) (heckePrimePowerLogTail χ x s) := by
  sorry

local notation "invLog(" n ")" => ((Real.log ((n : ℕ) : ℝ) : ℂ)⁻¹)

/-- Paper: Equations (B.7.2.1) and (B.7.2.19), pp. 649 and 652. These
are the oscillatory summands weighted by the difference of reciprocal
logarithms at successive norms at or above the cutoff. -/
def heckePrimePowerTailOscillationTerm (t₀ x : ℝ) (s : ℂ) (n : ℕ) : ℂ :=
  if x ≤ (n : ℝ) then
    heckePrimePowerTailOscillation t₀ (n - 1) s * (invLog(n) - invLog(n - 1))
  else 0

/-- On the 1-line away from the pole ordinate, the weighted oscillatory terms are bounded by
`2 / |t₀ - t|` times one summable majorant, the telescoping differences of reciprocal logarithms. -/
private theorem summable_heckePrimePowerTailOscillationTerm_bound (t₀ x : ℝ) (hx : 2 < x) :
    ∃ u : ℕ → ℝ, Summable u ∧ (∀ n, 0 ≤ u n) ∧ ∀ t : ℝ, t ≠ t₀ → ∀ n,
      ‖heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n‖ ≤ 2 / |t₀ - t| * u n := by
  let f : ℕ → ℝ := fun k ↦ (Real.log ((k + 2 : ℕ) : ℝ))⁻¹
  have hlog (k : ℕ) : 0 < Real.log ((k + 2 : ℕ) : ℝ) :=
    Real.log_pos (by push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])
  have hf_anti (k : ℕ) : f (k + 1) ≤ f k :=
    inv_anti₀ (hlog k) (Real.log_le_log (by positivity) (by push_cast; linarith))
  have htel : Summable (fun k ↦ f k - f (k + 1)) := by
    refine summable_of_sum_range_le (c := f 0) (fun k ↦ sub_nonneg.mpr (hf_anti k)) fun n ↦ ?_
    rw [Finset.sum_range_sub']
    linarith [inv_nonneg.mpr (hlog n).le]
  let u : ℕ → ℝ := fun n ↦ if 3 ≤ n then f (n - 3) - f (n - 3 + 1) else 0
  have hu3 (k : ℕ) : u (k + 3) = f k - f (k + 1) := by simp [u]
  have hu0 (n : ℕ) : 0 ≤ u n := by
    simp only [u]
    split_ifs
    · exact sub_nonneg.mpr (hf_anti _)
    · exact le_rfl
  refine ⟨u, (summable_nat_add_iff 3).mp (by simpa only [hu3] using htel), hu0, fun t ht n ↦ ?_⟩
  set s : ℂ := ⟨1, t⟩
  have hws : (⟨1, t₀⟩ : ℂ) - s ≠ 0 := by
    intro h
    apply ht
    have := congrArg Complex.im h
    simp [s] at this
    linarith
  have hre : ((⟨1, t₀⟩ : ℂ) - s).re = 0 := by simp [s]
  have hnorm : ‖(⟨1, t₀⟩ : ℂ) - s‖ = |t₀ - t| := by
    rw [Complex.norm_eq_sqrt_sq_add_sq, hre]
    simp [s, Real.sqrt_sq_eq_abs]
  have hg (m : ℕ) : ‖heckePrimePowerTailOscillation t₀ m s‖ ≤ 2 / |t₀ - t| := by
    have hsw : s ≠ ⟨1, t₀⟩ := fun h ↦ hws (by rw [h, sub_self])
    simp only [heckePrimePowerTailOscillation, hsw, ↓reduceIte, norm_div, ← hnorm]
    apply div_le_div_of_nonneg_right _ (norm_nonneg _)
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one]
    have : ‖(m : ℂ) ^ ((⟨1, t₀⟩ : ℂ) - s)‖ ≤ 1 := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [Nat.cast_zero, Complex.zero_cpow hws, norm_zero]
        exact zero_le_one
      · rw [Complex.norm_natCast_cpow_of_pos hm, hre, Real.rpow_zero]
    linarith
  have hd (k : ℕ) : ‖((Real.log ((k + 3 : ℕ) : ℝ) : ℂ))⁻¹ - ((Real.log ((k + 2 : ℕ) : ℝ) : ℂ))⁻¹‖ =
      f k - f (k + 1) := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (hf_anti k))]
  have hC : 0 ≤ 2 / |t₀ - t| := by positivity
  simp only [heckePrimePowerTailOscillationTerm]
  split_ifs with hxn
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := by
      refine ⟨n - 3, ?_⟩
      have : (2 : ℝ) < n := hx.trans_le hxn
      have : 2 < n := by exact_mod_cast this
      omega
    rw [norm_mul, show k + 3 - 1 = k + 2 by omega, hd k, hu3]
    exact mul_le_mul_of_nonneg_right (hg _) (sub_nonneg.mpr (hf_anti k))
  · rw [norm_zero]
    exact mul_nonneg hC (hu0 n)

/-- Paper: Equations (B.7.2.1) and (B.7.2.19), pp. 649 and 652. The weighted
oscillatory terms are summable on the 1-line away from the pole.
Deviation: The cutoff is greater than two so the reciprocal logarithms
in the tail have nonzero denominators. -/
theorem summable_heckePrimePowerTailOscillationTerm (t₀ x t : ℝ) (hx : 2 < x) (ht : t ≠ t₀) :
    Summable (heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩) := by
  obtain ⟨u, hu, -, hb⟩ := summable_heckePrimePowerTailOscillationTerm_bound t₀ x hx
  exact Summable.of_norm_bounded (hu.mul_left _) (hb t ht)

/-- Paper: Theorem B.7.2.1(1), pp. 649–651. For a pure norm character,
the grouped logarithmic tail converges uniformly on compact sets away from
the pole. The oscillatory terms give the displayed main term and the continuous
error is bounded uniformly by `2 ε / log x`.
Deviation: The formula holds for all sufficiently large real cutoffs. Partial summation
uses only integer endpoints, including `M - 1`. The threshold exceeds two. -/
theorem heckePrimePowerLogTail_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ ∀ x ≥ x₀,
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
        (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K ∧
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        heckePrimePowerLogTail χ x ⟨1, t⟩ =
          -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) +
            error t - ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n := by
  sorry

/-- Paper: Theorem B.7.2.1(2), pp. 649–651. For a character nontrivial on
the norm-one subgroup the grouped tail converges uniformly on each compact set
on the 1-line. Its limit is continuous and uniformly smaller than `2 ε / log x`.
Deviation: The compact set of ordinates refers to `1 + iK`, as in the
equation and the convergence clause. -/
theorem heckePrimePowerLogTail_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x ≥ x₀,
      TendstoUniformlyOn
        (fun N : ℕ ↦ fun t : ℝ ↦
          ∑ n ∈ Finset.range N, heckePrimePowerLogTailTerm χ x ⟨1, t⟩ n)
        (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) atTop K ∧
      ContinuousOn (fun t : ℝ ↦ heckePrimePowerLogTail χ x ⟨1, t⟩) K ∧
      ∀ t ∈ K, ‖heckePrimePowerLogTail χ x ⟨1, t⟩‖ < 2 * ε / Real.log x := by
  sorry

-- TODO(paper-gap): The proof on p. 651 uses a uniform bound for the Perron error
-- on the entire 1-line. The compact-set estimates of §B.7.1 suffice here.

/-- Paper: Equation (B.7.2.15), p. 651. This finite set contains the
finite places whose prime ideals have norm strictly below `x`. -/
def heckePrimesBelow (F : Type*) [Field F] [NumberField F] (x : ℝ) : Finset (V[F]) :=
  (Ring.HasFiniteQuotients.finite_absNorm_heightOneSpectrum_le (S := 𝓞 F)
    (⌈x⌉₊ - 1)).toFinset

/-- Paper: Equation (B.7.2.15), p. 651. The strict cutoff excludes primes of
norm exactly `x`, including when `x` is an integer. -/
theorem heckePrimesBelow_mem_iff (v : V[F]) (x : ℝ) :
    v ∈ heckePrimesBelow F x ↔ (v.asIdeal.absNorm : ℝ) < x := by
  have hN : v.asIdeal.absNorm ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  simp only [heckePrimesBelow, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  rw [← Nat.lt_ceil]
  omega

/-- Paper: Corollary B.7.2.3, p. 651. For a character nontrivial on the
norm-one subgroup, the prime sum converges locally uniformly on the 1-line. -/
theorem heckePrimeSum_tendstoLocallyUniformly_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop := by
  sorry

/-- Paper: Corollary B.7.2.3, p. 651. For a pure norm character, the
prime sum converges locally uniformly on the 1-line away from the pole. -/
theorem heckePrimeSum_tendstoLocallyUniformlyOn_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    ∃ limit : ℝ → ℂ, TendstoLocallyUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦
        ∑ v ∈ heckePrimesBelow F x, heckePrimePowerLogTerm χ v 0 ⟨1, t⟩)
      limit atTop ({t₀}ᶜ : Set ℝ) := by
  sorry

/-- Paper: Equation (B.7.2.17), p. 652. The reciprocal partial Euler product
uses the finite Euler factors with prime norm strictly below the cutoff.
Deviation: The strict cutoff extends the definition to real `x`. -/
def reciprocalHeckeEulerProductBelow (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  reciprocalPartialHeckeEulerProduct χ (heckePrimesBelow F x) s

/-- Paper: Equation (B.7.2.17), p. 652. Each prime below the strict cutoff
contributes its linear Euler polynomial, with coefficient zero at ramified primes. -/
theorem reciprocalHeckeEulerProductBelow_eq_prod (χ : U[F]) (x : ℝ) (s : ℂ) :
    reciprocalHeckeEulerProductBelow χ x s =
      ∏ v ∈ heckePrimesBelow F x,
        (1 - heckeIdealValue (ideleClassNormTwist χ 0) v.asIdeal *
          (v.asIdeal.absNorm : ℂ) ^ (-s)) := by
  classical
  unfold reciprocalHeckeEulerProductBelow reciprocalPartialHeckeEulerProduct
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  have h := heckeIdealValue_prime_pow (ideleClassNormTwist χ 0) v (k := 1) one_pos
  rw [pow_one] at h
  rw [h, finiteHeckeEulerFactor]
  by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v <;> simp [hv]

/-- Paper: Equation (B.7.2.19), p. 652. This is the oscillatory part of
the logarithmic tail for a pure norm character, evaluated at ordinate `t`.
Deviation: The first term uses `t₀ - t` in its denominator, as required by
Equation (B.7.2.1). Its use is on the complement of the pole ordinate. -/
def heckeEulerProductOscillation (t₀ x t : ℝ) : ℂ :=
  -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) -
    ∑' n : ℕ, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n

/-- Paper: Equation (B.7.2.19), p. 652. On compact sets away from the pole,
the endpoint term minus the finite correction sums converges uniformly to `G_x`.
Deviation: The cutoff is greater than two so `log (M - 1)` is nonzero. -/
theorem heckeEulerProductOscillation_tendstoUniformlyOn (t₀ x : ℝ) (hx : 2 < x)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    TendstoUniformlyOn (fun N : ℕ ↦ fun t : ℝ ↦
      -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1) -
        ∑ n ∈ Finset.range N, heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n)
      (heckeEulerProductOscillation t₀ x) atTop K := by
  obtain ⟨u, hu, hu0, hb⟩ := summable_heckePrimePowerTailOscillationTerm_bound t₀ x hx
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact tendstoUniformlyOn_empty
  obtain ⟨t₁, ht₁K, hmin⟩ := hK.exists_isMinOn hKne
    ((continuous_const.sub continuous_id).abs.continuousOn (s := K) (f := fun t : ℝ ↦ |t₀ - t|))
  have hδ : 0 < |t₀ - t₁| := abs_pos.mpr (sub_ne_zero.mpr fun h ↦ hpole (h ▸ ht₁K))
  have hM : ∀ n, ∀ t ∈ K,
      ‖heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n‖ ≤ 2 / |t₀ - t₁| * u n := by
    intro n t ht
    refine (hb t (fun h ↦ hpole (h ▸ ht)) n).trans (mul_le_mul_of_nonneg_right ?_ (hu0 n))
    exact div_le_div_of_nonneg_left (by norm_num) hδ (isMinOn_iff.mp hmin t ht)
  have hT := tendstoUniformlyOn_tsum_nat
    (f := fun n t ↦ heckePrimePowerTailOscillationTerm t₀ x ⟨1, t⟩ n) (hu.mul_left _) hM
  have hA : TendstoUniformlyOn
      (fun (_ : ℕ) (t : ℝ) ↦
        -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1))
      (fun t : ℝ ↦ -heckePrimePowerTailOscillation t₀ (⌈x⌉₊ - 1) ⟨1, t⟩ * invLog(⌈x⌉₊ - 1))
      atTop K :=
    fun v hv ↦ Filter.Eventually.of_forall fun _ _ _ ↦ refl_mem_uniformity hv
  exact hA.sub hT

/-- Paper: Theorem B.7.2.4(1), Equation (B.7.2.19), p. 652. The oscillatory
part is real analytic away from the pole ordinate.
Deviation: The cutoff is greater than two so `log (M - 1)` is nonzero. -/
theorem heckeEulerProductOscillation_analyticOnNhd (t₀ x : ℝ) (hx : 2 < x) :
    AnalyticOnNhd ℝ (heckeEulerProductOscillation t₀ x) ({t₀}ᶜ : Set ℝ) := by
  sorry

/-- Paper: Equation (B.7.2.19), p. 652. The oscillatory part is uniformly
`O(1 / log x)` on any compact set of ordinates away from the pole. -/
theorem heckeEulerProductOscillation_bound (t₀ : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop, ∀ t ∈ K,
      ‖heckeEulerProductOscillation t₀ x t‖ ≤ C / Real.log x := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction `H_x` is minus
the logarithmic terms whose primes lie below the cutoff but whose powers
have reached or exceeded it. Such powers have exponent at least two. -/
def heckeEulerProductLogCorrection (χ : U[F]) (x : ℝ) (s : ℂ) : ℂ :=
  -(∑' a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
      heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s)

/-- Paper: Theorem B.7.2.4(1), p. 652. The positive majorant over prime powers
of exponent at least two is summable for an abscissa greater than one half. -/
theorem summable_heckeHigherPrimePowerWeights (F : Type*) [Field F] [NumberField F]
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun a : V[F] × ℕ ↦
      (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ σ))) := by
  have hσ0 : 0 < σ := by linarith
  have hP : Summable (fun v : V[F] ↦ (v.asIdeal.absNorm : ℝ) ^ (-(2 * σ))) :=
    (summable_absNorm_rpow F (by linarith : 1 < 2 * σ)).comp_injective
      HeightOneSpectrum.asIdeal_injective
  have hρ : Summable (fun k : ℕ ↦ ((2 : ℝ) ^ (-σ)) ^ k) :=
    summable_geometric_of_lt_one (by positivity)
      (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))
  refine (Summable.mul_of_nonneg hP hρ (fun _ ↦ by positivity)
    (fun _ ↦ by positivity)).of_nonneg_of_le (fun _ ↦ by positivity) fun a ↦ ?_
  obtain ⟨v, k⟩ := a
  have hN : (2 : ℝ) ≤ v.asIdeal.absNorm := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  set N : ℝ := ((v.asIdeal.absNorm : ℕ) : ℝ) with hNdef
  have hN0 : 0 < N := by linarith
  dsimp only
  push_cast
  rw [← hNdef]
  have hk : (1 : ℝ) ≤ k + 2 := by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  calc 1 / (((k : ℝ) + 2) * (N ^ (k + 2)) ^ σ) ≤ 1 / (N ^ (k + 2)) ^ σ := by
        apply one_div_le_one_div_of_le (by positivity)
        exact le_mul_of_one_le_left (by positivity) hk
    _ = N ^ (-(2 * σ)) * (N ^ (-σ)) ^ k := by
        rw [← Real.rpow_natCast N, ← Real.rpow_mul hN0.le, ← Real.rpow_natCast (N ^ (-σ)),
          ← Real.rpow_mul hN0.le, ← Real.rpow_add hN0, one_div, ← Real.rpow_neg hN0.le]
        congr 1
        push_cast
        ring
    _ ≤ N ^ (-(2 * σ)) * ((2 : ℝ) ^ (-σ)) ^ k := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (by positivity)
          (Real.rpow_le_rpow_of_nonpos (by norm_num) hN (by linarith)) k

/-- Paper: Theorem B.7.2.4(1), p. 652. The series defining the correction
converges absolutely and uniformly on half-planes strictly to the right of one half.
Its sum is the negative of `H_x`. -/
theorem heckeEulerProductLogCorrection_hasSumUniformlyOn (χ : U[F]) (x : ℝ)
    {σ : ℝ} (hσ : 1 / 2 < σ) :
    HasSumUniformlyOn
      (fun (a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
        x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)}) s ↦
        heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s)
      (fun s ↦ -heckeEulerProductLogCorrection χ x s) {s : ℂ | σ ≤ s.re} := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction has norm at most
the tail of the positive majorant with prime-power norm at least `x`.
Deviation: The absolute majorant is evaluated at the real part of `s`. -/
theorem heckeEulerProductLogCorrection_norm_le (χ : U[F]) (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re) :
    ‖heckeEulerProductLogCorrection χ x s‖ ≤
      ∑' a : {a : V[F] × ℕ // x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)},
        (1 : ℝ) / ((a.val.2 + 2 : ℕ) *
          (((a.val.1.asIdeal.absNorm ^ (a.val.2 + 2) : ℕ) : ℝ) ^ s.re)) := by
  classical
  let w : V[F] × ℕ → ℝ := fun a ↦
    (1 : ℝ) / ((a.2 + 2 : ℕ) * (((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ) ^ s.re))
  have hw : Summable w := summable_heckeHigherPrimePowerWeights F hs
  have hbound (a : V[F] × ℕ) : ‖heckePrimePowerLogTerm χ a.1 (a.2 + 1) s‖ ≤ w a := by
    obtain ⟨v, k⟩ := a
    have hval : ‖heckeIdealValue (ideleClassNormTwist χ 0) (v.asIdeal ^ (k + 1 + 1))‖ ≤ 1 := by
      rw [heckeIdealValue_prime_pow _ v (Nat.succ_pos _)]
      split_ifs
      · rw [norm_pow, norm_ideleClassNormTwist_zero_localValue, one_pow]
      · simp
    have hpos : 0 < (v.asIdeal ^ (k + 1 + 1)).absNorm :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (pow_ne_zero _ v.ne_bot))
    simp only [heckePrimePowerLogTerm, w]
    rw [norm_div, norm_mul, Complex.norm_natCast, Complex.norm_natCast_cpow_of_pos hpos, map_pow]
    exact div_le_div_of_nonneg_right hval (by positivity)
  have hA : Summable (fun a : {a : V[F] × ℕ // (a.1.asIdeal.absNorm : ℝ) < x ∧
      x ≤ ((a.1.asIdeal.absNorm ^ (a.2 + 2) : ℕ) : ℝ)} ↦
        ‖heckePrimePowerLogTerm χ a.val.1 (a.val.2 + 1) s‖) :=
    (hw.subtype _).of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun a ↦ hbound a.val)
  rw [heckeEulerProductLogCorrection, norm_neg]
  refine (norm_tsum_le_tsum_norm hA).trans ?_
  exact hA.tsum_le_tsum_of_inj (fun a ↦ ⟨a.val, a.property.2⟩)
    (fun a b h ↦ Subtype.ext (by simpa using congrArg Subtype.val h))
    (fun _ _ ↦ by positivity)
    (fun a ↦ hbound a.val) (hw.subtype _)

/-- Paper: Theorem B.7.2.4(1), p. 652. The correction tends to zero
uniformly on the whole 1-line. -/
theorem heckeEulerProductLogCorrection_tendstoUniformly (χ : U[F]) :
    TendstoUniformly (fun x : ℝ ↦ fun t : ℝ ↦ heckeEulerProductLogCorrection χ x ⟨1, t⟩)
      (fun _ ↦ 0) atTop := by
  sorry

/-- Paper: Theorem B.7.2.4(1), p. 652. Off the pole, multiplying the
reciprocal partial product by the continued finite L-function gives the
exponential of the oscillation, the cutoff correction and a small continuous error.
Deviation: Uses the sign-corrected oscillation from Equation (B.7.2.19).
The cutoff threshold is greater than two. Real cutoffs have the same strict
norm rule as integer cutoffs. -/
theorem reciprocalHeckeEulerProductBelow_mul_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 2 < x₀ ∧ ∀ x ≥ x₀,
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
          Complex.exp (error t + heckeEulerProductOscillation t₀ x t +
            heckeEulerProductLogCorrection χ x ⟨1, t⟩) := by
  sorry

/-- Paper: Theorem B.7.2.4(1), Equation (B.7.2.20), p. 652. The product
with the finite L-function tends uniformly to one on compact sets away from the pole. -/
theorem reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_normTwist
    (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) (hpole : t₀ ∉ K) :
    TendstoUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩)
      (fun _ ↦ 1) atTop K := by
  sorry

/-- Paper: Theorem B.7.2.4(2), Equation (B.7.2.21), p. 652. For a
character nontrivial on the norm-one subgroup the product with the finite
L-function has an exponential comparison on every compact set of ordinates.
Deviation: Uses `+ H_x` from the definition of the correction, in agreement
with (B.7.2.18). Real cutoffs have the same strict norm rule as integer cutoffs. -/
theorem reciprocalHeckeEulerProductBelow_mul_of_nontrivial_on_normOne (χ : U[F])
    (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ x₀ : ℝ, 1 < x₀ ∧ ∀ x ≥ x₀,
      ∃ error : ℝ → ℂ, ContinuousOn error K ∧ ∀ t ∈ K,
        ‖error t‖ ≤ 2 * ε / Real.log x ∧
        reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩ =
          Complex.exp (error t + heckeEulerProductLogCorrection χ x ⟨1, t⟩) := by
  sorry

/-- Paper: Theorem B.7.2.4(2), Equation (B.7.2.22), p. 652. For a
character nontrivial on the norm-one subgroup the product with the finite
L-function tends uniformly to one on every compact set of ordinates. -/
theorem reciprocalHeckeEulerProductBelow_mul_tendstoUniformlyOn_of_nontrivial_on_normOne
    (χ : U[F]) (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩ * L ⟨1, t⟩)
      (fun _ ↦ 1) atTop K := by
  sorry

/-- Paper: Equation (B.7.2.23), p. 653. At a regular nonzero point of the
continued L-function on or to the right of the 1-line, the norm-ordered
logarithmic tail and its correction give the reciprocal product comparison.
Deviation: Uses `+ H_x` and exponentiates to avoid selecting a logarithm branch.
The convergence of the ordered sum is explicit. -/
theorem reciprocalHeckeEulerProductBelow_mul_eq_exp_logTail (χ : U[F]) {x : ℝ} (hx : 1 < x)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s)
    (s : ℂ) (hs : 1 ≤ s.re) (hregular : meromorphicOrderAt L s = 0) :
    Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ) ∧
      reciprocalHeckeEulerProductBelow χ x s * L s =
        Complex.exp (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s) := by
  sorry

/-- Paper: Equation (B.7.2.23), p. 653. The logarithmic tail restricted to
primes of norm at least `x`, grouped by prime-power norm, is the full
prime-power tail plus the cutoff correction.
Deviation: Adds `H_x`, which already carries the minus sign. -/
theorem heckePrimePowerLogTail_add_correction (χ : U[F]) (x : ℝ) (s : ℂ)
    (hs : 1 / 2 < s.re)
    (hsum : Summable (heckePrimePowerLogTailTerm χ x s) (SummationFilter.conditional ℕ)) :
    HasSum (fun n : ℕ ↦
      ∑ᶠ a : {a : V[F] × ℕ // x ≤ (a.1.asIdeal.absNorm : ℝ) ∧
        a.1.asIdeal.absNorm ^ (a.2 + 1) = n},
        heckePrimePowerLogTerm χ a.val.1 a.val.2 s)
      (heckePrimePowerLogTail χ x s + heckeEulerProductLogCorrection χ x s)
      (SummationFilter.conditional ℕ) := by
  sorry

/-- Paper: Corollary B.7.2.5, Equation (B.7.2.24), p. 653. For a character
nontrivial on the norm-one subgroup, the prime-norm-ordered Euler product
converges locally uniformly to the continued finite L-function on the 1-line. -/
theorem heckeEulerProductBelow_tendstoLocallyUniformly_of_nontrivial_on_normOne
    (χ : U[F]) (hχ : χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype ≠ 1)
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformly
      (fun x : ℝ ↦ fun t : ℝ ↦ ∏ v ∈ heckePrimesBelow F x, finiteHeckeEulerFactor χ v ⟨1, t⟩)
      (fun t : ℝ ↦ L ⟨1, t⟩) atTop := by
  sorry

/-- Paper: Corollary B.7.2.5, Equation (B.7.2.24), p. 653. For a pure
norm character, the prime-norm-ordered Euler product converges locally uniformly
to the continued finite L-function off the pole ordinate. -/
theorem heckeEulerProductBelow_tendstoLocallyUniformlyOn_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformlyOn
      (fun x : ℝ ↦ fun t : ℝ ↦ ∏ v ∈ heckePrimesBelow F x, finiteHeckeEulerFactor χ v ⟨1, t⟩)
      (fun t : ℝ ↦ L ⟨1, t⟩) atTop ({t₀}ᶜ : Set ℝ) := by
  sorry

/-- A pure norm power of the trivial character is unramified at every finite place, and its
value on a uniformizer is the inverse norm of the place raised to the exponent. -/
private theorem reciprocalHeckeEulerProductBelow_at_pole_eq_prod_local (χ : U[F]) (b : ℂ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) b) (v : V[F]) :
    (ideleClassNormTwist χ 0).IsUnramifiedAt v ∧
      (ideleClassNormTwist χ 0).localValue v = (v.asIdeal.absNorm : ℂ) ^ (-b) := by
  have hval (u : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist χ 0).restrict v u = (‖(u : v.adicCompletion F)‖ : ℂ) ^ b := by
    rw [hχ, HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u
    change (((1 : U[F]) g : Circle) : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ b = _
    rw [show ideleClassNorm F g = _ from ideleClassNorm_ofAdicCompletion F v u]
    simp
  have hu : (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
    apply HeckeCharacter.isUnramifiedAt_iff.mpr
    intro x
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom x
    change (ideleClassNormTwist χ 0).restrict v u = 1
    rw [hval, show ‖(u : v.adicCompletion F)‖ = 1 from ?_, Complex.ofReal_one, Complex.one_cpow]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
      (show u ∈ (v.adicCompletionIntegers F).units from ⟨x.val.property, x.inv.property⟩)
  refine ⟨hu, ?_⟩
  let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
  have hn : ‖(u : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹ := by
    have hv : Valued.v (π : v.adicCompletion F) = WithZero.exp (-1 : ℤ) := hπ.trans
      (congrArg Units.val (Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
        (v.valuedAdicCompletion_surjective F)))
    change ‖(π : v.adicCompletion F)‖ = (v.asIdeal.absNorm : ℝ)⁻¹
    rw [FinitePlace.norm_def, hv, WithZeroMulInt.toNNReal_neg_apply _ (by simp)]
    simp
  rw [hu.localValue_eq u hπ, hval, hn, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) b, ← Complex.cpow_neg,
    Complex.ofReal_natCast]

/-- Paper: Remark B.7.2.6, Equation (B.7.2.25), p. 653. At the pole
ordinate the reciprocal product for a pure norm character equals the untwisted
Mertens product. -/
theorem reciprocalHeckeEulerProductBelow_at_pole_eq_prod (χ : U[F]) (t₀ x : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    reciprocalHeckeEulerProductBelow χ x ⟨1, t₀⟩ =
      ∏ v ∈ heckePrimesBelow F x, (1 - (v.asIdeal.absNorm : ℂ)⁻¹) := by
  classical
  rw [reciprocalHeckeEulerProductBelow_eq_prod]
  refine Finset.prod_congr rfl fun v _ ↦ ?_
  obtain ⟨hu, hl⟩ := reciprocalHeckeEulerProductBelow_at_pole_eq_prod_local χ _ hχ v
  have h := heckeIdealValue_prime_pow (ideleClassNormTwist χ 0) v (k := 1) one_pos
  simp only [pow_one, hu, ↓reduceIte] at h
  have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  rw [h, hl, ← Complex.cpow_add _ _ hq,
    show -(-Complex.I * t₀) + -(⟨1, t₀⟩ : ℂ) = -1 by apply Complex.ext <;> simp,
    Complex.cpow_neg_one]

/-- Paper: Remark B.7.2.6, Equation (B.7.2.25), p. 653. Multiplying
the Mertens product at the pole ordinate by the logarithm of the cutoff gives
a limit of `exp (-γ)` divided by the norm-one class volume. -/
theorem reciprocalHeckeEulerProductBelow_mertens (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀)) :
    Tendsto (fun x : ℝ ↦ (Real.log x : ℂ) * reciprocalHeckeEulerProductBelow χ x ⟨1, t₀⟩)
      atTop (𝓝 ((Real.exp (-Real.eulerMascheroniConstant) /
        (normOneIdeleClassTamagawaMeasure F univ).toReal : ℝ) : ℂ)) := by
  sorry

/-- Paper: Remark B.7.2.7, p. 653. For a pure norm character the reciprocal
partial products tend locally uniformly on the 1-line to the reciprocal of the
continued finite L-function. Its reciprocal takes the removable value zero at the pole.
Deviation: Local uniform convergence holds across the pole ordinate as well (R27). -/
theorem reciprocalHeckeEulerProductBelow_tendstoLocallyUniformly_normTwist (χ : U[F]) (t₀ : ℝ)
    (hχ : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀))
    (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ) (hSeries : ∀ s : halfPlane, L s = finiteHeckeL χ s) :
    TendstoLocallyUniformly (fun x : ℝ ↦ fun t : ℝ ↦ reciprocalHeckeEulerProductBelow χ x ⟨1, t⟩)
      (fun t : ℝ ↦ (L ⟨1, t⟩)⁻¹) atTop := by
  sorry

end RiemannMasullo
