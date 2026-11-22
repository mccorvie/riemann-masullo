module

public import RiemannMasullo.AppB_AnalyticNT.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec5
public import RiemannMasullo.Ch03_IdelicZeta.Sec3b

import all RiemannMasullo.Ch02_AdelicTheta.Sec2a
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gaussian.Schwartz

/-!
# §7.1.1–7.1.2 Almost periodic functions and S-local theta asymptotics

The finite set `S` lists the finite places. All archimedean places are included.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set
open scoped BigOperators NNReal Topology

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F

-- The Euler product, its reciprocal, and the upper density in (7.1.1.1),
-- (7.1.1.2), and (7.1.1.4) use the constructions of §B.5.3.

-- TODO(paper-gap): Lemma 7.1.1.1(1) forces T₀ = 0. The trivial character of ℚ
-- with a finite place above 2 has a pole at σ = T₀ = 0. For ramified places in S,
-- the phase in the printed product is undefined. Equation (7.1.1.3) also reverses
-- the phase sign in (7.1.1.1).

/-- A factor `1 - u r` with `r ∈ [m, M]` and `0 < m` has norm at least
`max (m |Im u|) (1 - M max (Re u) 0)`, a continuous function of `u` alone. -/
private theorem exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_factor
    (u : ℂ) {m M r : ℝ} (hm : 0 < m) (hr : r ∈ Icc m M) :
    max (m * |u.im|) (1 - M * max u.re 0) ≤ ‖1 - u * (r : ℂ)‖ := by
  have hr0 : 0 ≤ r := hm.le.trans hr.1
  refine max_le ?_ ?_
  · calc m * |u.im| ≤ r * |u.im| := mul_le_mul_of_nonneg_right hr.1 (abs_nonneg _)
      _ = |(1 - u * (r : ℂ)).im| := by
          simp [abs_mul, abs_of_nonneg hr0, mul_comm]
      _ ≤ ‖1 - u * (r : ℂ)‖ := Complex.abs_im_le_norm _
  · have h1 : r * u.re ≤ r * max u.re 0 := mul_le_mul_of_nonneg_left (le_max_left _ _) hr0
    have h2 : r * max u.re 0 ≤ M * max u.re 0 :=
      mul_le_mul_of_nonneg_right hr.2 (le_max_right _ _)
    calc 1 - M * max u.re 0 ≤ 1 - u.re * r := by nlinarith
      _ = (1 - u * (r : ℂ)).re := by simp
      _ ≤ ‖1 - u * (r : ℂ)‖ := Complex.re_le_norm _

private theorem exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_eventually_pos
    (z : ℂ) {ω m M : ℝ} (hω : ω ≠ 0) (hm : 0 < m) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < max (m * |(z * (Circle.exp (t * ω) : ℂ)).im|)
      (1 - M * max (z * (Circle.exp (t * ω) : ℂ)).re 0) := by
  have hc : Continuous (fun t : ℝ ↦ max (m * |(z * (Circle.exp (t * ω) : ℂ)).im|)
      (1 - M * max (z * (Circle.exp (t * ω) : ℂ)).re 0)) := by fun_prop
  by_cases h0 : 0 < max (m * |z.im|) (1 - M * max z.re 0)
  · have h0' : 0 < (fun t : ℝ ↦ max (m * |(z * (Circle.exp (t * ω) : ℂ)).im|)
        (1 - M * max (z * (Circle.exp (t * ω) : ℂ)).re 0)) 0 := by simpa using h0
    exact ((hc.tendsto 0).mono_left nhdsWithin_le_nhds).eventually (lt_mem_nhds h0')
  · rw [not_lt, max_le_iff] at h0
    have him : z.im = 0 := by
      have := h0.1
      have : |z.im| ≤ 0 := by nlinarith [abs_nonneg z.im]
      exact abs_nonpos_iff.mp this
    have hre : 0 < z.re := by
      by_contra h
      rw [max_eq_right (not_lt.mp h)] at h0
      linarith [h0.2]
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (Real.pi / |ω|) :=
      Ioo_mem_nhdsGT (by positivity)
    filter_upwards [hI] with t ht
    apply lt_max_of_lt_left
    apply mul_pos hm
    apply abs_pos.mpr
    rw [Circle.coe_exp, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, him, zero_mul, add_zero]
    refine mul_ne_zero hre.ne' ?_
    have hω' : 0 < |ω| := abs_pos.mpr hω
    have hlt : |t * ω| < Real.pi := by
      rw [abs_mul, abs_of_pos ht.1]
      have := ht.2
      rwa [lt_div_iff₀ hω'] at this
    intro hs
    rw [Real.sin_eq_zero_iff_of_lt_of_lt (by linarith [neg_abs_le (t * ω)])
      (lt_of_le_of_lt (le_abs_self _) hlt)] at hs
    exact (mul_ne_zero ht.1.ne' hω) hs

private theorem exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_phaseShift
    {ι : Type*} [Fintype ι] (a : ι → ℂ) (ω : ι → ℝ) (hω : ∀ i, ω i ≠ 0) (m M : ι → ℝ)
    (hm : ∀ i, 0 < m i) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : ι → Circle, ∃ t ∈ Ioo (0 : ℝ) 1, ∀ r : ι → ℝ,
      (∀ i, r i ∈ Icc (m i) (M i)) →
      c ≤ ‖∏ i, (1 - a i * (x i : ℂ) * (Circle.exp (t * ω i) : ℂ) * (r i : ℂ))‖ := by
  classical
  let h (i : ι) (u : ℂ) : ℝ := max (m i * |u.im|) (1 - M i * max u.re 0)
  let Q (t : ℝ) (x : ι → Circle) : ℝ :=
    ∏ i, h i (a i * (x i : ℂ) * (Circle.exp (t * ω i) : ℂ))
  have hQ (t : ℝ) : Continuous (Q t) := by
    dsimp [Q, h]
    fun_prop
  have hshift (x : ι → Circle) : ∃ t ∈ Ioo (0 : ℝ) 1, 0 < Q t x := by
    have hI : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo (0 : ℝ) 1 := Ioo_mem_nhdsGT zero_lt_one
    obtain ⟨t, ht, hf⟩ := (hI.and (eventually_all.mpr fun i ↦
      exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_eventually_pos
        (a i * x i) (M := M i) (hω i) (hm i))).exists
    exact ⟨t, ht, Finset.prod_pos fun i _ ↦ hf i⟩
  choose t ht hpos using hshift
  let d (x : ι → Circle) := Q (t x) x / 2
  let U (x : ι → Circle) := {y | d x < Q (t x) y}
  have hU (x) : U x ∈ 𝓝 x :=
    (isOpen_lt continuous_const (hQ (t x))).mem_nhds (half_lt_self (hpos x))
  obtain ⟨s, hs⟩ := CompactSpace.elim_nhds_subcover U hU
  have cover (y : ι → Circle) : ∃ x ∈ s, y ∈ U x := by
    have : y ∈ ⋃ x ∈ s, U x := hs ▸ mem_univ y
    simpa only [mem_iUnion, exists_prop] using this
  obtain ⟨x, hx, _⟩ := cover 1
  obtain ⟨z, _, hz⟩ := s.exists_min_image d ⟨x, hx⟩
  refine ⟨d z, half_pos (hpos z), fun y ↦ ?_⟩
  obtain ⟨x, hx, hy⟩ := cover y
  refine ⟨t x, ht x, fun r hr ↦ (hz x hx).trans ((le_of_lt hy).trans ?_)⟩
  rw [norm_prod]
  exact Finset.prod_le_prod₀ (fun i _ ↦ le_max_of_le_left (mul_nonneg (hm i).le (abs_nonneg _)))
    fun i _ ↦ exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_factor
      _ (hm i) (hr i)

/-- Paper: Lemma 7.1.1.1, p. 313.
There are ordered heights escaping to infinity on both tails at which the finite Euler
product is uniformly bounded on the closed strip from `-δ` to `1 + δ`.
Deviation: Uses the sign convention for index zero from §B.5.3.2 and the Euler factors
of §3.2.1, with factor one at ramified places. A positive lower bound on the reciprocal
product expresses both the upper bound and avoidance of poles. -/
theorem exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow
    (S : Finset Primes) (_hPic : Subsingleton (CommRing.Pic ((S : Set Primes).integer F)))
    (χ : PontryaginDual C𝔽) (_hχ : ideleClassNormTwist χ 0 ∈ unramifiedOutside F S)
    {δ : ℝ} (_hδ : 0 < δ) :
    ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧ Monotone T ∧
      (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k < 0 → T k ≤ 0) ∧
      Tendsto (fun k ↦ |T k|) (comap (abs : ℤ → ℤ) atTop) atTop ∧
      ∀ k : ℤ, ∀ σ ∈ Icc (-δ) (1 + δ),
        c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((σ : ℂ) + (T k : ℂ) * Complex.I)‖ := by
  classical
  let q (v : S) : ℝ := (v.val.asIdeal.absNorm : ℝ)
  have hq1 (v : S) : 1 < q v := by
    dsimp only [q]; exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  let a (v : S) : ℂ := if (ideleClassNormTwist χ 0).IsUnramifiedAt v.val then
    (ideleClassNormTwist χ 0).localValue v.val else 0
  let ω (v : S) := -Real.log (q v)
  let phase (r : ℝ) (v : S) := Circle.exp (r * ω v)
  have hω (v : S) : ω v ≠ 0 := neg_ne_zero.mpr (Real.log_pos (hq1 v)).ne'
  have hpow (σ r : ℝ) (v : S) :
      (v.val.asIdeal.absNorm : ℂ) ^ (-((σ : ℂ) + (r : ℂ) * Complex.I)) =
        (phase r v : ℂ) * ((q v ^ (-σ) : ℝ) : ℂ) := by
    have hq : (v.val.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val)).ne'
    rw [Complex.cpow_def_of_ne_zero hq, ← Complex.natCast_log, Circle.coe_exp,
      Real.rpow_def_of_pos (zero_lt_one.trans (hq1 v)), Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    dsimp [ω, q]
    push_cast
    ring
  have hfac (σ r t : ℝ) (v : S) :
      (finiteHeckeEulerFactor χ v.val ((σ : ℂ) + ((r + t : ℝ) : ℂ) * Complex.I))⁻¹ =
        1 - a v * (phase r v : ℂ) * (Circle.exp (t * ω v) : ℂ) * ((q v ^ (-σ) : ℝ) : ℂ) := by
    by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v.val
    · rw [finiteHeckeEulerFactor, ite_eq_left hv, inv_inv, hpow]
      simp only [a, ite_eq_left hv, phase, add_mul, Circle.exp_add, Circle.coe_mul]
      ring
    · rw [finiteHeckeEulerFactor, ite_eq_right hv]
      simp [a, hv]
  obtain ⟨c, hc, hshift⟩ :=
    exists_heights_reciprocalPartialHeckeEulerProduct_strip_boundedBelow_phaseShift
      a ω hω (fun v ↦ q v ^ (-(1 + δ))) (fun v ↦ q v ^ δ)
      (fun v ↦ Real.rpow_pos_of_pos (zero_lt_one.trans (hq1 v)) _)
  choose t ht hbound using fun k : ℤ ↦ hshift (phase k)
  let T (k : ℤ) : ℝ := k + t k
  have hI (k : ℤ) : T k ∈ Ioo (k : ℝ) ((k : ℝ) + 1) :=
    ⟨lt_add_of_pos_right _ (ht k).1, add_lt_add_right (ht k).2 _⟩
  refine ⟨c, T, hc, ?_, ?_, ?_, ?_, fun k σ hσ ↦ ?_⟩
  · apply monotone_int_of_le_succ
    intro k
    exact ((hI k).2.trans (by simpa only [Int.cast_add, Int.cast_one] using (hI (k + 1)).1)).le
  · intro k hk
    exact (show 0 ≤ (k : ℝ) by exact_mod_cast hk).trans (hI k).1.le
  · intro k hk
    have h : (k : ℝ) + 1 ≤ 0 := by exact_mod_cast (show k + 1 ≤ 0 by omega)
    exact (hI k).2.le.trans h
  · have hlim : Tendsto (fun k : ℤ ↦ ((|k| : ℤ) : ℝ)) (comap (abs : ℤ → ℤ) atTop) atTop :=
      tendsto_intCast_atTop_atTop.comp tendsto_comap
    refine tendsto_atTop_mono (fun k ↦ ?_) (tendsto_atTop_add_const_right _ (-1) hlim)
    rw [Int.cast_abs]
    have h := abs_sub_abs_le_abs_sub (k : ℝ) (T k)
    rw [abs_of_nonpos (sub_nonpos.mpr (hI k).1.le)] at h
    linarith [(hI k).2]
  · have hr (v : S) : q v ^ (-σ) ∈ Icc (q v ^ (-(1 + δ))) (q v ^ δ) :=
      ⟨Real.rpow_le_rpow_of_exponent_le (hq1 v).le (by linarith [hσ.2]),
        Real.rpow_le_rpow_of_exponent_le (hq1 v).le (by linarith [hσ.1])⟩
    have h := hbound k (fun v ↦ q v ^ (-σ)) hr
    rw [reciprocalPartialHeckeEulerProduct, ← Finset.prod_coe_sort]
    simpa only [T, hfac] using h


-- TODO(paper-gap): The proof on p. 315 uses a different reflection for each place,
-- and positive symmetric upper density alone does not guarantee visits on both tails.
-- The zero list on p. 313 also omits the shift by -itᵥ in (7.1.1.1).

section SLocal

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "twistₛ" => quasiCharacterNormTwist (G := Jₛ) mₛ
  (IsProperMap.continuous (isProperMap_sIdeleQuotientNorm F S))
local notation "zetaGerm(" f "," c ")" => fun z ↦ sLocalIdelicZFunction f (twistₛ c z)

-- TODO(paper-gap): The preamble's a₋ₙ ≠ 0 condition at N = 0 fails at holomorphic zeros.

/-- Paper: Definition 7.1.2.1, p. 316.
The polar S-multiplicity is the order of the pole of the continued zeta function at `c`.
It is zero at every point without a pole, including when the germ vanishes identically. -/
def sLocalPolarMultiplicity (f : ℬₛ) (c : QuasiCharacter Jₛ) : ℕ :=
  (-(meromorphicOrderAt (zetaGerm(f, c)) 0).untop₀).toNat

/-- Paper: Definition 7.1.2.1, p. 316.
The multiplicity vanishes exactly at the quasi-characters with nonnegative meromorphic order. -/
theorem sLocalPolarMultiplicity_eq_zero_iff (f : ℬₛ) (c : QuasiCharacter Jₛ) :
    sLocalPolarMultiplicity f c = 0 ↔
      0 ≤ meromorphicOrderAt (zetaGerm(f, c)) 0 := by
  unfold sLocalPolarMultiplicity
  generalize meromorphicOrderAt (zetaGerm(f, c)) 0 = o
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe n => simp

/-- Paper: Definition 7.1.2.1, p. 316.
The integer-indexed Laurent coefficient is computed in the norm-twist coordinate centered
at `c`, by taking the residue after shifting the desired power to exponent minus one. -/
def sLocalZLaurentCoeff (f : ℬₛ) (c : QuasiCharacter Jₛ) (m : ℤ) : ℂ :=
  complexResidue (fun z ↦ sLocalIdelicZFunction f (twistₛ c z) / z ^ (m + 1)) 0

/-- Paper: Definition 7.1.2.1, p. 316.
The coefficient sequence gives a Laurent expansion of the centered zeta germ, with partial
sums converging uniformly on compact subsets of a punctured disc. -/
theorem sLocalZLaurentCoeff_hasLaurentSeries (f : ℬₛ) (c : QuasiCharacter Jₛ) :
    HasVectorLaurentSeriesAt (zetaGerm(f, c)) 0 (sLocalZLaurentCoeff f c) := by sorry

-- TODO(paper-gap): In Lemma 7.1.2.2(1), the complex-place shift has the wrong sign.
-- The uniqueness of the contributing place stated on p. 317 fails when poles coincide.

/-- Paper: Lemma 7.1.2.2, p. 316.
The poles of the S-local correcting factor are the union of the two archimedean families
and the periodic lattices at unramified finite places.
Deviation: As in §3.3, the complex-place abscissae start at minus half the absolute angular
weight. The union allows more than one place to contribute to the same pole. -/
theorem sLocalRhoFactor_poles_iff (χ : PontryaginDual Jₛ) (s : ℂ) :
    let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    let c := twistₛ χ₀ 0
    meromorphicOrderAt (fun z ↦ sLocalRhoFactor (twistₛ χ₀ z)) s < 0 ↔
      (∃ (w : InfinitePlace F) (hw : w.IsReal) (n : ℕ),
        let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c)).exists.choose
        s = -p.1 - ((2 * n + p.2.val : ℕ) : ℂ)) ∨
      (∃ (w : InfinitePlace F) (hw : w.IsComplex) (n : ℕ),
        let p := (complexLocalEulerParameters w hw (sLocalInfiniteRestriction w c)).exists.choose
        s = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)) ∨
      (∃ (v : S) (m : ℤ) (t : ℝ),
        let period := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
        t ∈ Ico 0 period ∧
          (∀ x : (v.val.adicCompletion F)ˣ,
            sLocalFiniteRestriction v c x =
              ((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) ∧
          s = (((m : ℝ) * period - t : ℝ) : ℂ) * Complex.I) := by sorry

open Classical in
/-- Paper: Lemma 7.1.2.2, p. 317.
At a pole of the correcting factor, its order counts all the places where the
restricted local Tate factor has a pole.
Deviation: Each local pole is simple. The count includes coincident poles. -/
theorem sLocalRhoFactor_orderAt_pole (χ : PontryaginDual Jₛ) (s : ℂ) :
    let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ
    let c := fun z : ℂ ↦ twistₛ χ₀ z
    let ρ := fun z : ℂ ↦ sLocalRhoFactor (c z)
    let arch := Finset.univ.filter (fun w : InfinitePlace F ↦
      meromorphicOrderAt (fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (c z))) s < 0)
    let fin := Finset.univ.filter (fun v : S ↦
      meromorphicOrderAt (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (c z))) s < 0)
    meromorphicOrderAt ρ s < 0 →
      meromorphicOrderAt ρ s = ((-((arch.card + fin.card : ℕ) : ℤ) : ℤ) : WithTop ℤ) := by sorry

end SLocal

-- TODO(paper-gap): Theorem 7.1.2.3 omits the real Gaussian's constant term, uses
-- a_{k-1} in place of a_{-k}, and counts coincident poles once per contributing place.
-- The strict cutoff can omit higher-order poles on Re(s) = -A, where the claimed
-- L¹ remainder constant is undefined. The bounded-set version has the same defects.
-- TODO(paper-gap): Footnote 1, p. 321, flags the missing growth control on the
-- horizontal heights for the appeal to Theorem B.3.2.1.

section Counterexample

local notation "Jℚ" => SIdeleQuotient ℚ ∅
local notation "Jℚ₁" => MonoidHom.ker (sIdeleQuotientNorm ℚ ∅)
local notation "μℚ₁" => sLocalNormOneQuotientMeasure ℚ ∅

local instance instMeasurableNormOneRatSec1a : MeasurableSpace Jℚ₁ := borel _
local instance instHaarNormOneRatSec1a : Measure.IsHaarMeasure μℚ₁ :=
  (sLocalNormOneQuotientMeasure_normProduct (F := ℚ) (S := ∅)).1

/-- At the rational archimedean stage, the real Gaussian evaluated on an idele
depends only on its idelic norm. -/
private theorem sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_gaussian :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      ∀ g : (SAdeleRing ℚ ∅)ˣ, f (Multiplicative.ofAdd g.val) =
        (Real.exp (-(((sIdeleNorm ℚ ∅ g).val : ℝ) ^ 2)) : ℂ) := by
  let w := Rat.infinitePlace
  let j := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let e : SAdeleRing ℚ ∅ ≃ₜ ℝ := ((Homeomorph.prodUnique _ _).trans
    (Homeomorph.piUnique fun v : InfinitePlace ℚ ↦ v.Completion)).trans j.toHomeomorph
  let a : SAdeleRing ℚ ∅ ≃+ ℝ :=
    { e.toEquiv with
      map_add' := fun x y ↦
        map_add (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace)
          (x.1 w) (y.1 w) }
  let E : Multiplicative (SAdeleRing ℚ ∅) ≃ₜ* Multiplicative ℝ :=
    { a.toMultiplicative with
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  have : T2Space (Multiplicative (SAdeleRing ℚ ∅)) := e.isEmbedding.t2Space
  have : LocallyCompactSpace (Multiplicative (SAdeleRing ℚ ∅)) :=
    e.isOpenEmbedding.locallyCompactSpace
  have : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  have : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  obtain ⟨b, hb⟩ := exists_gaussian_schwartz (E := ℝ) 1 zero_lt_one
  obtain ⟨T, hT⟩ := realSchwartzBruhat_equiv
  refine ⟨⟨(T b).val ∘ E, schwartzBruhat_mem_comp_equiv E (T b).property⟩, fun g ↦ ?_⟩
  change T b (Multiplicative.ofAdd (j (g.val.1 w))) = _
  rw [hT, hb, neg_one_mul, j.isometry.norm_map_of_map_zero (map_zero
    (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace))]
  have hn : ((sIdeleNorm ℚ ∅ g).val : ℝ) = ‖g.val.1 w‖ := by
    rw [sIdeleNorm, Finset.univ_eq_empty (α := (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))),
      Finset.prod_empty, mul_one, Fintype.prod_subsingleton _ w,
      Rat.isReal_infinitePlace.mult_eq_one, pow_one]
    rfl
  rw [hn]

/-- Both rational unit translates have the same Gaussian value. Averaging the
result over norm-one classes multiplies it by their total Haar mass. -/
private theorem sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_eval
    (f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)))
    (hf : ∀ g : (SAdeleRing ℚ ∅)ˣ, f (Multiplicative.ofAdd g.val) =
      (Real.exp (-(((sIdeleNorm ℚ ∅ g).val : ℝ) ^ 2)) : ℂ)) (g : Jℚ) :
    sLocalHomogeneousAdelicTheta ℚ ∅ μℚ₁ (1 : PontryaginDual Jℚ₁) f g =
      ((μℚ₁).real univ : ℂ) * (2 * (Real.exp (-(((sIdeleQuotientNorm ℚ ∅ g).val : ℝ) ^ 2)) : ℂ)) := by
  let φ (t : ℝ≥0ˣ) : ℂ := Real.exp (-((t.val : ℝ) ^ 2))
  have hclass (x : Jℚ) : sLocalAdelicThetaOnClasses ℚ ∅ f x = 2 * φ (sIdeleQuotientNorm ℚ ∅ x) := by
    refine Quotient.inductionOn x fun y ↦ ?_
    refine (sLocalAdelicThetaOnClasses_mk ℚ ∅ f y).trans ((sLocalAdelicTheta_apply ℚ ∅ f y).trans ?_)
    let U := (((∅ : Finset (HeightOneSpectrum (𝓞 ℚ))) : Set (HeightOneSpectrum (𝓞 ℚ))).integer ℚ)ˣ
    have hcard : Nat.card U = 2 := by
      dsimp only [U]
      rw [Finset.coe_empty, integer_empty]
      let e := Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)
      let units := Units.mapEquiv (e.toRingEquiv.trans Rat.ringOfIntegersEquiv).toMulEquiv
      rw [Nat.card_congr units.toEquiv, Nat.card_eq_fintype_card, Fintype.card_units_int]
    calc
      _ = ∑' _ : U, φ (sIdeleNorm ℚ ∅ y) := by
        apply tsum_congr
        intro u
        let d := Units.map
          ((adeleProjection ℚ ∅).comp (integralAdelesOutside ℚ ∅).subtype).toMonoidHom
          (Units.map (integralAdeleDiagonal ℚ ∅).toMonoidHom u)
        have hu : sIdeleNorm ℚ ∅ d = 1 := (sIdeleNorm_spec ℚ ∅).2 ⟨u, rfl⟩
        exact (hf (d * y)).trans (congrArg φ (by rw [map_mul, hu, one_mul]))
      _ = _ := by
        change (∑' _ : U, φ (sIdeleNorm ℚ ∅ y)) = 2 * φ (sIdeleNorm ℚ ∅ y)
        rw [tsum_const, hcard, nsmul_eq_mul, Nat.cast_ofNat]
  change (∫ h : Jℚ₁, sLocalAdelicThetaOnClasses ℚ ∅ f (g * h.val) *
    ((1 : PontryaginDual Jℚ₁) h : ℂ) ∂μℚ₁) = _
  have hker (h : Jℚ₁) : sIdeleQuotientNorm ℚ ∅ h.val = 1 := h.property
  simp only [hclass, map_mul, hker, mul_one,
    PontryaginDual.one_apply, Circle.coe_one, integral_const, Complex.real_smul, φ]

/-- A radial Gaussian profile with nonzero mass has a nonzero limit along the
norm, whereas a square-root bound would force its limit to be zero. -/
private theorem sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_limit
    {X : Type*} (r : X → ℝ) (hr : Ioi 0 ⊆ range r) (c : ℂ) (hc : c ≠ 0)
    (θ : X → ℂ) (hθ : ∀ x, θ x = c * (2 * (Real.exp (-(r x ^ 2)) : ℂ))) :
    ¬ Asymptotics.IsBigO (comap r (𝓝[>] (0 : ℝ))) θ (fun x ↦ r x ^ (1 / 2 : ℝ)) := by
  let l := comap r (𝓝[>] (0 : ℝ))
  have : l.NeBot := (inferInstance : (𝓝[>] (0 : ℝ)).NeBot).comap_of_range_mem
    (mem_of_superset self_mem_nhdsWithin hr)
  have hr₀ : Tendsto r l (𝓝 0) := tendsto_comap.mono_right nhdsWithin_le_nhds
  have hroot : Tendsto (fun x ↦ r x ^ (1 / 2 : ℝ)) l (𝓝 0) := by
    simpa only [Function.comp_def, ← Real.sqrt_eq_rpow, Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp hr₀
  have hlim : Tendsto θ l (𝓝 (c * 2)) := by
    rw [funext hθ]
    have h : Continuous (fun t : ℝ ↦ c * (2 * (Real.exp (-(t ^ 2)) : ℂ))) := by fun_prop
    simpa [Function.comp_def] using (h.tendsto 0).comp hr₀
  exact fun hO ↦ (mul_ne_zero hc (by norm_num)) (tendsto_nhds_unique hlim (hO.trans_tendsto hroot))

/-- Paper: Theorem 7.1.2.3, p. 317.
Over the rationals with only the real place and the trivial character, the square-root
bound at norm zero fails for some test function. The real Gaussian gives a witness.
Deviation: States a counterexample to (7.1.2.3) at `A = 1/2`, where both printed sums are empty. -/
theorem sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing ℚ ∅)),
      let normℝ (g : Jℚ) := ((sIdeleQuotientNorm ℚ ∅ g : ℝ≥0) : ℝ)
      ¬ Asymptotics.IsBigO (comap normℝ (𝓝[>] (0 : ℝ)))
        (sLocalHomogeneousAdelicTheta ℚ ∅ μℚ₁ (1 : PontryaginDual Jℚ₁) f : Jℚ → ℂ)
        (fun g ↦ (normℝ g) ^ (1 / 2 : ℝ)) := by
  let r (g : Jℚ) : ℝ := (sIdeleQuotientNorm ℚ ∅ g).val
  have hr : Ioi 0 ⊆ range r := by
    intro t ht
    obtain ⟨s, hs⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
    let u : ℝ≥0ˣ := Units.mk0 ⟨t, ht.le⟩ (ne_of_gt (show (0 : ℝ≥0) < ⟨t, ht.le⟩ from ht))
    exact ⟨s u, congrArg (fun v : ℝ≥0ˣ ↦ (v.val : ℝ)) (hs u)⟩
  have : CompactSpace Jℚ₁ := isCompact_iff_compactSpace.mp
    ((isProperMap_sIdeleQuotientNorm ℚ ∅).isCompact_preimage (isCompact_singleton (x := 1)))
  have : IsFiniteMeasure μℚ₁ := CompactSpace.isFiniteMeasure (μ := μℚ₁)
  let c : ℂ := (μℚ₁).real univ
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μℚ₁)).ne'
  refine sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_gaussian.elim fun f hf ↦ ?_
  let θ : Jℚ → ℂ := sLocalHomogeneousAdelicTheta ℚ ∅ μℚ₁ (1 : PontryaginDual Jℚ₁) f
  have he : ∀ g, θ g = c * (2 * (Real.exp (-(r g ^ 2)) : ℂ)) :=
    sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_eval f hf
  exact ⟨f, sLocalHomogeneousAdelicTheta_rat_not_isBigO_sqrt_limit r hr c hc θ he⟩

end Counterexample

-- TODO(paper-gap): Remark 7.1.2.4 drops the imaginary-unit conversion in the phase
-- and reverses the phase sign in the displayed list for the saturated product.

/-- The reciprocal of `1 - b exp(-L z)`, with `exp(-L) ≠ 1`, is meromorphic with a nonpositive
integer order, which is negative exactly at the zeros of `1 - b exp(-L z)`. -/
private theorem finiteHeckeEulerFactor_poles_iff_exp
    (b L : ℂ) (hL : Complex.exp (-L) ≠ 1) (s : ℂ) :
    MeromorphicAt (fun z ↦ (1 - b * Complex.exp (-(L * z)))⁻¹) s ∧ ∃ k : ℤ, k ≤ 0 ∧
      meromorphicOrderAt (fun z ↦ (1 - b * Complex.exp (-(L * z)))⁻¹) s = k ∧
      (k < 0 ↔ 1 - b * Complex.exp (-(L * s)) = 0) := by
  let g : ℂ → ℂ := fun z ↦ 1 - b * Complex.exp (-(L * z))
  have hg : ∀ z, AnalyticAt ℂ g z := fun z ↦ by fun_prop
  have hne : analyticOrderAt g s ≠ ⊤ := by
    intro htop
    have h0 := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero s hg).mp htop
    have e0 := congrFun h0 0
    have e1 := congrFun h0 1
    simp only [g, Pi.zero_apply, mul_zero, neg_zero, Complex.exp_zero, mul_one,
      sub_eq_zero] at e0 e1
    subst e0
    exact hL (by simpa using e1.symm)
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hne
  refine ⟨(hg s).meromorphicAt.inv, -(k : ℤ), by omega, ?_, ?_⟩
  · change meromorphicOrderAt g⁻¹ s = _
    rw [meromorphicOrderAt_inv, (hg s).meromorphicOrderAt_eq, ← hk]
    simp
  · have : (-(k : ℤ) < 0) ↔ analyticOrderAt g s ≠ 0 := by
      rw [← hk]; simp; omega
    rw [this, analyticOrderAt_ne_zero]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨hg s, h⟩⟩

/-- Every finite Hecke Euler factor is meromorphic with a nonpositive integer order, negative
exactly at the zeros of the Euler polynomial at an unramified place. -/
private theorem finiteHeckeEulerFactor_poles_iff_order
    (χ : PontryaginDual C𝔽) (v : Primes) (s : ℂ) :
    MeromorphicAt (finiteHeckeEulerFactor χ v) s ∧ ∃ k : ℤ, k ≤ 0 ∧
      meromorphicOrderAt (finiteHeckeEulerFactor χ v) s = k ∧
      (k < 0 ↔ (ideleClassNormTwist χ 0).IsUnramifiedAt v ∧
        1 - (ideleClassNormTwist χ 0).localValue v * (v.asIdeal.absNorm : ℂ) ^ (-s) = 0) := by
  classical
  by_cases hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · have hN0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    let L := Complex.log (v.asIdeal.absNorm : ℂ)
    have hpow (z : ℂ) : (v.asIdeal.absNorm : ℂ) ^ (-z) = Complex.exp (-(L * z)) := by
      rw [Complex.cpow_def_of_ne_zero hN0]
      congr 1
      ring
    have hL : Complex.exp (-L) ≠ 1 := by
      rw [Complex.exp_neg, Complex.exp_log hN0]
      intro h
      have := inv_eq_one.mp h
      have h2 := HeightOneSpectrum.one_lt_absNorm v
      have : (v.asIdeal.absNorm : ℕ) = 1 := by exact_mod_cast this
      omega
    have hfun : finiteHeckeEulerFactor χ v = fun z ↦
        (1 - (ideleClassNormTwist χ 0).localValue v * Complex.exp (-(L * z)))⁻¹ := by
      funext z
      rw [finiteHeckeEulerFactor, ite_eq_left hv, hpow]
    obtain ⟨hm, k, hk, ho, hiff⟩ :=
      finiteHeckeEulerFactor_poles_iff_exp ((ideleClassNormTwist χ 0).localValue v) L hL s
    rw [hfun]
    exact ⟨hm, k, hk, ho, by rw [hiff, hpow]; simp [hv]⟩
  · have hfun : finiteHeckeEulerFactor χ v = fun _ ↦ 1 := by
      funext z
      rw [finiteHeckeEulerFactor, ite_eq_right hv]
    rw [hfun]
    refine ⟨MeromorphicAt.const _ _, 0, le_rfl, ?_, by simp [hv]⟩
    rw [meromorphicOrderAt_const]
    simp

/-- Paper: Remark 7.1.2.4, p. 318.
At an unramified finite place the poles of the Hecke Euler factor are equally spaced on
the imaginary axis. The phase is specified by the value at a local uniformizer.
Deviation: Uses the global character after extension and the phase convention
`χ(πᵥ) = qᵥ^(-it)` of Lemma 7.1.2.2. The period lattice is a subgroup of `ℂ`. -/
theorem finiteHeckeEulerFactor_poles_iff (χ : PontryaginDual C𝔽) (v : Primes)
    (_hv : (ideleClassNormTwist χ 0).IsUnramifiedAt v) (t : ℝ)
    (_ht : (ideleClassNormTwist χ 0).localValue v =
      (v.asIdeal.absNorm : ℂ) ^ (-(t : ℂ) * Complex.I)) (s : ℂ) :
    meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0 ↔
      ∃ m : ℤ, s = (((m : ℝ) * (2 * Real.pi / Real.log (v.asIdeal.absNorm : ℝ)) - t : ℝ) : ℂ) *
        Complex.I := by
  obtain ⟨-, k, -, ho, hiff⟩ := finiteHeckeEulerFactor_poles_iff_order χ v s
  have hq : 1 < (v.asIdeal.absNorm : ℝ) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hℓ : 0 < Real.log (v.asIdeal.absNorm : ℝ) := Real.log_pos hq
  have hN0 : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
  set ℓ := Real.log (v.asIdeal.absNorm : ℝ) with hℓdef
  have hlog : Complex.log (v.asIdeal.absNorm : ℂ) = (ℓ : ℂ) := by
    rw [hℓdef, Complex.natCast_log]
  rw [ho, show ((k : WithTop ℤ) < 0 ↔ k < 0) from by exact_mod_cast Iff.rfl, hiff, _ht,
    and_iff_right _hv, sub_eq_zero, ← Complex.cpow_add _ _ hN0, eq_comm,
    Complex.cpow_def_of_ne_zero hN0, hlog, Complex.exp_eq_one_iff]
  have hℓ0 : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨-n, ?_⟩
    push_cast
    field_simp
    linear_combination -hn
  · rintro ⟨m, hm⟩
    refine ⟨-m, ?_⟩
    rw [hm]
    push_cast
    field_simp
    ring

open Classical in
/-- Paper: Remark 7.1.2.4, p. 318.
At a rational prime with all places above it in `S`, the poles of the product are precisely
the poles of the individual local Euler factors at those places.
Deviation: The factors at ramified places are one, as in §3.2.1. -/
theorem finiteHeckeEulerProduct_poles_iff (χ : PontryaginDual C𝔽) (S : Finset Primes)
    (p : HeightOneSpectrum (𝓞 ℚ)) (_hsat : ∀ v : Primes, v.under (𝓞 ℚ) = p → v ∈ S)
    (s : ℂ) :
    let Sₚ := S.filter (fun v ↦ v.under (𝓞 ℚ) = p)
    meromorphicOrderAt (fun z ↦ ∏ v ∈ Sₚ, finiteHeckeEulerFactor χ v z) s < 0 ↔
      ∃ v ∈ Sₚ, meromorphicOrderAt (finiteHeckeEulerFactor χ v) s < 0 := by
  intro Sₚ
  choose hm k hk ho _ using fun v ↦ finiteHeckeEulerFactor_poles_iff_order χ v s
  have hfun : (fun z ↦ ∏ v ∈ Sₚ, finiteHeckeEulerFactor χ v z) =
      ∏ v ∈ Sₚ, finiteHeckeEulerFactor χ v := by
    funext z
    simp [Finset.prod_apply]
  rw [hfun, meromorphicOrderAt_prod (fun v _ ↦ hm v)]
  simp only [ho]
  norm_cast
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have : ∑ v ∈ Sₚ, k v = 0 :=
      Finset.sum_eq_zero fun v hv ↦ le_antisymm (hk v) (hne v hv)
    omega
  · rintro ⟨v, hv, hlt⟩
    have h := Finset.single_le_sum (f := fun w ↦ -k w) (fun w _ ↦ neg_nonneg.mpr (hk w)) hv
    rw [Finset.sum_neg_distrib] at h
    omega

-- TODO(prerequisite): The induced Euler-factor identity in Remark 7.1.2.4 needs
-- global Weil groups and their induction and local L-factor constructions.
-- TODO(later): needs §7.2.1 for continuity of the Laurent coefficient operators and
-- their descent to the coinvariants (Theorem 7.2.1.1(1)–(2)).
-- TODO(paper-gap): The eigendistribution interpretation on pp. 319–321 fails for
-- general Laurent coefficients. For the real Gaussian at the trivial character,
-- scaling f(x) to f(x/r) adds log(r) * a₋₁ to a₀. At a multiple pole, lower polar
-- coefficients also mix under dilation. The leading polar coefficient transforms by
-- the character, and all coefficients have the character law on norm-one elements.
-- On p. 321 the lattice index is also used as a Laurent index. At index zero a
-- test function compactly supported in the S-ideles can have nonzero a₀.
-- TODO(paper-gap): The contour formula on p. 323 needs positive orientation and
-- exclusion of the other poles, as in Lemma C.5.3.2. Compare scalar normal forms
-- away from the distributional poles, as in infiniteLocalIdelicZFunction_distribution.

end RiemannMasullo
