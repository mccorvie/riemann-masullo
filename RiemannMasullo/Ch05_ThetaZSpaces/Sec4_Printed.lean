module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a

/-!
# Chapter 5.4: statements that are false as printed

The printed claims are propositions, with separate statements of their negations.
The corresponding results are in `Sec4.lean` and the errata are recorded in `ERRATA.md`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

local notation "Test(" A ")" => SchwartzBruhat (Multiplicative (A))
local notation "normℂ(" t ")" => (((t : ℝ≥0ˣ).val : ℝ) : ℂ)
local notation "restrict₁(" F ", " S ", " χ ")" => ((χ : PontryaginDual (SIdeleQuotient F S)).comp
  (⟨(sIdeleQuotientNorm F S).ker.subtype, continuous_subtype_val⟩ :
    (sIdeleQuotientNorm F S).ker →ₜ* SIdeleQuotient F S))
local notation "ρₛ(" field ", " places ", " χ ", " s ")" =>
  sLocalRhoFactor (F := field) (S := places)
    (quasiCharacterNormTwist (sIdeleQuotientNorm field places)
      (isProperMap_sIdeleQuotientNorm field places).continuous
      ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ)) (s))

local notation "rightInterval" => Ioi (0 : ℝ)
local notation "leftInterval" => Iio (1 : ℝ)
local notation "rightHalf" => Complex.re ⁻¹' rightInterval
local notation "leftHalf" => Complex.re ⁻¹' leftInterval
local notation "overlap" => Complex.re ⁻¹' Ioo (0 : ℝ) 1
local notation "B⁺" => SchwartzBergman rightInterval
local notation "B⁻" => SchwartzBergman leftInterval
local notation "Eω(" field ", " places ", " I ", " ω ")" =>
  ↥(sLocalDecayIsotype (F := field) (S := places) (I) (ω))

/-- Paper: Theorem 5.4.1.1(1), p. 266.
As printed: the Fourier coordinate of the zeta pair is equivariant with multiplier
`t^(1-s) · ω̄(k)` for translation by the class `τ(t)k`. This records the second
coordinate on the common strip where the printed range `Re s > 0` meets the Fourier
coordinate’s domain `Re s < 1`. Character inversion expresses conjugation.
Remark 5.4.1.2 and Proposition 5.4.1.4 repeat this multiplier. The repaired declarations are
`sLocalZetaPair_translate` and `exists_sLocalZetaPair_action`. See ERRATA F60. -/
def Printed.sLocalZetaPair_translate : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let A := SAdeleRing F S
    let J := SIdeleQuotient F S
    let m := sIdeleQuotientNorm F S
    ∀ (τ : ℝ≥0ˣ →ₜ* J) (hτ : RightInverse τ m) (ω : PontryaginDual m.ker),
      let χ := (existsUnique_sLocalNormSectionCharacter (F := F) (S := S) τ hτ ω).exists.choose
      ∀ (u : Aˣ) (t : ℝ≥0ˣ) (k : m.ker) (f : Test(A)),
        (QuotientGroup.mk u : J) = τ t * k.val →
        let U := sLocalZetaPair (F := F) (S := S) χ
        let p := U (Submodule.Quotient.mk f)
        let q := U (Submodule.Quotient.mk (schwartzBruhatUnitTranslate (R := A) u f))
        EqOn q.2.val (fun s ↦ normℂ(t) ^ (1 - s) * ((ω⁻¹) k : ℂ) * p.2.val s) overlap

/-- Paper: Theorem 5.4.1.1(1), p. 266.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and `ω = 1`.
Use `f(x) = exp(−πx²)` and the positive real idele `u = 2`. At `s = 1/4` the Fourier
coordinate is nonzero. Fourier scaling multiplies it by `2^(1/4)`, while the printed
rule multiplies it by `2^(3/4)`. The same mismatch applies to the polar-free case on p. 267
using a nonzero even nonnegative smooth bump supported in `1/2 < |x| < 3/2`, whose first
zeta coordinate is positive at `s = 1/4` and whose second is nonzero by the functional equation.
-/
theorem Printed.sLocalZetaPair_translate_false : ¬ Printed.sLocalZetaPair_translate := by
  sorry

/-- Paper: Remark 5.4.1.2, p. 266.
As printed: for a unitary lift of section frequency `x`, the reflected Fourier coordinate
in the lift's chart is the normalized Fourier coordinate evaluated at `s − ix`. This records
the second vertical translation in the remark. `existsUnique_sLocalZetaPair` gives the chart
values, and `sLocalCech_left_commutes` gives the unreflected transforms. See ERRATA F61. -/
def Printed.sLocalZetaPair_reflectedShift : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    let J := SIdeleQuotient F S
    ∀ (τ : ℝ≥0ˣ →ₜ* J) (hτ : RightInverse τ (sIdeleQuotientNorm F S))
      (χ : PontryaginDual J) (x : ℝ),
      (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = normℂ(t) ^ ((x : ℂ) * Complex.I)) →
      let χ₀ := (existsUnique_sLocalNormSectionCharacter (F := F) (S := S)
        τ hτ (restrict₁(F, S, χ))).exists.choose
      ∀ f : Test(SAdeleRing F S),
        let p := sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)
        let p₀ := sLocalZetaPair (F := F) (S := S) χ₀ (Submodule.Quotient.mk f)
        EqOn p.2.val (fun s ↦ p₀.2.val (s - (x : ℂ) * Complex.I)) leftHalf

/-- Paper: Remark 5.4.1.2, p. 266.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and the lift
`χ(g) = |g|^i` of the trivial norm-one character, so `x = 1`. For the self-dual Gaussian
`f(y) = exp(−πy²)`, write `Z(z) = π^(−z/2) Γ(z/2)` for its norm-twist zeta function.
At `s = 1 − ε + i` with `ε > 0`, the printed shift gives `Z(ε)` while the lifted
Fourier coordinate is `Z(ε − 2i)`. The former has a pole as `ε` tends to zero and the
latter has a finite limit.
-/
theorem Printed.sLocalZetaPair_reflectedShift_false : ¬ Printed.sLocalZetaPair_reflectedShift := by
  sorry

/-- Paper: Theorem 5.4.2.2(2), p. 276.
As printed: radial inversion with the factor `t⁻¹` and the norm-one coordinate fixed sends
every function of the conjugate isotype with weights in `1 − I` back into the same weighted
isotype. This records the source and membership assertion in the prose, which uses `1 − I`
at both ends. The displayed type uses `I` at both ends.
`existsUnique_sLocalCechRadialReflection` exchanges the two intervals. See ERRATA F62. -/
def Printed.sLocalCechRadialReflection : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S)
    (_hτ : RightInverse τ (sIdeleQuotientNorm F S)),
    let E := Eω(F, S, leftInterval, restrict₁(F, S, χ⁻¹))
    ∀ f : E, ∃ j : E,
      ∀ (t : ℝ≥0ˣ) (k : (sIdeleQuotientNorm F S).ker),
        j.val.val (τ t * k.val) = normℂ(t)⁻¹ * f.val.val (τ t⁻¹ * k.val)

/-- Paper: Theorem 5.4.2.2(2), p. 276.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and `χ = 1`.
Use `f(t) = exp(−1/t) / t`. For every `a < 1`, the twist `t^a f(t)` is Schwartz in
`log t`, since the power at infinity is `a−1 < 0` and the exponential dominates at zero.
The radial image is `exp(−t)`. Its weight-zero twist tends to `1` as `t` tends to zero,
and hence is outside the target with weights `a < 1`.
-/
theorem Printed.sLocalCechRadialReflection_false : ¬ Printed.sLocalCechRadialReflection := by
  sorry

/-- Paper: Theorem 5.4.2.2(3), p. 276.
As printed: reflection followed by multiplication by the local correcting factor gives
a linear topological isomorphism from the right half-plane Schwartz–Bergman space to the
reflected half-plane Schwartz–Bergman space. `sLocalCechBergman_exact` uses the product on the
overlap where it is holomorphic. See ERRATA F63. -/
def Printed.sLocalCechBergman_reflection : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)),
    ∃ J : B⁺ ≃L[ℂ] B⁻, ∀ p : B⁺,
      EqOn (J p).val (fun s ↦ ρₛ(F, S, χ, s) * p.val (1 - s)) leftHalf

private theorem Printed.sLocalCechBergman_reflection_false_pole :
    ∃ s₀ : ℂ, s₀.re < 1 ∧ meromorphicOrderAt
      (fun z ↦ ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
        (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), z)) s₀ < 0 := by
  obtain ⟨w, hw⟩ : ∃ w : InfinitePlace ℚ, w.IsReal := by
    classical
    have hcard := InfinitePlace.nrRealPlaces_eq_one_of_finrank_eq_one (K := ℚ)
      (Module.finrank_self ℚ)
    obtain ⟨⟨w, hw⟩⟩ := Fintype.card_pos_iff.mp (lt_of_lt_of_eq one_pos hcard.symm)
    exact ⟨w, hw⟩
  let χ₀ := (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
    (1 : PontryaginDual (SIdeleQuotient ℚ ∅))
  let c := quasiCharacterNormTwist (sIdeleQuotientNorm ℚ ∅)
    (isProperMap_sIdeleQuotientNorm ℚ ∅).continuous χ₀ 0
  let p := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w c)).exists.choose
  obtain ⟨n, hn⟩ := exists_nat_gt (-p.1.re)
  refine ⟨-p.1 - ((2 * n + p.2.val : ℕ) : ℂ), ?_, ?_⟩
  · have h2 : (0 : ℝ) ≤ (p.2.val : ℝ) := Nat.cast_nonneg _
    rw [Complex.sub_re, Complex.neg_re, Complex.natCast_re]
    push_cast
    linarith
  · exact (sLocalRhoFactor_poles_iff (F := ℚ) (S := ∅) 1 _).2 (Or.inl ⟨w, hw, n, rfl⟩)

open scoped Topology in
/-- Paper: Theorem 5.4.2.2(3), p. 276.
Take `F = ℚ`, `S` consisting of the real place, and `χ = 1`. Use `p(s) = exp(s²)` on
the right half-plane. The factor `π^((1−2s)/2) Γ(s/2) / Γ((1−s)/2)` has a simple pole
at zero, where `p(1) = e`. The product is unbounded as `s` approaches zero through
positive real arguments, so no holomorphic output exists on the reflected half-plane.
-/
theorem Printed.sLocalCechBergman_reflection_false : ¬ Printed.sLocalCechBergman_reflection := by
  intro h
  obtain ⟨s₀, hs₀, hpole⟩ := Printed.sLocalCechBergman_reflection_false_pole
  obtain ⟨J, hJ⟩ := h ℚ ∅ 1
  let p : B⁺ := ⟨(Complex.re ⁻¹' rightInterval).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)),
    gaussian_mem_schwartzBergmanSubmodule _ isOpen_Ioi⟩
  have hopen : IsOpen leftHalf := isOpen_Iio.preimage Complex.continuous_re
  have hmem : s₀ ∈ leftHalf := hs₀
  have hd : DifferentiableOn ℂ (J p).val leftHalf := (J p).2.2.1
  have han : AnalyticAt ℂ (fun z ↦ (J p).val z / Complex.exp ((1 - z) ^ 2)) s₀ :=
    ((hd.analyticAt (hopen.mem_nhds hmem)).div (by fun_prop) (Complex.exp_ne_zero _))
  have heq : (fun z ↦ ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), z)) =ᶠ[𝓝[≠] s₀]
      (fun z ↦ (J p).val z / Complex.exp ((1 - z) ^ 2)) := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    filter_upwards [hopen.mem_nhds hmem] with z hz
    have hz' : (1 - z) ∈ Complex.re ⁻¹' rightInterval := by
      change 0 < (1 - z).re
      have : z.re < 1 := hz
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hv : p.val (1 - z) = Complex.exp ((1 - z) ^ 2) :=
      indicator_of_mem hz' (fun z : ℂ ↦ Complex.exp (z ^ 2))
    have hJz := hJ p hz
    simp only at hJz
    rw [hJz, hv, mul_div_cancel_right₀ _ (Complex.exp_ne_zero _)]
  rw [meromorphicOrderAt_congr heq] at hpole
  exact absurd han.meromorphicOrderAt_nonneg (not_le.mpr hpole)

local notation "mellinAt(" τ ", " f ", " z ")" =>
  (∫ t : ℝ≥0ˣ, (f) ((τ) t) * normℂ(t) ^ (z) ∂positiveRealHaar)

/-- Paper: Theorem 5.4.2.2(4)–(5), (5.4.2.6), p. 276.
As printed: the right square commutes on every input of the two upper weighted isotypes.
On the overlap, the top-then-right path has second term `ρ(s) Q(s)` by the conjugation of
the multiplier by Mellin in (4). The down-then-right path has second term `ρ(s) Q(1−s)`
by (3). Here `Q` denotes the second Mellin transform. We read “similarly” in (1) as using
the printed shift for both transforms and express the two paths after Mellin evaluation,
with the first projection as in (5) on p. 277. See `existsUnique_sLocalCechDifference`
for the repaired difference and ERRATA F64.
-/
def Printed.sLocalCech_right_commutes : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))
    (χ : PontryaginDual (SIdeleQuotient F S)) (τ : ℝ≥0ˣ →ₜ* SIdeleQuotient F S)
    (_hτ : RightInverse τ (sIdeleQuotientNorm F S)) (x : ℝ),
    (∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = normℂ(t) ^ ((x : ℂ) * Complex.I)) →
    ∀ (M₁ : Eω(F, S, rightInterval, restrict₁(F, S, χ)) ≃L[ℂ] B⁺)
      (M₂ : Eω(F, S, rightInterval, restrict₁(F, S, χ⁻¹)) ≃L[ℂ] B⁺),
      (∀ f s, s ∈ rightHalf → (M₁ f).val s = mellinAt(τ, f.val.val, s + (x : ℂ) * Complex.I)) →
      (∀ f s, s ∈ rightHalf → (M₂ f).val s = mellinAt(τ, f.val.val, s + (x : ℂ) * Complex.I)) →
      ∀ f g, EqOn
        (fun s ↦ (M₁ f).val s - ρₛ(F, S, χ, s) * (M₂ g).val s)
        (fun s ↦ (M₁ f).val s - ρₛ(F, S, χ, s) * (M₂ g).val (1 - s)) overlap

open scoped Topology in
private theorem Printed.sLocalCech_right_commutes_false_ne_zero :
    ∃ r : ℝ, 0 < r ∧ r < 1 / 2 ∧
      ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
        (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), (r : ℂ)) ≠ 0 := by
  obtain ⟨s₀, -, hpole⟩ := Printed.sLocalCechBergman_reflection_false_pole
  have hmero : Meromorphic (fun z ↦ ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), z)) :=
    sLocalRhoFactor_meromorphic (F := ℚ) (S := ∅) 1
  have hon : MeromorphicOn (fun z ↦ ρₛ(ℚ, (∅ : Finset (HeightOneSpectrum (𝓞 ℚ))),
      (1 : PontryaginDual (SIdeleQuotient ℚ ∅)), z)) univ := fun z _ ↦ hmero z
  have htop := hon.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ s₀) (mem_univ (((1 / 4 : ℝ)) : ℂ)) (ne_top_of_lt hpole)
  have hev := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hmero _)).1 htop
  have ht : Filter.Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[≠] (1 / 4 : ℝ))
      (𝓝[≠] (((1 / 4 : ℝ)) : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact fun h ↦ hr (Complex.ofReal_injective h)
  have hI : ∀ᶠ r in 𝓝[≠] (1 / 4 : ℝ), r ∈ Ioo (0 : ℝ) (1 / 2) :=
    nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨r, hr1, hr2⟩ := ((ht.eventually hev).and hI).exists
  exact ⟨r, hr2.1, hr2.2, hr1⟩

private theorem Printed.sLocalCech_right_commutes_false_cancel (a b c d : ℂ) (hb : b ≠ 0)
    (h : a - b * c = a - b * d) : c = d :=
  mul_left_cancel₀ hb (sub_right_injective h)

private theorem Printed.sLocalCech_right_commutes_false_gaussian (r : ℝ) (hr0 : 0 < r)
    (hr1 : r < 1 / 2)
    (h : (Complex.re ⁻¹' Ioi (0 : ℝ)).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)) (r : ℂ) =
      (Complex.re ⁻¹' Ioi (0 : ℝ)).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)) (1 - (r : ℂ))) :
    False := by
  have h1 : (r : ℂ) ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
    change 0 < (r : ℂ).re
    rw [Complex.ofReal_re]
    exact hr0
  have h2 : (1 - (r : ℂ)) ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
    change 0 < (1 - (r : ℂ)).re
    rw [Complex.sub_re, Complex.one_re, Complex.ofReal_re]
    linarith
  rw [indicator_of_mem h1, indicator_of_mem h2] at h
  have h3 : Real.exp (r ^ 2) = Real.exp ((1 - r) ^ 2) := by
    exact_mod_cast h
  have := Real.exp_injective h3
  nlinarith

private theorem Printed.sLocalCech_right_commutes_false_transport {X : Type*} (v : X → ℂ → ℂ)
    {x y : X} (e : x = y) {a b : ℂ} (h : v x a = v x b) : v y a = v y b :=
  e ▸ h

/-- Paper: Theorem 5.4.2.2(4)–(5), (5.4.2.6), p. 276.
Take `F = ℚ`, `S` consisting of the real place, the positive-real section, and `χ = 1`,
so both Mellin transforms have shift zero. Set the first input to zero and the second
to the inverse Mellin image of `Q(s) = exp((s−2)²)` on the right half-plane.
At `s = 1/4`, `Q(1/4)` and `Q(3/4)` differ and `ρ(1/4) ≠ 0`. Both arguments are in
the overlap and the two paths give different values there.
-/
theorem Printed.sLocalCech_right_commutes_false : ¬ Printed.sLocalCech_right_commutes := by
  intro h
  obtain ⟨r, hr0, hr1, hρ⟩ := Printed.sLocalCech_right_commutes_false_ne_zero
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section (F := ℚ) (S := ∅)
  obtain ⟨M₁, hM₁, -⟩ := existsUnique_sLocalDecayMellin (F := ℚ) (S := ∅) τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi nonempty_Ioi
    (restrict₁(ℚ, ∅, (1 : PontryaginDual (SIdeleQuotient ℚ ∅)))) 0
  obtain ⟨M₂, hM₂, -⟩ := existsUnique_sLocalDecayMellin (F := ℚ) (S := ∅) τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi nonempty_Ioi
    (restrict₁(ℚ, ∅, (1 : PontryaginDual (SIdeleQuotient ℚ ∅))⁻¹)) 0
  let q : B⁺ := ⟨(Complex.re ⁻¹' rightInterval).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)),
    gaussian_mem_schwartzBergmanSubmodule _ isOpen_Ioi⟩
  have hmem : (r : ℂ) ∈ overlap := by
    change (r : ℂ).re ∈ Ioo (0 : ℝ) 1
    rw [Complex.ofReal_re]
    exact ⟨hr0, by linarith⟩
  have hx : ∀ t : ℝ≥0ˣ, ((1 : PontryaginDual (SIdeleQuotient ℚ ∅)) (τ t) : ℂ) =
      normℂ(t) ^ (((0 : ℝ) : ℂ) * Complex.I) := fun t ↦ by simp
  have h₁ : ∀ f s, s ∈ rightHalf →
      (M₁ f).val s = mellinAt(τ, f.val.val, s + ((0 : ℝ) : ℂ) * Complex.I) :=
    fun f s hs ↦ (hM₁ f s hs).2
  have h₂ : ∀ f s, s ∈ rightHalf →
      (M₂ f).val s = mellinAt(τ, f.val.val, s + ((0 : ℝ) : ℂ) * Complex.I) :=
    fun f s hs ↦ (hM₂ f s hs).2
  have key := h ℚ ∅ 1 τ hτ 0 hx M₁ M₂ h₁ h₂ (M₁.symm q) (M₂.symm q) hmem
  have key₁ := Printed.sLocalCech_right_commutes_false_cancel _ _ _ _ hρ key
  have e : M₂ (M₂.symm q) = q := M₂.apply_symm_apply q
  have key₂ : q.val (r : ℂ) = q.val (1 - (r : ℂ)) :=
    Printed.sLocalCech_right_commutes_false_transport (fun x : B⁺ ↦ x.val) e key₁
  exact Printed.sLocalCech_right_commutes_false_gaussian r hr0 hr1 key₂

end RiemannMasullo
