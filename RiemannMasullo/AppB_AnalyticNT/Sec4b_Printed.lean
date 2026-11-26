module

public import RiemannMasullo.AppB_AnalyticNT.Sec4b
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
import all RiemannMasullo.AppB_AnalyticNT.Sec4a
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings
import all RiemannMasullo.AppB_AnalyticNT.Sec2
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import RiemannMasullo.AppA_AlgebraicNT.Sec3

/-!
# Appendix B.4: statements that are false as printed

The propositions record the false parts of the printed claims. The repaired statements are
in `Sec4b.lean`, and `ERRATA.md` records the counterexamples. Nothing imports this file.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NNReal NumberField.AdeleRing SchwartzMap Topology

namespace RiemannMasullo

set_option quotPrecheck false

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "U[" F "]" => PontryaginDual C[F]
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v) : ℝ)
local notation "halfPlane" => (Complex.re ⁻¹' Ioi (1 : ℝ))
local notation "strip(" a ", " b ")" => (Complex.re ⁻¹' Ioo (a : ℝ) (b : ℝ))
local notation "atHeight" => (fun (σ t : ℝ) ↦ (σ : ℂ) + (t : ℂ) * Complex.I)
local notation "logMellin" => (fun (f : ℝ → ℂ) ↦ mellin (fun t ↦ f (Real.log t)))
local notation "twoPiI" => (2 * (Real.pi : ℂ) * Complex.I)
local notation "ord(" L ")" => MeromorphicOn.divisor L univ
local notation "isContinuation(" χ ", " L ")" =>
  (MeromorphicNFOn L univ ∧ ∀ s : halfPlane, L s = completedHeckeL χ s)
local notation "delta(" F ", " χ ")" =>
  (if (χ).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 then (1 : ℂ) else 0)

/-- Paper: Equation (B.4.2.2), p. 614. As printed: the pole contribution alone is
minus the Mellin values at zero and one when the character is trivial on norm-one
idele classes, and zero otherwise. See `hasSum_heckeAsymptoticResidue` and ERRATA F32. -/
def Printed.heckeAsymptoticResidue_poleTerm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (f : 𝓢(ℝ, ℂ)),
    ExponentialDecay f →
    ∀ (L : ℂ → ℂ), isContinuation(χ, L) →
      HasSum (fun ρ : {z : ℂ // ord(L) z < 0} ↦ (ord(L) ρ.val : ℂ) * logMellin f ρ.val)
        (-(delta(F, χ) * (logMellin f 0 + logMellin f 1)))

private theorem printed_shifted_poles :
    ∃ (χ : U[ℚ]) (L : ℂ → ℂ), isContinuation(χ, L) ∧
      χ.toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype = 1 ∧
      ∀ Φ : ℂ → ℂ, HasSum
        (fun ρ : {z : ℂ // ord(L) z < 0} ↦ (ord(L) ρ.val : ℂ) * Φ ρ.val)
        (-(Φ (-Complex.I) + Φ (1 - Complex.I))) := by
  let c := ideleClassNormTwist (1 : U[ℚ]) Complex.I
  have hn (g : C[ℚ]) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * ((((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ Complex.I)‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  let χ : U[ℚ] :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hn g)⟩
      map_one' := Subtype.ext c.map_one
      map_mul' := fun g h ↦ Subtype.ext (c.map_mul g h)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hk : χ.toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype = 1 := by
    ext1 g
    apply Subtype.ext
    change (1 : ℂ) * ((((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ Complex.I) = 1
    rw [MonoidHom.mem_ker.mp g.property]
    simp
  have hχ : ideleClassNormTwist χ 0 = c := by
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    simp
  obtain ⟨Z, hZ, hA⟩ := completedHeckeL_exists_continuation (1 : U[ℚ])
  let L (s : ℂ) := Z (s + Complex.I)
  have hL : MeromorphicNFOn L univ := fun _ _ ↦
    meromorphicNFAt_fun_comp_add_const_iff_meromorphicNFAt.mpr (hZ (mem_univ _))
  refine ⟨χ, L, ⟨hL, fun s ↦ ?_⟩, hk, fun Φ ↦ ?_⟩
  · rw [completedHeckeL_of_normTwist χ Complex.I (by simp) hχ]
    exact hA ⟨(s : ℂ) + Complex.I, by change 1 < (s : ℂ).re + Complex.I.re; simpa only [Complex.I_re, add_zero] using (show 1 < (s : ℂ).re from s.property)⟩
  · have ho (s : ℂ) : ord(L) s = (meromorphicOrderAt Z (s + Complex.I)).untop₀ := by
      rw [hL.meromorphicOn.divisor_apply (mem_univ s)]
      simp [L, meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt]
    have h₀ : ord(L) (-Complex.I) = -1 := by
      simp [ho, completedHeckeL_one_order_zero Z hZ hA]
    have h₁ : ord(L) (1 - Complex.I) = -1 := by
      simp [ho, completedHeckeL_one_order_one Z hZ hA]
    let a : {z : ℂ // ord(L) z < 0} := ⟨-Complex.I, by rw [h₀]; decide⟩
    let b : {z : ℂ // ord(L) z < 0} := ⟨1 - Complex.I, by rw [h₁]; decide⟩
    have hab : a ≠ b := by
      intro he
      have := congrArg (fun z : {z : ℂ // ord(L) z < 0} ↦ z.val.re) he
      norm_num [a, b] at this
    have hall (s : {z : ℂ // ord(L) z < 0}) : s = a ∨ s = b := by
      by_contra! hs
      have hmem : s.val + Complex.I ∉ ({0, 1} : Set ℂ) := by
        simp only [mem_insert_iff, mem_singleton_iff, not_or]
        exact ⟨fun he ↦ hs.1 (Subtype.ext (eq_neg_of_add_eq_zero_left he)),
          fun he ↦ hs.2 (Subtype.ext (eq_sub_of_add_eq he))⟩
      have hnn := (completedHeckeL_one_analyticOnNhd Z hZ hA _ hmem).meromorphicOrderAt_nonneg
      exact s.property.not_ge ((ho s.val) ▸ WithTop.untop₀_nonneg.mpr hnn)
    have hsum := (hasSum_ite_eq a (-Φ a.val)).add (hasSum_ite_eq b (-Φ b.val))
    rw [show -(Φ (-Complex.I) + Φ (1 - Complex.I)) = -Φ a.val + -Φ b.val by dsimp [a, b]; ring]
    refine hsum.congr_fun fun s ↦ ?_
    rcases hall s with rfl | rfl <;> simp [hab, hab.symm, a, b, h₀, h₁]

private theorem printed_gaussian_shift :
    ∃ f : 𝓢(ℝ, ℂ), ExponentialDecay f ∧ ∀ x y : ℝ,
      logMellin f ((x : ℂ) - Complex.I) + logMellin f ((y : ℂ) - Complex.I) ≠
        logMellin f x + logMellin f y := by
  obtain ⟨f, hf, _, _, hd⟩ := exists_gaussian_logProfile_exponentialDecay
  let C := (Real.pi : ℂ) ^ (1 / 2 : ℂ)
  have hC : C ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hΦ (s : ℂ) : logMellin f s = C * Complex.exp (s ^ 2 / 4) := by
    refine (mellin_fromLog_eq_integral_cexp f s).trans ?_
    have he (x : ℝ) : f x * Complex.exp (s * x) =
        Complex.exp ((-1 : ℂ) * x ^ 2 + s * x + 0) := by
      rw [hf, Complex.ofReal_exp, ← Complex.exp_add]
      push_cast
      ring_nf
    simp_rw [he]
    rw [integral_cexp_quadratic (by norm_num)]
    simp [C]
    congr 1
    ring
  refine ⟨f, hd, fun x y he ↦ ?_⟩
  simp_rw [hΦ, ← mul_add] at he
  have he' := mul_left_cancel₀ hC he
  have hnorm (t : ℝ) :
      ‖Complex.exp (((t : ℂ) - Complex.I) ^ 2 / 4)‖ < Real.exp (t ^ 2 / 4) := by
    rw [Complex.norm_exp, Real.exp_lt_exp]
    simp [sq, Complex.mul_re]
    linarith
  have hreal (t : ℝ) : Complex.exp ((t : ℂ) ^ 2 / 4) = (Real.exp (t ^ 2 / 4) : ℂ) := by
    rw [Complex.ofReal_exp]
    push_cast
    rfl
  have hle := norm_add_le (Complex.exp (((x : ℂ) - Complex.I) ^ 2 / 4))
    (Complex.exp (((y : ℂ) - Complex.I) ^ 2 / 4))
  rw [he', hreal, hreal, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_of_nonneg (add_pos (Real.exp_pos _) (Real.exp_pos _)).le] at hle
  exact (add_lt_add (hnorm x) (hnorm y)).not_ge hle

/-- Paper: Equation (B.4.2.2), p. 614. The rational character
`g ↦ |g| ^ i` has simple poles at `-i` and `1 - i`. For the Gaussian logarithmic
test, each shifted Mellin sample has modulus strictly smaller than the corresponding
positive real sample at zero or one. -/
theorem Printed.heckeAsymptoticResidue_poleTerm_false :
    ¬ Printed.heckeAsymptoticResidue_poleTerm := by
  intro h
  obtain ⟨χ, L, hL, hk, hs⟩ := printed_shifted_poles
  obtain ⟨f, hd, hf⟩ := printed_gaussian_shift
  have he := (hs (logMellin f)).unique (h ℚ χ f hd L hL)
  rw [ite_eq_left hk, one_mul, neg_inj] at he
  apply hf 0 1
  simpa using he

/-- Paper: Theorem B.4.2.2, Equation (B.4.2.17), p. 616. As printed: the
centered pole contribution alone is minus the two Mellin values at minus and plus
one half for every character. See `hasSum_heckeExplicitFormula` and ERRATA F32. -/
def Printed.heckeExplicitFormula_poleTerm : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (f : 𝓢(ℝ, ℂ)),
    ExponentialDecay f →
    ∀ (L : ℂ → ℂ), isContinuation(χ, L) →
      HasSum (fun ρ : {z : ℂ // ord(L) z < 0} ↦ (ord(L) ρ.val : ℂ) * logMellin f (ρ.val - 1 / 2))
        (-logMellin f (-1 / 2) - logMellin f (1 / 2))

/-- Paper: Theorem B.4.2.2, Equation (B.4.2.17), p. 616. The poles of the
rational character `g ↦ |g| ^ i` give the centered samples at `-1/2 - i` and
`1/2 - i`. Their moduli on a Gaussian test are strictly smaller than the printed
samples at `-1/2` and `1/2`. -/
theorem Printed.heckeExplicitFormula_poleTerm_false :
    ¬ Printed.heckeExplicitFormula_poleTerm := by
  intro h
  obtain ⟨χ, L, hL, _, hs⟩ := printed_shifted_poles
  obtain ⟨f, hd, hf⟩ := printed_gaussian_shift
  have he := (hs fun s ↦ logMellin f (s - 1 / 2)).unique (h ℚ χ f hd L hL)
  apply hf (-1 / 2) (1 / 2)
  push_cast
  convert congrArg Neg.neg he using 1 <;> push Not <;> ring_nf

/-- Paper: §B.4.2.1, Equation (B.4.2.1), p. 614. As printed: the completed
logarithmic derivative satisfies the horizontal growth bound of Definition B.3.1.1
on the strip, including at index zero. This isolates clause (2) of slow growth.
See `hasSlowGrowthNearPoles_completedHeckeL_logDeriv`,
`hasSum_heckeAsymptoticResidue`, and ERRATA F33. -/
def Printed.hasSlowGrowthNearPoles_completedHeckeL_logDeriv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (L : ℂ → ℂ),
    isContinuation(χ, L) → ∀ a : ℝ, 1 < a → a ≤ 2 →
      ∃ (T : ℤ → ℝ) (β A : ℝ), 0 < β ∧ 0 < A ∧
        ∀ (k : ℤ) (σ : ℝ), σ ∈ Ioo (1 - a) a →
          ‖logDeriv L (atHeight σ (T k))‖ ≤ A * |(k : ℝ)| ^ β

private theorem printedLogDeriv_nonzero_near (L : ℂ → ℂ) (hL : MeromorphicNFOn L univ)
    (hp : meromorphicOrderAt L 1 = -1) (z : ℂ) :
    ∀ᶠ s in 𝓝[≠] z, logDeriv L s ≠ 0 := by
  have hm := hL.meromorphicOn.logDeriv
  have ho : meromorphicOrderAt (logDeriv L) 1 = -1 :=
    meromorphicOrderAt_logDeriv_eq_neg_one (by simp [hp]) (by simp [hp])
  apply (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hm z (mem_univ z))).mp
  exact hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ (mem_univ 1)
    (mem_univ z) (by simp [ho])

/-- Paper: §B.4.2.1, Equation (B.4.2.1), p. 614. At index zero, the bound
forces the rational completed zeta logarithmic derivative to vanish along the
horizontal segment at height `T 0`. Such an accumulating set of zeros contradicts
its simple pole at one. -/
theorem Printed.hasSlowGrowthNearPoles_completedHeckeL_logDeriv_false :
    ¬ Printed.hasSlowGrowthNearPoles_completedHeckeL_logDeriv := by
  intro h
  obtain ⟨L, hL, hA⟩ := completedHeckeL_exists_continuation (1 : U[ℚ])
  obtain ⟨T, β, A, hβ, _, hb⟩ := h ℚ 1 L ⟨hL, hA⟩ 2 (by norm_num) le_rfl
  let z : ℂ := (T 0 : ℂ) * Complex.I
  have ht : Tendsto (fun x : ℝ ↦ (x : ℂ) + z) (𝓝[>] 0) (𝓝[≠] z) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.continuousAt.add_const z
        (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simpa using (show x ≠ 0 from ne_of_gt hx)
  have hne := ht.eventually
    (printedLogDeriv_nonzero_near L hL (completedHeckeL_one_order_one L hL hA) z)
  have hpos : ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x := self_mem_nhdsWithin
  have hlt : ∀ᶠ x : ℝ in 𝓝[>] 0, x < 2 :=
    (eventually_lt_nhds (show (0 : ℝ) < 2 by norm_num)).filter_mono nhdsWithin_le_nhds
  obtain ⟨x, hx, hx', hn⟩ := (hpos.and (hlt.and hne)).exists
  have hb' := hb 0 x ⟨by linarith [show 0 < x from hx], hx'⟩
  simp only [Int.cast_zero, abs_zero, Real.zero_rpow hβ.ne', mul_zero, norm_le_zero_iff] at hb'
  exact hn hb'

/-- Paper: §B.4.2.1, unnumbered display before (B.4.2.2), p. 614. As printed:
the two pole samples with positive sign minus the zero sum equals the rectangular limit
of signed meromorphic orders. Each sum is truncated in absolute imaginary part, and the
signed sum also uses the open strip. See `hasSum_heckeAsymptoticResidue` and ERRATA F34. -/
def Printed.heckeAsymptoticResidue_reversedSigns : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (f : 𝓢(ℝ, ℂ)),
    ExponentialDecay f →
    ∀ (L : ℂ → ℂ), isContinuation(χ, L) → ∀ a : ℝ, 1 < a → a ≤ 2 →
      (∀ s : ℂ, s.re = 1 - a ∨ s.re = a → meromorphicOrderAt L s = 0) →
      ∃ zeros : ℂ,
        Tendsto (fun T : ℝ ↦
          ∑ᶠ ρ : {z : ℂ // 0 < ord(L) z ∧ |z.im| < T}, logMellin f ρ.val * (ord(L) ρ.val : ℂ))
          atTop (𝓝 zeros) ∧
        Tendsto (fun T : ℝ ↦
          ∑ᶠ ρ : {z : ℂ // z ∈ strip(1 - a, a) ∧ |z.im| < T},
            logMellin f ρ.val * (ord(L) ρ.val : ℂ))
          atTop (𝓝 (delta(F, χ) * (logMellin f 0 + logMellin f 1) - zeros))

private theorem printed_translated_profiles :
    ∃ f : 𝓢(ℝ, ℂ), ExponentialDecay f ∧ (∀ x : ℝ, 0 < (logMellin f x).re) ∧
      ∀ n : ℕ, ∃ g : 𝓢(ℝ, ℂ), ExponentialDecay g ∧ ∀ s : ℂ,
        logMellin g s = Complex.exp ((n : ℂ) * (s - 1)) * logMellin f s := by
  let β : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩
  have hβ : HasCompactSupport (fun x ↦ (β x : ℂ)) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let f := hβ.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  have hd (u : 𝓢(ℝ, ℂ)) (hu : HasCompactSupport (u : ℝ → ℂ)) : ExponentialDecay u := by
    have hz (j : ℕ) : iteratedDeriv j (u : ℝ → ℂ) =ᶠ[cocompact ℝ] 0 := by
      have hh := hu.iteratedFDeriv (𝕜 := ℝ) j
      rw [hasCompactSupport_iff_eventuallyEq, coclosedCompact_eq_cocompact] at hh
      filter_upwards [hh] with x hx
      rw [iteratedDeriv_eq_iteratedFDeriv, hx]
      rfl
    exact ⟨fun j _ _ ↦ ((hz j).filter_mono atTop_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _), fun j _ _ ↦ ((hz j).filter_mono atBot_le_cocompact).trans_isBigO
      (Asymptotics.isBigO_zero _ _)⟩
  have hM (v : 𝓢(ℝ, ℂ)) (s : ℂ) : logMellin v s = ∫ x : ℝ, v x * Complex.exp (s * x) :=
    mellin_fromLog_eq_integral_cexp v s
  refine ⟨f, hd f hβ, fun s ↦ ?_, fun n ↦ ?_⟩
  · let u (x : ℝ) := β x * Real.exp (s * x)
    have he (x : ℝ) : f x * Complex.exp ((s : ℂ) * x) = (u x : ℂ) := by
      change (β x : ℂ) * _ = _
      simp [u, Complex.ofReal_exp]
    rw [hM, integral_congr_ae (ae_of_all volume he),
      integral_complex_ofReal, Complex.ofReal_re]
    apply (β.continuous.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))).integral_pos_of_hasCompactSupport_nonneg_ne_zero β.hasCompactSupport.mul_right
    · intro x
      exact mul_nonneg (β.nonneg) (Real.exp_pos _).le
    · exact (show u 0 ≠ 0 by simp [u, β.one_of_mem_closedBall (Metric.mem_closedBall_self β.rIn_pos.le)])
  · let g := (Real.exp (-(n : ℝ)) : ℂ) • (f.compSubConstCLM ℂ (n : ℝ))
    have hg : HasCompactSupport (g : ℝ → ℂ) := by
      have ht := hβ.comp_homeomorph (Homeomorph.addRight (-(n : ℝ)))
      exact ht.mul_left
    refine ⟨g, hd g hg, fun s ↦ ?_⟩
    rw [hM, hM,
      ← integral_add_right_eq_self (fun x : ℝ ↦ g x * Complex.exp (s * x)) (n : ℝ),
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with x
    change (Real.exp (-(n : ℝ)) : ℂ) * f (x + n - n) * _ = _
    rw [add_sub_cancel_right, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_natCast,
      Complex.ofReal_add, mul_add, Complex.exp_add]
    rw [show (n : ℂ) * (s - 1) = -(n : ℂ) + s * n by ring, Complex.exp_add]
    push_cast
    ring

private theorem printed_finsum_bound {S : Set ℂ} (f : S → ℂ) (g : ℂ → ℝ)
    (hg : Summable g) (hn : ∀ z, 0 ≤ g z) (hf : ∀ z, (f z).re ≤ g z.val) :
    (∑ᶠ z, f z).re ≤ ∑' z, g z := by
  classical
  by_cases h : (support f).Finite
  · rw [finsum_eq_sum_of_support_subset (s := h.toFinset) _ (by simp), Complex.re_sum]
    refine (Finset.sum_le_sum (fun i _ ↦ hf i)).trans ?_
    let e : S ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
    exact (Finset.sum_map h.toFinset e g).ge.trans
      (hg.sum_le_tsum (h.toFinset.map e) (fun i _ ↦ hn i))
  · rw [finsum_of_infinite_support h, Complex.zero_re]
    exact tsum_nonneg hn

private theorem printed_zeta_boundary (L : ℂ → ℂ) (hL : isContinuation((1 : U[ℚ]), L)) :
    ∀ s : ℂ, s.re = 1 - 2 ∨ s.re = 2 → meromorphicOrderAt L s = 0 := by
  have hn (z : ℂ) (hz : 1 < z.re) : L z ≠ 0 := by
    rw [show L z = completedHeckeL 1 ⟨z, hz⟩ from hL.2 ⟨z, hz⟩, completedHeckeL]
    exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos _ (zero_lt_one.trans hz))
      (finiteHeckeL_ne_zero_of_one_lt_re _ ⟨z, hz⟩)
  obtain ⟨ε, _, _, he⟩ := completedHeckeL_continuation_functionalEquation 1 L L
    hL.1 hL.2 hL.1 (by simpa using hL.2)
  intro s hs
  apply (hL.1 (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr
  rcases hs with hs | hs
  · intro h
    have hr := hn (1 - s) (by simp [Complex.sub_re, hs])
    exact hr (by rw [he, h, mul_zero])
  · exact hn _ (by linarith)

/-- Paper: §B.4.2.1, unnumbered display before (B.4.2.2), p. 614. Take the
completed rational zeta function, `a = 2`, and a nonzero nonnegative smooth
compactly supported logarithmic bump `f₀` with Mellin transform `Φ₀`. Use
`f(x) = exp(-n) f₀(x - n)` for sufficiently large `n`. Its Mellin transform is
`exp(n(s - 1)) Φ₀(s)`. Each zero has real part less than one, so absolute
summability for `Φ₀` gives a zero sum tending to zero as `n` grows. The pole sample
at one remains `Φ₀(1) > 0` and the sample at zero tends to zero. The two sides
therefore have real parts of opposite signs for large `n`. -/
theorem Printed.heckeAsymptoticResidue_reversedSigns_false :
    ¬ Printed.heckeAsymptoticResidue_reversedSigns := by
  intro h
  obtain ⟨L, hL, ha⟩ := completedHeckeL_exists_continuation (1 : U[ℚ])
  obtain ⟨f, hd, hpos, htranslate⟩ := printed_translated_profiles
  let d := ord(L)
  let b (s : ℂ) := ‖(d s : ℂ) * logMellin f s‖
  have hb : Summable b := (hasSum_heckeAsymptoticResidue _ f hd L hL ha 2
    (by norm_num) (by norm_num)).2.2.summable.norm
  have hz (s : ℂ) (hs : 0 < d s) : s.re < 1 := by
    by_cases h' : 0 < s.re
    · apply completedHeckeL_continuation_zeros _ L hL ha h'
      change 0 < ord(L) s at hs
      rw [hL.meromorphicOn.divisor_apply (mem_univ s)] at hs
      by_cases ht : meromorphicOrderAt L s = ⊤
      · simp [ht]
      · rw [← WithTop.coe_untop₀_of_ne_top ht]
        exact_mod_cast hs
    · linarith
  let B (n : ℕ) (s : ℂ) := if 0 < d s then Real.exp (s.re - 1) ^ n * b s else 0
  have hBn (n : ℕ) (s : ℂ) : 0 ≤ B n s := by dsimp only [B, b]; split_ifs <;> positivity
  have hBle (n : ℕ) (s : ℂ) : B n s ≤ b s := by
    dsimp only [B]
    split_ifs with hs
    · exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (Real.exp_pos _).le
        (Real.exp_le_one_iff.mpr (sub_nonpos.mpr (hz s hs).le)))
    · exact norm_nonneg _
  have hlim : Tendsto (fun n ↦ ∑' s, B n s) atTop (𝓝 0) := by
    have ht (s : ℂ) : Tendsto (fun n ↦ B n s) atTop (𝓝 0) := by
      dsimp only [B]
      split_ifs with hs
      · simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos _).le
          (Real.exp_lt_one_iff.mpr (sub_neg.mpr (hz s hs)))).mul_const (b s)
      · exact tendsto_const_nhds
    simpa using tendsto_tsum_of_dominated_convergence (g := fun _ ↦ 0) hb ht
      (Eventually.of_forall fun n s ↦ by rw [Real.norm_of_nonneg (hBn n s)]; exact hBle n s)
  obtain ⟨n, hn⟩ := (hlim.eventually_lt_const (half_pos (hpos 1))).exists
  obtain ⟨g, hg, he⟩ := htranslate n
  have hpos' (x : ℝ) : 0 < (logMellin g x).re := by
    rw [he, show (n : ℂ) * ((x : ℂ) - 1) = (((n : ℝ) * (x - 1) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_exp, Complex.re_ofReal_mul]
    exact mul_pos (Real.exp_pos _) (hpos _)
  have h1 : logMellin g 1 = logMellin f 1 := by simp [he]
  have hpoint (s : ℂ) : (logMellin g s * (d s : ℂ)).re ≤ B n s := by
    by_cases hp : 0 < d s
    · refine (Complex.re_le_norm _).trans (le_of_eq ?_)
      rw [he, mul_assoc, norm_mul, mul_comm (logMellin f s), Complex.norm_exp]
      simp only [B, ite_eq_left hp, b, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
        Complex.sub_re, Complex.one_re, zero_mul, sub_zero, ← Real.exp_nat_mul]
    · rw [show B n s = 0 by simp [B, hp]]
      by_cases hs : s ∈ ({0, 1} : Set ℂ)
      · rcases (show s = 0 ∨ s = 1 by simpa using hs) with rfl | rfl
        all_goals
          rw [show (d _ : ℂ) = ((d _ : ℝ) : ℂ) by norm_cast, Complex.re_mul_ofReal]
          apply mul_nonpos_of_nonneg_of_nonpos
          · first | simpa using (hpos' 0).le | simpa using (hpos' 1).le
          · exact_mod_cast le_of_not_gt hp
      · have hnn := (completedHeckeL_one_analyticOnNhd L hL ha _ hs).meromorphicOrderAt_nonneg
        have hge : 0 ≤ d s := by
          change 0 ≤ ord(L) s
          rw [hL.meromorphicOn.divisor_apply (mem_univ s)]
          exact WithTop.untop₀_nonneg.mpr hnn
        simp [le_antisymm (le_of_not_gt hp) hge]
  have hsum := hb.of_nonneg_of_le (hBn n) (hBle n)
  obtain ⟨z, hz₁, hz₂⟩ := h ℚ 1 g hg L ⟨hL, ha⟩ 2 (by norm_num) (by norm_num)
    (printed_zeta_boundary L ⟨hL, ha⟩)
  have hzle := le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hz₁)
    (Eventually.of_forall fun T ↦ printed_finsum_bound (S := {s : ℂ | 0 < d s ∧ |s.im| < T}) _ _ hsum (hBn n) fun u ↦ hpoint u.val)
  have hple := le_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp hz₂)
    (Eventually.of_forall fun T ↦ printed_finsum_bound (S := {s : ℂ | s ∈ strip(1 - 2, 2) ∧ |s.im| < T}) _ _ hsum (hBn n) fun u ↦ hpoint u.val)
  have hk : (1 : U[ℚ]).toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype = 1 := rfl
  simp only [ite_eq_left hk, one_mul, Complex.sub_re, Complex.add_re, h1] at hple
  change z.re ≤ ∑' s, B n s at hzle
  have hp0 : 0 < (logMellin g 0).re := by simpa using hpos' 0
  change (∑' s, B n s) < (logMellin f (1 : ℝ)).re / 2 at hn
  norm_num only [Complex.ofReal_one] at hn
  linarith

/-- Paper: Equation (B.4.2.3), p. 614. As printed: the logarithmic derivative
equals the reflected logarithmic derivative plus the logarithm of the discriminant–conductor
product, at regular nonzero points of both functions.
See `completedHeckeL_logDeriv_reflection` and ERRATA F35. -/
def Printed.completedHeckeL_logDeriv_reflection : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (L Ldual : ℂ → ℂ),
    isContinuation(χ, L) → isContinuation(χ⁻¹, Ldual) →
    ∀ s : ℂ, meromorphicOrderAt L s = 0 → meromorphicOrderAt Ldual (1 - s) = 0 →
      logDeriv L s = logDeriv Ldual (1 - s) + (heckeLogDiscriminantConductor χ : ℂ)

/-- Paper: Equation (B.4.2.3), p. 614. For the trivial rational character, compare
the printed and corrected reflection identities near one. Together they force
the logarithmic derivative to vanish near its simple pole at one. -/
theorem Printed.completedHeckeL_logDeriv_reflection_false :
    ¬ Printed.completedHeckeL_logDeriv_reflection := by
  intro h
  obtain ⟨L, hL, hA⟩ := completedHeckeL_exists_continuation (1 : U[ℚ])
  have hd : ∀ s : halfPlane, L s = completedHeckeL (1 : U[ℚ])⁻¹ s := by simpa using hA
  have hp := completedHeckeL_one_order_one L hL hA
  have hz := completedHeckeL_one_order_zero L hL hA
  have hnear (z : ℂ) (ho : meromorphicOrderAt L z = -1) :
      ∀ᶠ s in 𝓝[≠] z, meromorphicOrderAt L s = 0 :=
    ((meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hL.meromorphicOn _ (mem_univ _))).mp
      (by simp [ho])).mono fun s hs ↦ (hL (mem_univ s)).meromorphicOrderAt_eq_zero_iff.mpr hs
  have hr : Tendsto (fun s : ℂ ↦ 1 - s) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have ht : Tendsto (fun s : ℂ ↦ 1 - s) (𝓝 1) (𝓝 (1 - 1)) :=
        (show Continuous (fun s : ℂ ↦ 1 - s) by fun_prop).tendsto 1
      rw [sub_self] at ht
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_ne_zero.mpr (Ne.symm hs)
  obtain ⟨s, hs, hsr, hn⟩ := ((hnear 1 hp).and
    ((hr.eventually (hnear 0 hz)).and (printedLogDeriv_nonzero_near L hL hp 1))).exists
  have h₁ := h ℚ 1 L L ⟨hL, hA⟩ ⟨hL, hd⟩ s hs hsr
  have h₂ := RiemannMasullo.completedHeckeL_logDeriv_reflection (1 : U[ℚ]) L L hL hA hL hd s hs
  exact hn (by linear_combination (h₁ + h₂) / 2)

/-- Paper: Equation (B.4.2.10), p. 615. As printed: the raw real-line
integral gives the sample at the prime power with coefficient one. The character
value is defined at the unramified places in (3.2.1.1), and the contour
abscissa is the one chosen on p. 614.
See `hasSum_heckeExplicitFormula` and ERRATA F36. -/
def Printed.heckePrimePower_mellinSample : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (v : Primes(F)),
    (ideleClassNormTwist χ 0).IsUnramifiedAt v →
    ∀ (m : ℕ), 0 < m → ∀ (a : ℝ), 1 < a → a ≤ 2 →
    ∀ f : 𝓢(ℝ, ℂ), ExponentialDecay f →
      let Q : ℂ := q(v)
      let c := ((ideleClassNormTwist χ 0).localValue v) ^ m
      let l : ℂ := Real.log q(v)
      (l * c / Q ^ ((m : ℂ) * (a : ℂ))) *
        (∫ t : ℝ, logMellin f (atHeight a t) / Q ^ ((m : ℂ) * (t : ℂ) * Complex.I)) =
          l * c * f ((m : ℝ) * Real.log q(v))

private theorem printedPrimePower_integral (f : 𝓢(ℝ, ℂ)) (hf : ExponentialDecay f)
    (a x : ℝ) (hx : 0 < x) :
    (∫ y : ℝ, logMellin f (atHeight a y) * (x : ℂ) ^ (-(atHeight a y))) =
      2 * (Real.pi : ℂ) * f (Real.log x) :=
  integral_mul_cpow_of_mellinInv_eq (mellinInv_mellin_eq a _ hx
    (mellinConvergent_of_exponentialDecay f hf a) (verticalIntegrable_logMellin f hf a)
    (f.continuous.continuousAt.comp (Real.continuousAt_log hx.ne')))

private theorem printedPrimePower_witness :
    ∃ v : Primes(ℚ), (ideleClassNormTwist (1 : U[ℚ]) 0).IsUnramifiedAt v ∧
      (ideleClassNormTwist (1 : U[ℚ]) 0).localValue v = 1 := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let v : Primes(ℚ) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hr (u : (v.adicCompletion ℚ)ˣ) :
      (ideleClassNormTwist (1 : U[ℚ]) 0).restrict v (u : v.adicCompletion ℚ) = 1 := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    change (1 : ℂ) * _ ^ (0 : ℂ) = _
    simp
  obtain ⟨u, hu⟩ := (Valued.v : Valuation (v.adicCompletion ℚ) _).exists_isUniformizer_of_isCyclic_of_nontrivial
  have hχ : (ideleClassNormTwist (1 : U[ℚ]) 0).IsUnramifiedAt v :=
    HeckeCharacter.isUnramifiedAt_iff.mpr fun x ↦
      hr (Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom x)
  exact ⟨v, hχ, (hχ.localValue_eq _ hu).trans (hr (Units.mk0 (u : v.adicCompletion ℚ) hu.ne_zero))⟩

/-- Paper: Equation (B.4.2.10), p. 615. Use the trivial character of `ℚ`,
a finite place, `m = 1`, `a = 2`, and `f(x) = exp(-x²)`. The prime-power
sample is nonzero, and Mellin inversion gives a factor `2π` in the raw integral. -/
theorem Printed.heckePrimePower_mellinSample_false : ¬ Printed.heckePrimePower_mellinSample :=
  by
  intro h
  obtain ⟨v, hu, hv⟩ := printedPrimePower_witness
  obtain ⟨f, hf, _, _, hd⟩ := exists_gaussian_logProfile_exponentialDecay
  let q := q(v)
  have hq : 1 < q := by dsimp only [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  have hl : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  have htest : f (Real.log q) ≠ 0 := by rw [hf]; exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hp := h ℚ 1 v hu 1 (by decide) 2 (by norm_num) (by norm_num) f hd
  dsimp only at hp
  simp only [hv, pow_one, Nat.cast_one, Complex.ofReal_ofNat, one_mul, mul_one] at hp
  change (Real.log q : ℂ) / (q : ℂ) ^ (2 : ℂ) *
    (∫ t : ℝ, logMellin f (atHeight 2 t) / (q : ℂ) ^ ((t : ℂ) * Complex.I)) = _ at hp
  have hsplit (t : ℝ) : (q : ℂ) ^ (-(atHeight 2 t)) =
      ((q : ℂ) ^ (2 : ℂ))⁻¹ * ((q : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ := by
    rw [neg_add_rev, Complex.cpow_add _ _ hqC, Complex.cpow_neg, Complex.cpow_neg]
    norm_num
    ring
  have hM := printedPrimePower_integral f hd 2 q (by linarith)
  simp_rw [hsplit, mul_left_comm (logMellin f _), ← div_eq_mul_inv] at hM
  rw [integral_const_mul] at hM
  have he : 2 * (Real.pi : ℂ) * f (Real.log q) = f (Real.log q) := by
    apply mul_left_cancel₀ hl
    rw [← hM]
    convert hp using 1
    ring
  have he' : 2 * (Real.pi : ℂ) = 1 := mul_right_cancel₀ htest (he.trans (one_mul _).symm)
  have := congrArg Complex.re he'
  norm_num at this
  linarith [Real.pi_gt_three]

/-- Paper: Equation (B.4.2.11), p. 615. As printed: the reflected upward
contour gives the reciprocal sample with coefficient minus i times the inverse
prime power. The character value is defined at the unramified places in (3.2.1.1),
and the contour abscissa is the one chosen on p. 614.
See `hasSum_heckeExplicitFormula` and ERRATA F36. -/
def Printed.heckePrimePower_mellinSample_reflected : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (v : Primes(F)),
    (ideleClassNormTwist χ 0).IsUnramifiedAt v →
    ∀ (m : ℕ), 0 < m → ∀ (a : ℝ), 1 < a → a ≤ 2 →
    ∀ f : 𝓢(ℝ, ℂ), ExponentialDecay f →
      let Q : ℂ := q(v)
      let cdual := ((ideleClassNormTwist χ⁻¹ 0).localValue v) ^ m
      let l : ℂ := Real.log q(v)
      l * verticalLineIntegral
        (fun s ↦ logMellin f (1 - s) * cdual / Q ^ ((m : ℂ) * s)) a =
          -Complex.I * l * (cdual / Q ^ m) * f (-(m : ℝ) * Real.log q(v))

/-- Paper: Equation (B.4.2.11), p. 615. Use the trivial character of `ℚ`,
a finite place, `m = 1`, `a = 2`, and `f(x) = exp(-x²)`. The reciprocal
sample is nonzero. The reflected integral gives `2πi` times the inverse prime
power, since reversing the endpoints cancels the change of differential. -/
theorem Printed.heckePrimePower_mellinSample_reflected_false :
    ¬ Printed.heckePrimePower_mellinSample_reflected := by
  intro h
  obtain ⟨v, hu, hv⟩ := printedPrimePower_witness
  obtain ⟨f, hf, _, _, hd⟩ := exists_gaussian_logProfile_exponentialDecay
  let q := q(v)
  have hq : 1 < q := by dsimp only [q]; exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hq' : 0 < q := by linarith
  have hqC : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq'.ne'
  have hl : (Real.log q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hq).ne'
  have htest : f (-Real.log q) ≠ 0 := by rw [hf]; exact Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hp := h ℚ 1 v hu 1 (by decide) 2 (by norm_num) (by norm_num) f hd
  dsimp only at hp
  simp only [inv_one, hv, Nat.cast_one, one_mul, mul_one, pow_one, neg_one_mul] at hp
  let Φ := logMellin f
  let J := fun t : ℝ ↦ Φ (1 - atHeight 2 t) / (q : ℂ) ^ (atHeight 2 t)
  change (Real.log q : ℂ) * (Complex.I * ∫ t, J t) =
    -Complex.I * (Real.log q : ℂ) * (1 / (q : ℂ)) * f (-Real.log q) at hp
  have hM := printedPrimePower_integral f hd (-1) q⁻¹ (inv_pos.mpr hq')
  rw [Real.log_inv] at hM
  have hsub (t : ℝ) : J (-t) =
      (q : ℂ)⁻¹ * (Φ (atHeight (-1) t) * ((q⁻¹ : ℝ) : ℂ) ^ (-(atHeight (-1) t))) := by
    have hz : 1 - atHeight 2 (-t) = atHeight (-1) t := by push_cast; ring
    have hs : atHeight 2 (-t) = 1 + -(atHeight (-1) t) := by push_cast; ring
    unfold J
    rw [hz, hs, Complex.cpow_add 1 _ hqC, Complex.cpow_one]
    simp only [Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg hq'.le, div_eq_mul_inv, mul_inv_rev]
    ring
  have hJ : (∫ t, J t) = (q : ℂ)⁻¹ * (2 * (Real.pi : ℂ) * f (-Real.log q)) := by
    rw [← integral_neg_eq_self J, funext hsub, integral_const_mul, hM]
  rw [hJ] at hp
  have hc : (Real.log q : ℂ) * Complex.I * (q : ℂ)⁻¹ * f (-Real.log q) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hl Complex.I_ne_zero) (inv_ne_zero hqC)) htest
  have he : (2 * (Real.pi : ℂ) + 1) * ((Real.log q : ℂ) * Complex.I *
      (q : ℂ)⁻¹ * f (-Real.log q)) = 0 := by linear_combination hp
  have he' := congrArg Complex.re ((mul_eq_zero.mp he).resolve_right hc)
  norm_num at he'
  linarith [Real.pi_gt_three]

local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "localChart(" w ", " χ ")" =>
  quasiCharacterNormTwist
    ((Units.map nnNormHom.toMonoidHom) ^ (InfinitePlace.mult w) :
      (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ) (continuous_infiniteLocalModule w)
    (ContinuousMonoidHom.comp circleToComplex χ)
local notation "classRestriction(" F ", " w ", " χ ")" =>
  ((χ).comp ⟨IdeleClassGroup.ofCompletion (𝓞 F) F w, continuous_ideleClass_ofCompletion F w⟩)
local notation "positiveUnit(" w ", " t ", " ht ")" =>
  (if hw : InfinitePlace.IsReal w then
    Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom
      (Units.mk0 t (ne_of_gt ht))
  else
    Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw)).symm.toMonoidHom
      (Units.mk0 (t : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))))
local notation "isRadialExponent(" w ", " χ ", " s ")" =>
  ((s : ℂ).re = 0 ∧ ∀ (t : ℝ) (ht : 0 < t), (χ (positiveUnit(w, t, ht)) : ℂ) = (t : ℂ) ^ s)
local notation "archAlpha(" w ")" =>
  (if InfinitePlace.IsReal w then -Real.log Real.pi / 2 else -Real.log (2 * Real.pi))
local notation "archDegree(" w ")" => (if InfinitePlace.IsReal w then (2 : ℝ) else 1)
local notation "archMult(" w ")" => (InfinitePlace.mult w : ℝ)

/-- Paper: Equation (B.4.2.12), pp. 615–616. As printed: the local logarithmic
derivative has constant minus alpha and the digamma argument is s minus the
positive-real character exponent, divided by the local degree. See
`realHeckeArchimedean_mellinLogDeriv`, `complexHeckeArchimedean_mellinLogDeriv`,
and ERRATA F37 and F39. -/
def Printed.heckeArchimedean_logDeriv : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : U[F]) (w : InfinitePlace F) (sv : ℂ),
    isRadialExponent(w, classRestriction(F, w, χ), sv) →
    ∀ s : ℂ,
      let Lv := infiniteLocalEulerFactor w ∘ localChart(w, classRestriction(F, w, χ))
      let z := (s - sv) / (archDegree(w) : ℂ)
      meromorphicOrderAt Lv s = 0 → meromorphicOrderAt Complex.Gamma z = 0 →
        logDeriv Lv s = -(archAlpha(w) : ℂ) + (archDegree(w) : ℂ)⁻¹ * logDeriv Complex.Gamma z

/-- Paper: Equation (B.4.2.12), pp. 615–616. At the real place of `ℚ` with
trivial character and `s = 2`, the printed and actual digamma arguments agree.
The constant is `-log(π)/2` from the gamma prefactor, while the printed constant is
`+log(π)/2`. Independently, the primitive quadratic character modulo three has
local sign at the real place. It has the same exponent on positive reals as the
trivial character, but its gamma argument is `(s + 1)/2` in place of `s/2`. -/
theorem Printed.heckeArchimedean_logDeriv_false :
    ¬ Printed.heckeArchimedean_logDeriv := by
  intro h
  have hw := Rat.isReal_infinitePlace
  have hone : ((1 : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ)).comp
      ⟨IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace,
        continuous_ideleClass_ofCompletion ℚ Rat.infinitePlace⟩) = 1 :=
    ContinuousMonoidHom.ext fun _ ↦ rfl
  have key :=
    h ℚ 1 Rat.infinitePlace 0 (by rw [hone]; exact ⟨by simp, fun t ht ↦ by simp⟩) 2
  simp only [hone] at key
  have hfun : ∀ x, infiniteLocalEulerFactor Rat.infinitePlace
      (quasiCharacterNormTwist ((Units.map nnNormHom.toMonoidHom) ^ Rat.infinitePlace.mult)
        (continuous_infiniteLocalModule Rat.infinitePlace)
        (ContinuousMonoidHom.comp (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ) 1)
          x) =
      Complex.Gammaℝ x := fun x ↦ infiniteLocalEulerFactor_real_norm _ hw x
  simp only [Function.comp_def, hw, ite_true] at key
  simp only [hfun] at key
  have hz : ((2 : ℂ) - 0) / ((2 : ℝ) : ℂ) = 1 := by norm_num
  rw [hz] at key
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hdΓ : ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ Complex.Gamma s := fun s hs ↦
    Complex.differentiableAt_Gamma s fun m hm ↦ by
      have := congrArg Complex.re hm
      simp at this
      linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hΓ1 : AnalyticAt ℂ Complex.Gamma 1 :=
    DifferentiableOn.analyticAt (fun s hs ↦ (hdΓ s hs).differentiableWithinAt)
      (hopen.mem_nhds (by simp))
  have hdpow : ∀ s : ℂ, DifferentiableAt ℂ (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) s :=
    fun s ↦
    ((differentiableAt_id.neg.div_const 2).const_cpow (Or.inl hpi))
  have hdhalf :
      ∀ s : ℂ, 0 < s.re → DifferentiableAt ℂ (fun s : ℂ ↦ Complex.Gamma (s / 2)) s :=
    fun s hs ↦ (hdΓ (s / 2) (by simpa using hs)).comp s (differentiableAt_id.div_const 2)
  have hGR : AnalyticAt ℂ (fun x : ℂ ↦ x.Gammaℝ) 2 :=
    DifferentiableOn.analyticAt (fun s hs ↦ ((hdpow s).mul (hdhalf s hs)).differentiableWithinAt)
      (hopen.mem_nhds (by simp))
  have hord1 := hGR.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
    (Complex.Gammaℝ_ne_zero_of_re_pos (by simp))
  have hord2 := hΓ1.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr (by simp)
  have k := key hord1 hord2
  have hsplit : logDeriv (fun x : ℂ ↦ x.Gammaℝ) 2 =
      logDeriv (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) 2 +
        logDeriv (fun s : ℂ ↦ Complex.Gamma (s / 2)) 2 :=
    logDeriv_mul (f := fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2))
      (g := fun s : ℂ ↦ Complex.Gamma (s / 2))
      2 (by simp [hpi]) (by norm_num) (hdpow 2) (hdhalf 2 (by simp))
  have hpow :
      logDeriv (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2)) 2 = -(Real.log Real.pi : ℂ) / 2 := by
    have hd : HasDerivAt (fun s : ℂ ↦ (Real.pi : ℂ) ^ (-s / 2))
        ((Real.pi : ℂ) ^ (-(2 : ℂ) / 2) * Complex.log Real.pi * (-1 / 2)) 2 :=
      ((hasDerivAt_id' (2 : ℂ)).neg.div_const 2).const_cpow (Or.inl hpi)
    have hne : (Real.pi : ℂ) ^ (-(2 : ℂ) / 2) ≠ 0 := by simp [hpi]
    rw [logDeriv_apply, hd.deriv, ← Complex.ofReal_log Real.pi_pos.le]
    field_simp
  have hgam : logDeriv (fun s : ℂ ↦ Complex.Gamma (s / 2)) 2 =
      logDeriv Complex.Gamma 1 * (1 / 2) := by
    have := logDeriv_comp (f := Complex.Gamma) (g := fun s : ℂ ↦ s / 2) (x := 2)
      (by norm_num; exact hdΓ 1 (by simp)) (differentiableAt_id.div_const 2)
    simp only [Function.comp_def] at this
    rw [this]
    norm_num
  rw [hsplit, hpow, hgam] at k
  push_cast at k
  have hlog : (Real.log Real.pi : ℂ) = 0 := by linear_combination -k
  have := Real.log_pos (by linarith [Real.pi_gt_three] : (1 : ℝ) < Real.pi)
  exact absurd (Complex.ofReal_eq_zero.mp hlog) this.ne'

/-- Paper: Proposition B.4.2.1, proof, Equation (B.4.2.16), p. 616. As printed:
the sum of the local contour integrals equals the centered contour with the two
bare digammas. See `realHeckeArchimedean_mellinLogDeriv`,
`complexHeckeArchimedean_mellinLogDeriv`, and ERRATA F37. -/
def Printed.heckeArchimedean_mellinLogDeriv_centered : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (sv : ℂ),
    isRadialExponent(w, χ, sv) →
    ∀ (a : ℝ), 1 < a → ∀ f : 𝓢(ℝ, ℂ), ExponentialDecay f →
      let Lv := infiniteLocalEulerFactor w ∘ localChart(w, χ)
      let LvDual := infiniteLocalEulerFactor w ∘ localChart(w, χ⁻¹)
      let N : ℂ := archMult(w)
      verticalLineIntegral
          (fun s ↦ logMellin f s * logDeriv Lv s + logMellin f (1 - s) * logDeriv LvDual s) a
          / twoPiI =
        verticalLineIntegral (fun s ↦ logMellin f s *
          (logDeriv Complex.Gamma (N * (s - sv) / 2) +
            logDeriv Complex.Gamma (N * (1 - s + sv) / 2))) (1 / 2) / twoPiI

private theorem printed_complex_place :
    ∃ (F : Type) (_ : Field F) (_ : NumberField F) (w : InfinitePlace F), w.IsComplex := by
  have : IsCyclotomicExtension {4} ℚ (CyclotomicField 4 ℚ) := by
    convert! CyclotomicField.isCyclotomicExtension 4 ℚ using 1
  let w : InfinitePlace (CyclotomicField 4 ℚ) := Classical.arbitrary _
  exact ⟨CyclotomicField 4 ℚ, inferInstance, inferInstance, w,
    (IsCyclotomicExtension.Rat.isTotallyComplex (CyclotomicField 4 ℚ) (n := 4) (by decide)).isComplex w⟩

private theorem printed_arch_angular {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (hw : w.IsComplex) (n : ℕ) :
    ∃ χ : PontryaginDual w.Completionˣ, isRadialExponent(w, χ, (0 : ℂ)) ∧
      (complexLocalEulerParameters w hw (ContinuousMonoidHom.comp circleToComplex χ)).exists.choose =
        (0, (n : ℤ)) := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
  let p (u : w.Completionˣ) := e u.val / (‖e u.val‖ : ℂ)
  have hne (u : w.Completionˣ) : e u.val ≠ 0 := e.map_ne_zero_iff.mpr u.ne_zero
  have hp (u : w.Completionˣ) : ‖p u‖ = 1 := by
    simp [p, (norm_pos_iff.mpr (hne u)).ne']
  have he : Continuous (fun u : w.Completionˣ ↦ e u.val) :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).continuous.comp Units.continuous_val
  let χ : PontryaginDual w.Completionˣ :=
    { toFun := fun u ↦ ⟨p u ^ n, mem_sphere_zero_iff_norm.mpr (by simp [hp])⟩
      map_one' := Subtype.ext (by simp [p])
      map_mul' := fun u v ↦ Subtype.ext (by
        change p (u * v) ^ n = p u ^ n * p v ^ n
        simp [p, Complex.ofReal_mul, mul_pow, mul_div_mul_comm])
      continuous_toFun := ((he.div (Complex.continuous_ofReal.comp he.norm)
        (fun u ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hne u)))).pow n).subtype_mk _ }
  have hval (u : ℂˣ) : (χ (Units.map e.symm.toMonoidHom u) : ℂ) =
      ((u.val : ℂ) / (‖u.val‖ : ℂ)) ^ n := by
    change (e (e.symm u.val) / (‖e (e.symm u.val)‖ : ℂ)) ^ n = _
    rw [e.apply_symm_apply]
  refine ⟨χ, ⟨by simp, fun t ht ↦ ?_⟩, ?_⟩
  · rw [dite_eq_right (InfinitePlace.not_isReal_iff_isComplex.mpr hw)]
    simpa [Complex.norm_real, abs_of_pos ht, ht.ne'] using hval
      (Units.mk0 (t : ℂ) (Complex.ofReal_ne_zero.mpr ht.ne'))
  · apply (complexLocalEulerParameters w hw _).unique (complexLocalEulerParameters w hw _).exists.choose_spec
    intro u
    simp only [Complex.cpow_zero, one_mul, zpow_natCast]
    exact hval u

private theorem printed_arch_kernel_ne (f : 𝓢(ℝ, ℂ)) (hf : ∀ t : ℝ, f t = (Real.exp (-(t ^ 2)) : ℂ))
    (h₀ : IntegrableOn (heckeArchimedeanDigammaKernel 1 0 1 f) (Ioi 0))
    (h₂ : IntegrableOn (heckeArchimedeanDigammaKernel 1 1 2 f) (Ioi 0)) :
    (∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1 1 2 f t) ≠
      ∫ t in Ioi (0 : ℝ), heckeArchimedeanDigammaKernel 1 0 1 f t := by
  let g (t : ℝ) := Real.exp (-(t ^ 2)) + Real.exp (-t) * Real.exp (-((-t) ^ 2))
  have hg (t : ℝ) (ht : 0 < t) : heckeArchimedeanDigammaKernel 1 1 2 f t -
      heckeArchimedeanDigammaKernel 1 0 1 f t = (g t : ℂ) := by
    have hden : (1 : ℂ) - Real.exp (-t) ≠ 0 := sub_ne_zero.mpr (by
      exact_mod_cast (Real.exp_lt_one_iff.mpr (neg_neg_of_pos ht)).ne')
    have htwo : Complex.exp (-(2 : ℂ) * t) = (Real.exp (-t) : ℂ) ^ 2 := by
      rw [sq, Complex.ofReal_exp, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp only [heckeArchimedeanDigammaKernel, one_mul, neg_zero, zero_mul, Complex.exp_zero,
      mul_one, neg_one_mul, htwo, g, Complex.ofReal_add, Complex.ofReal_mul, hf]
    rw [← Complex.ofReal_neg, ← Complex.ofReal_exp]
    field_simp
    push_cast
    ring
  have hae := ae_restrict_of_forall_mem (μ := volume) measurableSet_Ioi hg
  have hi : IntegrableOn g (Ioi 0) := ((h₂.sub h₀).congr hae).re
  have hpos : 0 < ∫ t in Ioi (0 : ℝ), g t := by
    apply (integral_pos_iff_support_of_nonneg (fun t ↦ (show 0 < g t by dsimp [g]; positivity).le) hi).mpr
    have hs : support g = univ := eq_univ_of_forall fun t ↦
      (show 0 < g t by dsimp [g]; positivity).ne'
    rw [hs, Measure.restrict_apply_univ]
    exact isOpen_Ioi.measure_pos volume nonempty_Ioi
  intro he
  apply (Complex.ofReal_ne_zero.mpr hpos.ne')
  rw [← integral_complex_ofReal, ← integral_congr_ae hae, integral_sub h₂ h₀, he, sub_self]

/-- Paper: Proposition B.4.2.1, proof, Equation (B.4.2.16), p. 616. At a complex
place, the trivial character and the angular character of weight two have the
same radial exponent. The printed centered integrals coincide. The corrected
digamma kernels on a Gaussian differ by a strictly positive integral. -/
theorem Printed.heckeArchimedean_mellinLogDeriv_centered_false :
    ¬ Printed.heckeArchimedean_mellinLogDeriv_centered := by
  intro h
  obtain ⟨F, _, _, w, hw⟩ := printed_complex_place
  obtain ⟨f, hf, _, _, hd⟩ := exists_gaussian_logProfile_exponentialDecay
  let P := verticalLineIntegral (fun s ↦ logMellin f s *
    (logDeriv Complex.Gamma ((archMult(w) : ℂ) * (s - 0) / 2) +
      logDeriv Complex.Gamma ((archMult(w) : ℂ) * (1 - s + 0) / 2))) (1 / 2) / twoPiI
  have eqn (n : ℕ) :
      let K := heckeArchimedeanDigammaKernel 1 ((n : ℂ) / 2) (1 + (n : ℂ) / 2) f
      IntegrableOn K (Ioi 0) ∧ P = (∫ t in Ioi (0 : ℝ), K t) - 2 * (Real.log (2 * Real.pi) : ℂ) * f 0 := by
    obtain ⟨χ, hχ, hp⟩ := printed_arch_angular w hw n
    have he := h F w χ 0 hχ 2 (by norm_num) f hd
    have hc := (complexHeckeArchimedean_mellinLogDeriv w hw χ f hd 2 (by norm_num)).2
    dsimp only at hc
    rw [hp] at hc
    simp only [Int.natAbs_natCast, zero_add, sub_zero] at hc
    exact ⟨hc.1, he.symm.trans hc.2⟩
  have h₀ := eqn 0
  have h₂ := eqn 2
  norm_num only [Nat.cast_zero, Nat.cast_ofNat, zero_div, add_zero, div_self (two_ne_zero : (2 : ℂ) ≠ 0),
    one_add_one_eq_two] at h₀ h₂
  exact printed_arch_kernel_ne f hf h₀.1 h₂.1 (sub_left_inj.mp (h₂.2.symm.trans h₀.2))

/-- Paper: Proposition B.4.2.1, Equation (B.4.2.15), p. 616. As printed: the
displayed archimedean integral exists. This isolates convergence at the upper
endpoint by truncating the printed integrand from one to a growing upper bound.
The same integral occurs in (B.4.2.17). See `heckeArchimedeanDigammaKernel` and ERRATA F38. -/
def Printed.heckeArchimedean_integral_convergesAtTop : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) (sv : ℂ),
    isRadialExponent(w, χ, sv) →
    ∀ (a : ℝ), 1 < a → ∀ f : 𝓢(ℝ, ℂ), ExponentialDecay f →
      let N : ℝ := archMult(w)
      let K := fun x : ℝ ↦
        (N : ℂ) * f 0 / (x : ℂ) -
          (f x * Complex.exp (sv * (x : ℂ)) + f (-x) * Complex.exp (-sv * (x : ℂ))) *
            (Real.exp ((2 / N - 1 / 2) * x) : ℂ) / (1 - (Real.exp (-(2 / N * x)) : ℂ))
      ∃ tail : ℂ, Tendsto (fun R : ℝ ↦ ∫ x in Ioc 1 R, K x) atTop (𝓝 tail)

/-- Paper: Proposition B.4.2.1, Equation (B.4.2.15), p. 616. At the real
place of `ℚ`, take the trivial local character, `a = 2`, and a smooth
logarithmic bump supported in `(-1,1)` with value one at zero. On `x > 1`
the two samples vanish, so the upper truncation is exactly `log R` for `R > 1`. -/
theorem Printed.heckeArchimedean_integral_convergesAtTop_false :
    ¬ Printed.heckeArchimedean_integral_convergesAtTop := by
  intro h
  let β : ContDiffBump (0 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have hβ1 : β 0 = 1 := β.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num))
  have hcs : HasCompactSupport (fun x ↦ (β x : ℂ)) :=
    β.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : 𝓢(ℝ, ℂ) := hcs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  have hf : ∀ x, f x = β x := fun _ ↦ rfl
  have hts : tsupport (f : ℝ → ℂ) ⊆ Metric.closedBall 0 (1 / 2) := by
    refine (tsupport_comp_subset Complex.ofReal_zero _).trans ?_
    rw [β.tsupport_eq]
  have hout : ∀ x : ℝ, 1 / 2 < |x| → x ∉ tsupport (f : ℝ → ℂ) := by
    intro x hx hmem
    have := hts hmem
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    linarith
  have hzero : ∀ x : ℝ, 1 / 2 < |x| → f x = 0 := fun x hx ↦
    image_eq_zero_of_notMem_tsupport (hout x hx)
  have hder : ∀ (j : ℕ) (x : ℝ), 1 / 2 < |x| → iteratedDeriv j (f : ℝ → ℂ) x = 0 := by
    intro j x hx
    rw [iteratedDeriv_eq_iteratedFDeriv,
      image_eq_zero_of_notMem_tsupport (fun hm ↦ hout x hx (tsupport_iteratedFDeriv_subset j hm))]
    rfl
  have hdec : ExponentialDecay f := by
    refine ⟨fun j A _ ↦ ?_, fun j A _ ↦ ?_⟩
    · refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
      filter_upwards [eventually_gt_atTop (1 / 2 : ℝ)] with x hx
      exact hder j x (by rw [abs_of_pos (by linarith)]; exact hx)
    · refine EventuallyEq.trans_isBigO ?_ (Asymptotics.isBigO_zero _ _)
      filter_upwards [eventually_lt_atBot (-(1 / 2) : ℝ)] with x hx
      exact hder j x (by rw [abs_of_neg (by linarith)]; linarith)
  obtain ⟨tail, ht⟩ :=
    h ℚ Rat.infinitePlace 1 0 ⟨by simp, fun t ht ↦ by simp⟩ 2 (by norm_num) f hdec
  have hN : (InfinitePlace.mult Rat.infinitePlace : ℝ) = 1 := by
    simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
  have hlog : ∀ R : ℝ, 1 ≤ R → (∫ x in Ioc 1 R,
      ((InfinitePlace.mult Rat.infinitePlace : ℝ) : ℂ) * f 0 / (x : ℂ) -
        (f x * Complex.exp (0 * (x : ℂ)) + f (-x) * Complex.exp (-0 * (x : ℂ))) *
          (Real.exp ((2 / (InfinitePlace.mult Rat.infinitePlace : ℝ) - 1 / 2) * x) : ℂ) /
            (1 - (Real.exp (-(2 / (InfinitePlace.mult Rat.infinitePlace : ℝ) * x)) : ℂ))) =
      (Real.log R : ℂ) := by
    intro R hR
    rw [setIntegral_congr_fun measurableSet_Ioc (g := fun x : ℝ ↦ ((x⁻¹ : ℝ) : ℂ))
      (fun x hx ↦ by
        have hx1 : 1 / 2 < |x| := by rw [abs_of_pos (by linarith [hx.1])]; linarith [hx.1]
        have hx2 : 1 / 2 < |-x| := by rwa [abs_neg]
        rw [hzero x hx1, hzero (-x) hx2, hN, hf, hβ1]
        push_cast
        ring)]
    rw [integral_complex_ofReal, ← intervalIntegral.integral_of_le hR,
      integral_inv_of_pos one_pos (by linarith), div_one]
  have hre := (Complex.continuous_re.tendsto _).comp ht
  refine not_tendsto_nhds_of_tendsto_atTop Real.tendsto_log_atTop _
    (hre.congr' ?_)
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  simp only [Function.comp_apply]
  rw [hlog R hR, Complex.ofReal_re]

local notation "𝒮ₐ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "𝒟(" G ")" => BruhatCompactSupport G
local notation "addTest(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "ν𝔭(" F ", " v ")" => finiteLocalAdditiveTamagawaMeasure F v
local notation "ν∞(" F ", " w ")" => infiniteLocalAdditiveTamagawaMeasure F w
local notation "ψ∞(" F ", " w ")" =>
  (fun x ↦ adeleStandardCharacter F (@Pi.single _ _ _ (Classical.decEq _) w x, 0))

local instance instFiniteCompletionMeasurableB4Printed
    (F : Type) [Field F] [NumberField F] (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F) := borel _
local instance instFiniteUnitsMeasurableB4Printed
    (F : Type) [Field F] [NumberField F] (v : Primes(F)) :
    MeasurableSpace (v.adicCompletion F)ˣ := borel _
local instance instInfiniteCompletionMeasurableB4Printed
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F) :
    MeasurableSpace w.Completion := borel _
local instance instFiniteUnitsLocallyCompactB4Printed
    (F : Type) [Field F] [NumberField F] (v : Primes(F)) :
    LocallyCompactSpace (v.adicCompletion F)ˣ :=
  letI : ProperSpace (v.adicCompletion F) := properSpace_adicCompletion v
  inferInstance
local instance instIdeleClassT2B4Printed
    (F : Type) [Field F] [NumberField F] : T2Space C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactB4Printed
    (F : Type) [Field F] [NumberField F] : LocallyCompactSpace C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1

/-- Paper: Proposition B.4.3.1, uniqueness sentence, p. 618. As printed: the
function defined by (B.4.3.2) is an additive Schwartz–Bruhat test at every finite
place. This is the membership assertion in the uniqueness sentence. See
`finiteLogFourier_unique` and ERRATA F40. -/
def Printed.finiteLog_isSchwartzBruhat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Primes(F)),
    ∃ J : 𝒮ₐ(v.adicCompletion F), ∀ x : v.adicCompletion F, x ≠ 0 →
      addTest(J) x = (Real.log ‖x‖ / Real.log q(v) : ℝ)

/-- Paper: Proposition B.4.3.1, uniqueness sentence, p. 618. In the completion
of `ℚ` at two, the values at `2^n` are `-n`. They are unbounded as the arguments
tend to zero, so no value at zero gives even a continuous representative. -/
theorem Printed.finiteLog_isSchwartzBruhat_false : ¬ Printed.finiteLog_isSchwartzBruhat := by
  intro h
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 ℚ)
  let v : HeightOneSpectrum (𝓞 ℚ) := ⟨m, hm.isPrime, NeZero.ne m⟩
  obtain ⟨J, hJ⟩ := h ℚ v
  let val : Valuation (v.adicCompletion ℚ) (WithZero (Multiplicative ℤ)) := Valued.v
  obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
  have hlt : ‖(π : v.adicCompletion ℚ)‖ < 1 :=
    Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one
  have hpos : 0 < ‖(π : v.adicCompletion ℚ)‖ := norm_pos_iff.mpr hπ.ne_zero
  have hq : 0 < Real.log (Ideal.absNorm v.asIdeal : ℝ) :=
    Real.log_pos (by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v)
  have hc : Continuous fun x : v.adicCompletion ℚ ↦ J (Multiplicative.ofAdd x) :=
    (schwartzBruhat_continuous J).comp continuous_ofAdd
  have hlim : Tendsto (fun n : ℕ ↦ (π : v.adicCompletion ℚ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hlt
  have hre := (Complex.continuous_re.tendsto _).comp ((hc.tendsto 0).comp hlim)
  have hbot : Tendsto (fun n : ℕ ↦ (n : ℝ) *
      (Real.log ‖(π : v.adicCompletion ℚ)‖ / Real.log (Ideal.absNorm v.asIdeal : ℝ)))
      atTop atBot :=
    tendsto_natCast_atTop_atTop.atTop_mul_const_of_neg
      (div_neg_of_neg_of_pos (Real.log_neg hpos hlt) hq)
  refine not_tendsto_nhds_of_tendsto_atBot hbot _ (hre.congr fun n ↦ ?_)
  have hn := hJ _ (pow_ne_zero n hπ.ne_zero)
  simp only [Function.comp_apply]
  rw [show J (Multiplicative.ofAdd ((π : v.adicCompletion ℚ) ^ n)) = _ from hn,
    Complex.ofReal_re, norm_pow, Real.log_pow]
  ring

local notation "archLogPairing(" F ", " w ", " f ")" =>
  (∫ y : InfinitePlace.Completion w, (Real.log (‖y‖ ^ InfinitePlace.mult w) : ℂ) *
    tamagawaFourier ν∞(F, w) ψ∞(F, w) addTest(f) y ∂ν∞(F, w))
local notation "eulerLogConstant" => (Real.log (2 * Real.pi) + Real.eulerMascheroniConstant)

/-- Paper: Proposition B.4.3.2(1), Equation (B.4.3.13), p. 619. As printed:
the real Fourier pairing is minus the full cutoff limit minus twice the logarithmic
constant times the value at zero. See `realLogFourier_finitePart` and ERRATA F41. -/
def Printed.realLogFourier_finitePart : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), w.IsReal →
    ∀ f : 𝒮ₐ(w.Completion), ∃ A : ℂ,
      Tendsto (fun ε : ℝ ↦
        (∫ x in {x : w.Completion | ε ≤ ‖x‖}, addTest(f) x / (‖x‖ : ℂ) ∂ν∞(F, w)) +
          2 * addTest(f) 0 * (Real.log ε : ℂ)) (𝓝[>] 0) (𝓝 A) ∧
      archLogPairing(F, w, f) = -A - 2 * (eulerLogConstant : ℂ) * addTest(f) 0

private theorem printed_nonnegative_test {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {U : Set G}
    (hU : IsOpen U) {x : G} (hx : x ∈ U) :
    ∃ f : SchwartzBruhat G, HasCompactSupport f.val ∧ tsupport f.val ⊆ U ∧ f x = 1 ∧
      ∀ y, f y = ((f y).re : ℂ) ∧ 0 ≤ (f y).re := by
  obtain ⟨v, hc, hs, hv⟩ := schwartzBruhat_exists_local_unit hU hx
  let φ (z : ℂ) : ℂ := (z.re ^ 2 : ℝ)
  have hφ : ContDiff ℝ (∞) φ := Complex.ofRealCLM.contDiff.comp (Complex.reCLM.contDiff.pow 2)
  have h0 : φ 0 = 0 := by simp [φ]
  obtain ⟨f, hf⟩ := compact_schwartzBruhat_comp hc hφ h0
  have hs' : tsupport f.val ⊆ tsupport v.val := hf ▸ tsupport_comp_subset h0 _
  refine ⟨f, hc.of_isClosed_subset (isClosed_tsupport _) hs', hs'.trans hs, ?_, ?_⟩
  · change f.val x = 1
    rw [hf, comp_apply, hv.eq_of_nhds]
    norm_num [φ]
  · intro y
    change f.val y = _ ∧ 0 ≤ (f.val y).re
    rw [hf]
    exact ⟨rfl, sq_nonneg _⟩

private theorem printed_arch_cutoff_test {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (d : w.Completion → ℝ) (hd : Continuous d)
    (hd₀ : d 0 = 0) (hd₁ : d 1 = 1) :
    ∃ (f : 𝒮ₐ(w.Completion)) (B : ℝ), addTest(f) 0 = 0 ∧ 0 < B ∧
      ∀ᶠ ε : ℝ in 𝓝[>] 0,
        (∫ x in {x | ε ≤ d x}, addTest(f) x / (d x : ℂ) ∂ν∞(F, w)) = (B : ℂ) := by
  let U : Set (Multiplicative w.Completion) := {x | 1 / 2 < d x.toAdd}
  obtain ⟨f, hc, hs, hf₁, hf⟩ := printed_nonnegative_test
    (x := Multiplicative.ofAdd (1 : w.Completion)) (U := U)
    (isOpen_lt continuous_const (hd.comp continuous_toAdd)) (by norm_num [U, hd₁])
  have hout (x : w.Completion) (hx : d x ≤ 1 / 2) : addTest(f) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hm ↦ (not_lt.mpr hx) (hs hm))
  let g (x : w.Completion) := (addTest(f) x).re / max (d x) (1 / 2)
  let μ := ν∞(F, w)
  let : BorelSpace w.Completion := ⟨rfl⟩
  let : μ.IsAddHaarMeasure := infiniteLocalAdditiveTamagawaMeasure_haar F w
  have hden (x : w.Completion) : 0 < max (d x) (1 / 2) :=
    lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hcont : Continuous g := ((Complex.continuous_re.comp (schwartzBruhat_continuous f)).comp
    continuous_ofAdd).div (hd.max continuous_const) (fun x ↦ (hden x).ne')
  have hgcs : HasCompactSupport g := by
    simp only [g, div_eq_mul_inv]
    exact ((hc.comp_homeomorph
    (Homeomorph.refl w.Completion : w.Completion ≃ₜ Multiplicative w.Completion)).comp_left
      Complex.zero_re).mul_right
  have hB := hcont.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := μ) hgcs
    (fun x ↦ div_nonneg (hf _).2 (hden x).le) (x := 1)
    (by change (f (Multiplicative.ofAdd 1)).re / max (d 1) (1 / 2) ≠ 0; rw [hf₁, hd₁]; norm_num)
  refine ⟨f, ∫ x, g x ∂μ, hout 0 (by rw [hd₀]; norm_num), hB, ?_⟩
  filter_upwards [(eventually_lt_nhds (show (0 : ℝ) < 1 / 2 by norm_num)).filter_mono
    nhdsWithin_le_nhds] with ε hε
  rw [← integral_indicator (measurableSet_le measurable_const hd.measurable),
    ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : 1 / 2 < d x
  · rw [indicator_of_mem (show ε ≤ d x from (hε.trans hx).le)]
    simp only [g, max_eq_left hx.le, Complex.ofReal_div]
    rw [← (hf _).1]
  · have hz := hout x (le_of_not_gt hx)
    simp [indicator_apply, hz, g]

/-- Paper: Proposition B.4.3.2(1), Equation (B.4.3.13), p. 619. At the rational
real place use a nonnegative test supported away from zero and equal to one at
one. Its positive cutoff integral detects the factor of two. -/
theorem Printed.realLogFourier_finitePart_false : ¬ Printed.realLogFourier_finitePart := by
  intro h
  let w := Rat.infinitePlace
  obtain ⟨f, B, h0, hB, hcut⟩ := printed_arch_cutoff_test w (fun x ↦ ‖x‖) continuous_norm
    norm_zero norm_one
  obtain ⟨A, hA, he⟩ := h ℚ w Rat.isReal_infinitePlace f
  have hcorr := (RiemannMasullo.realLogFourier_finitePart w Rat.isReal_infinitePlace f).2.2
  simp only [h0, mul_zero, zero_mul, add_zero, sub_zero] at hA he hcorr
  have hAB := tendsto_nhds_unique hA (Tendsto.congr' (EventuallyEq.symm hcut) tendsto_const_nhds)
  have hAC := tendsto_nhds_unique hA hcorr
  change A = -2 * archLogPairing(ℚ, w, f) at hAC
  have hAz : A = 0 := by linear_combination -hAC + 2 * he
  exact (Complex.ofReal_ne_zero.mpr hB.ne') (hAB.symm.trans hAz)

/-- Paper: Proposition B.4.3.2(2), Equation (B.4.3.14), p. 619. As printed:
the complex Fourier pairing is minus the full squared-modulus cutoff limit minus
four pi times the logarithmic constant times the value at zero. The additive
measure is twice planar Lebesgue measure. See `complexLogFourier_finitePart` and ERRATA F41. -/
def Printed.complexLogFourier_finitePart : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (w : InfinitePlace F), w.IsComplex →
    ∀ f : 𝒮ₐ(w.Completion), ∃ A : ℂ,
      Tendsto (fun ε : ℝ ↦
        (∫ x in {x : w.Completion | ε ≤ ‖x‖ ^ 2},
          addTest(f) x / ((‖x‖ ^ 2 : ℝ) : ℂ) ∂ν∞(F, w)) +
          (2 * Real.pi : ℝ) * addTest(f) 0 * (Real.log ε : ℂ)) (𝓝[>] 0) (𝓝 A) ∧
      archLogPairing(F, w, f) = -A - (4 * Real.pi * eulerLogConstant : ℝ) * addTest(f) 0

/-- Paper: Proposition B.4.3.2(2), Equation (B.4.3.14), p. 619. At a complex
place of the fourth cyclotomic field, a nonnegative test supported away from zero
and equal to one at one has a positive cutoff integral. This detects the factor
of `2π`. -/
theorem Printed.complexLogFourier_finitePart_false :
    ¬ Printed.complexLogFourier_finitePart := by
  intro h
  obtain ⟨F, _, _, w, hw⟩ := printed_complex_place
  obtain ⟨f, B, h0, hB, hcut⟩ := printed_arch_cutoff_test w (fun x ↦ ‖x‖ ^ 2)
    (continuous_norm.pow 2) (by simp) (by simp)
  obtain ⟨A, hA, he⟩ := h F w hw f
  have hcorr := (RiemannMasullo.complexLogFourier_finitePart w hw f).2.2
  simp only [h0, mul_zero, zero_mul, add_zero, sub_zero] at hA he hcorr
  have hAB := tendsto_nhds_unique hA (Tendsto.congr' (EventuallyEq.symm hcut) tendsto_const_nhds)
  have hAC := tendsto_nhds_unique hA hcorr
  change A = -((2 * Real.pi : ℝ) : ℂ) * archLogPairing(F, w, f) at hAC
  rw [he, neg_mul_neg] at hAC
  have hne : ((2 * Real.pi : ℝ) : ℂ) ≠ 1 := by
    norm_cast
    linarith [Real.pi_gt_three]
  have hAz : A = 0 := by
    by_contra ha
    exact hne (mul_right_cancel₀ ha (hAC.symm.trans (one_mul A).symm))
  exact (Complex.ofReal_ne_zero.mpr hB.ne') (hAB.symm.trans hAz)

/-- Paper: Lemma B.4.4.3, Equation (B.4.4.6), p. 620. As printed: on tests
vanishing at one, the principal value is minus the integer-unit mass times the
stated positive density paired with the inverse-square-root weighted test.
This substitutes the printed restriction of the distribution into the equation,
where the weighted test also vanishes at one. See
`existsUnique_finiteWeilFourierDistribution` and ERRATA F42. -/
def Printed.finiteWeilPrincipalValue_positiveDensity : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (v : Primes(F))
    (f : 𝒟((v.adicCompletion F)ˣ)), f.val 1 = 0 →
      let V := (finiteLocalMultiplicativeTamagawaMeasure F v (v.adicCompletionIntegers F).units).toReal
      let g := Function.extend Units.val (f.val : (v.adicCompletion F)ˣ → ℂ) (fun _ ↦ 0)
      finiteConnesWeilPrincipalValue v 1 f =
        -(V : ℂ) * ((q(v) / (q(v) - 1) : ℝ) : ℂ) *
          ∫ x, g x / (Real.sqrt ‖x‖ : ℂ) / (‖1 - x‖ : ℂ) ∂ν𝔭(F, v)

/-- Paper: Lemma B.4.4.3, Equation (B.4.4.6), p. 620. At a finite rational
place take a nonnegative test supported on nonzero elements of absolute value less than one
and equal to one at a uniformizer. The principal value is positive, whereas the
printed integral with its sign is nonpositive. -/
theorem Printed.finiteWeilPrincipalValue_positiveDensity_false :
    ¬ Printed.finiteWeilPrincipalValue_positiveDensity := by
  intro h
  obtain ⟨v, _, _⟩ := printedPrimePower_witness
  let K := v.adicCompletion ℚ
  let μ := finiteLocalMultiplicativeTamagawaMeasure ℚ v
  let : BorelSpace Kˣ := ⟨rfl⟩
  let : μ.IsHaarMeasure := finiteLocalMultiplicativeTamagawaMeasure_haar ℚ v
  obtain ⟨π, hπ⟩ := (Valued.v : Valuation K (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
  let u₀ := Units.mk0 (π : K) hπ.ne_zero
  let U : Set Kˣ := {u | ‖u.val‖ < 1}
  have hU : IsOpen U := isOpen_lt (continuous_norm.comp Units.continuous_val) continuous_const
  have hu : u₀ ∈ U := Valued.toNormedField.norm_lt_one_iff.mpr hπ.val_lt_one
  obtain ⟨f, hc, hs, hf₀, hf⟩ := printed_nonnegative_test hU hu
  let b : 𝒟(Kˣ) := ⟨f.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth f), hc⟩
  have hb : b.val 1 = 0 := image_eq_zero_of_notMem_tsupport (fun hm ↦
    (show (1 : Kˣ) ∉ U by simp [U]) (hs hm))
  have he := h ℚ v b hb
  obtain ⟨hi, hp⟩ := finiteConnesWeilPrincipalValue_of_apply_one_zero v b hb
  let k (u : Kˣ) := (f u).re * Real.sqrt ‖u.val‖ / ‖1 - u.val‖
  have hk (u : Kˣ) : b.val u * (Real.sqrt ‖u.val‖ : ℂ) / (‖1 - u.val‖ : ℂ) = (k u : ℂ) := by
    change f u * _ / _ = _
    rw [(hf u).1]
    push_cast [k]
    simp
  have hint : Integrable k μ := by
    simp_rw [hk] at hi
    exact hi.re
  have hpos : 0 < ∫ u, k u ∂μ := by
    apply (integral_pos_iff_support_of_nonneg (fun u ↦ div_nonneg
      (mul_nonneg (hf u).2 (Real.sqrt_nonneg _)) (norm_nonneg _)) hint).mpr
    let W := U ∩ {u : Kˣ | 0 < (f u).re}
    have hW : IsOpen W := hU.inter (isOpen_lt continuous_const
      (Complex.continuous_re.comp (schwartzBruhat_continuous f)))
    refine (hW.measure_pos μ ⟨u₀, hu, by simp [hf₀]⟩).trans_le (measure_mono ?_)
    intro u hwu
    have hne : (1 : K) ≠ u.val := by
      intro h1
      have hlt := hwu.1
      change ‖u.val‖ < 1 at hlt
      simp [← h1] at hlt
    exact (div_pos (mul_pos hwu.2 (Real.sqrt_pos.mpr (norm_pos_iff.mpr u.ne_zero)))
      (norm_pos_iff.mpr (sub_ne_zero.mpr hne))).ne'
  let g := Function.extend Units.val (b.val : Kˣ → ℂ) (fun _ ↦ 0)
  have hg (x : K) : g x = ((g x).re : ℂ) ∧ 0 ≤ (g x).re := by
    by_cases hx : x = 0
    · subst x
      have hgz : g 0 = 0 := Function.extend_apply' _ _ _ (by simp)
      simp [hgz]
    · have hext : g x = f (Units.mk0 x hx) := Units.val_injective.extend_apply _ _ (Units.mk0 x hx)
      rw [hext]
      exact hf _
  let j (x : K) := (g x).re / Real.sqrt ‖x‖ / ‖1 - x‖
  have hj (x : K) : g x / (Real.sqrt ‖x‖ : ℂ) / (‖1 - x‖ : ℂ) = (j x : ℂ) := by
    simp only [j, Complex.ofReal_div, ← (hg x).1]
  have hnonneg : 0 ≤ ∫ x, j x ∂ν𝔭(ℚ, v) :=
    integral_nonneg fun x ↦ div_nonneg (div_nonneg (hg x).2 (Real.sqrt_nonneg _)) (norm_nonneg _)
  let V := (μ (v.adicCompletionIntegers ℚ).units).toReal
  change finiteConnesWeilPrincipalValue v 1 b =
    -(V : ℂ) * ((q(v) / (q(v) - 1) : ℝ) : ℂ) *
      (∫ x, g x / (Real.sqrt ‖x‖ : ℂ) / (‖1 - x‖ : ℂ) ∂ν𝔭(ℚ, v)) at he
  have hp' : finiteConnesWeilPrincipalValue v 1 b = ((∫ u, k u ∂μ : ℝ) : ℂ) :=
    hp.trans ((integral_congr_ae (ae_of_all μ hk)).trans integral_complex_ofReal)
  have hj' : (∫ x, g x / (Real.sqrt ‖x‖ : ℂ) / (‖1 - x‖ : ℂ) ∂ν𝔭(ℚ, v)) =
      ((∫ x, j x ∂ν𝔭(ℚ, v) : ℝ) : ℂ) :=
    (integral_congr_ae (ae_of_all _ hj)).trans integral_complex_ofReal
  rw [hp', hj'] at he
  have hq : 1 < q(v) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v
  have hv : 0 ≤ V := ENNReal.toReal_nonneg
  have he' := congrArg Complex.re he
  simp only [← Complex.ofReal_neg, ← Complex.ofReal_mul, Complex.ofReal_re] at he'
  rw [he'] at hpos
  exact hpos.not_ge (mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hv) (div_nonneg (zero_le_one.trans hq.le)
      (sub_nonneg.mpr hq.le))) hnonneg)

local notation "archUnitMass(" w ")" => (if InfinitePlace.IsReal w then (2 : ℝ) else 2 * Real.pi)

/-- Paper: Theorem B.4.4.7, Equation (B.4.4.16), p. 623. The pointwise
absolutely convergent identity on every idelic test includes one term for each
zero quasi-character and divides the archimedean principal values by the local
unit masses. A norm section indexes each quasi-character exactly once. This
isolates the scalar identity from the additional assertion of convergence in the
strong dual. See `idelicExplicitFormula` and ERRATA F43. -/
def Printed.idelicExplicitFormula_archNormalization : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (τ : ℝ≥0ˣ →ₜ* C[F]),
    RightInverse τ (ideleClassNorm F) → ∀ f : 𝒟(C[F]),
      let zeros := {z : {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1} × ℂ //
        0 < ord(explicitFormulaCompletedHeckeL z.1.val) z.2}
      let V : ℂ := (normOneIdeleClassTamagawaMeasure F univ).toReal
      let weight := fun (g : C[F]) (a : ℂ) ↦ (((ideleClassNorm F g).val : ℝ) : ℂ) ^ a
      let moment := fun (a : ℂ) ↦
        (∫ g, f.val g * weight g a ∂ideleClassTamagawaMeasure F) / V
      ∃ (arch : (w : InfinitePlace F) → 𝒟(w.Completionˣ))
        (finite : (v : Primes(F)) → 𝒟((v.adicCompletion F)ˣ)) (finiteSum : ℂ),
        (∀ w u, (arch w).val u = f.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
        (∀ v u, (finite v).val u = f.val (IdeleClassGroup.ofAdicCompletion (𝓞 F) F v u)) ∧
        HasSum (fun v : Primes(F) ↦
          let μ := finiteLocalMultiplicativeTamagawaMeasure F v
          let mass := (μ (v.adicCompletionIntegers F).units).toReal
          (Real.log q(v) / mass : ℝ) * finiteConnesWeilPrincipalValue v 1 (finite v)) finiteSum ∧
        HasSum (fun z : zeros ↦
          (∫ g, f.val g * ideleClassNormTwist z.val.1.val z.val.2 g * weight g (-1 / 2)
            ∂ideleClassTamagawaMeasure F) / V)
          (moment (-1 / 2) + moment (1 / 2) -
            (∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (arch w) /
              (archUnitMass(w) : ℂ)) - finiteSum)

local notation "sectionCharts(" F ", " τ ")" =>
  {χ : U[F] // ∀ t : ℝ≥0ˣ, χ (τ t) = 1}
local notation "sectionZeros(" F ", " τ ")" =>
  {z : sectionCharts(F, τ) × ℂ // 0 < ord(explicitFormulaCompletedHeckeL z.1.val) z.2}
local notation "sectionSample(" F ", " f ", " z ")" =>
  ((∫ g : C[F], (f).val g * ideleClassNormTwist (z).val.1.val (z).val.2 g *
    ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ (-1 / 2 : ℂ)) ∂ideleClassTamagawaMeasure F) /
    ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ))
local notation "sectionExcess(" F ", " f ", " z ")" =>
  ((1 - (ord(explicitFormulaCompletedHeckeL (z).val.1.val) (z).val.2 : ℂ)) * sectionSample(F, f, z))

private theorem printed_test_ext {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] {u v : 𝒟(G)}
    (h : ∀ x, u.val x = v.val x) : u = v := Subtype.ext (funext h)

private def printed_arch_pv {F : Type} [Field F] [NumberField F]
    (w : InfinitePlace F) (u : 𝒟(w.Completionˣ)) : ℂ :=
  (infiniteConnesWeilPrincipalValue (F := F) w).toLinearMap.toFun u

private theorem printed_sum_value {ι : Type*} {f : ι → ℂ} {x y : ℂ}
    (h : HasSum f x) (he : x = y) : HasSum f y := he ▸ h

-- Evaluate the strong-dual identity on the same test as the printed identity.
-- Their difference retains exactly the excess zero multiplicities and the local mass factors.
private theorem printed_arch_difference_general {F : Type} [Field F] [NumberField F]
    (h : Printed.idelicExplicitFormula_archNormalization) (τ : ℝ≥0ˣ →ₜ* C[F])
    (hτ : RightInverse τ (ideleClassNorm F)) (f : 𝒟(C[F])) :
    ∃ a : (w : InfinitePlace F) → 𝒟(w.Completionˣ),
      (∀ w u, (a w).val u = f.val (IdeleClassGroup.ofCompletion (𝓞 F) F w u)) ∧
      HasSum (fun z : sectionZeros(F, τ) ↦ sectionExcess(F, f, z))
        (∑ w : InfinitePlace F, (printed_arch_pv w (a w) -
          printed_arch_pv w (a w) / (if w.IsReal then ((2 : ℝ) : ℂ) else 2 * (Real.pi : ℂ)))) := by
  obtain ⟨S, P, A, V, hS, hP, hA, hV, _, _, hVs, hSs⟩ := idelicExplicitFormula (F := F) τ hτ
  obtain ⟨a, v, b, ha, hv, hb, hZ⟩ := h F τ hτ f
  let ev := ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) f
  choose u hu hAc using fun w ↦ hA w f
  have heA : u = a := funext fun w ↦ printed_test_ext (G := w.Completionˣ)
    (fun x ↦ (hu w x).trans (ha w x).symm)
  subst a
  choose d hd hVc using fun i ↦ hV i f
  have heV : d = v := funext fun i ↦ printed_test_ext (G := (i.adicCompletion F)ˣ)
    (fun x ↦ (hd i x).trans (hv i x).symm)
  subst v
  have hFc : ev (∑' i, V i) = b :=
    (ev.hasSum hVs.hasSum).unique (hb.congr_fun fun i ↦ hVc i)
  let mass := ((normOneIdeleClassTamagawaMeasure F univ).toReal : ℂ)
  let M (s : ℂ) := (∫ g : C[F], f.val g * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ s)
    ∂ideleClassTamagawaMeasure F) / mass
  let B (w : InfinitePlace F) := printed_arch_pv w (u w)
  let D (w : InfinitePlace F) := B w / (if w.IsReal then ((2 : ℝ) : ℂ) else 2 * (Real.pi : ℂ))
  have hp : ev P = M (-1 / 2) + M (1 / 2) := (hP f).trans (add_div _ _ _)
  have hab : ev (∑ w, A w) = ∑ w, B w :=
    (map_sum ev A Finset.univ).trans (Finset.sum_congr rfl fun w _ ↦ hAc w)
  have hval : ev (P - (∑ w, A w) - (∑' i, V i)) =
      M (-1 / 2) + M (1 / 2) - (∑ w, B w) - b :=
    (map_sub ev _ _).trans (congrArg₂ (· - ·)
      ((map_sub ev _ _).trans (congrArg₂ (· - ·) hp hab)) hFc)
  have hZ' : HasSum (fun z : sectionZeros(F, τ) ↦ sectionSample(F, f, z))
      (M (-1 / 2) + M (1 / 2) - (∑ w, D w) - b) := hZ
  have hR := hZ'.sub (printed_sum_value (ev.hasSum hSs) hval)
  have hcanc (m n a d c : ℂ) : (m + n - d - c) - (m + n - a - c) = a - d := by ring
  have hlim := (hcanc (M (-1 / 2)) (M (1 / 2)) (∑ w, B w) (∑ w, D w) b).trans
    (Finset.sum_sub_distrib (f := B) (g := D)).symm
  refine ⟨u, ha, (printed_sum_value hR hlim).congr_fun ?_⟩
  intro z
  change _ = sectionSample(F, f, z) - (S z).toLinearMap.toFun f
  have hv (m i c : ℂ) : (1 - m) * (i / c) = i / c - m / c * i := by ring
  exact (hv _ _ _).trans (congrArg (sectionSample(F, f, z) - ·) (hS z f).symm)

private theorem printed_halfplane_connected (E : Set ℂ) (hc : E.Countable) :
    IsPreconnected ({z : ℂ | 0 < z.re} \ E) := by
  let φ (z : ℂ) : ℂ := ⟨Real.exp z.re, z.im⟩
  have hφ : Continuous φ := Complex.equivRealProdCLM.symm.continuous.comp
    ((Real.continuous_exp.comp Complex.continuous_re).prodMk Complex.continuous_im)
  have hinj : Injective φ := by
    intro x y h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    exact Complex.ext (Real.exp_injective hr) hi
  have he : φ '' (φ ⁻¹' E)ᶜ = {z : ℂ | 0 < z.re} \ E := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Real.exp_pos _, hx⟩
    · rintro ⟨hz, hn⟩
      let x : ℂ := ⟨Real.log z.re, z.im⟩
      have hx : φ x = z := Complex.ext (Real.exp_log hz) rfl
      exact ⟨x, fun h ↦ hn (hx ▸ h), hx⟩
  rw [← he]
  exact ((hc.preimage hinj).isConnected_compl_of_one_lt_rank (by
    rw [Complex.rank_real_complex]; norm_num)).isPreconnected.image φ hφ.continuousOn

private theorem printed_cauchy_analytic {ι : Type*} (w b : ι → ℂ) (hb : Summable (fun i ↦ ‖b i‖))
    {E : Set ℂ} (hE : IsClosed E) (hw : ∀ i, w i ∈ E) :
    AnalyticOnNhd ℂ (fun z ↦ ∑' i, b i / (z - w i)) Eᶜ := by
  intro z hz
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hE.isOpen_compl.mem_nhds hz)
  let U := Metric.ball z (r / 2)
  have hu : IsOpen U := Metric.isOpen_ball
  have hsep (i : ι) (v : ℂ) (hv : v ∈ U) : r / 2 ≤ ‖v - w i‖ := by
    have hout : ¬ dist (w i) z < r := fun h ↦ hball h (hw i)
    have ht := dist_triangle (w i) v z
    rw [dist_comm (w i) v, dist_eq_norm v (w i)] at ht
    exact le_of_lt (by linarith [show dist v z < r / 2 from hv, le_of_not_gt hout])
  have hD := Complex.differentiableOn_tsum_of_summable_norm (hb.div_const (r / 2))
    (F := fun i v ↦ b i / (v - w i)) (U := U)
    (fun i ↦ (differentiableOn_const (b i)).div (differentiableOn_id.sub_const _) (fun v hv ↦
      norm_ne_zero_iff.mp (lt_of_lt_of_le (half_pos hr) (hsep i v hv)).ne')) hu
    (fun i v hv ↦ by
      rw [norm_div]
      exact div_le_div_of_nonneg_left (norm_nonneg _) (half_pos hr) (hsep i v hv))
  exact hD.analyticAt (hu.mem_nhds (Metric.mem_ball_self (half_pos hr)))

private def printed_laplace (S : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), S t * Complex.exp (-z * t)

private theorem printed_laplace_analytic (S : ℝ → ℂ) (hS : Measurable S)
    (C : ℝ) (hC : ∀ t, 0 < t → ‖S t‖ ≤ C) :
    AnalyticOnNhd ℂ (printed_laplace S) {z | 0 < z.re} := by
  let H := {z : ℂ | 0 < z.re}
  have hH : IsOpen H := isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hH
  intro z hz
  let μ := volume.restrict (Ioi (0 : ℝ))
  let a := z.re / 2
  have ha : 0 < a := half_pos hz
  let U := {x : ℂ | a < x.re}
  have hU : U ∈ 𝓝 z := (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by exact half_lt_self (show 0 < z.re from hz))
  let F (x : ℂ) (t : ℝ) := S t * Complex.exp (-x * t)
  let D (x : ℂ) (t : ℝ) := F x t * (-(t : ℂ))
  have hM (x : ℂ) : Measurable (F x) := hS.mul (by fun_prop)
  have hn (x : ℂ) (t : ℝ) : ‖F x t‖ = ‖S t‖ * Real.exp (-x.re * t) := by
    simp [F, Complex.norm_exp]
  have hInt : Integrable (F z) μ := by
    apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos (show 0 < z.re from hz)) 0).const_mul C).mono'
      (hM _).aestronglyMeasurable
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
    rw [hn]
    exact mul_le_mul_of_nonneg_right (hC _ ht) (Real.exp_pos _).le
  have hDI : Integrable (fun t : ℝ ↦ C * (t * Real.exp (-a * t))) μ := by
    have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) (by norm_num) ha
    simpa [Real.rpow_one] using hi.const_mul C
  have hB : ∀ᵐ t ∂μ, ∀ x ∈ U, ‖D x t‖ ≤ C * (t * Real.exp (-a * t)) := by
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht x hx ↦ ?_
    rw [show ‖D x t‖ = ‖F x t‖ * t by simp [D, abs_of_pos (show 0 < t from ht)], hn,
      mul_comm t, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ ht.le
    exact mul_le_mul (hC _ ht) (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
      (neg_le_neg (show a < x.re from hx).le) ht.le)) (Real.exp_pos _).le ((norm_nonneg _).trans (hC _ ht))
  have hD (t : ℝ) (x : ℂ) : HasDerivAt (fun y ↦ F y t) (D x t) x := by
    simpa [F, D, mul_assoc] using (((hasDerivAt_id x).neg.mul_const (t : ℂ)).cexp.const_mul (S t))
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    (Eventually.of_forall fun x ↦ (hM x).aestronglyMeasurable) hInt
    ((hM z).mul (show Measurable (fun t : ℝ ↦ -(t : ℂ)) by fun_prop)).aestronglyMeasurable
    hB hDI (Eventually.of_forall fun t x _ ↦ hD t x)).2.differentiableAt.differentiableWithinAt

private theorem printed_laplace_series {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (hb : Summable (fun i ↦ ‖b i‖)) (hw : ∀ i, (w i).re ≤ 1)
    {z : ℂ} (hz : 1 < z.re) :
    printed_laplace (fun t ↦ ∑' i, b i * Complex.exp (w i * t)) z =
      ∑' i, b i / (z - w i) := by
  let F (i : ι) (t : ℝ) := b i * Complex.exp ((w i - z) * t)
  have hn (i : ι) : (w i - z).re < 0 := by rw [Complex.sub_re]; linarith [hw i]
  have hi (i : ι) : IntegrableOn (F i) (Ioi 0) :=
    (integrableOn_exp_mul_complex_Ioi (hn i) 0).const_mul _
  have he (i : ι) : (∫ t in Ioi (0 : ℝ), F i t) = b i / (z - w i) := by
    rw [show (∫ t in Ioi (0 : ℝ), F i t) = b i * ∫ t in Ioi (0 : ℝ),
      Complex.exp ((w i - z) * t) from integral_const_mul _ _, integral_exp_mul_complex_Ioi (hn i)]
    simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    rw [show w i - z = -(z - w i) by ring, neg_div_neg_eq, one_div, div_eq_mul_inv]
  have hsum : Summable (fun i ↦ ∫ t in Ioi (0 : ℝ), ‖F i t‖) := by
    apply (hb.mul_right (∫ t in Ioi (0 : ℝ), Real.exp ((1 - z.re) * t))).of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _)
    intro i
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hi i).norm
      ((integrableOn_exp_mul_Ioi (sub_neg.mpr hz) 0).const_mul _) measurableSet_Ioi
    intro t ht
    rw [show ‖F i t‖ = ‖b i‖ * Real.exp (((w i).re - z.re) * t) by
      simp [F, Complex.norm_exp]]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_right (sub_le_sub_right (hw i) _) ht.le)) (norm_nonneg _)
  have hs := integral_tsum_of_summable_integral_norm hi hsum
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∑' i, F i t := by
      apply integral_congr_ae
      filter_upwards with t
      rw [← tsum_mul_right]
      apply tsum_congr
      intro i
      rw [mul_assoc, ← Complex.exp_add, show w i * (t : ℂ) + -z * t = (w i - z) * t by ring]
    _ = _ := hs.symm.trans (tsum_congr he)

private theorem printed_no_bounded_positive_series {ι : Type*} [Countable ι] (w b : ι → ℂ)
    (hb : Summable (fun i ↦ ‖b i‖)) (hw : ∀ i, (w i).re ≤ 1)
    {E : Set ℂ} (hE : IsClosed E) (hc : E.Countable) (hz : (0 : ℂ) ∉ E) (hmem : ∀ i, w i ∈ E)
    (c C : ℝ) (hc₀ : 0 < c)
    (hpos : ∀ t : ℝ, 0 < t → c ≤ (∑' i, b i * Complex.exp (w i * t)).re)
    (hbdd : ∀ t : ℝ, 0 < t → ‖∑' i, b i * Complex.exp (w i * t)‖ ≤ C) : False := by
  let S (t : ℝ) := ∑' i, b i * Complex.exp (w i * t)
  let A (z : ℂ) := ∑' i, b i / (z - w i)
  have hM : Measurable S := Measurable.tsum fun i ↦ (by fun_prop : Measurable (fun t : ℝ ↦
    b i * Complex.exp (w i * t)))
  have hA := printed_cauchy_analytic w b hb hE hmem
  let U := {z : ℂ | 0 < z.re} \ E
  have hL := printed_laplace_analytic S hM C hbdd
  have hco := printed_halfplane_connected E hc
  obtain ⟨z, hzR, hzE⟩ : ∃ z : ℂ, 1 < z.re ∧ z ∉ E := by
    obtain ⟨z, hz, hzE⟩ := hc.dense_compl ℝ |>.inter_open_nonempty _
      (isOpen_lt continuous_const Complex.continuous_re)
      (show ({z : ℂ | 1 < z.re} : Set ℂ).Nonempty from ⟨2, by norm_num⟩)
    exact ⟨z, hz, hzE⟩
  -- On Re z > 1 the Laplace integral can be taken term by term. Continue the
  -- equality along the right half-plane with the possible poles removed.
  have hEq : EqOn (printed_laplace S) A U := by
    apply (hL.mono sdiff_subset).eqOn_of_preconnected_of_eventuallyEq
      (hA.mono (fun _ hx ↦ hx.2)) hco (z₀ := z) ⟨zero_lt_one.trans hzR, hzE⟩
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hzR] with a ha
    exact printed_laplace_series w b hb hw ha
  have hcont : ContinuousAt A 0 := (hA 0 hz).continuousAt
  have hzero : Tendsto (fun x : ℝ ↦ x * (A x).re) (𝓝[>] 0) (𝓝 0) := by
    have ho : Tendsto Complex.ofReal (𝓝 (0 : ℝ)) (𝓝 (0 : ℂ)) := by simpa using Complex.continuous_ofReal.tendsto (0 : ℝ)
    have hh := Complex.continuous_re.continuousAt.tendsto.comp (hcont.tendsto.comp ho)
    simpa using (tendsto_id.mul hh).mono_left nhdsWithin_le_nhds
  apply hc₀.not_ge
  apply ge_of_tendsto hzero
  have hnh := (hE.isOpen_compl.preimage Complex.continuous_ofReal).mem_nhds
    (show (0 : ℝ) ∈ Complex.ofReal ⁻¹' Eᶜ by simpa using hz)
  filter_upwards [self_mem_nhdsWithin, (show Complex.ofReal ⁻¹' Eᶜ ∈ 𝓝[>] 0 from nhdsWithin_le_nhds hnh)] with x hx hxE
  have hx₀ : 0 < x := hx
  rw [← hEq ⟨hx₀, hxE⟩]
  let μ := volume.restrict (Ioi (0 : ℝ))
  let F (t : ℝ) := S t * Complex.exp (-(x : ℂ) * t)
  have hF (t : ℝ) : F t = S t * (Real.exp (-x * t) : ℂ) := by simp [F, Complex.ofReal_exp]
  have hi : Integrable F μ := by
    apply ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hx₀) 0).const_mul C).mono'
      (hM.mul (by fun_prop)).aestronglyMeasurable
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht ↦ ?_
    change ‖F t‖ ≤ C * Real.exp (-x * t)
    rw [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    exact mul_le_mul_of_nonneg_right (hbdd t ht) (Real.exp_pos _).le
  change c ≤ x * (∫ t, F t ∂μ).re
  rw [← (show (∫ t, (F t).re ∂μ) = (∫ t, F t ∂μ).re from integral_re hi), ← div_le_iff₀' hx₀]
  calc
    c / x = ∫ t in Ioi (0 : ℝ), c * Real.exp (-x * t) := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hx₀)]; simp [div_eq_mul_inv]
    _ ≤ _ := by
      apply setIntegral_mono_on ((integrableOn_exp_mul_Ioi (neg_neg_of_pos hx₀) 0).const_mul c)
        hi.re measurableSet_Ioi
      intro t ht
      change _ ≤ (F t).re
      rw [hF, Complex.re_mul_ofReal]
      exact mul_le_mul_of_nonneg_right (hpos t ht) (Real.exp_pos _).le

private theorem printed_real_kernel_bounds {K : Type} [NormedField K] [LocallyCompactSpace Kˣ]
    [MeasurableSpace Kˣ] [BorelSpace Kˣ] (μ : Measure Kˣ) [μ.IsHaarMeasure]
    (v : Kˣ → ℝ) (hv : Continuous v) (hc : HasCompactSupport v) (hn : ∀ x, 0 ≤ v x)
    (hp : ∃ x, v x ≠ 0) (hs : ∀ x, v x ≠ 0 → 2 < ‖x.val‖) :
    ∃ B : ℝ, 0 < B ∧ ∀ a : Kˣ, 1 ≤ ‖a.val‖ →
      let V := (∫ y : Kˣ, v y * Real.sqrt ‖y.val‖ / ‖(a⁻¹).val - y.val‖ ∂μ)
      B / 2 ≤ V ∧ V ≤ 2 * B := by
  -- This fixed positive integrand is comparable to every translated kernel on the support.
  let g (y : Kˣ) := v y / Real.sqrt ‖y.val‖
  have hq (y : Kˣ) : 0 < Real.sqrt ‖y.val‖ := Real.sqrt_pos.mpr (norm_pos_iff.mpr y.ne_zero)
  have hgc : Continuous g := hv.div (Real.continuous_sqrt.comp Units.continuous_val.norm)
    (fun y ↦ (hq y).ne')
  have hgs : HasCompactSupport g := by
    apply HasCompactSupport.intro hc
    intro y hy
    simp [g, image_eq_zero_of_notMem_tsupport hy]
  have hgi := hgc.integrable_of_hasCompactSupport (μ := μ) hgs
  obtain ⟨x, hx⟩ := hp
  have hB := hgc.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := μ) hgs
    (fun y ↦ div_nonneg (hn y) (hq y).le) (x := x) (div_ne_zero hx (hq x).ne')
  refine ⟨_, hB, fun a ha ↦ ?_⟩
  let k (y : Kˣ) := v y * Real.sqrt ‖y.val‖ / ‖(a⁻¹).val - y.val‖
  have hai : ‖(a⁻¹).val‖ ≤ 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv]
    exact inv_le_one_of_one_le₀ ha
  have hb (y : Kˣ) : g y / 2 ≤ k y ∧ k y ≤ 2 * g y := by
    by_cases hy : v y = 0
    · simp [g, k, hy]
    have hy' := hs y hy
    have hlow := norm_sub_norm_le y.val (a⁻¹).val
    rw [norm_sub_rev] at hlow
    have hhigh := norm_sub_le (a⁻¹).val y.val
    have hden : 0 < ‖(a⁻¹).val - y.val‖ := by linarith
    have hq₂ := Real.sq_sqrt (norm_nonneg y.val)
    have hlow' : ‖y.val‖ ≤ 2 * ‖(a⁻¹).val - y.val‖ := by linarith
    have hhigh' : ‖(a⁻¹).val - y.val‖ ≤ 2 * ‖y.val‖ := by linarith
    dsimp only [g, k]
    have h := hq y
    constructor
    · rw [div_div, div_le_div_iff₀ (mul_pos h zero_lt_two) hden]
      calc
        _ ≤ v y * (2 * ‖y.val‖) := mul_le_mul_of_nonneg_left hhigh' (hn y)
        _ = _ := by rw [← hq₂, Real.sqrt_sq (hq y).le]; ring
    · rw [← mul_div_assoc, div_le_div_iff₀ hden h]
      calc
        _ = v y * ‖y.val‖ := by rw [← hq₂, Real.sqrt_sq (hq y).le]; ring
        _ ≤ v y * (2 * ‖(a⁻¹).val - y.val‖) := mul_le_mul_of_nonneg_left hlow' (hn y)
        _ = _ := by ring
  have hk : Integrable k μ := by
    refine (hgi.const_mul 2).mono' (show Measurable k by dsimp [k]; fun_prop).aestronglyMeasurable ?_
    refine ae_of_all μ fun y ↦ ?_
    rw [Real.norm_of_nonneg (show 0 ≤ k y from div_nonneg (mul_nonneg (hn y) (hq y).le) (norm_nonneg _))]
    exact (hb y).2
  constructor
  · rw [← integral_div]
    exact integral_mono (hgi.div_const 2) hk (fun y ↦ (hb y).1)
  · rw [← integral_const_mul]
    exact integral_mono hk (hgi.const_mul 2) (fun y ↦ (hb y).2)

private theorem printed_scaled_kernel {K : Type} [NormedField K] [MeasurableSpace Kˣ]
    [BorelSpace Kˣ] (μ : Measure Kˣ) [μ.IsHaarMeasure] (v : Kˣ → ℝ)
    (a : Kˣ) :
    (Real.sqrt ‖a.val‖ : ℂ) * (∫ x : Kˣ, (v (a⁻¹ * x) : ℂ) *
      (Real.sqrt ‖x.val‖ : ℂ) / (‖1 - x.val‖ : ℂ) ∂μ) =
    ((∫ y : Kˣ, v y * Real.sqrt ‖y.val‖ / ‖(a⁻¹).val - y.val‖ ∂μ : ℝ) : ℂ) := by
  rw [← integral_mul_left_eq_self (μ := μ) (fun x : Kˣ ↦ (v (a⁻¹ * x) : ℂ) *
    (Real.sqrt ‖x.val‖ : ℂ) / (‖1 - x.val‖ : ℂ)) a, ← integral_const_mul, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with y
  have ha := norm_pos_iff.mpr a.ne_zero
  have hden : ‖1 - (a * y).val‖ = ‖a.val‖ * ‖(a⁻¹).val - y.val‖ := by
    rw [← norm_mul, mul_sub, ← Units.val_mul, mul_inv_cancel, Units.val_one, Units.val_mul]
  rw [inv_mul_cancel_left, hden, Units.val_mul, norm_mul, Real.sqrt_mul (norm_nonneg _)]
  norm_cast
  field_simp [ha.ne']
  ring_nf
  rw [Real.sq_sqrt ha.le]
  ring

private theorem printed_radial_bump {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (m : G →* ℝ≥0ˣ) (hm : IsProperMap m) (x : G) (hx : 2 < ((m x).val : ℝ)) :
    ∃ f : SchwartzBruhat G, HasCompactSupport f.val ∧ f x = 1 ∧
      (∀ y, f y ≠ 0 → 2 < ((m y).val : ℝ)) ∧
      (∀ y, f y = ((f y).re : ℂ) ∧ 0 ≤ (f y).re) ∧
      ∀ y k, m k = 1 → f (k * y) = f y := by
  let k := m.ker
  have hk : IsCompact (k : Set G) := hm.isCompact_preimage isCompact_singleton
  let : IsClosed (k : Set G) := hk.isClosed
  let q := QuotientGroup.mk' k
  let p := QuotientGroup.kerLift m
  have hq : Topology.IsQuotientMap q := QuotientGroup.isQuotientMap_mk _
  have hp : Continuous p := hq.continuous_iff.mpr hm.continuous
  let r (u : G ⧸ k) : ℝ := (p u).val
  have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp hp)
  obtain ⟨v, hv, hU, h₁, hvR⟩ := printed_nonnegative_test
    (U := {u | 2 < r u}) (x := q x) (isOpen_lt continuous_const hr) hx
  obtain ⟨P, hP⟩ := continuous_schwartzBruhat_compactQuotient_pullback k hk
  have hc : HasCompactSupport (P v).val := by
    apply HasCompactSupport.intro (hm.isCompact_preimage (hv.image hp))
    intro y hy
    rw [show (P v).val y = v (q y) from hP _ _]
    apply image_eq_zero_of_notMem_tsupport
    exact fun h ↦ hy ⟨q y, h, rfl⟩
  refine ⟨P v, hc, (hP _ _).trans h₁, fun y hy ↦ ?_, fun y ↦ ?_, fun y u hu ↦ ?_⟩
  · rw [hP v y] at hy
    exact hU (subset_tsupport _ hy)
  · rw [hP v y]
    exact hvR _
  · have he : q (u * y) = q y := by
      rw [map_mul, show q u = 1 from (QuotientGroup.eq_one_iff u).mpr hu, one_mul]
    exact (hP v (u * y)).trans ((congrArg v.val he).trans (hP v y).symm)

private theorem printed_bruhat_translate {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
    (v : SchwartzBruhat G) (hv : HasCompactSupport v.val) (a : G) :
    ∃ f : 𝒟(G), ∀ g, f.val g = v (a⁻¹ * g) := by
  let u : SchwartzBruhat G := ⟨_, schwartzBruhat_translate_mem a v⟩
  exact ⟨⟨u.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth u),
    hv.comp_homeomorph (Homeomorph.mulLeft a⁻¹)⟩, fun _ ↦ rfl⟩

private def printed_ratSection : ℝ≥0ˣ →ₜ* C[ℚ] :=
  ⟨(QuotientGroup.mk' _).comp (canonicalIdeleNormSection ℚ),
    continuous_quotient_mk'.comp (canonicalIdeleNormSection_continuous ℚ)⟩

private theorem printed_ratSection_spec : RightInverse printed_ratSection (ideleClassNorm ℚ) :=
  canonicalIdeleNormSection_rightInverse ℚ

local notation "ratChart" => {χ : U[ℚ] // ∀ t : ℝ≥0ˣ, χ (printed_ratSection t) = 1}
local notation "ratZeros" => {z : ratChart × ℂ // 0 < ord(explicitFormulaCompletedHeckeL z.1.val) z.2}
local notation "ratVol" => ((normOneIdeleClassTamagawaMeasure ℚ univ).toReal : ℂ)
local notation "ratWeight(" g ", " a ")" => ((((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ (a : ℂ))
local notation "ratInf" => Rat.infinitePlace
local notation "ratLoc" => IdeleClassGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace
local notation "ratSample(" f ", " z ")" =>
  ((∫ g : C[ℚ], (f).val g * ideleClassNormTwist (z).val.1.val (z).val.2 g *
    ratWeight(g, -1 / 2) ∂ideleClassTamagawaMeasure ℚ) / ratVol)
local notation "ratExcess(" f ", " z ")" =>
  ((1 - (ord(explicitFormulaCompletedHeckeL (z).val.1.val) (z).val.2 : ℂ)) * ratSample(f, z))

private def printed_chartWeight (z : ratZeros) : C[ℚ] →* ℂ :=
  (ideleClassNormTwist z.val.1.val z.val.2 * ideleClassNormTwist (1 : U[ℚ]) (-1 / 2)).toMonoidHom

private theorem printed_chartWeight_apply (z : ratZeros) (g : C[ℚ]) :
    printed_chartWeight z g = ideleClassNormTwist z.val.1.val z.val.2 g * ratWeight(g, -1 / 2) := by
  change ideleClassNormTwist z.val.1.val z.val.2 g * ((1 : ℂ) * ratWeight(g, -1 / 2)) = _
  rw [one_mul]

private def printed_sample (f : C[ℚ] → ℂ) (z : ratZeros) : ℂ :=
  (∫ g, f g * printed_chartWeight z g ∂ideleClassTamagawaMeasure ℚ) / ratVol

private theorem printed_sample_eq (f : 𝒟(C[ℚ])) (z : ratZeros) :
    printed_sample f.val z = ratSample(f, z) := by
  apply congrArg (· / ratVol)
  exact integral_congr_ae (ae_of_all _ (fun g ↦ by dsimp only; rw [printed_chartWeight_apply z g, mul_assoc]))

private theorem printed_sample_translate (f : C[ℚ] → ℂ) (a : C[ℚ]) (z : ratZeros) :
    printed_sample (fun g ↦ f (a⁻¹ * g)) z = printed_chartWeight z a * printed_sample f z := by
  let : MeasurableSpace C[ℚ] := borel _
  let : BorelSpace C[ℚ] := ⟨rfl⟩
  let μ := ideleClassTamagawaMeasure ℚ
  let : μ.IsHaarMeasure := (ideleClassTamagawaMeasure_isWeil (F := ℚ)).1
  change (∫ g, f (a⁻¹ * g) * printed_chartWeight z g ∂μ) / ratVol = _
  rw [← integral_mul_left_eq_self (μ := μ) (fun g ↦ f (a⁻¹ * g) * printed_chartWeight z g) a]
  have he (g : C[ℚ]) : f (a⁻¹ * (a * g)) * printed_chartWeight z (a * g) =
      printed_chartWeight z a * (f g * printed_chartWeight z g) := by
    rw [inv_mul_cancel_left, map_mul]; ring
  rw [integral_congr_ae (ae_of_all μ he), integral_const_mul]
  dsimp [printed_sample, μ]
  ring

-- Invariance under norm-one classes forces every nonzero Mellin sample into the trivial chart.
private theorem printed_chart_trivial {f : C[ℚ] → ℂ} {z : ratZeros}
    (hInv : ∀ y k, ideleClassNorm ℚ k = 1 → f (k * y) = f y)
    (hf : printed_sample f z ≠ 0) : z.val.1.val = 1 := by
  have hk (k : C[ℚ]) (hn : ideleClassNorm ℚ k = 1) : z.val.1.val k = 1 := by
    have hfun : (fun g ↦ f (k⁻¹ * g)) = f := funext fun g ↦
      hInv _ _ (by rw [map_inv, hn, inv_one])
    have he := printed_sample_translate f k z
    rw [hfun] at he
    have hc : printed_chartWeight z k = 1 :=
      mul_right_cancel₀ hf (he.symm.trans (one_mul _).symm)
    apply Subtype.ext
    rw [printed_chartWeight_apply] at hc
    change ((z.val.1.val k : Circle) : ℂ) * _ ^ z.val.2 * _ ^ _ = 1 at hc
    simpa [hn] using hc
  ext1 g
  let t := ideleClassNorm ℚ g
  have ht := printed_ratSection_spec t
  have hn : ideleClassNorm ℚ (g / printed_ratSection t) = 1 := by rw [map_div, ht]; exact div_self' _
  have he := hk _ hn
  rwa [map_div, z.val.1.property t, div_one] at he

private theorem printed_local_unit (t : ℝ) :
    ∃ a : Rat.infinitePlace.Completionˣ, ‖a.val‖ = Real.exp t := by
  let e := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let u := Units.mk0 (Real.exp t) (Real.exp_pos _).ne'
  refine ⟨Units.map e.symm.toMonoidHom u, ?_⟩
  change ‖e.symm (Real.exp t)‖ = Real.exp t
  exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace).symm.isometry.norm_map_of_map_zero
    (map_zero e.symm) (Real.exp t)).trans (Real.norm_of_nonneg (Real.exp_pos _).le)

private theorem printed_local_norm (a : Rat.infinitePlace.Completionˣ) :
    (((ideleClassNorm ℚ (ratLoc a)).val : ℝ≥0) : ℝ) = ‖a.val‖ := by
  rw [ideleClassNorm_ofCompletion, Rat.isReal_infinitePlace.mult_eq_one, pow_one]
  rfl

private theorem printed_chartWeight_exp {z : ratZeros} (hz : z.val.1.val = 1) {t : ℝ}
    (a : Rat.infinitePlace.Completionˣ) (ha : ‖a.val‖ = Real.exp t) :
    (Real.exp (t / 2) : ℂ) * printed_chartWeight z (ratLoc a) = Complex.exp (z.val.2 * t) := by
  rw [printed_chartWeight_apply]
  change _ * (((z.val.1.val (ratLoc a) : Circle) : ℂ) * _ ^ z.val.2 * _ ^ _) = _
  rw [hz]
  change _ * ((1 : ℂ) * _ ^ z.val.2 * _ ^ _) = _
  simp only [one_mul, printed_local_norm, ha]
  have hp : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  rw [Complex.cpow_def_of_ne_zero hp, Complex.cpow_def_of_ne_zero hp,
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp, Complex.ofReal_exp,
    ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem printed_spectral_support :
    ∃ E : Set ℂ, IsClosed E ∧ E.Countable ∧ (0 : ℂ) ∉ E ∧
      ∀ z : ratZeros, z.val.1.val = 1 → z.val.2 ∈ E ∧ z.val.2.re ≤ 1 := by
  let L := explicitFormulaCompletedHeckeL (1 : U[ℚ])
  obtain ⟨hm, hA⟩ := explicitFormulaCompletedHeckeL_spec (1 : U[ℚ])
  let E := {s : ℂ | 0 < ord(L) s}
  have hsub : E ⊆ (ord(L)).support := fun s h ↦ (show 0 < ord(L) s from h).ne'
  have hD := (ord(L)).discreteSupport
  have hc := isClosed_of_subset_discrete_closed hsub hD ((ord(L)).closedSupport isClosed_univ)
  have hz : (0 : ℂ) ∉ E := by
    change ¬ 0 < ord(L) 0
    rw [hm.meromorphicOn.divisor_apply (mem_univ _), completedHeckeL_one_order_zero _ hm hA]
    decide
  refine ⟨E, hc, ?_, hz, fun z he ↦ ?_⟩
  · exact (HereditarilyLindelofSpace.isLindelof E).countable_of_isDiscrete (hD.mono hsub)
  · have hp := z.property
    rw [he] at hp
    refine ⟨hp, ?_⟩
    by_cases hs : 0 < z.val.2.re
    · apply (completedHeckeL_continuation_zeros (1 : U[ℚ]) L hm hA hs ?_).le
      change 0 < ord(L) z.val.2 at hp
      rw [hm.meromorphicOn.divisor_apply (mem_univ _)] at hp
      by_cases ht : meromorphicOrderAt L z.val.2 = ⊤
      · simp [ht]
      · rw [← WithTop.coe_untop₀_of_ne_top ht]
        exact_mod_cast hp
    · linarith

private theorem printed_sum_at_real_place {ι : Type*} [Fintype ι] [Subsingleton ι]
    (B D : ι → ℂ) (w : ι) (hw : D w = 2) :
    (∑ i, (B i - B i / D i)) = B w / 2 := by
  rw [Fintype.sum_subsingleton _ w, hw]
  ring

private theorem printed_arch_difference_single {F : Type} [Field F] [NumberField F]
    [Subsingleton (InfinitePlace F)] (h : Printed.idelicExplicitFormula_archNormalization)
    (τ : ℝ≥0ˣ →ₜ* C[F]) (hτ : RightInverse τ (ideleClassNorm F))
    (w : InfinitePlace F) (hw : w.IsReal) (f : 𝒟(C[F])) :
    ∃ u : 𝒟(w.Completionˣ), (∀ x, u.val x = f.val (IdeleClassGroup.ofCompletion (𝓞 F) F w x)) ∧
      HasSum (fun z : sectionZeros(F, τ) ↦ sectionExcess(F, f, z))
        (printed_arch_pv w u / 2) := by
  obtain ⟨a, ha, hs⟩ := printed_arch_difference_general (F := F) h τ hτ f
  let D (v : InfinitePlace F) : ℂ := if v.IsReal then ((2 : ℝ) : ℂ) else 2 * (Real.pi : ℂ)
  have hw' : D w = 2 := by simp only [D, ite_eq_left hw, Complex.ofReal_ofNat]
  exact ⟨a w, ha w, printed_sum_value hs
    (printed_sum_at_real_place (fun v ↦ printed_arch_pv v (a v)) D w hw')⟩

private theorem printed_arch_difference_rat (h : Printed.idelicExplicitFormula_archNormalization)
    (f : 𝒟(C[ℚ])) :
    ∃ u : 𝒟(Rat.infinitePlace.Completionˣ), (∀ x, u.val x = f.val (ratLoc x)) ∧
      HasSum (fun z : ratZeros ↦ ratExcess(f, z))
        (printed_arch_pv ratInf u / 2) := by
  exact printed_arch_difference_single (F := ℚ) h printed_ratSection printed_ratSection_spec
    ratInf Rat.isReal_infinitePlace f

local notation "ratMu" => infiniteLocalMultiplicativeTamagawaMeasure ℚ Rat.infinitePlace
local notation "ratOrd(" z ")" => (ord(explicitFormulaCompletedHeckeL (z).val.1.val) (z).val.2 : ℂ)
local notation "ratKernel(" v ", " a ")" =>
  (∫ y : Rat.infinitePlace.Completionˣ, ((v) (ratLoc y)).re * Real.sqrt ‖y.val‖ /
    ‖((a)⁻¹).val - y.val‖ ∂ratMu : ℝ)

private theorem printed_translated_arch (h : Printed.idelicExplicitFormula_archNormalization)
    (v : SchwartzBruhat C[ℚ]) (hc : HasCompactSupport v.val)
    (hsupp : ∀ y, v y ≠ 0 → 2 < ((ideleClassNorm ℚ y).val : ℝ))
    (hreal : ∀ y, v y = ((v y).re : ℂ))
    (a : Rat.infinitePlace.Completionˣ) (ha : 1 ≤ ‖a.val‖) :
    HasSum (fun z : ratZeros ↦ (Real.sqrt ‖a.val‖ : ℂ) * printed_chartWeight z (ratLoc a) *
      ((1 - ratOrd(z)) * printed_sample v.val z)) ((ratKernel(v, a) : ℂ) / 4) := by
  obtain ⟨f, hf⟩ := printed_bruhat_translate v hc (ratLoc a)
  obtain ⟨u, hu, hS⟩ := printed_arch_difference_rat h f
  have hu' (x : Rat.infinitePlace.Completionˣ) : u.val x = v (ratLoc (a⁻¹ * x)) := by
    rw [hu, hf, map_mul, map_inv]
  have hone : u.val 1 = 0 := by
    rw [hu', mul_one]
    by_contra hne
    have hlt := hsupp _ hne
    rw [printed_local_norm, Units.val_inv_eq_inv_val, norm_inv] at hlt
    linarith [inv_le_one_of_one_le₀ ha]
  let : BorelSpace Rat.infinitePlace.Completion := ⟨rfl⟩
  let : BorelSpace Rat.infinitePlace.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : (ratMu).IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure ratInf
  have hscaled := printed_scaled_kernel ratMu (fun y ↦ (v (ratLoc y)).re) a
  have hI : (Real.sqrt ‖a.val‖ : ℂ) * (∫ x : Rat.infinitePlace.Completionˣ, u.val x *
      (Real.sqrt ‖x.val‖ : ℂ) / (‖1 - x.val‖ : ℂ) ∂ratMu) = (ratKernel(v, a) : ℂ) := by
    refine Eq.trans (congrArg ((Real.sqrt ‖a.val‖ : ℂ) * ·) (integral_congr_ae ?_)) hscaled
    exact ae_of_all _ fun x ↦ by dsimp only; rw [hu' x, hreal (ratLoc (a⁻¹ * x)), Complex.ofReal_re]
  have hterm (z : ratZeros) :
      (Real.sqrt ‖a.val‖ : ℂ) * ratExcess(f, z) =
        (Real.sqrt ‖a.val‖ : ℂ) * printed_chartWeight z (ratLoc a) *
          ((1 - ratOrd(z)) * printed_sample v.val z) := by
    rw [← printed_sample_eq, show f.val = _ from funext hf, printed_sample_translate]
    ring
  refine printed_sum_value ((hS.mul_left (Real.sqrt ‖a.val‖ : ℂ)).congr_fun
    (fun z ↦ (hterm z).symm)) ?_
  change (Real.sqrt ‖a.val‖ : ℂ) * (infiniteConnesWeilPrincipalValue ratInf u / 2) = _
  rw [realConnesWeilPrincipalValue_of_apply_one_zero _ Rat.isReal_infinitePlace u hone, ← hI]
  ring

/-- Paper: Theorem B.4.4.7, Equation (B.4.4.16), p. 623. Translate a
nonnegative radial rational test supported in norm greater than two. Subtract the
two formulas and multiply by the square root of the translating norm. The real
principal value then stays between two fixed positive constants. The spectral
side is an exponential series on the rational zeta zeros. Its Laplace transform
continues across zero as a sum of Cauchy kernels, although the positive lower
bound forces divergence there. -/
theorem Printed.idelicExplicitFormula_archNormalization_false :
    ¬ Printed.idelicExplicitFormula_archNormalization := by
  intro h
  obtain ⟨a₀, ha₀⟩ := printed_local_unit (Real.log 3)
  rw [Real.exp_log (by norm_num : 0 < (3 : ℝ))] at ha₀
  obtain ⟨v, hc, hv₀, hvS, hvR, hInv⟩ := printed_radial_bump (ideleClassNorm ℚ)
    (isProperMap_ideleClassNorm ℚ) (ratLoc a₀) (by rw [printed_local_norm, ha₀]; norm_num)
  let u (y : Rat.infinitePlace.Completionˣ) := (v (ratLoc y)).re
  have hu : Continuous u := Complex.continuous_re.comp ((schwartzBruhat_continuous v).comp
    (continuous_ideleClass_ofCompletion ℚ ratInf))
  have huC : HasCompactSupport u := by
    let f : 𝒟(C[ℚ]) := ⟨v.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth v), hc⟩
    obtain ⟨f', hf', _⟩ := printed_arch_difference_rat h f
    have heq : u = Complex.re ∘ f'.val := funext fun y ↦ congrArg Complex.re (hf' y).symm
    exact heq ▸ f'.property.2.comp_left Complex.zero_re
  have huS (y : Rat.infinitePlace.Completionˣ) (hy : u y ≠ 0) : 2 < ‖y.val‖ := by
    have hn : v (ratLoc y) ≠ 0 := fun he ↦ hy (congrArg Complex.re he)
    exact printed_local_norm y ▸ hvS _ hn
  let : BorelSpace Rat.infinitePlace.Completion := ⟨rfl⟩
  let : BorelSpace Rat.infinitePlace.Completionˣ := borelSpace_units_of_continuousInv₀ _
  let : (ratMu).IsHaarMeasure := infiniteLocalMultiplicativeTamagawaMeasure_isHaarMeasure ratInf
  obtain ⟨B, hB, hbounds⟩ := printed_real_kernel_bounds ratMu u hu huC
    (fun y ↦ (hvR _).2) ⟨a₀, (show u a₀ = 1 from congrArg Complex.re hv₀) ▸ one_ne_zero⟩ huS
  -- At translation zero the difference formula gives absolute summability. At positive
  -- translations the same coefficients acquire the exponential of the zero times t.
  let b (z : ratZeros) := (1 - ratOrd(z)) * printed_sample v.val z
  have h₁ := printed_translated_arch h v hc hvS (fun y ↦ (hvR y).1)
    (1 : Rat.infinitePlace.Completionˣ) (by simp)
  have hsum : Summable b := by
    simpa only [Units.val_one, norm_one, Real.sqrt_one, Complex.ofReal_one, map_one, one_mul] using h₁.summable
  let J := support b
  let : Countable J := hsum.countable_support
  have htr (z : J) : z.val.val.1.val = 1 := printed_chart_trivial hInv
    (right_ne_zero_of_mul (show (1 - ratOrd(z.val)) * printed_sample v.val z.val ≠ 0 from z.property))
  obtain ⟨E, hE, hcnt, h₀, hmem⟩ := printed_spectral_support
  let w (z : J) := z.val.val.2
  let S (t : ℝ) := ∑' z : J, b z.val * Complex.exp (w z * t)
  have hS (t : ℝ) (ht : 0 < t) : B / 8 ≤ (S t).re ∧ ‖S t‖ ≤ B / 2 := by
    obtain ⟨a, ha⟩ := printed_local_unit t
    have ha₁ : 1 ≤ ‖a.val‖ := ha ▸ (Real.one_le_exp ht.le)
    have hA := printed_translated_arch h v hc hvS (fun y ↦ (hvR y).1) a ha₁
    let d (z : ratZeros) := (Real.sqrt ‖a.val‖ : ℂ) * printed_chartWeight z (ratLoc a) * b z
    have hsupp : support d ⊆ J := fun z hz ↦ right_ne_zero_of_mul hz
    have hs := (hasSum_subtype_iff_of_support_subset hsupp).mpr hA
    have hterm (z : J) : d z.val = b z.val * Complex.exp (w z * t) := by
      dsimp only [d]
      rw [ha, ← Real.exp_half, printed_chartWeight_exp (htr z) a ha, mul_comm]
    have hvalue : S t = (ratKernel(v, a) : ℂ) / 4 := (hs.congr_fun (fun z ↦ (hterm z).symm)).tsum_eq
    obtain ⟨hl, hh⟩ := hbounds a ha₁
    change B / 2 ≤ ratKernel(v, a) at hl
    change ratKernel(v, a) ≤ 2 * B at hh
    rw [hvalue, ← Complex.ofReal_ofNat (n := 4), ← Complex.ofReal_div, Complex.ofReal_re,
      Complex.norm_real, Real.norm_of_nonneg (by linarith : 0 ≤ ratKernel(v, a) / 4)]
    constructor <;> linarith
  exact printed_no_bounded_positive_series w (fun z : J ↦ b z.val) (hsum.subtype _).norm
    (fun z ↦ (hmem z.val (htr z)).2) hE hcnt h₀ (fun z ↦ (hmem z.val (htr z)).1)
    _ _ (show 0 < B / 8 by positivity) (fun t ht ↦ (hS t ht).1) (fun t ht ↦ (hS t ht).2)

/-- Paper: Lemma B.4.4.8, Equation (B.4.4.17), p. 624. As printed: for a
positive-real-modulated abelian Lie group and a Haar measure, the Mellin evaluations
of every compactly supported Bruhat test are absolutely summable over any set
of quasi-characters whose intersection with each connected component is discrete
and lies in a bounded-width vertical strip of that component. See
`summable_bruhatMellin_of_polynomialCount` and ERRATA F44. -/
def Printed.summable_bruhatMellin_of_discreteStrips : Prop :=
  ∀ (G : Type) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (d : ℕ) [ChartedSpace (EuclideanSpace ℝ (Fin d)) G]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) (∞) G]
    [LieGroup (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin d))) (∞) G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m), Surjective m →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (Z : Set (QuasiCharacter G)),
      (∀ c : QuasiCharacter G,
        IsDiscrete (Z ∩ connectedComponent c) ∧
          ∃ a b : ℝ, a < b ∧
            Z ∩ connectedComponent c ⊆ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 (Ioo a b)) →
      ∀ f : 𝒟(G), Summable (fun c : Z ↦ ‖∫ g, f.val g * c.val g ∂μ‖)

private theorem printed_discrete_abscissas {X : Type*} [TopologicalSpace X]
    (σ : X → ℝ) (hσ : Continuous σ) (c : ℕ → X)
    (hc : ∀ n, σ (c n) = ((n : ℝ) + 1)⁻¹) : IsDiscrete (range c) := by
  refine isDiscrete_iff_forall_mem_exists_isOpen.mpr ?_
  rintro _ ⟨n, rfl⟩
  let U := {x | ((n : ℝ) + 1 / 2) * σ x < 1} ∩ {x | 1 < ((n : ℝ) + 3 / 2) * σ x}
  refine ⟨U, (isOpen_lt (continuous_const.mul hσ) continuous_const).inter
    (isOpen_lt continuous_const (continuous_const.mul hσ)), ?_⟩
  have hmem (k : ℕ) : c k ∈ U ↔ k = n := by
    change _ * σ (c k) < 1 ∧ 1 < _ * σ (c k) ↔ _
    rw [hc, ← div_eq_mul_inv, ← div_eq_mul_inv, div_lt_iff₀ (by positivity),
      lt_div_iff₀ (by positivity)]
    constructor
    · rintro ⟨h₁, h₂⟩
      rcases lt_trichotomy k n with h | h | h
      · have hl : (k : ℝ) + 1 ≤ n := by exact_mod_cast h
        linarith
      · exact h
      · have hl : (n : ℝ) + 1 ≤ k := by exact_mod_cast h
        linarith
    · rintro rfl
      constructor <;> linarith
  ext x
  constructor
  · rintro ⟨hx, k, rfl⟩
    rw [(hmem k).mp hx]
    rfl
  · rintro rfl
    exact ⟨(hmem n).mpr rfl, mem_range_self _⟩

private theorem printed_discrete_samples {G : Type} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hs : Surjective m) :
    ∃ (Z : Set (QuasiCharacter G)) (f : 𝒟(G)),
      (∀ p : QuasiCharacter G, IsDiscrete (Z ∩ connectedComponent p) ∧
        ∃ a b : ℝ, a < b ∧ Z ∩ connectedComponent p ⊆ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 (Ioo a b)) ∧
      ¬ Summable (fun c : Z ↦ ‖∫ g, f.val g * c.val g ∂Measure.haar‖) := by
  let a (n : ℕ) := ((n : ℝ) + 1)⁻¹
  let c (n : ℕ) := quasiCharacterNormTwist m.toMonoidHom m.continuous 1 (a n : ℂ)
  let σ := quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2
  have hc (n : ℕ) : σ (c n) = a n :=
    quasiCharacterAbscissa_of_unitary_twist m.toMonoidHom hm.1 hm.2 (c n) 1 (a n : ℂ) (fun _ ↦ rfl)
  have hd := printed_discrete_abscissas σ (continuous_quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2) c hc
  let r (x : G) : ℝ := (m x).val
  have hr : Continuous r := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hpos (x : G) : 0 < r x := NNReal.coe_pos.mpr (Units.zero_lt _)
  let u₂ := Units.mk0 (2 : ℝ≥0) (by norm_num)
  obtain ⟨y, hy⟩ := hs u₂
  have hy₂ : 1 < r y := by simp [r, hy, u₂]
  obtain ⟨v, hv, hU, h₁, hvR⟩ := printed_nonnegative_test (U := {g | 1 < r g}) (isOpen_lt continuous_const hr) hy₂
  let f : 𝒟(G) := ⟨v.val, (mem_bruhatSmoothSubmodule_iff _).mpr (schwartzBruhat_isBruhatSmooth v), hv⟩
  refine ⟨range c, f, fun p ↦ ⟨hd.mono inter_subset_left, 0, 2, by norm_num, ?_⟩, ?_⟩
  · rintro _ ⟨⟨n, rfl⟩, _⟩
    change 0 < σ (c n) ∧ σ (c n) < 2
    rw [hc]
    dsimp [a]
    constructor
    · positivity
    · rw [inv_lt_iff_one_lt_mul₀ (by positivity)]
      linarith [Nat.cast_nonneg (α := ℝ) n]
  · intro hsum
    let j (n : ℕ) : range c := ⟨c n, mem_range_self _⟩
    have hj : Injective j := by
      intro n k he
      have he' := congrArg (fun p : range c ↦ σ p.val) he
      change σ (c n) = σ (c k) at he'
      simpa [hc, a] using he'
    have hs' : Summable (fun n ↦ ‖∫ g, f.val g * (j n).val g ∂Measure.haar‖) := hsum.comp_injective hj
    let u (g : G) := (v g).re
    have hu : Continuous u := Complex.continuous_re.comp (schwartzBruhat_continuous v)
    have huC : HasCompactSupport u := hv.comp_left Complex.zero_re
    let B := ∫ g, u g ∂Measure.haar
    have hB : 0 < B := hu.integral_pos_of_hasCompactSupport_nonneg_ne_zero huC
      (fun g ↦ (hvR g).2) (x := y) (by simp [u, h₁])
    have hbound (n : ℕ) : B ≤ ‖∫ g, f.val g * (j n).val g ∂Measure.haar‖ := by
      let w (g : G) := r g ^ a n
      have hw : Continuous w := hr.rpow_const (fun g ↦ Or.inl (hpos g).ne')
      have hint := (hu.mul hw).integrable_of_hasCompactSupport (μ := Measure.haar) huC.mul_right
      have hle : B ≤ ∫ g, u g * w g ∂Measure.haar := by
        apply integral_mono (hu.integrable_of_hasCompactSupport huC) hint
        intro g
        by_cases hg : g ∈ tsupport v.val
        · exact le_mul_of_one_le_right (hvR g).2 (Real.one_le_rpow (hU hg).le (by dsimp [a]; positivity))
        · have hz : v g = 0 := image_eq_zero_of_notMem_tsupport hg
          simp [u, hz]
      have he (g : G) : f.val g * (j n).val g = ((u g * w g : ℝ) : ℂ) := by
        change v g * (1 * (r g : ℂ) ^ (a n : ℂ)) = _
        rw [one_mul, ← Complex.ofReal_cpow (hpos g).le]
        exact (congrArg (· * _) (hvR g).1).trans (Complex.ofReal_mul _ _).symm
      rw [integral_congr_ae (ae_of_all Measure.haar he), integral_complex_ofReal, Complex.norm_real]
      exact hle.trans (le_abs_self _)
    exact hB.not_ge (ge_of_tendsto hs'.tendsto_atTop_zero (Eventually.of_forall hbound))

/-- Paper: Lemma B.4.4.8, p. 624. On the multiplicative copy of the real line,
use the real exponents `1/(n+1)`. Their limit is omitted, so the set is discrete
and lies in the strip with real parts between zero and two. A nonnegative test
supported where the modulus exceeds one has every sample bounded below by its
strictly positive Haar integral. -/
theorem Printed.summable_bruhatMellin_of_discreteStrips_false :
    ¬ Printed.summable_bruhatMellin_of_discreteStrips := by
  intro h
  let E := EuclideanSpace ℝ (Fin 1)
  let G := Multiplicative E
  let e := PiLp.equivOfUnique (p := 2) (𝕜 := ℝ) (ι := Fin 1) (β := fun _ ↦ ℝ)
  let l : G ≃ₜ* Multiplicative ℝ :=
    { toMulEquiv := e.toLinearEquiv.toAddEquiv.toMultiplicative
      continuous_toFun := e.continuous
      continuous_invFun := e.symm.continuous }
  let m := l.trans positiveRealLogEquiv.symm
  have hadd := ContMDiffAdd.contMDiff_add (I := modelWithCornersSelf ℝ E) (n := ∞) (G := E)
  have hneg := LieAddGroup.contMDiff_neg (I := modelWithCornersSelf ℝ E) (n := ∞) (G := E)
  let : ChartedSpace E G := inferInstanceAs (ChartedSpace E E)
  let : IsManifold (modelWithCornersSelf ℝ E) (∞) G :=
    inferInstanceAs (IsManifold (modelWithCornersSelf ℝ E) (∞) E)
  let : LieGroup (modelWithCornersSelf ℝ E) (∞) G :=
    { contMDiff_mul := hadd
      contMDiff_inv := hneg }
  have hm : IsModulation (m : G →ₜ* ℝ≥0ˣ) := by
    refine ⟨m.toHomeomorph.isProperMap, m.symm (Units.mk0 (2 : ℝ≥0) (by norm_num)), ?_⟩
    rw [show (m : G →ₜ* ℝ≥0ˣ) _ = _ from m.apply_symm_apply _]
    intro he
    have he' := congrArg Units.val he
    norm_num at he'
  obtain ⟨Z, f, hZ, hf⟩ := printed_discrete_samples (m : G →ₜ* ℝ≥0ˣ) hm m.surjective
  exact hf (h G 1 m hm m.surjective Measure.haar Z hZ f)

end RiemannMasullo
