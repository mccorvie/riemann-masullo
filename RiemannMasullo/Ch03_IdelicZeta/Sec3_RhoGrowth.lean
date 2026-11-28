module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Gamma.VerticalStripRatio
import Mathlib.Analysis.Complex.Liouville
import RiemannMasullo.AppA_AlgebraicNT.Sec3
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Growth of the S-local correcting factor on vertical lines

Proposition 3.3.1.5(3), (3.3.1.11), p. 132, bounds the derivatives of the S-local correcting
factor on each vertical line of positive abscissa. As printed the exponent omits the archimedean
degrees, and the printed bound is refuted in `Sec3_Printed` (ERRATA F16). This file proves the
corrected bound: on the line of abscissa `σ > 0` the `k`th derivative is
`O(|τ| ^ (n (σ - 1/2)) (log |τ|) ^ k)`, where `n = [F : ℚ] = r₁ + 2 r₂`.

The proof bounds the factor itself on vertical strips near the line, then applies Cauchy's
estimate on discs of radius `1 / log |τ|`. Away from the line the factor is the epsilon factor
times the S-local Euler factor divided by its dual (`sLocalRhoFactor_eq_epsilon_mul`). At an
archimedean place the quotient of Euler factors is a quotient of gamma factors at a common height,
bounded by `norm_Gamma_div_le_rpow_on_strip`. At a finite place every factor is a function of the
chart that is periodic in the imaginary direction, since the local norm takes values in the
powers of the residue cardinality, and so it is bounded on vertical strips.
-/

@[expose] public noncomputable section

open Complex Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology ComplexConjugate

namespace RiemannMasullo

section GammaRatio

/-- A power of a height comparable to `s` is bounded by a constant times the same power of `s`,
for exponents in a bounded range. -/
private theorem rpow_le_of_comparable {u s e B : ℝ} (hs : 0 < s) (hlo : s / 4 ≤ u) (hhi : u ≤ s)
    (he : |e| ≤ B) :
    u ^ e ≤ 4 ^ B * s ^ e := by
  have hs4 : 0 < s / 4 := div_pos hs (by norm_num)
  have hu : 0 < u := hs4.trans_le hlo
  rcases le_total 0 e with h0 | h0
  · have h1 : (1 : ℝ) ≤ 4 ^ B := Real.one_le_rpow (by norm_num) ((abs_nonneg e).trans he)
    calc u ^ e ≤ s ^ e := Real.rpow_le_rpow hu.le hhi h0
      _ ≤ 4 ^ B * s ^ e := le_mul_of_one_le_left (Real.rpow_nonneg hs.le _) h1
  · have hneg : -e ≤ B := by rw [abs_of_nonpos h0] at he; exact he
    have h4 : (4 : ℝ) ^ (-e) ≤ 4 ^ B := Real.rpow_le_rpow_of_exponent_le (by norm_num) hneg
    have hq : (s / 4) ^ e = 4 ^ (-e) * s ^ e := by
      rw [Real.div_rpow hs.le (by norm_num), Real.rpow_neg (by norm_num), div_eq_mul_inv,
        mul_comm]
    calc u ^ e ≤ (s / 4) ^ e := Real.rpow_le_rpow_of_nonpos hs4 hlo h0
      _ = 4 ^ (-e) * s ^ e := hq
      _ ≤ 4 ^ B * s ^ e := mul_le_mul_of_nonneg_right h4 (Real.rpow_nonneg hs.le _)

/-- The norm of a power of a positive real number. -/
private theorem norm_ofReal_cpow_of_pos {b : ℝ} (hb : 0 < b) (u : ℂ) :
    ‖(b : ℂ) ^ u‖ = b ^ u.re :=
  Complex.norm_cpow_eq_rpow_re_of_pos hb u

/-- The norm of the gamma function is invariant under conjugating the argument. -/
private theorem norm_Gamma_conj (w : ℂ) : ‖Complex.Gamma (conj w)‖ = ‖Complex.Gamma w‖ := by
  rw [Complex.Gamma_conj, Complex.norm_conj]

/-- At large height, a height shifted by a fixed amount stays within a factor of two. -/
private theorem abs_add_comparable {u c : ℝ} (hu : 4 * |c| + 4 ≤ |u|) :
    |u| / 2 ≤ |u + c| ∧ |u + c| ≤ 2 * |u| := by
  have h1 := abs_sub_abs_le_abs_sub u (-c)
  rw [sub_neg_eq_add, abs_neg] at h1
  have h2 := abs_add_le u c
  constructor <;> linarith [abs_nonneg c]

/-- On a vertical strip of positive abscissa and at large height, the quotient of the real gamma
factor at `z + t + a` by the one at `1 - (z + t) + a` is at most a constant times
`|Im z| ^ (Re z - 1/2)`, for `t` purely imaginary and `a ≥ 0`. -/
theorem exists_norm_Gammaℝ_div_le {a : ℝ} (ha : 0 ≤ a) {x₀ x₁ : ℝ} (hx₀ : 0 < x₀)
    (t : ℂ) (ht : t.re = 0) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ z : ℂ, x₀ ≤ z.re → z.re ≤ x₁ → T ≤ |z.im| →
      ‖Complex.Gammaℝ (z + t + a) / Complex.Gammaℝ (1 - (z + t) + a)‖ ≤
        C * |z.im| ^ (z.re - 1 / 2) := by
  have hM : 1 ≤ |x₁| + |x₀| + a + 2 := by linarith [abs_nonneg x₁, abs_nonneg x₀]
  obtain ⟨C₀, hC₀, hC₀b⟩ := norm_Gamma_div_le_rpow_on_strip hM
  refine ⟨Real.pi ^ (|x₀| + |x₁| + 1) * (C₀ * 4 ^ (|x₀| + |x₁| + 1)), 4 * |t.im| + 4,
    by positivity, by positivity, ?_⟩
  intro z hzx₀ hzx₁ hzT
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hzim : 0 < |z.im| := lt_of_lt_of_le (by positivity) hzT
  obtain ⟨hy_lo, hy_hi⟩ := abs_add_comparable hzT
  have hy2 : 1 ≤ |(z.im + t.im) / 2| := by
    rw [abs_div, abs_two]; linarith [abs_nonneg t.im]
  have hw₁ : (z + t + a) / 2 = (⟨(z.re + a) / 2, (z.im + t.im) / 2⟩ : ℂ) := by
    apply Complex.ext <;> simp [ht]
  have hw₂ : conj ((1 - (z + t) + a) / 2) = (⟨(1 - z.re + a) / 2, (z.im + t.im) / 2⟩ : ℂ) := by
    have hc : conj ((1 - (z + t) + a) / 2) = (1 - (conj z + conj t) + a) / 2 := by
      simp [map_ofNat]
    rw [hc]
    apply Complex.ext <;> simp [Complex.div_ofNat_re, Complex.div_ofNat_im, ht]; ring
  have hgam : ‖Complex.Gamma ((z + t + a) / 2) / Complex.Gamma ((1 - (z + t) + a) / 2)‖ ≤
      C₀ * |(z.im + t.im) / 2| ^ (z.re - 1 / 2) := by
    rw [norm_div, ← norm_Gamma_conj ((1 - (z + t) + a) / 2), hw₁, hw₂, ← norm_div]
    have h := hC₀b ((z.re + a) / 2) ((1 - z.re + a) / 2) ((z.im + t.im) / 2)
      (by rw [abs_le]; constructor <;> linarith [le_abs_self x₁, abs_nonneg x₁, abs_nonneg x₀])
      (by rw [abs_le]; constructor <;>
        linarith [le_abs_self x₁, neg_abs_le x₁, abs_nonneg x₁, abs_nonneg x₀])
      hy2
    convert h using 3; ring
  have hpow : ‖(Real.pi : ℂ) ^ (-(z + t + a) / 2)‖ / ‖(Real.pi : ℂ) ^ (-(1 - (z + t) + a) / 2)‖ ≤
      Real.pi ^ (|x₀| + |x₁| + 1) := by
    rw [norm_ofReal_cpow_of_pos hpi, norm_ofReal_cpow_of_pos hpi, ← Real.rpow_sub hpi]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
    have : (-(z + t + a) / 2).re - (-(1 - (z + t) + a) / 2).re = 1 / 2 - z.re := by
      simp [ht]; ring
    rw [this]
    linarith [neg_abs_le x₀, abs_nonneg x₁]
  have hcmp : |(z.im + t.im) / 2| ^ (z.re - 1 / 2) ≤
      4 ^ (|x₀| + |x₁| + 1) * |z.im| ^ (z.re - 1 / 2) := by
    apply rpow_le_of_comparable hzim
    · rw [abs_div, abs_two]; linarith
    · rw [abs_div, abs_two]; linarith
    · rw [abs_le]; constructor <;>
        linarith [le_abs_self x₁, neg_abs_le x₀, abs_nonneg x₁, abs_nonneg x₀]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def, mul_div_mul_comm, norm_mul, norm_div]
  calc ‖(Real.pi : ℂ) ^ (-(z + t + a) / 2)‖ / ‖(Real.pi : ℂ) ^ (-(1 - (z + t) + a) / 2)‖ *
        ‖Complex.Gamma ((z + t + a) / 2) / Complex.Gamma ((1 - (z + t) + a) / 2)‖
      ≤ Real.pi ^ (|x₀| + |x₁| + 1) * (C₀ * |(z.im + t.im) / 2| ^ (z.re - 1 / 2)) :=
        mul_le_mul hpow hgam (norm_nonneg _) (by positivity)
    _ ≤ Real.pi ^ (|x₀| + |x₁| + 1) * (C₀ * (4 ^ (|x₀| + |x₁| + 1) * |z.im| ^ (z.re - 1 / 2))) := by
        gcongr
    _ = _ := by ring

/-- On a vertical strip of positive abscissa and at large height, the quotient of the complex
gamma factor at `z + t + r` by the one at `1 - (z + t) + r` is at most a constant times
`|Im z| ^ (2 (Re z - 1/2))`, for `t` purely imaginary and `r ≥ 0`. -/
theorem exists_norm_Gammaℂ_div_le {r : ℝ} (hr : 0 ≤ r) {x₀ x₁ : ℝ} (hx₀ : 0 < x₀)
    (t : ℂ) (ht : t.re = 0) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ z : ℂ, x₀ ≤ z.re → z.re ≤ x₁ → T ≤ |z.im| →
      ‖Complex.Gammaℂ (z + t + r) / Complex.Gammaℂ (1 - (z + t) + r)‖ ≤
        C * |z.im| ^ (2 * (z.re - 1 / 2)) := by
  have hM : 1 ≤ 2 * (|x₁| + |x₀| + r + 2) := by linarith [abs_nonneg x₁, abs_nonneg x₀]
  obtain ⟨C₀, hC₀, hC₀b⟩ := norm_Gamma_div_le_rpow_on_strip hM
  let B : ℝ := 2 * (|x₀| + |x₁| + 1)
  refine ⟨(2 * Real.pi) ^ B * (C₀ * (4 ^ B * 4 ^ B)), 4 * |t.im| + 4, by positivity, by positivity,
    ?_⟩
  intro z hzx₀ hzx₁ hzT
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hzim : 0 < |z.im| := lt_of_lt_of_le (by positivity) hzT
  obtain ⟨hy_lo, hy_hi⟩ := abs_add_comparable hzT
  have hy1 : 1 ≤ |z.im + t.im| := by linarith [abs_nonneg t.im]
  have hw₁ : z + t + r = (⟨z.re + r, z.im + t.im⟩ : ℂ) := by
    apply Complex.ext <;> simp [ht]
  have hw₂ : conj (1 - (z + t) + r) = (⟨1 - z.re + r, z.im + t.im⟩ : ℂ) := by
    apply Complex.ext <;> simp [ht]; ring
  have hgam : ‖Complex.Gamma (z + t + r) / Complex.Gamma (1 - (z + t) + r)‖ ≤
      C₀ * |z.im + t.im| ^ (2 * (z.re - 1 / 2)) := by
    rw [norm_div, ← norm_Gamma_conj (1 - (z + t) + r), hw₁, hw₂, ← norm_div]
    have h := hC₀b (z.re + r) (1 - z.re + r) (z.im + t.im)
      (by rw [abs_le]; constructor <;> linarith [le_abs_self x₁, abs_nonneg x₁, abs_nonneg x₀])
      (by rw [abs_le]; constructor <;>
        linarith [le_abs_self x₁, neg_abs_le x₁, abs_nonneg x₁, abs_nonneg x₀])
      hy1
    convert h using 3; ring
  have hpow : ‖2 * (2 * (Real.pi : ℂ)) ^ (-(z + t + r))‖ /
      ‖2 * (2 * (Real.pi : ℂ)) ^ (-(1 - (z + t) + r))‖ ≤ (2 * Real.pi) ^ B := by
    have e2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
    rw [e2, norm_mul, norm_mul, norm_ofReal_cpow_of_pos h2pi, norm_ofReal_cpow_of_pos h2pi,
      mul_div_mul_left _ _ (by norm_num), ← Real.rpow_sub h2pi]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith [Real.pi_gt_three])
    have : (-(z + t + r)).re - (-(1 - (z + t) + r)).re = 1 - 2 * z.re := by
      simp [ht]; ring
    rw [this]
    linarith [neg_abs_le x₀, abs_nonneg x₁]
  have hcmp : |z.im + t.im| ^ (2 * (z.re - 1 / 2)) ≤
      4 ^ B * 4 ^ B * |z.im| ^ (2 * (z.re - 1 / 2)) := by
    have hlo2 : (2 * |z.im|) / 4 ≤ |z.im + t.im| := by linarith
    calc |z.im + t.im| ^ (2 * (z.re - 1 / 2))
        ≤ 4 ^ B * (2 * |z.im|) ^ (2 * (z.re - 1 / 2)) := by
          apply rpow_le_of_comparable (by positivity) hlo2 hy_hi
          rw [abs_le]; constructor <;>
            linarith [le_abs_self x₁, neg_abs_le x₀, abs_nonneg x₁, abs_nonneg x₀]
      _ = 4 ^ B * (2 ^ (2 * (z.re - 1 / 2)) * |z.im| ^ (2 * (z.re - 1 / 2))) := by
          rw [Real.mul_rpow (by norm_num) hzim.le]
      _ ≤ 4 ^ B * (4 ^ B * |z.im| ^ (2 * (z.re - 1 / 2))) := by
          gcongr
          calc (2 : ℝ) ^ (2 * (z.re - 1 / 2)) ≤ 2 ^ B :=
                Real.rpow_le_rpow_of_exponent_le (by norm_num) (by
                  linarith [le_abs_self x₁, abs_nonneg x₀])
            _ ≤ 4 ^ B := Real.rpow_le_rpow (by norm_num) (by norm_num) (by positivity)
      _ = 4 ^ B * 4 ^ B * |z.im| ^ (2 * (z.re - 1 / 2)) := by ring
  rw [Complex.Gammaℂ_def, Complex.Gammaℂ_def, mul_div_mul_comm, norm_mul, norm_div]
  calc ‖2 * (2 * (Real.pi : ℂ)) ^ (-(z + t + r))‖ / ‖2 * (2 * (Real.pi : ℂ)) ^ (-(1 - (z + t) + r))‖ *
        ‖Complex.Gamma (z + t + r) / Complex.Gamma (1 - (z + t) + r)‖
      ≤ (2 * Real.pi) ^ B * (C₀ * |z.im + t.im| ^ (2 * (z.re - 1 / 2))) :=
        mul_le_mul hpow hgam (norm_nonneg _) (by positivity)
    _ ≤ (2 * Real.pi) ^ B * (C₀ * (4 ^ B * 4 ^ B * |z.im| ^ (2 * (z.re - 1 / 2)))) := by gcongr
    _ = _ := by ring

end GammaRatio


section LocalFactors

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ" => SIdeleQuotient F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "classOf" => (QuotientGroup.mk : Iₛ → Jₛ)
local notation "modℂ[" m "," g "]" => (((m g : ℝ≥0) : ℝ) : ℂ)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "m∞(" w ")" => ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
  (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)
local notation "m𝔭(" v ")" => (Units.map nnNormHom.toMonoidHom :
  (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)
local notation "h∞(" w ")" => continuous_infiniteLocalModule w
local notation "h𝔭(" v ")" => continuous_finiteLocalModule v
local notation "chartₛ(" χ ")" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ ((circleToComplex).comp χ)
local notation "chart∞[" w "," χ "]" =>
  quasiCharacterNormTwist m∞(w) h∞(w) ((circleToComplex).comp χ)
local notation "chart𝔭[" v "," χ "]" =>
  quasiCharacterNormTwist m𝔭(v) h𝔭(v) ((circleToComplex).comp χ)
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v))
local notation "eProd" => ContinuousMulEquiv.prodUnits
  (InfiniteAdeleRing F) ((v : S) → HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "eArch" => ContinuousMulEquiv.piUnits (M := InfinitePlace.Completion (K := F))
local notation "eFin" => ContinuousMulEquiv.piUnits (M := fun v : S ↦ HeightOneSpectrum.adicCompletion F (Subtype.val v))
local notation "archAt(" w ")" => fun x ↦
  classOf ((eProd).symm ((eArch).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w x), 1))
local notation "finAt(" v ")" => fun x ↦
  classOf ((eProd).symm (1, (eFin).symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x)))
local notation "realModel(" hw ")" => InfinitePlace.Completion.ringEquivRealOfIsReal hw
local notation "complexModel(" hw ")" => InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
local notation "realShape[" hw "," c "," z "," a "]" => (∀ x : ℝˣ,
  c (Units.map (realModel(hw)).symm.toMonoidHom x) =
    (‖(x : ℝ)‖ : ℂ) ^ (z : ℂ) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ (a : Fin 2).val)
local notation "complexShape[" hw "," c "," z "," r "]" => (∀ x : ℂˣ,
  c (Units.map (complexModel(hw)).symm.toMonoidHom x) =
    ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z : ℂ) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (r : ℤ))
local notation "unit(" χ ")" => (circleToComplex).comp χ

/-- Restriction of a unitary S-local chart to an archimedean place is the chart of one
unitary character of the place, given by composing with a fixed insertion. -/
private theorem exists_infiniteInsertion_chart (w : InfinitePlace F) :
    ∃ i : w.Completionˣ →ₜ* Jₛ, ∀ (χ : PontryaginDual Jₛ) (s : ℂ),
      sLocalInfiniteRestriction w (chartₛ(χ) s) = chart∞[w, χ.comp i] s := by
  let h := sLocalInfiniteInsertion_properties (S := S) w
  let i : w.Completionˣ →ₜ* Jₛ := ⟨⟨⟨archAt(w), h.1⟩, h.2.1⟩, h.2.2⟩
  refine ⟨i, fun χ s ↦ ?_⟩
  ext1 g
  change (χ (i g) : ℂ) * (modℂ[mₛ, i g]) ^ s = (χ (i g) : ℂ) * _ ^ s
  have hm := sLocalInfiniteRestriction_norm (S := S) w g
  change ((1 : PontryaginDual Jₛ) (i g) : ℂ) * (modℂ[mₛ, i g]) ^ (1 : ℂ) = _ at hm
  simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using
    congrArg (fun t : ℂ ↦ (χ (i g) : ℂ) * t ^ s) hm

/-- Restriction of a unitary S-local chart to a finite place of `S` is the chart of one
unitary character of the place, given by composing with a fixed insertion. -/
private theorem exists_finiteInsertion_chart (v : S) :
    ∃ i : (v.val.adicCompletion F)ˣ →ₜ* Jₛ, ∀ (χ : PontryaginDual Jₛ) (s : ℂ),
      sLocalFiniteRestriction v (chartₛ(χ) s) = chart𝔭[v.val, χ.comp i] s := by
  let h := sLocalFiniteInsertion_properties v
  let i : (v.val.adicCompletion F)ˣ →ₜ* Jₛ := ⟨⟨⟨finAt(v), h.1⟩, h.2.1⟩, h.2.2⟩
  refine ⟨i, fun χ s ↦ ?_⟩
  ext1 g
  change (χ (i g) : ℂ) * (modℂ[mₛ, i g]) ^ s = (χ (i g) : ℂ) * _ ^ s
  have hm := sLocalFiniteRestriction_norm v g
  change ((1 : PontryaginDual Jₛ) (i g) : ℂ) * (modℂ[mₛ, i g]) ^ (1 : ℂ) = _ at hm
  simpa only [PontryaginDual.one_apply, Circle.coe_one, one_mul, Complex.cpow_one] using
    congrArg (fun t : ℂ ↦ (χ (i g) : ℂ) * t ^ s) hm

/-- The dual of a unitary S-local chart has the inverse unitary base and the reflected
parameter. -/
private theorem dual_sLocal_chart (χ : PontryaginDual Jₛ) (s : ℂ) :
    dualQuasiCharacter (G := Jₛ) mₛ hmₛ (chartₛ(χ) s) = chartₛ(χ⁻¹) (1 - s) := by
  ext1 u
  let N : ℂ := (((mₛ u : ℝ≥0) : ℝ) : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ u).ne_zero)
  change N * chartₛ(χ) s u⁻¹ = (χ⁻¹ u : ℂ) * N ^ (1 - s)
  rw [map_inv]
  change N * ((χ u : ℂ) * N ^ s)⁻¹ = (χ u : ℂ)⁻¹ * N ^ (1 - s)
  rw [mul_inv_rev, Complex.cpow_sub 1 s hN, Complex.cpow_one, div_eq_mul_inv]
  ac_rfl

/-- A unitary character of a real place has a purely imaginary exponent and a parity. -/
private theorem real_unitary_shape (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) :
    ∃ (t : ℂ) (a : Fin 2), t.re = 0 ∧ realShape[hw, unit(χ), t, a] := by
  let e := (realModel(hw)).symm
  let i : ℝˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
  obtain ⟨p, ht, hp⟩ := (existsUnique_realUnits_character_parameters ((unit(χ)).comp i)
    (fun _ ↦ Circle.norm_coe _)).exists
  exact ⟨p.1, p.2, ht, hp⟩

/-- A unitary character of a complex place has a purely imaginary exponent and an angular
weight. -/
private theorem complex_unitary_shape (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) :
    ∃ (t : ℂ) (r : ℤ), t.re = 0 ∧ complexShape[hw, unit(χ), t, r] := by
  let e := (complexModel(hw)).symm
  let i : ℂˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
  obtain ⟨p, ht, hp⟩ := (existsUnique_complexUnits_character_parameters ((unit(χ)).comp i)
    (fun _ ↦ Circle.norm_coe _)).exists
  exact ⟨p.1, p.2, ht, hp⟩

private theorem real_module_model (w : InfinitePlace F) (hw : w.IsReal) (x : ℝˣ) :
    (((m∞(w) (Units.map (realModel(hw)).symm.toMonoidHom x) : ℝ≥0) : ℝ)) = ‖x.val‖ := by
  have hn : ‖(realModel(hw)).symm x.val‖ = ‖x.val‖ :=
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
      (map_zero (realModel(hw)).symm) x.val
  simp [InfinitePlace.mult, hw, hn]

private theorem complex_module_model (w : InfinitePlace F) (hw : w.IsComplex) (x : ℂˣ) :
    (((m∞(w) (Units.map (complexModel(hw)).symm.toMonoidHom x) : ℝ≥0) : ℝ)) = ‖x.val‖ ^ 2 := by
  have hn : ‖(complexModel(hw)).symm x.val‖ = ‖x.val‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.isometry.norm_map_of_map_zero
      (map_zero (complexModel(hw)).symm) x.val
  simp [InfinitePlace.mult, InfinitePlace.not_isReal_iff_isComplex.mpr hw, hn]

private theorem real_chart_shape (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (t : ℂ) (a : Fin 2) (hc : realShape[hw, unit(χ), t, a])
    (z : ℂ) : realShape[hw, chart∞[w, χ] z, z + t, a] := by
  intro x
  let u := Units.map (realModel(hw)).symm.toMonoidHom x
  change unit(χ) u * ((((m∞(w) u : ℝ≥0) : ℝ)) : ℂ) ^ z = _
  rw [hc x, real_module_model, Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero))]
  ring

private theorem complex_chart_shape (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) (t : ℂ) (r : ℤ) (hc : complexShape[hw, unit(χ), t, r])
    (z : ℂ) : complexShape[hw, chart∞[w, χ] z, z + t, r] := by
  intro x
  let u := Units.map (complexModel(hw)).symm.toMonoidHom x
  change unit(χ) u * ((((m∞(w) u : ℝ≥0) : ℝ)) : ℂ) ^ z = _
  rw [hc x, complex_module_model, Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero)))]
  ring

/-- The inverse of a real unitary character has the negated exponent and the same parity. -/
private theorem real_inv_shape (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (t : ℂ) (a : Fin 2) (hc : realShape[hw, unit(χ), t, a]) :
    realShape[hw, unit(χ⁻¹), -t, a] := by
  intro x
  have h := hc x
  change ((χ (Units.map (realModel(hw)).symm.toMonoidHom x) : Circle) : ℂ) = _ at h
  change ((χ (Units.map (realModel(hw)).symm.toMonoidHom x) : Circle) : ℂ)⁻¹ = _
  rw [h, mul_inv, Complex.cpow_neg]
  congr 1
  fin_cases a <;> by_cases hx : 0 < (x : ℝ) <;> simp [hx]

/-- The inverse of a complex unitary character has the negated exponent and weight. -/
private theorem complex_inv_shape (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) (t : ℂ) (r : ℤ)
    (hc : complexShape[hw, unit(χ), t, r]) :
    complexShape[hw, unit(χ⁻¹), -t, -r] := by
  intro x
  have h := hc x
  change ((χ (Units.map (complexModel(hw)).symm.toMonoidHom x) : Circle) : ℂ) = _ at h
  change ((χ (Units.map (complexModel(hw)).symm.toMonoidHom x) : Circle) : ℂ)⁻¹ = _
  rw [h, mul_inv, Complex.cpow_neg, zpow_neg]

private theorem real_euler_of_shape (w : InfinitePlace F) (hw : w.IsReal)
    (c : QuasiCharacter w.Completionˣ) (z : ℂ) (a : Fin 2) (h : realShape[hw, c, z, a]) :
    infiniteLocalEulerFactor w c = Complex.Gammaℝ (z + a.val) := by
  have hp := (realLocalEulerParameters w hw c).unique
    (realLocalEulerParameters w hw c).exists.choose_spec (y₂ := (z, a)) h
  simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hp]

private theorem complex_euler_of_shape (w : InfinitePlace F) (hw : w.IsComplex)
    (c : QuasiCharacter w.Completionˣ) (z : ℂ) (r : ℤ) (h : complexShape[hw, c, z, r]) :
    infiniteLocalEulerFactor w c = Complex.Gammaℂ (z + r.natAbs / 2) / 2 := by
  have hp := (complexLocalEulerParameters w hw c).unique
    (complexLocalEulerParameters w hw c).exists.choose_spec (y₂ := (z, r)) h
  simp only [infiniteLocalEulerFactor, InfinitePlace.not_isReal_iff_isComplex.mpr hw,
    ↓reduceDIte, hp]

/-- The archimedean epsilon factor is a power of `i`. -/
theorem norm_infiniteLocalEpsilonFactor (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) :
    ‖infiniteLocalEpsilonFactor w c‖ = 1 := by
  unfold infiniteLocalEpsilonFactor
  split_ifs <;> simp

/-- At a finite place, a unitary chart takes a value of modulus `q ^ (-Re w)` at a uniformizer. -/
private theorem norm_chart_uniformizer (v : Primes) (η : PontryaginDual (v.adicCompletion F)ˣ)
    (π : (v.adicCompletion F)ˣ) (hπ : ‖(π : v.adicCompletion F)‖ = (q(v) : ℝ)⁻¹) (w : ℂ) :
    ‖chart𝔭[v, η] w π‖ = (q(v) : ℝ) ^ (-w.re) := by
  have hq : (0 : ℝ) < q(v) := by
    exact_mod_cast zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)
  change ‖((η π : Circle) : ℂ) * ((((m𝔭(v) π : ℝ≥0) : ℝ)) : ℂ) ^ w‖ = _
  have hm : (((m𝔭(v) π : ℝ≥0) : ℝ)) = (q(v) : ℝ)⁻¹ := by
    change ((‖(π : v.adicCompletion F)‖₊ : ℝ≥0) : ℝ) = _
    rw [coe_nnNorm, hπ]
  rw [norm_mul, hm, norm_ofReal_cpow_of_pos (inv_pos.mpr hq), Real.inv_rpow hq.le,
    ← Real.rpow_neg hq.le, Circle.norm_coe, one_mul]

private theorem norm_inv_one_sub_le {u : ℂ} {b : ℝ} (hu : ‖u‖ = b) (hb : b < 1) :
    ‖(1 - u)⁻¹‖ ≤ (1 - b)⁻¹ := by
  have h1 : 1 - b ≤ ‖1 - u‖ := by
    have := norm_sub_norm_le (1 : ℂ) u
    rw [norm_one, hu] at this; exact this
  rw [norm_inv]
  exact inv_anti₀ (sub_pos.mpr hb) h1

/-- At a finite place and positive abscissa, the Euler factor of a unitary chart is at most
`(1 - q ^ (-Re w))⁻¹`. -/
theorem norm_finiteLocalEulerFactor_chart_le (v : Primes) (η : PontryaginDual (v.adicCompletion F)ˣ)
    {w : ℂ} (hw : 0 < w.re) :
    ‖finiteLocalEulerFactor v (chart𝔭[v, η] w)‖ ≤ (1 - (q(v) : ℝ) ^ (-w.re))⁻¹ := by
  have hq1 : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hlt : (q(v) : ℝ) ^ (-w.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hq1 (neg_neg_of_pos hw)
  have hpos : 0 < 1 - (q(v) : ℝ) ^ (-w.re) := sub_pos.mpr hlt
  unfold finiteLocalEulerFactor
  split_ifs with hun
  · exact norm_inv_one_sub_le (norm_chart_uniformizer v η _
      (norm_uniformizer_adicCompletion v _ (Valued.v : Valuation (v.adicCompletion F)
        (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec) w) hlt
  · rw [norm_one]
    exact one_le_inv₀ hpos |>.mpr (by linarith [Real.rpow_nonneg (zero_le_one.trans hq1.le) (-w.re)])

/-- At a finite place, the reciprocal of the Euler factor of a unitary chart is at most
`1 + q ^ (-Re w)`. -/
theorem norm_inv_finiteLocalEulerFactor_chart_le (v : Primes)
    (η : PontryaginDual (v.adicCompletion F)ˣ) (w : ℂ) :
    ‖(finiteLocalEulerFactor v (chart𝔭[v, η] w))⁻¹‖ ≤ 1 + (q(v) : ℝ) ^ (-w.re) := by
  have hq : (0 : ℝ) ≤ q(v) := Nat.cast_nonneg _
  unfold finiteLocalEulerFactor
  split_ifs with hun
  · rw [inv_inv]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, norm_chart_uniformizer v η _
      (norm_uniformizer_adicCompletion v _ (Valued.v : Valuation (v.adicCompletion F)
        (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec) w]
  · rw [inv_one, norm_one]
    linarith [Real.rpow_nonneg hq (-w.re)]

/-- At a finite place a unitary chart is periodic in the imaginary direction, with period
`2π / log q`, since the local norm takes values in the integral powers of `q`. -/
private theorem chart𝔭_add_period (v : Primes) (η : PontryaginDual (v.adicCompletion F)ˣ)
    (z : ℂ) :
    chart𝔭[v, η] (z + (2 * Real.pi / Real.log (q(v) : ℝ) : ℝ) * I) = chart𝔭[v, η] z := by
  have hq1 : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  have hlog : Real.log (q(v) : ℝ) ≠ 0 := (Real.log_pos hq1).ne'
  ext1 g
  change ((η g : Circle) : ℂ) * ((((m𝔭(v) g : ℝ≥0) : ℝ)) : ℂ) ^ (z + _) =
    ((η g : Circle) : ℂ) * ((((m𝔭(v) g : ℝ≥0) : ℝ)) : ℂ) ^ z
  have hg : (g : v.adicCompletion F) ≠ 0 := g.ne_zero
  have hm : (((m𝔭(v) g : ℝ≥0) : ℝ)) = (q(v) : ℝ) ^ (WithZero.log (Valued.v (g : v.adicCompletion F))) := by
    change ((‖(g : v.adicCompletion F)‖₊ : ℝ≥0) : ℝ) = _
    rw [coe_nnNorm, norm_adicCompletion_eq_zpow F v hg]
  set k : ℤ := WithZero.log (Valued.v (g : v.adicCompletion F))
  have hpos : (0 : ℝ) < (q(v) : ℝ) ^ k := zpow_pos (by linarith) k
  have hne : ((((m𝔭(v) g : ℝ≥0) : ℝ)) : ℂ) ≠ 0 := by
    rw [hm]; exact_mod_cast hpos.ne'
  rw [Complex.cpow_add _ _ hne]
  have hone : ((((m𝔭(v) g : ℝ≥0) : ℝ)) : ℂ) ^ (((2 * Real.pi / Real.log (q(v) : ℝ) : ℝ) : ℂ) * I) = 1 := by
    rw [Complex.cpow_def_of_ne_zero hne, hm, ← Complex.ofReal_log hpos.le, Real.log_zpow]
    have hr : (k : ℝ) * Real.log (q(v) : ℝ) * (2 * Real.pi / Real.log (q(v) : ℝ)) =
        k * (2 * Real.pi) := by
      field_simp
    have : ((((k : ℝ) * Real.log (q(v) : ℝ) : ℝ)) : ℂ) *
        (((2 * Real.pi / Real.log (q(v) : ℝ) : ℝ) : ℂ) * I) = (k : ℂ) * (2 * Real.pi * I) := by
      calc ((((k : ℝ) * Real.log (q(v) : ℝ) : ℝ)) : ℂ) *
            (((2 * Real.pi / Real.log (q(v) : ℝ) : ℝ) : ℂ) * I)
          = ((((k : ℝ) * Real.log (q(v) : ℝ) * (2 * Real.pi / Real.log (q(v) : ℝ)) : ℝ)) : ℂ) * I := by
            rw [Complex.ofReal_mul ((k : ℝ) * Real.log (q(v) : ℝ))]; ring
        _ = (((k * (2 * Real.pi) : ℝ)) : ℂ) * I := by rw [hr]
        _ = (k : ℂ) * (2 * Real.pi * I) := by push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [hone, mul_one]

/-- At a finite place the epsilon factor of a unitary chart is bounded on every vertical strip. -/
theorem exists_norm_finiteLocalEpsilonFactor_chart_le (v : Primes)
    (η : PontryaginDual (v.adicCompletion F)ˣ) (x₀ x₁ : ℝ) :
    ∃ C : ℝ, ∀ z : ℂ, x₀ ≤ z.re → z.re ≤ x₁ →
      ‖finiteLocalEpsilonFactor v (chart𝔭[v, η] z)‖ ≤ C := by
  have hq1 : (1 : ℝ) < q(v) := by exact_mod_cast HeightOneSpectrum.one_lt_absNorm v
  set P : ℝ := 2 * Real.pi / Real.log (q(v) : ℝ)
  have hP : 0 < P := div_pos (by positivity) (Real.log_pos hq1)
  let f : ℂ → ℂ := finiteLocalEpsilonFactor v ∘ chart𝔭[v, η]
  have hf : Continuous f := continuousOn_univ.mp (finiteLocalEpsilonFactor_entire v η).continuousOn
  have hper : Function.Periodic f ((P : ℂ) * I) := fun z ↦ by
    change finiteLocalEpsilonFactor v (chart𝔭[v, η] (z + (P : ℂ) * I)) =
      finiteLocalEpsilonFactor v (chart𝔭[v, η] z)
    rw [chart𝔭_add_period]
  obtain ⟨C, hC⟩ := (isCompact_Icc.reProdIm (isCompact_Icc (a := (0 : ℝ)) (b := P))).exists_bound_of_continuousOn
    (s := Icc x₀ x₁ ×ℂ Icc 0 P) hf.continuousOn
  refine ⟨C, fun z hz₀ hz₁ ↦ ?_⟩
  let n : ℤ := ⌊z.im / P⌋
  have hshift := hper.sub_int_mul_eq (x := z) n
  have hmem : z - (n : ℂ) * ((P : ℂ) * I) ∈ Icc x₀ x₁ ×ℂ Icc 0 P := by
    have hre : (z - (n : ℂ) * ((P : ℂ) * I)).re = z.re := by simp
    have him : (z - (n : ℂ) * ((P : ℂ) * I)).im = z.im - n * P := by simp
    rw [Complex.mem_reProdIm, hre, him]
    have h1 := Int.floor_le (z.im / P)
    have h2 := Int.lt_floor_add_one (z.im / P)
    rw [le_div_iff₀ hP] at h1
    rw [div_lt_iff₀ hP] at h2
    exact ⟨⟨hz₀, hz₁⟩, by constructor <;> nlinarith⟩
  have h := hC _ hmem
  rw [hshift] at h
  exact h

/-- At an archimedean place, the Euler factor of the restricted chart at `z` divided by that of
the restricted inverse chart at `1 - z` is at most a constant times
`|Im z| ^ (mult w · (Re z - 1/2))` on a vertical strip of positive abscissa, at large height. -/
private theorem exists_infinite_euler_ratio_le (χ : PontryaginDual Jₛ) (w : InfinitePlace F)
    {x₀ x₁ : ℝ} (hx₀ : 0 < x₀) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ z : ℂ, x₀ ≤ z.re → z.re ≤ x₁ → T ≤ |z.im| →
      ‖infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z))‖ /
        ‖infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ⁻¹) (1 - z)))‖ ≤
      C * |z.im| ^ ((InfinitePlace.mult w : ℝ) * (z.re - 1 / 2)) := by
  obtain ⟨i, hi⟩ := exists_infiniteInsertion_chart (S := S) w
  have hinv : (χ⁻¹).comp i = (χ.comp i)⁻¹ := ContinuousMonoidHom.ext fun _ ↦ rfl
  by_cases hw : w.IsReal
  · obtain ⟨t, a, ht, hsh⟩ := real_unitary_shape w hw (χ.comp i)
    have hsh' := real_inv_shape w hw (χ.comp i) t a hsh
    obtain ⟨C, T, hC, hT, hb⟩ :=
      exists_norm_Gammaℝ_div_le (a := (a.val : ℝ)) (by positivity) (x₁ := x₁) hx₀ t ht
    refine ⟨C, T, hC, hT, fun z h0 h1 hT' ↦ ?_⟩
    have hmult : (InfinitePlace.mult w : ℝ) = 1 := by simp [InfinitePlace.mult, hw]
    rw [hi χ z]
    erw [hi χ⁻¹ (1 - z)]
    rw [hinv, real_euler_of_shape w hw _ _ _ (real_chart_shape w hw _ t a hsh z),
      real_euler_of_shape w hw _ _ _ (real_chart_shape w hw _ (-t) a hsh' (1 - z)), ← norm_div,
      hmult, one_mul]
    have harg : 1 - z + -t + ((a.val : ℕ) : ℂ) = 1 - (z + t) + (((a.val : ℕ) : ℝ) : ℂ) := by
      push_cast; ring
    have harg' : z + t + ((a.val : ℕ) : ℂ) = z + t + (((a.val : ℕ) : ℝ) : ℂ) := by push_cast; ring
    rw [harg, harg']
    exact hb z h0 h1 hT'
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    obtain ⟨t, r, ht, hsh⟩ := complex_unitary_shape w hc (χ.comp i)
    have hsh' := complex_inv_shape w hc (χ.comp i) t r hsh
    obtain ⟨C, T, hC, hT, hb⟩ :=
      exists_norm_Gammaℂ_div_le (r := (r.natAbs : ℝ) / 2) (by positivity) (x₁ := x₁) hx₀ t ht
    refine ⟨C, T, hC, hT, fun z h0 h1 hT' ↦ ?_⟩
    have hmult : (InfinitePlace.mult w : ℝ) = 2 := by
      simp [InfinitePlace.mult, hw]
    rw [hi χ z]
    erw [hi χ⁻¹ (1 - z)]
    rw [hinv, complex_euler_of_shape w hc _ _ _ (complex_chart_shape w hc _ t r hsh z),
      complex_euler_of_shape w hc _ _ _ (complex_chart_shape w hc _ (-t) (-r) hsh' (1 - z)),
      Int.natAbs_neg, norm_div, norm_div, div_div_div_cancel_right₀ (by norm_num), ← norm_div,
      hmult]
    have harg : 1 - z + -t + ((r.natAbs : ℕ) : ℂ) / 2 =
        1 - (z + t) + (((r.natAbs : ℕ) : ℝ) / 2 : ℝ) := by push_cast; ring
    have harg' : z + t + ((r.natAbs : ℕ) : ℂ) / 2 = z + t + (((r.natAbs : ℕ) : ℝ) / 2 : ℝ) := by
      push_cast; ring
    rw [harg, harg']
    exact hb z h0 h1 hT'

/-- Where the factorization of `sLocalRhoFactor_eq_epsilon_mul` holds, the S-local correcting
factor on a vertical strip of positive abscissa is at most a constant times
`|Im z| ^ (n (Re z - 1/2))` at large height, where `n = [F : ℚ]`. -/
private theorem exists_rho_bound_of_factorization (χ : PontryaginDual Jₛ) {x₀ x₁ : ℝ}
    (hx₀ : 0 < x₀) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ z : ℂ, x₀ ≤ z.re → z.re ≤ x₁ → T ≤ |z.im| →
      sLocalRhoFactor (chartₛ(χ) z) = sLocalEpsilonFactor (chartₛ(χ) z) *
        (sLocalHeckeL (chartₛ(χ) z) /
          sLocalHeckeL (dualQuasiCharacter (G := Jₛ) mₛ hmₛ (chartₛ(χ) z))) →
      ‖sLocalRhoFactor (chartₛ(χ) z)‖ ≤
        C * |z.im| ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1 / 2)) := by
  classical
  choose Cw Tw hCw hTw hbw using
    fun w : InfinitePlace F ↦ exists_infinite_euler_ratio_le (S := S) χ w (x₁ := x₁) hx₀
  have hfin_eps : ∀ v : S, ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, x₀ ≤ z.re → z.re ≤ x₁ →
      ‖finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z))‖ ≤ C := by
    intro v
    obtain ⟨i, hi⟩ := exists_finiteInsertion_chart (S := S) v
    obtain ⟨C, hC⟩ := exists_norm_finiteLocalEpsilonFactor_chart_le v.val (χ.comp i) x₀ x₁
    refine ⟨max C 1, by positivity, fun z h0 h1 ↦ ?_⟩
    rw [hi χ z]
    exact (hC z h0 h1).trans (le_max_left _ _)
  choose Ce hCe hbe using hfin_eps
  have hq1 (v : S) : (1 : ℝ) < q(v.val) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  let Q (v : S) : ℝ := (1 - (q(v.val) : ℝ) ^ (-x₀))⁻¹ * (1 + (q(v.val) : ℝ) ^ (x₁ - 1))
  have hlt (v : S) : (q(v.val) : ℝ) ^ (-x₀) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (hq1 v) (neg_neg_of_pos hx₀)
  have hQ (v : S) : 0 < Q v := by
    have := hlt v
    have : 0 < 1 - (q(v.val) : ℝ) ^ (-x₀) := sub_pos.mpr this
    positivity
  have hfin_euler (v : S) (z : ℂ) (h0 : x₀ ≤ z.re) (h1 : z.re ≤ x₁) :
      ‖finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z))‖ /
        ‖finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ⁻¹) (1 - z)))‖ ≤
      Q v := by
    obtain ⟨i, hi⟩ := exists_finiteInsertion_chart (S := S) v
    rw [hi χ z]
    erw [hi χ⁻¹ (1 - z)]
    rw [div_eq_mul_inv, ← norm_inv]
    have hq0 : (0 : ℝ) < q(v.val) := zero_lt_one.trans (hq1 v)
    apply mul_le_mul
    · refine (norm_finiteLocalEulerFactor_chart_le v.val _ (hx₀.trans_le h0)).trans ?_
      apply inv_anti₀ (sub_pos.mpr (hlt v))
      have : (q(v.val) : ℝ) ^ (-z.re) ≤ (q(v.val) : ℝ) ^ (-x₀) :=
        Real.rpow_le_rpow_of_exponent_le (hq1 v).le (by linarith)
      linarith
    · refine (norm_inv_finiteLocalEulerFactor_chart_le v.val _ (1 - z)).trans ?_
      have hre : -(1 - z).re = z.re - 1 := by simp
      rw [hre]
      have : (q(v.val) : ℝ) ^ (z.re - 1) ≤ (q(v.val) : ℝ) ^ (x₁ - 1) :=
        Real.rpow_le_rpow_of_exponent_le (hq1 v).le (by linarith)
      linarith
    · exact norm_nonneg _
    · have := sub_pos.mpr (hlt v); positivity
  have hCwP : 0 < ∏ w, Cw w := Finset.prod_pos fun w _ ↦ hCw w
  have hCeP : 0 < ∏ v, Ce v := Finset.prod_pos fun v _ ↦ hCe v
  have hQP : 0 < ∏ v, Q v := Finset.prod_pos fun v _ ↦ hQ v
  have hTsum : 0 ≤ ∑ w, Tw w := Finset.sum_nonneg fun w _ ↦ (hTw w).le
  refine ⟨(∏ w, Cw w) * (∏ v, Ce v) * (∏ v, Q v), 1 + ∑ w, Tw w,
    mul_pos (mul_pos hCwP hCeP) hQP, by linarith, ?_⟩
  intro z h0 h1 hT heq
  have hTw' (w : InfinitePlace F) : Tw w ≤ |z.im| := by
    have : Tw w ≤ ∑ w, Tw w :=
      Finset.single_le_sum (fun w _ ↦ (hTw w).le) (Finset.mem_univ w)
    linarith
  have him : 0 < |z.im| := lt_of_lt_of_le (by linarith) hT
  rw [heq, dual_sLocal_chart, sLocalEpsilonFactor, sLocalHeckeL, sLocalHeckeL, norm_mul, norm_div,
    norm_mul, norm_mul, norm_mul, norm_prod, norm_prod, norm_prod, norm_prod, norm_prod, norm_prod,
    Finset.prod_eq_one (fun w _ ↦ norm_infiniteLocalEpsilonFactor w _), one_mul, mul_div_mul_comm,
    ← Finset.prod_div_distrib, ← Finset.prod_div_distrib]
  have hW : ∏ w, ‖infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ) z))‖ /
        ‖infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (chartₛ(χ⁻¹) (1 - z)))‖ ≤
      (∏ w, Cw w) * |z.im| ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1 / 2)) := by
    calc _ ≤ ∏ w, (Cw w * |z.im| ^ ((InfinitePlace.mult w : ℝ) * (z.re - 1 / 2))) :=
          Finset.prod_le_prod₀ (fun w _ ↦ by positivity) (fun w _ ↦ hbw w z h0 h1 (hTw' w))
      _ = (∏ w, Cw w) * |z.im| ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1 / 2)) := by
          rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos him, ← Finset.sum_mul,
            ← InfinitePlace.sum_mult_eq, Nat.cast_sum]
  have hE : ∏ v : S, ‖finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z))‖ ≤
      ∏ v, Ce v :=
    Finset.prod_le_prod₀ (fun v _ ↦ norm_nonneg _) (fun v _ ↦ hbe v z h0 h1)
  have hV : ∏ v : S, ‖finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ) z))‖ /
        ‖finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (chartₛ(χ⁻¹) (1 - z)))‖ ≤
      ∏ v, Q v :=
    Finset.prod_le_prod₀ (fun v _ ↦ by positivity) (fun v _ ↦ hfin_euler v z h0 h1)
  calc _ ≤ (∏ v, Ce v) * (((∏ w, Cw w) * |z.im| ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1 / 2))) *
        ∏ v, Q v) := by
        apply mul_le_mul hE (mul_le_mul hW hV (Finset.prod_nonneg fun v _ ↦ by positivity)
          (by positivity)) (mul_nonneg (Finset.prod_nonneg fun w _ ↦ by positivity)
            (Finset.prod_nonneg fun v _ ↦ by positivity)) hCeP.le
    _ = _ := by ring

/-- The S-local correcting factor in a unitary chart is analytic on the right half-plane. -/
private theorem analyticOnNhd_sLocalRho (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) (Complex.re ⁻¹' Ioi (0 : ℝ)) := by
  simpa only [iteratedDeriv_zero] using sLocalRhoFactor_iteratedDeriv_analyticOn χ 0

/-- Paper: Proposition 3.3.1.5(3), (3.3.1.11), p. 132, for `k = 0`, on vertical strips.
On a vertical strip of positive abscissa and at large height, the S-local correcting factor in a
unitary chart is at most a constant times `|Im z| ^ (n (Re z - 1/2))`, where `n = [F : ℚ]`.
Deviation: The exponent carries the degree `n = r₁ + 2 r₂`, which the printed bound omits
(ERRATA F16). -/
theorem exists_norm_sLocalRhoFactor_le (χ : PontryaginDual Jₛ) {x₀ x₁ : ℝ} (hx₀ : 0 < x₀) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ z : ℂ, x₀ ≤ z.re → z.re ≤ x₁ → T ≤ |z.im| →
      ‖sLocalRhoFactor (chartₛ(χ) z)‖ ≤
        C * |z.im| ^ ((Module.finrank ℚ F : ℝ) * (z.re - 1 / 2)) := by
  obtain ⟨C, T, hC, hT, hb⟩ :=
    exists_rho_bound_of_factorization (S := S) χ (x₀ := x₀ / 2) (x₁ := x₁ + 1) (by positivity)
  refine ⟨C, T + 1, hC, by linarith, fun z h0 h1 hT' ↦ ?_⟩
  let n : ℝ := Module.finrank ℚ F
  let B : ℂ → ℝ := fun y ↦ C * |y.im| ^ (n * (y.re - 1 / 2))
  have hU : ∀ᶠ y in 𝓝 z, x₀ / 2 < y.re ∧ y.re < x₁ + 1 ∧ T < |y.im| := by
    have h1' : x₀ / 2 < z.re := by linarith
    have h2' : z.re < x₁ + 1 := by linarith
    have h3' : T < |z.im| := by linarith
    filter_upwards [continuousAt_const.eventually_lt Complex.continuous_re.continuousAt h1',
      Complex.continuous_re.continuousAt.eventually_lt continuousAt_const h2',
      continuousAt_const.eventually_lt (continuous_abs.comp Complex.continuous_im).continuousAt h3']
      with y hy1 hy2 hy3
    exact ⟨hy1, hy2, hy3⟩
  have hgood := (sLocalRhoFactor_eq_epsilon_mul (S := S) χ).filter_mono (nhdsNE_le_codiscrete z)
  have hev : ∀ᶠ y in 𝓝[≠] z, ‖sLocalRhoFactor (chartₛ(χ) y)‖ ≤ B y := by
    filter_upwards [hgood, nhdsWithin_le_nhds hU] with y hy hyU
    exact hb y hyU.1.le hyU.2.1.le hyU.2.2.le hy
  have hzpos : 0 < z.re := by linarith
  have hρ : ContinuousAt (fun y ↦ ‖sLocalRhoFactor (chartₛ(χ) y)‖) z :=
    ((analyticOnNhd_sLocalRho χ z hzpos).continuousAt).norm
  have him : 0 < |z.im| := by linarith
  have hB : ContinuousAt B z := by
    apply continuousAt_const.mul
    apply ContinuousAt.rpow (continuous_abs.comp Complex.continuous_im).continuousAt
      (continuousAt_const.mul (Complex.continuous_re.continuousAt.sub continuousAt_const))
    exact Or.inl him.ne'
  exact le_of_tendsto_of_tendsto (hρ.tendsto.mono_left nhdsWithin_le_nhds)
    (hB.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- Paper: Proposition 3.3.1.5(3), (3.3.1.11), p. 132. On the vertical line of abscissa `σ > 0`,
the `k`th complex derivative of the S-local correcting factor in a unitary chart is at most a
constant times `|τ| ^ (n (σ - 1/2)) (log |τ|) ^ k` for large `|τ|`, where `n = [F : ℚ]`.
Deviation: The exponent of `|τ|` is `n (σ - 1/2)` with `n = r₁ + 2 r₂`. The printed exponent
`σ - 1/2` omits the archimedean degrees and is refuted in
`Printed.sLocalRhoFactor_iteratedDeriv_isBigO_false` (ERRATA F16). -/
theorem exists_norm_iteratedDeriv_sLocalRhoFactor_le (χ : PontryaginDual Jₛ) (k : ℕ) {σ : ℝ}
    (hσ : 0 < σ) :
    ∃ C T : ℝ, 0 < C ∧ 1 < T ∧ ∀ t : ℝ, T ≤ |t| →
      ‖iteratedDeriv k (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) ((σ : ℂ) + (t : ℂ) * I)‖ ≤
        C * |t| ^ ((Module.finrank ℚ F : ℝ) * (σ - 1 / 2)) * Real.log |t| ^ k := by
  set n : ℝ := (Module.finrank ℚ F : ℝ) with hn
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  obtain ⟨C₀, T₀, hC₀, hT₀, hb⟩ :=
    exists_norm_sLocalRhoFactor_le (S := S) χ (x₀ := σ / 2) (x₁ := σ + 1) (by positivity)
  let B : ℝ := n * (σ + 1) + n
  let C : ℝ := k.factorial * (C₀ * 4 ^ B * 2 ^ B * Real.exp n)
  let T : ℝ := T₀ + 1 + Real.exp (2 / σ) + Real.exp 2
  have hT1 : 1 < T := by
    have h1 := Real.exp_pos (2 / σ)
    have h2 : 1 < Real.exp 2 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith
  refine ⟨C, T, by positivity, hT1, fun t ht ↦ ?_⟩
  have ht1 : 1 ≤ |t| := by have := Real.exp_pos (2 / σ); have := Real.exp_pos 2; linarith
  have htpos : 0 < |t| := by linarith
  set L : ℝ := Real.log |t| with hL
  have hL2 : 2 ≤ L := by
    rw [hL, ← Real.exp_le_exp, Real.exp_log htpos]
    have := Real.exp_pos (2 / σ); linarith
  have hLσ : 2 / σ ≤ L := by
    rw [hL, ← Real.exp_le_exp, Real.exp_log htpos]
    have := Real.exp_pos 2; linarith
  have hLpos : 0 < L := by linarith
  set r : ℝ := L⁻¹ with hr
  have hrpos : 0 < r := inv_pos.mpr hLpos
  have hr_half : r ≤ 1 / 2 := by
    rw [hr]; rw [inv_le_comm₀ hLpos (by norm_num)]; linarith
  have hr_σ : r ≤ σ / 2 := by
    rw [hr, inv_le_comm₀ hLpos (by positivity)]
    calc (σ / 2)⁻¹ = 2 / σ := by field_simp
      _ ≤ L := hLσ
  let c : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hcre : c.re = σ := by simp [c]
  have hcim : c.im = t := by simp [c]
  let f : ℂ → ℂ := fun z ↦ sLocalRhoFactor (chartₛ(χ) z)
  have hfA := analyticOnNhd_sLocalRho (S := S) χ
  have hsub : Metric.closedBall c r ⊆ Complex.re ⁻¹' Ioi (0 : ℝ) := by
    intro w hw
    rw [Metric.mem_closedBall, dist_eq_norm] at hw
    have h := (Complex.abs_re_le_norm (w - c)).trans hw
    rw [Complex.sub_re, hcre, abs_le] at h
    show 0 < w.re
    linarith
  have hD : DiffContOnCl ℂ f (Metric.ball c r) :=
    (hfA.differentiableOn).diffContOnCl_ball hsub
  let M : ℝ := C₀ * 4 ^ B * 2 ^ B * Real.exp n * |t| ^ (n * (σ - 1 / 2))
  have hsphere : ∀ w ∈ Metric.sphere c r, ‖f w‖ ≤ M := by
    intro w hw
    rw [mem_sphere_iff_norm] at hw
    have hre := (Complex.abs_re_le_norm (w - c)).trans hw.le
    have him := (Complex.abs_im_le_norm (w - c)).trans hw.le
    rw [Complex.sub_re, hcre, abs_le] at hre
    rw [Complex.sub_im, hcim] at him
    have him1 : |w.im - t| ≤ 1 / 2 := him.trans hr_half
    have hwim_lo : |t| / 2 ≤ |w.im| := by
      have := abs_sub_abs_le_abs_sub t w.im
      rw [abs_sub_comm] at this; linarith
    have hwim_hi : |w.im| ≤ 2 * |t| := by
      have := abs_sub_abs_le_abs_sub w.im t; linarith
    have hwT : T₀ ≤ |w.im| := by
      have := abs_sub_abs_le_abs_sub t w.im
      rw [abs_sub_comm] at this
      have : T₀ + 1 ≤ |t| := by have := Real.exp_pos (2 / σ); have := Real.exp_pos 2; linarith
      linarith
    have hb' := hb w (by linarith) (by linarith) hwT
    set e : ℝ := n * (w.re - 1 / 2)
    have hw1 : w.re - 1 / 2 ≤ σ + 1 := by linarith [hre.2]
    have hw2 : -1 ≤ w.re - 1 / 2 := by linarith [hre.1]
    have hm1 := mul_le_mul_of_nonneg_left hw1 hn0
    have hm2 := mul_le_mul_of_nonneg_left hw2 hn0
    have hnσ : 0 ≤ n * (σ + 1) := by positivity
    have he : |e| ≤ B := by
      rw [abs_le]; constructor <;> (simp only [e, B]; linarith)
    have h1 : |w.im| ^ e ≤ 4 ^ B * (2 * |t|) ^ e :=
      rpow_le_of_comparable (by positivity) (by linarith) hwim_hi he
    have h2 : (2 * |t|) ^ e ≤ 2 ^ B * |t| ^ e := by
      rw [Real.mul_rpow (by norm_num) htpos.le]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) ((le_abs_self e).trans he))
        (Real.rpow_nonneg htpos.le _)
    have h3 : |t| ^ e ≤ |t| ^ (n * (σ - 1 / 2)) * Real.exp n := by
      have hexp : |t| ^ (n * r) = Real.exp n := by
        rw [Real.rpow_def_of_pos htpos, ← hL, hr]
        congr 1; field_simp
      calc |t| ^ e ≤ |t| ^ (n * (σ - 1 / 2) + n * r) :=
            Real.rpow_le_rpow_of_exponent_le ht1 (by
              have := mul_le_mul_of_nonneg_left
                (show w.re - 1 / 2 ≤ σ - 1 / 2 + r by linarith [hre.2]) hn0
              simp only [e]; linarith)
        _ = |t| ^ (n * (σ - 1 / 2)) * Real.exp n := by rw [Real.rpow_add htpos, hexp]
    calc ‖f w‖ ≤ C₀ * |w.im| ^ e := hb'
      _ ≤ C₀ * (4 ^ B * (2 ^ B * (|t| ^ (n * (σ - 1 / 2)) * Real.exp n))) := by
          gcongr
          exact h1.trans (by gcongr; exact h2.trans (by gcongr))
      _ = M := by ring
  have hcauchy := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hrpos hD hsphere
  calc ‖iteratedDeriv k f c‖ ≤ k.factorial * M / r ^ k := hcauchy
    _ = C * |t| ^ (n * (σ - 1 / 2)) * L ^ k := by
        rw [hr, inv_pow, div_inv_eq_mul]
        ring

/-- Paper: Proposition 3.3.1.5(3), (3.3.1.11), p. 132, on the critical line. There the `k`th
complex derivative of the S-local correcting factor in a unitary chart is at most a constant times
`(log |τ|) ^ k` for large `|τ|`. This is the bound on the derivatives of the Tate phase used for
the reflected coordinates of Theorem 12.4.1.1. -/
theorem exists_norm_iteratedDeriv_sLocalRhoFactor_criticalLine_le (χ : PontryaginDual Jₛ)
    (k : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 1 < T ∧ ∀ t : ℝ, T ≤ |t| →
      ‖iteratedDeriv k (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
        C * Real.log |t| ^ k := by
  obtain ⟨C, T, hC, hT, hb⟩ :=
    exists_norm_iteratedDeriv_sLocalRhoFactor_le (S := S) χ k (σ := 1 / 2) (by norm_num)
  refine ⟨C, T, hC, hT, fun t ht ↦ ?_⟩
  have h := hb t ht
  simpa using h

open Asymptotics in
/-- Paper: Proposition 3.3.1.5(3), (3.3.1.11), p. 132, with the degree in the exponent. On each
vertical line of positive abscissa `σ`, the `k`th complex derivative of the S-local correcting
factor in a unitary chart is `O(|τ| ^ (n (σ - 1/2)) |log |τ|| ^ k)` as `|τ| → ∞`, where
`n = [F : ℚ]`.
Deviation: The printed exponent is `σ - 1/2`; the statement as printed is
`Printed.sLocalRhoFactor_iteratedDeriv_isBigO`, refuted in Lean (ERRATA F16). -/
theorem sLocalRhoFactor_iteratedDeriv_isBigO (χ : PontryaginDual Jₛ) (k : ℕ) {σ : ℝ}
    (hσ : 0 < σ) :
    (fun t : ℝ ↦ iteratedDeriv k (fun z ↦ sLocalRhoFactor (chartₛ(χ) z))
        ((σ : ℂ) + (t : ℂ) * I))
      =O[comap (fun t : ℝ ↦ |t|) atTop]
        (fun t : ℝ ↦ |t| ^ ((Module.finrank ℚ F : ℝ) * (σ - 1 / 2)) * |Real.log (|t|)| ^ k) := by
  obtain ⟨C, T, hC, hT, hb⟩ := exists_norm_iteratedDeriv_sLocalRhoFactor_le (S := S) χ k hσ
  refine IsBigO.of_bound C ?_
  have hev : ∀ᶠ t in comap (fun t : ℝ ↦ |t|) atTop, T ≤ |t| :=
    tendsto_comap.eventually (eventually_ge_atTop T)
  filter_upwards [hev] with t ht
  have ht1 : 1 ≤ |t| := by linarith
  have hlog : 0 ≤ Real.log |t| := Real.log_nonneg ht1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg t) _), abs_pow,
    abs_abs, abs_of_nonneg hlog, ← mul_assoc]
  exact hb t ht

/-- Along the critical line `ξ ↦ 1/2 - 2π i ξ`, the real-variable derivatives of the correcting
factor are the complex derivatives times powers of `-2π i`. -/
private theorem iteratedDeriv_criticalPhase (χ : PontryaginDual Jₛ) (k : ℕ) :
    iteratedDeriv k (fun ξ : ℝ ↦ sLocalRhoFactor (chartₛ(χ) ((1 / 2 : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * I))) =
      fun ξ : ℝ ↦ (-(2 * Real.pi : ℂ) * I) ^ k *
        iteratedDeriv k (fun z ↦ sLocalRhoFactor (chartₛ(χ) z))
          ((1 / 2 : ℂ) + (-(2 * Real.pi : ℂ) * I) * (ξ : ℂ)) := by
  set c : ℂ := -(2 * Real.pi : ℂ) * I
  let f : ℂ → ℂ := fun z ↦ sLocalRhoFactor (chartₛ(χ) z)
  have hre (ξ : ℝ) : 0 < ((1 / 2 : ℂ) + c * (ξ : ℂ)).re := by simp [c]
  have hstep (j : ℕ) (ξ : ℝ) :
      HasDerivAt (fun y : ℝ ↦ c ^ j * iteratedDeriv j f ((1 / 2 : ℂ) + c * (y : ℂ)))
        (c ^ (j + 1) * iteratedDeriv (j + 1) f ((1 / 2 : ℂ) + c * (ξ : ℂ))) ξ := by
    have hA : AnalyticAt ℂ (iteratedDeriv j f) ((1 / 2 : ℂ) + c * (ξ : ℂ)) :=
      sLocalRhoFactor_iteratedDeriv_analyticOn χ j _ (hre ξ)
    have hd : HasDerivAt (iteratedDeriv j f) (iteratedDeriv (j + 1) f ((1 / 2 : ℂ) + c * (ξ : ℂ)))
        ((1 / 2 : ℂ) + c * (ξ : ℂ)) := by
      rw [iteratedDeriv_succ]
      exact hA.differentiableAt.hasDerivAt
    have hlin : HasDerivAt (fun w : ℂ ↦ (1 / 2 : ℂ) + c * w) c (ξ : ℂ) := by
      simpa using ((hasDerivAt_id (ξ : ℂ)).const_mul c).const_add (1 / 2 : ℂ)
    have hcomp := (hd.comp (ξ : ℂ) hlin).const_mul (c ^ j)
    have hreal := hcomp.comp_ofReal
    simp only [Function.comp_def] at hreal
    convert hreal using 1
    ring
  induction k with
  | zero =>
    funext ξ
    simp only [iteratedDeriv_zero, pow_zero, one_mul]
    congr 2
    simp only [c]
    push_cast
    ring
  | succ j ih =>
    rw [iteratedDeriv_succ, ih]
    funext ξ
    exact (hstep j ξ).deriv

/-- Paper: Proposition 3.3.1.5(3), (3.3.1.11), p. 132, on the critical line, in the real variable
`ξ` of the parameter `1/2 - 2π i ξ`. The `k`th derivative of the S-local correcting factor along
the critical line is at most a constant times `(1 + log (2 + |ξ|)) ^ k`, for every real `ξ`. This
is the bound on the derivatives of the Tate phase used for the reflected coordinates of
Theorem 12.4.1.1. -/
theorem exists_norm_iteratedDeriv_criticalPhase_le (χ : PontryaginDual Jₛ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ,
      ‖iteratedDeriv k (fun ξ : ℝ ↦
          sLocalRhoFactor (chartₛ(χ) ((1 / 2 : ℂ) - ((2 * Real.pi * ξ : ℝ) : ℂ) * I))) ξ‖ ≤
        C * (1 + Real.log (2 + |ξ|)) ^ k := by
  obtain ⟨C₁, T, hC₁, hT, hb⟩ :=
    exists_norm_iteratedDeriv_sLocalRhoFactor_criticalLine_le (S := S) χ k
  set c : ℂ := -(2 * Real.pi : ℂ) * I with hc
  let f : ℂ → ℂ := fun z ↦ sLocalRhoFactor (chartₛ(χ) z)
  have hre (ξ : ℝ) : 0 < ((1 / 2 : ℂ) + c * (ξ : ℂ)).re := by simp [c]
  let G : ℝ → ℂ := fun ξ ↦ c ^ k * iteratedDeriv k f ((1 / 2 : ℂ) + c * (ξ : ℂ))
  have hG : Continuous G := by
    refine continuous_const.mul ?_
    exact (sLocalRhoFactor_iteratedDeriv_analyticOn χ k).continuousOn.comp_continuous
      (by fun_prop) hre
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨C₂, hC₂⟩ := (isCompact_Icc (a := -(T / (2 * Real.pi))) (b := T / (2 * Real.pi))
    ).exists_bound_of_continuousOn hG.continuousOn
  have hlog2pi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by linarith [Real.pi_gt_three])
  refine ⟨(2 * Real.pi) ^ k * C₁ * (Real.log (2 * Real.pi) + 1) ^ k + max C₂ 0, by positivity,
    fun ξ ↦ ?_⟩
  rw [iteratedDeriv_criticalPhase]
  change ‖G ξ‖ ≤ _
  have hξ2 : (1 : ℝ) ≤ 2 + |ξ| := by linarith [abs_nonneg ξ]
  have hlogξ : 0 ≤ Real.log (2 + |ξ|) := Real.log_nonneg hξ2
  have hL1 : 1 ≤ (1 + Real.log (2 + |ξ|)) ^ k := one_le_pow₀ (by linarith)
  have hnc : ‖c‖ = 2 * Real.pi := by
    rw [hc, norm_mul, norm_neg, Complex.norm_I, mul_one]
    exact_mod_cast Real.norm_of_nonneg hpi.le
  by_cases hξ : T ≤ |-(2 * Real.pi * ξ)|
  · have hpt : (1 / 2 : ℂ) + c * (ξ : ℂ) = (1 / 2 : ℂ) + ((-(2 * Real.pi * ξ) : ℝ) : ℂ) * I := by
      rw [hc]; push_cast; ring
    have h := hb (-(2 * Real.pi * ξ)) hξ
    have hT1 : 1 ≤ |-(2 * Real.pi * ξ)| := by linarith
    have habs : |-(2 * Real.pi * ξ)| = 2 * Real.pi * |ξ| := by
      rw [abs_neg, abs_mul, abs_of_pos hpi]
    have hlog0 : 0 ≤ Real.log |-(2 * Real.pi * ξ)| := Real.log_nonneg hT1
    have hlogle : Real.log |-(2 * Real.pi * ξ)| ≤
        (Real.log (2 * Real.pi) + 1) * (1 + Real.log (2 + |ξ|)) := by
      have hξpos : 0 < |ξ| := by
        rw [habs] at hT1
        by_contra hne
        have : |ξ| = 0 := le_antisymm (not_lt.mp hne) (abs_nonneg ξ)
        rw [this, mul_zero] at hT1; linarith
      rw [habs, Real.log_mul hpi.ne' hξpos.ne']
      have : Real.log |ξ| ≤ Real.log (2 + |ξ|) := Real.log_le_log hξpos (by linarith)
      nlinarith
    calc ‖G ξ‖ = (2 * Real.pi) ^ k *
          ‖iteratedDeriv k f ((1 / 2 : ℂ) + ((-(2 * Real.pi * ξ) : ℝ) : ℂ) * I)‖ := by
          simp only [G]; rw [norm_mul, norm_pow, hnc, hpt]
      _ ≤ (2 * Real.pi) ^ k * (C₁ * Real.log |-(2 * Real.pi * ξ)| ^ k) := by gcongr
      _ ≤ (2 * Real.pi) ^ k * (C₁ * ((Real.log (2 * Real.pi) + 1) * (1 + Real.log (2 + |ξ|))) ^ k) := by
          gcongr
      _ = (2 * Real.pi) ^ k * C₁ * (Real.log (2 * Real.pi) + 1) ^ k *
            (1 + Real.log (2 + |ξ|)) ^ k := by rw [mul_pow (Real.log (2 * Real.pi) + 1)]; ring
      _ ≤ _ := by
          have : 0 ≤ max C₂ 0 * (1 + Real.log (2 + |ξ|)) ^ k := by positivity
          nlinarith
  · have hmem : ξ ∈ Icc (-(T / (2 * Real.pi))) (T / (2 * Real.pi)) := by
      rw [not_le, abs_neg, abs_mul, abs_of_pos hpi] at hξ
      rw [mem_Icc, ← abs_le, le_div_iff₀ hpi]
      linarith
    have h := hC₂ ξ hmem
    have h0 : 0 ≤ (2 * Real.pi) ^ k * C₁ * (Real.log (2 * Real.pi) + 1) ^ k *
        (1 + Real.log (2 + |ξ|)) ^ k := by positivity
    calc ‖G ξ‖ ≤ max C₂ 0 := h.trans (le_max_left _ _)
      _ ≤ max C₂ 0 * (1 + Real.log (2 + |ξ|)) ^ k :=
          le_mul_of_one_le_right (le_max_right _ _) hL1
      _ ≤ _ := by nlinarith

end LocalFactors

end RiemannMasullo
