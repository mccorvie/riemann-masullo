module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckePoissonFormula
public import RiemannMasullo.AppB_AnalyticNT.Sec7a
import RiemannMasullo.AppB_AnalyticNT.HeckeGammaRecurrence
import RiemannMasullo.ForMathlib.NumberTheory.LSeries.RationalShift
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.Tactic

/-!
# Finite-order Hecke zero-divisor relations and ordinary Euler coefficients

For a finite packet of finite-order idèle-class characters, with arbitrary complex weights,
suppose the weighted orders at each point of the open critical strip vanish outside a finite
set. The weighted ordinary Euler logarithmic derivative then vanishes throughout `1 < Re s`,
and every weighted norm-grouped von Mangoldt coefficient vanishes.

This proves the analytic implication of the full-divisor criterion in the discussion of #5571.
The central line is included with full multiplicity. The complex two-point resolvent and actual
Hecke rectangles are supplied by #7669. The ordinary ideal series and norm coefficients are
those of Masullo, Equations (B.6.1.12)–(B.6.1.14), p. 638.
-/

@[expose] public noncomputable section

open Classical Complex Filter Function NumberField Polynomial Set Topology
open scoped NNReal

namespace RiemannMasullo.HeckeDivisorRigidity

open DirichletShift

variable {K : Type*} [Field K] [NumberField K]
local notation "CK" => IdeleClassGroup (𝓞 K) K
local notation "U" => PontryaginDual CK
local notation "ord(" χ "," z ")" =>
  MeromorphicOn.divisor (continuedCompletedHeckeL (F := K) χ) univ z

local notation "posOrder(" χ "," z ")" => Int.toNat (ord(χ,z))

/-- The logarithmic derivative after compensating the two simple principal poles. -/
def correctedCompletedLogDeriv (χ : U) (z : ℂ) : ℂ :=
  logDeriv (continuedCompletedHeckeL χ) z +
    if χ = 1 then 1/z + 1/(z-1) else 0

private theorem euler_order (χ : U) (s : ℂ) (hs : 1 < s.re) :
    meromorphicOrderAt (continuedCompletedHeckeL χ) s = 0 := by
  have hL := continuedCompletedHeckeL_spec χ
  apply (hL.1 (mem_univ _)).meromorphicOrderAt_eq_zero_iff.mpr
  rw [hL.2 ⟨s,hs⟩]
  exact mul_ne_zero (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hs))
    (finiteHeckeL_ne_zero_of_one_lt_re χ _)

/-- The positive orders on the whole plane sum to the actual corrected completed
logarithmic derivative difference, for any two points in the Euler half-plane. -/
private theorem hasSum_positiveOrder_two_points
    (τ : ℝ≥0ˣ →ₜ* CK) (hτ : RightInverse τ (ideleClassNorm K))
    (χ : U) (hχ : ∀ r : ℝ≥0ˣ, χ (τ r) = 1)
    (z b : ℂ) (hz : 1 < z.re) (hb : 1 < b.re) :
    HasSum (fun p : ℂ ↦ (posOrder(χ,p) : ℂ) * (1/(z-p) - 1/(b-p)))
      (correctedCompletedLogDeriv χ z - correctedCompletedLogDeriv χ b) := by
  let L := continuedCompletedHeckeL χ
  let r (p : ℂ) := 1/(z-p) - 1/(b-p)
  have hL := continuedCompletedHeckeL_spec χ
  have hz₀ := euler_order χ z hz
  have hb₀ := euler_order χ b hb
  have hreg (u : ℂ) (hu : meromorphicOrderAt L u = 0) : AnalyticAt ℂ (logDeriv L) u := by
    have hm := hL.1 (mem_univ u)
    have ha := hm.meromorphicOrderAt_nonneg_iff_analyticAt.mp hu.ge
    exact ha.deriv.div ha (hm.meromorphicOrderAt_eq_zero_iff.mp hu)
  have hfinite (u : ℂ) : meromorphicOrderAt L u ≠ ⊤ :=
    hL.1.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
      (mem_univ z) (mem_univ u) (by rw [hz₀]; exact WithTop.coe_ne_top)
  have hpos : Summable (fun p : HeckePoisson.Site χ ↦ (HeckePoisson.multiplicity p : ℂ)*r p.val) := by
    apply HeckePoisson.summable_site_resolvent_difference
    · intro p he
      exact (HeckePoisson.siteStrip p).2.not_gt (he ▸ hz)
    · intro p he
      exact (HeckePoisson.siteStrip p).2.not_gt (he ▸ hb)
  have htot := HeckePoisson.hasSum_normalized_signed_divisor τ hτ χ hχ r hpos
  let signed (u : ℂ) := (ord(χ,u) : ℂ)*r u
  let D := {u : ℂ | meromorphicOrderAt L u ≠ 0}
  have hsub : support signed ⊆ D := by
    intro u hu hzero
    apply hu
    change meromorphicOrderAt (continuedCompletedHeckeL χ) u = 0 at hzero
    simp [signed, MeromorphicOn.divisor_apply hL.1.meromorphicOn (mem_univ u), hzero]
  have hsd := (hasSum_subtype_iff_of_support_subset hsub).mpr htot
  have he (u : D) : signed u.val =
      ((meromorphicOrderAt L u.val).untop₀ : ℂ) * (1/(z-u.val)-1/(b-u.val)) := by
    dsimp only [signed, r, L]
    rw [MeromorphicOn.divisor_apply hL.1.meromorphicOn (mem_univ u.val)]
  have h₂ := hsd.congr_fun (fun u ↦ (he u).symm)
  obtain ⟨A,B,M,hbox,hsmall⟩ := ResolventRectangle.exists_sublinear_regularHeckeBoxes χ
  have h₃ := ResolventRectangle.hasSum_divisor_resolvent_of_sublinear_boxes L hL.1.meromorphicOn
    hfinite z b hz₀ hb₀ (hreg z hz₀) (hreg b hb₀) A B M hbox hsmall h₂.summable
  have hx := h₂.unique h₃
  let pos (p : ℂ) := (posOrder(χ,p) : ℂ)*r p
  have hsupp : support pos ⊆ {p : ℂ | 0 < ord(χ,p)} := by
    intro u hu
    by_contra hneg
    change ¬ 0 < ord(χ,u) at hneg
    have hzero : (ord(χ,u)).toNat = 0 := by omega
    exact hu (by simp [pos, hzero])
  apply (hasSum_subtype_iff_of_support_subset hsupp).mp
  change HasSum (fun p : HeckePoisson.Site χ ↦ (HeckePoisson.multiplicity p : ℂ)*r p.val) _
  suffices hp : (∑' p : HeckePoisson.Site χ, (HeckePoisson.multiplicity p : ℂ)*r p.val) =
      correctedCompletedLogDeriv χ z - correctedCompletedLogDeriv χ b by
    exact hp ▸ hpos.hasSum
  change (∑' p : HeckePoisson.Site χ, (HeckePoisson.multiplicity p : ℂ)*r p.val) -
    (if χ = 1 then r 0+r 1 else 0) = logDeriv L z - logDeriv L b at hx
  by_cases ht : χ = 1
  · simp only [correctedCompletedLogDeriv, ite_eq_left ht, r, sub_zero] at hx ⊢
    dsimp only [L] at hx
    linear_combination hx
  · simpa only [correctedCompletedLogDeriv, ite_eq_right ht, add_zero, sub_zero, L] using hx

/-- If the weighted orders cancel in the open critical strip off a specified finite set,
its complete contribution is exactly the finite two-point Cauchy sum over that set. -/
private theorem weighted_completed_two_points_of_finite_exceptions {ι : Type*}
    (τ : ℝ≥0ˣ →ₜ* CK) (hτ : RightInverse τ (ideleClassNorm K))
    (rows : Finset ι) (χ : ι → U) (c : ι → ℂ)
    (hnorm : ∀ i ∈ rows, ∀ r : ℝ≥0ˣ, χ i (τ r) = 1)
    (E : Finset ℂ)
    (hvan : ∀ p : ℂ, p.re ∈ Ioo (0 : ℝ) 1 → p ∉ E →
      ∑ i ∈ rows, c i * (posOrder(χ i,p) : ℂ) = 0)
    (z b : ℂ) (hz : 1 < z.re) (hb : 1 < b.re) :
    (∑ i ∈ rows, c i * (correctedCompletedLogDeriv (χ i) z -
      correctedCompletedLogDeriv (χ i) b)) =
    ∑ p ∈ E, (∑ i ∈ rows, c i * (posOrder(χ i,p) : ℂ)) * (1/(z-p) - 1/(b-p)) := by
  let r (p : ℂ) := 1/(z-p) - 1/(b-p)
  have hrows := hasSum_sum (s := rows) fun i hi ↦
    (hasSum_positiveOrder_two_points τ hτ (χ i) (hnorm i hi) z b hz hb).mul_left (c i)
  let t (p : ℂ) := (∑ i ∈ rows, c i * (posOrder(χ i,p) : ℂ))*r p
  have hsum : HasSum t (∑ i ∈ rows, c i * (correctedCompletedLogDeriv (χ i) z -
      correctedCompletedLogDeriv (χ i) b)) := by
    apply hrows.congr_fun
    intro p
    simp [t, r, Finset.sum_mul, mul_assoc]
  apply hsum.unique
  apply hasSum_sum_of_ne_finset_zero
  intro p hp
  by_cases hstrip : p.re ∈ Ioo (0 : ℝ) 1
  · simp [t, hvan p hstrip hp]
  · have he (i : ι) : posOrder(χ i,p) = 0 := by
      have hneg := mt (HeckePoisson.positive_divisor_re_mem_Ioo (χ i) (z := p)) hstrip
      omega
    simp [t, he]

/-- A finite-order character is trivial on the image of any homomorphism
from the positive real norm group, since that group has roots of all orders. -/
private theorem finiteOrder_trivial_on_section (χ : U) (hfin : IsOfFinOrder χ)
    (τ : ℝ≥0ˣ →ₜ* CK) (r : ℝ≥0ˣ) : χ (τ r) = 1 := by
  obtain ⟨n, hn, hpow⟩ := hfin.exists_pow_eq_one
  let v : ℝ≥0ˣ := Units.mk0 (r.val ^ (1 / (n : ℝ)))
    (NNReal.rpow_pos (Units.zero_lt r)).ne'
  have hv : v ^ n = r := by
    apply Units.ext
    change (r.val ^ (1 / (n : ℝ))) ^ n = r.val
    rw [← NNReal.rpow_natCast]
    exact NNReal.rpow_self_rpow_inv (Nat.cast_ne_zero.mpr hn.ne') _
  rw [← hv, map_pow, map_pow]
  exact (ContinuousMonoidHom.pow_apply (χ : CK →ₜ* Circle) n (τ v)).symm.trans
    (DFunLike.congr_fun hpow (τ v))

/-- For finite-order rows on any number field the arithmetic hypotheses suffice.
Neither a choice of norm section nor a normalization assumption enters the statement. -/
theorem finiteOrder_completed_two_points_of_finite_exceptions {ι : Type*}
    (rows : Finset ι) (χ : ι → U) (c : ι → ℂ)
    (hfin : ∀ i ∈ rows, IsOfFinOrder (χ i))
    (E : Finset ℂ)
    (hvan : ∀ p : ℂ, p.re ∈ Ioo (0 : ℝ) 1 → p ∉ E →
      ∑ i ∈ rows, c i * (posOrder(χ i,p) : ℂ) = 0)
    (z b : ℂ) (hz : 1 < z.re) (hb : 1 < b.re) :
    (∑ i ∈ rows, c i * (correctedCompletedLogDeriv (χ i) z -
      correctedCompletedLogDeriv (χ i) b)) =
    ∑ p ∈ E, (∑ i ∈ rows, c i * (posOrder(χ i,p) : ℂ)) * (1/(z-p) - 1/(b-p)) := by
  let τ : ℝ≥0ˣ →ₜ* CK := (⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩ :
    IdeleGroup (𝓞 K) K →ₜ* CK).comp
      ⟨canonicalIdeleNormSection K, canonicalIdeleNormSection_continuous K⟩
  have hτ : RightInverse τ (ideleClassNorm K) := canonicalIdeleNormSection_rightInverse K
  exact weighted_completed_two_points_of_finite_exceptions τ hτ rows χ c
    (fun i hi ↦ finiteOrder_trivial_on_section (χ i) (hfin i hi) τ) E hvan z b hz hb

/-- The meromorphic continuation of the ordinary finite Hecke Euler series. -/
abbrev ordinary (χ : U) : ℂ → ℂ := (finiteHeckeL_exists_continuation χ).choose

/-- Paper: Equation (B.6.1.14), p. 638. The coefficient at positive integral norm
of the negative ordinary logarithmic derivative, summed with the packet weights. -/
def packetCoefficient {ι : Type*} (rows : Finset ι) (χ : ι → U) (c : ι → ℂ) : ℕ → ℂ :=
  ∑ i ∈ rows, c i • heckeLogDerivCoefficient (ideleClassNormTwist (χ i) 0)

/-- Sum the ordinary Euler logarithmic derivatives over the finite packet and group the
ideal terms by their positive integral norms. -/
private theorem packet_hasSum {ι : Type*} (rows : Finset ι) (χ : ι → U) (c : ι → ℂ)
    {s : ℂ} (hs : 1 < s.re) : LSeriesHasSum (packetCoefficient rows χ c) s
    (∑ i ∈ rows, c i * (-logDeriv (ordinary (χ i)) s)) := by
  classical
  let J := {I : Ideal (𝓞 K) // I ≠ ⊥}
  let v (i : ι) (I : Ideal (𝓞 K)) := heckeIdealVonMangoldt (ideleClassNormTwist (χ i) 0) I
  have hideals : HasSum (fun I : J ↦ ∑ i ∈ rows, c i * (v i I.val / (I.val.absNorm : ℂ)^s))
      (∑ i ∈ rows, c i * (-logDeriv (ordinary (χ i)) s)) := by
    refine hasSum_sum fun i _ ↦ ?_
    have hL := (finiteHeckeL_exists_continuation (χ i)).choose_spec
    exact (finiteHeckeL_negLogDeriv_hasSum_ideals (χ i) (ordinary (χ i)) hL.1 hL.2 ⟨s,hs⟩).mul_left (c i)
  refine (hideals.tsum_fiberwise (fun I : J ↦ I.val.absNorm)).congr_fun fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have : IsEmpty ↑((fun I : J ↦ I.val.absNorm) ⁻¹' {0}) :=
      ⟨fun b ↦ b.val.property (Ideal.absNorm_eq_zero_iff.mp b.property)⟩
    rw [tsum_empty, LSeries.term_zero]
  · let A := {I : Ideal (𝓞 K) // I ≠ ⊥ ∧ I.absNorm = n}
    have hf : {I : Ideal (𝓞 K) | I ≠ ⊥ ∧ I.absNorm = n}.Finite :=
      (Ring.HasFiniteQuotients.finite_absNorm_eq (S := 𝓞 K) n).subset fun _ h ↦ h.2
    have : Finite A := hf.to_subtype
    let : Fintype A := Fintype.ofFinite _
    let e : ↑((fun I : J ↦ I.val.absNorm) ⁻¹' {n}) ≃ A :=
      { toFun := fun b ↦ ⟨b.val.val, b.val.property, b.property⟩
        invFun := fun I ↦ ⟨⟨I.val,I.property.1⟩,I.property.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    rw [← e.symm.tsum_eq, tsum_fintype, LSeries.term_of_ne_zero hn]
    simp only [packetCoefficient, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      heckeLogDerivCoefficient, finsum_eq_sum_of_fintype, Finset.sum_div, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro I _
    apply Finset.sum_congr rfl
    intro i _
    change (c i * heckeIdealVonMangoldt _ I.val) / (n : ℂ)^s =
      c i * (v i I.val / (I.val.absNorm : ℂ)^s)
    rw [I.property.2]
    dsimp only [v]
    ring

private theorem completed_logDeriv_eq_gamma_add_ordinary (χ : U) (s : ℂ) (hs : 1 < s.re) :
    logDeriv (continuedCompletedHeckeL χ) s =
      logDeriv (heckeGammaFactor χ) s + logDeriv (ordinary χ) s := by
  have hL := (finiteHeckeL_exists_continuation χ).choose_spec
  have hloc : continuedCompletedHeckeL χ =ᶠ[𝓝 s] (fun z ↦ heckeGammaFactor χ z * ordinary χ z) := by
    filter_upwards [(isOpen_Ioi.preimage Complex.continuous_re).mem_nhds
      (show s ∈ Complex.re ⁻¹' Ioi (1 : ℝ) from hs)] with z hz
    rw [(continuedCompletedHeckeL_spec χ).2 ⟨z,hz⟩]
    exact congrArg (heckeGammaFactor χ z * ·) (hL.2 ⟨z,hz⟩).symm
  have he := finiteHeckeL_logDeriv_hasSum_ideals χ (ordinary χ) hL.1 hL.2 ⟨s,hs⟩
  exact (logDeriv_congr_nhds hloc).eq_of_nhds.trans <| logDeriv_fun_mul s
    (heckeGammaFactor_ne_zero_of_re_pos χ (zero_lt_one.trans hs)) he.2.1
    (differentiableAt_heckeGammaFactor_of_re_pos χ (zero_lt_one.trans hs)) he.1.differentiableAt

/-- Any polynomial implementing the genuine gamma shift supplies its logarithmic
derivative difference on the same half-plane. -/
private theorem logDeriv_gamma_shift_of_polynomial (χ : U) (P : ℂ[X])
    (hP : ∀ z : ℂ, 0 < z.re → heckeGammaFactor χ (z+2) = heckeGammaFactor χ z * P.eval z)
    {z : ℂ} (hz : 0 < z.re) :
    logDeriv (heckeGammaFactor χ) (z+2) - logDeriv (heckeGammaFactor χ) z =
      P.derivative.eval z / P.eval z := by
  let G := heckeGammaFactor χ
  have hshift : 0 < (z+2).re := by simp only [Complex.add_re, Complex.re_ofNat]; linarith
  have hP₀ : P.eval z ≠ 0 := by
    intro h
    exact heckeGammaFactor_ne_zero_of_re_pos χ hshift (by rw [hP z hz, h, mul_zero])
  have hEq : (fun w : ℂ ↦ G (w+2)) =ᶠ[𝓝 z] fun w ↦ G w * P.eval w := by
    have hr : Complex.re ⁻¹' (Ioi (0 : ℝ)) ∈ 𝓝 z :=
      (Complex.continuous_re.tendsto z) (Ioi_mem_nhds hz)
    filter_upwards [hr] with w hw
    exact hP w hw
  have hlog := (logDeriv_congr_nhds hEq).eq_of_nhds
  have ha : HasDerivAt (fun w : ℂ ↦ w+2) 1 z := (hasDerivAt_id z).add_const 2
  have hcomp : logDeriv (fun w : ℂ ↦ G (w+2)) z = logDeriv G (z+2) := by
    change logDeriv (G ∘ (fun w : ℂ ↦ w+2)) z = _
    rw [logDeriv_comp (f := G) (g := fun w : ℂ ↦ w+2) (x := z)
      (differentiableAt_heckeGammaFactor_of_re_pos χ hshift) ha.differentiableAt,
      ha.deriv, mul_one]
  rw [hcomp, logDeriv_fun_mul z (heckeGammaFactor_ne_zero_of_re_pos χ hz)
    hP₀ (differentiableAt_heckeGammaFactor_of_re_pos χ hz)
    (P.hasDerivAt z).differentiableAt, logDeriv_apply (fun w ↦ P.eval w), (P.hasDerivAt z).deriv] at hlog
  exact sub_eq_iff_eq_add.mpr (by rw [hlog, add_comm])

/-- The logarithmic derivative of the true gamma factor changes by a rational function
when the argument increases by two. -/
private theorem gamma_logDeriv_shift_rational (χ : U) :
    RayRational (fun x : ℝ ↦ logDeriv (heckeGammaFactor χ) ((x : ℂ) + 2) -
      logDeriv (heckeGammaFactor χ) (x : ℂ)) := by
  obtain ⟨p, hp, he⟩ := exists_gamma_shift_polynomial χ
  refine ⟨p.derivative, p, hp, ?_⟩
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hshift : 0 < ((x : ℂ) + 2).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofNat]
    linarith
  have hn : p.eval (x : ℂ) ≠ 0 := by
    intro h
    exact heckeGammaFactor_ne_zero_of_re_pos χ hshift (by rw [he x hx, h, mul_zero])
  rw [logDeriv_gamma_shift_of_polynomial χ p he hx, div_mul_cancel₀ _ hn]

private theorem packet_zero_or_one {ι : Type*} (rows : Finset ι) (χ : ι → U) (c : ι → ℂ)
    (n : ℕ) (hn : n = 0 ∨ n = 1) : packetCoefficient rows χ c n = 0 := by
  classical
  simp only [packetCoefficient, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro i _
  have h := heckeLogDerivCoefficient_le_vonMangoldt (χ i) n
  rcases hn with rfl | rfl <;> simp at h <;> simp [h]

/-- If the weighted completed logarithmic derivative has rational shift
difference on the positive ray, the actual ordinary Euler packet vanishes on its entire
half-plane. All Euler decay and analytic continuation are supplied internally. -/
private theorem ordinary_zero_of_completed_rational_shift {ι : Type*}
    (rows : Finset ι) (χ : ι → U) (c : ι → ℂ)
    (hcomp : RayRational (fun x : ℝ ↦ ∑ i ∈ rows, c i *
      (logDeriv (continuedCompletedHeckeL (χ i)) ((x : ℂ) + 2) -
        logDeriv (continuedCompletedHeckeL (χ i)) (x : ℂ)))) :
    (∀ n, packetCoefficient rows χ c n = 0) ∧
    (∀ s : ℂ, 1 < s.re → ∑ i ∈ rows, c i * logDeriv (ordinary (χ i)) s = 0) := by
  let a := packetCoefficient rows χ c
  have hae := (packet_hasSum rows χ c (s := 2) (by norm_num)).LSeriesSummable.abscissaOfAbsConv_le
  have ha : LSeries.abscissaOfAbsConv a < ⊤ := hae.trans_lt (EReal.coe_lt_top _)
  have heul (s : ℂ) (hs : 1 < s.re) : LSeries a s = ∑ i ∈ rows, c i * (-logDeriv (ordinary (χ i)) s) :=
    (packet_hasSum rows χ c hs).LSeries_eq
  have hg := RayRational.sum rows _ (fun i _ ↦ RayRational.const_mul (c i) (gamma_logDeriv_shift_rational (χ i)))
  have hold : ∀ n, a n = 0 := by
    apply lseries_shift_rational_rigidity a ha (packet_zero_or_one rows χ c 0 (Or.inl rfl))
      (packet_zero_or_one rows χ c 1 (Or.inr rfl))
    apply (hcomp.sub hg).congr
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hs : 1 < ((x : ℂ)+2).re := by simp only [Complex.add_re,Complex.ofReal_re,Complex.re_ofNat]; linarith
    rw [heul _ hx, heul _ hs, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [completed_logDeriv_eq_gamma_add_ordinary _ _ hs,
      completed_logDeriv_eq_gamma_add_ordinary _ _ hx]
    ring
  refine ⟨hold,fun s hs ↦ ?_⟩
  have he := heul s hs
  have az : a = 0 := funext hold
  rw [az, LSeries_zero] at he
  simp only [Pi.zero_apply, mul_neg, Finset.sum_neg_distrib, zero_eq_neg] at he
  exact he

private def simpleShift (p : ℂ) (x : ℝ) : ℂ :=
  1/((x : ℂ) + 2 - p) - 1/((x : ℂ) - p)

private theorem simpleShift_rational (p : ℂ) : RayRational (simpleShift p) := by
  apply ((RayRational.inv_sub (p-2)).sub (RayRational.inv_sub p)).congr
  filter_upwards with x
  dsimp only [simpleShift]
  rw [show (x : ℂ) - (p-2) = (x : ℂ) + 2 - p by ring]

private def principalShift (χ : U) (x : ℝ) : ℂ := open Classical in
  if χ = 1 then simpleShift 0 x + simpleShift 1 x else 0

private theorem principalShift_rational (χ : U) : RayRational (principalShift χ) := by
  classical
  change RayRational (fun x : ℝ ↦ if χ = 1 then simpleShift 0 x + simpleShift 1 x else 0)
  by_cases h : χ = 1
  · simpa only [h,ite_true] using (simpleShift_rational 0).add (simpleShift_rational 1)
  · simpa only [h,ite_false] using RayRational.const 0

/-- A full-strip divisor relation outside even an arbitrary finite exception set forces every
weighted ordinary Hecke logarithmic-derivative coefficient to vanish, and the weighted
ordinary logarithmic derivative is zero throughout Re s > 1. -/
theorem ordinary_logDeriv_eq_zero_of_finite_exception_divisor {ι : Type*}
    (rows : Finset ι) (χ : ι → U) (c : ι → ℂ)
    (hfin : ∀ i ∈ rows, IsOfFinOrder (χ i)) (E : Finset ℂ)
    (hvan : ∀ p : ℂ, p.re ∈ Ioo (0 : ℝ) 1 → p ∉ E →
      ∑ i ∈ rows, c i * (posOrder(χ i,p) : ℂ) = 0) :
    (∀ n, packetCoefficient rows χ c n = 0) ∧
    (∀ s : ℂ, 1 < s.re → ∑ i ∈ rows, c i * logDeriv (ordinary (χ i)) s = 0) := by
  classical
  let d (p : ℂ) := ∑ i ∈ rows, c i * (posOrder(χ i,p) : ℂ)
  have hr := RayRational.sum E _ fun p _ ↦ RayRational.const_mul (d p) (simpleShift_rational p)
  have hcorr : RayRational (fun x : ℝ ↦ ∑ i ∈ rows, c i * (correctedCompletedLogDeriv (χ i)
      ((x : ℂ)+2) - correctedCompletedLogDeriv (χ i) (x : ℂ))) := by
    apply hr.congr
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
    have hs : 1 < ((x : ℂ)+2).re := by simp only [Complex.add_re,Complex.ofReal_re,Complex.re_ofNat]; linarith
    exact (finiteOrder_completed_two_points_of_finite_exceptions rows χ c hfin E hvan
      ((x : ℂ)+2) (x : ℂ) hs hx).symm
  have hprincipal := RayRational.sum rows _ fun i _ ↦ RayRational.const_mul (c i) (principalShift_rational (χ i))
  apply ordinary_zero_of_completed_rational_shift rows χ c
  apply (hcorr.sub hprincipal).congr
  filter_upwards with x
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : χ i = 1
  · simp [correctedCompletedLogDeriv,principalShift,simpleShift,hi]
    ring
  · simp [correctedCompletedLogDeriv,principalShift,hi]

/-- The norm-grouped coefficients from Equation (B.6.1.14), written directly in the
project's arithmetic notation, vanish at every integer norm. -/
theorem weighted_heckeLogDerivCoefficient_eq_zero_of_finite_exceptions {ι : Type*}
    (rows : Finset ι) (χ : ι → U) (c : ι → ℂ)
    (hfin : ∀ i ∈ rows, IsOfFinOrder (χ i)) (E : Finset ℂ)
    (hvan : ∀ p : ℂ, p.re ∈ Ioo (0 : ℝ) 1 → p ∉ E →
      ∑ i ∈ rows, c i * (posOrder(χ i,p) : ℂ) = 0) (n : ℕ) :
    ∑ i ∈ rows, c i * heckeLogDerivCoefficient (ideleClassNormTwist (χ i) 0) n = 0 := by
  simpa only [packetCoefficient, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using
    (ordinary_logDeriv_eq_zero_of_finite_exception_divisor rows χ c hfin E hvan).1 n

/-- Exact full zero-divisor cancellation, with central multiplicities included, implies the
ordinary weighted Euler logarithmic derivatives vanish on the whole Euler half-plane. -/
theorem ordinary_logDeriv_eq_zero_of_full_divisor {ι : Type*}
    (rows : Finset ι) (χ : ι → U) (c : ι → ℂ)
    (hfin : ∀ i ∈ rows, IsOfFinOrder (χ i))
    (hvan : ∀ p : ℂ, p.re ∈ Ioo (0 : ℝ) 1 →
      ∑ i ∈ rows, c i * (posOrder(χ i,p) : ℂ) = 0) :
    ∀ s : ℂ, 1 < s.re → ∑ i ∈ rows, c i * logDeriv (ordinary (χ i)) s = 0 :=
  (ordinary_logDeriv_eq_zero_of_finite_exception_divisor rows χ c hfin ∅ (fun p hp _ ↦ hvan p hp)).2

end RiemannMasullo.HeckeDivisorRigidity
