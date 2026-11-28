module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4a_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec4a_StripJetAccretivity
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.GradedCompanion
import RiemannMasullo.AppB_AnalyticNT.Sec4b
import RiemannMasullo.Ch10_TraceSpectral.Sec3

/-! # Uniform column bounds for positive-width strip quotients at Sobolev order zero

The normalized Mellin companion, independent of the width, controls the adjoint
on finite families of retained strip jets in any fixed angular mode. For widths
at most A the column bound has the explicit factor 1 + 2 A and a sum of inverse
quadratic height weights, one for each jet order.

The application refers to Theorem 10.4.2.1 (p. 459). Its Hilbert-space columns
are taken in an arbitrary orthonormal basis of each finite jet span.
-/

@[expose] public noncomputable section

open Complex MeasureTheory Set IsDedekindDomain NumberField Multiplicative
open scoped ComplexConjugate NNReal NumberField.AdeleRing InnerProductSpace

namespace RiemannMasullo

section

set_option quotPrecheck false
variable {F : Type*} [Field F] [NumberField F]
attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "m𝔽" => (continuousIdeleClassNorm F : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "logNorm" => (logIdeleClassNorm F)
local notation "W(" α ")" => CompactIntervalSobolev μ𝔽 logNorm (-α) α 0
local notation "site(" j ")" => ((j).val.2.1 : ℂ) + ((j).val.2.2.1 : ℂ) * I
local notation "jetVec(" χ "," hα "," j ")" =>
  (spectralStripJet_memLp χ hα le_rfl j).toLp
    (spectralZeroJet (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)

private theorem quotient_adjoint_column_norm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (K : Submodule ℂ E) [K.HasOrthogonalProjection] [IsClosed (K : Set E)]
    [CompleteSpace (E ⧸ K)] (T : E →L[ℂ] E) (Q : (E ⧸ K) →L[ℂ] (E ⧸ K))
    (hQ : ∀ x, Q (K.mkQ x) = K.mkQ (T x)) (e : E) (he : e ∈ Kᗮ) :
    ‖Q.adjoint (K.mkQ e)‖ = ‖T.adjoint e‖ := by
  have hi (x : E) (hx : x ∈ Kᗮ) (y : E) :
      ⟪K.mkQ x,K.mkQ y⟫_ℂ = ⟪x,y⟫_ℂ := by
    have hp : K.mkQ (K.starProjection y) = 0 := (Submodule.Quotient.mk_eq_zero K).mpr
      (K.starProjection_apply_mem y)
    calc
      _ = ⟪K.mkQ x,K.mkQ (y-K.starProjection y)⟫_ℂ := by rw [map_sub, hp, sub_zero]
      _ = ⟪x,y-K.starProjection y⟫_ℂ :=
        Submodule.Quotient.inner_mk_mk K _ _ hx (Submodule.sub_starProjection_mem_orthogonal _)
      _ = _ := by
        rw [inner_sub_right, inner_eq_zero_symm.mp
          ((Submodule.mem_orthogonal K x).mp hx _ (K.starProjection_apply_mem y)), sub_zero]
  have hT : T.adjoint e ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro f hf
    rw [ContinuousLinearMap.adjoint_inner_right]
    apply Submodule.inner_right_of_mem_orthogonal _ he
    apply (Submodule.Quotient.mk_eq_zero K).mp
    change K.mkQ (T f) = 0
    rw [← hQ, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero K).mpr hf, map_zero]
  have h : Q.adjoint (K.mkQ e) = K.mkQ (T.adjoint e) := by
    refine ext_inner_right ℂ fun v ↦ ?_
    obtain ⟨x,rfl⟩ := K.mkQ_surjective v
    rw [ContinuousLinearMap.adjoint_inner_left, hQ, hi _ he, hi _ hT,
      ContinuousLinearMap.adjoint_inner_left]
  rw [h, ← K.quotientEquivOrthogonal.norm_map]
  change ‖K.quotientEquivOrthogonal (Submodule.Quotient.mk (T.adjoint e))‖ = _
  rw [K.quotientEquivOrthogonal_mk _ hT]
  rfl

/-- One companion realizes L-z for every character trivial on the same norm section. -/
theorem exists_normalized_heckeTest_mellin_affine_companion
    (τ : ℝ≥0ˣ →ₜ* C𝔽) (hτ : Function.RightInverse τ (ideleClassNorm F))
    (φ : BruhatCompactSupport C𝔽) (L : ℝ) :
    ∃ ψ : BruhatCompactSupport C𝔽, ∀ (η : PontryaginDual C𝔽), (∀ q, η (τ q) = 1) → ∀ z : ℂ,
      (∫ g : C𝔽, ψ.val g * ideleClassNormTwist η z g ∂μ𝔽) =
      ((L : ℂ)-z) * ∫ g : C𝔽, φ.val g * ideleClassNormTwist η z g ∂μ𝔽 := by
  let b : Multiplicative ℝ →ₜ* C𝔽 := ⟨τ.toMonoidHom.comp positiveRealLogEquiv.symm.toMulEquiv.toMonoidHom,
    τ.continuous.comp positiveRealLogEquiv.symm.continuous⟩
  have hn (t : ℝ) : ((ideleClassNorm F (b (Multiplicative.ofAdd t))).val : ℝ) = Real.exp t := by
    change ((ideleClassNorm F (τ (positiveRealLogEquiv.symm (Multiplicative.ofAdd t)))).val : ℝ) = _
    rw [hτ]
    have h := positiveRealLogEquiv_apply (positiveRealLogEquiv.symm (Multiplicative.ofAdd t))
    rw [ContinuousMulEquiv.apply_symm_apply, toAdd_ofAdd] at h
    exact (Real.exp_log (NNReal.coe_pos.mpr (Units.zero_lt _))).symm.trans (congrArg Real.exp h.symm)
  let φ' : BruhatCompactSupport C𝔽 :=
    ⟨bruhatDirectionalDeriv b φ.val, ideleClass_bruhatFlowDeriv_mem b φ⟩
  refine ⟨(L : ℂ) • φ + φ', fun η hη z ↦ ?_⟩
  have hchain : HasDerivAt (fun t : ℝ ↦ ideleClassNormTwist η z (b (Multiplicative.ofAdd t))) z 0 := by
    have he := ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const z).cexp
    have hge : HasDerivAt (fun t : ℝ ↦ exp ((t : ℂ)*z)) z 0 := by simpa using he
    refine hge.congr_of_eventuallyEq (.of_forall fun t ↦ ?_)
    change ((η (b (Multiplicative.ofAdd t)) : Circle) : ℂ) *
      (((ideleClassNorm F (b (Multiplicative.ofAdd t))).val : ℝ) : ℂ)^z = _
    rw [show η (b (Multiplicative.ofAdd t)) = 1 from hη _, Circle.coe_one, one_mul, hn,
      Complex.ofReal_exp, Complex.cpow_def_of_ne_zero (Complex.exp_ne_zero _),
      Complex.log_exp (by simp [Real.pi_pos]) (by simp [Real.pi_pos.le])]
  have hval : (∫ g : C𝔽, φ'.val g * ideleClassNormTwist η z g ∂μ𝔽) =
      -(z * ∫ g : C𝔽, φ.val g * ideleClassNormTwist η z g ∂μ𝔽) :=
    ideleClass_integral_bruhatFlowDeriv_mul b (ideleClassNormTwist η z) hchain φ
  have hint (f : BruhatCompactSupport C𝔽) :
      Integrable (fun g : C𝔽 ↦ f.val g * ideleClassNormTwist η z g) μ𝔽 :=
    ((continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp f.property.1)).mul
      (ideleClassNormTwist η z).continuous).integrable_of_hasCompactSupport f.property.2.mul_right
  change (∫ g : C𝔽, ((L : ℂ)*φ.val g+φ'.val g) * ideleClassNormTwist η z g ∂μ𝔽) = _
  simp_rw [add_mul, mul_assoc]
  rw [integral_add ((hint φ).const_mul _) (hint φ'), integral_const_mul, hval]
  ring

/-- The logarithmic moments of a compact Bruhat Mellin transform in a fixed character. -/
private def heckeStripMoment (η : PontryaginDual C𝔽) (f : BruhatCompactSupport C𝔽)
    (z : ℂ) (k : ℕ) : ℂ :=
  ∫ g : C𝔽, f.val g * ideleClassNormTwist η z g * (logNorm g : ℂ)^k ∂μ𝔽

private theorem heckeStripMoment_hasDerivAt (η : PontryaginDual C𝔽) (f : BruhatCompactSupport C𝔽)
    (z : ℂ) (k : ℕ) :
    HasDerivAt (fun w ↦ heckeStripMoment η f w k) (heckeStripMoment η f z (k+1)) z :=
  hasDerivAt_ideleClass_bruhatMoment η f z k

/-- Multiplication of a full Mellin transform by L-z differentiates on the complete jet
block, including the order-lowering term. -/
private theorem heckeStripMoment_affine_companion_succ (η : PontryaginDual C𝔽) (φ ψ : BruhatCompactSupport C𝔽)
    (L : ℝ) (hψ : ∀ z : ℂ, (∫ g : C𝔽, ψ.val g * ideleClassNormTwist η z g ∂μ𝔽) =
      ((L : ℂ)-z) * ∫ g : C𝔽, φ.val g * ideleClassNormTwist η z g ∂μ𝔽) (k : ℕ) (z : ℂ) :
    heckeStripMoment η ψ z (k+1) = ((L : ℂ)-z)*heckeStripMoment η φ z (k+1) -
      ((k+1 : ℕ) : ℂ)*heckeStripMoment η φ z k := by
  have hm (v : ℂ) : heckeStripMoment η ψ v 0 = ((L : ℂ)-v)*heckeStripMoment η φ v 0 := by
    simpa [heckeStripMoment] using hψ v
  have ha (v : ℂ) : HasDerivAt (fun w : ℂ ↦ (L : ℂ)-w) (-1 : ℂ) v := by
    simpa only [id_eq] using (hasDerivAt_id v).const_sub (L : ℂ)
  induction k generalizing z with
  | zero =>
    have eqf : (fun v ↦ heckeStripMoment η ψ v 0) = (fun v ↦ ((L : ℂ)-v)*heckeStripMoment η φ v 0) :=
      funext hm
    have hh := heckeStripMoment_hasDerivAt η ψ z 0
    rw [eqf] at hh
    have he := hh.unique ((ha z).mul (heckeStripMoment_hasDerivAt η φ z 0))
    rw [he]
    push_cast
    ring
  | succ k ih =>
    have eqf := funext ih
    have hh := heckeStripMoment_hasDerivAt η ψ z (k+1)
    rw [eqf] at hh
    have he := hh.unique (((ha z).mul (heckeStripMoment_hasDerivAt η φ z (k+1))).sub
      ((heckeStripMoment_hasDerivAt η φ z k).const_mul ((k+1 : ℕ) : ℂ)))
    rw [he]
    push_cast
    ring

private theorem finite_jet_succ_affine {E : Type*} [AddCommGroup E] [Module ℂ E]
    (p q : ℕ → ℂ) (c : ℂ) (v : ℕ → E) (m : ℕ) (q₀ : q 0 = c*p 0)
    (q' : ∀ n, q (n+1) = c*p (n+1) - ((n+1 : ℕ) : ℂ)*p n) :
    (∑ i ∈ Finset.range (m+2), conj (((m+1).choose i : ℂ) * q (m+1-i)) • v i) =
      conj c • (∑ i ∈ Finset.range (m+2), conj (((m+1).choose i : ℂ) * p (m+1-i)) • v i) -
      ((m+1 : ℕ) : ℂ) • (∑ i ∈ Finset.range (m+1), conj ((m.choose i : ℂ) * p (m-i)) • v i) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ (f := fun i ↦
    conj (((m+1).choose i : ℂ) * p (m+1-i)) • v i)]
  simp only [Nat.sub_self, Nat.choose_self, Nat.cast_one, one_mul, q₀, map_mul, smul_add,
    Finset.smul_sum, smul_smul]
  rw [add_sub_right_comm, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hd : m+1-i = m-i+1 := by omega
  rw [hd, q' (m-i), map_sub, map_mul, map_mul, ← sub_smul]
  congr 1
  have hchoose : ((m.choose i : ℕ) : ℂ) * ((m+1 : ℕ) : ℂ) =
      (((m+1).choose i : ℕ) : ℂ) * ((m-i+1 : ℕ) : ℂ) := by
    exact_mod_cast hd ▸ Nat.choose_mul_succ_eq m i
  simp only [map_natCast]
  linear_combination hchoose * conj (p (m-i))

private def stripLowerJet {χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽}
    {a α : ℝ} (j : SpectralStripJetIndex χ a α 0) (m : ℕ) (hm : m ≤ j.val.2.2.2) :
    SpectralStripJetIndex χ a α 0 :=
  ⟨(j.val.1,j.val.2.1,j.val.2.2.1,m), lt_of_le_of_lt hm j.property⟩

private def stripLowerJetVector {χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽}
    {a α : ℝ} (r : SpectralStripJetIndex χ a α 0 → W(α)) (j : SpectralStripJetIndex χ a α 0) (m : ℕ) : W(α) :=
  if hm : m ≤ j.val.2.2.2 then r (stripLowerJet j m hm) else 0

private theorem stripLowerJet_adjoint_row
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽) {a α : ℝ} (hα : 0 ≤ α)
    (r : SpectralStripJetIndex χ a α 0 → W(α))
    (hr : ∀ j f, ⟪r j,f⟫_ℂ = spectralSobolevPairing f (jetVec(χ,hα,j)))
    (j : SpectralStripJetIndex χ a α 0) (f : BruhatCompactSupport C𝔽)
    (m : ℕ) (hm : m ≤ j.val.2.2.2) :
    (hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα) le_rfl f).adjoint
      (r (stripLowerJet j m hm)) =
      ∑ i ∈ Finset.range (m+1), conj ((m.choose i : ℂ) * heckeStripMoment (χ j.val.1) f site(j) (m-i)) •
        stripLowerJetVector r j i := by
  rw [Isolated.spectralStripJet_adjoint_testAction a hα le_rfl χ r hr (stripLowerJet j m hm) f]
  change (∑ i : Fin (m + 1), _) = _
  rw [← Fin.sum_univ_eq_sum_range]
  apply Fintype.sum_congr
  intro i
  have hi : (i : ℕ) ≤ j.val.2.2.2 := (Nat.le_of_lt_succ i.isLt).trans hm
  simp only [stripLowerJetVector, dite_eq_left hi]
  rfl

private theorem map_smul_sub_smul_jet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] E) (a b : ℂ) (x y : E) :
    a • T x - b • T y = T (a • x - b • y) := by rw [map_sub, map_smul, map_smul]

private theorem strip_actual_binomial_companion {E : Type*} [AddCommGroup E] [Module ℂ E]
    (η : PontryaginDual C𝔽) (φ ψ : BruhatCompactSupport C𝔽) (L : ℝ) (z : ℂ)
    (hψ : ∀ w : ℂ, (∫ g : C𝔽, ψ.val g * ideleClassNormTwist η w g ∂μ𝔽) =
      ((L : ℂ)-w) * ∫ g : C𝔽, φ.val g * ideleClassNormTwist η w g ∂μ𝔽)
    (v : ℕ → E) (k : ℕ) :
    (∑ i ∈ Finset.range (k+2), conj (((k+1).choose i : ℂ) * heckeStripMoment η ψ z (k+1-i)) • v i) =
      ((L : ℂ)-conj z) • (∑ i ∈ Finset.range (k+2), conj (((k+1).choose i : ℂ) * heckeStripMoment η φ z (k+1-i)) • v i) -
      ((k+1 : ℕ) : ℂ) • (∑ i ∈ Finset.range (k+1), conj ((k.choose i : ℂ) * heckeStripMoment η φ z (k-i)) • v i) := by
  have hq0 : heckeStripMoment η ψ z 0 = ((L : ℂ)-z)*heckeStripMoment η φ z 0 := by
    simpa only [heckeStripMoment, pow_zero, mul_one] using hψ z
  have hn (n : ℕ) := heckeStripMoment_affine_companion_succ η φ ψ L hψ n z
  simpa only [map_sub, conj_ofReal] using finite_jet_succ_affine (heckeStripMoment η φ z)
    (heckeStripMoment η ψ z) ((L : ℂ)-z) v k hq0 hn

/-- On any higher spectral jet the affine companion acts by the logarithmic generator:
the order-lowering term has exactly the degree of the jet. -/
private theorem spectralStripJet_adjoint_affine_companion_succ
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽) {a α : ℝ} (hα : 0 ≤ α)
    (r : SpectralStripJetIndex χ a α 0 → W(α))
    (hr : ∀ j f, ⟪r j,f⟫_ℂ = spectralSobolevPairing f (jetVec(χ,hα,j)))
    (j : SpectralStripJetIndex χ a α 0) (k : ℕ) (hk : j.val.2.2.2 = k+1)
    (φ ψ : BruhatCompactSupport C𝔽) (L : ℝ)
    (hψ : ∀ z : ℂ, (∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ j.val.1) z g ∂μ𝔽) =
      ((L : ℂ)-z) * ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ j.val.1) z g ∂μ𝔽) :
    let low : SpectralStripJetIndex χ a α 0 := ⟨(j.val.1, j.val.2.1, j.val.2.2.1, k),
      lt_of_le_of_lt (by omega : k ≤ j.val.2.2.2) j.property⟩
    let T (f : BruhatCompactSupport C𝔽) := hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα) le_rfl f
    (T ψ).adjoint (r j) =
      (T φ).adjoint (((L : ℂ)-conj site(j)) • r j - ((k+1 : ℕ) : ℂ) • r low) := by
  classical
  let T (f : BruhatCompactSupport C𝔽) := hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα) le_rfl f
  let p (f : BruhatCompactSupport C𝔽) n := heckeStripMoment (χ j.val.1) f site(j) n
  have hj : j = stripLowerJet j (k+1) (le_of_eq hk.symm) := by
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl hk))
  have he := strip_actual_binomial_companion (χ j.val.1) φ ψ L site(j) hψ (stripLowerJetVector r j) k
  change (T ψ).adjoint (r j) = (T φ).adjoint
    (((L : ℂ)-conj site(j)) • r j - ((k+1 : ℕ) : ℂ) • r (stripLowerJet j k (by omega)))
  have hψrow := stripLowerJet_adjoint_row χ hα r hr j ψ (k+1) (le_of_eq hk.symm)
  have hφrow := stripLowerJet_adjoint_row χ hα r hr j φ (k+1) (le_of_eq hk.symm)
  have hlo := stripLowerJet_adjoint_row χ hα r hr j φ k (by omega)
  have hψtop := (congrArg (fun v ↦ (T ψ).adjoint (r v)) hj).trans hψrow
  have hφtop := (congrArg (fun v ↦ (T φ).adjoint (r v)) hj).trans hφrow
  calc
    _ = _ := hψtop
    _ = _ := he
    _ = ((L : ℂ)-conj site(j)) • (T φ).adjoint (r j) -
          ((k+1 : ℕ) : ℂ) • (T φ).adjoint (r (stripLowerJet j k (by omega))) :=
      congrArg₂ (fun (u v : W(α)) ↦ ((L : ℂ)-conj site(j)) • u - ((k+1 : ℕ) : ℂ) • v)
        hφtop.symm hlo.symm
    _ = _ := map_smul_sub_smul_jet (T φ).adjoint _ _ _ _

private theorem strip_resolvent_uniform_width {A α β t : ℝ} (hwidth : α ≤ A) (hβ : |β| < α) :
    ((((A+1 : ℝ) : ℂ) - conj ((β : ℂ) + (t : ℂ)*I))⁻¹).re ≤ (1+2*A)/(1+t^2) := by
  let u := A+1-β
  have hu : 1 ≤ u := by dsimp [u]; linarith [(abs_lt.mp hβ).2]
  have htop : u ≤ 1+2*A := by dsimp [u]; linarith [(abs_lt.mp hβ).1]
  have hs : 1+t^2 ≤ u^2+t^2 := by nlinarith [sq_nonneg (u-1)]
  have he : ((((A+1 : ℝ) : ℂ) - conj ((β : ℂ) + (t : ℂ)*I))⁻¹).re = u/(u^2+t^2) := by
    rw [Complex.inv_re, Complex.normSq_apply]
    simp only [sub_re, sub_im, conj_re, conj_im, add_re, add_im, mul_I_re, mul_I_im, ofReal_re,
      ofReal_im, neg_zero, add_zero, zero_add, zero_sub, neg_neg, u, pow_two]
  rw [he]
  exact (div_le_div_of_nonneg_left (by linarith) (by positivity) hs).trans
    (div_le_div_of_nonneg_right htop (by positivity))

/-- A whole band of positive strip widths can use one rate and one test companion.
At rate A+1 the explicit constant before the height sum is 1+2A. -/
private theorem finite_strip_column_bound_uniform_in_width {ι : Type*} [Fintype ι] {A α K E : ℝ}
    (hwidth : α ≤ A) (hE : 0 ≤ E) (β t : ι → ℝ) (hβ : ∀ i, |β i| < α)
    (h : (A+1-α)*E ≤ K^2*∑ i, ((((A+1 : ℝ):ℂ)-conj ((β i : ℂ)+(t i : ℂ)*I))⁻¹).re) :
    E ≤ (1+2*A)*K^2*∑ i, (1+(t i)^2)⁻¹ := by
  calc
    _ ≤ (A+1-α)*E := le_mul_of_one_le_left hE (by linarith)
    _ ≤ _ := h
    _ ≤ K^2 * ∑ i, (1+2*A)/(1+(t i)^2) := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun i _ ↦ strip_resolvent_uniform_width hwidth (hβ i)) (sq_nonneg _)
    _ = _ := by simp only [div_eq_mul_inv, ← Finset.mul_sum]; ring

private theorem spectralStripJet_adjoint_affine_companion
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽) {a α : ℝ} (hα : 0 ≤ α)
    (r : SpectralStripJetIndex χ a α 0 → W(α))
    (hr : ∀ j f, ⟪r j,f⟫_ℂ = spectralSobolevPairing f (jetVec(χ,hα,j)))
    (j : SpectralStripJetIndex χ a α 0) (φ ψ : BruhatCompactSupport C𝔽) (L : ℝ)
    (hψ : ∀ z : ℂ, (∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ j.val.1) z g ∂μ𝔽) =
      ((L : ℂ)-z) * ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ j.val.1) z g ∂μ𝔽) :
    let T (f : BruhatCompactSupport C𝔽) := hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα) le_rfl f
    (T ψ).adjoint (r j) = (T φ).adjoint
      (((L : ℂ)-conj site(j)) • r j - (j.val.2.2.2 : ℂ) • r (j.lowerOne)) := by
  let T (f : BruhatCompactSupport C𝔽) := hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα) le_rfl f
  let z := site(j)
  let m (f : BruhatCompactSupport C𝔽) := ∫ g : C𝔽, f.val g * ideleClassNormTwist (χ j.val.1) z g ∂μ𝔽
  change (T ψ).adjoint (r j) = (T φ).adjoint (((L : ℂ)-conj z) • r j - (j.val.2.2.2 : ℂ) • r j.lowerOne)
  by_cases h0 : j.val.2.2.2 = 0
  · have he (f : BruhatCompactSupport C𝔽) : (T f).adjoint (r j) = conj (m f) • r j := by
      dsimp only [T, m, z]
      obtain ⟨⟨c, b, t, k⟩, hk⟩ := j
      simp only at h0
      subst h0
      rw [Isolated.spectralStripJet_adjoint_testAction a hα le_rfl χ r hr _ f]
      simp
    have hφe := he φ
    have hψe := he ψ
    have hd : conj (m ψ) = ((L : ℂ)-conj z)*conj (m φ) := by
      rw [show m ψ = ((L : ℂ)-z)*m φ from hψ z, map_mul, map_sub, conj_ofReal]
    have hv : ((L : ℂ)-conj z) • r j - (j.val.2.2.2 : ℂ) • r j.lowerOne = ((L : ℂ)-conj z) • r j :=
      sub_eq_self.mpr ((congrArg (fun q : ℂ ↦ q • r j.lowerOne)
        (show (j.val.2.2.2 : ℂ) = 0 by exact_mod_cast h0)).trans (zero_smul ℂ _))
    calc
      _ = conj (m ψ) • r j := hψe
      _ = ((L : ℂ)-conj z) • (conj (m φ) • r j) := by rw [hd,mul_smul]
      _ = ((L : ℂ)-conj z) • (T φ).adjoint (r j) := congrArg (((L : ℂ)-conj z) • ·) hφe.symm
      _ = (T φ).adjoint (((L : ℂ)-conj z) • r j) := ((T φ).adjoint.map_smul _ _).symm
      _ = _ := congrArg (T φ).adjoint hv.symm
  · obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero h0
    have h := spectralStripJet_adjoint_affine_companion_succ χ hα r hr j n hn φ ψ L hψ
    have hs : j.lowerOne =
        (⟨(j.val.1,j.val.2.1,j.val.2.2.1,n),lt_of_le_of_lt (by omega : n ≤ j.val.2.2.2) j.property⟩ :
          SpectralStripJetIndex χ a α 0) := by
      apply Subtype.ext
      exact Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (by change j.val.2.2.2 - 1 = n; omega)))
    let jn : SpectralStripJetIndex χ a α 0 := ⟨(j.val.1,j.val.2.1,j.val.2.2.1,n),
      lt_of_le_of_lt (by omega : n ≤ j.val.2.2.2) j.property⟩
    have hm : ((n+1:ℕ):ℂ) • r jn = (j.val.2.2.2:ℂ) • r j.lowerOne :=
      congrArg₂ (fun (k : ℕ) (v : SpectralStripJetIndex χ a α 0) ↦ (k:ℂ) • r v) hn.symm hs.symm
    exact h.trans (congrArg (T φ).adjoint (congrArg (((L : ℂ)-conj z) • r j - ·) hm))

/-- Paper: Theorem 10.4.2.1, p. 459. Quantitative upper bound for the actual quotient
adjoint on a finite predecessor-closed family of retained strip jets in a single angular mode.
Reconstruction: the polynomial-exponential energy in the primal strip Gram controls all orders
with unrestricted multiplicities and spacings. -/
theorem spectralStripConvolution_finite_jet_bound
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (a : ℝ) {α L : ℝ} (hα : 0 < α) (hL : α < L) (φ ψ : BruhatCompactSupport C𝔽)
    (ω : PontryaginDual (ideleClassNorm F).ker)
    (hψ : ∀ z : ℂ, (∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) z g ∂μ𝔽) =
      ((L : ℂ)-z) * ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) z g ∂μ𝔽)
    (r : SpectralStripJetIndex χ a α 0 → W(α)) (hrind : LinearIndependent ℂ r)
    (hr : ∀ j f, ⟪r j,f⟫_ℂ = spectralSobolevPairing f (jetVec(χ,hα.le,j)))
    (S : Finset (SpectralStripJetIndex χ a α 0)) (hS : ∀ i ∈ S, i.val.1 = ω)
    (hpred : ∀ i ∈ S, i.lowerOne ∈ S)
    (e : OrthonormalBasis S ℂ (Submodule.span ℂ (Set.range fun i : S ↦ r i.val))) :
    let Θ := globalThetaSobolev F a (neg_le_self hα.le) (le_rfl : 0 ≤ (0 : ℝ))
    let A := spectralConvolution (F := F) a (neg_le_self hα.le) (le_rfl : 0 ≤ (0 : ℝ)) φ
    let V := Submodule.span ℂ (r '' {j | j.val.1 = ω})
    let U := (hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα.le) le_rfl ψ).adjoint.comp V.subtypeL
    (L-α) * ∑ k, ‖A.adjoint (Θ.mkQ (e k : W(α)))‖^2 ≤
      ‖U‖^2 * ∑ i : S, (((L : ℂ) - conj site(i.val))⁻¹).re := by
  classical
  let T (f : BruhatCompactSupport C𝔽) : W(α) →L[ℂ] W(α) :=
    hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα.le) le_rfl f
  let Θ := globalThetaSobolev F a (neg_le_self hα.le) (le_rfl : 0 ≤ (0 : ℝ))
  let A := spectralConvolution (F := F) a (neg_le_self hα.le) (le_rfl : 0 ≤ (0 : ℝ)) φ
  let V : Submodule ℂ W(α) := Submodule.span ℂ (r '' {j | j.val.1 = ω})
  let v (i : S) := r i.val
  let d (i : S) := (L : ℂ)-conj site(i.val)
  let degree (i : S) := i.val.val.2.2.2
  let pred (i : S) : S := ⟨i.val.lowerOne, hpred i.val i.property⟩
  have hdeg (i : S) (hi : degree i ≠ 0) : degree (pred i) < degree i := by
    change degree i - 1 < degree i
    omega
  have hd (i : S) : 0 ≤ ((d i)⁻¹).re := by
    have hh := i.val.abs_re_lt_width
    rw [Complex.inv_re]
    exact div_nonneg (by change 0 ≤ L - site(i.val).re; linarith [(abs_lt.mp hh).2]) (normSq_nonneg _)
  have hU (i : S) : (T ψ).adjoint (v i) =
      (T φ).adjoint (d i • v i - (degree i : ℂ) • v (pred i)) :=
    spectralStripJet_adjoint_affine_companion χ hα.le r hr i.val φ ψ L (by simpa only [hS i.val i.property] using hψ)
  have hform (c : S → ℂ) : (L-α) * ‖∑ i : S, c i • v i‖^2 ≤
      (⟪∑ i : S, c i • v i, ∑ i : S, c i •
        (d i • v i - (degree i : ℂ) • v (pred i))⟫_ℂ).re := by
    let f (j : SpectralStripJetIndex χ a α 0) := if hj : j ∈ S then c ⟨j,hj⟩ else 0
    have hs (w : SpectralStripJetIndex χ a α 0 → W(α)) :
        ∑ j ∈ S, f j • w j = ∑ i : S, c i • w i.val := by
      rw [← Finset.sum_coe_sort]
      apply Fintype.sum_congr; intro i
      simp only [f, dite_eq_left i.property]
    have h := spectralStripJet_riesz_generator_accretive χ hα.le r hr S ω hS f L
    rw [hs r,hs (fun j ↦ ((L : ℂ)-conj site(j)) • r j - (j.val.2.2.2 : ℂ) • r j.lowerOne)] at h
    exact h
  have hraw := finite_jetFamily_companion_column_bound v (hrind.comp (fun i : S ↦ i.val) Subtype.val_injective)
    d degree pred hdeg hd (sub_pos.mpr hL) hform (T φ).adjoint (T ψ).adjoint hU V
    (fun i ↦ Submodule.subset_span ⟨i.val,hS i.val i.property,rfl⟩) e
  have hK : Submodule.span ℂ (Set.range v) ≤ Θᗮ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change v i ∈ Θᗮ
    rw [Submodule.mem_orthogonal']
    intro y hy
    rw [show v i = r i.val from rfl, hr]
    exact spectralStripJet_commonKernel_forward χ hα.le le_rfl y hy i.val
  have hQ (k : S) : ‖A.adjoint (Θ.mkQ (e k : W(α)))‖ = ‖(T φ).adjoint (e k : W(α))‖ :=
    quotient_adjoint_column_norm Θ (T φ) A (spectralConvolution_mkQ a (neg_le_self hα.le) le_rfl φ) _
      (hK (e k).property)
  change (L-α) * ∑ k, ‖A.adjoint (Θ.mkQ (e k : W(α)))‖^2 ≤ _
  simp_rw [hQ]
  exact hraw

/-- Paper: Theorem 10.4.2.1, p. 459. Quantitative estimate on every finite predecessor-closed
family in a single mode, simultaneously for all positive widths at most A.
Its right hand side uses the actual companion norm on the full mode. -/
theorem spectralStripConvolution_finite_jet_bound_uniform_width
    (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual C𝔽)
    (a A : ℝ) {α : ℝ} (hα : 0 < α) (hwidth : α ≤ A) (φ ψ : BruhatCompactSupport C𝔽)
    (ω : PontryaginDual (ideleClassNorm F).ker)
    (hψ : ∀ z : ℂ, (∫ g : C𝔽, ψ.val g * ideleClassNormTwist (χ ω) z g ∂μ𝔽) =
      (((A+1 : ℝ):ℂ)-z) * ∫ g : C𝔽, φ.val g * ideleClassNormTwist (χ ω) z g ∂μ𝔽)
    (r : SpectralStripJetIndex χ a α 0 → W(α)) (hrind : LinearIndependent ℂ r)
    (hr : ∀ j f, ⟪r j,f⟫_ℂ = spectralSobolevPairing f (jetVec(χ,hα.le,j)))
    (S : Finset (SpectralStripJetIndex χ a α 0)) (hS : ∀ i ∈ S, i.val.1 = ω)
    (hpred : ∀ i ∈ S, i.lowerOne ∈ S)
    (e : OrthonormalBasis S ℂ (Submodule.span ℂ (Set.range fun i : S ↦ r i.val))) :
    let Θ := globalThetaSobolev F a (neg_le_self hα.le) (le_rfl : 0 ≤ (0 : ℝ))
    let T := spectralConvolution (F := F) a (neg_le_self hα.le) (le_rfl : 0 ≤ (0 : ℝ)) φ
    let V := Submodule.span ℂ (r '' {j | j.val.1 = ω})
    let U := (hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα.le) le_rfl ψ).adjoint.comp V.subtypeL
    ∑ k, ‖T.adjoint (Θ.mkQ (e k : W(α)))‖^2 ≤
      (1+2*A)*‖U‖^2 * ∑ i : S, (1+i.val.val.2.2.1^2)⁻¹ := by
  let Θ := globalThetaSobolev F a (neg_le_self hα.le) (le_rfl : 0 ≤ (0 : ℝ))
  let T := spectralConvolution (F := F) a (neg_le_self hα.le) (le_rfl : 0 ≤ (0 : ℝ)) φ
  let V := Submodule.span ℂ (r '' {j | j.val.1 = ω})
  let U := (hardySobolevTestAction μ𝔽 m𝔽 (-α) α 0 (neg_le_self hα.le) le_rfl ψ).adjoint.comp V.subtypeL
  let E := ∑ k, ‖T.adjoint (Θ.mkQ (e k : W(α)))‖^2
  have hE : 0 ≤ E := Finset.sum_nonneg fun i _ ↦ sq_nonneg _
  have hβ (i : S) : |i.val.val.2.1| < α := by
    simpa only [add_re, mul_I_re, ofReal_im, neg_zero, ofReal_re, add_zero] using i.val.abs_re_lt_width
  exact finite_strip_column_bound_uniform_in_width hwidth hE (fun i : S ↦ i.val.val.2.1)
    (fun i : S ↦ i.val.val.2.2.1) hβ (K := ‖U‖) (spectralStripConvolution_finite_jet_bound χ a hα
      (by linarith : α < A+1) φ ψ ω hψ r hrind hr S hS hpred e)

end
end RiemannMasullo
