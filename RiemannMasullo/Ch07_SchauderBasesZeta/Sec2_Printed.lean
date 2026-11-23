module

public import Mathlib.Algebra.Field.ULift
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
import all RiemannMasullo.Ch03_IdelicZeta.Sec4
import all RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a

/-! # §7.2 Claims that are false as printed -/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set Topology
open scoped BigOperators NNReal NumberField.AdeleRing

namespace RiemannMasullo
namespace Printed

set_option quotPrecheck false

universe u

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ(" F ", " S ")" => SIdeleQuotient F S
local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "Xₛ(" F ", " S ")" => QuasiCharacter (Jₛ(F, S))
local notation "ℬₛ(" F ", " S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "ℬ𝔽(" F ")" => SchwartzBruhat (Multiplicative (𝔸[F]))
local notation "mₛ(" F ", " S ")" => sIdeleQuotientNorm F S
local notation "m𝔽(" F ")" => ideleClassNorm F
local notation "J₁(" F ", " S ")" => (mₛ(F, S)).ker
local notation "hmₛ(" F ", " S ")" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "twistₛ(" F ", " S ")" =>
  quasiCharacterNormTwist (G := Jₛ(F, S)) mₛ(F, S) hmₛ(F, S)
local notation "dualₛ(" F ", " S ")" => dualQuasiCharacter (G := Jₛ(F, S)) mₛ(F, S) hmₛ(F, S)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "onComponent(" F ", " S ", " c ", " ω ")" =>
  (normOneRestriction mₛ(F, S) c = (circleToComplex).comp ω)
local notation "Θₛ(" F ", " S ", " ω ")" => SLocalHomogeneousThetaSpace F S ω
local notation "Kₛ(" F ", " S ", " ω ")" => LinearMap.ker (sLocalHomogeneousAdelicThetaLinearMap F S ω)
local notation "K𝔽(" F ", " ω ")" => LinearMap.ker (homogeneousAdelicThetaLinearMap F ω)
local notation "poleLocus(" F ", " S ")" => ({c : Xₛ(F, S) | 0 < sLocalRhoPoleOrder c})
local notation "globalUnitary(" F ", " χ ")" => ((circleToComplex).comp χ : QuasiCharacter (C𝔽(F)))
local notation "globalNormOne(" F ", " χ ")" =>
  ((χ).comp (⟨(m𝔽(F)).ker.subtype, continuous_subtype_val⟩ : (m𝔽(F)).ker →ₜ* C𝔽(F))
    : PontryaginDual (m𝔽(F)).ker)
local notation "localChart(" F ", " S ", " χ ", " h ")" =>
  twistₛ(F, S) (sIdeleRestriction F S ⟨globalUnitary(F, χ), h⟩)
local notation "outsideS(" h₀ ", " hχ ")" => (fun v hv ↦ hχ v (fun hv₀ ↦ hv (h₀ hv₀)))

/-- Paper: Definition 7.1.2.1, p. 316, and Theorem 7.2.1.1(1), p. 334.
The literal nonnegative subscript in §7.1 denotes the coefficient of the positive
power, including the constant at index zero. -/
def sLocalNonnegativeLaurentCoeff {F : Type u} [Field F] [NumberField F] {S : Finset Places(F)}
    (c : Xₛ(F, S)) (k : ℕ) : StrongDual ℂ ℬₛ(F, S) :=
  let a := fun f : ℬₛ(F, S) ↦ sLocalZLaurentCoeff f c (k : ℤ)
  let h := sLocalZLaurentCoeff_continuous_linear c (k : ℤ)
  ⟨h.2.mk' a, h.1⟩

/-- Paper: Equation (7.2.1.8), p. 334.
Every closed rectifiable contour bounding the indicated domain gives the coefficient.
Rectifiable contours are integrated in Lipschitz parametrizations, available by
arclength reparametrization. Both directions of traversal are allowed. -/
def sLocalPrincipalPartCoeff_any_contour : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (c : Xₛ(F, S)),
    c ∈ poleLocus(F, S) → ∀ (k : ℕ) (f : ℬₛ(F, S)) (γ : ℝ → ℂ),
    (∃ K : ℝ≥0, LipschitzOnWith K γ (Icc 0 1)) → γ 0 = γ 1 →
    let bounds := fun D : Set ℂ ↦ IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧
      frontier D = γ '' Icc 0 1
    ∀ D : Set ℂ, bounds D → (∀ U, bounds U → U = D) → 0 ∈ D →
      let integrand := fun t : ℝ ↦ (γ t) ^ ((k : ℤ) - 1) *
        sLocalIdelicZFunction f (twistₛ(F, S) c (γ t)) * deriv γ t
      IntervalIntegrable integrand MeasureTheory.volume 0 1 ∧
        sLocalNonnegativeLaurentCoeff c k f = (∫ t in (0 : ℝ)..1, integrand t) / (2 * (Real.pi : ℂ) * Complex.I)

/-- Paper: Theorem 7.2.1.1(2), p. 334.
Each coefficient descends to the homogeneous theta quotient and is an
eigendistribution of weight equal to its center. -/
def sLocalPrincipalPartCoeff_eigendistribution : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (ω : PontryaginDual J₁(F, S)) (c : Xₛ(F, S)), onComponent(F, S, c, ω) → ∀ k : ℕ,
    LinearMap.ker (sLocalAdelicTheta F S) ≤ (sLocalNonnegativeLaurentCoeff c k).ker ∧
      Kₛ(F, S, ω) ≤ (sLocalNonnegativeLaurentCoeff c k).ker ∧
      sLocalNonnegativeLaurentCoeff c k ∈ sLocalEigendistributions c

open scoped TensorProduct in
/-- A product of local tests at the archimedean places and the places of `S` is a
test on the S-adeles. -/
private theorem sLocalPrincipalPartCoeff_eigendistribution_tensor {F : Type u} [Field F]
    [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (a : (w : InfinitePlace F) → SchwartzBruhat (Multiplicative w.Completion))
    (b : (v : S) → SchwartzBruhat (Multiplicative (v.val.adicCompletion F))) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)), ∀ x : SAdeleRing F S,
      f (Multiplicative.ofAdd x) =
        (∏ w, a w (Multiplicative.ofAdd (x.1 w))) * ∏ v, b v (Multiplicative.ofAdd (x.2 v)) := by
  classical
  let G (w : InfinitePlace F) := Multiplicative w.Completion
  let (w : InfinitePlace F) : T2Space (G w) := (inferInstance : T2Space w.Completion)
  let (w : InfinitePlace F) : LocallyCompactSpace (G w) :=
    (inferInstance : LocallyCompactSpace w.Completion)
  let (w : InfinitePlace F) : SecondCountableTopology (G w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  obtain ⟨a₀, ha⟩ := schwartzBruhat_pi_test G a
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ* ((w : InfinitePlace F) → G w) :=
    { toFun := fun x w ↦ Multiplicative.ofAdd (x.toAdd w)
      invFun := fun x ↦ Multiplicative.ofAdd (fun w ↦ (x w).toAdd)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let arch : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨a₀.val ∘ e, schwartzBruhat_mem_comp_equiv e a₀.property⟩
  obtain ⟨t, ht⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  refine ⟨t (arch ⊗ₜ[ℂ] (⨂ₜ[ℂ] v : S, b v)), fun x ↦ ?_⟩
  rw [ht arch b x]
  exact congrArg (· * _) (ha (e (Multiplicative.ofAdd x.1)))

/-- For a function holomorphic on a closed disc, the residue formula of the Laurent
coefficients gives its Taylor coefficients. -/
private theorem sLocalPrincipalPartCoeff_eigendistribution_residue {h : ℂ → ℂ} {R : ℝ≥0}
    (hR : 0 < R)
    (hh : DifferentiableOn ℂ h (Metric.closedBall 0 R)) (k : ℕ) :
    complexResidue (fun z ↦ h z / z ^ ((k : ℤ) + 1)) 0 =
      cauchyPowerSeries h 0 R k (fun _ ↦ 1) := by
  refine (tendsto_const_nhds.congr' ?_).limUnder_eq
  filter_upwards [Ioo_mem_nhdsGT hR] with r hr
  have := sLocalZLaurentCoeff_hasLaurentSeries_circleIntegral (g := h) (h := h) (N := 0) hR hh
    (fun z _ ↦ by simp) k hr
  simpa using this.symm

/-- Two functions holomorphic on a closed disc whose residue coefficients are
proportional agree up to that factor on the open disc. -/
private theorem sLocalPrincipalPartCoeff_eigendistribution_eqOn {A B : ℂ → ℂ} {R : ℝ≥0}
    (hR : 0 < R) (a : ℂ)
    (hA : DifferentiableOn ℂ A (Metric.closedBall 0 R))
    (hB : DifferentiableOn ℂ B (Metric.closedBall 0 R))
    (hc : ∀ k : ℕ, complexResidue (fun z ↦ B z / z ^ ((k : ℤ) + 1)) 0 =
      a * complexResidue (fun z ↦ A z / z ^ ((k : ℤ) + 1)) 0)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) R) : B z = a * A z := by
  simp only [sLocalPrincipalPartCoeff_eigendistribution_residue hR hA, sLocalPrincipalPartCoeff_eigendistribution_residue hR hB] at hc
  have hz' : z ∈ Metric.eball (0 : ℂ) R := by
    rw [Metric.mem_eball, edist_zero_right]
    exact_mod_cast (mem_ball_zero_iff.mp hz)
  have hsA := (hA.hasFPowerSeriesOnBall hR).hasSum hz'
  have hsB := (hB.hasFPowerSeriesOnBall hR).hasSum hz'
  have hterm (p : FormalMultilinearSeries ℂ ℂ ℂ) (n : ℕ) :
      p n (fun _ ↦ z) = z ^ n * p n (fun _ ↦ 1) := by
    have := (p n).map_smul_univ (fun _ ↦ z) (fun _ ↦ 1)
    simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  simp only [zero_add, hterm, hc] at hsA hsB
  have := hsA.mul_left a
  refine hsB.unique (this.congr_fun fun n ↦ by ring)

/-- Translating a test by an S-idele multiplies its zeta integral by the character
at the class of that idele. -/
private theorem sLocalPrincipalPartCoeff_eigendistribution_translate {F : Type u} [Field F]
    [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (u : (SAdeleRing F S)ˣ)
    (c : QuasiCharacter (SIdeleQuotient F S)) :
    sLocalIdelicZetaIntegral (schwartzBruhatUnitTranslate u f) c =
      c (QuotientGroup.mk u) * sLocalIdelicZetaIntegral f c := by
  let (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
  let (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F) := borel _
  let : MeasurableSpace (InfiniteAdeleRing F) :=
    inferInstanceAs (MeasurableSpace ((w : InfinitePlace F) → w.Completion))
  let : MeasurableSpace (SAdeleRing F S) :=
    inferInstanceAs (MeasurableSpace (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  let : BorelSpace (SAdeleRing F S)ˣ := sIdeleGroup_borelSpace
  let := sMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) (S := S)
  unfold sLocalIdelicZetaIntegral
  rw [← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_mul_left_eq_self _ u]
  congr 1
  funext g
  rw [schwartzBruhatUnitTranslate_apply, Units.val_mul, ← mul_assoc, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, one_mul, QuotientGroup.mk_mul, map_mul]
  ring

/-- Over ℚ with only the real place, take the standard Gaussian, whose Z-function does not
vanish at `1/2` on the trivial component, and translate it by an idele of norm different
from one. If every coefficient there were an eigendistribution, the two Z-functions would
have proportional Taylor series, which forces the Z-function to vanish near `1/2`. -/
private theorem sLocalPrincipalPartCoeff_eigendistribution_false_aux :
    ¬ sLocalPrincipalPartCoeff_eigendistribution.{u} := by
  intro h
  let := NumberField.of_ringEquiv ℚ (ULift.{u} ℚ) (ULift.ringEquiv.{0, u} (R := ℚ)).symm
  let F := ULift.{u} ℚ
  let S : Finset (HeightOneSpectrum (𝓞 F)) := ∅
  let tw := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
  let χ : PontryaginDual (SIdeleQuotient F S) := 1
  let s₀ : ℂ := 1 / 2
  let c := tw ((circleToComplex).comp χ) s₀
  let χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ := fun _ ↦ 1
  have hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ) := fun w ↦ by
    ext g; rfl
  obtain ⟨f, hf⟩ := sLocalPrincipalPartCoeff_eigendistribution_tensor S
    (fun w ↦ infiniteStandardGaussian w (χArch w))
    (fun v ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v c))
  have hE := sLocalNormalizedEigendistribution_gaussian χ s₀ χArch hχ f hf
  have hspec := (existsUnique_sLocalNormalizedEigendistribution c).exists.choose_spec f
  have hN : sLocalNormalizedZFunction f c = 1 := by
    rw [← hspec]
    change _ * sLocalNormalizedEigendistribution c f = 1
    rw [hE]
    simp [S]
  have hpos : s₀ ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
    show (0 : ℝ) < (1 / 2 : ℂ).re
    norm_num
  have hdiv := sLocalNormalizedZFunction_eq_div f χ hpos
  have hI : sLocalIdelicZetaIntegral f c ≠ 0 := by
    intro h0
    change sLocalNormalizedZFunction f c = _ at hdiv
    rw [hdiv, h0, zero_div] at hN
    exact zero_ne_one hN
  have hZ : sLocalIdelicZFunction f c = sLocalIdelicZetaIntegral f c :=
    sLocalIdelicZFunction_eq_integral f ⟨χ, s₀, hpos, rfl⟩
  have htw (z : ℂ) : tw c z = tw ((circleToComplex).comp χ) (s₀ + z) := by
    ext1 g
    have hm : ((((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    change ((circleToComplex).comp χ) g * (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ) ^ s₀ *
        (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ) ^ z = ((circleToComplex).comp χ) g *
        (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ) ^ (s₀ + z)
    rw [mul_assoc, ← Complex.cpow_add _ _ hm]
  have hopen : IsOpen (Complex.re ⁻¹' Ioi (0 : ℝ)) := isOpen_Ioi.preimage Complex.continuous_re
  have hZa (g : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (w : ℂ) (hw : 0 < w.re) :
      AnalyticAt ℂ (fun z ↦ sLocalIdelicZFunction g (tw ((circleToComplex).comp χ) z)) w :=
    ((sLocalIdelicZetaIntegral_analyticOn g χ) w hw).congr
      (Filter.eventually_of_mem (hopen.mem_nhds hw) fun z hz ↦
        (sLocalIdelicZFunction_eq_integral g ⟨χ, z, hz, rfl⟩).symm)
  -- the component and a translation of nontrivial norm
  have hon : normOneRestriction (sIdeleQuotientNorm F S) c =
      (circleToComplex).comp (1 : PontryaginDual (sIdeleQuotientNorm F S).ker) := by
    ext g
    change ((circleToComplex).comp χ) g.val *
      (((sIdeleQuotientNorm F S g.val : ℝ≥0) : ℝ) : ℂ) ^ s₀ = ((1 : Circle) : ℂ)
    rw [MonoidHom.mem_ker.mp g.property]
    simp only [Units.val_one, NNReal.coe_one, Complex.ofReal_one, Complex.one_cpow, mul_one]
    rfl
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (σ t)
  have hmu : sIdeleQuotientNorm F S (QuotientGroup.mk u) ≠ 1 := by
    rw [hu, hσ t]; exact ht
  have hk (k : ℕ) := (mem_sLocalEigendistributions c _).mp (h F S 1 c hon k).2.2 u f
  let τf := schwartzBruhatUnitTranslate u f
  let A : ℂ → ℂ := fun z ↦ sLocalIdelicZFunction f (tw c z)
  let B : ℂ → ℂ := fun z ↦ sLocalIdelicZFunction τf (tw c z)
  let R : ℝ≥0 := 1 / 4
  have hR : 0 < R := by norm_num [R]
  have hball (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) R) : 0 < (s₀ + z).re := by
    have h1 := Complex.abs_re_le_norm z
    rw [mem_closedBall_zero_iff] at hz
    have h2 : ((R : ℝ)) = 1 / 4 := by norm_num [R]
    simp only [Complex.add_re, s₀]
    norm_num
    have := (abs_le.mp (h1.trans (hz.trans h2.le))).1
    linarith
  have hdiff (g : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
      DifferentiableOn ℂ (fun z ↦ sLocalIdelicZFunction g (tw c z)) (Metric.closedBall 0 R) := by
    intro z hz
    simp only [htw]
    exact ((hZa g _ (hball z hz)).comp_of_eq (by fun_prop) rfl).differentiableAt.differentiableWithinAt
  have hc (k : ℕ) : complexResidue (fun z ↦ B z / z ^ ((k : ℤ) + 1)) 0 =
      c (QuotientGroup.mk u) * complexResidue (fun z ↦ A z / z ^ ((k : ℤ) + 1)) 0 := hk k
  have hBA := sLocalPrincipalPartCoeff_eigendistribution_eqOn hR (c (QuotientGroup.mk u)) (hdiff f) (hdiff τf) hc
  have hcu : c (QuotientGroup.mk u) ≠ 0 := by
    intro h0
    have := map_mul c (QuotientGroup.mk u) (QuotientGroup.mk u)⁻¹
    rw [mul_inv_cancel, map_one, h0, zero_mul] at this
    exact one_ne_zero this
  have hmpos : 0 < (((sIdeleQuotientNorm F S (QuotientGroup.mk u) : ℝ≥0) : ℝ)) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  have hm1 : (((sIdeleQuotientNorm F S (QuotientGroup.mk u) : ℝ≥0) : ℝ)) ≠ 1 := by
    intro h1
    exact hmu (Units.val_eq_one.mp (NNReal.coe_eq_one.mp h1))
  have hzero (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) (1 / 4)) : A x = 0 := by
    have hxb : (x : ℂ) ∈ Metric.ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx.1]
      norm_num [R]
      exact hx.2
    have e1 := hBA x hxb
    have e2 : B x = (tw c x) (QuotientGroup.mk u) * A x := by
      have hp := hball x (Metric.ball_subset_closedBall hxb)
      change sLocalIdelicZFunction τf (tw c x) = _ * sLocalIdelicZFunction f (tw c x)
      rw [htw, sLocalIdelicZFunction_eq_integral τf ⟨χ, _, hp, rfl⟩,
        sLocalIdelicZFunction_eq_integral f ⟨χ, _, hp, rfl⟩, sLocalPrincipalPartCoeff_eigendistribution_translate]
    have e3 : (tw c x) (QuotientGroup.mk u) = c (QuotientGroup.mk u) *
        ((((sIdeleQuotientNorm F S (QuotientGroup.mk u) : ℝ≥0) : ℝ) ^ x : ℝ) : ℂ) := by
      change c _ * _ ^ (x : ℂ) = _
      rw [Complex.ofReal_cpow hmpos.le]
    rw [e3, mul_assoc] at e2
    have e4 := mul_left_cancel₀ hcu (e2.symm.trans e1)
    have hne : ((((sIdeleQuotientNorm F S (QuotientGroup.mk u) : ℝ≥0) : ℝ) ^ x : ℝ) : ℂ) ≠ 1 := by
      rw [Ne, Complex.ofReal_eq_one]
      intro h1
      have := congrArg Real.log h1
      rw [Real.log_rpow hmpos, Real.log_one, mul_eq_zero] at this
      rcases this with h2 | h2
      · exact hx.1.ne' h2
      · exact hm1 (Real.eq_one_of_pos_of_log_eq_zero hmpos h2)
    have e5 : (((((sIdeleQuotientNorm F S (QuotientGroup.mk u) : ℝ≥0) : ℝ) ^ x : ℝ) : ℂ) - 1) *
        A x = 0 := by rw [sub_mul, e4, one_mul, sub_self]
    exact (mul_eq_zero.mp e5).resolve_left (sub_ne_zero.mpr hne)
  have hA0 : A 0 = 0 := by
    have hcont : ContinuousAt A 0 := (hdiff f).continuousOn.continuousAt
      (Metric.closedBall_mem_nhds 0 hR)
    have ht1 : Tendsto (fun x : ℝ ↦ A x) (𝓝[>] 0) (𝓝 (A 0)) := by
      have := (hcont.comp_of_eq (Complex.continuous_ofReal.continuousAt (x := (0 : ℝ)))
        Complex.ofReal_zero).tendsto
      exact this.mono_left nhdsWithin_le_nhds
    have ht2 : Tendsto (fun x : ℝ ↦ A x) (𝓝[>] 0) (𝓝 0) :=
      tendsto_const_nhds.congr' (Filter.eventually_of_mem (Ioo_mem_nhdsGT (by norm_num))
        fun x hx ↦ (hzero x hx).symm)
    exact tendsto_nhds_unique ht1 ht2
  have h4 : tw c 0 = c := by
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    rw [Complex.cpow_zero, mul_one]
  change sLocalIdelicZFunction f (tw c 0) = 0 at hA0
  rw [h4, hZ] at hA0
  exact hI hA0

/-- Paper: Theorem 7.2.1.1(2), p. 334.
For ℚ at the real place, translate a nonzero nonnegative even bump supported in
2 < |x| < 3 by dilation by 2. At the trivial center its first Mellin derivative
increases by log(2) times the positive constant coefficient. With the polar
reading of (7.2.1.8), use the Gaussian times the integer indicator over ℚ at
∞ and p. The top coefficient is 2/log p, so translation by p changes the
residue by −2 at the trivial character. -/
theorem sLocalPrincipalPartCoeff_eigendistribution_false :
    ¬ sLocalPrincipalPartCoeff_eigendistribution :=
  sLocalPrincipalPartCoeff_eigendistribution_false_aux

/-- Paper: Theorem 7.2.1.1(3), p. 334.
A nonzero coefficient functional forces the corresponding pole-order bound on every test. -/
def sLocalPrincipalPartCoeff_universal_pole_bound : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (c : Xₛ(F, S)) (k : ℕ),
    sLocalNonnegativeLaurentCoeff c k ≠ 0 →
      c ∈ poleLocus(F, S) ∧ ∀ f : ℬₛ(F, S), k ≤ sLocalPolarMultiplicity f c

/-- Over ℚ with only the real place, the standard Gaussian has Z-function equal to the
Euler factor times its normalized value one, so it does not vanish at `1/2` on the trivial
component. There the correcting factor is regular, so the constant coefficient is a nonzero
functional at a character outside the pole locus. -/
private theorem sLocalPrincipalPartCoeff_universal_pole_bound_false_aux :
    ¬ sLocalPrincipalPartCoeff_universal_pole_bound.{u} := by
  intro h
  let := NumberField.of_ringEquiv ℚ (ULift.{u} ℚ) (ULift.ringEquiv.{0, u} (R := ℚ)).symm
  let F := ULift.{u} ℚ
  let S : Finset (HeightOneSpectrum (𝓞 F)) := ∅
  let tw := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
  let χ : PontryaginDual (SIdeleQuotient F S) := 1
  let s₀ : ℂ := 1 / 2
  let c := tw ((circleToComplex).comp χ) s₀
  let χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ := fun _ ↦ 1
  have hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ) := fun w ↦ by
    ext g; rfl
  obtain ⟨f, hf⟩ := sLocalPrincipalPartCoeff_eigendistribution_tensor S (fun w ↦ infiniteStandardGaussian w (χArch w))
    (fun v ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v c))
  have hE := sLocalNormalizedEigendistribution_gaussian χ s₀ χArch hχ f hf
  have hspec := (existsUnique_sLocalNormalizedEigendistribution c).exists.choose_spec f
  have hN : sLocalNormalizedZFunction f c = 1 := by
    rw [← hspec]
    change _ * sLocalNormalizedEigendistribution c f = 1
    rw [hE]
    simp [S]
  have hpos : s₀ ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
    show (0 : ℝ) < (1 / 2 : ℂ).re
    norm_num
  have hdiv := sLocalNormalizedZFunction_eq_div f χ hpos
  have hI : sLocalIdelicZetaIntegral f c ≠ 0 := by
    intro h0
    change sLocalNormalizedZFunction f c = _ at hdiv
    rw [hdiv, h0, zero_div] at hN
    exact zero_ne_one hN
  have hZ : sLocalIdelicZFunction f c = sLocalIdelicZetaIntegral f c :=
    sLocalIdelicZFunction_eq_integral f ⟨χ, s₀, hpos, rfl⟩
  have htw (z : ℂ) : tw c z = tw ((circleToComplex).comp χ) (s₀ + z) := by
    ext1 g
    have hm : ((((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ)) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
    change ((circleToComplex).comp χ) g * (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ) ^ s₀ *
        (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ) ^ z = ((circleToComplex).comp χ) g *
        (((sIdeleQuotientNorm F S g : ℝ≥0) : ℝ) : ℂ) ^ (s₀ + z)
    rw [mul_assoc, ← Complex.cpow_add _ _ hm]
  have hopen : IsOpen (Complex.re ⁻¹' Ioi (0 : ℝ)) := isOpen_Ioi.preimage Complex.continuous_re
  have hZa : AnalyticAt ℂ (fun z ↦ sLocalIdelicZFunction f (tw ((circleToComplex).comp χ) z)) s₀ :=
    ((sLocalIdelicZetaIntegral_analyticOn f χ) s₀ hpos).congr
      (Filter.eventually_of_mem (hopen.mem_nhds hpos) fun z hz ↦
        (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩).symm)
  have hg : AnalyticAt ℂ (fun z ↦ sLocalIdelicZFunction f (tw c z)) 0 := by
    simp only [htw]
    exact hZa.comp_of_eq (by fun_prop) (add_zero s₀)
  have hR : AnalyticAt ℂ (fun z ↦ sLocalRhoFactor (tw c z)) 0 := by
    simp only [htw]
    exact (sLocalRhoFactor_analyticAt_criticalLine χ s₀ (by norm_num [s₀])).comp_of_eq
      (by fun_prop) (add_zero s₀)
  have hcoeff : sLocalNonnegativeLaurentCoeff c 0 ≠ 0 := by
    intro h0
    have h1 : sLocalZLaurentCoeff f c ((0 : ℕ) : ℤ) = 0 := DFunLike.congr_fun h0 f
    unfold sLocalZLaurentCoeff at h1
    have h2 : (fun z ↦ sLocalIdelicZFunction f (tw c z) / z ^ (((0 : ℕ) : ℤ) + 1)) =
        fun z ↦ sLocalIdelicZFunction f (tw c z) / (z - 0) := by
      funext z; simp
    have h3 := complexResidue_div_sub hg
    change complexResidue (fun z ↦ sLocalIdelicZFunction f (tw c z) / z ^ (((0 : ℕ) : ℤ) + 1)) 0
      = 0 at h1
    rw [h2, h3] at h1
    have h4 : tw c 0 = c := by
      ext1 g
      change c g * _ ^ (0 : ℂ) = c g
      rw [Complex.cpow_zero, mul_one]
    rw [h4, hZ] at h1
    exact hI h1
  have hpole := (h F S c 0 hcoeff).1
  change 0 < sLocalRhoPoleOrder c at hpole
  unfold sLocalRhoPoleOrder sLocalIdelicOrderBound at hpole
  rw [min_eq_left hR.meromorphicOrderAt_nonneg] at hpole
  simp at hpole

/-- Paper: Theorem 7.2.1.1(3), p. 334.
At the trivial character over ℚ with only the real place, an even nonnegative
nonzero bump on 2 < |x| < 3 has positive first Mellin derivative and no pole. -/
theorem sLocalPrincipalPartCoeff_universal_pole_bound_false :
    ¬ sLocalPrincipalPartCoeff_universal_pole_bound :=
  sLocalPrincipalPartCoeff_universal_pole_bound_false_aux

/-- Paper: Theorem 7.2.1.1(4), p. 334.
For every supported pole bound, its annihilator is generated in the strong dual
by the above-bound coefficients, asserted to be eigendistributions of their centers.
Deviation: The bound is extended by zero off its support in the allowed pole locus. -/
def sLocalThetaPoleBound_eigen_annihilator : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (ω : PontryaginDual J₁(F, S))
    (U : Set Xₛ(F, S)) (_hU : U ⊆ poleLocus(F, S)) (m : Xₛ(F, S) → ℕ) (_hm : ∀ c ∉ U, m c = 0),
    IsClosed (sLocalThetaPoleBound ω m : Set (Θₛ(F, S, ω))) ∧
    (sLocalThetaPoleBound ω m).dualAnnihilator.comap (ContinuousLinearMap.coeLM ℂ) =
      (Submodule.span ℂ {T : StrongDual ℂ (Θₛ(F, S, ω)) |
        ∃ (c : Xₛ(F, S)) (_hc : onComponent(F, S, c, ω)) (k : ℕ),
          c ∈ poleLocus(F, S) ∧ m c < k ∧
            ∀ f : ℬₛ(F, S), T ((Kₛ(F, S, ω)).mkQ f) = sLocalNonnegativeLaurentCoeff c k f
      }).topologicalClosure ∧
    (∀ (c : Xₛ(F, S)), onComponent(F, S, c, ω) → c ∈ poleLocus(F, S) → ∀ k : ℕ, m c < k →
      sLocalNonnegativeLaurentCoeff c k ∈ sLocalEigendistributions c)

/-- Paper: Theorem 7.2.1.1(4), p. 334.
For the zero bound over ℚ at the real place, the first positive coefficient
is among the asserted eigendistributions. On a positive even bump supported in
2 < |x| < 3, dilation by 2 changes it by log(2) times the nonzero constant term. -/
theorem sLocalThetaPoleBound_eigen_annihilator_false :
    ¬ sLocalThetaPoleBound_eigen_annihilator := by sorry

/-- Paper: Remark 7.2.1.2, p. 335, first sequence.
The coefficient map on tests descends to the indicated quotient, has the printed
kernel, and maps onto the printed product. The index set in the display ranges
over the selected divisor on the character space. -/
def sLocalThetaPoleBound_low_coefficients_exact : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (ω : PontryaginDual J₁(F, S))
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places(F)) (_h₀ : S₀ ⊆ S),
    let n := sLocalSelectedPoleMultiplicity SArch S₀ (F := F) (S := S)
    let I := {i : Xₛ(F, S) × ℕ // 0 < i.2 ∧ i.2 ≤ n i.1}
    ∃ A : Θₛ(F, S, ω) →ₗ[ℂ] (I → ℂ), A.ker = sLocalThetaPoleBound ω n ∧
      Function.Surjective A ∧ ∀ (f : ℬₛ(F, S)) (i : I),
        A ((Kₛ(F, S, ω)).mkQ f) i = sLocalNonnegativeLaurentCoeff i.val.1 i.val.2 f

private theorem ulift_rat_numberField : NumberField (ULift.{u} ℚ) :=
  NumberField.of_ringEquiv ℚ (ULift.{u} ℚ) (ULift.ringEquiv.{0, u} (R := ℚ)).symm

/-- Every test has at most the allowed pole order of the correcting factor. -/
private theorem sLocalThetaPoleBound_low_coefficients_exact_polar_le {F : Type u} [Field F]
    [NumberField F] {S : Finset Places(F)} (f : ℬₛ(F, S)) (c : Xₛ(F, S)) :
    sLocalPolarMultiplicity f c ≤ sLocalRhoPoleOrder c := by
  let : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  have := isClosed_sProjectedDiagonal (F := F) (S := S)
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  have hne : ∃ g, mₛ(F, S) g ≠ 1 := ⟨σ t, (hσ t).trans_ne ht⟩
  have hpos (g : Jₛ(F, S)) : 0 < ((mₛ(F, S) g : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  -- Write the character as a norm twist of a unitary character.
  let a := quasiCharacterAbscissa mₛ(F, S) (isProperMap_sIdeleQuotientNorm F S) hne c
  let d := twistₛ(F, S) c (-(a : ℂ))
  have hd (g : Jₛ(F, S)) : ‖d g‖ = 1 := by
    change ‖c g * (((mₛ(F, S) g : ℝ≥0) : ℝ) : ℂ) ^ (-(a : ℂ))‖ = 1
    rw [norm_mul, norm_quasiCharacter_eq_rpow_abscissa mₛ(F, S)
        (isProperMap_sIdeleQuotientNorm F S) hne,
      Complex.norm_cpow_eq_rpow_re_of_pos (hpos g), Complex.neg_re, Complex.ofReal_re]
    exact (Real.rpow_add (hpos g) a (-a)).symm.trans (by simp)
  let χ : PontryaginDual Jₛ(F, S) :=
    { toFun := fun g ↦ ⟨d g, mem_sphere_zero_iff_norm.mpr (hd g)⟩
      map_one' := Circle.ext (map_one d)
      map_mul' := fun x y ↦ Circle.ext (map_mul d x y)
      continuous_toFun := d.continuous.subtype_mk _ }
  have htwist (z : ℂ) : twistₛ(F, S) c z = twistₛ(F, S) ((circleToComplex).comp χ) (z + a) := by
    ext1 g
    change c g * _ ^ z = c g * _ ^ (-(a : ℂ)) * _ ^ (z + a)
    rw [mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (hpos g).ne')]
    ring_nf
  -- Recenter the chart at the abscissa and compare orders there.
  have hZ : meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (twistₛ(F, S) c z)) 0 =
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f
        (twistₛ(F, S) ((circleToComplex).comp χ) z)) a := by
    simp only [htwist]
    exact (meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt (x := (0 : ℂ))
      (c := (a : ℂ)) (f := fun z ↦ sLocalIdelicZFunction f
        (twistₛ(F, S) ((circleToComplex).comp χ) z))).trans (by rw [zero_add])
  have hB : sLocalIdelicOrderBound c = min 0 (meromorphicOrderAt (fun z ↦
      sLocalRhoFactor (twistₛ(F, S) ((circleToComplex).comp χ) z)) a) := by
    simp only [sLocalIdelicOrderBound, htwist]
    exact congrArg (min 0) ((meromorphicOrderAt_fun_comp_add_const_eq_meromorphicOrderAt
      (x := (0 : ℂ)) (c := (a : ℂ)) (f := fun z ↦ sLocalRhoFactor
        (twistₛ(F, S) ((circleToComplex).comp χ) z))).trans (by rw [zero_add]))
  have hle := sLocalIdelicZFunction_poles f χ a
  rw [← hB, ← hZ, sLocalIdelicOrderBound_eq_neg_poleOrder] at hle
  unfold sLocalPolarMultiplicity
  generalize meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (twistₛ(F, S) c z)) 0 = o at hle
  induction o using WithTop.recTopCoe with
  | top => simp
  | coe k =>
    have hk : -(sLocalRhoPoleOrder c : ℤ) ≤ k := WithTop.coe_le_coe.mp hle
    simp only [WithTop.untop₀_coe]
    omega

/-- A span of images of all vectors under a surjective linear map is everything. -/
private theorem sLocalThetaPoleBound_low_coefficients_exact_span_eq_top {M N : Type u}
    {_ : AddCommGroup M} {_ : Module ℂ M} {_ : AddCommGroup N} {_ : Module ℂ N} (q : M →ₗ[ℂ] N)
    (hq : Function.Surjective q) (P : M → Prop) (hP : ∀ f, P f) :
    Submodule.span ℂ {x | ∃ f, q f = x ∧ P f} = ⊤ := by
  refine eq_top_iff.mpr fun x _ ↦ ?_
  obtain ⟨f, rfl⟩ := hq x
  exact Submodule.subset_span ⟨f, rfl, hP f⟩

/-- A linear map onto a nonzero product cannot have full kernel. -/
private theorem sLocalThetaPoleBound_low_coefficients_exact_not_surjective {M ι : Type u}
    {_ : AddCommGroup M} {_ : Module ℂ M} (A : M →ₗ[ℂ] ι → ℂ) (hker : A.ker = ⊤)
    (hs : Function.Surjective A) (i : ι) : False := by
  obtain ⟨x, hx⟩ := hs fun _ ↦ 1
  have hx0 : A x = 0 := LinearMap.mem_ker.mp (hker ▸ Submodule.mem_top)
  exact one_ne_zero ((congrFun hx i).symm.trans (congrFun hx0 i))

/-- With every place selected the bound is the full pole order, which every test
satisfies, so the kernel is everything. The coefficient map would then vanish while
mapping onto a nonzero product. -/
private theorem sLocalThetaPoleBound_low_coefficients_exact_false_aux :
    ¬ sLocalThetaPoleBound_low_coefficients_exact.{u} := by
  intro h
  let := ulift_rat_numberField.{u}
  let F := ULift.{u} ℚ
  let S : Finset Places(F) := ∅
  obtain ⟨A, hker, hsurj, -⟩ := h F S 1 Finset.univ S subset_rfl
  have hn (c : Xₛ(F, S)) : sLocalSelectedPoleMultiplicity Finset.univ S c =
      sLocalRhoPoleOrder c :=
    sLocalSelectedPoleMultiplicity_full c
  have hpos : 0 < sLocalRhoPoleOrder (1 : Xₛ(F, S)) := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces, sLocalPolePlaces_one.1, Finset.card_univ]
    exact Nat.add_pos_left Fintype.card_pos _
  refine sLocalThetaPoleBound_low_coefficients_exact_not_surjective A (hker.trans ?_) hsurj
    ⟨((1 : Xₛ(F, S)), 1), Nat.one_pos, by rw [hn]; exact hpos⟩
  unfold sLocalThetaPoleBound
  refine sLocalThetaPoleBound_low_coefficients_exact_span_eq_top _
    (Submodule.mkQ_surjective _) _ fun f c _ ↦ ?_
  exact (sLocalThetaPoleBound_low_coefficients_exact_polar_le f c).trans_eq (hn c).symm

/-- Paper: Remark 7.2.1.2, p. 335.
Over ℚ with the real place and p, select p. The product of a nonzero nonnegative
even bump supported on 2 < |x| < 3 with the indicator of integer units has entire
trivial-component transform and positive first Taylor coefficient at zero.
Under the polar reading, use a real bump equal to one near zero instead.
Its simple pole there is allowed by the selected bound and has nonzero residue. -/
theorem sLocalThetaPoleBound_low_coefficients_exact_false :
    ¬ sLocalThetaPoleBound_low_coefficients_exact :=
  sLocalThetaPoleBound_low_coefficients_exact_false_aux

open Classical in
/-- Paper: Remark 7.2.1.2, p. 335, second sequence.
The printed sequence of global sections is identified with the first sequence
by Mellin and the indicated principal-part coordinates. On the character surface
a divisor of multiplicity b has b Laurent coordinates in its principal-parts
stalk. Sections of that principal-parts sheaf are their product over the
discrete support. The Mellin transform of an isotype is supported on its component. -/
def sLocalThetaPoleBound_printed_mellin_sequence : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (ω : PontryaginDual J₁(F, S))
    (SArch : Finset (InfinitePlace F)) (S₀ : Finset Places(F)) (_h₀ : S₀ ⊆ S),
    let m := sLocalRhoPoleOrder (F := F) (S := S)
    let n := sLocalSelectedPoleMultiplicity SArch S₀ (F := F) (S := S)
    let r := fun c : Xₛ(F, S) ↦ m c - n c
    let lower := fun (b : Xₛ(F, S) → ℕ) (c : Xₛ(F, S)) ↦ ((-(b c : ℤ) : ℤ) : WithTop ℤ)
    let sections := fun b : Xₛ(F, S) → ℕ ↦
      ↥(meromorphicWithPoleBound (twistₛ(F, S)) (lower b))
    let parts := fun b : Xₛ(F, S) → ℕ ↦ (c : Xₛ(F, S)) → Fin (b c) → ℂ
    ∃ (inc : sections r →ₗ[ℂ] sections m) (P : sections m →ₗ[ℂ] parts r)
        (M : Θₛ(F, S, ω) ≃ₗ[ℂ] sections m) (E : parts r ≃ₗ[ℂ] parts n),
      (∀ (g : sections r) (c : Xₛ(F, S)) (hm : 0 ≤ lower m c) (hr : 0 ≤ lower r c),
        (inc g).val ⟨c, hm⟩ = g.val ⟨c, hr⟩) ∧
      Function.Injective inc ∧ inc.range = P.ker ∧ Function.Surjective P ∧
      (∀ (f : ℬₛ(F, S)) (c : Xₛ(F, S)) (hc : 0 ≤ lower m c),
        (M ((Kₛ(F, S, ω)).mkQ f)).val ⟨c, hc⟩ =
          if onComponent(F, S, c, ω) then sLocalIdelicZFunction f c else 0) ∧
      inc.range.comap M.toLinearMap = sLocalThetaPoleBound ω n ∧
      (∀ (c : Xₛ(F, S)), 0 < n c →
        ∃ e : (Fin (r c) → ℂ) ≃ₗ[ℂ] (Fin (n c) → ℂ), ∀ y : parts r, E y c = e (y c)) ∧
      (∀ (f : ℬₛ(F, S)) (c : Xₛ(F, S)) (j : Fin (n c)),
        E (P (M ((Kₛ(F, S, ω)).mkQ f))) c j = sLocalNonnegativeLaurentCoeff c (j.val + 1) f)

/-- Selecting every place makes the selected divisor the full pole order, so the
remaining divisor vanishes while the selected multiplicity at the trivial character
is positive. A linear equivalence between the two stalks would compare dimensions
zero and positive. -/
private theorem sLocalThetaPoleBound_printed_mellin_sequence_false_aux :
    ¬ sLocalThetaPoleBound_printed_mellin_sequence.{u} := by
  intro h
  let := ulift_rat_numberField.{u}
  let F := ULift.{u} ℚ
  let S : Finset Places(F) := ∅
  obtain ⟨_, _, _, _, -, -, -, -, -, -, he, -⟩ :=
    h F S 1 Finset.univ S subset_rfl
  have hn : sLocalSelectedPoleMultiplicity Finset.univ S (1 : Xₛ(F, S)) =
      sLocalRhoPoleOrder (1 : Xₛ(F, S)) :=
    sLocalSelectedPoleMultiplicity_full 1
  have hpos : 0 < sLocalRhoPoleOrder (1 : Xₛ(F, S)) := by
    rw [sLocalRhoPoleOrder_eq_card_polePlaces, sLocalPolePlaces_one.1, Finset.card_univ]
    exact Nat.add_pos_left Fintype.card_pos _
  obtain ⟨e, -⟩ := he 1 (hn ▸ hpos)
  have hdim := e.finrank_eq
  simp only [Module.finrank_fin_fun, hn, Nat.sub_self] at hdim
  omega

/-- Paper: Remark 7.2.1.2, p. 335.
Over ℚ with the real place and p, select p. At 2πi/log p on the trivial
component the full and selected multiplicities both equal one. The last
identification would take the zero-dimensional stalk to a one-dimensional one. -/
theorem sLocalThetaPoleBound_printed_mellin_sequence_false :
    ¬ sLocalThetaPoleBound_printed_mellin_sequence :=
  sLocalThetaPoleBound_printed_mellin_sequence_false_aux

/-- Paper: Remark 7.2.1.2, p. 335.
The middle-term surjectivity consequence on each component takes the whole
homogeneous theta space onto all meromorphic sections with the full divisor
bound. Those sections are expressed as meromorphic functions in a component chart. -/
def sLocalMellin_surjective_divisorBounded : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (χ : PontryaginDual Jₛ(F, S))
    (Z : ℂ → ℂ), Meromorphic Z →
    (∀ z : ℂ, let c : Xₛ(F, S) := twistₛ(F, S) ((circleToComplex).comp χ) z
      ((-(sLocalRhoPoleOrder c : ℤ) : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt Z z) →
    ∃ f : ℬₛ(F, S), (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ(F, S) ((circleToComplex).comp χ) z))
      =ᶠ[codiscrete ℂ] Z

/-- The constant function one meets every divisor bound. A test matching it off a
discrete set would agree with it on the right half-plane, where its Z-function is
holomorphic, against the decay in height of `sLocalIdelicZFunction_schwartzOnStrip`. -/
private theorem sLocalMellin_surjective_divisorBounded_false_aux :
    ¬ sLocalMellin_surjective_divisorBounded.{u} := by
  intro h
  let := ulift_rat_numberField.{u}
  let F := ULift.{u} ℚ
  let S : Finset Places(F) := ∅
  obtain ⟨f, hf⟩ := h F S 1 (fun _ ↦ 1) (fun x ↦ analyticAt_const.meromorphicAt) (fun z ↦ by
    classical
    rw [meromorphicOrderAt_const, ite_eq_right_iff.mpr (fun h ↦ absurd h one_ne_zero)]
    exact WithTop.coe_le_coe.mpr (by omega))
  set Zf : ℂ → ℂ := fun z ↦
    sLocalIdelicZFunction f (twistₛ(F, S) ((circleToComplex).comp 1) z) with hZf
  have hs := sLocalIdelicZFunction_schwartzOnStrip f 1 1 3 one_pos (by norm_num) 0
  simp only [iteratedDeriv_zero] at hs
  obtain ⟨-, hdiff, hdec⟩ := hs
  -- On the strip the Z-function is continuous, so it equals one there.
  have hone (s : ℂ) (hs : s.re ∈ Ioo 1 3) : Zf s = 1 := by
    have hc : ContinuousAt Zf s := (hdiff.differentiableAt
      ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds hs)).continuousAt
    have h1 : Tendsto Zf (𝓝[≠] s) (𝓝 1) :=
      tendsto_const_nhds.congr' ((hf.filter_mono (nhdsNE_le_codiscrete s)).mono
        fun z hz ↦ hz.symm)
    exact tendsto_nhds_unique (hc.tendsto.mono_left nhdsWithin_le_nhds) h1
  obtain ⟨C, hC, hev⟩ := hdec (1 / 2) (by norm_num) (by norm_num) 1 le_rfl
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hev
  obtain ⟨N, hN⟩ := hev
  set b : ℝ := max N (C + 1) with hb
  have hb1 : C + 1 ≤ b := le_max_right _ _
  have hbpos : 0 < b := by linarith
  have key := hN b (le_max_left _ _) b (abs_of_pos hbpos) 2 ⟨by norm_num, by norm_num⟩
  change ‖Zf (((2 : ℝ) : ℂ) + (b : ℂ) * Complex.I)‖ ≤ _ at key
  rw [hone _ (by norm_num), norm_one, pow_one, abs_of_pos hbpos, le_div_iff₀ hbpos] at key
  linarith

/-- Paper: Remark 7.2.1.2, p. 335.
For ℚ with only the real place and the trivial component, the constant entire
function one satisfies the divisor bound but violates the vertical decay of
every Schwartz–Bruhat Mellin transform on the line of real part one. -/
theorem sLocalMellin_surjective_divisorBounded_false :
    ¬ sLocalMellin_surjective_divisorBounded :=
  sLocalMellin_surjective_divisorBounded_false_aux

/-- Paper: Remark 7.2.1.3, p. 335.
The full pole bound is identified with the closure of the homogeneous theta
image of tests vanishing to all required orders on coordinate hyperplanes. -/
def sLocalThetaPoleBound_full_eq_polarFree : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (ω : PontryaginDual J₁(F, S))
    (r : (w : {w : InfinitePlace F // w.IsReal}) →
      {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
    (c : (w : {w : InfinitePlace F // w.IsComplex}) →
      {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)}),
    sLocalThetaPoleBound ω sLocalRhoPoleOrder =
      ((sAdelePolarFree S r c).map (Kₛ(F, S, ω)).mkQ).topologicalClosure

/-- Paper: Remark 7.2.1.3, p. 335.
For ℚ with the real place and p, the real Gaussian times the indicator of ℤₚ
has a double pole at the trivial character. The coordinatewise polar-free
image has entire Mellin transform and its closure still has the zero pole bound. -/
theorem sLocalThetaPoleBound_full_eq_polarFree_false :
    ¬ sLocalThetaPoleBound_full_eq_polarFree := by sorry

open Classical in
/-- Paper: Preamble to (7.2.1.12), p. 336.
The coordinate insertions into the S-idèle quotient are closed embeddings. -/
def sLocalCoordinate_closedEmbedding : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)),
    let prod := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
      ((v : S) → v.val.adicCompletion F)
    let arch := ContinuousMulEquiv.piUnits (M := InfinitePlace.Completion (K := F))
    let fin := ContinuousMulEquiv.piUnits (M := fun v : S ↦ v.val.adicCompletion F)
    (∀ w : InfinitePlace F, IsClosedEmbedding (fun x : w.Completionˣ ↦
      (QuotientGroup.mk (prod.symm (arch.symm (Pi.mulSingle w x), 1)) : Jₛ(F, S)))) ∧
    (∀ v : S, IsClosedEmbedding (fun x : (v.val.adicCompletion F)ˣ ↦
      (QuotientGroup.mk (prod.symm (1, fin.symm (Pi.mulSingle v x))) : Jₛ(F, S))))

/-- Every universe contains a number field of degree one, namely a lift of ℚ. -/
private theorem sLocalCoordinate_closedEmbedding_exists_numberField :
    ∃ (F : Type u) (_ : Field F) (_ : NumberField F), Module.finrank ℚ F = 1 := by
  let e : ULift.{u} ℚ ≃+* ℚ := ULift.ringEquiv
  have : CharZero (ULift.{u} ℚ) := RingHom.charZero e.toRingHom
  let l : ULift.{u} ℚ ≃ₗ[ℚ] ℚ := e.toRatAlgEquiv.toLinearEquiv
  have : FiniteDimensional ℚ (ULift.{u} ℚ) := Module.Finite.equiv l.symm
  exact ⟨ULift.{u} ℚ, inferInstance, {}, by rw [l.finrank_eq, Module.finrank_self]⟩

/-- A number field of degree one has a single infinite place. -/
private theorem sLocalCoordinate_closedEmbedding_subsingleton (F : Type*) [Field F]
    [NumberField F] (h : Module.finrank ℚ F = 1) : Subsingleton (InfinitePlace F) := by
  have h₁ := InfinitePlace.card_add_two_mul_card_eq_rank F
  have h₂ := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := F)
  exact Fintype.card_le_one_iff_subsingleton.mp (by omega)

open Classical in
/-- The refutation at a fixed universe: in a degree-one field the units −1 and 1 at the
only infinite place have the same class, since −1 is a global unit. -/
private theorem sLocalCoordinate_closedEmbedding_false_aux
    (h : sLocalCoordinate_closedEmbedding.{u}) : False := by
  obtain ⟨F, _, _, hF⟩ := sLocalCoordinate_closedEmbedding_exists_numberField.{u}
  have key : ∀ (w : InfinitePlace F) (x : w.Completionˣ),
      (((ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F)
        ((v : (∅ : Finset (HeightOneSpectrum (𝓞 F)))) → v.val.adicCompletion F)).symm
        (ContinuousMulEquiv.piUnits.symm (Pi.mulSingle w x), 1) : (SAdeleRing F ∅)ˣ) :
          SAdeleRing F ∅).1 w = x := by
    intro w x
    change ((Pi.mulSingle w x : ∀ w, w.Completionˣ) w : w.Completion) = x
    rw [Pi.mulSingle_eq_same]
  have hsub := sLocalCoordinate_closedEmbedding_subsingleton F hF
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hinj := ((h F ∅).1 w).injective
  have hne : (-1 : w.Completionˣ) ≠ 1 := by
    intro h1
    have h2 := congrArg (fun x : w.Completionˣ ↦ InfinitePlace.Completion.extensionEmbedding w x.val) h1
    norm_num at h2
  apply hne
  apply hinj
  dsimp only
  refine ((sIdeleQuotient_mk_eq_one F ∅ _).2 ⟨-1, ?_⟩).trans
    ((sIdeleQuotient_mk_eq_one F ∅ _).2 ⟨1, ?_⟩).symm
  all_goals
    apply Units.ext
    apply Prod.ext
    · funext v
      obtain rfl := Subsingleton.elim v w
      refine Eq.trans ?_ ((sAdele_diagonal_apply F ∅ _).2.1 v).symm
      rw [key]
      simp
    · funext v
      exact absurd v.2 (Finset.notMem_empty _)

/-- Paper: Preamble to (7.2.1.12), p. 336.
For ℚ with only the real place, the two real units 1 and −1 give the same class. -/
theorem sLocalCoordinate_closedEmbedding_false : ¬ sLocalCoordinate_closedEmbedding :=
  sLocalCoordinate_closedEmbedding_false_aux

/-- Paper: Chart change before Theorem 7.2.1.4, p. 336.
For two unitary base points of the same component, the new base is asserted to be
the pure imaginary norm twist specifying the chart translation. -/
def sLocalChangeOfChart_pureNormBase : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (χ χ' : PontryaginDual Jₛ(F, S)),
    (∀ g : J₁(F, S), χ g.val = χ' g.val) →
    ∃! t : ℝ, (circleToComplex).comp χ' = twistₛ(F, S) 1 ((t : ℂ) * Complex.I) ∧
      ∀ s : ℂ, twistₛ(F, S) ((circleToComplex).comp χ') (s - (t : ℂ) * Complex.I) =
        twistₛ(F, S) ((circleToComplex).comp χ) s

/-- Paper: Chart change before Theorem 7.2.1.4, p. 336.
For ℚ with the real place and 5, take the quadratic character on the 5-adic units,
trivial on 5 and on the real factor. It kills the S-units. Its twist by the norm
to the power i still equals −1 on the 5-adic unit 2, where every pure norm twist is one. -/
theorem sLocalChangeOfChart_pureNormBase_false : ¬ sLocalChangeOfChart_pureNormBase := by sorry

open Classical in
/-- Paper: Equation (7.2.1.13), p. 336. The unscaled formula with a specified Laurent exponent. -/
def sLocalUnscaledLeadingIdentity (exponent : ℕ → ℤ) : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (c : Xₛ(F, S)),
    c ∈ poleLocus(F, S) → ∀ f : ℬₛ(F, S),
    let arch := sLocalArchPolePlaces c
    let fin := sLocalFinitePolePlaces c
    let archEuler (w : InfinitePlace F) (z : ℂ) :=
      infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (twistₛ(F, S) c z))
    let finEuler (v : S) (z : ℂ) :=
      finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (twistₛ(F, S) c z))
    sLocalZLaurentCoeff f c (exponent (sLocalRhoPoleOrder c)) =
      (∏ w ∈ arch, complexResidue (archEuler w) 0) *
      (∏ w ∈ Finset.univ \ arch, archEuler w 0) *
      (∏ v ∈ fin, complexResidue (finEuler v) 0) *
      (∏ v ∈ Finset.univ \ fin, finEuler v 0) *
      sLocalNormalizedEigendistribution (dualₛ(F, S) c) (sAdeleSchwartzFourier f)

/-- Paper: Equation (7.2.1.13), p. 336.
Reading the subscript according to Definition 7.1.2.1 gives a nonnegative exponent. -/
def sLocalPrincipalPartCoeff_leading_literal : Prop :=
  sLocalUnscaledLeadingIdentity.{u} (fun m ↦ (m : ℤ))

/-- Paper: Equation (7.2.1.13), p. 336.
For ℚ with the real place take the trivial center and an even nonzero nonnegative
bump on 2 < |x| < 3. Its first Mellin derivative is positive. The right side is
zero since the leading polar functional at the trivial character is a multiple
of the test value at zero. -/
theorem sLocalPrincipalPartCoeff_leading_literal_false :
    ¬ sLocalPrincipalPartCoeff_leading_literal := by sorry

/-- Paper: Equation (7.2.1.13), p. 336.
With the leading-pole interpretation specified in (7.2.1.19), the unscaled
product still omits the factor from Fourier and Gaussian normalization. -/
def sLocalPrincipalPartCoeff_leading_unscaled : Prop :=
  sLocalUnscaledLeadingIdentity.{u} (fun m ↦ -(m : ℤ))

/-- Paper: Equation (7.2.1.13), p. 336.
Take ℚ(i) with the complex place and the place over 2, the trivial character, and
the standard complex Gaussian times the local integer indicator. The leading
coefficient is nonzero. The finite unit mass and epsilon at the center are each
1/2, so the printed right-hand side is four times the left-hand side. -/
theorem sLocalPrincipalPartCoeff_leading_unscaled_false :
    ¬ sLocalPrincipalPartCoeff_leading_unscaled := by sorry

/-- Paper: Equation (7.2.1.14), p. 337.
The test coefficient on the left is read with Definition 7.1.2.1. The sentence
following the display explicitly specifies exponent −m+j for the rho coefficient. -/
def sLocalPrincipalPartCoeff_lower_literal : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (c : Xₛ(F, S))
    (f : ℬₛ(F, S)) (k : ℕ), k < sLocalRhoPoleOrder c →
    let m := sLocalRhoPoleOrder c
    sLocalNonnegativeLaurentCoeff c k f =
      ∑ j ∈ Finset.range (m - k + 1),
        complexResidue (fun z : ℂ ↦ sLocalRhoFactor (twistₛ(F, S) c z) *
          z ^ ((m : ℤ) - (j : ℤ) - 1)) 0 *
        (iteratedDeriv (m - k - j) (fun z ↦ sLocalIdelicZFunction
          (sAdeleSchwartzFourier f) (dualₛ(F, S) (twistₛ(F, S) c z))) 0 /
          ((m - k - j).factorial : ℂ))

/-- Paper: Equation (7.2.1.14), p. 337.
Over ℚ with the real place and p, at the trivial center m = 2. Take index one,
a nonzero nonnegative even bump supported on 2 < |x| < 3 and the finite unit
indicator. Its zeta function is entire. The convolution on the right gives its
zero residue, while its first Taylor coefficient on the left is positive. -/
theorem sLocalPrincipalPartCoeff_lower_literal_false :
    ¬ sLocalPrincipalPartCoeff_lower_literal := by sorry

/-- Paper: Equation (7.2.1.17), p. 337.
The printed functional equation inserts an additional epsilon factor in the
ratio of the original and Fourier Euler products. The two basic products use
the same normalization, so their common scalar cancels. -/
def sLocalFunctionalEquation_extra_epsilon : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (χ : PontryaginDual Jₛ(F, S))
    (f : ℬₛ(F, S)),
    (fun z : ℂ ↦ sLocalIdelicZFunction f (twistₛ(F, S) ((circleToComplex).comp χ) z))
      =ᶠ[codiscrete ℂ] fun z ↦
        let c : Xₛ(F, S) := twistₛ(F, S) ((circleToComplex).comp χ) z
        sLocalEpsilonFactor c * (sLocalHeckeL c / sLocalFourierEulerProduct c) *
          sLocalIdelicZFunction (sAdeleSchwartzFourier f) (dualₛ(F, S) c)

/-- Paper: Equation (7.2.1.17), p. 337.
For ℚ(i) with the complex place and the place over 2, take the trivial unitary
base and its standard Gaussian tensor. At exponent 1/4 the zeta integral is
nonzero and the epsilon factor is not one. The ratio already contains epsilon,
so the proposed identity fails on a neighborhood of that exponent. -/
theorem sLocalFunctionalEquation_extra_epsilon_false :
    ¬ sLocalFunctionalEquation_extra_epsilon := by sorry

open Classical in
/-- Paper: Proposition 7.2.2.1, p. 339.
The four printed conditions include exact global zero orders, with the
one-order exception at the trivial character on the selected divisor. -/
def sLocalPrincipalValue_tfae_exact_order : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S S₀ : Finset Places(F)) (h₀ : S₀ ⊆ S)
    (_hn : S₀.Nonempty) (_hPic : Subsingleton (CommRing.Pic ((S : Set Places(F)).integer F)))
    (χ : PontryaginDual C𝔽(F)) (hχ : globalUnitary(F, χ) ∈ unramifiedOutside F S₀) (f : ℬₛ(F, S)),
    let hS : globalUnitary(F, χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(F, χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(F, χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(F, S, ωₛ)).mkQ f
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ(F, S)), onComponent(F, S, c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        ∀ k : ℕ, sLocalRhoPoleOrder c - sLocalFinitePoleMultiplicity S₀ c < k →
          k ≤ sLocalRhoPoleOrder c → sLocalNonnegativeLaurentCoeff c k f = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(F, S, χ, hS) s) →
        let n := sLocalFinitePoleMultiplicity S₀ (localChart(F, S, χ, hS) s)
        meromorphicOrderAt Z s = ((if ideleClassNormTwist χ s = 1 then n - 1 else n : ℕ) : WithTop ℤ)),
      x ∈ (sLocalHomogeneousThetaPrincipalValue h₀ ωₛ).range,
      (∃ g : ℬ𝔽(F), (K𝔽(F, ω)).mkQ (adelePrincipalValue F S₀ g) = π x)
    ]

/-- The trivial unitary character is unramified outside every finite set of places. -/
private theorem sLocalPrincipalValue_tfae_exact_order_one_mem {F : Type*} [Field F]
    [NumberField F] (S : Finset Places(F)) :
    globalUnitary(F, (1 : PontryaginDual C𝔽(F))) ∈ unramifiedOutside F S := by
  rw [mem_unramifiedOutside_iff]
  intro v _ u
  rfl

/-- The local chart of the trivial unitary character at exponent zero is the trivial
quasi-character. -/
private theorem sLocalPrincipalValue_tfae_exact_order_chart {F : Type*} [Field F]
    [NumberField F] (S : Finset Places(F))
    (hS : globalUnitary(F, (1 : PontryaginDual C𝔽(F))) ∈ unramifiedOutside F S) :
    localChart(F, S, (1 : PontryaginDual C𝔽(F)), hS) 0 = 1 := by
  ext g
  induction g using QuotientGroup.induction_on with | H x => ?_
  change sIdeleRestriction F S _ (QuotientGroup.mk x) * _ ^ (0 : ℂ) = 1
  rw [Complex.cpow_zero, mul_one, sIdeleRestriction_mk]
  rfl

/-- The global Z-function of a test vanishing pointwise vanishes identically along the
trivial chart, so its order at zero is ⊤. -/
private theorem sLocalPrincipalValue_tfae_exact_order_zero {F : Type*} [Field F]
    [NumberField F] (f : ℬ𝔽(F)) (hf : ∀ x, f x = 0) :
    meromorphicOrderAt (fun s ↦ globalIdelicZFunction f
      (ideleClassNormTwist (1 : PontryaginDual C𝔽(F)) s)) 0 = ⊤ := by
  have hM := (globalIdelicZFunction_meromorphic f 1).meromorphicOn
  refine hM.meromorphicOrderAt_eq_top_of_isPreconnected (x := 2) isPreconnected_univ
    (mem_univ _) (mem_univ _) ?_
  rw [meromorphicOrderAt_eq_top_iff]
  have hopen : {s : ℂ | 1 < s.re} ∈ 𝓝 (2 : ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [nhdsWithin_le_nhds hopen] with s hs
  have hmem : ideleClassNormTwist (1 : PontryaginDual C𝔽(F)) s ∈
      (relativeRightHalfPlane (ideleClassNorm F) (isProperMap_ideleClassNorm F)
        (ideleClassNorm_ne_one (F := F)) 1 : Set (QuasiCharacter C𝔽(F))) := by
    change 1 < quasiCharacterAbscissa (ideleClassNorm F) (isProperMap_ideleClassNorm F)
      (ideleClassNorm_ne_one (F := F)) _
    rw [quasiCharacterAbscissa_ideleClassNormTwist]
    exact hs
  rw [globalIdelicZFunction_eq_integral f hmem]
  simp [globalIdelicZetaIntegral, hf]

/-- The refutation at a fixed universe, with the zero test and the trivial character. -/
private theorem sLocalPrincipalValue_tfae_exact_order_false_aux
    (h : sLocalPrincipalValue_tfae_exact_order.{u}) : False := by
  classical
  obtain ⟨F, _, _, -⟩ := sLocalCoordinate_closedEmbedding_exists_numberField.{u}
  obtain ⟨T, hT⟩ := eventually_trivial_sIdealClassGroup F
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v₀ : Places(F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have h₀ : ({v₀} : Finset Places(F)) ⊆ insert v₀ T := by simp
  have H := h F (insert v₀ T) {v₀} h₀ (Finset.singleton_nonempty v₀)
    (hT _ (Finset.subset_insert _ _)) 1 (sLocalPrincipalValue_tfae_exact_order_one_mem _) 0
  have hiff := H _ (List.mem_cons_self ..) _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h2 := hiff.mp (fun _ _ _ _ _ _ ↦ map_zero _) 0
  have hpos : 0 < sLocalFinitePoleMultiplicity {v₀} (1 : Xₛ(F, insert v₀ T)) := by
    rw [sLocalFinitePoleMultiplicity_one _ h₀]
    exact Finset.card_pos.mpr (Finset.singleton_nonempty v₀)
  have h3 := h2 (by
    convert hpos using 2
    exact sLocalPrincipalValue_tfae_exact_order_chart _ _)
  have h4 := sLocalPrincipalValue_tfae_exact_order_zero
    (sAdeleSchwartzToGlobal F (insert v₀ T) 0) (fun x ↦ by rw [map_zero]; rfl)
  exact WithTop.top_ne_natCast _ (h4.symm.trans h3)

/-- Paper: Proposition 7.2.2.1, p. 339.
Take ℚ, the real place and p, select p, and take the trivial character and the
zero test. Its local coefficients vanish and both principal-value preimages
can be zero. Its global order at the trivial character is ⊤, whereas the
printed condition requires order zero. -/
theorem sLocalPrincipalValue_tfae_exact_order_false :
    ¬ sLocalPrincipalValue_tfae_exact_order :=
  sLocalPrincipalValue_tfae_exact_order_false_aux

open Classical in
/-- Paper: Corollary 7.2.2.2, p. 340.
The four printed conditions on the two-evaluation kernel require exact global
zero orders and shift the local coefficient interval at the trivial character. -/
def sLocalPolarPrincipalValue_tfae_exact_order : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S S₀ : Finset Places(F)) (h₀ : S₀ ⊆ S)
    (_hn : S₀.Nonempty) (_hPic : Subsingleton (CommRing.Pic ((S : Set Places(F)).integer F)))
    (χ : PontryaginDual C𝔽(F)) (hχ : globalUnitary(F, χ) ∈ unramifiedOutside F S₀)
    (f : sAdelePolarSubspace F S),
    let hS : globalUnitary(F, χ) ∈ unramifiedOutside F S := outsideS(h₀, hχ)
    let ω := globalNormOne(F, χ)
    let hω : NormOneCharacterUnramifiedOutside ω S := ⟨⟨globalUnitary(F, χ), hS⟩, fun _ ↦ rfl⟩
    let ωₛ := sLocalNormOneCharacter S ω hω
    let x := (Kₛ(F, S, ωₛ)).mkQ f.val
    let π := sLocalHomogeneousThetaToGlobal hω
    let Z := fun s ↦ globalIdelicZFunction (sAdeleSchwartzToGlobal F S f.val) (ideleClassNormTwist χ s)
    List.TFAE [
      (∀ (c : Xₛ(F, S)), onComponent(F, S, c, ωₛ) → 0 < sLocalFinitePoleMultiplicity S₀ c →
        let m := sLocalRhoPoleOrder c
        let n := sLocalFinitePoleMultiplicity S₀ c
        ∀ k : ℕ, (if c = 1 then m - n ≤ k ∧ k ≤ m - 1 else m - n < k ∧ k ≤ m) →
          sLocalNonnegativeLaurentCoeff c k f.val = 0),
      (∀ s : ℂ, 0 < sLocalFinitePoleMultiplicity S₀ (localChart(F, S, χ, hS) s) →
        meromorphicOrderAt Z s = (sLocalFinitePoleMultiplicity S₀ (localChart(F, S, χ, hS) s) : WithTop ℤ)),
      (∃ g : sAdelePolarSubspace F S, (Kₛ(F, S, ωₛ)).mkQ (sAdelePrincipalValue F h₀ g.val) = x),
      (∃ g : adelePolarSubspace F, (K𝔽(F, ω)).mkQ (adelePrincipalValue F S₀ g.val) = π x)
    ]

/-- The refutation at a fixed universe, with the zero polar test and the trivial
character. -/
private theorem sLocalPolarPrincipalValue_tfae_exact_order_false_aux
    (h : sLocalPolarPrincipalValue_tfae_exact_order.{u}) : False := by
  classical
  obtain ⟨F, _, _, -⟩ := sLocalCoordinate_closedEmbedding_exists_numberField.{u}
  obtain ⟨T, hT⟩ := eventually_trivial_sIdealClassGroup F
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v₀ : Places(F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have h₀ : ({v₀} : Finset Places(F)) ⊆ insert v₀ T := by simp
  have H := h F (insert v₀ T) {v₀} h₀ (Finset.singleton_nonempty v₀)
    (hT _ (Finset.subset_insert _ _)) 1 (sLocalPrincipalValue_tfae_exact_order_one_mem _) 0
  have hiff := H _ (List.mem_cons_self ..) _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  have h2 := hiff.mp (fun _ _ _ _ _ ↦ map_zero _) 0
  have hpos : 0 < sLocalFinitePoleMultiplicity {v₀} (1 : Xₛ(F, insert v₀ T)) := by
    rw [sLocalFinitePoleMultiplicity_one _ h₀]
    exact Finset.card_pos.mpr (Finset.singleton_nonempty v₀)
  have h3 := h2 (by
    convert hpos using 2
    exact sLocalPrincipalValue_tfae_exact_order_chart _ _)
  have h4 := sLocalPrincipalValue_tfae_exact_order_zero
    (sAdeleSchwartzToGlobal F (insert v₀ T) 0) (fun x ↦ by rw [map_zero]; rfl)
  exact WithTop.top_ne_natCast _ (h4.symm.trans h3)

/-- Paper: Corollary 7.2.2.2, p. 340.
Take ℚ, the real place and p, select p, and take the trivial character and the
zero test. Both evaluations vanish, all local coefficients vanish, and both
principal-value preimages can be zero. The global order is ⊤ at the trivial
character, while the asserted order is one. -/
theorem sLocalPolarPrincipalValue_tfae_exact_order_false :
    ¬ sLocalPolarPrincipalValue_tfae_exact_order :=
  sLocalPolarPrincipalValue_tfae_exact_order_false_aux

open Metric in
/-- The exterior of a closed disc is preconnected. -/
private theorem sLocalPrincipalPartCoeff_any_contour_exterior (r : ℝ) (hr : 0 ≤ r) : IsPreconnected {z : ℂ | r < ‖z‖} := by
  have hc : Continuous (fun p : ℝ × ℝ ↦ circleMap 0 p.1 p.2) := by
    unfold circleMap; fun_prop
  have him : (fun p : ℝ × ℝ ↦ circleMap 0 p.1 p.2) '' (Ioi r ×ˢ univ) = {z : ℂ | r < ‖z‖} := by
    ext z
    constructor
    · rintro ⟨⟨ρ, θ⟩, ⟨hρ, -⟩, rfl⟩
      simp only [mem_ofPred_eq, norm_circleMap_zero]
      rw [abs_of_pos (hr.trans_lt hρ)]; exact hρ
    · intro hz
      refine ⟨⟨‖z‖, Complex.arg z⟩, ⟨hz, mem_univ _⟩, ?_⟩
      simp only [circleMap, zero_add]
      exact Complex.norm_mul_exp_arg_mul_I z
  rw [← him]
  exact (isPreconnected_Ioi.prod isPreconnected_univ).image _ hc.continuousOn

open Metric in
/-- A bounded connected open set whose frontier is a circle is the open disc. -/
private theorem sLocalPrincipalPartCoeff_any_contour_unique (r : ℝ) (hr : 0 < r) (U : Set ℂ) (hU : IsOpen U) (hc : IsConnected U)
    (hb : Bornology.IsBounded U) (hf : frontier U = sphere 0 r) : U = ball 0 r := by
  have hdisj : U ∩ sphere 0 r = ∅ := hf ▸ hU.inter_frontier_eq
  have hcl : closure U = U ∪ sphere 0 r := by
    rw [← hf, ← closure_sdiff_interior, hU.interior_eq, union_sdiff_self, union_eq_right.mpr subset_closure]
  have hsub : ∀ V : Set ℂ, IsPreconnected V → V ∩ sphere 0 r = ∅ → (V ∩ U).Nonempty → V ⊆ U := by
    intro V hV hVs hne
    refine hV.subset_of_closure_inter_subset hU hne ?_
    rw [hcl]
    rintro z ⟨hz | hz, hzV⟩
    · exact hz
    · exact absurd (show z ∈ V ∩ sphere 0 r from ⟨hzV, hz⟩) (by rw [hVs]; exact notMem_empty z)
  have hext : ¬ ({z : ℂ | r < ‖z‖} ∩ U).Nonempty := by
    intro hne
    have h1 := hsub _ (sLocalPrincipalPartCoeff_any_contour_exterior r hr.le) (by
      ext z; simp only [mem_inter_iff, mem_ofPred_eq, mem_sphere_zero_iff_norm, mem_empty_iff_false,
        iff_false, not_and]; intro h h'; linarith) hne
    have : Bornology.IsBounded (closedBall (0 : ℂ) r ∪ {z : ℂ | r < ‖z‖}) :=
      isBounded_closedBall.union (hb.subset h1)
    have huniv : closedBall (0 : ℂ) r ∪ {z : ℂ | r < ‖z‖} = univ := by
      ext z; simp only [mem_union, mem_closedBall_zero_iff, mem_ofPred_eq, mem_univ, iff_true]
      exact le_or_gt _ _
    rw [huniv] at this
    exact NormedSpace.unbounded_univ ℝ ℂ this
  have hUb : U ⊆ ball 0 r := by
    intro z hz
    rw [mem_ball_zero_iff]
    rcases lt_trichotomy ‖z‖ r with h | h | h
    · exact h
    · exact absurd (show z ∈ U ∩ sphere 0 r from ⟨hz, mem_sphere_zero_iff_norm.mpr h⟩)
        (by rw [hdisj]; exact notMem_empty z)
    · exact absurd ⟨z, h, hz⟩ hext
  obtain ⟨z₀, hz₀⟩ := hc.nonempty
  refine hUb.antisymm (hsub _ (convex_ball 0 r).isPreconnected ?_ ⟨z₀, hUb hz₀, hz₀⟩)
  ext z; simp only [mem_inter_iff, mem_ball_zero_iff, mem_sphere_zero_iff_norm, mem_empty_iff_false,
    iff_false, not_and]; intro h h'; linarith

open Metric in
/-- Reversing a path negates the line integral. -/
private theorem sLocalPrincipalPartCoeff_any_contour_reverse (γ : ℝ → ℂ) (G : ℂ → ℂ) :
    (∫ t in (0 : ℝ)..1, G (γ (1 - t)) * deriv (fun s ↦ γ (1 - s)) t) =
      -∫ t in (0 : ℝ)..1, G (γ t) * deriv γ t := by
  have h1 : (fun t ↦ G (γ (1 - t)) * deriv (fun s ↦ γ (1 - s)) t) =
      fun t ↦ -(G (γ (1 - t)) * deriv γ (1 - t)) := by
    funext t; rw [deriv_comp_const_sub]; ring
  rw [h1, intervalIntegral.integral_neg, intervalIntegral.integral_comp_sub_left
    (fun t ↦ G (γ t) * deriv γ t) 1]
  norm_num

open Metric in
/-- The unit-time circle traces the whole circle on `[0, 1]`. -/
private theorem sLocalPrincipalPartCoeff_any_contour_image (r : ℝ) (hr : 0 < r) :
    (fun t : ℝ ↦ circleMap 0 r (2 * Real.pi * t)) '' Icc 0 1 = sphere 0 r := by
  apply Subset.antisymm
  · rintro _ ⟨t, -, rfl⟩
    simp [abs_of_pos hr]
  · intro z hz
    rw [← abs_of_pos hr, ← image_circleMap_Ioc] at hz
    obtain ⟨θ, hθ, rfl⟩ := hz
    refine ⟨θ / (2 * Real.pi), ⟨div_nonneg hθ.1.le (by positivity), ?_⟩, ?_⟩
    · rw [div_le_one (by positivity)]; exact hθ.2
    · simp only; congr 1; field_simp


open Metric in
/-- A germ of order at least `-1` whose nonnegative Laurent coefficients vanish is `a / z`. -/
private theorem sLocalPrincipalPartCoeff_any_contour_simplePole {g : ℂ → ℂ}
    (hg : MeromorphicAt g 0) (hord : (-(meromorphicOrderAt g 0).untop₀).toNat ≤ 1)
    (hc : ∀ k : ℕ, complexResidue (fun z ↦ g z / z ^ ((k : ℤ) + 1)) 0 = 0) :
    ∃ a : ℂ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = a * z⁻¹ := by
  obtain ⟨h, hh, hgh⟩ : ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z⁻¹ * h z := by
    by_cases ho : meromorphicOrderAt g 0 = ⊤
    · refine ⟨0, analyticAt_const, ?_⟩
      filter_upwards [meromorphicOrderAt_eq_top_iff.mp ho] with z hz
      simp [hz]
    · obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp ho
      rw [← hm, WithTop.untop₀_coe] at hord
      obtain ⟨φ, hφ, -, hgφ⟩ := (meromorphicOrderAt_eq_int_iff hg).mp hm.symm
      refine ⟨fun z ↦ z ^ (m + 1).toNat * φ z, (analyticAt_id.pow _).mul hφ, ?_⟩
      filter_upwards [hgφ, self_mem_nhdsWithin] with z hz hz0
      have hz0' : z ≠ 0 := hz0
      rw [hz, sub_zero, smul_eq_mul, ← mul_assoc]
      congr 1
      rw [← zpow_natCast, Int.toNat_of_nonneg (by omega), ← zpow_neg_one, ← zpow_add₀ hz0']
      ring_nf
  obtain ⟨R₀, hR₀, hR₀h⟩ := hh.exists_ball_analyticOnNhd
  obtain ⟨ε, hε, hεg⟩ := Metric.mem_nhdsWithin_iff.mp hgh
  let R : ℝ≥0 := ⟨min R₀ ε / 2, by positivity⟩
  have hR : (0 : ℝ≥0) < R := by
    change (0 : ℝ) < min R₀ ε / 2; positivity
  have hRR₀ : (R : ℝ) < R₀ := by
    change min R₀ ε / 2 < R₀; linarith [min_le_left R₀ ε, lt_min hR₀ hε]
  have hRε : (R : ℝ) < ε := by
    change min R₀ ε / 2 < ε; linarith [min_le_right R₀ ε, lt_min hR₀ hε]
  have hhd : DifferentiableOn ℂ h (closedBall 0 R) := fun z hz ↦
    (hR₀h z (closedBall_subset_ball hRR₀ hz)).differentiableAt.differentiableWithinAt
  have hcoef (k : ℕ) : cauchyPowerSeries h 0 R (k + 1) (fun _ ↦ 1) = 0 := by
    refine Eq.trans ?_ (hc k)
    symm
    refine (tendsto_const_nhds.congr' ?_).limUnder_eq
    filter_upwards [Ioo_mem_nhdsGT hR] with r hr
    have key := sLocalZLaurentCoeff_hasLaurentSeries_circleIntegral
      (g := fun z ↦ z⁻¹ * h z) (h := h) (N := 1) hR hhd
      (fun z _ ↦ by simp) (k : ℤ) hr
    rw [if_pos (by omega), show ((k : ℤ) + ((1 : ℕ) : ℤ)).toNat = k + 1 by omega] at key
    have e : circleIntegral (fun z ↦ g z / z ^ ((k : ℤ) + 1)) 0 r =
        circleIntegral (fun z ↦ (z⁻¹ * h z) / z ^ ((k : ℤ) + 1)) 0 r := by
      refine circleIntegral.integral_congr hr.1.le fun z hz ↦ ?_
      have hzr : ‖z‖ = r := mem_sphere_zero_iff_norm.mp hz
      have hm : z ∈ ball (0 : ℂ) ε ∩ {0}ᶜ := by
        refine ⟨mem_ball_zero_iff.mpr (lt_of_eq_of_lt hzr (hr.2.trans hRε)), ?_⟩
        intro h0
        rw [mem_singleton_iff.mp h0, norm_zero] at hzr
        exact hr.1.ne hzr
      change g z / _ = _
      rw [show g z = z⁻¹ * h z from hεg hm]
    rw [e]
    simpa using key.symm
  have hp := hhd.hasFPowerSeriesOnBall hR
  have hconst : ∀ z ∈ ball (0 : ℂ) R, h z = h 0 := by
    intro z hz
    have hz' : z ∈ Metric.eball (0 : ℂ) R := by
      rw [Metric.mem_eball, edist_zero_right]
      exact_mod_cast (mem_ball_zero_iff.mp hz)
    have hs := hp.hasSum hz'
    have hterm (n : ℕ) : cauchyPowerSeries h 0 R n (fun _ ↦ z) =
        z ^ n * cauchyPowerSeries h 0 R n (fun _ ↦ 1) := by
      have := (cauchyPowerSeries h 0 R n).map_smul_univ (fun _ ↦ z) (fun _ ↦ 1)
      simp only [smul_eq_mul, mul_one, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at this
      exact this
    simp only [zero_add, hterm] at hs
    have h1 : HasSum (fun n : ℕ ↦ z ^ n * cauchyPowerSeries h 0 R n (fun _ ↦ 1))
        (z ^ 0 * cauchyPowerSeries h 0 R 0 (fun _ ↦ 1)) := by
      refine hasSum_single 0 fun n hn ↦ ?_
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
      rw [hcoef k, mul_zero]
    rw [hs.unique h1, pow_zero, one_mul, hp.coeff_zero]
  refine ⟨h 0, ?_⟩
  filter_upwards [hgh, inter_mem_nhdsWithin _ (ball_mem_nhds (0 : ℂ) hR)] with z hz hzb
  rw [hz, hconst z hzb.2, mul_comm]

open Metric in
/-- The unit circle run once in unit time is Lipschitz. -/
private theorem sLocalPrincipalPartCoeff_any_contour_lipschitz : ∃ K : ℝ≥0, LipschitzWith K (fun t : ℝ ↦ circleMap 0 1 (2 * Real.pi * t)) := by
  refine ⟨Real.nnabs 1 * ⟨2 * Real.pi, by positivity⟩, (lipschitzWith_circleMap 0 1).comp ?_⟩
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [Real.dist_eq, Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)]
  rfl

open Metric in
/-- The reflection `t ↦ 1 - t` is an isometry. -/
private theorem sLocalPrincipalPartCoeff_any_contour_lipschitz_rev : LipschitzWith 1 (fun t : ℝ ↦ 1 - t) :=
  LipschitzWith.of_dist_le_mul fun x y ↦ by
    simp only [Real.dist_eq, NNReal.coe_one, one_mul]
    rw [abs_sub_comm]; ring_nf; rfl

/-- Over ℚ with no finite places, the standard Gaussian has a nonzero Z-function at `1/2`
on the trivial component. -/
private theorem sLocalPrincipalPartCoeff_any_contour_gaussian [NumberField (ULift.{u} ℚ)] :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing (ULift.{u} ℚ) ∅)),
      sLocalIdelicZFunction f (quasiCharacterNormTwist (G := SIdeleQuotient (ULift.{u} ℚ) ∅)
        (sIdeleQuotientNorm (ULift.{u} ℚ) ∅) (isProperMap_sIdeleQuotientNorm _ _).continuous
        ((circleToComplex).comp (1 : PontryaginDual (SIdeleQuotient (ULift.{u} ℚ) ∅)))
        (1 / 2)) ≠ 0 := by
  let F := ULift.{u} ℚ
  let S : Finset (HeightOneSpectrum (𝓞 F)) := ∅
  let tw := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
  let χ : PontryaginDual (SIdeleQuotient F S) := 1
  let s₀ : ℂ := 1 / 2
  let c := tw ((circleToComplex).comp χ) s₀
  let χArch : (w : InfinitePlace F) → PontryaginDual w.Completionˣ := fun _ ↦ 1
  have hχ : ∀ w, (circleToComplex).comp (χArch w) =
      sLocalInfiniteRestriction w ((circleToComplex).comp χ) := fun w ↦ by
    ext g; rfl
  obtain ⟨f, hf⟩ := sLocalPrincipalPartCoeff_eigendistribution_tensor S
    (fun w ↦ infiniteStandardGaussian w (χArch w))
    (fun v ↦ finiteStandardGaussian v.val (sLocalFiniteRestriction v c))
  have hE := sLocalNormalizedEigendistribution_gaussian χ s₀ χArch hχ f hf
  have hspec := (existsUnique_sLocalNormalizedEigendistribution c).exists.choose_spec f
  have hN : sLocalNormalizedZFunction f c = 1 := by
    rw [← hspec]
    change _ * sLocalNormalizedEigendistribution c f = 1
    rw [hE]
    simp [S]
  have hpos : s₀ ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
    show (0 : ℝ) < (1 / 2 : ℂ).re
    norm_num
  have hdiv := sLocalNormalizedZFunction_eq_div f χ hpos
  have hI : sLocalIdelicZetaIntegral f c ≠ 0 := by
    intro h0
    change sLocalNormalizedZFunction f c = _ at hdiv
    rw [hdiv, h0, zero_div] at hN
    exact zero_ne_one hN
  have hZ : sLocalIdelicZFunction f c = sLocalIdelicZetaIntegral f c :=
    sLocalIdelicZFunction_eq_integral f ⟨χ, s₀, hpos, rfl⟩
  exact ⟨f, fun h0 ↦ hI (hZ.symm.trans h0)⟩

/-- Over ℚ with no finite places, run the unit circle around the pole of the trivial
character in both directions. Every coefficient is then its own negative, so all
nonnegative coefficients vanish. With a pole of order at most one, the Z-function is
`a / z` near the pole, translation by an idele of norm other than one forces `a = 0`,
and the identity theorem then contradicts the Gaussian. -/
private theorem sLocalPrincipalPartCoeff_any_contour_false_aux :
    ¬ sLocalPrincipalPartCoeff_any_contour.{u} := by
  intro h
  let := NumberField.of_ringEquiv ℚ (ULift.{u} ℚ) (ULift.ringEquiv.{0, u} (R := ℚ)).symm
  let F := ULift.{u} ℚ
  let S : Finset (HeightOneSpectrum (𝓞 F)) := ∅
  let tw := quasiCharacterNormTwist (G := SIdeleQuotient F S) (sIdeleQuotientNorm F S)
    (isProperMap_sIdeleQuotientNorm F S).continuous
  let χ : PontryaginDual (SIdeleQuotient F S) := 1
  let c₁ : QuasiCharacter (SIdeleQuotient F S) := (circleToComplex).comp χ
  have hone : c₁ = 1 := by ext g; rfl
  -- the pole order of the trivial character is one
  have hcard : Fintype.card (InfinitePlace F) = 1 := by
    have h1 : Module.finrank ℚ F = 1 := by
      rw [((ULift.ringEquiv.{0, u} (R := ℚ)).toRatAlgEquiv.toLinearEquiv).finrank_eq,
        Module.finrank_self]
    have := sLocalCoordinate_closedEmbedding_subsingleton F h1
    exact le_antisymm (Fintype.card_le_one_iff_subsingleton.mpr this) Fintype.card_pos
  have hpole : 0 < sLocalRhoPoleOrder c₁ := by
    rw [hone, sLocalRhoPoleOrder_eq_card_polePlaces, sLocalPolePlaces_one.1, Finset.card_univ]
    exact Nat.add_pos_left Fintype.card_pos _
  have hle : sLocalRhoPoleOrder c₁ ≤ 1 := by
    rw [hone, sLocalRhoPoleOrder_eq_card_polePlaces, sLocalPolePlaces_one.1, Finset.card_univ,
      hcard]
    have : (sLocalFinitePolePlaces (1 : QuasiCharacter (SIdeleQuotient F S))).card ≤ 0 :=
      (Finset.card_le_univ _).trans (by simp [S])
    omega
  -- the unit circle in both directions
  let γ : ℝ → ℂ := fun t ↦ circleMap 0 1 (2 * Real.pi * t)
  let γ' : ℝ → ℂ := fun t ↦ γ (1 - t)
  obtain ⟨K, hK⟩ := sLocalPrincipalPartCoeff_any_contour_lipschitz
  have hγc : γ 0 = γ 1 := by
    simp only [γ, circleMap, mul_zero, mul_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      zero_add]
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.exp_two_pi_mul_I]
    simp
  have himg : γ '' Icc 0 1 = Metric.sphere 0 1 :=
    sLocalPrincipalPartCoeff_any_contour_image 1 one_pos
  have himg' : γ' '' Icc 0 1 = Metric.sphere 0 1 := by
    rw [← himg]
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨1 - t, ⟨by linarith [ht.2], by linarith [ht.1]⟩, by simp [γ']⟩
  have hfr : frontier (Metric.ball (0 : ℂ) 1) = Metric.sphere 0 1 := frontier_ball 0 one_ne_zero
  have hconn : IsConnected (Metric.ball (0 : ℂ) 1) :=
    ⟨Metric.nonempty_ball.mpr one_pos, (convex_ball 0 1).isPreconnected⟩
  have huniq (U : Set ℂ) (hU : IsOpen U ∧ IsConnected U ∧ Bornology.IsBounded U ∧
      frontier U = Metric.sphere 0 1) : U = Metric.ball 0 1 :=
    sLocalPrincipalPartCoeff_any_contour_unique 1 one_pos U hU.1 hU.2.1 hU.2.2.1 hU.2.2.2
  have hzero (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (k : ℕ) :
      sLocalZLaurentCoeff f c₁ k = 0 := by
    have e1 := (h F S c₁ hpole k f γ ⟨K, hK.lipschitzOnWith⟩ hγc (Metric.ball 0 1)
      ⟨Metric.isOpen_ball, hconn, Metric.isBounded_ball, hfr.trans himg.symm⟩
      (fun U hU ↦ huniq U ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.trans himg⟩)
      (Metric.mem_ball_self one_pos)).2
    have e2 := (h F S c₁ hpole k f γ' ⟨K * 1, (hK.comp
      sLocalPrincipalPartCoeff_any_contour_lipschitz_rev).lipschitzOnWith⟩
      (show γ (1 - 0) = γ (1 - 1) by rw [sub_zero, sub_self]; exact hγc.symm) (Metric.ball 0 1)
      ⟨Metric.isOpen_ball, hconn, Metric.isBounded_ball, hfr.trans himg'.symm⟩
      (fun U hU ↦ huniq U ⟨hU.1, hU.2.1, hU.2.2.1, hU.2.2.2.trans himg'⟩)
      (Metric.mem_ball_self one_pos)).2
    have e3 : (∫ t in (0 : ℝ)..1, γ' t ^ ((k : ℤ) - 1) *
        sLocalIdelicZFunction f (tw c₁ (γ' t)) * deriv γ' t) =
        -∫ t in (0 : ℝ)..1, γ t ^ ((k : ℤ) - 1) *
        sLocalIdelicZFunction f (tw c₁ (γ t)) * deriv γ t :=
      sLocalPrincipalPartCoeff_any_contour_reverse γ
        (fun w ↦ w ^ ((k : ℤ) - 1) * sLocalIdelicZFunction f (tw c₁ w))
    have e1' : sLocalZLaurentCoeff f c₁ k = (∫ t in (0 : ℝ)..1, γ t ^ ((k : ℤ) - 1) *
        sLocalIdelicZFunction f (tw c₁ (γ t)) * deriv γ t) /
        (2 * (Real.pi : ℂ) * Complex.I) := e1
    have e2' : sLocalZLaurentCoeff f c₁ k = (∫ t in (0 : ℝ)..1, γ' t ^ ((k : ℤ) - 1) *
        sLocalIdelicZFunction f (tw c₁ (γ' t)) * deriv γ' t) /
        (2 * (Real.pi : ℂ) * Complex.I) := e2
    rw [e3, neg_div] at e2'
    linear_combination (e1' + e2') / 2
  -- the Z-functions on the trivial component
  have hZm (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
      MeromorphicOn (fun z ↦ sLocalIdelicZFunction f (tw c₁ z)) univ :=
    (sLocalIdelicZFunction_meromorphic f χ).meromorphicOn
  have hpoleF (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) :
      ∃ a : ℂ, ∀ᶠ z in 𝓝[≠] (0 : ℂ), sLocalIdelicZFunction f (tw c₁ z) = a * z⁻¹ := by
    have hord := sLocalThetaPoleBound_low_coefficients_exact_polar_le f c₁
    unfold sLocalPolarMultiplicity at hord
    exact sLocalPrincipalPartCoeff_any_contour_simplePole (hZm f 0 (mem_univ 0))
      (hord.trans hle) (fun k ↦ hzero f k)
  obtain ⟨f, hf⟩ := sLocalPrincipalPartCoeff_any_contour_gaussian.{u}
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨t, ht⟩ := exists_ne (1 : ℝ≥0ˣ)
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (σ t)
  have hmu : sIdeleQuotientNorm F S (QuotientGroup.mk u) ≠ 1 := by
    rw [hu, hσ t]; exact ht
  let m : ℝ := ((sIdeleQuotientNorm F S (QuotientGroup.mk u) : ℝ≥0) : ℝ)
  have hmpos : 0 < m := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hm1 : m ≠ 1 := by
    intro h1
    exact hmu (Units.val_eq_one.mp (NNReal.coe_eq_one.mp h1))
  let τf := schwartzBruhatUnitTranslate u f
  have hrel (x : ℝ) (hx : 0 < x) : sLocalIdelicZFunction τf (tw c₁ x) =
      ((m ^ x : ℝ) : ℂ) * sLocalIdelicZFunction f (tw c₁ x) := by
    have hp : (x : ℂ) ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by simpa using hx
    rw [sLocalIdelicZFunction_eq_integral τf ⟨χ, _, hp, rfl⟩,
      sLocalIdelicZFunction_eq_integral f ⟨χ, _, hp, rfl⟩,
      sLocalPrincipalPartCoeff_eigendistribution_translate]
    congr 1
    change ((circleToComplex).comp χ) _ * ((m : ℝ) : ℂ) ^ (x : ℂ) = _
    rw [Complex.ofReal_cpow hmpos.le]
    change ((1 : Circle) : ℂ) * _ = _
    rw [Circle.coe_one, one_mul]
  obtain ⟨a, ha⟩ := hpoleF f
  obtain ⟨b, hb⟩ := hpoleF τf
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), sLocalIdelicZFunction f (tw c₁ (x : ℂ)) = a * (x : ℂ)⁻¹ ∧
      sLocalIdelicZFunction τf (tw c₁ (x : ℂ)) = b * (x : ℂ)⁻¹ := by
    have hT : Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
        (eventually_nhdsWithin_of_forall fun x (hx : 0 < x) ↦ by
          simpa using hx.ne')
    exact hT.eventually (ha.and hb)
  obtain ⟨δ, hδ, hδs⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hpt (x : ℝ) (hx : x ∈ Ioo 0 δ) : b = ((m ^ x : ℝ) : ℂ) * a := by
    obtain ⟨e1, e2⟩ := hδs hx
    have e := hrel x hx.1
    rw [e1, e2] at e
    have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast hx.1.ne'
    have e' : b * (x : ℂ)⁻¹ = ((m ^ x : ℝ) : ℂ) * a * (x : ℂ)⁻¹ := by rw [e]; ring
    exact mul_right_cancel₀ (inv_ne_zero hx0) e'
  have hδ0 : (0 : ℝ) < δ := hδ
  have ha0 : a = 0 := by
    have p1 := hpt (δ / 2) ⟨by positivity, by linarith⟩
    have p2 := hpt (δ / 3) ⟨by positivity, by linarith⟩
    have hne : m ^ (δ / 2) ≠ m ^ (δ / 3) := by
      intro he
      have := congrArg Real.log he
      rw [Real.log_rpow hmpos, Real.log_rpow hmpos] at this
      have hl := Real.log_ne_zero_of_pos_of_ne_one hmpos hm1
      have := mul_right_cancel₀ hl this
      linarith
    have hne' : ((m ^ (δ / 2) : ℝ) : ℂ) - ((m ^ (δ / 3) : ℝ) : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (by exact_mod_cast hne)
    have : (((m ^ (δ / 2) : ℝ) : ℂ) - ((m ^ (δ / 3) : ℝ) : ℂ)) * a = 0 := by
      rw [sub_mul, ← p1, ← p2, sub_self]
    exact (mul_eq_zero.mp this).resolve_left hne'
  -- the identity theorem
  have h0 : meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction f (tw c₁ z)) 0 = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [ha] with z hz
    rw [hz, ha0, zero_mul]
  have h12 := (hZm f).meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ
    (mem_univ 0) (mem_univ (1 / 2)) h0
  rw [meromorphicOrderAt_eq_top_iff] at h12
  have hopen : IsOpen (Complex.re ⁻¹' Ioi (0 : ℝ)) := isOpen_Ioi.preimage Complex.continuous_re
  have hhalf : (1 / 2 : ℂ) ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
    show (0 : ℝ) < (1 / 2 : ℂ).re
    norm_num
  have hcont : ContinuousAt (fun z ↦ sLocalIdelicZFunction f (tw c₁ z)) (1 / 2) :=
    (((sLocalIdelicZetaIntegral_analyticOn f χ) _ hhalf).congr
      (Filter.eventually_of_mem (hopen.mem_nhds hhalf) fun z hz ↦
        (sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩).symm)).continuousAt
  have hv : sLocalIdelicZFunction f (tw c₁ (1 / 2)) = 0 :=
    tendsto_nhds_unique (hcont.tendsto.mono_left nhdsWithin_le_nhds)
      (tendsto_const_nhds.congr' (h12.mono fun z hz ↦ hz.symm))
  exact hf hv

/-- Paper: Equation (7.2.1.8), p. 334.
Over ℚ with only the real place, a nonnegative nonzero even bump on 2 < |x| < 3
has positive first Mellin derivative at zero and zero integral in the formula for
index one on a small circle. Independently of the subscript convention, at index
zero the Gaussian on the positive circle of center −1 and radius 3/2 picks up the
additional residue π of Γℝ(z)/z at −2. -/
theorem sLocalPrincipalPartCoeff_any_contour_false :
    ¬ sLocalPrincipalPartCoeff_any_contour :=
  sLocalPrincipalPartCoeff_any_contour_false_aux

end Printed
end RiemannMasullo
