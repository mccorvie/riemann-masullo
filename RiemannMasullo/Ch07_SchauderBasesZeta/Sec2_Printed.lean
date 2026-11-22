module

public import Mathlib.Algebra.Field.ULift
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2

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

/-- Paper: Equation (7.2.1.8), p. 334.
Over ℚ with only the real place, a nonnegative nonzero even bump on 2 < |x| < 3
has positive first Mellin derivative at zero and zero integral in the formula for
index one on a small circle. Independently of the subscript convention, at index
zero the Gaussian on the positive circle of center −1 and radius 3/2 picks up the
additional residue π of Γℝ(z)/z at −2. -/
theorem sLocalPrincipalPartCoeff_any_contour_false :
    ¬ sLocalPrincipalPartCoeff_any_contour := by sorry

/-- Paper: Theorem 7.2.1.1(2), p. 334.
Each coefficient descends to the homogeneous theta quotient and is an
eigendistribution of weight equal to its center. -/
def sLocalPrincipalPartCoeff_eigendistribution : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F))
    (ω : PontryaginDual J₁(F, S)) (c : Xₛ(F, S)), onComponent(F, S, c, ω) → ∀ k : ℕ,
    LinearMap.ker (sLocalAdelicTheta F S) ≤ (sLocalNonnegativeLaurentCoeff c k).ker ∧
      Kₛ(F, S, ω) ≤ (sLocalNonnegativeLaurentCoeff c k).ker ∧
      sLocalNonnegativeLaurentCoeff c k ∈ sLocalEigendistributions c

/-- Paper: Theorem 7.2.1.1(2), p. 334.
For ℚ at the real place, translate a nonzero nonnegative even bump supported in
2 < |x| < 3 by dilation by 2. At the trivial center its first Mellin derivative
increases by log(2) times the positive constant coefficient. With the polar
reading of (7.2.1.8), use the Gaussian times the integer indicator over ℚ at
∞ and p. The top coefficient is 2/log p, so translation by p changes the
residue by −2 at the trivial character. -/
theorem sLocalPrincipalPartCoeff_eigendistribution_false :
    ¬ sLocalPrincipalPartCoeff_eigendistribution := by sorry

/-- Paper: Theorem 7.2.1.1(3), p. 334.
A nonzero coefficient functional forces the corresponding pole-order bound on every test. -/
def sLocalPrincipalPartCoeff_universal_pole_bound : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (S : Finset Places(F)) (c : Xₛ(F, S)) (k : ℕ),
    sLocalNonnegativeLaurentCoeff c k ≠ 0 →
      c ∈ poleLocus(F, S) ∧ ∀ f : ℬₛ(F, S), k ≤ sLocalPolarMultiplicity f c

/-- Paper: Theorem 7.2.1.1(3), p. 334.
At the trivial character over ℚ with only the real place, an even nonnegative
nonzero bump on 2 < |x| < 3 has positive first Mellin derivative and no pole. -/
theorem sLocalPrincipalPartCoeff_universal_pole_bound_false :
    ¬ sLocalPrincipalPartCoeff_universal_pole_bound := by sorry

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

/-- Paper: Remark 7.2.1.2, p. 335.
For ℚ with only the real place and the trivial component, the constant entire
function one satisfies the divisor bound but violates the vertical decay of
every Schwartz–Bruhat Mellin transform on the line of real part one. -/
theorem sLocalMellin_surjective_divisorBounded_false :
    ¬ sLocalMellin_surjective_divisorBounded := by sorry

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

end Printed
end RiemannMasullo
