module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Exponential system on monogenic quotients

Masullo, §4.4, pp. 188–197. We use the left translation convention
`f (g⁻¹ * x)` and the Fourier convention of §D.1.1.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set Topology UniformSpace
open scoped ENNReal NNReal TensorProduct

set_option quotPrecheck false

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (γ : G)

local notation "K" => m.toMonoidHom.ker
local notation "L" => Real.log ((m γ).val : ℝ)
local notation "Γ" => Subgroup.zpowers γ
local notation "Q" => G ⧸ Γ
local notation "S" => SchwartzBruhat Q
local notation "E" => ModulatedExponentialDecay m (Set.univ : Set ℝ)
local notation "logModule" x => Real.log ((m x).val : ℝ)
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)

/-! ## 4.4.1 Mellin transform in split coordinates -/

-- TODO(paper-gap): Page 189 calls S_I(G) locally compact and identifies its
-- topology with the projective twist topology for arbitrary I.
-- TODO(paper-gap): The compact Fourier factor in (4.4.1.2) is a function on Ĝ¹.
-- The displayed codomain uses G¹, and the next formula evaluates M at c(τ(t)g).

section Mellin

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
variable (hm : IsModulation m) (hms : Surjective m)
variable (I : Set ℝ) (hOpen : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty)
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (χ : PontryaginDual G)

local notation "D" => ModulatedExponentialDecay m I
local notation "P" => PositiveRealExponentialDecay I
local notation "B" => SchwartzBergman I
local notation "M" => positiveRealFourierMellin I hOpen hInt hne
local notation "twist[" s "]" => quasiCharacterNormTwist m.toMonoidHom m.continuous
  ((circleToComplex).comp χ) s
local notation "phase[" b "]" => (b : ℂ) * Complex.I
local notation "avg⟦" f ", " t "⟧" => (∫ k : K, (χ k.val : ℂ) * (f).val (k.val * τ t) ∂μ₁)

include hOpen hInt hne hms hτ hμ in
/-- Paper: Equations (4.4.1.1) and (4.4.1.4), pp. 189–190. In the chart of a unitary
character, the group Mellin integral splits into the compact character integral
and a positive-real integral. Both the inner and outer integrals converge. -/
theorem modulatedMellin_split (f : D) (s : ℂ) (hs : s.re ∈ I) :
    (∀ t : ℝ≥0ˣ, Integrable (fun k : K ↦ (χ k.val : ℂ) * f.val (k.val * τ t)) μ₁) ∧
    Integrable (fun t : ℝ≥0ˣ ↦ ((t.val : ℝ) : ℂ) ^ s * (χ (τ t) : ℂ) * avg⟦f, t⟧)
      positiveRealHaar ∧
    modulatedFourierMellin m I hm μ f.val (twist[s]) =
      ∫ t : ℝ≥0ˣ, ((t.val : ℝ) : ℂ) ^ s * (χ (τ t) : ℂ) * avg⟦f, t⟧ ∂positiveRealHaar := by
  sorry

include hOpen hInt hne hms hτ hμ in
/-- Paper: Equation (4.4.1.2), p. 190. The Mellin transform identifies the decay
space with the completed inductive tensor of the compact dual's Schwartz–Bruhat
space and the scalar Schwartz–Bergman space, evaluated in split coordinates.
Deviation: The compact Fourier factor is indexed by characters of the norm-one
group, as in Theorem D.3.3.13. Its Haar measure can have arbitrary positive mass. -/
theorem modulatedMellin_tensor_equiv :
    let U := InductiveTensor (SchwartzBruhat (PontryaginDual K)) B
    ∃ (F : D ≃L[ℂ] Completion U) (j : Completion U →L[ℂ] (PontryaginDual K → B)),
      Injective j ∧
      (∀ (v : SchwartzBruhat (PontryaginDual K)) (H : B) ω,
        j (Completion.coe' (α := U) (v ⊗ₜ[ℂ] H)) ω = v ω • H) ∧
      ∀ (f : D) (c : QuasiCharacter G) (ω : PontryaginDual K) (s : ℂ), s.re ∈ I →
        (∀ (k : K) (t : ℝ≥0ˣ),
          c (k.val * τ t) = (ω k : ℂ) * ((t.val : ℝ) : ℂ) ^ s) →
        modulatedFourierMellin m I hm μ f.val c = (j (F f) ω).val s := by sorry

/-- Paper: Discussion 4.4.1.1, p. 191. A unitary character has a unique real
frequency along the fixed positive-real section. -/
theorem existsUnique_modulatedMellinSectionFrequency :
    ∃! b : ℝ, ∀ t : ℝ≥0ˣ, χ (τ t) = Circle.exp (b * Real.log (t.val : ℝ)) := by
  have key (b : ℝ) (t : ℝ≥0ˣ) : ((t.val : ℝ) : ℂ) ^ ((b : ℂ) * Complex.I) =
      (Circle.exp (b * Real.log (t.val : ℝ)) : ℂ) := by
    have ht : 0 < (t.val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne'),
      ← Complex.ofReal_log ht.le, Circle.coe_exp]
    congr 1
    push_cast
    ring
  obtain ⟨z, ⟨hre, hz⟩, huniq⟩ := existsUnique_unitaryComplexPower
    ((circleToComplex).comp (ContinuousMonoidHom.comp χ τ)) (fun t ↦ Circle.norm_coe _)
  have hzb : z = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp [hre]
  refine ⟨z.im, fun t ↦ Circle.ext ?_, fun b hb ↦ ?_⟩
  · rw [← key, ← hzb]
    exact hz t
  · have h := huniq ((b : ℂ) * Complex.I) ⟨by simp, fun t ↦ ?_⟩
    · rw [← h]
      simp
    · rw [key, ← hb t]
      rfl

-- TODO(paper-gap): The bottom arrow in (4.4.1.3) evaluates the scalar Mellin
-- transform at s. The displayed integral on p. 191 evaluates it at s + i x₀.
-- Item (3) also uses the idele class notation C_F¹ for the general group G¹.

include hms hτ hμ in
/-- Paper: Discussion 4.4.1.1, pp. 190–191. The compact average followed by
restriction to the section identifies its kernel quotient with the scalar decay
space. The group transform on this character component agrees, after translation
of its argument by minus the section frequency times i, with the scalar Mellin
transform of that profile.
Deviation: The bottom arrow uses the unshifted scalar Mellin transform specified
by the diagram. The isotypic quotient is represented by the kernel of the
section profile of the unnormalized average. -/
theorem modulatedMellin_isotypicDiagram (b : ℝ)
    (hb : ∀ t : ℝ≥0ˣ, χ (τ t) = Circle.exp (b * Real.log (t.val : ℝ))) :
    ∃ (A : D →L[ℂ] P) (F : D →L[ℂ] B) (T : B ≃L[ℂ] B)
      (e : (D ⧸ A.ker) ≃L[ℂ] P),
      (∀ f t, (A f).val (Real.log (t.val : ℝ)) = avg⟦f, t⟧) ∧
      (∀ f s, s.re ∈ I → (F f).val s = modulatedFourierMellin m I hm μ f.val (twist[s])) ∧
      (∀ H s, s.re ∈ I → (T H).val s = H.val (s - phase[b])) ∧
      (∀ f, e (A.ker.mkQ f) = A f) ∧
      (∀ f, T (F f) = M (e (A.ker.mkQ f))) := by sorry

include hOpen hInt hne hms in
/-- Paper: Discussion 4.4.1.1(1–2), p. 191. Translation by the inverse generator
acts on the group Mellin transform by the value of the twisted character there. -/
theorem modulatedMellin_translate (f : D) (s : ℂ) (hs : s.re ∈ I) :
    let f' : D := ⟨fun x ↦ f.val ((γ⁻¹)⁻¹ * x),
      modulatedExponentialDecaySubmodule_translate m I hm hms γ⁻¹ f⟩
    modulatedFourierMellin m I hm μ f'.val (twist[s]) =
      (χ γ⁻¹ : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s) *
        modulatedFourierMellin m I hm μ f.val (twist[s]) := by
  intro f'
  have hmem : twist[s] ∈ relativeVerticalStrip m.toMonoidHom hm.1 hm.2 I := by
    change quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 (twist[s]) ∈ I
    rw [quasiCharacterAbscissa_of_unitary_twist m.toMonoidHom hm.1 hm.2 _ χ s (fun _ ↦ rfl)]
    exact hs
  have hval : (twist[s]) γ⁻¹ = (χ γ⁻¹ : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s) := by
    change (χ γ⁻¹ : ℂ) * (((m γ⁻¹).val : ℝ) : ℂ) ^ s = _
    rw [map_inv m γ, Units.val_inv_eq_inv_val, NNReal.coe_inv, Complex.ofReal_inv,
      Complex.inv_cpow_ofReal_nonneg (NNReal.coe_nonneg _), Complex.cpow_neg]
  exact (modulatedFourierMellin_equivariant m I hm hInt hne μ hOpen hms γ⁻¹ f ⟨_, hmem⟩).trans
    (congrArg (· * modulatedFourierMellin m I hm μ f.val (twist[s])) hval)

include hτ in
/-- Paper: Discussion 4.4.1.1(3), p. 191. Compact averaging sends translation by
the inverse generator to dilation of the positive-real profile by its module,
weighted by the character of the inverse generator's compact component. -/
theorem modulatedMellin_average_translate (f : D) (t : ℝ≥0ˣ) :
    (∫ k : K, (χ k.val : ℂ) * f.val (γ * (k.val * τ t)) ∂μ₁) =
      (χ (τ (m γ) * γ⁻¹) : ℂ) * avg⟦f, m γ * t⟧ := by
  have hk₀ : γ * (τ (m γ))⁻¹ ∈ K := by
    change m (γ * (τ (m γ))⁻¹) = 1
    rw [map_mul, map_inv m (τ (m γ)), hτ (m γ), mul_inv_cancel]
  obtain ⟨k₀, hk₀v⟩ : ∃ k₀ : K, k₀.val = γ * (τ (m γ))⁻¹ := ⟨⟨_, hk₀⟩, rfl⟩
  have hpt (k : K) : (χ k.val : ℂ) * f.val (γ * (k.val * τ t)) =
      (χ (τ (m γ) * γ⁻¹) : ℂ) *
        ((χ (k₀ * k).val : ℂ) * f.val ((k₀ * k).val * τ (m γ * t))) := by
    have h1 : γ * (k.val * τ t) = (k₀ * k).val * τ (m γ * t) := by
      rw [Subgroup.coe_mul, hk₀v, map_mul τ, mul_assoc γ, mul_assoc γ, mul_comm _ k.val,
        mul_assoc k.val, inv_mul_cancel_left]
    have h2 : k.val = τ (m γ) * γ⁻¹ * (k₀ * k).val := by
      rw [Subgroup.coe_mul, hk₀v, mul_assoc γ, mul_assoc, inv_mul_cancel_left,
        mul_inv_cancel_left]
    rw [h1, ← mul_assoc, ← Circle.coe_mul, ← map_mul, ← h2]
  simp_rw [hpt]
  rw [integral_const_mul]
  congr 1
  exact integral_mul_left_eq_self
    (fun k : K ↦ (χ k.val : ℂ) * f.val (k.val * τ (m γ * t))) k₀

include hτ in
/-- Paper: Discussion 4.4.1.1(3), p. 191. The cyclic translation action descends
continuously to the isotypic quotient, realized as the quotient by the kernel
of the compact average in section coordinates. -/
theorem modulatedMellin_isotype_quotient_action (hγ : 1 < (m γ).val)
    (A : D →L[ℂ] P)
    (hA : ∀ f t, (A f).val (Real.log (t.val : ℝ)) = avg⟦f, t⟧)
    (ρ : G →* (D →L[ℂ] D)) (hρ : ∀ g f x, (ρ g f).val x = f.val (g⁻¹ * x)) :
    let V := D ⧸ A.ker
    ∃ r : (Γ) →* (V →L[ℂ] V),
      (∀ (g : (Γ)) (f : D), r g (A.ker.mkQ f) = A.ker.mkQ (ρ g.val f)) ∧
      Continuous (fun z : (Γ) × V ↦ r z.1 z.2) := by sorry

include hOpen hInt hne in
/-- Paper: Discussion 4.4.1.1(4), p. 191. The scalar Mellin transform takes the
dilation and compact character factor of the section profile to multiplication
by the corresponding complex power and character value. -/
theorem modulatedMellin_profile_translate (p p' : P)
    (hp : ∀ x : ℝ, p'.val x = (χ (τ (m γ) * γ⁻¹) : ℂ) * p.val (L + x))
    (s : ℂ) (hs : s.re ∈ I) :
    (M p').val s =
      (χ (τ (m γ) * γ⁻¹) : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s) * (M p).val s := by
  have ha : 0 < ((m γ).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m γ))
  rw [positiveRealFourierMellin_apply I hOpen hInt hne p' s hs,
    positiveRealFourierMellin_apply I hOpen hInt hne p s hs, mul_assoc,
    ← smul_eq_mul (a := (((m γ).val : ℝ) : ℂ) ^ (-s)),
    ← mellin_comp_mul_left (fun u ↦ p.val (Real.log u)) s ha, ← smul_eq_mul,
    ← mellin_const_smul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
  simp only [hp, Real.log_mul ha.ne' (mem_Ioi.mp ht).ne', smul_eq_mul]

/-- Paper: Discussion 4.4.1.1(5), p. 191. Translating the group multiplier in the
spectral variable gives the compact character times the scalar multiplier. -/
theorem modulatedMellin_shift_multiplier (b : ℝ)
    (hb : ∀ t : ℝ≥0ˣ, χ (τ t) = Circle.exp (b * Real.log (t.val : ℝ))) (s : ℂ) :
    (χ γ⁻¹ : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s + phase[b]) =
      (χ (τ (m γ) * γ⁻¹) : ℂ) * (((m γ).val : ℝ) : ℂ) ^ (-s) := by
  have hx : 0 < ((m γ).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m γ))
  have hx' : (((m γ).val : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have key : (((m γ).val : ℝ) : ℂ) ^ phase[b] = (χ (τ (m γ)) : ℂ) := by
    rw [hb, Complex.cpow_def_of_ne_zero hx', ← Complex.ofReal_log hx.le, Circle.coe_exp]
    congr 1
    push_cast
    ring
  rw [map_mul, Circle.coe_mul, Complex.cpow_add _ _ hx', key]
  ring

end Mellin

/-! ## 4.4.2 Periodization and the exponential system -/

section Periodization

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (hm : IsModulation m) (hms : Surjective m) (hγ : 1 < (m γ).val)

local notation "per[" f ", " x "]" => ∑' n : ℤ, (f).val (γ ^ n * x)

include hm hms hγ in
/-- Paper: Definition 4.4.2.1, pp. 191–192. The orbit sum at a representative
belongs to the Schwartz–Bruhat space of the quotient. -/
theorem modulatedPeriodization_mem (f : E) :
    (fun z : Q ↦ per[f, z.out]) ∈ schwartzBruhatSubmodule Q := by sorry

/-- Paper: Definition 4.4.2.1, pp. 191–192. Periodization sums a two-sided
exponentially decaying function over the integer translates of a quotient point. -/
def modulatedPeriodization (f : E) : S :=
  ⟨fun z ↦ per[f, z.out], modulatedPeriodization_mem m γ hm hms hγ f⟩

/-- Paper: Definition 4.4.2.1, p. 192. At every lift of a quotient point the
orbit series converges to the specified periodization. -/
theorem modulatedPeriodization_hasSum (f : E) (x : G) :
    HasSum (fun n : ℤ ↦ f.val (γ ^ n * x))
      (modulatedPeriodization m γ hm hms hγ f (QuotientGroup.mk x)) := by sorry

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "weightedOrbit⟦" f ", " n ", " x "⟧" =>
  ∫ k : K, (χ k.val : ℂ) * (f).val (γ ^ n * (k.val * x)) ∂μ₁

include hm hms hγ in
/-- Paper: Definition 4.4.2.1, pp. 191–192. The character-weighted orbit
sum at a representative belongs to the Schwartz–Bruhat space of the quotient. -/
theorem modulatedIsotypicPeriodization_mem (f : E) :
    (fun z : Q ↦ ∑' n : ℤ, weightedOrbit⟦f, n, z.out⟧) ∈ schwartzBruhatSubmodule Q := by sorry

/-- Paper: Definition 4.4.2.1 and Remark 4.4.2.2, pp. 191–192. Homogeneous
periodization sums the unnormalized compact character averages over the orbit.
The formula weights the translate by the character evaluated at the translating
element and uses only the restriction of the character to the compact group. -/
def modulatedIsotypicPeriodization (f : E) : S :=
  ⟨fun z ↦ ∑' n : ℤ, weightedOrbit⟦f, n, z.out⟧,
    modulatedIsotypicPeriodization_mem m γ hm hms hγ μ₁ χ f⟩

include hm in
/-- Paper: Definition 4.4.2.1, p. 192. For every lift and every integer
translate the compact average is integrable. -/
theorem modulatedIsotypicPeriodization_integrable (f : E) (n : ℤ) (x : G) :
    Integrable (fun k : K ↦ (χ k.val : ℂ) * f.val (γ ^ n * (k.val * x))) μ₁ := by sorry

/-- Paper: Definition 4.4.2.1, p. 192. At every lift the orbit series of the
compact averages converges to the homogeneous periodization. -/
theorem modulatedIsotypicPeriodization_hasSum (f : E) (x : G) :
    HasSum (fun n : ℤ ↦ weightedOrbit⟦f, n, x⟧)
      (modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ f (QuotientGroup.mk x)) := by sorry

/-- Paper: Definition 4.4.2.1, p. 192. Left translation by a norm-one element
multiplies the homogeneous periodization by the character evaluated there. -/
theorem modulatedIsotypicPeriodization_homogeneous (f : E) (k : K) (z : Q) :
    let F := modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ f
    F (QuotientGroup.mk k.val⁻¹ * z) = (χ k.val : ℂ) * F z := by sorry

-- TODO(later): needs §4.5.1.1 for convergence in the Schwartz–Bruhat topology
-- and the continuous, open and surjective periodization maps there.

end Periodization

section CyclicCharacters

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (hm : IsModulation m) (hms : Surjective m) (hγ : 1 < (m γ).val)
variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (k : m.toMonoidHom.ker), χ ω k.val = ω k)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)

local notation "J" => PontryaginDual K × ℤ
local notation "expValue[" j ", " x "]" =>
  (χ (j).1 x)⁻¹ * Circle.exp ((t₀ (j).1 - 2 * Real.pi * ((j).2 : ℝ) / L) * logModule x)

-- TODO(paper-gap): Situation 4.4.2.3 calls γ a real number and leaves the
-- restriction equation in (4) unfinished. Here γ is an element of G and
-- the lift restricts to ω.

/-- Paper: Situation 4.4.2.3(4–5), p. 192. Each norm-one character admits a lift
with its section frequency and its phase at the generator.
Deviation: The restriction equation missing from (4) is stated as in Lemma 4.4.2.5. -/
theorem exists_modulatedCyclicCharacter_lifts (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (hγ : 1 < (m γ).val) :
    ∃ (χ : PontryaginDual K → PontryaginDual G) (b t₀ : PontryaginDual K → ℝ),
      (∀ ω (k : K), χ ω k.val = ω k) ∧
      (∀ ω (t : ℝ≥0ˣ), χ ω (τ t) = Circle.exp (b ω * Real.log (t.val : ℝ))) ∧
      (∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t₀ ω * L) = χ ω γ) := by
  have hmem (x : G) : x * (τ (m x))⁻¹ ∈ K := by
    change m (x * (τ (m x))⁻¹) = 1
    rw [map_mul, map_inv, hτ (m x), mul_inv_cancel]
  let p : G →ₜ* K :=
    { toFun := fun x ↦ ⟨x * (τ (m x))⁻¹, hmem x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y ↦ Subtype.ext (by
        change x * y * (τ (m (x * y)))⁻¹ = x * (τ (m x))⁻¹ * (y * (τ (m y))⁻¹)
        rw [map_mul, map_mul, mul_inv, mul_mul_mul_comm])
      continuous_toFun :=
        (continuous_id.mul (τ.continuous.comp m.continuous).inv).subtype_mk hmem }
  let χ : PontryaginDual K → PontryaginDual G := fun ω ↦ ContinuousMonoidHom.comp ω p
  have hphase (ω : PontryaginDual K) :
      ∃ t : ℝ, t ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t * L) = χ ω γ :=
    (existsUnique_modulatedCharacterPhase m γ hγ (χ ω)).exists
  choose t₀ ht₀ using hphase
  refine ⟨χ, fun _ ↦ 0, t₀, fun ω k ↦ ?_, fun ω t ↦ ?_, ht₀⟩
  · have hk : p k.val = k := Subtype.ext (by
      change k.val * (τ (m k.val))⁻¹ = k.val
      rw [show m k.val = 1 from k.property, map_one, inv_one, mul_one])
    change ω (p k.val) = ω k
    rw [hk]
  · have ht : p (τ t) = 1 := Subtype.ext (by
      change τ t * (τ (m (τ t)))⁻¹ = 1
      rw [hτ t, mul_inv_cancel])
    change ω (p (τ t)) = _
    rw [ht]
    simp

include hm hms hχ in
/-- Paper: Remark 4.4.2.4, p. 192. With the chosen lifts, the norm twists
parametrize all continuous quasi-characters, one complex coordinate per
norm-one character. The unitary characters correspond to the imaginary axis. -/
theorem modulatedCyclicQuasiCharacter_coordinates :
    ∃ e : (PontryaginDual K × ℂ) ≃ₜ QuasiCharacter G,
      (∀ p, e p = quasiCharacterNormTwist m.toMonoidHom m.continuous
        ((circleToComplex).comp (χ p.1)) p.2) ∧
      ∀ p, (∀ x : G, ‖e p x‖ = 1) ↔ p.2.re = 0 := by sorry

/-- Paper: Lemma 4.4.2.5, p. 193. The cyclic subgroup is closed, so its
quotient is Hausdorff. -/
theorem modulatedCyclicSubgroup_closed (hγ : 1 < (m γ).val) :
    IsClosed (Γ : Set G) := by
  have := modulated_zpowers_discrete m γ hγ
  exact Subgroup.isClosed_of_discreteTopology

/-- Paper: Lemma 4.4.2.5, p. 193. The quotient by the cyclic subgroup is compact. -/
theorem modulatedCyclicQuotient_compact (hm : IsModulation m) (hγ : 1 < (m γ).val) :
    CompactSpace Q := by sorry

include ht₀ hγ in
/-- Paper: Lemma 4.4.2.5, p. 193. The exponential formula is a continuous
unitary homomorphism on the quotient. -/
theorem modulatedCyclicCharacter_properties (j : J) :
    let u : G → Circle := fun x ↦ expValue[j, x]
    u 1 = 1 ∧ (∀ x y, u (x * y) = u x * u y) ∧ Continuous u ∧
      (∀ x : (Γ), u x.val = 1) := by
  intro u
  have hpos (x : G) : ((m x).val : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hL : L ≠ 0 := (Real.log_pos (by exact_mod_cast hγ)).ne'
  have hone : u 1 = 1 := by simp [u]
  have hmul (x y : G) : u (x * y) = u x * u y := by
    simp only [u, map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos x) (hpos y), mul_add,
      Circle.exp_add, mul_inv]
    exact mul_mul_mul_comm _ _ _ _
  have hcont : Continuous u := by
    have hlog : Continuous fun x : G ↦ logModule x :=
      (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log hpos
    exact (map_continuous (χ j.1)).inv.mul
      (Circle.exp.continuous.comp (continuous_const.mul hlog))
  have hgen : u γ = 1 := by
    have harg : (t₀ j.1 - 2 * Real.pi * (j.2 : ℝ) / L) * L =
        t₀ j.1 * L - 2 * Real.pi * (j.2 : ℝ) := by
      rw [sub_mul, div_mul_cancel₀ _ hL]
    change (χ j.1 γ)⁻¹ * Circle.exp ((t₀ j.1 - 2 * Real.pi * (j.2 : ℝ) / L) * L) = 1
    rw [harg, Circle.exp_sub, (ht₀ j.1).2, Circle.exp_two_pi_mul_int, div_one, inv_mul_cancel]
  refine ⟨hone, hmul, hcont, ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  let U : G →* Circle := { toFun := u, map_one' := hone, map_mul' := hmul }
  have hU (y : G) : U y = u y := rfl
  change u (γ ^ k) = 1
  rw [← hU, map_zpow, hU, hgen, one_zpow]

/-- Paper: Equation (4.4.2.4), p. 193. The lattice character is the inverse of
the chosen lift multiplied by the indicated phase and integer frequency. -/
def modulatedCyclicCharacter (j : J) : PontryaginDual Q :=
  let h := modulatedCyclicCharacter_properties m γ hγ χ t₀ ht₀ j
  let u : G →* Circle :=
    { toFun := fun x ↦ expValue[j, x]
      map_one' := h.1
      map_mul' := h.2.1 }
  let v := QuotientGroup.lift Γ u (fun {x} hx ↦ h.2.2.2 ⟨x, hx⟩)
  ⟨v, (QuotientGroup.isQuotientMap_mk Γ).continuous_iff.mpr h.2.2.1⟩

/-- Paper: Equation (4.4.2.4), p. 193. The quotient character takes its
prescribed value at every representative. -/
theorem modulatedCyclicCharacter_mk (j : J) (x : G) :
    modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j (QuotientGroup.mk x) = expValue[j, x] := by
  simp only [modulatedCyclicCharacter]
  rfl

-- TODO(paper-gap): The proof on p. 193 chooses t₁ in an interval open at zero.
-- For the trivial lift this forces t₀ = -t₁ to be the excluded upper endpoint.

include hm hms hχ in
/-- Paper: Lemma 4.4.2.5, p. 193. Pulling the quotient characters back along the
quotient map gives exactly the annihilator, with one pair per character. -/
theorem modulatedCyclicCharacter_annihilator :
    let q : G →ₜ* Q := ⟨QuotientGroup.mk' Γ, QuotientGroup.continuous_mk⟩
    ∃ e : J ≃ lcaAnnihilator Γ,
      ∀ j, (e j).val = PontryaginDual.map q (modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j) := by
  sorry

include hm hγ in
/-- Paper: Lemma 4.4.2.5, p. 193. The annihilator carries the discrete topology
induced by the dual of the original group. -/
theorem modulatedCyclicAnnihilator_discrete :
    DiscreteTopology (lcaAnnihilator Γ) := by sorry

end CyclicCharacters

section ExponentialSystem

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (hm : IsModulation m) (hms : Surjective m) (hγ : 1 < (m γ).val)
variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (k : m.toMonoidHom.ker), χ ω k.val = ω k)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)

local notation "J" => PontryaginDual K × ℤ
local notation "ξ" => modulatedCyclicCharacter m γ hγ χ t₀ ht₀

include hm in
/-- Paper: Lemma 4.4.2.6(1), p. 193. The cyclic quotient character, viewed
as a complex-valued function, belongs to the Schwartz–Bruhat space. -/
theorem modulatedCyclicExponential_mem (j : J) :
    (fun z : Q ↦ (ξ j z : ℂ)) ∈ schwartzBruhatSubmodule Q := by sorry

/-- Paper: Equation (4.4.2.5), p. 193. The exponential basis vector is the
complex-valued cyclic quotient character. -/
def modulatedCyclicExponential (j : J) : S :=
  ⟨fun z ↦ (ξ j z : ℂ), modulatedCyclicExponential_mem m γ hm hγ χ t₀ ht₀ j⟩

local notation "e" => modulatedCyclicExponential m γ hm hγ χ t₀ ht₀

/-- Paper: Equation (4.4.2.5), p. 193. In split coordinates the exponential
has the conjugate compact character and the shifted integer frequency. -/
theorem modulatedCyclicExponential_split (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (b : PontryaginDual K → ℝ)
    (hb : ∀ ω (t : ℝ≥0ˣ), χ ω (τ t) = Circle.exp (b ω * Real.log (t.val : ℝ)))
    (j : J) (t : ℝ≥0ˣ) (k : K) (hk : χ j.1 k.val = j.1 k) :
    e j (QuotientGroup.mk (τ t * k.val)) =
      star (j.1 k : ℂ) *
        (Circle.exp ((t₀ j.1 - 2 * Real.pi * (j.2 : ℝ) / L - b j.1) *
          Real.log (t.val : ℝ)) : ℂ) := by sorry

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [hHaar₁ : μ₁.IsHaarMeasure]

local instance instMeasurableSpaceCyclicQuotientSec4 : MeasurableSpace Q := borel _
local instance instBorelSpaceCyclicQuotientSec4 : BorelSpace Q := ⟨rfl⟩
variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [hHaar : ν.IsHaarMeasure]

local notation "coeff⟦" j "⟧" => (fun f : S ↦ (L * μ₁.real univ)⁻¹ * lcaFourier ν f (ξ j))

include hm hHaar₁ hHaar in
/-- Paper: Equation (4.4.2.6), p. 193. With Haar measure on the compact quotient,
the Fourier coefficient formula is linear and continuous in the test function. -/
theorem modulatedCyclicFourierCoeff_linearContinuous (j : J) :
    IsLinearMap ℂ (coeff⟦j⟧) ∧ Continuous (coeff⟦j⟧) := by sorry

-- TODO(paper-gap): The exponent in (4.4.2.6) uses log γ, which is undefined
-- for a general group element. The conjugate of (4.4.2.5) uses log|γ|_G.

/-- Paper: Equation (4.4.2.6), p. 193. The coordinate functional integrates
against the conjugate of the exponential and divides by the quotient volume.
Deviation: The denominator inside the printed exponent is read as the logarithm
of the module, in accordance with (4.4.2.5). -/
def modulatedCyclicFourierCoeff (j : J) : StrongDual ℂ S :=
  let h := modulatedCyclicFourierCoeff_linearContinuous m γ hm hγ χ t₀ ht₀ μ₁ ν j
  ⟨IsLinearMap.mk' (coeff⟦j⟧) h.1, h.2⟩

local notation "a" => modulatedCyclicFourierCoeff m γ hm hγ χ t₀ ht₀ μ₁ ν

/-- Paper: Equation (4.4.2.6), p. 193. The coefficient integrates the
Schwartz–Bruhat function against the conjugate exponential with the stated normalization. -/
theorem modulatedCyclicFourierCoeff_apply (j : J) (f : S) :
    Integrable (fun z ↦ f z * star (e j z)) ν ∧
    a j f = (L * μ₁.real univ)⁻¹ * ∫ z, f z * star (e j z) ∂ν := by sorry

variable [SecondCountableTopology G]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G)
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

include hm hms hχ hτ hμ hν in
/-- Paper: Lemma 4.4.2.6(1), p. 193. Every enumeration of the full character
index gives an absolute Schauder basis, with the Fourier coefficients as coordinates. -/
theorem modulatedCyclicExponential_absoluteBasis :
    Nonempty (ℕ ≃ J) ∧
      ∀ σ : ℕ ≃ J, IsSchauderBasis (e ∘ σ) (a ∘ σ) ∧
        SchauderBasis.IsAbsolute (e ∘ σ) (a ∘ σ) := by sorry

include hm hms hχ hτ hμ hν in
/-- Paper: Lemma 4.4.2.6, p. 197. The coefficient functionals in any such
enumeration form an absolute Schauder basis of the strong dual. Its coordinate
functionals are evaluations at the original exponentials. -/
theorem modulatedCyclicFourierCoeff_absoluteBasis (σ : ℕ ≃ J) :
    let eval : ℕ → StrongDual ℂ (StrongDual ℂ S) :=
      fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (e (σ n))
    IsSchauderBasis (a ∘ σ) eval ∧ SchauderBasis.IsAbsolute (a ∘ σ) eval := by sorry

-- TODO(paper-gap): In (4.4.2.10) the Fourier transform must be evaluated
-- at the basis character itself with the displayed Fourier convention.

include hm hms hχ hτ hμ hν in
/-- Paper: Lemma 4.4.2.6(2a), p. 194. A unique Schwartz–Bruhat function on
the annihilator assigns each basis character its coordinate coefficient. -/
theorem modulatedCyclicFourierCoeff_schwartz (f : S) :
    let q : G →ₜ* Q := ⟨QuotientGroup.mk' Γ, QuotientGroup.continuous_mk⟩
    ∃! v : SchwartzBruhat (lcaAnnihilator Γ), ∀ j : J,
      ∀ η : lcaAnnihilator Γ, η.val = PontryaginDual.map q (ξ j) → v η = a j f := by sorry

/-- Paper: Lemma 4.4.2.6(2b), p. 194. For a fixed compact character, the seminorm
values of the exponential vectors multiply every Schwartz sequence into another
Schwartz sequence. The integers are written multiplicatively in the Bruhat space. -/
theorem modulatedCyclicExponential_seminorm_multiplier
    (p : Seminorm ℂ S) (hp : Continuous p) (ω : PontryaginDual K)
    (v : SchwartzBruhat (Multiplicative ℤ)) :
    (fun n : Multiplicative ℤ ↦ (p (e (ω, n.toAdd)) : ℂ) * v n) ∈
      schwartzBruhatSubmodule (Multiplicative ℤ) := by sorry

include hm hγ hτ hμ hν in
/-- Paper: Remark 4.4.2.7, p. 194. The Weil quotient measure has total mass
equal to the product of the logarithmic period and the volume of the norm-one group. -/
theorem modulatedCyclicQuotient_measure_univ :
    ν univ = ENNReal.ofReal L * μ₁ univ := by sorry

include hm hγ hτ hμ hν in
/-- Paper: Remark 4.4.2.7, p. 194. Dividing the quotient Haar measure by its
specified total mass gives the probability Haar measure. -/
theorem modulatedCyclicQuotient_probabilityHaar :
    IsProbabilityMeasure ((ENNReal.ofReal L * μ₁ univ)⁻¹ • ν) := by sorry

include hms hτ hμ hν in
/-- Paper: Remark 4.4.2.7, p. 194. Normalizing the norm-one Haar measure to
mass one gives the same Weil quotient measure as dividing by that mass
after taking the quotient. -/
theorem modulatedCyclicQuotient_canonicalHaar :
    IsWeilQuotientMeasure Γ (canonicalModulatedHaar m hm) Measure.count ((μ₁ univ)⁻¹ • ν) :=
  by sorry

-- TODO(paper-gap): Remark 4.4.2.8 gives no transport map for the topology of
-- the multiplier space. Its algebraic membership is used in Lemma 4.4.2.6(2b).
-- Its seminorm example on the positive reals also uses a function outside S(ℝ>0).

/-- Paper: Remark 4.4.2.9, p. 194. Multiplication by a unitary character
preserves the Schwartz–Bruhat space of the original group. -/
theorem pontryaginDual_mul_schwartzBruhat (η : PontryaginDual G) (f : SchwartzBruhat G) :
    (fun x ↦ (η x : ℂ) * f x) ∈ schwartzBruhatSubmodule G := by sorry

/-- Paper: Remark 4.4.2.9, p. 194. At a fixed compact character the values of a
continuous seminorm on the cyclic exponentials have polynomial growth.
Deviation: The polynomial bound is expressed with a nonnegative constant and
a power of one plus the absolute frequency. -/
theorem modulatedCyclicExponential_seminorm_polynomialGrowth
    (p : Seminorm ℂ S) (hp : Continuous p) (ω : PontryaginDual K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ d : ℕ, ∀ n : ℤ, p (e (ω, n)) ≤ C * (1 + |(n : ℝ)|) ^ d := by
  sorry

-- TODO(paper-gap): The proof on p. 195 asserts that the coefficients vanish
-- on the annihilator of the stage subgroup. They vanish off that annihilator.
-- TODO(paper-gap): For (4.4.2.8), a finite-set exhaustion must eventually
-- contain each fixed character. A union equal to the index set is insufficient.
-- TODO(paper-gap): On p. 196 the directional derivative symbol is zero at
-- the trivial character. Multiplication by it cannot be an automorphism.

end ExponentialSystem

end RiemannMasullo
