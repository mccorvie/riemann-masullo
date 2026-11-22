module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count

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

/-- A function in the Schwartz–Bruhat submodule is bounded. -/
private theorem schwartzBruhatSubmodule_exists_norm_le {H : Type*} [CommGroup H]
    [TopologicalSpace H] {g : H → ℂ} (hg : g ∈ schwartzBruhatSubmodule H) :
    ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C := by
  let P (g : H → ℂ) : Prop := ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C
  have hzero : P 0 := ⟨0, fun x ↦ by simp⟩
  have hadd : ∀ g h, P g → P h → P (g + h) := by
    rintro g h ⟨C, hC⟩ ⟨D, hD⟩
    exact ⟨C + D, fun x ↦ (norm_add_le (g x) (h x)).trans (add_le_add (hC x) (hD x))⟩
  refine Submodule.iSup_induction (motive := P) _ hg (fun a g hg ↦ ?_) hzero hadd
  refine Submodule.iSup_induction (motive := P) _ hg (fun e g hg ↦ ?_) hzero hadd
  obtain ⟨s, rfl⟩ := LinearMap.mem_range.mp hg
  have hb (z) : ‖s z‖ ≤ (elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal := by
    have hz : (‖s z‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0) := by
      rw [elementarySchwartzBound_zero]
      exact le_iSup (fun y ↦ (‖s y‖₊ : ℝ≥0∞)) z
    exact ENNReal.toReal_mono (s.property.2 (0, 0, 0, 0)).ne hz
  refine ⟨(elementarySchwartzBound (s : _ → ℂ) (0, 0, 0, 0)).toReal, fun x ↦ ?_⟩
  rw [schwartzBruhatStageRealization_apply]
  split_ifs
  · exact hb _
  · simp

/-- A two-sided sequence with geometric decay in both directions is summable. -/
private theorem summable_of_zpow_bounds (u : ℤ → ℂ) (c ρ C₁ C₂ : ℝ) (hc : 1 < c)
    (h1 : ∀ n, ‖u n‖ ≤ C₁ * (c ^ n * ρ)⁻¹) (h2 : ∀ n, ‖u n‖ ≤ C₂ * (c ^ n * ρ)) :
    Summable u := by
  have hg : Summable fun n : ℕ ↦ c⁻¹ ^ n :=
    summable_geometric_of_lt_one (inv_nonneg.mpr (zero_le_one.trans hc.le))
      (inv_lt_one_of_one_lt₀ hc)
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_norm_bounded (hg.mul_left (C₁ * ρ⁻¹)) fun n ↦ (h1 n).trans_eq ?_
    change C₁ * (c ^ (n : ℤ) * ρ)⁻¹ = C₁ * ρ⁻¹ * c⁻¹ ^ n
    rw [zpow_natCast, inv_pow]
    ring
  · refine Summable.of_norm_bounded (hg.mul_left (C₂ * ρ)) fun n ↦ (h2 (-n)).trans_eq ?_
    change C₂ * (c ^ (-(n : ℤ)) * ρ) = C₂ * ρ * c⁻¹ ^ n
    rw [zpow_neg, zpow_natCast, inv_pow]
    ring

/-- A two-sided decay function is dominated by the module and by its inverse. -/
private theorem modulatedExponentialDecay_exists_weight_bounds (f : E) :
    ∃ C₁ C₂ : ℝ, ∀ y : G, ‖f.val y‖ ≤ C₁ * ((m y).val : ℝ)⁻¹ ∧
      ‖f.val y‖ ≤ C₂ * ((m y).val : ℝ) := by
  obtain ⟨C₁, h1⟩ := schwartzBruhatSubmodule_exists_norm_le
    (Submodule.mem_comap.mp ((Submodule.mem_iInf _).mp f.property ⟨1, mem_univ 1⟩))
  obtain ⟨C₂, h2⟩ := schwartzBruhatSubmodule_exists_norm_le
    (Submodule.mem_comap.mp ((Submodule.mem_iInf _).mp f.property ⟨-1, mem_univ (-1)⟩))
  refine ⟨C₁, C₂, fun y ↦ ?_⟩
  have hy : 0 < ((m y).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m y))
  have e1 : ‖((((m y).val : ℝ) ^ (1 : ℝ) : ℝ) : ℂ) * f.val y‖ ≤ C₁ := h1 y
  have e2 : ‖((((m y).val : ℝ) ^ (-1 : ℝ) : ℝ) : ℂ) * f.val y‖ ≤ C₂ := h2 y
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _),
    Real.rpow_one] at e1
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hy.le _),
    Real.rpow_neg_one] at e2
  refine ⟨?_, ((inv_mul_le_iff₀ hy).mp e2).trans_eq (mul_comm _ _)⟩
  rw [← div_eq_mul_inv]
  exact (le_div_iff₀ hy).mpr ((mul_comm _ _).trans_le e1)

/-- The module of a point of the orbit of the generator. -/
private theorem modulation_zpow_mul (n : ℤ) (z : G) :
    ((m (γ ^ n * z)).val : ℝ) = ((m γ).val : ℝ) ^ n * ((m z).val : ℝ) := by
  rw [map_mul m, map_zpow m, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
    NNReal.coe_zpow]

/-- The periodization at the class of a point is the orbit sum at that point. -/
private theorem modulatedPeriodization_apply_mk (f : E) (x : G) :
    modulatedPeriodization m γ hm hms hγ f (QuotientGroup.mk x) =
      ∑' n : ℤ, f.val (γ ^ n * x) := by
  obtain ⟨⟨h, hh⟩, e⟩ := QuotientGroup.mk_out_eq_mul Γ x
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have e' : (QuotientGroup.mk x : Q).out = γ ^ j * x := e.trans (mul_comm _ _)
  change ∑' n : ℤ, f.val (γ ^ n * (QuotientGroup.mk x : Q).out) = _
  rw [e', ← (Equiv.addRight j).tsum_eq (fun n : ℤ ↦ f.val (γ ^ n * x))]
  refine tsum_congr fun n ↦ ?_
  change f.val (γ ^ n * (γ ^ j * x)) = f.val (γ ^ (n + j) * x)
  rw [zpow_add, mul_assoc]

/-- The orbit series of a two-sided decay function is summable. -/
private theorem modulatedPeriodization_summable (hc : 1 < (m γ).val) (f : E) (x : G) :
    Summable fun n : ℤ ↦ f.val (γ ^ n * x) := by
  obtain ⟨C₁, C₂, hb⟩ := modulatedExponentialDecay_exists_weight_bounds m f
  refine summable_of_zpow_bounds _ ((m γ).val : ℝ) ((m x).val : ℝ) C₁ C₂
    (by exact_mod_cast hc) (fun n ↦ ?_) (fun n ↦ ?_)
  · rw [← modulation_zpow_mul m γ]
    exact (hb _).1
  · rw [← modulation_zpow_mul m γ]
    exact (hb _).2
/-- Paper: Definition 4.4.2.1, p. 192. At every lift of a quotient point the
orbit series converges to the specified periodization. -/
theorem modulatedPeriodization_hasSum (f : E) (x : G) :
    HasSum (fun n : ℤ ↦ f.val (γ ^ n * x))
      (modulatedPeriodization m γ hm hms hγ f (QuotientGroup.mk x)) := by
  rw [modulatedPeriodization_apply_mk m γ hm hms hγ f x]
  exact (modulatedPeriodization_summable m γ hγ f x).hasSum
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
    Integrable (fun k : K ↦ (χ k.val : ℂ) * f.val (γ ^ n * (k.val * x))) μ₁ := by
  have hmem : f.val ∈ schwartzBruhatSubmodule G := by
    have h := (Submodule.mem_iInf _).mp f.property ⟨0, mem_univ 0⟩
    rwa [Submodule.mem_comap, modulationWeight_zero] at h
  have hf : Continuous f.val := schwartzBruhat_continuous (G := G) ⟨f.val, hmem⟩
  have : CompactSpace K :=
    isCompact_iff_compactSpace.mp (hm.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have hcont : Continuous (fun k : K ↦ (χ k.val : ℂ) * f.val (γ ^ n * (k.val * x))) :=
    (continuous_subtype_val.comp ((map_continuous χ).comp continuous_subtype_val)).mul
      (hf.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const)))
  exact hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The homogeneous periodization at the class of a point is the sum of the compact
averages over the orbit of that point. -/
private theorem modulatedIsotypicPeriodization_apply_mk (f : E) (x : G) :
    modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ f (QuotientGroup.mk x) =
      ∑' n : ℤ, weightedOrbit⟦f, n, x⟧ := by
  obtain ⟨⟨h, hh⟩, e⟩ := QuotientGroup.mk_out_eq_mul Γ x
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have e' : (QuotientGroup.mk x : Q).out = γ ^ j * x := e.trans (mul_comm _ _)
  change ∑' n : ℤ, weightedOrbit⟦f, n, (QuotientGroup.mk x : Q).out⟧ = _
  rw [e', ← (Equiv.addRight j).tsum_eq (fun n : ℤ ↦ weightedOrbit⟦f, n, x⟧)]
  refine tsum_congr fun n ↦ integral_congr_ae (.of_forall fun k ↦ ?_)
  change (χ k.val : ℂ) * f.val (γ ^ n * (k.val * (γ ^ j * x))) =
    (χ k.val : ℂ) * f.val (γ ^ (n + j) * (k.val * x))
  rw [zpow_add, mul_assoc, mul_left_comm (γ ^ j)]

/-- The series of the compact averages over an orbit is summable. -/
private theorem modulatedIsotypicPeriodization_summable (hprop : IsModulation m)
    (hc : 1 < (m γ).val) (f : E) (x : G) :
    Summable fun n : ℤ ↦ weightedOrbit⟦f, n, x⟧ := by
  obtain ⟨C₁, C₂, hb⟩ := modulatedExponentialDecay_exists_weight_bounds m f
  have : CompactSpace K :=
    isCompact_iff_compactSpace.mp (hprop.1.isCompact_preimage (isCompact_singleton (x := 1)))
  have hk (k : K) : ((m (k.val * x)).val : ℝ) = ((m x).val : ℝ) := by
    rw [map_mul m, show m k.val = 1 from MonoidHom.mem_ker.mp k.property, one_mul]
  have hbd (D : ℝ) (n : ℤ) (h : ∀ k : K, ‖f.val (γ ^ n * (k.val * x))‖ ≤ D) :
      ‖weightedOrbit⟦f, n, x⟧‖ ≤ D * μ₁.real univ :=
    norm_integral_le_of_norm_le_const (.of_forall fun k ↦ by
      rw [norm_mul, Circle.norm_coe, one_mul]
      exact h k)
  refine summable_of_zpow_bounds _ ((m γ).val : ℝ) ((m x).val : ℝ) (C₁ * μ₁.real univ)
    (C₂ * μ₁.real univ) (by exact_mod_cast hc) (fun n ↦ ?_) (fun n ↦ ?_)
  · refine (hbd (C₁ * (((m γ).val : ℝ) ^ n * ((m x).val : ℝ))⁻¹) n fun k ↦ ?_).trans_eq
      (by ring)
    rw [← hk k, ← modulation_zpow_mul m γ]
    exact (hb _).1
  · refine (hbd (C₂ * (((m γ).val : ℝ) ^ n * ((m x).val : ℝ))) n fun k ↦ ?_).trans_eq
      (by ring)
    rw [← hk k, ← modulation_zpow_mul m γ]
    exact (hb _).2
/-- Paper: Definition 4.4.2.1, p. 192. At every lift the orbit series of the
compact averages converges to the homogeneous periodization. -/
theorem modulatedIsotypicPeriodization_hasSum (f : E) (x : G) :
    HasSum (fun n : ℤ ↦ weightedOrbit⟦f, n, x⟧)
      (modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ f (QuotientGroup.mk x)) := by
  rw [modulatedIsotypicPeriodization_apply_mk m γ hm hms hγ μ₁ χ f x]
  exact (modulatedIsotypicPeriodization_summable m γ μ₁ χ hm hγ f x).hasSum
/-- Paper: Definition 4.4.2.1, p. 192. Left translation by a norm-one element
multiplies the homogeneous periodization by the character evaluated there. -/
theorem modulatedIsotypicPeriodization_homogeneous (f : E) (k : K) (z : Q) :
    let F := modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ f
    F (QuotientGroup.mk k.val⁻¹ * z) = (χ k.val : ℂ) * F z := by
  intro F
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have h1 : F (QuotientGroup.mk (k.val⁻¹ * x)) = ∑' n : ℤ, weightedOrbit⟦f, n, k.val⁻¹ * x⟧ :=
    modulatedIsotypicPeriodization_apply_mk m γ hm hms hγ μ₁ χ f _
  have h2 : F (QuotientGroup.mk x) = ∑' n : ℤ, weightedOrbit⟦f, n, x⟧ :=
    modulatedIsotypicPeriodization_apply_mk m γ hm hms hγ μ₁ χ f x
  rw [← QuotientGroup.mk_mul, h1, h2, ← tsum_mul_left]
  refine tsum_congr fun n ↦ ?_
  rw [← integral_const_mul, ← integral_mul_right_eq_self (μ := μ₁) _ k]
  refine integral_congr_ae (.of_forall fun k' ↦ ?_)
  change (χ (k' * k).val : ℂ) * f.val (γ ^ n * ((k' * k).val * (k.val⁻¹ * x))) =
    (χ k.val : ℂ) * ((χ k'.val : ℂ) * f.val (γ ^ n * (k'.val * x)))
  rw [Subgroup.coe_mul, map_mul χ, Circle.coe_mul, mul_assoc k'.val, mul_inv_cancel_left]
  ring
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
    CompactSpace Q := by
  have hpos (x : G) : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt (m x))
  have hproper : IsProperMap (fun x : G ↦ Real.log ((m x).val : ℝ)) := by
    let e : ℝ≥0ˣ ≃ₜ ℝ :=
      (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
    have he : (e ∘ m) = fun x : G ↦ Real.log ((m x).val : ℝ) :=
      funext fun g ↦ (Real.log_of_pos (hpos g)).symm
    exact he ▸ e.isProperMap.comp hm.1
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  have hC := hproper.isCompact_preimage (isCompact_Icc (a := (0 : ℝ)) (b := L))
  have himg :
      ((↑) : G → Q) '' ((fun x : G ↦ Real.log ((m x).val : ℝ)) ⁻¹' Icc 0 L) = univ := by
    refine eq_univ_of_forall fun z ↦ ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
    have h1 := (le_div_iff₀ hL).mp (Int.floor_le (Real.log ((m x).val : ℝ) / L))
    have h2 := (div_lt_iff₀ hL).mp (Int.lt_floor_add_one (Real.log ((m x).val : ℝ) / L))
    generalize ⌊Real.log ((m x).val : ℝ) / L⌋ = n at h1 h2
    rw [add_one_mul] at h2
    refine ⟨γ ^ (-n) * x, ?_, ?_⟩
    · have hlog : Real.log ((m (γ ^ (-n) * x)).val : ℝ) =
          Real.log ((m x).val : ℝ) - n * L := by
        rw [map_mul m, map_zpow m, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
          NNReal.coe_zpow, Real.log_mul (zpow_ne_zero _ (hpos γ).ne') (hpos x).ne',
          Real.log_zpow]
        push_cast
        ring
      change Real.log ((m (γ ^ (-n) * x)).val : ℝ) ∈ Icc 0 L
      rw [hlog]
      constructor <;> linarith
    · rw [QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem_zpowers γ _), one_mul]
  rw [← isCompact_univ_iff, ← himg]
  exact hC.image QuotientGroup.continuous_mk

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
    DiscreteTopology (lcaAnnihilator Γ) := by
  have := modulatedCyclicQuotient_compact m γ hm hγ
  obtain ⟨d, -⟩ := lcaQuotientDual_equiv_annihilator Γ (modulatedCyclicSubgroup_closed m γ hγ)
  exact d.toHomeomorph.discreteTopology_iff.mp inferInstance

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
          Real.log (t.val : ℝ)) : ℂ) := by
  have hlog : (logModule (τ t * k.val)) = Real.log (t.val : ℝ) := by
    rw [map_mul, hτ t, show m k.val = 1 from k.2, mul_one]
  change ((modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j (QuotientGroup.mk (τ t * k.val)) :
    Circle) : ℂ) = _
  rw [modulatedCyclicCharacter_mk, hlog, map_mul, hb, hk, sub_mul _ (b j.1), Circle.exp_sub,
    Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul]
  congr 1
  simp only [mul_inv, div_eq_mul_inv]
  ac_rfl

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
    a j f = (L * μ₁.real univ)⁻¹ * ∫ z, f z * star (e j z) ∂ν := by
  have := modulatedCyclicQuotient_compact m γ hm hγ
  refine ⟨?_, rfl⟩
  have hξ : Continuous (fun z : Q ↦ ((ξ j z : Circle) : ℂ)) :=
    continuous_subtype_val.comp (ξ j).continuous
  exact ((schwartzBruhat_continuous f).mul hξ.star).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

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
    ν univ = ENNReal.ofReal L * μ₁ univ := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  have : DiscreteTopology Γ := modulated_zpowers_discrete m γ hγ
  have hΓ : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_closed m γ hγ
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  have : (Measure.count : Measure Γ).Regular := count_regular_of_discreteTopology
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hφ : Continuous fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2 := by fun_prop
  -- The measure `μ` is a Haar measure: a multiple of the canonical one.
  let μ₀ : Measure K := Measure.haarMeasure ⊤
  have hcan := canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₀ Measure.haarMeasure_self
  have : (canonicalModulatedHaar m hm).IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have : SFinite (positiveRealHaar : Measure ℝ≥0ˣ) := by unfold positiveRealHaar; infer_instance
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have hscale := Measure.isMulLeftInvariant_eq_smul μ₁ μ₀
  set c := Measure.haarScalarFactor μ₁ μ₀
  have hc : (c : ℝ≥0∞) ≠ 0 := by
    intro h
    rw [ENNReal.coe_eq_zero] at h
    rw [h, zero_smul] at hscale
    exact NeZero.ne μ₁ hscale
  have hprod : μ₁.prod positiveRealHaar = c • μ₀.prod positiveRealHaar := by
    rw [← Measure.prod_smul_left, ← hscale]
  have hμc : μ = (c : ℝ≥0∞) • canonicalModulatedHaar m hm := by
    rw [hμ, hprod, Measure.map_smul _ hφ.aemeasurable, hcan, ENNReal.smul_def]
  have : μ.IsHaarMeasure := hμc ▸ Measure.IsHaarMeasure.smul _ hc ENNReal.coe_ne_top
  have : μ.Regular := by
    let μH : Measure G := Measure.haarMeasure (Classical.arbitrary _)
    rw [Measure.isMulLeftInvariant_eq_smul μ μH]
    exact Measure.Regular.smul ENNReal.coe_ne_top
  -- A Borel fundamental domain for the cyclic subgroup.
  let ℓ : G → ℝ := fun x ↦ Real.log ((m x).val : ℝ)
  have hpos (x : G) : (0 : ℝ) < (m x).val := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hℓ (x : G) (k : ℤ) : ℓ (x * γ ^ k) = ℓ x + k * L := by
    simp only [ℓ, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
      NNReal.coe_zpow, Real.log_mul (hpos x).ne' (zpow_pos (hpos γ) k).ne', Real.log_zpow]
  let Δ : Set G := {x | ((m x).val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)}
  have hmemΔ (x : G) : x ∈ Δ ↔ ℓ x ∈ Ico 0 L := by
    change ((m x).val : ℝ) ∈ Ico 1 ((m γ).val : ℝ) ↔ _
    simp only [mem_Ico, ℓ, Real.log_nonneg_iff (hpos x), Real.log_lt_log_iff (hpos x) (hpos γ)]
  have hcontm : Continuous fun x : G ↦ ((m x).val : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hΔ : MeasurableSet Δ := hcontm.measurable measurableSet_Ico
  have hbij : Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : Q)) := by
    constructor
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (QuotientGroup.eq.mp hxy)
      have hyx : y = x * γ ^ k := by rw [hk, mul_inv_cancel_left]
      have hx' := (hmemΔ x).mp hx
      have hy' := (hmemΔ y).mp hy
      rw [hyx, hℓ] at hy'
      have h1 : (k : ℝ) < 1 := by
        by_contra h
        nlinarith [hx'.1, hy'.2]
      have h2 : (-1 : ℝ) < k := by
        by_contra h
        nlinarith [hx'.2, hy'.1]
      have hk0 : k = 0 := by
        have : k < 1 := by exact_mod_cast h1
        have : -1 < k := by exact_mod_cast h2
        omega
      exact Subtype.ext (show x = y by rw [hyx, hk0, zpow_zero, mul_one])
    · intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      let k : ℤ := -⌊ℓ x / L⌋
      refine ⟨⟨x * γ ^ k, (hmemΔ _).mpr ?_⟩, ?_⟩
      · rw [hℓ]
        have hf := Int.floor_le (ℓ x / L)
        have hf' := Int.lt_floor_add_one (ℓ x / L)
        rw [le_div_iff₀ hL] at hf
        rw [div_lt_iff₀ hL] at hf'
        constructor
        · simp only [k, Int.cast_neg]; nlinarith
        · simp only [k, Int.cast_neg]; nlinarith
      · exact QuotientGroup.mk_mul_of_mem x (Subgroup.zpow_mem_zpowers γ k)
  -- The mass of the fundamental domain.
  have hPR : positiveRealHaar {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)} =
      ENNReal.ofReal L := by
    let ex (x : ℝ) := Units.mk0 (Real.exp x).toNNReal (by positivity)
    have he : Measurable ex :=
      measurable_comap_iff.mpr (continuous_real_toNNReal.comp Real.continuous_exp).measurable
    have hset : MeasurableSet {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)} :=
      measurableSet_Ico.preimage
        (NNReal.continuous_coe.measurable.comp MeasurableSpace.le_map_comap)
    change (volume.map ex) _ = _
    rw [Measure.map_apply he hset]
    have hpre : ex ⁻¹' {t | (t.val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)} = Ico 0 L := by
      ext x
      change (1 ≤ ((Real.exp x).toNNReal : ℝ) ∧ ((Real.exp x).toNNReal : ℝ) < _) ↔ _
      rw [Real.coe_toNNReal _ (Real.exp_pos x).le, Real.one_le_exp_iff,
        ← Real.lt_log_iff_exp_lt (hpos γ)]
      rfl
    rw [hpre, Real.volume_Ico, sub_zero]
  have hμΔ : μ Δ = μ₁ univ * ENNReal.ofReal L := by
    rw [hμ, Measure.map_apply hφ.measurable hΔ]
    have hpre : (fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2) ⁻¹' Δ =
        univ ×ˢ {t : ℝ≥0ˣ | (t.val : ℝ) ∈ Ico 1 ((m γ).val : ℝ)} := by
      ext ⟨k, t⟩
      have hk : m (k : G) = 1 := k.property
      change ((m ((k : G) * τ t)).val : ℝ) ∈ Ico 1 ((m γ).val : ℝ) ↔ _
      rw [map_mul, hk, one_mul, hτ t]
      simp
    rw [hpre, Measure.prod_prod, hPR]
  -- Weil's formula for the constant function one.
  have hΔfin : μ Δ ≠ ∞ := by
    rw [hμΔ]
    exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hint : Integrable (fun _ : Q ↦ (1 : ℂ)) ν := by
    rw [weilFundamentalDomain_integrable_iff Γ hΓ μ hΔ hbij ν hν]
    exact (integrable_indicator_iff hΔ).mpr (integrableOn_const hΔfin)
  have heq := weilFundamentalDomain_integral Γ hΓ μ hΔ hbij ν hν hint
  have hνfin : ν univ ≠ ∞ := by
    have := (integrable_const_iff.mp hint).resolve_left one_ne_zero
    exact measure_ne_top ν univ
  simp only [integral_const, measureReal_restrict_apply_univ, Complex.real_smul, mul_one,
    Complex.ofReal_inj] at heq
  have hreal : ν.real univ = μ.real Δ := heq
  rw [← ENNReal.ofReal_toReal hνfin, ← measureReal_def, hreal, measureReal_def,
    ENNReal.ofReal_toReal hΔfin, hμΔ, mul_comm]

include hm hγ hτ hμ hν in
/-- Paper: Remark 4.4.2.7, p. 194. Dividing the quotient Haar measure by its
specified total mass gives the probability Haar measure. -/
theorem modulatedCyclicQuotient_probabilityHaar :
    IsProbabilityMeasure ((ENNReal.ofReal L * μ₁ univ)⁻¹ • ν) := by
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have h0 : ENNReal.ofReal L * μ₁ univ ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.mpr hL).ne' (Measure.measure_univ_ne_zero.mpr (NeZero.ne μ₁))
  have htop : ENNReal.ofReal L * μ₁ univ ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top μ₁ univ)
  constructor
  rw [smul_apply, smul_eq_mul,
    modulatedCyclicQuotient_measure_univ m γ hm hγ μ₁ ν τ hτ μ hμ hν,
    ENNReal.inv_mul_cancel h0 htop]

include hms hτ hμ hν in
/-- Paper: Remark 4.4.2.7, p. 194. Normalizing the norm-one Haar measure to
mass one gives the same Weil quotient measure as dividing by that mass
after taking the quotient. -/
theorem modulatedCyclicQuotient_canonicalHaar :
    IsWeilQuotientMeasure Γ (canonicalModulatedHaar m hm) Measure.count ((μ₁ univ)⁻¹ • ν) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite (positiveRealHaar : Measure ℝ≥0ˣ) := by unfold positiveRealHaar; infer_instance
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  have hφ : Continuous fun z : K × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2 := by fun_prop
  -- The canonical measure is `μ` divided by the mass of the norm-one group.
  let μ₀ : Measure K := Measure.haarMeasure ⊤
  have hμ₀ : μ₀ univ = 1 := Measure.haarMeasure_self
  have hcan := canonicalModulatedHaar_eq_map_prod m hm τ hτ μ₀ hμ₀
  have hscale := Measure.isMulLeftInvariant_eq_smul μ₁ μ₀
  set c := Measure.haarScalarFactor μ₁ μ₀
  have hc : μ₁ univ = c := by
    conv_lhs => rw [hscale]
    rw [smul_apply, hμ₀, ENNReal.smul_def, smul_eq_mul, mul_one]
  have h0 : μ₁ univ ≠ 0 := Measure.measure_univ_ne_zero.mpr (NeZero.ne μ₁)
  have htop : μ₁ univ ≠ ∞ := measure_ne_top μ₁ univ
  have hprod : μ₁.prod positiveRealHaar = c • μ₀.prod positiveRealHaar := by
    rw [← Measure.prod_smul_left, ← hscale]
  have hμc : μ = μ₁ univ • canonicalModulatedHaar m hm := by
    rw [hμ, hprod, Measure.map_smul _ hφ.aemeasurable, hcan, ENNReal.smul_def, hc]
  have hcanμ : canonicalModulatedHaar m hm = (μ₁ univ)⁻¹ • μ := by
    rw [hμc, smul_smul, ENNReal.inv_mul_cancel h0 htop, one_smul]
  -- Rescale both sides of Weil's formula.
  obtain ⟨hνH, hνR, hW⟩ := hν
  refine ⟨Measure.IsHaarMeasure.smul _ (ENNReal.inv_ne_zero.mpr htop)
      (ENNReal.inv_ne_top.mpr h0), Measure.Regular.smul (ENNReal.inv_ne_top.mpr h0),
    fun f hf ↦ ?_⟩
  rw [hcanμ, integral_smul_measure, integral_smul_measure, hW f hf]

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
