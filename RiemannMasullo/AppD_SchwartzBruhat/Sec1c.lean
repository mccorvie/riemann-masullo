module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1b
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Differential operators, Poisson summation, supports and translations

Masullo, §§D.1.6–D.1.9, pp. 765–783.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology
open scoped TensorProduct Topology

namespace RiemannMasullo

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

section DifferentialOperators

/-- Paper: Definition D.1.6.1, p. 765. The topological Lie algebra is the
space of continuous one-parameter subgroups with the compact-open topology. -/
abbrev LCATopologicalLie (G : Type*) [Group G] [TopologicalSpace G] :=
  Multiplicative ℝ →ₜ* G

/-- Paper: Definition D.1.6.1, p. 765. Each one-parameter subgroup of the real
line is scalar multiplication by its value at time one.
Deviation: Sanity check on the additive real line. -/
theorem lcaTopologicalLie_real (a : LCATopologicalLie (Multiplicative ℝ)) (t : ℝ) :
    (a (Multiplicative.ofAdd t)).toAdd =
      t * (a (Multiplicative.ofAdd 1)).toAdd := by
  let f : ℝ →+ ℝ := AddMonoidHom.toMultiplicative.symm a.toMonoidHom
  have hf : Continuous f := a.continuous
  change f t = t * f 1
  simpa only [smul_eq_mul, mul_one] using map_real_smul f hf t (1 : ℝ)

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

-- TODO(paper-gap): D.1.6.4 claims local compactness of the compact-open hom groups.
-- For the countable product of circles the one-parameter subgroup space is ℝ^ℕ.

omit hT2 in
/-- If evaluation identifies `G` with its Pontryagin bidual, transposing character
evaluation gives the inverse to dualizing one-parameter subgroups. -/
theorem lcaTopologicalLie_dual_of_bidual
    (eG : G ≃ₜ* PontryaginDual (PontryaginDual G))
    (heG : ∀ x χ, eG x χ = χ x) :
    ∃ e : LCATopologicalLie G ≃ₜ*
        (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)),
      ∀ a, e a = PontryaginDual.map a := by
  let evalReal := pontryaginDual_eval (G := Multiplicative ℝ)
  let eGinv : PontryaginDual (PontryaginDual G) →ₜ* G := eG.symm
  let dual := PontryaginDual.mapHom (Multiplicative ℝ) G
  let inverse (b : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)) :
      LCATopologicalLie G :=
    eGinv.comp ((PontryaginDual.map b).comp evalReal)
  have hEval (b : PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ))
      (t : Multiplicative ℝ) (χ : PontryaginDual G) : χ (inverse b t) = b χ t := by
    calc
      χ (inverse b t) = eG (inverse b t) χ := (heG _ _).symm
      _ = evalReal t (b χ) := by
        change eG (eG.symm (PontryaginDual.map b (evalReal t))) χ = _
        rw [eG.apply_symm_apply, PontryaginDual.map_apply]
      _ = b χ t := rfl
  have hLeft : Function.LeftInverse inverse dual := by
    intro a
    apply ContinuousMonoidHom.ext
    intro t
    apply eG.injective
    apply PontryaginDual.ext
    intro χ
    rw [heG, heG, hEval (dual a)]
    rfl
  have hRight : Function.RightInverse inverse dual :=
    fun b ↦ ContinuousMonoidHom.ext fun χ ↦ PontryaginDual.ext fun t ↦ hEval b t χ
  have hCont : Continuous inverse :=
    eGinv.continuous_comp_right.comp
      (evalReal.continuous_comp_left.comp
        (PontryaginDual.mapHom (PontryaginDual G) (PontryaginDual (Multiplicative ℝ))).continuous)
  exact ⟨{ toFun := dual
           invFun := inverse
           left_inv := hLeft
           right_inv := hRight
           map_mul' := map_mul dual
           continuous_toFun := dual.continuous
           continuous_invFun := hCont }, fun _ ↦ rfl⟩

/-- Paper: Lemma D.1.6.4, p. 766. Precomposition of characters with a
one-parameter subgroup gives the canonical compact-open topological group isomorphism.
Deviation: The local compactness assertion fails for an infinite product of circles. -/
theorem lcaTopologicalLie_dual :
    ∃ e : LCATopologicalLie G ≃ₜ*
        (PontryaginDual G →ₜ* PontryaginDual (Multiplicative ℝ)),
      ∀ a, e a = PontryaginDual.map a := by
  obtain ⟨eG, heG⟩ := pontryaginDual_bidual (G := G)
  exact lcaTopologicalLie_dual_of_bidual eG heG

/-- Paper: Definition D.1.6.5, p. 766. Differentiate the orbit curve of a
function along a one-parameter subgroup at time zero. -/
def bruhatDirectionalDeriv (a : LCATopologicalLie G) (f : G → ℂ) (x : G) : ℂ :=
  deriv (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t))) 0

omit hTop hT2 hLC in
/-- Paper: Definition D.1.6.5, p. 766. Differentiation along the identity
one-parameter subgroup of the real line recovers the ordinary derivative.
Deviation: Sanity check on the additive real line. -/
theorem bruhatDirectionalDeriv_real
    (a : LCATopologicalLie (Multiplicative ℝ))
    (ha : ∀ t, a (Multiplicative.ofAdd t) = Multiplicative.ofAdd t)
    (f : Multiplicative ℝ → ℂ) (x : ℝ) :
    bruhatDirectionalDeriv a f (Multiplicative.ofAdd x) =
      deriv (f ∘ Multiplicative.ofAdd) x := by sorry

/-- Paper: Definition D.1.6.5, p. 766. For a Bruhat C¹ function the orbit
derivative exists at time zero for every starting point. -/
theorem hasDerivAt_bruhatDirectionalDeriv (a : LCATopologicalLie G) {f : G → ℂ}
    (hf : IsBruhatContDiff 1 f) (x : G) :
    HasDerivAt (fun t : ℝ ↦ f (x * a (Multiplicative.ofAdd t)))
      (bruhatDirectionalDeriv a f x) 0 := by sorry

-- TODO(paper-gap): The proofs of D.1.6.6 and D.1.6.7 use support in an open
-- compactly generated subgroup. A global smooth function need not have such support.

/-- Paper: Lemma D.1.6.6, p. 767. A first derivative of a Bruhat C¹ function
is continuous. -/
theorem bruhatDirectionalDeriv_continuous (a : LCATopologicalLie G) {f : G → ℂ}
    (hf : IsBruhatContDiff 1 f) :
    Continuous (bruhatDirectionalDeriv a f) := by sorry

/-- Paper: Lemma D.1.6.6, p. 767. The first derivative of a Bruhat smooth
function is Bruhat smooth. -/
theorem bruhatDirectionalDeriv_mem_smooth (a : LCATopologicalLie G)
    (f : bruhatSmoothSubmodule (G := G)) :
    bruhatDirectionalDeriv a f ∈ bruhatSmoothSubmodule := by sorry

/-- Paper: Lemma D.1.6.6, p. 767. The first derivative satisfies the product
rule on pairs of Bruhat C¹ functions. -/
theorem bruhatDirectionalDeriv_mul (a : LCATopologicalLie G) {f g : G → ℂ}
    (hf : IsBruhatContDiff 1 f) (hg : IsBruhatContDiff 1 g) :
    bruhatDirectionalDeriv a (f * g) =
      f * bruhatDirectionalDeriv a g + g * bruhatDirectionalDeriv a f := by sorry

/-- Paper: Definition D.1.6.5, p. 766. The orbit derivative is additive on
Bruhat C¹ functions. -/
theorem bruhatDirectionalDeriv_add (a : LCATopologicalLie G)
    (f g : bruhatContDiffSubmodule (G := G) 1) :
    bruhatDirectionalDeriv a (f + g : bruhatContDiffSubmodule 1) =
      bruhatDirectionalDeriv a f + bruhatDirectionalDeriv a g := by sorry

/-- Paper: Definition D.1.6.5, p. 766. The orbit derivative commutes with
complex scalar multiplication on Bruhat C¹ functions. -/
theorem bruhatDirectionalDeriv_smul (a : LCATopologicalLie G)
    (f : bruhatContDiffSubmodule (G := G) 1) (c : ℂ) :
    bruhatDirectionalDeriv a (c • f : bruhatContDiffSubmodule 1) =
      c • bruhatDirectionalDeriv a f := by sorry

/-- Paper: Definition D.1.6.5, p. 766. Orbit differentiation is a complex
linear map from Bruhat C¹ functions to continuous functions. -/
def bruhatDirectionalDerivLinear (a : LCATopologicalLie G) :
    bruhatContDiffSubmodule (G := G) 1 →ₗ[ℂ] C(G, ℂ) where
  toFun f := ⟨bruhatDirectionalDeriv a f,
    bruhatDirectionalDeriv_continuous a ((mem_bruhatContDiffSubmodule_iff 1 f.val).mp f.property)⟩
  map_add' f g := ContinuousMap.ext (congrFun (bruhatDirectionalDeriv_add a f g))
  map_smul' c f := ContinuousMap.ext (congrFun (bruhatDirectionalDeriv_smul a f c))

/-- Paper: Definition D.1.6.5, p. 766. Evaluation of the bundled map agrees
with the derivative of the orbit curve. -/
theorem bruhatDirectionalDerivLinear_apply (a : LCATopologicalLie G)
    (f : bruhatContDiffSubmodule (G := G) 1) (x : G) :
    bruhatDirectionalDerivLinear a f x = bruhatDirectionalDeriv a f x := by sorry

/-- Paper: Lemma D.1.6.7(1), p. 767. The first-order operator is the complex
linear directional derivative acting on the smooth submodule. -/
def bruhatFirstOrder (a : LCATopologicalLie G) :
    Module.End ℂ (bruhatSmoothSubmodule (G := G)) where
  toFun f := ⟨bruhatDirectionalDeriv a f, bruhatDirectionalDeriv_mem_smooth a f⟩
  map_add' f g := Subtype.ext
    (bruhatDirectionalDeriv_add a ⟨f, (Submodule.mem_iInf _).mp f.property 1⟩
      ⟨g, (Submodule.mem_iInf _).mp g.property 1⟩)
  map_smul' c f := Subtype.ext
    (bruhatDirectionalDeriv_smul a ⟨f, (Submodule.mem_iInf _).mp f.property 1⟩ c)

/-- Paper: Lemma D.1.6.7(1), p. 767. Evaluation of the first-order operator
gives the orbit derivative. -/
theorem bruhatFirstOrder_apply (a : LCATopologicalLie G)
    (f : bruhatSmoothSubmodule (G := G)) (x : G) :
    (bruhatFirstOrder a f : G → ℂ) x = bruhatDirectionalDeriv a f x := by sorry

/-- Paper: Lemma D.1.6.7(1), p. 767. The directional derivative commutes
with left translations. -/
theorem bruhatFirstOrder_translate (a : LCATopologicalLie G)
    (f : bruhatSmoothSubmodule (G := G)) (g : G) :
    ∃ f' : bruhatSmoothSubmodule (G := G),
      (∀ x : G, f'.val x = f.val (g⁻¹ * x)) ∧
      ∀ x : G, (bruhatFirstOrder a f').val x = (bruhatFirstOrder a f).val (g⁻¹ * x) := by sorry

/-- Paper: Lemma D.1.6.7(1), p. 767. First-order operators add under
pointwise multiplication of one-parameter subgroups. -/
theorem bruhatFirstOrder_mul (a b : LCATopologicalLie G) :
    bruhatFirstOrder (a * b) = bruhatFirstOrder a + bruhatFirstOrder b := by sorry

/-- Paper: Lemma D.1.6.7(1), p. 767. Scaling the real parameter scales
the first-order operator by the same factor. -/
theorem bruhatFirstOrder_scale (a : LCATopologicalLie G) (c : ℝ) :
    let scale : LCATopologicalLie (Multiplicative ℝ) :=
      ⟨(c • LinearMap.id (R := ℝ) (M := ℝ)).toAddMonoidHom.toMultiplicative,
        continuous_const_mul c⟩
    bruhatFirstOrder (a.comp scale) = c • bruhatFirstOrder a := by sorry

/-- Paper: Lemma D.1.6.7(1), p. 767. The directional derivative restricts
to a continuous complex linear endomorphism of the Schwartz–Bruhat space. -/
theorem bruhatFirstOrder_schwartz :
    ∀ a : LCATopologicalLie G, ∃ A : SchwartzBruhat G →L[ℂ] SchwartzBruhat G,
      ∀ f x, A f x = bruhatDirectionalDeriv a f x := by sorry

/-- Paper: Lemma D.1.6.7(2), p. 767. First-order operators commute on the
smooth submodule. -/
theorem bruhatFirstOrder_commute (a b : LCATopologicalLie G) :
    Commute (bruhatFirstOrder a) (bruhatFirstOrder b) := by sorry

/-- Paper: Definition D.1.6.8(1), p. 768. Invariant differential operators
form the unital complex subalgebra generated by the first-order operators. -/
def bruhatDiffAlgebra (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] :
    Subalgebra ℂ (Module.End ℂ (bruhatSmoothSubmodule (G := G))) :=
  Algebra.adjoin ℂ (range (bruhatFirstOrder (G := G)))

/-- Paper: Definition D.1.6.8(1), p. 768. The invariant differential operator
algebra is commutative. -/
theorem bruhatDiffAlgebra_commute (D E : bruhatDiffAlgebra G) : Commute D E := by sorry

/-- Paper: Definition D.1.6.8(1), p. 768. The first-order generator belongs to
the differential operator algebra. -/
def bruhatDiffGenerator (a : LCATopologicalLie G) : bruhatDiffAlgebra G :=
  ⟨bruhatFirstOrder a, Algebra.subset_adjoin ⟨a, rfl⟩⟩

/-- Paper: Definition D.1.6.8(1), p. 768. The complex degree-one space is
the complex span of the first-order generators inside the differential operator algebra. -/
def bruhatDiffDegreeOne : Submodule ℂ (bruhatDiffAlgebra G) :=
  Submodule.span ℂ (range (bruhatDiffGenerator (G := G)))

/-- Paper: Definition D.1.6.8(1), p. 768. The real degree-one space is the
real span of first-order operators.
Deviation: This span is taken inside the ambient endomorphism algebra, where every
element of the span belongs to the differential operator algebra. -/
def bruhatDiffDegreeOneReal : Submodule ℝ (Module.End ℂ (bruhatSmoothSubmodule (G := G))) :=
  Submodule.span ℝ (range (bruhatFirstOrder (G := G)))

/-- Paper: Definition D.1.6.8(1), p. 768. The complex first-order space
contains each generator and excludes the identity operator.
Deviation: Sanity check distinguishing the span from the unital algebra. -/
theorem bruhatDiffDegreeOne_sanity (a : LCATopologicalLie G) :
    bruhatDiffGenerator a ∈ bruhatDiffDegreeOne ∧
      (1 : bruhatDiffAlgebra G) ∉ bruhatDiffDegreeOne := by sorry

/-- Paper: Definition D.1.6.8(1), p. 768. The real degree-one space consists
of individual first-order operators, by real linearity in the direction. -/
theorem mem_bruhatDiffDegreeOneReal_iff
    (D : Module.End ℂ (bruhatSmoothSubmodule (G := G))) :
    D ∈ bruhatDiffDegreeOneReal ↔ ∃ a : LCATopologicalLie G, D = bruhatFirstOrder a := by sorry

/-- Paper: Definition D.1.6.8(2), p. 768. A word acts by applying its first
letter first and its last letter last. -/
def bruhatDiffWord (w : List (LCATopologicalLie G)) : bruhatDiffAlgebra G :=
  (w.reverse.map bruhatDiffGenerator).prod

/-- Paper: Definition D.1.6.8(2), p. 768. A one-letter word evaluates to its
first-order generator. -/
theorem bruhatDiffWord_singleton (a : LCATopologicalLie G) :
    bruhatDiffWord [a] = bruhatDiffGenerator a := by sorry

/-- Paper: Definition D.1.6.8(2), p. 768. Each operator has a presentation
as a finite linear combination of words in the first-order generators. -/
theorem bruhatDiff_exists_presentation (D : bruhatDiffAlgebra G) :
    ∃ c : List (LCATopologicalLie G) →₀ ℂ, c.sum (fun w z ↦ z • bruhatDiffWord w) = D := by sorry

/-- Paper: Definition D.1.6.8(2), p. 768. The degree is the smallest possible
maximum word length among finite presentations of the operator.
Deviation: Finset supremum sets the empty presentation's length to zero. -/
def bruhatDiffDegree (D : bruhatDiffAlgebra G) : ℕ :=
  sInf {n : ℕ | ∃ c : List (LCATopologicalLie G) →₀ ℂ,
    c.sum (fun w z ↦ z • bruhatDiffWord w) = D ∧ n = c.support.sup List.length}

/-- Paper: Remark D.1.6.9, p. 768. A nontrivial one-parameter subgroup
gives a differential operator of degree one. -/
theorem bruhatDiffDegree_generator (a : LCATopologicalLie G) (ha : a ≠ 1) :
    bruhatDiffDegree (bruhatDiffGenerator a) = 1 := by sorry

/-- Paper: Remark D.1.6.11, p. 768. A character gives a Bruhat smooth
function via its circle-valued character map.
Deviation: The global differentiability definition in §D.1.5 allows any
good subgroup in the kernel, so the symbol can use the character itself. -/
theorem pontryaginDual_mem_bruhatSmooth (χ : PontryaginDual G) :
    (fun x : G ↦ (χ x : ℂ)) ∈ bruhatSmoothSubmodule := by sorry

/-- Paper: Definition D.1.6.10, p. 768. The symbol evaluates the differential
operator applied to a character at the group identity. -/
def bruhatDiffSymbol (D : bruhatDiffAlgebra G) (χ : PontryaginDual G) : ℂ :=
  (D.val ⟨fun x : G ↦ (χ x : ℂ), pontryaginDual_mem_bruhatSmooth χ⟩).val 1

/-- Paper: Definition D.1.6.10, p. 768. The identity operator has constant
symbol one.
Deviation: Sanity check on the normalization of the symbol. -/
theorem bruhatDiffSymbol_one (χ : PontryaginDual G) :
    bruhatDiffSymbol (1 : bruhatDiffAlgebra G) χ = 1 := by sorry

omit hTop hT2 hLC in
/-- Paper: Example D.1.6.12, p. 768. On the real line, the symbol of the
ordinary derivative at the character of frequency ξ is 2πiξ. -/
theorem bruhatDiffSymbol_real (ξ : ℝ) (χ : PontryaginDual (Multiplicative ℝ))
    (hχ : ∀ x : ℝ, χ (Multiplicative.ofAdd x) = Real.fourierChar (ξ * x)) :
    bruhatDiffSymbol (bruhatDiffGenerator (ContinuousMonoidHom.id (Multiplicative ℝ))) χ =
      2 * ↑Real.pi * Complex.I * (ξ : ℂ) := by sorry

/-- Paper: Lemma D.1.6.13, p. 769. A character is an eigenfunction of a word
of first derivatives, with eigenvalue the product of the individual symbols. -/
theorem bruhatDiffWord_character (w : List (LCATopologicalLie G))
    (χ : PontryaginDual G) (x : G) :
    ((bruhatDiffWord w).val ⟨_, pontryaginDual_mem_bruhatSmooth χ⟩).val x =
      (w.map (fun a ↦ bruhatDiffSymbol (bruhatDiffGenerator a) χ)).prod * (χ x : ℂ) :=
  by sorry

/-- Paper: Lemma D.1.6.13, p. 769. The symbol of a word is the product
of its first-order symbols. -/
theorem bruhatDiffSymbol_word (w : List (LCATopologicalLie G)) (χ : PontryaginDual G) :
    bruhatDiffSymbol (bruhatDiffWord w) χ =
      (w.map (fun a ↦ bruhatDiffSymbol (bruhatDiffGenerator a) χ)).prod := by sorry

/-- Paper: Lemma D.1.6.13, p. 769. The symbol is invariant under every
compact subgroup of the dual. -/
theorem bruhatDiffSymbol_compact_invariant (D : bruhatDiffAlgebra G)
    (K : Subgroup (PontryaginDual G)) (hK : IsCompact (K : Set (PontryaginDual G)))
    (χ : PontryaginDual G) (k : K) :
    bruhatDiffSymbol D (χ * k.val) = bruhatDiffSymbol D χ := by sorry

/-- Paper: Lemma D.1.6.14, p. 769. Real first-order operators correspond
bijectively and real-linearly to continuous real-valued homomorphisms on the dual.
The exponential formula is the commutativity of the diagram on characters.
Deviation: Real linearity is expressed by the pointwise laws on the target. -/
theorem bruhatDiffDegreeOne_frequency :
    ∃ σ : bruhatDiffDegreeOneReal (G := G) ≃ (PontryaginDual G →ₜ* Multiplicative ℝ),
      (∀ D E χ, (σ (D + E) χ).toAdd = (σ D χ).toAdd + (σ E χ).toAdd) ∧
      (∀ (c : ℝ) D χ, (σ (c • D) χ).toAdd = c * (σ D χ).toAdd) ∧
      ∀ (a : LCATopologicalLie G) (D : bruhatDiffDegreeOneReal (G := G)),
        D.val = bruhatFirstOrder a → ∀ χ (t : ℝ),
          Real.fourierChar ((σ D χ).toAdd * t) = χ (a (Multiplicative.ofAdd t)) :=
  by sorry

/-- Paper: Corollary D.1.6.15, p. 770. The first-order symbol is the real
frequency multiplied by 2πi. The frequency is identified by the character pairing. -/
theorem bruhatDiffSymbol_generator (a : LCATopologicalLie G) (χ : PontryaginDual G)
    (r : ℝ) (hr : ∀ t : ℝ, Real.fourierChar (r * t) = χ (a (Multiplicative.ofAdd t))) :
    bruhatDiffSymbol (bruhatDiffGenerator a) χ = 2 * ↑Real.pi * Complex.I * (r : ℂ) :=
  by sorry

/-- Paper: Lemma D.1.6.16, p. 770. On an elementary group a smooth function
is Schwartz exactly when each symbol times each differentiated function is
continuous and globally bounded. The dual symbols are evaluated through biduality. -/
theorem mem_schwartzBruhat_iff_bruhatDiff_bounded (e : ElementaryLCAPresentation G)
    (b : G ≃ₜ* PontryaginDual (PontryaginDual G)) (hb : ∀ x χ, b x χ = χ x)
    (f : bruhatSmoothSubmodule (G := G)) :
    (f : G → ℂ) ∈ schwartzBruhatSubmodule G ↔
      ∀ (D : bruhatDiffAlgebra G) (E : bruhatDiffAlgebra (PontryaginDual G)),
        Continuous (fun x ↦ bruhatDiffSymbol E (b x) * (D.val f).val x) ∧
        ∃ C : ℝ, ∀ x, ‖bruhatDiffSymbol E (b x) * (D.val f).val x‖ ≤ C := by sorry

end DifferentialOperators

section AveragingAndFourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

variable (K : Subgroup G)

section CompactAveraging

local instance sec1cCompactSubgroupMeasurableSpace : MeasurableSpace K := borel _

/-- Paper: Lemma D.1.6.18, p. 772. Normalized Haar averaging over a compact
subgroup of an elementary group gives a continuous surjection of Schwartz spaces. -/
theorem elementary_schwartzBruhat_average (e : ElementaryLCAPresentation G)
    (hK : IsCompact (K : Set G)) (μK : Measure K) [μK.IsHaarMeasure] [IsProbabilityMeasure μK] :
    ∃ P : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ K),
      (∀ (f : SchwartzBruhat G) (x : G),
        Integrable (fun k : K ↦ f (x * k.val)) μK ∧
        P f (QuotientGroup.mk x) = ∫ k : K, f (x * k.val) ∂μK) ∧
      Function.Surjective P := by sorry

end CompactAveraging

variable [MeasurableSpace G] [hBorel : BorelSpace G]

local instance sec1cDualMeasurableSpace : MeasurableSpace (PontryaginDual G) := borel _
local instance sec1cQuotientMeasurableSpace : MeasurableSpace (G ⧸ K) := borel _
local instance sec1cQuotientDualMeasurableSpace :
    MeasurableSpace (PontryaginDual (G ⧸ K)) := borel _

variable (μ : Measure G) [hHaar : μ.IsHaarMeasure] [hRegular : μ.Regular]

include hBorel hHaar hRegular

/-- Paper: Lemma D.1.6.19(1), p. 773. An invariant differential operator
preserves Schwartz–Bruhat functions, and on the Fourier side it acts by
multiplication by its symbol. Both integrals are defined on integrable functions. -/
theorem lcaFourier_bruhatDiff (D : bruhatDiffAlgebra G) (f : SchwartzBruhat G) :
    ∃ (hf : (f : G → ℂ) ∈ bruhatSmoothSubmodule)
      (g : SchwartzBruhat G), (g : G → ℂ) = (D.val ⟨f, hf⟩).val ∧
      Integrable (f : G → ℂ) μ ∧ Integrable (g : G → ℂ) μ ∧
      lcaFourier μ g = bruhatDiffSymbol D * lcaFourier μ f := by sorry

/-- Paper: Lemma D.1.6.19(2), p. 773. The Fourier integral gives a continuous
linear isomorphism of the two Schwartz–Bruhat spaces. -/
theorem schwartzBruhat_fourier_equiv :
    ∃ F : SchwartzBruhat G ≃L[ℂ] SchwartzBruhat (PontryaginDual G),
      ∀ f : SchwartzBruhat G, Integrable (f : G → ℂ) μ ∧
        ∀ χ, F f χ = lcaFourier μ f χ := by sorry

-- TODO(paper-gap): (D.1.6.25) has different domains on its two sides. Its right side
-- is an inverse transform on G, whereas the left side is a Fourier transform on the dual.
-- The direction of the Fourier transform on the right in (D.1.6.26) is also reversed.
-- The footnotes on pp. 771, 773 and 775 leave the measure comparison to be checked.

/-- Paper: Lemma D.1.6.19(3), p. 773. Normalized structural averaging and
extension by zero intertwine with Fourier transform at the dual structural pair.
Deviation: This is the projector identity described after (D.1.6.26), with the
forward transform on both paths and both compact averages taken with mass one.
The ill-typed inverse-transform formula (D.1.6.25) is left open. -/
theorem lcaFourier_structural_projectors (a : BruhatStructuralPair G)
    (μK : Measure ↥(OrderDual.ofDual a.val.2))
    [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (νJ : Measure (lcaAnnihilator a.val.1))
    [νJ.IsHaarMeasure] [IsProbabilityMeasure νJ]
    (f : SchwartzBruhat G) :
    let avg := (a.val.1 : Set G).indicator
      (fun x ↦ ∫ k : ↥(OrderDual.ofDual a.val.2), f (x * k.val) ∂μK)
    Integrable (f : G → ℂ) μ ∧ Integrable avg μ ∧
      (∀ x : G, Integrable (fun k : ↥(OrderDual.ofDual a.val.2) ↦ f (x * k.val)) μK) ∧
      (∀ χ : PontryaginDual G,
        Integrable (fun ψ : lcaAnnihilator a.val.1 ↦ lcaFourier μ f (χ * ψ.val)) νJ) ∧
      lcaFourier μ avg =
        (lcaAnnihilator (OrderDual.ofDual a.val.2) : Set (PontryaginDual G)).indicator
          (fun χ ↦ ∫ ψ : lcaAnnihilator a.val.1, lcaFourier μ f (χ * ψ.val) ∂νJ) := by sorry

omit hHaar hRegular
variable (μK : Measure K) [hHaarK : μK.IsHaarMeasure] [hRegularK : μK.Regular]
variable (hK : IsClosed (K : Set G))

include hK hHaarK hRegularK

-- TODO(paper-gap): The proof of D.1.7.1 uses properness of G → G/k and
-- openness of k. For k = ℤ in G = ℝ both assertions fail.

/-- Paper: Theorem D.1.7.1, p. 776. The integral of a Schwartz–Bruhat function
over each coset exists and gives a Schwartz–Bruhat function on the quotient. -/
theorem lcaCosetIntegral_mem_schwartzBruhat (f : SchwartzBruhat G) :
    (∀ x : G, Integrable (fun k : K ↦ f (x * k.val)) μK) ∧
      lcaCosetIntegral K μK f ∈ schwartzBruhatSubmodule (G ⧸ K) := by sorry

/-- Paper: (D.1.7.1)–(D.1.7.2), p. 776. Take the existing coset integral with
values in the Schwartz–Bruhat space on the quotient. -/
def schwartzBruhatCosetIntegral (f : SchwartzBruhat G) : SchwartzBruhat (G ⧸ K) :=
  ⟨lcaCosetIntegral K μK f, (lcaCosetIntegral_mem_schwartzBruhat K μK hK f).2⟩

/-- Paper: (D.1.7.2), p. 776. At a quotient point represented by x the
Schwartz–Bruhat coset integral is the integral along the translate by x. -/
theorem schwartzBruhatCosetIntegral_mk (f : SchwartzBruhat G) (x : G) :
    schwartzBruhatCosetIntegral K μK hK f (QuotientGroup.mk x) =
      ∫ k : K, f (x * k.val) ∂μK := by sorry

include hHaar hRegular in
/-- Paper: Theorem D.1.7.1(1), p. 776. The coset integral is obtained by integrating
the Fourier transform over the annihilator against the quotient's dual Haar measure.
Deviation: The dual of the quotient is used directly and its characters
are pulled back to G, so the integral uses the specified Plancherel normalization. -/
theorem schwartzBruhat_poisson (μQ : Measure (G ⧸ K)) (hQ : IsWeilQuotientMeasure K μ μK μQ)
    (νQ : Measure (PontryaginDual (G ⧸ K))) (hνQ : IsLCAPlancherelMeasure μQ νQ)
    (f : SchwartzBruhat G) (x : G) :
    let q : G →ₜ* G ⧸ K := ⟨QuotientGroup.mk' K, continuous_quotient_mk'⟩
    Integrable (f : G → ℂ) μ ∧
      Integrable (fun χ ↦ lcaFourier μ f (PontryaginDual.map q χ) * (χ (q x) : ℂ)) νQ ∧
      schwartzBruhatCosetIntegral K μK hK f (q x) =
        ∫ χ, lcaFourier μ f (PontryaginDual.map q χ) * (χ (q x) : ℂ) ∂νQ := by sorry

/-- Paper: Theorem D.1.7.1(2), p. 776. The coset integral on Schwartz–Bruhat
functions is a continuous linear map. -/
theorem schwartzBruhatCosetIntegral_continuousLinear :
    ∃ P : SchwartzBruhat G →L[ℂ] SchwartzBruhat (G ⧸ K),
      ∀ f, P f = schwartzBruhatCosetIntegral K μK hK f := by sorry

/-- Paper: Theorem D.1.7.1(2), p. 776. Every Schwartz–Bruhat function on the
quotient is the coset integral of a Schwartz–Bruhat function on the group. -/
theorem schwartzBruhatCosetIntegral_surjective :
    Function.Surjective (schwartzBruhatCosetIntegral K μK hK) := by sorry

/-- Paper: Theorem D.1.7.1(2), p. 776. Under second countability the coset
integral is a topological quotient map. -/
theorem schwartzBruhatCosetIntegral_isQuotientMap [SecondCountableTopology G] :
    IsQuotientMap (schwartzBruhatCosetIntegral K μK hK) := by sorry

end AveragingAndFourier

section Supports

open UniformSpace

local instance sec1cContinuousSMulSeminorms {X : Type*} [AddCommGroup X] [Module ℂ X] {ι : Type*}
    (p : SeminormFamily ℂ X ι) : ContinuousSMul ℂ (WithGeneratingSeminorms X p) :=
  (withGeneratingSeminorms_spec X p).continuousSMul

variable {G H : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G] [CommGroup H] [TopologicalSpace H]
  [hTopH : IsTopologicalGroup H] [hT2H : T2Space H] [hLCH : LocallyCompactSpace H]

include hTop hT2 hLC

include hTopH hT2H hLCH in
/-- Paper: Lemma D.1.8.1(1), p. 778. Multiplication of functions on the factors
gives a continuous linear isomorphism from the completed inductive tensor product
onto the Schwartz–Bruhat space of the product. -/
theorem schwartzBruhat_kernel_equiv [SecondCountableTopology G] [SecondCountableTopology H] :
    ∃ e : Completion (InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)) ≃L[ℂ]
        SchwartzBruhat (G × H),
      ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (x : G) (y : H),
        e (Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))
          (f ⊗ₜ[ℂ] g)) (x, y) = f x * g y := by sorry

/-- Paper: Lemma D.1.8.1(2), p. 778. The completed projective tensor product
of the strong duals is the strong dual on the product. On pure tensors
the identification multiplies the two evaluations. -/
theorem schwartzBruhat_strongDual_kernel_equiv [SecondCountableTopology G]
    [SecondCountableTopology H]
    (e : Completion (InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H)) ≃L[ℂ]
      SchwartzBruhat (G × H))
    (he : ∀ (f : SchwartzBruhat G) (g : SchwartzBruhat H) (x : G) (y : H),
      e (Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))
        (f ⊗ₜ[ℂ] g)) (x, y) = f x * g y) :
    ∃ E : Completion (ProjectiveTensor (StrongDual ℂ (SchwartzBruhat G))
          (StrongDual ℂ (SchwartzBruhat H))) ≃L[ℂ] StrongDual ℂ (SchwartzBruhat (G × H)),
      ∀ (S : StrongDual ℂ (SchwartzBruhat G)) (T : StrongDual ℂ (SchwartzBruhat H))
        (f : SchwartzBruhat G) (g : SchwartzBruhat H),
        E (Completion.coe' (α := ProjectiveTensor (StrongDual ℂ (SchwartzBruhat G))
          (StrongDual ℂ (SchwartzBruhat H))) (S ⊗ₜ[ℂ] T))
          (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat G) (SchwartzBruhat H))
            (f ⊗ₜ[ℂ] g))) = S f * T g := by sorry

-- TODO(paper-gap): The proof after (D.1.8.3) cites part (1) for the strong-dual
-- tensor identification at the Fréchet stages. That step uses the nuclear Fréchet result.

/-- Paper: Definition D.1.8.2(1), p. 779. The vanishing locus is the union of
open sets on which the distribution kills all Schwartz–Bruhat tests supported there. -/
def schwartzBruhatVanishingLocus (T : StrongDual ℂ (SchwartzBruhat G)) : Set G :=
  ⋃₀ {U | IsOpen U ∧ ∀ f : SchwartzBruhat G, tsupport (f : G → ℂ) ⊆ U → T f = 0}

/-- Paper: Definition D.1.8.2(2), p. 779. The support is the complement of the
vanishing locus. -/
def schwartzBruhatDistributionSupport (T : StrongDual ℂ (SchwartzBruhat G)) : Set G :=
  (schwartzBruhatVanishingLocus T)ᶜ

/-- Paper: Definition D.1.8.2, p. 779. Point evaluation vanishes precisely off
the evaluation point and has singleton support.
Deviation: Sanity check on both the vanishing locus and the support. -/
theorem schwartzBruhat_dirac_support (x : G) :
    ∃ δ : StrongDual ℂ (SchwartzBruhat G),
      (∀ f, δ f = f x) ∧
      schwartzBruhatVanishingLocus δ = {x}ᶜ ∧ schwartzBruhatDistributionSupport δ = {x} :=
  by sorry

omit hTop hT2 hLC in
/-- Paper: Proposition D.1.8.3, p. 779. The support of a tensor product of four
tempered distributions on the elementary factors is the product of their supports.
Deviation: The tensor distribution is characterized by its pairings with pure tensors. -/
theorem elementary_schwartzBruhat_tensor_support
    (m n r : ℕ) {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F] :
    let R := Multiplicative (EuclideanSpace ℝ (Fin m))
    let T := Multiplicative (Fin n → AddCircle (1 : ℝ))
    let Z := Multiplicative (Fin r → ℤ)
    let A := Multiplicative F
    ∀ (d₁ : StrongDual ℂ (SchwartzBruhat R)) (d₂ : StrongDual ℂ (SchwartzBruhat T))
      (d₃ : StrongDual ℂ (SchwartzBruhat Z)) (d₄ : StrongDual ℂ (SchwartzBruhat A))
      (d : StrongDual ℂ (SchwartzBruhat (R × T × Z × A))),
      (∀ (f₁ : SchwartzBruhat R) (f₂ : SchwartzBruhat T) (f₃ : SchwartzBruhat Z)
        (f₄ : SchwartzBruhat A), ∃ f : SchwartzBruhat (R × T × Z × A),
        (∀ x, f x = f₁ x.1 * f₂ x.2.1 * f₃ x.2.2.1 * f₄ x.2.2.2) ∧
        d f = d₁ f₁ * d₂ f₂ * d₃ f₃ * d₄ f₄) →
      schwartzBruhatDistributionSupport d =
        schwartzBruhatDistributionSupport d₁ ×ˢ (schwartzBruhatDistributionSupport d₂ ×ˢ
          (schwartzBruhatDistributionSupport d₃ ×ˢ schwartzBruhatDistributionSupport d₄)) :=
  by sorry

open Classical in
/-- Paper: Lemma D.1.8.4, p. 780. Pullback and extension by zero are continuous
on a structural quotient and induce restriction of a tempered distribution.
The vanishing locus of the original distribution is covered by the lifted
vanishing loci of these restrictions. -/
theorem schwartzBruhatVanishingLocus_subset_stages (T : StrongDual ℂ (SchwartzBruhat G)) :
    ∃ j : ∀ a : BruhatStructuralPair G, SchwartzBruhat a.quotient →L[ℂ] SchwartzBruhat G,
      (∀ (a : BruhatStructuralPair G) (f : SchwartzBruhat a.quotient) (x : G),
        j a f x = if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x, hx⟩) else 0) ∧
      schwartzBruhatVanishingLocus T ⊆
        ⋃ a : BruhatStructuralPair G,
          Subtype.val '' (QuotientGroup.mk ⁻¹' schwartzBruhatVanishingLocus (T.comp (j a))) :=
  by sorry

end Supports

section Translations

variable {H E : Type*} [Group H] [TopologicalSpace H] [hTopH : IsTopologicalGroup H]

include hTopH in
/-- Paper: Lemma D.1.9.1, p. 780. A linear group action on a strict inductive
limit of barrelled spaces is continuous if it jointly acts at each stage through
the corresponding subsystem of open subgroups.
Deviation: Stages are identified with their images with the subspace topology.
Linearity is explicit, as in the proof's representation by linear operators. -/
theorem continuous_action_strict_inductive_limit [T2Space H] [LocallyCompactSpace H]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E] [PolynormableSpace ℂ E]
    (K : ℕ → OpenSubgroup H) (hK : Monotone K) (hK' : ∀ h : H, ∃ n, h ∈ K n)
    (S : ℕ → Submodule ℂ E) (hS : Monotone S) (hS' : ∀ x : E, ∃ n, x ∈ S n)
    (hFinal : ‹TopologicalSpace E› = locallyConvexFinalTopology (fun n ↦ (S n).subtype))
    (hBarrelled : ∀ n, BarrelledSpace ℂ (S n))
    (ρ : H →* (E ≃ₗ[ℂ] E))
    (hPreserve : ∀ n (k : K n) (x : S n), ρ k.val x.val ∈ S n)
    (hContinuous : ∀ n, Continuous (fun p : K n × S n ↦ ρ p.1.val p.2.val)) :
    Continuous (fun p : H × E ↦ ρ p.1 p.2) := by sorry

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [hTop : IsTopologicalGroup G]
  [hT2 : T2Space G] [hLC : LocallyCompactSpace G]

include hTop hT2 hLC

/-- Paper: Proposition D.1.9.2, p. 781. A left translate of a Schwartz–Bruhat
function is again Schwartz–Bruhat. -/
theorem schwartzBruhat_translate_mem (g : G) (f : SchwartzBruhat G) :
    (fun x ↦ f (g⁻¹ * x)) ∈ schwartzBruhatSubmodule G := by sorry

/-- Paper: Proposition D.1.9.2, p. 781. The left translation by g evaluates
the original function at g⁻¹x. -/
def schwartzBruhatTranslate (g : G) (f : SchwartzBruhat G) : SchwartzBruhat G :=
  ⟨fun x ↦ f (g⁻¹ * x), schwartzBruhat_translate_mem g f⟩

/-- Paper: Proposition D.1.9.2, p. 781. Translating a test function by g and
evaluating at gx recovers its original value at x.
Deviation: Sanity check on the direction of left translation. -/
theorem schwartzBruhatTranslate_apply_mul (g x : G) (f : SchwartzBruhat G) :
    schwartzBruhatTranslate g f (g * x) = f x := by sorry

/-- Paper: Proposition D.1.9.2, p. 781. For a second-countable group, left
translation is jointly continuous in the group element and Schwartz–Bruhat function. -/
theorem schwartzBruhatTranslate_continuous [SecondCountableTopology G] :
    Continuous (fun p : G × SchwartzBruhat G ↦ schwartzBruhatTranslate p.1 p.2) := by sorry

/-- Paper: Proposition D.1.9.2, p. 781. Translations by a compact set of group
elements send one common zero-neighborhood into any prescribed zero-neighborhood. -/
theorem schwartzBruhatTranslate_equicontinuous [SecondCountableTopology G]
    (K : Set G) (hK : IsCompact K) {U : Set (SchwartzBruhat G)} (hU : U ∈ 𝓝 0) :
    ∃ V ∈ 𝓝 (0 : SchwartzBruhat G),
      ∀ g ∈ K, ∀ f ∈ V, schwartzBruhatTranslate g f ∈ U := by sorry

-- TODO(paper-gap): D.1.9.3 omits additivity of the action. The proof uses
-- distributivity over sums, and the statement fails for actions by arbitrary homeomorphisms.

omit hTop hT2 hLC in
include hTopH in
/-- Paper: Lemma D.1.9.3, p. 781. A complex linear action on the completion
is jointly continuous if each operator is continuous and the invariant original
space has a jointly continuous action.
Deviation: The linear action needed for the addition identities in the proof is explicit. -/
theorem continuous_action_completion [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
    [ContinuousSMul ℂ E] [T2Space E]
    (ρ : H →* (UniformSpace.Completion E ≃ₗ[ℂ] UniformSpace.Completion E))
    (hEach : ∀ h : H, Continuous (ρ h))
    (τ : H →* (E ≃ₗ[ℂ] E))
    (hτ : ∀ h (x : E), ρ h (x : UniformSpace.Completion E) = (τ h x : UniformSpace.Completion E))
    (hJoint : Continuous (fun p : H × E ↦ τ p.1 p.2)) :
    Continuous (fun p : H × UniformSpace.Completion E ↦ ρ p.1 p.2) := by sorry

omit hTop hT2 hLC in
include hTopH in
/-- Paper: Lemma D.1.9.4, p. 782. The diagonal action induced by continuous
linear actions on both factors is jointly continuous on their projective tensor product. -/
theorem continuous_action_projectiveTensor
    {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [T2Space E] [T2Space F] [PolynormableSpace ℂ E] [PolynormableSpace ℂ F]
    (ρ : H →* (E ≃ₗ[ℂ] E)) (τ : H →* (F ≃ₗ[ℂ] F))
    (hρ : Continuous (fun p : H × E ↦ ρ p.1 p.2))
    (hτ : Continuous (fun p : H × F ↦ τ p.1 p.2)) :
    Continuous (fun p : H × ProjectiveTensor E F ↦
      (show ProjectiveTensor E F from
        TensorProduct.map (ρ p.1).toLinearMap (τ p.1).toLinearMap p.2)) := by sorry

end Translations

end RiemannMasullo
