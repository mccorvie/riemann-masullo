module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3a
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b

/-! # Extensions by zero and holomorphic S-idelic zeta functions

Masullo, §5.3.3–5.3.4, pp. 249–265.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped ContDiff Distributions FourierTransform NNReal NumberField.AdeleRing SchwartzMap TensorProduct Topology

namespace RiemannMasullo

set_option quotPrecheck false

section PuncturedLine

-- TODO(paper-gap): The logarithmic argument substitution leaves the exponent interval I fixed.

/-- Paper: Example 5.3.3.1, p. 249.
Logarithmic coordinates give a linear homeomorphism between the weighted spaces on
the real line and the positive multiplicative reals.
Deviation: The exponents are unchanged under the logarithmic change of the argument. -/
theorem positiveRealExponentialDecay_log_equiv (I : Set ℝ) (hI : OrdConnected I)
    (hne : I.Nonempty) :
    ∃ e : PositiveRealExponentialDecay I ≃L[ℂ]
        ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) I,
      ∀ f t, (e f).val t = f.val (Real.log (t.val : ℝ)) :=
  identityModulationExponentialDecay_equiv I hI hne

local notation "normPower(" K ", " d ")" =>
  (Units.map nnNormHom.toMonoidHom ^ d : Kˣ →* ℝ≥0ˣ)

/-- Paper: Proposition 5.3.3.2, p. 249.
Natural powers of the norm on the multiplicative group are continuous as
maps to the positive reals. -/
theorem continuous_archimedeanUnitModulation (K : Type*) [NormedField K] (d : ℕ) :
    Continuous (normPower(K, d)) := by sorry

/-- Paper: Proposition 5.3.3.2, p. 249.
The real multiplicative group uses the norm, and the complex multiplicative group
uses the squared norm. -/
def archimedeanUnitModulation (K : Type*) [NormedField K] (d : ℕ) : Kˣ →ₜ* ℝ≥0ˣ :=
  ⟨normPower(K, d), continuous_archimedeanUnitModulation K d⟩

/-- Paper: Proposition 5.3.3.2, p. 249.
At a nonzero argument the module evaluates to the indicated power of its norm. -/
theorem archimedeanUnitModulation_apply (K : Type*) [NormedField K] (d : ℕ) (u : Kˣ) :
    ((archimedeanUnitModulation K d u).val : ℝ) = ‖(u : K)‖ ^ d := by sorry

local notation "𝓔(" K ", " d ", " I ")" => ModulatedExponentialDecay (archimedeanUnitModulation K d) I
local notation "punctured(" K ")" => (⟨{0}ᶜ, isClosed_singleton.isOpen_compl⟩ : Opens K)
local notation "𝒟₀(" K ")" => 𝓓(punctured(K), ℂ)
local notation "zeroExtension(" f ")" =>
  (fun x ↦ if hx : x ≠ 0 then f (Units.mk0 x hx) else (0 : ℂ))
local notation "complexCoordinate(" conjugate ")" =>
  (fun z : ℂ ↦ if conjugate then star z else z)
local notation "wirtinger(" conjugate ")" =>
  (if conjugate then wirtingerConjDeriv else wirtingerDeriv)

/-- Paper: §5.3.3, p. 249.
Restriction gives a continuous linear injection of additive real Schwartz functions into
the space with all positive weights. -/
theorem realSchwartz_restrict_positiveDecay :
    ∃ R : 𝓢(ℝ, ℂ) →L[ℂ] 𝓔(ℝ, 1, Ioi 0), Injective R ∧
      ∀ (f : 𝓢(ℝ, ℂ)) (u : ℝˣ), (R f).val u = f u.val := by sorry

/-- Paper: §5.3.3, p. 249.
Restriction of an additive complex Schwartz function to the units gives a continuous
linear injection into the space with all positive squared-norm weights. -/
theorem complexSchwartz_restrict_positiveDecay :
    ∃ R : 𝓢(ℂ, ℂ) →L[ℂ] 𝓔(ℂ, 2, Ioi 0), Injective R ∧
      ∀ (f : 𝓢(ℂ, ℂ)) (u : ℂˣ), (R f).val u = f u.val := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is a linear homeomorphism on compactly supported
smooth tests on the punctured real line. -/
theorem realCoordinate_mul_puncturedTest :
    ∃ M : 𝒟₀(ℝ) ≃L[ℂ] 𝒟₀(ℝ), ∀ f x, M f x = (x : ℂ) * f x := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by either complex coordinate, z or its conjugate, is a linear homeomorphism
on compactly supported smooth tests on the punctured complex plane. -/
theorem complexCoordinate_mul_puncturedTest (conjugate : Bool) :
    ∃ M : 𝒟₀(ℂ) ≃L[ℂ] 𝒟₀(ℂ), ∀ f z, M f z = complexCoordinate(conjugate) z * f z := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is continuous for decay on a closed upper half-line. -/
theorem realCoordinate_mul_exponentialDecay (a : ℝ) :
    ∃ M : 𝓔(ℝ, 1, Ici a) →L[ℂ] 𝓔(ℝ, 1, Ici a),
      ∀ f x, (M f).val x = ((x : ℝ) : ℂ) * f.val x := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by z or its conjugate is continuous for decay on a closed upper half-line. -/
theorem complexCoordinate_mul_exponentialDecay (conjugate : Bool) (a : ℝ) :
    ∃ M : 𝓔(ℂ, 2, Ici a) →L[ℂ] 𝓔(ℂ, 2, Ici a),
      ∀ f z, (M f).val z = complexCoordinate(conjugate) z.val * f.val z := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by the real coordinate is continuously invertible for decay at all exponents. -/
theorem realCoordinate_mul_allExponentialDecay :
    ∃ M : 𝓔(ℝ, 1, univ) ≃L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (M f).val x = ((x : ℝ) : ℂ) * f.val x := by sorry

/-- Paper: Proposition 5.3.3.2(1), p. 249.
Multiplication by z or its conjugate is continuously invertible for decay at all exponents. -/
theorem complexCoordinate_mul_allExponentialDecay (conjugate : Bool) :
    ∃ M : 𝓔(ℂ, 2, univ) ≃L[ℂ] 𝓔(ℂ, 2, univ),
      ∀ f z, (M f).val z = complexCoordinate(conjugate) z.val * f.val z := by sorry

-- TODO(paper-gap): Footnote 8 flags the closed-range argument. A convergent net in the LF
-- space of tests need not eventually be bounded and a directed set need not have countable cofinality.

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
Each ordinary derivative is a continuous operator of closed range on punctured real tests. -/
theorem iteratedDeriv_puncturedTest_closedRange (m : ℕ) :
    ∃ D : 𝒟₀(ℝ) →L[ℂ] 𝒟₀(ℝ), IsClosed (range D) ∧
      ∀ f x, D f x = iteratedDeriv m (f : ℝ → ℂ) x := by sorry

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Both first Wirtinger operators have closed range on punctured complex tests. -/
theorem wirtinger_puncturedTest_closedRange (conjugate : Bool) :
    ∃ D : 𝒟₀(ℂ) →L[ℂ] 𝒟₀(ℂ), IsClosed (range D) ∧
      ∀ f z, D f z = wirtinger(conjugate) f z := by sorry

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
An ordinary derivative of order m shifts the lower endpoint of the decay interval by m. -/
theorem iteratedDeriv_exponentialDecay (m : ℕ) (a : ℝ) :
    ∃ D : 𝓔(ℝ, 1, Ioi a) →L[ℂ] 𝓔(ℝ, 1, Ioi (a + m)),
      ∀ f x, (D f).val x = iteratedDeriv m zeroExtension(f.val) x.val := by sorry

-- TODO(paper-gap): The first Wirtinger operator in the printed weighted shift is
-- missing the exponent m. The proof uses m derivatives for both operators.

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Either iterated Wirtinger derivative gives a continuous operator into the indicated decay space.
Deviation: Both derivatives have order m, as in the proof. The stated target with shift m is
retained, although the squared norm permits a shift of m/2. -/
theorem iteratedWirtinger_exponentialDecay (conjugate : Bool) (m : ℕ) {a : ℝ} (_ha : a < 0) :
    ∃ D : 𝓔(ℂ, 2, Ioi a) →L[ℂ] 𝓔(ℂ, 2, Ioi (a + m)),
      ∀ f z, (D f).val z = ((wirtinger(conjugate))^[m] zeroExtension(f.val)) z.val := by sorry

/-- Paper: Proposition 5.3.3.2(2)(1), p. 249.
Ordinary derivatives act continuously on the punctured real space with decay at all exponents. -/
theorem iteratedDeriv_allExponentialDecay (m : ℕ) :
    ∃ D : 𝓔(ℝ, 1, univ) →L[ℂ] 𝓔(ℝ, 1, univ),
      ∀ f x, (D f).val x = iteratedDeriv m zeroExtension(f.val) x.val := by sorry

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Both iterated Wirtinger operators preserve the punctured complex space with decay at all
exponents and act continuously there. -/
theorem iteratedWirtinger_allExponentialDecay (conjugate : Bool) (m : ℕ) :
    ∃ D : 𝓔(ℂ, 2, univ) →L[ℂ] 𝓔(ℂ, 2, univ),
      ∀ f z, (D f).val z = ((wirtinger(conjugate))^[m] zeroExtension(f.val)) z.val := by sorry

/-- Paper: Proposition 5.3.3.2(2)(1), p. 250.
Weighted Schwartz–Bruhat functions are smooth on the punctured real line. -/
theorem realExponentialDecay_contDiffOn (f : 𝓔(ℝ, 1, Ioi 0)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set ℝ) := by sorry

/-- Paper: Proposition 5.3.3.2(2)(2), p. 250.
Weighted Schwartz–Bruhat functions are smooth on the punctured complex plane
as functions of two real variables. -/
theorem complexExponentialDecay_contDiffOn (f : 𝓔(ℂ, 2, Ioi 0)) :
    ContDiffOn ℝ (∞ : ℕ∞ω) zeroExtension(f.val) ({0}ᶜ : Set ℂ) := by sorry

end PuncturedLine

section ArchimedeanProduct

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

local notation "archAdd(" ι ", " κ ")" => ((ι → ℝ) × (κ → ℂ))
local notation "archMul(" ι ", " κ ")" => ((ι → ℝˣ) × (κ → ℂˣ))
local notation "archVal" => fun u ↦ (fun i ↦ (u.1 i).val, fun j ↦ (u.2 j).val)
local notation "meetsWall(" x ")" => ((∃ i, x.1 i = 0) ∨ (∃ j, x.2 j = 0))
local notation "weights(" ι ", " κ ", " I ")" =>
  ((ι → (insert 0 I : Set ℝ)) × (κ → (insert 0 I : Set ℝ)))

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

local notation "weightMap(" a ")" => LinearMap.mulLeft ℂ
  (fun u : archMul(ι, κ) ↦
    ((∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ)) : ℝ) *
    ((∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ)) : ℝ) : archMul(ι, κ) → ℂ)

/-- Paper: Lemma 5.3.3.3, p. 252.
Every partial coordinate weight with exponents in I must yield a Schwartz–Bruhat function.
Deviation: A zero exponent encodes an omitted coordinate in (5.3.3.5), including the
unweighted condition when every coordinate is omitted. -/
def archimedeanWeightedSchwartzSubmodule (I : Set ℝ) :
    Submodule ℂ (archMul(ι, κ) → ℂ) :=
  ⨅ a : weights(ι, κ, I), (schwartzBruhatSubmodule _).comap (weightMap(a))

/-- Paper: Lemma 5.3.3.3, p. 252.
The map for a family of exponents applies its weight and returns a Schwartz–Bruhat function. -/
def archimedeanSchwartzTwist (I : Set ℝ) (a : weights(ι, κ, I)) :
    archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I →ₗ[ℂ]
      SchwartzBruhat (archMul(ι, κ)) :=
  ((weightMap(a)).comp (archimedeanWeightedSchwartzSubmodule I).subtype).codRestrict
    (schwartzBruhatSubmodule _) (fun f ↦
      Submodule.mem_comap.1 ((Submodule.mem_iInf _).1 f.property a))

/-- Paper: Lemma 5.3.3.3, p. 252.
The twist uses one power of the real norm and the corresponding power of the squared
complex norm in each coordinate. -/
theorem archimedeanSchwartzTwist_apply (I : Set ℝ) (a : weights(ι, κ, I))
    (f : archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (u : archMul(ι, κ)) :
    archimedeanSchwartzTwist I a f u =
      (↑(∏ i, ‖(u.1 i).val‖ ^ (a.1 i : ℝ)) : ℂ) *
      (↑(∏ j, (‖(u.2 j).val‖ ^ (2 : ℕ)) ^ (a.2 j : ℝ)) : ℂ) * f.val u := by sorry

/-- Paper: Lemma 5.3.3.3, p. 252.
On both the real and complex coordinates, choosing only zero exponents gives the
unweighted Schwartz–Bruhat space. -/
theorem archimedeanWeightedSchwartzSubmodule_singleton_zero :
    archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) {0} =
      schwartzBruhatSubmodule (archMul(ι, κ)) := by sorry

/-- Paper: Lemma 5.3.3.3, p. 252.
The topology is the initial locally convex topology for all the partial weight maps into
the Schwartz–Bruhat space in (5.3.3.8). -/
abbrev ArchimedeanWeightedSchwartz (I : Set ℝ) :=
  WithGeneratingSeminorms (archimedeanWeightedSchwartzSubmodule (ι := ι) (κ := κ) I)
    (fun i : weights(ι, κ, I) ×
      {p : Seminorm ℂ (SchwartzBruhat (archMul(ι, κ))) // Continuous p} ↦
      i.2.val.comp (archimedeanSchwartzTwist I i.1))

local notation "𝓦(" I ")" => ArchimedeanWeightedSchwartz (ι := ι) (κ := κ) I

/-- Paper: Lemma 5.3.3.3, p. 252.
When there are no coordinates, the weighted Schwartz space is the scalar field. -/
theorem archimedeanWeightedSchwartz_empty_equiv (I : Set ℝ) :
    ∃ e : ArchimedeanWeightedSchwartz (ι := Empty) (κ := Empty) I ≃L[ℂ] ℂ,
      ∀ f, e f = f.val (1 : archMul(Empty, Empty)) := by sorry

-- TODO(paper-gap): The proof's integer exponents need not meet I. Use a countable
-- family of exponents in I bracketing each exponent in I, together with zero.

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the topology from the partial weight maps is Fréchet. -/
theorem archimedeanWeightedSchwartz_frechet {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : IsFrechetTVS 𝓦(I) := by sorry

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the weighted Schwartz–Bruhat space is separable. -/
theorem archimedeanWeightedSchwartz_separable {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : SeparableSpace 𝓦(I) := by sorry

/-- Paper: Lemma 5.3.3.3(1), p. 252.
For an open nonempty interval the weighted Schwartz–Bruhat space is nuclear. -/
theorem archimedeanWeightedSchwartz_nuclear {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) : IsNuclearTVS 𝓦(I) := by sorry

/-- Paper: Lemma 5.3.3.3(2), p. 252.
The finite projective tensor topology is generated by seminorms with jointly continuous
pullback along the pure tensor map, as for the binary projective tensor product of §C.2.3. -/
abbrev FiniteProjectiveTensor {ι : Type*} [Fintype ι] (E : ι → Type*)
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℂ (E i)] [∀ i, TopologicalSpace (E i)] :=
  WithGeneratingSeminorms (⨂[ℂ] i, E i)
    (fun p : {p : Seminorm ℂ (⨂[ℂ] i, E i) //
      Continuous (fun f : ∀ i, E i ↦ p (⨂ₜ[ℂ] i, f i))} ↦ p.val)

/-- Paper: Lemma 5.3.3.3(2), p. 252.
With no factors the projective tensor product identifies topologically with the scalars
and the empty pure tensor maps to one. -/
theorem finiteProjectiveTensor_empty_equiv :
    ∃ e : FiniteProjectiveTensor (fun _ : Empty ↦ ℂ) ≃L[ℂ] ℂ,
      e (⨂ₜ[ℂ] i : Empty, (0 : ℂ)) = 1 := by sorry

-- TODO(paper-gap): If 0 ∉ I the factors S_I need not be unweighted Schwartz–Bruhat,
-- whereas (5.3.3.6) requires this. Include the unweighted twist on each factor.

set_option maxHeartbeats 600000 in
/-- Paper: Lemma 5.3.3.3(2), p. 252.
The canonical map multiplies pure factors evaluated in their own coordinates and
extends to a linear homeomorphism on the completion.
Deviation: The factors include weight zero for the unweighted condition in (5.3.3.6).
When zero already belongs to I these are the factors printed in the paper. -/
theorem archimedeanWeightedSchwartz_tensor {I : Set ℝ} (_ho : IsOpen I)
    (_hi : OrdConnected I) (_hne : I.Nonempty) :
    let J := insert 0 I
    let R := ModulatedExponentialDecay (archimedeanUnitModulation ℝ 1) J
    let C := ModulatedExponentialDecay (archimedeanUnitModulation ℂ 2) J
    let T := ProjectiveTensor (FiniteProjectiveTensor (fun _ : ι ↦ R))
      (FiniteProjectiveTensor (fun _ : κ ↦ C))
    ∃ L : T →L[ℂ] 𝓦(I), IsEmbedding L ∧
      (∀ (f : ι → R) (g : κ → C) (u : archMul(ι, κ)),
        (L ((⨂ₜ[ℂ] i, f i) ⊗ₜ[ℂ] (⨂ₜ[ℂ] j, g j))).val u =
          (∏ i, (f i).val (u.1 i)) * ∏ j, (g j).val (u.2 j)) ∧
      ∃ e : UniformSpace.Completion T ≃L[ℂ] 𝓦(I), ∀ z : T, e z = L z := by sorry

local notation "jet(" n ", " x ", " v ")" =>
  (fun f : 𝓢(archAdd(ι, κ), ℂ) ↦ iteratedFDeriv ℝ n (f : archAdd(ι, κ) → ℂ) x v)

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Evaluation of the real derivative of order n at a point and a tuple of directions
is complex-linear in the Schwartz function. -/
theorem archimedeanSchwartzJet_isLinear (n : ℕ) (x : archAdd(ι, κ))
    (v : Fin n → archAdd(ι, κ)) : IsLinearMap ℂ (jet(n, x, v)) := by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 252.
The flat Schwartz subspace is the intersection of the kernels of all jets on the
union of the coordinate hyperplanes.
Deviation: Full real Fréchet derivatives express the equivalent vanishing of the
mixed ordinary and Wirtinger derivatives. The coordinates are the product field coordinates. -/
def archimedeanFlatSchwartz : Submodule ℂ 𝓢(archAdd(ι, κ), ℂ) :=
  ⨅ x : {x : archAdd(ι, κ) // meetsWall(x)}, ⨅ n : ℕ, ⨅ v : Fin n → archAdd(ι, κ),
    LinearMap.ker ((archimedeanSchwartzJet_isLinear n x.val v).mk' _)

/-- Paper: Lemma 5.3.3.3(3), p. 252.
For one real factor the jet conditions recover the real flat subspace of §5.3.2. -/
theorem archimedeanFlatSchwartz_one_real :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := Unit) (κ := Empty)) ≃L[ℂ] ↥realSchwartzFlatAtOrigin,
      ∀ f (x : ℝ), (e f).val x = f.val (fun _ ↦ x, fun j ↦ Empty.elim j) := by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 252.
For one complex factor the real jet conditions recover the mixed Wirtinger conditions of §5.3.2. -/
theorem archimedeanFlatSchwartz_one_complex :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := Empty) (κ := Unit)) ≃L[ℂ] ↥complexSchwartzFlatAtOrigin,
      ∀ f (z : ℂ), (e f).val z = f.val (fun i ↦ Empty.elim i, fun _ ↦ z) := by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 252.
Schwartz functions supported away from every coordinate hyperplane are flat along them. -/
theorem mem_archimedeanFlatSchwartz_of_tsupport (f : 𝓢(archAdd(ι, κ), ℂ))
    (_hf : Disjoint (tsupport f) {x : archAdd(ι, κ) | meetsWall(x)}) :
    f ∈ archimedeanFlatSchwartz := by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 252.
The subspace of Schwartz functions with all jets zero on the coordinate hyperplanes is closed. -/
theorem archimedeanFlatSchwartz_isClosed :
    IsClosed (↑(archimedeanFlatSchwartz (ι := ι) (κ := κ)) : Set 𝓢(archAdd(ι, κ), ℂ)) := by sorry

-- TODO(paper-gap): The estimates (5.3.3.21)–(5.3.3.23) fail for bumps
-- supported close to, but away from, the origin.

/-- Paper: Lemma 5.3.3.3(3), p. 253.
Restriction to the product of the punctured lines identifies flat Schwartz functions
with the all-exponent weighted space. The inverse extends by zero. -/
theorem archimedeanFlatSchwartz_restrict_equiv :
    ∃ e : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) ≃L[ℂ] 𝓦(univ),
      ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)), (e f).val u = f.val (archVal u) :=
  by sorry

/-- Paper: Lemma 5.3.3.3(3), p. 253.
A continuous quasi-character on the product of punctured fields acts by multiplication
through a unique linear homeomorphism of the flat Schwartz space. -/
theorem archimedeanFlatSchwartz_quasiCharacter_mul (c : QuasiCharacter (archMul(ι, κ))) :
    ∃! M : ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)) ≃L[ℂ]
        ↥(archimedeanFlatSchwartz (ι := ι) (κ := κ)),
      ∀ (f : archimedeanFlatSchwartz) (u : archMul(ι, κ)),
        (M f).val (archVal u) = c u * f.val (archVal u) := by sorry

end ArchimedeanProduct

section ArchimedeanMellin

local notation "realProfile(" f ", " ε ")" =>
  (fun t : ℝ ↦ f t + (-1 : ℂ) ^ (ε).val * f (-t))
local notation "unitAngle(" θ ")" => Complex.exp ((θ : ℂ) * Complex.I)
local notation "complexProfile(" f ", " n ")" =>
  (fun t : ℝ ↦ ∫ θ in (0 : ℝ)..(2 * Real.pi),
    (unitAngle(θ)) ^ n * f ((Real.sqrt t : ℂ) * unitAngle(θ)))

/-- Paper: Proposition 5.3.3.4, p. 258.
The real Mellin integral converges on the right half-plane and has a unique
meromorphic continuation for each sign parity. -/
theorem realArchimedeanMellin_existsUnique (f : 𝓢(ℝ, ℂ)) (ε : Fin 2) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      ∀ s : ℂ, 0 < s.re → HasMellin (realProfile(f, ε)) s (L s) := by sorry

/-- Paper: Proposition 5.3.3.4, p. 258.
The real local Mellin transform is the meromorphic continuation of the weighted
integral over the two signs in (5.3.3.26). -/
def realArchimedeanMellin (f : 𝓢(ℝ, ℂ)) (ε : Fin 2) : ℂ → ℂ :=
  (realArchimedeanMellin_existsUnique f ε).exists.choose

/-- Paper: Proposition 5.3.3.4, p. 258.
The positive half-plane gives the defining integral for the real Mellin transform. -/
theorem realArchimedeanMellin_eq_integral (f : 𝓢(ℝ, ℂ)) (ε : Fin 2)
    (s : ℂ) (_hs : 0 < s.re) :
    realArchimedeanMellin f ε s = mellin (realProfile(f, ε)) s := by sorry

/-- Paper: Proposition 5.3.3.4, p. 258.
The complex Mellin integral converges on the right half-plane and has a unique
meromorphic continuation for each integral angular weight.
Deviation: The angular measure is dθ in the norm coordinate t = |z|², as in §3.3.
The printed 2 dθ would double the Tamagawa integral. -/
theorem complexArchimedeanMellin_existsUnique (f : 𝓢(ℂ, ℂ)) (n : ℤ) :
    ∃! L : ℂ → ℂ, MeromorphicNFOn L univ ∧
      ∀ s : ℂ, 0 < s.re → HasMellin (complexProfile(f, n)) s (L s) := by sorry

/-- Paper: Proposition 5.3.3.4, p. 258.
The complex local Mellin transform is the meromorphic continuation of the angular
and radial integral in (5.3.3.26).
Deviation: The angular measure is normalized as in §3.3. -/
def complexArchimedeanMellin (f : 𝓢(ℂ, ℂ)) (n : ℤ) : ℂ → ℂ :=
  (complexArchimedeanMellin_existsUnique f n).exists.choose

/-- Paper: Proposition 5.3.3.4, p. 258.
The positive half-plane gives the defining integral for the complex Mellin transform.
Deviation: The angular measure is normalized as in §3.3. -/
theorem complexArchimedeanMellin_eq_integral (f : 𝓢(ℂ, ℂ)) (n : ℤ)
    (s : ℂ) (_hs : 0 < s.re) :
    complexArchimedeanMellin f n s = mellin (complexProfile(f, n)) s := by sorry

/-- Paper: Proposition 5.3.3.4, p. 258.
In the real field model the local zeta function of §3.3 is the two-sign Mellin transform
at the radial exponent and parity of the given quasi-character. -/
theorem realArchimedeanMellin_eq_infiniteLocalIdelicZFunction
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsReal)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℝ, ℂ), (∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivRealOfIsReal hw x) = f (Multiplicative.ofAdd x)) ∧
      ∀ c : QuasiCharacter w.Completionˣ,
        let p := (realLocalEulerParameters w hw c).exists.choose
        infiniteLocalIdelicZFunction w f c = realArchimedeanMellin g p.2 p.1 := by sorry

/-- Paper: Proposition 5.3.3.4, p. 258.
In the complex field model the local zeta function of §3.3 is the angular Mellin transform
at the squared-norm exponent and angular weight of the given quasi-character. -/
theorem complexArchimedeanMellin_eq_infiniteLocalIdelicZFunction
    {F : Type*} [Field F] [NumberField F] (w : InfinitePlace F) (hw : w.IsComplex)
    (f : SchwartzBruhat (Multiplicative w.Completion)) :
    ∃ g : 𝓢(ℂ, ℂ), (∀ x : w.Completion,
      g (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw x) = f (Multiplicative.ofAdd x)) ∧
      ∀ c : QuasiCharacter w.Completionˣ,
        let p := (complexLocalEulerParameters w hw c).exists.choose
        infiniteLocalIdelicZFunction w f c = complexArchimedeanMellin g p.2 p.1 := by sorry

local notation "realMonomial(" n ")" => SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ) ^ n)
local notation "complexMonomial(" p ", " q ")" =>
  SchwartzMap.smulLeftCLM ℂ (fun z : ℂ ↦ z ^ p * star z ^ q)
local notation "shiftParity(" ε ", " n ")" => Fin.ofNat 2 ((ε).val + n)
local notation "rhoReal(" ε ", " s ")" =>
  ((Complex.I ^ (ε).val) *
    (Complex.Gammaℝ (s + (ε).val) / Complex.Gammaℝ (1 - s + (ε).val)))
local notation "rhoComplex(" n ", " s ")" =>
  ((Complex.I ^ (n).natAbs) *
    (Complex.Gammaℂ (s + ((n).natAbs : ℂ) / 2) / Complex.Gammaℂ (1 - s + ((n).natAbs : ℂ) / 2)))

-- TODO(paper-gap): (5.3.3.28) drops M_{x^n} on the left. Its proof supplies the multiplier.

/-- Paper: Proposition 5.3.3.4(1), p. 258.
Multiplying by xⁿ shifts the real Mellin exponent by n and shifts the sign character by
the parity of n.
Deviation: The multiplier on the left is restored from (5.3.3.32)–(5.3.3.34). -/
theorem realArchimedeanMellin_monomial (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)) :
    realArchimedeanMellin (realMonomial(n) f) ε =
      fun s ↦ realArchimedeanMellin f shiftParity(ε, n) (s + n) := by sorry

/-- Paper: Proposition 5.3.3.4(1), p. 258.
The real monomial Mellin transform satisfies the Fourier relation at the shifted
exponent and parity. The product is understood as a meromorphic identity. -/
theorem realArchimedeanMellin_monomial_functionalEquation (n : ℕ) (ε : Fin 2) (f : 𝓢(ℝ, ℂ)) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let a := shiftParity(ε, n)
      let t := s + (n : ℂ)
      realArchimedeanMellin (realMonomial(n) f) ε s =
        rhoReal(a, t) * realArchimedeanMellin (𝓕 f) a (1 - t) := by sorry

/-- Paper: Proposition 5.3.3.4(2), p. 258.
Multiplying by zᵖ times the qth power of its conjugate shifts the Mellin exponent
by (p+q)/2 and the angular weight by p−q. -/
theorem complexArchimedeanMellin_monomial (p q : ℕ) (n : ℤ) (f : 𝓢(ℂ, ℂ)) :
    complexArchimedeanMellin (complexMonomial(p, q) f) n =
      fun s ↦ complexArchimedeanMellin f (n + (p : ℤ) - q) (s + ((p : ℂ) + q) / 2) := by sorry

-- TODO(paper-gap): The complex phase in (5.3.3.25) disagrees with the trace-pairing Fourier
-- transform for nontrivial angular weights. Use the phase from §3.3, per ERRATA I91.

/-- Paper: Proposition 5.3.3.4(2), p. 258.
The complex monomial Mellin transform satisfies the Fourier relation at the shifted
exponent and angular weight. The trace-pairing transform is the Euclidean Fourier
transform evaluated at twice the conjugate argument and multiplied by the self-dual mass factor.
Deviation: The phase is i to the absolute angular weight, as in ERRATA I91. -/
theorem complexArchimedeanMellin_monomial_functionalEquation (p q : ℕ) (n : ℤ)
    (f : 𝓢(ℂ, ℂ)) :
    ∃ fHat : 𝓢(ℂ, ℂ), (∀ z : ℂ, fHat z = 2 * (𝓕 f) (2 * star z)) ∧
      ∀ᶠ s : ℂ in codiscrete ℂ,
        let k := n + (p : ℤ) - q
        let t := s + ((p : ℂ) + q) / 2
        complexArchimedeanMellin (complexMonomial(p, q) f) n s =
          rhoComplex(k, t) * complexArchimedeanMellin fHat (-k) (1 - t) := by sorry

end ArchimedeanMellin

section SAdele

open Classical

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => ℬ(Aₛ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "Xₛ" => QuasiCharacter Jₛ
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "chartₛ(" χ ")" =>
  quasiCharacterNormTwist (G := Jₛ) mₛ (isProperMap_sIdeleQuotientNorm F S).continuous
    ((circleToComplex).comp (χ))
local notation "χ₁(" χ ")" =>
  ((χ : Jₛ →ₜ* Circle).comp
    (⟨((mₛ).ker).subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ) : PontryaginDual J₁)
local notation "thetaAt(" χ ")" => sLocalHomogeneousAdelicThetaLinearMap F S (χ)
local notation "A∞" => InfiniteAdeleRing F
local notation "RealPlaces" => {w : InfinitePlace F // w.IsReal}
local notation "ComplexPlaces" => {w : InfinitePlace F // w.IsComplex}
local notation "ArchCoordinates" => ((RealPlaces → ℝ) × (ComplexPlaces → ℂ))
local notation "RealModels" => ((w : RealPlaces) →
  {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
local notation "ComplexModels" => ((w : ComplexPlaces) →
  {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})
local notation "assemble(" r ", " c ", " x ")" =>
  (show A∞ from fun w ↦ if h : w.IsReal then ((r ⟨w, h⟩).val.symm) ((x).1 ⟨w, h⟩)
    else ((c ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩).val.symm)
      ((x).2 ⟨w, InfinitePlace.not_isReal_iff_isComplex.mp h⟩))

-- TODO(paper-gap): In (5.3.4.1), (5.3.4.7) and (5.3.4.15), the finite
-- zero-extension factors must be compactly supported locally constant tests on the
-- units. Remark 2.1.2.1 distinguishes these from the full multiplicative Schwartz
-- space. On Q_p, the sequence p^(-k) on shells of valuation k ≥ 0 is Schwartz on Z,
-- but its zero extension is not locally constant at zero.

/-- Paper: Definition 5.3.4.1, p. 259.
A function on the unit group has an additive Schwartz extension vanishing at zero
exactly when it is locally constant and compactly supported there.
Deviation: The finite punctured test space in (5.3.4.1) is interpreted as
compactly supported locally constant tests, consistently with Remark 2.1.2.1. -/
theorem exists_finitePlaceSchwartz_zeroExtension_iff (v : V) (h : (v.adicCompletion F)ˣ → ℂ) :
    (∃ f : ℬ(v.adicCompletion F), f (Multiplicative.ofAdd 0) = 0 ∧
      ∀ u : (v.adicCompletion F)ˣ, f (Multiplicative.ofAdd u.val) = h u) ↔
      IsLocallyConstant h ∧ HasCompactSupport h := by sorry

/-- Paper: Definition 5.3.4.1, p. 259.
The finite-place conditions are the kernels of evaluation at adeles with a zero
coordinate at one of the selected finite places. -/
def sAdeleFiniteZeroSchwartz (S T : Finset V) : Submodule ℂ ℬ(SAdeleRing F S) :=
  ⨅ x : {x : SAdeleRing F S // ∃ v : S, v.val ∈ T ∧ x.2 v = 0},
    LinearMap.ker ((LinearMap.proj (Multiplicative.ofAdd x.val)).comp
      (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)

/-- Paper: Definition 5.3.4.1, p. 259.
Passing from a Schwartz function in archimedean coordinates to its underlying
function is complex-linear. -/
theorem archimedeanSchwartz_coe_isLinear :
    IsLinearMap ℂ (fun f : 𝓢(ArchCoordinates, ℂ) ↦ (f : ArchCoordinates → ℂ)) := by sorry

/-- Paper: Definition 5.3.4.1, p. 259.
The polar-free subspace imposes flatness on every archimedean slice and vanishing
at a zero coordinate at every finite place.
Deviation: The finite punctured factors in (5.3.4.1) are compactly supported tests on
the units. The subspace has the topology inherited from the S-adelic Schwartz space
of Proposition 2.1.4.1, which uses the inductive archimedean–finite tensor topology.
The span identity below is algebraic. The projective topology in print is generally coarser. -/
def sAdelePolarFree (S : Finset V) (r : RealModels) (c : ComplexModels) :
    Submodule ℂ ℬ(SAdeleRing F S) :=
  sAdeleFiniteZeroSchwartz S S ⊓
    ⨅ y : (v : S) → v.val.adicCompletion F,
      let flat := (archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces)).map
        ((archimedeanSchwartz_coe_isLinear (F := F)).mk' _)
      let slice := LinearMap.funLeft ℂ ℂ (fun x : ArchCoordinates ↦
        Multiplicative.ofAdd (assemble(r, c, x), y))
      flat.comap (slice.comp (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype)

/-- Paper: Definition 5.3.4.1, p. 259.
For a pure tensor with nonzero factors, finite-coordinate vanishing is exactly
vanishing at zero of each factor selected by T. -/
theorem sAdeleFiniteZeroSchwartz_tmul_iff (T : Finset V)
    (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)) (_hf : f ≠ 0)
    (_hg : ∀ v, g v ≠ 0) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) ∈ sAdeleFiniteZeroSchwartz S T ↔
      ∀ v : S, v.val ∈ T → g v (Multiplicative.ofAdd 0) = 0 := by sorry

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The selected finite zero-coordinate conditions cut out the span in (5.3.4.15).
Deviation: At the selected places its factors are the zero extensions of compactly
supported locally constant tests on the unit group. -/
theorem sAdeleFiniteZeroSchwartz_eq_span_tmul (T : Finset V) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdeleFiniteZeroSchwartz S T = Submodule.span ℂ {h : ℬₛ |
      ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∀ v : S, v.val ∈ T → g v (Multiplicative.ofAdd 0) = 0) ∧
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = h} := by sorry

/-- Paper: Definition 5.3.4.1, p. 259.
The slice definition equals the span of the corrected pure tensors in (5.3.4.1). Their
archimedean factor is flat and their finite factors vanish at zero. -/
theorem sAdelePolarFree_eq_span_tmul (r : RealModels) (c : ComplexModels) :
    let e := (sAdeleSchwartz_inductiveTensor_equiv F S).choose
    sAdelePolarFree S r c = Submodule.span ℂ {h : ℬₛ |
      ∃ (f : ℬ(A∞)) (g : ∀ v : S, ℬ(v.val.adicCompletion F)),
        (∃ f₀ : archimedeanFlatSchwartz (ι := RealPlaces) (κ := ComplexPlaces),
          ∀ x : ArchCoordinates, f₀.val x = f (Multiplicative.ofAdd (assemble(r, c, x)))) ∧
        (∀ v : S, g v (Multiplicative.ofAdd 0) = 0) ∧
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, g v)) = h} := by sorry

/-- Paper: Lemma 5.3.4.2(1), p. 260.
The polar-free functions form a closed subspace in the S-adelic Schwartz–Bruhat topology. -/
theorem sAdelePolarFree_isClosed (r : RealModels) (c : ComplexModels) :
    IsClosed (↑(sAdelePolarFree S r c) : Set ℬₛ) := by sorry

/-- Paper: Lemma 5.3.4.2(1), p. 260.
Inverse left translation by an S-idele preserves the polar-free subspace. -/
theorem sAdelePolarFree_translate (r : RealModels) (c : ComplexModels)
    (g : Aₛˣ) (f : ℬₛ) (_hf : f ∈ sAdelePolarFree S r c) :
    schwartzBruhatUnitTranslate g f ∈ sAdelePolarFree S r c := by sorry

/-- Paper: Lemma 5.3.4.2(1), p. 260.
The polar-free subspace is independent of the archimedean field identifications. -/
theorem sAdelePolarFree_eq_of_models (r r' : RealModels) (c c' : ComplexModels) :
    sAdelePolarFree S r c = sAdelePolarFree S r' c' := by sorry

-- TODO(paper-gap): The proof of (2) starts from entireness and concludes local vanishing.
-- Restricted local characters are coupled by the S-units, and a pole can cancel against
-- a zero of a different factor. The stated implication goes in the other direction.

/-- Paper: Lemma 5.3.4.2(2), p. 260.
The zeta transform of a polar-free test is entire on every norm-twist component. -/
theorem sLocalIdelicZFunction_entire_of_polarFree (r : RealModels) (c : ComplexModels)
    (f : ℬₛ) (_hf : f ∈ sAdelePolarFree S r c) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ := by sorry

/-- Paper: Lemma 5.3.4.2(3), p. 260.
A continuous quasi-character of the S-ideles trivial on S-units acts on polar-free
functions by pointwise multiplication and defines a linear homeomorphism.
The character is given on the S-idele quotient. -/
theorem sAdelePolarFree_quasiCharacter_mul (r : RealModels) (c : ComplexModels) (b : Xₛ) :
    ∃ M : ↥(sAdelePolarFree S r c) ≃L[ℂ] ↥(sAdelePolarFree S r c),
      ∀ f (g : Aₛˣ), (M f).val (Multiplicative.ofAdd g.val) =
        b (QuotientGroup.mk g) * f.val (Multiplicative.ofAdd g.val) := by sorry

-- TODO(paper-gap): In (5.3.4.9), the summation index m_v does not occur in the summand.
-- Norm-one class representatives with archimedean component one need not exist.

/-- Paper: Lemma 5.3.4.3, p. 261.
Every log-Schwartz function decaying at all real exponents lifts to a polar-free test
whose trivial homogeneous theta function is the given radial function. -/
theorem sLocalHomogeneousTheta_trivial_exists_polarFree (r : RealModels) (c : ComplexModels)
    (φ : PositiveRealExponentialDecay univ) :
    ∃ f : sAdelePolarFree S r c, ∀ g : Jₛ,
      thetaAt(1) f.val g = φ.val (Real.log ((mₛ g).val : ℝ)) := by sorry

/-- Paper: Proposition 5.3.4.4(1)–(2), p. 264.
On the component of χ, a zeta transform is entire exactly when it agrees there
with the transform of a polar-free test. -/
theorem sLocalIdelicZFunction_entire_iff_eq_polarFree (r : RealModels) (c : ComplexModels)
    (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ ↔
      ∃ f₀ : sAdelePolarFree S r c, ∀ s : ℂ,
        sLocalIdelicZFunction f (chartₛ(χ) s) = sLocalIdelicZFunction f₀.val (chartₛ(χ) s) := by sorry

/-- Paper: Proposition 5.3.4.4(1) and (3), p. 264.
On the component of χ, a zeta transform is entire exactly when the homogeneous theta
function has exponential decay at every real exponent. Its covariance is the
norm-one isotype property already supplied by §2.3. -/
theorem sLocalIdelicZFunction_entire_iff_theta_exponentialDecay (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s)) univ ↔
      (⇑(thetaAt(χ₁(χ)) f) : Jₛ → ℂ) ∈ modulatedExponentialDecaySubmodule
        ⟨mₛ, (isProperMap_sIdeleQuotientNorm F S).continuous⟩ univ := by sorry

/-- Paper: Proposition 5.3.4.5(1), p. 264.
Applying the principal value at selected finite places divides the zeta function
by their Euler factors as a meromorphic identity. -/
theorem sLocalIdelicZFunction_principalValue (T : Finset V) (hT : T ⊆ S)
    (f : ℬₛ) (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let c := chartₛ(χ) s
      sLocalIdelicZFunction (sAdelePrincipalValue F hT f) c =
        sLocalIdelicZFunction f c /
          ∏ v : S, if v.val ∈ T then finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)
            else 1 := by sorry

-- TODO(paper-gap): (5.3.4.14) gives the allowed pole multiplicity, which can exceed
-- the actual order. A local gamma factor contributes a positive multiplicity at a pole.

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The archimedean pole bound counts the local Euler factors with a pole on the
given norm-twist line at the given exponent. Each such pole is simple. -/
def sLocalArchimedeanPoleMultiplicity (χ : PontryaginDual Jₛ) (s : ℂ) : ℕ :=
  (Finset.univ.filter (fun w : InfinitePlace F ↦
    meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
      (sLocalInfiniteRestriction w (chartₛ(χ) z))) s < 0)).card

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The pole multiplicity is positive exactly at a pole of some pulled-back
archimedean Euler factor. -/
theorem sLocalArchimedeanPoleMultiplicity_pos_iff (χ : PontryaginDual Jₛ) (s : ℂ) :
    0 < sLocalArchimedeanPoleMultiplicity χ s ↔
      ∃ w : InfinitePlace F, meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
        (sLocalInfiniteRestriction w (chartₛ(χ) z))) s < 0 := by sorry

/-- Paper: Proposition 5.3.4.5(2), p. 264.
The negative of the allowed pole multiplicity is the sum of the negative parts
of the meromorphic orders of the local archimedean Euler factors. -/
theorem sLocalArchimedeanPoleMultiplicity_eq_sum (χ : PontryaginDual Jₛ) (s : ℂ) :
    (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) =
      ∑ w : InfinitePlace F, min 0
        (meromorphicOrderAt (fun z ↦ infiniteLocalEulerFactor w
          (sLocalInfiniteRestriction w (chartₛ(χ) z))) s) := by sorry

/-- Paper: Proposition 5.3.4.5(2), p. 264.
After all finite principal values, the zeta pole order is bounded by the total
archimedean Euler pole multiplicity.
Deviation: The assertion gives an upper bound since the input can cancel poles.
The multiplicity counts positive pole orders. -/
theorem sLocalIdelicZFunction_principalValue_pole_bound (f : ℬₛ)
    (χ : PontryaginDual Jₛ) (s : ℂ) :
    (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) ≤
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)) s := by sorry

/-- Paper: Proposition 5.3.4.5(2), p. 264.
On each component a choice of test realizes the full allowed archimedean pole divisor.
Deviation: Attainment is an existence assertion. The input can cancel any allowed pole. -/
theorem exists_sLocalIdelicZFunction_principalValue_attaining_poles (χ : PontryaginDual Jₛ) :
    ∃ f : ℬₛ, ∀ s : ℂ,
      meromorphicOrderAt (fun z ↦ sLocalIdelicZFunction
        (sAdelePrincipalValue F (Finset.Subset.refl S) f) (chartₛ(χ) z)) s =
        (↑(-(sLocalArchimedeanPoleMultiplicity χ s : ℤ)) : WithTop ℤ) := by sorry

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The subspace cut out by the selected finite zero-coordinate conditions is closed. -/
theorem sAdeleFiniteZeroSchwartz_isClosed (T : Finset V) :
    IsClosed (↑(sAdeleFiniteZeroSchwartz S T) : Set ℬₛ) := by sorry

local notation "thetaQuotient(" χ ")" => (LinearMap.ker (thetaAt(χ))).mkQ

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The principal value preserves the kernel of each homogeneous theta transform. -/
theorem sAdelePrincipalValue_preserves_homogeneousThetaKernel {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) :
    LinearMap.ker (thetaAt(ψ)) ≤
      (LinearMap.ker (thetaAt(ψ))).comap (sAdelePrincipalValue F hT) := by sorry

/-- Paper: Proposition 5.3.4.5(3), p. 264.
Weil's operator on homogeneous theta classes is induced by its action on tests. -/
def sLocalHomogeneousThetaPrincipalValue {T : Finset V} (hT : T ⊆ S) (ψ : PontryaginDual J₁) :
    SLocalHomogeneousThetaSpace F S ψ →ₗ[ℂ] SLocalHomogeneousThetaSpace F S ψ :=
  (LinearMap.ker (thetaAt(ψ))).mapQ (LinearMap.ker (thetaAt(ψ))) (sAdelePrincipalValue F hT)
    (sAdelePrincipalValue_preserves_homogeneousThetaKernel hT ψ)

/-- Paper: Proposition 5.3.4.5(3), p. 264.
On a homogeneous theta class the operator sends the representative to its principal value. -/
theorem sLocalHomogeneousThetaPrincipalValue_mk {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) (f : ℬₛ) :
    sLocalHomogeneousThetaPrincipalValue hT ψ (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (sAdelePrincipalValue F hT f) := rfl

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The closed embedding of Lemma 5.3.1.5 restricts to the homogeneous theta quotient,
identified with its isotype by §5.2. -/
theorem sLocalHomogeneousThetaPrincipalValue_isClosedEmbedding {T : Finset V} (hT : T ⊆ S)
    (ψ : PontryaginDual J₁) : IsClosedEmbedding (sLocalHomogeneousThetaPrincipalValue hT ψ) :=
  by sorry

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The principal value range in the homogeneous theta quotient is the image of tests
vanishing at the finite zero-coordinate hyperplanes. -/
theorem sLocalPrincipalValue_homogeneousTheta_range (χ : PontryaginDual Jₛ) :
    LinearMap.range (sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) χ₁(χ)) =
      (sAdeleFiniteZeroSchwartz S S).map (thetaQuotient(χ₁(χ))) := by sorry

/-- Paper: Proposition 5.3.4.5(3), p. 264.
The same homogeneous theta image is obtained by imposing finite zero-coordinate
vanishing only at the unramified places of χ. -/
theorem sLocalPrincipalValue_homogeneousTheta_range_unramified (χ : PontryaginDual Jₛ)
    (T : Finset V) (_hT : T ⊆ S)
    (_hχ : ∀ v : S, v.val ∈ T ↔ ∀ u : (v.val.adicCompletionIntegers F)ˣ,
      sLocalFiniteRestriction v (chartₛ(χ) 0)
        (Units.map (HeightOneSpectrum.adicCompletionIntegers F v.val).subtype.toMonoidHom u) = 1) :
    LinearMap.range (sLocalHomogeneousThetaPrincipalValue (Finset.Subset.refl S) χ₁(χ)) =
      (sAdeleFiniteZeroSchwartz S T).map (thetaQuotient(χ₁(χ))) := by sorry

end SAdele

end RiemannMasullo
