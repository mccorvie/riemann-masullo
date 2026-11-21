module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec2b
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Schwartz–Bergman spaces and Schwartz–Bruhat functions with exponential decay

Masullo, Appendix D, §§D.3.1–D.3.3.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function MeasureTheory Set Topology TopologicalSpace UniformSpace
open scoped ContDiff NNReal ENNReal SchwartzMap TensorProduct

section Bergman

/-- Paper: Lemma D.3.1.1, p. 797. Bounds for one polynomial weight on every
interior strip persist after taking any number of complex derivatives. -/
theorem verticalStrip_weighted_iteratedDeriv_bounded (a b : ℝ) (hab : a < b)
    (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f (Complex.re ⁻¹' Ioo a b)) (N : ℕ)
    (h : ∀ c d : ℝ, a < c → c < d → d < b →
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Ioo c d)))
    (k : ℕ) (c d : ℝ) (hac : a < c) (hcd : c < d) (hdb : d < b) :
    BddAbove ((fun z : ℂ ↦ ‖z ^ N * iteratedDeriv k f z‖) '' (Complex.re ⁻¹' Ioo c d)) :=
  by sorry

-- TODO(paper-gap): The proof's displayed denominator in (D.3.1.2) uses
-- σ + Re(z), although the real part of σ + iT - z is σ - Re(z).

/-- Paper: Definition D.3.1.3, p. 800. The strip conditions are closed under
the vector space operations. -/
theorem schwartzBergman_closure (I : Set ℝ) :
    let P (f : ℂ → ℂ) :=
      EqOn f 0 (Complex.re ⁻¹' I)ᶜ ∧ DifferentiableOn ℂ f (Complex.re ⁻¹' I) ∧
      ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ I → ∀ N : ℕ,
        BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Icc a b))
    P 0 ∧ (∀ {f g}, P f → P g → P (f + g)) ∧ (∀ c : ℂ, ∀ {f}, P f → P (c • f)) :=
  by sorry

/-- Paper: Definition D.3.1.3, p. 800. These are the holomorphic functions
with rapid decay on every bounded-width strip whose real closure is contained in the interval.
Deviation: Functions are extended by zero outside their strip to give a common carrier.
Bounds are tested on closed substrips, which is equivalent on an open interval. -/
def schwartzBergmanSubmodule (I : Set ℝ) : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | EqOn f 0 (Complex.re ⁻¹' I)ᶜ ∧ DifferentiableOn ℂ f (Complex.re ⁻¹' I) ∧
    ∀ (a b : ℝ), a ≤ b → Icc a b ⊆ I → ∀ N : ℕ,
      BddAbove ((fun z : ℂ ↦ ‖z ^ N * f z‖) '' (Complex.re ⁻¹' Icc a b))}
  zero_mem' := (schwartzBergman_closure I).1
  add_mem' := (schwartzBergman_closure I).2.1
  smul_mem' := (schwartzBergman_closure I).2.2

/-- Paper: Definition D.3.1.3, p. 800. The Gaussian restricted to a strip
gives a nonzero example whenever the strip is nonempty.
Deviation: Sanity check in the zero-extension representation. -/
theorem gaussian_mem_schwartzBergmanSubmodule (I : Set ℝ) (hI : IsOpen I) :
    (Complex.re ⁻¹' I).indicator (fun z : ℂ ↦ Complex.exp (z ^ 2)) ∈
      schwartzBergmanSubmodule I := by sorry

/-- Paper: (D.3.1.7), p. 799. Evaluate the polynomially weighted function on the
vertical line with real part a. -/
def weightedVerticalTrace (a : ℝ) (N : ℕ) (f : ℂ → ℂ) (x : ℝ) : ℂ :=
  let z : ℂ := (a : ℂ) + (x : ℂ) * Complex.I
  z ^ N * f z

/-- Paper: (D.3.1.7), p. 799. At zero height, the trace evaluates the weighted
function on the real axis. -/
theorem weightedVerticalTrace_zero_height (a : ℝ) (N : ℕ) (f : ℂ → ℂ) :
    weightedVerticalTrace a N f 0 = (a : ℂ) ^ N * f a := by sorry

/-- Paper: Lemma D.3.1.2, p. 799. Each polynomially weighted trace belongs to
the indicated Lᵖ space.
Deviation: The single-line bounds also give this for an endpoint when the
carrier is used with a closed interval. -/
theorem schwartzBergman_trace_memLp (I : Set ℝ) (a : I)
    (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) (N : ℕ) (f : schwartzBergmanSubmodule I) :
    MemLp (weightedVerticalTrace a N f.val) p volume := by sorry

/-- Paper: Definition D.3.1.3, p. 800. The weighted L² norm on one line
satisfies the seminorm laws. -/
theorem schwartzBergman_l2_seminorm (I : Set ℝ) (i : I × ℕ) :
    let q (f : schwartzBergmanSubmodule I) :=
      (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal
    (∀ f g, q (f + g) ≤ q f + q g) ∧ (∀ (c : ℂ) f, q (c • f) = ‖c‖ * q f) :=
  by sorry

-- TODO(paper-gap): Definition D.3.1.3 specifies positive rational abscissae
-- even for intervals contained in the negative half-line. Lemma D.3.1.2
-- instead uses real abscissae tending to both ends of the interval.

/-- Paper: Definition D.3.1.3, p. 800. Equip the Schwartz–Bergman
submodule with the topology of weighted L² convergence on interior vertical lines.
Deviation: Use all lines and p = 2 to make the choice-independent topology canonical.
Lemma D.3.1.2 identifies this with each of the paper's countable families. -/
abbrev SchwartzBergman (I : Set ℝ) :=
  WithGeneratingSeminorms (schwartzBergmanSubmodule I)
    (fun i : I × ℕ ↦ Seminorm.of
      (fun f : schwartzBergmanSubmodule I ↦
        (eLpNorm (weightedVerticalTrace i.1 i.2 f.val) 2 volume).toReal)
      (schwartzBergman_l2_seminorm I i).1 (schwartzBergman_l2_seminorm I i).2)

/-- Paper: Lemma D.3.1.2, p. 799. Weighted Lᵖ norms on a sequence of lines
reaching both ends of the interval generate the Schwartz–Bergman topology.
Deviation: The endpoint condition is expressed by bracketing every real point of I. -/
theorem schwartzBergman_lp_generates (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (a : ℕ → I)
    (ha : ∀ x : I, (∃ n, (a n : ℝ) < x) ∧ ∃ n, (x : ℝ) < a n)
    (p : ℝ≥0∞) (hp : 1 < p) (hp' : p < ⊤) :
    GeneratesLpSeminorms volume p
      (fun (i : ℕ × ℕ) (f : SchwartzBergman I) ↦ weightedVerticalTrace (a i.1) i.2 f.val) :=
  by sorry

/-- Paper: Lemma D.3.1.2, p. 799. The topology also comes from taking the
Schwartz restriction to each vertical line. -/
theorem schwartzBergman_schwartzLine_topology (I : Set ℝ) (hI : IsOpen I)
    (hInt : OrdConnected I) (hne : I.Nonempty) :
    ∃ T : SchwartzBergman I → (I → 𝓢(ℝ, ℂ)),
      (∀ f (a : I) x, T f a x = weightedVerticalTrace a 0 f.val x) ∧ IsEmbedding T :=
  by sorry

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is Fréchet. -/
theorem schwartzBergman_frechet (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : IsFrechetTVS (SchwartzBergman I) := by sorry

/-- Paper: Lemma D.3.1.2, p. 799. The Schwartz–Bergman space is separable. -/
theorem schwartzBergman_separable (I : Set ℝ) (hI : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) : SeparableSpace (SchwartzBergman I) := by sorry

end Bergman

section PositiveReal

/-- Paper: Definition D.3.2.1, p. 801. A real Schwartz map is viewed as a
function by the linear forgetful map. -/
def realSchwartzCoe : 𝓢(ℝ, ℂ) →ₗ[ℂ] (ℝ → ℂ) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Paper: Definition D.3.2.1, p. 801. Forgetting the Schwartz properties
retains the values of the function. -/
theorem realSchwartzCoe_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : realSchwartzCoe f x = f x := by sorry

/-- Paper: Definition D.3.2.1, p. 801. In logarithmic coordinates, weighting
by tᵃ amounts to multiplying by exp(ax). -/
def logExponentialWeight (a : ℝ) : (ℝ → ℂ) →ₗ[ℂ] (ℝ → ℂ) :=
  LinearMap.mulLeft ℂ (fun x : ℝ ↦ (Real.exp (a * x) : ℂ))

/-- Paper: Definition D.3.2.1, p. 801. The weight at exponent zero does not
change the function. -/
theorem logExponentialWeight_zero (f : ℝ → ℂ) : logExponentialWeight 0 f = f := by sorry

/-- Paper: Definition D.3.2.1, p. 801. A logarithmic profile belongs to the
decay submodule if each weighted profile is a real-line Schwartz function.
Deviation: The carrier is in the logarithmic coordinate x = log t. -/
def logExponentialDecaySubmodule (I : Set ℝ) : Submodule ℂ (ℝ → ℂ) :=
  ⨅ a : I, realSchwartzCoe.range.comap (logExponentialWeight a)

/-- Paper: Definition D.3.2.1, p. 801. The multiplier Tₐ is the weighted
profile, bundled as a Schwartz map. -/
theorem logExponentialDecay_weight_mem_range (I : Set ℝ)
    (a : I) (f : logExponentialDecaySubmodule I) :
    logExponentialWeight a f.val ∈ realSchwartzCoe.range := by sorry

/-- Paper: (D.3.2.1), p. 801. This is the linear multiplier to the space
of Schwartz functions in logarithmic coordinates. -/
def logExponentialDecayTwist (I : Set ℝ) (a : I) : logExponentialDecaySubmodule I →ₗ[ℂ] 𝓢(ℝ, ℂ) :=
  (LinearEquiv.ofInjective realSchwartzCoe DFunLike.coe_injective).symm.toLinearMap.comp
    (((logExponentialWeight a).comp (logExponentialDecaySubmodule I).subtype).codRestrict
      realSchwartzCoe.range (logExponentialDecay_weight_mem_range I a))

/-- Paper: (D.3.2.1), p. 801. The bundled multiplier evaluates to
exp(ax) times the original logarithmic profile. -/
theorem logExponentialDecayTwist_apply (I : Set ℝ) (a : I)
    (f : logExponentialDecaySubmodule I) (x : ℝ) :
    logExponentialDecayTwist I a f x = (Real.exp ((a : ℝ) * x) : ℂ) * f.val x := by sorry

/-- Paper: Definition D.3.2.1, p. 801. The topology is induced by
all weighted Schwartz profiles, using the usual seminorms on the real Schwartz space.
Deviation: Positive real functions are represented by their logarithmic profiles. -/
abbrev PositiveRealExponentialDecay (I : Set ℝ) :=
  WithGeneratingSeminorms (logExponentialDecaySubmodule I)
    (fun i : I × ℕ × ℕ ↦
      (SchwartzMap.seminorm ℂ i.2.1 i.2.2).comp (logExponentialDecayTwist I i.1))

/-- Paper: Definition D.3.2.1, p. 801. The family of weighted profiles embeds
the decay space in a product of real Schwartz spaces. -/
theorem positiveRealExponentialDecay_isEmbedding (I : Set ℝ) (hne : I.Nonempty) :
    IsEmbedding (fun (f : PositiveRealExponentialDecay I) (a : I) ↦
      logExponentialDecayTwist I a f) := by sorry

variable (I : Set ℝ)

local notation "E" => PositiveRealExponentialDecay I
local notation "D" => StrongDual ℂ E

/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space is Fréchet. -/
theorem positiveRealExponentialDecay_frechet (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsFrechetTVS E := by sorry

/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space is nuclear. -/
theorem positiveRealExponentialDecay_nuclear (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsNuclearTVS E := by sorry

/-- Paper: Lemma D.3.2.3(1), p. 801. The positive-real decay space has the
Montel property and is barrelled. -/
theorem positiveRealExponentialDecay_montel (hInt : OrdConnected I) (hne : I.Nonempty) :
    BarrelledSpace ℂ E ∧ MontelSpace ℂ E := by sorry

/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual is complete. -/
theorem positiveRealExponentialDecay_strongDual_complete (hInt : OrdConnected I) (hne : I.Nonempty) :
    CompleteSpace D := by sorry

/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual is nuclear. -/
theorem positiveRealExponentialDecay_strongDual_nuclear (hInt : OrdConnected I) (hne : I.Nonempty) :
    IsNuclearTVS D := by sorry

/-- Paper: Lemma D.3.2.3(2), p. 801. The strong dual has the Montel
property and is barrelled. -/
theorem positiveRealExponentialDecay_strongDual_montel (hInt : OrdConnected I) (hne : I.Nonempty) :
    BarrelledSpace ℂ D ∧ MontelSpace ℂ D := by sorry

/-- Paper: Lemma D.3.2.3(3), p. 801. If zero lies in I, the zero-weight
profile is a continuous linear inclusion into the ordinary Schwartz space. -/
theorem positiveRealExponentialDecay_continuous_inclusion (h0 : 0 ∈ I) :
    ∃ T : E →L[ℂ] 𝓢(ℝ, ℂ), Injective T ∧ ∀ f x, T f x = f.val x := by sorry

-- TODO(prerequisite): Lemma D.3.2.3(4–6) needs the three independently defined
-- subspaces from §B.2.1.1, Definition B.2.1.1.

/-- Paper: Proposition D.3.2.5, p. 802. On the strip, the positive-real Mellin
integral converges absolutely. The profile is pulled back by the real logarithm. -/
theorem positiveRealExponentialDecay_mellinConvergent (f : E) (s : ℂ) (hs : s.re ∈ I) :
    MellinConvergent (fun t ↦ f.val (Real.log t)) s := by sorry

/-- Paper: Proposition D.3.2.5, p. 802. The Mellin integral induces a unique
continuous linear equivalence with the Schwartz–Bergman space on the strip. -/
theorem existsUnique_positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) :
    ∃! M : E ≃L[ℂ] SchwartzBergman I, ∀ (f : E) (s : ℂ), s.re ∈ I →
      (M f).val s = mellin (fun t ↦ f.val (Real.log t)) s := by sorry

/-- Paper: Definition D.3.2.6, p. 803. The Fourier–Mellin transform is
the continuous linear equivalence furnished by the Mellin integral. -/
def positiveRealFourierMellin (hOpen : IsOpen I) (hInt : OrdConnected I) (hne : I.Nonempty) :
    E ≃L[ℂ] SchwartzBergman I :=
  Classical.choose (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists

/-- Paper: Definition D.3.2.6, p. 803. Evaluation of the Fourier–Mellin
transform on the strip gives the absolutely convergent Mellin integral. -/
theorem positiveRealFourierMellin_apply (hOpen : IsOpen I) (hInt : OrdConnected I)
    (hne : I.Nonempty) (f : E) (s : ℂ) (hs : s.re ∈ I) :
    (positiveRealFourierMellin I hOpen hInt hne f).val s =
      mellin (fun t ↦ f.val (Real.log t)) s := by sorry

/-- Paper: (D.3.2.3–4), p. 803. In logarithmic coordinates the weighted
L² norm is the norm of this exponentially and polynomially weighted derivative. -/
def exponentialDecayL2Integrand (a b : ℝ) (m : ℕ) (f : PositiveRealExponentialDecay univ)
    (x : ℝ) : ℂ :=
  ((Real.exp (a * |x|) * |x| ^ b : ℝ) : ℂ) * iteratedDeriv m f.val x

/-- Paper: (D.3.2.3–4), p. 803. At b = 0 the logarithmic power disappears,
leaving the pure exponential weight. -/
theorem exponentialDecayL2Integrand_zero_log (a : ℝ) (m : ℕ)
    (f : PositiveRealExponentialDecay univ) (x : ℝ) :
    exponentialDecayL2Integrand a 0 m f x =
      (Real.exp (a * |x|) : ℂ) * iteratedDeriv m f.val x := by sorry

/-- Paper: Lemma D.3.2.7(1), p. 803. Each weighted derivative is in L² and its
L² norm defines a continuous seminorm. The choice b = 0 includes (D.3.2.3). -/
theorem exponentialDecayL2_continuous_seminorm (a b : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (m : ℕ) :
    let w := exponentialDecayL2Integrand a b m
    (∀ f, MemLp (w f) 2 volume) ∧
      ∃ p : Seminorm ℂ (PositiveRealExponentialDecay univ), Continuous p ∧
        ∀ f, ENNReal.ofReal (p f) = eLpNorm (w f) 2 volume := by sorry

/-- Paper: Lemma D.3.2.7(2), p. 803. Exponential weights on an unbounded sequence
of positive exponents generate the topology. -/
theorem exponentialDecayL2_generates (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hunbounded : ¬ BddAbove (range a)) :
    GeneratesLpSeminorms volume 2
      (fun (i : ℕ × ℕ) ↦ exponentialDecayL2Integrand (a i.1) 0 i.2) := by sorry

/-- Paper: Lemma D.3.2.7(3), p. 803. The same topology is generated by including
all nonnegative integer logarithmic weights. -/
theorem exponentialDecayL2_log_generates (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hunbounded : ¬ BddAbove (range a)) :
    GeneratesLpSeminorms volume 2
      (fun (i : ℕ × ℕ × ℕ) ↦ exponentialDecayL2Integrand (a i.1) i.2.1 i.2.2) := by sorry

end PositiveReal

section Modulated

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (I : Set ℝ)

/-- Paper: Definition D.3.3.1, p. 804. Multiply a function by the real power
of the modulation at each point. -/
def modulationWeight (a : ℝ) : (G → ℂ) →ₗ[ℂ] (G → ℂ) :=
  LinearMap.mulLeft ℂ (fun g : G ↦ (((m g).val : ℝ) ^ a : ℝ))

/-- Paper: Definition D.3.3.1, p. 804. Weighting at exponent zero is
the identity. -/
theorem modulationWeight_zero (f : G → ℂ) : modulationWeight m 0 f = f := by sorry

/-- Paper: Definition D.3.3.1, p. 804. All real twists with exponents in I
must lie in the Schwartz–Bruhat submodule.
Forward, backward and two-sided exponential decay use `Ici 0`, `Iic 0` and `univ`.
Deviation: Continuity follows from any one twist when I is nonempty. -/
def modulatedExponentialDecaySubmodule : Submodule ℂ (G → ℂ) :=
  ⨅ a : I, (schwartzBruhatSubmodule G).comap (modulationWeight m a)

/-- Paper: Definition D.3.3.1, p. 804. The exponent set containing only zero
recovers the ordinary Schwartz–Bruhat functions. -/
theorem modulatedExponentialDecaySubmodule_singleton_zero :
    modulatedExponentialDecaySubmodule m {0} = schwartzBruhatSubmodule G := by sorry

/-- Paper: (D.3.3.2), p. 805. The given exponent supplies the corresponding
Schwartz–Bruhat membership. -/
theorem modulationWeight_mem_schwartzBruhat (a : I) (f : modulatedExponentialDecaySubmodule m I) :
    modulationWeight m a f.val ∈ schwartzBruhatSubmodule G := by sorry

/-- Paper: (D.3.3.2), p. 805. The linear map Tₐ sends a function in the decay
submodule to its weighted Schwartz–Bruhat function. -/
def modulatedExponentialDecayTwist (a : I) :
    modulatedExponentialDecaySubmodule m I →ₗ[ℂ] SchwartzBruhat G :=
  ((modulationWeight m a).comp (modulatedExponentialDecaySubmodule m I).subtype).codRestrict
    (schwartzBruhatSubmodule G) (modulationWeight_mem_schwartzBruhat m I a)

/-- Paper: (D.3.3.2), p. 805. The bundled twist evaluates to the pointwise
product with the power of the modulation. -/
theorem modulatedExponentialDecayTwist_apply (a : I) (f : modulatedExponentialDecaySubmodule m I)
    (g : G) :
    modulatedExponentialDecayTwist m I a f g = ((((m g).val : ℝ) ^ (a : ℝ) : ℝ) : ℂ) * f.val g :=
  by sorry

variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]

/-- Paper: Definition D.3.3.1, p. 804. Inverse left translation preserves
the decay submodule. -/
theorem modulatedExponentialDecaySubmodule_translate (hm : IsModulation m) (hms : Surjective m)
    (g : G) (f : modulatedExponentialDecaySubmodule m I) :
    (fun x : G ↦ f.val (g⁻¹ * x)) ∈ modulatedExponentialDecaySubmodule m I := by sorry

/-- Paper: Lemma D.3.3.2, p. 804. If two exponent twists are Schwartz–Bruhat,
every intermediate exponent twist is Schwartz–Bruhat as well. -/
theorem modulationWeight_mem_schwartzBruhat_between (hm : IsModulation m) (hms : Surjective m)
    (f : G → ℂ) (a c b : ℝ) (hac : a < c) (hcb : c < b)
    (ha : modulationWeight m a f ∈ schwartzBruhatSubmodule G)
    (hb : modulationWeight m b f ∈ schwartzBruhatSubmodule G) :
    modulationWeight m c f ∈ schwartzBruhatSubmodule G := by sorry

-- TODO(paper-gap): The finite-generation wording in Definition D.3.3.3
-- refers to the annihilator in the dual of the norm-one subgroup. In
-- the full dual the opening compact-generation condition applies.
local notation "GoodCompact" => {k : Subgroup G // IsCompact (k : Set G) ∧
  IsCompactlyGeneratedGroup (lcaAnnihilator k)}

/-- Paper: Definition D.3.3.3, p. 805. The modulation is trivial on each
compact subgroup because the positive-real group has no nontrivial compact subgroup. -/
theorem compactSubgroup_le_modulation_ker (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    k ≤ m.toMonoidHom.ker := by sorry

/-- Paper: Definition D.3.3.3, p. 805. The homomorphism induced by the
modulation on a compact-subgroup quotient is continuous. -/
theorem continuous_quotientModulation (k : Subgroup G) (hk : IsCompact (k : Set G)) :
    Continuous (QuotientGroup.lift k m.toMonoidHom (compactSubgroup_le_modulation_ker m k hk)) :=
  by sorry

/-- Paper: Definition D.3.3.3, p. 805. Use the descended modulation to form
the projective system on the quotient by a compact subgroup. -/
def quotientModulation (k : Subgroup G) (hk : IsCompact (k : Set G)) : (G ⧸ k) →ₜ* ℝ≥0ˣ where
  toMonoidHom := QuotientGroup.lift k m.toMonoidHom (compactSubgroup_le_modulation_ker m k hk)
  continuous_toFun := continuous_quotientModulation m k hk

/-- Paper: Definition D.3.3.3, p. 805. The descended modulation agrees with
the original one on each coset representative. -/
theorem quotientModulation_apply (k : Subgroup G) (hk : IsCompact (k : Set G)) (g : G) :
    quotientModulation m k hk (g : G ⧸ k) = m g := by sorry

/-- Paper: Definition D.3.3.3, p. 805. The stage S_I(k,G) carries the topology
induced by the Schwartz–Bruhat twists on G/k.
Deviation: The k-invariant functions are represented on the quotient. -/
abbrev ModulatedExponentialDecayStage (k : GoodCompact) :=
  let n := quotientModulation m k.val k.property.1
  WithGeneratingSeminorms (modulatedExponentialDecaySubmodule n I)
    (fun i : I × {p : Seminorm ℂ (SchwartzBruhat (G ⧸ k.val)) // Continuous p} ↦
      i.2.val.comp (modulatedExponentialDecayTwist n I i.1))

/-- Paper: Definition D.3.3.3, p. 805. Pulling a stage profile back along
the quotient map lands in the ambient decay submodule. -/
theorem modulatedExponentialDecayStage_pullback_mem (k : GoodCompact)
    (f : ModulatedExponentialDecayStage m I k) :
    (fun g : G ↦ f.val (g : G ⧸ k.val)) ∈ modulatedExponentialDecaySubmodule m I := by sorry

/-- Paper: (D.3.3.1), p. 805. The canonical stage map is pullback from G/k. -/
def modulatedExponentialDecayStageInclusion (k : GoodCompact) :
    ModulatedExponentialDecayStage m I k →ₗ[ℂ] modulatedExponentialDecaySubmodule m I :=
  ((LinearMap.pi fun g : G ↦ LinearMap.proj (g : G ⧸ k.val)).comp
    (modulatedExponentialDecaySubmodule (quotientModulation m k.val k.property.1) I).subtype
  ).codRestrict (modulatedExponentialDecaySubmodule m I)
    (modulatedExponentialDecayStage_pullback_mem m I k)

/-- Paper: (D.3.3.1), p. 805. A stage maps bijectively onto the k-invariant
functions in the ambient decay submodule. -/
theorem modulatedExponentialDecayStageInclusion_range (k : GoodCompact) :
    Injective (modulatedExponentialDecayStageInclusion m I k) ∧
      ∀ f : modulatedExponentialDecaySubmodule m I,
        f ∈ (modulatedExponentialDecayStageInclusion m I k).range ↔
          ∀ (g : G) (u : k.val), f.val (g * u.val) = f.val g := by sorry

/-- Paper: Definition D.3.3.3, p. 805. The topology of S_I(G) is the final
locally convex topology for the inclusions of the compact-subgroup stages. -/
abbrev ModulatedExponentialDecay :=
  WithGeneratingSeminorms (modulatedExponentialDecaySubmodule m I)
    (Subtype.val : {p : Seminorm ℂ (modulatedExponentialDecaySubmodule m I) //
      ∀ k : GoodCompact, Continuous (p ∘ modulatedExponentialDecayStageInclusion m I k)} → _)

/-- Paper: Definition D.3.3.3, p. 805. The stage inclusions exhaust the
underlying space. -/
theorem modulatedExponentialDecay_exists_stage (hm : IsModulation m) (hms : Surjective m)
    (hInt : OrdConnected I) (hne : I.Nonempty) :
    ∀ f : ModulatedExponentialDecay m I, ∃ k : GoodCompact,
      f ∈ (modulatedExponentialDecayStageInclusion m I k).range := by sorry

end Modulated

/-- Paper: Example D.3.3.4, p. 805. For the identity modulation, the inductive
space agrees with the positive-real projective space in logarithmic coordinates. -/
theorem identityModulationExponentialDecay_equiv (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) :
    ∃ e : PositiveRealExponentialDecay I ≃L[ℂ]
        ModulatedExponentialDecay (ContinuousMonoidHom.id ℝ≥0ˣ) I,
      ∀ (f : PositiveRealExponentialDecay I) (t : ℝ≥0ˣ),
        (e f).val t = f.val (Real.log (t.val : ℝ)) := by sorry

section ModulatedExamples

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)

local notation "GoodCompact" => {k : Subgroup G // IsCompact (k : Set G) ∧
  IsCompactlyGeneratedGroup (lcaAnnihilator k)}

include hm hms

/-- Paper: Example D.3.3.5, p. 805. Weighting by the difference of exponents
identifies the two singleton decay spaces.
Deviation: This includes the ordinary Schwartz–Bruhat case at exponent zero
via the continuous equivalence in the next declaration. -/
theorem modulatedExponentialDecay_singleton_equiv (a b : ℝ) :
    ∃ e : ModulatedExponentialDecay m {a} ≃L[ℂ] ModulatedExponentialDecay m {b},
      ∀ f, (e f).val = modulationWeight m (a - b) f.val := by sorry

/-- Paper: Example D.3.3.5, p. 805. Weighting by the given exponent identifies
the singleton decay space with the ordinary Schwartz–Bruhat space. -/
theorem modulatedExponentialDecay_singleton_schwartz (a : ℝ) :
    ∃ e : ModulatedExponentialDecay m {a} ≃L[ℂ] SchwartzBruhat G,
      ∀ f, (e f : G → ℂ) = modulationWeight m a f.val := by sorry

/-- Paper: Example D.3.3.5, p. 805. The diagonal map from a stage over a
compact interval to the two endpoint stages is a closed topological embedding. -/
theorem modulatedExponentialDecayStage_endpoints_closedEmbedding (k : GoodCompact)
    (a b : ℝ) (hab : a ≤ b) :
    ∃ T : ModulatedExponentialDecayStage m (Icc a b) k →L[ℂ]
        ModulatedExponentialDecayStage m {a} k × ModulatedExponentialDecayStage m {b} k,
      IsClosedEmbedding T ∧ ∀ f, (T f).1.val = f.val ∧ (T f).2.val = f.val := by sorry

/-- Paper: Example D.3.3.5, p. 805. For a nonempty interval, each stage is Fréchet. -/
theorem modulatedExponentialDecayStage_frechet (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    IsFrechetTVS (ModulatedExponentialDecayStage m I k) := by sorry

/-- Paper: Example D.3.3.5, p. 805. For a nonempty interval, each stage is nuclear. -/
theorem modulatedExponentialDecayStage_nuclear (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    IsNuclearTVS (ModulatedExponentialDecayStage m I k) := by sorry

/-- Paper: Example D.3.3.5, p. 805. For a nonempty interval, each stage is separable. -/
theorem modulatedExponentialDecayStage_separable (I : Set ℝ) (hInt : OrdConnected I)
    (hne : I.Nonempty) (k : GoodCompact) :
    SeparableSpace (ModulatedExponentialDecayStage m I k) := by sorry

end ModulatedExamples

-- The remaining part starts with the transition maps at the end of Example
-- D.3.3.5, p. 805.
-- TODO(paper-gap): Proposition D.3.3.10(3) misses included endpoints when
-- J only accumulates at them. On [0,1], translates of a fixed smooth bump
-- centered at n and scaled by exp(-n) are bounded at every a < 1, while the
-- a = 1 twists have an unbounded first polynomial Schwartz seminorm.
-- TODO(paper-gap): In Theorem D.3.3.13 the tensor formula requires the
-- Haar measures on the group and compact factor to be chosen compatibly.

end RiemannMasullo
