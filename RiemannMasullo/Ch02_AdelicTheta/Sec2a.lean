module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import RiemannMasullo.Ch02_AdelicTheta.Sec1
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn

/-!
# Global adelic theta functions

Masullo, §§2.2.1–2.2.3, pp. 74–86. The theta operator sums over nonzero field
elements, with the additive Tamagawa measure used for its Fourier identity.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

section Lattice

/-- Paper: Equation (2.2.1.1), p. 75. The shell consists of vectors with
supremum norm in the half-open interval of width one starting at `r`. -/
def euclideanSupNormShell (N : ℕ) (r : ℝ) : Set (Fin N → ℝ) :=
  {x | ‖x‖ ∈ Ico r (r + 1)}

/-- Paper: Equation (2.2.1.1), p. 75. In dimension one the shell uses the
absolute value of the single coordinate, with the outer endpoint excluded. -/
theorem mem_euclideanSupNormShell_one (x r : ℝ) :
    (fun _ : Fin 1 ↦ x) ∈ euclideanSupNormShell 1 r ↔ r ≤ |x| ∧ |x| < r + 1 := by sorry

/-- Paper: Lemma 2.2.1.1, p. 75. Each shell is bounded in the supremum norm. -/
theorem euclideanSupNormShell_bounded {N : ℕ} (_hN : 1 ≤ N) {r : ℝ} (_hr : 1 ≤ r) :
    IsBounded (euclideanSupNormShell N r) := by
  apply (Metric.isBounded_ball (x := (0 : Fin N → ℝ)) (r := r + 1)).subset
  intro x hx
  simpa only [Metric.mem_ball, dist_zero_right] using hx.2

/-- Paper: Lemma 2.2.1.1, p. 75. Each shell is measurable for completed
Lebesgue measure. -/
theorem euclideanSupNormShell_lebesgueMeasurable {N : ℕ} (_hN : 1 ≤ N) {r : ℝ}
    (_hr : 1 ≤ r) :
    NullMeasurableSet (euclideanSupNormShell N r) volume := by sorry

/-- Paper: Lemma 2.2.1.1, p. 75. For large radii, the shell has finitely many
lattice points and their number is at most a constant times `r ^ (N - 1)`. -/
theorem euclideanSupNormShell_lattice_count {N : ℕ} (_hN : 1 ≤ N)
    (Γ : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop,
      ((Γ : Set (Fin N → ℝ)) ∩ euclideanSupNormShell N r).Finite ∧
      (((Γ : Set (Fin N → ℝ)) ∩ euclideanSupNormShell N r).ncard : ℝ) ≤
        C * r ^ (N - 1) := by sorry

-- TODO(paper-gap): Proposition 2.2.1.3, p. 76, excludes Γ ∩ K from the sum,
-- but the term with ξ = -x can remain. Take Γ = ℤ, K = {1}, x = 1 and ξ = -1.

end Lattice

section Adelic

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "normℝ" => fun (g : C[F]) ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])

/-- Paper: Lemma 2.2.2.1, p. 77. The average sums the Schwartz–Bruhat function
at the adeles `g * (ξ + x)` as `ξ` ranges over the nonzero field elements. -/
def adelicAverage (f : ℬ[F]) (g : 𝕀[F]) (x : 𝔸[F]) : ℂ :=
  ∑' ξ : Fˣ, f (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] (ξ : F) + x)))

/-- Paper: Lemma 2.2.2.1, p. 77. The series of absolute values of the summands
in the adelic average converges uniformly on every compact set. -/
theorem adelicAverage_summableUniformlyOn (f : ℬ[F])
    (K : Set (𝕀[F] × 𝔸[F])) (hK : IsCompact K) :
    SummableUniformlyOn (fun (ξ : Fˣ) (p : 𝕀[F] × 𝔸[F]) ↦
      ‖f (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖) K := by sorry

/-- Paper: Lemma 2.2.2.1(1), p. 77. Adding the term at `ξ = 0` to the adelic
average gives the sum over all field elements. -/
theorem hasSum_adelicAverage_add_zeroTerm (f : ℬ[F]) (g : 𝕀[F]) (x : 𝔸[F]) :
    HasSum (fun ξ : F ↦ f (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] ξ + x))))
      (adelicAverage f g x + f (Multiplicative.ofAdd (g.val * x))) := by sorry

/-- Paper: Lemma 2.2.2.1(1), p. 77. The adelic average is jointly continuous in
the idele and adele arguments. -/
theorem adelicAverage_continuous (f : ℬ[F]) :
    Continuous (uncurry (adelicAverage f)) := by sorry

/-- Paper: Lemma 2.2.2.1(1), p. 77. The sum with the zero term included is
invariant under addition of a diagonal field element to the adele argument. -/
theorem adelicAverage_add_zeroTerm_add_principal (f : ℬ[F]) (g : 𝕀[F]) (x : 𝔸[F]) (a : F) :
    let y := algebraMap F 𝔸[F] a + x
    adelicAverage f g y + f (Multiplicative.ofAdd (g.val * y)) =
      adelicAverage f g x + f (Multiplicative.ofAdd (g.val * x)) := by sorry

/-- Paper: Lemma 2.2.2.1(2), p. 77. The adelic average at `x = 0` is continuous
as a function of the idele. -/
theorem adelicAverage_at_zero_continuous (f : ℬ[F]) :
    Continuous (fun g : 𝕀[F] ↦ adelicAverage f g 0) := by sorry

/-- Paper: Lemma 2.2.2.1(2), p. 77. The adelic average at `x = 0` is invariant
under multiplication by principal ideles.
Deviation: Invariance is expressed as constancy on the fibers of the quotient map. -/
theorem adelicAverage_at_zero_factorsThrough (f : ℬ[F]) :
    FactorsThrough (fun g : 𝕀[F] ↦ adelicAverage f g 0) classOf := by sorry

-- TODO(paper-gap): Lemma 2.2.2.1(3), pp. 77–78, bounds the whole idele sum
-- using an Archimedean restriction alone. Over ℚ, keep g∞ = 1 and take the
-- p-component p^m and all other finite components 1. For finite test function 1_Ẑ,
-- the contributing rationals lie in p^(-m) ℤ, so no fixed fractional ideal can
-- give the printed bound for a positive Archimedean bump near 0.

/-- Paper: Definition 2.2.3.1, p. 81. The global adelic theta function descends
the average at `x = 0` to a continuous function on the idele class group. -/
def adelicTheta (f : ℬ[F]) : C(C[F], ℂ) :=
  IsQuotientMap.lift (f := ⟨classOf, QuotientGroup.continuous_mk⟩)
    (QuotientGroup.isQuotientMap_mk (IdeleGroup.principalSubgroup (𝓞 F) F))
    ⟨fun g ↦ adelicAverage f g 0, adelicAverage_at_zero_continuous f⟩
    (adelicAverage_at_zero_factorsThrough f)

/-- Paper: Definition 2.2.3.1, p. 81. At the class of an idele, theta sums
the test function over its nonzero principal multiples. -/
theorem adelicTheta_mk (f : ℬ[F]) (g : 𝕀[F]) :
    adelicTheta f (classOf g) =
      ∑' ξ : Fˣ, f (Multiplicative.ofAdd (algebraMap F 𝔸[F] (ξ : F) * g.val)) := by sorry

/-- Paper: Definition 2.2.3.1, p. 82. Formation of the global adelic theta
function is complex linear. -/
theorem adelicTheta_isLinear : IsLinearMap ℂ (adelicTheta (F := F)) := by sorry

local instance : MeasurableSpace 𝔸[F] := borel _

/-- Paper: Theorem 2.2.3.2, p. 82. The Fourier integral for the standard adelic
character and the additive Tamagawa measure gives a Schwartz–Bruhat function. -/
theorem adeleSchwartzFourier_mem (f : ℬ[F]) :
    (fun y : Multiplicative 𝔸[F] ↦ tamagawaFourier (additiveTamagawaMeasure F)
      (adeleStandardCharacter F) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by sorry

/-- Paper: Theorem 2.2.3.2, p. 82. The Fourier transform in the theta identity
uses the trace character and the covolume-one measure of Appendix A. -/
def adeleSchwartzFourier (f : ℬ[F]) : ℬ[F] :=
  ⟨fun y ↦ tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
    (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd, adeleSchwartzFourier_mem f⟩

/-- Paper: Theorem 2.2.3.2, p. 82. The value of the Fourier transform at zero
is the integral of the Schwartz–Bruhat function, which is integrable. -/
theorem adeleSchwartzFourier_apply_zero (f : ℬ[F]) :
    Integrable (fun x ↦ f (Multiplicative.ofAdd x)) (additiveTamagawaMeasure F) ∧
    adeleSchwartzFourier f zeroAdele =
      ∫ x, f (Multiplicative.ofAdd x) ∂additiveTamagawaMeasure F := by sorry

/-- Paper: Theorem 2.2.3.2, p. 82. Adelic Riemann–Roch relates theta at an idele
class to the Fourier-transformed theta at its inverse, including the two zero terms. -/
theorem adelicTheta_riemannRoch (f : ℬ[F]) (g : C[F]) :
    adelicTheta f g = (normℝ g)⁻¹ • adelicTheta (adeleSchwartzFourier f) g⁻¹ +
      (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele := by sorry

/-- Paper: Theorem 2.2.3.4(1), p. 83. Theta decays faster than any inverse
power of the idele class norm as that norm tends to infinity. -/
theorem adelicTheta_decay_large (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < normℝ g →
      ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Theorem 2.2.3.4(2), p. 83. After subtracting the explicit polar
terms, theta decays faster than any power of the norm as it tends to zero. -/
theorem adelicTheta_decay_small (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], normℝ g < T →
      ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
        C * (normℝ g) ^ N := by sorry

/-- Paper: Theorem 2.2.3.4(3), p. 83. If both zero terms vanish, theta
decays at both ends at every exponential rate in the absolute logarithmic norm. -/
theorem adelicTheta_decay_both (f : ℬ[F]) (hf : f zeroAdele = 0)
    (hFourier : adeleSchwartzFourier f zeroAdele = 0) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < |Real.log (normℝ g)| →
      ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := by sorry

/-- Paper: Theorem 2.2.3.4(4), p. 83. The three decay estimates admit a common
constant and threshold uniform over a bounded set of Schwartz–Bruhat functions.
The two-sided estimate applies to members whose two zero terms vanish. -/
theorem adelicTheta_decay_bounded (B : Set ℬ[F]) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C[F],
      (T < normℝ g → ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (normℝ g < T →
        ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
          C * (normℝ g) ^ N) ∧
      (f zeroAdele = 0 → adeleSchwartzFourier f zeroAdele = 0 →
        Real.exp (-|Real.log (normℝ g)|) < T →
        ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) := by sorry

/-- Paper: Theorem 2.2.3.4(5), p. 83. The uniform estimates on a bounded set
hold with threshold one and a common constant. -/
theorem adelicTheta_decay_bounded_threshold_one (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : C[F],
      (1 < normℝ g → ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (normℝ g < 1 →
        ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
          C * (normℝ g) ^ N) ∧
      (f zeroAdele = 0 → adeleSchwartzFourier f zeroAdele = 0 →
        Real.exp (-|Real.log (normℝ g)|) < 1 →
        ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) := by sorry

end Adelic

end RiemannMasullo
