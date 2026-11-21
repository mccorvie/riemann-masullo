module

public import RiemannMasullo.AppC_LCTVS.Sec5a
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-!
# Spaces of smooth vector-valued functions

Masullo, Appendix C, §C.5.1.5. Periodic functions are represented on the Euclidean
cover. The uniform topology of Definition C.5.1.26 and the seminorm formulas of
Remark C.5.1.28 both appear, with their incompatibility recorded below.
-/

@[expose] public noncomputable section

open Bornology Filter Function Set Topology
open scoped ContDiff UniformConvergence

namespace RiemannMasullo

variable {d : ℕ} {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

local notation "V" => EuclideanSpace ℝ (Fin d)
local notation "eucInt" n => (WithLp.toLp 2 (fun i ↦ ((n i : ℤ) : ℝ)))

/-- Paper: Definition C.5.1.26(2), p. 735. A multi-index derivative is witnessed by
successive vector-valued lifts of weak coordinate derivatives in coordinate order. -/
def HasVectorMultiPartial (α : Fin d → ℕ) (f g : V → E) : Prop :=
  let rec hasPartials (h : V → E) : List (Fin d) → Prop
    | [] => h = g
    | i :: rest => ∃ h' : V → E,
        HasWeakPartialOn (k := ℝ) (Ω := univ) i h
          (fun x ↦ toPettisWeakCompletion E (h' x)) ∧ hasPartials h' rest
  hasPartials f (List.finRange d |>.flatMap fun i ↦ List.replicate (α i) i)

/-- Paper: Definition C.5.1.26(2), p. 735. The derivative for the zero multi-index
is the original function. -/
theorem hasVectorMultiPartial_zero_iff (f g : V → E) :
    HasVectorMultiPartial 0 f g ↔ f = g := by
  have h : (List.finRange d).flatMap (fun i ↦ List.replicate ((0 : Fin d → ℕ) i) i) = [] := by
    simp [List.flatMap_eq_nil_iff]
  unfold HasVectorMultiPartial
  rw [h]
  rfl

/-- Paper: Definition C.5.1.26(2), p. 735. Differentiating a coordinate function
once gives the corresponding entry of the identity matrix. -/
theorem hasVectorMultiPartial_coordinate (i j : Fin d) :
    HasVectorMultiPartial (Pi.single i 1) (fun x : V ↦ (x j : ℂ))
      (fun _ ↦ if i = j then (1 : ℂ) else 0) := by sorry

variable [hAdd : IsTopologicalAddGroup E] [hSMul : ContinuousSMul ℂ E]
  [hSemi : PolynormableSpace ℂ E] [hT2 : T2Space E]

variable (d E) in
/-- Paper: Definition C.5.1.26(1), p. 735. The periodic smooth space consists of the
smooth maps on the Euclidean cover fixed by every integer translation.
Deviation: The underlying submodule is available without assuming quasi-completeness. -/
def vectorPeriodicSmoothSubmodule : Submodule ℂ (V → E) :=
  (⨅ m : ℕ, vectorContDiffOrderSubmodule (E := E) (univ : Set V) m) ⊓
    ⨅ (n : Fin d → ℤ) (x : V), LinearMap.ker
      ((LinearMap.proj (x + eucInt n) : (V → E) →ₗ[ℂ] E) - LinearMap.proj x)

/-- Paper: Definition C.5.1.26(1), p. 735. On the complex scalar line as target,
membership means ordinary smoothness and invariance under the integer translations. -/
theorem mem_vectorPeriodicSmoothSubmodule_complex_iff (f : V → ℂ) :
    f ∈ vectorPeriodicSmoothSubmodule d ℂ ↔
      ContDiff ℝ ∞ f ∧ ∀ n : Fin d → ℤ, Periodic f (eucInt n) := by sorry

/-- Paper: Definition C.5.1.26(2), p. 735. Every mixed coordinate derivative,
multiplied by any complex polynomial in the real coordinates, has bounded range. -/
def HasVectorSchwartzDecay (f : V → E) : Prop :=
  ∀ (α : Fin d → ℕ) (p : MvPolynomial (Fin d) ℂ), ∃ g : V → E,
    HasVectorMultiPartial α f g ∧
      IsVonNBounded ℂ (range fun x : V ↦ p.eval (fun i ↦ (x i : ℂ)) • g x)

include hAdd hSMul in
/-- Paper: Definition C.5.1.26(2), p. 735. The zero function satisfies the
Schwartz bounds. -/
theorem hasVectorSchwartzDecay_zero : HasVectorSchwartzDecay (0 : V → E) := by sorry

include hAdd hSMul in
/-- Paper: Definition C.5.1.26(2), p. 735. The Schwartz bounds are stable
under addition. -/
theorem HasVectorSchwartzDecay.add {f g : V → E}
    (hf : HasVectorSchwartzDecay f) (hg : HasVectorSchwartzDecay g) :
    HasVectorSchwartzDecay (f + g) := by sorry

include hAdd hSMul in
/-- Paper: Definition C.5.1.26(2), p. 735. The Schwartz bounds are stable
under complex scalar multiplication. -/
theorem HasVectorSchwartzDecay.smul {f : V → E} (c : ℂ) (hf : HasVectorSchwartzDecay f) :
    HasVectorSchwartzDecay (c • f) := by sorry

variable (d E) in
/-- Paper: Definition C.5.1.26(2), p. 735. The vector-valued Schwartz space is the
subspace of smooth functions satisfying all polynomially weighted derivative bounds.
Deviation: The underlying submodule is available without assuming quasi-completeness. -/
def vectorSchwartzSubmodule : Submodule ℂ (V → E) :=
  (⨅ m : ℕ, vectorContDiffOrderSubmodule (E := E) (univ : Set V) m) ⊓
    { carrier := {f | HasVectorSchwartzDecay f}
      zero_mem' := hasVectorSchwartzDecay_zero
      add_mem' := HasVectorSchwartzDecay.add
      smul_mem' := fun c _ hf ↦ hf.smul c }

include hAdd hSMul hT2 in
/-- Paper: Definition C.5.1.26(2), p. 735. In positive dimension a nonzero constant
fails the bound with a linear coordinate weight. -/
theorem not_hasVectorSchwartzDecay_const (hd : 0 < d) {z : E} (hz : z ≠ 0) :
    ¬ HasVectorSchwartzDecay (fun _ : V ↦ z) := by sorry

/-- Paper: Definition C.5.1.26(2), p. 735. For scalar-valued functions, the carrier
of the Schwartz submodule agrees with Mathlib's Schwartz functions. -/
theorem mem_vectorSchwartzSubmodule_complex_iff (f : V → ℂ) :
    f ∈ vectorSchwartzSubmodule d ℂ ↔ ∃ g : SchwartzMap V ℂ, (g : V → ℂ) = f := by sorry

/-- Paper: Definition C.5.1.26(1–2), p. 735. The topology on either submodule
is induced by uniform convergence of function values in the additive uniformity of the target.
Periodic functions have the same uniform bounds on the cover and on the torus. -/
@[instance_reducible]
def uniformValueTopology {X : Type*} (S : Submodule ℂ (X → E)) : TopologicalSpace S :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  TopologicalSpace.induced (fun f : S ↦ (UniformFun.ofFun f.val : X →ᵤ E)) inferInstance

include hSMul hSemi hT2 in
/-- Paper: Definition C.5.1.26(1–2), p. 735. A family converges to zero in the
uniform value topology exactly when scalar convergence is uniform in both the argument
and the functional, for every equicontinuous set of functionals. -/
theorem tendsto_uniformValueTopology_zero_iff {X I : Type*} (S : Submodule ℂ (X → E))
    (l : Filter I) (f : I → S) :
    letI := uniformValueTopology S
    Tendsto f l (𝓝 0) ↔
      ∀ A : Set (StrongDual ℂ E), EquicontinuousAt (fun φ : A ↦ (φ.val : E → ℂ)) 0 →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ j in l, ∀ x : X, ∀ φ ∈ A, ‖φ ((f j).val x)‖ < ε := by sorry

include hT2 in
/-- Paper: Definition C.5.1.26(1–2), p. 735. The uniform value topology is Hausdorff. -/
theorem uniformValueTopology_t2Space {X : Type*} (S : Submodule ℂ (X → E)) :
    letI := uniformValueTopology S
    T2Space S := by sorry

variable (d E) in
/-- Paper: Remark C.5.1.27, p. 735. Each scalar evaluation of a weakly smooth
periodic map is a scalar smooth periodic function. -/
def weakPeriodicSmoothSubmodule : Submodule ℂ (V → E) :=
  ⨅ φ : StrongDual ℂ E, (vectorPeriodicSmoothSubmodule d ℂ).comap (φ.toLinearMap.compLeft V)

/-- Paper: Remark C.5.1.27, p. 735. The weak periodic condition tests ordinary
smoothness and integer translation invariance of each scalar evaluation. -/
theorem mem_weakPeriodicSmoothSubmodule_iff (f : V → E) :
    f ∈ weakPeriodicSmoothSubmodule d E ↔
      ∀ φ : StrongDual ℂ E, ContDiff ℝ ∞ (φ ∘ f) ∧
        ∀ n : Fin d → ℤ, Periodic (φ ∘ f) (eucInt n) := by sorry

variable (d E) in
/-- Paper: Remark C.5.1.27, p. 735. Each scalar evaluation of a weak Schwartz
function is a scalar Schwartz function. -/
def weakSchwartzSubmodule : Submodule ℂ (V → E) :=
  ⨅ φ : StrongDual ℂ E, (vectorSchwartzSubmodule d ℂ).comap (φ.toLinearMap.compLeft V)

/-- Paper: Remark C.5.1.27, p. 735. Every scalar evaluation of a weak Schwartz
function is represented by a Mathlib Schwartz map. -/
theorem mem_weakSchwartzSubmodule_iff (f : V → E) :
    f ∈ weakSchwartzSubmodule d E ↔
      ∀ φ : StrongDual ℂ E, ∃ g : SchwartzMap V ℂ, (g : V → ℂ) = φ ∘ f := by sorry

/-- Paper: Remark C.5.1.27, p. 735. In a quasi-complete target the two
definitions of the periodic smooth space agree. -/
theorem vectorPeriodicSmoothSubmodule_eq_weak :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      vectorPeriodicSmoothSubmodule d E = weakPeriodicSmoothSubmodule d E := by sorry

/-- Paper: Remark C.5.1.27, p. 735. In a quasi-complete target the two
definitions of the Schwartz space agree. -/
theorem vectorSchwartzSubmodule_eq_weak :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      vectorSchwartzSubmodule d E = weakSchwartzSubmodule d E := by sorry

-- TODO(paper-gap): The families in (C.5.1.45) and (C.5.1.46) do not generate
-- the printed topology. Already for scalar functions, uniform convergence of values
-- does not imply uniform convergence of first derivatives.

/-- Paper: Remark C.5.1.28, p. 735. The uniform value topology on periodic smooth
functions is locally convex. -/
theorem vectorPeriodicSmoothSubmodule_uniformValue_polynormable :
    letI : TopologicalSpace (vectorPeriodicSmoothSubmodule d E) :=
      uniformValueTopology (vectorPeriodicSmoothSubmodule d E)
    PolynormableSpace ℂ (vectorPeriodicSmoothSubmodule d E) := by sorry

/-- Paper: Remark C.5.1.28, p. 735. The uniform value topology on the Schwartz
submodule is locally convex. -/
theorem vectorSchwartzSubmodule_uniformValue_polynormable :
    letI : TopologicalSpace (vectorSchwartzSubmodule d E) :=
      uniformValueTopology (vectorSchwartzSubmodule d E)
    PolynormableSpace ℂ (vectorSchwartzSubmodule d E) := by sorry

/-- Paper: (C.5.1.45), p. 735. The supremum of a continuous seminorm on a mixed
derivative of a periodic smooth function is finite and defines a seminorm.
Deviation: The supremum is over the Euclidean cover of the torus. -/
theorem exists_vectorPeriodicSmoothDerivativeSeminorm (q : Seminorm ℂ E) (hq : Continuous q)
    (α : Fin d → ℕ) :
    ∃ s : Seminorm ℂ (vectorPeriodicSmoothSubmodule d E),
      ∀ f : vectorPeriodicSmoothSubmodule d E, ∃ g : V → E,
        HasVectorMultiPartial α f.val g ∧ BddAbove (range (q ∘ g)) ∧
          s f = ⨆ x : V, q (g x) := by sorry

/-- Paper: (C.5.1.46), p. 735. The supremum of a continuous seminorm on
a polynomially weighted mixed derivative is finite and defines a seminorm. -/
theorem exists_vectorSchwartzDerivativeSeminorm (q : Seminorm ℂ E) (hq : Continuous q)
    (α : Fin d → ℕ) (p : MvPolynomial (Fin d) ℂ) :
    ∃ s : Seminorm ℂ (vectorSchwartzSubmodule d E),
      ∀ f : vectorSchwartzSubmodule d E, ∃ g : V → E,
        HasVectorMultiPartial α f.val g ∧
          BddAbove (range fun x : V ↦ q (p.eval (fun i ↦ (x i : ℂ)) • g x)) ∧
          s f = ⨆ x : V, q (p.eval (fun i ↦ (x i : ℂ)) • g x) := by sorry

-- Remark C.5.1.29 on p. 736 repeats the weak definitions and equalities of Remark C.5.1.27.

-- TODO(paper-gap): C.5.1.30(1–3) fails even for E = ℂ with the uniform value topology.
-- Smooth uniform approximants to |sin(2πx)| on the torus and to χ(x)|x| on ℝ
-- are bounded and Cauchy but their limits are not differentiable at zero.

-- TODO(paper-gap): C.5.1.30(4), (C.5.1.47), needs a topology on C∞(Y)
-- and a compatible meaning of smoothness on the scalar and vector sides.
-- With ordinary scalar smoothness and continuous evaluation on C∞(Y),
-- currying (x,y) ↦ x² fails the vector order-zero condition.

-- TODO(paper-gap): C.5.1.30(4), (C.5.1.48), uses conflicting topologies on S.
-- With the printed topology the scalar S(Y) already fails the quasi-completeness
-- assumption of Definition C.5.1.26 for the target of the iterated space.
-- Even the weak definition in Remark C.5.1.27 with that topology allows
-- rapidly decaying families of slices with unbounded derivatives in Y.

end RiemannMasullo
