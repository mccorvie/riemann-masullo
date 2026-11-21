module

public import RiemannMasullo.AppC_LCTVS.Sec5a
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import RiemannMasullo.AppC_LCTVS.Sec1
import RiemannMasullo.ForMathlib.Analysis.Calculus.Deriv.Weak
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Partial
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.WeakSpace

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
      (fun _ ↦ if i = j then (1 : ℂ) else 0) := by
  have hIndices :
      (List.finRange d).flatMap (fun k ↦ List.replicate ((Pi.single i 1 : Fin d → ℕ) k) k) =
        [i] := by
    calc
      _ = (List.finRange d).filter (fun k ↦ decide (k = i)) := by
        rw [← List.filterMap_eq_filter, List.filterMap_eq_flatMap_toList]
        congr 1
        funext k
        by_cases hk : k = i <;> simp [Option.guard, hk]
      _ = [i] := by rw [List.filter_eq, List.count_finRange]; rfl
  unfold HasVectorMultiPartial
  rw [hIndices]
  refine ⟨fun _ ↦ if i = j then (1 : ℂ) else 0, ?_, rfl⟩
  intro φ x
  change HasDerivWithinAt _ (φ (if i = j then 1 else 0)) _ _
  apply HasDerivAt.hasDerivWithinAt
  let L : ℝ →L[ℝ] ℂ :=
    (if i = j then (1 : ℝ) else 0) • (φ.restrictScalars ℝ).comp Complex.ofRealCLM
  have hDeriv := (L.hasFDerivAt.hasDerivAt (x := 0)).const_add (φ ((x : V) j))
  by_cases hij : i = j <;>
    simpa [L, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, eq_comm (a := j), hij]
      using hDeriv

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

/-- At positive order, the scalar vector differentiability condition implies ordinary
continuous differentiability of that order. -/
private theorem contDiff_of_vectorContDiffOrderOn_succ (m : ℕ) {f : V → ℂ}
    (hf : VectorContDiffOrderOn (k := ℝ) f univ (m + 1)) :
    ContDiff ℝ (↑(m + 1 : ℕ)) f := by
  have step {m : ℕ} {f : V → ℂ} {g : Fin d → V → ℂ}
      (hg : ∀ i, HasWeakPartialOn (k := ℝ) (Ω := univ) i f
        (fun x ↦ toPettisWeakCompletion ℂ (g i x)))
      (hc : ∀ i, ContDiff ℝ (m : ℕ∞) (g i)) : ContDiff ℝ (↑(m + 1 : ℕ)) f := by
    have hderiv (x : V) : HasFDerivAt f
        (∑ i, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (g i x)) x := by
      refine hasFDerivAt_of_continuous_coordinate_derivatives g
        (fun i ↦ Eventually.of_forall fun y ↦ ?_) (fun i ↦ (hc i).continuous.continuousAt)
      have h := hg i (ContinuousLinearMap.id ℂ ℂ) ⟨y, mem_univ y⟩
      simpa [HasLineDerivAt, toPettisWeakCompletion_apply] using h
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    refine ⟨fun x ↦ (hderiv x).differentiableAt, by simp, ?_⟩
    have hformula : fderiv ℝ f = fun x ↦
        ∑ i, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (g i x) :=
      funext fun x ↦ (hderiv x).fderiv
    rw [hformula]
    exact ContDiff.sum fun i _ ↦
      (ContinuousLinearMap.smulRightL ℝ V ℂ (EuclideanSpace.proj i)).contDiff.comp (hc i)
  induction m generalizing f with
  | zero =>
    choose g hg hc _ using hf
    exact step hg fun i ↦ contDiff_zero.mpr (continuousOn_univ.mp (hc i))
  | succ m ih =>
    choose g hg _ horder using hf
    exact step hg fun i ↦ ih (horder i)

/-- The Fréchet derivative of an integer-periodic function has the same periods. -/
private theorem fderiv_integer_periodic {f : V → ℂ}
    (hp : ∀ n : Fin d → ℤ, Periodic f (eucInt n)) (n : Fin d → ℤ) :
    Periodic (fderiv ℝ f) (eucInt n) := by
  intro x
  rw [← fderiv_comp_add_right, show (fun y ↦ f (y + eucInt n)) = f from funext (hp n)]

/-- A smooth scalar periodic map satisfies the vector order condition at every finite order.
At order zero, the derivative bound on the unit cube controls all normalized differences. -/
private theorem vectorContDiffOrderOn_of_contDiff_periodic (m : ℕ) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (hp : ∀ n : Fin d → ℤ, Periodic f (eucInt n)) :
    VectorContDiffOrderOn (k := ℝ) f univ m := by
  induction m generalizing f with
  | zero =>
    have h' := contDiff_infty_iff_fderiv.mp hf
    let Q : Set (Fin d → ℝ) := univ.pi fun _ ↦ Icc 0 1
    have hQ : IsCompact Q := isCompact_univ_pi fun _ ↦ isCompact_Icc
    obtain ⟨C, hC⟩ := ((hQ.image (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ))).image
      h'.2.continuous).isBounded.exists_norm_le
    have hbound (x : V) : ‖fderiv ℝ f x‖ ≤ C := by
      let n : Fin d → ℤ := fun i ↦ ⌊x i⌋
      have hx : (x - eucInt n) ∈ WithLp.toLp 2 '' Q := by
        refine ⟨WithLp.ofLp (x - eucInt n), ?_, rfl⟩
        intro i _
        change x i - (⌊x i⌋ : ℝ) ∈ Icc 0 1
        exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
      have heq := fderiv_integer_periodic hp n (x - eucInt n)
      rw [sub_add_cancel] at heq
      rw [heq]
      exact hC _ (mem_image_of_mem _ hx)
    apply (NormedSpace.isVonNBounded_iff ℂ).mpr
    refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
    rintro _ ⟨x, _, y, _, hxy, _, rfl⟩
    have hnorm : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy.symm)
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hnorm),
      ← div_eq_inv_mul, div_le_iff₀ hnorm]
    exact (convex_univ : Convex ℝ (univ : Set V)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ h'.1 z) (fun z _ ↦ hbound z) (mem_univ x) (mem_univ y)
  | succ m ih =>
    have h' := contDiff_infty_iff_fderiv.mp hf
    intro i
    let v : V := EuclideanSpace.single i 1
    let g (x : V) := fderiv ℝ f x v
    have hg : ContDiff ℝ ∞ g := h'.2.clm_apply contDiff_const
    refine ⟨g, ?_, hg.continuous.continuousOn,
      ih hg (fun n x ↦ congrArg (fun L : V →L[ℝ] ℂ ↦ L v) (fderiv_integer_periodic hp n x))⟩
    intro φ x
    have h : HasLineDerivAt ℝ f (g x) x v := (h'.1 x).hasFDerivAt.hasLineDerivAt v
    change HasDerivWithinAt (fun t : ℝ ↦ φ (f ((x : V) + t • v))) (φ (g x)) _ 0
    exact ((φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h).hasDerivWithinAt

/-- Paper: Definition C.5.1.26(1), p. 735. On the complex scalar line as target,
membership means ordinary smoothness and invariance under the integer translations. -/
theorem mem_vectorPeriodicSmoothSubmodule_complex_iff (f : V → ℂ) :
    f ∈ vectorPeriodicSmoothSubmodule d ℂ ↔
      ContDiff ℝ ∞ f ∧ ∀ n : Fin d → ℤ, Periodic f (eucInt n) := by
  simp only [vectorPeriodicSmoothSubmodule, Submodule.mem_inf, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero, Periodic]
  constructor
  · rintro ⟨h, hp⟩
    refine ⟨contDiff_infty.mpr fun m ↦ ?_, hp⟩
    exact (contDiff_of_vectorContDiffOrderOn_succ m (h (m + 1))).of_le (by simp)
  · rintro ⟨hf, hp⟩
    exact ⟨fun m ↦ vectorContDiffOrderOn_of_contDiff_periodic m hf hp, hp⟩

/-- Paper: Definition C.5.1.26(2), p. 735. Every mixed coordinate derivative,
multiplied by any complex polynomial in the real coordinates, has bounded range. -/
def HasVectorSchwartzDecay (f : V → E) : Prop :=
  ∀ (α : Fin d → ℕ) (p : MvPolynomial (Fin d) ℂ), ∃ g : V → E,
    HasVectorMultiPartial α f g ∧
      IsVonNBounded ℂ (range fun x : V ↦ p.eval (fun i ↦ (x i : ℂ)) • g x)

omit hAdd hSMul hSemi hT2 in
/-- A chain of successive weak coordinate partials from zero to zero exists along every list of
coordinates. -/
private theorem hasPartials_zero :
    ∀ l : List (Fin d), HasVectorMultiPartial.hasPartials (0 : V → E) 0 l
  | [] => rfl
  | i :: rest => by
    refine ⟨0, fun φ x ↦ ?_, hasPartials_zero rest⟩
    change HasDerivWithinAt _ (φ ((0 : V → E) x)) _ _
    simpa only [Pi.zero_apply, map_zero] using hasDerivWithinAt_const (0 : ℝ) _ (0 : ℂ)

omit hAdd hSMul hSemi hT2 in
/-- Chains of successive weak coordinate partials add along a common list of coordinates. -/
private theorem hasPartials_add (g₁ g₂ : V → E) :
    ∀ (l : List (Fin d)) (h₁ h₂ : V → E), HasVectorMultiPartial.hasPartials g₁ h₁ l →
      HasVectorMultiPartial.hasPartials g₂ h₂ l →
        HasVectorMultiPartial.hasPartials (g₁ + g₂) (h₁ + h₂) l
  | [], _, _, e₁, e₂ => by
    change _ = _ at e₁ e₂
    change _ = _
    rw [e₁, e₂]
  | i :: rest, _, _, ⟨h₁', d₁, r₁⟩, ⟨h₂', d₂, r₂⟩ => by
    refine ⟨h₁' + h₂', fun φ x ↦ ?_, hasPartials_add g₁ g₂ rest _ _ r₁ r₂⟩
    have e₁ : HasDerivWithinAt _ (φ (h₁' x)) _ _ := d₁ φ x
    have e₂ : HasDerivWithinAt _ (φ (h₂' x)) _ _ := d₂ φ x
    change HasDerivWithinAt _ (φ ((h₁' + h₂') x)) _ _
    simpa only [Pi.add_apply, map_add, Pi.add_def] using e₁.add e₂

omit hAdd hSMul hSemi hT2 in
/-- Chains of successive weak coordinate partials scale along a common list of coordinates. -/
private theorem hasPartials_smul (c : ℂ) (g : V → E) :
    ∀ (l : List (Fin d)) (h : V → E), HasVectorMultiPartial.hasPartials g h l →
      HasVectorMultiPartial.hasPartials (c • g) (c • h) l
  | [], _, e => by
    change _ = _ at e
    change _ = _
    rw [e]
  | i :: rest, _, ⟨h', dh, r⟩ => by
    refine ⟨c • h', fun φ x ↦ ?_, hasPartials_smul c g rest _ r⟩
    have e : HasDerivWithinAt _ (φ (h' x)) _ _ := dh φ x
    change HasDerivWithinAt _ (φ ((c • h') x)) _ _
    simpa only [Pi.smul_apply, map_smul, Pi.smul_def] using HasDerivWithinAt.const_smul c e

include hAdd hSMul in
/-- Paper: Definition C.5.1.26(2), p. 735. The zero function satisfies the
Schwartz bounds. -/
theorem hasVectorSchwartzDecay_zero : HasVectorSchwartzDecay (0 : V → E) := by
  intro α p
  refine ⟨0, hasPartials_zero _, ?_⟩
  refine (isVonNBounded_singleton (0 : E)).subset ?_
  rintro _ ⟨x, rfl⟩
  simp

include hAdd hSMul in
/-- Paper: Definition C.5.1.26(2), p. 735. The Schwartz bounds are stable
under addition. -/
theorem HasVectorSchwartzDecay.add {f g : V → E}
    (hf : HasVectorSchwartzDecay f) (hg : HasVectorSchwartzDecay g) :
    HasVectorSchwartzDecay (f + g) := by
  intro α p
  obtain ⟨g₁, hg₁, b₁⟩ := hf α p
  obtain ⟨g₂, hg₂, b₂⟩ := hg α p
  refine ⟨g₁ + g₂, hasPartials_add g₁ g₂ _ f g hg₁ hg₂, (b₁.add b₂).subset ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, by simp [smul_add]⟩

include hAdd hSMul in
/-- Paper: Definition C.5.1.26(2), p. 735. The Schwartz bounds are stable
under complex scalar multiplication. -/
theorem HasVectorSchwartzDecay.smul {f : V → E} (c : ℂ) (hf : HasVectorSchwartzDecay f) :
    HasVectorSchwartzDecay (c • f) := by
  intro α p
  obtain ⟨g, hg, b⟩ := hf α p
  refine ⟨c • g, hasPartials_smul c g _ f hg, (b.image (c • ContinuousLinearMap.id ℂ E)).subset ?_⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨_, ⟨x, rfl⟩, by simp⟩

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
    ¬ HasVectorSchwartzDecay (fun _ : V ↦ z) := by
  intro h
  let i : Fin d := ⟨0, hd⟩
  obtain ⟨g, hg, hb⟩ := h 0 (MvPolynomial.X i)
  rw [← (hasVectorMultiPartial_zero_iff _ _).mp hg] at hb
  obtain ⟨r, hr, hsub⟩ := (hb (compl_singleton_mem_nhds hz.symm)).exists_pos
  have hmem : (r : ℂ) • z ∈ range (fun x : V ↦
      (MvPolynomial.X i).eval (fun j ↦ (x j : ℂ)) • z) := by
    exact ⟨EuclideanSpace.single i r, by simp [PiLp.single_apply]⟩
  have hnorm : r ≤ ‖(r : ℂ)‖ := by simp [abs_of_pos hr]
  have hzU := (Set.smul_mem_smul_set_iff₀ (Complex.ofReal_ne_zero.mpr hr.ne') _ _).mp
    (hsub (r : ℂ) hnorm hmem)
  exact hzU (mem_singleton z)

/-- On the complex line, testing with the identity recovers the ordinary coordinate derivative. -/
private theorem hasWeakPartialOn_complex_iff (i : Fin d) (f g : V → ℂ) :
    HasWeakPartialOn (k := ℝ) (Ω := univ) i f (fun x ↦ toPettisWeakCompletion ℂ (g x)) ↔
      ∀ x, HasLineDerivAt ℝ f (g x) x (EuclideanSpace.single i 1) := by
  have hset (x : V) : {t : ℝ | x + t • EuclideanSpace.single i 1 ∈ (univ : Set V)} =
      univ := by simp
  constructor
  · intro h x
    have hx := h (ContinuousLinearMap.id ℂ ℂ) ⟨x, mem_univ x⟩
    change HasDerivWithinAt _ (g x) {t : ℝ | x + t • EuclideanSpace.single i 1 ∈
      (univ : Set V)} 0 at hx
    rw [hset, hasDerivWithinAt_univ] at hx
    exact hx
  · intro h φ x
    change HasDerivWithinAt _ (φ (g x)) {t : ℝ | (x : V) + t •
      EuclideanSpace.single i 1 ∈ (univ : Set V)} 0
    rw [hset, hasDerivWithinAt_univ]
    exact (φ.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 (h x)

/-- Each vector differentiability order for complex-valued maps gives the corresponding
ordinary Fréchet differentiability order. -/
private theorem contDiff_of_vectorContDiffOrderOn_complex {f : V → ℂ} {m : ℕ}
    (hf : VectorContDiffOrderOn f univ m) : ContDiff ℝ m f := by
  induction m generalizing f with
  | zero =>
    rw [Nat.cast_zero, contDiff_zero]
    obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp hf
    refine continuous_iff_continuousAt.mpr fun x ↦ Metric.continuousAt_iff.mpr fun ε hε ↦ ?_
    refine ⟨min 1 (ε / (max C 0 + 1)), lt_min zero_lt_one (by positivity), fun y hy ↦ ?_⟩
    by_cases hxy : x = y
    · simpa [hxy] using hε
    have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
    rw [dist_eq_norm] at hy ⊢
    have hb := hC _ ⟨x, mem_univ x, y, mem_univ y, hxy,
      (hy.trans_le (min_le_left _ _)).le, rfl⟩
    have hnorm : ‖y - x‖⁻¹ * ‖f y - f x‖ ≤ C := by
      simpa only [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hd.le)]
        using hb
    have hle : ‖f y - f x‖ ≤ C * ‖y - x‖ := by
      rwa [mul_comm, ← div_eq_mul_inv, div_le_iff₀ hd] at hnorm
    calc
      ‖f y - f x‖ ≤ (max C 0 + 1) * ‖y - x‖ :=
        hle.trans (mul_le_mul_of_nonneg_right (by linarith [le_max_left C 0]) hd.le)
      _ < ε := (lt_div_iff₀' (by positivity : 0 < max C 0 + 1)).mp
        (hy.trans_le (min_le_right _ _))
  | succ m ih =>
    choose g hg hc hm using (show ∀ i : Fin d, ∃ g : V → ℂ,
      HasWeakPartialOn (k := ℝ) (Ω := univ) i f (fun x ↦ toPettisWeakCompletion ℂ (g x)) ∧
        ContinuousOn g univ ∧ VectorContDiffOrderOn g univ m from hf)
    have hD (x : V) : HasFDerivAt f
        (∑ i, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (g i x)) x :=
      hasFDerivAt_of_continuous_coordinate_derivatives g
        (fun i ↦ Eventually.of_forall ((hasWeakPartialOn_complex_iff i f (g i)).mp (hg i)))
        (fun i ↦ (continuousOn_univ.mp (hc i)).continuousAt)
    rw [Nat.cast_succ, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x ↦ (hD x).differentiableAt, by simp, fun v ↦ ?_⟩
    have heq : (fun x ↦ fderiv ℝ f x v) = fun x ↦ ∑ i, v i • g i x := by
      funext x
      simp [(hD x).fderiv]
    rw [heq]
    simpa only [Finset.sum_apply] using
      (ContDiff.sum (s := Finset.univ) fun i _ ↦ (ih (hm i)).const_smul (v i))

/-- Directional differentiation preserves the Schwartz conditions and hence every vector
differentiability order, including the uniform difference bound at order zero. -/
private theorem vectorContDiffOrderOn_of_schwartzMap (f : SchwartzMap V ℂ) (m : ℕ) :
    VectorContDiffOrderOn (f : V → ℂ) univ m := by
  induction m generalizing f with
  | zero =>
    obtain ⟨C, hC, hbound⟩ := f.decay 0 1
    let K : NNReal := ⟨C, hC.le⟩
    have hlip : LipschitzWith K f := lipschitzWith_of_nnNorm_fderiv_le f.differentiable fun x ↦ by
      change ‖fderiv ℝ (f : V → ℂ) x‖ ≤ C
      simpa [← norm_iteratedFDeriv_fderiv (n := 0)] using hbound x
    apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
    refine ⟨C, ?_⟩
    rintro z ⟨x, -, y, -, hxy, -, rfl⟩
    have hd : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hxy))
    rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr hd.le), mul_comm,
      ← div_eq_mul_inv, div_le_iff₀ hd]
    exact hlip.norm_sub_le y x
  | succ m ih =>
    intro i
    let g : SchwartzMap V ℂ := LineDeriv.lineDerivOp (EuclideanSpace.single i 1 : V) f
    refine ⟨g, (hasWeakPartialOn_complex_iff i f g).mpr (fun x ↦ ?_),
      g.continuous.continuousOn, ih g⟩
    exact (f.differentiable x).hasFDerivAt.hasLineDerivAt _

/-- Successive weak coordinate partials of a Schwartz function can all be represented by
Schwartz functions. -/
private theorem schwartzMap_hasPartials (f : SchwartzMap V ℂ) (l : List (Fin d)) :
    ∃ g : SchwartzMap V ℂ, HasVectorMultiPartial.hasPartials (g : V → ℂ) (f : V → ℂ) l := by
  induction l generalizing f with
  | nil => exact ⟨f, rfl⟩
  | cons i l ih =>
    let g : SchwartzMap V ℂ := LineDeriv.lineDerivOp (EuclideanSpace.single i 1 : V) f
    obtain ⟨h, hh⟩ := ih g
    exact ⟨h, g, (hasWeakPartialOn_complex_iff i f g).mpr (fun x ↦
      (f.differentiable x).hasFDerivAt.hasLineDerivAt _), hh⟩

/-- A polynomial in the real coordinates is a multiplier of temperate growth. -/
private theorem polynomial_hasTemperateGrowth (p : MvPolynomial (Fin d) ℂ) :
    Function.HasTemperateGrowth (fun x : V ↦ p.eval (fun i ↦ (x i : ℂ))) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval_C] using Function.HasTemperateGrowth.const (E := V) c
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul (Complex.ofRealCLM.comp (EuclideanSpace.proj (𝕜 := ℝ) i)).hasTemperateGrowth

/-- A Schwartz map satisfies all the polynomially weighted weak partial bounds. -/
private theorem hasVectorSchwartzDecay_of_schwartzMap (f : SchwartzMap V ℂ) :
    HasVectorSchwartzDecay (f : V → ℂ) := by
  intro α p
  obtain ⟨g, hg⟩ := schwartzMap_hasPartials f
    ((List.finRange d).flatMap fun i ↦ List.replicate (α i) i)
  let h := SchwartzMap.smulLeftCLM ℂ (fun x : V ↦ p.eval (fun i ↦ (x i : ℂ))) g
  have hh : (h : V → ℂ) = _ := SchwartzMap.smulLeftCLM_apply (polynomial_hasTemperateGrowth p) g
  refine ⟨g, hg, (NormedSpace.isVonNBounded_iff' ℂ).mpr
    ⟨SchwartzMap.seminorm ℂ 0 0 h, ?_⟩⟩
  rintro _ ⟨x, rfl⟩
  simpa only [hh] using h.norm_le_seminorm ℂ x

/-- The ordinary coordinate partial in direction `i` is the Fréchet derivative
evaluated at the corresponding basis vector. -/
private def coordPartial (f : V → ℂ) (i : Fin d) : V → ℂ :=
  fun x ↦ fderiv ℝ f x (EuclideanSpace.single i 1)

/-- The coordinate partial of a smooth function is smooth. -/
private theorem contDiff_coordPartial {f : V → ℂ} (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ContDiff ℝ ∞ (coordPartial f i) :=
  ((contDiff_infty_iff_fderiv.mp hf).2).clm_apply contDiff_const

/-- For a smooth function, each weak chain ends at the iterated ordinary coordinate partial. -/
private theorem hasPartials_eq_foldl (l : List (Fin d)) {f g : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (h : HasVectorMultiPartial.hasPartials g f l) :
    g = l.foldl coordPartial f := by
  induction l generalizing f with
  | nil => exact h.symm
  | cons i l ih =>
    obtain ⟨f', hf', hrest⟩ := h
    have heq : f' = coordPartial f i := by
      funext x
      have h₁ : HasDerivAt (fun t : ℝ ↦ f (x + t • EuclideanSpace.single i 1)) (f' x) 0 :=
        (hasWeakPartialOn_complex_iff i f f').mp hf' x
      have h₂ : HasDerivAt (fun t : ℝ ↦ f (x + t • EuclideanSpace.single i 1))
          (coordPartial f i x) 0 :=
        (hf.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _
      exact h₁.unique h₂
    subst f'
    exact ih (contDiff_coordPartial hf i) hrest

/-- For smooth functions the result of successive coordinate differentiation depends only
on the multiplicities of the coordinates. -/
private theorem foldl_coordPartial_eq_of_perm {l₁ l₂ : List (Fin d)} (h : l₁.Perm l₂)
    {f : V → ℂ} (hf : ContDiff ℝ ∞ f) :
    l₁.foldl coordPartial f = l₂.foldl coordPartial f := by
  induction h generalizing f with
  | nil => rfl
  | cons i _ ih => exact ih (contDiff_coordPartial hf i)
  | swap i j l =>
    have hswap : coordPartial (coordPartial f j) i = coordPartial (coordPartial f i) j := by
      funext x
      have hd : DifferentiableAt ℝ (fderiv ℝ f) x :=
        ((contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)) x
      let ev (k : Fin d) := ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single k (1 : ℝ))
      change fderiv ℝ (ev j ∘ fderiv ℝ f) x (EuclideanSpace.single i 1) =
        fderiv ℝ (ev i ∘ fderiv ℝ f) x (EuclideanSpace.single j 1)
      rw [(ev j).fderiv_comp_left hd, (ev i).fderiv_comp_left hd]
      exact (hf.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])).eq _ _
    simp only [List.foldl_cons, hswap]
  | trans _ _ ih₁ ih₂ => exact (ih₁ hf).trans (ih₂ hf)

/-- A list of coordinates is a permutation of the list grouped by its multiplicities. -/
private theorem perm_grouped_coordinates (l : List (Fin d)) :
    l.Perm ((List.finRange d).flatMap fun i ↦ List.replicate (l.count i) i) := by
  apply List.perm_iff_count.mpr
  intro i
  rw [List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
  rw [List.sum_map_ite]
  have hi : (List.finRange d).filter (fun j ↦ decide (j = i)) = [i] := by
    rw [List.filter_eq, List.count_finRange]
    rfl
  simp [hi]

/-- The Fréchet derivative evaluated on a coordinate tuple is the corresponding chain of
coordinate derivatives, starting with the last slot of the tuple. -/
private theorem iteratedFDeriv_apply_coordinates {n : ℕ} (v : Fin n → Fin d) {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (x : V) :
    iteratedFDeriv ℝ n f x (fun i ↦ EuclideanSpace.single (v i) 1) =
      ((List.ofFn v).reverse.foldl coordPartial f) x := by
  induction n generalizing f with
  | zero => simp [iteratedFDeriv_zero_eq_comp]
  | succ n ih =>
    rw [List.ofFn_succ', List.concat_eq_append, List.reverse_concat', List.foldl_cons, ← ih _ (contDiff_coordPartial hf _),
      iteratedFDeriv_succ_apply_right]
    let ev := ContinuousLinearMap.apply ℝ ℂ (EuclideanSpace.single (v (Fin.last n)) (1 : ℝ))
    change iteratedFDeriv ℝ n (fderiv ℝ f) x
        (fun i ↦ EuclideanSpace.single (v i.castSucc) 1) (EuclideanSpace.single (v (Fin.last n)) 1) =
      iteratedFDeriv ℝ n (ev ∘ fderiv ℝ f) x (fun i ↦ EuclideanSpace.single (v i.castSucc) 1)
    rw [ev.iteratedFDeriv_comp_left (contDiff_infty_iff_fderiv.mp hf).2.contDiffAt (by simp)]
    rfl

/-- Polynomial decay of the weak partials gives uniform norm-weighted bounds on the
Fréchet derivative evaluated at any fixed tuple of standard coordinate vectors. -/
private theorem coordinate_decay_of_hasVectorSchwartzDecay {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (h : HasVectorSchwartzDecay f) (k n : ℕ) (v : Fin n → Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖x‖ ^ k *
      ‖iteratedFDeriv ℝ n f x (fun i ↦ EuclideanSpace.single (v i) 1)‖ ≤ C := by
  let l := (List.ofFn v).reverse
  let p : MvPolynomial (Fin d) ℂ := (1 + ∑ i, MvPolynomial.X i ^ 2) ^ k
  obtain ⟨g, hg, hb⟩ := h (fun i ↦ l.count i) p
  have hg' : HasVectorMultiPartial.hasPartials g f
      ((List.finRange d).flatMap fun i ↦ List.replicate (l.count i) i) := by
    simpa only [HasVectorMultiPartial] using hg
  have heq := (foldl_coordPartial_eq_of_perm (perm_grouped_coordinates l) hf).trans
    (hasPartials_eq_foldl _ hf hg').symm
  obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp hb
  refine ⟨max C 0, le_max_right _ _, fun x ↦ ?_⟩
  rw [iteratedFDeriv_apply_coordinates v hf, show l.foldl coordPartial f x = g x from congrFun heq x]
  have hweight : ‖x‖ ^ k ≤ ‖p.eval (fun i ↦ (x i : ℂ))‖ := by
    have heval : p.eval (fun i ↦ (x i : ℂ)) = (((1 + ‖x‖ ^ 2) ^ k : ℝ) : ℂ) := by
      simp only [p, map_pow, map_add, map_sum, map_one, MvPolynomial.eval_X,
        EuclideanSpace.real_norm_sq_eq, Complex.ofReal_pow, Complex.ofReal_add,
        Complex.ofReal_one, Complex.ofReal_sum]
    rw [heval, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (by nlinarith [sq_nonneg (‖x‖ - 1)]) _
  calc
    _ ≤ ‖p.eval (fun i ↦ (x i : ℂ))‖ * ‖g x‖ :=
      mul_le_mul_of_nonneg_right hweight (norm_nonneg _)
    _ = ‖p.eval (fun i ↦ (x i : ℂ)) • g x‖ := (norm_smul _ _).symm
    _ ≤ C := hC _ (mem_range_self x)
    _ ≤ max C 0 := le_max_left _ _

/-- A uniform bound on the weighted coordinate evaluations controls the full operator norm
by expanding each argument in the standard Euclidean basis. -/
private theorem schwartz_decay_of_hasVectorSchwartzDecay {f : V → ℂ}
    (hf : ContDiff ℝ ∞ f) (h : HasVectorSchwartzDecay f) (k n : ℕ) :
    ∃ C : ℝ, ∀ x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤ C := by
  classical
  choose C hC hbound using coordinate_decay_of_hasVectorSchwartzDecay hf h k n
  refine ⟨∑ v, C v, fun x ↦ ?_⟩
  let A := ‖x‖ ^ k • iteratedFDeriv ℝ n f x
  have hA (v : Fin n → Fin d) : ‖A (fun i ↦ EuclideanSpace.single (v i) 1)‖ ≤ C v := by
    simpa [A, norm_smul, abs_of_nonneg (pow_nonneg (norm_nonneg x) k)] using hbound v x
  have hnorm : ‖A‖ ≤ ∑ v, C v := by
    apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun v _ ↦ hC v)
    intro m
    let e (i : Fin d) : V := EuclideanSpace.single i 1
    have hexpand : (fun i ↦ ∑ j, m i j • e j) = m := by
      funext i
      have hs := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (m i)
      change (∑ j, m i j • EuclideanSpace.basisFun (Fin d) ℝ j) = m i at hs
      simpa only [e, EuclideanSpace.basisFun_apply] using hs
    calc
      ‖A m‖ = ‖∑ v : Fin n → Fin d, (∏ i, m i (v i)) • A (fun i ↦ e (v i))‖ := by
        rw [show A m = A (fun i ↦ ∑ j, m i j • e j) from
          congrArg (fun a ↦ A a) hexpand.symm]
        rw [show A (fun i ↦ ∑ j, m i j • e j) = ∑ v : Fin n → Fin d,
          A (fun i ↦ m i (v i) • e (v i)) from A.toMultilinearMap.map_sum _]
        simp only [ContinuousMultilinearMap.map_smul_univ]
      _ ≤ ∑ v : Fin n → Fin d, ‖(∏ i, m i (v i)) • A (fun i ↦ e (v i))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ v : Fin n → Fin d, (∏ i, ‖m i‖) * C v := by
        apply Finset.sum_le_sum
        intro v _
        rw [norm_smul, norm_prod]
        exact mul_le_mul
          (Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ PiLp.norm_apply_le _ _)
          (hA v) (norm_nonneg _) (by positivity)
      _ = _ := by rw [mul_comm (∑ v, C v), Finset.mul_sum]
  simpa [A, norm_smul, abs_of_nonneg (pow_nonneg (norm_nonneg x) k)] using hnorm

/-- Paper: Definition C.5.1.26(2), p. 735. For scalar-valued functions, the carrier
of the Schwartz submodule agrees with Mathlib's Schwartz functions. -/
theorem mem_vectorSchwartzSubmodule_complex_iff (f : V → ℂ) :
    f ∈ vectorSchwartzSubmodule d ℂ ↔ ∃ g : SchwartzMap V ℂ, (g : V → ℂ) = f := by
  rw [vectorSchwartzSubmodule, Submodule.mem_inf, Submodule.mem_iInf]
  change ((∀ m, VectorContDiffOrderOn f univ m) ∧ HasVectorSchwartzDecay f) ↔ _
  constructor
  · rintro ⟨hm, hd⟩
    have hf := contDiff_infty.mpr (fun m ↦ contDiff_of_vectorContDiffOrderOn_complex (hm m))
    exact ⟨⟨f, hf, schwartz_decay_of_hasVectorSchwartzDecay hf hd⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨vectorContDiffOrderOn_of_schwartzMap g, hasVectorSchwartzDecay_of_schwartzMap g⟩

/-- Paper: Definition C.5.1.26(1–2), p. 735. The topology on either submodule
is induced by uniform convergence of function values in the additive uniformity of the target.
Periodic functions have the same uniform bounds on the cover and on the torus. -/
@[instance_reducible]
def uniformValueTopology {X : Type*} (S : Submodule ℂ (X → E)) : TopologicalSpace S :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  TopologicalSpace.induced (fun f : S ↦ (UniformFun.ofFun f.val : X →ᵤ E)) inferInstance

-- Retain the continuous scalar multiplication and Hausdorff assumptions in the signature.
set_option linter.unusedSectionVars false in
include hSMul hSemi hT2 in
/-- Paper: Definition C.5.1.26(1–2), p. 735. A family converges to zero in the
uniform value topology exactly when scalar convergence is uniform in both the argument
and the functional, for every equicontinuous set of functionals. -/
theorem tendsto_uniformValueTopology_zero_iff {X I : Type*} (S : Submodule ℂ (X → E))
    (l : Filter I) (f : I → S) :
    letI := uniformValueTopology S
    Tendsto f l (𝓝 0) ↔
      ∀ A : Set (StrongDual ℂ E), EquicontinuousAt (fun φ : A ↦ (φ.val : E → ℂ)) 0 →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ j in l, ∀ x : X, ∀ φ ∈ A, ‖φ ((f j).val x)‖ < ε := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  have : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  have hb := UniformFun.hasBasis_nhds_of_basis X E (UniformFun.ofFun (0 : X → E))
    (𝓝 (0 : E)).basis_sets.uniformity_of_nhds_zero
  simp only [nhds_induced, tendsto_comap_iff, hb.tendsto_right_iff,
    Function.comp_def, Set.mem_ofPred_eq, UniformFun.gen, UniformFun.toFun_ofFun,
    Submodule.coe_zero, Pi.zero_apply, sub_zero]
  constructor
  · intro h A hA ε hε
    have hnear : (∀ᶠ y in 𝓝 (0 : E), ∀ φ : A, ‖φ.val y‖ < ε) := by
      simpa only [map_zero, dist_zero_left] using Metric.equicontinuousAt_iff_right.mp hA ε hε
    filter_upwards [h _ hnear] with j hj x φ hφ
    exact hj x ⟨φ, hφ⟩
  · intro h U hU
    obtain ⟨p, hp, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
    let A : Set (StrongDual ℂ E) := {φ | ∀ y, ‖φ y‖ ≤ p y}
    have hA : EquicontinuousAt (fun φ : A ↦ (φ.val : E → ℂ)) 0 := by
      rw [Metric.equicontinuousAt_iff_right]
      intro ε hε
      filter_upwards [p.ball_mem_nhds hp hε] with y hy φ
      simpa only [map_zero, dist_zero_left] using
        (φ.property y).trans_lt (p.mem_ball_zero.mp hy)
    filter_upwards [h A hA 1 one_pos] with j hj x
    obtain ⟨φ, hφ, hEq⟩ := exists_dual_norm_eq_seminorm p hp ((f j).val x)
    exact hpU (p.mem_ball_zero.mpr (hEq ▸ hj x φ hφ))

include hT2 in
/-- Paper: Definition C.5.1.26(1–2), p. 735. The uniform value topology is Hausdorff. -/
theorem uniformValueTopology_t2Space {X : Type*} (S : Submodule ℂ (X → E)) :
    letI := uniformValueTopology S
    T2Space S := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  let := uniformValueTopology S
  exact IsEmbedding.t2Space ⟨⟨rfl⟩, fun f g h ↦ Subtype.ext (UniformFun.ofFun.injective h)⟩

variable (d E) in
/-- Paper: Remark C.5.1.27, p. 735. Each scalar evaluation of a weakly smooth
periodic map is a scalar smooth periodic function. -/
def weakPeriodicSmoothSubmodule : Submodule ℂ (V → E) :=
  ⨅ φ : StrongDual ℂ E, (vectorPeriodicSmoothSubmodule d ℂ).comap (φ.toLinearMap.compLeft V)

-- Retain the section instances in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Remark C.5.1.27, p. 735. The weak periodic condition tests ordinary
smoothness and integer translation invariance of each scalar evaluation. -/
theorem mem_weakPeriodicSmoothSubmodule_iff (f : V → E) :
    f ∈ weakPeriodicSmoothSubmodule d E ↔
      ∀ φ : StrongDual ℂ E, ContDiff ℝ ∞ (φ ∘ f) ∧
        ∀ n : Fin d → ℤ, Periodic (φ ∘ f) (eucInt n) := by
  rw [weakPeriodicSmoothSubmodule, Submodule.mem_iInf]
  exact forall_congr' fun φ ↦
    Submodule.mem_comap.trans (mem_vectorPeriodicSmoothSubmodule_complex_iff (φ ∘ f))

variable (d E) in
/-- Paper: Remark C.5.1.27, p. 735. Each scalar evaluation of a weak Schwartz
function is a scalar Schwartz function. -/
def weakSchwartzSubmodule : Submodule ℂ (V → E) :=
  ⨅ φ : StrongDual ℂ E, (vectorSchwartzSubmodule d ℂ).comap (φ.toLinearMap.compLeft V)

/-- Paper: Remark C.5.1.27, p. 735. Every scalar evaluation of a weak Schwartz
function is represented by a Mathlib Schwartz map. -/
theorem mem_weakSchwartzSubmodule_iff (f : V → E) :
    f ∈ weakSchwartzSubmodule d E ↔
      ∀ φ : StrongDual ℂ E, ∃ g : SchwartzMap V ℂ, (g : V → ℂ) = φ ∘ f := by
  rw [weakSchwartzSubmodule, Submodule.mem_iInf]
  simp only [Submodule.mem_comap]
  change (∀ φ : StrongDual ℂ E, φ ∘ f ∈ vectorSchwartzSubmodule d ℂ) ↔ _
  exact forall_congr' fun φ ↦ mem_vectorSchwartzSubmodule_complex_iff (φ ∘ f)

omit hAdd hSMul hSemi hT2 in
/-- Scalar evaluation preserves each order of vector differentiability on the Euclidean cover. -/
private theorem vectorContDiffOrderOn_univ_comp_dual (φ : StrongDual ℂ E) (m : ℕ) {f : V → E}
    (hf : VectorContDiffOrderOn (k := ℝ) f univ m) :
    VectorContDiffOrderOn (k := ℝ) (φ ∘ f) univ m := by
  induction m generalizing f with
  | zero =>
    unfold VectorContDiffOrderOn at hf ⊢
    apply (hf.image φ).subset
    rintro _ ⟨x, hx, y, hy, hxy, hdist, rfl⟩
    exact ⟨_, ⟨x, hx, y, hy, hxy, hdist, rfl⟩, by simp⟩
  | succ m ih =>
    intro i
    obtain ⟨g, hg, hc, hm⟩ := hf i
    refine ⟨φ ∘ g, ?_, φ.continuous.comp_continuousOn hc, ih hm⟩
    intro ψ x
    exact hg (ψ.comp φ) x

/-- If all scalar evaluations are smooth and periodic, the vector map has bounded normalized
differences and is continuous. -/
private theorem periodic_order_zero_of_scalar {f : V → E}
    (hf : ∀ φ : StrongDual ℂ E, ContDiff ℝ ∞ (φ ∘ f) ∧
      ∀ n : Fin d → ℤ, Periodic (φ ∘ f) (eucInt n)) :
    VectorContDiffOrderOn (k := ℝ) f univ 0 ∧ Continuous f := by
  have hb : VectorContDiffOrderOn (k := ℝ) f univ 0 := by
    unfold VectorContDiffOrderOn
    apply (isVonNBounded_iff_dual_image _).mpr
    intro φ
    have hφ := vectorContDiffOrderOn_of_contDiff_periodic 0 (hf φ).1 (hf φ).2
    unfold VectorContDiffOrderOn at hφ
    apply ((NormedSpace.isVonNBounded_iff ℂ).mp hφ).subset
    rintro _ ⟨_, ⟨x, hx, y, hy, hxy, hdist, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, hxy, hdist, by simp⟩
  refine ⟨hb, continuous_iff_continuousAt.mpr fun x ↦ ?_⟩
  change Tendsto f (𝓝 x) (𝓝 (f x))
  apply tendsto_sub_nhds_zero_iff.mp
  let r (y : V) : ℂ := (‖y - x‖ : ℝ)
  let q (y : V) : E := (r y)⁻¹ • (f y - f x)
  have hr : Tendsto r (𝓝 x) (𝓝 0) := by
    have h : Tendsto (fun y : V ↦ ‖y - x‖) (𝓝 x) (𝓝 0) := by
      simpa using (continuousAt_id.sub (continuousAt_const (y := x))).norm.tendsto (x := x)
    simpa [r, Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h
  unfold VectorContDiffOrderOn at hb
  have hsmall : ∀ᶠ y in 𝓝 x, ‖y - x‖ < 1 :=
    Metric.eventually_nhds_iff_ball.mpr ⟨1, zero_lt_one, fun y hy ↦ by
      simpa [Metric.mem_ball, dist_eq_norm] using hy⟩
  refine ((hb.union (isVonNBounded_singleton (0 : E))).smul_tendsto_zero
    (x := q) (hsmall.mono fun y hy ↦ ?_) hr).congr fun y ↦ ?_
  · by_cases h : y = x
    · right
      simp [q, h]
    · left
      exact ⟨x, mem_univ _, y, mem_univ _, Ne.symm h, hy.le, by simp [q, r]⟩
  · change r y • ((r y)⁻¹ • (f y - f x)) = f y - f x
    by_cases h : y = x
    · simp [h]
    · exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h))) _

/-- In a quasi-complete target, a coordinate derivative has an E-valued representative if every
scalar evaluation is twice continuously differentiable. The scalar Taylor remainder bounds the
differences of the vector difference quotients after rescaling. -/
private theorem exists_vector_coordinate_lift {f : V → E}
    (hf : ∀ φ : StrongDual ℂ E, ContDiff ℝ 2 (φ ∘ f)) (i : Fin d) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      ∃ g : V → E, ∀ (φ : StrongDual ℂ E) (x : V),
        φ (g x) = fderiv ℝ (φ ∘ f) x (EuclideanSpace.single i 1) := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : IsUniformAddGroup E := isUniformAddGroup_of_addCommGroup
  intro hcomplete
  have hpoint (x : V) : ∃ y : E, ∀ φ : StrongDual ℂ E,
      φ y = fderiv ℝ (φ ∘ f) x (EuclideanSpace.single i 1) := by
    let v : V := EuclideanSpace.single i 1
    let F (φ : StrongDual ℂ E) (s : ℝ) := φ (f (x + s • v))
    let t (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹
    let q (n : ℕ) : E := (((t n)⁻¹ : ℝ) : ℂ) • (f (x + t n • v) - f x)
    have htpos (n : ℕ) : 0 < t n := by positivity
    have htone (n : ℕ) : t n ≤ 1 := by
      apply inv_le_one_of_one_le₀
      exact le_add_of_nonneg_left (Nat.cast_nonneg n)
    have ht : Tendsto t atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    have hline : ContDiff ℝ 2 (fun s : ℝ ↦ x + s • v) :=
      contDiff_const.add (contDiff_id.smul contDiff_const)
    have hq (φ : StrongDual ℂ E) (n : ℕ) :
        φ (q n) = (t n)⁻¹ • (F φ (t n) - F φ 0) := by
      simp [q, F, Complex.real_smul]
    have hderiv (φ : StrongDual ℂ E) :
        HasDerivAt (F φ) (fderiv ℝ (φ ∘ f) x v) 0 :=
      ((hf φ).differentiable (by simp) x).hasFDerivAt.hasLineDerivAt v
    have hscalar (φ : StrongDual ℂ E) : Tendsto (φ ∘ q) atTop
        (𝓝 (fderiv ℝ (φ ∘ f) x v)) := by
      refine ((hderiv φ).tendsto_slope_zero.comp (tendsto_nhdsWithin_iff.mpr
        ⟨ht, Eventually.of_forall fun n ↦ (htpos n).ne'⟩)).congr ?_
      intro n
      simpa only [zero_add, Function.comp_apply] using (hq φ n).symm
    have hb : IsVonNBounded ℂ (range q) := by
      apply (isVonNBounded_iff_dual_image _).mpr
      intro φ
      rw [← range_comp]
      exact (NormedSpace.isVonNBounded_iff ℂ).mp ((hscalar φ).isVonNBounded_range ℂ)
    let r (p : ℕ × ℕ) : ℝ := t p.1 + t p.2
    let z (p : ℕ × ℕ) : E := (((r p)⁻¹ : ℝ) : ℂ) • (q p.2 - q p.1)
    have hrpos (p : ℕ × ℕ) : 0 < r p := add_pos (htpos _) (htpos _)
    have hz : IsVonNBounded ℂ (range z) := by
      apply (isVonNBounded_iff_dual_image _).mpr
      intro φ
      have hF : ContDiffOn ℝ 2 (F φ) (Icc 0 1) := ((hf φ).comp hline).contDiffOn
      obtain ⟨C, hC⟩ := exists_taylor_mean_remainder_bound (n := 1) hF
      have hTaylor (s : ℝ) :
          taylorWithinEval (F φ) 1 (Icc 0 1) 0 s =
            F φ 0 + s • fderiv ℝ (φ ∘ f) x v := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, taylorWithinEval_succ, taylor_within_zero_eval]
        simp [iteratedDerivWithin_one, (hderiv φ).hasDerivWithinAt.derivWithin
          (uniqueDiffOn_Icc zero_lt_one 0 ⟨le_rfl, zero_le_one⟩)]
      have herr (n : ℕ) :
          ‖φ (q n) - fderiv ℝ (φ ∘ f) x v‖ ≤ C * t n := by
        have h := hC (t n) ⟨(htpos n).le, htone n⟩
        rw [hTaylor, sub_zero] at h
        calc
          ‖φ (q n) - fderiv ℝ (φ ∘ f) x v‖ =
              (t n)⁻¹ * ‖F φ (t n) - (F φ 0 + t n • fderiv ℝ (φ ∘ f) x v)‖ := by
            have he : (t n)⁻¹ • (F φ (t n) - (F φ 0 + t n • fderiv ℝ (φ ∘ f) x v)) =
                φ (q n) - fderiv ℝ (φ ∘ f) x v := by
              rw [sub_add_eq_sub_sub, smul_sub, inv_smul_smul₀ (htpos n).ne', hq φ n]
            rw [← he, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (htpos n)]
          _ ≤ C * t n := (inv_mul_le_iff₀ (htpos n)).mpr (by simpa [pow_two, mul_left_comm,
            mul_comm, mul_assoc] using h)
      refine isBounded_iff_forall_norm_le.mpr ⟨C, ?_⟩
      rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      simp only [z, map_smul, map_sub, norm_smul, Complex.norm_real, Real.norm_eq_abs,
        abs_inv, abs_of_pos (hrpos p)]
      apply (inv_mul_le_iff₀ (hrpos p)).mpr
      rw [mul_comm, show r p = t p.1 + t p.2 from rfl, add_comm (t p.1), mul_add]
      exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
        (add_le_add (herr p.2) (by simpa [norm_sub_rev] using herr p.1))
    have hr : Tendsto (fun p : ℕ × ℕ ↦ (r p : ℂ)) (atTop ×ˢ atTop) (𝓝 0) := by
      have h : Tendsto r (atTop ×ˢ atTop) (𝓝 0) := by
        simpa only [r, Function.comp_apply, add_zero] using
          (ht.comp tendsto_fst).add (ht.comp tendsto_snd)
      change Tendsto (Complex.ofReal ∘ r) _ _
      simpa only [Complex.ofReal_zero] using (Complex.continuous_ofReal.tendsto 0).comp h
    have hc : Cauchy (atTop.map q) := by
      rw [cauchy_map_iff, uniformity_eq_comap_nhds_zero, tendsto_comap_iff]
      refine ⟨inferInstance, (hz.smul_tendsto_zero
        (Eventually.of_forall fun p ↦ mem_range_self p) hr).congr fun p ↦ ?_⟩
      change (r p : ℂ) • ((((r p)⁻¹ : ℝ) : ℂ) • (q p.2 - q p.1)) = _
      rw [Complex.ofReal_inv]
      exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (hrpos p).ne') _
    have hmem : atTop.map q ≤ 𝓟 (closure (range q)) :=
      le_principal_iff.mpr (mem_map.mpr (Eventually.of_forall fun n ↦
        subset_closure (mem_range_self n)))
    obtain ⟨y, _, hy⟩ := hcomplete.quasiComplete hb.closure isClosed_closure _ hc hmem
    exact ⟨y, fun φ ↦ tendsto_nhds_unique ((φ.continuous.tendsto y).comp hy) (hscalar φ)⟩
  choose g hg using hpoint
  exact ⟨g, fun φ x ↦ hg x φ⟩

/-- Paper: Remark C.5.1.27, p. 735. In a quasi-complete target the two
definitions of the periodic smooth space agree. -/
theorem vectorPeriodicSmoothSubmodule_eq_weak :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      vectorPeriodicSmoothSubmodule d E = weakPeriodicSmoothSubmodule d E := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  intro hcomplete
  have hweak (f : V → E) : f ∈ weakPeriodicSmoothSubmodule d E ↔
      ∀ φ : StrongDual ℂ E, ContDiff ℝ ∞ (φ ∘ f) ∧
        ∀ n : Fin d → ℤ, Periodic (φ ∘ f) (eucInt n) := by
    rw [weakPeriodicSmoothSubmodule, Submodule.mem_iInf]
    exact forall_congr' fun φ ↦ mem_vectorPeriodicSmoothSubmodule_complex_iff (φ ∘ f)
  have hstrong (f : V → E) : f ∈ vectorPeriodicSmoothSubmodule d E ↔
      (∀ m, VectorContDiffOrderOn (k := ℝ) f univ m) ∧
        ∀ n : Fin d → ℤ, Periodic f (eucInt n) := by
    unfold vectorPeriodicSmoothSubmodule
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.proj_apply, sub_eq_zero, Periodic]
    rfl
  apply SetLike.ext
  intro f
  rw [hstrong, hweak]
  constructor
  · rintro ⟨hm, hp⟩ φ
    refine ⟨contDiff_infty.mpr fun m ↦ ?_, fun n x ↦ congrArg φ (hp n x)⟩
    exact (contDiff_of_vectorContDiffOrderOn_succ m
      (vectorContDiffOrderOn_univ_comp_dual φ (m + 1) (hm (m + 1)))).of_le (by simp)
  · intro hf
    refine ⟨?_, fun n x ↦ SeparatingDual.eq_iff_forall_dual_eq.mpr fun φ ↦ (hf φ).2 n x⟩
    intro m
    induction m generalizing f with
    | zero => exact (periodic_order_zero_of_scalar hf).1
    | succ m ih =>
      intro i
      obtain ⟨g, hg⟩ := exists_vector_coordinate_lift (fun φ ↦ (hf φ).1.of_le (by simp)) i hcomplete
      let v : V := EuclideanSpace.single i 1
      have heval (φ : StrongDual ℂ E) : φ ∘ g = fun x ↦ fderiv ℝ (φ ∘ f) x v :=
        funext (hg φ)
      have hgscalar (φ : StrongDual ℂ E) :
          ContDiff ℝ ∞ (φ ∘ g) ∧ ∀ n : Fin d → ℤ, Periodic (φ ∘ g) (eucInt n) := by
        rw [heval]
        exact ⟨(contDiff_infty_iff_fderiv.mp (hf φ).1).2.clm_apply contDiff_const,
          fun n x ↦ congrArg (fun L : V →L[ℝ] ℂ ↦ L v) (fderiv_integer_periodic (hf φ).2 n x)⟩
      refine ⟨g, ?_, (periodic_order_zero_of_scalar hgscalar).2.continuousOn, ih g hgscalar⟩
      intro φ x
      change HasDerivWithinAt (fun t : ℝ ↦ φ (f ((x : V) + t • v))) (φ (g x)) _ 0
      rw [hg φ x]
      have h : HasDerivAt (fun t : ℝ ↦ φ (f ((x : V) + t • v)))
          (fderiv ℝ (φ ∘ f) x v) 0 :=
        ((hf φ).1.differentiable (by simp) (x : V)).hasFDerivAt.hasLineDerivAt v
      exact h.hasDerivWithinAt

omit hAdd hSMul hSemi hT2 in
/-- A vector-valued weak coordinate derivative turns into the ordinary line derivative
after applying a continuous linear functional. -/
private theorem HasWeakPartialOn.hasLineDerivAt_eval
    {f g : V → E} {i : Fin d}
    (h : HasWeakPartialOn (k := ℝ) (Ω := univ) i f
      (fun x ↦ toPettisWeakCompletion E (g x))) (φ : StrongDual ℂ E) (x : V) :
    HasLineDerivAt ℝ (φ ∘ f) (φ (g x)) x (EuclideanSpace.single i 1) := by
  simpa [HasLineDerivAt, Function.comp_def, toPettisWeakCompletion_apply] using
    h φ ⟨x, mem_univ x⟩

omit hAdd hSMul hSemi hT2 in
/-- Testing by a continuous functional preserves each finite vector differentiability order. -/
private theorem vectorContDiffOrderOn_eval (φ : StrongDual ℂ E) {f : V → E}
    {m : ℕ} (h : VectorContDiffOrderOn f univ m) :
    VectorContDiffOrderOn (φ ∘ f) univ m := by
  induction m generalizing f with
  | zero =>
    apply (h.image φ).subset
    rintro _ ⟨x, hx, y, hy, hxy, hd, rfl⟩
    exact ⟨_, ⟨x, hx, y, hy, hxy, hd, rfl⟩, by simp⟩
  | succ m ih =>
    intro i
    obtain ⟨g, hg, hc, hm⟩ := h i
    exact ⟨φ ∘ g, (hasWeakPartialOn_complex_iff i _ _).mpr (hg.hasLineDerivAt_eval φ),
      φ.continuous.comp_continuousOn hc, ih hm⟩

omit hAdd hSMul hSemi hT2 in
/-- Testing by a continuous functional preserves every chain of coordinate derivatives. -/
private theorem hasPartials_eval (φ : StrongDual ℂ E) (l : List (Fin d))
    {f g : V → E} (h : HasVectorMultiPartial.hasPartials g f l) :
    HasVectorMultiPartial.hasPartials (φ ∘ g) (φ ∘ f) l := by
  induction l generalizing f with
  | nil => exact congrArg (φ ∘ ·) (show f = g from h)
  | cons i l ih =>
    obtain ⟨f', hf', hrest⟩ := h
    exact ⟨φ ∘ f', (hasWeakPartialOn_complex_iff i _ _).mpr (hf'.hasLineDerivAt_eval φ),
      ih hrest⟩

omit hAdd hSMul hT2 in
/-- Weak Schwartz maps satisfy the order-zero bounded difference condition. -/
private theorem vectorContDiffOrderOn_zero_of_weakSchwartz {f : V → E}
    (hf : f ∈ weakSchwartzSubmodule d E) : VectorContDiffOrderOn f univ 0 := by
  apply isVonNBounded_of_dual_bounded
  intro φ
  rw [weakSchwartzSubmodule, Submodule.mem_iInf] at hf
  obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp
    ((Submodule.mem_iInf _).mp ((Submodule.mem_inf.mp (hf φ)).1) 0)
  refine ⟨C, ?_⟩
  rintro _ ⟨x, hx, y, hy, hxy, hd, rfl⟩
  simpa [map_smul, map_sub] using hC _ ⟨x, hx, y, hy, hxy, hd, rfl⟩

omit hSemi hT2 in
/-- The bounded normalized differences in the order-zero condition imply continuity. -/
private theorem continuous_of_vectorContDiffOrderOn_zero {f : V → E}
    (hf : VectorContDiffOrderOn f univ 0) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_sub_nhds_zero_iff.mp
  have ht : Tendsto (fun y : V ↦ (‖y - x‖ : ℂ)) (𝓝 x) (𝓝 0) := by
    have h : Continuous fun y : V ↦ (‖y - x‖ : ℂ) :=
      Complex.continuous_ofReal.comp (continuous_id.sub continuous_const).norm
    simpa using h.tendsto x
  have hnear : ∀ᶠ y in 𝓝 x, ‖y - x‖ ≤ 1 := by
    filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with y hy
    exact ((dist_eq_norm y x) ▸ (Metric.mem_ball.mp hy)).le
  have hq : ∀ᶠ y in 𝓝 x,
      ((‖y - x‖⁻¹ : ℝ) : ℂ) • (f y - f x) ∈
        insert 0 {z : E | ∃ a ∈ (univ : Set V), ∃ b ∈ (univ : Set V),
          a ≠ b ∧ ‖b - a‖ ≤ 1 ∧ z = ((‖b - a‖⁻¹ : ℝ) : ℂ) • (f b - f a)} := by
    filter_upwards [hnear] with y hy
    rcases eq_or_ne x y with rfl | hne
    · simp
    · exact mem_insert_of_mem _ ⟨x, mem_univ x, y, mem_univ y, hne, hy, rfl⟩
  have hb := (isVonNBounded_insert (0 : E)).mpr (show IsVonNBounded ℂ _ from hf)
  apply (hb.smul_tendsto_zero hq ht).congr
  intro y
  change (‖y - x‖ : ℂ) • (((‖y - x‖⁻¹ : ℝ) : ℂ) • (f y - f x)) = f y - f x
  rcases eq_or_ne y x with rfl | hne
  · simp
  · rw [Complex.ofReal_inv, smul_inv_smul₀ (by simpa using sub_ne_zero.mpr hne)]

/-- Each weak Schwartz coordinate derivative has a vector-valued lift which is again
weak Schwartz, since its scalar evaluations are Schwartz directional derivatives. -/
private theorem exists_weakSchwartz_partial {f : V → E}
    (hf : f ∈ weakSchwartzSubmodule d E) (i : Fin d) :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E → ∃ g : V → E, g ∈ weakSchwartzSubmodule d E ∧
      HasWeakPartialOn (k := ℝ) (Ω := univ) i f (fun x ↦ toPettisWeakCompletion E (g x)) := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  intro hqc
  let v : V := EuclideanSpace.single i 1
  have hscalar (φ : StrongDual ℂ E) : ∃ F : SchwartzMap V ℂ, (F : V → ℂ) = φ ∘ f :=
    (mem_vectorSchwartzSubmodule_complex_iff _).mp ((Submodule.mem_iInf _).mp hf φ)
  have hex (x : V) : ∃ z : E, ∀ φ : StrongDual ℂ E,
      HasLineDerivAt ℝ (φ ∘ f) (φ z) x v := by
    apply exists_hasDerivAt_eval_zero_of_contDiff (F := fun t : ℝ ↦ f (x + t • v)) _ hqc
    intro φ
    obtain ⟨F, h⟩ := hscalar φ
    change ContDiff ℝ 2 ((φ ∘ f) ∘ fun t : ℝ ↦ x + t • v)
    rw [← h]
    exact (F.smooth 2).comp (by fun_prop)
  choose g hg using hex
  refine ⟨g, ?_, fun φ x ↦ (hg x φ).hasDerivWithinAt⟩
  apply (Submodule.mem_iInf _).mpr
  intro φ
  obtain ⟨F, hF⟩ := hscalar φ
  let G : SchwartzMap V ℂ := LineDeriv.lineDerivOp v F
  apply (mem_vectorSchwartzSubmodule_complex_iff _).mpr
  refine ⟨G, funext fun x ↦ ?_⟩
  change G x = φ (g x)
  have hG : HasLineDerivAt ℝ (F : V → ℂ) (G x) x v :=
    (F.differentiable x).hasFDerivAt.hasLineDerivAt v
  rw [hF] at hG
  exact hG.unique (hg x φ)

/-- Paper: Remark C.5.1.27, p. 735. In a quasi-complete target the two
definitions of the Schwartz space agree. -/
theorem vectorSchwartzSubmodule_eq_weak :
    letI := IsTopologicalAddGroup.rightUniformSpace E
    QuasiCompleteSpace ℂ E →
      vectorSchwartzSubmodule d E = weakSchwartzSubmodule d E := by
  let := IsTopologicalAddGroup.rightUniformSpace E
  intro hqc
  ext f
  rw [vectorSchwartzSubmodule, Submodule.mem_inf, Submodule.mem_iInf]
  change ((∀ m, VectorContDiffOrderOn f univ m) ∧ HasVectorSchwartzDecay f) ↔ _
  constructor
  · rintro ⟨ho, hd⟩
    apply (Submodule.mem_iInf _).mpr
    intro φ
    rw [Submodule.mem_comap, vectorSchwartzSubmodule, Submodule.mem_inf, Submodule.mem_iInf]
    change (∀ m, VectorContDiffOrderOn (φ ∘ f) univ m) ∧ HasVectorSchwartzDecay (φ ∘ f)
    refine ⟨fun m ↦ vectorContDiffOrderOn_eval φ (ho m), fun α p ↦ ?_⟩
    obtain ⟨g, hg, hb⟩ := hd α p
    refine ⟨φ ∘ g, hasPartials_eval φ _ hg, (hb.image φ).subset ?_⟩
    rintro _ ⟨x, rfl⟩
    exact ⟨_, mem_range_self x, map_smul φ _ _⟩
  · intro hf
    have horder (m : ℕ) {f : V → E} (hf : f ∈ weakSchwartzSubmodule d E) :
        VectorContDiffOrderOn f univ m := by
      induction m generalizing f with
      | zero => exact vectorContDiffOrderOn_zero_of_weakSchwartz hf
      | succ m ih =>
        intro i
        obtain ⟨g, hg, hpartial⟩ := exists_weakSchwartz_partial hf i hqc
        exact ⟨g, hpartial, (continuous_of_vectorContDiffOrderOn_zero
          (vectorContDiffOrderOn_zero_of_weakSchwartz hg)).continuousOn, ih hg⟩
    have hchain (l : List (Fin d)) {f : V → E} (hf : f ∈ weakSchwartzSubmodule d E) :
        ∃ g ∈ weakSchwartzSubmodule d E, HasVectorMultiPartial.hasPartials g f l := by
      induction l generalizing f with
      | nil => exact ⟨f, hf, rfl⟩
      | cons i l ih =>
        obtain ⟨g, hg, hpartial⟩ := exists_weakSchwartz_partial hf i hqc
        obtain ⟨h, hh, hrest⟩ := ih hg
        exact ⟨h, hh, g, hpartial, hrest⟩
    refine ⟨fun m ↦ horder m hf, fun α p ↦ ?_⟩
    obtain ⟨g, hg, hpartial⟩ := hchain
      ((List.finRange d).flatMap fun i ↦ List.replicate (α i) i) hf
    refine ⟨g, hpartial, isVonNBounded_of_dual_bounded fun φ ↦ ?_⟩
    obtain ⟨F, hF⟩ := (mem_vectorSchwartzSubmodule_complex_iff (φ ∘ g)).mp
      ((Submodule.mem_iInf _).mp hg φ)
    let G := SchwartzMap.smulLeftCLM ℂ (fun x : V ↦ p.eval (fun i ↦ (x i : ℂ))) F
    have hG : (G : V → ℂ) = _ :=
      SchwartzMap.smulLeftCLM_apply (polynomial_hasTemperateGrowth p) F
    refine ⟨SchwartzMap.seminorm ℂ 0 0 G, ?_⟩
    rintro _ ⟨x, rfl⟩
    simpa only [hG, hF, Function.comp_apply, map_smul] using G.norm_le_seminorm ℂ x

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

omit hAdd hSMul hSemi hT2 in
/-- The continuous dual separates points, so a chain of weak coordinate derivatives
has a unique vector-valued endpoint. -/
private theorem hasPartials_unique [SeparatingDual ℂ E] (l : List (Fin d)) {f g₁ g₂ : V → E}
    (h₁ : HasVectorMultiPartial.hasPartials g₁ f l)
    (h₂ : HasVectorMultiPartial.hasPartials g₂ f l) : g₁ = g₂ := by
  induction l generalizing f with
  | nil => exact (show f = g₁ from h₁).symm.trans (show f = g₂ from h₂)
  | cons i l ih =>
    obtain ⟨f₁, hd₁, hr₁⟩ := h₁
    obtain ⟨f₂, hd₂, hr₂⟩ := h₂
    have heq : f₁ = f₂ := funext fun x ↦ SeparatingDual.eq_iff_forall_dual_eq.mpr fun φ ↦
      (hd₁.hasLineDerivAt_eval φ x).unique (hd₂.hasLineDerivAt_eval φ x)
    rw [← heq] at hr₂
    exact ih hr₁ hr₂

omit hAdd hSMul hSemi hT2 in
/-- A continuous integer-periodic map takes all its values on the compact unit cube,
so each continuous seminorm on its range is bounded above. -/
private theorem bddAbove_seminorm_of_continuous_integer_periodic (q : Seminorm ℂ E)
    (hq : Continuous q) {g : V → E} (hg : Continuous g)
    (hp : ∀ n : Fin d → ℤ, Periodic g (eucInt n)) : BddAbove (range (q ∘ g)) := by
  let Q : Set (Fin d → ℝ) := univ.pi fun _ ↦ Icc 0 1
  have hQ : IsCompact Q := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hCube := hQ.image (PiLp.continuous_toLp 2 (fun _ : Fin d ↦ ℝ))
  apply (hCube.bddAbove_image (hq.comp hg).continuousOn).mono
  rintro _ ⟨x, rfl⟩
  let n : Fin d → ℤ := fun i ↦ ⌊x i⌋
  have hx : (x - eucInt n) ∈ WithLp.toLp 2 '' Q := by
    refine ⟨WithLp.ofLp (x - eucInt n), ?_, rfl⟩
    intro i _
    change x i - (⌊x i⌋ : ℝ) ∈ Icc 0 1
    exact ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  refine ⟨x - eucInt n, hx, congrArg q ?_⟩
  have heq := hp n (x - eucInt n)
  rw [sub_add_cancel] at heq
  exact heq.symm

omit hAdd hSMul hSemi hT2 in
/-- A differentiability order matching the chain length supplies continuous lifts
throughout the chain. A separating dual transfers all periods to those lifts. -/
private theorem exists_continuous_integer_periodic_hasPartials [SeparatingDual ℂ E]
    (l : List (Fin d)) {f : V → E} (hf : VectorContDiffOrderOn f univ l.length)
    (hc : Continuous f)
    (hp : ∀ n : Fin d → ℤ, Periodic f (eucInt n)) :
    ∃ g : V → E, HasVectorMultiPartial.hasPartials g f l ∧ Continuous g ∧
      ∀ n : Fin d → ℤ, Periodic g (eucInt n) := by
  induction l generalizing f with
  | nil => exact ⟨f, rfl, hc, hp⟩
  | cons i l ih =>
    obtain ⟨f', hd, hc', ho⟩ := hf i
    have hp' (n : Fin d → ℤ) : Periodic f' (eucInt n) := by
      intro x
      apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).mpr
      intro φ
      have hline (t : ℝ) : φ (f ((x + eucInt n) + t • EuclideanSpace.single i 1)) =
          φ (f (x + t • EuclideanSpace.single i 1)) := by
        rw [add_right_comm x, hp n]
      have h' : HasDerivAt (fun t : ℝ ↦ φ (f ((x + eucInt n) +
          t • EuclideanSpace.single i 1))) (φ (f' (x + eucInt n))) 0 :=
        hd.hasLineDerivAt_eval φ (x + eucInt n)
      rw [funext hline] at h'
      exact h'.unique (hd.hasLineDerivAt_eval φ x)
    obtain ⟨g, hg, hgc, hgp⟩ := ih ho (continuousOn_univ.mp hc') hp'
    exact ⟨g, ⟨f', hd, hg⟩, hgc, hgp⟩

/-- Paper: (C.5.1.45), p. 735. The supremum of a continuous seminorm on a mixed
derivative of a periodic smooth function is finite and defines a seminorm.
Deviation: The supremum is over the Euclidean cover of the torus. -/
theorem exists_vectorPeriodicSmoothDerivativeSeminorm (q : Seminorm ℂ E) (hq : Continuous q)
    (α : Fin d → ℕ) :
    ∃ s : Seminorm ℂ (vectorPeriodicSmoothSubmodule d E),
      ∀ f : vectorPeriodicSmoothSubmodule d E, ∃ g : V → E,
        HasVectorMultiPartial α f.val g ∧ BddAbove (range (q ∘ g)) ∧
          s f = ⨆ x : V, q (g x) := by
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  let l := (List.finRange d).flatMap fun i ↦ List.replicate (α i) i
  have hderiv (f : vectorPeriodicSmoothSubmodule d E) :
      ∃ g : V → E, HasVectorMultiPartial.hasPartials g f.val l ∧
        BddAbove (range (q ∘ g)) := by
    have hf := f.property
    simp only [vectorPeriodicSmoothSubmodule, Submodule.mem_inf, Submodule.mem_iInf,
      LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.proj_apply, sub_eq_zero] at hf
    obtain ⟨g, hg, hc, hp⟩ := exists_continuous_integer_periodic_hasPartials l
      (hf.1 l.length) (continuous_of_vectorContDiffOrderOn_zero (hf.1 0)) hf.2
    exact ⟨g, hg, bddAbove_seminorm_of_continuous_integer_periodic q hq hc hp⟩
  choose g hg hb using hderiv
  let D : vectorPeriodicSmoothSubmodule d E →ₗ[ℂ] (V → E) :=
    { toFun := g
      map_add' := fun f₁ f₂ ↦ hasPartials_unique l (hg (f₁ + f₂))
        (hasPartials_add (g f₁) (g f₂) l f₁.val f₂.val (hg f₁) (hg f₂))
      map_smul' := fun c f ↦ hasPartials_unique l (hg (c • f))
        (hasPartials_smul c (g f) l f.val (hg f)) }
  let p (x : V) := q.comp ((LinearMap.proj x).comp D)
  have hp : BddAbove (range p) := Seminorm.bddAbove_range_iff.mpr hb
  exact ⟨⨆ x, p x, fun f ↦ ⟨g f, hg f, hb f, Seminorm.iSup_apply hp⟩⟩

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
