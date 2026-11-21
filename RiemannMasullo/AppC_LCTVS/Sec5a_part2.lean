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
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Partial
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach

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
