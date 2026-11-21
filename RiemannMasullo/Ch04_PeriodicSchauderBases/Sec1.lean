module

public import RiemannMasullo.AppC_LCTVS.Sec2b
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Topology.Algebra.Equicontinuity
public import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Analysis.PSeries

/-!
# Schauder bases

Masullo, §4.1, pp. 155–161. The scalar field is complex, and the ambient spaces
use the locally convex topology of Appendix C.
-/

@[expose] public noncomputable section

open Bornology Filter Function Set Topology
open scoped BigOperators ContDiff

namespace RiemannMasullo

section Fourier

open scoped Interval

/-- Differentiation of a smooth periodic lift multiplies its Fourier coefficient by the
corresponding frequency. -/
private theorem fourierCoeffOn_deriv_one_periodic {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    (hper : Periodic f 1) (m : ℤ) :
    fourierCoeffOn zero_lt_one (deriv f) m =
      (2 * Real.pi * Complex.I * m) * fourierCoeffOn zero_lt_one f m := by
  obtain ⟨hd, hd'⟩ := contDiff_infty_iff_deriv.mp hf
  have hcont := hd'.continuous
  have hend : f 1 = f 0 := by simpa using hper 0
  let e (x : ℝ) := fourier (-m) (x : AddCircle (1 : ℝ))
  let a : ℂ := 2 * Real.pi * Complex.I * m
  have he (x : ℝ) : HasDerivAt e (-a * e x) x := by
    simpa [e, a, neg_mul] using hasDerivAt_fourier_neg 1 m x
  have hecont : Continuous e := (fourier (-m)).continuous.comp (AddCircle.continuous_mk' 1)
  have heend : e 1 = e 0 := by simp only [e, AddCircle.coe_period, AddCircle.coe_zero]
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := 0) (b := 1) hecont.continuousOn hf.continuous.continuousOn
    (fun x _ ↦ he x) (fun x _ ↦ (hd x).hasDerivAt)
    ((continuous_const.mul hecont).intervalIntegrable 0 1) (hcont.intervalIntegrable 0 1)
  rw [hend, heend, sub_self, zero_sub] at h
  simp_rw [mul_assoc, intervalIntegral.integral_const_mul, neg_mul, neg_neg] at h
  have hcoeff (g : ℝ → ℂ) :
      fourierCoeffOn zero_lt_one g m = ∫ x in 0..1, e x * g x := by
    rw [fourierCoeffOn_eq_integral, sub_zero]
    simp only [div_one, one_smul, smul_eq_mul, e]
  rw [hcoeff, hcoeff]
  exact h

/-- Paper: (4.1.1.1), p. 156. The Fourier series of a smooth function on the
unit circle converges uniformly in every derivative order.
Deviation: Functions on the circle are represented by their periodic lifts, and
the smooth convergence is expressed using the net of finite partial sums. -/
theorem smooth_fourier_series {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hper : Periodic φ 1) (k : ℕ) :
    TendstoUniformlyOn
      (fun s : Finset ℤ ↦ iteratedDeriv k (fun t : ℝ ↦
        ∑ m ∈ s, fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) φ m *
          fourier m (t : AddCircle (1 : ℝ))))
      (iteratedDeriv k φ) atTop (Ico 0 1) := by
  have deriv_periodic {f : ℝ → ℂ} (hf : Periodic f 1) : Periodic (deriv f) 1 := by
    intro x
    rw [← deriv_comp_add_const, show (fun y ↦ f (y + 1)) = f from funext hf]
  induction k generalizing φ with
  | zero =>
      simp only [iteratedDeriv_zero]
      have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
      let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hφ.continuous⟩
      have hcoeff (m : ℤ) : fourierCoeff F m = fourierCoeffOn zero_lt_one φ m := by
        rw [fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral]
        simp [F, Periodic.lift_coe]
      have hs : Summable (fourierCoeff F) := by
        have hd := (contDiff_infty_iff_deriv.mp hφ).2
        have hdd := (contDiff_infty_iff_deriv.mp hd).2
        obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn
          (s := uIcc (0 : ℝ) 1) hdd.continuous.continuousOn
        have hbound (m : ℤ) : ‖fourierCoeffOn zero_lt_one (deriv (deriv φ)) m‖ ≤ C := by
          rw [fourierCoeffOn_eq_integral]
          simp only [sub_zero, div_one, one_smul]
          have hb : ∀ x ∈ uIoc (0 : ℝ) 1,
              ‖fourier (-m) (x : AddCircle (1 : ℝ)) • deriv (deriv φ) x‖ ≤ C := by
            intro x hx
            rw [norm_smul, fourier_apply, Circle.norm_coe, one_mul]
            exact hC x (uIoc_subset_uIcc hx)
          simpa using intervalIntegral.norm_integral_le_of_norm_le_const hb
        -- Two derivatives give an inverse-square bound away from frequency zero.
        let a : ℂ := 2 * Real.pi * Complex.I
        have ha : 0 < ‖a‖ := norm_pos_iff.mpr (by simp [a, Real.pi_ne_zero])
        have hp := Real.summable_one_div_int_pow.mpr (by decide : 1 < (2 : ℕ))
        refine (hp.mul_left (C / ‖a‖ ^ 2)).of_norm_bounded_eventually ?_
        filter_upwards [eventually_cofinite_ne (0 : ℤ)] with m hm
        rw [hcoeff]
        specialize hbound m
        rw [fourierCoeffOn_deriv_one_periodic hd (deriv_periodic hper),
          fourierCoeffOn_deriv_one_periodic hφ hper, ← mul_assoc, ← pow_two, norm_mul,
          norm_pow, norm_mul, mul_pow, Complex.norm_intCast, sq_abs] at hbound
        have hpos : 0 < ‖a‖ ^ 2 * (m : ℝ)^2 := by
          have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm
          positivity
        rw [mul_one_div, div_div]
        exact (le_div_iff₀ hpos).2 (by simpa only [a, mul_comm] using hbound)
      have hu := ContinuousMap.tendsto_iff_tendstoUniformly.mp
        (hasSum_fourier_series_of_summable hs)
      have hlift := hu.comp (fun t : ℝ ↦ (t : AddCircle (1 : ℝ)))
      simp only [Function.comp_def, ContinuousMap.sum_apply, ContinuousMap.smul_apply,
        smul_eq_mul, hcoeff] at hlift
      simpa only [F, ContinuousMap.coe_mk, Periodic.lift_coe, SummationFilter.unconditional_filter]
        using hlift.tendstoUniformlyOn
  | succ k ih =>
      simp only [iteratedDeriv_succ']
      have hsum (s : Finset ℤ) :
          deriv (fun t : ℝ ↦ ∑ m ∈ s, fourierCoeffOn zero_lt_one φ m *
            fourier m (t : AddCircle (1 : ℝ))) =
          fun t : ℝ ↦ ∑ m ∈ s, fourierCoeffOn zero_lt_one (deriv φ) m *
            fourier m (t : AddCircle (1 : ℝ)) := by
        funext t
        apply HasDerivAt.deriv
        apply HasDerivAt.fun_sum
        intro m _
        rw [fourierCoeffOn_deriv_one_periodic hφ hper]
        simpa only [Complex.ofReal_one, div_one, mul_left_comm, mul_assoc] using
          (hasDerivAt_fourier 1 m t).const_mul (fourierCoeffOn zero_lt_one φ m)
      simp only [hsum]
      exact ih (contDiff_infty_iff_deriv.mp hφ).2 (deriv_periodic hper)

/-- Paper: (4.1.1.1), p. 156. A series of exponentials converging in the smooth
topology has the Fourier coefficients of its limit.
Deviation: We use periodic lifts and take the symmetric partial sums. -/
theorem smooth_fourier_series_unique {φ : ℝ → ℂ} (hφ : ContDiff ℝ ∞ φ) (hper : Periodic φ 1)
    (a : ℤ → ℂ)
    (ha : ∀ k : ℕ, TendstoUniformlyOn
      (fun N : ℕ ↦ iteratedDeriv k (fun t : ℝ ↦
        ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a m * fourier m (t : AddCircle (1 : ℝ))))
      (iteratedDeriv k φ) atTop (Ico 0 1)) :
    a = fourierCoeffOn (zero_lt_one : (0 : ℝ) < 1) φ := by
  have : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hφ.continuous⟩
  let S (N : ℕ) : C(AddCircle (1 : ℝ), ℂ) :=
    ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), a m • fourier m
  -- Every point of the circle has a representative in the interval of uniform convergence.
  have hS : Tendsto S atTop (𝓝 F) := by
    rw [ContinuousMap.tendsto_iff_tendstoUniformly, Metric.tendstoUniformly_iff]
    have h := ha 0
    simp only [iteratedDeriv_zero, Metric.tendstoUniformlyOn_iff] at h
    intro ε hε
    filter_upwards [h ε hε] with N hN t
    obtain ⟨x, hx, rfl⟩ := AddCircle.eq_coe_Ico t
    simpa only [F, S, ContinuousMap.coe_mk, Periodic.lift_coe, ContinuousMap.sum_apply,
      ContinuousMap.smul_apply, smul_eq_mul] using hN x hx
  funext m
  -- Taking a coefficient is continuous via the embedding into L² and its Fourier basis.
  let coeff : C(AddCircle (1 : ℝ), ℂ) →L[ℂ] ℂ :=
    (innerSL ℂ (fourierBasis m)).comp (ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ)
  have hcoeff (f : C(AddCircle (1 : ℝ), ℂ)) : coeff f = fourierCoeff f m := by
    dsimp only [coeff]
    rw [ContinuousLinearMap.comp_apply, innerSL_apply_apply, ← fourierBasis.repr_apply_apply,
      fourierBasis_repr, fourierCoeff_toLp]
  have hF : coeff F = fourierCoeffOn zero_lt_one φ m := by
    rw [hcoeff, fourierCoeff_eq_intervalIntegral _ _ 0, fourierCoeffOn_eq_integral]
    simp [F, Periodic.lift_coe]
  rw [← hF]
  refine tendsto_nhds_unique_of_eventuallyEq tendsto_const_nhds
    (coeff.continuous.continuousAt.tendsto.comp hS) ?_
  filter_upwards [eventually_ge_atTop m.natAbs] with N hN
  have hm : m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
    rw [Finset.mem_Icc]
    omega
  simp only [Function.comp_apply, S, map_sum, map_smul]
  simp only [hcoeff, fourierCoeff_fourier]
  rw [Finset.sum_eq_single_of_mem m hm]
  · simp
  · intro j _ hj
    simp [hj]

end Fourier

section Definitions

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]

/-- Paper: Definition 4.1.1.1(1), p. 157. The coefficient functionals and basis vectors
are biorthogonal, and the ordered coordinate series converges to the original vector. -/
def IsTopologicalBasis (x : ℕ → E) (f : ℕ → Module.Dual ℂ E) : Prop :=
  (∀ m n, f m (x n) = if m = n then 1 else 0) ∧
    ∀ u, HasSum (fun m ↦ f m u • x m) u (SummationFilter.conditional ℕ)

/-- Paper: Definition 4.1.1.1(2), p. 157. A Schauder basis is a topological basis
with continuous coefficient functionals, expressed by taking them in the continuous dual. -/
def IsSchauderBasis (x : ℕ → E) (f : ℕ → StrongDual ℂ E) : Prop :=
  IsTopologicalBasis x (fun m ↦ (f m).toLinearMap)

/-- Paper: Definition 4.1.1.1(2), p. 157. On a normed space the Schauder basis
predicate agrees with Mathlib's bundled sequence and its coefficient maps. -/
theorem isSchauderBasis_iff_exists_mathlib {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (x : ℕ → F) (f : ℕ → StrongDual ℂ F) :
    IsSchauderBasis x f ↔ ∃ b : _root_.SchauderBasis ℂ F, b.basis = x ∧ b.coord = f := by sorry

-- TODO(paper-gap): The individual block sums can converge even when the ordered
-- series has no limit. The equivalent permutation description needs cumulative sums.

namespace SchauderBasis

variable (x : ℕ → E) (f : ℕ → StrongDual ℂ E)

section Projections

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]

/-- Paper: Definition 4.1.2.1(1), p. 158. The basic projection at index k keeps
the coordinates from zero through k. -/
def partialProjection (k : ℕ) : E →L[ℂ] E :=
  ∑ m ∈ Finset.Iic k, (f m).smulRight (x m)

/-- Paper: Definition 4.1.2.1(1), p. 158. The kth basic projection keeps exactly
the basis vectors with index at most k. -/
theorem partialProjection_apply_basis (h : IsSchauderBasis x f) (k n : ℕ) :
    partialProjection x f k (x n) = if n ≤ k then x n else 0 := by sorry

/-- Paper: Definition 4.1.2.1(1), p. 158. The basic projections of an equicontinuous
basis form an equicontinuous family. For linear maps it suffices to test at zero. -/
def IsEquicontinuous : Prop :=
  letI := IsTopologicalAddGroup.rightUniformSpace E
  EquicontinuousAt (fun k ↦ (partialProjection x f k : E → E)) 0

end Projections

/-- Paper: Definition 4.1.2.1(2), p. 158. The coordinate series of each vector of an
unconditional basis converges to that vector along the net of finite partial sums.
Deviation: This uses unconditional summation, corresponding to the paper's
permutation formulation. The printed formulation with individual block sums is false. -/
def IsUnconditional : Prop :=
  ∀ u, HasSum (fun m ↦ f m u • x m) u

/-- Paper: Definition 4.1.2.1(2), p. 158. For a Schauder basis, unconditional
summation is equivalent to convergence of each permuted coordinate series. -/
theorem isUnconditional_iff_forall_permutation [IsTopologicalAddGroup E] [T2Space E]
    (h : IsSchauderBasis x f) :
    IsUnconditional x f ↔ ∀ (u : E) (σ : ℕ ≃ ℕ),
      Summable (fun m ↦ f (σ m) u • x (σ m)) (SummationFilter.conditional ℕ) := by sorry

/-- Paper: Definition 4.1.2.1(3), p. 158. For each continuous seminorm, one
continuous seminorm bounds the sums of the seminorms of the coordinate terms
for all vectors. Summability records the convergence implicit in (4.1.2.1). -/
def IsAbsolute : Prop :=
  ∀ q : Seminorm ℂ E, Continuous q → ∃ q' : Seminorm ℂ E, Continuous q' ∧
    ∀ u, Summable (fun m ↦ q (f m u • x m)) ∧
      (∑' m, q (f m u • x m)) ≤ q' u

/-- Paper: Definition 4.1.2.1(4), p. 158. The ordered series associated to any
scalar sequence converges if its partial sums are von Neumann bounded. -/
def IsBoundedlyComplete : Prop :=
  ∀ a : ℕ → ℂ, IsVonNBounded ℂ (range fun k : ℕ ↦ ∑ m ∈ Finset.Iic k, a m • x m) →
    Summable (fun m ↦ a m • x m) (SummationFilter.conditional ℕ)

/-- Paper: Definition 4.1.2.1(5), p. 158. A Schauder basis is shrinking if its
coefficient functionals form a Schauder basis of the strong dual with the
coordinate maps given by evaluation at the original basis vectors. -/
def IsShrinking [ContinuousSMul ℂ E] : Prop :=
  IsSchauderBasis f (fun m ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (x m))

/-- Paper: Definition 4.1.2.1(6), p. 158. A regular basis has a single zero
neighborhood that excludes all its basis vectors. -/
def IsRegular : Prop :=
  ∃ U ∈ 𝓝 (0 : E), ∀ m, x m ∉ U

/-- Paper: Definition 4.1.2.1(6), p. 158. A normalized basis is regular and its
basis vectors are von Neumann bounded. -/
def IsNormalized : Prop :=
  IsRegular x ∧ IsVonNBounded ℂ (range x)

end SchauderBasis

end Definitions

namespace SchauderBasis

local notation "coordinateVector" => (fun n : ℕ ↦ Pi.single n (1 : ℂ))
local notation "coordinateFunctional" =>
  (fun n : ℕ ↦ ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ℕ ↦ ℂ) n)

section Examples

/-- Paper: Definition 4.1.1.1(1), p. 157. Single-coordinate vectors and the
coordinate functionals give a topological basis of the complex sequence space
with the product topology. -/
theorem pi_isTopologicalBasis :
    IsTopologicalBasis coordinateVector (fun n ↦ (coordinateFunctional n).toLinearMap) := by sorry

/-- Paper: Definition 4.1.2.1(1), p. 158. The basic projections of the coordinate
basis of the complex sequence space are equicontinuous in the product topology. -/
theorem pi_isEquicontinuous :
    IsEquicontinuous coordinateVector coordinateFunctional := by sorry

/-- Paper: Definition 4.1.2.1(3), p. 158. The coordinate basis of the complex
sequence space with the product topology is absolute. -/
theorem pi_isAbsolute :
    IsAbsolute coordinateVector coordinateFunctional := by sorry

/-- Paper: Definition 4.1.2.1(4), p. 158. The coordinate basis of the complex
sequence space with the product topology is boundedly complete. -/
theorem pi_isBoundedlyComplete : IsBoundedlyComplete coordinateVector := by sorry

/-- Paper: Definition 4.1.2.1(5), p. 158. A countable orthonormal Hilbert basis is
shrinking, with its coefficients given by the inner products against its vectors. -/
theorem hilbertBasis_isShrinking {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (b : HilbertBasis ℕ ℂ H) :
    IsShrinking (fun n ↦ b n) (fun n ↦ innerSL ℂ (b n)) := by sorry

/-- Paper: Definition 4.1.2.1(6), p. 158. Every zero neighborhood in the complex
sequence space with the product topology contains a coordinate basis vector. -/
theorem pi_not_isRegular : ¬ IsRegular coordinateVector := by sorry

/-- Paper: Definition 4.1.2.1(6), p. 158. A countable orthonormal Hilbert basis is
normalized in the paper's sense. -/
theorem hilbertBasis_isNormalized {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ℕ ℂ H) : IsNormalized (fun n ↦ b n) := by sorry

end Examples

section Results

universe u v

variable {E : Type u} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
variable {x : ℕ → E} {f : ℕ → StrongDual ℂ E}

/-- Paper: Remark 4.1.2.2, p. 158. The absolute sum under a seminorm can also be
written as the sum of the coefficient norms times the seminorms of the basis vectors. -/
theorem tsum_seminorm_coordinates (q : Seminorm ℂ E) (u : E)
    (h : Summable (fun m ↦ q (f m u • x m))) :
    (∑' m, q (f m u • x m)) = ∑' m, ‖f m u‖ * q (x m) := by
  simp only [map_smul_eq_mul]

/-- Paper: Remark 4.1.2.2, p. 159. The coordinate basis of the complex sequence
space has equicontinuous basic projections and fails equicontinuity for its
coefficient functionals. -/
theorem pi_coeff_not_equicontinuousAt :
    ¬ EquicontinuousAt (fun n (u : ℕ → ℂ) ↦ coordinateFunctional n u) 0 := by sorry

/-- Paper: Remark 4.1.2.2, p. 159. A Schauder basis with equicontinuous
coefficient functionals is regular. -/
theorem isRegular_of_equicontinuous_coeff (hb : IsSchauderBasis x f)
    (hf : EquicontinuousAt (fun m ↦ (f m : E → ℂ)) 0) : IsRegular x := by
  refine ⟨{u | ∀ n, dist (f n 0) (f n u) < 1},
    Metric.equicontinuousAt_iff_right.mp hf 1 zero_lt_one, ?_⟩
  intro n hn
  have hdiag : f n (x n) = 1 := by simpa using hb.1 n n
  simpa [hdiag] using hn n

/-- Paper: Remark 4.1.2.2, p. 159. A regular Schauder basis has equicontinuous
coefficient functionals if the space has its Mackey topology and the Mackey
topology on the dual is sequentially complete. -/
theorem equicontinuous_coeff_of_isRegular [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] (hb : IsSchauderBasis x f) (hr : IsRegular x)
    (hM : (inferInstance : TopologicalSpace E) = mackeyTopology (topDualPairing ℂ E).flip)
    (hseq : let τ := mackeyTopology (topDualPairing ℂ E)
      ∀ g : ℕ → StrongDual ℂ E,
        (∀ U ∈ @nhds _ τ 0, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n → g m - g n ∈ U) →
        ∃ φ, Tendsto g atTop (@nhds _ τ φ)) :
    EquicontinuousAt (fun m ↦ (f m : E → ℂ)) 0 := by sorry

/-- Paper: Remark 4.1.2.3, p. 159. A Fréchet space with a regular Schauder basis
has a continuous norm, represented by a continuous seminorm separating zero. -/
theorem exists_continuous_norm_of_isRegular (hE : IsFrechetTVS E) (hb : IsSchauderBasis x f)
    (hr : IsRegular x) : ∃ q : Seminorm ℂ E, Continuous q ∧ ∀ u, q u = 0 → u = 0 := by sorry

/-- Paper: Remark 4.1.2.3, p. 159. A Fréchet space with a regular Schauder basis
has no complemented closed subspace isomorphic to the product of countably
many copies of the complex field. -/
theorem no_complemented_pi_of_isRegular (hE : IsFrechetTVS E) (hb : IsSchauderBasis x f)
    (hr : IsRegular x) :
    ¬ ∃ S : Submodule ℂ E, IsClosed (S : Set E) ∧ S.ClosedComplemented ∧
      Nonempty (S ≃L[ℂ] (ℕ → ℂ)) := by sorry

-- TODO(paper-gap): The printed proof does not address bounded completeness on either
-- side and leaves the passage from unconditional convergence in the bidual to
-- unconditional convergence in the strong dual unjustified.

section AbsoluteDuality

variable [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] [hLC : PolynormableSpace ℂ E]
  [hHausdorff : T2Space E] [hBarrelled : BarrelledSpace ℂ E]
variable (hComplete : @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E))
  (hReflexive : IsHomeomorph (ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)))
  (hb : IsSchauderBasis x f) (ha : IsAbsolute x f)

include hLC hHausdorff hBarrelled hComplete hReflexive hb ha

/-- Paper: Lemma 4.1.2.4, p. 159. An absolute Schauder basis of a complete
barrelled reflexive space is shrinking. -/
theorem isShrinking_of_isAbsolute : IsShrinking x f := by sorry

/-- Paper: Lemma 4.1.2.4, p. 159. An absolute Schauder basis of a complete
barrelled reflexive space is boundedly complete. -/
theorem isBoundedlyComplete_of_isAbsolute : IsBoundedlyComplete x := by sorry

/-- Paper: Lemma 4.1.2.4, p. 159. The coefficient basis of the strong dual is
unconditional, with coefficients given by evaluation at the original basis vectors. -/
theorem strongDual_isUnconditional_of_isAbsolute :
    IsUnconditional f (fun m ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (x m)) := by sorry

/-- Paper: Lemma 4.1.2.4, p. 159. The coefficient basis of the strong dual is
boundedly complete. -/
theorem strongDual_isBoundedlyComplete_of_isAbsolute : IsBoundedlyComplete f := by sorry

/-- Paper: Lemma 4.1.2.4, p. 159. If the original space is also nuclear, the
coefficient basis of the strong dual is shrinking. -/
theorem strongDual_isShrinking_of_isAbsolute (hNuclear : IsNuclearTVS.{v, u} E) :
    IsShrinking f (fun m ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (x m)) := by sorry

end AbsoluteDuality

/-- Paper: Remark 4.1.2.5, p. 160. On a Fréchet space, the pointwise absolute
summability of all coordinate series under continuous seminorms is equivalent
to the absolute basis condition with continuous seminorm bounds. -/
theorem isAbsolute_iff_summable_of_frechet (hE : IsFrechetTVS E) (hb : IsSchauderBasis x f) :
    IsAbsolute x f ↔
      ∀ (q : Seminorm ℂ E), Continuous q → ∀ u, Summable (fun m ↦ q (f m u • x m)) := by sorry

/-- Paper: Remark 4.1.2.5, p. 161. The two absolute basis conditions also
agree in a strict countable inductive limit of nuclear Fréchet spaces.
Deviation: The defining sequence is given by its increasing images in the
limit with their subspace topologies, as in Appendix C. -/
theorem isAbsolute_iff_summable_of_strictLF_stages [T2Space E]
    (S : ℕ → Submodule ℂ E) (hS : Monotone S)
    (hFrechet : ∀ n, IsFrechetTVS (S n)) (hNuclear : ∀ n, IsNuclearTVS.{v, u} (S n))
    (hexhaustive : ∀ u : E, ∃ n, u ∈ S n)
    (ht : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology (fun n ↦ (S n).subtype))
    (hb : IsSchauderBasis x f) :
    IsAbsolute x f ↔
      ∀ (q : Seminorm ℂ E), Continuous q → ∀ u, Summable (fun m ↦ q (f m u • x m)) := by sorry

/-- Paper: Theorem 4.1.2.6(1), p. 161. Every equicontinuous Schauder basis of a
nuclear space is absolute. -/
theorem isAbsolute_of_isNuclearTVS [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (hE : IsNuclearTVS.{v, u} E) (hb : IsSchauderBasis x f) (heq : IsEquicontinuous x f) :
    IsAbsolute x f := by sorry

/-- Paper: Theorem 4.1.2.6(2), p. 161. Every Schauder basis of a nuclear Fréchet
space is absolute. -/
theorem isAbsolute_of_nuclear_frechet (hE : IsNuclearTVS.{v, u} E) (hFrechet : IsFrechetTVS E)
    (hb : IsSchauderBasis x f) : IsAbsolute x f := by sorry

/-- Paper: Theorem 4.1.2.6(3), p. 161. Every Schauder basis in a strict countable
inductive limit of nuclear Fréchet spaces is absolute.
Deviation: The defining sequence is given by its increasing images in the
limit with their subspace topologies, as in Appendix C. -/
theorem isAbsolute_of_nuclear_strictLF_stages [T2Space E]
    (S : ℕ → Submodule ℂ E) (hS : Monotone S)
    (hFrechet : ∀ n, IsFrechetTVS (S n)) (hNuclear : ∀ n, IsNuclearTVS.{v, u} (S n))
    (hexhaustive : ∀ u : E, ∃ n, u ∈ S n)
    (ht : (inferInstance : TopologicalSpace E) = locallyConvexFinalTopology (fun n ↦ (S n).subtype))
    (hb : IsSchauderBasis x f) : IsAbsolute x f := by sorry

end Results

end SchauderBasis

end RiemannMasullo
