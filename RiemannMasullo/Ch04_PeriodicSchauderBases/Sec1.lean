module

public import RiemannMasullo.AppC_LCTVS.Sec2b
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.Normed.Module.Bases
public import Mathlib.Topology.Algebra.Equicontinuity
public import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Baire.LocallyCompactRegular
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SeparatingDual
import RiemannMasullo.ForMathlib.Topology.Algebra.InfiniteSum.NatInt

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
    IsSchauderBasis x f ↔ ∃ b : _root_.SchauderBasis ℂ F, b.basis = x ∧ b.coord = f := by
  constructor
  · intro h
    -- Pack the biorthogonality and the convergence of the coordinate series into
    -- Mathlib's bundled structure. The only mismatch is the decidability instance
    -- for `Pi.single`, which is bridged by case-splitting on the index equality.
    refine ⟨⟨x, f, fun i j => ?_, fun u => h.2 u⟩, rfl, rfl⟩
    by_cases hij : i = j <;> simpa [hij, Pi.single_apply] using h.1 i j
  · -- Conversely, unpack the bundled structure and read off the two conditions.
    rintro ⟨b, rfl, rfl⟩
    refine ⟨fun m n => ?_, fun u => b.expansion u⟩
    by_cases hmn : m = n <;> simpa [hmn, Pi.single_apply] using b.ortho m n

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
    partialProjection x f k (x n) = if n ≤ k then x n else 0 := by
  have horth (m : ℕ) : (f m) (x n) = if m = n then (1 : ℂ) else 0 := by
    simpa [ContinuousLinearMap.coe_coe] using h.1 m n
  simp only [partialProjection, sum_apply, ContinuousLinearMap.smulRight_apply]
  simp_rw [horth]
  have hterm (m : ℕ) :
      (if m = n then (1 : ℂ) else 0) • x m = if m = n then x n else 0 := by
    split_ifs with hmn <;> simp [hmn]
  simp_rw [hterm, Finset.sum_ite_eq', Finset.mem_Iic]

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
      Summable (fun m ↦ f (σ m) u • x (σ m)) (SummationFilter.conditional ℕ) := by
  constructor
  · intro hu u σ
    exact (σ.hasSum_iff.mpr (hu u)).summable.mono_filter
      (SummationFilter.conditional ℕ).le_atTop
  · intro hperm u
    exact hasSum_of_summable_conditional_permutations
      ((show IsTopologicalBasis x (fun m ↦ (f m).toLinearMap) from h).2 u) (hperm u)

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
    IsTopologicalBasis coordinateVector (fun n ↦ (coordinateFunctional n).toLinearMap) := by
  refine ⟨fun m n ↦ ?_, fun u ↦ ?_⟩
  · simp [ContinuousLinearMap.coe_proj, LinearMap.proj_apply, Pi.single_apply]
  · rw [Pi.hasSum]
    intro j
    simp only [ContinuousLinearMap.coe_proj, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero]
    have : HasSum (fun b : ℕ ↦ if j = b then u b else 0) (u j)
        (SummationFilter.conditional ℕ) := by
      simpa using hasSum_sum_of_ne_finset_zero (L := SummationFilter.conditional ℕ) (s := {j})
        (fun b hb ↦
          ite_eq_right (Ne.symm (Finset.notMem_singleton.mp hb)))
    exact this

/-- Paper: Definition 4.1.2.1(1), p. 158. The basic projections of the coordinate
basis of the complex sequence space are equicontinuous in the product topology. -/
theorem pi_isEquicontinuous :
    IsEquicontinuous coordinateVector coordinateFunctional := by
  have hproj (k : ℕ) (u : ℕ → ℂ) (j : ℕ) :
      partialProjection coordinateVector coordinateFunctional k u j =
        if j ≤ k then u j else 0 := by
    simp only [partialProjection, sum_apply, ContinuousLinearMap.smulRight_apply,
      Finset.sum_apply, ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_Iic]
  unfold IsEquicontinuous EquicontinuousAt
  intro U hU
  rw [uniformity_eq_comap_nhds_zero'] at hU
  obtain ⟨V, hV, hVU⟩ := Filter.mem_comap.mp hU
  -- Every basic product neighborhood of zero is preserved by coordinate truncation.
  rw [nhds_pi] at hV
  obtain ⟨I, hI, s, hs, hsV⟩ := Filter.mem_pi.mp hV
  filter_upwards [set_pi_mem_nhds (x := (0 : ℕ → ℂ)) hI (fun j _ ↦ hs j)] with u hu k
  apply hVU
  simp only [mem_preimage, map_zero, neg_zero, add_zero]
  apply hsV
  intro j hj
  rw [hproj]
  split_ifs
  · exact hu j hj
  · exact mem_of_mem_nhds (hs j)

/-- Paper: Definition 4.1.2.1(3), p. 158. The coordinate basis of the complex
sequence space with the product topology is absolute. -/
theorem pi_isAbsolute :
    IsAbsolute coordinateVector coordinateFunctional := by
  classical
  intro q hq
  let p (n : ℕ) : Seminorm ℂ (ℕ → ℂ) := (normSeminorm ℂ ℂ).comp (LinearMap.proj n)
  let e := Equiv.sigmaEquivProd ℕ Unit
  have hp : WithSeminorms p :=
    (withSeminorms_pi fun _ : ℕ ↦ norm_withSeminorms ℂ ℂ).congr_equiv
      (e.trans (Equiv.prodUnique ℕ Unit)).symm
  obtain ⟨s, C, _, hC⟩ := Seminorm.bound_sum_of_continuous hp q hq
  let term (m : ℕ) : (ℕ → ℂ) →L[ℂ] (ℕ → ℂ) :=
    (coordinateFunctional m).smulRight ((coordinateVector : ℕ → ℕ → ℂ) m)
  let r (m : ℕ) := q.comp (term m).toLinearMap
  refine ⟨∑ m ∈ s, r m,
    Seminorm.continuous_finsetSum (fun m _ ↦ hq.comp (term m).continuous), ?_⟩
  intro u
  -- Outside the controlling coordinates, the seminorm of each coordinate term is zero.
  have hz (m : ℕ) (hm : m ∉ s) : q (term m u) = 0 := by
    have h := hC (term m u)
    rw [smul_apply] at h
    change q _ ≤ C • (FunLike.coeAddMonoidHom _ _ _ (∑ i ∈ s, p i)) _ at h
    rw [map_sum, Finset.sum_apply, Finset.sum_eq_zero (fun i hi ↦ ?_), smul_zero] at h
    · exact le_antisymm h (apply_nonneg q _)
    · have him : i ≠ m := fun him ↦ hm (him ▸ hi)
      change ‖term m u i‖ = 0
      simp [term, ContinuousLinearMap.smulRight_apply, Pi.smul_apply, Pi.single_eq_of_ne him]
  change Summable (fun m ↦ q (term m u)) ∧ (∑' m, q (term m u)) ≤ (∑ m ∈ s, r m) u
  have hs := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ) hz
  refine ⟨hs.summable, le_of_eq ?_⟩
  rw [hs.tsum_eq]
  change _ = (FunLike.coeAddMonoidHom _ _ _ (∑ m ∈ s, r m)) u
  rw [map_sum, Finset.sum_apply]
  rfl

/-- Paper: Definition 4.1.2.1(4), p. 158. The coordinate basis of the complex
sequence space with the product topology is boundedly complete. -/
theorem pi_isBoundedlyComplete : IsBoundedlyComplete coordinateVector := by
  intro a _
  -- In the product topology every coordinate series is eventually constant, so the
  -- ordered partial sums converge to the scalar sequence itself.
  refine ⟨a, ?_⟩
  rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff]
  simp only [Function.comp_def]
  rw [tendsto_pi_nhds]
  intro n
  refine tendsto_atTop_of_eventually_const (i₀ := n + 1) fun N hN ↦ ?_
  rw [Finset.sum_apply]
  have hn : n ∈ Finset.range N := Finset.mem_range.mpr (Nat.lt_of_succ_le hN)
  rw [Finset.sum_eq_single_of_mem n hn]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
  · intro m _ hmn
    rw [Pi.smul_apply, Pi.single_eq_of_ne hmn.symm, smul_zero]

/-- Paper: Definition 4.1.2.1(5), p. 158. A countable orthonormal Hilbert basis is
shrinking, with its coefficients given by the inner products against its vectors. -/
theorem hilbertBasis_isShrinking {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (b : HilbertBasis ℕ ℂ H) :
    IsShrinking (fun n ↦ b n) (fun n ↦ innerSL ℂ (b n)) := by sorry

/-- Paper: Definition 4.1.2.1(6), p. 158. Every zero neighborhood in the complex
sequence space with the product topology contains a coordinate basis vector. -/
theorem pi_not_isRegular : ¬ IsRegular coordinateVector := by
  rintro ⟨U, hU, havoid⟩
  have hzero : Tendsto coordinateVector atTop (𝓝 (0 : ℕ → ℂ)) := by
    refine tendsto_pi_nhds.mpr fun j ↦ ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ne_atTop j] with n hn
    simp only [Pi.single_eq_of_ne' hn, Pi.zero_apply]
  obtain ⟨n, hn⟩ := (hzero.eventually hU).exists
  exact havoid n hn

/-- Paper: Definition 4.1.2.1(6), p. 158. A countable orthonormal Hilbert basis is
normalized in the paper's sense. -/
theorem hilbertBasis_isNormalized {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (b : HilbertBasis ℕ ℂ H) : IsNormalized (fun n ↦ b n) := by
  have hnorm (n : ℕ) : ‖b n‖ = 1 := b.orthonormal.norm_eq_one n
  constructor
  · refine ⟨Metric.ball 0 1, Metric.ball_mem_nhds 0 zero_lt_one, fun n ↦ ?_⟩
    rw [mem_ball_zero_iff, hnorm]
    exact lt_irrefl 1
  · refine (NormedSpace.isVonNBounded_iff' ℂ).mpr ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact (hnorm n).le

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
    ¬ EquicontinuousAt (fun n (u : ℕ → ℂ) ↦ coordinateFunctional n u) 0 := by
  rw [Metric.equicontinuousAt_iff_right]
  push Not
  refine ⟨1 / 2, by norm_num, ?_⟩
  rw [Filter.frequently_iff]
  intro t ht
  rw [nhds_pi] at ht
  obtain ⟨I, hIfin, q, hq, hqsub⟩ := Filter.mem_pi.mp ht
  obtain ⟨j, hj⟩ := hIfin.exists_notMem
  refine ⟨Pi.single j (1 : ℂ), ?_, j, ?_⟩
  · refine hqsub ?_
    rw [Set.mem_pi]
    intro a ha
    have haj : a ≠ j := by
      intro haeq
      subst haeq
      exact hj ha
    rw [Pi.single_eq_of_ne haj]
    exact mem_of_mem_nhds (hq a)
  · simp only [ContinuousLinearMap.proj_apply, Pi.zero_apply, Pi.single_eq_same,
      dist_eq_norm, zero_sub, norm_neg, norm_one]
    norm_num

/-- Paper: Remark 4.1.2.2, p. 159. A Schauder basis with equicontinuous
coefficient functionals is regular. -/
theorem isRegular_of_equicontinuous_coeff (hb : IsSchauderBasis x f)
    (hf : EquicontinuousAt (fun m ↦ (f m : E → ℂ)) 0) : IsRegular x := by
  refine ⟨{u | ∀ n, dist (f n 0) (f n u) < 1},
    Metric.equicontinuousAt_iff_right.mp hf 1 zero_lt_one, ?_⟩
  intro n hn
  have hdiag : f n (x n) = 1 := by simpa using hb.1 n n
  simpa [hdiag] using hn n

section RegularCoefficients

open scoped ComplexOrder

section

variable [PolynormableSpace ℂ E] [T2Space E]

omit [T2Space E] in
/-- The coordinate scalars of a regular basis converge pointwise to zero. -/
private theorem tendsto_coeff_zero_of_regular [IsTopologicalAddGroup E]
    (hb : IsSchauderBasis x f) (hr : IsRegular x)
    (u : E) : Tendsto (fun n ↦ f n u) atTop (𝓝 0) := by
  obtain ⟨U, hU, hx⟩ := hr
  obtain ⟨p, hp, hpU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
  have hpx (n : ℕ) : 1 ≤ p (x n) := le_of_not_gt fun hn ↦
    hx n (hpU (p.mem_ball_zero.mpr hn))
  have hs : Tendsto (fun n ↦ ∑ i ∈ Finset.range n, f i u • x i) atTop (𝓝 u) := by
    have h := hb.2 u
    rw [HasSum, SummationFilter.conditional_filter_eq_map_range, tendsto_map'_iff] at h
    exact h
  have ht : Tendsto (fun n ↦ f n u • x n) atTop (𝓝 0) := by
    have hd := (hs.comp (tendsto_add_atTop_nat 1)).sub hs
    simpa only [Function.comp_def, Finset.sum_range_succ_sub_sum, sub_self] using hd
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h := (hp.tendsto 0).comp ht
  rw [map_zero] at h
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ ?_) h
  exact (le_mul_of_one_le_right (norm_nonneg _) (hpx n)).trans_eq
    (map_smul_eq_mul p (f n u) (x n)).symm

/-- A pointwise null sequence of continuous functionals is uniformly bounded
on each weakly compact convex set. -/
private theorem coeff_bounded_on_weakDisk
    (hf : ∀ u, Tendsto (fun n ↦ f n u) atTop (𝓝 0))
    {K : Set E} (hK : IsCompact (X := WeakSpace ℂ E) K) (hc : Convex ℂ K) :
    ∃ C : ℝ, 0 < C ∧ ∀ u ∈ K, ∀ n, ‖f n u‖ ≤ C := by
  let : SeparatingDual ℂ E := polynormableSpace_separatingDual ℂ E
  rcases K.eq_empty_or_nonempty with rfl | hKn
  · exact ⟨1, one_pos, by simp⟩
  let K' : Set (WeakSpace ℂ E) := K
  have : CompactSpace K' := isCompact_iff_compactSpace.mp hK
  have : Nonempty K' := hKn.to_subtype
  let F (M : ℕ) : Set K' := {u | ∀ n, ‖f n u.val‖ ≤ M}
  have hFclosed (M : ℕ) : IsClosed (F M) := by
    have heq : F M = ⋂ n, {u : K' | ‖f n u.val‖ ≤ M} := by
      ext u
      simp [F]
    rw [heq]
    exact isClosed_iInter fun n ↦ isClosed_le
      ((WeakBilin.eval_continuous (topDualPairing ℂ E).flip (f n)).comp
        continuous_subtype_val).norm continuous_const
  have hcover : ⋃ M, F M = univ := by
    apply eq_univ_of_forall
    intro u
    obtain ⟨r, hr⟩ := Metric.isBounded_iff_subset_closedBall (0 : ℂ) |>.mp
      (Metric.isBounded_range_of_tendsto _ (hf u.val))
    obtain ⟨M, hM⟩ := exists_nat_ge r
    exact mem_iUnion.mpr ⟨M, fun n ↦ (mem_closedBall_zero_iff.mp (hr (mem_range_self n))).trans hM⟩
  -- The Baire theorem gives a bound on a relatively open part of the compact set.
  obtain ⟨M, a, ha⟩ := nonempty_interior_of_iUnion_of_closed hFclosed hcover
  obtain ⟨V, hV, hsub⟩ := (mem_nhds_subtype K' a (F M)).mp (mem_interior_iff_mem_nhds.mp ha)
  have ha' : a ∈ F M := interior_subset ha
  -- One sufficiently small homothety sends the entire compact set into that part.
  have hnear : ∀ᶠ t : ℝ in 𝓝 0,
      ∀ y ∈ K', a.val + (t : ℂ) • (y - a.val) ∈ V := by
    apply hK.eventually_forall_of_forall_eventually
    intro y _
    have hcont : Continuous (fun z : ℝ × WeakSpace ℂ E ↦
        a.val + (z.1 : ℂ) • (z.2 - a.val)) :=
      continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).smul
        (continuous_snd.sub continuous_const))
    exact hcont.continuousAt (x := (0, y)).preimage_mem_nhds
      (by simpa using hV)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hlt : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds zero_lt_one)
  have : NeBot (𝓝[>] (0 : ℝ)) := nhdsGT_neBot 0
  obtain ⟨t, ⟨ht, ht1⟩, htV⟩ := ((hpos.and hlt).and (hnear.filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨(M + M) / t + 1, by positivity, fun u hu n ↦ ?_⟩
  let y : WeakSpace ℂ E := u
  let w : WeakSpace ℂ E := a.val + (t : ℂ) • (y - a.val)
  have hu' : w ∈ K' := by
    have hc' : Convex ℝ K' := hc.lift ℝ
    exact hc'.add_smul_sub_mem a.property hu ⟨ht.le, ht1.le⟩
  let z : K' := ⟨w, hu'⟩
  have hz : z ∈ F M := hsub (htV y hu)
  have heq : f n z.val - (1 - (t : ℂ)) * f n a.val = (t : ℂ) * f n u := by
    let a₀ : E := a.val
    change f n (a₀ + (t : ℂ) • (u - a₀)) - (1 - (t : ℂ)) * f n a₀ = _
    simp only [map_add, map_smul, map_sub, smul_eq_mul]
    ring
  have hbound : ‖(t : ℂ) * f n u‖ ≤ (M : ℝ) + M := by
    rw [← heq]
    refine (norm_sub_le _ _).trans (add_le_add (hz n) ?_)
    rw [norm_mul, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr ht1.le)]
    exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith)).trans (ha' n)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le] at hbound
  exact ((le_div_iff₀' ht).mpr hbound).trans (le_add_of_nonneg_right zero_le_one)

omit [PolynormableSpace ℂ E] [T2Space E] in
/-- Convergence in the Mackey topology of the dual can be tested by uniform convergence
of the evaluations on weakly compact absolutely convex subsets. -/
private theorem tendsto_mackeyDual_iff {ι : Type*} {l : Filter ι}
    {g : ι → StrongDual ℂ E} {φ : StrongDual ℂ E} :
    Tendsto g l (@nhds _ (mackeyTopology (topDualPairing ℂ E)) φ) ↔
      ∀ K : Set E, AbsConvex ℂ K → IsCompact (X := WeakSpace ℂ E) K →
        TendstoUniformlyOn (fun i u ↦ g i u) φ l K := by
  let S : Set (Set E) := {K | AbsConvex ℂ K ∧ IsCompact (X := WeakSpace ℂ E) K}
  let ev (ψ : StrongDual ℂ E) := UniformOnFun.ofFun S (fun u ↦ ψ u)
  change Tendsto g l (@nhds _ (TopologicalSpace.induced ev inferInstance) φ) ↔ _
  rw [nhds_induced, tendsto_comap_iff, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  simp only [S, ev, mem_ofPred_eq, and_imp, Function.comp_def, UniformOnFun.toFun_ofFun]

/-- Sequential completeness of the Mackey dual makes every absolutely summable
combination of a pointwise null sequence of functionals continuous. -/
private theorem exists_dual_of_summable_coeff
    (hf : ∀ u, Tendsto (fun n ↦ f n u) atTop (𝓝 0))
    (hseq : let τ := mackeyTopology (topDualPairing ℂ E)
      ∀ g : ℕ → StrongDual ℂ E,
        (∀ U ∈ @nhds _ τ 0, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n → g m - g n ∈ U) →
        ∃ φ, Tendsto g atTop (@nhds _ τ φ))
    (a : ℕ → ℂ) (ha : Summable (fun n ↦ ‖a n‖)) :
    ∃ φ : StrongDual ℂ E, ∀ u, HasSum (fun n ↦ a n * f n u) (φ u) := by
  let g (n : ℕ) : StrongDual ℂ E := ∑ i ∈ Finset.range n, a i • f i
  have hg (n : ℕ) (u : E) : g n u = ∑ i ∈ Finset.range n, a i * f i u := by
    simp [g, smul_eq_mul]
  have hCauchy :
      Tendsto (fun p : ℕ × ℕ ↦ g p.1 - g p.2) (atTop ×ˢ atTop)
        (@nhds _ (mackeyTopology (topDualPairing ℂ E)) 0) := by
    refine tendsto_mackeyDual_iff.mpr fun K hK hcomp ↦ ?_
    obtain ⟨C, hC, hbound⟩ := coeff_bounded_on_weakDisk hf hcomp hK.2
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp ha.hasSum.tendsto_sum_nat.cauchySeq
      (ε / C) (div_pos hε hC)
    have hle (m n : ℕ) (hm : N ≤ m) (hn : N ≤ n) (hmn : n ≤ m) (u : E) (hu : u ∈ K) :
        ‖g m u - g n u‖ < ε := by
      have ht := hN m hm n hn
      rw [Real.dist_eq, ← Finset.sum_Ico_eq_sub _ hmn, abs_of_nonneg
        (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at ht
      rw [hg, hg, ← Finset.sum_Ico_eq_sub _ hmn]
      calc
        ‖∑ i ∈ Finset.Ico n m, a i * f i u‖
          ≤ ∑ i ∈ Finset.Ico n m, ‖a i‖ * C := by
            refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_left (hbound u hu i) (norm_nonneg _)
        _ = (∑ i ∈ Finset.Ico n m, ‖a i‖) * C := by rw [Finset.sum_mul]
        _ < ε := (lt_div_iff₀ hC).mp ht
    refine eventually_prod_iff.mpr
      ⟨fun m ↦ N ≤ m, eventually_ge_atTop N, fun n ↦ N ≤ n, eventually_ge_atTop N, ?_⟩
    intro m hm n hn u hu
    simp only [sub_apply, zero_apply, dist_zero_left]
    rcases le_total n m with hmn | hnm
    · exact hle m n hm hn hmn u hu
    · rw [norm_sub_rev]
      exact hle n m hn hm hnm u hu
  obtain ⟨φ, hφ⟩ := hseq g fun U hU ↦ by
    obtain ⟨_, hm, _, hn, hmem⟩ := eventually_prod_iff.mp (hCauchy.eventually hU)
    obtain ⟨M, hM⟩ := eventually_atTop.mp hm
    obtain ⟨N, hN⟩ := eventually_atTop.mp hn
    exact ⟨max M N, fun m n hm hn ↦ hmem (hM m ((le_max_left _ _).trans hm))
      (hN n ((le_max_right _ _).trans hn))⟩
  refine ⟨φ, fun u ↦ ?_⟩
  obtain ⟨C, _, hbound⟩ := coeff_bounded_on_weakDisk hf
    (K := {u}) isCompact_singleton (convex_singleton _)
  have hs : Summable (fun n ↦ a n * f n u) := (ha.mul_right C).of_norm_bounded fun n ↦ by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hbound u (mem_singleton _) n) (norm_nonneg _)
  let v : WeakSpace ℂ E := u
  let L : ℂ →ₗ[ℂ] WeakSpace ℂ E := (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight v
  let D := Metric.closedBall (0 : ℂ) 1
  have hD : AbsConvex ℂ (L '' D) :=
    ⟨(balanced_closedBall_zero (𝕜 := ℂ)).image L,
      (convex_RCLike_iff_convex_real.mpr (convex_closedBall (0 : ℂ) 1)).linear_image L⟩
  have hcompact : IsCompact (L '' D) := (isCompact_closedBall _ _).image
    (continuous_id.smul continuous_const)
  have hu : v ∈ L '' D := ⟨1, by simp [D], by change (1 : ℂ) • v = v; simp⟩
  have hpoint : Tendsto (fun n ↦ g n u) atTop (𝓝 (φ u)) :=
    (tendsto_mackeyDual_iff.mp hφ _ hD hcompact).tendsto_at hu
  have heq := tendsto_nhds_unique hs.hasSum.tendsto_sum_nat (by simpa only [hg] using hpoint)
  simpa only [heq] using hs.hasSum

/-- A pointwise null sequence in a sequentially complete Mackey dual lies in
an absolutely convex weakly compact set of continuous functionals. -/
private theorem exists_weakly_compact_disk_of_coeff
    (hf : ∀ u, Tendsto (fun n ↦ f n u) atTop (𝓝 0))
    (hseq : let τ := mackeyTopology (topDualPairing ℂ E)
      ∀ g : ℕ → StrongDual ℂ E,
        (∀ U ∈ @nhds _ τ 0, ∃ N : ℕ, ∀ m n, N ≤ m → N ≤ n → g m - g n ∈ U) →
        ∃ φ, Tendsto g atTop (@nhds _ τ φ)) :
    ∃ D : Set (StrongDual ℂ E), AbsConvex ℂ D ∧
      IsCompact (X := WeakBilin (topDualPairing ℂ E)) D ∧ range f ⊆ D := by
  classical
  let A : Set (ℕ → ℂ) := {a | ∀ k, ∑ i ∈ Finset.range k, ‖a i‖ ≤ 1}
  let p (k : ℕ) : Seminorm ℂ (ℕ → ℂ) :=
    ∑ i ∈ Finset.range k, (normSeminorm ℂ ℂ).comp (LinearMap.proj i)
  have hp (k : ℕ) (a : ℕ → ℂ) : p k a = ∑ i ∈ Finset.range k, ‖a i‖ := by
    simp [p, Seminorm.comp_apply]
  have hAeq : A = ⋂ k, (p k).closedBall 0 1 := by
    ext a
    simp [A, hp]
  have hA : AbsConvex ℂ A := by
    rw [hAeq]
    exact ⟨balanced_iInter fun k ↦ (p k).balanced_closedBall_zero 1,
      convex_iInter fun k ↦ convex_RCLike_iff_convex_real.mpr ((p k).convex_closedBall 0 1)⟩
  have hAcompact : IsCompact A := by
    have hclosed : IsClosed A := by
      rw [hAeq]
      refine isClosed_iInter fun k ↦ ?_
      rw [show (p k).closedBall 0 1 = {a | ∑ i ∈ Finset.range k, ‖a i‖ ≤ 1} by
        ext a
        simp [hp]]
      exact isClosed_le (continuous_finsetSum _ fun i _ ↦ (continuous_apply i).norm)
        continuous_const
    refine (isCompact_univ_pi fun _ : ℕ ↦ isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset
      hclosed fun a ha i _ ↦ mem_closedBall_zero_iff.mpr ?_
    exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (a j))
      (Finset.mem_range.mpr (Nat.lt_succ_self i))).trans (ha (i + 1))
  have hsum (a : A) : Summable (fun i ↦ ‖a.val i‖) :=
    summable_of_sum_range_le (fun _ ↦ norm_nonneg _) a.property
  -- Map the compact unit ball of absolutely summable weights into the weak dual.
  choose φ hφ using fun a : A ↦ exists_dual_of_summable_coeff hf hseq a.val (hsum a)
  have huniq (a : A) (ψ : StrongDual ℂ E) (hψ : ∀ u, HasSum (fun i ↦ a.val i * f i u) (ψ u)) :
      φ a = ψ :=
    ContinuousLinearMap.ext fun u ↦ (hφ a u).unique (hψ u)
  have hcontinuous : @Continuous A (WeakBilin (topDualPairing ℂ E)) _
      (WeakBilin.instTopologicalSpace _) φ := by
    refine WeakBilin.continuous_of_continuous_eval _ fun u ↦ ?_
    change Continuous (fun a ↦ φ a u)
    -- The tails are uniformly small because the absolute weights sum to at most one.
    let G (k : ℕ) (a : A) := ∑ i ∈ Finset.range k, a.val i * f i u
    have hconv : TendstoUniformly G (fun a ↦ φ a u) atTop := by
      rw [Metric.tendstoUniformly_iff]
      intro ε hε
      obtain ⟨N, hN⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp (hf u) (ε / 2) (half_pos hε))
      filter_upwards [eventually_ge_atTop N] with k hk a
      have htail : HasSum (fun j : ℕ ↦ a.val (j + k) * f (j + k) u) (φ a u - G k a) :=
        (hasSum_nat_add_iff' k).mpr (hφ a u)
      have hnormtail : Summable (fun j : ℕ ↦ ‖a.val (j + k)‖) :=
        (summable_nat_add_iff k).mpr (hsum a)
      have habs : (∑' j : ℕ, ‖a.val (j + k)‖) ≤ 1 := by
        have h := (hsum a).sum_add_tsum_nat_add k
        exact (le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).trans
          (h.trans_le ((hsum a).tsum_le_of_sum_range_le a.property))
      have hestimate := htail.norm_le_of_bounded (hnormtail.hasSum.mul_right (ε / 2)) (fun j ↦ by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [dist_zero_right] using
            (hN (j + k) (hk.trans (Nat.le_add_left _ _))).le) (norm_nonneg _))
      rw [dist_eq_norm]
      exact (hestimate.trans (mul_le_mul_of_nonneg_right habs (half_pos hε).le)).trans_lt
        (by simpa only [one_mul] using half_lt_self hε)
    refine hconv.continuous (Eventually.of_forall fun k ↦ ?_).frequently
    unfold G
    exact continuous_finsetSum _ fun i _ ↦
      ((continuous_apply i).comp continuous_subtype_val).mul continuous_const
  refine ⟨range φ, ⟨?_, ?_⟩, ?_, ?_⟩
  · rw [balanced_iff_smul_mem]
    rintro c hc _ ⟨a, rfl⟩
    refine ⟨⟨c • a.val, balanced_iff_smul_mem.mp hA.1 hc a.property⟩, huniq _ _ fun u ↦ ?_⟩
    simpa only [Pi.smul_apply, smul_eq_mul, smul_apply, mul_assoc]
      using (hφ a u).mul_left c
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ c d hc hd hcd
    refine ⟨⟨c • a.val + d • b.val, hA.2 a.property b.property hc hd hcd⟩,
      huniq _ _ fun u ↦ ?_⟩
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, smul_apply,
      add_apply, add_mul, mul_assoc]
      using ((hφ a u).mul_left c).add ((hφ b u).mul_left d)
  · let : CompactSpace A := isCompact_iff_compactSpace.mp hAcompact
    exact isCompact_range hcontinuous
  · rintro _ ⟨n, rfl⟩
    let e (i : ℕ) : ℂ := if i = n then 1 else 0
    have hn : e ∈ A := by
      intro k
      simp only [e, apply_ite (fun z : ℂ ↦ ‖z‖), norm_one, norm_zero, Finset.sum_ite_eq']
      split_ifs <;> simp
    refine ⟨⟨e, hn⟩, huniq _ _ fun u ↦ ?_⟩
    convert hasSum_ite_eq n (f n u) using 1
    funext i
    by_cases hi : i = n <;> simp [e, hi]

end

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
    EquicontinuousAt (fun m ↦ (f m : E → ℂ)) 0 := by
  obtain ⟨D, hD, hcompact, hsub⟩ :=
    exists_weakly_compact_disk_of_coeff (tendsto_coeff_zero_of_regular hb hr) hseq
  let K : Set (Set (StrongDual ℂ E)) :=
    {A | AbsConvex ℂ A ∧ IsCompact (X := WeakBilin (topDualPairing ℂ E)) A}
  let ev (u : E) := UniformOnFun.ofFun K (fun φ : StrongDual ℂ E ↦ φ u)
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  rw [show (𝓝 (0 : E)) = @nhds E (mackeyTopology (topDualPairing ℂ E).flip) 0 from
    congrArg (fun t ↦ @nhds E t 0) hM]
  change _ ∈ @nhds _ (TopologicalSpace.induced ev inferInstance) 0
  rw [nhds_induced]
  have hU := UniformOnFun.gen_mem_nhds ℂ K (ev 0) (s := D)
    (show D ∈ K from ⟨hD, hcompact⟩) (Metric.uniformity_basis_dist.mem_of_mem hε)
  filter_upwards [preimage_mem_comap hU] with u hu n
  exact hu (f n) (hsub (mem_range_self n))

end RegularCoefficients

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
