module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
public import RiemannMasullo.ForMathlib.Analysis.Distribution.TestFunction
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Group.Pointwise.Set.Scalar
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.FiniteExhaustion
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Symmetric
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Instances.RealVectorSpace
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Real
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.LocallyConvex.AbsConvex
import Mathlib.Analysis.LocallyConvex.Polar
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.StrongTopology
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Montel
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.StrongBidual
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.HahnBanach
import RiemannMasullo.ForMathlib.Analysis.Normed.Module.Seminorm.DirectSum
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.PiL2
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Compactness.Bases
import Mathlib.Topology.LocallyConstant.Algebra
import RiemannMasullo.ForMathlib.Topology.LocallyConstant.CompactSupport

/-!
# Schwartz–Bruhat functions

Masullo, §2.1, pp. 59–74. We use the Schwartz–Bruhat spaces of Appendix D
and the tensor topologies of Appendix C. As in Appendix A, a finite set of
places containing the Archimedean places is represented by its finite part.
-/

@[expose] public noncomputable section

open Bornology Filter Function IsDedekindDomain NumberField Set Topology
open scoped BigOperators Cardinal ContDiff NumberField.AdeleRing RestrictedProduct TensorProduct
  UniformConvergenceCLM

namespace RiemannMasullo

universe u v

local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)
local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)

section Euclidean

open TopologicalSpace
open scoped Distributions

/-- Paper: Example 2.1.1.1, p. 59. A fixed compact support stage embeds
topologically into the smooth compactly supported test functions on the real line.
The ordinary distribution space in the example is the strong dual of this Mathlib test space. -/
theorem realTestFunction_stage_isEmbedding (K : Compacts ℝ) :
    IsEmbedding (TestFunction.ofSupportedInCLM ℂ
      (show (K : Set ℝ) ⊆ (⊤ : Opens ℝ) from Set.subset_univ _) :
        𝓓_{K}(ℝ, ℂ) →L[ℂ] 𝓓(⊤, ℂ)) := by
  exact isEmbedding_testFunction_ofSupportedIn (Set.subset_univ _)

/-- Paper: (2.1.1.1)–(2.1.1.4), p. 60. The weighted magnitude is the norm
of the mixed partial derivative times one plus the absolute coordinate monomial.
Deviation: On smooth functions the mixed partial is evaluated by applying
the iterated Fréchet derivative to the corresponding coordinate vectors. -/
def euclideanSchwartzWeightedDeriv {m : ℕ} (α β : Fin m → ℕ)
    (f : EuclideanSpace ℝ (Fin m) → ℂ) (x : EuclideanSpace ℝ (Fin m)) : ℝ :=
  let directions := (List.finRange m).flatMap fun i ↦ List.replicate (β i) i
  (1 + |∏ i, (x i) ^ α i|) *
    ‖iteratedFDeriv ℝ directions.length f x
      (fun j ↦ EuclideanSpace.single (directions.get j) 1)‖

/-- Paper: (2.1.1.4), p. 61. With both multi-indices zero the expression
reduces to twice the norm of the original value. -/
theorem euclideanSchwartzWeightedDeriv_zero {m : ℕ}
    (f : EuclideanSpace ℝ (Fin m) → ℂ) (x : EuclideanSpace ℝ (Fin m)) :
    euclideanSchwartzWeightedDeriv 0 0 f x = 2 * ‖f x‖ := by
  have h : (List.finRange m).flatMap (fun i ↦ List.replicate ((0 : Fin m → ℕ) i) i) = [] := by simp
  unfold euclideanSchwartzWeightedDeriv
  rw [h]
  simp [one_add_one_eq_two]

private abbrev coordinateWeightIndex {m : ℕ} (k : ℕ) (i : Option (Fin m)) : Fin m → ℕ :=
  i.elim 0 (fun j ↦ Pi.single j k)

private theorem exists_coordinate_weight {m : ℕ} (k : ℕ) (x : EuclideanSpace ℝ (Fin m)) :
    ∃ i : Option (Fin m), ‖x‖ ^ k ≤ ((m : ℝ) + 1) ^ k * |∏ j, x j ^ coordinateWeightIndex k i j| := by
  classical
  let b : Option (Fin m) → ℝ := fun i ↦ i.elim 1 (fun j ↦ |x j|)
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ b Finset.univ_nonempty
  have hbi : 1 ≤ b i := hi none (Finset.mem_univ _)
  have hb := zero_le_one.trans hbi
  have hx : ‖x‖ ≤ ((m : ℝ) + 1) * b i := by
    have hrepr := (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr x
    calc
      ‖x‖ ≤ ∑ j, |x j| := by
        conv_lhs => rw [← hrepr]
        refine (norm_sum_le _ _).trans_eq ?_
        simp only [norm_smul, OrthonormalBasis.norm_eq_one, EuclideanSpace.basisFun_repr,
          Real.norm_eq_abs, mul_one]
      _ ≤ ∑ _j : Fin m, b i := Finset.sum_le_sum fun j _ ↦ hi (some j) (Finset.mem_univ _)
      _ ≤ _ := by simp; linarith
  use i
  have hpow := pow_le_pow_left₀ (norm_nonneg _) hx k
  rw [mul_pow] at hpow
  convert hpow using 2
  cases i with
  | none => simp [coordinateWeightIndex, b]
  | some j => simp [coordinateWeightIndex, b, Pi.single, Function.update, apply_ite, abs_pow]

private abbrev coordinateMultiplicity {m n : ℕ} (t : Fin n → Fin m) (j : Fin m) := (List.ofFn t).count j

private theorem perm_coordinate_directions {m n : ℕ} (t : Fin n → Fin m) :
    (List.ofFn t).Perm ((List.finRange m).flatMap fun i ↦ List.replicate (coordinateMultiplicity t i) i) := by
  apply List.perm_iff_count.mpr
  intro j
  rw [List.count_flatMap, ← Fin.sum_univ_def]
  simp [List.count_replicate, coordinateMultiplicity]

/-- Bounds on finitely many weighted mixed partials control each weighted Fréchet derivative. -/
private theorem schwartz_norm_bound_of_coordinates {m : ℕ} (k n : ℕ)
    {f : EuclideanSpace ℝ (Fin m) → ℂ} (hf : ContDiff ℝ (∞) f)
    (x : EuclideanSpace ℝ (Fin m)) {C : ℝ}
    (hC : ∀ (i : Option (Fin m)) (t : Fin n → Fin m),
      euclideanSchwartzWeightedDeriv (coordinateWeightIndex k i) (coordinateMultiplicity t) f x ≤ C) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖ ≤
      (((m : ℝ) + 1) ^ k * Fintype.card (Fin n → Fin m)) * C := by
  classical
  let T := iteratedFDeriv ℝ n f x
  let e (j : Fin m) := EuclideanSpace.single j (1 : ℝ)
  obtain ⟨i, hi⟩ := exists_coordinate_weight k x
  let w := |∏ j, x j ^ coordinateWeightIndex k i j|
  have heval (t : Fin n → Fin m) : w * ‖T (fun j ↦ e (t j))‖ ≤ C := by
    let dirs := (List.finRange m).flatMap fun j ↦ List.replicate (coordinateMultiplicity t j) j
    have heq : T (fun j ↦ e (t j)) = iteratedFDeriv ℝ dirs.length f x (fun j ↦ e (dirs.get j)) := by
      have H := iteratedFDeriv_apply_list_perm hf e (perm_coordinate_directions t) x
      let eval (s : (Σ r, Fin r → Fin m)) := iteratedFDeriv ℝ s.1 f x (fun j ↦ e (s.2 j))
      exact (congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨n, t⟩)).symm.trans H
    rw [heq]
    exact (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (norm_nonneg _)).trans (hC i t)
  calc
    ‖x‖ ^ k * ‖T‖ ≤ (((m : ℝ) + 1) ^ k * w) * ∑ t : Fin n → Fin m, ‖T (fun j ↦ e (t j))‖ :=
      mul_le_mul hi (norm_multilinear_le_sum_euclidean_basis T) (norm_nonneg _) (by positivity)
    _ = ((m : ℝ) + 1) ^ k * ∑ t : Fin n → Fin m, w * ‖T (fun j ↦ e (t j))‖ := by
      rw [mul_assoc, Finset.mul_sum]
    _ ≤ ((m : ℝ) + 1) ^ k * ∑ _ : Fin n → Fin m, C := by
      gcongr with t
      exact heval t
    _ = _ := by simp [mul_assoc]

/-- Each weighted mixed partial is bounded by the sum of an unweighted and a weighted Schwartz
seminorm of the same derivative order. -/
private theorem weighted_partial_le_schwartz_seminorms {m : ℕ}
    (f : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) (α β : Fin m → ℕ)
    (x : EuclideanSpace ℝ (Fin m)) :
    let n := ((List.finRange m).flatMap fun i ↦ List.replicate (β i) i).length
    euclideanSchwartzWeightedDeriv α β f x ≤ SchwartzMap.seminorm ℝ 0 n f + SchwartzMap.seminorm ℝ (∑ i, α i) n f := by
  let dirs := (List.finRange m).flatMap fun i ↦ List.replicate (β i) i
  let T := iteratedFDeriv ℝ dirs.length f x
  let v (j : Fin dirs.length) := EuclideanSpace.single (dirs.get j) (1 : ℝ)
  have hv (j : Fin dirs.length) : ‖v j‖ = 1 := by
    simpa only [v, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin m) ℝ).norm_eq_one (dirs.get j)
  have heval : ‖T v‖ ≤ ‖T‖ := by simpa only [hv, Finset.prod_const_one, mul_one] using T.le_opNorm v
  have hweight : |∏ i, x i ^ α i| ≤ ‖x‖ ^ (∑ i, α i) := by
    rw [← Real.norm_eq_abs, norm_prod]
    calc
      (∏ i, ‖x i ^ α i‖) ≤ ∏ i, ‖x‖ ^ α i := by
        refine Finset.prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ ?_)
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x i) (α i)
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
  change (1 + |∏ i, x i ^ α i|) * ‖T v‖ ≤ _
  rw [one_add_mul]
  exact add_le_add (heval.trans (f.norm_iteratedFDeriv_le_seminorm ℝ _ x))
    ((mul_le_mul hweight heval (norm_nonneg _) (by positivity)).trans (f.le_seminorm ℝ _ _ x))

/-- Paper: Definition 2.1.1.4, p. 60. A smooth function is Schwartz exactly when
each coordinate-monomial-weighted mixed partial derivative is bounded.
Deviation: The space uses Mathlib's equivalent norm and Fréchet-derivative
formulation. Finiteness of (2.1.1.4) is expressed by boundedness. -/
theorem schwartzMap_euclidean_iff (m : ℕ) (f : EuclideanSpace ℝ (Fin m) → ℂ) :
    (∃ g : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ, ∀ x, g x = f x) ↔
      ContDiff ℝ (∞) f ∧ ∀ α β : Fin m → ℕ,
        BddAbove (Set.range (euclideanSchwartzWeightedDeriv α β f)) := by
  constructor
  · rintro ⟨g, hg⟩
    obtain rfl : (g : _ → ℂ) = f := funext hg
    refine ⟨g.smooth', ?_⟩
    intro α β
    let n := ((List.finRange m).flatMap fun i ↦ List.replicate (β i) i).length
    refine ⟨SchwartzMap.seminorm ℝ 0 n g + SchwartzMap.seminorm ℝ (∑ i, α i) n g, ?_⟩
    rintro _ ⟨x, rfl⟩
    exact weighted_partial_le_schwartz_seminorms g α β x
  · rintro ⟨hf, h⟩
    choose C hC using h
    refine ⟨⟨f, hf, ?_⟩, fun _ ↦ rfl⟩
    intro k n
    let c (p : Option (Fin m) × (Fin n → Fin m)) := C (coordinateWeightIndex k p.1) (coordinateMultiplicity p.2)
    obtain ⟨B, hB⟩ := Finite.bddAbove_range c
    refine ⟨_, fun x ↦ schwartz_norm_bound_of_coordinates k n hf x (C := B) fun i t ↦ ?_⟩
    exact (hC _ _ (mem_range_self x)).trans (hB (mem_range_self (i, t)))

/-- Paper: Definition 2.1.1.4, p. 61. Mathlib's Schwartz topology agrees with
the topology generated by the weighted mixed partial seminorms from (2.1.1.4).
Deviation: The seminorm convergence criterion is stated in epsilon form. -/
theorem schwartzMap_euclidean_tendsto_iff {m : ℕ} {ι : Type*} (l : Filter ι)
    (f : ι → SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)
    (g : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) :
    Tendsto f l (𝓝 g) ↔ ∀ (α β : Fin m → ℕ) (ε : ℝ), 0 < ε →
      ∀ᶠ i in l, ∀ x, euclideanSchwartzWeightedDeriv α β (f i - g) x < ε := by
  classical
  rw [(schwartz_withSeminorms ℝ _ _).tendsto_nhds]
  constructor
  · intro h α β ε hε
    let n := ((List.finRange m).flatMap fun j ↦ List.replicate (β j) j).length
    filter_upwards [h (0, n) (ε / 2) (half_pos hε),
      h (∑ j, α j, n) (ε / 2) (half_pos hε)] with i hi₀ hi x
    exact (weighted_partial_le_schwartz_seminorms (f i - g) α β x).trans_lt
      ((add_lt_add hi₀ hi).trans_eq (add_halves ε))
  · rintro h ⟨k, n⟩ ε hε
    let C : ℝ := ((m : ℝ) + 1) ^ k * Fintype.card (Fin n → Fin m)
    have hC : 0 ≤ C := by positivity
    let δ := ε / (C + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    have hsmall : C * δ < ε := by
      calc
        C * δ < (C + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one C) hδ
        _ = ε := by
          dsimp only [δ]
          field_simp
    have hfinite : ∀ᶠ i in l, ∀ (j : Option (Fin m)) (t : Fin n → Fin m),
        ∀ x, euclideanSchwartzWeightedDeriv (coordinateWeightIndex k j) (coordinateMultiplicity t)
          (f i - g) x < δ := Filter.eventually_all.mpr fun j ↦ Filter.eventually_all.mpr
            fun t ↦ h _ _ _ hδ
    filter_upwards [hfinite] with i hi
    apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (f i - g)
      (mul_nonneg hC hδ.le) _) hsmall
    exact fun x ↦ schwartz_norm_bound_of_coordinates k n ((f i - g).smooth ⊤) x
      fun j t ↦ (hi j t x).le

section Nuclearity

open MeasureTheory UniformSpace
open scoped NNReal

/-- An absolutely summable rank-one expansion of a normed-space map induces an
integral evaluation form. -/
private theorem integral_evaluation_of_rankOne_series
    {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    [NormedAddCommGroup Y] [NormedSpace ℂ Y]
    (T : X →L[ℂ] Y) (φ : ℕ → X →L[ℂ] ℂ) (b : ℕ → Y)
    (hs : Summable (fun n ↦ ‖φ n‖ * ‖b n‖))
    (hT : ∀ x, HasSum (fun n ↦ φ n x • b n) (T x)) :
    IsIntegralBilinearForm (fun x (ψ : StrongDual ℂ Y) ↦ ψ (T x)) := by
  let F := StrongDual ℂ Y
  let : PolynormableSpace ℂ X := (norm_withSeminorms ℂ X).toPolynormableSpace
  let : PolynormableSpace ℂ F := (norm_withSeminorms ℂ F).toPolynormableSpace
  let L : X ⊗[ℂ] F →ₗ[ℂ] ℂ := TensorProduct.lift
    (LinearMap.mk₂ ℂ (fun x (ψ : F) ↦ ψ (T x))
      (by intros; simp) (by intros; simp) (by intros; rfl) (by intros; rfl))
  have hsum (z : X ⊗[ℂ] F) :
      HasSum (fun n ↦ (tensorDualOperator z (φ n)) (b n)) (L z) := by
    induction z using TensorProduct.inductionOn with
    | tmul x ψ =>
      simpa [L, tensorDualOperator_tmul] using (hT x).mapL ψ
    | add z w hz hw => simpa using hz.add hw
  let ε : Seminorm ℂ (InjectiveTensor X F) := injectiveTensorNorm X F
  let C : ℝ≥0 := ⟨∑' n, ‖φ n‖ * ‖b n‖, tsum_nonneg fun _ ↦ by positivity⟩
  have hbound (z : X ⊗[ℂ] F) : ‖L z‖ ≤ C * ε z := by
    obtain ⟨A, hA, hε⟩ := injectiveTensorNorm_eq_opNorm z
    have hterm (n : ℕ) :
        ‖(tensorDualOperator z (φ n)) (b n)‖ ≤ (‖φ n‖ * ‖b n‖) * ε z := by
      rw [← hA, show ε z = ‖A‖ from hε]
      calc
        ‖(A (φ n)) (b n)‖ ≤ ‖A (φ n)‖ * ‖b n‖ := (A (φ n)).le_opNorm _
        _ ≤ (‖A‖ * ‖φ n‖) * ‖b n‖ :=
          mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ = _ := by ring
    have hdom := hs.mul_right (ε z)
    have hs' := hdom.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
    change ‖L z‖ ≤ (∑' n, ‖φ n‖ * ‖b n‖) * ε z
    rw [← (hsum z).tsum_eq, ← tsum_mul_right]
    exact (norm_tsum_le_tsum_norm hs').trans (hs'.tsum_le_tsum hterm hdom)
  let hI := withGeneratingSeminorms_spec (X ⊗[ℂ] F)
    (fun UV : {U : Set X // U ∈ 𝓝 0} × {V : Set F // V ∈ 𝓝 0} ↦
      injectiveTensorSeminorm UV.1 UV.2)
  have hε : Continuous ε := hI.continuous_seminorm
    (⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩,
     ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds 0 one_pos⟩)
  let L' : InjectiveTensor X F →ₗ[ℂ] ℂ := L
  have hL : Continuous L' :=
    (norm_withSeminorms ℂ ℂ).continuous_of_continuous_comp L' fun _ ↦
      Seminorm.continuous_of_le (q := C • ε) (hε.const_smul C) hbound
  exact ⟨⟨L', hL⟩, fun _ _ ↦ rfl⟩

/-- A summable coefficient bound and a uniform vector bound in each continuous
seminorm suffice for nuclearity. -/
private theorem nuclear_of_rankOne_series
    {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [PolynormableSpace ℂ E] [T2Space E]
    (h : ∀ q : Seminorm ℂ E, Continuous q →
      ∃ (p : Seminorm ℂ E) (φ : ℕ → E →ₗ[ℂ] ℂ) (b : ℕ → E)
        (d : ℕ → ℝ) (C : ℝ), Continuous p ∧ 0 ≤ C ∧ Summable d ∧
        (∀ n, 0 ≤ d n) ∧ (∀ n x, ‖φ n x‖ ≤ d n * p x) ∧
        (∀ n, q (b n) ≤ C) ∧ ∀ x, HasSum (fun n ↦ φ n x • b n) x) :
    IsNuclearTVS.{v} E := by
  apply (isNuclearTVS_iff_localBanach_integral E).mpr
  intro U hU bU cU
  have := PolynormableSpace.isTopologicalAddGroup ℂ E
  have : ContinuousSMul ℂ E := PolynormableSpace.continuousSMul ℂ E
  have : ContinuousSMul ℝ E :=
    MulAction.continuousSMul_compHom (f := (algebraMap ℝ ℂ).toMonoidHom) Complex.continuous_ofReal
  let q := gaugeSeminorm bU cU (absorbent_nhds_zero hU)
  obtain ⟨p₀, φ, b, d, C, hp₀, hC, hd, hd₀, hφ, hb, hsum⟩ :=
    h q (continuous_gauge cU hU)
  obtain ⟨r, hr, hrU⟩ := (PolynormableSpace.hasBasis_zero_ball ℂ E).mem_iff.mp hU
  let p := p₀ + r
  have hp : Continuous p := hp₀.add hr
  have hp₀p (x : E) : p₀ x ≤ p x := le_add_of_nonneg_right (apply_nonneg r x)
  let V := p.ball 0 1
  have hV : V ∈ 𝓝 0 := p.ball_mem_nhds hp one_pos
  have bV := p.balanced_ball_zero 1
  have cV := p.convex_ball 0 1
  have hVU : V ⊆ U := fun x hx ↦ hrU <| r.mem_ball_zero.mpr
    ((le_add_of_nonneg_left (apply_nonneg p₀ x)).trans_lt (p.mem_ball_zero.mp hx))
  have hpg : gaugeSeminorm bV cV (absorbent_nhds_zero hV) = p :=
    DFunLike.coe_injective (p.restrictScalars ℝ).gauge_ball
  refine ⟨V, hV, bV, cV, hVU, ?_⟩
  let p' := gaugeSeminorm bV cV (absorbent_nhds_zero hV)
  let T := localBanachMap p' q (gauge_mono (absorbent_nhds_zero hV) hVU)
  have hbound (n : ℕ) (x : E) : ‖φ n x‖ ≤ d n * p' x := by
    rw [show p' = p from hpg]
    exact (hφ n x).trans (mul_le_mul_of_nonneg_left (hp₀p x) (hd₀ n))
  let f (n : ℕ) : WithLocalSeminorm p' →L[ℂ] ℂ :=
    (show WithLocalSeminorm p' →ₗ[ℂ] ℂ from φ n).mkContinuous (d n) (hbound n)
  let φ' (n : ℕ) := (f n).fromCompletion
  let b' (n : ℕ) : LocalBanach q := (show WithLocalSeminorm q from b n)
  have hφ' (n : ℕ) : ‖φ' n‖ ≤ d n := by
    apply ContinuousLinearMap.opNorm_le_bound _ (hd₀ n)
    intro x
    induction x using Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      rw [show φ' n (x : LocalBanach p') = f n x from (f n).fromCompletion_apply_coe x,
        Completion.norm_coe]
      exact hbound n x
  have hb' (n : ℕ) : ‖b' n‖ ≤ C := (localBanach_norm_coe q (b n)).trans_le (hb n)
  have hs : Summable (fun n ↦ ‖φ' n‖ * ‖b' n‖) :=
    (hd.mul_right C).of_nonneg_of_le (fun _ ↦ by positivity)
      (fun n ↦ mul_le_mul (hφ' n) (hb' n) (norm_nonneg _) (hd₀ n))
  apply integral_evaluation_of_rankOne_series T φ' b' hs
  let R (n : ℕ) : LocalBanach p' →L[ℂ] LocalBanach q := (φ' n).smulRight (b' n)
  have hR : Summable R :=
    Summable.of_norm (hs.congr fun n ↦ ((φ' n).norm_smulRight_apply (b' n)).symm)
  let j₀ : E →ₗ[ℂ] LocalBanach q := Completion.toComplL.toLinearMap.comp LinearMap.id
  have hj₀ (x : E) : ‖j₀ x‖ = q x := localBanach_norm_coe q x
  let j : E →L[ℂ] LocalBanach q := ⟨j₀, by
    apply (PolynormableSpace.withSeminorms ℂ E).continuous_normedSpace_rng (LocalBanach q) j₀
    refine ⟨{⟨q, continuous_gauge cU hU⟩}, 1, ?_⟩
    simpa using (show (normSeminorm ℂ _).comp j₀ ≤ q from fun x ↦ (hj₀ x).le)⟩
  -- On the dense image of E, the operator series is the original expansion.
  have hRT : (∑' n, R n) = T := by
    ext x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
      have hsum' := (hsum x).mapL j
      have hsumR := hR.hasSum.mapL
        (ContinuousLinearMap.apply ℂ (LocalBanach q) (x : LocalBanach p'))
      apply hsumR.unique
      convert hsum' using 1
      · ext n
        change φ' n (x : LocalBanach p') • b' n = j (φ n x • b n)
        rw [(f n).fromCompletion_apply_coe, map_smul]
        rfl
      · exact localBanachMap_coe p' q _ x
  intro x
  simpa only [hRT, ContinuousLinearMap.apply_apply, R, ContinuousLinearMap.smulRight_apply] using
    hR.hasSum.mapL (ContinuousLinearMap.apply ℂ (LocalBanach q) x)


/-- A series of Euclidean Schwartz functions is summable if it is absolutely
summable in every defining seminorm. -/
private theorem euclideanSchwartz_summable_of_seminorm {m : ℕ}
    {f : ℕ → SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ}
    (h : ∀ k l, Summable (fun n ↦ SchwartzMap.seminorm ℂ k l (f n))) : Summable f := by
  let E := SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ
  have : CompleteSpace E := completeSpace_schwartzMap
  apply summable_iff_cauchySeq_finset.mpr
  rw [CauchySeq, cauchy_map_iff', uniformity_eq_comap_nhds_zero, tendsto_comap_iff,
    (schwartz_withSeminorms ℂ _ _).tendsto_nhds]
  rintro ⟨k, l⟩ ε hε
  let p : Seminorm ℂ E := SchwartzMap.seminorm ℂ k l
  let j : E →ₗ[ℂ] LocalBanach p := Completion.toComplL.toLinearMap.comp LinearMap.id
  have hj (x : E) : ‖j x‖ = p x := localBanach_norm_coe p x
  have hs : Summable (fun n ↦ j (f n)) := Summable.of_norm (by simpa only [hj] using h k l)
  have ht := cauchy_map_iff'.mp (summable_iff_cauchySeq_finset.mp hs)
  rw [tendsto_uniformity_iff_dist_tendsto_zero, Metric.tendsto_nhds] at ht
  filter_upwards [ht ε hε] with s hs'
  rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg] at hs'
  rw [dist_eq_norm', ← map_sum, ← map_sum, ← map_sub, hj] at hs'
  simpa only [sub_zero, Function.comp_apply, schwartzSeminormFamily, p] using hs'

/-- In positive dimension, the Hermite functions form a Hilbert basis of complex
L² consisting of Schwartz functions. Enumerating the multi-indices in order
of total degree gives an indexing by ℕ with polynomial growth of the basis
seminorms and rapid decay of the coefficients. For each decay order the bound
is uniform on the unit ball of a suitable continuous Schwartz seminorm. -/
private theorem euclideanSchwartz_hermite_estimates (m : ℕ) (hm : 0 < m) :
    let D := EuclideanSpace ℝ (Fin m)
    let E := SchwartzMap D ℂ
    let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure D)
    ∃ (b : ℕ → E) (B : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure D))),
      (∀ n, J (b n) = B n) ∧
      (∀ q : Seminorm ℂ E, Continuous q → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧
        ∀ n : ℕ, q (b n) ≤ C * ((n : ℝ) + 1) ^ k) ∧
      ∀ k : ℕ, ∃ p : Seminorm ℂ E, Continuous p ∧
        ∀ (n : ℕ) (f : E), ‖B.repr (J f) n‖ * ((n : ℝ) + 1) ^ k ≤ p f := by
  sorry

/-- Paper: Proposition 2.1.1.6, p. 61. The Euclidean Schwartz space is nuclear. -/
theorem euclideanSchwartz_nuclear (m : ℕ) :
    IsNuclearTVS.{v} (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) := by
  let D := EuclideanSpace ℝ (Fin m)
  let E := SchwartzMap D ℂ
  let : PolynormableSpace ℂ E := (schwartz_withSeminorms ℂ _ _).toPolynormableSpace
  by_cases hm : m = 0
  · subst m
    let eval : E →ₗ[ℂ] ℂ :=
      { toFun := fun f ↦ f 0
        map_add' := by intros; rfl
        map_smul' := by intros; rfl }
    have heval : Injective eval := by
      intro f g h
      ext x
      exact (Subsingleton.elim (0 : D) x) ▸ h
    let : FiniteDimensional ℂ E := FiniteDimensional.of_injective eval heval
    exact isNuclearTVS_of_finiteDimensional E
  let J := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure D)
  obtain ⟨b, B, hb, hgrowth, hdecay⟩ := euclideanSchwartz_hermite_estimates m (Nat.pos_of_ne_zero hm)
  change ∀ n, J (b n) = B n at hb
  let φ (n : ℕ) : E →ₗ[ℂ] ℂ := ((innerSL ℂ (B n)).comp J).toLinearMap
  have hcoeff (n : ℕ) (f : E) : φ n f = B.repr (J f) n := (B.repr_apply_apply _ _).symm
  let d (n : ℕ) : ℝ := (((n : ℝ) + 1) ^ 2)⁻¹
  have hd : Summable d := by
    simpa only [d, Function.comp_def, Nat.cast_succ] using
      (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).comp_injective Nat.succ_injective
  have hd₀ (n : ℕ) : 0 ≤ d n := by positivity
  -- Rescale the two factors without changing their product to bound the vectors
  -- uniformly in the chosen seminorm and the coefficients by a summable sequence.
  have hscale (q : Seminorm ℂ E) (hq : Continuous q) :
      ∃ (p : Seminorm ℂ E) (ψ : ℕ → E →ₗ[ℂ] ℂ) (c : ℕ → E) (C : ℝ),
        Continuous p ∧ 0 ≤ C ∧ (∀ n f, ‖ψ n f‖ ≤ d n * p f) ∧
          (∀ n, q (c n) ≤ C) ∧ ∀ n f, ψ n f • c n = φ n f • b n := by
    obtain ⟨C, k, hC, hq'⟩ := hgrowth q hq
    obtain ⟨p, hp, hp'⟩ := hdecay (k + 2)
    let w (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ k
    have hw (n : ℕ) : 0 < w n := by positivity
    refine ⟨p, fun n ↦ (w n : ℂ) • φ n, fun n ↦ (w n : ℂ)⁻¹ • b n, C, hp, hC, ?_, ?_, ?_⟩
    · intro n f
      rw [LinearMap.smul_apply, norm_smul, Complex.norm_of_nonneg (hw n).le, hcoeff]
      have hh := hp' n f
      rw [pow_add] at hh
      change ‖B.repr (J f) n‖ * (w n * ((n : ℝ) + 1) ^ 2) ≤ p f at hh
      rw [← mul_assoc, mul_comm ‖B.repr (J f) n‖] at hh
      exact (le_inv_mul_iff₀ (by positivity : 0 < ((n : ℝ) + 1) ^ 2)).mpr (by
        rw [mul_comm]
        exact hh)
    · intro n
      rw [map_smul_eq_mul, norm_inv, Complex.norm_of_nonneg (hw n).le]
      exact (inv_mul_le_iff₀ (hw n)).mpr (by rw [mul_comm]; exact hq' n)
    · intro n f
      have hw' : (w n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hw n).ne'
      rw [LinearMap.smul_apply, smul_eq_mul, smul_smul, mul_right_comm,
        mul_inv_cancel₀ hw', one_mul]
  have hsum (f : E) : HasSum (fun n ↦ φ n f • b n) f := by
    have hs : Summable (fun n ↦ φ n f • b n) := by
      apply euclideanSchwartz_summable_of_seminorm
      intro k l
      let q : Seminorm ℂ E := SchwartzMap.seminorm ℂ k l
      obtain ⟨p, ψ, c, C, -, hC, hψ, hc, heq⟩ := hscale q
        ((schwartz_withSeminorms ℂ _ _).continuous_seminorm (k, l))
      apply ((hd.mul_right (p f)).mul_right C).of_nonneg_of_le (fun _ ↦ apply_nonneg _ _)
      intro n
      change q (φ n f • b n) ≤ (d n * p f) * C
      rw [← heq, map_smul_eq_mul]
      exact mul_le_mul (hψ n f) (hc n) (apply_nonneg _ _) (by positivity)
    -- Identify the Schwartz limit using the same sum in L².
    have hJ : Injective J := by
      intro f₁ f₂ he
      apply SchwartzMap.ext
      have h₁ := f₁.coeFn_toLp 2 (volume : Measure D)
      have h₂ := f₂.coeFn_toLp 2 (volume : Measure D)
      change f₁.toLp 2 (volume : Measure D) = f₂.toLp 2 (volume : Measure D) at he
      rw [he] at h₁
      exact congrFun ((f₁.continuous.ae_eq_iff_eq _ f₂.continuous).mp (h₁.symm.trans h₂))
    have hL2 := B.hasSum_repr (J f)
    have hsumJ := hs.hasSum.mapL J
    have h' : J (∑' n, φ n f • b n) = J f := by
      apply hsumJ.unique
      simpa only [map_smul, hcoeff, hb] using hL2
    simpa only [hJ h'] using hs.hasSum
  apply nuclear_of_rankOne_series
  intro q hq
  obtain ⟨p, ψ, c, C, hp, hC, hψ, hc, heq⟩ := hscale q hq
  exact ⟨p, ψ, c, d, C, hp, hC, hd, hd₀, hψ, hc, fun f ↦ by simpa only [heq] using hsum f⟩

end Nuclearity

/-- Paper: Proposition 2.1.1.6, p. 61. The Euclidean Schwartz space is Fréchet. -/
theorem euclideanSchwartz_frechet (m : ℕ) :
    IsFrechetTVS (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) := by
  let E := SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ
  have : (uniformity E).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero E]
    infer_instance
  refine ⟨inferInstance, (schwartz_withSeminorms ℂ _ _).toPolynormableSpace,
    UniformSpace.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq]
  exact completeSpace_schwartzMap

section Reflexivity

open Metric LineDeriv
open scoped SchwartzMap BoundedContinuousFunction OnePoint

/-- Each mixed partial with its coordinate weight is dominated pointwise by an
ordinary Schwartz function, depending continuously and linearly on the input. -/
private theorem exists_schwartz_weighted_partial_clm {m : ℕ} (α β : Fin m → ℕ) :
    let E := SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ
    ∃ T : E →L[ℂ] E, ∀ (f : E) x, euclideanSchwartzWeightedDeriv α β f x ≤ ‖T f x‖ := by
  let D := EuclideanSpace ℝ (Fin m)
  let w (x : D) := ∏ i, x i ^ α i
  have hw (s : Finset (Fin m)) : (fun x : D ↦ ∏ i ∈ s, x i ^ α i).HasTemperateGrowth := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (((EuclideanSpace.proj (𝕜 := ℝ) i).hasTemperateGrowth.pow (α i)).mul ih)
  -- Replace the nonsmooth absolute weight by a polynomial majorant.
  have hW : (fun x : D ↦ ((2 + w x ^ 2 : ℝ) : ℂ)).HasTemperateGrowth := by
    have : w.HasTemperateGrowth := hw Finset.univ
    fun_prop
  let dirs := (List.finRange m).flatMap fun i ↦ List.replicate (β i) i
  let v (j : Fin dirs.length) := EuclideanSpace.single (dirs.get j) (1 : ℝ)
  let T := (SchwartzMap.smulLeftCLM ℂ (fun x : D ↦ ((2 + w x ^ 2 : ℝ) : ℂ))).comp
    (iteratedLineDerivOpCLM ℂ (SchwartzMap D ℂ) v)
  refine ⟨T, fun f x ↦ ?_⟩
  change (1 + |w x|) * _ ≤ ‖SchwartzMap.smulLeftCLM ℂ _ _ x‖
  rw [SchwartzMap.smulLeftCLM_apply_apply hW, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 2 + w x ^ 2)]
  change (1 + |w x|) * ‖iteratedFDeriv ℝ _ f x v‖ ≤ (2 + w x ^ 2) * ‖∂^{v} f x‖
  rw [SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  nlinarith [sq_nonneg (|w x| - 1), sq_abs (w x)]

/-- Bounded closed sets in the Euclidean Schwartz space are compact: all weighted
mixed partials are relatively compact in the uniform norm by Arzelà–Ascoli. -/
private theorem montel_euclideanSchwartz (m : ℕ) :
    MontelSpace ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) := by
  let D := EuclideanSpace ℝ (Fin m)
  let E := SchwartzMap D ℂ
  obtain ⟨J, hJ, hcomp⟩ := schwartz_compactified_bounded D
  choose T hT using @exists_schwartz_weighted_partial_clm m
  let I := (Fin m → ℕ) × (Fin m → ℕ)
  -- The uniform norms of these coordinates recover every defining seminorm.
  let c : E →L[ℂ] (I → OnePoint D →ᵇ ℂ) := ContinuousLinearMap.pi fun i ↦ J.comp (T i.1 i.2)
  have hi : IsUniformInducing c := by
    apply AddMonoidHom.isUniformInducing_of_isInducing (f := c.toLinearMap.toAddMonoidHom)
    apply Topology.isInducing_iff_nhds.mpr
    intro f
    refine le_antisymm (c.continuous.tendsto f).le_comap ?_
    apply tendsto_id'.mp
    apply (schwartzMap_euclidean_tendsto_iff _ _ _).mpr
    intro α β ε hε
    have hc := (tendsto_pi_nhds.mp (tendsto_comap (f := c) (x := 𝓝 (c f)))) (α, β)
    filter_upwards [(Metric.tendsto_nhds.mp hc ε hε)] with g hg x
    have hx := hT α β (g - f) x
    rw [← hJ] at hx
    apply hx.trans_lt
    refine ((J (T α β (g - f))).norm_coe_le_norm x).trans_lt ?_
    change dist (J (T α β g)) (J (T α β f)) < ε at hg
    simpa only [map_sub, dist_eq_norm] using hg
  have : CompleteSpace E := completeSpace_schwartzMap
  constructor
  intro S hclosed hS
  apply TotallyBounded.isCompact_of_isClosed _ hclosed
  apply (totallyBounded_image_iff hi).mp
  let K (i : I) := closure (J '' ((T i.1 i.2) '' S))
  have hK (i : I) : IsCompact (K i) := hcomp _ (hS.image (T i.1 i.2))
  apply (isCompact_univ_pi hK).totallyBounded.subset
  rintro _ ⟨f, hf, rfl⟩ i _
  exact subset_closure (mem_image_of_mem _ (mem_image_of_mem _ hf))

open scoped ComplexOrder in
/-- A strong-bidual functional belongs to the bipolar of evaluations on a compact
disk of Schwartz functions. This disk already has weakly closed evaluation image. -/
private theorem euclideanSchwartz_eval_surjective (m : ℕ) :
    let E := SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ
    Surjective (ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)) := by
  let E := SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ
  let D := StrongDual ℂ E
  have : PolynormableSpace ℂ E := (schwartz_withSeminorms ℂ _ _).toPolynormableSpace
  have : MontelSpace ℂ E := montel_euclideanSchwartz m
  change Surjective (ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ))
  intro b
  have hU : b ⁻¹' closedBall 0 1 ∈ 𝓝 (0 : D) :=
    b.continuous.continuousAt.preimage_mem_nhds (by rw [map_zero]; exact closedBall_mem_nhds _ zero_lt_one)
  obtain ⟨⟨S, r⟩, ⟨hS, hr⟩, htest⟩ :=
    (ContinuousLinearMap.hasBasis_nhds_zero_of_basis Metric.nhds_basis_closedBall).mem_iff.mp hU
  let scale : E →L[ℂ] E := (r : ℂ)⁻¹ • ContinuousLinearMap.id ℂ E
  obtain ⟨K, hK, habs, hsub⟩ := exists_compact_absConvex_superset (hS.image scale)
  let B : Module.Dual ℂ D →ₗ[ℂ] D →ₗ[ℂ] ℂ := .id
  let j : E →ₗ[ℂ] WeakBilin B := (topDualPairing ℂ E).flip
  let A : Set (WeakBilin B) := j '' K
  have hB : B.Nondegenerate := LinearMap.Nondegenerate.id
  have hT : T2Space (WeakBilin B) := (WeakBilin.isEmbedding (B := B) injective_id).t2Space
  have hclosed : IsClosed A := (hK.image
    (WeakBilin.continuous_of_continuous_eval B fun φ ↦ φ.continuous : Continuous j)).isClosed
  have hpolar : b.toLinearMap ∈ B.flip.polar (B.polar A) := by
    intro φ hφ
    apply mem_closedBall_zero_iff.mp (htest (a := φ) ?_)
    intro x hx
    have h := hφ _ (mem_image_of_mem j (hsub (mem_insert_of_mem _ (mem_image_of_mem scale hx))))
    change ‖φ ((r : ℂ)⁻¹ • x)‖ ≤ 1 at h
    rw [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      inv_mul_le_iff₀ hr, mul_one] at h
    exact mem_closedBall_zero_iff.mpr h
  -- Apply the bipolar theorem in the algebraic dual paired with D.
  have hbip : B.flip.polar (B.polar A) ⊆ A := by
    let : TopologicalSpace (Module.Dual ℂ D) := inferInstanceAs (TopologicalSpace (WeakBilin B))
    let : TopologicalSpace D := inferInstanceAs (TopologicalSpace (WeakBilin B.flip))
    have : PolynormableSpace ℂ (Module.Dual ℂ D) := B.weakBilin_withSeminorms.toPolynormableSpace
    have : PolynormableSpace ℂ D := B.flip.weakBilin_withSeminorms.toPolynormableSpace
    have : T2Space (Module.Dual ℂ D) := hT
    have : T2Space D := (WeakBilin.isEmbedding (LinearMap.ker_eq_bot.mp
      (LinearMap.separatingLeft_iff_ker_eq_bot.mp (LinearMap.flip_separatingLeft.mpr hB.2)))).t2Space
    rw [bipolar_eq_weakClosure_absConvexHull B hB A]
    apply closure_minimal _ hclosed
    apply absConvexHull_min _ ⟨habs.1.image j, habs.2.linear_image j⟩
    exact insert_subset (⟨0, hsub (mem_insert _ _), map_zero j⟩ : (0 : WeakBilin B) ∈ A) Subset.rfl
  obtain ⟨x, _, hx⟩ := hbip hpolar
  exact ⟨x, ContinuousLinearMap.ext (LinearMap.congr_fun hx)⟩

end Reflexivity

/-- Paper: Proposition 2.1.1.6, p. 61. Evaluation identifies the Euclidean Schwartz space
with its strong bidual. -/
theorem euclideanSchwartz_reflexive (m : ℕ) :
    let E := SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ
    ∃ e : E ≃L[ℂ] StrongDual ℂ (StrongDual ℂ E), ∀ f L, e f L = L f := by
  let E := SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ
  have : PolynormableSpace ℂ E := (schwartz_withSeminorms ℂ _ _).toPolynormableSpace
  have : BarrelledSpace ℂ E := isFrechetTVS_barrelled (euclideanSchwartz_frechet m)
  let j := ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ)
  have he : IsEmbedding j := isEmbedding_strongBidual_eval
  have hh := isHomeomorph_iff_isEmbedding_surjective.mpr ⟨he, euclideanSchwartz_eval_surjective m⟩
  exact ⟨.ofIsHomeomorph (.ofBijective j hh.bijective) hh, fun _ _ ↦ rfl⟩

/-- Paper: Proposition 2.1.1.6, p. 61. The strong dual of the Euclidean Schwartz space
is complete. -/
theorem euclideanSchwartz_strongDual_complete (m : ℕ) :
    CompleteSpace (StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)) := by
  infer_instance

/-- Paper: Proposition 2.1.1.6, p. 61. The strong dual of the Euclidean Schwartz space
is nuclear. -/
theorem euclideanSchwartz_strongDual_nuclear (m : ℕ) :
    IsNuclearTVS.{v} (StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)) := by
  exact (isNuclearTVS_strongDual_iff (euclideanSchwartz_frechet m)).2
    (euclideanSchwartz_nuclear m)

section StrongDualMontel

open Bornology Metric Set Topology Filter
open scoped Pointwise ComplexOrder

/-- Paper: Proposition 2.1.1.6, p. 61 (first half). By Banach-Steinhaus, every strongly bounded
family of continuous linear functionals on a polynormable space is dominated by a fixed continuous
seminorm. -/
theorem strongDual_bounded_in_polar {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] [BarrelledSpace ℂ E] {S : Set (StrongDual ℂ E)}
    (hS : IsVonNBounded ℂ S) :
    ∃ p : Seminorm ℂ E, Continuous p ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ ∈ S, ∀ x, ‖φ x‖ ≤ C * p x := by
  classical
  let 𝓕 : S → (E →SL[RingHom.id ℂ] ℂ) := fun φ ↦ φ.1
  have hb : ∀ x, IsVonNBounded ℂ (range fun φ : S ↦ 𝓕 φ x) := fun x ↦
    IsVonNBounded.subset (fun y hy ↦ by
      obtain ⟨φ, rfl⟩ := Set.mem_range.mp hy
      exact ⟨φ, φ.2, by simp [𝓕]⟩)
      (hS.image (ContinuousLinearMap.applyₗ (E := E) ℂ (RingHom.id ℂ) x))
  have hEqui : UniformEquicontinuous ((↑) ∘ (fun φ : S ↦ (𝓕 φ : E →ₗ[ℂ] ℂ))) :=
    PolynormableSpace.banach_steinhaus (𝓕 := 𝓕) hb
  -- Convert uniform equicontinuity into a seminorm bound via the defining seminorm family.
  have hsm :=
    ((norm_withSeminorms ℂ ℂ).uniformEquicontinuous_iff_exists_continuous_seminorm
      (fun φ : S ↦ (𝓕 φ : E →ₗ[ℂ] ℂ))).mp hEqui
  obtain ⟨p, hp, hle⟩ := hsm ()
  refine ⟨p, hp, 1, zero_le_one, fun φ hφ x ↦ ?_⟩
  simpa using hle ⟨φ, hφ⟩ x

section DualMontelHelpers

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E]
  [IsUniformAddGroup E] [ContinuousSMul ℂ E] [PolynormableSpace ℂ E] [T2Space E]

open ContinuousLinearMap
open scoped NNReal

private structure DualBoundData (q : Seminorm ℂ E) (r : ℝ) (s : Set E) (n : ℕ) where
  prev : StrongDual ℂ E
  φ : StrongDual ℂ E
  x : E
  ψ : StrongDual ℂ E
  M : ℝ
  hx : x ∈ s
  hdom : ∀ y, ‖φ y‖ ≤ q y
  hat : φ x = (q x : ℂ)
  hM : 0 ≤ M
  hprev : ∀ z ∈ s, ‖prev z‖ ≤ M
  hbig : 2 * (3 : ℝ) ^ n * (M + (n : ℝ) + 1) < q x
  hψ : ψ = prev + (r ^ n : ℂ) • φ

private theorem isVonNBounded_of_dual_pointwise_bounded {s : Set E}
    (hs : ∀ φ : StrongDual ℂ E, ∃ C : ℝ, ∀ x ∈ s, ‖φ x‖ ≤ C) :
    IsVonNBounded ℂ s := by
  classical
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  apply (PolynormableSpace.withSeminorms ℂ E).isVonNBounded_iff_seminorm_bddAbove.mpr
  intro q
  by_contra hnb
  have hunb : ∀ a : ℝ, ∃ x ∈ s, a < q.1 x := by
    simpa [not_bddAbove_iff, forall_mem_image] using hnb
  let r : ℝ := 1 / 3
  have hr0 : 0 ≤ r := by norm_num
  have hr1 : r < 1 := by norm_num
  have hrpos : 0 < r := by norm_num
  have hgeom : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have htsum : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  have htsum_val : ∑' n : ℕ, r ^ n = 3 / 2 := by
    rw [htsum]; simp only [r]; norm_num
  let build (n : ℕ) (prev : StrongDual ℂ E) : DualBoundData q.1 r s n :=
    let C := Classical.choose (hs prev)
    let hC := Classical.choose_spec (hs prev)
    let M : ℝ := max C 0
    let target := 2 * (3 : ℝ) ^ n * (M + (n : ℝ) + 1)
    let x := Classical.choose (hunb target)
    let hx := Classical.choose_spec (hunb target)
    let φ0 := Classical.choose (RiemannMasullo.exists_dual_norm_eq_seminorm q.1 q.2 x)
    let hφ0 := Classical.choose_spec (RiemannMasullo.exists_dual_norm_eq_seminorm q.1 q.2 x)
    let c := Classical.choose (RCLike.exists_norm_eq_mul_self (φ0 x))
    let hc := Classical.choose_spec (RCLike.exists_norm_eq_mul_self (φ0 x))
    let φ : StrongDual ℂ E := c • φ0
    let hdom : ∀ y, ‖φ y‖ ≤ q.1 y := fun y => by
      have h : ‖(c • φ0) y‖ = ‖φ0 y‖ := by
        rw [smul_apply, smul_eq_mul, norm_mul, hc.1, one_mul]
      rw [h]
      exact hφ0.1 y
    let hat : φ x = (q.1 x : ℂ) := by
      rw [smul_apply, smul_eq_mul, ← hc.2]
      exact congrArg Complex.ofReal hφ0.2
    let hprev : ∀ z ∈ s, ‖prev z‖ ≤ M := fun z hz => (hC z hz).trans (le_max_left _ _)
    ⟨prev, φ, x, prev + (r ^ n : ℂ) • φ, M, hx.1, hdom, hat, le_max_right _ _, hprev, hx.2, rfl⟩
  let seq : (n : ℕ) → DualBoundData q.1 r s n :=
    Nat.rec (motive := fun n => DualBoundData q.1 r s n) (build 0 0)
      (fun n d => build (n + 1) d.ψ)
  have hseq0 : (seq 0).prev = 0 := by
    change (build 0 0).prev = 0
    rfl
  have hsucc (n : ℕ) : (seq (n + 1)).prev = (seq n).ψ := by
    change (build (n + 1) (seq n).ψ).prev = (seq n).ψ
    rfl
  have hpartial (n : ℕ) (x : E) :
      (seq n).ψ x = ∑ k ∈ Finset.range (n + 1), (r ^ k : ℂ) * (seq k).φ x := by
    induction n with
    | zero =>
        rw [(seq 0).hψ, hseq0, zero_add, smul_apply, pow_zero, one_smul]
        simp [Finset.range_one]
    | succ n ih =>
        rw [(seq (n + 1)).hψ, hsucc n, add_apply, ih, smul_apply, smul_eq_mul]
        conv_rhs => rw [Finset.sum_range_succ]
  let term (x : E) (n : ℕ) : ℂ := (r : ℂ) ^ n * (seq n).φ x
  have hterm_norm (x : E) (n : ℕ) : ‖term x n‖ ≤ r ^ n * q.1 x := by
    unfold term
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
    exact mul_le_mul_of_nonneg_left ((seq n).hdom x) (pow_nonneg hr0 n)
  have hterm_sum (x : E) : Summable (term x) :=
    Summable.of_norm_bounded (hgeom.mul_right (q.1 x)) (hterm_norm x)
  let f (x : E) : ℂ := ∑' n, term x n
  have hsplit (n : ℕ) (x : E) :
      f x = (seq n).ψ x + ∑' k, term x (k + (n + 1)) := by
    have h := (hterm_sum x).sum_add_tsum_nat_add (n + 1)
    unfold f
    rw [← h, hpartial]
  have htail_coeff (n : ℕ) : ∑' k : ℕ, r ^ (k + (n + 1)) = r ^ n / 2 := by
    have hshift : ∑' k : ℕ, r ^ (k + (n + 1)) = r ^ (n + 1) * ∑' k : ℕ, r ^ k := by
      rw [eq_comm, ← tsum_mul_left]
      congr
      ext k
      simp [pow_add, mul_comm]
    rw [hshift, htsum_val, pow_succ]
    simp only [r]
    ring
  have htail_summable (n : ℕ) (x : E) : Summable fun k => term x (k + (n + 1)) :=
    ((summable_nat_add_iff (n + 1)).2 (hterm_sum x))
  have htail (n : ℕ) :
      ‖∑' k, term (seq n).x (k + (n + 1))‖ ≤ (r ^ n / 2) * q.1 (seq n).x := by
    have hle : ∀ k, ‖term (seq n).x (k + (n + 1))‖ ≤ r ^ (k + (n + 1)) * q.1 (seq n).x :=
      fun k => hterm_norm _ _
    have hsum : Summable fun k => r ^ (k + (n + 1)) * q.1 (seq n).x :=
      ((summable_nat_add_iff (n + 1)).2 hgeom).mul_right _
    have hn : Summable fun k => ‖term (seq n).x (k + (n + 1))‖ :=
      Summable.of_norm_bounded hsum fun k => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
        exact hle k
    refine (norm_tsum_le_tsum_norm hn).trans ?_
    refine (hn.tsum_le_tsum hle hsum).trans ?_
    rw [tsum_mul_right, htail_coeff]
  have hgt (n : ℕ) : (n : ℝ) + 1 < ‖f (seq n).x‖ := by
    have hx := (seq n).hx
    have hsplitx := hsplit n (seq n).x
    have hmain : (r : ℂ) ^ n * (seq n).φ (seq n).x = ↑(r ^ n * q.1 (seq n).x) := by
      rw [(seq n).hat, ← Complex.ofReal_pow, ← Complex.ofReal_mul]
    have hmain_norm : ‖(r ^ n : ℂ) * (seq n).φ (seq n).x‖ = r ^ n * q.1 (seq n).x := by
      rw [hmain, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
      exact mul_nonneg (pow_nonneg hr0 n) (apply_nonneg _ _)
    have hprev_norm : ‖(seq n).prev (seq n).x‖ ≤ (seq n).M := (seq n).hprev _ (seq n).hx
    have hdecomp :
        f (seq n).x = (seq n).prev (seq n).x + (r ^ n : ℂ) * (seq n).φ (seq n).x +
          ∑' k, term (seq n).x (k + (n + 1)) := by
      rw [hsplitx, (seq n).hψ, add_apply, smul_apply, smul_eq_mul]
    set a : ℂ := (seq n).prev (seq n).x
    set b : ℂ := (r ^ n : ℂ) * (seq n).φ (seq n).x
    set c : ℂ := ∑' k, term (seq n).x (k + (n + 1))
    have hbc : b = a + b + c - a - c := by ring
    have htri : ‖b‖ ≤ ‖a + b + c‖ + ‖a‖ + ‖c‖ := by
      calc ‖b‖ = ‖a + b + c + (-a) + (-c)‖ := by simpa [sub_eq_add_neg] using congrArg norm hbc
        _ ≤ ‖a + b + c + (-a)‖ + ‖-c‖ := norm_add_le _ _
        _ ≤ ‖a + b + c‖ + ‖-a‖ + ‖-c‖ := by
          gcongr
          exact norm_add_le _ _
        _ = ‖a + b + c‖ + ‖a‖ + ‖c‖ := by simp [norm_neg]
    have hcnorm : ‖c‖ ≤ (r ^ n / 2) * q.1 (seq n).x := by simpa [c] using htail n
    have hbnorm : ‖b‖ = r ^ n * q.1 (seq n).x := by simpa [b] using hmain_norm
    have hanorm : ‖a‖ ≤ (seq n).M := by simpa [a] using hprev_norm
    have hf : f (seq n).x = a + b + c := by simpa [a, b, c] using hdecomp
    have hlow : (r ^ n / 2) * q.1 (seq n).x - (seq n).M ≤ ‖f (seq n).x‖ := by
      have htri' : ‖b‖ ≤ ‖f (seq n).x‖ + ‖a‖ + ‖c‖ := by simpa [hf] using htri
      linarith
    have hcalc : (n : ℝ) + 1 < (r ^ n / 2) * q.1 (seq n).x - (seq n).M := by
      have hpow : r ^ n * (3 : ℝ) ^ n = 1 := by simp [r]
      have hmul : r ^ n / 2 * (2 * (3 : ℝ) ^ n * ((seq n).M + (n : ℝ) + 1)) =
          (seq n).M + (n : ℝ) + 1 := by
        calc r ^ n / 2 * (2 * (3 : ℝ) ^ n * ((seq n).M + (n : ℝ) + 1))
            = (r ^ n * (3 : ℝ) ^ n) * ((seq n).M + (n : ℝ) + 1) := by ring
          _ = (seq n).M + (n : ℝ) + 1 := by rw [hpow, one_mul]
      have hpos : 0 < r ^ n / 2 := by positivity
      have hlt := mul_lt_mul_of_pos_left (seq n).hbig hpos
      rw [hmul] at hlt
      linarith
    linarith [hlow, hcalc]
  let ℓ : E →ₗ[ℂ] ℂ :=
    { toFun := f
      map_add' := fun x y => by
        unfold f term
        simp only [map_add, mul_add]
        change ∑' n, ((r : ℂ) ^ n * (seq n).φ x + (r : ℂ) ^ n * (seq n).φ y) =
          ∑' n, (r : ℂ) ^ n * (seq n).φ x + ∑' n, (r : ℂ) ^ n * (seq n).φ y
        exact (hterm_sum x).tsum_add (hterm_sum y)
      map_smul' := fun a x => by
        change f (a • x) = a * f x
        unfold f
        have hterm : ∀ n, term (a • x) n = a * term x n := fun n => by
          unfold term
          rw [map_smul, smul_eq_mul]
          ring
        simp_rw [hterm]
        rw [tsum_mul_left] }
  have hcont : Continuous ℓ := by
    apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms ℂ ℂ) ℓ
    intro _
    let c : ℝ≥0 := ⟨3 / 2, by norm_num⟩
    refine Seminorm.continuous_of_le (p := (normSeminorm ℂ ℂ).comp ℓ) (q := c • q.1) ?_ ?_
    · have hpt : ∀ x, (c • q.1) x = (c : ℝ) * q.1 x := fun x => by
        rw [smul_apply, NNReal.smul_def, smul_eq_mul]
      exact (q.2.const_mul (c : ℝ)).congr hpt
    · intro x
      have hn : Summable fun n => ‖term x n‖ :=
        Summable.of_norm_bounded (hgeom.mul_right (q.1 x)) fun n => by
          rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
          exact hterm_norm x n
      calc ‖ℓ x‖ = ‖f x‖ := rfl
        _ ≤ ∑' n, ‖term x n‖ := norm_tsum_le_tsum_norm hn
        _ ≤ ∑' n, r ^ n * q.1 x := hn.tsum_le_tsum (hterm_norm x) (hgeom.mul_right _)
        _ = (∑' n, r ^ n) * q.1 x := tsum_mul_right
        _ = (3 / 2) * q.1 x := by rw [htsum_val]
        _ = (c • q.1) x := by rw [smul_apply, NNReal.smul_def, smul_eq_mul]; rfl
  obtain ⟨C, hC⟩ := hs ⟨ℓ, hcont⟩
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hbad := hC (seq n).x (seq n).hx
  have hbig := hgt n
  have hnorm : ‖ℓ (seq n).x‖ = ‖f (seq n).x‖ := rfl
  have hn' : C < (n : ℝ) := by exact_mod_cast hn
  have hleC : ‖f (seq n).x‖ ≤ C := by simpa [hnorm] using hbad
  linarith

private theorem isCompact_weakPolar (p : Seminorm ℂ E) (hp : Continuous p) (C : ℝ) (hC : 0 ≤ C) :
    IsCompact {φ : WeakDual ℂ E | ∀ x, ‖φ x‖ ≤ C * p x} := by
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  let D : Set (E → ℂ) := univ.pi fun x => Metric.closedBall 0 (C * p x)
  let ev : WeakDual ℂ E → E → ℂ := fun φ x => φ x
  have hD : IsCompact D := isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hev : IsEmbedding ev := WeakBilin.isEmbedding ContinuousLinearMap.coe_injective
  rw [hev.isCompact_iff]
  have himage : ev '' {φ : WeakDual ℂ E | ∀ x, ‖φ x‖ ≤ C * p x} =
      D ∩ range ((↑) : (E →ₗ[ℂ] ℂ) → E → ℂ) := by
    ext f
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨fun x _ => mem_closedBall_zero_iff.mpr (hφ x), ⟨(φ : E →ₗ[ℂ] ℂ), rfl⟩⟩
    · rintro ⟨hf, l, rfl⟩
      have hb : ∀ x, ‖l x‖ ≤ C * p x := fun x =>
        mem_closedBall_zero_iff.mp (hf x (mem_univ x))
      have hl : Continuous l := by
        apply WithSeminorms.continuous_of_continuous_comp (norm_withSeminorms ℂ ℂ) l
        intro _
        let c : ℝ≥0 := ⟨C, hC⟩
        have hpt : ∀ x, (c • p) x = C * p x := fun x => by
          rw [smul_apply, NNReal.smul_def, smul_eq_mul]
          congr 1
        have hqc : Continuous (⇑(c • p)) := (hp.const_mul C).congr hpt
        exact Seminorm.continuous_of_le hqc fun x => by rw [hpt]; exact hb x
      exact ⟨(⟨l, hl⟩ : StrongDual ℂ E), hb, rfl⟩
  rw [himage]
  exact hD.inter_right (LinearMap.isClosed_range_coe E ℂ (RingHom.id ℂ))

private theorem strongDual_polar_isCompact_aux [MontelSpace ℂ E]
    (p : Seminorm ℂ E) (hp : Continuous p) (C : ℝ) (hC : 0 ≤ C) :
    IsCompact {φ : StrongDual ℂ E | ∀ x, ‖φ x‖ ≤ C * p x} := by
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  let Kw : Set (WeakDual ℂ E) := {φ | ∀ x, ‖φ x‖ ≤ C * p x}
  have hKw : IsCompact Kw := isCompact_weakPolar p hp C hC
  have hcont : ContinuousOn (fun φ : WeakDual ℂ E => (φ.toStrongDual : StrongDual ℂ E)) Kw := by
    rw [continuousOn_iff_continuous_restrict]
    rw [continuous_iff_continuousAt]
    intro φ₀
    have hbasis := ContinuousLinearMap.hasBasis_nhds_zero_of_basis
      (σ := RingHom.id ℂ) (E := E) (F := ℂ) Metric.nhds_basis_ball
    suffices hdiff : Tendsto (fun ψ : Kw => (ψ.1.toStrongDual - φ₀.1.toStrongDual : StrongDual ℂ E))
        (𝓝 φ₀) (𝓝 0) by
      have hconst : Tendsto (fun _ : Kw => φ₀.1.toStrongDual) (𝓝 φ₀) (𝓝 φ₀.1.toStrongDual) :=
        tendsto_const_nhds
      change Tendsto (fun ψ : Kw => ψ.1.toStrongDual) (𝓝 φ₀) (𝓝 φ₀.1.toStrongDual)
      simpa [zero_add] using hdiff.add hconst
    apply hbasis.tendsto_right_iff.mpr
    rintro ⟨S, ε⟩ ⟨hS, hε⟩
    let V : Set E := {z | C * p z < ε / 3}
    have hV : V ∈ 𝓝 (0 : E) := by
      have hc : Continuous fun z : E => C * p z := hp.const_mul C
      have htend : Tendsto (fun z : E => C * p z) (𝓝 0) (𝓝 (0 : ℝ)) := by
        simpa [map_zero p, mul_zero] using hc.tendsto 0
      have hε3 : 0 < ε / 3 := by positivity
      have hmem : Iio (ε / 3) ∈ Filter.map (fun z : E => C * p z) (𝓝 0) :=
        htend (Iio_mem_nhds hε3)
      rw [Filter.mem_map] at hmem
      rw [show (fun z : E => C * p z) ⁻¹' Iio (ε / 3) = V by
        ext z; simp [V, mem_Iio]] at hmem
      exact hmem
    have hT : IsCompact (closure S) :=
      MontelSpace.isCompact_of_isClosed_of_isVonNBounded ℂ isClosed_closure hS.closure
    obtain ⟨t, -, hcover⟩ := hT.elim_nhds_subcover (fun y => {z | z - y ∈ V}) fun y hy => by
      have hf : Continuous (fun z : E => z - y) := continuous_id.sub continuous_const
      have hpre := hf.tendsto y
      simp only [sub_self] at hpre
      exact hpre hV
    let W : Set (WeakDual ℂ E) := {ψ | ∀ y ∈ t, ‖ψ y - φ₀.1 y‖ < ε / 3}
    have hW : W ∈ 𝓝 (φ₀.1 : WeakDual ℂ E) := by
      rw [show W = ⋂ y ∈ (t : Set E), {ψ : WeakDual ℂ E | ‖ψ y - φ₀.1 y‖ < ε / 3} by
        ext ψ; simp [W]]
      rw [biInter_mem t.finite_toSet]
      intro y hy
      have hε3 : 0 < ε / 3 := by positivity
      have : {ψ : WeakDual ℂ E | ψ y ∈ ball (φ₀.1 y) (ε / 3)} ∈ 𝓝 φ₀.1 :=
        (WeakDual.eval_continuous y).continuousAt.preimage_mem_nhds (ball_mem_nhds _ hε3)
      simpa [Metric.mem_ball, dist_eq_norm] using this
    refine mem_of_superset (continuous_subtype_val.continuousAt.preimage_mem_nhds hW) ?_
    intro ψ hψ
    intro x hx
    have hxT : x ∈ closure S := subset_closure hx
    have hxU : x ∈ ⋃ y ∈ t, {z | z - y ∈ V} := hcover hxT
    simp only [mem_iUnion, mem_setOf] at hxU
    obtain ⟨y, hy, hdiff⟩ := hxU
    have h1 : ‖ψ.1 (x - y)‖ < ε / 3 :=
      lt_of_le_of_lt (ψ.2 (x - y)) hdiff
    have h2 : ‖φ₀.1 (x - y)‖ < ε / 3 :=
      lt_of_le_of_lt (φ₀.2 (x - y)) hdiff
    have h3 : ‖ψ.1 y - φ₀.1 y‖ < ε / 3 := by
      have : ψ.1 ∈ W := hψ
      exact this y hy
    have hsplit : ψ.1 x - φ₀.1 x =
        ψ.1 (x - y) + (ψ.1 y - φ₀.1 y) - φ₀.1 (x - y) := by
      simp [map_sub, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    have hnorm : ‖ψ.1.toStrongDual x - φ₀.1.toStrongDual x‖ < ε := by
      rw [WeakDual.toStrongDual_apply, WeakDual.toStrongDual_apply, hsplit]
      have hneg : ‖-φ₀.1 (x - y)‖ = ‖φ₀.1 (x - y)‖ := norm_neg _
      calc ‖ψ.1 (x - y) + (ψ.1 y - φ₀.1 y) + -φ₀.1 (x - y)‖
          ≤ ‖ψ.1 (x - y) + (ψ.1 y - φ₀.1 y)‖ + ‖-φ₀.1 (x - y)‖ := norm_add_le _ _
        _ = ‖ψ.1 (x - y) + (ψ.1 y - φ₀.1 y)‖ + ‖φ₀.1 (x - y)‖ := by rw [hneg]
        _ ≤ ‖ψ.1 (x - y)‖ + ‖ψ.1 y - φ₀.1 y‖ + ‖φ₀.1 (x - y)‖ := by
            linarith [norm_add_le (ψ.1 (x - y)) (ψ.1 y - φ₀.1 y)]
        _ < ε / 3 + ε / 3 + ε / 3 := by linarith
        _ = ε := by ring
    simpa [mem_ball_zero_iff, sub_apply] using hnorm
  have himage : (fun φ : WeakDual ℂ E => (φ.toStrongDual : StrongDual ℂ E)) '' Kw =
      {φ : StrongDual ℂ E | ∀ x, ‖φ x‖ ≤ C * p x} := by
    ext ψ
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      intro x
      simpa [WeakDual.toStrongDual_apply] using hφ x
    · intro hψ
      refine ⟨ψ.toWeakDual, hψ, ?_⟩
      simp
  rw [← himage]
  exact hKw.image_of_continuousOn hcont

private theorem strongDual_barrel_nbhd_aux
    (hE : ∀ l : StrongDual ℂ (StrongDual ℂ E), ∃ f : E, ∀ φ : StrongDual ℂ E, l φ = φ f)
    (B : Set (StrongDual ℂ E)) (hBclosed : IsClosed B) (hBabs : AbsConvex ℂ B)
    (hBabsorb : ∀ φ : StrongDual ℂ E, ∃ r : ℝ, 0 < r ∧ φ ∈ (algebraMap ℝ ℂ r) • B) :
    B ∈ 𝓝 (0 : StrongDual ℂ E) := by
  let : IsTopologicalAddGroup E := PolynormableSpace.isTopologicalAddGroup ℂ E
  have h0 : (0 : StrongDual ℂ E) ∈ B := by
    obtain ⟨r, hr, hmem⟩ := hBabsorb 0
    rw [mem_smul_set] at hmem
    obtain ⟨ψ, hψ, hψ0⟩ := hmem
    have hr0 : algebraMap ℝ ℂ r ≠ 0 := by simp [hr.ne']
    have : ψ = 0 := by
      let c : ℂ := algebraMap ℝ ℂ r
      have hc : c ≠ 0 := hr0
      calc ψ = c⁻¹ • (c • ψ) := by rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
        _ = c⁻¹ • (0 : StrongDual ℂ E) := by rw [hψ0]
        _ = 0 := by ext x; simp [smul_apply, smul_eq_mul]
    simpa [this] using hψ
  let A : Set E := {x | ∀ φ ∈ B, ‖φ x‖ ≤ 1}
  have hweak : ∀ φ : StrongDual ℂ E, ∃ M : ℝ, ∀ x ∈ A, ‖φ x‖ ≤ M := by
    intro φ
    obtain ⟨r, hr, hmem⟩ := hBabsorb φ
    rw [mem_smul_set] at hmem
    obtain ⟨ψ, hψ, rfl⟩ := hmem
    refine ⟨r, fun x hx => ?_⟩
    rw [smul_apply, smul_eq_mul, norm_mul, norm_algebraMap, norm_one, mul_one, Real.norm_eq_abs,
      abs_of_pos hr]
    simpa using mul_le_mul_of_nonneg_left (hx _ hψ) hr.le
  have hA : IsVonNBounded ℂ A := isVonNBounded_of_dual_pointwise_bounded hweak
  have hpolar_eq : StrongDual.polar ℂ A = B := by
    apply Subset.antisymm
    · intro φ hφ
      by_contra hnot
      have hconv : Convex ℝ B := (convex_RCLike_iff_convex_real).mp hBabs.2
      have : LocallyConvexSpace ℝ (StrongDual ℂ E) := inferInstance
      obtain ⟨l, u, hlu, hlφ⟩ :=
        RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ) hconv hBclosed hnot
      obtain ⟨x, hx⟩ := hE l
      have hu : 0 < u := by simpa [hx, map_zero] using hlu 0 h0
      have hnormψ : ∀ ψ ∈ B, ‖ψ x‖ < u := by
        intro ψ hψ
        obtain ⟨c, hc, hcψ⟩ := RCLike.exists_norm_eq_mul_self (ψ x)
        have hψc : c • ψ ∈ B := (balanced_iff_smul_mem.mp hBabs.1) (by simpa [hc] using le_of_eq hc) hψ
        have hre : RCLike.re ((c • ψ) x) = ‖ψ x‖ := by
          rw [smul_apply, smul_eq_mul, ← hcψ, RCLike.ofReal_re]
        rw [← hre, ← hx]
        exact hlu _ hψc
      have hφbig : u < ‖φ x‖ := by
        have : u < RCLike.re (φ x) := by simpa [hx] using hlφ
        exact this.trans_le (RCLike.re_le_norm _)
      let y : E := (u : ℂ)⁻¹ • x
      have hyA : y ∈ A := by
        intro ψ hψ
        rw [map_smul, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hu, mul_comm]
        exact ((div_lt_one hu).mpr (hnormψ ψ hψ)).le
      have hyφ : ¬ ‖φ y‖ ≤ 1 := by
        rw [map_smul, smul_eq_mul, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hu, mul_comm, ← div_eq_mul_inv]
        exact not_le.mpr ((one_lt_div hu).mpr hφbig)
      exact hyφ (hφ y hyA)
    · intro ψ hψ x hx
      exact hx ψ hψ
  have hnhds : {φ : StrongDual ℂ E | MapsTo φ A (ball (0 : ℂ) 1)} ∈ 𝓝 0 :=
    ContinuousLinearMap.eventually_nhds_zero_mapsTo (σ := RingHom.id ℂ) hA
      (ball_mem_nhds (0 : ℂ) zero_lt_one)
  refine mem_of_superset hnhds ?_
  intro φ hφ
  have : φ ∈ StrongDual.polar ℂ A := fun x hx => (mem_ball_zero_iff.mp (hφ hx)).le
  simpa [hpolar_eq] using this

end DualMontelHelpers

/-- Paper: Proposition 2.1.1.6, p. 61 (first half). In a polynormable Montel space, each fixed
seminorm bound on the strong dual is compact: on such equicontinuous families the strong topology
agrees with the topology of pointwise convergence, and Tychonoff gives compactness. -/

theorem strongDual_polar_isCompact {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] [MontelSpace ℂ E]
    (p : Seminorm ℂ E) (hp : Continuous p) (C : ℝ) (hC : 0 ≤ C) :
    IsCompact {φ : StrongDual ℂ E | ∀ x, ‖φ x‖ ≤ C * p x} :=
  strongDual_polar_isCompact_aux p hp C hC

/-- Paper: Proposition 2.1.1.6, p. 61 (first half). The strong dual of a Montel polynormable
space has the Heine-Borel property: closed bounded sets are compact. -/
theorem strongDual_montel_heineBorel {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E] [MontelSpace ℂ E] [BarrelledSpace ℂ E] :
    MontelSpace ℂ (StrongDual ℂ E) := by
  constructor
  intro S hclosed hS
  obtain ⟨p, hp, C, hC, hbound⟩ := strongDual_bounded_in_polar hS
  have hsub : S ⊆ {φ : StrongDual ℂ E | ∀ x, ‖φ x‖ ≤ C * p x} := fun φ hφ x ↦ hbound φ hφ x
  exact (strongDual_polar_isCompact p hp C hC).of_isClosed_subset hclosed hsub

/-- Paper: Proposition 2.1.1.6, p. 61 (second half). Every barrel in the strong dual is a
neighborhood of zero: its polar in the base space is weakly closed, absolutely convex and
bounded (each functional is bounded on it by definition of the polar), hence its bipolar,
which contains the barrel by Hahn-Banach separation, is the polar of a bounded set. -/
theorem strongDual_barrel_nbhd {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] [ContinuousSMul ℂ E]
    [PolynormableSpace ℂ E] [T2Space E]
    (hE : ∀ l : StrongDual ℂ (StrongDual ℂ E), ∃ f : E, ∀ φ : StrongDual ℂ E, l φ = φ f)
    (B : Set (StrongDual ℂ E)) (hBclosed : IsClosed B) (hBabs : AbsConvex ℂ B)
    (hBabsorb : ∀ φ : StrongDual ℂ E, ∃ r : ℝ, 0 < r ∧ φ ∈ (algebraMap ℝ ℂ r) • B) :
    B ∈ 𝓝 (0 : StrongDual ℂ E) :=
  strongDual_barrel_nbhd_aux hE B hBclosed hBabs hBabsorb

/-- Paper: Proposition 2.1.1.6, p. 61 (second half). If every barrel in a locally convex space
is a neighborhood of zero, the space is barrelled: the unit closed ball of a lower semicontinuous
seminorm is a closed absolutely convex absorbing set. -/
theorem barrelled_of_barrel_nbhd {E : Type*} [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (h : ∀ B : Set E, IsClosed B → AbsConvex ℂ B →
      (∀ x : E, ∃ r : ℝ, 0 < r ∧ x ∈ (algebraMap ℝ ℂ r) • B) → B ∈ 𝓝 (0 : E)) :
    BarrelledSpace ℂ E := by
  constructor
  intro q hq
  refine q.continuous' (r := 1) ?_
  refine h (q.closedBall 0 1) ?_ ?_ ?_
  · rw [q.closedBall_zero_eq]
    exact hq.isClosed_preimage 1
  · exact ⟨q.balanced_closedBall_zero 1, convex_RCLike_iff_convex_real.mpr (q.convex_closedBall 0 1)⟩
  · intro x
    have hpos : (0 : ℝ) < q x + 1 := by positivity
    have hcnorm : ‖algebraMap ℝ ℂ (q x + 1)‖ = q x + 1 := by
      rw [norm_algebraMap, norm_one, mul_one, Real.norm_eq_abs, abs_of_nonneg hpos.le]
    refine ⟨q x + 1, hpos, ?_⟩
    rw [Set.mem_smul_set]
    refine ⟨(algebraMap ℝ ℂ (q x + 1))⁻¹ • x, ?_, ?_⟩
    · rw [Seminorm.mem_closedBall_zero, map_smul_eq_mul, norm_inv, hcnorm]
      exact inv_mul_le_iff₀ hpos |>.mpr (by linarith)
    · have hcne : algebraMap ℝ ℂ (q x + 1) ≠ 0 := by
        intro hzero
        have hnorm : ‖algebraMap ℝ ℂ (q x + 1)‖ = 0 := by rw [hzero]; exact norm_zero
        rw [hcnorm] at hnorm
        exact absurd hnorm (by linarith)
      rw [smul_smul, mul_inv_cancel₀ hcne, one_smul]

end StrongDualMontel


/-- Paper: Proposition 2.1.1.6, p. 61. The strong dual is Montel, meaning it is
barrelled and its closed bounded subsets are compact. -/
theorem euclideanSchwartz_strongDual_montel (m : ℕ) :
    let D := StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)
    BarrelledSpace ℂ D ∧ MontelSpace ℂ D := by
  let E := SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ
  have hpE : PolynormableSpace ℂ E := (schwartz_withSeminorms ℂ _ _).toPolynormableSpace
  have hME : MontelSpace ℂ E := montel_euclideanSchwartz m
  have hBE : BarrelledSpace ℂ E := isFrechetTVS_barrelled (euclideanSchwartz_frechet m)
  have hT2E : T2Space E := inferInstance
  have heval : ∀ l : StrongDual ℂ (StrongDual ℂ E), ∃ f : E, ∀ φ : StrongDual ℂ E, l φ = φ f := by
    obtain ⟨e, he⟩ := euclideanSchwartz_reflexive m
    intro l
    have hl : ∀ φ, l φ = φ (e.symm l) := by
      intro φ
      have hle : l = e (e.symm l) := (ContinuousLinearEquiv.apply_symm_apply e l).symm
      have hh := he (e.symm l) φ
      rw [← hle] at hh
      exact hh
    exact ⟨e.symm l, hl⟩
  exact ⟨barrelled_of_barrel_nbhd (strongDual_barrel_nbhd heval),
    strongDual_montel_heineBorel (E := E)⟩

-- TODO(paper-gap): §2.1.1.3 cites Theorem D.1.5.7 with separability in place of
-- second countability. A separable non-second-countable compact abelian group
-- can have a nonnuclear Schwartz–Bruhat space.

section RealSchwartzBruhat

open scoped ENNReal NNReal

/-- A compact identity neighborhood generates a connected locally compact group. -/
private theorem realBruhat_compactlyGenerated (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [PreconnectedSpace G] :
    IsCompactlyGeneratedGroup G := by
  obtain ⟨K, hc, hK⟩ := exists_compact_mem_nhds (1 : G)
  have hOpen : IsOpen (Subgroup.closure K : Set G) :=
    Subgroup.isOpen_of_mem_nhds _ (mem_of_superset hK Subgroup.subset_closure)
  exact ⟨K, hK, hc, SetLike.coe_injective
    ((OpenSubgroup.isClopen ⟨Subgroup.closure K, hOpen⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)⟩

/-- A real structural pair has full open subgroup and trivial kernel, so its quotient
map identifies it with the real group. -/
private theorem realBruhat_pair_quotient (a : BruhatStructuralPair (Multiplicative ℝ)) :
    ∃ (h : ∀ x : Multiplicative ℝ, x ∈ a.val.1)
      (q : Multiplicative ℝ ≃ₜ* a.quotient),
        ∀ x, q x = QuotientGroup.mk ⟨x, h x⟩ := by
  obtain ⟨d, -⟩ := exists_realPontryaginDualEquiv
  let : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  let : ConnectedSpace (PontryaginDual (Multiplicative ℝ)) :=
    d.surjective.connectedSpace d.continuous
  have ha : a.val.1 = ⊤ := SetLike.coe_injective
    ((OpenSubgroup.isClopen ⟨a.val.1, a.property.1⟩).eq_univ ⟨1, Subgroup.one_mem _⟩)
  let k := OrderDual.ofDual a.val.2
  have hk : k = ⊥ := by
    let U : OpenSubgroup (PontryaginDual (Multiplicative ℝ)) :=
      ⟨lcaAnnihilator k, a.property.2.2.1.2.1⟩
    have hann : lcaAnnihilator k = ⊤ :=
      SetLike.coe_injective (U.isClopen.eq_univ ⟨1, U.one_mem⟩)
    refine le_antisymm (fun x hx ↦ Subgroup.mem_bot.mpr ?_) bot_le
    apply (pontryaginDual_pairing_separates (G := Multiplicative ℝ)).1
    funext χ
    exact ((mem_lcaAnnihilator_iff k χ).mp (hann ▸ Subgroup.mem_top χ) ⟨x, hx⟩).trans
      (map_one χ).symm
  have h (x : Multiplicative ℝ) : x ∈ a.val.1 := ha ▸ Subgroup.mem_top x
  let i : Multiplicative ℝ ≃ₜ* a.val.1 :=
    { toMulEquiv :=
        { toFun := fun x ↦ ⟨x, h x⟩
          invFun := Subtype.val
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_mul' := fun _ _ ↦ rfl }
      continuous_toFun := continuous_id.subtype_mk _
      continuous_invFun := continuous_subtype_val }
  let p := (QuotientGroup.mk' (k.comap a.val.1.subtype)).comp i.toMulEquiv.toMonoidHom
  have hp : IsOpenQuotientMap p :=
    QuotientGroup.isOpenQuotientMap_mk.comp i.toHomeomorph.isOpenQuotientMap
  have hpInj : Injective p := (MonoidHom.ker_eq_bot_iff p).mp (le_antisymm (fun x hx ↦ by
    change (QuotientGroup.mk (i x) : a.quotient) = 1 at hx
    exact hk ▸ (a.quotient_mk_eq_one (i x)).mp hx) bot_le)
  let q := MulEquiv.ofBijective p ⟨hpInj, hp.surjective⟩
  exact ⟨h, q.toContinuousMulEquiv (fun _ ↦ hp.isQuotientMap.isOpen_preimage), fun _ ↦ rfl⟩

/-- The full real group with trivial kernel has a one-dimensional elementary presentation. -/
private theorem realBruhat_stage_exists :
    ∃ a : BruhatStructuralPair (Multiplicative ℝ), Nonempty (ElementaryLCAPresentation a.quotient) := by
  obtain ⟨d, -⟩ := exists_realPontryaginDualEquiv
  let : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  let : ConnectedSpace (PontryaginDual (Multiplicative ℝ)) :=
    d.surjective.connectedSpace d.continuous
  have hAnn : lcaAnnihilator (⊥ : Subgroup (Multiplicative ℝ)) = ⊤ := by
    refine eq_top_iff.mpr fun χ _ ↦ (mem_lcaAnnihilator_iff _ _).mpr fun x ↦ ?_
    rw [Subgroup.mem_bot.mp x.property, map_one]
  have hGood : IsBruhatGoodSubgroup (⊥ : Subgroup (Multiplicative ℝ)) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [Subgroup.coe_bot] using isClosed_singleton
    · rw [hAnn, Subgroup.coe_top]
      exact isOpen_univ
    · rw [hAnn]
      let : ConnectedSpace (⊤ : Subgroup (PontryaginDual (Multiplicative ℝ))) :=
        (Subgroup.topEquiv.symm.surjective.connectedSpace
          (continuous_id.subtype_mk _))
      have hOpen : IsOpen ((⊤ : Subgroup (PontryaginDual (Multiplicative ℝ))) :
          Set (PontryaginDual (Multiplicative ℝ))) := by simp
      let : LocallyCompactSpace (⊤ : Subgroup (PontryaginDual (Multiplicative ℝ))) :=
        hOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
      exact realBruhat_compactlyGenerated _
  have hTop : IsOpen ((⊤ : Subgroup (Multiplicative ℝ)) : Set (Multiplicative ℝ)) := by simp
  let : ConnectedSpace (⊤ : Subgroup (Multiplicative ℝ)) :=
    Subgroup.topEquiv.symm.surjective.connectedSpace (continuous_id.subtype_mk _)
  let : LocallyCompactSpace (⊤ : Subgroup (Multiplicative ℝ)) :=
    hTop.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let a : BruhatStructuralPair (Multiplicative ℝ) := ⟨(⊤, OrderDual.toDual ⊥),
    hTop, realBruhat_compactlyGenerated _, hGood, bot_le⟩
  obtain ⟨_, q, _⟩ := realBruhat_pair_quotient a
  let E := EuclideanSpace ℝ (Fin 1)
  let L : ℝ ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E, finrank_euclideanSpace])
  let B := (Fin 0 → AddCircle (1 : ℝ)) × (Fin 0 → ℤ) × Fin 1
  let : Unique B := uniqueOfSubsingleton 0
  let M : ℝ ≃+ ElementaryLieGroup 1 0 0 (Fin 1) :=
    L.toLinearEquiv.toAddEquiv.trans (AddEquiv.prodUnique (M := E) (N := B)).symm
  let M' : Multiplicative ℝ ≃ₜ* Multiplicative (ElementaryLieGroup 1 0 0 (Fin 1)) :=
    ⟨AddEquiv.toMultiplicative M,
      show Continuous (fun x : ℝ ↦ (L x, (default : B))) from
        L.continuous.prodMk continuous_const,
      show Continuous (fun x : E × B ↦ L.symm x.1) from
        L.symm.continuous.comp continuous_fst⟩
  refine ⟨a, ⟨?_⟩⟩
  exact { realDim := 1, torusDim := 0, latticeRank := 0, finiteFactor := Fin 1, equiv := q.symm.trans M' }

/-- In any elementary presentation of a real structural quotient, the torus and
discrete factors are trivial, and the real coordinate is a continuous real-linear equivalence. -/
private theorem realBruhat_stage_coordinates (a : BruhatStructuralPair (Multiplicative ℝ))
    (e : ElementaryLCAPresentation a.quotient) :
    e.torusDim = 0 ∧ e.latticeRank = 0 ∧ Subsingleton e.finiteFactor ∧
    ∃ (h : ∀ x : Multiplicative ℝ, x ∈ a.val.1)
      (L : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin e.realDim)),
      ∀ x : ℝ, (e.equiv (QuotientGroup.mk ⟨Multiplicative.ofAdd x, h _⟩)).toAdd =
        (L x, 0, 0, 0) := by
  obtain ⟨h, q, hq⟩ := realBruhat_pair_quotient a
  let E := EuclideanSpace ℝ (Fin e.realDim)
  let T := Fin e.torusDim → AddCircle (1 : ℝ)
  let Z := Fin e.latticeRank → ℤ
  let F := e.finiteFactor
  let P := ElementaryLieGroup e.realDim e.torusDim e.latticeRank F
  let w := q.trans e.equiv
  let W : ℝ ≃+ P := MulEquiv.toAdditive w.toMulEquiv
  have hW : Continuous W := w.continuous
  have hWi : Continuous W.symm := w.symm.continuous
  let : ConnectedSpace P := W.surjective.connectedSpace hW
  let : ConnectedSpace Z :=
    (show Surjective (fun p : P ↦ p.2.2.1) from fun z ↦ ⟨(0, 0, z, 0), rfl⟩).connectedSpace
      (continuous_fst.comp (continuous_snd.comp continuous_snd))
  let : ConnectedSpace F :=
    (show Surjective (fun p : P ↦ p.2.2.2) from fun b ↦ ⟨(0, 0, 0, b), rfl⟩).connectedSpace
      (continuous_snd.comp (continuous_snd.comp continuous_snd))
  have hZ : Subsingleton Z := subsingleton_of_preconnected_totallyDisconnected
  have hF : Subsingleton F := subsingleton_of_preconnected_totallyDisconnected
  have hz : e.latticeRank = 0 := by
    by_contra hn
    let i : Fin e.latticeRank := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hi := congrFun (hZ.elim (0 : Z) 1) i
    exact zero_ne_one hi
  let tor : T →+ ℝ :=
    { toFun := fun t ↦ W.symm (0, t, 0, 0)
      map_zero' := by
        let p : P := (0, 0, 0, 0)
        have he : p + p = p :=
          Prod.ext (zero_add _) (Prod.ext (zero_add _) (Prod.ext (zero_add _) (hF.elim _ _)))
        have hzero := W.symm.map_add p p
        rw [he] at hzero
        change W.symm p = 0
        linarith
      map_add' := fun t u ↦ by
        rw [← W.symm.map_add]
        apply congrArg W.symm
        exact Prod.ext (zero_add _).symm
          (Prod.ext rfl (Prod.ext (zero_add _).symm (hF.elim _ _))) }
  have htor : Continuous tor :=
    hWi.comp (continuous_const.prodMk (continuous_id.prodMk continuous_const))
  obtain ⟨C, hC⟩ := (isCompact_univ.image htor).isBounded.exists_norm_le
  have htor0 (t : T) : tor t = 0 := by
    by_contra ht
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖tor t‖)
    have hb := hC (tor (n • t)) (mem_image_of_mem tor (mem_univ (n • t)))
    rw [map_nsmul, nsmul_eq_mul, norm_mul, Real.norm_natCast] at hb
    exact (not_lt_of_ge hb) ((div_lt_iff₀ (norm_pos_iff.mpr ht)).mp hn)
  have hT : Subsingleton T := ⟨fun t u ↦ by
    have hu : tor t = tor u := (htor0 t).trans (htor0 u).symm
    exact congrArg (fun p : P ↦ p.2.1) (W.symm.injective hu)⟩
  have ht : e.torusDim = 0 := by
    by_contra hn
    let i : Fin e.torusDim := ⟨0, Nat.pos_of_ne_zero hn⟩
    have hi := congrFun (hT.elim (fun _ ↦ ((1 / 2 : ℝ) : AddCircle (1 : ℝ))) 0) i
    exact (show (1 / 2 : ℝ) ≠ 0 by norm_num)
      ((AddCircle.coe_eq_zero_iff_of_mem_Ico (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)).mp hi)
  let I : P ≃+ E :=
    { toFun := Prod.fst
      invFun := fun x ↦ (x, 0, 0, 0)
      left_inv := fun p ↦ Prod.ext rfl (Subsingleton.elim _ _)
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  let L := (W.trans I).toRealLinearEquiv (continuous_fst.comp hW)
    (hWi.comp (continuous_id.prodMk continuous_const))
  refine ⟨ht, hz, hF, h, L, fun x ↦ ?_⟩
  rw [← hq]
  exact Prod.ext rfl (Subsingleton.elim _ _)

/-- The sole coordinate of the one-dimensional Euclidean space. -/
private abbrev realBruhatCoordinate : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
  PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)

/-- In dimension one, the elementary weighted bound is the supremum of the
corresponding classical weighted derivative norms. -/
private theorem elementarySchwartz_real_bound {F : Type*} [Nonempty F]
    (f : ℝ → ℂ) (hf : ContDiff ℝ (∞) f) (i : ElementarySchwartzIndex 1 0 0) :
    elementarySchwartzBound (fun p : ElementaryLieGroup 1 0 0 F ↦ f (realBruhatCoordinate p.1)) i =
      ⨆ x : ℝ, ENNReal.ofReal (‖x‖ ^ i.1 0 * ‖iteratedFDeriv ℝ (i.2.1 0) f x‖) := by
  let E := EuclideanSpace ℝ (Fin 1)
  let E₀ := EuclideanSpace ℝ (Fin 0)
  let P : E × E₀ →L[ℝ] ℝ :=
    realBruhatCoordinate.toContinuousLinearMap.comp (ContinuousLinearMap.fst ℝ E E₀)
  let u : E × E₀ := (EuclideanSpace.single 0 1, 0)
  have hu : P u = 1 := by simp [P, u, realBruhatCoordinate]
  let g : ElementaryLieGroup 1 0 0 F → ℂ := fun p ↦ f (realBruhatCoordinate p.1)
  change elementarySchwartzBound g i = _
  have hpartial (xt : E × E₀) (a : Fin 0 → ℤ) (b : F) :
      elementaryPartial g i.2.1 i.2.2.1 xt a b = iteratedDeriv (i.2.1 0) f (P xt) := by
    have hd : ((List.ofFn (fun j : Fin 1 ↦
        List.replicate (i.2.1 j) ((EuclideanSpace.single j 1 : E), (0 : E₀)))).flatten ++
        (List.ofFn (fun j : Fin 0 ↦ List.replicate (i.2.2.1 j)
          ((0 : E), (EuclideanSpace.single j 1 : E₀)))).flatten) =
        List.replicate (i.2.1 0) u := by
      simp [List.ofFn_succ, u]
    have hrep (l : List (E × E₀)) (hl : l = List.replicate (i.2.1 0) u) :
        iteratedFDeriv ℝ l.length (f ∘ P) xt l.get = iteratedDeriv (i.2.1 0) f (P xt) := by
      subst l
      rw [P.iteratedFDeriv_comp_right hf xt (by simp),
        ContinuousMultilinearMap.compContinuousLinearMap_apply,
        iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]
      simp [hu]
    exact hrep _ hd
  simp only [elementarySchwartzBound, hpartial, Finset.univ_eq_empty (α := Fin 0),
    Finset.prod_empty, mul_one, Fin.prod_univ_one, ENNReal.coe_nnreal_eq, coe_nnNorm,
    norm_mul, norm_pow, Complex.norm_real, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hp : Surjective P := fun x ↦ ⟨(realBruhatCoordinate.symm x, 0),
    realBruhatCoordinate.apply_symm_apply x⟩
  simp only [iSup_const]
  exact hp.iSup_comp (fun x : ℝ ↦ ENNReal.ofReal
    (‖x‖ ^ i.1 0 * ‖iteratedFDeriv ℝ (i.2.1 0) f x‖))

/-- The one-dimensional elementary stage with trivial other factors is the classical
Schwartz space, with the same seminorms. -/
private theorem elementarySchwartz_real_equiv (F : Type*) [AddCommGroup F] [Subsingleton F] :
    ∃ e : SchwartzMap ℝ ℂ ≃L[ℂ] ElementarySchwartz 1 0 0 F,
      ∀ (f : SchwartzMap ℝ ℂ) (p : ElementaryLieGroup 1 0 0 F),
        e f p = f (realBruhatCoordinate p.1) := by
  classical
  let P := ElementaryLieGroup 1 0 0 F
  let A : SchwartzMap ℝ ℂ →ₗ[ℂ] ElementarySchwartz 1 0 0 F :=
    { toFun := fun f ↦ ⟨fun p ↦ f (realBruhatCoordinate p.1), by
        refine ⟨fun _ _ ↦ f.smooth'.comp
          (realBruhatCoordinate.toContinuousLinearMap.contDiff.comp contDiff_fst), fun i ↦ ?_⟩
        rw [elementarySchwartz_real_bound (f : ℝ → ℂ) f.smooth']
        refine lt_of_le_of_lt (iSup_le fun x ↦ ENNReal.ofReal_le_ofReal (f.le_seminorm ℂ _ _ x))
          ENNReal.ofReal_lt_top⟩
      map_add' := fun _ _ ↦ Subtype.ext rfl
      map_smul' := fun _ _ ↦ Subtype.ext rfl }
  have hA (f : SchwartzMap ℝ ℂ) (p : P) : A f p = f (realBruhatCoordinate p.1) := rfl
  have hp (p : P) : p = (p.1, 0, 0, 0) :=
    Prod.ext rfl (Subsingleton.elim _ _)
  have hsurj : Surjective A := by
    intro s
    let f : ℝ → ℂ := fun x ↦ s (realBruhatCoordinate.symm x, 0, 0, 0)
    have hs (p : P) : s p = f (realBruhatCoordinate p.1) := by
      dsimp only [f]
      erw [realBruhatCoordinate.symm_apply_apply]
      exact congrArg s (hp p)
    have hf : ContDiff ℝ (∞) f := by
      have hh := s.property.1 (0 : Fin 0 → ℤ) 0
      have hcomp := hh.comp (realBruhatCoordinate.symm.toContinuousLinearMap.contDiff.prodMk
        (contDiff_const (c := (0 : EuclideanSpace ℝ (Fin 0)))))
      convert hcomp using 1
      funext x
      exact congrArg s (Prod.ext rfl (Subsingleton.elim _ _))
    have hb (k n : ℕ) :
        (⨆ x : ℝ, ENNReal.ofReal (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖)) < (⊤ : ℝ≥0∞) := by
      let i : ElementarySchwartzIndex 1 0 0 := (fun _ ↦ k, fun _ ↦ n, 0, 0)
      have heq : s.val = (fun p : P ↦ f (realBruhatCoordinate p.1)) := funext hs
      calc
        _ = elementarySchwartzBound (fun p : P ↦ f (realBruhatCoordinate p.1)) i :=
          (elementarySchwartz_real_bound f hf i).symm
        _ = elementarySchwartzBound s.val i := congrArg (fun g ↦ elementarySchwartzBound g i) heq.symm
        _ < (⊤ : ℝ≥0∞) := s.property.2 i
    let t : SchwartzMap ℝ ℂ := ⟨f, hf, fun k n ↦ by
      let C := (⨆ x : ℝ, ENNReal.ofReal (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖))
      refine ⟨C.toReal, fun x ↦ ?_⟩
      apply (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp
      rw [ENNReal.ofReal_toReal (hb k n).ne]
      exact le_iSup (fun x : ℝ ↦ ENNReal.ofReal (‖x‖ ^ k * ‖iteratedFDeriv ℝ n f x‖)) x⟩
    exact ⟨t, Subtype.ext (funext fun p ↦ (hs p).symm)⟩
  let e := LinearEquiv.ofBijective A ⟨fun f g h ↦ SchwartzMap.ext fun x ↦ by
    have hh := congrArg (fun s : ElementarySchwartz 1 0 0 F ↦
      s (realBruhatCoordinate.symm x, 0, 0, 0)) h
    simpa only [hA, realBruhatCoordinate.apply_symm_apply] using hh, hsurj⟩
  have hseminorm (f : SchwartzMap ℝ ℂ) (i : ElementarySchwartzIndex 1 0 0) :
      elementarySchwartzSeminorm i (e f) = SchwartzMap.seminorm ℂ (i.1 0) (i.2.1 0) f := by
    have heq : (e f).val = (fun p : P ↦ f (realBruhatCoordinate p.1)) := rfl
    change (elementarySchwartzBound (e f).val i).toReal = _
    rw [heq, elementarySchwartz_real_bound (f : ℝ → ℂ) f.smooth', ENNReal.toReal_iSup
      (fun _ ↦ ENNReal.ofReal_ne_top)]
    simp only [ENNReal.toReal_ofReal (mul_nonneg (pow_nonneg (norm_nonneg _) _) (norm_nonneg _))]
    let b (x : ℝ) := ‖x‖ ^ i.1 0 * ‖iteratedFDeriv ℝ (i.2.1 0) f x‖
    have hb : BddAbove (range b) := ⟨_, forall_mem_range.mpr (f.le_seminorm ℂ _ _)⟩
    exact le_antisymm (ciSup_le (f.le_seminorm ℂ _ _))
      (SchwartzMap.seminorm_le_bound ℂ _ _ f
        ((by positivity : 0 ≤ b 0).trans (le_ciSup hb 0)) (le_ciSup hb))
  refine ⟨⟨e, ?_, ?_⟩, hA⟩
  · apply (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp e.toLinearMap
    intro i
    refine ((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm (i.1 0, i.2.1 0)).congr ?_
    intro f
    exact (hseminorm f i).symm
  · apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp e.symm.toLinearMap
    rintro ⟨k, n⟩
    let i : ElementarySchwartzIndex 1 0 0 := (fun _ ↦ k, fun _ ↦ n, 0, 0)
    exact ((withGeneratingSeminorms_spec _ _).continuous_seminorm i).congr fun s ↦ by
      change elementarySchwartzSeminorm i s = SchwartzMap.seminorm ℂ k n (e.symm s)
      rw [← hseminorm (e.symm s) i, e.apply_symm_apply]

set_option maxHeartbeats 800000 in
/-- Every elementary stage of the real group is continuously linearly equivalent
to the classical Schwartz space by pointwise realization. -/
private theorem realBruhat_stage_equiv (a : BruhatStructuralPair (Multiplicative ℝ))
    (e : ElementaryLCAPresentation a.quotient) :
    ∃ J : SchwartzMap ℝ ℂ ≃L[ℂ] SchwartzBruhatStage e,
      ∀ (f : SchwartzMap ℝ ℂ) (x : Multiplicative ℝ),
        schwartzBruhatStageRealization a e (J f) x = f x.toAdd := by
  classical
  obtain ⟨ht, hz, hF, h, L, hL⟩ := realBruhat_stage_coordinates a e
  have hm : e.realDim = 1 := by
    simpa [finrank_euclideanSpace] using L.toLinearEquiv.finrank_eq.symm
  rcases e with @⟨m, n, r, F, group, finite, topology, discrete, equiv⟩
  dsimp only at hm ht hz
  subst m n r
  letI := group
  letI := finite
  letI := topology
  letI := discrete
  obtain ⟨E, hE⟩ := elementarySchwartz_real_equiv F
  let l : ℝ ≃L[ℝ] ℝ := L.trans realBruhatCoordinate
  let P := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ l.symm (F := ℂ)
  let Q := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ l (F := ℂ)
  let J := ContinuousLinearEquiv.equivOfInverse P Q
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (l.symm_apply_apply x))
    (fun f ↦ SchwartzMap.ext fun x ↦ congrArg f (l.apply_symm_apply x))
  refine ⟨J.trans E, fun f x ↦ ?_⟩
  have hreal := schwartzBruhatStageRealization_apply a
    { realDim := 1, torusDim := 0, latticeRank := 0, finiteFactor := F, equiv := equiv } ((J.trans E) f) x
  rw [dite_eq_left (h x)] at hreal
  refine hreal.trans ((congrArg (fun p : ElementaryLieGroup 1 0 0 F ↦ E (P f) p)
    (hL x.toAdd)).trans ?_)
  exact (hE (P f) _).trans (congrArg f (l.symm_apply_apply x.toAdd))

/-- Paper: §2.1.1.3, p. 63. The classical Schwartz space on the real line agrees
with the Schwartz–Bruhat space of the additive real group, including its topology. -/
theorem realSchwartzBruhat_equiv :
    ∃ e : SchwartzMap ℝ ℂ ≃L[ℂ] ℬ(ℝ),
      ∀ (f : SchwartzMap ℝ ℂ) (x : ℝ), e f (Multiplicative.ofAdd x) = f x := by
  classical
  let R : SchwartzMap ℝ ℂ →ₗ[ℂ] (Multiplicative ℝ → ℂ) :=
    { toFun := fun f x ↦ f x.toAdd
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let J (a : BruhatStructuralPair (Multiplicative ℝ)) (e : ElementaryLCAPresentation a.quotient) :=
    Classical.choose (realBruhat_stage_equiv a e)
  have hJ (a : BruhatStructuralPair (Multiplicative ℝ)) (e : ElementaryLCAPresentation a.quotient) :=
    Classical.choose_spec (realBruhat_stage_equiv a e)
  let a₀ := Classical.choose realBruhat_stage_exists
  let e₀ := Classical.choice (Classical.choose_spec realBruhat_stage_exists)
  have hRange (a : BruhatStructuralPair (Multiplicative ℝ))
      (e : ElementaryLCAPresentation a.quotient) :
      (schwartzBruhatStageRealization a e).range = R.range := by
    have hcomp : (schwartzBruhatStageRealization a e).comp (J a e).toLinearEquiv.toLinearMap = R :=
      LinearMap.ext fun f ↦ funext (hJ a e f)
    rw [← hcomp, LinearMap.range_comp, LinearMap.range_eq_top.mpr (J a e).surjective,
      Submodule.map_top]
  have hrange : schwartzBruhatSubmodule (Multiplicative ℝ) = R.range := by
    unfold schwartzBruhatSubmodule
    exact le_antisymm (iSup_le fun a ↦ iSup_le fun e ↦ (hRange a e).le)
      (le_iSup_of_le a₀ (le_iSup_of_le e₀ (hRange a₀ e₀).ge))
  let A : SchwartzMap ℝ ℂ →ₗ[ℂ] ℬ(ℝ) :=
    R.codRestrict (schwartzBruhatSubmodule (Multiplicative ℝ)) fun f ↦
      hrange ▸ LinearMap.mem_range_self R f
  let E := LinearEquiv.ofBijective A
    ⟨fun f g h ↦ SchwartzMap.ext fun x ↦ congrArg (fun s : ℬ(ℝ) ↦ s (Multiplicative.ofAdd x)) h,
      fun s ↦ by
        have hs : s.val ∈ R.range := hrange ▸ s.property
        obtain ⟨f, hf⟩ := hs
        exact ⟨f, Subtype.ext hf⟩⟩
  have hA (a : BruhatStructuralPair (Multiplicative ℝ))
      (e : ElementaryLCAPresentation a.quotient) (f : SchwartzMap ℝ ℂ) :
      (schwartzBruhatStageInclusion a e (J a e f) : ℬ(ℝ)) = E f :=
    Subtype.ext (funext (hJ a e f))
  refine ⟨⟨E, ?_, ?_⟩, fun _ _ ↦ rfl⟩
  · apply (withGeneratingSeminorms_spec _ Subtype.val).continuous_of_continuous_comp A
    rintro ⟨p, hp⟩
    exact ((hp a₀ e₀).comp (J a₀ e₀).continuous).congr (fun f ↦ congrArg p (hA a₀ e₀ f))
  · apply (schwartz_withSeminorms ℂ ℝ ℂ).continuous_of_continuous_comp E.symm.toLinearMap
    intro i
    let p := (schwartzSeminormFamily ℂ ℝ ℂ i).comp E.symm.toLinearMap
    have hp (a : BruhatStructuralPair (Multiplicative ℝ))
        (e : ElementaryLCAPresentation a.quotient) :
        Continuous (p ∘ schwartzBruhatStageInclusion a e) := by
      refine (((schwartz_withSeminorms ℂ ℝ ℂ).continuous_seminorm i).comp
        (J a e).symm.continuous).congr fun s ↦ ?_
      change schwartzSeminormFamily ℂ ℝ ℂ i ((J a e).symm s) =
        schwartzSeminormFamily ℂ ℝ ℂ i (E.symm (schwartzBruhatStageInclusion a e s))
      apply congrArg (schwartzSeminormFamily ℂ ℝ ℂ i)
      apply E.injective
      exact (hA a e ((J a e).symm s)).symm.trans
        ((congrArg (fun t : SchwartzBruhatStage e ↦ (schwartzBruhatStageInclusion a e t : ℬ(ℝ)))
          ((J a e).apply_symm_apply s)).trans
            (E.apply_symm_apply (schwartzBruhatStageInclusion a e s)).symm)
    exact (withGeneratingSeminorms_spec _ Subtype.val).continuous_seminorm ⟨p, hp⟩

end RealSchwartzBruhat

end Euclidean

section FinitePlaces

variable (F : Type u) [Field F] [NumberField F]

section

variable (w : Places(F))
local notation "G" => Multiplicative (w.adicCompletion F)

/-- The compact sets of the additive completion are contained in compact open subgroups. -/
private theorem finitePlace_exists_compactOpenSubgroup {s : Set G} (hs : IsCompact s) :
    ∃ H : OpenSubgroup G, IsCompact (H : Set G) ∧ s ⊆ H := by
  let := properSpace_adicCompletion w (K := F)
  have hs' : IsCompact (Multiplicative.toAdd '' s) := hs.image continuous_toAdd
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hs'.isBounded
  let B := IsUltrametricDist.closedBall_openAddSubgroup (w.adicCompletion F)
    (lt_max_of_lt_right (zero_lt_one' ℝ) : 0 < max r 1)
  let H : OpenSubgroup G := ⟨B.toAddSubgroup.toSubgroup, B.isOpen⟩
  refine ⟨H, isCompact_closedBall (0 : w.adicCompletion F) _, fun x hx ↦ ?_⟩
  exact Metric.closedBall_subset_closedBall (le_max_left r _) (hr (mem_image_of_mem _ hx))

/-- The open subgroup of a structural pair for the additive completion is compact. -/
private theorem finitePlace_bruhatSubgroup_compact (a : BruhatStructuralPair G) :
    IsCompact (a.val.1 : Set G) := by
  obtain ⟨U, -, hU, hgen⟩ := a.property.2.1
  obtain ⟨H, hH, hUH⟩ :=
    finitePlace_exists_compactOpenSubgroup F w (hU.image continuous_subtype_val)
  refine hH.of_isClosed_subset (a.val.1.isClosed_of_isOpen a.property.1) ?_
  have h := ((H.toSubgroup.comap a.val.1.subtype).closure_le).2
    (fun x hx ↦ hUH (mem_image_of_mem _ hx))
  rw [hgen] at h
  exact fun x hx ↦ h (Subgroup.mem_top (x := (⟨x, hx⟩ : a.val.1)))

/-- Every elementary quotient in a structural pair for the additive completion is discrete. -/
private theorem finitePlace_bruhatQuotient_discrete (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) : DiscreteTopology a.quotient := by
  -- Pull back the neighborhood, then send an open subgroup inside it to the quotient.
  let : NonarchimedeanGroup a.quotient := {
    is_nonarchimedean := fun U hU ↦ by
      let q := QuotientGroup.mk' ((OrderDual.ofDual a.val.2).comap a.val.1.subtype)
      have hq : Continuous q := QuotientGroup.continuous_mk
      have hpre : q ⁻¹' U ∈ 𝓝 (1 : a.val.1) :=
        hq.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU)
      change q ⁻¹' U ∈ 𝓝 (⟨1, a.val.1.one_mem⟩ : a.val.1) at hpre
      rw [nhds_subtype_eq_comap] at hpre
      obtain ⟨V, hV, hsub⟩ := mem_comap.mp hpre
      have hV' : Multiplicative.ofAdd ⁻¹' V ∈ 𝓝 (0 : w.adicCompletion F) :=
        continuous_ofAdd.continuousAt.preimage_mem_nhds hV
      obtain ⟨B, hB⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hV'
      let H := OpenSubgroup.comap a.val.1.subtype continuous_subtype_val
        (⟨B.toAddSubgroup.toSubgroup, B.isOpen⟩ : OpenSubgroup G)
      refine ⟨⟨H.toSubgroup.map q, QuotientGroup.isOpenMap_coe _ H.isOpen⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hsub (hB hx) }
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.2
    (a.property.2.2.1.1.preimage continuous_subtype_val)
  let : T2Space a.quotient := inferInstance
  let : LocallyConnectedSpace (AddCircle (1 : ℝ)) :=
    (QuotientAddGroup.isQuotientMap_mk _).isCoinducing.locallyConnectedSpace
  let : LocallyConnectedSpace (Multiplicative
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)) := by
    change LocallyConnectedSpace
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)
    infer_instance
  let : LocallyConnectedSpace a.quotient :=
    e.equiv.symm.toHomeomorph.isQuotientMap.isCoinducing.locallyConnectedSpace
  refine discreteTopology_iff_isOpen_singleton_one.2 ?_
  rw [← totallyDisconnectedSpace_iff_connectedComponent_singleton.1 inferInstance (1 : a.quotient)]
  exact isOpen_connectedComponent

/-- Each realized stage on the additive completion is locally constant and compactly supported. -/
private theorem finitePlace_bruhatStage_locallyConstant_compactSupport
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) :
    IsLocallyConstant (schwartzBruhatStageRealization a e s) ∧
      HasCompactSupport (schwartzBruhatStageRealization a e s) := by
  classical
  let := finitePlace_bruhatQuotient_discrete F w a e
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ a.val.1
    · let q : a.val.1 → a.quotient := QuotientGroup.mk
      let V := q ⁻¹' {q ⟨x, hx⟩}
      have hV : IsOpen V := (isOpen_discrete _).preimage QuotientGroup.continuous_mk
      refine ⟨Subtype.val '' V, a.property.1.isOpenEmbedding_subtypeVal.isOpenMap _ hV,
        ⟨⟨x, hx⟩, rfl, rfl⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have heq : q y = q ⟨x, hx⟩ := hy
      simp only [schwartzBruhatStageRealization_apply, dite_eq_left y.property, dite_eq_left hx]
      exact congrArg (fun z ↦ s (Multiplicative.toAdd (e.equiv z))) heq
    · refine ⟨(a.val.1 : Set G)ᶜ, (a.val.1.isClosed_of_isOpen a.property.1).isOpen_compl, hx, ?_⟩
      intro y hy
      change y ∉ a.val.1 at hy
      simp only [schwartzBruhatStageRealization_apply, dite_eq_right hy, dite_eq_right hx]
  · apply HasCompactSupport.of_support_subset_isCompact (finitePlace_bruhatSubgroup_compact F w a)
    intro x hx
    by_contra h
    change x ∉ a.val.1 at h
    exact hx (by simp only [schwartzBruhatStageRealization_apply, dite_eq_right h])

open Classical in
set_option maxRecDepth 2048 in
/-- Every function on a finite cyclic structural quotient realizes a Schwartz–Bruhat function. -/
private theorem finitePlace_mem_cyclicStage (a : BruhatStructuralPair G)
    [Finite a.quotient] [DiscreteTopology a.quotient] (ha : IsCyclic a.quotient)
    (f : a.quotient → ℂ) :
    (fun x : G ↦ if hx : x ∈ a.val.1 then f (QuotientGroup.mk ⟨x, hx⟩) else 0) ∈
      schwartzBruhatSubmodule G := by
  classical
  let n := Nat.card a.quotient
  let : NeZero n := ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  let j : a.quotient ≃* Multiplicative (Fin n) :=
    (zmodCyclicMulEquiv ha).symm.trans (ZMod.finEquiv n).symm.toAddEquiv.toMultiplicative
  let k : Multiplicative (ElementaryLieGroup 0 0 0 (Fin n)) ≃* Multiplicative (Fin n) :=
    { toEquiv := (Equiv.uniqueProd _ _).trans ((Equiv.uniqueProd _ _).trans (Equiv.uniqueProd _ _))
      map_mul' := fun _ _ ↦ rfl }
  let e : ElementaryLCAPresentation a.quotient :=
    { realDim := 0, torusDim := 0, latticeRank := 0, finiteFactor := Fin n
      equiv := (j.trans k.symm).toContinuousMulEquiv
        (fun S ↦ iff_of_true (isOpen_discrete _) (isOpen_discrete _)) }
  let g : ElementaryLieGroup 0 0 0 (Fin n) → ℂ := fun z ↦ f (e.equiv.symm (Multiplicative.ofAdd z))
  have hg : g ∈ elementarySchwartzSubmodule 0 0 0 (Fin n) := by
    refine ⟨fun z b ↦ ?_, fun i ↦ ?_⟩
    · have heq : (fun x ↦ g (elementaryCover x z b)) = fun _ ↦ g (elementaryCover 0 z b) :=
        funext fun x ↦ congrArg (fun y ↦ g (elementaryCover y z b)) (Subsingleton.elim x 0)
      rw [heq]
      exact contDiff_const
    · rw [Subsingleton.elim i (0, 0, 0, 0), elementarySchwartzBound_zero]
      let M := Finset.univ.sup fun z ↦ ‖g z‖₊
      exact (iSup_le fun z ↦ ENNReal.coe_le_coe.2 (Finset.le_sup (Finset.mem_univ z))).trans_lt
        (ENNReal.coe_lt_top (r := M))
  let s : SchwartzBruhatStage e := ⟨g, hg⟩
  apply Submodule.mem_iSup_of_mem a
  apply Submodule.mem_iSup_of_mem e
  refine ⟨s, funext fun x ↦ ?_⟩
  by_cases hx : x ∈ a.val.1
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_left hx]
    exact congrArg f (e.equiv.symm_apply_apply (QuotientGroup.mk ⟨x, hx⟩))
  · simp only [schwartzBruhatStageRealization_apply, dite_eq_right hx]

open Classical in
/-- A character on a finite quotient of a compact open subgroup, extended by zero, is
Schwartz–Bruhat because its image is cyclic. -/
private theorem finitePlace_mem_characterStage (H : OpenSubgroup G) (hH : IsCompact (H : Set G))
    (L : Subgroup H.toSubgroup) (hL : IsOpen (L : Set H.toSubgroup))
    (ψ : AddChar (Additive (H.toSubgroup ⧸ L)) ℂ) :
    (fun x : G ↦ if hx : x ∈ H.toSubgroup then ψ (QuotientGroup.mk ⟨x, hx⟩) else 0) ∈
      schwartzBruhatSubmodule G := by
  classical
  let : LocallyCompactSpace G := locallyCompactSpace_adicCompletion w (K := F)
  let Q := H.toSubgroup ⧸ L
  let : DiscreteTopology Q := QuotientGroup.discreteTopology hL
  let φ : H.toSubgroup →* ℂ := ψ.toMonoidHom.comp (QuotientGroup.mk' L)
  let K := φ.ker.map H.toSubgroup.subtype
  have hKopen : IsOpen (K : Set G) := by
    apply H.isOpen.isOpenEmbedding_subtypeVal.isOpenMap
    change IsOpen ((QuotientGroup.mk : H.toSubgroup → Q) ⁻¹' (ψ ⁻¹' {1}))
    exact (isOpen_discrete _).preimage QuotientGroup.continuous_mk
  have hKH : K ≤ H.toSubgroup := fun _ ⟨x, _, hx⟩ ↦ hx ▸ x.property
  have hKclosed := K.isClosed_of_isOpen hKopen
  let : CompactSpace H.toSubgroup := isCompact_iff_compactSpace.1 hH
  let : CompactSpace (lcaAnnihilator K) :=
    isCompact_iff_compactSpace.1 (isCompact_lcaAnnihilator K hKopen)
  let a : BruhatStructuralPair G :=
    ⟨⟨H.toSubgroup, OrderDual.toDual K⟩, H.isOpen, isCompactlyGeneratedGroup_of_compact,
      ⟨hKclosed, isOpen_lcaAnnihilator K (hH.of_isClosed_subset hKclosed hKH),
        (show IsCompactlyGeneratedGroup (lcaAnnihilator K) from
          isCompactlyGeneratedGroup_of_compact)⟩, hKH⟩
  let : DiscreteTopology a.quotient :=
    QuotientGroup.discreteTopology (hKopen.preimage continuous_subtype_val)
  let : Finite a.quotient := finite_of_compact_of_discrete
  have hker : K.comap H.toSubgroup.subtype = φ.ker :=
    Subgroup.comap_map_eq_self_of_injective Subtype.val_injective _
  let i : a.quotient →* ℂ := QuotientGroup.lift _ φ hker.le
  have hi : Injective i := (QuotientGroup.injective_lift_iff _ φ hker.le).2 hker
  exact finitePlace_mem_cyclicStage F w a (isCyclic_of_injective_ringHom i hi) i

/-- A compactly supported, locally constant function descends to a finite quotient on a compact
open subgroup. Extending the Fourier expansion on that quotient by zero gives Bruhat membership. -/
private theorem finitePlace_mem_of_locallyConstant_compactSupport
    (f : G → ℂ) (hf : IsLocallyConstant f) (hc : HasCompactSupport f) :
    f ∈ schwartzBruhatSubmodule G := by
  classical
  obtain ⟨H, hH, hs⟩ := finitePlace_exists_compactOpenSubgroup F w hc
  have hO : IsOpen {p : G × G | f (p.1 * p.2) = f p.1} := by
    convert ((hf.comp_continuous continuous_mul).comp₂ (hf.comp_continuous continuous_fst) Eq) {True}
      using 1
    ext p
    change (f (p.1 * p.2) = f p.1) ↔ (f (p.1 * p.2) = f p.1) = True
    simp
  obtain ⟨_, V, _, hV, hHV, h1V, hprod⟩ := generalized_tube_lemma hH isCompact_singleton hO
    (show (H : Set G) ×ˢ ({1} : Set G) ⊆ _ by
      rintro ⟨x, y⟩ ⟨_, hy⟩
      obtain rfl := mem_singleton_iff.mp hy
      simp)
  have hnhds : Multiplicative.ofAdd ⁻¹' V ∈ 𝓝 (0 : w.adicCompletion F) :=
    continuous_ofAdd.continuousAt.preimage_mem_nhds (hV.mem_nhds (h1V (mem_singleton 1)))
  obtain ⟨B, hB⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ hnhds
  let L := B.toAddSubgroup.toSubgroup.comap H.toSubgroup.subtype
  let Q := H.toSubgroup ⧸ L
  have hL : IsOpen (L : Set H.toSubgroup) := B.isOpen.preimage continuous_subtype_val
  let : CompactSpace H.toSubgroup := isCompact_iff_compactSpace.1 hH
  let : DiscreteTopology Q := QuotientGroup.discreteTopology hL
  let : Finite Q := finite_of_compact_of_discrete
  let f₀ : Additive Q → ℂ :=
    Quotient.lift (fun x : H.toSubgroup ↦ f x.val) (by
      intro x y hxy
      have heq : (QuotientGroup.mk x : Q) = QuotientGroup.mk y := Quotient.sound hxy
      have hmem : x⁻¹ * y ∈ L := (QuotientGroup.eq (s := L)).mp heq
      have hmemV : (x : G)⁻¹ * (y : G) ∈ V := hB hmem
      have hh := hprod (mk_mem_prod (hHV x.property) hmemV)
      simpa only [mem_ofPred_eq, mul_inv_cancel_left] using hh.symm)
  let extend : (Additive Q → ℂ) →ₗ[ℂ] (G → ℂ) :=
    LinearMap.pi fun x ↦ if hx : x ∈ H.toSubgroup then
      LinearMap.proj (Additive.ofMul (QuotientGroup.mk ⟨x, hx⟩ : Q)) else 0
  have hextend (g : Additive Q → ℂ) (x : G) :
      extend g x = if hx : x ∈ H.toSubgroup then g (QuotientGroup.mk ⟨x, hx⟩) else 0 := by
    dsimp only [extend]
    rw [LinearMap.pi_apply]
    split_ifs <;> rfl
  -- The finite quotient need not be cyclic, but each character factors through a cyclic quotient.
  have hle : ⊤ ≤ (schwartzBruhatSubmodule G).comap extend := by
    rw [← (AddChar.complexBasis (Additive Q)).span_eq]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨ψ, rfl⟩
    rw [AddChar.complexBasis_apply]
    change extend (ψ : Additive Q → ℂ) ∈ schwartzBruhatSubmodule G
    rw [funext (hextend _)]
    exact finitePlace_mem_characterStage F w H hH L hL ψ
  have hmem : extend f₀ ∈ schwartzBruhatSubmodule G := hle Submodule.mem_top
  have hEq : extend f₀ = f := funext fun x ↦ by
    rw [hextend]
    split_ifs with hx
    · rfl
    · exact (notMem_support.mp (fun h ↦ hx (hs (subset_tsupport f h)))).symm
  rwa [hEq] at hmem

end

/-- Paper: §2.1.2.2, p. 63. The additive Schwartz–Bruhat space of a finite completion
consists exactly of the locally constant, compactly supported functions. -/
theorem mem_finitePlaceSchwartz_iff (w : Places(F)) (f : w.adicCompletion F → ℂ) :
    (∃ g : ℬ(w.adicCompletion F), ∀ x, g (Multiplicative.ofAdd x) = f x) ↔
      IsLocallyConstant f ∧ HasCompactSupport f := by
  let G := Multiplicative (w.adicCompletion F)
  change (∃ g : SchwartzBruhat G, ∀ x : G, g x = f x) ↔ _
  constructor
  · rintro ⟨g, hg⟩
    let S : Submodule ℂ (G → ℂ) :=
      { carrier := {h | IsLocallyConstant h ∧ HasCompactSupport h}
        zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
        add_mem' := fun hf hh ↦ ⟨hf.1.comp₂ hh.1 (· + ·), hf.2.add hh.2⟩
        smul_mem' := fun c _ hf ↦ ⟨hf.1.comp (c • ·), hf.2.smul_left⟩ }
    have hle : schwartzBruhatSubmodule G ≤ S := by
      refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
      rintro _ ⟨s, rfl⟩
      exact finitePlace_bruhatStage_locallyConstant_compactSupport F w a e s
    have hmem := hle (show (g : G → ℂ) ∈ schwartzBruhatSubmodule G from g.property)
    rwa [funext hg] at hmem
  · rintro ⟨hf, hc⟩
    exact ⟨⟨f, finitePlace_mem_of_locallyConstant_compactSupport F w f hf hc⟩, fun _ ↦ rfl⟩

-- TODO(paper-gap): In Remark 2.1.2.3, continuity of all linear functionals alone
-- does not characterize the finest locally convex topology. The weak topology
-- also makes all those functionals continuous.

/-- Paper: §2.1.2.2, p. 63. Each elementary Schwartz stage of the additive finite completion
is finite-dimensional because its structural quotient is compact and discrete. -/
private theorem finitePlace_bruhatStage_finiteDimensional (w : Places(F))
    (a : BruhatStructuralPair (Multiplicative (w.adicCompletion F)))
    (e : ElementaryLCAPresentation a.quotient) : FiniteDimensional ℂ (SchwartzBruhatStage e) := by
  let : CompactSpace a.val.1 :=
    isCompact_iff_compactSpace.mp (finitePlace_bruhatSubgroup_compact F w a)
  let : CompactSpace a.quotient := Quotient.compactSpace
  let : DiscreteTopology a.quotient := finitePlace_bruhatQuotient_discrete F w a e
  let : Finite a.quotient := finite_of_compact_of_discrete
  let : Finite (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    Finite.of_equiv a.quotient e.equiv.toEquiv
  change FiniteDimensional ℂ (elementarySchwartzSubmodule _ _ _ _)
  infer_instance

/-- Paper: Proposition 2.1.2.4(1), p. 64. The local Schwartz–Bruhat topology
is the finest locally convex topology. -/
theorem finitePlaceSchwartz_finestTopology (w : Places(F)) :
    (inferInstance : TopologicalSpace ℬ(w.adicCompletion F)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex ℬ(w.adicCompletion F))) := by
  let G := Multiplicative (w.adicCompletion F)
  let E := SchwartzBruhat G
  let P := {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion a e)}
  let p : SeminormFamily ℂ (schwartzBruhatSubmodule G) P := Subtype.val
  have hfinest := finestLocallyConvex_withSeminorms E
  let : ContinuousSMul ℂ (FinestLocallyConvex E) := hfinest.continuousSMul
  have hsurj : Surjective p := by
    intro q
    refine ⟨⟨q, ?_⟩, rfl⟩
    intro a e
    let : FiniteDimensional ℂ (SchwartzBruhatStage e) :=
      finitePlace_bruhatStage_finiteDimensional F w a e
    let : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
    let : ContinuousSMul ℂ (SchwartzBruhatStage e) :=
      elementarySchwartz_withSeminorms.continuousSMul
    let j : SchwartzBruhatStage e →ₗ[ℂ] FinestLocallyConvex E :=
      schwartzBruhatStageInclusion a e
    exact (hfinest.continuous_seminorm q).comp j.continuous_of_finiteDimensional
  let t (q : Seminorm ℂ (schwartzBruhatSubmodule G)) :
      TopologicalSpace (schwartzBruhatSubmodule G) :=
    q.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
  let tS : TopologicalSpace (schwartzBruhatSubmodule G) :=
    (inferInstance : TopologicalSpace E)
  let tF : TopologicalSpace (schwartzBruhatSubmodule G) :=
    (inferInstance : TopologicalSpace (FinestLocallyConvex E))
  have hstage : tS = ⨅ i : P, t (p i) :=
    (withGeneratingSeminorms_spec (schwartzBruhatSubmodule G) p).topologicalSpace_eq_iInf
  have hall : tF = ⨅ q, t q := hfinest.topologicalSpace_eq_iInf
  exact hstage.trans ((hsurj.iInf_comp t).trans hall.symm)

open TopologicalSpace in
/-- The local Schwartz–Bruhat space is spanned by the countable family of indicators
of compact open subsets of the completion. -/
private theorem finitePlaceSchwartz_countableSpanningSet (w : Places(F)) :
    ∃ s : Set (schwartzBruhatSubmodule (Multiplicative (w.adicCompletion F))),
      s.Countable ∧ Submodule.span ℂ s = ⊤ := by
  classical
  let K := w.adicCompletion F
  let E := ↥(schwartzBruhatSubmodule (Multiplicative K))
  let : ProperSpace K := properSpace_adicCompletion w (K := F)
  let compactOpens : Set (Set K) := {U | IsCompact U ∧ IsOpen U}
  let C := ↥compactOpens
  let : Countable (countableBasis K) := countable_countableBasis K
  -- Every compact open set is a finite union of basic open sets.
  let unionBasis (t : Finset (countableBasis K)) : Set K := (t : Set (countableBasis K)).sUnion
  let : Countable C := (countable_range unionBasis).mono fun U hU ↦ by
    obtain ⟨t, ht⟩ := eq_sUnion_finset_of_isTopologicalBasis_of_isCompact_open _
      (isBasis_countableBasis K) U hU.1 hU.2
    exact ⟨t, ht.symm⟩
  have hχ (U : C) : ∃ g : E, ∀ x : K,
      g.val (Multiplicative.ofAdd x) = U.val.indicator (1 : K → ℂ) x := by
    have hcl : IsClopen U.val := ⟨U.property.1.isClosed, U.property.2⟩
    apply (mem_finitePlaceSchwartz_iff F w _).2
    refine ⟨(LocallyConstant.charFn ℂ hcl).isLocallyConstant, ?_⟩
    exact U.property.1.of_isClosed_subset isClosed_closure
      (closure_minimal support_indicator_subset hcl.1)
  let χ (U : C) : E := (hχ U).choose
  have hχ_apply (U : C) (x : K) :
      (χ U).val (Multiplicative.ofAdd x) = U.val.indicator (1 : K → ℂ) x :=
    (hχ U).choose_spec x
  have hcount : (range χ).Countable := countable_range χ
  refine ⟨range χ, hcount, ?_⟩
  apply top_unique
  intro g _
  let f : K → ℂ := fun x ↦ g.val (Multiplicative.ofAdd x)
  obtain ⟨hf, hc⟩ := (mem_finitePlaceSchwartz_iff F w f).1 ⟨g, fun _ ↦ rfl⟩
  have hfinite : (f '' tsupport f).Finite := by
    let : CompactSpace (tsupport f) := isCompact_iff_compactSpace.mp hc
    rw [← range_domRestrict]
    exact (hf.comp_continuous continuous_subtype_val).range_finite
  let A := hfinite.toFinset.erase 0
  have h₀ (a : A) : a.val ≠ 0 := (Finset.mem_erase.mp a.property).1
  let U (a : A) : C := ⟨{x | f x = a.val},
    hc.of_isClosed_subset (hf.isClosed_fiber a.val)
      (fun x hx ↦ subset_tsupport f (mem_support.mpr (fun h ↦ h₀ a (hx.symm.trans h)))),
    hf.isOpen_fiber a.val⟩
  have hsum : (∑ a : A, a.val • χ (U a)) = g := by
    apply Subtype.ext
    funext x
    let y : K := Multiplicative.toAdd x
    let ev : E →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (schwartzBruhatSubmodule (Multiplicative K)).subtype
    change ev (∑ a : A, a.val • χ (U a)) = f y
    simp only [map_sum, map_smul]
    have hterm (a : A) : ev (χ (U a)) = if f y = a.val then 1 else 0 := by
      change (χ (U a)).val (Multiplicative.ofAdd y) = _
      rw [hχ_apply]
      rfl
    simp only [hterm]
    by_cases hy : f y = 0
    · rw [hy]
      apply Finset.sum_eq_zero
      intro a _
      rw [ite_eq_right (h₀ a).symm, smul_zero]
    · have hmem : f y ∈ A := Finset.mem_erase.mpr
        ⟨hy, hfinite.mem_toFinset.mpr ⟨y, subset_tsupport f (mem_support.mpr hy), rfl⟩⟩
      let a : A := ⟨f y, hmem⟩
      rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _) (fun b _ hb ↦ ?_)]
      · simp [a]
      · have hne : f y ≠ b.val := fun h ↦ hb (Subtype.ext h.symm)
        simp [hne]
  rw [← hsum]
  exact Submodule.sum_mem _ fun a _ ↦ Submodule.smul_mem _ _
    (Submodule.subset_span (mem_range_self (U a)))

/-- Paper: Proposition 2.1.2.4(1), p. 64. The local Schwartz–Bruhat space has countable
complex dimension. -/
theorem finitePlaceSchwartz_countableRank (w : Places(F)) :
    Module.rank ℂ ℬ(w.adicCompletion F) ≤ ℵ₀ := by
  change Module.rank ℂ ↥(schwartzBruhatSubmodule (Multiplicative (w.adicCompletion F))) ≤ ℵ₀
  obtain ⟨s, hs, hspan⟩ := finitePlaceSchwartz_countableSpanningSet F w
  rw [← rank_top ℂ _, ← hspan]
  exact (rank_span_le s).trans (Cardinal.mk_le_aleph0_iff.mpr hs.to_subtype)

/-- Finite spans of a countable generating set give a strict LF presentation
for the finest locally convex topology. -/
private theorem finestLocallyConvex_strictLF_of_countable_span
    (E : Type u) [AddCommGroup E] [Module ℂ E]
    {s : Set E} (hs : s.Countable) (hspan : Submodule.span ℂ s = ⊤) :
    IsStrictLFSpace (FinestLocallyConvex E) := by
  let W := FinestLocallyConvex E
  let : T2Space W := finestLocallyConvex_t2 E
  have hfinest := finestLocallyConvex_withSeminorms E
  let A := hs.finiteExhaustion
  let S (n : ℕ) : Submodule ℂ W := Submodule.span ℂ (A n)
  have hmono : Monotone S := fun _ _ h ↦ Submodule.span_mono (A.mono h)
  have hFinite (n : ℕ) : FiniteDimensional ℂ (S n) :=
    FiniteDimensional.span_of_finite ℂ (A.finite n)
  refine ⟨inferInstance, S, hmono, ?_, ?_, ?_⟩
  · intro n
    let : FiniteDimensional ℂ (S n) := hFinite n
    let e := (Module.finBasis ℂ (S n)).equivFun.toContinuousLinearEquiv
    refine ⟨inferInstance, inferInstance, e.toHomeomorph.isEmbedding.metrizableSpace, ?_⟩
    let : UniformSpace (S n) := IsTopologicalAddGroup.rightUniformSpace (S n)
    let : IsUniformAddGroup (S n) := isUniformAddGroup_of_addCommGroup
    exact FiniteDimensional.completeSpace ℂ (S n)
  · intro g
    apply (Submodule.mem_iSup_of_directed S hmono.directed_le).mp
    have hSup : (⨆ n, S n) = ⊤ := by
      change (⨆ n, Submodule.span ℂ (A n)) = ⊤
      rw [Submodule.iSup_span, A.iUnion_eq, hspan]
    exact hSup.symm ▸ Submodule.mem_top
  · let P : SeminormFamily ℂ W {p : Seminorm ℂ W // ∀ n, Continuous (p ∘ (S n).subtype)} :=
      Subtype.val
    have hP : Surjective P := by
      intro p
      refine ⟨⟨p, fun n ↦ ?_⟩, rfl⟩
      let : FiniteDimensional ℂ (S n) := hFinite n
      exact (hfinest.continuous_seminorm p).comp (S n).subtype.continuous_of_finiteDimensional
    let t (p : Seminorm ℂ W) : TopologicalSpace W :=
      p.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
    have hfinal := (withGeneratingSeminorms_spec W P).topologicalSpace_eq_iInf
    exact hfinest.topologicalSpace_eq_iInf.trans ((hP.iInf_comp t).symm.trans hfinal.symm)

/-- Paper: Proposition 2.1.2.4(1), p. 64. The local Schwartz–Bruhat space is a strict
LF-space. -/
theorem finitePlaceSchwartz_strictLF (w : Places(F)) :
    IsStrictLFSpace ℬ(w.adicCompletion F) := by
  let E := ↥(schwartzBruhatSubmodule (Multiplicative (w.adicCompletion F)))
  let tS : TopologicalSpace E := (inferInstance : TopologicalSpace ℬ(w.adicCompletion F))
  let tF : TopologicalSpace E := (inferInstance : TopologicalSpace (FinestLocallyConvex E))
  change @IsStrictLFSpace E _ _ tS
  have htop : tS = tF := finitePlaceSchwartz_finestTopology F w
  refine Eq.mpr (congrArg (fun t ↦ @IsStrictLFSpace E _ _ t) htop) ?_
  exact (finitePlaceSchwartz_countableSpanningSet F w).elim fun s hs ↦
    finestLocallyConvex_strictLF_of_countable_span E hs.1 hs.2

/-- A strict LF presentation gives completeness for the compatible additive uniformity. -/
private theorem completeSpace_of_strictLF {E : Type*} [AddCommGroup E] [Module ℂ E]
    [UniformSpace E] [IsUniformAddGroup E] (h : IsStrictLFSpace E) : CompleteSpace E := by
  obtain ⟨_, S, hmono, hFrechet, hcover, htop⟩ := h
  choose hadd hpoly hmetr hcomplete using hFrechet
  let := hadd
  let := hpoly
  let := hmetr
  let : ∀ n, T2Space (S n) := fun _ ↦ inferInstance
  let j (n : ℕ) : S n →L[ℂ] S (n + 1) :=
    (S n).subtypeL.codRestrict (S (n + 1)) fun x ↦ hmono n.le_succ x.property
  have hlim : IsInjectiveLCLimit j (fun n ↦ (S n).subtypeL) := by
    refine ⟨fun _ ↦ Subtype.val_injective, fun _ ↦ rfl, fun x ↦ ?_, htop⟩
    obtain ⟨n, hn⟩ := hcover x
    exact ⟨n, ⟨⟨x, hn⟩, rfl⟩⟩
  rw [← IsUniformAddGroup.rightUniformSpace_eq (G := E)]
  exact (strictLCLimit_complete_nonmetrizable hcomplete hlim fun n ↦
    IsEmbedding.of_comp (j n).continuous continuous_subtype_val IsEmbedding.subtypeVal).1

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local Schwartz–Bruhat space is complete. -/
theorem finitePlaceSchwartz_complete (w : Places(F)) :
    CompleteSpace ℬ(w.adicCompletion F) :=
  completeSpace_of_strictLF (finitePlaceSchwartz_strictLF F w)

open scoped NNReal in
/-- A countable spanning set gives a rank-one expansion with geometrically
bounded coefficients for the finest locally convex topology. -/
private theorem finestLocallyConvex_nuclear_of_countable_span
    (E : Type u) [AddCommGroup E] [Module ℂ E]
    {s : Set E} (hs : s.Countable) (hspan : Submodule.span ℂ s = ⊤) :
    IsNuclearTVS.{v} (FinestLocallyConvex E) := by
  classical
  let W := FinestLocallyConvex E
  let : T2Space W := finestLocallyConvex_t2 E
  obtain ⟨t, hts, htspan, htindep⟩ := exists_linearIndependent ℂ s
  let b : Module.Basis t ℂ W := Module.Basis.mk htindep (by
    change (⊤ : Submodule ℂ E) ≤ Submodule.span ℂ (range ((↑) : t → E))
    rw [Subtype.range_coe, htspan, hspan])
  let : Encodable t := (hs.mono hts).toEncodable
  let e : t → ℕ := Encodable.encode
  have he : Injective e := Encodable.encode_injective
  apply nuclear_of_rankOne_series
  intro q _
  let d (n : ℕ) : ℝ := (1 / 2) ^ n
  have hd (n : ℕ) : 0 < d n := by dsimp [d]; positivity
  -- Rescale each basis vector to lie in the unit ball of q.
  let a (i : t) : ℝ := 1 + q (b i)
  have ha (i : t) : 0 < a i := by dsimp [a]; positivity
  let c (i : t) : ℝ≥0 := ⟨a i / d (e i), div_nonneg (ha i).le (hd _).le⟩
  let pᵢ (i : t) : Seminorm ℂ ℂ := c i • normSeminorm ℂ ℂ
  let coords := (b.repr.trans (finsuppLEquivDirectSum ℂ ℂ t)).toLinearMap
  let p : Seminorm ℂ W := (directSumSeminorm pᵢ).comp coords
  let φ₀ (i : t) : W →ₗ[ℂ] ℂ := (a i : ℂ) • b.coord i
  let z₀ (i : t) : W := (a i : ℂ)⁻¹ • b i
  let φ := e.extend φ₀ (fun _ ↦ 0)
  let z := e.extend z₀ (fun _ ↦ 0)
  refine ⟨p, φ, z, d, 1, (finestLocallyConvex_withSeminorms E).continuous_seminorm p,
    zero_le_one, summable_geometric_two, fun n ↦ (hd n).le, ?_, ?_, ?_⟩
  · intro n x
    by_cases hn : n ∈ range e
    · obtain ⟨i, rfl⟩ := hn
      have hcoord : (a i / d (e i)) * ‖b.repr x i‖ ≤ p x := by
        have h := sum_le_directSumSeminorm pᵢ (coords x) {i}
        rw [Finset.sum_singleton] at h
        exact h
      rw [show φ (e i) = φ₀ i from he.extend_apply _ _ _]
      change ‖(a i : ℂ) * b.repr x i‖ ≤ d (e i) * p x
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (ha i).le]
      rw [div_mul_eq_mul_div₀] at hcoord
      simpa only [mul_comm (d (e i)) (p x)] using (div_le_iff₀ (hd _)).mp hcoord
    · rw [show φ n = 0 from extend_apply' _ _ _ hn, LinearMap.zero_apply, norm_zero]
      exact mul_nonneg (hd n).le (apply_nonneg p x)
  · intro n
    by_cases hn : n ∈ range e
    · obtain ⟨i, rfl⟩ := hn
      rw [show z (e i) = z₀ i from he.extend_apply _ _ _]
      dsimp only [z₀]
      rw [map_smul_eq_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (ha i).le,
        ← div_eq_inv_mul, div_le_one (ha i)]
      exact le_add_of_nonneg_left zero_le_one
    · rw [show z n = 0 from extend_apply' _ _ _ hn, map_zero]
      exact zero_le_one
  · intro x
    apply (he.hasSum_iff (f := fun n ↦ φ n x • z n) (fun n hn ↦ ?_)).mp
    · have hterm (i : t) : φ (e i) x • z (e i) = b.repr x i • b i := by
        rw [show φ (e i) = φ₀ i from he.extend_apply _ _ _,
          show z (e i) = z₀ i from he.extend_apply _ _ _]
        change ((a i : ℂ) * b.repr x i) • ((a i : ℂ)⁻¹ • b i) = _
        rw [smul_smul, mul_comm (a i : ℂ), mul_assoc,
          mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ha i).ne'), mul_one]
      change HasSum (fun i : t ↦ φ (e i) x • z (e i)) x
      simp_rw [hterm]
      have hsum := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional t)
        (s := (b.repr x).support)
        (f := fun i ↦ b.repr x i • b i)
        (fun i hi ↦ by rw [Finsupp.notMem_support_iff.mp hi, zero_smul])
      change HasSum _ ((b.repr x).sum fun i c ↦ c • b i) at hsum
      simpa only [← Finsupp.linearCombination_apply, b.linearCombination_repr] using hsum
    · rw [show φ n = 0 from extend_apply' _ _ _ hn, LinearMap.zero_apply, zero_smul]

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local Schwartz–Bruhat space is Hausdorff
locally convex and nuclear. -/
theorem finitePlaceSchwartz_nuclear (w : Places(F)) :
    IsNuclearTVS.{v} ℬ(w.adicCompletion F) := by
  let E := ↥(schwartzBruhatSubmodule (Multiplicative (w.adicCompletion F)))
  let tS : TopologicalSpace E := (inferInstance : TopologicalSpace ℬ(w.adicCompletion F))
  let tF : TopologicalSpace E := (inferInstance : TopologicalSpace (FinestLocallyConvex E))
  change @IsNuclearTVS.{v} E _ _ tS
  have htop : tS = tF := finitePlaceSchwartz_finestTopology F w
  rw [htop]
  obtain ⟨s, hs, hspan⟩ := finitePlaceSchwartz_countableSpanningSet F w
  exact finestLocallyConvex_nuclear_of_countable_span E hs hspan

section FinestMontel

open scoped Pointwise

/-- Every seminorm is continuous in the finest locally convex topology, so that topology is
barrelled. -/
private theorem finestLocallyConvex_barrelled (E : Type*) [AddCommGroup E] [Module ℂ E] :
    BarrelledSpace ℂ (FinestLocallyConvex E) := by
  refine ⟨fun p _ ↦ ?_⟩
  exact (finestLocallyConvex_withSeminorms E).continuous_seminorm p

/-- Closed von Neumann bounded sets are compact in the finest locally convex topology: each is
closed and absorbed by a compact neighborhood inside a finite-dimensional subspace. -/
private theorem finestLocallyConvex_montel (E : Type*) [AddCommGroup E] [Module ℂ E] :
    MontelSpace ℂ (FinestLocallyConvex E) := by
  refine ⟨fun s hs hbd ↦ ?_⟩
  obtain ⟨S, hfin, hsub, hbdS⟩ := (finestLocallyConvex_isVonNBounded_iff (E := E) s).mp hbd
  have : FiniteDimensional ℂ S := hfin
  have : LocallyCompactSpace S := LocallyCompactSpace.of_finiteDimensional_of_complete ℂ S
  obtain ⟨K, hK, hKnhds⟩ := exists_compact_mem_nhds (0 : S)
  let pre : Set S := Subtype.val ⁻¹' s
  have habs : Absorbs ℂ K pre := hbdS hKnhds
  obtain ⟨a, ha⟩ := habs.exists
  have hpre : IsCompact pre :=
    (hK.smul a).of_isClosed_subset (hs.preimage continuous_subtype_val) ha
  have himage : Subtype.val '' pre = s := by
    unfold pre
    apply image_preimage_eq_of_subset
    rw [Subtype.range_val]
    exact hsub
  rw [← himage]
  exact hpre.image continuous_subtype_val

end FinestMontel

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local Schwartz–Bruhat space is Montel. -/
theorem finitePlaceSchwartz_montel (w : Places(F)) :
    BarrelledSpace ℂ ℬ(w.adicCompletion F) ∧ MontelSpace ℂ ℬ(w.adicCompletion F) := by
  let E := ↥(schwartzBruhatSubmodule (Multiplicative (w.adicCompletion F)))
  let tS : TopologicalSpace E := (inferInstance : TopologicalSpace ℬ(w.adicCompletion F))
  let tF : TopologicalSpace E := (inferInstance : TopologicalSpace (FinestLocallyConvex E))
  have htop : tS = tF := finitePlaceSchwartz_finestTopology F w
  refine ⟨?_, ?_⟩
  · change @BarrelledSpace ℂ E _ _ _ tS
    exact Eq.mpr (congrArg (fun t ↦ @BarrelledSpace ℂ E _ _ _ t) htop)
      (finestLocallyConvex_barrelled E)
  · change @MontelSpace ℂ E _ _ _ tS
    exact Eq.mpr (congrArg (fun t ↦ @MontelSpace ℂ E _ _ _ t) htop)
      (finestLocallyConvex_montel E)

/-- Paper: Proposition C.2.5.1(6), p. 692. With the finest locally convex topology,
a countable-dimensional space has Fréchet strong dual, via evaluation on a basis. -/
private theorem finestLocallyConvex_dual_frechet_of_countableRank
    (E : Type*) [AddCommGroup E] [Module ℂ E] (hE : Module.rank ℂ E ≤ ℵ₀) :
    IsFrechetTVS (StrongDual ℂ (FinestLocallyConvex E)) := by
  classical
  let W := FinestLocallyConvex E
  let D := StrongDual ℂ W
  let ι := Module.Free.ChooseBasisIndex ℂ W
  let b : Module.Basis ι ℂ W := Module.Free.chooseBasis ℂ W
  let : Countable ι := Cardinal.mk_le_aleph0_iff.mp (b.mk_eq_rank''.trans_le hE)
  let : T2Space W := finestLocallyConvex_t2 E
  let : ContinuousSMul ℂ W := (finestLocallyConvex_withSeminorms E).continuousSMul
  let e : D ≃ₗ[ℂ] (ι → ℂ) :=
    { toFun := fun f i ↦ f (b i)
      invFun := fun z ↦ ⟨b.constr ℂ z, continuous_of_finestLocallyConvex E _⟩
      left_inv := fun f ↦ ContinuousLinearMap.ext fun x ↦ LinearMap.congr_fun
        (b.constr_eq ℂ (f := f.toLinearMap) fun _ ↦ rfl) x
      right_inv := fun z ↦ funext (b.constr_basis ℂ z)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  have hEval : Continuous e := continuous_pi fun i ↦ continuous_eval_const (b i)
  have hContValue (x : W) : Continuous (fun z : ι → ℂ ↦ e.symm z x) := by
    change Continuous (fun z : ι → ℂ ↦ (b.constr ℂ z) x)
    simp only [b.constr_apply, Finsupp.sum]
    exact continuous_finsetSum _ fun i _ ↦
      (continuous_apply i : Continuous (fun z : ι → ℂ ↦ z i)).const_smul (b.repr x i)
  -- On a bounded set, uniform convergence is controlled by finitely many evaluations.
  have hInv : Continuous e.symm := by
    apply continuous_of_tendsto_nhds_zero e.symm
    rw [(ContinuousLinearMap.hasBasis_nhds_zero_of_basis
      (Metric.nhds_basis_ball (x := (0 : ℂ)))).tendsto_right_iff]
    rintro ⟨B, ε⟩ ⟨hB, hε⟩
    obtain ⟨S, hS, hBS, hBounded⟩ :=
      (finestLocallyConvex_isVonNBounded_iff (E := E) B).mp hB
    let : FiniteDimensional ℂ S := hS
    let c := Module.finBasis ℂ S
    have hCoord i : ∃ C : ℝ, ∀ x ∈ (Subtype.val : S → W) ⁻¹' B, ‖c.repr x i‖ ≤ C := by
      let l : S →L[ℂ] ℂ := ⟨c.coord i, (c.coord i).continuous_of_finiteDimensional⟩
      exact (NormedSpace.image_isVonNBounded_iff ℂ).mp (hBounded.image l)
    choose C hC using hCoord
    let p (z : ι → ℂ) : ℝ := ∑ i, C i * ‖e.symm z (c i : W)‖
    have hp : Continuous p := continuous_finsetSum _ fun i _ ↦
      continuous_const.mul (hContValue (c i)).norm
    have hp₀ : p 0 = 0 := by simp [p]
    have hSmall : ∀ᶠ z in 𝓝 (0 : ι → ℂ), p z < ε :=
      hp.continuousAt.eventually_lt continuousAt_const (hp₀ ▸ hε)
    filter_upwards [hSmall] with z hz
    intro x hx
    rw [Metric.mem_ball, dist_zero_right]
    let y : S := ⟨x, hBS hx⟩
    let f : S →ₗ[ℂ] ℂ := (e.symm z).toLinearMap.comp S.subtype
    change ‖f y‖ < ε
    calc
      ‖f y‖ = ‖∑ i, c.repr y i • f (c i)‖ := by
        simpa only [map_sum, map_smul] using congrArg (fun x ↦ ‖f x‖) (c.sum_repr y).symm
      _ ≤ ∑ i, ‖c.repr y i • f (c i)‖ := norm_sum_le _ _
      _ ≤ p z := by
        apply Finset.sum_le_sum
        intro i _
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hC i y hx) (norm_nonneg _)
      _ < ε := hz
  let dualEquiv : D ≃L[ℂ] (ι → ℂ) := ⟨e, hEval, hInv⟩
  have hInd := dualEquiv.toHomeomorph.isInducing
  refine ⟨inferInstance, dualEquiv.PolynormableSpace,
    dualEquiv.toHomeomorph.isEmbedding.metrizableSpace, ?_⟩
  rw [IsUniformAddGroup.rightUniformSpace_eq (G := D)]
  exact (AddMonoidHom.isUniformInducing_of_isInducing (f := dualEquiv.toLinearEquiv.toAddMonoidHom)
    hInd).completeSpace_congr dualEquiv.surjective |>.mpr inferInstance

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local strong dual is Fréchet. -/
theorem finitePlaceSchwartz_strongDual_frechet (w : Places(F)) :
    IsFrechetTVS (StrongDual ℂ ℬ(w.adicCompletion F)) := by
  let E := ↥(schwartzBruhatSubmodule (Multiplicative (w.adicCompletion F)))
  let tS : TopologicalSpace E := (inferInstance : TopologicalSpace ℬ(w.adicCompletion F))
  let tF : TopologicalSpace E := (inferInstance : TopologicalSpace (FinestLocallyConvex E))
  change (letI : TopologicalSpace E := tS; IsFrechetTVS (StrongDual ℂ E))
  have htop : tS = tF := finitePlaceSchwartz_finestTopology F w
  exact Eq.mpr (congrArg (fun t : TopologicalSpace E ↦
    letI := t
    IsFrechetTVS (StrongDual ℂ E)) htop)
    (finestLocallyConvex_dual_frechet_of_countableRank E (finitePlaceSchwartz_countableRank F w))

/-- Paper: Proposition C.2.5.1(6), p. 692. The strong dual of a space with its finest
locally convex topology is nuclear. Each bounded set of the primal space lies in a
finite-dimensional subspace, so uniform convergence on that set follows from
convergence on finitely many basis vectors.
Deviation: Nuclearity of the strong dual holds without the countability hypothesis. -/
private theorem finestLocallyConvex_strongDual_nuclear
    (E : Type u) [AddCommGroup E] [Module ℂ E] :
    IsNuclearTVS.{v} (StrongDual ℂ (FinestLocallyConvex E)) := by
  let W := FinestLocallyConvex E
  let D := StrongDual ℂ W
  let Dweak := WeakDual ℂ W
  have hW := finestLocallyConvex_withSeminorms E
  let : IsTopologicalAddGroup W := hW.isTopologicalAddGroup
  let : ContinuousSMul ℂ W := hW.continuousSMul
  let : PolynormableSpace ℂ W := hW.toPolynormableSpace
  let : T2Space W := finestLocallyConvex_t2 E
  have hweak : Continuous (StrongDual.toWeakDual : D → Dweak) :=
    WeakDual.continuous_of_continuous_eval (fun x : W ↦ continuous_eval_const x)
  have hstrong : Continuous (WeakDual.toStrongDual : Dweak → D) := by
    apply continuous_of_tendsto_nhds_zero (WeakDual.toStrongDual : Dweak ≃ₗ[ℂ] D)
    apply ContinuousLinearMap.hasBasis_nhds_zero.tendsto_right_iff.mpr
    rintro ⟨B, U⟩ ⟨hB, hU⟩
    obtain ⟨S, hdim, hBS, hbounded⟩ := (finestLocallyConvex_isVonNBounded_iff B).mp hB
    -- Restrict to S by recording the evaluations on its basis.
    let b := Module.finBasis ℂ S
    let e := (b.constr ℂ).trans
      (LinearMap.toContinuousLinearMap : (S →ₗ[ℂ] ℂ) ≃ₗ[ℂ] StrongDual ℂ S)
    let r (f : Dweak) : StrongDual ℂ S := e (fun i ↦ f (b i : W))
    have hr : Continuous r := e.toLinearMap.continuous_of_finiteDimensional.comp
      (continuous_pi fun i ↦ WeakDual.eval_continuous (b i : W))
    have hr_zero : r 0 = 0 := e.map_zero
    have ht : Tendsto r (𝓝 0) (𝓝 0) := hr_zero ▸ hr.continuousAt
    filter_upwards [ht.eventually (ContinuousLinearMap.eventually_nhds_zero_mapsTo hbounded hU)]
      with f hf
    intro x hx
    let y : S := ⟨x, hBS hx⟩
    have hy : r f y = f x := by
      have heq : (r f).toLinearMap = f.toStrongDual.toLinearMap.comp S.subtype := by
        apply b.ext
        intro i
        exact b.constr_basis ℂ (fun i ↦ f (b i : W)) i
      exact LinearMap.congr_fun heq y
    exact hy ▸ hf (show y ∈ Subtype.val ⁻¹' B from hx)
  let tS : TopologicalSpace D := inferInstance
  let tW : TopologicalSpace D := (inferInstance : TopologicalSpace Dweak)
  have htop : tS = tW :=
    le_antisymm (continuous_id_iff_le.mp hweak) (continuous_id_iff_le.mp hstrong)
  change @IsNuclearTVS.{v} D _ _ tS
  rw [htop]
  exact isNuclearTVS_weakDual W

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local strong dual is nuclear. -/
theorem finitePlaceSchwartz_strongDual_nuclear (w : Places(F)) :
    IsNuclearTVS.{v} (StrongDual ℂ ℬ(w.adicCompletion F)) := by
  let E := ↥(schwartzBruhatSubmodule (Multiplicative (w.adicCompletion F)))
  let tS : TopologicalSpace E := (inferInstance : TopologicalSpace ℬ(w.adicCompletion F))
  let tF : TopologicalSpace E := (inferInstance : TopologicalSpace (FinestLocallyConvex E))
  let P (t : TopologicalSpace E) := IsNuclearTVS.{v} (@StrongDual ℂ _ _ E t _ _)
  change P tS
  have htop : tS = tF := finitePlaceSchwartz_finestTopology F w
  rw [htop]
  exact finestLocallyConvex_strongDual_nuclear E

/-- Paper: Proposition 2.1.2.4(3), p. 64. Every linear subspace of the local Schwartz–Bruhat
space has a continuous linear retraction. -/
theorem finitePlaceSchwartz_complemented (w : Places(F))
    (W : Submodule ℂ ℬ(w.adicCompletion F)) : W.ClosedComplemented := by
  exact (congrArg (fun t ↦ @Submodule.ClosedComplemented ℂ _ _ t _ _ W)
    (finitePlaceSchwartz_finestTopology F w)).mpr
    (finestLocallyConvex_submodule_closedComplemented W)

-- TODO(paper-gap): Examples 2.1.2.5–6 assert that every open subset is a finite union
-- of balls. The whole local field is open and noncompact. The assertion applies
-- to compact open subsets, which suffice for the displayed expansion.

open scoped WithZero in
/-- Paper: Example 2.1.2.6, p. 65. A local Schwartz–Bruhat function is a finite linear
combination of indicators of translates of nonzero powers of the maximal ideal.
Deviation: The uniformizer is specified by its normalized valuation. -/
theorem finitePlaceSchwartz_sum_indicators (w : Places(F)) (f : ℬ(w.adicCompletion F))
    (π : w.adicCompletion F)
    (hπ : Valued.v π = WithZero.exp (-1 : ℤ)) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (a : Fin n → w.adicCompletion F) (N : Fin n → ℤ),
      (∀ i, N i ≠ 0) ∧ ∀ x : w.adicCompletion F,
        f (Multiplicative.ofAdd x) =
          ∑ i, c i * Set.indicator
            {y | ∃ z : w.adicCompletionIntegers F, y = a i + π ^ N i * z.val} (fun _ ↦ 1) x := by
  classical
  let K := w.adicCompletion F
  let g : K → ℂ := fun x ↦ f (Multiplicative.ofAdd x)
  obtain ⟨hg, hc⟩ := (mem_finitePlaceSchwartz_iff F w g).1 ⟨f, fun _ ↦ rfl⟩
  -- Compactness gives one neighborhood of translations fixing all values on the support.
  have hopen : IsOpen {p : K × K | g (p.1 + p.2) = g p.1} := by
    have hloc : IsLocallyConstant (fun p : K × K ↦ g (p.1 + p.2) = g p.1) :=
      (hg.comp_continuous continuous_add).comp₂ (hg.comp_continuous continuous_fst) Eq
    simpa only [eq_iff_iff, iff_true] using hloc.isOpen_fiber True
  obtain ⟨U, V, _, hV, hU, hzero, hUV⟩ :=
    generalized_tube_lemma hc (isCompact_singleton (x := (0 : K))) hopen (by
      rintro ⟨x, y⟩ ⟨_, hy⟩
      obtain rfl := mem_singleton_iff.mp hy
      change g (x + 0) = g x
      rw [add_zero])
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp (hV.mem_nhds (hzero (mem_singleton 0)))
  let ν : Valuation K ℤᵐ⁰ := Valued.v
  let r : ℤᵐ⁰ := MonoidWithZeroHom.ValueGroup₀.embedding γ.val
  have hr : r ≠ 0 := by simp [r]
  let N : ℤ := max 1 (1 - WithZero.log r)
  have hN : 0 < N := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hpow : ν (π ^ N) = WithZero.exp (-N) := by
    rw [map_zpow₀ ν, show ν π = _ from hπ, ← WithZero.exp_zsmul]
    simp
  have hv : ν (π ^ N) ≠ 0 := by simp [hpow]
  have hlt : ν (π ^ N) < r := by
    rw [hpow, ← WithZero.exp_log hr, WithZero.exp_lt_exp]
    have h := le_max_right 1 (1 - WithZero.log r)
    omega
  let L := ν.leAddSubgroup (ν (π ^ N))
  have hL : (L : Set K) ⊆ V := fun x hx ↦
    hγ ((ν.restrict_lt_iff_lt_embedding).mpr (lt_of_le_of_lt hx hlt))
  have hLopen : IsOpen (L : Set K) := by
    change IsOpen {x : K | ν x ≤ ν (π ^ N)}
    have hball : IsOpen {x : K | ν.restrict x ≤ ν.restrict (π ^ N)} :=
      Valued.isOpen_closedBall K (fun h ↦ hv (ν.restrict_eq_zero_iff.mp h))
    simpa only [Valuation.restrict_le_iff] using hball
  let q : K → K ⧸ L := QuotientAddGroup.mk
  let : DiscreteTopology (K ⧸ L) := QuotientAddGroup.discreteTopology hLopen
  let A := q '' tsupport g
  have hfinite : A.Finite := (hc.image QuotientAddGroup.continuous_mk).finite_of_discrete
  let : Fintype A := hfinite.fintype
  let e := (Fintype.equivFin A).symm
  let a (i : Fin (Fintype.card A)) : K := (e i).property.choose
  have ha (i : Fin (Fintype.card A)) : a i ∈ tsupport g ∧ q (a i) = (e i).val :=
    (e i).property.choose_spec
  -- Each quotient fiber is a translate of the scaled integer ring.
  have hfiber (x y : K) :
      (∃ z : w.adicCompletionIntegers F, x = y + π ^ N * z.val) ↔ q x = q y := by
    have hp : π ^ N ≠ 0 := fun h ↦ hv (by rw [h, map_zero])
    rw [QuotientAddGroup.eq_iff_sub_mem]
    constructor
    · rintro ⟨z, rfl⟩
      change ν (y + π ^ N * z.val - y) ≤ ν (π ^ N)
      rw [add_sub_cancel_left, map_mul]
      exact mul_le_of_le_one_right' z.property
    · intro hx
      have hz : (x - y) / π ^ N ∈ w.adicCompletionIntegers F := by
        change ν ((x - y) / π ^ N) ≤ 1
        rw [ν.map_div, div_le_one₀ (pos_of_ne_zero hv)]
        exact hx
      exact ⟨⟨_, hz⟩, by
        change x = y + π ^ N * ((x - y) / π ^ N)
        rw [mul_comm (π ^ N), div_mul_cancel₀ _ hp, add_sub_cancel]⟩
  refine ⟨_, fun i ↦ g (a i), a, fun _ ↦ N, fun _ ↦ hN.ne', fun x ↦ ?_⟩
  change g x = _
  simp only [Set.indicator, Set.mem_ofPred_eq, hfiber, fun i ↦ (ha i).2]
  by_cases hx : q x ∈ A
  · let i := e.symm ⟨q x, hx⟩
    have hi : (e i).val = q x := congrArg Subtype.val (e.apply_symm_apply ⟨q x, hx⟩)
    rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ _)]
    · rw [ite_eq_left hi.symm, mul_one]
      have hmem : x - a i ∈ L :=
        QuotientAddGroup.eq_iff_sub_mem.mp (show q x = q (a i) from hi.symm.trans (ha i).2.symm)
      have heq : g (a i + (x - a i)) = g (a i) :=
        hUV (mk_mem_prod (hU (ha i).1) (hL hmem))
      simpa only [add_sub_cancel] using heq
    · intro j _ hj
      have hne : q x ≠ (e j).val := fun h ↦ hj (e.injective (Subtype.ext (h.symm.trans hi.symm)))
      rw [ite_eq_right hne, mul_zero]
  · have hgx : g x = 0 := notMem_support.mp fun hs ↦ hx ⟨x, subset_tsupport g hs, rfl⟩
    rw [hgx]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : q x ≠ (e i).val := fun h ↦ hx (h.symm ▸ (e i).property)
    rw [ite_eq_right hne, mul_zero]

/-- Paper: Proposition 2.1.2.8, p. 65. The finite adelic tail is the restricted product
of the finite completions outside the chosen finite set, relative to their integer rings. -/
abbrev FiniteAdeleTail (S : Finset (Places(F))) :=
  Πʳ w : {w : Places(F) // w ∉ S},
    [w.val.adicCompletion F, w.val.adicCompletionIntegers F]

/-- Paper: Proposition 2.1.2.8, p. 65. When no finite places are omitted, the tail is
the finite adele ring, with its usual topology and coordinate projections.
Deviation: This is a sanity check for the restricted product over the complement. -/
theorem finiteAdeleTail_empty :
    ∃ e : FiniteAdeleTail F ∅ ≃+* 𝔸ᶠ[F], IsHomeomorph e ∧
      ∀ (x : FiniteAdeleTail F ∅) (w : Places(F)) (hw : w ∉ (∅ : Finset (Places(F)))),
        (e x) w = x ⟨w, hw⟩ := by
  let f : Places(F) → {w : Places(F) // w ∉ (∅ : Finset (Places(F)))} :=
    fun w ↦ ⟨w, Finset.notMem_empty w⟩
  have hf : Tendsto f cofinite cofinite :=
    Injective.tendsto_cofinite (f := f) fun a b h ↦ congrArg Subtype.val h
  have hg : Tendsto (Subtype.val : {w : Places(F) // w ∉ (∅ : Finset (Places(F)))} → Places(F))
      cofinite cofinite := Subtype.val_injective.tendsto_cofinite
  let φ : FiniteAdeleTail F ∅ →+* 𝔸ᶠ[F] :=
    RestrictedProduct.mapAlongRingHom _ _ f hf (fun _ ↦ RingHom.id _)
      (.of_forall fun _ ↦ Set.mapsTo_id _)
  let ψ : 𝔸ᶠ[F] →+* FiniteAdeleTail F ∅ :=
    RestrictedProduct.mapAlongRingHom (fun w : Places(F) ↦ w.adicCompletion F)
      (fun w : {w : Places(F) // w ∉ (∅ : Finset (Places(F)))} ↦ w.val.adicCompletion F)
      Subtype.val hg (fun _ ↦ RingHom.id _) (.of_forall fun _ ↦ Set.mapsTo_id _)
  refine ⟨RingEquiv.ofRingHom φ ψ (by ext x w; rfl) (by ext x w; rfl), ?_, fun _ _ _ ↦ rfl⟩
  refine isHomeomorph_iff_exists_inverse.mpr
    ⟨RestrictedProduct.mapAlong_continuous _ _ f hf _ (.of_forall fun _ ↦ Set.mapsTo_id _)
        fun _ ↦ continuous_id, ψ, fun _ ↦ rfl, fun _ ↦ rfl,
      RestrictedProduct.mapAlong_continuous _ _ _ hg _ (.of_forall fun _ ↦ Set.mapsTo_id _)
        fun _ ↦ continuous_id⟩

/-- Paper: Proposition 2.1.2.8, p. 65. This product retains exactly the finite
completions at the chosen places, with the finite product topology. -/
abbrev FinitePlaceProduct (S : Finset (Places(F))) := ∀ w : S, w.val.adicCompletion F

/-- Paper: Proposition 2.1.2.8, p. 65. The one-place product identifies with
that place's completion by evaluation.
Deviation: This is a sanity check on the product indexing. -/
theorem finitePlaceProduct_singleton (w : Places(F)) :
    ∃ e : FinitePlaceProduct F {w} ≃+* w.adicCompletion F, IsHomeomorph e ∧
      ∀ x, e x = x ⟨w, Finset.mem_singleton_self w⟩ :=
  ⟨RingEquiv.piUnique _, (Homeomorph.piUnique _).isHomeomorph, fun _ ↦ rfl⟩

local instance (S : Finset (Places(F))) :
    Fact (∀ w : {w : Places(F) // w ∉ S},
      IsOpen (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F))) :=
  ⟨fun w ↦ Valued.isOpen_valuationSubring (w.val.adicCompletion F)⟩

-- TODO(paper-gap): The cofinal family in the proof of Proposition 2.1.2.8 only
-- shrinks inside the integral product. It cannot exhaust the ambient group.

/-- For a totally disconnected group whose compact sets fit in compact subgroups, each
elementary stage is realized by locally constant functions with compact support. -/
private theorem bruhatStage_locallyConstant_compactSupport {G : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hcompact : ∀ K : Set G, IsCompact K → ∃ H : Subgroup G, IsCompact (H : Set G) ∧ K ⊆ H)
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (s : SchwartzBruhatStage e) :
    IsLocallyConstant (schwartzBruhatStageRealization a e s) ∧
      HasCompactSupport (schwartzBruhatStageRealization a e s) := by
  classical
  obtain ⟨U, -, hU, hgen⟩ := a.property.2.1
  obtain ⟨H, hH, hUH⟩ := hcompact _ (hU.image continuous_subtype_val)
  have h := ((H.comap a.val.1.subtype).closure_le).2
    (fun x hx ↦ hUH (mem_image_of_mem _ hx))
  rw [hgen] at h
  have hc : IsCompact (a.val.1 : Set G) :=
    hH.of_isClosed_subset (a.val.1.isClosed_of_isOpen a.property.1)
      fun x hx ↦ h (Subgroup.mem_top (x := (⟨x, hx⟩ : a.val.1)))
  let : CompactSpace a.val.1 := isCompact_iff_compactSpace.mp hc
  let : NonarchimedeanGroup a.quotient := {
    is_nonarchimedean := fun V hV ↦ by
      let q := QuotientGroup.mk' ((OrderDual.ofDual a.val.2).comap a.val.1.subtype)
      have hq : Continuous q := QuotientGroup.continuous_mk
      have hp : q ⁻¹' V ∈ 𝓝 (1 : a.val.1) :=
        hq.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hV)
      obtain ⟨W, ⟨hW, h1W⟩, hWV⟩ := (nhds_basis_isClopen (1 : a.val.1)).mem_iff.mp hp
      obtain ⟨B, hB⟩ := IsTopologicalGroup.exist_openSubgroup_sub_clopen_nhds_of_one hW h1W
      refine ⟨⟨B.toSubgroup.map q, QuotientGroup.isOpenMap_coe _ B.isOpen⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hWV (hB hx) }
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.2
    (a.property.2.2.1.1.preimage continuous_subtype_val)
  let : LocallyConnectedSpace (AddCircle (1 : ℝ)) :=
    (QuotientAddGroup.isQuotientMap_mk _).isCoinducing.locallyConnectedSpace
  let : LocallyConnectedSpace (Multiplicative
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)) :=
    inferInstanceAs (LocallyConnectedSpace
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor))
  let : LocallyConnectedSpace a.quotient :=
    e.equiv.symm.toHomeomorph.isQuotientMap.isCoinducing.locallyConnectedSpace
  let : DiscreteTopology a.quotient := discreteTopology_iff_isOpen_singleton_one.2 (by
    rw [← totallyDisconnectedSpace_iff_connectedComponent_singleton.1 inferInstance (1 : a.quotient)]
    exact isOpen_connectedComponent)
  refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x ↦ ?_, ?_⟩
  · by_cases hx : x ∈ a.val.1
    · let q : a.val.1 → a.quotient := QuotientGroup.mk
      let V := q ⁻¹' {q ⟨x, hx⟩}
      have hV : IsOpen V := (isOpen_discrete _).preimage QuotientGroup.continuous_mk
      refine ⟨Subtype.val '' V, a.property.1.isOpenEmbedding_subtypeVal.isOpenMap _ hV,
        ⟨⟨x, hx⟩, rfl, rfl⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have heq : q y = q ⟨x, hx⟩ := hy
      simp only [schwartzBruhatStageRealization_apply, dite_eq_left y.property, dite_eq_left hx]
      exact congrArg (fun z ↦ s (Multiplicative.toAdd (e.equiv z))) heq
    · refine ⟨(a.val.1 : Set G)ᶜ, (a.val.1.isClosed_of_isOpen a.property.1).isOpen_compl, hx, ?_⟩
      intro y hy
      change y ∉ a.val.1 at hy
      simp only [schwartzBruhatStageRealization_apply, dite_eq_right hy, dite_eq_right hx]
  · apply HasCompactSupport.of_support_subset_isCompact hc
    intro x hx
    by_contra h
    change x ∉ a.val.1 at h
    exact hx (by simp only [schwartzBruhatStageRealization_apply, dite_eq_right h])

/-- Second-countable totally disconnected groups whose compact sets fit in compact subgroups
have countable-dimensional Schwartz–Bruhat spaces. -/
private theorem schwartzBruhat_countableRank_of_compactSubgroups (G : Type*)
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [TotallyDisconnectedSpace G]
    [SecondCountableTopology G]
    (hcompact : ∀ K : Set G, IsCompact K → ∃ H : Subgroup G, IsCompact (H : Set G) ∧ K ⊆ H) :
    Module.rank ℂ (SchwartzBruhat G) ≤ ℵ₀ := by
  change Module.rank ℂ ↥(schwartzBruhatSubmodule G) ≤ ℵ₀
  obtain ⟨s, hs, hspan⟩ := exists_countable_span_of_locallyConstant_compactSupport G ℂ
  have hle : schwartzBruhatSubmodule G ≤ Submodule.span ℂ s := by
    refine iSup_le fun a ↦ iSup_le fun e ↦ ?_
    rintro _ ⟨f, rfl⟩
    obtain ⟨hf, hc⟩ := bruhatStage_locallyConstant_compactSupport hcompact a e f
    exact hspan _ hf hc
  exact (Submodule.rank_mono hle).trans
    ((rank_span_le s).trans (Cardinal.mk_le_aleph0_iff.mpr hs.to_subtype))

/-- Finite places form a countable set because their ideals are finitely generated
over the countable ring of integers. -/
private theorem finitePlaces_countable : Countable (Places(F)) := by
  let : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  let : Countable (𝓞 F) := (RingOfIntegers.coe_injective (K := F)).countable
  have h : Surjective (fun s : Finset (𝓞 F) ↦ Ideal.span (s : Set (𝓞 F))) :=
    fun I ↦ IsNoetherian.noetherian I
  let : Countable (Ideal (𝓞 F)) := h.countable
  exact (show Injective (HeightOneSpectrum.asIdeal (R := 𝓞 F)) from fun _ _ h ↦
    HeightOneSpectrum.ext h).countable

/-- Additive form of compact-subgroup containment in a finite completion. -/
private theorem adicCompletion_compact_subset_addSubgroup (w : Places(F))
    (K : Set (w.adicCompletion F)) (hK : IsCompact K) :
    ∃ H : AddSubgroup (w.adicCompletion F), IsCompact (H : Set (w.adicCompletion F)) ∧ K ⊆ H := by
  obtain ⟨H, hH, hKH⟩ :=
    finitePlace_exists_compactOpenSubgroup F w (hK.image continuous_ofAdd)
  exact ⟨H.toSubgroup.toAddSubgroup, hH, fun x hx ↦ hKH (mem_image_of_mem _ hx)⟩

/-- Compact sets in a finite product fit in products of compact additive subgroups. -/
private theorem finitePlaceProduct_compact_subset_subgroup (S : Finset (Places(F)))
    (K : Set (Multiplicative (FinitePlaceProduct F S))) (hK : IsCompact K) :
    ∃ H : Subgroup (Multiplicative (FinitePlaceProduct F S)),
      IsCompact (H : Set (Multiplicative (FinitePlaceProduct F S))) ∧ K ⊆ H := by
  choose B hB hKB using fun w : S ↦ adicCompletion_compact_subset_addSubgroup F w.val _
    (hK.image ((continuous_apply w).comp continuous_toAdd))
  exact ⟨(AddSubgroup.pi univ B).toSubgroup, isCompact_univ_pi hB,
    fun x hx w _ ↦ hKB w (mem_image_of_mem _ hx)⟩

open TopologicalSpace in
/-- The tail is covered by the open stages with integral coordinates outside a finite set.
Each of these stages embeds into the ordinary countable product. -/
private theorem finiteAdeleTail_secondCountable (T : Finset (Places(F))) :
    SecondCountableTopology (FiniteAdeleTail F T) := by
  classical
  let I := {w : Places(F) // w ∉ T}
  let K (w : I) := w.val.adicCompletion F
  let O (w : I) : Set (K w) := w.val.adicCompletionIntegers F
  have hopen (w : I) : IsOpen (O w) := Valued.isOpen_valuationSubring (K w)
  let : Countable (Places(F)) := finitePlaces_countable F
  let (w : I) : ProperSpace (K w) := properSpace_adicCompletion w.val
  let U (s : Finset I) := {a : FiniteAdeleTail F T | ∀ w ∉ s, a w ∈ O w}
  let (s : Finset I) : SecondCountableTopology (U s) := by
    have hs : Filter.cofinite ≤ Filter.principal (s : Set I)ᶜ :=
      le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
    have he := RestrictedProduct.isEmbedding_inclusion_principal (R := K) (A := O) hs
    let : SecondCountableTopology (Πʳ w : I, [K w, O w]_[Filter.principal (s : Set I)ᶜ]) :=
      (RestrictedProduct.isEmbedding_coe_of_principal (R := K) (A := O)).secondCountableTopology
    have hrange : range (RestrictedProduct.inclusion K O hs) = U s := by
      rw [RestrictedProduct.range_inclusion]
      ext a
      exact Filter.eventually_principal
    exact hrange ▸ he.toHomeomorph.symm.isEmbedding.secondCountableTopology
  refine secondCountableTopology_of_countable_cover (U := U)
    (fun _ ↦ RestrictedProduct.isOpen_forall_imp_mem hopen) (eq_univ_of_forall fun a ↦ ?_)
  have he := Filter.eventually_cofinite.mp a.2
  exact mem_iUnion.mpr ⟨he.toFinset, fun w hw ↦ by
    by_contra h
    exact hw (he.mem_toFinset.mpr h)⟩

/-- Compact sets in the tail have a common finite set of possibly nonintegral
coordinates. Bound those coordinates by compact additive subgroups. -/
private theorem finiteAdeleTail_compact_subset_subgroup (T : Finset (Places(F)))
    (C : Set (Multiplicative (FiniteAdeleTail F T))) (hC : IsCompact C) :
    ∃ H : Subgroup (Multiplicative (FiniteAdeleTail F T)),
      IsCompact (H : Set (Multiplicative (FiniteAdeleTail F T))) ∧ C ⊆ H := by
  classical
  let I := {w : Places(F) // w ∉ T}
  let K (w : I) := w.val.adicCompletion F
  let O (w : I) := w.val.adicCompletionIntegers F
  let C' := Multiplicative.toAdd '' C
  let U (s : Finset I) := {a : FiniteAdeleTail F T | ∀ w ∉ s, a w ∈ O w}
  have hcover : C' ⊆ ⋃ s, U s := by
    intro a _
    have ha := Filter.eventually_cofinite.mp a.2
    exact mem_iUnion.mpr ⟨ha.toFinset, fun w hw ↦ not_not.mp (hw ∘ ha.mem_toFinset.mpr)⟩
  obtain ⟨s, hs⟩ := (hC.image continuous_toAdd).elim_directed_cover U
    (fun _ ↦ RestrictedProduct.isOpen_forall_imp_mem (fun w ↦ Valued.isOpen_valuationSubring (K w)))
    hcover (fun s₁ s₂ ↦ ⟨s₁ ∪ s₂, fun _ hx w hw ↦ hx w (fun h ↦ hw (Finset.mem_union_left _ h)),
      fun _ hx w hw ↦ hx w (fun h ↦ hw (Finset.mem_union_right _ h))⟩)
  choose B hB hCB using fun w : I ↦ adicCompletion_compact_subset_addSubgroup F w.val _
    ((hC.image continuous_toAdd).image (RestrictedProduct.continuous_eval w))
  let D (w : I) : AddSubgroup (K w) := if w ∈ s then B w else (O w).toAddSubgroup
  have hD_in (w : I) (hw : w ∈ s) : D w = B w := ite_eq_left hw
  have hD_out (w : I) (hw : w ∉ s) : D w = (O w).toAddSubgroup := ite_eq_right hw
  let (w : I) : CompactSpace (D w) := by
    by_cases hw : w ∈ s
    · rw [hD_in w hw]
      exact isCompact_iff_compactSpace.mp (hB w)
    · rw [hD_out w hw]
      exact compactSpace_adicCompletionIntegers w.val
  let eval : FiniteAdeleTail F T →+ (∀ w : I, K w) :=
    ⟨⟨fun a w ↦ a w, rfl⟩, fun _ _ ↦ rfl⟩
  let H := (AddSubgroup.pi univ D).comap eval
  have hfilter : Filter.cofinite ≤ Filter.principal (s : Set I)ᶜ :=
    le_principal_iff.mpr s.finite_toSet.compl_mem_cofinite
  have hD (a : ∀ w, K w) (ha : ∀ w, a w ∈ D w) :
      ∀ᶠ w in Filter.principal (s : Set I)ᶜ, a w ∈ O w :=
    Filter.eventually_principal.mpr fun w hw ↦ by
      have hn : w ∉ s := hw
      have hm := ha w
      rw [hD_out w hn] at hm
      exact hm
  let j (a : ∀ w, D w) : Πʳ w : I, [K w, O w]_[Filter.principal (s : Set I)ᶜ] :=
    RestrictedProduct.mk (fun w ↦ a w) (hD _ fun w ↦ (a w).property)
  let i := RestrictedProduct.inclusion K (fun w ↦ (O w : Set (K w))) hfilter
  have hj : Continuous j := RestrictedProduct.continuous_rng_of_principal_iff_forall.mpr
    (fun w ↦ continuous_subtype_val.comp (continuous_apply w))
  have hH : range (i ∘ j) = (H : Set (FiniteAdeleTail F T)) := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      exact fun w _ ↦ (x w).property
    · intro ha
      exact ⟨fun w ↦ ⟨a w, ha w (mem_univ _)⟩, DFunLike.ext _ _ fun _ ↦ rfl⟩
  refine ⟨H.toSubgroup, ?_, fun x hx w _ ↦ ?_⟩
  · change IsCompact (H : Set (FiniteAdeleTail F T))
    rw [← hH]
    exact isCompact_range ((RestrictedProduct.continuous_inclusion hfilter).comp hj)
  · change (Multiplicative.toAdd x) w ∈ D w
    by_cases hw : w ∈ s
    · rw [hD_in w hw]
      exact hCB w (mem_image_of_mem _ (mem_image_of_mem _ hx))
    · rw [hD_out w hw]
      exact hs (mem_image_of_mem _ hx) w hw

/-- Paper: Proposition 2.1.2.8(1), p. 65. The finite-product and tail Schwartz–Bruhat
spaces have countable complex dimension. -/
theorem finiteProduct_tailSchwartz_countableRank (S T : Finset (Places(F))) :
    Module.rank ℂ ℬ((FinitePlaceProduct F S)) ≤ ℵ₀ ∧
      Module.rank ℂ ℬ(FiniteAdeleTail F T) ≤ ℵ₀ := by
  constructor
  · let (w : S) : ProperSpace (w.val.adicCompletion F) := properSpace_adicCompletion w.val
    let : TotallyDisconnectedSpace (Multiplicative (FinitePlaceProduct F S)) :=
      inferInstanceAs (TotallyDisconnectedSpace (∀ w : S, w.val.adicCompletion F))
    exact schwartzBruhat_countableRank_of_compactSubgroups _
      (finitePlaceProduct_compact_subset_subgroup F S)
  · let : SecondCountableTopology (FiniteAdeleTail F T) := finiteAdeleTail_secondCountable F T
    let : IsTopologicalAddGroup (FiniteAdeleTail F T) := by
      unfold FiniteAdeleTail
      infer_instance
    let : T2Space (Multiplicative (FiniteAdeleTail F T)) :=
      inferInstanceAs (T2Space (Πʳ w : {w : Places(F) // w ∉ T},
        [w.val.adicCompletion F, w.val.adicCompletionIntegers F]))
    let : TotallyDisconnectedSpace (Multiplicative (FiniteAdeleTail F T)) :=
      ⟨isTotallyDisconnected_of_image
        (RestrictedProduct.continuous_coe.comp continuous_toAdd).continuousOn
        (DFunLike.coe_injective.comp Multiplicative.toAdd.injective)
        (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
    exact schwartzBruhat_countableRank_of_compactSubgroups _
      (finiteAdeleTail_compact_subset_subgroup F T)

/-- If every compact subset of a Hausdorff topological group is contained in a compact subgroup,
then every open compactly generated subgroup is compact (its generating compact set lies in a
compact subgroup, and the subgroup is the closure of that subgroup's image). -/
private theorem bruhatSubgroup_compact_of_mem_compactSubgroup {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    (h : ∀ ⦃s : Set G⦄, IsCompact s → ∃ H : Subgroup G, IsCompact (H : Set G) ∧ s ⊆ H)
    (a : BruhatStructuralPair G) : IsCompact (a.val.1 : Set G) := by
  obtain ⟨U, -, hU, hgen⟩ := a.property.2.1
  obtain ⟨H, hH, hUH⟩ := h (hU.image continuous_subtype_val)
  refine hH.of_isClosed_subset (a.val.1.isClosed_of_isOpen a.property.1) ?_
  have hc := ((H.comap a.val.1.subtype).closure_le).2
    (fun x hx ↦ hUH (mem_image_of_mem _ hx))
  rw [hgen] at hc
  exact fun x hx ↦ hc (Subgroup.mem_top (x := (⟨x, hx⟩ : a.val.1)))

/-- If open subgroups form a neighbourhood base at the identity, every structural quotient
of the group is discrete, so the associated elementary stage is finite-dimensional. -/
private theorem bruhatQuotient_discrete_of_smallSubgroups {G : Type*} [CommGroup G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ∀ U : Set G, U ∈ 𝓝 (1 : G) → ∃ V : Subgroup G, IsOpen (V : Set G) ∧ (V : Set G) ⊆ U)
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) :
    DiscreteTopology a.quotient := by
  -- Pull back the neighborhood, then send an open subgroup inside it to the quotient.
  let : NonarchimedeanGroup a.quotient := {
    is_nonarchimedean := fun U hU ↦ by
      let q := QuotientGroup.mk' ((OrderDual.ofDual a.val.2).comap a.val.1.subtype)
      have hq : Continuous q := QuotientGroup.continuous_mk
      have hpre : q ⁻¹' U ∈ 𝓝 (1 : a.val.1) :=
        hq.continuousAt.preimage_mem_nhds (by simpa only [map_one] using hU)
      change q ⁻¹' U ∈ 𝓝 (⟨1, a.val.1.one_mem⟩ : a.val.1) at hpre
      rw [nhds_subtype_eq_comap] at hpre
      obtain ⟨V, hV, hsub⟩ := mem_comap.mp hpre
      obtain ⟨B, hBopen, hBsub⟩ := h V hV
      let H := OpenSubgroup.comap a.val.1.subtype continuous_subtype_val
        (⟨B, hBopen⟩ : OpenSubgroup G)
      refine ⟨⟨H.toSubgroup.map q, QuotientGroup.isOpenMap_coe _ H.isOpen⟩, ?_⟩
      rintro _ ⟨x, hx, rfl⟩
      exact hsub (hBsub hx) }
  let : T1Space a.quotient := QuotientGroup.t1Space_iff.2
    (a.property.2.2.1.1.preimage continuous_subtype_val)
  let : T2Space a.quotient := inferInstance
  let : LocallyConnectedSpace (AddCircle (1 : ℝ)) :=
    (QuotientAddGroup.isQuotientMap_mk _).isCoinducing.locallyConnectedSpace
  let : LocallyConnectedSpace (Multiplicative
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)) := by
    change LocallyConnectedSpace
      (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor)
    infer_instance
  let : LocallyConnectedSpace a.quotient :=
    e.equiv.symm.toHomeomorph.isQuotientMap.isCoinducing.locallyConnectedSpace
  refine discreteTopology_iff_isOpen_singleton_one.2 ?_
  rw [← totallyDisconnectedSpace_iff_connectedComponent_singleton.1 inferInstance (1 : a.quotient)]
  exact isOpen_connectedComponent

/-- Each stage over a compact structural quotient with discrete quotient is finite-dimensional. -/
private theorem bruhatStage_finiteDimensional_of_compactDiscrete {G : Type*} [CommGroup G]
    [TopologicalSpace G]
    (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient)
    (hcomp : IsCompact (a.val.1 : Set G)) (hdisc : DiscreteTopology a.quotient) :
    FiniteDimensional ℂ (SchwartzBruhatStage e) := by
  let : CompactSpace a.val.1 := isCompact_iff_compactSpace.mp hcomp
  let : CompactSpace a.quotient := Quotient.compactSpace
  let : DiscreteTopology a.quotient := hdisc
  let : Finite a.quotient := finite_of_compact_of_discrete
  let : Finite (ElementaryLieGroup e.realDim e.torusDim e.latticeRank e.finiteFactor) :=
    Finite.of_equiv a.quotient e.equiv.toEquiv
  change FiniteDimensional ℂ (elementarySchwartzSubmodule _ _ _ _)
  infer_instance

/-- If every structural stage is finite-dimensional, every seminorm restricts continuously to
each stage, so the Schwartz–Bruhat topology is the finest locally convex topology. -/
private theorem schwartzBruhat_eq_finestLocallyConvex_of_stageFiniteDim {G : Type*} [CommGroup G]
    [TopologicalSpace G]
    (h : ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      FiniteDimensional ℂ (SchwartzBruhatStage e)) :
    (inferInstance : TopologicalSpace (SchwartzBruhat G)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex (SchwartzBruhat G))) := by
  let E := SchwartzBruhat G
  let P := {p : Seminorm ℂ (schwartzBruhatSubmodule G) //
    ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient),
      Continuous (p ∘ schwartzBruhatStageInclusion a e)}
  let p : SeminormFamily ℂ (schwartzBruhatSubmodule G) P := Subtype.val
  have hfinest := finestLocallyConvex_withSeminorms E
  let : ContinuousSMul ℂ (FinestLocallyConvex E) := hfinest.continuousSMul
  have hsurj : Surjective p := by
    intro q
    refine ⟨⟨q, ?_⟩, rfl⟩
    intro a e
    let := h a e
    let : T2Space (SchwartzBruhatStage e) := elementarySchwartz_t2
    let : ContinuousSMul ℂ (SchwartzBruhatStage e) :=
      elementarySchwartz_withSeminorms.continuousSMul
    let j : SchwartzBruhatStage e →ₗ[ℂ] FinestLocallyConvex E :=
      schwartzBruhatStageInclusion a e
    exact (hfinest.continuous_seminorm q).comp j.continuous_of_finiteDimensional
  let t (q : Seminorm ℂ (schwartzBruhatSubmodule G)) :
      TopologicalSpace (schwartzBruhatSubmodule G) :=
    q.toSeminormedAddCommGroup.toUniformSpace.toTopologicalSpace
  let tS : TopologicalSpace (schwartzBruhatSubmodule G) :=
    (inferInstance : TopologicalSpace E)
  let tF : TopologicalSpace (schwartzBruhatSubmodule G) :=
    (inferInstance : TopologicalSpace (FinestLocallyConvex E))
  have hstage : tS = ⨅ i : P, t (p i) :=
    (withGeneratingSeminorms_spec (schwartzBruhatSubmodule G) p).topologicalSpace_eq_iInf
  have hall : tF = ⨅ q, t q := hfinest.topologicalSpace_eq_iInf
  exact hstage.trans ((hsurj.iInf_comp t).trans hall.symm)

/-- Every compact subset of a finite product of finite completions lies in a compact subgroup. -/
private theorem finitePlaceProduct_mem_compactSubgroup (S : Finset (Places(F)))
    {s : Set (Multiplicative (FinitePlaceProduct F S))} (hs : IsCompact s) :
    ∃ H : Subgroup (Multiplicative (FinitePlaceProduct F S)),
      IsCompact (H : Set (Multiplicative (FinitePlaceProduct F S))) ∧ s ⊆ H := by
  let R := FinitePlaceProduct F S
  have hsR : IsCompact (Multiplicative.toAdd '' s) := hs.image continuous_toAdd
  have hproj (w : S) :
      IsCompact (Multiplicative.ofAdd '' ((fun x : R ↦ x w) '' (Multiplicative.toAdd '' s))) :=
    (hsR.image (continuous_apply w)).image continuous_ofAdd
  choose H hHc hHs using fun w : S ↦ finitePlace_exists_compactOpenSubgroup F w.val (hproj w)
  let D (w : S) : AddSubgroup (w.val.adicCompletion F) := (H w).toSubgroup.toAddSubgroup'
  let P : AddSubgroup R := AddSubgroup.pi Set.univ D
  have hmem (x : Multiplicative R) :
      x ∈ P.toSubgroup ↔ ∀ w : S, (Multiplicative.toAdd x) w ∈ D w := by
    rw [Multiplicative.mem_toSubgroup, AddSubgroup.mem_pi]
    simp
  refine ⟨P.toSubgroup, ?_, ?_⟩
  · have hset : (P.toSubgroup : Set (Multiplicative R)) =
        Set.univ.pi fun w ↦ (H w : Set (Multiplicative (w.val.adicCompletion F))) := by
      ext x
      constructor
      · intro hx w _
        have h1 : (Multiplicative.toAdd x) w ∈ D w :=
          ((hmem x).1 (SetLike.mem_coe.mp hx)) w
        simp only [D, Subgroup.mem_toAddSubgroup'] at h1
        have hcoord : Multiplicative.ofAdd ((Multiplicative.toAdd x) w) = x w := by
          delta Multiplicative.toAdd Multiplicative.ofAdd
          rfl
        rw [hcoord] at h1
        exact h1
      · intro hx
        refine SetLike.mem_coe.mpr ((hmem x).2 fun w ↦ ?_)
        simp only [D, Subgroup.mem_toAddSubgroup']
        have hcoord : Multiplicative.ofAdd ((Multiplicative.toAdd x) w) = x w := by
          delta Multiplicative.toAdd Multiplicative.ofAdd
          rfl
        rw [hcoord]
        exact hx w (Set.mem_univ w)
    rw [hset]
    exact isCompact_univ_pi fun w ↦ hHc w
  · intro x hx
    rw [SetLike.mem_coe, hmem]
    intro w
    apply (Subgroup.mem_toAddSubgroup' _ _).2
    refine hHs w ?_
    exact ⟨(Multiplicative.toAdd x) w,
      ⟨Multiplicative.toAdd x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩

/-- Open subgroups form a neighbourhood base at the identity of a finite product of
finite completions. -/
private theorem finitePlaceProduct_smallSubgroups (S : Finset (Places(F)))
    {U : Set (Multiplicative (FinitePlaceProduct F S))}
    (hU : U ∈ 𝓝 (1 : Multiplicative (FinitePlaceProduct F S))) :
    ∃ V : Subgroup (Multiplicative (FinitePlaceProduct F S)),
      IsOpen (V : Set (Multiplicative (FinitePlaceProduct F S))) ∧
        (V : Set (Multiplicative (FinitePlaceProduct F S))) ⊆ U := by
  let R := FinitePlaceProduct F S
  have hU0 : Multiplicative.ofAdd ⁻¹' U ∈ 𝓝 (0 : R) :=
    continuous_ofAdd.continuousAt.preimage_mem_nhds hU
  rw [nhds_pi] at hU0
  obtain ⟨I, hI, rest⟩ := Filter.mem_pi.mp hU0
  obtain ⟨t, ht, hsub⟩ := rest
  choose B hB using fun w : S ↦ NonarchimedeanAddGroup.is_nonarchimedean (t w) (ht w)
  let D (w : S) : AddSubgroup (w.val.adicCompletion F) := (B w).toAddSubgroup
  let P : AddSubgroup R := AddSubgroup.pi Set.univ D
  have hmem (x : Multiplicative R) :
      x ∈ P.toSubgroup ↔ ∀ w : S, (Multiplicative.toAdd x) w ∈ (B w : Set _) := by
    rw [Multiplicative.mem_toSubgroup, AddSubgroup.mem_pi]
    simp [D]
  refine ⟨P.toSubgroup, ?_, ?_⟩
  · have hset : (P.toSubgroup : Set (Multiplicative R)) =
        Set.univ.pi fun w ↦ (B w : Set (w.val.adicCompletion F)) := by
      ext x
      constructor
      · intro hx w _
        have h1 : (Multiplicative.toAdd x) w ∈ (B w : Set _) :=
          ((hmem x).1 (SetLike.mem_coe.mp hx)) w
        have hcoord : (Multiplicative.toAdd x) w = x w := by
          delta Multiplicative.toAdd
          rfl
        rw [hcoord] at h1
        exact h1
      · intro hx
        refine SetLike.mem_coe.mpr ((hmem x).2 fun w ↦ ?_)
        have hcoord : (Multiplicative.toAdd x) w = x w := by
          delta Multiplicative.toAdd
          rfl
        rw [hcoord]
        exact hx w (Set.mem_univ w)
    rw [hset]
    exact isOpen_set_pi Set.finite_univ fun w _ ↦ (B w).isOpen
  · intro x hx
    rw [SetLike.mem_coe] at hx
    have hxB : ∀ w : S, (Multiplicative.toAdd x) w ∈ (B w : Set _) := (hmem x).1 hx
    have hxI : (Multiplicative.toAdd x) ∈ I.pi t := by
      intro w hw
      exact hB w (hxB w)
    have hxU : Multiplicative.ofAdd (Multiplicative.toAdd x) ∈ U := hsub hxI
    have hxeq : Multiplicative.ofAdd (Multiplicative.toAdd x) = x := by
      delta Multiplicative.toAdd Multiplicative.ofAdd
      rfl
    rw [hxeq] at hxU
    exact hxU

/-- Every compact subset of a finite adele tail lies in a compact subgroup. -/
private theorem finiteAdeleTail_mem_compactSubgroup (T : Finset (Places(F)))
    {s : Set (Multiplicative (FiniteAdeleTail F T))} (hs : IsCompact s) :
    ∃ H : Subgroup (Multiplicative (FiniteAdeleTail F T)),
      IsCompact (H : Set (Multiplicative (FiniteAdeleTail F T))) ∧ s ⊆ H := by
  classical
  unfold FiniteAdeleTail at *
  let ι := {w : Places(F) // w ∉ T}
  let K := fun w : ι ↦ w.val.adicCompletion F
  let A : (w : ι) → Set (K w) := fun w ↦ w.val.adicCompletionIntegers F
  let R := FiniteAdeleTail F T
  have hAopen : ∀ w : ι, IsOpen (A w) := fun w ↦ Valued.isOpen_valuationSubring (K w)
  have hsR : IsCompact (Multiplicative.toAdd '' s) := hs.image continuous_toAdd
  let ιF := {E : Set ι // E.Finite}
  haveI : Nonempty ιF := ⟨⟨∅, Set.finite_empty⟩⟩
  let U (E : ιF) : Set R := {x | ∀ w, w ∉ E.1 → x w ∈ A w}
  have hUopen (E : ιF) : IsOpen (U E) := by
    have hopen :=
      RestrictedProduct.isOpen_forall_imp_mem
        (R := fun w : {w : Places(F) // w ∉ T} ↦ w.val.adicCompletion F)
        (A := fun w : {w : Places(F) // w ∉ T} ↦
          (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F)))
        (fun w ↦ Valued.isOpen_valuationSubring (w.val.adicCompletion F))
        (p := fun w ↦ w ∉ E.1)
    convert hopen using 1
  have hcover : Multiplicative.toAdd '' s ⊆ ⋃ E : ιF, U E := by
    intro x _
    have hfin : {w | x w ∉ A w}.Finite := Filter.eventually_cofinite.mp x.2
    exact Set.mem_iUnion.mpr ⟨⟨_, hfin⟩, fun w hw ↦ by
      by_contra h
      exact hw h⟩
  have hdir : Directed (fun a b : Set R ↦ a ⊆ b) U := by
    intro E₁ E₂
    refine ⟨⟨E₁.1 ∪ E₂.1, E₁.2.union E₂.2⟩, ?_, ?_⟩
    · intro x hx w hw
      exact hx w (fun hE ↦ hw (Or.inl hE))
    · intro x hx w hw
      exact hx w (fun hE ↦ hw (Or.inr hE))
  obtain ⟨E, hsE⟩ := hsR.elim_directed_cover U hUopen hcover hdir
  have hproj (w : ι) : IsCompact ((fun x : R ↦ x w) '' (Multiplicative.toAdd '' s)) :=
    hsR.image (RestrictedProduct.continuous_eval (R := K) (A := A) w)
  let spec (w : ι) :=
    finitePlace_exists_compactOpenSubgroup F w.val ((hproj w).image continuous_ofAdd)
  let Hball (w : ι) : OpenSubgroup (Multiplicative (K w)) := (spec w).choose
  have hHball (w : ι) := (spec w).choose_spec
  let Oadd (w : ι) : AddSubgroup (K w) :=
    (w.val.adicCompletionIntegers F).toSubring.toAddSubgroup
  let D (w : ι) : AddSubgroup (K w) :=
    if w ∈ E.1 then (Hball w).toSubgroup.toAddSubgroup' else Oadd w
  have hDcomp (w : ι) : IsCompact (D w : Set (K w)) := by
    by_cases hw : w ∈ E.1
    · have hEq : (D w : Set (K w)) =
          (Hball w : Set (Multiplicative (K w))) := by
        ext z
        have hDw : D w = (Hball w).toSubgroup.toAddSubgroup' := by
          unfold D
          rw [if_pos hw]
        rw [hDw, SetLike.mem_coe, Subgroup.mem_toAddSubgroup']
        rw [show Multiplicative.ofAdd z = z by delta Multiplicative.ofAdd; rfl]
        rfl
      rw [hEq]
      exact (hHball w).1
    · have hEq : (D w : Set (K w)) = A w := by
        ext z
        simp [D, hw, Oadd, A, Subring.coe_toAddSubgroup, ValuationSubring.mem_toSubring]
      rw [hEq]
      have hrange :
          Set.range (Subtype.val : w.val.adicCompletionIntegers F → K w) = A w := by
        ext z
        constructor
        · rintro ⟨u, rfl⟩
          exact u.property
        · intro hz
          exact ⟨⟨z, hz⟩, rfl⟩
      rw [← hrange]
      haveI : CompactSpace (w.val.adicCompletionIntegers F) :=
        compactSpace_adicCompletionIntegers (K := F) w.val
      exact isCompact_range continuous_subtype_val
  let Sset : Set ι := E.1ᶜ
  have hS : Filter.cofinite ≤ Filter.principal Sset :=
    Filter.le_principal_iff.mpr E.2.compl_mem_cofinite
  let Q : Set (Π w, K w) := Set.univ.pi fun w ↦ (D w : Set (K w))
  have hQ : IsCompact Q := isCompact_univ_pi hDcomp
  let RS := Πʳ (w : ι), [K w, A w]_[Filter.principal Sset]
  have hQsub : Q ⊆ Set.range ((↑) : RS → Π w, K w) := by
    rw [RestrictedProduct.range_coe_principal]
    intro x hx w hw
    have hwE : w ∉ E.1 := hw
    have hxw : x w ∈ (D w : Set _) := hx w trivial
    have hEq : (D w : Set (K w)) = A w := by
      ext z
      simp [D, hwE, Oadd, A, Subring.coe_toAddSubgroup, ValuationSubring.mem_toSubring]
    rw [← hEq]
    exact hxw
  have hpre : IsCompact (((↑) : RS → Π w, K w) ⁻¹' Q) :=
    (RestrictedProduct.isEmbedding_coe_of_principal (R := K) (A := A) (S := Sset)).isCompact_preimage_iff
      hQsub |>.mpr hQ
  let incl := RestrictedProduct.inclusion K A hS
  have heq : {x : R | ∀ w, x w ∈ D w} = incl '' (((↑) : RS → Π w, K w) ⁻¹' Q) := by
    ext x
    constructor
    · intro hx
      have hxS : ∀ w ∈ Sset, x w ∈ A w := by
        intro w hw
        have hwE : w ∉ E.1 := hw
        have hEq : D w = Oadd w := by simp [D, hwE]
        have hxw : x w ∈ Oadd w := hEq ▸ hx w
        simpa [Oadd, A, Subring.coe_toAddSubgroup, ValuationSubring.mem_toSubring] using hxw
      obtain ⟨y, hy⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually K A hS
        (Filter.eventually_principal.mpr hxS)
      refine ⟨y, ?_, hy⟩
      intro w _
      have hxw : x w ∈ D w := hx w
      rw [← hy] at hxw
      rwa [RestrictedProduct.inclusion_apply] at hxw
    · rintro ⟨y, hy, rfl⟩
      intro w
      rw [RestrictedProduct.inclusion_apply]
      have hyQ : (y : Π w, K w) ∈ Q := hy
      exact hyQ w trivial
  let Hadd : AddSubgroup R :=
    { carrier := {x | ∀ w, x w ∈ D w}
      zero_mem' := fun w ↦ by
        rw [RestrictedProduct.zero_apply]
        exact (D w).zero_mem
      add_mem' := fun {a b} ha hb w ↦ by
        rw [RestrictedProduct.add_apply]
        exact (D w).add_mem (ha w) (hb w)
      neg_mem' := fun {a} ha w ↦ by
        rw [RestrictedProduct.neg_apply]
        exact (D w).neg_mem (ha w) }
  have hcarrier : (Hadd : Set R) = incl '' (((↑) : RS → Π w, K w) ⁻¹' Q) := by
    simpa [Hadd] using heq
  refine ⟨Hadd.toSubgroup, ?_, ?_⟩
  · have hcomp : IsCompact (Hadd : Set R) := by
      rw [hcarrier]
      exact hpre.image (RestrictedProduct.continuous_inclusion (R := K) (A := A) hS)
    have hset : (Hadd.toSubgroup : Set (Multiplicative R)) = (Hadd : Set R) := by
      ext z
      rw [SetLike.mem_coe, Multiplicative.mem_toSubgroup]
      rfl
    rw [hset]
    exact hcomp
  · intro x hx
    rw [SetLike.mem_coe, Multiplicative.mem_toSubgroup]
    intro w
    by_cases hw : w ∈ E.1
    · have hmem : Multiplicative.ofAdd ((Multiplicative.toAdd x) w) ∈ Hball w :=
        (hHball w).2 ⟨(Multiplicative.toAdd x) w,
          ⟨Multiplicative.toAdd x, ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
      have hDw : D w = (Hball w).toSubgroup.toAddSubgroup' := by simp [D, hw]
      rw [hDw]
      simpa [Subgroup.mem_toAddSubgroup'] using hmem
    · have hx0 : Multiplicative.toAdd x ∈ Multiplicative.toAdd '' s := ⟨x, hx, rfl⟩
      have hxA : (Multiplicative.toAdd x) w ∈ A w := hsE hx0 w hw
      have hDw : D w = Oadd w := by simp [D, hw]
      rw [hDw]
      simpa [Oadd, A, Subring.coe_toAddSubgroup, ValuationSubring.mem_toSubring] using hxA

/-- Open subgroups form a neighbourhood base at the identity of a finite adele tail. -/
private theorem finiteAdeleTail_smallSubgroups (T : Finset (Places(F)))
    {U : Set (Multiplicative (FiniteAdeleTail F T))}
    (hU : U ∈ 𝓝 (1 : Multiplicative (FiniteAdeleTail F T))) :
    ∃ V : Subgroup (Multiplicative (FiniteAdeleTail F T)),
      IsOpen (V : Set (Multiplicative (FiniteAdeleTail F T))) ∧
        (V : Set (Multiplicative (FiniteAdeleTail F T))) ⊆ U := by
  classical
  unfold FiniteAdeleTail at *
  let ι := {w : Places(F) // w ∉ T}
  let K := fun w : ι ↦ w.val.adicCompletion F
  let A : (w : ι) → Set (K w) := fun w ↦ w.val.adicCompletionIntegers F
  let R := FiniteAdeleTail F T
  have hAopen : ∀ w : ι, IsOpen (A w) := fun w ↦ Valued.isOpen_valuationSubring (K w)
  have hU0 : Multiplicative.ofAdd ⁻¹' U ∈ 𝓝 (0 : R) :=
    continuous_ofAdd.continuousAt.preimage_mem_nhds hU
  let Suniv : Set ι := Set.univ
  have hS : Filter.cofinite ≤ Filter.principal Suniv := by
    rw [Filter.principal_univ]
    exact le_top
  let Runiv := Πʳ (w : ι), [K w, A w]_[Filter.principal Suniv]
  let incl : Runiv → R := RestrictedProduct.inclusion K A hS
  have hzero : incl 0 = (0 : R) := by
    ext w
    rfl
  have hnhds : 𝓝 (0 : R) = Filter.map incl (𝓝 (0 : Runiv)) := by
    simpa [hzero, incl, R, K, A, ι, FiniteAdeleTail] using
      RestrictedProduct.nhds_eq_map_inclusion (R := K) (A := A) hAopen hS (0 : Runiv)
  have hpre : incl ⁻¹' (Multiplicative.ofAdd ⁻¹' U) ∈ 𝓝 (0 : Runiv) := by
    rw [← Filter.mem_map, ← hnhds]
    exact hU0
  rw [(RestrictedProduct.isEmbedding_coe_of_principal (R := K) (A := A) (S := Suniv)).nhds_eq_comap
    (0 : Runiv)] at hpre
  obtain ⟨W, hW, hWsub⟩ := Filter.mem_comap.mp hpre
  rw [nhds_pi] at hW
  obtain ⟨I, hI, rest⟩ := Filter.mem_pi.mp hW
  obtain ⟨t, ht, hsub⟩ := rest
  choose B hB using fun w : ι ↦ NonarchimedeanAddGroup.is_nonarchimedean (t w) (ht w)
  let Oadd (w : ι) : AddSubgroup (K w) :=
    (w.val.adicCompletionIntegers F).toSubring.toAddSubgroup
  let D (w : ι) : AddSubgroup (K w) :=
    if w ∈ I then (B w).toAddSubgroup ⊓ Oadd w else Oadd w
  let Oset : Set Runiv := {y | ∀ w, w ∈ I → y w ∈ (B w : Set (K w))}
  have hOopen : IsOpen Oset := by
    have hrewrite : Oset = ((↑) : Runiv → Π w, K w) ⁻¹' (I.pi fun w ↦ (B w : Set (K w))) := by
      ext y
      simp [Oset, Set.mem_preimage, Set.mem_pi]
    rw [hrewrite]
    exact (isOpen_set_pi hI fun w _ ↦ (B w).isOpen).preimage
      (RestrictedProduct.continuous_coe (R := K) (A := A))
  have hembed :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal (R := K) (A := A) hAopen hS
  let Hadd : AddSubgroup R :=
    { carrier := {x | ∀ w, x w ∈ D w}
      zero_mem' := fun w ↦ by
        rw [RestrictedProduct.zero_apply]
        exact (D w).zero_mem
      add_mem' := fun {a b} ha hb w ↦ by
        rw [RestrictedProduct.add_apply]
        exact (D w).add_mem (ha w) (hb w)
      neg_mem' := fun {a} ha w ↦ by
        rw [RestrictedProduct.neg_apply]
        exact (D w).neg_mem (ha w) }
  have hEq : (Hadd : Set R) = incl '' Oset := by
    ext x
    constructor
    · intro hx
      have hxA : ∀ w, x w ∈ A w := by
        intro w
        by_cases hw : w ∈ I
        · have hxD : x w ∈ (B w).toAddSubgroup ⊓ Oadd w := by simpa [D, hw] using hx w
          rw [AddSubgroup.mem_inf] at hxD
          simpa [Oadd, A, Subring.coe_toAddSubgroup, ValuationSubring.mem_toSubring] using hxD.2
        · have hxD : x w ∈ Oadd w := by simpa [D, hw] using hx w
          simpa [Oadd, A, Subring.coe_toAddSubgroup, ValuationSubring.mem_toSubring] using hxD
      obtain ⟨y, hy⟩ := RestrictedProduct.exists_inclusion_eq_of_eventually K A hS
        (Filter.Eventually.of_forall hxA)
      refine ⟨y, ?_, hy⟩
      intro w hw
      have hxD : x w ∈ (B w).toAddSubgroup ⊓ Oadd w := by simpa [D, hw] using hx w
      rw [AddSubgroup.mem_inf] at hxD
      rw [← hy] at hxD
      rw [RestrictedProduct.inclusion_apply] at hxD
      exact hxD.1
    · rintro ⟨y, hy, rfl⟩
      intro w
      by_cases hw : w ∈ I
      · rw [RestrictedProduct.inclusion_apply]
        have hyA : y w ∈ A w :=
          (Filter.eventually_principal.mp y.2) w (Set.mem_univ w)
        simp only [D, hw, dif_pos, AddSubgroup.mem_inf]
        refine ⟨hy w hw, ?_⟩
        simpa [Oadd, A, Subring.coe_toAddSubgroup, ValuationSubring.mem_toSubring] using hyA
      · rw [RestrictedProduct.inclusion_apply]
        have hyA : y w ∈ A w :=
          (Filter.eventually_principal.mp y.2) w (Set.mem_univ w)
        simp only [D, hw, dif_neg]
        simpa [Oadd, A, Subring.coe_toAddSubgroup, ValuationSubring.mem_toSubring] using hyA
  have hcoe : (Hadd.toSubgroup : Set (Multiplicative R)) = (Hadd : Set R) := by
    ext z
    rw [SetLike.mem_coe, Multiplicative.mem_toSubgroup]
    rfl
  refine ⟨Hadd.toSubgroup, ?_, ?_⟩
  · rw [hcoe, hEq]
    exact hembed.isOpenMap _ hOopen
  · intro x hx
    rw [hcoe, hEq] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hyW : ((y : Runiv) : Π w, K w) ∈ I.pi fun w ↦ t w := by
      intro w hw
      exact hB w (hy w hw)
    have hyU : Multiplicative.ofAdd (incl y) ∈ U := hWsub (hsub hyW)
    have hxy : Multiplicative.ofAdd (incl y) = incl y := Multiplicative.ext rfl
    rw [← hxy]
    exact hyU

/-- Paper: Proposition 2.1.2.8(1), p. 65. Both Schwartz–Bruhat spaces carry
the finest locally convex topology. -/
theorem finiteProduct_tailSchwartz_finestTopology (S T : Finset (Places(F))) :
    (inferInstance : TopologicalSpace ℬ((FinitePlaceProduct F S))) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex ℬ((FinitePlaceProduct F S)))) ∧
    (inferInstance : TopologicalSpace ℬ(FiniteAdeleTail F T)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex ℬ(FiniteAdeleTail F T))) := by
  constructor
  · let G := Multiplicative (FinitePlaceProduct F S)
    haveI : T2Space G := by
      change T2Space (FinitePlaceProduct F S)
      infer_instance
    haveI : IsTopologicalGroup G := inferInstance
    refine schwartzBruhat_eq_finestLocallyConvex_of_stageFiniteDim fun a e ↦
      bruhatStage_finiteDimensional_of_compactDiscrete a e
        (bruhatSubgroup_compact_of_mem_compactSubgroup
          (fun ⦃s⦄ hs ↦ finitePlaceProduct_mem_compactSubgroup F S hs) a)
        (bruhatQuotient_discrete_of_smallSubgroups
          (fun U hU ↦ finitePlaceProduct_smallSubgroups F S hU) a e)
  · let G := Multiplicative (FiniteAdeleTail F T)
    haveI : IsTopologicalRing (FiniteAdeleTail F T) :=
      RestrictedProduct.isTopologicalRing (fun w : {w // w ∉ T} ↦ w.val.adicCompletion F)
    haveI : T2Space G := by
      change T2Space (FiniteAdeleTail F T)
      infer_instance
    haveI : IsTopologicalGroup G := inferInstance
    refine schwartzBruhat_eq_finestLocallyConvex_of_stageFiniteDim fun a e ↦
      bruhatStage_finiteDimensional_of_compactDiscrete a e
        (bruhatSubgroup_compact_of_mem_compactSubgroup
          (fun ⦃s⦄ hs ↦ finiteAdeleTail_mem_compactSubgroup F T hs) a)
        (bruhatQuotient_discrete_of_smallSubgroups
          (fun U hU ↦ finiteAdeleTail_smallSubgroups F T hU) a e)

/-- A countable-dimensional space with the finest locally convex topology is strict LF,
using finite spans of a basis. -/
private theorem strictLF_of_countableRank_of_finestTopology
    (E : Type*) [AddCommGroup E] [Module ℂ E] [t : TopologicalSpace E]
    (hRank : Module.rank ℂ E ≤ ℵ₀)
    (hTop : t = (inferInstance : TopologicalSpace (FinestLocallyConvex E))) :
    IsStrictLFSpace E := by
  let b := Module.Free.chooseBasis ℂ E
  let : Countable (Module.Free.ChooseBasisIndex ℂ E) :=
    Cardinal.mk_le_aleph0_iff.mp (b.mk_eq_rank''.trans_le hRank)
  exact Eq.mpr (congrArg (fun t' ↦ @IsStrictLFSpace E _ _ t') hTop)
    (finestLocallyConvex_strictLF_of_countable_span E (countable_range b) b.span_eq)

/-- Paper: Proposition 2.1.2.8(1), p. 65. Both Schwartz–Bruhat spaces are strict LF-spaces.
Their bornological property is stated in `schwartzBruhat_bornological`. -/
theorem finiteProduct_tailSchwartz_strictLF (S T : Finset (Places(F))) :
    IsStrictLFSpace ℬ((FinitePlaceProduct F S)) ∧ IsStrictLFSpace ℬ(FiniteAdeleTail F T) := by
  have hRank := finiteProduct_tailSchwartz_countableRank F S T
  have hTop := finiteProduct_tailSchwartz_finestTopology F S T
  exact ⟨strictLF_of_countableRank_of_finestTopology ℬ((FinitePlaceProduct F S)) hRank.1 hTop.1,
    strictLF_of_countableRank_of_finestTopology ℬ(FiniteAdeleTail F T) hRank.2 hTop.2⟩

/-- Paper: Proposition 2.1.2.8(2), p. 65. The finite-product and tail Schwartz–Bruhat
spaces are complete. -/
theorem finiteProduct_tailSchwartz_complete (S T : Finset (Places(F))) :
    CompleteSpace ℬ((FinitePlaceProduct F S)) ∧ CompleteSpace ℬ(FiniteAdeleTail F T) := by sorry

/-- Paper: Proposition 2.1.2.8(2), p. 65. Both Schwartz–Bruhat spaces are Hausdorff,
locally convex and nuclear. -/
theorem finiteProduct_tailSchwartz_nuclear (S T : Finset (Places(F))) :
    IsNuclearTVS.{v} ℬ((FinitePlaceProduct F S)) ∧ IsNuclearTVS.{v} ℬ(FiniteAdeleTail F T) := by sorry

/-- Paper: Proposition 2.1.2.8(2), p. 65. Both Schwartz–Bruhat spaces are Montel. -/
theorem finiteProduct_tailSchwartz_montel (S T : Finset (Places(F))) :
    (BarrelledSpace ℂ ℬ((FinitePlaceProduct F S)) ∧ MontelSpace ℂ ℬ((FinitePlaceProduct F S))) ∧
      (BarrelledSpace ℂ ℬ(FiniteAdeleTail F T) ∧ MontelSpace ℂ ℬ(FiniteAdeleTail F T)) := by
  have of_finest (E : Type u) [AddCommGroup E] [Module ℂ E] (t : TopologicalSpace E)
      (ht : t = (inferInstance : TopologicalSpace (FinestLocallyConvex E))) :
      @BarrelledSpace ℂ E _ _ _ t ∧ @MontelSpace ℂ E _ _ _ t :=
    Eq.mpr (congrArg (fun t' ↦ @BarrelledSpace ℂ E _ _ _ t' ∧ @MontelSpace ℂ E _ _ _ t') ht)
      ⟨finestLocallyConvex_barrelled E, finestLocallyConvex_montel E⟩
  have hTop := finiteProduct_tailSchwartz_finestTopology F S T
  exact ⟨of_finest ℬ((FinitePlaceProduct F S)) _ hTop.1,
    of_finest ℬ(FiniteAdeleTail F T) _ hTop.2⟩

/-- Paper: Proposition 2.1.2.8(2), p. 65. Both strong duals are Fréchet. -/
theorem finiteProduct_tailSchwartz_strongDual_frechet (S T : Finset (Places(F))) :
    IsFrechetTVS (StrongDual ℂ ℬ((FinitePlaceProduct F S))) ∧
      IsFrechetTVS (StrongDual ℂ ℬ(FiniteAdeleTail F T)) := by sorry

/-- Paper: Proposition 2.1.2.8(2), p. 65. Both strong duals are nuclear. -/
theorem finiteProduct_tailSchwartz_strongDual_nuclear (S T : Finset (Places(F))) :
    IsNuclearTVS.{v} (StrongDual ℂ ℬ((FinitePlaceProduct F S))) ∧
      IsNuclearTVS.{v} (StrongDual ℂ ℬ(FiniteAdeleTail F T)) := by sorry

/-- Paper: Proposition 2.1.2.8(3), p. 65. Every linear subspace in either Schwartz–Bruhat
space has a continuous linear retraction. -/
theorem finiteProduct_tailSchwartz_complemented (S T : Finset (Places(F))) :
    (∀ W : Submodule ℂ ℬ((FinitePlaceProduct F S)), W.ClosedComplemented) ∧
      (∀ W : Submodule ℂ ℬ(FiniteAdeleTail F T), W.ClosedComplemented) := by sorry

-- TODO(paper-gap): Remark 2.1.2.9 claims countable dimension under separability
-- for arbitrary locally profinite groups. A separable uncountable product of
-- two-element groups has uncountably many linearly independent coordinate characters.

section UnitAction

variable {R : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/-- Paper: (2.1.2.2), p. 65. Pullback by multiplication by an inverse unit
preserves additive Schwartz–Bruhat functions.
Deviation: The common membership check is stated for any commutative topological ring. -/
theorem schwartzBruhat_unitTranslate_mem (g : Rˣ) (f : ℬ(R)) :
    (fun x : Multiplicative R ↦ f (Multiplicative.ofAdd ((↑g⁻¹ : R) * x.toAdd))) ∈
      schwartzBruhatSubmodule (Multiplicative R) := by sorry

/-- Paper: (2.1.2.2), p. 65. A unit acts on a Schwartz–Bruhat function by
pullback along multiplication by its inverse. -/
def schwartzBruhatUnitTranslate (g : Rˣ) (f : ℬ(R)) : ℬ(R) :=
  ⟨_, schwartzBruhat_unitTranslate_mem g f⟩

/-- Paper: (2.1.2.2), p. 65. At an input x the transformed function has
the original value at the product of the inverse unit and x. -/
theorem schwartzBruhatUnitTranslate_apply (g : Rˣ) (f : ℬ(R)) (x : R) :
    schwartzBruhatUnitTranslate g f (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd ((↑g⁻¹ : R) * x)) := rfl

end UnitAction

/-- Paper: Lemma 2.1.2.10(1), p. 66. Local unit translations of a converging
sequence converge uniformly over the integer units, for each continuous seminorm.
Deviation: Uniform convergence is expressed by its eventual epsilon bounds. -/
theorem finitePlaceSchwartz_unitTranslate_tendsto (w : Places(F))
    (f : ℕ → ℬ(w.adicCompletion F)) (l : ℬ(w.adicCompletion F))
    (hf : Tendsto f atTop (𝓝 l)) (p : Seminorm ℂ ℬ(w.adicCompletion F)) (hp : Continuous p)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : (w.adicCompletion F)ˣ,
      (↑g : w.adicCompletion F) ∈ w.adicCompletionIntegers F →
      (↑g⁻¹ : w.adicCompletion F) ∈ w.adicCompletionIntegers F →
      p (schwartzBruhatUnitTranslate g (f n - l)) < ε := by sorry

/-- Paper: Lemma 2.1.2.10(2), p. 66. For a finite product of local fields,
convergence is uniform over the product of integer unit groups.
Deviation: The limit used in the displayed formula is made explicit. -/
theorem finiteProductSchwartz_unitTranslate_tendsto (S : Finset (Places(F)))
    (f : ℕ → ℬ((FinitePlaceProduct F S))) (l : ℬ((FinitePlaceProduct F S)))
    (hf : Tendsto f atTop (𝓝 l)) (p : Seminorm ℂ ℬ((FinitePlaceProduct F S))) (hp : Continuous p)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : (FinitePlaceProduct F S)ˣ,
      (∀ w : S, (g.val w) ∈ w.val.adicCompletionIntegers F ∧
        (g.inv w) ∈ w.val.adicCompletionIntegers F) →
      p (schwartzBruhatUnitTranslate g (f n - l)) < ε := by sorry

/-- Paper: Lemma 2.1.2.10(3), p. 66. For a restricted product of local fields,
convergence is uniform over the full product of integer unit groups.
Deviation: The proof and Remark 2.1.2.12 specify the unit group in (2.1.2.5).
The continuous seminorm used in the displayed formula is made explicit. -/
theorem finiteAdeleTailSchwartz_unitTranslate_tendsto (S : Finset (Places(F)))
    (f : ℕ → ℬ(FiniteAdeleTail F S)) (l : ℬ(FiniteAdeleTail F S))
    (hf : Tendsto f atTop (𝓝 l)) (p : Seminorm ℂ ℬ(FiniteAdeleTail F S)) (hp : Continuous p)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ g : (FiniteAdeleTail F S)ˣ,
      (∀ w : {w : Places(F) // w ∉ S}, (g.val w) ∈ w.val.adicCompletionIntegers F ∧
        (g.inv w) ∈ w.val.adicCompletionIntegers F) →
      p (schwartzBruhatUnitTranslate g (f n - l)) < ε := by sorry

-- TODO(later): needs §4.3.3 and §D.2 for the application in Remark 2.1.2.12.
-- TODO(paper-gap): The remark also allows arbitrary closed subspaces for the
-- quotient action. Such a subspace must be invariant under the acting group.

end FinitePlaces

section Adeles

variable (F : Type u) [Field F] [NumberField F]

/-- Paper: Lemma 2.1.3.2(1), p. 68. The finite and global adelic Schwartz–Bruhat
spaces are strict LF-spaces.
Deviation: The nuclearity statements below imply that every strict Fréchet
presentation has nuclear stages by Remark C.1.5.12. -/
theorem adeleSchwartz_strictLF :
    IsStrictLFSpace ℬ(𝔸ᶠ[F]) ∧ IsStrictLFSpace ℬ(𝔸[F]) := by sorry

/-- Paper: Lemma 2.1.3.2(1), p. 68. The finite and global adelic Schwartz–Bruhat
spaces are complete. -/
theorem adeleSchwartz_complete :
    CompleteSpace ℬ(𝔸ᶠ[F]) ∧ CompleteSpace ℬ(𝔸[F]) := by sorry

/-- Paper: Lemma 2.1.3.2(1), p. 68. The finite and global adelic Schwartz–Bruhat
spaces are Hausdorff, locally convex and nuclear. -/
theorem adeleSchwartz_nuclear :
    IsNuclearTVS.{v} ℬ(𝔸ᶠ[F]) ∧ IsNuclearTVS.{v} ℬ(𝔸[F]) := by sorry

/-- Paper: Lemma 2.1.3.2(1), p. 68. Both adelic Schwartz–Bruhat spaces are Montel. -/
theorem adeleSchwartz_montel :
    (BarrelledSpace ℂ ℬ(𝔸ᶠ[F]) ∧ MontelSpace ℂ ℬ(𝔸ᶠ[F])) ∧
      (BarrelledSpace ℂ ℬ(𝔸[F]) ∧ MontelSpace ℂ ℬ(𝔸[F])) := by sorry

/-- Paper: Lemma 2.1.3.2(1), p. 68. Both adelic strong duals are complete. -/
theorem adeleSchwartz_strongDual_complete :
    CompleteSpace (StrongDual ℂ ℬ(𝔸ᶠ[F])) ∧
      CompleteSpace (StrongDual ℂ ℬ(𝔸[F])) := by sorry

/-- Paper: Lemma 2.1.3.2(1), p. 68. Both adelic strong duals are Hausdorff,
locally convex and nuclear. -/
theorem adeleSchwartz_strongDual_nuclear :
    IsNuclearTVS.{v} (StrongDual ℂ ℬ(𝔸ᶠ[F])) ∧
      IsNuclearTVS.{v} (StrongDual ℂ ℬ(𝔸[F])) := by sorry

/-- Paper: Lemma 2.1.3.2(1), p. 68. Both adelic strong duals are Montel. -/
theorem adeleSchwartz_strongDual_montel :
    (BarrelledSpace ℂ (StrongDual ℂ ℬ(𝔸ᶠ[F])) ∧ MontelSpace ℂ (StrongDual ℂ ℬ(𝔸ᶠ[F]))) ∧
      (BarrelledSpace ℂ (StrongDual ℂ ℬ(𝔸[F])) ∧ MontelSpace ℂ (StrongDual ℂ ℬ(𝔸[F]))) := by sorry

/-- Paper: Lemma 2.1.3.2(1), p. 68. The strong dual of the finite adelic
Schwartz–Bruhat space is Fréchet. -/
theorem finiteAdeleSchwartz_strongDual_frechet :
    IsFrechetTVS (StrongDual ℂ ℬ(𝔸ᶠ[F])) := by sorry

/-- Paper: Lemma 2.1.3.2(2), p. 68. The canonical map from the uncompleted
inductive tensor product to global adelic Schwartz–Bruhat functions is an
isomorphism. On pure tensors the map multiplies the two evaluations. -/
theorem adeleSchwartz_inductiveTensor_equiv :
    ∃ e : InductiveTensor ℬ(InfiniteAdeleRing F) ℬ(𝔸ᶠ[F]) ≃L[ℂ] ℬ(𝔸[F]),
      ∀ (f : ℬ(InfiniteAdeleRing F)) (g : ℬ(𝔸ᶠ[F])) (x : 𝔸[F]),
        e (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x) =
          f (Multiplicative.ofAdd x.1) * g (Multiplicative.ofAdd x.2) := by sorry

/-- Paper: Lemma 2.1.3.2(2), p. 68. The inductive tensor product of the
Archimedean and finite adelic Schwartz–Bruhat spaces is complete. -/
theorem adeleSchwartz_inductiveTensor_complete :
    CompleteSpace (InductiveTensor ℬ(InfiniteAdeleRing F) ℬ(𝔸ᶠ[F])) := by sorry

-- ERRATA F11: Subgroup indicators are even in each finite coordinate.
-- The compact open subsets used below allow the coset indicators needed in the proof.

/-- Paper: Lemma 2.1.3.2(3), p. 68. Every adelic Schwartz–Bruhat function is a
finite linear combination of Archimedean Schwartz functions times finite adelic
rectangle indicators. The rectangle is integral at all but finitely many places.
Deviation: The local sets are compact open subsets, as in the proof on p. 70. -/
theorem adeleSchwartz_eq_sum_compactOpen_rectangles (f : ℬ(𝔸[F])) :
    ∃ (r : ℕ) (c : Fin r → ℂ) (arch : Fin r → ℬ(InfiniteAdeleRing F))
        (K : Fin r → (v : Places(F)) → Set (v.adicCompletion F)) (φ : Fin r → ℬ(𝔸[F])),
      1 ≤ r ∧
      (∀ i, (∀ v, IsCompact (K i v) ∧ IsOpen (K i v)) ∧
        (∀ᶠ v in cofinite, K i v = (v.adicCompletionIntegers F : Set (v.adicCompletion F))) ∧
        ∀ x : 𝔸[F], φ i (Multiplicative.ofAdd x) =
          arch i (Multiplicative.ofAdd x.1) *
            Set.indicator {y : 𝔸ᶠ[F] | ∀ v, y v ∈ K i v} (fun _ ↦ (1 : ℂ)) x.2) ∧
      f = ∑ i, c i • φ i := by sorry

-- TODO(paper-gap): The proof on p. 69 cites “Lemma ??” for second countability
-- and Proposition 2.1.2.8(6), which has only three parts.

/-- Paper: Remark 2.1.3.3, p. 69. The identity from the inductive to the
projective tensor product of the adelic factors is a continuous bijection
whose topology is strictly weakened. -/
theorem adeleSchwartz_inductiveTensor_not_isEmbedding :
    ¬ @IsEmbedding (InductiveTensor ℬ(InfiniteAdeleRing F) ℬ(𝔸ᶠ[F]))
      (ProjectiveTensor ℬ(InfiniteAdeleRing F) ℬ(𝔸ᶠ[F])) _ _ id := by sorry

/-- Paper: Remark 2.1.3.4, p. 70. The injective and projective tensor topologies
on the tensor product of the adelic factors coincide. -/
theorem adeleSchwartz_injectiveTensor_projectiveTensor :
    @IsHomeomorph (InjectiveTensor ℬ(InfiniteAdeleRing F) ℬ(𝔸ᶠ[F]))
      (ProjectiveTensor ℬ(InfiniteAdeleRing F) ℬ(𝔸ᶠ[F])) _ _ id := by sorry

end Adeles

section SAdeles

variable (F : Type u) [Field F] [NumberField F]

local notation "𝒮(" S ")" => ℬ(SAdeleRing F S)

/-- Paper: (2.1.4.5), p. 71. The complementary projection keeps exactly the
finite coordinates outside the chosen set of places. -/
def finiteAdeleTailProjection (S : Finset (Places(F))) (x : 𝔸ᶠ[F]) : FiniteAdeleTail F S :=
  RestrictedProduct.mk (fun w ↦ x w.val)
    (Subtype.val_injective.tendsto_cofinite.eventually x.cofinite_mem_adicCompletionIntegers)

/-- Paper: (2.1.4.5), p. 71. The complementary projection evaluates to the
original coordinate at every omitted place. -/
theorem finiteAdeleTailProjection_apply (S : Finset (Places(F))) (x : 𝔸ᶠ[F])
    (w : {w : Places(F) // w ∉ S}) :
    finiteAdeleTailProjection F S x w = x w.val := by
  rfl

/-- Paper: Proposition 2.1.4.1(1), p. 71. The inductive tensor product of the
Archimedean factor with the finite tensor product of the local factors is
canonically the Schwartz–Bruhat space of the S-adeles.
Deviation: The finite tensor product uses its finest locally convex topology,
which is its inductive tensor topology by Lemma C.2.5.2. -/
theorem sAdeleSchwartz_inductiveTensor_equiv (S : Finset (Places(F))) :
    let V := FinestLocallyConvex (⨂[ℂ] w : S, ℬ(w.val.adicCompletion F))
    ∃ e : InductiveTensor ℬ(InfiniteAdeleRing F) V ≃L[ℂ] 𝒮(S),
      ∀ (f : ℬ(InfiniteAdeleRing F)) (g : ∀ w : S, ℬ(w.val.adicCompletion F))
        (x : SAdeleRing F S),
        e (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd x) =
          f (Multiplicative.ofAdd x.1) * ∏ w : S, g w (Multiplicative.ofAdd (x.2 w)) := by sorry

/-- Paper: Proposition 2.1.4.1(2), p. 71. The S-adelic Schwartz–Bruhat space is a strict
LF-space.
Deviation: Nuclearity below implies that its strict Fréchet stages are nuclear
by Remark C.1.5.12. -/
theorem sAdeleSchwartz_strictLF (S : Finset (Places(F))) :
    IsStrictLFSpace 𝒮(S) := by sorry

/-- Paper: Proposition 2.1.4.1(2), p. 71. The S-adelic Schwartz–Bruhat space is complete. -/
theorem sAdeleSchwartz_complete (S : Finset (Places(F))) :
    CompleteSpace 𝒮(S) := by sorry

/-- Paper: Proposition 2.1.4.1(2), p. 71. The S-adelic Schwartz–Bruhat space is
Hausdorff, locally convex and nuclear. -/
theorem sAdeleSchwartz_nuclear (S : Finset (Places(F))) :
    IsNuclearTVS.{v} 𝒮(S) := by sorry

/-- Paper: Proposition 2.1.4.1(2), p. 71. The S-adelic Schwartz–Bruhat space is Montel. -/
theorem sAdeleSchwartz_montel (S : Finset (Places(F))) :
    BarrelledSpace ℂ 𝒮(S) ∧ MontelSpace ℂ 𝒮(S) := by sorry

/-- Paper: Proposition 2.1.4.1(2), p. 71. The strong dual of the S-adelic
Schwartz–Bruhat space is complete. -/
theorem sAdeleSchwartz_strongDual_complete (S : Finset (Places(F))) :
    CompleteSpace (StrongDual ℂ 𝒮(S)) := by sorry

/-- Paper: Proposition 2.1.4.1(2), p. 71. The strong dual of the S-adelic
Schwartz–Bruhat space is Hausdorff, locally convex and nuclear. -/
theorem sAdeleSchwartz_strongDual_nuclear (S : Finset (Places(F))) :
    IsNuclearTVS.{v} (StrongDual ℂ 𝒮(S)) := by sorry

/-- Paper: Proposition 2.1.4.1(2), p. 71. The strong dual of the S-adelic
Schwartz–Bruhat space is Montel. -/
theorem sAdeleSchwartz_strongDual_montel (S : Finset (Places(F))) :
    BarrelledSpace ℂ (StrongDual ℂ 𝒮(S)) ∧ MontelSpace ℂ (StrongDual ℂ 𝒮(S)) := by sorry

open Classical in
/-- Paper: (2.1.4.3), p. 71. The extension formula gives a linear map into
the space of all functions, before restricting its range to Schwartz–Bruhat functions. -/
def sAdeleSchwartzTransitionFunctions {S T : Finset (Places(F))} (hST : S ⊆ T) :
    𝒮(S) →ₗ[ℂ] (Multiplicative (SAdeleRing F T) → ℂ) :=
  (LinearMap.pi fun x : Multiplicative (SAdeleRing F T) ↦
    (if ∀ w : T, w.val ∉ S → x.toAdd.2 w ∈ w.val.adicCompletionIntegers F
      then (1 : ℂ) else 0) •
      LinearMap.proj (Multiplicative.ofAdd
        (x.toAdd.1, fun w : S ↦ x.toAdd.2 ⟨w.val, hST w.property⟩))).comp
    (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype

/-- Paper: (2.1.4.3), p. 71. Multiplying the pulled-back function by the
integer-coordinate indicators at newly selected places gives a Schwartz–Bruhat function. -/
theorem sAdeleSchwartz_transition_mem {S T : Finset (Places(F))} (hST : S ⊆ T) (f : 𝒮(S)) :
    sAdeleSchwartzTransitionFunctions F hST f ∈
      schwartzBruhatSubmodule (Multiplicative (SAdeleRing F T)) := by sorry

/-- Paper: (2.1.4.2)–(2.1.4.3), p. 71. The transition map keeps the old variables
and multiplies by the indicator that every new place's coordinate is integral. -/
def sAdeleSchwartzTransition {S T : Finset (Places(F))} (hST : S ⊆ T) :
    𝒮(S) →ₗ[ℂ] 𝒮(T) :=
  (sAdeleSchwartzTransitionFunctions F hST).codRestrict
    (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F T)))
    (sAdeleSchwartz_transition_mem F hST)

open Classical in
/-- Paper: (2.1.4.3), p. 71. The transition map evaluates to the old function on
the old coordinates if all new coordinates are integral, and to zero otherwise. -/
theorem sAdeleSchwartzTransition_apply {S T : Finset (Places(F))} (hST : S ⊆ T)
    (f : 𝒮(S)) (x : SAdeleRing F T) :
    sAdeleSchwartzTransition F hST f (Multiplicative.ofAdd x) =
      if ∀ w : T, w.val ∉ S → x.2 w ∈ w.val.adicCompletionIntegers F then
        f (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩))
      else 0 := by
  change (if _ then (1 : ℂ) else 0) • f (Multiplicative.ofAdd
    (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩)) = _
  simp only [toAdd_ofAdd]
  split_ifs <;> simp

/-- Paper: Proposition 2.1.4.1(3)–(4), p. 71. The transition map is a topological
embedding, so it is continuous and injective and induces the intrinsic topology. -/
theorem sAdeleSchwartzTransition_isEmbedding {S T : Finset (Places(F))} (hST : S ⊆ T) :
    IsEmbedding (sAdeleSchwartzTransition F hST) := by sorry

/-- Paper: Proposition 2.1.4.1(1), p. 71. Enlarging the place set inserts the
integer indicators in a pure tensor. The functions realizing the two tensors
are related by the canonical transition map. -/
theorem sAdeleSchwartzTransition_pure {S T : Finset (Places(F))} (hST : S ⊆ T)
    (a : ℬ(InfiniteAdeleRing F)) (g : ∀ w : T, ℬ(w.val.adicCompletion F))
    (hg : ∀ (w : T), w.val ∉ S → ∀ (y : w.val.adicCompletion F),
      g w (Multiplicative.ofAdd y) =
        Set.indicator (w.val.adicCompletionIntegers F : Set (w.val.adicCompletion F))
          (fun _ ↦ 1) y)
    (f : 𝒮(S))
    (hf : ∀ x : SAdeleRing F S, f (Multiplicative.ofAdd x) =
      a (Multiplicative.ofAdd x.1) * ∏ w : S,
        g ⟨w.val, hST w.property⟩ (Multiplicative.ofAdd (x.2 w)))
    (x : SAdeleRing F T) :
    sAdeleSchwartzTransition F hST f (Multiplicative.ofAdd x) =
      a (Multiplicative.ofAdd x.1) * ∏ w : T, g w (Multiplicative.ofAdd (x.2 w)) := by
  rw [sAdeleSchwartzTransition_apply]
  split_ifs with h
  · rw [hf]
    congr 1
    refine Fintype.prod_of_injective (fun w : S ↦ (⟨w.val, hST w.property⟩ : T))
      (fun u v huv ↦ Subtype.ext (by simpa using huv)) _ _ (fun w hw ↦ ?_) fun _ ↦ rfl
    have hwS : w.val ∉ S := fun hS ↦ hw ⟨⟨w.val, hS⟩, rfl⟩
    rw [hg w hwS, Set.indicator_of_mem (h w hwS)]
  · push Not at h
    obtain ⟨w, hwS, hx⟩ := h
    rw [Finset.prod_eq_zero (Finset.mem_univ w)
      (by rw [hg w hwS, Set.indicator_of_notMem hx]), mul_zero]

open Classical in
/-- Paper: (2.1.4.5), p. 71. The global extension formula gives a linear map into
the space of all functions, before restricting its range to Schwartz–Bruhat functions. -/
def sAdeleSchwartzToGlobalFunctions (S : Finset (Places(F))) :
    𝒮(S) →ₗ[ℂ] (Multiplicative 𝔸[F] → ℂ) :=
  (LinearMap.pi fun x : Multiplicative 𝔸[F] ↦
    (if ∀ w : Places(F), w ∉ S → x.toAdd.2 w ∈ w.adicCompletionIntegers F
      then (1 : ℂ) else 0) • LinearMap.proj (Multiplicative.ofAdd (adeleProjection F S x.toAdd))).comp
    (schwartzBruhatSubmodule (Multiplicative (SAdeleRing F S))).subtype

/-- Paper: (2.1.4.5), p. 71. The pullback of an S-adelic test function
multiplied by the indicator of integral coordinates outside S is Schwartz–Bruhat. -/
theorem sAdeleSchwartz_toGlobal_mem (S : Finset (Places(F))) (f : 𝒮(S)) :
    sAdeleSchwartzToGlobalFunctions F S f ∈
      schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by sorry

/-- Paper: (2.1.4.5), p. 71. The global inclusion extends an S-adelic
function by the indicator of the product of integer rings outside S. -/
def sAdeleSchwartzToGlobal (S : Finset (Places(F))) : 𝒮(S) →ₗ[ℂ] ℬ(𝔸[F]) :=
  (sAdeleSchwartzToGlobalFunctions F S).codRestrict (schwartzBruhatSubmodule (Multiplicative 𝔸[F]))
    (sAdeleSchwartz_toGlobal_mem F S)

open Classical in
/-- Paper: (2.1.4.5), p. 71. The global inclusion evaluates to the local function
on the retained coordinates when all other coordinates are integral. -/
theorem sAdeleSchwartzToGlobal_apply (S : Finset (Places(F))) (f : 𝒮(S)) (x : 𝔸[F]) :
    sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x) =
      if ∀ w : Places(F), w ∉ S → x.2 w ∈ w.adicCompletionIntegers F then
        f (Multiplicative.ofAdd (adeleProjection F S x))
      else 0 := by
  change (if _ then (1 : ℂ) else 0) • f (Multiplicative.ofAdd (adeleProjection F S x)) = _
  simp only [toAdd_ofAdd]
  split_ifs <;> simp

/-- Paper: Proposition 2.1.4.1(5), p. 71. Each S-local space embeds topologically
in the global Schwartz–Bruhat space by extension with the integer indicator. -/
theorem sAdeleSchwartzToGlobal_isEmbedding (S : Finset (Places(F))) :
    IsEmbedding (sAdeleSchwartzToGlobal F S) := by sorry

/-- Paper: Proposition 2.1.4.1(5), p. 71. The global inclusions are compatible
with the transition maps, so they induce the canonical colimit map. -/
theorem sAdeleSchwartzToGlobal_comp {S T : Finset (Places(F))} (hST : S ⊆ T) :
    (sAdeleSchwartzToGlobal F T).comp (sAdeleSchwartzTransition F hST) =
      sAdeleSchwartzToGlobal F S := by
  refine LinearMap.ext fun f ↦ Subtype.ext (funext fun x ↦ ?_)
  change sAdeleSchwartzToGlobal F T (sAdeleSchwartzTransition F hST f)
      (Multiplicative.ofAdd x.toAdd) = sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd x.toAdd)
  have hp2 : ∀ (U : Finset (Places(F))) (y : 𝔸[F]) (w : U),
      (adeleProjection F U y).2 w = y.2 w.val := fun _ _ _ ↦ rfl
  refine (sAdeleSchwartzToGlobal_apply F T (sAdeleSchwartzTransition F hST f) x.toAdd).trans
    (Eq.trans ?_ (sAdeleSchwartzToGlobal_apply F S f x.toAdd).symm)
  rw [sAdeleSchwartzTransition_apply F hST f (adeleProjection F T x.toAdd)]
  simp only [hp2]
  split_ifs with hT hTS h₁ h₁ h₁
  · congr 2
  · refine absurd (fun w hw ↦ ?_) h₁
    by_cases hwT : w ∈ T
    · simpa only [hp2] using hTS ⟨w, hwT⟩ hw
    · exact hT w hwT
  · exact absurd (fun w hw ↦ by rw [hp2]; exact h₁ w hw) hTS
  · rfl
  · exact absurd (fun w hw ↦ h₁ w fun h ↦ hw (hST h)) hT
  · rfl

/-- Paper: Proposition 2.1.4.1(5), p. 71. Every global Schwartz–Bruhat function
lies in one of the embedded S-local spaces.
Deviation: The algebraic colimit of the injective system is expressed as the
directed union of the images. -/
theorem sAdeleSchwartzToGlobal_exhaustive (f : ℬ(𝔸[F])) :
    ∃ S : Finset (Places(F)), f ∈ LinearMap.range (sAdeleSchwartzToGlobal F S) := by sorry

/-- Paper: Proposition 2.1.4.1(5), p. 71. The global Schwartz–Bruhat topology is
the locally convex final topology of the S-local embeddings.
Deviation: Together with the directed union of the images, this states the
canonical colimit isomorphism on the global carrier. -/
theorem sAdeleSchwartzToGlobal_finalTopology :
    (inferInstance : TopologicalSpace ℬ(𝔸[F])) =
      locallyConvexFinalTopology (sAdeleSchwartzToGlobal F) := by sorry

/-- Paper: Corollary 2.1.4.2, p. 72. Multiplying S-local and complementary
test functions identifies their inductive tensor product with global test functions. -/
theorem sAdeleTailSchwartz_inductiveTensor_equiv (S : Finset (Places(F))) :
    ∃ e : InductiveTensor 𝒮(S) ℬ(FiniteAdeleTail F S) ≃L[ℂ] ℬ(𝔸[F]),
      ∀ (f : 𝒮(S)) (g : ℬ(FiniteAdeleTail F S)) (x : 𝔸[F]),
        e (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x) =
          f (Multiplicative.ofAdd (adeleProjection F S x)) *
            g (Multiplicative.ofAdd (finiteAdeleTailProjection F S x.2)) := by sorry

open Classical in
/-- Paper: Corollary 2.1.4.2, p. 72. Multiplication of test functions in the old
and new variables identifies their inductive tensor product with the enlarged S-local space. -/
theorem sAdeleDifferenceSchwartz_inductiveTensor_equiv
    {S T : Finset (Places(F))} (hST : S ⊆ T) :
    ∃ e : InductiveTensor 𝒮(S) ℬ(FinitePlaceProduct F (T \ S)) ≃L[ℂ] 𝒮(T),
      ∀ (f : 𝒮(S)) (g : ℬ(FinitePlaceProduct F (T \ S))) (x : SAdeleRing F T),
        e (f ⊗ₜ[ℂ] g) (Multiplicative.ofAdd x) =
          f (Multiplicative.ofAdd (x.1, fun w : S ↦ x.2 ⟨w.val, hST w.property⟩)) *
            g (Multiplicative.ofAdd (fun w : ↥(T \ S) ↦ x.2 ⟨w.val, (Finset.mem_sdiff.mp w.property).1⟩)) :=
  by sorry

/-- Paper: Corollary 2.1.4.2, p. 72. The inductive tensor product of the
S-adelic and complementary Schwartz–Bruhat spaces is complete. -/
theorem sAdeleTailSchwartz_inductiveTensor_complete (S : Finset (Places(F))) :
    CompleteSpace (InductiveTensor 𝒮(S) ℬ(FiniteAdeleTail F S)) := by sorry

open Classical in
/-- Paper: Corollary 2.1.4.2, p. 72. The inductive tensor product for the
old and added places is complete. -/
theorem sAdeleDifferenceSchwartz_inductiveTensor_complete (S T : Finset (Places(F)))
    (_hST : S ⊆ T) :
    CompleteSpace (InductiveTensor 𝒮(S) ℬ(FinitePlaceProduct F (T \ S))) := by sorry

-- TODO(paper-gap): Lemma 2.1.4.3(1) cites (2.1.4.4) for the complemented image.
-- The image in the projection statement is that of the stage map (2.1.4.5).
-- The proof also switches from the inductive to the projective tensor topology
-- when identifying the image, although Corollary 2.1.4.2 uses the inductive topology.

/-- Paper: Lemma 2.1.4.3(1), p. 73. Each global stage inclusion has a continuous
projection onto its range, acting as the identity there and idempotent on the whole space. -/
theorem sAdeleSchwartzToGlobal_projection (S : Finset (Places(F))) :
    ∃ P : ℬ(𝔸[F]) →L[ℂ] ℬ(𝔸[F]),
      LinearMap.range P.toLinearMap = LinearMap.range (sAdeleSchwartzToGlobal F S) ∧
      P.toLinearMap.comp (sAdeleSchwartzToGlobal F S) = sAdeleSchwartzToGlobal F S ∧
      P.comp P = P := by sorry

/-- Paper: Lemma 2.1.4.3(2), p. 73. A global projection onto the S-stage
restricts to an idempotent projection on each larger stage, with the S-stage as its image. -/
theorem sAdeleSchwartz_projection_factors {S T : Finset (Places(F))} (hST : S ⊆ T)
    (P : ℬ(𝔸[F]) →L[ℂ] ℬ(𝔸[F]))
    (hRange : LinearMap.range P.toLinearMap = LinearMap.range (sAdeleSchwartzToGlobal F S))
    (hFix : P.toLinearMap.comp (sAdeleSchwartzToGlobal F S) = sAdeleSchwartzToGlobal F S) :
    ∃ Q : 𝒮(T) →L[ℂ] 𝒮(T),
      (sAdeleSchwartzToGlobal F T).comp Q.toLinearMap =
        P.toLinearMap.comp (sAdeleSchwartzToGlobal F T) ∧
      LinearMap.range Q.toLinearMap = LinearMap.range (sAdeleSchwartzTransition F hST) ∧
      Q.comp Q = Q := by sorry

/-- Paper: Lemma 2.1.4.3(2), p. 73. The image of a transition map admits a
continuous linear retraction. -/
theorem sAdeleSchwartzTransition_complemented {S T : Finset (Places(F))} (hST : S ⊆ T) :
    (LinearMap.range (sAdeleSchwartzTransition F hST)).ClosedComplemented := by sorry

-- TODO(paper-gap): Equation (2.1.4.13) equates maps with different codomains.
-- The preceding factorization and the compatible global inclusions identify
-- the transition map that is missing on its left side.

/-- Paper: Lemma 2.1.4.3(3), p. 73. Stage projections factoring the same global
projection commute with enlargement of the containing stage.
Deviation: The left side of (2.1.4.13) is composed with the transition to the
larger codomain. This is the compatibility given by the factorization in part (2). -/
theorem sAdeleSchwartz_projection_compatible {T U : Finset (Places(F))} (hTU : T ⊆ U)
    (P : ℬ(𝔸[F]) →L[ℂ] ℬ(𝔸[F]))
    (Q : 𝒮(T) →L[ℂ] 𝒮(T)) (R : 𝒮(U) →L[ℂ] 𝒮(U))
    (hQ : (sAdeleSchwartzToGlobal F T).comp Q.toLinearMap =
      P.toLinearMap.comp (sAdeleSchwartzToGlobal F T))
    (hR : (sAdeleSchwartzToGlobal F U).comp R.toLinearMap =
      P.toLinearMap.comp (sAdeleSchwartzToGlobal F U)) :
    (sAdeleSchwartzTransition F hTU).comp Q.toLinearMap =
      R.toLinearMap.comp (sAdeleSchwartzTransition F hTU) := by sorry

/-- Paper: Corollary 2.1.4.4, p. 74. Any net of continuous projections onto the
S-adelic images tends to the identity in the topology of uniform convergence
on von Neumann bounded subsets. -/
theorem sAdeleSchwartz_projections_tendsto
    (P : Finset (Places(F)) → ℬ(𝔸[F]) →L[ℂ] ℬ(𝔸[F]))
    (hRange : ∀ S, LinearMap.range (P S).toLinearMap =
      LinearMap.range (sAdeleSchwartzToGlobal F S))
    (hFix : ∀ S, (P S).toLinearMap.comp (sAdeleSchwartzToGlobal F S) =
      sAdeleSchwartzToGlobal F S) :
    let E := ℬ(𝔸[F])
    let B := {s : Set E | IsVonNBounded ℂ s}
    let e := UniformConvergenceCLM.ofFun (RingHom.id ℂ) E B
    Tendsto (fun S ↦ e (P S)) atTop (𝓝 (e (ContinuousLinearMap.id ℂ E))) := by sorry

end SAdeles

end RiemannMasullo
