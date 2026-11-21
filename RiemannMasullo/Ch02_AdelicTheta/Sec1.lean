module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
public import RiemannMasullo.ForMathlib.Analysis.Distribution.TestFunction
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.PSeries
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Symmetric
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Complete
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.PiL2

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

/-- Paper: Proposition 2.1.1.6, p. 61. Evaluation identifies the Euclidean Schwartz space
with its strong bidual. -/
theorem euclideanSchwartz_reflexive (m : ℕ) :
    let E := SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ
    ∃ e : E ≃L[ℂ] StrongDual ℂ (StrongDual ℂ E), ∀ f L, e f L = L f := by sorry

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

/-- Paper: Proposition 2.1.1.6, p. 61. The strong dual is Montel, meaning it is
barrelled and its closed bounded subsets are compact. -/
theorem euclideanSchwartz_strongDual_montel (m : ℕ) :
    let D := StrongDual ℂ (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)
    BarrelledSpace ℂ D ∧ MontelSpace ℂ D := by sorry

-- TODO(paper-gap): §2.1.1.3 cites Theorem D.1.5.7 with separability in place of
-- second countability. A separable non-second-countable compact abelian group
-- can have a nonnuclear Schwartz–Bruhat space.

/-- Paper: §2.1.1.3, p. 63. The classical Schwartz space on the real line agrees
with the Schwartz–Bruhat space of the additive real group, including its topology. -/
theorem realSchwartzBruhat_equiv :
    ∃ e : SchwartzMap ℝ ℂ ≃L[ℂ] ℬ(ℝ),
      ∀ (f : SchwartzMap ℝ ℂ) (x : ℝ), e f (Multiplicative.ofAdd x) = f x := by sorry

end Euclidean

section FinitePlaces

variable (F : Type u) [Field F] [NumberField F]

/-- Paper: §2.1.2.2, p. 63. The additive Schwartz–Bruhat space of a finite completion
consists exactly of the locally constant, compactly supported functions. -/
theorem mem_finitePlaceSchwartz_iff (w : Places(F)) (f : w.adicCompletion F → ℂ) :
    (∃ g : ℬ(w.adicCompletion F), ∀ x, g (Multiplicative.ofAdd x) = f x) ↔
      IsLocallyConstant f ∧ HasCompactSupport f := by sorry

-- TODO(paper-gap): In Remark 2.1.2.3, continuity of all linear functionals alone
-- does not characterize the finest locally convex topology. The weak topology
-- also makes all those functionals continuous.

/-- Paper: Proposition 2.1.2.4(1), p. 64. The local Schwartz–Bruhat space has countable
complex dimension. -/
theorem finitePlaceSchwartz_countableRank (w : Places(F)) :
    Module.rank ℂ ℬ(w.adicCompletion F) ≤ ℵ₀ := by sorry

/-- Paper: Proposition 2.1.2.4(1), p. 64. The local Schwartz–Bruhat topology
is the finest locally convex topology. -/
theorem finitePlaceSchwartz_finestTopology (w : Places(F)) :
    (inferInstance : TopologicalSpace ℬ(w.adicCompletion F)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex ℬ(w.adicCompletion F))) := by sorry

/-- Paper: Proposition 2.1.2.4(1), p. 64. The local Schwartz–Bruhat space is a strict
LF-space. -/
theorem finitePlaceSchwartz_strictLF (w : Places(F)) :
    IsStrictLFSpace ℬ(w.adicCompletion F) := by sorry

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local Schwartz–Bruhat space is complete. -/
theorem finitePlaceSchwartz_complete (w : Places(F)) :
    CompleteSpace ℬ(w.adicCompletion F) := by sorry

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local Schwartz–Bruhat space is Hausdorff
locally convex and nuclear. -/
theorem finitePlaceSchwartz_nuclear (w : Places(F)) :
    IsNuclearTVS.{v} ℬ(w.adicCompletion F) := by sorry

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local Schwartz–Bruhat space is Montel. -/
theorem finitePlaceSchwartz_montel (w : Places(F)) :
    BarrelledSpace ℂ ℬ(w.adicCompletion F) ∧ MontelSpace ℂ ℬ(w.adicCompletion F) := by sorry

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local strong dual is Fréchet. -/
theorem finitePlaceSchwartz_strongDual_frechet (w : Places(F)) :
    IsFrechetTVS (StrongDual ℂ ℬ(w.adicCompletion F)) := by sorry

/-- Paper: Proposition 2.1.2.4(2), p. 64. The local strong dual is nuclear. -/
theorem finitePlaceSchwartz_strongDual_nuclear (w : Places(F)) :
    IsNuclearTVS.{v} (StrongDual ℂ ℬ(w.adicCompletion F)) := by sorry

/-- Paper: Proposition 2.1.2.4(3), p. 64. Every linear subspace of the local Schwartz–Bruhat
space has a continuous linear retraction. -/
theorem finitePlaceSchwartz_complemented (w : Places(F))
    (W : Submodule ℂ ℬ(w.adicCompletion F)) : W.ClosedComplemented := by sorry

-- TODO(paper-gap): Examples 2.1.2.5–6 assert that every open subset is a finite union
-- of balls. The whole local field is open and noncompact. The assertion applies
-- to compact open subsets, which suffice for the displayed expansion.

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
  sorry

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

/-- Paper: Proposition 2.1.2.8(1), p. 65. The finite-product and tail Schwartz–Bruhat
spaces have countable complex dimension. -/
theorem finiteProduct_tailSchwartz_countableRank (S T : Finset (Places(F))) :
    Module.rank ℂ ℬ((FinitePlaceProduct F S)) ≤ ℵ₀ ∧
      Module.rank ℂ ℬ(FiniteAdeleTail F T) ≤ ℵ₀ := by sorry

/-- Paper: Proposition 2.1.2.8(1), p. 65. Both Schwartz–Bruhat spaces carry
the finest locally convex topology. -/
theorem finiteProduct_tailSchwartz_finestTopology (S T : Finset (Places(F))) :
    (inferInstance : TopologicalSpace ℬ((FinitePlaceProduct F S))) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex ℬ((FinitePlaceProduct F S)))) ∧
    (inferInstance : TopologicalSpace ℬ(FiniteAdeleTail F T)) =
      (inferInstance : TopologicalSpace (FinestLocallyConvex ℬ(FiniteAdeleTail F T))) := by sorry

/-- Paper: Proposition 2.1.2.8(1), p. 65. Both Schwartz–Bruhat spaces are strict LF-spaces.
Their bornological property is stated in `schwartzBruhat_bornological`. -/
theorem finiteProduct_tailSchwartz_strictLF (S T : Finset (Places(F))) :
    IsStrictLFSpace ℬ((FinitePlaceProduct F S)) ∧ IsStrictLFSpace ℬ(FiniteAdeleTail F T) := by sorry

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
      (BarrelledSpace ℂ ℬ(FiniteAdeleTail F T) ∧ MontelSpace ℂ ℬ(FiniteAdeleTail F T)) := by sorry

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
