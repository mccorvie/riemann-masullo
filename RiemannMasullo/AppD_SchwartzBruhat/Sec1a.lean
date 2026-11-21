module

public import RiemannMasullo.AppC_LCTVS.Sec2a_part2
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Measure.Haar.Quotient
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Topology.Algebra.PontryaginDual
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.ContinuousMap.CompactlySupported
import RiemannMasullo.ForMathlib.Analysis.Calculus.FDeriv.Symmetric
import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.PiL2
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.SmoothFamily
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Separation
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.Probability.Kernel.Composition.IntegralCompProd
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Measure
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Regular
import RiemannMasullo.ForMathlib.Topology.Algebra.PontryaginDual.Compact
import Mathlib.Topology.ContinuousMap.StoneWeierstrass
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Measure.Haar.Unique
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Haar.Extension
import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.Topology.Algebra.Support
import RiemannMasullo.ForMathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Fourier analysis and Schwartz spaces of elementary abelian Lie groups

Masullo, §§D.1.1–D.1.3, pp. 745–757.
-/

@[expose] public noncomputable section

open Bornology Filter MeasureTheory Set Topology
open scoped BigOperators ContDiff ENNReal NNReal TensorProduct Topology ZeroAtInfty

namespace RiemannMasullo

section Pontryagin

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]

-- Retain `T2Space G` in the existing signature.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem D.1.1.1(1), p. 746. The Pontryagin dual is Hausdorff and locally compact.
Mathlib supplies its abelian topological group structure and precomposition functor
`PontryaginDual.map`, with `PontryaginDual.map_one` and `PontryaginDual.map_comp`. -/
theorem pontryaginDual_basic : T2Space (PontryaginDual G) ∧
    LocallyCompactSpace (PontryaginDual G) := by
  exact ⟨inferInstance, inferInstance⟩

/-- Paper: Theorem D.1.1.1(2), p. 746. Characters separate points of the group, and
evaluation separates characters. -/
theorem pontryaginDual_pairing_separates :
    Function.Injective (fun (x : G) (χ : PontryaginDual G) ↦ χ x) ∧
    Function.Injective (fun (χ : PontryaginDual G) (x : G) ↦ χ x) := by
  constructor
  · intro x y h
    by_contra hxy
    obtain ⟨χ, hχ⟩ := exists_pontryaginDual_apply_ne_one (div_ne_one.mpr hxy)
    exact hχ (by simp [map_div, congrFun h χ])
  · intro χ ψ h
    exact PontryaginDual.ext (congrFun h)

omit [T2Space G] in
/-- Paper: (D.1.1.3), p. 746. Evaluating characters at a point gives a continuous
homomorphism from the group into its bidual. -/
def pontryaginDual_eval : G →ₜ* PontryaginDual (PontryaginDual G) := by
  have hEval : Continuous (fun p : PontryaginDual G × G ↦ p.1 p.2) :=
    (continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_fst).prodMk continuous_snd)
  let atPoint (x : G) : PontryaginDual (PontryaginDual G) :=
    { toFun := fun χ ↦ χ x
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := hEval.comp (continuous_id.prodMk continuous_const) }
  refine
    { toFun := atPoint
      map_one' := PontryaginDual.ext fun χ ↦ map_one χ
      map_mul' := fun x y ↦ PontryaginDual.ext fun χ ↦ map_mul χ x y
      continuous_toFun := ?_ }
  exact ContinuousMonoidHom.continuous_of_continuous_uncurry atPoint
    (hEval.comp (continuous_snd.prodMk continuous_fst))

/-- Paper: Theorem D.1.1.1(2), p. 746. Every identity neighborhood contains the points
where a suitable compact set of characters is uniformly within distance `1 / 4` of `1`.
One can use a positive-definite bump supported in the neighborhood and a compact set
carrying most of its Bochner measure. -/
theorem exists_pontryaginDual_compact_test {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ K : Set (PontryaginDual G), IsCompact K ∧
      ∀ x : G, (∀ χ ∈ K, dist (χ x) 1 < 1 / 4) → x ∈ U := by
  exact exists_compact_pontryaginDual_test hU

/-- Paper: Theorem D.1.1.1(2), p. 746. Evaluation embeds the group as a closed subgroup
of its bidual. -/
theorem isClosedEmbedding_pontryaginDual_eval :
    IsClosedEmbedding (pontryaginDual_eval (G := G)) := by
  let e := pontryaginDual_eval (G := G)
  have hInducing : IsInducing e := by
    rw [IsTopologicalGroup.isInducing_iff_nhds_one]
    refine le_antisymm ?_ ?_
    · have h : Tendsto e (𝓝 1) (𝓝 (e 1)) := e.continuous.tendsto 1
      rw [map_one] at h
      exact h.le_comap
    · intro U hU
      obtain ⟨K, hK, hTest⟩ := exists_pontryaginDual_compact_test hU
      let V : Set (PontryaginDual (PontryaginDual G)) :=
        {ψ | MapsTo ψ K (Metric.ball 1 (1 / 4))}
      have hV : IsOpen V :=
        (ContinuousMap.isOpen_setOfPred_mapsTo hK Metric.isOpen_ball).preimage
          (ContinuousMonoidHom.isInducing_toContinuousMap (PontryaginDual G) Circle).continuous
      refine Filter.mem_comap.mpr ⟨V, hV.mem_nhds ?_, fun x hx ↦ hTest x (fun χ hχ ↦ hx hχ)⟩
      intro χ _
      simp [Metric.mem_ball]
  have hInjective : Function.Injective e := by
    intro x y h
    exact pontryaginDual_pairing_separates.1 (funext fun χ ↦ DFunLike.congr_fun h χ)
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let : UniformSpace (PontryaginDual (PontryaginDual G)) := IsTopologicalGroup.rightUniformSpace _
  let : IsUniformGroup G := isUniformGroup_of_commGroup
  let : IsUniformGroup (PontryaginDual (PontryaginDual G)) := isUniformGroup_of_commGroup
  let : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace G
  exact (MonoidHom.isUniformEmbedding_of_isEmbedding (f := e)
    ⟨hInducing, hInjective⟩).isClosedEmbedding

/-- For each identity neighborhood in the dual, there is an inner-regular probability
measure on the group whose Fourier–Stieltjes transform vanishes off that neighborhood.
One route is to take the autocorrelation of a bump on the dual and use Plancherel to
represent it by the squared modulus of the inverse transform of the bump. -/
theorem exists_pontryaginDual_localized_integral [MeasurableSpace G] [BorelSpace G]
    {V : Set (PontryaginDual G)} (hV : V ∈ 𝓝 (1 : PontryaginDual G)) :
    ∃ ν : Measure G, IsProbabilityMeasure ν ∧ ν.InnerRegular ∧
      ∀ ψ ∉ V, ∫ x, (ψ x : ℂ) ∂ν = 0 := by
  sorry

open scoped Pointwise in
omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] in
/-- If a character of the dual is orthogonal to evaluations against a finite inner
regular measure, it is orthogonal to every character of the dual. Evaluation functions
form a point-separating self-adjoint algebra after taking their complex linear span. -/
theorem pontryaginDual_integral_mul_eq_zero
    [MeasurableSpace (PontryaginDual G)] [BorelSpace (PontryaginDual G)]
    (ν : Measure (PontryaginDual G)) [IsFiniteMeasure ν] [ν.InnerRegular]
    (η : PontryaginDual (PontryaginDual G))
    (h : ∀ x : G, ∫ χ, (η χ : ℂ) * (χ x : ℂ) ∂ν = 0)
    (ψ : PontryaginDual (PontryaginDual G)) : ∫ χ, (η χ : ℂ) * (ψ χ : ℂ) ∂ν = 0 := by
  -- The space of abstract characters is compact in the pointwise topology.
  let B : Set (G → Circle) := {f | f 1 = 1 ∧ ∀ x y, f (x * y) = f x * f y}
  have hB : IsClosed B := by
    rw [show B = {f : G → Circle | f 1 = 1} ∩
      ⋂ x, ⋂ y, {f : G → Circle | f (x * y) = f x * f y} by ext; simp [B]]
    exact (isClosed_eq (continuous_apply 1) continuous_const).inter
      (isClosed_iInter fun x ↦ isClosed_iInter fun y ↦
        isClosed_eq (continuous_apply (x * y)) ((continuous_apply x).mul (continuous_apply y)))
  let : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let emb : PontryaginDual G → B := fun χ ↦ ⟨χ, map_one χ, map_mul χ⟩
  have hEmb : Continuous emb := by
    apply Continuous.subtype_mk
    exact continuous_pi fun x ↦ (continuous_eval_const (F := C(G, Circle)) x).comp
      (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous
  have hInj : Function.Injective emb := fun _ _ hEq ↦
    DFunLike.coe_injective (congrArg Subtype.val hEq)
  let coord : G →* C(B, ℂ) :=
    { toFun := fun x ↦ ⟨fun b ↦ (b.1 x : ℂ),
        continuous_subtype_val.comp ((continuous_apply x).comp continuous_subtype_val)⟩
      map_one' := ContinuousMap.ext fun b ↦ by
        show (b.1 1 : ℂ) = 1
        rw [b.2.1, Circle.coe_one]
      map_mul' := fun x y ↦ ContinuousMap.ext fun b ↦ by
        show (b.1 (x * y) : ℂ) = _
        rw [b.2.2, Circle.coe_mul]
        rfl }
  have hStar (x : G) : star (coord x) = coord x⁻¹ := by
    ext b
    change star (b.1 x : ℂ) = (b.1 x⁻¹ : ℂ)
    have hInv : b.1 x⁻¹ = (b.1 x)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← b.2.2, inv_mul_cancel, b.2.1]
    rw [hInv, Circle.coe_inv_eq_conj, Complex.star_def]
  let A := StarAlgebra.adjoin ℂ (Set.range coord)
  have hSep : A.SeparatesPoints := by
    intro a b hab
    obtain ⟨x, hx⟩ : ∃ x, a.1 x ≠ b.1 x := by
      by_contra! hEq
      exact hab (Subtype.ext (funext hEq))
    exact ⟨coord x, ⟨coord x, StarAlgebra.subset_adjoin _ _ (mem_range_self x), rfl⟩,
      fun hEq ↦ hx (Subtype.ext hEq)⟩
  have hSpan : A.toSubalgebra.toSubmodule ≤ Submodule.span ℂ (Set.range coord) := by
    rw [StarAlgebra.adjoin_eq_span]
    apply Submodule.span_mono
    suffices Submonoid.closure (Set.range coord ∪ star (Set.range coord)) ≤
        MonoidHom.mrange coord from this
    apply Submonoid.closure_le.mpr
    rintro z (hMem | hMem)
    · exact hMem
    · obtain ⟨x, hx⟩ := Set.mem_star.mp hMem
      exact ⟨x⁻¹, (hStar x).symm.trans (by rw [hx, star_star])⟩
  let test (F : C(B, ℂ)) (χ : PontryaginDual G) := (η χ : ℂ) * F (emb χ)
  have hBound (F : C(B, ℂ)) (χ : PontryaginDual G) : ‖test F χ‖ ≤ ‖F‖ := by
    simp [test, ContinuousMap.norm_coe_le_norm]
  have hInt (F : C(B, ℂ)) : Integrable (test F) ν :=
    Integrable.of_bound ((continuous_subtype_val.comp η.continuous).mul
      (F.continuous.comp hEmb)).aestronglyMeasurable ‖F‖ (.of_forall (hBound F))
  let L : C(B, ℂ) →L[ℂ] ℂ := LinearMap.mkContinuous
    { toFun := fun F ↦ ∫ χ, test F χ ∂ν
      map_add' := fun F H ↦ by
        simp only [test, ContinuousMap.add_apply, mul_add]
        exact integral_add (hInt F) (hInt H)
      map_smul' := fun c F ↦ by
        simp only [test, ContinuousMap.smul_apply, mul_smul_comm,
          RingHom.id_apply, integral_smul] }
    (ν.real univ) fun F ↦ by
      simpa [mul_comm] using norm_integral_le_of_norm_le_const (μ := ν) (.of_forall (hBound F))
  -- Stone–Weierstrass extends the vanishing from evaluations to all continuous tests.
  have hL : ∀ F, L F = 0 := by
    have hDense := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints A hSep
    intro F
    have hClosed : IsClosed {H | L H = 0} := isClosed_eq L.continuous continuous_const
    refine closure_minimal (s := (A : Set C(B, ℂ))) ?_ hClosed ?_
    · intro H hH
      have hKer : Submodule.span ℂ (Set.range coord) ≤ L.toLinearMap.ker :=
        Submodule.span_le.mpr (fun _ ⟨x, hx⟩ ↦ hx ▸ h x)
      exact hKer (hSpan hH)
    · have hF : F ∈ A.topologicalClosure := hDense ▸ StarSubalgebra.mem_top
      exact hF
  let target (χ : PontryaginDual G) : ℂ := ψ χ
  have hTarget : Continuous target := continuous_subtype_val.comp ψ.continuous
  have hTargetInt : Integrable (fun χ ↦ (η χ : ℂ) * target χ) ν :=
    Integrable.of_bound
      ((continuous_subtype_val.comp η.continuous).mul hTarget).aestronglyMeasurable
      1 (.of_forall fun χ ↦ by simp [target])
  -- Extend the target from a compact set carrying nearly all the mass of ν.
  by_contra hNe
  let ε := ‖∫ χ, (η χ : ℂ) * target χ ∂ν‖
  have hε : 0 < ε := norm_pos_iff.mpr hNe
  obtain ⟨K, -, hK, hTail⟩ := MeasurableSet.univ.exists_isCompact_sdiff_lt
    (μ := ν) (measure_ne_top ν _) (ENNReal.ofReal_pos.mpr (by positivity : 0 < ε / 3)).ne'
  rw [← compl_eq_univ_sdiff] at hTail
  have hTail' : ν.real Kᶜ < ε / 3 := by
    simpa [measureReal_def, ENNReal.toReal_ofReal (by positivity : 0 ≤ ε / 3)] using
      (ENNReal.toReal_lt_toReal (measure_ne_top ν _) ENNReal.ofReal_ne_top).mpr hTail
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let incl : K → B := emb ∘ Subtype.val
  have hIncl : IsClosedEmbedding incl :=
    (hEmb.comp continuous_subtype_val).isClosedEmbedding (hInj.comp Subtype.val_injective)
  let re : C(K, ℝ) := ⟨fun χ ↦ (target χ.1).re,
    Complex.continuous_re.comp (hTarget.comp continuous_subtype_val)⟩
  let im : C(K, ℝ) := ⟨fun χ ↦ (target χ.1).im,
    Complex.continuous_im.comp (hTarget.comp continuous_subtype_val)⟩
  obtain ⟨R, hR, hRe⟩ := BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding
    (BoundedContinuousFunction.mkOfCompact re) hIncl
  obtain ⟨I, hI, hIm⟩ := BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding
    (BoundedContinuousFunction.mkOfCompact im) hIncl
  have hR₁ : ‖R‖ ≤ 1 := hR.le.trans <| (BoundedContinuousFunction.norm_le zero_le_one).2
    fun χ ↦ (Complex.abs_re_le_norm (target χ.1)).trans (by simp [target])
  have hI₁ : ‖I‖ ≤ 1 := hI.le.trans <| (BoundedContinuousFunction.norm_le zero_le_one).2
    fun χ ↦ (Complex.abs_im_le_norm (target χ.1)).trans (by simp [target])
  let F : C(B, ℂ) := ⟨fun b ↦ (R b : ℂ) + (I b : ℂ) * Complex.I, by fun_prop⟩
  have hF (b : B) : ‖F b‖ ≤ 2 := by
    refine (norm_add_le _ _).trans ?_
    simpa [F, norm_mul, one_add_one_eq_two] using add_le_add
      ((BoundedContinuousFunction.norm_coe_le_norm R b).trans hR₁)
      ((BoundedContinuousFunction.norm_coe_le_norm I b).trans hI₁)
  have hAgree : ∀ χ ∈ K, F (emb χ) = target χ := by
    intro χ hχ
    have hr := congrFun hRe ⟨χ, hχ⟩
    have hi := congrFun hIm ⟨χ, hχ⟩
    change R (emb χ) = (target χ).re at hr
    change I (emb χ) = (target χ).im at hi
    simp only [F, ContinuousMap.coe_mk, hr, hi, Complex.re_add_im]
  have hDiff (χ : PontryaginDual G) : ‖(η χ : ℂ) * target χ - test F χ‖ ≤ 3 := by
    change ‖(η χ : ℂ) * target χ - (η χ : ℂ) * F (emb χ)‖ ≤ 3
    rw [← mul_sub, norm_mul, Circle.norm_coe, one_mul]
    calc
      _ ≤ ‖target χ‖ + ‖F (emb χ)‖ := norm_sub_le _ _
      _ ≤ 1 + 2 := add_le_add (by simp [target]) (hF (emb χ))
      _ = 3 := by norm_num
  let diff (χ : PontryaginDual G) := (η χ : ℂ) * target χ - test F χ
  have hDiffInt : Integrable diff ν := hTargetInt.sub (hInt F)
  have hKZero : ∫ χ in K, diff χ ∂ν = 0 := by
    calc
      _ = ∫ _ in K, (0 : ℂ) ∂ν := by
        exact setIntegral_congr_fun hK.isClosed.measurableSet fun χ hχ ↦ by
          simp [diff, test, hAgree χ hχ]
      _ = 0 := integral_zero _ _
  have hFull : (∫ χ in Kᶜ, diff χ ∂ν) = ∫ χ, (η χ : ℂ) * target χ ∂ν := by
    rw [← zero_add (∫ χ in Kᶜ, diff χ ∂ν), ← hKZero,
      integral_add_compl hK.isClosed.measurableSet hDiffInt]
    change (∫ χ, (η χ : ℂ) * target χ - test F χ ∂ν) = _
    rw [integral_sub hTargetInt (hInt F)]
    change _ - L F = _
    rw [hL, sub_zero]
  have hLe := norm_setIntegral_le_of_norm_le_const (f := diff) (measure_lt_top ν Kᶜ)
    (fun χ _ ↦ hDiff χ)
  rw [hFull] at hLe
  linarith

/-- Paper: Theorem D.1.1.1(2), p. 746. Evaluation gives the canonical topological
group isomorphism with the double dual. -/
theorem pontryaginDual_bidual :
    ∃ e : G ≃ₜ* PontryaginDual (PontryaginDual G),
      ∀ x χ, e x χ = χ x := by
  let e := pontryaginDual_eval (G := G)
  have hEmb := isClosedEmbedding_pontryaginDual_eval (G := G)
  have hSurj : Function.Surjective e := by
    intro η
    by_contra hη
    -- Choose a transform that vanishes on the translate of the evaluation image by η⁻¹.
    let V := ((η * ·) ⁻¹' Set.range e)ᶜ
    have hV : V ∈ 𝓝 (1 : PontryaginDual (PontryaginDual G)) :=
      (hEmb.isClosed_range.preimage (continuous_const.mul continuous_id)).isOpen_compl.mem_nhds
        (by simpa [V] using hη)
    let : MeasurableSpace (PontryaginDual G) := borel _
    let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
    obtain ⟨ν, hν, hReg, hZero⟩ := exists_pontryaginDual_localized_integral hV
    let := hν
    let := hReg
    have hTest (x : G) : ∫ χ, (η⁻¹ χ : ℂ) * (χ x : ℂ) ∂ν = 0 := by
      have hx : η⁻¹ * e x ∉ V := by simp [V]
      exact hZero _ hx
    have hz := pontryaginDual_integral_mul_eq_zero ν η⁻¹ hTest η
    have hProd (χ : PontryaginDual G) : (η⁻¹ χ : ℂ) * (η χ : ℂ) = 1 := by
      rw [← Circle.coe_mul]
      change ((η⁻¹ * η) χ : ℂ) = 1
      rw [inv_mul_cancel, PontryaginDual.one_apply, Circle.coe_one]
    simp [hProd] at hz
  let equiv := MulEquiv.ofBijective e.toMonoidHom ⟨hEmb.injective, hSurj⟩
  have hOpen := hEmb.isInducing.isOpenMap (by rw [hSurj.range_eq]; exact isOpen_univ)
  exact ⟨equiv.toContinuousMulEquiv (fun _ ↦
    (hOpen.isQuotientMap e.continuous hSurj).isCoinducing.isOpen_preimage),
    fun _ _ ↦ rfl⟩

/-- Paper: Theorem D.1.1.1(3), p. 746. A locally compact abelian group is compact
exactly when its dual is discrete. -/
theorem compactSpace_iff_discretePontryaginDual :
    CompactSpace G ↔ DiscreteTopology (PontryaginDual G) := by
  constructor
  · intro h
    infer_instance
  · intro h
    exact (isClosedEmbedding_pontryaginDual_eval (G := G)).compactSpace

end Pontryagin

section Fourier

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

local instance : MeasurableSpace (PontryaginDual G) := borel _

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]

/-- Paper: (D.1.1.4), p. 746. Evaluate the Fourier transform by integrating against
the complex conjugate of a character. -/
def lcaFourier (μ : Measure G) (f : G → ℂ) (χ : PontryaginDual G) : ℂ :=
  ∫ x, f x * star (χ x : ℂ) ∂μ

-- Retain the existing signature, including the unused integrability hypothesis.
set_option linter.unusedSectionVars false in
set_option linter.unusedVariables false in
/-- Paper: (D.1.1.4), p. 746. At the trivial character the transform is the integral
of the original function. -/
theorem lcaFourier_one (f : G → ℂ) (hf : Integrable f μ) :
    lcaFourier μ f 1 = ∫ x, f x ∂μ := by
  simp [lcaFourier, PontryaginDual.one_apply]

/-- Paper: (D.1.1.5), p. 746. Multiplicative convolution integrates the product with
the left translate of the second function. -/
def lcaConvolution (μ : Measure G) (f g : G → ℂ) (x : G) : ℂ :=
  ∫ y, f y * g (y⁻¹ * x) ∂μ

/-- Paper: (D.1.1.5), p. 746. Convolution on a one-point group is multiplication
scaled by its total Haar mass. -/
theorem lcaConvolution_subsingleton [Subsingleton G] (f g : G → ℂ) (x : G) :
    lcaConvolution μ f g x = (μ univ).toReal * f x * g x := by
  unfold lcaConvolution
  calc
    (∫ y, f y * g (y⁻¹ * x) ∂μ) = ∫ _ : G, f x * g x ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y ↦ by
        change f y * g (y⁻¹ * x) = f x * g x
        rw [Subsingleton.elim y x, Subsingleton.elim (x⁻¹ * x) x]
    _ = (μ univ).toReal * f x * g x := by
      simp only [integral_const, measureReal_def, Complex.real_smul, mul_assoc]

open scoped Pointwise in
/-- A product-measurable representative for the convolution kernel, carried on a
rectangle with σ-finite sides. The two sectionwise identities avoid any measurability
assumption on multiplication for the product σ-algebra. -/
private theorem lcaConvolution_kernel {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    ∃ (S : Set G) (k : G × G → ℂ), SigmaFinite (μ.restrict S) ∧ StronglyMeasurable k ∧
      Function.support k ⊆ S ×ˢ S ∧
      (∀ x, ∀ᵐ y ∂μ, k (x, y) = f y * g (y⁻¹ * x)) ∧
      (∀ᵐ y ∂μ, ∀ᵐ x ∂μ, k (x, y) = f y * g (y⁻¹ * x)) := by
  obtain ⟨F, hF, cF, tF⟩ := exists_tendsto_ae_compactSupport hf
  obtain ⟨H, hH, cH, tH⟩ := exists_tendsto_ae_compactSupport hg
  let K n := tsupport (F n) ∪ tsupport (F n) * tsupport (H n)
  have hK (n) : IsCompact (K n) := (hF n).isCompact.union ((hF n).isCompact.mul (hH n).isCompact)
  let S := ⋃ n, K n
  have hS : MeasurableSet S := MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  have hσ : SigmaFinite (μ.restrict S) := by
    refine ⟨⟨⟨fun n ↦ K n ∪ Sᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hS.compl),
        union_inter_distrib_right, compl_inter_self, union_empty]
      exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
    · rw [← iUnion_union]
      exact union_compl_self S
  let P (n : ℕ) (p : G × G) := F n p.2 * H n (p.2⁻¹ * p.1)
  have hP (n) : Function.support (P n) ⊆ K n ×ˢ K n := by
    rintro ⟨x, y⟩ hp
    have hfy := subset_tsupport (F n) ((mul_ne_zero_iff.mp hp).1)
    have hgy := subset_tsupport (H n) ((mul_ne_zero_iff.mp hp).2)
    exact ⟨Or.inr ⟨y, hfy, y⁻¹ * x, hgy, mul_inv_cancel_left y x⟩, Or.inl hfy⟩
  have mP (n) : StronglyMeasurable (P n) := by
    have hcompact : HasCompactSupport (P n) := HasCompactSupport.intro ((hK n).prod (hK n))
      (fun p hp ↦ Function.notMem_support.mp (fun h ↦ hp (hP n h)))
    exact hcompact.stronglyMeasurable_of_prod ((cF n).comp continuous_snd |>.mul
      ((cH n).comp (continuous_snd.inv.mul continuous_fst)))
  let k (p : G × G) := limUnder atTop (fun n ↦ P n p)
  refine ⟨S, k, hσ, StronglyMeasurable.limUnder mP, ?_, ?_, ?_⟩
  · intro p hp
    by_contra h
    have hz (n) : P n p = 0 := Function.notMem_support.mp fun hn ↦
      h ⟨mem_iUnion.mpr ⟨n, (hP n hn).1⟩, mem_iUnion.mpr ⟨n, (hP n hn).2⟩⟩
    have ht : Tendsto (fun n ↦ P n p) atTop (𝓝 0) := by
      simp only [hz]
      exact tendsto_const_nhds
    exact hp ht.limUnder_eq
  · intro x
    have hmp := (measurePreserving_mul_right μ x).comp (Measure.measurePreserving_inv μ)
    filter_upwards [tF, hmp.quasiMeasurePreserving.tendsto_ae.eventually tH] with y hy hy'
    exact (hy.mul hy').limUnder_eq
  · filter_upwards [tF] with y hy
    have hmp := measurePreserving_mul_left μ y⁻¹
    filter_upwards [hmp.quasiMeasurePreserving.tendsto_ae.eventually tH] with x hx
    exact (hy.mul hx).limUnder_eq

/-- Paper: (D.1.1.5)–(D.1.1.6), p. 746. The fibre integrals of two L¹ functions
exist almost everywhere and their convolution is L¹ with the product norm bound. -/
theorem lcaConvolution_integrable {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    (∀ᵐ x ∂μ, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ) ∧
      Integrable (lcaConvolution μ f g) μ ∧
      eLpNorm (lcaConvolution μ f g) 1 μ ≤ eLpNorm f 1 μ * eLpNorm g 1 μ := by
  obtain ⟨S, k, hσ, hk, hs, hrow, hcol⟩ := lcaConvolution_kernel μ hf hg
  have hzero (p : G × G) (hp : p ∉ S ×ˢ S) : k p = 0 :=
    Function.notMem_support.mp fun h ↦ hp (hs h)
  let N (x : G) := ∫⁻ y in S, ‖k (x, y)‖ₑ ∂μ
  have hN : Measurable N := hk.eNorm.lintegral_prod_right'
  have hfull (x) : N x = ∫⁻ y, ‖k (x, y)‖ₑ ∂μ := by
    apply setLIntegral_eq_of_support_subset
    intro y hy
    by_contra h
    exact hy (by simp [hzero (x, y) (fun hp ↦ h hp.2)])
  have hconv (x) : (∫ y in S, k (x, y) ∂μ) = lcaConvolution μ f g x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun y hy ↦ hzero (x, y) (fun hp ↦ hy hp.2))).trans (integral_congr_ae (hrow x))
  have hm : StronglyMeasurable (lcaConvolution μ f g) := (funext hconv) ▸ hk.integral_prod_right'
  -- Tonelli applies on the supporting rectangle, even when Haar measure on G is not σ-finite.
  have hbound : ∫⁻ x, N x ∂μ ≤ eLpNorm f 1 μ * eLpNorm g 1 μ := calc
    _ = ∫⁻ x in S, N x ∂μ := by
      symm
      apply setLIntegral_eq_of_support_subset
      intro x hx
      by_contra h
      exact hx (by simp [N, fun y ↦ hzero (x, y) (fun hp ↦ h hp.1)])
    _ = ∫⁻ y in S, ∫⁻ x in S, ‖k (x, y)‖ₑ ∂μ ∂μ := lintegral_lintegral_swap hk.eNorm.aemeasurable
    _ ≤ ∫⁻ y, ∫⁻ x, ‖k (x, y)‖ₑ ∂μ ∂μ :=
      lintegral_mono' Measure.restrict_le_self fun y ↦ setLIntegral_le_lintegral _ _
    _ = ∫⁻ y, ‖f y‖ₑ * eLpNorm g 1 μ ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hcol] with y hy
      calc
        _ = ∫⁻ x, ‖f y‖ₑ * ‖g (y⁻¹ * x)‖ₑ ∂μ := lintegral_congr_ae <|
          hy.mono fun x hx ↦ by rw [hx, eNorm_mul]
        _ = _ := by
          rw [lintegral_const_mul' _ _ (by simp), lintegral_mul_left_eq_self (fun z ↦ ‖g z‖ₑ),
            eLpNorm_one_eq_lintegral_eNorm hg.aestronglyMeasurable]
    _ = _ := by
      rw [lintegral_mul_const'' _ hf.aestronglyMeasurable.eNorm,
        eLpNorm_one_eq_lintegral_eNorm hf.aestronglyMeasurable]
  have hfin := hbound.trans_lt (ENNReal.mul_lt_top (memLp_one_iff_integrable.2 hf)
    (memLp_one_iff_integrable.2 hg))
  have hle : ∫⁻ x, ‖lcaConvolution μ f g x‖ₑ ∂μ ≤ ∫⁻ x, N x ∂μ :=
    lintegral_mono fun x ↦ hconv x ▸ eNorm_integral_le_lintegral_eNorm _
  refine ⟨?_, ⟨hm.aestronglyMeasurable, hle.trans_lt hfin⟩, ?_⟩
  · filter_upwards [ae_lt_top hN hfin.ne] with x hx
    have hInt : Integrable (fun y ↦ k (x, y)) μ :=
      ⟨(hk.comp_measurable measurable_prodMk_left).aestronglyMeasurable, (hfull x).symm.trans_lt hx⟩
    exact hInt.congr (hrow x)
  · rw [eLpNorm_one_eq_lintegral_eNorm hm.aestronglyMeasurable]
    exact hle.trans hbound

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [μ.IsHaarMeasure] [μ.Regular] in
/-- Multiplication by a conjugated character preserves integrability. -/
private theorem integrable_fourierIntegrand {f : G → ℂ} (hf : Integrable f μ)
    (χ : PontryaginDual G) : Integrable (fun x ↦ f x * star (χ x : ℂ)) μ := by
  exact hf.mul_bdd (c := 1) ((continuous_subtype_val.comp χ.continuous).star.aestronglyMeasurable)
    (.of_forall fun x ↦ by simp)

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [BorelSpace G]
    [μ.IsHaarMeasure] [μ.Regular] in
/-- The Fourier integral is bounded by the integral of the absolute value. -/
private theorem norm_lcaFourier_le_integral_norm (f : G → ℂ) (χ : PontryaginDual G) :
    ‖lcaFourier μ f χ‖ ≤ ∫ x, ‖f x‖ ∂μ := by
  simpa only [lcaFourier, norm_mul, norm_star, Circle.norm_coe, mul_one] using
    norm_integral_le_integral_norm (μ := μ) (fun x ↦ f x * star (χ x : ℂ))

omit [IsTopologicalGroup G] [μ.IsHaarMeasure] in
/-- Uniform convergence of characters on compact sets controls the integral, since
the integral of the norm of an L¹ function outside a suitable compact set is small. -/
private theorem continuous_lcaFourier {f : G → ℂ} (hf : Integrable f μ) :
    Continuous (lcaFourier μ f) := by
  rw [continuous_iff_continuousAt]
  intro ψ
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨K, -, hK, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hf
    MeasurableSet.univ (show 0 < ε / 4 by positivity)
  rw [← compl_eq_univ_sdiff] at hTail
  let I := ∫ x, ‖f x‖ ∂μ
  have hI : 0 ≤ I := integral_nonneg fun _ ↦ norm_nonneg _
  let δ := ε / 2 / (I + 1)
  have hδ : 0 < δ := div_pos (half_pos hε) (by positivity)
  let d (p : PontryaginDual G × G) : ℂ := star (p.1 p.2 : ℂ) - star (ψ p.2 : ℂ)
  have he : Continuous (fun p : PontryaginDual G × G ↦ p.1 p.2) :=
    (continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_fst).prodMk continuous_snd)
  have hd : Continuous d := (continuous_subtype_val.comp he).star.sub
    ((continuous_subtype_val.comp ψ.continuous).comp continuous_snd).star
  have hNear : ∀ᶠ χ in 𝓝 ψ, ∀ x ∈ K, ‖d (χ, x)‖ < δ :=
    hK.eventually_forall_of_forall_eventually fun x _ ↦
      (isOpen_lt hd.norm continuous_const).mem_nhds (by simpa [d] using hδ)
  filter_upwards [hNear] with χ hχ
  let q (x : G) := f x * d (χ, x)
  have hq : Integrable q μ := by
    refine ((integrable_fourierIntegrand μ hf χ).sub
      (integrable_fourierIntegrand μ hf ψ)).congr (.of_forall fun x ↦ ?_)
    change f x * star (χ x : ℂ) - f x * star (ψ x : ℂ) =
      f x * (star (χ x : ℂ) - star (ψ x : ℂ))
    exact (mul_sub _ _ _).symm
  have hOn : ‖∫ x in K, q x ∂μ‖ ≤ ε / 2 := by
    have hBound := norm_integral_le_of_norm_le (μ := μ.restrict K) (f := q)
      (hf.norm.const_mul δ).integrableOn
      ((ae_restrict_mem hK.isClosed.measurableSet).mono fun x hx ↦ by
        change ‖f x * d (χ, x)‖ ≤ _
        rw [norm_mul, mul_comm]
        exact mul_le_mul_of_nonneg_right (hχ x hx).le (norm_nonneg _))
    rw [integral_const_mul] at hBound
    refine hBound.trans ((mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hf.norm (.of_forall fun _ ↦ norm_nonneg _)) hδ.le).trans ?_)
    calc
      δ * I ≤ δ * (I + 1) := by gcongr; linarith
      _ = ε / 2 := div_mul_cancel₀ _ (by positivity)
  have hOff : ‖∫ x in Kᶜ, q x ∂μ‖ < ε / 2 := by
    have hBound := norm_integral_le_of_norm_le (μ := μ.restrict Kᶜ) (f := q)
      (hf.norm.const_mul 2).integrableOn (.of_forall fun x ↦ by
        change ‖f x * d (χ, x)‖ ≤ _
        rw [norm_mul, mul_comm]
        refine mul_le_mul_of_nonneg_right ((norm_sub_le _ _).trans ?_) (norm_nonneg _)
        simp [one_add_one_eq_two])
    rw [integral_const_mul] at hBound
    exact hBound.trans_lt (by linarith)
  have hEq : (∫ x, q x ∂μ) = lcaFourier μ f χ - lcaFourier μ f ψ := by
    simp only [q, d, lcaFourier, mul_sub]
    exact integral_sub (integrable_fourierIntegrand μ hf χ) (integrable_fourierIntegrand μ hf ψ)
  rw [dist_eq_norm, ← hEq, ← integral_add_compl hK.isClosed.measurableSet hq]
  exact (norm_add_le _ _).trans_lt (by linarith)

omit [T2Space G] [LocallyCompactSpace G] [μ.Regular] in
/-- Left translation multiplies the Fourier transform by the corresponding character value. -/
private theorem lcaFourier_translate (f : G → ℂ) (a : G) (χ : PontryaginDual G) :
    lcaFourier μ (fun x ↦ f (a * x)) χ = (χ a : ℂ) * lcaFourier μ f χ := by
  have hUnit : (χ a : ℂ) * star (χ a : ℂ) = 1 := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Circle.norm_coe]
    simp
  unfold lcaFourier
  rw [← integral_mul_left_eq_self (μ := μ) (fun x ↦ f x * star (χ x : ℂ)) a,
    ← integral_const_mul]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    change f (a * x) * star (χ x : ℂ) =
      (χ a : ℂ) * (f (a * x) * star (χ (a * x) : ℂ))
    have hMul : (χ (a * x) : ℂ) = (χ a : ℂ) * (χ x : ℂ) := by
      simp only [map_mul, Circle.coe_mul]
    rw [hMul, star_mul]
    symm
    calc
      _ = ((χ a : ℂ) * star (χ a : ℂ)) * (f (a * x) * star (χ x : ℂ)) := by ring
      _ = _ := by rw [hUnit, one_mul]

omit [T2Space G] [LocallyCompactSpace G] [μ.Regular] in
/-- A small L¹ translation difference bounds the transform times the displacement
of the character at the translating element. -/
private theorem norm_mul_lcaFourier_le_translation {f : G → ℂ} (hf : Integrable f μ)
    (a : G) (χ : PontryaginDual G) :
    ‖(χ a : ℂ) - 1‖ * ‖lcaFourier μ f χ‖ ≤
      ‖Lp.compMeasurePreserving (a * ·) (measurePreserving_mul_left μ a)
        ((memLp_one_iff_integrable.mpr hf).toLp f) - (memLp_one_iff_integrable.mpr hf).toLp f‖ := by
  let f₁ := (memLp_one_iff_integrable.mpr hf).toLp f
  let T := Lp.compMeasurePreserving (a * ·) (measurePreserving_mul_left μ a) f₁
  have hF : (f₁ : G → ℂ) =ᵐ[μ] f := MemLp.coeFn_toLp (memLp_one_iff_integrable.mpr hf)
  have hT : (T : G → ℂ) =ᵐ[μ] fun x ↦ f (a * x) :=
    (Lp.coeFn_compMeasurePreserving f₁ _).trans
      ((measurePreserving_mul_left μ a).quasiMeasurePreserving.ae_eq_comp hF)
  have hDiff : ((T - f₁ : Lp ℂ 1 μ) : G → ℂ) =ᵐ[μ] fun x ↦ f (a * x) - f x :=
    (Lp.coeFn_sub T f₁).trans (hT.sub hF)
  have hTransform : lcaFourier μ (T - f₁ : Lp ℂ 1 μ) χ =
      ((χ a : ℂ) - 1) * lcaFourier μ f χ := by
    unfold lcaFourier at *
    calc
      _ = ∫ x, (f (a * x) - f x) * star (χ x : ℂ) ∂μ :=
        integral_congr_ae (hDiff.mono fun x hx ↦ by rw [hx])
      _ = (∫ x, f (a * x) * star (χ x : ℂ) ∂μ) -
          ∫ x, f x * star (χ x : ℂ) ∂μ := by
        simp_rw [sub_mul]
        exact integral_sub
          (integrable_fourierIntegrand μ
            ((measurePreserving_mul_left μ a).integrable_comp_of_integrable hf) χ) (integrable_fourierIntegrand μ hf χ)
      _ = _ := by
        rw [sub_mul, one_mul]
        exact congrArg (· - _) (lcaFourier_translate μ f a χ)
  rw [← norm_mul, ← hTransform, L1.norm_eq_integral_norm (T - f₁)]
  exact norm_lcaFourier_le_integral_norm μ _ χ

/-- Paper: Lemma D.1.1.2(1), p. 746. The Fourier transform of an L¹ function
is continuous and vanishes at infinity on the dual group. -/
theorem lcaFourier_zeroAtInfty {f : G → ℂ} (hf : Integrable f μ) :
    ∃ F : C₀(PontryaginDual G, ℂ), ∀ χ, F χ = lcaFourier μ f χ := by
  refine ⟨⟨⟨lcaFourier μ f, continuous_lcaFourier μ hf⟩, ?_⟩, fun _ ↦ rfl⟩
  apply NormedAddGroup.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨r, hr, hPolar⟩ := exists_isCompact_pontryaginDual_polar (G := G)
  let f₁ := (memLp_one_iff_integrable.mpr hf).toLp f
  let T (a : G) := Lp.compMeasurePreserving (a * ·) (measurePreserving_mul_left μ a) f₁
  have hc : Continuous T := by
    have hMul : Continuous fun a : G ↦ ContinuousMap.mulLeft (X := G) a :=
      (ContinuousMap.curry
        ⟨fun p : G × G ↦ p.1 * p.2, continuous_mul⟩).continuous
    exact continuous_const.compMeasurePreservingLp hMul _ ENNReal.one_ne_top
  have hOne : T 1 = f₁ := by
    apply Lp.ext
    simpa [T, Function.comp_def] using
      Lp.coeFn_compMeasurePreserving f₁ (measurePreserving_mul_left μ (1 : G))
  let U := {a | ‖T a - f₁‖ < r * ε}
  have hU : U ∈ 𝓝 (1 : G) :=
    (isOpen_lt (hc.sub continuous_const).norm continuous_const).mem_nhds
      (by
        change ‖T 1 - f₁‖ < r * ε
        rw [hOne, sub_self, norm_zero]
        exact mul_pos hr hε)
  refine mem_cocompact.mpr ⟨_, hPolar U hU, fun χ hχ ↦ ?_⟩
  have hOut : ¬ ∀ a ∈ U, χ a ∈ Metric.closedBall 1 r := hχ
  push Not at hOut
  obtain ⟨a, ha, hFar⟩ := hOut
  have hDist : r ≤ ‖(χ a : ℂ) - 1‖ := by
    have hd : r < dist (χ a) 1 := lt_of_not_ge hFar
    change r < dist (χ a : ℂ) ((1 : Circle) : ℂ) at hd
    simpa only [Circle.coe_one, dist_eq_norm] using hd.le
  have hle := norm_mul_lcaFourier_le_translation μ hf a χ
  change _ ≤ ‖T a - f₁‖ at hle
  change ‖T a - f₁‖ < r * ε at ha
  exact (mul_lt_mul_iff_of_pos_left hr).mp
    ((mul_le_mul_of_nonneg_right hDist (norm_nonneg _)).trans_lt (hle.trans_lt ha))

omit [μ.IsHaarMeasure] in
/-- An integrable function whose Fourier transform is zero vanishes almost everywhere. -/
private theorem ae_eq_zero_of_lcaFourier_eq_zero {f : G → ℂ} (hf : Integrable f μ)
    (h : ∀ χ, lcaFourier μ f χ = 0) : f =ᵐ[μ] 0 := by
  let e (x : G) : PontryaginDual G →* Circle :=
    { toFun := fun χ ↦ χ x
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hInj : Function.Injective e := fun _ _ hEq ↦
    pontryaginDual_pairing_separates.1 (funext (DFunLike.congr_fun hEq))
  refine ae_eq_zero_of_integral_mul_circle_eq_zero e (fun χ ↦ χ.continuous) hInj hf ?_
  intro χ
  have hinv (x : G) : star (χ⁻¹ x : ℂ) = (χ x : ℂ) := by
    change star (((χ x)⁻¹ : Circle) : ℂ) = _
    rw [Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  change (∫ x, f x * (χ x : ℂ) ∂μ) = 0
  simpa only [lcaFourier, hinv] using h χ⁻¹

/-- Paper: Lemma D.1.1.2(2), p. 746. The integral formula gives an injective
complex-linear map on L¹ equivalence classes with operator norm at most one. -/
theorem lcaFourier_L1 :
    ∃ F : Lp ℂ 1 μ →ₗ[ℂ] C₀(PontryaginDual G, ℂ),
      (∀ f χ, F f χ = lcaFourier μ (f : G → ℂ) χ) ∧
      Function.Injective F ∧ ∀ f, ‖F f‖ ≤ ‖f‖ := by
  choose transform hTransform using fun f : Lp ℂ 1 μ ↦
    lcaFourier_zeroAtInfty μ (L1.integrable_coeFn f)
  let F : Lp ℂ 1 μ →ₗ[ℂ] C₀(PontryaginDual G, ℂ) :=
    { toFun := transform
      map_add' f g := ZeroAtInftyContinuousMap.ext fun χ ↦ by
        change transform (f + g) χ = transform f χ + transform g χ
        rw [hTransform, hTransform, hTransform]
        unfold lcaFourier
        calc
          _ = ∫ x, (f x + g x) * star (χ x : ℂ) ∂μ :=
            integral_congr_ae ((Lp.coeFn_add f g).mono fun x hx ↦ by rw [hx]; rfl)
          _ = _ := by
            simp_rw [add_mul]
            exact integral_add (integrable_fourierIntegrand μ (L1.integrable_coeFn f) χ)
              (integrable_fourierIntegrand μ (L1.integrable_coeFn g) χ)
      map_smul' c f := ZeroAtInftyContinuousMap.ext fun χ ↦ by
        change transform (c • f) χ = c • transform f χ
        rw [hTransform, hTransform]
        unfold lcaFourier
        calc
          _ = ∫ x, c • (f x * star (χ x : ℂ)) ∂μ :=
            integral_congr_ae ((Lp.coeFn_smul c f).mono fun x hx ↦ by
              rw [hx]
              exact smul_mul_assoc c (f x) _)
          _ = _ := integral_smul c _ }
  refine ⟨F, hTransform, LinearMap.ker_eq_bot.mp ?_, fun f ↦ ?_⟩
  · apply LinearMap.ker_eq_bot'.mpr
    intro f hf
    have hZero (χ : PontryaginDual G) : lcaFourier μ (f : G → ℂ) χ = 0 := by
      rw [← hTransform f χ]
      exact DFunLike.congr_fun hf χ
    exact Lp.ext ((ae_eq_zero_of_lcaFourier_eq_zero μ (L1.integrable_coeFn f) hZero).trans
      (Lp.coeFn_zero ℂ 1 μ).symm)
  · rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (norm_nonneg _)).mpr
    intro χ
    change ‖transform f χ‖ ≤ ‖f‖
    rw [hTransform, L1.norm_eq_integral_norm]
    exact norm_lcaFourier_le_integral_norm μ _ χ

/-- Each fibre of an `L²` convolution is integrable, with the Cauchy–Schwarz bound. -/
lemma integrable_lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) (x : G) :
    Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ ∧
      ‖lcaConvolution μ f g x‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hpres : MeasurePreserving (fun y : G ↦ x / y) μ μ :=
    Measure.measurePreserving_div_left μ x
  have hfun : (fun y ↦ g (y⁻¹ * x)) = g ∘ fun y ↦ x / y := by
    ext y
    simp [div_eq_mul_inv, mul_comm]
  have hg' : MemLp (fun y ↦ g (y⁻¹ * x)) 2 μ := hfun ▸ hg.comp_measurePreserving hpres
  have hnorm : eLpNorm (fun y ↦ g (y⁻¹ * x)) 2 μ = eLpNorm g 2 μ := by
    rw [hfun]
    exact eLpNorm_comp_measurePreserving hg.aestronglyMeasurable hpres
  have hmul : MemLp (fun y ↦ f y * g (y⁻¹ * x)) 1 μ := hf.mul hg'
  have hint : Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ := memLp_one_iff_integrable.mp hmul
  have hprod : eLpNorm (fun y ↦ f y * g (y⁻¹ * x)) 1 μ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    have hsmul := eLpNorm_smul_le_mul_eLpNorm (μ := μ) (p := 2) (q := 2) (r := 1)
      (φ := f) (f := fun y ↦ g (y⁻¹ * x)) hf.aestronglyMeasurable hg'.aestronglyMeasurable
    have hEq : (fun y ↦ f y * g (y⁻¹ * x)) = f • fun y ↦ g (y⁻¹ * x) := by
      ext y
      simp [smul_eq_mul]
    simpa [hEq, hnorm] using hsmul
  refine ⟨hint, ?_⟩
  have hfin : eLpNorm f 2 μ * eLpNorm g 2 μ ≠ ⊤ :=
    ENNReal.mul_ne_top hf.eLpNorm_ne_top hg.eLpNorm_ne_top
  have hI : ‖∫ y, f y * g (y⁻¹ * x) ∂μ‖ₑ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
    calc
      ‖∫ y, f y * g (y⁻¹ * x) ∂μ‖ₑ
          ≤ ∫⁻ y, ‖f y * g (y⁻¹ * x)‖ₑ ∂μ :=
            eNorm_integral_le_lintegral_eNorm (fun y ↦ f y * g (y⁻¹ * x))
      _ ≤ eLpNorm (fun y ↦ f y * g (y⁻¹ * x)) 1 μ := lintegral_eNorm_le_eLpNorm_one
      _ ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := hprod
  simpa [lcaConvolution, toReal_eNorm', ENNReal.toReal_mul] using ENNReal.toReal_mono hfin hI

/-- Translation in `L²` makes the convolution of two `L²` functions continuous. -/
lemma continuous_lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    Continuous (lcaConvolution μ f g) := by
  haveI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨ENNReal.ofNat_ne_top⟩
  let gInv : G → ℂ := fun y ↦ g y⁻¹
  have hgInv : MemLp gInv 2 μ := hg.comp_measurePreserving (Measure.measurePreserving_inv μ)
  let F : Lp ℂ 2 μ := hf.toLp f
  let H : Lp ℂ 2 μ := hgInv.toLp gInv
  let pairing := (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2
  have hshift : Continuous fun x : G ↦ DomMulAct.mk x⁻¹ • H :=
    (continuous_smul (M := Gᵈᵐᵃ) (X := Lp ℂ 2 μ)).comp
      ((DomMulAct.continuous_mk.comp continuous_inv).prodMk continuous_const)
  have hcont : Continuous (fun x : G ↦ pairing F (DomMulAct.mk x⁻¹ • H)) :=
    (pairing F).continuous.comp hshift
  refine hcont.congr fun x ↦ ?_
  rw [ContinuousLinearMap.lpPairing_eq_integral, lcaConvolution]
  simp only [ContinuousLinearMap.mul_apply']
  apply integral_congr_ae
  have hF : (F : G → ℂ) =ᵐ[μ] f := hf.coeFn_toLp
  have hH : (H : G → ℂ) =ᵐ[μ] gInv := hgInv.coeFn_toLp
  have hleft : (fun y ↦ (H : G → ℂ) (x⁻¹ * y)) =ᵐ[μ] fun y ↦ gInv (x⁻¹ * y) :=
    (measurePreserving_mul_left μ x⁻¹).quasiMeasurePreserving.ae_eq_comp hH
  have hAct := DomMulAct.smul_Lp_ae_eq (DomMulAct.mk x⁻¹) H
  simp only [Equiv.symm_apply_apply, smul_eq_mul] at hAct
  have htrans : (DomMulAct.mk x⁻¹ • H : Lp ℂ 2 μ) =ᵐ[μ] fun y ↦ g (y⁻¹ * x) := by
    refine hAct.trans (hleft.trans ?_)
    filter_upwards with y
    simp [gInv, mul_inv_rev, inv_inv]
  filter_upwards [hF, htrans] with y hyF hyT
  simp only [hyF, hyT]

/-- Paper: Lemma D.1.1.2(3), p. 747. The fibre integrals of two L² functions
exist everywhere and give a continuous function vanishing at infinity with the product norm bound. -/
theorem lcaConvolution_L2 {f g : G → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∀ x, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ) ∧
      ∃ F : C₀(G, ℂ), (∀ x, F x = lcaConvolution μ f g x) ∧
        ‖F‖ ≤ (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have hint : ∀ x, Integrable (fun y ↦ f y * g (y⁻¹ * x)) μ :=
    fun x ↦ (integrable_lcaConvolution_L2 μ hf hg x).1
  have hpoint : ∀ x, ‖lcaConvolution μ f g x‖ ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal :=
    fun x ↦ (integrable_lcaConvolution_L2 μ hf hg x).2
  have hcont : Continuous (lcaConvolution μ f g) := continuous_lcaConvolution_L2 μ hf hg
  let A := (eLpNorm f 2 μ).toReal
  let B := (eLpNorm g 2 μ).toReal
  have hzero : Tendsto (lcaConvolution μ f g) (cocompact G) (𝓝 (0 : ℂ)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hCpos : 0 < A + B + 1 := by positivity
    let δr : ℝ := min 1 (ε / (2 * (A + B + 1)))
    have hδpos : 0 < δr := by
      have : 0 < ε / (2 * (A + B + 1)) := by positivity
      exact lt_min one_pos this
    have hδle : δr ≤ 1 := min_le_left _ _
    have hδmul : δr * (A + B + 1) ≤ ε / 2 := by
      have hle : δr ≤ ε / (2 * (A + B + 1)) := min_le_right _ _
      calc
        δr * (A + B + 1) ≤ ε / (2 * (A + B + 1)) * (A + B + 1) :=
          mul_le_mul_of_nonneg_right hle hCpos.le
        _ = ε / 2 := by field_simp [hCpos.ne']
    obtain ⟨f', hf'diff, hf'cont, hf'supp⟩ :=
      exists_hasCompactSupport_eLpNorm_sub_le (p := 2) ENNReal.ofNat_ne_top hf
        (ENNReal.ofReal_pos.mpr hδpos).ne'
    obtain ⟨g', hg'diff, hg'cont, hg'supp⟩ :=
      exists_hasCompactSupport_eLpNorm_sub_le (p := 2) ENNReal.ofNat_ne_top hg
        (ENNReal.ofReal_pos.mpr hδpos).ne'
    have hf' : MemLp f' 2 μ := hf'cont.memLp_of_hasCompactSupport (p := 2) hf'supp
    have hg' : MemLp g' 2 μ := hg'cont.memLp_of_hasCompactSupport (p := 2) hg'supp
    have hδf : (eLpNorm (f - f') 2 μ).toReal ≤ δr := by
      simpa [ENNReal.toReal_ofReal hδpos.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hf'diff
    have hδg : (eLpNorm (g - g') 2 μ).toReal ≤ δr := by
      simpa [ENNReal.toReal_ofReal hδpos.le] using
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hg'diff
    have hf'norm : (eLpNorm f' 2 μ).toReal ≤ A + δr := by
      have hle : eLpNorm f' 2 μ ≤ eLpNorm (f - f') 2 μ + eLpNorm f 2 μ := by
        calc
          eLpNorm f' 2 μ = eLpNorm (f + -(f - f')) 2 μ := by
            congr 1
            ext y
            simp [Pi.add_apply, Pi.sub_apply]
          _ ≤ eLpNorm f 2 μ + eLpNorm (-(f - f')) 2 μ :=
            eLpNorm_add_le (by norm_num : (1 : ℝ≥0∞) ≤ 2)
          _ = eLpNorm (f - f') 2 μ + eLpNorm f 2 μ := by rw [eLpNorm_neg, add_comm]
      have hfin1 : eLpNorm (f - f') 2 μ ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hf'diff
      have hfin : eLpNorm (f - f') 2 μ + eLpNorm f 2 μ ≠ ⊤ :=
        ENNReal.add_ne_top.2 ⟨hfin1, hf.eLpNorm_ne_top⟩
      calc
        (eLpNorm f' 2 μ).toReal ≤ (eLpNorm (f - f') 2 μ + eLpNorm f 2 μ).toReal :=
          ENNReal.toReal_mono hfin hle
        _ = (eLpNorm (f - f') 2 μ).toReal + A := by
          rw [ENNReal.toReal_add hfin1 hf.eLpNorm_ne_top]
        _ ≤ δr + A := by gcongr
        _ = A + δr := add_comm _ _
    open scoped Pointwise in
    let K := tsupport f' * tsupport g'
    have hK : IsCompact K := hf'supp.isCompact.mul hg'supp.isCompact
    rw [eventually_iff, mem_cocompact']
    refine ⟨K, hK, ?_⟩
    intro x hx
    have hx' : ¬ dist (lcaConvolution μ f g x) 0 < ε := by
      simpa [mem_compl_iff, mem_ofPred] using hx
    by_contra hxK
    have htail : lcaConvolution μ f' g' x = 0 := by
      rw [lcaConvolution]
      rw [show (fun y ↦ f' y * g' (y⁻¹ * x)) = (0 : G → ℂ) by
        ext y
        by_contra hne
        have hy1 : y ∈ tsupport f' :=
          subset_tsupport f' (Function.mem_support.2 (left_ne_zero_of_mul hne))
        have hy2 : y⁻¹ * x ∈ tsupport g' :=
          subset_tsupport g' (Function.mem_support.2 (right_ne_zero_of_mul hne))
        exact hxK ⟨y, hy1, y⁻¹ * x, hy2, mul_inv_cancel_left y x⟩]
      exact integral_zero _ _
    have hsplit : lcaConvolution μ f g x - lcaConvolution μ f' g' x =
        lcaConvolution μ (f - f') g x + lcaConvolution μ f' (g - g') x := by
      have h1 := (integrable_lcaConvolution_L2 μ (hf.sub hf') hg x).1
      have h2 := (integrable_lcaConvolution_L2 μ hf' (hg.sub hg') x).1
      simp only [lcaConvolution]
      have hfg := hint x
      have hfg' := (integrable_lcaConvolution_L2 μ hf' hg' x).1
      rw [← integral_sub hfg hfg', ← integral_add h1 h2]
      refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
      simp only [Pi.sub_apply]
      ring
    have hdist : ‖lcaConvolution μ f g x‖ ≤
        (eLpNorm (f - f') 2 μ).toReal * B + (eLpNorm f' 2 μ).toReal * (eLpNorm (g - g') 2 μ).toReal := by
      calc
        ‖lcaConvolution μ f g x‖ =
            ‖lcaConvolution μ f g x - lcaConvolution μ f' g' x‖ := by rw [htail, sub_zero]
        _ = ‖lcaConvolution μ (f - f') g x + lcaConvolution μ f' (g - g') x‖ := by rw [hsplit]
        _ ≤ ‖lcaConvolution μ (f - f') g x‖ + ‖lcaConvolution μ f' (g - g') x‖ := norm_add_le _ _
        _ ≤ (eLpNorm (f - f') 2 μ).toReal * (eLpNorm g 2 μ).toReal +
              (eLpNorm f' 2 μ).toReal * (eLpNorm (g - g') 2 μ).toReal :=
            add_le_add (integrable_lcaConvolution_L2 μ (hf.sub hf') hg x).2
              (integrable_lcaConvolution_L2 μ hf' (hg.sub hg') x).2
    have hsmall : ‖lcaConvolution μ f g x‖ < ε := by
      calc
        ‖lcaConvolution μ f g x‖ ≤
            (eLpNorm (f - f') 2 μ).toReal * B +
              (eLpNorm f' 2 μ).toReal * (eLpNorm (g - g') 2 μ).toReal := hdist
        _ ≤ δr * B + (A + δr) * δr := by
            gcongr
        _ ≤ δr * B + (A + 1) * δr := by
            gcongr
        _ = δr * (A + B + 1) := by ring
        _ ≤ ε / 2 := hδmul
        _ < ε := by linarith
    exact hx' <| by simpa [dist_zero_right] using hsmall
  let F : C₀(G, ℂ) :=
    { toFun := lcaConvolution μ f g
      continuous_toFun := hcont
      zero_at_infty' := hzero }
  refine ⟨hint, F, fun _ ↦ rfl, ?_⟩
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  exact (BoundedContinuousFunction.norm_le_of_nonempty (f := F.toBCF)).2 fun x ↦ by
    simpa [F, dist_eq_norm] using hpoint x

/-- Paper: Lemma D.1.1.2(4), p. 747. A Plancherel measure is a regular Haar measure
on the dual for which the Fourier transform preserves the finite L² norm on L¹ ∩ L². -/
def IsLCAPlancherelMeasure (μ : Measure G) (ν : Measure (PontryaginDual G)) : Prop :=
  ν.IsHaarMeasure ∧ ν.Regular ∧
    ∀ (f : G → ℂ), Integrable f μ → MemLp f 2 μ →
      MemLp (lcaFourier μ f) 2 ν ∧ eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ

/-- Paper: Lemma D.1.1.2(4), p. 747. On the one-point group the two
total masses must be reciprocals. -/
theorem isLCAPlancherelMeasure_subsingleton [Subsingleton G]
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular] :
    IsLCAPlancherelMeasure μ ν ↔ ν univ = (μ univ)⁻¹ := by
  let : Subsingleton (PontryaginDual G) :=
    ⟨fun χ ψ ↦ PontryaginDual.ext fun x ↦ by
      rw [Subsingleton.elim x 1, map_one, map_one]⟩
  have hμPos : 0 < μ univ := isOpen_univ.measure_pos μ univ_nonempty
  have hμTop : μ univ ≠ ⊤ := measure_ne_top μ univ
  have hμNorm : ‖μ.real univ‖ₑ = μ univ := by
    rw [← ofReal_norm, Measure.real, Real.norm_of_nonneg ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal hμTop
  have hFourier (c : ℂ) :
      lcaFourier μ (fun _ ↦ c) = fun _ ↦ μ.real univ • c := by
    funext χ
    rw [Subsingleton.elim χ 1, lcaFourier_one μ _ (integrable_const c), integral_const]
  have hScale :
      μ univ * ν univ ^ (1 / 2 : ℝ) =
        μ univ ^ (1 / 2 : ℝ) * (μ univ * ν univ) ^ (1 / 2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← mul_assoc,
      ← ENNReal.rpow_add _ _ hμPos.ne' hμTop]
    norm_num
  constructor
  · intro h
    have hNorm := (h.2.2 (fun _ ↦ (1 : ℂ)) (integrable_const _) (memLp_const _)).2
    simp only [hFourier, eLpNorm_const' _ two_ne_zero ENNReal.ofNat_ne_top,
      ENNReal.toReal_ofNat, eNorm_smul, hμNorm, eNorm_one, mul_one, one_mul, hScale] at hNorm
    have hCancel := (ENNReal.mul_right_inj
      (ENNReal.rpow_pos hμPos hμTop).ne'
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hμTop).ne).mp
      (hNorm.trans (mul_one _).symm)
    have hMass : μ univ * ν univ = 1 :=
      (ENNReal.strictMono_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)).injective
        (hCancel.trans (ENNReal.one_rpow _).symm)
    exact ENNReal.eq_inv_of_mul_eq_one_left ((mul_comm _ _).trans hMass)
  · intro h
    refine ⟨inferInstance, inferInstance, fun f _ _ ↦ ?_⟩
    have hf : f = fun _ ↦ f 1 := funext fun x ↦ congrArg f (Subsingleton.elim x 1)
    rw [hf, hFourier]
    refine ⟨memLp_const _, ?_⟩
    simp only [eLpNorm_const' _ two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
      eNorm_smul, hμNorm]
    rw [mul_comm (μ univ) ‖f 1‖ₑ, mul_assoc, hScale, h,
      ENNReal.mul_inv_cancel hμPos.ne' hμTop, ENNReal.one_rpow, mul_one]

omit [μ.Regular] in
/-- The Fourier norm of a single nonzero compactly supported test function fixes the
scalar between two regular Haar measures satisfying Plancherel. -/
private theorem isLCAPlancherelMeasure_unique
    {ν₁ ν₂ : Measure (PontryaginDual G)}
    (h₁ : IsLCAPlancherelMeasure μ ν₁) (h₂ : IsLCAPlancherelMeasure μ ν₂) : ν₁ = ν₂ := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let := h₁.1
  let := h₁.2.1
  let := h₂.1
  let := h₂.2.1
  let c := ν₁.haarScalarFactor ν₂
  have hc : ν₁ = c • ν₂ := Measure.isMulLeftInvariant_eq_smul_of_regular _ _
  obtain ⟨g, hgK, -, hg₁⟩ := exists_continuous_nonneg_pos (1 : G)
  let f : G → ℂ := fun x ↦ g x
  have hfC : Continuous f := Complex.continuous_ofReal.comp g.continuous
  have hfK : HasCompactSupport f := hgK.comp_left Complex.ofReal_zero
  have hf₁ := hfC.integrable_of_hasCompactSupport (μ := μ) hfK
  have hf₂ := hfC.memLp_of_hasCompactSupport (μ := μ) (p := 2) hfK
  have hnorm : eLpNorm f 2 μ ≠ 0 := by
    intro hzero
    have hae := (eLpNorm_eq_zero_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)).mp hzero
    have hEq : f = 0 := Measure.eq_of_ae_eq hae hfC continuous_const
    exact hg₁ (Complex.ofReal_eq_zero.mp (congrFun hEq 1))
  have hScale := (h₁.2.2 f hf₁ hf₂).2
  rw [hc, eLpNorm_smul_measure_of_ne_top' (by simp : (2 : ℝ≥0∞) ≠ ⊤) _
    _ (h₂.2.2 f hf₁ hf₂).1.aestronglyMeasurable, (h₂.2.2 f hf₁ hf₂).2] at hScale
  change (↑(c ^ ((2 : ℝ≥0∞).toReal)⁻¹) : ℝ≥0∞) * eLpNorm f 2 μ = eLpNorm f 2 μ at hScale
  rw [ENNReal.coe_rpow_of_nonneg _ (by positivity)] at hScale
  have hRoot : (c : ℝ≥0∞) ^ ((2 : ℝ≥0∞).toReal)⁻¹ = 1 :=
    (ENNReal.mul_left_inj hnorm hf₂.eLpNorm_ne_top).mp (hScale.trans (one_mul _).symm)
  have hc₁ : c = 1 := by
    apply ENNReal.coe_injective
    apply (ENNReal.strictMono_rpow_of_pos (by norm_num : 0 < ((2 : ℝ≥0∞).toReal)⁻¹)).injective
    simpa only [ENNReal.coe_one, ENNReal.one_rpow] using hRoot
  rw [hc, hc₁, one_smul]

/-- A Fourier norm identity for compactly supported continuous functions extends to
integrable square-integrable functions by approximation in both norms. -/
private theorem isLCAPlancherelMeasure_of_compactSupport
    (ν : Measure (PontryaginDual G)) [ν.IsHaarMeasure] [ν.Regular]
    (h : ∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
      eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ) :
    IsLCAPlancherelMeasure μ ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hp : 1 ≤ (2 : ℝ≥0∞) := by norm_num
  have hsub {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
      lcaFourier μ (f - g) = lcaFourier μ f - lcaFourier μ g := by
    funext χ
    simp only [lcaFourier, Pi.sub_apply, sub_mul]
    exact integral_sub (integrable_fourierIntegrand μ hf χ) (integrable_fourierIntegrand μ hg χ)
  have hApprox (f : G → ℂ) (hf₁ : Integrable f μ) (hf₂ : MemLp f 2 μ) :
      ∃ (g : ℕ → G → ℂ), (∀ n, Continuous (g n) ∧ HasCompactSupport (g n)) ∧
        Tendsto (fun n ↦ eLpNorm (g n - f) 2 μ) atTop (𝓝 0) ∧
        ∀ χ, Tendsto (fun n ↦ lcaFourier μ (g n) χ) atTop (𝓝 (lcaFourier μ f χ)) := by
    let ε (n : ℕ) : ℝ≥0∞ := ((n : ℝ≥0∞) + 1)⁻¹
    have hε : Tendsto ε atTop (𝓝 0) := by
      simpa only [ε, Function.comp_def, Nat.cast_add, Nat.cast_one] using
        ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
    choose g hgC hgK hg₁ hg₂ using fun n : ℕ ↦
      exists_hasCompactSupport_eLpNorm_sub_le_two le_rfl hp ENNReal.one_ne_top
        (by simp) (memLp_one_iff_integrable.mpr hf₁) hf₂ (ε := ε n) (by simp [ε])
    have hlim (p : ℝ≥0∞) (hg : ∀ n, eLpNorm (f - g n) p μ ≤ ε n) :
        Tendsto (fun n ↦ eLpNorm (g n - f) p μ) atTop (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hε (fun _ ↦ bot_le)
        (fun n ↦ (eLpNorm_sub_comm _ _ _ _).le.trans (hg n))
    refine ⟨g, fun n ↦ ⟨hgC n, hgK n⟩, hlim 2 hg₂, fun χ ↦ ?_⟩
    have hmem (n : ℕ) := ((hgC n).integrable_of_hasCompactSupport (μ := μ) (hgK n)).sub hf₁
    refine tendsto_iff_norm_sub_tendsto_zero.mpr ?_
    have hlim' := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hlim 1 hg₁)
    simp only [ENNReal.toReal_zero, Function.comp_def] at hlim'
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim'
      (fun _ ↦ norm_nonneg _) (fun n ↦ ?_)
    have hEq : (eLpNorm (g n - f) 1 μ).toReal = ∫ x, ‖(g n - f) x‖ ∂μ := by
      rw [eLpNorm_one_eq_lintegral_eNorm (hmem n).aestronglyMeasurable,
        ← ofReal_integral_norm_eq_lintegral_eNorm (hmem n),
        ENNReal.toReal_ofReal (integral_nonneg fun _ ↦ norm_nonneg _)]
    rw [hEq, ← Pi.sub_apply, ← hsub
      ((hgC n).integrable_of_hasCompactSupport (hgK n)) hf₁]
    exact norm_lcaFourier_le_integral_norm μ _ χ
  -- Pointwise convergence of the transforms and Fatou give the bound for arbitrary inputs.
  have hupper (f : G → ℂ) (hf₁ : Integrable f μ) (hf₂ : MemLp f 2 μ) :
      eLpNorm (lcaFourier μ f) 2 ν ≤ eLpNorm f 2 μ := by
    obtain ⟨g, hg, hlim₂, hlimF⟩ := hApprox f hf₁ hf₂
    have hg₁ (n : ℕ) : Integrable (g n) μ :=
      (hg n).1.integrable_of_hasCompactSupport (hg n).2
    have hg₂ (n : ℕ) : MemLp (g n) 2 μ := (hg n).1.memLp_of_hasCompactSupport (hg n).2
    have hnorm : Tendsto (fun n ↦ eLpNorm (g n) 2 μ) atTop (𝓝 (eLpNorm f 2 μ)) := by
      have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg₂ f hf₂).mpr hlim₂
      simpa only [Lp.eNorm_toLp] using ht.eNorm
    calc
      eLpNorm (lcaFourier μ f) 2 ν ≤ liminf (fun n ↦ eLpNorm (lcaFourier μ (g n)) 2 ν) atTop :=
        Lp.eLpNorm_lim_le_liminf_eLpNorm
          (fun n ↦ (continuous_lcaFourier μ (hg₁ n)).aestronglyMeasurable)
          _ (continuous_lcaFourier μ hf₁).aestronglyMeasurable (.of_forall hlimF)
      _ = eLpNorm f 2 μ := by
        simp_rw [h _ (hg _).1 (hg _).2]
        exact hnorm.liminf_eq
  refine ⟨inferInstance, inferInstance, fun f hf₁ hf₂ ↦ ?_⟩
  have hfF : MemLp (lcaFourier μ f) 2 ν :=
    (hupper f hf₁ hf₂).trans_lt hf₂.eLpNorm_lt_top
  obtain ⟨g, hg, hlim₂, -⟩ := hApprox f hf₁ hf₂
  have hg₁ (n : ℕ) : Integrable (g n) μ :=
    (hg n).1.integrable_of_hasCompactSupport (hg n).2
  have hg₂ (n : ℕ) : MemLp (g n) 2 μ := (hg n).1.memLp_of_hasCompactSupport (hg n).2
  have hgF (n : ℕ) : MemLp (lcaFourier μ (g n)) 2 ν :=
    (h (g n) (hg n).1 (hg n).2).trans_lt (hg₂ n).eLpNorm_lt_top
  -- The bound applied to differences gives convergence of the transformed sequence in L².
  have hlimF : Tendsto (fun n ↦ eLpNorm (lcaFourier μ (g n) - lcaFourier μ f) 2 ν)
      atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim₂
      (fun _ ↦ bot_le) (fun n ↦ ?_)
    rw [← hsub (hg₁ n) hf₁]
    exact hupper _ ((hg₁ n).sub hf₁) ((hg₂ n).sub hf₂)
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' g hg₂ f hf₂).mpr hlim₂
  have htF := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hgF _ hfF).mpr hlimF
  refine ⟨hfF, tendsto_nhds_unique (l := atTop)
    (f := fun n ↦ eLpNorm (lcaFourier μ (g n)) 2 ν) ?_ ?_⟩
  · simpa only [Lp.eNorm_toLp] using htF.eNorm
  · simp_rw [h _ (hg _).1 (hg _).2]
    simpa only [Lp.eNorm_toLp] using ht.eNorm

open scoped CompactlySupported in
/-- The autocorrelation of a continuous compactly supported function is the
Fourier–Stieltjes transform of a finite regular positive measure on the dual.
This is the autocorrelation case of Bochner's theorem. -/
theorem exists_lcaAutocorrelation_measure (f : C_c(G, ℂ)) :
    ∃ ρ : Measure (PontryaginDual G), IsFiniteMeasure ρ ∧ ρ.Regular ∧
      ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
        lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x := by
  sorry

open scoped CompactlySupported in
/-- Averaging the weighted spectral measures of two autocorrelations over dual
translations gives this identity on each measurable set. For a dual character `a`,
the spectral measure of `f` modulated by `a` is the translate of its spectral
measure by `a`. Weight that translate by the squared Fourier magnitude of `g`,
or weight the spectral measure of `g` by the shifted squared Fourier magnitude
of `f`. The two measures have the same Fourier–Stieltjes transform by
commutativity of convolution. Integrate the resulting identity over `a`
against the fixed Haar measure `η`. -/
theorem lcaAutocorrelation_measure_mul_lintegral
    (η : Measure (PontryaginDual G)) [η.IsHaarMeasure] [η.Regular]
    (f g : C_c(G, ℂ)) (ρ σ : Measure (PontryaginDual G))
    [IsFiniteMeasure ρ] [ρ.Regular] [IsFiniteMeasure σ] [σ.Regular]
    (hρ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
      lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x)
    (hσ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂σ) =
      lcaConvolution μ g (fun y ↦ star (g y⁻¹)) x)
    {s : Set (PontryaginDual G)} (hs : MeasurableSet s) :
    (∫⁻ χ, ‖lcaFourier μ f χ‖ₑ ^ 2 ∂η) * σ s =
      ρ univ * (∫⁻ χ in s, ‖lcaFourier μ g χ‖ₑ ^ 2 ∂η) := by
  sorry

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [μ.Regular] in
open scoped CompactlySupported in
/-- Evaluating the Fourier–Stieltjes representation at the identity identifies
the total mass with the integral of the squared source norm. -/
private theorem lcaAutocorrelation_measure_univ (f : C_c(G, ℂ))
    (ρ : Measure (PontryaginDual G)) [IsFiniteMeasure ρ]
    (hρ : ∀ x : G, (∫ χ, (χ x : ℂ) ∂ρ) =
      lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x) :
    ρ univ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have hSqC : Continuous (fun x ↦ ‖f x‖ ^ 2) := f.continuous.norm.pow 2
  have hSqK : HasCompactSupport (fun x ↦ ‖f x‖ ^ 2) :=
    f.hasCompactSupport.norm.comp_left (g := fun t : ℝ ↦ t ^ 2) (by simp)
  have hAuto : lcaConvolution μ f (fun y ↦ star (f y⁻¹)) 1 =
      ((∫ x, ‖f x‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [lcaConvolution, ← integral_complex_ofReal]
    apply integral_congr_ae
    exact .of_forall fun x ↦ by
      simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have h := congrArg Complex.re (hρ 1)
  simp only [map_one, Circle.coe_one, integral_const, Complex.real_smul, mul_one,
    Complex.ofReal_re, hAuto] at h
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ univ)]
  change ENNReal.ofReal (ρ.real univ) = _
  rw [h, ofReal_integral_eq_lintegral_ofReal (hSqC.integrable_of_hasCompactSupport hSqK)
    (.of_forall fun x ↦ sq_nonneg _)]
  exact lintegral_congr fun x ↦ by rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

open scoped CompactlySupported in
/-- A nonnegative compactly supported bump fixes the normalization of Haar measure
on the dual. Its spectral measure gives positive mass to a compact set, so the
averaging identity on that set ensures its squared Fourier integral is finite. -/
private theorem exists_lcaFourier_weighted_haar
    (ρ : C_c(G, ℂ) → Measure (PontryaginDual G))
    (hρ : ∀ f, IsFiniteMeasure (ρ f) ∧ (ρ f).Regular ∧
      ∀ x : G, (∫ χ, (χ x : ℂ) ∂(ρ f)) =
        lcaConvolution μ f (fun y ↦ star (f y⁻¹)) x) :
    ∃ ν : Measure (PontryaginDual G), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ f : C_c(G, ℂ), ν.withDensity (fun χ ↦ ‖lcaFourier μ f χ‖ₑ ^ 2) = ρ f := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let η : Measure (PontryaginDual G) := MeasureTheory.Measure.haar
  let (g : C_c(G, ℂ)) : IsFiniteMeasure (ρ g) := (hρ g).1
  let (g : C_c(G, ℂ)) : (ρ g).Regular := (hρ g).2.1
  obtain ⟨b, hbK, hb₀, hb₁⟩ := exists_continuous_nonneg_pos (1 : G)
  let f : C_c(G, ℂ) := ⟨⟨fun x ↦ (b x : ℂ), Complex.continuous_ofReal.comp b.continuous⟩,
    hbK.comp_left Complex.ofReal_zero⟩
  let w (g : C_c(G, ℂ)) (χ : PontryaginDual G) := ‖lcaFourier μ g χ‖ₑ ^ 2
  have hf₁ : f 1 ≠ 0 := Complex.ofReal_ne_zero.mpr hb₁
  have hw (g : C_c(G, ℂ)) : Continuous (w g) :=
    ENNReal.continuous_coe.comp ((continuous_lcaFourier μ g.integrable).nnNorm.pow 2)
  have hfSq : Continuous (fun x ↦ ‖f x‖ₑ ^ 2) :=
    ENNReal.continuous_coe.comp (f.continuous.nnNorm.pow 2)
  have hM : ρ f univ ≠ 0 := by
    rw [lcaAutocorrelation_measure_univ μ f (ρ f) (hρ f).2.2]
    apply ne_of_gt
    apply (lintegral_pos_iff_support hfSq.measurable).2
    exact (isOpen_ne_fun hfSq continuous_const).measure_pos μ
      ⟨1, show ‖f 1‖ₑ ^ 2 ≠ 0 by simpa using hf₁⟩
  have hF₁ : lcaFourier μ f 1 ≠ 0 := by
    rw [lcaFourier_one μ f f.integrable]
    change (∫ x, (b x : ℂ) ∂μ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr
      (b.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hbK hb₀ hb₁).ne'
  let I : ℝ≥0∞ := ∫⁻ χ, w f χ ∂η
  have hI₀ : I ≠ 0 := by
    apply ne_of_gt
    apply (lintegral_pos_iff_support (hw f).measurable).2
    exact (isOpen_ne_fun (hw f) continuous_const).measure_pos η
      ⟨1, show w f 1 ≠ 0 by simpa [w] using hF₁⟩
  obtain ⟨K, -, hK, hKpos⟩ := MeasurableSet.univ.exists_lt_isCompact (pos_iff_ne_zero.mpr hM)
  have hI_top : I ≠ ⊤ := by
    intro h
    have hAvg := lcaAutocorrelation_measure_mul_lintegral μ η f f (ρ f) (ρ f)
      (hρ f).2.2 (hρ f).2.2 hK.isClosed.measurableSet
    change I * ρ f K = ρ f univ * (∫⁻ χ in K, w f χ ∂η) at hAvg
    rw [h, ENNReal.top_mul hKpos.ne'] at hAvg
    have hBound (χ : PontryaginDual G) : w f χ ≤ ENNReal.ofReal (∫ x, ‖f x‖ ∂μ) ^ 2 := by
      change ‖lcaFourier μ f χ‖ₑ ^ 2 ≤ _
      rw [← ofReal_norm]
      exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal
        (norm_lcaFourier_le_integral_norm μ f χ)) _
    have hFinite : (∫⁻ χ in K, w f χ ∂η) < ⊤ := by
      refine (lintegral_mono hBound).trans_lt ?_
      rw [setLIntegral_const]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) hK.measure_lt_top
    exact (ENNReal.mul_lt_top (measure_lt_top (ρ f) univ) hFinite).ne hAvg.symm
  let c := ρ f univ * I⁻¹
  have hc₀ : c ≠ 0 := mul_ne_zero hM (ENNReal.inv_ne_zero.mpr hI_top)
  have hc_top : c ≠ ⊤ :=
    ENNReal.mul_ne_top (measure_ne_top (ρ f) univ) (ENNReal.inv_ne_top.mpr hI₀)
  refine ⟨c • η, Measure.IsHaarMeasure.smul η hc₀ hc_top, Measure.Regular.smul hc_top, ?_⟩
  intro g
  ext1 s hs
  have hAvg := lcaAutocorrelation_measure_mul_lintegral μ η f g (ρ f) (ρ g)
    (hρ f).2.2 (hρ g).2.2 hs
  change I * ρ g s = ρ f univ * (∫⁻ χ in s, w g χ ∂η) at hAvg
  change (c • η).withDensity (w g) s = _
  rw [withDensity_apply _ hs, setLIntegral_smul_measure, smul_eq_mul]
  calc
    c * (∫⁻ χ in s, w g χ ∂η) = I⁻¹ * (ρ f univ * (∫⁻ χ in s, w g χ ∂η)) := by
      dsimp [c]
      ac_rfl
    _ = ρ g s := by rw [← hAvg, ← mul_assoc, ENNReal.inv_mul_cancel hI₀ hI_top, one_mul]

open scoped CompactlySupported in
/-- There is a regular Haar measure on the dual for which the Fourier transform
preserves the L² norm of every continuous compactly supported function. It suffices
to construct this measure by Fourier inversion at the identity for autocorrelations
of such functions. -/
theorem exists_lcaFourier_eLpNorm_eq_of_hasCompactSupport :
    ∃ ν : Measure (PontryaginDual G), ν.IsHaarMeasure ∧ ν.Regular ∧
      ∀ (f : G → ℂ), Continuous f → HasCompactSupport f →
        eLpNorm (lcaFourier μ f) 2 ν = eLpNorm f 2 μ := by
  choose ρ hρ using exists_lcaAutocorrelation_measure μ
  obtain ⟨ν, hHaar, hRegular, hDensity⟩ := exists_lcaFourier_weighted_haar μ ρ hρ
  refine ⟨ν, hHaar, hRegular, fun f hf hs ↦ ?_⟩
  let g : C_c(G, ℂ) := ⟨⟨f, hf⟩, hs⟩
  let : IsFiniteMeasure (ρ g) := (hρ g).1
  have hMass : ρ g univ = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ :=
    lcaAutocorrelation_measure_univ μ g (ρ g) (hρ g).2.2
  have hSqEq : (∫⁻ χ, ‖lcaFourier μ f χ‖ₑ ^ 2 ∂ν) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
    have h := congrArg (fun m : Measure (PontryaginDual G) ↦ m univ) (hDensity g)
    change (ν.withDensity (fun χ ↦ ‖lcaFourier μ f χ‖ₑ ^ 2)) univ = ρ g univ at h
    rwa [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hMass] at h
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  have hFourier := continuous_lcaFourier μ (hf.integrable_of_hasCompactSupport (μ := μ) hs)
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hFourier.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  rw [hSqEq]

/-- Paper: Lemma D.1.1.2(4), p. 747. There is exactly one Plancherel measure. -/
theorem lcaPlancherelMeasure_existsUnique :
    ∃! ν : Measure (PontryaginDual G), IsLCAPlancherelMeasure μ ν := by
  obtain ⟨ν, hHaar, hReg, hNorm⟩ := exists_lcaFourier_eLpNorm_eq_of_hasCompactSupport μ
  let := hHaar
  let := hReg
  have hν := isLCAPlancherelMeasure_of_compactSupport μ ν hNorm
  exact ⟨ν, hν, fun ν' hν' ↦ isLCAPlancherelMeasure_unique μ hν' hν⟩

/-- The range of an L² Fourier isometry has trivial orthogonal complement.
Orthogonality to translates of each integrable test function forces the product of its
conjugated transform with the orthogonal vector to vanish almost everywhere. -/
private theorem lcaFourier_isometry_surjective
    {ν : Measure (PontryaginDual G)} [ν.Regular]
    (U : Lp ℂ 2 μ →ₗᵢ[ℂ] Lp ℂ 2 ν)
    (hU : ∀ (f : G → ℂ), Integrable f μ → ∀ (h₂ : MemLp f 2 μ),
      (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f) :
    Function.Surjective U := by
  classical
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let R := U.toLinearMap.range
  have hClosed : IsClosed (R : Set (Lp ℂ 2 ν)) := U.isometry.isClosedEmbedding.isClosed_range
  let : CompleteSpace R := hClosed.isComplete.completeSpace_coe
  suffices R = ⊤ from LinearMap.range_eq_top.mp this
  refine Submodule.orthogonal_eq_bot_iff.mp ((Submodule.eq_bot_iff _).mpr ?_)
  intro g hg
  have hInner (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ) :
      ∫ χ, g χ * star (lcaFourier μ f χ) ∂ν = 0 := by
    have hZero := (R.mem_orthogonal g).mp hg _ (U.toLinearMap.mem_range_self (h₂.toLp f))
    change inner ℂ (U (h₂.toLp f)) g = 0 at hZero
    rw [L2.inner_def] at hZero
    refine (integral_congr_ae ((hU f hf h₂).mono fun χ hχ ↦ ?_)).trans hZero
    rw [RCLike.inner_apply, starRingEnd_apply, hχ]
  have hProduct (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ) :
      (fun χ ↦ g χ * star (lcaFourier μ f χ)) =ᵐ[ν] 0 := by
    have hInt : Integrable (fun χ ↦ g χ * star (lcaFourier μ f χ)) ν :=
      (L2.integrable_inner (𝕜 := ℂ) (U (h₂.toLp f)) g).congr
        ((hU f hf h₂).mono fun χ hχ ↦ by
          change inner ℂ (U (h₂.toLp f) χ) (g χ) = _
          rw [RCLike.inner_apply, starRingEnd_apply, hχ])
    refine ae_eq_zero_of_integral_mul_circle_eq_zero (X := PontryaginDual G) (D := G)
      (fun χ : PontryaginDual G ↦ χ.toMonoidHom)
      (fun a ↦ (continuous_eval_const (F := C(G, Circle)) a).comp
        (ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous)
      (fun _ _ h ↦ PontryaginDual.ext (fun a ↦ congrArg (fun k : G →* Circle ↦ k a) h))
      hInt ?_
    intro a
    let m := measurePreserving_mul_left μ a⁻¹
    have hZero := hInner (fun x ↦ f (a⁻¹ * x)) (m.integrable_comp_of_integrable hf)
      (h₂.comp_measurePreserving m)
    refine (integral_congr_ae (.of_forall fun χ ↦ ?_)).trans hZero
    change g χ * star (lcaFourier μ f χ) * (χ a : ℂ) = _
    rw [lcaFourier_translate μ f a⁻¹ χ, star_mul, map_inv, Circle.coe_inv_eq_conj,
      ← Complex.star_def, star_star]
    ring
  -- A modulated indicator of a compact neighborhood gives a transform nonzero at each point.
  obtain ⟨K, hK, hK₁⟩ := exists_compact_mem_nhds (1 : G)
  have hKm := hK.isClosed.measurableSet
  have hKfin := (hK.measure_lt_top (μ := μ)).ne
  have hKpos : 0 < μ K := (isOpen_interior.measure_pos μ
    ⟨1, mem_interior_iff_mem_nhds.mpr hK₁⟩).trans_le (measure_mono interior_subset)
  let : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.mpr hKfin
  let f (ψ : PontryaginDual G) : G → ℂ := K.indicator fun x ↦ (ψ x : ℂ)
  have hfLp (ψ : PontryaginDual G) (p : ℝ≥0∞) : MemLp (f ψ) p μ :=
    (memLp_indicator_iff_restrict hKm.nullMeasurableSet).mpr <|
      MemLp.of_bound (continuous_subtype_val.comp ψ.continuous).aestronglyMeasurable
        1 (.of_forall fun x ↦ (Circle.norm_coe (ψ x)).le)
  have hf (ψ : PontryaginDual G) : Integrable (f ψ) μ :=
    memLp_one_iff_integrable.mp (hfLp ψ 1)
  have hNonzero (ψ : PontryaginDual G) : lcaFourier μ (f ψ) ψ ≠ 0 := by
    unfold lcaFourier
    rw [show (fun x ↦ f ψ x * star (ψ x : ℂ)) = K.indicator (fun _ ↦ (1 : ℂ)) by
      funext x
      by_cases hx : x ∈ K
      · simp only [f, indicator_of_mem hx, Complex.star_def, Complex.mul_conj,
          Complex.normSq_eq_norm_sq, Circle.norm_coe, one_pow, Complex.ofReal_one]
      · simp [f, hx]]
    rw [integral_indicator hKm, integral_const, Measure.real, Measure.restrict_apply_univ,
      Complex.real_smul, mul_one]
    exact Complex.ofReal_ne_zero.mpr (ENNReal.toReal_pos hKpos.ne' hKfin).ne'
  let O (ψ : PontryaginDual G) := {χ | lcaFourier μ (f ψ) χ ≠ 0}
  have hOpen (ψ : PontryaginDual G) : IsOpen (O ψ) :=
    isOpen_ne_fun (continuous_lcaFourier μ (hf ψ)) continuous_const
  have hLocal (ψ : PontryaginDual G) : ∀ᵐ χ ∂ν.restrict (O ψ), g χ = 0 := by
    filter_upwards [ae_restrict_of_ae (hProduct (f ψ) (hf ψ) (hfLp ψ 2)),
      ae_restrict_mem (hOpen ψ).measurableSet] with χ hχ hmem
    exact (mul_eq_zero.mp hχ).resolve_right (star_ne_zero.mpr hmem)
  have hCompact (L : Set (PontryaginDual G)) (hL : IsCompact L) :
      ∀ᵐ χ ∂ν.restrict L, g χ = 0 := by
    obtain ⟨t, -, ht⟩ := hL.elim_nhds_subcover O (fun ψ _ ↦ (hOpen ψ).mem_nhds (hNonzero ψ))
    exact ae_mono (Measure.restrict_mono ht le_rfl)
      ((ae_restrict_biUnion_finset_iff O t _).mpr (fun ψ _ ↦ hLocal ψ))
  -- Compact approximation of the integrable squared norm avoids a countability assumption.
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [L2.inner_def]
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply le_of_forall_pos_lt_add
  intro ε hε
  let q (χ : PontryaginDual G) := inner ℂ (g χ) (g χ)
  have hq : Integrable q ν := L2.integrable_inner g g
  obtain ⟨L, -, hL, hTail⟩ := exists_isCompact_integral_norm_sdiff_lt hq MeasurableSet.univ hε
  have hZero : ∫ χ in L, q χ ∂ν = 0 := by
    have hqZero : q =ᵐ[ν.restrict L] (0 : PontryaginDual G → ℂ) :=
      (hCompact L hL).mono fun χ hχ ↦ by simp [q, hχ]
    rw [integral_congr_ae hqZero, Pi.zero_def, integral_zero]
  have hEq : (∫ χ, q χ ∂ν) = ∫ χ in Lᶜ, q χ ∂ν := by
    rw [← integral_add_compl hL.isClosed.measurableSet hq, hZero, zero_add]
  change ‖∫ χ, q χ ∂ν‖ < 0 + ε
  rw [hEq, zero_add]
  exact (norm_integral_le_integral_norm q).trans_lt (by rwa [← compl_eq_univ_sdiff] at hTail)

/-- Paper: Lemma D.1.1.2(4), p. 747. The Fourier transform on L¹ ∩ L²
extends uniquely to a unitary isomorphism on L². -/
theorem lcaFourier_unitary (ν : Measure (PontryaginDual G))
    (hν : IsLCAPlancherelMeasure μ ν) :
    ∃! U : Lp ℂ 2 μ ≃ₗᵢ[ℂ] Lp ℂ 2 ν,
      ∀ (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ),
        (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by
  let : ν.Regular := hν.2.1
  let D : Submodule ℂ (Lp ℂ 2 μ) :=
    { carrier := {f | Integrable (f : G → ℂ) μ}
      zero_mem' := (integrable_zero G ℂ μ).congr (Lp.coeFn_zero ℂ 2 μ).symm
      add_mem' := fun {_ _} hf hg ↦ (hf.add hg).congr (Lp.coeFn_add _ _).symm
      smul_mem' := fun c _ hf ↦ (hf.smul c).congr (Lp.coeFn_smul c _).symm }
  have hDense : DenseRange D.subtype := by
    apply (Lp.simpleFunc.dense (E := ℂ) (p := 2) (μ := μ) ENNReal.ofNat_ne_top).mono
    intro f hf
    let g : Lp.simpleFunc ℂ 2 μ := ⟨f, hf⟩
    have hInt : Integrable (Lp.simpleFunc.toSimpleFunc g) μ :=
      (SimpleFunc.memLp_iff_integrable two_ne_zero ENNReal.ofNat_ne_top).mp (Lp.simpleFunc.memLp g)
    exact ⟨⟨f, hInt.congr (Lp.simpleFunc.toSimpleFunc_eq_toFun g)⟩, rfl⟩
  have hPlancherel (f : D) := hν.2.2 f f.2 (Lp.memLp (f : Lp ℂ 2 μ))
  let transform (f : D) : Lp ℂ 2 ν := (hPlancherel f).1.toLp (lcaFourier μ f)
  have hTransform (f : D) : (transform f : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f :=
    MemLp.coeFn_toLp _
  let F : D →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := transform
      map_add' f g := by
        apply Lp.ext
        filter_upwards [hTransform (f + g), hTransform f, hTransform g,
          Lp.coeFn_add (transform f) (transform g)] with χ hfg hf hg hAdd
        change transform (f + g) χ = (transform f + transform g) χ
        rw [hfg, hAdd, Pi.add_apply, hf, hg]
        unfold lcaFourier
        calc
          _ = ∫ x, ((f : Lp ℂ 2 μ) x + (g : Lp ℂ 2 μ) x) * star (χ x : ℂ) ∂μ :=
            integral_congr_ae ((Lp.coeFn_add (f : Lp ℂ 2 μ) g).mono fun x hx ↦ by
              change ((f : Lp ℂ 2 μ) + (g : Lp ℂ 2 μ)) x * _ = _
              rw [hx]
              rfl)
          _ = _ := by
            simp_rw [add_mul]
            exact integral_add (integrable_fourierIntegrand μ f.2 χ)
              (integrable_fourierIntegrand μ g.2 χ)
      map_smul' c f := by
        apply Lp.ext
        filter_upwards [hTransform (c • f), hTransform f, Lp.coeFn_smul c (transform f)]
          with χ hcf hf hSmul
        change transform (c • f) χ = (c • transform f) χ
        rw [hcf, hSmul, Pi.smul_apply, hf]
        unfold lcaFourier
        calc
          _ = ∫ x, c • ((f : Lp ℂ 2 μ) x * star (χ x : ℂ)) ∂μ :=
            integral_congr_ae ((Lp.coeFn_smul c (f : Lp ℂ 2 μ)).mono fun x hx ↦ by
              change ((c • (f : Lp ℂ 2 μ)) : Lp ℂ 2 μ) x * _ = _
              rw [hx, Pi.smul_apply]
              exact smul_mul_assoc _ _ _)
          _ = _ := integral_smul c _ }
  have hNorm (f : D) : ‖F f‖ = ‖D.subtype f‖ := by
    change ‖(hPlancherel f).1.toLp (lcaFourier μ f)‖ = ‖(f : Lp ℂ 2 μ)‖
    rw [Lp.norm_toLp, Lp.norm_def, (hPlancherel f).2]
  let U := F.extendOfIsometry hDense hNorm
  have hU (f : G → ℂ) (hf : Integrable f μ) (h₂ : MemLp f 2 μ) :
      (U (h₂.toLp f) : PontryaginDual G → ℂ) =ᵐ[ν] lcaFourier μ f := by
    let x : D := ⟨h₂.toLp f, hf.congr h₂.coeFn_toLp.symm⟩
    have hEq : U (D.subtype x) = F x := F.extendOfIsometry_eq hDense hNorm x
    change (U (D.subtype x) : PontryaginDual G → ℂ) =ᵐ[ν] _
    rw [hEq]
    refine (hTransform x).trans (.of_forall fun χ ↦ integral_congr_ae ?_)
    exact h₂.coeFn_toLp.mono fun y hy ↦ by change _ * _ = _ * _; rw [hy]
  let e := LinearIsometryEquiv.ofSurjective U (lcaFourier_isometry_surjective μ U hU)
  refine ⟨e, hU, fun V hV ↦ ?_⟩
  apply LinearIsometryEquiv.ext
  intro f
  refine hDense.induction_on (p := fun w ↦ V w = e w) f
    (isClosed_eq V.continuous e.continuous) fun x ↦ ?_
  have hx := Lp.memLp (x : Lp ℂ 2 μ)
  have hEq : hx.toLp (x : G → ℂ) = D.subtype x := Lp.toLp_coeFn _ hx
  rw [← hEq]
  exact Lp.ext ((hV x x.2 hx).trans (hU x x.2 hx).symm)

-- TODO(paper-gap): Lemma D.1.1.2(5) asserts continuity and pointwise inversion for an
-- arbitrary measurable representative. A nonzero function supported at one point of
-- the real line has zero transform, and its double transform is everywhere zero.

/-- The integral of an L¹ convolution is the product of the integrals of its factors. -/
private theorem integral_lcaConvolution {f g : G → ℂ} (hf : Integrable f μ)
    (hg : Integrable g μ) :
    (∫ x, lcaConvolution μ f g x ∂μ) = (∫ y, f y ∂μ) * (∫ z, g z ∂μ) := by
  obtain ⟨S, k, hσ, hk, hs, hrow, hcol⟩ := lcaConvolution_kernel μ hf hg
  have hzeroRow (x : G) (hx : x ∉ S) (y : G) : k (x, y) = 0 :=
    Function.notMem_support.mp fun h ↦ hx (hs h).1
  have hzeroCol (y : G) (hy : y ∉ S) (x : G) : k (x, y) = 0 :=
    Function.notMem_support.mp fun h ↦ hy (hs h).2
  -- Fubini applies to the kernel on its σ-finite supporting rectangle.
  have hInt : Integrable k ((μ.restrict S).prod (μ.restrict S)) := by
    refine (integrable_prod_iff' hk.aestronglyMeasurable).2 ⟨?_, ?_⟩
    · apply ae_mono Measure.restrict_le_self
      filter_upwards [hcol] with y hy
      exact (((hg.comp_mul_left y⁻¹).const_mul (f y)).congr
        (hy.mono fun _ hx ↦ hx.symm)).restrict
    · refine (hf.norm.mul_const (∫ z, ‖g z‖ ∂μ)).restrict.congr ?_
      apply ae_mono Measure.restrict_le_self
      filter_upwards [hcol] with y hy
      symm
      calc
        _ = ∫ x, ‖k (x, y)‖ ∂μ := setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun x hx ↦ by simp [hzeroRow x hx])
        _ = ∫ x, ‖f y * g (y⁻¹ * x)‖ ∂μ :=
          integral_congr_ae (hy.mono fun _ hx ↦ congrArg norm hx)
        _ = _ := by
          simp only [norm_mul, integral_const_mul, integral_mul_left_eq_self (fun z ↦ ‖g z‖)]
  have hrowIntegral (x : G) : (∫ y in S, k (x, y) ∂μ) = lcaConvolution μ f g x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroCol · · x)).trans
      (integral_congr_ae (hrow x))
  calc
    _ = ∫ x in S, ∫ y in S, k (x, y) ∂μ ∂μ := by
      simp_rw [← hrowIntegral]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ by simp [hzeroRow x hx])).symm
    _ = ∫ y in S, ∫ x in S, k (x, y) ∂μ ∂μ := integral_integral_swap hInt
    _ = ∫ y, ∫ x, k (x, y) ∂μ ∂μ := by
      have hcolIntegral (y : G) : (∫ x in S, k (x, y) ∂μ) = ∫ x, k (x, y) ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (hzeroRow · · y)
      simp_rw [hcolIntegral]
      exact setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun y hy ↦ by simp [hzeroCol y hy])
    _ = _ := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [hcol] with y hy
      rw [integral_congr_ae hy, integral_const_mul, integral_mul_left_eq_self g]

/-- Paper: Lemma D.1.1.2(6), p. 747. The Fourier transform takes L¹ convolution
to pointwise multiplication on the dual. -/
theorem lcaFourier_convolution {f g : G → ℂ} (hf : Integrable f μ) (hg : Integrable g μ) :
    lcaFourier μ (lcaConvolution μ f g) = lcaFourier μ f * lcaFourier μ g := by
  funext χ
  change (∫ x, lcaConvolution μ f g x * star (χ x : ℂ) ∂μ) =
    (∫ x, f x * star (χ x : ℂ) ∂μ) * (∫ x, g x * star (χ x : ℂ) ∂μ)
  rw [← integral_lcaConvolution μ (integrable_fourierIntegrand μ hf χ)
    (integrable_fourierIntegrand μ hg χ)]
  apply integral_congr_ae
  exact .of_forall fun x ↦ by
    simp only [lcaConvolution, ← integral_mul_const]
    apply integral_congr_ae
    exact .of_forall fun y ↦ by
      have hχ : (χ x : ℂ) = (χ y : ℂ) * (χ (y⁻¹ * x) : ℂ) := by
        rw [← Circle.coe_mul, ← map_mul, mul_inv_cancel_left]
      rw [hχ, star_mul]
      ring

end Fourier

section Weil

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
variable (H : Subgroup G) (hH : IsClosed (H : Set G))

local instance : MeasurableSpace (G ⧸ H) := borel _

/-- Paper: (D.1.2.1), p. 747. Integrate over the translate of the subgroup represented
by a quotient point. The representative is chosen by `Quotient.out`. -/
def lcaCosetIntegral (μH : Measure H) (f : G → ℂ) (q : G ⧸ H) : ℂ :=
  ∫ h : H, f (q.out * (h : G)) ∂μH

/-- Paper: (D.1.2.1), p. 747. If the fibre is integrable at a representative,
the quotient integral agrees with integration using that representative. -/
theorem lcaCosetIntegral_mk (μH : Measure H) [μH.IsHaarMeasure] (f : G → ℂ) (x : G)
    (hf : Integrable (fun h : H ↦ f (x * (h : G))) μH) :
    lcaCosetIntegral H μH f (QuotientGroup.mk x) =
      ∫ h : H, f (x * (h : G)) ∂μH := by
  rw [lcaCosetIntegral]
  set y : G := Quotient.out (QuotientGroup.mk x) with hydef
  have hy : QuotientGroup.mk y = QuotientGroup.mk x := Quotient.out_eq' _
  have hk : y⁻¹ * x ∈ H := QuotientGroup.eq.mp hy
  let k : H := ⟨y⁻¹ * x, hk⟩
  have hxe : x = y * (k : G) := by
    simp [k]
  rw [hxe]
  have hassoc : ∀ h : H, y * (k : G) * (h : G) = y * ((k * h : H) : G) := by
    intro h
    rw [Subgroup.coe_mul, mul_assoc]
  simp_rw [hassoc]
  exact (MeasureTheory.integral_mul_left_eq_self (fun h : H ↦ f (y * (h : G))) k).symm

/-- Paper: Theorem D.1.2.1, p. 747. A regular Haar measure on the quotient
is normalized by Weil's formula on continuous compactly supported test functions. -/
def IsWeilQuotientMeasure (μ : Measure G) (μH : Measure H) (ν : Measure (G ⧸ H)) : Prop :=
  ν.IsHaarMeasure ∧ ν.Regular ∧
    ∀ f : C(G, ℂ), HasCompactSupport f →
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν

/-- Paper: Theorem D.1.2.1, p. 747. Taking the quotient by the trivial
subgroup, normalized to mass one, recovers the pushforward of the group measure. -/
theorem isWeilQuotientMeasure_bot (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular] :
    IsWeilQuotientMeasure (⊥ : Subgroup G) μ Measure.count
      (μ.map (QuotientGroup.mk : G → G ⧸ (⊥ : Subgroup G))) := by
  let : BorelSpace (G ⧸ (⊥ : Subgroup G)) := ⟨rfl⟩
  let e := (QuotientGroup.quotientBot (G := G)).symm
  let h := e.toEquiv.toHomeomorphOfContinuousOpen
    QuotientGroup.continuous_mk QuotientGroup.isOpenMap_coe
  refine ⟨e.isHaarMeasure_map μ h.continuous h.symm.continuous, Measure.Regular.map h, ?_⟩
  intro f _
  have hcoset (q : G ⧸ (⊥ : Subgroup G)) :
      lcaCosetIntegral (⊥ : Subgroup G) Measure.count f q = f (h.symm q) := by
    have hout : q.out = h.symm q :=
      h.injective ((Quotient.out_eq' q).trans (h.apply_symm_apply q).symm)
    simp [lcaCosetIntegral, Subsingleton.count_eq_dirac (1 : (⊥ : Subgroup G)), hout]
  simp_rw [hcoset]
  change (∫ x, f x ∂μ) = ∫ q, f (h.symm q) ∂(μ.map h)
  simpa only [Homeomorph.toMeasurableEquiv_coe, h.symm_apply_apply] using
    (integral_map_equiv (μ := μ) h.toMeasurableEquiv (fun q ↦ f (h.symm q))).symm

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
variable (μH : Measure H) [μH.IsHaarMeasure] [μH.Regular]

include hH in
/-- Paper: Theorem D.1.2.1, p. 747. There is a unique quotient Haar measure
satisfying Weil's formula for compactly supported continuous functions. -/
theorem weilQuotientMeasure_existsUnique :
    ∃! ν : Measure (G ⧸ H), IsWeilQuotientMeasure H μ μH ν := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : IsClosed (H : Set G) := hH
  let h := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let ν₀ : Measure (G ⧸ H) := MeasureTheory.Measure.haar
  let μ₀ := h.inducedMeasure μH ν₀
  let c := Measure.haarScalarFactor μ μ₀
  have hc : c ≠ 0 := (Measure.haarScalarFactor_pos_of_isHaarMeasure μ μ₀).ne'
  have hμ : μ = c • μ₀ := Measure.isMulLeftInvariant_eq_smul_of_regular μ μ₀
  let ν := c • ν₀
  let hνH : ν.IsHaarMeasure := Measure.IsHaarMeasure.nnreal_smul ν₀ hc
  have hν : IsWeilQuotientMeasure H μ μH ν := by
    refine ⟨hνH, inferInstance, ?_⟩
    intro f hf
    let f' : CompactlySupportedContinuousMap G ℂ := ⟨f, hf⟩
    have hfib (q : G ⧸ H) : h.pushforward μH f' q = lcaCosetIntegral H μH f q := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change h.pushforward μH f' ((QuotientGroup.mk' H) x) = _
      rw [h.pushforward_apply_apply]
      exact (lcaCosetIntegral_mk H μH f x (h.pullback f' x).integrable).symm
    change (∫ x, f' x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂(c • ν₀)
    rw [hμ, integral_smul_nnreal_measure, integral_smul_nnreal_measure,
      integral_inducedMeasure_complex h μH ν₀ f', h.integrate_apply]
    simp_rw [hfib]
  refine ⟨ν, hν, ?_⟩
  intro ν' hν'
  let : ν'.IsHaarMeasure := hν'.1
  let : ν'.Regular := hν'.2.1
  let d := Measure.haarScalarFactor ν' ν
  have hνeq : ν' = d • ν := Measure.isMulLeftInvariant_eq_smul_of_regular ν' ν
  obtain ⟨g, hg, hnonneg, hpos⟩ := exists_continuous_nonneg_pos (1 : G)
  let f : C(G, ℂ) := ⟨fun x ↦ (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
  have hf : HasCompactSupport (f : G → ℂ) := hg.comp_left Complex.ofReal_zero
  have hI : (∫ x, f x ∂μ) ≠ 0 := by
    change (∫ x, (g x : ℂ) ∂μ) ≠ 0
    rw [integral_complex_ofReal]
    exact Complex.ofReal_ne_zero.mpr (g.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
      hg hnonneg hpos).ne'
  have hscalar := hν'.2.2 f hf
  rw [hνeq, integral_smul_nnreal_measure, ← hν.2.2 f hf] at hscalar
  have hunit : d = 1 := by
    have he : (1 : ℂ) * (∫ x, f x ∂μ) = ((d : ℝ) : ℂ) * (∫ x, f x ∂μ) := by
      simpa only [one_mul, NNReal.smul_def, Complex.real_smul] using hscalar
    exact_mod_cast (mul_right_cancel₀ hI he).symm
  simpa [hunit] using hνeq

-- TODO(paper-gap): Theorem D.1.2.1 also asserts a.e. existence of the fibre integral
-- for every measurable function. For H = G = ℝ and f = 1, the sole fibre has infinite integral.

include hH in
/-- Left Haar measure of a fibre does not depend on the representative of the coset. -/
lemma fibreMeasure_eq_of_mk_eq {U : Set G} {x y : G}
    (hxy : (QuotientGroup.mk x : G ⧸ H) = QuotientGroup.mk y) :
    μH {h : H | x * (h : G) ∈ U} = μH {h : H | y * (h : G) ∈ U} := by
  have hk : x⁻¹ * y ∈ H := QuotientGroup.eq.mp hxy
  let k : H := ⟨x⁻¹ * y, hk⟩
  have hy : y = x * (k : G) := by simp [k]
  have hset :
      {h : H | y * (h : G) ∈ U} =
        (fun h : H => k * h) ⁻¹' {h : H | x * (h : G) ∈ U} := by
    ext h
    simp only [mem_preimage, Set.mem_setOf_eq, hy, Subgroup.coe_mul, mul_assoc]
  have hembed : MeasurableEmbedding (fun h : H => k * h) :=
    (Homeomorph.mulLeft k).measurableEmbedding
  rw [hset, ← hembed.map_apply, map_mul_left_eq_self]

open scoped Pointwise in
include hH in
/-- The fibre measure of an open set, as a function on the quotient, is lower semicontinuous. -/
lemma fibreMeasure_open_lowerSemicontinuous {U : Set G} (hU : IsOpen U) :
    LowerSemicontinuous fun q : G ⧸ H => μH {h : H | q.out * (h : G) ∈ U} := by
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro r
  rw [isOpen_iff_mem_nhds]
  intro q hq
  let x : G := q.out
  have hxq : QuotientGroup.mk x = q := Quotient.out_eq' q
  let V : Set H := {h : H | x * (h : G) ∈ U}
  have hVopen : IsOpen V :=
    hU.preimage ((continuous_const_mul x).comp continuous_subtype_val)
  have hVr : r < μH V := by simpa [V, x] using hq
  obtain ⟨K, hKV, hKc, hKμ⟩ :=
    (Measure.Regular.innerRegular (μ := μH)) hVopen r hVr
  let ι : H → G := fun h => x * (h : G)
  have hι : Continuous ι := (continuous_const_mul x).comp continuous_subtype_val
  have hKG : IsCompact (ι '' K) := hKc.image hι
  have hKGU : ι '' K ⊆ U := by
    rintro _ ⟨h, hh, rfl⟩
    exact hKV hh
  obtain ⟨W, hW, hWK⟩ := compact_open_separated_mul_left hKG hU hKGU
  have hWx : (fun v : G => v * x) '' W ∈ 𝓝 x := by
    have hmem : (Homeomorph.mulRight x) '' W ∈ 𝓝 (Homeomorph.mulRight x 1) := by
      rw [← (Homeomorph.mulRight x).map_nhds_eq (1 : G)]
      exact image_mem_map hW
    simpa [Homeomorph.coe_mulRight] using hmem
  have hπ : 𝓝 q = Filter.map (QuotientGroup.mk : G → G ⧸ H) (𝓝 x) := by
    simpa [hxq] using QuotientGroup.nhds_eq H x
  refine mem_of_superset (by
      rw [hπ]
      exact image_mem_map (m := (QuotientGroup.mk : G → G ⧸ H)) hWx) ?_
  rintro _ ⟨y, hyW, rfl⟩
  rw [mem_preimage, mem_Ioi]
  rcases hyW with ⟨v, hv, rfl⟩
  have hKy : K ⊆ {h : H | (v * x) * (h : G) ∈ U} := by
    intro h hh
    have hvK : v * (x * (h : G)) ∈ W * (ι '' K) := by
      exact Set.mul_mem_mul hv ⟨h, hh, rfl⟩
    simpa [mul_assoc] using hWK hvK
  have hle : μH K ≤ μH {h : H | (v * x) * (h : G) ∈ U} := measure_mono hKy
  have hinv := fibreMeasure_eq_of_mk_eq H hH μH (U := U) (x := v * x)
    (y := (QuotientGroup.mk (v * x)).out)
    (Quotient.out_eq' (QuotientGroup.mk (v * x))).symm
  simpa [hinv] using hKμ.trans_le hle

include hH in
/-- Fibre integrals of a compactly supported continuous function are continuous on the quotient. -/
lemma continuous_realFibreIntegral {g : G → ℝ} (hg : Continuous g) (hgs : HasCompactSupport g) :
    Continuous fun q : G ⧸ H => ∫ h : H, g (q.out * (h : G)) ∂μH := by
  haveI : IsClosed (H : Set G) := hH
  let ses : TopologicalGroup.IsSES (H.subtype) (QuotientGroup.mk' H) :=
    TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let f' : CompactlySupportedContinuousMap G ℂ :=
    ⟨⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp hg⟩, hgs.comp_left Complex.ofReal_zero⟩
  have hpt : ∀ q : G ⧸ H,
      ses.pushforward μH f' q =
        Complex.ofReal (∫ h : H, g (q.out * (h : G)) ∂μH) := by
    intro q
    have hfib : ses.pushforward μH f' q = lcaCosetIntegral H μH (f' : G → ℂ) q := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change ses.pushforward μH f' ((QuotientGroup.mk' H) x) = _
      rw [ses.pushforward_apply_apply]
      exact (lcaCosetIntegral_mk H μH (f' : G → ℂ) x (ses.pullback f' x).integrable).symm
    rw [hfib, lcaCosetIntegral]
    exact integral_complex_ofReal (μ := μH) (f := fun h : H => g (q.out * (h : G)))
  have hre : (fun q : G ⧸ H => ∫ h : H, g (q.out * (h : G)) ∂μH) =
      fun q => (ses.pushforward μH f' q).re := by
    ext q
    rw [hpt, Complex.ofReal_re]
  rw [hre]
  exact Complex.continuous_re.comp (ses.pushforward μH f').continuous

include hH in
/-- At a quotient point where a test function sits strictly under the fibre measure of an open
set, a compactly supported bump in that set has strictly larger fibre integral nearby. -/
lemma exists_fibreBump_lt (ν : Measure (G ⧸ H))
    (_hν : IsWeilQuotientMeasure H μ μH ν) {U : Set G} (hU : IsOpen U)
    {ψ : G ⧸ H → ℝ} (hψ : Continuous ψ)
    {q : G ⧸ H} {c : ℝ} (hc : 0 ≤ c)
    (hlt : ENNReal.ofReal c < μH {h : H | q.out * (h : G) ∈ U}) :
    ∃ V : Set (G ⧸ H), IsOpen V ∧ q ∈ V ∧ ∃ g : G → ℝ, Continuous g ∧ HasCompactSupport g ∧
      (∀ x, 0 ≤ g x) ∧ (∀ x, g x ≤ 1) ∧ (∀ x, x ∉ U → g x = 0) ∧
      ∀ q' ∈ V, c < ∫ h : H, g (q'.out * (h : G)) ∂μH := by
  let x : G := q.out
  have hxq : (QuotientGroup.mk x : G ⧸ H) = q := Quotient.out_eq' q
  let fibre : Set H := {h : H | x * (h : G) ∈ U}
  have hfibre : IsOpen fibre :=
    hU.preimage ((continuous_const_mul x).comp continuous_subtype_val)
  have hlt' : ENNReal.ofReal c < μH fibre := by
    simpa [fibre, x, hxq] using hlt
  obtain ⟨L, hLf, hLc, hLμ⟩ :=
    (Measure.Regular.innerRegular (μ := μH)) hfibre (ENNReal.ofReal c) hlt'
  let ι : H → G := fun h => x * (h : G)
  have hι : Continuous ι := (continuous_const_mul x).comp continuous_subtype_val
  have hLG : IsCompact (ι '' L) := hLc.image hι
  have hLGU : ι '' L ⊆ U := by
    rintro _ ⟨h, hh, rfl⟩
    exact hLf hh
  obtain ⟨⟨gC, gcont⟩, hg1, hg0, hgs, hg01⟩ :=
    exists_continuous_one_zero_of_isCompact hLG hU.isClosed_compl
      (disjoint_compl_right_iff_subset.mpr hLGU)
  have hgU : ∀ y, y ∉ U → gC y = 0 := by
    intro y hy
    exact hg0 hy
  have hint : c < ∫ h : H, gC (x * (h : G)) ∂μH := by
    haveI : IsClosed (H : Set G) := hH
    let ιH : H → G := fun h => x * (h : G)
    have hιemb : IsClosedEmbedding ιH :=
      (Homeomorph.mulLeft x).isClosedEmbedding.comp (IsClosedEmbedding.subtypeVal hH)
    have hsupp : HasCompactSupport (fun h : H => gC (ιH h)) :=
      HasCompactSupport.intro (hιemb.isProperMap.isCompact_preimage hgs) (by
        intro h hh
        exact image_eq_zero_of_notMem_tsupport hh)
    have hgint : Integrable (fun h : H => gC (ιH h)) μH :=
      (gcont.comp hιemb.continuous).integrable_of_hasCompactSupport hsupp
    have hone : (L.indicator (fun _ => (1 : ℝ≥0∞))) ≤ fun h => ENNReal.ofReal (gC (ιH h)) := by
      intro h
      by_cases hh : h ∈ L
      · have : gC (ιH h) = 1 := hg1 (mem_image_of_mem ι hh)
        simp [hh, this]
      · simp [hh]
    have hlin : μH L ≤ ENNReal.ofReal (∫ h, gC (ιH h) ∂μH) := by
      calc μH L = ∫⁻ h in L, (1 : ℝ≥0∞) ∂μH := (setLIntegral_one L).symm
        _ = ∫⁻ h, L.indicator (fun _ => (1 : ℝ≥0∞)) h ∂μH :=
            (lintegral_indicator hLc.measurableSet _).symm
        _ ≤ ∫⁻ h, ENNReal.ofReal (gC (ιH h)) ∂μH := lintegral_mono hone
        _ = ENNReal.ofReal (∫ h, gC (ιH h) ∂μH) :=
            (ofReal_integral_eq_lintegral_ofReal hgint
              (Eventually.of_forall fun h => (hg01 (ιH h)).1)).symm
    have hltL : ENNReal.ofReal c < ENNReal.ofReal (∫ h, gC (ιH h) ∂μH) := hLμ.trans_le hlin
    have hposint : 0 < ∫ h, gC (ιH h) ∂μH := by
      by_contra hle
      have heq : ∫ h, gC (ιH h) ∂μH = 0 :=
        le_antisymm (le_of_not_gt hle) (integral_nonneg fun h => (hg01 (ιH h)).1)
      have hμ0 : μH L = 0 := by
        have := hlin
        rw [heq, ENNReal.ofReal_zero] at this
        exact le_antisymm this bot_le
      rw [hμ0] at hLμ
      exact not_lt_of_ge bot_le hLμ
    exact (ENNReal.ofReal_lt_ofReal_iff hposint).mp hltL
  have hcont := continuous_realFibreIntegral H hH μH gcont hgs
  have hpos : ∀ᶠ q' in 𝓝 q, c < ∫ h : H, gC (q'.out * (h : G)) ∂μH := by
    have hgt : c < ∫ h : H, gC (q.out * (h : G)) ∂μH := by simpa [x] using hint
    exact tendsto_const_nhds.eventually_lt (hcont.tendsto q) hgt
  rw [eventually_nhds_iff] at hpos
  obtain ⟨V, hVq, hVo, hV⟩ := hpos
  refine ⟨V, hVo, hV, gC, gcont, hgs, fun y => (hg01 y).1, fun y => (hg01 y).2, hgU, hVq⟩

include hH in
/-- Weil's formula for a nonnegative compactly supported continuous function, in real form. -/
lemma integral_eq_integral_realFibreIntegral (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) {g : G → ℝ} (hg : Continuous g)
    (hgs : HasCompactSupport g) :
    ∫ x, g x ∂μ = ∫ q, (∫ h : H, g (q.out * (h : G)) ∂μH) ∂ν := by
  let fC : C(G, ℂ) := ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp hg⟩
  have hfC : HasCompactSupport (fC : G → ℂ) := hgs.comp_left Complex.ofReal_zero
  have hW := hν.2.2 fC hfC
  have hfib : ∀ q, lcaCosetIntegral H μH (fC : G → ℂ) q =
      Complex.ofReal (∫ h : H, g (q.out * (h : G)) ∂μH) := by
    intro q
    rw [lcaCosetIntegral]
    exact integral_complex_ofReal (μ := μH) (f := fun h : H => g (q.out * (h : G)))
  have hleft : ∫ x, fC x ∂μ = Complex.ofReal (∫ x, g x ∂μ) := integral_complex_ofReal
  have hright : ∫ q, lcaCosetIntegral H μH (fC : G → ℂ) q ∂ν =
      Complex.ofReal (∫ q, (∫ h : H, g (q.out * (h : G)) ∂μH) ∂ν) := by
    simp_rw [hfib]
    exact integral_complex_ofReal
  have hcont : Continuous fun q : G ⧸ H => ∫ h : H, g (q.out * (h : G)) ∂μH :=
    continuous_realFibreIntegral H hH μH hg hgs
  have hint : Integrable (fun q : G ⧸ H => ∫ h : H, g (q.out * (h : G)) ∂μH) ν := by
    let _ : BorelSpace (G ⧸ H) := ⟨rfl⟩
    haveI : ν.IsHaarMeasure := hν.1
    haveI : ν.Regular := hν.2.1
    haveI : IsClosed (H : Set G) := hH
    let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
    let f' : CompactlySupportedContinuousMap G ℂ := ⟨fC, hfC⟩
    have heq : ∀ q, ses.pushforward μH f' q = lcaCosetIntegral H μH (fC : G → ℂ) q := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change ses.pushforward μH f' ((QuotientGroup.mk' H) x) = _
      rw [ses.pushforward_apply_apply]
      exact (lcaCosetIntegral_mk H μH (f' : G → ℂ) x (ses.pullback f' x).integrable).symm
    have hre : (fun q => ∫ h, g (q.out * (h : G)) ∂μH) =
        fun q => (ses.pushforward μH f' q).re := by
      ext q
      rw [heq, hfib]
      rfl
    rw [hre]
    exact (Complex.continuous_re.comp (ses.pushforward μH f').continuous).integrable_of_hasCompactSupport
      ((ses.pushforward μH f').hasCompactSupport.comp_left (Complex.zero_re))
  rw [hleft, hright, Complex.ofReal_inj] at hW
  exact hW

omit [T2Space G] [LocallyCompactSpace G] [μH.Regular] in
include hH in
private lemma weilTest_fibre_integrable {E : Type*} [NormedAddCommGroup E]
    {f : G → E} (hc : Continuous f) (hs : HasCompactSupport f) (q : G ⧸ H) :
    Integrable (fun h : H ↦ f (q.out * (h : G))) μH := by
  let i : H → G := fun h ↦ q.out * (h : G)
  have hi : IsClosedEmbedding i :=
    (Homeomorph.mulLeft q.out).isClosedEmbedding.comp (IsClosedEmbedding.subtypeVal hH)
  exact (hc.comp hi.continuous).integrable_of_hasCompactSupport
    (.intro (hi.isProperMap.isCompact_preimage hs) fun x hx ↦
      image_eq_zero_of_notMem_tsupport (f := f) (x := i x) hx)

omit [μH.Regular] in
include hH in
private lemma weilTest_average {f : G → ℂ} (hc : Continuous f) (hs : HasCompactSupport f) :
    Continuous (lcaCosetIntegral H μH f) ∧ HasCompactSupport (lcaCosetIntegral H μH f) := by
  have : IsClosed (H : Set G) := hH
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let g : CompactlySupportedContinuousMap G ℂ := ⟨⟨f, hc⟩, hs⟩
  have he : (ses.pushforward μH g : G ⧸ H → ℂ) = lcaCosetIntegral H μH f := by
    funext q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    change ses.pushforward μH g ((QuotientGroup.mk' H) x) = _
    rw [ses.pushforward_apply_apply]
    exact (lcaCosetIntegral_mk H μH f x (ses.pullback g x).integrable).symm
  rw [← he]
  exact ⟨(ses.pushforward μH g).continuous, (ses.pushforward μH g).hasCompactSupport⟩

omit [μH.Regular] in
include hH in
private lemma weilTest_realAverage_integrable (ν : Measure (G ⧸ H)) [ν.IsHaarMeasure]
    {g : G → ℝ} (hc : Continuous g) (hs : HasCompactSupport g) :
    Integrable (fun q : G ⧸ H ↦ ∫ h : H, g (q.out * (h : G)) ∂μH) ν := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  obtain ⟨h₁, h₂⟩ := weilTest_average H hH μH (Complex.continuous_ofReal.comp hc)
    (hs.comp_left Complex.ofReal_zero)
  have he : (fun q : G ⧸ H ↦ ∫ h : H, g (q.out * (h : G)) ∂μH) =
      Complex.re ∘ lcaCosetIntegral H μH (Complex.ofReal ∘ g) := by
    funext q
    simp [Function.comp_def, lcaCosetIntegral, integral_complex_ofReal]
  rw [he]
  exact (Complex.continuous_re.comp h₁).integrable_of_hasCompactSupport
    (h₂.comp_left Complex.zero_re)

include hH in
/-- On a compact subset of a strict fibre level set, finitely many test bumps give a
single minorant for the open set upstairs. -/
private lemma weil_fibre_level_compact (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) {U : Set G} (hU : IsOpen U) (hUf : μ U ≠ ⊤)
    {K : Set (G ⧸ H)} (hK : IsCompact K) {c : ℝ} (hc : 0 ≤ c)
    (hlev : ∀ q ∈ K, ENNReal.ofReal c < μH {h : H | q.out * (h : G) ∈ U}) :
    ν.real K * c ≤ μ.real U := by
  classical
  have : IsClosed (H : Set G) := hH
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have : ν.IsHaarMeasure := hν.1
  choose V hVo hV g hgc hgs hg0 hg1 hgU hgt using fun q : K ↦
    exists_fibreBump_lt H hH μ μH ν hν hU (continuous_const (y := (0 : ℝ))) hc (hlev q q.2)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover V hVo (fun q hq ↦ mem_iUnion.2 ⟨⟨q, hq⟩, hV _⟩)
  let b (x : G) := min (∑ i ∈ t, g i x) 1
  have hbc : Continuous b := (continuous_finsetSum _ fun i _ ↦ hgc i).min continuous_const
  have hbs : HasCompactSupport b := by
    have hs : HasCompactSupport (∑ i ∈ t, g i) := by
      clear hbc b ht
      induction t using Finset.induction_on with
      | empty => simpa using (HasCompactSupport.zero : HasCompactSupport (0 : G → ℝ))
      | insert i t hi ih => simpa [hi] using (hgs i).add ih
    simpa only [Function.comp_def, Finset.sum_apply] using
      hs.comp_left (g := fun y : ℝ ↦ min y 1) (by norm_num)
  have hb0 x : 0 ≤ b x := le_min (Finset.sum_nonneg fun i _ ↦ hg0 i x) zero_le_one
  have hmajor : K.indicator (fun _ ↦ c) ≤ fun q ↦ ∫ h : H, b (q.out * (h : G)) ∂μH := by
    intro q
    by_cases hq : q ∈ K
    · rw [indicator_of_mem hq]
      obtain ⟨i, hi, hVq⟩ := mem_iUnion₂.mp (ht hq)
      refine (hgt i q hVq).le.trans (integral_mono_of_nonneg (.of_forall fun h ↦ hg0 i _)
        (weilTest_fibre_integrable H hH μH hbc hbs q) (.of_forall fun h ↦ ?_))
      exact le_min (Finset.single_le_sum (fun j _ ↦ hg0 j _) hi) (hg1 i _)
    · simpa [hq] using integral_nonneg (μ := μH) (fun h : H ↦ hb0 (q.out * (h : G)))
  have hle := integral_mono_of_nonneg (μ := ν)
    (.of_forall (indicator_nonneg (fun _ _ ↦ hc)))
    (weilTest_realAverage_integrable H hH μH ν hbc hbs) (.of_forall hmajor)
  rw [integral_indicator_const _ hK.isClosed.measurableSet,
    ← integral_eq_integral_realFibreIntegral H hH μ μH ν hν hbc hbs] at hle
  refine hle.trans ?_
  have hU1 := (integrable_indicator_iff hU.measurableSet).mpr
    (integrableOn_const (C := (1 : ℝ)) hUf)
  calc ∫ x, b x ∂μ ≤ ∫ x, U.indicator (fun _ ↦ (1 : ℝ)) x ∂μ :=
        integral_mono_of_nonneg (.of_forall hb0) hU1 (.of_forall fun x ↦ by
          by_cases hx : x ∈ U
          · simp [hx, b]
          · simp [b, hx, fun i ↦ hgU i x hx])
    _ = μ.real U := by simp [integral_indicator_const _ hU.measurableSet]

include hH in
/-- Null sets upstairs are null on almost every fibre. Outer regularity lets us apply
the compact level estimate to open supersets of arbitrarily small measure. -/
private lemma ae_weil_fibre (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ μH ν)
    {P : G → Prop} (hP : ∀ᵐ x ∂μ, P x) : ∀ᵐ q : G ⧸ H ∂ν, ∀ᵐ h : H ∂μH, P (q.out * (h : G)) := by
  have : IsClosed (H : Set G) := hH
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have : ν.IsHaarMeasure := hν.1
  have : ν.Regular := hν.2.1
  let S := {x | ¬ P x}
  let m (s : Set G) (q : G ⧸ H) := μH {h : H | q.out * (h : G) ∈ s}
  have hz : μ S = 0 := ae_iff.mp hP
  have hsmall (r : ℝ≥0) (hr : 0 < r) : ∀ᵐ q ∂ν, m S q ≤ r := by
    rw [ae_iff]
    by_contra hpos
    obtain ⟨a, ha, ha'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (pos_iff_ne_zero.mpr hpos)
    obtain ⟨U, hSU, hU, hUf⟩ := S.exists_isOpen_lt_of_lt (μ := μ) (↑(a * r) : ℝ≥0∞)
      (by rw [hz, ENNReal.coe_pos]; exact mul_pos (ENNReal.coe_pos.mp ha) hr)
    have hsub : {q | ¬ m S q ≤ ↑r} ⊆ {q | ↑r < m U q} := fun q hq ↦
      (lt_of_not_ge hq).trans_le (measure_mono fun _ hh ↦ hSU hh)
    have ho : IsOpen {q | ↑r < m U q} :=
      (fibreMeasure_open_lowerSemicontinuous H hH μH hU).isOpen_preimage _
    obtain ⟨K, hKU, hK, haK⟩ := (Measure.Regular.innerRegular (μ := ν)) ho _
      (ha'.trans_le (measure_mono hsub))
    have hKf := hK.measure_lt_top (μ := ν)
    have h1 := weil_fibre_level_compact H hH μ μH ν hν hU (hUf.trans_le le_top).ne hK r.2
      (fun q hq ↦ by
        change ENNReal.ofReal (r : ℝ) < m U q
        rw [ENNReal.ofReal_coe_nnreal]
        exact hKU hq)
    have h2 : (a : ℝ) < ν.real K := by
      simpa [Measure.real] using (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top hKf.ne).mpr haK
    have h3 : μ.real U < (a : ℝ) * r := by
      simpa [Measure.real] using (ENNReal.toReal_lt_toReal (hUf.trans_le le_top).ne
        ENNReal.coe_ne_top).mpr hUf
    exact (not_lt_of_ge h1) (h3.trans (mul_lt_mul_of_pos_right h2 hr))
  have hall : ∀ᵐ q ∂ν, ∀ r : ℚ, 0 < (r : ℝ).toNNReal → m S q ≤ ↑(r : ℝ).toNNReal :=
    ae_all_iff.mpr fun r ↦ by
      by_cases hr : 0 < (r : ℝ).toNNReal
      · filter_upwards [hsmall _ hr] with q hq using fun _ ↦ hq
      · exact .of_forall fun _ h ↦ (hr h).elim
  filter_upwards [hall] with q hq
  apply ae_iff.mpr
  change m S q = 0
  by_contra h
  obtain ⟨r, -, hr, hr'⟩ := ENNReal.lt_iff_exists_rat_btwn.mp (pos_iff_ne_zero.mpr h)
  exact (not_lt_of_ge (hq r (ENNReal.coe_pos.mp hr))) hr'

include hH in
/-- The fibre integral of the norm of a compact test satisfies Weil in lower-integral form. -/
private lemma weilTest_fibreNorm (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ μH ν)
    {g : G → ℂ} (hc : Continuous g) (hs : HasCompactSupport g) :
    let B (q : G ⧸ H) := ∫⁻ h : H, ‖g (q.out * (h : G))‖ₑ ∂μH
    Measurable B ∧ (∫⁻ q, B q ∂ν) = ∫⁻ x, ‖g x‖ₑ ∂μ := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have : ν.IsHaarMeasure := hν.1
  dsimp only
  have he (q : G ⧸ H) := ofReal_integral_norm_eq_lintegral_eNorm
    (weilTest_fibre_integrable H hH μH hc hs q)
  simp_rw [← he]
  refine ⟨(continuous_realFibreIntegral H hH μH hc.norm hs.norm).measurable.ennreal_ofReal, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal (weilTest_realAverage_integrable H hH μH ν hc.norm hs.norm)
      (.of_forall fun q ↦ integral_nonneg fun h ↦ norm_nonneg _),
    ← integral_eq_integral_realFibreIntegral H hH μ μH ν hν hc.norm hs.norm,
    ofReal_integral_norm_eq_lintegral_eNorm (hc.integrable_of_hasCompactSupport hs)]

include hH in
/-- Paper: Theorem D.1.2.1, p. 747. For an L¹ function the fibre
integrals exist quotient-almost everywhere, define an L¹ function and satisfy Weil's formula. -/
theorem weilQuotientIntegral_L1 (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ μH ν)
    {f : G → ℂ} (hf : Integrable f μ) :
    (∀ᵐ q ∂ν, Integrable (fun h : H ↦ f (q.out * (h : G))) μH) ∧
      Integrable (lcaCosetIntegral H μH f) ν ∧
      (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  obtain ⟨g, hg, hs, he⟩ := exists_compactTest_tsum hf
  let B n (q : G ⧸ H) := ∫⁻ h : H, ‖g n (q.out * (h : G))‖ₑ ∂μH
  have hB n : Measurable (B n) ∧ (∫⁻ q, B n q ∂ν) = ∫⁻ x, ‖g n x‖ₑ ∂μ :=
    weilTest_fibreNorm H hH μ μH ν hν (hg n).1 (hg n).2
  have hsum : (∑' n, ∫⁻ q, B n q ∂ν) ≠ ⊤ := by simpa only [fun n ↦ (hB n).2] using hs
  have hfin : ∀ᵐ q ∂ν, ∑' n, B n q < ⊤ := by
    apply ae_lt_top' (.tsum fun n ↦ (hB n).1.aemeasurable)
    rwa [lintegral_tsum fun n ↦ (hB n).1.aemeasurable]
  let A n := lcaCosetIntegral H μH (g n)
  have hA n : AEStronglyMeasurable (A n) ν :=
    (weilTest_average H hH μH (hg n).1 (hg n).2).1.aestronglyMeasurable
  have hAsum : (∑' n, ∫⁻ q, ‖A n q‖ₑ ∂ν) ≠ ⊤ := by
    refine ne_top_of_le_ne_top hsum (tsum_le_tsum (g := fun n ↦ ∫⁻ q, B n q ∂ν) fun n ↦ ?_)
    exact lintegral_mono fun q ↦ eNorm_integral_le_lintegral_eNorm _
  have hfib : ∀ᵐ q ∂ν, Integrable (fun h : H ↦ f (q.out * (h : G))) μH ∧
      lcaCosetIntegral H μH f q = ∑' n, A n q := by
    filter_upwards [hfin, ae_weil_fibre H hH μ μH ν hν he] with q hq heq
    have hm n := (weilTest_fibre_integrable H hH μH (hg n).1 (hg n).2 q).1
    exact ⟨(integrable_tsum_of_lintegral_eNorm hm hq.ne).congr (Filter.EventuallyEq.symm heq),
      (integral_congr_ae heq).trans (integral_tsum hm hq.ne)⟩
  have heA : lcaCosetIntegral H μH f =ᵐ[ν] fun q ↦ ∑' n, A n q := hfib.mono fun q hq ↦ hq.2
  refine ⟨hfib.mono fun q hq ↦ hq.1, (integrable_tsum_of_lintegral_eNorm hA hAsum).congr heA.symm, ?_⟩
  rw [integral_congr_ae he, integral_congr_ae heA, integral_tsum hA hAsum,
    integral_tsum (fun n ↦ (hg n).1.aestronglyMeasurable) hs]
  exact tsum_congr fun n ↦ hν.2.2 ⟨g n, (hg n).1⟩ (hg n).2

include hH in
/-- Integrating the translated subgroup measures against the normalized quotient measure
recovers the group measure. -/
private theorem weilMeasure_eq_bind [SigmaFinite μ] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) :
    let κ : G ⧸ H → Measure G := fun q ↦ μH.map (fun h : H ↦ q.out * (h : G))
    Measurable κ ∧ ν.bind κ = μ := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : SigmaCompactSpace G := sigmaCompactSpace_of_sigmaFinite_haar μ
  let K := CompactExhaustion.choice G
  let ses := TopologicalGroup.IsSES.ofClosedSubgroup H hH
  let tr (x : G) (h : H) : G := x * (h : G)
  have htr (x : G) : Continuous (tr x) := continuous_const.mul continuous_subtype_val
  let κ : G ⧸ H → Measure G := fun q ↦ μH.map (tr q.out)
  change Measurable κ ∧ ν.bind κ = μ

  have hgmeas (g : CompactlySupportedContinuousMap G ℝ) :
      Measurable (fun x ↦ ENNReal.ofReal (g x)) :=
    (ENNReal.continuous_ofReal.comp g.continuous).measurable
  have htest (g : CompactlySupportedContinuousMap G ℝ) (hg : ∀ x, 0 ≤ g x) (q : G ⧸ H) :
      (∫⁻ x, ENNReal.ofReal (g x) ∂κ q) = ENNReal.ofReal (ses.pushforward μH g q) := by
    have hq : (QuotientGroup.mk' H) q.out = q := Quotient.out_eq' q
    have hpush := ses.pushforward_apply_apply μH g q.out
    rw [hq] at hpush
    rw [show κ q = μH.map (tr q.out) from rfl,
      lintegral_map (hgmeas g) (htr q.out).measurable, hpush]
    exact (ofReal_integral_eq_lintegral_ofReal (μ := μH) (ses.pullback g q.out).integrable
      (.of_forall fun h ↦ hg (tr q.out h))).symm

  -- Compactly supported functions approximate the measure of each open fibre from below.
  have hopen {U : Set G} (hU : IsOpen U) : Measurable (fun q ↦ κ q U) := by
    suffices LowerSemicontinuous (fun q ↦ κ q U) from this.measurable
    let F := {g : CompactlySupportedContinuousMap G ℝ //
      tsupport g ⊆ U ∧ ∀ x, g x ∈ Icc 0 1}
    have hsup (q : G ⧸ H) :
        κ q U = ⨆ g : F, ENNReal.ofReal (ses.pushforward μH g.1 q) := by
      rw [show κ q U = μH (tr q.out ⁻¹' U) from
        Measure.map_apply (htr q.out).measurable hU.measurableSet]
      apply le_antisymm
      · refine le_of_forall_lt fun r hr ↦ ?_
        obtain ⟨L, hLU, hL, hrL⟩ := (hU.preimage (htr q.out)).exists_lt_isCompact (μ := μH) hr
        obtain ⟨g, hgL, hgcompact, hgU, hg⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen
          (hL.image (htr q.out)) hU (image_subset_iff.mpr hLU)
        let g' : CompactlySupportedContinuousMap G ℝ := ⟨g, hgcompact⟩
        refine hrL.trans_le (le_iSup_of_le (⟨g', hgU, hg⟩ : F) ?_)
        rw [← htest g' (fun x ↦ (hg x).1), show κ q = μH.map (tr q.out) from rfl,
          lintegral_map (hgmeas g') (htr q.out).measurable, ← lintegral_indicator_one hL.measurableSet]
        apply lintegral_mono
        intro h
        by_cases hh : h ∈ L
        · change L.indicator 1 h ≤ ENNReal.ofReal (g (tr q.out h))
          simp [hh, hgL (mem_image_of_mem _ hh)]
        · simp [hh]
      · refine iSup_le fun g ↦ ?_
        rw [← htest g.1 (fun x ↦ (g.2.2 x).1), show κ q = μH.map (tr q.out) from rfl,
          lintegral_map (hgmeas g.1) (htr q.out).measurable,
          ← lintegral_indicator_one (hU.preimage (htr q.out)).measurableSet]
        apply lintegral_mono
        intro h
        by_cases hh : tr q.out h ∈ U
        · simpa [hh] using ENNReal.ofReal_le_ofReal (g.2.2 (tr q.out h)).2
        · have hz : g.1 (tr q.out h) = 0 :=
            image_eq_zero_of_notMem_tsupport (fun hm ↦ hh (g.2.1 hm))
          simp [hz, hh]
    simp_rw [hsup]
    exact lowerSemicontinuous_iSup fun g ↦
      (ENNReal.continuous_ofReal.comp (ses.pushforward μH g.1).continuous).lowerSemicontinuous

  have hκcompact (q : G ⧸ H) {L : Set G} (hL : IsCompact L) : κ q L < ⊤ := by
    rw [show κ q L = μH (tr q.out ⁻¹' L) from
      Measure.map_apply (htr q.out).measurable hL.measurableSet]
    exact ((Homeomorph.mulLeft q.out).isClosedEmbedding.comp
      ses.isClosedEmbedding).isCompact_preimage hL |>.measure_lt_top

  -- The restrictions to relatively compact open sets are finite on each fibre.
  have hκ : Measurable κ := by
    let U (n : ℕ) := interior (K n)
    have hU : ⋃ n, U n = univ := by
      refine iUnion_eq_univ_iff.mpr fun x ↦ ?_
      obtain ⟨n, hn⟩ := K.exists_mem x
      exact ⟨n + 1, K.subset_interior_succ n hn⟩
    have hrestrict (n : ℕ) : Measurable (fun q ↦ (κ q).restrict (U n)) := by
      let (q : G ⧸ H) : IsFiniteMeasure ((κ q).restrict (U n)) :=
        ⟨by
          rw [Measure.restrict_apply_univ]
          exact (measure_mono interior_subset).trans_lt (hκcompact q (K.isCompact n))⟩
      refine Measurable.measure_of_isPiSystem BorelSpace.measurable_eq isPiSystem_isOpen ?_ ?_
      · intro S hS
        change IsOpen S at hS
        simpa only [Measure.restrict_apply hS.measurableSet] using
          hopen (hS.inter (isOpen_interior : IsOpen (U n)))
      · simpa only [Measure.restrict_apply_univ] using hopen (isOpen_interior : IsOpen (U n))
    refine Measure.measurable_of_measurable_coe _ fun S hS ↦ ?_
    have heq (q : G ⧸ H) : κ q S = ⨆ n, (κ q).restrict (U n) S := by
      have hmono : Monotone (fun n ↦ S ∩ U n) :=
        monotone_const.inter (fun _ _ h ↦ interior_mono (K.subset h))
      simpa only [← inter_iUnion, hU, inter_univ, Measure.restrict_apply hS] using
        hmono.measure_iUnion (μ := κ q)
    simp_rw [heq]
    exact Measurable.iSup fun n ↦ (Measure.measurable_coe hS).comp (hrestrict n)

  let ρ := ν.bind κ
  have htests (g : CompactlySupportedContinuousMap G ℝ) (hg : ∀ x, 0 ≤ g x) :
      (∫⁻ x, ENNReal.ofReal (g x) ∂ρ) = ∫⁻ x, ENNReal.ofReal (g x) ∂μ := by
    let gℂ : C(G, ℂ) := ⟨fun x ↦ (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩
    have hgℂ : HasCompactSupport gℂ := g.hasCompactSupport.comp_left Complex.ofReal_zero
    have hcoset (q : G ⧸ H) : lcaCosetIntegral H μH gℂ q = (ses.pushforward μH g q : ℂ) := by
      have hq : (QuotientGroup.mk' H) q.out = q := Quotient.out_eq' q
      rw [← hq, ses.pushforward_apply_apply]
      rw [hq]
      exact integral_complex_ofReal
    have hgPush : ∀ q, 0 ≤ ses.pushforward μH g q := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      change 0 ≤ ses.pushforward μH g ((QuotientGroup.mk' H) x)
      rw [ses.pushforward_apply_apply]
      exact integral_nonneg fun h ↦ hg (tr x h)
    have heq : (∫ x, g x ∂μ) = ∫ q, ses.pushforward μH g q ∂ν := by
      have heq := hν.2.2 gℂ hgℂ
      simp_rw [hcoset] at heq
      change (∫ x, (g x : ℂ) ∂μ) = _ at heq
      rw [integral_complex_ofReal, integral_complex_ofReal] at heq
      exact Complex.ofReal_injective heq
    rw [Measure.lintegral_bind hκ.aemeasurable (hgmeas g).aemeasurable]
    simp_rw [htest g hg]
    rw [← ofReal_integral_eq_lintegral_ofReal (ses.pushforward μH g).integrable
      (.of_forall hgPush), ← ofReal_integral_eq_lintegral_ofReal g.integrable (.of_forall hg), heq]

  let : IsFiniteMeasureOnCompacts ρ := ⟨by
    intro L hL
    obtain ⟨g, hgL, hgcompact, -, hg⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hL isOpen_univ (subset_univ L)
    let g' : CompactlySupportedContinuousMap G ℝ := ⟨g, hgcompact⟩
    calc
      ρ L = ∫⁻ x, L.indicator 1 x ∂ρ := (lintegral_indicator_one hL.measurableSet).symm
      _ ≤ ∫⁻ x, ENNReal.ofReal (g' x) ∂ρ := by
        apply lintegral_mono
        intro x
        change L.indicator 1 x ≤ ENNReal.ofReal (g x)
        by_cases hx : x ∈ L
        · simp [hx, hgL hx]
        · simp [hx]
      _ = ∫⁻ x, ENNReal.ofReal (g' x) ∂μ := htests g' (fun x ↦ (hg x).1)
      _ < ⊤ := by
        rw [← ofReal_integral_eq_lintegral_ofReal g'.integrable (.of_forall fun x ↦ (hg x).1)]
        exact ENNReal.ofReal_lt_top⟩

  have hrepresentative (x : G) : κ (QuotientGroup.mk x) = μH.map (tr x) := by
    let y : G := (QuotientGroup.mk x : G ⧸ H).out
    have hy : (QuotientGroup.mk y : G ⧸ H) = QuotientGroup.mk x := Quotient.out_eq' _
    let k : H := ⟨y⁻¹ * x, QuotientGroup.eq.mp hy⟩
    have htr_eq : tr x = tr y ∘ (k * ·) := by
      funext h
      simp [tr, k, ← mul_assoc]
    change μH.map (tr y) = _
    rw [htr_eq, ← Measure.map_map (htr y).measurable
      (measurePreserving_mul_left μH k).measurable, (measurePreserving_mul_left μH k).map_eq]

  let : ρ.IsMulLeftInvariant := ⟨by
    intro x
    have hx : Measurable (x * · : G → G) := (continuous_const.mul continuous_id).measurable
    have hcov (q : G ⧸ H) : (κ q).map (x * ·) = κ (QuotientGroup.mk x * q) := by
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      change (κ (QuotientGroup.mk y)).map (x * ·) =
        κ ((QuotientGroup.mk' H) x * (QuotientGroup.mk' H) y)
      rw [← (QuotientGroup.mk' H).map_mul x y]
      change (κ (QuotientGroup.mk y)).map (x * ·) = κ (QuotientGroup.mk (x * y))
      rw [hrepresentative, hrepresentative, Measure.map_map hx (htr y).measurable]
      simp only [tr, Function.comp_def, mul_assoc]
    change (ν.bind κ).map (x * ·) = ν.bind κ
    rw [Measure.map_bind hκ.aemeasurable hx.aemeasurable]
    simp_rw [hcov]
    have hshift := measurePreserving_mul_left ν (QuotientGroup.mk x)
    rw [← Measure.bind_map hshift.measurable.aemeasurable hκ.aemeasurable, hshift.map_eq]⟩

  -- Uniqueness on relatively compact sets extends along the exhaustion.
  let c := Measure.haarScalarFactor ρ μ
  have hscalar : ρ = c • μ := by
    ext S hS
    have hmono : Monotone (fun n ↦ S ∩ K n) :=
      monotone_const.inter (fun _ _ h ↦ K.subset h)
    have hcover : ⋃ n, S ∩ K n = S := by rw [← inter_iUnion, K.iUnion_eq, inter_univ]
    rw [← hcover, hmono.measure_iUnion, hmono.measure_iUnion]
    congr with n
    exact Measure.measure_isMulInvariant_eq_smul_of_isCompact_closure ρ μ
      ((K.isCompact n).closure_of_subset inter_subset_right)
  obtain ⟨g, hgcompact, hg, hgpos⟩ := exists_continuous_nonneg_pos (1 : G)
  let g' : CompactlySupportedContinuousMap G ℝ := ⟨g, hgcompact⟩
  have hpos : 0 < ∫ x, g' x ∂μ :=
    g.continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero hgcompact hg hgpos
  have heq := htests g' hg
  rw [← ofReal_integral_eq_lintegral_ofReal g'.integrable (.of_forall hg),
    ← ofReal_integral_eq_lintegral_ofReal g'.integrable (.of_forall hg), hscalar,
    integral_smul_nnreal_measure] at heq
  have heq' : (c : ℝ) * (∫ x, g' x ∂μ) = ∫ x, g' x ∂μ :=
    (ENNReal.ofReal_eq_ofReal_iff (by positivity) hpos.le).mp heq
  have hc : c = 1 := by
    exact_mod_cast (mul_right_cancel₀ hpos.ne' (heq'.trans (one_mul _).symm))
  exact ⟨hκ, by simpa [hc] using hscalar⟩

include hH in
/-- Paper: Lemma D.1.2.3, p. 747. For a σ-finite group, finiteness of
the iterated integral of the norm implies integrability and Weil's formula. -/
theorem integrable_of_weilNormIntegral [SigmaFinite μ] (ν : Measure (G ⧸ H))
    (hν : IsWeilQuotientMeasure H μ μH ν) {f : G → ℂ} (hf : Measurable f)
    (hfin : (∫⁻ q, ∫⁻ h : H, ‖f (q.out * (h : G))‖₊ ∂μH ∂ν) < (⊤ : ℝ≥0∞)) :
    Integrable f μ ∧ (∫ x, f x ∂μ) = ∫ q, lcaCosetIntegral H μH f q ∂ν := by
  let tr (q : G ⧸ H) (h : H) : G := q.out * (h : G)
  have htr (q : G ⧸ H) : Measurable (tr q) :=
    (continuous_const.mul continuous_subtype_val).measurable
  let κ : G ⧸ H → Measure G := fun q ↦ μH.map (tr q)
  have hκ : Measurable κ ∧ ν.bind κ = μ := weilMeasure_eq_bind H hH μ μH ν hν
  have hfint : Integrable f μ := by
    refine ⟨hf.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_eNorm, ← hκ.2, Measure.lintegral_bind hκ.1.aemeasurable
      hf.eNorm.aemeasurable]
    have hnorm (q : G ⧸ H) : (∫⁻ x, ‖f x‖ₑ ∂κ q) = ∫⁻ h : H, ‖f (tr q h)‖ₑ ∂μH :=
      lintegral_map hf.eNorm (htr q)
    simp_rw [hnorm, eNorm_eq_nnNorm]
    exact hfin
  refine ⟨hfint, ?_⟩
  let kernel : ProbabilityTheory.Kernel (G ⧸ H) G := ⟨κ, hκ.1⟩
  have hcomp := Measure.comp_eq_comp_const_apply (κ := kernel) (μ := ν)
  have hInt : Integrable f ((kernel.comp (ProbabilityTheory.Kernel.const Unit ν)) ()) := by
    rwa [← hcomp, show ν.bind (⇑kernel) = μ from hκ.2]
  calc
    (∫ x, f x ∂μ) = ∫ q, ∫ x, f x ∂κ q ∂ν := by
      rw [← hκ.2, show ν.bind κ = _ from hcomp]
      have heq := ProbabilityTheory.Kernel.integral_comp hInt
      rw [ProbabilityTheory.Kernel.const_apply] at heq
      exact heq
    _ = ∫ q, lcaCosetIntegral H μH f q ∂ν := by
      congr with q
      exact integral_map (htr q).aemeasurable hf.aestronglyMeasurable

section FundamentalDomain

variable [DiscreteTopology H] [SecondCountableTopology G]
variable {Δ Δ' : Set G} (hΔ : MeasurableSet Δ)
variable (hbij : Function.Bijective (fun x : Δ ↦ (QuotientGroup.mk x.val : G ⧸ H)))

-- Retain the existing topological and measure hypotheses in the signature.
set_option linter.unusedSectionVars false in
include hH hΔ hbij in
/-- Paper: Proposition D.1.2.4, p. 748. The integrals over the translates
of a Borel fundamental domain sum absolutely to the group integral. -/
theorem weilFundamentalDomain_hasSum {f : G → ℂ} (hf : Integrable f μ) :
    HasSum (fun h : H ↦ ∫ x in (fun y : G ↦ y * (h : G)) '' Δ, f x ∂μ)
      (∫ x, f x ∂μ) := by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  let translate (h : H) : Set G := (fun y : G ↦ y * (h : G)) '' Δ
  have hmeas (h : H) : MeasurableSet (translate h) :=
    (measurableEmbedding_mulRight (h : G)).measurableSet_image' hΔ
  have hdisj : Pairwise (fun h k ↦ Disjoint (translate h) (translate k)) := by
    intro h k hne
    rw [Set.disjoint_left]
    rintro x ⟨a, ha, hax⟩ ⟨b, hb, hbx⟩
    have hab : (⟨a, ha⟩ : Δ) = ⟨b, hb⟩ := hbij.1 <| calc
      QuotientGroup.mk a = QuotientGroup.mk (a * (h : G)) :=
        (QuotientGroup.mk_mul_of_mem a h.property).symm
      _ = QuotientGroup.mk (b * (k : G)) := congrArg QuotientGroup.mk (hax.trans hbx.symm)
      _ = QuotientGroup.mk b := QuotientGroup.mk_mul_of_mem b k.property
    have hab' : a = b := congrArg Subtype.val hab
    apply hne
    apply Subtype.ext
    exact mul_left_cancel (by simpa only [hab'] using hax.trans hbx.symm)
  have hcover : ⋃ h, translate h = univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨a, ha⟩ := hbij.2 (QuotientGroup.mk x)
    let h : H := ⟨(a : G)⁻¹ * x, QuotientGroup.eq.mp ha⟩
    exact mem_iUnion.mpr ⟨h, a, a.property, mul_inv_cancel_left _ _⟩
  simpa only [hcover, Measure.restrict_univ, translate] using
    hasSum_integral_iUnion hmeas hdisj hf.integrableOn

variable (ν : Measure (G ⧸ H)) (hν : IsWeilQuotientMeasure H μ Measure.count ν)

-- Retain the existing hypotheses in the signature.
set_option linter.unusedSectionVars false in
include hH hΔ hbij hν in
/-- Paper: Proposition D.1.2.4, p. 748. Borel measurability on the quotient
can be tested on the pullback restricted to a Borel fundamental domain. -/
theorem weilFundamentalDomain_measurable_iff (f : G ⧸ H → ℂ) :
    Measurable f ↔ Measurable (Δ.indicator (fun x ↦ f (QuotientGroup.mk x))) := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  have hmk : Continuous (QuotientGroup.mk : G → G ⧸ H) := QuotientGroup.continuous_mk
  refine ⟨fun hf ↦ (hf.comp hmk.measurable).indicator hΔ, fun hf ↦ ?_⟩
  let : IsClosed (H : Set G) := hH
  let : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  let : IsUniformGroup G := isUniformGroup_of_commGroup
  let : CompleteSpace G := IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace G
  let := IsUniformGroup.uniformity_countably_generated (α := G)
  let : PolishSpace G := by constructor
  let q : Δ → G ⧸ H := fun x ↦ QuotientGroup.mk x.val
  have hq : MeasurableEmbedding q :=
    hmk.continuousOn.measurableEmbedding hΔ (injOn_iff_injective.mpr hbij.1)
  have hrestrict : Measurable (f ∘ q) := by
    have heq : (Δ.indicator (fun x ↦ f (QuotientGroup.mk x))) ∘ ((↑) : Δ → G) = f ∘ q :=
      funext fun x ↦ indicator_of_mem x.property _
    rw [← heq]
    exact hf.comp measurable_subtype_coe
  intro s hs
  have hsurj : Function.Surjective q := hbij.2
  rw [← hsurj.image_preimage (f ⁻¹' s)]
  exact hq.measurableSet_image' (hrestrict hs)

include hbij in
/-- Every point has a unique right `H`-translate in the Borel section `Δ`. -/
private lemma weilSection_existsUnique (x : G) : ∃! γ : H.op, γ • x ∈ Δ := by
  obtain ⟨d, hd⟩ := hbij.2 (QuotientGroup.mk x)
  have hmem : x⁻¹ * (d : G) ∈ H := by
    simpa [mul_inv_rev, inv_inv] using H.inv_mem ((QuotientGroup.eq).mp hd)
  let g : H.op := H.equivOp ⟨x⁻¹ * (d : G), hmem⟩
  have hgx : g • x = (d : G) := by
    have hg : (g : Gᵐᵒᵖ) = MulOpposite.op (x⁻¹ * (d : G)) := rfl
    rw [Submonoid.smul_def, hg, MulOpposite.smul_eq_mul_unop]
    simp
  refine ExistsUnique.intro g (hgx ▸ d.property) ?_
  intro g' hg'
  have hmk (γ : H.op) :
      QuotientGroup.mk (s := H) (γ • x) = QuotientGroup.mk (s := H) x := by
    rw [Submonoid.smul_def, MulOpposite.smul_eq_mul_unop, QuotientGroup.eq]
    simpa [mul_inv_rev, mul_assoc] using H.inv_mem ((Subgroup.mem_op).mp γ.property)
  let a : Δ := ⟨g • x, hgx ▸ d.property⟩
  let b : Δ := ⟨g' • x, hg'⟩
  have hab : a = b := hbij.1 ((hmk g).trans (hmk g').symm)
  have hgx' : g • x = g' • x := congrArg Subtype.val hab
  rw [Submonoid.smul_def, Submonoid.smul_def, MulOpposite.smul_eq_mul_unop,
    MulOpposite.smul_eq_mul_unop] at hgx'
  exact Subtype.ext <| MulOpposite.unop_injective <| mul_left_cancel hgx'.symm

include hΔ hbij in
/-- A Borel set meeting every coset exactly once is a strict fundamental domain for the
right action of `H`. -/
private lemma weilSection_isFundamentalDomain :
    IsFundamentalDomain H.op Δ μ :=
  IsFundamentalDomain.mk' hΔ.nullMeasurableSet (weilSection_existsUnique H hbij)

/-- Right multiplication by `H` does not change the coset. -/
private lemma weilSection_mk_smul (γ : H.op) (x : G) :
    QuotientGroup.mk (s := H) (γ • x) = QuotientGroup.mk (s := H) x := by
  rw [Submonoid.smul_def, MulOpposite.smul_eq_mul_unop, QuotientGroup.eq]
  simpa [mul_inv_rev, mul_assoc] using H.inv_mem ((Subgroup.mem_op).mp γ.property)

include hH hΔ hbij hν in
/-- Paper: Proposition D.1.2.4, p. 748. Integrability on the quotient
can be tested on the pullback restricted to a Borel fundamental domain. -/
theorem weilFundamentalDomain_integrable_iff (f : G ⧸ H → ℂ) :
    Integrable f ν ↔ Integrable (Δ.indicator (fun x ↦ f (QuotientGroup.mk x))) μ := by
  haveI : IsClosed (H : Set G) := hH
  letI : BorelSpace (G ⧸ H) := ⟨rfl⟩
  haveI : Countable H :=
    (TopologicalSpace.separableSpace_iff_countable (α := H)).1 inferInstance
  haveI : Countable H.op := Countable.of_equiv H H.equivOp
  haveI : MeasurableConstSMul H.op G :=
    ⟨fun γ ↦ by
      have heq : (fun x ↦ γ • x) = fun x ↦ x * (γ : Gᵐᵒᵖ).unop := by
        ext x
        rw [Submonoid.smul_def, MulOpposite.smul_eq_mul_unop]
      rw [heq]
      exact measurable_mul_const _⟩
  haveI : SMulInvariantMeasure H.op G μ :=
    ⟨fun γ s _hs ↦ by
      have heq : (fun x ↦ γ • x) = fun x ↦ x * (γ : Gᵐᵒᵖ).unop := by
        ext x
        rw [Submonoid.smul_def, MulOpposite.smul_eq_mul_unop]
      rw [heq]
      exact measure_preimage_mul_right μ _ s⟩
  let π : G → G ⧸ H := QuotientGroup.mk
  have hπ : Measurable π := QuotientGroup.continuous_mk.measurable
  have hfund : IsFundamentalDomain H.op Δ μ := weilSection_isFundamentalDomain H μ hΔ hbij
  have hfundImage (g : G) : IsFundamentalDomain H.op ((fun y ↦ g * y) '' Δ) μ := by
    refine IsFundamentalDomain.mk'
      ((measurableEmbedding_mulLeft g).measurableSet_image.mpr hΔ).nullMeasurableSet fun x ↦ ?_
    obtain ⟨γ, hγ, huniq⟩ := weilSection_existsUnique H hbij (g⁻¹ * x)
    have hcomm : γ • x = g * (γ • (g⁻¹ * x)) := by
      rw [Submonoid.smul_def, Submonoid.smul_def, MulOpposite.smul_eq_mul_unop,
        MulOpposite.smul_eq_mul_unop]
      simp [mul_assoc]
    refine ExistsUnique.intro γ ?_ ?_
    · rw [hcomm]
      exact ⟨γ • (g⁻¹ * x), hγ, rfl⟩
    · intro γ' hγ'
      apply huniq
      have hcomm' : γ' • (g⁻¹ * x) = g⁻¹ * (γ' • x) := by
        rw [Submonoid.smul_def, Submonoid.smul_def, MulOpposite.smul_eq_mul_unop,
          MulOpposite.smul_eq_mul_unop]
        simp [mul_assoc]
      rw [hcomm']
      obtain ⟨y, hy, hyx⟩ := hγ'
      have hyx' : g⁻¹ * (γ' • x) = y := by
        rw [← hyx]
        simp
      simpa [hyx'] using hy
  have hpush (g : G) :
      (μ.restrict ((fun y ↦ g * y) '' Δ)).map π = (μ.restrict Δ).map π := by
    ext U hU
    have hpre : MeasurableSet (π ⁻¹' U) := hU.preimage hπ
    rw [Measure.map_apply hπ hU, Measure.restrict_apply hpre, Measure.map_apply hπ hU,
      Measure.restrict_apply hpre]
    refine (hfund.measure_set_eq (hfundImage g) hpre ?_).symm
    intro γ
    ext y
    simp only [Set.mem_preimage, π]
    rw [weilSection_mk_smul H γ y]
  let νΔ : Measure (G ⧸ H) := (μ.restrict Δ).map π
  haveI : νΔ.IsMulLeftInvariant := by
    refine ⟨fun q ↦ ?_⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    let L : G → G := fun x ↦ g * x
    let LQ : G ⧸ H → G ⧸ H := fun r ↦ π g * r
    have hpres : MeasurePreserving L (μ.restrict Δ) (μ.restrict (L '' Δ)) :=
      (measurePreserving_mul_left μ g).restrict_image_emb (measurableEmbedding_mulLeft g) Δ
    have hcomp : LQ ∘ π = π ∘ L := by
      ext x
      simp [LQ, L, π, QuotientGroup.mk_mul]
    calc
      Measure.map LQ νΔ = Measure.map LQ (Measure.map π (μ.restrict Δ)) := rfl
      _ = Measure.map (LQ ∘ π) (μ.restrict Δ) :=
        Measure.map_map (measurable_const_mul (π g)) hπ
      _ = Measure.map (π ∘ L) (μ.restrict Δ) := by rw [hcomp]
      _ = Measure.map π (Measure.map L (μ.restrict Δ)) :=
        (Measure.map_map hπ (measurable_const_mul g)).symm
      _ = Measure.map π (μ.restrict (L '' Δ)) := by rw [hpres.map_eq]
      _ = νΔ := by rw [hpush g]
  have hdisc : IsDiscrete (H : Set G) :=
    (SetLike.isDiscrete_iff_discreteTopology).2 inferInstance
  obtain ⟨U, hU, -, hsep⟩ := hdisc.exists_nhds_eq_one_of_image_mulRight_inter_nonempty
  obtain ⟨K0, hK0, hK0n⟩ := exists_compact_mem_nhds (1 : G)
  have hmem : K0 ∩ U ∈ 𝓝 (1 : G) := Filter.inter_mem hK0n hU
  obtain ⟨W, hWsub, hWo, hW1⟩ := mem_nhds_iff.mp hmem
  have hWcl : IsCompact (closure W) :=
    IsCompact.of_isClosed_subset hK0 isClosed_closure
      (closure_minimal (hWsub.trans inter_subset_left) hK0.isClosed)
  have hWlt : μ W < (⊤ : ℝ≥0∞) :=
    lt_of_le_of_lt (measure_mono subset_closure) hWcl.measure_lt_top
  have hWpos : 0 < μ W := hWo.measure_pos μ ⟨1, hW1⟩
  have hWU : W ⊆ U := hWsub.trans inter_subset_right
  let leftPiece (h : H) : Set G := W ∩ (fun x ↦ x * (h : G)) '' Δ
  let rightPiece (h : H) : Set G := (fun x ↦ x * (h : G)) '' W ∩ Δ
  have hleftMeas (h : H) : MeasurableSet (leftPiece h) :=
    hWo.measurableSet.inter ((measurableEmbedding_mulRight (h : G)).measurableSet_image.mpr hΔ)
  have hrightMeas (h : H) : MeasurableSet (rightPiece h) :=
    ((Homeomorph.mulRight (h : G)).isOpenMap W hWo).measurableSet.inter hΔ
  have hdisjL : Pairwise fun h₁ h₂ ↦ Disjoint (leftPiece h₁) (leftPiece h₂) := by
    intro h₁ h₂ hne
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ ↦ ?_
    rcases hz₁ with ⟨-, d₁, hd₁, rfl⟩
    rcases hz₂ with ⟨-, d₂, hd₂, hd₂eq⟩
    have hsame : QuotientGroup.mk (s := H) d₁ = QuotientGroup.mk (s := H) d₂ := by
      rw [QuotientGroup.eq]
      have heq : d₂ = d₁ * ((h₁ : G) * (h₂ : G)⁻¹) := by
        apply mul_right_cancel (b := (h₂ : G))
        calc
          d₂ * (h₂ : G) = d₁ * (h₁ : G) := hd₂eq
          _ = d₁ * ((h₁ : G) * (h₂ : G)⁻¹) * (h₂ : G) := by simp [mul_assoc]
      rw [heq]
      simp
      exact H.mul_mem h₁.property (H.inv_mem h₂.property)
    have heqd : d₁ = d₂ := by
      have hsub : (⟨d₁, hd₁⟩ : Δ) = ⟨d₂, hd₂⟩ := hbij.1 (by simpa using hsame)
      simpa using congrArg Subtype.val hsub
    have hh : (h₁ : G) = h₂ := by
      apply mul_left_cancel (a := d₁)
      calc d₁ * (h₁ : G) = d₂ * (h₂ : G) := hd₂eq.symm
        _ = d₁ * (h₂ : G) := by rw [heqd]
    exact hne (Subtype.ext hh)
  have hdisjR : Pairwise fun h₁ h₂ ↦ Disjoint (rightPiece h₁) (rightPiece h₂) := by
    intro h₁ h₂ hne
    refine Set.disjoint_left.mpr fun z hz₁ hz₂ ↦ ?_
    rcases hz₁ with ⟨⟨w₁, hw₁, rfl⟩, -⟩
    rcases hz₂ with ⟨⟨w₂, hw₂, hw₂eq⟩, -⟩
    have hmk : QuotientGroup.mk (s := H) w₁ = QuotientGroup.mk (s := H) w₂ := by
      rw [QuotientGroup.eq]
      have heq : w₂ = w₁ * ((h₁ : G) * (h₂ : G)⁻¹) := by
        apply mul_right_cancel (b := (h₂ : G))
        calc
          w₂ * (h₂ : G) = w₁ * (h₁ : G) := hw₂eq
          _ = w₁ * ((h₁ : G) * (h₂ : G)⁻¹) * (h₂ : G) := by simp [mul_assoc]
      rw [heq]
      simp
      exact H.mul_mem h₁.property (H.inv_mem h₂.property)
    have hrel : w₁⁻¹ * w₂ ∈ H := (QuotientGroup.eq).mp hmk
    have hone : w₁⁻¹ * w₂ = 1 := by
      apply hsep _ hrel
      exact ⟨w₂, ⟨w₁, hWU hw₁, by simp⟩, hWU hw₂⟩
    have hw12 : w₁ = w₂ := by
      have : w₁ * (w₁⁻¹ * w₂) = w₁ := by simp [hone]
      exact (by simpa using this : w₂ = w₁).symm
    have hh : (h₁ : G) = h₂ := by
      apply mul_left_cancel (a := w₁)
      calc w₁ * (h₁ : G) = w₂ * (h₂ : G) := hw₂eq.symm
        _ = w₁ * (h₂ : G) := by rw [hw12]
    exact hne (Subtype.ext hh)
  have hcoverL : ⋃ h : H, leftPiece h = W := by
    ext w
    constructor
    · rintro ⟨-, ⟨h, rfl⟩, hw, -⟩
      exact hw
    · intro hw
      obtain ⟨d, hd⟩ := hbij.2 (π w)
      have hh : (d : G)⁻¹ * w ∈ H := (QuotientGroup.eq).mp hd
      refine mem_iUnion.2 ⟨⟨(d : G)⁻¹ * w, hh⟩, hw, ⟨d, d.property, ?_⟩⟩
      exact mul_inv_cancel_left (d : G) w
  have hcoverR : ⋃ h : H, rightPiece h = π ⁻¹' (π '' W) ∩ Δ := by
    ext z
    constructor
    · rintro ⟨_, ⟨h, rfl⟩, ⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w, hw, by simpa [π] using (QuotientGroup.mk_mul w (h : G)).symm⟩, hz⟩
    · rintro ⟨⟨w, hw, hwz⟩, hz⟩
      have hh : w⁻¹ * z ∈ H := (QuotientGroup.eq).mp (by simpa [π] using hwz)
      refine mem_iUnion.2 ⟨⟨w⁻¹ * z, hh⟩, ⟨w, hw, ?_⟩, hz⟩
      exact mul_inv_cancel_left w z
  have hμ (h : H) : μ (leftPiece h) = μ (rightPiece h⁻¹) := by
    have hpre : (fun y ↦ y * (h : G)⁻¹) ⁻¹' rightPiece h⁻¹ = leftPiece h := by
      ext y
      constructor
      · intro hy
        obtain ⟨⟨w, hw, hwz⟩, hyΔ⟩ := hy
        have hwz' : w = y := by simpa using hwz
        have hyw : y = w := hwz'.symm
        subst hyw
        exact ⟨hw, y * (h : G)⁻¹, hyΔ, by simp⟩
      · rintro ⟨hyW, d, hd, hd'⟩
        refine ⟨⟨y, hyW, rfl⟩, ?_⟩
        have hd'' : d * (h : G) = y := by simpa using hd'
        rw [← hd'']
        simpa using hd
    rw [← hpre]
    exact measure_preimage_mul_right μ ((h : G)⁻¹) (rightPiece h⁻¹)
  have hmass : νΔ (π '' W) = μ W := by
    have hopen : IsOpen (π '' W) := QuotientGroup.isOpenMap_coe W hWo
    rw [Measure.map_apply hπ hopen.measurableSet,
      Measure.restrict_apply (hopen.measurableSet.preimage hπ), ← hcoverR,
      measure_iUnion hdisjR hrightMeas]
    have hre : (∑' h : H, μ (rightPiece h)) = ∑' h : H, μ (leftPiece h) := by
      simp_rw [fun h : H ↦ (by simpa using (hμ h⁻¹).symm : μ (rightPiece h) = μ (leftPiece h⁻¹))]
      exact (Equiv.inv H).tsum_eq (fun h ↦ μ (leftPiece h))
    rw [hre, ← measure_iUnion hdisjL hleftMeas, hcoverL]
  let S (g : G) : Set (G ⧸ H) := (fun r ↦ π g * r) '' (π '' W)
  haveI : IsFiniteMeasureOnCompacts νΔ := by
    refine ⟨fun K hK ↦ ?_⟩
    have hsub : K ⊆ ⋃ g : G, S g := by
      intro q _
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      refine mem_iUnion.2 ⟨x, ⟨1, ?_, by simp [π]⟩⟩
      exact ⟨1, hW1, by simp [π]⟩
    have hSopen (g : G) : IsOpen (S g) :=
      (Homeomorph.mulLeft (π g)).isOpenMap _ (QuotientGroup.isOpenMap_coe W hWo)
    obtain ⟨t, ht⟩ := hK.elim_finite_subcover S hSopen hsub
    have hpiece (g : G) : νΔ (S g) = νΔ (π '' W) := by
      have him : S g = (fun r ↦ (π g)⁻¹ * r) ⁻¹' (π '' W) := by
        ext r
        constructor
        · rintro ⟨r', hr', rfl⟩
          have : (π g)⁻¹ * (π g * r') = r' := by
            rw [← mul_assoc, inv_mul_cancel, one_mul]
          simpa [this] using hr'
        · intro hr
          refine ⟨(π g)⁻¹ * r, hr, ?_⟩
          change π g * ((π g)⁻¹ * r) = r
          rw [← mul_assoc, mul_inv_cancel, one_mul]
      rw [him, measure_preimage_mul]
    have hle : νΔ K ≤ ∑ g ∈ t, νΔ (S g) :=
      (measure_mono ht).trans (measure_biUnion_finset_le t S)
    have hsum : ∑ g ∈ t, νΔ (S g) = (t.card : ℝ≥0∞) * νΔ (π '' W) := by
      simp [hpiece, Finset.sum_const, nsmul_eq_mul]
    rw [hsum, hmass] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top _)) hWlt)
  haveI : Measure.IsHaarMeasure ν := hν.1
  have hscale : νΔ = Measure.haarScalarFactor νΔ ν • ν :=
    Measure.isMulLeftInvariant_eq_smul νΔ ν
  have hc0 : Measure.haarScalarFactor νΔ ν ≠ 0 := by
    intro h0
    have hzeroμ : νΔ = (0 : Measure (G ⧸ H)) := by simpa [h0] using hscale
    have hzero : νΔ (π '' W) = 0 := by simp [hzeroμ]
    exact hWpos.ne' (hmass.symm.trans hzero)
  have hiffν : Integrable f ν ↔ Integrable f νΔ := by
    rw [hscale]
    exact (integrable_smul_measure (c := (Measure.haarScalarFactor νΔ ν : ℝ≥0∞))
      (by exact_mod_cast hc0) ENNReal.coe_ne_top).symm
  haveI : PolishSpace G := by
    letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
    haveI : IsUniformGroup G := isUniformGroup_of_commGroup (G := G)
    haveI : CompleteSpace G :=
      IsRightUniformGroup.completeSpace_of_weaklyLocallyCompactSpace (G := G)
    haveI := IsUniformGroup.uniformity_countably_generated (α := G)
    infer_instance
  have hinj : InjOn π Δ := by
    intro a ha b hb hab
    have hsub : (⟨a, ha⟩ : Δ) = ⟨b, hb⟩ := hbij.1 (by simpa using hab)
    exact congrArg Subtype.val hsub
  have hemb : MeasurableEmbedding (Δ.domRestrict π) :=
    ContinuousOn.measurableEmbedding (f := π) hΔ QuotientGroup.continuous_mk.continuousOn hinj
  have hmap : νΔ = Measure.map (Δ.domRestrict π) (μ.comap ((↑) : Δ → G)) := by
    have hsub : (μ.comap ((↑) : Δ → G)).map ((↑) : Δ → G) = μ.restrict Δ := by
      rw [(MeasurableEmbedding.subtype_coe hΔ).map_comap, Subtype.range_coe]
    calc
      νΔ = Measure.map π (μ.restrict Δ) := rfl
      _ = Measure.map π (Measure.map ((↑) : Δ → G) (μ.comap ((↑) : Δ → G))) := by rw [← hsub]
      _ = Measure.map (π ∘ ((↑) : Δ → G)) (μ.comap ((↑) : Δ → G)) :=
        Measure.map_map hπ continuous_subtype_val.measurable
      _ = Measure.map (Δ.domRestrict π) (μ.comap ((↑) : Δ → G)) := rfl
  rw [hiffν, hmap, hemb.integrable_map_iff]
  have hfun : (fun x : Δ ↦ f (π (x : G))) = (fun x ↦ f (π x)) ∘ ((↑) : Δ → G) := rfl
  rw [show f ∘ Δ.domRestrict π = (fun x ↦ f (π x)) ∘ ((↑) : Δ → G) from hfun]
  rw [← integrableOn_iff_comap_subtypeVal (f := fun x ↦ f (π x)) hΔ,
    integrable_indicator_iff hΔ]

include hH hΔ hbij hν in
/-- Paper: Proposition D.1.2.4, p. 748. The integral on the quotient
equals the integral of its pullback over a Borel fundamental domain. -/
theorem weilFundamentalDomain_integral {f : G ⧸ H → ℂ} (hf : Integrable f ν) :
    (∫ q, f q ∂ν) = ∫ x in Δ, f (QuotientGroup.mk x) ∂μ := by
  let : BorelSpace (G ⧸ H) := ⟨rfl⟩
  let : IsClosed (H : Set G) := hH
  let : (Measure.count : Measure H).IsHaarMeasure :=
    { lt_top_of_isCompact := fun _ hs ↦ Measure.count_apply_lt_top.mpr hs.finite_of_discrete
      open_pos := fun _ _ hs ↦ Measure.count_ne_zero hs }
  let π : G → G ⧸ H := QuotientGroup.mk
  have hπ : Measurable π := QuotientGroup.continuous_mk.measurable
  let tr (q : G ⧸ H) (h : H) : G := q.out * (h : G)
  let κ (q : G ⧸ H) : Measure G := Measure.count.map (tr q)
  have hκ : Measurable κ ∧ ν.bind κ = μ :=
    weilMeasure_eq_bind H hH μ Measure.count ν hν
  have hmap : (μ.restrict Δ).map π = ν := by
    ext S hS
    have hSΔ := (hπ hS).inter hΔ
    rw [Measure.map_apply hπ hS, Measure.restrict_apply (hπ hS), ← hκ.2,
      Measure.bind_apply hSΔ hκ.1.aemeasurable, ← lintegral_indicator_one hS]
    congr with q
    have htr : Measurable (tr q) := (continuous_const.mul continuous_subtype_val).measurable
    have hq (h : H) : π (tr q h) = q :=
      (QuotientGroup.mk_mul_of_mem q.out h.property).trans (Quotient.out_eq' q)
    change Measure.count.map (tr q) (π ⁻¹' S ∩ Δ) = S.indicator 1 q
    rw [Measure.map_apply htr hSΔ]
    by_cases hqS : q ∈ S
    · obtain ⟨a, ha⟩ := hbij.2 q
      let k : H := ⟨q.out⁻¹ * (a : G), QuotientGroup.eq.mp ((Quotient.out_eq' q).trans ha.symm)⟩
      have hk : tr q k = a := mul_inv_cancel_left _ _
      have hsingleton : tr q ⁻¹' (π ⁻¹' S ∩ Δ) = {k} := by
        ext h
        change (π (tr q h) ∈ S ∧ tr q h ∈ Δ) ↔ h = k
        constructor
        · rintro ⟨_, hh⟩
          have heq : (⟨tr q h, hh⟩ : Δ) = a := hbij.1 ((hq h).trans ha.symm)
          apply Subtype.ext
          exact mul_left_cancel ((congrArg Subtype.val heq).trans hk.symm)
        · rintro rfl
          exact ⟨(hq k).symm ▸ hqS, hk.symm ▸ a.property⟩
      rw [hsingleton, Measure.count_singleton, indicator_of_mem hqS, Pi.one_apply]
    · have hempty : tr q ⁻¹' (π ⁻¹' S ∩ Δ) = ∅ :=
        eq_empty_iff_forall_notMem.mpr fun h hh ↦ hqS ((hq h) ▸ hh.1)
      rw [hempty, measure_empty, indicator_of_notMem hqS]
  rw [← hmap] at hf ⊢
  exact integral_map hπ.aemeasurable hf.aestronglyMeasurable

-- Retain the existing topological and measure hypotheses in the signature.
set_option linter.unusedSectionVars false in
include hH hΔ hbij in
/-- Paper: Corollary D.1.2.5, p. 748. The integral of a subgroup-invariant function
over one Borel fundamental domain agrees with its integral over any other such domain. -/
theorem weilFundamentalDomain_integral_eq (hΔ' : MeasurableSet Δ')
    (hbij' : Function.Bijective (fun x : Δ' ↦ (QuotientGroup.mk x.val : G ⧸ H)))
    {f : G → ℂ} (hf : Measurable f) (hinv : ∀ (x : G) (h : H), f (x * (h : G)) = f x)
    (hint : IntegrableOn f Δ μ) :
    IntegrableOn f Δ' μ ∧ (∫ x in Δ, f x ∂μ) = ∫ x in Δ', f x ∂μ := by
  let : Countable H := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hdomain {D : Set G} (hD : MeasurableSet D)
      (hDq : Function.Bijective (fun x : D ↦ (QuotientGroup.mk x.val : G ⧸ H))) :
      IsFundamentalDomain H D μ := by
    apply IsFundamentalDomain.mk' hD.nullMeasurableSet
    intro x
    obtain ⟨y, hy⟩ := hDq.surjective (QuotientGroup.mk x)
    let h : H := ⟨x⁻¹ * (y : G), QuotientGroup.eq.mp hy.symm⟩
    have hh : (h : G) * x = (y : G) := by
      change (x⁻¹ * (y : G)) * x = (y : G)
      rw [mul_comm, mul_inv_cancel_left]
    refine ⟨h, ?_, ?_⟩
    · change (h : G) * x ∈ D
      rw [hh]
      exact y.property
    · intro k hk
      have hkq : (QuotientGroup.mk ((k : G) * x) : G ⧸ H) = QuotientGroup.mk x := by
        rw [mul_comm, QuotientGroup.mk_mul_of_mem x k.property]
      have hky : (⟨(k : G) * x, hk⟩ : D) = y := hDq.injective (hkq.trans hy.symm)
      exact Subtype.ext (mul_right_cancel ((congrArg Subtype.val hky).trans hh.symm))
  have hs := hdomain hΔ hbij
  have ht := hdomain hΔ' hbij'
  have hsmul (h : H) (x : G) : f (h • x) = f x := by
    change f ((h : G) * x) = f x
    rw [mul_comm, hinv]
  exact ⟨⟨hf.aestronglyMeasurable, (hs.hasFiniteIntegral_on_iff ht hsmul).mp hint.2⟩,
    hs.setIntegral_eq ht hsmul⟩

end FundamentalDomain

-- TODO(later): needs §D.1.4 (Definition D.1.4.5 and Lemma D.1.4.6) for the
-- annihilator and its canonical identification with the quotient dual in
-- Situation D.1.2.6, Theorem D.1.2.7 and Remark D.1.2.8.

end Weil

section Elementary

/-- Paper: (D.1.3.1), p. 749. The elementary group has real, torus, integer
and finite factors.
Deviation: The whole group is written additively, with `AddCircle 1` for ℝ/ℤ. -/
abbrev ElementaryLieGroup (m n r : ℕ) (F : Type*) :=
  EuclideanSpace ℝ (Fin m) × (Fin n → AddCircle (1 : ℝ)) × (Fin r → ℤ) × F

variable {m n r : ℕ} {F : Type*} [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F]
  [Finite F]

/-- Paper: (D.1.3.2), p. 749. The covering map reduces each real torus coordinate
modulo the integer lattice and leaves the other coordinates fixed. -/
def elementaryCover (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))
    (a : Fin r → ℤ) (b : F) : ElementaryLieGroup m n r F :=
  (xt.1, fun i ↦ (xt.2 i : AddCircle (1 : ℝ)), a, b)

/-- Paper: (D.1.3.1)–(D.1.3.2), p. 749. Every group element has a lift
for its real and torus coordinates. -/
theorem elementaryCover_surjective (a : Fin r → ℤ) (b : F)
    (x : EuclideanSpace ℝ (Fin m)) (z : Fin n → AddCircle (1 : ℝ)) :
    ∃ t : EuclideanSpace ℝ (Fin n), elementaryCover (x, t) a b = (x, z, a, b) := by
  choose s hs using fun i ↦ QuotientAddGroup.mk_surjective (z i)
  refine ⟨WithLp.toLp 2 s, ?_⟩
  simp only [elementaryCover, Prod.mk.injEq, true_and, and_true]
  funext i
  exact hs i

/-- Paper: (D.1.3.3), p. 749. The mixed partial is evaluated on the cover by
repeating differentiation along each coordinate vector according to its exponent. -/
def elementaryPartial (f : ElementaryLieGroup m n r F → ℂ)
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) : ℂ :=
  let realDirections : List (List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :=
    List.ofFn (fun i : Fin m ↦ List.replicate (β i) (EuclideanSpace.single i 1, 0))
  let torusDirections : List (List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n))) :=
    List.ofFn (fun i : Fin n ↦ List.replicate (γ i) (0, EuclideanSpace.single i 1))
  let directions : List (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) :=
    realDirections.flatten ++ torusDirections.flatten
  iteratedFDeriv ℝ directions.length (fun v ↦ f (elementaryCover v a b)) xt directions.get

/-- Paper: (D.1.3.3), p. 749. With both multi-indices zero, the partial is just the
pullback of the function to the cover. -/
theorem elementaryPartial_zero (f : ElementaryLieGroup m n r F → ℂ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    elementaryPartial f 0 0 xt a b = f (elementaryCover xt a b) := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let directions : List X :=
    ((List.ofFn (fun _ : Fin m ↦ ([] : List X))).flatten ++
      (List.ofFn (fun _ : Fin n ↦ ([] : List X))).flatten)
  have hnil (k : ℕ) : (List.replicate k ([] : List X)).flatten = [] := by
    induction k with
    | zero => rfl
    | succ j ih => rw [List.replicate_succ, List.flatten_cons, ih]; rfl
  have hdir : directions = [] := by
    dsimp [directions]
    rw [List.ofFn_const, List.ofFn_const]
    rw [hnil m, hnil n]
    rfl
  have hlen : directions.length = 0 := by rw [hdir]; rfl
  simp only [elementaryPartial]
  change (iteratedFDeriv ℝ directions.length (fun v ↦ f (elementaryCover v a b)) xt)
      directions.get = f (elementaryCover xt a b)
  have hiter (k : ℕ) (hk : k = 0) (d : Fin k → X) :
      (iteratedFDeriv ℝ k (fun v ↦ f (elementaryCover v a b)) xt) d =
        f (elementaryCover xt a b) := by
    subst k
    exact iteratedFDeriv_zero_apply d
  exact hiter directions.length hlen directions.get

/-- Paper: (D.1.3.4), p. 750. The lifted partials of a smooth fibre are smooth
and have the same value at any two lifts of a given group point. -/
theorem elementaryPartial_descends (f : ElementaryLieGroup m n r F → ℂ)
    (β : Fin m → ℕ) (γ : Fin n → ℕ) (a : Fin r → ℤ) (b : F)
    (hf : ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) :
    ContDiff ℝ ∞ (fun xt ↦ elementaryPartial f β γ xt a b) ∧
      ∀ u v, elementaryCover u a b = elementaryCover v a b →
        elementaryPartial f β γ u a b = elementaryPartial f β γ v a b := by
  let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
  let p : X → ℂ := fun w ↦ f (elementaryCover w a b)
  have hs {k : ℕ} (d : Fin k → X) :
      ContDiff ℝ ∞ (fun w ↦ (iteratedFDeriv ℝ k p w) d) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k ↦ X) ℂ d).contDiff.comp
      (hf.iteratedFDeriv_right (by simp))
  refine ⟨hs _, fun u v huv ↦ ?_⟩
  have hre : u.1 = v.1 := congrArg (fun y : ElementaryLieGroup m n r F ↦ y.1) huv
  have htor (i : Fin n) : (u.2 i : AddCircle (1 : ℝ)) = (v.2 i : AddCircle (1 : ℝ)) :=
    congrArg (fun y : ElementaryLieGroup m n r F ↦ y.2.1 i) huv
  have hshift : (fun w : X ↦ p (w + (v - u))) = p := by
    funext w
    apply congrArg f
    apply Prod.ext
    · change w.1 + (v.1 - u.1) = w.1
      simp [hre]
    · refine Prod.ext (funext fun i ↦ ?_) rfl
      change ((w.2 i + (v.2 i - u.2 i) : ℝ) : AddCircle (1 : ℝ)) = (w.2 i : AddCircle (1 : ℝ))
      simp only [AddCircle.coe_add, AddCircle.coe_sub, htor, sub_self, add_zero]
  have hderiv (k : ℕ) : iteratedFDeriv ℝ k p u = iteratedFDeriv ℝ k p v := by
    simpa only [hshift, add_sub_cancel] using
      (iteratedFDeriv_comp_add_right (f := p) k (v - u) u)
  dsimp only [elementaryPartial]
  dsimp only [p] at hderiv
  rw [hderiv]

/-- Paper: (D.1.3.7), p. 750. These are the two monomial multi-indices and the
two derivative multi-indices in the paper's order. -/
abbrev ElementarySchwartzIndex (m n r : ℕ) :=
  (Fin m → ℕ) × (Fin m → ℕ) × (Fin n → ℕ) × (Fin r → ℕ)

/-- Paper: (D.1.3.6)–(D.1.3.7), p. 750. Take the supremum of the absolute value
of a mixed partial multiplied by the real and integer monomials.
Deviation: The supremum ranges over all lifts of the torus coordinates. -/
def elementarySchwartzBound (f : ElementaryLieGroup m n r F → ℂ)
    (i : ElementarySchwartzIndex m n r) : ℝ≥0∞ :=
  ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
    ((‖((∏ k, (xt.1 k : ℂ) ^ i.1 k) * (∏ k, (a k : ℂ) ^ i.2.2.2 k)) *
      elementaryPartial f i.2.1 i.2.2.1 xt a b‖₊ : ℝ≥0∞))

/-- Paper: (D.1.3.7), p. 750. With every index zero the bound is the supremum
of the absolute value of the original function. -/
theorem elementarySchwartzBound_zero (f : ElementaryLieGroup m n r F → ℂ) :
    elementarySchwartzBound f (0, 0, 0, 0) =
      ⨆ g, (‖f g‖₊ : ℝ≥0∞) := by
  simp only [elementarySchwartzBound, Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul,
    elementaryPartial_zero]
  apply le_antisymm
  · exact iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ le_iSup (fun g ↦ (‖f g‖₊ : ℝ≥0∞)) (elementaryCover xt a b)
  · refine iSup_le fun ⟨x, z, a, b⟩ ↦ ?_
    obtain ⟨t, ht⟩ := elementaryCover_surjective a b x z
    rw [← ht]
    exact le_iSup_of_le (x, t) (le_iSup_of_le a (le_iSup_of_le b le_rfl))

section

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

/-- Paper: Definition D.1.3.1, p. 750. The zero function is smooth on each
discrete fibre and has finite weighted bounds. -/
theorem elementarySchwartzSubmodule_zero_mem :
    (0 : ElementaryLieGroup m n r F → ℂ) ∈
      {f | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
        ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)} := by
  refine ⟨fun _ _ ↦ contDiff_const, fun i ↦ ?_⟩
  simp [elementarySchwartzBound, elementaryPartial]

/-- Each weighted mixed-derivative bound is subadditive on fibrewise smooth functions. -/
theorem elementarySchwartzBound_add_le {f g : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)))
    (hg : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b)))
    (i : ElementarySchwartzIndex m n r) :
    elementarySchwartzBound (f + g) i ≤ elementarySchwartzBound f i + elementarySchwartzBound g i := by
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  have hpartial : elementaryPartial (f + g) i.2.1 i.2.2.1 xt a b =
      elementaryPartial f i.2.1 i.2.2.1 xt a b + elementaryPartial g i.2.1 i.2.2.1 xt a b := by
    have hadd (n : ℕ) :
        iteratedFDeriv ℝ n (fun v ↦ (f + g) (elementaryCover v a b)) xt =
          iteratedFDeriv ℝ n (fun v ↦ f (elementaryCover v a b)) xt +
          iteratedFDeriv ℝ n (fun v ↦ g (elementaryCover v a b)) xt :=
      iteratedFDeriv_add_apply ((hf a b).of_le (by simp)).contDiffAt
        ((hg a b).of_le (by simp)).contDiffAt
    dsimp only [elementaryPartial]
    rw [hadd]
    rfl
  rw [hpartial, mul_add]
  refine le_trans (ENNReal.coe_le_coe.mpr (nnNorm_add_le _ _)) ?_
  rw [ENNReal.coe_add]
  apply add_le_add <;> exact le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl))

/-- Paper: Definition D.1.3.1, p. 750. The Schwartz condition is closed under addition. -/
theorem elementarySchwartzSubmodule_add_mem {f g : ElementaryLieGroup m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞))
    (hg : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound g i < (⊤ : ℝ≥0∞)) :
    f + g ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by
  refine ⟨fun a b ↦ (hf.1 a b).add (hg.1 a b), fun i ↦ ?_⟩
  exact (elementarySchwartzBound_add_le hf.1 hg.1 i).trans_lt (ENNReal.add_lt_top.2 ⟨hf.2 i, hg.2 i⟩)

/-- Complex scalar multiplication scales each weighted mixed-derivative bound by its norm. -/
theorem elementarySchwartzBound_smul (c : ℂ) {f : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)))
    (i : ElementarySchwartzIndex m n r) :
    elementarySchwartzBound (c • f) i = (‖c‖₊ : ℝ≥0∞) * elementarySchwartzBound f i := by
  simp only [elementarySchwartzBound, ENNReal.mul_iSup]
  apply iSup_congr
  intro xt
  apply iSup_congr
  intro a
  apply iSup_congr
  intro b
  have hpartial : elementaryPartial (c • f) i.2.1 i.2.2.1 xt a b =
      c • elementaryPartial f i.2.1 i.2.2.1 xt a b := by
    have hsmul (n : ℕ) :
        iteratedFDeriv ℝ n (fun v ↦ (c • f) (elementaryCover v a b)) xt =
          c • iteratedFDeriv ℝ n (fun v ↦ f (elementaryCover v a b)) xt :=
      iteratedFDeriv_const_smul_apply ((hf a b).of_le (by simp)).contDiffAt
    dsimp only [elementaryPartial]
    rw [hsmul]
    rfl
  rw [hpartial, smul_eq_mul, mul_left_comm, nnNorm_mul, ENNReal.coe_mul]

/-- Paper: Definition D.1.3.1, p. 750. The Schwartz condition is closed under
complex scalar multiplication. -/
theorem elementarySchwartzSubmodule_smul_mem (c : ℂ) {f : ElementaryLieGroup m n r F → ℂ}
    (hf : (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)) :
    c • f ∈ {h | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ h (elementaryCover xt a b))) ∧
      ∀ i, elementarySchwartzBound h i < (⊤ : ℝ≥0∞)} := by
  refine ⟨fun a b ↦ (hf.1 a b).const_smul c, fun i ↦ ?_⟩
  rw [elementarySchwartzBound_smul c hf.1 i]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hf.2 i)

/-- Paper: Definition D.1.3.1, p. 750. A Schwartz function is smooth in the real
and torus variables on each discrete fibre and has finite bounds for all four multi-indices. -/
def elementarySchwartzSubmodule (m n r : ℕ) (F : Type*) :
    Submodule ℂ (ElementaryLieGroup m n r F → ℂ) where
  carrier := {f | (∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b))) ∧
    ∀ i, elementarySchwartzBound f i < (⊤ : ℝ≥0∞)}
  zero_mem' := elementarySchwartzSubmodule_zero_mem
  add_mem' := elementarySchwartzSubmodule_add_mem
  smul_mem' := elementarySchwartzSubmodule_smul_mem

end

/-- Paper: Definition D.1.3.1, p. 750. On the purely real factor the paper's
membership condition agrees with Mathlib's Schwartz class. -/
theorem elementarySchwartzSubmodule_real_iff
    (f : EuclideanSpace ℝ (Fin m) → ℂ) :
    (fun g : ElementaryLieGroup m 0 0 PUnit ↦ f g.1) ∈
        elementarySchwartzSubmodule m 0 0 PUnit ↔
      ∃ s : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ, (s : _ → ℂ) = f := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  let X := E × EuclideanSpace ℝ (Fin 0)
  let g : ElementaryLieGroup m 0 0 PUnit → ℂ := fun p ↦ f p.1
  let P : X →L[ℝ] E := ContinuousLinearMap.fst ℝ E _
  let J : E →L[ℝ] X := ContinuousLinearMap.inl ℝ E _
  let coord (j : Fin m) : E := EuclideanSpace.single j 1
  let liftedCoord (j : Fin m) : X := (coord j, 0)
  let directions (β : Fin m → ℕ) := (List.ofFn fun j ↦ List.replicate (β j) (liftedCoord j)).flatten
  let mixedPartial (β : Fin m → ℕ) (x : E) : ℂ :=
    iteratedFDeriv ℝ (directions β).length f x (fun j ↦ ((directions β).get j).1)
  let weight (α : Fin m → ℕ) (x : E) : ℝ := ∏ j, ‖x j‖ ^ α j
  -- The torus and lattice indices are empty, so only the real coordinates contribute.
  have hBound (hf : ContDiff ℝ ∞ f) (i : ElementarySchwartzIndex m 0 0) :
      elementarySchwartzBound g i =
        ⨆ x : E, ENNReal.ofReal (weight i.1 x * ‖mixedPartial i.2.1 x‖) := by
    have hPartial (xt : X) (a : Fin 0 → ℤ) (b : PUnit) :
        elementaryPartial g i.2.1 i.2.2.1 xt a b = mixedPartial i.2.1 xt.1 := by
      let l : List X := directions i.2.1 ++
        (List.ofFn fun j ↦ List.replicate (i.2.2.1 j) (0, EuclideanSpace.single j 1)).flatten
      have hl : l = directions i.2.1 := by simp [l]
      change (fun v : List X ↦ iteratedFDeriv ℝ v.length (f ∘ P) xt v.get) l = _
      rw [hl]
      change iteratedFDeriv ℝ (directions i.2.1).length (f ∘ P) xt (directions i.2.1).get = _
      rw [P.iteratedFDeriv_comp_right hf xt (by simp),
        ContinuousMultilinearMap.compContinuousLinearMap_apply]
      rfl
    simp only [elementarySchwartzBound, hPartial, Finset.univ_eq_empty (α := Fin 0),
      Finset.prod_empty, mul_one, ENNReal.coe_nnreal_eq, coe_nnNorm, norm_mul, norm_prod,
      norm_pow, Complex.norm_real, iSup_const]
    exact (show Function.Surjective (Prod.fst : X → E) from fun x ↦ ⟨(x, 0), rfl⟩).iSup_comp
      (fun x ↦ ENNReal.ofReal (weight i.1 x * ‖mixedPartial i.2.1 x‖))
  -- Group any tuple of coordinate directions by its multiplicities.
  have hCoord (hf : ContDiff ℝ ∞ f) {n : ℕ} (t : Fin n → Fin m) (x : E) :
      iteratedFDeriv ℝ n f x (fun j ↦ coord (t j)) = mixedPartial (fun j ↦ (List.ofFn t).count j) x := by
    let β (j : Fin m) := (List.ofFn t).count j
    let l := (List.finRange m).flatMap fun j ↦ List.replicate (β j) j
    have hPerm : (List.ofFn t).Perm l := by
      apply List.perm_iff_count.mpr
      intro j
      rw [List.count_flatMap, ← Fin.sum_univ_def]
      simp [List.count_replicate, β]
    have hDirs : l.map liftedCoord = directions β := by
      simp [l, directions, List.ofFn_eq_map, List.flatMap, Function.comp_def]
    have h := iteratedFDeriv_apply_list_perm hf (Prod.fst : X → E) (hPerm.map liftedCoord) x
    rw [hDirs, List.map_ofFn] at h
    let eval (s : Σ k, Fin k → X) := iteratedFDeriv ℝ s.1 f x (fun j ↦ (s.2 j).1)
    exact (congrArg eval (List.equivSigmaTuple.apply_symm_apply ⟨n, liftedCoord ∘ t⟩)).symm.trans h
  change ((∀ (a : Fin 0 → ℤ) (b : PUnit), ContDiff ℝ ∞ (f ∘ P)) ∧
    ∀ i, elementarySchwartzBound g i < (⊤ : ℝ≥0∞)) ↔ _
  constructor
  · rintro ⟨hs, hb⟩
    have hf : ContDiff ℝ ∞ f := (hs 0 PUnit.unit).comp J.contDiff
    refine ⟨⟨f, hf, ?_⟩, rfl⟩
    intro k n
    let α (i : Option (Fin m)) : Fin m → ℕ := i.elim 0 (fun j ↦ Pi.single j k)
    let β (t : Fin n → Fin m) (j : Fin m) := (List.ofFn t).count j
    let idx (i : Option (Fin m)) (t : Fin n → Fin m) :
        ElementarySchwartzIndex m 0 0 := (α i, β t, 0, 0)
    obtain ⟨C, hC⟩ := Finite.bddAbove_range (fun p : Option (Fin m) × (Fin n → Fin m) ↦
      (elementarySchwartzBound g (idx p.1 p.2)).toReal)
    refine ⟨((m : ℝ) + 1) ^ k * (Fintype.card (Fin n → Fin m) * C), fun x ↦ ?_⟩
    -- Include the constant weight so the maximum exists even when m = 0.
    let c (i : Option (Fin m)) : ℝ := i.elim 1 (fun j ↦ ‖x j‖)
    obtain ⟨i, -, hi⟩ := Finset.exists_max_image Finset.univ c Finset.univ_nonempty
    have hsum : ‖x‖ ≤ ∑ j, ‖x j‖ := by
      conv_lhs => rw [← (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr x]
      refine (norm_sum_le _ _).trans_eq ?_
      simp only [norm_smul, OrthonormalBasis.norm_eq_one, EuclideanSpace.basisFun_repr, mul_one]
    have hsize : ‖x‖ ≤ ((m : ℝ) + 1) * c i := calc
      _ ≤ ∑ _j : Fin m, c i :=
        hsum.trans (Finset.sum_le_sum fun j _ ↦ hi (some j) (Finset.mem_univ _))
      _ ≤ _ := by
        have hnonneg : 0 ≤ c i := zero_le_one.trans (hi none (Finset.mem_univ _))
        simp [add_mul, hnonneg]
    have hw : weight (α i) x = c i ^ k := by
      cases i <;> simp [weight, α, c, Pi.single, Function.update, apply_ite]
    have hpow : ‖x‖ ^ k ≤ ((m : ℝ) + 1) ^ k * weight (α i) x := by
      rw [hw, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hsize k
    let T := iteratedFDeriv ℝ n f x
    have hpoint (t : Fin n → Fin m) : weight (α i) x * ‖T (fun j ↦ coord (t j))‖ ≤ C := by
      rw [show T (fun j ↦ coord (t j)) = mixedPartial (β t) x from hCoord hf t x]
      have hle : ENNReal.ofReal (weight (α i) x * ‖mixedPartial (β t) x‖) ≤
          elementarySchwartzBound g (idx i t) := by
        rw [hBound hf]
        exact le_iSup (fun y ↦ ENNReal.ofReal (weight (α i) y * ‖mixedPartial (β t) y‖)) x
      have h := ENNReal.toReal_mono (hb (idx i t)).ne hle
      rw [ENNReal.toReal_ofReal (by dsimp [weight]; positivity)] at h
      exact h.trans (hC (mem_range_self (i, t)))
    calc
      ‖x‖ ^ k * ‖T‖ ≤ (((m : ℝ) + 1) ^ k * weight (α i) x) *
          ∑ t : Fin n → Fin m, ‖T (fun j ↦ coord (t j))‖ :=
        mul_le_mul hpow (norm_multilinear_le_sum_euclidean_basis T) (norm_nonneg _) (by positivity)
      _ = ((m : ℝ) + 1) ^ k * ∑ t : Fin n → Fin m, weight (α i) x * ‖T (fun j ↦ coord (t j))‖ := by
        rw [mul_assoc, Finset.mul_sum]
      _ ≤ ((m : ℝ) + 1) ^ k * ∑ _t : Fin n → Fin m, C :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ ↦ hpoint t) (by positivity)
      _ = _ := by simp
  · rintro ⟨s, rfl⟩
    refine ⟨fun _ _ ↦ s.smooth'.comp P.contDiff, fun i ↦ ?_⟩
    rw [hBound s.smooth']
    obtain ⟨C, -, hC⟩ := s.decay (∑ j, i.1 j) (directions i.2.1).length
    refine lt_of_le_of_lt (b := ENNReal.ofReal C)
      (iSup_le fun x ↦ ENNReal.ofReal_le_ofReal ?_) ENNReal.ofReal_lt_top
    have hw : weight i.1 x ≤ ‖x‖ ^ (∑ j, i.1 j) := calc
      _ ≤ ∏ j, ‖x‖ ^ i.1 j :=
        Finset.prod_le_prod₀ (fun _ _ ↦ by positivity) fun j _ ↦
          pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le x j) _
      _ = _ := Finset.prod_pow_eq_pow_sum _ _ _
    have he (j : Fin (directions i.2.1).length) : ‖((directions i.2.1).get j).1‖ = 1 := by
      have hmem := List.get_mem (directions i.2.1) j
      simp only [directions, List.mem_flatten, List.mem_ofFn] at hmem
      obtain ⟨_, ⟨q, rfl⟩, hq⟩ := hmem
      rw [List.eq_of_mem_replicate hq]
      change ‖EuclideanSpace.single q (1 : ℝ)‖ = 1
      simpa only [EuclideanSpace.basisFun_apply] using
        (EuclideanSpace.basisFun (Fin m) ℝ).norm_eq_one q
    have hD : ‖mixedPartial i.2.1 x‖ ≤ ‖iteratedFDeriv ℝ (directions i.2.1).length s x‖ := by
      simpa only [mixedPartial, he, Finset.prod_const_one, mul_one] using
        (iteratedFDeriv ℝ (directions i.2.1).length s x).le_opNorm
          (fun j ↦ ((directions i.2.1).get j).1)
    exact (mul_le_mul hw hD (norm_nonneg _) (by positivity)).trans (hC x)

section

omit [AddCommGroup F] [TopologicalSpace F] [DiscreteTopology F] [Finite F]

/-- Paper: Definition D.1.3.1, p. 750. Every weighted bound vanishes on the zero function. -/
theorem elementarySchwartzSeminorm_map_zero (i : ElementarySchwartzIndex m n r) :
    (elementarySchwartzBound (0 : elementarySchwartzSubmodule m n r F).val i).toReal = 0 := by
  change (elementarySchwartzBound (0 : ElementaryLieGroup m n r F → ℂ) i).toReal = 0
  simp [elementarySchwartzBound, elementaryPartial]

/-- Paper: Definition D.1.3.1, p. 750. Each real-valued weighted bound is subadditive
on the Schwartz submodule. -/
theorem elementarySchwartzSeminorm_add_le (i : ElementarySchwartzIndex m n r)
    (f g : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (f + g).val i).toReal ≤
      (elementarySchwartzBound f.val i).toReal + (elementarySchwartzBound g.val i).toReal := by
  change (elementarySchwartzBound (f.val + g.val) i).toReal ≤ _
  exact (ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨(f.property.2 i).ne, (g.property.2 i).ne⟩)
    (elementarySchwartzBound_add_le f.property.1 g.property.1 i)).trans_eq
    (ENNReal.toReal_add (f.property.2 i).ne (g.property.2 i).ne)

/-- Paper: Definition D.1.3.1, p. 750. Scaling a Schwartz function multiplies its
real-valued weighted bound by the norm of the scalar. -/
theorem elementarySchwartzSeminorm_smul (i : ElementarySchwartzIndex m n r)
    (c : ℂ) (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (c • f).val i).toReal =
      ‖c‖ * (elementarySchwartzBound f.val i).toReal := by
  change (elementarySchwartzBound (c • f.val) i).toReal = _
  rw [elementarySchwartzBound_smul c f.property.1, ENNReal.toReal_mul]
  rfl

/-- Paper: Definition D.1.3.1, p. 750. Each real-valued weighted bound is invariant
under negation on the Schwartz submodule. -/
theorem elementarySchwartzSeminorm_neg (i : ElementarySchwartzIndex m n r)
    (f : elementarySchwartzSubmodule m n r F) :
    (elementarySchwartzBound (-f).val i).toReal =
      (elementarySchwartzBound f.val i).toReal := by
  change (elementarySchwartzBound (-f.val) i).toReal = _
  rw [← neg_one_smul ℂ f.val, elementarySchwartzBound_smul (-1 : ℂ) f.property.1]
  simp

/-- Paper: Definition D.1.3.1, p. 750. On the Schwartz submodule each finite
weighted bound gives a real-valued seminorm. -/
def elementarySchwartzSeminorm (i : ElementarySchwartzIndex m n r) :
    Seminorm ℂ (elementarySchwartzSubmodule m n r F) where
  toFun f := (elementarySchwartzBound f.val i).toReal
  map_zero' := elementarySchwartzSeminorm_map_zero i
  add_le' := elementarySchwartzSeminorm_add_le i
  smul' := elementarySchwartzSeminorm_smul i
  neg' := elementarySchwartzSeminorm_neg i

end

/-- Paper: Definition D.1.3.1, p. 750. The locally convex topology on
the Schwartz space is generated by the weighted derivative seminorms. -/
abbrev ElementarySchwartz (m n r : ℕ) (F : Type*) :=
  WithGeneratingSeminorms (elementarySchwartzSubmodule m n r F) elementarySchwartzSeminorm

instance : CoeFun (ElementarySchwartz m n r F) (fun _ ↦ ElementaryLieGroup m n r F → ℂ) where
  coe f := (show elementarySchwartzSubmodule m n r F from f).val

/-- A linear family of elementary Schwartz functions on a barrelled space is continuous
if its point evaluations are continuous linear functionals. -/
theorem continuous_toElementarySchwartz_of_eval
    {U F : Type*} [AddCommGroup U] [Module ℂ U] [UniformSpace U]
    [IsUniformAddGroup U] [ContinuousSMul ℂ U] [BarrelledSpace ℂ U]
    {m n r : ℕ} (A : U →ₗ[ℂ] ElementarySchwartz m n r F)
    (he : ∀ g, ∃ L : U →L[ℂ] ℂ, ∀ u, L u = A u g) : Continuous A := by
  choose ev hev using he
  refine (withGeneratingSeminorms_spec _ _).continuous_of_continuous_comp A fun i ↦ ?_
  let p := (elementarySchwartzSeminorm i).comp A
  apply p.continuous_of_lowerSemicontinuous
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro R
  by_cases hR : 0 ≤ R
  · let X := EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)
    let D (xt : X) (a : Fin r → ℤ) (b : F) (u : U) :=
      elementaryPartial (A u).val i.2.1 i.2.2.1 xt a b
    have hD (xt : X) (a : Fin r → ℤ) (b : F) : Continuous (D xt a b) := by
      let V (x : X) := ev (elementaryCover x a b)
      have hV (u : U) : ContDiff ℝ ∞ (fun x ↦ V x u) := by
        simpa only [V, hev] using ((A u).property.1 a b)
      have hdiff (k : ℕ) (v : Fin k → X) :
          Continuous (fun u ↦ iteratedFDeriv ℝ k (fun x ↦ A u (elementaryCover x a b)) xt v) := by
        obtain ⟨L, hL⟩ := exists_clm_iteratedFDeriv_apply V hV k xt v
        simpa only [funext hL, V, hev] using L.continuous
      exact hdiff _ _
    let w (xt : X) (a : Fin r → ℤ) : ℂ :=
      (∏ k, (xt.1 k : ℂ) ^ i.1 k) * (∏ k, (a k : ℂ) ^ i.2.2.2 k)
    have hset : p ⁻¹' Iic R = ⋂ xt, ⋂ a, ⋂ b, {u | ‖w xt a * D xt a b u‖ ≤ R} := by
      ext u
      change (elementarySchwartzBound (A u).val i).toReal ≤ R ↔ _
      rw [← ENNReal.ofReal_le_ofReal_iff hR, ENNReal.ofReal_toReal ((A u).property.2 i).ne]
      simp only [elementarySchwartzBound, iSup_le_iff, mem_iInter, mem_ofPred_eq, X, w, D,
        ENNReal.coe_nnreal_eq, coe_nnNorm, ENNReal.ofReal_le_ofReal_iff hR]
    rw [hset]
    exact isClosed_iInter fun xt ↦ isClosed_iInter fun a ↦ isClosed_iInter fun b ↦
      isClosed_le (continuous_const.mul (hD xt a b)).norm continuous_const
  · have hset : p ⁻¹' Iic R = ∅ := by
      ext u
      exact ⟨fun h ↦ (hR ((apply_nonneg p u).trans h)).elim, False.elim⟩
    rw [hset]
    exact isClosed_empty

/-- Paper: Definition D.1.3.1, p. 750. At zero multi-indices the seminorm is the
uniform norm of the underlying function. -/
theorem elementarySchwartzSeminorm_zero (f : ElementarySchwartz m n r F) :
    elementarySchwartzSeminorm (0, 0, 0, 0) f = ⨆ g, ‖f g‖ := by
  change (elementarySchwartzBound f.val (0, 0, 0, 0)).toReal = _
  rw [elementarySchwartzBound_zero, ENNReal.toReal_iSup (fun _ ↦ ENNReal.coe_ne_top)]
  rfl

/-- Paper: Definition D.1.3.1, p. 750. The canonical seminorm family generates
the topology of the space. -/
theorem elementarySchwartz_withSeminorms :
    WithSeminorms (E := ElementarySchwartz m n r F) elementarySchwartzSeminorm := by
  exact withGeneratingSeminorms_spec _ _

/-- Paper: Remark D.1.3.2, p. 750. The Schwartz topology is Hausdorff. -/
theorem elementarySchwartz_t2 : T2Space (ElementarySchwartz m n r F) := by
  let hp := withGeneratingSeminorms_spec (elementarySchwartzSubmodule m n r F) elementarySchwartzSeminorm
  have : T1Space (ElementarySchwartz m n r F) := hp.T1_of_separating fun f hf ↦ by
    let i : ElementarySchwartzIndex m n r := (0, 0, 0, 0)
    refine ⟨i, fun hzero ↦ hf ?_⟩
    apply Subtype.ext
    funext g
    have h : ‖f g‖ ≤ elementarySchwartzSeminorm i f := by
      change (‖f.val g‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound f.val i).toReal
      apply ENNReal.toReal_mono (f.property.2 i).ne
      rw [show i = (0, 0, 0, 0) from rfl, elementarySchwartzBound_zero]
      exact le_iSup (fun x ↦ (‖f.val x‖₊ : ENNReal)) g
    change f.val g = 0
    exact norm_eq_zero.mp (le_antisymm (h.trans_eq hzero) (norm_nonneg _))
  infer_instance

/-- Paper: Lemma D.1.3.3, p. 750. Pullback by a topological group automorphism
gives a linear topological automorphism of the elementary Schwartz space. -/
theorem elementarySchwartz_pullback (φ : ElementaryLieGroup m n r F ≃ₜ+ ElementaryLieGroup m n r F) :
    ∃ e : ElementarySchwartz m n r F ≃L[ℂ] ElementarySchwartz m n r F,
      ∀ f g, e f g = f (φ g) := by sorry

/-- `1 + ‖x‖ ^ j` is controlled by the constant term and the pure powers of the coordinates. -/
lemma one_add_euclidean_pow_le {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (j : ℕ) :
    1 + ‖x‖ ^ j ≤
      (1 + (Real.sqrt (d : ℝ)) ^ j) * (1 + ∑ i : Fin d, |x i| ^ j) := by
  cases j with
  | zero =>
    simp only [pow_zero]
    have hsum : (0 : ℝ) ≤ ∑ i : Fin d, (1 : ℝ) :=
      Finset.sum_nonneg fun _ _ => zero_le_one
    linarith
  | succ j =>
    cases d with
    | zero =>
      have : IsEmpty (Fin 0) := ⟨Fin.elim0⟩
      have hx0 : ‖x‖ = 0 := by
        rw [← sq_eq_zero_iff, EuclideanSpace.real_norm_sq_eq]
        simp [Finset.univ_eq_empty]
      simp [hx0, Real.sqrt_zero, zero_pow (Nat.succ_ne_zero _), Finset.univ_eq_empty]
    | succ d =>
      have : Nonempty (Fin (Nat.succ d)) := ⟨0⟩
      obtain ⟨i0, hi0, hmax⟩ :=
        Finset.exists_max_image (Finset.univ : Finset (Fin (Nat.succ d)))
          (fun i => |x i|) Finset.univ_nonempty
      have hsq : ‖x‖ ^ 2 ≤ (Nat.succ d : ℝ) * |x i0| ^ 2 := by
        rw [EuclideanSpace.real_norm_sq_eq]
        calc
          ∑ i, (x i) ^ 2 = ∑ i, |x i| ^ 2 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← sq_abs]
          _ ≤ ∑ i, |x i0| ^ 2 :=
            Finset.sum_le_sum fun i hi => pow_le_pow_left₀ (abs_nonneg _) (hmax i hi) 2
          _ = (Nat.succ d : ℝ) * |x i0| ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hnorm : ‖x‖ ≤ Real.sqrt (Nat.succ d : ℝ) * |x i0| := by
        refine le_of_sq_le_sq ?_ (mul_nonneg (Real.sqrt_nonneg _) (abs_nonneg _))
        rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
        exact hsq
      set t : ℝ := (Real.sqrt (Nat.succ d : ℝ)) ^ Nat.succ j
      have ht : 0 ≤ t := pow_nonneg (Real.sqrt_nonneg _) _
      have hpow : ‖x‖ ^ Nat.succ j ≤ t * |x i0| ^ Nat.succ j := by
        calc
          ‖x‖ ^ Nat.succ j ≤ (Real.sqrt (Nat.succ d : ℝ) * |x i0|) ^ Nat.succ j :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm _
          _ = t * |x i0| ^ Nat.succ j := by rw [mul_pow]
      have hi0le : |x i0| ^ Nat.succ j ≤ ∑ i, |x i| ^ Nat.succ j :=
        Finset.single_le_sum (fun i _ => pow_nonneg (abs_nonneg (x i)) (Nat.succ j)) hi0
      have hnormsum : ‖x‖ ^ Nat.succ j ≤ t * ∑ i, |x i| ^ Nat.succ j :=
        hpow.trans (mul_le_mul_of_nonneg_left hi0le ht)
      have hS : 0 ≤ ∑ i : Fin (Nat.succ d), |x i| ^ Nat.succ j :=
        Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _
      calc
        1 + ‖x‖ ^ Nat.succ j ≤ 1 + t * ∑ i, |x i| ^ Nat.succ j :=
          add_le_add_right hnormsum 1
        _ ≤ (1 + t) * (1 + ∑ i, |x i| ^ Nat.succ j) := by nlinarith

/-- A monomial in the coordinates is at most the corresponding power of the Euclidean norm. -/
lemma prod_abs_pow_le_norm_pow {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) (α : Fin d → ℕ) :
    ∏ k, |x k| ^ α k ≤ ‖x‖ ^ ∑ k, α k := by
  calc
    ∏ k, |x k| ^ α k ≤ ∏ k, ‖x‖ ^ α k := by
      refine Finset.prod_le_prod₀ (fun _ _ => pow_nonneg (abs_nonneg _) _) fun k _ => ?_
      exact pow_le_pow_left₀ (abs_nonneg _)
        (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le x k) (α k)
    _ = ‖x‖ ^ ∑ k, α k := Finset.prod_pow_eq_pow_sum _ _ _

/-- Mixed partials are additive on fibrewise smooth functions. -/
lemma elementaryPartial_add {f g : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)))
    (hg : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ g (elementaryCover xt a b)))
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    elementaryPartial (f + g) β γ xt a b =
      elementaryPartial f β γ xt a b + elementaryPartial g β γ xt a b := by
  have hadd (n : ℕ) :
      iteratedFDeriv ℝ n (fun v ↦ (f + g) (elementaryCover v a b)) xt =
        iteratedFDeriv ℝ n (fun v ↦ f (elementaryCover v a b)) xt +
        iteratedFDeriv ℝ n (fun v ↦ g (elementaryCover v a b)) xt :=
    iteratedFDeriv_add_apply ((hf a b).of_le (by simp)).contDiffAt
      ((hg a b).of_le (by simp)).contDiffAt
  dsimp only [elementaryPartial]
  rw [hadd]
  rfl

/-- Mixed partials are homogeneous on fibrewise smooth functions. -/
lemma elementaryPartial_smul (c : ℂ) {f : ElementaryLieGroup m n r F → ℂ}
    (hf : ∀ a b, ContDiff ℝ ∞ (fun xt ↦ f (elementaryCover xt a b)))
    (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    elementaryPartial (c • f) β γ xt a b = c • elementaryPartial f β γ xt a b := by
  have hsmul (n : ℕ) :
      iteratedFDeriv ℝ n (fun v ↦ (c • f) (elementaryCover v a b)) xt =
        c • iteratedFDeriv ℝ n (fun v ↦ f (elementaryCover v a b)) xt :=
    iteratedFDeriv_const_smul_apply ((hf a b).of_le (by simp)).contDiffAt
  dsimp only [elementaryPartial]
  rw [hsmul]
  rfl

/-- A coordinate monomial times a partial is bounded by the corresponding Euclidean weight. -/
lemma monomial_norm_le_p1 (f : ElementaryLieGroup m n r F → ℂ)
    (α : Fin m → ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ) (δ : Fin r → ℕ)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ‖((∏ k, (xt.1 k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)) *
        elementaryPartial f β γ xt a b‖ ≤
      (1 + ‖xt.1‖ ^ ∑ k, α k) *
        (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ ∑ k, δ k) *
        ‖elementaryPartial f β γ xt a b‖ := by
  let aVec : EuclideanSpace ℝ (Fin r) := WithLp.toLp 2 (fun k ↦ (a k : ℝ))
  have hX : ‖∏ k, (xt.1 k : ℂ) ^ α k‖ = ∏ k, |xt.1 k| ^ α k := by
    simp [norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hA : ‖∏ k, (a k : ℂ) ^ δ k‖ = ∏ k, |aVec k| ^ δ k := by
    simp [aVec, norm_prod, norm_pow, Complex.norm_intCast]
  rw [norm_mul, norm_mul, hX, hA]
  have hx : ∏ k, |xt.1 k| ^ α k ≤ 1 + ‖xt.1‖ ^ ∑ k, α k :=
    (prod_abs_pow_le_norm_pow xt.1 α).trans (le_add_of_nonneg_left zero_le_one)
  have ha : ∏ k, |aVec k| ^ δ k ≤ 1 + ‖aVec‖ ^ ∑ k, δ k :=
    (prod_abs_pow_le_norm_pow aVec δ).trans (le_add_of_nonneg_left zero_le_one)
  have hprod :
      (∏ k, |xt.1 k| ^ α k) * (∏ k, |aVec k| ^ δ k) ≤
        (1 + ‖xt.1‖ ^ ∑ k, α k) * (1 + ‖aVec‖ ^ ∑ k, δ k) :=
    mul_le_mul hx ha (Finset.prod_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _)
      (add_nonneg zero_le_one (pow_nonneg (norm_nonneg _) _))
  simpa [aVec, mul_assoc] using
    mul_le_mul_of_nonneg_right hprod (norm_nonneg (elementaryPartial f β γ xt a b))

/-- A monomial times a partial is bounded by the corresponding Schwartz seminorm. -/
lemma monomial_partial_le_seminorm (α : Fin m → ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (δ : Fin r → ℕ) (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ‖((∏ k, (xt.1 k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)) *
        elementaryPartial f β γ xt a b‖ ≤
      elementarySchwartzSeminorm (α, β, γ, δ) f := by
  let z : ℂ := ((∏ k, (xt.1 k : ℂ) ^ α k) * (∏ k, (a k : ℂ) ^ δ k)) *
      elementaryPartial f β γ xt a b
  have hcoe : (‖z‖₊ : ℝ≥0∞) ≤ elementarySchwartzBound f.val (α, β, γ, δ) :=
    le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl))
  change ‖z‖ ≤ (elementarySchwartzBound f.val (α, β, γ, δ)).toReal
  rw [← toReal_coe_nnNorm z]
  exact ENNReal.toReal_mono (f.property.2 (α, β, γ, δ)).ne hcoe

lemma prod_abs_pow_single {d : ℕ} (x : Fin d → ℝ) (i : Fin d) (j : ℕ) :
    ∏ k, |x k| ^ (Pi.single i j k) = |x i| ^ j := by
  rw [Finset.prod_eq_single i]
  · simp [Pi.single_eq_same]
  · intro k _ hk
    simp [Pi.single_eq_of_ne hk, pow_zero]
  · intro hk
    exact (hk (Finset.mem_univ i)).elim

lemma zero_monomial_partial_le (β : Fin m → ℕ) (γ : Fin n → ℕ) (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    ‖elementaryPartial f β γ xt a b‖ ≤ elementarySchwartzSeminorm (0, β, γ, 0) f := by
  have h := monomial_partial_le_seminorm (0 : Fin m → ℕ) β γ (0 : Fin r → ℕ) f xt a b
  simpa only [Pi.zero_apply, pow_zero, Finset.prod_const_one, one_mul] using h

lemma single_real_partial_le (i : Fin m) (j : ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    |xt.1 i| ^ j * ‖elementaryPartial f β γ xt a b‖ ≤
      elementarySchwartzSeminorm (Pi.single i j, β, γ, 0) f := by
  have h := monomial_partial_le_seminorm (Pi.single i j) β γ (0 : Fin r → ℕ) f xt a b
  have hnorm : ‖((∏ k, (xt.1 k : ℂ) ^ (Pi.single i j k)) * (∏ k, (a k : ℂ) ^ (0 : ℕ))) *
        elementaryPartial f β γ xt a b‖ =
      |xt.1 i| ^ j * ‖elementaryPartial f β γ xt a b‖ := by
    rw [norm_mul, norm_mul]
    simp only [norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast,
      Pi.zero_apply, pow_zero, Finset.prod_const_one, norm_one, mul_one]
    rw [prod_abs_pow_single (fun k => xt.1 k) i j]
  rw [← hnorm]
  exact h

lemma single_int_partial_le (k0 : Fin r) (j' : ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    |(a k0 : ℝ)| ^ j' * ‖elementaryPartial f β γ xt a b‖ ≤
      elementarySchwartzSeminorm ((0 : Fin m → ℕ), β, γ, Pi.single k0 j') f := by
  have h := monomial_partial_le_seminorm (0 : Fin m → ℕ) β γ (Pi.single k0 j') f xt a b
  have hnorm : ‖((∏ k, (xt.1 k : ℂ) ^ (0 : ℕ)) * (∏ k, (a k : ℂ) ^ (Pi.single k0 j' k))) *
        elementaryPartial f β γ xt a b‖ =
      |(a k0 : ℝ)| ^ j' * ‖elementaryPartial f β γ xt a b‖ := by
    rw [norm_mul, norm_mul]
    simp only [norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast,
      Pi.zero_apply, pow_zero, Finset.prod_const_one, norm_one, one_mul]
    rw [prod_abs_pow_single (fun k => (a k : ℝ)) k0 j']
  rw [← hnorm]
  exact h

lemma single_both_partial_le (i : Fin m) (k0 : Fin r) (j j' : ℕ) (β : Fin m → ℕ) (γ : Fin n → ℕ)
    (f : ElementarySchwartz m n r F)
    (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F) :
    |xt.1 i| ^ j * |(a k0 : ℝ)| ^ j' * ‖elementaryPartial f β γ xt a b‖ ≤
      elementarySchwartzSeminorm (Pi.single i j, β, γ, Pi.single k0 j') f := by
  have h := monomial_partial_le_seminorm (Pi.single i j) β γ (Pi.single k0 j') f xt a b
  have hnorm : ‖((∏ k, (xt.1 k : ℂ) ^ (Pi.single i j k)) *
        (∏ k, (a k : ℂ) ^ (Pi.single k0 j' k))) * elementaryPartial f β γ xt a b‖ =
      |xt.1 i| ^ j * |(a k0 : ℝ)| ^ j' * ‖elementaryPartial f β γ xt a b‖ := by
    rw [norm_mul, norm_mul]
    simp only [norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_intCast]
    rw [prod_abs_pow_single (fun k => xt.1 k) i j,
      prod_abs_pow_single (fun k => (a k : ℝ)) k0 j']
  rw [← hnorm]
  exact h

/-- Paper: Lemma D.1.3.4, p. 751. Polynomial weights in the two Euclidean lengths,
with a fixed mixed partial for each seminorm, generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_P1 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
            (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
            ‖elementaryPartial f i.2.2.1 i.2.2.2 xt a b‖) := by
  let bound (i : ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)) (f : ElementarySchwartz m n r F) : ℝ≥0∞ :=
    ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
      ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
        (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
        ‖elementaryPartial f i.2.2.1 i.2.2.2 xt a b‖)
  letI : DecidableEq (ElementarySchwartzIndex m n r) := Classical.decEq _
  have hest (i : ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)) :
      ∃ (s : Finset (ElementarySchwartzIndex m n r)) (C : ℝ), 0 ≤ C ∧
        ∀ f, bound i f ≤ ENNReal.ofReal (C * ((s.sup elementarySchwartzSeminorm) f)) := by
    let j := i.1
    let j' := i.2.1
    let β := i.2.2.1
    let γ := i.2.2.2
    let Cx : ℝ := 1 + (Real.sqrt (m : ℝ)) ^ j
    let Ca : ℝ := 1 + (Real.sqrt (r : ℝ)) ^ j'
    let s0 : Finset (ElementarySchwartzIndex m n r) := {(0, β, γ, (0 : Fin r → ℕ))}
    let sx : Finset (ElementarySchwartzIndex m n r) :=
      Finset.univ.image fun t : Fin m => (Pi.single t j, β, γ, (0 : Fin r → ℕ))
    let sy : Finset (ElementarySchwartzIndex m n r) :=
      Finset.univ.image fun t : Fin r => ((0 : Fin m → ℕ), β, γ, Pi.single t j')
    let sz : Finset (ElementarySchwartzIndex m n r) :=
      Finset.univ.image fun q : Fin m × Fin r => (Pi.single q.1 j, β, γ, Pi.single q.2 j')
    let s := ((s0 ∪ sx) ∪ sy) ∪ sz
    let C : ℝ := Cx * Ca * ((m + 1) * (r + 1) : ℝ)
    refine ⟨s, C, by positivity, fun f => ?_⟩
    refine iSup_le fun xt => iSup_le fun a => iSup_le fun b => ?_
    let aVec := (WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))
    let N : ℝ := ‖elementaryPartial f β γ xt a b‖
    let Sx : ℝ := ∑ t : Fin m, |xt.1 t| ^ j
    let Sa : ℝ := ∑ t : Fin r, |aVec t| ^ j'
    let supS : ℝ := (s.sup elementarySchwartzSeminorm) f
    have hx : 1 + ‖xt.1‖ ^ j ≤ Cx * (1 + Sx) := by
      simpa only [Cx, Sx] using one_add_euclidean_pow_le xt.1 j
    have ha : 1 + ‖aVec‖ ^ j' ≤ Ca * (1 + Sa) := by
      simpa only [Ca, Sa] using one_add_euclidean_pow_le aVec j'
    have hcoord (t : Fin r) : aVec t = (a t : ℝ) := by
      simp [aVec]
    have hmem0 : ((0 : Fin m → ℕ), β, γ, (0 : Fin r → ℕ)) ∈ s :=
      Finset.mem_union_left sz (Finset.mem_union_left sy (Finset.mem_union_left sx
        (Finset.mem_singleton_self _)))
    have hmemx (t : Fin m) : (Pi.single t j, β, γ, (0 : Fin r → ℕ)) ∈ s :=
      Finset.mem_union_left sz (Finset.mem_union_left sy (Finset.mem_union_right s0
        (Finset.mem_image_of_mem _ (Finset.mem_univ t))))
    have hmemy (t : Fin r) : ((0 : Fin m → ℕ), β, γ, Pi.single t j') ∈ s :=
      Finset.mem_union_left sz (Finset.mem_union_right (s0 ∪ sx)
        (Finset.mem_image_of_mem _ (Finset.mem_univ t)))
    have hmemz (t : Fin m) (u : Fin r) : (Pi.single t j, β, γ, Pi.single u j') ∈ s :=
      Finset.mem_union_right ((s0 ∪ sx) ∪ sy)
        (Finset.mem_image_of_mem _ (Finset.mem_univ (t, u)))
    have hN : N ≤ supS :=
      (zero_monomial_partial_le β γ f xt a b).trans (Seminorm.le_finset_sup_apply hmem0)
    have hxle (t : Fin m) : |xt.1 t| ^ j * N ≤ supS :=
      (single_real_partial_le t j β γ f xt a b).trans (Seminorm.le_finset_sup_apply (hmemx t))
    have hale (t : Fin r) : |aVec t| ^ j' * N ≤ supS := by
      rw [hcoord t]
      exact (single_int_partial_le t j' β γ f xt a b).trans (Seminorm.le_finset_sup_apply (hmemy t))
    have hboth (t : Fin m) (u : Fin r) : |xt.1 t| ^ j * |aVec u| ^ j' * N ≤ supS := by
      rw [hcoord u]
      exact (single_both_partial_le t u j j' β γ f xt a b).trans
        (Seminorm.le_finset_sup_apply (hmemz t u))
    have hweights : (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') * N ≤
        Cx * Ca * ((1 + Sx) * (1 + Sa) * N) := by
      have hmul : (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') ≤ (Cx * (1 + Sx)) * (Ca * (1 + Sa)) :=
        mul_le_mul hx ha (by positivity) (by positivity)
      calc
        (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') * N ≤
            ((Cx * (1 + Sx)) * (Ca * (1 + Sa))) * N :=
          mul_le_mul_of_nonneg_right hmul (norm_nonneg _)
        _ = Cx * Ca * ((1 + Sx) * (1 + Sa) * N) := by ring
    have hexpand : (1 + Sx) * (1 + Sa) * N =
        N + ∑ t : Fin m, |xt.1 t| ^ j * N + ∑ t : Fin r, |aVec t| ^ j' * N +
          ∑ t : Fin m, ∑ u : Fin r, |xt.1 t| ^ j * |aVec u| ^ j' * N := by
      have hSx : Sx * N = ∑ t : Fin m, |xt.1 t| ^ j * N := by simp only [Sx, Finset.sum_mul]
      have hSa : Sa * N = ∑ t : Fin r, |aVec t| ^ j' * N := by simp only [Sa, Finset.sum_mul]
      have hSS : Sx * Sa * N =
          ∑ t : Fin m, ∑ u : Fin r, |xt.1 t| ^ j * |aVec u| ^ j' * N := by
        simp only [Sx, Sa]
        rw [mul_assoc, Finset.sum_mul, Finset.sum_mul]
        simp_rw [Finset.mul_sum, ← mul_assoc]
      calc
        (1 + Sx) * (1 + Sa) * N = N + Sx * N + Sa * N + Sx * Sa * N := by ring
        _ = N + ∑ t : Fin m, |xt.1 t| ^ j * N + ∑ t : Fin r, |aVec t| ^ j' * N +
            ∑ t : Fin m, ∑ u : Fin r, |xt.1 t| ^ j * |aVec u| ^ j' * N := by rw [hSx, hSa, hSS]
    have hconst : supS + ∑ _t : Fin m, supS + ∑ _t : Fin r, supS +
        ∑ _t : Fin m, ∑ _u : Fin r, supS = ((m + 1) * (r + 1) : ℝ) * supS := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    have hsumle : (1 + Sx) * (1 + Sa) * N ≤ ((m + 1) * (r + 1) : ℝ) * supS := by
      rw [hexpand]
      refine (add_le_add (add_le_add (add_le_add hN ?_) ?_) ?_).trans_eq hconst
      · exact Finset.sum_le_sum fun t _ => hxle t
      · exact Finset.sum_le_sum fun t _ => hale t
      · exact Finset.sum_le_sum fun t _ => Finset.sum_le_sum fun u _ => hboth t u
    have hfinal : (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') * N ≤ C * supS := by
      calc
        (1 + ‖xt.1‖ ^ j) * (1 + ‖aVec‖ ^ j') * N ≤
            Cx * Ca * ((1 + Sx) * (1 + Sa) * N) := hweights
        _ ≤ Cx * Ca * (((m + 1) * (r + 1) : ℝ) * supS) :=
          mul_le_mul_of_nonneg_left hsumle (by positivity)
        _ = C * supS := by ring
    have hEnn := ENNReal.ofReal_le_ofReal hfinal
    simpa only [j, j', β, γ, aVec, N, supS] using hEnn
  have hfin (i) (f : ElementarySchwartz m n r F) : bound i f ≠ ⊤ := by
    obtain ⟨_, _, _, hle⟩ := hest i
    exact ((hle f).trans_lt ENNReal.ofReal_lt_top).ne
  have hadd (i) (f g : ElementarySchwartz m n r F) :
      bound i (f + g) ≤ bound i f + bound i g := by
    refine iSup_le fun xt => iSup_le fun a => iSup_le fun b => ?_
    have hp := elementaryPartial_add f.property.1 g.property.1 i.2.2.1 i.2.2.2 xt a b
    set w : ℝ := (1 + ‖xt.1‖ ^ i.1) *
      (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1)
    have hw : 0 ≤ w := by positivity
    have hsum : w * ‖elementaryPartial (↑(f + g)) i.2.2.1 i.2.2.2 xt a b‖ ≤
        w * ‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b‖ +
          w * ‖elementaryPartial (↑g) i.2.2.1 i.2.2.2 xt a b‖ := by
      calc
        w * ‖elementaryPartial (↑(f + g)) i.2.2.1 i.2.2.2 xt a b‖ =
            w * ‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b +
              elementaryPartial (↑g) i.2.2.1 i.2.2.2 xt a b‖ := by
          rw [show elementaryPartial (↑(f + g)) i.2.2.1 i.2.2.2 xt a b =
            elementaryPartial (f.val + g.val) i.2.2.1 i.2.2.2 xt a b by rfl, hp]
        _ ≤ w * (‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b‖ +
            ‖elementaryPartial (↑g) i.2.2.1 i.2.2.2 xt a b‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hw
        _ = w * ‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b‖ +
            w * ‖elementaryPartial (↑g) i.2.2.1 i.2.2.2 xt a b‖ := by ring
    refine (ENNReal.ofReal_le_ofReal hsum).trans ?_
    rw [ENNReal.ofReal_add (mul_nonneg hw (norm_nonneg _)) (mul_nonneg hw (norm_nonneg _))]
    exact add_le_add
      (le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl)))
      (le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl)))
  have hsmul (i) (c : ℂ) (f : ElementarySchwartz m n r F) :
      bound i (c • f) = ENNReal.ofReal ‖c‖ * bound i f := by
    have hbody : ∀ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ)
        (b : F),
        ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
          (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
          ‖elementaryPartial (↑(c • f)) i.2.2.1 i.2.2.2 xt a b‖) =
          ENNReal.ofReal ‖c‖ * ENNReal.ofReal ((1 + ‖xt.1‖ ^ i.1) *
            (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
            ‖elementaryPartial (↑f) i.2.2.1 i.2.2.2 xt a b‖) := by
      intro xt a b
      have hp := elementaryPartial_smul c f.property.1 i.2.2.1 i.2.2.2 xt a b
      have hfun : elementaryPartial (↑(c • f)) i.2.2.1 i.2.2.2 xt a b =
          elementaryPartial (c • f.val) i.2.2.1 i.2.2.2 xt a b := rfl
      rw [hfun, hp, norm_smul]
      have hcomm : (1 + ‖xt.1‖ ^ i.1) *
          (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
            (‖c‖ * ‖elementaryPartial f.val i.2.2.1 i.2.2.2 xt a b‖) =
          ‖c‖ * ((1 + ‖xt.1‖ ^ i.1) *
            (1 + ‖(WithLp.toLp 2 (fun k ↦ (a k : ℝ)) : EuclideanSpace ℝ (Fin r))‖ ^ i.2.1) *
              ‖elementaryPartial f.val i.2.2.1 i.2.2.2 xt a b‖) := by ring
      rw [hcomm, ENNReal.ofReal_mul (norm_nonneg _)]
    simp_rw [bound, hbody, ENNReal.mul_iSup]
  let p : SeminormFamily ℂ (ElementarySchwartz m n r F)
      (ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ)) :=
    fun i => Seminorm.of (fun f => (bound i f).toReal)
      (fun f g => by
        calc
          (bound i (f + g)).toReal ≤ (bound i f + bound i g).toReal :=
            ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hfin i f, hfin i g⟩) (hadd i f g)
          _ = (bound i f).toReal + (bound i g).toReal :=
            ENNReal.toReal_add (hfin i f) (hfin i g))
      (fun c f => by
        rw [hsmul i c f]
        exact ENNReal.toReal_ofReal_mul ‖c‖ (bound i f) (norm_nonneg c))
  refine ⟨p, ?_, ?_⟩
  · refine elementarySchwartz_withSeminorms.congr
      (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
      (Seminorm.IsBounded.of_real (f := LinearMap.id) ?_)
    · intro i
      obtain ⟨s, C, hC, hle⟩ := hest i
      refine ⟨s, C, fun f => ?_⟩
      have hreal : (bound i f).toReal ≤ C * ((s.sup elementarySchwartzSeminorm) f) := by
        refine (ENNReal.toReal_mono ENNReal.ofReal_lt_top.ne (hle f)).trans_eq ?_
        exact ENNReal.toReal_ofReal (mul_nonneg hC (apply_nonneg _ _))
      change (bound i f).toReal ≤ C * ((s.sup elementarySchwartzSeminorm) f)
      exact hreal
    · intro idx
      let iP : ℕ × ℕ × (Fin m → ℕ) × (Fin n → ℕ) :=
        (∑ k, idx.1 k, ∑ k, idx.2.2.2 k, idx.2.1, idx.2.2.1)
      refine ⟨{iP}, 1, fun f => ?_⟩
      rw [Finset.sup_singleton, one_mul]
      change elementarySchwartzSeminorm idx f ≤ (bound iP f).toReal
      have hpt : elementarySchwartzBound f.val idx ≤ bound iP f := by
        refine iSup_le fun xt => iSup_le fun a => iSup_le fun b => ?_
        have hle := monomial_norm_le_p1 f.val idx.1 idx.2.1 idx.2.2.1 idx.2.2.2 xt a b
        have hcoe : (‖((∏ k, (xt.1 k : ℂ) ^ idx.1 k) * (∏ k, (a k : ℂ) ^ idx.2.2.2 k)) *
            elementaryPartial f.val idx.2.1 idx.2.2.1 xt a b‖₊ : ℝ≥0∞) =
            ENNReal.ofReal ‖((∏ k, (xt.1 k : ℂ) ^ idx.1 k) * (∏ k, (a k : ℂ) ^ idx.2.2.2 k)) *
              elementaryPartial f.val idx.2.1 idx.2.2.1 xt a b‖ := by
          rw [show ‖((∏ k, (xt.1 k : ℂ) ^ idx.1 k) * (∏ k, (a k : ℂ) ^ idx.2.2.2 k)) *
              elementaryPartial f.val idx.2.1 idx.2.2.1 xt a b‖ =
              (‖((∏ k, (xt.1 k : ℂ) ^ idx.1 k) * (∏ k, (a k : ℂ) ^ idx.2.2.2 k)) *
                elementaryPartial f.val idx.2.1 idx.2.2.1 xt a b‖₊ : ℝ) from rfl,
            ENNReal.ofReal_coe_nnreal]
        rw [hcoe]
        exact (ENNReal.ofReal_le_ofReal hle).trans
          (le_iSup_of_le xt (le_iSup_of_le a (le_iSup_of_le b le_rfl)))
      exact ENNReal.toReal_mono (hfin iP f) hpt
  · intro i f
    change ENNReal.ofReal (bound i f).toReal = bound i f
    exact ENNReal.ofReal_toReal (hfin i f)

/-- Paper: Lemma D.1.3.4, p. 751. Complex polynomial weights in the real and integer
coordinates, with a fixed mixed partial for each seminorm, generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_P2 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        ((Fin m → ℕ) × (Fin n → ℕ) × MvPolynomial (Fin m ⊕ Fin r) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          ENNReal.ofReal
            (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.2.2‖ *
              ‖elementaryPartial f i.1 i.2.1 xt a b‖) := by sorry

/-- Paper: Lemma D.1.3.4, p. 751. Polynomial weights applied to
constant-coefficient polynomial differential operators generate the Schwartz topology. -/
theorem elementarySchwartz_withSeminorms_P3 :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F)
        (MvPolynomial (Fin m ⊕ Fin r) ℂ × MvPolynomial (Fin m ⊕ Fin n) ℂ),
      WithSeminorms p ∧ ∀ i f, ENNReal.ofReal (p i f) =
        ⨆ (xt : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)) (a : Fin r → ℤ) (b : F),
          (‖MvPolynomial.eval (Sum.elim (fun k ↦ (xt.1 k : ℂ)) (fun k ↦ (a k : ℂ))) i.1 *
            i.2.coeff.sum (fun d c ↦ c * elementaryPartial f
              (fun k ↦ d (.inl k)) (fun k ↦ d (.inr k)) xt a b)‖₊ : ℝ≥0∞) := by sorry

/-- Paper: Lemma D.1.3.5(1), p. 752. Summing the monomial seminorms with each
multi-index of total degree at most N gives a family of norms generating the topology. -/
theorem elementarySchwartz_withSeminorms_sum :
    ∃ p : SeminormFamily ℂ (ElementarySchwartz m n r F) ℕ,
      WithSeminorms p ∧ (∀ N f, p N f = 0 ↔ f = 0) ∧
        ∀ N f, p N f =
          ∑ i : (Fin m → Fin (N + 1)) × (Fin m → Fin (N + 1)) ×
                (Fin n → Fin (N + 1)) × (Fin r → Fin (N + 1)),
            if (∑ k, (i.1 k).val) ≤ N ∧ (∑ k, (i.2.1 k).val) ≤ N ∧
                (∑ k, (i.2.2.1 k).val) ≤ N ∧ (∑ k, (i.2.2.2 k).val) ≤ N then
              elementarySchwartzSeminorm
                (fun k ↦ (i.1 k).val, fun k ↦ (i.2.1 k).val,
                  fun k ↦ (i.2.2.1 k).val, fun k ↦ (i.2.2.2 k).val) f
            else 0 := by sorry

/-- Paper: Lemma D.1.3.5(2), p. 752. The elementary Schwartz space is Fréchet. -/
theorem elementarySchwartz_isFrechet : IsFrechetTVS (ElementarySchwartz m n r F) := by sorry

end Elementary

section ElementaryTensor

variable {m n r : ℕ} {F : Type*}

/-- Paper: (D.1.3.17), p. 752. The j-th bound on a sequence is its absolute sum
with weight `(1 + |a|)^j`, where the integer lattice inherits the Euclidean length. -/
def rapidDecaySequenceBound (j : ℕ) (s : (Fin r → ℤ) → ℂ) : ℝ≥0∞ :=
  ∑' a : Fin r → ℤ,
    (1 + (‖(WithLp.toLp 2 (fun i ↦ (a i : ℝ)) : EuclideanSpace ℝ (Fin r))‖₊ : ℝ≥0∞)) ^ j *
      (‖s a‖₊ : ℝ≥0∞)

/-- Paper: (D.1.3.17), p. 752. On a point mass at the origin the weighted sum
is the norm of the mass, for every weight. -/
theorem rapidDecaySequenceBound_singleton_zero (j : ℕ) (c : ℂ) :
    rapidDecaySequenceBound (r := r) j (({0} : Set (Fin r → ℤ)).indicator (fun _ ↦ c)) =
      (‖c‖₊ : ℝ≥0∞) := by
  rw [rapidDecaySequenceBound, tsum_eq_single 0]
  · have h0 : (WithLp.toLp 2 (fun i : Fin r ↦ (((0 : Fin r → ℤ) i : ℤ) : ℝ)) :
        EuclideanSpace ℝ (Fin r)) = 0 := by
      ext i; simp
    rw [h0]
    simp
  · intro a ha
    simp [Set.indicator_of_notMem (show a ∉ ({0} : Set (Fin r → ℤ)) from ha)]

/-- Paper: Remark D.1.3.6, p. 752. The zero lattice sequence has finite weighted
absolute sums of all orders. -/
theorem rapidDecaySequenceSubmodule_zero_mem :
    ∀ j, rapidDecaySequenceBound j (0 : (Fin r → ℤ) → ℂ) < ⊤ := by
  intro j
  simp [rapidDecaySequenceBound]

/-- The weighted absolute sum of a sum of sequences is at most the sum of the
weighted absolute sums. -/
theorem rapidDecaySequenceBound_add_le (j : ℕ) (s t : (Fin r → ℤ) → ℂ) :
    rapidDecaySequenceBound j (s + t) ≤
      rapidDecaySequenceBound j s + rapidDecaySequenceBound j t := by
  unfold rapidDecaySequenceBound
  rw [← tsum_add]
  refine tsum_le_tsum fun a ↦ ?_
  rw [← mul_add]
  gcongr
  simp only [Pi.add_apply]
  exact_mod_cast nnNorm_add_le _ _

/-- Paper: Remark D.1.3.6, p. 752. Rapidly decreasing lattice sequences are closed
under addition. -/
theorem rapidDecaySequenceSubmodule_add_mem {s t : (Fin r → ℤ) → ℂ}
    (hs : ∀ j, rapidDecaySequenceBound j s < ⊤)
    (ht : ∀ j, rapidDecaySequenceBound j t < ⊤) :
    ∀ j, rapidDecaySequenceBound j (s + t) < ⊤ := fun j ↦
  (rapidDecaySequenceBound_add_le j s t).trans_lt (ENNReal.add_lt_top.2 ⟨hs j, ht j⟩)

/-- Scaling a sequence multiplies its weighted absolute sum by the norm of the scalar. -/
theorem rapidDecaySequenceBound_smul (j : ℕ) (c : ℂ) (s : (Fin r → ℤ) → ℂ) :
    rapidDecaySequenceBound j (c • s) = (‖c‖₊ : ℝ≥0∞) * rapidDecaySequenceBound j s := by
  unfold rapidDecaySequenceBound
  rw [← ENNReal.tsum_mul_left]
  congr 1
  ext a
  simp only [Pi.smul_apply, smul_eq_mul, nnNorm_mul, ENNReal.coe_mul]
  ring

/-- Paper: Remark D.1.3.6, p. 752. Rapidly decreasing lattice sequences are closed
under complex scalar multiplication. -/
theorem rapidDecaySequenceSubmodule_smul_mem (c : ℂ) {s : (Fin r → ℤ) → ℂ}
    (hs : ∀ j, rapidDecaySequenceBound j s < ⊤) :
    ∀ j, rapidDecaySequenceBound j (c • s) < ⊤ := fun j ↦ by
  rw [rapidDecaySequenceBound_smul]
  exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hs j)

/-- Paper: Remark D.1.3.6, p. 752. A rapidly decreasing lattice sequence
has finite weighted absolute sums of all orders. -/
def rapidDecaySequenceSubmodule (r : ℕ) : Submodule ℂ ((Fin r → ℤ) → ℂ) where
  carrier := {s | ∀ j, rapidDecaySequenceBound j s < ⊤}
  zero_mem' := rapidDecaySequenceSubmodule_zero_mem
  add_mem' := rapidDecaySequenceSubmodule_add_mem
  smul_mem' := rapidDecaySequenceSubmodule_smul_mem

/-- Paper: Remark D.1.3.6, p. 752. Every finitely supported lattice sequence
belongs to the rapidly decreasing sequence space. -/
theorem mem_rapidDecaySequenceSubmodule_of_finiteSupport (s : (Fin r → ℤ) → ℂ)
    (hs : (Function.support s).Finite) :
    s ∈ rapidDecaySequenceSubmodule r := by
  intro j
  rw [rapidDecaySequenceBound, tsum_eq_sum (s := hs.toFinset)]
  · exact ENNReal.sum_lt_top.2 fun a _ ↦
      ENNReal.mul_lt_top (ENNReal.pow_lt_top (by simp)) ENNReal.coe_lt_top
  · intro a ha
    simp [Function.notMem_support.1 (fun h ↦ ha (hs.mem_toFinset.2 h))]

/-- Paper: (D.1.3.17), p. 752. Each weighted absolute sum vanishes on the zero sequence. -/
theorem rapidDecaySequenceSeminorm_map_zero (j : ℕ) :
    (rapidDecaySequenceBound j (0 : rapidDecaySequenceSubmodule r).val).toReal = 0 := by
  simp [rapidDecaySequenceBound]

/-- Paper: (D.1.3.17), p. 752. Each real-valued weighted absolute sum is subadditive
on rapidly decreasing lattice sequences. -/
theorem rapidDecaySequenceSeminorm_add_le (j : ℕ) (s t : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (s + t).val).toReal ≤
      (rapidDecaySequenceBound j s.val).toReal + (rapidDecaySequenceBound j t.val).toReal := by
  have hs : rapidDecaySequenceBound j s.val < ⊤ := s.2 j
  have ht : rapidDecaySequenceBound j t.val < ⊤ := t.2 j
  rw [← ENNReal.toReal_add hs.ne ht.ne]
  exact ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨hs, ht⟩).ne
    (rapidDecaySequenceBound_add_le j s.val t.val)

/-- Paper: (D.1.3.17), p. 752. Scaling a rapidly decreasing lattice sequence
multiplies its real-valued weighted absolute sum by the norm of the scalar. -/
theorem rapidDecaySequenceSeminorm_smul (j : ℕ) (c : ℂ) (s : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (c • s).val).toReal =
      ‖c‖ * (rapidDecaySequenceBound j s.val).toReal := by
  rw [Submodule.coe_smul, rapidDecaySequenceBound_smul, ENNReal.toReal_mul]
  simp

/-- Paper: (D.1.3.17), p. 752. Each real-valued weighted absolute sum is invariant
under negation on rapidly decreasing lattice sequences. -/
theorem rapidDecaySequenceSeminorm_neg (j : ℕ) (s : rapidDecaySequenceSubmodule r) :
    (rapidDecaySequenceBound j (-s).val).toReal = (rapidDecaySequenceBound j s.val).toReal := by
  simp [rapidDecaySequenceBound]

/-- Paper: (D.1.3.17), p. 752. The finite weighted sums are seminorms on the
space of rapidly decreasing sequences. -/
def rapidDecaySequenceSeminorm (j : ℕ) : Seminorm ℂ (rapidDecaySequenceSubmodule r) where
  toFun s := (rapidDecaySequenceBound j s.val).toReal
  map_zero' := rapidDecaySequenceSeminorm_map_zero j
  add_le' := rapidDecaySequenceSeminorm_add_le j
  smul' := rapidDecaySequenceSeminorm_smul j
  neg' := rapidDecaySequenceSeminorm_neg j

/-- Paper: Remark D.1.3.6, p. 753. The weighted absolute-sum seminorms generate
the locally convex topology on the rapidly decreasing lattice sequences. -/
abbrev RapidDecaySequence (r : ℕ) :=
  WithGeneratingSeminorms (rapidDecaySequenceSubmodule r) rapidDecaySequenceSeminorm

instance : CoeFun (RapidDecaySequence r) (fun _ ↦ (Fin r → ℤ) → ℂ) where
  coe s := (show rapidDecaySequenceSubmodule r from s).val

/-- Paper: (D.1.3.17), p. 752. On a rapidly decreasing sequence the seminorm
of order zero is the unweighted absolute sum. -/
theorem rapidDecaySequenceSeminorm_zero (s : RapidDecaySequence r) :
    rapidDecaySequenceSeminorm 0 s = ∑' a, ‖s a‖ := by
  change (rapidDecaySequenceBound 0 _).toReal = _
  rw [rapidDecaySequenceBound, ENNReal.tsum_toReal_eq (fun a ↦ by simp)]
  simp

/-- Paper: Remark D.1.3.6, p. 753. The weighted sums generate the topology
and give a Fréchet space. -/
theorem rapidDecaySequence_withSeminorms :
    WithSeminorms (E := RapidDecaySequence r) rapidDecaySequenceSeminorm :=
  withGeneratingSeminorms_spec _ _

/-- Paper: Remark D.1.3.6, p. 753. The rapidly decreasing sequence space is Fréchet. -/
theorem rapidDecaySequence_isFrechet : IsFrechetTVS (RapidDecaySequence r) := by sorry

/-- Paper: Remark D.1.3.6, p. 752. Reading a sequence as a function on the
integer lattice identifies it with the elementary Schwartz space of that lattice. -/
theorem rapidDecaySequence_equiv_elementarySchwartz :
    ∃ e : RapidDecaySequence r ≃L[ℂ] ElementarySchwartz 0 0 r PUnit,
      ∀ s (g : ElementaryLieGroup 0 0 r PUnit), e s g = s g.2.2.1 := by sorry

-- TODO(later): needs §C.2.4 for the nuclearity assertion in Remark D.1.3.6.

/-- Paper: (D.1.3.18), p. 753. Bracket the projective tensor product into two pairs. -/
abbrev elementaryProjectiveTensor (m n r : ℕ) (F : Type*) :=
  ProjectiveTensor
    (ProjectiveTensor (SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)
      (ElementarySchwartz 0 n 0 PUnit))
    (ProjectiveTensor (RapidDecaySequence r) (F → ℂ))

/-- Paper: (D.1.3.18), p. 753. The four factors carry the projective tensor topology.
The real factor uses Mathlib's Schwartz space, and the torus factor is the
elementary Schwartz space with its other factors trivial. -/
def ElementarySchwartzTensor (m n r : ℕ) (F : Type*) : Type _ :=
  elementaryProjectiveTensor m n r F

section TensorInstances

set_option synthInstance.maxHeartbeats 100000

instance : AddCommGroup (ElementarySchwartzTensor m n r F) :=
  inferInstanceAs (AddCommGroup (elementaryProjectiveTensor m n r F))

instance : Module ℂ (ElementarySchwartzTensor m n r F) :=
  inferInstanceAs (Module ℂ (elementaryProjectiveTensor m n r F))

instance : UniformSpace (ElementarySchwartzTensor m n r F) :=
  inferInstanceAs (UniformSpace (elementaryProjectiveTensor m n r F))

instance : IsUniformAddGroup (ElementarySchwartzTensor m n r F) :=
  inferInstanceAs (IsUniformAddGroup (elementaryProjectiveTensor m n r F))

instance : ContinuousSMul ℂ (ElementarySchwartzTensor m n r F) :=
  WithSeminorms.continuousSMul (E := ElementarySchwartzTensor m n r F)
    (withGeneratingSeminorms_spec _ _)

instance : UniformContinuousConstSMul ℂ (ElementarySchwartzTensor m n r F) :=
  uniformContinuousConstSMul_of_continuousConstSMul ℂ _

end TensorInstances

/-- Paper: (D.1.3.19), p. 753. Form the pure tensor in the projective product
of the four Schwartz factors. -/
def elementarySchwartzTmul (u : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ)
    (v : ElementarySchwartz 0 n 0 PUnit) (s : RapidDecaySequence r) (c : F → ℂ) :
    ElementarySchwartzTensor m n r F :=
  (u ⊗ₜ[ℂ] v) ⊗ₜ[ℂ] (s ⊗ₜ[ℂ] c)

variable [hF : Finite F]

include hF in
/-- Paper: Lemma D.1.3.7(1), p. 753. Multiplying the four factors pointwise on
pure tensors gives a linear embedding that induces the projective tensor product topology. -/
theorem elementarySchwartzTensor_isEmbedding :
    ∃ φ : ElementarySchwartzTensor m n r F →ₗ[ℂ] ElementarySchwartz m n r F,
      IsEmbedding φ ∧
        ∀ (u : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) (v : ElementarySchwartz 0 n 0 PUnit)
          (s : RapidDecaySequence r) (c : F → ℂ) (g : ElementaryLieGroup m n r F),
          φ (elementarySchwartzTmul u v s c) g =
            u g.1 * v (0, g.2.1, 0, PUnit.unit) * s g.2.2.1 * c g.2.2.2 := by sorry

include hF in
/-- Paper: Lemma D.1.3.7(2), p. 753. Multiplication of the factors on pure tensors
extends uniquely to a linear topological isomorphism from the projective completion.
Deviation: We complete the iterated algebraic projective tensor product once. -/
theorem elementarySchwartzTensor_completion_equiv :
    ∃! e : UniformSpace.Completion (ElementarySchwartzTensor m n r F) ≃L[ℂ]
        ElementarySchwartz m n r F,
      ∀ (u : SchwartzMap (EuclideanSpace ℝ (Fin m)) ℂ) (v : ElementarySchwartz 0 n 0 PUnit)
        (s : RapidDecaySequence r) (c : F → ℂ) (g : ElementaryLieGroup m n r F),
        e (UniformSpace.Completion.coe' (α := ElementarySchwartzTensor m n r F)
          (elementarySchwartzTmul u v s c)) g =
          u g.1 * v (0, g.2.1, 0, PUnit.unit) * s g.2.2.1 * c g.2.2.2 := by sorry

-- TODO(paper-gap): In the proof of Lemma D.1.3.7(2), (D.1.3.33) bounds a global
-- seminorm by a quantity tending to zero as the real or lattice coordinate goes to infinity.

/-- Paper: Lemma D.1.3.7(3), p. 753. The strong dual of the elementary Schwartz
space is complete. Completeness of the Schwartz space is part of Lemma D.1.3.5(2). -/
theorem elementarySchwartz_strongDual_complete :
    CompleteSpace (StrongDual ℂ (ElementarySchwartz m n r F)) := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. Evaluation gives a linear topological
isomorphism from the elementary Schwartz space to its strong double dual. -/
theorem elementarySchwartz_reflexive :
    ∃ e : ElementarySchwartz m n r F ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (ElementarySchwartz m n r F)),
      ∀ f L, e f L = L f := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. Evaluation gives a linear topological
isomorphism from the strong dual to its own strong double dual. -/
theorem elementarySchwartz_strongDual_reflexive :
    let D := StrongDual ℂ (ElementarySchwartz m n r F)
    ∃ e : D ≃L[ℂ] StrongDual ℂ (StrongDual ℂ D), ∀ L M, e L M = M L := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. Closed bounded subsets of the elementary
Schwartz space are compact. -/
theorem elementarySchwartz_isCompact_of_isClosed_isVonNBounded
    {A : Set (ElementarySchwartz m n r F)} (hA : IsClosed A) (hb : IsVonNBounded ℂ A) :
    IsCompact A := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. Closed bounded subsets of the strong dual
of the elementary Schwartz space are compact. -/
theorem elementarySchwartz_strongDual_isCompact_of_isClosed_isVonNBounded
    {A : Set (StrongDual ℂ (ElementarySchwartz m n r F))}
    (hA : IsClosed A) (hb : IsVonNBounded ℂ A) :
    IsCompact A := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. The elementary Schwartz space is barrelled. -/
theorem elementarySchwartz_barrelled : BarrelledSpace ℂ (ElementarySchwartz m n r F) := by sorry

/-- Paper: Lemma D.1.3.7(3), p. 753. The strong dual of the elementary Schwartz
space is barrelled. -/
theorem elementarySchwartz_strongDual_barrelled :
    BarrelledSpace ℂ (StrongDual ℂ (ElementarySchwartz m n r F)) := by sorry

-- TODO(later): needs §C.2.4 for the nuclearity of the Schwartz space and its
-- strong dual in Lemma D.1.3.7(3).
-- TODO(later): needs §C.5.1 (Theorem C.5.1.30(4)) for the vector-valued Schwartz
-- identifications used to define distribution tensor products in Remark D.1.3.8.

end ElementaryTensor

end RiemannMasullo
