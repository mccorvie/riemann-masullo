module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_AnnularProjectionDefect
public import RiemannMasullo.AppC_LCTVS.Sec3a_part2
import Mathlib.Analysis.MeanInequalities

/-! # Complementary compression of a weighted trace defect -/

public noncomputable section

open scoped InnerProductSpace

namespace RiemannMasullo

variable {E F G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]

/-- The correction due to the weighted projection is the negative of the
trace on its complementary compression. The identity holds for an annular
lift and an injective inclusion between the two Hilbert spaces. -/
theorem hilbertTrace_projectionDefect_eq_neg_complement
    (J : E →L[ℂ] F) (hJ : Function.Injective J) (L : F →L[ℂ] E)
    (P : E →L[ℂ] E) (hP : P * P = P) (T : nuclearEndomorphisms F)
    (hTransfer : IsNuclearOperator ((L.comp T.val).comp J)) :
    let R : E →L[ℂ] E := 1 - P
    let D := (J.comp P - J).comp L
    hilbertTrace ⟨D * T.val, mul_mem_nuclearEndomorphisms_left D T⟩ =
      -hilbertTrace (Isolated.nuclearCompress R ⟨_, hTransfer⟩) := by
  intro R D
  have hR : R * R = R := by
    simp only [R, mul_sub, sub_mul, one_mul, mul_one, hP, sub_self, sub_zero]
  let A := (R.comp L).comp T.val
  have hA : IsNuclearOperator A := by
    obtain ⟨c, φ, y, hc, hφ, hy, hsum⟩ :=
      (isNuclearOperator_iff_isBanachNuclear T.val).mp T.property
    let M := R.comp L
    refine (isNuclearOperator_iff_isBanachNuclear A).mpr
      ⟨c, φ, M ∘ y, hc, hφ, (M.continuous.tendsto' 0 0 (map_zero M)).comp hy, fun x ↦ ?_⟩
    change HasSum (fun n ↦ (c n * φ n x) • M (y n)) (M (T.val x))
    simpa only [map_smul] using M.hasSum (hsum x)
  obtain ⟨hAJ, hJA⟩ := isNuclearOperator_factor_comps J hJ A hA
  let S : nuclearEndomorphisms E := ⟨A.comp J, hAJ⟩
  let V : nuclearEndomorphisms F := ⟨J.comp A, hJA⟩
  let C : nuclearEndomorphisms E := ⟨_, hTransfer⟩
  have hSwap : hilbertTrace S = hilbertTrace V := by
    rw [hilbertTrace_eq_nuclearTrace, hilbertTrace_eq_nuclearTrace]
    exact nuclearTrace_factor_comps hilbert_approximationProperty hilbert_approximationProperty
      J hJ A hA
  have hS : (⟨R * C.val, mul_mem_nuclearEndomorphisms_left R C⟩ :
      nuclearEndomorphisms E) = S := rfl
  have hD : (⟨D * T.val, mul_mem_nuclearEndomorphisms_left D T⟩ :
      nuclearEndomorphisms F) = -V := by
    apply Subtype.ext
    ext x
    change J (P (L (T.val x))) - J (L (T.val x)) =
      -J (L (T.val x) - P (L (T.val x)))
    rw [map_sub, neg_sub]
  rw [hD, hilbertTrace_nuclearCompress_eq_left_of_idempotent R hR C, hS, hSwap]
  obtain ⟨tr, htr⟩ := hilbertTrace_linear (H := F)
  rw [← htr, map_neg, htr]

private theorem norm_hilbertTrace_comp_le_basis {ι : Type*}
    (b : HilbertBasis ι ℂ E) (U : G →L[ℂ] E) (V : E →L[ℂ] G)
    (hU : U.adjoint ∈ hilbertSchmidtOperators E G) (hV : V ∈ hilbertSchmidtOperators E G)
    (hT : IsNuclearOperator (U.comp V)) :
    ‖hilbertTrace ⟨U.comp V, hT⟩‖ ≤
      Real.sqrt (∑' i, ‖U.adjoint (b i)‖ ^ 2) * Real.sqrt (∑' i, ‖V (b i)‖ ^ 2) := by
  have hu := (mem_hilbertSchmidtOperators_iff_summable_basis b U.adjoint).mp hU
  have hv := (mem_hilbertSchmidtOperators_iff_summable_basis b V).mp hV
  have hpair := Real.summable_and_inner_le_Lp_mul_Lq_tsum_of_nonneg
    Real.HolderConjugate.two_two
    (fun i : ι ↦ norm_nonneg (U.adjoint (b i))) (fun i : ι ↦ norm_nonneg (V (b i)))
    (by simpa only [Real.rpow_two] using hu) (by simpa only [Real.rpow_two] using hv)
  let T : nuclearEndomorphisms E := ⟨U.comp V, hT⟩
  have hdiag := summable_norm_hilbertDiagonal b T.val T.property
  have htrace : hilbertTrace T = ∑' i, ⟪b i, T.val (b i)⟫_ℂ :=
    tsum_hilbertDiagonal_eq _ b T.val T.property
  refine (congrArg norm htrace).le.trans ((norm_tsum_le_tsum_norm hdiag).trans ?_)
  refine (hdiag.tsum_le_tsum ?_ hpair.1).trans ?_
  · intro i
    change ‖⟪b i, U (V (b i))⟫_ℂ‖ ≤ ‖U.adjoint (b i)‖ * ‖V (b i)‖
    rw [← U.adjoint_inner_left]
    exact norm_inner_le_norm _ _
  · simpa only [Real.sqrt_eq_rpow, Real.rpow_two] using hpair.2

/-- A right-supported annular operator has a trace-defect bound in terms of
both complementary factors. The right-band projection may be applied
before measuring the right factor. This estimate works with the weighted
orthogonal projection even when the weighted and order-zero projections
fail to intertwine. -/
theorem norm_hilbertTrace_projectionDefect_le_complement_factors {ι : Type*}
    (b : HilbertBasis ι ℂ E) (J : E →L[ℂ] F) (hJ : Function.Injective J) (L : F →L[ℂ] E)
    (P : E →L[ℂ] E) (hP : P * P = P) (Q : F →L[ℂ] F)
    (T : nuclearEndomorphisms F) (hRight : T.val * Q = T.val)
    (X : G →L[ℂ] F) (Y : F →L[ℂ] G) (hFactor : T.val = X.comp Y)
    (hTransfer : IsNuclearOperator ((L.comp T.val).comp J)) :
    let R : E →L[ℂ] E := 1 - P
    let U := R.comp (L.comp X)
    let V := (Y.comp Q).comp (J.comp R)
    let D := (J.comp P - J).comp L
    U.adjoint ∈ hilbertSchmidtOperators E G → V ∈ hilbertSchmidtOperators E G →
    ‖hilbertTrace ⟨D * T.val, mul_mem_nuclearEndomorphisms_left D T⟩‖ ≤
      Real.sqrt (∑' i, ‖U.adjoint (b i)‖ ^ 2) * Real.sqrt (∑' i, ‖V (b i)‖ ^ 2) := by
  intro R U V D hU hV
  let C : nuclearEndomorphisms E := Isolated.nuclearCompress R ⟨_, hTransfer⟩
  have heq : C.val = U.comp V := by
    ext x
    change R (L (T.val (J (R x)))) = R (L (X (Y (Q (J (R x))))))
    have h := DFunLike.congr_fun hRight (J (R x))
    change T.val (Q (J (R x))) = T.val (J (R x)) at h
    rw [← h, hFactor, ContinuousLinearMap.comp_apply]
  have hC : IsNuclearOperator (U.comp V) := heq ▸ C.property
  have hC' : C = ⟨_, hC⟩ := Subtype.ext heq
  have hTrace := hilbertTrace_projectionDefect_eq_neg_complement J hJ L P hP T hTransfer
  change hilbertTrace ⟨D * T.val, _⟩ = -hilbertTrace C at hTrace
  rw [hTrace, norm_neg, hC']
  exact norm_hilbertTrace_comp_le_basis b U V hU hV hC

/-- In a flat pairing with the weighted projection residual, any vector in
the weighted band can be subtracted from the adjoint of the flat row. -/
theorem inner_transport_starProjection_sub_eq
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (J : E →L[ℂ] F) (f q : E) (hq : q ∈ K) (g : F) :
    ⟪g, J (K.starProjection f - f)⟫_ℂ =
      ⟪J.adjoint g - q, K.starProjection f - f⟫_ℂ := by
  have horth := Submodule.inner_right_of_mem_orthogonal hq
    (K.sub_starProjection_mem_orthogonal f)
  rw [← J.adjoint_inner_left, inner_sub_left, ← neg_sub f (K.starProjection f),
    inner_neg_right q, horth, neg_zero, sub_zero]

/-- Bounds the flat pairing with the weighted projection residual by two
weighted approximation errors. Near the moving band edge, `q` can be a
scalar multiple of the same row in the weighted band. Away from this edge,
`p` can be an approximation to the cutoff column in the weighted band. -/
theorem norm_inner_transport_starProjection_sub_le
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (J : E →L[ℂ] F) (f p q : E) (hp : p ∈ K) (hq : q ∈ K) (g : F) :
    ‖⟪g, J (K.starProjection f - f)⟫_ℂ‖ ≤ ‖J.adjoint g - q‖ * ‖f - p‖ := by
  have hdist : ‖K.starProjection f - f‖ ≤ ‖f - p‖ := by
    rw [norm_sub_rev, Submodule.starProjection_minimal]
    have hbounded : BddBelow (Set.range fun v : K ↦ ‖f - (v : E)‖) := by
      refine ⟨0, ?_⟩
      rintro _ ⟨v, rfl⟩
      exact norm_nonneg _
    exact ciInf_le hbounded ⟨p, hp⟩
  rw [inner_transport_starProjection_sub_eq K J f q hq g]
  exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))

/-- To compare a weighted projection with its order-zero counterpart, move
the order-zero projection to the row if the range of the weighted
projection maps into the order-zero range. -/
theorem inner_transport_starProjection_compare_eq
    (K : Submodule ℂ E) [K.HasOrthogonalProjection]
    (K₀ : Submodule ℂ F) [K₀.HasOrthogonalProjection]
    (J : E →L[ℂ] F) (hBand : K.map J.toLinearMap ≤ K₀) (f : E) (g : F) :
    ⟪g, J (K.starProjection f) - K₀.starProjection (J f)⟫_ℂ =
      ⟪K₀.starProjection g, J (K.starProjection f - f)⟫_ℂ := by
  have hmem : J (K.starProjection f) ∈ K₀ :=
    hBand ⟨K.starProjection f, K.starProjection_apply_mem f, rfl⟩
  have heq : J (K.starProjection f) - K₀.starProjection (J f) =
      K₀.starProjection (J (K.starProjection f - f)) := by
    rw [map_sub, map_sub, K₀.starProjection_eq_self_iff.mpr hmem]
  rw [heq, ← K₀.starProjection.adjoint_inner_left]
  exact congrArg (fun A : F →L[ℂ] F ↦ ⟪A g, J (K.starProjection f - f)⟫_ℂ)
    (ContinuousLinearMap.isSelfAdjoint_iff'.mp (isSelfAdjoint_starProjection K₀))

end RiemannMasullo
