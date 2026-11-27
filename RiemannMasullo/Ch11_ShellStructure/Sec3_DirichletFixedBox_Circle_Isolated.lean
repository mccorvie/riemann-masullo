module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Division_Isolated
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Nontrivial primitive Dirichlet characters in fixed Fourier boxes (Circle)

Fixed-box stage spaces, quotient semigroups, and modulated circle action for primitive `χ`.

Nothing outside the `Sec3_DirichletFixedBox*` / `Sec3_RatBridge*` isolated stack imports this module.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField RiemannMasullo Set Topology
open scoped BigOperators ContDiff FourierTransform NNReal Real SchwartzMap

namespace RiemannMasullo.Isolated

/-! ### Section 4: Modulated circle action, unconditional basis, trace expansion, and lower bound -/

section CircleActionAndTraceNorm

open MeasureTheory Filter Topology Real
open scoped InnerProductSpace Convolution ENNReal

/-- Generating set of `dirichletStagePreSpace χ T X α s` inside `CompactIntervalSobolev`:
depleted twisted half-log profiles of fixed-box tests supported on `[-R, R]` (`R = X / ∏ q ∈ T, q`). -/
def dirichletStageSet {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (X α s : ℝ) (_hα : 0 ≤ α) (_hs : 0 ≤ s) :
    Set (CompactIntervalSobolev volume id (-α) α s) :=
  { v | ∃ f₀ : 𝓢(ℝ, ℂ), IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀ ∧
      ∃ hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
          (intervalSobolevMeasure volume id (-α) α s false),
        v = toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem }

theorem toDirichletStrip_congr_ae {α s : ℝ} {U V : ℝ → ℂ}
    (hU : MemLp U 2 (intervalSobolevMeasure volume id (-α) α s false))
    (hV : MemLp V 2 (intervalSobolevMeasure volume id (-α) α s false))
    (h_eq : U =ᵐ[volume] V) :
    toDirichletStrip α s U hU = toDirichletStrip α s V hV := by
  refine Lp.ext ?_
  have hμ := withDensity_absolutelyContinuous volume
    (fun x : ℝ ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s x))
  filter_upwards [hU.coeFn_toLp, hμ h_eq, hV.coeFn_toLp] with x h1 h2 h3
  exact h1.trans (h2.trans h3.symm)

theorem toDirichletStrip_sub_smul_congr_ae {α s : ℝ} {c₁ c₂ : ℂ} {U₁ U₂ W : ℝ → ℂ}
    (hU₁ : MemLp U₁ 2 (intervalSobolevMeasure volume id (-α) α s false))
    (hU₂ : MemLp U₂ 2 (intervalSobolevMeasure volume id (-α) α s false))
    (hW : MemLp W 2 (intervalSobolevMeasure volume id (-α) α s false))
    (h_eq : ∀ x : ℝ, c₁ * U₁ x - c₂ * U₂ x = W x) :
    c₁ • toDirichletStrip α s U₁ hU₁ - c₂ • toDirichletStrip α s U₂ hU₂ =
      toDirichletStrip α s W hW := by
  refine Lp.ext ?_
  let μ₀ := intervalSobolevMeasure volume id (-α) α s false
  filter_upwards [Lp.coeFn_sub (c₁ • toDirichletStrip α s U₁ hU₁) (c₂ • toDirichletStrip α s U₂ hU₂),
    Lp.coeFn_smul c₁ (toDirichletStrip α s U₁ hU₁),
    Lp.coeFn_smul c₂ (toDirichletStrip α s U₂ hU₂),
    hU₁.coeFn_toLp, hU₂.coeFn_toLp, hW.coeFn_toLp] with x hsub hs1 hs2 h1 h2 h3
  rw [hsub, Pi.sub_apply, hs1, hs2, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  calc c₁ * (toDirichletStrip α s U₁ hU₁ : ℝ → ℂ) x -
        c₂ * (toDirichletStrip α s U₂ hU₂ : ℝ → ℂ) x
      = c₁ * U₁ x - c₂ * U₂ x := by rw [show (toDirichletStrip α s U₁ hU₁ : ℝ → ℂ) x = U₁ x from h1,
          show (toDirichletStrip α s U₂ hU₂ : ℝ → ℂ) x = U₂ x from h2]
    _ = W x := h_eq x
    _ = _ := h3.symm

theorem twistedHalfLogProfile_testDepleteStep {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {q : ℕ} (hq : 0 < q) (f : 𝓢(ℝ, ℂ)) :
    twistedHalfLogProfile χ (testDepleteStep χ q f) =
      depleteStepFun χ q (twistedHalfLogProfile χ f) := by
  simp only [testDepleteStep, hq.ne', ↓reduceDIte, sub_apply,
    ContinuousLinearMap.id_apply, smul_apply,
    depleteStepFun, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply]
  rw [twistedHalfLogProfile_sub, twistedHalfLogProfile_smul,
    twistedHalfLogProfile_schwartzScale χ hq]

/-- Pre-Hilbert span of depleted fixed-box vectors at stage `T`. -/
noncomputable def dirichletStagePreSpace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    Submodule ℂ (CompactIntervalSobolev volume id (-α) α s) :=
  Submodule.span ℂ (dirichletStageSet χ T X α s hα hs)

/-- Closed fixed-box Hilbert subspace at stage `T`. -/
noncomputable def dirichletStageSpace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    Submodule ℂ (CompactIntervalSobolev volume id (-α) α s) :=
  (dirichletStagePreSpace χ T X α s hα hs).topologicalClosure

theorem isClosed_dirichletStageSpace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    IsClosed (dirichletStageSpace χ T X α s hα hs : Set (CompactIntervalSobolev volume id (-α) α s)) :=
  Submodule.isClosed_topologicalClosure _

instance instCompleteSpaceDirichletStageSpace {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    CompleteSpace (dirichletStageSpace χ T X α s hα hs) :=
  (isClosed_dirichletStageSpace χ T X α s hα hs).completeSpace_coe

theorem mem_dirichletStageSpace_of_test {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (T : Finset ℕ) {X α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀)
    (hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
      (intervalSobolevMeasure volume id (-α) α s false)) :
    toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem ∈
      dirichletStageSpace χ T X α s hα hs :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f₀, hf₀, hmem, rfl⟩)

theorem clm_zero_on_dirichletStageSpace {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : Finset ℕ) (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (Φ : dirichletStageSpace χ T X α s hα hs →L[ℂ] F)
    (hgen : ∀ f₀ : 𝓢(ℝ, ℂ), ∀ _hf₀ : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) f₀,
      ∀ hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
          (intervalSobolevMeasure volume id (-α) α s false),
        Φ ⟨toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem,
          mem_dirichletStageSpace_of_test T hα hs _hf₀ hmem⟩ = 0)
    (x : dirichletStageSpace χ T X α s hα hs) : Φ x = 0 := by
  let E := dirichletStageSpace χ T X α s hα hs
  have hpre : dirichletStagePreSpace χ T X α s hα hs ≤ Submodule.map E.subtype Φ.ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f₀, hf₀, hmem, rfl⟩
    exact ⟨⟨toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem,
      mem_dirichletStageSpace_of_test T hα hs hf₀ hmem⟩, hgen f₀ hf₀ hmem, rfl⟩
  have hmem_cl : x.1 ∈ closure (dirichletStagePreSpace χ T X α s hα hs : Set _) := by
    rw [← Submodule.topologicalClosure_coe]; exact x.2
  rw [Metric.mem_closure_iff] at hmem_cl
  refine norm_le_zero_iff.mp (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  rw [zero_add]
  by_cases hΦ : ‖Φ‖ = 0
  · have hΦ0 : Φ = 0 := norm_eq_zero.mp hΦ
    rw [hΦ0]
    simp [hε.le]
  · obtain ⟨y, hy, hxy⟩ :=
      hmem_cl (ε / ‖Φ‖) (div_pos hε (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hΦ)))
    obtain ⟨yE, hyE_ker, rfl⟩ := hpre hy
    have hy0 : Φ yE = 0 := hyE_ker
    have hsub : Φ x = Φ (x - yE) := by rw [map_sub, hy0, sub_zero]
    rw [hsub]
    calc ‖Φ (x - yE)‖ ≤ ‖Φ‖ * ‖x - yE‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖Φ‖ * (ε / ‖Φ‖) :=
          mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm, Submodule.coe_sub] using hxy.le)
            (norm_nonneg _)
      _ = ε := mul_div_cancel₀ ε hΦ

theorem dirichletDeplete_commute_step {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (q : ℕ) (T : Finset ℕ) (U : ℝ → ℂ) :
    depleteStepFun χ q (dirichletDeplete χ T U) =
      dirichletDeplete χ T (depleteStepFun χ q U) := by
  induction T using Finset.induction_on with
  | empty =>
    rw [dirichletDeplete_empty, LinearMap.id_apply, LinearMap.id_apply]
  | insert r S hrS ih =>
    rw [dirichletDeplete_insert χ hrS, LinearMap.comp_apply, LinearMap.comp_apply, ← ih]
    exact congrFun (congrArg DFunLike.coe (depleteStepFun_comm χ q r)) (dirichletDeplete χ S U)

theorem dirichletStageSpace_insert_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    dirichletStageSpace χ (insert p T) X α s hα hs ≤
      dirichletStageSpace χ T X α s hα hs := by
  refine (dirichletStagePreSpace χ (insert p T) X α s hα hs).topologicalClosure_minimal ?_
    (isClosed_dirichletStageSpace χ T X α s hα hs)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨g₀, hg₀, hmem, rfl⟩
  have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
  have hprod_pos : 0 < ∏ q ∈ T, (q : ℝ) :=
    Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hT q hq).1.pos
  have hR_pos : 0 < X / ∏ q ∈ T, (q : ℝ) := div_pos hX hprod_pos
  have hg₀' : IsDirichletFixedBoxTest χ ((X / ∏ q ∈ T, (q : ℝ)) / p) g₀ := by
    rwa [div_div, mul_comm (∏ q ∈ T, (q : ℝ)) (p : ℝ), ← Finset.prod_insert hpT]
  have hf_box : IsDirichletFixedBoxTest χ (X / ∏ q ∈ T, (q : ℝ)) (testDepleteStep χ p g₀) := by
    have h1 := isDirichletFixedBoxTest_testDepleteStep hp.pos (div_pos hR_pos hp_pos).le hg₀'
    have hmul : (p : ℝ) * ((X / ∏ q ∈ T, (q : ℝ)) / p) = X / ∏ q ∈ T, (q : ℝ) :=
      mul_div_cancel₀ _ hp_pos.ne'
    rwa [hmul] at h1
  have hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
  have hmem' : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ (testDepleteStep χ p g₀))) 2
      (intervalSobolevMeasure volume id (-α) α s false) :=
    dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs hf_box
  have heq : toDirichletStrip α s (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) hmem =
      toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ (testDepleteStep χ p g₀)))
        hmem' := by
    apply toDirichletStrip_congr_ae
    refine Filter.Eventually.of_forall fun x ↦ ?_
    rw [dirichletDeplete_insert χ hpT, LinearMap.comp_apply, twistedHalfLogProfile_testDepleteStep χ hp.pos]
    have hcomm := dirichletDeplete_commute_step χ p T (twistedHalfLogProfile χ g₀)
    exact congrFun hcomm x
  rw [heq]
  exact mem_dirichletStageSpace_of_test T hα hs hf_box hmem'

/-- Hilbert quotient `E / N_sub` realized as the orthogonal complement subspace `E ⊓ N_subᗮ`.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
noncomputable def dirichletStageQuotient {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (p : ℕ) (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    Submodule ℂ (CompactIntervalSobolev volume id (-α) α s) :=
  dirichletStageSpace χ T X α s hα hs ⊓
    (dirichletStageSpace χ (insert p T) X α s hα hs : Submodule ℂ _)ᗮ

theorem isClosed_dirichletStageQuotient {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (p : ℕ) (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    IsClosed (dirichletStageQuotient χ T p X α s hα hs :
      Set (CompactIntervalSobolev volume id (-α) α s)) :=
  (isClosed_dirichletStageSpace χ T X α s hα hs).inter
    (dirichletStageSpace χ (insert p T) X α s hα hs).isClosed_orthogonal

instance instCompleteSpaceDirichletStageQuotient {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (p : ℕ) (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    CompleteSpace (dirichletStageQuotient χ T p X α s hα hs) :=
  (isClosed_dirichletStageQuotient χ T p X α s hα hs).completeSpace_coe

/-- Orthogonal quotient projection from `E := dirichletStageSpace χ T X α s` onto
`Q := dirichletStageQuotient χ T p X α s`. -/
noncomputable def dirichletStageQuotMap {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    dirichletStageSpace χ T X α s hα hs →L[ℂ] dirichletStageQuotient χ T p X α s hα hs :=
  let E := dirichletStageSpace χ T X α s hα hs
  let N_sub : Submodule ℂ _ := dirichletStageSpace χ (insert p T) X α s hα hs
  have hle : N_sub ≤ E := dirichletStageSpace_insert_le hχ hN T hT hp hpT hX hα hs
  have hmem : ∀ x : E, N_subᗮ.starProjection x.1 ∈ dirichletStageQuotient χ T p X α s hα hs := by
    intro x
    refine ⟨?_, N_subᗮ.starProjection_apply_mem x.1⟩
    have hsplit : x.1 = N_sub.starProjection x.1 + N_subᗮ.starProjection x.1 :=
      (N_sub.starProjection_add_starProjection_orthogonal x.1).symm
    have hNmem : N_sub.starProjection x.1 ∈ E := hle (N_sub.starProjection_apply_mem x.1)
    have heq : N_subᗮ.starProjection x.1 = x.1 - N_sub.starProjection x.1 :=
      eq_sub_of_add_eq' hsplit.symm
    rw [heq]
    exact E.sub_mem x.2 hNmem
  (N_subᗮ.starProjection.comp E.subtypeL).codRestrict _ hmem

@[simp]
theorem coe_dirichletStageQuotMap {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (x : dirichletStageSpace χ T X α s hα hs) :
    (dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs x :
      CompactIntervalSobolev volume id (-α) α s) =
      (dirichletStageSpace χ (insert p T) X α s hα hs : Submodule ℂ _)ᗮ.starProjection x.1 := rfl

theorem dirichletStageQuotMap_sub_mem {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (x : dirichletStageSpace χ T X α s hα hs) :
    x.1 - (dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs x :
      CompactIntervalSobolev volume id (-α) α s) ∈
      dirichletStageSpace χ (insert p T) X α s hα hs := by
  let N_sub : Submodule ℂ _ := dirichletStageSpace χ (insert p T) X α s hα hs
  have hsplit : x.1 = N_sub.starProjection x.1 + N_subᗮ.starProjection x.1 :=
    (N_sub.starProjection_add_starProjection_orthogonal x.1).symm
  have hsub : x.1 - N_subᗮ.starProjection x.1 = N_sub.starProjection x.1 :=
    sub_eq_of_eq_add hsplit
  rw [coe_dirichletStageQuotMap, hsub]
  exact N_sub.starProjection_apply_mem x.1

theorem dirichletStageQuotMap_eq_zero_iff {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (x : dirichletStageSpace χ T X α s hα hs) :
    dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs x = 0 ↔
      x.1 ∈ dirichletStageSpace χ (insert p T) X α s hα hs := by
  let N_sub : Submodule ℂ _ := dirichletStageSpace χ (insert p T) X α s hα hs
  rw [Subtype.ext_iff, coe_dirichletStageQuotMap, Submodule.coe_zero]
  constructor
  · intro h0
    have hmem := dirichletStageQuotMap_sub_mem hχ hN T hT hp hpT hX hα hs x
    rw [coe_dirichletStageQuotMap] at hmem
    simpa [h0] using hmem
  · intro hx
    have h1 : N_sub.starProjection x.1 = x.1 := N_sub.starProjection_eq_self_iff.mpr hx
    have hsplit : x.1 = N_sub.starProjection x.1 + N_subᗮ.starProjection x.1 :=
      (N_sub.starProjection_add_starProjection_orthogonal x.1).symm
    rw [h1] at hsplit
    dsimp only [N_sub] at hsplit
    exact left_eq_add.mp hsplit

theorem dirichletStageQuotMap_self {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs ⟨q.1, q.2.1⟩ = q := by
  refine Subtype.ext ?_
  rw [coe_dirichletStageQuotMap]
  exact ((dirichletStageSpace χ (insert p T) X α s hα hs : Submodule ℂ _)ᗮ.starProjection_eq_self_iff).mpr
    q.2.2

theorem norm_dirichletStageQuotMap_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    ‖dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  rw [one_mul]
  change ‖((dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs x :
      CompactIntervalSobolev volume id (-α) α s))‖ ≤ ‖x.1‖
  rw [coe_dirichletStageQuotMap]
  exact (dirichletStageSpace χ (insert p T) X α s hα hs :
    Submodule ℂ _)ᗮ.norm_starProjection_apply_le x.1

/-- Normalized spectral coordinate row `dirichletNormalizedRow χ T p X α s hα hs j` restricted
to the Hilbert quotient `dirichletStageQuotient χ T p X α s hα hs`. -/
noncomputable def dirichletQuotRow {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : Finset ℕ) (p : ℕ) (X α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s) (j : ℤ) :
    StrongDual ℂ (dirichletStageQuotient χ T p X α s hα hs) :=
  (dirichletNormalizedRow χ T p X α s hα hs j).comp
    (dirichletStageQuotient χ T p X α s hα hs).subtypeL

theorem dirichletNormalizedRow_eq_zero_of_mem_insert {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (j : ℤ)
    {v : CompactIntervalSobolev volume id (-α) α s}
    (hv : v ∈ dirichletStageSpace χ (insert p T) X α s hα hs) :
    dirichletNormalizedRow χ T p X α s hα hs j v = 0 := by
  let row := dirichletNormalizedRow χ T p X α s hα hs j
  let K : Submodule ℂ (CompactIntervalSobolev volume id (-α) α s) := row.ker
  have hK_closed : IsClosed (K : Set (CompactIntervalSobolev volume id (-α) α s)) :=
    row.isClosed_ker
  have hle : dirichletStageSpace χ (insert p T) X α s hα hs ≤ K := by
    refine (dirichletStagePreSpace χ (insert p T) X α s hα hs).topologicalClosure_minimal ?_
      hK_closed
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨g₀, hg₀, hmem, rfl⟩
    change row (toDirichletStrip α s (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ g₀)) hmem) = 0
    have hg₀' : IsDirichletFixedBoxTest χ (X / ((p : ℝ) * ∏ q ∈ T, (q : ℝ))) g₀ := by
      rwa [← Finset.prod_insert hpT]
    simpa [row] using
      dirichletNormalizedRow_apply_next_stage_zero hχ hN T hT hp hpN hpT hX hα hs hg₀' j
  exact hle hv

theorem dirichletQuotRow_quotMap {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (j : ℤ)
    (x : dirichletStageSpace χ T X α s hα hs) :
    dirichletQuotRow χ T p X α s hα hs j (dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs x) =
      dirichletNormalizedRow χ T p X α s hα hs j x.1 := by
  have hdiff := dirichletNormalizedRow_eq_zero_of_mem_insert hχ hN T hT hp hpN hpT hX hα hs j
    (dirichletStageQuotMap_sub_mem hχ hN T hT hp hpT hX hα hs x)
  rw [map_sub, sub_eq_zero] at hdiff
  exact hdiff.symm

private theorem isFiniteMeasureOnCompacts_intervalSobolev (α s : ℝ) :
    IsFiniteMeasureOnCompacts (intervalSobolevMeasure volume id (-α) α s false) := by
  refine ⟨fun K hK ↦ ?_⟩
  let ρ := intervalSobolevDensity (-α) α s
  have hρc := stripDensity_continuous (-α) α s
  let M : ℝ := max 0 (sSup (ρ '' K))
  have hbdd : BddAbove (ρ '' K) := (hK.image hρc).bddAbove
  have hM_le : ∀ x ∈ K, ρ x ≤ M := fun x hx ↦
    (le_csSup hbdd ⟨x, hx, rfl⟩).trans (le_max_right _ _)
  have hvol_lt : volume K < ⊤ := hK.measure_lt_top
  change volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) K < ⊤
  rw [withDensity_apply _ hK.measurableSet]
  calc ∫⁻ x in K, ENNReal.ofReal (ρ x) ∂volume
      ≤ ∫⁻ _ in K, ENNReal.ofReal M ∂volume :=
        setLIntegral_mono (Measurable.ennreal_ofReal (measurable_const)) fun x hx ↦
          ENNReal.ofReal_le_ofReal (hM_le x hx)
    _ = ENNReal.ofReal M * volume K := by rw [setLIntegral_const]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hvol_lt

theorem continuous_backHalfShiftCLM (α s : ℝ) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (v : CompactIntervalSobolev volume id (-α) α s) :
    Continuous (fun a : ℝ ↦ backHalfShiftCLM α s hα hs a v) := by
  have : IsFiniteMeasureOnCompacts (intervalSobolevMeasure volume id (-α) α s false) :=
    isFiniteMeasureOnCompacts_intervalSobolev α s
  let μ₀ := intervalSobolevMeasure volume id (-α) α s false
  let ρ := intervalSobolevDensity (-α) α s
  have hρc := stripDensity_continuous (-α) α s
  have hρp := stripDensity_pos (-α) α s
  have hsmooth_cont : ∀ g : ℝ → ℂ, HasCompactSupport g → Continuous g →
      ∀ (hg_mem : MemLp g 2 μ₀),
        Continuous (fun a : ℝ ↦ backHalfShiftCLM α s hα hs a (hg_mem.toLp g)) := by
    intro g hg_supp hg_cont hg_mem
    rw [continuous_iff_continuousAt]
    intro a₀
    let K := tsupport g
    have hK_cpt : IsCompact K := hg_supp
    obtain ⟨Rg₀, hRg₀⟩ := hK_cpt.isBounded.subset_closedBall (0 : ℝ)
    let Rg : ℝ := max Rg₀ 0
    have hK_sub : K ⊆ Set.Icc (-Rg) Rg := fun y hy ↦ by
      have h1 : |y| ≤ Rg₀ := by
        simpa [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hRg₀ hy
      exact abs_le.mp (h1.trans (le_max_left _ _))
    have hg_zero : ∀ y : ℝ, Rg < |y| → g y = 0 := fun y hy ↦ by
      by_contra hne
      have hmem : y ∈ K := subset_tsupport g (Function.mem_support.mpr hne)
      have := abs_le.mpr (hK_sub hmem)
      linarith
    have hg_bdd : BddAbove ((fun x : ℝ ↦ ‖g x‖) '' K) := (hK_cpt.image hg_cont.norm).bddAbove
    let Cg : ℝ := max 1 (sSup ((fun x : ℝ ↦ ‖g x‖) '' K))
    have hCg_pos : 0 < Cg := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hg_le : ∀ y : ℝ, ‖g y‖ ≤ Cg := fun y ↦ by
      by_cases hy : y ∈ K
      · exact (le_csSup hg_bdd ⟨y, hy, rfl⟩).trans (le_max_right _ _)
      · have hz : g y = 0 := by
          by_contra hne
          exact hy (subset_tsupport g (Function.mem_support.mpr hne))
        rw [hz, norm_zero]
        exact hCg_pos.le
    let R_dom : ℝ := Rg + |a₀| + 1
    let C_dom : ℝ := (2 * Real.exp ((a₀ + 1) / 2) * Cg) ^ 2
    let dom : ℝ → ℝ := Set.indicator (Set.Icc (-R_dom) R_dom) (fun x : ℝ ↦ C_dom * ρ x)
    have hdom_int : Integrable dom volume :=
      IntegrableOn.integrable_indicator ((continuous_const.mul hρc).integrableOn_Icc) measurableSet_Icc
    let F : ℝ → ℝ → ℝ := fun a x ↦
      ‖(Real.exp (a / 2) : ℂ) * g (x - a) - (Real.exp (a₀ / 2) : ℂ) * g (x - a₀)‖ ^ 2 * ρ x
    have hF_tend : Tendsto (fun a : ℝ ↦ ∫ x : ℝ, F a x ∂volume) (𝓝 a₀) (𝓝 (∫ x : ℝ, F a₀ x ∂volume)) := by
      refine tendsto_integral_filter_of_dominated_convergence dom ?_ ?_ hdom_int ?_
      · refine Filter.Eventually.of_forall fun a ↦ ?_
        have hc : Continuous (F a) := by
          refine ((Continuous.norm ?_).pow 2).mul hρc
          exact (continuous_const.mul (hg_cont.comp (continuous_id.sub continuous_const))).sub
            (continuous_const.mul (hg_cont.comp (continuous_id.sub continuous_const)))
        exact hc.aestronglyMeasurable
      · filter_upwards [Icc_mem_nhds (by linarith : a₀ - 1 < a₀) (by linarith : a₀ < a₀ + 1)] with
          a ha
        refine Filter.Eventually.of_forall fun x ↦ ?_
        have hF_nn : 0 ≤ F a x := mul_nonneg (sq_nonneg _) (hρp x).le
        rw [Real.norm_of_nonneg hF_nn]
        dsimp only [dom]
        by_cases hx : x ∈ Set.Icc (-R_dom) R_dom
        · rw [Set.indicator_of_mem hx]
          have hsub : ‖(Real.exp (a / 2) : ℂ) * g (x - a) - (Real.exp (a₀ / 2) : ℂ) * g (x - a₀)‖ ≤
              2 * Real.exp ((a₀ + 1) / 2) * Cg := by
            have h1 : ‖(Real.exp (a / 2) : ℂ) * g (x - a)‖ ≤ Real.exp ((a₀ + 1) / 2) * Cg := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
              exact mul_le_mul (Real.exp_le_exp.mpr (by linarith [ha.2])) (hg_le _) (norm_nonneg _)
                (Real.exp_pos _).le
            have h2 : ‖(Real.exp (a₀ / 2) : ℂ) * g (x - a₀)‖ ≤ Real.exp ((a₀ + 1) / 2) * Cg := by
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
              exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) (hg_le _) (norm_nonneg _)
                (Real.exp_pos _).le
            calc ‖(Real.exp (a / 2) : ℂ) * g (x - a) - (Real.exp (a₀ / 2) : ℂ) * g (x - a₀)‖
                ≤ ‖(Real.exp (a / 2) : ℂ) * g (x - a)‖ +
                    ‖(Real.exp (a₀ / 2) : ℂ) * g (x - a₀)‖ := norm_sub_le _ _
              _ ≤ Real.exp ((a₀ + 1) / 2) * Cg + Real.exp ((a₀ + 1) / 2) * Cg := add_le_add h1 h2
              _ = 2 * Real.exp ((a₀ + 1) / 2) * Cg := by ring
          calc F a x = ‖_‖ ^ 2 * ρ x := rfl
            _ ≤ C_dom * ρ x := by
                refine mul_le_mul_of_nonneg_right ?_ (hρp x).le
                exact sq_le_sq' (by linarith [norm_nonneg ((Real.exp (a / 2) : ℂ) * g (x - a) -
                  (Real.exp (a₀ / 2) : ℂ) * g (x - a₀))]) hsub
        · rw [Set.indicator_of_notMem hx]
          have hgt_dom : R_dom < |x| := by
            rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
            rcases hx with hlt | hgt
            · exact lt_of_lt_of_le (by linarith) (neg_le_abs x)
            · exact lt_of_lt_of_le hgt (le_abs_self x)
          have ha_abs : |a| ≤ |a₀| + 1 := by
            have hdif : |a - a₀| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
            have htri := abs_add_le (a - a₀) a₀
            simpa using htri.trans (by linarith [hdif])
          have hxa : Rg < |x - a| := by
            have h1 : |x| ≤ |x - a| + |a| := by simpa using abs_add_le (x - a) a
            dsimp [R_dom] at hgt_dom
            linarith
          have hxa0 : Rg < |x - a₀| := by
            have h1 : |x| ≤ |x - a₀| + |a₀| := by simpa using abs_add_le (x - a₀) a₀
            dsimp [R_dom] at hgt_dom
            linarith
          simp [F, hg_zero _ hxa, hg_zero _ hxa0]
      · refine Filter.Eventually.of_forall fun x ↦ ?_
        have hcont_a : Continuous fun a : ℝ ↦ F a x := by
          refine ((Continuous.norm ?_).pow 2).mul continuous_const
          exact ((Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_id.div_const 2))).mul
            (hg_cont.comp (continuous_const.sub continuous_id))).sub continuous_const
        exact hcont_a.continuousAt.tendsto
    have hF_zero : ∫ x : ℝ, F a₀ x ∂volume = 0 := by simp [F]
    rw [hF_zero] at hF_tend
    have hdist_sq : ∀ a : ℝ, ‖backHalfShiftCLM α s hα hs a (hg_mem.toLp g) -
        backHalfShiftCLM α s hα hs a₀ (hg_mem.toLp g)‖ ^ 2 = ∫ x : ℝ, F a x ∂volume := by
      intro a
      let diff := backHalfShiftCLM α s hα hs a (hg_mem.toLp g) -
        backHalfShiftCLM α s hα hs a₀ (hg_mem.toLp g)
      have hid : ‖diff‖ ^ 2 = (⟪diff, diff⟫_ℂ).re := (inner_self_eq_norm_sq (𝕜 := ℂ) diff).symm
      rw [hid, L2.inner_def]
      have ha_fn : ∀ b : ℝ, (backHalfShiftCLM α s hα hs b (hg_mem.toLp g) : ℝ → ℂ) =ᵐ[volume]
          fun x ↦ (Real.exp (b / 2) : ℂ) * g (x - b) := by
        intro b
        have hb1 : (backHalfShiftCLM α s hα hs b (hg_mem.toLp g) : ℝ → ℂ) =ᵐ[μ₀]
            fun x ↦ (Real.exp (b / 2) : ℂ) * (hg_mem.toLp g : ℝ → ℂ) (x - b) := by
          simpa [backHalfShiftCLM] using
            (halfShift_memLp_and_eLpNorm hα hs b (Lp.memLp (hg_mem.toLp g))).1.coeFn_toLp
        have hb1' : (backHalfShiftCLM α s hα hs b (hg_mem.toLp g) : ℝ → ℂ) =ᵐ[volume]
            fun x ↦ (Real.exp (b / 2) : ℂ) * (hg_mem.toLp g : ℝ → ℂ) (x - b) := by
          have hcoe := (ae_withDensity_iff hρc.measurable.ennreal_ofReal).mp hb1
          filter_upwards [hcoe] with x hx
          exact hx (ENNReal.ofReal_pos.mpr (hρp x)).ne'
        have hg_vol : (hg_mem.toLp g : ℝ → ℂ) =ᵐ[volume] g := by
          have hcoe := (ae_withDensity_iff hρc.measurable.ennreal_ofReal).mp hg_mem.coeFn_toLp
          filter_upwards [hcoe] with x hx
          exact hx (ENNReal.ofReal_pos.mpr (hρp x)).ne'
        have hg_shift : (fun x ↦ (hg_mem.toLp g : ℝ → ℂ) (x - b)) =ᵐ[volume] fun x ↦ g (x - b) := by
          have hmp : Measure.map (fun x : ℝ ↦ x - b) volume = volume :=
            (measurePreserving_sub_right volume b).map_eq
          have : ∀ᵐ x ∂(Measure.map (fun x : ℝ ↦ x - b) volume), (hg_mem.toLp g : ℝ → ℂ) x = g x := by
            rwa [hmp]
          exact ae_of_ae_map (by fun_prop) this
        filter_upwards [hb1', hg_shift] with x hx1 hx2
        rw [hx1, hx2]
      have hsub_vol : (diff : ℝ → ℂ) =ᵐ[volume]
          fun x ↦ (Real.exp (a / 2) : ℂ) * g (x - a) - (Real.exp (a₀ / 2) : ℂ) * g (x - a₀) := by
        have hcoe := (ae_withDensity_iff hρc.measurable.ennreal_ofReal).mp
          (Lp.coeFn_sub (backHalfShiftCLM α s hα hs a (hg_mem.toLp g))
            (backHalfShiftCLM α s hα hs a₀ (hg_mem.toLp g)))
        have hsub' : (diff : ℝ → ℂ) =ᵐ[volume]
            fun x ↦ (backHalfShiftCLM α s hα hs a (hg_mem.toLp g) : ℝ → ℂ) x -
              (backHalfShiftCLM α s hα hs a₀ (hg_mem.toLp g) : ℝ → ℂ) x := by
          filter_upwards [hcoe] with x hx
          exact hx (ENNReal.ofReal_pos.mpr (hρp x)).ne'
        filter_upwards [hsub', ha_fn a, ha_fn a₀] with x hx h1 h0
        rw [hx, h1, h0]
      change (∫ x : ℝ, (diff : ℝ → ℂ) x * starRingEnd ℂ ((diff : ℝ → ℂ) x) ∂
          (volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x)))).re = ∫ x : ℝ, F a x ∂volume
      rw [integral_withDensity_eq_integral_toReal_smul₀
        hρc.measurable.ennreal_ofReal.aemeasurable
        (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
      change (Complex.reCLM (∫ x : ℝ, (ENNReal.ofReal (ρ x)).toReal •
          ((diff : ℝ → ℂ) x * starRingEnd ℂ ((diff : ℝ → ℂ) x)))) = _
      have hmem_w : MemLp (diff : ℝ → ℂ) 2 μ₀ := Lp.memLp diff
      have hsq_int : Integrable (fun x : ℝ ↦ ((‖(diff : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ)) μ₀ :=
        Complex.ofRealCLM.integrable_comp
          ((memLp_two_iff_integrable_sq_norm hmem_w.aestronglyMeasurable).mp hmem_w)
      have hint_int : Integrable (fun x : ℝ ↦ (diff : ℝ → ℂ) x * starRingEnd ℂ ((diff : ℝ → ℂ) x)) μ₀ := by
        refine hsq_int.congr (Filter.Eventually.of_forall fun x ↦ ?_)
        dsimp only
        rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      have hint_w : Integrable (fun x : ℝ ↦ (ENNReal.ofReal (ρ x)).toReal •
          ((diff : ℝ → ℂ) x * starRingEnd ℂ ((diff : ℝ → ℂ) x))) volume :=
        (integrable_withDensity_iff_integrable_smul' hρc.measurable.ennreal_ofReal
          (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hint_int
      rw [← Complex.reCLM.integral_comp_comm hint_w]
      refine integral_congr_ae ?_
      filter_upwards [hsub_vol] with x hx
      have hmul : (diff : ℝ → ℂ) x * starRingEnd ℂ ((diff : ℝ → ℂ) x) =
          ((‖(Real.exp (a / 2) : ℂ) * g (x - a) -
            (Real.exp (a₀ / 2) : ℂ) * g (x - a₀)‖ ^ 2 : ℝ) : ℂ) := by
        rw [hx, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
      rw [Complex.reCLM_apply, Complex.real_smul, ENNReal.toReal_ofReal (hρp x).le,
        hmul, Complex.mul_re]
      simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      dsimp [F]
      ring
    have hnorm_tend : Tendsto (fun a : ℝ ↦ ‖backHalfShiftCLM α s hα hs a (hg_mem.toLp g) -
        backHalfShiftCLM α s hα hs a₀ (hg_mem.toLp g)‖) (𝓝 a₀) (𝓝 0) := by
      have hsq_tend : Tendsto (fun a : ℝ ↦ ‖backHalfShiftCLM α s hα hs a (hg_mem.toLp g) -
          backHalfShiftCLM α s hα hs a₀ (hg_mem.toLp g)‖ ^ 2) (𝓝 a₀) (𝓝 0) := by
        simpa [hdist_sq] using hF_tend
      have hsqrt := (Real.continuous_sqrt.continuousAt.tendsto.comp hsq_tend)
      simpa using hsqrt.congr (fun a ↦ Real.sqrt_sq (norm_nonneg _))
    exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm_tend
  rw [continuous_iff_continuousAt]
  intro a₀
  change Tendsto (fun a : ℝ ↦ backHalfShiftCLM α s hα hs a v) (𝓝 a₀)
    (𝓝 (backHalfShiftCLM α s hα hs a₀ v))
  rw [Metric.tendsto_nhds]
  intro ε hε
  let M₀ : ℝ := Real.exp ((a₀ + 1) / 2 + α * (|a₀| + 1)) * (2 + 2 * (|a₀| + 1) ^ 2) ^ (s / 4) + 1
  have hM₀_pos : 0 < M₀ := by positivity
  have hM₀_bd : ∀ a ∈ Set.Icc (a₀ - 1) (a₀ + 1), ‖backHalfShiftCLM α s hα hs a‖ ≤ M₀ := by
    intro a ha
    have hle := norm_backHalfShiftCLM_le α s hα hs a
    have ha_abs : |a| ≤ |a₀| + 1 := by
      have hdif : |a - a₀| ≤ 1 := abs_le.mpr ⟨by linarith [ha.1], by linarith [ha.2]⟩
      have htri := abs_add_le (a - a₀) a₀
      simpa using htri.trans (by linarith [hdif])
    have h1 : Real.exp (a / 2 + α * |a|) ≤ Real.exp ((a₀ + 1) / 2 + α * (|a₀| + 1)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [ha.2, hα]
    have h2 : (2 + 2 * a ^ 2) ^ (s / 4) ≤ (2 + 2 * (|a₀| + 1) ^ 2) ^ (s / 4) := by
      apply Real.rpow_le_rpow (by positivity)
      · have hsq : a ^ 2 ≤ (|a₀| + 1) ^ 2 := by
          rw [← sq_abs a]
          exact pow_le_pow_left₀ (abs_nonneg a) ha_abs 2
        linarith
      · positivity
    have hmul := mul_le_mul h1 h2 (by positivity) (Real.exp_pos _).le
    linarith
  obtain ⟨g, hg_supp, hg_smooth, hg_eLp⟩ :=
    MemLp.exist_eLpNorm_sub_le (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) (Lp.memLp v)
      (by positivity : 0 < ε / (3 * M₀))
  have hg_mem : MemLp g 2 μ₀ := hg_smooth.continuous.memLp_of_hasCompactSupport hg_supp
  let gLp := hg_mem.toLp g
  have hgv : ‖v - gLp‖ ≤ ε / (3 * M₀) := by
    have hsub_ae : ((v - gLp : Lp ℂ 2 μ₀) : ℝ → ℂ) =ᵐ[μ₀] (v : ℝ → ℂ) - g := by
      filter_upwards [Lp.coeFn_sub v gLp, hg_mem.coeFn_toLp] with x hx1 hx2
      calc ((v - gLp : Lp ℂ 2 μ₀) : ℝ → ℂ) x = (v : ℝ → ℂ) x - (gLp : ℝ → ℂ) x := hx1
        _ = ((v : ℝ → ℂ) - g) x := by rw [Pi.sub_apply, hx2]
    change ‖(v - gLp : Lp ℂ 2 μ₀)‖ ≤ ε / (3 * M₀)
    rw [Lp.norm_def, eLpNorm_congr_ae hsub_ae]
    exact ENNReal.toReal_le_of_le_ofReal (by positivity) hg_eLp
  have hcont_g : Tendsto (fun a : ℝ ↦ backHalfShiftCLM α s hα hs a gLp) (𝓝 a₀)
      (𝓝 (backHalfShiftCLM α s hα hs a₀ gLp)) :=
    (hsmooth_cont g hg_supp hg_smooth.continuous hg_mem).continuousAt
  rw [Metric.tendsto_nhds] at hcont_g
  filter_upwards [Icc_mem_nhds (by linarith : a₀ - 1 < a₀) (by linarith : a₀ < a₀ + 1),
    hcont_g (ε / 3) (by positivity)] with a ha_Icc ha_g
  rw [dist_eq_norm] at ha_g ⊢
  have h1 : ‖backHalfShiftCLM α s hα hs a v - backHalfShiftCLM α s hα hs a gLp‖ ≤ M₀ * (ε / (3 * M₀)) := by
    rw [← map_sub]
    calc ‖backHalfShiftCLM α s hα hs a (v - gLp)‖
        ≤ ‖backHalfShiftCLM α s hα hs a‖ * ‖v - gLp‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M₀ * (ε / (3 * M₀)) := mul_le_mul (hM₀_bd a ha_Icc) hgv (norm_nonneg _) hM₀_pos.le
  have h2 : ‖backHalfShiftCLM α s hα hs a gLp - backHalfShiftCLM α s hα hs a₀ gLp‖ < ε / 3 := ha_g
  have h3 : ‖backHalfShiftCLM α s hα hs a₀ gLp - backHalfShiftCLM α s hα hs a₀ v‖ ≤
      M₀ * (ε / (3 * M₀)) := by
    rw [← map_sub]
    calc ‖backHalfShiftCLM α s hα hs a₀ (gLp - v)‖
        ≤ ‖backHalfShiftCLM α s hα hs a₀‖ * ‖gLp - v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M₀ * (ε / (3 * M₀)) := by
          refine mul_le_mul (hM₀_bd a₀ ⟨by linarith, by linarith⟩) ?_ (norm_nonneg _) hM₀_pos.le
          rwa [norm_sub_rev]
  have hM₀_cancel : M₀ * (ε / (3 * M₀)) = ε / 3 := by field_simp [hM₀_pos.ne']
  calc ‖backHalfShiftCLM α s hα hs a v - backHalfShiftCLM α s hα hs a₀ v‖
      = ‖(backHalfShiftCLM α s hα hs a v - backHalfShiftCLM α s hα hs a gLp) +
          (backHalfShiftCLM α s hα hs a gLp - backHalfShiftCLM α s hα hs a₀ gLp) +
          (backHalfShiftCLM α s hα hs a₀ gLp - backHalfShiftCLM α s hα hs a₀ v)‖ := by
          congr 1; abel
    _ ≤ ‖backHalfShiftCLM α s hα hs a v - backHalfShiftCLM α s hα hs a gLp‖ +
          ‖backHalfShiftCLM α s hα hs a gLp - backHalfShiftCLM α s hα hs a₀ gLp‖ +
          ‖backHalfShiftCLM α s hα hs a₀ gLp - backHalfShiftCLM α s hα hs a₀ v‖ := by
        linarith [norm_add_le (backHalfShiftCLM α s hα hs a v - backHalfShiftCLM α s hα hs a gLp)
          (backHalfShiftCLM α s hα hs a gLp - backHalfShiftCLM α s hα hs a₀ gLp),
          norm_add_le ((backHalfShiftCLM α s hα hs a v - backHalfShiftCLM α s hα hs a gLp) +
            (backHalfShiftCLM α s hα hs a gLp - backHalfShiftCLM α s hα hs a₀ gLp))
            (backHalfShiftCLM α s hα hs a₀ gLp - backHalfShiftCLM α s hα hs a₀ v)]
    _ < M₀ * (ε / (3 * M₀)) + ε / 3 + M₀ * (ε / (3 * M₀)) := by linarith
    _ = ε := by rw [hM₀_cancel]; ring

theorem backHalfShiftCLM_apply_depleted_scale {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (_hχ : χ.IsPrimitive) (_hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {R α s : ℝ} (hR : 0 < R) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {f₀ : 𝓢(ℝ, ℂ)} (hf₀ : IsDirichletFixedBoxTest χ R f₀) (a : ℝ) (ha : 0 ≤ a) :
    let fa := schwartzScale (Real.exp (-a)) (Real.exp_pos _).ne' f₀
    IsDirichletFixedBoxTest χ R fa ∧
      ∀ (hmem : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) 2
          (intervalSobolevMeasure volume id (-α) α s false))
        (hmem_a : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ fa)) 2
          (intervalSobolevMeasure volume id (-α) α s false)),
        backHalfShiftCLM α s hα hs a
            (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem) =
          toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ fa)) hmem_a := by
  intro fa
  have hexp_pos : 0 < Real.exp (-a) := Real.exp_pos (-a)
  have hfa_box : IsDirichletFixedBoxTest χ (R * Real.exp (-a)) fa := by
    refine ⟨fun x ↦ ?_, ?_⟩
    · simp only [fa, schwartzScale_apply]
      have : Real.exp (-a) * (-x) = -(Real.exp (-a) * x) := by ring
      rw [this, hf₀.1]
    · have hsupp : tsupport (fun w : ℝ ↦ (𝓕 fa) w) ⊆
          (fun w : ℝ ↦ Real.exp a * w) ⁻¹' tsupport (fun w : ℝ ↦ (𝓕 f₀) w) := by
        refine closure_minimal ?_ ((isClosed_tsupport _).preimage (continuous_const.mul continuous_id))
        intro w hw
        rw [Function.mem_support] at hw
        rw [Set.mem_preimage]
        refine subset_tsupport _ (Function.mem_support.mpr ?_)
        intro h0
        apply hw
        rw [fourier_schwartzScale _ hexp_pos.ne' f₀ w, div_eq_mul_inv, Real.exp_neg,
          abs_of_pos (inv_pos.mpr (Real.exp_pos a)), inv_inv, mul_comm w (Real.exp a), h0, mul_zero]
      intro w hw
      have hmem := hf₀.2 (hsupp hw)
      dsimp only at hmem
      rw [Set.mem_Icc] at hmem ⊢
      have hmul_neg : -(R * Real.exp (-a)) ≤ w := by
        calc -(R * Real.exp (-a)) = (-R) * Real.exp (-a) := by ring
          _ ≤ (Real.exp a * w) * Real.exp (-a) :=
              mul_le_mul_of_nonneg_right hmem.1 (Real.exp_pos (-a)).le
          _ = w := by
              rw [mul_comm (Real.exp a) w, mul_assoc, ← Real.exp_add, add_neg_cancel,
                Real.exp_zero, mul_one]
      have hmul_pos : w ≤ R * Real.exp (-a) := by
        calc w = (Real.exp a * w) * Real.exp (-a) := by
              rw [mul_comm (Real.exp a) w, mul_assoc, ← Real.exp_add, add_neg_cancel,
                Real.exp_zero, mul_one]
          _ ≤ R * Real.exp (-a) := mul_le_mul_of_nonneg_right hmem.2 (Real.exp_pos (-a)).le
      exact ⟨hmul_neg, hmul_pos⟩
  have hle_R : R * Real.exp (-a) ≤ R :=
    mul_le_of_le_one_right hR.le (Real.exp_le_one_iff.mpr (by linarith))
  refine ⟨hfa_box.mono hle_R, fun hmem hmem_a ↦ ?_⟩
  have hmem_shift := (halfShift_memLp_and_eLpNorm hα hs a hmem).1
  rw [backHalfShiftCLM_apply_toDirichletStrip α s hα hs a hmem hmem_shift]
  apply toDirichletStrip_congr_ae
  refine Filter.Eventually.of_forall fun x ↦ ?_
  have htw : twistedHalfLogProfile χ fa =
      fun y : ℝ ↦ (Real.exp (a / 2) : ℂ) * twistedHalfLogProfile χ f₀ (y - a) := by
    ext y
    simp only [twistedHalfLogProfile, twistedRadialTheta, fa, schwartzScale_apply]
    have hexp_split : Real.exp (y / 2) = Real.exp (a / 2) * Real.exp ((y - a) / 2) := by
      rw [← Real.exp_add]
      congr 1; ring
    have hexp_shift : ∀ m : ℤ, Real.exp (-a) * ((m : ℝ) * Real.exp y) = (m : ℝ) * Real.exp (y - a) := by
      intro m
      rw [Real.exp_sub, div_eq_mul_inv, Real.exp_neg]
      ring
    simp_rw [hexp_shift]
    rw [hexp_split, Complex.ofReal_mul, mul_assoc]
  have hdep : ∀ (x : ℝ) (U : ℝ → ℂ),
      dirichletDeplete χ T (fun y : ℝ ↦ (Real.exp (a / 2) : ℂ) * U (y - a)) x =
        (Real.exp (a / 2) : ℂ) * dirichletDeplete χ T U (x - a) := by
    clear htw hfa_box hle_R hmem hmem_a hmem_shift
    induction T using Finset.induction_on with
    | empty =>
      intro x U
      rw [dirichletDeplete_empty, LinearMap.id_apply, LinearMap.id_apply]
    | insert q S hqS ih =>
      intro x U
      have hq0 : 0 < q := hT q (Finset.mem_insert_self q S)
      have hS : ∀ r ∈ S, 0 < r := fun r hr ↦ hT r (Finset.mem_insert_of_mem hr)
      rw [dirichletDeplete_insert χ hqS, LinearMap.comp_apply, LinearMap.comp_apply]
      have hsub1 : dirichletDeplete χ S (fun y : ℝ ↦ (Real.exp (a / 2) : ℂ) * U (y - a)) =
          fun y : ℝ ↦ (Real.exp (a / 2) : ℂ) * dirichletDeplete χ S U (y - a) := by
        ext y
        exact ih hS y U
      rw [hsub1]
      simp only [depleteStepFun, LinearMap.sub_apply, LinearMap.id_apply,
        LinearMap.smul_apply, halfTwistLogDilate, hq0.ne', ↓reduceIte,
        LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      have hadd_sub : x + Real.log q - a = x - a + Real.log q := by ring
      rw [hadd_sub]
      ring
  rw [htw, hdep x]

theorem backHalfShiftCLM_mem_dirichletStageSpace {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, 0 < q)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (a : ℝ) (ha : 0 ≤ a) {v : CompactIntervalSobolev volume id (-α) α s}
    (hv : v ∈ dirichletStageSpace χ T X α s hα hs) :
    backHalfShiftCLM α s hα hs a v ∈ dirichletStageSpace χ T X α s hα hs := by
  let E := dirichletStageSpace χ T X α s hα hs
  let S_map := backHalfShiftCLM α s hα hs a
  let pre : Submodule ℂ _ := E.comap S_map.toLinearMap
  have hpre_closed : IsClosed (pre : Set (CompactIntervalSobolev volume id (-α) α s)) :=
    (isClosed_dirichletStageSpace χ T X α s hα hs).preimage S_map.continuous
  have hle : E ≤ pre := by
    refine (dirichletStagePreSpace χ T X α s hα hs).topologicalClosure_minimal ?_ hpre_closed
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f₀, hf₀, hmem, rfl⟩
    have hR_pos : 0 < X / ∏ q ∈ T, (q : ℝ) :=
      div_pos hX (Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hT q hq))
    have ⟨hfa_box, hshift_eq⟩ := backHalfShiftCLM_apply_depleted_scale hχ hN T hT hR_pos hα hs hf₀ a ha
    have hmem_a : MemLp (dirichletDeplete χ T
        (twistedHalfLogProfile χ (schwartzScale (Real.exp (-a)) (Real.exp_pos _).ne' f₀))) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN T hT hR_pos hα hs hfa_box
    change backHalfShiftCLM α s hα hs a _ ∈ E
    rw [hshift_eq hmem hmem_a]
    exact mem_dirichletStageSpace_of_test T hα hs hfa_box hmem_a
  exact hle hv

/-- Forward translation semigroup `S_real a` (`a ≥ 0`) descended to the Hilbert quotient `Q`. -/
noncomputable def dirichletQuotSemigroup {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (a : ℝ) (ha : 0 ≤ a) :
    dirichletStageQuotient χ T p X α s hα hs →L[ℂ] dirichletStageQuotient χ T p X α s hα hs :=
  let E := dirichletStageSpace χ T X α s hα hs
  let Q := dirichletStageQuotient χ T p X α s hα hs
  let qMap := dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
  let hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
  let S_Q : Q →L[ℂ] E := ((backHalfShiftCLM α s hα hs a).comp Q.subtypeL).codRestrict E
    fun q ↦ backHalfShiftCLM_mem_dirichletStageSpace hχ hN T hTpos hX hα hs a ha q.2.1
  qMap.comp S_Q

theorem dirichletQuotSemigroup_quotMap {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {a : ℝ} (ha : 0 ≤ a) (x : dirichletStageSpace χ T X α s hα hs) :
    dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha
        (dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs x) =
      dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
        ⟨backHalfShiftCLM α s hα hs a x.1,
          backHalfShiftCLM_mem_dirichletStageSpace hχ hN T (fun q hq ↦ (hT q hq).1.pos) hX hα hs a ha x.2⟩ := by
  have hTpos' : ∀ q ∈ insert p T, 0 < q := fun q hq ↦ by
    rcases Finset.mem_insert.mp hq with rfl | hqT
    · exact hp.pos
    · exact (hT q hqT).1.pos
  have hsub := dirichletStageQuotMap_sub_mem hχ hN T hT hp hpT hX hα hs x
  have hmem_ins : backHalfShiftCLM α s hα hs a x.1 -
      backHalfShiftCLM α s hα hs a
        (dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs x :
          CompactIntervalSobolev volume id (-α) α s) ∈
      dirichletStageSpace χ (insert p T) X α s hα hs := by
    rw [← map_sub]
    exact backHalfShiftCLM_mem_dirichletStageSpace hχ hN (insert p T) hTpos' hX hα hs a ha hsub
  have hq0 := (dirichletStageQuotMap_eq_zero_iff hχ hN T hT hp hpT hX hα hs
    (⟨backHalfShiftCLM α s hα hs a x.1,
        backHalfShiftCLM_mem_dirichletStageSpace hχ hN T (fun q hq ↦ (hT q hq).1.pos) hX hα hs a ha x.2⟩ -
      ⟨backHalfShiftCLM α s hα hs a
          (dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs x :
            CompactIntervalSobolev volume id (-α) α s),
        backHalfShiftCLM_mem_dirichletStageSpace hχ hN T (fun q hq ↦ (hT q hq).1.pos) hX hα hs a ha
          (dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs x).2.1⟩)).mpr hmem_ins
  rw [map_sub, sub_eq_zero] at hq0
  exact hq0.symm

theorem dirichletQuotSemigroup_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs 0 le_rfl = ContinuousLinearMap.id ℂ _ := by
  ext1 q
  have hq := dirichletStageQuotMap_self hχ hN T hT hp hpT hX hα hs q
  conv_lhs => rw [← hq, dirichletQuotSemigroup_quotMap]
  simp only [backHalfShiftCLM_zero, ContinuousLinearMap.id_apply]
  exact hq

theorem dirichletQuotSemigroup_add {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (a + b) (add_nonneg ha hb) =
      (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha).comp
        (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs b hb) := by
  ext1 q
  have hq := dirichletStageQuotMap_self hχ hN T hT hp hpT hX hα hs q
  rw [ContinuousLinearMap.comp_apply]
  conv_rhs =>
    rw [← hq, dirichletQuotSemigroup_quotMap, dirichletQuotSemigroup_quotMap]
  conv_lhs => rw [← hq, dirichletQuotSemigroup_quotMap]
  congr 1
  ext1
  simp [backHalfShiftCLM_add]

theorem norm_dirichletQuotSemigroup_le {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {a : ℝ} (ha : 0 ≤ a) :
    ‖dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha‖ ≤
      Real.exp (a / 2 + α * |a|) * (2 + 2 * a ^ 2) ^ (s / 4) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun q ↦ ?_
  have hq := dirichletStageQuotMap_self hχ hN T hT hp hpT hX hα hs q
  conv_lhs => rw [← hq, dirichletQuotSemigroup_quotMap]
  calc ‖dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
        ⟨backHalfShiftCLM α s hα hs a q.1, _⟩‖
      ≤ 1 * ‖backHalfShiftCLM α s hα hs a q.1‖ := by
        exact (norm_dirichletStageQuotMap_le hχ hN T hT hp hpT hX hα hs |> fun hn ↦
          (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hn (norm_nonneg _)))
    _ = ‖backHalfShiftCLM α s hα hs a q.1‖ := one_mul _
    _ ≤ ‖backHalfShiftCLM α s hα hs a‖ * ‖q.1‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ (Real.exp (a / 2 + α * |a|) * (2 + 2 * a ^ 2) ^ (s / 4)) * ‖q‖ :=
        mul_le_mul_of_nonneg_right (norm_backHalfShiftCLM_le α s hα hs a) (norm_nonneg _)

theorem continuous_dirichletQuotSemigroup_apply {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (q : dirichletStageQuotient χ T p X α s hα hs) :
    ContinuousOn (fun a : ℝ ↦
        if ha : 0 ≤ a then dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha q else 0)
      (Set.Ici 0) := by
  let qMap := dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
  let E := dirichletStageSpace χ T X α s hα hs
  let F_E : ℝ → E := fun a ↦
    if ha : 0 ≤ a then ⟨backHalfShiftCLM α s hα hs a q.1,
      backHalfShiftCLM_mem_dirichletStageSpace hχ hN T (fun r hr ↦ (hT r hr).1.pos) hX hα hs a ha q.2.1⟩
    else 0
  have hF_E_cont : ContinuousOn F_E (Set.Ici 0) := by
    rw [continuousOn_iff_continuous_domRestrict]
    let G : Set.Ici (0 : ℝ) → E := fun a ↦ ⟨backHalfShiftCLM α s hα hs a.1 q.1,
      backHalfShiftCLM_mem_dirichletStageSpace hχ hN T (fun r hr ↦ (hT r hr).1.pos) hX hα hs a.1 a.2 q.2.1⟩
    have hG : Continuous G := Continuous.subtype_mk
      ((continuous_backHalfShiftCLM α s hα hs q.1).comp continuous_subtype_val) _
    refine hG.congr fun ⟨a, ha⟩ ↦ ?_
    change G ⟨a, ha⟩ = F_E a
    have ha0 : 0 ≤ a := ha
    simp [G, F_E, ha0]
  have heq : Set.EqOn
      (fun a : ℝ ↦ if ha : 0 ≤ a then dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha q else 0)
      (fun a : ℝ ↦ qMap (F_E a)) (Set.Ici 0) := by
    intro a ha
    have ha' : 0 ≤ a := ha
    simp only [ha', ↓reduceDIte, F_E]
    have hq := dirichletStageQuotMap_self hχ hN T hT hp hpT hX hα hs q
    conv_lhs => rw [← hq, dirichletQuotSemigroup_quotMap]
  exact (qMap.continuous.comp_continuousOn hF_E_cont).congr heq

theorem dirichletQuotSemigroup_log_prime {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    let hL_nn : 0 ≤ Real.log p := (Real.log_pos (by exact_mod_cast hp.one_lt)).le
    dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (Real.log p) hL_nn =
      χ (p : ZMod N) • ContinuousLinearMap.id ℂ _ := by
  intro hL_nn
  let Q := dirichletStageQuotient χ T p X α s hα hs
  let qMap := dirichletStageQuotMap hχ hN T hT hp hpT hX hα hs
  let S_L := dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (Real.log p) hL_nn
  let T_op : dirichletStageSpace χ T X α s hα hs →L[ℂ] Q := (S_L.comp qMap) - (χ (p : ZMod N) • qMap)
  have hker : ∀ x, T_op x = 0 := by
    refine clm_zero_on_dirichletStageSpace χ T X α s hα hs T_op fun f₀ hf₀ hmem ↦ ?_
    change S_L (qMap ⟨_, _⟩) - χ (p : ZMod N) • qMap ⟨_, _⟩ = 0
    rw [dirichletQuotSemigroup_quotMap, ← map_smul, ← map_sub, dirichletStageQuotMap_eq_zero_iff]
    have hp_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hp.pos
    have hR_pos : 0 < X / ∏ q ∈ T, (q : ℝ) :=
      div_pos hX (Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hT q hq).1.pos)
    have hTpos : ∀ q ∈ T, 0 < q := fun q hq ↦ (hT q hq).1.pos
    let f_L := schwartzScale (Real.exp (-Real.log p)) (Real.exp_pos _).ne' f₀
    have ⟨hfL_box, hshift_eq⟩ := backHalfShiftCLM_apply_depleted_scale hχ hN T hTpos hR_pos hα hs hf₀
      (Real.log p) hL_nn
    have hmem_L : MemLp (dirichletDeplete χ T (twistedHalfLogProfile χ f_L)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN T hTpos hR_pos hα hs hfL_box
    have hfL_shrunk : IsDirichletFixedBoxTest χ (X / ∏ q ∈ insert p T, (q : ℝ)) f_L := by
      have hsub_supp : tsupport (fun w : ℝ ↦ (𝓕 f_L) w) ⊆
          Set.Icc (-(X / (∏ q ∈ T, (q : ℝ)) * Real.exp (-Real.log p)))
            (X / (∏ q ∈ T, (q : ℝ)) * Real.exp (-Real.log p)) := by
        refine closure_minimal ?_ isClosed_Icc
        intro w hw
        dsimp only [f_L] at hw
        rw [Function.mem_support, fourier_schwartzScale _ (Real.exp_pos _).ne' f₀ w,
          abs_of_pos (Real.exp_pos _), Real.exp_neg, inv_inv, div_inv_eq_mul] at hw
        have hnz : (𝓕 f₀) ((p : ℝ) * w) ≠ 0 := by
          intro h0
          apply hw
          rw [Real.exp_log hp_pos, mul_comm w (p : ℝ), h0, mul_zero]
        have hmem_Icc := hf₀.2 (subset_tsupport _ (Function.mem_support.mpr hnz))
        rw [Set.mem_Icc] at hmem_Icc
        rw [Set.mem_Icc, Real.exp_neg, Real.exp_log hp_pos]
        have hw1 : -(X / (∏ q ∈ T, (q : ℝ)) * (p : ℝ)⁻¹) ≤ w := by
          calc -(X / (∏ q ∈ T, (q : ℝ)) * (p : ℝ)⁻¹)
              = (-(X / ∏ q ∈ T, (q : ℝ))) * (p : ℝ)⁻¹ := by ring
            _ ≤ ((p : ℝ) * w) * (p : ℝ)⁻¹ :=
                mul_le_mul_of_nonneg_right hmem_Icc.1 (inv_nonneg.mpr hp_pos.le)
            _ = w := by rw [mul_comm (p : ℝ) w, mul_assoc, mul_inv_cancel₀ hp_pos.ne', mul_one]
        have hw2 : w ≤ X / (∏ q ∈ T, (q : ℝ)) * (p : ℝ)⁻¹ := by
          calc w = ((p : ℝ) * w) * (p : ℝ)⁻¹ := by
                rw [mul_comm (p : ℝ) w, mul_assoc, mul_inv_cancel₀ hp_pos.ne', mul_one]
            _ ≤ (X / ∏ q ∈ T, (q : ℝ)) * (p : ℝ)⁻¹ :=
                mul_le_mul_of_nonneg_right hmem_Icc.2 (inv_nonneg.mpr hp_pos.le)
        exact ⟨hw1, hw2⟩
      have hdiv_eq : X / (∏ q ∈ T, (q : ℝ)) * Real.exp (-Real.log p) =
          X / ∏ q ∈ insert p T, (q : ℝ) := by
        rw [Real.exp_neg, Real.exp_log hp_pos, Finset.prod_insert hpT, div_eq_mul_inv,
          div_eq_mul_inv, mul_inv]
        ring
      refine ⟨fun x ↦ ?_, hdiv_eq ▸ hsub_supp⟩
      simp only [f_L, schwartzScale_apply]
      have hneg : Real.exp (-Real.log p) * (-x) = -(Real.exp (-Real.log p) * x) := by ring
      rw [hneg, hf₀.1]
    have hTpos' : ∀ q ∈ insert p T, 0 < q := fun q hq ↦ by
      rcases Finset.mem_insert.mp hq with rfl | hqT
      · exact hp.pos
      · exact (hT q hqT).1.pos
    have hR'_pos : 0 < X / ∏ q ∈ insert p T, (q : ℝ) :=
      div_pos hX (Finset.prod_pos fun q hq ↦ Nat.cast_pos.mpr (hTpos' q hq))
    have hmem_ins : MemLp (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ f_L)) 2
        (intervalSobolevMeasure volume id (-α) α s false) :=
      dirichletDeplete_memLp hχ hN (insert p T) hTpos' hR'_pos hα hs hfL_shrunk
    have hcomp_eq : toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_L)) hmem_L -
        χ (p : ZMod N) • toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem =
        toDirichletStrip α s (dirichletDeplete χ (insert p T) (twistedHalfLogProfile χ f_L)) hmem_ins := by
      have h1_eq : (1 : ℂ) • toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_L)) hmem_L =
          toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f_L)) hmem_L := one_smul _ _
      rw [← h1_eq]
      refine toDirichletStrip_sub_smul_congr_ae hmem_L hmem hmem_ins fun x ↦ ?_
      have hscale_back : schwartzScale (p : ℝ) hp_pos.ne' f_L = f₀ := by
        ext y
        simp only [f_L, schwartzScale_apply, Real.exp_neg, Real.exp_log hp_pos]
        rw [← mul_assoc, inv_mul_cancel₀ hp_pos.ne', one_mul]
      rw [dirichletDeplete_insert χ hpT, LinearMap.comp_apply]
      have hcomm := dirichletDeplete_commute_step χ p T (twistedHalfLogProfile χ f_L)
      change (1 : ℂ) * dirichletDeplete χ T (twistedHalfLogProfile χ f_L) x -
          χ (p : ZMod N) * dirichletDeplete χ T (twistedHalfLogProfile χ f₀) x =
        depleteStepFun χ p (dirichletDeplete χ T (twistedHalfLogProfile χ f_L)) x
      rw [one_mul, hcomm, ← twistedHalfLogProfile_testDepleteStep χ hp.pos]
      have hstep_f : testDepleteStep χ p f_L = f_L - χ (p : ZMod N) • f₀ := by
        simp [testDepleteStep, hp.ne_zero, hscale_back]
      rw [hstep_f, twistedHalfLogProfile_sub, twistedHalfLogProfile_smul, map_sub, map_smul,
        Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have hstep_mem : backHalfShiftCLM α s hα hs (Real.log p)
          (toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem) -
        χ (p : ZMod N) •
          toDirichletStrip α s (dirichletDeplete χ T (twistedHalfLogProfile χ f₀)) hmem ∈
        dirichletStageSpace χ (insert p T) X α s hα hs := by
      rw [hshift_eq hmem hmem_L, hcomp_eq]
      exact mem_dirichletStageSpace_of_test (insert p T) hα hs hfL_shrunk hmem_ins
    simpa using hstep_mem
  ext1 q
  have hq := dirichletStageQuotMap_self hχ hN T hT hp hpT hX hα hs q
  have h0 := hker ⟨q.1, q.2.1⟩
  dsimp [T_op] at h0
  rw [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, hq, sub_eq_zero] at h0
  exact h0

/-- Modulated circle action `τ_ext u` on `Q`, extended periodically from `[0, Real.log p]` to `ℝ`.
Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496.
Credit: `@mrshu`'s Comment #8 on `#7351`. -/
noncomputable def dirichletQuotModulatedAction {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (u : ℝ) :
    dirichletStageQuotient χ T p X α s hα hs →L[ℂ] dirichletStageQuotient χ T p X α s hα hs :=
  let L : ℝ := Real.log p
  let t0 : ℝ := Complex.arg (χ (p : ZMod N)) / L
  let r : ℝ := Int.fract (u / L) * L
  have hr_nn : 0 ≤ r :=
    mul_nonneg (Int.fract_nonneg (u / L)) (Real.log_pos (by exact_mod_cast hp.one_lt)).le
  Complex.exp (-((t0 : ℂ) * Complex.I * (r : ℂ))) •
    dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r hr_nn

theorem dirichletQuotModulatedAction_eq_of_Icc {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {a : ℝ} (ha0 : 0 ≤ a) (haL : a ≤ Real.log p) :
    dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs a =
      Complex.exp (-((Complex.arg (χ (p : ZMod N)) / Real.log p : ℂ) * Complex.I * (a : ℂ))) •
        dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha0 := by
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rcases lt_or_eq_of_le haL with hlt | rfl
  · have hdiv_nn : 0 ≤ a / Real.log p := div_nonneg ha0 hL_pos.le
    have hdiv_lt : a / Real.log p < 1 := (div_lt_one hL_pos).mpr hlt
    have hfract : Int.fract (a / Real.log p) = a / Real.log p := Int.fract_eq_self.mpr ⟨hdiv_nn, hdiv_lt⟩
    have hr_eq : Int.fract (a / Real.log p) * Real.log p = a := by
      rw [hfract, div_mul_cancel₀ _ hL_pos.ne']
    have hr_C : ((Int.fract (a / Real.log p) * Real.log p : ℝ) : ℂ) = (a : ℂ) := by
      exact_mod_cast hr_eq
    have hpow : Complex.exp (-((Complex.arg (χ (p : ZMod N)) / Real.log p : ℂ) * Complex.I *
          ((Int.fract (a / Real.log p) * Real.log p : ℝ) : ℂ))) =
        Complex.exp (-((Complex.arg (χ (p : ZMod N)) / Real.log p : ℂ) * Complex.I * (a : ℂ))) := by
      rw [hr_C]
    have hsemi : dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs
          (Int.fract (a / Real.log p) * Real.log p)
          (mul_nonneg (Int.fract_nonneg (a / Real.log p)) hL_pos.le) =
        dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha0 := by
      congr 1
    dsimp [dirichletQuotModulatedAction]
    rw [Complex.ofReal_div, hpow, hsemi]
  · have hdiv_one : Real.log p / Real.log p = 1 := div_self hL_pos.ne'
    have hr_zero : Int.fract (Real.log p / Real.log p) * Real.log p = 0 := by
      rw [hdiv_one, Int.fract_one, zero_mul]
    have hS_zero : dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs
          (Int.fract (Real.log p / Real.log p) * Real.log p)
          (mul_nonneg (Int.fract_nonneg _) hL_pos.le) =
        dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs 0 le_rfl := by
      congr 1
    have hpow0 : Complex.exp (-(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) *
          Complex.I * ((Int.fract (Real.log p / Real.log p) * Real.log p : ℝ) : ℂ))) = 1 := by
      rw [hr_zero, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero]
    dsimp [dirichletQuotModulatedAction]
    rw [hpow0, one_smul, hS_zero, dirichletQuotSemigroup_zero, dirichletQuotSemigroup_log_prime]
    ext1 q
    rw [smul_apply, ContinuousLinearMap.id_apply, smul_apply, ContinuousLinearMap.id_apply, smul_smul]
    have hnorm : ‖χ (p : ZMod N)‖ = 1 := dirichlet_norm_apply_eq_one_of_coprime χ hpN
    have hexp : Complex.exp ((Complex.arg (χ (p : ZMod N)) : ℂ) * Complex.I) = χ (p : ZMod N) := by
      have h := Complex.norm_mul_exp_arg_mul_I (χ (p : ZMod N))
      rwa [hnorm, Complex.ofReal_one, one_mul] at h
    have hmul_arg :
        (-((Complex.arg (χ (p : ZMod N)) / Real.log p : ℂ) * Complex.I * (Real.log p : ℂ))) =
          -((Complex.arg (χ (p : ZMod N)) : ℂ) * Complex.I) := by
      have hL_C : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
      calc -((Complex.arg (χ (p : ZMod N)) / Real.log p : ℂ) * Complex.I * (Real.log p : ℂ))
          = -((Complex.arg (χ (p : ZMod N)) : ℂ) * Complex.I *
              ((Real.log p : ℂ) / (Real.log p : ℂ))) := by ring
        _ = -((Complex.arg (χ (p : ZMod N)) : ℂ) * Complex.I) := by rw [div_self hL_C, mul_one]
    rw [hmul_arg, Complex.exp_neg, hexp,
      inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)), one_smul]

theorem dirichletQuotModulatedAction_periodic {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    Function.Periodic (dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs) (Real.log p) := by
  intro u
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hfract : Int.fract ((u + Real.log p) / Real.log p) = Int.fract (u / Real.log p) := by
    rw [add_div, div_self hL_pos.ne', Int.fract_add_one]
  dsimp [dirichletQuotModulatedAction]
  simp_rw [hfract]

theorem dirichletQuotModulatedAction_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) :
    dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs 0 = ContinuousLinearMap.id ℂ _ := by
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  rw [dirichletQuotModulatedAction_eq_of_Icc hχ hN T hT hp hpN hpT hX hα hs le_rfl hL_pos.le,
    Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero, one_smul,
    dirichletQuotSemigroup_zero]

private theorem dirichletQuotModulatedSemigroup_add_nat_mul {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    let L := Real.log p
    let t0 := Complex.arg (χ (p : ZMod N)) / L
    Complex.exp (-((t0 : ℂ) * Complex.I * ((r + n * L : ℝ) : ℂ))) •
        dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r + n * L)
          (add_nonneg hr (mul_nonneg (Nat.cast_nonneg n) (Real.log_pos (by exact_mod_cast hp.one_lt)).le)) =
      Complex.exp (-((t0 : ℂ) * Complex.I * (r : ℂ))) •
        dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r hr := by
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  induction n with
  | zero => simp
  | succ k ih =>
    have hhk_nn : 0 ≤ r + (k : ℝ) * Real.log p :=
      add_nonneg hr (mul_nonneg (Nat.cast_nonneg k) hL_pos.le)
    have hsplit_r : r + ((k + 1 : ℕ) : ℝ) * Real.log p = (r + (k : ℝ) * Real.log p) + Real.log p := by
      push_cast; ring
    have hnorm : ‖χ (p : ZMod N)‖ = 1 := dirichlet_norm_apply_eq_one_of_coprime χ hpN
    have hexp : Complex.exp ((Complex.arg (χ (p : ZMod N)) : ℂ) * Complex.I) = χ (p : ZMod N) := by
      have h := Complex.norm_mul_exp_arg_mul_I (χ (p : ZMod N))
      rwa [hnorm, Complex.ofReal_one, one_mul] at h
    have hexp_neg : Complex.exp (-((Complex.arg (χ (p : ZMod N)) : ℂ) * Complex.I)) =
        (χ (p : ZMod N))⁻¹ := by
      rw [Complex.exp_neg, hexp]
    have hL_C : (Real.log p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL_pos.ne'
    have hmod_step :
        Complex.exp (-(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I *
            ((r + ((k + 1 : ℕ) : ℝ) * Real.log p : ℝ) : ℂ))) =
          Complex.exp (-(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I *
              ((r + (k : ℝ) * Real.log p : ℝ) : ℂ))) * (χ (p : ZMod N))⁻¹ := by
      rw [hsplit_r]
      have harg : -(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I *
            ((r + (k : ℝ) * Real.log p + Real.log p : ℝ) : ℂ)) =
          -(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I *
              ((r + (k : ℝ) * Real.log p : ℝ) : ℂ)) +
            (-((Complex.arg (χ (p : ZMod N)) : ℂ) * Complex.I)) := by
        calc -(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I *
              (((r + (k : ℝ) * Real.log p + Real.log p : ℝ) : ℂ)))
            = -(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I *
                ((r + (k : ℝ) * Real.log p : ℝ) : ℂ)) +
              (-((Complex.arg (χ (p : ZMod N)) : ℂ) * Complex.I *
                ((Real.log p : ℂ) / (Real.log p : ℂ)))) := by push_cast; ring
          _ = _ := by rw [div_self hL_C, mul_one]
      rw [harg, Complex.exp_add, hexp_neg]
    have hS_split : dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r + ((k + 1 : ℕ) : ℝ) * Real.log p)
          (add_nonneg hr (mul_nonneg (Nat.cast_nonneg (k + 1)) hL_pos.le)) =
        (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r + (k : ℝ) * Real.log p) hhk_nn).comp
          (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (Real.log p) hL_pos.le) := by
      have hS1 : dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r + ((k + 1 : ℕ) : ℝ) * Real.log p)
            (add_nonneg hr (mul_nonneg (Nat.cast_nonneg (k + 1)) hL_pos.le)) =
          dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs ((r + (k : ℝ) * Real.log p) + Real.log p)
            (add_nonneg hhk_nn hL_pos.le) := by
        congr 1
      rw [hS1, dirichletQuotSemigroup_add hχ hN T hT hp hpT hX hα hs hhk_nn hL_pos.le]
    dsimp only
    rw [hS_split, dirichletQuotSemigroup_log_prime]
    have hcomp_smul : (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r + (k : ℝ) * Real.log p) hhk_nn).comp
        (χ (p : ZMod N) • ContinuousLinearMap.id ℂ _) =
        χ (p : ZMod N) • dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r + (k : ℝ) * Real.log p) hhk_nn := by
      ext1 q; simp
    rw [hcomp_smul, hmod_step, smul_smul, mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)), mul_one]
    exact ih

private theorem dirichletQuotSemigroup_congr {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a = b) :
    dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs a ha =
      dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs b hb := by
  subst hab
  rfl

theorem dirichletQuotModulatedAction_add {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (hN : 1 < N)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime ∧ q.Coprime N)
    {p : ℕ} (hp : p.Prime) (hpN : p.Coprime N) (hpT : p ∉ T)
    {X α s : ℝ} (hX : 0 < X) (hα : 0 ≤ α) (hs : 0 ≤ s) (u v : ℝ) :
    dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs (u + v) =
      (dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs u).comp
        (dirichletQuotModulatedAction hχ hN T hT hp hpT hX hα hs v) := by
  have hL_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  let L := Real.log p
  let t0 := Complex.arg (χ (p : ZMod N)) / L
  let f1 := Int.fract (u / L)
  let f2 := Int.fract (v / L)
  let r1 := f1 * L
  let r2 := f2 * L
  have hf1_0 : 0 ≤ f1 := Int.fract_nonneg _
  have hf2_0 : 0 ≤ f2 := Int.fract_nonneg _
  have hf1_1 : f1 < 1 := Int.fract_lt_one _
  have hf2_1 : f2 < 1 := Int.fract_lt_one _
  have hr1 : 0 ≤ r1 := mul_nonneg hf1_0 hL_pos.le
  have hr2 : 0 ≤ r2 := mul_nonneg hf2_0 hL_pos.le
  have hu_eq : u = (⌊u / L⌋ : ℝ) * L + r1 := by
    have := Int.floor_add_fract (u / L)
    calc u = (u / L) * L := (div_mul_cancel₀ u hL_pos.ne').symm
      _ = ((⌊u / L⌋ : ℝ) + f1) * L := by rw [this]
      _ = _ := by ring
  have hv_eq : v = (⌊v / L⌋ : ℝ) * L + r2 := by
    have := Int.floor_add_fract (v / L)
    calc v = (v / L) * L := (div_mul_cancel₀ v hL_pos.ne').symm
      _ = ((⌊v / L⌋ : ℝ) + f2) * L := by rw [this]
      _ = _ := by ring
  have hsum_div : (u + v) / L = ((⌊u / L⌋ + ⌊v / L⌋ : ℤ) : ℝ) + (f1 + f2) := by
    have hsum_num : u + v = ((⌊u / L⌋ + ⌊v / L⌋ : ℤ) : ℝ) * L + (r1 + r2) := by
      calc u + v = ((⌊u / L⌋ : ℝ) * L + r1) + ((⌊v / L⌋ : ℝ) * L + r2) := by rw [← hu_eq, ← hv_eq]
        _ = ((⌊u / L⌋ + ⌊v / L⌋ : ℤ) : ℝ) * L + (r1 + r2) := by push_cast; ring
    calc (u + v) / L = (((⌊u / L⌋ + ⌊v / L⌋ : ℤ) : ℝ) * L + (r1 + r2)) / L := by rw [hsum_num]
      _ = ((⌊u / L⌋ + ⌊v / L⌋ : ℤ) : ℝ) + (f1 + f2) := by
          rw [add_div, mul_div_cancel_right₀ _ hL_pos.ne']
          dsimp [r1, r2]; rw [← add_mul, mul_div_cancel_right₀ _ hL_pos.ne']
  have hfr : Int.fract ((u + v) / L) = Int.fract (f1 + f2) := by
    rw [hsum_div, add_comm, Int.fract_add_intCast, add_comm]
  rcases lt_or_ge (f1 + f2) 1 with hlt1 | hge1
  · have hfr_eq : Int.fract ((u + v) / L) * L = r1 + r2 := by
      rw [hfr, Int.fract_eq_self.mpr ⟨add_nonneg hf1_0 hf2_0, hlt1⟩, add_mul]
    have hfr_eq_C : ((Int.fract ((u + v) / L) * L : ℝ) : ℂ) = ((r1 + r2 : ℝ) : ℂ) := by
      exact_mod_cast hfr_eq
    have hpow : Complex.exp (-((t0 : ℂ) * Complex.I *
          ((Int.fract ((u + v) / L) * L : ℝ) : ℂ))) =
        Complex.exp (-((t0 : ℂ) * Complex.I * ((r1 + r2 : ℝ) : ℂ))) := by
      rw [hfr_eq_C]
    have hsemi : dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (Int.fract ((u + v) / L) * L)
          (mul_nonneg (Int.fract_nonneg _) hL_pos.le) =
        dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r1 + r2) (add_nonneg hr1 hr2) :=
      dirichletQuotSemigroup_congr hχ hN T hT hp hpT hX hα hs _ _ hfr_eq
    ext1 q
    rw [ContinuousLinearMap.comp_apply]
    dsimp [dirichletQuotModulatedAction]
    rw [smul_apply, smul_apply, smul_apply, map_smul, smul_smul,
      hpow, hsemi, dirichletQuotSemigroup_add hχ hN T hT hp hpT hX hα hs hr1 hr2,
      ContinuousLinearMap.comp_apply]
    have hce : -((t0 : ℂ) * Complex.I * ((r1 + r2 : ℝ) : ℂ)) =
        -((t0 : ℂ) * Complex.I * (r1 : ℂ)) + -((t0 : ℂ) * Complex.I * (r2 : ℂ)) := by
      push_cast; ring
    rw [hce, Complex.exp_add]
  · have hf_lt2 : f1 + f2 - 1 < 1 := by linarith
    have hfr_1 : Int.fract (f1 + f2) = f1 + f2 - 1 := by
      have h1 : f1 + f2 = (f1 + f2 - 1) + ((1 : ℤ) : ℝ) := by push_cast; ring
      conv_lhs => rw [h1, Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, hf_lt2⟩
    let r3 := Int.fract ((u + v) / L) * L
    have hr3_nn : 0 ≤ r3 := mul_nonneg (Int.fract_nonneg _) hL_pos.le
    have hr3_add : r3 + (1 : ℕ) * L = r1 + r2 := by
      dsimp [r3, r1, r2]; rw [hfr, hfr_1]; push_cast; ring
    have hstep := dirichletQuotModulatedSemigroup_add_nat_mul hχ hN T hT hp hpN hpT hX hα hs 1 hr3_nn
    dsimp only at hstep
    have hr3_C : ((r1 + r2 : ℝ) : ℂ) = ((r3 + (1 : ℕ) * Real.log p : ℝ) : ℂ) := by
      exact_mod_cast hr3_add.symm
    have h1 : Complex.exp (-((t0 : ℂ) * Complex.I * ((r1 + r2 : ℝ) : ℂ))) =
        Complex.exp (-(((Complex.arg (χ (p : ZMod N)) / Real.log p : ℝ) : ℂ) * Complex.I *
          ((r3 + (1 : ℕ) * Real.log p : ℝ) : ℂ))) := by
      dsimp only [t0, L]
      rw [hr3_C]
    have h2 : dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r1 + r2) (add_nonneg hr1 hr2) =
        dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r3 + (1 : ℕ) * Real.log p)
          (add_nonneg hr3_nn (mul_nonneg (Nat.cast_nonneg 1) hL_pos.le)) :=
      dirichletQuotSemigroup_congr hχ hN T hT hp hpT hX hα hs _ _
        (show r1 + r2 = r3 + (1 : ℕ) * Real.log p from hr3_add.symm)
    have hstep' : Complex.exp (-((t0 : ℂ) * Complex.I * ((r1 + r2 : ℝ) : ℂ))) •
          dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (r1 + r2) (add_nonneg hr1 hr2) =
        Complex.exp (-((t0 : ℂ) * Complex.I * (r3 : ℂ))) •
          dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r3 hr3_nn := by
      rw [h1, h2]
      exact hstep
    ext1 q
    rw [ContinuousLinearMap.comp_apply]
    dsimp [dirichletQuotModulatedAction]
    have hcomp := congrFun (congrArg DFunLike.coe hstep') q
    rw [smul_apply, smul_apply] at hcomp
    rw [smul_apply, smul_apply, smul_apply, map_smul, smul_smul,
      ← ContinuousLinearMap.comp_apply,
      ← dirichletQuotSemigroup_add hχ hN T hT hp hpT hX hα hs hr1 hr2]
    have hstep_r3 : Complex.exp (-((t0 : ℂ) * Complex.I * (r3 : ℂ))) •
          dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs r3 hr3_nn q =
        Complex.exp (-((t0 : ℂ) * Complex.I * ((Int.fract ((u + v) / L) * L : ℝ) : ℂ))) •
          (dirichletQuotSemigroup hχ hN T hT hp hpT hX hα hs (Int.fract ((u + v) / L) * L)
            (mul_nonneg (Int.fract_nonneg _) hL_pos.le)) q := rfl
    rw [← hstep_r3, ← hcomp]
    have hce : -((t0 : ℂ) * Complex.I * ((r1 + r2 : ℝ) : ℂ)) =
        -((t0 : ℂ) * Complex.I * (r1 : ℂ)) + -((t0 : ℂ) * Complex.I * (r2 : ℂ)) := by
      push_cast; ring
    rw [hce, Complex.exp_add]


end CircleActionAndTraceNorm

end RiemannMasullo.Isolated
