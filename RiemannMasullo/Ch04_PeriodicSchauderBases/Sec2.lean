module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a
public import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.PSeries
import RiemannMasullo.ForMathlib.Analysis.Fourier.PoissonSummation

/-!
# Periodization and Schauder bases on the positive real axis

Masullo, §4.2, pp. 161–174. The logarithmic coordinate is (x = log t).
The circle coordinate is (x / log γ) modulo one.
-/

@[expose] public noncomputable section

open Bornology Function MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff Distributions SchwartzMap

namespace RiemannMasullo

local notation "E" => PositiveRealExponentialDecay (Set.univ : Set ℝ)
local notation "S" => ElementarySchwartz 0 1 0 (PUnit : Type)
local notation "G" => ElementaryLieGroup 0 1 0 (PUnit : Type)
local notation "T" => AddCircle (1 : ℝ)
local notation "point" z => ((0, fun _ : Fin 1 ↦ z, 0, PUnit.unit) : G)
local notation "freq" => Equiv.intEquivNat.symm
local notation "phase[" γ ", " m "]" => (2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) / (Real.log γ : ℂ))

section Periodization

variable (γ : ℝ) (hγ : 1 < γ)

/-- Paper: Definition 4.2.1.1, p. 162. Sum the translates of a logarithmic profile
at a representative of the unit-circle coordinate.
Deviation: The same formula is used on ordinary Schwartz profiles, as in Remark 4.2.2.6. -/
def cyclicPeriodizationValue (_hγ : 1 < γ) (f : 𝓢(ℝ, ℂ)) (g : G) : ℂ :=
  ∑' k : ℤ, f (Real.log γ * ((AddCircle.equivIco 1 0 (g.2.1 0)).val + k))

/-- Paper: Definition 4.2.1.1, p. 162. The sum converges and can be computed at
any real lift of the circle coordinate.
Deviation: This also checks the formula on the ordinary Schwartz space. -/
theorem cyclicPeriodizationValue_hasSum (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f (x + (k : ℝ) * Real.log γ))
      (cyclicPeriodizationValue γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by
  let L := Real.log γ
  have hL : L ≠ 0 := (Real.log_pos hγ).ne'
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL)
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (f.compSubConstCLM ℂ (-x))
  have hs : Summable (fun k : ℤ ↦ F (k : ℝ)) :=
    summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
      ((F.isBigO_cocompact_rpow (-2)).comp_tendsto Int.tendsto_coe_cofinite)
  let a (k : ℤ) := f (x + (k : ℝ) * L)
  have ha : Summable a := by
    simpa [a, F, e, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, add_comm] using hs
  let r := ((AddCircle.equivIco (1 : ℝ) 0) ((x / L : ℝ) : T)).val
  change HasSum a (∑' k : ℤ, f (L * (r + k)))
  have hr : r = x / L - ⌊x / L⌋ := by
    dsimp only [r]
    rw [AddCircle.coe_equivIco_mk_apply, div_one, mul_one, ← Int.self_sub_floor]
  convert ha.hasSum using 1
  calc
    (∑' k : ℤ, f (L * (r + k))) = ∑' k : ℤ, a ((Equiv.subRight ⌊x / L⌋) k) := by
      apply tsum_congr
      intro k
      simp only [a, Equiv.subRight_apply, Int.cast_sub, hr]
      congr 1
      field_simp
      ring
    _ = ∑' k : ℤ, a k := (Equiv.subRight ⌊x / L⌋).tsum_eq a

/-- A smooth periodic lift gives an elementary Schwartz function on the circle. -/
private theorem mem_elementarySchwartz_circle_of_contDiff {h : T → ℂ}
    (hs : ContDiff ℝ ∞ (fun x : ℝ ↦ h (x : T))) :
    (fun g : G ↦ h (g.2.1 0)) ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  let X := EuclideanSpace ℝ (Fin 0) × EuclideanSpace ℝ (Fin 1)
  let φ : G → ℂ := fun g ↦ h (g.2.1 0)
  let L : X →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp (ContinuousLinearMap.snd ℝ _ _)
  have hφ (a : Fin 0 → ℤ) (b : PUnit) :
      ContDiff ℝ ∞ (fun xt ↦ φ (elementaryCover xt a b)) := hs.comp L.contDiff
  refine ⟨hφ, fun i ↦ ?_⟩
  let s (x : ℝ) : X := (0, x • EuclideanSpace.single 0 1)
  have hsc : Continuous s := continuous_const.prodMk (continuous_id.smul continuous_const)
  let D := elementaryPartial φ i.2.1 i.2.2.1
  have hD := elementaryPartial_descends φ i.2.1 i.2.2.1 0 PUnit.unit (hφ 0 PUnit.unit)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (hD.1.continuous.comp hsc).continuousOn
  apply lt_of_le_of_lt (b := ENNReal.ofReal C) _ ENNReal.ofReal_lt_top
  refine iSup_le fun xt ↦ iSup_le fun a ↦ iSup_le fun b ↦ ?_
  have ha : a = 0 := Subsingleton.elim _ _
  have hb : b = PUnit.unit := Subsingleton.elim _ _
  subst a b
  let r := (AddCircle.equivIco (1 : ℝ) 0) (xt.2 0 : T)
  have hr : (r : ℝ) ∈ Icc 0 1 := Ico_subset_Icc_self (by simpa using r.property)
  have he : elementaryCover (s r) (0 : Fin 0 → ℤ) PUnit.unit =
      elementaryCover xt 0 PUnit.unit := by
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ rfl)
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    change (↑((r.val • EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0) : T) = _
    trans (r.val : T)
    · simp [PiLp.smul_apply]
    · exact AddCircle.coe_equivIco
  have hbound : ‖D xt 0 PUnit.unit‖ ≤ C := by
    dsimp only [D]
    rw [← hD.2 (s r) xt he]
    exact hC r hr
  simp only [Fin.prod_univ_zero, one_mul, ENNReal.coe_nnreal_eq, coe_nnNorm]
  exact ENNReal.ofReal_le_ofReal hbound

/-- Paper: Lemma 4.2.1.5(1), p. 165. The orbit sum gives a smooth function
on the circle.
Deviation: Smoothness also holds on the ordinary Schwartz source. -/
theorem cyclicPeriodizationValue_mem (f : 𝓢(ℝ, ℂ)) :
    cyclicPeriodizationValue γ hγ f ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by
  let h (z : T) := cyclicPeriodizationValue γ hγ f (point z)
  change (fun g : G ↦ h (g.2.1 0)) ∈ _
  apply mem_elementarySchwartz_circle_of_contDiff
  let L := Real.log γ
  have hL : L ≠ 0 := (Real.log_pos hγ).ne'
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL)
  let F := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f
  have he : (fun x : ℝ ↦ h (x : T)) = fun x : ℝ ↦ ∑' n : ℤ, F (x + n) := by
    funext x
    simpa [h, F, e, L, hL, (Real.log_pos hγ).ne', add_mul] using
      (cyclicPeriodizationValue_hasSum γ hγ f (x * L)).tsum_eq.symm
  rw [he]
  exact schwartz_contDiff_periodization F

/-- Paper: Lemma 4.2.1.5(2), p. 165. The orbit sum is linear and continuous
in the Schwartz profile.
Deviation: The bundled properties also hold on the ordinary Schwartz source. -/
theorem cyclicPeriodizationValue_spec :
    (∀ f g, cyclicPeriodizationValue γ hγ (f + g) =
      cyclicPeriodizationValue γ hγ f + cyclicPeriodizationValue γ hγ g) ∧
    (∀ (c : ℂ) f, cyclicPeriodizationValue γ hγ (c • f) = c • cyclicPeriodizationValue γ hγ f) ∧
    Continuous (Y := S) (fun f ↦ (⟨cyclicPeriodizationValue γ hγ f,
      cyclicPeriodizationValue_mem γ hγ f⟩ : S)) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. The cyclic orbit sum is a continuous linear
map from ordinary Schwartz profiles to smooth functions on the circle. -/
def cyclicSchwartzPeriodization : 𝓢(ℝ, ℂ) →L[ℂ] S where
  toFun f := ⟨cyclicPeriodizationValue γ hγ f, cyclicPeriodizationValue_mem γ hγ f⟩
  map_add' f g := Subtype.ext ((cyclicPeriodizationValue_spec γ hγ).1 f g)
  map_smul' c f := Subtype.ext ((cyclicPeriodizationValue_spec γ hγ).2.1 c f)
  cont := (cyclicPeriodizationValue_spec γ hγ).2.2

/-- Paper: Remark 4.2.2.6, p. 173. On the ordinary Schwartz space, periodization
has the same absolutely convergent orbit sum on a logarithmic lift. -/
theorem cyclicSchwartzPeriodization_hasSum (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f (x + (k : ℝ) * Real.log γ))
      (cyclicSchwartzPeriodization γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by sorry

/-- Paper: Definition 4.2.1.1, p. 162. Periodization of an exponentially
decaying Schwartz function sums its translates by integer powers of γ.
Deviation: The source is represented by logarithmic profiles and the target
by the elementary Schwartz space on the unit circle. -/
def cyclicPeriodization : E →ₗ[ℂ] S :=
  (cyclicSchwartzPeriodization γ hγ).toLinearMap.comp
    (logExponentialDecayTwist univ ⟨0, mem_univ _⟩)

/-- Paper: (4.2.1.2), p. 162. The periodized value is the sum over the orbit
of any logarithmic lift. The statement records convergence of the series. -/
theorem cyclicPeriodization_hasSum (f : E) (x : ℝ) :
    HasSum (fun k : ℤ ↦ f.val (x + (k : ℝ) * Real.log γ))
      (cyclicPeriodization γ hγ f (point ((x / Real.log γ : ℝ) : T))) := by sorry

end Periodization

section Fourier

/-- Paper: (4.2.1.3), p. 162. The circle Fourier monomial is smooth and
belongs to the elementary Schwartz space. -/
theorem cyclicExponential_mem (m : ℤ) :
    (fun g : G ↦ fourier m (g.2.1 0)) ∈ elementarySchwartzSubmodule 0 1 0 PUnit.{1} := by sorry

/-- Paper: (4.2.1.3), p. 162. The exponential system consists of the usual
Fourier monomials in the normalized circle coordinate. -/
def cyclicExponential (m : ℤ) : S :=
  ⟨fun g ↦ fourier m (g.2.1 0), cyclicExponential_mem m⟩

/-- Paper: (4.2.1.3), p. 162. The monomial pulled back to the positive real
axis is the power with exponent (2πim / log γ).
Deviation: The argument x on the cover is the logarithm of the positive variable. -/
theorem cyclicExponential_apply (γ : ℝ) (hγ : 1 < γ) (m : ℤ) (x : ℝ) :
    cyclicExponential m (point ((x / Real.log γ : ℝ) : T)) =
      Complex.exp (phase[γ, m] * (x : ℂ)) := by sorry

/-- Paper: (4.2.1.4), p. 162. The normalized circle Fourier coefficient is
linear and continuous for the smooth topology. -/
theorem cyclicFourierCoeff_spec (m : ℤ) :
    (∀ f g : S, fourierCoeff (fun z : T ↦ (f + g) (point z)) m =
      fourierCoeff (fun z : T ↦ f (point z)) m + fourierCoeff (fun z : T ↦ g (point z)) m) ∧
    (∀ (c : ℂ) (f : S), fourierCoeff (fun z : T ↦ (c • f) (point z)) m =
      c * fourierCoeff (fun z : T ↦ f (point z)) m) ∧
    Continuous (fun f : S ↦ fourierCoeff (fun z : T ↦ f (point z)) m) := by sorry

/-- Paper: (4.2.1.4), p. 162. The coefficient uses Mathlib's Fourier integral
with probability Haar measure, which absorbs the factor (1 / log γ). -/
def cyclicFourierCoeff (m : ℤ) : StrongDual ℂ S where
  toFun f := fourierCoeff (fun z : T ↦ f (point z)) m
  map_add' := (cyclicFourierCoeff_spec m).1
  map_smul' := (cyclicFourierCoeff_spec m).2.1
  cont := (cyclicFourierCoeff_spec m).2.2

/-- Paper: Lemma 4.2.1.2, p. 162. A monomial has its own coefficient equal to
one and every other coefficient zero. -/
theorem cyclicFourierCoeff_exponential (m n : ℤ) :
    cyclicFourierCoeff m (cyclicExponential n) = if m = n then 1 else 0 := by sorry

/-- Paper: Lemma 4.2.1.2(1), p. 162. The circle exponentials form an absolute
Schauder basis with the Fourier coefficient functionals.
Deviation: The Schauder basis predicates of §4.1 use the natural-number
enumeration of the integer frequencies. -/
theorem cyclicExponential_absoluteBasis :
    IsSchauderBasis (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) ∧
      SchauderBasis.IsAbsolute (cyclicExponential ∘ freq) (cyclicFourierCoeff ∘ freq) := by sorry

/-- Paper: Lemma 4.2.1.2(2), p. 162. Fourier coefficients are an unconditional
Schauder basis of the strong dual, with coordinates given by evaluation on the monomials.
Deviation: Frequencies are enumerated by the natural numbers. -/
theorem cyclicFourierCoeff_unconditionalBasis :
    let ev := fun n : ℕ ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (cyclicExponential (freq n))
    IsSchauderBasis (cyclicFourierCoeff ∘ freq) ev ∧
      SchauderBasis.IsUnconditional (cyclicFourierCoeff ∘ freq) ev := by sorry

/-- Paper: Lemma 4.2.1.2(3), p. 162. The quotient Fourier coefficient is the
normalized integral of the lift over the multiplicative fundamental interval. -/
theorem cyclicFourierCoeff_interval (γ : ℝ) (hγ : 1 < γ) (f : S) (m : ℤ) :
    cyclicFourierCoeff m f =
      (Real.log γ : ℂ)⁻¹ * ∫ t in (1 : ℝ)..γ,
        f (point ((Real.log t / Real.log γ : ℝ) : T)) *
          Complex.exp (-phase[γ, m] * (Real.log t : ℂ)) / (t : ℂ) := by sorry

-- TODO(paper-gap): The estimate (4.2.1.7) uses m^k for negative frequencies.
-- For f = e₋₁ and k = 1 the printed right-hand side is negative.

end Fourier

section QuotientDual

variable {X : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℂ X] [T2Space X] [PolynormableSpace ℂ X]

/-- Paper: Lemma 4.2.1.3, p. 163. Pullback along the quotient embeds the weak dual
and has image the continuous functionals vanishing on the closed subspace. -/
theorem quotientDual_weakEmbedding (M : Submodule ℂ X) (hM : IsClosed (M : Set X)) :
    let pull := fun l : WeakDual ℂ (X ⧸ M) ↦ StrongDual.toWeakDual (l.toStrongDual.comp M.mkQL)
    IsEmbedding pull ∧ range pull = {l | ∀ x ∈ M, l x = 0} := by
  dsimp only
  constructor
  · have he : IsEmbedding (fun l : WeakDual ℂ (X ⧸ M) ↦ (l : (X ⧸ M) → ℂ)) :=
      WeakBilin.isEmbedding (B := topDualPairing ℂ (X ⧸ M)) ContinuousLinearMap.coe_injective
    have hπ := M.mkQ_surjective.isEmbedding_comp (X := ℂ) M.mkQ
    apply Topology.IsEmbedding.of_comp (g := fun l : WeakDual ℂ X ↦ (l : X → ℂ))
      (WeakDual.continuous_of_continuous_eval fun x ↦ WeakDual.eval_continuous (M.mkQ x))
      WeakDual.coeFn_continuous
    exact hπ.comp he
  · ext l
    constructor
    · rintro ⟨v, rfl⟩ x hx
      change v (Submodule.Quotient.mk x) = 0
      rw [(Submodule.Quotient.mk_eq_zero M).mpr hx, map_zero]
    · intro h
      refine ⟨StrongDual.toWeakDual (M.liftQL l.toStrongDual (fun x hx ↦ h x hx)), ?_⟩
      exact DFunLike.ext _ _ fun _ ↦ rfl

/-- Paper: Lemma 4.2.1.3, p. 163. The image of the quotient adjoint in the
strong dual consists precisely of the functionals vanishing on the subspace. -/
theorem quotientDual_strongRange (M : Submodule ℂ X) (hM : IsClosed (M : Set X)) :
    range (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) =
      {l : StrongDual ℂ X | ∀ x ∈ M, l x = 0} := by
  exact (quotientDual_weakEmbedding M hM).2

/-- Paper: Lemma 4.2.1.3(1), p. 163. For a nuclear Fréchet space the quotient
adjoint also embeds the strong dual, with image the same annihilator. -/
theorem quotientDual_strongEmbedding_of_nuclear (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (hN : IsNuclearTVS X) (hF : IsFrechetTVS X) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by sorry

/-- Paper: Lemma 4.2.1.3(2), p. 164. For a Hilbert space the quotient adjoint
embeds the strong dual, with image the annihilator of the closed subspace. -/
theorem quotientDual_strongEmbedding_of_hilbert {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (M : Submodule ℂ H) (hM : IsClosed (M : Set H)) :
    IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL) := by
  have : CompleteSpace M := hM.completeSpace_coe
  let s : (H ⧸ M) →L[ℂ] H :=
    Mᗮ.subtypeL.comp M.quotientEquivOrthogonal.toLinearIsometry.toContinuousLinearMap
  let r := ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ s
  apply Topology.IsEmbedding.of_leftInverse (f := r) _ r.continuous
    (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL).continuous
  intro φ
  ext x
  change φ (M.mkQ ((M.quotientEquivOrthogonal x : Mᗮ) : H)) = φ x
  congr 1
  exact (M.quotientEquivOrthogonal_symm_eq_mk _ (M.quotientEquivOrthogonal x).property).symm.trans
    (M.quotientEquivOrthogonal.symm_apply_apply x)

/-- Paper: Remark 4.2.1.4, p. 164. In a totally reflexive Fréchet space, a
strong embedding of the quotient adjoint implies bounded lifting for the quotient. -/
theorem liftsBoundedSets_of_quotientDual_strongEmbedding (hF : IsFrechetTVS X)
    (hR : ∀ (N : Submodule ℂ X), IsClosed (N : Set X) →
      ∃ e : (X ⧸ N) ≃L[ℂ] StrongDual ℂ (StrongDual ℂ (X ⧸ N)),
        ∀ x l, e x l = l x)
    (M : Submodule ℂ X) (hM : IsClosed (M : Set X))
    (h : IsEmbedding (ContinuousLinearMap.precomp (τ := RingHom.id ℂ) ℂ M.mkQL)) :
    LiftsBoundedSets M.mkQL := by sorry

-- TODO(paper-gap): The classification in Remark 4.2.1.4 needs a hypothesis
-- about bounded lifting for all closed-subspace quotients of X.

end QuotientDual

section Kernel

variable (γ : ℝ) (hγ : 1 < γ)

/-- Paper: Lemma 4.2.1.5(2), p. 165. The periodization of exponential profiles
is continuous. Smoothness in part (1) is built into its elementary Schwartz target. -/
theorem cyclicPeriodization_continuous : Continuous (cyclicPeriodization γ hγ) := by sorry

/-- Paper: Lemma 4.2.1.5(2), p. 165. Every smooth quotient function has an
exponentially decaying lift under periodization. -/
theorem cyclicPeriodization_surjective : Surjective (cyclicPeriodization γ hγ) := by sorry

/-- Paper: Lemma 4.2.1.5(2), p. 165. Periodization sends open sets to open sets. -/
theorem cyclicPeriodization_isOpenMap : IsOpenMap (cyclicPeriodization γ hγ) := by sorry

/-- Paper: Lemma 4.2.1.5(2), p. 165. Bundle the periodization and its continuity
as a continuous linear map. -/
def cyclicPeriodizationCLM : E →L[ℂ] S :=
  ⟨cyclicPeriodization γ hγ, cyclicPeriodization_continuous γ hγ⟩

/-- Paper: Lemma 4.2.1.5(2), p. 165. The bundled map gives the periodization
with the same value at every logarithmic lift. -/
theorem cyclicPeriodizationCLM_apply (f : E) (x : ℝ) :
    cyclicPeriodizationCLM γ hγ f (point ((x / Real.log γ : ℝ) : T)) =
      ∑' k : ℤ, f.val (x + (k : ℝ) * Real.log γ) := by sorry

local notation "Φ" => cyclicPeriodizationCLM γ hγ
local notation "Mγ" => LinearMap.ker (ContinuousLinearMap.toLinearMap Φ)
local notation "Q" => E ⧸ Mγ
local notation "desc" => Submodule.liftQL Mγ Φ le_rfl

/-- Paper: Lemma 4.2.1.5(3), p. 165. The kernel is the closed linear span of
the differences between a function and its translate by γ.
Deviation: The difference is expressed in logarithmic coordinates. -/
theorem cyclicPeriodization_ker :
    Mγ = (Submodule.span ℂ {g : E | ∃ f : E,
      ∀ x : ℝ, g.val x = f.val x - f.val (x + Real.log γ)}).topologicalClosure := by sorry

/-- Paper: Lemma 4.2.1.5(3), p. 165. The quotient functional is obtained from
the Fourier coefficient by undoing probability Haar normalization.
Its pullback is the Mellin evaluation at the negative Fourier frequency. -/
def cyclicQuotientMellinCoeff (m : ℤ) : StrongDual ℂ Q :=
  (Real.log γ : ℂ) • (cyclicFourierCoeff m).comp desc

/-- Paper: Lemma 4.2.1.5(3), p. 165. On representatives the quotient functional
is the Mellin integral with exponent −2πim/log γ. -/
theorem cyclicQuotientMellinCoeff_mk (m : ℤ) (f : E) :
    cyclicQuotientMellinCoeff γ hγ m (Submodule.mkQL Mγ f) =
      mellin (fun t ↦ f.val (Real.log t)) (-phase[γ, m]) := by sorry

-- TODO(paper-gap): In the continuity proof, (4.2.1.14) cannot hold for fixed T
-- and arbitrary ε. At t = T γⁿ the term k = -n alone equals T⁻ᴺ.
-- The difference quotient in (4.2.1.17) has the opposite derivative sign.

/-- Paper: Lemma 4.2.1.5(3), p. 165. The Mellin evaluations form an unconditional
Schauder basis on the strong quotient dual. Lemma 4.2.1.3 identifies this dual
with the annihilator with its inherited strong topology. -/
theorem cyclicQuotientMellinCoeff_unconditionalBasis :
    let δ := cyclicQuotientMellinCoeff γ hγ ∘ freq
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ Q),
      IsSchauderBasis δ c ∧ SchauderBasis.IsUnconditional δ c := by sorry

/-- Paper: Remark 4.2.1.6, p. 165. Every bounded subset of a Hausdorff
quotient of the exponential decay space has a bounded lift. -/
theorem positiveRealExponentialDecay_liftsBoundedSets (M : Submodule ℂ E)
    (hM : IsClosed (M : Set E)) : LiftsBoundedSets M.mkQL := by sorry

end Kernel

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient basis of the
strong dual is absolute, with coordinates given by evaluation on the monomials. -/
theorem cyclicFourierCoeff_absolute :
    SchauderBasis.IsAbsolute (cyclicFourierCoeff ∘ freq)
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (cyclicExponential (freq n))) := by sorry

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient functionals
are bounded in the strong dual. -/
theorem cyclicFourierCoeff_bounded :
    IsVonNBounded ℂ (range cyclicFourierCoeff) := by sorry

/-- Paper: Corollary 4.2.1.7, p. 169. The Fourier coefficient functionals are
equicontinuous as maps on the circle Schwartz space. -/
theorem cyclicFourierCoeff_equicontinuous :
    Equicontinuous (fun m : ℤ ↦ (cyclicFourierCoeff m : S → ℂ)) := by sorry

-- TODO(paper-gap): The proof on p. 169 gives the positive Mellin frequency
-- and drops the Haar normalization factor. Formula (4.2.1.5) fixes both.

/-- Paper: Remark 4.2.1.8, p. 170. Periodization identifies the exponential-decay
quotient with the smooth circle Schwartz space.
Deviation: The source is the quotient by the kernel of the periodization. -/
theorem cyclicPeriodization_quotient_equiv (γ : ℝ) (hγ : 1 < γ) :
    let P := cyclicPeriodizationCLM γ hγ
    ∃ e : (E ⧸ P.ker) ≃L[ℂ] S, ∀ f : E, e (P.ker.mkQL f) = P f := by sorry

/-- Paper: Remark 4.2.1.8, p. 170. The exponential system is regular in
the smooth topology. -/
theorem cyclicExponential_regular :
    SchauderBasis.IsRegular (cyclicExponential ∘ freq) := by sorry

/-- Paper: Remark 4.2.1.8, p. 170. The exponential system is unbounded
in the smooth topology. -/
theorem cyclicExponential_not_bounded :
    ¬ IsVonNBounded ℂ (range cyclicExponential) := by sorry

section CompactSupport

local notation "D[" K "]" => 𝓓_{K}(ℝ, ℂ)
local notation "symmInterval[" a ", " b "]" =>
  Compacts.mk (Icc (Real.log b - Real.log a) (Real.log b + Real.log a)) isCompact_Icc

/-- Paper: §4.2.2, p. 170. A smooth logarithmic profile supported in a fixed
compact set satisfies all exponential Schwartz weights. -/
theorem compactLogProfile_mem (K : Compacts ℝ) (f : D[K]) :
    (f : ℝ → ℂ) ∈ logExponentialDecaySubmodule univ := by
  exact mem_logExponentialDecaySubmodule_of_hasCompactSupport univ f.hasCompactSupport f.contDiff

/-- Paper: §4.2.2, p. 170. Including profiles supported in a fixed compact set
into the exponential decay space is continuous for the uniform derivative topology. -/
theorem compactLogProfile_continuous (K : Compacts ℝ) :
    Continuous (Y := E) (fun f : D[K] ↦ ⟨(f : ℝ → ℂ), compactLogProfile_mem K f⟩) := by sorry

/-- Paper: §4.2.2, p. 170. The inclusion of the fixed-support test space
takes the same function as an exponentially decaying profile.
Deviation: The support set is the logarithmic image of the paper's K. -/
def compactLogProfileInclusion (K : Compacts ℝ) : D[K] →L[ℂ] E where
  toFun f := ⟨(f : ℝ → ℂ), compactLogProfile_mem K f⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := compactLogProfile_continuous K

/-- Paper: §4.2.2, p. 170. A decay profile lies in the image of the test
space precisely when its topological support is contained in the designated compact set. -/
theorem compactLogProfileInclusion_range (K : Compacts ℝ) (f : E) :
    f ∈ range (compactLogProfileInclusion K) ↔ tsupport f.val ⊆ (K : Set ℝ) := by sorry

/-- Paper: Theorem 4.2.2.1, p. 170. An entire function is a Fourier integral
of an L² function supported on the indicated interval exactly when it has
the stated exponential type and an L² trace on the real line. -/
theorem paleyWiener_compactInterval (A : ℝ) (hA : 0 < A) (f : ℂ → ℂ)
    (hf : Differentiable ℂ f) :
    (∃ F : ℝ → ℂ, MemLp F 2 (volume.restrict (Ioo (-A) A)) ∧
      ∀ z, f z = ∫ x in Ioo (-A) A, F x * Complex.exp (Complex.I * (x : ℂ) * z)) ↔
    ((∃ C : ℝ, 0 < C ∧ ∀ z, ‖f z‖ ≤ C * Real.exp (A * ‖z‖)) ∧
      MemLp (fun x : ℝ ↦ f x) 2 volume) := by sorry

-- TODO(paper-gap): The multiplicative restatement following 4.2.2.1
-- uses A directly as an interval endpoint. The endpoint for type A is exp A.

variable (γ : ℝ) (hγ : 1 < γ)

local notation "Φ[" K "]" =>
  ContinuousLinearMap.comp (cyclicPeriodizationCLM γ hγ) (compactLogProfileInclusion K)

-- TODO(paper-gap): Proposition 4.2.2.2(1) asserts surjectivity for all compact K
-- mapping onto the quotient. For K = [1, γ], the class of 1 has only endpoint
-- representatives in K, where every smooth test function supported in K vanishes.

include hγ in
/-- Paper: Proposition 4.2.2.2(1), p. 171. The closed multiplicative interval
of radius a about b covers the quotient when its logarithmic length exceeds log γ.
Deviation: The interval and quotient map are in logarithmic coordinates. -/
theorem cyclicQuotient_surjOn_interval (a b : ℝ) (ha : 1 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    SurjOn (fun x : ℝ ↦ ((x / Real.log γ : ℝ) : T))
      (symmInterval[a, b] : Set ℝ) univ := by
  intro z _
  let L := Real.log γ
  let A := Real.log (b / a)
  have hL : 0 < L := Real.log_pos hγ
  have hA : A = Real.log b - Real.log a := Real.log_div hb.ne' (lt_trans zero_lt_one ha).ne'
  let r := (AddCircle.equivIco (1 : ℝ) (A / L)) z
  have hr : (r : ℝ) ∈ Ico (A / L) (A / L + 1) := r.property
  refine ⟨(r : ℝ) * L, ⟨?_, ?_⟩, ?_⟩
  · rw [← hA]
    exact (div_le_iff₀ hL).mp hr.1
  · have hu := mul_lt_mul_of_pos_right hr.2 hL
    rw [add_mul, div_mul_cancel₀ _ hL.ne', one_mul] at hu
    change _ ≤ Real.log b + Real.log a
    dsimp only [L] at hu
    linarith [hA]
  · change ((↑((r : ℝ) * L / L) : T)) = z
    rw [mul_div_cancel_right₀ _ hL.ne']
    exact AddCircle.coe_equivIco

/-- Paper: Proposition 4.2.2.2(1), p. 171. Periodization gives a continuous
linear isomorphism from the fixed-support interval quotient to the smooth circle space.
Deviation: This states the strict-width interval case treated on p. 172. -/
theorem compactIntervalPeriodization_quotient_equiv (a b : ℝ) (ha : 1 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    ∃ e : (D[K] ⧸ P.ker) ≃L[ℂ] S, ∀ f : D[K], e (P.ker.mkQL f) = P f := by sorry

-- TODO(paper-gap): Proposition 4.2.2.2(2) with a = γ, b = 1, and A₀ = γ
-- forces ψ to be supported in {1}. For a nonzero smooth bump u supported
-- in (1, γ), the function x ↦ u(x) - u(γx) is nonzero and in the stated kernel.

include hγ in
/-- Paper: Remark 4.2.2.3, p. 171. A compact set containing a slightly
enlarged translated fundamental interval covers the quotient. -/
theorem cyclicQuotient_surjOn_of_contains (K : Compacts ℝ) (n : ℤ) (hn : 1 ≤ n)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hK : Icc (n * Real.log γ + Real.log (1 - ε))
      (n * Real.log γ + Real.log (γ + ε)) ⊆ (K : Set ℝ)) :
    SurjOn (fun x : ℝ ↦ ((x / Real.log γ : ℝ) : T)) (K : Set ℝ) univ := by sorry

/-- Paper: Lemma 4.2.2.4, p. 171. The test space with support in a given
compact set is a closed subspace of the exponential decay space. -/
theorem compactLogProfileInclusion_closed (K : Compacts ℝ)
    (hK : (interior (K : Set ℝ)).Nonempty) :
    IsClosed (range (compactLogProfileInclusion K)) := by sorry

/-- Paper: Lemma 4.2.2.4, p. 171. The test space's uniform derivative topology
agrees with the topology inherited from the exponential decay space. -/
theorem compactLogProfileInclusion_isEmbedding (K : Compacts ℝ)
    (hK : (interior (K : Set ℝ)).Nonempty) :
    IsEmbedding (compactLogProfileInclusion K) := by sorry

/-- Paper: Proposition 4.2.2.5(1), p. 173. The Mellin evaluation sequence
is an absolute Schauder basis of the strong quotient dual. This dual is
identified with the annihilator by Lemma 4.2.1.3. -/
theorem cyclicQuotientMellinCoeff_absoluteBasis :
    let δ := cyclicQuotientMellinCoeff γ hγ ∘ freq
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (E ⧸ (cyclicPeriodizationCLM γ hγ).ker)),
      IsSchauderBasis δ c ∧ SchauderBasis.IsAbsolute δ c := by sorry

/-- Paper: Proposition 4.2.2.5(2), p. 173. For an interval wider than a
fundamental interval, all monomials have lifts supported in that same interval,
whose classes are an absolute Schauder basis for the fixed-support quotient. -/
theorem compactIntervalPeriodization_absoluteBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    ∃ u : ℤ → D[K], (∀ m, P (u m) = cyclicExponential m) ∧
      let basis := P.ker.mkQL ∘ u ∘ freq
      let coeff := fun n ↦ (cyclicFourierCoeff (freq n)).comp (P.ker.liftQL P le_rfl)
      IsSchauderBasis basis coeff ∧ SchauderBasis.IsAbsolute basis coeff := by sorry

/-- Paper: Proposition 4.2.2.5(2), p. 173. Descending the restricted Mellin
evaluations gives an absolute Schauder basis of the strong fixed-support quotient dual. -/
theorem compactIntervalPeriodization_dual_absoluteBasis (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hwide : Real.log γ < 2 * Real.log a) :
    let K := symmInterval[a, b]
    let P := Φ[K]
    let δ := fun n ↦ (Real.log γ : ℂ) •
      (cyclicFourierCoeff (freq n)).comp (P.ker.liftQL P le_rfl)
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (D[K] ⧸ P.ker)),
      IsSchauderBasis δ c ∧ SchauderBasis.IsAbsolute δ c := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. Periodization on ordinary Schwartz
profiles has a continuous linear right inverse. -/
theorem cyclicSchwartzPeriodization_hasSection :
    ∃ s : S →L[ℂ] 𝓢(ℝ, ℂ), Function.RightInverse s (cyclicSchwartzPeriodization γ hγ) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. Periodization on exponential Schwartz
profiles has a continuous linear right inverse. -/
theorem cyclicPeriodization_hasSection :
    ∃ s : S →L[ℂ] E, Function.RightInverse s (cyclicPeriodizationCLM γ hγ) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. The circle Schwartz space is topologically
and linearly isomorphic to the space of rapidly decreasing integer sequences. -/
theorem cyclicSchwartz_equiv_rapidDecay :
    Nonempty (S ≃L[ℂ] RapidDecaySequence 1) := by sorry

/-- Paper: Remark 4.2.2.6, p. 173. The real Schwartz space is topologically
and linearly isomorphic to the space of rapidly decreasing sequences. -/
theorem realSchwartz_equiv_rapidDecay :
    Nonempty (𝓢(ℝ, ℂ) ≃L[ℂ] RapidDecaySequence 1) := by sorry

/-- Paper: Remark 4.2.2.6, p. 174. The kernel of periodization of ordinary
Schwartz functions is topologically and linearly isomorphic to the source. -/
theorem cyclicSchwartzPeriodization_ker_equiv :
    Nonempty ((cyclicSchwartzPeriodization γ hγ).ker ≃L[ℂ] 𝓢(ℝ, ℂ)) := by sorry

/-- Paper: Remark 4.2.2.6, p. 174. The product of two rapid-decay sequence
spaces is topologically and linearly isomorphic to one such space. -/
theorem rapidDecaySequence_prod_equiv :
    Nonempty ((RapidDecaySequence 1 × RapidDecaySequence 1) ≃L[ℂ] RapidDecaySequence 1) := by sorry

end CompactSupport

end RiemannMasullo
