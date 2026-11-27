module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec4
public import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.Ch02_AdelicTheta.Sec3
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # The order-zero S-local theta Fourier cutoff

The Hilbert Fourier isometry transports a quotient multiplier to the completed
theta space. The resulting bounded map agrees with the scalar Fourier cutoff on
each compact Fourier test on which the quotient multiplier formula holds.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "J" => SIdeleQuotient F S
local notation "H" => SLocalThetaL2 F S
local notation "Tests" => SchwartzBruhat (Multiplicative (SAdeleRing F S))

local instance : MeasurableSpace J := borel _

local instance : T2Space J :=
  letI := isClosed_sProjectedDiagonal (F := F) (S := S)
  inferInstance

local instance : BorelSpace J := ⟨rfl⟩

local instance : LocallyCompactSpace J :=
  letI : LocallyCompactSpace (SAdeleRing F S)ˣ := (sIdeleGroup_description F S).2.2.1
  inferInstanceAs (LocallyCompactSpace ((SAdeleRing F S)ˣ ⧸ sProjectedDiagonal F S))

set_option maxSynthPendingDepth 8 in
local instance : SecondCountableTopology J :=
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let (v : S) : SecondCountableTopology (v.val.adicCompletion F) := secondCountable_of_proper
  let (w : InfinitePlace F) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (InfiniteAdeleRing F) :=
    inferInstanceAs (SecondCountableTopology ((w : InfinitePlace F) → w.Completion))
  let : SecondCountableTopology ((v : S) → v.val.adicCompletion F) := inferInstance
  let : SecondCountableTopology (SAdeleRing F S) :=
    inferInstanceAs (SecondCountableTopology
      (InfiniteAdeleRing F × ((v : S) → v.val.adicCompletion F)))
  let : SecondCountableTopology (SAdeleRing F S)ˣ :=
    (sIdeleGroup_description F S).1.secondCountableTopology
  inferInstanceAs (SecondCountableTopology ((SAdeleRing F S)ˣ ⧸ sProjectedDiagonal F S))

local notation "νθ" => (sLocalQuotientTamagawaMeasure F S).withDensity
  (fun x : J ↦ ENNReal.ofReal ((sIdeleQuotientNorm F S x).val : ℝ))
local notation "Uθ" =>
  (existsUnique_sLocalThetaL2Fourier (F := F) (S := S)).exists.choose
local notation "iθ" => (SLocalThetaL2.inclusion (F := F) (S := S))
local notation "FT" => sAdeleSchwartzFourier (F := F) (S := S)
local notation "gen(" f ")" =>
  SLocalThetaL2.completionMap F S (Submodule.Quotient.mk (f : Tests))

/-- Paper: (12.4.1.8), p. 517. Compress a quotient multiplier to the actual theta Hilbert space and
conjugate it by the unitary Fourier transform. -/
def sLocalThetaL2FourierCutoff (ρ : J → ℝ) (hm : Measurable ρ) (hb : ∀ x, |ρ x| ≤ 1) :
    H →L[ℂ] H :=
  (Uθ).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((iθ).toContinuousLinearMap.adjoint.comp
      ((lpCutoffMultiplier νθ ρ hm hb).comp
        ((iθ).toContinuousLinearMap.comp (Uθ).toLinearIsometry.toContinuousLinearMap)))

/-- A quotient multiplier bounded by one gives a contraction at order zero. -/
theorem norm_sLocalThetaL2FourierCutoff_le_one
    (ρ : J → ℝ) (hm : Measurable ρ) (hb : ∀ x, |ρ x| ≤ 1) :
    ‖sLocalThetaL2FourierCutoff ρ hm hb‖ ≤ 1 := by
  let M := lpCutoffMultiplier νθ ρ hm hb
  let A := (iθ).toContinuousLinearMap.adjoint
  have hM : ‖M‖ ≤ 1 := (exists_lpCutoffMultiplier νθ ρ hm hb).choose_spec.1
  have hA : ‖A‖ ≤ 1 := by
    change ‖(iθ).toContinuousLinearMap.adjoint‖ ≤ 1
    rw [ContinuousLinearMap.adjoint.norm_map]
    exact (iθ).norm_toContinuousLinearMap_le
  apply (sLocalThetaL2FourierCutoff ρ hm hb).opNorm_le_bound zero_le_one
  intro u
  change ‖(Uθ).symm (A (M (iθ (Uθ u))))‖ ≤ 1 * ‖u‖
  rw [(Uθ).symm.norm_map, one_mul]
  calc
    _ ≤ ‖A‖ * ‖M (iθ (Uθ u))‖ := A.le_opNorm _
    _ ≤ ‖M (iθ (Uθ u))‖ := mul_le_of_le_one_left (norm_nonneg _) hA
    _ ≤ ‖M‖ * ‖iθ (Uθ u)‖ := M.le_opNorm _
    _ ≤ ‖iθ (Uθ u)‖ := mul_le_of_le_one_left (norm_nonneg _) hM
    _ = ‖u‖ := by rw [(iθ).norm_map, (Uθ).norm_map]

private theorem sLocalThetaL2FourierCutoff_test_inclusion_ae (f : Tests) :
    (iθ (gen(f)) : J → ℂ) =ᵐ[νθ] sLocalAdelicThetaOnClasses F S f := by
  rw [SLocalThetaL2.inclusion_completionMap]
  exact (existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose_spec.2 f

private theorem sLocalThetaL2Cutoff_mul_test
    (ρ : J → ℝ) (hm : Measurable ρ) (hb : ∀ x, |ρ x| ≤ 1) (f g : Tests)
    (hθ : ∀ x, sLocalAdelicThetaOnClasses F S g x =
      (ρ x : ℂ) * sLocalAdelicThetaOnClasses F S f x) :
    lpCutoffMultiplier νθ ρ hm hb (iθ (gen(f))) = iθ (gen(g)) := by
  apply Lp.ext
  filter_upwards [lpCutoffMultiplier_apply νθ ρ hm hb (iθ (gen(f))),
    sLocalThetaL2FourierCutoff_test_inclusion_ae f,
    sLocalThetaL2FourierCutoff_test_inclusion_ae g] with x hm' hf hg
  exact hm'.trans ((congrArg (fun z : ℂ ↦ (ρ x : ℂ) * z) hf).trans
    ((hθ x).symm.trans hg.symm))

private theorem adjoint_apply_isometry {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
    (i : E →ₗᵢ[ℂ] G) (u : E) :
    i.toContinuousLinearMap.adjoint (i u) = u := by
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self,
    LinearIsometry.coe_toContinuousLinearMap] using DFunLike.congr_fun i.adjoint_comp_self u

/-- Paper: (12.4.1.8), p. 517. The bounded cutoff agrees with every realized
Schwartz–Bruhat cutoff on its theta class when the Fourier theta functions
differ by the indicated quotient multiplier. -/
theorem sLocalThetaL2FourierCutoff_generator_of_theta
    (ρ : J → ℝ) (hm : Measurable ρ) (hb : ∀ x, |ρ x| ≤ 1) (f g : Tests)
    (hθ : ∀ x, sLocalAdelicThetaOnClasses F S (FT g) x =
      (ρ x : ℂ) * sLocalAdelicThetaOnClasses F S (FT f) x) :
    sLocalThetaL2FourierCutoff ρ hm hb (gen(f)) = gen(g) := by
  let U := Uθ
  let i := iθ
  let M := lpCutoffMultiplier νθ ρ hm hb
  let u := gen(f)
  let v := gen(g)
  have hU (w : Tests) : U (gen(w)) = gen(FT w) :=
    (existsUnique_sLocalThetaL2Fourier (F := F) (S := S)).exists.choose_spec w
  have hM : M (i (U u)) = i (U v) := by
    change M (i (U (gen(f)))) = i (U (gen(g)))
    rw [hU f, hU g]
    exact sLocalThetaL2Cutoff_mul_test ρ hm hb (FT f) (FT g) hθ
  calc
    sLocalThetaL2FourierCutoff ρ hm hb (gen(f)) =
        U.symm (i.toContinuousLinearMap.adjoint (M (i (U u)))) := rfl
    _ = U.symm (i.toContinuousLinearMap.adjoint (i (U v))) :=
      congrArg (fun z ↦ U.symm (i.toContinuousLinearMap.adjoint z)) hM
    _ = U.symm (U v) := congrArg U.symm (adjoint_apply_isometry i (U v))
    _ = gen(g) := U.symm_apply_apply v

local notation "Kₛ" => LinearMap.ker (sLocalAdelicTheta F S)

private theorem continuous_sLocalThetaL2_testImage :
    Continuous (fun f : Tests ↦ gen(f)) := by
  let i := SLocalThetaL2.inclusion (F := F) (S := S)
  let j := (existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose
  apply i.isometry.isEmbedding.continuous_iff.mpr
  change Continuous (fun f : Tests ↦ i (gen(f)))
  have h (f : Tests) : i (gen(f)) = j ((Kₛ).mkQL f) :=
    SLocalThetaL2.inclusion_completionMap (Submodule.Quotient.mk f)
  simp_rw [h]
  exact j.continuous.comp (Kₛ).mkQL.continuous

/-- The images of compactly supported S-adelic Schwartz–Bruhat tests are dense
in the weighted theta completion at half density and order zero. -/
private theorem sLocalThetaL2_dense_compactSupport :
    Dense {x : SLocalThetaL2 F S | ∃ f : Tests, HasCompactSupport f.val ∧ gen(f) = x} := by
  have hrange : DenseRange (fun f : Tests ↦ gen(f)) := by
    refine (sLocalThetaL2_dense (F := F) (S := S)).mono ?_
    rintro _ ⟨x, rfl⟩
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective (p := Kₛ) x
    exact ⟨f, rfl⟩
  change Dense ((fun f : Tests ↦ gen(f)) '' {f : Tests | HasCompactSupport f.val})
  apply hrange.dense_image continuous_sLocalThetaL2_testImage
  intro f
  obtain ⟨u, hu, ht⟩ := exists_sAdeleSchwartz_compact_support_seq f
  exact mem_closure_of_tendsto ht (.of_forall hu)

private theorem sLocalThetaL2_compactCore_fourier_four (f : Tests) :
    FT (FT (FT (FT f))) = f := by
  apply Subtype.ext
  funext x
  exact (sLocal_fourier_inversion (FT (FT f)) x.toAdd).trans
    ((sLocal_fourier_inversion f (-x.toAdd)).trans
      (congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (neg_neg x.toAdd)))

/-- The images of tests with compactly supported additive Fourier transforms
are dense in the weighted theta completion. The inverse unitary theta Fourier
map carries the compactly supported test images to these images. -/
theorem sLocalThetaL2_dense_compactFourierSupport :
    Dense {x : SLocalThetaL2 F S |
      ∃ f : Tests, HasCompactSupport (FT f).val ∧ gen(f) = x} := by
  obtain ⟨e, he, -⟩ := existsUnique_sLocalThetaL2Fourier (F := F) (S := S)
  have hd := e.symm.surjective.denseRange.dense_image e.symm.continuous
    (sLocalThetaL2_dense_compactSupport (F := F) (S := S))
  refine hd.mono ?_
  rintro _ ⟨x, ⟨f, hf, rfl⟩, rfl⟩
  let g := FT (FT (FT f))
  have hg : FT g = f := sLocalThetaL2_compactCore_fourier_four f
  refine ⟨g, hg.symm ▸ hf, ?_⟩
  apply e.injective
  rw [he g, hg, e.apply_symm_apply]

end RiemannMasullo
