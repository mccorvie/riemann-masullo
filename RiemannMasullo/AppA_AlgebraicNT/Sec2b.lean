module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.SpecialFunctions.Complex.Arg
public import Mathlib.Geometry.Manifold.Instances.UnitsOfNormedAlgebra
public import Mathlib.Geometry.Manifold.Submersion
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import all Mathlib.Geometry.Manifold.Submersion
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.PolarCoord
import Mathlib.Topology.Algebra.Group.Units
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Logarithmic coordinates and idelic fundamental domains

Appendix A.2.3–A.2.4 of Masullo. For lattice calculations we use Mathlib's coordinates
on the trace-zero hyperplane, which omit one place. The omitted coordinate is minus
the sum of the others. All interiors and closures are taken in the indicated groups.
-/

@[expose] public section

noncomputable section

-- Integer module instances on the additive versions of quotient unit groups.
set_option maxSynthPendingDepth 8

namespace RiemannMasullo

open Function NumberField IsDedekindDomain Topology
open NumberField.Units.dirichletUnitTheorem InfinitePlace.Completion
open scoped Classical NNReal Pointwise ContDiff Manifold RestrictedProduct

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "𝓤" => Additive ((𝓞 F)ˣ ⧸ Units.torsion F)
local notation "unitAtInfinity" => Units.map (RingHom.toMonoidHom
  (RingHom.comp (algebraMap F (InfiniteAdeleRing F)) (algebraMap (𝓞 F) F)))
local notation "atInfinity" =>
  Units.map (RingHom.toMonoidHom (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
local notation "fromInfinity" =>
  (Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

/-- Paper: Definition A.2.3.1, p. 548. The archimedean norm multiplies the local
absolute values with exponent one at real places and two at complex places. Its
kernel is the group of norm-one archimedean ideles. -/
def infiniteIdeleNorm : 𝕀∞ →* ℝ≥0ˣ :=
  ∏ v : InfinitePlace F, ((Units.map nnNormHom.toMonoidHom).comp
    (Units.map (Pi.evalRingHom _ v).toMonoidHom)) ^ v.mult

local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)
local notation "N₁" => MonoidHom.ker (ideleNorm F)

/-- Paper: Definition A.2.3.1, p. 548. Giving an archimedean idele finite components
equal to one preserves its norm. -/
theorem infiniteIdeleNorm_eq_global (g : 𝕀∞) :
    infiniteIdeleNorm F g = ideleNorm F (fromInfinity g) := by
  apply Units.ext
  apply NNReal.coe_injective
  rw [((ideleNorm_spec F).1 (fromInfinity g)).2]
  have hfin (v : Primes(F)) : (fromInfinity g).val.2 v = 1 := rfl
  simp only [hfin, norm_one, finprod_one, mul_one]
  simp [infiniteIdeleNorm, Units.coe_prod]
  rfl

/-- Paper: Definition A.2.3.1, p. 548. The archimedean norm is continuous. -/
theorem infiniteIdeleNorm_continuous : Continuous (infiniteIdeleNorm F) := by
  apply Continuous.of_coeHom_comp
  change Continuous (fun g : 𝕀∞ ↦ (infiniteIdeleNorm F g).val)
  simp only [infiniteIdeleNorm, MonoidHom.finsetProd_apply, Units.coe_prod, MonoidHom.pow_apply]
  exact continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp Units.continuous_val).nnNorm.pow _

/-- Paper: Definition A.2.3.1, p. 548. The norm-one archimedean ideles form a closed subgroup. -/
theorem infiniteIdeleNorm_ker_closed : IsClosed (N∞ : Set 𝕀∞) := by
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage (infiniteIdeleNorm_continuous F)

/-- Paper: Definition A.2.3.1, p. 548. The full logarithm records the logarithm of
the normalized absolute value at every archimedean place. -/
def infiniteIdeleLog (g : 𝕀∞) (v : InfinitePlace F) : ℝ :=
  v.mult * Real.log ‖g.val v‖

/-- Paper: Definition A.2.3.1, p. 548. Every real tuple is the logarithm of an
archimedean idele. -/
theorem infiniteIdeleLog_surjective : Surjective (infiniteIdeleLog F) := by
  intro x
  let r (v : InfinitePlace F) := Real.exp (x v / v.mult)
  have hnorm (v : InfinitePlace F) : ∃ z : v.Completion, ‖z‖ = r v := by
    by_cases hv : v.IsReal
    · obtain ⟨z, hz⟩ := surjective_extensionEmbeddingOfIsReal hv (r v)
      refine ⟨z, ?_⟩
      rw [← (isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) z,
        hz, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    · obtain ⟨z, hz⟩ := surjective_extensionEmbedding_of_isComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hv) (r v : ℂ)
      refine ⟨z, ?_⟩
      rw [← (isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) z,
        hz, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  choose z hz using hnorm
  let g : 𝕀∞ := MulEquiv.piUnits.symm fun v =>
    Units.mk0 (z v) (norm_ne_zero_iff.mp ((hz v).trans_ne (Real.exp_pos _).ne'))
  refine ⟨g, ?_⟩
  funext v
  change (v.mult : ℝ) * Real.log ‖z v‖ = x v
  rw [hz, Real.log_exp, mul_div_cancel₀ _ InfinitePlace.mult_coe_ne_zero]

/-- Paper: Lemma A.2.3.2(1), p. 548. The logarithm takes products to sums. -/
theorem infiniteIdeleLog_mul (g h : 𝕀∞) :
    infiniteIdeleLog F (g * h) = infiniteIdeleLog F g + infiniteIdeleLog F h := by
  have hne (u : 𝕀∞) (v : InfinitePlace F) : u.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom u).ne_zero
  funext v
  change (v.mult : ℝ) * Real.log ‖(g.val * h.val) v‖ =
    v.mult * Real.log ‖g.val v‖ + v.mult * Real.log ‖h.val v‖
  rw [← mul_add, ← Real.log_mul (norm_ne_zero_iff.mpr (hne g v)) (norm_ne_zero_iff.mpr (hne h v)),
    ← norm_mul]
  rfl

/-- Paper: Lemma A.2.3.2(1), p. 548. The full logarithm is continuous. -/
theorem infiniteIdeleLog_continuous : Continuous (infiniteIdeleLog F) := by
  apply continuous_pi
  intro v
  have hne (g : 𝕀∞) : g.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom g).ne_zero
  exact continuous_const.mul (((continuous_apply v).comp Units.continuous_val).norm.log
    (fun g ↦ norm_ne_zero_iff.mpr (hne g)))

/-- Paper: Lemma A.2.3.2(1), p. 548. The coordinates of the logarithm of a norm-one
idele sum to zero, the defining equation of the logarithmic hyperplane. -/
theorem infiniteIdeleLog_sum_zero (g : N∞) : ∑ v, infiniteIdeleLog F g.val v = 0 := by
  have hne (v : InfinitePlace F) : g.val.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom g.val).ne_zero
  have hprod := congrArg (fun u : ℝ≥0ˣ ↦ ((u : ℝ≥0) : ℝ))
    (show infiniteIdeleNorm F g.val = 1 from g.property)
  simp [infiniteIdeleNorm, Units.coe_prod] at hprod
  change ∏ v : InfinitePlace F, ‖g.val.val v‖ ^ v.mult = 1 at hprod
  have hlog := congrArg Real.log hprod
  rw [Real.log_prod (fun v _ ↦ pow_ne_zero v.mult (norm_ne_zero_iff.mpr (hne v)))] at hlog
  simpa only [infiniteIdeleLog, Real.log_pow, Real.log_one] using hlog

local notation "mixedUnits" => Units.mapEquiv (RingEquiv.toMulEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace F))

section Submersion

local notation "E" => mixedEmbedding.mixedSpace F
local notation "V" => InfinitePlace F → ℝ
local notation "C" => {w : InfinitePlace F // InfinitePlace.IsComplex w} → ℝ

omit [NumberField F] in
/-- The local absolute value of an idele agrees with the norm in mixed coordinates. -/
private theorem infiniteIdeleLog_eq_mixed (g : Eˣ) (v : InfinitePlace F) :
    infiniteIdeleLog F ((mixedUnits).symm g) v =
      v.mult * Real.log (mixedEmbedding.normAtPlace v g.val) := by
  let a := (mixedUnits).symm g
  have ha : InfiniteAdeleRing.ringEquiv_mixedSpace F a.val = g.val :=
    congrArg Units.val ((mixedUnits).apply_symm_apply g)
  rw [← ha]
  unfold infiniteIdeleLog
  congr 2
  by_cases hv : v.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hv]
    exact ((isometry_extensionEmbeddingOfIsReal hv).norm_map_of_map_zero (map_zero _) (a.val v)).symm
  · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
    rw [mixedEmbedding.normAtPlace_apply_of_isComplex hv']
    exact ((isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) (a.val v)).symm

/-- Paper: Lemma A.2.3.2(2), p. 548. In the real and complex completion coordinates the
full logarithm is a smooth submersion of real manifolds. -/
theorem infiniteIdeleLog_submersion :
    Manifold.IsSubmersion 𝓘(ℝ, mixedEmbedding.mixedSpace F) 𝓘(ℝ, InfinitePlace F → ℝ) ∞
      (fun g : (mixedEmbedding.mixedSpace F)ˣ ↦ infiniteIdeleLog F ((mixedUnits).symm g)) := by
  let f : Eˣ → V := fun g ↦ infiniteIdeleLog F ((mixedUnits).symm g)
  -- Split the real and imaginary coordinates, weighting only the log coordinates.
  let h := (mixedEmbedding.mixedSpaceToRealMixedSpace F).trans
    (mixedEmbedding.homeoRealMixedSpacePolarSpace F)
  have hfst (z : E) (v : InfinitePlace F) :
      (h z).1 v = if hv : v.IsReal then z.1 ⟨v, hv⟩
        else (z.2 ⟨v, InfinitePlace.not_isReal_iff_isComplex.mp hv⟩).re := by
    rw [show h z = mixedEmbedding.homeoRealMixedSpacePolarSpace F
      (mixedEmbedding.mixedSpaceToRealMixedSpace F z) from rfl,
      mixedEmbedding.homeoRealMixedSpacePolarSpace_apply]
    rfl
  have hsnd (z : E) (v : {w : InfinitePlace F // w.IsComplex}) : (h z).2 v = (z.2 v).im := by
    rfl
  let e₀ : E ≃ₗ[ℝ] V × C :=
    { h.toEquiv with
      map_add' := by
        intro z w
        apply Prod.ext <;> funext v
        · change (h (z + w)).1 v = (h z).1 v + (h w).1 v
          simp only [hfst]
          split_ifs <;> simp
        · change (h (z + w)).2 v = (h z).2 v + (h w).2 v
          simp [hsnd]
      map_smul' := by
        intro r z
        apply Prod.ext <;> funext v
        · change (h (r • z)).1 v = r * (h z).1 v
          simp only [hfst]
          split_ifs <;> simp
        · change (h (r • z)).2 v = r * (h z).2 v
          simp [hsnd] }
  let multEquiv : V ≃L[ℝ] V :=
    ContinuousLinearEquiv.piCongrRight fun v ↦
      ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 (v.mult : ℝ) InfinitePlace.mult_coe_ne_zero)
  let e : E ≃L[ℝ] V × C :=
    e₀.toContinuousLinearEquiv.trans (multEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ C))
  have he (z : E) (v : InfinitePlace F) : (e z).1 v = (h z).1 v * v.mult := rfl
  -- The real and complex logarithms are smooth charts on neighborhoods of one.
  let logChart : OpenPartialHomeomorph E E :=
    (OpenPartialHomeomorph.pi fun _ ↦ Real.expPartialHomeomorph.symm).prod
      (OpenPartialHomeomorph.pi fun _ ↦ Complex.expOpenPartialHomeomorph.symm)
  have hlogSource (z : E) (hz : z ∈ logChart.source) :
      (∀ v, 0 < z.1 v) ∧ (∀ v, z.2 v ∈ Complex.slitPlane) :=
    ⟨fun v ↦ hz.1 v trivial, fun v ↦ hz.2 v trivial⟩
  have hlogSmooth : ContDiffOn ℝ ∞ logChart logChart.source := by
    change ContDiffOn ℝ ∞ (fun z : E ↦ (fun v ↦ Real.log (z.1 v),
      fun v ↦ Complex.log (z.2 v))) logChart.source
    refine (contDiffOn_pi.mpr fun v ↦ ?_).prodMk (contDiffOn_pi.mpr fun v ↦ ?_)
    · intro z hz
      apply ContDiffAt.contDiffWithinAt
      exact (show ContDiffAt ℝ ∞ (fun z : E ↦ z.1 v) z by fun_prop).log
        ((hlogSource z hz).1 v).ne'
    · intro z hz
      apply ContDiffAt.contDiffWithinAt
      exact ((Complex.contDiffAt_log ((hlogSource z hz).2 v)).restrict_scalars ℝ).comp z
        (show ContDiffAt ℝ ∞ (fun z : E ↦ z.2 v) z by fun_prop)
  have hexpSmooth : ContDiff ℝ ∞ logChart.symm := by
    change ContDiff ℝ ∞ (fun z : E ↦ (fun v ↦ Real.exp (z.1 v),
      fun v ↦ Complex.exp (z.2 v)))
    fun_prop
  apply Manifold.IsSubmersionOfComplement.isSubmersion (F := C)
  intro g
  -- Translate the source to one and the target to zero.
  let a := chartAt E g
  let m := (ContinuousAddEquiv.mulLeft g⁻¹).toHomeomorph.toOpenPartialHomeomorph
  let φ := a.trans (m.trans logChart)
  let ψ := (Homeomorph.addRight (-f g)).toOpenPartialHomeomorph
  have ha : a ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ Eˣ :=
    IsManifold.chart_mem_maximalAtlas g
  have hm : ContDiff ℝ ∞ m := by
    change ContDiff ℝ ∞ (fun z : E ↦ (↑g⁻¹ : E) * z)
    fun_prop
  have hm' : ContDiff ℝ ∞ m.symm := by
    change ContDiff ℝ ∞ (fun z : E ↦ (↑g : E) * z)
    fun_prop
  have hφ : φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ∞ Eˣ := by
    apply φ.mem_maximalAtlas_of_contMDiffOn
    · have hma : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ (m ∘ a) φ.source :=
        hm.contMDiff.comp_contMDiffOn
          ((contMDiffOn_of_mem_maximalAtlas ha).mono fun _ hx ↦ hx.1)
      exact hlogSmooth.contMDiffOn.comp hma fun _ hx ↦ hx.2.2
    · exact (contMDiffOn_symm_of_mem_maximalAtlas ha).comp
        (hm'.contMDiff.comp_contMDiffOn hexpSmooth.contMDiff.contMDiffOn) fun _ hx ↦ hx.2
  have hψ : ψ ∈ IsManifold.maximalAtlas 𝓘(ℝ, V) ∞ V := by
    apply ψ.mem_maximalAtlas_of_contMDiffOn <;> rw [contMDiffOn_iff_contDiffOn]
    · exact (show ContDiff ℝ ∞ (fun z : V ↦ z + -f g) by fun_prop).contDiffOn
    · rw [show (ψ.symm : V → V) = (Homeomorph.addRight (-f g)).symm from rfl,
        Homeomorph.addRight_symm]
      exact (show ContDiff ℝ ∞ (fun z : V ↦ z + - -f g) by fun_prop).contDiffOn
  have hg : g ∈ φ.source := by
    refine ⟨mem_chart_source E g, Set.mem_univ _, ?_⟩
    have hm1 : m (a g) = 1 := g.inv_val
    change m (a g) ∈ logChart.source
    rw [hm1]
    exact ⟨fun _ _ ↦ (zero_lt_one : (0 : ℝ) < 1), fun _ _ ↦ Complex.one_mem_slitPlane⟩
  have hform (u : Eˣ) : ψ (f u) = (e (φ u)).1 := by
    let t := g⁻¹ * u
    have hshift : ψ (f u) = f t := by
      have hmul : f (g * t) = f g + f t := by
        exact (congrArg (infiniteIdeleLog F) (map_mul (mixedUnits).symm g t)).trans
          (infiniteIdeleLog_mul F _ _)
      rw [show g * t = u by simp [t]] at hmul
      change f u + -f g = f t
      rw [hmul]
      abel
    rw [hshift]
    funext v
    change infiniteIdeleLog F ((mixedUnits).symm t) v = _
    rw [infiniteIdeleLog_eq_mixed, he, hfst]
    change _ = (if hv : v.IsReal then Real.log (t.val.1 ⟨v, hv⟩)
      else (Complex.log (t.val.2 ⟨v, InfinitePlace.not_isReal_iff_isComplex.mp hv⟩)).re) * _
    by_cases hv : v.IsReal
    · rw [dite_eq_left hv, mixedEmbedding.normAtPlace_apply_of_isReal hv, Real.norm_eq_abs,
        Real.log_abs, mul_comm]
    · rw [dite_eq_right hv, mixedEmbedding.normAtPlace_apply_of_isComplex
        (InfinitePlace.not_isReal_iff_isComplex.mp hv), Complex.log_re, mul_comm]
  refine Manifold.IsSubmersionAtOfComplement.mk_of_charts e φ ψ hg (Set.mem_univ _)
    hφ hψ (fun _ _ ↦ Set.mem_univ _) ?_
  intro z hz
  have hz' : z ∈ φ.target := by simpa using hz
  change ψ (f (φ.symm z)) = (e z).1
  rw [hform, φ.right_inv hz']

end Submersion

/-- Paper: Lemma A.2.3.2(2), p. 548. The logarithm kernel is the product of the real
sign groups and the complex circles. The equivalence is the identity in the ambient
real and complex coordinates, identifying the embedded Lie groups. -/
theorem infiniteIdeleLog_kernel :
    let L : 𝕀∞ →* Multiplicative (InfinitePlace F → ℝ) :=
      MonoidHom.mk' (fun g ↦ Multiplicative.ofAdd (infiniteIdeleLog F g)) (infiniteIdeleLog_mul F)
    ∃ e : L.ker ≃ₜ* (({v : InfinitePlace F // v.IsReal} → rootsOfUnity 2 ℝ) ×
        ({v : InfinitePlace F // v.IsComplex} → Circle)), ∀ g,
      let z := InfiniteAdeleRing.ringEquiv_mixedSpace F g.val.val
      (∀ v, ((e g).1 v).val.val = z.1 v) ∧ (∀ v, (((e g).2 v : Circle) : ℂ) = z.2 v) := by
  sorry

/-- Paper: Lemma A.2.3.2(3), p. 548. The full logarithm is proper. -/
theorem infiniteIdeleLog_proper : IsProperMap (infiniteIdeleLog F) := by
  sorry

/-- Paper: Definition A.2.3.3, p. 548. Mathlib's logarithmic embedding of units is
the restriction of the full idelic logarithm to diagonal units, in the coordinates
on the sum-zero hyperplane obtained by omitting the distinguished place. -/
theorem regulator_eq_infiniteIdeleLog (u : (𝓞 F)ˣ) (v : {w : InfinitePlace F // w ≠ w₀}) :
    Units.logEmbedding F (Additive.ofMul u) v = infiniteIdeleLog F (unitAtInfinity u) v.val := by
  sorry

/-- Paper: Lemma A.2.3.4(1), p. 548. The regulator image is discrete in the hyperplane. -/
theorem regulator_discrete : IsDiscrete (Set.range (Units.logEmbedding F)) := by
  sorry

/-- Paper: Lemma A.2.3.4(1), p. 548. The regulator image is closed in the hyperplane. -/
theorem regulator_closed : IsClosed (Set.range (Units.logEmbedding F)) := by
  sorry

/-- Paper: Lemma A.2.3.4(1), p. 548. The quotient of the hyperplane by the regulator
image is compact. -/
theorem regulator_cocompact : CompactSpace (logSpace F ⧸ (Units.logEmbedding F).range) := by
  sorry

/-- Paper: Lemma A.2.3.4(2), p. 548. The regulator kernel is exactly the torsion subgroup. -/
theorem regulator_kernel : (Units.logEmbedding F).ker = (Units.torsion F).toAddSubgroup :=
  logEmbedding_ker

/-- Paper: Lemma A.2.3.4(2), p. 548. The torsion units are the roots of unity of
order dividing the number of torsion units. -/
theorem regulator_torsion_roots : Units.torsion F = rootsOfUnity (Units.torsionOrder F) (𝓞 F) :=
  (Units.rootsOfUnity_eq_torsion F).symm

/-- Paper: Lemma A.2.3.4(2), p. 548. The group of torsion units is finite. -/
theorem regulator_torsion_finite : Finite (Units.torsion F) := by
  infer_instance

/-- Paper: Lemma A.2.3.4(2), p. 548. The group of torsion units is cyclic. -/
theorem regulator_torsion_cyclic : IsCyclic (Units.torsion F) := by
  infer_instance

/-- Paper: Lemma A.2.3.4(3), p. 548. The unit group is finitely generated. -/
theorem regulator_units_finitelyGenerated : Group.FG (𝓞 F)ˣ := by
  exact Group.fg_iff_monoid_fg.mpr inferInstance

/-- Paper: Lemma A.2.3.4(3), p. 548. The units modulo torsion have an integral basis
of cardinality the number of infinite places minus one. -/
theorem regulator_units_mod_torsion_basis : Nonempty (Module.Basis (Fin (Units.rank F)) ℤ 𝓤) := by
  exact ⟨Units.basisModTorsion F⟩

variable (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))

/-- Paper: Equation (A.2.3.8), p. 549. Every norm-one archimedean logarithm has unique
real coordinates in the logarithms of the chosen basis of units modulo torsion. -/
theorem regulator_coordinates_unique (g : N∞) :
    ∃! t : Fin (Units.rank F) → ℝ, ∀ w : {w : InfinitePlace F // w ≠ w₀},
      infiniteIdeleLog F g.val w.val = ∑ i, t i * Units.logEmbeddingQuot F (b i) w := by
  sorry

/-- Paper: Equation (A.2.3.9), p. 549. The regulator parallelotope is the half-open
fundamental parallelepiped of the image of the chosen basis of units modulo torsion. -/
def regulatorParallelotope : Set (logSpace F) :=
  ZSpan.fundamentalDomain ((b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F))

/-- Paper: Equations (A.2.3.9)–(A.2.3.10), p. 549. On a basis direction a real
multiple belongs to the regulator parallelotope exactly for coefficients in [0,1). -/
theorem regulatorParallelotope_basis_line (i : Fin (Units.rank F)) (t : ℝ) :
    t • Units.logEmbeddingQuot F (b i) ∈ regulatorParallelotope F b ↔ t ∈ Set.Ico 0 1 := by
  sorry

-- TODO(paper-gap): Lemma A.2.3.5 calls F a hyperplane. Equations (A.2.3.5) and (A.2.3.9)
-- define the hyperplane and parallelotope for the number field F.

/-- Paper: Lemma A.2.3.5(1), p. 549. The closure of the parallelotope in the
logarithmic hyperplane is compact.
Deviation: We take F to be the number field of (A.2.3.5). -/
theorem regulatorParallelotope_precompact : IsCompact (closure (regulatorParallelotope F b)) := by
  sorry

/-- Paper: Lemma A.2.3.5(1), p. 549. The parallelotope has nonempty relative interior. -/
theorem regulatorParallelotope_interior : (interior (regulatorParallelotope F b)).Nonempty := by
  sorry

/-- Paper: Lemma A.2.3.5(2), p. 549. Regulator translates cover the hyperplane. -/
theorem regulatorParallelotope_cover :
    (⋃ x : (Units.logEmbedding F).range, x.val +ᵥ regulatorParallelotope F b) = Set.univ := by
  sorry

/-- Paper: Lemma A.2.3.5(2), p. 549. Every nonzero regulator translate misses the parallelotope. -/
theorem regulatorParallelotope_disjoint (x : (Units.logEmbedding F).range) (hx : x ≠ 0) :
    Disjoint (x.val +ᵥ regulatorParallelotope F b) (regulatorParallelotope F b) := by
  sorry

/-- Paper: Equation (A.2.3.12), p. 549. The natural ideal class of an idele is the
product of its finite local contributions, with the valuation convention of §A.1. -/
def ideleIdealClass (g : 𝕀[F]) : CommRing.Pic (𝓞 F) :=
  ∏ᶠ v : Primes(F), localIdealClass F v (Units.map
    ((RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd _ _)).toMonoidHom g)

/-- Paper: Equation (A.2.3.12), p. 549. Only finitely many local factors in the
idele's ideal class can be nontrivial. -/
theorem ideleIdealClass_finite_support (g : 𝕀[F]) :
    (fun v : Primes(F) ↦ localIdealClass F v (Units.map
      ((RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
        (RingHom.snd _ _)).toMonoidHom g)).HasFiniteMulSupport := by
  sorry

/-- Paper: Equation (A.2.3.12), p. 549. An idele supported at one finite place
has exactly the local ideal class from §A.1. -/
theorem ideleIdealClass_ofAdicCompletion (v : Primes(F)) (x : (v.adicCompletion F)ˣ) :
    ideleIdealClass F (IdeleGroup.ofAdicCompletion (𝓞 F) F v x) = localIdealClass F v x := by
  sorry

/-- Paper: Equation (A.2.3.12), p. 549. Every ideal class has a norm-one representative,
and the representative of the trivial class can be chosen to be one. -/
theorem exists_normOne_class_representatives :
    ∃ r : CommRing.Pic (𝓞 F) → N₁, r 1 = 1 ∧ ∀ c, ideleIdealClass F (r c).val = c := by
  sorry

variable (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)

/-- Paper: Definition A.2.3.6, p. 549. At the chosen place keep the half-open sector
from angle zero to two pi divided by the number of roots of unity. Postcomposition
by a real algebra automorphism of ℂ allows either embedding at a complex place. -/
def inTorsionSector (x : v₀.Completionˣ) : Prop :=
  (σ (extensionEmbedding v₀ x.val)).arg ∈ Set.Ico 0 (2 * Real.pi / Units.torsionOrder F)

/-- Paper: Definition A.2.3.6, p. 549. At a real place the angular condition selects
exactly the positive component. -/
theorem inTorsionSector_real (hv : v₀.IsReal) (x : v₀.Completionˣ) :
    inTorsionSector F v₀ σ x ↔ 0 < extensionEmbeddingOfIsReal hv x.val := by
  sorry

local notation "atPlace" => Units.map (RingHom.toMonoidHom (Pi.evalRingHom InfinitePlace.Completion v₀))
local notation "inLogBox" => fun g : N∞ ↦
  (fun w : {w : InfinitePlace F // w ≠ w₀} ↦ infiniteIdeleLog F (Subtype.val g) (Subtype.val w)) ∈
    regulatorParallelotope F b

/-- Paper: Definition A.2.3.6, p. 549. The archimedean domain consists of norm-one
ideles with logarithm in the parallelotope and chosen coordinate in the torsion sector. -/
def infiniteIdeleFundamentalDomain : Set N∞ :=
  {g | inLogBox g ∧ inTorsionSector F v₀ σ (atPlace g.val)}

/-- Paper: Definition A.2.3.6, p. 549. The only diagonal unit in the archimedean
domain is the identity. -/
theorem unit_mem_infiniteIdeleFundamentalDomain (u : (𝓞 F)ˣ) :
    unitAtInfinity u ∈ (N∞).subtype '' infiniteIdeleFundamentalDomain F b v₀ σ ↔ u = 1 := by
  sorry

variable (r : CommRing.Pic (𝓞 F) → (ideleNorm F).ker)
local notation "E∞" => infiniteIdeleFundamentalDomain F b v₀ σ
local notation "integralUnits" =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F ∅))))

/-- Paper: Definition A.2.3.6, p. 549. The global norm-one domain is the union of
the class representative translates of the archimedean domain times the finite integral units. -/
def ideleFundamentalDomain : Set N₁ :=
  ⋃ c, r c • {g : N₁ | g.val ∈ integralUnits ∧ atInfinity g.val ∈ (N∞).subtype '' E∞}

local notation "E₁" => ideleFundamentalDomain F b v₀ σ r
local notation "principal₁" =>
  MonoidHom.codRestrict (IdeleGroup.unitEmbedding (𝓞 F) F) N₁
    (fun x ↦ And.right (ideleNorm_spec F) (Set.mem_range_self x))

variable (hr₁ : r 1 = 1) (hr : ∀ c, ideleIdealClass F (r c).val = c)

/-- A unit whose logarithm belongs to the regulator parallelotope has zero logarithm. -/
private theorem logEmbedding_eq_zero_of_mem_regulatorParallelotope (u : (𝓞 F)ˣ)
    (hu : Units.logEmbedding F (Additive.ofMul u) ∈ regulatorParallelotope F b) :
    Units.logEmbedding F (Additive.ofMul u) = 0 := by
  let B := b.map (Units.logEmbeddingEquiv F)
  let z := Units.logEmbeddingEquiv F (Additive.ofMul (QuotientGroup.mk u))
  change (z : logSpace F) ∈ ZSpan.fundamentalDomain (B.ofZLatticeBasis ℝ _) at hu
  change (z : logSpace F) = 0
  apply (B.ofZLatticeBasis ℝ _).repr.injective
  ext i
  rw [ZSpan.mem_fundamentalDomain] at hu
  have hi := hu i
  rw [B.ofZLatticeBasis_repr_apply ℝ _ z i] at hi ⊢
  simp only [map_zero, Finsupp.zero_apply]
  have hi' : 0 ≤ B.repr z i ∧ B.repr z i < 1 := ⟨by exact_mod_cast hi.1, by exact_mod_cast hi.2⟩
  exact_mod_cast (show B.repr z i = 0 by omega)

/-- The chosen half-open sector contains no diagonal torsion unit other than one. -/
private theorem torsionUnit_eq_one_of_inTorsionSector (u : (𝓞 F)ˣ) (hu : u ∈ Units.torsion F)
    (hsector : inTorsionSector F v₀ σ (atPlace (unitAtInfinity u))) : u = 1 := by
  let f : F →+* ℂ := σ.toRingHom.comp ((extensionEmbedding v₀).comp
    ((Pi.evalRingHom InfinitePlace.Completion v₀).comp (algebraMap F (InfiniteAdeleRing F))))
  let z := f (algebraMap (𝓞 F) F u.val)
  let n := Units.torsionOrder F
  have hn : 0 < (n : ℝ) := by exact_mod_cast Units.torsionOrder_pos F
  have hz : z ^ n = 1 := by
    simpa only [Units.val_pow_eq_pow_val, map_pow, Units.val_one, map_one] using
      congrArg (fun a : (𝓞 F)ˣ ↦ f (algebraMap (𝓞 F) F a.val))
        (Units.pow_torsionOrder_eq_one F hu)
  change z.arg ∈ Set.Ico 0 (2 * Real.pi / n) at hsector
  have hangle : (((n : ℝ) * z.arg : ℝ) : Real.Angle) = 0 := by
    rw [Real.Angle.natCast_mul_eq_nsmul, ← Complex.arg_pow_coe_angle, hz]
    simp
  have harg : (n : ℝ) * z.arg = 0 := by
    have hinj := AddCircle.injOn_coe_Ico (2 * Real.pi) (0 : ℝ)
    rw [zero_add] at hinj
    exact hinj ⟨mul_nonneg hn.le hsector.1, mul_comm (n : ℝ) z.arg ▸
      (lt_div_iff₀ hn).mp hsector.2⟩ ⟨le_rfl, Real.two_pi_pos⟩ hangle
  have hnorm : ‖z‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg z) (Units.torsionOrder_ne_zero F)).mp
    rw [← norm_pow, hz, norm_one]
  apply Units.coe_injective F
  apply f.injective
  have hz₁ : z = 1 := Complex.ext_norm_arg (by simpa using hnorm)
    (by simpa using (mul_eq_zero.mp harg).resolve_left hn.ne')
  simpa only [Units.val_one, map_one] using hz₁

/-- A diagonal idele that is a unit in the integral adele ring comes from a global unit. -/
private theorem exists_globalUnit_of_principal_mem_integralUnits (x : Fˣ)
    (hx : IdeleGroup.unitEmbedding (𝓞 F) F x ∈ integralUnits) :
    ∃ u : (𝓞 F)ˣ, Units.map (algebraMap (𝓞 F) F).toMonoidHom u = x := by
  obtain ⟨a, ha⟩ := hx
  have lift (y : F) (hy : algebraMap F (AdeleRing (𝓞 F) F) y ∈ integralAdelesOutside F ∅) :
      y ∈ (algebraMap (𝓞 F) F).range := by
    have h := (diagonal_mem_integralAdelesOutside F ∅ y).mp hy
    rwa [Finset.coe_empty, integer_empty, Algebra.mem_bot] at h
  have hval : a.val.val = algebraMap F (AdeleRing (𝓞 F) F) x.val := congrArg Units.val ha
  have hinv : a.inv.val = algebraMap F (AdeleRing (𝓞 F) F) x.inv := congrArg Units.inv ha
  obtain ⟨y, hy⟩ := lift x.val (hval ▸ a.val.property)
  obtain ⟨z, hz⟩ := lift x.inv (hinv ▸ a.inv.property)
  let u : (𝓞 F)ˣ := ⟨y, z,
    (IsFractionRing.injective (𝓞 F) F) (by rw [map_mul, hy, hz, x.val_inv, map_one]),
    (IsFractionRing.injective (𝓞 F) F) (by rw [map_mul, hy, hz, x.inv_val, map_one])⟩
  exact ⟨u, Units.ext hy⟩

include hr₁ hr in
/-- Paper: Definition A.2.3.6, p. 549. With the trivial class represented by one,
the only principal idele in the global domain is the identity. -/
theorem principal_mem_ideleFundamentalDomain (x : Fˣ) :
    principal₁ x ∈ E₁ ↔ x = 1 := by
  constructor
  · intro hx
    obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hx
    obtain ⟨g, ⟨hgInt, hgArch⟩, hcg⟩ := Set.mem_smul_set.mp hc
    obtain ⟨e, he⟩ := (picard_uniformization F ∅).2.2.2
    let q := QuotientGroup.mk'
      ((IdeleGroup.principalSubgroup (𝓞 F) F ⊔ integralUnits).comap (N₁).subtype)
    have hclass (a : N₁) : e (q a) = ideleIdealClass F a.val := he a
    have hqx : q (principal₁ x) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_left (Set.mem_range_self x))
    have hqg : q g = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_sup_right hgInt)
    have hqc := congrArg q hcg
    rw [smul_eq_mul, map_mul, hqg, mul_one, hqx] at hqc
    have hc₁ : c = 1 := by rw [← hr c, ← hclass, hqc, map_one]
    have hg : g = principal₁ x := by simpa only [hc₁, hr₁, one_smul] using hcg
    subst g
    obtain ⟨u, hu⟩ := exists_globalUnit_of_principal_mem_integralUnits F x hgInt
    have hArch : atInfinity ((principal₁ x).val) = unitAtInfinity u := by
      rw [← hu]
      exact Units.ext rfl
    obtain ⟨gInf, ⟨hlog, hsector⟩, hgInf⟩ := hgArch
    have hgVal : gInf.val = unitAtInfinity u := hgInf.trans hArch
    change inTorsionSector F v₀ σ (atPlace gInf.val) at hsector
    rw [hgVal] at hsector
    change (fun w : {w : InfinitePlace F // w ≠ w₀} ↦
      infiniteIdeleLog F gInf.val w.val) ∈ regulatorParallelotope F b at hlog
    rw [hgVal] at hlog
    have hlogEq : Units.logEmbedding F (Additive.ofMul u) =
        fun w ↦ infiniteIdeleLog F (unitAtInfinity u) w.val := by
      funext w
      rw [logEmbedding_component, infiniteIdeleLog]
      change _ = (w.val.mult : ℝ) * Real.log
        ‖algebraMap F (InfiniteAdeleRing F) (algebraMap (𝓞 F) F u.val) w.val‖
      rw [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe]
      rfl
    rw [← hlogEq] at hlog
    have htors := logEmbedding_eq_zero_iff.mp
      (logEmbedding_eq_zero_of_mem_regulatorParallelotope F b u hlog)
    rw [torsionUnit_eq_one_of_inTorsionSector F v₀ σ u htors hsector, map_one] at hu
    exact hu.symm
  · rintro rfl
    apply Set.mem_iUnion.mpr
    refine ⟨1, Set.mem_smul_set.mpr ⟨1, ⟨one_mem _, ?_⟩, by rw [hr₁, one_smul, map_one]⟩⟩
    refine ⟨1, ⟨?_, ?_⟩, ?_⟩
    · have hzero : (fun w : {w : InfinitePlace F // w ≠ w₀} ↦
          infiniteIdeleLog F (1 : 𝕀∞) w.val) = 0 := by
        funext w
        change (w.val.mult : ℝ) * Real.log ‖(1 : w.val.Completion)‖ = 0
        simp
      change (fun w : {w : InfinitePlace F // w ≠ w₀} ↦
        infiniteIdeleLog F (1 : 𝕀∞) w.val) ∈ regulatorParallelotope F b
      rw [hzero, regulatorParallelotope, ZSpan.mem_fundamentalDomain]
      simp
    · change inTorsionSector F v₀ σ (atPlace (1 : 𝕀∞))
      simp [inTorsionSector, Set.mem_Ico, div_pos Real.two_pi_pos
        (Nat.cast_pos.mpr (Units.torsionOrder_pos F))]
    · change (1 : 𝕀∞) = atInfinity (1 : 𝕀[F])
      rw [map_one]

-- Remark A.2.3.7, p. 549, is a bibliographic identification of (A.2.3.14).

/-- Paper: Lemma A.2.3.8(1), p. 550. The archimedean domain has compact closure in
the norm-one group. -/
theorem infiniteIdeleFundamentalDomain_precompact : IsCompact (closure E∞) := by
  sorry

/-- Paper: Lemma A.2.3.8(1), p. 550. The archimedean domain also has compact closure
in the full archimedean idele group. -/
theorem infiniteIdeleFundamentalDomain_precompact_ambient :
    IsCompact (closure ((N∞).subtype '' E∞)) := by
  sorry

/-- Paper: Lemma A.2.3.8(1), p. 550. The archimedean domain has nonempty interior
relative to the norm-one group. -/
theorem infiniteIdeleFundamentalDomain_interior : (interior E∞).Nonempty := by
  sorry

local notation "archDomain" => (Subgroup.subtype N∞ '' E∞)

/-- Paper: Lemma A.2.3.8(2), p. 550. Diagonal unit translates cover exactly the
norm-one archimedean ideles. -/
theorem infiniteIdeleFundamentalDomain_cover :
    (⋃ u : (𝓞 F)ˣ, unitAtInfinity u • archDomain) = N∞ := by
  sorry

/-- Paper: Lemma A.2.3.8(2), p. 550. A nonidentity unit translates the archimedean
domain disjointly from itself. -/
theorem infiniteIdeleFundamentalDomain_disjoint (u : (𝓞 F)ˣ) (hu : u ≠ 1) :
    Disjoint (unitAtInfinity u • archDomain) archDomain := by
  sorry

/-- Paper: Lemma A.2.3.8(2), p. 550. The torsion translates recover the whole
preimage of the logarithmic parallelotope in the norm-one group. -/
theorem infiniteIdeleFundamentalDomain_torsion_cover :
    (⋃ u : Units.torsion F, unitAtInfinity u.val • archDomain) =
      (N∞).subtype '' {g : N∞ | inLogBox g} := by
  sorry

-- TODO(paper-gap): (A.2.3.18) repeats the closure where the preceding sentence specifies K.
-- The proof on p. 551 reduces the general compact K to the case K equal to the closure.

/-- Paper: Lemma A.2.3.8(3), p. 550. Only finitely many diagonal unit translates of
the closure meet a given compact set in the norm-one group.
Deviation: We use K as in the preceding sentence and the proof on p. 551. -/
theorem infiniteIdeleFundamentalDomain_finite_translates (K : Set N∞) (hK : IsCompact K) :
    {u : (𝓞 F)ˣ | ((unitAtInfinity u • ((N∞).subtype '' closure E∞)) ∩
      ((N∞).subtype '' K)).Nonempty}.Finite := by
  sorry

-- TODO(paper-gap): (A.2.3.20) describes a positive real ray. For complex v₀ the
-- sector in Definition A.2.3.6 is wider, as (A.2.3.21) on p. 551 also shows.

section ExactSequences

local notation "H" => (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ integralUnits)

-- TODO(paper-gap): (A.2.3.22) leaves the arrows implicit. With multiplication as the
-- quotient map, diagonal units must enter the two factors with opposite exponents.

/-- Paper: Proposition A.2.3.9, p. 552. Multiplication of a principal idele and an
idele integral and invertible at all finite places is a strict quotient onto their
product subgroup. Its kernel is the diagonally embedded discrete group of global units.
Deviation: We order the factors as the discrete field units followed by the integral
idele group. For the multiplication map the two copies of a kernel unit are inverse. -/
theorem idele_principal_integral_exact :
    letI : TopologicalSpace Fˣ := ⊥
    letI : TopologicalSpace (𝓞 F)ˣ := ⊥
    let d := IdeleGroup.unitEmbedding (𝓞 F) F
    let j := Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom
    ∃ (i : (𝓞 F)ˣ →* Fˣ × (integralAdelesOutside F ∅)ˣ)
      (p : Fˣ × (integralAdelesOutside F ∅)ˣ →* ↥(H : Subgroup 𝕀[F])),
      (∀ u, (i u).1 = Units.map (algebraMap (𝓞 F) F).toMonoidHom u ∧
        j (i u).2 = (d (i u).1)⁻¹) ∧
      (∀ x, (p x).val = d x.1 * j x.2) ∧ IsClosedEmbedding i ∧
        MulExact i p ∧ IsOpenQuotientMap p := by
  sorry

/-- Paper: Proposition A.2.3.9, p. 552. The ideal class map is a strict quotient of
the ideles onto the discrete Picard group, with the principal times integral subgroup
as its closed kernel. -/
theorem idele_ideal_class_exact :
    letI : TopologicalSpace (CommRing.Pic (𝓞 F)) := ⊥
    ∃ p : 𝕀[F] →* CommRing.Pic (𝓞 F), (∀ g, p g = ideleIdealClass F g) ∧
      IsClosedEmbedding (Subgroup.subtype H) ∧ MulExact (Subgroup.subtype H) p ∧
      IsOpenQuotientMap p := by
  sorry

/-- Paper: Proposition A.2.3.9, p. 552. Restriction to norm one still gives a strict
quotient onto the discrete Picard group, with the norm-one part of the same kernel. -/
theorem normOne_ideal_class_exact :
    letI : TopologicalSpace (CommRing.Pic (𝓞 F)) := ⊥
    let H₁ := Subgroup.comap (Subgroup.subtype N₁) H
    ∃ p : N₁ →* CommRing.Pic (𝓞 F), (∀ g, p g = ideleIdealClass F g.val) ∧
      IsClosedEmbedding H₁.subtype ∧ MulExact H₁.subtype p ∧ IsOpenQuotientMap p := by
  sorry

end ExactSequences

section Representatives

omit [NumberField F] in
/-- Paper: Lemma A.2.3.2(3), p. 548. Compact sets of logarithms bound both the
archimedean coordinates and their inverses, so their preimages are compact. -/
private theorem infiniteIdeleLog_isCompact_preimage {K : Set (InfinitePlace F → ℝ)}
    (hK : IsCompact K) : IsCompact (infiniteIdeleLog F ⁻¹' K) := by
  have : T1Space (InfiniteAdeleRing F) := inferInstanceAs (T1Space (∀ w : InfinitePlace F, w.Completion))
  have hne (g : 𝕀∞) (w : InfinitePlace F) : g.val w ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion w).toMonoidHom g).ne_zero
  have hcont : Continuous (infiniteIdeleLog F) := by
    apply continuous_pi
    intro w
    exact continuous_const.mul (((continuous_apply w).comp Units.continuous_val).norm.log
      (fun g ↦ norm_ne_zero_iff.mpr (hne g w)))
  have hbound (w : InfinitePlace F) :
      ∃ R, ∀ x ∈ K, Real.exp (|x w| / w.mult) ≤ R := by
    obtain ⟨R, hR⟩ := hK.exists_bound_of_continuousOn
      ((((continuous_apply w).abs.div_const (w.mult : ℝ)).rexp).continuousOn)
    exact ⟨R, fun x hx ↦ (Real.le_norm_self _).trans (hR x hx)⟩
  choose R hR using hbound
  let B : Set (InfiniteAdeleRing F) := Set.univ.pi fun w ↦ Metric.closedBall 0 (R w)
  have hB : IsCompact B := by
    apply isCompact_univ_pi
    intro w
    let e := extensionEmbedding w
    have he : Isometry e := isometry_extensionEmbedding w
    convert he.isClosedEmbedding.isCompact_preimage (isCompact_closedBall (e 0) (R w)) using 1
    ext z
    simp only [Set.mem_preimage, Metric.mem_closedBall, he.dist_eq]
  refine (Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hB.prod (MulOpposite.opHomeomorph.symm.isCompact_preimage.mpr hB))).of_isClosed_subset
      (hK.isClosed.preimage hcont) ?_
  intro g hg
  have hlog (w : InfinitePlace F) :
      infiniteIdeleLog F g w / (w.mult : ℝ) = Real.log ‖g.val w‖ :=
    mul_div_cancel_left₀ _ InfinitePlace.mult_coe_ne_zero
  have hnorm (w : InfinitePlace F) :
      Real.exp |Real.log ‖g.val w‖| ≤ R w := by
    have hm : 0 ≤ (w.mult : ℝ) := Nat.cast_nonneg _
    rw [← hlog, abs_div, abs_of_nonneg hm]
    exact hR w (infiniteIdeleLog F g) hg
  change g.val ∈ B ∧ g.inv ∈ B
  constructor
  · intro w _
    change g.val w ∈ Metric.closedBall 0 (R w)
    rw [Metric.mem_closedBall, dist_zero_right, ← Real.exp_log (norm_pos_iff.mpr (hne g w))]
    exact (Real.exp_le_exp.mpr (le_abs_self _)).trans (hnorm w)
  · intro w _
    have hinv : g.inv w = (g.val w)⁻¹ := by
      exact (Units.val_inv_eq_inv_val (Units.map (Pi.evalRingHom
        InfinitePlace.Completion w).toMonoidHom g))
    change g.inv w ∈ Metric.closedBall 0 (R w)
    rw [Metric.mem_closedBall, dist_zero_right, hinv, norm_inv,
      ← Real.exp_log (norm_pos_iff.mpr (hne g w)), ← Real.exp_neg]
    exact (Real.exp_le_exp.mpr (neg_le_abs _)).trans (hnorm w)

/-- Paper: Lemma A.2.3.8(1), p. 550. The compact logarithmic parallelepiped
encloses the archimedean domain after the omitted coordinate is restored. -/
private theorem infiniteIdeleFundamentalDomain_subset_compact :
    ∃ A : Set 𝕀∞, IsCompact A ∧ (N∞).subtype '' E∞ ⊆ A := by
  let B := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  let extend (x : logSpace F) (w : InfinitePlace F) :=
    if hw : w = w₀ then -∑ v, x v else x ⟨w, hw⟩
  have hExtend : Continuous extend := by
    apply continuous_pi
    intro w
    by_cases hw : w = w₀
    · simp only [extend, hw, dite_true]
      exact (continuous_finsetSum Finset.univ fun v _ ↦ continuous_apply v :
        Continuous (fun x : logSpace F ↦ ∑ v, x v)).neg
    · simp only [extend, hw, dite_false]
      exact continuous_apply (⟨w, hw⟩ : {v : InfinitePlace F // v ≠ w₀})
  refine ⟨infiniteIdeleLog F ⁻¹' (extend '' B.parallelepiped),
    infiniteIdeleLog_isCompact_preimage F (B.parallelepiped.isCompact.image hExtend), ?_⟩
  rintro _ ⟨g, hg, rfl⟩
  refine ⟨fun v ↦ infiniteIdeleLog F g.val v.val,
    ZSpan.fundamentalDomain_subset_parallelepiped B hg.1, ?_⟩
  funext w
  by_cases hw : w = w₀
  · subst w
    have h := infiniteIdeleLog_sum_zero F g
    rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, add_eq_zero_iff_eq_neg] at h
    simp only [extend, dite_true]
    exact h.symm
  · simp only [extend, hw, dite_false]
    rfl

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(1), p. 552. The global domain has compact closure
in the norm-one ideles. -/
theorem ideleFundamentalDomain_precompact : IsCompact (closure E₁) := by
  obtain ⟨hT2, _, _, _, _, hClosed⟩ := ideleGroup_topology F
  obtain ⟨_, _, _, _, _, hFinite, ⟨ePic⟩⟩ := ideleClassGroup_finiteness F
  have : Finite (CommRing.Pic (𝓞 F)) := @Finite.of_equiv _ _ hFinite ePic.toEquiv
  have : T1Space (FiniteAdeleRing (𝓞 F) F) := by
    change T1Space (Πʳ v : Primes(F), [v.adicCompletion F, v.adicCompletionIntegers F])
    infer_instance
  obtain ⟨A, hA, hDomain⟩ := infiniteIdeleFundamentalDomain_subset_compact F b v₀ σ
  let S : Subring (FiniteAdeleRing (𝓞 F) F) :=
    ⨅ v : Primes(F), (v.adicCompletionIntegers F).toSubring.comap
      (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v)
  have hS_iff (a : FiniteAdeleRing (𝓞 F) F) :
      a ∈ S ↔ ∀ v : Primes(F), a v ∈ v.adicCompletionIntegers F := by
    simp only [S, Subring.mem_iInf]
    rfl
  have hS : IsCompact (S : Set (FiniteAdeleRing (𝓞 F) F)) := by
    have (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F) :=
      compactSpace_adicCompletionIntegers v
    let insert : (∀ v : Primes(F), v.adicCompletionIntegers F) → FiniteAdeleRing (𝓞 F) F :=
      RestrictedProduct.structureMap _ _ Filter.cofinite
    have hInsert : Continuous insert := RestrictedProduct.isEmbedding_structureMap.continuous
    have hRange : Set.range insert = S := by
      change Set.range (RestrictedProduct.structureMap _
        (fun v : Primes(F) ↦ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
        Filter.cofinite) = _
      rw [RestrictedProduct.range_structureMap]
      ext a
      exact (hS_iff a).symm
    rw [← hRange]
    exact isCompact_range hInsert
  let e := ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)
  let C : Set N₁ := Subtype.val ⁻¹' (e.symm '' (A ×ˢ (S.toSubmonoid.units : Set _)))
  have hC : IsCompact C := hClosed.isClosedEmbedding_subtypeVal.isCompact_preimage
    ((hA.prod (Submonoid.units_isCompact hS)).image e.symm.continuous)
  apply (isCompact_iUnion fun c ↦ hC.smul (r c)).closure_of_subset
  apply Set.iUnion_mono
  intro c
  apply Set.smul_set_mono
  rintro g ⟨⟨u, hu⟩, hg⟩
  refine ⟨e g.val, ⟨hDomain hg, ?_⟩, e.symm_apply_apply _⟩
  have hmem (a : integralAdelesOutside F ∅) : a.val.2 ∈ S := by
    have h := a.property
    simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty, not_false_eq_true,
      true_implies] at h
    exact (hS_iff _).mpr h
  change g.val.val.2 ∈ S ∧ g.val.inv.2 ∈ S
  rw [← hu]
  exact ⟨hmem u.val, hmem u.inv⟩

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(1), p. 552. The global domain has nonempty interior
in the norm-one ideles. -/
theorem ideleFundamentalDomain_interior : (interior E₁).Nonempty := by
  sorry

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(2), p. 552. Principal translates cover the norm-one ideles. -/
theorem ideleFundamentalDomain_cover : (⋃ x : Fˣ, principal₁ x • E₁) = Set.univ := by
  sorry

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(2), p. 552. A nonidentity principal translate is
disjoint from the global domain. -/
theorem ideleFundamentalDomain_disjoint (x : Fˣ) (hx : x ≠ 1) :
    Disjoint (principal₁ x • E₁) E₁ := by
  sorry

include hr₁ hr in
/-- Paper: Proposition A.2.3.10(3), p. 552. Only finitely many principal translates
of the closure of the global domain meet a given compact subset of the norm-one ideles. -/
theorem ideleFundamentalDomain_finite_translates (K : Set N₁) (hK : IsCompact K) :
    {x : Fˣ | ((principal₁ x • closure E₁) ∩ K).Nonempty}.Finite := by
  sorry

variable (s : ℝ≥0ˣ →* (InfiniteAdeleRing F)ˣ) (hs : Continuous s) (hn : RightInverse s (infiniteIdeleNorm F))

include hs hn in
/-- Paper: Lemma A.2.3.11, p. 553. Multiplication by any continuous homomorphic
section splits the archimedean norm as a Lie group product. In mixed real and complex
coordinates both directions extend smoothly to open neighborhoods of their domains. -/
theorem infiniteIdeleNormSection_product :
    let m := InfiniteAdeleRing.ringEquiv_mixedSpace F
    ∃ e : (ℝ≥0ˣ × N∞) ≃ₜ* 𝕀∞, (∀ t g, e (t, g) = s t * g.val) ∧
      (∃ f : ℝ × mixedEmbedding.mixedSpace F → mixedEmbedding.mixedSpace F,
        ContDiffOn ℝ ∞ f {z | 0 < z.1} ∧
        ∀ (t : ℝ≥0ˣ) (g : N∞), f ((t.val : ℝ), m g.val.val) = m (e (t, g)).val) ∧
      (∃ f : mixedEmbedding.mixedSpace F → ℝ × mixedEmbedding.mixedSpace F,
        ContDiffOn ℝ ∞ f {z | IsUnit z} ∧ ∀ g : 𝕀∞, f (m g.val) =
          (((e.symm g).1.val : ℝ), m (e.symm g).2.val.val)) := by
  sorry

include hr₁ hr hs hn in
/-- Paper: Lemma A.2.3.12, p. 553. Multiplication of a principal idele, a section
value supported at infinity and a global domain element parametrizes all ideles bijectively. -/
theorem ideleFundamentalDomain_bijective :
    let j : 𝕀∞ →* 𝕀[F] := fromInfinity
    Bijective (fun z : Fˣ × ℝ≥0ˣ × E₁ ↦
      IdeleGroup.unitEmbedding (𝓞 F) F z.1 * j (s z.2.1) * z.2.2.val.val) := by
  sorry

end Representatives

local notation "placeSection" =>
  MonoidHom.comp (Units.map (InfiniteAdeleRing.ofCompletion v₀))
    (infinitePlaceRealPower F v₀ ((InfinitePlace.mult v₀ : ℝ)⁻¹))

variable (K : Set ℝ≥0ˣ) (hK : IsCompact K)
local notation "productLocus" => (placeSection '' K) * (Subgroup.subtype N∞ '' closure E∞)

omit [NumberField F] in
/-- Ideles whose full logarithms lie in a compact set have compact closure.
Each local coordinate is bounded above in norm and bounded away from zero. -/
private theorem infiniteIdeleLog_closure_preimage_compact
    (C : Set (InfinitePlace F → ℝ)) (hC : IsCompact C) :
    IsCompact (closure (infiniteIdeleLog F ⁻¹' C)) := by
  let logRadius (v : InfinitePlace F) (x : InfinitePlace F → ℝ) := x v / (v.mult : ℝ)
  have hlogRadius (v : InfinitePlace F) : Continuous (logRadius v) :=
    (continuous_apply v).div_const _
  choose lower hlower using fun v ↦ hC.bddBelow_image (hlogRadius v).continuousOn
  choose upper hupper using fun v ↦ hC.bddAbove_image (hlogRadius v).continuousOn
  let annulus (v : InfinitePlace F) : Set v.Completion :=
    Metric.closedBall 0 (Real.exp (upper v)) ∩ {z | Real.exp (lower v) ≤ ‖z‖}
  have hannulus (v : InfinitePlace F) : IsCompact (annulus v) := by
    have he := isometry_extensionEmbedding v
    have hball : IsCompact (Metric.closedBall (0 : v.Completion) (Real.exp (upper v))) := by
      simpa only [← he.preimage_closedBall] using he.isClosedEmbedding.isCompact_preimage
        (isCompact_closedBall (extensionEmbedding v 0) (Real.exp (upper v)))
    exact hball.inter_right (isClosed_le continuous_const continuous_norm)
  let box := Set.univ.pi fun v ↦ Units.val ⁻¹' annulus v
  have hbox : IsCompact box := isCompact_univ_pi fun v ↦ by
    refine Units.isEmbedding_val₀.isInducing.isCompact_preimage' (hannulus v) ?_
    intro z hz
    have hzpos : 0 < ‖z‖ := (Real.exp_pos _).trans_le hz.2
    exact ⟨Units.mk0 z (norm_pos_iff.mp hzpos), rfl⟩
  refine (ContinuousMulEquiv.piUnits.toHomeomorph.isCompact_preimage.mpr hbox).closure_of_subset ?_
  intro g hg v _
  have hlog : logRadius v (infiniteIdeleLog F g) = Real.log ‖g.val v‖ :=
    mul_div_cancel_left₀ _ v.mult_coe_ne_zero
  have hne : g.val v ≠ 0 :=
    (Units.map (Pi.evalRingHom InfinitePlace.Completion v).toMonoidHom g).ne_zero
  have hnorm : Real.exp (logRadius v (infiniteIdeleLog F g)) = ‖g.val v‖ := by
    rw [hlog, Real.exp_log (norm_pos_iff.mpr hne)]
  have hmem : logRadius v (infiniteIdeleLog F g) ∈ logRadius v '' C := ⟨_, hg, rfl⟩
  change g.val v ∈ annulus v
  simp only [annulus, Set.mem_inter_iff, mem_closedBall_zero_iff, Set.mem_ofPred_eq, ← hnorm]
  exact ⟨Real.exp_le_exp.mpr (hupper v hmem), Real.exp_le_exp.mpr (hlower v hmem)⟩

include hK in
/-- Paper: Lemma A.2.3.13(1), p. 553. Multiplying the closed archimedean domain by
a compact subset of the positive subgroup at the chosen place gives a compact set.
The positive subgroup is parametrized by the single-place norm section. -/
theorem infiniteIdele_product_compact : IsCompact productLocus := by
  have hsection : Continuous placeSection := by
    change Continuous (atInfinity ∘ singlePlaceIdeleNormSection F v₀)
    exact (continuous_fst.units_map _).comp (singlePlaceIdeleNormSection_continuous F v₀)
  let fullLog (x : logSpace F) (v : InfinitePlace F) :=
    if hv : v ≠ w₀ then x ⟨v, hv⟩ else -∑ w, x w
  have hfullLog : Continuous fullLog := by
    apply continuous_pi
    intro v
    by_cases hv : v ≠ w₀
    · simpa only [fullLog, dite_eq_left hv] using
        (continuous_apply (⟨v, hv⟩ : {w : InfinitePlace F // w ≠ w₀}))
    · simp only [fullLog, dite_eq_right hv]
      exact continuous_neg.comp (continuous_finsetSum Finset.univ fun w _ ↦ continuous_apply w)
  let basis := (b.map (Units.logEmbeddingEquiv F)).ofZLatticeBasis ℝ (Units.unitLattice F)
  have hLogPreimage := infiniteIdeleLog_closure_preimage_compact F _
    (basis.parallelepiped.isCompact.image hfullLog)
  have hsub : IsClosedEmbedding (Subgroup.subtype N∞) :=
    (infiniteIdeleNorm_ker_closed F).isClosedEmbedding_subtypeVal
  have hDomain : IsCompact (closure E∞) := by
    refine (hsub.isCompact_preimage hLogPreimage).closure_of_subset ?_
    intro g hg
    apply subset_closure
    let x : logSpace F := fun w ↦ infiniteIdeleLog F g.val w
    refine ⟨x, ZSpan.fundamentalDomain_subset_parallelepiped basis hg.1, ?_⟩
    funext v
    change fullLog x v = infiniteIdeleLog F g.val v
    by_cases hv : v ≠ w₀
    · simp only [fullLog, dite_eq_left hv, x]
    · obtain rfl : v = w₀ := not_ne_iff.mp hv
      have hsum := infiniteIdeleLog_sum_zero F g
      rw [Fintype.sum_eq_add_sum_subtype_ne _ w₀, add_eq_zero_iff_eq_neg] at hsum
      simpa only [fullLog, dite_eq_right (not_ne_iff.mpr rfl), x] using hsum.symm
  exact (hK.image hsection).mul (hDomain.image hsub.continuous)

include hK in
/-- Paper: Lemma A.2.3.13(1), p. 553. If the compact set has interior in the
positive subgroup, the product has interior in the archimedean ideles. -/
theorem infiniteIdele_product_interior (hi : (interior K).Nonempty) :
    (interior productLocus).Nonempty := by
  sorry

include hK in
/-- Paper: Lemma A.2.3.13(2), p. 553. The product in the archimedean adele ring
misses every coordinate hyperplane. -/
theorem infiniteIdele_product_disjoint_hyperplanes :
    Disjoint (Units.val '' productLocus) (⋃ v : InfinitePlace F, {a : InfiniteAdeleRing F | a v = 0}) := by
  sorry

include hK in
/-- Paper: Lemma A.2.3.13(3), p. 553. If the compact set has interior in the positive
subgroup, the product also has interior in the archimedean adele ring. -/
theorem infiniteIdele_product_adele_interior (hi : (interior K).Nonempty) :
    (interior (Units.val '' productLocus)).Nonempty := by
  sorry

section SLocal

variable (S : Finset (Primes(F)))
local notation "Oₛ(" F ", " S ")" => Set.integer (S : Set (Primes(F))) F
local notation "𝕀ₛ" => (SAdeleRing F S)ˣ
local notation "Nₛ" => MonoidHom.ker (sIdeleNorm F S)
local notation "projectS" => Units.map (RingHom.toMonoidHom (adeleProjection F S))
local notation "outsideInclusion" =>
  Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S)))
local notation "diagonalS" => Units.map (RingHom.toMonoidHom (integralAdeleDiagonal F S))
local notation "unitAtS" => MonoidHom.comp projectS (MonoidHom.comp outsideInclusion diagonalS)

variable {ι : Type*} (a : Module.Basis ι ℤ (𝓞 F))

/-- Paper: Definition A.2.4.1, p. 554. The S-adelic domain is the archimedean half-open
parallelepiped of the integral basis times the local integer rings at the finite places in S. -/
def sAdeleFundamentalDomain : Set (SAdeleRing F S) :=
  {x | x.1 ∈ infiniteAdeleFundamentalDomain F a ∧ ∀ v : S, x.2 v ∈ v.val.adicCompletionIntegers F}

local notation "Dₛ" => sAdeleFundamentalDomain F S a
local notation "addAtS" =>
  RingHom.comp (adeleProjection F S)
    (RingHom.comp (Subring.subtype (integralAdelesOutside F S)) (integralAdeleDiagonal F S))

/-- Paper: Definition A.2.4.1, p. 554. The only diagonal S-integer in the domain is zero. -/
theorem diagonal_mem_sAdeleFundamentalDomain (x : Oₛ(F, S)) : addAtS x ∈ Dₛ ↔ x = 0 := by
  sorry

/-- Paper: Lemma A.2.4.2(1), p. 554. S-integer translates of the additive domain
cover the S-adeles. -/
theorem sAdeleFundamentalDomain_cover : (⋃ x : Oₛ(F, S), addAtS x +ᵥ Dₛ) = Set.univ := by
  sorry

/-- Paper: Lemma A.2.4.2(2), p. 554. Only finitely many diagonal S-integer translates
of the closure meet a given compact subset of the S-adeles. -/
theorem sAdeleFundamentalDomain_finite_translates (K : Set (SAdeleRing F S)) (hK : IsCompact K) :
    {x : Oₛ(F, S) | ((addAtS x +ᵥ closure Dₛ) ∩ K).Nonempty}.Finite := by
  sorry

/-- Paper: Definition A.2.4.3, p. 554. The S-logarithm has one normalized log absolute
value for each infinite place and each selected finite place, as in (A.2.4.7) on p. 555. -/
def sIdeleLog (g : 𝕀ₛ) : InfinitePlace F ⊕ S → ℝ :=
  Sum.elim (fun v ↦ v.mult * Real.log ‖g.val.1 v‖) (fun v ↦ Real.log ‖g.val.2 v‖)

/-- Paper: Definition A.2.4.3, p. 555. Summing all S-logarithmic coordinates gives
the logarithm of the S-idelic norm. -/
theorem sIdeleLog_sum (g : 𝕀ₛ) :
    ∑ v, sIdeleLog F S g v = Real.log ((sIdeleNorm F S g).val : ℝ) := by
  sorry

/-- Paper: Definition A.2.4.3, p. 554. On diagonal S-units the S-logarithm vanishes
exactly on torsion units. -/
theorem sIdeleLog_unit_eq_zero (u : Oₛ(F, S)ˣ) :
    sIdeleLog F S (unitAtS u) = 0 ↔ u ∈ CommGroup.torsion Oₛ(F, S)ˣ := by
  sorry

/-- Paper: §A.2.4.2, p. 554. The roots of unity in the ordinary units map onto
the full torsion subgroup of the S-units, so its order is independent of S. -/
theorem sUnit_torsion_eq_image :
    (Units.torsion F).map (Units.map (algebraMap (𝓞 F) Oₛ(F, S)).toMonoidHom) =
      CommGroup.torsion Oₛ(F, S)ˣ := by
  sorry

local notation "sRank(" F ", " S ")" => (Fintype.card (InfinitePlace F) + Finset.card S - 1)
variable (bₛ : Module.Basis (Fin sRank(F, S)) ℤ (Additive (Oₛ(F, S)ˣ ⧸ CommGroup.torsion Oₛ(F, S)ˣ)))

-- TODO(paper-gap): (A.2.4.8) says to choose a basis of the full S-unit group, which
-- contains the nonidentity torsion unit -1. As in (A.2.3.7), a basis is taken modulo torsion.

/-- Paper: Definition A.2.4.3, p. 555. The S-parallelotope consists of the sums of
basis logarithms with each real coefficient in the half-open unit interval.
Deviation: The integral basis is of the S-units modulo torsion. We take representatives
to evaluate their logarithms. -/
def sRegulatorParallelotope : Set (InfinitePlace F ⊕ S → ℝ) :=
  {y | ∃ t : Fin sRank(F, S) → ℝ, (∀ i, t i ∈ Set.Ico 0 1) ∧
    y = ∑ i, t i • sIdeleLog F S (unitAtS (bₛ i).toMul.out)}

/-- Paper: Definition A.2.4.3, p. 555. The S-parallelotope is contained in the
hyperplane where the sum of the coordinates vanishes. -/
theorem sRegulatorParallelotope_sum_zero (y : InfinitePlace F ⊕ S → ℝ)
    (hy : y ∈ sRegulatorParallelotope F S bₛ) : ∑ v, y v = 0 := by
  sorry

/-- Paper: Definition A.2.4.3, p. 555. Along a basis logarithm the parallelotope
includes the coefficient zero and excludes one. Any lift of the basis unit gives the same test.
Deviation: We use the basis modulo torsion specified for (A.2.4.8). -/
theorem sRegulatorParallelotope_basis_line (i : Fin sRank(F, S)) (u : Oₛ(F, S)ˣ)
    (hu : QuotientGroup.mk u = (bₛ i).toMul) (t : ℝ) :
    t • sIdeleLog F S (unitAtS u) ∈ sRegulatorParallelotope F S bₛ ↔ t ∈ Set.Ico 0 1 := by
  sorry

/-- Paper: Definition A.2.4.3, p. 554. The local norm-one domain cuts out the
S-parallelotope in logarithmic coordinates and the torsion sector at the chosen infinite place. -/
def sLocalIdeleFundamentalDomain : Set Nₛ :=
  {g | sIdeleLog F S g.val ∈ sRegulatorParallelotope F S bₛ ∧
    inTorsionSector F v₀ σ (atPlace (Units.map (RingHom.fst _ _).toMonoidHom g.val))}

local notation "Eₛ" => sLocalIdeleFundamentalDomain F v₀ σ S bₛ

/-- Paper: Definition A.2.4.3, p. 554. The local domain contains exactly one
diagonal S-unit, namely the identity. -/
theorem unit_mem_sLocalIdeleFundamentalDomain (u : Oₛ(F, S)ˣ) :
    unitAtS u ∈ Subgroup.subtype Nₛ '' Eₛ ↔ u = 1 := by
  sorry

local notation "outsideNormOne(" F ", " S ")" => MonoidHom.ker (MonoidHom.comp (ideleNorm F)
  (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F S)))))
local notation "Picₛ(" F ", " S ")" => CommRing.Pic Oₛ(F, S)

-- TODO(paper-gap): In (A.2.4.4) every allowed representative is a unit outside S and
-- therefore has trivial S-ideal class. The prescribed family need not exist.

/-- Paper: Definition A.2.4.3, p. 554. Every idele integral and invertible outside
S has trivial ideal class after extension to the S-integers.
Deviation: This is the obstruction to the representatives prescribed for (A.2.4.4). -/
theorem sIdele_ideal_class_trivial (g : (integralAdelesOutside F S)ˣ) :
    CommRing.Pic.mapAlgebra (𝓞 F) Oₛ(F, S) (ideleIdealClass F (outsideInclusion g)) = 1 := by
  let ev (v : Primes(F)) := (RestrictedProduct.evalRingHom
    (fun w : Primes(F) ↦ w.adicCompletion F) v).comp (RingHom.snd
      (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let x (v : Primes(F)) := Units.map (ev v).toMonoidHom (outsideInclusion g)
  have hle (a : integralAdelesOutside F S) (v : Primes(F)) (hv : v ∉ S) :
      Valued.v (ev v a.val) ≤ 1 := by
    have ha := a.property
    simp only [integralAdelesOutside, Subring.mem_iInf, Subring.mem_comap] at ha
    exact ha v hv
  -- Both the idele and its inverse are integral outside S.
  have hsupp : (Function.mulSupport fun v ↦ localIdealClass F v (x v)) ⊆ (S : Set _) := by
    intro v hv
    by_contra hvS
    apply hv
    apply (localIdealClass_normalization F v (x v)).1
    rw [HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one]
    have hmul : Valued.v (x v).val * Valued.v (x v).inv = 1 := by
      rw [← map_mul, (x v).val_inv, map_one]
    exact eq_one_of_one_le_mul_left (hle g.val v hvS) (hle g.inv v hvS) hmul.ge
  change CommRing.Pic.mapAlgebra (𝓞 F) Oₛ(F, S)
    (∏ᶠ v, localIdealClass F v (x v)) = 1
  rw [finprod_eq_finsetProd_of_mulSupport_subset _ hsupp,
    Finset.prod_subtype S (fun _ ↦ Iff.rfl)]
  -- The product over S comes from the first map in the Picard localization sequence.
  have h := picard_localization_exact F ∅ S (Finset.empty_subset S)
  dsimp only at h
  rw [Finset.sdiff_empty] at h
  obtain ⟨j, _, hexact, _, hj⟩ := h
  have hclass := hexact.apply_apply_eq_one (QuotientGroup.mk (fun v : S ↦ QuotientGroup.mk (x v)))
  rw [hj, ← CommRing.Pic.mapRingHom_algebraMap, CommRing.Pic.mapRingHom_mapRingHom] at hclass
  rwa [← CommRing.Pic.mapRingHom_algebraMap]

/-- Paper: Definition A.2.4.3, p. 554. Equation (A.2.4.4) takes a union of translates
of the local domain times the outside integral units, inside the norm-one group integral
and invertible outside S.
Deviation: The displayed union is defined for supplied translating elements. The paper's
class representative condition is impossible when the S-class group is nontrivial. -/
def sIdeleFundamentalDomain (rₛ : Picₛ(F, S) → outsideNormOne(F, S)) : Set outsideNormOne(F, S) :=
  ⋃ c, rₛ c • {g : outsideNormOne(F, S) |
    projectS (outsideInclusion g.val) ∈ (Subgroup.subtype Nₛ '' Eₛ)}

/-- Paper: Definition A.2.4.3, p. 554. With trivial S-class group and its prescribed
identity representative, membership in the displayed union is tested by projection to S. -/
theorem mem_sIdeleFundamentalDomain_of_classNumberOne [Subsingleton Picₛ(F, S)]
    (rₛ : Picₛ(F, S) → outsideNormOne(F, S)) (h₁ : rₛ 1 = 1) (g : outsideNormOne(F, S)) :
    g ∈ sIdeleFundamentalDomain F v₀ σ S bₛ rₛ ↔
      projectS (outsideInclusion g.val) ∈ (Subgroup.subtype Nₛ '' Eₛ) := by
  sorry

/-- Paper: Proposition A.2.4.4(1), p. 555. The local domain has compact closure in
the norm-one S-ideles. -/
theorem sLocalIdeleFundamentalDomain_precompact : IsCompact (closure Eₛ) := by
  sorry

/-- Paper: Proposition A.2.4.4(1), p. 555. The local domain has nonempty interior in
the norm-one S-ideles. -/
theorem sLocalIdeleFundamentalDomain_interior : (interior Eₛ).Nonempty := by
  sorry

local notation "localDomain" => (Subgroup.subtype Nₛ '' Eₛ)

/-- Paper: Proposition A.2.4.4(2), p. 555. The diagonal S-unit translates of the local
domain cover exactly the norm-one S-ideles. -/
theorem sLocalIdeleFundamentalDomain_cover :
    (⋃ u : Oₛ(F, S)ˣ, unitAtS u • localDomain) = Nₛ := by
  sorry

/-- Paper: Proposition A.2.4.4(2), p. 555. Every nonidentity S-unit translates the
local domain disjointly from itself. -/
theorem sLocalIdeleFundamentalDomain_disjoint (u : Oₛ(F, S)ˣ) (hu : u ≠ 1) :
    Disjoint (unitAtS u • localDomain) localDomain := by
  sorry

/-- Paper: Proposition A.2.4.4(3), p. 555. Only finitely many S-unit translates of
the closure meet a given compact subset of the norm-one S-ideles. -/
theorem sLocalIdeleFundamentalDomain_finite_translates (K : Set Nₛ) (hK : IsCompact K) :
    {u : Oₛ(F, S)ˣ | ((unitAtS u • (Subgroup.subtype Nₛ '' closure Eₛ)) ∩
      (Subgroup.subtype Nₛ '' K)).Nonempty}.Finite := by
  sorry

-- TODO(paper-gap): Proposition A.2.4.4(4) requires the nonexistent representatives
-- of (A.2.4.4) in the nontrivial class group case. The identity represents the trivial case.

variable [Subsingleton Picₛ(F, S)] (rₛ : Picₛ(F, S) → outsideNormOne(F, S)) (h₁ : rₛ 1 = 1)
local notation "globalSDomain" => sIdeleFundamentalDomain F v₀ σ S bₛ rₛ

include h₁ in
/-- Paper: Proposition A.2.4.4(4), p. 555. The domain with outside unit factors has
compact closure in the norm-one group integral and invertible outside S.
Deviation: We state the case where the prescribed representatives exist. -/
theorem sIdeleFundamentalDomain_precompact : IsCompact (closure globalSDomain) := by
  sorry

include h₁ in
/-- Paper: Proposition A.2.4.4(4), p. 555. The domain with outside unit factors has
nonempty interior relative to that group.
Deviation: We assume the S-class group is trivial. -/
theorem sIdeleFundamentalDomain_interior : (interior globalSDomain).Nonempty := by
  sorry

include h₁ in
/-- Paper: Proposition A.2.4.4(4), p. 555. S-unit translates cover the norm-one
group integral and invertible outside S.
Deviation: We assume the S-class group is trivial. -/
theorem sIdeleFundamentalDomain_cover :
    (⋃ u : Oₛ(F, S)ˣ, diagonalS u • (Subgroup.subtype outsideNormOne(F, S) '' globalSDomain)) =
      outsideNormOne(F, S) := by
  sorry

include h₁ in
/-- Paper: Proposition A.2.4.4(4), p. 555. A nonidentity S-unit translates the domain
with outside unit factors disjointly from itself.
Deviation: We assume the S-class group is trivial. -/
theorem sIdeleFundamentalDomain_disjoint (u : Oₛ(F, S)ˣ) (hu : u ≠ 1) :
    let E := Subgroup.subtype outsideNormOne(F, S) '' globalSDomain
    Disjoint (diagonalS u • E) E := by
  sorry

/-- Paper: Remark A.2.4.5, p. 555. All sufficiently large finite sets of places have
trivial S-ideal class group. The finite set parameter lists the finite places only. -/
theorem eventually_trivial_sIdealClassGroup :
    ∃ T : Finset (Primes(F)), ∀ S : Finset (Primes(F)), T ⊆ S →
      Subsingleton (CommRing.Pic (Set.integer (S : Set (Primes(F))) F)) := by
  sorry

/-- Paper: Remark A.2.4.5, p. 555. When the S-class group is trivial the inclusion
induces a topological isomorphism on idele classes, compatible with both norms. -/
theorem sIdeleClassGroup_equiv_of_classNumberOne :
    ∃ e : SIdeleClassGroup F S ≃ₜ* IdeleClassGroup (𝓞 F) F,
      (∀ g : (integralAdelesOutside F S)ˣ, e (QuotientGroup.mk g) =
        QuotientGroup.mk (outsideInclusion g)) ∧ ∀ c, ideleClassNorm F (e c) = sIdeleClassNorm F S c := by
  sorry

-- TODO(paper-gap): Remark A.2.4.5 asserts coverage of the full norm-one ideles before
-- taking classes. For F = ℚ a principal prime outside S is a norm-one idele and is
-- not a unit at that prime. All the proposed S-unit translates are units there.

/-- Paper: Remark A.2.4.5, p. 555. For any finite set of rational places a principal
prime idele has norm one and lies outside the group of ideles invertible off that set.
Deviation: This gives a counterexample to the asserted cover inside the full norm-one group. -/
theorem exists_rat_prime_idele_outside (S : Finset (Primes(ℚ))) :
    ∃ (p : ℕ) (u : ℚˣ), p.Prime ∧ u.val = (p : ℚ) ∧
      let g := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ u
      g ∈ (ideleNorm ℚ).ker ∧ g ∉ (Units.map (integralAdelesOutside ℚ S).subtype.toMonoidHom).range := by
  sorry

end SLocal

end RiemannMasullo
