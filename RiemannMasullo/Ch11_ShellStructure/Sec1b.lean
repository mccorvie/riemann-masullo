module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
public import RiemannMasullo.Ch11_ShellStructure.Sec1a

import all RiemannMasullo.AppA_AlgebraicNT.Sec3

/-!
# S-local carvings

Masullo, §11.1.2, pp. 480–483. A finite set of places in the base records its
finite places, with all archimedean places included throughout.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped Classical NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "μ𝔽" => ideleClassTamagawaMeasure F
local notation "μ₁" => normOneIdeleClassTamagawaMeasure F
local notation "ℬ₀" => ↥(adelePolarSubspace F)
local notation "ℬₛ(" S ")" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "m𝔽" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽 →ₜ* ℝ≥0ˣ)
local notation "norm𝔽" => fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)
local notation "classOf" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)

local instance instIdeleClassMeasurableSpaceSec1b : MeasurableSpace C𝔽 := borel _
local instance instIdeleClassBorelSpaceSec1b : BorelSpace C𝔽 := ⟨rfl⟩
local instance instIdeleClassT2SpaceSec1b : T2Space C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instIdeleClassLocallyCompactSpaceSec1b : LocallyCompactSpace C𝔽 :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instIdeleClassSecondCountableSec1b : SecondCountableTopology C𝔽 :=
  letI := idele_secondCountable F
  inferInstanceAs (SecondCountableTopology
    (I𝔽 ⧸ IdeleGroup.principalSubgroup (𝓞 F) F))
local instance instIdeleClassHaarMeasureSec1b : Measure.IsHaarMeasure μ𝔽 :=
  (ideleClassTamagawaMeasure_isWeil F).1

/-- Paper: (11.1.2.1), p. 480. The indices are the finite sets of places outside
the base set, ordered by inclusion. All the archimedean places are in the base. -/
abbrev SLocalCarvingIndex (S : Finset V) := {T : Finset V // Disjoint S T}

/-- Paper: (11.1.2.1), p. 480. A finite set occurs as an index exactly when
each of its places is outside the base set. -/
theorem exists_sLocalCarvingIndex_iff (S T : Finset V) :
    (∃ i : SLocalCarvingIndex (F := F) S, i.val = T) ↔ ∀ v ∈ T, v ∉ S := by
  constructor
  · rintro ⟨⟨T', h⟩, rfl⟩ v hv hS
    exact Finset.disjoint_left.1 h hS hv
  · intro h
    exact ⟨⟨T, Finset.disjoint_left.2 fun v hS hT ↦ h v hT hS⟩, rfl⟩

/-- Paper: (11.1.2.1), p. 480. There are countably many finite-place indices. -/
theorem countable_sLocalCarvingIndex (S : Finset V) :
    Countable (SLocalCarvingIndex (F := F) S) := by
  have hR : Countable (𝓞 F) := (RingOfIntegers.basis F).repr.injective.countable
  have hV : Countable V := by
    have hfg : ∀ I : Ideal (𝓞 F), ∃ s : Finset (𝓞 F), Ideal.span (s : Set (𝓞 F)) = I :=
      fun I ↦ (IsNoetherian.noetherian I)
    choose g hg using hfg
    have hinj : Injective (fun v : V ↦ g v.asIdeal) := fun a b h ↦
      HeightOneSpectrum.ext (by rw [← hg a.asIdeal, ← hg b.asIdeal]; exact congrArg _ (congrArg _ h))
    exact hinj.countable
  unfold SLocalCarvingIndex
  infer_instance

variable (F) in
/-- Paper: Theorem 11.1.2.1, p. 480. The zero-line ambient space is weighted L²
on the idele classes. It is the singleton-base case of the space used in §10.1. -/
abbrev IdeleClassZeroLineSobolev (s : ℝ) :=
  CompactIntervalSobolev μ𝔽 (fun g ↦ Real.log (norm𝔽 g)) 0 0 s

local notation "W(" s ")" => IdeleClassZeroLineSobolev F s
local notation "ν(" s ")" =>
  (μ𝔽).withDensity (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g))))
local notation "M(" s ", " J ", " hJ ")" => modulatedAbsoluteCutoffOperator m𝔽 (ν(s)) J hJ
local notation "Wω(" s ", " hs ", " ω ")" =>
  actionIsotype ((hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp
    (ideleClassNorm F).ker.subtype) ω

/-- Paper: (11.1.2.2)–(11.1.2.3), p. 480. The two cutoff choices are the
positive half-line and the two-sided band in the idelic norm variable. -/
def sLocalCarvingBand (twoSided : Bool) (Λ : ℝ) : Set ℝ :=
  if twoSided then Icc Λ⁻¹ Λ else Ici Λ⁻¹

/-- Paper: (11.1.2.3), p. 480. Both cutoff bands are Borel. -/
theorem measurableSet_sLocalCarvingBand (twoSided : Bool) (Λ : ℝ) :
    MeasurableSet (sLocalCarvingBand twoSided Λ) := by
  unfold sLocalCarvingBand
  split_ifs
  · exact measurableSet_Icc
  · exact measurableSet_Ici

/-- Paper: (11.1.2.3), p. 480. The half-line retains norm one at radius two
and the bounded band excludes norm three.
Deviation: Sanity check distinguishing the two cutoffs. -/
theorem sLocalCarvingBand_radius_two :
    (1 : ℝ) ∈ sLocalCarvingBand false 2 ∧ (3 : ℝ) ∉ sLocalCarvingBand true 2 := by
  simp only [sLocalCarvingBand, ite_true, ite_false, Bool.false_eq_true, mem_Ici, mem_Icc, not_and,
    not_le]
  constructor <;> norm_num

/-- Paper: (11.1.2.3), p. 480. Homogeneous theta of an adelic test with both
polar values zero is in weighted L² on the zero line. -/
theorem memLp_homogeneousTheta_zeroLine (s : ℝ) (ω : PontryaginDual C₁) (f : ℬ₀) :
    MemLp (homogeneousAdelicTheta ω f.val : C𝔽 → ℂ) 2 (ν(s)) := by
  have hs₀ : (0 : ℝ) ≤ max s 0 := le_max_right _ _
  obtain ⟨j, -, -, hj⟩ :=
    exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := 0) (le_refl (0 : ℝ)) hs₀ ω
  have hf := (mem_adelePolarSubspace f.val).mp f.property
  let x : ↥(globalPolarFreeThetaSubmodule (F := F) ω) :=
    ⟨Submodule.Quotient.mk f.val,
      (mem_globalPolarFreeThetaSubmodule ω _).mpr ⟨f.val, hf.1, hf.2, rfl⟩⟩
  have hx := (hj f x rfl).2.trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽 _))
  have hmem := (Lp.memLp (j x).val.val).ae_eq
    ((withDensity_absolutelyContinuous _ _).ae_le hx)
  refine hmem.mono_measure (withDensity_mono (.of_forall fun g ↦ ?_))
  simp only [Bool.false_eq_true, ite_false]
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg (Real.log (norm𝔽 g))])
    (by linarith [le_max_left s 0])

/-- Paper: (11.1.2.3), p. 480. A global finite-place principal value preserves
the two polar vanishing conditions. -/
theorem adelePrincipalValue_mem_polarSubspace (T : Finset V) (f : ℬ₀) :
    adelePrincipalValue F T f.val ∈ adelePolarSubspace F := by sorry

local notation "P(" T ", " f ")" =>
  (⟨adelePrincipalValue F T (f).val, adelePrincipalValue_mem_polarSubspace T f⟩ : ℬ₀)
local notation "θ(" s ", " ω ", " f ")" =>
  (memLp_homogeneousTheta_zeroLine s ω f).toLp (homogeneousAdelicTheta ω (f).val)

/-- Paper: (11.1.2.5), p. 480. The uncut stage is the closure of the homogeneous
polar-free theta image after applying the selected finite-place principal values.
Deviation: The image is presented by its linear span in the full weighted L² model. -/
def sLocalUncutCarving (s : ℝ) (ω : PontryaginDual C₁) (T : Finset V) :
    Submodule ℂ (W(s)) :=
  (Submodule.span ℂ (range (fun f : ℬ₀ ↦ θ(s, ω, P(T, f))))).topologicalClosure

/-- Conjugating `map id P` by an equivalence gives the identity when `P` fixes every vector.
Stated in the shape of `sAdelePrincipalValue`, so that it applies syntactically. -/
private theorem sLocalUncutCarving_empty_conj_left {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (P : G →ₗ[ℂ] G) (hP : ∀ x, P x = x) :
    e.toLinearMap.comp ((TensorProduct.map (LinearMap.id : E →ₗ[ℂ] E) P).comp
      e.symm.toLinearMap) = LinearMap.id := by
  have hP' : P = LinearMap.id := LinearMap.ext hP
  subst hP'
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
  exact (congrArg e h).trans (e.apply_symm_apply x)

/-- Conjugating `map P id` by an equivalence gives the identity when `P` fixes every vector.
Stated in the shape of `adelePrincipalValue`, so that it applies syntactically. -/
private theorem sLocalUncutCarving_empty_conj_right {E G N : Type*} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (P : E →ₗ[ℂ] E) (hP : ∀ x, P x = x) :
    e.toLinearMap.comp ((TensorProduct.map P (LinearMap.id : G →ₗ[ℂ] G)).comp
      e.symm.toLinearMap) = LinearMap.id := by
  have hP' : P = LinearMap.id := LinearMap.ext hP
  subst hP'
  refine LinearMap.ext fun x ↦ ?_
  have h := LinearMap.congr_fun (TensorProduct.map_id (R := ℂ) (M := E) (N := G)) (e.symm x)
  exact (congrArg e h).trans (e.apply_symm_apply x)

open scoped TensorProduct in
/-- A tensor power of identity maps fixes every vector of the finest locally convex copy. -/
private theorem sLocalUncutCarving_empty_piMap {ι : Type*} [Fintype ι] [DecidableEq ι]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    (f : ∀ i, M i →ₗ[ℂ] M i) (hf : ∀ i, f i = LinearMap.id)
    (x : FinestLocallyConvex (⨂[ℂ] i, M i)) :
    (PiTensorProduct.map f : FinestLocallyConvex (⨂[ℂ] i, M i) →ₗ[ℂ]
      FinestLocallyConvex (⨂[ℂ] i, M i)) x = x := by
  have : f = fun _ ↦ LinearMap.id := funext hf
  subst this
  rw [PiTensorProduct.map_id]
  rfl

/-- With no selected places the S-local principal value is the identity. -/
private theorem sLocalUncutCarving_empty_sPV (h : (∅ : Finset V) ⊆ ∅) :
    sAdelePrincipalValue F h = LinearMap.id := by
  unfold sAdelePrincipalValue
  exact sLocalUncutCarving_empty_conj_left _ _
    (sLocalUncutCarving_empty_piMap _ fun w ↦ absurd w.2 (Finset.notMem_empty _))

/-- With no selected places the global principal value is the identity. -/
private theorem sLocalUncutCarving_empty_PV : adelePrincipalValue F (∅ : Finset V) = LinearMap.id := by
  unfold adelePrincipalValue
  exact sLocalUncutCarving_empty_conj_right _ _ fun x ↦
    LinearMap.congr_fun (sLocalUncutCarving_empty_sPV _) x

/-- Paper: (11.1.2.5), p. 480. The empty stage is the closure of the unrestricted
homogeneous polar-free theta image.
Deviation: Sanity check for the uncut stage. -/
theorem sLocalUncutCarving_empty (s : ℝ) (ω : PontryaginDual C₁) :
    sLocalUncutCarving s ω ∅ =
      (Submodule.span ℂ (range (fun f : ℬ₀ ↦ θ(s, ω, f)))).topologicalClosure := by
  have hP : ∀ f : ℬ₀, adelePrincipalValue F ∅ f.val = f.val := fun f ↦
    LinearMap.ext_iff.mp sLocalUncutCarving_empty_PV f.val
  simp only [sLocalUncutCarving, hP]

/-- The norm-one isotype of the ambient space is closed: it is an intersection of kernels of
continuous operators. -/
private theorem sLocalCutoffCarving_le_cutoffIsotype_closed (s : ℝ) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) : IsClosed (Wω(s, hs, ω) : Set (W(s))) := by
  simp only [actionIsotype, Submodule.coe_iInf]
  refine isClosed_iInter fun g ↦ ?_
  have hc : Continuous fun u : W(s) ↦ ((hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp
      (ideleClassNorm F).ker.subtype) g u - (ω g : ℂ) • u :=
    (((hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs).comp
      (ideleClassNorm F).ker.subtype) g).continuous.sub (continuous_const_smul (ω g : ℂ))
  exact isClosed_eq hc continuous_const

/-- Homogeneous theta of a polar-free test lies in the norm-one isotype of the ambient space:
it is the inclusion of the homogeneous theta class of §10.1, on which norm-one translation acts
by the character. -/
private theorem sLocalCutoffCarving_le_cutoffIsotype_theta (s : ℝ) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) (f : ℬ₀) : θ(s, ω, f) ∈ Wω(s, hs, ω) := by
  obtain ⟨j, -, -, hj⟩ :=
    exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := 0) (le_refl (0 : ℝ)) hs ω
  have hf := (mem_adelePolarSubspace f.val).mp f.property
  let x : ↥(globalPolarFreeThetaSubmodule (F := F) ω) :=
    ⟨Submodule.Quotient.mk f.val,
      (mem_globalPolarFreeThetaSubmodule ω _).mpr ⟨f.val, hf.1, hf.2, rfl⟩⟩
  have hx := (hj f x rfl).2.trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽 _))
  have hx' : ((j x).val.val : C𝔽 → ℂ) =ᵐ[ν(s)] (homogeneousAdelicTheta ω f.val : C𝔽 → ℂ) :=
    (withDensity_absolutelyContinuous _ _).ae_le hx
  have heq : θ(s, ω, f) = (j x).val.val := Lp.ext ((MemLp.coeFn_toLp _).trans hx'.symm)
  have hiso := (mem_actionIsotype _ ω _).mp (j x).property
  have hspec := (exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose_spec.1
  rw [mem_actionIsotype]
  intro h
  rw [heq]
  exact (hspec h.val (j x).val).symm.trans (congrArg Subtype.val (hiso h))

/-- Paper: (11.1.2.5), p. 480. Before any prime condition the uncut stage is the
norm-one isotype of the global theta completion from Definition 10.1.1.1. -/
theorem sLocalUncutCarving_empty_eq_globalThetaSobolev (s : ℝ) (hs : 0 ≤ s)
    (ω : PontryaginDual C₁) :
    sLocalUncutCarving s ω ∅ =
      globalThetaSobolev F 0 (α := 0) (β := 0) le_rfl hs ⊓ Wω(s, hs, ω) := by
  obtain ⟨j, -, hdense, hj⟩ :=
    exists_globalHomogeneousThetaSobolevInclusion (F := F) (a := 0) (le_refl (0 : ℝ)) hs ω
  have hspec := (exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose_spec.1
  -- Every vector of the range of `j` is a homogeneous theta, and conversely.
  have hθ (f : ℬ₀) (x : ↥(globalPolarFreeThetaSubmodule (F := F) ω))
      (hx : x.val = Submodule.Quotient.mk f.val) : θ(s, ω, f) = (j x).val.val := by
    have h := (hj f x hx).2.trans (Filter.EventuallyEq.of_eq (modulationWeight_zero m𝔽 _))
    have h' : ((j x).val.val : C𝔽 → ℂ) =ᵐ[ν(s)] (homogeneousAdelicTheta ω f.val : C𝔽 → ℂ) :=
      (withDensity_absolutelyContinuous _ _).ae_le h
    exact Lp.ext ((MemLp.coeFn_toLp _).trans h'.symm)
  rw [sLocalUncutCarving_empty]
  apply le_antisymm
  · refine Submodule.topologicalClosure_minimal _ ?_
      ((Submodule.isClosed_topologicalClosure _).inter
        (sLocalCutoffCarving_le_cutoffIsotype_closed s hs ω))
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, rfl⟩
    have hf := (mem_adelePolarSubspace f.val).mp f.property
    let x : ↥(globalPolarFreeThetaSubmodule (F := F) ω) :=
      ⟨Submodule.Quotient.mk f.val,
        (mem_globalPolarFreeThetaSubmodule ω _).mpr ⟨f.val, hf.1, hf.2, rfl⟩⟩
    refine ⟨?_, sLocalCutoffCarving_le_cutoffIsotype_theta s hs ω f⟩
    have hm := (j x).val.property
    rw [← hθ f x rfl] at hm
    exact hm
  · intro u hu
    obtain ⟨huH, huW⟩ := Submodule.mem_inf.mp hu
    let y₀ : ↥(globalThetaSobolev F 0 (α := 0) (β := 0) le_rfl hs) := ⟨u, huH⟩
    have hy₀ : y₀ ∈ actionIsotype
        ((exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose.comp
          (ideleClassNorm F).ker.subtype) ω := by
      rw [mem_actionIsotype]
      intro h
      exact Subtype.ext ((hspec h.val y₀).trans ((mem_actionIsotype _ ω u).mp huW h))
    have hι : Continuous fun z : ↥(actionIsotype
        ((exists_globalThetaSobolevAction (F := F) 0 (le_refl (0 : ℝ)) hs).choose.comp
          (ideleClassNorm F).ker.subtype) ω) ↦ (z.val.val : W(s)) :=
      continuous_subtype_val.comp continuous_subtype_val
    let Φ : ℬ₀ → ↥(globalPolarFreeThetaSubmodule (F := F) ω) := fun f ↦
      ⟨Submodule.Quotient.mk f.val, (mem_globalPolarFreeThetaSubmodule ω _).mpr
        ⟨f.val, ((mem_adelePolarSubspace f.val).mp f.property).1,
          ((mem_adelePolarSubspace f.val).mp f.property).2, rfl⟩⟩
    have hΦ : Function.Surjective Φ := by
      intro x
      obtain ⟨f', hf', hx⟩ := x.property
      exact ⟨⟨f', hf'⟩, Subtype.ext hx⟩
    have hd2 : DenseRange (j ∘ Φ) := hdense.comp hΦ.denseRange j.continuous
    have hcl := image_closure_subset_closure_image hι ⟨⟨y₀, hy₀⟩, hd2 _, rfl⟩
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    refine closure_mono ?_ hcl
    rintro _ ⟨_, ⟨f, rfl⟩, rfl⟩
    change (j (Φ f)).val.val ∈ _
    rw [← hθ f (Φ f) rfl]
    exact Submodule.subset_span ⟨f, rfl⟩

/-- Paper: (11.1.2.3), p. 480. The cutoff stage is the closure of the linear
space obtained by applying the cutoff to the restricted theta tests.
Deviation: Read the printed P as the principal value PV used on p. 481. The
definition accepts any measurable norm band, including both in `sLocalCarvingBand`. -/
def sLocalCutoffCarving (s : ℝ) (ω : PontryaginDual C₁) (T : Finset V)
    (J : Set ℝ) (hJ : MeasurableSet J) : Submodule ℂ (W(s)) :=
  (Submodule.span ℂ (range (fun f : ℬ₀ ↦ M(s, J, hJ) (θ(s, ω, P(T, f)))))).topologicalClosure

/-- The absolute cutoff commutes with translation by a norm-one class, which does not move
the idelic norm. -/
private theorem sLocalCutoffCarving_le_cutoffIsotype_comm (s : ℝ) (hs : 0 ≤ s)
    (J : Set ℝ) (hJ : MeasurableSet J) (h : C₁) (u : W(s)) :
    M(s, J, hJ) (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val u) =
      hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val (M(s, J, hJ) u) := by
  have hn : Continuous norm𝔽 :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hdens : Continuous (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Continuous.rpow_const (f := fun x : ℝ ↦ 1 + x ^ 2) (by fun_prop)
        fun x ↦ Or.inl (by positivity))
  have hpos (g : C𝔽) : 0 < intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)) :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hνμ : ν(s) ≪ μ𝔽 := withDensity_absolutelyContinuous _ _
  have hμν : μ𝔽 ≪ ν(s) := withDensity_absolutelyContinuous'
    ((hdens.measurable.comp (Real.measurable_log.comp hn.measurable)).ennreal_ofReal.aemeasurable)
    (.of_forall fun g ↦ (ENNReal.ofReal_pos.mpr (hpos g)).ne')
  let c : C𝔽 → ℂ := fun g ↦ (modulatedAbsoluteCutoff m𝔽 J g : ℂ)
  have hc (g : C𝔽) : c (h.val⁻¹ * g) = c g := by
    have hh : ideleClassNorm F h.val = 1 := h.property
    have hng : ((m𝔽 (h.val⁻¹ * g)).val : ℝ) = ((m𝔽 g).val : ℝ) := by
      change ((ideleClassNorm F (h.val⁻¹ * g)).val : ℝ) = ((ideleClassNorm F g).val : ℝ)
      rw [map_mul, map_inv, hh, inv_one, one_mul]
    simp only [c, modulatedAbsoluteCutoff, Set.indicator_apply, Set.mem_preimage, hng, Pi.one_apply]
  have hq := (measurePreserving_mul_left μ𝔽 h.val⁻¹).quasiMeasurePreserving
  have hT (v : W(s)) := hardySobolevTranslation_apply μ𝔽 m𝔽 0 0 s le_rfl hs h.val v
  have hM (v : W(s)) := modulatedAbsoluteCutoffOperator_apply m𝔽 (ν(s)) J hJ v
  refine Lp.ext ?_
  have hL : (M(s, J, hJ) (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val u) : C𝔽 → ℂ)
      =ᵐ[ν(s)] fun g ↦ c g * u (h.val⁻¹ * g) := by
    filter_upwards [hM (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val u),
      hνμ.ae_le (hT u)] with g h1 h2
    rw [h1, h2]
  have hR : (hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val (M(s, J, hJ) u) : C𝔽 → ℂ)
      =ᵐ[ν(s)] fun g ↦ c g * u (h.val⁻¹ * g) := by
    have h3 := hq.ae_eq_comp (hμν.ae_le (hM u))
    filter_upwards [hνμ.ae_le (hT (M(s, J, hJ) u)), hνμ.ae_le h3] with g h1 h2
    rw [h1]
    simp only [Function.comp_apply] at h2
    rw [h2]
    exact congrArg (· * u (h.val⁻¹ * g)) (hc g)
  exact hL.trans hR.symm

/-- Paper: (11.1.2.3), p. 480. Each finite cutoff stage belongs to the cutoff
image of the ambient norm-one isotype. -/
theorem sLocalCutoffCarving_le_cutoffIsotype (s : ℝ) (hs : 0 ≤ s) (ω : PontryaginDual C₁)
    (T : Finset V) (J : Set ℝ) (hJ : MeasurableSet J) :
    sLocalCutoffCarving s ω T J hJ ≤ (Wω(s, hs, ω)).map (M(s, J, hJ)).toLinearMap := by
  have hproj := modulatedAbsoluteCutoffOperator_projection m𝔽 (ν(s)) J hJ
  have hidem : ∀ y, M(s, J, hJ) (M(s, J, hJ) y) = M(s, J, hJ) y := fun y ↦
    congrArg (fun L : W(s) →L[ℂ] W(s) ↦ L y) hproj.1.isIdempotentElem.eq
  -- The image of the isotype is the isotype intersected with the range, which is closed.
  have himage : (((Wω(s, hs, ω)).map (M(s, J, hJ)).toLinearMap : Submodule ℂ (W(s))) :
        Set (W(s))) = (Wω(s, hs, ω) : Set (W(s))) ∩ (range (M(s, J, hJ)) : Set (W(s))) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, z, rfl⟩
      rw [SetLike.mem_coe, mem_actionIsotype] at hz ⊢
      intro h
      change hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val (M(s, J, hJ) z) = _
      rw [← sLocalCutoffCarving_le_cutoffIsotype_comm s hs J hJ h z]
      have hz' := hz h
      change hardySobolevTranslation μ𝔽 m𝔽 0 0 s le_rfl hs h.val z = _ at hz'
      rw [hz', map_smul]
      rfl
    · rintro ⟨hy, z, rfl⟩
      exact ⟨M(s, J, hJ) z, hy, hidem z⟩
  have hclosed : IsClosed (((Wω(s, hs, ω)).map (M(s, J, hJ)).toLinearMap : Submodule ℂ (W(s))) :
      Set (W(s))) := by
    rw [himage]
    exact (sLocalCutoffCarving_le_cutoffIsotype_closed s hs ω).inter hproj.2
  refine Submodule.topologicalClosure_minimal _ ?_ hclosed
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨f, rfl⟩
  exact ⟨_, sLocalCutoffCarving_le_cutoffIsotype_theta s hs ω _, rfl⟩

private theorem hardySobolevCutoff_univ_aux {A : Type*} [MeasurableSpace A] {μ : Measure A}
    (U : Set A) (hU : MeasurableSet U) (hUu : U = univ) (f : Lp ℂ 2 μ) :
    hardySobolevCutoff hU f = f := by
  subst hUu
  refine Lp.ext ?_
  unfold hardySobolevCutoff
  filter_upwards [MemLp.coeFn_toLp ((Lp.memLp f).indicator hU.nullMeasurableSet)] with x hx
  rw [hx]
  simp

/-- Paper: (11.1.2.3), p. 480. The full norm band leaves the uncut stage unchanged.
Deviation: Sanity check for the cutoff-stage definition. -/
theorem sLocalCutoffCarving_univ (s : ℝ) (ω : PontryaginDual C₁) (T : Finset V) :
    sLocalCutoffCarving s ω T univ MeasurableSet.univ = sLocalUncutCarving s ω T := by
  have h : ∀ x : W(s), M(s, univ, MeasurableSet.univ) x = x := fun x ↦
    (modulatedAbsoluteCutoffOperator_eq_hardySobolevCutoff m𝔽 (ν(s)) univ MeasurableSet.univ x).trans
      (hardySobolevCutoff_univ_aux _ _ (preimage_univ) x)
  simp only [sLocalCutoffCarving, sLocalUncutCarving, h]

/-- Paper: (11.1.2.4), p. 480. The cofinal limit is the intersection of all
finite-place cutoff stages outside the base set. -/
def sLocalCarvingLimit (s : ℝ) (ω : PontryaginDual C₁) (S : Finset V)
    (J : Set ℝ) (hJ : MeasurableSet J) : Submodule ℂ (W(s)) :=
  ⨅ i : SLocalCarvingIndex (F := F) S, sLocalCutoffCarving s ω i.val J hJ

/-- Paper: Remark 11.1.2.2, p. 480. A cofinal sequence increases by inclusion
and exhausts the finite places outside the base set. -/
def IsSLocalCarvingCofinal {S : Finset V} (A : ℕ → SLocalCarvingIndex (F := F) S) : Prop :=
  Monotone A ∧ (⋃ k, ((A k).val : Set V)) = (S : Set V)ᶜ

/-- Paper: Remark 11.1.2.2, p. 480. An increasing sequence exhausts the outside
places exactly when every finite set of them is contained in some term. -/
theorem isSLocalCarvingCofinal_iff {S : Finset V} (A : ℕ → SLocalCarvingIndex (F := F) S) :
    IsSLocalCarvingCofinal A ↔ Monotone A ∧ ∀ i : SLocalCarvingIndex (F := F) S, ∃ k, i ≤ A k := by
  unfold IsSLocalCarvingCofinal
  refine and_congr_right fun hA ↦ ⟨fun h i ↦ ?_, fun h ↦ ?_⟩
  · have hv : ∀ v ∈ i.val, ∃ k, v ∈ (A k).val := fun v hv ↦ by
      have : v ∈ (S : Set V)ᶜ := fun hS ↦ Finset.disjoint_left.mp i.2 hS hv
      rw [← h] at this
      simpa using this
    choose! k hk using hv
    refine ⟨i.val.sup k, fun v hv' ↦ ?_⟩
    exact hA (Finset.le_sup (f := k) hv') (hk v hv')
  · refine Set.Subset.antisymm ?_ ?_
    · intro v hv
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hv
      intro hS
      exact Finset.disjoint_left.mp (A k).2 (by simpa using hS) hk
    · intro v hv
      obtain ⟨k, hk⟩ := h ⟨{v}, by simpa using hv⟩
      exact Set.mem_iUnion.mpr ⟨k, hk (Finset.mem_singleton_self v)⟩

/-- The finite places of a number field form a countable type: their ideals are
finitely generated over the countable ring of integers. -/
private theorem exists_sLocalCarvingCofinal_countable (K : Type*) [Field K] [NumberField K] :
    Countable (HeightOneSpectrum (𝓞 K)) := by
  have : Countable K := (Module.finBasis ℚ K).equivFun.injective.countable
  have : Countable (𝓞 K) := (RingOfIntegers.coe_injective (K := K)).countable
  have h : Surjective (fun s : Finset (𝓞 K) ↦ Ideal.span (s : Set (𝓞 K))) :=
    fun I ↦ IsNoetherian.noetherian I
  have : Countable (Ideal (𝓞 K)) := h.countable
  exact (show Injective (HeightOneSpectrum.asIdeal (R := 𝓞 K)) from fun _ _ h ↦
    HeightOneSpectrum.ext h).countable

/-- Paper: Remark 11.1.2.2, p. 480. Every base admits a cofinal sequence
of finite sets of outside places. -/
theorem exists_sLocalCarvingCofinal (S : Finset V) :
    ∃ A : ℕ → SLocalCarvingIndex (F := F) S, IsSLocalCarvingCofinal A := by
  have := exists_sLocalCarvingCofinal_countable F
  let := Encodable.ofCountable V
  refine ⟨fun k ↦ ⟨((Finset.range k).biUnion fun n ↦ (Encodable.decode₂ V n).toFinset) \ S,
    Finset.disjoint_sdiff⟩, ?_, ?_⟩
  · intro a b hab
    exact Finset.sdiff_subset_sdiff
      (Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_subset_range.2 hab)) le_rfl
  · ext v
    simp only [Set.mem_iUnion, Finset.mem_coe, Finset.mem_sdiff, Finset.mem_biUnion,
      Finset.mem_range, Option.mem_toFinset, Set.mem_compl_iff]
    constructor
    · rintro ⟨k, _, h⟩
      exact h
    · intro h
      exact ⟨Encodable.encode v + 1,
        ⟨Encodable.encode v, Nat.lt_succ_self _, Encodable.mem_decode₂.2 rfl⟩, h⟩

 
open scoped TensorProduct in
/-- Two linear maps agree once they agree on the pure tensors of an
inductive tensor product with a finite tensor product. -/
private theorem sLocalCutoffCarving_antitone_extPi {ι : Type*} [Fintype ι] {E N : Type*}
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] N) (L₁ L₂ : N →ₗ[ℂ] N)
    (h : ∀ (a : E) (g : ∀ i, M i), L₁ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i))) = L₂ (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) :
    L₁ = L₂ := by
  have key : ∀ y : E ⊗[ℂ] (⨂[ℂ] i, M i), L₁ (e y) = L₂ (e y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      exact (congrArg L₁ (map_zero e)).trans ((map_zero L₁).trans
        ((map_zero L₂).symm.trans (congrArg L₂ (map_zero e)).symm))
    | tmul a b =>
      induction b using PiTensorProduct.induction_on with
      | smul_tprod r g =>
        rw [show a ⊗ₜ[ℂ] (r • PiTensorProduct.tprod ℂ g) = r • (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g)
            from TensorProduct.tmul_smul r a _,
          show e (r • (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g)) =
            r • e (a ⊗ₜ[ℂ] PiTensorProduct.tprod ℂ g) from map_smul e r _,
          map_smul, map_smul, h]
      | add b c hb hc =>
        rw [TensorProduct.tmul_add]
        exact (congrArg L₁ (map_add e _ _)).trans ((map_add L₁ _ _).trans
          ((congrArg₂ (· + ·) hb hc).trans ((map_add L₂ _ _).symm.trans
            (congrArg L₂ (map_add e _ _)).symm)))
    | add y z hy hz =>
      exact (congrArg L₁ (map_add e y z)).trans ((map_add L₁ _ _).trans
        ((congrArg₂ (· + ·) hy hz).trans ((map_add L₂ _ _).symm.trans
          (congrArg L₂ (map_add e y z)).symm)))
  refine LinearMap.ext fun x ↦ ?_
  calc L₁ x = L₁ (e (e.symm x)) := by rw [e.apply_symm_apply]
    _ = L₂ (e (e.symm x)) := key (e.symm x)
    _ = L₂ x := by rw [e.apply_symm_apply]

/-- The S-local principal values compose over disjoint sets of selected places. -/
private theorem sLocalCutoffCarving_antitone_sPV {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') :
    sAdelePrincipalValue F (Finset.Subset.refl T') =
      (sAdelePrincipalValue F hT).comp (sAdelePrincipalValue F (Finset.sdiff_subset (s := T') (t := T))) := by
  refine sLocalCutoffCarving_antitone_extPi (sAdeleSchwartz_inductiveTensor_equiv F T').choose _ _ fun a g ↦ ?_
  have h1 := sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl T') a g
  have h2 := sAdelePrincipalValue_tmul (F := F) (Finset.sdiff_subset (s := T') (t := T)) a g
  have h3 := sAdelePrincipalValue_tmul (F := F) hT a
    (fun w : T' ↦ if (w : HeightOneSpectrum (𝓞 F)) ∈ T' \ T then
      finitePlacePrincipalValue (F := F) w.val (g w) else g w)
  refine h1.trans ?_
  refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (sAdelePrincipalValue F hT) h2.symm)
  refine Eq.trans ?_ h3.symm
  apply congrArg
  apply congrArg
  apply congrArg
  funext w
  by_cases hw : (w : HeightOneSpectrum (𝓞 F)) ∈ T
  · simp [hw, w.2, Finset.mem_sdiff]
  · simp [hw, w.2, Finset.mem_sdiff]

/-- Two linear maps agree once they agree on the pure tensors of an inductive tensor product. -/
private theorem sLocalCutoffCarving_antitone_extTail {E G N : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (L₁ L₂ : N →ₗ[ℂ] N)
    (h : ∀ (a : E) (b : G), L₁ (e (a ⊗ₜ[ℂ] b)) = L₂ (e (a ⊗ₜ[ℂ] b))) :
    L₁ = L₂ := by
  have key : ∀ y : TensorProduct ℂ E G, L₁ (e y) = L₂ (e y) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero =>
      exact (congrArg L₁ (map_zero e)).trans ((map_zero L₁).trans
        ((map_zero L₂).symm.trans (congrArg L₂ (map_zero e)).symm))
    | tmul a b => exact h a b
    | add y z hy hz =>
      exact (congrArg L₁ (map_add e y z)).trans ((map_add L₁ _ _).trans
        ((congrArg₂ (· + ·) hy hz).trans ((map_add L₂ _ _).symm.trans
          (congrArg L₂ (map_add e y z)).symm)))
  refine LinearMap.ext fun x ↦ ?_
  calc L₁ x = L₁ (e (e.symm x)) := by rw [e.apply_symm_apply]
    _ = L₂ (e (e.symm x)) := key (e.symm x)
    _ = L₂ x := by rw [e.apply_symm_apply]

/-- The global principal value at a larger set is the one at the smaller set after the one
at the difference. -/
private theorem sLocalCutoffCarving_antitone_PV {T T' : Finset (HeightOneSpectrum (𝓞 F))} (hT : T ⊆ T') :
    adelePrincipalValue F T' =
      (adelePrincipalValue F T).comp (adelePrincipalValue F (T' \ T)) := by
  refine sLocalCutoffCarving_antitone_extTail (sAdeleTailSchwartz_inductiveTensor_equiv F T').choose _ _ fun a b ↦ ?_
  have h1 := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl T') a b
  have h2 := adelePrincipalValue_tmul (F := F) (Finset.sdiff_subset (s := T') (t := T)) a b
  have h3 := adelePrincipalValue_tmul (F := F) hT
    (sAdelePrincipalValue F (Finset.sdiff_subset (s := T') (t := T)) a) b
  refine h1.trans ?_
  refine Eq.trans ?_ (LinearMap.comp_apply _ _ _).symm
  refine Eq.trans ?_ (congrArg (adelePrincipalValue F T) h2.symm)
  refine Eq.trans ?_ h3.symm
  apply congrArg
  apply congrArg₂ _ _ rfl
  exact (LinearMap.ext_iff.mp (sLocalCutoffCarving_antitone_sPV hT) a).trans (LinearMap.comp_apply _ _ _)

/-- Generic range inclusion: no project definitions occur, so nothing is unfolded. -/
private theorem sLocalCutoffCarving_antitone_range {A β : Type*} [AddCommMonoid A] [Module ℂ A]
    (B : Submodule ℂ A) (Φ : B → β) (L L' R : A → A)
    (h : ∀ f : B, L f.val ∈ B) (h' : ∀ f : B, L' f.val ∈ B) (hR : ∀ f : B, R f.val ∈ B)
    (hc : ∀ f : B, L (R f.val) = L' f.val) :
    range (fun f : B ↦ Φ ⟨L' f.val, h' f⟩) ⊆ range (fun f : B ↦ Φ ⟨L f.val, h f⟩) := by
  rintro _ ⟨f, rfl⟩
  exact ⟨⟨R f.val, hR f⟩, congrArg Φ (Subtype.ext (hc f))⟩

/-- Paper: (11.1.2.12), p. 481. Adding finite-place conditions gives a smaller
cutoff stage in the inclusion order.
Deviation: The monotonicity applies to any measurable norm band. -/
theorem sLocalCutoffCarving_antitone (s : ℝ) (ω : PontryaginDual C₁)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    Antitone (fun T : Finset V ↦ sLocalCutoffCarving s ω T J hJ) := by
  intro T T' hTT'
  have hP : ∀ f : ℬ₀, adelePrincipalValue F T (adelePrincipalValue F (T' \ T) f.val) =
      adelePrincipalValue F T' f.val := fun f ↦
    ((LinearMap.ext_iff.mp (sLocalCutoffCarving_antitone_PV hTT') f.val).trans
      (LinearMap.comp_apply _ _ _)).symm
  show sLocalCutoffCarving s ω T' J hJ ≤ sLocalCutoffCarving s ω T J hJ
  unfold sLocalCutoffCarving
  have key := sLocalCutoffCarving_antitone_range (adelePolarSubspace F)
    (fun g : ℬ₀ ↦ M(s, J, hJ) (θ(s, ω, g)))
    (adelePrincipalValue F T) (adelePrincipalValue F T') (adelePrincipalValue F (T' \ T))
    (adelePrincipalValue_mem_polarSubspace T) (adelePrincipalValue_mem_polarSubspace T')
    (adelePrincipalValue_mem_polarSubspace (T' \ T)) hP
  with_reducible exact Submodule.topologicalClosure_mono (Submodule.span_mono key)

local notation "ωOf(" χ ")" =>
  (χ).comp (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ :
    C₁ →ₜ* C𝔽)
local notation "Unramified(" χ ", " S ")" => ideleClassNormTwist χ 0 ∈ unramifiedOutside F S
local notation "TrivialPic(" S ")" => Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) S F))
local notation "DegreeBound(" s ")" => 2 * (Module.finrank ℚ F : ℝ) ≤ s
local notation "J(" b ", " Λ ")" => sLocalCarvingBand b Λ
local notation "hJ(" b ", " Λ ")" => measurableSet_sLocalCarvingBand b Λ

/-- Paper: Theorem 11.1.2.1(1), p. 480, and (11.1.2.13)–(11.1.2.15),
pp. 481–482. Every cofinal sequence realizes the same limit by intersection.
Deviation: Equality to the intersection over all indices also gives a sanity
check for the sequence-independent definition. -/
theorem sLocalCarvingLimit_eq_iInf {S : Finset V} (s : ℝ) (ω : PontryaginDual C₁)
    (J : Set ℝ) (hJ : MeasurableSet J)
    (A : ℕ → SLocalCarvingIndex (F := F) S) (_hA : IsSLocalCarvingCofinal A) :
    sLocalCarvingLimit s ω S J hJ = ⨅ k, sLocalCutoffCarving s ω (A k).val J hJ := by
  unfold sLocalCarvingLimit
  apply le_antisymm
  · exact le_iInf fun k ↦ iInf_le _ (A k)
  · refine le_iInf fun i ↦ ?_
    obtain ⟨k, hik⟩ := ((isSLocalCarvingCofinal_iff A).1 _hA).2 i
    exact (iInf_le _ k).trans (sLocalCutoffCarving_antitone s ω J hJ hik)

/-- Paper: Theorem 11.1.2.1(1), p. 480. The cofinal limit is closed in the
ambient weighted L² space. -/
theorem isClosed_sLocalCarvingLimit (S : Finset V) (s : ℝ) (ω : PontryaginDual C₁)
    (J : Set ℝ) (hJ : MeasurableSet J) :
    IsClosed (sLocalCarvingLimit s ω S J hJ : Set (W(s))) := by
  rw [sLocalCarvingLimit, Submodule.coe_iInf]
  exact isClosed_iInter fun i ↦ Submodule.isClosed_topologicalClosure _

/-- Paper: Theorem 11.1.2.1(1), p. 480. The cofinal limit lies in the image
of the ambient isotype under the cutoff. -/
theorem sLocalCarvingLimit_le_cutoffIsotype {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (_hΛ : 0 < Λ) :
    let hs₀ : 0 ≤ s := (mul_nonneg zero_le_two (Nat.cast_nonneg _)).trans hs
    sLocalCarvingLimit s (ωOf(χ)) S (J(twoSided, Λ)) (hJ(twoSided, Λ)) ≤
      (Wω(s, hs₀, ωOf(χ))).map (M(s, J(twoSided, Λ), hJ(twoSided, Λ))).toLinearMap := by
  intro hs₀
  exact (iInf_le _ (⟨∅, Finset.disjoint_empty_right S⟩ : SLocalCarvingIndex (F := F) S)).trans
    (sLocalCutoffCarving_le_cutoffIsotype _ _ _ _ _ _)

-- TODO(paper-gap): On p. 482 the basis conclusion of Theorem 11.2.0.2
-- requires s ≥ 2 * card(i'), while (11.1.2.2) bounds the field degree.
-- A direct proof can use a Mellin evaluation at a new Euler zero if one
-- exhibits a polar-free test on which the smaller stage has nonzero value.

/-- Paper: Theorem 11.1.2.1(2), p. 480, (11.1.2.5). If the larger stage adds
a place over a rational prime absent at the smaller stage, the inclusion of the
uncut completions is strict. -/
theorem sLocalUncutCarving_lt {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (_hs : DegreeBound(s)) (i i' : SLocalCarvingIndex (F := F) S) (_hii' : i < i')
    (_hp : ∃ p : ℕ, p.Prime ∧
      (∀ v ∈ i.val, (p : 𝓞 F) ∉ v.asIdeal) ∧ ∃ v ∈ i'.val, (p : 𝓞 F) ∈ v.asIdeal) :
    sLocalUncutCarving s (ωOf(χ)) i'.val < sLocalUncutCarving s (ωOf(χ)) i.val := by sorry

/-- Paper: Theorem 11.1.2.1(2), p. 480, (11.1.2.6). The cutoff stages
are nested under the inclusion order of their finite-place indices.
Deviation: The inclusion permits equality. The printed subsequence claim fails
for the bounded cutoffs over ℚ, already when one prime is added. -/
theorem sLocalCutoffCarving_le {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (_hs : DegreeBound(s)) (i i' : SLocalCarvingIndex (F := F) S) (_hii' : i ≤ i')
    (twoSided : Bool) (Λ : ℝ) (_hΛ : 0 < Λ) :
    let J := J(twoSided, Λ)
    let hJ : MeasurableSet J := hJ(twoSided, Λ)
    sLocalCutoffCarving s (ωOf(χ)) i'.val J hJ ≤
      sLocalCutoffCarving s (ωOf(χ)) i.val J hJ := by
  exact sLocalCutoffCarving_antitone s (ωOf(χ)) _ _ _hii'

-- TODO(paper-gap): In (11.1.2.16) eventual equality gives equality at all
-- earlier radii by applying their nested cutoffs. The representatives can vary
-- with the radius, so strong convergence on fixed inputs gives no contradiction.

/-- Paper: (11.1.2.7), p. 480. The local test is extended to ideles by
multiplying by the indicator of integer units at every place outside S. -/
def sLocalCarvingIdeleTest (S : Finset V) (f : ℬₛ(S)) : I𝔽 → ℂ :=
  {g : I𝔽 | ∀ v ∉ S, Valued.v (g.val.2 v) = 1}.indicator
    (fun g ↦ f (Multiplicative.ofAdd (adeleProjection F S g.val)))

/-- Paper: (11.1.2.7), p. 480. At the identity idele the outside unit factor
is one.
Deviation: Sanity check for extension by the outside unit factor. -/
theorem sLocalCarvingIdeleTest_one (S : Finset V) (f : ℬₛ(S)) :
    sLocalCarvingIdeleTest S f 1 = f (Multiplicative.ofAdd 1) := by
  have h1 : (1 : I𝔽) ∈ {g : I𝔽 | ∀ v ∉ S, Valued.v (g.val.2 v) = 1} := fun v _ ↦ by
    show Valued.v (1 : v.adicCompletion F) = 1
    exact map_one _
  rw [sLocalCarvingIdeleTest, Set.indicator_of_mem h1]
  simp

/-- Paper: (11.1.2.7), p. 480. The raw theta generator sums the extended local
test over nonzero principal multiples of an idele representing the class. -/
def sLocalCarvingTheta (S : Finset V) (f : ℬₛ(S)) (g : C𝔽) : ℂ :=
  ideleThetaSum (sLocalCarvingIdeleTest S f) g.out

/-- The raw theta value at a class is the orbit series at any representative: changing the
representative by a principal idele reindexes the series over `Fˣ`. -/
private theorem sLocalCarvingTheta_classOf (S : Finset V) (f : ℬₛ(S)) (g : I𝔽) :
    sLocalCarvingTheta S f (classOf g) = ideleThetaSum (sLocalCarvingIdeleTest S f) g := by
  unfold sLocalCarvingTheta
  obtain ⟨⟨h, η, rfl⟩, he⟩ :=
    QuotientGroup.mk_out_eq_mul (IdeleGroup.principalSubgroup (𝓞 F) F) g
  change ideleThetaSum _ (QuotientGroup.mk g : C𝔽).out = _
  rw [he]
  unfold ideleThetaSum
  refine Eq.trans ?_ ((Equiv.mulRight η).tsum_eq fun ξ ↦
    sLocalCarvingIdeleTest S f (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g))
  refine tsum_congr fun ξ ↦ congrArg _ ?_
  rw [Equiv.coe_mulRight, map_mul]
  change IdeleGroup.unitEmbedding (𝓞 F) F ξ * (g * IdeleGroup.unitEmbedding (𝓞 F) F η) = _
  rw [mul_comm g, mul_assoc]

/-- Outside `S`, the valuation of a principal translate is the valuation of the field element
times the valuation of the idele. -/
private theorem sLocalCarvingTheta_spec_valuation (g : I𝔽) (ξ : Fˣ) (v : V) :
    Valued.v ((IdeleGroup.unitEmbedding (𝓞 F) F ξ * g).val.2 v) =
      v.valuation F (ξ : F) * Valued.v (g.val.2 v) := by
  change Valued.v ((algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ : F)) v * g.val.2 v) = _
  rw [Valuation.map_mul]
  congr 1
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (ξ : F)

/-- If one principal translate of `g` is a unit outside `S`, then another one is exactly when
the ratio of the field elements is an S-unit. -/
private theorem sLocalCarvingTheta_spec_mem (S : Finset V) (g : I𝔽) (ξ₀ ξ : Fˣ)
    (h₀ : IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * g ∈
      {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1}) :
    IdeleGroup.unitEmbedding (𝓞 F) F ξ * g ∈ {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1} ↔
      ξ * ξ₀⁻¹ ∈ (S : Set V).unit F := by
  refine forall₂_congr fun v hv ↦ ?_
  have h0 := h₀ v hv
  rw [sLocalCarvingTheta_spec_valuation] at h0 ⊢
  have hξ₀ : v.valuation F (ξ₀ : F) ≠ 0 := by simp
  change _ ↔ v.valuation F ((ξ : F) * ((ξ₀⁻¹ : Fˣ) : F)) = 1
  rw [map_mul, Units.val_inv_eq_inv_val, map_inv₀]
  constructor
  · intro h
    rw [← h0] at h
    exact (mul_inv_eq_one₀ hξ₀).mpr (mul_right_cancel₀ (by
      intro h'; rw [h', mul_zero] at h0; exact zero_ne_one h0) h)
  · intro h
    rw [(mul_inv_eq_one₀ hξ₀).mp h]
    exact h0

/-- The orbit series of the extended local test is absolutely summable: its nonzero terms lie on
one coset of the S-units, where they form the S-local theta series at an S-idele. -/
private theorem sLocalCarvingTheta_spec_summable (S : Finset V) (f : ℬₛ(S)) (g : I𝔽) :
    Summable (fun ξ : Fˣ ↦ sLocalCarvingIdeleTest S f
      (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g)) := by
  by_cases hex : ∃ ξ₀ : Fˣ, IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * g ∈
      {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1}
  swap
  · push Not at hex
    refine summable_zero.congr fun ξ ↦ ?_
    unfold sLocalCarvingIdeleTest
    rw [Set.indicator_of_notMem (hex ξ)]
  obtain ⟨ξ₀, h₀⟩ := hex
  let P : Set Fˣ := ((S : Set V).unit F : Set Fˣ)
  let h : Fˣ → ℂ := fun ξ ↦ f (Multiplicative.ofAdd (adeleProjection F S
    (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g).val))
  have hterm (ξ : Fˣ) : sLocalCarvingIdeleTest S f (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g) =
      P.indicator (fun ξ ↦ h (ξ * ξ₀)) (ξ * ξ₀⁻¹) := by
    unfold sLocalCarvingIdeleTest
    by_cases hξ : ξ * ξ₀⁻¹ ∈ P
    · rw [Set.indicator_of_mem ((sLocalCarvingTheta_spec_mem S g ξ₀ ξ h₀).mpr hξ),
        Set.indicator_of_mem hξ, inv_mul_cancel_right]
    · rw [Set.indicator_of_notMem (mt (sLocalCarvingTheta_spec_mem S g ξ₀ ξ h₀).mp hξ),
        Set.indicator_of_notMem hξ]
  refine (summable_congr hterm).mpr ?_
  refine ((Equiv.mulRight ξ₀⁻¹).summable_iff (f := P.indicator fun ξ ↦ h (ξ * ξ₀))).mpr ?_
  refine summable_subtype_iff_indicator.mp ?_
  let g'' : (SAdeleRing F S)ˣ :=
    Units.map (adeleProjection F S).toMonoidHom (IdeleGroup.unitEmbedding (𝓞 F) F ξ₀ * g)
  have hS := ((sLocalAdelicTheta_hasSumUniformlyOn F S f {g''} isCompact_singleton).hasSum
    (Set.mem_singleton g'')).summable
  have hG : Summable (fun u : ((S : Set V).integer F)ˣ ↦
      h (((Set.unitEquivUnitsInteger (S : Set V) F).symm u : Fˣ) * ξ₀)) := by
    refine hS.congr fun u ↦ congrArg f (congrArg Multiplicative.ofAdd ?_)
    simp only [map_mul, Units.val_mul]
    rw [mul_assoc]
    rfl
  refine (((Set.unitEquivUnitsInteger (S : Set V) F).toEquiv.summable_iff).mpr hG).congr
    fun x ↦ ?_
  simp

/-- Paper: (11.1.2.7), p. 480. At any representative of the class the displayed
orbit series is absolutely convergent and gives the raw theta generator. -/
theorem sLocalCarvingTheta_spec (S : Finset V) (f : ℬₛ(S)) (g : I𝔽) :
    Summable (fun ξ : Fˣ ↦ sLocalCarvingIdeleTest S f
      (IdeleGroup.unitEmbedding (𝓞 F) F ξ * g)) ∧
    sLocalCarvingTheta S f (classOf g) = ideleThetaSum (sLocalCarvingIdeleTest S f) g :=
  ⟨sLocalCarvingTheta_spec_summable S f g, sLocalCarvingTheta_classOf S f g⟩

/-- The S-component of an inserted S-idele is the S-idele itself. -/
private theorem sLocalCarvingTheta_sIdeleInsertion_proj (S : Finset V) (g : (SAdeleRing F S)ˣ) :
    adeleProjection F S (sIdeleInsertion F S g).val = g.val := by
  obtain ⟨h1, h2, -⟩ := sIdeleInsertion_apply F S g
  exact Prod.ext h1 (funext fun v ↦ h2 v)

/-- At an inserted S-idele, the outside unit condition on a principal translate holds exactly
for the S-units. -/
private theorem sLocalCarvingTheta_sIdeleInsertion_mem (S : Finset V) (g : (SAdeleRing F S)ˣ)
    (ξ : Fˣ) :
    (IdeleGroup.unitEmbedding (𝓞 F) F ξ * sIdeleInsertion F S g ∈
      {g' : I𝔽 | ∀ v ∉ S, Valued.v (g'.val.2 v) = 1}) ↔ ξ ∈ (S : Set V).unit F := by
  refine forall₂_congr fun v hv ↦ ?_
  have h1 : (IdeleGroup.unitEmbedding (𝓞 F) F ξ * sIdeleInsertion F S g).val.2 v =
      ((ξ : F) : v.adicCompletion F) := by
    change (algebraMap F (FiniteAdeleRing (𝓞 F) F) (ξ : F)) v * (sIdeleInsertion F S g).val.2 v = _
    rw [(sIdeleInsertion_apply F S g).2.2 v (by exact_mod_cast hv), mul_one]
    rfl
  rw [h1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation']

/-- Paper: (11.1.2.7), p. 480. At an inserted S-idele the outside unit condition
selects exactly the S-units, giving the S-local theta of Definition 2.3.1.1. -/
theorem sLocalCarvingTheta_sIdeleInsertion (S : Finset V) (f : ℬₛ(S)) (g : (SAdeleRing F S)ˣ) :
    sLocalCarvingTheta S f (classOf (sIdeleInsertion F S g)) = sLocalAdelicTheta F S f g := by
  rw [sLocalCarvingTheta_classOf, sLocalAdelicTheta_apply]
  unfold ideleThetaSum
  let P : Set Fˣ := ((S : Set V).unit F : Set Fˣ)
  let h : Fˣ → ℂ := fun ξ ↦ f (Multiplicative.ofAdd (adeleProjection F S
    (IdeleGroup.unitEmbedding (𝓞 F) F ξ * sIdeleInsertion F S g).val))
  have hterm (ξ : Fˣ) : sLocalCarvingIdeleTest S f
      (IdeleGroup.unitEmbedding (𝓞 F) F ξ * sIdeleInsertion F S g) = P.indicator h ξ := by
    unfold sLocalCarvingIdeleTest
    by_cases hξ : ξ ∈ P
    · rw [Set.indicator_of_mem ((sLocalCarvingTheta_sIdeleInsertion_mem S g ξ).mpr hξ),
        Set.indicator_of_mem hξ]
    · rw [Set.indicator_of_notMem (mt (sLocalCarvingTheta_sIdeleInsertion_mem S g ξ).mp hξ),
        Set.indicator_of_notMem hξ]
  rw [tsum_congr hterm, ← tsum_subtype P h]
  refine Eq.trans ?_ ((Set.unitEquivUnitsInteger (S : Set V) F).toEquiv.tsum_eq _)
  refine tsum_congr fun x ↦ congrArg f (congrArg Multiplicative.ofAdd ?_)
  rw [Units.val_mul, Units.val_mul, map_mul, sLocalCarvingTheta_sIdeleInsertion_proj]
  rfl

/-- Paper: (11.1.2.7), p. 480. The raw theta is integrable on each norm-one
coset against a continuous norm-one character.
Deviation: This is the integrability needed for the character projection. -/
theorem integrable_sLocalCarvingTheta_normOne (S : Finset V) (ω : PontryaginDual C₁)
    (f : ℬₛ(S)) (g : C𝔽) :
    Integrable (fun h : C₁ ↦ sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ)) μ₁ := by sorry

/-- Paper: (11.1.2.7), p. 480. Average the raw theta generator against the
norm-one character and then apply the cutoff.
Deviation: The norm-one average places the generator in the claimed isotype. -/
def sLocalCarvingGenerator (S : Finset V) (ω : PontryaginDual C₁)
    (J : Set ℝ) (f : ℬₛ(S)) : C𝔽 → ℂ :=
  (norm𝔽 ⁻¹' J).indicator (fun g ↦ ∫ h : C₁,
    sLocalCarvingTheta S f (h.val * g) * (ω h : ℂ) ∂μ₁)

/-- Paper: (11.1.2.7), p. 480. For the trivial norm-one character the average
of a norm-one-invariant generator multiplies its cutoff by the Haar mass.
Deviation: Sanity check for the character average in the repaired generator. -/
theorem sLocalCarvingGenerator_trivial (S : Finset V) (J : Set ℝ) (f : ℬₛ(S))
    (_hf : ∀ (h : C₁) (g : C𝔽), sLocalCarvingTheta S f (h.val * g) = sLocalCarvingTheta S f g) :
    sLocalCarvingGenerator S 1 J f =
      fun g ↦ (μ₁).real univ • (norm𝔽 ⁻¹' J).indicator (sLocalCarvingTheta S f) g := by
  funext g
  unfold sLocalCarvingGenerator
  by_cases hg : g ∈ norm𝔽 ⁻¹' J
  · simp only [Set.indicator_of_mem hg, _hf]
    simp [integral_const]
  · simp [Set.indicator_of_notMem hg]

/-- Paper: Theorem 11.1.2.1(3), p. 480. The projected cutoff generators are
square-integrable for the zero-line weight. -/
theorem memLp_sLocalCarvingGenerator {S : Finset V} (χ : PontryaginDual C𝔽)
    (_hχ : Unramified(χ, S)) (_hPic : TrivialPic((S : Set V)))
    (s : ℝ) (_hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (_hΛ : 0 < Λ)
    (f : ℬₛ(S)) (_hf : f (Multiplicative.ofAdd 0) = 0)
    (_hFf : sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0) :
    MemLp (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f) 2 (ν(s)) := by sorry

-- TODO(paper-gap): Page 483 uses R_{Λ,S} without defining it. Both spans in
-- the quotient already have Fourier value zero. The argument still needs to
-- approximate every vector of the intersection by projected local generators.

/-- Paper: Theorem 11.1.2.1(3), p. 480. The cofinal limit is the closed span of
the projected cutoff theta functions of local tests whose value and Fourier value
at zero vanish.
Deviation: Use the norm-one character average in (11.1.2.7). The closure is
taken in the full weighted L² space, where the cutoff isotype is closed. -/
theorem sLocalCarvingLimit_eq_closedSpan {S : Finset V} (χ : PontryaginDual C𝔽)
    (hχ : Unramified(χ, S)) (hPic : TrivialPic((S : Set V)))
    (s : ℝ) (hs : DegreeBound(s)) (twoSided : Bool) (Λ : ℝ) (hΛ : 0 < Λ) :
    sLocalCarvingLimit s (ωOf(χ)) S (J(twoSided, Λ)) (hJ(twoSided, Λ)) = (Submodule.span ℂ {u : W(s) |
      ∃ (f : ℬₛ(S)) (hf : f (Multiplicative.ofAdd 0) = 0)
        (hFf : sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0),
        u = (memLp_sLocalCarvingGenerator χ hχ hPic s hs twoSided Λ hΛ f hf hFf).toLp
          (sLocalCarvingGenerator S (ωOf(χ)) (J(twoSided, Λ)) f)}).topologicalClosure := by sorry

/-- The L² norm of a vector of a weighted L² space that agrees almost everywhere with the
restriction of another vector to a measurable set is the weighted integral of the square of
the other vector over the set. -/
private theorem sLocalCarving_cutoff_norm_aux {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (w : A → ℝ) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x) (E : Set A) (hE : MeasurableSet E)
    (u v : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x)))
    (hv : (v : A → ℂ) =ᵐ[μ.withDensity fun x ↦ ENNReal.ofReal (w x)] E.indicator (u : A → ℂ)) :
    IntegrableOn (fun x ↦ ‖u x‖ ^ 2 * w x) E μ ∧
      ‖v‖ = Real.sqrt (∫ x in E, ‖u x‖ ^ 2 * w x ∂μ) := by
  have hd : Measurable fun x ↦ ENNReal.ofReal (w x) := hw.ennreal_ofReal
  have hfin : ∀ᵐ x ∂μ, ENNReal.ofReal (w x) < ⊤ := .of_forall fun _ ↦ ENNReal.ofReal_lt_top
  have hreal (x : A) : (ENNReal.ofReal (w x)).toReal = w x := ENNReal.toReal_ofReal (hw0 x)
  have hsq (f : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x))) : Integrable (fun x ↦ ‖f x‖ ^ 2) (μ.withDensity fun x ↦ ENNReal.ofReal (w x)) := by
    have h := (Lp.memLp f).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h
  have hu : Integrable (fun x ↦ ‖u x‖ ^ 2 * w x) μ := by
    have h := (integrable_withDensity_iff_integrable_smul' hd hfin).mp (hsq u)
    refine h.congr (.of_forall fun x ↦ ?_)
    simp only [hreal, smul_eq_mul, mul_comm]
  refine ⟨hu.integrableOn, ?_⟩
  have hnorm : ‖v‖ ^ 2 = ∫ x, ‖v x‖ ^ 2 ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner v v)]
    congr 1
    funext x
    exact inner_self_eq_norm_sq (𝕜 := ℂ) (v x)
  have hint : ∫ x, ‖v x‖ ^ 2 ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) = ∫ x in E, ‖u x‖ ^ 2 * w x ∂μ := by
    calc ∫ x, ‖v x‖ ^ 2 ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) = ∫ x, E.indicator (fun x ↦ ‖u x‖ ^ 2) x ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) := by
          refine integral_congr_ae (hv.mono fun x hx ↦ ?_)
          change ‖v x‖ ^ 2 = _
          rw [hx]
          by_cases hxE : x ∈ E
          · simp [hxE]
          · simp [hxE]
      _ = ∫ x in E, ‖u x‖ ^ 2 ∂(μ.withDensity fun x ↦ ENNReal.ofReal (w x)) := integral_indicator hE
      _ = ∫ x in E, (ENNReal.ofReal (w x)).toReal • ‖u x‖ ^ 2 ∂μ :=
          setIntegral_withDensity_eq_setIntegral_toReal_smul₀ hd.aemeasurable (ae_restrict_of_ae hfin) _ hE
      _ = _ := by
          refine setIntegral_congr_fun hE fun x _ ↦ ?_
          simp only [hreal, smul_eq_mul, mul_comm]
  rw [← hint, ← hnorm, Real.sqrt_sq (norm_nonneg v)]

/-- Paper: (11.1.2.8)–(11.1.2.9), p. 481. The cutoff norm is the weighted
L² norm restricted to the idelic norm band.
Deviation: For the two-sided cutoff the integral is over the bounded band. -/
theorem sLocalCarving_cutoff_norm (s : ℝ) (twoSided : Bool) (Λ : ℝ) (u : W(s)) :
    let E := norm𝔽 ⁻¹' J(twoSided, Λ)
    let integrand := fun g : C𝔽 ↦ ‖u g‖ ^ 2 * (1 + Real.log (norm𝔽 g) ^ 2) ^ (s / 2)
    IntegrableOn integrand E μ𝔽 ∧
      ‖M(s, J(twoSided, Λ), hJ(twoSided, Λ)) u‖ =
        Real.sqrt (∫ g in E, integrand g ∂μ𝔽) := by
  intro E integrand
  have hn : Continuous norm𝔽 :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (isProperMap_ideleClassNorm F).continuous)
  have hdens : Continuous (intervalSobolevDensity 0 0 s) := by
    unfold intervalSobolevDensity
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).max
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul
      (Continuous.rpow_const (f := fun x : ℝ ↦ 1 + x ^ 2) (by fun_prop)
        fun x ↦ Or.inl (by positivity))
  have hm : Measurable fun g : C𝔽 ↦ intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)) :=
    hdens.measurable.comp (Real.measurable_log.comp hn.measurable)
  have hw0 (g : C𝔽) : 0 ≤ intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)) :=
    mul_nonneg (le_max_of_le_left (Real.exp_pos _).le) (Real.rpow_nonneg (by positivity) _)
  have hv : (M(s, J(twoSided, Λ), hJ(twoSided, Λ)) u : C𝔽 → ℂ) =ᵐ[ν(s)] E.indicator (u : C𝔽 → ℂ) := by
    refine (modulatedAbsoluteCutoffOperator_apply m𝔽 (ν(s)) _ _ u).trans (.of_forall fun g ↦ ?_)
    by_cases hg : g ∈ E
    · have hg' : ((m𝔽 g).val : ℝ) ∈ J(twoSided, Λ) := hg
      simp [modulatedAbsoluteCutoff, indicator, hg, hg']
    · have hg' : ((m𝔽 g).val : ℝ) ∉ J(twoSided, Λ) := hg
      simp [modulatedAbsoluteCutoff, indicator, hg, hg']
  have h := sLocalCarving_cutoff_norm_aux μ𝔽
    (fun g ↦ intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g))) hm hw0 E
    (hn.measurable (hJ(twoSided, Λ))) u _ hv
  have hw (g : C𝔽) : intervalSobolevDensity 0 0 s (Real.log (norm𝔽 g)) =
      (1 + Real.log (norm𝔽 g) ^ 2) ^ (s / 2) := by
    simp [intervalSobolevDensity]
  simp only [hw] at h
  exact h

/-- Paper: (11.1.2.10)–(11.1.2.11), p. 481. The image under the cutoff of the
completed uncut stage lies in the cutoff stage, and its closure is the cutoff stage.
Deviation: The equality takes the closure of the image of the completed stage.
The argument in print establishes density there. -/
theorem sLocalCutoffCarving_eq_closure_map (s : ℝ) (ω : PontryaginDual C₁)
    (T : Finset V) (J : Set ℝ) (hJ : MeasurableSet J) :
    sLocalCutoffCarving s ω T J hJ =
      ((sLocalUncutCarving s ω T).map (M(s, J, hJ)).toLinearMap).topologicalClosure := by
  have closureImage {E G ι : Type _} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
      [ContinuousAdd E] [ContinuousSMul ℂ E] [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
      [ContinuousAdd G] [ContinuousSMul ℂ G] (L : E →L[ℂ] G) (f : ι → E) :
      (Submodule.span ℂ (range (fun i ↦ L (f i)))).topologicalClosure =
        ((Submodule.span ℂ (range f)).topologicalClosure.map L.toLinearMap).topologicalClosure := by
    let B := Submodule.span ℂ (range f)
    have h : Submodule.span ℂ (range (fun i ↦ L (f i))) = B.map L.toLinearMap :=
      (congrArg (Submodule.span ℂ) (Set.range_comp' (L : E → G) f)).trans
        (Submodule.map_span L.toLinearMap (range f)).symm
    refine (congrArg Submodule.topologicalClosure h).trans (le_antisymm ?_ ?_)
    · exact Submodule.topologicalClosure_mono (Submodule.map_mono B.le_topologicalClosure)
    · exact Submodule.topologicalClosure_minimal _ (B.topologicalClosure_map L) (Submodule.isClosed_topologicalClosure _)
  dsimp only [sLocalCutoffCarving, sLocalUncutCarving, IdeleClassZeroLineSobolev, CompactIntervalSobolev, Bool.false_eq_true, ite_false]
  with_reducible_and_instances
    exact closureImage (E := Lp ℂ 2 (ν(s))) (G := Lp ℂ 2 (ν(s))) (ι := ℬ₀)
      (M(s, J, hJ)) (fun g : ℬ₀ ↦ θ(s, ω, P(T, g)))

-- TODO(paper-gap): For (11.1.2.11), closed range of the cutoff on the ambient space
-- does not establish closed range on each completed uncut stage.

end RiemannMasullo
