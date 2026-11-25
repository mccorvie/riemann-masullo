module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3b
import RiemannMasullo.AppA_AlgebraicNT.Sec2
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Finite order up to a norm twist for rational idèle characters -/

@[expose] public noncomputable section

open Function IsDedekindDomain NumberField Topology
open InfinitePlace.Completion
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

local notation "RatFinitePlace" => HeightOneSpectrum (𝓞 ℚ)
local notation "RatIntegralUnits" => (v : RatFinitePlace) → (v.adicCompletionIntegers ℚ)ˣ
local notation "Crat" => IdeleClassGroup (𝓞 ℚ) ℚ

/-- On a compact totally disconnected group the kernel of a unitary character
contains an open subgroup of finite index. -/
private theorem compact_torsion_of_totallyDisconnected
    {U : Type*} [CommGroup U] [TopologicalSpace U] [IsTopologicalGroup U]
    [T2Space U] [CompactSpace U] [TotallyDisconnectedSpace U] (ψ : PontryaginDual U) :
    ∃ n : ℕ, 0 < n ∧ ∀ u, ψ u ^ n = 1 := by
  have hopen := (Circle.isOpen_centeredArc (Real.pi / 2)).preimage ψ.continuous
  have hone : (1 : U) ∈ ψ ⁻¹' Circle.centeredArc (Real.pi / 2) := by
    change ψ 1 ∈ Circle.centeredArc (Real.pi / 2)
    rw [map_one, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨H, _, hH⟩ := exists_compact_openSubgroup_sub_mem_nhds (hopen.mem_nhds hone)
  have hker (u : U) (hu : u ∈ H) : ψ u = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    rw [← map_pow]
    exact hH (H.pow_mem hu n)
  refine ⟨H.toSubgroup.index, Nat.card_pos, fun u ↦ ?_⟩
  rw [← map_pow]
  exact hker _ (H.toSubgroup.pow_index_mem u)

/-- The positive coordinate of (A.2.2.3) is the idelic norm. -/
private theorem ratClass_norm_of_integral_components
    {t : ℝ≥0ˣ} {u : RatIntegralUnits} {g : IdeleGroup (𝓞 ℚ) ℚ}
    (harchRep : extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (g.val.1 Rat.infinitePlace) = t.val)
    (hf : ∀ v, g.val.2 v = (u v).val.val) :
    ((ideleNorm ℚ g).val : ℝ) = (t.val : ℝ) := by
  have hfin (v : RatFinitePlace) : ‖g.val.2 v‖ = 1 := by
    rw [hf v]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom (u v))).mp
        ⟨(u v).val.property, (u v).inv.property⟩
  have harch := (isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _) (g.val.1 Rat.infinitePlace)
  rw [((ideleNorm_spec ℚ).1 g).2, Fintype.prod_subsingleton _ Rat.infinitePlace,
    finprod_eq_one_of_forall_eq_one hfin, mul_one, ← harch, harchRep]
  simp [InfinitePlace.mult, Rat.isReal_infinitePlace]

/-- Paper: Equation (A.2.2.3), p. 546. Every unitary rational idèle class character agrees,
after a common positive power, with an imaginary power of the idelic norm. -/
theorem ratIdeleClassCharacter_pow_eq_norm_pow (η : PontryaginDual Crat) :
    ∃ (κ : ℝ) (N : ℕ), 0 < N ∧ ∀ x : Crat,
      (η x : ℂ) ^ N = (((((ideleClassNorm ℚ x : ℝ≥0) : ℝ) : ℂ) ^
        ((κ : ℂ) * Complex.I)) ^ N) := by
  classical
  let (v : RatFinitePlace) : CompactSpace (v.adicCompletionIntegers ℚ) :=
    compactSpace_adicCompletionIntegers v
  let (v : RatFinitePlace) : TotallyDisconnectedSpace (v.adicCompletionIntegers ℚ)ˣ :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  obtain ⟨e, he⟩ := ratIdeleClassGroup_decomposition
  let ja : ℝ≥0ˣ →ₜ* Crat := ⟨e.toMonoidHom.comp (MonoidHom.inl _ _),
    e.continuous.comp (continuous_id.prodMk continuous_const)⟩
  let ju : RatIntegralUnits →ₜ* Crat := ⟨e.toMonoidHom.comp (MonoidHom.inr _ _),
    e.continuous.comp (continuous_const.prodMk continuous_id)⟩
  let a := η.comp ja
  let b := η.comp ju
  obtain ⟨N, hN, hb⟩ := compact_torsion_of_totallyDisconnected b
  let c : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
  obtain ⟨z, ⟨hz, ha⟩, _⟩ := existsUnique_unitaryComplexPower (c.comp a)
    (fun t ↦ (a t).norm_coe)
  have hzi : z = (z.im : ℂ) * Complex.I := by
    simpa only [hz, Complex.ofReal_zero, zero_add] using (Complex.re_add_im z).symm
  have ha' (t : ℝ≥0ˣ) : (a t : ℂ) = (((t.val : ℝ) : ℂ) ^ ((z.im : ℂ) * Complex.I)) :=
    hzi ▸ ha t
  refine ⟨z.im, N, hN, ?_⟩
  intro x
  obtain ⟨⟨t, u⟩, rfl⟩ := e.surjective x
  obtain ⟨g, harchRep, hf, heg⟩ := he t u
  have hn : ((ideleClassNorm ℚ (e (t, u))).val : ℝ) = (t.val : ℝ) := by
    rw [heg]
    exact ratClass_norm_of_integral_components harchRep hf
  have hsplit : η (e (t, u)) = a t * b u := by
    change η (e (t, u)) = η (e (t, 1)) * η (e (1, u))
    rw [← map_mul, ← map_mul]
    simp
  have hb' : (b u : ℂ) ^ N = 1 := by
    exact (Circle.coe_pow (b u) N).symm.trans
      ((congrArg (fun v : Circle ↦ (v : ℂ)) (hb u)).trans Circle.coe_one)
  rw [hsplit, Circle.coe_mul, mul_pow, hb', mul_one, ha', hn]

/-- Paper: Remark 3.3.1.6, p. 135, and Equation (A.2.2.3), p. 546. Extending a rational
S-local character gives one imaginary norm power and one positive integer exponent that
agree after powering on the entire S-idèle quotient. -/
theorem ratSLocalCharacter_pow_eq_norm_pow {S : Finset RatFinitePlace}
    (χ : PontryaginDual (SIdeleQuotient ℚ S)) :
    ∃ (κ : ℝ) (N : ℕ), 0 < N ∧ ∀ x : SIdeleQuotient ℚ S,
      (χ x : ℂ) ^ N = (((((sIdeleQuotientNorm ℚ S x : ℝ≥0) : ℝ) : ℂ) ^
        ((κ : ℂ) * Complex.I)) ^ N) := by
  obtain ⟨η, _, hext, _⟩ := sLocal_character_extension χ
  obtain ⟨κ, N, hN, hη⟩ := ratIdeleClassCharacter_pow_eq_norm_pow η
  refine ⟨κ, N, hN, ?_⟩
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  let y : Crat := QuotientGroup.mk (sIdeleInsertion ℚ S g)
  have hχ : (η y : ℂ) = (χ (QuotientGroup.mk g) : ℂ) := by
    have h := DFunLike.congr_fun hext (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at h
    change (η y : ℂ) * _ ^ (0 : ℂ) = (χ (QuotientGroup.mk g) : ℂ) * _ ^ (0 : ℂ) at h
    simpa only [Complex.cpow_zero, mul_one] using h
  have hn : ideleClassNorm ℚ y = sIdeleQuotientNorm ℚ S (QuotientGroup.mk g) :=
    ideleNorm_sIdeleInsertion ℚ S g
  simpa only [hχ, hn] using hη y

end RiemannMasullo
