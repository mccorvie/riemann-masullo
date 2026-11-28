module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2
public import RiemannMasullo.Ch03_IdelicZeta.Sec1_RatSLocalUnitLattice

/-! # The actual rational standard unramified theta tensor

On the genuine positive unit transversal, the selected finite factors pick
exactly the nonnegative valuation cone. Summation over the two real signs
therefore gives the exact real theta series over the prime-power lattice. -/

public noncomputable section
namespace RiemannMasullo.RatUnramifiedThetaLattice
open NumberField IsDedekindDomain RatFinitePositiveUnitRep
open scoped Classical WithZero NumberField.AdeleRing

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))

section TensorEvaluation

variable {S : Finset V}
local notation "U" => (Set.integer (S : Set V) ℚ)ˣ
local notation "diag" => sUnitEmbedding ℚ S
local notation "rc" => InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace

/-- Integral diagonal S-units, including both signs. -/
abbrev integralUnits (S : Finset V) : Set (Set.integer (S : Set V) ℚ)ˣ :=
  {u | ∀ v : S, Valued.v ((sUnitEmbedding ℚ S u).val.2 v) ≤ 1}

abbrev latticeRadius (n : S → ℕ) : ℝ := ∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ n v

variable (f : B∞) (phi : ℝ → ℂ)
  (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = phi (rc (a Rat.infinitePlace)))
  (x : (SAdeleRing ℚ S)ˣ) (hx : Normalized S x)

include hf hx in
private theorem term (u : U) :
    sLocalStandardThetaTensor (F := ℚ) (S := S) 1 f (Multiplicative.ofAdd (diag u * x).val) =
      if u ∈ integralUnits S then phi (realCoord S x * realCoord S (diag u)) else 0 := by
  classical
  rw [sLocalStandardThetaTensor_apply, hf]
  have hfin (v : S) : finiteStandardGaussian v.val (sLocalFiniteRestriction v (1 : QuasiCharacter (SIdeleQuotient ℚ S)))
      (Multiplicative.ofAdd ((diag u * x).val.2 v)) =
      if Valued.v ((diag u).val.2 v) ≤ 1 then 1 else 0 := by
    change finiteStandardGaussianValue _ _ _ = _
    rw [finiteStandardGaussianValue]
    have ht : ∀ a ∈ (v.val.adicCompletionIntegers ℚ).units,
        sLocalFiniteRestriction v (1 : QuasiCharacter (SIdeleQuotient ℚ S)) a = 1 := by
      intro a _
      rfl
    rw [ite_eq_left ht, Set.indicator_apply]
    have hm : Multiplicative.toAdd (Multiplicative.ofAdd ((diag u * x).val.2 v)) ∈
        ((v.val.adicCompletionIntegers ℚ) : Set _) ↔ Valued.v ((diag u).val.2 v) ≤ 1 := by
      change Valued.v ((diag u).val.2 v * x.val.2 v) ≤ 1 ↔ _
      rw [map_mul, hx.2 v, mul_one]
    simp only [hm]
  simp_rw [hfin]
  by_cases hu : u ∈ integralUnits S
  · rw [ite_eq_left hu]
    simp only [ite_eq_left (hu _), Finset.prod_const_one, mul_one]
    change phi (realCoord S (diag u * x)) = _
    rw [map_mul, mul_comm]
  · rw [ite_eq_right hu]
    change ¬ ∀ v : S, Valued.v ((diag u).val.2 v) ≤ 1 at hu
    obtain ⟨v, hv⟩ := not_forall.mp hu
    rw [Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_right hv), mul_zero]

include hf hx in
/-- The arithmetic input only enumerates actual integral diagonal units and identifies
their signed real coordinates. No convergence or theta evaluation is assumed. -/
private theorem hasSum (e : ((S → ℕ) × Bool) ≃ integralUnits S)
    (he : ∀ n b, realCoord S (diag (e (n,b)).val) =
      if b then latticeRadius n else -latticeRadius n) :
    HasSum (fun n : S → ℕ ↦ phi (realCoord S x * latticeRadius n) +
      phi (-(realCoord S x * latticeRadius n)))
      (sLocalAdelicThetaOnClasses ℚ S (sLocalStandardThetaTensor 1 f) (QuotientGroup.mk x)) := by
  classical
  let F (u : U) := sLocalStandardThetaTensor (F := ℚ) (S := S) 1 f
    (Multiplicative.ofAdd (diag u * x).val)
  have hterm := term f phi hf x hx
  have hsupp : Function.support F ⊆ integralUnits S := by
    intro u hu
    by_contra h
    exact hu ((hterm u).trans (ite_eq_right h))
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  have hs : HasSum F (∑' u, F u) :=
    (sLocalAdelicTheta_hasSumUniformlyOn ℚ S (sLocalStandardThetaTensor 1 f) {x}
      isCompact_singleton).hasSum rfl
  have hsub := (hasSum_subtype_iff_of_support_subset hsupp).mpr hs
  have hpair : HasSum (fun p ↦ F (e p).val) (∑' u, F u) := e.hasSum_iff.mpr hsub
  apply hpair.prod_fiberwise
  intro n
  convert (hasSum_fintype (fun b : Bool ↦ F (e (n,b)).val)) using 1
  simp only [Fintype.sum_bool, F, hterm, ite_eq_left (e _).property, he, Bool.false_eq_true,
    ite_false, ite_true, mul_neg]

end TensorEvaluation

section IntegralCone

variable (S : Finset V)
local notation "U" => (Set.integer (S : Set V) ℚ)ˣ
local notation "H" => sProjectedDiagonal ℚ S
local notation "diag" => sUnitEmbedding ℚ S

private def toDiagonal (u : U) : H := ⟨diag u, ⟨_, ⟨u, rfl⟩, rfl⟩⟩

private theorem realCoord_diag (u : U) : realCoord S (diag u) = (u.val.val : ℚ) := by
  change InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace
    (algebraMap ℚ Rat.infinitePlace.Completion (u.val.val : ℚ)) = _
  simp

private def unitDiagonal : U ≃ H := Equiv.ofBijective (toDiagonal S) ⟨by
  intro u v h
  apply Units.ext
  apply Subtype.ext
  have h' := congrArg (fun d : H ↦ realCoord S d.val) h
  change realCoord S (diag u) = realCoord S (diag v) at h'
  rw [realCoord_diag, realCoord_diag] at h'
  exact_mod_cast h', by
  intro d
  obtain ⟨u, hu⟩ := (sIdeleQuotient_mk_eq_one ℚ S d.val).mp
    ((QuotientGroup.eq_one_iff _).mpr d.property)
  exact ⟨u, Subtype.ext hu.symm⟩⟩

private def kcoord (u : U) : Bool × (S → ℤ) :=
  diagonalCoordinates S (unitDiagonal S u)

private theorem valuation_unit_nonzero (u : U) (v : S) : Valued.v ((diag u).val.2 v) ≠ 0 := by
  let e := (Pi.evalRingHom (fun w : S ↦ w.val.adicCompletion ℚ) v).comp
    (RingHom.snd (InfiniteAdeleRing ℚ) ((w : S) → w.val.adicCompletion ℚ))
  exact (Valuation.ne_zero_iff _).mpr (Units.map e.toMonoidHom (diag u)).ne_zero

private theorem mem_integral_iff (u : U) : u ∈ integralUnits S ↔ ∀ v, 0 ≤ (kcoord S u).2 v := by
  change (∀ v : S, Valued.v ((diag u).val.2 v) ≤ 1) ↔ _
  apply forall_congr' fun v ↦ ?_
  change Valued.v ((diag u).val.2 v) ≤ 1 ↔ 0 ≤ -WithZero.log (Valued.v ((diag u).val.2 v))
  rw [← WithZero.exp_log (valuation_unit_nonzero S u v), WithZero.log_exp, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

private def ofCoords (c : Bool × (S → ℤ)) : U := (unitDiagonal S).symm (diagonalEnumeration S c)

private theorem coord_ofCoords (c : Bool × (S → ℤ)) : kcoord S (ofCoords S c) = c := by
  simp [kcoord, ofCoords, diagonalCoordinates_enumeration]

private theorem injective_kcoord : Function.Injective (kcoord S) := by
  intro u v h
  apply (unitDiagonal S).injective
  obtain ⟨a, ha⟩ := (diagonalEnumeration S).surjective (unitDiagonal S u)
  obtain ⟨b, hb⟩ := (diagonalEnumeration S).surjective (unitDiagonal S v)
  change diagonalCoordinates S (unitDiagonal S u) = diagonalCoordinates S (unitDiagonal S v) at h
  rw [← ha, ← hb, diagonalCoordinates_enumeration, diagonalCoordinates_enumeration] at h
  rw [← ha, ← hb, h]

/-- Exact natural-lattice indexing of the integral rational S-units, with both signs. -/
def integralUnitEnumeration : ((S → ℕ) × Bool) ≃ integralUnits S :=
  Equiv.ofBijective (fun c ↦ ⟨ofCoords S (c.2, fun v ↦ (c.1 v : ℤ)),
    (mem_integral_iff S _).mpr (by rw [coord_ofCoords]; exact fun v ↦ Int.natCast_nonneg _)⟩) (by
    constructor
    · rintro ⟨n,b⟩ ⟨n',b'⟩ h
      have h' := congrArg (fun u : integralUnits S ↦ kcoord S u.val) h
      simp only [coord_ofCoords] at h'
      refine Prod.ext (funext fun v ↦ ?_) (congrArg Prod.fst h')
      have hv : (n v : ℤ) = (n' v : ℤ) := congrFun (congrArg Prod.snd h') v
      exact Int.ofNat_inj.mp hv
    · intro u
      let c := kcoord S u.val
      refine ⟨⟨fun v ↦ (c.2 v).toNat, c.1⟩, Subtype.ext ((injective_kcoord S) ?_)⟩
      rw [coord_ofCoords]
      exact Prod.ext rfl (funext fun v ↦ Int.toNat_of_nonneg ((mem_integral_iff S u.val).mp u.property v)))

private theorem exact_integral_signedCoord (n : S → ℕ) (b : Bool) :
    realCoord S (diag (integralUnitEnumeration S (n,b)).val) =
      if b then latticeRadius n else -latticeRadius n := by
  let c : Bool × (S → ℤ) := (b, fun v ↦ (n v : ℤ))
  let d := diagonalEnumeration S c
  have hd : (unitDiagonal S (integralUnitEnumeration S (n,b)).val : H) = d := by
    change unitDiagonal S ((unitDiagonal S).symm d) = d
    exact Equiv.apply_symm_apply _ _
  change realCoord S (unitDiagonal S (integralUnitEnumeration S (n,b)).val).val = _
  rw [hd]
  have habs := abs_realCoord_enumeration S b c.2
  have hsign := congrArg Prod.fst (diagonalCoordinates_enumeration S c)
  change decide (0 < realCoord S d.val) = b at hsign
  change |realCoord S d.val| = ∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ (n v : ℤ) at habs
  simp only [zpow_natCast] at habs
  cases b
  · have h : ¬ 0 < realCoord S d.val := of_decide_eq_false hsign
    rw [abs_of_nonpos (le_of_not_gt h)] at habs
    simpa only [Bool.false_eq_true, ite_false] using neg_eq_iff_eq_neg.mp habs
  · have h : 0 < realCoord S d.val := of_decide_eq_true hsign
    simpa only [abs_of_pos h, ite_true] using habs

/-- The true rational unramified theta of the standard finite-place tensor unfolds
into the sum of the two real signs over the ordinary nonnegative valuation lattice. -/
theorem actual_unramified_theta_hasSum (f : B∞) (phi : ℝ → ℂ)
    (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = phi
      (InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (a Rat.infinitePlace)))
    (x : (SAdeleRing ℚ S)ˣ) (hx : Normalized S x) :
    HasSum (fun n : S → ℕ ↦ phi (realCoord S x * latticeRadius n) +
      phi (-(realCoord S x * latticeRadius n)))
      (sLocalAdelicThetaOnClasses ℚ S (sLocalStandardThetaTensor 1 f) (QuotientGroup.mk x)) :=
  hasSum f phi hf x hx (integralUnitEnumeration S) (exact_integral_signedCoord S)


end IntegralCone

end RiemannMasullo.RatUnramifiedThetaLattice
