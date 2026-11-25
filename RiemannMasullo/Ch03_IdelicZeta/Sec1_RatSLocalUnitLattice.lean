module

public import RiemannMasullo.Ch03_IdelicZeta.Sec1_RatSLocalUnitRepresentative
public import RiemannMasullo.AppA_AlgebraicNT.Sec3

/-! # Explicit signed valuation lattice of the actual rational S-unit diagonal

Positive unit compensation realizes every sign and every tuple of integer
valuations. The product formula then gives the exact absolute real coordinate. -/

public noncomputable section
namespace RiemannMasullo.RatFinitePositiveUnitRep
open NumberField IsDedekindDomain InfinitePlace.Completion
open scoped Classical WithZero NNReal NumberField.AdeleRing
local notation "V" => HeightOneSpectrum (𝓞 ℚ)
variable (S : Finset V)

private abbrev loc (v : S) := Units.map (((Pi.evalRingHom _ v).comp
  (RingHom.snd (InfiniteAdeleRing ℚ) ((w : S) → w.val.adicCompletion ℚ))).toMonoidHom)

/-- True denotes positive real sign. The exponent of a local uniformizer is minus the
logarithm of the multiplicative valuation (not plus the logarithm). -/
@[expose] def diagonalCoordinates (d : sProjectedDiagonal ℚ S) : Bool × (S → ℤ) :=
  (decide (0 < realCoord S d.val), fun v ↦ -WithZero.log (Valued.v (d.val.val.2 v)))

private theorem arch_ne (x : (SAdeleRing ℚ S)ˣ) : realCoord S x ≠ 0 :=
  ((Group.isUnit x).map (realCoord S)).ne_zero

private theorem coordinates_fiber (b : Bool) (n : S → ℤ) :
    ∃! d : sProjectedDiagonal ℚ S, diagonalCoordinates S d = (b,n) := by
  choose t ht using fun v : S ↦ v.val.valuedAdicCompletion_surjective ℚ (WithZero.exp (n v))
  have h0 (v : S) : t v ≠ 0 := by
    intro h
    exact WithZero.exp_ne_zero ((ht v).symm.trans (by rw [h, map_zero]))
  let a : (InfiniteAdeleRing ℚ)ˣ := if b then 1 else -1
  let x : (SAdeleRing ℚ S)ˣ := ⟨(a.val,t), (a.inv, fun v ↦ (t v)⁻¹),
    Prod.ext a.val_inv (funext fun v ↦ mul_inv_cancel₀ (h0 v)),
    Prod.ext a.inv_val (funext fun v ↦ inv_mul_cancel₀ (h0 v))⟩
  have ha : realCoord S x = if b then 1 else -1 := by
    cases b
    · change extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (-(1 : Rat.infinitePlace.Completion)) = -1
      simp
    · change extensionEmbeddingOfIsReal Rat.isReal_infinitePlace (1 : Rat.infinitePlace.Completion) = 1
      simp
  have iff_norm (d : sProjectedDiagonal ℚ S) : Normalized S (d.val * x) ↔
      diagonalCoordinates S d = (b,n) := by
    unfold Normalized diagonalCoordinates
    rw [Prod.mk.injEq, map_mul]
    apply and_congr
    · rw [ha]
      have hn := arch_ne S d.val
      cases b
      · simp only [Bool.false_eq_true, ite_false, mul_neg, mul_one, neg_pos]
        constructor
        · intro h
          exact decide_eq_false (not_lt_of_ge h.le)
        · intro h
          exact lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false h)) hn
      · simp
    · rw [funext_iff]
      apply forall_congr' fun v ↦ ?_
      change Valued.v (d.val.val.2 v * t v) = 1 ↔ _
      have hne := (Valuation.ne_zero_iff Valued.v).mpr (loc S v d.val).ne_zero
      change Valued.v (d.val.val.2 v) ≠ 0 at hne
      rw [map_mul, ht, ← WithZero.exp_log hne, ← WithZero.exp_add, ← WithZero.exp_zero]
      simp only [WithZero.exp_inj, WithZero.log_exp]
      omega
  obtain ⟨d, hd, hu⟩ := existsUnique_compensation S x
  exact ⟨d, (iff_norm d).mp hd, fun e he ↦ hu e ((iff_norm e).mpr he)⟩

/-- A reindexing equivalence for sums over the actual projected rational S-unit diagonal. -/
def diagonalEnumeration : (Bool × (S → ℤ)) ≃ sProjectedDiagonal ℚ S :=
  (Equiv.ofBijective (diagonalCoordinates S) ⟨by
    intro d e h
    obtain ⟨a, _, hu⟩ := coordinates_fiber S (diagonalCoordinates S e).1 (diagonalCoordinates S e).2
    exact (hu d h).trans (hu e rfl).symm, by
    rintro ⟨b,n⟩; exact (coordinates_fiber S b n).exists⟩).symm

@[simp] theorem diagonalCoordinates_enumeration (k : Bool × (S → ℤ)) :
    diagonalCoordinates S (diagonalEnumeration S k) = k :=
  (diagonalEnumeration S).symm_apply_apply k

/-- The absolute real coordinate of the indexed diagonal is precisely the product
of residue cardinalities to the (uniformizer-positive) integer exponents. -/
theorem abs_realCoord_enumeration (b : Bool) (n : S → ℤ) :
    |realCoord S (diagonalEnumeration S (b,n)).val| = ∏ v : S, (v.val.asIdeal.absNorm : ℝ) ^ n v := by
  let d := diagonalEnumeration S (b,n)
  have hn (v : S) := congrFun (congrArg Prod.snd (diagonalCoordinates_enumeration S (b,n))) v
  have hq : (QuotientGroup.mk d.val : SIdeleQuotient ℚ S) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr d.property
  have hN : sIdeleNorm ℚ S d.val = 1 := by
    rw [← sIdeleQuotientNorm_mk, hq, map_one]
  have he := congrArg (fun u : ℝ≥0ˣ ↦ (u.val : ℝ)) hN
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, Units.val_mul,
    Units.coe_prod, NNReal.coe_mul, NNReal.coe_prod, Fintype.prod_subsingleton _ Rat.infinitePlace,
    Rat.isReal_infinitePlace.mult_eq_one] at he
  change ‖d.val.val.1 Rat.infinitePlace‖ ^ 1 * (∏ v : S, ‖d.val.val.2 v‖) = 1 at he
  rw [pow_one] at he
  rw [← (isometry_extensionEmbeddingOfIsReal Rat.isReal_infinitePlace).norm_map_of_map_zero
    (map_zero _), Real.norm_eq_abs] at he
  have hf (v : S) : ‖d.val.val.2 v‖ = ((v.val.asIdeal.absNorm : ℝ) ^ n v)⁻¹ := by
    change ‖(loc S v d.val).val‖ = _
    rw [norm_adicCompletion_eq_zpow ℚ v.val (loc S v d.val).ne_zero, ← zpow_neg]
    congr 1
    have hv := hn v
    change -WithZero.log (Valued.v (loc S v d.val).val) = n v at hv
    omega
  simp_rw [hf] at he
  rw [Finset.prod_inv_distrib, ← div_eq_mul_inv] at he
  have hp (v : S) : 0 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val))
  exact (div_eq_one_iff_eq (Finset.prod_ne_zero_iff.mpr fun v _ ↦ zpow_ne_zero _ (hp v).ne')).mp he
end RiemannMasullo.RatFinitePositiveUnitRep
