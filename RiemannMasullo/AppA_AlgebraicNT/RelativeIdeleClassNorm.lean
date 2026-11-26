module

public import RiemannMasullo.AppA_AlgebraicNT.Sec2

/-!
# The relative norm of idele classes

For a number field of degree `d`, rational finite-order characters agreeing after
norm pullback on the norm-one classes have equal `d`-th powers. This applies the
relative determinant norm of Lemma A.2.2.2, p. 546.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Function NumberField IsDedekindDomain Topology
open scoped Classical NNReal NumberField.AdeleRing

variable (F : Type*) [Field F] [NumberField F]

local notation "𝕀[" E "]" => IdeleGroup (𝓞 E) E
local notation "ιF" => Module.Free.ChooseBasisIndex ℤ (𝓞 F)
local notation "dQ" => algebraMap ℚ 𝔸[ℚ]
local notation "dL" => algebraMap F 𝔸[F]

local notation "C[" E "]" => IdeleClassGroup (𝓞 E) E
local notation "principal(" E ")" => IdeleGroup.principalSubgroup (𝓞 E) E

private theorem relativeIdeleClassNormRat_diagonal (x : F) :
    letI := (rationalAdeleEmbedding F).toAlgebra
    Algebra.norm 𝔸[ℚ] (dL x) = dQ (Algebra.norm ℚ x) := by
  let := (rationalAdeleEmbedding F).toAlgebra
  obtain ⟨b, hb⟩ := exists_adelicIntegralBasis F
  rw [Algebra.norm_eq_matrix_det b, Algebra.norm_eq_matrix_det (integralBasis F), RingHom.map_det]
  congr 1
  ext i j
  change (Algebra.leftMulMatrix b (dL x)) i j = dQ ((Algebra.leftMulMatrix (integralBasis F) x) i j)
  rw [Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, hb, ← map_mul]
  let y := x * integralBasis F j
  let q := (integralBasis F).equivFun y
  have hy : b.equivFun.symm (fun i ↦ dQ (q i)) = dL y := by
    calc
      _ = dL ((integralBasis F).equivFun.symm q) := by
        rw [b.equivFun_symm_apply, Module.Basis.equivFun_symm_apply, map_sum]
        apply Finset.sum_congr rfl
        intro k _
        simp only [hb, Algebra.smul_def, map_mul]
        exact congrArg (· * dL (integralBasis F k)) ((rationalAdeleEmbedding_spec F).2.1 (q k))
      _ = _ := congrArg dL ((integralBasis F).equivFun.symm_apply_apply y)
  change b.equivFun (dL y) i = dQ (q i)
  rw [← hy, LinearEquiv.apply_symm_apply]

private theorem relativeIdeleClassNormRat_principal :
    principal(F) ≤ (principal(ℚ)).comap (relativeIdeleNormRat F) := by
  rintro _ ⟨x, rfl⟩
  refine ⟨Units.map (Algebra.norm ℚ) x, Units.ext ?_⟩
  exact (relativeIdeleClassNormRat_diagonal F (x : F)).symm

/-- The relative determinant norm of Lemma A.2.2.2, p. 546, as a continuous
homomorphism on idele classes. -/
@[no_expose] def relativeIdeleClassNormRat : C[F] →ₜ* C[ℚ] where
  toMonoidHom := QuotientGroup.map (principal(F)) (principal(ℚ))
    (relativeIdeleNormRat F) (relativeIdeleClassNormRat_principal F)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk (principal(F))).continuous_iff.mpr <|
    (QuotientGroup.isQuotientMap_mk (principal(ℚ))).continuous.comp (relativeIdeleNormRat_continuous F)

/-- On the class of an idele the relative class norm is represented by its
determinant norm. -/
@[simp] theorem relativeIdeleClassNormRat_mk (g : 𝕀[F]) :
    relativeIdeleClassNormRat F (QuotientGroup.mk g) = QuotientGroup.mk (relativeIdeleNormRat F g) := by
  exact QuotientGroup.map_mk (principal(F)) (principal(ℚ)) (relativeIdeleNormRat F)
    (relativeIdeleClassNormRat_principal F) g

/-- Finite-order characters agree everywhere when they agree on the kernel
of a surjective positive norm. Every coset has an e-th power representative. -/
private theorem relativeIdeleClassNormRat_eq_of_ker {G M : Type*} [Group G] [CommGroup M]
    (ν : G →* ℝ≥0ˣ) (hν : Surjective ν) (φ ψ : G →* M) {e : ℕ} (he : 0 < e)
    (hφ : ∀ x, φ x ^ e = 1) (hψ : ∀ x, ψ x ^ e = 1)
    (hker : ∀ g, ν g = 1 → φ g = ψ g) (g : G) : φ g = ψ g := by
  let t := Units.map (NNReal.rpowMonoidHom (e : ℝ)⁻¹) (ν g)
  have ht : t ^ e = ν g := Units.ext (NNReal.rpow_inv_natCast_pow (ν g).val he.ne')
  obtain ⟨u, hu⟩ := hν t
  have hz : ν (g / u ^ e) = 1 := by rw [map_div, map_pow, hu, ht, div_self']
  simpa only [map_div, map_pow, hφ, hψ, div_one] using hker (g / u ^ e) hz

/-- If two finite-order rational characters have the same norm pullback on
norm-one idele classes, their field-degree powers coincide. -/
theorem relativeIdeleClassNormRat_pow_eq_of_restrict_eq {M : Type*} [CommGroup M]
    {χ θ : C[ℚ] →* M} (hχ : IsOfFinOrder χ) (hθ : IsOfFinOrder θ)
    (hcomp : (χ.comp (relativeIdeleClassNormRat F).toMonoidHom).comp (ideleClassNorm F).ker.subtype =
      (θ.comp (relativeIdeleClassNormRat F).toMonoidHom).comp (ideleClassNorm F).ker.subtype) :
    χ ^ Module.finrank ℚ F = θ ^ Module.finrank ℚ F := by
  let e := orderOf χ * orderOf θ
  have he : 0 < e := Nat.mul_pos hχ.orderOf_pos hθ.orderOf_pos
  have hχe : χ ^ e = 1 := orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_mul_right _ _)
  have hθe : θ ^ e = 1 := orderOf_dvd_iff_pow_eq_one.mp (Nat.dvd_mul_left _ _)
  have eval {φ : C[ℚ] →* M} (h : φ ^ e = 1) (y : C[ℚ]) : φ y ^ e = 1 := by
    rw [← MonoidHom.pow_apply, h, MonoidHom.one_apply]
  have h := relativeIdeleClassNormRat_eq_of_ker (ideleClassNorm F)
    (ideleGroup_quotient.{_,0} F).2.2.2.2.2.2.2.2.2.1
    (χ.comp (relativeIdeleClassNormRat F).toMonoidHom)
    (θ.comp (relativeIdeleClassNormRat F).toMonoidHom) he
    (fun x ↦ eval hχe (relativeIdeleClassNormRat F x))
    (fun x ↦ eval hθe (relativeIdeleClassNormRat F x))
    (fun x hx ↦ DFunLike.congr_fun hcomp ⟨x, hx⟩)
  apply MonoidHom.ext
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (principal(ℚ)) y
  let j := Units.map (rationalAdeleEmbedding F).toMonoidHom g
  have hg := h (QuotientGroup.mk j)
  change χ ((QuotientGroup.mk' (principal(ℚ))) (relativeIdeleNormRat F j)) =
    θ ((QuotientGroup.mk' (principal(ℚ))) (relativeIdeleNormRat F j)) at hg
  simpa only [j, relativeIdeleNormRat_on_rational, map_pow, MonoidHom.pow_apply] using hg

/-- Pullback to the norm-one components is injective on all finite-order
rational characters whose orders are coprime to the field degree. This applies
to the full family at once, independently of the orders and conductors. -/
theorem relativeIdeleClassNormRat_injOn_coprime (M : Type*) [CommGroup M] :
    Set.InjOn (fun χ : C[ℚ] →* M ↦
        (χ.comp (relativeIdeleClassNormRat F).toMonoidHom).comp (ideleClassNorm F).ker.subtype)
      {χ | IsOfFinOrder χ ∧ (orderOf χ).Coprime (Module.finrank ℚ F)} := by
  rintro χ ⟨hχ,hχd⟩ θ ⟨hθ,hθd⟩ hcomp
  have hd : orderOf (χ / θ) ∣ Module.finrank ℚ F := orderOf_dvd_of_pow_eq_one (by
    rw [div_pow, relativeIdeleClassNormRat_pow_eq_of_restrict_eq F hχ hθ hcomp, div_self'])
  have he : orderOf (χ / θ) ∣ orderOf χ * orderOf θ := by
    simpa only [div_eq_mul_inv, orderOf_inv] using (Commute.all χ θ⁻¹).orderOf_mul_dvd_mul_orderOf
  exact div_eq_one.mp (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hχd.mul_left hθd) he hd))

end RiemannMasullo
