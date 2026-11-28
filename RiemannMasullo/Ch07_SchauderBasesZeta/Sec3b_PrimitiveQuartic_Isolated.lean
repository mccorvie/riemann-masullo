module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b_IsotypicAverages
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.FieldTheory.Normal.Closure
import Mathlib.FieldTheory.Galois.Basic
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Analysis.Complex.IsIntegral
import Mathlib.Data.Fintype.EquivFin
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.RingTheory.Localization.Module
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated

/-! # Repeated primary poles in primitive totally imaginary quartic fields

Formalizes willzh0's restriction on repeated primary poles in the setting of
Theorem 7.3.3.4, pp. 360–363 (issue #7336).

Source: https://github.com/mccorvie/riemann-masullo/issues/7336#issuecomment-7145955656
-/

noncomputable section

namespace RiemannMasullo.Isolated

open Function NumberField IsDedekindDomain Topology
open scoped Classical ComplexConjugate NNReal Pointwise RestrictedProduct WithZero


/-! ### The Galois action on the four embeddings -/

section

open NumberField

/-- The Galois group of the normal closure can move any ordered pair of distinct
embeddings to any other. This is the two-transitivity hypothesis in the primitive
quartic argument. -/
def QuarticNormalClosurePairTransitive (F : Type*) [Field F] [NumberField F] : Prop :=
  let L := IntermediateField.normalClosure ℚ F ℂ
  ∀ f₁ f₂ g₁ g₂ : F →ₐ[ℚ] L, f₁ ≠ f₂ → g₁ ≠ g₂ →
    ∃ e : L ≃ₐ[ℚ] L, e.toAlgHom.comp f₁ = g₁ ∧ e.toAlgHom.comp f₂ = g₂

section

variable {F : Type*} [Field F] [NumberField F]

local notation "L" => IntermediateField.normalClosure ℚ F ℂ

private noncomputable def normalClosureComplexEmbeddings : (F →ₐ[ℚ] L) ≃ (F →+* ℂ) :=
  (normalClosure.algHomEquiv ℚ F ℂ).trans (RingHom.equivRatAlgHom F ℂ).symm

private theorem normalClosureComplexEmbeddings_apply (f : F →ₐ[ℚ] L) (x : F) :
    normalClosureComplexEmbeddings f x = (f x : ℂ) := rfl

private theorem normalClosureComplexEmbeddings_symm_apply (f : F →+* ℂ) (x : F) :
    ((normalClosureComplexEmbeddings.symm f x : L) : ℂ) = f x := by
  rw [← normalClosureComplexEmbeddings_apply, Equiv.apply_symm_apply]

private theorem quartic_pair_product_eq_one
    (h : QuarticNormalClosurePairTransitive F) {x : F}
    (f g : F →+* ℂ) (hfg : f ≠ g) (hprod : f x * g x = 1)
    (f' g' : F →+* ℂ) (hfg' : f' ≠ g') :
    f' x * g' x = 1 := by
  let Φ := normalClosureComplexEmbeddings (F := F)
  have h' : Φ.symm f x * Φ.symm g x = 1 := by
    apply Subtype.ext
    change (((Φ.symm f x : L) : ℂ) * ((Φ.symm g x : L) : ℂ)) = 1
    simpa only [normalClosureComplexEmbeddings_symm_apply, Φ] using hprod
  obtain ⟨e, he₁, he₂⟩ :=
    h (Φ.symm f) (Φ.symm g) (Φ.symm f') (Φ.symm g')
      (Φ.symm.injective.ne hfg) (Φ.symm.injective.ne hfg')
  have he₁' : e (Φ.symm f x) = Φ.symm f' x := DFunLike.congr_fun he₁ x
  have he₂' : e (Φ.symm g x) = Φ.symm g' x := DFunLike.congr_fun he₂ x
  have h'' := congrArg (fun y ↦ e y) h'
  rw [map_mul, map_one, he₁', he₂'] at h''
  simpa only [map_mul, map_one, IntermediateField.coe_val,
    normalClosureComplexEmbeddings_symm_apply, Φ] using congrArg (fun y : L ↦ (L : IntermediateField ℚ ℂ).val y) h''

/-- In a totally imaginary quartic with doubly transitive normal-closure action,
an element of modulus one at one embedding is \(1\) or \(-1\). -/
theorem quartic_eq_one_or_neg_one_of_norm_eq_one [IsTotallyComplex F]
    (hdeg : Module.finrank ℚ F = 4) (h : QuarticNormalClosurePairTransitive F)
    (f : F →+* ℂ) (x : F) (hx : ‖f x‖ = 1) : x = 1 ∨ x = -1 := by
  let g := ComplexEmbedding.conjugate f
  have hgf : g ≠ f :=
    fun e ↦ (IsTotallyComplex.complexEmbedding_not_isReal f) (ComplexEmbedding.isReal_iff.mpr e)
  have hfg : f x * g x = 1 := by
    change f x * (starRingEnd ℂ) (f x) = 1
    rw [Complex.mul_conj', hx]
    norm_num
  have hcard : Fintype.card (F →+* ℂ) = 4 := (NumberField.Embeddings.card F ℂ).trans hdeg
  let E := Fintype.equivFinOfCardEq hcard
  obtain ⟨j, hjf, hjg⟩ := Fin.exists_ne_and_ne_of_two_lt (E f) (E g) (by decide)
  let k := E.symm j
  have hkf : k ≠ f := fun eq ↦ hjf (by simp [← eq, k])
  have hkg : k ≠ g := fun eq ↦ hjg (by simp [← eq, k])
  have hfk := quartic_pair_product_eq_one h f g hgf.symm hfg f k hkf.symm
  have hgk := quartic_pair_product_eq_one h f g hgf.symm hfg g k hkg.symm
  have hfn : f x ≠ 0 := norm_ne_zero_iff.mp (by rw [hx]; exact one_ne_zero)
  have hg_eq : g x = k x := mul_left_cancel₀ hfn (hfg.trans hfk.symm)
  rw [← hg_eq, ← sq] at hgk
  exact sq_eq_one_iff.mp (g.injective (by simpa only [map_pow, map_one] using hgk))


private noncomputable def quarticMoveEmbedding (e : L ≃ₐ[ℚ] L) (f : F →+* ℂ) : F →+* ℂ :=
  normalClosureComplexEmbeddings (e.toAlgHom.comp (normalClosureComplexEmbeddings.symm f))

private theorem quarticMoveEmbedding_apply (e : L ≃ₐ[ℚ] L) (f : F →+* ℂ) (x : F) :
    quarticMoveEmbedding e f x = (e (normalClosureComplexEmbeddings.symm f x) : ℂ) := rfl

private theorem quarticMoveEmbedding_injective (e : L ≃ₐ[ℚ] L) :
    Function.Injective (quarticMoveEmbedding (F := F) e) := by
  intro f g h
  apply normalClosureComplexEmbeddings.symm.injective
  have hh := normalClosureComplexEmbeddings.injective h
  apply AlgHom.ext
  intro x
  apply e.injective
  exact DFunLike.congr_fun hh x

private theorem quartic_exists_move_embedding_pair
    (h : QuarticNormalClosurePairTransitive F)
    {f₁ f₂ g₁ g₂ : F →+* ℂ} (hf : f₁ ≠ f₂) (hg : g₁ ≠ g₂) :
    ∃ e : L ≃ₐ[ℚ] L, quarticMoveEmbedding e f₁ = g₁ ∧ quarticMoveEmbedding e f₂ = g₂ := by
  let Φ := normalClosureComplexEmbeddings (F := F)
  obtain ⟨e, he₁, he₂⟩ := h (Φ.symm f₁) (Φ.symm f₂) (Φ.symm g₁) (Φ.symm g₂)
    (Φ.symm.injective.ne hf) (Φ.symm.injective.ne hg)
  refine ⟨e, ?_, ?_⟩
  · change Φ (e.toAlgHom.comp (Φ.symm f₁)) = g₁
    rw [he₁, Equiv.apply_symm_apply]
  · change Φ (e.toAlgHom.comp (Φ.symm f₂)) = g₂
    rw [he₂, Equiv.apply_symm_apply]

private theorem quartic_angular_relation_move (e : L ≃ₐ[ℚ] L)
    (f f' g g' : F →+* ℂ) (x : F) (m n : ℤ) (N : ℕ)
    (h : ((f x / f' x) ^ m * (g x / g' x) ^ n) ^ N = 1) :
    ((quarticMoveEmbedding e f x / quarticMoveEmbedding e f' x) ^ m *
      (quarticMoveEmbedding e g x / quarticMoveEmbedding e g' x) ^ n) ^ N = 1 := by
  let Φ := normalClosureComplexEmbeddings (F := F)
  have hl : ((Φ.symm f x / Φ.symm f' x) ^ m * (Φ.symm g x / Φ.symm g' x) ^ n) ^ N = 1 := by
    apply ((L : IntermediateField ℚ ℂ).val : L →ₐ[ℚ] ℂ).injective
    rw [map_pow, map_mul, map_zpow₀, map_zpow₀, map_div₀, map_div₀, map_one]
    change ((((Φ.symm f x : L) : ℂ) / ((Φ.symm f' x : L) : ℂ)) ^ m *
      (((Φ.symm g x : L) : ℂ) / ((Φ.symm g' x : L) : ℂ)) ^ n) ^ N = 1
    simpa only [Φ, normalClosureComplexEmbeddings_symm_apply] using h
  have hm := congrArg (fun y : L ↦ (L : IntermediateField ℚ ℂ).val (e y)) hl
  simp only [map_pow, map_mul, map_zpow₀, map_div₀, map_one] at hm
  exact hm

private theorem quartic_zpow_pow_eq_one {r : ℝ} (hr : 0 < r) (hr' : r ≠ 1)
    {N : ℕ} (hN : 0 < N) {k : ℤ} (h : (r ^ k) ^ N = 1) : k = 0 := by
  rw [← zpow_natCast, ← zpow_mul, zpow_eq_one_iff_right₀ hr.le hr'] at h
  exact (mul_eq_zero.mp h).resolve_right (by exact_mod_cast hN.ne')

/-- In a primitive totally imaginary quartic, a torsion angular relation at an
element with unequal archimedean magnitudes forces both angular exponents to vanish. -/
theorem quartic_angular_exponents_eq_zero [IsTotallyComplex F]
    (hdeg : Module.finrank ℚ F = 4) (h : QuarticNormalClosurePairTransitive F)
    (f g : F →+* ℂ) (hgf : g ≠ f) (hgcf : g ≠ ComplexEmbedding.conjugate f)
    (x : F) (hx : ‖f x‖ ≠ ‖g x‖) (m n : ℤ) {N : ℕ} (hN : 0 < N)
    (hang : ((f x / star (f x)) ^ m * (g x / star (g x)) ^ n) ^ N = 1) :
    m = 0 ∧ n = 0 := by
  classical
  let cf := ComplexEmbedding.conjugate f
  let cg := ComplexEmbedding.conjugate g
  have hcff : cf ≠ f := fun eq ↦ IsTotallyComplex.complexEmbedding_not_isReal f
    (ComplexEmbedding.isReal_iff.mpr eq)
  have hcgg : cg ≠ g := fun eq ↦ IsTotallyComplex.complexEmbedding_not_isReal g
    (ComplexEmbedding.isReal_iff.mpr eq)
  have hcgf : cg ≠ f := by
    intro eq
    exact hgcf ((ComplexEmbedding.involutive_conjugate F g).symm.trans
      (congrArg ComplexEmbedding.conjugate eq))
  have hcgcf : cg ≠ cf := (ComplexEmbedding.involutive_conjugate F).injective.ne hgf

  have hcard : Fintype.card (F →+* ℂ) = 4 := (NumberField.Embeddings.card F ℂ).trans hdeg
  have hSet : ({f, cf, g, cg} : Finset (F →+* ℂ)) = Finset.univ := by
    apply (Finset.card_eq_iff_eq_univ _).mp
    rw [hcard]
    have hgnot : g ∉ ({cg} : Finset (F →+* ℂ)) := by simpa using hcgg.symm
    have hcfnot : cf ∉ ({g, cg} : Finset (F →+* ℂ)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hgcf.symm, hcgcf.symm⟩
    have hfnot : f ∉ ({cf, g, cg} : Finset (F →+* ℂ)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hcff.symm, hgf.symm, hcgf.symm⟩
    rw [Finset.card_insert_of_notMem hfnot, Finset.card_insert_of_notMem hcfnot,
      Finset.card_insert_of_notMem hgnot, Finset.card_singleton]
  let A := ‖f x‖
  let B := ‖g x‖
  have hcfA : ‖cf x‖ = A := norm_star _
  have hcgB : ‖cg x‖ = B := norm_star _
  have hOther (j : F →+* ℂ) (hjf : j ≠ f) (hjcf : j ≠ cf) : ‖j x‖ = B := by
    have hj : j ∈ ({f, cf, g, cg} : Finset (F →+* ℂ)) := hSet ▸ Finset.mem_univ j
    obtain h | h : j = g ∨ j = cg := by simpa [hjf, hjcf] using hj
    · simp [h, B]
    · simpa [h] using hcgB
  have hMoveOther (e : L ≃ₐ[ℚ] L) {a b c : F →+* ℂ}
      (ha : quarticMoveEmbedding e a = f) (hb : quarticMoveEmbedding e b = cf)
      (hca : c ≠ a) (hcb : c ≠ b) : ‖quarticMoveEmbedding e c x‖ = B :=
    hOther _ (fun eq ↦ hca (quarticMoveEmbedding_injective e (eq.trans ha.symm)))
      (fun eq ↦ hcb (quarticMoveEmbedding_injective e (eq.trans hb.symm)))
  have hx0 : x ≠ 0 := fun eq ↦ hx (by simp [eq])
  have hA : 0 < A := norm_pos_iff.mpr ((map_ne_zero f).mpr hx0)
  have hB : 0 < B := norm_pos_iff.mpr ((map_ne_zero g).mpr hx0)
  have hr : 0 < A / B := div_pos hA hB
  have hr' : A / B ≠ 1 := by
    intro eq
    exact hx ((div_eq_iff hB.ne').mp eq |>.trans (one_mul B))
  have hpow (e : L ≃ₐ[ℚ] L) :=
    quartic_angular_relation_move e f cf g cg x m n N hang

  obtain ⟨e₁, he₁f, he₁g⟩ := quartic_exists_move_embedding_pair h hgf.symm hcff.symm
  have he₁cfB : ‖quarticMoveEmbedding e₁ cf x‖ = B :=
    hMoveOther e₁ he₁f he₁g hcff hgcf.symm
  have he₁cgB : ‖quarticMoveEmbedding e₁ cg x‖ = B :=
    hMoveOther e₁ he₁f he₁g hcgf hcgg
  have h₁ := congrArg (fun z : ℂ ↦ ‖z‖) (hpow e₁)
  rw [norm_pow, norm_mul, norm_zpow, norm_zpow, norm_div, norm_div, norm_one,
    he₁f, he₁g, he₁cfB, he₁cgB, hcfA, ← zpow_add₀ hr.ne'] at h₁
  have hsum := quartic_zpow_pow_eq_one hr hr' hN h₁

  obtain ⟨e₂, he₂f, he₂cg⟩ := quartic_exists_move_embedding_pair h hcgf.symm hcff.symm
  have he₂cfB : ‖quarticMoveEmbedding e₂ cf x‖ = B :=
    hMoveOther e₂ he₂f he₂cg hcff hcgcf.symm
  have he₂gB : ‖quarticMoveEmbedding e₂ g x‖ = B :=
    hMoveOther e₂ he₂f he₂cg hgf hcgg.symm
  have h₂ := congrArg (fun z : ℂ ↦ ‖z‖) (hpow e₂)
  rw [norm_pow, norm_mul, norm_zpow, norm_zpow, norm_div, norm_div, norm_one,
    he₂f, he₂cg, he₂cfB, he₂gB, hcfA, ← inv_div A B, inv_zpow',
    ← zpow_add₀ hr.ne'] at h₂
  have hdiff := quartic_zpow_pow_eq_one hr hr' hN h₂
  omega

private theorem quartic_automorphism_eq_one
    (hdeg : Module.finrank ℚ F = 4)
    (hprimitive : ∀ K : IntermediateField ℚ F, K = ⊥ ∨ K = ⊤)
    (e : F ≃ₐ[ℚ] F) : e = 1 := by
  have horder (a : F ≃ₐ[ℚ] F) : orderOf a = 4 ∨ orderOf a = 1 := by
    rw [← Nat.card_zpowers, ← IntermediateField.finrank_fixedField_eq_card]
    rcases hprimitive (IntermediateField.fixedField (Subgroup.zpowers a)) with h | h
    · exact Or.inl (by rw [h, IntermediateField.finrank_bot', hdeg])
    · exact Or.inr (by rw [h, IntermediateField.finrank_top])
  rcases horder e with he | he
  · have he₂ : orderOf (e ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by decide) (by rw [he]; decide), he]
    rcases horder (e ^ 2) with h | h <;> omega
  · exact orderOf_eq_one_iff.mp he

private theorem quartic_normalClosure_normal : Normal ℚ L :=
  (show IsNormalClosure ℚ F L from
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun _ ↦ IsAlgClosed.splits _)).normal

private theorem normalClosure_exists_move (f g : F →ₐ[ℚ] L) :
    ∃ e : L ≃ₐ[ℚ] L, e.toAlgHom.comp f = g := by
  let : Normal ℚ L := quartic_normalClosure_normal
  let i : f.fieldRange →ₐ[ℚ] L := g.comp f.equivFieldRange.symm.toAlgHom
  let e := AlgEquiv.ofBijective (i.liftNormal L) (AlgHom.normal_bijective ℚ L L _)
  refine ⟨e, AlgHom.ext fun x ↦ ?_⟩
  change i.liftNormal L (algebraMap f.fieldRange L (f.equivFieldRange x)) = g x
  rw [i.liftNormal_commutes]
  simp [i]

private theorem normalClosure_fixes_iff (e : L ≃ₐ[ℚ] L) (f : F →ₐ[ℚ] L) :
    e ∈ f.fieldRange.fixingSubgroup ↔ e.toAlgHom.comp f = f := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact AlgHom.ext fun x ↦ h (f x) ⟨x, rfl⟩
  · intro h y hy
    obtain ⟨x, hx⟩ := AlgHom.mem_fieldRange.mp hy
    rw [← hx]
    exact DFunLike.congr_fun h x

private theorem quartic_exists_move_of_ne
    (hdeg : Module.finrank ℚ F = 4)
    (hprimitive : ∀ K : IntermediateField ℚ F, K = ⊥ ∨ K = ⊤)
    (f g : F →ₐ[ℚ] L) (hfg : g ≠ f) :
    ∃ e : L ≃ₐ[ℚ] L, e ∈ f.fieldRange.fixingSubgroup ∧ e.toAlgHom.comp g ≠ g := by
  classical
  let : IsGalois ℚ L := isGalois_iff.mpr ⟨inferInstance, quartic_normalClosure_normal⟩
  by_contra! h
  have hle : g.fieldRange ≤ f.fieldRange := by
    rw [← IsGalois.fixedField_fixingSubgroup f.fieldRange]
    exact (IntermediateField.le_fixedField_iff_le_fixingSubgroup _ _).mpr
      fun e he ↦ (normalClosure_fixes_iff e g).mpr (h e he)
  have hEq : g.fieldRange = f.fieldRange := by
    apply IntermediateField.eq_of_le_of_finrank_eq hle
    exact g.equivFieldRange.toLinearEquiv.finrank_eq.symm.trans
      f.equivFieldRange.toLinearEquiv.finrank_eq
  let e := g.equivFieldRange.trans ((IntermediateField.equivOfEq hEq).trans f.equivFieldRange.symm)
  have he (x : F) : f (e x) = g x := by
    change ((f.equivFieldRange (e x) : f.fieldRange) : L) = g x
    simp [e, IntermediateField.equivOfEq]
    rfl
  exact hfg (AlgHom.ext fun x ↦ by simpa [quartic_automorphism_eq_one hdeg hprimitive e] using (he x).symm)

private theorem quartic_normalClosure_card (hdeg : Module.finrank ℚ F = 4) :
    Fintype.card (F →ₐ[ℚ] L) = 4 :=
  (Fintype.card_congr normalClosureComplexEmbeddings).trans
    ((NumberField.Embeddings.card F ℂ).trans hdeg)

/-- An algebraic quartic with no proper intermediate field over \(\mathbb Q\)
has a doubly transitive normal-closure action on its embeddings. -/
theorem quarticNormalClosurePairTransitive_of_primitive
    (hdeg : Module.finrank ℚ F = 4)
    (hprimitive : ∀ K : IntermediateField ℚ F, K = ⊥ ∨ K = ⊤) :
    QuarticNormalClosurePairTransitive F := by
  classical
  intro f₁ f₂ g₁ g₂ hf hg
  obtain ⟨e₀, he₀⟩ := normalClosure_exists_move f₁ g₁
  let a := e₀.toAlgHom.comp f₂
  have ha : a ≠ g₁ := by
    intro eq
    apply hf
    exact AlgHom.ext fun x ↦ e₀.injective (DFunLike.congr_fun (he₀.trans eq.symm) x)
  suffices h : ∃ e : L ≃ₐ[ℚ] L, e ∈ g₁.fieldRange.fixingSubgroup ∧
      e.toAlgHom.comp a = g₂ by
    obtain ⟨e, hef, he⟩ := h
    refine ⟨e₀.trans e, ?_, he⟩
    change e.toAlgHom.comp (e₀.toAlgHom.comp f₁) = g₁
    rw [he₀]
    exact (normalClosure_fixes_iff e g₁).mp hef
  by_cases hab : a = g₂
  · exact ⟨1, Subgroup.one_mem _, hab⟩
  obtain ⟨e₁, he₁f, he₁a⟩ := quartic_exists_move_of_ne hdeg hprimitive g₁ a ha
  let b := e₁.toAlgHom.comp a
  by_cases hb₂ : b = g₂
  · exact ⟨e₁, he₁f, hb₂⟩
  have hb₁ : b ≠ g₁ := by
    intro eq
    apply ha
    exact AlgHom.ext fun x ↦ e₁.injective
      (DFunLike.congr_fun (eq.trans ((normalClosure_fixes_iff e₁ g₁).mp he₁f).symm) x)
  have hfour : ({g₁, g₂, a, b} : Finset (F →ₐ[ℚ] L)) = Finset.univ := by
    apply (Finset.card_eq_iff_eq_univ _).mp
    rw [quartic_normalClosure_card hdeg]
    have hanot : a ∉ ({b} : Finset (F →ₐ[ℚ] L)) := by simpa using he₁a.symm
    have h₂not : g₂ ∉ ({a, b} : Finset (F →ₐ[ℚ] L)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hab, Ne.symm hb₂⟩
    have h₁not : g₁ ∉ ({g₂, a, b} : Finset (F →ₐ[ℚ] L)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hg, ha.symm, hb₁.symm⟩
    rw [Finset.card_insert_of_notMem h₁not, Finset.card_insert_of_notMem h₂not,
      Finset.card_insert_of_notMem hanot, Finset.card_singleton]
  obtain ⟨e₂, he₂f, he₂g⟩ := quartic_exists_move_of_ne hdeg hprimitive g₁ g₂ hg.symm
  let c := e₂.toAlgHom.comp g₂
  have hc₁ : c ≠ g₁ := by
    intro eq
    apply hg.symm
    exact AlgHom.ext fun x ↦ e₂.injective
      (DFunLike.congr_fun (eq.trans ((normalClosure_fixes_iff e₂ g₁).mp he₂f).symm) x)
  have hcmem : c ∈ ({g₁, g₂, a, b} : Finset (F →ₐ[ℚ] L)) := hfour ▸ Finset.mem_univ c
  have hc : c = a ∨ c = b := by simpa [hc₁, show c ≠ g₂ from he₂g] using hcmem
  rcases hc with hc | hc
  · refine ⟨e₂.symm, ?_, ?_⟩
    · exact Subgroup.inv_mem _ he₂f
    · exact AlgHom.ext fun x ↦ by
        change e₂.symm (a x) = g₂ x
        rw [← DFunLike.congr_fun hc x]
        exact e₂.symm_apply_apply _
  · refine ⟨e₁.trans e₂.symm, Subgroup.mul_mem _ (Subgroup.inv_mem _ he₂f) he₁f, ?_⟩
    exact AlgHom.ext fun x ↦ by
      change e₂.symm (b x) = g₂ x
      rw [← DFunLike.congr_fun hc x]
      exact e₂.symm_apply_apply _

end

end

/-! ### Finite ideles attached to a pair of poles -/

section

variable (F : Type*) [Field F] [NumberField F]

local notation "Primes(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "𝕀∞" => (InfiniteAdeleRing F)ˣ
local notation "N₁" => MonoidHom.ker (ideleNorm F)
local notation "atInfinity" =>
  Units.map (RingHom.toMonoidHom (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
local notation "fromInfinity" =>
  Units.map (MonoidHom.inl (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F
local notation "integralUnits" =>
  MonoidHom.range (Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F ∅))))

/-- A power of a norm-one idele is a principal idele times an integral unit idele. -/
theorem primitiveQuartic_principalize_ratio (g : N₁) :
    ∃ n : ℕ, 0 < n ∧ ∃ a : Fˣ, ∃ u : 𝕀[F],
      u ∈ integralUnits ∧ g.val ^ n = principal a * u := by
  obtain ⟨e, _⟩ := (picard_uniformization F ∅).2.2.2
  let : Finite (CommRing.Pic (𝓞 F)) :=
    Finite.of_equiv (ClassGroup (𝓞 F)) (ClassGroup.equivPic (𝓞 F)).toEquiv
  obtain ⟨n, hn, he⟩ := (isOfFinOrder_of_finite (e (QuotientGroup.mk g))).exists_pow_eq_one
  have hg : QuotientGroup.mk (g ^ n) = 1 := e.injective <| by
    change e ((QuotientGroup.mk' _) (g ^ n)) = e 1
    rw [map_pow, map_pow, map_one]
    exact he
  have hsup := (QuotientGroup.eq_one_iff (g ^ n)).mp hg
  change g.val ^ n ∈ (IdeleGroup.principalSubgroup (𝓞 F) F ⊔ integralUnits) at hsup
  obtain ⟨_, ⟨a, rfl⟩, u, hu, h⟩ := Subgroup.mem_sup.mp hsup
  exact ⟨n, hn, a, u, hu, h.symm⟩

/-- The principal generator of the power has exactly the same finite support. -/
theorem primitiveQuartic_principalize_support {g : 𝕀[F]} {n : ℕ} (hn : 0 < n)
    {a : Fˣ} {u : 𝕀[F]} (hu : u ∈ integralUnits) (h : g ^ n = principal a * u)
    (v : Primes(F)) :
    (v.valuation F (a : F) = 1) ↔ Valued.v (g.val.2 v) = (1 : ℤᵐ⁰) := by
  let eval := (RestrictedProduct.evalRingHom (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
    (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
  let f := (Valued.v : Valuation (v.adicCompletion F) ℤᵐ⁰).toMonoidWithZeroHom.toMonoidHom.comp
    ((Units.coeHom (v.adicCompletion F)).comp (Units.map eval.toMonoidHom))
  have he := congrArg f h
  rw [map_pow, map_mul] at he
  have hu' : f u = 1 :=
    (mem_integralIdeleRange_iff F u).mp hu v
  have ha : f (principal a) = v.valuation F (a : F) := by
    change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = _
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (a : F)
  rw [hu', mul_one, ha] at he
  rw [← he]
  exact pow_eq_one_iff_of_nonneg zero_le hn.ne'

local notation "C₁" => MonoidHom.ker (ideleClassNorm F)

/-- Passing a norm-one idele to its global idele class. -/
def primitiveQuarticNormOneClass : N₁ →* C₁ :=
  ((QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)).comp (Subgroup.subtype N₁)).codRestrict
    _ fun g ↦ g.property

/-- Giving a norm-one archimedean idele finite components equal to one. -/
def primitiveQuarticArchIdele : (infiniteIdeleNorm F).ker →* N₁ :=
  ((fromInfinity).comp (infiniteIdeleNorm F).ker.subtype).codRestrict _ fun a ↦
    (infiniteIdeleNorm_eq_global F a.val).symm.trans a.property

/-- The archimedean projection of an integral, norm-one idele has norm one. -/
theorem primitiveQuartic_infiniteNorm_of_integral (u : 𝕀[F])
    (hu : u ∈ integralUnits) (hn : ideleNorm F u = 1) :
    infiniteIdeleNorm F (atInfinity u) = 1 := by
  have hfin : (∏ᶠ v : Primes(F), ‖u.val.2 v‖) = 1 :=
    finprod_eq_one_of_forall_eq_one fun v ↦ Valued.toNormedField.norm_eq_one_iff.mpr
      ((mem_integralIdeleRange_iff F u).mp hu v)
  rw [infiniteIdeleNorm_eq_global, ← hn]
  apply Units.ext
  apply NNReal.coe_injective
  rw [((ideleNorm_spec F).1 (fromInfinity (atInfinity u))).2, ((ideleNorm_spec F).1 u).2, hfin]
  have h₁ (v : Primes(F)) : (fromInfinity (atInfinity u)).val.2 v = 1 := rfl
  simp only [h₁, norm_one, finprod_one]
  rfl

/-- The units supported at finite places have torsion image under any norm-one circle character. -/
theorem primitiveQuartic_finite_unit_character_exponent (ω : PontryaginDual C₁) :
    ∃ n : ℕ, 0 < n ∧ ∀ (u : N₁), u.val ∈ integralUnits → atInfinity u.val = 1 →
      ω (primitiveQuarticNormOneClass F u) ^ n = 1 := by
  let U := (v : Primes(F)) → (v.adicCompletionIntegers F).units
  have hC (v : Primes(F)) : CompactSpace (v.adicCompletionIntegers F).units :=
    isCompact_iff_compactSpace.mp
      (Submonoid.units_isCompact (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)))
  have hTD (v : Primes(F)) : TotallyDisconnectedSpace (v.adicCompletion F)ˣ :=
    ⟨isTotallyDisconnected_of_image Units.continuous_val.continuousOn Units.val_injective
      (isTotallyDisconnected_of_totallyDisconnectedSpace _)⟩
  have : CompactSpace U := inferInstanceAs (CompactSpace (∀ v : Primes(F), _))
  have : TotallyDisconnectedSpace U := inferInstanceAs (TotallyDisconnectedSpace (∀ v : Primes(F), _))
  obtain ⟨e, he⟩ := (ideleGroup_topology F).2.2.2.1
  let s : U →* Πʳ v : Primes(F), [(v.adicCompletion F)ˣ, (v.adicCompletionIntegers F).units] :=
    { toFun := RestrictedProduct.structureMap (fun v : Primes(F) ↦ (v.adicCompletion F)ˣ)
        (fun v : Primes(F) ↦ ((v.adicCompletionIntegers F).units : Set (v.adicCompletion F)ˣ))
        Filter.cofinite
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hs : Continuous s := by
    exact RestrictedProduct.isEmbedding_structureMap.continuous
  let raw : U →* 𝕀[F] := e.symm.toMonoidHom.comp ((MonoidHom.inr _ _).comp s)
  have hraw (x : U) : e (raw x) = (1, s x) := e.apply_symm_apply _
  have harch (x : U) (v : InfinitePlace F) : (raw x).val.1 v = 1 := by
    rw [← (he _).1 v, hraw]
    rfl
  have hfin (x : U) (v : Primes(F)) : (raw x).val.2 v = (x v).val.val := by
    rw [← (he _).2 v, hraw]
    rfl
  have hnorm (x : U) : ideleNorm F (raw x) = 1 := by
    apply Units.ext
    apply NNReal.coe_injective
    rw [((ideleNorm_spec F).1 (raw x)).2]
    have hlocal (v : Primes(F)) : ‖(raw x).val.2 v‖ = 1 := by
      rw [hfin]
      exact Valued.toNormedField.norm_eq_one_iff.mpr
        (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp (x v).property)
    simp only [harch, hlocal, norm_one, one_pow, Finset.prod_const_one, finprod_one, mul_one,
      Units.val_one, NNReal.coe_one]
  let i : U →* N₁ := raw.codRestrict _ hnorm
  have hi : Continuous i := (e.symm.continuous.comp (continuous_const.prodMk hs)).subtype_mk _
  let q := primitiveQuarticNormOneClass F
  have hq : Continuous q :=
    (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
  let ψ : PontryaginDual U := ⟨ω.toMonoidHom.comp (q.comp i), ω.continuous.comp (hq.comp hi)⟩
  have hopen := (Circle.isOpen_centeredArc (Real.pi / 2)).preimage ψ.continuous
  have hone : (1 : U) ∈ ψ ⁻¹' Circle.centeredArc (Real.pi / 2) := by
    change ψ 1 ∈ Circle.centeredArc (Real.pi / 2)
    rw [map_one, Circle.mem_centeredArc (by linarith [Real.pi_pos])]
    simp [Real.pi_pos]
  obtain ⟨H, _, hH⟩ := exists_compact_openSubgroup_sub_mem_nhds (hopen.mem_nhds hone)
  have hker (x : U) (hx : x ∈ H) : ψ x = 1 := by
    apply Circle.eq_one_of_forall_pow_mem_centeredArc_pi_div_two
    intro n _
    rw [← map_pow]
    exact hH (H.pow_mem hx n)
  refine ⟨H.toSubgroup.index, Nat.card_pos, ?_⟩
  intro u hu harchu
  let x : U := fun v ↦ ⟨(e u.val).2 v, by
    apply HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
    rw [(he _).2 v]
    exact (mem_integralIdeleRange_iff F u.val).mp hu v⟩
  have hxu : i x = u := by
    apply Subtype.ext
    apply e.injective
    change e (raw x) = e u.val
    rw [hraw]
    apply Prod.ext
    · funext v
      apply Units.ext
      rw [(he _).1 v]
      exact congrArg (fun z : 𝕀∞ ↦ z.val v) harchu.symm
    · ext v
      rfl
  rw [← hxu]
  change ψ x ^ H.toSubgroup.index = 1
  rw [← map_pow]
  exact hker _ (H.toSubgroup.pow_index_mem x)

/-- A norm-one character trivial on a purely finite idele has torsion value on
  the archimedean projection of a generator principalizing that idele. -/
theorem primitiveQuartic_principalize_character (ω : PontryaginDual C₁) (g : N₁)
    (hg : ω (primitiveQuarticNormOneClass F g) = 1) (harchg : atInfinity g.val = 1) :
    ∃ a : Fˣ, ∃ b : (infiniteIdeleNorm F).ker, b.val = atInfinity (principal a) ∧
      IsOfFinOrder (ω (primitiveQuarticNormOneClass F (primitiveQuarticArchIdele F b))) ∧
      ∀ v : Primes(F), v.valuation F (a : F) = 1 ↔ Valued.v (g.val.val.2 v) = (1 : ℤᵐ⁰) := by
  obtain ⟨n, hn, a, u, hu, he⟩ := primitiveQuartic_principalize_ratio F g
  let N := (ideleNorm F).ker
  let p : Fˣ →* N := (principal).codRestrict _ fun x ↦ (ideleNorm_spec F).2 (Set.mem_range_self x)
  have hnu : ideleNorm F u = 1 := by
    have h := congrArg (ideleNorm F) he
    rw [map_pow, map_mul, show ideleNorm F (principal a) = 1 from (p a).property,
      one_mul, g.property, one_pow] at h
    exact h.symm
  let U : N := ⟨u, hnu⟩
  have hep : g ^ n = p a * U := Subtype.ext he
  let q := primitiveQuarticNormOneClass F
  have hqa : q (p a) = 1 := by
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (principal a)).mpr (Set.mem_range_self a)
  have hωu : ω (q U) = 1 := by
    have h := congrArg (fun x : N ↦ ω (q x)) hep
    change (ω.toMonoidHom.comp q) (g ^ n) = (ω.toMonoidHom.comp q) (p a * U) at h
    rw [map_pow, map_mul] at h
    change ω (q g) ^ n = ω (q (p a)) * ω (q U) at h
    rw [hg, one_pow, hqa, map_one, one_mul] at h
    exact h.symm
  have harch : atInfinity (principal a) * atInfinity u = 1 := by
    have h := congrArg (atInfinity) he
    rw [map_pow, map_mul, harchg, one_pow] at h
    exact h.symm
  let B : (infiniteIdeleNorm F).ker :=
    ⟨atInfinity u, primitiveQuartic_infiniteNorm_of_integral F u hu hnu⟩
  have hBa : (B⁻¹).val = atInfinity (principal a) := (eq_inv_of_mul_eq_one_left harch).symm
  let ins := primitiveQuarticArchIdele F
  let V := U / ins B
  have hUV : U = V * ins B := (div_mul_cancel U (ins B)).symm
  have hV : V.val ∈ integralUnits := by
    apply (mem_integralIdeleRange_iff F V.val).mpr
    intro v
    let ev := Units.map ((RestrictedProduct.evalRingHom
      (fun w : Primes(F) ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom
    have heval : ev (ins B).val = 1 := Units.ext rfl
    change Valued.v (ev (u / (ins B).val)).val = 1
    rw [map_div, heval, div_one]
    exact (mem_integralIdeleRange_iff F u).mp hu v
  have hVarch : atInfinity V.val = 1 := by
    change atInfinity (u / (ins B).val) = 1
    rw [map_div]
    exact div_self' (atInfinity u)
  obtain ⟨m, hm, hωm⟩ := primitiveQuartic_finite_unit_character_exponent F ω
  have hωB : ω (q (ins B⁻¹)) = ω (q V) := by
    have h := congrArg (fun x : N ↦ ω (q x)) hUV
    change (ω.toMonoidHom.comp q) U = (ω.toMonoidHom.comp q) (V * ins B) at h
    rw [map_mul] at h
    change ω (q U) = ω (q V) * ω (q (ins B)) at h
    rw [hωu] at h
    rw [map_inv, map_inv, map_inv, eq_inv_of_mul_eq_one_left h.symm]
  refine ⟨a, B⁻¹, hBa, isOfFinOrder_iff_pow_eq_one.mpr ⟨m, hm, ?_⟩,
    primitiveQuartic_principalize_support F hn hu he⟩
  rw [hωB]
  exact hωm V hV hVarch

variable {S : Finset (Primes(F))}

/-- At a finite pole the local character is one on the chosen uniformizer. -/
private theorem primitiveQuartic_pole_uniformizer
    (c : QuasiCharacter (SIdeleQuotient F S)) (w : S) (hw : w ∈ sLocalFinitePolePlaces c) :
    ∃ u : (w.val.adicCompletion F)ˣ,
      ‖u.val‖ = (w.val.asIdeal.absNorm : ℝ)⁻¹ ∧ sLocalFiniteRestriction w c u = 1 := by
  let π := (Valued.v : Valuation (w.val.adicCompletion F) ℤᵐ⁰)
    |>.exists_isUniformizer_of_isCyclic_of_nontrivial
  let u : (w.val.adicCompletion F)ˣ := Units.mk0 π.choose π.choose_spec.ne_zero
  refine ⟨u, norm_uniformizer_adicCompletion w.val _ π.choose_spec, ?_⟩
  have hzero : finiteLocalEulerFactor w.val (sLocalFiniteRestriction w c) = 0 := by
    have hm := (sLocalPrincipalPartCoeff_leading_formula_fin_factor c w).1
    have ho := (Finset.mem_filter.mp hw).2
    by_contra h
    have hz : quasiCharacterNormTwist (sIdeleQuotientNorm F S)
        (isProperMap_sIdeleQuotientNorm F S).continuous c 0 = c := by
      ext1 x
      exact (congrArg (c x * ·) (Complex.cpow_zero _)).trans (mul_one _)
    exact ho.ne (hm.meromorphicOrderAt_eq_zero_iff.mpr (by simpa only [hz] using h))
  unfold finiteLocalEulerFactor at hzero
  split at hzero
  · change (1 - sLocalFiniteRestriction w c u)⁻¹ = 0 at hzero
    exact (sub_eq_zero.mp (inv_eq_zero.mp hzero)).symm
  · exact False.elim (one_ne_zero hzero)

/-- Two distinct finite poles over one rational prime give a character-trivial norm-one
idele with exactly those two places in its valuation support. -/
theorem primitiveQuartic_pole_ratio (ω : PontryaginDual C₁)
    (hω : NormOneCharacterUnramifiedOutside ω S) (p : HeightOneSpectrum (𝓞 ℚ))
    (c : QuasiCharacter (SIdeleQuotient F S))
    (hc : ∀ x : (sIdeleQuotientNorm F S).ker,
      c x.val = (sLocalNormOneCharacter S ω hω x : ℂ))
    (v w : S) (hne : v ≠ w) (hvp : v.val ∈ sLocalPrimaryPlaces S p)
    (hwp : w.val ∈ sLocalPrimaryPlaces S p)
    (hv : v ∈ sLocalFinitePolePlaces c) (hw : w ∈ sLocalFinitePolePlaces c) :
    ∃ g : N₁, ω (primitiveQuarticNormOneClass F g) = 1 ∧ atInfinity g.val = 1 ∧
      ∀ x : Primes(F), Valued.v (g.val.val.2 x) ≠ (1 : ℤᵐ⁰) ↔ x = v.val ∨ x = w.val := by
  classical
  let f (i : S) := i.val.asIdeal.inertiaDeg (𝓞 ℚ)
  have residue (i : S) (hi : i.val ∈ sLocalPrimaryPlaces S p) :
      p.asIdeal.absNorm ^ f i = i.val.asIdeal.absNorm ∧ 0 < f i := by
    have e := ((mem_sLocalPrimaryPlaces p i.val).mp hi).2
    let : i.val.asIdeal.IsPrime := i.val.isPrime
    let : i.val.asIdeal.LiesOver p.asIdeal := ⟨(congrArg HeightOneSpectrum.asIdeal e).symm⟩
    have h := Ideal.absNorm_pow_inertiaDeg p.asIdeal i.val.asIdeal
    refine ⟨h, Nat.pos_of_ne_zero fun h0 ↦ ?_⟩
    change p.asIdeal.absNorm ^ f i = i.val.asIdeal.absNorm at h
    rw [h0, pow_zero] at h
    exact (HeightOneSpectrum.one_lt_absNorm i.val).ne h
  obtain ⟨u, hu, hzu⟩ := primitiveQuartic_pole_uniformizer F c v hv
  obtain ⟨t, ht, hzt⟩ := primitiveQuartic_pole_uniformizer F c w hw
  let q : (SAdeleRing F S)ˣ →* SIdeleQuotient F S := QuotientGroup.mk' _
  let ins (i : S) (z : (i.val.adicCompletion F)ˣ) : (SAdeleRing F S)ˣ :=
    (ContinuousMulEquiv.prodUnits (InfiniteAdeleRing F) ((s : S) → s.val.adicCompletion F)).symm
      (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) i z))
  have modIns (i : S) (z : (i.val.adicCompletion F)ˣ) :
      ((sIdeleQuotientNorm F S (q (ins i z))).val : ℝ) = ‖z.val‖ := by
    have h := sLocalFiniteRestriction_norm (F := F) (S := S) i z
    change ((1 : PontryaginDual (SIdeleQuotient F S)) (q (ins i z)) : ℂ) *
      (((sIdeleQuotientNorm F S (q (ins i z))).val : ℝ) : ℂ) ^ (1 : ℂ) = _ at h
    simpa using h
  let g := ins v u ^ f w / ins w t ^ f v
  have hn : sIdeleQuotientNorm F S (q g) = 1 := by
    dsimp only [g]
    rw [map_div, map_div, div_eq_one, map_pow, map_pow, map_pow, map_pow]
    apply Units.ext
    apply NNReal.eq
    change ((sIdeleQuotientNorm F S (q (ins v u))).val : ℝ) ^ f w =
      ((sIdeleQuotientNorm F S (q (ins w t))).val : ℝ) ^ f v
    rw [modIns, modIns, hu, ht, inv_pow, inv_pow, ← Nat.cast_pow, ← Nat.cast_pow,
      ← (residue v hvp).1, ← (residue w hwp).1, ← pow_mul, ← pow_mul, Nat.mul_comm]
  let a := sIdeleInsertion F S g
  have ha : ideleNorm F a = 1 := by
    rw [ideleNorm_sIdeleInsertion, ← sIdeleQuotientNorm_mk]
    exact hn
  let A : N₁ := ⟨a, ha⟩
  refine ⟨A, ?_, ?_, ?_⟩
  · have hχ : (sLocalNormOneCharacter S ω hω ⟨q g, hn⟩ : ℂ) = 1 := by
      rw [← hc]
      change c (q (ins v u ^ f w / ins w t ^ f v)) = 1
      rw [map_div, map_div, map_pow, map_pow, map_pow, map_pow,
        show c (q (ins v u)) = 1 from hzu, show c (q (ins w t)) = 1 from hzt,
        one_pow, one_pow, div_one]
    obtain ⟨d, hd⟩ := hω
    apply Circle.ext
    have hx := sLocalNormOneCharacter_eq_sIdeleRestriction ω d hd ⟨q g, hn⟩
    rw [hχ] at hx
    change 1 = sIdeleRestriction F S d (QuotientGroup.mk g) at hx
    rw [sIdeleRestriction_mk] at hx
    exact (hd (primitiveQuarticNormOneClass F A)).symm.trans hx.symm
  · apply Units.ext
    change a.val.1 = 1
    rw [(sIdeleInsertion_apply F S g).1]
    let arch := Units.map (RingHom.fst (InfiniteAdeleRing F) ((i : S) → i.val.adicCompletion F)).toMonoidHom
    have hIns (i : S) (z : (i.val.adicCompletion F)ˣ) : arch (ins i z) = 1 := rfl
    have h := (show arch g = 1 by simp [g, hIns])
    exact congrArg Units.val h
  · have hnormSupport (i : S) : ‖g.val.2 i‖ ≠ 1 ↔ i = v ∨ i = w := by
      let fin : (SAdeleRing F S)ˣ →* (i.val.adicCompletion F)ˣ :=
        Units.map ((Pi.evalRingHom (fun j : S ↦ j.val.adicCompletion F) i).comp
          (RingHom.snd _ _)).toMonoidHom
      have hs (z : (i.val.adicCompletion F)ˣ) : fin (ins i z) = z := by
        change (@Pi.mulSingle S (fun j : S ↦ (j.val.adicCompletion F)ˣ) _
          (Classical.decEq _) i z) i = z
        exact @Pi.mulSingle_eq_same S (fun j : S ↦ (j.val.adicCompletion F)ˣ) _
          (Classical.decEq _) i z
      have ho (j : S) (z : (j.val.adicCompletion F)ˣ) (h : j ≠ i) : fin (ins j z) = 1 := by
        change (@Pi.mulSingle S (fun j : S ↦ (j.val.adicCompletion F)ˣ) _
          (Classical.decEq _) j z) i = 1
        exact @Pi.mulSingle_eq_of_ne S (fun j : S ↦ (j.val.adicCompletion F)ˣ) _
          (Classical.decEq _) j i h.symm z
      change ‖(fin g).val‖ ≠ 1 ↔ i = v ∨ i = w
      rw [show fin g = fin (ins v u) ^ f w / fin (ins w t) ^ f v by simp only [g, map_div, map_pow],
        Units.val_div_eq_div_val, norm_div, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
        norm_pow, norm_pow]
      by_cases hiv : i = v
      · subst i
        rw [hs u, ho w t hne.symm, Units.val_one, norm_one, one_pow, div_one, hu]
        have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
          exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
        have hlt := pow_lt_one₀ (by positivity : 0 ≤ (v.val.asIdeal.absNorm : ℝ)⁻¹)
          (inv_lt_one_of_one_lt₀ hq) (residue w hwp).2.ne'
        exact ⟨fun _ ↦ Or.inl rfl, fun _ ↦ hlt.ne⟩
      · by_cases hiw : i = w
        · subst i
          rw [hs t, ho v u hne, Units.val_one, norm_one, one_pow, one_div, ht]
          have hq : 1 < (w.val.asIdeal.absNorm : ℝ) := by
            exact_mod_cast HeightOneSpectrum.one_lt_absNorm w.val
          have hlt := pow_lt_one₀ (by positivity : 0 ≤ (w.val.asIdeal.absNorm : ℝ)⁻¹)
            (inv_lt_one_of_one_lt₀ hq) (residue v hvp).2.ne'
          exact ⟨fun _ ↦ Or.inr rfl, fun _ h ↦ hlt.ne (inv_eq_one.mp h)⟩
        · rw [ho v u (Ne.symm hiv), ho w t (Ne.symm hiw)]
          simp [hiv, hiw]
    intro x
    by_cases hx : x ∈ S
    · let i : S := ⟨x, hx⟩
      change Valued.v (a.val.2 x) ≠ 1 ↔ x = v.val ∨ x = w.val
      rw [(sIdeleInsertion_apply F S g).2.1 i]
      refine (not_congr Valued.toNormedField.norm_eq_one_iff.symm).trans ((hnormSupport i).trans ?_)
      exact or_congr Subtype.ext_iff Subtype.ext_iff
    · change Valued.v (a.val.2 x) ≠ 1 ↔ x = v.val ∨ x = w.val
      rw [(sIdeleInsertion_apply F S g).2.2 x hx, map_one]
      simp [show x ≠ v.val from fun h ↦ hx (h ▸ v.property),
        show x ≠ w.val from fun h ↦ hx (h ▸ w.property)]

end

/-! ### The archimedean character and the logarithms -/

section

open NumberField InfinitePlace.Completion IsDedekindDomain Topology
open NumberField.Units
open scoped NNReal Classical WithZero

variable (F : Type*) [Field F] [NumberField F]

local notation "C" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "A∞" => InfiniteAdeleRing F
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

private def primitiveQuarticArchInsertion : A∞ˣ →* IdeleGroup (𝓞 F) F :=
  Units.map (MonoidHom.inl A∞ (FiniteAdeleRing (𝓞 F) F))

/-- Passage from the norm-one archimedean ideles to norm-one idele classes. -/
def primitiveQuarticArchClass : N∞ →ₜ* C₁ :=
  let q : IdeleGroup (𝓞 F) F →* C := QuotientGroup.mk' _
  let f := (q.comp (primitiveQuarticArchInsertion F)).comp
    (infiniteIdeleNorm F).ker.subtype
  { f.codRestrict _ (fun g => by
      change ideleNorm F (primitiveQuarticArchInsertion F g.val) = 1
      rw [primitiveQuarticArchInsertion, ← infiniteIdeleNorm_eq_global F]
      exact g.property) with
    continuous_toFun := by
      apply Continuous.subtype_mk
      exact (QuotientGroup.continuous_mk.comp
        ((continuous_id.prodMk continuous_const).units_map _)).comp continuous_subtype_val }

private def primitiveQuarticArchUnit (w : InfinitePlace F) (g : A∞ˣ) :
    w.Completionˣ :=
  Units.map (Pi.evalRingHom _ w).toMonoidHom g

private theorem primitiveQuarticArchClass_eq_mul (w₁ w₂ : InfinitePlace F)
    (hd : w₁ ≠ w₂) (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂)
    (g : N∞) :
    (primitiveQuarticArchClass F g).val =
      IdeleClassGroup.ofCompletion (𝓞 F) F w₁ (primitiveQuarticArchUnit F w₁ g.val) *
        IdeleClassGroup.ofCompletion (𝓞 F) F w₂ (primitiveQuarticArchUnit F w₂ g.val) := by
  let q : IdeleGroup (𝓞 F) F →* C := QuotientGroup.mk' _
  change q (primitiveQuarticArchInsertion F g.val) =
    q (IdeleGroup.ofCompletion (𝓞 F) F w₁ (primitiveQuarticArchUnit F w₁ g.val)) *
      q (IdeleGroup.ofCompletion (𝓞 F) F w₂ (primitiveQuarticArchUnit F w₂ g.val))
  rw [← map_mul]
  congr 1
  apply Units.ext
  apply Prod.ext
  · funext w
    change g.val.val w =
      Pi.mulSingle (M := fun v : InfinitePlace F => v.Completion) w₁ (g.val.val w₁) w *
        Pi.mulSingle (M := fun v : InfinitePlace F => v.Completion) w₂ (g.val.val w₂) w
    rcases hc w with rfl | rfl
    · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hd, mul_one]
    · rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hd.symm, one_mul]
  · change (1 : FiniteAdeleRing (𝓞 F) F) = 1 * 1
    exact (one_mul _).symm

private theorem primitiveQuarticArchLocal_parameters (c : HeckeCharacter (𝓞 F) F)
    (hc : ∀ a, ‖c a‖ = 1) (w : InfinitePlace F) (hw : w.IsComplex) :
    ∃ (t : ℝ) (m : ℤ), ∀ u : w.Completionˣ,
      let z := extensionEmbedding w u.val
      c (IdeleClassGroup.ofCompletion (𝓞 F) F w u) =
        Complex.exp ((t : ℂ) * Complex.I * (Real.log ‖z‖ : ℂ)) *
          (z / (‖z‖ : ℂ)) ^ m := by
  let e := ringEquivComplexOfIsComplex hw
  let p : ℂˣ →ₜ* w.Completionˣ :=
    ⟨Units.map e.symm.toMonoidHom,
      (isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
  let d : ℂˣ →ₜ* ℂ := (infinitePlaceRestriction F w c).comp p
  have hdn (z : ℂˣ) : ‖d z‖ = 1 := hc _
  obtain ⟨⟨a, m⟩, ⟨ha, hp⟩, _⟩ := existsUnique_complexUnits_character_parameters d hdn
  refine ⟨2 * a.im, m, fun u => ?_⟩
  let x := Units.map e.toMonoidHom u
  have hx : (x : ℂ) = extensionEmbedding w u.val := ringEquivComplexOfIsComplex_apply hw u.val
  have hpu : p x = u := Units.ext (e.symm_apply_apply _)
  have hdp : d x = c (IdeleClassGroup.ofCompletion (𝓞 F) F w u) := by
    change c (IdeleClassGroup.ofCompletion (𝓞 F) F w (p x)) = _
    rw [hpu]
  change c (IdeleClassGroup.ofCompletion (𝓞 F) F w u) = _
  rw [← hdp, hp x]
  change ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ a * _ = _
  have hapos : 0 < ‖(x : ℂ)‖ := norm_pos_iff.mpr x.ne_zero
  have harr : a = (a.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa using ha
    · simp
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (pow_pos hapos 2).ne'),
    ← Complex.ofReal_log (pow_pos hapos 2).le, Real.log_pow]
  nth_rw 1 [harr]
  rw [hx]
  push_cast
  congr 1
  ring

private theorem primitiveQuarticArch_log (w₁ w₂ : InfinitePlace F)
    (h₁ : w₁.IsComplex) (h₂ : w₂.IsComplex) (hd : w₁ ≠ w₂)
    (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂) (g : N∞) :
    Real.log ‖extensionEmbedding w₂ (g.val.val w₂)‖ =
      -Real.log ‖extensionEmbedding w₁ (g.val.val w₁)‖ := by
  have hu : (Finset.univ : Finset (InfinitePlace F)) = {w₁, w₂} := by
    ext w
    simpa using hc w
  have h := infiniteIdeleLog_sum_zero F g
  rw [hu, Finset.sum_pair hd] at h
  rw [(isometry_extensionEmbedding w₁).norm_map_of_map_zero (map_zero _) _,
    (isometry_extensionEmbedding w₂).norm_map_of_map_zero (map_zero _) _]
  simp only [infiniteIdeleLog, h₁.mult_eq_two, h₂.mult_eq_two, Nat.cast_ofNat] at h
  linarith

/-- On norm-one archimedean ideles with two complex places, a unitary character has
one radial frequency and two integral angular frequencies. -/
theorem primitiveQuarticArchCharacter_parameters (ω : PontryaginDual C₁)
    (w₁ w₂ : InfinitePlace F) (h₁ : w₁.IsComplex) (h₂ : w₂.IsComplex)
    (hd : w₁ ≠ w₂) (hc : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂) :
    ∃ (t : ℝ) (m₁ m₂ : ℤ), ∀ g : N∞,
      let z₁ := extensionEmbedding w₁ (g.val.val w₁)
      let z₂ := extensionEmbedding w₂ (g.val.val w₂)
      (ω (primitiveQuarticArchClass F g) : ℂ) =
        Complex.exp ((t : ℂ) * Complex.I * (Real.log ‖z₁‖ : ℂ)) *
          (z₁ / (‖z₁‖ : ℂ)) ^ m₁ * (z₂ / (‖z₂‖ : ℂ)) ^ m₂ := by
  let s : ℝ≥0ˣ →* C :=
    (QuotientGroup.mk' _).comp (canonicalIdeleNormSection F)
  have hs : Function.RightInverse s (ideleClassNorm F) :=
    canonicalIdeleNormSection_rightInverse F
  have hcNorm : Continuous (ideleClassNorm F) :=
    (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.1
  let r : C →ₜ* C₁ :=
    { toFun := fun a => ⟨a / s (ideleClassNorm F a), by rw [MonoidHom.mem_ker, map_div, hs, div_self']⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [map_mul, mul_div_mul_comm]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_id.div'
          ((QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous F)).comp hcNorm) }
  have hr (a : C₁) : r a.val = a := by
    apply Subtype.ext
    change a.val / s (ideleClassNorm F a.val) = a.val
    rw [MonoidHom.mem_ker.mp a.property, map_one, div_one]
  let c : HeckeCharacter (𝓞 F) F :=
    (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (ω.comp r)
  have hcn (a : C) : ‖c a‖ = 1 := Circle.norm_coe _
  obtain ⟨t₁, m₁, hm₁⟩ := primitiveQuarticArchLocal_parameters F c hcn w₁ h₁
  obtain ⟨t₂, m₂, hm₂⟩ := primitiveQuarticArchLocal_parameters F c hcn w₂ h₂
  refine ⟨t₁ - t₂, m₁, m₂, fun g => ?_⟩
  have hcg : c (primitiveQuarticArchClass F g).val = (ω (primitiveQuarticArchClass F g) : ℂ) := by
    change (ω (r (primitiveQuarticArchClass F g).val) : ℂ) = _
    rw [hr]
  rw [← hcg, primitiveQuarticArchClass_eq_mul F w₁ w₂ hd hc, map_mul, hm₁, hm₂]
  let z₁ := extensionEmbedding w₁ (g.val.val w₁)
  let z₂ := extensionEmbedding w₂ (g.val.val w₂)
  change Complex.exp ((t₁ : ℂ) * Complex.I * (Real.log ‖z₁‖ : ℂ)) *
      (z₁ / (‖z₁‖ : ℂ)) ^ m₁ *
      (Complex.exp ((t₂ : ℂ) * Complex.I * (Real.log ‖z₂‖ : ℂ)) *
        (z₂ / (‖z₂‖ : ℂ)) ^ m₂) =
    Complex.exp (((t₁ - t₂ : ℝ) : ℂ) * Complex.I * (Real.log ‖z₁‖ : ℂ)) *
      (z₁ / (‖z₁‖ : ℂ)) ^ m₁ * (z₂ / (‖z₂‖ : ℂ)) ^ m₂
  have hlog : Real.log ‖z₂‖ = -Real.log ‖z₁‖ := primitiveQuarticArch_log F w₁ w₂ h₁ h₂ hd hc g
  rw [hlog, Complex.ofReal_neg]
  rw [mul_mul_mul_comm, ← Complex.exp_add, ← mul_assoc]
  push_cast
  congr 2
  ring_nf

private theorem primitiveQuarticArchUnit_normOne (u : (𝓞 F)ˣ) :
    infiniteIdeleNorm F (Units.map (((algebraMap F A∞).comp (algebraMap (𝓞 F) F)).toMonoidHom) u) =
      1 := by
  apply Units.ext
  apply NNReal.coe_injective
  have hterm (v : InfinitePlace F) :
      ‖(algebraMap F A∞ (algebraMap (𝓞 F) F u.val)) v‖ =
        v (algebraMap (𝓞 F) F u.val) := by
    rw [InfiniteAdeleRing.algebraMap_apply, AbsoluteValue.Completion.norm_coe, WithAbs.ofAbs_toAbs]
    rfl
  simp only [infiniteIdeleNorm, Units.val_one, NNReal.coe_one, MonoidHom.finsetProd_apply,
    MonoidHom.pow_apply, MonoidHom.comp_apply, Units.coe_prod, Units.val_pow_eq_pow_val,
    NNReal.coe_prod, NNReal.coe_pow]
  change ∏ v : InfinitePlace F,
      ‖(algebraMap F A∞ (algebraMap (𝓞 F) F u.val)) v‖ ^ v.mult = 1
  simp_rw [hterm, InfinitePlace.prod_eq_abs_norm, Units.norm]
  norm_cast

/-- The archimedean diagonal of a global unit has norm one. -/
def primitiveQuarticArchUnitDiagonal (u : (𝓞 F)ˣ) : N∞ :=
  ⟨Units.map (((algebraMap F A∞).comp (algebraMap (𝓞 F) F)).toMonoidHom) u,
    primitiveQuarticArchUnit_normOne F u⟩

/-- The archimedean diagonal agrees with the place's embedding of the global unit. -/
theorem primitiveQuarticArchUnitDiagonal_apply (u : (𝓞 F)ˣ) (w : InfinitePlace F) :
    extensionEmbedding w ((primitiveQuarticArchUnitDiagonal F u).val.val w) =
      w.embedding (u : F) := by
  change extensionEmbedding w (algebraMap F A∞ (u : F) w) = _
  rw [InfiniteAdeleRing.algebraMap_apply, extensionEmbedding_coe]
  rfl

/-- A number field with two infinite places has a nontorsion unit. -/
theorem primitiveQuarticArch_exists_unit (h : Fintype.card (InfinitePlace F) = 2) :
    ∃ u : (𝓞 F)ˣ, u ∉ Units.torsion F := by
  let i : Fin (NumberField.Units.rank F) := ⟨0, by simp [NumberField.Units.rank, h]⟩
  refine ⟨fundSystem F i, fun hu => ?_⟩
  have he : (QuotientGroup.mk (fundSystem F i) : (𝓞 F)ˣ ⧸ Units.torsion F) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hu
  have hb := fundSystem_mk F i
  rw [he] at hb
  exact (basisModTorsion F).ne_zero i hb.symm

local notation "J" => IdeleGroup (𝓞 F) F
local notation "J₁" => MonoidHom.ker (ideleNorm F)
local notation "j" => Units.map (RingHom.toMonoidHom (Subring.subtype (integralAdelesOutside F ∅)))
local notation "q" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "p∞" =>
  Units.map (RingHom.toMonoidHom (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))

/-- The finite class group and a common exponent on finite integral units make any
character trivial on the norm-one archimedean ideles a finite-order character. -/
theorem primitiveQuarticArch_trivial_finiteOrder (ω : PontryaginDual C₁)
    (hArch : ∀ g : N∞, ω (primitiveQuarticArchClass F g) = 1) :
    IsOfFinOrder ω := by
  obtain ⟨n, hn, hfin⟩ := primitiveQuartic_finite_unit_character_exponent F ω
  obtain ⟨p, _, _, hexact, _⟩ := normOne_ideal_class_exact F
  let h := Nat.card (CommRing.Pic (𝓞 F))
  obtain ⟨_, _, _, _, _, hFinite, ⟨ePic⟩⟩ := ideleClassGroup_finiteness F
  let : Finite (CommRing.Pic (𝓞 F)) := @Finite.of_equiv _ _ hFinite ePic.toEquiv
  have hh : 0 < h := Nat.card_pos
  apply isOfFinOrder_iff_pow_eq_one.mpr
  refine ⟨h * n, Nat.mul_pos hh hn, ?_⟩
  apply PontryaginDual.ext
  intro a
  change (((ω : C₁ →ₜ* Circle) ^ (h * n)) a) = 1
  refine (ContinuousMonoidHom.pow_apply (ω : C₁ →ₜ* Circle) (h * n) a).trans ?_
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective a.val
  let X : J₁ := ⟨x, by
    change ideleClassNorm F (QuotientGroup.mk x) = 1
    rw [hx]
    exact a.property⟩
  have hxa : primitiveQuarticNormOneClass F X = a := Subtype.ext hx
  have hpow : p (X ^ h) = 1 :=
    (map_pow p X h).trans (pow_card_eq_one' (x := p X))
  obtain ⟨y, hy⟩ := (hexact _).mp hpow
  have hy' : (X ^ h).val ∈ IdeleGroup.principalSubgroup (𝓞 F) F ⊔ (MonoidHom.range j) := by
    rw [← hy]
    exact y.property
  obtain ⟨d, hd, b, hb, hdb⟩ := Subgroup.mem_sup.mp hy'
  have hdNorm : ideleNorm F d = 1 := (ideleNorm_spec F).2 hd
  have hbNorm : ideleNorm F b = 1 := by
    have hnorm := congrArg (ideleNorm F) hdb
    rw [map_mul, hdNorm, one_mul] at hnorm
    exact hnorm.trans (X ^ h).property
  let B : J₁ := ⟨b, hbNorm⟩
  have hba : primitiveQuarticNormOneClass F B = a ^ h := by
    apply Subtype.ext
    have H := congrArg q hdb
    have hqd : q d = 1 := (QuotientGroup.eq_one_iff _).mpr hd
    rw [map_mul, hqd, one_mul] at H
    change q b = _
    exact H.trans (congrArg Subtype.val ((map_pow (primitiveQuarticNormOneClass F) X h).trans
      (congrArg (fun k : C₁ => k ^ h) hxa)))
  let g : N∞ := ⟨p∞ b, primitiveQuartic_infiniteNorm_of_integral F b hb hbNorm⟩
  let bArch := primitiveQuarticArchInsertion F g.val
  have hbArchnorm : ideleNorm F bArch = 1 :=
    (infiniteIdeleNorm_eq_global F g.val).symm.trans g.property
  have hbArch : bArch ∈ (MonoidHom.range j) := by
    apply (mem_integralIdeleRange_iff F _).mpr
    intro v
    change Valued.v (1 : v.adicCompletion F) = 1
    exact map_one _
  let U : J₁ := ⟨b / bArch, MonoidHom.mem_ker.mpr (by rw [map_div, hbNorm, hbArchnorm, div_one])⟩
  have hU : U.val ∈ (MonoidHom.range j) := (MonoidHom.range j).div_mem hb hbArch
  have hUArch : p∞ U.val = 1 := by
    change p∞ (b / bArch) = 1
    rw [map_div, show p∞ bArch = p∞ b by apply Units.ext; rfl, div_self']
  have hB : B = U * (⟨bArch, hbArchnorm⟩ : J₁) := by
    apply Subtype.ext
    exact (div_mul_cancel b bArch).symm
  let w : C₁ →* Circle := (ω : C₁ →ₜ* Circle).toMonoidHom
  change w a ^ (h * n) = 1
  rw [pow_mul, ← map_pow w, ← hba, hB, map_mul, map_mul]
  change (ω (primitiveQuarticNormOneClass F U) * ω (primitiveQuarticArchClass F g)) ^ n = _
  rw [hArch g, mul_one]
  exact hfin U hU hUArch

end

/-- Classical input: the Six Exponentials Theorem of Siegel, Lang, and Ramachandra.
See Michel Waldschmidt, *The Role of Complex Conjugation in Transcendental Number
Theory*, Theorem 2.1, p. 4,
https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/DION2005proceedings.pdf. -/
private theorem sixExponentials (x : Fin 2 → ℂ) (y : Fin 3 → ℂ)
    (hx : LinearIndependent ℚ x) (hy : LinearIndependent ℚ y) :
    ∃ i j, ¬ IsAlgebraic ℚ (Complex.exp (x i * y j)) := by
  sorry

private theorem sixExponentials_for_quartic (t : ℝ) (ht : t ≠ 0) (ell : Fin 3 → ℝ)
    (hell : LinearIndependent ℚ ell)
    (halg : ∀ j, IsAlgebraic ℚ ((Real.exp (ell j) : ℝ) : ℂ))
    (hχ : ∀ j, IsAlgebraic ℚ (Complex.exp ((t : ℂ) * Complex.I * (ell j : ℂ)))) :
    False := by
  let x : Fin 2 → ℂ := ![1, (t : ℂ) * Complex.I]
  have hx : LinearIndependent ℚ x := by
    rw [linearIndependent_fin2]
    constructor
    · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr ht) Complex.I_ne_zero
    · intro a ha
      have h := congrArg Complex.re ha
      simp [x, Rat.smul_def, Complex.mul_re] at h
  let f : ℝ →ₗ[ℚ] ℂ := Complex.ofRealCLM.toLinearMap.restrictScalars ℚ
  have hf : f.ker = ⊥ := LinearMap.ker_eq_bot.mpr Complex.ofReal_injective
  obtain ⟨i, j, hj⟩ := sixExponentials x (fun j ↦ (ell j : ℂ)) hx (hell.map' f hf)
  apply hj
  fin_cases i
  · simpa [x, Complex.ofReal_exp] using halg j
  · exact hχ j

private def logAbsEmbedding {F : Type*} [Field F] (σ : F →+* ℂ) : Additive Fˣ →+ ℝ where
  toFun x := Real.log ‖σ (x.toMul : F)‖
  map_zero' := by simp
  map_add' x y := by
    change Real.log ‖σ ((x.toMul : F) * (y.toMul : F))‖ = _
    rw [map_mul, norm_mul, Real.log_mul]
    · exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr x.toMul.ne_zero)
    · exact norm_ne_zero_iff.mpr ((map_ne_zero σ).mpr y.toMul.ne_zero)

private theorem zpow_infinite_order {M : Type*} [Group M] {u : M} {a : ℤ}
    (hu : ¬ IsOfFinOrder u) (h : IsOfFinOrder (u ^ a)) : a = 0 := by
  obtain ⟨N, hN, hp⟩ := h.exists_pow_eq_one
  rw [← zpow_natCast, ← zpow_mul] at hp
  by_contra hn
  exact hu (isOfFinOrder_iff_zpow_eq_one.mpr ⟨a * (N : ℤ), by exact mul_ne_zero hn (by
    exact_mod_cast hN.ne'), hp⟩)

private theorem order_support_coefficients {M V : Type*} [CommGroup M] [DecidableEq V]
    (ord : V → M →* Multiplicative ℤ) (S T : Finset V) (hS : S.card = 2) (hT : T.card = 2)
    (hne : S ≠ T) (u g h : M) (hu : ∀ v, ord v u = 1)
    (hg : ∀ v, ord v g ≠ 1 ↔ v ∈ S) (hh : ∀ v, ord v h ≠ 1 ↔ v ∈ T)
    (a b d : ℤ) (ht : IsOfFinOrder (u ^ a * g ^ b * h ^ d)) : b = 0 ∧ d = 0 := by
  have hleft : ¬ S ⊆ T := fun h ↦ hne
    (Finset.eq_of_subset_of_card_le h (by omega))
  have hright : ¬ T ⊆ S := fun h ↦ hne.symm
    (Finset.eq_of_subset_of_card_le h (by omega))
  obtain ⟨v, hvS, hvT⟩ := Finset.not_subset.mp hleft
  obtain ⟨w, hwT, hwS⟩ := Finset.not_subset.mp hright
  have hz (v : V) : ord v (u ^ a * g ^ b * h ^ d) = 1 := ((ord v).isOfFinOrder ht).eq_one'
  have hv : ord v g ^ b = 1 := by
    simpa only [map_mul, map_zpow, hu v, not_ne_iff.mp (mt (hh v).mp hvT), one_zpow,
      one_mul, mul_one] using hz v
  have hw : ord w h ^ d = 1 := by
    simpa only [map_mul, map_zpow, hu w, not_ne_iff.mp (mt (hg w).mp hwS), one_zpow,
      one_mul] using hz w
  have expand (k : ℤ) (x : Multiplicative ℤ) (hx : x ≠ 1) (h : x ^ k = 1) : k = 0 := by
    have he : k * x.toAdd = 0 := congrArg Multiplicative.toAdd h
    exact (mul_eq_zero.mp he).resolve_right hx
  exact ⟨expand b _ ((hg v).mpr hvS) hv, expand d _ ((hh w).mpr hwT) hw⟩

private theorem logAbs_independent_of_distinct_supports {F V : Type*} [Field F] [DecidableEq V]
    (σ : F →+* ℂ) (ord : V → Fˣ →* Multiplicative ℤ) (S T : Finset V)
    (hS : S.card = 2) (hT : T.card = 2) (hne : S ≠ T) (u g h : Fˣ)
    (hlog : ∀ x : Fˣ, logAbsEmbedding σ (Additive.ofMul x) = 0 → IsOfFinOrder x)
    (hu : ∀ v, ord v u = 1) (huOrder : ¬ IsOfFinOrder u)
    (hg : ∀ v, ord v g ≠ 1 ↔ v ∈ S) (hh : ∀ v, ord v h ≠ 1 ↔ v ∈ T) :
    LinearIndependent ℚ ![logAbsEmbedding σ (Additive.ofMul u),
      logAbsEmbedding σ (Additive.ofMul g), logAbsEmbedding σ (Additive.ofMul h)] := by
  apply (LinearIndependent.iff_fractionRing ℤ ℚ).mp
  apply Fintype.linearIndependent_iff.mpr
  intro a ha i
  let b := a 0
  let d := a 1
  let e := a 2
  let x : Fˣ := u ^ b * g ^ d * h ^ e
  have hx : logAbsEmbedding σ (Additive.ofMul x) = 0 := by
    rw [Fin.sum_univ_three] at ha
    change logAbsEmbedding σ (b • Additive.ofMul u + d • Additive.ofMul g +
      e • Additive.ofMul h) = 0
    rw [map_add, map_add, map_zsmul, map_zsmul, map_zsmul]
    exact ha
  have ht := hlog x hx
  obtain ⟨hd, he⟩ := order_support_coefficients ord S T hS hT hne u g h hu hg hh b d e ht
  have hu' : IsOfFinOrder (u ^ b) := by
    simpa only [x, hd, he, zpow_zero, mul_one] using ht
  have hb := zpow_infinite_order huOrder hu'
  fin_cases i
  · exact hb
  · exact hd
  · exact he

private theorem algebraic_norm_of_algebraic {z : ℂ} (hz : IsAlgebraic ℚ z) :
    IsAlgebraic ℚ (‖z‖ : ℂ) := by
  apply IsAlgebraic.of_pow (n := 2) (by decide)
  rw [← Complex.mul_conj']
  exact hz.mul (hz.algHom (starRingEnd ℂ).toRatAlgHom)

private theorem algebraic_zpow {z : ℂ} (hz : IsAlgebraic ℚ z) (m : ℤ) :
    IsAlgebraic ℚ (z ^ m) := by
  cases m with
  | ofNat n =>
      change IsAlgebraic ℚ (z ^ (n : ℤ))
      rw [zpow_natCast]
      exact hz.pow n
  | negSucc n => simpa only [zpow_negSucc] using (hz.pow (n + 1)).inv

private theorem exp_radial_algebraic {z₁ z₂ : ℂ} (hz₁ : IsAlgebraic ℚ z₁)
    (hz₂ : IsAlgebraic ℚ z₂) (hn₁ : z₁ ≠ 0) (hn₂ : z₂ ≠ 0) (m₁ m₂ : ℤ) (t l : ℝ)
    (ht : IsOfFinOrder (Complex.exp ((t : ℂ) * Complex.I * (l : ℂ)) *
      (z₁ / (‖z₁‖ : ℂ)) ^ m₁ * (z₂ / (‖z₂‖ : ℂ)) ^ m₂)) :
    IsAlgebraic ℚ (Complex.exp ((t : ℂ) * Complex.I * (l : ℂ))) := by
  have h₁ : IsAlgebraic ℚ ((z₁ / (‖z₁‖ : ℂ)) ^ m₁) :=
    algebraic_zpow (by
      rw [div_eq_mul_inv]
      exact hz₁.mul (algebraic_norm_of_algebraic hz₁).inv) m₁
  have h₂ : IsAlgebraic ℚ ((z₂ / (‖z₂‖ : ℂ)) ^ m₂) :=
    algebraic_zpow (by
      rw [div_eq_mul_inv]
      exact hz₂.mul (algebraic_norm_of_algebraic hz₂).inv) m₂
  have h₁' : (z₁ / (‖z₁‖ : ℂ)) ^ m₁ ≠ 0 := zpow_ne_zero _ (div_ne_zero hn₁
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn₁)))
  have h₂' : (z₂ / (‖z₂‖ : ℂ)) ^ m₂ ≠ 0 := zpow_ne_zero _ (div_ne_zero hn₂
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hn₂)))
  have hA : IsAlgebraic ℚ (Complex.exp ((t : ℂ) * Complex.I * (l : ℂ)) *
      (z₁ / (‖z₁‖ : ℂ)) ^ m₁ * (z₂ / (‖z₂‖ : ℂ)) ^ m₂) := by
    obtain ⟨N, hN, he⟩ := ht.exists_pow_eq_one
    exact IsAlgebraic.of_pow hN (he.symm ▸ isAlgebraic_one)
  have h : IsAlgebraic ℚ ((Complex.exp ((t : ℂ) * Complex.I * (l : ℂ)) *
      (z₁ / (‖z₁‖ : ℂ)) ^ m₁ * (z₂ / (‖z₂‖ : ℂ)) ^ m₂) /
      (z₂ / (‖z₂‖ : ℂ)) ^ m₂ / (z₁ / (‖z₁‖ : ℂ)) ^ m₁) := by
    simpa only [div_eq_mul_inv] using (hA.mul h₂.inv).mul h₁.inv
  rwa [mul_div_cancel_right₀ _ h₂', mul_div_cancel_right₀ _ h₁'] at h

private theorem angular_square {z : ℂ} (hz : z ≠ 0) :
    (z / (‖z‖ : ℂ)) ^ 2 = z / star z := by
  rw [div_pow, ← Complex.mul_conj']
  change z ^ 2 / (z * star z) = z / star z
  field_simp [hz, star_ne_zero.mpr hz]

private theorem angular_product_square {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) (m n : ℤ) :
    ((z / (‖z‖ : ℂ)) ^ m * (w / (‖w‖ : ℂ)) ^ n) ^ 2 =
      (z / star z) ^ m * (w / star w) ^ n := by
  have h (ζ : ℂ) (hζ : ζ ≠ 0) (k : ℤ) :
      ((ζ / (‖ζ‖ : ℂ)) ^ k) ^ 2 = (ζ / star ζ) ^ k := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, angular_square hζ]
  rw [mul_pow, h z hz m, h w hw n]

private theorem algebraic_norm_embedding {F : Type*} [Field F] [NumberField F]
    (σ : F →+* ℂ) (x : F) : IsAlgebraic ℚ (‖σ x‖ : ℂ) :=
  algebraic_norm_of_algebraic ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom σ.toRatAlgHom)

open NumberField InfinitePlace.Completion IsDedekindDomain Topology
open scoped Classical NNReal WithZero

section

variable {F : Type*} [Field F] [NumberField F]

local notation "Prime" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "N∞" => MonoidHom.ker (infiniteIdeleNorm F)

private def primitiveOrd (v : Prime) : Fˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (v.valuation F).toMonoidWithZeroHom.toMonoidHom)

private theorem primitiveOrd_eq_one (v : Prime) (a : Fˣ) :
    primitiveOrd v a = 1 ↔ v.valuation F (a : F) = 1 := by
  change WithZero.unitsWithZeroEquiv
    (Units.map (v.valuation F).toMonoidWithZeroHom.toMonoidHom a) = 1 ↔ _
  rw [← map_one WithZero.unitsWithZeroEquiv, WithZero.unitsWithZeroEquiv.injective.eq_iff]
  refine ⟨fun h ↦ congrArg Units.val h, fun h ↦ ?_⟩
  apply Units.ext
  exact h

private theorem primitiveOrd_unit (v : Prime) (u : (𝓞 F)ˣ) :
    primitiveOrd v (Units.map (algebraMap (𝓞 F) F).toMonoidHom u) = 1 := by
  rw [primitiveOrd_eq_one]
  change v.valuation F (algebraMap (𝓞 F) F (u : 𝓞 F)) = 1
  rw [v.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.mpr (v.asIdeal.notMem_of_isUnit u.isUnit)

private theorem primitiveQuartic_two_infinite_places [IsTotallyComplex F]
    (hdegree : Module.finrank ℚ F = 4) : Fintype.card (InfinitePlace F) = 2 := by
  have h := IsTotallyComplex.finrank F
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  omega

private theorem primitiveQuartic_log_zero_torsion [IsTotallyComplex F]
    (hdegree : Module.finrank ℚ F = 4) (hGalois : QuarticNormalClosurePairTransitive F)
    (σ : F →+* ℂ) (a : Fˣ) (ha : logAbsEmbedding σ (Additive.ofMul a) = 0) :
    IsOfFinOrder a := by
  have ha' : Real.log ‖σ (a : F)‖ = 0 := ha
  have hn := norm_pos_iff.mpr ((map_ne_zero σ).mpr a.ne_zero)
  have hm : ‖σ (a : F)‖ = 1 := by rw [← Real.exp_log hn, ha', Real.exp_zero]
  rcases quartic_eq_one_or_neg_one_of_norm_eq_one hdegree hGalois σ (a : F) hm with h | h
  · rw [show a = 1 by exact Units.ext h]
    exact IsOfFinOrder.one
  · rw [show a = -1 by exact Units.ext h]
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, neg_one_sq⟩

private theorem algebraic_exp_logAbsEmbedding (σ : F →+* ℂ) (a : Fˣ) :
    IsAlgebraic ℚ (Real.exp (logAbsEmbedding σ (Additive.ofMul a)) : ℂ) := by
  change IsAlgebraic ℚ (Real.exp (Real.log ‖σ (a : F)‖) : ℂ)
  rw [Real.exp_log (norm_pos_iff.mpr ((map_ne_zero σ).mpr a.ne_zero))]
  exact algebraic_norm_embedding σ a

/-- A field element has a norm-one archimedean diagonal on which the given character
takes a root-of-unity value. -/
private def PrimitiveQuarticTorsionDiagonal (ω : PontryaginDual C₁) (a : Fˣ) : Prop :=
  ∃ g : N∞,
    (∀ w : InfinitePlace F, extensionEmbedding w (g.val.val w) = w.embedding (a : F)) ∧
    IsOfFinOrder (ω (primitiveQuarticArchClass F g))

private theorem primitiveQuartic_radial_ne_zero [IsTotallyComplex F]
    (hdegree : Module.finrank ℚ F = 4) (hGalois : QuarticNormalClosurePairTransitive F)
    (ω : PontryaginDual C₁)
    (hω : ¬ ∀ g : N∞, ω (primitiveQuarticArchClass F g) = 1)
    (u : Fˣ) (hu : ¬ IsOfFinOrder u) (hunit : PrimitiveQuarticTorsionDiagonal ω u)
    (w₁ w₂ : InfinitePlace F) (hne : w₁ ≠ w₂)
    (hall : ∀ w : InfinitePlace F, w = w₁ ∨ w = w₂)
    (t : ℝ) (m₁ m₂ : ℤ)
    (hχ : ∀ g : N∞,
      let z₁ := extensionEmbedding w₁ (g.val.val w₁)
      let z₂ := extensionEmbedding w₂ (g.val.val w₂)
      (ω (primitiveQuarticArchClass F g) : ℂ) =
        Complex.exp ((t : ℂ) * Complex.I * (Real.log ‖z₁‖ : ℂ)) *
          (z₁ / (‖z₁‖ : ℂ)) ^ m₁ * (z₂ / (‖z₂‖ : ℂ)) ^ m₂) : t ≠ 0 := by
  intro ht
  obtain ⟨g, hg, hgΩ⟩ := hunit
  have hgLog := primitiveQuarticArch_log F w₁ w₂ (IsTotallyComplex.isComplex w₁)
    (IsTotallyComplex.isComplex w₂) hne hall g
  rw [hg w₁, hg w₂] at hgLog
  have hdiff : ‖w₁.embedding (u : F)‖ ≠ ‖w₂.embedding (u : F)‖ := by
    intro h
    rw [← h] at hgLog
    exact hu (primitiveQuartic_log_zero_torsion hdegree hGalois w₁.embedding u (by
      change Real.log ‖w₁.embedding (u : F)‖ = 0
      linarith))
  have hembed : w₂.embedding ≠ w₁.embedding := by
    intro h
    apply hne
    simpa only [InfinitePlace.mk_embedding] using (congrArg InfinitePlace.mk h).symm
  have hconj : w₂.embedding ≠ ComplexEmbedding.conjugate w₁.embedding := by
    intro h
    apply hne
    simpa only [InfinitePlace.mk_embedding, InfinitePlace.mk_conjugate_eq] using
      (congrArg InfinitePlace.mk h).symm
  have hangular := Circle.coeHom.isOfFinOrder hgΩ
  rw [show Circle.coeHom (ω (primitiveQuarticArchClass F g)) =
      (ω (primitiveQuarticArchClass F g) : ℂ) from rfl, hχ g] at hangular
  simp only [ht, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul] at hangular
  rw [hg w₁, hg w₂] at hangular
  have hang := hangular.pow (n := 2)
  rw [angular_product_square ((map_ne_zero w₁.embedding).mpr u.ne_zero)
    ((map_ne_zero w₂.embedding).mpr u.ne_zero)] at hang
  obtain ⟨N, hN, hpower⟩ := hang.exists_pow_eq_one
  obtain ⟨hm₁, hm₂⟩ := quartic_angular_exponents_eq_zero hdegree hGalois
    w₁.embedding w₂.embedding hembed hconj (u : F) hdiff m₁ m₂ hN hpower
  apply hω
  intro y
  apply Subtype.ext
  change (ω (primitiveQuarticArchClass F y) : ℂ) = 1
  simpa only [ht, hm₁, hm₂, Complex.ofReal_zero, zero_mul, Complex.exp_zero, zpow_zero,
    mul_one] using hχ y

/-- Two different two-place supports, together with a nontorsion unit, would give
three independent logarithms with algebraic exponentials in both rows of the
Six Exponentials Theorem. -/
private theorem primitiveQuartic_distinct_supports_impossible [IsTotallyComplex F]
    (hdegree : Module.finrank ℚ F = 4) (hGalois : QuarticNormalClosurePairTransitive F)
    (ω : PontryaginDual C₁)
    (hω : ¬ ∀ g : N∞, ω (primitiveQuarticArchClass F g) = 1)
    (u : (𝓞 F)ˣ) (hu : u ∉ NumberField.Units.torsion F)
    (hunit : PrimitiveQuarticTorsionDiagonal ω
      (Units.map (algebraMap (𝓞 F) F).toMonoidHom u))
    (P Q : Finset Prime) (hP : P.card = 2) (hQ : Q.card = 2)
    (a b : Fˣ) (ha : ∀ v, v.valuation F (a : F) ≠ 1 ↔ v ∈ P)
    (hb : ∀ v, v.valuation F (b : F) ≠ 1 ↔ v ∈ Q)
    (haχ : PrimitiveQuarticTorsionDiagonal ω a) (hbχ : PrimitiveQuarticTorsionDiagonal ω b) :
    P = Q := by
  by_contra hPQ
  have hcard := primitiveQuartic_two_infinite_places hdegree
  let e := Fintype.equivFinOfCardEq hcard
  let w₁ := e.symm 0
  let w₂ := e.symm 1
  have hne : w₁ ≠ w₂ := e.symm.injective.ne (by decide)
  have hall (w : InfinitePlace F) : w = w₁ ∨ w = w₂ := by
    have h : e w = 0 ∨ e w = 1 := (show ∀ j : Fin 2, j = 0 ∨ j = 1 from by decide) (e w)
    exact h.imp (fun h ↦ e.injective (by simpa [w₁] using h))
      (fun h ↦ e.injective (by simpa [w₂] using h))
  obtain ⟨t, m₁, m₂, hχ⟩ := primitiveQuarticArchCharacter_parameters F ω w₁ w₂
    (IsTotallyComplex.isComplex w₁) (IsTotallyComplex.isComplex w₂) hne hall
  let U := Units.map (algebraMap (𝓞 F) F).toMonoidHom u
  have hU : ¬ IsOfFinOrder U := by
    intro h
    apply hu
    apply (CommGroup.mem_torsion u).mpr
    exact (Units.map_injective (FaithfulSMul.algebraMap_injective (𝓞 F) F)).isOfFinOrder_iff.mp h
  have ht := primitiveQuartic_radial_ne_zero hdegree hGalois ω hω U hU hunit w₁ w₂ hne hall
    t m₁ m₂ hχ
  let x : Fin 3 → Fˣ := ![U, a, b]
  let ell : Fin 3 → ℝ := fun j ↦ logAbsEmbedding w₁.embedding (Additive.ofMul (x j))
  have hell : LinearIndependent ℚ ell := by
    have he : ell = ![logAbsEmbedding w₁.embedding (Additive.ofMul U),
      logAbsEmbedding w₁.embedding (Additive.ofMul a),
      logAbsEmbedding w₁.embedding (Additive.ofMul b)] := by
      funext j
      fin_cases j <;> rfl
    rw [he]
    exact logAbs_independent_of_distinct_supports w₁.embedding primitiveOrd P Q hP hQ hPQ U a b
      (primitiveQuartic_log_zero_torsion hdegree hGalois _) (fun v ↦ primitiveOrd_unit v u) hU
      (fun v ↦ (not_congr (primitiveOrd_eq_one v a)).trans (ha v))
      (fun v ↦ (not_congr (primitiveOrd_eq_one v b)).trans (hb v))
  refine sixExponentials_for_quartic t ht ell hell (fun j ↦ algebraic_exp_logAbsEmbedding _ _) ?_
  have hex (j : Fin 3) : PrimitiveQuarticTorsionDiagonal ω (x j) := by
    fin_cases j
    · exact hunit
    · exact haχ
    · exact hbχ
  intro j
  obtain ⟨g, hg, hgω⟩ := hex j
  have h := Circle.coeHom.isOfFinOrder hgω
  change IsOfFinOrder (ω (primitiveQuarticArchClass F g) : ℂ) at h
  rw [hχ g, hg w₁, hg w₂] at h
  exact exp_radial_algebraic
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x j : F)).algHom w₁.embedding.toRatAlgHom)
    ((Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (x j : F)).algHom w₂.embedding.toRatAlgHom)
    ((map_ne_zero w₁.embedding).mpr (x j).ne_zero) ((map_ne_zero w₂.embedding).mpr (x j).ne_zero)
    m₁ m₂ t (ell j) h

end


section

variable {F : Type*} [Field F] [NumberField F]

local notation "Prime" => HeightOneSpectrum (𝓞 F)
local notation "C₁" => MonoidHom.ker (ideleClassNorm F)
local notation "N₁" => MonoidHom.ker (ideleNorm F)
local notation "J" => IdeleGroup (𝓞 F) F
local notation "atInfinity" =>
  Units.map (RingHom.toMonoidHom (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
local notation "principal" => IdeleGroup.unitEmbedding (𝓞 F) F

private theorem primitiveQuartic_unit_torsion_diagonal (ω : PontryaginDual C₁) (u : (𝓞 F)ˣ) :
    PrimitiveQuarticTorsionDiagonal ω (Units.map (algebraMap (𝓞 F) F).toMonoidHom u) := by
  let a := Units.map (algebraMap (𝓞 F) F).toMonoidHom u
  let A := primitiveQuarticArchUnitDiagonal F u
  refine ⟨A, primitiveQuarticArchUnitDiagonal_apply F u, ?_⟩
  let G : N₁ := ⟨principal a, (ideleNorm_spec F).2 (Set.mem_range_self a)⟩
  let I := primitiveQuarticArchIdele F A
  let V := G / I
  have hVfinite : V.val ∈ (Units.map (integralAdelesOutside F ∅).subtype.toMonoidHom).range := by
    apply (mem_integralIdeleRange_iff F V.val).mpr
    intro v
    let ev := Units.map ((RestrictedProduct.evalRingHom
      (fun w : Prime ↦ w.adicCompletion F) v).comp
      (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))).toMonoidHom
    have heval : ev I.val = 1 := Units.ext rfl
    change Valued.v (ev (G.val / I.val)).val = 1
    rw [map_div, heval, div_one]
    change Valued.v (algebraMap F (v.adicCompletion F) (a : F)) = 1
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := v) (a : F)).trans
      ((primitiveOrd_eq_one v a).mp (primitiveOrd_unit v u))
  have hVarch : atInfinity V.val = 1 := by
    change atInfinity (G.val / I.val) = 1
    rw [map_div]
    exact div_self' (atInfinity G.val)
  let q := primitiveQuarticNormOneClass F
  have hG : q G = 1 := by
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (principal a)).mpr (Set.mem_range_self a)
  have hV : ω (q V) = (ω (q I))⁻¹ := by
    change (ω.toMonoidHom.comp q) (G / I) = _
    rw [map_div, MonoidHom.comp_apply, MonoidHom.comp_apply, hG, map_one, one_div]
    rfl
  obtain ⟨n, hn, hnV⟩ := primitiveQuartic_finite_unit_character_exponent F ω
  have h : IsOfFinOrder (ω (q V)) := isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, hnV V hVfinite hVarch⟩
  rw [hV, isOfFinOrder_inv_iff] at h
  exact h

private theorem primitiveQuartic_pole_torsion_diagonal {T : Finset Prime}
    (ω : PontryaginDual C₁) (hT : NormOneCharacterUnramifiedOutside ω T)
    (p : HeightOneSpectrum (𝓞 ℚ)) (c : QuasiCharacter (SIdeleQuotient F T))
    (hc : ∀ x : (sIdeleQuotientNorm F T).ker,
      c x.val = (sLocalNormOneCharacter T ω hT x : ℂ))
    (v w : T) (hvw : v ≠ w) (hvp : v.val ∈ sLocalPrimaryPlaces T p)
    (hwp : w.val ∈ sLocalPrimaryPlaces T p)
    (hv : v ∈ sLocalFinitePolePlaces c) (hw : w ∈ sLocalFinitePolePlaces c) :
    ∃ a : Fˣ, (∀ x : Prime, x.valuation F (a : F) ≠ 1 ↔ x ∈ ({v.val, w.val} : Finset Prime)) ∧
      PrimitiveQuarticTorsionDiagonal ω a := by
  obtain ⟨G, hG, hGarch, hGsupp⟩ := primitiveQuartic_pole_ratio F ω hT p c hc
    v w hvw hvp hwp hv hw
  obtain ⟨a, A, hA, htorsion, hsupp⟩ := primitiveQuartic_principalize_character F ω G hG hGarch
  refine ⟨a, fun x ↦ (not_congr (hsupp x)).trans ((hGsupp x).trans (by simp)),
    A, fun w ↦ ?_, htorsion⟩
  rw [hA]
  change extensionEmbedding w (algebraMap F (InfiniteAdeleRing F) (a : F) w) = _
  rw [InfiniteAdeleRing.algebraMap_apply, extensionEmbedding_coe]
  rfl

/-- A nontorsion norm-one character of a primitive totally imaginary quartic has at
most one unordered pair of distinct finite poles above the same rational prime. The
two stages and rational primes can be chosen independently, and the quasi-characters
at the two centers restrict to the same global norm-one character. Uses the Six
Exponentials Theorem. See willzh0's argument in issue #7336. -/
public theorem primitiveQuartic_repeatedPolePair_unique [IsTotallyComplex F]
    (hdegree : Module.finrank ℚ F = 4)
    (hprimitive : ∀ K : IntermediateField ℚ F, K = ⊥ ∨ K = ⊤)
    {T U : Finset Prime} (ω : PontryaginDual C₁) (hω : ¬ IsOfFinOrder ω)
    (hT : NormOneCharacterUnramifiedOutside ω T) (hU : NormOneCharacterUnramifiedOutside ω U)
    (p q : HeightOneSpectrum (𝓞 ℚ))
    (c : QuasiCharacter (SIdeleQuotient F T)) (d : QuasiCharacter (SIdeleQuotient F U))
    (hc : ∀ x : (sIdeleQuotientNorm F T).ker, c x.val = (sLocalNormOneCharacter T ω hT x : ℂ))
    (hd : ∀ x : (sIdeleQuotientNorm F U).ker, d x.val = (sLocalNormOneCharacter U ω hU x : ℂ))
    (v w : T) (v' w' : U) (hvw : v ≠ w) (hvw' : v' ≠ w')
    (hvp : v.val ∈ sLocalPrimaryPlaces T p) (hwp : w.val ∈ sLocalPrimaryPlaces T p)
    (hvq : v'.val ∈ sLocalPrimaryPlaces U q) (hwq : w'.val ∈ sLocalPrimaryPlaces U q)
    (hv : v ∈ sLocalFinitePolePlaces c) (hw : w ∈ sLocalFinitePolePlaces c)
    (hv' : v' ∈ sLocalFinitePolePlaces d) (hw' : w' ∈ sLocalFinitePolePlaces d) :
    ({v.val, w.val} : Finset Prime) = {v'.val, w'.val} := by
  have hGalois := quarticNormalClosurePairTransitive_of_primitive hdegree hprimitive
  have hnArch : ¬ ∀ g, ω (primitiveQuarticArchClass F g) = 1 := by
    intro hχ
    exact hω (primitiveQuarticArch_trivial_finiteOrder F ω hχ)
  obtain ⟨u, hu⟩ := primitiveQuarticArch_exists_unit F (primitiveQuartic_two_infinite_places hdegree)
  obtain ⟨a, ha, haχ⟩ := primitiveQuartic_pole_torsion_diagonal ω hT p c hc v w hvw hvp hwp hv hw
  obtain ⟨b, hb, hbχ⟩ := primitiveQuartic_pole_torsion_diagonal ω hU q d hd v' w' hvw' hvq hwq hv' hw'
  exact primitiveQuartic_distinct_supports_impossible hdegree hGalois ω hnArch u hu
    (primitiveQuartic_unit_torsion_diagonal ω u) _ _ (Finset.card_pair (Subtype.val_injective.ne hvw))
    (Finset.card_pair (Subtype.val_injective.ne hvw')) a b ha hb haχ hbχ

/-- The primary finite pole multiplicity of a nontorsion norm-one character is at most two
in a primitive totally imaginary quartic. -/
public theorem primitiveQuartic_primaryPoleMultiplicity_le_two [IsTotallyComplex F]
    (hdegree : Module.finrank ℚ F = 4)
    (hprimitive : ∀ K : IntermediateField ℚ F, K = ⊥ ∨ K = ⊤)
    {T : Finset Prime} (ω : PontryaginDual C₁) (hω : ¬ IsOfFinOrder ω)
    (hT : NormOneCharacterUnramifiedOutside ω T) (p : HeightOneSpectrum (𝓞 ℚ))
    (c : QuasiCharacter (SIdeleQuotient F T))
    (hc : ∀ x : (sIdeleQuotientNorm F T).ker, c x.val = (sLocalNormOneCharacter T ω hT x : ℂ)) :
    sLocalFinitePoleMultiplicity (sLocalPrimaryPlaces T p) c ≤ 2 := by
  by_contra! h
  obtain ⟨v, w, z, hv, hw, hz, hvw, hvz, hwz⟩ := Finset.two_lt_card_iff.mp h
  obtain ⟨hv, hvp⟩ := Finset.mem_filter.mp hv
  obtain ⟨hw, hwp⟩ := Finset.mem_filter.mp hw
  obtain ⟨hz, hzp⟩ := Finset.mem_filter.mp hz
  have heq := primitiveQuartic_repeatedPolePair_unique hdegree hprimitive ω hω hT hT p p c c
    hc hc v w v z hvw hvz hvp hwp hvp hzp hv hw hv hz
  have hmem : w.val ∈ ({v.val, z.val} : Finset Prime) := by rw [← heq]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton, Subtype.val_injective.ne hvw.symm,
    Subtype.val_injective.ne hwz, false_or] at hmem

end


end RiemannMasullo.Isolated
