module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RatBridge_Theta_Isolated

/-!
# Principal value and depletion over ℚ

Workstream B for #7351, stage 2: Weil's principal value `adelePrincipalValue ℚ T` (Definition
5.3.1.4, p. 242) at a finite set `T` of places coprime to the conductor, on the homogeneous theta
of (11.3.1.3), p. 494, is the depletion operator `∏_{p ∈ T} (I - χ(p) D_p)` of
`Sec3_DirichletFixedBox_Isolated` on the half-logarithmic profile.

* `ratPV_singleton_of_invariant`: on a test invariant under the local units at `v`, the principal
  value at `v` is the test minus its translate by the idele `π` at `v`, for every uniformizer `π`.
* `ratPV_eq_sum_translate`, `adelePrincipalValue_apply_ratDirichlet`: the pointwise formula, as
  inclusion–exclusion over the subsets of `T`.
* `ratBridge_principalValue_general`, `ratBridge_principalValue_theta`: the theta identity for
  every test invariant under the local units at the places of `T` (any factors elsewhere).
* `ratBridge_principalValue`: the identity for the Dirichlet test of stage 1.

Nothing imports this module; all declarations live in `namespace RiemannMasullo.Isolated`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology IsDedekindDomain
open scoped NNReal SchwartzMap NumberField.AdeleRing TensorProduct

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

/-! ### The principal value at one place (re-derived from `Ch11_ShellStructure/Sec2a`) -/

section PVFormula

variable {F : Type*} [Field F] [NumberField F]

local notation "V" => HeightOneSpectrum (𝓞 F)

/-- Inserting a local completion into the adeles is continuous. -/
private theorem ratPVFormula_cont (v : V) :
    Continuous (AdeleRing.ofAdicCompletion (𝓞 F) F v) := by
  classical
  apply continuous_const.prodMk
  apply continuous_restrictedProduct_of_uniform
  · intro w
    exact (continuous_apply w).comp (continuous_mulSingle (A := fun u : V ↦
      u.adicCompletion F) v)
  · filter_upwards [Filter.eventually_cofinite_ne v] with w hw x
    change Pi.mulSingle v x w ∈ w.adicCompletionIntegers F
    rw [Pi.mulSingle_eq_of_ne hw]
    exact (w.adicCompletionIntegers F).one_mem

/-- The adele with `(π u)⁻¹` at `v` and `1` elsewhere, as a continuous function of the unit. -/
private theorem ratPVFormula_contU (v : V)
    (π : (v.adicCompletion F)ˣ) :
    Continuous (fun u : (v.adicCompletion F)ˣ ↦
      ((IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : IdeleGroup (𝓞 F) F) : 𝔸[F])) :=
  (ratPVFormula_cont v).comp
    (Units.continuous_val.comp ((continuous_const.mul continuous_id).inv))

/-- On an S-adele, the projection of the idele inserted at `v` has trivial infinite part and the
inserted value at `v`, for `S = {v}`. -/
private theorem ratPVFormula_proj (v : V)
    (y : (v.adicCompletion F)ˣ) (z : SAdeleRing F {v}) :
    (z * adeleProjection F {v} (IdeleGroup.ofAdicCompletion (𝓞 F) F v y : 𝔸[F])).1 = z.1 ∧
      ((z * adeleProjection F {v} (IdeleGroup.ofAdicCompletion (𝓞 F) F v y : 𝔸[F])).2
        ⟨v, Finset.mem_singleton_self v⟩ : v.adicCompletion F) =
        (z.2 ⟨v, Finset.mem_singleton_self v⟩ : v.adicCompletion F) * (y : v.adicCompletion F) := by
  classical
  constructor
  · change z.1 * 1 = z.1
    rw [mul_one]
  · change (z.2 ⟨v, Finset.mem_singleton_self v⟩ : v.adicCompletion F) *
      Pi.mulSingle v (y : v.adicCompletion F) v = _
    rw [Pi.mulSingle_eq_same]

open scoped TensorProduct in
/-- A predicate on the target of an inductive tensor product with a finite tensor product holds
everywhere once it holds on pure tensors and is closed under zero, addition and scalars. -/
private theorem ratPVFormula_ind {ι : Type*} [Fintype ι]
    {E N : Type*} {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E (FinestLocallyConvex (⨂[ℂ] i, M i)) ≃L[ℂ] N) (P : N → Prop)
    (_h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y)) (hsmul : ∀ (r : ℂ) x, P x → P (r • x))
    (hpure : ∀ (a : E) (g : ∀ i, M i), P (e (a ⊗ₜ[ℂ] (⨂ₜ[ℂ] i, g i)))) (x : N) : P x := by
  have key : ∀ y : E ⊗[ℂ] (⨂[ℂ] i, M i), P (e y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a b =>
      induction b using PiTensorProduct.induction_on with
      | smul_tprod r g =>
        exact (congrArg (fun t ↦ P (e t)) (TensorProduct.tmul_smul r a _)).mpr
          ((congrArg P (map_smul e r _)).mpr (hsmul r _ (hpure a g)))
      | add b c hb hc =>
        exact (congrArg (fun t ↦ P (e t)) (TensorProduct.tmul_add a b c)).mpr
          ((congrArg P (map_add e _ _)).mpr (hadd _ _ hb hc))
    | add y z hy hz => exact (congrArg P (map_add e y z)).mpr (hadd _ _ hy hz)
  exact (congrArg P (e.apply_symm_apply x)).mp (key (e.symm x))

/-- Paper: Definition 5.3.1.4(1) and Lemma 5.3.1.3, p. 241. For `S = {v}` the S-local principal
value is the identity minus the normalized unit average of the translates by `(π u)⁻¹` at `v`. -/
private theorem ratPVFormula_local (v : V)
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (a : SchwartzBruhat (Multiplicative (SAdeleRing F {v}))) (z : SAdeleRing F {v}) :
    sAdelePrincipalValue F (Finset.Subset.refl {v}) a (Multiplicative.ofAdd z) =
      a (Multiplicative.ofAdd z) - ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          a (Multiplicative.ofAdd (z * adeleProjection F {v}
            (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F])))
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v) := by
  classical
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  have hUc : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let T : (v.adicCompletion F)ˣ → SAdeleRing F {v} := fun u ↦
    adeleProjection F {v} (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F])
  have hT : Continuous T :=
    (continuous_fst.prodMk (continuous_pi fun w ↦
      (RestrictedProduct.continuous_eval w.val).comp continuous_snd)).comp
      (ratPVFormula_contU v π)
  have hint (b : SchwartzBruhat (Multiplicative (SAdeleRing F {v}))) (z : SAdeleRing F {v}) :
      IntegrableOn (fun u ↦ b (Multiplicative.ofAdd (z * T u))) U μ :=
    ((schwartzBruhat_continuous b).comp (continuous_ofAdd.comp
      (continuous_const.mul hT))).continuousOn.integrableOn_compact hUc
  let P : SchwartzBruhat (Multiplicative (SAdeleRing F {v})) → Prop := fun b ↦
    ∀ z : SAdeleRing F {v},
      sAdelePrincipalValue F (Finset.Subset.refl {v}) b (Multiplicative.ofAdd z) =
        b (Multiplicative.ofAdd z) - ((μ.real U)⁻¹ : ℝ) *
          ∫ u in U, b (Multiplicative.ofAdd (z * T u)) ∂μ
  have hzero : P 0 := fun z ↦ by
    rw [map_zero]
    change (0 : ℂ) = 0 - _ * ∫ u in U, (0 : ℂ) ∂μ
    simp
  have hadd (b₁ b₂ : SchwartzBruhat (Multiplicative (SAdeleRing F {v}))) (h₁ : P b₁)
      (h₂ : P b₂) : P (b₁ + b₂) := fun z ↦ by
    rw [map_add]
    change sAdelePrincipalValue F (Finset.Subset.refl {v}) b₁ (Multiplicative.ofAdd z) +
        sAdelePrincipalValue F (Finset.Subset.refl {v}) b₂ (Multiplicative.ofAdd z) =
      (b₁ (Multiplicative.ofAdd z) + b₂ (Multiplicative.ofAdd z)) - _ *
        ∫ u in U, (b₁ (Multiplicative.ofAdd (z * T u)) + b₂ (Multiplicative.ofAdd (z * T u))) ∂μ
    rw [integral_add (hint b₁ z) (hint b₂ z), h₁ z, h₂ z]
    ring
  have hsmul (r : ℂ) (b : SchwartzBruhat (Multiplicative (SAdeleRing F {v}))) (h : P b) :
      P (r • b) := fun z ↦ by
    rw [map_smul]
    change r * sAdelePrincipalValue F (Finset.Subset.refl {v}) b (Multiplicative.ofAdd z) =
      r * b (Multiplicative.ofAdd z) - _ * ∫ u in U, r * b (Multiplicative.ofAdd (z * T u)) ∂μ
    rw [integral_const_mul, h z]
    ring
  let w₀ : ({v} : Finset V) := ⟨v, Finset.mem_singleton_self v⟩
  have hw₀ (w : ({v} : Finset V)) : w = w₀ := Subtype.ext (Finset.mem_singleton.mp w.2)
  have hspec := (sAdeleSchwartz_inductiveTensor_equiv F {v}).choose_spec
  have hpure (f : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
      (g : ∀ w : ({v} : Finset V), SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
      P ((sAdeleSchwartz_inductiveTensor_equiv F {v}).choose
        (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w))) := fun z ↦ by
    have ht := sAdelePrincipalValue_tmul (F := F) (Finset.Subset.refl ({v} : Finset V)) f g
    refine (congrArg (fun b : SchwartzBruhat (Multiplicative (SAdeleRing F {v})) ↦
      b (Multiplicative.ofAdd z)) ht).trans ?_
    have hprod (x : SAdeleRing F {v}) (h : ∀ w : ({v} : Finset V),
        SchwartzBruhat (Multiplicative (w.val.adicCompletion F))) :
        ∏ w : ({v} : Finset V), h w (Multiplicative.ofAdd (x.2 w)) =
          h w₀ (Multiplicative.ofAdd (x.2 w₀)) :=
      Fintype.prod_eq_single w₀ fun w hw ↦ absurd (hw₀ w) hw
    have e1 := hspec f (fun w ↦ if w.val ∈ ({v} : Finset V) then
      finitePlacePrincipalValue w.val (g w) else g w) z
    have e2 := hspec f g z
    have e3 : ∫ u in U, (sAdeleSchwartz_inductiveTensor_equiv F {v}).choose
        (f ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, g w)) (Multiplicative.ofAdd (z * T u)) ∂μ =
        ∫ u in U, f (Multiplicative.ofAdd (z * T u).1) *
          ∏ w : ({v} : Finset V), g w (Multiplicative.ofAdd ((z * T u).2 w)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun u ↦ hspec f g (z * T u))
    refine e1.trans (Eq.trans ?_ (congrArg₂ (fun x y : ℂ ↦ x - (((μ.real U)⁻¹ : ℝ) : ℂ) * y)
      e2 e3).symm)
    dsimp only
    rw [hprod, hprod]
    have hin (u : (v.adicCompletion F)ˣ) : f (Multiplicative.ofAdd (z * T u).1) *
        ∏ w : ({v} : Finset V), g w (Multiplicative.ofAdd ((z * T u).2 w)) =
        f (Multiplicative.ofAdd z.1) * g w₀ (Multiplicative.ofAdd
          ((z.2 w₀ : v.adicCompletion F) *
            (((π * u)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F))) := by
      obtain ⟨h1, h2⟩ := ratPVFormula_proj v ((π * u)⁻¹) z
      rw [hprod]
      exact congrArg₂ (· * ·) (congrArg (fun x ↦ f (Multiplicative.ofAdd x)) h1)
        (congrArg (fun x ↦ g w₀ (Multiplicative.ofAdd x)) h2)
    have hpv := finitePlacePrincipalValue_spec v π hπ (g w₀) (Multiplicative.ofAdd (z.2 w₀))
    unfold finitePlacePrincipalValueFun at hpv
    have hu (u : (v.adicCompletion F)ˣ) :
        (z.2 w₀ : v.adicCompletion F) * (((π * u)⁻¹ : (v.adicCompletion F)ˣ) : v.adicCompletion F) =
          (↑u⁻¹ : v.adicCompletion F) * ((↑π⁻¹ : v.adicCompletion F) *
            (Multiplicative.ofAdd (z.2 w₀ : v.adicCompletion F)).toAdd) := by
      rw [mul_inv_rev, Units.val_mul]
      change _ = _ * (_ * (z.2 w₀ : v.adicCompletion F))
      ring
    show f (Multiplicative.ofAdd z.1) *
        (if (w₀ : V) ∈ ({v} : Finset V) then finitePlacePrincipalValue (w₀ : V) (g w₀) else g w₀)
          (Multiplicative.ofAdd (z.2 w₀)) =
      f (Multiplicative.ofAdd z.1) * g w₀ (Multiplicative.ofAdd (z.2 w₀)) -
        (((μ.real U)⁻¹ : ℝ) : ℂ) * ∫ u in U, f (Multiplicative.ofAdd (z * T u).1) *
          ∏ w : ({v} : Finset V), g w (Multiplicative.ofAdd ((z * T u).2 w)) ∂μ
    rw [ite_eq_left_of_eq_true _ _ (eq_true (Finset.mem_singleton_self v)),
      integral_congr_ae (Filter.Eventually.of_forall hin), integral_const_mul]
    change f (Multiplicative.ofAdd z.1) *
        finitePlacePrincipalValue v (g w₀) (Multiplicative.ofAdd (z.2 w₀)) = _
    rw [hpv]
    simp only [hu, Complex.ofReal_inv]
    ring
  exact ratPVFormula_ind
    (sAdeleSchwartz_inductiveTensor_equiv F {v}).choose P hzero hadd hsmul hpure a z

/-- A predicate on the target of an inductive tensor product of two factors holds everywhere
once it holds on pure tensors and is closed under zero, addition and scalars. -/
private theorem ratPVFormula_ind₂ {E G N : Type*}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [AddCommGroup G] [Module ℂ G] [TopologicalSpace G]
    [AddCommGroup N] [Module ℂ N] [TopologicalSpace N]
    (e : InductiveTensor E G ≃L[ℂ] N) (P : N → Prop)
    (_h0 : P 0) (hadd : ∀ x y, P x → P y → P (x + y))
    (hpure : ∀ (a : E) (b : G), P (e (a ⊗ₜ[ℂ] b))) (x : N) : P x := by
  have key : ∀ y : TensorProduct ℂ E G, P (e y) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul a b => exact hpure a b
    | add y z hy hz => exact (congrArg P (map_add e y z)).mpr (hadd _ _ hy hz)
  exact (congrArg P (e.apply_symm_apply x)).mp (key (e.symm x))

/-- Multiplying an adele by the idele inserted at `v` does not change its coordinates off `{v}`. -/
private theorem ratPVFormula_tail (v : V)
    (y : (v.adicCompletion F)ˣ) (x : 𝔸[F]) :
    finiteAdeleTailProjection F {v}
        (x * (IdeleGroup.ofAdicCompletion (𝓞 F) F v y : 𝔸[F])).2 =
      finiteAdeleTailProjection F {v} x.2 := by
  classical
  apply RestrictedProduct.ext
  intro w
  rw [finiteAdeleTailProjection_apply, finiteAdeleTailProjection_apply]
  have hw : (w.val : V) ≠ v := fun h ↦ w.2 (by rw [h]; exact Finset.mem_singleton_self v)
  change x.2 w.val * Pi.mulSingle v (y : v.adicCompletion F) w.val = x.2 w.val
  rw [Pi.mulSingle_eq_of_ne hw, mul_one]

/-- Paper: Definition 5.3.1.4(2) and Lemma 5.3.1.3, p. 241. On adelic tests, the principal value
at the single place `v` is the identity minus the normalized unit average of the translates by
the idele `(π u)⁻¹` at `v`. -/
private theorem ratPVFormula_global (v : V)
    (π : (v.adicCompletion F)ˣ) (hπ : Valued.v.IsUniformizer π.val)
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) (x : 𝔸[F]) :
    adelePrincipalValue F {v} f (Multiplicative.ofAdd x) =
      f (Multiplicative.ofAdd x) - ((finiteLocalMultiplicativeTamagawaMeasure F v).real
          ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ))⁻¹ *
        ∫ u in ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ),
          f (Multiplicative.ofAdd (x * (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F])))
          ∂(finiteLocalMultiplicativeTamagawaMeasure F v) := by
  classical
  let : MeasurableSpace (v.adicCompletion F)ˣ := borel _
  have : BorelSpace (v.adicCompletion F)ˣ := ⟨rfl⟩
  have := finiteLocalMultiplicativeTamagawaMeasure_isHaarMeasure (F := F) v
  let μ := finiteLocalMultiplicativeTamagawaMeasure F v
  let U : Set (v.adicCompletion F)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set (v.adicCompletion F)ˣ)
  have hUc : IsCompact U := Submonoid.units_isCompact
    (isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v))
  let E : (v.adicCompletion F)ˣ → 𝔸[F] := fun u ↦
    (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F])
  have hE : Continuous E := ratPVFormula_contU v π
  have hint (b : SchwartzBruhat (Multiplicative 𝔸[F])) (x : 𝔸[F]) :
      IntegrableOn (fun u ↦ b (Multiplicative.ofAdd (x * E u))) U μ :=
    ((schwartzBruhat_continuous b).comp (continuous_ofAdd.comp
      (continuous_const.mul hE))).continuousOn.integrableOn_compact hUc
  let P : SchwartzBruhat (Multiplicative 𝔸[F]) → Prop := fun b ↦ ∀ x : 𝔸[F],
    adelePrincipalValue F {v} b (Multiplicative.ofAdd x) =
      b (Multiplicative.ofAdd x) - ((μ.real U)⁻¹ : ℝ) *
        ∫ u in U, b (Multiplicative.ofAdd (x * E u)) ∂μ
  have hzero : P 0 := fun x ↦ by
    rw [map_zero]
    change (0 : ℂ) = 0 - _ * ∫ u in U, (0 : ℂ) ∂μ
    simp
  have hadd (b₁ b₂ : SchwartzBruhat (Multiplicative 𝔸[F])) (h₁ : P b₁) (h₂ : P b₂) :
      P (b₁ + b₂) := fun x ↦ by
    rw [map_add]
    change adelePrincipalValue F {v} b₁ (Multiplicative.ofAdd x) +
        adelePrincipalValue F {v} b₂ (Multiplicative.ofAdd x) =
      (b₁ (Multiplicative.ofAdd x) + b₂ (Multiplicative.ofAdd x)) - _ *
        ∫ u in U, (b₁ (Multiplicative.ofAdd (x * E u)) + b₂ (Multiplicative.ofAdd (x * E u))) ∂μ
    rw [integral_add (hint b₁ x) (hint b₂ x), h₁ x, h₂ x]
    ring
  have hspec := (sAdeleTailSchwartz_inductiveTensor_equiv F {v}).choose_spec
  have hpure (a : SchwartzBruhat (Multiplicative (SAdeleRing F {v})))
      (b : SchwartzBruhat (Multiplicative (FiniteAdeleTail F {v}))) :
      P ((sAdeleTailSchwartz_inductiveTensor_equiv F {v}).choose (a ⊗ₜ[ℂ] b)) := fun x ↦ by
    have ht := adelePrincipalValue_tmul (F := F) (Finset.Subset.refl ({v} : Finset V)) a b
    refine (congrArg (fun c : SchwartzBruhat (Multiplicative 𝔸[F]) ↦
      c (Multiplicative.ofAdd x)) ht).trans ?_
    have e1 := hspec (sAdelePrincipalValue F (Finset.Subset.refl ({v} : Finset V)) a) b x
    have e2 := hspec a b x
    have e3 : ∫ u in U, (sAdeleTailSchwartz_inductiveTensor_equiv F {v}).choose (a ⊗ₜ[ℂ] b)
        (Multiplicative.ofAdd (x * E u)) ∂μ =
        ∫ u in U, a (Multiplicative.ofAdd (adeleProjection F {v} (x * E u))) *
          b (Multiplicative.ofAdd (finiteAdeleTailProjection F {v} (x * E u).2)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall fun u ↦ hspec a b (x * E u))
    refine e1.trans (Eq.trans ?_ (congrArg₂ (fun y z : ℂ ↦ y - (((μ.real U)⁻¹ : ℝ) : ℂ) * z)
      e2 e3).symm)
    dsimp only
    have hin (u : (v.adicCompletion F)ˣ) :
        a (Multiplicative.ofAdd (adeleProjection F {v} (x * E u))) *
          b (Multiplicative.ofAdd (finiteAdeleTailProjection F {v} (x * E u).2)) =
        b (Multiplicative.ofAdd (finiteAdeleTailProjection F {v} x.2)) *
          a (Multiplicative.ofAdd (adeleProjection F {v} x * adeleProjection F {v}
            (IdeleGroup.ofAdicCompletion (𝓞 F) F v (π * u)⁻¹ : 𝔸[F]))) := by
      rw [ratPVFormula_tail v ((π * u)⁻¹) x, map_mul, mul_comm]
    rw [integral_congr_ae (Filter.Eventually.of_forall hin), integral_const_mul,
      ratPVFormula_local v π hπ a (adeleProjection F {v} x)]
    ring
  exact ratPVFormula_ind₂
    (sAdeleTailSchwartz_inductiveTensor_equiv F {v}).choose P hzero hadd hpure f x

end PVFormula

/-! ### Rational places: the uniformizer `p` and local unit invariance -/

section Rat

open NumberFieldKB.Chebotarev.RatIdele

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Bℚ" => SchwartzBruhat (Multiplicative 𝔸)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "ι" => IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ

private theorem valued_pr (v : Vℚ) :
    Valued.v (pr v : v.adicCompletion ℚ) = WithZero.exp (-1) := by
  simpa only [Rat.cast_natCast, eq_self, ↓reduceIte] using valued_prime v (pr_prime v)

/-- The rational prime `p_v` is a uniformizer of `ℚ_v`. -/
theorem ratPrime_isUniformizer (v : Vℚ) : Valued.v.IsUniformizer (pr v : v.adicCompletion ℚ) := by
  rw [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_mem_range ⟨_, valued_pr v⟩]
  exact valued_pr v

/-- The rational prime `p_v` as a unit of `ℚ_v`. -/
def ratPrimeUnit (v : Vℚ) : (v.adicCompletion ℚ)ˣ :=
  Units.mk0 _ (ratPrime_isUniformizer v).ne_zero

@[simp]
theorem ratPrimeUnit_val (v : Vℚ) : (ratPrimeUnit v : v.adicCompletion ℚ) = pr v := rfl

/-- A test on the rational adeles is invariant under the local integer units at `v`. -/
def IsLocalUnitInvariant (v : Vℚ) (φ : Bℚ) : Prop :=
  ∀ u : (v.adicCompletion ℚ)ˣ, u ∈ (HeightOneSpectrum.adicCompletionIntegers ℚ v).units →
    ∀ x : 𝔸, φ (Multiplicative.ofAdd (x * (ι v u : 𝔸))) = φ (Multiplicative.ofAdd x)

/-- Translation by any idele preserves local unit invariance. -/
theorem IsLocalUnitInvariant.translate {v : Vℚ} {φ : Bℚ} (h : IsLocalUnitInvariant v φ)
    (a : IdQ) : IsLocalUnitInvariant v (schwartzBruhatUnitTranslate a φ) := by
  intro u hu x
  rw [schwartzBruhatUnitTranslate_apply, schwartzBruhatUnitTranslate_apply, ← mul_assoc]
  exact h u hu _

/-- Paper: Definition 5.3.1.2 and Lemma 5.3.1.3, p. 241.
On a test invariant under the local units at `v`, Weil's principal value at `v` is the test
minus its translate by the idele `π` at `v`, for every uniformizer `π` of `ℚ_v`. In particular
the result does not depend on the uniformizer. Through the tensor identification, at the factor
`1_{ℤ_p}` this is `1_{ℤ_p} - 1_{pℤ_p}`. -/
theorem ratPV_singleton_of_invariant (v : Vℚ) (π : (v.adicCompletion ℚ)ˣ)
    (hπ : Valued.v.IsUniformizer π.val) (φ : Bℚ) (hφ : IsLocalUnitInvariant v φ) :
    adelePrincipalValue ℚ {v} φ = φ - schwartzBruhatUnitTranslate (ι v π) φ := by
  classical
  let : MeasurableSpace (v.adicCompletion ℚ)ˣ := borel _
  have : BorelSpace (v.adicCompletion ℚ)ˣ := ⟨rfl⟩
  let μ := finiteLocalMultiplicativeTamagawaMeasure ℚ v
  let U : Set (v.adicCompletion ℚ)ˣ :=
    ((HeightOneSpectrum.adicCompletionIntegers ℚ v).units : Set (v.adicCompletion ℚ)ˣ)
  have hU : MeasurableSet U :=
    (Submonoid.isOpen_units (Valued.isOpen_valuationSubring _)).measurableSet
  have hm : μ.real U ≠ 0 :=
    (finitePlacePrincipalValue_integrable (F := ℚ) v π 0 1).1.ne'
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : 𝔸, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [ratPVFormula_global v π hπ φ x]
  change _ = φ (Multiplicative.ofAdd x) -
    schwartzBruhatUnitTranslate (ι v π) φ (Multiplicative.ofAdd x)
  rw [schwartzBruhatUnitTranslate_apply]
  have hc : ∀ u ∈ U, φ (Multiplicative.ofAdd (x * (ι v (π * u)⁻¹ : 𝔸))) =
      φ (Multiplicative.ofAdd ((↑(ι v π)⁻¹ : 𝔸) * x)) := by
    intro u hu
    have hu' : u⁻¹ ∈ (HeightOneSpectrum.adicCompletionIntegers ℚ v).units := inv_mem hu
    rw [← hφ u⁻¹ hu' ((↑(ι v π)⁻¹ : 𝔸) * x)]
    have e : x * (ι v (π * u)⁻¹ : 𝔸) = (↑(ι v π)⁻¹ : 𝔸) * x * (ι v u⁻¹ : 𝔸) := by
      rw [mul_inv_rev, map_mul (ι v), Units.val_mul, ← map_inv (ι v)]
      ring
    rw [e]
  change _ - (((μ.real U)⁻¹ : ℝ) : ℂ) * ∫ u in U, _ ∂μ = _
  rw [setIntegral_congr_fun hU hc, setIntegral_const, Complex.real_smul, ← mul_assoc,
    ← Complex.ofReal_mul, inv_mul_cancel₀ hm, Complex.ofReal_one, one_mul]

open Classical in
/-- Paper: Definition 5.3.1.4(2), p. 242. Adding a place: the principal value at `insert v T`
is the one at `T` after the one at `v`. -/
theorem ratPV_insert {v : Vℚ} {T : Finset Vℚ} (hv : v ∉ T) :
    adelePrincipalValue ℚ (insert v T) =
      (adelePrincipalValue ℚ T).comp (adelePrincipalValue ℚ {v}) := by
  rw [sLocalCutoffCarving_antitone_PV (Finset.subset_insert v T), Finset.insert_sdiff_cancel hv]

private theorem translate_translate (a b : IdQ) (φ : Bℚ) :
    schwartzBruhatUnitTranslate a (schwartzBruhatUnitTranslate b φ) =
      schwartzBruhatUnitTranslate (a * b) φ := by
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : 𝔸, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [schwartzBruhatUnitTranslate_apply, schwartzBruhatUnitTranslate_apply,
    schwartzBruhatUnitTranslate_apply, mul_inv_rev, Units.val_mul, ← mul_assoc, mul_comm
      (↑b⁻¹ : 𝔸)]

private theorem translate_one (φ : Bℚ) : schwartzBruhatUnitTranslate (1 : IdQ) φ = φ := by
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : 𝔸, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  simp only [schwartzBruhatUnitTranslate_apply, inv_one, Units.val_one, one_mul]

open Classical in
/-- The idele `∏_{v ∈ A} p_v`, with `p_v` at the place `v` and `1` elsewhere. -/
def ratPrimeIdele (A : Finset Vℚ) : IdQ :=
  ∏ v ∈ A, ι v (ratPrimeUnit v)

/-- Paper: Definition 5.3.1.4, p. 242, and Lemma 5.3.1.3, p. 241.
**Pointwise formula, translate form.** On a test invariant under the local units at every place
of `T`, the principal value at `T` is the inclusion–exclusion sum of its translates by the
ideles `∏_{v ∈ A} p_v`, `A ⊆ T`. -/
theorem ratPV_eq_sum_translate (T : Finset Vℚ) (φ : Bℚ)
    (hφ : ∀ v ∈ T, IsLocalUnitInvariant v φ) :
    adelePrincipalValue ℚ T φ =
      ∑ A ∈ T.powerset, ((-1 : ℂ) ^ A.card) • schwartzBruhatUnitTranslate (ratPrimeIdele A) φ := by
  classical
  induction T using Finset.induction_on generalizing φ with
  | empty =>
    rw [sLocalUncutCarving_empty_PV, Finset.powerset_empty, Finset.sum_singleton,
      Finset.card_empty, pow_zero, one_smul, ratPrimeIdele, Finset.prod_empty, translate_one]
    rfl
  | insert v T hv ih =>
    have hφT : ∀ w ∈ T, IsLocalUnitInvariant w φ := fun w hw ↦ hφ w (Finset.mem_insert_of_mem hw)
    rw [ratPV_insert hv, LinearMap.comp_apply,
      ratPV_singleton_of_invariant v (ratPrimeUnit v) (ratPrime_isUniformizer v) φ
        (hφ v (Finset.mem_insert_self v T)), map_sub, ih φ hφT,
      ih _ fun w hw ↦ (hφT w hw).translate _, Finset.sum_powerset_insert hv, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun A hA ↦ ?_
    have hvA : v ∉ A := fun h ↦ hv (Finset.mem_powerset.mp hA h)
    rw [translate_translate, Finset.card_insert_of_notMem hvA]
    simp only [ratPrimeIdele]
    rw [Finset.prod_insert hvA, mul_comm (ι v (ratPrimeUnit v)), pow_succ, mul_neg_one, neg_smul]


/-! ### Theta of translates, the character at `p`, and the norm of `p` -/

private theorem adelicTheta_translate (a : IdQ) (φ : Bℚ) (c : Cℚ) :
    adelicTheta (schwartzBruhatUnitTranslate a φ) c =
      adelicTheta φ (QuotientGroup.mk a⁻¹ * c) := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
  rw [← QuotientGroup.mk_mul, adelicTheta_mk, adelicTheta_mk]
  refine tsum_congr fun ξ ↦ ?_
  rw [schwartzBruhatUnitTranslate_apply, Units.val_mul, mul_left_comm]

/-- Paper: Definition 2.2.5.1, p. 95. The homogeneous theta of the translate of a test by an
idele `a` is the homogeneous theta of the test at the class translated by `a⁻¹`. -/
theorem ratBridge_homogeneousTheta_translate (ω₁ : PontryaginDual (ideleClassNorm ℚ).ker)
    (a : IdQ) (φ : Bℚ) (g : Cℚ) :
    homogeneousAdelicTheta ω₁ (schwartzBruhatUnitTranslate a φ) g =
      homogeneousAdelicTheta ω₁ φ (QuotientGroup.mk a⁻¹ * g) := by
  simp only [homogeneousAdelicTheta, ContinuousMap.coe_mk]
  refine integral_congr_ae (.of_forall fun h ↦ ?_)
  dsimp only
  rw [adelicTheta_translate, mul_left_comm (QuotientGroup.mk a⁻¹ : Cℚ)]

private theorem homTheta_sub (ω₁ : PontryaginDual (ideleClassNorm ℚ).ker) (f g : Bℚ) (y : Cℚ) :
    homogeneousAdelicTheta ω₁ (f - g) y =
      homogeneousAdelicTheta ω₁ f y - homogeneousAdelicTheta ω₁ g y :=
  congrArg (fun F : C(Cℚ, ℂ) ↦ F y) (((homogeneousAdelicTheta_isLinear ω₁).mk' _).map_sub f g)

/-- The prime `p_v` as a positive unit of `ℝ≥0`. -/
def ratPrimeNN (v : Vℚ) : ℝ≥0ˣ :=
  Units.mk0 (pr v : ℝ≥0) (by exact_mod_cast (pr_prime v).ne_zero)

theorem ratPrimeNN_coe (v : Vℚ) : (((ratPrimeNN v : ℝ≥0ˣ) : ℝ≥0) : ℝ) = pr v := rfl

/-- The idele class of `p_v` at `v` has norm `p_v⁻¹`. -/
theorem ideleClassNorm_ratPrimeUnit (v : Vℚ) :
    ideleClassNorm ℚ (QuotientGroup.mk (ι v (ratPrimeUnit v))) = (ratPrimeNN v)⁻¹ := by
  have h := ideleClassNorm_ofAdicCompletion (F := ℚ) v (ratPrimeUnit v)
  refine h.trans (Units.ext (NNReal.coe_injective ?_))
  change ‖(pr v : v.adicCompletion ℚ)‖ = ((pr v : ℝ≥0)⁻¹ : ℝ≥0)
  rw [norm_uniformizer_adicCompletion v _ (ratPrime_isUniformizer v), absNorm_asIdeal]
  simp

/-- `eˣ` as a positive unit of `ℝ≥0`. -/
def ratExpUnit (x : ℝ) : ℝ≥0ˣ :=
  Units.mk0 ⟨Real.exp x, (Real.exp_pos x).le⟩
    fun h ↦ (Real.exp_pos x).ne' (congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) h)

theorem ratExpUnit_coe (x : ℝ) : (((ratExpUnit x : ℝ≥0ˣ) : ℝ≥0) : ℝ) = Real.exp x := rfl

private theorem halfTwist_shift (q : ℕ) (hq : 0 < q) (Θ : ℝ → ℂ) (y : ℝ) :
    (Real.exp (y / 2) : ℂ) * Θ ((q : ℝ) * Real.exp y) =
      halfTwistLogDilate q (fun z ↦ (Real.exp (z / 2) : ℂ) * Θ (Real.exp z)) y := by
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  simp only [halfTwistLogDilate, LinearMap.coe_mk, AddHom.coe_mk, hq.ne', ↓reduceIte]
  rw [show Real.exp (y + Real.log q) = q * Real.exp y by
    rw [Real.exp_add, Real.exp_log hqr, mul_comm], ← mul_assoc]
  congr 1
  have h1 : (q : ℂ) ^ (-(1 / 2 : ℂ)) = (((q : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hqr.le]
    push_cast
    rfl
  rw [h1, ← Complex.ofReal_mul, Real.rpow_def_of_pos hqr, ← Real.exp_add]
  congr 2
  ring

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

private theorem ratDirichletIdeleChar_section' (hχ : χ.IsPrimitive) (t : ℝ≥0ˣ) :
    ratDirichletIdeleChar hχ (ratNormSection t) = 1 := by
  obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp
    (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hχ).choose_spec.1
  let r := (t : ℝ≥0) ^ ((k : ℝ)⁻¹)
  let u : ℝ≥0ˣ := Units.mk0 r (NNReal.rpow_pos (Units.zero_lt t)).ne'
  have hu : u ^ k = t := Units.ext (NNReal.rpow_inv_natCast_pow _ hk.ne')
  rw [← hu, map_pow, map_pow]
  exact (ContinuousMonoidHom.pow_apply (ratDirichletIdeleChar hχ : Cℚ →ₜ* Circle) k
    (ratNormSection u)).symm.trans
    (congrArg (fun η : PontryaginDual Cℚ ↦ η (ratNormSection u)) hpow)

/-- The character `ψ` takes the value `χ(p)` on the idele class of `p` at a place `p ∤ N`. -/
theorem ratDirichletIdeleChar_ratPrimeUnit (hχ : χ.IsPrimitive) (v : Vℚ) (hv : (pr v).Coprime N) :
    (ratDirichletIdeleChar hχ (QuotientGroup.mk (ι v (ratPrimeUnit v))) : ℂ) = χ (pr v) :=
  (ratDirichletIdeleChar_mk hχ _).trans (ideleChar_uniformizer N χ hv _ (valued_pr v))

/-- The theta profile of the translate of a test by `p` at `v ∤ N`: if the homogeneous theta of
`φ` at `k · τ(t)` is `ω(k)⁻¹ · M · Θ(t)`, that of the translate is `ω(k)⁻¹ · M · χ(p) Θ(p t)`. -/
private theorem theta_translate_profile (hχ : χ.IsPrimitive) (v : Vℚ) (hv : (pr v).Coprime N)
    (φ : Bℚ) (M : ℂ) (Θ : ℝ → ℂ)
    (hΘ : ∀ (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker),
      homogeneousAdelicTheta (ratDirichletNormOneChar hχ) φ (k.val * ratNormSection t) =
        (ratDirichletNormOneChar hχ k : ℂ)⁻¹ * M * Θ ((t : ℝ≥0) : ℝ))
    (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker) :
    homogeneousAdelicTheta (ratDirichletNormOneChar hχ)
        (schwartzBruhatUnitTranslate (ι v (ratPrimeUnit v)) φ) (k.val * ratNormSection t) =
      (ratDirichletNormOneChar hχ k : ℂ)⁻¹ * M *
        (χ (pr v) * Θ ((pr v : ℝ) * ((t : ℝ≥0) : ℝ))) := by
  rw [ratBridge_homogeneousTheta_translate]
  set a : Cℚ := QuotientGroup.mk (ι v (ratPrimeUnit v)) with ha
  have hk' : a⁻¹ * k.val * (ratNormSection (ratPrimeNN v))⁻¹ ∈ (ideleClassNorm ℚ).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, ha, ideleClassNorm_ratPrimeUnit,
      ideleClassNorm_ratNormSection, show ideleClassNorm ℚ k.val = 1 from k.property, inv_inv,
      mul_one, mul_inv_cancel]
  let k' : (ideleClassNorm ℚ).ker := ⟨_, hk'⟩
  have heq : QuotientGroup.mk (ι v (ratPrimeUnit v))⁻¹ * (k.val * ratNormSection t) =
      k'.val * ratNormSection (ratPrimeNN v * t) := by
    rw [map_mul ratNormSection, QuotientGroup.mk_inv]
    change a⁻¹ * (k.val * ratNormSection t) =
      a⁻¹ * k.val * (ratNormSection (ratPrimeNN v))⁻¹ *
        (ratNormSection (ratPrimeNN v) * ratNormSection t)
    group
  have hω : ratDirichletNormOneChar hχ k' = (ratDirichletIdeleChar hχ a)⁻¹ *
      ratDirichletNormOneChar hχ k := by
    rw [ratDirichletNormOneChar_apply, ratDirichletNormOneChar_apply]
    change ratDirichletIdeleChar hχ (a⁻¹ * k.val * (ratNormSection (ratPrimeNN v))⁻¹) = _
    rw [map_mul, map_mul, map_inv, map_inv, ratDirichletIdeleChar_section', inv_one, mul_one]
  rw [heq, hΘ, hω, Circle.coe_mul, Circle.coe_inv, mul_inv, inv_inv, ha,
    ratDirichletIdeleChar_ratPrimeUnit hχ v hv, Units.val_mul, NNReal.coe_mul, ratPrimeNN_coe]
  ring

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ

/-- Paper: Proposition 11.2.0.1, pp. 484–485, Definition 5.3.1.4, p. 242, and (11.3.1.3),
p. 494, over `ℚ`.
**Principal value against depletion, general form.** Let `T` be a finite set of places `p ∤ N`
and `φ` a test invariant under the local units at every place of `T` (with arbitrary factors at
the other places, in particular at `q ∣ N`). If the homogeneous theta of `φ` for `ω = ψ|_{C₁}`
at `k · τ(t)` is `ω(k)⁻¹ · M · Θ(t)`, then that of `PV_T φ` at `k · τ(eˣ)` is
`ω(k)⁻¹ · M · e^{-x/2} · (∏_{p ∈ T} (I - χ(p) D_p)) U (x)`, with `U(y) = e^{y/2} Θ(e^y)` the
half-logarithmic profile and `dirichletDeplete` of `Sec3_DirichletFixedBox_Isolated`. -/
theorem ratBridge_principalValue_general (hχ : χ.IsPrimitive) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) (φ : Bℚ) (hφ : ∀ v ∈ T, IsLocalUnitInvariant v φ)
    (M : ℂ) (Θ : ℝ → ℂ)
    (hΘ : ∀ (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker),
      homogeneousAdelicTheta ω φ (k.val * ratNormSection t) =
        (ω k : ℂ)⁻¹ * M * Θ ((t : ℝ≥0) : ℝ))
    (k : (ideleClassNorm ℚ).ker) (x : ℝ) :
    homogeneousAdelicTheta ω (adelePrincipalValue ℚ T φ) (k.val * ratNormSection (ratExpUnit x)) =
      (ω k : ℂ)⁻¹ * M * ((Real.exp (-(x / 2)) : ℂ) *
        dirichletDeplete χ (T.image pr) (fun y ↦ (Real.exp (y / 2) : ℂ) * Θ (Real.exp y)) x) := by
  classical
  induction T using Finset.induction_on generalizing φ Θ x with
  | empty =>
    rw [sLocalUncutCarving_empty_PV, Finset.image_empty, dirichletDeplete_empty]
    change homogeneousAdelicTheta _ φ _ = _
    rw [hΘ, ratExpUnit_coe, LinearMap.id_apply, ← mul_assoc (Real.exp (-(x / 2)) : ℂ),
      ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Complex.ofReal_one,
      one_mul]
  | insert v T hv ih =>
    have hTv := hT v (Finset.mem_insert_self v T)
    have hT' : ∀ w ∈ T, (pr w).Coprime N := fun w hw ↦ hT w (Finset.mem_insert_of_mem hw)
    have hφT : ∀ w ∈ T, IsLocalUnitInvariant w φ := fun w hw ↦ hφ w (Finset.mem_insert_of_mem hw)
    have hpv : pr v ∉ T.image pr := fun h ↦ by
      obtain ⟨w, hw, hwv⟩ := Finset.mem_image.mp h
      exact hv (pr_injective hwv ▸ hw)
    have hp0 : 0 < pr v := (pr_prime v).pos
    let U : ℝ → ℂ := fun y ↦ (Real.exp (y / 2) : ℂ) * Θ (Real.exp y)
    let D := dirichletDeplete χ (T.image pr)
    have hshift : (fun y ↦ (Real.exp (y / 2) : ℂ) *
        (χ (pr v) * Θ ((pr v : ℝ) * Real.exp y))) = χ (pr v) • halfTwistLogDilate (pr v) U := by
      funext y
      rw [Pi.smul_apply, smul_eq_mul, ← halfTwist_shift (pr v) hp0 Θ y]
      ring
    have hc : Commute (depleteStepFun χ (pr v)) D :=
      Finset.noncommProd_commute _ _ _ _ fun q _ ↦ depleteStepFun_comm χ _ q
    have hstep : depleteStepFun χ (pr v) (D U) =
        D U - D (χ (pr v) • halfTwistLogDilate (pr v) U) := by
      rw [← mul_apply_eq_comp, hc.eq, mul_apply_eq_comp, depleteStepFun, LinearMap.sub_apply,
        LinearMap.id_apply, LinearMap.smul_apply, map_sub]
    rw [ratPV_insert hv, LinearMap.comp_apply,
      ratPV_singleton_of_invariant v (ratPrimeUnit v) (ratPrime_isUniformizer v) φ
        (hφ v (Finset.mem_insert_self v T)), map_sub, homTheta_sub, ih hT' φ hφT Θ hΘ x,
      ih hT' _ (fun w hw ↦ (hφT w hw).translate _) (fun r ↦ χ (pr v) * Θ ((pr v : ℝ) * r))
        (theta_translate_profile hχ v hTv φ M Θ hΘ) x, hshift, Finset.image_insert,
      dirichletDeplete_insert χ hpv, LinearMap.comp_apply]
    change _ = _ * (_ * depleteStepFun χ (pr v) (D U) x)
    rw [hstep, Pi.sub_apply]
    ring

/-- Paper: Proposition 11.2.0.1, pp. 484–485, over `ℚ`.
**Principal value against depletion, in terms of theta.** For every test `φ` invariant under the
local units at the places of `T` (all `p ∤ N`), the homogeneous theta of `PV_T φ` at `k · τ(eˣ)`
is `ω(k)⁻¹ e^{-x/2}` times the depletion of the half-logarithmic profile
`y ↦ e^{y/2} Θ_ω(φ)(τ(e^y))` of the homogeneous theta of `φ` itself. No polarity is needed. -/
theorem ratBridge_principalValue_theta (hχ : χ.IsPrimitive) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) (φ : Bℚ) (hφ : ∀ v ∈ T, IsLocalUnitInvariant v φ)
    (k : (ideleClassNorm ℚ).ker) (x : ℝ) :
    homogeneousAdelicTheta ω (adelePrincipalValue ℚ T φ) (k.val * ratNormSection (ratExpUnit x)) =
      (ω k : ℂ)⁻¹ * ((Real.exp (-(x / 2)) : ℂ) * dirichletDeplete χ (T.image pr)
        (fun y ↦ (Real.exp (y / 2) : ℂ) *
          homogeneousAdelicTheta ω φ (ratNormSection (ratExpUnit y)))
        x) := by
  classical
  let pos : ℝ → ℝ≥0ˣ := fun r ↦
    if h : 0 < r then Units.mk0 ⟨r, h.le⟩ (fun h' ↦ h.ne' (congrArg (fun r : ℝ≥0 ↦ (r : ℝ)) h'))
    else 1
  have hpos (t : ℝ≥0ˣ) : pos ((t : ℝ≥0) : ℝ) = t := by
    have h : (0 : ℝ) < ((t : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt t)
    simp only [pos, h, ↓reduceDIte]
    exact Units.ext rfl
  have hΘ (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker) :
      homogeneousAdelicTheta ω φ (k.val * ratNormSection t) =
        (ω k : ℂ)⁻¹ * 1 * homogeneousAdelicTheta ω φ (ratNormSection (pos ((t : ℝ≥0) : ℝ))) := by
    have hk : k.val * ratNormSection t = (k⁻¹).val⁻¹ * ratNormSection t := by
      rw [Subgroup.coe_inv, inv_inv]
    rw [hk, homogeneousAdelicTheta_homogeneous, hpos, map_inv, Circle.coe_inv, mul_one]
  have hfun : (fun y ↦ (Real.exp (y / 2) : ℂ) *
      homogeneousAdelicTheta ω φ (ratNormSection (pos (Real.exp y)))) =
      fun y ↦ (Real.exp (y / 2) : ℂ) * homogeneousAdelicTheta ω φ (ratNormSection (ratExpUnit y)) :=
    funext fun y ↦ by rw [← ratExpUnit_coe y, hpos]
  rw [ratBridge_principalValue_general hχ T hT φ hφ 1
    (fun r ↦ homogeneousAdelicTheta ω φ (ratNormSection (pos r))) hΘ k x, hfun, mul_one]


/-! ### The Dirichlet test -/

local notation "Sχ" => ratDirichletS N
local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)
local notation "realCoord" =>
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace

private theorem mul_ofAdic_fst (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ) (x : 𝔸) :
    (x * (ι v u : 𝔸)).1 = x.1 :=
  mul_one x.1

private theorem mul_ofAdic_snd_self (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ) (x : 𝔸) :
    (x * (ι v u : 𝔸)).2 v = x.2 v * u := by
  classical
  change x.2 v * Pi.mulSingle v (u : v.adicCompletion ℚ) v = _
  rw [Pi.mulSingle_eq_same]

private theorem mul_ofAdic_snd_ne {v w : Vℚ} (hw : w ≠ v) (u : (v.adicCompletion ℚ)ˣ) (x : 𝔸) :
    (x * (ι v u : 𝔸)).2 w = x.2 w := by
  classical
  change x.2 w * Pi.mulSingle v (u : v.adicCompletion ℚ) w = _
  rw [Pi.mulSingle_eq_of_ne hw, mul_one]

/-- A place over a prime coprime to the conductor is not one of the places of `ratDirichletS`. -/
theorem notMem_ratDirichletS_of_coprime {v : Vℚ} (hv : (pr v).Coprime N) : v ∉ Sχ := fun h ↦
  (pr_prime v).one_lt.ne' (hv.eq_one_of_dvd ((mem_ratDirichletS (NeZero.ne N) v).mp h))

/-- The Dirichlet test is invariant under the local units at every place outside `ratDirichletS`,
where its factor is the integer indicator. -/
theorem dirTest_isLocalUnitInvariant (hχ : χ.IsPrimitive) (f : 𝓢(ℝ, ℂ)) {v : Vℚ} (hv : v ∉ Sχ) :
    IsLocalUnitInvariant v (dirTest hχ f) := by
  intro u hu x
  have hu1 : Valued.v (u : v.adicCompletion ℚ) = 1 :=
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp hu
  have hc (w : Vℚ) : (x * (ι v u : 𝔸)).2 w ∈ w.adicCompletionIntegers ℚ ↔
      x.2 w ∈ w.adicCompletionIntegers ℚ := by
    by_cases hw : w = v
    · subst hw
      rw [mul_ofAdic_snd_self, HeightOneSpectrum.mem_adicCompletionIntegers,
        HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, hu1, mul_one]
    · rw [mul_ofAdic_snd_ne hw]
  have hs (w : Sχ) : (x * (ι v u : 𝔸)).2 w.val = x.2 w.val :=
    mul_ofAdic_snd_ne (fun h ↦ hv (by rw [← h]; exact w.2)) u x
  rw [dirTest_apply, dirTest_apply, mul_ofAdic_fst]
  simp only [hs]
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact absurd (fun w hw ↦ (hc w).mp (h₁ w hw)) h₂
  · exact absurd (fun w hw ↦ (hc w).mpr (h₂ w hw)) h₁
  · rfl

open Classical in
private theorem ratPrimeIdele_inv_mul (A : Finset Vℚ) (x : 𝔸) :
    ((↑(ratPrimeIdele A)⁻¹ : 𝔸) * x).1 = x.1 ∧
      ∀ w : Vℚ, ((↑(ratPrimeIdele A)⁻¹ : 𝔸) * x).2 w =
        (if w ∈ A then (pr w : w.adicCompletion ℚ)⁻¹ else 1) * x.2 w := by
  induction A using Finset.induction_on generalizing x with
  | empty =>
    simp only [ratPrimeIdele, Finset.prod_empty, inv_one, Units.val_one, one_mul,
      Finset.notMem_empty, ↓reduceIte, implies_true, and_self]
  | insert v A hv ih =>
    have e : (↑(ratPrimeIdele (insert v A))⁻¹ : 𝔸) * x =
        (↑(ratPrimeIdele A)⁻¹ : 𝔸) * x * (ι v (ratPrimeUnit v)⁻¹ : 𝔸) := by
      simp only [ratPrimeIdele]
      rw [Finset.prod_insert hv, mul_inv, Units.val_mul, map_inv]
      ring
    obtain ⟨h1, h2⟩ := ih x
    rw [e]
    refine ⟨(mul_ofAdic_fst _ _ _).trans h1, fun w ↦ ?_⟩
    by_cases hw : w = v
    · subst hw
      rw [mul_ofAdic_snd_self, h2]
      simp only [hv, Finset.mem_insert_self, ↓reduceIte, one_mul, Units.val_inv_eq_inv_val,
        ratPrimeUnit_val]
      ring
    · rw [mul_ofAdic_snd_ne hw, h2]
      simp only [Finset.mem_insert, hw, false_or]

open Classical in
/-- Paper: Definition 5.3.1.4, p. 242, and Lemma 5.3.1.3, p. 241, over `ℚ`.
**Pointwise formula for the principal value of the Dirichlet test.** For a finite set `T` of
places `p ∤ N`, `PV_T (dirTest χ f)` at the adele `x` is the inclusion–exclusion sum over
`A ⊆ T` of `(-1)^{|A|}` times the Dirichlet test at `x` with `x_p` replaced by `x_p / p` for
`p ∈ A`. Expanded, this is the product of the local factors `1_{ℤ_p}(x_p) - 1_{pℤ_p}(x_p)` at
`p ∈ T` with the factors of `dirTest` elsewhere.
Deviation: Stated as the inclusion–exclusion sum of `ratPV_eq_sum_translate`; the product form
is its expansion and is not stated separately. -/
theorem adelePrincipalValue_apply_ratDirichlet (hχ : χ.IsPrimitive) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) (f : 𝓢(ℝ, ℂ)) (x : 𝔸) :
    adelePrincipalValue ℚ T (dirTest hχ f) (Multiplicative.ofAdd x) =
      ∑ A ∈ T.powerset, (-1 : ℂ) ^ A.card *
        if ∀ w : Vℚ, w ∉ Sχ → (if w ∈ A then (pr w : w.adicCompletion ℚ)⁻¹ else 1) * x.2 w ∈
            w.adicCompletionIntegers ℚ then
          f (realCoord (x.1 Rat.infinitePlace)) *
            ∏ w : Sχ, unitCharTestFun w.val (ratDirichletLocalChar hχ w.val) (x.2 w.val)
        else 0 := by
  let ev : Bℚ →ₗ[ℂ] ℂ :=
    { toFun := fun φ ↦ φ (Multiplicative.ofAdd x)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  change ev (adelePrincipalValue ℚ T (dirTest hχ f)) = _
  rw [ratPV_eq_sum_translate T _ fun v hv ↦
    dirTest_isLocalUnitInvariant hχ f (notMem_ratDirichletS_of_coprime (hT v hv)), map_sum]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  rw [map_smul, smul_eq_mul]
  congr 1
  change dirTest hχ f (Multiplicative.ofAdd ((↑(ratPrimeIdele A)⁻¹ : 𝔸) * x)) = _
  obtain ⟨h1, h2⟩ := ratPrimeIdele_inv_mul A x
  have hs (w : Sχ) : ((↑(ratPrimeIdele A)⁻¹ : 𝔸) * x).2 w.val = x.2 w.val := by
    have hwA : w.val ∉ A := fun h ↦
      notMem_ratDirichletS_of_coprime (hT _ (Finset.mem_powerset.mp hA h)) w.2
    rw [h2]
    simp only [hwA, ↓reduceIte, one_mul]
  rw [dirTest_apply]
  simp only [hs, h1]
  simp only [h2]

/-- Paper: Proposition 11.2.0.1, pp. 484–485, and (11.3.1.3), p. 494, over `ℚ`.
**Principal value of the Dirichlet test against depletion.** For a primitive `χ` of conductor
`N > 1` and a finite set `T` of places `p ∤ N`, the homogeneous theta of `PV_T (dirTest χ f)` at
`k · τ(eˣ)` is `ω(k)⁻¹ · mass · e^{-x/2} · (∏_{p ∈ T} (I - χ(p) D_p)) U_χ(f) (x)`, where
`U_χ(f) = twistedHalfLogProfile χ f` and `T' = T.image pr` is the set of primes of `T`. -/
theorem ratBridge_principalValue (hχ : χ.IsPrimitive) (hN : 1 < N) (T : Finset Vℚ)
    (hT : ∀ v ∈ T, (pr v).Coprime N) (f : 𝓢(ℝ, ℂ)) (k : (ideleClassNorm ℚ).ker) (x : ℝ) :
    homogeneousAdelicTheta ω (adelePrincipalValue ℚ T (dirTest hχ f))
        (k.val * ratNormSection (ratExpUnit x)) =
      (ω k : ℂ)⁻¹ * mass * ((Real.exp (-(x / 2)) : ℂ) *
        dirichletDeplete χ (T.image pr) (twistedHalfLogProfile χ f) x) :=
  ratBridge_principalValue_general hχ T hT _
    (fun v hv ↦ dirTest_isLocalUnitInvariant hχ f (notMem_ratDirichletS_of_coprime (hT v hv))) _
    (twistedRadialTheta χ f) (fun t k ↦ ratBridge_dirichletTest_theta hχ hN f t k) k x

end Rat

end RiemannMasullo.Isolated
