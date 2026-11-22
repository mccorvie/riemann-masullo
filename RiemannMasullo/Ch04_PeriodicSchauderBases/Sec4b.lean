module

public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec4
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec2
import all RiemannMasullo.AppD_SchwartzBruhat.Sec3a
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# Comparisons for the exponential system on monogenic quotients

Masullo, §4.4.2, pp. 191–194. The two descriptions of the annihilator use
inverse characters. In the positive-real case, normalized logarithmic
coordinates identify the quotient with the unit circle used in §4.2.
-/

@[expose] public noncomputable section

open Function MeasureTheory Set
open scoped NNReal

namespace RiemannMasullo

section Modulated

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* ℝ≥0ˣ) (γ : G) (hm : IsModulation m) (hms : Surjective m)
  (hγ : 1 < (m γ).val)

local notation "K" => m.toMonoidHom.ker

/-- Paper: Equation (4.4.2.4), p. 193, and Remark D.3.5.2, pp. 818–819.
With the same lifts, phases and integer indices, the §4.4 quotient character
pulled back to the original group is the pointwise inverse of the appendix character.
Deviation: This makes the comparison of the two parametrizations explicit. -/
theorem modulatedCyclicCharacter_eq_inv_zpowers_annihilator
    (χ : PontryaginDual K → PontryaginDual G)
    (hχ : ∀ (ω : PontryaginDual K) (k : K), χ ω k.val = ω k)
    (t₀ : PontryaginDual K → ℝ)
    (ht₀ : let L := Real.log ((m γ).val : ℝ)
      ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t₀ ω * L) = χ ω γ)
    (j : PontryaginDual K × ℤ) (x : G) :
    let a := (modulatedCharacter_zpowers_annihilator m hm hms γ hγ χ hχ t₀ ht₀).choose
    modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j (QuotientGroup.mk x) = ((a j).val x)⁻¹ := by
  dsimp only
  rw [modulatedCyclicCharacter_mk,
    (modulatedCharacter_zpowers_annihilator m hm hms γ hγ χ hχ t₀ ht₀).choose_spec j.1 j.2 x,
    mul_inv, ← Circle.exp_neg, ← neg_mul, neg_sub]

/-- Paper: Definition 4.4.2.1, pp. 191–192, and Proposition 4.5.1.1(1), p. 197.
The ordinary orbit sum is complex-linear on the two-sided decay space. -/
theorem modulatedPeriodization_isLinearMap :
    IsLinearMap ℂ (modulatedPeriodization m γ hm hms hγ) := by
  have hs := modulatedPeriodization_hasSum m γ hm hms hγ
  constructor
  · intro f g
    apply Subtype.ext
    funext z
    induction z using QuotientGroup.induction_on with
    | _ x => exact (hs (f + g) x).unique ((hs f x).add (hs g x))
  · intro c f
    apply Subtype.ext
    funext z
    induction z using QuotientGroup.induction_on with
    | _ x => exact (hs (c • f) x).unique ((hs f x).const_smul c)

variable [MeasurableSpace G] [BorelSpace G]

/-- Paper: Definition 4.4.2.1, pp. 191–192, and Proposition 4.5.1.1(3), p. 198.
The character-weighted orbit sum is complex-linear on the two-sided decay space. -/
theorem modulatedIsotypicPeriodization_isLinearMap (μ₁ : Measure K) [μ₁.IsHaarMeasure]
    (χ : PontryaginDual G) :
    IsLinearMap ℂ (modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ) := by
  have hs := modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ χ
  have hi := modulatedIsotypicPeriodization_integrable m γ hm μ₁ χ
  constructor
  · intro f g
    apply Subtype.ext
    funext z
    induction z using QuotientGroup.induction_on with
    | _ x =>
      apply (hs (f + g) x).unique
      apply ((hs f x).add (hs g x)).congr_fun
      intro n
      change (∫ k : K, (χ k.val : ℂ) * (f.val _ + g.val _) ∂μ₁) = _
      simp_rw [mul_add]
      exact integral_add (hi f n x) (hi g n x)
  · intro c f
    apply Subtype.ext
    funext z
    induction z using QuotientGroup.induction_on with
    | _ x =>
      apply (hs (c • f) x).unique
      apply ((hs f x).const_smul c).congr_fun
      intro n
      change (∫ k : K, (χ k.val : ℂ) * (c * f.val _) ∂μ₁) = _
      simp_rw [mul_left_comm (χ _ : ℂ) c]
      exact integral_const_mul _ _

end Modulated

section PositiveReal

local notation "m" => ContinuousMonoidHom.id ℝ≥0ˣ
local notation "K" => MonoidHom.ker (ContinuousMonoidHom.toMonoidHom m)
local notation "χ₀" => (fun _ : PontryaginDual K ↦ (1 : PontryaginDual ℝ≥0ˣ))
local notation "t₀" => (fun _ : PontryaginDual K ↦ (0 : ℝ))
local notation "T" => AddCircle (1 : ℝ)
local notation "S" => ElementarySchwartz 0 1 0 (PUnit : Type)
local notation "point" z => ((0, fun _ : Fin 1 ↦ z, 0, PUnit.unit) :
  ElementaryLieGroup 0 1 0 (PUnit : Type))

/-- Paper: Example D.3.3.4, p. 805. The positive reals with the identity module
are a modulated group. -/
theorem identityModulation_isModulation : IsModulation m :=
  ⟨isProperMap_id, exists_ne 1⟩

variable (γ : ℝ≥0ˣ) (hγ : 1 < γ.val)

local notation "Q[" g "]" => ℝ≥0ˣ ⧸ Subgroup.zpowers g
local notation "L[" g "]" => Real.log ((Units.val g : ℝ≥0) : ℝ)

include hγ in
/-- Paper: Situation 4.4.2.3(5), p. 192, and Remark 4.4.2.8, p. 194.
For the trivial lift, the prescribed phase is zero. -/
theorem positiveRealCyclic_trivialPhase :
    ∀ ω : PontryaginDual K, t₀ ω ∈ Ico 0 (2 * Real.pi / L[γ]) ∧
      Circle.exp (t₀ ω * L[γ]) = χ₀ ω γ := by
  intro ω
  have hL : 0 < L[γ] := Real.log_pos (by exact_mod_cast hγ)
  refine ⟨⟨le_rfl, div_pos (by positivity) hL⟩, ?_⟩
  simp

include hγ in
/-- The normalized logarithm takes the generator to one and descends to the circle. -/
private theorem positiveRealCyclicCoordinate :
    ∃ e : Q[γ] ≃ₜ* Multiplicative T, ∀ t : ℝ≥0ˣ,
      (e (QuotientGroup.mk t)).toAdd = ((L[t] / L[γ] : ℝ) : T) := by
  have hL : L[γ] ≠ 0 := (Real.log_pos (by exact_mod_cast hγ)).ne'
  let d := (ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L[γ] hL)).symm
  let c : ℝ≥0ˣ ≃ₜ* Multiplicative ℝ := positiveRealLogEquiv.trans
    { d.toLinearEquiv.toAddEquiv.toMultiplicative with
      continuous_toFun := d.continuous
      continuous_invFun := d.symm.continuous }
  have hc (t : ℝ≥0ˣ) : (c t).toAdd = L[t] / L[γ] := by
    change (positiveRealLogEquiv t).toAdd * (L[γ])⁻¹ = _
    rw [positiveRealLogEquiv_apply, div_eq_mul_inv]
  have hgen : c γ = Multiplicative.ofAdd (1 : ℝ) := (hc γ).trans (div_self hL)
  let H := Subgroup.zpowers (Multiplicative.ofAdd (1 : ℝ))
  have hmap : (Subgroup.zpowers γ).map c.toMulEquiv.toMonoidHom = H := by
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hgen
  let q : Q[γ] ≃* Multiplicative T := QuotientGroup.congr _ H c.toMulEquiv hmap
  let e : Q[γ] ≃ₜ* Multiplicative T :=
    { q with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        ((AddCircle.continuous_mk' (1 : ℝ)).comp c.continuous)
      continuous_invFun := (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp c.symm.continuous) }
  exact ⟨e, fun t ↦ congrArg (fun x : ℝ ↦ (x : T)) (hc t)⟩

local notation "E₁" => ElementaryLieGroup 0 1 0 (PUnit : Type)

/-- In the elementary one-torus all factors except the circle are trivial. -/
private def elementaryCircleCoordinate : Multiplicative T ≃ₜ* Multiplicative E₁ where
  toFun z := Multiplicative.ofAdd (point z.toAdd)
  invFun g := Multiplicative.ofAdd (g.toAdd.2.1 0)
  left_inv _ := rfl
  right_inv g := by
    change (point (g.toAdd.2.1 0)) = g.toAdd
    refine Prod.ext (Subsingleton.elim _ _) (Prod.ext ?_ (Subsingleton.elim _ _))
    funext i
    rw [Subsingleton.elim i 0]
  map_mul' _ _ := Prod.ext (Subsingleton.elim _ _) (Prod.ext rfl (Subsingleton.elim _ _))
  continuous_toFun := continuous_const.prodMk ((continuous_pi fun _ ↦ continuous_id).prodMk
    continuous_const)
  continuous_invFun := (continuous_apply 0).comp (continuous_fst.comp continuous_snd)

include hγ in
/-- Paper: Definition 4.2.1.1, p. 162, and Remark 4.4.2.8, p. 194.
The two Schwartz topologies on the positive-real cyclic quotient agree under
the coordinate log(t) / log(γ) modulo one.
Deviation: The paper uses the same space for both models. Lean states their
continuous linear equivalence and specifies it by evaluation on representatives. -/
theorem positiveRealCyclicSchwartz_equiv :
    ∃ A : SchwartzBruhat Q[γ] ≃L[ℂ] S, ∀ (f : SchwartzBruhat Q[γ]) (t : ℝ≥0ˣ),
      A f (point ((L[t] / L[γ] : ℝ) : T)) = f (QuotientGroup.mk t) := by
  refine (positiveRealCyclicCoordinate γ hγ).elim fun c hc ↦ ?_
  have : T2Space Q[γ] := c.toHomeomorph.isEmbedding.t2Space
  have : SecondCountableTopology Q[γ] := c.toHomeomorph.isEmbedding.secondCountableTopology
  let p : ElementaryLCAPresentation Q[γ] := ⟨0, 1, 0, PUnit, c.trans elementaryCircleCoordinate⟩
  have hG := (lca_elementary_iff (G := Q[γ])).mpr ⟨p⟩
  let top : (⊤ : Subgroup Q[γ]) ≃ₜ* Q[γ] :=
    ⟨Subgroup.topEquiv, continuous_subtype_val, continuous_id.subtype_mk _⟩
  let a : BruhatStructuralPair Q[γ] := ⟨(⊤, OrderDual.toDual ⊥), isOpen_univ,
    isCompactlyGeneratedGroup_of_continuousMulEquiv top.symm hG.1,
    isBruhatGoodSubgroup_bot_iff.mpr hG.2, bot_le⟩
  let q : a.quotient ≃* Q[γ] :=
    QuotientGroup.quotientKerEquivOfRightInverse a.val.1.subtype top.symm (fun _ ↦ rfl)
  let q' : a.quotient ≃ₜ* Q[γ] :=
    { q with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr continuous_subtype_val
      continuous_invFun := QuotientGroup.continuous_mk.comp top.symm.continuous }
  let e : ElementaryLCAPresentation a.quotient := ⟨0, 1, 0, PUnit, q'.trans p.equiv⟩
  let J : S →ₗ[ℂ] SchwartzBruhat Q[γ] := schwartzBruhatStageInclusion a e
  have hJ := schwartzBruhatStage_isEmbedding a e
  have hs := schwartzBruhat_maxStage_surjective a (fun b ↦
    (show b.val.1 ≤ ⊤ ∧ (⊥ : Subgroup Q[γ]) ≤ OrderDual.ofDual b.val.2 from ⟨le_top, bot_le⟩)) e
  let B := ContinuousLinearEquiv.ofIsHomeomorph (LinearEquiv.ofBijective J ⟨hJ.injective, hs⟩)
    (isHomeomorph_iff_isEmbedding_surjective.mpr ⟨hJ, hs⟩)
  refine ⟨B.symm, fun f t ↦ ?_⟩
  have hval (s : S) : B s (QuotientGroup.mk t) = s (point ((L[t] / L[γ] : ℝ) : T)) := by
    change schwartzBruhatStageRealization a e s (QuotientGroup.mk t) = _
    rw [schwartzBruhatStageRealization_apply, dite_eq_left (Subgroup.mem_top _)]
    change s (point ((c (QuotientGroup.mk t)).toAdd)) = _
    rw [hc]
  rw [← hval, B.apply_symm_apply]

variable (A : SchwartzBruhat Q[γ] ≃L[ℂ] S)
  (hA : ∀ (f : SchwartzBruhat Q[γ]) (t : ℝ≥0ˣ),
    A f (point ((L[t] / L[γ] : ℝ) : T)) = f (QuotientGroup.mk t))

include hA

/-- Test a transported function against an elementary circle function on representatives. -/
private theorem positiveRealCyclic_eq_of_mk (f : SchwartzBruhat Q[γ]) (s : S)
    (h : ∀ t : ℝ≥0ˣ, f (QuotientGroup.mk t) = s (point ((L[t] / L[γ] : ℝ) : T))) :
    A f = s := by
  have he (t : ℝ≥0ˣ) : f (QuotientGroup.mk t) = A.symm s (QuotientGroup.mk t) := by
    let ev (v : S) := v (point ((L[t] / L[γ] : ℝ) : T))
    exact (h t).trans ((congrArg ev (A.apply_symm_apply s)).symm.trans (hA (A.symm s) t))
  have hf : f = A.symm s :=
    Subtype.ext (funext fun z ↦ QuotientGroup.induction_on (C := fun q ↦ f q = A.symm s q) z he)
  exact (congrArg A hf).trans (A.apply_symm_apply s)

/-- Paper: Equations (4.2.1.3), p. 162, and (4.4.2.5), p. 193.
In normalized logarithmic coordinates the trivial-lift exponential of §4.4
at index n is the §4.2 exponential at index −n.
Deviation: This makes the change of index between the two conventions explicit. -/
theorem modulatedCyclicExponential_positiveReal (n : ℤ) :
    A (modulatedCyclicExponential m γ identityModulation_isModulation hγ χ₀ t₀
      (positiveRealCyclic_trivialPhase γ hγ) (1, n)) = cyclicExponential (-n) := by
  apply positiveRealCyclic_eq_of_mk γ A hA
  intro t
  change (modulatedCyclicCharacter m γ hγ χ₀ t₀ (positiveRealCyclic_trivialPhase γ hγ)
    (1, n) (QuotientGroup.mk t) : ℂ) = _
  refine (congrArg (fun z : Circle ↦ (z : ℂ)) (modulatedCyclicCharacter_mk m γ hγ χ₀ t₀
    (positiveRealCyclic_trivialPhase γ hγ) (1, n) t)).trans ?_
  refine Eq.trans ?_ (cyclicExponential_apply _ (NNReal.coe_lt_coe.mpr hγ) (-n) L[t]).symm
  change (↑((1 : Circle)⁻¹ * Circle.exp ((0 - 2 * Real.pi * (n : ℝ) / L[γ]) * L[t])) : ℂ) = _
  rw [inv_one, one_mul, Circle.coe_exp]
  congr 1
  push_cast
  ring

local instance instBorelSpacePositiveRealsSec4b : BorelSpace ℝ≥0ˣ :=
  borelSpace_units_of_continuousInv₀ ℝ≥0
local instance instMeasurableSpaceCyclicQuotientSec4b : MeasurableSpace Q[γ] := borel _

variable (μ₁ : Measure K) [μ₁.IsHaarMeasure]

omit hA in
/-- Transport to the circle takes quotient Haar measure to its mass times probability Haar. -/
private theorem map_haar_cyclicCoordinate {G : Type*} [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    (c : G ≃ₜ* Multiplicative T) (ν : Measure G) [ν.IsHaarMeasure] :
    ν.map (fun q ↦ (c q).toAdd) = ν univ • (AddCircle.haarAddCircle : Measure T) := by
  let ρ : Measure T := ν.map (fun q ↦ (c q).toAdd)
  have hH := c.isHaarMeasure_map ν
  have : ρ.IsAddLeftInvariant :=
    ⟨fun z ↦ map_mul_left_eq_self (ν.map c) (Multiplicative.ofAdd z)⟩
  have : IsFiniteMeasureOnCompacts ρ := hH.toIsFiniteMeasureOnCompacts
  have h := Measure.isAddInvariant_eq_smul_of_compactSpace ρ AddCircle.haarAddCircle
  have hmass := congrArg (fun η : Measure T ↦ η univ) h
  have hρ : ρ univ = ν univ := Measure.map_apply c.continuous.measurable MeasurableSet.univ
  simp only [smul_apply, measure_univ, ENNReal.smul_def, smul_eq_mul, mul_one, hρ] at hmass
  rw [hmass]
  exact h

/-- Paper: Equations (4.2.1.4), p. 162, and (4.4.2.6), p. 193, and Remark 4.4.2.7, p. 194.
With the stated quotient Haar mass, the trivial-lift coefficient at index n
is the pullback of the probability Haar Fourier coefficient at index −n.
Deviation: The quotient measure is specified by its Haar mass, and the index
change and transport between the two models are explicit. -/
theorem modulatedCyclicFourierCoeff_positiveReal (ν : Measure Q[γ]) [ν.IsHaarMeasure]
    (hν : ν univ = ENNReal.ofReal L[γ] * μ₁ univ) (n : ℤ) :
    modulatedCyclicFourierCoeff m γ identityModulation_isModulation hγ χ₀ t₀
      (positiveRealCyclic_trivialPhase γ hγ) μ₁ ν (1, n) =
        (cyclicFourierCoeff (-n)).comp A.toContinuousLinearMap := by
  refine (positiveRealCyclicCoordinate γ hγ).elim fun c hc ↦ ?_
  have : BorelSpace Q[γ] := ⟨rfl⟩
  have : Subsingleton K := ⟨fun x y ↦ Subtype.ext (x.property.trans y.property.symm)⟩
  have hL : 0 < L[γ] := Real.log_pos (NNReal.coe_lt_coe.mpr hγ)
  have hμ : 0 < μ₁.real univ := measureReal_univ_pos
  have heval (s : SchwartzBruhat Q[γ]) (q : Q[γ]) : A s (point (c q).toAdd) = s q :=
    QuotientGroup.induction_on (C := fun q ↦ A s (point (c q).toAdd) = s q) q fun t ↦
      (congrArg (fun z : T ↦ A s (point z)) (hc t)).trans (hA s t)
  let v := modulatedCyclicExponential m γ identityModulation_isModulation hγ χ₀ t₀
    (positiveRealCyclic_trivialPhase γ hγ) (1, n)
  have hv : A v = cyclicExponential (-n) := modulatedCyclicExponential_positiveReal γ hγ A hA n
  apply ContinuousLinearMap.ext
  intro f
  let F (z : T) := fourier n z * A f (point z)
  have hF (q : Q[γ]) : f q * star (v q) = F (c q).toAdd := by
    let z := (c q).toAdd
    have hexp : v q = fourier (-n) z :=
      (heval v q).symm.trans (congrArg (fun s : S ↦ s (point z)) hv)
    have hstar : star (v q) = fourier n z :=
      (congrArg star (hexp.trans fourier_neg)).trans (star_star _)
    exact (congrArg₂ (· * ·) (heval f q).symm hstar).trans (mul_comm _ _)
  have hi : (∫ q, F (c q).toAdd ∂ν) = (ν univ).toReal • ∫ z, F z ∂AddCircle.haarAddCircle := calc
    _ = ∫ z, F z ∂ν.map (fun q ↦ (c q).toAdd) :=
      (integral_map_equiv c.toHomeomorph.toMeasurableEquiv F).symm
    _ = _ := by rw [map_haar_cyclicCoordinate c ν, integral_smul_measure]
  change (L[γ] * μ₁.real univ)⁻¹ * (∫ q, f q * star (v q) ∂ν) =
    ∫ z : T, fourier (- -n) z • A f (point z) ∂AddCircle.haarAddCircle
  let mass : ℂ := (L[γ] : ℂ) * (μ₁.real univ : ℂ)
  have hm : ((ν univ).toReal : ℂ) = mass := by
    simp only [hν, ENNReal.toReal_mul, ENNReal.toReal_ofReal hL.le, Complex.ofReal_mul, mass,
      Measure.real]
  have hm₀ : mass ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hL.ne') (Complex.ofReal_ne_zero.mpr hμ.ne')
  have hs : (∫ q, f q * star (v q) ∂ν) = mass * ∫ z, F z ∂AddCircle.haarAddCircle :=
    (integral_congr_ae (ae_of_all _ hF)).trans
      (hi.trans ((Complex.real_smul).trans (congrArg (· * _) hm)))
  have hinv : (((L[γ] * μ₁.real univ)⁻¹ : ℝ) : ℂ) = mass⁻¹ := by
    rw [Complex.ofReal_inv, Complex.ofReal_mul]
  calc
    _ = mass⁻¹ * (mass * ∫ z, F z ∂AddCircle.haarAddCircle) := congrArg₂ (· * ·) hinv hs
    _ = ∫ z, F z ∂AddCircle.haarAddCircle := inv_mul_cancel_left₀ hm₀ _
    _ = _ := congrArg (fun j ↦ ∫ z : T, fourier j z • A f (point z) ∂AddCircle.haarAddCircle)
      (neg_neg n).symm

local notation "logProfiles" =>
  Exists.choose (identityModulationExponentialDecay_equiv univ ordConnected_univ univ_nonempty)

/-- Paper: Definitions 4.2.1.1, p. 162, and 4.4.2.1, pp. 191–192.
The ordinary periodizations agree under the logarithmic identification of
the sources and the normalized logarithmic identification of the targets.
Deviation: The comparison makes the coordinate transports explicit. -/
theorem modulatedPeriodization_positiveReal (f : PositiveRealExponentialDecay univ) :
    A (modulatedPeriodization m γ identityModulation_isModulation surjective_id hγ
      (logProfiles f)) = cyclicPeriodization γ.val (NNReal.coe_lt_coe.mpr hγ) f := by
  apply positiveRealCyclic_eq_of_mk γ A hA
  intro t
  have hs := modulatedPeriodization_hasSum m γ identityModulation_isModulation surjective_id hγ
    (logProfiles f) t
  apply hs.unique
  apply (cyclicPeriodization_hasSum γ.val (NNReal.coe_lt_coe.mpr hγ) f L[t]).congr_fun
  intro n
  refine (identityModulationExponentialDecay_equiv univ ordConnected_univ univ_nonempty).choose_spec
    f (γ ^ n * t) |>.trans (congrArg f.val ?_)
  rw [Units.val_mul, NNReal.coe_mul, Real.log_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow,
    Real.log_zpow, add_comm]
  · exact NNReal.coe_ne_zero.mpr (γ ^ n).ne_zero
  · exact NNReal.coe_ne_zero.mpr t.ne_zero

/-- Paper: Definitions 4.2.1.1, p. 162, and 4.4.2.1, pp. 191–192.
After the same coordinate transports, trivial-character periodization is the
§4.2 periodization multiplied by the Haar mass of the trivial norm-one group.
Deviation: The comparison makes the coordinate transports and mass factor explicit. -/
theorem modulatedIsotypicPeriodization_positiveReal (f : PositiveRealExponentialDecay univ) :
    A (modulatedIsotypicPeriodization m γ identityModulation_isModulation surjective_id hγ
      μ₁ 1 (logProfiles f)) =
        (μ₁.real univ : ℂ) • cyclicPeriodization γ.val (NNReal.coe_lt_coe.mpr hγ) f := by
  let g := logProfiles f
  let P := modulatedPeriodization m γ identityModulation_isModulation surjective_id hγ g
  let mass : ℂ := μ₁.real univ
  have hP : modulatedIsotypicPeriodization m γ identityModulation_isModulation surjective_id hγ
      μ₁ 1 g = mass • P := by
    apply Subtype.ext
    funext q
    induction q using QuotientGroup.induction_on with
    | _ t =>
      apply (modulatedIsotypicPeriodization_hasSum m γ identityModulation_isModulation
        surjective_id hγ μ₁ 1 g t).unique
      apply ((modulatedPeriodization_hasSum m γ identityModulation_isModulation
        surjective_id hγ g t).const_smul mass).congr_fun
      intro n
      have hk (k : K) : k.val = 1 := k.property
      change (∫ k : K, (1 : ℂ) * g.val (γ ^ n * (k.val * t)) ∂μ₁) = mass * g.val (γ ^ n * t)
      simp only [hk, one_mul, integral_const, Complex.real_smul, mass]
  exact (congrArg A hP).trans ((A.map_smul mass P).trans
    (congrArg (mass • ·) (modulatedPeriodization_positiveReal γ hγ A hA f)))

end PositiveReal

end RiemannMasullo
