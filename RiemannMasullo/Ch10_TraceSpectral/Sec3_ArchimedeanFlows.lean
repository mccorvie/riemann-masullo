module

public import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec1
import RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c

/-! # The archimedean parameters of a character are its frequencies along archimedean flows

A unitary character of the idele classes has, at each infinite place, a radial exponent and
(at a complex place) an angular weight: the parameters of `realHeckeCharacter_parameters` and
`complexHeckeCharacter_parameters`. The count of characters in the library,
`idelicExplicitFormula_normOneFourier_count`, measures a character by its frequencies along
one-parameter subgroups of the norm-one classes instead. This file links the two, for the
characters that are trivial on the image of a norm section `τ`: there are finitely many
one-parameter subgroups of the norm-one classes, one or two for each infinite place, along
which the frequency of the character is its radial exponent, or its angular weight times `i`.

* `exists_normOne_flows_archimedean_parameters`: if all these frequencies have norm at most
  `X`, then all archimedean parameters have norm at most `X`. This is the private lemma
  `idelicExplicitFormula_summable_spectral_characters_archimedean` of
  `AppB_AnalyticNT/Sec4b.lean`, with the character not in a subtype.
* `exists_flows_archimedean_parameters_le`: the same with the flows as one-parameter subgroups
  of the idele classes with values in the norm-one classes, and the frequency
  `bruhatDirectionalDeriv (Y i) (fun g ↦ (ψ g : ℂ)) 1` in the shape of the count.

The flows are the radial flow `t ↦ e ^ t` at a real place, and the radial flow `t ↦ e ^ (t / 2)`
and the rotation `t ↦ e ^ (i t)` at a complex place, each divided by its image under
`τ ∘ norm`.

Three private helpers are copies of private lemmas of `AppB_AnalyticNT/Sec4b.lean`:
`explicitFormula_real_character`, `explicitFormula_exp_cpow` and
`idelicExplicitFormula_infiniteMatching_complexCharacterSum_polar`.

`Sec3_TraceClass` uses `exists_flows_archimedean_parameters_le`. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "infiniteClassMap(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w

/-- At a real place, a character on the class of a real unit is given by its radial exponent
and sign parity. Copy of the private `explicitFormula_real_character` of
`AppB_AnalyticNT/Sec4b.lean`. -/
private theorem exists_normOne_flows_archimedean_parameters_real_character
    (w : InfinitePlace F) (hw : w.IsReal) (χ : PontryaginDual C𝔽) (u : ℝˣ) :
    ((χ (infiniteClassMap(w)
      (Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom u)) :
        Circle) : ℂ) =
      (‖(u : ℝ)‖ : ℂ) ^ (realHeckeCharacter_parameters χ w hw).exists.choose.1 *
        (if 0 < (u : ℝ) then 1 else (-1 : ℂ)) ^
          (realHeckeCharacter_parameters χ w hw).exists.choose.2.val := by
  rw [← ((realHeckeCharacter_parameters χ w hw).exists.choose_spec.2 u)]
  change _ = (χ _ : ℂ) * (_ : ℂ) ^ (0 : ℂ)
  rw [Complex.cpow_zero, mul_one]

/-- `(e^x)^a = e^{a x}` for real `x`. Copy of the private `explicitFormula_exp_cpow` of
`AppB_AnalyticNT/Sec4b.lean`. -/
private theorem exists_normOne_flows_archimedean_parameters_exp_cpow (x : ℝ) (a : ℂ) :
    ((Real.exp x : ℝ) : ℂ) ^ a = Complex.exp (a * x) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]

/-- The norm and the inverse character of a complex local unit in log-polar coordinates. Copy
of the private `idelicExplicitFormula_infiniteMatching_complexCharacterSum_polar` of
`AppB_AnalyticNT/Sec4b.lean`. -/
private theorem exists_normOne_flows_archimedean_parameters_polar
    (w : InfinitePlace F) (hw : w.IsComplex) (y φ : ℝ) :
    let e := Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm.toMonoidHom
    let z : ℂ := y / 2 + φ * Complex.I
    let c := infiniteClassMap(w) (e (Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)))
    Real.log ((ideleClassNorm F c : ℝ≥0) : ℝ) = y ∧ ∀ χ : PontryaginDual C𝔽,
      let p := (complexHeckeCharacter_parameters χ w hw).exists.choose
      (χ c : ℂ)⁻¹ = Complex.exp (-p.1 * y) * Complex.exp (φ * Complex.I) ^ (-p.2) := by
  intro e z
  let u := Units.mk0 (Complex.exp z) (Complex.exp_ne_zero z)
  let c := infiniteClassMap(w) (e u)
  have hz : ‖(u : ℂ)‖ = Real.exp (y / 2) := by
    change ‖Complex.exp _‖ = _
    simp [Complex.norm_exp, z, Complex.div_ofNat_re]
  have hr : ‖(u : ℂ)‖ ^ 2 = Real.exp y := by
    rw [hz, sq, ← Real.exp_add]
    congr 1
    ring
  have harg : (u : ℂ) / (‖(u : ℂ)‖ : ℂ) = Complex.exp (φ * Complex.I) := by
    rw [hz, div_eq_iff (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
    change Complex.exp (_ + _) = _
    rw [Complex.exp_add, mul_comm, Complex.ofReal_exp, Complex.ofReal_div, Complex.ofReal_ofNat]
  have hn : Real.log ((ideleClassNorm F c : ℝ≥0) : ℝ) = y := by
    rw [show ((ideleClassNorm F c : ℝ≥0) : ℝ) = ‖(u : ℂ)‖ ^ 2 by
      rw [ideleClassNorm_ofCompletion, hw.mult_eq_two]
      change ‖((e u : w.Completionˣ) : w.Completion)‖ ^ 2 = _
      congr 1
      let j := InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw
      change ‖j.symm (u : ℂ)‖ = ‖(u : ℂ)‖
      rw [← dist_zero_right, ← dist_zero_right (u : ℂ), ← j.symm.dist_eq _ 0,
        show j.symm 0 = 0 from
          map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hw).symm],
      hr, Real.log_exp]
  refine ⟨hn, fun χ ↦ ?_⟩
  let p := (complexHeckeCharacter_parameters χ w hw).exists.choose
  have hp := (complexHeckeCharacter_parameters χ w hw).exists.choose_spec.2 u
  change (χ c : ℂ) * _ ^ (0 : ℂ) = _ at hp
  rw [Complex.cpow_zero, mul_one, hr, harg,
    exists_normOne_flows_archimedean_parameters_exp_cpow] at hp
  rw [hp, mul_inv, ← Complex.exp_neg, ← zpow_neg]
  simp only [neg_mul]

open Classical in
/-- For one infinite place: two one-parameter subgroups of the norm-one classes along which
the frequency of every character trivial on the image of the norm section is its radial
exponent, or (second subgroup, complex place) its angular weight times `i`. This is the
construction in the proof of the private
`idelicExplicitFormula_summable_spectral_characters_archimedean` of
`AppB_AnalyticNT/Sec4b.lean`, with the frequencies kept as equalities. -/
private theorem exists_normOne_flows_archimedean_parameters_place (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) (w : InfinitePlace F) :
    ∃ Y : Bool → LCATopologicalLie (ideleClassNorm F).ker,
      ∀ χ : PontryaginDual C𝔽, (∀ t : ℝ≥0ˣ, χ (τ t) = 1) →
        if hw : w.IsReal then
          ∀ j, bruhatDirectionalDeriv (Y j) (fun u ↦ (χ u.val : ℂ)) 1 =
            (realHeckeCharacter_parameters χ w hw).exists.choose.1
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          bruhatDirectionalDeriv (Y false) (fun u ↦ (χ u.val : ℂ)) 1 = p.1 ∧
            bruhatDirectionalDeriv (Y true) (fun u ↦ (χ u.val : ℂ)) 1 =
              (p.2 : ℂ) * Complex.I := by
  let N : C𝔽 →ₜ* ℝ≥0ˣ := ⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩
  let proj : C𝔽 →ₜ* (ideleClassNorm F).ker :=
    ⟨(ContinuousMonoidHom.id C𝔽 / τ.comp N).toMonoidHom.codRestrict _ (fun x ↦ by
      change ideleClassNorm F (x / τ (ideleClassNorm F x)) = 1
      rw [map_div, hτ, div_self']),
      ((ContinuousMonoidHom.id C𝔽 / τ.comp N).continuous).subtype_mk _⟩
  have hfreq (b : LCATopologicalLie C𝔽) (χ : PontryaginDual C𝔽)
      (hχ : ∀ t : ℝ≥0ˣ, χ (τ t) = 1) (a : ℂ)
      (ha : ∀ t : ℝ, (χ (b (Multiplicative.ofAdd t)) : ℂ) = Complex.exp (a * t)) :
      bruhatDirectionalDeriv (proj.comp b) (fun u ↦ (χ u.val : ℂ)) 1 = a := by
    have hd : HasDerivAt (fun t : ℝ ↦ Complex.exp (a * t)) a 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul a).cexp
    apply (hd.congr_of_eventuallyEq (.of_forall fun t ↦ ?_)).deriv
    simp only [one_mul]
    change (χ (b _ / τ (N (b _))) : ℂ) = _
    rw [map_div, hχ, div_one, ha]
  let ι : w.Completionˣ →ₜ* C𝔽 := ⟨infiniteClassMap(w), continuous_ideleClass_ofCompletion F w⟩
  by_cases hw : w.IsReal
  · let e : ℝˣ →ₜ* w.Completionˣ :=
      ⟨Units.map (InfinitePlace.Completion.ringEquivRealOfIsReal hw).symm.toMonoidHom,
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
    let expU : Multiplicative ℝ →ₜ* ℝˣ :=
      { toFun := fun t ↦ Units.mk0 (Real.exp t.toAdd) (Real.exp_pos _).ne'
        map_one' := Units.ext Real.exp_zero
        map_mul' := fun x y ↦ Units.ext (Real.exp_add _ _)
        continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
          (Real.continuous_exp.comp continuous_toAdd) }
    let b := ι.comp (e.comp expU)
    refine ⟨fun _ ↦ proj.comp b, fun χ hχ ↦ ?_⟩
    rw [dite_eq_left hw]
    intro _
    exact hfreq b χ hχ (realHeckeCharacter_parameters χ w hw).exists.choose.1 (fun t ↦ by
      rw [show (χ (b (Multiplicative.ofAdd t)) : ℂ) = _ from
        exists_normOne_flows_archimedean_parameters_real_character w hw χ
          (expU (Multiplicative.ofAdd t))]
      simp only [show (expU (Multiplicative.ofAdd t)).val = Real.exp t from rfl,
        ite_eq_left (Real.exp_pos t), one_pow, mul_one, Real.norm_of_nonneg (Real.exp_pos t).le,
        exists_normOne_flows_archimedean_parameters_exp_cpow])
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let e : ℂˣ →ₜ* w.Completionˣ :=
      ⟨Units.map (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm.toMonoidHom,
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.continuous.units_map _⟩
    let b (d : ℂ) : Multiplicative ℝ →ₜ* ℂˣ :=
      { toFun := fun x ↦ Units.mk0 (Complex.exp ((x.toAdd : ℂ) * d)) (Complex.exp_ne_zero _)
        map_one' := Units.ext (by simp)
        map_mul' := fun x y ↦ Units.ext (by simp [add_mul, Complex.exp_add])
        continuous_toFun := Units.isEmbedding_val₀.continuous_iff.mpr
          (Complex.continuous_exp.comp
            ((Complex.continuous_ofReal.comp continuous_toAdd).mul continuous_const)) }
    let path (d : ℂ) := ι.comp (e.comp (b d))
    refine ⟨fun j ↦ cond j (proj.comp (path Complex.I)) (proj.comp (path (1 / 2))),
      fun χ hχ ↦ ?_⟩
    rw [dite_eq_right hw]
    let p := (complexHeckeCharacter_parameters χ w hc).exists.choose
    have hval (y φ : ℝ) := congrArg Inv.inv
      ((exists_normOne_flows_archimedean_parameters_polar w hc y φ).2 χ)
    have hr := hfreq (path (1 / 2)) χ hχ p.1 (fun t ↦ by
      change (χ (infiniteClassMap(w) (e (Units.mk0 (Complex.exp ((t : ℂ) * (1 / 2)))
        (Complex.exp_ne_zero _)))) : ℂ) = _
      have h := hval t 0
      simp only [Complex.ofReal_zero, zero_mul, add_zero, Complex.exp_zero, one_zpow, mul_one,
        neg_mul, Complex.exp_neg, inv_inv, div_eq_mul_inv, one_mul] at h ⊢
      exact h)
    have hi := hfreq (path Complex.I) χ hχ ((p.2 : ℂ) * Complex.I) (fun t ↦ by
      have h := hval 0 t
      simp only [Complex.ofReal_zero, zero_div, zero_add, mul_zero, Complex.exp_zero,
        one_mul, zpow_neg, inv_inv, ← Complex.exp_int_mul] at h
      exact h.trans (congrArg Complex.exp (by dsimp [p]; ring)))
    exact ⟨hr, hi⟩

open Classical in
/-- Paper: Lemma B.4.4.9, pp. 624–625. Let `τ` be a section of the norm of the idele classes.
There are finitely many
one-parameter subgroups `Y i` of the norm-one classes such that for every unitary character `χ`
trivial on the image of `τ` and every real `X`: if all frequencies
`bruhatDirectionalDeriv (Y i) χ 1` have norm at most `X`, then at every infinite place the
radial exponent of `χ` has norm at most `X` and, at a complex place, its angular weight has
absolute value at most `X`.
Reconstruction: The paper does not state this. The sums over characters of these pages need it
to pass from the frequencies of a character to its archimedean parameters. It is the private
lemma
`idelicExplicitFormula_summable_spectral_characters_archimedean` of
`AppB_AnalyticNT/Sec4b.lean`, with the character not in a subtype. -/
theorem exists_normOne_flows_archimedean_parameters (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ (n : ℕ) (Y : Fin n → LCATopologicalLie (ideleClassNorm F).ker),
      ∀ χ : PontryaginDual C𝔽, (∀ t : ℝ≥0ˣ, χ (τ t) = 1) → ∀ X : ℝ,
        (∀ i, ‖bruhatDirectionalDeriv (Y i) (fun u ↦ (χ u.val : ℂ)) 1‖ ≤ X) →
        ∀ w : InfinitePlace F, if hw : w.IsReal then
          ‖(realHeckeCharacter_parameters χ w hw).exists.choose.1‖ ≤ X
        else
          let p := (complexHeckeCharacter_parameters χ w
            (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
          ‖p.1‖ ≤ X ∧ (p.2.natAbs : ℝ) ≤ X := by
  choose Y hY using exists_normOne_flows_archimedean_parameters_place τ hτ
  let e := Fintype.equivFin (InfinitePlace F × Bool)
  refine ⟨_, fun i ↦ Y (e.symm i).1 (e.symm i).2, fun χ hχ X hX w ↦ ?_⟩
  have hX' : ∀ j, ‖bruhatDirectionalDeriv (Y w j) (fun u ↦ (χ u.val : ℂ)) 1‖ ≤ X :=
    fun j ↦ by simpa only [e.symm_apply_apply] using hX (e (w, j))
  have h := hY w χ hχ
  by_cases hw : w.IsReal
  · rw [dite_eq_left hw] at h ⊢
    rw [← h false]
    exact hX' false
  · rw [dite_eq_right hw] at h ⊢
    obtain ⟨h1, h2⟩ := h
    have h3 := hX' true
    rw [h2, norm_mul, Complex.norm_I, mul_one, Complex.norm_intCast] at h3
    refine ⟨by rw [← h1]; exact hX' false, ?_⟩
    rw [Nat.cast_natAbs]
    exact_mod_cast h3

/-- The frequency along a one-parameter subgroup of the norm-one classes, computed in the
norm-one classes or in the idele classes. -/
private theorem exists_flows_archimedean_parameters_subtype
    (Y : LCATopologicalLie (ideleClassNorm F).ker) (f : C𝔽 → ℂ) :
    bruhatDirectionalDeriv
        ((⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽).comp Y) f 1 =
      bruhatDirectionalDeriv Y (fun u ↦ f u.val) 1 := by
  change deriv (fun t : ℝ ↦ f (1 * (Y (Multiplicative.ofAdd t)).val)) 0 =
    deriv (fun t : ℝ ↦ f ((1 * Y (Multiplicative.ofAdd t) : C₁) : C𝔽)) 0
  simp only [one_mul]

open Classical in
/-- Paper: Lemma B.4.4.9, pp. 624–625. Let `τ` be a section of the norm of the idele classes.
There are finitely many one-parameter subgroups `Y i` of the idele classes, with values in the
norm-one classes, such that for every unitary character `ψ` trivial on the image of `τ` and
every real `X`: if all frequencies `bruhatDirectionalDeriv (Y i) ψ 1` have norm at most `X`,
then at every infinite place the radial exponent of `ψ` has norm at most `X` and, at a complex
place, its angular weight has absolute value at most `X`. The subgroups and the frequencies
have the form of those of `idelicExplicitFormula_normOneFourier_count`.
Reconstruction: The paper does not state this; see
`exists_normOne_flows_archimedean_parameters`, of which this is the form with the one-parameter
subgroups in the idele classes. -/
theorem exists_flows_archimedean_parameters_le (τ : ℝ≥0ˣ →ₜ* C𝔽)
    (hτ : RightInverse τ (ideleClassNorm F)) :
    ∃ (n : ℕ) (Y : Fin n → Multiplicative ℝ →ₜ* C𝔽),
      (∀ i t, Y i t ∈ (ideleClassNorm F).ker) ∧
      ∀ ψ : PontryaginDual C𝔽, (∀ t : ℝ≥0ˣ, ψ (τ t) = 1) → ∀ X : ℝ,
        (∀ i, ‖bruhatDirectionalDeriv (Y i) (fun g : C𝔽 ↦ (ψ g : ℂ)) 1‖ ≤ X) →
        ∀ w : InfinitePlace F, if hw : w.IsReal then
            ‖(realHeckeCharacter_parameters ψ w hw).exists.choose.1‖ ≤ X
          else
            let p := (complexHeckeCharacter_parameters ψ w
              (InfinitePlace.not_isReal_iff_isComplex.mp hw)).exists.choose
            ‖p.1‖ ≤ X ∧ (p.2.natAbs : ℝ) ≤ X := by
  obtain ⟨n, Y, h⟩ := exists_normOne_flows_archimedean_parameters τ hτ
  refine ⟨n, fun i ↦
    (⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩ : C₁ →ₜ* C𝔽).comp (Y i),
    fun i t ↦ (Y i t).property, fun ψ hψ X hX ↦ h ψ hψ X fun i ↦ ?_⟩
  have hi := hX i
  simp only [exists_flows_archimedean_parameters_subtype] at hi
  exact hi

end RiemannMasullo
