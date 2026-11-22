module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.AppB_AnalyticNT.Sec2
public import RiemannMasullo.AppC_LCTVS.Sec5b
import all RiemannMasullo.Ch02_AdelicTheta.Sec3
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import all RiemannMasullo.AppB_AnalyticNT.Sec2
import Mathlib.Analysis.Complex.Liouville
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Partial Euler products and local zeta residues

Masullo, §3.3 from (3.3.1.25) through §3.3.2, pp. 134–141.
The exponent variables use the normalized local absolute values.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo
set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ" => SIdeleQuotient F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "ℬ(" K ")" => SchwartzBruhat (Multiplicative K)
local notation "test(" f ")" => (fun x ↦ f (Multiplicative.ofAdd x))
local notation "circleToComplex" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ)
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "m∞(" w ")" => ((Units.map nnNormHom.toMonoidHom) ^ InfinitePlace.mult w :
  (InfinitePlace.Completion w)ˣ →* ℝ≥0ˣ)
local notation "m𝔭(" v ")" => (Units.map nnNormHom.toMonoidHom :
  (HeightOneSpectrum.adicCompletion F v)ˣ →* ℝ≥0ˣ)
local notation "h∞(" w ")" => continuous_infiniteLocalModule w
local notation "h𝔭(" v ")" => continuous_finiteLocalModule v
local notation "chartₛ(" χ ")" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ ((circleToComplex).comp χ)
local notation "emptyChart" => quasiCharacterNormTwist (G := SIdeleQuotient F ∅)
  (sIdeleQuotientNorm F ∅) (isProperMap_sIdeleQuotientNorm F ∅).continuous 1
local notation "chart∞[" w "," χ "]" =>
  quasiCharacterNormTwist m∞(w) h∞(w) ((circleToComplex).comp χ)
local notation "chart𝔭[" v "," χ "]" =>
  quasiCharacterNormTwist m𝔭(v) h𝔭(v) ((circleToComplex).comp χ)
local notation "rightHalf" => (Complex.re ⁻¹' Ioi (0 : ℝ))
local notation "vert(" σ "," t ")" => ((σ : ℂ) + (t : ℂ) * Complex.I)
local notation "q(" v ")" => (Ideal.absNorm (HeightOneSpectrum.asIdeal v))
local notation "diffExp(" v ")" => multiplicity (HeightOneSpectrum.asIdeal v) (differentIdeal ℤ (𝓞 F))
local notation "μ∞(" w ")" => infiniteLocalMultiplicativeTamagawaMeasure F w
local notation "μ𝔭(" v ")" => finiteLocalMultiplicativeTamagawaMeasure F v
local notation "ψ∞(" w ")" => (fun x ↦ adeleStandardCharacter F
  (@Pi.single _ _ _ (Classical.decEq _) w x, 0))
local notation "F∞(" w ")" => tamagawaFourier (infiniteLocalAdditiveTamagawaMeasure F w) ψ∞(w)
local notation "F𝔭(" v ")" => tamagawaFourier (finiteLocalAdditiveTamagawaMeasure F v)
  (finiteLocalStandardCharacter F v)

local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
local instance (v : Primes) : MeasurableSpace (v.adicCompletion F) := borel _
local instance (v : Primes) : MeasurableSpace (v.adicCompletion F)ˣ := borel _

local notation "realModel(" hw ")" => InfinitePlace.Completion.ringEquivRealOfIsReal hw
local notation "complexModel(" hw ")" => InfinitePlace.Completion.ringEquivComplexOfIsComplex hw
local notation "realShape[" hw "," c "," z "," a "]" => (∀ x : ℝˣ,
  c (Units.map (realModel(hw)).symm.toMonoidHom x) =
    (‖(x : ℝ)‖ : ℂ) ^ (z : ℂ) * (if 0 < (x : ℝ) then 1 else (-1 : ℂ)) ^ (a : Fin 2).val)
local notation "complexShape[" hw "," c "," z "," r "]" => (∀ x : ℂˣ,
  c (Units.map (complexModel(hw)).symm.toMonoidHom x) =
    ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ (z : ℂ) * ((x : ℂ) / (‖(x : ℂ)‖ : ℂ)) ^ (r : ℤ))
local notation "unramified[" v "," c "]" => (∀ u : (HeightOneSpectrum.adicCompletionIntegers F v)ˣ,
  c (Units.map (HeightOneSpectrum.adicCompletionIntegers F v).subtype.toMonoidHom u) = 1)

/-- Paper: Equation (3.3.1.25), p. 134. A real local quasi-character has a
unique complex radial exponent and sign parity for its Euler factor. -/
theorem realLocalEulerParameters (w : InfinitePlace F) (hw : w.IsReal)
    (c : QuasiCharacter w.Completionˣ) :
    ∃! p : ℂ × Fin 2, realShape[hw, c, p.1, p.2] := by
  let e := (realModel(hw)).symm
  let i : ℝˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.continuous.units_map _⟩
  exact existsUnique_realUnits_quasiCharacter_parameters (c.comp i)

/-- Paper: Equation (3.3.1.25), p. 134. A complex local quasi-character has a
unique exponent for the squared absolute value and a unique angular weight. -/
theorem complexLocalEulerParameters (w : InfinitePlace F) (hw : w.IsComplex)
    (c : QuasiCharacter w.Completionˣ) :
    ∃! p : ℂ × ℤ, complexShape[hw, c, p.1, p.2] := by
  let e := (complexModel(hw)).symm
  let i : ℂˣ →ₜ* w.Completionˣ := ⟨Units.map e.toMonoidHom,
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).symm.continuous.units_map _⟩
  exact existsUnique_complexUnits_quasiCharacter_parameters (c.comp i)

/-- Paper: Equation (3.3.1.25), p. 134. The infinite local Euler factor is the
real or complex gamma factor shifted by the sign parity or angular weight.
Deviation: As in §3.2.1, the complex factor uses half of Mathlib's Gammaℂ. -/
def infiniteLocalEulerFactor (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) : ℂ :=
  open Classical in
  if hw : w.IsReal then
    let p := (realLocalEulerParameters w hw c).exists.choose
    Complex.Gammaℝ (p.1 + (p.2.val : ℂ))
  else
    let p := (complexLocalEulerParameters w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) c).exists.choose
    Complex.Gammaℂ (p.1 + (p.2.natAbs : ℂ) / 2) / 2

/-- Paper: Equation (3.3.1.25), p. 134. The Euler factor of a bare norm power
at a real place is the unshifted real gamma factor. -/
theorem infiniteLocalEulerFactor_real_norm (w : InfinitePlace F) (_hw : w.IsReal) (s : ℂ) :
    infiniteLocalEulerFactor w (chart∞[w, (1 : PontryaginDual w.Completionˣ)] s) =
      Complex.Gammaℝ s := by
  have hshape : realShape[_hw, (chart∞[w, (1 : PontryaginDual w.Completionˣ)] s), s,
      (0 : Fin 2)] := by
    intro x
    have hn : ‖((realModel(_hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
      (InfinitePlace.Completion.isometryEquivRealOfIsReal _hw).symm.isometry.norm_map_of_map_zero
        (map_zero (realModel(_hw)).symm) (x : ℝ)
    change (((1 : PontryaginDual w.Completionˣ)
      (Units.map (realModel(_hw)).symm.toMonoidHom x) : Circle) : ℂ) *
      (((m∞(w) (Units.map (realModel(_hw)).symm.toMonoidHom x) : ℝ≥0) : ℝ) : ℂ) ^ s = _
    simp [InfinitePlace.mult, _hw, hn]
  have h := (realLocalEulerParameters w _hw _).unique
    (realLocalEulerParameters w _hw _).exists.choose_spec (y₂ := (s, 0)) hshape
  simp only [infiniteLocalEulerFactor, _hw, ↓reduceDIte, h, Fin.val_zero, Nat.cast_zero, add_zero]

/-- Paper: Equation (3.3.1.25), p. 134. The finite local Euler factor of an
unramified character is the reciprocal of one minus its value at a uniformizer.
A ramified character contributes one. -/
def finiteLocalEulerFactor (v : Primes) (c : QuasiCharacter (v.adicCompletion F)ˣ) : ℂ :=
  open Classical in
  if unramified[v, c] then
    let h := (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial
    (1 - c (Units.mk0 h.choose h.choose_spec.ne_zero))⁻¹
  else 1

/-- Paper: Equation (3.3.1.25), p. 134. A bare norm power over a finite local
field gives the geometric Euler factor in the right half-plane. -/
theorem finiteLocalEulerFactor_norm (v : Primes) {s : ℂ} (hs : s ∈ rightHalf) :
    finiteLocalEulerFactor v (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s) =
      (1 - (q(v) : ℂ) ^ (-s))⁻¹ := by
  have hval (g : (v.adicCompletion F)ˣ) :
      chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s g = ((‖g.val‖ : ℝ) : ℂ) ^ s := by
    change (((1 : PontryaginDual (v.adicCompletion F)ˣ) g : Circle) : ℂ) *
      (((m𝔭(v) g : ℝ≥0) : ℝ) : ℂ) ^ s = _
    rw [PontryaginDual.one_apply, Circle.coe_one, one_mul]
    rfl
  have hunr : unramified[v, chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s] := by
    intro u
    rw [hval]
    have hu : ‖(Units.map (HeightOneSpectrum.adicCompletionIntegers F v).subtype.toMonoidHom u :
        (v.adicCompletion F)ˣ).val‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
          (a := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u)).mp
          ⟨u.val.property, u.inv.property⟩)
    rw [hu, Complex.ofReal_one, Complex.one_cpow]
  unfold finiteLocalEulerFactor
  rw [if_pos hunr]
  dsimp only
  have harg : ((q(v) : ℝ) : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg (by positivity)]
    exact Real.pi_ne_zero.symm
  rw [hval, Units.val_mk0, norm_uniformizer_adicCompletion v _
    (Valued.v : Valuation (v.adicCompletion F)
      (WithZero (Multiplicative ℤ))).exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec,
    Complex.ofReal_inv, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg, Complex.ofReal_natCast]

/-- Paper: Equation (3.3.1.25), p. 134. The S-local Hecke L-function is the
product of the Euler factors of the restricted quasi-characters. -/
def sLocalHeckeL (c : QuasiCharacter Jₛ) : ℂ :=
  (∏ w : InfinitePlace F, infiniteLocalEulerFactor w (sLocalInfiniteRestriction w c)) *
    ∏ v : S, finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c)

/-- Paper: Equation (3.3.1.25), p. 134. For a bare norm power and no finite
places, the partial Euler product consists of the unshifted gamma factors. -/
theorem sLocalHeckeL_archimedean (s : ℂ) :
    sLocalHeckeL (emptyChart s) =
      Complex.Gammaℝ s ^ InfinitePlace.nrRealPlaces F *
        (Complex.Gammaℂ s / 2) ^ InfinitePlace.nrComplexPlaces F := by
  classical
  rw [sLocalHeckeL, Finset.univ_eq_attach, Finset.attach_empty, Finset.prod_empty, mul_one]
  have hfac (w : InfinitePlace F) :
      infiniteLocalEulerFactor w (sLocalInfiniteRestriction w (emptyChart s)) =
        if w.IsReal then Complex.Gammaℝ s else Complex.Gammaℂ s / 2 := by
    have hval (g : w.Completionˣ) : sLocalInfiniteRestriction w (emptyChart s) g =
        (((m∞(w) g : ℝ≥0) : ℝ) : ℂ) ^ s :=
      sLocalInfiniteRestriction_normTwist (S := ∅) w s g
    by_cases hw : w.IsReal
    · have hshape : realShape[hw, (sLocalInfiniteRestriction w (emptyChart s)), s, (0 : Fin 2)] := by
        intro x
        have hn : ‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
          (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
            (map_zero (realModel(hw)).symm) (x : ℝ)
        rw [hval]
        simp [InfinitePlace.mult, hw, hn]
      have h := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (emptyChart s))).unique
        (realLocalEulerParameters w hw _).exists.choose_spec (y₂ := (s, 0)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, ↓reduceIte, h, Fin.val_zero,
        Nat.cast_zero, add_zero]
    · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
      have hshape : complexShape[hc, (sLocalInfiniteRestriction w (emptyChart s)), s, (0 : ℤ)] := by
        intro x
        have hn : ‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
          (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
            (map_zero (complexModel(hc)).symm) (x : ℂ)
        rw [hval]
        simp [InfinitePlace.mult, hw, hn]
      have h := (complexLocalEulerParameters w hc (sLocalInfiniteRestriction w (emptyChart s))).unique
        (complexLocalEulerParameters w hc _).exists.choose_spec (y₂ := (s, 0)) hshape
      simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, ↓reduceIte, h, Int.natAbs_zero,
        Nat.cast_zero, zero_div, add_zero]
  simp_rw [hfac]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  simp_rw [InfinitePlace.not_isReal_iff_isComplex]
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]

-- TODO(paper-gap): The description after (3.3.1.25) calls local insertion
-- injective. For ℚ with only its real place, insertion kills the diagonal unit −1.

/-- Paper: Remark 3.3.1.6, p. 135. The chosen unitary base lifts to a unitary
idele class character, and the finite set of places can be enlarged to kill
the Picard group.
Deviation: Agreement is expressed through the restriction in §3.1.2. The lift
is unramified outside S because its prescribed value on the outside unit
factors is trivial. -/
theorem sLocal_character_extension (χ : PontryaginDual Jₛ) :
    ∃ (χ' : PontryaginDual C𝔽) (h : ideleClassNormTwist χ' 0 ∈ unramifiedOutside F S),
      sIdeleRestriction F S ⟨ideleClassNormTwist χ' 0, h⟩ = chartₛ(χ) 0 ∧
      ∃ T : Finset Primes, S ⊆ T ∧ Subsingleton (CommRing.Pic ((T : Set Primes).integer F)) := by
  let ψ := (circleToComplex).comp χ
  obtain ⟨c, hc⟩ := sIdeleRestriction_surjective F S ψ
  have hn (x : C𝔽) : c.val x ≠ 0 := ((Group.isUnit x).map c.val).ne_zero
  let e : PontryaginDual C𝔽 :=
    { toFun x := ⟨c.val x / (‖c.val x‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
        rw [norm_div, Complex.norm_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr (hn x))])⟩
      map_one' := Subtype.ext (by simp)
      map_mul' x y := Subtype.ext (by
        change c.val (x * y) / (‖c.val (x * y)‖ : ℂ) =
          (c.val x / (‖c.val x‖ : ℂ)) * (c.val y / (‖c.val y‖ : ℂ))
        rw [map_mul, norm_mul, Complex.ofReal_mul, div_mul_div_comm])
      continuous_toFun := (c.val.continuous.div (Complex.continuous_ofReal.comp c.val.continuous.norm)
        (fun x ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hn x)))).subtype_mk _ }
  have he (x : C𝔽) : ideleClassNormTwist e 0 x = c.val x / (‖c.val x‖ : ℂ) := by
    change (e x : ℂ) * (((ideleClassNorm F x : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) = _
    rw [Complex.cpow_zero, mul_one]
    rfl
  have hu : ideleClassNormTwist e 0 ∈ unramifiedOutside F S := by
    apply (mem_unramifiedOutside_iff F S _).mpr
    intro v hv u
    let y := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
    let x := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v y
    have hx : c.val x = 1 := (mem_unramifiedOutside_iff F S c.val).mp c.property v hv u
    change ideleClassNormTwist e 0 x = 1
    simp [he, hx]
  refine ⟨e, hu, ?_, (picard_uniformization F S).1⟩
  ext1 x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  let y := QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F) (sIdeleInsertion F S g)
  have hval : c.val y = (χ (QuotientGroup.mk g) : ℂ) := by
    have h := DFunLike.congr_fun hc (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at h
    exact h
  rw [sIdeleRestriction_mk]
  change ideleClassNormTwist e 0 y = (χ (QuotientGroup.mk g) : ℂ) * _ ^ (0 : ℂ)
  simp [he, hval]

local notation "sProdUnits" => ContinuousMulEquiv.prodUnits
  (InfiniteAdeleRing F) ((v : S) → v.val.adicCompletion F)
local notation "sInfiniteUnit(" w ", " x ")" => (sProdUnits).symm
  (ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) w x), 1)
local notation "sFiniteUnit(" v ", " x ")" => (sProdUnits).symm
  (1, ContinuousMulEquiv.piUnits.symm (@Pi.mulSingle _ _ _ (Classical.decEq _) v x))

/-- Inserting an infinite local unit through the S-ideles gives its full idele insertion. -/
private theorem sIdeleInsertion_infiniteUnit (w : InfinitePlace F) (x : w.Completionˣ) :
    sIdeleInsertion F S (sInfiniteUnit(w, x)) = IdeleGroup.ofCompletion (𝓞 F) F w x := by
  classical
  obtain ⟨ha, hf, ho⟩ := sIdeleInsertion_apply F S (sInfiniteUnit(w, x))
  apply Units.ext
  apply Prod.ext
  · rw [ha]
    funext u
    change ((Pi.mulSingle (M := fun t ↦ t.Completionˣ) w x u : u.Completionˣ) : u.Completion) =
      Pi.mulSingle (M := fun t ↦ t.Completion) w (x : w.Completion) u
    by_cases hu : u = w
    · subst u
      simp
    · simp [Pi.mulSingle_eq_of_ne hu]
  · apply RestrictedProduct.ext
    intro v
    change (sIdeleInsertion F S (sInfiniteUnit(w, x))).val.2 v = 1
    by_cases hv : v ∈ S
    · exact hf ⟨v, hv⟩
    · exact ho v hv

/-- Inserting a finite local unit through the S-ideles gives its full idele insertion. -/
private theorem sIdeleInsertion_finiteUnit (v : S) (x : (v.val.adicCompletion F)ˣ) :
    sIdeleInsertion F S (sFiniteUnit(v, x)) = IdeleGroup.ofAdicCompletion (𝓞 F) F v.val x := by
  classical
  let : DecidableEq S := Classical.decEq _
  obtain ⟨ha, hf, ho⟩ := sIdeleInsertion_apply F S (sFiniteUnit(v, x))
  apply Units.ext
  apply Prod.ext
  · exact ha
  · apply RestrictedProduct.ext
    intro u
    change (sIdeleInsertion F S (sFiniteUnit(v, x))).val.2 u =
      RestrictedProduct.mulSingle (fun w : Primes ↦ w.adicCompletionIntegers F) v.val x.val u
    by_cases hu : u = v.val
    · subst u
      rw [hf v, RestrictedProduct.mulSingle_eq_same]
      change ((Pi.mulSingle (M := fun t : S ↦ (t.val.adicCompletion F)ˣ) v x v :
        (v.val.adicCompletion F)ˣ) : v.val.adicCompletion F) = _
      rw [Pi.mulSingle_eq_same]
    · rw [RestrictedProduct.mulSingle_eq_of_ne _ _ hu]
      by_cases hm : u ∈ S
      · rw [hf ⟨u, hm⟩]
        change ((Pi.mulSingle (M := fun t : S ↦ (t.val.adicCompletion F)ˣ) v x ⟨u, hm⟩ :
          (u.adicCompletion F)ˣ) : u.adicCompletion F) = 1
        rw [Pi.mulSingle_eq_of_ne (fun e ↦ hu (congrArg Subtype.val e)), Units.val_one]
      · exact ho u hm

/-- The finite local Euler factor of a restricted global twist uses the same
ramification condition and uniformizer value as the global finite Euler factor. -/
private theorem finiteLocalEulerFactor_eq_finiteHeckeEulerFactor
    (χ' : PontryaginDual C𝔽) (v : Primes) (s : ℂ) :
    finiteLocalEulerFactor v (finitePlaceRestriction F v (ideleClassNormTwist χ' s)) =
      finiteHeckeEulerFactor χ' v s := by
  classical
  let c := finitePlaceRestriction F v (ideleClassNormTwist χ' s)
  let c₀ := finitePlaceRestriction F v (ideleClassNormTwist χ' 0)
  have htwist (x : (v.adicCompletion F)ˣ) :
      c x = c₀ x * (‖x.val‖ : ℂ) ^ s := by
    let g := IdeleClassGroup.ofAdicCompletion (𝓞 F) F v x
    change (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) * _
    rw [Complex.cpow_zero, mul_one, ideleClassNorm_ofAdicCompletion]
    rfl
  have hrestrict (x : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist χ' 0).restrict v x.val = c₀ x := by
    rw [HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    rfl
  have hunram : unramified[v, c] ↔ (ideleClassNormTwist χ' 0).IsUnramifiedAt v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    refine forall_congr' fun u ↦ ?_
    let x := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom u
    change c x = 1 ↔ (ideleClassNormTwist χ' 0).restrict v x.val = 1
    have hn : ‖x.val‖ = 1 :=
      Valued.toNormedField.norm_eq_one_iff.mpr
        ((HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one (a := x)).mp
          ⟨u.val.property, u.inv.property⟩)
    rw [htwist, hn, Complex.ofReal_one, Complex.one_cpow, mul_one, hrestrict]
  change finiteLocalEulerFactor v c = finiteHeckeEulerFactor χ' v s
  by_cases hv : (ideleClassNormTwist χ' 0).IsUnramifiedAt v
  · rw [finiteLocalEulerFactor, ite_eq_left (hunram.mpr hv), finiteHeckeEulerFactor, ite_eq_left hv]
    let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    let hπ := val.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec
    let π := Units.mk0 _ hπ.ne_zero
    change (1 - c π)⁻¹ = _
    have hn := norm_uniformizer_adicCompletion v π.val hπ
    rw [htwist, hv.localValue_eq π.val hπ, hrestrict, hn,
      Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) s,
      Complex.cpow_neg, Complex.ofReal_natCast]
  · rw [finiteLocalEulerFactor, ite_eq_right (mt hunram.mp hv), finiteHeckeEulerFactor,
      ite_eq_right hv]

/-- The product of local factors of the infinite restrictions of a global
norm twist is the global gamma factor. -/
private theorem prod_infiniteLocalEulerFactor_eq_heckeGammaFactor
    (χ' : PontryaginDual C𝔽) (s : ℂ) :
    (∏ w : InfinitePlace F,
      infiniteLocalEulerFactor w (infinitePlaceRestriction F w (ideleClassNormTwist χ' s))) =
      heckeGammaFactor χ' s := by
  classical
  unfold heckeGammaFactor
  refine Finset.prod_congr rfl fun w _ ↦ ?_
  let c := infinitePlaceRestriction F w (ideleClassNormTwist χ' s)
  let c₀ := infinitePlaceRestriction F w (ideleClassNormTwist χ' 0)
  have htwist (x : w.Completionˣ) :
      c x = c₀ x * ((‖x.val‖ ^ w.mult : ℝ) : ℂ) ^ s := by
    let g := IdeleClassGroup.ofCompletion (𝓞 F) F w x
    change (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ' g : ℂ) * (((ideleClassNorm F g : ℝ≥0) : ℝ) : ℂ) ^ (0 : ℂ) * _
    rw [Complex.cpow_zero, mul_one, ideleClassNorm_ofCompletion]
    rfl
  change infiniteLocalEulerFactor w c = _
  by_cases hw : w.IsReal
  · let a := (realHeckeCharacter_parameters χ' w hw).exists.choose
    have ha := (realHeckeCharacter_parameters χ' w hw).exists.choose_spec.2
    have hshape : realShape[hw, c, s + a.1, a.2] := by
      intro x
      have hn : ‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero (realModel(hw)).symm) (x : ℝ)
      have hx : (‖(x : ℝ)‖ : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
      rw [htwist, ha, Complex.cpow_add _ _ hx]
      change _ * ((‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s = _
      simp only [hn, InfinitePlace.mult, hw, ite_true, pow_one]
      ac_rfl
    have hp := (realLocalEulerParameters w hw c).unique
      (realLocalEulerParameters w hw c).exists.choose_spec (y₂ := (s + a.1, a.2)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hp, a]
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    let a := (complexHeckeCharacter_parameters χ' w hc).exists.choose
    have ha := (complexHeckeCharacter_parameters χ' w hc).exists.choose_spec.2
    have hshape : complexShape[hc, c, s + a.1, a.2] := by
      intro x
      have hn : ‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero (complexModel(hc)).symm) (x : ℂ)
      have hx : ((‖(x : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero))
      rw [htwist, ha, Complex.cpow_add _ _ hx]
      change _ * ((‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ ^ w.mult : ℝ) : ℂ) ^ s = _
      simp only [hn, InfinitePlace.mult, hw, ite_false]
      ac_rfl
    have hp := (complexLocalEulerParameters w hc c).unique
      (complexLocalEulerParameters w hc c).exists.choose_spec (y₂ := (s + a.1, a.2)) hshape
    simp only [infiniteLocalEulerFactor, hw, ↓reduceDIte, hp, a]

/-- Paper: Remark 3.3.1.6, p. 135. Along the component of any such lift,
the S-local product matches the selected Euler factors of the global L-function. -/
theorem sLocalHeckeL_eq_partialEulerProduct (χ : PontryaginDual Jₛ) (χ' : PontryaginDual C𝔽)
    (h : ideleClassNormTwist χ' 0 ∈ unramifiedOutside F S)
    (hχ : sIdeleRestriction F S ⟨ideleClassNormTwist χ' 0, h⟩ = chartₛ(χ) 0) (s : ℂ) :
    sLocalHeckeL (chartₛ(χ) s) =
      heckeGammaFactor χ' s * ∏ v : S, finiteHeckeEulerFactor χ' v.val s := by
  classical
  have htwist (g : (SAdeleRing F S)ˣ) :
      chartₛ(χ) s (QuotientGroup.mk g) =
        ideleClassNormTwist χ' s (QuotientGroup.mk (sIdeleInsertion F S g)) := by
    have hbase := DFunLike.congr_fun hχ (QuotientGroup.mk g)
    rw [sIdeleRestriction_mk] at hbase
    change (χ' (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ (0 : ℂ) =
      (χ (QuotientGroup.mk g) : ℂ) * _ ^ (0 : ℂ) at hbase
    simp only [Complex.cpow_zero, mul_one] at hbase
    change (χ (QuotientGroup.mk g) : ℂ) *
        (((mₛ (QuotientGroup.mk g) : ℝ≥0) : ℝ) : ℂ) ^ s =
      (χ' (QuotientGroup.mk (sIdeleInsertion F S g)) : ℂ) * _ ^ s
    rw [← hbase, sIdeleQuotientNorm_mk, ← ideleNorm_sIdeleInsertion]
    rfl
  have hinfinite (w : InfinitePlace F) : sLocalInfiniteRestriction w (chartₛ(χ) s) =
      infinitePlaceRestriction F w (ideleClassNormTwist χ' s) := by
    ext1 x
    change chartₛ(χ) s (QuotientGroup.mk (sInfiniteUnit(w, x))) =
      ideleClassNormTwist χ' s (QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 F) F w x))
    rw [htwist, sIdeleInsertion_infiniteUnit]
  have hfinite (v : S) : sLocalFiniteRestriction v (chartₛ(χ) s) =
      finitePlaceRestriction F v.val (ideleClassNormTwist χ' s) := by
    ext1 x
    change chartₛ(χ) s (QuotientGroup.mk (sFiniteUnit(v, x))) =
      ideleClassNormTwist χ' s (QuotientGroup.mk (IdeleGroup.ofAdicCompletion (𝓞 F) F v.val x))
    rw [htwist, sIdeleInsertion_finiteUnit]
  simp_rw [sLocalHeckeL, hinfinite, hfinite, prod_infiniteLocalEulerFactor_eq_heckeGammaFactor,
    finiteLocalEulerFactor_eq_finiteHeckeEulerFactor]

section StripDecay

open scoped ContDiff SchwartzMap

local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "classOf" => (QuotientGroup.mk : Iₛ → Jₛ)

local instance stripNormOneMeasurableSpace : MeasurableSpace J₁ := borel _
local notation "μJ₁" => sLocalNormOneQuotientMeasure F S
local instance stripNormOneIsHaarMeasure : Measure.IsHaarMeasure (μJ₁ : Measure J₁) :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

/-- The exponential homeomorphism from the real line to the positive units. -/
private def expUnit : ℝ ≃ₜ ℝ≥0ˣ :=
  Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
local notation "radialTheta(" τ "," ψ "," f ")" =>
  (fun x : ℝ ↦ sLocalHomogeneousAdelicTheta F S μJ₁ ψ f (classOf (τ (expUnit x))))

/-- Coercing the exponential unit to a real gives the ordinary exponential. -/
private theorem expUnit_val (x : ℝ) : ((expUnit x : ℝ≥0) : ℝ) = Real.exp x := rfl

/-- Addition of logarithmic coordinates corresponds to multiplication of units. -/
private theorem expUnit_add (x y : ℝ) : expUnit (x + y) = expUnit x * expUnit y :=
  Units.ext (NNReal.coe_inj.mp (Real.exp_add x y))

/-- The exponential of zero is the identity unit. -/
private theorem expUnit_zero : expUnit 0 = 1 :=
  Units.ext (NNReal.coe_inj.mp Real.exp_zero)

/-- In logarithmic coordinates the derivative of homogeneous theta is theta
applied to the differentiated test function. -/
private theorem radialTheta_hasDerivAt (τ : ℝ≥0ˣ →ₜ* Iₛ) (ψ : PontryaginDual J₁)
    (f : ℬ(Aₛ)) (x : ℝ) :
    HasDerivAt radialTheta(τ, ψ, f)
      (radialTheta(τ, ψ, (sAdeleDirectionalDeriv F S τ f)) x) x := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hExp : Tendsto expUnit (𝓝[≠] (0 : ℝ)) (𝓝[≠] (1 : ℝ≥0ˣ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨((expUnit).continuous.tendsto' 0 1 expUnit_zero).mono_left
      nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact fun h ↦ ht ((expUnit).injective (h.trans expUnit_zero.symm))
  let θ := radialTheta(τ, ψ, f)
  change Tendsto (fun t : ℝ ↦ t⁻¹ • (θ (x + t) - θ x)) _ _
  have hTheta : Tendsto (fun t : ℝ ↦ (θ (x + t) - θ x) / ((Real.exp t : ℂ) - 1))
      (𝓝[≠] 0) (𝓝 (radialTheta(τ, ψ, (sAdeleDirectionalDeriv F S τ f)) x)) := by
    apply ((sLocalHomogeneousAdelicTheta_directionalDeriv F S τ μJ₁ ψ f
      (τ (expUnit x))).comp hExp).congr
    intro t
    have hmul : τ (expUnit t) * τ (expUnit x) = τ (expUnit (x + t)) := by
      rw [expUnit_add, map_mul τ (expUnit x) (expUnit t), mul_comm]
    change (sLocalHomogeneousAdelicTheta F S μJ₁ ψ f (classOf (τ (expUnit t) * τ (expUnit x))) -
      θ x) / (((((expUnit t : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) - 1) = _
    exact congrArg₂ (· / ·)
      (congrArg (fun u : Iₛ ↦ sLocalHomogeneousAdelicTheta F S μJ₁ ψ f (classOf u) - θ x) hmul)
      (congrArg (fun a : ℝ ↦ (a : ℂ) - 1) (expUnit_val t))
  have hRatio : Tendsto (fun t : ℝ ↦ (t⁻¹ : ℝ) • ((Real.exp t : ℂ) - 1))
      (𝓝[≠] 0) (𝓝 1) := by
    simpa using (hasDerivAt_iff_tendsto_slope_zero.mp (Real.hasDerivAt_exp 0).ofReal_comp)
  have hprod := hRatio.mul hTheta
  rw [one_mul] at hprod
  apply hprod.congr'
  filter_upwards [self_mem_nhdsWithin (s := ({0} : Set ℝ)ᶜ) (a := 0)] with t ht
  have ht' : t ≠ 0 := ht
  have hd : (Real.exp t : ℂ) - 1 ≠ 0 := by
    exact sub_ne_zero.mpr (fun he ↦ ht' (Real.exp_injective (by rw [Real.exp_zero]; exact_mod_cast he)))
  rw [smul_mul_assoc, mul_div_left_comm, div_self hd, mul_one]

/-- Paper: Lemma 3.3.1.7(1), p. 136. Along a homomorphic section of the
S-idelic norm, homogeneous theta weighted by a complex exponential of positive
real part decays exponentially at both ends of the logarithmic axis.
The small-norm estimate uses a smaller positive weight and the large-norm
estimate uses an inverse norm power exceeding the given weight. -/
private theorem sLocalHomogeneousAdelicTheta_weighted_radial_bound (τ : ℝ≥0ˣ →ₜ* Iₛ)
    (hτ : RightInverse τ (sIdeleNorm F S)) (ψ : PontryaginDual J₁) (f : ℬ(Aₛ))
    (c : ℂ) (hc : 0 < c.re) :
    ∃ M δ : ℝ, 0 ≤ M ∧ 0 < δ ∧ ∀ x : ℝ,
      ‖Complex.exp (c * x) * radialTheta(τ, ψ, f) x‖ ≤ M * Real.exp (-δ * |x|) := by sorry

/-- Multiplying homogeneous theta in logarithmic coordinates by a positive
complex exponential gives a Schwartz function. -/
private theorem exists_schwartz_weighted_radialTheta (τ : ℝ≥0ˣ →ₜ* Iₛ)
    (hτ : RightInverse τ (sIdeleNorm F S)) (ψ : PontryaginDual J₁) (f : ℬ(Aₛ))
    (c : ℂ) (hc : 0 < c.re) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = Complex.exp (c * x) * radialTheta(τ, ψ, f) x := by
  let profile (v : ℬ(Aₛ)) (x : ℝ) := Complex.exp (c * x) * radialTheta(τ, ψ, v) x
  let D : ℬ(Aₛ) → ℬ(Aₛ) := fun v ↦ c • v + sAdeleDirectionalDeriv F S τ v
  have hd (v : ℬ(Aₛ)) (x : ℝ) : HasDerivAt (profile v) (profile (D v) x) x := by
    have he := ((Complex.ofRealCLM.hasDerivAt (x := x)).const_mul c).cexp
    let Θ : ℬ(Aₛ) →ₗ[ℂ] C(Jₛ, ℂ) := sLocalHomogeneousAdelicTheta F S μJ₁ ψ
    let u : Jₛ := classOf (τ (expUnit x))
    have hD : Θ (D v) u = c * Θ v u + Θ (sAdeleDirectionalDeriv F S τ v) u := by
      have h := congrArg (fun g : C(Jₛ, ℂ) ↦ g u)
        ((Θ.map_add (c • v) (sAdeleDirectionalDeriv F S τ v)).trans
          (congrArg (· + Θ (sAdeleDirectionalDeriv F S τ v)) (Θ.map_smul c v)))
      exact h
    apply (he.mul (radialTheta_hasDerivAt τ ψ v x)).congr_deriv
    change Complex.exp (c * x) * (c * (1 : ℂ)) * Θ v u +
      Complex.exp (c * x) * Θ (sAdeleDirectionalDeriv F S τ v) u =
      Complex.exp (c * x) * Θ (D v) u
    have hfactor (u a b : ℂ) : u * (c * 1) * a + u * b = u * (c * a + b) := by ring
    exact (hfactor _ _ _).trans (congrArg (Complex.exp (c * x) * ·) hD.symm)
  have hi (n : ℕ) : iteratedDeriv n (profile f) = profile (D^[n] f) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
      exact funext fun x ↦ (hd _ x).deriv
  have hs : ContDiff ℝ (∞ : ℕ∞ω) (profile f) := by
    apply contDiff_of_differentiable_iteratedDeriv
    intro n _
    rw [hi]
    exact fun x ↦ (hd _ x).differentiableAt
  refine ⟨⟨profile f, hs, ?_⟩, fun x ↦ rfl⟩
  intro k n
  obtain ⟨M, δ, hM, hδ, hbound⟩ := sLocalHomogeneousAdelicTheta_weighted_radial_bound τ hτ ψ (D^[n] f) c hc
  -- The exponential bound absorbs each Schwartz seminorm's polynomial weight.
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ x : ℝ, ‖x‖ ^ k * Real.exp (-δ * |x|) ≤ B := by
    let d := δ / (k + 1 : ℝ)
    have hd : 0 < d := by dsimp [d]; positivity
    refine ⟨d⁻¹ ^ k, fun x ↦ ?_⟩
    have hx : |x| ≤ d⁻¹ * Real.exp (d * |x|) := by
      rw [inv_mul_eq_div, le_div_iff₀ hd, mul_comm]
      linarith [Real.add_one_le_exp (d * |x|)]
    have he : (k : ℝ) * (d * |x|) ≤ δ * |x| := by
      rw [← mul_assoc]
      apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
      dsimp [d]
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
      linarith
    rw [Real.norm_eq_abs]
    calc
      _ ≤ (d⁻¹ * Real.exp (d * |x|)) ^ k * Real.exp (-δ * |x|) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) hx _) (Real.exp_nonneg _)
      _ = d⁻¹ ^ k * Real.exp ((k : ℝ) * (d * |x|) + -δ * |x|) := by
        rw [mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      _ ≤ d⁻¹ ^ k * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr (by linarith)) (by positivity)
      _ = _ := mul_one _
  refine ⟨M * B, fun x ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv, hi]
  calc
    _ ≤ ‖x‖ ^ k * (M * Real.exp (-δ * |x|)) :=
      mul_le_mul_of_nonneg_left (hbound x) (by positivity)
    _ = M * (‖x‖ ^ k * Real.exp (-δ * |x|)) := mul_left_comm _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hB x) hM

/-- The radial integral in logarithmic coordinates is the Mellin transform
of the weighted theta profile, with the weight subtracted from the exponent. -/
private theorem radialMellin_eq_mellin (τ : ℝ≥0ˣ →ₜ* Iₛ)
    (hτ : RightInverse τ (sIdeleNorm F S)) (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ)
    (z : ℂ) (e : ℝ)
    (hχ : ∀ t : ℝ≥0ˣ, (χ (classOf (τ t)) : ℂ) = ((((t : ℝ≥0) : ℝ) : ℂ) ^ z))
    (g : ℝ → ℂ)
    (hg : ∀ x : ℝ, g x = Complex.exp (((e : ℂ) + z) * x) *
      radialTheta(τ, (χ.comp ⟨Subgroup.subtype J₁, continuous_subtype_val⟩), f) x)
    (s : ℂ) :
    sLocalRadialMellinIntegral τ f χ s = mellin (fun t ↦ g (Real.log t)) (s - e) := by
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have hmeasure : positiveRealHaar = volume.map expUnit := by
    apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
    funext x
    apply Units.ext
    apply NNReal.eq
    exact Real.coe_toNNReal _ (Real.exp_pos x).le
  let ψ : PontryaginDual J₁ := χ.comp ⟨Subgroup.subtype J₁, continuous_subtype_val⟩
  let Θ (t : ℝ≥0ˣ) := sLocalHomogeneousAdelicTheta F S μJ₁ ψ f (classOf (τ t))
  let c (t : ℝ≥0ˣ) := chartₛ(χ) s (classOf (τ t))
  change (∫ t, Θ t * c t ∂positiveRealHaar) = _
  have hchange : (∫ t, Θ t * c t ∂positiveRealHaar) =
      ∫ x : ℝ, Θ (expUnit x) * c (expUnit x) :=
    (congrArg (fun μ : Measure ℝ≥0ˣ ↦ ∫ t, Θ t * c t ∂μ) hmeasure).trans
      (expUnit.measurableEmbedding.integral_map _)
  rw [hchange, mellin_logProfile_eq]
  apply integral_congr_ae
  filter_upwards with x
  have hpow (w : ℂ) : (Real.exp x : ℂ) ^ w = Complex.exp ((x : ℂ) * w) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  have hchart : c (expUnit x) = Complex.exp ((x : ℂ) * z + (x : ℂ) * s) := by
    let unorm (t : ℝ≥0ˣ) : ℂ := (((t : ℝ≥0) : ℝ) : ℂ)
    have hu : unorm (expUnit x) = (Real.exp x : ℂ) :=
      congrArg Complex.ofReal (expUnit_val x)
    have hm : mₛ (classOf (τ (expUnit x))) = expUnit x := hτ (expUnit x)
    calc
      c (expUnit x) = (χ (classOf (τ (expUnit x))) : ℂ) *
          unorm (mₛ (classOf (τ (expUnit x)))) ^ s := rfl
      _ = unorm (expUnit x) ^ z * unorm (expUnit x) ^ s :=
        congrArg₂ (· * ·) (hχ (expUnit x)) (congrArg (fun t ↦ unorm t ^ s) hm)
      _ = _ := by rw [hu, hpow, hpow, Complex.exp_add]
  rw [hchart]
  have hx : g x = Complex.exp (((e : ℂ) + z) * x) * Θ (expUnit x) := hg x
  rw [hx, ← mul_assoc, ← Complex.exp_add, mul_comm (Θ (expUnit x))]
  congr 2
  ring

/-- The holomorphic S-local zeta function has rapid decay uniformly on
each closed strip in the positive half-plane. -/
private theorem sLocalIdelicZFunction_heightBound (f : ℬ(Aₛ)) (χ : PontryaginDual Jₛ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (N : ℕ) (hN : 1 ≤ N) :
    ∃ C > (0 : ℝ), ∀ᶠ y : ℝ in comap abs atTop, ∀ σ ∈ Icc a b,
      ‖sLocalIdelicZFunction f (chartₛ(χ) (vert(σ, y)))‖ ≤ C / |y| ^ N := by
  let p := Units.map (adeleProjection F S).toMonoidHom
  have hp : Continuous p := (continuous_fst.prodMk (continuous_pi fun v : S ↦
    (RestrictedProduct.continuous_eval v.val).comp continuous_snd)).units_map _
  let τ : ℝ≥0ˣ →ₜ* Iₛ := ⟨p.comp (canonicalIdeleNormSection F),
    hp.comp (canonicalIdeleNormSection_continuous F)⟩
  have hτ : RightInverse τ (sIdeleNorm F S) := thetaSection_rightInverse F S
  let q : Iₛ →ₜ* Jₛ := ⟨QuotientGroup.mk' _, QuotientGroup.continuous_mk⟩
  let ψ : PontryaginDual J₁ := χ.comp ⟨Subgroup.subtype J₁, continuous_subtype_val⟩
  obtain ⟨z, ⟨hz, hχ⟩, -⟩ :=
    existsUnique_unitaryComplexPower (((circleToComplex).comp χ).comp (q.comp τ))
      (fun t ↦ Circle.norm_coe (χ (q (τ t))))
  let e := a / 2
  have he : 0 < e := half_pos ha
  obtain ⟨g, hg⟩ := exists_schwartz_weighted_radialTheta τ hτ ψ f ((e : ℂ) + z)
    (by simpa [hz] using he)
  have hweight (σ : ℝ) (hσ : σ ∈ Icc (a - e) (b - e)) :
      ∃ h : 𝓢(ℝ, ℂ), ∀ x : ℝ, h x = (Real.exp (σ * x) : ℂ) * g x := by
    have hs : 0 < (((σ + e : ℝ) : ℂ) + z).re := by
      simp only [Complex.add_re, Complex.ofReal_re, hz, add_zero]
      linarith [hσ.1]
    obtain ⟨h, hh⟩ := exists_schwartz_weighted_radialTheta τ hτ ψ f _ hs
    refine ⟨h, fun x ↦ ?_⟩
    let θ := radialTheta(τ, ψ, f) x
    calc
      h x = Complex.exp ((((σ + e : ℝ) : ℂ) + z) * x) * θ := hh x
      _ = (Real.exp (σ * x) : ℂ) * (Complex.exp (((e : ℂ) + z) * x) * θ) := by
        rw [Complex.ofReal_exp, Complex.ofReal_mul, ← mul_assoc, ← Complex.exp_add]
        congr 2
        push_cast
        ring
      _ = _ := congrArg ((Real.exp (σ * x) : ℂ) * ·) (hg x).symm
  obtain ⟨C, hC, hbound⟩ :=
    mellin_eventualHeightBound_of_weighted_schwartz g (a - e) (b - e) (by linarith) hweight N hN
  refine ⟨C, hC, hbound.mono (fun y hy σ hσ ↦ ?_)⟩
  have hs : vert(σ, y) ∈ rightHalf := by
    have hpos : 0 < σ := ha.trans_le hσ.1
    simpa [mem_preimage, mem_Ioi, Complex.mul_I_re] using hpos
  have hc : ∃ (χ' : PontryaginDual Jₛ) (s : ℂ), s ∈ rightHalf ∧
      chartₛ(χ) (vert(σ, y)) = chartₛ(χ') s := ⟨χ, _, hs, rfl⟩
  rw [sLocalIdelicZFunction_eq_integral f hc, ← sLocalThetaMellinIntegral_eq_zeta f hc,
    ← sLocalRadialMellinIntegral_eq_theta τ hτ f χ _ hs,
    radialMellin_eq_mellin τ hτ f χ z e hχ g hg]
  have hσ' : σ - e ∈ Icc (a - e) (b - e) :=
    ⟨sub_le_sub_right hσ.1 _, sub_le_sub_right hσ.2 _⟩
  have harg : vert(σ, y) - (e : ℂ) = vert((σ - e : ℝ), y) := by
    push_cast
    ring
  rw [harg]
  exact hy (σ - e) hσ'

/-- Paper: Lemma 3.3.1.7(1), p. 135. On every bounded strip in the positive
half-plane the zeta function is uniformly Schwartz in height. -/
theorem sLocalIdelicZFunction_schwartzOnStrip (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∀ k : ℕ, UniformlySchwartzOnStrip
      (iteratedDeriv k (fun s ↦ sLocalIdelicZFunction f (chartₛ(χ) s))) a b := by
  let Z (s : ℂ) := sLocalIdelicZFunction f (chartₛ(χ) s)
  have hOpen : IsOpen rightHalf := isOpen_Ioi.preimage Complex.continuous_re
  have hZ : DifferentiableOn ℂ Z rightHalf := by
    refine (sLocalThetaMellinIntegral_analyticOn f χ).differentiableOn.congr ?_
    intro s hs
    have hc : ∃ (χ' : PontryaginDual Jₛ) (w : ℂ), w ∈ rightHalf ∧
        chartₛ(χ) s = chartₛ(χ') w := ⟨χ, s, hs, rfl⟩
    exact (sLocalIdelicZFunction_eq_integral f hc).trans
      (sLocalThetaMellinIntegral_eq_zeta f hc).symm
  intro k
  refine ⟨hab, ?_, fun ε hε _ N hN ↦ ?_⟩
  · intro s hs
    have hpos : s ∈ rightHalf := ha.trans hs.1
    rw [iteratedDeriv_eq_iterate]
    exact ((hZ.analyticAt (hOpen.mem_nhds hpos)).iterated_deriv k).differentiableAt.differentiableWithinAt
  · -- The circle stays inside the wider strip and changes the height by at most one.
    let r := min (ε / 2) 1
    have hr : 0 < r := lt_min (half_pos hε) zero_lt_one
    have hrε : r ≤ ε / 2 := min_le_left _ _
    have hr1 : r ≤ 1 := min_le_right _ _
    obtain ⟨C, hC, hdecay⟩ := sLocalIdelicZFunction_heightBound f χ a b ha hab N hN
    obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp hdecay)
    refine ⟨(k.factorial : ℝ) * (2 ^ N * C) / r ^ k, by positivity, ?_⟩
    have hlarge : ∀ᶠ y : ℝ in comap abs atTop, max (T + 1) 2 ≤ |y| :=
      tendsto_comap.eventually (eventually_ge_atTop _)
    filter_upwards [hlarge] with y hy σ hσ
    let s := vert(σ, y)
    have hre : s.re = σ := by simp [s]
    have him : s.im = y := by simp [s]
    have hsub (w : ℂ) (hw : w ∈ Metric.closedBall s r) : w.re ∈ Icc a b := by
      have h := (Complex.abs_re_le_norm (w - s)).trans (mem_closedBall_iff_norm.mp hw)
      rw [Complex.sub_re, hre, abs_le] at h
      exact ⟨by linarith [hσ.1, h.1], by linarith [hσ.2, h.2]⟩
    have hdiff := hZ.diffContOnCl_ball (c := s) (R := r)
      (fun w hw ↦ ha.trans_le (hsub w hw).1)
    have hsphere (w : ℂ) (hw : w ∈ Metric.sphere s r) : ‖Z w‖ ≤ 2 ^ N * C / |y| ^ N := by
      have h := (Complex.abs_im_le_norm (w - s)).trans (mem_sphere_iff_norm.mp hw).le
      rw [Complex.sub_im, him] at h
      have hyw : |y| ≤ |w.im| + 1 := by
        have htriangle := abs_sub_abs_le_abs_sub y w.im
        rw [abs_sub_comm] at htriangle
        linarith
      have hTy : T + 1 ≤ |y| := (le_max_left _ _).trans hy
      have hy2 : 2 ≤ |y| := (le_max_right _ _).trans hy
      have hT' : T ≤ |w.im| := by linarith
      have hyw' : |y| / 2 ≤ |w.im| := by linarith
      have hypos : 0 < |y| := by linarith
      have hbound := hT |w.im| hT' w.im rfl w.re (hsub w (Metric.sphere_subset_closedBall hw))
      rw [Complex.re_add_im] at hbound
      calc
        ‖Z w‖ ≤ C / |w.im| ^ N := hbound
        _ ≤ C / (|y| / 2) ^ N := div_le_div_of_nonneg_left hC.le (by positivity)
          (pow_le_pow_left₀ (by positivity) hyw' _)
        _ = 2 ^ N * C / |y| ^ N := by rw [div_pow, div_div_eq_mul_div, mul_comm C]
    calc
      _ ≤ (k.factorial : ℝ) * (2 ^ N * C / |y| ^ N) / r ^ k :=
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le k hr hdiff hsphere
      _ = _ := by simp only [div_eq_mul_inv]; ring

end StripDecay

/-- Paper: Equation (3.3.1.26), p. 135. The normalized S-local zeta function
is the meromorphic quotient by the local Euler product.
Deviation: The quotient is put in normal form before evaluation, so that a
removable singularity takes its limiting value. -/
def sLocalNormalizedZFunction (f : ℬ(SAdeleRing F S)) (c : QuasiCharacter Jₛ) : ℂ :=
  toMeromorphicNFOn (fun s : ℂ ↦
    let c' := quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ c s
    sLocalIdelicZFunction f c' / sLocalHeckeL c') univ 0

/-- Paper: Equation (3.3.1.26), p. 135. In the positive half-plane the
normalized function is the convergent zeta integral divided by the Euler product. -/
theorem sLocalNormalizedZFunction_eq_div (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ)
    {s : ℂ} (hs : s ∈ rightHalf) :
    sLocalNormalizedZFunction f (chartₛ(χ) s) =
      sLocalIdelicZetaIntegral f (chartₛ(χ) s) / sLocalHeckeL (chartₛ(χ) s) := by sorry

/-- Paper: Equation (3.3.1.27), p. 135. The normalized zeta function has the
given Stirling growth bound uniformly on each closed positive strip.
Deviation: The real exponential uses absolute height in both directions. -/
theorem sLocalNormalizedZFunction_heightBound (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (N : ℕ) (hN : 1 ≤ N) :
    let d : ℝ := (InfinitePlace.nrRealPlaces F : ℝ) / 2 + InfinitePlace.nrComplexPlaces F
    ∃ C > (0 : ℝ), ∀ᶠ t : ℝ in comap abs atTop, ∀ σ ∈ Icc a b,
      ‖sLocalNormalizedZFunction f (chartₛ(χ) (vert(σ, t)))‖ ≤
        C * |t| ^ (-((N : ℝ) + (σ - 1 / 2) * d)) * Real.exp (Real.pi * |t| / 2 * d) :=
  by sorry

-- TODO(paper-gap): The proof's (3.3.1.34) inserts an extra ε_S in the
-- decomposition of Z_S/L_S. The estimate above uses the quotient in (3.3.1.26).
-- Footnote 2 asks for a reference for the uniform rapid decay of the finite-place quotient.

/-- Paper: Lemma 3.3.1.7(3)(a)(i)–(ii), p. 135. The infinite epsilon factor
depends on the real sign parity or the absolute complex angular weight.
Deviation: The phase is i to that power for the conjugate Fourier kernel
of App. A and D and the direction of Tate's equation used in §3.3.1. -/
def infiniteLocalEpsilonFactor (w : InfinitePlace F) (c : QuasiCharacter w.Completionˣ) : ℂ :=
  open Classical in
  if hw : w.IsReal then
    Complex.I ^ (realLocalEulerParameters w hw c).exists.choose.2.val
  else
    Complex.I ^ (complexLocalEulerParameters w
      (InfinitePlace.not_isReal_iff_isComplex.mp hw) c).exists.choose.2.natAbs

/-- Paper: Lemma 3.3.1.7(3)(a)(i), p. 135. The odd real component contributes
the constant epsilon factor i with the existing Fourier transform.
Deviation: The printed phase is conjugated. -/
theorem infiniteLocalEpsilonFactor_real_odd (w : InfinitePlace F) (hw : w.IsReal)
    (c : QuasiCharacter w.Completionˣ) (s : ℂ) (hc : realShape[hw, c, s, 1]) :
    infiniteLocalEpsilonFactor w c = Complex.I := by
  have h := (realLocalEulerParameters w hw c).unique
    (realLocalEulerParameters w hw c).exists.choose_spec (y₂ := (s, 1)) hc
  simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h, Fin.val_one, pow_one]

/-- Paper: Lemma 3.3.1.7(3)(a)(iii), pp. 135–136. The finite epsilon factor
is the local Tate factor with the two local Euler factors removed.
Deviation: Normal form retains removable values. The Tate factor uses the
standard local character, with the finite-place sign fixed in App. A. -/
def finiteLocalEpsilonFactor (v : Primes) (c : QuasiCharacter (v.adicCompletion F)ˣ) : ℂ :=
  toMeromorphicNFOn (fun s : ℂ ↦
    let c' := quasiCharacterNormTwist m𝔭(v) h𝔭(v) c s
    finiteLocalTateFactor v c' / finiteLocalEulerFactor v c' *
      finiteLocalEulerFactor v (dualQuasiCharacter m𝔭(v) h𝔭(v) c')) univ 0

/-- Paper: Equation (3.3.1.29), p. 135. On a bare norm power the finite
epsilon factor is the different norm to the exponent s minus one half. -/
theorem finiteLocalEpsilonFactor_norm (v : Primes) (s : ℂ) :
    finiteLocalEpsilonFactor v (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s) =
      ((q(v) : ℂ) ^ diffExp(v)) ^ (s - 1 / 2) := by sorry

/-- Paper: Equation (3.3.1.30), p. 136. For a ramified unitary base trivial
on the chosen uniformizer, the epsilon factor is the normalized Gauss sum
over unit representatives modulo the conductor times the indicated norm power.
Deviation: The norm power uses the product of the different and conductor.
The sum uses the existing finite standard character, including the sign in F13. -/
theorem finiteLocalEpsilonFactor_ramified (v : Primes)
    (χ : PontryaginDual (v.adicCompletion F)ˣ) (π : (v.adicCompletion F)ˣ)
    (hπ : (Valued.v : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ))).IsUniformizer (π : v.adicCompletion F)) (hχπ : χ π = 1)
    (n : ℕ) (hn : 0 < n)
    (hcond : IsLeast {j : ℕ | ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 →
      ‖u.val - 1‖ ≤ (q(v) : ℝ) ^ (-(j : ℤ)) → χ u = 1} n)
    (U : Finset ((v.adicCompletion F)ˣ)) (hU : ∀ u ∈ U, ‖u.val‖ = 1)
    (hreps : ∀ u : (v.adicCompletion F)ˣ, ‖u.val‖ = 1 →
      ∃! a : U, ‖a.val.val - u.val‖ ≤ (q(v) : ℝ) ^ (-(n : ℤ))) (s : ℂ) :
    finiteLocalEpsilonFactor v (chart𝔭[v, χ] s) =
      ((q(v) : ℂ) ^ (diffExp(v) + n)) ^ (s - 1 / 2) *
        ((q(v) : ℂ) ^ n) ^ (-(1 / 2 : ℂ)) *
        ∑ u ∈ U, (χ u : ℂ) *
          (finiteLocalStandardCharacter F v (u.val / π.val ^ (diffExp(v) + n)) : ℂ) :=
  by sorry

/-- Paper: Lemma 3.3.1.7(3)(a), p. 135. The infinite local epsilon factor
is entire in each norm-twist chart. -/
theorem infiniteLocalEpsilonFactor_entire (w : InfinitePlace F) (χ : PontryaginDual w.Completionˣ) :
    AnalyticOnNhd ℂ (infiniteLocalEpsilonFactor w ∘ chart∞[w, χ]) univ := by
  suffices h : ∀ s, infiniteLocalEpsilonFactor w (chart∞[w, χ] s) =
      infiniteLocalEpsilonFactor w (chart∞[w, χ] 0) by
    rw [show infiniteLocalEpsilonFactor w ∘ chart∞[w, χ] =
      fun _ ↦ infiniteLocalEpsilonFactor w (chart∞[w, χ] 0) from funext h]
    exact fun _ _ ↦ analyticAt_const
  intro s
  have hval (t : ℂ) (g : w.Completionˣ) : chart∞[w, χ] t g =
      (χ g : ℂ) * ((((m∞(w) g : ℝ≥0) : ℝ)) : ℂ) ^ t := rfl
  by_cases hw : w.IsReal
  · have hp := (realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose_spec
    have hshape : realShape[hw, (chart∞[w, χ] s),
        (realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose.1 + s,
        (realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose.2] := by
      intro x
      have hn : ‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero (realModel(hw)).symm) (x : ℝ)
      have h0 := hp x
      rw [hval, Complex.cpow_zero, mul_one] at h0
      have hm : (((m∞(w) (Units.map (realModel(hw)).symm.toMonoidHom x) : ℝ≥0) : ℝ)) =
          ‖(x : ℝ)‖ := by
        simp [InfinitePlace.mult, hw, hn]
      have hx : ((‖(x : ℝ)‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr x.ne_zero)
      rw [hval, h0, hm, Complex.cpow_add _ _ hx]
      ring
    have h := (realLocalEulerParameters w hw (chart∞[w, χ] s)).unique
      (realLocalEulerParameters w hw (chart∞[w, χ] s)).exists.choose_spec
      (y₂ := ((realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose.1 + s,
        (realLocalEulerParameters w hw (chart∞[w, χ] 0)).exists.choose.2)) hshape
    simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h]
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have hp := (complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose_spec
    have hshape : complexShape[hc, (chart∞[w, χ] s),
        (complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose.1 + s,
        (complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose.2] := by
      intro x
      have hn : ‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero (complexModel(hc)).symm) (x : ℂ)
      have h0 := hp x
      rw [hval, Complex.cpow_zero, mul_one] at h0
      have hm : (((m∞(w) (Units.map (complexModel(hc)).symm.toMonoidHom x) : ℝ≥0) : ℝ)) =
          ‖(x : ℂ)‖ ^ 2 := by
        simp [InfinitePlace.mult, hw, hn]
      have hx : (((‖(x : ℂ)‖ ^ 2 : ℝ)) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr (pow_ne_zero _ (norm_ne_zero_iff.mpr x.ne_zero))
      rw [hval, h0, hm, Complex.cpow_add _ _ hx]
      ring
    have h := (complexLocalEulerParameters w hc (chart∞[w, χ] s)).unique
      (complexLocalEulerParameters w hc (chart∞[w, χ] s)).exists.choose_spec
      (y₂ := ((complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose.1 + s,
        (complexLocalEulerParameters w hc (chart∞[w, χ] 0)).exists.choose.2)) hshape
    simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h]

/-- Paper: Lemma 3.3.1.7(3)(a), p. 135. The finite local epsilon factor
is entire in each norm-twist chart. -/
theorem finiteLocalEpsilonFactor_entire (v : Primes) (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    AnalyticOnNhd ℂ (finiteLocalEpsilonFactor v ∘ chart𝔭[v, χ]) univ := by sorry

/-- Paper: Equation (3.3.1.28), p. 135. The S-local epsilon factor is the
product of the epsilon factors of the restricted quasi-characters. -/
def sLocalEpsilonFactor (c : QuasiCharacter Jₛ) : ℂ :=
  (∏ w : InfinitePlace F, infiniteLocalEpsilonFactor w (sLocalInfiniteRestriction w c)) *
    ∏ v : S, finiteLocalEpsilonFactor v.val (sLocalFiniteRestriction v c)

/-- Paper: Equation (3.3.1.28), p. 135. With only archimedean places, the
trivial component has epsilon factor one. -/
theorem sLocalEpsilonFactor_archimedean_trivial (s : ℂ) :
    sLocalEpsilonFactor (emptyChart s) = 1 := by
  rw [sLocalEpsilonFactor, Finset.univ_eq_attach, Finset.attach_empty, Finset.prod_empty, mul_one]
  refine Finset.prod_eq_one fun w _ ↦ ?_
  have hval (g : w.Completionˣ) : sLocalInfiniteRestriction w (emptyChart s) g =
      (((m∞(w) g : ℝ≥0) : ℝ) : ℂ) ^ s :=
    sLocalInfiniteRestriction_normTwist (S := ∅) w s g
  by_cases hw : w.IsReal
  · have hshape : realShape[hw, (sLocalInfiniteRestriction w (emptyChart s)), s, (0 : Fin 2)] := by
      intro x
      have hn : ‖((realModel(hw)).symm (x : ℝ) : w.Completion)‖ = ‖(x : ℝ)‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hw).symm.isometry.norm_map_of_map_zero
          (map_zero (realModel(hw)).symm) (x : ℝ)
      rw [hval]
      simp [InfinitePlace.mult, hw, hn]
    have h := (realLocalEulerParameters w hw (sLocalInfiniteRestriction w (emptyChart s))).unique
      (realLocalEulerParameters w hw _).exists.choose_spec (y₂ := (s, 0)) hshape
    simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h, Fin.val_zero, pow_zero]
  · have hc : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hw
    have hshape : complexShape[hc, (sLocalInfiniteRestriction w (emptyChart s)), s, (0 : ℤ)] := by
      intro x
      have hn : ‖((complexModel(hc)).symm (x : ℂ) : w.Completion)‖ = ‖(x : ℂ)‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero (complexModel(hc)).symm) (x : ℂ)
      rw [hval]
      simp [InfinitePlace.mult, hw, hn]
    have h := (complexLocalEulerParameters w hc (sLocalInfiniteRestriction w (emptyChart s))).unique
      (complexLocalEulerParameters w hc _).exists.choose_spec (y₂ := (s, 0)) hshape
    simp only [infiniteLocalEpsilonFactor, hw, ↓reduceDIte, h, Int.natAbs_zero, pow_zero]

/-- Paper: Lemma 3.3.1.7(3)(b), p. 136. The S-local epsilon factor is entire. -/
theorem sLocalEpsilonFactor_entire (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalEpsilonFactor (chartₛ(χ) s)) univ := by sorry

/-- Paper: Lemma 3.3.1.7(3)(b), p. 136. The S-local epsilon factor is nowhere zero. -/
theorem sLocalEpsilonFactor_ne_zero (c : QuasiCharacter Jₛ) :
    sLocalEpsilonFactor c ≠ 0 := by sorry

/-- Paper: Lemma 3.3.1.7(3)(b), p. 136. The S-local epsilon factor has
modulus one on the critical line. -/
theorem sLocalEpsilonFactor_norm_criticalLine (χ : PontryaginDual Jₛ) {s : ℂ} (hs : s.re = 1 / 2) :
    ‖sLocalEpsilonFactor (chartₛ(χ) s)‖ = 1 := by sorry

/-- Paper: Equations (3.3.1.31) and (3.3.1.33), pp. 136–137. The entire
normalized zeta functions satisfy the S-local Fourier functional equation.
Deviation: The numerator on the right is the Z-function in (3.3.1.33). -/
theorem sLocalNormalizedZFunction_functionalEquation (f : ℬ(SAdeleRing F S))
    (c : QuasiCharacter Jₛ) :
    sLocalNormalizedZFunction f c =
      sLocalEpsilonFactor c * sLocalNormalizedZFunction (sAdeleSchwartzFourier f)
        (dualQuasiCharacter (G := Jₛ) mₛ hmₛ c) := by sorry

/-- Paper: Equation (3.3.1.32), p. 136. As meromorphic functions, the
correcting factor is epsilon times the Euler factor divided by its dual.
Deviation: The equality is expressed off a discrete set of exponents. -/
theorem sLocalRhoFactor_eq_epsilon_mul (χ : PontryaginDual Jₛ) :
    ∀ᶠ s : ℂ in codiscrete ℂ,
      let c := chartₛ(χ) s
      sLocalRhoFactor c = sLocalEpsilonFactor c *
        (sLocalHeckeL c / sLocalHeckeL (dualQuasiCharacter (G := Jₛ) mₛ hmₛ c)) := by sorry

/-- Twisting a point of the norm-twist chart moves along the chart. -/
private theorem sLocal_chart_twist (χ : PontryaginDual Jₛ) (s t : ℂ) :
    quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ (chartₛ(χ) s) t = chartₛ(χ) (s + t) := by
  ext1 g
  let N : ℂ := (((mₛ g : ℝ≥0) : ℝ) : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
  change (χ g : ℂ) * N ^ s * N ^ t = (χ g : ℂ) * N ^ (s + t)
  rw [Complex.cpow_add _ _ hN, mul_assoc]

/-- Duality in the norm-twist chart takes the inverse unitary character and
reflects the exponent. -/
private theorem sLocal_dual_chart (χ : PontryaginDual Jₛ) (s : ℂ) :
    dualQuasiCharacter (G := Jₛ) mₛ hmₛ (chartₛ(χ) s) = chartₛ(χ⁻¹) (1 - s) := by
  ext1 g
  let N : ℂ := (((mₛ g : ℝ≥0) : ℝ) : ℂ)
  have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
  change N * chartₛ(χ) s g⁻¹ = (χ⁻¹ g : ℂ) * N ^ (1 - s)
  rw [map_inv]
  change N * ((χ g : ℂ) * N ^ s)⁻¹ = (χ⁻¹ g : ℂ) * N ^ (1 - s)
  rw [mul_inv_rev, Complex.cpow_sub 1 s hN, Complex.cpow_one, div_eq_mul_inv,
    show ((χ⁻¹ g : Circle) : ℂ) = (χ g : ℂ)⁻¹ from rfl]
  ac_rfl

/-- The reciprocal of the S-local Euler product is entire in the norm-twist chart. -/
private theorem differentiable_inv_sLocalHeckeL (χ : PontryaginDual Jₛ) :
    Differentiable ℂ (fun s ↦ (sLocalHeckeL (chartₛ(χ) s))⁻¹) := by
  classical
  obtain ⟨χ', h, hχ, -⟩ := sLocal_character_extension χ
  simp_rw [sLocalHeckeL_eq_partialEulerProduct χ χ' h hχ, mul_inv, ← Finset.prod_inv_distrib]
  refine (differentiable_inv_heckeGammaFactor χ').mul
    (Differentiable.fun_finsetProd fun v _ ↦ ?_)
  unfold finiteHeckeEulerFactor
  split_ifs
  · simp_rw [inv_inv]
    have hq : (q(v.val) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
      ((Ideal.absNorm_eq_zero_iff).not.mpr v.val.ne_bot)
    exact (differentiable_const _).sub ((differentiable_const _).mul
      ((differentiable_neg).const_cpow (Or.inl hq)))
  · simp_rw [inv_one]
    exact differentiable_const _

/-- If a function on the plane is meromorphic with no poles, then normalizing each
of its translates and evaluating at the origin gives an entire function. -/
private theorem analyticOnNhd_toMeromorphicNFOn_translate {H : ℂ → ℂ}
    (hH : MeromorphicOn H univ) (hord : ∀ s, 0 ≤ meromorphicOrderAt H s) :
    AnalyticOnNhd ℂ (fun s ↦ toMeromorphicNFOn (fun t ↦ H (s + t)) univ 0) univ := by
  let G := toMeromorphicNFOn H univ
  have hG (s : ℂ) : AnalyticAt ℂ G s :=
    (meromorphicNFOn_toMeromorphicNFOn H univ (mem_univ s)).meromorphicOrderAt_nonneg_iff_analyticAt.mp
      (by rw [meromorphicOrderAt_toMeromorphicNFOn hH (mem_univ s)]; exact hord s)
  have heq (s : ℂ) : toMeromorphicNFOn (fun t ↦ H (s + t)) univ 0 = G s := by
    have hm : MeromorphicOn (fun t ↦ H (s + t)) univ := fun t _ ↦ by
      have := (hH (s + t) (mem_univ _)).comp_analyticAt (g := fun t ↦ s + t) (by fun_prop)
      exact this
    have hGs : AnalyticAt ℂ (fun t ↦ G (s + t)) 0 :=
      (by simpa using hG s : AnalyticAt ℂ G (s + 0)).comp (by fun_prop)
    have hnear : (fun t ↦ H (s + t)) =ᶠ[𝓝[≠] 0] fun t ↦ G (s + t) := by
      have ht : Tendsto (fun t : ℂ ↦ s + t) (𝓝[≠] 0) (𝓝[≠] s) := by
        refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
        · exact (by simpa using (continuous_const_add s).tendsto (0 : ℂ) :
            Tendsto (fun t : ℂ ↦ s + t) (𝓝 0) (𝓝 s)).mono_left nhdsWithin_le_nhds
        · filter_upwards [self_mem_nhdsWithin] with t ht
          simpa using ht
      exact ht.eventually (hH.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ s)).symm
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hm (mem_univ 0),
      (toMeromorphicNFAt_eventuallyEq_nhds_congr hnear).eq_of_nhds,
      toMeromorphicNFAt_eq_self.mpr hGs.meromorphicNFAt]
    simp only [add_zero]
  intro s _
  rw [show (fun s ↦ toMeromorphicNFOn (fun t ↦ H (s + t)) univ 0) = G from funext heq]
  exact hG s

/-- Paper: Lemma 3.3.1.7(2), p. 135. Dividing by the Euler product removes
all poles of the S-local zeta function. -/
theorem sLocalNormalizedZFunction_entire (f : ℬ(SAdeleRing F S)) (χ : PontryaginDual Jₛ) :
    AnalyticOnNhd ℂ (fun s ↦ sLocalNormalizedZFunction f (chartₛ(χ) s)) univ := by
  -- Z / L = Z · L⁻¹ with L⁻¹ entire; a pole of Z is a pole of ρ = ε · L / L̂,
  -- whose order is at most the order of the zero of L⁻¹.
  let Z : ℂ → ℂ := fun u ↦ sLocalIdelicZFunction f (chartₛ(χ) u)
  let Λ : ℂ → ℂ := fun u ↦ (sLocalHeckeL (chartₛ(χ) u))⁻¹
  let Λ' : ℂ → ℂ := fun u ↦ (sLocalHeckeL (chartₛ(χ⁻¹) (1 - u)))⁻¹
  let ε : ℂ → ℂ := fun u ↦ sLocalEpsilonFactor (chartₛ(χ) u)
  have hΛ : Differentiable ℂ Λ := differentiable_inv_sLocalHeckeL χ
  have hΛ' : Differentiable ℂ Λ' :=
    (differentiable_inv_sLocalHeckeL χ⁻¹).comp (by fun_prop)
  have hZ : MeromorphicOn Z univ := (sLocalIdelicZFunction_meromorphic f χ).meromorphicOn
  have hH : MeromorphicOn (Z * Λ) univ := fun s _ ↦
    (hZ s (mem_univ s)).mul (hΛ.analyticAt s).meromorphicAt
  have hord (s : ℂ) : 0 ≤ meromorphicOrderAt (Z * Λ) s := by
    have hΛo := (hΛ.analyticAt s).meromorphicOrderAt_nonneg
    rw [meromorphicOrderAt_mul (hZ s (mem_univ s)) (hΛ.analyticAt s).meromorphicAt]
    rcases le_or_gt 0 (meromorphicOrderAt Z s) with hz | hz
    · exact add_nonneg hz hΛo
    have hρ := (min_le_iff.mp (sLocalIdelicZFunction_poles f χ s)).resolve_left (not_le.mpr hz)
    have hρeq : (fun z ↦ sLocalRhoFactor (chartₛ(χ) z)) =ᶠ[𝓝[≠] s] ε * (Λ⁻¹ * Λ') := by
      filter_upwards [nhdsNE_le_codiscrete s (sLocalRhoFactor_eq_epsilon_mul χ)] with u hu
      simp only at hu
      simp only [Pi.mul_apply, Pi.inv_apply, ε, Λ, Λ', inv_inv, hu, div_eq_mul_inv,
        sLocal_dual_chart]
    have hε := ((sLocalEpsilonFactor_entire χ) s (mem_univ s))
    rw [meromorphicOrderAt_congr hρeq, meromorphicOrderAt_mul hε.meromorphicAt
      ((hΛ.analyticAt s).meromorphicAt.inv.mul (hΛ'.analyticAt s).meromorphicAt),
      meromorphicOrderAt_mul (hΛ.analyticAt s).meromorphicAt.inv (hΛ'.analyticAt s).meromorphicAt,
      meromorphicOrderAt_inv] at hρ
    have hεo := hε.meromorphicOrderAt_nonneg
    have hΛ'o := (hΛ'.analyticAt s).meromorphicOrderAt_nonneg
    generalize meromorphicOrderAt Z s = a at *
    generalize meromorphicOrderAt Λ s = l at *
    generalize meromorphicOrderAt ε s = e at *
    generalize meromorphicOrderAt Λ' s = l' at *
    induction l using WithTop.recTopCoe with
    | top => simp
    | coe n =>
      induction a using WithTop.recTopCoe with
      | top => exact absurd hz (not_lt.mpr le_top)
      | coe a =>
        induction e using WithTop.recTopCoe with
        | top => simp at hρ
        | coe e =>
          induction l' using WithTop.recTopCoe with
          | top => simp at hρ
          | coe l' =>
            rw [← WithTop.LinearOrderedAddCommGroup.coe_neg] at hρ
            norm_cast at *
            omega
  have hfun : (fun s ↦ sLocalNormalizedZFunction f (chartₛ(χ) s)) =
      fun s ↦ toMeromorphicNFOn (fun t ↦ (Z * Λ) (s + t)) univ 0 := by
    funext s
    simp only [sLocalNormalizedZFunction, sLocal_chart_twist, Pi.mul_apply, Z, Λ, div_eq_mul_inv]
  rw [hfun]
  exact analyticOnNhd_toMeromorphicNFOn_translate hH hord

/-- Paper: Remark 3.3.1.8, p. 136. At each infinite place the additive
Tamagawa measure is self-dual for the restricted standard character. The finite
case is already stated as finiteLocalAdditiveTamagawaMeasure_selfDual. -/
theorem infiniteLocalAdditiveTamagawaMeasure_selfDual (w : InfinitePlace F) :
    IsTamagawaSelfDual (infiniteLocalAdditiveTamagawaMeasure F w) ψ∞(w) := by sorry


/-! ## Local zeta functions and their poles -/

/-- Paper: Equation (3.3.2.1), p. 137. The archimedean zeta integral is
absolutely convergent on the positive half-plane. -/
theorem infiniteLocalIdelicZetaIntegral_integrable (w : InfinitePlace F) (f : ℬ(w.Completion))
    (χ : PontryaginDual w.Completionˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    Integrable (fun g : w.Completionˣ ↦ test(f) g.val * chart∞[w, χ] s g) μ∞(w) := by
  let K := w.Completion
  have hσ : 0 < s.re := hs
  -- Measure the test function through the isometric embedding into the complex numbers.
  let ι := InfinitePlace.Completion.extensionEmbedding w
  have hι : Isometry ι := InfinitePlace.Completion.isometry_extensionEmbedding w
  have hιn (x : K) : ‖ι x‖ = ‖x‖ := hι.norm_map_of_map_zero (map_zero ι) x
  let m : Multiplicative K →* Multiplicative ℂ := ι.toAddMonoidHom.toMultiplicative
  have hm : Continuous m := continuous_ofAdd.comp (hι.continuous.comp continuous_toAdd)
  -- Compact subgroups of the completion are trivial, so every good subgroup is in the kernel.
  have hk (a : BruhatStructuralPair (Multiplicative K)) : OrderDual.ofDual a.val.2 ≤ m.ker := by
    let k := OrderDual.ofDual a.val.2
    have hkc := isCompact_lcaDualAnnihilator (lcaAnnihilator k) a.property.2.2.1.2.1
    rw [lcaDualAnnihilator_annihilator k a.property.2.2.1.1] at hkc
    obtain ⟨B, hB⟩ := hkc.exists_bound_of_continuousOn (continuous_toAdd.comp hm).continuousOn
    intro x hx
    rw [MonoidHom.mem_ker]
    by_contra h
    have hy : 0 < ‖(m x).toAdd‖ := norm_pos_iff.mpr (fun h0 ↦ h (toAdd_eq_zero.mp h0))
    obtain ⟨n, hn⟩ := exists_nat_gt (B / ‖(m x).toAdd‖)
    have hn' := hB (x ^ n) (k.pow_mem hx n)
    change ‖(m (x ^ n)).toAdd‖ ≤ B at hn'
    rw [map_pow, toAdd_pow, RCLike.norm_nsmul ℝ, nsmul_eq_mul] at hn'
    exact (not_lt_of_ge hn') ((div_lt_iff₀ hy).mp hn)
  obtain ⟨-, -, -, hdecay⟩ := schwartzBruhat_exists_coordinate_bounds
    (G := Multiplicative K) (T := PUnit.{1}) (fun _ ↦ PUnit.unit) (fun x ↦ ‖(m x).toAdd‖)
    (fun _ ↦ norm_nonneg _) (fun _ ↦ ⟨univ, isCompact_univ, fun _ _ ↦ mem_univ _⟩)
    (fun a e st N ↦ stage_exists_decay a e st N m hm (hk a)) f
  -- A power of the norm larger than the exponent controls the growth of the character.
  obtain ⟨k, hkσ⟩ := exists_nat_gt (2 * s.re)
  have hwk : (w.mult : ℝ) * s.re < k := by
    have hmult : (w.mult : ℝ) ≤ 2 := by
      by_cases h : w.IsReal
      · simp [h.mult_eq_one]
      · simp [(InfinitePlace.not_isReal_iff_isComplex.mp h).mult_eq_two]
    exact (mul_le_mul_of_nonneg_right hmult hσ.le).trans_lt hkσ
  obtain ⟨B₀, hB₀, hb₀⟩ := hdecay 0
  obtain ⟨B₁, hB₁, hb₁⟩ := hdecay k
  have hBd (x : K) : ‖f (Multiplicative.ofAdd x)‖ * (max 1 ‖x‖) ^ k ≤ max B₀ B₁ := by
    have hmx : ‖(m (Multiplicative.ofAdd x)).toAdd‖ = ‖x‖ := hιn x
    rcases le_total ‖x‖ 1 with hx | hx
    · have h := hb₀ (Multiplicative.ofAdd x)
      rw [pow_zero, mul_one] at h
      rw [max_eq_left hx, one_pow, mul_one]
      exact h.trans (le_max_left _ _)
    · have h := hb₁ (Multiplicative.ofAdd x)
      rw [hmx] at h
      rw [max_eq_right hx]
      exact h.trans (le_max_right _ _)
  have : BorelSpace K := ⟨rfl⟩
  have : BorelSpace Kˣ := borelSpace_units_of_continuousInv₀ K
  have ha := infiniteLocalTamagawa_integrable_norm_rpow w hσ k hwk
  refine (ha.2.const_mul (max B₀ B₁)).mono' ?_ (ae_of_all _ fun g ↦ ?_)
  · have hf : Continuous fun g : Kˣ ↦ f (Multiplicative.ofAdd g.val) :=
      (schwartzBruhat_continuous (G := Multiplicative K) f).comp
        (continuous_ofAdd.comp Units.continuous_val)
    exact (hf.mul (chart∞[w, χ] s).continuous).aestronglyMeasurable
  · have hchart : ‖chart∞[w, χ] s g‖ = ‖(g : K)‖ ^ ((w.mult : ℝ) * s.re) := by
      change ‖(χ g : ℂ) * ((((m∞(w) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ s‖ = _
      rw [norm_mul, Circle.norm_coe, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
      have hval : (((m∞(w) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) = ‖(g : K)‖ ^ w.mult := by
        simp [MonoidHom.pow_apply, Units.val_pow_eq_pow_val]
      rw [hval, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    rw [norm_mul, hchart]
    change ‖f (Multiplicative.ofAdd (g : K))‖ * ‖(g : K)‖ ^ ((w.mult : ℝ) * s.re) ≤
      max B₀ B₁ * (‖(g : K)‖ ^ ((w.mult : ℝ) * s.re) / (max 1 ‖(g : K)‖) ^ k)
    have hD : 0 < (max 1 ‖(g : K)‖) ^ k := by positivity
    rw [← mul_div_assoc, le_div_iff₀ hD, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (hBd _) (by positivity)

/-- Paper: Equation (3.3.2.1), p. 137. The finite local zeta integral is
absolutely convergent on the positive half-plane. -/
theorem finiteLocalIdelicZetaIntegral_integrable (v : Primes) (f : ℬ(v.adicCompletion F))
    (χ : PontryaginDual (v.adicCompletion F)ˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    Integrable (fun g : (v.adicCompletion F)ˣ ↦ test(f) g.val * chart𝔭[v, χ] s g) μ𝔭(v) := by
  let K := v.adicCompletion F
  have : ProperSpace K := properSpace_adicCompletion v
  have hσ : 0 < s.re := hs
  -- The test function is bounded and vanishes off a compact set.
  have hstage (a : BruhatStructuralPair (Multiplicative K)) :
      ∃ C : Set K, IsCompact C ∧ ∀ x ∈ a.val.1, Multiplicative.toAdd x ∈ C := by
    obtain ⟨V, _, hV, hgen⟩ := a.property.2.1
    have hc : Continuous fun x : a.val.1 ↦ Multiplicative.toAdd (x : Multiplicative K) :=
      continuous_toAdd.comp continuous_subtype_val
    obtain ⟨r, hr⟩ := hV.exists_bound_of_continuousOn hc.continuousOn
    let ρ := max r 0
    let H : Subgroup (Multiplicative K) :=
      { carrier := {x | ‖Multiplicative.toAdd x‖ ≤ ρ}
        one_mem' := by simp [ρ]
        mul_mem' := fun hx hy ↦
          (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
        inv_mem' := fun {x} hx ↦ by
          change ‖Multiplicative.toAdd x⁻¹‖ ≤ ρ
          rw [toAdd_inv, norm_neg]
          exact hx }
    have hle : Subgroup.closure V ≤ H.comap a.val.1.subtype :=
      (Subgroup.closure_le _).2 fun x hx ↦ (hr x hx).trans (le_max_left _ _)
    rw [hgen] at hle
    refine ⟨Metric.closedBall 0 ρ, isCompact_closedBall _ _, fun x hx ↦ ?_⟩
    have h := Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top (x := (⟨x, hx⟩ : a.val.1))))
    change ‖Multiplicative.toAdd x‖ ≤ ρ at h
    rwa [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨C, hC, hsupp, hbd⟩ := schwartzBruhat_exists_coordinate_bounds
    (G := Multiplicative K) (fun x ↦ Multiplicative.toAdd x)
    (fun x ↦ ‖((1 : Multiplicative K →* Multiplicative ℝ) x).toAdd‖) (fun _ ↦ norm_nonneg _)
    hstage (fun a e st N ↦ stage_exists_decay a e st N 1 continuous_const (by simp)) f
  obtain ⟨B, hB, hB'⟩ := hbd 0
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn continuous_norm.continuousOn
  -- Dominate by a multiple of the truncated norm power.
  have : BorelSpace Kˣ := ⟨rfl⟩
  have hb := finiteLocalTamagawa_integrable_norm_rpow v hσ R
  refine (hb.2.const_mul B).mono' ?_ (ae_of_all _ fun g ↦ ?_)
  · have hf : Continuous fun g : Kˣ ↦ f (Multiplicative.ofAdd g.val) :=
      (schwartzBruhat_continuous (G := Multiplicative K) f).comp
        (continuous_ofAdd.comp Units.continuous_val)
    exact (hf.mul (chart𝔭[v, χ] s).continuous).aestronglyMeasurable
  · have hchart : ‖chart𝔭[v, χ] s g‖ = ‖(g : K)‖ ^ s.re := by
      change ‖(χ g : ℂ) * ((((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ s‖ = _
      rw [norm_mul, Circle.norm_coe, one_mul,
        Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
      rfl
    rw [norm_mul, hchart]
    change ‖f (Multiplicative.ofAdd (g : K))‖ * ‖(g : K)‖ ^ s.re ≤ _
    by_cases hg : (g : K) ∈ C
    · have hRg : ‖(g : K)‖ ≤ R := by simpa using hR _ hg
      rw [indicator_of_mem (show g ∈ {u : Kˣ | ‖(u : K)‖ ≤ R} from hRg)]
      have h := hB' (Multiplicative.ofAdd (g : K))
      rw [pow_zero, mul_one] at h
      exact mul_le_mul_of_nonneg_right h (by positivity)
    · have h0 : f (Multiplicative.ofAdd (g : K)) = 0 := hsupp _ hg
      rw [h0, norm_zero, zero_mul]
      exact mul_nonneg hB (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)

local notation "normBand[" m "," n "]" =>
  {g | (((m g : ℝ≥0) : ℝ)) ∈ Icc (n + 1 : ℝ)⁻¹ (n + 1)}

/-- Paper: Equation (3.3.2.1), p. 137. Norm-band truncations of the
archimedean zeta integral converge uniformly on compact positive exponent sets.
Deviation: Uniformity is stated on compact subsets of the convergence domain. -/
theorem infiniteLocalIdelicZetaIntegral_tendstoUniformlyOn (w : InfinitePlace F)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (K : Set ℂ)
    (hK : IsCompact K) (hKpos : K ⊆ rightHalf) :
    TendstoUniformlyOn (fun (n : ℕ) (s : ℂ) ↦
      ∫ g in normBand[m∞(w), n], test(f) g.val * chart∞[w, χ] s g ∂μ∞(w))
      (fun s ↦ localIdelicZetaIntegral μ∞(w) test(f) (chart∞[w, χ] s)) atTop K := by sorry

/-- Paper: Equation (3.3.2.1), p. 137. Norm-band truncations of the
finite local zeta integral converge uniformly on compact positive exponent sets.
Deviation: Uniformity is stated on compact subsets of the convergence domain. -/
theorem finiteLocalIdelicZetaIntegral_tendstoUniformlyOn (v : Primes)
    (f : ℬ(v.adicCompletion F)) (χ : PontryaginDual (v.adicCompletion F)ˣ) (K : Set ℂ)
    (hK : IsCompact K) (hKpos : K ⊆ rightHalf) :
    TendstoUniformlyOn (fun (n : ℕ) (s : ℂ) ↦
      ∫ g in normBand[m𝔭(v), n], test(f) g.val * chart𝔭[v, χ] s g ∂μ𝔭(v))
      (fun s ↦ localIdelicZetaIntegral μ𝔭(v) test(f) (chart𝔭[v, χ] s)) atTop K := by
  let L := v.adicCompletion F
  have : ProperSpace L := properSpace_adicCompletion v
  have : BorelSpace Lˣ := ⟨rfl⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact tendstoUniformlyOn_empty
  -- The real parts of the exponents lie in a compact interval of positive numbers.
  obtain ⟨s₁, hs₁, hmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
  obtain ⟨s₂, -, hmax⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
  let a := s₁.re
  let b := s₂.re
  have ha : 0 < a := hKpos hs₁
  have hb : 0 < b := ha.trans_le (hmax hs₁)
  -- The test function is bounded and vanishes outside a ball.
  have hstage (p : BruhatStructuralPair (Multiplicative L)) :
      ∃ C : Set L, IsCompact C ∧ ∀ x ∈ p.val.1, Multiplicative.toAdd x ∈ C := by
    obtain ⟨V, _, hV, hgen⟩ := p.property.2.1
    have hc : Continuous fun x : p.val.1 ↦ Multiplicative.toAdd (x : Multiplicative L) :=
      continuous_toAdd.comp continuous_subtype_val
    obtain ⟨r, hr⟩ := hV.exists_bound_of_continuousOn hc.continuousOn
    let ρ := max r 0
    let H : Subgroup (Multiplicative L) :=
      { carrier := {x | ‖Multiplicative.toAdd x‖ ≤ ρ}
        one_mem' := by simp [ρ]
        mul_mem' := fun hx hy ↦
          (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)
        inv_mem' := fun {x} hx ↦ by
          change ‖Multiplicative.toAdd x⁻¹‖ ≤ ρ
          rw [toAdd_inv, norm_neg]
          exact hx }
    have hle : Subgroup.closure V ≤ H.comap p.val.1.subtype :=
      (Subgroup.closure_le _).2 fun x hx ↦ (hr x hx).trans (le_max_left _ _)
    rw [hgen] at hle
    refine ⟨Metric.closedBall 0 ρ, isCompact_closedBall _ _, fun x hx ↦ ?_⟩
    have h := Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_top (x := (⟨x, hx⟩ : p.val.1))))
    change ‖Multiplicative.toAdd x‖ ≤ ρ at h
    rwa [Metric.mem_closedBall, dist_zero_right]
  obtain ⟨C, hC, hsupp, hbd⟩ := schwartzBruhat_exists_coordinate_bounds
    (G := Multiplicative L) (fun x ↦ Multiplicative.toAdd x)
    (fun x ↦ ‖((1 : Multiplicative L →* Multiplicative ℝ) x).toAdd‖) (fun _ ↦ norm_nonneg _)
    hstage (fun p e st N ↦ stage_exists_decay p e st N 1 continuous_const (by simp)) f
  obtain ⟨B, hB, hB'⟩ := hbd 0
  obtain ⟨R, hR⟩ := hC.exists_bound_of_continuousOn continuous_norm.continuousOn
  -- A majorant that works for every exponent in the compact set.
  let ind (σ : ℝ) := {u : Lˣ | ‖(u : L)‖ ≤ R}.indicator (fun u ↦ ‖(u : L)‖ ^ σ)
  let M : Lˣ → ℝ := fun u ↦ B * (ind a u + ind b u)
  have hM : Integrable M μ𝔭(v) :=
    ((finiteLocalTamagawa_integrable_norm_rpow v ha R).2.add
      (finiteLocalTamagawa_integrable_norm_rpow v hb R).2).const_mul B
  have hchart (s : ℂ) (g : Lˣ) : ‖chart𝔭[v, χ] s g‖ = ‖(g : L)‖ ^ s.re := by
    change ‖(χ g : ℂ) * ((((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) : ℂ) ^ s‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    rfl
  have hdom (s : ℂ) (hs : s ∈ K) (g : Lˣ) :
      ‖test(f) g.val * chart𝔭[v, χ] s g‖ ≤ M g := by
    rw [norm_mul, hchart]
    change ‖f (Multiplicative.ofAdd (g : L))‖ * ‖(g : L)‖ ^ s.re ≤ M g
    by_cases hg : (g : L) ∈ C
    · have hRg : ‖(g : L)‖ ≤ R := by simpa using hR _ hg
      have hmem : g ∈ {u : Lˣ | ‖(u : L)‖ ≤ R} := hRg
      have hpos : 0 < ‖(g : L)‖ := norm_pos_iff.mpr g.ne_zero
      have hpow : ‖(g : L)‖ ^ s.re ≤ ind a g + ind b g := by
        simp only [ind, indicator_of_mem hmem]
        rcases le_total ‖(g : L)‖ 1 with h1 | h1
        · exact (Real.rpow_le_rpow_of_exponent_ge hpos h1 (hmin hs)).trans
            (le_add_of_nonneg_right (by positivity))
        · exact (Real.rpow_le_rpow_of_exponent_le h1 (hmax hs)).trans
            (le_add_of_nonneg_left (by positivity))
      have h := hB' (Multiplicative.ofAdd (g : L))
      rw [pow_zero, mul_one] at h
      exact mul_le_mul h hpow (by positivity) hB
    · have h0 : f (Multiplicative.ofAdd (g : L)) = 0 := hsupp _ hg
      rw [h0, norm_zero, zero_mul]
      exact mul_nonneg hB (add_nonneg (Set.indicator_nonneg (fun _ _ ↦ by positivity) _)
        (Set.indicator_nonneg (fun _ _ ↦ by positivity) _))
  -- The bands are measurable, increase, and exhaust the units.
  let band (n : ℕ) : Set Lˣ := normBand[m𝔭(v), n]
  have hcont : Continuous fun g : Lˣ ↦ (((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (continuous_finiteLocalModule v))
  have hbandm (n : ℕ) : MeasurableSet (band n) := hcont.measurable measurableSet_Icc
  have hmono : Monotone band := by
    intro n k hnk g hg
    have h : (n + 1 : ℝ) ≤ k + 1 := by exact_mod_cast Nat.succ_le_succ hnk
    exact ⟨(inv_anti₀ (by positivity) h).trans hg.1, hg.2.trans h⟩
  have hunion : (⋃ n, band n) = univ := by
    refine eq_univ_of_forall fun g ↦ mem_iUnion.mpr ?_
    have hpos : 0 < (((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    obtain ⟨n, hn⟩ := exists_nat_ge (max (((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ)
      ((((m𝔭(v) g : ℝ≥0ˣ) : ℝ≥0) : ℝ))⁻¹)
    refine ⟨n, ?_, ?_⟩
    · rw [inv_le_comm₀ (by positivity) hpos]
      exact (le_max_right _ _).trans (hn.trans (by linarith))
    · exact (le_max_left _ _).trans (hn.trans (by linarith))
  -- The tails of the majorant tend to zero.
  have htail : Tendsto (fun n ↦ ∫ g in (band n)ᶜ, M g ∂μ𝔭(v)) atTop (𝓝 0) := by
    have h := tendsto_setIntegral_of_monotone (μ := μ𝔭(v)) hbandm hmono
      (by rw [hunion]; exact hM.integrableOn)
    rw [hunion, Measure.restrict_univ] at h
    have heq (n : ℕ) : ∫ g in (band n)ᶜ, M g ∂μ𝔭(v) =
        ∫ g, M g ∂μ𝔭(v) - ∫ g in band n, M g ∂μ𝔭(v) := by
      rw [← integral_add_compl (hbandm n) hM, add_sub_cancel_left]
    simp_rw [heq]
    simpa using (tendsto_const_nhds (x := ∫ g, M g ∂μ𝔭(v))).sub h
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_order.1 htail).2 ε hε] with n hn s hs
  have hint := finiteLocalIdelicZetaIntegral_integrable v f χ (hKpos hs)
  rw [dist_eq_norm, localIdelicZetaIntegral, ← integral_add_compl (hbandm n) hint,
    add_sub_cancel_left]
  refine lt_of_le_of_lt (norm_integral_le_of_norm_le hM.integrableOn
    (ae_of_all _ fun g ↦ hdom s hs g)) hn

/-- Paper: §3.3.2, p. 137. The archimedean integral (3.3.2.1) has a unique
meromorphic continuation, in normal form in every norm-twist chart. -/
theorem infiniteLocalIdelicZFunction_existsUnique (w : InfinitePlace F) (f : ℬ(w.Completion)) :
    ∃! Z : QuasiCharacter w.Completionˣ → ℂ, ∀ χ : PontryaginDual w.Completionˣ,
      MeromorphicNFOn (Z ∘ chart∞[w, χ]) univ ∧
        EqOn (Z ∘ chart∞[w, χ]) (fun s ↦ localIdelicZetaIntegral μ∞(w) test(f) (chart∞[w, χ] s))
          rightHalf := by sorry

/-- Paper: §3.3.2, p. 137. The archimedean Z-function is the meromorphic
continuation of the local integral. -/
def infiniteLocalIdelicZFunction (w : InfinitePlace F) (f : ℬ(w.Completion)) :
    QuasiCharacter w.Completionˣ → ℂ :=
  (infiniteLocalIdelicZFunction_existsUnique w f).exists.choose

/-- Paper: Equation (3.3.2.1), p. 137. In the half-plane of convergence the
archimedean Z-function gives the integral using the multiplicative Tamagawa measure. -/
theorem infiniteLocalIdelicZFunction_eq_integral (w : InfinitePlace F) (f : ℬ(w.Completion))
    (χ : PontryaginDual w.Completionˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    infiniteLocalIdelicZFunction w f (chart∞[w, χ] s) =
      localIdelicZetaIntegral μ∞(w) test(f) (chart∞[w, χ] s) :=
  ((infiniteLocalIdelicZFunction_existsUnique w f).exists.choose_spec χ).2 hs

/-- Paper: §3.3.2, p. 137. The finite local integral (3.3.2.1) has a unique
meromorphic continuation, in normal form in every norm-twist chart. -/
theorem finiteLocalIdelicZFunction_existsUnique (v : Primes) (f : ℬ(v.adicCompletion F)) :
    ∃! Z : QuasiCharacter (v.adicCompletion F)ˣ → ℂ, ∀ χ : PontryaginDual (v.adicCompletion F)ˣ,
      MeromorphicNFOn (Z ∘ chart𝔭[v, χ]) univ ∧
        EqOn (Z ∘ chart𝔭[v, χ]) (fun s ↦ localIdelicZetaIntegral μ𝔭(v) test(f) (chart𝔭[v, χ] s))
          rightHalf := by sorry

/-- Paper: §3.3.2, p. 137. The finite local Z-function is the meromorphic
continuation of the local integral. -/
def finiteLocalIdelicZFunction (v : Primes) (f : ℬ(v.adicCompletion F)) :
    QuasiCharacter (v.adicCompletion F)ˣ → ℂ :=
  (finiteLocalIdelicZFunction_existsUnique v f).exists.choose

/-- Paper: Equation (3.3.2.1), p. 137. In the half-plane of convergence the
finite local Z-function gives the integral using the multiplicative Tamagawa measure. -/
theorem finiteLocalIdelicZFunction_eq_integral (v : Primes) (f : ℬ(v.adicCompletion F))
    (χ : PontryaginDual (v.adicCompletion F)ˣ) {s : ℂ} (hs : s ∈ rightHalf) :
    finiteLocalIdelicZFunction v f (chart𝔭[v, χ] s) =
      localIdelicZetaIntegral μ𝔭(v) test(f) (chart𝔭[v, χ] s) :=
  ((finiteLocalIdelicZFunction_existsUnique v f).exists.choose_spec χ).2 hs

/-- Paper: §3.3.2, p. 137. In each archimedean chart the local zeta function
is meromorphic with values in the strong dual of the test space.
Deviation: Agreement with scalar normal form is required off the
distributional poles, where evaluation on a test function is regular. -/
theorem infiniteLocalIdelicZFunction_distribution (w : InfinitePlace F)
    (χ : PontryaginDual w.Completionˣ) :
    let poles := {s : ℂ | ∃ f : ℬ(w.Completion),
      meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s < 0}
    ∃ Z : ℂ → StrongDual ℂ (ℬ(w.Completion)), IsVectorMeromorphicOn Z univ poles ∧
      ∀ s ∉ poles, ∀ f, Z s f = infiniteLocalIdelicZFunction w f (chart∞[w, χ] s) := by sorry

/-- Paper: §3.3.2, p. 137. In each finite-place chart the local zeta function
is meromorphic with values in the strong dual of the test space.
Deviation: Agreement with scalar normal form is required off the
distributional poles. -/
theorem finiteLocalIdelicZFunction_distribution (v : Primes)
    (χ : PontryaginDual (v.adicCompletion F)ˣ) :
    let poles := {s : ℂ | chart𝔭[v, χ] s = 1}
    ∃ Z : ℂ → StrongDual ℂ (ℬ(v.adicCompletion F)), IsVectorMeromorphicOn Z univ poles ∧
      ∀ s ∉ poles, ∀ f, Z s f = finiteLocalIdelicZFunction v f (chart𝔭[v, χ] s) := by sorry

/-- Paper: Lemma 3.3.2.1(1)(1), p. 138. In the pure sign-parity chart, each
scalar zeta function has at most simple poles. The exponents at which some
test function gives a pole are the nonpositive integers of that parity.
Deviation: Tests against Schwartz–Bruhat functions specify the distributional pole. -/
theorem infiniteLocalIdelicZFunction_real_poles (w : InfinitePlace F) (hw : w.IsReal)
    (χ : PontryaginDual w.Completionˣ) (a : Fin 2)
    (hχ : realShape[hw, ((circleToComplex).comp χ), 0, a]) (s : ℂ) :
    (∀ f : ℬ(w.Completion),
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s) ∧
    ((∃ f : ℬ(w.Completion),
      meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s = -1) ↔
      ∃ k : ℕ, s = -((2 * k + a.val : ℕ) : ℂ)) := by sorry

/-- Paper: Lemma 3.3.2.1(1)(2), p. 138. In the pure angular-weight chart,
each scalar zeta function has at most simple poles. The exponents at which
some test function gives a pole are minus half the absolute weight minus a natural number.
Deviation: Tests against Schwartz–Bruhat functions specify the distributional pole. -/
theorem infiniteLocalIdelicZFunction_complex_poles (w : InfinitePlace F) (hw : w.IsComplex)
    (χ : PontryaginDual w.Completionˣ) (r : ℤ)
    (hχ : complexShape[hw, ((circleToComplex).comp χ), 0, r]) (s : ℂ) :
    (∀ f : ℬ(w.Completion),
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s) ∧
    ((∃ f : ℬ(w.Completion),
      meromorphicOrderAt (infiniteLocalIdelicZFunction w f ∘ chart∞[w, χ]) s = -1) ↔
      ∃ m : ℕ, s = -(r.natAbs : ℂ) / 2 - m) := by sorry

-- TODO(paper-gap): The right side of (3.3.2.13) has the opposite sign from
-- its gamma quotient. The residue of that quotient in (3.3.2.16) needs +i.
-- In (3.3.2.14) and (3.3.2.17) the conjugate Fourier kernel gives +i to
-- the absolute angular weight. In (3.3.2.21) the proof needs m ≥ 0.
-- The residue formulas below use ordinary Taylor coefficients.

/-- Paper: Lemma 3.3.2.1(2)(1), p. 138. At a real pole, the residue applied
to a test function is twice the Taylor coefficient of the corresponding degree.
Deviation: This evaluates the residue directly on the test function. In the
paper's scaled differential notation the odd coefficient has phase +i. -/
theorem infiniteLocalIdelicZFunction_real_residue (w : InfinitePlace F) (hw : w.IsReal)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (a : Fin 2)
    (hχ : realShape[hw, ((circleToComplex).comp χ), 0, a]) (k : ℕ) :
    let n := 2 * k + a.val
    let s₀ : ℂ := -(n : ℂ)
    Tendsto (fun s : ℂ ↦ (s - s₀) * infiniteLocalIdelicZFunction w f (chart∞[w, χ] s))
      (𝓝[≠] s₀) (𝓝 (2 * iteratedDeriv n (fun x : ℝ ↦ test(f) ((realModel(hw)).symm x)) 0 /
        (n.factorial : ℂ))) := by sorry

/-- Paper: Lemma 3.3.2.1(2)(2), p. 139. The z-Wirtinger derivative differentiates
in the two real coordinate directions with coefficients 1/2 and −i/2.
Deviation: The scaling by 1/(2πi) is absorbed into the residue formula. -/
def wirtingerDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I) / 2

/-- Paper: Lemma 3.3.2.1(2)(2), p. 139. The conjugate-Wirtinger derivative
uses coefficients 1/2 and i/2 in the real coordinate directions.
Deviation: The scaling by 1/(2πi) is absorbed into the residue formula. -/
def wirtingerConjDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I) / 2

/-- Paper: Lemma 3.3.2.1(2)(2), p. 139. The Wirtinger derivatives distinguish
the coordinate function from its conjugate. -/
theorem wirtingerDeriv_id_conj (z : ℂ) :
    wirtingerDeriv id z = 1 ∧ wirtingerDeriv star z = 0 ∧
      wirtingerConjDeriv id z = 0 ∧ wirtingerConjDeriv star z = 1 := by
  have hconj : fderiv ℝ (⇑(starRingEnd ℂ)) z = (Complex.conjLIE.toContinuousLinearMap) := by
    have hfun : (⇑Complex.conjLIE : ℂ → ℂ) = (⇑(starRingEnd ℂ) : ℂ → ℂ) := by
      funext w
      exact Complex.conjLIE_apply w
    rw [← hfun]
    exact Complex.conjLIE.toContinuousLinearMap.fderiv
  simp [wirtingerDeriv, wirtingerConjDeriv, hconj, Complex.conjLIE_apply]

/-- Paper: Lemma 3.3.2.1(2)(2), pp. 138–139. At a complex pole the residue
is 2π times the Taylor coefficient of angular weight opposite to the character.
Deviation: This uses unscaled Wirtinger derivatives on the test function,
absorbing the phase and normalization into the Taylor coefficient. -/
theorem infiniteLocalIdelicZFunction_complex_residue (w : InfinitePlace F) (hw : w.IsComplex)
    (f : ℬ(w.Completion)) (χ : PontryaginDual w.Completionˣ) (r : ℤ)
    (hχ : complexShape[hw, ((circleToComplex).comp χ), 0, r]) (m : ℕ) :
    let s₀ : ℂ := -(r.natAbs : ℂ) / 2 - m
    let a := m + (-r).toNat
    let b := m + r.toNat
    let g : ℂ → ℂ := fun z ↦ test(f) ((complexModel(hw)).symm z)
    Tendsto (fun s : ℂ ↦ (s - s₀) * infiniteLocalIdelicZFunction w f (chart∞[w, χ] s))
      (𝓝[≠] s₀) (𝓝 (2 * (Real.pi : ℂ) *
        ((wirtingerConjDeriv^[b]) ((wirtingerDeriv^[a]) g)) 0 /
        ((a.factorial : ℂ) * (b.factorial : ℂ)))) := by sorry

/-- Paper: Equation (3.3.2.11), p. 139. The archimedean local functional
equation holds between meromorphic continuations with the standard Fourier transform.
Deviation: Equality is expressed off a discrete set of exponents. -/
theorem infiniteLocalIdelicZFunction_functionalEquation (w : InfinitePlace F) (f : ℬ(w.Completion)) :
    ∃ fHat : ℬ(w.Completion), test(fHat) = F∞(w) test(f) ∧
      ∀ χ : PontryaginDual w.Completionˣ, ∀ᶠ s : ℂ in codiscrete ℂ,
        let c := chart∞[w, χ] s
        infiniteLocalIdelicZFunction w f c = infiniteLocalTateFactor w c *
          infiniteLocalIdelicZFunction w fHat (dualQuasiCharacter m∞(w) h∞(w) c) := by sorry

/-- Paper: Equation (3.3.2.11), p. 139. The finite-place local functional
equation holds between meromorphic continuations with the standard Fourier transform.
Deviation: Equality is expressed off a discrete set of exponents. -/
theorem finiteLocalIdelicZFunction_functionalEquation (v : Primes) (f : ℬ(v.adicCompletion F)) :
    ∃ fHat : ℬ(v.adicCompletion F), test(fHat) = F𝔭(v) test(f) ∧
      ∀ χ : PontryaginDual (v.adicCompletion F)ˣ, ∀ᶠ s : ℂ in codiscrete ℂ,
        let c := chart𝔭[v, χ] s
        finiteLocalIdelicZFunction v f c = finiteLocalTateFactor v c *
          finiteLocalIdelicZFunction v fHat (dualQuasiCharacter m𝔭(v) h𝔭(v) c) := by sorry

/-- Paper: Lemma 3.3.2.2, p. 141. Each scalar finite local zeta function
has at most simple poles. A pole occurs for some test function exactly over
the trivial quasi-character, including its periodic lifts in the exponent plane.
Deviation: Tests against Schwartz–Bruhat functions specify the distributional pole. -/
theorem finiteLocalIdelicZFunction_poles (v : Primes)
    (χ : PontryaginDual (v.adicCompletion F)ˣ) (s : ℂ) :
    (∀ f : ℬ(v.adicCompletion F),
      (-1 : WithTop ℤ) ≤ meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) s) ∧
    ((∃ f : ℬ(v.adicCompletion F),
      meromorphicOrderAt (finiteLocalIdelicZFunction v f ∘ chart𝔭[v, χ]) s = -1) ↔
      chart𝔭[v, χ] s = 1) := by sorry

-- TODO(paper-gap): In (3.3.2.23) the indicator of ℤₚˣ would have nonzero
-- residue, but its trivial-component zeta integral is identically 1.
-- The measure relation used under (3.3.2.25) omits the finite-place factor
-- q/(q−1) of Lemma A.3.2.3.

/-- Paper: Equation (3.3.2.23), p. 141. The residue at the trivial character
is evaluation at zero times the multiplicative mass of the integer units
divided by log of the residue field size.
Deviation: Fourier inversion yields f(0). The factor 1−q⁻¹ cancels against
the weighted measure factor in Lemma A.3.2.3. -/
theorem finiteLocalIdelicZFunction_residue (v : Primes) (f : ℬ(v.adicCompletion F)) :
    Tendsto (fun s : ℂ ↦ s * finiteLocalIdelicZFunction v f
      (chart𝔭[v, (1 : PontryaginDual (v.adicCompletion F)ˣ)] s)) (𝓝[≠] 0)
      (𝓝 (((μ𝔭(v) (v.adicCompletionIntegers F).units).toReal : ℂ) /
        (Real.log (q(v) : ℝ) : ℂ) * test(f) 0)) := by sorry

end RiemannMasullo
