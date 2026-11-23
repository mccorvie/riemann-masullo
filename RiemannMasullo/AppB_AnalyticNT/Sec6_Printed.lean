module

public import Mathlib.Algebra.Field.ULift
public import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import RiemannMasullo.AppB_AnalyticNT.Sec6
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace

/-!
# Appendix B.6: statements that are false as printed

The printed claims are kept as propositions with separate refutation statements.
Nothing imports this file.
-/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped Topology

namespace RiemannMasullo

local notation "U[" F "]" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
local notation "halfPlane" => Complex.re ⁻¹' Ioi (1 : ℝ)

/-- Paper: Proposition B.6.1.1, real-zero clause, p. 636. As printed: for every
number field and continuous character, any zero of its finite Hecke L-function at
a real point in `[1/2, 1]` forces the square of the character to be trivial.
Positive meromorphic order expresses a genuine zero. The repaired
`finiteHeckeL_zeroFreeRegion` omits the real-zero clause. See ERRATA F23. -/
def Printed.finiteHeckeL_quadratic_of_real_zero : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (L : ℂ → ℂ),
    MeromorphicNFOn L univ → (∀ s : halfPlane, L s = finiteHeckeL χ s) →
      ∀ σ ∈ Icc (1 / 2 : ℝ) 1, 0 < meromorphicOrderAt L (σ : ℂ) → χ ^ 2 = 1

/-- A universe lift of the rationals is a number field. -/
private theorem finiteHeckeL_quadratic_of_real_zero_numberField.{u} :
    NumberField (ULift.{u} ℚ) := by
  let e : ULift.{u} ℚ ≃+* ℚ := ULift.ringEquiv
  have : CharZero (ULift.{u} ℚ) :=
    charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  have : FiniteDimensional ℚ (ULift.{u} ℚ) :=
    Module.Finite.of_injective e.toRatAlgEquiv.toLinearMap e.injective
  exact ⟨⟩

/-- A universe lift of the rationals has the Dedekind zeta function of the rationals. -/
private theorem finiteHeckeL_quadratic_of_real_zero_dedekindZeta.{u}
    [NumberField (ULift.{u} ℚ)] (s : ℂ) :
    dedekindZeta (ULift.{u} ℚ) s = dedekindZeta ℚ s := by
  let e : 𝓞 (ULift.{u} ℚ) ≃+* 𝓞 ℚ := RingOfIntegers.mapRingEquiv ULift.ringEquiv
  have hnorm (I : Ideal (𝓞 (ULift.{u} ℚ))) : Ideal.absNorm (I.map e) = Ideal.absNorm I := by
    rw [Ideal.absNorm_eq_natCard, Ideal.absNorm_eq_natCard]
    exact (Nat.card_congr (Ideal.quotientEquiv I (I.map e) e rfl).toEquiv).symm
  have hc (n : ℕ) : Nat.card {I : Ideal (𝓞 (ULift.{u} ℚ)) // Ideal.absNorm I = n} =
      Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.idealComapOrderIso.symm.toEquiv fun I ↦ ?_)
    change _ ↔ Ideal.absNorm (I.map e) = n
    rw [hnorm]
  change LSeries _ s = LSeries _ s
  congr 1
  funext n
  rw [hc]

/-- Over the rationals the Dedekind zeta series is the Riemann zeta function
to the right of one. -/
private theorem finiteHeckeL_quadratic_of_real_zero_rat {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta ℚ s = riemannZeta s := by
  have hc (n : ℕ) : Nat.card {I : Ideal (𝓞 ℚ) // I.absNorm = n} = 1 := by
    let : Unique {I : Ideal (𝓞 ℚ) // I.absNorm = n} :=
      { default := ⟨_, RatRingOfIntegers.absNorm_span_natCast n⟩
        uniq := fun I ↦ by
          apply Subtype.ext
          obtain ⟨m, hm⟩ := RatRingOfIntegers.exists_eq_span_natCast I.val
          have hmn : m = n := by
            simpa only [hm, RatRingOfIntegers.absNorm_span_natCast] using I.property
          simpa only [hmn] using hm }
    exact Nat.card_unique
  simpa only [dedekindZeta, hc, Nat.cast_one, Pi.one_def] using LSeries_one_eq_riemannZeta hs

/-- The Riemann zeta function is meromorphic on the plane. -/
private theorem finiteHeckeL_quadratic_of_real_zero_meromorphic :
    MeromorphicOn riemannZeta univ := by
  intro s _
  have ha := (DirichletCharacter.differentiable_LFunctionTrivChar₁ 1).analyticAt s
  have hm : MeromorphicAt (fun z : ℂ ↦ DirichletCharacter.LFunctionTrivChar₁ 1 z / (z - 1)) s :=
    ha.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt
  apply hm.congr
  filter_upwards [(eventually_cofinite_ne (1 : ℂ)).filter_mono (nhdsNE_le_cofinite s)] with z hz
  rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hz,
    mul_div_cancel_left₀ _ (sub_ne_zero.mpr hz)]
  simp [DirichletCharacter.LFunctionTrivChar]

/-- The finite L-function of the trivial character is the Dedekind zeta series. -/
private theorem finiteHeckeL_quadratic_of_real_zero_one (F : Type*) [Field F] [NumberField F]
    (s : halfPlane) : finiteHeckeL (1 : U[F]) s = dedekindZeta F s := by
  have he := completedHeckeL_one_eq_dedekindZeta (F := F) s
  rw [← heckeGammaFactor_one] at he
  exact mul_left_cancel₀ (heckeGammaFactor_ne_zero_of_re_pos (1 : U[F])
    (zero_lt_one.trans s.property)) he

/-- The norm twist evaluates to the character times a power of the idelic norm. -/
private theorem finiteHeckeL_quadratic_of_real_zero_apply (F : Type*) [Field F] [NumberField F]
    (χ : U[F]) (s : ℂ) (g : IdeleClassGroup (𝓞 F) F) :
    ideleClassNormTwist χ s g = (χ g : ℂ) * (((ideleClassNorm F g : NNReal) : ℝ) : ℂ) ^ s :=
  rfl

/-- An imaginary translation of the Euler product is the Euler product of the translated
unitary character. -/
private theorem finiteHeckeL_quadratic_of_real_zero_twist (F : Type*) [Field F] [NumberField F]
    (χ ψ : U[F]) (a : ℂ) (ha : a.re = 0)
    (hψ : ideleClassNormTwist ψ 0 = ideleClassNormTwist χ a) (s : halfPlane) :
    finiteHeckeL ψ s = finiteHeckeL χ ⟨(s : ℂ) + a, by
      change 1 < (s : ℂ).re + a.re
      rw [ha, add_zero]
      exact s.property⟩ := by
  let w : halfPlane := ⟨(s : ℂ) + a, by
    change 1 < (s : ℂ).re + a.re
    rw [ha, add_zero]
    exact s.property⟩
  apply (finiteHeckeL_hasProd ψ s).unique ((finiteHeckeL_hasProd χ w).congr_fun ?_)
  intro v
  have hval (t : (v.adicCompletion F)ˣ) :
      (ideleClassNormTwist ψ 0).restrict v t =
        (ideleClassNormTwist χ 0).restrict v t * (‖(t : v.adicCompletion F)‖ : ℂ) ^ a := by
    rw [hψ, HeckeCharacter.restrict, HeckeCharacter.restrict,
      MulChar.ofUnitHom_coe, MulChar.ofUnitHom_coe]
    simp only [MonoidHom.comp_apply, MonoidHom.coe_toHomUnits, ContinuousMonoidHom.coe_toMonoidHom,
      MonoidHom.coe_ofClass]
    rw [finiteHeckeL_quadratic_of_real_zero_apply, finiteHeckeL_quadratic_of_real_zero_apply,
      Complex.cpow_zero, mul_one, ideleClassNorm_ofAdicCompletion]
    rfl
  have hu : (ideleClassNormTwist ψ 0).IsUnramifiedAt v ↔
      (ideleClassNormTwist χ 0).IsUnramifiedAt v := by
    rw [HeckeCharacter.isUnramifiedAt_iff, HeckeCharacter.isUnramifiedAt_iff]
    apply forall_congr'
    intro t
    let u := Units.map (v.adicCompletionIntegers F).subtype.toMonoidHom t
    have hn : ‖(u : v.adicCompletion F)‖ = 1 := by
      apply Valued.toNormedField.norm_eq_one_iff.mpr
      exact IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp
        (show u ∈ (v.adicCompletionIntegers F).units from ⟨t.val.property, t.inv.property⟩)
    change (ideleClassNormTwist ψ 0).restrict v u = 1 ↔
      (ideleClassNormTwist χ 0).restrict v u = 1
    rw [hval, hn, Complex.ofReal_one, Complex.one_cpow, mul_one]
  by_cases hx : (ideleClassNormTwist χ 0).IsUnramifiedAt v
  · let val : Valuation (v.adicCompletion F) (WithZero (Multiplicative ℤ)) := Valued.v
    obtain ⟨π, hπ⟩ := val.exists_isUniformizer_of_isCyclic_of_nontrivial
    let u := Units.mk0 (π : v.adicCompletion F) hπ.ne_zero
    have hn := norm_uniformizer_adicCompletion v _ hπ
    have hq : (v.asIdeal.absNorm : ℂ) ≠ 0 := by
      exact_mod_cast (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v)).ne'
    rw [finiteHeckeEulerFactor, finiteHeckeEulerFactor, ite_eq_left hx, ite_eq_left (hu.mpr hx),
      hx.localValue_eq u hπ, (hu.mpr hx).localValue_eq u hπ, hval]
    change (1 - (_ * (‖(π : v.adicCompletion F)‖ : ℂ) ^ a) * _)⁻¹ =
      (1 - _ * _ ^ (-((s : ℂ) + a)))⁻¹
    rw [hn, Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg (Nat.cast_nonneg _) a,
      ← Complex.cpow_neg, Complex.ofReal_natCast, mul_assoc, ← Complex.cpow_add _ _ hq]
    rw [show -a + -(s : ℂ) = -((s : ℂ) + a) by ring]
  · simp [finiteHeckeEulerFactor, hx, hu.not.mpr hx]

/-- An imaginary power of the idelic norm with nonzero exponent is a unitary
character whose square is nontrivial. -/
private theorem finiteHeckeL_quadratic_of_real_zero_char (F : Type*) [Field F] [NumberField F]
    (γ : ℝ) (hγ : γ ≠ 0) :
    ∃ ψ : U[F], ψ ^ 2 ≠ 1 ∧
      ideleClassNormTwist ψ 0 = ideleClassNormTwist (1 : U[F]) (γ * Complex.I) := by
  let c := ideleClassNormTwist (1 : U[F]) (γ * Complex.I)
  have hnorm (g : IdeleClassGroup (𝓞 F) F) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ ((γ : ℂ) * Complex.I)‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  let ψ : U[F] :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hnorm g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun x y ↦ Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hc (g : IdeleClassGroup (𝓞 F) F) :
      (ψ g : ℂ) = (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ ((γ : ℂ) * Complex.I) := by
    change (1 : ℂ) * (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ ((γ : ℂ) * Complex.I) = _
    simp
  refine ⟨ψ, ?_, ?_⟩
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
    let u : Units NNReal := Units.mk0 ⟨Real.exp (Real.pi / (2 * γ)), (Real.exp_pos _).le⟩
      (by intro h; exact (Real.exp_ne_zero _) (congrArg (fun x : NNReal ↦ (x : ℝ)) h))
    obtain ⟨g, hg⟩ := hsurj u
    have hval := DFunLike.congr_fun h g
    have he : (ψ g : ℂ) ^ 2 = 1 := by
      have hv := congrArg (fun x : Circle ↦ (x : ℂ)) hval
      change ((ψ g ^ 2 : Circle) : ℂ) = ((1 : Circle) : ℂ) at hv
      simpa using hv
    rw [hc, ← Complex.cpow_nat_mul, hg] at he
    change ((Real.exp (Real.pi / (2 * γ)) : ℝ) : ℂ) ^ (2 * ((γ : ℂ) * Complex.I)) = 1 at he
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp] at he
    have hγc : (γ : ℂ) ≠ 0 := by exact_mod_cast hγ
    have hx : ((Real.pi / (2 * γ) : ℝ) : ℂ) * (2 * ((γ : ℂ) * Complex.I)) =
        Real.pi * Complex.I := by
      push_cast
      field_simp
    rw [hx, Complex.exp_pi_mul_I] at he
    norm_num at he
  · ext g
    change (c g) * (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ (0 : ℂ) = c g
    rw [Complex.cpow_zero, mul_one]

/-- The printed clause fails over a universe lift of the rationals. -/
private theorem finiteHeckeL_quadratic_of_real_zero_contra.{u}
    (h : Printed.finiteHeckeL_quadratic_of_real_zero.{u}) : False := by
  have : NumberField (ULift.{u} ℚ) := finiteHeckeL_quadratic_of_real_zero_numberField
  obtain ⟨γ, hγ, hz⟩ := HardyFirstZero.first_zero_on_line
  have hγ0 : γ ≠ 0 := by
    intro h0
    have := hγ.1
    rw [h0] at this
    norm_num at this
  obtain ⟨ψ, hψ2, hψ⟩ := finiteHeckeL_quadratic_of_real_zero_char (ULift.{u} ℚ) γ hγ0
  let b : ℂ := γ * Complex.I
  have hb : b.re = 0 := by simp [b]
  let f : ℂ → ℂ := fun s ↦ riemannZeta (s + b)
  have hfa (s : ℂ) (hs : s + b ≠ 1) : AnalyticAt ℂ f s := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | z + b ≠ 1})
      (fun z hz ↦ ((differentiableAt_riemannZeta hz).comp z
        (differentiableAt_id.add_const b)).differentiableWithinAt)
    exact (isOpen_ne_fun (continuous_id.add continuous_const) continuous_const).mem_nhds hs
  have hf : MeromorphicOn f univ := fun s _ ↦
    MeromorphicAt.comp_analyticAt (g := fun z : ℂ ↦ z + b) (x := s)
      (finiteHeckeL_quadratic_of_real_zero_meromorphic (s + b) (mem_univ _))
      (analyticAt_id.add analyticAt_const)
  let L := toMeromorphicNFOn f univ
  have hL : MeromorphicNFOn L univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have heq : ∀ s : halfPlane, L s = finiteHeckeL ψ s := by
    intro s
    have hre : 1 < ((s : ℂ) + b).re := by
      rw [Complex.add_re, hb, add_zero]
      exact s.property
    have hne : (s : ℂ) + b ≠ 1 := fun h1 ↦ by
      rw [h1] at hre
      norm_num at hre
    change toMeromorphicNFOn f univ s = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hf (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr (hfa s hne).meromorphicNFAt,
      finiteHeckeL_quadratic_of_real_zero_twist (ULift.{u} ℚ) 1 ψ b hb hψ s,
      finiteHeckeL_quadratic_of_real_zero_one]
    change riemannZeta ((s : ℂ) + b) = dedekindZeta (ULift.{u} ℚ) ((s : ℂ) + b)
    rw [finiteHeckeL_quadratic_of_real_zero_dedekindZeta,
      finiteHeckeL_quadratic_of_real_zero_rat hre]
  have hord : 0 < meromorphicOrderAt L ((1 / 2 : ℝ) : ℂ) := by
    have hne : ((1 / 2 : ℝ) : ℂ) + b ≠ 1 := fun h1 ↦ by
      have := congrArg Complex.re h1
      rw [Complex.add_re, hb, add_zero, Complex.ofReal_re, Complex.one_re] at this
      norm_num at this
    have hcongr : meromorphicOrderAt L ((1 / 2 : ℝ) : ℂ) =
        meromorphicOrderAt f ((1 / 2 : ℝ) : ℂ) :=
      meromorphicOrderAt_congr (hf.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ _))
    rw [hcongr]
    apply (tendsto_zero_iff_meromorphicOrderAt_pos (hf _ (mem_univ _))).mp
    have h0 : f ((1 / 2 : ℝ) : ℂ) = 0 := by
      change riemannZeta (((1 / 2 : ℝ) : ℂ) + γ * Complex.I) = 0
      push_cast
      exact hz
    rw [← h0]
    exact (hfa _ hne).continuousAt.continuousWithinAt
  exact hψ2 (h (ULift.{u} ℚ) ψ L hL heq (1 / 2) ⟨le_rfl, by norm_num⟩ hord)

/-- Paper: Proposition B.6.1.1, real-zero clause, p. 636. Choose a nonreal critical-line
zero `1/2 + iγ` of the Riemann zeta function by Hardy's theorem. Over the rational
field, the unitary character `χ = |·|^(iγ)` has finite L-function `ζ(s + iγ)` on `Re s > 1`.
Take its meromorphic normal form on the plane, setting the value at `1 - iγ` to zero.
At `σ = 1/2` it has positive order. The idelic norm is onto the positive reals, so `γ ≠ 0`
implies `χ ^ 2 ≠ 1`. -/
theorem Printed.finiteHeckeL_quadratic_of_real_zero_false :
    ¬ Printed.finiteHeckeL_quadratic_of_real_zero := by
  intro h
  exact finiteHeckeL_quadratic_of_real_zero_contra h

/-- Paper: Paragraph following Proposition B.6.1.1, p. 636. As printed: for every
number field and every continuous character whose square is nontrivial, the finite Hecke
L-function of its square is entire. The note after `finiteHeckeL_zeroFreeRegion`
records the shifted pole. See ERRATA F24. -/
def Printed.finiteHeckeL_sq_entire_of_not_quadratic : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]) (L : ℂ → ℂ),
    χ ^ 2 ≠ 1 → MeromorphicNFOn L univ →
      (∀ s : halfPlane, L s = finiteHeckeL (χ ^ 2) s) → Differentiable ℂ L

/-- A field isomorphic to the rationals is a number field. -/
private theorem finiteHeckeL_sq_entire_numberField (K : Type*) [Field K] (e : K ≃+* ℚ) :
    NumberField K := by
  let : CharZero K := charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  let : FiniteDimensional ℚ K := Module.Finite.of_injective e.toRatAlgEquiv.toLinearMap e.injective
  exact ⟨⟩

/-- An imaginary power of the idelic norm gives a nonquadratic character whose square
is trivial on the norm-one subgroup. -/
private theorem finiteHeckeL_sq_entire_char_exists (F : Type*) [Field F] [NumberField F] :
    ∃ χ : U[F], χ ^ 2 ≠ 1 ∧
    (χ ^ 2).toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 := by
  let c := ideleClassNormTwist (1 : U[F]) Complex.I
  have hnorm (g : IdeleClassGroup (𝓞 F) F) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos
      (NNReal.coe_pos.mpr (Units.zero_lt _)), Complex.I_re, Real.rpow_zero]
  let χ : U[F] :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hnorm g)⟩
      map_one' := Subtype.ext (map_one c)
      map_mul' := fun x y ↦ Subtype.ext (map_mul c x y)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hc (g : IdeleClassGroup (𝓞 F) F) :
      (χ g : ℂ) = (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I := by
    change (1 : ℂ) * (((↑(ideleClassNorm F g) : NNReal) : ℝ) : ℂ) ^ Complex.I = _
    simp
  refine ⟨χ, ?_, ?_⟩
  · intro h
    obtain ⟨_, _, _, _, _, _, _, _, _, hsurj, _⟩ := ideleGroup_quotient.{_, 0} F
    let u : Units NNReal := Units.mk0 ⟨Real.exp (Real.pi / 2), (Real.exp_pos _).le⟩
      (by intro h; exact (Real.exp_ne_zero _) (congrArg (fun x : NNReal ↦ (x : ℝ)) h))
    obtain ⟨g, hg⟩ := hsurj u
    have hval := DFunLike.congr_fun h g
    have he : (χ g : ℂ) ^ 2 = 1 := by
      have hv := congrArg (fun x : Circle ↦ (x : ℂ)) hval
      change ((χ g ^ 2 : Circle) : ℂ) = ((1 : Circle) : ℂ) at hv
      simpa using hv
    rw [hc, ← Complex.cpow_nat_mul, hg] at he
    change ((Real.exp (Real.pi / 2) : ℝ) : ℂ) ^ (2 * Complex.I) = 1 at he
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_ne_zero _)),
      ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp] at he
    have hx : ((Real.pi / 2 : ℝ) : ℂ) * (2 * Complex.I) = Real.pi * Complex.I := by push_cast; ring
    rw [hx, Complex.exp_pi_mul_I] at he
    norm_num at he
  · ext g
    change (χ g.1 : ℂ) ^ 2 = 1
    rw [hc]
    have hg : ideleClassNorm F g.1 = 1 := MonoidHom.mem_ker.mp g.2
    change (((↑(↑(ideleClassNorm F g.1) : NNReal) : ℝ) : ℂ) ^ Complex.I) ^ 2 = 1
    rw [hg]
    simp

/-- The completed L-function has a pole on the one-line when the character is
trivial on the norm-one subgroup, so its finite part cannot be entire. -/
private theorem finiteHeckeL_sq_entire_pole_contra (F : Type*) [Field F] [NumberField F] (ψ : U[F])
    (hψ : ψ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1)
    (L : ℂ → ℂ) (hL : Differentiable ℂ L)
    (heq : ∀ s : halfPlane, L s = finiteHeckeL ψ s) : False := by
  let P : ℂ → ℂ := fun s ↦ heckeGammaFactor ψ s * L s
  have hP : MeromorphicOn P univ := fun s _ ↦
    (meromorphic_heckeGammaFactor ψ s).mul (hL.analyticAt s).meromorphicAt
  let Q := toMeromorphicNFOn P univ
  have hQ : MeromorphicNFOn Q univ := meromorphicNFOn_toMeromorphicNFOn _ _
  have hEq : ∀ s : halfPlane, Q s = completedHeckeL ψ s := by
    intro s
    have hs : 0 < (s : ℂ).re := zero_lt_one.trans s.property
    have ha : AnalyticAt ℂ (heckeGammaFactor ψ) s := by
      apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
        (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos ψ hz).differentiableWithinAt)
      exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs
    have hPa : AnalyticAt ℂ P s := ha.mul (hL.analyticAt s)
    change toMeromorphicNFOn P univ s = _
    rw [toMeromorphicNFOn_eq_toMeromorphicNFAt hP (mem_univ _),
      toMeromorphicNFAt_eq_self.mpr hPa.meromorphicNFAt]
    change heckeGammaFactor ψ s * L s = _
    rw [heq s]
    rfl
  obtain ⟨t, ⟨_, _, hpole, _⟩, _⟩ := completedHeckeL_continuation_simplePoles ψ Q hQ hEq hψ
  let p : ℂ := 1 + Complex.I * (t : ℂ)
  have hp : 0 < p.re := by simp [p, Complex.mul_re]
  have ha : AnalyticAt ℂ (heckeGammaFactor ψ) p := by
    apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
      (fun z hz ↦ (differentiableAt_heckeGammaFactor_of_re_pos ψ hz).differentiableWithinAt)
    exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hp
  have hPa : AnalyticAt ℂ P p := ha.mul (hL.analyticAt p)
  have hord : meromorphicOrderAt Q p = meromorphicOrderAt P p :=
    meromorphicOrderAt_congr (hP.toMeromorphicNFOn_eq_self_on_nhdsNE (mem_univ p))
  have hn := hPa.meromorphicOrderAt_nonneg
  rw [← hord, hpole] at hn
  exact (not_le_of_gt (show (-1 : WithTop ℤ) < 0 by decide)) hn

/-- Paper: Paragraph following Proposition B.6.1.1, p. 636. Over the rational
field take `χ = |·|^i`. Its square is nontrivial because the idelic norm is
onto. The finite L-function of its square equals `ζ(s + 2i)` on `Re s > 1`.
Use the meromorphic normal form on the plane, setting the value at `1 - 2i` to zero.
The germ there still has a simple pole, so this continuation is not entire. -/
theorem Printed.finiteHeckeL_sq_entire_of_not_quadratic_false :
    ¬ Printed.finiteHeckeL_sq_entire_of_not_quadratic := by
  intro h
  let : Field (ULift ℚ) := (Equiv.ulift : ULift ℚ ≃ ℚ).field
  let : NumberField (ULift ℚ) :=
    finiteHeckeL_sq_entire_numberField _ (Equiv.ulift : ULift ℚ ≃ ℚ).ringEquiv
  obtain ⟨χ, hχ, hk⟩ := finiteHeckeL_sq_entire_char_exists (ULift ℚ)
  obtain ⟨L, hL, heq⟩ := finiteHeckeL_exists_continuation (χ ^ 2)
  exact finiteHeckeL_sq_entire_pole_contra (ULift ℚ) (χ ^ 2) hk L
    (h (ULift ℚ) χ L hχ hL heq) heq

/-- Paper: Lemma B.6.1.2(1), p. 637. As printed: for every number field and
continuous character trivial on the norm-one classes, after undoing its imaginary
norm twist the ideal summatory function divided by its argument tends to the
norm-one Tamagawa volume times the inverse square root of the norm of the different.
This is the asymptotic in (B.6.1.7), for the character's norm parameter.
The repaired `heckeIdealSummatory_tendsto_of_trivial_on_normOne` uses the
Dedekind zeta residue, equal to the volume alone. See ERRATA F25. -/
def Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F] (χ : U[F]),
    χ.toMonoidHom.comp (ideleClassNorm F).ker.subtype = 1 →
      ∀ t₀ : ℝ,
        ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : U[F]) (-Complex.I * t₀) →
          let d : ℝ := (differentIdeal ℤ (𝓞 F)).absNorm
          let μ := normOneIdeleClassTamagawaMeasure F
          Tendsto (fun x : ℝ ↦ heckeIdealSummatory (ideleClassNormTwist χ (Complex.I * t₀)) x / x)
            atTop (𝓝 (((Real.sqrt d)⁻¹ * μ.real univ : ℝ) : ℂ))

/-- A universe lift of `ℚ(i)` is a number field. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_numberField.{u} :
    NumberField (ULift.{u} (CyclotomicField 4 ℚ)) := by
  let e : ULift.{u} (CyclotomicField 4 ℚ) ≃+* CyclotomicField 4 ℚ := ULift.ringEquiv
  have : CharZero (ULift.{u} (CyclotomicField 4 ℚ)) :=
    charZero_of_injective_ringHom (f := e.symm.toRingHom) e.symm.injective
  have : FiniteDimensional ℚ (ULift.{u} (CyclotomicField 4 ℚ)) :=
    Module.Finite.of_injective e.toRatAlgEquiv.toLinearMap e.injective
  exact ⟨⟩

/-- A universe lift of `ℚ(i)` has degree two over `ℚ`. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_finrank.{u} :
    1 < Module.finrank ℚ (ULift.{u} (CyclotomicField 4 ℚ)) := by
  let e : ULift.{u} (CyclotomicField 4 ℚ) ≃+* CyclotomicField 4 ℚ := ULift.ringEquiv
  have h := CyclotomicField.isCyclotomicExtension 4 ℚ
  have h4 := @IsCyclotomicExtension.finrank 4 _ ℚ (CyclotomicField 4 ℚ) _ _ _ _ (by exact h)
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))
  rw [e.toRatAlgEquiv.toLinearEquiv.finrank_eq]
  have h2 : Module.finrank ℚ (CyclotomicField 4 ℚ) = Nat.totient 4 := by convert h4
  rw [h2]
  decide

/-- The norm-one Tamagawa volume equals the residue of the Dedekind zeta function. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_volume
    (F : Type*) [Field F] [NumberField F] :
    (normOneIdeleClassTamagawaMeasure F).real univ = dedekindZeta_residue F := by
  rw [Measure.real, normOneIdeleClassTamagawaMeasure_volume, dedekindZeta_residue_def]
  have := NumberField.classNumber_pos F
  have := NumberField.Units.regulator_pos F
  have := NumberField.Units.torsionOrder_pos F
  have := Int.natAbs_pos.mpr (NumberField.discr_ne_zero F)
  rw [ENNReal.toReal_ofReal (by positivity), Nat.cast_natAbs, Int.cast_abs]
  ring

/-- For a number field other than `ℚ` the printed limit differs from the residue. -/
private theorem heckeIdealSummatory_tendsto_of_trivial_on_normOne_contra.{u}
    (F : Type u) [Field F] [NumberField F] (hF : 1 < Module.finrank ℚ F)
    (h : Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne.{u}) : False := by
  have h1 : (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)).toMonoidHom.comp
      (ideleClassNorm F).ker.subtype = 1 := by
    ext; rfl
  have h0 : ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0 =
      ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
        (-Complex.I * ((0 : ℝ) : ℂ)) := by
    simp
  have hp : Tendsto (fun x : ℝ ↦ heckeIdealSummatory
        (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F))
          (Complex.I * ((0 : ℝ) : ℂ))) x / x)
      atTop (𝓝 (((Real.sqrt ((differentIdeal ℤ (𝓞 F)).absNorm : ℝ))⁻¹ *
        (normOneIdeleClassTamagawaMeasure F).real univ : ℝ) : ℂ)) := h F 1 h1 0 h0
  have hr := (heckeIdealSummatory_tendsto_of_trivial_on_normOne _ h1).2 0 h0
  have he := tendsto_nhds_unique hr hp
  rw [heckeIdealSummatory_tendsto_of_trivial_on_normOne_volume, Complex.ofReal_inj,
    NumberField.absNorm_differentIdeal F (𝓞 F)] at he
  have hpos := NumberField.dedekindZeta_residue_pos F
  have hd := NumberField.abs_discr_gt_two hF
  have hs : Real.sqrt ((discr F).natAbs : ℝ) = 1 := by
    have hm : (Real.sqrt ((discr F).natAbs : ℝ))⁻¹ * dedekindZeta_residue F =
        1 * dedekindZeta_residue F := by
      rw [one_mul]; exact he.symm
    exact inv_eq_one.mp (mul_right_cancel₀ hpos.ne' hm)
  rw [Real.sqrt_eq_one, Nat.cast_natAbs, Int.cast_abs] at hs
  have : (2 : ℝ) < |(discr F : ℝ)| := by exact_mod_cast hd
  linarith

/-- Paper: Lemma B.6.1.2(1), p. 637. Take `F = ℚ(√5)`, `χ = 1`, and
`t₀ = 0`. With `φ = (1 + √5) / 2`, the ideal-counting limit is the zeta
residue `2 log φ / √5`, equal to the norm-one volume by (A.3.2.1). The
norm of the different is five, so the display instead gives `2 log φ / 5`. -/
theorem Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne_false :
    ¬ Printed.heckeIdealSummatory_tendsto_of_trivial_on_normOne := fun h ↦
  @heckeIdealSummatory_tendsto_of_trivial_on_normOne_contra _ _
    heckeIdealSummatory_tendsto_of_trivial_on_normOne_numberField
    heckeIdealSummatory_tendsto_of_trivial_on_normOne_finrank h

end RiemannMasullo
