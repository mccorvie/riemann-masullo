module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec2
public import RiemannMasullo.Ch11_ShellStructure.Sec1b
import RiemannMasullo.Ch02_AdelicTheta.Sec2a
import all RiemannMasullo.Ch03_IdelicZeta.Sec3
import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.Gaussian

/-!
# Printed outside-unit product claims in §11.1.2

The corresponding idele test and theta function are in `Sec1b.lean`.
-/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped BigOperators Classical NNReal NumberField.AdeleRing nonZeroDivisors

namespace RiemannMasullo

local notation "V[" F "]" => HeightOneSpectrum (𝓞 F)
local notation "I[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ(" A ")" => SchwartzBruhat (Multiplicative A)
local notation "classOf[" F "]" => QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F)

/-- Paper: Theorem 11.1.2.1(3), proof, p. 483. As printed: replacing the
integer indicator at every finite place outside S by the integer-unit
indicator gives a Schwartz–Bruhat function on the additive adeles. The
local test has the tensor form and the two polar vanishing conditions from
p. 482. The definition `sLocalCarvingIdeleTest` uses the product on the
ideles (ERRATA F204). -/
def Printed.sLocalCarvingOutsideUnits_schwartzBruhat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ f : sAdelePolarSubspace F S,
      (∃ (arch : ℬ(InfiniteAdeleRing F))
         (fv : (v : S) → ℬ(v.val.adicCompletion F)),
        ∀ x : SAdeleRing F S, f.val (Multiplicative.ofAdd x) =
          arch (Multiplicative.ofAdd x.1) * ∏ v : S, fv v (Multiplicative.ofAdd (x.2 v))) →
      ∃ h : ℬ(𝔸[F]), ∀ x : 𝔸[F],
        h (Multiplicative.ofAdd x) =
          {y : 𝔸[F] | ∀ v ∉ S, Valued.v (y.2 v) = 1}.indicator
            (fun y ↦ f.val (Multiplicative.ofAdd (adeleProjection F S y))) x

/-- Trivial Picard group of ℤ as the S-integers of ℚ for `S = ∅`. -/
private theorem sec1b_rat_empty_trivialPic :
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 ℚ) ((∅ : Finset V[ℚ]) : Set V[ℚ]) ℚ)) := by
  rw [Finset.coe_empty, integer_empty]
  let e := (Algebra.botEquivOfInjective (IsFractionRing.injective (𝓞 ℚ) ℚ)).toRingEquiv
  let i := Rat.ringOfIntegersEquiv.symm.trans e.symm
  let := IsPrincipalIdealRing.of_surjective i i.surjective
  infer_instance

/-- The trivial character is unramified outside `S = ∅`. -/
private theorem sec1b_rat_one_unramified :
    ideleClassNormTwist (1 : PontryaginDual C[ℚ]) 0 ∈ unramifiedOutside ℚ ∅ := by
  have h1 : ideleClassNormTwist (1 : PontryaginDual C[ℚ]) 0 = 1 := by
    ext g
    change (1 : ℂ) * (((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ (0 : ℂ) = 1
    simp
  rw [h1]
  exact (mem_unramifiedOutside_iff ℚ ∅ 1).mpr (fun _ _ _ ↦ rfl)

/-- An odd real Schwartz test on `SAdeleRing ℚ ∅` factoring through `InfiniteAdeleRing ℚ`,
with zero value and zero Fourier value at zero, and `exp(-1)` at `1`. -/
private theorem sec1b_exists_odd_test :
    ∃ (arch : ℬ(InfiniteAdeleRing ℚ)) (f : sAdelePolarSubspace ℚ ∅),
      (∀ x : SAdeleRing ℚ ∅, f.val (Multiplicative.ofAdd x) = arch (Multiplicative.ofAdd x.1)) ∧
      f.val (Multiplicative.ofAdd 1) = (Real.exp (-1) : ℂ) := by
  let g0 : SchwartzMap ℝ ℝ := SchwartzMap.gaussian 1 zero_lt_one
  let g : SchwartzMap ℝ ℂ := SchwartzMap.postcompCLM Complex.ofRealCLM g0
  let b : SchwartzMap ℝ ℂ := SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) g
  have hb : ∀ x : ℝ, b x = (x : ℂ) * (Real.exp (-(x ^ 2)) : ℂ) := by
    intro x
    change SchwartzMap.smulLeftCLM ℂ (fun x : ℝ ↦ (x : ℂ)) g x = _
    rw [SchwartzMap.smulLeftCLM_apply_apply Complex.hasTemperateGrowth_ofReal]
    simp [g, g0, SchwartzMap.postcompCLM_apply, SchwartzMap.gaussian_apply, smul_eq_mul,
      Real.norm_eq_abs, sq_abs]
  with_reducible refine realSchwartzBruhat_equiv.elim fun T hT ↦ ?_
  let realEquiv := InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
  let realIso := InfinitePlace.Completion.isometryEquivRealOfIsReal Rat.isReal_infinitePlace
  let : Unique (InfinitePlace ℚ) := ⟨⟨Rat.infinitePlace⟩, fun _ ↦ Subsingleton.elim _ _⟩
  let eInfHomeo : InfiniteAdeleRing ℚ ≃ₜ ℝ :=
    (Homeomorph.piUnique fun w : InfinitePlace ℚ ↦ w.Completion).trans realIso.toHomeomorph
  let eArch : Multiplicative (InfiniteAdeleRing ℚ) ≃ₜ* Multiplicative ℝ :=
    { toEquiv :=
        { toFun := fun x ↦ Multiplicative.ofAdd (realEquiv (x.toAdd Rat.infinitePlace))
          invFun := fun y ↦ Multiplicative.ofAdd (eInfHomeo.symm y.toAdd)
          left_inv := fun x ↦ by
            apply congrArg Multiplicative.ofAdd
            exact eInfHomeo.symm_apply_apply x.toAdd
          right_inv := fun y ↦ by
            apply congrArg Multiplicative.ofAdd
            exact eInfHomeo.apply_symm_apply y.toAdd }
      map_mul' := fun x y ↦ congrArg Multiplicative.ofAdd (map_add realEquiv _ _)
      continuous_toFun := eInfHomeo.continuous
      continuous_invFun := eInfHomeo.symm.continuous }
  have : T2Space (Multiplicative (InfiniteAdeleRing ℚ)) := eArch.isEmbedding.t2Space
  have : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing ℚ)) :=
    eArch.isOpenEmbedding.locallyCompactSpace
  have : T2Space (Multiplicative ℝ) := inferInstanceAs (T2Space ℝ)
  have : LocallyCompactSpace (Multiplicative ℝ) := inferInstanceAs (LocallyCompactSpace ℝ)
  let arch : ℬ(InfiniteAdeleRing ℚ) :=
    ⟨(T b).val ∘ eArch, schwartzBruhat_mem_comp_equiv eArch (T b).property⟩
  have harch : ∀ x : InfiniteAdeleRing ℚ,
      arch (Multiplicative.ofAdd x) = b (realEquiv (x Rat.infinitePlace)) := fun x ↦ by
    change (T b) (Multiplicative.ofAdd (realEquiv (x Rat.infinitePlace))) = _
    exact hT b _
  let eSA : Multiplicative (SAdeleRing ℚ ∅) ≃ₜ* Multiplicative (InfiniteAdeleRing ℚ) :=
    { toEquiv :=
        { toFun := fun x ↦ Multiplicative.ofAdd x.toAdd.1
          invFun := fun y ↦ Multiplicative.ofAdd (y.toAdd, 0)
          left_inv := fun x ↦ congrArg Multiplicative.ofAdd
            (Prod.ext rfl (Subsingleton.elim 0 x.toAdd.2))
          right_inv := fun _ ↦ rfl }
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_fst
      continuous_invFun := continuous_id.prodMk continuous_const }
  have : T2Space (Multiplicative (SAdeleRing ℚ ∅)) := eSA.isEmbedding.t2Space
  have : LocallyCompactSpace (Multiplicative (SAdeleRing ℚ ∅)) :=
    eSA.isOpenEmbedding.locallyCompactSpace
  let f₀ : ℬ(SAdeleRing ℚ ∅) :=
    ⟨arch.val ∘ eSA, schwartzBruhat_mem_comp_equiv eSA arch.property⟩
  have hf₀_eval : ∀ x : SAdeleRing ℚ ∅,
      f₀ (Multiplicative.ofAdd x) = arch (Multiplicative.ofAdd x.1) := fun _ ↦ rfl
  have hf₀_zero : f₀ (Multiplicative.ofAdd 0) = 0 := by
    rw [hf₀_eval, harch]
    change b (realEquiv 0) = 0
    rw [map_zero, hb]
    simp
  have hf₀_odd : ∀ x : SAdeleRing ℚ ∅,
      f₀ (Multiplicative.ofAdd (-x)) = - f₀ (Multiplicative.ofAdd x) := by
    intro x
    rw [hf₀_eval, harch, hf₀_eval, harch]
    change b (realEquiv (-(x.1 Rat.infinitePlace))) = - b (realEquiv (x.1 Rat.infinitePlace))
    rw [map_neg, hb, hb, Complex.ofReal_neg, neg_sq, neg_mul]
  have hf₀_fourier : sAdeleSchwartzFourier f₀ (Multiplicative.ofAdd 0) = 0 := by
    rw [sAdeleSchwartzFourier_apply_zero]
    have hmeas := sAdele_fourierMeasure (F := ℚ) (S := ∅)
    let G := Multiplicative (SAdeleRing ℚ ∅)
    let : MeasurableSpace (SAdeleRing ℚ ∅) := instMeasurableSpaceSAdeleRing ℚ ∅
    let : MeasurableSpace G := instMeasurableSpaceSAdeleRing ℚ ∅
    let μ : MeasureTheory.Measure G := sAdditiveTamagawaMeasure ℚ ∅
    have : T2Space G := hmeas.1
    have : LocallyCompactSpace G := hmeas.2.1
    have : BorelSpace G := hmeas.2.2.1
    have : μ.IsHaarMeasure := hmeas.2.2.2.1
    have : μ.Regular := hmeas.2.2.2.2
    have hinv : ∫ y : G, f₀ y⁻¹ ∂μ = ∫ y : G, f₀ y ∂μ :=
      MeasureTheory.integral_inv_eq_self (fun y : G ↦ f₀ y) μ
    have hneg : ∫ y : G, f₀ y⁻¹ ∂μ = - ∫ y : G, f₀ y ∂μ := by
      have hfun : (fun y : G ↦ f₀ y⁻¹) = (fun y : G ↦ - f₀ y) := funext fun y ↦ by
        change f₀ (Multiplicative.ofAdd (-y.toAdd)) = - f₀ (Multiplicative.ofAdd y.toAdd)
        exact hf₀_odd y.toAdd
      rw [hfun, MeasureTheory.integral_neg]
    have heq : ∫ y : G, f₀ y ∂μ = - ∫ y : G, f₀ y ∂μ := hinv.symm.trans hneg
    have h2 : (2 : ℂ) * ∫ y : G, f₀ y ∂μ = 0 := by
      rw [two_mul]
      nth_rw 2 [heq]
      exact add_neg_cancel _
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)
  have hf₀_mem : f₀ ∈ sAdelePolarSubspace ℚ ∅ := by
    change (f₀ (Multiplicative.ofAdd 0), sAdeleSchwartzFourier f₀ (Multiplicative.ofAdd 0)) = 0
    exact Prod.mk_eq_zero.mpr ⟨hf₀_zero, hf₀_fourier⟩
  refine ⟨arch, ⟨f₀, hf₀_mem⟩, hf₀_eval, ?_⟩
  rw [hf₀_eval, harch]
  change b (realEquiv 1) = (Real.exp (-1) : ℂ)
  rw [map_one, hb, one_pow, Complex.ofReal_one, one_mul]

/-- Paper: Theorem 11.1.2.1(3), proof, p. 483. Take `F = ℚ`, the trivial
character, and `S = ∅` (only the real place in the paper). The real test
`x exp(−x²)` vanishes at zero and has zero integral. At the identity adele the product
is `exp(−1)`. Adeles obtained by changing only the p-coordinate to p tend
to the identity as p runs through distinct primes, but their products are
zero. This contradicts continuity of a Schwartz–Bruhat function. -/
theorem Printed.sLocalCarvingOutsideUnits_schwartzBruhat_false :
    ¬ Printed.sLocalCarvingOutsideUnits_schwartzBruhat := by
  intro hprinted
  obtain ⟨arch, f, hf_eval, hf_one⟩ := sec1b_exists_odd_test
  have hfact : ∃ (arch' : ℬ(InfiniteAdeleRing ℚ)) (fv : (v : (∅ : Finset V[ℚ])) → ℬ(v.val.adicCompletion ℚ)),
      ∀ x : SAdeleRing ℚ ∅, f.val (Multiplicative.ofAdd x) =
        arch' (Multiplicative.ofAdd x.1) * ∏ v : (∅ : Finset V[ℚ]), fv v (Multiplicative.ofAdd (x.2 v)) := by
    refine ⟨arch, fun v ↦ False.elim (Finset.notMem_empty v.1 v.2), fun x ↦ ?_⟩
    rw [hf_eval x, Finset.univ_eq_empty, Finset.prod_empty, mul_one]
  obtain ⟨h, hh⟩ := hprinted ℚ 1 ∅ sec1b_rat_one_unramified sec1b_rat_empty_trivialPic f hfact
  have hcont : Continuous (fun x : 𝔸[ℚ] ↦ h (Multiplicative.ofAdd x)) :=
    (schwartzBruhat_continuous h).comp continuous_ofAdd
  have h_one : h (Multiplicative.ofAdd 1) = (Real.exp (-1) : ℂ) := by
    have hmem : (1 : 𝔸[ℚ]) ∈ {y : 𝔸[ℚ] | ∀ v ∉ (∅ : Finset V[ℚ]), Valued.v (y.2 v) = 1} := by
      intro v _
      have h1v : (1 : FiniteAdeleRing (𝓞 ℚ) ℚ) v = 1 := rfl
      rw [Prod.snd_one, h1v, map_one]
    rw [hh 1, Set.indicator_of_mem hmem]
    exact (congrArg (fun z ↦ f.val (Multiplicative.ofAdd z))
      (map_one (adeleProjection ℚ ∅))).trans hf_one
  let inc : (Π v : V[ℚ], (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))) → FiniteAdeleRing (𝓞 ℚ) ℚ :=
    (RestrictedProduct.inclusion (fun v : V[ℚ] ↦ v.adicCompletion ℚ)
      (fun v : V[ℚ] ↦ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)))
      (le_top : Filter.cofinite ≤ ⊤)).comp RestrictedProduct.homeoTop
  have hinc_cont : Continuous inc :=
    (RestrictedProduct.continuous_inclusion le_top).comp RestrictedProduct.homeoTop.continuous
  let oneInt : Π v : V[ℚ], (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    fun _ ↦ ⟨1, Subring.one_mem _⟩
  let seqInt : V[ℚ] → Π w : V[ℚ], (w.adicCompletionIntegers ℚ : Set (w.adicCompletion ℚ)) :=
    fun v ↦ Function.update oneInt v ⟨0, Subring.zero_mem _⟩
  have htend_int : Filter.Tendsto seqInt Filter.cofinite (nhds oneInt) := by
    rw [tendsto_pi_nhds]
    intro w
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    refine Filter.eventually_cofinite.mpr ((Set.finite_singleton w).subset fun v hv ↦ ?_)
    by_contra hvw
    exact hv (Function.update_of_ne (Ne.symm hvw) ⟨0, Subring.zero_mem _⟩ oneInt).symm
  let seqA : V[ℚ] → 𝔸[ℚ] := fun v ↦ (1, inc (seqInt v))
  have htend_A : Filter.Tendsto seqA Filter.cofinite (nhds (1 : 𝔸[ℚ])) := by
    have h1 : (1 : 𝔸[ℚ]) = (1, inc oneInt) := Prod.ext rfl (by ext v; rfl)
    rw [h1, nhds_prod_eq]
    exact tendsto_const_nhds.prodMk (hinc_cont.continuousAt.tendsto.comp htend_int)
  have hseq_zero : ∀ v : V[ℚ], h (Multiplicative.ofAdd (seqA v)) = 0 := by
    intro v
    have hnot : seqA v ∉ {y : 𝔸[ℚ] | ∀ w ∉ (∅ : Finset V[ℚ]), Valued.v (y.2 w) = 1} := by
      intro hmem
      have hv := hmem v (Finset.notMem_empty v)
      have hv0 : (seqA v).2 v = 0 := by
        change (inc (seqInt v)) v = 0
        exact congrArg Subtype.val (Function.update_self v ⟨0, Subring.zero_mem _⟩ oneInt)
      rw [hv0, map_zero] at hv
      exact zero_ne_one hv
    rw [hh (seqA v), Set.indicator_of_notMem hnot]
  have hinf : Infinite V[ℚ] :=
    Infinite.of_injective Rat.HeightOneSpectrum.primesEquiv.symm
      Rat.HeightOneSpectrum.primesEquiv.symm.injective
  have hlim : Filter.Tendsto (fun v : V[ℚ] ↦ h (Multiplicative.ofAdd (seqA v)))
      Filter.cofinite (nhds (h (Multiplicative.ofAdd 1))) :=
    hcont.continuousAt.tendsto.comp htend_A
  have hlim0 : Filter.Tendsto (fun v : V[ℚ] ↦ h (Multiplicative.ofAdd (seqA v)))
      Filter.cofinite (nhds (0 : ℂ)) := by
    simp_rw [hseq_zero]
    exact tendsto_const_nhds
  have heq0 : h (Multiplicative.ofAdd 1) = 0 := tendsto_nhds_unique hlim hlim0
  rw [h_one] at heq0
  exact Real.exp_ne_zero (-1) (Complex.ofReal_eq_zero.mp heq0)

/-- Paper: Theorem 11.1.2.1(3), proof, p. 483. As printed: the unaveraged
product with the open lower norm cutoff defines a function of the idele
class. This is the descent claimed for the displayed generators, including
those of the space whose tests only satisfy the Fourier vanishing condition.
The formula `sLocalCarvingTheta_spec` instead uses the principal orbit sum
at each representative (ERRATA F205). -/
def Printed.sLocalCarvingCutoffProduct_descends : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C[F]) (S : Finset V[F]),
    ideleClassNormTwist χ 0 ∈ unramifiedOutside F S →
    Subsingleton (CommRing.Pic (Set.integer (R := 𝓞 F) (S : Set V[F]) F)) →
    ∀ (Λ : ℝ), 0 < Λ →
      ∀ f : ℬ(SAdeleRing F S), sAdeleSchwartzFourier f (Multiplicative.ofAdd 0) = 0 →
        ∃ h : C[F] → ℂ, ∀ g : I[F],
          h (classOf[F] g) =
            {u : I[F] | Λ⁻¹ < ((ideleNorm F u).val : ℝ)}.indicator
              (sLocalCarvingIdeleTest S f) g

/-- Paper: Theorem 11.1.2.1(3), proof, p. 483. Take `F = ℚ`, the trivial
character, `S = ∅` (only the real place in the paper), `Λ = 2`, and the
real test `x exp(−x²)`. The principal ideles 1 and 2 give the same class and both
have norm one. The displayed product takes value `exp(−1)` on 1 and
zero on 2 because its 2-adic coordinate is not a unit. -/
theorem Printed.sLocalCarvingCutoffProduct_descends_false :
    ¬ Printed.sLocalCarvingCutoffProduct_descends := by
  intro hprinted
  obtain ⟨_, f, _, hf_one⟩ := sec1b_exists_odd_test
  have hf_fourier : sAdeleSchwartzFourier f.val (Multiplicative.ofAdd 0) = 0 :=
    ((mem_sAdelePolarSubspace f.val).mp f.property).2
  obtain ⟨h, hh⟩ := hprinted ℚ 1 ∅ sec1b_rat_one_unramified sec1b_rat_empty_trivialPic
    2 (by norm_num) f.val hf_fourier
  have h1_class : h (classOf[ℚ] 1) = (Real.exp (-1) : ℂ) := by
    have hnorm1 : (2 : ℝ)⁻¹ < ((ideleNorm ℚ (1 : I[ℚ])).val : ℝ) := by
      rw [map_one, Units.val_one, NNReal.coe_one]
      norm_num
    rw [hh 1, Set.indicator_of_mem hnorm1, sLocalCarvingIdeleTest_one]
    exact hf_one
  obtain ⟨p, u, hp, -, hg_ker, hg_out⟩ := exists_rat_prime_idele_outside (∅ : Finset V[ℚ])
  let g := IdeleGroup.unitEmbedding (𝓞 ℚ) ℚ u
  have hg_class : classOf[ℚ] g = classOf[ℚ] 1 := by
    rw [map_one]
    exact (QuotientGroup.eq_one_iff g).mpr ⟨u, rfl⟩
  have hnorm_g : (2 : ℝ)⁻¹ < ((ideleNorm ℚ g).val : ℝ) := by
    rw [MonoidHom.mem_ker.mp hg_ker, Units.val_one, NNReal.coe_one]
    norm_num
  have hnot_unit : ¬ (∀ v ∉ (∅ : Finset V[ℚ]), Valued.v (g.val.2 v) = 1) := by
    intro hall
    apply hg_out
    have hmem_int : ∀ v : V[ℚ], g.val.2 v ∈ (v.adicCompletionIntegers ℚ : Set _) := by
      intro v
      change Valued.v (g.val.2 v) ≤ 1
      exact (hall v (Finset.notMem_empty v)).le
    have hinv_int : ∀ v : V[ℚ], g⁻¹.val.2 v ∈ (v.adicCompletionIntegers ℚ : Set _) := by
      intro v
      change Valued.v (g⁻¹.val.2 v) ≤ 1
      have hmul : g.val.2 v * g⁻¹.val.2 v = 1 :=
        congrArg (fun z : 𝔸[ℚ] ↦ z.2 v) (Units.mul_inv g)
      have hvmul : Valued.v (g.val.2 v) * Valued.v (g⁻¹.val.2 v) = 1 := by
        rw [← map_mul, hmul, map_one]
      rw [hall v (Finset.notMem_empty v), one_mul] at hvmul
      exact hvmul.le
    let w : ↥(integralAdelesOutside ℚ (∅ : Finset V[ℚ])) :=
      ⟨g.val, Subring.mem_iInf.mpr fun v ↦ Subring.mem_iInf.mpr fun _ ↦ hmem_int v⟩
    let winv : ↥(integralAdelesOutside ℚ (∅ : Finset V[ℚ])) :=
      ⟨g⁻¹.val, Subring.mem_iInf.mpr fun v ↦ Subring.mem_iInf.mpr fun _ ↦ hinv_int v⟩
    refine ⟨⟨w, winv, Subtype.ext g.mul_inv, Subtype.ext g.inv_mul⟩, Units.ext rfl⟩
  have hg_zero : h (classOf[ℚ] g) = 0 := by
    rw [hh g, Set.indicator_of_mem hnorm_g, sLocalCarvingIdeleTest, Set.indicator_of_notMem hnot_unit]
  rw [hg_class, h1_class] at hg_zero
  exact Real.exp_ne_zero (-1) (Complex.ofReal_eq_zero.mp hg_zero)

end RiemannMasullo
