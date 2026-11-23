module

public import RiemannMasullo.AppB_AnalyticNT.Sec5
import Mathlib.Algebra.Field.ULift
import Mathlib.NumberTheory.Real.Irrational

/-!
# Appendix B.5: statements that are false as printed

The printed claims are kept as propositions with separate refutation statements.
Nothing imports this file.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open Complex.HadamardThreeLines (verticalStrip)
open scoped Topology

namespace RiemannMasullo

/-- Paper: §B.5.1, injectivity sentence, p. 627. As printed: in every positive
dimension, the torus flow of rationally independent frequencies is injective.
This is the injectivity clause of the sentence. The repaired
`torusFlow_injective_of_linearIndependent` requires dimension at least two.
See ERRATA F19. -/
def Printed.torusFlow_injective_of_linearIndependent : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ (τ : Fin N → ℝ), LinearIndependent ℚ τ → Injective (torusFlow τ)

/-- Paper: §B.5.1, injectivity sentence, p. 627. In dimension one the
single frequency `1` is rationally independent, and times zero and one have the same
image modulo one. -/
theorem Printed.torusFlow_injective_of_linearIndependent_false :
    ¬ Printed.torusFlow_injective_of_linearIndependent := by
  intro h
  have hli : LinearIndependent ℚ (fun _ : Fin 1 ↦ (1 : ℝ)) :=
    linearIndependent_unique_iff.mpr one_ne_zero
  have h01 :
      torusFlow (fun _ : Fin 1 ↦ (1 : ℝ)) 1 = torusFlow (fun _ : Fin 1 ↦ (1 : ℝ)) 0 := by
    rw [torusFlow_one, map_zero]
    funext i
    exact AddCircle.coe_period (1 : ℝ)
  exact one_ne_zero (h 1 le_rfl _ hli h01)

/-- Paper: Theorem B.5.2.1(2), p. 627. As printed: for every frequency vector
and every Riemann-integrable function on its orbit closure, the forward time average
in (B.5.2.1) exists and tends to the Haar probability integral. The forward equality
requires the time integrals to exist for all sufficiently large endpoints.
The repaired `kroneckerWeyl_riemannIntegrable_forward` assumes a measurable time
trace. See ERRATA F20. -/
def Printed.kroneckerWeyl_riemannIntegrable_forward : Prop :=
  ∀ (N : ℕ) [NeZero N] (τ : Fin N → ℝ)
    (μ : Measure (torusFlowClosure τ)) [μ.IsAddHaarMeasure] [IsProbabilityMeasure μ]
    (u : torusFlowClosure τ → ℂ), TorusRiemannIntegrable μ u →
      let trace := fun t ↦ u (torusFlowInClosure τ t)
      (∀ᶠ T : ℝ in atTop, IntervalIntegrable trace volume 0 T) ∧
        Tendsto (fun T : ℝ ↦ T⁻¹ • ∫ t in 0..T, trace t) atTop (𝓝 (∫ x, u x ∂μ))

private theorem Printed.kroneckerWeyl_rat_functional :
    ∃ g : ℝ →ₗ[ℚ] ℚ, ∀ q : ℚ, g (q : ℝ) = q := by
  let f : ℚ →ₗ[ℚ] ℝ := LinearMap.toSpanSingleton ℚ ℝ (1 : ℝ)
  have hf (q : ℚ) : f q = (q : ℝ) := by simp [f, Rat.smul_one_eq_cast]
  have hk : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr fun a b hab ↦ by
    rw [hf, hf] at hab; exact_mod_cast hab
  obtain ⟨g, hg⟩ := f.exists_leftInverse_of_injective hk
  refine ⟨g, fun q ↦ ?_⟩
  have := LinearMap.congr_fun hg q
  rwa [LinearMap.comp_apply, hf] at this

open scoped Pointwise in
private theorem Printed.kroneckerWeyl_not_nullMeasurable_ker (g : ℝ →ₗ[ℚ] ℚ)
    (hg : ∀ q : ℚ, g (q : ℝ) = q) :
    ¬ ∀ n : ℕ, NullMeasurableSet ({x | g x = 0} ∩ Icc (-(n : ℝ)) n) volume := by
  intro hA
  set A : Set ℝ := {x | g x = 0} with hAdef
  have hAU : A = ⋃ n : ℕ, A ∩ Icc (-(n : ℝ)) n := by
    ext x
    simp only [mem_iUnion, mem_inter_iff, mem_Icc]
    refine ⟨fun hx ↦ ?_, fun ⟨_, hx, _⟩ ↦ hx⟩
    obtain ⟨n, hn⟩ := exists_nat_ge |x|
    exact ⟨n, hx, neg_le_of_abs_le hn, le_of_abs_le hn⟩
  by_cases h0 : ∀ n : ℕ, volume (A ∩ Icc (-(n : ℝ)) n) = 0
  · have hA0 : volume A = 0 := by rw [hAU]; exact measure_iUnion_null h0
    have hcover : (univ : Set ℝ) = ⋃ q : ℚ, (fun x ↦ x + -(q : ℝ)) ⁻¹' A := by
      ext x
      simp only [mem_univ, mem_iUnion, mem_preimage, true_iff]
      refine ⟨g x, ?_⟩
      change g (x + -(g x : ℝ)) = 0
      rw [map_add, map_neg, hg, add_neg_cancel]
    have : volume (univ : Set ℝ) = 0 := by
      rw [hcover]
      refine measure_iUnion_null fun q ↦ ?_
      rw [measure_preimage_add_right]
      exact hA0
    simp at this
  · push Not at h0
    obtain ⟨n, hn⟩ := h0
    obtain ⟨M, hMs, hMm, hMae⟩ := (hA n).exists_measurable_subset_ae_eq
    have hMpos : 0 < volume M := by rw [measure_congr hMae]; exact pos_iff_ne_zero.mpr hn
    have hMfin : volume M ≠ ⊤ := ((measure_mono (hMs.trans inter_subset_right)).trans_lt
      measure_Icc_lt_top).ne
    have hnhds := Measure.sub_mem_nhds_zero_of_addHaar_pos_ne_top volume M hMm hMpos hMfin
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnhds
    obtain ⟨q, hq0, hqδ⟩ := exists_rat_btwn hδ
    have hqmem : (q : ℝ) ∈ M - M := hball (by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hq0]; exact hqδ)
    obtain ⟨a, ha, b, hb, hab⟩ := hqmem
    have ha' : g a = 0 := (hMs ha).1
    have hb' : g b = 0 := (hMs hb).1
    have : g (q : ℝ) = 0 := by rw [← hab, map_sub, ha', hb', sub_self]
    rw [hg] at this
    exact (Rat.cast_pos.mp hq0).ne' this

private theorem Printed.kroneckerWeyl_exists_nonmeasurable :
    ∃ L : ℝ, 0 < L ∧ ∃ E : Set ℝ, E ⊆ Ioc 0 L ∧ ¬ NullMeasurableSet E volume := by
  obtain ⟨g, hg⟩ := Printed.kroneckerWeyl_rat_functional
  have h := Printed.kroneckerWeyl_not_nullMeasurable_ker g hg
  push Not at h
  obtain ⟨n, hn⟩ := h
  set A : Set ℝ := {x | g x = 0} ∩ Icc (-(n : ℝ)) n
  refine ⟨2 * n + 1, by positivity, (fun x ↦ x + -((n : ℝ) + 1)) ⁻¹' A, ?_, fun hE ↦ hn ?_⟩
  · intro x hx
    obtain ⟨-, h1, h2⟩ := hx
    constructor <;> linarith
  · have hpre : A = (fun x ↦ x + ((n : ℝ) + 1)) ⁻¹' ((fun x ↦ x + -((n : ℝ) + 1)) ⁻¹' A) := by
      ext x; simp only [mem_preimage, add_neg_cancel_right]
    rw [hpre]
    exact hE.preimage (measurePreserving_add_right volume _).quasiMeasurePreserving

private theorem Printed.kroneckerWeyl_measure_arc_eq_zero {G : Type*} [AddCommGroup G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddLeftInvariant] [IsFiniteMeasure μ]
    (φ : ℝ →+ G) (hφc : Continuous φ) (hφ : Injective φ) (L : ℝ) (hL : 0 ≤ L) :
    μ (φ '' Icc 0 L) = 0 := by
  set K := φ '' Icc 0 L
  have hKm : MeasurableSet K := ((isCompact_Icc).image hφc).isClosed.measurableSet
  let P : ℕ → Set G := fun k ↦ (fun h ↦ φ (-((k : ℝ) * (L + 1))) + h) ⁻¹' K
  have hPm (k : ℕ) : MeasurableSet (P k) := measurable_const_add _ hKm
  have hPμ (k : ℕ) : μ (P k) = μ K := measure_preimage_add μ _ K
  have hdisj : Pairwise (Disjoint on P) := by
    intro j k hjk
    refine Set.disjoint_left.mpr fun x hxj hxk ↦ hjk ?_
    obtain ⟨s, ⟨hs0, hsL⟩, hs⟩ := hxj
    obtain ⟨s', ⟨hs0', hsL'⟩, hs'⟩ := hxk
    have heq : φ (s - s') = φ (((k : ℝ) - j) * (L + 1)) := by
      have e1 : φ s = φ (-((j : ℝ) * (L + 1))) + x := hs
      have e2 : φ s' = φ (-((k : ℝ) * (L + 1))) + x := hs'
      rw [map_sub, e1, e2, show ((k : ℝ) - j) * (L + 1) = -((j : ℝ) * (L + 1)) - -((k : ℝ) * (L + 1)) by ring,
        map_sub]
      abel
    have h := hφ heq
    rcases lt_trichotomy j k with hlt | heq' | hgt
    · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hlt
      nlinarith
    · exact heq'
    · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hgt
      nlinarith
  by_contra hne
  have hU := measure_iUnion (μ := μ) hdisj hPm
  simp only [hPμ, ENNReal.tsum_const_eq_top_of_ne_zero hne] at hU
  exact measure_ne_top μ (⋃ k, P k) hU

private theorem Printed.kroneckerWeyl_linearIndependent_sqrt_two :
    LinearIndependent ℚ ![(1 : ℝ), √2] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  rw [Rat.smul_def, Rat.smul_def, mul_one] at hst
  by_cases ht : t = 0
  · subst ht
    simp only [Rat.cast_zero, zero_mul, add_zero, Rat.cast_eq_zero] at hst
    exact ⟨hst, rfl⟩
  · exfalso
    have ht' : (t : ℝ) ≠ 0 := by exact_mod_cast ht
    have h2 : √2 = ((-s / t : ℚ) : ℝ) := by
      push_cast
      field_simp
      linarith
    exact irrational_sqrt_two ⟨_, h2.symm⟩

/-- Paper: Theorem B.5.2.1(2), p. 627. Take frequencies `(1, √2)` and a
non-Lebesgue-measurable subset `E` of `(0, 1)`. The indicator of the image of `E`
under the flow is bounded and continuous off the compact Haar-null orbit arc of
`[0, 1]`. Injectivity makes its time trace the indicator of `E`, which is
nonmeasurable on every interval `[0, T]` with `T ≥ 1`. -/
theorem Printed.kroneckerWeyl_riemannIntegrable_forward_false :
    ¬ Printed.kroneckerWeyl_riemannIntegrable_forward := by
  intro h
  obtain ⟨L, hL, E, hE, hnm⟩ := Printed.kroneckerWeyl_exists_nonmeasurable
  set τ : Fin 2 → ℝ := ![(1 : ℝ), √2]
  have hinj : Injective (torusFlowInClosure τ) := fun s t hst ↦
    RiemannMasullo.torusFlow_injective_of_linearIndependent le_rfl
      Printed.kroneckerWeyl_linearIndependent_sqrt_two (congrArg Subtype.val hst)
  let φ : ℝ →+ torusFlowClosure τ :=
    { toFun := torusFlowInClosure τ
      map_zero' := Subtype.ext (map_zero (torusFlow τ))
      map_add' := fun s t ↦ Subtype.ext (map_add (torusFlow τ) s t) }
  have hφc : Continuous φ := (torusFlow τ).continuous.subtype_mk _
  have : CompactSpace (torusFlowClosure τ) := isCompact_iff_compactSpace.mp
    (AddSubgroup.isClosed_topologicalClosure _).isCompact
  let μ : Measure (torusFlowClosure τ) := Measure.addHaarMeasure ⊤
  have : IsProbabilityMeasure μ := ⟨Measure.addHaarMeasure_self⟩
  set K := φ '' Icc 0 L with hKdef
  have hK0 : μ K = 0 :=
    Printed.kroneckerWeyl_measure_arc_eq_zero μ φ hφc hinj L hL.le
  have hKc : IsClosed K := ((isCompact_Icc).image hφc).isClosed
  have hEK : φ '' E ⊆ K := image_mono fun x hx ↦ Ioc_subset_Icc_self (hE hx)
  let u : torusFlowClosure τ → ℂ := (φ '' E).indicator fun _ ↦ 1
  have hu : TorusRiemannIntegrable μ u := by
    refine ⟨⟨1, fun x ↦ ?_⟩, ?_⟩
    · by_cases hx : x ∈ φ '' E <;> simp [u, hx]
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hK0] with x hx
      refine continuousAt_const.congr (f := fun _ ↦ (0 : ℂ)) ?_
      filter_upwards [hKc.isOpen_compl.mem_nhds hx] with y hy
      exact (indicator_of_notMem (fun h ↦ hy (hEK h)) _).symm
  have htrace : (fun t ↦ u (torusFlowInClosure τ t)) = E.indicator fun _ ↦ (1 : ℂ) := by
    funext t
    by_cases ht : t ∈ E
    · have : torusFlowInClosure τ t ∈ φ '' E := ⟨t, ht, rfl⟩
      simp [u, ht, this]
    · have : torusFlowInClosure τ t ∉ φ '' E := fun ⟨s, hs, hst⟩ ↦ ht (hinj hst ▸ hs)
      simp [u, ht, this]
  have hint := (h 2 τ μ u hu).1
  obtain ⟨T, hT, hLT⟩ := (hint.and (eventually_ge_atTop L)).exists
  rw [htrace] at hT
  have hmeas := (hT.1).aestronglyMeasurable.aemeasurable
  have hET : E ⊆ Ioc 0 T := fun x hx ↦ ⟨(hE hx).1, (hE hx).2.trans hLT⟩
  rw [← aemeasurable_indicator_iff measurableSet_Ioc, indicator_indicator,
    inter_eq_right.mpr hET, aemeasurable_indicator_const_iff] at hmeas
  exact hnm hmeas

/-- Paper: Proposition B.5.3.2(1),(3), p. 632. As printed: for every number field,
finite set of places containing the archimedean places, and continuous character
unramified at its finite places, there are heights with both stated signs and a common
finite bound on the product in (B.5.3.3) for every integer index. The bound is written
as a positive lower bound on the norm of the product of the denominators, so it
excludes zeros of every denominator. These two sign conditions and the bound are
the clauses at issue. The repaired
`exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow` allows a positive
height at index zero. See ERRATA F21. -/
def Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow : Prop :=
  ∀ (F : Type*) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (χ : PontryaginDual (IdeleClassGroup (𝓞 F) F)),
    (∀ v ∈ S, (ideleClassNormTwist χ 0).IsUnramifiedAt v) →
      ∃ (c : ℝ) (T : ℤ → ℝ), 0 < c ∧
        (∀ k, 0 ≤ k → 0 ≤ T k) ∧ (∀ k, k ≤ 0 → T k ≤ 0) ∧
        ∀ k, c ≤ ‖reciprocalPartialHeckeEulerProduct χ S ((T k : ℂ) * Complex.I)‖

/-- Every number field refutes the printed bound: the trivial character has a zero
factor at time zero. -/
private theorem
    Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow_false_of_numberField.{u}
    (F : Type u) [Field F] [NumberField F]
    (h : Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow.{u}) : False := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  let v : HeightOneSpectrum (𝓞 F) := ⟨m, hm.isPrime, NeZero.ne m⟩
  have hone :
      ∀ g, ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0 g = 1 := by
    intro g
    change ((1 : Circle) : ℂ) * (_ : ℂ) ^ (0 : ℂ) = 1
    simp
  have hres : ∀ x : v.adicCompletion F, x ≠ 0 →
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).restrict v x =
        1 := by
    intro x hx
    rw [show x = ((Units.mk0 x hx : (v.adicCompletion F)ˣ) : v.adicCompletion F) from rfl,
      HeckeCharacter.restrict, MulChar.ofUnitHom_coe]
    simp [hone]
  have hunr :
      (ideleClassNormTwist (1 : PontryaginDual (IdeleClassGroup (𝓞 F) F)) 0).IsUnramifiedAt
        v := by
    rw [HeckeCharacter.isUnramifiedAt_iff]
    intro x
    exact hres _ (by simp)
  obtain ⟨c, T, hc, hpos, hneg, hbound⟩ := h F {v} 1 (by simpa using hunr)
  have hT : T 0 = 0 := le_antisymm (hneg 0 le_rfl) (hpos 0 le_rfl)
  have h0 := hbound 0
  rw [hT, reciprocalPartialHeckeEulerProduct_singleton _ v hunr,
    hunr.localValue_eq _ Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec,
    hres _ (Valued.v.exists_isUniformizer_of_isCyclic_of_nontrivial.choose_spec.ne_zero)] at h0
  simp at h0
  linarith

/-- Paper: Proposition B.5.3.2(1),(3), p. 632. Take the rational field,
the trivial character, and the places consisting of infinity and the prime above two.
Both sign conditions apply at index zero, so `T 0 = 0`. The only finite factor
in the denominator is then `|1 - 2^0| = 0`. -/
theorem Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow_false :
    ¬ Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow := by
  intro h
  have : CharZero (ULift ℚ) := ⟨fun a b hab ↦ by simpa using congrArg ULift.down hab⟩
  have : NumberField (ULift ℚ) := ⟨⟩
  exact
    Printed.exists_heights_reciprocalPartialHeckeEulerProduct_boundedBelow_false_of_numberField
      (ULift ℚ) h

/-- Paper: Lemma B.5.3.4(2), p. 633. As printed: if a holomorphic function on a
bounded nonempty open vertical strip is strongly recurrent on every closed disc it
contains, then the function is strongly recurrent on every compact subset of the strip.
Part (1) is `stronglyRecurrentOn_of_subset`. See ERRATA F22. -/
def Printed.stronglyRecurrentOn_compact_of_closedBall : Prop :=
  ∀ (a b : ℝ), a < b → ∀ (f : ℂ → ℂ), DifferentiableOn ℂ f (verticalStrip a b) →
    (∀ (z : ℂ) (r : ℝ), 0 ≤ r → Metric.closedBall z r ⊆ verticalStrip a b →
      StronglyRecurrentOn f (Metric.closedBall z r)) →
    ∀ (K : Set ℂ), IsCompact K → K ⊆ verticalStrip a b → StronglyRecurrentOn f K

/-- Paper: Lemma B.5.3.4(2), p. 633. In the strip `|Re z| < 1/2` take the
segment `K = [-2i, 2i]`. Construct an entire function of norm less than one on
`K` and greater than three at every `4ji` for nonzero integer `j`.
Start with polynomial approximations to zero on `K` and four at `±4i`.
Cycle through the rational closed discs strictly inside the strip. At stage
`L = 2^n`, approximate the preceding polynomial on the square of half-side
`4L + 1` and copy its values from the scheduled disc of center `c` to its vertical
translates by `i (4m + 2 - Im c)` for `L ≤ m < 2L`. Their centers have height
`4m + 2` and their radii are less than one half. Schedule each disc infinitely often
after it fits in the old square. Approximate four at `±4ji` for `L < j ≤ 2L`. The union of the
square, new discs, and new marks has connected complement, so Runge approximation
allows summable errors of total less than one. For each disc strictly inside a scheduled
disc, the copy errors tend to zero and continuity gives intervals of good shifts of fixed
positive width.
These intervals give positive upper density along its blocks. Every shift of
`K` by imaginary height of absolute value at least six meets a mark, so its
return times for tolerance two have upper density zero. -/
theorem Printed.stronglyRecurrentOn_compact_of_closedBall_false :
    ¬ Printed.stronglyRecurrentOn_compact_of_closedBall := by
  sorry

end RiemannMasullo
