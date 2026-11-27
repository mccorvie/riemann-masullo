module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4

/-! # The sharp orbital mass for a cutoff with an inner radius

Paper: Theorem 12.4.1.1, footnote 2, p. 514, with (12.4.1.22)–(12.4.1.24), p. 518.

Footnote 2 asks to replace the spatial cutoff by a smoothing of the indicator of
`[1 / λ'', λ]`, with `λ''` not tied to `λ`, and then to study the convergence of the integral
in (12.4.1.23) as `λ', λ'' → +∞`. This file does that computation for sharp indicators.

* `sLocalTraceSharpMass_sub_eq_integral`: the skew-diagonal integral for the norms in `(a, L]`
  is the difference of the sharp orbital masses at `L * L'` and at `a * L'`.
* `sLocalTraceSharpMass_sub_asymptotic`: as both radii tend to infinity, that difference is the
  logarithmic term for their ratio plus `o(1)`. The local principal values of
  (12.4.1.1)–(12.4.1.3) cancel.
* `sLocalTraceSharpMass_sub_tendsto_zero_of_identity_eq_zero`: for a test that vanishes at the
  identity the two limits stand side by side, the local principal values without inner radius
  and zero with it.

So the limit asked for in the footnote depends on `λ' / λ''`. If that ratio tends to infinity
the amended mass has no local term. ERRATA row M39 records this for `ℚ` with the real place
and a bump supported in `(1, 2)`. Here it holds for every number field and every `S` to which
`sLocalTraceSharpMass_asymptotic` applies. The case in which `λ' / λ''` tends to zero is not
treated here. -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instSIdeleT2Sec4

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "Hₛ" => sProjectedDiagonal F S
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ w.mult) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "volume₁" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
local notation "ψₛ" => sAdeleStandardCharacter F S
local notation "fourierₛ" => tamagawaFourier νₛ ψₛ
local notation "band(" L ")" => sLocalPWProductRegion (F := F) S L
local notation "archTest" => ((w : InfinitePlace F) → BruhatCompactSupport w.Completionˣ)
local notation "finiteTest" => ((v : S) → BruhatCompactSupport (v.val.adicCompletion F)ˣ)
local notation "archClass(" w ")" => IdeleClassGroup.ofCompletion (𝓞 F) F w
local notation "finiteClass(" v ")" => IdeleClassGroup.ofAdicCompletion (𝓞 F) F v
local notation "finiteVolume(" v ")" =>
  (finiteLocalMultiplicativeTamagawaMeasure F v
    ((HeightOneSpectrum.adicCompletionIntegers F v).units : Set _)).toReal
local notation "principalValues(" a "," b ")" =>
  ((∑ w : InfinitePlace F, infiniteConnesWeilPrincipalValue w (a w)) +
    ∑ v : S, ((Real.log (v.val.asIdeal.absNorm : ℝ) / finiteVolume(v.val) : ℝ) : ℂ) *
      finiteConnesWeilPrincipalValue v.val 1 (b v))

/-- The S-idelic norm is continuous. A copy of the private lemma
`sLocalTrace_sIdeleNorm_continuous` of `Sec4`. -/
private theorem annularSharpMass_sIdeleNorm_continuous : Continuous (sIdeleNorm F S) := by
  apply Units.isEmbedding_val₀.continuous_iff.mpr
  change Continuous (fun g : Iₛ ↦ ((sIdeleNorm F S g).val))
  simp only [sIdeleNorm, MonoidHom.mul_apply, MonoidHom.finsetProd_apply, MonoidHom.pow_apply,
    Units.val_mul, Units.coe_prod, Units.val_pow_eq_pow_val]
  change Continuous (fun g : Iₛ ↦ (∏ w : InfinitePlace F, ‖g.val.1 w‖₊ ^ w.mult) *
    ∏ v : S, ‖g.val.2 v‖₊)
  fun_prop

/-- The indicator of the frequency band is measurable, bounded and even. These three facts are
proved inside the private lemma `sLocalTraceSharp_diag` of `Sec4` and repeated here. -/
private theorem annularSharpMass_band_symbol (L' : ℝ) :
    Measurable (indicator band(L') (fun _ : Aₛ ↦ (1 : ℂ))) ∧
      (∃ C : ℝ, ∀ u, ‖indicator band(L') (fun _ : Aₛ ↦ (1 : ℂ)) u‖ ≤ C) ∧
      ∀ u : Aₛ, indicator band(L') (fun _ : Aₛ ↦ (1 : ℂ)) (-u) =
        indicator band(L') (fun _ ↦ 1) u := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have hm : Continuous fun t : Aₛ ↦ modS(t) :=
    (continuous_finsetProd _ fun w _ ↦
      (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  have hband : MeasurableSet (band(L')) := (isClosed_le hm continuous_const).measurableSet
  have hneg (u : Aₛ) : -u ∈ band(L') ↔ u ∈ band(L') := by
    have h1 (w : InfinitePlace F) : ‖(-u.1) w‖ = ‖u.1 w‖ := by
      rw [show (-u.1) w = -(u.1 w) from rfl, norm_neg]
    simp [sLocalPWProductRegion, h1]
  refine ⟨measurable_const.indicator hband,
    ⟨1, fun u ↦ by by_cases h : u ∈ band(L') <;> simp [h]⟩, fun u ↦ ?_⟩
  by_cases h : u ∈ band(L')
  · rw [indicator_of_mem ((hneg u).2 h), indicator_of_mem h]
  · rw [indicator_of_notMem (mt (hneg u).1 h), indicator_of_notMem h]

/-- Paper: Theorem 12.4.1.1, footnote 2, p. 514, and (12.4.1.22)–(12.4.1.24), p. 518. With a
sharp spatial cutoff to the norms in `(a, L]` and the sharp frequency band of radius `L'`, the
skew-diagonal integral on a fundamental domain of the S-units is the difference of the sharp
orbital masses at `L * L'` and at `a * L'`. In the notation of the footnote `L = λ`,
`L' = λ'` and `a = 1 / λ''`, so the two radii are `λ λ'` and `λ' / λ''`.
Reconstruction: The footnote asks for a cutoff with an inner radius not tied to `λ` and leaves
the computation to be done. This is that computation for sharp indicators, as
`sLocalTraceSharpMass_eq_integral` is for the cutoff without inner radius.
Deviation: The inner edge is excluded from the norm interval. -/
theorem sLocalTraceSharpMass_sub_eq_integral (f : BruhatCompactSupport Iₛ) (ξ : Hₛ)
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μₛ)
    (a L L' : ℝ) (ha : 0 < a) (haL : a ≤ L) (hL' : 0 < L') :
    let d := D ∩ {x : Iₛ | a < normS(x) ∧ normS(x) ≤ L}
    let K := sLocalTraceCutoffKernel f
      (indicator {x : Iₛ | a < normS(x) ∧ normS(x) ≤ L} (fun _ ↦ 1))
      (indicator band(L') (fun _ ↦ 1))
    let diag := fun x : Iₛ ↦ K (ξ.val * x) x.val
    IntegrableOn diag d ((νₛ).comap (Units.val : Iₛ → Aₛ)) ∧
      (∫ x in d, diag x ∂((νₛ).comap (Units.val : Iₛ → Aₛ))) =
        sLocalTraceSharpMass f ξ (L * L') - sLocalTraceSharpMass f ξ (a * L') := by
  intro d K diag
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  let m : Measure Iₛ := (νₛ).comap (Units.val : Iₛ → Aₛ)
  obtain ⟨hmeas, hbd, heven⟩ := annularSharpMass_band_symbol (F := F) (S := S) L'
  have hξ : sIdeleNorm F S ξ.val = 1 := by
    obtain ⟨γ, hγ, he⟩ := Subgroup.mem_map.mp ξ.property
    exact he ▸ (sIdeleNorm_spec F S).2 hγ
  have hnorm (x : Iₛ) : normS(ξ.val * x) = normS(x) := by rw [map_mul, hξ, one_mul]
  have hnm : Measurable fun x : Iₛ ↦ normS(x) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      annularSharpMass_sIdeleNorm_continuous)).measurable
  let BL : Set Iₛ := {x | normS(x) ≤ L}
  let Ba : Set Iₛ := {x | normS(x) ≤ a}
  let An : Set Iₛ := {x | a < normS(x) ∧ normS(x) ≤ L}
  have hBL : MeasurableSet BL := hnm measurableSet_Iic
  have hBa : MeasurableSet Ba := hnm measurableSet_Iic
  have hAn : MeasurableSet An := hnm measurableSet_Ioc
  let I : Iₛ → ℂ := fun x ↦ (sLocalTraceMeasureFactor S : ℂ) *
    ∫ u, indicator band(L') (fun _ : Aₛ ↦ (1 : ℂ)) u *
      fourierₛ (sLocalTraceEta f ξ) (x.val * u) ∂νₛ
  -- the diagonal of every norm cutoff is the indicator of its norm set times one function
  have hK (B : Set Iₛ) (hB : ∀ x : Iₛ, ξ.val * x ∈ B ↔ x ∈ B) :
      (fun x : Iₛ ↦ sLocalTraceCutoffKernel f (indicator B (fun _ ↦ 1))
        (indicator band(L') (fun _ ↦ 1)) (ξ.val * x) x.val) = B.indicator I := by
    funext x
    rw [(sLocalTraceCutoffKernel_skew f _ _ hmeas hbd heven ξ x).2, mul_assoc]
    by_cases hx : x ∈ B
    · rw [indicator_of_mem ((hB x).2 hx), indicator_of_mem hx, one_mul]
    · rw [indicator_of_notMem (mt (hB x).1 hx), indicator_of_notMem hx, zero_mul]
  have hKL := hK BL fun x ↦ by change normS(ξ.val * x) ≤ L ↔ normS(x) ≤ L; rw [hnorm]
  have hKa := hK Ba fun x ↦ by change normS(ξ.val * x) ≤ a ↔ normS(x) ≤ a; rw [hnorm]
  have hKA := hK An fun x ↦ by
    change (a < normS(ξ.val * x) ∧ normS(ξ.val * x) ≤ L) ↔ (a < normS(x) ∧ normS(x) ≤ L)
    rw [hnorm]
  -- integrals over `D ∩ B` are integrals of indicators against the measure restricted to `D`
  have hint (B : Set Iₛ) (hB : MeasurableSet B) (g : Iₛ → ℂ) :
      IntegrableOn g (D ∩ B) m ↔ Integrable (B.indicator g) (m.restrict D) := by
    rw [integrable_indicator_iff hB, IntegrableOn, IntegrableOn, Measure.restrict_restrict hB,
      inter_comm]
  have hval (B : Set Iₛ) (hB : MeasurableSet B) (g : Iₛ → ℂ) :
      ∫ x in D ∩ B, g x ∂m = ∫ x, B.indicator g x ∂(m.restrict D) := by
    rw [integral_indicator hB, Measure.restrict_restrict hB, inter_comm]
  obtain ⟨hiL, heL⟩ := sLocalTraceSharpMass_eq_integral f ξ D hD L L' (ha.trans_le haL) hL'
  obtain ⟨hia, hea⟩ := sLocalTraceSharpMass_eq_integral f ξ D hD a L' ha hL'
  have hiL' : Integrable (BL.indicator I) (m.restrict D) := by
    have h := (hint BL hBL (BL.indicator I)).mp (by rw [← hKL]; exact hiL)
    rwa [indicator_indicator, inter_self] at h
  have heL' : ∫ x, BL.indicator I x ∂(m.restrict D) = sLocalTraceSharpMass f ξ (L * L') := by
    have h := hval BL hBL (BL.indicator I)
    rw [indicator_indicator, inter_self] at h
    rw [← h, ← hKL]
    exact heL
  have hia' : Integrable (Ba.indicator I) (m.restrict D) := by
    have h := (hint Ba hBa (Ba.indicator I)).mp (by rw [← hKa]; exact hia)
    rwa [indicator_indicator, inter_self] at h
  have hea' : ∫ x, Ba.indicator I x ∂(m.restrict D) = sLocalTraceSharpMass f ξ (a * L') := by
    have h := hval Ba hBa (Ba.indicator I)
    rw [indicator_indicator, inter_self] at h
    rw [← h, ← hKa]
    exact hea
  have hsplit : An.indicator I = fun x ↦ BL.indicator I x - Ba.indicator I x := by
    funext x
    by_cases h1 : normS(x) ≤ a
    · rw [indicator_of_mem (show x ∈ BL from h1.trans haL),
        indicator_of_notMem (show x ∉ An from fun h ↦ absurd h1 (not_le.mpr h.1)),
        indicator_of_mem (show x ∈ Ba from h1), sub_self]
    · by_cases h2 : normS(x) ≤ L
      · rw [indicator_of_mem (show x ∈ BL from h2),
          indicator_of_mem (show x ∈ An from ⟨not_le.mp h1, h2⟩),
          indicator_of_notMem (show x ∉ Ba from h1), sub_zero]
      · rw [indicator_of_notMem (show x ∉ BL from h2),
          indicator_of_notMem (show x ∉ An from fun h ↦ h2 h.2),
          indicator_of_notMem (show x ∉ Ba from h1), sub_zero]
  have hiA : Integrable (An.indicator I) (m.restrict D) := by
    rw [hsplit]
    exact hiL'.sub hia'
  have heA : ∫ x, An.indicator I x ∂(m.restrict D) =
      sLocalTraceSharpMass f ξ (L * L') - sLocalTraceSharpMass f ξ (a * L') := by
    rw [hsplit, integral_sub hiL' hia', heL', hea']
  have hdiag : diag = An.indicator I := hKA
  rw [hdiag]
  constructor
  · have h := (hint An hAn (An.indicator I)).mpr (by rwa [indicator_indicator, inter_self])
    exact h
  · have h := hval An hAn (An.indicator I)
    rw [indicator_indicator, inter_self] at h
    exact h.trans heA

/-- Paper: Theorem 12.4.1.1, footnote 2, p. 514, with (12.4.1.25)–(12.4.1.28), p. 519. The
summed sharp orbital masses `M R` satisfy two limits. With the logarithmic term removed, `M R`
tends to the norm-one volume times the local principal values, which is
`sLocalTraceSharpMass_asymptotic`. The difference `M R₁ - M R₂`, which by
`sLocalTraceSharpMass_sub_eq_integral` is the summed mass for a cutoff with inner radius, minus
the logarithmic term for `R₁ / R₂`, tends to zero as both radii tend to infinity: the local
principal values cancel. In the notation of the footnote `R₁ = λ λ'` and `R₂ = λ' / λ''`, so
whenever `λ' / λ''` tends to infinity the mass of the amended cutoff is
`φ(1) log (λ λ'') + o(1)` times the volume, with no local term.
Reconstruction: The footnote asks to “study the convergence” of the amended integral and
states no result. Sharp indicators are used, as in `sLocalTraceSharpMass_asymptotic`. -/
theorem sLocalTraceSharpMass_sub_asymptotic
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g)))) :
    ∃ (a : archTest) (b : finiteTest) (M : ℝ → ℂ),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      (∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R)) ∧
      Tendsto (fun R ↦ M R - (volume₁ : ℂ) * φ.val 1 * (Real.log R : ℂ))
        atTop (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) ∧
      Tendsto (fun p : ℝ × ℝ ↦ M p.1 - M p.2 -
          (volume₁ : ℂ) * φ.val 1 * ((Real.log p.1 - Real.log p.2 : ℝ) : ℂ))
        (atTop ×ˢ atTop) (𝓝 0) := by
  obtain ⟨a, b, M, ha, hb, hM, hlim⟩ :=
    sLocalTraceSharpMass_asymptotic (F := F) (S := S) φ hPic hRamified hOutside f hLift
  refine ⟨a, b, M, ha, hb, hM, hlim, ?_⟩
  have h1 := hlim.comp (tendsto_fst (f := (atTop : Filter ℝ)) (g := (atTop : Filter ℝ)))
  have h2 := hlim.comp (tendsto_snd (f := (atTop : Filter ℝ)) (g := (atTop : Filter ℝ)))
  have h3 := h1.sub h2
  rw [sub_self] at h3
  refine h3.congr fun p ↦ ?_
  simp only [Function.comp_apply, Complex.ofReal_sub]
  ring

/-- Paper: Theorem 12.4.1.1, footnote 2, p. 514. For a test that vanishes at the identity, the
summed sharp orbital masses tend to the norm-one volume times the local principal values, while
the summed masses of the cutoffs with inner radius tend to zero as `λ λ'` and `λ' / λ''` tend
to infinity. So the amended cutoff gives the formula of the theorem only if `λ' / λ''` stays
bounded or the local principal values sum to zero. -/
theorem sLocalTraceSharpMass_sub_tendsto_zero_of_identity_eq_zero
    (φ : BruhatCompactSupport C𝔽)
    (hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (hφ : φ.val 1 = 0) :
    ∃ (a : archTest) (b : finiteTest) (M : ℝ → ℂ),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ),
        (a w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (b v).val u = φ.val (finiteClass(v.val) u)) ∧
      (∀ᶠ R in atTop, HasSum (fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ R) (M R)) ∧
      Tendsto M atTop (𝓝 ((volume₁ : ℂ) * principalValues(a, b))) ∧
      Tendsto (fun p : ℝ × ℝ ↦ M p.1 - M p.2) (atTop ×ˢ atTop) (𝓝 0) := by
  obtain ⟨a, b, M, ha, hb, hM, h1, h2⟩ :=
    sLocalTraceSharpMass_sub_asymptotic (F := F) (S := S) φ hPic hRamified hOutside f hLift
  refine ⟨a, b, M, ha, hb, hM, ?_, ?_⟩
  · simpa only [hφ, mul_zero, zero_mul, sub_zero] using h1
  · simpa only [hφ, mul_zero, zero_mul, sub_zero] using h2

end RiemannMasullo
