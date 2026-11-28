module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4

/-!
# The lower spatial cutoff of footnote 2

Footnote 2 on p. 514 proposes to replace the spatial cutoff of Theorem 12.4.1.1, which smooths
the indicator of `|x| ≤ λ`, by a smoothing of the indicator of `1/λ'' ≤ |x| ≤ λ` with `λ''`
not tied to `λ`, and to study the limit as `λ', λ''` tend to infinity. The gap note above
`sLocalTrace_asymptotic_of_sharp_comparison` asks for this cutoff family.

With sharp cutoffs the answer follows from `Sec4.lean`. Removing the spatial region
`|x| ≤ 1/λ''` removes the sharp orbital mass at radius `λ' / λ''`, so the annular mass is the
difference of the sharp masses at the radii `λ λ'` and `λ' / λ''` (`sLocalAnnularMass_eq`).
When both radii tend to infinity, `sLocalTraceSharpMass_asymptotic` applies to both. The
local principal values cancel, and the summed annular masses less `volume₁ φ(1) log (λ λ'')`
tend to zero (`sLocalAnnularMass_asymptotic`). So the lower cutoff keeps the conclusion of
Theorem 12.4.1.1 only if `λ' / λ''` does not tend to infinity. When `λ' / λ''` tends to zero, the
summed sharp masses at radius `λ' / λ''` tend to zero (`sLocalTraceSharpMass_tsum_tendsto_zero`),
and the annular masses have the asymptotic of Theorem 12.4.1.1
(`sLocalAnnularMass_asymptotic_of_tendsto_zero`).

The fundamental domain is assumed measurable here.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ENNReal NNReal Topology

namespace RiemannMasullo.Isolated

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSAdeleMeasurableSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instSIdeleLocallyCompactSec1
  instFiniteCompletionUnitsLocallyCompactSec4b

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "V" => HeightOneSpectrum (𝓞 F)
local notation "Aₛ" => SAdeleRing F S
local notation "Iₛ" => (SAdeleRing F S)ˣ
local notation "Hₛ" => sProjectedDiagonal F S
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "classAtS(" g ")" => (QuotientGroup.mk (sIdeleInsertion F S g) : C𝔽)
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Aₛ).1 w‖ ^ w.mult) *
  ∏ v : S, ‖(x : Aₛ).2 v‖)
local notation "normS(" x ")" => (((sIdeleNorm F S x).val : ℝ))
local notation "νₛ" => sAdditiveTamagawaMeasure F S
local notation "μₛ" => sMultiplicativeTamagawaMeasure F S
local notation "volume₁" => ((sLocalNormOneQuotientMeasure F S) univ).toReal
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

local instance instSIdeleT2AnnularMass : T2Space Iₛ := (sIdeleGroup_description F S).2.1

theorem measurable_normS : Measurable fun x : Iₛ ↦ normS(x) := by
  have : BorelSpace Aₛ := sAdeleRing_borelSpace
  have : BorelSpace Iₛ := sIdeleGroup_borelSpace
  have hm : Continuous fun x : Aₛ ↦ modS(x) :=
    (continuous_finsetProd _ fun w _ ↦ (((continuous_apply w).comp continuous_fst).norm.pow _)).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  have h (x : Iₛ) : normS(x) = modS(x.val) := by simp [sIdeleNorm, Units.coe_prod]
  simp_rw [h]
  exact (hm.comp Units.continuous_val).measurable

theorem normS_unit_mul (ξ : Hₛ) (x : Iₛ) : normS(ξ.val * x) = normS(x) := by
  obtain ⟨γ, hγ, hξ⟩ := Subgroup.mem_map.mp ξ.property
  have h1 : sIdeleNorm F S ξ.val = 1 := by
    rw [← hξ]
    exact (sIdeleNorm_spec F S).2 hγ
  rw [map_mul, h1, one_mul]

/-- Paper: footnote 2, p. 514, with Step II, pp. 516–517.
The orbital mass of the unit `ξ` for the sharp annular spatial cutoff `c < |x| ≤ a` and the sharp
frequency cutoff `|u| ≤ b`: the integral of the kernel on the skew diagonal over the part of
norm at most `a` of the S-unit fundamental domain `D`. In the notation of the footnote,
`a = λ`, `b = λ'` and `c = 1 / λ''`. -/
def sLocalAnnularMass (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (D : Set Iₛ) (a b c : ℝ) : ℂ :=
  ∫ x in D ∩ {x : Iₛ | normS(x) ≤ a},
    sLocalTraceCutoffKernel f (indicator {x : Iₛ | c < normS(x) ∧ normS(x) ≤ a} (fun _ ↦ 1))
      (indicator band(b) (fun _ ↦ 1)) (ξ.val * x) x.val ∂((νₛ).comap Units.val)

/-- Reconstruction: the annular orbital mass is the difference of the sharp orbital masses at
the radii `a b` and `c b`. -/
theorem sLocalAnnularMass_eq (f : BruhatCompactSupport Iₛ) (ξ : Hₛ) (D : Set Iₛ)
    (hD : IsFundamentalDomain Hₛ D μₛ) (hDm : MeasurableSet D) {a b c : ℝ} (hc : 0 < c)
    (hca : c ≤ a) (hb : 0 < b) :
    sLocalAnnularMass f ξ D a b c =
      sLocalTraceSharpMass f ξ (a * b) - sLocalTraceSharpMass f ξ (c * b) := by
  have ha : 0 < a := hc.trans_le hca
  have hn := measurable_normS (F := F) (S := S)
  let K (r : ℝ) := sLocalTraceCutoffKernel f (indicator {x : Iₛ | normS(x) ≤ r} (fun _ ↦ 1))
    (indicator band(b) (fun _ ↦ 1))
  let T : Set Iₛ := {x | c < normS(x)}
  have hT : MeasurableSet T := measurableSet_lt measurable_const hn
  have hda : MeasurableSet (D ∩ {x : Iₛ | normS(x) ≤ a}) :=
    hDm.inter (measurableSet_le hn measurable_const)
  have hdc : MeasurableSet (D ∩ {x : Iₛ | normS(x) ≤ c}) :=
    hDm.inter (measurableSet_le hn measurable_const)
  obtain ⟨hAi, hAe⟩ := sLocalTraceSharpMass_eq_integral f ξ D hD a b ha hb
  obtain ⟨-, hCe⟩ := sLocalTraceSharpMass_eq_integral f ξ D hD c b hc hb
  dsimp only at hAi hAe hCe
  -- On the slab of norm at most `a`, the annular kernel is the sharp kernel times `1_T`.
  have hann : sLocalAnnularMass f ξ D a b c =
      ∫ x in D ∩ {x : Iₛ | normS(x) ≤ a}, T.indicator (fun x ↦ K a (ξ.val * x) x.val) x
        ∂((νₛ).comap Units.val) := by
    refine setIntegral_congr_fun hda fun x hx ↦ ?_
    have hxa : normS(x) ≤ a := hx.2
    simp only [K, sLocalTraceCutoffKernel]
    by_cases hcx : c < normS(x)
    · rw [indicator_of_mem (show x ∈ T from hcx),
        indicator_of_mem (show c < normS(ξ.val * x) ∧ normS(ξ.val * x) ≤ a by
          rw [normS_unit_mul]
          exact ⟨hcx, hxa⟩),
        indicator_of_mem (show normS(ξ.val * x) ≤ a by rw [normS_unit_mul]; exact hxa)]
    · rw [indicator_of_notMem (show x ∉ T from hcx),
        indicator_of_notMem (show ¬ (c < normS(ξ.val * x) ∧ normS(ξ.val * x) ≤ a) by
          rw [normS_unit_mul]
          exact fun h ↦ hcx h.1), zero_mul]
  -- The part of norm at most `c` of the slab is the slab of norm at most `c`.
  have hdiff : (D ∩ {x : Iₛ | normS(x) ≤ a}) \ T = D ∩ {x : Iₛ | normS(x) ≤ c} := by
    ext x
    constructor
    · rintro ⟨⟨hD', -⟩, h⟩
      exact ⟨hD', not_lt.1 (show ¬ c < normS(x) from h)⟩
    · rintro ⟨hD', h⟩
      exact ⟨⟨hD', (show normS(x) ≤ c from h).trans hca⟩,
        show ¬ c < normS(x) from not_lt.2 h⟩
  -- On the slab of norm at most `c`, the sharp kernels of radii `a` and `c` agree.
  have hKc : ∫ x in D ∩ {x : Iₛ | normS(x) ≤ c}, K a (ξ.val * x) x.val
      ∂((νₛ).comap Units.val) = sLocalTraceSharpMass f ξ (c * b) := by
    rw [← hCe]
    refine setIntegral_congr_fun hdc fun x hx ↦ ?_
    have hxc : normS(x) ≤ c := hx.2
    simp only [K, sLocalTraceCutoffKernel]
    rw [indicator_of_mem (show normS(ξ.val * x) ≤ a by rw [normS_unit_mul]; exact hxc.trans hca),
      indicator_of_mem (show normS(ξ.val * x) ≤ c by rw [normS_unit_mul]; exact hxc)]
  have hsplit := integral_inter_add_sdiff hT hAi
  rw [hdiff, hKc, hAe] at hsplit
  rw [hann, setIntegral_indicator hT]
  linear_combination hsplit

/-- Paper: footnote 2, p. 514, with Theorem 12.4.1.1, pp. 514–519.
Reconstruction: with the sharp annular spatial cutoff `c < |x| ≤ a` and the sharp frequency
cutoff `|u| ≤ b`, suppose both `a b` and `c b` tend to infinity. In the notation of the footnote
these are `λ λ'` and `λ' / λ''`. Then the summed annular masses less `volume₁ φ(1) log (a / c)`
tend to zero. The local principal values of (12.4.1.1)–(12.4.1.3) cancel between the two sharp
masses, and the logarithmic term becomes `log (λ λ'')`. So the lower cutoff of the footnote keeps
the conclusion of Theorem 12.4.1.1 only if `λ' / λ''` does not tend to infinity. -/
theorem sLocalAnnularMass_asymptotic (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μₛ) (hDm : MeasurableSet D)
    {ι : Type*} {l : Filter ι} (a b c : ι → ℝ) (hc : ∀ᶠ i in l, 0 < c i)
    (hca : ∀ᶠ i in l, c i ≤ a i) (hb : ∀ᶠ i in l, 0 < b i)
    (hab : Tendsto (fun i ↦ a i * b i) l atTop) (hcb : Tendsto (fun i ↦ c i * b i) l atTop) :
    Tendsto (fun i ↦ (∑' ξ : Hₛ, sLocalAnnularMass f ξ D (a i) (b i) (c i)) -
      (volume₁ : ℂ) * φ.val 1 * (Real.log (a i / c i) : ℂ)) l (𝓝 0) := by
  obtain ⟨pa, pb, M, -, -, hsum, hlim⟩ := sLocalTraceSharpMass_asymptotic (F := F) (S := S) φ
    _hPic _hRamified _hOutside f _hLift
  have h := (hlim.comp hab).sub (hlim.comp hcb)
  rw [sub_self] at h
  refine h.congr' ?_
  filter_upwards [hc, hca, hb, hab.eventually hsum, hcb.eventually hsum] with i hci hcai hbi
    hs1 hs2
  have hS : HasSum (fun ξ : Hₛ ↦ sLocalAnnularMass f ξ D (a i) (b i) (c i))
      (M (a i * b i) - M (c i * b i)) := by
    have h' := hs1.sub hs2
    refine h'.congr_fun fun ξ ↦ ?_
    exact sLocalAnnularMass_eq f ξ D hD hDm hci hcai hbi
  simp only [Function.comp_apply]
  rw [hS.tsum_eq]
  have hai : 0 < a i := hci.trans_le hcai
  rw [Real.log_div hai.ne' hci.ne', Real.log_mul hai.ne' hbi.ne', Real.log_mul hci.ne' hbi.ne']
  push_cast
  ring

/-- Paper: footnote 2, p. 514, with Theorem 12.4.1.1, pp. 514–519.
Reconstruction: with the sharp annular spatial cutoff `c < |x| ≤ a` and the sharp frequency
cutoff `|u| ≤ b`, suppose `a b` tends to infinity and `c b` tends to zero from above. In the
notation of the footnote these are `λ λ'` and `λ' / λ''`. Then the summed annular masses less
`volume₁ φ(1) log (a b)` tend to `volume₁` times the sum of the local principal values, the
conclusion of Theorem 12.4.1.1. The annular masses are the sharp masses at radius `a b` less the
sharp masses at radius `c b` (`sLocalAnnularMass_eq`), and the latter sum to something that tends
to zero (`sLocalTraceSharpMass_tsum_tendsto_zero`). -/
theorem sLocalAnnularMass_asymptotic_of_tendsto_zero (φ : BruhatCompactSupport C𝔽)
    (_hPic : Subsingleton (CommRing.Pic ((S : Set V).integer F)))
    (_hRamified : ∀ v : V, differentIdeal ℤ (𝓞 F) ≤ v.asIdeal → v ∈ S)
    (_hOutside : ∀ (a : outsideIntegralIdeleUnits F S) (c : C𝔽),
      φ.val (QuotientGroup.mk a.val * c) = φ.val c)
    (f : BruhatCompactSupport Iₛ)
    (_hLift : ∀ g : Iₛ, HasSum (fun ξ : Hₛ ↦ f.val (ξ.val * g)) (φ.val (classAtS(g))))
    (D : Set Iₛ) (hD : IsFundamentalDomain Hₛ D μₛ) (hDm : MeasurableSet D)
    {ι : Type*} {l : Filter ι} (a b c : ι → ℝ) (hc : ∀ᶠ i in l, 0 < c i)
    (hca : ∀ᶠ i in l, c i ≤ a i) (hb : ∀ᶠ i in l, 0 < b i)
    (hab : Tendsto (fun i ↦ a i * b i) l atTop) (hcb : Tendsto (fun i ↦ c i * b i) l (𝓝[>] 0)) :
    ∃ (pa : archTest) (pb : finiteTest),
      (∀ (w : InfinitePlace F) (u : w.Completionˣ), (pa w).val u = φ.val (archClass(w) u)) ∧
      (∀ (v : S) (u : (v.val.adicCompletion F)ˣ),
        (pb v).val u = φ.val (finiteClass(v.val) u)) ∧
      Tendsto (fun i ↦ (∑' ξ : Hₛ, sLocalAnnularMass f ξ D (a i) (b i) (c i)) -
        (volume₁ : ℂ) * φ.val 1 * (Real.log (a i * b i) : ℂ)) l
        (𝓝 ((volume₁ : ℂ) * principalValues(pa, pb))) := by
  obtain ⟨pa, pb, M, hpa, hpb, hsum, hlim⟩ := sLocalTraceSharpMass_asymptotic (F := F) (S := S) φ
    _hPic _hRamified _hOutside f _hLift
  refine ⟨pa, pb, hpa, hpb, ?_⟩
  obtain ⟨B, -, hB⟩ := sLocalTraceSharpMass_norm_sum_le_rpow f (c := 1 / 2) (by norm_num)
    (by norm_num)
  have h0 := (sLocalTraceSharpMass_tsum_tendsto_zero f).comp hcb
  have h := (hlim.comp hab).sub h0
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [hc, hca, hb, hab.eventually hsum,
    (hcb.mono_right nhdsWithin_le_nhds).eventually (gt_mem_nhds (zero_lt_one' ℝ))]
    with i hci hcai hbi hs1 hsmall
  have hcbpos : 0 < c i * b i := mul_pos hci hbi
  have hs2 : Summable fun ξ : Hₛ ↦ sLocalTraceSharpMass f ξ (c i * b i) :=
    (hB hcbpos hsmall.le).1.of_norm
  have hS : HasSum (fun ξ : Hₛ ↦ sLocalAnnularMass f ξ D (a i) (b i) (c i))
      (M (a i * b i) - ∑' ξ : Hₛ, sLocalTraceSharpMass f ξ (c i * b i)) := by
    refine (hs1.sub hs2.hasSum).congr_fun fun ξ ↦ ?_
    exact sLocalAnnularMass_eq f ξ D hD hDm hci hcai hbi
  simp only [Function.comp_apply]
  rw [hS.tsum_eq]
  ring

end RiemannMasullo.Isolated
