module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RadialPrimeTrace
import RiemannMasullo.ForMathlib.Analysis.Fourier.SpectralProbeRange
import RiemannMasullo.External.HardyCriticalLine.CriticalLineZeroInfinitude
import RiemannMasullo.Ch13_ZerosHecke.Targets

/-! # Simultaneous signed trace comparison at finitely many widths

The spectral observation vector records the full positive divisor, each retained
strip trace and the two polar moments. A critical-line zero contributes to all
positive widths with the same multiplicity. The two poles are separate atoms.
These vectors can be synthesized by smooth tests supported arbitrarily far out
on the positive log axis.
-/

@[expose] public noncomputable section

open Classical Filter MeasureTheory Set NumberField
open scoped ArithmeticFunction ContDiff NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false

local notation "D" => MeromorphicOn.divisor completedRiemannZeta univ
local notation "Z" => {z : ℂ // 0 < D z}
local notation "m(" z ")" => (D ((z : Z).val)).toNat
local notation "keep(" a ", " s ", " z ")" =>
  spectralStripMultiplicity a s ((z : Z).val.re - 1 / 2) (m(z))

private def observationFrequency : Z ⊕ Bool → ℂ
  | .inl z => z.val - 1 / 2
  | .inr false => -(1 / 2)
  | .inr true => 1 / 2

private theorem observationFrequency_injective : Function.Injective observationFrequency := by
  rintro (z | p) (u | q) h
  · exact congrArg Sum.inl (Subtype.ext (sub_left_inj.mp h))
  · have hh := congrArg Complex.re h
    have hstrip := abs_lt.mp (completedZetaZero_mem_centeredCriticalStrip z)
    cases q <;> norm_num [observationFrequency] at hh <;> linarith [hstrip.1, hstrip.2]
  · have hh := congrArg Complex.re h
    have hstrip := abs_lt.mp (completedZetaZero_mem_centeredCriticalStrip u)
    cases p <;> norm_num [observationFrequency] at hh <;> linarith [hstrip.1, hstrip.2]
  · cases p <;> cases q <;> first | rfl | norm_num [observationFrequency] at h

private theorem observationFrequency_discrete (z : ℂ) :
    ∀ᶠ u in 𝓝[≠] z, u ∉ range observationFrequency := by
  have hD := (MeromorphicOn.divisor completedRiemannZeta univ).eq_zero_codiscreteWithin
  have h := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.mp hD) (z + 1 / 2) (mem_univ _)
  rw [compl_univ, union_empty] at h
  have ht : Tendsto (fun u : ℂ ↦ u + 1 / 2) (𝓝[≠] z) (𝓝[≠] (z + 1 / 2)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · exact ((continuous_id.add continuous_const).tendsto z).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      exact fun h' ↦ hu (add_right_cancel h')
  have hp (a : ℂ) : ∀ᶠ u in 𝓝[≠] z, u ≠ a := by
    rcases eq_or_ne z a with rfl | ha
    · exact self_mem_nhdsWithin
    · exact mem_nhdsWithin_of_mem_nhds (isOpen_ne.mem_nhds ha)
  filter_upwards [ht.eventually h, hp (-(1 / 2)), hp (1 / 2)] with u hu hneg hpos
  rintro ⟨i, rfl⟩
  rcases i with ρ | p
  · change D (ρ.val - 1 / 2 + 1 / 2) = 0 at hu
    rw [sub_add_cancel] at hu
    exact ρ.property.ne' hu
  · cases p <;> contradiction

private theorem observationFrequency_re (i) : (observationFrequency i).re ≤ 1 / 2 := by
  rcases i with z | p
  · simpa [observationFrequency] using (abs_lt.mp (completedZetaZero_mem_centeredCriticalStrip z)).2.le
  · cases p <;> norm_num [observationFrequency]

private theorem exists_critical_divisor_site : ∃ z : Z, z.val.re = 1 / 2 := by
  obtain ⟨t, ht⟩ := HardyCriticalLine.positiveHardyZeroHeights_infinite.nonempty
  let z : ℂ := 1 / 2 + (t : ℂ) * Complex.I
  have hre : z.re = 1 / 2 := by simp [z]
  have hz : riemannZeta z = 0 := (HardyCriticalLine.hardyFunctionReal_eq_zero_iff t).mp ht.2
  have hn : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have ha := analyticOn_riemannZeta z hn
  have htwo : analyticOrderAt riemannZeta 2 = 0 :=
    analyticOrderAt_eq_zero.mpr (.inr (riemannZeta_ne_zero_of_one_le_re (by norm_num)))
  have hfin := analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (x := 2) (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
    (by simp) hn (by simp [htwo])
  obtain ⟨n, hor⟩ := ENat.ne_top_iff_exists.mp hfin
  have hn' : 0 < n := by
    rw [Nat.pos_iff_ne_zero]
    have := ha.analyticOrderAt_ne_zero.mpr hz
    rw [← hor] at this
    exact_mod_cast this
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hpos : 0 < D z := by
    rw [← divisor_rat_principal_eq_zeta, MeromorphicOn.divisor_apply
      (continuedCompletedHeckeL_spec _).1.meromorphicOn (mem_univ _),
      ← meromorphicOrderAt_finiteHeckeL_continuation _ hm (fun s ↦
        (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
          (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num),
      ha.meromorphicOrderAt_eq, ← hor, ENat.map_natCast, WithTop.untop₀_coe]
    exact_mod_cast hn'
  exact ⟨⟨z, hpos⟩, hre⟩

variable {κ : Type*}

private def traceObservation (a s : κ → ℝ) : Z ⊕ Bool → (Option κ ⊕ Bool) → ℂ
  | .inl z, .inl none => m(z)
  | .inl z, .inl (some k) => keep(a k, s k, z)
  | .inr p, .inr q => if p = q then 1 else 0
  | .inr _, .inl _ => 0
  | .inl _, .inr _ => 0

private def prescribedObservation (v P M : ℂ) : Option κ ⊕ Bool → ℂ
  | .inl _ => v
  | .inr false => M
  | .inr true => P

private theorem prescribedObservation_mem_span (a s : κ → ℝ) (ha : ∀ k, 0 < a k) (v P M : ℂ) :
    prescribedObservation (κ := κ) v P M ∈ Submodule.span ℂ (range (traceObservation a s)) := by
  obtain ⟨z, hz⟩ := exists_critical_divisor_site
  have hmul : (m(z) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Int.pos_iff_toNat_pos.mp z.property).ne'
  have hi (k : κ) : keep(a k, s k, z) = m(z) :=
    spectralStripMultiplicity_interior (by rw [hz, sub_self]; exact ⟨neg_lt_zero.mpr (ha k), ha k⟩) _ _
  let U := Submodule.span ℂ (range (traceObservation a s))
  have hat (i) : traceObservation a s i ∈ U := Submodule.subset_span (mem_range_self i)
  have h := U.add_mem (U.add_mem (U.smul_mem (v / (m(z) : ℂ)) (hat (.inl z)))
    (U.smul_mem M (hat (.inr false)))) (U.smul_mem P (hat (.inr true)))
  convert h using 1
  ext q
  rcases q with k | p
  · cases k with
    | none => simp [prescribedObservation, traceObservation, hmul]
    | some k => simp only [prescribedObservation, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        traceObservation, hi, mul_zero, add_zero, div_mul_cancel₀ _ hmul]
  · cases p <;> simp [prescribedObservation, traceObservation]

private theorem observation_summable (a s : κ → ℝ) (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    Summable (fun i ↦ bilateralLaplace H (observationFrequency i) • traceObservation a s i) := by
  apply Summable.sum _ _ (hasSum_fintype _).summable
  apply Pi.summable.mpr
  have h := (hasSum_zetaZeros_centeredVonMangoldt H hd hc hp).summable
  intro k
  rcases k with k | p
  · cases k with
    | none => simpa only [Function.comp_apply, Pi.smul_apply, smul_eq_mul, traceObservation,
        observationFrequency, mul_comm] using h
    | some k =>
      apply Summable.of_norm_bounded h.norm
      intro z
      change ‖bilateralLaplace H (z.val - 1 / 2) * (keep(a k, s k, z) : ℂ)‖ ≤ _
      rw [norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast, mul_comm]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact_mod_cast (show keep(a k, s k, z) ≤ m(z) by
        unfold spectralStripMultiplicity
        split
        · exact le_rfl
        split
        · exact min_le_left _ _
        · exact Nat.zero_le _)
  · exact (summable_zero : Summable (fun _ : Z ↦ (0 : ℂ))).congr (fun z ↦ by
      simp [Function.comp, traceObservation])

private theorem realize_trace_observation [Fintype κ] (a s : κ → ℝ) (B : ℝ) (H₀ : ℝ → ℂ)
    (hd₀ : ContDiff ℝ (∞) H₀) (hc₀ : HasCompactSupport H₀) (hp₀ : tsupport H₀ ⊆ Ioi 0)
    (o : Option κ ⊕ Bool → ℂ) (ho : o ∈ Submodule.span ℂ (range (traceObservation a s))) :
    ∃ H : ℝ → ℂ, ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioi 0 ∧
      EqOn H H₀ (Iic B) ∧
      HasSum (fun i ↦ bilateralLaplace H (observationFrequency i) • traceObservation a s i) o := by
  let W := Submodule.span ℂ (range (traceObservation a s))
  have h₀ := (observation_summable a s H₀ hd₀ hc₀ hp₀).hasSum
  let d := ∑' i, bilateralLaplace H₀ (observationFrequency i) • traceObservation a s i
  have hd : d ∈ W := tsum_mem W.isClosed_of_finiteDimensional fun i ↦
    W.smul_mem _ (Submodule.subset_span (mem_range_self i))
  obtain ⟨G, hg, hgc, hB, hG⟩ := (exists_tail_probe_iff_mem_span observationFrequency
    (traceObservation a s) (max B 0) observationFrequency_injective observationFrequency_discrete
    observationFrequency_re (fun H hh hc hp ↦ observation_summable a s H hh hc
      (hp.trans (Ioi_subset_Ioi (le_max_right _ _)))) (o - d)).mpr (W.sub_mem ho hd)
  refine ⟨fun x ↦ H₀ x + G x, hd₀.add hg, hc₀.add hgc,
    (tsupport_add H₀ G).trans (union_subset hp₀ (hB.trans (Ioi_subset_Ioi (le_max_right _ _)))),
    fun x hx ↦ ?_, ?_⟩
  · have hn : x ∉ tsupport G := fun h ↦ (not_lt_of_ge (hx.trans (le_max_left _ _))) (hB h)
    exact add_eq_left.mpr (image_eq_zero_of_notMem_tsupport hn)
  · have h := h₀.add hG
    change HasSum _ (d + (o - d)) at h
    rw [add_sub_cancel] at h
    apply h.congr_fun
    intro i
    rw [bilateralLaplace_add hd₀.continuous hg.continuous hc₀ hgc, add_smul]

private theorem full_observation (a s : κ → ℝ) (H : ℝ → ℂ) (o : Option κ ⊕ Bool → ℂ)
    (h : HasSum (fun i ↦ bilateralLaplace H (observationFrequency i) • traceObservation a s i) o)
    (k : Option κ) :
    HasSum (fun z : Z ↦ bilateralLaplace H (z.val - 1 / 2) * traceObservation a s (.inl z) (.inl k))
      (o (.inl k)) := by
  let f (i : Z ⊕ Bool) := bilateralLaplace H (observationFrequency i) * traceObservation a s i (.inl k)
  have hf : HasSum f (o (.inl k)) := Pi.hasSum.mp h (.inl k)
  have hz (i : Z ⊕ Bool) (hi : i ∉ range (Sum.inl : Z → Z ⊕ Bool)) : f i = 0 := by
    cases i with
    | inl z => exact (hi (mem_range_self z)).elim
    | inr b => simp [f, traceObservation]
  exact (Sum.inl_injective.hasSum_iff hz).mpr hf

private theorem pole_observation (a s : κ → ℝ) (H : ℝ → ℂ) (o : Option κ ⊕ Bool → ℂ)
    (h : HasSum (fun i ↦ bilateralLaplace H (observationFrequency i) • traceObservation a s i) o)
    (b : Bool) : bilateralLaplace H (observationFrequency (.inr b)) = o (.inr b) := by
  let f (i : Z ⊕ Bool) := bilateralLaplace H (observationFrequency i) * traceObservation a s i (.inr b)
  have hf : HasSum f (o (.inr b)) := Pi.hasSum.mp h (.inr b)
  rw [← hf.tsum_eq, tsum_eq_single (.inr b)]
  · simp [f, traceObservation]
  · rintro (z | p) hne
    · simp [f, traceObservation]
    · have hb : p ≠ b := fun he ↦ hne (congrArg Sum.inr he)
      simp [f, traceObservation, hb]

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instFiniteCompletionUnitsLocallyCompactSec4b instSIdeleQuotientMeasurableSpaceSec1
  instNormOneSIdeleQuotientMeasurableSpaceSec1 instSIdeleLocallyCompactSec1 instSIdeleT2Sec4

local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Pl" => IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)
local notation "V" => (((normOneIdeleClassTamagawaMeasure ℚ) univ).toReal : ℂ)
local notation "band(" ha ")" => (neg_nonpos.mpr ha |>.trans ha)
local notation "Q(" ha ", " hs ")" => spectralSobolevQuotient ℚ (1 / 2) (band(ha)) (zero_lt_one.trans hs).le
local notation "radial(" φ ", " H ")" => ∀ x : Cℚ, (φ : BruhatCompactSupport Cℚ).val x =
  (H : ℝ → ℂ) (Real.log ((ideleClassNorm ℚ x : ℝ≥0) : ℝ))
local notation "lifts(" S ", " f ", " φ ")" => ∀ g : (SAdeleRing ℚ S)ˣ,
  HasSum (fun ξ : sProjectedDiagonal ℚ S ↦ (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ).val (ξ.val * g))
    ((φ : BruhatCompactSupport Cℚ).val (QuotientGroup.mk (sIdeleInsertion ℚ S g)))
local notation "pole(" φ ", " z ")" => modulatedFourierMellin (continuousIdeleClassNorm ℚ) univ
  ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  (ideleClassTamagawaMeasure ℚ) (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist 1 z)
local notation "rep(" T ", " φ ", " ha ", " hs ")" =>
  (T : nuclearEndomorphisms Q(ha, hs)).val =
    spectralConvolution (F := ℚ) (1 / 2) (band(ha)) (zero_lt_one.trans hs).le φ

/-- A positive-log profile agreeing with the given one through height B, its finite
periodized lift, two global Mellin poles, the polar-corrected sharp local limit and
the Hilbert traces of its strip convolution at the specified widths and orders.
All scalar entries are normalized by the volume of the norm-one classes. -/
def RealizableRadialTraceData (H₀ : ℝ → ℂ) (B : ℝ) (a s : κ → ℝ)
    (v P M : ℂ) (q : κ → ℂ) : Prop :=
  ∃ (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ) (S : Finset Pl)
    (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
    ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioi 0 ∧ EqOn H H₀ (Iic B) ∧
    radial(φ, H) ∧ lifts(S, f, φ) ∧ pole(φ, (1 / 2)) = V * P ∧ pole(φ, (-(1 / 2))) = V * M ∧
    centeredVonMangoldtValue H = v ∧
    (∀ k, HasSum (fun z : Z ↦ (keep(a k, s k, z) : ℂ) * bilateralLaplace H (z.val - 1 / 2)) (q k)) ∧
    Tendsto (fun R : ℝ ↦ -rationalCorrectedSharpMass f R) atTop (𝓝 (V * v)) ∧
    ∀ (k : κ) (ha : 0 ≤ a k) (hs : 1 < s k) (T : nuclearEndomorphisms Q(ha, hs)),
      rep(T, φ, ha, hs) → hilbertTrace T = V * q k

private theorem trace_data_of_mem_span [Fintype κ] (H₀ : ℝ → ℂ) (hd₀ : ContDiff ℝ (∞) H₀)
    (hc₀ : HasCompactSupport H₀) (hp₀ : tsupport H₀ ⊆ Ioi 0) (B : ℝ) (a s : κ → ℝ)
    (o : Option κ ⊕ Bool → ℂ) (ho : o ∈ Submodule.span ℂ (range (traceObservation a s))) :
    RealizableRadialTraceData H₀ B a s (o (.inl none)) (o (.inr true)) (o (.inr false))
      (fun k ↦ o (.inl (some k))) := by
  obtain ⟨H, hH, hc, hp, hB, hobs⟩ := realize_trace_observation a s B H₀ hd₀ hc₀ hp₀ o ho
  obtain ⟨l, u, hlu⟩ := bddBelow_bddAbove_iff_subset_Icc.mp ⟨hc.bddBelow, hc.bddAbove⟩
  obtain ⟨S, hS⟩ := exists_radialSharpMass_stripTrace_comparison l u
  obtain ⟨φ, f, hφ, hf, hlim, _⟩ := hS H hH hc hp hlu
  have hM (z : ℂ) : pole(φ, z) = V * bilateralLaplace H z := by
    rw [normTest_mellin H hH.continuous φ hφ]
    have h := grh_shift_integral H hH.continuous (fun _ ↦ (1 : ℂ)) (fun _ ↦ rfl) 0 z
    simpa [bilateralLaplace] using congrArg (fun u : ℂ ↦ V * u) h
  have hv : centeredVonMangoldtValue H = o (.inl none) := by
    apply (hasSum_zetaZeros_centeredVonMangoldt H hH hc hp).unique
    simpa only [traceObservation, mul_comm] using full_observation a s H o hobs none
  refine ⟨H, φ, S, f, hH, hc, hp, hB, hφ, hf,
    (hM _).trans (congrArg _ (pole_observation a s H o hobs true)),
    (hM _).trans (congrArg _ (pole_observation a s H o hobs false)), hv, ?_, hv ▸ hlim, ?_⟩
  · intro k
    simpa only [traceObservation, mul_comm] using full_observation a s H o hobs (some k)
  intro k ha hs T hT
  apply (hasSum_radialStripTrace H hH.continuous φ hφ ha hs T hT).unique
  apply ((full_observation a s H o hobs (some k)).mul_left V).congr_fun
  intro z
  simp only [traceObservation, mul_comm]

/-- Paper: §12.3, p. 514. Given any finite family of positive half-widths and
Sobolev orders above one, the signed sharp local limit and all quotient traces
can be made exactly equal to any prescribed value, with independently prescribed
polar moments. The test can simultaneously agree with an arbitrary initial
positive-log profile on the entire half-line through B. -/
theorem exists_simultaneous_signed_radial_trace [Fintype κ] (H₀ : ℝ → ℂ)
    (hd₀ : ContDiff ℝ (∞) H₀) (hc₀ : HasCompactSupport H₀) (hp₀ : tsupport H₀ ⊆ Ioi 0)
    (B : ℝ) (a s : κ → ℝ) (ha : ∀ k, 0 < a k) (v P M : ℂ) :
    RealizableRadialTraceData H₀ B a s v P M (fun _ ↦ v) :=
  trace_data_of_mem_span H₀ hd₀ hc₀ hp₀ B a s _ (prescribedObservation_mem_span a s ha v P M)

private theorem retained_le_full (a s : ℝ) (z : Z) : keep(a, s, z) ≤ m(z) := by
  unfold spectralStripMultiplicity
  split
  · exact le_rfl
  split
  · exact min_le_left _ _
  · exact Nat.zero_le _

private theorem single_trace_data_of_loss (H₀ : ℝ → ℂ) (hd₀ : ContDiff ℝ (∞) H₀)
    (hc₀ : HasCompactSupport H₀) (hp₀ : tsupport H₀ ⊆ Ioi 0) (B a s : ℝ) (ha : 0 < a)
    (z : Z) (hz : keep(a, s, z) < m(z)) (v q P M : ℂ) :
    RealizableRadialTraceData H₀ B (fun _ : Unit ↦ a) (fun _ ↦ s) v P M (fun _ ↦ q) := by
  let f := traceObservation (fun _ : Unit ↦ a) (fun _ ↦ s)
  let m : ℂ := m(z)
  let k : ℂ := keep(a, s, z)
  have hkm : k - m ≠ 0 := sub_ne_zero.mpr (by dsimp [k, m]; exact_mod_cast hz.ne)
  let d := (q - v) / (k - m)
  have he : d * (k - m) = q - v := div_mul_cancel₀ _ hkm
  let o := prescribedObservation (κ := Unit) (v - d * m) P M + d • f (.inl z)
  have ho : o ∈ Submodule.span ℂ (range f) := Submodule.add_mem _
    (prescribedObservation_mem_span _ _ (fun _ ↦ ha) _ P M)
    (Submodule.smul_mem _ _ (Submodule.subset_span (mem_range_self _)))
  have h₀ : o (.inl none) = v := by change v - d * m + d * m = v; ring
  have hq (u : Unit) : o (.inl (some u)) = q := by
    change v - d * m + d * k = q
    linear_combination he
  have hP : o (.inr true) = P := by change P + d * 0 = P; ring
  have hM : o (.inr false) = M := by change M + d * 0 = M; ring
  simpa only [h₀, hP, hM, hq] using trace_data_of_mem_span H₀ hd₀ hc₀ hp₀ B
    (fun _ : Unit ↦ a) (fun _ ↦ s) o ho

/-- Paper: §12.3, p. 514. At one fixed positive width the realizable signed
trace data have a dichotomy. Equal local and quotient values are always attainable.
Distinct values are attainable exactly when a positive divisor site loses at least
one jet, including partial loss on an edge. In that case the local value, quotient
value and both polar moments are independently arbitrary, with the prescribed
initial profile fixed through any finite log cutoff. -/
theorem realizable_singleWidthTrace_iff (H₀ : ℝ → ℂ) (hd₀ : ContDiff ℝ (∞) H₀)
    (hc₀ : HasCompactSupport H₀) (hp₀ : tsupport H₀ ⊆ Ioi 0) (B a s : ℝ) (ha : 0 < a)
    (v q P M : ℂ) :
    RealizableRadialTraceData H₀ B (fun _ : Unit ↦ a) (fun _ ↦ s) v P M (fun _ ↦ q) ↔
      q = v ∨ ∃ z : Z, keep(a, s, z) < m(z) := by
  constructor
  · rintro ⟨H, _, _, _, hH, hc, hp, _, _, _, _, _, hv, hsum, _⟩
    by_cases h : ∃ z : Z, keep(a, s, z) < m(z)
    · exact Or.inr h
    left
    have he (z : Z) : keep(a, s, z) = m(z) := le_antisymm (retained_le_full a s z)
      (le_of_not_gt (fun hz ↦ h ⟨z, hz⟩))
    have hq := hsum ()
    simp only [he] at hq
    exact (hq.unique (hasSum_zetaZeros_centeredVonMangoldt H hH hc hp)).trans hv
  · rintro (rfl | ⟨z, hz⟩)
    · exact exists_simultaneous_signed_radial_trace H₀ hd₀ hc₀ hp₀ B _ _ (fun _ ↦ ha) _ _ _
    · exact single_trace_data_of_loss H₀ hd₀ hc₀ hp₀ B a s ha z hz v q P M

private theorem exterior_of_order_one {a : ℝ} (H : ℝ → ℂ) {v : ℂ}
    (hfull : HasSum (fun z : Z ↦ (m(z) : ℂ) * bilateralLaplace H (z.val - 1 / 2)) v)
    (hopen : HasSum (fun z : Z ↦ (keep(a, 1, z) : ℂ) * bilateralLaplace H (z.val - 1 / 2)) v) :
    HasSum (fun z : {z : Z // a ≤ |z.val.re - 1 / 2|} ↦
      (m(z.val) : ℂ) * bilateralLaplace H (z.val.val - 1 / 2)) 0 := by
  apply (hasSum_subtype_iff_indicator (s := {z : Z | a ≤ |z.val.re - 1 / 2|})
    (f := fun z : Z ↦ (m(z) : ℂ) * bilateralLaplace H (z.val - 1 / 2))).mpr
  rw [← sub_self v]
  apply (hfull.sub hopen).congr_fun
  intro z
  by_cases he : a ≤ |z.val.re - 1 / 2|
  · have hi : ¬ (-a < z.val.re - 1 / 2 ∧ z.val.re - 1 / 2 < a) := fun h ↦ he.not_gt (abs_lt.mpr h)
    rw [Set.indicator_of_mem (show z ∈ {z : Z | a ≤ |z.val.re - 1 / 2|} from he)]
    simp only [spectralStripMultiplicity, ite_eq_right hi, spectralBoundaryMultiplicity,
      sub_self, zero_div, Nat.ceil_zero, Nat.min_zero, ite_self, Nat.cast_zero, zero_mul, sub_zero]
  · have hi := abs_lt.mp (lt_of_not_ge he)
    rw [Set.indicator_of_notMem (show z ∉ {z : Z | a ≤ |z.val.re - 1 / 2|} from he)]
    simp only [spectralStripMultiplicity, ite_eq_left hi, sub_self]

local notation "sectionRows(" τ ")" => {ψ : PontryaginDual Cℚ // ∀ t : ℝ≥0ˣ, ψ (τ t) = 1}
local notation "extSites(" τ ", " a ")" => {y : sectionRows(τ) × ℂ // 0 <
  MeromorphicOn.divisor (continuedCompletedHeckeL y.1.val) univ y.2 ∧ a ≤ |y.2.re - 1 / 2|}
local notation "extTerm(" φ ", " y ")" =>
  ((MeromorphicOn.divisor (continuedCompletedHeckeL (y).val.1.val) univ (y).val.2 : ℤ) : ℂ) *
    modulatedFourierMellin (continuousIdeleClassNorm ℚ) univ
      ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩ (ideleClassTamagawaMeasure ℚ)
      (φ : BruhatCompactSupport Cℚ).val (ideleClassNormTwist (y).val.1.val ((y).val.2 - 1 / 2))

/-- Paper: §12.3, p. 514, and Theorem 12.5.1.1, pp. 519–520. For any finite list
of positive widths one test meets the signed local-to-Hilbert comparison and the
paper's full exterior-zero cancellation, for every choice of norm section. Even
when zeros lie exactly on a strip edge, the cancellation includes their full
multiplicities, while the Hilbert trace counts the admitted boundary jets.
Both polar moments, the common trace value, and the initial log profile are prescribed. -/
theorem exists_signed_trace_with_exterior_cancellation [Fintype κ] (H₀ : ℝ → ℂ)
    (hd₀ : ContDiff ℝ (∞) H₀) (hc₀ : HasCompactSupport H₀) (hp₀ : tsupport H₀ ⊆ Ioi 0)
    (B : ℝ) (a s : κ → ℝ) (ha : ∀ k, 0 < a k) (v P M : ℂ) :
    ∃ (H : ℝ → ℂ) (φ : BruhatCompactSupport Cℚ) (S : Finset Pl)
      (f : BruhatCompactSupport (SAdeleRing ℚ S)ˣ),
      ContDiff ℝ (∞) H ∧ HasCompactSupport H ∧ tsupport H ⊆ Ioi 0 ∧ EqOn H H₀ (Iic B) ∧
      radial(φ, H) ∧ lifts(S, f, φ) ∧ pole(φ, (1 / 2)) = V * P ∧ pole(φ, (-(1 / 2))) = V * M ∧
      centeredVonMangoldtValue H = v ∧
      Tendsto (fun R : ℝ ↦ -rationalCorrectedSharpMass f R) atTop (𝓝 (V * v)) ∧
      (∀ (k : κ) (hs : 1 < s k) (T : nuclearEndomorphisms Q((ha k).le, hs)),
        rep(T, φ, (ha k).le, hs) → hilbertTrace T = V * v) ∧
      ∀ (τ : ℝ≥0ˣ →ₜ* Cℚ), Function.RightInverse τ (ideleClassNorm ℚ) →
        ∀ k, HasSum (fun y : extSites(τ, a k) ↦ extTerm(φ, y)) 0 := by
  let widths (i : Bool × κ) := a i.2
  let orders (i : Bool × κ) := if i.1 then s i.2 else 1
  obtain ⟨H, φ, S, f, hd, hc, hp, hB, hφ, hf, hP, hM, hv, hspec, hlim, hT⟩ :=
    exists_simultaneous_signed_radial_trace H₀ hd₀ hc₀ hp₀ B widths orders (fun i ↦ ha i.2) v P M
  refine ⟨H, φ, S, f, hd, hc, hp, hB, hφ, hf, hP, hM, hv, hlim, ?_, ?_⟩
  · intro k hs T h
    exact hT (true, k) (ha k).le hs T h
  intro τ hτ k
  apply (hasSum_radialDivisor_restrict_iff {z | a k ≤ |z.re - 1 / 2|} H hd.continuous φ hφ τ hτ _).mpr
  have h := exterior_of_order_one H (hv ▸ hasSum_zetaZeros_centeredVonMangoldt H hd hc hp)
    (hspec (false, k))
  rw [← mul_zero (V : ℂ)]
  apply HasSum.mul_left
  exact h

end RiemannMasullo
