module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RationalCentralBruhat
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCentralHeatFloor
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_FlatCentralHeatLimit

/-!
# The heated Bruhat trace across norm one on the rational order-zero level

For a smooth real test supported on a reciprocal dilation window, the sharp
finite part acquires the second derivative of the logarithmic profile at zero,
multiplied by the limit of the variance parameter times `log (B * L)`. This
coefficient uses the total variance `2 * τ` of the two Gaussian factors. The
same formula holds for the actual quotient Haar diagonal at positive variance.

The logarithmic heat prescription and the cold crossing formula are due to
mrshu (#7354, #7693). The ordinary level projection uses thierryaaron's
real-even model (#7651, #7681) and the actual Chapter 9 order-zero operator from #7705.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set ProbabilityTheory
open scoped CompactlySupported NumberField.AdeleRing NNReal ENNReal Topology

namespace RiemannMasullo.AnnularBand
open RatEmptyRealLevelBridge

set_option maxSynthPendingDepth 8
set_option quotPrecheck false
attribute [local instance] RiemannMasullo.instSIdeleQuotientMeasurableSpaceSec1

local notation "J" => SIdeleQuotient ℚ ∅
local notation "m" => continuousSIdeleQuotientNorm ℚ ∅
local notation "R(" g ")" => (((m g).val : ℝ))
local notation "μ" => sLocalQuotientTamagawaMeasure ℚ ∅
local notation "ν₀" => (μ).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (Real.log (R(g)))))
local notation "Hq" => Lp ℂ 2 ν₀
local notation "ν₊" => volume.restrict (Ioi (0 : ℝ))
local notation "H₊" => Lp ℂ 2 ν₊
local notation "posR(" g ")" => NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (m g).ne_zero)

local instance : BorelSpace J := ⟨rfl⟩
local instance : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
local instance : T2Space J := by
  have := isClosed_sProjectedDiagonal (F := ℚ) (S := ∅)
  exact inferInstanceAs (T2Space (_ ⧸ _))
local instance : SecondCountableTopology J := by
  let (v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) : ProperSpace (v.val.adicCompletion ℚ) :=
    properSpace_adicCompletion v.val
  let (w : InfinitePlace ℚ) : SecondCountableTopology w.Completion :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  let : SecondCountableTopology (SAdeleRing ℚ ∅) := inferInstanceAs (SecondCountableTopology
    (((w : InfinitePlace ℚ) → w.Completion) × ((v : (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))) → v.val.adicCompletion ℚ)))
  let : SecondCountableTopology (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).1.secondCountableTopology
  infer_instance
local instance : LocallyCompactSpace J := by
  let : LocallyCompactSpace (SAdeleRing ℚ ∅)ˣ := (sIdeleGroup_description ℚ ∅).2.2.1
  exact inferInstanceAs (LocallyCompactSpace (_ ⧸ _))
local instance : (μ).IsHaarMeasure := (sLocalQuotientTamagawaMeasure_isWeil (F := ℚ) (S := ∅)).1

open FlatPolar

/-- Zero-variance heat on the quotient is the identity on every nuclear endomorphism. -/
theorem quotientLogHeatSandwich_zero (T : nuclearEndomorphisms Hq) :
    quotientLogHeatSandwich 0 T = T := by
  have h (v : Hq) : quotientLogHeat 0 v = v := by
    change orderZeroHalfTwist (logHeat 0 (orderZeroHalfTwist.symm v)) = v
    rw [logHeat_apply, gaussianReal_zero_var, integral_dirac, logDilation_zero,
      LinearIsometryEquiv.apply_symm_apply]
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro v
  change quotientLogHeat 0 (T.val (quotientLogHeat 0 v)) = T.val v
  exact (h _).trans (congrArg (fun x : Hq ↦ T.val x) (h v))

/-- A radial quotient test and its norm profile give identical finite heat traces,
including the two genuine orthogonal projections and both translations. -/
theorem hilbertTrace_quotientBruhat_heat_eq_physical {B : ℝ} (hB : 0 < B)
    (h L : ℝ) (τ : ℝ≥0) (ψ : BruhatCompactSupport J) (φ : C_c(ℝ≥0ˣ, ℂ))
    (hφ : ∀ q : J, φ (m q) = ψ.val q) :
    hilbertTrace (quotientLogHeatSandwich τ (quotientBruhatLevelCompressionNuclear hB h L ψ)) =
    hilbertTrace (logHeatSandwich τ (meanZeroCompactCosineTraceOperator h L B φ)) := by
  obtain ⟨φ', hp, _, ha⟩ := exists_rayTest_support_hardySobolevTestAction_eq ψ univ isClosed_univ
    (fun q _ ↦ mem_univ (R(q)))
  have hsame : φ' = φ := by
    ext t
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
    have hqt : m (σ t) = t := hσ t
    exact hqt ▸ (hp (σ t)).trans (hφ (σ t)).symm
  subst φ'
  have hN : quotientBruhatLevelCompressionNuclear hB h L ψ = quotientMeanZeroCompactNuclear hB h L φ := by
    apply Subtype.ext
    exact congrArg (fun A : Hq →L[ℂ] Hq ↦ (orderZeroLevelProjection B).comp
      ((modulatedAbsoluteCutoffOperator m ν₀ (Ioc h L) measurableSet_Ioc).comp
        (A.comp (orderZeroLevelProjection B)))) ha
  rw [hN, hilbertTrace_quotientLogHeatSandwich_meanZeroCompact]

/-- On any varying band, removing the polar rank changes the Gaussian displacement
by a quantity tending to zero with the variance, without a rate tying it to the band. -/
theorem tendsto_meanZero_displacement_sub_ambient
    {ι : Type*} {l : Filter ι} {B h L : ι → ℝ} {τ : ι → ℝ≥0}
    (hB : ∀ i, 0 < B i) (hτ : Tendsto τ l (𝓝 0)) (φ : C_c(ℝ≥0ˣ,ℂ)) :
    let t (i : ι) (v : ℝ≥0) := hilbertTrace (logHeatSandwich v
      (meanZeroCompactCosineTraceOperator (h i) (L i) (B i) φ))
    let a (i : ι) (v : ℝ≥0) := hilbertTrace (logHeatSandwich v
      (compactCosineTraceOperator 0 (B i) (h i) (L i) φ))
    Tendsto (fun i ↦ t i (τ i) - t i 0 - (a i (τ i) - a i 0)) l (𝓝 0) := by
  intro t a
  have ht : Tendsto (fun i ↦ Real.sqrt (Real.sqrt (((τ i + τ i : ℝ≥0) : ℝ)))) l (𝓝 0) := by
    simpa only [Function.comp_def, NNReal.coe_zero, add_zero, Real.sqrt_zero] using
      ((Real.continuous_sqrt.tendsto _).comp ((Real.continuous_sqrt.tendsto _).comp
        (NNReal.continuous_coe.tendsto _ |>.comp (hτ.add hτ))))
  apply squeeze_zero_norm (fun i ↦ ?_) (by simpa using (tendsto_const_nhds (x := 2*‖compactDilationAction φ‖)).mul ht)
  have h := centralWindow_meanZeroHeat_cold_difference (hB i) (h i) (L i) (τ i) φ
  have he : t i (τ i)-t i 0-(a i (τ i)-a i 0) = t i (τ i)-a i (τ i)-(t i 0-a i 0) := by abel
  exact (he ▸ h)

open scoped ContDiff

set_option maxHeartbeats 700000 in
/-- Finite rank removal, the moving floor and the radial Gaussian displacement
combine with the exact zero-heat finite part at the level of native operators. -/
theorem tendsto_native_central_heat_of_ambient
    {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) {w : ℝ → ℝ} (hw : ContDiff ℝ (∞) w)
    (hs : ∀ r : ℝ, r ∉ Icc (centralDilation δ) (centralDilation (-δ)) → w r = 0)
    (ψ : BruhatCompactSupport J) (hψ : ∀ q : J, ψ.val q = (w (R(q)) : ℂ))
    (φ : C_c(ℝ≥0ˣ,ℂ)) (hφ : ∀ q : J, φ (m q) = ψ.val q)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {B h L : ι → ℝ} {τ : ι → ℝ≥0}
    (hB : ∀ i, 0 < B i) (hL : ∀ i, 0 < L i)
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop) (hτ : Tendsto τ l (𝓝 0)) {c : ℝ}
    (hamb : Tendsto (fun i ↦ hilbertTrace (logHeatSandwich (τ i) (compactCosineTraceOperator 0 (B i) 0 (L i) φ)) -
      hilbertTrace (logHeatSandwich 0 (compactCosineTraceOperator 0 (B i) 0 (L i) φ))) l (𝓝 (c : ℂ)))
    (hfloor : Tendsto (fun i ↦ hilbertTrace (logHeatSandwich (τ i)
      (meanZeroCompactCosineTraceOperator 0 (L i) (B i) φ)) - hilbertTrace (logHeatSandwich (τ i)
      (meanZeroCompactCosineTraceOperator (h i) (L i) (B i) φ))) l (𝓝 0)) :
    Tendsto (fun i ↦ hilbertTrace (quotientLogHeatSandwich (τ i)
        (quotientBruhatLevelCompressionNuclear (hB i) (h i) (L i) ψ)) -
      ((w 1 * Real.log (B i * L i) : ℝ) : ℂ)) l
        (𝓝 ((actualCentralTraceFinitePart δ w : ℂ) + (c : ℂ))) := by
  let m₀ i v := hilbertTrace (logHeatSandwich v (meanZeroCompactCosineTraceOperator 0 (L i) (B i) φ))
  let a₀ i v := hilbertTrace (logHeatSandwich v (compactCosineTraceOperator 0 (B i) 0 (L i) φ))
  let mₕ i := hilbertTrace (logHeatSandwich (τ i) (meanZeroCompactCosineTraceOperator (h i) (L i) (B i) φ))
  let x₀ i := ((w 1 * Real.log (B i * L i) : ℝ) : ℂ)
  have hpolar : Tendsto (fun i ↦ m₀ i (τ i) - m₀ i 0 - (a₀ i (τ i) - a₀ i 0)) l (𝓝 0) :=
    tendsto_meanZero_displacement_sub_ambient (h := fun _ ↦ 0) hB hτ φ
  change Tendsto (fun i ↦ a₀ i (τ i) - a₀ i 0) l (𝓝 (c:ℂ)) at hamb
  change Tendsto (fun i ↦ m₀ i (τ i) - mₕ i) l (𝓝 0) at hfloor
  obtain ⟨ψ',hψ',hc⟩ := exists_bruhatTest_cold_centralFinitePart hδ0 hδ1 hw hs
  have he : ψ' = ψ := Subtype.ext (funext fun q ↦ (hψ' q).trans (hψ q).symm)
  subst ψ'
  have h₀ : Tendsto (fun i ↦ m₀ i 0 - x₀ i) l (𝓝 (actualCentralTraceFinitePart δ w : ℂ)) := by
    apply (hc hB hL hBL).congr
    intro i
    exact congrArg (fun x : ℂ ↦ x - x₀ i)
      ((congrArg hilbertTrace (quotientLogHeatSandwich_zero _)).symm.trans
        (hilbertTrace_quotientBruhat_heat_eq_physical (hB i) 0 (L i) 0 ψ φ hφ))
  have hj := ((h₀.add hamb).add hpolar).sub hfloor
  simp only [add_zero, sub_zero] at hj
  refine hj.congr fun i ↦ ?_
  rw [hilbertTrace_quotientBruhat_heat_eq_physical (hB i) (h i) (L i) (τ i) ψ φ hφ]
  change (m₀ i 0 - x₀ i + (a₀ i (τ i) - a₀ i 0) +
    (m₀ i (τ i) - m₀ i 0 - (a₀ i (τ i) - a₀ i 0))) - (m₀ i (τ i)-mₕ i) = mₕ i-x₀ i
  abel

open scoped ContDiff
open RatEmptyRealLevelBridge ThroughOneStability
open FlatPolar

/-- At the rational real place and order zero, the native Chapter 9 Bruhat
compression has the sharp reciprocal-window finite part plus the logarithmic
curvature of the radial test times the limiting variance--cutoff product. -/
theorem tendsto_quotientBruhatLevel_heatTrace_centralFinitePart {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {w : ℝ → ℝ} (hw : ContDiff ℝ (∞) w)
    (hs : ∀ r : ℝ, r ∉ Icc (centralDilation δ) (centralDilation (-δ)) → w r = 0)
    (ψ : BruhatCompactSupport J) (hψ : ∀ q : J, ψ.val q = (w (R(q)) : ℂ))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {B h L : ι → ℝ} {τ : ι → ℝ≥0} {κ : ℝ}
    (hB : ∀ i, 0 < B i) (hL : ∀ i, 0 < L i) (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ h i ≤ L i)
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hτ : Tendsto τ l (𝓝 0))
    (hκ : Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 κ)) :
    Tendsto (fun i ↦ hilbertTrace (quotientLogHeatSandwich (τ i)
      (quotientBruhatLevelCompressionNuclear (hB i) (h i) (L i) ψ)) -
      ((w 1 * Real.log (B i * L i) : ℝ) : ℂ)) l
      (𝓝 ((actualCentralTraceFinitePart δ w + κ * (deriv w 1 + deriv (deriv w) 1) : ℝ) : ℂ)) := by
  obtain ⟨φ, hφ, _, _⟩ := exists_rayTest_support_hardySobolevTestAction_eq ψ univ isClosed_univ
    (fun _ _ ↦ mem_univ _)
  have hφw (u : ℝ≥0ˣ) : φ u = (w (u.val : ℝ) : ℂ) := by
    obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section ℚ ∅
    have he : m (σ u) = u := hσ u
    simpa only [he] using (hφ (σ u)).trans (hψ (σ u))
  rw [Complex.ofReal_add]
  apply tendsto_native_central_heat_of_ambient hδ0 hδ1 hw hs ψ hψ φ hφ hB hL hBL hτ
  · exact tendsto_ambientHeat_central_displacement hδ0 hδ1 hw
      (by simpa only [centralDilation,sub_eq_add_neg] using hs) φ hφw hB
      (fun i ↦ (hL i).le) hBL hτ hκ
  · exact tendsto_meanZero_heatTrace_remove_spatialFloor hB hbox hBh hτ φ

/-- At positive variance the integral of the actual Chapter 9 kernel on the
quotient Haar diagonal has the same centered limit as its Hilbert trace. -/
theorem tendsto_quotientBruhatLevel_haarDiagonal_centralFinitePart {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {w : ℝ → ℝ} (hw : ContDiff ℝ (∞) w)
    (hs : ∀ r : ℝ, r ∉ Icc (centralDilation δ) (centralDilation (-δ)) → w r = 0)
    (ψ : BruhatCompactSupport J) (hψ : ∀ q : J, ψ.val q = (w (R(q)) : ℂ))
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {B h L : ι → ℝ} {τ : ι → ℝ≥0} {κ : ℝ}
    (hB : ∀ i, 0 < B i) (hL : ∀ i, 0 < L i) (hbox : ∀ᶠ i in l, 0 ≤ h i ∧ h i ≤ L i)
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop)
    (hBh : Tendsto (fun i ↦ B i * h i) l (𝓝 0)) (hτ : Tendsto τ l (𝓝 0))
    (hκ : Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 κ))
    (hpos : ∀ᶠ i in l, 0 < τ i) :
    Tendsto (fun i ↦ (∫ q : J, quotientLogHaarHeatKernel (τ i)
      (quotientBruhatLevelCompression (B i) (h i) (L i) ψ) q q ∂μ) -
      ((w 1 * Real.log (B i * L i) : ℝ) : ℂ)) l
      (𝓝 ((actualCentralTraceFinitePart δ w + κ * (deriv w 1 + deriv (deriv w) 1) : ℝ) : ℂ)) := by
  apply (tendsto_quotientBruhatLevel_heatTrace_centralFinitePart hδ0 hδ1 hw hs ψ hψ
    hB hL hbox hBL hBh hτ hκ).congr'
  filter_upwards [hpos] with i hi
  exact congrArg (fun z : ℂ ↦ z - ((w 1 * Real.log (B i * L i) : ℝ) : ℂ))
    (quotientLogHaarHeatKernel_diagonal_trace hi
      (quotientBruhatLevelCompressionNuclear (hB i) (h i) (L i) ψ)).2.symm

/-- Every smooth real radial test on the reciprocal window determines a single
genuine quotient Bruhat test for all positive-heat diagonal limits. -/
theorem exists_bruhatTest_haarDiagonal_centralFinitePart {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) {w : ℝ → ℝ} (hw : ContDiff ℝ (∞) w)
    (hs : ∀ r : ℝ, r ∉ Icc (centralDilation δ) (centralDilation (-δ)) → w r = 0) :
    ∃ ψ : BruhatCompactSupport J, (∀ q : J, ψ.val q = (w (R(q)) : ℂ)) ∧
      ∀ {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {B h L : ι → ℝ} {τ : ι → ℝ≥0} {κ : ℝ}
        (_hB : ∀ i, 0 < B i) (_hL : ∀ i, 0 < L i), (∀ᶠ i in l, 0 ≤ h i ∧ h i ≤ L i) →
        Tendsto (fun i ↦ B i * L i) l atTop → Tendsto (fun i ↦ B i * h i) l (𝓝 0) →
        Tendsto τ l (𝓝 0) → Tendsto (fun i ↦ (τ i : ℝ) * Real.log (B i * L i)) l (𝓝 κ) →
        (∀ᶠ i in l, 0 < τ i) →
        Tendsto (fun i ↦ (∫ q : J, quotientLogHaarHeatKernel (τ i)
          (quotientBruhatLevelCompression (B i) (h i) (L i) ψ) q q ∂μ) -
          ((w 1 * Real.log (B i * L i) : ℝ) : ℂ)) l
          (𝓝 ((actualCentralTraceFinitePart δ w + κ * (deriv w 1 + deriv (deriv w) 1) : ℝ) : ℂ)) := by
  have ha : 0 < centralDilation δ := inv_pos.mpr (by linarith)
  obtain ⟨ψ,hψ⟩ := exists_bruhatTest_of_smooth_radialWindow w hw ha hs
  exact ⟨ψ,hψ,fun hB hL hbox hBL hBh hτ hκ hpos ↦
    tendsto_quotientBruhatLevel_haarDiagonal_centralFinitePart hδ0 hδ1 hw hs ψ hψ
      hB hL hbox hBL hBh hτ hκ hpos⟩

end RiemannMasullo.AnnularBand
