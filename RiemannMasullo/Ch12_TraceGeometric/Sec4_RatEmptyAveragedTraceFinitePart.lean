module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RatEmptyTraceFinitePart
public import RiemannMasullo.Ch12_TraceGeometric.Sec4_RealPWLevelTransport

/-! # The logarithmic finite part of the actual averaged compression

The genuine rational quotient compression of a Haar-averaged test is nuclear
at finite cutoffs. Its Hilbert trace has the same explicit finite part across
norm one as the scalar average of the one-dilation traces. -/

public noncomputable section

open Filter MeasureTheory Set NumberField IsDedekindDomain
open scoped Interval NNReal ENNReal Topology NumberField.AdeleRing

namespace RiemannMasullo.RatEmptyRealLevelBridge

set_option quotPrecheck false

local notation "S₀" => (∅ : Finset (HeightOneSpectrum (𝓞 ℚ)))
local notation "J" => SIdeleQuotient ℚ S₀
local notation "N" => sIdeleQuotientNorm ℚ S₀
local notation "W" => Lp ℂ 2 ((sLocalQuotientTamagawaMeasure ℚ S₀).withDensity
  (fun g ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 0 (Real.log (((N g).val : ℝ≥0) : ℝ)))))
local notation "P(" ω ", " B ")" =>
  (sLocalInvariantPWSobolev (F := ℚ) (S := S₀) (s := 0) le_rfl
    (a := 1 / 2) (by norm_num) ω B).starProjection

/-- The unique norm class at each positive real radius. Outside positive radii
its arbitrary value is not used in the Haar integral. -/
def realHaarNormClass (g : ℝ) : J :=
  if hg : 0 < g then
    quotientElement (Units.mk0 g.toNNReal (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt hg)))
  else 1

theorem realHaarNormClass_norm {g : ℝ} (hg : 0 < g) : ((N (realHaarNormClass g)).val : ℝ) = g := by
  rw [realHaarNormClass, dite_eq_left hg, quotientElement_spec, Units.val_mk0,
    Real.coe_toNNReal _ hg.le]

private theorem integral_flat_eq_actual (ω : PontryaginDual (MonoidHom.ker N))
    {B L a b : ℝ} (hB : 0 < B) (hL : 0 ≤ L) (ha : 0 < a) (hab : a ≤ b) (w : ℝ → ℝ) :
    (∫ g in a..b, (w g : ℂ) * realPWLevelCompressionTrace B L g / (g : ℂ)) =
      ∫ g in a..b, (w g : ℂ) * actualCompressionTrace ω hB hL g / (g : ℂ) := by
  apply intervalIntegral.integral_congr
  intro g hg
  rw [uIcc_of_le hab] at hg
  dsimp only
  rw [actualCompressionTrace_eq_flat ω hB hL (ha.trans_le hg.1)]

/-- Actual quotient operators are averaged vectorwise against the Haar density,
then compressed to the genuine level with the sharp spatial cutoff. Their
Hilbert traces, after the exact logarithmic subtraction, have a finite limit. -/
theorem tendsto_actualHaarAveragedCompressionTrace_centralFinitePart
    (ω : PontryaginDual (MonoidHom.ker N)) {δ C : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hC : 0 ≤ C) {w : ℝ → ℝ} (hw : Continuous w)
    (hw1 : ∀ g ∈ Icc (centralDilation δ) (centralDilation (-δ)), |w g - w 1| ≤ C * |g - 1|)
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated] {B L : ι → ℝ}
    (hB : ∀ i, 0 < B i) (hL : ∀ i, 0 < L i)
    (hBL : Tendsto (fun i ↦ B i * L i) l atTop) :
    ∃ A : ι → W →L[ℂ] W,
      (∀ i (F : W), A i F = ∫ g in centralDilation δ..centralDilation (-δ),
        ((w g / g : ℝ) : ℂ) • ratEmptyTranslation (realHaarNormClass g) F) ∧
      ∃ hn : ∀ i, IsNuclearOperator (P(ω, B i) ∘L ratEmptyCutoff (L i) ∘L A i ∘L P(ω, B i)),
        Tendsto (fun i ↦ hilbertTrace ⟨_, hn i⟩ - ((w 1 * Real.log (B i * L i) : ℝ) : ℂ)) l
          (𝓝 (actualCentralTraceFinitePart δ w : ℂ)) := by
  have ha : 0 < centralDilation δ := by
    change 0 < (1 + δ)⁻¹
    positivity
  have hab : centralDilation δ ≤ centralDilation (-δ) := by
    change (1 + δ)⁻¹ ≤ (1 + -δ)⁻¹
    exact inv_anti₀ (by linarith : 0 < 1 + -δ) (by linarith)
  have hfin (i : ι) := ratEmpty_hilbertTrace_average_compression ω (hB i) (hL i).le
    ha hab (φ := w) hw.continuousOn realHaarNormClass (fun _ hg ↦ realHaarNormClass_norm hg)
  choose A hA hn ht using hfin
  refine ⟨A, hA, hn, ?_⟩
  refine (tendsto_actualHaarTrace_centralFinitePart ω hδ0 hδ1 hC hw hw1 hB hL hBL).congr fun i ↦ ?_
  rw [ht i, integral_flat_eq_actual ω (hB i) (hL i).le ha hab]

end RiemannMasullo.RatEmptyRealLevelBridge
