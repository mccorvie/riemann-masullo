module

public import RiemannMasullo.Ch10_TraceSpectral.Sec2
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ConductorAtoms
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ConductorDensity
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic

/-! # Individual prime-power limits for rational finite-level angular tests

Masullo §12.3, p. 514. Compare the actual strip multiplicities of the primitive
functions at one modulus with their positive-log prime formulas.
-/

@[expose] public noncomputable section

open Filter Function Set MeasureTheory
open scoped ArithmeticFunction BigOperators ContDiff Topology

namespace RiemannMasullo.RationalConductor

open ConductorDensity

/-- A shift by `a` in the Mellin coordinate multiplies the radial test by `exp(-ax)`. -/
def shiftedProfile (a : ℝ) (H : ℝ → ℂ) (x : ℝ) : ℂ := (Real.exp (-a * x) : ℂ) * H x

theorem bilateralLaplace_shiftedProfile (a : ℝ) (H : ℝ → ℂ) (z : ℂ) :
    bilateralLaplace (shiftedProfile a H) z = bilateralLaplace H (z - a) := by
  unfold bilateralLaplace
  apply integral_congr_ae
  refine Eventually.of_forall fun x ↦ ?_
  simp only [shiftedProfile, Complex.ofReal_exp, Complex.ofReal_mul, Complex.ofReal_neg]
  calc
    _ = H x * (Complex.exp (-(a : ℂ) * x) * Complex.exp (z * x)) := by ring
    _ = _ := by rw [← Complex.exp_add]; congr 2; ring

/-- The archimedean term for parity `j=0,1` and a profile supported above log norm zero. -/
def archTerm (j : ℕ) (G : ℝ → ℂ) : ℂ :=
  ∫ x in Ioi (0 : ℝ), G x * ((Real.exp (-(j : ℝ) * x) / (1 - Real.exp (-2 * x)) : ℝ) : ℂ)

/-- The classical compactly smoothed positive-log explicit formula for the primitive
characters. The two killed Mellin moments account for the pole corrections at `0,1`. -/
def PositiveLogDirichletFormula : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (G : ℝ → ℂ),
    ContDiff ℝ ∞ G → HasCompactSupport G → tsupport G ⊆ Ioi 0 →
    bilateralLaplace G 0 = 0 → bilateralLaplace G 1 = 0 →
    HasSum (fun z : {z : ℂ // 0 < z.re ∧ z.re < 1} ↦
      (completedPrimitiveOrder (χ, z) : ℂ) * bilateralLaplace G z.val)
      (primeAndArchRow G (archTerm 0 G) (archTerm 1 G) χ)

/-- The scalar from a prescribed subset of the primitive divisor multiplicities
at the true real translate of a spectral coordinate. -/
def divisorRow {q : ℕ} (a : ℝ) (H : ℝ → ℂ) (w : Site q → ℕ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' z : {z : ℂ // 0 < z.re ∧ z.re < 1}, (w (χ, z) : ℂ) * bilateralLaplace H (z.val - a)

private theorem row_comparison {q : ℕ} [NeZero q] (a : ℝ) (H : ℝ → ℂ) (w : Site q → ℕ)
    (hw : ∀ i, w i ≤ completedPrimitiveOrder i)
    (hfull : ∀ χ : DirichletCharacter ℂ q, HasSum (fun z : {z : ℂ // 0 < z.re ∧ z.re < 1} ↦
      (completedPrimitiveOrder (χ, z) : ℂ) * bilateralLaplace H (z.val - a))
      (primeAndArchRow (shiftedProfile a H) (archTerm 0 (shiftedProfile a H))
        (archTerm 1 (shiftedProfile a H)) χ))
    (hs : Summable (fun i : Site q ↦ ((completedPrimitiveOrder i - w i : ℕ) : ℝ) *
      ‖bilateralLaplace H (i.2.val - a)‖)) (r : (ZMod q)ˣ) :
    (∀ χ : DirichletCharacter ℂ q, Summable (fun z : {z : ℂ // 0 < z.re ∧ z.re < 1} ↦
      ‖(w (χ, z) : ℂ) * bilateralLaplace H (z.val - a)‖)) ∧
    ‖cylinderAverage q r (divisorRow a H w) -
      cylinderAverage q r (primeAndArchRow (shiftedProfile a H) (archTerm 0 (shiftedProfile a H))
        (archTerm 1 (shiftedProfile a H)))‖ ≤
      (∑' i : Site q, ((completedPrimitiveOrder i - w i : ℕ) : ℝ) *
        ‖bilateralLaplace H (i.2.val - a)‖) / q.totient := by
  let m (i : Site q) := completedPrimitiveOrder i - w i
  let L (i : Site q) := bilateralLaplace H (i.2.val - a)
  let v (i : Site q) := (m i : ℝ) * ‖L i‖
  let t (i : Site q) := (m i : ℂ) * L i
  let Full := primeAndArchRow (q := q) (shiftedProfile a H) (archTerm 0 (shiftedProfile a H))
    (archTerm 1 (shiftedProfile a H))
  have hsum : Summable v := hs
  have hrow := ((summable_prod_of_nonneg (fun i : Site q ↦ show 0 ≤ v i by dsimp [v]; positivity)).mp hsum).1
  have ht (χ : DirichletCharacter ℂ q) : Summable (fun z ↦ ‖t (χ, z)‖) := by
    simpa only [t, v, norm_mul, Complex.norm_natCast] using hrow χ
  have heq (i : Site q) : (w i : ℂ) * L i = (completedPrimitiveOrder i : ℂ) * L i - t i := by
    simp only [t, m, Nat.cast_sub (hw i)]
    ring
  have he (χ : DirichletCharacter ℂ q) : HasSum (fun z ↦ (w (χ, z) : ℂ) * L (χ, z))
      (Full χ - ∑' z, t (χ, z)) := by
    exact ((hfull χ).sub (ht χ).of_norm.hasSum).congr_fun fun z ↦ heq (χ, z)
  refine ⟨fun χ ↦ (he χ).summable.norm, ?_⟩
  have hb (χ : DirichletCharacter ℂ q) :
      ‖divisorRow a H w χ - Full χ‖ ≤ ∑' z, v (χ, z) := by
    change ‖(∑' z, (w (χ, z) : ℂ) * L (χ, z)) - Full χ‖ ≤ _
    rw [(he χ).tsum_eq, sub_sub_cancel_left, norm_neg]
    exact (norm_tsum_le_tsum_norm (ht χ)).trans_eq (tsum_congr fun z ↦ by simp [t, v])
  change ‖cylinderAverage q r (divisorRow a H w) - cylinderAverage q r Full‖ ≤ (∑' i, v i) / _
  rw [← map_sub, hsum.tsum_prod' hrow, tsum_fintype]
  exact (norm_cylinderAverage_le _ _).trans (div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun χ _ ↦ hb χ) (Nat.cast_nonneg _))

/-- For any retained multiplicities equal to the true completed primitive orders
throughout the central open band, the actual finite angular Fourier sum has the
single-atom asymptotic. The full zeros and the Montgomery count are the two classical
arithmetic inputs. The estimate includes all omitted boundary jets. -/
theorem conductor_atom_error {σ C ε a : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (hC : 0 ≤ C) (hcount : MontgomeryProductCount σ (montgomeryExponent σ) C) (hε : 0 < ε)
    (hef : PositiveLogDirichletFormula) {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (hpos : tsupport H ⊆ Ioi 0)
    (hm₀ : bilateralLaplace H (-(a : ℂ)) = 0) (hm₁ : bilateralLaplace H (1 - a) = 0)
    {b : ℕ} (hb : 2 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (hbq : b.Coprime q), b + 1 < q →
      ∀ w : Site q → ℕ, (∀ i, w i ≤ completedPrimitiveOrder i) →
      (∀ i, 1 - σ < i.2.val.re → i.2.val.re < σ → w i = completedPrimitiveOrder i) →
      (∀ χ : DirichletCharacter ℂ q, Summable (fun z : {z : ℂ // 0 < z.re ∧ z.re < 1} ↦
        ‖(w (χ, z) : ℂ) * bilateralLaplace H (z.val - a)‖)) ∧
      ‖cylinderAverage q (ZMod.unitOfCoprime b hbq) (divisorRow a H w) +
        (((b : ℝ) ^ (-a) : ℝ) : ℂ) * primeSample H b‖ ≤ B * (q : ℝ) ^ (-(1 - montgomeryExponent σ) + ε) := by
  let G := shiftedProfile a H
  have hG : HasCompactSupport G := hc.mul_left (f := fun x ↦ (Real.exp (-a * x) : ℂ))
  have hGpos : tsupport G ⊆ Ioi 0 := by
    exact (tsupport_mul_subset_right (f := fun x ↦ (Real.exp (-a * x) : ℂ)) (g := H)).trans hpos
  have hGdiff : ContDiff ℝ ∞ G := by
    change ContDiff ℝ ∞ (fun x : ℝ ↦ (Real.exp (-a * x) : ℂ) * H x)
    have he : ContDiff ℝ ∞ (fun x : ℝ ↦ Real.exp (-a * x)) := by fun_prop
    exact (Complex.ofRealCLM.contDiff.comp he).mul hH
  have hG₀ : bilateralLaplace G 0 = 0 := by simpa only [G, bilateralLaplace_shiftedProfile, zero_sub] using hm₀
  have hG₁ : bilateralLaplace G 1 = 0 := by simpa only [G, bilateralLaplace_shiftedProfile] using hm₁
  obtain ⟨K, hK, hprime⟩ := norm_primeAndArchRow_add_le hG hb
  obtain ⟨D, hD, htail⟩ := normalized_omitted_mass hσ hσ1 hC hcount.to_count
    (hH.of_le (by simp)) hc |a| hε
  refine ⟨D + K, add_nonneg hD hK, fun q _ hbq hq w hw hw' ↦ ?_⟩
  let m (i : Site q) : ℝ := (completedPrimitiveOrder i - w i : ℕ)
  have hm (i : Site q) : m i ≤ completedPrimitiveOrder i := by
    change ((completedPrimitiveOrder i - w i : ℕ) : ℝ) ≤ (completedPrimitiveOrder i : ℝ)
    exact_mod_cast (Nat.sub_le _ _)
  have hwing (i : Site q) (hi : m i ≠ 0) : σ ≤ i.2.val.re ∨ i.2.val.re ≤ 1 - σ := by
    by_contra! h
    exact hi (by simp [m, hw' i h.2 h.1])
  obtain ⟨hs, hbound⟩ := htail q a le_rfl m (fun i ↦ Nat.cast_nonneg _) hm hwing
  let r := ZMod.unitOfCoprime b hbq
  let F := primeAndArchRow (q := q) G (archTerm 0 G) (archTerm 1 G)
  have hfull (χ : DirichletCharacter ℂ q) := hef q χ G hGdiff hG hGpos hG₀ hG₁
  obtain ⟨hs', he⟩ := row_comparison a H w hw
    (fun χ ↦ (hfull χ).congr_fun (fun z ↦ by simp [G, bilateralLaplace_shiftedProfile])) hs r
  refine ⟨hs', ?_⟩
  have hθ : 0 ≤ montgomeryExponent σ := mul_nonneg (sub_nonneg.mpr hσ1.le)
    (le_min (div_nonneg (by norm_num) (by linarith)) (div_nonneg (by norm_num) (by linarith)))
  have hpower : (q : ℝ)⁻¹ ≤ (q : ℝ) ^ (-(1 - montgomeryExponent σ) + ε) := by
    rw [← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast NeZero.pos q) (by linarith)
  have hp := hprime q hbq hq (archTerm 0 G) (archTerm 1 G)
  rw [← primeSample_shift H a (by omega : 0 < b)]
  change ‖cylinderAverage q r (divisorRow a H w) + primeSample G b‖ ≤ _
  calc
    _ = ‖(cylinderAverage q r (divisorRow a H w) - cylinderAverage q r F) +
        (cylinderAverage q r F + primeSample G b)‖ := by congr 1; abel
    _ ≤ _ := norm_add_le _ _
    _ ≤ D * (q : ℝ) ^ (-(1 - montgomeryExponent σ) + ε) + K / q :=
      add_le_add (he.trans hbound) hp
    _ ≤ _ := by rw [add_mul, div_eq_mul_inv]; gcongr


private theorem strip_le_full (γ s x : ℝ) (m : ℕ) : spectralStripMultiplicity γ s x m ≤ m := by
  unfold spectralStripMultiplicity
  split
  · rfl
  split
  · exact min_le_left _ _
  · exact Nat.zero_le _

private theorem strip_le_strip {α β : ℝ} (hα : 0 ≤ α) (hab : α < β) (s x : ℝ) (m : ℕ) :
    spectralStripMultiplicity α s x m ≤ spectralStripMultiplicity β s x m := by
  by_cases hi : -β < x ∧ x < β
  · rw [spectralStripMultiplicity_interior hi]
    exact strip_le_full _ _ _ _
  · have hn : ¬(-α < x ∧ x < α) := fun h ↦ hi ⟨by linarith [h.1], by linarith [h.2]⟩
    have he : ¬(x = -α ∨ x = α) := by
      rintro (h | h) <;> apply hi <;> constructor <;> linarith
    rw [spectralStripMultiplicity, ite_eq_right hn, ite_eq_right he]
    exact Nat.zero_le _

/-- The prescribed signed wide-minus-narrow sum in the chart of spectral center zero.
The subtraction occurs after both literal jet multiplicities have been cast. -/
def signedLostRow {q : ℕ} [NeZero q] (α β s : ℝ) (H : ℝ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' z : {z : ℂ // 0 < z.re ∧ z.re < 1},
    ((spectralStripMultiplicity β s z.val.re (completedPrimitiveOrder (χ, z)) : ℂ) -
      spectralStripMultiplicity α s z.val.re (completedPrimitiveOrder (χ, z))) * bilateralLaplace H z.val

/-- The literal retained zero sum at spectral center `1/2`, with its true shifted
Mellin argument and its prescribed boundary multiplicities. -/
def centeredRetainedRow {q : ℕ} [NeZero q] (α s : ℝ) (H : ℝ → ℂ) :
    DirichletCharacter ℂ q → ℂ :=
  divisorRow (1 / 2) H fun i ↦
    spectralStripMultiplicity α s (i.2.val.re - 1 / 2) (completedPrimitiveOrder i)

/-- Off-center nested widths recover the individual von Mangoldt atom at `b`
with Montgomery's exponent, uniformly over all moduli coprime to `b`. -/
theorem signedLostRow_atom_error {σ C ε α β s : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (hC : 0 ≤ C) (hcount : MontgomeryProductCount σ (montgomeryExponent σ) C)
    (hα : 0 ≤ α) (hn : α ≤ 1 - σ) (hw : σ ≤ β) (hε : 0 < ε)
    (hef : PositiveLogDirichletFormula) {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (hpos : tsupport H ⊆ Ioi 0)
    (hm₀ : bilateralLaplace H 0 = 0) (hm₁ : bilateralLaplace H 1 = 0) {b : ℕ} (hb : 2 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (hbq : b.Coprime q), b + 1 < q →
      ‖cylinderAverage q (ZMod.unitOfCoprime b hbq) (signedLostRow α β s H) + primeSample H b‖ ≤
        B * (q : ℝ) ^ (-(1 - montgomeryExponent σ) + ε) := by
  obtain ⟨B, hB, hbound⟩ := conductor_atom_error (a := 0) hσ hσ1 hC hcount hε hef hH hc hpos
    (by simpa using hm₀) (by simpa using hm₁) hb
  refine ⟨B, hB, fun q _ hbq hq ↦ ?_⟩
  let w (i : Site q) := spectralStripMultiplicity β s i.2.val.re (completedPrimitiveOrder i) -
    spectralStripMultiplicity α s i.2.val.re (completedPrimitiveOrder i)
  have hle (i : Site q) : w i ≤ completedPrimitiveOrder i :=
    (Nat.sub_le _ _).trans (strip_le_full _ _ _ _)
  have hmid (i : Site q) (hl : 1 - σ < i.2.val.re) (hr : i.2.val.re < σ) :
      w i = completedPrimitiveOrder i := by
    have hβ : -β < i.2.val.re ∧ i.2.val.re < β := ⟨by linarith, by linarith⟩
    have ha : ¬(-α < i.2.val.re ∧ i.2.val.re < α) := fun h ↦ by linarith [h.2]
    have hEdge : ¬(i.2.val.re = -α ∨ i.2.val.re = α) := by rintro (h | h) <;> linarith
    simp only [w, spectralStripMultiplicity, ite_eq_left hβ,
      ite_eq_right ha, ite_eq_right hEdge, Nat.sub_zero]
  have heq : divisorRow 0 H w = signedLostRow (q := q) α β s H := by
    funext χ
    unfold divisorRow signedLostRow
    apply tsum_congr
    intro z
    simp only [w, Nat.cast_sub (strip_le_strip hα (by linarith : α < β) s z.val.re _),
      Complex.ofReal_zero, sub_zero]
  simpa only [heq, neg_zero, Real.rpow_zero, Complex.ofReal_one, one_mul] using
    (hbound q hbq hq w hle hmid).2

/-- At a fixed positive centered width the retained sum recovers the same atom with
the factor `b^(-1/2)`. The test kills the true shifted moments at `-1/2,1/2`. -/
theorem centeredRetainedRow_atom_error {σ C ε α s : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (hC : 0 ≤ C) (hcount : MontgomeryProductCount σ (montgomeryExponent σ) C)
    (hw : σ - 1 / 2 ≤ α) (hε : 0 < ε)
    (hef : PositiveLogDirichletFormula) {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H)
    (hc : HasCompactSupport H) (hpos : tsupport H ⊆ Ioi 0)
    (hmMinus : bilateralLaplace H (-1 / 2) = 0) (hmPlus : bilateralLaplace H (1 / 2) = 0) {b : ℕ} (hb : 2 ≤ b) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (hbq : b.Coprime q), b + 1 < q →
      ‖cylinderAverage q (ZMod.unitOfCoprime b hbq) (centeredRetainedRow α s H) +
        (((b : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * primeSample H b‖ ≤
        B * (q : ℝ) ^ (-(1 - montgomeryExponent σ) + ε) := by
  obtain ⟨B, hB, hbound⟩ := conductor_atom_error (a := 1 / 2) hσ hσ1 hC hcount hε hef hH hc hpos
    (by convert hmMinus using 2; norm_num) (by convert hmPlus using 2; norm_num) hb
  refine ⟨B, hB, fun q _ hbq hq ↦ ?_⟩
  let w (i : Site q) := spectralStripMultiplicity α s (i.2.val.re - 1 / 2) (completedPrimitiveOrder i)
  have hmid (i : Site q) (hl : 1 - σ < i.2.val.re) (hr : i.2.val.re < σ) :
      w i = completedPrimitiveOrder i :=
    spectralStripMultiplicity_interior ⟨by linarith, by linarith⟩ _ _
  exact (hbound q hbq hq w (fun i ↦ strip_le_full _ _ _ _) hmid).2

/-- The one-modulus product estimate of Montgomery for each fixed right rectangle. -/
def HistoricalMontgomeryDensity : Prop :=
  ∀ σ : ℝ, 1 / 2 < σ → σ < 1 → ∃ C : ℝ, 0 ≤ C ∧ MontgomeryProductCount σ (montgomeryExponent σ) C

private theorem conductor_limit_of_rate {ι : Type*} {l : Filter ι} {q : ι → ℕ}
    (hq : Tendsto q l atTop) (v : ι → ℂ) (z : ℂ) {K γ : ℝ} (hγ : γ < 0)
    (h : ∀ᶠ i in l, ‖v i + z‖ ≤ K * (q i : ℝ) ^ γ) : Tendsto v l (𝓝 (-z)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun i ↦ norm_nonneg _)
  · simpa only [sub_neg_eq_add] using h
  · have hq' : Tendsto (fun i ↦ (q i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hq
    simpa only [neg_neg, Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (neg_pos.mpr hγ)).comp hq').const_mul K

/-- Along every sequence of moduli coprime to `b≥2`, angular cylinders at the residue
of `b` recover exactly its individual von Mangoldt atom for the off-center widths. -/
theorem signedLostRow_tendsto {ι : Type*} {l : Filter ι} {q : ι → ℕ} [∀ i, NeZero (q i)]
    (hq : Tendsto q l atTop) {b : ℕ} (hb : 2 ≤ b) (hbq : ∀ i, b.Coprime (q i))
    {α β s : ℝ} (hα : 0 ≤ α) (hn : α < 1 / 2) (hw : 1 / 2 < β)
    (hM : HistoricalMontgomeryDensity) (hef : PositiveLogDirichletFormula) {H : ℝ → ℂ}
    (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (hpos : tsupport H ⊆ Ioi 0)
    (hm₀ : bilateralLaplace H 0 = 0) (hm₁ : bilateralLaplace H 1 = 0) :
    Tendsto (fun i ↦ cylinderAverage (q i) (ZMod.unitOfCoprime b (hbq i))
      (signedLostRow α β s H)) l (𝓝 (-primeSample H b)) := by
  let σ := min (3 / 4) (min (1 - α) β)
  have hσ : 1 / 2 < σ := lt_min (by norm_num) (lt_min (by linarith) hw)
  have hσ1 : σ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hα' : α ≤ 1 - σ := by
    have h := (min_le_right (3 / 4 : ℝ) (min (1 - α) β)).trans (min_le_left _ _)
    linarith
  have hβ : σ ≤ β := (min_le_right _ _).trans (min_le_right _ _)
  obtain ⟨C, hC, hcount⟩ := hM σ hσ hσ1
  let ε := (1 - montgomeryExponent σ) / 2
  have hθ := montgomeryExponent_lt_one hσ hσ1
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨K, hK, hbound⟩ := signedLostRow_atom_error (s := s) hσ hσ1 hC hcount hα hα' hβ hε
    hef hH hc hpos hm₀ hm₁ hb
  apply conductor_limit_of_rate hq _ _ (show -(1 - montgomeryExponent σ) + ε < 0 by dsimp [ε]; linarith)
  filter_upwards [hq.eventually (eventually_gt_atTop (b + 1))] with i hi using hbound (q i) (hbq i) hi

/-- For the true retained zero rows at spectral center `1/2`, the recovered atom is
`-Λ(b) H(log b) / √b` for every fixed positive width. -/
theorem centeredRetainedRow_tendsto {ι : Type*} {l : Filter ι} {q : ι → ℕ} [∀ i, NeZero (q i)]
    (hq : Tendsto q l atTop) {b : ℕ} (hb : 2 ≤ b) (hbq : ∀ i, b.Coprime (q i))
    {α s : ℝ} (hw : 0 < α) (hM : HistoricalMontgomeryDensity) (hef : PositiveLogDirichletFormula)
    {H : ℝ → ℂ} (hH : ContDiff ℝ ∞ H) (hc : HasCompactSupport H) (hpos : tsupport H ⊆ Ioi 0)
    (hmMinus : bilateralLaplace H (-1 / 2) = 0) (hmPlus : bilateralLaplace H (1 / 2) = 0) :
    Tendsto (fun i ↦ cylinderAverage (q i) (ZMod.unitOfCoprime b (hbq i))
      (centeredRetainedRow α s H)) l (𝓝 (-((((b : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * primeSample H b))) := by
  let σ := min (3 / 4) (1 / 2 + α)
  have hσ : 1 / 2 < σ := lt_min (by norm_num) (by linarith)
  have hσ1 : σ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hα' : σ - 1 / 2 ≤ α := by
    have h := min_le_right (3 / 4 : ℝ) (1 / 2 + α)
    linarith
  obtain ⟨C, hC, hcount⟩ := hM σ hσ hσ1
  let ε := (1 - montgomeryExponent σ) / 2
  have hθ := montgomeryExponent_lt_one hσ hσ1
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨K, hK, hbound⟩ := centeredRetainedRow_atom_error (s := s) hσ hσ1 hC hcount hα' hε
    hef hH hc hpos hmMinus hmPlus hb
  apply conductor_limit_of_rate hq _ _ (show -(1 - montgomeryExponent σ) + ε < 0 by dsimp [ε]; linarith)
  filter_upwards [hq.eventually (eventually_gt_atTop (b + 1))] with i hi using hbound (q i) (hbq i) hi

end RiemannMasullo.RationalConductor
