module
public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxCardinals
public import RiemannMasullo.ForMathlib.MeasureTheory.Function.L2Space.HalfLineMellin
public import RiemannMasullo.ForMathlib.Analysis.Calculus.IteratedDeriv.VanishingProduct
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-! # Bounded coordinates on completed rational fixed-box packets

Polynomial exponential windows make every Mellin jet a continuous functional
on logarithmic `L²`. The exact finite Euler product identifies its first
nonzero jet at zero. These normalized coordinates annihilate the next closed
stage and remain biorthogonal to all common-box cardinal lifts. Restriction and
quotient descent give continuous coordinate maps and linearly independent
cardinal classes in the actual completed packet.
-/

public noncomputable section
open Filter MeasureTheory Set Function FourierTransform
open scoped FourierTransform SchwartzMap Topology ContDiff
namespace RiemannMasullo.RationalPacket

private theorem stage_supported_of_ae {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) (f : 𝓢(ℝ, ℂ)) (h0 : (𝓕 f) 0 = 0)
    (hb : ∀ y : ℝ, X / (∏ p ∈ T, (p : ℝ)) < |y| → (𝓕 f) y = 0)
    (F : LogL2) (hF : F =ᵐ[volume] stage T f) :
    ∀ᵐ x ∂volume, x < -Real.log X → F x = 0 := by
  filter_upwards [hF] with x hx hxa
  exact hx.trans (stage_eq_zero_before_box hX T hT h0 hb hxa)

private theorem stage_fourier_eq_of_ae (T : Finset ℕ) (f : 𝓢(ℝ, ℂ))
    (F : LogL2) (hF : F =ᵐ[volume] stage T f) :
    𝓕 (dampedStage T f) = 𝓕 (fun x : ℝ ↦ (Real.exp (-x/2) : ℂ) * F x) := by
  ext ξ
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards [hF] with x hx
  rw [dampedStage_apply, hx]

private theorem stage_fourier_contDiff {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (h0 : (𝓕 f) 0 = 0)
    (hb : ∀ y : ℝ, X / (∏ p ∈ T, (p : ℝ)) < |y| → (𝓕 f) y = 0) :
    ContDiff ℝ ∞ (𝓕 (dampedStage T f)) := by
  have hm := (stage_memLp_and_dampedStage_integrable hX T hT hf h0 hb).1
  let F := hm.toLp (stage T f)
  have hF : F =ᵐ[volume] stage T f := hm.coeFn_toLp
  rw [stage_fourier_eq_of_ae T f F hF]
  exact contDiff_fourier_halfLine (-Real.log X) F (stage_supported_of_ae hX T hT f h0 hb F hF)

/-- The derivatives of an actual damped theta stage are bounded Hilbert rows
in its fixed box, including every derivative needed at the zero frequency. -/
theorem stage_fourier_jet {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, 1 ≤ q) (f : 𝓢(ℝ, ℂ)) (h0 : (𝓕 f) 0 = 0)
    (hb : ∀ y : ℝ, X / (∏ p ∈ T, (p : ℝ)) < |y| → (𝓕 f) y = 0)
    (F : LogL2) (hF : F =ᵐ[volume] stage T f) (ξ : ℝ) (r : ℕ) :
    iteratedDeriv r (𝓕 (dampedStage T f)) ξ =
      (-2 * (Real.pi : ℂ) * Complex.I)^r * halfLineMellinJet (-Real.log X) ξ r F := by
  rw [stage_fourier_eq_of_ae T f F hF]
  exact iteratedDeriv_fourier_halfLine (-Real.log X) ξ r F
    (stage_supported_of_ae hX T hT f h0 hb F hF)

private theorem stage_integrable_subsets {U : ℝ} (hU : 0 < U)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (f : 𝓢(ℝ, ℂ))
    (hf : f 0 = 0) (hF0 : (𝓕 f) 0 = 0) (hb : ∀ r, U < |r| → (𝓕 f) r = 0) :
    ∀ S ⊆ T, Integrable (dampedStage S f) := by
  intro S hS
  have hprod : 0 < ∏ q ∈ S, (q : ℝ) := Finset.prod_pos fun q hq ↦ by
    exact_mod_cast (hT q (hS hq)).pos
  exact (stage_memLp_and_dampedStage_integrable (X := U * ∏ q ∈ S, (q : ℝ))
    (mul_pos hU hprod) S (fun q hq ↦ (hT q (hS hq)).one_lt.le) hf hF0
    (by simpa only [mul_div_cancel_right₀ _ hprod.ne'] using hb)).2

private theorem contDiff_eulerFactor (l : ℝ) :
    ContDiff ℝ ∞ (fun ξ : ℝ ↦ 1 - (Real.fourierChar (l * ξ) : ℂ)) := by
  simp only [Real.fourierChar_apply]
  apply contDiff_const.sub
  have hs : ContDiff ℝ ∞ (fun ξ : ℝ ↦ ((2 * Real.pi * (l * ξ) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (contDiff_const.mul (contDiff_const.mul contDiff_id))
  exact (hs.mul contDiff_const).cexp

private theorem deriv_eulerFactor_zero (l : ℝ) :
    deriv (fun ξ : ℝ ↦ 1 - (Real.fourierChar (l * ξ) : ℂ)) 0 =
      -2 * (Real.pi : ℂ) * Complex.I * l := by
  have hd := (Real.hasDerivAt_fourierChar (l * 0)).scomp 0
    ((hasDerivAt_id (0 : ℝ)).const_mul l)
  have hh := hd.const_sub (1 : ℂ)
  have he : deriv (fun ξ : ℝ ↦ 1 - (Real.fourierChar (l * ξ) : ℂ)) 0 =
      -((l : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
    simpa only [id_eq, Function.comp_def, mul_zero, Real.fourierChar_apply,
      Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one, one_mul, Complex.real_smul] using hh.deriv
  rw [he]
  ring

/-- Earlier Euler factors give the precise zero jet of the actual theta stage,
with the first nonzero derivative determined by the empty-stage zero row. -/
theorem stage_fourier_zero_jet {U : ℝ} (hU : 0 < U) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) (f : 𝓢(ℝ, ℂ))
    (hf : f 0 = 0) (h0 : (𝓕 f) 0 = 0) (hb : ∀ r, U < |r| → (𝓕 f) r = 0) :
    (∀ k : ℕ, k < T.card → iteratedDeriv k (𝓕 (dampedStage T f)) 0 = 0) ∧
      iteratedDeriv T.card (𝓕 (dampedStage T f)) 0 =
        (T.card.factorial : ℂ) * (∏ q ∈ T, (-2 * (Real.pi : ℂ) * Complex.I * Real.log q)) *
          𝓕 (dampedStage ∅ f) 0 := by
  have hprod : 𝓕 (dampedStage T f) = fun ξ ↦
      (∏ q ∈ T, (1 - (Real.fourierChar (Real.log q * ξ) : ℂ))) * 𝓕 (dampedStage ∅ f) ξ :=
    funext fun ξ ↦ fourier_dampedStage_prod T f ξ (fun q hq ↦ (hT q hq).pos)
      (stage_integrable_subsets hU T hT f hf h0 hb)
  rw [hprod]
  have hg : ContDiff ℝ ∞ (𝓕 (dampedStage ∅ f)) :=
    stage_fourier_contDiff hU ∅ (by simp) f hf h0 (by simpa using hb)
  have h := iteratedDeriv_finset_prod_zero T
    (fun q ξ ↦ 1 - (Real.fourierChar (Real.log q * ξ) : ℂ)) (𝓕 (dampedStage ∅ f))
    (fun q _ ↦ contDiff_eulerFactor _) hg (by simp)
  simpa only [deriv_eulerFactor_zero] using h

private theorem fourierJetConstant_ne_zero : (-2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
  mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero

private theorem packetZeroNormalizer_ne_zero (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) :
    (T.card.factorial : ℂ) * (∏ q ∈ T, (Real.log q : ℂ)) ≠ 0 := by
  apply mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  apply Finset.prod_ne_zero_iff.mpr
  intro q hq
  exact Complex.ofReal_ne_zero.mpr (Real.log_pos (show (1 : ℝ) < q by exact_mod_cast (hT q hq).one_lt)).ne'

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The normalized coordinates
of a rational fixed-box packet are bounded functionals on the ambient logarithmic
Hilbert space. At zero the coordinate uses the moment of order `T.card`.
Deviation: the ordinary logarithmic `L²` specialization is used here. -/
def packetRow (X : ℝ) (T : Finset ℕ) (p : ℕ) (n : ℤ) : LogL2 →L[ℂ] ℂ :=
  if n = 0 then
    ((T.card.factorial : ℂ) * (∏ q ∈ T, (Real.log q : ℂ)))⁻¹ •
      halfLineMellinJet (-Real.log X) 0 T.card
  else
    (∏ q ∈ T, (1 - (Real.fourierChar (Real.log q * ((n : ℝ) / Real.log p)) : ℂ)))⁻¹ •
      halfLineMellinJet (-Real.log X) ((n : ℝ) / Real.log p) 0

/-- The explicit normalized row, including its higher-order zero-frequency
normalization. -/
theorem packetRow_apply (X : ℝ) (T : Finset ℕ) (p : ℕ) (n : ℤ) (F : LogL2) :
    packetRow X T p n F = if n = 0 then
      halfLineMellinJet (-Real.log X) 0 T.card F /
        ((T.card.factorial : ℂ) * ∏ q ∈ T, (Real.log q : ℂ))
    else halfLineMellinJet (-Real.log X) ((n : ℝ) / Real.log p) 0 F /
      (∏ q ∈ T, (1 - (Real.fourierChar (Real.log q * ((n : ℝ) / Real.log p)) : ℂ))) := by
  by_cases hn : n = 0 <;> simp [packetRow, hn, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- On every genuine smooth earlier-stage vector, the normalized bounded rows
recover the empty-stage Fourier samples, including the pole-normalized zero row. -/
theorem packetRow_stage {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T)
    (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (h0 : (𝓕 f) 0 = 0)
    (hb : ∀ y : ℝ, X / (∏ q ∈ T, (q : ℝ)) < |y| → (𝓕 f) y = 0)
    (F : LogL2) (hF : F =ᵐ[volume] stage T f) (n : ℤ) :
    packetRow X T p n F = 𝓕 (dampedStage ∅ f) ((n : ℝ) / Real.log p) := by
  have hprod : 0 < ∏ q ∈ T, (q : ℝ) := Finset.prod_pos fun q hq ↦ by
    exact_mod_cast (hT q hq).pos
  have hU := div_pos hX hprod
  rw [packetRow_apply]
  by_cases hn : n = 0
  · subst n
    simp only [ite_true, Int.cast_zero, zero_div]
    apply (div_eq_iff (packetZeroNormalizer_ne_zero T hT)).mpr
    have htop := (stage_fourier_zero_jet hU T hT f hf h0 hb).2
    rw [stage_fourier_jet hX T (fun q hq ↦ (hT q hq).one_lt.le) f h0 hb F hF,
      Finset.prod_mul_distrib, Finset.prod_const] at htop
    apply mul_left_cancel₀ (pow_ne_zero T.card fourierJetConstant_ne_zero)
    calc
      _ = (T.card.factorial : ℂ) *
          ((-2 * (Real.pi : ℂ) * Complex.I)^T.card * ∏ q ∈ T, (Real.log q : ℂ)) *
          𝓕 (dampedStage ∅ f) 0 := htop
      _ = _ := by ring
  · rw [ite_eq_right hn]
    have hrow := stage_fourier_jet hX T (fun q hq ↦ (hT q hq).one_lt.le) f h0 hb F hF
      ((n : ℝ) / Real.log p) 0
    simp only [iteratedDeriv_zero, pow_zero, one_mul] at hrow
    rw [← hrow, fourier_dampedStage_prod T f _ (fun q hq ↦ (hT q hq).pos)
      (stage_integrable_subsets hU T hT f hf h0 hb),
      mul_div_cancel_left₀ _ (prime_mesh_euler_prod_ne_zero T hp hpT hT hn)]

/-- Every zero-frequency Mellin jet below the number of earlier primes
vanishes on the actual Hilbert closure of that stage. -/
theorem halfLineMellinJet_stage_closure_zero {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) (k : ℕ) (hk : k < T.card)
    {F : LogL2} (hF : F ∈ closure (stageGenerators X T)) :
    halfLineMellinJet (-Real.log X) 0 k F = 0 := by
  apply closure_minimal (s := stageGenerators X T)
    (t := {F | halfLineMellinJet (-Real.log X) 0 k F = 0}) ?_
    (isClosed_singleton.preimage (halfLineMellinJet _ _ _).continuous) hF
  intro G hG
  obtain ⟨f, hf, h0, hb, hG⟩ := (mem_stageGenerators_iff X T G).mp hG
  have hprod : 0 < ∏ q ∈ T, (q : ℝ) := Finset.prod_pos fun q hq ↦ by
    exact_mod_cast (hT q hq).pos
  have hz := (stage_fourier_zero_jet (div_pos hX hprod) T hT f hf h0 hb).1 k hk
  rw [stage_fourier_jet hX T (fun q hq ↦ (hT q hq).one_lt.le) f h0 hb G hG] at hz
  exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero k fourierJetConstant_ne_zero)

/-- The order-zero rows on every earlier-prime mesh vanish on the genuine
closed stage, measured by the same half-line Hilbert functionals. -/
theorem halfLineMellinJet_stage_closure_mesh {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) {p : ℕ} (hpT : p ∈ T) (j : ℤ)
    {F : LogL2} (hF : F ∈ closure (stageGenerators X T)) :
    halfLineMellinJet (-Real.log X) ((j : ℝ) / Real.log p) 0 F = 0 := by
  apply closure_minimal (s := stageGenerators X T)
    (t := {F | halfLineMellinJet (-Real.log X) ((j : ℝ) / Real.log p) 0 F = 0}) ?_
    (isClosed_singleton.preimage (halfLineMellinJet _ _ _).continuous) hF
  intro G hG
  obtain ⟨f, hf, h0, hb, hG⟩ := (mem_stageGenerators_iff X T G).mp hG
  have hprod : 0 < ∏ q ∈ T, (q : ℝ) := Finset.prod_pos fun q hq ↦ by
    exact_mod_cast (hT q hq).pos
  have hi := stage_integrable_subsets (div_pos hX hprod) T hT f hf h0 hb
  have hrow := stage_fourier_jet hX T (fun q hq ↦ (hT q hq).one_lt.le) f h0 hb G hG
    ((j : ℝ) / Real.log p) 0
  simp only [iteratedDeriv_zero, pow_zero, one_mul] at hrow
  change halfLineMellinJet (-Real.log X) ((j : ℝ) / Real.log p) 0 G = 0
  rw [← hrow]
  simpa only [Finset.insert_erase hpT] using
    fourier_dampedStage_zero_on_mesh (T.erase p) (hT p hpT).one_lt (Finset.notMem_erase _ _) f
      (hi (T.erase p) (Finset.erase_subset ..)) j

/-- All normalized packet rows annihilate the next completed stage. In
particular, the zero row survives normalization before taking the closure. -/
theorem packetRow_eq_zero_of_mem_next {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T)
    {F : LogL2} (hF : F ∈ closure (stageGenerators X (insert p T))) (n : ℤ) :
    packetRow X T p n F = 0 := by
  have hTp : ∀ q ∈ insert p T, q.Prime := by
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp
    · exact hT q hq
  rw [packetRow_apply]
  by_cases hn : n = 0
  · rw [ite_eq_left hn, halfLineMellinJet_stage_closure_zero hX (insert p T) hTp T.card
      (by simp [Finset.card_insert_of_notMem hpT]) hF, zero_div]
  · rw [ite_eq_right hn, halfLineMellinJet_stage_closure_mesh hX (insert p T) hTp
      (Finset.mem_insert_self ..) n hF, zero_div]

/-- On an actual polar even source in the earlier box, all bounded normalized
rows vanish exactly when its stage has a genuine representative in the next,
smaller source box. This is an exact smooth denominator statement. -/
theorem stageGenerators_insert_iff_packetRows_zero {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT : ∀ q ∈ T, q.Prime) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T)
    (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) (h0 : (𝓕 f) 0 = 0)
    (he : ∀ r, (𝓕 f) (-r) = (𝓕 f) r)
    (hb : ∀ r, X / (∏ q ∈ T, (q : ℝ)) < |r| → (𝓕 f) r = 0)
    (F : LogL2) (hF : F =ᵐ[volume] stage T f) :
    F ∈ stageGenerators X (insert p T) ↔ ∀ n : ℤ, packetRow X T p n F = 0 := by
  constructor
  · intro hn n
    exact packetRow_eq_zero_of_mem_next hX T hT hp hpT (subset_closure hn) n
  · intro hz
    have hprod : 0 < ∏ q ∈ T, (q : ℝ) := Finset.prod_pos fun q hq ↦ by
      exact_mod_cast (hT q hq).pos
    have hU := div_pos hX hprod
    have hi := stage_integrable_subsets hU T hT f hf h0 hb
    have hempty (n : ℤ) : 𝓕 (dampedStage ∅ f) ((n : ℝ) / Real.log p) = 0 :=
      (packetRow_stage hX T hT hp hpT f hf h0 hb F hF n).symm.trans (hz n)
    obtain ⟨g, hg, hg0, hgb, hfg⟩ := exists_smaller_box_stage_of_theta_rows hp T hT hpT hU
      f hf h0 he hb (fun n _ ↦ by
        rw [fourier_dampedStage_prod T f _ (fun q hq ↦ (hT q hq).pos) hi, hempty n, mul_zero])
      (by simpa using (thetaBoundaryMellin_fourier f 0).trans (by simpa using hempty 0))
    refine (mem_stageGenerators_iff X (insert p T) F).mpr ⟨g, hg, hg0, ?_, ?_⟩
    · intro r hr
      apply hgb r
      simpa only [Finset.prod_insert hpT, mul_comm (p : ℝ), div_div] using hr
    · exact hF.trans (ae_of_all _ hfg)

/-- Every integer mode has a polar, even Fourier representative in the original
source box, with exactly its prescribed bounded rows. -/
theorem exists_fixedBox_biorthogonal_even_stage {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) :
    ∃ v : ℤ → LogL2,
      (∀ n, ∃ f : 𝓢(ℝ, ℂ), f 0 = 0 ∧ (𝓕 f) 0 = 0 ∧
        (∀ r, (𝓕 f) (-r) = (𝓕 f) r) ∧
        (∀ r, X / (∏ q ∈ T, (q : ℝ)) < |r| → (𝓕 f) r = 0) ∧
        v n =ᵐ[volume] stage T f) ∧
      ∀ j n : ℤ, packetRow X T p j (v n) = if j = n then 1 else 0 := by
  classical
  have hprod : 0 < ∏ q ∈ T, (q : ℝ) := Finset.prod_pos fun q hq ↦ by
    exact_mod_cast (hT q hq).pos
  obtain ⟨ε, hε, f, hf⟩ := exists_fixedBox_theta_cardinals
    (show (1 : ℝ) < p by exact_mod_cast hp.one_lt) (div_pos hX hprod)
  have hdata : ∀ n : ℤ, ∃ F : LogL2,
      (∃ f : 𝓢(ℝ, ℂ), f 0 = 0 ∧ (𝓕 f) 0 = 0 ∧
        (∀ r, (𝓕 f) (-r) = (𝓕 f) r) ∧
        (∀ r, X / (∏ q ∈ T, (q : ℝ)) < |r| → (𝓕 f) r = 0) ∧
        F =ᵐ[volume] stage T f) ∧
      ∀ j : ℤ, packetRow X T p j F = if j = n then 1 else 0 := by
    intro n
    obtain ⟨hf0, hF0, hFc, he, hb, hrows⟩ := hf (-n)
    have hband (r : ℝ) (hr : X / (∏ q ∈ T, (q : ℝ)) < |r|) := hb r (Or.inr hr)
    have hm := (stage_memLp_and_dampedStage_integrable hX T
      (fun q hq ↦ (hT q hq).one_lt.le) hf0 hF0 hband).1
    let F := hm.toLp (stage T (f (-n)))
    have hF : F =ᵐ[volume] stage T (f (-n)) := hm.coeFn_toLp
    refine ⟨F, ⟨f (-n), hf0, hF0, he, hband, hF⟩, fun j ↦ ?_⟩
    rw [packetRow_stage hX T hT hp hpT (f (-n)) hf0 hF0 hband F hF j]
    have h := hrows (-j)
    have hphase : (((2 * Real.pi * (((-j : ℤ) : ℝ) / Real.log p) : ℝ) : ℂ) * Complex.I) =
        ((-2 * Real.pi * ((j : ℝ) / Real.log p) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hphase, thetaBoundaryMellin_fourier] at h
    simpa only [neg_inj] using h
  choose v hv hrow using hdata
  exact ⟨v, hv, fun j n ↦ hrow n j⟩

/-- Every integer mode has a genuine fixed-box stage vector biorthogonal to
all the bounded normalized rows, including the zero mode. -/
theorem exists_fixedBox_biorthogonal_stage {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) :
    ∃ v : ℤ → LogL2, (∀ n, v n ∈ stageGenerators X T) ∧
      ∀ j n : ℤ, packetRow X T p j (v n) = if j = n then 1 else 0 := by
  obtain ⟨v, hv, hrow⟩ := exists_fixedBox_biorthogonal_even_stage hX T hT hp hpT
  refine ⟨v, fun n ↦ ?_, hrow⟩
  obtain ⟨f, hf, h0, _, hb, hF⟩ := hv n
  exact (mem_stageGenerators_iff X T (v n)).mpr ⟨f, hf, h0, hb, hF⟩

/-- Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The actual completed rational
fixed-box packet contains all integer cardinal classes, with continuous
biorthogonal quotient coordinates. These classes are linearly independent.
Deviation: this proves survival and independence after completion; density of
the cardinal span and the Schauder expansion are not asserted here. -/
theorem exists_closed_packet_cardinals {X : ℝ} (hX : 0 < X) (T : Finset ℕ)
    (hT : ∀ q ∈ T, q.Prime) {p : ℕ} (hp : p.Prime) (hpT : p ∉ T) :
    let E := (closedStageSubmodule X T (fun q hq ↦ (hT q hq).one_lt.le)).toSubmodule
    let N := (closedStageSubmodule X (insert p T) (fun q hq ↦ by
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp.one_lt.le
      · exact (hT q hq).one_lt.le)).toSubmodule
    let D := N.comap E.subtype
    N ≤ E ∧ IsClosed (D : Set E) ∧ ∃ v : ℤ → E, ∃ ℓ : ℤ → ((E ⧸ D) →L[ℂ] ℂ),
      (∀ n, (v n : LogL2) ∈ stageGenerators X T) ∧
      (∀ j n : ℤ, ℓ j (D.mkQ (v n)) = if j = n then 1 else 0) ∧
      LinearIndependent ℂ (fun n ↦ D.mkQ (v n)) := by
  classical
  let hT1 : ∀ q ∈ T, 1 ≤ q := fun q hq ↦ (hT q hq).one_lt.le
  let hTp1 : ∀ q ∈ insert p T, 1 ≤ q := fun q hq ↦ by
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact hp.one_lt.le
    · exact (hT q hq).one_lt.le
  let E := (closedStageSubmodule X T hT1).toSubmodule
  let N := (closedStageSubmodule X (insert p T) hTp1).toSubmodule
  let D := N.comap E.subtype
  change N ≤ E ∧ IsClosed (D : Set E) ∧ ∃ v : ℤ → E, ∃ ℓ : ℤ → ((E ⧸ D) →L[ℂ] ℂ), _
  have hNE : N ≤ E := by
    intro F hF
    exact (mem_closedStageSubmodule_iff X T hT1 F).mpr
      ((closure_mono (stageGenerators_insert_subset hX T hT1 hp.one_lt.le))
        ((mem_closedStageSubmodule_iff X (insert p T) hTp1 F).mp hF))
  have hDc : IsClosed (D : Set E) :=
    (closedStageSubmodule X (insert p T) hTp1).isClosed.preimage E.subtypeL.continuous
  obtain ⟨V, hV, hrow⟩ := exists_fixedBox_biorthogonal_stage hX T hT hp hpT
  let v (n : ℤ) : E := ⟨V n, (mem_closedStageSubmodule_iff X T hT1 (V n)).mpr (subset_closure (hV n))⟩
  let r (n : ℤ) : E →L[ℂ] ℂ := (packetRow X T p n).comp E.subtypeL
  have hker (n : ℤ) : D ≤ (r n).ker := by
    intro F hF
    change packetRow X T p n (F : LogL2) = 0
    exact packetRow_eq_zero_of_mem_next hX T hT hp hpT
      ((mem_closedStageSubmodule_iff X (insert p T) hTp1 (F : LogL2)).mp hF) n
  let ℓ (n : ℤ) : (E ⧸ D) →L[ℂ] ℂ := D.liftQL (r n) (hker n)
  have hpair (j n : ℤ) : ℓ j (D.mkQ (v n)) = if j = n then 1 else 0 := by
    change packetRow X T p j (V n) = _
    exact hrow j n
  refine ⟨hNE, hDc, v, ℓ, hV, hpair, ?_⟩
  apply LinearIndependent.of_pairwise_dual_eq_zero_one (fun n ↦ D.mkQ (v n))
    (fun j ↦ (ℓ j).toLinearMap)
  · intro i j hij
    simp only [ContinuousLinearMap.coe_coe, hpair, ite_eq_right hij]
  · intro i
    simp only [ContinuousLinearMap.coe_coe, hpair, ite_true]

end RiemannMasullo.RationalPacket
