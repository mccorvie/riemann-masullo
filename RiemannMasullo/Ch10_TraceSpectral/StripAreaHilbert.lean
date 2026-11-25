module

public import RiemannMasullo.Ch10_TraceSpectral.StripAreaNorm
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # A closed Hilbert model for the pure area strip norm

The Laplace jet of a radial weighted profile is in a concrete complex `L²` space.
The range is closed by the two-sided norm comparison. Surviving boundary moments
are continuous on the closed strip.
-/

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology Classical

@[expose] public noncomputable section
namespace RiemannMasullo

/-- Count the derivative order, integrate the ordinate against Lebesgue measure, and
weight the real coordinate by the boundary-distance density on the open strip. -/
def stripAreaJetMeasure (α s : ℝ) (m : ℕ) : Measure (Fin (m+1) × (ℝ × ℝ)) :=
  Measure.count.prod (((volume.restrict (Ioo (-α) α)).withDensity
    (fun σ ↦ ENNReal.ofReal ((α - |σ|) ^ (2 * (m : ℝ) - s - 1)))).prod volume)

/-- The finite strip jet as a single scalar function on the indexed strip. -/
def stripAreaJet (m : ℕ) (F : ℂ → ℂ) (q : Fin (m+1) × (ℝ × ℝ)) : ℂ :=
  iteratedDeriv q.1.val F ((q.2.1 : ℂ) + q.2.2 * Complex.I)

/-- The area measure does not see the boundary or the exterior of the strip. -/
theorem ae_mem_stripAreaJetMeasure (α s : ℝ) (m : ℕ) :
    ∀ᵐ q ∂stripAreaJetMeasure α s m, q.2.1 ∈ Ioo (-α) α := by
  let w := fun σ : ℝ ↦ ENNReal.ofReal ((α - |σ|) ^ (2 * (m : ℝ) - s - 1))
  let μ := (volume.restrict (Ioo (-α) α)).withDensity w
  have hσ : ∀ᵐ σ ∂μ, σ ∈ Ioo (-α) α :=
    (ae_restrict_mem measurableSet_Ioo).filter_mono (withDensity_absolutelyContinuous _ w).ae_le
  have hq : ∀ᵐ q : ℝ × ℝ ∂μ.prod volume, q.1 ∈ Ioo (-α) α :=
    Measure.quasiMeasurePreserving_fst.ae hσ
  exact (Measure.quasiMeasurePreserving_snd (μ := (Measure.count : Measure (Fin (m+1))))
    (ν := μ.prod volume)).ae hq

private def stripAreaJetExt (α : ℝ) (m : ℕ) (F : ℂ → ℂ) (q : Fin (m+1) × (ℝ × ℝ)) : ℂ :=
  if q.2.1 ∈ Ioo (-α) α then stripAreaJet m F q else 0

private theorem measurable_stripAreaJetExt {α : ℝ} {m : ℕ} {F : ℂ → ℂ}
    (hF : ∀ k : Fin (m+1), ContinuousOn (iteratedDeriv k.val F) {z : ℂ | |z.re| < α}) :
    Measurable (stripAreaJetExt α m F) := by
  apply measurable_from_prod_countable_right
  intro k
  let S : Set (ℝ × ℝ) := Prod.fst ⁻¹' Ioo (-α) α
  let z := fun q : ℝ × ℝ ↦ (q.1 : ℂ) + q.2 * Complex.I
  have hz : Continuous z := by dsimp [z]; fun_prop
  have hzS : MapsTo z S {v : ℂ | |v.re| < α} := fun q hq ↦ by
    simpa [z] using (abs_lt.mpr (show q.1 ∈ Ioo (-α) α from hq))
  have hc := ((hF k).comp hz.continuousOn hzS).domRestrict.measurable
  apply measurable_of_restrict_of_restrict_compl (s := S) (measurable_fst measurableSet_Ioo)
  · convert hc using 1
    funext q
    simp [Set.domRestrict, stripAreaJetExt, stripAreaJet, z,
      show q.val.1 ∈ Ioo (-α) α from q.property]
  · have hzero : Sᶜ.domRestrict (fun q ↦ stripAreaJetExt α m F (k, q)) = fun _ ↦ 0 := by
      funext q
      simp [Set.domRestrict, stripAreaJetExt, show q.val.1 ∉ Ioo (-α) α from q.property]
    rw [hzero]
    exact measurable_const

private theorem stripAreaJetExt_ae_eq (α s : ℝ) (m : ℕ) (F : ℂ → ℂ) :
    stripAreaJetExt α m F =ᵐ[stripAreaJetMeasure α s m] stripAreaJet m F :=
  (ae_mem_stripAreaJetMeasure α s m).mono fun _ hq ↦ ite_eq_left hq

/-- No ambient measurability outside the open strip is required. -/
theorem aemeasurable_stripAreaJet {α s : ℝ} {m : ℕ} {F : ℂ → ℂ}
    (hF : ∀ k : Fin (m+1), ContinuousOn (iteratedDeriv k.val F) {z : ℂ | |z.re| < α}) :
    AEMeasurable (stripAreaJet m F) (stripAreaJetMeasure α s m) :=
  (measurable_stripAreaJetExt hF).aemeasurable.congr (stripAreaJetExt_ae_eq α s m F)

/-- Tonelli and finite counting identify the squared scalar jet integral exactly with
`stripAreaJetEnergy`, not merely up to equivalence of norms. -/
theorem lintegral_stripAreaJet_enorm_sq {α s : ℝ} {m : ℕ} {F : ℂ → ℂ}
    (hp : 1 ≤ 2 * (m : ℝ) - s)
    (hF : ∀ k : Fin (m+1), ContinuousOn (iteratedDeriv k.val F) {z : ℂ | |z.re| < α}) :
    (∫⁻ q, ‖stripAreaJet m F q‖ₑ ^ 2 ∂stripAreaJetMeasure α s m) =
      stripAreaJetEnergy α s m F := by
  let G := fun q ↦ ‖stripAreaJetExt α m F q‖ₑ ^ 2
  have hG : Measurable G := (measurable_stripAreaJetExt hF).eNorm.pow_const 2
  let g := fun q : ℝ × ℝ ↦ ∫⁻ k : Fin (m+1), G (k, q) ∂Measure.count
  have hg : Measurable g := hG.lintegral_prod_left'
  have hinner : Measurable (fun σ : ℝ ↦ ∫⁻ t : ℝ, g (σ, t)) := hg.lintegral_prod_right'
  have hw : Continuous (fun σ : ℝ ↦ (α - |σ|) ^ (2 * (m : ℝ) - s - 1)) :=
    (continuous_const.sub continuous_abs).rpow_const (fun _ ↦ Or.inr (sub_nonneg.mpr hp))
  calc
    _ = ∫⁻ q, G q ∂stripAreaJetMeasure α s m := by
      apply lintegral_congr_ae
      filter_upwards [stripAreaJetExt_ae_eq α s m F] with q hq
      simp only [G, hq]
    _ = _ := by
      rw [stripAreaJetMeasure, lintegral_prod_symm' G hG]
      change (∫⁻ q, g q ∂((volume.restrict (Ioo (-α) α)).withDensity _).prod volume) = _
      rw [lintegral_prod g hg.aemeasurable,
        lintegral_withDensity_eq_lintegral_mul _ hw.measurable.ennreal_ofReal hinner,
        stripAreaJetEnergy]
      refine setLIntegral_congr_fun measurableSet_Ioo fun σ hσ ↦ ?_
      simp only [Pi.mul_apply]
      congr 1
      apply lintegral_congr
      intro t
      simp only [g, lintegral_count, tsum_fintype, G, stripAreaJetExt, ite_eq_left hσ, stripAreaJet]
      exact Fin.sum_univ_eq_sum_range (fun k ↦ ‖iteratedDeriv k F ((σ : ℂ) + t * Complex.I)‖ₑ ^ 2) _


variable {α s : ℝ}

local notation "ν" => (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal (intervalSobolevDensity (-α) α s x))

private theorem areaProfile_density_continuous (α s : ℝ) :
    Continuous (intervalSobolevDensity (-α) α s) := by
  unfold intervalSobolevDensity
  have hleft : Continuous (fun x : ℝ ↦ Real.exp (2 * -α * x)) := by fun_prop
  have hright : Continuous (fun x : ℝ ↦ Real.exp (2 * α * x)) := by fun_prop
  exact (hleft.max hright).mul
    ((by fun_prop : Continuous fun x : ℝ ↦ 1 + x^2).rpow_const (fun _ ↦ Or.inl (by positivity)))

private theorem areaProfile_density_pos (α s x : ℝ) : 0 < intervalSobolevDensity (-α) α s x :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

theorem areaProfile_volume_ac : volume ≪ ν :=
  withDensity_absolutelyContinuous' (areaProfile_density_continuous α s).measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (areaProfile_density_pos α s x)).ne')

theorem areaProfile_memLp_exp_abs (hs : 0 ≤ s) (f : Lp ℂ 2 ν) :
    MemLp (fun x : ℝ ↦ Real.exp (α * |x|) • f x) 2 volume := by
  have hm := (Lp.aestronglyMeasurable f).mono_ac areaProfile_volume_ac
  have hw : Continuous fun x : ℝ ↦ Real.exp (α * |x|) := by fun_prop
  have hwm := hw.aestronglyMeasurable.smul hm
  apply (memLp_two_iff_integrable_sq_norm hwm).2
  have hsq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hd := (areaProfile_density_continuous α s).measurable.ennreal_ofReal
  have hI : Integrable (fun x : ℝ ↦ ‖f x‖ ^ 2 * intervalSobolevDensity (-α) α s x) volume := by
    refine ((integrable_withDensity_iff hd (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).1 hsq).congr ?_
    exact .of_forall fun x ↦ by simp only [ENNReal.toReal_ofReal (areaProfile_density_pos α s x).le]
  refine hI.mono' (hwm.norm.pow 2) (.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  change ‖Real.exp (α * |x|) • f x‖^2 ≤ _
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow, mul_comm _ (‖f x‖ ^ 2)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  unfold intervalSobolevDensity
  have hmax : Real.exp (α * |x|) ^ 2 ≤ max (Real.exp (2 * -α * x)) (Real.exp (2 * α * x)) := by
    rw [← Real.exp_nat_mul]
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
      exact le_max_of_le_right (Real.exp_le_exp.mpr (by push_cast; ring_nf; rfl))
    · rw [abs_of_nonpos hx]
      exact le_max_of_le_left (Real.exp_le_exp.mpr (by push_cast; ring_nf; rfl))
  exact hmax.trans (le_mul_of_one_le_right (le_trans (by positivity) hmax)
    (Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)))

theorem areaProfile_energy_eq (f : Lp ℂ 2 ν) :
    ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 * ENNReal.ofReal (intervalSobolevDensity (-α) α s x) =
      ENNReal.ofReal (‖f‖ ^ 2) := by
  have h := lintegral_withDensity_eq_lintegral_mul₀'
    (μ := (volume : Measure ℝ)) (areaProfile_density_continuous α s).measurable.ennreal_ofReal.aemeasurable
    ((Lp.aestronglyMeasurable f).eNorm.pow_const (2 : ℕ))
  calc
    _ = ∫⁻ x : ℝ, ‖f x‖ₑ ^ 2 ∂ν := by simpa only [Pi.mul_apply, mul_comm] using h.symm
    _ = _ := by
      rw [ENNReal.ofReal_pow (norm_nonneg f), ofReal_norm, Lp.eNorm_def]
      simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num)
        (Lp.aestronglyMeasurable f)).symm

theorem areaProfile_bilateralLaplace_congr {f g : ℝ → ℂ} (h : f =ᵐ[ν] g) :
    bilateralLaplace f = bilateralLaplace g := by
  funext z
  apply integral_congr_ae
  filter_upwards [areaProfile_volume_ac.ae_le h] with x hx
  rw [hx]

theorem areaProfile_bilateralLaplace_add (hs : 0 ≤ s) (f g : Lp ℂ 2 ν) {z : ℂ}
    (hz : |z.re| < α) : bilateralLaplace (⇑(f + g)) z = bilateralLaplace f z + bilateralLaplace g z := by
  rw [areaProfile_bilateralLaplace_congr (Lp.coeFn_add f g)]
  simp only [bilateralLaplace, Pi.add_apply, add_mul]
  exact integral_add (integrable_mul_cexp_of_memLp_exp_abs (areaProfile_memLp_exp_abs hs f) hz)
    (integrable_mul_cexp_of_memLp_exp_abs (areaProfile_memLp_exp_abs hs g) hz)

theorem areaProfile_bilateralLaplace_smul (c : ℂ) (f : Lp ℂ 2 ν) (z : ℂ) :
    bilateralLaplace (⇑(c • f)) z = c • bilateralLaplace f z := by
  rw [areaProfile_bilateralLaplace_congr (Lp.coeFn_smul c f)]
  simp only [bilateralLaplace, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]

private theorem area_eLpNorm_sq {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℂ} (hf : AEStronglyMeasurable f μ) :
    (eLpNorm f 2 μ)^2 = ∫⁻ x, ‖f x‖ₑ^2 ∂μ := by
  simpa using (eLpNorm_nnreal_pow_eq_lintegral (p := (2 : ℝ≥0)) (by norm_num) hf)

private theorem areaProfile_contDiffAt (hs : 0 ≤ s) (f : Lp ℂ 2 ν) (k : ℕ)
    {z : ℂ} (hz : |z.re| < α) : ContDiffAt ℂ k (bilateralLaplace f) z :=
  ((differentiableOn_bilateralLaplace (areaProfile_memLp_exp_abs hs f)).analyticAt
    ((continuous_abs.comp Complex.continuous_re).continuousAt.eventually (Iio_mem_nhds hz))).contDiffAt

/-- The pure area jet is realized in a single `L²` space, and the image of the
weighted radial profile space is closed. -/
theorem exists_stripAreaJetEmbedding (hα : 0 < α) (hs : 0 ≤ s) (m : ℕ)
    (hp : 1 ≤ 2 * (m : ℝ) - s) :
    ∃ T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (stripAreaJetMeasure α s m),
      IsClosed (Set.range T) ∧ Function.Injective T ∧
      ∀ f, (T f : _ → ℂ) =ᵐ[stripAreaJetMeasure α s m] stripAreaJet m (bilateralLaplace f) := by
  let μ := stripAreaJetMeasure α s m
  let jet (f : Lp ℂ 2 ν) := stripAreaJet m (bilateralLaplace f)
  have hc (f : Lp ℂ 2 ν) (k : Fin (m+1)) :=
    continuousOn_iteratedDeriv_bilateralLaplace (areaProfile_memLp_exp_abs hs f) k.val
  obtain ⟨c, C, hcpos, hCpos, hcompare⟩ := stripAreaJetEnergy_bilateralLaplace_comparable hα hs m hp
  have hsq (f : Lp ℂ 2 ν) := hcompare f (areaProfile_memLp_exp_abs hs f)
  have hm (f : Lp ℂ 2 ν) : MemLp (jet f) 2 μ := by
    have ha := (aemeasurable_stripAreaJet (s := s) (hc f)).aestronglyMeasurable
    change eLpNorm (jet f) 2 μ < ∞
    have htop : eLpNorm (jet f) 2 μ ^ 2 < ∞ := by
      rw [area_eLpNorm_sq ha, lintegral_stripAreaJet_enorm_sq hp (hc f)]
      exact (hsq f).2.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
        ((areaProfile_energy_eq f).symm ▸ ENNReal.ofReal_lt_top))
    by_contra! h
    simp [top_unique h] at htop
  let T₀ (f : Lp ℂ 2 ν) : Lp ℂ 2 μ := (hm f).toLp (jet f)
  have hrep (f : Lp ℂ 2 ν) : (T₀ f : _ → ℂ) =ᵐ[μ] jet f := (hm f).coeFn_toLp
  have hnorm (f : Lp ℂ 2 ν) : ENNReal.ofReal (‖T₀ f‖^2) =
      stripAreaJetEnergy α s m (bilateralLaplace f) := by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm, Lp.eNorm_def,
      area_eLpNorm_sq (Lp.aestronglyMeasurable (T₀ f)), ← lintegral_stripAreaJet_enorm_sq hp (hc f)]
    exact lintegral_congr_ae ((hrep f).mono fun _ h ↦ congrArg (fun v : ℂ ↦ ‖v‖ₑ^2) h)
  let L : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := T₀
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [hrep (f+g), hrep f, hrep g, Lp.coeFn_add (T₀ f) (T₀ g),
          ae_mem_stripAreaJetMeasure α s m] with q hsum hf hg hadd hq
        rw [hsum, hadd, Pi.add_apply, hf, hg]
        let z : ℂ := (q.2.1 : ℂ) + q.2.2 * Complex.I
        have hz : |z.re| < α := by simpa [z] using abs_lt.mpr hq
        have hnear : ∀ᶠ w in 𝓝 z, |(w : ℂ).re| < α :=
          (continuous_abs.comp Complex.continuous_re).continuousAt.eventually (Iio_mem_nhds hz)
        have he : bilateralLaplace (⇑(f+g)) =ᶠ[𝓝 z]
            fun w ↦ bilateralLaplace f w + bilateralLaplace g w :=
          hnear.mono fun _ hw ↦ areaProfile_bilateralLaplace_add hs f g hw
        change iteratedDeriv q.1.val (bilateralLaplace (⇑(f+g))) z = _
        rw [he.iteratedDeriv_eq, iteratedDeriv_fun_add
          (areaProfile_contDiffAt hs f _ hz) (areaProfile_contDiffAt hs g _ hz)]
        rfl
      map_smul' := fun d f ↦ by
        apply Lp.ext
        filter_upwards [hrep (d • f), hrep f, Lp.coeFn_smul d (T₀ f)] with q hdf hf hscl
        change (T₀ (d • f) : _ → ℂ) q = (d • T₀ f : Lp ℂ 2 μ) q
        rw [hdf, hscl, Pi.smul_apply, hf]
        change iteratedDeriv _ (bilateralLaplace (⇑(d • f))) _ = _
        rw [show bilateralLaplace (⇑(d • f)) = fun z ↦ d * bilateralLaplace f z from
          funext (areaProfile_bilateralLaplace_smul d f), iteratedDeriv_const_mul_field]
        rfl }
  have hb (f : Lp ℂ 2 ν) : c * ‖f‖^2 ≤ ‖T₀ f‖^2 ∧ ‖T₀ f‖^2 ≤ C * ‖f‖^2 := by
    have h := hsq f
    dsimp only at h
    rw [areaProfile_energy_eq, ← hnorm, ← ENNReal.ofReal_mul hcpos.le,
      ← ENNReal.ofReal_mul hCpos.le] at h
    exact ⟨(ENNReal.ofReal_le_ofReal_iff (sq_nonneg _)).1 h.1,
      (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCpos.le (sq_nonneg _))).1 h.2⟩
  have hu (f : Lp ℂ 2 ν) : ‖L f‖ ≤ Real.sqrt C * ‖f‖ := by
    apply le_of_sq_le_sq _ (by positivity)
    rw [mul_pow, Real.sq_sqrt hCpos.le]
    exact (hb f).2
  let T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ := L.mkContinuous (Real.sqrt C) hu
  have hg (f : Lp ℂ 2 ν) : ‖f‖ ≤ (Real.sqrt c)⁻¹ * ‖T f‖ := by
    have h : Real.sqrt c * ‖f‖ ≤ ‖T₀ f‖ := by
      apply le_of_sq_le_sq _ (norm_nonneg _)
      rw [mul_pow, Real.sq_sqrt hcpos.le]
      exact (hb f).1
    rw [← div_eq_inv_mul, le_div_iff₀ (Real.sqrt_pos.2 hcpos), mul_comm]
    exact h
  let A : ℝ≥0 := ⟨(Real.sqrt c)⁻¹, by positivity⟩
  have hanti : AntilipschitzWith A T := T.antilipschitz_of_bound hg
  exact ⟨T, hanti.isClosed_range T.uniformContinuous, hanti.injective, hrep⟩

/-- The exact area Hilbert space is a closed subspace of the measured strip jet space. -/
theorem exists_stripAreaJetEquiv (hα : 0 < α) (hs : 0 ≤ s) (m : ℕ)
    (hp : 1 ≤ 2 * (m : ℝ) - s) :
    ∃ H : Submodule ℂ (Lp ℂ 2 (stripAreaJetMeasure α s m)),
      IsClosed (H : Set (Lp ℂ 2 (stripAreaJetMeasure α s m))) ∧
      ∃ E : Lp ℂ 2 ν ≃L[ℂ] H, ∀ f,
        ((E f : Lp ℂ 2 (stripAreaJetMeasure α s m)) : _ → ℂ) =ᵐ[stripAreaJetMeasure α s m]
          stripAreaJet m (bilateralLaplace f) := by
  obtain ⟨T, hclosed, hinj, hrep⟩ := exists_stripAreaJetEmbedding hα hs m hp
  let H := T.toLinearMap.range
  have hc : IsClosed (H : Set (Lp ℂ 2 (stripAreaJetMeasure α s m))) := hclosed
  let : CompleteSpace H := hc.completeSpace_coe
  let U := T.codRestrict H (fun f ↦ LinearMap.mem_range_self T.toLinearMap f)
  have hu : Function.Bijective U := by
    constructor
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · rintro ⟨_, ⟨f, rfl⟩⟩
      exact ⟨f, rfl⟩
  exact ⟨H, hc, ContinuousLinearEquiv.ofBijective U (LinearMap.ker_eq_bot.mpr hu.1)
    (LinearMap.range_eq_top.mpr hu.2), hrep⟩

/-- A retained moment of an actual weighted profile is continuous right up to both edges.
The pointwise majorant is the sum of the weighted energy density and a single integrable
Japanese bracket; neither term depends on the evaluation site. -/
theorem continuousOn_bilateralLaplace_moment_closedStrip {a s : ℝ} {k : ℕ}
    (hk : 2 * (k : ℝ) + 1 < s)
    (f : Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity (-a) a s x))) :
    ContinuousOn (bilateralLaplace (fun x : ℝ ↦ (x : ℂ)^k * f x)) {z : ℂ | |z.re| ≤ a} := by
  let ρ := intervalSobolevDensity (-a) a s
  let B (x : ℝ) := (1 + x ^ 2) ^ (-(s - 2 * (k : ℝ)) / 2)
  have hρ : Continuous ρ := by
    unfold ρ intervalSobolevDensity
    refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun x ↦ Or.inl ?_)
    positivity
  have hpos (x : ℝ) : 0 < ρ x :=
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  have hd := hρ.measurable.ennreal_ofReal
  have hbase : volume ≪ volume.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) :=
    withDensity_absolutelyContinuous' hd.aemeasurable
      (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  have hfm := (Lp.aestronglyMeasurable f).mono_ac hbase
  have hA : Integrable (fun x : ℝ ↦ ‖f x‖ ^ 2 * ρ x) volume := by
    have hsq := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
    refine ((integrable_withDensity_iff hd (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).1 hsq).congr ?_
    exact .of_forall fun x ↦ by simp only [ENNReal.toReal_ofReal (hpos x).le]
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < s - 2 * k := by
    rw [Module.finrank_self]; push_cast; linarith
  have hB : Integrable B volume := by
    simpa only [B, Real.norm_eq_abs, sq_abs] using
      (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hr)
  unfold bilateralLaplace
  apply continuousOn_of_dominated (bound := fun x ↦ ‖f x‖ ^ 2 * ρ x + B x)
  · intro z _
    exact ((Complex.continuous_ofReal.pow k).aestronglyMeasurable.mul hfm).mul
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable)
  · intro z hz
    apply Eventually.of_forall
    intro x
    obtain ⟨hl, hu⟩ := abs_le.mp (show |z.re| ≤ a from hz)
    let M := max (Real.exp (2 * -a * x)) (Real.exp (2 * a * x))
    have hM : Real.exp (2 * z.re * x) ≤ M := by
      rcases le_total 0 x with hx | hx
      · exact le_max_of_le_right (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hu) hx]))
      · exact le_max_of_le_left (Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr hl) (neg_nonneg.mpr hx)]))
    have hx : 0 < 1 + x ^ 2 := by positivity
    have he : Real.exp (z.re * x) ^ 2 = Real.exp (2 * z.re * x) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hp : (|x| ^ k) ^ 2 ≤ (1 + x ^ 2) ^ k := by
      rw [← pow_mul, Nat.mul_comm k 2, pow_mul, sq_abs]
      exact pow_le_pow_left₀ (sq_nonneg x) (by linarith) k
    have hcancel : ρ x * B x = M * (1 + x ^ 2) ^ k := by
      change (M * _ ^ (s / 2)) * _ = _
      dsimp only [B]
      rw [mul_assoc, ← Real.rpow_add hx, ← Real.rpow_natCast (1 + x ^ 2) k]
      congr 2
      ring
    have hb : 0 ≤ B x := Real.rpow_nonneg hx.le _
    have hA0 : 0 ≤ ‖f x‖ ^ 2 * ρ x := mul_nonneg (sq_nonneg _) (hpos x).le
    apply le_of_sq_le_sq _ (add_nonneg hA0 hb)
    simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_pow, he]
    calc
      _ ≤ ((1 + x ^ 2) ^ k * ‖f x‖ ^ 2) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_right hp (sq_nonneg _)) hM
          (Real.exp_pos _).le (mul_nonneg (pow_nonneg hx.le _) (sq_nonneg _))
      _ = (‖f x‖ ^ 2 * ρ x) * B x := by rw [mul_assoc (‖f x‖ ^ 2), hcancel]; ring
      _ ≤ _ := by nlinarith [sq_nonneg (‖f x‖ ^ 2 * ρ x - B x), mul_nonneg hA0 hb]
  · exact hA.add hB
  · exact .of_forall fun x ↦ (continuous_const.mul
      (Complex.continuous_exp.comp (continuous_id.mul continuous_const))).continuousOn

/-- An interior strip derivative converges to the corresponding retained moment
at either boundary, with no restriction on the direction of approach. -/
theorem tendsto_iteratedDeriv_bilateralLaplace_at_edge {k : ℕ}
    (hk : 2 * (k : ℝ) + 1 < s) (f : Lp ℂ 2 ν) {ρ : ℂ} (hρ : |ρ.re| = α) :
    Tendsto (iteratedDeriv k (bilateralLaplace f)) (𝓝[{z : ℂ | |z.re| < α}] ρ)
      (𝓝 (bilateralLaplace (fun x : ℝ ↦ (x : ℂ)^k * f x) ρ)) := by
  have hc := continuousOn_bilateralLaplace_moment_closedStrip hk f ρ hρ.le
  have hI : {z : ℂ | |z.re| < α} ⊆ {z : ℂ | |z.re| ≤ α} :=
    fun z hz ↦ (show |z.re| < α from hz).le
  have he : iteratedDeriv k (bilateralLaplace f) =ᶠ[𝓝[{z : ℂ | |z.re| < α}] ρ]
      bilateralLaplace (fun x : ℝ ↦ (x : ℂ)^k * f x) :=
    eventually_mem_nhdsWithin.mono (fun _ hz ↦
      iteratedDeriv_bilateralLaplace_eq_moment (areaProfile_memLp_exp_abs (by linarith) f) k hz)
  exact (tendsto_congr' he).mpr (hc.mono hI)

end RiemannMasullo
