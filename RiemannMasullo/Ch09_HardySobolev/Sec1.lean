module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec3a
public import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
import Mathlib.MeasureTheory.Integral.Prod
import RiemannMasullo.ForMathlib.MeasureTheory.Function.ContinuousMapDense
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic
import RiemannMasullo.ForMathlib.MeasureTheory.Integral.Bochner.Regular

/-!
# Sobolev spaces on locally compact abelian groups

Masullo, §9.1, pp. 395–403.
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set Topology TopologicalSpace
open scoped CompactlySupported ENNReal NNReal ZeroAtInfty

namespace RiemannMasullo

local instance sobolevDualMeasurableSpace {A : Type*} [CommGroup A] [TopologicalSpace A] :
    MeasurableSpace (PontryaginDual A) := borel _

section Weighted

variable {A : Type*}

/-- Paper: Definition 9.1.1.1, p. 396. On the group where the weight is evaluated,
a Sobolev weight is nonnegative, continuous, and subadditive up to one positive constant.
Deviation: The argument group is explicit. For the paper's weight on G it is the dual of G. -/
def IsSobolevWeight [Mul A] [TopologicalSpace A] (w : A → ℝ≥0) : Prop :=
  Continuous w ∧ ∃ C : ℝ≥0, 0 < C ∧ ∀ x y, w (x * y) ≤ C * (w x + w y)

/-- Paper: Definition 9.1.1.1, p. 396. Every constant nonnegative weight is a Sobolev weight.
Deviation: Sanity check on the weight condition. -/
theorem isSobolevWeight_const [Mul A] [TopologicalSpace A] (c : ℝ≥0) :
    IsSobolevWeight (fun _ : A ↦ c) :=
  ⟨continuous_const, 1, one_pos, fun _ _ ↦ by rw [one_mul]; exact le_self_add⟩

/-- Paper: Definition 9.1.1.1, p. 396. The measure for degree s has density
`(1 + w²)^(s/2)` with respect to the measure on the group carrying the weight. -/
def sobolevMeasure [MeasurableSpace A] (ν : Measure A) (w : A → ℝ≥0) (s : ℝ) : Measure A :=
  ν.withDensity fun x ↦ ENNReal.ofReal ((1 + (w x : ℝ) ^ 2) ^ (s / 2))

/-- Paper: Definition 9.1.1.1, p. 396. At degree zero, the weighted measure is the original
measure.
Deviation: Sanity check on the normalization in (9.1.1.3). -/
theorem sobolevMeasure_zero [MeasurableSpace A] (ν : Measure A) (w : A → ℝ≥0) :
    sobolevMeasure ν w 0 = ν := by
  simp [sobolevMeasure]

-- TODO(paper-gap): The input to the completion is written C_c(Ĝ) but its norm takes a
-- Fourier transform and still evaluates on Ĝ. Use the Fourier-side interpretation below.

/-- Paper: Definition 9.1.1.1, p. 396. The Sobolev space consists of square-integrable
classes for the weighted measure. Use the dual group and the Plancherel measure for H^s_w(G).
Deviation: The completed space is realized directly as the weighted L² from Lemma 9.1.1.2.
An element in this model already represents the Fourier-side function. -/
abbrev WeightedSobolev [MeasurableSpace A] (ν : Measure A) (w : A → ℝ≥0) (s : ℝ) :=
  Lp ℂ 2 (sobolevMeasure ν w s)

/-- Paper: Definition 9.1.1.1, p. 396. In the weighted L² model the norm is the square root
of the integral of the squared modulus times the prescribed density.
Deviation: Sanity check on (9.1.1.3), written directly for Fourier-side representatives. -/
theorem weightedSobolev_norm [MeasurableSpace A] [TopologicalSpace A] [BorelSpace A]
    (ν : Measure A) {w : A → ℝ≥0} (hw : Continuous w) (s : ℝ)
    (f : WeightedSobolev ν w s) :
    Integrable (fun x ↦ ‖f x‖ ^ 2 * (1 + (w x : ℝ) ^ 2) ^ (s / 2)) ν ∧
    ‖f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 * (1 + (w x : ℝ) ^ 2) ^ (s / 2) ∂ν) := by
  let μ : Measure A := sobolevMeasure ν w s
  let ρ : A → ℝ := fun x ↦ (1 + (w x : ℝ) ^ 2) ^ (s / 2)
  have hρ_cont : Continuous ρ := by
    refine Continuous.rpow_const (continuous_const.add
      ((NNReal.continuous_coe.comp hw).pow 2)) ?_
    intro x
    refine Or.inl (ne_of_gt ?_)
    exact lt_of_lt_of_le one_pos (le_add_of_nonneg_right (sq_nonneg _))
  have hρ_nonneg (x : A) : 0 ≤ ρ x := by
    dsimp only [ρ]
    exact Real.rpow_nonneg (add_nonneg zero_le_one (sq_nonneg _)) _
  have hdens : Measurable (fun x ↦ ENNReal.ofReal (ρ x)) :=
    (ENNReal.continuous_ofReal.comp hρ_cont).measurable
  have hμ : μ = ν.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) := rfl
  have hflt : ∀ᵐ x ∂ν, ENNReal.ofReal (ρ x) < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hint_sq : Integrable (fun x ↦ ‖(f : A → ℂ) x‖ ^ 2) μ :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  have hint : Integrable (fun x ↦ ‖f x‖ ^ 2 * ρ x) ν := by
    rw [hμ] at hint_sq
    refine ((integrable_withDensity_iff hdens hflt).1 hint_sq).congr ?_
    filter_upwards with x
    rw [ENNReal.toReal_ofReal (hρ_nonneg x)]
  refine ⟨hint, ?_⟩
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (x := f)]
  refine congrArg Real.sqrt ?_
  rw [L2.inner_def (f := f) (g := f), ← integral_re (L2.integrable_inner f f)]
  simp_rw [inner_self_eq_norm_sq]
  calc
    ∫ x, ‖(f : A → ℂ) x‖ ^ 2 ∂sobolevMeasure ν w s
        = ∫ x, ‖(f : A → ℂ) x‖ ^ 2 ∂ν.withDensity (fun x ↦ ENNReal.ofReal (ρ x)) := rfl
    _ = ∫ x, (ENNReal.ofReal (ρ x)).toReal • ‖(f : A → ℂ) x‖ ^ 2 ∂ν :=
      integral_withDensity_eq_integral_toReal_smul hdens hflt _
    _ = ∫ x, ‖f x‖ ^ 2 * (1 + (w x : ℝ) ^ 2) ^ (s / 2) ∂ν := by
      refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
      dsimp
      rw [ENNReal.toReal_ofReal (hρ_nonneg x), mul_comm]

end Weighted

section LCA

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]

variable (μ : Measure G) [μ.IsHaarMeasure] [μ.Regular]
  (ν : Measure (PontryaginDual G)) {w : PontryaginDual G → ℝ≥0} {s : ℝ}

/-- Paper: Definition 9.1.1.1, p. 396. Continuous compactly supported functions embed as a
dense complex-linear subspace of the Fourier-side Sobolev space.
Deviation: The norm in (9.1.1.3) is applied to the test functions as Fourier-side data. -/
theorem weightedSobolev_compactSupport_dense (_hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) :
    ∃ J : (PontryaginDual G →C_c ℂ) →ₗ[ℂ] WeightedSobolev ν w s,
      DenseRange J ∧ Function.Injective J ∧
        ∀ f, (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : ν.IsHaarMeasure := _hν.1
  let : ν.Regular := _hν.2.1
  let ρ (χ : PontryaginDual G) : ℝ := (1 + (w χ : ℝ) ^ 2) ^ (s / 2)
  have hρpos (χ : PontryaginDual G) : 0 < ρ χ := Real.rpow_pos_of_pos (by positivity) _
  have hbase : Continuous (fun χ ↦ 1 + (w χ : ℝ) ^ 2) :=
    continuous_const.add ((NNReal.continuous_coe.comp _hw.1).pow 2)
  have hρ : Continuous ρ := hbase.rpow_const fun χ ↦ Or.inl (by positivity)
  let νw := sobolevMeasure ν w s
  let : IsLocallyFiniteMeasure νw := IsLocallyFiniteMeasure.withDensity_ofReal hρ
  have hννw : ν ≪ νw :=
    withDensity_absolutelyContinuous' hρ.measurable.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun χ ↦ (ENNReal.ofReal_pos.mpr (hρpos χ)).ne')
  have mem (f : PontryaginDual G →C_c ℂ) : MemLp (f : PontryaginDual G → ℂ) 2 νw :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  let J : (PontryaginDual G →C_c ℂ) →ₗ[ℂ] WeightedSobolev ν w s :=
    { toFun := fun f ↦ (mem f).toLp f
      map_add' := fun f g ↦ MemLp.toLp_add (mem f) (mem g)
      map_smul' := fun c f ↦ MemLp.toLp_const_smul c (mem f) }
  have hJ (f : PontryaginDual G →C_c ℂ) :
      (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) :=
    hννw.ae_eq (mem f).coeFn_toLp
  have hJinj : Function.Injective J := by
    intro f g hfg
    apply DFunLike.coe_injective
    exact Measure.eq_of_ae_eq ((hJ f).symm.trans (hfg ▸ hJ g)) f.continuous g.continuous
  refine ⟨J, ?_, hJinj, hJ⟩
  -- Multiplying by the square root of the density transfers the weighted L² seminorm.
  let m (χ : PontryaginDual G) : ℂ := Real.sqrt (ρ χ)
  have hm : Continuous m := Complex.continuous_ofReal.comp hρ.sqrt
  have hmne (χ : PontryaginDual G) : m χ ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (hρpos χ)).ne'
  have hnorm (u : PontryaginDual G → ℂ) (hu : AEStronglyMeasurable u νw) :
      eLpNorm u 2 νw = eLpNorm (fun χ ↦ m χ * u χ) 2 ν := by
    have huν := hu.mono_ac hννw
    change eLpNorm u 2 νw = eLpNorm (m * u) 2 ν
    rw [eLpNorm_eq_eLpNorm' (p := 2) (by simp) ENNReal.ofNat_ne_top hu,
      eLpNorm_eq_eLpNorm' (p := 2) (by simp) ENNReal.ofNat_ne_top (hm.aestronglyMeasurable.mul huν)]
    simp only [eLpNorm', ENNReal.toReal_ofNat, ENNReal.rpow_two]
    congr 1
    change (∫⁻ χ, ‖u χ‖ₑ ^ 2 ∂ν.withDensity (fun χ ↦ ENNReal.ofReal (ρ χ))) = _
    rw [lintegral_withDensity_eq_lintegral_mul₀ hρ.measurable.aemeasurable.ennreal_ofReal
      (huν.eNorm.pow_const 2)]
    apply lintegral_congr
    intro χ
    have hmSq : ‖m χ‖ₑ ^ 2 = ENNReal.ofReal (ρ χ) := by
      rw [← ofReal_norm, show ‖m χ‖ = Real.sqrt (ρ χ) by simp [m],
        ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt (hρpos χ).le]
    simp only [Pi.mul_apply, eNorm_mul, mul_pow, hmSq]
  intro f
  refine EMetric.mem_closure_iff.mpr fun ε hε ↦ ?_
  have hf := Lp.memLp f
  have hmf : MemLp (fun χ ↦ m χ * f χ) 2 ν := by
    change eLpNorm (fun χ ↦ m χ * f χ) 2 ν < ∞
    rw [← hnorm _ hf.aestronglyMeasurable]
    exact hf.eLpNorm_lt_top
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨g, hgDist, hgCont, hgSupp⟩ :=
    exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top hmf hδ.ne'
  let a : PontryaginDual G →C_c ℂ :=
    ⟨⟨fun χ ↦ (m χ)⁻¹ * g χ, (hm.inv₀ hmne).mul hgCont⟩, hgSupp.mul_left⟩
  refine ⟨J a, ⟨a, rfl⟩, ?_⟩
  have hfa : ((f : PontryaginDual G → ℂ) - (J a : PontryaginDual G → ℂ)) =ᵐ[νw]
      (f : PontryaginDual G → ℂ) - (a : PontryaginDual G → ℂ) :=
    Filter.EventuallyEq.rfl.sub (mem a).coeFn_toLp
  change edist f (J a) < ε
  rw [Lp.edist_def, eLpNorm_congr_ae hfa,
    hnorm _ (hf.aestronglyMeasurable.sub (mem a).aestronglyMeasurable)]
  have hdiff : (fun χ ↦ m χ * (f χ - a χ)) = (fun χ ↦ m χ * f χ) - g := by
    funext χ
    simp [a, mul_sub, hmne χ]
  change eLpNorm (fun χ ↦ m χ * (f χ - a χ)) 2 ν < ε
  rw [hdiff]
  exact hgDist.trans_lt hδε

/-- Paper: Lemma 9.1.1.2, p. 396. The weighted L² space is complete with its
Mathlib L² inner product. -/
theorem weightedSobolev_complete (_hν : IsLCAPlancherelMeasure μ ν) (_hw : IsSobolevWeight w) :
    CompleteSpace (WeightedSobolev ν w s) := by
  infer_instance

omit [μ.Regular] in
/-- Paper: Lemma 9.1.1.2, p. 396. For a second-countable group, the Sobolev Hilbert
space is separable. -/
theorem weightedSobolev_separable [SecondCountableTopology G]
    (_hν : IsLCAPlancherelMeasure μ ν) (_hw : IsSobolevWeight w) :
    SeparableSpace (WeightedSobolev ν w s) := by sorry

/-- Paper: Proposition 9.1.1.3(1), p. 396. In nonnegative degree the Sobolev space
includes continuously and contractively into Haar L² via inverse Plancherel. -/
theorem weightedSobolev_toL2 (hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) (_hs : 0 ≤ s) :
    let U := Classical.choose (lcaFourier_unitary μ ν hν).exists
    ∃ J : WeightedSobolev ν w s →L[ℂ] Lp ℂ 2 μ,
      Function.Injective J ∧ ‖J‖ ≤ 1 ∧
        ∀ f, (U (J f) : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by
  intro U
  let νw := sobolevMeasure ν w s
  have hle : ν ≤ νw := calc
    ν = ν.withDensity 1 := withDensity_one.symm
    _ ≤ νw := by
      apply withDensity_mono
      refine ae_of_all _ fun χ ↦ ?_
      simpa only [Pi.one_apply, ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.one_le_rpow (le_add_of_nonneg_right (sq_nonneg (w χ : ℝ)))
          (div_nonneg _hs (by norm_num)))
  have hνw : νw ≪ ν := withDensity_absolutelyContinuous _ _
  have mem (f : WeightedSobolev ν w s) : MemLp (f : PontryaginDual G → ℂ) 2 ν :=
    (Lp.memLp f).mono_measure hle
  let I : WeightedSobolev ν w s →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun f ↦ (mem f).toLp f
      map_add' f g :=
        (MemLp.toLp_congr (mem (f + g)) ((mem f).add (mem g))
          (ae_mono hle (Lp.coeFn_add f g))).trans (MemLp.toLp_add (mem f) (mem g))
      map_smul' c f :=
        (MemLp.toLp_congr (mem (c • f)) ((mem f).const_smul c)
          (ae_mono hle (Lp.coeFn_smul c f))).trans (MemLp.toLp_const_smul c (mem f)) }
  let K := U.symm.toLinearEquiv.toLinearMap.comp I
  have hK (f : WeightedSobolev ν w s) : ‖K f‖ ≤ 1 * ‖f‖ := by
    change ‖U.symm (I f)‖ ≤ _
    rw [U.symm.norm_map, one_mul]
    change ‖(mem f).toLp f‖ ≤ ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.memLp f).eLpNorm_lt_top.ne (eLpNorm_mono_measure _ hle)
  let J := K.mkContinuous 1 hK
  have hJ (f : WeightedSobolev ν w s) :
      (U (J f) : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by
    change (U (U.symm (I f)) : PontryaginDual G → ℂ) =ᵐ[ν] _
    rw [U.apply_symm_apply]
    exact (mem f).coeFn_toLp
  refine ⟨J, ?_, K.mkContinuous_norm_le zero_le_one hK, hJ⟩
  intro f g hfg
  exact Lp.ext (hνw.ae_eq ((hJ f).symm.trans (hfg ▸ hJ g)))

-- TODO(paper-gap): In (9.1.1.6) the lower-degree input is printed where the inclusion
-- requires a higher-degree input. Elements of the lower-degree space can have infinite
-- higher-degree weighted integral.

/-- Paper: Proposition 9.1.1.3(2), p. 397. For s' > s ≥ 0, the inclusion from
degree s' to degree s is contractive and preserves the Fourier-side representative.
Deviation: The variable in (9.1.1.6) ranges over the source of the displayed inclusion. -/
theorem weightedSobolev_ofHigherDegree (_hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) (_hs : 0 ≤ s) {s' : ℝ} (_hss' : s < s') :
    ∃ J : WeightedSobolev ν w s' →L[ℂ] WeightedSobolev ν w s,
      Function.Injective J ∧ ‖J‖ ≤ 1 ∧
        ∀ f, (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) := by
  have hmono {a b : ℝ} (hab : a ≤ b) : sobolevMeasure ν w a ≤ sobolevMeasure ν w b := by
    apply withDensity_mono
    refine ae_of_all _ fun χ ↦ ENNReal.ofReal_le_ofReal ?_
    exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (sq_nonneg _))
      (div_le_div_of_nonneg_right hab (by norm_num))
  have hle := hmono _hss'.le
  have hνle : ν ≤ sobolevMeasure ν w s := calc
    ν = sobolevMeasure ν w 0 := (sobolevMeasure_zero ν w).symm
    _ ≤ sobolevMeasure ν w s := hmono _hs
  have h_ac : sobolevMeasure ν w s' ≪ ν := withDensity_absolutelyContinuous _ _
  have hle' : sobolevMeasure ν w s ≤ (1 : ℝ≥0∞) • sobolevMeasure ν w s' := by
    simpa only [one_smul] using hle
  have hone : (1 : ℝ≥0∞) ≠ ∞ := ENNReal.one_ne_top
  let I : WeightedSobolev ν w s' →L[ℝ] WeightedSobolev ν w s :=
    Lp.LpToLpOfMeasureLeSMul hone hle'
  have hI (f : WeightedSobolev ν w s') :
      (I f : PontryaginDual G → ℂ) =ᵐ[sobolevMeasure ν w s] (f : PontryaginDual G → ℂ) :=
    Lp.coeFn_LpToLpOfMeasureLeSMul hone hle' f
  let J : WeightedSobolev ν w s' →L[ℂ] WeightedSobolev ν w s :=
    { toFun := I
      map_add' := I.map_add
      map_smul' := fun c f ↦ Lp.ext <|
        (hI (c • f)).trans <| Filter.EventuallyEq.trans (ae_mono hle (Lp.coeFn_smul c f)) <|
          ((hI f).symm.fun_comp (c • ·)).trans (Lp.coeFn_smul c (I f)).symm
      cont := I.continuous }
  have hJ (f : WeightedSobolev ν w s') :
      (J f : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ) :=
    ae_mono hνle (hI f)
  refine ⟨J, ?_, ?_, hJ⟩
  · intro f g hfg
    exact Lp.ext (h_ac.ae_eq ((hJ f).symm.trans (hfg ▸ hJ g)))
  · rw [← ContinuousLinearMap.norm_restrictScalars (𝕜' := ℝ) J]
    change ‖I‖ ≤ 1
    simpa [I] using Lp.norm_LpToLpOfMeasureLeSMul_le (E := ℂ) (p := 2) hone hle'

omit [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 9.1.1.3(3), p. 397. Cauchy–Schwarz with the density and its
reciprocal controls the unweighted integral of the norm of a Fourier-side Sobolev element. -/
private theorem weightedSobolev_integrable
    (hw : IsSobolevWeight w)
    (h : Integrable (fun χ ↦ (1 + (w χ : ℝ) ^ 2) ^ (-s / 2)) ν)
    (f : WeightedSobolev ν w s) :
    Integrable (f : PontryaginDual G → ℂ) ν ∧
      (∫ χ, ‖f χ‖ ∂ν) ≤ ‖f‖ * Real.sqrt (∫ χ, (1 + (w χ : ℝ) ^ 2) ^ (-s / 2) ∂ν) := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let ρ (χ : PontryaginDual G) : ℝ := (1 + (w χ : ℝ) ^ 2) ^ (s / 2)
  have hρ (χ : PontryaginDual G) : 0 < ρ χ := Real.rpow_pos_of_pos (by positivity) _
  have hrecip (χ : PontryaginDual G) : (1 + (w χ : ℝ) ^ 2) ^ (-s / 2) = (ρ χ)⁻¹ := by
    rw [neg_div, Real.rpow_neg (by positivity)]
  have hρc : Continuous ρ := by
    have hbase : Continuous (fun χ ↦ 1 + (w χ : ℝ) ^ 2) :=
      continuous_const.add ((NNReal.continuous_coe.comp hw.1).pow 2)
    exact hbase.rpow_const fun χ ↦ Or.inl (by positivity)
  have hAC : ν ≪ sobolevMeasure ν w s :=
    withDensity_absolutelyContinuous' hρc.measurable.aemeasurable.ennreal_ofReal
      (ae_of_all _ fun χ ↦ (ENNReal.ofReal_pos.mpr (hρ χ)).ne')
  have hf := weightedSobolev_norm ν hw.1 s f
  let a (χ : PontryaginDual G) := ‖f χ‖ * Real.sqrt (ρ χ)
  let b (χ : PontryaginDual G) := Real.sqrt (ρ χ)⁻¹
  have ha (χ : PontryaginDual G) : 0 ≤ a χ := mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  have hb (χ : PontryaginDual G) : 0 ≤ b χ := Real.sqrt_nonneg _
  have ha_sq (χ : PontryaginDual G) : a χ ^ 2 = ‖f χ‖ ^ 2 * ρ χ := by
    change (‖f χ‖ * Real.sqrt (ρ χ)) ^ 2 = _
    rw [mul_pow, Real.sq_sqrt (hρ χ).le]
  have hb_sq (χ : PontryaginDual G) : b χ ^ 2 = (1 + (w χ : ℝ) ^ 2) ^ (-s / 2) := by
    change (Real.sqrt (ρ χ)⁻¹) ^ 2 = _
    rw [Real.sq_sqrt (inv_nonneg.mpr (hρ χ).le), hrecip]
  have haLp : MemLp a 2 ν := by
    have haM : AEStronglyMeasurable a ν :=
      ((Lp.aestronglyMeasurable f).mono_ac hAC).norm.mul hρc.sqrt.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm haM).2
    simpa only [Real.norm_of_nonneg (ha _), ha_sq] using hf.1
  have hbLp : MemLp b 2 ν := by
    have hbM : AEStronglyMeasurable b ν :=
      (hρc.inv₀ fun χ ↦ (hρ χ).ne').sqrt.aestronglyMeasurable
    apply (memLp_two_iff_integrable_sq_norm hbM).2
    simpa only [Real.norm_of_nonneg (hb _), hb_sq] using h
  have hab (χ : PontryaginDual G) : a χ * b χ = ‖f χ‖ := by
    dsimp only [a, b]
    rw [mul_assoc, ← Real.sqrt_mul (hρ χ).le,
      mul_inv_cancel₀ (hρ χ).ne', Real.sqrt_one, mul_one]
  have hint : Integrable (fun χ ↦ ‖f χ‖) ν := by
    have hm : MemLp (a * b) 1 ν := haLp.mul hbLp
    simpa only [Pi.mul_def, hab] using memLp_one_iff_integrable.mp hm
  refine ⟨⟨(Lp.aestronglyMeasurable f).mono_ac hAC,
    (hasFiniteIntegral_norm_iff _).mp hint.hasFiniteIntegral⟩, ?_⟩
  have hbound := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
    (show MemLp a (ENNReal.ofReal 2) ν by simpa using haLp)
    (show MemLp b (ENNReal.ofReal 2) ν by simpa using hbLp)
  rw [hf.2]
  simpa only [Real.norm_of_nonneg (ha _), Real.norm_of_nonneg (hb _), hab, Real.rpow_two,
    ha_sq, hb_sq, ← Real.sqrt_eq_rpow] using hbound

omit [μ.IsHaarMeasure] in
/-- The inverse Fourier integral and the forward transform are adjoint on integrable
test functions. Compactly supported approximations provide a product-measurable kernel
even when the product topology and product σ-algebra have different Borel sets. -/
private theorem lcaInverseFourier_integral_pairing
    {u : PontryaginDual G → ℂ} {q : G → ℂ} (hu : Integrable u ν) (hq : Integrable q μ)
    [ν.Regular] :
    (∫ x, (∫ χ, u χ * (χ x : ℂ) ∂ν) * star (q x) ∂μ) =
      ∫ χ, u χ * star (lcaFourier μ q χ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  obtain ⟨S, -, hqZero, hSσ⟩ := hq.aefinStronglyMeasurable.exists_set_sigmaFinite
  obtain ⟨T, -, huZero, hTσ⟩ := hu.aefinStronglyMeasurable.exists_set_sigmaFinite
  let := hSσ
  let := hTσ
  have hqZero := ae_imp_of_ae_restrict hqZero
  have huZero := ae_imp_of_ae_restrict huZero
  obtain ⟨Q, hQc, hQ, htQ⟩ := exists_tendsto_ae_compactSupport hq
  obtain ⟨U, hUc, hU, htU⟩ := exists_tendsto_ae_compactSupport hu
  let K (x : G) (χ : PontryaginDual G) := (u χ * (χ x : ℂ)) * star (q x)
  let A (n : ℕ) (p : G × PontryaginDual G) := (U n p.2 * (p.2 p.1 : ℂ)) * star (Q n p.1)
  have hEval : Continuous (fun p : G × PontryaginDual G ↦ (p.2 p.1 : ℂ)) :=
    continuous_subtype_val.comp ((continuous_eval (F := C(G, Circle))).comp
      (((ContinuousMonoidHom.isInducing_toContinuousMap G Circle).continuous.comp
        continuous_snd).prodMk continuous_fst))
  have hA (n : ℕ) : StronglyMeasurable (A n) := by
    apply HasCompactSupport.stronglyMeasurable_of_prod
      ((((hU n).comp continuous_snd).mul hEval).mul ((hQ n).comp continuous_fst).star)
    refine HasCompactSupport.intro ((hQc n).prod (hUc n)) ?_
    intro p hp
    by_cases hq : p.1 ∈ tsupport (Q n)
    · have hu : U n p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun hu ↦ hp ⟨hq, hu⟩)
      simp [hu]
    · simp [image_eq_zero_of_notMem_tsupport hq]
  let k (p : G × PontryaginDual G) := limUnder atTop (fun n ↦ A n p)
  have hk : StronglyMeasurable k := StronglyMeasurable.limUnder hA
  have hLimit : ∀ᵐ x ∂μ, ∀ᵐ χ ∂ν, k (x, χ) = K x χ := by
    filter_upwards [htQ] with x hx
    filter_upwards [htU] with χ hχ
    exact ((hχ.mul tendsto_const_nhds).mul hx.star).limUnder_eq
  have hLimit' : ∀ᵐ χ ∂ν, ∀ᵐ x ∂μ, k (x, χ) = K x χ := by
    filter_upwards [htU] with χ hχ
    filter_upwards [htQ] with x hx
    exact ((hχ.mul tendsto_const_nhds).mul hx.star).limUnder_eq
  have hChar (x : G) : AEStronglyMeasurable (fun χ : PontryaginDual G ↦ (χ x : ℂ)) ν :=
    (hEval.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  have hRow (x : G) : Integrable (K x) ν :=
    (hu.mul_bdd (c := 1) (hChar x) (.of_forall fun χ ↦ (Circle.norm_coe (χ x)).le)).mul_const _
  have hInt : Integrable k ((μ.restrict S).prod (ν.restrict T)) := by
    apply (integrable_prod_iff hk.aestronglyMeasurable).2
    have hLim : ∀ᵐ x ∂μ.restrict S, (fun χ ↦ k (x, χ)) =ᵐ[ν.restrict T] K x :=
      ae_restrict_of_ae (hLimit.mono fun _ hx ↦ ae_restrict_of_ae hx)
    refine ⟨hLim.mono fun x hx ↦ (hRow x).restrict.congr hx.symm, ?_⟩
    refine (hq.norm.mul_const (∫ χ in T, ‖u χ‖ ∂ν)).restrict.congr ?_
    filter_upwards [hLim] with x hx
    symm
    calc
      _ = ∫ χ in T, ‖K x χ‖ ∂ν := integral_congr_ae (hx.mono fun χ hχ ↦ congrArg norm hχ)
      _ = _ := by simp [K, integral_mul_const, mul_comm]
  have hrowEq : ∀ᵐ x ∂μ, (∫ χ in T, k (x, χ) ∂ν) = ∫ χ, K x χ ∂ν := by
    filter_upwards [hLimit] with x hx
    rw [integral_congr_ae (ae_restrict_of_ae hx)]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact huZero.mono fun χ hχ hmem ↦ by simp [K, hχ hmem]
  have hcolEq : ∀ᵐ χ ∂ν, (∫ x in S, k (x, χ) ∂μ) = ∫ x, K x χ ∂μ := by
    filter_upwards [hLimit'] with χ hχ
    rw [integral_congr_ae (ae_restrict_of_ae hχ)]
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    exact hqZero.mono fun x hx hmem ↦ by simp [K, hx hmem]
  calc
    _ = ∫ x, ∫ χ, K x χ ∂ν ∂μ := by simp_rw [K, integral_mul_const]
    _ = ∫ x in S, ∫ χ, K x χ ∂ν ∂μ := by
      symm
      exact setIntegral_eq_integral_of_ae_compl_eq_zero
        (hqZero.mono fun x hx hmem ↦ by simp [K, hx hmem])
    _ = ∫ x in S, ∫ χ in T, k (x, χ) ∂ν ∂μ :=
      integral_congr_ae (ae_restrict_of_ae (hrowEq.mono fun _ hx ↦ hx.symm))
    _ = ∫ χ in T, ∫ x in S, k (x, χ) ∂μ ∂ν := integral_integral_swap hInt
    _ = ∫ χ in T, ∫ x, K x χ ∂μ ∂ν := integral_congr_ae (ae_restrict_of_ae hcolEq)
    _ = ∫ χ, ∫ x, K x χ ∂μ ∂ν := setIntegral_eq_integral_of_ae_compl_eq_zero
      (huZero.mono fun χ hχ hmem ↦ by simp [K, hχ hmem])
    _ = _ := by
      congr with χ
      simp only [K, mul_assoc, integral_const_mul, lcaFourier, Complex.star_def,
        ← integral_conj, map_mul, starRingEnd_self_apply]
      congr 1
      apply integral_congr_ae
      exact .of_forall fun x ↦ mul_comm _ _

/-- Paper: Proposition 9.1.1.3(3), p. 397. For an L² element whose Plancherel transform is
integrable, the inverse Fourier integral represents that element and vanishes at infinity. -/
private theorem lcaInverseFourier_zeroAtInfty (hν : IsLCAPlancherelMeasure μ ν)
    (v : Lp ℂ 2 μ) (u : PontryaginDual G → ℂ) (hu : Integrable u ν)
    (hv : ((lcaFourier_unitary μ ν hν).exists.choose v : PontryaginDual G → ℂ) =ᵐ[ν] u) :
    ∃ F : C₀(G, ℂ), (F : G → ℂ) =ᵐ[μ] (v : G → ℂ) ∧
      ∀ x, F x = ∫ χ, u χ * (χ x : ℂ) ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  obtain ⟨H, hH⟩ := lcaFourier_zeroAtInfty ν hu
  let e : CocompactMap G (PontryaginDual (PontryaginDual G)) :=
    ⟨⟨pontryaginDual_eval, pontryaginDual_eval.continuous⟩,
      isClosedEmbedding_pontryaginDual_eval.tendsto_cocompact⟩
  let F : C₀(G, ℂ) := (H.comp e).comp
    ⟨⟨Inv.inv, continuous_inv⟩, (Homeomorph.inv G).isClosedEmbedding.tendsto_cocompact⟩
  have hF (x : G) : F x = ∫ χ, u χ * (χ x : ℂ) ∂ν := by
    change H (pontryaginDual_eval x⁻¹) = _
    rw [hH]
    unfold lcaFourier
    apply integral_congr_ae
    exact .of_forall fun χ ↦ by
      change u χ * star (χ x⁻¹ : ℂ) = _
      rw [map_inv, Circle.coe_inv_eq_conj, ← Complex.star_def, star_star]
  refine ⟨F, ?_, hF⟩
  -- The nonzero set of a function in C₀ lies in a countable union of compact sets.
  let K (n : ℕ) : Set G := {x | 1 / ((n : ℝ) + 1) ≤ ‖F x‖}
  have hK (n : ℕ) : IsCompact (K n) := by
    have hc : IsClosed (K n) := isClosed_le continuous_const F.continuous.norm
    obtain ⟨L, hL, hsub⟩ := mem_cocompact.mp
      ((Metric.tendsto_nhds.mp F.zero_at_infty') _ (by positivity : 0 < 1 / ((n : ℝ) + 1)))
    exact hL.of_isClosed_subset hc fun x hx ↦ by
      by_contra hxL
      change 1 / ((n : ℝ) + 1) ≤ ‖F x‖ at hx
      have hlt : dist (F x) 0 < 1 / ((n : ℝ) + 1) := hsub hxL
      exact not_lt_of_ge hx (dist_zero_right (F x) ▸ hlt)
  let S := ⋃ n, K n
  have hS : MeasurableSet S := MeasurableSet.iUnion fun n ↦ (hK n).isClosed.measurableSet
  have hFS : ∀ x ∈ Sᶜ, F x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hne)
    exact hx (mem_iUnion.mpr ⟨n, hn.le⟩)
  have hσ : SigmaFinite (μ.restrict S) := by
    refine ⟨⟨⟨fun n ↦ K n ∪ Sᶜ, fun _ ↦ trivial, fun n ↦ ?_, ?_⟩⟩⟩
    · rw [Measure.restrict_apply ((hK n).isClosed.measurableSet.union hS.compl),
        union_inter_distrib_right, compl_inter_self, union_empty]
      exact (measure_mono inter_subset_left).trans_lt (hK n).measure_lt_top
    · rw [← iUnion_union]
      exact union_compl_self S
  have hFin : AEFinStronglyMeasurable (F : G → ℂ) μ :=
    (F.continuous.stronglyMeasurable.finStronglyMeasurable_of_set_sigmaFinite
      hS hFS hσ).aefinStronglyMeasurable
  apply AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq _ _ _
    hFin ((Lp.memLp v).aefinStronglyMeasurable two_ne_zero ENNReal.ofNat_ne_top)
  · intro A _ hA
    let : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.mpr hA.ne
    exact Integrable.of_bound F.continuous.aestronglyMeasurable ‖F.toBCF‖
      (.of_forall F.toBCF.norm_coe_le_norm)
  · exact fun A _ hA ↦ integrableOn_Lp_of_measure_ne_top v (by norm_num) hA.ne
  · intro A hA hAμ
    let q : G → ℂ := A.indicator fun _ ↦ 1
    have hq : Integrable q μ := memLp_one_iff_integrable.mp
      (memLp_indicator_const 1 hA.nullMeasurableSet 1 (.inr hAμ.ne))
    have hq₂ : MemLp q 2 μ := memLp_indicator_const 2 hA.nullMeasurableSet 1 (.inr hAμ.ne)
    let U := (lcaFourier_unitary μ ν hν).exists.choose
    have hU := (lcaFourier_unitary μ ν hν).exists.choose_spec q hq hq₂
    have hIndic (g : G → ℂ) : (∫ x, g x * star (q x) ∂μ) = ∫ x in A, g x ∂μ := by
      rw [← integral_indicator hA]
      congr with x
      by_cases hx : x ∈ A <;> simp [q, hx]
    calc
      _ = ∫ x, (∫ χ, u χ * (χ x : ℂ) ∂ν) * star (q x) ∂μ := by
        simp_rw [← hF]
        exact (hIndic F).symm
      _ = ∫ χ, u χ * star (lcaFourier μ q χ) ∂ν :=
        lcaInverseFourier_integral_pairing μ ν hu hq
      _ = inner ℂ (U (hq₂.toLp q)) (U v) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [hv, hU] with χ hχ hχ'
        rw [RCLike.inner_apply, starRingEnd_apply, hχ, hχ']
      _ = inner ℂ (hq₂.toLp q) v := U.inner_map_map _ _
      _ = _ := by
        rw [← hIndic v, L2.inner_def]
        exact integral_congr_ae (hq₂.coeFn_toLp.mono fun x hx ↦ by
          change inner ℂ ((hq₂.toLp q) x) (v x) = v x * star (q x)
          rw [RCLike.inner_apply, starRingEnd_apply, hx])

/-- Paper: Proposition 9.1.1.3(3), p. 397. When the reciprocal density is integrable,
the inverse Plancherel class of each Sobolev element has a unique representative
vanishing at infinity. The representative map is a bounded linear injection. -/
theorem weightedSobolev_toZeroAtInfty (hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) (_hs : 0 ≤ s)
    (_h : Integrable (fun χ ↦ (1 + (w χ : ℝ) ^ 2) ^ (-s / 2)) ν) :
    let U := Classical.choose (lcaFourier_unitary μ ν hν).exists
    ∃ (J : WeightedSobolev ν w s →L[ℂ] Lp ℂ 2 μ)
      (E : WeightedSobolev ν w s →L[ℂ] C₀(G, ℂ)) (C : ℝ),
      (∀ f, (U (J f) : PontryaginDual G → ℂ) =ᵐ[ν] (f : PontryaginDual G → ℂ)) ∧
      Function.Injective E ∧ 0 < C ∧ ‖E‖ ≤ C ∧
      ∀ f g, g = E f ↔ (g : G → ℂ) =ᵐ[μ] (J f : G → ℂ) := by
  intro U
  obtain ⟨J, hJinj, -, hJ⟩ := weightedSobolev_toL2 μ ν hν _hw _hs
  have hL1 (f : WeightedSobolev ν w s) := weightedSobolev_integrable ν _hw _h f
  choose F hF hFormula using fun f ↦
    lcaInverseFourier_zeroAtInfty μ ν hν (J f) f (hL1 f).1 (hJ f)
  have unique (f : WeightedSobolev ν w s) (g : C₀(G, ℂ))
      (hg : (g : G → ℂ) =ᵐ[μ] (J f : G → ℂ)) : g = F f :=
    DFunLike.coe_injective (Measure.eq_of_ae_eq (hg.trans (hF f).symm)
      g.continuous (F f).continuous)
  let L : WeightedSobolev ν w s →ₗ[ℂ] C₀(G, ℂ) :=
    { toFun := F
      map_add' := fun f g ↦ (unique (f + g) (F f + F g) (by
        rw [J.map_add]
        exact ((hF f).add (hF g)).trans (Lp.coeFn_add (J f) (J g)).symm)).symm
      map_smul' := fun c f ↦ (unique (c • f) (c • F f) (by
        rw [J.map_smul]
        exact ((hF f).fun_comp (c • ·)).trans (Lp.coeFn_smul c (J f)).symm)).symm }
  let C := Real.sqrt (∫ χ, (1 + (w χ : ℝ) ^ 2) ^ (-s / 2) ∂ν) + 1
  have hC : 0 < C := add_pos_of_nonneg_of_pos (Real.sqrt_nonneg _) one_pos
  have hBound (f : WeightedSobolev ν w s) : ‖L f‖ ≤ C * ‖f‖ := by
    rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply (BoundedContinuousFunction.norm_le (mul_nonneg hC.le (norm_nonneg _))).mpr
    intro x
    change ‖F f x‖ ≤ C * ‖f‖
    rw [hFormula]
    calc
      _ ≤ ∫ χ, ‖f χ‖ ∂ν := by
        simpa only [norm_mul, Circle.norm_coe, mul_one] using
          norm_integral_le_integral_norm (μ := ν) (fun χ ↦ f χ * (χ x : ℂ))
      _ ≤ C * ‖f‖ := ((hL1 f).2).trans (by
        rw [mul_comm C]
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg _))
  let E := L.mkContinuous C hBound
  refine ⟨J, E, C, hJ, ?_, hC, L.mkContinuous_norm_le hC.le hBound, ?_⟩
  · intro f g hfg
    change F f = F g at hfg
    apply hJinj
    exact Lp.ext ((hF f).symm.trans (hfg ▸ hF g))
  · intro f g
    change g = F f ↔ _
    exact ⟨fun h ↦ h ▸ hF f, unique f g⟩

/-- The unweighted product pairing identifies the strong dual of a weighted L² space with the
weighted L² space of opposite degree, for any continuous weight on a Borel space. -/
private theorem weightedSobolev_dual_of_continuous {X : Type*} [MeasurableSpace X]
    [TopologicalSpace X] [BorelSpace X] (ν : Measure X) {w : X → ℝ≥0} (hw : Continuous w)
    (s : ℝ) :
    ∃! T : StrongDual ℂ (WeightedSobolev ν w s) ≃ₗᵢ[ℂ] WeightedSobolev ν w (-s),
      ∀ Λ f, Integrable (fun χ ↦ f χ * T Λ χ) ν ∧ Λ f = ∫ χ, f χ * T Λ χ ∂ν := by
  let ρ (t : ℝ) (χ : X) := (1 + (w χ : ℝ) ^ 2) ^ (t / 2)
  have hρpos (t : ℝ) (χ : X) : 0 < ρ t χ :=
    Real.rpow_pos_of_pos (by positivity) _
  have hρ (t : ℝ) : Continuous (ρ t) := by
    have hcont : Continuous (fun χ ↦ 1 + (w χ : ℝ) ^ 2) :=
      continuous_const.add ((NNReal.continuous_coe.comp hw).pow 2)
    exact hcont.rpow_const fun χ ↦ Or.inl (by positivity)
  have hrecip (t : ℝ) (χ : X) : ρ t χ * ρ (-t) χ = 1 := by
    dsimp only [ρ]
    rw [← Real.rpow_add (by positivity), neg_div, add_neg_cancel, Real.rpow_zero]
  have hdens (t : ℝ) : Measurable (fun χ ↦ ENNReal.ofReal (ρ t χ)) :=
    (hρ t).measurable.ennreal_ofReal
  have hfinite (t : ℝ) : ∀ᵐ χ ∂ν, ENNReal.ofReal (ρ t χ) < ∞ :=
    ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hbase (t : ℝ) : ν ≪ sobolevMeasure ν w t :=
    withDensity_absolutelyContinuous' (hdens t).aemeasurable
      (ae_of_all _ fun χ ↦ (ENNReal.ofReal_pos.mpr (hρpos t χ)).ne')
  have hweighted (t : ℝ) : sobolevMeasure ν w t ≪ ν := withDensity_absolutelyContinuous _ _
  -- Conjugation times the density interchanges the two weighted L² spaces.
  let u (t : ℝ) (f : WeightedSobolev ν w t) (χ : X) : ℂ :=
    (ρ t χ : ℂ) * star (f χ)
  have hsq (t : ℝ) (f : WeightedSobolev ν w t) (χ : X) :
      ‖u t f χ‖ ^ 2 * ρ (-t) χ = ‖f χ‖ ^ 2 * ρ t χ := by
    calc
      _ = ‖f χ‖ ^ 2 * (ρ t χ * (ρ t χ * ρ (-t) χ)) := by
        dsimp only [u]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hρpos t χ), norm_star]
        ring
      _ = _ := by rw [hrecip, mul_one]
  have hmem (t : ℝ) (f : WeightedSobolev ν w t) :
      MemLp (u t f) 2 (sobolevMeasure ν w (-t)) := by
    have hmeas : AEStronglyMeasurable (u t f) (sobolevMeasure ν w (-t)) :=
      (Complex.continuous_ofReal.comp (hρ t)).aestronglyMeasurable.mul
        (((Lp.aestronglyMeasurable f).mono_ac (hbase t)).mono_ac (hweighted (-t))).star
    apply (memLp_two_iff_integrable_sq_norm hmeas).2
    change Integrable (fun χ ↦ ‖u t f χ‖ ^ 2) (ν.withDensity fun χ ↦ ENNReal.ofReal (ρ (-t) χ))
    apply (integrable_withDensity_iff (hdens (-t)) (hfinite (-t))).2
    refine (weightedSobolev_norm ν hw t f).1.congr (ae_of_all _ fun χ ↦ ?_)
    change ‖f χ‖ ^ 2 * ρ t χ = ‖u t f χ‖ ^ 2 * (ENNReal.ofReal (ρ (-t) χ)).toReal
    rw [ENNReal.toReal_ofReal (hρpos (-t) χ).le, hsq]
  let S (t : ℝ) (f : WeightedSobolev ν w t) : WeightedSobolev ν w (-t) :=
    (hmem t f).toLp (u t f)
  have hS (t : ℝ) (f : WeightedSobolev ν w t) :
      (S t f : X → ℂ) =ᵐ[ν] u t f :=
    (hbase (-t)).ae_eq (hmem t f).coeFn_toLp
  have hSnorm (t : ℝ) (f : WeightedSobolev ν w t) : ‖S t f‖ = ‖f‖ := by
    rw [(weightedSobolev_norm ν hw (-t) (S t f)).2, (weightedSobolev_norm ν hw t f).2]
    congr 1
    apply integral_congr_ae
    filter_upwards [hS t f] with χ hχ
    change ‖S t f χ‖ ^ 2 * ρ (-t) χ = ‖f χ‖ ^ 2 * ρ t χ
    rw [hχ, hsq]
  let C : WeightedSobolev ν w s →ₗᵢ⋆[ℂ] WeightedSobolev ν w (-s) :=
    { toFun := S s
      map_add' := fun f g ↦ Lp.ext <| (hweighted (-s)).ae_eq <| by
        filter_upwards [hS s (f + g), hS s f, hS s g,
          (hbase s).ae_eq (Lp.coeFn_add f g),
          (hbase (-s)).ae_eq (Lp.coeFn_add (S s f) (S s g))] with χ hfg hf hg hχ hsum
        rw [hfg, hsum]
        change u s (f + g) χ = S s f χ + S s g χ
        rw [hf, hg]
        simp only [u, hχ, Pi.add_apply, star_add, mul_add]
      map_smul' := fun c f ↦ Lp.ext <| (hweighted (-s)).ae_eq <| by
        filter_upwards [hS s (c • f), hS s f, (hbase s).ae_eq (Lp.coeFn_smul c f),
          (hbase (-s)).ae_eq (Lp.coeFn_smul ((starRingEnd ℂ) c) (S s f))]
          with χ hcf hf hχ hsmul
        rw [hcf, hsmul]
        change u s (c • f) χ = (starRingEnd ℂ) c • S s f χ
        rw [hf]
        simp only [u, hχ, Pi.smul_apply, starRingEnd_apply, smul_eq_mul, star_mul', mul_left_comm]
      norm_map' := hSnorm s }
  have hSurj : Function.Surjective C := by
    intro g
    have hs' : - -s = s := neg_neg s
    let f : WeightedSobolev ν w s := hs' ▸ S (-s) g
    have hf : (f : X → ℂ) =ᵐ[ν] u (-s) g := by
      have hcast (t : ℝ) (ht : - -s = t) :
          ((ht ▸ S (-s) g : WeightedSobolev ν w t) : X → ℂ) = S (-s) g := by
        subst t
        rfl
      exact (hcast s hs').eventuallyEq.trans (hS (-s) g)
    refine ⟨f, Lp.ext ((hweighted (-s)).ae_eq ?_)⟩
    change (S s f : X → ℂ) =ᵐ[ν] g
    filter_upwards [hS s f, hf] with χ hSf hfχ
    have hstar : star (ρ (-s) χ : ℂ) = (ρ (-s) χ : ℂ) := Complex.conj_ofReal _
    rw [hSf]
    simp only [u, hfχ, star_mul', hstar, star_star]
    rw [← mul_assoc, ← Complex.ofReal_mul, hrecip, Complex.ofReal_one, one_mul]
  let R := InnerProductSpace.toDual ℂ (WeightedSobolev ν w s)
  let T : StrongDual ℂ (WeightedSobolev ν w s) ≃ₗᵢ[ℂ] WeightedSobolev ν w (-s) :=
    R.symm.trans (LinearIsometryEquiv.ofSurjective C hSurj)
  have hPair (Λ : StrongDual ℂ (WeightedSobolev ν w s)) (f : WeightedSobolev ν w s) :
      Integrable (fun χ ↦ f χ * T Λ χ) ν ∧
        Λ f = ∫ χ, f χ * T Λ χ ∂ν := by
    let g := R.symm Λ
    have hprod : (fun χ ↦ f χ * T Λ χ) =ᵐ[ν]
        fun χ ↦ (ENNReal.ofReal (ρ s χ)).toReal • inner ℂ (g χ) (f χ) := by
      filter_upwards [hS s g] with χ hχ
      change f χ * S s g χ = _
      rw [hχ, ENNReal.toReal_ofReal (hρpos s χ).le, RCLike.inner_apply, starRingEnd_apply]
      simp only [u, Complex.real_smul, mul_left_comm]
    refine ⟨?_, ?_⟩
    · exact ((integrable_withDensity_iff_integrable_smul' (hdens s) (hfinite s)).1
        (L2.integrable_inner g f)).congr hprod.symm
    · calc
        Λ f = inner ℂ g f := InnerProductSpace.toDual_symm_apply.symm
        _ = ∫ χ, inner ℂ (g χ) (f χ) ∂sobolevMeasure ν w s := L2.inner_def g f
        _ = ∫ χ, (ENNReal.ofReal (ρ s χ)).toReal • inner ℂ (g χ) (f χ) ∂ν :=
          integral_withDensity_eq_integral_toReal_smul (hdens s) (hfinite s) _
        _ = ∫ χ, f χ * T Λ χ ∂ν := integral_congr_ae hprod.symm
  refine ⟨T, hPair, fun T' hT' ↦ LinearIsometryEquiv.ext fun Λ ↦ ?_⟩
  apply T.symm.injective
  rw [T.symm_apply_apply]
  apply ContinuousLinearMap.ext
  intro f
  rw [(hPair (T.symm (T' Λ)) f).2, T.apply_symm_apply, (hT' Λ f).2]

-- TODO(paper-gap): The bound (9.1.1.15) places an extra square root on each L² norm.

/-- Paper: Lemma 9.1.1.5, p. 397. The unweighted integral of the pointwise product
pairs opposite degrees. It represents every continuous linear functional uniquely and
isometrically by an element in the opposite degree. -/
theorem weightedSobolev_dual (_hν : IsLCAPlancherelMeasure μ ν)
    (_hw : IsSobolevWeight w) (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (WeightedSobolev ν w s) ≃ₗᵢ[ℂ] WeightedSobolev ν w (-s),
      ∀ Λ f, Integrable (fun χ ↦ f χ * T Λ χ) ν ∧ Λ f = ∫ χ, f χ * T Λ χ ∂ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  exact weightedSobolev_dual_of_continuous ν _hw.1 s

end LCA

section Modulated

variable {G : Type*} [CommGroup G] [TopologicalSpace G]
  (m : G →ₜ* ℝ≥0ˣ)

/-- Paper: (9.1.2.1), p. 399. The logarithmic Sobolev weight is the absolute
value of the logarithm of the module. -/
def modulatedSobolevWeight (x : G) : ℝ≥0 :=
  ⟨|Real.log ((m x).val : ℝ)|, abs_nonneg _⟩

/-- Paper: (9.1.2.1), p. 399. At an element of module exp(t), the weight is |t|.
Deviation: Sanity check in logarithmic coordinates. -/
theorem modulatedSobolevWeight_of_exp {x : G} (t : ℝ)
    (hx : ((m x).val : ℝ) = Real.exp t) :
    (modulatedSobolevWeight m x : ℝ) = |t| := by sorry

/-- Paper: (9.1.2.1), p. 399. The logarithmic weight satisfies the Sobolev
weight condition with subadditivity constant one. -/
theorem modulatedSobolevWeight_subadditive :
    Continuous (modulatedSobolevWeight m) ∧
      ∀ x y, modulatedSobolevWeight m (x * y) ≤
        modulatedSobolevWeight m x + modulatedSobolevWeight m y := by
  have hne (x : G) : ((m x).val : ℝ) ≠ 0 :=
    NNReal.coe_ne_zero.mpr (m x).ne_zero
  constructor
  · have hm : Continuous (fun x ↦ ((m x).val : ℝ)) :=
      NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
    exact ((hm.log hne).abs).subtype_mk _
  · intro x y
    change |Real.log ((m (x * y)).val : ℝ)| ≤
      |Real.log ((m x).val : ℝ)| + |Real.log ((m y).val : ℝ)|
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul (hne x) (hne y)]
    exact abs_add_le _ _

variable [MeasurableSpace G] (μ : Measure G)

/-- Paper: Definition 9.1.2.1, p. 399. The modulated Sobolev space is square-integrable
with the logarithmic weight on the original group, as in (9.1.2.3).
Deviation: Use the direct weighted L² realization in every real degree. The paper introduces
nonnegative degrees here and uses negative degrees in Proposition 9.1.2.5. -/
abbrev ModulatedSobolev (s : ℝ) :=
  WeightedSobolev μ (modulatedSobolevWeight m) s

/-- Paper: Definition 9.1.2.1, p. 399. The norm on the modulated Sobolev space is the weighted
integral norm on the original group.
Deviation: Sanity check for the direct model and its extension to real degrees. -/
theorem modulatedSobolev_norm [BorelSpace G] (s : ℝ) (f : ModulatedSobolev m μ s) :
    Integrable (fun x ↦ ‖f x‖ ^ 2 * (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (s / 2)) μ ∧
    ‖f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 * (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (s / 2) ∂μ) :=
  weightedSobolev_norm μ (modulatedSobolevWeight_subadditive m).1 s f

-- Definition D.2.1.1, p. 793, defines modulated groups for second-countable `G`, and the
-- structure lemmas for `IsModulation` assume it; the recall on p. 399 omits the word.
variable [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [BorelSpace G] [μ.IsHaarMeasure]

variable (ν : Measure (PontryaginDual G))

omit [SecondCountableTopology G] in
/-- The Fourier transform of an integrable square-integrable function on the dual,
evaluated at the canonical characters of the bidual, preserves its L² norm. -/
private theorem lcaFourier_eval_memLp [μ.Regular] (hν : IsLCAPlancherelMeasure μ ν)
    {u : PontryaginDual G → ℂ} (hu : Integrable u ν) (hu₂ : MemLp u 2 ν) :
    MemLp (fun x : G ↦ lcaFourier ν u (pontryaginDual_eval x)) 2 μ ∧
      eLpNorm (fun x : G ↦ lcaFourier ν u (pontryaginDual_eval x)) 2 μ = eLpNorm u 2 ν := by
  let U := (lcaFourier_unitary μ ν hν).exists.choose
  let v := U.symm (hu₂.toLp u)
  have hv : (U v : PontryaginDual G → ℂ) =ᵐ[ν] u := by
    rw [show U v = hu₂.toLp u from U.apply_symm_apply _]
    exact hu₂.coeFn_toLp
  obtain ⟨F, hF, hFormula⟩ := lcaInverseFourier_zeroAtInfty μ ν hν v u hu hv
  have hEval : (fun x : G ↦ lcaFourier ν u (pontryaginDual_eval x)) = F ∘ Inv.inv := by
    funext x
    rw [Function.comp_apply, hFormula, lcaFourier]
    congr with χ
    change u χ * star (χ x : ℂ) = u χ * (χ x⁻¹ : ℂ)
    rw [map_inv, Circle.coe_inv_eq_conj, Complex.star_def]
  have hMem : MemLp (F : G → ℂ) 2 μ := MemLp.ae_eq hF.symm (Lp.memLp v)
  have hInv := Measure.measurePreserving_inv μ
  refine ⟨hEval ▸ hMem.comp_measurePreserving hInv, ?_⟩
  rw [hEval, eLpNorm_comp_measurePreserving hMem.aestronglyMeasurable hInv,
    eLpNorm_congr_ae hF, ← Lp.eNorm_def, U.symm.eNorm_map]
  exact Lp.eNorm_toLp hu₂

omit [SecondCountableTopology G] in
/-- A translation of the bidual evaluation has the same Plancherel norm, since
translation of a Fourier transform multiplies its input by a unit-modulus character. -/
private theorem lcaFourier_mul_eval_memLp [μ.Regular] (hν : IsLCAPlancherelMeasure μ ν)
    (η : PontryaginDual (PontryaginDual G))
    {u : PontryaginDual G → ℂ} (hu : Integrable u ν) (hu₂ : MemLp u 2 ν) :
    MemLp (fun x : G ↦ lcaFourier ν u (η * pontryaginDual_eval x)) 2 μ ∧
      eLpNorm (fun x : G ↦ lcaFourier ν u (η * pontryaginDual_eval x)) 2 μ = eLpNorm u 2 ν := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let c (χ : PontryaginDual G) : ℂ := star (η χ : ℂ)
  have hc : AEStronglyMeasurable c ν :=
    (continuous_subtype_val.comp η.continuous).star.aestronglyMeasurable
  have hcn (χ : PontryaginDual G) : ‖c χ‖ = 1 := by simp [c]
  have hNorm (χ : PontryaginDual G) : ‖u χ * c χ‖ = ‖u χ‖ := by
    rw [norm_mul, hcn, mul_one]
  have hNorm₂ : eLpNorm (u * c) 2 ν = eLpNorm u 2 ν :=
    eLpNorm_congr_norm_ae (hu₂.aestronglyMeasurable.mul hc) hu₂.aestronglyMeasurable
      (.of_forall hNorm)
  have hc₂ : MemLp (u * c) 2 ν :=
    hu₂.congr_norm (hu₂.aestronglyMeasurable.mul hc) (.of_forall fun χ ↦ (hNorm χ).symm)
  have hEq : (fun x : G ↦ lcaFourier ν u (η * pontryaginDual_eval x)) =
      fun x ↦ lcaFourier ν (u * c) (pontryaginDual_eval x) := by
    funext x
    unfold lcaFourier
    congr with χ
    change u χ * star (↑(η χ * pontryaginDual_eval x χ) : ℂ) =
      (u χ * star (η χ : ℂ)) * star (pontryaginDual_eval x χ : ℂ)
    rw [Circle.coe_mul, star_mul, mul_assoc, mul_comm (star (η χ : ℂ))]
  rw [hEq, ← hNorm₂]
  exact lcaFourier_eval_memLp μ ν hν (hu.mul_bdd hc (.of_forall fun χ ↦ (hcn χ).le)) hc₂

/-- Paper: Theorem D.1.1.1(2), p. 746. Evaluation identifies the group with its bidual.
Deviation: This proof assumes a second-countable group and an available Plancherel measure.
The Fourier isometries on two distinct cosets would give a nonzero integrable
density on their disjoint union with every character integral equal to zero. -/
private theorem pontryaginDual_bidual_of_plancherel
    (hν : IsLCAPlancherelMeasure μ ν) :
    ∃ b : G ≃ₜ* PontryaginDual (PontryaginDual G), ∀ x χ, b x χ = χ x := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : ν.IsHaarMeasure := hν.1
  let : ν.Regular := hν.2.1
  let b := pontryaginDual_eval (G := G)
  have hEmb : IsClosedEmbedding b := isClosedEmbedding_pontryaginDual_eval (G := G)
  have hSurj : Function.Surjective b := by
    intro η
    by_contra hη
    let H := PontryaginDual G
    let D : Submodule ℂ (Lp ℂ 2 ν) :=
      { carrier := {u | Integrable (u : H → ℂ) ν}
        zero_mem' := (integrable_zero H ℂ ν).congr (Lp.coeFn_zero ℂ 2 ν).symm
        add_mem' := fun {_ _} hu hv ↦ (hu.add hv).congr (Lp.coeFn_add _ _).symm
        smul_mem' := fun c _ hu ↦ (hu.smul c).congr (Lp.coeFn_smul c _).symm }
    let F (ψ : PontryaginDual H) (u : D) (x : G) := lcaFourier ν u (ψ * b x)
    have hLp (ψ : PontryaginDual H) (u : D) :=
      lcaFourier_mul_eval_memLp μ ν hν ψ u.2 (Lp.memLp u.1)
    let J (ψ : PontryaginDual H) (u : D) : Lp ℂ 2 μ := (hLp ψ u).1.toLp (F ψ u)
    have hJ (ψ : PontryaginDual H) (u : D) : (J ψ u : G → ℂ) =ᵐ[μ] F ψ u :=
      MemLp.coeFn_toLp _
    have hKernel (u : D) (ζ : PontryaginDual H) :
        Integrable (fun χ ↦ u.val χ * star (ζ χ : ℂ)) ν :=
      u.2.mul_bdd (c := 1) (continuous_subtype_val.comp ζ.continuous).star.aestronglyMeasurable
        (.of_forall fun χ ↦ by simp)
    let L (ψ : PontryaginDual H) : D →ₗᵢ[ℂ] Lp ℂ 2 μ :=
      { toFun := J ψ
        map_add' := fun u v ↦ by
          apply Lp.ext
          filter_upwards [hJ ψ (u + v), hJ ψ u, hJ ψ v, Lp.coeFn_add (J ψ u) (J ψ v)]
            with x huv hu hv hsum
          change J ψ (u + v) x = (J ψ u + J ψ v) x
          rw [huv, hsum, Pi.add_apply, hu, hv]
          unfold F lcaFourier
          rw [← integral_add (hKernel u _) (hKernel v _)]
          exact integral_congr_ae ((Lp.coeFn_add u.val v.val).mono fun χ hχ ↦ by
            change (u.val + v.val) χ * _ = _
            rw [hχ, Pi.add_apply, add_mul])
        map_smul' := fun c u ↦ by
          apply Lp.ext
          filter_upwards [hJ ψ (c • u), hJ ψ u, Lp.coeFn_smul c (J ψ u)]
            with x hcu hu hsmul
          change J ψ (c • u) x = (c • J ψ u) x
          rw [hcu, hsmul, Pi.smul_apply, hu]
          unfold F lcaFourier
          rw [← integral_smul]
          exact integral_congr_ae ((Lp.coeFn_smul c u.val).mono fun χ hχ ↦ by
            change (c • u.val) χ * _ = _
            rw [hχ, Pi.smul_apply, smul_mul_assoc])
        norm_map' := fun u ↦ by
          change ‖(hLp ψ u).1.toLp (F ψ u)‖ = ‖u.val‖
          rw [Lp.norm_toLp, (hLp ψ u).2, Lp.norm_def] }
    have hInner (ψ : PontryaginDual H) (u v : D) :
        ∫ x, F ψ v x * star (F ψ u x) ∂μ = inner ℂ u v := by
      rw [← (L ψ).inner_map_map u v, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hJ ψ u, hJ ψ v] with x hu hv
      change _ = inner ℂ (J ψ u x) (J ψ v x)
      rw [RCLike.inner_apply, starRingEnd_apply, hu, hv]
    -- An indicator of a compact neighborhood supplies a common nonzero input.
    obtain ⟨K, hK, hK₁⟩ := exists_compact_mem_nhds (1 : H)
    let u : H → ℂ := K.indicator fun _ ↦ 1
    have hu (p : ℝ≥0∞) : MemLp u p ν :=
      memLp_indicator_const p hK.isClosed.measurableSet.nullMeasurableSet 1
        (.inr (hK.measure_lt_top (μ := ν)).ne)
    let v : D := ⟨(hu 2).toLp u,
      (memLp_one_iff_integrable.mp (hu 1)).congr (hu 2).coeFn_toLp.symm⟩
    have hv : v ≠ 0 := by
      intro hv
      have hzero : u =ᵐ[ν] (0 : H → ℂ) := by
        refine (hu 2).coeFn_toLp.symm.trans ?_
        change (v.val : H → ℂ) =ᵐ[ν] _
        rw [hv]
        exact Lp.coeFn_zero ℂ 2 ν
      have hpos : 0 < ν K := (isOpen_interior.measure_pos ν
        ⟨1, mem_interior_iff_mem_nhds.mpr hK₁⟩).trans_le (measure_mono interior_subset)
      apply hpos.ne'
      have hOut : ∀ᵐ χ ∂ν, χ ∉ K :=
        hzero.mono fun χ hχ hχK ↦ by simp [u, hχK] at hχ
      simpa only [not_not, ofPred_mem_eq] using ae_iff.mp hOut
    let translate (χ : H) : D :=
      let hmp := measurePreserving_mul_left ν χ
      ⟨Lp.compMeasurePreserving (χ * ·) hmp v.val,
        (hmp.integrable_comp_of_integrable v.2).congr
          (Lp.coeFn_compMeasurePreserving v.val hmp).symm⟩
    have hMoment (ψ : PontryaginDual H) (χ : H) :
        ∫ x, (F ψ v x * star (F ψ v x)) * ((ψ * b x) χ : ℂ) ∂μ =
          inner ℂ v (translate χ) := by
      let hmp := measurePreserving_mul_left ν χ
      let t := translate χ
      have hTranslate (ζ : PontryaginDual H) :
          lcaFourier ν t ζ = (ζ χ : ℂ) * lcaFourier ν v ζ := by
        calc
          _ = lcaFourier ν (fun y ↦ v.val (χ * y)) ζ := by
            exact integral_congr_ae ((Lp.coeFn_compMeasurePreserving v.val hmp).mono fun y hy ↦
              congrArg (· * star (ζ y : ℂ)) hy)
          _ = ∫ y, (ζ χ : ℂ) * (v.val (χ * y) * star (ζ (χ * y) : ℂ)) ∂ν := by
            apply integral_congr_ae
            exact .of_forall fun y ↦ by
              change v.val (χ * y) * star (ζ y : ℂ) =
                (ζ χ : ℂ) * (v.val (χ * y) * star (ζ (χ * y) : ℂ))
              rw [map_mul, Circle.coe_mul, star_mul]
              have hUnit : (ζ χ : ℂ) * star (ζ χ : ℂ) = 1 := by
                simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
              calc
                _ = ((ζ χ : ℂ) * star (ζ χ : ℂ)) * (v.val (χ * y) * star (ζ y : ℂ)) := by
                  rw [hUnit, one_mul]
                _ = _ := by ring
          _ = _ := by
            rw [integral_const_mul]
            exact congrArg ((ζ χ : ℂ) * ·)
              (hmp.integral_comp (Homeomorph.mulLeft χ).toMeasurableEquiv.measurableEmbedding
                (fun y ↦ v.val y * star (ζ y : ℂ)))
      change _ = inner ℂ v t
      rw [← hInner ψ v t]
      exact integral_congr_ae (.of_forall fun x ↦ by
        change F ψ v x * star (F ψ v x) * _ = lcaFourier ν t (ψ * b x) * star (F ψ v x)
        rw [hTranslate]
        ring)
    -- Use separate copies of G for the evaluation image and its translate.
    let p (z : Bool × G) : PontryaginDual H := if z.1 then η * b z.2 else b z.2
    have hp : Continuous p := by
      apply Continuous.if _ (continuous_const.mul (b.continuous.comp continuous_snd))
        (b.continuous.comp continuous_snd)
      have hcl : IsClopen {z : Bool × G | z.1 = true} :=
        (isClopen_discrete {true}).preimage continuous_fst
      simp [hcl.frontier_eq]
    have hpinj : Function.Injective p := by
      have hdisj (x y : G) : b x ≠ η * b y := by
        intro h
        exact hη ⟨x / y, by rw [map_div, h, mul_div_cancel_right]⟩
      rintro ⟨i, x⟩ ⟨j, y⟩ h
      cases i <;> cases j
      · simpa [p, hEmb.injective.eq_iff] using h
      · exact (hdisj x y h).elim
      · exact (hdisj y x h.symm).elim
      · simpa [p, hEmb.injective.eq_iff] using h
    let cosetMeasure := (Measure.dirac false + Measure.dirac true).prod μ
    have hCosetMeasure : cosetMeasure = μ.map (Prod.mk false) + μ.map (Prod.mk true) := by
      dsimp only [cosetMeasure]
      rw [Measure.add_prod, Measure.dirac_prod, Measure.dirac_prod]
    let j (i : Bool) : MeasurableEmbedding (fun x : G ↦ (i, x)) :=
      MeasurableEmbedding.id.prodMk_left i
    let q (ψ : PontryaginDual H) (x : G) := F ψ v x * star (F ψ v x)
    have hq (ψ : PontryaginDual H) : Integrable (q ψ) μ := by
      refine (L2.integrable_inner (𝕜 := ℂ) (J ψ v) (J ψ v)).congr ?_
      filter_upwards [hJ ψ v] with x hx
      change inner ℂ (J ψ v x) (J ψ v x) = _
      rw [RCLike.inner_apply, starRingEnd_apply, hx]
    let g (z : Bool × G) : ℂ := if z.1 then -q η z.2 else q 1 z.2
    have hg₀ : Integrable g (μ.map (Prod.mk false)) := (j false).integrable_map_iff.mpr (hq 1)
    have hg₁ : Integrable g (μ.map (Prod.mk true)) := (j true).integrable_map_iff.mpr (hq η).neg
    have hg : Integrable g cosetMeasure := hCosetMeasure ▸ hg₀.add_measure hg₁
    let eval (z : Bool × G) := (p z).toMonoidHom
    have heval (χ : H) : Continuous (fun z ↦ eval z χ) :=
      ((continuous_eval_const (F := C(H, Circle)) χ).comp
        (ContinuousMonoidHom.isInducing_toContinuousMap H Circle).continuous).comp hp
    have hz := ae_eq_zero_of_integral_mul_circle_eq_zero eval heval
      (fun _ _ h ↦ hpinj (PontryaginDual.ext fun χ ↦
        congrArg (fun k : H →* Circle ↦ k χ) h)) hg (fun χ ↦ by
        let c (z : Bool × G) : ℂ := (eval z χ : ℂ)
        have hc (κ : Measure (Bool × G)) : AEStronglyMeasurable c κ :=
          (continuous_subtype_val.comp (heval χ)).aestronglyMeasurable
        have hnorm (z : Bool × G) : ‖c z‖ ≤ 1 := (Circle.norm_coe _).le
        rw [hCosetMeasure, integral_add_measure (hg₀.mul_bdd (hc _) (.of_forall hnorm))
          (hg₁.mul_bdd (hc _) (.of_forall hnorm)), (j false).integral_map, (j true).integral_map]
        change (∫ x, q 1 x * (b x χ : ℂ) ∂μ) + ∫ x, -q η x * ((η * b x) χ : ℂ) ∂μ = 0
        have hSame := (hMoment 1 χ).trans (hMoment η χ).symm
        simp only [one_mul] at hSame
        change (∫ x, q 1 x * (b x χ : ℂ) ∂μ) = ∫ x, q η x * ((η * b x) χ : ℂ) ∂μ at hSame
        simp only [neg_mul, integral_neg]
        rw [hSame, add_neg_cancel])
    have hz₀ : q 1 =ᵐ[μ] (0 : G → ℂ) := by
      have hzMap : ∀ᵐ z ∂μ.map (Prod.mk false), g z = 0 :=
        (ae_add_measure_iff.mp (hCosetMeasure ▸ hz)).1
      exact ((j false).ae_map_iff (p := fun z ↦ g z = 0)).mp hzMap
    apply hv
    apply inner_self_eq_zero (𝕜 := ℂ).mp
    rw [← hInner 1 v v, show (fun x ↦ F 1 v x * star (F 1 v x)) = q 1 from rfl,
      integral_congr_ae hz₀, Pi.zero_def, integral_zero]
  let equiv := MulEquiv.ofBijective b.toMonoidHom ⟨hEmb.injective, hSurj⟩
  have hOpen := hEmb.isInducing.isOpenMap (by rw [hSurj.range_eq]; exact isOpen_univ)
  exact ⟨equiv.toContinuousMulEquiv (fun _ ↦
    (hOpen.isQuotientMap b.continuous hSurj).isCoinducing.isOpen_preimage), fun _ _ ↦ rfl⟩

/-- Paper: Definition 9.1.2.1, p. 399. Evaluation into the bidual identifies the
group-side Sobolev space with H^s_w of the dual group. The pushed-forward Haar measure
on the bidual is the Plancherel measure of the dual group. -/
theorem modulatedSobolev_bidual (_hm : IsModulation m) (_hsurj : Function.Surjective m)
    (_hν : IsLCAPlancherelMeasure μ ν) (s : ℝ) :
    ∃ b : G ≃ₜ* PontryaginDual (PontryaginDual G),
      (∀ x χ, b x χ = χ x) ∧
      IsLCAPlancherelMeasure ν (μ.map b) ∧
      ∃ e : ModulatedSobolev m μ s ≃ₗᵢ[ℂ]
          WeightedSobolev (μ.map b) (modulatedSobolevWeight m ∘ b.symm) s,
        ∀ f, (e f : PontryaginDual (PontryaginDual G) → ℂ) =ᵐ[μ.map b] fun χ ↦ f (b.symm χ) := by
  let : BorelSpace (PontryaginDual G) := ⟨rfl⟩
  let : BorelSpace (PontryaginDual (PontryaginDual G)) := ⟨rfl⟩
  obtain ⟨b, hb⟩ := pontryaginDual_bidual_of_plancherel μ ν _hν
  let a := b.toHomeomorph.toMeasurableEquiv
  have ha : MeasurePreserving a μ (μ.map b) := ⟨a.measurable, rfl⟩
  have hEval : ∀ x : G, b x = pontryaginDual_eval x :=
    fun x ↦ PontryaginDual.ext (hb x)
  refine ⟨b, hb, ⟨b.isHaarMeasure_map μ, Measure.Regular.map b.toHomeomorph, ?_⟩, ?_⟩
  · intro u hu hu₂
    obtain ⟨hMem, hNorm⟩ := lcaFourier_eval_memLp μ ν _hν hu hu₂
    have hEq : lcaFourier ν u ∘ a = fun x ↦ lcaFourier ν u (pontryaginDual_eval x) :=
      funext fun x ↦ congrArg (lcaFourier ν u) (hEval x)
    have hMemComp : MemLp (lcaFourier ν u ∘ a) 2 μ := hEq.symm ▸ hMem
    have hMem' : MemLp (lcaFourier ν u) 2 (μ.map b) := by
      simpa only [Function.comp_def, MeasurableEquiv.apply_symm_apply] using
        hMemComp.comp_measurePreserving (ha.symm a)
    refine ⟨hMem', ?_⟩
    rw [← eLpNorm_comp_measurePreserving hMem'.aestronglyMeasurable ha, hEq]
    exact hNorm
  · let w := modulatedSobolevWeight m
    let ρ (x : G) : ℝ≥0∞ := ENNReal.ofReal ((1 + (w x : ℝ) ^ 2) ^ (s / 2))
    have hpos (x : G) : 0 < 1 + (w x : ℝ) ^ 2 := by positivity
    have hρ : Measurable ρ := (ENNReal.continuous_ofReal.comp
      (Continuous.rpow_const (continuous_const.add ((NNReal.continuous_coe.comp
        (modulatedSobolevWeight_subadditive m).1).pow 2)) fun x ↦ Or.inl (hpos x).ne')).measurable
    let μw := sobolevMeasure μ w s
    let νw := sobolevMeasure (μ.map b) (w ∘ b.symm) s
    have hw : MeasurePreserving a μw νw := by
      refine ⟨a.measurable, Measure.ext fun A hA ↦ ?_⟩
      change (Measure.map a (μ.withDensity ρ)) A =
        ((Measure.map a μ).withDensity (ρ ∘ a.symm)) A
      rw [a.measurableEmbedding.map_apply, withDensity_apply _ (a.measurable hA),
        withDensity_apply _ hA, ← lintegral_indicator (a.measurable hA), ← lintegral_indicator hA,
        a.measurableEmbedding.lintegral_map]
      exact lintegral_congr fun x ↦ by
        simp only [indicator, Function.comp_apply, a.symm_apply_apply]
        rfl
    let I : Lp ℂ 2 μw →ₗᵢ[ℂ] Lp ℂ 2 νw := Lp.compMeasurePreservingₗᵢ ℂ a.symm (hw.symm a)
    have hI : Function.Surjective I := by
      intro f
      refine ⟨Lp.compMeasurePreserving a hw f, ?_⟩
      change Lp.compMeasurePreserving a.symm (hw.symm a) (Lp.compMeasurePreserving a hw f) = f
      rw [← Lp.compMeasurePreserving_comp_apply f hw (hw.symm a)]
      simp
    let e := LinearIsometryEquiv.ofSurjective I hI
    refine ⟨e, fun f ↦ ?_⟩
    have hAC : μ.map b ≪ νw :=
      withDensity_absolutelyContinuous' (hρ.comp a.symm.measurable).aemeasurable
        (.of_forall fun χ ↦ (ENNReal.ofReal_pos.mpr
          (Real.rpow_pos_of_pos (hpos (a.symm χ)) _)).ne')
    exact hAC.ae_eq (Lp.coeFn_compMeasurePreserving f (hw.symm a))

-- TODO(paper-gap): (9.1.2.9) compares a squared norm on the left with homogeneous
-- expressions of degree one on the right. In (9.1.2.11) the sign of the exponent
-- for the character and the sign for its conjugate are printed the same way.

/-- Paper: Lemma 9.1.2.2, p. 400. At degree 2N the norms of the Fourier derivatives
up to order N for any algebra generator induce the Sobolev topology.
Deviation: The displayed C_F is read as G, as in the lemma's hypotheses. On completion
the derivatives are continuous L²-valued extensions from smooth compactly supported functions. -/
theorem modulatedSobolev_fourierDeriv_topology (_hm : IsModulation m)
    (_hsurj : Function.Surjective m) (_hν : IsLCAPlancherelMeasure μ ν) (N : ℕ)
    (D : bruhatDiffAlgebra (PontryaginDual G)) (_hD : Algebra.adjoin ℂ {D} = ⊤) :
    let E := ModulatedSobolev m μ (2 * (N : ℝ))
    ∃ A : Fin (N + 1) → (E →L[ℂ] Lp ℂ 2 ν),
      (∀ (f : G →C_c ℂ), IsBruhatSmooth (f : G → ℂ) →
        ∃ (u : E) (F : bruhatSmoothSubmodule (G := PontryaginDual G)),
          (u : G → ℂ) =ᵐ[μ] (f : G → ℂ) ∧ F.val = lcaFourier μ f ∧
          ∀ k, (A k u : PontryaginDual G → ℂ) =ᵐ[ν] ((D ^ (k : ℕ)).val F).val) ∧
      IsEmbedding (fun f : E ↦ fun k ↦ A k f) := by sorry

-- TODO(paper-gap): In Remark 9.1.2.3 the ordinary derivatives are on the Fourier side.
-- The stated generalization to all locally compact abelian groups also needs a weight.

/-- The Japanese bracket `(1 + |x|²)^(-s/2)` is Lebesgue integrable on the real line
exactly when `s > 1`. -/
private theorem integrable_one_add_sq_rpow_iff {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x : ℝ ↦ (1 + |x| ^ 2) ^ (-s / 2)) ↔ 1 < s := by
  constructor
  · intro h
    have hI : IntegrableOn (fun x : ℝ ↦ x ^ (-s)) (Ioi 1) := by
      refine (h.integrableOn.const_mul ((2 : ℝ) ^ (s / 2))).mono' ?_ ?_
      · exact (continuousOn_id.rpow_const fun x hx ↦
          Or.inl (zero_lt_one.trans hx).ne').aestronglyMeasurable measurableSet_Ioi
      · refine (ae_restrict_mem measurableSet_Ioi).mono fun x (hx : 1 < x) ↦ ?_
        have hx0 : 0 < x := zero_lt_one.trans hx
        rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx0 _)]
        have hle : 1 + |x| ^ 2 ≤ 2 * x ^ 2 := by
          rw [abs_of_pos hx0]; nlinarith
        have h1 : (2 * x ^ 2) ^ (-s / 2) ≤ (1 + |x| ^ 2) ^ (-s / 2) :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle (by linarith)
        have h2 : (2 * x ^ 2) ^ (-s / 2) = (2 : ℝ) ^ (-s / 2) * x ^ (-s) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hx0.le]
          congr 2; ring
        have h3 : (2 : ℝ) ^ (s / 2) * (2 : ℝ) ^ (-s / 2) = 1 := by
          rw [← Real.rpow_add (by norm_num)]; ring_nf; exact Real.rpow_zero 2
        calc x ^ (-s) = (2 : ℝ) ^ (s / 2) * ((2 : ℝ) ^ (-s / 2) * x ^ (-s)) := by
              rw [← mul_assoc, h3, one_mul]
          _ ≤ (2 : ℝ) ^ (s / 2) * (1 + |x| ^ 2) ^ (-s / 2) := by
              rw [← h2]; gcongr
    have := (integrableOn_Ioi_rpow_iff zero_lt_one).mp hI
    linarith
  · intro h
    have := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
      (r := s) (by simpa using h)
    simpa [Real.norm_eq_abs] using this

/-- In logarithmic coordinates, `(1 + |log t|²)^(-s/2)` is integrable for `dt/t` on the
positive reals exactly when `s > 1`. -/
private theorem integrable_positiveRealHaar_logBracket_iff {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun t : ℝ≥0ˣ ↦ (1 + |Real.log ((t.val : ℝ≥0) : ℝ)| ^ 2) ^ (-s / 2))
      positiveRealHaar ↔ 1 < s := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have hne (t : ℝ≥0ˣ) : ((t.val : ℝ≥0) : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr t.ne_zero
  have hFc : Continuous fun t : ℝ≥0ˣ ↦ (1 + |Real.log ((t.val : ℝ≥0) : ℝ)| ^ 2) ^ (-s / 2) :=
    ((((NNReal.continuous_coe.comp Units.continuous_val).log hne).abs.pow 2).const_add
      1).rpow_const fun t ↦ Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'
  have hE : Continuous fun x : ℝ ↦ Units.mk0 (Real.exp x).toNNReal
      (Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x))) := by
    rw [Units.continuous_iff]
    refine ⟨continuous_real_toNNReal.comp Real.continuous_exp, ?_⟩
    simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
    exact (continuous_real_toNNReal.comp Real.continuous_exp).inv₀ fun x ↦
      Real.toNNReal_eq_zero.not.mpr (not_le_of_gt (Real.exp_pos x))
  unfold positiveRealHaar
  rw [integrable_map_measure hFc.aestronglyMeasurable hE.aemeasurable]
  convert integrable_one_add_sq_rpow_iff hs using 3 with x
  simp [Real.coe_toNNReal _ (Real.exp_pos x).le]

/-- Paper: Lemma 9.1.2.4, p. 402. The reciprocal logarithmic Sobolev
density is integrable exactly above degree one. -/
theorem modulatedSobolev_reciprocal_integrable_iff (_hm : IsModulation m)
    (_hsurj : Function.Surjective m) {s : ℝ} (_hs : 0 ≤ s) :
    Integrable (fun x ↦ (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (-s / 2)) μ ↔ 1 < s := by
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : positiveRealHaar.IsHaarMeasure := positiveRealHaar_isHaarMeasure
  set f : G → ℝ := fun x ↦ (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (-s / 2)
  set F : ℝ≥0ˣ → ℝ := fun t ↦ (1 + |Real.log ((t.val : ℝ≥0) : ℝ)| ^ 2) ^ (-s / 2)
  have hne (t : ℝ≥0ˣ) : ((t.val : ℝ≥0) : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr t.ne_zero
  have hFc : Continuous F :=
    ((((NNReal.continuous_coe.comp Units.continuous_val).log hne).abs.pow 2).const_add
      1).rpow_const fun t ↦ Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne'
  have hfc : Continuous f := hFc.comp m.continuous
  obtain ⟨τ', hτ'⟩ := _hm.exists_section
  let r : ℝ≥0ˣ →ₜ* m.toMonoidHom.range :=
    ⟨(MonoidHom.id ℝ≥0ˣ).codRestrict _ fun t ↦ _hsurj t, continuous_id.subtype_mk _⟩
  let τ : ℝ≥0ˣ →ₜ* G := τ'.comp r
  have hτ : Function.RightInverse τ m := fun t ↦ hτ' (r t)
  have : CompactSpace m.toMonoidHom.ker := isCompact_iff_compactSpace.mp _hm.isCompact_ker
  let μ₁ : Measure m.toMonoidHom.ker := Measure.haarMeasure ⊤
  have hμ₁ : μ₁ univ = 1 := Measure.haarMeasure_self
  have hcan := canonicalModulatedHaar_eq_map_prod m _hm τ hτ μ₁ hμ₁
  have hνH : (canonicalModulatedHaar m _hm).IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m _hm).exists).1
  have h1 : Integrable f μ ↔ Integrable f (canonicalModulatedHaar m _hm) := by
    constructor
    · intro h; rw [Measure.isMulLeftInvariant_eq_smul (canonicalModulatedHaar m _hm) μ]
      exact h.smul_measure_nnreal
    · intro h; rw [Measure.isMulLeftInvariant_eq_smul μ (canonicalModulatedHaar m _hm)]
      exact h.smul_measure_nnreal
  have hφ : Continuous fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : G) * τ z.2 := by fun_prop
  have h2 : Integrable f (canonicalModulatedHaar m _hm) ↔
      Integrable (F ∘ Prod.snd) (μ₁.prod positiveRealHaar) := by
    rw [hcan, integrable_map_measure hfc.aestronglyMeasurable hφ.aemeasurable]
    congr! 1
    funext z
    have hk : m (z.1 : G) = 1 := z.1.property
    simp only [Function.comp_apply, f, F, map_mul, hk, one_mul, hτ z.2]
  have h3 : Integrable (F ∘ Prod.snd) (μ₁.prod positiveRealHaar) ↔
      Integrable F positiveRealHaar := by
    rw [← integrable_map_measure hFc.aestronglyMeasurable measurable_snd.aemeasurable,
      Measure.map_snd_prod, hμ₁, one_smul]
  rw [h1, h2, h3]
  exact integrable_positiveRealHaar_logBracket_iff _hs

/-- Paper: Proposition 9.1.2.5, p. 402. The unweighted product pairing on the group
identifies the strong dual isometrically with the space of opposite degree. -/
theorem modulatedSobolev_dual (_hm : IsModulation m) (_hsurj : Function.Surjective m)
    {s : ℝ} (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (ModulatedSobolev m μ s) ≃ₗᵢ[ℂ] ModulatedSobolev m μ (-s),
      ∀ Λ f, Integrable (fun x ↦ f x * T Λ x) μ ∧ Λ f = ∫ x, f x * T Λ x ∂μ :=
  weightedSobolev_dual_of_continuous μ (modulatedSobolevWeight_subadditive m).1 s

-- TODO(paper-gap): The simultaneous invariance described in the proof uses opposite
-- parameters for left and right translations under the transpose convention.

/-- Paper: Proposition 9.1.2.5, p. 402. The dual isometry intertwines the transpose
of left translation with right translation. Both translations are jointly continuous.
The transpose is precomposition as in (4.3.3.3). -/
theorem modulatedSobolev_dual_equivariant (hm : IsModulation m)
    (hsurj : Function.Surjective m) {s : ℝ} (hs : 0 ≤ s) :
    let E := ModulatedSobolev m μ s
    let F := ModulatedSobolev m μ (-s)
    let T := Classical.choose (modulatedSobolev_dual m μ hm hsurj hs).exists
    ∃ (L : G →* (E →L[ℂ] E)) (R : G →* (F →L[ℂ] F)),
      Continuous (fun p : G × E ↦ L p.1 p.2) ∧
      Continuous (fun p : G × F ↦ R p.1 p.2) ∧
      (∀ g f, (L g f : G → ℂ) =ᵐ[μ] fun x ↦ f (g⁻¹ * x)) ∧
      (∀ g u, (R g u : G → ℂ) =ᵐ[μ] fun x ↦ u (x * g)) ∧
      ∀ g Λ, T (Λ.comp (L g)) = R g (T Λ) := by sorry

-- TODO(paper-gap): In (9.1.2.15) the range of m is unspecified. For nonintegral
-- orders the signed logarithm can be negative and no convention for its power is given.

/-- Paper: Proposition 9.1.2.5, p. 402. A unitary module character times a natural
power of the logarithm lies in degree −s exactly when the power is less than (s−1)/2.
Deviation: The exponent in (9.1.2.15) is interpreted as a natural number, as for the
logarithmic derivatives in (9.2.1.16). -/
theorem modulatedSobolev_logPower_mem_iff (_hm : IsModulation m) (_hsurj : Function.Surjective m)
    {s : ℝ} (_hs : 1 < s) (t : ℝ) (k : ℕ) :
    MemLp (fun x ↦
      Complex.exp (Complex.I * (t : ℂ) * (Real.log ((m x).val : ℝ) : ℂ)) *
        (Real.log ((m x).val : ℝ) : ℂ) ^ k) 2
      (sobolevMeasure μ (modulatedSobolevWeight m) (-s)) ↔ (k : ℝ) < (s - 1) / 2 := by sorry

/-- Paper: Proposition 9.1.2.6, p. 403. Above degree one, each modulated Sobolev class
is absolutely integrable and the canonical inclusion into Haar L¹ is bounded. -/
theorem modulatedSobolev_toL1 (_hm : IsModulation m) (_hsurj : Function.Surjective m)
    {s : ℝ} (_hs : 1 < s) :
    ∃ (J : ModulatedSobolev m μ s →L[ℂ] Lp ℂ 1 μ) (C : ℝ),
      Function.Injective J ∧ 0 < C ∧ ‖J‖ ≤ C ∧
      ∀ f : ModulatedSobolev m μ s,
        Integrable (f : G → ℂ) μ ∧ (J f : G → ℂ) =ᵐ[μ] (f : G → ℂ) := by
  -- `P x = 1 + |log |x||²`; the Sobolev measure has density `P^(s/2)`.
  have hne (x : G) : (((m x).val : ℝ≥0) : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hL : Continuous fun x ↦ Real.log ((m x).val : ℝ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log hne
  have hPpos (x : G) : 0 < 1 + |Real.log ((m x).val : ℝ)| ^ 2 :=
    add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)
  have hP : Continuous fun x ↦ 1 + |Real.log ((m x).val : ℝ)| ^ 2 :=
    continuous_const.add (hL.abs.pow 2)
  have hρ : Continuous fun x ↦ (1 + (modulatedSobolevWeight m x : ℝ) ^ 2) ^ (s / 2) :=
    hP.rpow_const fun x ↦ Or.inl (hPpos x).ne'
  have hac₁ : sobolevMeasure μ (modulatedSobolevWeight m) s ≪ μ :=
    withDensity_absolutelyContinuous _ _
  have hac₂ : μ ≪ sobolevMeasure μ (modulatedSobolevWeight m) s :=
    withDensity_absolutelyContinuous' (ENNReal.continuous_ofReal.comp hρ).aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (hPpos x) _)).ne')
  set I := ∫ x, (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (-s / 2) ∂μ
  have hI : Integrable (fun x ↦ (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (-s / 2)) μ :=
    (modulatedSobolev_reciprocal_integrable_iff m μ _hm _hsurj (by linarith)).mpr _hs
  -- Cauchy–Schwarz against the weight, as in the paper.
  have key (f : ModulatedSobolev m μ s) :
      Integrable (f : G → ℂ) μ ∧
        ∫ x, ‖(f : G → ℂ) x‖ ∂μ ≤ Real.sqrt I * ‖f‖ := by
    obtain ⟨hfi, hfn⟩ := modulatedSobolev_norm m μ s f
    have hfm : AEStronglyMeasurable (f : G → ℂ) μ := (Lp.aestronglyMeasurable f).mono_ac hac₂
    set a : G → ℝ := fun x ↦
      ‖(f : G → ℂ) x‖ * (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (s / 4)
    set b : G → ℝ := fun x ↦ (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (-s / 4)
    have hab (x : G) : a x * b x = ‖(f : G → ℂ) x‖ := by
      simp only [a, b]
      rw [mul_assoc, ← Real.rpow_add (hPpos x), show s / 4 + -s / 4 = 0 by ring,
        Real.rpow_zero, mul_one]
    have ha2 (x : G) : a x ^ 2 =
        ‖(f : G → ℂ) x‖ ^ 2 * (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (s / 2) := by
      simp only [a]
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (hPpos x).le]
      norm_num; ring_nf
    have hb2 (x : G) : b x ^ 2 = (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (-s / 2) := by
      simp only [b]
      rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul (hPpos x).le]
      norm_num; ring_nf
    have hbc : Continuous b := hP.rpow_const fun x ↦ Or.inl (hPpos x).ne'
    have ham : MemLp a 2 μ :=
      (memLp_two_iff_integrable_sq (hfm.norm.mul
        (hP.rpow_const fun x ↦ Or.inl (hPpos x).ne').aestronglyMeasurable)).mpr
        (hfi.congr (ae_of_all _ fun x ↦ (ha2 x).symm))
    have hbm : MemLp b 2 μ :=
      (memLp_two_iff_integrable_sq hbc.aestronglyMeasurable).mpr
        (hI.congr (ae_of_all _ fun x ↦ (hb2 x).symm))
    have hint : Integrable (fun x ↦ ‖(f : G → ℂ) x‖) μ :=
      (ham.integrable_mul hbm).congr (ae_of_all _ hab)
    refine ⟨(integrable_norm_iff hfm).mp hint, ?_⟩
    have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all _ fun x ↦ mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hPpos x).le _))
      (ae_of_all _ fun x ↦ Real.rpow_nonneg (hPpos x).le _)
      (by rw [ENNReal.ofReal_ofNat]; exact ham) (by rw [ENNReal.ofReal_ofNat]; exact hbm)
    have e1 : ∫ x, a x * b x ∂μ = ∫ x, ‖(f : G → ℂ) x‖ ∂μ :=
      integral_congr_ae (ae_of_all _ hab)
    have e2 : ∫ x, a x ^ (2 : ℝ) ∂μ =
        ∫ x, ‖(f : G → ℂ) x‖ ^ 2 *
          (1 + |Real.log ((m x).val : ℝ)| ^ 2) ^ (s / 2) ∂μ :=
      integral_congr_ae (ae_of_all _ fun x ↦ by beta_reduce; rw [Real.rpow_two, ha2])
    have e3 : ∫ x, b x ^ (2 : ℝ) ∂μ = I :=
      integral_congr_ae (ae_of_all _ fun x ↦ by beta_reduce; rw [Real.rpow_two, hb2])
    calc ∫ x, ‖(f : G → ℂ) x‖ ∂μ = ∫ x, a x * b x ∂μ := e1.symm
      _ ≤ (∫ x, a x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
            (∫ x, b x ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) := hH
      _ = Real.sqrt I * ‖f‖ := by
        rw [e2, e3, hfn, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, mul_comm]
  -- The inclusion as a linear map into L¹.
  let J₀ : ModulatedSobolev m μ s →ₗ[ℂ] Lp ℂ 1 μ :=
    { toFun := fun f ↦ (key f).1.toL1 _
      map_add' := fun f g ↦ by
        apply Lp.ext
        filter_upwards [(key (f + g)).1.coeFn_toL1, (key f).1.coeFn_toL1,
          (key g).1.coeFn_toL1, Lp.coeFn_add ((key f).1.toL1 _) ((key g).1.toL1 _),
          hac₂.ae_le (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
        rw [h1, h4, Pi.add_apply, h2, h3, h5, Pi.add_apply]
      map_smul' := fun c f ↦ by
        apply Lp.ext
        filter_upwards [(key (c • f)).1.coeFn_toL1, (key f).1.coeFn_toL1,
          Lp.coeFn_smul c ((key f).1.toL1 _), hac₂.ae_le (Lp.coeFn_smul c f)]
          with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h3, Pi.smul_apply, h2, h4, Pi.smul_apply] }
  have hJ₀ (f : ModulatedSobolev m μ s) : ‖J₀ f‖ ≤ Real.sqrt I * ‖f‖ := by
    change ‖(key f).1.toL1 _‖ ≤ _
    rw [L1.norm_of_fun_eq_integral_norm]
    exact (key f).2
  let J := J₀.mkContinuous (Real.sqrt I) hJ₀
  refine ⟨J, Real.sqrt I + 1, ?_, by positivity,
    (J₀.mkContinuous_norm_le (Real.sqrt_nonneg _) hJ₀).trans (by linarith),
    fun f ↦ ⟨(key f).1, (key f).1.coeFn_toL1⟩⟩
  rw [injective_iff_map_eq_zero]
  intro f hf
  have h0 : ((key f).1.toL1 (f : G → ℂ) : G → ℂ) =ᵐ[μ] 0 := by
    have : (key f).1.toL1 (f : G → ℂ) = 0 := hf
    rw [this]
    exact Lp.coeFn_zero _ _ _
  have h1 : (f : G → ℂ) =ᵐ[sobolevMeasure μ (modulatedSobolevWeight m) s] 0 :=
    hac₁.ae_le ((key f).1.coeFn_toL1.symm.trans h0)
  exact Lp.ext (h1.trans (Lp.coeFn_zero _ _ _).symm)

end Modulated

end RiemannMasullo
