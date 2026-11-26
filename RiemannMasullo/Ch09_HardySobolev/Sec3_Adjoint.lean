module

public import RiemannMasullo.Ch09_HardySobolev.Sec3
import RiemannMasullo.AppD_SchwartzBruhat.Sec1a
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! # Integral kernels of weighted convolutions and their adjoints

For the Sobolev measure of §9.2, the forward kernel divides by the input density and the adjoint
kernel divides by the output density. Equality on continuous compactly supported inputs identifies
a finite two-sided masked kernel with the actual difference operator on the Hilbert space.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal InnerProductSpace Pointwise ComplexConjugate

namespace RiemannMasullo.WeightedConvolution

section IntegralKernels

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure]

/-- The input-first form of the Haar convolution integral. -/
private theorem convolution_eq_kernel (k v : G → ℂ) (x : G) :
    lcaConvolution μ k v x = ∫ y, k (x * y⁻¹) * v y ∂μ := by
  let H (g : G) := k g * v (g⁻¹ * x)
  rw [lcaConvolution, ← integral_div_left_eq_self H μ x]
  apply integral_congr_ae
  exact .of_forall fun y ↦ by simp [H, div_eq_mul_inv]

private theorem convolution_compact {k v : G → ℂ}
    (hk : HasCompactSupport k) (hv : HasCompactSupport v) :
    HasCompactSupport (lcaConvolution μ k v) := by
  apply HasCompactSupport.intro (hk.isCompact.mul hv.isCompact)
  intro x hx
  apply integral_eq_zero_of_ae
  refine .of_forall fun y ↦ by_contra fun h ↦ hx ?_
  exact ⟨y, subset_tsupport _ (left_ne_zero_of_mul h), y⁻¹ * x,
    subset_tsupport _ (right_ne_zero_of_mul h), mul_inv_cancel_left _ _⟩

/-- The norm closure of the continuous compactly supported representatives is all of weighted L². -/
private theorem dense_compactCore (ν : Measure G) [IsLocallyFiniteMeasure ν] :
    Dense {u : Lp ℂ 2 ν | ∃ f : G → ℂ,
      Continuous f ∧ HasCompactSupport f ∧ (u : G → ℂ) =ᵐ[ν] f} := by
  intro u
  apply EMetric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hδε⟩ := exists_between hε
  obtain ⟨f, hc, he, hf, hm⟩ := (Lp.memLp u).exists_hasCompactSupport_eLpNorm_sub_le (by simp) hδ.ne'
  refine ⟨hm.toLp f, ⟨f, hf, hc, hm.coeFn_toLp⟩, ?_⟩
  rw [Lp.edist_def, eLpNorm_congr_ae (EventuallyEq.rfl.sub hm.coeFn_toLp)]
  exact he.trans_lt hδε

private theorem integral_convolution_pair {k f v : G → ℂ}
    (hk : Continuous k) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    (∫ y, star (lcaConvolution μ k v y) * f y ∂μ) =
      ∫ x, star (v x) * (∫ y, star (k (y * x⁻¹)) * f y ∂μ) ∂μ := by
  let J (y x : G) := star (k (y * x⁻¹) * v x) * f y
  have hJ : Integrable (uncurry J) (μ.prod μ) := by
    have hcont : Continuous (uncurry J) :=
      (((hk.comp (continuous_fst.mul continuous_snd.inv)).mul (hv.comp continuous_snd)).star).mul
        (hf.comp continuous_fst)
    apply hcont.integrable_of_hasCompactSupport
    apply HasCompactSupport.of_support_subset_isCompact (hfc.prod hvc)
    intro p hp
    refine ⟨subset_tsupport _ (right_ne_zero_of_mul hp), subset_tsupport _ ?_⟩
    intro h
    exact hp (by simp [uncurry, J, h])
  calc
    _ = ∫ y, ∫ x, J y x ∂μ ∂μ := by
      apply integral_congr_ae
      refine .of_forall fun y ↦ ?_
      dsimp only
      rw [convolution_eq_kernel]
      change conj (∫ x, k (y * x⁻¹) * v x ∂μ) * f y = _
      rw [← integral_conj, ← integral_mul_const]
      rfl
    _ = ∫ x, ∫ y, J y x ∂μ ∂μ := integral_integral_swap hJ
    _ = _ := by
      apply integral_congr_ae
      refine .of_forall fun x ↦ ?_
      dsimp only
      rw [← integral_const_mul]
      exact integral_congr_ae (.of_forall fun y ↦ by simp [J, mul_left_comm, mul_assoc])

private theorem weighted_inner (ν : Measure G) (w : G → ℝ) (hw : Continuous w)
    (hp : ∀ x, 0 < w x) (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))
    (v u : Lp ℂ 2 ν) {V U : G → ℂ} (hv : (v : G → ℂ) =ᵐ[ν] V)
    (hu : (u : G → ℂ) =ᵐ[ν] U) :
    ⟪v,u⟫_ℂ = ∫ x, star (V x) * ((w x : ℂ) * U x) ∂μ := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, star (V x) * U x ∂ν := by
      apply integral_congr_ae
      filter_upwards [hv, hu] with x h₁ h₂
      rw [h₁, h₂]
      exact mul_comm _ _
    _ = _ := by
      rw [hν, show (fun x ↦ ENNReal.ofReal (w x)) =
        (fun x ↦ ((w x).toNNReal : ℝ≥0∞)) from rfl,
        integral_withDensity_eq_integral_smul hw.measurable.real_toNNReal]
      exact integral_congr_ae (.of_forall fun x ↦ by
        dsimp only
        rw [NNReal.smul_def, Real.coe_toNNReal _ (hp x).le, Complex.real_smul]
        ring)

/-- On the dense compact core the Haar kernel of the adjoint is the reflected
conjugate kernel times the input density divided by the output density. -/
private theorem adjoint_apply_compact (ν : Measure G) (w : G → ℝ) (hw : Continuous w)
    (hp : ∀ x, 0 < w x) (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))
    (k : G → ℂ) (hk : Continuous k) (hkc : HasCompactSupport k)
    (A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hA : ∀ v, (A v : G → ℂ) =ᵐ[μ] lcaConvolution μ k v)
    (u : Lp ℂ 2 ν) (f : G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hu : (u : G → ℂ) =ᵐ[ν] f) :
    (A.adjoint u : G → ℂ) =ᵐ[ν] fun x ↦
      (∫ y, star (k (y * x⁻¹)) * ((w y : ℂ) * f y) ∂μ) / (w x : ℂ) := by
  let q (z : G) := star (k z⁻¹)
  let b (y : G) := (w y : ℂ) * f y
  let H := lcaConvolution μ q b
  let g (x : G) := H x / (w x : ℂ)
  have hνμ : ν ≪ μ := hν ▸ withDensity_absolutelyContinuous μ _
  have hμν : μ ≪ ν := hν ▸ withDensity_absolutelyContinuous' hw.measurable.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
  let : IsLocallyFiniteMeasure ν := hν ▸ IsLocallyFiniteMeasure.withDensity_ofReal hw
  have hq : Continuous q := (hk.comp continuous_inv).star
  have hqc : HasCompactSupport q := (hkc.comp_homeomorph (Homeomorph.inv G)).comp_left (star_zero ℂ)
  have hb : Continuous b := (Complex.continuous_ofReal.comp hw).mul hf
  have hbc : HasCompactSupport b := hfc.mul_left
  have hH : Continuous H := continuous_lcaConvolution_L2 μ (hq.memLp_of_hasCompactSupport hqc)
    (hb.memLp_of_hasCompactSupport hbc)
  have hHc : HasCompactSupport H := convolution_compact μ hqc hbc
  have hg : Continuous g := hH.div (Complex.continuous_ofReal.comp hw) fun x ↦
    Complex.ofReal_ne_zero.mpr (hp x).ne'
  have hgc : HasCompactSupport g := by
    apply HasCompactSupport.intro hHc.isCompact
    intro x hx
    simp [g, image_eq_zero_of_notMem_tsupport hx]
  have hgLp : MemLp g 2 ν := hg.memLp_of_hasCompactSupport hgc
  have hHval (x : G) : H x = ∫ y, star (k (y * x⁻¹)) * b y ∂μ := by
    change lcaConvolution μ q b x = _
    rw [convolution_eq_kernel]
    apply integral_congr_ae
    exact .of_forall fun y ↦ by simp [q]
  have hEq : A.adjoint u = hgLp.toLp g := by
    apply (dense_compactCore (G := G) ν).eq_of_inner_right ℂ
    rintro v ⟨V, hV, hVc, hv⟩
    rw [ContinuousLinearMap.adjoint_inner_right]
    have hAV : (A v : G → ℂ) =ᵐ[ν] lcaConvolution μ k V := by
      refine hνμ.ae_eq ((hA v).trans (.of_forall fun x ↦ ?_))
      rw [convolution_eq_kernel, convolution_eq_kernel]
      exact integral_congr_ae ((hμν.ae_eq hv).mono fun y hy ↦ congrArg (k (x * y⁻¹) * ·) hy)
    rw [weighted_inner μ ν w hw hp hν (A v) u hAV hu,
      weighted_inner μ ν w hw hp hν v (hgLp.toLp g) hv hgLp.coeFn_toLp]
    change (∫ y, star (lcaConvolution μ k V y) * b y ∂μ) = _
    rw [integral_convolution_pair μ hk hb hbc hV hVc]
    apply integral_congr_ae
    refine .of_forall fun x ↦ congrArg (star (V x) * ·) ?_
    rw [← hHval, show (w x : ℂ) * g x = H x by
      dsimp [g]
      field_simp [Complex.ofReal_ne_zero.mpr (hp x).ne']]
  rw [hEq]
  refine hgLp.coeFn_toLp.trans (.of_forall fun x ↦ ?_)
  rw [show g x = H x / _ from rfl, hHval]


private theorem integral_density (ν : Measure G) (w : G → ℝ) (hw : Measurable w)
    (hp : ∀ x, 0 ≤ w x) (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))
    (f : G → ℂ) : (∫ x, f x ∂ν) = ∫ x, (w x : ℂ) * f x ∂μ := by
  rw [hν, show (fun x ↦ ENNReal.ofReal (w x)) =
    (fun x ↦ ((w x).toNNReal : ℝ≥0∞)) from rfl,
    integral_withDensity_eq_integral_smul hw.real_toNNReal]
  apply integral_congr_ae
  refine .of_forall fun x ↦ ?_
  dsimp only
  rw [NNReal.smul_def, Real.coe_toNNReal _ (hp x), Complex.real_smul]

/-- With respect to weighted measure the forward kernel uses only the input density. -/
private theorem apply_weighted (ν : Measure G) (w : G → ℝ) (hw : Measurable w)
    (hp : ∀ x, 0 < w x) (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))
    (k : G → ℂ) (A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hA : ∀ v, (A v : G → ℂ) =ᵐ[μ] lcaConvolution μ k v)
    (u : Lp ℂ 2 ν) (f : G → ℂ) (hu : (u : G → ℂ) =ᵐ[ν] f) :
    (A u : G → ℂ) =ᵐ[ν] fun x ↦ ∫ y, k (x * y⁻¹) / (w y : ℂ) * f y ∂ν := by
  have hνμ : ν ≪ μ := hν ▸ withDensity_absolutelyContinuous μ _
  have hμν : μ ≪ ν := hν ▸ withDensity_absolutelyContinuous' hw.ennreal_ofReal.aemeasurable
    (.of_forall fun x ↦ (ENNReal.ofReal_pos.mpr (hp x)).ne')
  apply (hνμ.ae_eq (hA u)).trans
  refine .of_forall fun x ↦ ?_
  dsimp only
  rw [convolution_eq_kernel, integral_density μ ν w hw (fun x ↦ (hp x).le) hν]
  apply integral_congr_ae
  filter_upwards [hμν.ae_eq hu] with y hy
  rw [hy]
  field_simp [Complex.ofReal_ne_zero.mpr (hp y).ne']

/-- The adjoint kernel against weighted measure uses only the output density. -/
private theorem adjoint_apply_compact_weighted (ν : Measure G) (w : G → ℝ) (hw : Continuous w)
    (hp : ∀ x, 0 < w x) (hν : ν = μ.withDensity (fun x ↦ ENNReal.ofReal (w x)))
    (k : G → ℂ) (hk : Continuous k) (hkc : HasCompactSupport k)
    (A : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (hA : ∀ v, (A v : G → ℂ) =ᵐ[μ] lcaConvolution μ k v)
    (u : Lp ℂ 2 ν) (f : G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hu : (u : G → ℂ) =ᵐ[ν] f) :
    (A.adjoint u : G → ℂ) =ᵐ[ν] fun x ↦
      ∫ y, star (k (y * x⁻¹)) / (w x : ℂ) * f y ∂ν := by
  apply (adjoint_apply_compact μ ν w hw hp hν k hk hkc A hA u f hf hfc hu).trans
  refine .of_forall fun x ↦ ?_
  dsimp only
  rw [integral_density μ ν w hw.measurable (fun x ↦ (hp x).le) hν,
    div_eq_mul_inv, ← integral_mul_const]
  exact integral_congr_ae (.of_forall fun y ↦ by dsimp only; ring)

variable (m : G →ₜ* ℝ≥0ˣ)

set_option quotPrecheck false in
local notation "L" => (fun x ↦ Real.log ((m x).val : ℝ))
local notation "ν" => (fun a b s ↦ intervalSobolevMeasure μ L a b s)
local notation "w" => (fun a b s x ↦ intervalSobolevDensity a b s (L x))

private theorem continuous_logNorm : Continuous L :=
  (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
    fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero

private theorem continuous_intervalDensity (a b s : ℝ) : Continuous (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
  positivity

private theorem intervalDensity_positive (a b s x : ℝ) : 0 < intervalSobolevDensity a b s x :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

/-- On continuous compactly supported inputs, the actual compact-interval test operator and
its Hilbert adjoint have their output-first kernels against the actual Sobolev measure. -/
theorem hardySobolevTestAction_compact_kernels (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (u : CompactIntervalSobolev μ L a b s)
    (f : G → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hu : (u : G → ℂ) =ᵐ[ν a b s] f) :
    let A : CompactIntervalSobolev μ L a b s →L[ℂ] CompactIntervalSobolev μ L a b s :=
      hardySobolevTestAction μ m a b s hab hs φ
    ((A u : G → ℂ) =ᵐ[ν a b s] fun x ↦ ∫ y, φ.val (x * y⁻¹) /
      (intervalSobolevDensity a b s (L y) : ℂ) * f y ∂(ν a b s)) ∧
    ((A.adjoint u : G → ℂ) =ᵐ[ν a b s] fun x ↦ ∫ y, star (φ.val (y * x⁻¹)) /
      (intervalSobolevDensity a b s (L x) : ℂ) * f y ∂(ν a b s)) := by
  intro A
  have hL := continuous_logNorm m
  have hD := continuous_intervalDensity a b s
  have hp (x : G) := intervalDensity_positive a b s (L x)
  have hφ : Continuous φ.val := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp φ.property.1)
  have hA := hardySobolevTestAction_apply μ m a b s hab hs φ
  exact ⟨apply_weighted μ (ν a b s) (w a b s) (hD.comp hL).measurable hp rfl φ.val A hA u f hu,
    adjoint_apply_compact_weighted μ (ν a b s) (w a b s) (hD.comp hL) hp rfl
      φ.val hφ φ.property.2 A hA u f hf hfc hu⟩

end IntegralKernels

section FiniteMaskedKernels

/-- A finite family of genuine two-sided square-integrable masks gives nuclearity
of a bounded operator as soon as its kernel agrees on a dense set of inputs. -/
private theorem isNuclearOperator_of_finite_masked_bruhat_on_dense
    {G κ : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [Fintype κ] (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (ν : Measure G) [SigmaFinite ν] (χ : κ → BruhatCompactSupport G) (l r : κ → G → ℂ)
    (hl : ∀ j, MemLp (l j) 2 ν) (hr : ∀ j, MemLp (r j) 2 ν)
    (R : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (D : Set (Lp ℂ 2 ν)) (hD : Dense D)
    (hR : ∀ u ∈ D, ∀ᵐ x ∂ν, R u x = ∑ j, ∫ y, l j x * (χ j).val (x * y⁻¹) * star (r j y) * u y ∂ν) :
    IsNuclearOperator R := by
  classical
  have hN (j : κ) := masked_bruhat_convolution_nuclear μ m hm hms (χ j).property.2
    ((mem_bruhatSmoothSubmodule_iff _).mp (χ j).property.1) ν (hl j) (hr j)
  choose T hn hT htrace using hN
  have heq : R = ∑ j, T j := by
    apply DFunLike.coe_injective
    apply Continuous.ext_on hD R.continuous (map_continuous _)
    intro u hu
    simp only [sum_apply]
    apply Lp.ext
    filter_upwards [hR u hu, Lp.coeFn_fun_finsetSum Finset.univ (fun j ↦ T j u),
      ae_all_iff.mpr (fun j ↦ hT j u)] with x hR hsum hrep
    rw [hR, hsum]
    exact Finset.sum_congr rfl fun j _ ↦ (hrep j).symm
  rw [heq]
  exact (nuclearEndomorphisms _).sum_mem fun j _ ↦ hn j

private theorem weightedIntegral_sub_finite {X ι κ : Type*} [MeasurableSpace X]
    [Fintype ι] [Fintype κ] (ν : Measure X) (g f : X → ℂ) (a : ι → X → ℂ)
    (d : ι → ℂ) (b : κ → X → ℂ) (hg : Integrable (fun y ↦ g y * f y) ν)
    (ha : ∀ i, Integrable (fun y ↦ a i y * f y) ν)
    (hb : ∀ j, Integrable (fun y ↦ b j y * f y) ν)
    (h : ∀ᵐ y ∂ν, g y - ∑ i, d i * a i y = ∑ j, b j y) :
    (∫ y, g y * f y ∂ν) - ∑ i, d i * ∫ y, a i y * f y ∂ν =
      ∑ j, ∫ y, b j y * f y ∂ν := by
  have hind : Integrable (fun y ↦ ∑ i, d i * (a i y * f y)) ν :=
    integrable_finsetSum _ (fun i _ ↦ (ha i).const_mul _)
  calc
    _ = (∫ y, g y * f y ∂ν) - ∫ y, ∑ i, d i * (a i y * f y) ∂ν := by
      rw [integral_finsetSum _ (fun i _ ↦ (ha i).const_mul (d i))]
      simp only [integral_const_mul]
    _ = ∫ y, g y * f y - ∑ i, d i * (a i y * f y) ∂ν := (integral_sub hg hind).symm
    _ = ∫ y, ∑ j, b j y * f y ∂ν := by
      refine integral_congr_ae (h.mono fun y hy ↦ ?_)
      simpa only [sub_mul, Finset.sum_mul, mul_assoc] using congrArg (· * f y) hy
    _ = _ := integral_finsetSum _ (fun i _ ↦ hb i)

/-- A pointwise identity of genuine kernels on compact continuous inputs makes the
difference between an operator and a finite bounded combination nuclear. The
trace-class terms are supplied by square-integrable masks on the same measure. -/
private theorem isNuclearOperator_sub_finite_of_masked_kernel
    {G ι κ : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] [SecondCountableTopology G]
    [Fintype ι] [Fintype κ] (μ : Measure G) [μ.IsHaarMeasure]
    (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m) (hms : Surjective m)
    (ν : Measure G) [SigmaFinite ν] [ν.Regular]
    (T : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν) (M A : ι → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (c : ι → G → ℂ) (k : G → G → ℂ) (q : ι → G → G → ℂ)
    (χ : κ → BruhatCompactSupport G) (l r : κ → G → ℂ)
    (hk : ∀ x, Continuous (k x)) (hq : ∀ i x, Continuous (q i x))
    (hT : ∀ (u : Lp ℂ 2 ν) (f : G → ℂ), Continuous f → HasCompactSupport f →
      (u : G → ℂ) =ᵐ[ν] f → (T u : G → ℂ) =ᵐ[ν] fun x ↦ ∫ y, k x y * f y ∂ν)
    (hA : ∀ (i) (u : Lp ℂ 2 ν) (f : G → ℂ), Continuous f → HasCompactSupport f →
      (u : G → ℂ) =ᵐ[ν] f → (A i u : G → ℂ) =ᵐ[ν] fun x ↦ ∫ y, q i x y * f y ∂ν)
    (hM : ∀ (i) (u : Lp ℂ 2 ν), (M i u : G → ℂ) =ᵐ[ν] fun x ↦ c i x * u x)
    (hl : ∀ j, MemLp (l j) 2 ν) (hr : ∀ j, MemLp (r j) 2 ν)
    (hkernel : ∀ᵐ x ∂ν, ∀ᵐ y ∂ν, k x y - ∑ i, c i x * q i x y =
      ∑ j, l j x * (χ j).val (x * y⁻¹) * star (r j y)) :
    IsNuclearOperator (T - ∑ i, (M i).comp (A i)) := by
  classical
  apply isNuclearOperator_of_finite_masked_bruhat_on_dense μ m hm hms ν χ l r hl hr _
    _ (dense_compactCore ν)
  intro u hu
  obtain ⟨f, hf, hc, huf⟩ := hu
  have hreps (i) : (M i (A i u) : G → ℂ) =ᵐ[ν] fun x ↦ c i x * ∫ y, q i x y * f y ∂ν :=
    (hM i _).trans ((hA i u f hf hc huf).mono fun x h ↦ congrArg (c i x * ·) h)
  simp only [sub_apply, sum_apply, ContinuousLinearMap.comp_apply]
  filter_upwards [Lp.coeFn_sub (T u) (∑ i, M i (A i u)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun i ↦ M i (A i u)), hT u f hf hc huf,
    ae_all_iff.mpr hreps, hkernel] with x hsub hsum ht ha hkernel
  rw [hsub, Pi.sub_apply, ht, hsum]
  simp_rw [ha]
  have hsg (j) : Integrable
      (fun y ↦ l j x * (χ j).val (x * y⁻¹) * star (r j y) * f y) ν := by
    have ht := continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp (χ j).property.1)
    have hb : Continuous (fun y ↦ l j x * (χ j).val (x * y⁻¹)) :=
      continuous_const.mul (ht.comp (continuous_const.mul continuous_inv))
    have hv : MemLp (fun y ↦ l j x * (χ j).val (x * y⁻¹) * f y) 2 ν :=
      (hb.mul hf).memLp_of_hasCompactSupport hc.mul_left
    refine (hv.integrable_mul (hr j).star).congr (.of_forall fun y ↦ ?_)
    change (l j x * (χ j).val (x * y⁻¹) * f y) * star (r j y) = _
    ring
  calc
    _ = ∑ j, ∫ y, l j x * (χ j).val (x * y⁻¹) * star (r j y) * f y ∂ν :=
      weightedIntegral_sub_finite ν _ f _ (fun i ↦ c i x) _
        (((hk x).mul hf).integrable_of_hasCompactSupport hc.mul_left)
        (fun i ↦ ((hq i x).mul hf).integrable_of_hasCompactSupport hc.mul_left) hsg hkernel
    _ = _ := Finset.sum_congr rfl fun i _ ↦ integral_congr_ae (huf.mono fun y hy ↦ by rw [hy])

end FiniteMaskedKernels

section SobolevAdjoints

set_option quotPrecheck false

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
variable (μ : Measure G) [μ.IsHaarMeasure] (m : G →ₜ* ℝ≥0ˣ)

local notation "L" => (fun x : G ↦ Real.log ((m x).val : ℝ))
local notation "w(" a ", " b ", " s ")" => (fun x : G ↦ intervalSobolevDensity a b s (L x))
local notation "ν(" a ", " b ", " s ")" => μ.withDensity (fun x ↦ ENNReal.ofReal (w(a, b, s) x))
local notation "W(" a ", " b ", " s ")" => CompactIntervalSobolev μ L a b s
local notation "A(" hab ", " hs ", " φ ")" => hardySobolevTestAction μ m _ _ _ hab hs φ

/-- A finite expansion of the difference kernel as two-sided masked compact
Bruhat convolutions makes the difference of the actual weighted convolution
and the indicated weighted adjoints nuclear. -/
theorem isNuclearOperator_sub_finite_masked_adjoints {ι κ : Type*} [Fintype ι] [Fintype κ]
    (hm : IsModulation m) (hms : Surjective m) (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport G) (c : ι → G → ℂ) (ψ : ι → BruhatCompactSupport G)
    (M : ι → W(a, b, s) →L[ℂ] W(a, b, s))
    (χ : κ → BruhatCompactSupport G) (l r : κ → G → ℂ)
    (hM : ∀ i (u : W(a, b, s)), (M i u : G → ℂ) =ᵐ[ν(a, b, s)] fun x ↦ c i x * u x)
    (hLR : ∀ j, MemLp (l j) 2 (ν(a, b, s)) ∧ MemLp (r j) 2 (ν(a, b, s)))
    (hid : ∀ x y, φ.val (x * y⁻¹) / (w(a, b, s) y : ℂ) -
      ∑ i, c i x * star ((ψ i).val (y * x⁻¹)) / (w(a, b, s) x : ℂ) =
      ∑ j, l j x * (χ j).val (x * y⁻¹) * star (r j y)) :
    let T : W(a, b, s) →L[ℂ] W(a, b, s) := A(hab, hs, φ)
    IsNuclearOperator (T - ∑ i, (M i).comp (A(hab, hs, ψ i)).adjoint) := by
  intro T
  have hw : Continuous (w(a, b, s)) := (continuous_intervalDensity a b s).comp (continuous_logNorm m)
  have hpos (y : G) : 0 < w(a, b, s) y := intervalDensity_positive a b s _
  let : IsLocallyFiniteMeasure (ν(a, b, s)) := IsLocallyFiniteMeasure.withDensity_ofReal hw
  have hc (d : BruhatCompactSupport G) : Continuous d.val :=
    continuous_of_bruhatSmooth ((mem_bruhatSmoothSubmodule_iff _).mp d.property.1)
  apply isNuclearOperator_sub_finite_of_masked_kernel μ m hm hms (ν(a, b, s)) T M
    (fun i ↦ (A(hab, hs, ψ i)).adjoint) c
    (fun x y ↦ φ.val (x * y⁻¹) / (w(a, b, s) y : ℂ))
    (fun i x y ↦ star ((ψ i).val (y * x⁻¹)) / (w(a, b, s) x : ℂ))
    χ l r ?_ ?_ ?_ ?_ hM (fun j ↦ (hLR j).1) (fun j ↦ (hLR j).2) ?_
  · intro x
    exact ((hc φ).comp (continuous_const.mul continuous_inv)).div
      (Complex.continuous_ofReal.comp hw) (fun y ↦ Complex.ofReal_ne_zero.mpr (hpos y).ne')
  · intro i x
    exact (continuous_star.comp ((hc (ψ i)).comp (continuous_id.mul continuous_const))).div_const _
  · intro u f hf hfc hu
    exact (hardySobolevTestAction_compact_kernels μ m a b s hab hs φ u f hf hfc hu).1
  · intro i u f hf hfc hu
    exact (hardySobolevTestAction_compact_kernels μ m a b s hab hs (ψ i) u f hf hfc hu).2
  · exact .of_forall fun x ↦ .of_forall fun y ↦ by simpa only [mul_div_assoc] using hid x y

end SobolevAdjoints

end RiemannMasullo.WeightedConvolution
