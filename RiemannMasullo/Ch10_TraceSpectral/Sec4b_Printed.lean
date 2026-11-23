module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.Ch10_TraceSpectral.Sec1

/-! # False assertions in §10.4.3 -/

@[expose] public noncomputable section

open Classical Filter Function MeasureTheory NumberField Set UniformSpace
open scoped NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxHeartbeats 900000

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "μ(" F ")" => ideleClassTamagawaMeasure F
local notation "m𝔽(" F ")" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C𝔽(F) →ₜ* ℝ≥0ˣ)
local notation "logNorm(" F ")" => (fun g : C𝔽(F) ↦ Real.log ((ideleClassNorm F g).val : ℝ))
local notation "h₀" => le_refl (0 : ℝ)
local notation "hStrip(" hα ")" => (neg_nonpos.mpr hα |>.trans hα)
local notation "hs₀(" hs ")" => (le_of_lt (zero_lt_one.trans hs))
local notation "w(" F ", " α ", " s ")" => (fun g : C𝔽(F) ↦
  intervalSobolevDensity (-α) α s (logNorm(F) g))
local notation "W(" F ", " α ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) (-α) α s
local notation "W'(" F ", " α ", " s ")" => CompactIntervalSobolev (μ(F)) logNorm(F) (-α) α s true
local notation "A(" F ", " hα ", " hs ", " φ ")" =>
  hardySobolevTestAction (μ(F)) m𝔽(F) _ _ _ (hStrip(hα)) hs φ
local notation "ν(" F ", " α ", " s ")" =>
  ((μ(F)).withDensity fun g ↦ ENNReal.ofReal (w(F, α, s) g))
local notation "ν'(" F ", " α ", " s ")" =>
  ((μ(F)).withDensity fun g ↦ ENNReal.ofReal (w(F, α, s) g)⁻¹)
local notation "sourceFirst(" F ", " α ", " s ")" =>
  Lp ℂ 2 ((ν'(F, α, s)).prod (ν(F, α, s)))
local notation "tensor(" F ", " α ", " s ")" =>
  Completion (ProjectiveTensor W'(F, α, s) W(F, α, s))
local notation "printedClass(" F ", " α ", " s ", " hα ", " hs ", " K ")" =>
  Lp.compMeasurePreserving Prod.swap
    (Measure.measurePreserving_swap (μ := ν'(F, α, s)) (ν := ν(F, α, s)))
    (sobolevProjectiveKernelClass (F := F) hα hs K)

/-- Paper: (10.4.3.1), p. 465. The displayed polynomial is claimed to
regularize the completed Hecke L-function for every unitary character.
Removable values are filled in according to the meromorphic convention of §7.1. -/
def Printed.unshiftedHeckeRegularization_entire : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)),
    Differentiable ℂ (toMeromorphicNFOn (fun z : ℂ ↦
      (z * (z - 1) / 2) ^ (if ∀ g : C₁(F), χ g.val = 1 then (1 : ℕ) else 0) *
        continuedCompletedHeckeL χ z) univ)

/-- Paper: (10.4.3.1), p. 465. For F = ℚ and χ = |·|^i the completed
L-function is completed zeta at z + i. Its pole at 1 − i survives
multiplication by z(z − 1)/2, which is nonzero there. -/
theorem Printed.unshiftedHeckeRegularization_entire_false :
    ¬ Printed.unshiftedHeckeRegularization_entire := by
  intro h
  let c := ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) Complex.I
  have hunit (g : C𝔽(ℚ)) : ‖c g‖ = 1 := by
    change ‖(1 : ℂ) * ((((ideleClassNorm ℚ g).val : ℝ) : ℂ) ^ Complex.I)‖ = 1
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos (NNReal.coe_pos.mpr (Units.zero_lt _))]
    simp
  let χ : PontryaginDual C𝔽(ℚ) :=
    { toFun := fun g ↦ ⟨c g, mem_sphere_zero_iff_norm.mpr (hunit g)⟩
      map_one' := Subtype.ext c.map_one
      map_mul' := fun g k ↦ Subtype.ext (c.map_mul g k)
      continuous_toFun := c.continuous.subtype_mk _ }
  have hk (g : C₁(ℚ)) : χ g.val = 1 := by
    apply Subtype.ext
    change (1 : ℂ) * ((((ideleClassNorm ℚ g.val).val : ℝ) : ℂ) ^ Complex.I) = 1
    rw [MonoidHom.mem_ker.mp g.property]
    simp
  have htwist : ideleClassNormTwist χ 0 = ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ))
      (-Complex.I * ((-1 : ℝ) : ℂ)) := by
    simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg_one, neg_neg]
    ext1 g
    change c g * _ ^ (0 : ℂ) = c g
    simp
  obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec χ
  have hker : χ.toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype = 1 := by
    ext1 g
    exact hk g
  obtain ⟨t, ht, -⟩ := completedHeckeL_continuation_simplePoles χ _ hL hEq hker
  have ht' := (existsUnique_ideleClassNormTwist χ hker).unique ht.1 htwist
  have hpole : meromorphicOrderAt (continuedCompletedHeckeL χ) (1 - Complex.I) = -1 := by
    simpa [ht', sub_eq_add_neg] using ht.2.2.1
  let P := fun z : ℂ ↦ z * (z - 1) / 2
  have hP : Differentiable ℂ P := by
    dsimp [P]
    fun_prop
  have hPne : P (1 - Complex.I) ≠ 0 := by
    dsimp [P]
    apply div_ne_zero (mul_ne_zero _ _) (by norm_num)
    · intro he
      have := congrArg Complex.re he
      norm_num at this
    · simp
  have hentire := h ℚ χ
  simp only [ite_eq_left hk, pow_one] at hentire
  change Differentiable ℂ (toMeromorphicNFOn (P * continuedCompletedHeckeL χ) univ) at hentire
  have hnonneg := (hentire.analyticAt (1 - Complex.I)).meromorphicOrderAt_nonneg
  have hm : MeromorphicOn P univ := fun z _ ↦ (hP.analyticAt z).meromorphicAt
  rw [meromorphicOrderAt_toMeromorphicNFOn (hm.mul hL.meromorphicOn) (mem_univ _),
    meromorphicOrderAt_mul_of_ne_zero (hP.analyticAt _) hPne, hpole] at hnonneg
  exact (by decide : ¬ (0 : WithTop ℤ) ≤ -1) hnonneg

/-- Paper: (10.4.3.5), p. 466. For a fixed character and shift, a unique
family of isotypic exponential-decay tests is biorthogonal to the zero jets.
The functional label uses the unshifted zero, as in the displayed formula. -/
def Printed.spectralSchwartzBiorthogonal_unique : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (χ : PontryaginDual C𝔽(F)) (a : ℝ),
    let ι : C₁(F) →ₜ* C𝔽(F) := ⟨(ideleClassNorm F).ker.subtype, continuous_subtype_val⟩
    let E := ↥(modulatedDecayIsotype m𝔽(F) univ (mem_univ 0) (χ.comp ι))
    let J := {j : ℂ × ℕ // j.2 <
      (meromorphicOrderAt (continuedCompletedHeckeL χ) ((a : ℂ) + j.1)).untop₀.toNat}
    ∃! ψ : J → E, ∀ j j' : J,
      (∫ g, (ψ j').val.val g * ideleClassNormTwist χ ((a : ℂ) + j.val.1) g *
        (logNorm(F) g : ℂ) ^ j.val.2 ∂(μ(F))) = if j = j' then 1 else 0

/-- Paper: (10.4.3.5), p. 466. For F = ℚ, χ = 1 and a = 0, add the
theta function of the rational test with finite factor 1_{ℤ̂} and archimedean
factor exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²) to any claimed biorthogonal
vector. This nonzero test has zero values under every zeta jet by divisibility
of its Mellin transform. Its theta function is nonzero at large norm. -/
theorem Printed.spectralSchwartzBiorthogonal_unique_false :
    ¬ Printed.spectralSchwartzBiorthogonal_unique := by sorry

local notation "represents(" F ", " α ", " s ", " B ", " k ")" =>
  (∀ u : W(F, α, s), ∀ᵐ x ∂(μ(F)),
    Integrable (fun y ↦ k (x, y) * u y) (μ(F)) ∧
      B u x = ∫ y, k (x, y) * u y ∂(μ(F)))
local notation "printedWeight(" F ", " α ", " s ", " ρ ", " k ")" =>
  (fun p : C𝔽(F) × C𝔽(F) ↦ (ρ p.1 * (w(F, α, s) p.2)⁻¹ ^ 2 : ℝ) • k p)

/-- Paper: (10.4.3.24)–(10.4.3.25), p. 470. The tensor image in the
source-first product is claimed to be the unique class whose displayed
weighted integral gives the spectral operator, with k evaluated at (x,y). -/
def Printed.spectralLineKernel_extraWeight : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → ∀ hs : 1 < s,
    ∀ φ : BruhatCompactSupport C𝔽(F),
      let B := (spectralProjection (F := F) a h₀ hs₀(hs)).comp (A(F, h₀, hs₀(hs), φ))
      ∃ K : tensor(F, 0, s), sobolevProjectiveKernelOperator (F := F) h₀ hs₀(hs) K = B ∧
        ∀ l : sourceFirst(F, 0, s),
          represents(F, 0, s, B, (fun p ↦ ((w(F, 0, s) p.2)⁻¹ : ℝ) • l p)) ↔
            l = printedClass(F, 0, s, h₀, hs₀(hs), K)

/-- Paper: (10.4.3.25), p. 470. Take F = ℚ, s = 4 and a equal to the
abscissa of the first positive-ordinate nontrivial zeta zero. A nonnegative
smooth test supported in a sufficiently small log-norm band about zero has
nonzero Mellin value there after shifting by a. The order-zero jet shows
spectral projection after convolution is nonzero. Let h be its output-first
Haar kernel. The displayed weighted integral would give
h(x,y) = h(y,x)/w(y) locally almost everywhere. Swapping x,y forces h to
vanish unless w(x)w(y)=1, a product-null set. Missing existence of a tensor
would itself falsify the asserted existence and uniqueness. -/
theorem Printed.spectralLineKernel_extraWeight_false :
    ¬ Printed.spectralLineKernel_extraWeight := by sorry

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471, second formula. The cutoff
spectral function is claimed to represent the geometric truncation.
The two reciprocal weights account for (10.4.3.26) and (10.4.3.30). -/
def Printed.spectralLineTruncatedKernel_geometric : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a s : ℝ), 0 < a → ∀ hs : 1 < s,
    ∀ (Λ ε : ℝ) (ρ : C𝔽(F) → ℝ) (hρ : IsModulatedCutoff m𝔽(F) Λ ε ρ),
      0 < Λ⁻¹ + ε → Λ⁻¹ + ε < Λ - ε →
      ∀ φ : BruhatCompactSupport C𝔽(F),
        let B := (spectralProjection (F := F) a h₀ hs₀(hs)).comp (A(F, h₀, hs₀(hs), φ))
        ∃ K : tensor(F, 0, s), sobolevProjectiveKernelOperator (F := F) h₀ hs₀(hs) K = B ∧
          IsSobolevHilbertSchmidtKernel (geometricTruncatedConvolution a h₀ hs₀(hs) hρ φ)
            (printedWeight(F, 0, s, ρ, printedClass(F, 0, s, h₀, hs₀(hs), K)))

section GeometricKernelCounterexample

local notation "C" => C𝔽(ℚ)
local notation "m" => m𝔽(ℚ)
local notation "μC" => μ(ℚ)
local notation "L" => logNorm(ℚ)
local notation "d(" α ")" => w(ℚ, α, 2)
local notation "νp(" α ")" => ν(ℚ, α, 2)
local notation "νm(" α ")" => ν'(ℚ, α, 2)
local notation "W₂(" α ")" => W(ℚ, α, 2)
local notation "hs₂" => (show (0 : ℝ) ≤ 2 by norm_num)

/-- To the right of the line of real part one, the strip jet family is
empty and its common kernel is the entire Sobolev space. -/
private theorem geometricKernel_theta_top {a α : ℝ} (hα : 0 ≤ α) (ha : 1 < a - α) :
    globalThetaSobolev ℚ a (hStrip(hα)) hs₂ = ⊤ := by
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  have hn (j : SpectralStripJetIndex χ a α 2) : False := by
    let z : ℂ := (a + j.val.2.1 : ℝ) + (j.val.2.2.1 : ℂ) * Complex.I
    let θ := χ j.val.1
    obtain ⟨hj, hp⟩ := j.mem_strip_order_pos hα
    have hz : 1 < z.re := by
      have hleft := hj.1
      simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith
    obtain ⟨hL, hEq⟩ := continuedCompletedHeckeL_spec θ
    change 0 < meromorphicOrderAt (continuedCompletedHeckeL θ) z at hp
    exact hz.not_gt (completedHeckeL_continuation_zeros θ _ hL hEq (zero_lt_one.trans hz) hp)
  apply top_unique
  intro u _
  exact (spectralStripJet_commonKernel (a := a) χ hχ hα hs₂ u).2 (fun j ↦ (hn j).elim)

/-- The spectral projection vanishes when the strip lies to the right of one. -/
private theorem geometricKernel_projection_zero {a α : ℝ} (hα : 0 ≤ α) (ha : 1 < a - α) :
    spectralProjection (F := ℚ) a hα hs₂ = 0 := by
  apply ContinuousLinearMap.ext
  intro u
  let N := globalThetaSobolev ℚ a (hStrip(hα)) hs₂
  let v := spectralProjection (F := ℚ) a hα hs₂ u
  have hv : v ∈ N.orthogonal := N.orthogonal.starProjection_apply_mem u
  have hbot : N.orthogonal = ⊥ := by
    change (globalThetaSobolev ℚ a (hStrip(hα)) hs₂).orthogonal = ⊥
    rw [geometricKernel_theta_top hα ha, Submodule.top_orthogonal_eq_bot]
  rw [hbot] at hv
  change v = 0
  rwa [Submodule.mem_bot] at hv

private theorem geometricKernel_density (α : ℝ) (g : C) :
    d(α) g = max (Real.exp (2 * -α * L g)) (Real.exp (2 * α * L g)) * (1 + L g ^ 2) := by
  norm_num [intervalSobolevDensity]

private theorem geometricKernel_density_continuous (α : ℝ) : Continuous d(α) := by
  rw [funext (geometricKernel_density α)]
  have hn : Continuous (fun g : C ↦ (((ideleClassNorm ℚ g).val : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp (m).continuous)
  have hlog : Continuous L := hn.log fun _ ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  exact ((Real.continuous_exp.comp (continuous_const.mul hlog)).max
    (Real.continuous_exp.comp (continuous_const.mul hlog))).mul
    (continuous_const.add (hlog.pow 2))

private theorem geometricKernel_haar_ac (α : ℝ) :
    μC ≪ νp(α) ∧ μC ≪ νm(α) := by
  have hp (g : C) : 0 < d(α) g := by rw [geometricKernel_density]; positivity
  refine ⟨?_, ?_⟩
  · exact withDensity_absolutelyContinuous'
      (geometricKernel_density_continuous α).measurable.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (hp g)).ne')
  · exact withDensity_absolutelyContinuous'
      (geometricKernel_density_continuous α).measurable.inv.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun g ↦ (ENNReal.ofReal_pos.mpr (inv_pos.mpr (hp g))).ne')

/-- A smooth cutoff is a compact Bruhat test. Using its own Sobolev vector
as input exhibits a nonzero cutoff of its convolution action. -/
private theorem geometricKernel_cutoff_convolution_nonzero {α : ℝ} (hα : 0 ≤ α) :
    ∃ (ρ : C → ℝ) (hρ : IsModulatedCutoff m 2 (1 / 4) ρ)
      (φ : BruhatCompactSupport C),
      (modulatedCutoffOperator m νp(α) hρ).comp (A(ℚ, hα, hs₂, φ)) ≠ 0 := by
  let hm : IsModulation m := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
  have hsurj : Surjective m := by
    intro q
    exact ⟨QuotientGroup.mk (canonicalIdeleNormSection ℚ q),
      canonicalIdeleNormSection_rightInverse ℚ q⟩
  obtain ⟨ρ, hρ⟩ := exists_smoothModulatedCutoff_radius_two m hm hsurj
  -- The proper-norm compactness calculation follows the conjugate-weight refutation in §10.3.
  have hK : HasCompactSupport ρ := by
    let e := Nonneg.unitsHomeomorphPos ℝ
    have hc : IsCompact ((Subtype.val : Ioi (0 : ℝ) → ℝ) ⁻¹' Icc (2⁻¹ : ℝ) 2) := by
      rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr]
      · exact isCompact_Icc
      · intro r hr
        exact (by norm_num : (0 : ℝ) < 2⁻¹).trans_le hr.1
    exact (hm.1.isCompact_preimage (e.isCompact_preimage.mpr hc)).of_isClosed_subset
      (isClosed_tsupport ρ) hρ.1.support_subset
  let b (g : C) : ℂ := ρ g
  have hbc : Continuous b := Complex.continuous_ofReal.comp hρ.continuous
  have hbK : HasCompactSupport b := hK.comp_left Complex.ofReal_zero
  let φ : BruhatCompactSupport C := ⟨b, (mem_bruhatSmoothSubmodule_iff _).mpr hρ.2, hbK⟩
  have h1 : ρ 1 = 1 := IsModulatedCutoff.apply_one m hρ.1 (by norm_num) (by norm_num)
  let : IsLocallyFiniteMeasure νp(α) := sobolevKernelWeight_locallyFinite (F := ℚ) α 2
  have hb : MemLp b 2 νp(α) := hbc.memLp_of_hasCompactSupport hbK
  let u : W₂(α) := hb.toLp b
  let Aφ := A(ℚ, hα, hs₂, φ)
  let G := (modulatedCutoffOperator m νp(α) hρ.1).comp Aφ
  refine ⟨ρ, hρ.1, φ, fun hG ↦ ?_⟩
  have hu : (u : C → ℂ) =ᵐ[μC] b := (geometricKernel_haar_ac α).1.ae_le hb.coeFn_toLp
  have hconv (x : C) :
      lcaConvolution μC φ.val u x = (∫ g, ρ g * ρ (g⁻¹ * x) ∂μC : ℝ) := by
    unfold lcaConvolution
    rw [← integral_complex_ofReal]
    apply integral_congr_ae
    have he (g : C) : x / g = g⁻¹ * x := by rw [div_eq_mul_inv, mul_comm]
    have hh := (Measure.measurePreserving_div_left μC x).quasiMeasurePreserving.ae_eq_comp hu
    filter_upwards [hh] with g hg
    change u (x / g) = b (x / g) at hg
    rw [he] at hg
    rw [hg, Complex.ofReal_mul]
  have hAe : (Aφ u : C → ℂ) =ᵐ[μC] fun x ↦
      ((∫ g, ρ g * ρ (g⁻¹ * x) ∂μC : ℝ) : ℂ) :=
    (hardySobolevTestAction_apply μC m (-α) α 2 (hStrip(hα)) hs₂ φ u).trans (ae_of_all μC hconv)
  have hmulAe := (geometricKernel_haar_ac α).1.ae_le
    (modulatedCutoffOperator_apply m νp(α) hρ.1 (Aφ u))
  have hzero : (G u : C → ℂ) =ᵐ[μC] 0 := by
    change G = 0 at hG
    rw [hG, zero_apply]
    exact (geometricKernel_haar_ac α).1.ae_le (Lp.coeFn_zero ℂ 2 νp(α))
  have hvanish : ∀ᵐ x ∂μC, ρ x * (∫ g, ρ g * ρ (g⁻¹ * x) ∂μC) = 0 := by
    filter_upwards [hAe, hmulAe, hzero] with x hAx hMx hZx
    change (modulatedCutoffOperator m νp(α) hρ.1 (Aφ u) : C → ℂ) x = 0 at hZx
    rw [hMx, hAx, ← Complex.ofReal_mul] at hZx
    exact Complex.ofReal_eq_zero.mp hZx
  let U := {x : C | 0 < ρ x}
  have hU : IsOpen U := isOpen_lt continuous_const hρ.continuous
  have hU1 : (1 : C) ∈ U := by change 0 < ρ 1; rw [h1]; norm_num
  have hpos (x : C) (hx : x ∈ U) : 0 < ∫ g, ρ g * ρ (g⁻¹ * x) ∂μC := by
    have hc : Continuous (fun g : C ↦ ρ g * ρ (g⁻¹ * x)) :=
      hρ.continuous.mul (hρ.continuous.comp (continuous_inv.mul continuous_const))
    apply hc.integral_pos_of_hasCompactSupport_nonneg_ne_zero hK.mul_right
      (fun g ↦ mul_nonneg (hρ.1.nonneg g) (hρ.1.nonneg _)) (x := 1)
    simpa only [h1, inv_one, one_mul] using (ne_of_gt hx)
  have hnot : ∀ᵐ x ∂μC, x ∉ U := hvanish.mono fun x hz hx ↦ (mul_pos hx (hpos x hx)).ne' hz
  have hnull : μC U = 0 := by simpa only [ae_iff, not_not, ofPred_mem_eq] using hnot
  exact (hU.measure_pos μC ⟨1, hU1⟩).ne' hnull

local notation "printedK(" α ", " hα ", " K ")" =>
  Lp.compMeasurePreserving Prod.swap
    (Measure.measurePreserving_swap (μ := νm(α)) (ν := νp(α)))
    (sobolevProjectiveKernelClass (F := ℚ) hα hs₂ K)

/-- The mixed Sobolev kernel of the zero spectral operator is zero. The
positive densities allow this to be read in the positive product measure. -/
private theorem geometricKernel_printed_zero {α : ℝ} (hα : 0 ≤ α)
    (K : tensor(ℚ, α, 2))
    (hK : sobolevProjectiveKernelOperator (F := ℚ) hα hs₂ K = 0)
    (r : C → ℝ) :
    printedWeight(ℚ, α, 2, r, printedK(α, hα, K))
      =ᵐ[(νp(α)).prod (νp(α))] 0 := by
  have hZero : (0 : Lp ℂ 2 ((νp(α)).prod (νm(α)))) =
      sobolevProjectiveKernelClass (F := ℚ) hα hs₂ K := by
    apply (sobolevProjectiveKernelClass_spec (F := ℚ) hα hs₂ K 0).1
    rw [hK]
    intro u
    have h0 := Lp.coeFn_zero ℂ 2 ((νp(α)).prod (νm(α)))
    have hAc : (μC).prod (μC) ≪ (νp(α)).prod (νm(α)) :=
      (geometricKernel_haar_ac α).1.prod (geometricKernel_haar_ac α).2
    have hrow := Measure.ae_ae_of_ae_prod (hAc.ae_le h0)
    have hzero := (geometricKernel_haar_ac α).1.ae_le (Lp.coeFn_zero ℂ 2 νp(α))
    filter_upwards [hrow, hzero] with x hx hzx
    have hh : (fun y ↦ (0 : Lp ℂ 2 ((νp(α)).prod (νm(α)))) (x, y) * u y) =ᵐ[μC] (0 : C → ℂ) := by
      filter_upwards [hx] with y hy
      simp only [hy, Pi.zero_apply, zero_mul]
    exact ⟨(integrable_zero C ℂ μC).congr hh.symm, hzx.trans (by rw [integral_congr_ae hh]; simp)⟩
  have hk : printedK(α, hα, K) = 0 := by
    rw [← hZero, map_zero]
  have hAc : (νp(α)).prod (νp(α)) ≪ (νm(α)).prod (νp(α)) :=
    ((withDensity_absolutelyContinuous μC _).trans (geometricKernel_haar_ac α).2).prod
      (Measure.AbsolutelyContinuous.refl _)
  rw [hk]
  filter_upwards [hAc.ae_le (Lp.coeFn_zero ℂ 2 ((νm(α)).prod (νp(α))))] with x hx
  rw [hx]
  simp

/-- A representative vanishing almost everywhere gives the zero operator. -/
private theorem geometricKernel_operator_zero {α : ℝ}
    (B : W₂(α) →L[ℂ] W₂(α)) (k : C × C → ℂ)
    (hk : k =ᵐ[(νp(α)).prod (νp(α))] 0)
    (hB : IsSobolevHilbertSchmidtKernel B k) : B = 0 := by
  obtain ⟨hm, hrep⟩ := hB
  obtain ⟨h0, hzero⟩ := isSobolevHilbertSchmidtKernel_zero (F := ℚ) (α := α) (s := 2)
  have he : hm.toLp k = h0.toLp 0 := MemLp.toLp_congr _ _ hk
  rw [he] at hrep
  exact hrep.symm.trans hzero

private theorem geometricKernel_line_eq {r : C → ℝ}
    (hr : IsModulatedCutoff m 2 (1 / 4) r) (φ : BruhatCompactSupport C) :
    (modulatedCutoffOperator m νp(0) hr).comp (A(ℚ, h₀, hs₂, φ)) =
      geometricTruncatedConvolution (F := ℚ) 2 h₀ hs₂ hr φ := by
  apply ContinuousLinearMap.ext
  intro u
  symm
  apply geometricTruncatedConvolution_apply_of_mem
  rw [geometricKernel_theta_top h₀ (by norm_num : (1 : ℝ) < 2 - 0)]
  exact Submodule.mem_top

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471. Over the rationals on the
zero-free line a = 2, take s = 2 and the smooth cutoff of radius two and
width one quarter. The spectral kernel vanishes. The cutoff's
self-convolution gives a nonzero geometric truncation. -/
theorem Printed.spectralLineTruncatedKernel_geometric_false :
    ¬ Printed.spectralLineTruncatedKernel_geometric := by
  intro hall
  obtain ⟨r, hr, φ, hne⟩ := geometricKernel_cutoff_convolution_nonzero h₀
  obtain ⟨K, hK, hrep⟩ := hall ℚ 2 2 (by norm_num) (by norm_num)
    2 (1 / 4) r hr (by norm_num) (by norm_num) φ
  have hspec := geometricKernel_projection_zero h₀ (a := 2) (by norm_num)
  have hk : sobolevProjectiveKernelOperator (F := ℚ) h₀ hs₂ K = 0 := by
    rw [hK, hspec]
    exact ContinuousLinearMap.zero_comp _
  have hG := geometricKernel_operator_zero _ _ (geometricKernel_printed_zero h₀ K hk r) hrep
  exact hne ((geometricKernel_line_eq hr φ).trans hG)


-- TODO(paper-gap): (10.4.3.45) applies the ambient kernel map to the
-- quotient tensor from (10.4.3.42). The bounds in (10.4.3.40) and in
-- (10.4.3.42) use N_s, while (10.4.3.38) and (10.4.3.43) use N_{I,s}.
-- There is no single literal typed assertion fixing both choices. Any
-- ambient limit of the transposed rectangles has spectral output, also
-- when the quotient tensors are transported by the map of (10.4.3.20).

/-- Paper: Theorem 10.4.3.5(3), p. 473. A necessary consequence of the
operator identity is that convolution after spectral projection has
spectral range, since every displayed rectangle has spectral output.
Deviation: This records a consequence independent of the ambiguous index
bounds and tensor type in the display. -/
def spectralStripTransposeLimit_rangeConsequence : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α s : ℝ), 0 < a →
    ∀ (hα : 0 ≤ α) (hs : 1 < s) (φ : BruhatCompactSupport C𝔽(F)),
      ∀ u : W(F, α, s),
        A(F, hα, hs₀(hs), φ) (spectralProjection a hα hs₀(hs) u) ∈
          (globalThetaSobolev F a hStrip(hα) hs₀(hs)).orthogonal

/-- Paper: Theorem 10.4.3.5(3), p. 473. Over ℚ use α = 0, s = 4
and a nontrivial zeta zero a + iγ. Its order-zero Riesz vector on the
log-norm line is g(t) = exp(−iγt)/(1+t²)². Every printed finite section
has spectral output. Take the nonzero weighted theta vector q of the
polar-free rational test with finite factor 1_{ℤ̂} and real factor
exp(−πx²) − 3 exp(−4πx²) + 2 exp(−16πx²).
The Fourier transform of (1+t²)⁻² is everywhere positive, so pairing q
with translates of g cannot vanish identically. Choose a smooth bump
of integral one concentrated at such a shift as φ. Then A(φ)g has a
nonzero geometric component, whereas any limit of the printed tensors
has spectral output. -/
theorem spectralStripTransposeLimit_rangeConsequence_false :
    ¬ spectralStripTransposeLimit_rangeConsequence := by sorry

/-- Paper: Theorem 10.4.3.6(2), p. 473, second formula. The cutoff
spectral function is claimed to represent the geometric restriction.
The two reciprocal weights account for (10.4.3.47) and (10.4.3.49).
The tensor is identified by the operator in (10.4.3.45).
Deviation: Interpret the unbound endpoint b using the cited interval [−α, α]. -/
def Printed.spectralStripRestrictionKernel_geometric : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (a α s : ℝ), 0 < a →
    ∀ (hα : 0 ≤ α) (hs : 1 < s) (Λ ε : ℝ) (ρ : C𝔽(F) → ℝ)
      (hρ : IsModulatedCutoff m𝔽(F) Λ ε ρ),
      0 < Λ⁻¹ + ε → Λ⁻¹ + ε < Λ - ε →
      ∀ φ : BruhatCompactSupport C𝔽(F),
        let B := (A(F, hα, hs₀(hs), φ)).comp (spectralProjection (F := F) a hα hs₀(hs))
        ∃ K : tensor(F, α, s), sobolevProjectiveKernelOperator (F := F) hα hs₀(hs) K = B ∧
          IsSobolevHilbertSchmidtKernel (geometricRestriction a hα hs₀(hs) hρ φ)
            (printedWeight(F, α, s, ρ, printedClass(F, α, s, hα, hs₀(hs), K)))

/-- Paper: Theorem 10.4.3.6(2), p. 473. Over the rationals, take a = 3,
α = 1 and s = 2. The strip lies to the right of one, so its spectral kernel
vanishes. The self-convolution of the smooth cutoff of radius two and
width one quarter gives a nonzero geometric restriction. -/
theorem Printed.spectralStripRestrictionKernel_geometric_false :
    ¬ Printed.spectralStripRestrictionKernel_geometric := by
  intro hall
  have hα : (0 : ℝ) ≤ 1 := by norm_num
  obtain ⟨r, hr, φ, hne⟩ := geometricKernel_cutoff_convolution_nonzero hα
  obtain ⟨K, hK, hrep⟩ := hall ℚ 3 1 2 (by norm_num) hα (by norm_num)
    2 (1 / 4) r hr (by norm_num) (by norm_num) φ
  have ha : (1 : ℝ) < 3 - 1 := by norm_num
  have hk : sobolevProjectiveKernelOperator (F := ℚ) hα hs₂ K = 0 := by
    rw [hK, geometricKernel_projection_zero hα ha]
    exact ContinuousLinearMap.comp_zero _
  have hG := geometricKernel_operator_zero _ _ (geometricKernel_printed_zero hα K hk r) hrep
  apply hne
  refine Eq.trans ?_ hG
  apply ContinuousLinearMap.ext
  intro u
  symm
  apply geometricRestriction_apply_of_mem
  rw [geometricKernel_theta_top hα ha]
  exact Submodule.mem_top

end GeometricKernelCounterexample

end RiemannMasullo
