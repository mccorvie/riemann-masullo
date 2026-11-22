module

public import RiemannMasullo.Ch09_HardySobolev.Sec1
public import RiemannMasullo.AppD_SchwartzBruhat.Sec3b
public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec1
public import Mathlib.Analysis.InnerProductSpace.TensorProduct
public import Mathlib.Analysis.Fourier.LpSpace
import RiemannMasullo.ForMathlib.MeasureTheory.Group.Arithmetic

/-!
# Hardy–Sobolev spaces and Paley–Wiener conditions

Masullo, §9.2, pp. 403–419. Scalar functions on the positive reals are represented
in the coordinate `x = log t`, so multiplicative Haar measure becomes Lebesgue measure.
-/

@[expose] public noncomputable section

open Filter Function MeasureTheory Set
open scoped ENNReal NNReal Topology TensorProduct

set_option maxSynthPendingDepth 3

namespace RiemannMasullo

-- TODO(paper-gap): The coordinate integrals on pp. 403 and 416 omit the
-- kernel character. Use the intrinsic transform from §D.3.3.

section Idelic

open NumberField
open scoped NumberField.AdeleRing

variable {F : Type*} [Field F] [NumberField F]

local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
set_option quotPrecheck false in
local notation "m[" F "]" =>
  (⟨ideleClassNorm F, (isProperMap_ideleClassNorm F).continuous⟩ : C[F] →ₜ* ℝ≥0ˣ)
set_option quotPrecheck false in
local notation "hm[" F "]" => (show IsModulation m[F] from
  ⟨isProperMap_ideleClassNorm F, ideleClassNorm_ne_one (F := F)⟩)

local instance instT2ClassSec2 : T2Space C[F] := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.1
local instance instLocallyCompactClassSec2 : LocallyCompactSpace C[F] :=
  (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.1
local instance instMeasurableClassSec2 : MeasurableSpace C[F] := borel _
local instance instBorelClassSec2 : BorelSpace C[F] := ⟨rfl⟩

/-- Paper: Remark 9.2.0.1, p. 403. Theta sends a polar test into the test space of
the two-sided Fourier–Mellin transform on the idele class group. -/
theorem adelicTheta_mem_modulatedExponentialDecay_of_polar
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) (_hf : f ∈ adelePolarSubspace F) :
    (adelicTheta (F := F) f : C[F] → ℂ) ∈ modulatedExponentialDecaySubmodule m[F] univ := by sorry

-- The canonical measure in §D.2 takes second countability as a typeclass argument.
variable [SecondCountableTopology C[F]]

/-- Paper: Remark 9.2.0.1, p. 403. The idele class Tamagawa measure is the canonical
modulated Haar measure times the Tamagawa mass of the norm-one classes. -/
theorem ideleClassTamagawaMeasure_eq_smul_canonical :
    ideleClassTamagawaMeasure F =
      (normOneIdeleClassTamagawaMeasure F) univ • canonicalModulatedHaar m[F] hm[F] := by
  let K := (ideleClassNorm F).ker
  let Q := C[F] ⧸ K
  let μC := ideleClassTamagawaMeasure F
  let μ₁ := normOneIdeleClassTamagawaMeasure F
  have hV := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  have hW := hV.2.2.2.2.2.2
  obtain ⟨hKc, hKcpt, hK₂, -⟩ := ideleClassGroup_finiteness F
  have : CompactSpace K := hKcpt
  have : μC.IsHaarMeasure := hV.2.2.1.1
  have : μC.Regular := hV.2.2.1.2.1
  have : μ₁.IsHaarMeasure := hV.2.2.2.1
  have : μ₁.Regular := hV.2.2.2.2.1
  obtain ⟨-, -, -, -, -, -, -, -, hn, hsurj, ⟨s, hs, hsn⟩, -⟩ := ideleGroup_quotient.{_, 0} F
  have : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ ℝ≥0
  have : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  have : SFinite (positiveRealHaar : Measure ℝ≥0ˣ) := by unfold positiveRealHaar; infer_instance
  -- The band of norms between 1 and e has `dt/t`-mass one.
  let S : Set ℝ≥0ˣ := {t | ((t.val : ℝ≥0) : ℝ) ∈ Icc 1 (Real.exp 1)}
  have hSm : MeasurableSet S :=
    (NNReal.continuous_coe.comp Units.continuous_val).measurable measurableSet_Icc
  have hPRS : positiveRealHaar S = 1 := by
    let T : ℝ≥0ˣ := Units.mk0 (Real.exp 1).toNNReal (by positivity)
    have hT : ((T.val : ℝ≥0) : ℝ) = Real.exp 1 := Real.coe_toNNReal _ (Real.exp_pos 1).le
    have h := positiveRealHaar_interval T (by rw [hT]; exact Real.one_le_exp zero_le_one)
    rw [hT, Real.log_exp, ENNReal.ofReal_one] at h
    exact h
  let B : Set C[F] := ideleClassNorm F ⁻¹' S
  have hBm : MeasurableSet B := (hn.measurable) hSm
  -- The canonical measure gives the band mass one.
  have : CompactSpace m[F].toMonoidHom.ker := isCompact_iff_compactSpace.mp hm[F].isCompact_ker
  obtain ⟨τ', hτ'⟩ := hm[F].exists_section
  let r : ℝ≥0ˣ →ₜ* m[F].toMonoidHom.range :=
    ⟨(MonoidHom.id ℝ≥0ˣ).codRestrict _ fun t ↦ hsurj t, continuous_id.subtype_mk _⟩
  let τ : ℝ≥0ˣ →ₜ* C[F] := τ'.comp r
  have hτ : RightInverse τ m[F] := fun t ↦ hτ' (r t)
  let μ₀ : Measure m[F].toMonoidHom.ker := Measure.haarMeasure ⊤
  have hcan := canonicalModulatedHaar_eq_map_prod m[F] hm[F] τ hτ μ₀ Measure.haarMeasure_self
  have hφ : Continuous fun z : m[F].toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C[F]) * τ z.2 := by fun_prop
  have hcanB : canonicalModulatedHaar m[F] hm[F] B = 1 := by
    rw [hcan, Measure.map_apply hφ.measurable hBm]
    have hpre : (fun z : m[F].toMonoidHom.ker × ℝ≥0ˣ ↦ (z.1 : C[F]) * τ z.2) ⁻¹' B =
        univ ×ˢ S := by
      ext ⟨k, t⟩
      have hk : ideleClassNorm F (k : C[F]) = 1 := k.property
      change ideleClassNorm F ((k : C[F]) * τ t) ∈ S ↔ _
      rw [map_mul, hk, one_mul, show ideleClassNorm F (τ t) = t from hτ t]
      simp
    rw [hpre, Measure.prod_prod, show μ₀ univ = 1 from Measure.haarMeasure_self, one_mul, hPRS]
  -- Weil's formula computes the class measure of the band.
  let : MeasurableSpace Q := borel Q
  have : BorelSpace Q := ⟨rfl⟩
  let e₀ := QuotientGroup.quotientKerEquivOfRightInverse (ideleClassNorm F) s hsn
  let e : Q ≃ₜ* ℝ≥0ˣ :=
    { e₀ with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk K).continuous_iff.mpr hn
      continuous_invFun := QuotientGroup.continuous_mk.comp hs }
  have he : MeasurableEmbedding (QuotientGroup.kerLift (ideleClassNorm F)) :=
    e.toHomeomorph.measurableEmbedding
  have hkerLift (q : Q) : QuotientGroup.kerLift (ideleClassNorm F) q = ideleClassNorm F q.out := by
    conv_lhs => rw [← Quotient.out_eq' q]
    rfl
  have hScpt : IsCompact S := by
    let h := Nonneg.unitsHomeomorphPos ℝ
    have hK : IsCompact {y : {x : ℝ // 0 < x} | y.val ∈ Icc 1 (Real.exp 1)} := by
      rw [Topology.IsEmbedding.subtypeVal.isCompact_iff]
      convert isCompact_Icc (a := (1 : ℝ)) (b := Real.exp 1) using 1
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, by linarith [hx.1]⟩, hx, rfl⟩
    have hSeq : S = h ⁻¹' {y | y.val ∈ Icc 1 (Real.exp 1)} := rfl
    rw [hSeq, ← h.image_symm]
    exact hK.image h.symm.continuous
  have hBcpt : IsCompact B := (isProperMap_ideleClassNorm F).isCompact_preimage hScpt
  let f : C[F] → ℂ := B.indicator fun _ ↦ 1
  have hfint : Integrable f μC :=
    (integrable_indicator_iff hBm).mpr (integrableOn_const hBcpt.measure_lt_top.ne)
  have hL1 := (weilQuotientIntegral_L1 K hKc μC μ₁ _ hW hfint).2.2
  let B' : Set Q := QuotientGroup.kerLift (ideleClassNorm F) ⁻¹' S
  have hB'm : MeasurableSet B' := he.measurable hSm
  have hcoset (q : Q) : lcaCosetIntegral K μ₁ f q = (μ₁.real univ : ℂ) * B'.indicator 1 q := by
    have hf (h : K) : f (q.out * (h : C[F])) = f q.out := by
      have hh : ideleClassNorm F (h : C[F]) = 1 := h.property
      simp only [f, B, indicator, mem_preimage, map_mul, hh, mul_one]
    simp only [lcaCosetIntegral, hf, integral_const, Complex.real_smul, measureReal_def]
    congr 1
    simp only [f, B, B', indicator, mem_preimage, hkerLift, Pi.one_apply]
  have hlhs : ∫ x, f x ∂μC = (μC.real B : ℂ) := by
    simp only [f, integral_indicator hBm, setIntegral_const, Complex.real_smul, mul_one]
  have hrhs : ∫ q, lcaCosetIntegral K μ₁ f q
      ∂(positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))) =
        (μ₁.real univ : ℂ) := by
    have hdt : (positiveRealHaar.comap (QuotientGroup.kerLift (ideleClassNorm F))).real B' = 1 := by
      have hsurj' : Surjective (QuotientGroup.kerLift (ideleClassNorm F)) := e.surjective
      rw [measureReal_def, he.comap_apply, show QuotientGroup.kerLift (ideleClassNorm F) '' B' = S
        from image_preimage_eq S hsurj', hPRS, ENNReal.toReal_one]
    simp only [hcoset, integral_const_mul]
    erw [integral_indicator hB'm]
    simp only [Pi.one_apply, setIntegral_const, Complex.real_smul, mul_one, hdt,
      Complex.ofReal_one]
  have hμCB : μC B = μ₁ univ := by
    have h : μC.real B = μ₁.real univ := by exact_mod_cast hlhs.symm.trans (hL1.trans hrhs)
    rwa [measureReal_def, measureReal_def,
      ENNReal.toReal_eq_toReal_iff' hBcpt.measure_lt_top.ne (measure_ne_top _ _)] at h
  -- Compare the two Haar measures on the band.
  have : (canonicalModulatedHaar m[F] hm[F]).IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m[F] hm[F]).exists).1
  have hscale := Measure.isMulLeftInvariant_eq_smul μC (canonicalModulatedHaar m[F] hm[F])
  set c := Measure.haarScalarFactor μC (canonicalModulatedHaar m[F] hm[F])
  have hc : (c : ℝ≥0∞) = μ₁ univ := by
    have h := congrArg (fun ν : Measure C[F] ↦ ν B) hscale
    simp only [smul_apply, ENNReal.smul_def, smul_eq_mul] at h
    rw [← hμCB, h, hcanB, mul_one]
  exact hscale.trans (by rw [ENNReal.smul_def, hc])

/-- Paper: Remark 9.2.0.1, p. 403. On the polar subspace the canonical theta integral
converges at every character and computes the entire global Z-function after rescaling. -/
theorem globalIdelicZFunction_eq_canonical_of_vanishing
    (f : SchwartzBruhat (Multiplicative 𝔸[F])) (hf : f ∈ adelePolarSubspace F)
    (c : QuasiCharacter C[F]) :
    let μ := canonicalModulatedHaar m[F] hm[F]
    let V := (normOneIdeleClassTamagawaMeasure F).real univ
    Integrable (fun g ↦ adelicTheta (F := F) f g * c g) μ ∧
      globalIdelicZFunction f c =
        (V : ℂ) * modulatedFourierMellin m[F] univ hm[F] μ (adelicTheta (F := F) f) c := by
  obtain ⟨h₀, hF₀⟩ := (mem_adelePolarSubspace f).mp hf
  have hμ := ideleClassTamagawaMeasure_eq_smul_canonical (F := F)
  have hI := globalThetaMellinIntegral_integrable_of_vanishing f h₀ hF₀ c
  have hZ := congrFun (globalThetaMellinIntegral_eq_continuation_of_vanishing f h₀ hF₀) c
  let V := normOneIdeleClassTamagawaMeasure F univ
  have hV := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec
  let : (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure := hV.2.2.2.1
  let : CompactSpace (ideleClassNorm F).ker := isCompact_iff_compactSpace.mp hm[F].isCompact_ker
  have hpos : V ≠ 0 := ne_of_gt (isOpen_univ.measure_pos _ univ_nonempty)
  have hfin : V ≠ ∞ := measure_ne_top _ _
  rw [hμ] at hI
  refine ⟨(integrable_smul_measure hpos hfin).mp hI, ?_⟩
  rw [← hZ, globalThetaMellinIntegral, hμ, integral_smul_measure]
  simp [modulatedFourierMellin, relativeVerticalStrip, measureReal_def, Complex.real_smul]

/-- Paper: Remark 9.2.0.1, p. 403. At a regular character the §5.1 operator agrees
with the scaled canonical transform. The quotient form follows from `globalThetaMellin_mk`.
Deviation: (5.1.1.1) names the operator Z. Its bundled target records regular values. -/
theorem globalIdelicMellin_eq_canonical_of_vanishing
    (f : SchwartzBruhat (Multiplicative 𝔸[F]))
    (hf : f (Multiplicative.ofAdd 0) = 0)
    (hFourier : adeleSchwartzFourier (F := F) f (Multiplicative.ofAdd 0) = 0)
    (c : {c : QuasiCharacter C[F] // 0 ≤ globalIdelicOrderBound (F := F) c}) :
    let μ := canonicalModulatedHaar m[F] hm[F]
    let V := (normOneIdeleClassTamagawaMeasure F).real univ
    Integrable (fun g ↦ adelicTheta (F := F) f g * c.val g) μ ∧
      (globalIdelicMellin (F := F) f).val c =
        (V : ℂ) * modulatedFourierMellin m[F] univ hm[F] μ (adelicTheta (F := F) f) c.val := by
  simpa only [globalIdelicMellin_apply] using
    globalIdelicZFunction_eq_canonical_of_vanishing f ((mem_adelePolarSubspace f).2 ⟨hf, hFourier⟩) c.val

end Idelic

local notation "verticalPoint" => (fun (b y : ℝ) ↦ (b : ℂ) + (y : ℂ) * Complex.I)
set_option quotPrecheck false in
local notation "logModule" =>
  (fun (m : _ →ₜ* ℝ≥0ˣ) g ↦ Real.log ((m g).val : ℝ))

/-- Paper: Definition 9.2.1.1(1), p. 404. The logarithmic weight is the sum of the
squared moment multipliers from order zero through order N, times the squared twist.
Deviation: N is the largest order included. The scalar source in (9.2.1.2) uses N − 1. -/
def lineSobolevDensity (b : ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  Real.exp (2 * b * x) * ∑ k ∈ Finset.range (N + 1), x ^ (2 * k)

/-- Paper: Definition 9.2.1.1(1), p. 404. With order zero only, the density
is just the squared twist.
Deviation: Sanity check in logarithmic coordinates. -/
theorem lineSobolevDensity_order_zero (b x : ℝ) :
    lineSobolevDensity b 0 x = Real.exp (2 * b * x) := by
  simp [lineSobolevDensity]

/-- Paper: Definition 9.2.1.1(1), p. 404. The completion is realized as weighted L².
Deviation: The norm combines the squared norms in (9.2.1.2) by summing them. The
maximum order is an explicit parameter and the scalar case uses Lebesgue measure and `id`. -/
abbrev LineSobolev {A : Type*} [MeasurableSpace A] (μ : Measure A) (logNorm : A → ℝ)
    (b : ℝ) (N : ℕ) :=
  Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (lineSobolevDensity b N (logNorm x)))

/-- Paper: Definition 9.2.1.1(1), p. 404. The scalar b-line Sobolev space uses the
moments of order zero through N.
Deviation: (9.2.1.2) prints 0 ≤ k ≤ N − 1. The proof of Theorem 9.2.1.2(1) on p. 405, the
target in Definition 9.2.1.1(2) and Theorem 9.2.1.5, which is the same space for a general
group, all use 0 ≤ k ≤ N. -/
abbrev ScalarLineSobolev (b : ℝ) (N : ℕ) :=
  LineSobolev volume id b N

/-- Paper: Definition 9.2.1.1(1), p. 404. In the scalar model the weighted integral
gives the norm, and the exponential-decay test profiles have dense image.
Deviation: The largest order is N, see `ScalarLineSobolev`. -/
theorem scalarLineSobolev_dense (b : ℝ) (N : ℕ) :
    ∃ j : PositiveRealExponentialDecay univ →L[ℂ] ScalarLineSobolev b N,
      Injective j ∧ DenseRange j ∧
      ∀ f, (j f : ℝ → ℂ) =ᵐ[volume] f.val ∧
        Integrable (fun x ↦ ‖f.val x‖ ^ 2 * lineSobolevDensity b N x) volume ∧
        ‖j f‖ = Real.sqrt (∫ x, ‖f.val x‖ ^ 2 * lineSobolevDensity b N x) := by
  sorry

/-- Paper: Definition 9.2.1.1(2), p. 404. Complete the entire Schwartz–Bergman
space by taking the closure of its derivative traces in a finite product of vertical L² spaces.
Deviation: The abscissas and largest derivative order are explicit. For one abscissa
this is (9.2.1.3) applied directly to the analytic function. The vertical measure is
a parameter, so either the printed or the Plancherel normalization can be used. For other measures the generators are the
Schwartz–Bergman functions whose indicated traces belong to L². -/
def hardySobolevTraceClosure {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ) (ν : Measure ℝ) :
    Submodule ℂ (PiLp 2 (fun _ : ι ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 ν))) :=
  (Submodule.span ℂ {u : PiLp 2 (fun _ : ι ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 ν)) |
    ∃ F : SchwartzBergman (univ : Set ℝ),
    ∀ i (k : Fin (N + 1)), (u i k : ℝ → ℂ) =ᵐ[ν]
      fun y ↦ iteratedDeriv (k : ℕ) F.val (verticalPoint (σ i) y)}).topologicalClosure

/-- Paper: Definition 9.2.1.1(2), p. 404. The model contains the Gaussian's
vertical derivative traces at any selected abscissas.
Deviation: Sanity check for the trace closure, using Lebesgue measure. -/
theorem gaussian_mem_hardySobolevTraceClosure {ι : Type*} [Fintype ι] (σ : ι → ℝ) (N : ℕ) :
    ∃ u : hardySobolevTraceClosure σ N volume,
      ∀ i (k : Fin (N + 1)), (u.val i k : ℝ → ℂ) =ᵐ[volume]
        fun y ↦ iteratedDeriv (k : ℕ) (fun z : ℂ ↦ Complex.exp (z ^ 2))
          (verticalPoint (σ i) y) := by
  let g (z : ℂ) := Complex.exp (z ^ 2)
  let F : SchwartzBergman (univ : Set ℝ) := ⟨g, by
    simpa [g] using gaussian_mem_schwartzBergmanSubmodule (univ : Set ℝ) isOpen_univ⟩
  have hpoly (k : ℕ) : ∃ p : Polynomial ℂ, iteratedDeriv k g = fun z ↦ p.eval z * g z := by
    induction k with
    | zero => exact ⟨1, by simp⟩
    | succ k ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p.derivative + Polynomial.C 2 * Polynomial.X * p, ?_⟩
      rw [iteratedDeriv_succ, hp]
      funext z
      have hg : HasDerivAt g (g z * (2 * z)) z := by
        simpa [g] using ((hasDerivAt_id z).pow 2).cexp
      refine ((p.hasDerivAt z).mul hg).deriv.trans ?_
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
      ring
  -- The vertical trace estimate applies to each monomial weight.
  have hweighted (a : ℝ) (p : Polynomial ℂ) :
      MemLp (fun y ↦ p.eval (verticalPoint a y) * g (verticalPoint a y)) 2 volume := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq =>
      simpa only [Polynomial.eval_add, add_mul, Pi.add_def] using hp.add hq
    | monomial n c =>
      have ht := schwartzBergman_trace_memLp univ ⟨a, mem_univ a⟩ 2 (by norm_num) (by norm_num) n F
      simpa only [Polynomial.eval_monomial, weightedVerticalTrace, F, mul_assoc] using ht.const_mul c
  have htrace (i : ι) (k : Fin (N + 1)) :
      MemLp (fun y ↦ iteratedDeriv (k : ℕ) g (verticalPoint (σ i) y)) 2 volume := by
    obtain ⟨p, hp⟩ := hpoly k
    rw [hp]
    exact hweighted (σ i) p
  let u : PiLp 2 (fun _ : ι ↦ PiLp 2 (fun _ : Fin (N + 1) ↦ Lp ℂ 2 (volume : Measure ℝ))) :=
    WithLp.toLp 2 fun i ↦ WithLp.toLp 2 fun k ↦ (htrace i k).toLp _
  have hu (i : ι) (k : Fin (N + 1)) : (u i k : ℝ → ℂ) =ᵐ[volume]
      fun y ↦ iteratedDeriv (k : ℕ) g (verticalPoint (σ i) y) :=
    (htrace i k).coeFn_toLp
  refine ⟨⟨u, ?_⟩, hu⟩
  exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨F, hu⟩)

/-- Paper: Definition 9.2.1.1(2), p. 404. The scalar analytic space uses
one line and derivatives of order zero through N, with the Plancherel measure `dy/(2π)`.
Deviation: (9.2.1.3) prints the factor `1/(2π)` outside the square root. The proof of
Theorem 9.2.1.2(2) uses the Plancherel measure `dx/(2π)`, which is what makes the Mellin
transform isometric. The derivative is taken directly on the analytic input. The norm squares
and sums the component norms. -/
abbrev ScalarLineHardySobolev (b : ℝ) (N : ℕ) :=
  hardySobolevTraceClosure (fun _ : Unit ↦ b) N
    (ENNReal.ofReal (1 / (2 * Real.pi)) • volume)

/-- Paper: Definition 9.2.1.1(2), p. 404. The zeroth trace of the Gaussian
has the L² norm in (9.2.1.3) with the Plancherel normalization.
Deviation: Sanity check on the space and its vertical measure. -/
theorem scalarLineHardySobolev_gaussian (b : ℝ) (N : ℕ) :
    let F := fun y : ℝ ↦ Complex.exp (verticalPoint b y ^ 2)
    ∃ u : ScalarLineHardySobolev b N,
      (u.val () 0 : ℝ → ℂ) =ᵐ[volume] F ∧
      ‖u.val () 0‖ = Real.sqrt ((1 / (2 * Real.pi)) * ∫ y, ‖F y‖ ^ 2) := by
  let c := ENNReal.ofReal (1 / (2 * Real.pi))
  have hc : 0 < 1 / (2 * Real.pi) := by positivity
  let g : SchwartzBergman (univ : Set ℝ) := ⟨fun z ↦ Complex.exp (z ^ 2), by
    simpa using gaussian_mem_schwartzBergmanSubmodule (univ : Set ℝ) isOpen_univ⟩
  let trace (k : Fin (N + 1)) (y : ℝ) := iteratedDeriv (k : ℕ) g.val (verticalPoint b y)
  obtain ⟨v, hv⟩ := gaussian_mem_hardySobolevTraceClosure (fun _ : Unit ↦ b) N
  have htrace (k : Fin (N + 1)) : MemLp (trace k) 2 (c • volume) :=
    ((Lp.memLp (v.val () k)).ae_eq (hv () k)).smul_measure ENNReal.ofReal_ne_top
  let u := WithLp.toLp 2 fun _ : Unit ↦ WithLp.toLp 2 fun k ↦ (htrace k).toLp (trace k)
  have hu (i : Unit) (k : Fin (N + 1)) : (u i k : ℝ → ℂ) =ᵐ[c • volume] trace k :=
    (htrace k).coeFn_toLp
  refine ⟨⟨u, Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨g, hu⟩)⟩, ?_, ?_⟩
  · simpa only [Measure.ae_ennreal_smul_measure_eq (c := c) (ENNReal.ofReal_pos.mpr hc).ne',
      trace, Fin.val_zero, iteratedDeriv_zero] using hu () 0
  · change ‖(htrace 0).toLp (trace 0)‖ = _
    rw [Lp.norm_toLp, MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top
      (htrace 0), ENNReal.toReal_ofReal (by positivity)]
    have hreal : c.toReal = 1 / (2 * Real.pi) := ENNReal.toReal_ofReal hc.le
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, integral_smul_measure, hreal, smul_eq_mul,
      trace, Fin.val_zero, iteratedDeriv_zero, g, Real.sqrt_eq_rpow, one_div]

/-- Paper: Theorem 9.2.1.2(1), p. 404. On L² the cutoff by a measurable set
is the class of the product with its indicator. -/
def hardySobolevCutoff {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {U : Set A} (hU : MeasurableSet U) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).indicator hU.nullMeasurableSet).toLp (U.indicator (f : A → ℂ))

/-- Paper: Theorem 9.2.1.2(1), p. 404. The cutoff is a continuous linear
idempotent with closed range, and its representative agrees with the pointwise cutoff.
Deviation: State the operator properties for any measurable set in the weighted L² model. -/
theorem hardySobolevCutoff_spec {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {U : Set A} (hU : MeasurableSet U) :
    ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, IsClosed (range P) ∧
      ∀ f, P (P f) = P f ∧ P f = hardySobolevCutoff hU f ∧
        (P f : A → ℂ) =ᵐ[μ] U.indicator f := by
  have hae (f : Lp ℂ 2 μ) : (hardySobolevCutoff hU f : A → ℂ) =ᵐ[μ] U.indicator f :=
    MemLp.coeFn_toLp _
  let L : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ :=
    { toFun := hardySobolevCutoff hU
      map_add' := fun f g ↦ by
        refine Lp.ext ?_
        filter_upwards [hae (f + g), hae f, hae g, Lp.coeFn_add f g,
          Lp.coeFn_add (hardySobolevCutoff hU f) (hardySobolevCutoff hU g)] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ U
        · simp only [Set.indicator_of_mem hx]
          exact h4
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := fun c f ↦ by
        refine Lp.ext ?_
        filter_upwards [hae (c • f), hae f, Lp.coeFn_smul c f,
          Lp.coeFn_smul c (hardySobolevCutoff hU f)] with x h1 h2 h3 h4
        rw [RingHom.id_apply, h1, h4, Pi.smul_apply, h2]
        by_cases hx : x ∈ U <;> simp [hx, h3] }
  have hbound (f : Lp ℂ 2 μ) : ‖L f‖ ≤ 1 * ‖f‖ := by
    rw [one_mul]
    refine Lp.norm_le_norm_of_ae_le ?_
    filter_upwards [hae f] with x hx
    exact hx ▸ norm_indicator_le_norm_self _ _
  obtain ⟨P, hP⟩ : ∃ P : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ, ∀ f, P f = hardySobolevCutoff hU f :=
    ⟨L.mkContinuous 1 hbound, fun _ ↦ rfl⟩
  have hidem (f : Lp ℂ 2 μ) : P (P f) = P f := by
    rw [hP (P f), hP f]
    refine Lp.ext ?_
    filter_upwards [hae (hardySobolevCutoff hU f), hae f] with x h1 h2
    rw [h1]
    by_cases hx : x ∈ U <;> simp [hx, h2]
  refine ⟨P, ?_, fun f ↦ ⟨hidem f, hP f, hP f ▸ hae f⟩⟩
  convert isClosed_eq P.continuous continuous_id using 1
  ext f
  exact ⟨fun ⟨g, hg⟩ ↦ hg ▸ hidem g, fun h ↦ ⟨f, h⟩⟩

/-- Paper: Theorem 9.2.1.2(1), p. 404. The closure of exponential-decay tests
supported strictly above the cutoff is the range of the cutoff projection.
Deviation: Use logarithmic coordinates. -/
theorem scalarLineSobolev_cutoff_closure (a b : ℝ) (_ha : 1 < a) (N : ℕ) :
    closure {u : ScalarLineSobolev b N | ∃ f : PositiveRealExponentialDecay univ,
      tsupport f.val ⊆ Ioi (-Real.log a) ∧ (u : ℝ → ℂ) =ᵐ[volume] f.val} =
    range (hardySobolevCutoff (μ := volume.withDensity fun x ↦
      ENNReal.ofReal (lineSobolevDensity b N x))
      (U := Ici (-Real.log a)) measurableSet_Ici) := by sorry

/-- Paper: Theorem 9.2.1.2(2), p. 404. The Mellin transform extends to an isometric
isomorphism from the b-line Sobolev space onto the b-line Hardy–Sobolev space.
Deviation: Orders 0 through N on both sides and the Plancherel measure `dy/(2π)`, see
`ScalarLineSobolev` and `ScalarLineHardySobolev`. -/
theorem scalarLineSobolev_mellin (b : ℝ) (N : ℕ) :
    ∃ M : ScalarLineSobolev b N ≃ₗᵢ[ℂ] ScalarLineHardySobolev b N,
      ∀ (f : PositiveRealExponentialDecay univ) (u : ScalarLineSobolev b N),
        (u : ℝ → ℂ) =ᵐ[volume] f.val →
        ∀ k : Fin (N + 1), ((M u).val () k : ℝ → ℂ) =ᵐ[volume]
          fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
            (verticalPoint b y) := by sorry

-- TODO(paper-gap): (9.2.1.2) prints orders up to N − 1 and (9.2.1.3) prints 1/(2π)
-- outside the square root; with either as printed Theorem 9.2.1.2(2) is not an isometry.
-- In Theorem 9.2.1.2(3) the Paley–Wiener bound has no stated limiting regime and the
-- printed split square roots fail at nonpositive real parts. The direct bound for a profile
-- supported in [−log a,0] uses the factor (∫_{−log a}^0 exp(2 Re(s) x) dx)^(1/2),
-- with value (log a)^(1/2) at Re(s) = 0.

/-- Paper: Theorem 9.2.1.2(3), p. 405. The top row splits a supported L²
class into its bounded-interval part and its right-hand part.
Deviation: State the top row alone for a measurable logarithmic coordinate with no
mass on the splitting level. The analytic row has the gaps noted above. -/
theorem hardySobolevCutoff_exact {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (x : A → ℝ) (hx : Measurable x) (c : ℝ) (_hc : c ≤ 0)
    (_hzero : μ (x ⁻¹' {0}) = 0) :
    let E := Lp ℂ 2 μ
    let S := fun (U : Set ℝ) ↦ {f : E | (f : A → ℂ) =ᵐ[μ] (x ⁻¹' U).indicator (f : A → ℂ)}
    ∃ (L M R : Submodule ℂ E) (i : L →L[ℂ] M) (p : M →L[ℂ] R),
      (L : Set E) = S (Icc c 0) ∧ (M : Set E) = S (Ici c) ∧ (R : Set E) = S (Ici 0) ∧
      (∀ f, (i f).val = f.val) ∧
      (∀ f, (p f).val = hardySobolevCutoff
        (μ := μ) (hx measurableSet_Ici : MeasurableSet (x ⁻¹' Ici 0)) f.val) ∧
      Injective i ∧ IsClosed (range i) ∧ Exact i p ∧ Surjective p ∧ IsOpenMap p := by
  intro E S
  have key (U : Set ℝ) (hU : MeasurableSet U) :
      ∃ K : Submodule ℂ (Lp ℂ 2 μ), IsClosed (K : Set (Lp ℂ 2 μ)) ∧
        ∀ f : Lp ℂ 2 μ, f ∈ K ↔ (f : A → ℂ) =ᵐ[μ] (x ⁻¹' U).indicator (f : A → ℂ) := by
    obtain ⟨P, -, hP⟩ := hardySobolevCutoff_spec (μ := μ) (hx hU)
    refine ⟨LinearMap.eqLocus (P : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ) LinearMap.id, ?_,
      fun f ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩
    · exact isClosed_eq P.continuous continuous_id
    · have h' : P f = f := h
      have h2 := (hP f).2.2
      rw [h'] at h2
      exact h2
    · exact Lp.ext ((hP f).2.2.trans h.symm)
  obtain ⟨L, hLc, hL⟩ := key (Icc c 0) measurableSet_Icc
  obtain ⟨M, -, hM⟩ := key (Ici c) measurableSet_Ici
  obtain ⟨R, -, hR⟩ := key (Ici 0) measurableSet_Ici
  obtain ⟨P, -, hP⟩ := hardySobolevCutoff_spec (μ := μ) (hx (measurableSet_Ici (a := (0 : ℝ))))
  have hnull : ∀ᵐ a ∂μ, a ∉ x ⁻¹' {0} := measure_eq_zero_iff_ae_notMem.1 _hzero
  have hLM : ∀ f : L, f.val ∈ M := by
    intro f
    refine (hM _).2 ?_
    filter_upwards [(hL f.val).1 f.2] with a ha
    by_cases h : a ∈ x ⁻¹' Ici c
    · exact (Set.indicator_of_mem h _).symm
    · have h2 : a ∉ x ⁻¹' Icc c 0 := fun h' ↦ h (show c ≤ x a ∧ x a ≤ 0 from h').1
      exact ha.trans ((Set.indicator_of_notMem h2 _).trans (Set.indicator_of_notMem h _).symm)
  have hRM : ∀ r : R, r.val ∈ M := by
    intro r
    refine (hM _).2 ?_
    filter_upwards [(hR r.val).1 r.2] with a ha
    by_cases h : a ∈ x ⁻¹' Ici c
    · exact (Set.indicator_of_mem h _).symm
    · have h2 : a ∉ x ⁻¹' Ici 0 := fun h' ↦ h (_hc.trans (show 0 ≤ x a from h'))
      exact ha.trans ((Set.indicator_of_notMem h2 _).trans (Set.indicator_of_notMem h _).symm)
  have hPR : ∀ f : M, P f.val ∈ R := by
    intro f
    refine (hR _).2 ?_
    have h1 := (hP (P f.val)).2.2
    rw [(hP f.val).1] at h1
    exact h1
  obtain ⟨i, hi⟩ : ∃ i : L →L[ℂ] M, ∀ f, (i f).val = f.val :=
    ⟨L.subtypeL.codRestrict M hLM, fun _ ↦ rfl⟩
  obtain ⟨p, hp⟩ : ∃ p : M →L[ℂ] R, ∀ f, (p f).val = P f.val :=
    ⟨(P.comp M.subtypeL).codRestrict R hPR, fun _ ↦ rfl⟩
  obtain ⟨j, hj⟩ : ∃ j : R →L[ℂ] M, ∀ r, (j r).val = r.val :=
    ⟨R.subtypeL.codRestrict M hRM, fun _ ↦ rfl⟩
  have hpj : ∀ r : R, p (j r) = r := fun r ↦ Subtype.ext ((hp _).trans
    ((congrArg (fun g ↦ P g) (hj r)).trans
      (Lp.ext ((hP r.val).2.2.trans ((hR r.val).1 r.2).symm))))
  have hinj : Injective i := fun f g h ↦
    Subtype.ext ((hi f).symm.trans ((congrArg (fun m : M ↦ (m : Lp ℂ 2 μ)) h).trans (hi g)))
  have hrange : IsClosed (range i) := by
    have hr : range i = (fun m : M ↦ (m : Lp ℂ 2 μ)) ⁻¹' (L : Set (Lp ℂ 2 μ)) := by
      ext m
      constructor
      · rintro ⟨f, rfl⟩
        have h1 : (i f).val ∈ L := by
          rw [hi]
          exact f.2
        exact h1
      · intro h
        exact ⟨⟨m.val, h⟩, Subtype.ext (hi _)⟩
    rw [hr]
    exact hLc.preimage continuous_subtype_val
  have hexact : Exact i p := by
    intro y
    constructor
    · intro h0
      have h0' : P y.val = 0 := (hp y).symm.trans (congrArg (fun r : R ↦ (r : Lp ℂ 2 μ)) h0)
      have hz : ((P y.val : Lp ℂ 2 μ) : A → ℂ) =ᵐ[μ] 0 := by
        rw [h0']
        exact Lp.coeFn_zero ℂ 2 μ
      have hyL : y.val ∈ L := by
        refine (hL _).2 ?_
        filter_upwards [(hM y.val).1 y.2, (hP y.val).2.2, hz] with a h1 h2 h3
        by_cases ha : a ∈ x ⁻¹' Icc c 0
        · exact (Set.indicator_of_mem ha _).symm
        · refine Eq.trans ?_ (Set.indicator_of_notMem ha _).symm
          by_cases hc' : a ∈ x ⁻¹' Ici c
          · have h0a : 0 ≤ x a := (le_total 0 (x a)).resolve_right
              fun hle ↦ ha (show x a ∈ Icc c 0 from ⟨hc', hle⟩)
            exact (Set.indicator_of_mem (show a ∈ x ⁻¹' Ici 0 from h0a) _).symm.trans
              (h2.symm.trans h3)
          · exact h1.trans (Set.indicator_of_notMem hc' _)
      exact ⟨⟨y.val, hyL⟩, Subtype.ext (hi _)⟩
    · rintro ⟨f, rfl⟩
      have hPf0 : P f.val = 0 := by
        refine Lp.ext ?_
        filter_upwards [(hL f.val).1 f.2, (hP f.val).2.2, hnull, Lp.coeFn_zero ℂ 2 μ]
          with a h1 h2 h3 h4
        refine h2.trans (Eq.trans ?_ h4.symm)
        by_cases ha : a ∈ x ⁻¹' Ici 0
        · have ha' : a ∉ x ⁻¹' Icc c 0 := fun h ↦
            h3 (show x a = 0 from le_antisymm (show c ≤ x a ∧ x a ≤ 0 from h).2 ha)
          exact (Set.indicator_of_mem ha _).trans (h1.trans (Set.indicator_of_notMem ha' _))
        · exact Set.indicator_of_notMem ha _
      exact Subtype.ext ((hp _).trans ((congrArg (fun g ↦ P g) (hi f)).trans hPf0))
  have hopen : IsOpenMap p := by
    refine IsOpenMap.of_sections fun m ↦ ⟨fun r ↦ m + j (r - p m), ?_, ?_, fun r ↦ ?_⟩
    · have hc : Continuous fun r : R ↦ m + j (r - p m) :=
        continuous_const.add (j.continuous.comp (continuous_id.sub continuous_const))
      exact hc.continuousAt
    · show m + j (p m - p m) = m
      rw [sub_self, map_zero, add_zero]
    · show p (m + j (r - p m)) = r
      rw [map_add, hpj, add_sub_cancel]
  exact ⟨L, M, R, i, p, Set.ext hL, Set.ext hM, Set.ext hR, hi,
    fun f ↦ (hp f).trans (hP f.val).2.1, hinj, hrange, hexact, fun r ↦ ⟨j r, hpj r⟩, hopen⟩

-- TODO(paper-gap): Corollary 9.2.1.3 omits the one-sided support hypothesis used
-- in its proof. The uniform Hardy bound at order N also exceeds the printed
-- source order.

/-- A power of `|x|` times a decaying exponential of `|x|` is integrable. -/
private theorem integrable_abs_pow_mul_exp_neg (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x : ℝ ↦ |x| ^ n * Real.exp (-(δ * |x|))) volume := by
  have hcont : Continuous fun x : ℝ ↦ |x| ^ n * Real.exp (-(δ * |x|)) :=
    (continuous_abs.pow n).mul (Real.continuous_exp.comp (continuous_const.mul continuous_abs).neg)
  refine (integrable_inv_one_add_sq.const_mul
    ((n + 2).factorial * Real.exp δ / δ ^ (n + 2))).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun x ↦ ?_)
  show ‖|x| ^ n * Real.exp (-(δ * |x|))‖ ≤
    (n + 2).factorial * Real.exp δ / δ ^ (n + 2) * (1 + x ^ 2)⁻¹
  have hA : 0 ≤ |x| := abs_nonneg x
  rw [Real.norm_of_nonneg (by positivity), ← div_eq_mul_inv, le_div_iff₀ (by positivity),
    le_div_iff₀ (by positivity)]
  have h := Real.pow_div_factorial_le_exp (x := δ * (1 + |x|)) (by positivity) (n + 2)
  rw [div_le_iff₀ (by positivity)] at h
  have h1 : |x| ^ n * (1 + x ^ 2) ≤ (1 + |x|) ^ (n + 2) := by
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ hA (by linarith) n) (by nlinarith [sq_abs x])
      (by positivity) (by positivity)
  have h2 : δ * (1 + |x|) + -(δ * |x|) = δ := by ring
  calc |x| ^ n * Real.exp (-(δ * |x|)) * (1 + x ^ 2) * δ ^ (n + 2)
      = |x| ^ n * (1 + x ^ 2) * δ ^ (n + 2) * Real.exp (-(δ * |x|)) := by ring
    _ ≤ (1 + |x|) ^ (n + 2) * δ ^ (n + 2) * Real.exp (-(δ * |x|)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by positivity))
          (Real.exp_pos _).le
    _ = (δ * (1 + |x|)) ^ (n + 2) * Real.exp (-(δ * |x|)) := by rw [mul_pow]; ring
    _ ≤ Real.exp (δ * (1 + |x|)) * (n + 2).factorial * Real.exp (-(δ * |x|)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
    _ = (n + 2).factorial * Real.exp δ := by
        rw [mul_right_comm, ← Real.exp_add, h2, mul_comm]

/-- Integration against a kernel whose square is integrable against the reciprocal density
is a continuous functional on a weighted L² space, by the Cauchy–Schwarz inequality. -/
private theorem weightedL2_pairing {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) {w : X → ℂ}
    (hw : AEStronglyMeasurable w ν) (hint : Integrable (fun x ↦ ‖w x‖ ^ 2 * (ρ x)⁻¹) ν) :
    ∃ Λ : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x ↦ f x * w x) ν ∧ Λ f = ∫ x, f x * w x ∂ν := by
  have hdens : Measurable (fun x ↦ ENNReal.ofReal (ρ x)) := hρ.ennreal_ofReal
  have hflt : ∀ᵐ x ∂ν, ENNReal.ofReal (ρ x) < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hbase : ν ≪ ν.withDensity fun x ↦ ENNReal.ofReal (ρ x) :=
    withDensity_absolutelyContinuous' hdens.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  let u : X → ℂ := fun x ↦ (((ρ x)⁻¹ : ℝ) : ℂ) * star (w x)
  have hmeas : AEStronglyMeasurable u (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) :=
    (Complex.measurable_ofReal.comp hρ.inv).aestronglyMeasurable.mul
      (hw.mono_ac (withDensity_absolutelyContinuous _ _)).star
  have hmem : MemLp u 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) := by
    apply (memLp_two_iff_integrable_sq_norm hmeas).2
    apply (integrable_withDensity_iff hdens hflt).2
    refine hint.congr (ae_of_all _ fun x ↦ ?_)
    change ‖w x‖ ^ 2 * (ρ x)⁻¹ =
      ‖(((ρ x)⁻¹ : ℝ) : ℂ) * star (w x)‖ ^ 2 * (ENNReal.ofReal (ρ x)).toReal
    rw [ENNReal.toReal_ofReal (hpos x).le, norm_mul, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos x))]
    calc ‖w x‖ ^ 2 * (ρ x)⁻¹ = ‖w x‖ ^ 2 * (ρ x)⁻¹ * ((ρ x)⁻¹ * ρ x) := by
          rw [inv_mul_cancel₀ (hpos x).ne', mul_one]
      _ = ((ρ x)⁻¹ * ‖w x‖) ^ 2 * ρ x := by ring
  let g := hmem.toLp u
  have hcoe : (g : X → ℂ) =ᵐ[ν] u := hbase.ae_eq hmem.coeFn_toLp
  refine ⟨innerSL ℂ g, fun f ↦ ?_⟩
  have hprod : (fun x ↦ f x * w x) =ᵐ[ν]
      fun x ↦ (ENNReal.ofReal (ρ x)).toReal • inner ℂ (g x) (f x) := by
    filter_upwards [hcoe] with x hx
    have hne : (ρ x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos x).ne'
    have hstar : star (((ρ x)⁻¹ : ℝ) : ℂ) = (((ρ x)⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [hx, ENNReal.toReal_ofReal (hpos x).le, RCLike.inner_apply, starRingEnd_apply]
    change f x * w x = ρ x • (f x * star ((((ρ x)⁻¹ : ℝ) : ℂ) * star (w x)))
    rw [star_mul', hstar, star_star, Complex.real_smul, Complex.ofReal_inv]
    calc f x * w x = (ρ x : ℂ) * (ρ x : ℂ)⁻¹ * (f x * w x) := by
          rw [mul_inv_cancel₀ hne, one_mul]
      _ = (ρ x : ℂ) * (f x * ((ρ x : ℂ)⁻¹ * w x)) := by ring
  refine ⟨((integrable_withDensity_iff_integrable_smul' hdens hflt).1
    (L2.integrable_inner g f)).congr hprod.symm, ?_⟩
  calc innerSL ℂ g f = inner ℂ g f := rfl
    _ = ∫ x, inner ℂ (g x) (f x) ∂(ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) :=
      L2.inner_def g f
    _ = ∫ x, (ENNReal.ofReal (ρ x)).toReal • inner ℂ (g x) (f x) ∂ν :=
      integral_withDensity_eq_integral_toReal_smul hdens hflt _
    _ = ∫ x, f x * w x ∂ν := integral_congr_ae hprod.symm

/-- The moment kernel `x ^ k * exp (z * x)`, cut off to a measurable set on which a
continuous positive density dominates it exponentially, gives a continuous functional on
the weighted L² space of that density. -/
private theorem weightedL2_moment_functional {ρ : ℝ → ℝ} (hρc : Continuous ρ)
    (hpos : ∀ x, 0 < ρ x) (z : ℂ) (k : ℕ) {U : Set ℝ} (hU : MeasurableSet U) {δ K : ℝ}
    (hδ : 0 < δ) (hK : 0 ≤ K)
    (hlow : ∀ x ∈ U, Real.exp (2 * z.re * x + δ * |x|) ≤ K * ρ x) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
        Λ f = ∫ x : ℝ, f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
  have hker : Continuous fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) :=
    (Complex.continuous_ofReal.pow k).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  refine weightedL2_pairing volume hρc.measurable hpos
    (hker.measurable.indicator hU).aestronglyMeasurable ?_
  refine ((integrable_abs_pow_mul_exp_neg (2 * k) hδ).const_mul K).mono'
    (((hker.measurable.indicator hU).norm.pow_const 2).mul
      hρc.measurable.inv).aestronglyMeasurable (Eventually.of_forall fun x ↦ ?_)
  show ‖‖U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x‖ ^ 2 *
      (ρ x)⁻¹‖ ≤ K * (|x| ^ (2 * k) * Real.exp (-(δ * |x|)))
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hpos x).le))]
  by_cases hx : x ∈ U
  · have hre : (z * (x : ℂ)).re = z.re * x := by simp
    rw [Set.indicator_of_mem hx, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      Complex.norm_exp, hre]
    have key : Real.exp (z.re * x) ^ 2 * (ρ x)⁻¹ ≤ K * Real.exp (-(δ * |x|)) := by
      rw [← div_eq_mul_inv, div_le_iff₀ (hpos x)]
      calc Real.exp (z.re * x) ^ 2
          = Real.exp (-(δ * |x|)) * Real.exp (2 * z.re * x + δ * |x|) := by
            rw [← Real.exp_add, sq, ← Real.exp_add]
            congr 1
            ring
        _ ≤ Real.exp (-(δ * |x|)) * (K * ρ x) :=
            mul_le_mul_of_nonneg_left (hlow x hx) (Real.exp_pos _).le
        _ = K * Real.exp (-(δ * |x|)) * ρ x := by ring
    calc (|x| ^ k * Real.exp (z.re * x)) ^ 2 * (ρ x)⁻¹
        = |x| ^ (2 * k) * (Real.exp (z.re * x) ^ 2 * (ρ x)⁻¹) := by ring
      _ ≤ |x| ^ (2 * k) * (K * Real.exp (-(δ * |x|))) :=
          mul_le_mul_of_nonneg_left key (by positivity)
      _ = K * (|x| ^ (2 * k) * Real.exp (-(δ * |x|))) := by ring
  · rw [Set.indicator_of_notMem hx, norm_zero, zero_pow two_ne_zero, zero_mul]
    exact mul_nonneg hK (by positivity)

/-- Differentiation under the integral sign for exponential moments on a measure space: if
every moment of `h` against `exp (σ * ℓ x)` is integrable for `σ` in an open interval, then on
the corresponding vertical strip the integral of `h x * exp (w * ℓ x)` is holomorphic, and its
`k`th derivative is the `k`th moment. -/
private theorem iteratedDeriv_exp_moment_of_measurable {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {h : X → ℂ} {ℓ : X → ℝ} (hℓ : Measurable ℓ) {α β : ℝ}
    (hint : ∀ σ ∈ Ioo α β, ∀ n : ℕ,
      Integrable (fun x ↦ h x * (ℓ x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (ℓ x : ℂ))) μ)
    (k : ℕ) {z : ℂ} (hz : z.re ∈ Ioo α β) :
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ x, h x * Complex.exp (w * (ℓ x : ℂ)) ∂μ) z ∧
      Integrable (fun x ↦ h x * (ℓ x : ℂ) ^ k * Complex.exp (z * (ℓ x : ℂ))) μ ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x, h x * Complex.exp (w * (ℓ x : ℂ)) ∂μ) z =
        ∫ x, h x * (ℓ x : ℂ) ^ k * Complex.exp (z * (ℓ x : ℂ)) ∂μ := by
  let F : ℕ → ℂ → X → ℂ := fun n w x ↦ h x * (ℓ x : ℂ) ^ n * Complex.exp (w * (ℓ x : ℂ))
  have hℓc : Measurable fun x ↦ (ℓ x : ℂ) := Complex.measurable_ofReal.comp hℓ
  have hexpc : ∀ w : ℂ, Measurable fun x ↦ Complex.exp (w * (ℓ x : ℂ)) := fun w ↦
    Complex.measurable_exp.comp (hℓc.const_mul w)
  have hm : AEStronglyMeasurable h μ := by
    refine ((hint z.re hz 0).aestronglyMeasurable.mul
      (hexpc (-(z.re : ℂ))).aestronglyMeasurable).congr (ae_of_all _ fun x ↦ ?_)
    show h x * (ℓ x : ℂ) ^ 0 * Complex.exp ((z.re : ℂ) * (ℓ x : ℂ)) *
      Complex.exp (-(z.re : ℂ) * (ℓ x : ℂ)) = h x
    rw [pow_zero, mul_one, mul_assoc, ← Complex.exp_add, neg_mul, add_neg_cancel,
      Complex.exp_zero, mul_one]
  have hFm : ∀ n w, AEStronglyMeasurable (F n w) μ := fun n w ↦
    (hm.mul (hℓc.pow_const n).aestronglyMeasurable).mul (hexpc w).aestronglyMeasurable
  have hnorm : ∀ n (w : ℂ) (x : X),
      ‖F n w x‖ = ‖h x‖ * |ℓ x| ^ n * Real.exp (w.re * ℓ x) := by
    intro n w x
    have hre : (w * (ℓ x : ℂ)).re = w.re * ℓ x := by simp
    show ‖h x * (ℓ x : ℂ) ^ n * Complex.exp (w * (ℓ x : ℂ))‖ = _
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
      hre]
  have hFi : ∀ n (w : ℂ), w.re ∈ Ioo α β → Integrable (F n w) μ := fun n w hw ↦
    (hint w.re hw n).mono (hFm n w) (ae_of_all _ fun x ↦ le_of_eq (by
      show ‖F n w x‖ = ‖F n (w.re : ℂ) x‖
      rw [hnorm, hnorm, Complex.ofReal_re]))
  have hderiv : ∀ n (w : ℂ), w.re ∈ Ioo α β →
      HasDerivAt (fun w ↦ ∫ x, F n w x ∂μ) (∫ x, F (n + 1) w x ∂μ) w := by
    intro n w hw
    obtain ⟨ε, hε, hεa, hεb⟩ : ∃ ε : ℝ, 0 < ε ∧ α < w.re - ε ∧ w.re + ε < β := by
      have h0 : 0 < min (w.re - α) (β - w.re) := lt_min (sub_pos.2 hw.1) (sub_pos.2 hw.2)
      have h1 := min_le_left (w.re - α) (β - w.re)
      have h2 := min_le_right (w.re - α) (β - w.re)
      exact ⟨min (w.re - α) (β - w.re) / 2, half_pos h0, by linarith, by linarith⟩
    have hlo : ((w.re - ε : ℝ) : ℂ).re ∈ Ioo α β := by
      rw [Complex.ofReal_re]
      exact ⟨hεa, by linarith⟩
    have hhi : ((w.re + ε : ℝ) : ℂ).re ∈ Ioo α β := by
      rw [Complex.ofReal_re]
      exact ⟨by linarith, hεb⟩
    refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w hε)
      (Eventually.of_forall (hFm n)) (hFi n w hw) (hFm (n + 1) w)
      (ae_of_all _ fun x w' hw' ↦ ?_)
      ((hFi (n + 1) _ hlo).norm.add (hFi (n + 1) _ hhi).norm)
      (ae_of_all _ fun x w' _ ↦ ?_)).2
    · show ‖F (n + 1) w' x‖ ≤
        ‖F (n + 1) ((w.re - ε : ℝ) : ℂ) x‖ + ‖F (n + 1) ((w.re + ε : ℝ) : ℂ) x‖
      rw [hnorm, hnorm, hnorm, Complex.ofReal_re, Complex.ofReal_re]
      have h2 : ‖w' - w‖ < ε := by
        rw [← dist_eq_norm]
        exact hw'
      have h1 := (Complex.abs_re_le_norm (w' - w)).trans_lt h2
      rw [Complex.sub_re] at h1
      obtain ⟨hl, hu⟩ := abs_lt.1 h1
      have hexp : Real.exp (w'.re * ℓ x) ≤
          Real.exp ((w.re - ε) * ℓ x) + Real.exp ((w.re + ε) * ℓ x) := by
        rcases le_total 0 (ℓ x) with hx | hx
        · have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ w.re + ε - w'.re) hx
          exact (Real.exp_le_exp.2 (by nlinarith)).trans
            (le_add_of_nonneg_left (Real.exp_pos _).le)
        · have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ w'.re - w.re + ε) (neg_nonneg.2 hx)
          exact (Real.exp_le_exp.2 (by nlinarith)).trans
            (le_add_of_nonneg_right (Real.exp_pos _).le)
      calc ‖h x‖ * |ℓ x| ^ (n + 1) * Real.exp (w'.re * ℓ x)
          ≤ ‖h x‖ * |ℓ x| ^ (n + 1) *
            (Real.exp ((w.re - ε) * ℓ x) + Real.exp ((w.re + ε) * ℓ x)) :=
            mul_le_mul_of_nonneg_left hexp (by positivity)
        _ = _ := mul_add _ _ _
    · exact (((hasDerivAt_id' w').mul_const (ℓ x : ℂ)).cexp.const_mul
        (h x * (ℓ x : ℂ) ^ n)).congr_deriv (by
          show h x * (ℓ x : ℂ) ^ n * (Complex.exp (w' * (ℓ x : ℂ)) * (1 * (ℓ x : ℂ))) =
            h x * (ℓ x : ℂ) ^ (n + 1) * Complex.exp (w' * (ℓ x : ℂ))
          ring)
  have hS : IsOpen {w : ℂ | w.re ∈ Ioo α β} := isOpen_Ioo.preimage Complex.continuous_re
  have hM : (fun w : ℂ ↦ ∫ x, h x * Complex.exp (w * (ℓ x : ℂ)) ∂μ) =
      fun w ↦ ∫ x, F 0 w x ∂μ := by
    funext w
    refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
    show h x * Complex.exp (w * (ℓ x : ℂ)) = h x * (ℓ x : ℂ) ^ 0 * Complex.exp (w * (ℓ x : ℂ))
    rw [pow_zero, mul_one]
  have hiter : ∀ n (w : ℂ), w.re ∈ Ioo α β →
      iteratedDeriv n (fun w ↦ ∫ x, F 0 w x ∂μ) w = ∫ x, F n w x ∂μ := by
    intro n
    induction n with
    | zero =>
      intro w _
      rw [iteratedDeriv_zero]
    | succ n ih =>
      intro w hw
      have hev : iteratedDeriv n (fun w ↦ ∫ x, F 0 w x ∂μ) =ᶠ[𝓝 w]
          fun w ↦ ∫ x, F n w x ∂μ :=
        (hS.eventually_mem hw).mono fun w' hw' ↦ ih w' hw'
      rw [iteratedDeriv_succ, hev.deriv_eq]
      exact (hderiv n w hw).deriv
  rw [hM]
  exact ⟨DifferentiableOn.analyticAt (s := {w : ℂ | w.re ∈ Ioo α β}) (fun w hw ↦
    (hderiv 0 w hw).differentiableAt.differentiableWithinAt) (hS.mem_nhds hz),
    hFi k z hz, hiter k z hz⟩

/-- Differentiation under the integral sign for exponential moments on the real line with
Lebesgue measure. -/
private theorem iteratedDeriv_exp_moment {h : ℝ → ℂ} {α β : ℝ}
    (hint : ∀ σ ∈ Ioo α β, ∀ n : ℕ,
      Integrable (fun x : ℝ ↦ h x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume)
    (k : ℕ) {z : ℂ} (hz : z.re ∈ Ioo α β) :
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ x : ℝ, h x * Complex.exp (w * (x : ℂ))) z ∧
      Integrable (fun x : ℝ ↦ h x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x : ℝ, h x * Complex.exp (w * (x : ℂ))) z =
        ∫ x : ℝ, h x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) :=
  iteratedDeriv_exp_moment_of_measurable measurable_id hint k hz
/-- The line density dominates its exponential factor. -/
private theorem exp_le_lineSobolevDensity (b : ℝ) (N : ℕ) (x : ℝ) :
    Real.exp (2 * b * x) ≤ lineSobolevDensity b N x := by
  unfold lineSobolevDensity
  refine le_mul_of_one_le_right (Real.exp_pos _).le ?_
  calc (1 : ℝ) = x ^ (2 * 0) := by rw [mul_zero, pow_zero]
    _ ≤ ∑ k ∈ Finset.range (N + 1), x ^ (2 * k) :=
      Finset.single_le_sum (f := fun k ↦ x ^ (2 * k))
        (fun k _ ↦ (even_two_mul k).pow_nonneg x) (Finset.mem_range.2 N.succ_pos)

/-- The line density is continuous. -/
private theorem continuous_lineSobolevDensity (b : ℝ) (N : ℕ) :
    Continuous (lineSobolevDensity b N) := by
  show Continuous fun x : ℝ ↦ Real.exp (2 * b * x) * ∑ k ∈ Finset.range (N + 1), x ^ (2 * k)
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (continuous_finsetSum _ fun k _ ↦ continuous_id.pow (2 * k))

/-- To the left of the line, every moment kernel cut off above a point gives a continuous
functional on the line space. -/
private theorem lineSobolev_cutoff_moment_functional (a b : ℝ) (ha : 1 < a) (N k : ℕ)
    (z : ℂ) (hz : z.re < b) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (lineSobolevDensity b N x)) →L[ℂ] ℂ,
      ∀ f : Lp ℂ 2 (volume.withDensity fun x ↦ ENNReal.ofReal (lineSobolevDensity b N x)),
        Integrable (fun x : ℝ ↦ (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  have hlogA : 0 < Real.log a := Real.log_pos ha
  have hbz : 0 < b - z.re := sub_pos.2 hz
  obtain ⟨Λ, hΛ⟩ := weightedL2_moment_functional (continuous_lineSobolevDensity b N)
    (fun x ↦ (Real.exp_pos _).trans_le (exp_le_lineSobolevDensity b N x)) z k
    (measurableSet_Ici (a := -Real.log a)) (δ := 2 * (b - z.re))
    (K := Real.exp (4 * (b - z.re) * Real.log a)) (mul_pos two_pos hbz) (Real.exp_pos _).le
    fun x hx ↦ by
      have hx' : -Real.log a ≤ x := hx
      have hle : 2 * z.re * x + 2 * (b - z.re) * |x| ≤
          4 * (b - z.re) * Real.log a + 2 * b * x := by
        rcases le_total 0 x with h0 | h0
        · rw [abs_of_nonneg h0]
          nlinarith [mul_pos hbz hlogA]
        · rw [abs_of_nonpos h0]
          nlinarith [mul_nonneg hbz.le (by linarith : 0 ≤ Real.log a + x)]
      calc Real.exp (2 * z.re * x + 2 * (b - z.re) * |x|)
          ≤ Real.exp (4 * (b - z.re) * Real.log a + 2 * b * x) := Real.exp_le_exp.2 hle
        _ = Real.exp (4 * (b - z.re) * Real.log a) * Real.exp (2 * b * x) := Real.exp_add _ _
        _ ≤ Real.exp (4 * (b - z.re) * Real.log a) * lineSobolevDensity b N x :=
          mul_le_mul_of_nonneg_left (exp_le_lineSobolevDensity b N x) (Real.exp_pos _).le
  refine ⟨Λ, fun f ↦ ?_⟩
  have hfun : (fun x : ℝ ↦ (Ici (-Real.log a)).indicator (⇑f) x *
      (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) = fun x : ℝ ↦ f x *
      (Ici (-Real.log a)).indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
    funext x
    by_cases hx : x ∈ Ici (-Real.log a)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_assoc]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, zero_mul, mul_zero]
  rw [hfun]
  exact hΛ f

/-- The Mellin transform of a profile in the logarithmic coordinate is its two-sided
exponential integral. -/
private theorem mellin_comp_log_eq (h : ℝ → ℂ) (s : ℂ) :
    mellin (fun t ↦ h (Real.log t)) s = ∫ x : ℝ, h x * Complex.exp (s * (x : ℂ)) := by
  rw [mellin, ← integral_comp_exp]
  refine integral_congr_ae (ae_of_all _ fun y ↦ ?_)
  show Real.exp y • (((Real.exp y : ℝ) : ℂ) ^ (s - 1) • h (Real.log (Real.exp y))) =
    h y * Complex.exp (s * (y : ℂ))
  have hexp : (y : ℂ) + (y : ℂ) * (s - 1) = s * (y : ℂ) := by ring
  rw [Real.log_exp, Complex.real_smul, smul_eq_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 (Real.exp_pos y).ne'),
    ← Complex.ofReal_log (Real.exp_pos y).le, Real.log_exp, Complex.ofReal_exp, ← mul_assoc,
    ← Complex.exp_add, hexp]
  exact mul_comm _ _

/-- Every exponential moment of an exponential-decay profile is integrable. -/
private theorem integrable_logExponentialDecay_moment (f : logExponentialDecaySubmodule univ)
    (σ : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ ↦ f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume := by
  have hfun : (fun x : ℝ ↦ f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) =
      fun x : ℝ ↦ (x : ℂ) ^ n * logExponentialDecayTwist univ ⟨σ, mem_univ σ⟩ f x := by
    funext x
    rw [logExponentialDecayTwist_apply]
    show f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ)) =
      (x : ℂ) ^ n * (((Real.exp (σ * x) : ℝ) : ℂ) * f.val x)
    rw [Complex.ofReal_exp, Complex.ofReal_mul]
    ring
  rw [hfun]
  refine (SchwartzMap.integrable_pow_mul volume
    (logExponentialDecayTwist univ ⟨σ, mem_univ σ⟩ f) n).mono'
    ((Complex.continuous_ofReal.pow n).mul (SchwartzMap.continuous _)).aestronglyMeasurable
    (ae_of_all _ fun x ↦ le_of_eq ?_)
  rw [norm_mul, norm_pow, Complex.norm_real]

/-- Paper: Corollary 9.2.1.4, p. 407. In the left half-plane each indicated derivative
evaluation is bounded on the part supported above the cutoff and is given by the moment integral.
Deviation: State the continuous functional on the supported source, where it extends the
derivative of the test Mellin transform. The normalization uses the corrected isometry in `scalarLineSobolev_mellin`. -/
theorem scalarLineSobolev_cutoff_eval (a b : ℝ) (_ha : 1 < a)
    (N k : ℕ) (_hk : k < N) (z : ℂ) (_hz : z.re < b) :
    ∃ Λ : ScalarLineSobolev b N →L[ℂ] ℂ,
      (∀ (f : ScalarLineSobolev b N), Integrable (fun x : ℝ ↦ (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, (Ici (-Real.log a)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) ∧
      ∀ (f : PositiveRealExponentialDecay univ) (u : ScalarLineSobolev b N),
        tsupport f.val ⊆ Ioi (-Real.log a) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z := by
  obtain ⟨Λ, hΛ⟩ := lineSobolev_cutoff_moment_functional a b _ha N k z _hz
  refine ⟨Λ, hΛ, fun f u hsupp hu ↦ ?_⟩
  have hint : ∀ σ ∈ Ioo (z.re - 1) (z.re + 1), ∀ n : ℕ, Integrable
      (fun x : ℝ ↦ f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume :=
    fun σ _ n ↦ integrable_logExponentialDecay_moment f σ n
  have hmel : mellin (fun t ↦ f.val (Real.log t)) =
      fun w : ℂ ↦ ∫ x : ℝ, f.val x * Complex.exp (w * (x : ℂ)) :=
    funext fun w ↦ mellin_comp_log_eq f.val w
  rw [hmel, (iteratedDeriv_exp_moment hint k ⟨by linarith, by linarith⟩).2.2]
  refine (hΛ u).2.trans (integral_congr_ae ?_)
  filter_upwards [hu] with x hx
  by_cases hmem : x ∈ Ici (-Real.log a)
  · rw [Set.indicator_of_mem hmem, hx]
  · have h0 : f.val x = 0 :=
      image_eq_zero_of_notMem_tsupport fun h ↦ hmem (Ioi_subset_Ici_self (hsupp h))
    rw [Set.indicator_of_notMem hmem, h0]

/-- Paper: Corollary 9.2.1.4, p. 407. The cutoff Mellin integral is holomorphic to
the left of the line and has the stated derivatives for every completed source class.
Deviation: As in `scalarLineSobolev_cutoff_eval`, apply the indicator to the source. -/
theorem scalarLineSobolev_cutoff_iteratedDeriv_mellin (a b : ℝ) (_ha : 1 < a)
    (N k : ℕ) (_hk : k < N) (f : ScalarLineSobolev b N) (z : ℂ) (_hz : z.re < b) :
    let u := (Ici (-Real.log a)).indicator (f : ℝ → ℂ)
    let M := fun w : ℂ ↦ ∫ x : ℝ, u x * Complex.exp (w * (x : ℂ))
    AnalyticAt ℂ M z ∧ iteratedDeriv k M z =
      ∫ x : ℝ, u x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  intro u M
  have h := iteratedDeriv_exp_moment (h := u) (α := z.re - 1) (β := b) (fun σ hσ n ↦ by
    obtain ⟨_, hΛ⟩ := lineSobolev_cutoff_moment_functional a b _ha N n (σ : ℂ)
      (by rw [Complex.ofReal_re]; exact hσ.2)
    exact (hΛ f).1) k ⟨by linarith, _hz⟩
  exact ⟨h.1, h.2.2⟩

/-- Below the abscissa `b`, the squared moment kernel divided by a number that dominates
`exp (2 * b * x)` decays exponentially on a half-line that is bounded below. -/
private theorem sq_moment_div_le {b σ L : ℝ} (hσ : σ < b) (hL : 0 ≤ L) (k : ℕ) {x r : ℝ}
    (hx : -L ≤ x) (hr : Real.exp (2 * b * x) ≤ r) :
    (|x| ^ k * Real.exp (σ * x)) ^ 2 * r⁻¹ ≤
      ((2 * k).factorial : ℝ) / (b - σ) ^ (2 * k) * Real.exp (2 * (b - σ) * L) *
        Real.exp (-((b - σ) * x)) := by
  have hη : 0 < b - σ := sub_pos.2 hσ
  have hrpos : 0 < r := (Real.exp_pos _).trans_le hr
  have hinv : r⁻¹ ≤ Real.exp (-(2 * b * x)) := by
    rw [Real.exp_neg]
    exact inv_anti₀ (Real.exp_pos _) hr
  have hfact : ((b - σ) * |x|) ^ (2 * k) ≤
      Real.exp ((b - σ) * |x|) * ((2 * k).factorial : ℝ) :=
    (div_le_iff₀ (Nat.cast_pos.2 (Nat.factorial_pos _))).1
      (Real.pow_div_factorial_le_exp _ (mul_nonneg hη.le (abs_nonneg x)) (2 * k))
  have hηk : 0 < (b - σ) ^ (2 * k) := pow_pos hη _
  have habs : |x| ^ (2 * k) ≤
      ((2 * k).factorial : ℝ) / (b - σ) ^ (2 * k) * Real.exp ((b - σ) * |x|) := by
    rw [mul_pow] at hfact
    rw [div_mul_eq_mul_div, le_div_iff₀ hηk]
    linarith
  have habsle : |x| ≤ x + 2 * L := abs_le.2 ⟨by linarith, by linarith⟩
  have hexp : Real.exp ((b - σ) * |x|) ≤ Real.exp ((b - σ) * (x + 2 * L)) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left habsle hη.le)
  have he : Real.exp (σ * x) ^ 2 = Real.exp (2 * σ * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hcomb : Real.exp ((b - σ) * (x + 2 * L)) *
      (Real.exp (2 * σ * x) * Real.exp (-(2 * b * x))) =
      Real.exp (2 * (b - σ) * L) * Real.exp (-((b - σ) * x)) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (|x| ^ k * Real.exp (σ * x)) ^ 2 * r⁻¹
      = |x| ^ (2 * k) * (Real.exp (2 * σ * x) * r⁻¹) := by
        rw [mul_pow, he, ← pow_mul, mul_comm k 2, mul_assoc]
    _ ≤ ((2 * k).factorial : ℝ) / (b - σ) ^ (2 * k) * Real.exp ((b - σ) * (x + 2 * L)) *
          (Real.exp (2 * σ * x) * Real.exp (-(2 * b * x))) :=
        mul_le_mul (habs.trans (mul_le_mul_of_nonneg_left hexp (by positivity)))
          (mul_le_mul_of_nonneg_left hinv (Real.exp_pos _).le)
          (mul_nonneg (Real.exp_pos _).le (inv_nonneg.2 hrpos.le)) (by positivity)
    _ = ((2 * k).factorial : ℝ) / (b - σ) ^ (2 * k) * Real.exp (2 * (b - σ) * L) *
          Real.exp (-((b - σ) * x)) := by
        rw [mul_assoc, hcomb]
        exact (mul_assoc _ _ _).symm

/-- The norm twist of a quasi-character is the quasi-character times the exponential of the
logarithmic module. -/
private theorem quasiCharacterNormTwist_eq_exp {G : Type*} [CommGroup G] [TopologicalSpace G]
    (m : G →ₜ* ℝ≥0ˣ) (χ : QuasiCharacter G) (w : ℂ) (g : G) :
    quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g =
      χ g * Complex.exp (w * (logModule m g : ℂ)) := by
  have hpos : 0 < ((m g).val : ℝ) := NNReal.coe_pos.mpr (pos_of_ne_zero (m g).ne_zero)
  change χ g * ((((m g : ℝ≥0) : ℝ) : ℂ)) ^ w =
    χ g * Complex.exp (w * (Real.log ((m g).val : ℝ) : ℂ))
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.2 hpos.ne'),
    ← Complex.ofReal_log hpos.le, mul_comm w]

/-- Differentiation under the integral sign for the norm twists of a quasi-character: if
every logarithmic moment against the real twists in an open interval is integrable, then the
twisted integral is holomorphic on the strip, and its `k`th derivative is the `k`th moment. -/
private theorem iteratedDeriv_normTwist_moment {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G)
    (χ : QuasiCharacter G) {u : G → ℂ} {α β : ℝ}
    (hint : ∀ σ ∈ Ioo α β, ∀ n : ℕ, Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ)
    (k : ℕ) {z : ℂ} (hz : z.re ∈ Ioo α β) :
    AnalyticAt ℂ (fun w : ℂ ↦
        ∫ g, u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ) z ∧
      Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ k *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) μ ∧
      iteratedDeriv k (fun w : ℂ ↦
          ∫ g, u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ) z =
        ∫ g, u g * (logModule m g : ℂ) ^ k *
          quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g ∂μ := by
  have hlog : Measurable (fun g ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable.log
  have hmom (n : ℕ) (w : ℂ) : (fun g ↦ u g * (logModule m g : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g) =
      fun g ↦ u g * χ g * (logModule m g : ℂ) ^ n * Complex.exp (w * (logModule m g : ℂ)) := by
    funext g
    rw [quasiCharacterNormTwist_eq_exp]
    ring
  have hM : (fun w : ℂ ↦
      ∫ g, u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ) =
      fun w ↦ ∫ g, u g * χ g * Complex.exp (w * (logModule m g : ℂ)) ∂μ := by
    funext w
    refine integral_congr_ae (ae_of_all _ fun g ↦ ?_)
    show u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g = _
    rw [quasiCharacterNormTwist_eq_exp, ← mul_assoc]
  have key := iteratedDeriv_exp_moment_of_measurable (μ := μ) (h := fun g ↦ u g * χ g) hlog
    (fun σ hσ n ↦ (hmom n (σ : ℂ)) ▸ hint σ hσ n) k hz
  rw [hM, hmom k z]
  exact key

section ModulatedLine

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ)

/-- For a Haar measure, a decaying exponential of the logarithmic module is integrable on
the part of the group where the logarithmic module is bounded below: translation by an
element of nontrivial module moves one compact band onto the next. -/
private theorem integrableOn_exp_neg_logModule (hm : IsModulation m) (μ : Measure G)
    [μ.IsHaarMeasure] {η : ℝ} (hη : 0 < η) (c : ℝ) :
    IntegrableOn (fun g ↦ Real.exp (-(η * logModule m g))) (logModule m ⁻¹' Ici c) μ := by
  let f (g : G) := Real.log ((m g).val : ℝ)
  have hpos (g : G) : 0 < ((m g).val : ℝ) :=
    NNReal.coe_pos.mpr (pos_of_ne_zero (m g).ne_zero)
  have hmul (g h : G) : f (g * h) = f g + f h := by
    simp only [f, map_mul, Units.val_mul, NNReal.coe_mul]
    exact Real.log_mul (hpos g).ne' (hpos h).ne'
  have hone : f 1 = 0 := by simp [f]
  have hproper : IsProperMap f := by
    let e : ℝ≥0ˣ ≃ₜ ℝ :=
      (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
    have he : (e ∘ m) = f := funext fun g ↦ (Real.log_of_pos (hpos g)).symm
    exact he ▸ e.isProperMap.comp hm.1
  have hfm : Measurable f := hproper.continuous.measurable
  obtain ⟨u, hu⟩ : ∃ u : G, 0 < f u := by
    obtain ⟨g, hg⟩ := hm.2
    have hn : f g ≠ 0 := by
      intro hz
      apply hg
      apply Units.ext
      apply NNReal.eq
      change ((m g).val : ℝ) = 1
      calc ((m g).val : ℝ) = Real.exp (f g) := (Real.exp_log (hpos g)).symm
        _ = 1 := by rw [hz, Real.exp_zero]
    rcases hn.lt_or_gt with h | h
    · refine ⟨g⁻¹, ?_⟩
      have hsum := hmul g⁻¹ g
      rw [inv_mul_cancel, hone] at hsum
      linarith
    · exact ⟨g, h⟩
  have hpow (j : ℕ) (g : G) : f (u ^ j * g) = j * f u + f g := by
    induction j with
    | zero => simp
    | succ n ih =>
      rw [pow_succ', mul_assoc, hmul, ih]
      push_cast
      ring
  let B (j : ℕ) : Set G := f ⁻¹' Icc (c + j * f u) (c + (j + 1) * f u)
  have hB0 : μ (f ⁻¹' Icc c (c + f u)) < ⊤ :=
    (hproper.isCompact_preimage isCompact_Icc).measure_lt_top
  have hBj (j : ℕ) : μ (B j) = μ (f ⁻¹' Icc c (c + f u)) := by
    rw [← measure_preimage_mul μ (u ^ j) (B j)]
    congr 1
    ext g
    simp only [B, mem_preimage, mem_Icc, hpow]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  have hcover : f ⁻¹' Ici c ⊆ ⋃ j, B j := by
    intro g hg
    have hg' : c ≤ f g := hg
    have h0 : 0 ≤ (f g - c) / f u := div_nonneg (sub_nonneg.2 hg') hu.le
    have h1 := Nat.floor_le h0
    have h2 := Nat.lt_floor_add_one ((f g - c) / f u)
    rw [le_div_iff₀ hu] at h1
    rw [div_lt_iff₀ hu] at h2
    have hmem : f g ∈ Icc (c + (⌊(f g - c) / f u⌋₊ : ℝ) * f u)
        (c + ((⌊(f g - c) / f u⌋₊ : ℝ) + 1) * f u) := ⟨by linarith, by linarith⟩
    exact mem_iUnion.2 ⟨_, hmem⟩
  have hr : Real.exp (-(η * f u)) < 1 :=
    Real.exp_lt_one_iff.2 (neg_lt_zero.2 (mul_pos hη hu))
  have hsum : Summable fun j : ℕ ↦ Real.exp (-(η * (c + j * f u))) := by
    refine ((summable_geometric_of_lt_one (Real.exp_pos _).le hr).mul_left
      (Real.exp (-(η * c)))).congr fun j ↦ ?_
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hfin : ∫⁻ g in f ⁻¹' Ici c, ENNReal.ofReal (Real.exp (-(η * f g))) ∂μ < ⊤ :=
    calc ∫⁻ g in f ⁻¹' Ici c, ENNReal.ofReal (Real.exp (-(η * f g))) ∂μ
        ≤ ∫⁻ g in ⋃ j, B j, ENNReal.ofReal (Real.exp (-(η * f g))) ∂μ :=
          lintegral_mono_set hcover
      _ ≤ ∑' j, ∫⁻ g in B j, ENNReal.ofReal (Real.exp (-(η * f g))) ∂μ :=
          lintegral_iUnion_le B _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (Real.exp (-(η * (c + j * f u)))) *
            μ (f ⁻¹' Icc c (c + f u)) := by
          refine tsum_le_tsum fun j ↦ ?_
          rw [← hBj j, ← setLIntegral_const]
          refine setLIntegral_mono' (hfm measurableSet_Icc) fun g hg ↦ ?_
          exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2
            (neg_le_neg (mul_le_mul_of_nonneg_left hg.1 hη.le)))
      _ < ⊤ := by
          rw [ENNReal.tsum_mul_right]
          exact ENNReal.mul_lt_top hsum.tsum_ofReal_ne_top.lt_top hB0
  have hint : Integrable (fun g ↦ Real.exp (-(η * f g))) (μ.restrict (f ⁻¹' Ici c)) :=
    ⟨(Real.measurable_exp.comp (hfm.const_mul η).neg).aestronglyMeasurable,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun g ↦ (Real.exp_pos _).le)).2 hfin⟩
  exact hint

/-- Above a cutoff of the logarithmic module, the moment kernel of a unitary quasi-character
twisted to an abscissa below `b` gives a continuous functional on the weighted L² space of a
Haar measure, for every density that dominates `exp (2 * b * x)`. -/
private theorem modulated_cutoff_moment_functional (hm : IsModulation m) (μ : Measure G)
    [μ.IsHaarMeasure] {ρ : ℝ → ℝ} (hρ : Measurable ρ) {b : ℝ}
    (hρge : ∀ x, Real.exp (2 * b * x) ≤ ρ x) {A : ℝ} (hA : 1 < A) (z : ℂ) (hz : z.re < b)
    (k : ℕ) (χ : QuasiCharacter G) (hχ : ∀ g, ‖χ g‖ = 1) :
    ∃ Λ : Lp ℂ 2 (μ.withDensity fun g ↦ ENNReal.ofReal (ρ (logModule m g))) →L[ℂ] ℂ,
      ∀ f : Lp ℂ 2 (μ.withDensity fun g ↦ ENNReal.ofReal (ρ (logModule m g))),
        Integrable (fun g ↦ (logModule m ⁻¹' Ici (-Real.log A)).indicator (⇑f) g *
          (logModule m g : ℂ) ^ k *
          quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) μ ∧
        Λ f = ∫ g, (logModule m ⁻¹' Ici (-Real.log A)).indicator (⇑f) g *
          (logModule m g : ℂ) ^ k *
          quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g ∂μ := by
  have hρpos (x : ℝ) : 0 < ρ x := (Real.exp_pos _).trans_le (hρge x)
  have hlog : Measurable (fun g ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable.log
  have hρm : Measurable fun g ↦ ρ (logModule m g) := hρ.comp hlog
  have hU : MeasurableSet (logModule m ⁻¹' Ici (-Real.log A)) := hlog measurableSet_Ici
  have hker : Measurable fun g ↦ (logModule m g : ℂ) ^ k *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g :=
    ((Complex.measurable_ofReal.comp hlog).pow_const k).mul (map_continuous _).measurable
  have hη : 0 < b - z.re := sub_pos.2 hz
  have hint : Integrable (fun g ↦ ‖(logModule m ⁻¹' Ici (-Real.log A)).indicator
      (fun g ↦ (logModule m g : ℂ) ^ k *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) g‖ ^ 2 *
      (ρ (logModule m g))⁻¹) μ := by
    refine ((integrable_indicator_iff hU).2 (Integrable.const_mul
      (integrableOn_exp_neg_logModule m hm μ hη (-Real.log A))
      (((2 * k).factorial : ℝ) / (b - z.re) ^ (2 * k) *
        Real.exp (2 * (b - z.re) * Real.log A)))).mono'
      (((hker.indicator hU).norm.pow_const 2).mul hρm.inv).aestronglyMeasurable
      (Eventually.of_forall fun g ↦ ?_)
    beta_reduce
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 (hρpos _).le))]
    by_cases hg : g ∈ logModule m ⁻¹' Ici (-Real.log A)
    · have hc : ‖quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g‖ =
          Real.exp (z.re * logModule m g) := by
        rw [quasiCharacterNormTwist_eq_exp, norm_mul, hχ g, one_mul, Complex.norm_exp]
        simp
      rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, norm_mul, norm_pow,
        Complex.norm_real, Real.norm_eq_abs, hc]
      exact sq_moment_div_le hz (Real.log_pos hA).le k
        (show -Real.log A ≤ logModule m g from hg) (hρge _)
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, norm_zero]
      simp
  obtain ⟨Λ, hΛ⟩ := weightedL2_pairing μ hρm (fun g ↦ hρpos _)
    (hker.indicator hU).aestronglyMeasurable hint
  refine ⟨Λ, fun f ↦ ?_⟩
  have hfun : (fun g ↦ (logModule m ⁻¹' Ici (-Real.log A)).indicator (⇑f) g *
      (logModule m g : ℂ) ^ k * quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) =
      fun g ↦ f g * (logModule m ⁻¹' Ici (-Real.log A)).indicator (fun g ↦
        (logModule m g : ℂ) ^ k *
          quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) g := by
    funext g
    by_cases hg : g ∈ logModule m ⁻¹' Ici (-Real.log A)
    · rw [Set.indicator_of_mem hg, Set.indicator_of_mem hg, mul_assoc]
    · rw [Set.indicator_of_notMem hg, Set.indicator_of_notMem hg, zero_mul, zero_mul, mul_zero]
  rw [hfun]
  exact hΛ f

/-- Over the full exponent line, the Fourier–Mellin integral is the integral against the
quasi-character. -/
private theorem modulatedFourierMellin_univ (hm : IsModulation m) (μ : Measure G)
    (f : G → ℂ) (c : QuasiCharacter G) :
    modulatedFourierMellin m univ hm μ f c = ∫ g, f g * c g ∂μ := by
  unfold modulatedFourierMellin
  rw [Set.indicator_of_mem]
  exact mem_univ (quasiCharacterAbscissa m.toMonoidHom hm.1 hm.2 c)

/-- Paper: Theorem 9.2.1.5(1), p. 408. With canonical Haar measure, the
exponential-decay tests complete to the weighted L² on the group.
Deviation: The squared norm sums the squared moments through order N in (9.2.1.19). -/
theorem modulatedLineSobolev_dense (hm : IsModulation m) (_hms : Surjective m)
    (b : ℝ) (N : ℕ) :
    let μ := canonicalModulatedHaar m hm
    ∃ j : ModulatedExponentialDecay m univ →L[ℂ] LineSobolev μ (logModule m) b N,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : G → ℂ) =ᵐ[μ] f.val := by sorry

/-- Paper: Theorem 9.2.1.5(1), p. 408. On a split modulated group the closed
cutoff range is the closure of the tests with support strictly above the cutoff.
Deviation: The section to all positive reals in the paper entails surjectivity. -/
theorem modulatedLineSobolev_cutoff_closure (hm : IsModulation m) (_hms : Surjective m)
    (a b : ℝ) (_ha : 1 < a) (N : ℕ) :
    let μ := canonicalModulatedHaar m hm
    closure {u : LineSobolev μ (logModule m) b N |
      ∃ f : ModulatedExponentialDecay m univ,
        tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log a) ∧
          (u : G → ℂ) =ᵐ[μ] f.val} =
      {u : LineSobolev μ (logModule m) b N |
        (u : G → ℂ) =ᵐ[μ] ((logModule m) ⁻¹' Ici (-Real.log a)).indicator (u : G → ℂ)} := by sorry

/-- Paper: Theorem 9.2.1.5(2), p. 408. In split coordinates the Hilbert tensor
extension takes an elementary product to the kernel factor tensored with its scalar
vertical derivative traces.
Deviation: The kernel L² stays in the physical coordinates of the displayed target.
The source includes order N as printed in (9.2.1.19). The vertical measure is
`dy/(2π)` and both Hilbert norms sum the squared norms through order N. -/
theorem modulatedLineSobolev_mellin (hm : IsModulation m)
    (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (a b : ℝ) (_ha : 1 < a) (N : ℕ) :
    let μ := canonicalModulatedHaar m hm
    let ν : Measure ℝ := ENNReal.ofReal (1 / (2 * Real.pi)) • volume
    let H := ScalarLineHardySobolev b N
    ∃ M : LineSobolev μ (logModule m) b N ≃ₗᵢ[ℂ]
        UniformSpace.Completion (Lp ℂ 2 μ₁ ⊗[ℂ] H),
      ∀ (g : Lp ℂ 2 μ₁) (f : PositiveRealExponentialDecay univ)
        (u : LineSobolev μ (logModule m) b N),
        (fun p : m.toMonoidHom.ker × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[
          μ₁.prod positiveRealHaar] (fun p ↦ g p.1 * f.val (Real.log (p.2.val : ℝ))) →
        ∃ v : H, (∀ k : Fin (N + 1), (v.val () k : ℝ → ℂ) =ᵐ[ν]
            fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
              (verticalPoint b y)) ∧ M u = ↑(g ⊗ₜ[ℂ] v) := by sorry

-- The coefficient only uses the probability measure on the kernel. Keep the ambient hypotheses.
set_option linter.unusedSectionVars false in
/-- Paper: Theorem 9.2.1.5(2), p. 408, and Equation (9.2.1.25), p. 409.
Taking the isotype coefficient of a line Mellin tensor multiplies the scalar trace
by the kernel Fourier coefficient at the inverse character, as in (D.3.3.14). -/
theorem modulatedLineSobolev_mellin_isotype
    [MeasurableSpace m.toMonoidHom.ker] [BorelSpace m.toMonoidHom.ker]
    (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (b : ℝ) (N : ℕ) (ω : PontryaginDual m.toMonoidHom.ker) :
    let H := ScalarLineHardySobolev b N
    ∃ coefficient : UniformSpace.Completion (Lp ℂ 2 μ₁ ⊗[ℂ] H) →L[ℂ] H,
      ∀ (g : Lp ℂ 2 μ₁) (v : H),
        coefficient ↑(g ⊗ₜ[ℂ] v) = lcaFourier μ₁ g ω⁻¹ • v := by
  intro H
  let : IsProbabilityMeasure μ₁ := ⟨_hμ₁⟩
  let ψ (x : m.toMonoidHom.ker) : ℂ := (ω⁻¹ x : Circle)
  have hψ : MemLp ψ 2 μ₁ := MemLp.of_bound
    (continuous_subtype_val.comp (ω⁻¹).continuous).aestronglyMeasurable 1
    (.of_forall fun x ↦ (Circle.norm_coe (ω⁻¹ x)).le)
  let L := innerSL ℂ (hψ.toLp ψ)
  have hL (g : Lp ℂ 2 μ₁) : L g = lcaFourier μ₁ g ω⁻¹ := by
    rw [lcaFourier]
    change (∫ x, inner ℂ (hψ.toLp ψ x) (g x) ∂μ₁) = _
    apply integral_congr_ae
    filter_upwards [hψ.coeFn_toLp] with x hx
    rw [hx]
    rfl
  let A : (Lp ℂ 2 μ₁ ⊗[ℂ] H) →L[ℂ] H :=
    (TensorProduct.lidIsometry ℂ H).toContinuousLinearEquiv.toContinuousLinearMap.comp (L.rTensor H)
  let : CompleteSpace H := inferInstanceAs (CompleteSpace (Submodule.topologicalClosure _))
  refine ⟨A.fromCompletion, fun g v ↦ ?_⟩
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  simp [A, hL]

-- TODO(paper-gap): Theorem 9.2.1.5(3) switches from the Hilbert tensor product
-- to the projective tensor product in the middle of the bottom row. Its right-hand
-- space is printed H^{N,2}. The scalar specialization (9.2.1.6) requires H^{2N,2}.
-- TODO(paper-gap): Corollary 9.2.1.6 also omits the one-sided support condition.

/-- Paper: Corollary 9.2.1.7, p. 409. Each quasi-character of abscissa below b
gives a continuous moment functional after the cutoff.
Deviation: Use the canonical Haar measure and the intrinsic quasi-character in the
product integral on the supported source. In split coordinates this gives
(9.2.1.25). A change of section changes the coordinates of the same quasi-character. -/
theorem modulatedLineSobolev_cutoff_eval (hm : IsModulation m) (_hms : Surjective m)
    (a b : ℝ) (_ha : 1 < a) (N k : ℕ) (_hk : k < N) (z : ℂ) (_hz : z.re < b)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let E := LineSobolev μ (logModule m) b N
    let U := (logModule m) ⁻¹' Ici (-Real.log a)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    ∃! Λ : E →L[ℂ] ℂ,
      (∀ f : E, Integrable (fun g ↦ U.indicator (⇑f) g *
          (logModule m g : ℂ) ^ k * c z g) μ ∧
        Λ f = ∫ g, U.indicator (⇑f) g * (logModule m g : ℂ) ^ k * c z g ∂μ) ∧
      ∀ (f : ModulatedExponentialDecay m univ) (u : E),
        tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log a) →
        (u : G → ℂ) =ᵐ[μ] f.val →
        Λ u = iteratedDeriv k (fun w ↦ modulatedFourierMellin m univ hm μ f.val (c w)) z := by
  intro μ E U c
  have hμ : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  obtain ⟨Λ, hΛ⟩ := modulated_cutoff_moment_functional m hm μ
    (continuous_lineSobolevDensity b N).measurable (exp_le_lineSobolevDensity b N) _ha z _hz
    k χ _hχ
  refine ⟨Λ, ⟨hΛ, fun f u hsupp hu ↦ ?_⟩,
    fun Λ' hΛ' ↦ ContinuousLinearMap.ext fun f ↦ (hΛ'.1 f).2.trans (hΛ f).2.symm⟩
  have hind : (logModule m ⁻¹' Ici (-Real.log a)).indicator (⇑u) =ᵐ[μ] f.val := by
    filter_upwards [hu] with g hg
    by_cases hgU : g ∈ logModule m ⁻¹' Ici (-Real.log a)
    · rw [Set.indicator_of_mem hgU, hg]
    · rw [Set.indicator_of_notMem hgU]
      exact (image_eq_zero_of_notMem_tsupport fun h ↦ hgU (Ioi_subset_Ici_self
        (show logModule m g ∈ Ioi (-Real.log a) from hsupp h))).symm
  have hint : ∀ σ ∈ Ioo (z.re - 1) b, ∀ n : ℕ,
      Integrable (fun g ↦ f.val g * (logModule m g : ℂ) ^ n *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := fun σ hσ n ↦ by
    obtain ⟨_, hΛσ⟩ := modulated_cutoff_moment_functional m hm μ
      (continuous_lineSobolevDensity b N).measurable (exp_le_lineSobolevDensity b N) _ha
      (σ : ℂ) (by rw [Complex.ofReal_re]; exact hσ.2) n χ _hχ
    refine (hΛσ u).1.congr ?_
    filter_upwards [hind] with g hg
    exact congrArg (fun t : ℂ ↦ t * (logModule m g : ℂ) ^ n *
      quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) hg
  have hFM : (fun w ↦ modulatedFourierMellin m univ hm μ f.val (c w)) = fun w ↦
      ∫ g, f.val g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ :=
    funext fun w ↦ modulatedFourierMellin_univ m hm μ f.val _
  obtain ⟨_, _, hderiv⟩ := iteratedDeriv_normTwist_moment m μ χ hint k
    (show z.re ∈ Ioo (z.re - 1) b from ⟨by linarith, _hz⟩)
  refine ((hΛ u).2.trans (integral_congr_ae ?_)).trans
    (hderiv.symm.trans (congrArg (fun F : ℂ → ℂ ↦ iteratedDeriv k F z) hFM.symm))
  filter_upwards [hind] with g hg
  exact congrArg (fun t : ℂ ↦ t * (logModule m g : ℂ) ^ k *
    quasiCharacterNormTwist m.toMonoidHom m.continuous χ z g) hg
/-- Paper: Corollary 9.2.1.7, p. 409. In each unitary chart the cutoff Mellin
integral of a completed line class is holomorphic and its derivatives are log moments.
Deviation: Apply the source cutoff as in `modulatedLineSobolev_cutoff_eval`. -/
theorem modulatedLineSobolev_cutoff_iteratedDeriv_mellin (hm : IsModulation m) (_hms : Surjective m)
    (a b : ℝ) (_ha : 1 < a) (N k : ℕ) (_hk : k < N) (z : ℂ) (_hz : z.re < b)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1)
    (f : LineSobolev (canonicalModulatedHaar m hm) (logModule m) b N) :
    let μ := canonicalModulatedHaar m hm
    let u := ((logModule m) ⁻¹' Ici (-Real.log a)).indicator (f : G → ℂ)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    let M := fun w : ℂ ↦ modulatedFourierMellin m univ hm μ u (c w)
    AnalyticAt ℂ M z ∧ iteratedDeriv k M z =
      ∫ g, u g * (logModule m g : ℂ) ^ k * c z g ∂μ := by
  intro μ u c M
  have hμ : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hint : ∀ σ ∈ Ioo (z.re - 1) b, ∀ n : ℕ,
      Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ n *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := fun σ hσ n ↦ by
    obtain ⟨_, hΛ⟩ := modulated_cutoff_moment_functional m hm μ
      (continuous_lineSobolevDensity b N).measurable (exp_le_lineSobolevDensity b N) _ha
      (σ : ℂ) (by rw [Complex.ofReal_re]; exact hσ.2) n χ _hχ
    exact (hΛ f).1
  have hM : M = fun w ↦
      ∫ g, u g * quasiCharacterNormTwist m.toMonoidHom m.continuous χ w g ∂μ :=
    funext fun w ↦ modulatedFourierMellin_univ m hm μ u _
  obtain ⟨h1, _, h3⟩ := iteratedDeriv_normTwist_moment m μ χ hint k
    (show z.re ∈ Ioo (z.re - 1) b from ⟨by linarith, _hz⟩)
  rw [hM]
  exact ⟨h1, h3⟩

end ModulatedLine
section Interval

/-- Paper: Proposition 9.2.1.8, p. 410. The density on a compact base interval
uses the larger of the squared endpoint weights and the logarithmic Sobolev factor.
Deviation: The argument is in logarithmic coordinates. -/
def intervalSobolevDensity (a b s x : ℝ) : ℝ :=
  max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) * (1 + x ^ 2) ^ (s / 2)

/-- Paper: Proposition 9.2.1.8, p. 410. At the unit of the positive reals the
density is one for every base interval and degree.
Deviation: Sanity check at logarithmic coordinate zero. -/
theorem intervalSobolevDensity_at_unit (a b s : ℝ) :
    intervalSobolevDensity a b s 0 = 1 := by
  simp [intervalSobolevDensity]

/-- Paper: Proposition 9.2.1.8, p. 410. The compact-interval space has the positive
endpoint density, and its dual model uses the reciprocal density.
Deviation: Both spaces are realized as weighted L². The measure and logarithmic
coordinate are explicit, and `dual = true` selects the reciprocal density. -/
abbrev CompactIntervalSobolev {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (a b s : ℝ) (dual : Bool := false) :=
  Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal
    (if dual then (intervalSobolevDensity a b s (logNorm x))⁻¹
     else intervalSobolevDensity a b s (logNorm x)))

/-- Paper: Definition 9.2.2.9, p. 416, with §10.2.1, p. 439. For the base interval {0} the
weighted measure is the Sobolev measure of Definition 9.1.2.1, so the space is W^{s,2}(G).
Deviation: Sanity check tying the density to §9.1. -/
theorem intervalSobolev_zero_eq_sobolevMeasure {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (s : ℝ) :
    (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logModule m x))) =
      sobolevMeasure μ (modulatedSobolevWeight m) s := by
  unfold sobolevMeasure
  congr 1
  funext x
  have hw : ((modulatedSobolevWeight m x : ℝ≥0) : ℝ) ^ 2 = Real.log ((m x).val : ℝ) ^ 2 :=
    sq_abs _
  rw [hw]
  simp [intervalSobolevDensity]

/-- Paper: Proposition 9.2.2.11, p. 417, with Corollary 10.2.2.3, p. 447. For the base interval
{0} the reciprocal-density measure is the Sobolev measure of degree −s of Proposition 9.1.2.5.
Deviation: Sanity check tying the dual density to §9.1. -/
theorem intervalSobolev_zero_dual_eq_sobolevMeasure {G : Type*} [CommGroup G]
    [TopologicalSpace G] [MeasurableSpace G] (m : G →ₜ* ℝ≥0ˣ) (μ : Measure G) (s : ℝ) :
    (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity 0 0 s (logModule m x))⁻¹) =
      sobolevMeasure μ (modulatedSobolevWeight m) (-s) := by
  unfold sobolevMeasure
  congr 1
  funext x
  have hw : ((modulatedSobolevWeight m x : ℝ≥0) : ℝ) ^ 2 = Real.log ((m x).val : ℝ) ^ 2 :=
    sq_abs _
  have h : (0 : ℝ) ≤ 1 + Real.log ((m x).val : ℝ) ^ 2 := by positivity
  rw [hw, neg_div, Real.rpow_neg h]
  simp [intervalSobolevDensity]

/-- Paper: Definition 9.2.1.1, p. 404. The b-line density and the density of the base
interval {b} in degree 2N bound each other, so the two spaces have the same elements and
topology.
Deviation: Sanity check comparing the two norms the paper uses for W_b^{2N,2}. -/
theorem lineSobolevDensity_le_interval (b : ℝ) (N : ℕ) (x : ℝ) :
    lineSobolevDensity b N x ≤ intervalSobolevDensity b b (2 * (N : ℝ)) x ∧
      intervalSobolevDensity b b (2 * (N : ℝ)) x ≤ 2 ^ N * lineSobolevDensity b N x := by
  have he : 0 ≤ Real.exp (2 * b * x) := (Real.exp_pos _).le
  have hx (k : ℕ) : 0 ≤ x ^ (2 * k) := pow_mul x 2 k ▸ pow_nonneg (sq_nonneg x) k
  have hpow : (1 + x ^ 2) ^ (2 * (N : ℝ) / 2) =
      ∑ k ∈ Finset.range (N + 1), x ^ (2 * k) * (N.choose k : ℝ) := by
    rw [mul_div_cancel_left₀ _ two_ne_zero, Real.rpow_natCast, add_comm, add_pow]
    simp [pow_mul]
  rw [lineSobolevDensity, intervalSobolevDensity, max_self, hpow]
  refine ⟨mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k hk ↦ ?_) he, ?_⟩
  · exact le_mul_of_one_le_right (hx k)
      (by exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
  · rw [mul_left_comm, Finset.mul_sum _ _ ((2 : ℝ) ^ N)]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ ↦ ?_) he
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_two_pow N k) (hx k)

-- TODO(paper-gap): The proposed test pairing on all of S_J × S_J can
-- diverge, and S_J need not be contained in the reciprocal-density space.

/-- The compact-interval density is positive. -/
private theorem intervalSobolevDensity_pos (a b s t : ℝ) : 0 < intervalSobolevDensity a b s t :=
  mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)

/-- The compact-interval density is continuous. -/
private theorem continuous_intervalSobolevDensity' (a b s : ℝ) :
    Continuous (intervalSobolevDensity a b s) := by
  unfold intervalSobolevDensity
  refine Continuous.mul (by fun_prop) (Continuous.rpow_const (by fun_prop) fun t ↦ Or.inl ?_)
  positivity

/-- In weighted L², the squared norm is the integral of the squared modulus against
the density. -/
private theorem weightedL2_norm_eq {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x)
    (f : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x))) :
    Integrable (fun x ↦ ‖f x‖ ^ 2 * ρ x) ν ∧ ‖f‖ = Real.sqrt (∫ x, ‖f x‖ ^ 2 * ρ x ∂ν) := by
  have hdens : Measurable (fun x ↦ ENNReal.ofReal (ρ x)) := hρ.ennreal_ofReal
  have hflt : ∀ᵐ x ∂ν, ENNReal.ofReal (ρ x) < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hint_sq : Integrable (fun x ↦ ‖(f : X → ℂ) x‖ ^ 2)
      (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).1 (Lp.memLp f)
  refine ⟨((integrable_withDensity_iff hdens hflt).1 hint_sq).congr
    (ae_of_all _ fun x ↦ by simp only [ENNReal.toReal_ofReal (hpos x).le]), ?_⟩
  rw [norm_eq_sqrt_re_inner (𝕜 := ℂ) (x := f)]
  refine congrArg Real.sqrt ?_
  rw [L2.inner_def (f := f) (g := f), ← integral_re (L2.integrable_inner f f)]
  simp_rw [inner_self_eq_norm_sq]
  rw [integral_withDensity_eq_integral_toReal_smul hdens hflt]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hpos x).le, mul_comm]

/-- The unweighted product pairing identifies the strong dual of a weighted L² space with
the L² space for the reciprocal density. -/
private theorem weightedL2_dual {X : Type*} [MeasurableSpace X] (ν : Measure X)
    {ρ₁ ρ₂ : X → ℝ} (hρ₁ : Measurable ρ₁) (hρ₂ : Measurable ρ₂)
    (hpos₁ : ∀ x, 0 < ρ₁ x) (hpos₂ : ∀ x, 0 < ρ₂ x) (hrecip : ∀ x, ρ₁ x * ρ₂ x = 1) :
    ∃! T : StrongDual ℂ (Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ₁ x))) ≃ₗᵢ[ℂ]
        Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ₂ x)),
      ∀ Λ f, Integrable (fun x ↦ f x * T Λ x) ν ∧ Λ f = ∫ x, f x * T Λ x ∂ν := by
  let E₁ := Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ₁ x))
  let E₂ := Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ₂ x))
  have hdens₁ : Measurable (fun x ↦ ENNReal.ofReal (ρ₁ x)) := hρ₁.ennreal_ofReal
  have hflt₁ : ∀ᵐ x ∂ν, ENNReal.ofReal (ρ₁ x) < ∞ := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top
  have hbase {ρ : X → ℝ} (hρ : Measurable ρ) (hpos : ∀ x, 0 < ρ x) :
      ν ≪ ν.withDensity fun x ↦ ENNReal.ofReal (ρ x) :=
    withDensity_absolutelyContinuous' hρ.ennreal_ofReal.aemeasurable
      (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hpos x)).ne')
  have hweighted (ρ : X → ℝ) : (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x)) ≪ ν :=
    withDensity_absolutelyContinuous _ _
  -- Conjugation times the density maps one weighted space isometrically onto the other.
  have hmap {ρ ρ' : X → ℝ} (hρ : Measurable ρ) (hρ' : Measurable ρ') (hpos : ∀ x, 0 < ρ x)
      (hpos' : ∀ x, 0 < ρ' x) (hr : ∀ x, ρ x * ρ' x = 1)
      (f : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ x))) :
      ∃ g : Lp ℂ 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)),
        (g : X → ℂ) =ᵐ[ν] (fun x ↦ (ρ x : ℂ) * star (f x)) ∧ ‖g‖ = ‖f‖ := by
    let u : X → ℂ := fun x ↦ (ρ x : ℂ) * star (f x)
    have hsq (x : X) : ‖u x‖ ^ 2 * ρ' x = ‖f x‖ ^ 2 * ρ x := by
      calc
        _ = ‖f x‖ ^ 2 * (ρ x * (ρ x * ρ' x)) := by
          dsimp only [u]
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hpos x), norm_star]
          ring
        _ = _ := by rw [hr, mul_one]
    have hmeas : AEStronglyMeasurable u (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) :=
      (Complex.measurable_ofReal.comp hρ).aestronglyMeasurable.mul
        (((Lp.aestronglyMeasurable f).mono_ac (hbase hρ hpos)).mono_ac (hweighted ρ')).star
    have hmem : MemLp u 2 (ν.withDensity fun x ↦ ENNReal.ofReal (ρ' x)) := by
      apply (memLp_two_iff_integrable_sq_norm hmeas).2
      apply (integrable_withDensity_iff hρ'.ennreal_ofReal
        (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).2
      refine (weightedL2_norm_eq ν hρ hpos f).1.congr (ae_of_all _ fun x ↦ ?_)
      change ‖f x‖ ^ 2 * ρ x = ‖u x‖ ^ 2 * (ENNReal.ofReal (ρ' x)).toReal
      rw [ENNReal.toReal_ofReal (hpos' x).le, hsq]
    have hcoe : (hmem.toLp u : X → ℂ) =ᵐ[ν] u := (hbase hρ' hpos').ae_eq hmem.coeFn_toLp
    refine ⟨hmem.toLp u, hcoe, ?_⟩
    rw [(weightedL2_norm_eq ν hρ' hpos' _).2, (weightedL2_norm_eq ν hρ hpos f).2]
    congr 1
    apply integral_congr_ae
    filter_upwards [hcoe] with x hx
    rw [hx, hsq]
  choose S hS hSnorm using hmap hρ₁ hρ₂ hpos₁ hpos₂ hrecip
  choose S' hS' _ using hmap hρ₂ hρ₁ hpos₂ hpos₁ (fun x ↦ (mul_comm _ _).trans (hrecip x))
  let C : E₁ →ₗᵢ⋆[ℂ] E₂ :=
    { toFun := S
      map_add' := fun f g ↦ Lp.ext <| (hweighted ρ₂).ae_eq <| by
        filter_upwards [hS (f + g), hS f, hS g,
          (hbase hρ₁ hpos₁).ae_eq (Lp.coeFn_add f g),
          (hbase hρ₂ hpos₂).ae_eq (Lp.coeFn_add (S f) (S g))] with x hfg hf hg hx hsum
        rw [hfg, hsum, Pi.add_apply, hf, hg, hx, Pi.add_apply, star_add, mul_add]
      map_smul' := fun c f ↦ Lp.ext <| (hweighted ρ₂).ae_eq <| by
        filter_upwards [hS (c • f), hS f, (hbase hρ₁ hpos₁).ae_eq (Lp.coeFn_smul c f),
          (hbase hρ₂ hpos₂).ae_eq (Lp.coeFn_smul ((starRingEnd ℂ) c) (S f))]
          with x hcf hf hx hsmul
        rw [hcf, hsmul, Pi.smul_apply, hf, hx, Pi.smul_apply]
        simp only [starRingEnd_apply, smul_eq_mul, star_mul', mul_left_comm]
      norm_map' := hSnorm }
  have hSurj : Function.Surjective C := by
    intro g
    refine ⟨S' g, Lp.ext ((hweighted ρ₂).ae_eq ?_)⟩
    change (S (S' g) : X → ℂ) =ᵐ[ν] g
    filter_upwards [hS (S' g), hS' g] with x hSx hS'x
    have hstar : star (ρ₂ x : ℂ) = (ρ₂ x : ℂ) := Complex.conj_ofReal _
    rw [hSx, hS'x, star_mul', hstar, star_star, ← mul_assoc, ← Complex.ofReal_mul, hrecip,
      Complex.ofReal_one, one_mul]
  let R := InnerProductSpace.toDual ℂ E₁
  let T : StrongDual ℂ E₁ ≃ₗᵢ[ℂ] E₂ := R.symm.trans (LinearIsometryEquiv.ofSurjective C hSurj)
  have hPair (Λ : StrongDual ℂ E₁) (f : E₁) :
      Integrable (fun x ↦ f x * T Λ x) ν ∧ Λ f = ∫ x, f x * T Λ x ∂ν := by
    let g := R.symm Λ
    have hprod : (fun x ↦ f x * T Λ x) =ᵐ[ν]
        fun x ↦ (ENNReal.ofReal (ρ₁ x)).toReal • inner ℂ (g x) (f x) := by
      filter_upwards [hS g] with x hx
      change f x * S g x = _
      rw [hx, ENNReal.toReal_ofReal (hpos₁ x).le, RCLike.inner_apply, starRingEnd_apply]
      simp only [Complex.real_smul, mul_left_comm]
    refine ⟨?_, ?_⟩
    · exact ((integrable_withDensity_iff_integrable_smul' hdens₁ hflt₁).1
        (L2.integrable_inner g f)).congr hprod.symm
    · calc
        Λ f = inner ℂ g f := InnerProductSpace.toDual_symm_apply.symm
        _ = ∫ x, inner ℂ (g x) (f x) ∂(ν.withDensity fun x ↦ ENNReal.ofReal (ρ₁ x)) :=
          L2.inner_def g f
        _ = ∫ x, (ENNReal.ofReal (ρ₁ x)).toReal • inner ℂ (g x) (f x) ∂ν :=
          integral_withDensity_eq_integral_toReal_smul hdens₁ hflt₁ _
        _ = ∫ x, f x * T Λ x ∂ν := integral_congr_ae hprod.symm
  refine ⟨T, hPair, fun T' hT' ↦ LinearIsometryEquiv.ext fun Λ ↦ ?_⟩
  apply T.symm.injective
  rw [T.symm_apply_apply]
  apply ContinuousLinearMap.ext
  intro f
  rw [(hPair (T.symm (T' Λ)) f).2, T.apply_symm_apply, (hT' Λ f).2]

/-- Paper: Proposition 9.2.1.8, p. 409. The strong dual of the scalar compact-interval
space is represented isometrically by integration against the reciprocal-density space.
Deviation: The duality is stated on the weighted L² spaces. The pairing on all of
S_J × S_J in (9.2.1.27) can diverge. The paper assumes a < b, but §10.2–10.4 apply the
duality to I = [−α, α] with α ≥ 0, so the one-point base is included. -/
theorem scalarIntervalSobolev_dual (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (CompactIntervalSobolev volume id a b s) ≃ₗᵢ[ℂ]
        CompactIntervalSobolev volume id a b s true,
      ∀ Λ f, Integrable (fun x ↦ f x * T Λ x) volume ∧
        Λ f = ∫ x, f x * T Λ x :=
  weightedL2_dual volume (continuous_intervalSobolevDensity' a b s).measurable
    (continuous_intervalSobolevDensity' a b s).measurable.inv
    (intervalSobolevDensity_pos a b s) (fun x ↦ inv_pos.mpr (intervalSobolevDensity_pos a b s x))
    (fun x ↦ mul_inv_cancel₀ (intervalSobolevDensity_pos a b s x).ne')

-- TODO(paper-gap): The topology generated by individual interior line norms in
-- (9.2.2.2) is strictly coarser than the uniform Hardy norm in (9.2.2.1).

/-- Paper: Definition 9.2.2.1, p. 412. Take the supremum of the endpoint weighted
L² norms over pairs of abscissas in the base interval.
Deviation: The supremum is extended-valued. It can be infinite on the paper's test
space for unbounded I. For an interval, every pair determines a subinterval. -/
def intervalSobolevENorm {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (I : Set ℝ) (s : ℝ) (f : A → ℂ) : ℝ≥0∞ :=
  ⨆ (a : I) (b : I), eLpNorm f 2
    (μ.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a b s (logNorm x)))

/-- Paper: Lemma 9.2.2.2(1), p. 412. On a compact base interval the exponential-decay
test space and every open-interval test space containing the base have the same completion.
Deviation: This states the compact case by identifying each dense continuous
inclusion into weighted L², with agreement on function representatives. -/
theorem scalarIntervalSobolev_dense (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (J : Set ℝ) (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    ∃ j : PositiveRealExponentialDecay J →L[ℂ] CompactIntervalSobolev volume id a b s,
      Injective j ∧ DenseRange j ∧ ∀ f, (j f : ℝ → ℂ) =ᵐ[volume] f.val := by sorry

/-- The square of a Schwartz function is integrable against every real power of `1 + x ^ 2`. -/
private theorem integrable_schwartz_sq_mul_rpow (g : SchwartzMap ℝ ℂ) (s : ℝ) :
    Integrable (fun x ↦ ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2)) volume := by
  obtain ⟨n, hn⟩ := exists_nat_ge (s / 2)
  have h1 : ∀ x : ℝ, (1 + x ^ 2) ^ (s / 2) ≤ (1 + ‖x‖) ^ (2 * n) := fun x ↦ by
    have hx : 1 + x ^ 2 ≤ (1 + ‖x‖) ^ 2 := by
      rw [Real.norm_eq_abs]
      nlinarith [abs_nonneg x, sq_abs x]
    calc (1 + x ^ 2) ^ (s / 2) ≤ (1 + x ^ 2) ^ (n : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg x]) hn
      _ = (1 + x ^ 2) ^ n := Real.rpow_natCast _ _
      _ ≤ ((1 + ‖x‖) ^ 2) ^ n := pow_le_pow_left₀ (by positivity) hx n
      _ = (1 + ‖x‖) ^ (2 * n) := (pow_mul _ _ _).symm
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ x : ℝ, (1 + ‖x‖) ^ (2 * n) * ‖g x‖ ≤ C := by
    refine ⟨2 ^ (2 * n) * (Finset.Iic (2 * n, 0)).sup (fun m ↦ SchwartzMap.seminorm ℝ m.1 m.2) g,
      fun x ↦ ?_⟩
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (2 * n, 0))
      le_rfl le_rfl g x
    rw [norm_iteratedFDeriv_zero] at h
    exact h
  have hmeas : AEStronglyMeasurable (fun x ↦ ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2)) volume :=
    ((g.continuous.norm.pow 2).mul ((continuous_const.add (continuous_pow 2)).rpow_const
      fun x ↦ Or.inl (by positivity : (0 : ℝ) < 1 + x ^ 2).ne')).aestronglyMeasurable
  refine ((g.integrable (μ := volume)).norm.const_mul C).mono' hmeas
    (Eventually.of_forall fun x ↦ ?_)
  have h0 : 0 ≤ ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2) := by positivity
  rw [Real.norm_of_nonneg h0]
  calc ‖g x‖ ^ 2 * (1 + x ^ 2) ^ (s / 2) ≤ ‖g x‖ ^ 2 * (1 + ‖x‖) ^ (2 * n) :=
        mul_le_mul_of_nonneg_left (h1 x) (by positivity)
    _ = (1 + ‖x‖) ^ (2 * n) * ‖g x‖ * ‖g x‖ := by ring
    _ ≤ C * ‖g x‖ := mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Paper: Lemma 9.2.2.2(2), p. 412. For a compact base interval the supremum
is attained at the two extreme abscissas and yields the stated weighted integral.
Deviation: Use the logarithmic coordinate and record finiteness before taking the real norm. -/
theorem scalarIntervalSobolev_norm (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) :
    Integrable (fun x ↦ ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x) volume ∧
      intervalSobolevENorm volume id (Icc a b) s f.val =
        ENNReal.ofReal (Real.sqrt (∫ x, ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x)) := by
  have hDpos : ∀ x : ℝ, 0 < intervalSobolevDensity a b s x := fun x ↦
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  -- Shrinking the endpoints inside `[a, b]` only lowers the density.
  have hmono : ∀ a' ∈ Icc a b, ∀ b' ∈ Icc a b, ∀ x : ℝ,
      intervalSobolevDensity a' b' s x ≤ intervalSobolevDensity a b s x := by
    intro a' ha' b' hb' x
    have key : ∀ c ∈ Icc a b,
        Real.exp (2 * c * x) ≤ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
      intro c hc
      rcases le_total 0 x with hx | hx
      · exact le_max_of_le_right (Real.exp_le_exp.2 (by nlinarith [hc.2]))
      · exact le_max_of_le_left (Real.exp_le_exp.2 (by nlinarith [hc.1]))
    exact mul_le_mul_of_nonneg_right (max_le (key a' ha') (key b' hb')) (by positivity)
  have hval : ∀ c x : ℝ, logExponentialDecayTwist univ ⟨c, mem_univ c⟩ f x =
      (Real.exp (c * x) : ℂ) * f.val x := fun c x ↦
    logExponentialDecayTwist_apply univ ⟨c, mem_univ c⟩ f x
  have hcont : Continuous f.val := by
    have h : ⇑(logExponentialDecayTwist univ ⟨0, mem_univ 0⟩ f) = f.val := by
      funext x
      rw [hval, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
    rw [← h]
    exact SchwartzMap.continuous _
  -- Each exponential twist of `f` is a Schwartz function.
  have hg : ∀ c : ℝ, ∃ g : SchwartzMap ℝ ℂ, ∀ x : ℝ,
      ‖g x‖ ^ 2 = Real.exp (2 * c * x) * ‖f.val x‖ ^ 2 := fun c ↦
    ⟨logExponentialDecayTwist univ ⟨c, mem_univ c⟩ f, fun x ↦ by
      rw [hval, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _),
        mul_pow, ← Real.exp_nat_mul]
      congr 2
      push_cast
      ring⟩
  obtain ⟨ga, hga⟩ := hg a
  obtain ⟨gb, hgb⟩ := hg b
  have hDmeas : Measurable fun x : ℝ ↦ intervalSobolevDensity a b s x := by
    unfold intervalSobolevDensity
    fun_prop
  have hint : Integrable (fun x ↦ ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x) volume := by
    refine ((integrable_schwartz_sq_mul_rpow ga s).add
      (integrable_schwartz_sq_mul_rpow gb s)).mono'
      ((hcont.measurable.norm.pow_const 2).mul hDmeas).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (hDpos x).le), Pi.add_apply, hga, hgb]
    unfold intervalSobolevDensity
    have hw : 0 ≤ (1 + x ^ 2) ^ (s / 2) := by positivity
    have hmax : max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) ≤
        Real.exp (2 * a * x) + Real.exp (2 * b * x) :=
      max_le_add_of_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hmax hw)
      (sq_nonneg ‖f.val x‖)]
  have hρ : AEMeasurable (fun x ↦ (intervalSobolevDensity a b s x).toNNReal) volume :=
    hDmeas.real_toNNReal.aemeasurable
  have hsmul : ∀ x, (intervalSobolevDensity a b s x).toNNReal • ‖f.val x‖ ^ 2 =
      ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x := fun x ↦ by
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hDpos _).le, mul_comm]
  have hf2 : Integrable (fun x ↦ ‖f.val x‖ ^ 2)
      (volume.withDensity fun x ↦ ((intervalSobolevDensity a b s x).toNNReal : ℝ≥0∞)) :=
    (integrable_withDensity_iff_integrable_smul₀ hρ).2
      (hint.congr (Eventually.of_forall fun x ↦ (hsmul x).symm))
  have hmem : MemLp f.val 2
      (volume.withDensity fun x ↦ ((intervalSobolevDensity a b s x).toNNReal : ℝ≥0∞)) :=
    (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 hf2
  have hI : ∫ x, ‖f.val x‖ ^ 2 * intervalSobolevDensity a b s x = ∫ x, ‖f.val x‖ ^ 2
      ∂volume.withDensity fun x ↦ ((intervalSobolevDensity a b s x).toNNReal : ℝ≥0∞) := by
    rw [integral_withDensity_eq_integral_smul₀ hρ]
    exact integral_congr_ae (Eventually.of_forall fun x ↦ (hsmul x).symm)
  have hE : intervalSobolevENorm volume id (Icc a b) s f.val =
      eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) := by
    unfold intervalSobolevENorm
    refine le_antisymm (iSup₂_le fun a' b' ↦ eLpNorm_mono_measure _ (withDensity_mono
      (Eventually.of_forall fun x ↦ ENNReal.ofReal_le_ofReal (hmono _ a'.2 _ b'.2 _)))) ?_
    exact le_iSup₂_of_le (⟨a, left_mem_Icc.2 _hab⟩ : Icc a b) ⟨b, right_mem_Icc.2 _hab⟩ le_rfl
  refine ⟨hint, ?_⟩
  rw [hE, hI, Real.sqrt_eq_rpow]
  refine (MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top hmem).trans ?_
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]

/-- Paper: Lemma 9.2.2.2(2), p. 412. For even order the endpoint derivative
traces and the compact-interval weighted norm induce the same topology on the tests.
Deviation: Express equivalence by two-sided comparison with the sum of the finitely
many norms in (9.2.2.5). -/
theorem scalarIntervalSobolev_mellin_norm_bounds (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ f : PositiveRealExponentialDecay univ,
      let F := mellin (fun t ↦ f.val (Real.log t))
      let w := (intervalSobolevENorm volume id (Icc a b) (2 * (N : ℝ)) f.val).toReal
      let q := fun σ : ℝ ↦ ∑ k ∈ Finset.range (N + 1),
        (eLpNorm (fun y : ℝ ↦ iteratedDeriv k F (verticalPoint σ y)) 2 volume).toReal
      (∀ σ ∈ ({a, b} : Set ℝ), ∀ k ≤ N,
        MemLp (fun y : ℝ ↦ iteratedDeriv k F (verticalPoint σ y)) 2 volume) ∧
        w ≤ C * (q a + q b) ∧ q a + q b ≤ D * w := by sorry

/-- On a right half-line the supremum over pairs of abscissas equals the supremum over pairs
whose first abscissa is the left endpoint. -/
private theorem intervalSobolevENorm_Ici {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (a s : ℝ) (f : A → ℂ) :
    intervalSobolevENorm μ logNorm (Ici a) s f =
      ⨆ σ : Ici a, eLpNorm f 2 (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s (logNorm x))) := by
  unfold intervalSobolevENorm
  refine le_antisymm (iSup₂_le fun a' b' ↦ ?_)
    (iSup_le fun σ ↦ le_iSup₂_of_le (⟨a, self_mem_Ici⟩ : Ici a) σ le_rfl)
  have hσ : max (a' : ℝ) b' ∈ Ici a := le_max_of_le_left a'.2
  refine le_iSup_of_le (⟨_, hσ⟩ : Ici a) (eLpNorm_mono_measure _ (withDensity_mono
    (Eventually.of_forall fun g ↦ ENNReal.ofReal_le_ofReal ?_)))
  have key : ∀ c : ℝ, a ≤ c → c ≤ max (a' : ℝ) b' → ∀ x : ℝ, Real.exp (2 * c * x) ≤
      max (Real.exp (2 * a * x)) (Real.exp (2 * max (a' : ℝ) b' * x)) := by
    intro c hac hc x
    rcases le_total 0 x with hx | hx
    · exact le_max_of_le_right
        (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hc hx]))
    · exact le_max_of_le_left
        (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonpos_right hac hx]))
  unfold intervalSobolevDensity
  exact mul_le_mul_of_nonneg_right
    (max_le (key _ a'.2 (le_max_left _ _) _) (key _ b'.2 (le_max_right _ _) _)) (by positivity)

/-- On a left half-line the supremum over pairs of abscissas equals the supremum over pairs
whose second abscissa is the right endpoint. -/
private theorem intervalSobolevENorm_Iic {A : Type*} [MeasurableSpace A] (μ : Measure A)
    (logNorm : A → ℝ) (b s : ℝ) (f : A → ℂ) :
    intervalSobolevENorm μ logNorm (Iic b) s f =
      ⨆ σ : Iic b, eLpNorm f 2 (μ.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity σ b s (logNorm x))) := by
  unfold intervalSobolevENorm
  refine le_antisymm (iSup₂_le fun a' b' ↦ ?_)
    (iSup_le fun σ ↦ le_iSup₂_of_le σ (⟨b, self_mem_Iic⟩ : Iic b) le_rfl)
  have hσ : min (a' : ℝ) b' ∈ Iic b := min_le_of_left_le a'.2
  refine le_iSup_of_le (⟨_, hσ⟩ : Iic b) (eLpNorm_mono_measure _ (withDensity_mono
    (Eventually.of_forall fun g ↦ ENNReal.ofReal_le_ofReal ?_)))
  have key : ∀ c : ℝ, min (a' : ℝ) b' ≤ c → c ≤ b → ∀ x : ℝ, Real.exp (2 * c * x) ≤
      max (Real.exp (2 * min (a' : ℝ) b' * x)) (Real.exp (2 * b * x)) := by
    intro c hc hcb x
    rcases le_total 0 x with hx | hx
    · exact le_max_of_le_right
        (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_right hcb hx]))
    · exact le_max_of_le_left
        (Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonpos_right hc hx]))
  unfold intervalSobolevDensity
  exact mul_le_mul_of_nonneg_right
    (max_le (key _ (min_le_left _ _) a'.2 _) (key _ (min_le_right _ _) b'.2 _)) (by positivity)

/-- Paper: Lemma 9.2.2.2(3)(a), p. 412. For a right half-line the endpoint
supremum uses the left endpoint and an arbitrary point in the interval.
Deviation: The identity is extended-valued, since the supremum can be infinite. -/
theorem scalarIntervalSobolev_enorm_Ici (a s : ℝ) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) :
    intervalSobolevENorm volume id (Ici a) s f.val =
      ⨆ σ : Ici a, eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s x)) :=
  intervalSobolevENorm_Ici volume id a s f.val

/-- Paper: Lemma 9.2.2.2(3)(b), p. 412. For a left half-line the endpoint
supremum uses an arbitrary point in the interval and the right endpoint.
Deviation: The identity is extended-valued, since the supremum can be infinite. -/
theorem scalarIntervalSobolev_enorm_Iic (b s : ℝ) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) :
    intervalSobolevENorm volume id (Iic b) s f.val =
      ⨆ σ : Iic b, eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity σ b s x)) :=
  intervalSobolevENorm_Iic volume id b s f.val

/-- Paper: Definition 9.2.2.1, p. 412. A nonzero smooth test supported on a
compact subset of the positive logarithmic axis has infinite norm for a right half-line.
Deviation: This is a counterexample to the finiteness of the proposed norm. -/
theorem scalarIntervalSobolev_enorm_Ici_eq_top (a s : ℝ) (_hs : 0 ≤ s)
    (f : PositiveRealExponentialDecay univ) (_hf : f.val ≠ 0)
    (_hcompact : HasCompactSupport f.val) (_hsupport : tsupport f.val ⊆ Ioi 0) :
    intervalSobolevENorm volume id (Ici a) s f.val = ∞ := by
  have hcont : Continuous f.val := by
    have h : ⇑(logExponentialDecayTwist univ ⟨0, mem_univ 0⟩ f) = f.val := by
      funext x
      simpa only [Subtype.coe_mk, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul] using
        logExponentialDecayTwist_apply univ ⟨0, mem_univ (0 : ℝ)⟩ f x
    rw [← h]
    exact SchwartzMap.continuous _
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f.val x₀ ≠ 0 := by
    by_contra h
    exact _hf (funext fun x ↦ not_not.1 fun hx ↦ h ⟨x, hx⟩)
  have hx₀pos : 0 < x₀ := _hsupport (subset_tsupport _ hx₀)
  obtain ⟨c, hc, hcx⟩ : ∃ c : ℝ, 0 < c ∧ c < ‖f.val x₀‖ :=
    ⟨_, half_pos (norm_pos_iff.2 hx₀), half_lt_self (norm_pos_iff.2 hx₀)⟩
  -- An open set of positive measure on which `f` and the coordinate stay away from zero.
  obtain ⟨U, hUo, hx₀U, hUc, hUx⟩ : ∃ U : Set ℝ, IsOpen U ∧ x₀ ∈ U ∧
      (∀ x ∈ U, c < ‖f.val x‖) ∧ ∀ x ∈ U, x₀ / 2 < x :=
    ⟨{x | c < ‖f.val x‖} ∩ Ioi (x₀ / 2), (isOpen_lt continuous_const hcont.norm).inter isOpen_Ioi,
      ⟨hcx, half_lt_self hx₀pos⟩, fun x hx ↦ hx.1, fun x hx ↦ hx.2⟩
  have hUpos : volume U ≠ 0 := (hUo.measure_pos volume ⟨x₀, hx₀U⟩).ne'
  have hε : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc).ne'
  -- Chebyshev's inequality for the pair `(a, σ)` bounds an exponential in `σ` by the supremum.
  have hbound : ∀ σ : ℝ, max a 0 ≤ σ → ENNReal.ofReal (Real.exp (σ * x₀)) * volume U ≤
      (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal *
        intervalSobolevENorm volume id (Ici a) s f.val ^ (2 : ℝ≥0∞).toReal := by
    intro σ hσ
    have hσa : a ≤ σ := (le_max_left _ _).trans hσ
    have hσ0 : 0 ≤ σ := (le_max_right _ _).trans hσ
    have hle : eLpNorm f.val 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s x)) ≤
        intervalSobolevENorm volume id (Ici a) s f.val := by
      unfold intervalSobolevENorm
      exact le_iSup₂_of_le (⟨a, self_mem_Ici⟩ : Ici a) (⟨σ, hσa⟩ : Ici a) le_rfl
    have hdens : ∀ x ∈ U, ENNReal.ofReal (Real.exp (σ * x₀)) ≤
        ENNReal.ofReal (intervalSobolevDensity a σ s x) := by
      intro x hx
      have h1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (s / 2) :=
        Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by positivity)
      have h2 : Real.exp (σ * x₀) ≤ Real.exp (2 * σ * x) :=
        Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left (hUx x hx).le hσ0])
      refine ENNReal.ofReal_le_ofReal ?_
      unfold intervalSobolevDensity
      exact (h2.trans (le_max_right _ _)).trans
        (le_mul_of_one_le_right (le_max_of_le_right (Real.exp_pos _).le) h1)
    calc ENNReal.ofReal (Real.exp (σ * x₀)) * volume U
        = ∫⁻ _ in U, ENNReal.ofReal (Real.exp (σ * x₀)) := (setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in U, ENNReal.ofReal (intervalSobolevDensity a σ s x) :=
          setLIntegral_mono' hUo.measurableSet hdens
      _ = (volume.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a σ s x)) U :=
          (withDensity_apply _ hUo.measurableSet).symm
      _ ≤ (volume.withDensity fun x ↦ ENNReal.ofReal (intervalSobolevDensity a σ s x))
            {x | ENNReal.ofReal c ≤ ‖f.val x‖ₑ} := measure_mono fun x hx ↦ by
          rw [mem_ofPred_eq, ← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hUc x hx).le
      _ ≤ (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal * eLpNorm f.val 2 (volume.withDensity fun x ↦
            ENNReal.ofReal (intervalSobolevDensity a σ s x)) ^ (2 : ℝ≥0∞).toReal :=
          meas_ge_le_mul_pow_eLpNorm_eNorm _ two_ne_zero ENNReal.ofNat_ne_top hε
            fun h ↦ absurd h ENNReal.ofReal_ne_top
      _ ≤ _ := by gcongr
  by_contra htop
  have hBtop : (ENNReal.ofReal c)⁻¹ ^ (2 : ℝ≥0∞).toReal *
      intervalSobolevENorm volume id (Ici a) s f.val ^ (2 : ℝ≥0∞).toReal ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by simp) (ENNReal.inv_ne_top.2 hε))
      (ENNReal.rpow_ne_top_of_nonneg (by simp) htop)
  obtain ⟨K, hK, hKle⟩ : ∃ K : ℝ≥0∞, K ≠ ∞ ∧
      ∀ σ : ℝ, max a 0 ≤ σ → ENNReal.ofReal (Real.exp (σ * x₀)) ≤ K :=
    ⟨_, ENNReal.div_ne_top hBtop hUpos, fun σ hσ ↦
      (ENNReal.le_div_iff_mul_le (Or.inl hUpos) (Or.inr hBtop)).2 (hbound σ hσ)⟩
  have hlt : K.toReal < Real.exp (max (max a 0) (K.toReal / x₀) * x₀) := by
    have h := (div_le_iff₀ hx₀pos).1 (le_max_right (max a 0) (K.toReal / x₀))
    linarith [Real.add_one_le_exp (max (max a 0) (K.toReal / x₀) * x₀)]
  exact absurd (hKle _ (le_max_left _ _)) (not_le.2 ((ENNReal.lt_ofReal_iff_toReal_lt hK).2 hlt))

/-- An integrable function on the real line whose Fourier transform vanishes identically is
zero almost everywhere: pair it with the Fourier transforms of Schwartz functions. -/
private theorem ae_eq_zero_of_fourier_eq_zero {h : ℝ → ℂ} (hh : Integrable h)
    (hF : ∀ y : ℝ, FourierTransform.fourier h y = 0) : h =ᵐ[volume] 0 := by
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hh.locallyIntegrable fun g hg hgc ↦ ?_
  have hg₁ : HasCompactSupport (Complex.ofRealCLM ∘ g) := hgc.comp_left rfl
  let ψ : SchwartzMap ℝ ℂ := hg₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp hg)
  let φ : SchwartzMap ℝ ℂ := FourierTransform.fourierInv ψ
  have hφ : FourierTransform.fourier φ = ψ := FourierTransform.fourier_fourierInv_eq ψ
  have key : ∫ ξ, FourierTransform.fourier (φ : ℝ → ℂ) ξ • h ξ =
      ∫ x, φ x • FourierTransform.fourier h x := by
    simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (ContinuousLinearMap.lsmul ℂ ℂ) (L := innerₗ ℝ) Real.continuous_fourierChar
      continuous_inner φ.integrable hh
  calc ∫ x, g x • h x = ∫ x, ψ x • h x := by
        refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
        exact (Complex.coe_smul (g x) (h x)).symm
    _ = ∫ ξ, FourierTransform.fourier (φ : ℝ → ℂ) ξ • h ξ := by
        rw [← SchwartzMap.fourier_coe, hφ]
    _ = ∫ x, φ x • FourierTransform.fourier h x := key
    _ = 0 := by simp [hF]

/-- On the open strip of a compact base interval, each moment of a weighted L² class against
a real exponential is integrable. -/
private theorem intervalSobolev_integrable_moment (a b s : ℝ) (hs : 0 ≤ s)
    (f : CompactIntervalSobolev volume id a b s) {σ : ℝ} (hσ : σ ∈ Ioo a b) (n : ℕ) :
    Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume := by
  obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ σ - a ∧ δ ≤ b - σ :=
    ⟨min (σ - a) (b - σ), lt_min (sub_pos.2 hσ.1) (sub_pos.2 hσ.2),
      min_le_left _ _, min_le_right _ _⟩
  obtain ⟨_, hΛ⟩ := weightedL2_moment_functional (continuous_intervalSobolevDensity' a b s)
    (intervalSobolevDensity_pos a b s) (σ : ℂ) n MeasurableSet.univ (δ := 2 * δ) (K := 1)
    (mul_pos two_pos hδ) zero_le_one fun x _ ↦ by
      have h1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (s / 2) :=
        Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)
      rw [one_mul, Complex.ofReal_re]
      unfold intervalSobolevDensity
      refine le_trans ?_ (le_mul_of_one_le_right (le_max_of_le_left (Real.exp_pos _).le) h1)
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_max_of_le_right (Real.exp_le_exp.2
          (by nlinarith [mul_nonneg (sub_nonneg.2 hδb) hx]))
      · rw [abs_of_nonpos hx]
        exact le_max_of_le_left (Real.exp_le_exp.2
          (by nlinarith [mul_nonneg (sub_nonneg.2 hδa) (neg_nonneg.2 hx)]))
  simpa only [Set.indicator_univ, mul_assoc] using (hΛ f).1
-- TODO(paper-gap): Lemma 9.2.2.2(3) treats the infinite supremum as a finite
-- norm and identifies it with the topology of individual line norms.
-- TODO(paper-gap): Definition 9.2.2.3 does not specify how the derivative index k
-- should depend on s or restrict the sampled abscissas to I. The boundary
-- accumulation requirement alone does not determine the topology in 9.2.2.4(1).
-- TODO(paper-gap): The derivative range on p. 417 only samples integer orders.
-- For 1 < s < 2 it sees just the zeroth trace. On I = [−1,0] the Mellin
-- transforms of R⁻¹ φ(x/R), with φ smooth of integral one supported in (1,2),
-- tend to zero in every such line norm, including both endpoints, but equal
-- one at z = 0. The fractional-degree endpoint evaluations below concern
-- the weighted source. An analytic counterpart needs fractional trace control.
-- TODO(paper-gap): Proposition 9.2.2.4(2) does not supply an interior from which
-- to take boundary values for a singleton interval.

/-- Paper: Proposition 9.2.2.4(2), p. 414. A weighted L² class on a nondegenerate
compact base interval gives a holomorphic Mellin transform on its open strip.
Deviation: State the compact-base assertion in the weighted source model. -/
theorem scalarIntervalSobolev_mellin_holomorphic (a b s : ℝ) (_hab : a < b) (_hs : 0 ≤ s) :
    let E := CompactIntervalSobolev volume id a b s
    let strip := Complex.re ⁻¹' Ioo a b
    let M := fun (f : E) z ↦ ∫ x : ℝ, f x * Complex.exp (z * (x : ℂ))
    (∀ f : E, (∀ z ∈ strip, Integrable (fun x : ℝ ↦ f x * Complex.exp (z * (x : ℂ)))) ∧
      DifferentiableOn ℂ (M f) strip) ∧ Injective (fun f ↦ fun z : strip ↦ M f z.val) := by
  intro E strip M
  have hmom (f : E) (z : ℂ) (hz : z ∈ strip) :=
    iteratedDeriv_exp_moment (h := (f : ℝ → ℂ))
      (fun σ hσ n ↦ intervalSobolev_integrable_moment a b s _hs f hσ n) 0 (z := z) hz
  have hint (f : E) (z : ℂ) (hz : z ∈ strip) :
      Integrable (fun x : ℝ ↦ f x * Complex.exp (z * (x : ℂ))) := by
    simpa only [pow_zero, mul_one] using (hmom f z hz).2.1
  refine ⟨fun f ↦ ⟨hint f, fun z hz ↦ ?_⟩, fun f₁ f₂ heq ↦ ?_⟩
  · exact (hmom f z hz).1.differentiableAt.differentiableWithinAt
  · have hσ : ((a + b) / 2 : ℝ) ∈ Ioo a b := ⟨by linarith, by linarith⟩
    have hzmem (y : ℝ) : (((a + b) / 2 : ℝ) : ℂ) + ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.I ∈
        strip := by
      change (_ : ℂ).re ∈ Ioo a b
      simpa using hσ
    have hσmem : (((a + b) / 2 : ℝ) : ℂ) ∈ strip := by
      change (_ : ℂ).re ∈ Ioo a b
      simpa using hσ
    have hh : Integrable (fun x : ℝ ↦ (f₁ x - f₂ x) *
        Complex.exp ((((a + b) / 2 : ℝ) : ℂ) * (x : ℂ))) :=
      ((hint f₁ _ hσmem).sub (hint f₂ _ hσmem)).congr
        (ae_of_all _ fun x ↦ (sub_mul _ _ _).symm)
    have hzero := ae_eq_zero_of_fourier_eq_zero hh fun y ↦ by
      rw [Real.fourier_real_eq_integral_exp_smul]
      have hfun : (fun v : ℝ ↦ Complex.exp (((-2 * Real.pi * v * y : ℝ) : ℂ) * Complex.I) •
          ((f₁ v - f₂ v) * Complex.exp ((((a + b) / 2 : ℝ) : ℂ) * (v : ℂ)))) = fun v : ℝ ↦
          f₁ v * Complex.exp (((((a + b) / 2 : ℝ) : ℂ) +
            ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.I) * (v : ℂ)) -
          f₂ v * Complex.exp (((((a + b) / 2 : ℝ) : ℂ) +
            ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.I) * (v : ℂ)) := by
        funext v
        have hz : ((((a + b) / 2 : ℝ) : ℂ) + ((-2 * Real.pi * y : ℝ) : ℂ) * Complex.I) * (v : ℂ) =
            ((-2 * Real.pi * v * y : ℝ) : ℂ) * Complex.I + (((a + b) / 2 : ℝ) : ℂ) * (v : ℂ) := by
          push_cast
          ring
        rw [smul_eq_mul, hz, Complex.exp_add]
        ring
      rw [hfun, integral_sub (hint f₁ _ (hzmem y)) (hint f₂ _ (hzmem y))]
      exact sub_eq_zero.2 (congrFun heq ⟨_, hzmem y⟩)
    have hvol : (f₁ : ℝ → ℂ) =ᵐ[volume] f₂ := by
      filter_upwards [hzero] with x hx
      have hx' : (f₁ x - f₂ x) * Complex.exp ((((a + b) / 2 : ℝ) : ℂ) * (x : ℂ)) = 0 := hx
      exact sub_eq_zero.1 ((mul_eq_zero.1 hx').resolve_right (Complex.exp_ne_zero _))
    exact Lp.ext ((withDensity_absolutelyContinuous _ _).ae_le hvol)

/-- Paper: Proposition 9.2.2.4(2), p. 414. On either endpoint line of a
nondegenerate compact base interval, the interior Mellin integral has an almost-everywhere
limit, whose inverse Fourier transform has the required Sobolev weight.
Deviation: State the compact-base assertion using the weighted source model. -/
theorem scalarIntervalSobolev_boundary_values (a b s : ℝ) (_hab : a < b) (_hs : 0 ≤ s)
    (c : ℝ) (_hc : c ∈ ({a, b} : Set ℝ)) (f : CompactIntervalSobolev volume id a b s) :
    ∃ u : Lp ℂ 2 (volume : Measure ℝ),
      (∀ᵐ y : ℝ ∂volume, Tendsto
        (fun σ : ℝ ↦ ∫ x : ℝ, f x * Complex.exp (verticalPoint σ y * (x : ℂ)))
        (𝓝[Ioo a b] c) (𝓝 (u y))) ∧
      MemLp ((Lp.fourierTransformₗᵢ ℝ ℂ).symm u : ℝ → ℂ) 2
        (volume.withDensity fun x : ℝ ↦ ENNReal.ofReal ((1 + x ^ 2) ^ (s / 2))) := by sorry

/-- Paper: Proposition 9.2.2.4(2), p. 414. At even degree the almost-everywhere endpoint
limits of the moments from order zero through N are the traces of one element of the
Hardy–Sobolev space on that line.
Deviation: State the compact nondegenerate case in the weighted source model. -/
theorem scalarIntervalSobolev_boundary_traces (a b : ℝ) (_hab : a < b) (N : ℕ)
    (c : ℝ) (_hc : c ∈ ({a, b} : Set ℝ))
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) :
    ∃ u : ScalarLineHardySobolev c N,
      ∀ k : Fin (N + 1), ∀ᵐ y : ℝ ∂volume, Tendsto
        (fun σ : ℝ ↦ ∫ x : ℝ, f x * (x : ℂ) ^ (k : ℕ) *
          Complex.exp (verticalPoint σ y * (x : ℂ)))
        (𝓝[Ioo a b] c) (𝓝 (u.val () k y)) := by sorry

/-- Paper: Proposition 9.2.2.4(3), p. 414. For even degree and compact base,
Mellin gives a topological linear equivalence with the closure of the two endpoint traces.
Deviation: Use the endpoint topology of Lemma 9.2.2.2(2). The sampling rule of
Definition 9.2.2.3 does not define a sequence-independent topology as stated. -/
theorem scalarIntervalSobolev_mellin_endpoints (a b : ℝ) (_hab : a ≤ b) (N : ℕ)
    (J : Set ℝ) (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    let E := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
    let σ : Bool → ℝ := fun i ↦ if i then b else a
    ∃ M : E ≃L[ℂ] hardySobolevTraceClosure σ N volume,
      ∀ (f : PositiveRealExponentialDecay J) (u : E),
        (u : ℝ → ℂ) =ᵐ[volume] f.val →
        ∀ i (k : Fin (N + 1)), ((M u).val i k : ℝ → ℂ) =ᵐ[volume]
          fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
            (verticalPoint (σ i) y) := by sorry

/-- The moment kernel, cut off to a measurable set on which the endpoint exponentials
dominate it exponentially, gives a continuous functional on the compact-interval space. -/
private theorem intervalSobolev_moment_functional (a b s : ℝ) (hs : 0 ≤ s) (z : ℂ) (k : ℕ)
    {U : Set ℝ} (hU : MeasurableSet U) {δ K : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    (hlow : ∀ x ∈ U, Real.exp (2 * z.re * x + δ * |x|) ≤
      K * max (Real.exp (2 * a * x)) (Real.exp (2 * b * x))) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
        Λ f = ∫ x : ℝ, f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
  refine weightedL2_moment_functional (continuous_intervalSobolevDensity' a b s)
    (intervalSobolevDensity_pos a b s) z k hU hδ hK fun x hx ↦ (hlow x hx).trans
      (mul_le_mul_of_nonneg_left ?_ hK)
  have h1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (s / 2) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)
  unfold intervalSobolevDensity
  exact le_mul_of_one_le_right (le_max_of_le_left (Real.exp_pos _).le) h1

/-- Paper: Corollary 9.2.2.5(1), p. 414. On a compact base interval, every
interior derivative evaluation has a continuous extension given by the Mellin moment.
Deviation: State it in the weighted source model, which also allows nonintegral degree. -/
theorem scalarIntervalSobolev_eval_interior (a b s : ℝ) (_hs : 0 ≤ s)
    (z : ℂ) (_hz : z.re ∈ Ioo a b) (k : ℕ) :
    ∃ Λ : CompactIntervalSobolev volume id a b s →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  obtain ⟨δ, hδ, hδa, hδb⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ z.re - a ∧ δ ≤ b - z.re :=
    ⟨min (z.re - a) (b - z.re), lt_min (sub_pos.2 _hz.1) (sub_pos.2 _hz.2),
      min_le_left _ _, min_le_right _ _⟩
  change ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
      ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
    ∀ f, Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
      Λ f = ∫ x : ℝ, f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))
  obtain ⟨Λ, hΛ⟩ := intervalSobolev_moment_functional a b s _hs z k MeasurableSet.univ
    (δ := 2 * δ) (K := 1) (mul_pos two_pos hδ) zero_le_one fun x _ ↦ by
      rw [one_mul]
      rcases le_total 0 x with hx | hx
      · rw [abs_of_nonneg hx]
        exact le_max_of_le_right (Real.exp_le_exp.2
          (by nlinarith [mul_nonneg (sub_nonneg.2 hδb) hx]))
      · rw [abs_of_nonpos hx]
        exact le_max_of_le_left (Real.exp_le_exp.2
          (by nlinarith [mul_nonneg (sub_nonneg.2 hδa) (neg_nonneg.2 hx)]))
  refine ⟨Λ, fun f ↦ ?_⟩
  simpa only [Set.indicator_univ, mul_assoc] using hΛ f

/-- Paper: Corollary 9.2.2.5(1), p. 414. The kth complex derivative of the
Mellin integral on the open strip equals the absolutely convergent kth moment.
Deviation: State the compact-base assertion in logarithmic coordinates. -/
theorem scalarIntervalSobolev_iteratedDeriv_mellin (a b s : ℝ) (_hs : 0 ≤ s)
    (f : CompactIntervalSobolev volume id a b s) (k : ℕ) (z : ℂ) (_hz : z.re ∈ Ioo a b) :
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ x : ℝ, f x * Complex.exp (w * (x : ℂ))) z ∧
      Integrable (fun x : ℝ ↦ f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x : ℝ, f x * Complex.exp (w * (x : ℂ))) z =
        ∫ x : ℝ, f x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  refine iteratedDeriv_exp_moment (fun σ hσ n ↦ ?_) k _hz
  obtain ⟨_, hΛ⟩ := scalarIntervalSobolev_eval_interior a b s _hs (σ : ℂ)
    (by rwa [Complex.ofReal_re]) n
  exact (hΛ f).1

/-- A class that agrees almost everywhere with a test profile vanishing outside `U` has the
Mellin derivative of the profile as its moment against the kernel cut off to `U`. -/
private theorem integral_cutoff_moment_eq_iteratedDeriv_mellin
    (f : PositiveRealExponentialDecay univ) {u : ℝ → ℂ} (hu : u =ᵐ[volume] f.val)
    {U : Set ℝ} (hU : ∀ x, x ∉ U → f.val x = 0) (k : ℕ) (z : ℂ) :
    ∫ x : ℝ, u x * U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x =
      iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z := by
  have hint : ∀ σ ∈ Ioo (z.re - 1) (z.re + 1), ∀ n : ℕ, Integrable
      (fun x : ℝ ↦ f.val x * (x : ℂ) ^ n * Complex.exp ((σ : ℂ) * (x : ℂ))) volume :=
    fun σ _ n ↦ integrable_logExponentialDecay_moment f σ n
  have hmel : mellin (fun t ↦ f.val (Real.log t)) =
      fun w : ℂ ↦ ∫ x : ℝ, f.val x * Complex.exp (w * (x : ℂ)) :=
    funext fun w ↦ mellin_comp_log_eq f.val w
  rw [hmel, (iteratedDeriv_exp_moment hint k ⟨by linarith, by linarith⟩).2.2]
  refine integral_congr_ae ?_
  filter_upwards [hu] with x hx
  by_cases hmem : x ∈ U
  · rw [Set.indicator_of_mem hmem, hx, mul_assoc]
  · rw [Set.indicator_of_notMem hmem, hU x hmem, mul_zero, zero_mul, zero_mul]

/-- The squared modulus of the moment kernel. -/
private theorem norm_sq_moment_kernel (k : ℕ) (z : ℂ) (x : ℝ) :
    ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 = x ^ (2 * k) * Real.exp (2 * z.re * x) := by
  have hre : (z * (x : ℂ)).re = z.re * x := by simp
  have h1 : ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ = |x| ^ k * Real.exp (z.re * x) := by
    rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp, hre]
  have h2 : (|x| ^ k) ^ 2 = x ^ (2 * k) := by
    rw [← pow_mul, mul_comm, pow_mul, sq_abs, ← pow_mul]
  have h3 : Real.exp (z.re * x) ^ 2 = Real.exp (2 * z.re * x) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [h1, mul_pow, h2, h3]

/-- For an abscissa in the base interval, the squared moment kernel divided by the
compact-interval density is at most a quotient of powers. -/
private theorem sq_moment_kernel_div_density_le {a b s : ℝ} (k : ℕ) (z : ℂ)
    (hz : z.re ∈ Icc a b) (x : ℝ) :
    ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 * (intervalSobolevDensity a b s x)⁻¹ ≤
      x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
  have hy : 0 < (1 + x ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos (by positivity) _
  have hmpos : 0 < max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) :=
    lt_max_of_lt_left (Real.exp_pos _)
  have hm : Real.exp (2 * z.re * x) ≤ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
    rcases le_total 0 x with hx | hx
    · exact le_max_of_le_right (Real.exp_le_exp.2
        (by nlinarith [mul_nonneg (sub_nonneg.2 hz.2) hx]))
    · exact le_max_of_le_left (Real.exp_le_exp.2
        (by nlinarith [mul_nonneg (sub_nonneg.2 hz.1) (neg_nonneg.2 hx)]))
  rw [norm_sq_moment_kernel]
  unfold intervalSobolevDensity
  rw [mul_inv, mul_assoc, ← mul_assoc (Real.exp _)]
  refine mul_le_mul_of_nonneg_left ?_ (Even.pow_nonneg (even_two_mul k) x)
  refine mul_le_of_le_one_left (inv_nonneg.2 hy.le) ?_
  rw [← div_eq_mul_inv]
  exact (div_le_one hmpos).2 hm

/-- On the half-line where the exponential of an endpoint abscissa is the larger endpoint
weight, the squared moment kernel divided by the density is a quotient of powers. -/
private theorem sq_moment_kernel_div_density_eq {a b s : ℝ} (hab : a ≤ b) (k : ℕ) (z : ℂ)
    {x : ℝ} (hx : (z.re = b ∧ 0 ≤ x) ∨ (z.re = a ∧ x ≤ 0)) :
    ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 * (intervalSobolevDensity a b s x)⁻¹ =
      x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
  have hmax : max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) = Real.exp (2 * z.re * x) := by
    rcases hx with ⟨h, hx⟩ | ⟨h, hx⟩
    · rw [h]
      exact max_eq_right (Real.exp_le_exp.2
        (by nlinarith [mul_nonneg (sub_nonneg.2 hab) hx]))
    · rw [h]
      exact max_eq_left (Real.exp_le_exp.2
        (by nlinarith [mul_nonneg (sub_nonneg.2 hab) (neg_nonneg.2 hx)]))
  rw [norm_sq_moment_kernel]
  unfold intervalSobolevDensity
  rw [hmax, mul_inv, mul_assoc, ← mul_assoc (Real.exp _),
    mul_inv_cancel₀ (Real.exp_pos _).ne', one_mul]

/-- The quotient of powers is integrable exactly above the critical degree: sufficiency. -/
private theorem integrable_pow_mul_rpow_inv {k : ℕ} {s : ℝ} (h : 2 * (k : ℝ) + 1 < s) :
    Integrable (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) volume := by
  have hr : ((Module.finrank ℝ ℝ : ℕ) : ℝ) < s - 2 * k := by
    rw [Module.finrank_self]
    push_cast
    linarith
  refine (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) hr).mono'
    ((measurable_id.pow_const (2 * k)).mul
      ((measurable_const.add (measurable_id.pow_const 2)).pow_const
        (s / 2)).inv).aestronglyMeasurable (ae_of_all _ fun x ↦ ?_)
  have hy : 0 < 1 + x ^ 2 := by positivity
  have h1 : x ^ (2 * k) ≤ (1 + x ^ 2) ^ k := by
    rw [pow_mul]
    exact pow_le_pow_left₀ (sq_nonneg x) (by linarith) k
  have h2 : (1 + x ^ 2) ^ (-(s - 2 * k) / 2) = (1 + x ^ 2) ^ k * ((1 + x ^ 2) ^ (s / 2))⁻¹ := by
    rw [← Real.rpow_natCast (1 + x ^ 2) k, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
    congr 1
    ring
  rw [Real.norm_of_nonneg (mul_nonneg (Even.pow_nonneg (even_two_mul k) x)
    (inv_nonneg.2 (Real.rpow_nonneg hy.le _))), Real.norm_eq_abs, sq_abs, h2]
  exact mul_le_mul_of_nonneg_right h1 (inv_nonneg.2 (Real.rpow_nonneg hy.le _))

/-- The quotient of powers is integrable exactly above the critical degree: necessity. -/
private theorem lt_of_integrableOn_pow_mul_rpow_inv {k : ℕ} {s : ℝ} (hs : 0 ≤ s)
    (h : IntegrableOn (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹) (Ioi 1)) :
    2 * (k : ℝ) + 1 < s := by
  have key : IntegrableOn (fun x : ℝ ↦ x ^ (2 * (k : ℝ) - s)) (Ioi 1) := by
    refine Integrable.mono' (Integrable.const_mul h ((2 : ℝ) ^ (s / 2)))
      (measurable_id.pow_const _).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun x hx ↦ ?_))
    have hx1 : (1 : ℝ) < x := hx
    have hx0 : 0 < x := by linarith
    have hpos : 0 < (1 + x ^ 2) ^ (s / 2) := Real.rpow_pos_of_pos (by positivity) _
    have hcast : ((2 : ℕ) : ℝ) * (s / 2) = s := by
      push_cast
      ring
    have h1 : (1 + x ^ 2) ^ (s / 2) ≤ 2 ^ (s / 2) * x ^ s :=
      calc (1 + x ^ 2) ^ (s / 2) ≤ (2 * x ^ 2) ^ (s / 2) :=
            Real.rpow_le_rpow (by positivity) (by nlinarith) (by linarith)
        _ = 2 ^ (s / 2) * x ^ s := by
            rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast x 2,
              ← Real.rpow_mul hx0.le, hcast]
    have e : x ^ (2 * (k : ℝ) - s) = x ^ (2 * k) / x ^ s := by
      rw [Real.rpow_sub hx0, ← Real.rpow_natCast x (2 * k)]
      push_cast
      rfl
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), e, div_eq_mul_inv, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Even.pow_nonneg (even_two_mul k) x)
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, ← div_eq_inv_mul,
      div_le_iff₀ (Real.rpow_pos_of_pos hx0 s)]
    exact h1
  have hlt := (integrableOn_Ioi_rpow_iff zero_lt_one).1 key
  linarith

/-- At an abscissa of the base interval and above the critical degree, the moment kernel cut
off to a measurable set gives a continuous functional on the compact-interval space. -/
private theorem intervalSobolev_boundary_moment_functional (a b s : ℝ) (k : ℕ) (z : ℂ)
    (hz : z.re ∈ Icc a b) (hk : 2 * (k : ℝ) + 1 < s) {U : Set ℝ} (hU : MeasurableSet U) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
        Λ f = ∫ x : ℝ, f x *
          U.indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
  have hker : Continuous fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) :=
    (Complex.continuous_ofReal.pow k).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  have hρm := (continuous_intervalSobolevDensity' a b s).measurable
  refine weightedL2_pairing volume hρm (intervalSobolevDensity_pos a b s)
    (hker.measurable.indicator hU).aestronglyMeasurable ?_
  refine (integrable_pow_mul_rpow_inv hk).mono'
    (((hker.measurable.indicator hU).norm.pow_const 2).mul hρm.inv).aestronglyMeasurable
    (ae_of_all _ fun x ↦ ?_)
  have hpos := intervalSobolevDensity_pos a b s x
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.2 hpos.le))]
  exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _)
    (norm_indicator_le_norm_self _ _) 2) (inv_nonneg.2 hpos.le)).trans
    (sq_moment_kernel_div_density_le k z hz x)

/-- Below the upper endpoint, the moment kernel cut off above a point gives a continuous
functional on the compact-interval space. -/
private theorem intervalSobolev_cutoff_moment_functional (a b s : ℝ) (hs : 0 ≤ s) {A : ℝ}
    (hA : 1 < A) (z : ℂ) (hz : z.re < b) (k : ℕ) :
    ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
      ∀ f, Integrable (fun x : ℝ ↦ f x * (Ici (-Real.log A)).indicator
          (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
        Λ f = ∫ x : ℝ, f x * (Ici (-Real.log A)).indicator
          (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hbz : 0 < b - z.re := sub_pos.2 hz
  exact intervalSobolev_moment_functional a b s hs z k
    (measurableSet_Ici (a := -Real.log A)) (δ := 2 * (b - z.re))
    (K := Real.exp (4 * (b - z.re) * Real.log A)) (mul_pos two_pos hbz) (Real.exp_pos _).le
    fun x hx ↦ by
      have hx' : -Real.log A ≤ x := hx
      have hle : 2 * z.re * x + 2 * (b - z.re) * |x| ≤
          4 * (b - z.re) * Real.log A + 2 * b * x := by
        rcases le_total 0 x with h0 | h0
        · rw [abs_of_nonneg h0]
          nlinarith [mul_pos hbz hlogA]
        · rw [abs_of_nonpos h0]
          nlinarith [mul_nonneg hbz.le (by linarith : 0 ≤ Real.log A + x)]
      calc Real.exp (2 * z.re * x + 2 * (b - z.re) * |x|)
          ≤ Real.exp (4 * (b - z.re) * Real.log A + 2 * b * x) := Real.exp_le_exp.2 hle
        _ = Real.exp (4 * (b - z.re) * Real.log A) * Real.exp (2 * b * x) := Real.exp_add _ _
        _ ≤ Real.exp (4 * (b - z.re) * Real.log A) *
            max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le

/-- If a continuous functional on the compact-interval space evaluates the Mellin derivative
of each test supported in an open set, then the squared moment kernel is integrable on that
set against the reciprocal density: the functional is integration against a class of the dual
space, and this class agrees with the kernel almost everywhere on the set. -/
private theorem integrableOn_sq_moment_kernel_of_eval (a b s : ℝ) (hab : a ≤ b) (hs : 0 ≤ s)
    (k : ℕ) (z : ℂ) {V : Set ℝ} (hV : IsOpen V)
    (Λ : CompactIntervalSobolev volume id a b s →L[ℂ] ℂ)
    (hΛ : ∀ (f : PositiveRealExponentialDecay univ)
      (u : CompactIntervalSobolev volume id a b s),
      tsupport f.val ⊆ V → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) :
    IntegrableOn (fun x : ℝ ↦ ‖(x : ℂ) ^ k * Complex.exp (z * (x : ℂ))‖ ^ 2 *
      (intervalSobolevDensity a b s x)⁻¹) V := by
  have hρc := continuous_intervalSobolevDensity' a b s
  have hρpos := intervalSobolevDensity_pos a b s
  have hρi : Measurable fun x ↦ (intervalSobolevDensity a b s x)⁻¹ := hρc.measurable.inv
  have hρipos : ∀ x, 0 < (intervalSobolevDensity a b s x)⁻¹ := fun x ↦ inv_pos.2 (hρpos x)
  have hker : Continuous fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) :=
    (Complex.continuous_ofReal.pow k).mul
      (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal))
  obtain ⟨T, hT, -⟩ := scalarIntervalSobolev_dual a b s hab hs
  have hv2 := (weightedL2_norm_eq volume hρi hρipos (T Λ)).1
  have hvloc : LocallyIntegrable (T Λ : ℝ → ℂ) volume := by
    refine locallyIntegrable_iff.2 fun K hK ↦ ?_
    obtain ⟨_, hpair⟩ := weightedL2_pairing volume hρi hρipos
      (w := K.indicator fun _ ↦ (1 : ℂ))
      (measurable_const.indicator hK.measurableSet).aestronglyMeasurable
      (((integrable_indicator_iff hK.measurableSet).2
        (hρc.continuousOn.integrableOn_compact hK (μ := volume))).congr
        (ae_of_all _ fun x ↦ by
          by_cases hx : x ∈ K
          · simp [Set.indicator_of_mem hx]
          · simp [Set.indicator_of_notMem hx]))
    refine (integrable_indicator_iff hK.measurableSet).1
      ((hpair (T Λ)).1.congr (ae_of_all _ fun x ↦ ?_))
    by_cases hx : x ∈ K
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]
  have hloc : LocallyIntegrableOn
      (fun x : ℝ ↦ T Λ x - (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) V volume :=
    (hvloc.sub hker.locallyIntegrable).locallyIntegrableOn V
  have hae := hV.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun g hg hgc hgV ↦ by
    have hg₁ : HasCompactSupport fun x ↦ (g x : ℂ) := hgc.comp_left Complex.ofReal_zero
    have hcont : Continuous fun x ↦ (g x : ℂ) := Complex.continuous_ofReal.comp hg.continuous
    let fT : PositiveRealExponentialDecay univ := ⟨fun x ↦ (g x : ℂ),
      mem_logExponentialDecaySubmodule_of_hasCompactSupport univ hg₁
        (Complex.ofRealCLM.contDiff.comp hg)⟩
    have : IsLocallyFiniteMeasure (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) :=
      IsLocallyFiniteMeasure.withDensity_ofReal hρc
    have hmem : MemLp (fun x ↦ (g x : ℂ)) 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) :=
      hcont.memLp_of_hasCompactSupport hg₁
    have hbase : (volume : Measure ℝ) ≪ volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x) :=
      withDensity_absolutelyContinuous' hρc.measurable.ennreal_ofReal.aemeasurable
        (ae_of_all _ fun x ↦ (ENNReal.ofReal_pos.mpr (hρpos x)).ne')
    let u : CompactIntervalSobolev volume id a b s := hmem.toLp _
    have hu : (u : ℝ → ℂ) =ᵐ[volume] fun x ↦ (g x : ℂ) := hbase.ae_le hmem.coeFn_toLp
    have h1 := hΛ fT u ((tsupport_comp_subset Complex.ofReal_zero g).trans hgV) hu
    have h3 := integral_cutoff_moment_eq_iteratedDeriv_mellin fT
      (u := fun x ↦ (g x : ℂ)) (ae_eq_refl _) (U := univ)
      (fun x hx ↦ absurd (mem_univ x) hx) k z
    have hint1 : Integrable (fun x ↦ (g x : ℂ) * T Λ x) volume :=
      (hT Λ u).1.congr (hu.mono fun x hx ↦ congrArg (· * T Λ x) hx)
    have hint2 : Integrable (fun x : ℝ ↦ (g x : ℂ) *
        ((x : ℂ) ^ k * Complex.exp (z * (x : ℂ)))) volume :=
      (hcont.mul hker).integrable_of_hasCompactSupport hg₁.mul_right
    have heq : ∫ x, (g x : ℂ) * T Λ x =
        ∫ x : ℝ, (g x : ℂ) * ((x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) :=
      calc ∫ x, (g x : ℂ) * T Λ x = ∫ x, u x * T Λ x :=
            (integral_congr_ae (hu.mono fun x hx ↦ congrArg (· * T Λ x) hx)).symm
        _ = Λ u := (hT Λ u).2.symm
        _ = iteratedDeriv k (mellin (fun t ↦ fT.val (Real.log t))) z := h1
        _ = ∫ x : ℝ, (g x : ℂ) * (univ : Set ℝ).indicator
              (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := h3.symm
        _ = _ := by simp only [Set.indicator_univ]
    calc ∫ x, g x • (T Λ x - (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)))
        = ∫ x, ((g x : ℂ) * T Λ x -
            (g x : ℂ) * ((x : ℂ) ^ k * Complex.exp (z * (x : ℂ)))) :=
          integral_congr_ae (ae_of_all _ fun x ↦ by
            simp only [Complex.real_smul, mul_sub])
      _ = 0 := by rw [integral_sub hint1 hint2, heq, sub_self]
  refine hv2.integrableOn.congr
    ((ae_restrict_iff' hV.measurableSet).2 (hae.mono fun x hx hxV ↦ ?_))
  beta_reduce
  rw [sub_eq_zero.1 (hx hxV)]

/-- On supported tests the Mellin derivative evaluation at an endpoint abscissa extends
continuously exactly below the upper endpoint or above the critical degree. -/
private theorem intervalSobolev_cutoff_eval_endpoints_iff (a b A s : ℝ)
    (hab : a ≤ b) (hA : 1 < A) (hs : 0 ≤ s) (k : ℕ) (z : ℂ)
    (hz : z.re ∈ ({a, b} : Set ℝ)) :
    (∃ Λ : CompactIntervalSobolev volume id a b s →L[ℂ] ℂ,
      ∀ (f : PositiveRealExponentialDecay univ) (u : CompactIntervalSobolev volume id a b s),
      tsupport f.val ⊆ Ioi (-Real.log A) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hzI : z.re ∈ Icc a b := by
    rcases hz with h | h
    · rw [h]
      exact ⟨le_rfl, hab⟩
    · rw [show z.re = b from h]
      exact ⟨hab, le_rfl⟩
  constructor
  · rintro ⟨Λ, hΛ⟩
    by_cases hzb : z.re < b
    · exact Or.inl hzb
    · have h : z.re = b := le_antisymm hzI.2 (not_lt.1 hzb)
      have hint := integrableOn_sq_moment_kernel_of_eval a b s hab hs k z (V := Ioi 1)
        isOpen_Ioi Λ fun f u hsupp hu ↦
          hΛ f u (hsupp.trans (Ioi_subset_Ioi (by linarith))) hu
      exact Or.inr (lt_of_integrableOn_pow_mul_rpow_inv hs (hint.congr_fun (fun x hx ↦
        sq_moment_kernel_div_density_eq hab k z
          (Or.inl ⟨h, by linarith [show (1 : ℝ) < x from hx]⟩)) measurableSet_Ioi))
  · intro h
    have hfun : ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b s x)) →L[ℂ] ℂ,
        ∀ f, Integrable (fun x : ℝ ↦ f x * (Ici (-Real.log A)).indicator
            (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x) volume ∧
          Λ f = ∫ x : ℝ, f x * (Ici (-Real.log A)).indicator
            (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
      rcases h with h | h
      · exact intervalSobolev_cutoff_moment_functional a b s hs hA z h k
      · exact intervalSobolev_boundary_moment_functional a b s k z hzI h measurableSet_Ici
    obtain ⟨Λ, hΛ⟩ := hfun
    refine ⟨Λ, fun f u hsupp hu ↦ ?_⟩
    exact (hΛ u).2.trans (integral_cutoff_moment_eq_iteratedDeriv_mellin f hu (fun x hx ↦
      image_eq_zero_of_notMem_tsupport fun h' ↦ hx (Ioi_subset_Ici_self (hsupp h'))) k z)
-- TODO(paper-gap): Corollary 9.2.2.5(2) includes the divergent critical case s = 2k + 1.

/-- Paper: Corollary 9.2.2.5(2), p. 414. At either endpoint, a Mellin derivative
evaluation on the unrestricted tests extends continuously exactly when the degree
exceeds twice the derivative order plus one.
Deviation: The compact weighted model includes a singleton base. The critical
equality in the printed bound is excluded. -/
theorem scalarIntervalSobolev_eval_boundary_iff (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (k : ℕ) (z : ℂ) (_hz : z.re ∈ ({a, b} : Set ℝ)) :
    let E := CompactIntervalSobolev volume id a b s
    (∃ Λ : E →L[ℂ] ℂ, ∀ (f : PositiveRealExponentialDecay univ) (u : E),
      (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔ 2 * (k : ℝ) + 1 < s :=
  by
  intro E
  have hzI : z.re ∈ Icc a b := by
    rcases _hz with h | h
    · rw [h]
      exact ⟨le_rfl, _hab⟩
    · rw [show z.re = b from h]
      exact ⟨_hab, le_rfl⟩
  constructor
  · rintro ⟨Λ, hΛ⟩
    rcases _hz with h | h
    · have hint := integrableOn_sq_moment_kernel_of_eval a b s _hab _hs k z (V := Iio (-1))
        isOpen_Iio Λ fun f u _ hu ↦ hΛ f u hu
      have hG : IntegrableOn (fun x : ℝ ↦ x ^ (2 * k) * ((1 + x ^ 2) ^ (s / 2))⁻¹)
          (Iio (-1)) :=
        hint.congr_fun (fun x hx ↦ sq_moment_kernel_div_density_eq _hab k z
          (Or.inr ⟨h, by linarith [show x < -1 from hx]⟩)) measurableSet_Iio
      refine lt_of_integrableOn_pow_mul_rpow_inv _hs
        (hG.comp_neg_Ioi.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi)
      simp only [Even.neg_pow (even_two_mul k), neg_sq]
    · have hint := integrableOn_sq_moment_kernel_of_eval a b s _hab _hs k z (V := Ioi 1)
        isOpen_Ioi Λ fun f u _ hu ↦ hΛ f u hu
      exact lt_of_integrableOn_pow_mul_rpow_inv _hs (hint.congr_fun (fun x hx ↦
        sq_moment_kernel_div_density_eq _hab k z
          (Or.inl ⟨h, by linarith [show (1 : ℝ) < x from hx]⟩)) measurableSet_Ioi)
  · intro hk
    obtain ⟨Λ, hΛ⟩ := intervalSobolev_boundary_moment_functional a b s k z hzI hk
      MeasurableSet.univ
    refine ⟨Λ, fun f u hu ↦ ?_⟩
    exact (hΛ u).2.trans (integral_cutoff_moment_eq_iteratedDeriv_mellin f hu
      (fun x hx ↦ absurd (mem_univ x) hx) k z)

/-- Paper: Theorem 9.2.2.6(1), p. 415. On a compact base interval of even
degree the supported test closure is the same as the indicator range.
Deviation: Restrict the base to the case where the printed norm is finite on the tests. -/
theorem scalarIntervalSobolev_cutoff_closure (a b A : ℝ) (_hab : a ≤ b) (_hA : 1 < A)
    (N : ℕ) (J : Set ℝ) (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    closure {u : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) |
      ∃ f : PositiveRealExponentialDecay J,
        tsupport f.val ⊆ Ioi (-Real.log A) ∧ (u : ℝ → ℂ) =ᵐ[volume] f.val} =
      {u : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) |
        (u : ℝ → ℂ) =ᵐ[volume] (Ici (-Real.log A)).indicator (u : ℝ → ℂ)} := by sorry

-- TODO(paper-gap): Theorem 9.2.2.6(2) uses the undefined absolute spaces and
-- (9.2.2.28) has the same unspecified growth condition as (9.2.1.7).
-- TODO(paper-gap): Definition 9.2.2.7 refers back to that growth condition.

/-- Paper: Corollary 9.2.2.8(1), p. 415. In the supported space, derivative
evaluations have continuous extensions to all fixed abscissas below the upper endpoint.
Deviation: Use the compact-interval source model and the extension by the indicator. -/
theorem scalarIntervalSobolev_cutoff_eval (a b A : ℝ) (_hab : a ≤ b) (_hA : 1 < A)
    (N k : ℕ) (z : ℂ) (_hz : z.re < b) :
    ∃ Λ : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) →L[ℂ] ℂ,
      ∀ (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))),
        Integrable (fun x : ℝ ↦ (Ici (-Real.log A)).indicator (⇑f) x *
        (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
        Λ f = ∫ x : ℝ, (Ici (-Real.log A)).indicator (⇑f) x *
          (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  change ∃ Λ : Lp ℂ 2 (volume.withDensity fun x ↦
      ENNReal.ofReal (intervalSobolevDensity a b (2 * (N : ℝ)) x)) →L[ℂ] ℂ,
    ∀ f : Lp ℂ 2 (volume.withDensity fun x ↦
        ENNReal.ofReal (intervalSobolevDensity a b (2 * (N : ℝ)) x)),
      Integrable (fun x : ℝ ↦ (Ici (-Real.log A)).indicator (⇑f) x *
        (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) volume ∧
      Λ f = ∫ x : ℝ, (Ici (-Real.log A)).indicator (⇑f) x *
        (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))
  have hlogA : 0 < Real.log A := Real.log_pos _hA
  have hbz : 0 < b - z.re := sub_pos.2 _hz
  obtain ⟨Λ, hΛ⟩ := intervalSobolev_moment_functional a b (2 * (N : ℝ)) (by positivity) z k
    (measurableSet_Ici (a := -Real.log A)) (δ := 2 * (b - z.re))
    (K := Real.exp (4 * (b - z.re) * Real.log A)) (mul_pos two_pos hbz) (Real.exp_pos _).le
    fun x hx ↦ by
      have hx' : -Real.log A ≤ x := hx
      have hle : 2 * z.re * x + 2 * (b - z.re) * |x| ≤
          4 * (b - z.re) * Real.log A + 2 * b * x := by
        rcases le_total 0 x with h0 | h0
        · rw [abs_of_nonneg h0]
          nlinarith [mul_pos hbz hlogA]
        · rw [abs_of_nonpos h0]
          nlinarith [mul_nonneg hbz.le (by linarith : 0 ≤ Real.log A + x)]
      calc Real.exp (2 * z.re * x + 2 * (b - z.re) * |x|)
          ≤ Real.exp (4 * (b - z.re) * Real.log A + 2 * b * x) := Real.exp_le_exp.2 hle
        _ = Real.exp (4 * (b - z.re) * Real.log A) * Real.exp (2 * b * x) := Real.exp_add _ _
        _ ≤ Real.exp (4 * (b - z.re) * Real.log A) *
            max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.exp_pos _).le
  refine ⟨Λ, fun f ↦ ?_⟩
  have hfun : (fun x : ℝ ↦ (Ici (-Real.log A)).indicator (⇑f) x *
      (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) = fun x : ℝ ↦ f x *
      (Ici (-Real.log A)).indicator (fun x : ℝ ↦ (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) x := by
    funext x
    by_cases hx : x ∈ Ici (-Real.log A)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_assoc]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul, zero_mul, mul_zero]
  rw [hfun]
  exact hΛ f

/-- Paper: Corollary 9.2.2.8(1), p. 415. On the open half-plane below the upper
endpoint, the kth derivative of the supported Mellin integral is its kth moment.
Deviation: Use the cutoff in logarithmic coordinates on the compact-base source. -/
theorem scalarIntervalSobolev_cutoff_iteratedDeriv_mellin
    (a b A : ℝ) (_hab : a ≤ b) (_hA : 1 < A) (N k : ℕ)
    (f : CompactIntervalSobolev volume id a b (2 * (N : ℝ))) (z : ℂ) (_hz : z.re < b) :
    let g := (Ici (-Real.log A)).indicator (f : ℝ → ℂ)
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ x : ℝ, g x * Complex.exp (w * (x : ℂ))) z ∧
      Integrable (fun x : ℝ ↦ g x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ))) ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ x : ℝ, g x * Complex.exp (w * (x : ℂ))) z =
        ∫ x : ℝ, g x * (x : ℂ) ^ k * Complex.exp (z * (x : ℂ)) := by
  intro g
  refine iteratedDeriv_exp_moment (α := z.re - 1) (β := b) (fun σ hσ n ↦ ?_) k
    ⟨by linarith, _hz⟩
  obtain ⟨_, hΛ⟩ := scalarIntervalSobolev_cutoff_eval a b A _hab _hA N n (σ : ℂ)
    (by rw [Complex.ofReal_re]; exact hσ.2)
  exact (hΛ f).1

/-- Paper: Corollary 9.2.2.8(2), p. 416. At the upper endpoint a derivative
evaluation of an even-degree supported space is bounded exactly below order N.
Deviation: State bounded extendibility of the evaluation on supported tests in the
compact-interval source model. Here the degree is 2N, so there is no critical equality. -/
theorem scalarIntervalSobolev_cutoff_eval_boundary_iff (a b A : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (N k : ℕ) (z : ℂ) (_hz : z.re = b) :
    (∃ Λ : CompactIntervalSobolev volume id a b (2 * (N : ℝ)) →L[ℂ] ℂ,
      ∀ (f : PositiveRealExponentialDecay univ) (u : CompactIntervalSobolev volume id a b (2 * (N : ℝ))),
        tsupport f.val ⊆ Ioi (-Real.log A) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔ k < N := by
  refine (intervalSobolev_cutoff_eval_endpoints_iff a b A (2 * (N : ℝ)) _hab _hA
    (by positivity) k z (by rw [_hz]; simp)).trans ⟨fun h ↦ ?_, fun h ↦ Or.inr ?_⟩
  · rcases h with h | h
    · exact absurd h (by rw [_hz]; exact lt_irrefl b)
    · have h2 : 2 * k + 1 < 2 * N := by exact_mod_cast h
      omega
  · have h2 : 2 * k + 1 < 2 * N := by omega
    exact_mod_cast h2

/-- Paper: Corollary 9.2.2.8(1)–(2), p. 415. On supported scalar tests every order
extends at a distinct lower endpoint. At the upper endpoint the degree must exceed
twice the derivative order plus one.
Deviation: State the endpoint criterion in the compact weighted model for all nonnegative
degrees. The corollary states the even-degree case, with part (2) on p. 416. -/
theorem scalarIntervalSobolev_cutoff_eval_endpoints_iff (a b A s : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) (k : ℕ) (z : ℂ)
    (_hz : z.re ∈ ({a, b} : Set ℝ)) :
    let E := CompactIntervalSobolev volume id a b s
    (∃ Λ : E →L[ℂ] ℂ, ∀ (f : PositiveRealExponentialDecay univ) (u : E),
      tsupport f.val ⊆ Ioi (-Real.log A) → (u : ℝ → ℂ) =ᵐ[volume] f.val →
        Λ u = iteratedDeriv k (mellin (fun t ↦ f.val (Real.log t))) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by
  intro E
  exact intervalSobolev_cutoff_eval_endpoints_iff a b A s _hab _hA _hs k z _hz

end Interval

section ModulatedInterval

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  (m : G →ₜ* ℝ≥0ˣ) (hm : IsModulation m)

local notation "K" => m.toMonoidHom.ker

local instance instMeasurableSpaceDualKerSec2 : MeasurableSpace (PontryaginDual K) := borel _

/-- Paper: Definition 9.2.2.9, p. 416. For a compact base interval the
canonical group-side Sobolev space is weighted L² for the canonical Haar measure.
Deviation: Only compact base intervals give a finite norm on all the stated tests.
Use `intervalSobolevENorm` for the supremum expression on other intervals. -/
abbrev ModulatedIntervalSobolev (a b s : ℝ) :=
  CompactIntervalSobolev (canonicalModulatedHaar m hm) (logModule m) a b s

/-- Paper: Lemma 9.2.2.10(1), p. 416. On a compact base interval each open-interval
test space containing the base embeds continuously and densely in the weighted space.
Deviation: This states the compact case, with the canonical choice of Haar measure. -/
theorem modulatedIntervalSobolev_dense
    (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) (J : Set ℝ)
    (_hJ : IsOpen J) (_hInt : OrdConnected J) (_hsub : Icc a b ⊆ J) :
    ∃ j : ModulatedExponentialDecay m J →L[ℂ] ModulatedIntervalSobolev m hm a b s,
      Injective j ∧ DenseRange j ∧
      ∀ f, (j f : G → ℂ) =ᵐ[canonicalModulatedHaar m hm] f.val := by sorry

/-- Paper: Lemma 9.2.2.10(1), p. 416. For a compact base interval and an even degree,
pullback to split coordinates followed by the unitary kernel Fourier transform
identifies the space with the completed Hilbert tensor product.
Deviation: The pullback in (9.2.2.32) lands in physical kernel coordinates
before applying the compact Fourier transform. Use the weighted norm of (9.2.2.34). -/
theorem modulatedIntervalSobolev_tensor (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace K] [BorelSpace K] (μ₁ : Measure K) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (ν₁ : Measure (PontryaginDual K)) (hν₁ : IsLCAPlancherelMeasure μ₁ ν₁)
    (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
    let U := Classical.choose (lcaFourier_unitary μ₁ ν₁ hν₁).exists
    let E := ModulatedIntervalSobolev m hm a b (2 * (N : ℝ))
    let E₀ := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
    ∃ P : E ≃ₗᵢ[ℂ] UniformSpace.Completion (E₀ ⊗[ℂ] Lp ℂ 2 ν₁),
      ∀ (f : E₀) (g : Lp ℂ 2 μ₁) (u : E),
        (fun p : K × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[μ₁.prod positiveRealHaar]
          (fun p ↦ f (Real.log (p.2.val : ℝ)) * g p.1) →
        P u = ↑(f ⊗ₜ[ℂ] U g) := by sorry

/-- Paper: Lemma 9.2.2.10(1), p. 416. For a compact base interval and an even degree,
pullback to split coordinates followed by the unitary kernel Fourier transform and dual inversion
identifies the space with the completed Hilbert tensor product.
Deviation: The pullback in (9.2.2.32) lands in physical kernel coordinates
before applying the compact Fourier transform at the inverse character, as in (9.2.1.25).
Use the weighted norm of (9.2.2.34). -/
theorem modulatedIntervalSobolev_tensor_isotype (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace K] [BorelSpace K] (μ₁ : Measure K) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (ν₁ : Measure (PontryaginDual K)) (hν₁ : IsLCAPlancherelMeasure μ₁ ν₁)
    (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    letI : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
    letI : BorelSpace (PontryaginDual K) := ⟨rfl⟩
    letI : ν₁.IsHaarMeasure := hν₁.1
    letI : ν₁.Regular := hν₁.2.1
    let U := Classical.choose (lcaFourier_unitary μ₁ ν₁ hν₁).exists
    let invert := Lp.compMeasurePreserving (E := ℂ) (p := 2) Inv.inv
      (Measure.measurePreserving_inv ν₁)
    let E := ModulatedIntervalSobolev m hm a b (2 * (N : ℝ))
    let E₀ := CompactIntervalSobolev volume id a b (2 * (N : ℝ))
    ∃ P : E ≃ₗᵢ[ℂ] UniformSpace.Completion (E₀ ⊗[ℂ] Lp ℂ 2 ν₁),
      ∀ (f : E₀) (g : Lp ℂ 2 μ₁) (u : E),
        (fun p : K × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[μ₁.prod positiveRealHaar]
          (fun p ↦ f (Real.log (p.2.val : ℝ)) * g p.1) →
        P u = ↑(f ⊗ₜ[ℂ] invert (U g)) := by sorry

/-- Paper: Lemma 9.2.2.10(1), p. 416. For compact bases and even degrees,
the scalar Mellin transform on split elementary tensors acts by vertical derivative
traces and the Fourier transform acts on the kernel factor.
Deviation: Use the two endpoint traces of Lemma 9.2.2.2(2) and the Hilbert norm
which sums their squared norms. The compact Fourier transform follows the positive
character convention of (9.2.1.25), so the character in `lcaFourier` is inverted. -/
theorem modulatedIntervalSobolev_mellin_endpoints (τ : ℝ≥0ˣ →ₜ* G) (_hτ : RightInverse τ m)
    [MeasurableSpace K] [BorelSpace K] (μ₁ : Measure K) [μ₁.IsHaarMeasure] (_hμ₁ : μ₁ univ = 1)
    (ν₁ : Measure (PontryaginDual K)) (_hν₁ : IsLCAPlancherelMeasure μ₁ ν₁)
    (a b : ℝ) (_hab : a ≤ b) (N : ℕ) :
    let E := ModulatedIntervalSobolev m hm a b (2 * (N : ℝ))
    let σ : Bool → ℝ := fun i ↦ if i then b else a
    let H := hardySobolevTraceClosure σ N volume
    ∃ M : E ≃L[ℂ] UniformSpace.Completion (H ⊗[ℂ] Lp ℂ 2 ν₁),
      ∀ (f : PositiveRealExponentialDecay univ) (g : Lp ℂ 2 μ₁) (u : E),
        Integrable (g : K → ℂ) μ₁ →
        (fun p : K × ℝ≥0ˣ ↦ u ((p.1 : G) * τ p.2)) =ᵐ[μ₁.prod positiveRealHaar]
          (fun p ↦ f.val (Real.log (p.2.val : ℝ)) * g p.1) →
        ∃ (v : H) (w : Lp ℂ 2 ν₁),
          (∀ i (k : Fin (N + 1)), (v.val i k : ℝ → ℂ) =ᵐ[volume]
            fun y ↦ iteratedDeriv (k : ℕ) (mellin (fun t ↦ f.val (Real.log t)))
              (verticalPoint (σ i) y)) ∧
          (w : PontryaginDual K → ℂ) =ᵐ[ν₁] (fun χ ↦ lcaFourier μ₁ g χ⁻¹) ∧
          M u = ↑(v ⊗ₜ[ℂ] w) := by sorry

/-- Paper: Lemma 9.2.2.10(2), p. 417. For a compact base the norm of a completed
element is the square root of the integral with the maximum endpoint weight.
Deviation: The formula holds for the L² representative in the completed space. -/
theorem modulatedIntervalSobolev_norm (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s)
    (f : ModulatedIntervalSobolev m hm a b s) :
    let μ := canonicalModulatedHaar m hm
    let integrand := fun g ↦ ‖f g‖ ^ 2 * intervalSobolevDensity a b s (logModule m g)
    Integrable integrand μ ∧ ‖f‖ = Real.sqrt (∫ g, integrand g ∂μ) ∧
      intervalSobolevENorm μ (logModule m) (Icc a b) s (⇑f) = ENNReal.ofReal ‖f‖ := by
  intro μ integrand
  have hDpos : ∀ x : ℝ, 0 < intervalSobolevDensity a b s x := fun x ↦
    mul_pos (lt_max_of_lt_left (Real.exp_pos _)) (Real.rpow_pos_of_pos (by positivity) _)
  -- Shrinking the endpoints inside `[a, b]` only lowers the density.
  have hmono : ∀ a' ∈ Icc a b, ∀ b' ∈ Icc a b, ∀ x : ℝ,
      intervalSobolevDensity a' b' s x ≤ intervalSobolevDensity a b s x := by
    intro a' ha' b' hb' x
    have key : ∀ c ∈ Icc a b,
        Real.exp (2 * c * x) ≤ max (Real.exp (2 * a * x)) (Real.exp (2 * b * x)) := by
      intro c hc
      rcases le_total 0 x with hx | hx
      · exact le_max_of_le_right (Real.exp_le_exp.2 (by nlinarith [hc.2]))
      · exact le_max_of_le_left (Real.exp_le_exp.2 (by nlinarith [hc.1]))
    exact mul_le_mul_of_nonneg_right (max_le (key a' ha') (key b' hb')) (by positivity)
  have hcont : Continuous fun g : G ↦ ((m g).val : ℝ) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  have hDmeas : Measurable fun g : G ↦ intervalSobolevDensity a b s (logModule m g) := by
    have hlog : Measurable (logModule m) := Real.measurable_log.comp hcont.measurable
    unfold intervalSobolevDensity
    fun_prop
  have hρ : AEMeasurable (fun g ↦ (intervalSobolevDensity a b s (logModule m g)).toNNReal) μ :=
    hDmeas.real_toNNReal.aemeasurable
  have hf2 : Integrable (fun g ↦ ‖f g‖ ^ 2)
      (μ.withDensity fun g ↦
        ((intervalSobolevDensity a b s (logModule m g)).toNNReal : ℝ≥0∞)) := by
    have h := (Lp.memLp f).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
    exact h
  have hsmul : ∀ g, (intervalSobolevDensity a b s (logModule m g)).toNNReal • ‖f g‖ ^ 2 =
      integrand g := fun g ↦ by
    rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hDpos _).le, mul_comm]
  have hint : ∫ g, integrand g ∂μ = ∫ g, ‖f g‖ ^ 2
      ∂μ.withDensity fun g ↦
        ((intervalSobolevDensity a b s (logModule m g)).toNNReal : ℝ≥0∞) := by
    rw [integral_withDensity_eq_integral_smul₀ hρ]
    exact integral_congr_ae (Eventually.of_forall fun g ↦ (hsmul g).symm)
  refine ⟨?_, ?_, ?_⟩
  · exact ((integrable_withDensity_iff_integrable_smul₀ hρ).1 hf2).congr
      (Eventually.of_forall hsmul)
  · rw [hint, Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm two_ne_zero
      ENNReal.ofNat_ne_top (Lp.memLp f), ENNReal.toReal_ofReal (by positivity),
      Real.sqrt_eq_rpow]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, one_div]
    rfl
  · have hE : intervalSobolevENorm μ (logModule m) (Icc a b) s (⇑f) =
        eLpNorm f 2 (μ.withDensity fun g ↦
          ENNReal.ofReal (intervalSobolevDensity a b s (logModule m g))) := by
      unfold intervalSobolevENorm
      refine le_antisymm (iSup₂_le fun a' b' ↦ eLpNorm_mono_measure _ (withDensity_mono
        (Eventually.of_forall fun g ↦ ENNReal.ofReal_le_ofReal (hmono _ a'.2 _ b'.2 _)))) ?_
      exact le_iSup₂_of_le (⟨a, left_mem_Icc.2 _hab⟩ : Icc a b) ⟨b, right_mem_Icc.2 _hab⟩ le_rfl
    rw [hE, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top f)]
    rfl

/-- Paper: Lemma 9.2.2.10(3)(a), p. 417. The right half-line supremum can
be indexed using the left endpoint and one varying abscissa.
Deviation: Use extended values and read `t` in (9.2.2.35) as the module of g. -/
theorem modulatedIntervalSobolev_enorm_Ici (a s : ℝ) (_hs : 0 ≤ s)
    (f : ModulatedExponentialDecay m univ) :
    let μ := canonicalModulatedHaar m hm
    intervalSobolevENorm μ (logModule m) (Ici a) s f.val =
      ⨆ σ : Ici a, eLpNorm f.val 2 (μ.withDensity fun g ↦
        ENNReal.ofReal (intervalSobolevDensity a σ s (logModule m g))) :=
  intervalSobolevENorm_Ici _ (logModule m) a s f.val

/-- Paper: Lemma 9.2.2.10(3)(b), p. 417. The left half-line supremum can
be indexed using one varying abscissa and the right endpoint.
Deviation: Use extended values for the supremum in (9.2.2.36). -/
theorem modulatedIntervalSobolev_enorm_Iic (b s : ℝ) (_hs : 0 ≤ s)
    (f : ModulatedExponentialDecay m univ) :
    let μ := canonicalModulatedHaar m hm
    intervalSobolevENorm μ (logModule m) (Iic b) s f.val =
      ⨆ σ : Iic b, eLpNorm f.val 2 (μ.withDensity fun g ↦
        ENNReal.ofReal (intervalSobolevDensity σ b s (logModule m g))) :=
  intervalSobolevENorm_Iic _ (logModule m) b s f.val

-- TODO(paper-gap): As in Proposition 9.2.1.8, the test pairing and the
-- reciprocal-density norm are not defined on all the stated inputs.

/-- Paper: Proposition 9.2.2.11, p. 417. The weighted space pairs with the
reciprocal-density space via the unweighted integral and represents its strong dual.
Deviation: Use the Haar measure from the proposition on both sides. The test pairing
on all of S_J × S_J and the reciprocal-norm completion of all of S_J can fail. The paper
assumes a < b, but §10.2–10.4 apply (9.2.2.42) to I = [−α, α] with α ≥ 0, so the one-point
base is included. -/
theorem modulatedIntervalSobolev_dual (_hm : IsModulation m)
    (μ : Measure G) [μ.IsHaarMeasure] (a b s : ℝ) (_hab : a ≤ b) (_hs : 0 ≤ s) :
    ∃! T : StrongDual ℂ (CompactIntervalSobolev μ (logModule m) a b s) ≃ₗᵢ[ℂ]
        CompactIntervalSobolev μ (logModule m) a b s true,
      ∀ Λ f, Integrable (fun g ↦ f g * T Λ g) μ ∧
        Λ f = ∫ g, f g * T Λ g ∂μ := by
  have hlog : Measurable (fun g ↦ Real.log ((m g).val : ℝ)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).measurable.log
  have hρ := (continuous_intervalSobolevDensity' a b s).measurable.comp hlog
  exact weightedL2_dual μ hρ hρ.inv (fun g ↦ intervalSobolevDensity_pos a b s _)
    (fun g ↦ inv_pos.mpr (intervalSobolevDensity_pos a b s _))
    (fun g ↦ mul_inv_cancel₀ (intervalSobolevDensity_pos a b s _).ne')

/-- For a nonnegative degree, the compact-interval density dominates the exponential of its
upper endpoint. -/
private theorem exp_le_intervalSobolevDensity (a b s : ℝ) (hs : 0 ≤ s) (x : ℝ) :
    Real.exp (2 * b * x) ≤ intervalSobolevDensity a b s x := by
  have h1 : (1 : ℝ) ≤ (1 + x ^ 2) ^ (s / 2) :=
    Real.one_le_rpow (by nlinarith [sq_nonneg x]) (by linarith)
  unfold intervalSobolevDensity
  exact (le_max_right _ _).trans
    (le_mul_of_one_le_right (le_max_of_le_left (Real.exp_pos _).le) h1)
-- TODO(paper-gap): Corollary 9.2.2.12(1) omits the kernel character in the integral
-- for a general isotype and uses m rather than k for the power of the logarithm.

/-- Paper: Corollary 9.2.2.12(1), p. 418. Each isotype has a bounded
interior derivative evaluation on the supported compact-interval space.
Deviation: Use the weighted source model and the intrinsic quasi-character for
the chosen isotype. The printed formula corresponds to the trivial character. -/
theorem modulatedIntervalSobolev_cutoff_eval (a b A s : ℝ)
    (_hA : 1 < A) (_hs : 0 ≤ s) (z : ℂ) (_hz : z.re ∈ Ioo a b) (k : ℕ)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    let U := (logModule m) ⁻¹' Ici (-Real.log A)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ z
    ∃! Λ : E →L[ℂ] ℂ,
      ∀ f : E, Integrable (fun g ↦ U.indicator (⇑f) g * (logModule m g : ℂ) ^ k * c g) μ ∧
        Λ f = ∫ g, U.indicator (⇑f) g * (logModule m g : ℂ) ^ k * c g ∂μ := by
  intro μ E U c
  have hμ : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  obtain ⟨Λ, hΛ⟩ := modulated_cutoff_moment_functional m hm μ
    (continuous_intervalSobolevDensity' a b s).measurable
    (exp_le_intervalSobolevDensity a b s _hs) _hA z _hz.2 k χ _hχ
  exact ⟨Λ, hΛ, fun Λ' hΛ' ↦ ContinuousLinearMap.ext fun f ↦ (hΛ' f).2.trans (hΛ f).2.symm⟩

/-- Paper: Corollary 9.2.2.12(1), p. 418. In the norm-twist coordinate of a unitary
quasi-character, the kth derivative of the cutoff Mellin integral equals its kth moment.
Deviation: The intrinsic quasi-character includes the character missing in (9.2.2.43),
and the cutoff gives convergence throughout the open half-plane below the upper endpoint. -/
theorem modulatedIntervalSobolev_cutoff_iteratedDeriv_mellin (a b A s : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) (k : ℕ)
    (f : ModulatedIntervalSobolev m hm a b s) (z : ℂ) (_hz : z.re < b)
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let u := ((logModule m) ⁻¹' Ici (-Real.log A)).indicator (f : G → ℂ)
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    AnalyticAt ℂ (fun w : ℂ ↦ ∫ g, u g * c w g ∂μ) z ∧
      Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ k * c z g) μ ∧
      iteratedDeriv k (fun w : ℂ ↦ ∫ g, u g * c w g ∂μ) z =
        ∫ g, u g * (logModule m g : ℂ) ^ k * c z g ∂μ := by
  intro μ u c
  have hμ : μ.IsHaarMeasure :=
    (Classical.choose_spec (existsUnique_canonicalModulatedHaar m hm).exists).1
  have hint : ∀ σ ∈ Ioo (z.re - 1) b, ∀ n : ℕ,
      Integrable (fun g ↦ u g * (logModule m g : ℂ) ^ n *
        quasiCharacterNormTwist m.toMonoidHom m.continuous χ (σ : ℂ) g) μ := fun σ hσ n ↦ by
    obtain ⟨_, hΛ⟩ := modulated_cutoff_moment_functional m hm μ
      (continuous_intervalSobolevDensity' a b s).measurable
      (exp_le_intervalSobolevDensity a b s _hs) _hA (σ : ℂ)
      (by rw [Complex.ofReal_re]; exact hσ.2) n χ _hχ
    exact (hΛ f).1
  exact iteratedDeriv_normTwist_moment m μ χ hint k
    (show z.re ∈ Ioo (z.re - 1) b from ⟨by linarith, _hz⟩)
-- TODO(paper-gap): Corollary 9.2.2.12(2) includes the divergent critical case
-- s = 2k + 1 at the upper endpoint, even for the trivial kernel character.

/-- Paper: Corollary 9.2.2.12(2), p. 418. A Mellin derivative evaluation in any
isotype extends from supported tests at the endpoints of the compact base.
Deviation: At the upper endpoint the condition is strict. At a distinct lower
endpoint the cutoff allows all orders. The modulation is onto as in §9.2. -/
theorem modulatedIntervalSobolev_cutoff_eval_endpoints_iff (_hms : Surjective m)
    (a b A s : ℝ) (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) (k : ℕ)
    (z : ℂ) (_hz : z.re ∈ ({a, b} : Set ℝ))
    (χ : QuasiCharacter G) (_hχ : ∀ g, ‖χ g‖ = 1) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    let c := quasiCharacterNormTwist m.toMonoidHom m.continuous χ
    (∃ Λ : E →L[ℂ] ℂ, ∀ (f : ModulatedExponentialDecay m univ) (u : E),
      tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log A) → (u : G → ℂ) =ᵐ[μ] f.val →
        Λ u = iteratedDeriv k (fun w ↦ modulatedFourierMellin m univ hm μ f.val (c w)) z) ↔
      z.re < b ∨ 2 * (k : ℝ) + 1 < s := by sorry

/-- Paper: Theorem 9.2.2.13(1), p. 418. For compact bases and surjective module,
the support-restricted tests are dense in the indicator range.
Deviation: State the range as the fixed points of the cutoff on representatives.
A discrete modulation can have positive Haar mass at the cutoff itself. -/
theorem modulatedIntervalSobolev_cutoff_closure (_hms : Surjective m) (a b A s : ℝ)
    (_hab : a ≤ b) (_hA : 1 < A) (_hs : 0 ≤ s) :
    let μ := canonicalModulatedHaar m hm
    let E := ModulatedIntervalSobolev m hm a b s
    closure {u : E | ∃ f : ModulatedExponentialDecay m univ,
      tsupport f.val ⊆ (logModule m) ⁻¹' Ioi (-Real.log A) ∧
        (u : G → ℂ) =ᵐ[μ] f.val} =
      {u : E | (u : G → ℂ) =ᵐ[μ] ((logModule m) ⁻¹' Ici (-Real.log A)).indicator (u : G → ℂ)} :=
  by sorry

-- TODO(paper-gap): Theorem 9.2.2.13(2) uses the unspecified analytic space of
-- Definition 9.2.2.3. The cited Lemma 9.2.2.10(1) treats only even degrees.
-- TODO(paper-gap): Theorem 9.2.2.13(3) gives the unrestricted tensor space as
-- right target even though the induced Mellin map on that arrow has one-sided source.

end ModulatedInterval

end RiemannMasullo
