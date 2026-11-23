module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec6
import all RiemannMasullo.Ch03_IdelicZeta.Sec2
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.ZetaLab.HardyFirstZero.FirstZero

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

/-- Haar translation acts on the Mellin moments through the binomial expansion
of the shifted logarithm. -/
private theorem translated_mellin_moment {G : Type*} [CommGroup G] [TopologicalSpace G]
    [MeasurableSpace G] [IsTopologicalGroup G] [BorelSpace G]
    (μ : Measure G) [μ.IsMulLeftInvariant] (L : G → ℂ)
    (hL : ∀ x y, L (x * y) = L x + L y) (c : G →ₜ* ℂ) (f : G → ℂ)
    (hf : ∀ i : ℕ, Integrable (fun x ↦ f x * c x * (L x) ^ i) μ)
    (y : G) (k : ℕ) :
    (∫ x, f (y⁻¹ * x) * c x * (L x) ^ k ∂μ) =
      c y * ∑ i ∈ Finset.range (k + 1), (L y) ^ (k - i) * (k.choose i : ℂ) *
        (∫ x, f x * c x * (L x) ^ i ∂μ) := by
  let A (i : ℕ) := (L y) ^ (k - i) * (k.choose i : ℂ)
  let P (i : ℕ) (x : G) := f x * c x * (L x) ^ i
  have hchange :
      (∫ x, f (y⁻¹ * x) * c x * (L x) ^ k ∂μ) =
        ∫ x, f x * (c y * c x) * (L x + L y) ^ k ∂μ := by
    rw [← integral_mul_left_eq_self (μ := μ) (fun x ↦ f (y⁻¹ * x) * c x * (L x) ^ k) y]
    exact integral_congr_ae (ae_of_all _ fun x ↦ by
      dsimp only
      rw [inv_mul_cancel_left, map_mul, hL, add_comm (L y)])
  rw [hchange]
  change _ = c y * ∑ i ∈ Finset.range (k + 1), A i * (∫ x, P i x ∂μ)
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun i _ ↦ (hf i).const_mul (A i)), ← integral_const_mul]
  apply integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  rw [add_pow, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by dsimp [A, P]; ring

/-- The two real twists at abscissas one unit to either side dominate
every fixed logarithmic moment of a rational decay test. -/
private theorem rational_decay_moment_integrable (f : ModulatedExponentialDecay m𝔽(ℚ) univ) (z : ℂ) (k : ℕ) :
    Integrable (fun x ↦ f.val x * ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) z x *
      (logNorm(ℚ) x : ℂ) ^ k) μ(ℚ) := by
  let m := m𝔽(ℚ)
  let c := ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ)) z
  let L (x : C𝔽(ℚ)) : ℂ := logNorm(ℚ) x
  let T (a : ℝ) := modulatedExponentialDecayTwist m univ ⟨a, mem_univ a⟩ f
  have h₁ := (SchwartzBruhat.integrable μ(ℚ) (T (z.re + 1))).norm
  have h₂ := (SchwartzBruhat.integrable μ(ℚ) (T (z.re - 1))).norm
  have hf0 : AEStronglyMeasurable f.val μ(ℚ) :=
    (SchwartzBruhat.integrable μ(ℚ) (T 0)).aestronglyMeasurable.congr (ae_of_all _ fun x ↦
      (modulatedExponentialDecayTwist_apply m univ ⟨0, mem_univ _⟩ f x).trans (by simp))
  have hL : Continuous L := by
    apply Complex.continuous_ofReal.comp
    exact (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  refine ((h₁.add h₂).const_mul (k.factorial : ℝ)).mono'
    ((hf0.mul (c).continuous.aestronglyMeasurable).mul (hL.pow k).aestronglyMeasurable)
    (ae_of_all _ fun x ↦ ?_)
  let r : ℝ := (m x).val
  have hr : 0 < r := NNReal.coe_pos.mpr (Units.zero_lt (m x))
  have hTw (a : ℝ) : ‖(T a).val x‖ = r ^ a * ‖f.val x‖ := by
    refine (congrArg norm (modulatedExponentialDecayTwist_apply m univ ⟨a, mem_univ _⟩ f x)).trans ?_
    rw [norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg hr.le _)]
  have hc : ‖c x‖ = r ^ z.re := by
    change ‖(1 : ℂ) * (r : ℂ) ^ z‖ = _
    rw [one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hr]
  have hp : |Real.log r| ^ k ≤ (k.factorial : ℝ) * (r + r⁻¹) := by
    have h := Real.pow_div_factorial_le_exp |Real.log r| (abs_nonneg _) k
    have hk : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_le_iff₀ hk] at h
    have he : Real.exp |Real.log r| ≤ r + r⁻¹ := by
      rcases le_total 0 (Real.log r) with h | h
      · rw [abs_of_nonneg h, Real.exp_log hr]
        exact le_add_of_nonneg_right (inv_nonneg.mpr hr.le)
      · rw [abs_of_nonpos h, Real.exp_neg, Real.exp_log hr]
        exact le_add_of_nonneg_left hr.le
    exact h.trans ((mul_le_mul_of_nonneg_right he hk.le).trans_eq (mul_comm _ _))
  change ‖f.val x * c x * (L x) ^ k‖ ≤
    (k.factorial : ℝ) * (‖(T (z.re + 1)).val x‖ + ‖(T (z.re - 1)).val x‖)
  rw [norm_mul, norm_mul, hc, norm_pow, Complex.norm_real, Real.norm_eq_abs, hTw, hTw,
    Real.rpow_add hr, Real.rpow_sub hr, Real.rpow_one]
  calc
    ‖f.val x‖ * r ^ z.re * |Real.log r| ^ k ≤
      ‖f.val x‖ * r ^ z.re * ((k.factorial : ℝ) * (r + r⁻¹)) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
    _ = _ := by ring

/-- The rational order comparison is the one used for the strip index in
the proof of the ambient pairing refutation in Sec4a. -/
private theorem rational_biorthogonal_zero :
    ∃ z : ℂ, 0 < (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) z).untop₀.toNat := by
  obtain ⟨t, _, ht⟩ := HardyFirstZero.first_zero_on_line
  let z : ℂ := 1 / 2 + t * Complex.I
  have hne : z ≠ 1 := by
    intro he
    have := congrArg Complex.re he
    norm_num [z] at this
  have ha := analyticOn_riemannZeta z hne
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have he := meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual C𝔽(ℚ))
    hm (fun s ↦ by rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property])
    (s := z) (by norm_num [z])
  have hz2 : meromorphicOrderAt riemannZeta (2 : ℂ) = 0 := by
    have h := analyticOn_riemannZeta 2 (by norm_num : (2 : ℂ) ≠ 1)
    rw [h.meromorphicOrderAt_eq, h.analyticOrderAt_eq_zero.mpr
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))]
    rfl
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ (2 : ℂ)) (mem_univ z) (by rw [hz2]; simp)
  have hpos : analyticOrderAt riemannZeta z ≠ 0 := ha.analyticOrderAt_ne_zero.mpr ht
  refine ⟨z, ?_⟩
  rw [← he, ha.meromorphicOrderAt_eq]
  rw [ha.meromorphicOrderAt_eq] at hfin
  generalize analyticOrderAt riemannZeta z = k at hfin hpos ⊢
  cases k using ENat.recTopCoe with
  | top => simp at hfin
  | coe n =>
    have hn : n ≠ 0 := by simpa using hpos
    simpa using Nat.pos_of_ne_zero hn

private theorem rational_norm_haar_univ : μ(ℚ) univ = ⊤ := by
  let m := m𝔽(ℚ)
  let L := logNorm(ℚ)
  have hc : Continuous L := by
    exact (NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
      fun x ↦ NNReal.coe_ne_zero.mpr (m x).ne_zero
  have hs : Surjective L := by
    intro r
    let a : ℝ≥0 := ⟨Real.exp r, (Real.exp_pos r).le⟩
    let u := Units.mk0 a (NNReal.coe_ne_zero.mp (Real.exp_pos r).ne')
    obtain ⟨x, hx⟩ := ratIdeleNormSection_class_rightInverse.surjective u
    refine ⟨x, ?_⟩
    change Real.log (((ideleClassNorm ℚ x).val : ℝ)) = r
    rw [hx]
    exact Real.log_exp r
  have : NoncompactSpace C𝔽(ℚ) := ⟨fun h ↦
    NoncompactSpace.noncompact_univ (X := ℝ)
      (by simpa only [image_univ, hs.range_eq] using h.image hc)⟩
  exact measure_univ_of_isMulLeftInvariant μ(ℚ)

/-- Paper: (10.4.3.5), p. 466. A normalized translate of the test for the
highest jet at a certified rational zeta zero has the same biorthogonal
pairings. Uniqueness would make the test times its norm character a constant
integrable function on the noncompact idele class group, contrary to the
nonzero pairing at the highest jet. -/
theorem Printed.spectralSchwartzBiorthogonal_unique_false :
    ¬ Printed.spectralSchwartzBiorthogonal_unique := by
  classical
  intro h
  obtain ⟨z, hz⟩ := rational_biorthogonal_zero
  let m := m𝔽(ℚ)
  let χ := ideleClassNormTwist (1 : PontryaginDual C𝔽(ℚ))
  let L (x : C𝔽(ℚ)) : ℂ := logNorm(ℚ) x
  let N (w : ℂ) := (meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) (0 + w)).untop₀.toNat
  let J := {j : ℂ × ℕ // j.2 < N j.1}
  let n := N z - 1
  have hzN : 0 < N z := by simpa [N] using hz
  let j₀ : J := ⟨(z, n), by change n < N z; dsimp [n]; omega⟩
  let ι : (ideleClassNorm ℚ).ker →ₜ* C𝔽(ℚ) := ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩
  let ω := (1 : PontryaginDual C𝔽(ℚ)).comp ι
  let E := ↥(modulatedDecayIsotype m univ (mem_univ 0) ω)
  let M (f : C𝔽(ℚ) → ℂ) (w : ℂ) (k : ℕ) := ∫ g, f g * χ w g * (L g) ^ k ∂μ(ℚ)
  let P (ψ : J → E) := ∀ j j' : J, M (ψ j').val.val j.val.1 j.val.2 = if j = j' then 1 else 0
  have hex := h ℚ (1 : PontryaginDual C𝔽(ℚ)) 0
  simp only [Complex.ofReal_zero, zero_add] at hex
  change ∃! ψ : J → E, P ψ at hex
  obtain ⟨ψ, hψ, huniq⟩ := hex
  let f := (ψ j₀).val
  let c := χ z
  have hL (x y : C𝔽(ℚ)) : L (x * y) = L x + L y := by
    change (Real.log ((m (x * y)).val : ℝ) : ℂ) = _
    rw [map_mul, Units.val_mul, NNReal.coe_mul, Real.log_mul, Complex.ofReal_add]
    · exact NNReal.coe_ne_zero.mpr (m x).ne_zero
    · exact NNReal.coe_ne_zero.mpr (m y).ne_zero
  have hc (w : ℂ) (y : C𝔽(ℚ)) : χ w y ≠ 0 :=
    ((Group.isUnit y).map (χ w)).ne_zero
  have hMtrans (y : C𝔽(ℚ)) (j : J) :
      M (fun x ↦ f.val (y⁻¹ * x)) j.val.1 j.val.2 = c y * (if j = j₀ then 1 else 0) := by
    rw [show M (fun x ↦ f.val (y⁻¹ * x)) j.val.1 j.val.2 =
        χ j.val.1 y * ∑ i ∈ Finset.range (j.val.2 + 1),
          (L y) ^ (j.val.2 - i) * (j.val.2.choose i : ℂ) * M f.val j.val.1 i
      from translated_mellin_moment μ(ℚ) L hL (χ j.val.1) f.val
        (rational_decay_moment_integrable f j.val.1) y j.val.2]
    have hlow (i : ℕ) (hi : i ∈ Finset.range (j.val.2 + 1)) :
        M f.val j.val.1 i =
          if (⟨(j.val.1, i), (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans_lt j.property⟩ : J) =
            j₀ then 1 else 0 :=
      hψ ⟨(j.val.1, i), (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)).trans_lt j.property⟩ j₀
    by_cases hEq : j = j₀
    · subst j
      rw [ite_eq_left rfl]
      have hsum : (∑ i ∈ Finset.range (n + 1), (L y) ^ (n - i) *
          (n.choose i : ℂ) * M f.val z i) = 1 := by
        rw [Finset.sum_eq_single n]
        · have hn := hψ j₀ j₀
          change M f.val z n = _ at hn
          simp [hn]
        · intro i hi hni
          have hl := hlow i hi
          change M f.val z i = _ at hl
          rw [hl, ite_eq_right (fun he ↦ hni (congrArg (fun l : J ↦ l.val.2) he)), mul_zero]
        · simp
      change c y * (∑ i ∈ Finset.range (n + 1), (L y) ^ (n - i) *
        (n.choose i : ℂ) * M f.val z i) = c y * 1
      rw [hsum]
    · rw [ite_eq_right hEq, mul_zero]
      apply mul_eq_zero_of_right
      refine Finset.sum_eq_zero fun i hi ↦ ?_
      rw [hlow i hi, ite_eq_right ?_, mul_zero]
      intro he
      have hz' : j.val.1 = z := congrArg (fun l : J ↦ l.val.1) he
      have hi' : i = n := congrArg (fun l : J ↦ l.val.2) he
      have hj' : j.val.2 < N z := hz' ▸ j.property
      have hij := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      apply hEq
      have hn : j.val.2 = n := by
        apply le_antisymm _ (hi' ▸ hij)
        exact Nat.le_pred_of_lt hj'
      exact Subtype.ext (Prod.ext hz' hn)
  have himp (y : C𝔽(ℚ)) : f.val y * c y = f.val 1 := by
    have hm : IsModulation m := ⟨isProperMap_ideleClassNorm ℚ, ideleClassNorm_ne_one (F := ℚ)⟩
    let f' : ModulatedExponentialDecay m univ := ⟨fun x ↦ f.val (y⁻¹ * x),
      modulatedExponentialDecaySubmodule_translate m univ hm
        ratIdeleNormSection_class_rightInverse.surjective y f⟩
    have hf' : f' ∈ modulatedDecayIsotype m univ (mem_univ 0) ω := by
      apply (mem_modulatedDecayIsotype_iff m ω univ (mem_univ 0) f').mpr
      have hmem := (mem_modulatedDecayIsotype_iff m ω univ (mem_univ 0) f).mp (ψ j₀).property
      intro u x
      change f.val (y⁻¹ * (u.val⁻¹ * x)) = _ * f.val (y⁻¹ * x)
      rw [mul_left_comm, hmem]
    let v : E := (c y)⁻¹ • (⟨f', hf'⟩ : E)
    let ψ' : J → E := Function.update ψ j₀ v
    have hψ' : P ψ' := by
      intro j j'
      by_cases hj : j' = j₀
      · subst j'
        rw [show ψ' j₀ = v from Function.update_self ..]
        change (∫ x, ((c y)⁻¹ * f.val (y⁻¹ * x)) * χ j.val.1 x * L x ^ j.val.2 ∂μ(ℚ)) = _
        simp_rw [mul_assoc ((c y)⁻¹), integral_const_mul]
        change (c y)⁻¹ * M (fun x ↦ f.val (y⁻¹ * x)) j.val.1 j.val.2 = _
        rw [hMtrans, ← mul_assoc, inv_mul_cancel₀ (hc z y), one_mul]
      · simpa only [ψ', Function.update_of_ne hj] using hψ j j'
    have heq := congrArg (fun φ : J → E ↦ (φ j₀).val.val y) (huniq ψ' hψ')
    rw [show ψ' j₀ = v from Function.update_self ..] at heq
    change (c y)⁻¹ * f.val (y⁻¹ * y) = f.val y at heq
    rw [inv_mul_cancel] at heq
    rw [← heq, mul_comm _ (c y), ← mul_assoc, mul_inv_cancel₀ (hc z y), one_mul]
  have hfi : Integrable (fun x : C𝔽(ℚ) ↦ f.val 1) μ(ℚ) := by
    exact (rational_decay_moment_integrable f z 0).congr
      (ae_of_all μ(ℚ) fun x ↦ by
        change f.val x * c x * L x ^ 0 = _
        simpa only [pow_zero, mul_one] using himp x)
  have h1 : f.val 1 = 0 := (integrable_const_iff.mp hfi).resolve_right
    (fun hfinite ↦ (measure_lt_top μ(ℚ) univ).ne rational_norm_haar_univ)
  have hzero (x : C𝔽(ℚ)) : f.val x = 0 := (mul_eq_zero.mp ((himp x).trans h1)).resolve_right (hc z x)
  have hval := hψ j₀ j₀
  change M f.val z n = _ at hval
  simp [M, hzero] at hval

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

/-- Paper: Theorem 10.4.3.4(2), pp. 470–471. For F = ℚ, a = 2 and s = 4
there are no line zeros, so the spectral projector and its kernel vanish.
Use Λ = 2, ε = 1/8 and the indicator of the outer norm band as cutoff.
An even nonnegative bump in the log-norm band (−1/8, 1/8) convolved with
itself is positive near the identity, where the cutoff equals one. -/
theorem Printed.spectralLineTruncatedKernel_geometric_false :
    ¬ Printed.spectralLineTruncatedKernel_geometric := by sorry

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

/-- Paper: Theorem 10.4.3.6(2), p. 473. For F = ℚ, a = 3, α = 1
and s = 4 the strip lies in the zero-free half-plane. The spectral
kernel vanishes. With Λ = 2, ε = 1/8 and the outer-band indicator,
geometric restriction is nonzero on the same even log-norm bump used
for the line counterexample. -/
theorem Printed.spectralStripRestrictionKernel_geometric_false :
    ¬ Printed.spectralStripRestrictionKernel_geometric := by sorry

end RiemannMasullo
