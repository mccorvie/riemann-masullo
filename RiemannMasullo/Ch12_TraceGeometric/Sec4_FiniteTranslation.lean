module

public import RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.Ch02_AdelicTheta.Sec2a
import Mathlib.Order.Filter.Finite
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! # Additive periods of S-adelic Schwartz–Bruhat tests -/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NumberField.AdeleRing TensorProduct Topology

namespace RiemannMasullo

/-- Local constancy on a compact support gives a common neighborhood of
translations fixing the whole function. -/
private theorem locallyConstant_eventually_add_period_of_compactSupport {K : Type*}
    [AddCommGroup K] [TopologicalSpace K] [IsTopologicalAddGroup K] (g : K → ℂ)
    (hg : IsLocallyConstant g) (hcg : HasCompactSupport g) :
    ∀ᶠ h : K in 𝓝 0, ∀ y : K, g (y + h) = g y := by
  have hsmall : ∀ᶠ h : K in 𝓝 0, ∀ y ∈ tsupport g, g (y + h) = g y := by
    apply hcg.eventually_forall_of_forall_eventually
    intro y _
    have hadd : Continuous (fun p : K × K ↦ p.2 + p.1) :=
      continuous_snd.add continuous_fst
    have hsum := hadd.tendsto' (0, y) y (add_zero y)
    have hsnd : Tendsto (Prod.snd : K × K → K) (𝓝 (0, y)) (𝓝 y) :=
      continuous_snd.continuousAt
    filter_upwards [hsum.eventually (hg.eventually_eq y), hsnd.eventually (hg.eventually_eq y)]
      with p h₁ h₂
    exact h₁.trans h₂.symm
  have hneg : Tendsto (fun h : K ↦ -h) (𝓝 0) (𝓝 0) :=
    continuous_neg.tendsto' 0 0 neg_zero
  filter_upwards [hsmall, hneg.eventually hsmall] with h hh hm y
  by_cases hy : y ∈ tsupport g
  · exact hh y hy
  by_cases hy' : y + h ∈ tsupport g
  · simpa using (hm (y + h) hy').symm
  exact (image_eq_zero_of_notMem_tsupport hy').trans (image_eq_zero_of_notMem_tsupport hy).symm

variable {F : Type*} [Field F] [NumberField F]

local notation "ℬ(" K ")" => SchwartzBruhat (Multiplicative K)

/-- A fixed S-adelic Schwartz–Bruhat test is invariant under sufficiently small
additive shifts in the finite coordinates, uniformly over all S-adeles. -/
theorem sAdeleSchwartz_eventually_add_finite_period (S : Finset (HeightOneSpectrum (𝓞 F)))
    (f : ℬ(SAdeleRing F S)) :
    ∀ᶠ h : FinitePlaceProduct F S in 𝓝 0, ∀ x : SAdeleRing F S,
      f (Multiplicative.ofAdd (x + (0, h))) = f (Multiplicative.ofAdd x) := by
  let A := SAdeleRing F S
  let B := FinitePlaceProduct F S
  let L (w : S) := ℬ(w.val.adicCompletion F)
  let T := ⨂[ℂ] w : S, L w
  let V := FinestLocallyConvex T
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  obtain ⟨z, rfl⟩ := e.surjective f
  let P (z : InductiveTensor ℬ(InfiniteAdeleRing F) V) :=
    ∀ᶠ h : B in 𝓝 0, ∀ x : A,
      e z (Multiplicative.ofAdd (x + (0, h))) = e z (Multiplicative.ofAdd x)
  have hadd (z₁ z₂) (h₁ : P z₁) (h₂ : P z₂) : P (z₁ + z₂) := by
    dsimp only [P] at h₁ h₂ ⊢
    filter_upwards [h₁, h₂] with h hh₁ hh₂ x
    rw [show e (z₁ + z₂) = e z₁ + e z₂ from map_add e z₁ z₂]
    exact congrArg₂ (· + ·) (hh₁ x) (hh₂ x)
  have hsmul (c : ℂ) (z : InductiveTensor ℬ(InfiniteAdeleRing F) V) (hz : P z) : P (c • z) := by
    dsimp only [P] at hz ⊢
    filter_upwards [hz] with h hh x
    rw [map_smul]
    exact congrArg (c • ·) (hh x)
  change P z
  refine TensorProduct.inductionOn (motive := P) z ?_ hadd
  intro a b
  refine PiTensorProduct.induction_on (motive := fun s : T ↦ P (a ⊗ₜ[ℂ] (show V from s)))
    b ?_ ?_
  · intro c g
    let v : V := ⨂ₜ[ℂ] w, g w
    have hv : P (a ⊗ₜ[ℂ] v) := by
      let g₀ (w : S) (u : w.val.adicCompletion F) := g w (Multiplicative.ofAdd u)
      have hperiod (w : S) : ∀ᶠ h : B in 𝓝 0,
          ∀ y, g₀ w (y + h w) = g₀ w y := by
        have hg := (mem_finitePlaceSchwartz_iff F w.val (g₀ w)).mp ⟨g w, fun _ ↦ rfl⟩
        have hcoord : Continuous (fun h : B ↦ h w) := continuous_apply w
        exact (hcoord.tendsto' 0 0 rfl).eventually
          (locallyConstant_eventually_add_period_of_compactSupport _ hg.1 hg.2)
      dsimp only [P]
      filter_upwards [Filter.eventually_all.mpr hperiod] with h hh x
      calc
        _ = a (Multiplicative.ofAdd (x.1 + 0)) * ∏ w : S, g₀ w (x.2 w + h w) :=
          he a g (x + (0, h))
        _ = a (Multiplicative.ofAdd x.1) * ∏ w : S, g₀ w (x.2 w) := by
          simp only [add_zero, hh]
        _ = _ := (he a g x).symm
    change P (a ⊗ₜ[ℂ] (c • v))
    have ht : a ⊗ₜ[ℂ] (c • v) = c • (a ⊗ₜ[ℂ] v) :=
      (TensorProduct.mk ℂ ℬ(InfiniteAdeleRing F) V a).map_smul c v
    exact (congrArg P ht).mpr (hsmul c _ hv)
  · intro b₁ b₂ h₁ h₂
    change P (a ⊗ₜ[ℂ] ((b₁ : V) + (b₂ : V)))
    have ht : a ⊗ₜ[ℂ] ((b₁ : V) + (b₂ : V)) = a ⊗ₜ[ℂ] (b₁ : V) + a ⊗ₜ[ℂ] (b₂ : V) :=
      (TensorProduct.mk ℂ ℬ(InfiniteAdeleRing F) V a).map_add (b₁ : V) (b₂ : V)
    exact (congrArg P ht).mpr (hadd _ _ h₁ h₂)

section FiniteShift

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

set_option quotPrecheck false in
local notation "Eₛ" => ((w : InfinitePlace F) → w.Completion) ×
  ((v : S) → v.val.adicCompletion F)
set_option quotPrecheck false in
local notation "modS(" x ")" => ((∏ w : InfinitePlace F, ‖(x : Eₛ).1 w‖ ^ w.mult) *
  ∏ j : S, ‖(x : Eₛ).2 j‖)

open Classical in
/-- Paper: Theorem 12.4.1.1, Step II, p. 517.
If a single finite coordinate shift changes the radial modulus, both moduli
are bounded by the size of that shift times a fixed polynomial in the original
sup norm. The ultrametric inequality controls the changed coordinate. -/
theorem sAdele_modulus_max_le_of_ne_finite_shift
    (v : S) (x : Eₛ) (h : v.val.adicCompletion F) :
    let x' : Eₛ := x + (0, Pi.single v h)
    modS(x') ≠ modS(x) →
      max modS(x') modS(x) ≤
        ‖h‖ * (1 + ‖x‖) ^ ((∑ w : InfinitePlace F, w.mult) + Fintype.card S) := by
  classical
  intro x' hne
  let a := (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) *
    ∏ j ∈ Finset.univ.erase v, ‖x.2 j‖
  have hx : modS(x) = a * ‖x.2 v‖ := by
    change (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * (∏ j : S, ‖x.2 j‖) =
      (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) *
        (∏ j ∈ Finset.univ.erase v, ‖x.2 j‖) * ‖x.2 v‖
    rw [mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ v)]
  have hshift (j : S) : x'.2 j = x.2 j + Pi.single (M := fun v : S ↦ v.val.adicCompletion F) v h j := rfl
  have hp : (∏ j : S, ‖x'.2 j‖) =
      (∏ j ∈ Finset.univ.erase v, ‖x.2 j‖) * ‖x.2 v + h‖ := by
    rw [← Finset.prod_erase_mul Finset.univ (fun j : S ↦ ‖x'.2 j‖) (Finset.mem_univ v)]
    congr 1
    · refine Finset.prod_congr rfl fun j hj ↦ ?_
      rw [hshift, Pi.single_eq_of_ne (Finset.ne_of_mem_erase hj), add_zero]
    · rw [hshift, Pi.single_eq_same]
  have hx' : modS(x') = a * ‖x.2 v + h‖ := by
    have harch : x'.1 = x.1 := add_zero _
    rw [harch, hp]
    exact (mul_assoc _ _ _).symm
  have hv : ‖x.2 v‖ ≤ ‖h‖ := by
    by_contra! hlt
    have heq : ‖x.2 v + h‖ = ‖x.2 v‖ := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm, max_eq_left hlt.le]
      exact hlt.ne'
    exact hne (by rw [hx', hx, heq])
  have hv' : ‖x.2 v + h‖ ≤ ‖h‖ :=
    (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hv le_rfl)
  let b : ℝ := 1 + ‖x‖
  have hb : 1 ≤ b := le_add_of_nonneg_right (norm_nonneg _)
  have ha₁ : (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) ≤ b ^ (∑ w : InfinitePlace F, w.mult) := by
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (norm_nonneg (x.1 w)) _) fun w _ ↦ ?_
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_le_pi_norm x.1 w).trans ((norm_fst_le x).trans (le_add_of_nonneg_left zero_le_one))) w.mult
  have ha₂ : (∏ j ∈ Finset.univ.erase v, ‖x.2 j‖) ≤ b ^ Fintype.card S := by
    calc
      _ ≤ ∏ j ∈ Finset.univ.erase v, b := by
        refine Finset.prod_le_prod₀ (fun j _ ↦ norm_nonneg (x.2 j)) fun j _ ↦ ?_
        exact (norm_le_pi_norm x.2 j).trans ((norm_snd_le x).trans (le_add_of_nonneg_left zero_le_one))
      _ = b ^ (Finset.univ.erase v).card := Finset.prod_const _
      _ ≤ _ := pow_le_pow_right₀ hb (Finset.card_le_univ _)
  have ha₀ : 0 ≤ a := by dsimp only [a]; positivity
  have ha : a ≤ b ^ ((∑ w : InfinitePlace F, w.mult) + Fintype.card S) := by
    rw [pow_add]
    exact mul_le_mul ha₁ ha₂ (by positivity) (by positivity)
  rw [hx', hx]
  refine max_le ?_ ?_
  · rw [mul_comm ‖h‖]
    exact mul_le_mul ha hv' (norm_nonneg _) (by positivity)
  · rw [mul_comm ‖h‖]
    exact mul_le_mul ha hv (norm_nonneg _) (by positivity)

/-- For any natural exponent, the first translation difference of the cutoff amplitude
has that power of the shift norm as an additive L¹ bound. The shift fixes the amplitude,
and the radial symbol is constant near zero. The constant is uniform in admissible shifts
and in the scaling parameter above the positive floor. -/
private theorem finiteShift_radialProfile_L1_sub_le {E : Type*} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    (m : E → ℝ) (hm : Measurable m) (hm0 : ∀ x, 0 ≤ m x)
    (g : E → ℂ) (hg : AEStronglyMeasurable g μ) (d n : ℕ)
    (hW : Integrable (fun x ↦
      (1 + ‖x‖) ^ (d * n) * (Real.sqrt ‖g x‖ + ‖g x‖)) μ)
    (b : ℝ → ℂ) (hb : Measurable b) {c : ℂ} {a δ C M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hplateau : EqOn b (fun _ ↦ c) (Icc 0 a)) (hbd : ∀ t, ‖b t‖ ≤ M) :
    let k (t : ℝ) (x : E) := g x * b (m x / t)
    ∃ A ≥ 0, ∀ h : E, (∀ x, g (x + h) = g x) →
      (∀ x, m (x + h) ≠ m x →
        max (m (x + h)) (m x) ≤ C * ‖h‖ * (1 + ‖x‖) ^ d) →
      ∀ t : ℝ, δ ≤ t →
        Integrable (fun x ↦ k t (x + h) - k t x) μ ∧
        (∫ x, ‖k t (x + h) - k t x‖ ∂μ) ≤ A * ‖h‖ ^ n := by
  intro k
  let W (x : E) := (1 + ‖x‖) ^ (d * n) * (Real.sqrt ‖g x‖ + ‖g x‖)
  change Integrable W μ at hW
  let D := 2 * M * (C / (a * δ)) ^ n
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hW0 (x : E) : 0 ≤ W x := by dsimp [W]; positivity
  refine ⟨D * (∫ x, W x ∂μ), mul_nonneg hD (integral_nonneg hW0),
    fun h hperiod hgeom t ht ↦ ?_⟩
  have ht0 : 0 < t := hδ.trans_le ht
  let q (x : E) := b (m x / t)
  have hq : Measurable q := hb.comp (hm.div_const t)
  have hshift : Measurable (fun x : E ↦ x + h) :=
    (continuous_id.add continuous_const).measurable
  have hdmeas : AEStronglyMeasurable (fun x ↦ k t (x + h) - k t x) μ := by
    change AEStronglyMeasurable (fun x ↦ g (x + h) * q (x + h) - g x * q x) μ
    simp only [hperiod]
    exact (hg.mul (hq.comp hshift).aestronglyMeasurable).sub (hg.mul hq.aestronglyMeasurable)
  have hdiff (x : E) : ‖k t (x + h) - k t x‖ ≤ D * ‖h‖ ^ n * W x := by
    change ‖g (x + h) * q (x + h) - g x * q x‖ ≤ _
    rw [hperiod x, ← mul_sub, norm_mul]
    by_cases heq : m (x + h) = m x
    · rw [show q (x + h) = q x by simp only [q, heq], sub_self, norm_zero, mul_zero]
      positivity
    by_cases hmax : max (m (x + h)) (m x) ≤ a * t
    · have hplateau' (y : E) (hy : m y ≤ a * t) : q y = c := by
        change b (m y / t) = c
        exact hplateau ⟨div_nonneg (hm0 y) ht0.le, (div_le_iff₀ ht0).2 hy⟩
      rw [hplateau' (x + h) ((le_max_left _ _).trans hmax),
        hplateau' x ((le_max_right _ _).trans hmax), sub_self, norm_zero, mul_zero]
      positivity
    have hle : a * δ ≤ C * ‖h‖ * (1 + ‖x‖) ^ d :=
      (mul_le_mul_of_nonneg_left ht ha.le).trans ((lt_of_not_ge hmax).le.trans (hgeom x heq))
    have hbase : 1 ≤ (C / (a * δ)) * ‖h‖ * (1 + ‖x‖) ^ d := by
      calc
        1 ≤ (C * ‖h‖ * (1 + ‖x‖) ^ d) / (a * δ) :=
          (le_div_iff₀ (mul_pos ha hδ)).2 (by simpa only [one_mul] using hle)
        _ = _ := by ring
    have hpow : 1 ≤ (C / (a * δ)) ^ n * ‖h‖ ^ n * (1 + ‖x‖) ^ (d * n) := by
      simpa only [mul_pow, ← pow_mul] using (one_le_pow₀ hbase (n := n))
    have hqnorm : ‖q (x + h) - q x‖ ≤ 2 * M := by
      calc
        _ ≤ ‖q (x + h)‖ + ‖q x‖ := norm_sub_le _ _
        _ ≤ M + M := add_le_add (hbd _) (hbd _)
        _ = _ := by ring
    have hWdom : (1 + ‖x‖) ^ (d * n) * ‖g x‖ ≤ W x :=
      mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg _)) (by positivity)
    calc
      _ ≤ ‖g x‖ * (2 * M) := mul_le_mul_of_nonneg_left hqnorm (norm_nonneg _)
      _ ≤ ‖g x‖ * (2 * M) *
          ((C / (a * δ)) ^ n * ‖h‖ ^ n * (1 + ‖x‖) ^ (d * n)) :=
        le_mul_of_one_le_right (by positivity) hpow
      _ = D * ‖h‖ ^ n * ((1 + ‖x‖) ^ (d * n) * ‖g x‖) := by dsimp [D]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hWdom (by positivity)
  have hmajor : Integrable (fun x ↦ D * ‖h‖ ^ n * W x) μ :=
    hW.const_mul (D * ‖h‖ ^ n)
  have hint := hmajor.mono' hdmeas (ae_of_all _ hdiff)
  refine ⟨hint, (integral_mono hint.norm hmajor hdiff).trans_eq ?_⟩
  rw [integral_const_mul]
  ring

open Classical in
/-- Paper: Theorem 12.4.1.1, Step II, p. 517.
For a bounded radial profile constant near zero, small single-place finite
translations give an additive `L¹` difference of any prescribed order. The
constant is uniform in the finite place and in scales above a positive floor. -/
theorem sAdeleSchwartz_radialProfile_finiteShift_L1_le
    [MeasurableSpace Eₛ] [BorelSpace Eₛ] (μ : Measure Eₛ)
    (f : ℬ(SAdeleRing F S)) (n : ℕ)
    (hW : Integrable (fun x : Eₛ ↦
      (1 + ‖x‖) ^ (((∑ w : InfinitePlace F, w.mult) + Fintype.card S) * n) *
        (Real.sqrt ‖f (Multiplicative.ofAdd x)‖ + ‖f (Multiplicative.ofAdd x)‖)) μ)
    (b : ℝ → ℂ) (hb : Measurable b) {c : ℂ} {a δ M : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) (hM : 0 ≤ M)
    (hplateau : EqOn b (fun _ ↦ c) (Icc 0 a)) (hbd : ∀ t, ‖b t‖ ≤ M) :
    let k (t : ℝ) (x : Eₛ) := f (Multiplicative.ofAdd x) * b (modS(x) / t)
    ∃ ε > 0, ∃ A ≥ 0, ∀ (v : S) (h : v.val.adicCompletion F), ‖h‖ < ε →
      ∀ t : ℝ, δ ≤ t →
        Integrable (fun x ↦ k t (x + (0, Pi.single v h)) - k t x) μ ∧
        (∫ x, ‖k t (x + (0, Pi.single v h)) - k t x‖ ∂μ) ≤ A * ‖h‖ ^ n := by
  intro k
  let g (x : Eₛ) := f (Multiplicative.ofAdd x)
  have hg : Continuous g := (schwartzBruhat_continuous f).comp continuous_ofAdd
  have hm : Continuous fun x : Eₛ ↦ modS(x) :=
    (continuous_finsetProd _ fun w _ ↦ ((continuous_apply w).comp continuous_fst).norm.pow _).mul
      (continuous_finsetProd _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  obtain ⟨ε, hε, hperiod⟩ :=
    Metric.eventually_nhds_iff.mp (sAdeleSchwartz_eventually_add_finite_period S f)
  let d := (∑ w : InfinitePlace F, w.mult) + Fintype.card S
  obtain ⟨A, hA, hcut⟩ := finiteShift_radialProfile_L1_sub_le μ (fun x : Eₛ ↦ modS(x))
    hm.measurable (fun x ↦ by positivity) g hg.aestronglyMeasurable d n hW
    b hb (C := 1) ha hδ zero_le_one hM hplateau hbd
  refine ⟨ε, hε, A, hA, fun v h hh t ht ↦ ?_⟩
  let z : Eₛ := (0, Pi.single v h)
  have hz : ‖z‖ = ‖h‖ := by
    change max ‖(0 : (w : InfinitePlace F) → w.Completion)‖
      ‖(Pi.single v h : FinitePlaceProduct F S)‖ = ‖h‖
    rw [norm_zero, Pi.norm_single, max_eq_right (norm_nonneg _)]
  have hh' : dist (Pi.single v h : FinitePlaceProduct F S) 0 < ε := by
    rw [dist_zero_right, Pi.norm_single]
    exact hh
  have hgeom (x : Eₛ) (hx : modS(x + z) ≠ modS(x)) :
      max modS(x + z) modS(x) ≤ 1 * ‖z‖ * (1 + ‖x‖) ^ d := by
    rw [one_mul, hz]
    exact sAdele_modulus_max_le_of_ne_finite_shift v x h hx
  have hloc (x : Eₛ) : g (x + z) = g x := hperiod hh' x
  have hres := hcut z hloc hgeom t ht
  rw [hz] at hres
  exact hres

end FiniteShift

end RiemannMasullo
