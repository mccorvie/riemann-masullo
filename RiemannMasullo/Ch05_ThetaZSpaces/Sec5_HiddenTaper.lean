module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
public import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import RiemannMasullo.Ch05_ThetaZSpaces.Sec2

/-! # A growing logarithmic taper of actual polar-free theta tests

For the supported approximation problem associated with §12.5, pp. 519–520, consider
finite sums of norm dilations with bounded coefficients indexed by nonzero integral
ideals. Increasing the power of the logarithmic cutoff controls the part below the
reciprocal cutoff from rapid theta decay and ordinary ideal counting.
-/

public noncomputable section
open Function IsDedekindDomain NumberField Filter Set MeasureTheory
open scoped NNReal NumberField.AdeleRing nonZeroDivisors Topology

namespace RiemannMasullo
set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
local notation "I₀" => (Ideal (𝓞 F))⁰
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "I𝔽" => IdeleGroup (𝓞 F) F
local notation "normℝ" => fun g : C𝔽 ↦ ((ideleClassNorm F g).val : ℝ)

private def taperIdeals (L : ℝ) : Finset I₀ :=
  (Ring.HasFiniteQuotients.finite_absNorm_le₀ (S := 𝓞 F) ⌊Real.exp L⌋₊).toFinset

private def taperNormUnit (I : I₀) : ℝ≥0ˣ :=
  Units.mk0 (((I : Ideal (𝓞 F)).absNorm : ℕ) : ℝ≥0)
    (by exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors I).ne')

private theorem taperTranslate_mem (u : I𝔽) (f : adelePolarSubspace F) :
    schwartzBruhatUnitTranslate u f.val ∈ adelePolarSubspace F := by
  obtain ⟨h₀, hF⟩ := (mem_adelePolarSubspace f.val).mp f.property
  apply (mem_adelePolarSubspace _).mpr
  constructor
  · change f.val (Multiplicative.ofAdd (u.inv * 0)) = 0
    simpa only [mul_zero] using h₀
  · rw [adeleSchwartzFourier_zero_unitTranslate, hF, mul_zero]

/-- The finite ideal-norm logarithmic Riesz sum, realized on the original adelic test.
The norm section sends the positive ideal norm to an idèle, and the inverse translate
dilates the argument of theta by that norm. -/
def idealLogRieszThetaTest (τ : ℝ≥0ˣ →ₜ* I𝔽) (b : I₀ → ℂ)
    (f : adelePolarSubspace F) (L : ℝ) (d : ℕ) : adelePolarSubspace F :=
  ∑ I ∈ taperIdeals L,
    (b I * (((1 - Real.log ((I : Ideal (𝓞 F)).absNorm : ℝ) / L) ^ d : ℝ) : ℂ)) •
      (⟨schwartzBruhatUnitTranslate (τ (taperNormUnit I))⁻¹ f.val,
        taperTranslate_mem _ f⟩ : adelePolarSubspace F)

private theorem taperTheta_sum (τ : ℝ≥0ˣ →ₜ* I𝔽) (b : I₀ → ℂ)
    (f : adelePolarSubspace F) (L : ℝ) (d : ℕ) (g : C𝔽) :
    adelicTheta (idealLogRieszThetaTest τ b f L d).val g =
      ∑ I ∈ taperIdeals L,
        (b I * (((1 - Real.log ((I : Ideal (𝓞 F)).absNorm : ℝ) / L) ^ d : ℝ) : ℂ)) *
          adelicTheta f.val (QuotientGroup.mk (τ (taperNormUnit I)) * g) := by
  let ev := (ContinuousMap.evalCLM ℂ g).toLinearMap.comp (adelicThetaLinearMap F)
  change ev (idealLogRieszThetaTest τ b f L d).val = _
  simp only [idealLogRieszThetaTest, Submodule.coe_sum, Submodule.coe_smul_of_tower, map_sum,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro I _
  congr 1
  change adelicTheta (schwartzBruhatUnitTranslate _ _) _ = _
  rw [adelicTheta_unitTranslate, ← QuotientGroup.mk_inv, inv_inv]

/-- Evaluating the finite test gives the weighted sum over the nonzero ideals of norm
at most exp(L). Each summand evaluates the original theta at the inward norm dilation. -/
theorem idealLogRieszThetaTest_apply (τ : ℝ≥0ˣ →ₜ* I𝔽) (b : I₀ → ℂ)
    (f : adelePolarSubspace F) (L : ℝ) (d : ℕ) (g : C𝔽) :
    adelicTheta (idealLogRieszThetaTest τ b f L d).val g =
      ∑ I ∈ (Ring.HasFiniteQuotients.finite_absNorm_le₀ (S := 𝓞 F) ⌊Real.exp L⌋₊).toFinset,
        let n := (I : Ideal (𝓞 F)).absNorm
        let u : ℝ≥0ˣ := Units.mk0 (n : ℝ≥0) (by
          dsimp [n]
          exact_mod_cast (Ideal.absNorm_pos_of_nonZeroDivisors I).ne')
        b I * (((1 - Real.log n / L)^d : ℝ) : ℂ) *
          adelicTheta f.val (QuotientGroup.mk (τ u) * g) :=
  taperTheta_sum τ b f L d g

private theorem taperNorm_mul (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    (I : I₀) (g : C𝔽) :
    normℝ (QuotientGroup.mk (τ (taperNormUnit I)) * g) =
      ((I : Ideal (𝓞 F)).absNorm : ℝ) * normℝ g := by
  simp only [map_mul, Units.val_mul, NNReal.coe_mul]
  change ((ideleNorm F (τ (taperNormUnit I))).val : ℝ) * _ = _
  rw [hτ]
  rfl

/-- An upper norm bound on theta persists under every finite logarithmic taper. -/
theorem idealLogRieszThetaTest_vanishes_above_one (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (b : I₀ → ℂ) (f : adelePolarSubspace F)
    (hf : ∀ g : C𝔽, 1 < normℝ g → adelicTheta f.val g = 0)
    (L : ℝ) (d : ℕ) (g : C𝔽) (hg : 1 < normℝ g) :
    adelicTheta (idealLogRieszThetaTest τ b f L d).val g = 0 := by
  rw [taperTheta_sum]
  apply Finset.sum_eq_zero
  intro I _
  apply mul_eq_zero_of_right
  apply hf
  rw [taperNorm_mul τ hτ]
  exact hg.trans_le (le_mul_of_one_le_left (by linarith) (by
    exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I))

private theorem taperIdeals_card :
    ∃ D T : ℝ, ∀ L ≥ T, ((taperIdeals (F := F) L).card : ℝ) ≤ D * Real.exp L := by
  have h := (NumberField.Ideal.tendsto_norm_le_div_atTop₀ F).comp Real.tendsto_exp_atTop
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp (h.eventually_lt_const (lt_add_one _))
  refine ⟨2 ^ InfinitePlace.nrRealPlaces F * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces F *
    Units.regulator F * classNumber F / (Units.torsionOrder F * Real.sqrt |(discr F : ℝ)|) + 1,
    T, fun L hL ↦ ?_⟩
  have he := Equiv.subtypeEquivRight (p := fun I : I₀ ↦ I ∈ taperIdeals L)
    (q := fun I : I₀ ↦ ((I : Ideal (𝓞 F)).absNorm : ℝ) ≤ Real.exp L) (fun I ↦ by
      simp [taperIdeals, Nat.le_floor_iff (Real.exp_pos L).le])
  have hc := Nat.card_congr he
  rw [Nat.card_eq_fintype_card, Fintype.card_coe] at hc
  rw [hc]
  exact (div_le_iff₀ (Real.exp_pos L)).mp (hT L hL).le

private theorem taperTheta_small (f : adelePolarSubspace F) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : C𝔽, normℝ g < 1 → ‖adelicTheta f.val g‖ ≤ C * (normℝ g)^N := by
  obtain ⟨C, hC, h⟩ := adelicTheta_decay_bounded_threshold_one ({f.val} : Set _)
    (Bornology.isVonNBounded_singleton f.val) N
  obtain ⟨h₀,hF⟩ := (mem_adelePolarSubspace f.val).mp f.property
  refine ⟨C, hC, fun g hg ↦ ?_⟩
  simpa only [h₀, hF, smul_zero, sub_zero, add_zero] using (h f.val (by simp) g).2.1 hg

private theorem taper_factor_bound {q a L C B V : ℝ} {k : ℕ} (hk : L = a*k)
    (hL : 0 < L) (hq₀ : 0 ≤ q) (hq₁ : q ≤ 1) (hV : 0 ≤ V) (hB : V ≤ B)
    (hB₁ : 1 ≤ B) (hC : C ≤ Real.exp L) (hdec : V ≤ C * Real.exp (-(4 * Real.exp a * q * L))) :
    q ^ (2*k) * V ≤ B * Real.exp (-(2*L)) := by
  by_cases hq : q ≤ Real.exp (-a)
  · have hw : q^(2*k) ≤ Real.exp (-(2*L)) := calc
      _ ≤ (Real.exp (-a))^(2*k) := pow_le_pow_left₀ hq₀ hq _
      _ = _ := by rw [← Real.exp_nat_mul]; congr 1; push_cast; rw [hk]; ring
    exact (mul_le_mul hw hB hV (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  · have hprod : 1 ≤ Real.exp a * q := by
      rw [Real.exp_neg] at hq
      have := (inv_le_iff_one_le_mul₀ (Real.exp_pos a)).mp (le_of_not_ge hq)
      simpa only [mul_comm q] using this
    have hex : -(4 * Real.exp a * q * L) ≤ -(4*L) := by
      nlinarith [mul_le_mul_of_nonneg_right hprod hL.le]
    have hv : V ≤ Real.exp (-(2*L)) := calc
      _ ≤ _ := hdec
      _ ≤ Real.exp L * Real.exp (-(4*L)) :=
        mul_le_mul hC (Real.exp_le_exp.mpr hex) (Real.exp_pos _).le (Real.exp_pos _).le
      _ ≤ _ := by rw [← Real.exp_add]; apply Real.exp_le_exp.mpr; linarith
    exact mul_le_mul ((pow_le_one₀ hq₀ hq₁).trans hB₁) hv hV (by linarith)

private theorem taperTheta_stage (τ : ℝ≥0ˣ →ₜ* I𝔽) (hτ : RightInverse τ (ideleNorm F))
    (b : I₀ → ℂ) (hb : ∀ I, ‖b I‖ ≤ 1) (f : adelePolarSubspace F)
    {a L C B D : ℝ} {k N : ℕ} (hk : L = a*k) (hL : 0 < L) (hN : 4 * Real.exp a ≤ N)
    (hB₁ : 1 ≤ B) (hB : ∀ z : C𝔽, normℝ z < 1 → ‖adelicTheta f.val z‖ ≤ B)
    (hC : C ≤ Real.exp L) (hC₀ : 0 ≤ C)
    (hdec : ∀ z : C𝔽, normℝ z < 1 → ‖adelicTheta f.val z‖ ≤ C * (normℝ z)^N)
    (hcard : ((taperIdeals (F := F) L).card : ℝ) ≤ D * Real.exp L)
    (g : C𝔽) (hg : normℝ g < Real.exp (-L)) :
    ‖adelicTheta (idealLogRieszThetaTest τ b f L (2*k)).val g‖ ≤ (B*D) * Real.exp (-L) := by
  rw [taperTheta_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    _ ≤ ∑ _I ∈ taperIdeals (F := F) L, B * Real.exp (-(2*L)) := by
      apply Finset.sum_le_sum
      intro I hI
      let n : ℝ := (I : Ideal (𝓞 F)).absNorm
      let q := 1 - Real.log n / L
      let z : C𝔽 := QuotientGroup.mk (τ (taperNormUnit I)) * g
      have hn₁ : 1 ≤ n := by
        dsimp [n]
        exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I
      have hn : 0 < n := by linarith
      have hnle : n ≤ Real.exp L := by
        simpa [n, taperIdeals, Nat.le_floor_iff (Real.exp_pos L).le] using hI
      have hq₀ : 0 ≤ q := sub_nonneg.mpr <| (div_le_one hL).mpr ((Real.log_le_iff_le_exp hn).mpr hnle)
      have hq₁ : q ≤ 1 := sub_le_self _ (div_nonneg (Real.log_nonneg hn₁) hL.le)
      have hr : normℝ z < Real.exp (-(q*L)) := calc
        normℝ z = n * normℝ g := taperNorm_mul τ hτ I g
        _ < n * Real.exp (-L) := mul_lt_mul_of_pos_left hg hn
        _ = _ := by
          rw [← Real.exp_log hn, ← Real.exp_add]
          congr 1
          dsimp [q]
          field_simp
          ring
      have hz : normℝ z < 1 := hr.trans_le (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hq₀ hL.le)))
      have hp : 0 ≤ normℝ z := NNReal.coe_nonneg _
      have hpower : (normℝ z)^N ≤ Real.exp (-(4 * Real.exp a * q * L)) := calc
        _ ≤ (Real.exp (-(q*L)))^N := pow_le_pow_left₀ hp hr.le _
        _ = Real.exp ((N : ℝ) * (-(q*L))) := (Real.exp_nat_mul _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hN (mul_nonneg hq₀ hL.le)])
      have hf := taper_factor_bound hk hL hq₀ hq₁ (norm_nonneg _) (hB z hz) hB₁ hC
        ((hdec z hz).trans (mul_le_mul_of_nonneg_left hpower hC₀))
      change ‖(b I * ((q^(2*k) : ℝ) : ℂ)) * adelicTheta f.val z‖ ≤ _
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg hq₀ _), mul_assoc]
      exact (mul_le_of_le_one_left (mul_nonneg (pow_nonneg hq₀ _) (norm_nonneg _)) (hb I)).trans hf
    _ = ((taperIdeals (F := F) L).card : ℝ) * (B * Real.exp (-(2*L))) := by simp
    _ ≤ (D * Real.exp L) * (B * Real.exp (-(2*L))) :=
      mul_le_mul_of_nonneg_right hcard (mul_nonneg (by linarith) (Real.exp_pos _).le)
    _ = _ := by
      calc
        _ = (B*D) * (Real.exp L * Real.exp (-(2*L))) := by ring
        _ = _ := by rw [← Real.exp_add]; congr 2; ring

private theorem taperLogLength_tendsto (k : ℕ → ℕ) (hk : ∀ j, 0 < k j) :
    Tendsto (fun j : ℕ ↦ ((j : ℝ)+1) * k j) atTop atTop := by
  have ha : Tendsto (fun j : ℕ ↦ (j : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  exact Filter.tendsto_atTop_mono (fun j ↦
    le_mul_of_one_le_right (by positivity) (by exact_mod_cast hk j)) ha

private theorem taper_fixed_norm (k : ℕ → ℕ) (hk : ∀ j, 0 < k j) {v : ℝ} (hv : 0 ≤ v) :
    Tendsto (fun j : ℕ ↦ (1 - v/(((j : ℝ)+1)*k j))^(2*k j)) atTop (𝓝 1) := by
  have ha : Tendsto (fun j : ℕ ↦ (j : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have ht : Tendsto (fun j : ℕ ↦ 1 - 2*v/((j : ℝ)+1)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (ha.const_div_atTop (2*v))
  have he := (taperLogLength_tendsto k hk).eventually_ge_atTop v
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' ht tendsto_const_nhds
  · filter_upwards [he] with j hj
    have hkj : 0 < (k j : ℝ) := by exact_mod_cast hk j
    have hL : 0 < ((j : ℝ)+1)*k j := by positivity
    have hratio := (div_le_one hL).mpr hj
    have h := one_add_mul_le_pow (a := -(v/(((j : ℝ)+1)*k j))) (by linarith) (2*k j)
    convert h using 1
    · push_cast
      field_simp
      ring
  · filter_upwards [he] with j hj
    have hkj : 0 < (k j : ℝ) := by exact_mod_cast hk j
    exact pow_le_one₀ (sub_nonneg.mpr <| (div_le_one (by positivity)).mpr hj)
      (sub_le_self _ (div_nonneg hv (by positivity)))

/-- There is a single growing-degree schedule for each polar-free source, valid for
every system of bounded ideal coefficients. Each fixed ideal weight tends to one,
and the raw adelic theta is uniformly O(exp(-L)) below reciprocal cutoff exp(-L).
Here L=(j+1)k(j) is the log cutoff and the Riesz degree is 2k(j). -/
theorem exists_idealLogRieszThetaTest_hidden_bound (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (f : adelePolarSubspace F) :
    ∃ (k : ℕ → ℕ) (H : ℝ), 0 ≤ H ∧ (∀ j, 0 < k j) ∧
      let L (j : ℕ) := ((j : ℝ)+1)*k j
      Tendsto L atTop atTop ∧
      (∀ I : I₀, Tendsto (fun j ↦ (1 - Real.log ((I : Ideal (𝓞 F)).absNorm : ℝ)/L j)^(2*k j))
        atTop (𝓝 1)) ∧
      ∀ (b : I₀ → ℂ), (∀ I, ‖b I‖ ≤ 1) → ∀ j (g : C𝔽), normℝ g < Real.exp (-L j) →
        ‖adelicTheta (idealLogRieszThetaTest τ b f (L j) (2*k j)).val g‖ ≤ H * Real.exp (-L j) := by
  obtain ⟨D,T,hcard⟩ := taperIdeals_card (F := F)
  obtain ⟨B,_,hB⟩ := taperTheta_small f 0
  let H := max 1 B * max 0 D
  have hs (j : ℕ) : ∃ k : ℕ, 0 < k ∧ ∀ (b : I₀ → ℂ), (∀ I, ‖b I‖ ≤ 1) →
      ∀ g : C𝔽, normℝ g < Real.exp (-(((j : ℝ)+1)*k)) →
        ‖adelicTheta (idealLogRieszThetaTest τ b f (((j : ℝ)+1)*k) (2*k)).val g‖ ≤
          H * Real.exp (-(((j : ℝ)+1)*k)) := by
    let a := (j : ℝ)+1
    let N := ⌈4*Real.exp a⌉₊
    obtain ⟨C,hC,hdec⟩ := taperTheta_small f N
    obtain ⟨k,hk⟩ := exists_nat_gt (max 0 (max T (Real.log C)))
    have hk' : 0 < (k : ℝ) := (le_max_left _ _).trans_lt hk
    have hLk : (k : ℝ) ≤ a*k := le_mul_of_one_le_left hk'.le (by dsimp [a]; linarith [Nat.cast_nonneg (α := ℝ) j])
    have hmax : max T (Real.log C) ≤ a*k := (le_max_right _ _).trans (hk.le.trans hLk)
    refine ⟨k, by exact_mod_cast hk', fun b hb g hg ↦ ?_⟩
    have hsmall (z : C𝔽) (hz : normℝ z < 1) : ‖adelicTheta f.val z‖ ≤ max 1 B :=
      (by simpa using hB z hz : ‖adelicTheta f.val z‖ ≤ B).trans (le_max_right _ _)
    have hcount := (hcard _ ((le_max_left _ _).trans hmax)).trans
      (mul_le_mul_of_nonneg_right (le_max_right 0 D) (Real.exp_pos _).le)
    exact taperTheta_stage τ hτ b hb f (a := a) (N := N) rfl (hk'.trans_le hLk)
      (Nat.le_ceil _) (le_max_left _ _) hsmall
      ((Real.log_le_iff_le_exp hC).mp ((le_max_right _ _).trans hmax)) hC.le hdec hcount g hg
  choose k hk hbound using hs
  refine ⟨k,H,mul_nonneg (by positivity) (le_max_left _ _),hk,taperLogLength_tendsto k hk,
    fun I ↦ taper_fixed_norm k hk (Real.log_nonneg ?_),fun b hb j ↦ hbound j b hb⟩
  exact_mod_cast Ideal.absNorm_pos_of_nonZeroDivisors I

/-- In the centered log-norm chart the squared hidden norm tends to zero for every angular character, using the
same schedule that retains each fixed ideal coefficient. The chart may be any
continuous lift of the log norm. The estimate concerns the part x < -L. -/
theorem exists_idealLogRieszThetaTest_hidden_energy (τ : ℝ≥0ˣ →ₜ* I𝔽)
    (hτ : RightInverse τ (ideleNorm F)) (f : adelePolarSubspace F) :
    ∃ k : ℕ → ℕ, (∀ j, 0 < k j) ∧
      let L (j : ℕ) := ((j : ℝ)+1)*k j
      Tendsto L atTop atTop ∧
      (∀ I : I₀, Tendsto (fun j ↦ (1 - Real.log ((I : Ideal (𝓞 F)).absNorm : ℝ)/L j)^(2*k j))
        atTop (𝓝 1)) ∧
      ∀ (b : I₀ → ℂ), (∀ I, ‖b I‖ ≤ 1) → ∀ (ω : PontryaginDual (ideleClassNorm F).ker) (γ : C(ℝ, C𝔽)),
        (∀ x, normℝ (γ x) = Real.exp x) →
        Tendsto (fun j ↦ ∫ x in Iio (-L j),
          ‖homogeneousAdelicTheta ω (idealLogRieszThetaTest τ b f (L j) (2*k j)).val (γ x)‖^2 * Real.exp x)
          atTop (𝓝 0) := by
  obtain ⟨k,H,hH,hk,hL,hcoeff,hbound⟩ := exists_idealLogRieszThetaTest_hidden_bound τ hτ f
  refine ⟨k,hk,hL,hcoeff,fun b hb ω γ hγ ↦ ?_⟩
  let L (j : ℕ) := ((j : ℝ)+1)*k j
  let : MeasurableSpace C𝔽 := borel _
  let μ := normOneIdeleClassTamagawaMeasure F
  let M := (μ univ).toReal * H
  have he : Tendsto (fun j ↦ Real.exp (-L j)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hL)
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ integral_nonneg (fun _ ↦ by positivity)) _
    (show Tendsto (fun j ↦ M^2 * Real.exp (-L j)) atTop (𝓝 0) by
      simpa only [mul_zero] using he.const_mul (M^2))
  apply Eventually.of_forall
  intro j
  have hpos : 0 < L j := mul_pos (by positivity) (by exact_mod_cast hk j)
  have hi : IntegrableOn Real.exp (Iio (-L j)) volume := by
    have h := integrableOn_exp_mul_Iic (a := (1:ℝ)) zero_lt_one (-L j)
    exact (by simpa only [one_mul] using h : IntegrableOn Real.exp (Iic (-L j)) volume).mono_set Iio_subset_Iic_self
  calc
    _ ≤ ∫ x in Iio (-L j), M^2 * Real.exp x := by
      refine integral_mono_of_nonneg ?_ (hi.const_mul _) ?_
      · exact Eventually.of_forall fun x ↦ mul_nonneg (sq_nonneg _) (Real.exp_pos x).le
      · filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Iio (a := -L j))] with x hx
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        apply pow_le_pow_left₀ (norm_nonneg _)
        let : BorelSpace C𝔽 := ⟨rfl⟩
        let : CompactSpace (ideleClassNorm F).ker := (ideleClassGroup_finiteness F).2.1
        let : μ.IsHaarMeasure := (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1
        change ‖∫ h : (ideleClassNorm F).ker,
          adelicTheta (idealLogRieszThetaTest τ b f (L j) (2*k j)).val (h.val * γ x) * (ω h : ℂ) ∂μ‖ ≤ M
        refine (norm_integral_le_of_norm_le_const (.of_forall fun h ↦ ?_)).trans_eq
          (by rw [measureReal_def, mul_comm])
        rw [norm_mul, Circle.norm_coe, mul_one]
        have hn := hbound b hb j (h.val * γ x) (by
          simp only [map_mul, MonoidHom.mem_ker.mp h.property, one_mul]
          exact (hγ x).trans_lt (Real.exp_lt_exp.mpr hx))
        exact hn.trans (mul_le_of_le_one_right hH (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hpos.le)))
    _ = _ := by rw [integral_const_mul, ← integral_Iic_eq_integral_Iio, integral_exp_Iic]

end RiemannMasullo
