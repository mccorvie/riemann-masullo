module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.Order.SuccPred.IntervalSucc
import Mathlib.Tactic

/-! # The rational one-prime Paley–Wiener boundary cell

In the order-zero, trivial-angular model of Theorem 12.4.1.1, pp. 515–517, the
normalized prime-frequency shells above the flat band are geometric copies of a
single Hilbert space. This file computes the actual orthogonal projection in
these coordinates. The surviving physical-origin equation is the Lebesgue mean
over the boundary interval. The local theta identification and the cutoff trace
estimate are given in the [mathematical report on issue #7354](https://github.com/mccorvie/riemann-masullo/issues/7354#issuecomment-7152208733).
-/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped ComplexConjugate ENNReal Function InnerProductSpace Interval Topology

namespace RiemannMasullo.OnePrimePW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Normalized coefficients of the exterior-shell column, for ratio `r=p⁻¹ᐟ²`. -/
def shellWeight (r : ℝ) (n : ℕ) : ℝ := Real.sqrt (1 - r ^ 2) * r ^ n

private theorem shellWeight_nonneg {r : ℝ} (hr : 0 ≤ r) (n : ℕ) : 0 ≤ shellWeight r n :=
  mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hr _)

/-- Each normalized exterior column has unit square mass. -/
theorem hasSum_shellWeight_sq {r : ℝ} (hr : 0 ≤ r) (h : r < 1) :
    HasSum (fun n : ℕ ↦ shellWeight r n ^ 2) 1 := by
  have hr₂ : r ^ 2 < 1 := by nlinarith [mul_pos (sub_pos.mpr h) (by linarith : 0 < 1 + r)]
  have hc := (hasSum_geometric_of_lt_one (sq_nonneg r) hr₂).mul_left (1 - r ^ 2)
  convert hc using 1
  · ext n
    rw [shellWeight, mul_pow, Real.sq_sqrt (by linarith), ← pow_mul, ← pow_mul, Nat.mul_comm]
  · exact (mul_inv_cancel₀ (sub_ne_zero.mpr (ne_of_gt hr₂))).symm

/-- Copies of boundary data as a vector in the Hilbert sum. -/
def shellCopies {r : ℝ} (hr : 0 ≤ r) (h : r < 1) (x : E) : lp (fun _ : ℕ ↦ E) 2 :=
  ⟨fun n ↦ (shellWeight r n : ℂ) • x, by
    apply (memℓp_gen_iff (by norm_num)).mpr
    convert (hasSum_shellWeight_sq hr h).summable.mul_right (‖x‖ ^ 2) using 1
    ext n
    simp [norm_smul, Real.norm_eq_abs, abs_of_nonneg (shellWeight_nonneg hr _),
      mul_pow]⟩

/-- Isometric geometric extension of a boundary cell to the half-line of prime cells. -/
def shellEmbedding {r : ℝ} (hr : 0 ≤ r) (h : r < 1) : E →ₗᵢ[ℂ] lp (fun _ : ℕ ↦ E) 2 := by
  let L : E →ₗ[ℂ] lp (fun _ : ℕ ↦ E) 2 :=
    { toFun := shellCopies hr h
      map_add' := by intro x y; ext n; exact smul_add _ _ _
      map_smul' := by intro c x; ext n; exact smul_comm _ _ _ }
  apply L.isometryOfInner
  intro x y
  rw [lp.inner_eq_tsum]
  have hw := Complex.ofRealCLM.hasSum (hasSum_shellWeight_sq hr h)
  convert (hw.mul_right (inner ℂ x y)).tsum_eq using 1
  · congr 1
    ext n
    change inner ℂ ((shellWeight r n : ℂ) • x) ((shellWeight r n : ℂ) • y) = _
    rw [inner_smul_left, inner_smul_right]
    rw [Complex.conj_ofReal, Complex.ofRealCLM_apply, Complex.ofReal_pow, pow_two, mul_assoc]
  · change _ = (1 : ℂ) * _
    rw [one_mul]

@[simp] theorem shellEmbedding_apply {r : ℝ} (hr : 0 ≤ r) (h : r < 1) (x : E) (n : ℕ) :
    shellEmbedding hr h x n = (shellWeight r n : ℂ) • x := rfl

variable [CompleteSpace E]

private theorem summable_weighted_cells {r : ℝ} (hr : 0 ≤ r) (h : r < 1) (y : lp (fun _ : ℕ ↦ E) 2) :
    Summable (fun n ↦ (shellWeight r n : ℂ) • y n) := by
  have hc := ((hasSum_geometric_of_lt_one hr h).summable.mul_left
    (Real.sqrt (1 - r ^ 2))).mul_right ‖y‖
  apply hc.of_norm_bounded
  intro n
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (shellWeight_nonneg hr n)]
  exact mul_le_mul_of_nonneg_left (lp.norm_apply_le_norm (by norm_num) y n) (shellWeight_nonneg hr n)

/-- The real-coefficient geometric exterior column has the expected weighted sum as its adjoint. -/
theorem shellEmbedding_adjoint_apply {r : ℝ} (hr : 0 ≤ r) (h : r < 1) (y : lp (fun _ : ℕ ↦ E) 2) :
    (shellEmbedding hr h).toContinuousLinearMap.adjoint y = ∑' n, (shellWeight r n : ℂ) • y n := by
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.adjoint_inner_right, lp.inner_eq_tsum]
  have he := (innerSL ℂ x).map_tsum (summable_weighted_cells hr h y)
  change _ = (innerSL ℂ x) (∑' n, (shellWeight r n : ℂ) • y n)
  rw [he]
  apply tsum_congr
  intro n
  change inner ℂ ((shellWeight r n : ℂ) • x) (y n) = inner ℂ x ((shellWeight r n : ℂ) • y n)
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-- Exterior graph with boundary data in `K`. For the actual polar-free band,
`K` is the space of mean-zero boundary data. -/
def shellSubspace {r : ℝ} (hr : 0 ≤ r) (h : r < 1) (K : Submodule ℂ E) :
    Submodule ℂ (lp (fun _ : ℕ ↦ E) 2) :=
  ((shellEmbedding hr h).comp K.subtypeₗᵢ).toLinearMap.range

private theorem shellWeight_succ (r : ℝ) (n : ℕ) :
    (shellWeight r (n + 1) : ℂ) = (r : ℂ) * shellWeight r n := by
  push_cast [shellWeight, pow_succ]
  ring

/-- The graph consists exactly of square-summable families satisfying the
one-step scaling relation and the boundary condition at the first shell. -/
theorem mem_shellSubspace_iff {r : ℝ} (hr : 0 ≤ r) (h : r < 1) (K : Submodule ℂ E)
    (y : lp (fun _ : ℕ ↦ E) 2) :
    y ∈ shellSubspace hr h K ↔ y 0 ∈ K ∧ ∀ n : ℕ, y (n + 1) = (r : ℂ) • y n := by
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨K.smul_mem (shellWeight r 0 : ℂ) z.property, ?_⟩
    intro n
    change (shellWeight r (n + 1) : ℂ) • (z : E) = (r : ℂ) • (shellWeight r n : ℂ) • (z : E)
    rw [shellWeight_succ, mul_smul]
  · rintro ⟨hz, hrel⟩
    let c : ℂ := shellWeight r 0
    have hsq : r ^ 2 < 1 := by nlinarith [mul_pos (sub_pos.mpr h) (by linarith : 0 < 1 + r)]
    have hc : c ≠ 0 := by
      dsimp [c, shellWeight]
      simpa using (Real.sqrt_pos.mpr (sub_pos.mpr hsq)).ne'
    let z : K := ⟨c⁻¹ • y 0, K.smul_mem _ hz⟩
    refine ⟨z, ?_⟩
    change shellEmbedding hr h (z : E) = y
    ext n
    change (shellWeight r n : ℂ) • (z : E) = y n
    induction n with
    | zero =>
      change c • c⁻¹ • y 0 = y 0
      rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
    | succ n ih => rw [shellWeight_succ, mul_smul, ih, hrel]

instance shellSubspace_complete {r : ℝ} (hr : 0 ≤ r) (h : r < 1)
    (K : Submodule ℂ E) [CompleteSpace K] : CompleteSpace (shellSubspace hr h K) :=
  ((shellEmbedding hr h).comp K.subtypeₗᵢ).isometry.isClosedEmbedding.isClosed_range.completeSpace_coe

/-- Exact orthogonal projector on the geometric shell graph with an arbitrary
closed boundary constraint. The input and output shell numbers are independent. -/
theorem shellSubspace_starProjection {r : ℝ} (hr : 0 ≤ r) (h : r < 1) (K : Submodule ℂ E)
    [CompleteSpace K] (y : lp (fun _ : ℕ ↦ E) 2) (n : ℕ) :
    (shellSubspace hr h K).starProjection y n =
      (shellWeight r n : ℂ) • K.starProjection (∑' k, (shellWeight r k : ℂ) • y k) := by
  let J : E →ₗᵢ[ℂ] lp (fun _ : ℕ ↦ E) 2 := shellEmbedding hr h
  let a := J.toContinuousLinearMap.adjoint y
  have he : (shellSubspace hr h K).starProjection y = J (K.starProjection a) := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact ⟨⟨K.starProjection a, K.starProjection_apply_mem a⟩, rfl⟩
    · rintro _ ⟨z, rfl⟩
      change inner ℂ (y - J (K.starProjection a)) (J (z : E)) = 0
      rw [inner_sub_left, J.inner_map_map]
      change inner ℂ y (J.toContinuousLinearMap (z : E)) - _ = _
      rw [← J.toContinuousLinearMap.adjoint_inner_left]
      simpa only [inner_sub_left] using K.starProjection_inner_eq_zero a _ z.property
  rw [he]
  change (shellWeight r n : ℂ) • K.starProjection ((shellEmbedding hr h).toContinuousLinearMap.adjoint y) = _
  rw [shellEmbedding_adjoint_apply]

private theorem bandInterval {F : ℝ → ℂ} (hf : MemLp F 2 volume) (a b : ℝ) :
    IntervalIntegrable F volume a b :=
  (intervalIntegrable_iff' (by finiteness)).mpr
    ((hf.locallyIntegrable (by norm_num)).integrableOn_isCompact isCompact_uIcc)

/-- On the actual unweighted Fourier profile the surviving physical-origin pole
reduces to a mean over the one outermost band cell. -/
theorem integral_inverseStretch_eq_cell {F : ℝ → ℂ} (hf : MemLp F 2 volume)
    (B p : ℝ) (hp : p ≠ 0) :
    (∫ x in (0 : ℝ)..B, F x - p⁻¹ • F (x / p)) = ∫ x in B / p..B, F x := by
  have hd : IntervalIntegrable (fun x ↦ F (x / p)) volume 0 B := by
    have h := (bandInterval hf 0 (B / p)).comp_mul_right (c := p⁻¹)
    simpa [div_eq_mul_inv, mul_assoc, hp] using h
  have hds : IntervalIntegrable (fun x ↦ p⁻¹ • F (x / p)) volume 0 B := by
    convert hd.smul (p⁻¹ : ℝ) using 1
  rw [intervalIntegral.integral_sub (bandInterval hf _ _) hds,
    intervalIntegral.integral_smul, intervalIntegral.inv_smul_integral_comp_div, zero_div]
  exact intervalIntegral.integral_interval_sub_left (bandInterval hf _ _) (bandInterval hf _ _)

/-- For exterior data with prime scaling, the Lebesgue integral over a frequency
window of multiplicative width p is independent of its location. The scaling law
only has to hold almost everywhere above the first cell. -/
theorem integral_cell_eq_of_scale {F : ℝ → ℂ} (hf : MemLp F 2 volume)
    (p b u : ℝ) (hbu : b ≤ u) (hrel : ∀ᵐ x : ℝ, b ≤ x → p • F (p * x) = F x) :
    (∫ x in u..p * u, F x) = ∫ x in b..p * b, F x := by
  apply sub_eq_zero.mp
  rw [intervalIntegral.integral_interval_sub_interval_comm' (bandInterval hf _ _)
    (bandInterval hf _ _) (bandInterval hf _ _)]
  apply sub_eq_zero.mpr
  rw [← intervalIntegral.smul_integral_comp_mul_left F p, ← intervalIntegral.integral_smul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [hrel] with x hx hxu
  rw [uIoc_of_le hbu] at hxu
  exact hx hxu.1.le

/-- The surviving cell mean is an eigenfunctional of every positive unitary
dilation by a ≥ 1, on the actual a.e. prime-scaling graph. -/
theorem integral_cell_dilation {F : ℝ → ℂ} (hf : MemLp F 2 volume) (p b a : ℝ)
    (hb : 0 ≤ b) (ha : 1 ≤ a) (hrel : ∀ᵐ x : ℝ, b ≤ x → p • F (p * x) = F x) :
    (∫ x in b..p * b, Real.sqrt a • F (a * x)) =
      (Real.sqrt a)⁻¹ • ∫ x in b..p * b, F x := by
  have ha₀ : 0 < a := by linarith
  have hm := integral_cell_eq_of_scale hf p b (a * b) (le_mul_of_one_le_left hb ha) hrel
  rw [intervalIntegral.integral_smul, intervalIntegral.integral_comp_mul_left F ha₀.ne',
    show a * (p * b) = p * (a * b) by ring, hm, smul_smul]
  congr 1
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha₀
  field_simp
  nlinarith [Real.sq_sqrt ha₀.le]

local notation "cellMeasure(" l "," u ")" => Measure.restrict (volume : Measure ℝ) (Ioc l u)
local notation "Cell(" l "," u ")" => Lp ℂ 2 cellMeasure(l, u)

/-- The constant one on the physical boundary cell with Lebesgue measure. -/
def cellOne (l u : ℝ) : Cell(l, u) :=
  indicatorConstLp (s := Ioc l u) 2 measurableSet_Ioc (by
    rw [Measure.restrict_apply measurableSet_Ioc, inter_self, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top) (1 : ℂ)

private theorem cellOne_inner (l u : ℝ) (f : Cell(l, u)) :
    inner ℂ (cellOne l u) f = ∫ x in Ioc l u, f x := by
  rw [cellOne, L2.inner_indicatorConstLp_one, Measure.restrict_restrict measurableSet_Ioc, inter_self]

private theorem cellOne_norm_sq {l u : ℝ} (h : l ≤ u) :
    ((‖cellOne l u‖ ^ 2 : ℝ) : ℂ) = (↑(u - l) : ℂ) := by
  rw [Complex.ofReal_pow]
  calc
    _ = inner ℂ (cellOne l u) (cellOne l u) := (inner_self_eq_norm_sq_to_K _).symm
    _ = _ := by
      rw [cellOne, L2.inner_indicatorConstLp_one_indicatorConstLp_one, inter_self, Measure.real,
        Measure.restrict_apply measurableSet_Ioc, inter_self, Real.volume_Ioc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr h), RCLike.ofReal_eq_complex_ofReal]

/-- The closed subspace of boundary data with zero Lebesgue mean. -/
def meanZeroCell (l u : ℝ) : Submodule ℂ Cell(l, u) := (ℂ ∙ cellOne l u)ᗮ

instance meanZeroCell_complete (l u : ℝ) : CompleteSpace (meanZeroCell l u) :=
  (ℂ ∙ cellOne l u).isClosed_orthogonal.completeSpace_coe

/-- Membership in the boundary constraint is exactly vanishing of the cell integral. -/
theorem mem_meanZeroCell_iff (l u : ℝ) (f : Cell(l, u)) :
    f ∈ meanZeroCell l u ↔ (∫ x in Ioc l u, f x) = 0 := by
  rw [meanZeroCell, Submodule.mem_orthogonal_singleton_iff_inner_right, cellOne_inner]

/-- On the raw one-prime band, the surviving origin equation is exactly membership
of the physical boundary restriction in the mean-zero cell. -/
theorem mem_meanZeroCell_restrict_iff {p B : ℝ} (hp : 1 ≤ p) (hB : 0 ≤ B)
    {F : ℝ → ℂ} (hf : MemLp F 2 volume) :
    ((hf.restrict (Ioc (B / p) B)).toLp F) ∈ meanZeroCell (B / p) B ↔
      (∫ x in (0 : ℝ)..B, F x - p⁻¹ • F (x / p)) = 0 := by
  have hp₀ : 0 < p := by linarith
  have hband : B / p ≤ B := (div_le_iff₀ hp₀).mpr (le_mul_of_one_le_right hB hp)
  rw [mem_meanZeroCell_iff, integral_inverseStretch_eq_cell hf B p hp₀.ne',
    intervalIntegral.integral_of_le hband]
  rw [integral_congr_ae (hf.restrict _).coeFn_toLp]

/-- At shell n the actual orthogonal projection removes the Lebesgue mean of the
weighted sum of all exterior shells. This is the one-prime physical boundary-cell
model of (11.2.1.6) at Sobolev order zero. -/
theorem meanZeroShell_starProjection {r l u : ℝ} (hr : 0 ≤ r) (h : r < 1) (hlu : l ≤ u)
    (y : lp (fun _ : ℕ ↦ Cell(l, u)) 2) (n : ℕ) :
    let f := ∑' k, (shellWeight r k : ℂ) • y k
    (shellSubspace hr h (meanZeroCell l u)).starProjection y n =
      (shellWeight r n : ℂ) • (f - ((∫ x in Ioc l u, f x) / (↑(u - l) : ℂ)) • cellOne l u) := by
  intro f
  rw [shellSubspace_starProjection]
  congr 1
  change (ℂ ∙ cellOne l u)ᗮ.starProjection f = _
  rw [Submodule.starProjection_orthogonal, sub_apply,
    ContinuousLinearMap.id_apply, Submodule.starProjection_singleton, RCLike.ofReal_eq_complex_ofReal,
    cellOne_norm_sq hlu, cellOne_inner]

private theorem sampling_norm_sq_toLp {μ : Measure ℝ} {g : ℝ → ℂ} (hg : MemLp g 2 μ) :
    ‖hg.toLp g‖ ^ 2 = ∫ t, ‖g t‖ ^ 2 ∂μ := by
  calc
    ‖hg.toLp g‖ ^ 2 = ∫ t, ‖(hg.toLp g) t‖ ^ 2 ∂μ := by
      rw [@InnerProductSpace.norm_sq_eq_re_inner ℂ, L2.inner_def]
      simp_rw [inner_self_eq_norm_sq_to_K]
      norm_cast
    _ = _ := integral_congr_ae (hg.coeFn_toLp.fun_comp (fun z : ℂ ↦ ‖z‖ ^ 2))

private theorem sampling_memLp {F : ℝ → ℂ} (hF : MemLp F 2 volume)
    {c : ℝ} (hc : 0 < c) (s : Set ℝ) :
    MemLp (fun t ↦ (Real.sqrt c : ℂ) * F (c * t)) 2 (volume.restrict s) := by
  have hm : MemLp F 2 (Measure.map (fun t : ℝ ↦ c * t) volume) := by
    rw [Real.map_volume_mul_left hc.ne']
    exact hF.smul_measure ENNReal.ofReal_ne_top
  have hcomp : MemLp (fun t : ℝ ↦ F (c * t)) 2 volume :=
    hm.comp_of_map (measurable_const_mul c).aemeasurable
  exact (hcomp.const_mul (Real.sqrt c : ℂ)).restrict s

private theorem sampling_norm_sq_cell {F : ℝ → ℂ} {c b d : ℝ} (hc : 0 < c)
    (hbd : b ≤ d)
    (hg : MemLp (fun t ↦ (Real.sqrt c : ℂ) * F (c * t)) 2 (volume.restrict (Ioc b d))) :
    ‖hg.toLp _‖ ^ 2 = ∫ t in Ioc (c * b) (c * d), ‖F t‖ ^ 2 := by
  rw [sampling_norm_sq_toLp]
  simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg c), mul_pow,
    Real.sq_sqrt hc.le]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hbd,
    ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hbd hc.le)]
  exact intervalIntegral.smul_integral_comp_mul_left (fun t ↦ ‖F t‖ ^ 2) c

/-- The normalized restrictions of a square-integrable representative to the
positive cells (p^k b, p^(k+1)b] form an actual ℓ² family on (b,pb]. The squared
norms sum to the energy above b. The sampled coordinate formulas hold on one
common conull subset of the boundary cell. -/
private theorem exists_physicalShellSamples {F : ℝ → ℂ} (hF : MemLp F 2 volume)
    {p b : ℝ} (hp : 1 < p) (hb : 0 < b) :
    ∃ Y : lp (fun _ : ℕ ↦ Lp ℂ 2 (volume.restrict (Ioc b (p * b)))) 2,
      (∀ᵐ t ∂volume.restrict (Ioc b (p * b)), ∀ k : ℕ,
        (Y k) t = (Real.sqrt (p ^ k) : ℂ) * F (p ^ k * t)) ∧
      HasSum (fun k : ℕ ↦ ‖Y k‖ ^ 2) (∫ t in Ioi b, ‖F t‖ ^ 2) := by
  let I := Ioc b (p * b)
  let s (k : ℕ) := Ioc (p ^ k * b) (p ^ (k + 1) * b)
  let g (k : ℕ) (t : ℝ) : ℂ := (Real.sqrt (p ^ k) : ℂ) * F (p ^ k * t)
  have hp₀ : 0 < p := zero_lt_one.trans hp
  have hg (k : ℕ) : MemLp (g k) 2 (volume.restrict I) :=
    sampling_memLp hF (pow_pos hp₀ k) I
  let y (k : ℕ) : Lp ℂ 2 (volume.restrict I) := (hg k).toLp (g k)
  have he (k : ℕ) : ‖y k‖ ^ 2 = ∫ t in s k, ‖F t‖ ^ 2 := by
    change ‖(hg k).toLp (g k)‖ ^ 2 =
      ∫ t in Ioc (p ^ k * b) (p ^ (k + 1) * b), ‖F t‖ ^ 2
    have hpow : p ^ (k + 1) * b = p ^ k * (p * b) := by rw [pow_succ, mul_assoc]
    rw [hpow]
    exact sampling_norm_sq_cell (F := F) (pow_pos hp₀ k) (le_mul_of_one_le_left hb.le hp.le) (hg k)
  have hmono : Monotone (fun k : ℕ ↦ p ^ k * b) := fun _ _ h ↦
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hp.le h) hb.le
  have hd : Pairwise (Disjoint on s) := hmono.pairwise_disjoint_on_Ioc_succ
  have htop : Tendsto (fun k : ℕ ↦ p ^ k * b) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hp).atTop_mul_const hb
  have hu : (⋃ k, s k) = Ioi b := by
    simpa [s, Order.succ_eq_add_one] using
      (iUnion_Ioc_map_succ_eq_Ioi (f := fun k : ℕ ↦ p ^ k * b)
        (fun k ↦ hmono (show (⊥ : ℕ) ≤ k from bot_le)) (not_bddAbove_of_tendsto_atTop htop))
  have hfi : Integrable (fun t : ℝ ↦ ‖F t‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
  have hsum : HasSum (fun k : ℕ ↦ ‖y k‖ ^ 2) (∫ t in Ioi b, ‖F t‖ ^ 2) := by
    simpa only [he, hu] using
      (hasSum_integral_iUnion (μ := volume) (f := fun t : ℝ ↦ ‖F t‖ ^ 2)
        (s := s) (fun _ ↦ measurableSet_Ioc) hd hfi.integrableOn)
  have hmem : Memℓp y 2 := (memℓp_gen_iff (by norm_num)).2 (by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hsum.summable)
  exact ⟨⟨y, hmem⟩, ae_all_iff.mpr (fun k ↦ (hg k).coeFn_toLp), hsum⟩

/-- The normalized shell ratio of a rational prime is strictly less than one. -/
theorem inv_sqrt_prime_lt_one {p : ℕ} (hp : p.Prime) : (Real.sqrt (p : ℝ))⁻¹ < 1 := by
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  apply inv_lt_one_of_one_lt₀
  nlinarith [Real.sq_sqrt (show 0 ≤ (p : ℝ) by positivity), Real.sqrt_nonneg (p : ℝ)]

/-- The polar-free exterior graph of the rational one-prime band. Its first
frequency cell is `(b, p b]` and its normalized shell ratio is `1 / √p`. -/
def polarFreeShellSubspace {p : ℕ} (hp : p.Prime) (b : ℝ) :
    Submodule ℂ (lp (fun _ : ℕ ↦ Cell(b, (p : ℝ) * b)) 2) :=
  shellSubspace (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_sqrt_prime_lt_one hp)
    (meanZeroCell b (p * b))

instance polarFreeShellSubspace_complete {p : ℕ} (hp : p.Prime) (b : ℝ) :
    CompleteSpace (polarFreeShellSubspace hp b) := by
  unfold polarFreeShellSubspace
  infer_instance

/-- On the prime-frequency shells, the raw finite-band condition is the
one-step inverse-square-root-prime scaling law. Removing the physical-origin
pole imposes precisely the additional vanishing of the first Lebesgue mean. -/
theorem mem_polarFreeShellSubspace_iff {p : ℕ} (hp : p.Prime) (b : ℝ)
    (y : lp (fun _ : ℕ ↦ Cell(b, (p : ℝ) * b)) 2) :
    y ∈ polarFreeShellSubspace hp b ↔ (∫ t in Ioc b ((p : ℝ) * b), (y 0) t) = 0 ∧
      ∀ n : ℕ, y (n + 1) = (((Real.sqrt (p : ℝ))⁻¹ : ℝ) : ℂ) • y n := by
  rw [polarFreeShellSubspace, mem_shellSubspace_iff, mem_meanZeroCell_iff]

private theorem shellEmbedding_mem_iff {r : ℝ} (hr : 0 ≤ r) (h : r < 1)
    (K : Submodule ℂ E) (x : E) :
    shellEmbedding hr h x ∈ shellSubspace hr h K ↔ x ∈ K := by
  constructor
  · rintro ⟨z, hz⟩
    obtain rfl : (z : E) = x := (shellEmbedding hr h).injective hz
    exact z.property
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

private theorem shellSubspace_fixes_iff {r : ℝ} (hr : 0 ≤ r) (h : r < 1)
    (K : Submodule ℂ E) [CompleteSpace K] (x : E) :
    (shellSubspace hr h K).starProjection (shellEmbedding hr h x) = shellEmbedding hr h x ↔ x ∈ K :=
  (Submodule.starProjection_eq_self_iff (K := shellSubspace hr h K)).trans
    (shellEmbedding_mem_iff hr h K x)

/-- The normalized exterior extension of a physical boundary restriction is
fixed by the polar-free projector exactly when the inverse stretch has zero
integral on the raw band. -/
theorem polarFreeShellSubspace_fixes_extension_iff {p : ℕ} (hp : p.Prime)
    {b : ℝ} (hb : 0 ≤ b) {F : ℝ → ℂ} (hF : MemLp F 2 volume) :
    let f := (hF.restrict (Ioc b ((p : ℝ) * b))).toLp F
    let y := shellEmbedding (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_sqrt_prime_lt_one hp) f
    (polarFreeShellSubspace hp b).starProjection y = y ↔
      (∫ t in (0 : ℝ)..(p : ℝ) * b, F t - (p : ℝ)⁻¹ • F (t / p)) = 0 := by
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hcell : (p : ℝ) * b / p = b := mul_div_cancel_left₀ b (zero_lt_one.trans hp₁).ne'
  refine (shellSubspace_fixes_iff (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_sqrt_prime_lt_one hp)
    (meanZeroCell b ((p : ℝ) * b)) ((hF.restrict (Ioc b ((p : ℝ) * b))).toLp F)).trans ?_
  have hm := mem_meanZeroCell_restrict_iff (p := (p : ℝ)) (B := (p : ℝ) * b) hp₁.le
    (mul_nonneg (zero_lt_one.trans hp₁).le hb) hF
  rw [hcell] at hm
  exact hm

/-- Paper: Theorem 12.4.1.1, Step III, p. 517; cf. (11.2.1.6), p. 488.
The orthogonal projection averages the normalized exterior samples of a physical
frequency profile with geometric weights and removes their Lebesgue mean. The
sampling preserves the exterior energy exactly.

Deviation: one rational finite prime, trivial angular type, and Sobolev order zero. -/
theorem exists_polarFreeShellProjection {p : ℕ} (hp : p.Prime) {b : ℝ} (hb : 0 < b)
    {F : ℝ → ℂ} (hF : MemLp F 2 volume) :
    ∃ y : lp (fun _ : ℕ ↦ Cell(b, (p : ℝ) * b)) 2,
      (∀ᵐ t ∂cellMeasure(b, (p : ℝ) * b), ∀ k : ℕ,
        (y k) t = (Real.sqrt ((p : ℝ) ^ k) : ℂ) * F ((p : ℝ) ^ k * t)) ∧
      HasSum (fun k : ℕ ↦ ‖y k‖ ^ 2) (∫ t in Ioi b, ‖F t‖ ^ 2) ∧
      let w := shellWeight (Real.sqrt (p : ℝ))⁻¹
      let f := ∑' k, (w k : ℂ) • y k
      ∀ n : ℕ, (polarFreeShellSubspace hp b).starProjection y n =
        (w n : ℂ) • (f - ((∫ t in Ioc b ((p : ℝ) * b), f t) / (↑((p : ℝ) * b - b) : ℂ)) •
          cellOne b (p * b)) := by
  have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  obtain ⟨y, hy, he⟩ := exists_physicalShellSamples hF hp₁ hb
  refine ⟨y, hy, he, ?_⟩
  dsimp only
  intro n
  exact meanZeroShell_starProjection (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_sqrt_prime_lt_one hp)
    (le_mul_of_one_le_left hb.le hp₁.le) y n

end RiemannMasullo.OnePrimePW
