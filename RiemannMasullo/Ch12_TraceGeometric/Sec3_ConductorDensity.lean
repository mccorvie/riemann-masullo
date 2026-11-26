module

public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic

/-! # Conductor averages for omitted orders of primitive Dirichlet L-functions

Montgomery's single-modulus product estimate, in the closed-rectangle form of
M. Jutila, *On a density theorem of H. L. Montgomery for L-functions* (1972), (1.1),
enters through `MontgomeryProductCount`. The reduction to primitive multiplicities
and the fixed-test conductor bound are proved below.
-/

@[expose] public noncomputable section

open Filter Set Function MeasureTheory
open scoped Topology BigOperators ContDiff

namespace RiemannMasullo.ConductorDensity

/-- All level characters index their primitive lifts, including lifts of lower conductor. -/
abbrev Site (q : ℕ) := DirichletCharacter ℂ q × {z : ℂ // 0 < z.re ∧ z.re < 1}

def ordinaryOrder {q : ℕ} [NeZero q] (i : Site q) : ℕ :=
  (meromorphicOrderAt (DirichletCharacter.LFunction i.1) i.2.val).untop₀.toNat

def completedPrimitiveOrder {q : ℕ} [NeZero q] (i : Site q) : ℕ :=
  haveI : NeZero i.1.conductor := ⟨i.1.conductor_ne_zero⟩
  (meromorphicOrderAt (DirichletCharacter.completedLFunction i.1.primitiveCharacter)
    i.2.val).untop₀.toNat

private theorem order_changeLevel {d q : ℕ} [NeZero d] [NeZero q]
    (hdq : d ∣ q) (χ : DirichletCharacter ℂ d) {s : ℂ} (hs : 0 < s.re) (h1 : s ≠ 1) :
    meromorphicOrderAt (DirichletCharacter.LFunction (χ.changeLevel hdq)) s =
    meromorphicOrderAt (DirichletCharacter.LFunction χ) s := by
  let F (w : ℂ) := ∏ p ∈ q.primeFactors, (1 - χ p * (p : ℂ) ^ (-w))
  have hF : Differentiable ℂ F := by
    intro w
    refine DifferentiableAt.fun_finsetProd fun p hp ↦ ?_
    have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
    fun_prop (disch := first | exact hp0 | exact Or.inl hp0)
  have hF0 : F s ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ sub_ne_zero.mpr (fun h ↦ ?_)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
      rw [Complex.norm_natCast_cpow_of_pos (Nat.prime_of_mem_primeFactors hp).pos,
        Complex.neg_re]
      exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (neg_lt_zero.mpr hs)
    have hn := congrArg norm h
    rw [norm_one, norm_mul] at hn
    nlinarith [DirichletCharacter.norm_le_one χ (p : ZMod d),
      norm_nonneg (χ p), norm_nonneg ((p : ℂ) ^ (-s))]
  refine (meromorphicOrderAt_congr (f₂ := F * DirichletCharacter.LFunction χ) ?_).trans
    (meromorphicOrderAt_mul_of_ne_zero (hF.analyticAt s) hF0)
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [isOpen_ne.mem_nhds h1] with w hw
  simpa [F, mul_comm] using DirichletCharacter.LFunction_changeLevel hdq χ (.inr hw)

/-- Completion by the archimedean gamma factor preserves the Dirichlet order in the
positive half-plane. -/
theorem order_completion {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (DirichletCharacter.LFunction χ) s =
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) s := by
  let G (w : ℂ) := (χ.gammaFactor w)⁻¹
  have hG : Differentiable ℂ G := by
    rcases χ.even_or_odd with he | ho
    · simpa [G, he.gammaFactor_def] using Complex.differentiable_Gammaℝ_inv
    · simpa [G, ho.gammaFactor_def, Function.comp_def] using
        Complex.differentiable_Gammaℝ_inv.comp (differentiable_id.add_const (1 : ℂ))
  have hG0 : G s ≠ 0 := by
    apply inv_ne_zero
    rcases χ.even_or_odd with he | ho
    · exact he.gammaFactor_def s ▸ Complex.Gammaℝ_ne_zero_of_re_pos hs
    · rw [ho.gammaFactor_def]
      apply Complex.Gammaℝ_ne_zero_of_re_pos
      simpa using (show 0 < s.re + 1 by linarith)
  refine (meromorphicOrderAt_congr (f₂ := G * DirichletCharacter.completedLFunction χ) ?_).trans
    (meromorphicOrderAt_mul_of_ne_zero (hG.analyticAt s) hG0)
  have hs0 : s ≠ 0 := fun h ↦ by simp [h] at hs
  apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
  filter_upwards [isOpen_ne.mem_nhds hs0] with w hw
  simpa [G, div_eq_mul_inv, mul_comm] using χ.LFunction_eq_completed_div_gammaFactor w (.inl hw)

theorem ordinaryOrder_eq_completedPrimitiveOrder {q : ℕ} [NeZero q] (i : Site q) :
    ordinaryOrder i = completedPrimitiveOrder i := by
  let : NeZero i.1.conductor := ⟨i.1.conductor_ne_zero⟩
  have h1 : i.2.val ≠ 1 := fun h ↦ by simpa [h] using i.2.property.2
  have h := order_changeLevel i.1.conductor_dvd_level i.1.primitiveCharacter i.2.property.1 h1
  rw [DirichletCharacter.changeLevel_primitiveCharacter] at h
  exact congrArg (fun o : WithTop ℤ ↦ o.untop₀.toNat)
    (h.trans (order_completion i.1.primitiveCharacter i.2.property.1))

private theorem order_one_sub {d : ℕ} [NeZero d] (χ : DirichletCharacter ℂ d)
    (hχ : χ.IsPrimitive) (s : ℂ) :
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) (1 - s) =
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ⁻¹) s := by
  let G (w : ℂ) := (d : ℂ) ^ (w - 1 / 2) * χ.rootNumber
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne d
  have hG : Differentiable ℂ G := by dsimp [G]; fun_prop (disch := first | exact hd | exact Or.inl hd)
  have hG0 : G s ≠ 0 := mul_ne_zero (by simp [hd]) (χ.rootNumber_ne_zero hχ)
  have h' : deriv (fun w : ℂ ↦ 1 - w) s ≠ 0 := by simp
  rw [← meromorphicOrderAt_comp_of_deriv_ne_zero (f := DirichletCharacter.completedLFunction χ)
    (g := fun w : ℂ ↦ 1 - w) (by fun_prop) h']
  have heq : (DirichletCharacter.completedLFunction χ) ∘ (fun w : ℂ ↦ 1 - w) =
      G * DirichletCharacter.completedLFunction χ⁻¹ := funext hχ.completedLFunction_one_sub
  rw [heq]
  exact meromorphicOrderAt_mul_of_ne_zero (hG.analyticAt s) hG0

def reflect {q : ℕ} (i : Site q) : Site q :=
  ⟨i.1⁻¹, 1 - i.2.val, by simp only [Complex.sub_re, Complex.one_re]; constructor <;> linarith [i.2.property]⟩

theorem reflect_involutive {q : ℕ} : Function.Involutive (reflect (q := q)) := by
  intro i
  ext <;> simp [reflect]

theorem ordinaryOrder_reflect {q : ℕ} [NeZero q] (i : Site q) :
    ordinaryOrder (reflect i) = ordinaryOrder i := by
  let χ := i.1.primitiveCharacter
  let : NeZero i.1.conductor := ⟨i.1.conductor_ne_zero⟩
  have h1 : i.2.val ≠ 1 := fun h ↦ by simpa [h] using i.2.property.2
  have hs0 : 0 < (1 - i.2.val).re := (reflect i).2.property.1
  have hs1 : 1 - i.2.val ≠ 1 := by
    intro h
    have hz : i.2.val = 0 := by linear_combination -h
    simpa [hz] using i.2.property.1
  have hχ : χ.changeLevel i.1.conductor_dvd_level = i.1 := i.1.changeLevel_primitiveCharacter
  have hχinv : χ⁻¹.changeLevel i.1.conductor_dvd_level = i.1⁻¹ := by
    rw [map_inv, hχ]
  apply congrArg (fun o : WithTop ℤ ↦ o.untop₀.toNat)
  change meromorphicOrderAt (DirichletCharacter.LFunction i.1⁻¹) (1 - i.2.val) = _
  rw [← hχinv, order_changeLevel _ _ hs0 hs1, order_completion _ hs0,
    order_one_sub _ i.1.primitiveCharacter_isPrimitive.inv, inv_inv,
    ← order_completion _ i.2.property.1, ← order_changeLevel i.1.conductor_dvd_level χ i.2.property.1 h1, hχ]

theorem completedPrimitiveOrder_reflect {q : ℕ} [NeZero q] (i : Site q) :
    completedPrimitiveOrder (reflect i) = completedPrimitiveOrder i := by
  simpa only [← ordinaryOrder_eq_completedPrimitiveOrder] using ordinaryOrder_reflect i

/-- The finite-subset consequence of Montgomery's one-modulus estimate, Jutila (1.1).
Both horizontal edges and the vertical edge at `σ` are included. Nonzero summands use the
order of the ordinary Dirichlet function of the character at level `q`. -/
def MontgomeryCount (σ θ C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : ℝ), 2 ≤ T → ∀ S : Finset (Site q),
    (∀ i ∈ S, σ ≤ i.2.val.re ∧ |i.2.val.im| ≤ T) →
    ∑ i ∈ S, (ordinaryOrder i : ℝ) ≤ C * ((q : ℝ) * T) ^ θ * Real.log (q * T) ^ 14

/-- Positive multiplicity of the ordinary product over every character of one modulus. -/
def productOrder (q : ℕ) [NeZero q] (z : ℂ) : ℕ :=
  (meromorphicOrderAt (∏ χ : DirichletCharacter ℂ q, DirichletCharacter.LFunction χ) z).untop₀.toNat

/-- Jutila's original closed rectangle, expressed on arbitrary finite subsets. -/
def MontgomeryProductCount (σ θ C : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (T : ℝ), 2 ≤ T → ∀ Z : Finset ℂ,
    (∀ z ∈ Z, σ ≤ z.re ∧ z.re ≤ 1 ∧ |z.im| ≤ T) →
    ∑ z ∈ Z, (productOrder q z : ℝ) ≤ C * ((q : ℝ) * T) ^ θ * Real.log (q * T) ^ 14

private theorem ordinary_analytic {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) ({1}ᶜ : Set ℂ) :=
  (show DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {1}ᶜ from fun z hz ↦
    (χ.differentiableAt_LFunction z (.inl hz)).differentiableWithinAt).analyticOnNhd isOpen_compl_singleton

private theorem ordinary_order_coe {q : ℕ} [NeZero q] (i : Site q) :
    meromorphicOrderAt (DirichletCharacter.LFunction i.1) i.2.val =
      ((ordinaryOrder i : ℤ) : WithTop ℤ) := by
  have ha := ordinary_analytic i.1
  have hs : i.2.val ∈ ({1}ᶜ : Set ℂ) := fun h ↦ by
    change i.2.val = 1 at h
    simpa [h] using i.2.property.2
  have h2 : (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) := by simp
  have h2ord : analyticOrderAt (DirichletCharacter.LFunction i.1) (2 : ℂ) = 0 :=
    (ha _ h2).analyticOrderAt_eq_zero.mpr
      (i.1.LFunction_ne_zero_of_one_le_re (.inr (by norm_num)) (by norm_num))
  have hconn := (isConnected_compl_singleton_of_one_lt_rank (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)
    (1 : ℂ)).isPreconnected
  have hfin := ha.analyticOrderAt_ne_top_of_isPreconnected hconn h2 hs (by simp [h2ord])
  obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.mp hfin
  have horder : meromorphicOrderAt (DirichletCharacter.LFunction i.1) i.2.val = ((k : ℤ) : WithTop ℤ) := by
    rw [(ha _ hs).meromorphicOrderAt_eq, ← hk]
    rfl
  simp [ordinaryOrder, horder]

theorem productOrder_eq_sum {q : ℕ} [NeZero q]
    (z : {z : ℂ // 0 < z.re ∧ z.re < 1}) :
    productOrder q z.val = ∑ χ : DirichletCharacter ℂ q, ordinaryOrder (χ, z) := by
  classical
  have hs : z.val ∈ ({1}ᶜ : Set ℂ) := fun h ↦ by
    change z.val = 1 at h
    simpa [h] using z.property.2
  have hprod : meromorphicOrderAt (∏ χ : DirichletCharacter ℂ q, DirichletCharacter.LFunction χ) z.val =
      (((∑ χ : DirichletCharacter ℂ q, ordinaryOrder (χ, z) : ℕ) : ℤ) : WithTop ℤ) := by
    rw [meromorphicOrderAt_prod (fun χ _ ↦ (ordinary_analytic χ _ hs).meromorphicAt)]
    push_cast
    exact Finset.sum_congr rfl fun χ _ ↦ ordinary_order_coe (χ, z)
  rw [productOrder, hprod, WithTop.untop₀_coe, Int.toNat_natCast]

/-- Passing from the product to character labels preserves coincident zeros with their full
multiplicities. The pole at `1` lies outside each labelled strip site. -/
theorem MontgomeryProductCount.to_count {σ θ C : ℝ} (hp : MontgomeryProductCount σ θ C) :
    MontgomeryCount σ θ C := by
  classical
  intro q _ T hT S hS
  let Z := S.image Prod.snd
  have hsub : S ⊆ Finset.univ ×ˢ Z := fun i hi ↦
    Finset.mem_product.mpr ⟨Finset.mem_univ _, Finset.mem_image_of_mem _ hi⟩
  let v : {z : ℂ // 0 < z.re ∧ z.re < 1} ↪ ℂ := ⟨Subtype.val, Subtype.val_injective⟩
  have hz := hp q T hT (Z.map v) (by
    intro z h
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨(hS i hi).1, i.2.property.2.le, (hS i hi).2⟩)
  calc
    _ ≤ ∑ i ∈ Finset.univ ×ˢ Z, (ordinaryOrder i : ℝ) := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun i _ _ ↦ Nat.cast_nonneg _)
    _ = ∑ z ∈ Z, ∑ χ : DirichletCharacter ℂ q, (ordinaryOrder (χ, z) : ℝ) := by
      rw [Finset.sum_product, Finset.sum_comm]
    _ = ∑ z ∈ Z.map v, (productOrder q z : ℝ) := by
      rw [Finset.sum_map]
      apply Finset.sum_congr rfl
      intro z _
      change _ = (productOrder q z.val : ℝ)
      rw [productOrder_eq_sum, Nat.cast_sum]
    _ ≤ _ := hz

theorem omitted_count {σ θ C : ℝ} (hcount : MontgomeryCount σ θ C)
    {q : ℕ} [NeZero q] (m : Site q → ℝ) (hm : ∀ i, m i ≤ completedPrimitiveOrder i)
    (hwing : ∀ i, m i ≠ 0 → σ ≤ i.2.val.re ∨ i.2.val.re ≤ 1 - σ)
    (T : ℝ) (hT : 2 ≤ T) (S : Finset (Site q)) (hS : ∀ i ∈ S, |i.2.val.im| ≤ T) :
    ∑ i ∈ S, m i ≤ 2 * (C * ((q : ℝ) * T) ^ θ * Real.log (q * T) ^ 14) := by
  classical
  let R := S.filter (fun i ↦ σ ≤ i.2.val.re)
  let L := S.filter (fun i ↦ i.2.val.re ≤ 1 - σ)
  let e : Site q ↪ Site q := ⟨reflect, reflect_involutive.injective⟩
  have hR := hcount q T hT R (fun i hi ↦ ⟨(Finset.mem_filter.mp hi).2,
    hS i (Finset.mem_filter.mp hi).1⟩)
  have hL := hcount q T hT (L.map e) (by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
    obtain ⟨hiS, hil⟩ := Finset.mem_filter.mp hi
    change σ ≤ (1 - i.2.val).re ∧ |(1 - i.2.val).im| ≤ T
    simpa only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
      zero_sub, abs_neg] using (And.intro (by linarith : σ ≤ 1 - i.2.val.re) (hS i hiS)))
  simp only [Finset.sum_map, e, Function.Embedding.coeFn_mk, ordinaryOrder_reflect] at hL
  calc
    _ ≤ ∑ i ∈ S, ((if σ ≤ i.2.val.re then (ordinaryOrder i : ℝ) else 0) +
        (if i.2.val.re ≤ 1 - σ then (ordinaryOrder i : ℝ) else 0)) := by
      apply Finset.sum_le_sum
      intro i _
      have hmi := (ordinaryOrder_eq_completedPrimitiveOrder i).symm ▸ hm i
      by_cases hr : σ ≤ i.2.val.re <;> by_cases hl : i.2.val.re ≤ 1 - σ
      · simp [hr, hl]; linarith [Nat.cast_nonneg (ordinaryOrder i) (α := ℝ)]
      · simpa [hr, hl] using hmi
      · simpa [hr, hl] using hmi
      · have hzero : m i = 0 := by by_contra hn; exact (hwing i hn).elim hr hl
        simp [hzero, hr, hl]
    _ = (∑ i ∈ R, (ordinaryOrder i : ℝ)) + ∑ i ∈ L, (ordinaryOrder i : ℝ) := by
      simp [R, L, Finset.sum_filter, Finset.sum_add_distrib]
    _ ≤ _ := by linarith

private theorem summable_shifted_pow_geometric {d : ℝ} (hd : 0 < d) (h1 : d < 1) (k : ℕ) :
    Summable (fun n : ℕ ↦ ((n : ℝ) + 2) ^ k * d ^ n) := by
  have hs := summable_pow_mul_geometric_of_norm_lt_one k
    (show ‖d‖ < 1 by rwa [Real.norm_eq_abs, abs_of_pos hd])
  have ht := hs.comp_injective (show Function.Injective (fun n : ℕ ↦ n + 2) from
    fun _ _ h ↦ Nat.add_right_cancel h)
  refine (ht.mul_right (d ^ 2)⁻¹).congr fun n ↦ ?_
  simp [pow_add, hd.ne', mul_assoc]

/-- Explicit constant independent of the index type, its weights, and the level. -/
def heightConstant (θ : ℝ) (k : ℕ) : ℝ :=
  2 ^ θ * Real.log 2 ^ k * ∑' n : ℕ, ((n : ℝ) + 2) ^ k * ((2 : ℝ) ^ (θ - 1)) ^ n

theorem heightConstant_nonneg (θ : ℝ) (k : ℕ) : 0 ≤ heightConstant θ k := by
  unfold heightConstant
  positivity

/-- A finite-subset density estimate gives a uniform weighted bound with one power of decay. -/
theorem uniform_height_mass {ι : Type*} (h m : ι → ℝ) (hm : ∀ i, 0 ≤ m i)
    {θ U : ℝ} (hθ : θ < 1) (hU : 0 ≤ U) (k : ℕ)
    (hcount : ∀ T : ℝ, 2 ≤ T → ∀ S : Finset ι, (∀ i ∈ S, |h i| ≤ T) →
      ∑ i ∈ S, m i ≤ U * T ^ θ * Real.log (2 * T) ^ k) :
    Summable (fun i ↦ m i / (1 + |h i|)) ∧
    ∑' i, m i / (1 + |h i|) ≤ U * heightConstant θ k := by
  classical
  choose b hb using fun i : ι ↦ exists_nat_pow_near
    (show 1 ≤ 1 + |h i| from le_add_of_nonneg_right (abs_nonneg _)) (show (1 : ℝ) < 2 by norm_num)
  let d : ℝ := 2 ^ (θ - 1)
  let u (n : ℕ) := ((n : ℝ) + 2) ^ k * d ^ n
  let A : ℝ := U * (2 : ℝ) ^ θ * Real.log 2 ^ k
  have hd : 0 < d := Real.rpow_pos_of_pos (by norm_num) _
  have h1 : d < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hθ)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hu : Summable u := summable_shifted_pow_geometric hd h1 k
  have hpow (n : ℕ) : ((2 : ℝ) ^ n) ^ θ = ((2 : ℝ) ^ θ) ^ n := by
    rw [← Real.rpow_natCast (2 : ℝ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_natCast ((2 : ℝ) ^ θ) n, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm]
  have hlog (n : ℕ) : Real.log (2 * (2 : ℝ) ^ (n + 1)) = ((n : ℝ) + 2) * Real.log 2 := by
    rw [show 2 * (2 : ℝ) ^ (n + 1) = 2 ^ (n + 2) by ring, Real.log_pow]
    norm_num
  have hf (S : Finset ι) (n : ℕ) :
      ∑ i ∈ S with b i = n, m i / (1 + |h i|) ≤ A * u n := by
    let V := S.filter (fun i ↦ b i = n)
    have hn (i : ι) (hi : i ∈ V) : b i = n := (Finset.mem_filter.mp hi).2
    have hlo (i : ι) (hi : i ∈ V) : (2 : ℝ) ^ n ≤ 1 + |h i| := hn i hi ▸ (hb i).1
    have hhi (i : ι) (hi : i ∈ V) : |h i| ≤ (2 : ℝ) ^ (n + 1) := by
      have ht := (hb i).2
      rw [hn i hi] at ht
      linarith
    have h2 : 2 ≤ (2 : ℝ) ^ (n + 1) := by
      rw [pow_succ]
      nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)]
    calc
      _ ≤ ∑ i ∈ V, m i / (2 : ℝ) ^ n := Finset.sum_le_sum fun i hi ↦
        div_le_div_of_nonneg_left (hm i) (by positivity) (hlo i hi)
      _ = (∑ i ∈ V, m i) / (2 : ℝ) ^ n := by rw [Finset.sum_div]
      _ ≤ _ := (div_le_div_of_nonneg_right (hcount _ h2 V hhi) (by positivity)).trans_eq (by
        rw [hlog, hpow, pow_succ, mul_pow]
        dsimp [u, A, d]
        rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one, div_pow]
        ring)
  have hfinite (S : Finset ι) : ∑ i ∈ S, m i / (1 + |h i|) ≤ U * heightConstant θ k := by
    calc
      _ = ∑ n ∈ S.image b, ∑ i ∈ S with b i = n, m i / (1 + |h i|) :=
        (Finset.sum_fiberwise_of_maps_to (fun i hi ↦ Finset.mem_image_of_mem b hi) _).symm
      _ ≤ ∑ n ∈ S.image b, A * u n := Finset.sum_le_sum fun n _ ↦ hf S n
      _ ≤ ∑' n, A * u n := (hu.mul_left A).sum_le_tsum _ (fun n _ ↦ by dsimp [u]; positivity)
      _ = _ := by rw [tsum_mul_left]; dsimp [A, u, d, heightConstant]; ring
  have hs := summable_of_sum_le (fun i ↦ div_nonneg (hm i) (by positivity)) hfinite
  exact ⟨hs, hs.tsum_le_of_sum_le hfinite⟩

private theorem bounded_strip {H : ℝ → ℂ} (hH : Continuous H) (hc : HasCompactSupport H) (B : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, |z.re| ≤ B → ‖bilateralLaplace H z‖ ≤ K := by
  let u (x : ℝ) := ‖H x‖ * Real.exp (B * |x|)
  have hu : Integrable u := (hH.norm.mul (by fun_prop)).integrable_of_hasCompactSupport hc.norm.mul_right
  refine ⟨∫ x, u x, integral_nonneg (fun x ↦ mul_nonneg (norm_nonneg _) (Real.exp_pos _).le),
    fun z hz ↦ (norm_integral_le_integral_norm _).trans ?_⟩
  have hi : Integrable (fun x : ℝ ↦ H x * Complex.exp (z * x)) :=
    (hH.mul (by fun_prop)).integrable_of_hasCompactSupport hc.mul_right
  apply integral_mono hi.norm hu
  intro x
  change ‖H x * Complex.exp (z * x)‖ ≤ ‖H x‖ * Real.exp (B * |x|)
  rw [norm_mul, Complex.norm_exp]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [show (z * x).re = z.re * x by simp]
  exact (le_abs_self _).trans ((abs_mul _ _).le.trans (mul_le_mul_of_nonneg_right hz (abs_nonneg x)))

private theorem laplace_deriv {H : ℝ → ℂ} (hH : ContDiff ℝ 1 H) (hc : HasCompactSupport H) (z : ℂ) :
    bilateralLaplace (deriv H) z = -z * bilateralLaplace H z := by
  have hD := hH.continuous_deriv (by simp)
  let E := fun x : ℝ ↦ Complex.exp (z * x)
  have hE : Continuous E := by dsimp [E]; fun_prop
  have hE' (x : ℝ) : HasDerivAt E (z * E x) x := by
    change HasDerivAt (fun t : ℝ ↦ Complex.exp (z * t)) (z * Complex.exp (z * x)) x
    convert (((hasDerivAt_id' (x : ℂ)).const_mul z).cexp).comp_ofReal using 1
    ring
  have hp := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := E) (u' := fun x ↦ z * E x) (v := H) (v' := deriv H)
    (fun x _ ↦ hE' x) (fun x _ ↦ (hH.differentiable (by simp) x).hasDerivAt)
    ((hE.mul hD).integrable_of_hasCompactSupport hc.deriv.mul_left)
    (((continuous_const.mul hE).mul hH.continuous).integrable_of_hasCompactSupport hc.mul_left)
    ((hE.mul hH.continuous).integrable_of_hasCompactSupport hc.mul_left)
  change (∫ x : ℝ, deriv H x * E x) = -z * ∫ x : ℝ, H x * E x
  calc ∫ x : ℝ, deriv H x * E x
      = ∫ x : ℝ, E x * deriv H x := by congr 1; funext x; ring
    _ = -∫ x : ℝ, z * E x * H x := hp
    _ = _ := by rw [neg_mul, ← integral_const_mul]; congr 2; funext x; ring

/-- A single integration by parts gives fixed-profile decay on an arbitrary bounded real strip. -/
theorem fixed_profile_decay {H : ℝ → ℂ} (hH : ContDiff ℝ 1 H) (hc : HasCompactSupport H) (B : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, |z.re| ≤ B →
    ‖bilateralLaplace H z‖ ≤ K / (1 + |z.im|) := by
  have hD := hH.continuous_deriv (by simp)
  obtain ⟨C, hC, h0⟩ := bounded_strip hH.continuous hc B
  obtain ⟨D, hD0, h1⟩ := bounded_strip hD hc.deriv B
  refine ⟨C + D, add_nonneg hC hD0, fun z hz ↦ ?_⟩
  have hder := h1 z hz
  rw [laplace_deriv hH hc, norm_mul, norm_neg] at hder
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith [h0 z hz, mul_nonneg (sub_nonneg.mpr (Complex.abs_im_le_norm z))
    (norm_nonneg (bilateralLaplace H z))]

/-- Arbitrary polynomial decay of a fixed smooth compact profile, uniform
on bounded real strips. Each derivative supplies one height weight. -/
theorem fixed_profile_rapid_decay (n : ℕ) {H : ℝ → ℂ} (hd : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (B : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, |z.re| ≤ B →
      ‖bilateralLaplace H z‖ ≤ K / (1+|z.im|)^n := by
  induction n generalizing H with
  | zero => simpa only [pow_zero, div_one] using bounded_strip hd.continuous hc B
  | succ n ih =>
    obtain ⟨C,hC,h₀⟩ := ih hd hc
    obtain ⟨D,hD,h₁⟩ := ih (contDiff_infty_iff_deriv.mp hd).2 hc.deriv
    refine ⟨C+D,add_nonneg hC hD,fun z hz ↦ ?_⟩
    have ht : 0 < 1+|z.im| := by positivity
    have h := (le_div_iff₀ (pow_pos ht n)).mp (h₀ z hz)
    have h' := (le_div_iff₀ (pow_pos ht n)).mp (h₁ z hz)
    rw [laplace_deriv (hd.of_le (by simp)) hc,norm_mul,norm_neg] at h'
    have hle := mul_le_mul_of_nonneg_right (Complex.abs_im_le_norm z)
      (mul_nonneg (norm_nonneg (bilateralLaplace H z)) (pow_nonneg ht.le n))
    apply (le_div_iff₀ (pow_pos ht _)).mpr
    rw [pow_succ]
    linarith only [h,h',hle]

/-- Two integrations by parts give a summable height weight uniformly on a
bounded real strip, with a constant depending only on the radial profile. -/
theorem fixed_profile_quadratic_decay {H : ℝ → ℂ} (hd : ContDiff ℝ (∞) H)
    (hc : HasCompactSupport H) (B : ℝ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℂ, |z.re| ≤ B →
      ‖bilateralLaplace H z‖ ≤ K / (1+|z.im|)^2 := fixed_profile_rapid_decay 2 hd hc B

private theorem separate_log {q T : ℝ} (hq : 1 ≤ q) (hT : 2 ≤ T) :
    Real.log (q * T) ≤ (1 + Real.log q) * Real.log (2 * T) := by
  have hT0 : 0 < T := by linarith
  have hfour : (4 : ℝ) ≤ 2 * T := by linarith
  have hlog4 : 1 ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    linarith
  have hlog : 1 ≤ Real.log (2 * T) := hlog4.trans (Real.log_le_log (by norm_num) hfour)
  have hmono : Real.log T ≤ Real.log (2 * T) := Real.log_le_log hT0 (by linarith)
  rw [Real.log_mul (by linarith : q ≠ 0) hT0.ne']
  nlinarith [mul_nonneg (Real.log_nonneg hq) (sub_nonneg.mpr hlog)]

def montgomeryExponent (σ : ℝ) : ℝ := (1 - σ) * min (3 / (2 - σ)) (2 / σ)

theorem montgomeryExponent_lt_one {σ : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) :
    montgomeryExponent σ < 1 := by
  have H : 0 < 2 - σ := by linarith
  calc montgomeryExponent σ ≤ (1 - σ) * (3 / (2 - σ)) :=
        mul_le_mul_of_nonneg_left (min_le_left ..) (by linarith)
    _ < 1 := by rw [← mul_div_assoc]; apply (div_lt_iff₀ H).mpr; linarith

/-- A single constant controls every modulus, every allowed deficit, and every real Mellin
shift `a` in the prescribed compact interval. The only density assumption is Jutila (1.1). -/
theorem normalized_omitted_mass_log {σ θ C : ℝ} (hθ : θ < 1) (hC : 0 ≤ C)
    (hcount : MontgomeryCount σ θ C) {H : ℝ → ℂ} (hH : ContDiff ℝ 1 H)
    (hc : HasCompactSupport H) (A : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (a : ℝ), |a| ≤ A →
      ∀ m : Site q → ℝ, (∀ i, 0 ≤ m i) → (∀ i, m i ≤ completedPrimitiveOrder i) →
      (∀ i, m i ≠ 0 → σ ≤ i.2.val.re ∨ i.2.val.re ≤ 1 - σ) →
      Summable (fun i ↦ m i * ‖bilateralLaplace H (i.2.val - a)‖) ∧
      (∑' i, m i * ‖bilateralLaplace H (i.2.val - a)‖) / (q.totient : ℝ) ≤
        D * (q : ℝ) ^ θ * (1 + Real.log q) ^ 14 / q.totient := by
  obtain ⟨K, hK, hdec⟩ := fixed_profile_decay hH hc (1 + A)
  have hV := heightConstant_nonneg θ 14
  refine ⟨2 * C * heightConstant θ 14 * K, by positivity, ?_⟩
  intro q _ a ha m hm hmx hwing
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  let U := 2 * C * (q : ℝ) ^ θ * (1 + Real.log q) ^ 14
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hsep (T : ℝ) (hT : 2 ≤ T) :
      2 * (C * ((q : ℝ) * T) ^ θ * Real.log (q * T) ^ 14) ≤ U * T ^ θ * Real.log (2 * T) ^ 14 := by
    have hqt : 1 ≤ (q : ℝ) * T := by nlinarith [mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hT)]
    have hlog := pow_le_pow_left₀ (Real.log_nonneg hqt) (separate_log hq hT) 14
    rw [mul_pow] at hlog
    rw [Real.mul_rpow (by positivity) (by linarith)]
    calc
      _ ≤ 2 * (C * ((q : ℝ) ^ θ * T ^ θ) * ((1 + Real.log q) ^ 14 * Real.log (2 * T) ^ 14)) := by
        gcongr
      _ = _ := by dsimp [U]; ring
  obtain ⟨hs, hb⟩ := uniform_height_mass (fun i : Site q ↦ i.2.val.im) m hm hθ hU 14
    (fun T hT S hS ↦ (omitted_count hcount m hmx hwing T hT S hS).trans (hsep T hT))
  have hmaj (i : Site q) :
      m i * ‖bilateralLaplace H (i.2.val - a)‖ ≤ m i / (1 + |i.2.val.im|) * K := by
    have hre : |(i.2.val - (a : ℂ)).re| ≤ 1 + A := by
      rw [Complex.sub_re, Complex.ofReal_re]
      calc |i.2.val.re - a| ≤ |i.2.val.re| + |a| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_pos i.2.property.1]; linarith [i.2.property.2]
    have h := hdec (i.2.val - a) hre
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    calc _ ≤ m i * (K / (1 + |i.2.val.im|)) := mul_le_mul_of_nonneg_left h (hm i)
      _ = _ := by ring
  have hs' : Summable (fun i ↦ m i * ‖bilateralLaplace H (i.2.val - a)‖) :=
    Summable.of_nonneg_of_le (fun i ↦ mul_nonneg (hm i) (norm_nonneg _)) hmaj (hs.mul_right K)
  refine ⟨hs', div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)⟩
  calc
    _ ≤ ∑' i, m i / (1 + |i.2.val.im|) * K := hs'.tsum_le_tsum hmaj (hs.mul_right K)
    _ ≤ U * heightConstant θ 14 * K := by rw [tsum_mul_right]; gcongr
    _ = _ := by dsimp [U]; ring

/-- The elementary `q/φ(q) ≪ε q^ε` bound. Large primes absorb their Euler factor in
`p^ε`; there are only finitely many small primes. -/
theorem totient_ratio_le_rpow {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], (q : ℝ) / q.totient ≤ C * (q : ℝ) ^ e := by
  classical
  have ht := (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨M, hM⟩ := eventually_atTop.1 (ht.eventually_ge_atTop (2 : ℝ))
  refine ⟨(2 : ℝ) ^ M, by positivity, ?_⟩
  intro q _
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hφ : 0 < (q.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hq
  let u (p : ℕ) : ℝ := if p < M then 2 else 1
  have hpm {p : ℕ} (hp : p ∈ q.primeFactors) : 0 < p - 1 := by
    have := (Nat.prime_of_mem_primeFactors hp).two_le
    omega
  have hprod : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ) :=
    Finset.prod_pos fun p hp ↦ by exact_mod_cast hpm hp
  have heuler : (q : ℝ) / q.totient = ∏ p ∈ q.primeFactors, ((p : ℝ) / (p - 1 : ℕ)) := by
    rw [Finset.prod_div_distrib]
    apply (div_eq_div_iff hφ.ne' hprod.ne').mpr
    have hn := congrArg (fun n : ℕ ↦ (n : ℝ)) (Nat.totient_mul_prod_primeFactors q)
    have hr : (q.totient : ℝ) * (∏ p ∈ q.primeFactors, (p : ℝ)) =
        (q : ℝ) * ∏ p ∈ q.primeFactors, ((p - 1 : ℕ) : ℝ) := by
      simpa only [Nat.cast_mul, Nat.cast_prod] using hn
    linarith
  have hfac (p : ℕ) (hp : p ∈ q.primeFactors) :
      (p : ℝ) / (p - 1 : ℕ) ≤ u p * (p : ℝ) ^ e := by
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hp1 : 1 ≤ p := by have := (Nat.prime_of_mem_primeFactors hp).two_le; omega
    have hr : (p : ℝ) / (p - 1 : ℕ) ≤ 2 := by
      rw [Nat.cast_sub hp1, Nat.cast_one]
      apply (div_le_iff₀ (by linarith)).mpr
      linarith
    by_cases hsmall : p < M
    · have h1 := Real.one_le_rpow (by linarith : 1 ≤ (p : ℝ)) he.le
      simp [u, hsmall]
      linarith
    · simpa [u, hsmall] using hr.trans (hM p (le_of_not_gt hsmall))
  have hcard : (q.primeFactors.filter (· < M)).card ≤ M := by
    have hsub : q.primeFactors.filter (· < M) ⊆ Finset.range M :=
      fun p hp ↦ Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    simpa using Finset.card_le_card hsub
  have hu : ∏ p ∈ q.primeFactors, u p ≤ (2 : ℝ) ^ M := by
    change (∏ p ∈ q.primeFactors, if p < M then (2 : ℝ) else 1) ≤ _
    rw [← Finset.prod_filter]
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hcard
  have hrad : ∏ p ∈ q.primeFactors, (p : ℝ) ≤ (q : ℝ) := by
    have hle := (Nat.cast_le (α := ℝ)).mpr (Nat.le_of_dvd hq (Nat.prod_primeFactors_dvd q))
    simpa only [Nat.cast_prod] using hle
  rw [heuler]
  calc
    _ ≤ ∏ p ∈ q.primeFactors, (u p * (p : ℝ) ^ e) :=
        Finset.prod_le_prod₀ (fun p _ ↦ by positivity) hfac
    _ = (∏ p ∈ q.primeFactors, u p) * (∏ p ∈ q.primeFactors, (p : ℝ)) ^ e := by
      rw [Finset.prod_mul_distrib, Real.finsetProd_rpow _ _ (fun _ _ ↦ by positivity)]
    _ ≤ _ := mul_le_mul hu (Real.rpow_le_rpow (by positivity) hrad he.le) (by positivity) (by positivity)

private theorem log_pow_le_rpow {e : ℝ} (he : 0 < e) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → (1 + Real.log x) ^ 14 ≤ C * x ^ e := by
  let d := e / 14
  have hd : 0 < d := by dsimp [d]; positivity
  refine ⟨(1 + d⁻¹) ^ 14, by positivity, fun x hx ↦ ?_⟩
  have hx0 : 0 < x := by linarith
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 d)
  rw [Real.log_rpow hx0] at h
  have h1 := Real.one_le_rpow hx hd.le
  have hlog : Real.log x ≤ d⁻¹ * x ^ d := by
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hd).mpr
    linarith
  have hlin : 1 + Real.log x ≤ (1 + d⁻¹) * x ^ d := by nlinarith
  calc
    _ ≤ ((1 + d⁻¹) * x ^ d) ^ 14 := pow_le_pow_left₀ (by linarith [Real.log_nonneg hx]) hlin _
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast (x ^ d) 14, ← Real.rpow_mul hx0.le]
      congr 2
      dsimp [d]
      ring

/-- The normalized absolute omitted-order bound for the genuine completed primitive lifts.
All positive levels are covered. The exponent loss and test are fixed before the level,
Mellin shift, and omitted multiplicities are varied. -/
theorem normalized_omitted_mass {σ C : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1) (hC : 0 ≤ C)
    (hcount : MontgomeryCount σ (montgomeryExponent σ) C)
    {H : ℝ → ℂ} (hH : ContDiff ℝ 1 H) (hc : HasCompactSupport H)
    (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (q : ℕ) [NeZero q] (a : ℝ), |a| ≤ A →
      ∀ m : Site q → ℝ, (∀ i, 0 ≤ m i) → (∀ i, m i ≤ completedPrimitiveOrder i) →
      (∀ i, m i ≠ 0 → σ ≤ i.2.val.re ∨ i.2.val.re ≤ 1 - σ) →
      Summable (fun i ↦ m i * ‖bilateralLaplace H (i.2.val - a)‖) ∧
      (∑' i, m i * ‖bilateralLaplace H (i.2.val - a)‖) / (q.totient : ℝ) ≤
        D * (q : ℝ) ^ (-(1 - montgomeryExponent σ) + ε) := by
  let θ := montgomeryExponent σ
  obtain ⟨D, hD, hmass⟩ := normalized_omitted_mass_log (montgomeryExponent_lt_one hσ hσ1)
    hC hcount hH hc A
  have hh : 0 < ε / 2 := by positivity
  obtain ⟨C₁, hC₁, hφ⟩ := totient_ratio_le_rpow hh
  obtain ⟨C₂, hC₂, hlog⟩ := log_pow_le_rpow hh
  refine ⟨D * C₁ * C₂, by positivity, ?_⟩
  intro q _ a ha m hm hmx hwing
  obtain ⟨hs, hb⟩ := hmass q a ha m hm hmx hwing
  have hq : 1 ≤ (q : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hq0 : 0 < (q : ℝ) := by linarith
  refine ⟨hs, hb.trans ?_⟩
  calc
    _ = D * ((q : ℝ) / q.totient) * (1 + Real.log q) ^ 14 * (q : ℝ) ^ (θ - 1) := by
      rw [Real.rpow_sub hq0, Real.rpow_one]
      dsimp [θ]
      field_simp
    _ ≤ D * (C₁ * (q : ℝ) ^ (ε / 2)) * (C₂ * (q : ℝ) ^ (ε / 2)) * (q : ℝ) ^ (θ - 1) := by
      have hqφ := hφ q
      have hqlog := hlog q hq
      gcongr
    _ = D * C₁ * C₂ * (q : ℝ) ^ (-(1 - montgomeryExponent σ) + ε) := by
      rw [show -(1 - montgomeryExponent σ) + ε = ε / 2 + ε / 2 + (θ - 1) by dsimp [θ]; ring,
        Real.rpow_add hq0, Real.rpow_add hq0]
      ring

end RiemannMasullo.ConductorDensity
