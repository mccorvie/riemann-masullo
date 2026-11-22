module

public import RiemannMasullo.ForMathlib.Analysis.Distribution.SchwartzSpace.ChangeVariables
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-! # Translation differences of real-line Schwartz functions -/

@[expose] public noncomputable section

open Function Set
open scoped ContDiff SchwartzMap

namespace RiemannMasullo

private def forwardTail (f : ℝ → ℂ) (x : ℝ) := ∑' n : ℕ, f (x + n)

private theorem tailWeight_summable : Summable (fun n : ℕ ↦ (((n : ℝ) + 1) ^ 2)⁻¹) := by
  simpa only [Function.comp_def, Nat.cast_succ] using
    (Real.summable_nat_pow_inv.mpr (by decide : 1 < 2)).comp_injective Nat.succ_injective

/-- On the positive half-line, two extra powers control the sum over translates. -/
private theorem forwardTail_bound (f : 𝓢(ℝ, ℂ)) (k j : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ∀ n : ℕ,
      ‖x‖ ^ k * ‖iteratedDeriv j f (x + n)‖ ≤ (((n : ℝ) + 1) ^ 2)⁻¹ * C := by
  refine ⟨2 ^ (k + 2) * (Finset.Iic (k + 2, j)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f, fun x hx n ↦ ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k + 2, j))
    (k := k + 2) (n := j) le_rfl le_rfl f (x + n)
  simp only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ x + (n : ℝ)), pow_add] at h
  rw [← div_eq_inv_mul, le_div_iff₀ (by positivity), Real.norm_eq_abs, abs_of_nonneg hx, mul_right_comm]
  rw [pow_add (2 : ℝ) k 2]
  refine le_trans ?_ h
  gcongr (?_ ^ k * ?_ ^ 2) * _ <;> linarith [Nat.cast_nonneg (α := ℝ) n]

private theorem forwardTail_local_bound (f : 𝓢(ℝ, ℂ)) (b : ℝ) (j : ℕ) :
    ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ x ∈ Ioi b, ‖iteratedDeriv j f (x + n)‖ ≤ u n := by
  let g := f.compSubConstCLM ℂ (-b)
  obtain ⟨C, hC⟩ := forwardTail_bound g 0 j
  refine ⟨_, tailWeight_summable.mul_right C, fun n x hx ↦ ?_⟩
  have hh := hC (x - b) (sub_nonneg.mpr hx.le) n
  change ‖x - b‖ ^ 0 * ‖iteratedDeriv j (fun y ↦ f (y - -b)) (x - b + n)‖ ≤ _ at hh
  simpa only [pow_zero, one_mul, sub_neg_eq_add, iteratedDeriv_comp_add_const,
    show x - b + n + b = x + n by ring] using hh

private theorem forwardTail_smooth (f : 𝓢(ℝ, ℂ)) :
    ContDiff ℝ ∞ (forwardTail f) ∧ ∀ j, iteratedDeriv j (forwardTail f) = forwardTail (iteratedDeriv j f) := by
  have hd (j : ℕ) (x : ℝ) : HasDerivAt (forwardTail (iteratedDeriv j f))
      (forwardTail (iteratedDeriv (j + 1) f) x) x := by
    obtain ⟨u, hu, hle⟩ := forwardTail_local_bound f (x - 1) (j + 1)
    obtain ⟨v, hv, hle'⟩ := forwardTail_local_bound f (x - 1) j
    have hx : x ∈ Ioi (x - 1) := by exact sub_one_lt _
    apply hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioi isPreconnected_Ioi
      (g := fun (n : ℕ) y ↦ iteratedDeriv j f (y + n))
      (g' := fun (n : ℕ) y ↦ iteratedDeriv (j + 1) f (y + (n : ℝ))) (y₀ := x)
    · intro n y _
      rw [iteratedDeriv_succ]
      apply HasDerivAt.comp_add_const
      exact ((contDiff_iff_iteratedDeriv.mp (f.smooth (⊤ : ℕ∞))).2 j (by simp) (y + n)).hasDerivAt
    · exact hle
    · exact hx
    · exact .of_norm_bounded hv (fun n ↦ hle' n x hx)
    · exact hx
  have he (j : ℕ) : iteratedDeriv j (forwardTail f) = forwardTail (iteratedDeriv j f) := by
    induction j with
    | zero => simp
    | succ j ih => exact (iteratedDeriv_succ ..).trans (ih ▸ funext fun x ↦ (hd j x).deriv)
  exact ⟨contDiff_of_differentiable_iteratedDeriv (fun j _ ↦ he j ▸ fun x ↦ (hd j x).differentiableAt), he⟩

private theorem forwardTail_decay (f : 𝓢(ℝ, ℂ)) (k j : ℕ) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖x‖ ^ k * ‖iteratedDeriv j (forwardTail f) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := forwardTail_bound f k j
  refine ⟨∑' n : ℕ, (((n : ℝ) + 1) ^ 2)⁻¹ * C, fun x hx ↦ ?_⟩
  have hs := tailWeight_summable.mul_right C
  let a (n : ℕ) := iteratedDeriv j f (x + n)
  have hsum : Summable fun n ↦ ‖a n‖ := by
    obtain ⟨v, hv, h⟩ := forwardTail_local_bound f (x - 1) j
    exact hv.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ h n x (sub_one_lt _))
  rw [(forwardTail_smooth f).2 j]
  change ‖x‖ ^ k * ‖∑' n, a n‖ ≤ _
  refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hsum) (by positivity)).trans ?_
  rw [← tsum_mul_left]
  exact (hsum.mul_left _).tsum_le_tsum (hC x hx) hs

/-- Vanishing of the full orbit sum identifies the forward primitive with a
reflected backward primitive. Each supplies rapid decay on its own half-line. -/
private theorem forwardTail_schwartz_of_zero_sum (f : 𝓢(ℝ, ℂ))
    (hf : ∀ x : ℝ, HasSum (fun m : ℤ ↦ f (x + m)) 0) :
    ∃ g : 𝓢(ℝ, ℂ), (g : ℝ → ℂ) = forwardTail f := by
  let e := ContinuousLinearEquiv.neg ℝ (M := ℝ)
  let b := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e (f.compSubConstCLM ℂ 1)
  have hb (x : ℝ) : b x = f (-x - 1) := rfl
  have heq : forwardTail f = fun x ↦ -(forwardTail b (-x)) := by
    funext x
    let a (m : ℤ) := f (x + m)
    have hp : Summable (fun n : ℕ ↦ a n) := (hf x).summable.comp_injective Nat.cast_injective
    have hm : Summable (fun n : ℕ ↦ a (-(n + 1))) := (hf x).summable.comp_injective (fun i j h ↦ by omega)
    have h := (hp.hasSum.of_nat_of_neg_add_one hm.hasSum).unique (hf x)
    apply eq_neg_of_add_eq_zero_left
    convert h using 2
    · simp [forwardTail, a]
    · apply tsum_congr
      intro n
      rw [hb]
      dsimp [a]
      push_cast
      ring_nf
  refine ⟨⟨forwardTail f, (forwardTail_smooth f).1, fun k j ↦ ?_⟩, rfl⟩
  obtain ⟨C, hC⟩ := forwardTail_decay f k j
  obtain ⟨D, hD⟩ := forwardTail_decay b k j
  refine ⟨max C D, fun x ↦ ?_⟩
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  rcases le_total 0 x with hx | hx
  · exact (hC x hx).trans (le_max_left _ _)
  · rw [heq, iteratedDeriv_fun_neg, norm_neg, iteratedDeriv_comp_neg, norm_smul]
    simpa only [norm_pow, norm_neg, norm_one, one_pow, one_mul] using (hD (-x) (neg_nonneg.mpr hx)).trans (le_max_right C D)

/-- The forward tail solves the translation difference equation whenever the
bilateral sum vanishes. Rescaling reduces the estimates to unit spacing. -/
theorem schwartzOrbitPrimitive (L : ℝ) (hL : 0 < L) (f : 𝓢(ℝ, ℂ))
    (hf : ∀ x : ℝ, HasSum (fun n : ℤ ↦ f (x + n * L)) 0) :
    ∃ g : 𝓢(ℝ, ℂ), (∀ x : ℝ, g x = ∑' n : ℕ, f (x + n * L)) ∧
      ∀ x : ℝ, f x = g x - g (x + L) := by
  let e := ContinuousLinearEquiv.unitsEquivAut ℝ (Units.mk0 L hL.ne')
  let d := schwartzChangeVariable ℂ (F := ℂ) e
  have he (x : ℝ) : e x = x * L := rfl
  have hf' (x : ℝ) : HasSum (fun n : ℤ ↦ d f (x + n)) 0 := by
    change HasSum (fun n : ℤ ↦ f ((x + n) * L)) 0
    simpa only [add_mul] using hf (x * L)
  obtain ⟨g, hg⟩ := forwardTail_schwartz_of_zero_sum (d f) hf'
  have hg' (x : ℝ) : d.symm g x = ∑' n : ℕ, f (x + n * L) := by
    change g (e.symm x) = _
    rw [congrFun hg]
    apply tsum_congr
    intro n
    change f (e (e.symm x + n)) = _
    rw [map_add, e.apply_symm_apply, he]
  refine ⟨d.symm g, hg', fun x ↦ ?_⟩
  have hs := (hf x).summable.comp_injective Nat.cast_injective
  change Summable (fun n : ℕ ↦ f (x + (n : ℤ) * L)) at hs
  simp only [Int.cast_natCast] at hs
  rw [hg', hg', hs.tsum_eq_zero_add]
  have heq (n : ℕ) : x + ((n + 1 : ℕ) : ℝ) * L = x + L + n * L := by push_cast; ring
  simp only [heq, Nat.cast_zero, zero_mul, add_zero, add_sub_cancel_right]

/-- Translates through an arithmetic progression, weighted by a geometric
sequence, sum to a Schwartz function. Translation costs only polynomial growth. -/
theorem schwartzGeometricTranslates (f : 𝓢(ℝ, ℂ)) (t r : ℝ) (hr : 0 < r) (hr' : r < 1) :
    ∃ g : 𝓢(ℝ, ℂ), ∀ x : ℝ, g x = ∑' n : ℕ, r ^ n • f (x + n * t) := by
  let s (n : ℕ) : ℝ → ℂ := r ^ n • (fun x ↦ f (x + n * t))
  have htrans (n : ℕ) (j : ℕ∞) : ContDiff ℝ j (fun x : ℝ ↦ f (x + n * t)) :=
    (f.smooth j).comp (contDiff_id.add contDiff_const)
  have hsm (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (s n) := (htrans n ⊤).const_smul (r ^ n)
  have hder (j n : ℕ) (x : ℝ) : ‖iteratedFDeriv ℝ j (s n) x‖ =
      r ^ n * ‖iteratedFDeriv ℝ j f (x + n * t)‖ := by
    dsimp only [s]
    rw [iteratedFDeriv_const_smul_apply (htrans n j).contDiffAt, norm_smul, norm_pow,
      Real.norm_of_nonneg hr.le, iteratedFDeriv_comp_add_right]
  have hmajor (k j : ℕ) : ∃ u : ℕ → ℝ, Summable u ∧
      ∀ n x, ‖x‖ ^ k * ‖iteratedFDeriv ℝ j (s n) x‖ ≤ u n := by
    let C := 2 ^ k * (Finset.Iic (k, j)).sup (fun m ↦ SchwartzMap.seminorm ℂ m.1 m.2) f
    have hs := (summable_pow_mul_geometric_of_norm_lt_one k (show ‖r‖ < 1 by
      rwa [Real.norm_of_nonneg hr.le])).comp_injective Nat.succ_injective
    have hs' : Summable fun n : ℕ ↦ ((n : ℝ) + 1) ^ k * r ^ n := by
      simpa only [Function.comp_def, Nat.cast_succ, pow_succ r, mul_assoc, mul_inv_cancel₀ hr.ne',
        mul_one] using hs.mul_right r⁻¹
    refine ⟨_, hs'.mul_right ((1 + ‖t‖) ^ k * C), fun n x ↦ ?_⟩
    have hx : ‖x‖ ≤ (1 + ‖x + n * t‖) * (((n : ℝ) + 1) * (1 + ‖t‖)) := by
      have htt := norm_sub_le (x + n * t) (n * t)
      rw [add_sub_cancel_right, norm_mul, Real.norm_of_nonneg (Nat.cast_nonneg n)] at htt
      nlinarith only [htt, norm_nonneg (x + n * t), norm_nonneg t, Nat.cast_nonneg (α := ℝ) n,
        mul_nonneg (norm_nonneg (x + n * t)) (Nat.cast_nonneg (α := ℝ) n),
        mul_nonneg (norm_nonneg (x + n * t)) (norm_nonneg t),
        mul_nonneg (mul_nonneg (norm_nonneg (x + n * t)) (Nat.cast_nonneg (α := ℝ) n)) (norm_nonneg t)]
    have hb := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℂ) (m := (k, j))
      (k := k) (n := j) le_rfl le_rfl f (x + n * t)
    rw [hder]
    calc
      _ ≤ ((1 + ‖x + n * t‖) * (((n : ℝ) + 1) * (1 + ‖t‖))) ^ k * (r ^ n * _) := by
        gcongr
      _ = (((n : ℝ) + 1) ^ k * r ^ n * (1 + ‖t‖) ^ k) *
          ((1 + ‖x + n * t‖) ^ k * ‖iteratedFDeriv ℝ j f (x + n * t)‖) := by simp only [mul_pow]; ring
      _ ≤ _ := by
        change _ ≤ ((n : ℝ) + 1) ^ k * r ^ n * ((1 + ‖t‖) ^ k * C)
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb
          (show 0 ≤ ((n : ℝ) + 1) ^ k * r ^ n * (1 + ‖t‖) ^ k by positivity)
  choose u hu hub using hmajor
  have hu₀ (j n : ℕ) (x : ℝ) (_ : (j : ℕ∞) ≤ ⊤) : ‖iteratedFDeriv ℝ j (s n) x‖ ≤ u 0 j n := by
    simpa using hub 0 j n x
  have hsmooth := contDiff_tsum hsm (fun j _ ↦ hu 0 j) hu₀
  refine ⟨⟨_, hsmooth, fun k j ↦ ⟨∑' n, u k j n, fun x ↦ ?_⟩⟩, fun _ ↦ rfl⟩
  rw [iteratedFDeriv_tsum_apply hsm (fun i _ ↦ hu 0 i) hu₀ le_top]
  have hnorm := (hu 0 j).of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ hu₀ j n x le_top)
  refine (mul_le_mul_of_nonneg_left (norm_tsum_le_tsum_norm hnorm) (by positivity)).trans ?_
  rw [← tsum_mul_left]
  exact (hnorm.mul_left _).tsum_le_tsum (fun n ↦ hub k j n x) (hu k j)

end RiemannMasullo
