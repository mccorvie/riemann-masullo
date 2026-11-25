module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic

/-!
# Valuation fold of a rational product-frequency cutoff

The coordinates of a compact Fourier test at the unramified finite places are
valuation slices, constant in each coordinate after some finite upper bound.
The real Fourier profile on the rational theta quotient is their finite outward
difference fold. Keeping the unramified bases and the compact angular phases
as parameters also includes any finite set of reciprocal prime powers.

The independent gate in (12.4.1.8), pp. 516–517, multiplies the raw fold.
After normalization its effect is exactly conjugation by the geometric dilation
sum with conjugated angular phases. A plateau near zero yields another finite
valuation box; the product-frequency bound then gives the same real band. This
is a statement about the folded Fourier profiles, not the weighted trace limit.
-/

@[expose] public noncomputable section

namespace RiemannMasullo.QuotientFrequencyFold

/-- Coordinates count shells starting at the lower cutoff; values below the
lower cutoff are extended by zero. The product presentation orders the places. -/
def Vec (α : Type) : ℕ → Type
  | 0 => Unit
  | d + 1 => α × Vec α d

abbrev Shell := Vec ℕ

variable {E : Type*} [AddCommGroup E]

/-- Backward difference with zero boundary. -/
def back (f : ℕ → E) : ℕ → E
  | 0 => f 0
  | j + 1 => f (j+1) - f j

/-- Iterating `back` expands into the signed sum over the Boolean cube:
choosing the predecessor introduces one minus sign. -/
def coeff : (d : ℕ) → (Shell d → E) → Shell d → E
  | 0, F, k => F k
  | d+1, F, k => coeff d (fun t => back (fun j => F (j,t)) k.1) k.2

/-- Sum on the inclusive rectangle from zero to `h`. -/
def boxSum : (d : ℕ) → Shell d → (Shell d → E) → E
  | 0, _, F => F ()
  | d+1, h, F => ∑ j ∈ Finset.range (h.1+1), boxSum d h.2 (fun t => F (j,t))

/-- Product of upper-cone indicators, acting on a coefficient. -/
def cone : (d : ℕ) → Shell d → Shell d → E → E
  | 0, _, _, a => a
  | d+1, k, n, a => if k.1 ≤ n.1 then cone d k.2 n.2 a else 0

/-- Clamping leaves a family unchanged precisely when it is constant past
its upper cutoff in each coordinate. -/
def clamp : (d : ℕ) → Shell d → Shell d → Shell d
  | 0, _, _ => ()
  | d+1, h, n => (min h.1 n.1, clamp d h.2 n.2)

private theorem boxSum_zero (d : ℕ) (h : Shell d) :
    boxSum d h (fun _ => (0 : E)) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [boxSum, ih]

private theorem restricted (f : ℕ → E) (h n : ℕ) :
    (∑ j ∈ Finset.range (h+1), if j ≤ n then back f j else 0) = f (min h n) := by
  induction h with
  | zero => simp [back]
  | succ h ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases hj : h+1 ≤ n
    · simp [hj, min_eq_left (Nat.le_trans (Nat.le_succ h) hj), back]
    · have hn : n ≤ h := by omega
      simp [hj, min_eq_right hn, min_eq_right (Nat.le_trans hn (Nat.le_succ h))]

/-- Finite rectangular Möbius inversion, including upper-cone indicators. -/
theorem inversion (d : ℕ) (F : Shell d → E) (h n : Shell d) :
    boxSum d h (fun k => cone d k n (coeff d F k)) = F (clamp d h n) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (∑ j ∈ Finset.range (h.1+1), boxSum d h.2 (fun t =>
      if j ≤ n.1 then cone d t n.2 (coeff d (fun s => back (fun i => F (i,s)) j) t)
      else 0)) = F (min h.1 n.1, clamp d h.2 n.2)
    rw [← restricted (fun j => F (j, clamp d h.2 n.2)) h.1 n.1]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j ≤ n.1
    · simp only [ite_eq_left hj]; exact ih _ _ _
    · simp only [ite_eq_right hj]; exact boxSum_zero _ _

theorem finite_expansion (d : ℕ) (F : Shell d → E) (h : Shell d)
    (stable : ∀ n, F (clamp d h n) = F n) (n : Shell d) :
    F n = boxSum d h (fun k => cone d k n (coeff d F k)) :=
  ((inversion d F h n).trans (stable n)).symm

/-- Product radius in shifted shell coordinates; the factor from the lower
cutoffs is absorbed into the initial bound. -/
def weight : (d : ℕ) → Vec ℝ d → Shell d → ℝ
  | 0, _, _ => 1
  | d+1, p, k => p.1 ^ k.1 * weight d p.2 k.2

def basesGEOne : (d : ℕ) → Vec ℝ d → Prop
  | 0, _ => True
  | d+1, p => 1 ≤ p.1 ∧ basesGEOne d p.2

private theorem weight_nonneg (d : ℕ) (p : Vec ℝ d) (hp : basesGEOne d p) (k : Shell d) :
    0 ≤ weight d p k := by
  induction d with
  | zero => exact zero_le_one
  | succ d ih => exact mul_nonneg (pow_nonneg (zero_le_one.trans hp.1) _) (ih _ hp.2 _)

/-- Every backward-difference coefficient has the same product support
bound as the shell at its upper corner. Apply at each fixed real argument. -/
theorem coeff_support (d : ℕ) (p : Vec ℝ d) (hp : basesGEOne d p)
    (B u : ℝ) (hB : 0 ≤ B) (F : Shell d → E)
    (hF : ∀ k, B * weight d p k < |u| → F k = 0) (k : Shell d)
    (hout : B * weight d p k < |u|) : coeff d F k = 0 := by
  induction d generalizing B with
  | zero => exact hF k hout
  | succ d ih =>
    rcases k with ⟨j,t⟩
    refine ih p.2 hp.2 (B * p.1 ^ j) (mul_nonneg hB (pow_nonneg (zero_le_one.trans hp.1) _))
      (fun s => back (fun i => F (i,s)) j) ?_ t ?_
    · intro s hs
      have top : F (j,s) = 0 := hF _ (by simpa [weight, mul_assoc] using hs)
      cases j with
      | zero => exact top
      | succ i =>
        have hpow : p.1 ^ i ≤ p.1 ^ (i+1) := by
          rw [pow_succ]; exact le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans hp.1) _) hp.1
        have below : F (i,s) = 0 := hF _ (by
          simp only [weight, ← mul_assoc]
          exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hB)
            (weight_nonneg _ _ hp.2 _)) hs)
        simp [back, top, below]
    · simpa [weight, mul_assoc] using hout

/-- The initial reciprocal shell radius and angular/Gauss scalar are absorbed
in the slice `H`. Thus `weight a k * v` is exactly `v / c_k`. -/
def phase : (d : ℕ) → Vec ℂ d → Shell d → ℂ
  | 0, _, _ => 1
  | d+1, γ, k => (star γ.1) ^ k.1 * phase d γ.2 k.2

def shift : (d : ℕ) → Shell d → Shell d → Shell d
  | 0, _, _ => ()
  | d+1, k, j => (k.1 + j.1, shift d k.2 j.2)

private theorem shift_inj (d : ℕ) (k : Shell d) : Function.Injective (shift d k) := by
  induction d with
  | zero => intro x y _; cases x; cases y; rfl
  | succ d ih =>
    rintro ⟨i,x⟩ ⟨j,y⟩ h
    exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst h)) (ih _ (congrArg Prod.snd h))

private theorem weight_shift (d : ℕ) (a : Vec ℝ d) (k j : Shell d) :
    weight d a (shift d k j) = weight d a k * weight d a j := by
  induction d with
  | zero => simp [weight]
  | succ d ih => simp only [weight, shift, pow_add, ih]; ring

private theorem phase_shift (d : ℕ) (γ : Vec ℂ d) (k j : Shell d) :
    phase d γ (shift d k j) = phase d γ k * phase d γ j := by
  induction d with
  | zero => simp [phase]
  | succ d ih => simp only [phase, shift, pow_add, ih]; ring

private theorem cone_shift (d : ℕ) (k j : Shell d) (c : ℂ) :
    cone d k (shift d k j) c = c := by
  induction d with
  | zero => rfl
  | succ d ih => simp [cone, shift, ih]

private theorem cone_off (d : ℕ) (k n : Shell d) (c : ℂ)
    (hn : n ∉ Set.range (shift d k)) : cone d k n c = 0 := by
  induction d with
  | zero => cases n; exact (hn ⟨(), rfl⟩).elim
  | succ d ih =>
    rcases n with ⟨m,n⟩
    by_cases hm : k.1 ≤ m
    · simp only [cone, hm, ite_true]
      apply ih
      rintro ⟨j, rfl⟩
      exact hn ⟨(m-k.1,j), Prod.ext (by dsimp [shift]; omega) rfl⟩
    · simp [cone, hm]

private theorem box_mul (d : ℕ) (b : Shell d) (f : Shell d → ℂ) (c : ℂ) :
    c * boxSum d b f = boxSum d b (fun k => c * f k) := by
  induction d with
  | zero => rfl
  | succ d ih => simp [boxSum, Finset.mul_sum, ih]

private theorem box_hasSum {ι : Type*} (d : ℕ) (b : Shell d)
    (f : Shell d → ι → ℂ) (s : Shell d → ℂ) (hf : ∀ k, HasSum (f k) (s k)) :
    HasSum (fun i => boxSum d b (fun k => f k i)) (boxSum d b s) := by
  induction d with
  | zero => exact hf ()
  | succ d ih =>
    exact hasSum_sum (fun j _ => ih b.2 (fun t => f (j,t)) (fun t => s (j,t))
      (fun t => hf (j,t)))

variable {d : ℕ} (a : Vec ℝ d) (γ : Vec ℂ d)

/-- Normalized real Fourier profile: the finite sum of actual outward differences. -/
def core (b : Shell d) (H : Shell d → ℝ → ℂ) (v : ℝ) : ℂ :=
  boxSum d b (fun k => phase d γ k * coeff d (fun n => H n (weight d a k * v)) k)

/-- The raw fold of the dual slices, prior to taking any outward differences. -/
def fold (H : Shell d → ℝ → ℂ) (v : ℝ) : ℂ :=
  ∑' n, phase d γ n * H n (weight d a n * v)

/-- The geometric operator acts with conjugated, not physical, angular phase. -/
def scatter (f : ℝ → ℂ) (v : ℝ) : ℂ := ∑' j, phase d γ j * f (weight d a j * v)

/-- Shift each of the finitely many coefficient cones before summing the box.
All summability hypotheses are on individual dilation orbits, not on an
assumed folding identity. -/
theorem fold_eq_scatter (b : Shell d) (H : Shell d → ℝ → ℂ) (v : ℝ)
    (stable : ∀ x n, H (clamp d b n) x = H n x)
    (hs : ∀ k, Summable (fun j => phase d γ (shift d k j) *
      coeff d (fun n => H n (weight d a (shift d k j) * v)) k)) :
    fold a γ H v = scatter a γ (core a γ b H) v := by
  let t := fun (k j : Shell d) => phase d γ (shift d k j) *
    coeff d (fun n => H n (weight d a (shift d k j) * v)) k
  let u := fun (k n : Shell d) => phase d γ n * cone d k n
    (coeff d (fun i => H i (weight d a n * v)) k)
  have ht (k : Shell d) : HasSum (t k) (∑' j, t k j) := (hs k).hasSum
  have hu (k : Shell d) : HasSum (u k) (∑' j, t k j) := by
    apply ((shift_inj d k).hasSum_iff (f := u k) (fun n hn => by simp [u, cone_off d k n _ hn])).mp
    exact (ht k).congr_fun (fun j => by simp [Function.comp_apply, u, t, cone_shift])
  have hraw := box_hasSum d b u _ hu
  have hcore := box_hasSum d b t _ ht
  have h₁ : HasSum (fun n => phase d γ n * H n (weight d a n * v))
      (boxSum d b (fun k => ∑' j, t k j)) := hraw.congr_fun (fun n => by
    rw [finite_expansion d (fun i => H i (weight d a n * v)) b (stable _) n, box_mul])
  have h₂ : HasSum (fun j => phase d γ j * core a γ b H (weight d a j * v))
      (boxSum d b (fun k => ∑' j, t k j)) := hcore.congr_fun (fun j => by
    unfold core
    rw [box_mul]
    congr 1
    funext k
    simp only [t, weight_shift, phase_shift, mul_assoc]
    ring)
  exact h₁.tsum_eq.trans h₂.tsum_eq.symm

/-- `d₀` is the ramified conductor factor. The product radius at a dual
sample `x` in shell `n` is `d₀ * (x / weight a n)`. -/
def mask (d₀ : ℝ) (q : ℝ → ℂ) (H : Shell d → ℝ → ℂ) (n : Shell d) (x : ℝ) : ℂ :=
  q (d₀ * (x / weight d a n)) * H n x

theorem fold_mask (d₀ : ℝ) (q : ℝ → ℂ) (H : Shell d → ℝ → ℂ)
    (ha : ∀ n, weight d a n ≠ 0) (v : ℝ) :
    fold a γ (mask a d₀ q H) v = q (d₀*v) * fold a γ H v := by
  unfold fold mask
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [mul_comm (weight d a n) v, mul_div_cancel_right₀ _ (ha n)]
  ring

/-- A uniform lower bound for the finitely many unramified dilation bases.
For prime bases one can always take `r = 2`, including for the empty tuple. -/
def above (r : ℝ) : (d : ℕ) → Vec ℝ d → Prop
  | 0, _ => True
  | d+1, a => r ≤ a.1 ∧ above r d a.2

def origin : (d : ℕ) → Shell d
  | 0 => ()
  | d+1 => (0, origin d)

private theorem at_origin (d : ℕ) (a : Vec ℝ d) (γ : Vec ℂ d) :
    weight d a (origin d) = 1 ∧ phase d γ (origin d) = 1 := by
  induction d with
  | zero => exact ⟨rfl,rfl⟩
  | succ d ih => simp [weight, phase, origin, (ih a.2 γ.2).1, (ih a.2 γ.2).2]

private theorem one_le_weight {r : ℝ} (hr : 1 < r) (d : ℕ) (a : Vec ℝ d)
    (ha : above r d a) (j : Shell d) : 1 ≤ weight d a j := by
  induction d with
  | zero => exact le_rfl
  | succ d ih =>
    change 1 ≤ a.1 ^ j.1 * weight d a.2 j.2
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (hr.le.trans ha.1))
      (ih a.2 ha.2 j.2)

private theorem gap {r : ℝ} (hr : 1 < r) (d : ℕ) (a : Vec ℝ d)
    (ha : above r d a) (j : Shell d) (hj : j ≠ origin d) : r ≤ weight d a j := by
  induction d with
  | zero => cases j; exact (hj rfl).elim
  | succ d ih =>
    rcases j with ⟨m,j⟩
    cases m with
    | zero =>
      simp only [weight, pow_zero, one_mul]
      exact ih a.2 ha.2 j (fun h => hj (Prod.ext rfl h))
    | succ m =>
      have h₁ : 1 ≤ a.1 := hr.le.trans ha.1
      have h₂ := one_le_weight hr d a.2 ha.2 j
      calc
        r ≤ a.1 := ha.1
        _ ≤ a.1^(m+1) := by
          rw [pow_succ]
          exact le_mul_of_one_le_left (zero_le_one.trans h₁) (one_le_pow₀ h₁)
        _ ≤ a.1^(m+1) * weight d a.2 j :=
          le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h₁) _) h₂

/-- A compact upper real support cuts every multi-orbit to a finite box
at a strictly positive frequency. No analytic summability premise is needed. -/
theorem finite_sublevel {r : ℝ} (hr : 1 < r) (d : ℕ) (a : Vec ℝ d)
    (ha : above r d a) (B : ℝ) :
    ∃ s : Finset (Shell d), ∀ j, weight d a j ≤ B → j ∈ s := by
  classical
  induction d with
  | zero =>
    refine ⟨{()}, ?_⟩
    intro j _
    cases j
    exact Finset.mem_singleton_self _
  | succ d ih =>
    have h₁ := hr.trans_le ha.1
    obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt B h₁
    obtain ⟨s,hs⟩ := ih a.2 ha.2
    refine ⟨(Finset.range N) ×ˢ s, ?_⟩
    rintro ⟨m,j⟩ hj
    change a.1 ^ m * weight d a.2 j ≤ B at hj
    have h₂ := one_le_weight hr d a.2 ha.2 j
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_range.mpr
      by_contra! hn
      exact (not_lt_of_ge hj) (hN.trans_le ((pow_le_pow_right₀ h₁.le hn).trans
        (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h₁.le) _) h₂)))
    · exact hs j ((le_mul_of_one_le_left (zero_le_one.trans h₂) (one_le_pow₀ h₁.le)).trans hj)

private theorem orbit_summable {r : ℝ} (hr : 1 < r) (ha : above r d a)
    (B : ℝ) (f : ℝ → ℂ) (hB : ∀ x, B < x → f x = 0) {v : ℝ} (hv : 0 < v) :
    Summable (fun j => phase d γ j * f (weight d a j * v)) := by
  obtain ⟨s,hs⟩ := finite_sublevel hr d a ha (B/v)
  apply summable_of_ne_finset_zero (s := s)
  intro j hj
  rw [hB _ ((div_lt_iff₀ hv).mp (lt_of_not_ge (fun h => hj (hs j h)))), mul_zero]

/-- Injectivity on upper-bounded profiles on the open ray: peel off the
origin shell, descending through annuli of ratio `r`. -/
theorem scatter_injectiveOnRay {r : ℝ} (hr : 1 < r) (ha : above r d a)
    (f g : ℝ → ℂ) (B : ℝ) (hf : ∀ x, B < x → f x = 0)
    (hg : ∀ x, B < x → g x = 0)
    (he : ∀ x, 0 < x → scatter a γ f x = scatter a γ g x) {v : ℝ} (hv : 0 < v) :
    f v = g v := by
  classical
  have hstep (N : ℕ) : ∀ x : ℝ, 0 < x → B < r^N*x → f x = g x := by
    induction N with
    | zero =>
      intro x _ h
      simp only [pow_zero, one_mul] at h
      rw [hf x h, hg x h]
    | succ N ih =>
      intro x hx hB
      let z := fun j => phase d γ j * f (weight d a j*x) -
        phase d γ j * g (weight d a j*x)
      have hsum : (∑' j, z j) = 0 := by
        rw [show (∑' j, z j) = scatter a γ f x - scatter a γ g x from
          (orbit_summable a γ hr ha B f hf hx).tsum_sub (orbit_summable a γ hr ha B g hg hx),
          he x hx, sub_self]
      have hsingle : (∑' j, z j) = z (origin d) := by
        apply tsum_eq_single
        intro j hj
        have hgap := gap hr d a ha j hj
        have heq := ih (weight d a j*x) (mul_pos ((zero_lt_one.trans hr).trans_le hgap) hx)
          (by rw [pow_succ, mul_assoc] at hB
              exact hB.trans_le (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hgap hx.le) (pow_nonneg (zero_lt_one.trans hr).le _)))
        simp [z, heq]
      rw [hsingle] at hsum
      simpa [z, (at_origin d a γ).1, (at_origin d a γ).2, sub_eq_zero] using hsum
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (B/v) hr
  exact hstep N v hv ((div_lt_iff₀ hv).mp hN)

def BoundedAboveSupport (f : ℝ → ℂ) : Prop := ∃ B : ℝ, ∀ x, B < x → f x = 0

/-- Inverse on the actual image, with no arbitrary extension to nonsummable
profiles. The preceding injectivity theorem makes its values on `v>0` unique. -/
def inverse (y : ℝ → ℂ) (hy : ∃ f, BoundedAboveSupport f ∧
    ∀ x, 0 < x → scatter a γ f x = y x) : ℝ → ℂ := hy.choose

theorem inverse_of_scatter {r : ℝ} (hr : 1 < r) (ha : above r d a)
    (y f : ℝ → ℂ) (hf : BoundedAboveSupport f)
    (he : ∀ x, 0 < x → scatter a γ f x = y x) {v : ℝ} (hv : 0 < v) :
    inverse a γ y ⟨f,hf,he⟩ v = f v := by
  let hy : ∃ f, BoundedAboveSupport f ∧ ∀ x, 0 < x → scatter a γ f x = y x := ⟨f,hf,he⟩
  obtain ⟨C,hC⟩ := hy.choose_spec.1
  obtain ⟨B,hB⟩ := hf
  exact scatter_injectiveOnRay a γ hr ha hy.choose f (max C B)
    (fun x hx => hC x ((le_max_left ..).trans_lt hx))
    (fun x hx => hB x ((le_max_right ..).trans_lt hx))
    (fun x hx => (hy.choose_spec.2 x hx).trans (he x hx).symm) hv

/-- Enlarge the valuation box so that every point it changes, and its
clamped representative, have radius at least `L`. -/
private theorem deep_box {r : ℝ} (hr : 1 < r) (d : ℕ) (a : Vec ℝ d)
    (ha : above r d a) (b : Shell d) (L : ℝ) : ∃ c : Shell d, ∀ n,
    clamp d b (clamp d c n) = clamp d b n ∧
      (clamp d c n = n ∨ L ≤ weight d a (clamp d c n) ∧ L ≤ weight d a n) := by
  induction d with
  | zero => exact ⟨(), fun n => by cases n; exact ⟨rfl, Or.inl rfl⟩⟩
  | succ d ih =>
    obtain ⟨t,ht⟩ := ih a.2 ha.2 b.2
    have h₁ := hr.trans_le ha.1
    obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt L h₁
    let M := max b.1 N
    refine ⟨(M,t), ?_⟩
    rintro ⟨i,j⟩
    refine ⟨Prod.ext ?_ (ht j).1, ?_⟩
    · change min b.1 (min M i) = min b.1 i
      rw [← min_assoc, min_eq_left (le_max_left ..)]
    · by_cases hi : i ≤ M
      · rcases (ht j).2 with h|⟨hc,hn⟩
        · exact Or.inl (Prod.ext (min_eq_right hi) h)
        · exact Or.inr ⟨hc.trans (le_mul_of_one_le_left
            (zero_le_one.trans (one_le_weight hr d a.2 ha.2 _)) (one_le_pow₀ h₁.le)),
            hn.trans (le_mul_of_one_le_left (zero_le_one.trans (one_le_weight hr d a.2 ha.2 _))
              (one_le_pow₀ h₁.le))⟩
      · have hM : M ≤ i := by omega
        have hpow : L ≤ a.1 ^ M := hN.le.trans (pow_le_pow_right₀ h₁.le (le_max_right ..))
        apply Or.inr
        simp only [clamp, weight, min_eq_left hM]
        exact ⟨hpow.trans (le_mul_of_one_le_right (pow_nonneg (zero_le_one.trans h₁.le) _)
            (one_le_weight hr d a.2 ha.2 _)),
          (hpow.trans (pow_le_pow_right₀ h₁.le hM)).trans (le_mul_of_one_le_right
            (pow_nonneg (zero_le_one.trans h₁.le) _) (one_le_weight hr d a.2 ha.2 _))⟩

theorem mask_stable {r : ℝ} (hr : 1 < r) (ha : above r d a)
    (b : Shell d) (H : Shell d → ℝ → ℂ)
    (stable : ∀ x n, H (clamp d b n) x = H n x)
    (B : ℝ) (bounded : ∀ n x, B < |x| → H n x = 0)
    (d₀ : ℝ) (q : ℝ → ℂ) (ε : ℝ) (hε : 0 < ε)
    (plateau : ∀ x, |x| < ε → q x = q 0) :
    ∃ c, ∀ x n, mask a d₀ q H (clamp d c n) x = mask a d₀ q H n x := by
  let L := |d₀| * B / ε + 1
  obtain ⟨c,hc⟩ := deep_box hr d a ha b L
  refine ⟨c, fun x n => ?_⟩
  have hH : H (clamp d c n) x = H n x := by
    rw [← stable x (clamp d c n), (hc n).1, stable]
  unfold mask
  rw [hH]
  by_cases hx : B < |x|
  · simp [bounded n x hx]
  rcases (hc n).2 with h|⟨h₁,h₂⟩
  · rw [h]
  have small (j : Shell d) (hj : L ≤ weight d a j) :
      q (d₀ * (x / weight d a j)) = q 0 := by
    have hw : 0 < weight d a j := zero_lt_one.trans_le (one_le_weight hr d a ha _)
    apply plateau
    rw [abs_mul, abs_div, abs_of_pos hw, ← mul_div_assoc]
    apply (div_lt_iff₀ hw).mpr
    have hstrict : |d₀| * B / ε < weight d a j := (lt_add_one _).trans_le hj
    exact (mul_le_mul_of_nonneg_left (le_of_not_gt hx) (abs_nonneg d₀)).trans_lt
      (by simpa [mul_comm] using (div_lt_iff₀ hε).mp hstrict)
  rw [small _ h₁, small _ h₂]

private theorem coeff_zero (d : ℕ) (k : Shell d) :
    coeff d (fun _ => (0 : ℂ)) k = 0 := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rcases k with ⟨j,k⟩
    cases j <;> simpa [coeff, back] using ih k

private theorem box_zero' (d : ℕ) (b : Shell d) : boxSum d b (fun _ => (0 : ℂ)) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [boxSum, ih]

private theorem coeff_out (H : Shell d → ℝ → ℂ) (B : ℝ)
    (bounded : ∀ n x, B < |x| → H n x = 0) (x : ℝ) (hx : B < |x|) (k : Shell d) :
    coeff d (fun n => H n x) k = 0 := by
  have he : (fun n => H n x) = fun _ => (0 : ℂ) := funext (fun n => bounded n x hx)
  rw [he, coeff_zero]

private theorem core_bounded {r : ℝ} (hr : 1 < r) (ha : above r d a)
    (b : Shell d) (H : Shell d → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (bounded : ∀ n x, B < |x| → H n x = 0) : BoundedAboveSupport (core a γ b H) := by
  refine ⟨B, fun x hx => ?_⟩
  have h (k : Shell d) : B < |weight d a k*x| :=
    (hx.trans_le (le_mul_of_one_le_left (hB.trans hx.le) (one_le_weight hr d a ha k))).trans_le
      (le_abs_self _)
  have hz (k : Shell d) := coeff_out H B bounded _ (h k) k
  simp [core, hz, box_zero']

theorem fold_eq_scatter_of_bounded {r : ℝ} (hr : 1 < r) (ha : above r d a)
    (b : Shell d) (H : Shell d → ℝ → ℂ) (B : ℝ)
    (bounded : ∀ n x, B < |x| → H n x = 0)
    (stable : ∀ x n, H (clamp d b n) x = H n x) {v : ℝ} (hv : 0 < v) :
    fold a γ H v = scatter a γ (core a γ b H) v := by
  apply fold_eq_scatter a γ b H v stable
  intro k
  obtain ⟨s,hs⟩ := finite_sublevel hr d a ha (B/v)
  apply summable_of_ne_finset_zero (s := s)
  intro j hj
  have h : B < weight d a j * v := (div_lt_iff₀ hv).mp (lt_of_not_ge (fun h => hj (hs j h)))
  have hw := one_le_weight hr d a ha j
  have hk := one_le_weight hr d a ha k
  have h' : B < |weight d a (shift d k j) * v| := by
    rw [weight_shift, mul_assoc]
    exact (h.trans_le (le_mul_of_one_le_left (mul_nonneg (zero_le_one.trans hw) hv.le) hk)).trans_le
      (le_abs_self _)
  rw [coeff_out H B bounded _ h' _, mul_zero]

/-- Actual finite-stage descent. The new box exists by the plateau, not by
assuming invariance of a normalized level. In raw coordinates the result is
`M_q`; in normalized coordinates it is exactly `S⁻¹ M_q S` on the open ray. -/
theorem normalized_mask {r : ℝ} (hr : 1 < r) (ha : above r d a)
    (b : Shell d) (H : Shell d → ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (bounded : ∀ n x, B < |x| → H n x = 0)
    (stable : ∀ x n, H (clamp d b n) x = H n x)
    (d₀ : ℝ) (q : ℝ → ℂ) (ε : ℝ) (hε : 0 < ε) (plateau : ∀ x, |x| < ε → q x = q 0) :
    let y := fun x => q (d₀*x) * scatter a γ (core a γ b H) x
    ∃ c, (∀ x n, mask a d₀ q H (clamp d c n) x = mask a d₀ q H n x) ∧
      ∃ hy : ∃ f, BoundedAboveSupport f ∧ ∀ x, 0 < x → scatter a γ f x = y x,
        ∀ v, 0 < v → core a γ c (mask a d₀ q H) v = inverse a γ y hy v := by
  dsimp only
  obtain ⟨c,hc⟩ := mask_stable a hr ha b H stable B bounded d₀ q ε hε plateau
  have hm : ∀ n x, B < |x| → mask a d₀ q H n x = 0 := by
    intro n x hx; simp [mask, bounded n x hx]
  have hb := core_bounded a γ hr ha c _ B hB hm
  have he (x : ℝ) (hx : 0 < x) : scatter a γ (core a γ c (mask a d₀ q H)) x =
      q (d₀*x) * scatter a γ (core a γ b H) x := by
    rw [← fold_eq_scatter_of_bounded a γ hr ha c _ B hm hc hx,
      ← fold_eq_scatter_of_bounded a γ hr ha b H B bounded stable hx]
    exact fold_mask a γ d₀ q H (fun n => (zero_lt_one.trans_le (one_le_weight hr d a ha n)).ne') x
  exact ⟨c,hc,⟨_,hb,he⟩,fun _ hv => (inverse_of_scatter a γ hr ha _ _ hb he hv).symm⟩

private theorem above_implies_geOne {r : ℝ} (hr : 1 < r) (d : ℕ) (a : Vec ℝ d)
    (ha : above r d a) : basesGEOne d a := by
  induction d with
  | zero => trivial
  | succ d ih => exact ⟨hr.le.trans ha.1, ih a.2 ha.2⟩

/-- Paper: (12.4.1.8), p. 517. If the true product-frequency band becomes
`|u| ≤ B * weight a k` at valuation `k`, then the normalized profile has the
real Fourier band `|v| ≤ B`. This holds after any gate, independently of its
plateau; the plateau is separately what supplies the finite clamping box. -/
theorem core_eq_zero_outside_band {r : ℝ} (hr : 1 < r) (ha : above r d a)
    (b : Shell d) (H : Shell d → ℝ → ℂ) {B : ℝ} (hB : 0 ≤ B)
    (hH : ∀ k u, B * weight d a k < |u| → H k u = 0)
    (v : ℝ) (hv : B < |v|) : core a γ b H v = 0 := by
  have hw (k : Shell d) : 0 < weight d a k :=
    zero_lt_one.trans_le (one_le_weight hr d a ha k)
  have hz (k : Shell d) : coeff d (fun n ↦ H n (weight d a k * v)) k = 0 := by
    refine coeff_support d a (above_implies_geOne hr d a ha) B (weight d a k * v) hB
      (fun n ↦ H n (weight d a k * v)) (fun j hj ↦ hH j _ hj) k ?_
    · rw [abs_mul, abs_of_pos (hw k), mul_comm B]
      exact mul_lt_mul_of_pos_left hv (hw k)
  simp [core, hz, box_zero']

end RiemannMasullo.QuotientFrequencyFold
