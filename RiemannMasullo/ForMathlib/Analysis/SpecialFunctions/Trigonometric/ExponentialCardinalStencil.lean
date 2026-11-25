module

public import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Trigonometric.HyperbolicCardinal
public import Mathlib.Order.SuccPred.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Cardinal interpolation for the exponential kernel

Write `q_z(t) = exp (-|t - z|)`. A neighbor at `z ± d` contributes
`a_d q_z - b_d q_(z ± d)`, where `b_d = (exp d - exp (-d))⁻¹` and `a_d = exp (-d) b_d`.
Adding the contributions of the present neighbors to `q_z` gives a function that is one
at `z` and zero at every other site.

On a side with a neighbor, the cardinal function agrees with `profile d` up to that neighbor
and vanishes beyond it. On an unbounded side it agrees with the exponential kernel.
The same coefficients apply to vectors in any real module by `observe_cardinalStencil`.
-/

@[expose] public noncomputable section

namespace RiemannMasullo.GeometricHat

/-- The exponential kernel centered at `z`. -/
def expKernel (z t : ℝ) : ℝ := Real.exp (-|t - z|)

/-- The magnitude of the off-diagonal coefficient for a gap of width `d`. -/
def neighborWeight (d : ℝ) : ℝ := (Real.exp d - Real.exp (-d))⁻¹

/-- The contribution of one neighbor to the central coefficient. -/
def centerAdjustment (d : ℝ) : ℝ := Real.exp (-d) * neighborWeight d

/-- The correction from a single optional neighbor, with the center and the neighboring
vector supplied separately. -/
def neighborCorrection {E : Type*} [AddCommGroup E] [Module ℝ E]
    (gap : Option (Set.Ioi (0 : ℝ))) (center : E) (neighbor : ℝ → E) : E :=
  match gap with
  | none => 0
  | some d => centerAdjustment d.1 • center - neighborWeight d.1 • neighbor d.1

/-- The linear combination of the vector at `z` and the vectors at its present neighbors. -/
def cardinalStencil {E : Type*} [AddCommGroup E] [Module ℝ E]
    (k : ℝ → E) (z : ℝ) (left right : Option (Set.Ioi (0 : ℝ))) : E :=
  k z + neighborCorrection left (k z) (fun d ↦ k (z - d)) +
    neighborCorrection right (k z) (fun d ↦ k (z + d))

/-- The cardinal profile as a three-kernel linear combination on the entire real line. -/
def cardinalHat (z : ℝ) (left right : Option (Set.Ioi (0 : ℝ))) (t : ℝ) : ℝ :=
  cardinalStencil (fun j ↦ expKernel j t) z left right

/-- The side profile in the outward distance coordinate `r`. A finite side agrees with the
hyperbolic profile up to its neighbor. A side without a neighbor decays exponentially. -/
def sideProfile (gap : Option (Set.Ioi (0 : ℝ))) (r : ℝ) : ℝ :=
  match gap with
  | none => Real.exp (-r)
  | some d => if r ≤ d.1 then profile d.1 r else 0

private def correctionAt (gap : Option (Set.Ioi (0 : ℝ))) (r : ℝ) : ℝ :=
  neighborCorrection gap (Real.exp (-|r|)) (fun d ↦ Real.exp (-|r - d|))

private theorem cardinalHat_signed (z : ℝ) (left right : Option (Set.Ioi (0 : ℝ))) (t : ℝ) :
    cardinalHat z left right t =
      expKernel z t + correctionAt left (z - t) + correctionAt right (t - z) := by
  have hc : expKernel z t = Real.exp (-|z - t|) := by rw [expKernel, abs_sub_comm]
  have hl (d : ℝ) : expKernel (z - d) t = Real.exp (-|(z - t) - d|) := by
    rw [expKernel, show t - (z - d) = -((z - t) - d) by ring, abs_neg]
  have hr (d : ℝ) : expKernel (z + d) t = Real.exp (-|(t - z) - d|) := by
    rw [expKernel, show t - (z + d) = (t - z) - d by ring]
  have hl' : neighborCorrection left (expKernel z t) (fun d ↦ expKernel (z - d) t) =
      correctionAt left (z - t) := by
    rw [hc, funext hl]
    rfl
  have hr' : neighborCorrection right (expKernel z t) (fun d ↦ expKernel (z + d) t) =
      correctionAt right (t - z) := by
    rw [funext hr]
    rfl
  unfold cardinalHat cardinalStencil
  rw [hl', hr']

private theorem correctionAt_of_nonpos (gap : Option (Set.Ioi (0 : ℝ))) {r : ℝ} (hr : r ≤ 0) :
    correctionAt gap r = 0 := by
  cases gap with
  | none => rfl
  | some d =>
    have hrd : r - d.1 ≤ 0 := sub_nonpos.mpr (hr.trans d.property.le)
    have h : Real.exp (-|r - d.1|) = Real.exp (-d.1) * Real.exp (-|r|) := by
      rw [abs_of_nonpos hrd, abs_of_nonpos hr, ← Real.exp_add]
      congr 1
      ring
    simp only [correctionAt, neighborCorrection, smul_eq_mul, centerAdjustment, h]
    ring

private theorem one_add_centerAdjustment {d : ℝ} (hd : 0 < d) :
    1 + centerAdjustment d = Real.exp d * neighborWeight d := by
  have h : 0 < Real.exp d - Real.exp (-d) :=
    sub_pos.mpr (Real.exp_lt_exp.mpr ((neg_lt_zero.mpr hd).trans hd))
  unfold centerAdjustment neighborWeight
  field_simp [h.ne']
  ring

private theorem exp_add_correctionAt (gap : Option (Set.Ioi (0 : ℝ))) {r : ℝ}
    (hr : 0 ≤ r) : Real.exp (-|r|) + correctionAt gap r = sideProfile gap r := by
  cases gap with
  | none => simp [correctionAt, neighborCorrection, sideProfile, abs_of_nonneg hr]
  | some d =>
    simp only [correctionAt, neighborCorrection, smul_eq_mul, abs_of_nonneg hr, sideProfile]
    have h : Real.exp (-r) + (centerAdjustment d.1 * Real.exp (-r) -
        neighborWeight d.1 * Real.exp (-|r - d.1|)) =
        neighborWeight d.1 * (Real.exp (d.1 - r) - Real.exp (-|r - d.1|)) := by
      rw [sub_eq_add_neg d.1 r, Real.exp_add]
      linear_combination Real.exp (-r) * one_add_centerAdjustment d.property
    rw [h]
    by_cases hrd : r ≤ d.1
    · rw [ite_eq_left hrd, abs_of_nonpos (sub_nonpos.mpr hrd), neg_neg, ← neg_sub d.1 r]
      have htwo (x : ℝ) : Real.exp x - Real.exp (-x) = 2 * Real.sinh x := by
        rw [Real.sinh_eq]
        ring
      unfold neighborWeight profile
      rw [htwo d.1, htwo (d.1 - r)]
      have hs := (Real.sinh_pos_iff.mpr d.property).ne'
      field_simp [hs]
    · rw [ite_eq_right hrd, abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hrd)), neg_sub, sub_self,
        mul_zero]

/-- At an outward distance to the right, only the right neighbor changes the profile. -/
theorem cardinalHat_right (z : ℝ) (left right : Option (Set.Ioi (0 : ℝ))) {r : ℝ} (hr : 0 ≤ r) :
    cardinalHat z left right (z + r) = sideProfile right r := by
  rw [cardinalHat_signed, show z - (z + r) = -r by ring, add_sub_cancel_left,
    correctionAt_of_nonpos left (neg_nonpos.mpr hr), add_zero]
  simpa only [expKernel, add_sub_cancel_left] using exp_add_correctionAt right hr

/-- At an outward distance to the left, only the left neighbor changes the profile. -/
theorem cardinalHat_left (z : ℝ) (left right : Option (Set.Ioi (0 : ℝ))) {r : ℝ} (hr : 0 ≤ r) :
    cardinalHat z left right (z - r) = sideProfile left r := by
  rw [cardinalHat_signed, sub_sub_cancel, show z - r - z = -r by ring,
    correctionAt_of_nonpos right (neg_nonpos.mpr hr), add_zero]
  simpa only [expKernel, show z - r - z = -r by ring, abs_neg] using exp_add_correctionAt left hr

/-- A finite side vanishes at its neighbor and everywhere farther out. -/
theorem sideProfile_of_le {d : Set.Ioi (0 : ℝ)} {r : ℝ} (hr : d.1 ≤ r) :
    sideProfile (some d) r = 0 := by
  rcases hr.eq_or_lt with h | h
  · subst r
    simp [sideProfile, profile]
  · simp [sideProfile, h.not_ge]

/-- A missing neighbor leaves the original exponential on that side. -/
theorem sideProfile_none (r : ℝ) : sideProfile none r = Real.exp (-r) := rfl

/-- Up to the neighboring site the side profile is the normalized hyperbolic sine. -/
theorem sideProfile_in_gap (d : Set.Ioi (0 : ℝ)) {r : ℝ} (hr : r ≤ d.1) :
    sideProfile (some d) r = profile d.1 r := ite_eq_left hr

/-- The outward profile has value one at the center for every choice of neighbor. -/
theorem sideProfile_zero (gap : Option (Set.Ioi (0 : ℝ))) : sideProfile gap 0 = 1 := by
  cases gap with
  | none => simp [sideProfile]
  | some d => simp [sideProfile, profile, d.property.le, (Real.sinh_pos_iff.mpr d.property).ne']

/-- The stencil interpolates one at its center for every combination of neighbors. -/
theorem cardinalHat_self (z : ℝ) (left right : Option (Set.Ioi (0 : ℝ))) :
    cardinalHat z left right z = 1 := by
  simpa only [add_zero, sideProfile_zero] using cardinalHat_right z left right (r := 0) le_rfl

/-- A singleton's cardinal function consists of the unmodified exponential. -/
theorem cardinalHat_singleton (z t : ℝ) : cardinalHat z none none t = expKernel z t := by
  simp [cardinalHat, cardinalStencil, neighborCorrection]

/-- Every side lies between zero and the exponential with the same center. -/
theorem sideProfile_bounds (gap : Option (Set.Ioi (0 : ℝ))) {r : ℝ} (hr : 0 ≤ r) :
    0 ≤ sideProfile gap r ∧ sideProfile gap r ≤ Real.exp (-r) := by
  cases gap with
  | none => exact ⟨(Real.exp_pos _).le, le_rfl⟩
  | some d =>
    by_cases hrd : r ≤ d.1
    · rw [sideProfile_in_gap d hrd]
      exact profile_bounds d.property hr hrd
    · rw [sideProfile_of_le (le_of_not_ge hrd)]
      exact ⟨le_rfl, (Real.exp_pos _).le⟩

/-- Bounds on the translated cardinal function hold pointwise, independently of the gap lengths. -/
theorem cardinalHat_bounds (z : ℝ) (left right : Option (Set.Ioi (0 : ℝ))) (t : ℝ) :
    0 ≤ cardinalHat z left right t ∧ cardinalHat z left right t ≤ Real.exp (-|t - z|) := by
  rcases le_total z t with h | h
  · have hr := sub_nonneg.mpr h
    have he := cardinalHat_right z left right hr
    rw [add_sub_cancel] at he
    rw [he, abs_of_nonneg hr]
    exact sideProfile_bounds right hr
  · have hr := sub_nonneg.mpr h
    have he := cardinalHat_left z left right hr
    rw [sub_sub_cancel] at he
    rw [he, abs_sub_comm t z, abs_of_nonneg hr]
    exact sideProfile_bounds left hr

/-- A nearest gap is attained and is minimal among the strictly positive site distances.
The missing case means that there are no sites in that direction. -/
def IsNearestGap (distances : Set (Set.Ioi (0 : ℝ)))
    (gap : Option (Set.Ioi (0 : ℝ))) : Prop :=
  match gap with
  | none => distances = ∅
  | some d => IsLeast distances d

/-- A present nearest gap represents an actual site distance. -/
theorem IsNearestGap.mem_of_some {distances : Set (Set.Ioi (0 : ℝ))}
    {gap : Option (Set.Ioi (0 : ℝ))} (hg : IsNearestGap distances gap)
    {d : Set.Ioi (0 : ℝ)} (hd : gap = some d) : d ∈ distances := by
  subst gap
  exact hg.1

/-- The side profile vanishes at every occupied positive distance when the gap is nearest. -/
theorem IsNearestGap.sideProfile_eq_zero {distances : Set (Set.Ioi (0 : ℝ))}
    {gap : Option (Set.Ioi (0 : ℝ))} (hg : IsNearestGap distances gap)
    {r : Set.Ioi (0 : ℝ)} (hr : r ∈ distances) : sideProfile gap r.1 = 0 := by
  cases gap with
  | none => exact False.elim (Set.notMem_empty _ (hg ▸ hr))
  | some d => exact sideProfile_of_le (hg.2 hr)

/-- Kronecker interpolation on an arbitrary subset of the line having the specified
adjacent sites, with missing neighbors allowed on either side. -/
theorem cardinalHat_at_node {sites : Set ℝ} {z : ℝ} {left right : Option (Set.Ioi (0 : ℝ))}
    (hl : IsNearestGap {d | z - d.1 ∈ sites} left)
    (hr : IsNearestGap {d | z + d.1 ∈ sites} right) {t : ℝ} (ht : t ∈ sites) :
    cardinalHat z left right t = if t = z then 1 else 0 := by
  split
  next h =>
    subst t
    exact cardinalHat_self z left right
  next h =>
    rcases lt_or_gt_of_ne h with hlt | hgt
    · let d : Set.Ioi (0 : ℝ) := ⟨z - t, sub_pos.mpr hlt⟩
      have hd : z - d.1 = t := sub_sub_cancel _ _
      have he := cardinalHat_left z left right d.property.le
      rw [hd] at he
      exact he.trans (hl.sideProfile_eq_zero (r := d) (show z - d.1 ∈ sites by rwa [hd]))
    · let d : Set.Ioi (0 : ℝ) := ⟨t - z, sub_pos.mpr hgt⟩
      have hd : z + d.1 = t := add_sub_cancel _ _
      have he := cardinalHat_right z left right d.property.le
      rw [hd] at he
      exact he.trans (hr.sideProfile_eq_zero (r := d) (show z + d.1 ∈ sites by rwa [hd]))

section OrderedSites

variable {ι : Type*} [LinearOrder ι] (t : ι → ℝ) (ht : StrictMono t)

/-- Actual predecessor distance for an ordered site family, or no gap at its minimum. -/
def leftSiteGap [PredOrder ι] (i : ι) : Option (Set.Ioi (0 : ℝ)) :=
  if h : Order.pred i < i then some ⟨t i - t (Order.pred i), sub_pos.mpr (ht h)⟩ else none

/-- Actual successor distance for an ordered site family, or no gap at its maximum. -/
def rightSiteGap [SuccOrder ι] (i : ι) : Option (Set.Ioi (0 : ℝ)) :=
  if h : i < Order.succ i then some ⟨t (Order.succ i) - t i, sub_pos.mpr (ht h)⟩ else none

/-- The predecessor gives the nearest occupied distance on the left. -/
theorem leftSiteGap_isNearest [PredOrder ι] (i : ι) :
    IsNearestGap {d | t i - d.1 ∈ Set.range t} (leftSiteGap t ht i) := by
  unfold leftSiteGap
  split
  next h =>
    constructor
    · exact ⟨Order.pred i, (sub_sub_cancel _ _).symm⟩
    · rintro ⟨r, hpos⟩ ⟨j, hj⟩
      change t j = t i - r at hj
      change 0 < r at hpos
      have hij : j < i := ht.lt_iff_lt.mp (by linarith only [hj, hpos])
      change t i - t (Order.pred i) ≤ r
      linarith only [ht.monotone (Order.le_pred_of_lt hij), hj]
  next h =>
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨r, hpos⟩ ⟨j, hj⟩
    change t j = t i - r at hj
    change 0 < r at hpos
    have hij : j < i := ht.lt_iff_lt.mp (by linarith only [hj, hpos])
    exact h (Order.pred_lt_of_not_isMin hij.not_isMin)

/-- The successor gives the nearest occupied distance on the right. -/
theorem rightSiteGap_isNearest [SuccOrder ι] (i : ι) :
    IsNearestGap {d | t i + d.1 ∈ Set.range t} (rightSiteGap t ht i) := by
  unfold rightSiteGap
  split
  next h =>
    constructor
    · exact ⟨Order.succ i, (add_sub_cancel _ _).symm⟩
    · rintro ⟨r, hpos⟩ ⟨j, hj⟩
      change t j = t i + r at hj
      change 0 < r at hpos
      have hij : i < j := ht.lt_iff_lt.mp (by linarith only [hj, hpos])
      change t (Order.succ i) - t i ≤ r
      linarith only [ht.monotone (Order.succ_le_of_lt hij), hj]
  next h =>
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨r, hpos⟩ ⟨j, hj⟩
    change t j = t i + r at hj
    change 0 < r at hpos
    have hij : i < j := ht.lt_iff_lt.mp (by linarith only [hj, hpos])
    exact h (Order.lt_succ_of_not_isMax hij.not_isMax)

end OrderedSites

section Vectors

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- The local stencil commutes with every real-linear observation. -/
theorem map_cardinalStencil (L : E →ₗ[ℝ] F) (k : ℝ → E) (z : ℝ)
    (left right : Option (Set.Ioi (0 : ℝ))) :
    L (cardinalStencil k z left right) = cardinalStencil (fun j ↦ L (k j)) z left right := by
  cases left <;> cases right <;> simp [cardinalStencil, neighborCorrection]

private theorem neighborCorrection_congr (g : Option (Set.Ioi (0 : ℝ))) {x y : E}
    {f f' : ℝ → E} (h : x = y) (hg : ∀ d, g = some d → f d.1 = f' d.1) :
    neighborCorrection g x f = neighborCorrection g y f' := by
  cases g with
  | none => rfl
  | some d => simp only [neighborCorrection, h, hg d rfl]

/-- Equality at the center and the present neighbors suffices to identify two stencils. -/
theorem cardinalStencil_congr {k k' : ℝ → E} {z : ℝ} {left right : Option (Set.Ioi (0 : ℝ))}
    (hz : k z = k' z) (hl : ∀ d, left = some d → k (z - d.1) = k' (z - d.1))
    (hr : ∀ d, right = some d → k (z + d.1) = k' (z + d.1)) :
    cardinalStencil k z left right = cardinalStencil k' z left right :=
  congrArg₂ (· + ·) (congrArg₂ (· + ·) hz (neighborCorrection_congr left hz hl))
    (neighborCorrection_congr right hz hr)

private theorem neighborCorrection_mem (M : Submodule ℝ E) (g : Option (Set.Ioi (0 : ℝ)))
    {x : E} {f : ℝ → E} (hx : x ∈ M) (hg : ∀ d, g = some d → f d.1 ∈ M) :
    neighborCorrection g x f ∈ M := by
  cases g with
  | none => exact M.zero_mem
  | some d => exact M.sub_mem (M.smul_mem _ hx) (M.smul_mem _ (hg d rfl))

/-- The vector stencil belongs to any real submodule containing its occupied vectors. -/
theorem cardinalStencil_mem (M : Submodule ℝ E) {k : ℝ → E} {z : ℝ}
    {left right : Option (Set.Ioi (0 : ℝ))} (hz : k z ∈ M)
    (hl : ∀ d, left = some d → k (z - d.1) ∈ M)
    (hr : ∀ d, right = some d → k (z + d.1) ∈ M) :
    cardinalStencil k z left right ∈ M :=
  M.add_mem (M.add_mem hz (neighborCorrection_mem M left hz hl))
    (neighborCorrection_mem M right hz hr)

/-- A submodule containing all site vectors contains the stencil formed from their nearest
neighbors, even when the set of sites is infinite. -/
theorem cardinalStencil_mem_of_sites (M : Submodule ℝ E) {k : ℝ → E} {sites : Set ℝ}
    {z : ℝ} {left right : Option (Set.Ioi (0 : ℝ))} (hz : z ∈ sites)
    (hl : IsNearestGap {d | z - d.1 ∈ sites} left) (hr : IsNearestGap {d | z + d.1 ∈ sites} right)
    (hk : ∀ j ∈ sites, k j ∈ M) : cardinalStencil k z left right ∈ M :=
  cardinalStencil_mem M (hk z hz) (fun _ h ↦ hk _ (hl.mem_of_some h))
    (fun _ h ↦ hk _ (hr.mem_of_some h))

/-- Suppose a real-linear map sends each occupied vector to its exponential kernel value at
`t` times a fixed vector `v`. Then it sends their stencil to the cardinal value at `t` times `v`. -/
theorem observe_cardinalStencil (L : E →ₗ[ℝ] F) {k : ℝ → E} {z t : ℝ}
    {left right : Option (Set.Ioi (0 : ℝ))} (v : F) (hz : L (k z) = expKernel z t • v)
    (hl : ∀ d, left = some d → L (k (z - d.1)) = expKernel (z - d.1) t • v)
    (hr : ∀ d, right = some d → L (k (z + d.1)) = expKernel (z + d.1) t • v) :
    L (cardinalStencil k z left right) = cardinalHat z left right t • v := by
  rw [map_cardinalStencil]
  calc
    cardinalStencil (fun j ↦ L (k j)) z left right =
        cardinalStencil (fun j ↦ expKernel j t • v) z left right := cardinalStencil_congr hz hl hr
    _ = cardinalHat z left right t • v :=
      (map_cardinalStencil (LinearMap.toSpanSingleton ℝ F v)
        (fun j ↦ expKernel j t) z left right).symm

end Vectors

end RiemannMasullo.GeometricHat
