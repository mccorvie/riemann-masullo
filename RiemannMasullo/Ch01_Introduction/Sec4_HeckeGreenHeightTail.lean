module

public import RiemannMasullo.Ch01_Introduction.Sec4_HeckeGreenExterior
import RiemannMasullo.ForMathlib.Analysis.Complex.HalfPlaneJensenTail
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Exterior Hecke mass above a verified height

A reciprocal-power tail counts the actual positive divisor with multiplicities at both
signs of the ordinate. Horizontal reflection pairs the strict right and left sites.
-/

@[expose] public noncomputable section

open Complex Function NumberField

namespace RiemannMasullo.HeckePoisson

variable {F : Type*} [Field F] [NumberField F]
local notation "U𝔽" => PontryaginDual (IdeleClassGroup (𝓞 F) F)
set_option quotPrecheck false

local notation "High(" χ ", " H ")" => {z : Site χ // (H : ℝ) < |z.val.im|}

/-- The full two-sided multiplicity-weighted reciprocal-power tail above height `H`. -/
def inverseHeightTail (χ : U𝔽) (H : ℝ) (k : ℕ) : ℝ :=
  ∑' z : High(χ, H), (multiplicity z.val : ℝ) / |z.val.val.im| ^ k

private theorem real_multiplicity {χ : U𝔽} (z : Site χ) :
    (multiplicity z : ℝ) = (HeckeHalfPlaneJensen.order χ z.val : ℝ) := by
  exact_mod_cast Int.toNat_of_nonneg z.property.le

/-- The unit-window Hecke zero count implies summability of every reciprocal height power
of order at least two above each strictly positive cutoff, counting all divisor orders. -/
theorem summable_inverseHeightTail (χ : U𝔽) {H : ℝ} (hH : 0 < H) {k : ℕ} (hk : 2 ≤ k) :
    Summable (fun z : High(χ, H) ↦ (multiplicity z.val : ℝ) / |z.val.val.im| ^ k) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  have hbase : Summable (fun z : Site χ ↦ (multiplicity z : ℝ) / (1 + |z.val.im|) ^ 2) := by
    have hg : Summable (fun z : Site χ ↦ (HeckeHalfPlaneJensen.order χ z.val : ℝ) /
        (1 + |z.val.im|) ^ 2) := explicitFormulaCompletedHeckeL_summable_divisor_div_sq χ
    apply hg.congr
    intro z
    rw [real_multiplicity]
  let C := (1 + H⁻¹) ^ 2 * (H ^ j)⁻¹
  have hb := (hbase.subtype (fun z : Site χ ↦ H < |z.val.im|)).mul_left C
  apply Summable.of_nonneg_of_le (fun z ↦ by positivity) _ hb
  intro z
  let y := |z.val.val.im|
  have hy : H < y := z.property
  have hy₀ := hH.trans hy
  have h1 : 1 ≤ H⁻¹ * y := by
    calc
      1 = H⁻¹ * H := (inv_mul_cancel₀ hH.ne').symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hy.le (inv_nonneg.mpr hH.le)
  have hlin : 1 + y ≤ (1 + H⁻¹) * y := by linarith
  have hpow : 1 ≤ (H ^ j)⁻¹ * y ^ j := by
    calc
      1 = (H ^ j)⁻¹ * H ^ j := (inv_mul_cancel₀ (pow_ne_zero _ hH.ne')).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hH.le hy.le j) (by positivity)
  have hdom : (1 + y) ^ 2 ≤ C * y ^ (2 + j) := calc
    _ ≤ ((1 + H⁻¹) * y) ^ 2 := pow_le_pow_left₀ (by positivity) hlin 2
    _ ≤ ((1 + H⁻¹) * y) ^ 2 * ((H ^ j)⁻¹ * y ^ j) :=
      le_mul_of_one_le_right (sq_nonneg _) hpow
    _ = _ := by dsimp only [C]; rw [pow_add]; ring
  change (multiplicity z.val : ℝ) / y ^ (2 + j) ≤ C * ((multiplicity z.val : ℝ) / (1 + y) ^ 2)
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ (pow_pos hy₀ _) (by positivity)).mpr
  exact (mul_le_mul_of_nonneg_left hdom (Nat.cast_nonneg _)).trans_eq (by ring)

private theorem high_of_right {χ : U𝔽} {H : ℝ}
    (hc : ∀ z : Site χ, |z.val.im| ≤ H → z.val.re = 1 / 2)
    (z : HeckeHalfPlaneJensen.RightSite χ) : H < |z.val.im| := by
  by_contra! h
  exact z.property.2.ne' (hc ⟨z.val, z.property.1⟩ h)

private theorem right_tail_pair {χ : U𝔽} {H : ℝ} {k : ℕ} (hH : 0 < H) (hk : 2 ≤ k)
    (hc : ∀ z : Site χ, |z.val.im| ≤ H → z.val.re = 1 / 2) :
    let f := fun z : HeckeHalfPlaneJensen.RightSite χ ↦
      (HeckeHalfPlaneJensen.order χ z.val : ℝ) / |z.val.im| ^ k
    Summable f ∧ 2 * (∑' z, f z) ≤ inverseHeightTail χ H k := by
  classical
  let R := HeckeHalfPlaneJensen.RightSite χ
  let r (z : R) : High(χ, H) := ⟨⟨z.val, z.property.1⟩, high_of_right hc z⟩
  let l (z : R) : High(χ, H) := ⟨positiveSiteReflection χ (r z).val, by
    simpa only [positiveSiteReflection_im] using (r z).property⟩
  let w (z : High(χ, H)) := (multiplicity z.val : ℝ) / |z.val.val.im| ^ k
  let f (z : R) := (HeckeHalfPlaneJensen.order χ z.val : ℝ) / |z.val.im| ^ k
  have hr : Injective r := fun z u h ↦ Subtype.ext (congrArg (fun t : High(χ, H) ↦ t.val.val) h)
  have hl : Injective l := fun z u h ↦ hr (Subtype.ext ((positiveSiteReflection χ).injective
    (congrArg (fun t : High(χ, H) ↦ t.val) h)))
  have hdisj (z u : R) : r z ≠ l u := by
    intro h
    have he := congrArg (fun t : High(χ, H) ↦ t.val.val.re) h
    change z.val.re = 1 - u.val.re at he
    linarith [z.property.2, u.property.2]
  have hwr (z : R) : w (r z) = f z := by
    dsimp only [w, f]
    rw [real_multiplicity]
  have hwl (z : R) : w (l z) = f z := by
    simpa only [w, l, multiplicity_reflection, positiveSiteReflection_im] using hwr z
  have ht : Summable w := summable_inverseHeightTail χ hH hk
  have hs : Summable f := (ht.comp_injective hr).congr hwr
  let p := Sum.elim r l
  let d := Sum.elim f f
  have hi : Injective p := Sum.elim_injective.mpr ⟨hr, hl, hdisj⟩
  have hd : HasSum d ((∑' z, f z) + ∑' z, f z) := HasSum.sum hs.hasSum hs.hasSum
  have he (z : R ⊕ R) : d z ≤ w (p z) := by
    cases z with
    | inl z => exact (hwr z).ge
    | inr z => exact (hwl z).ge
  have hle := hd.summable.tsum_le_tsum_of_inj p hi (fun z _ ↦ by dsimp [w]; positivity) he ht
  rw [hd.tsum_eq, ← two_mul] at hle
  exact ⟨hs, hle⟩

/-- Uniformly for references `2 + t₀ i` with `|t₀| ≤ T < H`, the right-hand Green logarithms
are summable and their sum is bounded by three quarters of the full two-sided quadratic tail,
times the displayed translation factor, when all sites through `H` are central. -/
theorem translated_rightGreen_le_inverseHeightTail (χ : U𝔽) {t₀ T H : ℝ}
    (ht : |t₀| ≤ T) (hTH : T < H)
    (hc : ∀ z : Site χ, |z.val.im| ≤ H → z.val.re = 1 / 2) :
    let f := fun z : HeckeHalfPlaneJensen.RightSite χ ↦ (HeckeHalfPlaneJensen.order χ z.val : ℝ) *
      HalfPlaneJensen.greenKernel (z.val - (t₀ : ℂ) * I)
    Summable f ∧ (∑' z, f z) ≤ 3 / 4 * (H / (H - T)) ^ 2 * inverseHeightTail χ H 2 := by
  let C := (3 / 2 : ℝ) * (H / (H - T)) ^ 2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hH : 0 < H := (abs_nonneg t₀).trans_lt (ht.trans_lt hTH)
  obtain ⟨hr, hp⟩ := right_tail_pair hH (le_refl 2) hc
  let f (z : HeckeHalfPlaneJensen.RightSite χ) := (HeckeHalfPlaneJensen.order χ z.val : ℝ) *
    HalfPlaneJensen.greenKernel (z.val - (t₀ : ℂ) * I)
  have hsre (z : HeckeHalfPlaneJensen.RightSite χ) : z.val.re ≤ 1 :=
    (siteStrip (χ := χ) ⟨z.val, z.property.1⟩).2
  have hf (z : HeckeHalfPlaneJensen.RightSite χ) : 0 ≤ f z := by
    have hR : (z.val - (t₀ : ℂ) * I).re = z.val.re := by simp
    have hg := (HalfPlaneJensen.greenKernel_bounds (s := z.val - (t₀ : ℂ) * I)
      (hR.symm ▸ z.property.2.le) (hR.symm ▸ hsre z)).1
    rw [hR] at hg
    exact mul_nonneg (by exact_mod_cast z.property.1.le)
      ((div_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr z.property.2.le)) (by positivity)).trans hg)
  have hle (z : HeckeHalfPlaneJensen.RightSite χ) : f z ≤
      C * ((HeckeHalfPlaneJensen.order χ z.val : ℝ) / |z.val.im| ^ 2) := by
    have hg := HalfPlaneJensen.greenKernel_sub_imaginary_le_inv_sq z.property.2.le (hsre z)
      ht hTH (high_of_right hc z).le
    exact (mul_le_mul_of_nonneg_left hg (by exact_mod_cast z.property.1.le)).trans_eq (by dsimp [C]; ring)
  have hs := Summable.of_nonneg_of_le hf hle (hr.mul_left C)
  refine ⟨hs, ?_⟩
  have h := hs.tsum_le_tsum hle (hr.mul_left C)
  rw [tsum_mul_left] at h
  calc
    _ ≤ _ := h
    _ ≤ C * (inverseHeightTail χ H 2 / 2) := mul_le_mul_of_nonneg_left (by linarith only [hp]) hC
    _ = _ := by dsimp [C]; ring

/-- In the unshifted canonical Green mass each right-hand site and its distinct reflection
account for two copies in the full two-sided reciprocal-square tail. -/
theorem rightGreenMass_le_inverseHeightTail (χ : U𝔽) {H : ℝ} (hH : 0 < H)
    (hc : ∀ z : Site χ, |z.val.im| ≤ H → z.val.re = 1 / 2) :
    rightGreenMass χ ≤ 3 / 4 * inverseHeightTail χ H 2 := by
  have h := (translated_rightGreen_le_inverseHeightTail χ (t₀ := 0) (T := 0)
    (by simp) hH hc).2
  simpa [rightGreenMass, hH.ne'] using h

/-- For every positive strip half-width the sum of the absolute exterior samples is at
most the same Mellin envelope constant times the full high-ordinate tail. All occupied
sites at either edge are retained. -/
theorem absolute_exterior_le_inverseHeightTail (χ : U𝔽) (M : ℂ → ℂ)
    {k : ℕ} (hk : 2 ≤ k) {H W : ℝ} (hH : 0 < H) (hW : 0 ≤ W)
    (hc : ∀ z : Site χ, |z.val.im| ≤ H → z.val.re = 1 / 2)
    (hM : ∀ z : Site χ, |z.val.im| ^ k * ‖M z.val‖ ≤ W) {α : ℝ} (hα : 0 < α) :
    let f := fun z : {p : ℂ // 0 < HeckeHalfPlaneJensen.order χ p ∧ α ≤ |p.re - 1 / 2|} ↦
      ‖(HeckeHalfPlaneJensen.order χ z.val : ℂ) * M z.val‖
    HasSum f (∑' z, f z) ∧ (∑' z, f z) ≤ W * inverseHeightTail χ H k := by
  classical
  let X := {p : ℂ // 0 < HeckeHalfPlaneJensen.order χ p ∧ α ≤ |p.re - 1 / 2|}
  let i (z : X) : High(χ, H) := ⟨⟨z.val, z.property.1⟩, by
    by_contra! h
    have hc' := hc ⟨z.val, z.property.1⟩ h
    have hx := z.property.2
    change z.val.re = 1 / 2 at hc'
    rw [hc', sub_self, abs_zero] at hx
    exact hα.not_ge hx⟩
  have hi : Injective i := fun a b e ↦ Subtype.ext (congrArg (fun z : High(χ, H) ↦ z.val.val) e)
  let w (z : High(χ, H)) := W * ((multiplicity z.val : ℝ) / |z.val.val.im| ^ k)
  let f (z : X) := ‖(HeckeHalfPlaneJensen.order χ z.val : ℂ) * M z.val‖
  have hle (z : X) : f z ≤ w (i z) := by
    have hp := pow_pos (hH.trans (i z).property) k
    have hval : ‖M z.val‖ ≤ W / |z.val.im| ^ k := (le_div_iff₀ hp).mpr <| by
      rw [mul_comm]
      exact hM (i z).val
    have hm : 0 ≤ (HeckeHalfPlaneJensen.order χ z.val : ℝ) := by exact_mod_cast z.property.1.le
    dsimp only [f, w]
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hm, real_multiplicity]
    exact (mul_le_mul_of_nonneg_left hval hm).trans_eq (by dsimp only [i]; ring)
  have ht : Summable w := (summable_inverseHeightTail χ hH hk).mul_left W
  have hs : Summable f := Summable.of_nonneg_of_le (fun z ↦ norm_nonneg _) hle (ht.comp_injective hi)
  refine ⟨hs.hasSum, ?_⟩
  have hb := hs.tsum_le_tsum_of_inj i hi (fun z _ ↦ by dsimp only [w]; positivity) hle ht
  simpa only [w, tsum_mul_left, inverseHeightTail] using hb

end RiemannMasullo.HeckePoisson
