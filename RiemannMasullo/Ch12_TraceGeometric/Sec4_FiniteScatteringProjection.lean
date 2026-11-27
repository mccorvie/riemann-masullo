module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Module
public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-! # Finite scattering on the flat logarithmic Paley–Wiener level

Paper: (11.2.1.6), p. 488, and Theorem 12.4.1.1, pp. 514–517, Step III.
For a fixed angular block, a finite list of unramified Euler factors acts by
invertible geometric sums of log translations. Its actual flat orthogonal
projection is obtained by unitary scattering, not a similarity by these sums.
The logarithmic band is an almost-everywhere support condition in Mathlib's
Lebesgue L². Only the trivial full angular block has one additional Mellin
origin vector removed. This module does not identify the full adelic core or
claim any weighted trace limit. -/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped ComplexConjugate InnerProductSpace Topology

namespace RiemannMasullo.QuotientScattering

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (T A : H ≃L[ℂ] H)
variable (hA : A.toContinuousLinearMap = T.toContinuousLinearMap.adjoint)
variable (hn : ∀ x, A (T x) = T (A x))

/-- The equivalence `A` supplies the bounded inverse of the adjoint. Normality makes
`T ∘ A⁻¹` isometric, since `T` and its adjoint have the same pointwise norm. -/
def scatteringUnitary : H ≃ₗᵢ[ℂ] H where
  toLinearEquiv := A.symm.toLinearEquiv.trans T.toLinearEquiv
  norm_map' x := by
    let y := A.symm x
    have ha (z : H) : A z = T.toContinuousLinearMap.adjoint z :=
      DFunLike.congr_fun hA z
    have hi : inner ℂ (T y) (T y) = inner ℂ (A y) (A y) := calc
      _ = inner ℂ (A (T y)) y := by
        rw [ha (T y)]; exact (T.toContinuousLinearMap.adjoint_inner_left y (T y)).symm
      _ = inner ℂ (T (A y)) y := by rw [hn]
      _ = inner ℂ (A y) (A y) := by
        rw [ha y]; exact (T.toContinuousLinearMap.adjoint_inner_right _ y).symm
    change ‖T y‖ = ‖x‖
    calc
      _ = ‖A y‖ := by simp only [norm_eq_sqrt_re_inner (𝕜 := ℂ), hi]
      _ = ‖x‖ := by rw [show A y = x from A.apply_symm_apply x]

variable (E : Submodule ℂ H)
variable (hstable : ∀ x ∈ E, A x ∈ E) (hinv : ∀ x ∈ E, A.symm x ∈ E)
include hstable hinv

/-- The actual scattered subspace equals the isometric image, not just an
isomorphic copy of that image. -/
theorem scattering_map_eq : E.map T.toLinearEquiv.toLinearMap =
    E.map (scatteringUnitary T A hA hn).toLinearEquiv.toLinearMap := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨A x, hstable x hx, ?_⟩
    change T (A.symm (A x)) = T x
    rw [A.symm_apply_apply]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨A.symm x, hinv x hx, rfl⟩

variable [hproj : E.HasOrthogonalProjection]
include hA hn hproj

/-- Closedness/projection existence transfers along the scattering identity. -/
theorem scattering_hasProjection : (E.map T.toLinearEquiv.toLinearMap).HasOrthogonalProjection := by
  rw [scattering_map_eq T A hA hn E hstable hinv]
  infer_instance

/-- Conjugation formula for Mathlib's ambient-valued orthogonal projection. -/
theorem scattering_starProjection (x : H) :
    letI := scattering_hasProjection T A hA hn E hstable hinv
    (E.map T.toLinearEquiv.toLinearMap).starProjection x =
      (scatteringUnitary T A hA hn) (E.starProjection ((scatteringUnitary T A hA hn).symm x)) := by
  let U := scatteringUnitary T A hA hn
  have transfer (F : Submodule ℂ H) (he : F = E.map U.toLinearEquiv.toLinearMap)
      [F.HasOrthogonalProjection] : F.starProjection x = U (E.starProjection (U.symm x)) := by
    subst F
    exact Submodule.starProjection_map_apply U E x
  let := scattering_hasProjection T A hA hn E hstable hinv
  exact transfer _ (scattering_map_eq T A hA hn E hstable hinv)

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The Neumann equivalence on the ambient Hilbert space. -/
def geometricFactor (L : H →L[ℂ] H) (h : ‖L‖ < 1) : H ≃L[ℂ] H :=
  ContinuousLinearEquiv.ofUnit (Units.oneSub L h)

@[simp] theorem geometricFactor_apply (L : H →L[ℂ] H) (h : ‖L‖ < 1) (x : H) :
    geometricFactor L h x = x - L x := rfl

/-- Convergence in operator norm, not only convergence on individual vectors. -/
theorem geometricFactor_hasSum (L : H →L[ℂ] H) (h : ‖L‖ < 1) :
    HasSum (fun n : ℕ => L ^ n) (geometricFactor L h).symm.toContinuousLinearMap := by
  change HasSum (fun n : ℕ => L ^ n) (∑' n : ℕ, L ^ n)
  exact (summable_geometric_of_norm_lt_one h).hasSum

/-- Closedness is needed only for the inverse direction. -/
theorem geometricFactor_preserves (E : Submodule ℂ H) (hE : IsClosed (E : Set H))
    (L : H →L[ℂ] H) (h : ‖L‖ < 1) (hL : ∀ x ∈ E, L x ∈ E) :
    (∀ x ∈ E, geometricFactor L h x ∈ E) ∧
      (∀ x ∈ E, (geometricFactor L h).symm x ∈ E) := by
  refine ⟨fun x hx => E.sub_mem hx (hL x hx), ?_⟩
  intro x hx
  have hp (n : ℕ) : (L ^ n) x ∈ E := by
    induction n with
    | zero => simpa using hx
    | succ n ih => rw [pow_succ']; exact hL _ ih
  have hs : HasSum (fun n : ℕ => (L ^ n) x) ((geometricFactor L h).symm x) :=
    (ContinuousLinearMap.apply ℂ H x).hasSum (geometricFactor_hasSum L h)
  exact hE.mem_of_tendsto hs (Filter.Eventually.of_forall fun s => E.sum_mem fun n _ => hp n)

/-- Ordered finite compositions preserve the ray subspace in both directions;
no commutation of the factors is required. -/
theorem geometricProduct_preserves (E : Submodule ℂ H) (fs : List (H ≃L[ℂ] H))
    (hf : ∀ f ∈ fs, (∀ x ∈ E, f x ∈ E) ∧ (∀ x ∈ E, f.symm x ∈ E)) :
    (∀ x ∈ E, fs.prod x ∈ E) ∧ (∀ x ∈ E, fs.prod.symm x ∈ E) := by
  induction fs with
  | nil => exact ⟨fun _ hx => hx, fun _ hx => hx⟩
  | cons f fs ih =>
    obtain ⟨h₁, h₂⟩ := hf f (by simp)
    obtain ⟨h₃, h₄⟩ := ih (fun g hg => hf g (List.mem_cons_of_mem _ hg))
    simp only [List.prod_cons]
    exact ⟨fun x hx => h₁ _ (h₃ x hx), fun x hx => h₄ _ (h₂ x hx)⟩

local notation "LogFrequencyL2" => Lp ℂ 2 (volume : Measure ℝ)

/-- Pullback along a measure-preserving real translation. -/
def shift (t : ℝ) : LogFrequencyL2 →ₗᵢ[ℂ] LogFrequencyL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (· + t) (measurePreserving_add_right volume t)

private theorem shift_ae (t : ℝ) (f : LogFrequencyL2) :
    ⇑(shift t f) =ᵐ[volume] fun x => f (x + t) :=
  Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume t)

theorem shift_cancel (s t : ℝ) (h : s + t = 0) (f : LogFrequencyL2) :
    shift s (shift t f) = f := by
  apply Lp.ext
  filter_upwards [shift_ae s (shift t f),
    (measurePreserving_add_right volume s).quasiMeasurePreserving.ae (shift_ae t f)] with x hx hy
  change shift s (shift t f) x = shift t f (x + s) at hx
  change shift t f (x + s) = f ((x + s) + t) at hy
  simpa only [add_assoc, h, add_zero] using hx.trans hy

/-- Translation in log frequency, with the pullback convention `f (x + t)`. -/
def tau (t : ℝ) : LogFrequencyL2 ≃ₗᵢ[ℂ] LogFrequencyL2 where
  toFun := shift t
  invFun := shift (-t)
  left_inv := shift_cancel (-t) t (neg_add_cancel t)
  right_inv := shift_cancel t (-t) (add_neg_cancel t)
  map_add' := (shift t).map_add
  map_smul' := (shift t).map_smul
  norm_map' := (shift t).norm_map

theorem tau_ae (t : ℝ) (f : LogFrequencyL2) :
    ⇑(tau t f) =ᵐ[volume] fun x => f (x + t) := shift_ae t f

@[simp] theorem tau_symm_apply (t : ℝ) (f : LogFrequencyL2) :
    (tau t).symm f = tau (-t) f := rfl

/-- Functions supported, up to a volume-null set, on `(-∞, b]`. -/
def halfLine (b : ℝ) : ClosedSubmodule ℂ LogFrequencyL2 where
  carrier := {f | ∀ᵐ x ∂volume, b < x → f x = 0}
  zero_mem' := by
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x hx using fun _ => hx
  add_mem' := by
    intro f g hf hg
    filter_upwards [hf, hg, Lp.coeFn_add f g] with x hx hy hz
    intro h
    simpa only [Pi.add_apply, hx h, hy h, add_zero] using hz
  smul_mem' := by
    intro c f hf
    filter_upwards [hf, Lp.coeFn_smul c f] with x hx hz
    intro h
    simpa only [Pi.smul_apply, hx h, smul_zero] using hz
  isClosed' := by
    apply IsSeqClosed.isClosed
    intro f g hf hlim
    obtain ⟨φ, -, hφ⟩ := (tendstoInMeasure_of_tendsto_Lp hlim).exists_seq_tendsto_ae
    have hall : ∀ᵐ x ∂volume, ∀ n : ℕ, b < x → f n x = 0 :=
      ae_all_iff.mpr hf
    filter_upwards [hall, hφ] with x hx hconv
    intro h
    apply tendsto_nhds_unique hconv
    have heq : (fun n => f (φ n) x) = fun _ : ℕ => (0 : ℂ) := funext fun n => hx (φ n) h
    rw [heq]
    exact tendsto_const_nhds

theorem mem_halfLine_iff (b : ℝ) (f : LogFrequencyL2) :
    f ∈ halfLine b ↔ ∀ᵐ x ∂volume, b < x → f x = 0 := Iff.rfl

theorem tau_mem_halfLine {t b : ℝ} (ht : 0 ≤ t) {f : LogFrequencyL2}
    (hf : f ∈ halfLine b) : tau t f ∈ halfLine b := by
  rw [mem_halfLine_iff] at hf ⊢
  filter_upwards [tau_ae t f, (measurePreserving_add_right volume t).quasiMeasurePreserving.ae hf]
    with x hx hy
  intro h
  exact hx.trans (hy (lt_of_lt_of_le h (le_add_of_nonneg_right ht)))

/-- Mellin radial origin mode, cut off at log-radius `b`. -/
def originProfile (b : ℝ) : ℝ → ℂ :=
  (Iic b).indicator fun x => (Real.exp ((x - b) / 2) : ℂ)

theorem originProfile_memLp (b : ℝ) : MemLp (originProfile b) 2 volume := by
  have hc : Continuous (fun x : ℝ => (Real.exp ((x - b) / 2) : ℂ)) := by fun_prop
  apply (memLp_two_iff_integrable_sq_norm
    (hc.aestronglyMeasurable.indicator measurableSet_Iic)).2
  have hi : Integrable ((Iic b).indicator (fun x : ℝ ↦ Real.exp (-b) * Real.exp x))
      (volume : Measure ℝ) :=
    (integrable_indicator_iff measurableSet_Iic).2 ((integrableOn_exp_Iic b).const_mul (Real.exp (-b)))
  apply hi.congr
  filter_upwards with x
  by_cases hx : x ∈ Iic b
  · simp only [indicator_of_mem hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), pow_two, ← Real.exp_add]
    congr 1
    ring
  · simp [hx]

def originVector (b : ℝ) : LogFrequencyL2 := (originProfile_memLp b).toLp (originProfile b)

theorem originVector_ae (b : ℝ) : ⇑(originVector b) =ᵐ[volume] originProfile b :=
  (originProfile_memLp b).coeFn_toLp

def polarSubspace (b : ℝ) : ClosedSubmodule ℂ LogFrequencyL2 :=
  halfLine b ⊓ { toSubmodule := (innerSL ℂ (originVector b)).ker
                 isClosed' := (innerSL ℂ (originVector b)).isClosed_ker }

theorem mem_polarSubspace_iff (b : ℝ) (f : LogFrequencyL2) :
    f ∈ polarSubspace b ↔ f ∈ halfLine b ∧ inner ℂ (originVector b) f = 0 := Iff.rfl

/-- The inverse translate restricts to a scalar multiple on the entire source half-line. -/
theorem inverseTranslate_origin_ae {b t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ x ∂volume, x ≤ b → tau (-t) (originVector b) x =
      (Real.exp (-t / 2) : ℂ) * originVector b x := by
  filter_upwards [tau_ae (-t) (originVector b), originVector_ae b,
    (measurePreserving_add_right volume (-t)).quasiMeasurePreserving.ae (originVector_ae b)]
    with x hx hy hz
  intro h
  change originVector b (x + -t) = originProfile b (x + -t) at hz
  have h' : x + -t ∈ Iic b := by change x + -t ≤ b; linarith
  rw [hx, hz, hy]
  simp only [originProfile, indicator_of_mem h', indicator_of_mem (show x ∈ Iic b from h),
    ← Complex.ofReal_mul, ← Real.exp_add]
  congr 2
  ring

theorem tau_mem_polarSubspace {t b : ℝ} (ht : 0 ≤ t) {f : LogFrequencyL2}
    (hf : f ∈ polarSubspace b) : tau t f ∈ polarSubspace b := by
  obtain ⟨hs, ho⟩ := (mem_polarSubspace_iff b f).mp hf
  apply (mem_polarSubspace_iff b _).2
  refine ⟨tau_mem_halfLine ht hs, ?_⟩
  let c : ℂ := Real.exp (-t / 2)
  calc
    inner ℂ (originVector b) (tau t f) = inner ℂ (tau (-t) (originVector b)) f := by
      simpa using ((tau t).symm.inner_map_eq_flip (originVector b) f).symm
    _ = inner ℂ (c • originVector b) f := by
      rw [L2.inner_def, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [inverseTranslate_origin_ae (b := b) ht, (mem_halfLine_iff b f).mp hs,
        Lp.coeFn_smul c (originVector b)] with x hx hy hz
      by_cases hb : x ≤ b
      · rw [hx hb, hz]; rfl
      · simp [hy (lt_of_not_ge hb)]
    _ = 0 := by rw [inner_smul_left, ho, mul_zero]

/-- Both closed source spaces carry the ambient-valued continuous orthogonal projector. -/
def logSourceProjection (E : ClosedSubmodule ℂ LogFrequencyL2) :
    LogFrequencyL2 →L[ℂ] LogFrequencyL2 := by
  letI : CompleteSpace E.toSubmodule := inferInstanceAs (CompleteSpace E)
  exact E.toSubmodule.starProjection

theorem logSourceProjection_range (E : ClosedSubmodule ℂ LogFrequencyL2) :
    (logSourceProjection E).range = E.toSubmodule := by
  let : CompleteSpace E.toSubmodule := inferInstanceAs (CompleteSpace E)
  exact E.toSubmodule.range_starProjection

/-- The exponential boundary vector is normalized for Lebesgue log measure. -/
theorem inner_originVector_self (b : ℝ) :
    inner ℂ (originVector b) (originVector b) = 1 := by
  let g := (Iic b).indicator (fun x : ℝ ↦ Real.exp (-b) * Real.exp x)
  have hi : (∫ x, g x) = 1 := by
    dsimp only [g]
    rw [integral_indicator measurableSet_Iic, integral_const_mul,
      integral_exp_Iic, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  rw [L2.inner_def]
  calc
    _ = ∫ x, (g x : ℂ) := by
      apply integral_congr_ae
      filter_upwards [originVector_ae b] with x hx
      rw [hx]
      by_cases hxb : x ∈ Iic b
      · simp only [g, originProfile, indicator_of_mem hxb, RCLike.inner_apply, Complex.conj_ofReal,
          ← Complex.ofReal_mul, ← Real.exp_add]
        congr 2
        ring
      · simp [g, originProfile, hxb]
    _ = 1 := by rw [integral_complex_ofReal, hi, Complex.ofReal_one]

theorem originVector_mem_halfLine (b : ℝ) : originVector b ∈ halfLine b := by
  apply (mem_halfLine_iff b _).2
  filter_upwards [originVector_ae b] with x hx h
  rw [hx, originProfile, indicator_of_notMem (not_le.mpr h)]

/-- The trivial angular type removes just one flat boundary line. -/
theorem polarSourceProjection_apply (b : ℝ) (f : LogFrequencyL2) :
    logSourceProjection (polarSubspace b) f =
      logSourceProjection (halfLine b) f - inner ℂ (originVector b) f • originVector b := by
  let : CompleteSpace (polarSubspace b).toSubmodule := inferInstanceAs (CompleteSpace (polarSubspace b))
  let : CompleteSpace (halfLine b).toSubmodule := inferInstanceAs (CompleteSpace (halfLine b))
  let S := (halfLine b).toSubmodule
  let P := (polarSubspace b).toSubmodule
  let h := originVector b
  have hh : h ∈ S := originVector_mem_halfLine b
  have hs (y : LogFrequencyL2) (hy : y ∈ S) :
      inner ℂ y (S.starProjection f) = inner ℂ y f := by
    have hz := (Submodule.mem_orthogonal _ _).1 (S.sub_starProjection_mem_orthogonal f) y hy
    rw [inner_sub_right, sub_eq_zero] at hz
    exact hz.symm
  change P.starProjection f = S.starProjection f - inner ℂ h f • h
  apply Submodule.eq_starProjection_of_mem_orthogonal
  · apply (mem_polarSubspace_iff b _).2
    exact ⟨S.sub_mem (S.starProjection_apply_mem f) (S.smul_mem _ hh), by
      rw [inner_sub_right, hs h hh, inner_smul_right, inner_originVector_self, mul_one, sub_self]⟩
  · apply (Submodule.mem_orthogonal _ _).2
    intro y hy
    obtain ⟨hyS, hyh⟩ := (mem_polarSubspace_iff b y).1 hy
    have hz : inner ℂ y h = 0 := inner_eq_zero_symm.mp hyh
    simp only [inner_sub_right, inner_smul_right, hs y hyS, hz, mul_zero, sub_zero, sub_self]

theorem tau_add_apply (s t : ℝ) (x : LogFrequencyL2) : tau s (tau t x) = tau (s+t) x := by
  apply Lp.ext
  filter_upwards [tau_ae s (tau t x), (measurePreserving_add_right volume s).quasiMeasurePreserving.ae (tau_ae t x), tau_ae (s+t) x] with y h₁ h₂ h₃
  change tau t x (y+s) = x ((y+s)+t) at h₂
  exact h₁.trans (h₂.trans (by simpa only [add_assoc] using h₃.symm))

@[simp] theorem tau_zero_apply (x : LogFrequencyL2) : tau 0 x = x := by
  apply Lp.ext
  simpa using tau_ae 0 x

def tauOp (t : ℝ) : LogFrequencyL2 →L[ℂ] LogFrequencyL2 := (tau t : LogFrequencyL2 →L[ℂ] LogFrequencyL2)

theorem tauOp_adjoint (t : ℝ) : (tauOp t).adjoint = tauOp (-t) := by
  have hs (x : LogFrequencyL2) : tau (-t) (tau t x) = x := by
    rw [tau_add_apply, neg_add_cancel, tau_zero_apply]
  apply ((ContinuousLinearMap.eq_adjoint_iff _ _).2 ?_).symm
  intro x y
  change inner ℂ (tau (-t) x) y = inner ℂ x (tau t y)
  rw [← (tau (-t)).inner_map_map x (tau t y), hs]

theorem tauOp_commute (s t : ℝ) : Commute (tauOp s) (tauOp t) := by
  apply ContinuousLinearMap.ext
  intro x
  change tau s (tau t x) = tau t (tau s x)
  rw [tau_add_apply, tau_add_apply, add_comm]

structure ShiftFactor where
  coeff : ℂ
  time : ℝ
  small : ‖coeff‖ < 1

namespace ShiftFactor

def dual (p : ShiftFactor) : ShiftFactor := ⟨conj p.coeff, -p.time, by simpa using p.small⟩

theorem smallOp (p : ShiftFactor) : ‖p.coeff • tauOp p.time‖ < 1 := by
  have ht : ‖tauOp p.time‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by
    change ‖tau p.time x‖ ≤ 1 * ‖x‖
    rw [(tau p.time).norm_map, one_mul])
  rw [norm_smul]
  exact ((mul_le_mul_of_nonneg_left ht (norm_nonneg _)).trans_lt (by simpa using p.small))

def factor (p : ShiftFactor) : LogFrequencyL2 ≃L[ℂ] LogFrequencyL2 := geometricFactor _ p.smallOp

theorem factor_clm (p : ShiftFactor) : p.factor.toContinuousLinearMap = 1 - p.coeff • tauOp p.time := rfl

theorem factor_adjoint (p : ShiftFactor) : p.dual.factor.toContinuousLinearMap = p.factor.toContinuousLinearMap.adjoint := by
  have h : (p.coeff • tauOp p.time).adjoint = conj p.coeff • (tauOp p.time).adjoint :=
    star_smul p.coeff (tauOp p.time)
  simp [factor_clm, dual, ContinuousLinearMap.adjoint_one, h, tauOp_adjoint]

theorem factor_commute (p q : ShiftFactor) : Commute p.factor q.factor := by
  apply ContinuousLinearEquiv.ext
  funext x
  change p.factor (q.factor x) = q.factor (p.factor x)
  simp only [factor, geometricFactor_apply, smul_apply, map_sub, map_smul, tauOp,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    smul_sub, smul_smul, tau_add_apply]
  rw [mul_comm q.coeff p.coeff, add_comm q.time p.time]
  abel

end ShiftFactor

def shiftProduct (ps : List ShiftFactor) := (ps.map ShiftFactor.factor).prod

def dualShiftProduct (ps : List ShiftFactor) := shiftProduct (ps.reverse.map ShiftFactor.dual)

theorem shiftProduct_commute (ps qs : List ShiftFactor) : Commute (shiftProduct ps) (shiftProduct qs) := by
  apply Commute.list_prod_left
  intro f hf
  obtain ⟨p, _, rfl⟩ := List.mem_map.mp hf
  apply Commute.list_prod_right
  intro g hg
  obtain ⟨q, _, rfl⟩ := List.mem_map.mp hg
  exact p.factor_commute q

theorem shiftProduct_adjoint (ps : List ShiftFactor) : (dualShiftProduct ps).toContinuousLinearMap = (shiftProduct ps).toContinuousLinearMap.adjoint := by
  induction ps with
  | nil => exact ContinuousLinearMap.adjoint_one.symm
  | cons p ps ih =>
    simp only [dualShiftProduct, shiftProduct, List.reverse_cons, List.map_append, List.map_cons, List.map_nil, List.prod_append, List.prod_cons, List.prod_nil, mul_one] at ⊢
    change (dualShiftProduct ps).toContinuousLinearMap.comp p.dual.factor.toContinuousLinearMap = (p.factor.toContinuousLinearMap.comp (shiftProduct ps).toContinuousLinearMap).adjoint
    rw [ContinuousLinearMap.adjoint_comp, ih, p.factor_adjoint]

theorem shiftProduct_inverse_adjoint (ps : List ShiftFactor) : (dualShiftProduct ps).symm.toContinuousLinearMap = (shiftProduct ps).symm.toContinuousLinearMap.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro x y
  obtain ⟨u, rfl⟩ := (dualShiftProduct ps).surjective x
  obtain ⟨v, rfl⟩ := (shiftProduct ps).surjective y
  change inner ℂ ((dualShiftProduct ps).symm ((dualShiftProduct ps) u)) ((shiftProduct ps) v) = inner ℂ ((dualShiftProduct ps) u) ((shiftProduct ps).symm ((shiftProduct ps) v))
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  exact ((ContinuousLinearMap.eq_adjoint_iff _ _).1 (shiftProduct_adjoint ps) u v).symm

/-- The band with or without the Mellin origin condition. The Boolean describes the
full angular character, including its norm-one valuation character. -/
def logBand (polar : Bool) (b : ℝ) : ClosedSubmodule ℂ LogFrequencyL2 :=
  if polar then polarSubspace b else halfLine b

theorem tau_mem_logBand {polar : Bool} {b t : ℝ} (ht : 0 ≤ t) {f : LogFrequencyL2}
    (hf : f ∈ logBand polar b) : tau t f ∈ logBand polar b := by
  cases polar
  · exact tau_mem_halfLine ht hf
  · exact tau_mem_polarSubspace ht hf

/-- Each dual dilation difference and its norm-convergent inverse preserve the actual
closed band, including its polar constraint when present. -/
theorem dualProduct_preserves_logBand (ps : List ShiftFactor) (ht : ∀ p ∈ ps, p.time ≤ 0)
    (polar : Bool) (b : ℝ) :
    (∀ f ∈ logBand polar b, dualShiftProduct ps f ∈ logBand polar b) ∧
    (∀ f ∈ logBand polar b, (dualShiftProduct ps).symm f ∈ logBand polar b) := by
  apply geometricProduct_preserves (logBand polar b).toSubmodule
  intro q hq
  obtain ⟨q', hq', hqeq⟩ := List.mem_map.mp hq
  obtain ⟨p, hp, hpeq⟩ := List.mem_map.mp hq'
  rw [← hqeq, ← hpeq]
  apply geometricFactor_preserves (logBand polar b).toSubmodule (logBand polar b).isClosed'
  intro f hf
  have htime : 0 ≤ p.dual.time := neg_nonneg.mpr (ht p (List.mem_reverse.mp hp))
  exact (logBand polar b).toSubmodule.smul_mem p.dual.coeff (tau_mem_logBand htime hf)

/-- At an unramified finite place `q` is the residue cardinality and `γ` is the
phase of its valuation section. The adjoint translates into the left band. -/
def localEulerShift (q : ℝ) (hq : 1 < q) (γ : ℂ) (hγ : ‖γ‖ = 1) : ShiftFactor where
  coeff := γ * (Real.exp (-Real.log q / 2) : ℂ)
  time := -Real.log q
  small := by
    rw [norm_mul, hγ, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    apply Real.exp_lt_one_iff.mpr
    linarith [Real.log_pos hq]

theorem localEulerShift_time_nonpos (q : ℝ) (hq : 1 < q) (γ : ℂ) (hγ : ‖γ‖ = 1) :
    (localEulerShift q hq γ hγ).time ≤ 0 := neg_nonpos.mpr (Real.log_pos hq).le

/-- Finite geometric scattering and its genuine adjoint on the flat log Hilbert space. -/
def logScattering (ps : List ShiftFactor) : LogFrequencyL2 ≃L[ℂ] LogFrequencyL2 :=
  (shiftProduct ps).symm

def logScatteringAdjoint (ps : List ShiftFactor) : LogFrequencyL2 ≃L[ℂ] LogFrequencyL2 :=
  (dualShiftProduct ps).symm

theorem logScattering_adjoint (ps : List ShiftFactor) :
    (logScatteringAdjoint ps).toContinuousLinearMap = (logScattering ps).toContinuousLinearMap.adjoint :=
  shiftProduct_inverse_adjoint ps

theorem logScattering_normal (ps : List ShiftFactor) (f : LogFrequencyL2) :
    logScatteringAdjoint ps (logScattering ps f) = logScattering ps (logScatteringAdjoint ps f) := by
  have h := shiftProduct_commute (ps.reverse.map ShiftFactor.dual) ps
  exact DFunLike.congr_fun h.inv_inv.eq f

/-- The unitary that replaces nonunitary finite scattering on the constrained band. -/
def logScatteringUnitary (ps : List ShiftFactor) : LogFrequencyL2 ≃ₗᵢ[ℂ] LogFrequencyL2 :=
  scatteringUnitary (logScattering ps) (logScatteringAdjoint ps)
    (logScattering_adjoint ps) (logScattering_normal ps)

/-- The actual closed scattered band is the image under the bounded geometric product. -/
def scatteredLogBand (ps : List ShiftFactor) (polar : Bool) (b : ℝ) :
    Submodule ℂ LogFrequencyL2 :=
  (logBand polar b).toSubmodule.map (logScattering ps).toLinearEquiv.toLinearMap

theorem scatteredLogBand_hasProjection (ps : List ShiftFactor) (ht : ∀ p ∈ ps, p.time ≤ 0)
    (polar : Bool) (b : ℝ) : (scatteredLogBand ps polar b).HasOrthogonalProjection := by
  let : CompleteSpace (logBand polar b).toSubmodule := inferInstanceAs (CompleteSpace (logBand polar b))
  obtain ⟨h, hi⟩ := dualProduct_preserves_logBand ps ht polar b
  exact scattering_hasProjection (logScattering ps) (logScatteringAdjoint ps)
    (logScattering_adjoint ps) (logScattering_normal ps) (logBand polar b).toSubmodule hi h

/-- The geometric product itself is not unitary. Its actual orthogonal band
projector is conjugate by `T (T*)⁻¹`, not by `T`. -/
theorem scatteredLogBand_starProjection (ps : List ShiftFactor) (ht : ∀ p ∈ ps, p.time ≤ 0)
    (polar : Bool) (b : ℝ) (f : LogFrequencyL2) :
    letI := scatteredLogBand_hasProjection ps ht polar b
    (scatteredLogBand ps polar b).starProjection f =
      logScatteringUnitary ps (logSourceProjection (logBand polar b) ((logScatteringUnitary ps).symm f)) := by
  let : CompleteSpace (logBand polar b).toSubmodule := inferInstanceAs (CompleteSpace (logBand polar b))
  obtain ⟨h, hi⟩ := dualProduct_preserves_logBand ps ht polar b
  exact scattering_starProjection (logScattering ps) (logScatteringAdjoint ps)
    (logScattering_adjoint ps) (logScattering_normal ps) (logBand polar b).toSubmodule hi h f

/-- After any finite choice of unramified factors, the difference between the full
and polar-free projectors remains the rank-one projector on the scattered origin. -/
theorem scatteredLogBand_polar_starProjection (ps : List ShiftFactor)
    (ht : ∀ p ∈ ps, p.time ≤ 0) (b : ℝ) (f : LogFrequencyL2) :
    letI := scatteredLogBand_hasProjection ps ht true b
    letI := scatteredLogBand_hasProjection ps ht false b
    let e := logScatteringUnitary ps (originVector b)
    (scatteredLogBand ps true b).starProjection f =
      (scatteredLogBand ps false b).starProjection f - inner ℂ e f • e := by
  let : (scatteredLogBand ps true b).HasOrthogonalProjection :=
    scatteredLogBand_hasProjection ps ht true b
  let : (scatteredLogBand ps false b).HasOrthogonalProjection :=
    scatteredLogBand_hasProjection ps ht false b
  rw [scatteredLogBand_starProjection ps ht true b f,
    scatteredLogBand_starProjection ps ht false b f]
  simp only [logBand, ↓reduceIte, Bool.false_eq_true, polarSourceProjection_apply,
    map_sub, map_smul]
  rw [← LinearIsometryEquiv.inner_map_map (logScatteringUnitary ps),
    LinearIsometryEquiv.apply_symm_apply]

end RiemannMasullo.QuotientScattering
