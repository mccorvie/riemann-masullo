module

public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import RiemannMasullo.External.FermatDixmierMalliavin.OneParameter

/-! Compact smooth convolution factorization on elementary abelian Lie groups.

The one-parameter factorization is iterated along real coordinates. A compactly
supported partition of unity lifts torus tests to their real cover; periodization
then sends convolutions back to the quotient. Compact support in discrete directions
reduces the last step to a finite sum of single fibers. -/

@[expose] public noncomputable section

open Set Function Filter MeasureTheory
open scoped Topology

namespace RiemannMasullo

namespace DixmierMalliavin.Torus

/-- The real cover of a Euclidean factor times an indexed unit torus. -/
def cover {E ι : Type*} (x : E × (ι → ℝ)) : E × UnitAddTorus ι :=
  (x.1, fun i ↦ x.2 i)

end DixmierMalliavin.Torus

namespace DixmierMalliavin

/-- Compactly supported two-term factorization along one Euclidean coordinate. -/
private theorem exists_coordinate_factorization {ι : Type*} [Fintype ι] [DecidableEq ι]
    (i : ι) (ε : ℝ) (hε : 0 < ε) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ (g : (ι → ℝ) → ℂ) (k l : ℝ → ℂ), ContDiff ℝ (⊤ : ℕ∞) g ∧
      tsupport g ⊆ tsupport f ∧ ContDiff ℝ (⊤ : ℕ∞) k ∧ ContDiff ℝ (⊤ : ℕ∞) l ∧
      tsupport k ⊆ Icc (-ε) ε ∧ tsupport l ⊆ Icc (-ε) ε ∧
      ∀ x, f x = (∫ t : ℝ, k t * g (x - t • Pi.single i (1 : ℝ))) +
        ∫ t : ℝ, l t * f (x - t • Pi.single i (1 : ℝ)) := by
  classical
  let E (x : ι → ℝ) : ι → ℝ := fun j ↦ Real.exp (x j)
  let L (x : ι → ℝ) : ι → ℝ := fun j ↦ Real.log (x j)
  let Φ (y : ι → ℝ) := if ∀ j, 0 < y j then f (L y) else 0
  have hE : ContDiff ℝ (⊤ : ℕ∞) E := contDiff_pi.mpr fun j ↦
    Real.contDiff_exp.comp (contDiff_apply ℝ _ j)
  have hEL (y : ι → ℝ) (h : ∀ j, 0 < y j) : E (L y) = y :=
    funext fun j ↦ Real.exp_log (h j)
  have hLE (x : ι → ℝ) : L (E x) = x := funext fun j ↦ Real.log_exp (x j)
  have hpos (x : ι → ℝ) : ∀ j, 0 < E x j := fun j ↦ Real.exp_pos _
  have hΦE (x : ι → ℝ) : Φ (E x) = f x := by simp [Φ, hpos, hLE]
  have hK := hc.isCompact.image hE.continuous
  have hs : tsupport Φ ⊆ E '' tsupport f := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    by_cases h : ∀ j, 0 < y j
    · exact ⟨L y, subset_tsupport f (by simpa [Φ, h, mem_support] using hy), hEL y h⟩
    · exact ((mem_support.mp hy) (ite_eq_right h)).elim
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases h : ∀ j, 0 < y j
    · have hL : ContDiffAt ℝ (⊤ : ℕ∞) L y := contDiffAt_pi.mpr fun j ↦
        (Real.contDiffAt_log.mpr (h j).ne').comp y (contDiff_apply ℝ _ j).contDiffAt
      apply (hf.contDiffAt.comp y hL).congr_of_eventuallyEq
      have hp : ∀ᶠ z : ι → ℝ in 𝓝 y, ∀ j, 0 < z j := eventually_all.mpr fun j ↦
        (continuous_apply j).continuousAt.eventually (lt_mem_nhds (h j))
      exact hp.mono fun _ hz ↦ ite_eq_left hz
    · have hy : y ∉ tsupport Φ := fun hy ↦ by
        obtain ⟨x, _, rfl⟩ := hs hy
        exact h (hpos x)
      exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)
  let X : ι → ℝ := Pi.single i 1
  obtain ⟨G, k, l, hG, hsG, hk, hl, hsk, hsl, heq⟩ :=
    _root_.DixmierMalliavin.exists_eq_integral_mul_comp_mul_exp_smul_add (-X) ε hε Φ hΦ
      (hK.of_isClosed_subset (isClosed_tsupport _) hs)
  have hflow (x : ι → ℝ) (t : ℝ) : E x * NormedSpace.exp (t • -X) = E (x - t • X) := by
    funext j
    simp only [Pi.mul_apply, Pi.coe_exp, ← Real.exp_eq_exp_ℝ, E, smul_neg, sub_eq_add_neg,
      Pi.add_apply, Real.exp_add]
  refine ⟨G ∘ E, k, l, hG.comp hE, ?_, hk, hl, hsk, hsl, ?_⟩
  · apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    obtain ⟨y, hy, he⟩ := hs (hsG (subset_tsupport G (show E x ∈ support G from hx)))
    have hxy : y = x := by simpa only [hLE] using congrArg L he
    exact hxy ▸ hy
  · intro x
    simpa only [hflow, hΦE, comp_apply, X] using heq (E x)

end DixmierMalliavin

open MeasureTheory
open scoped ContDiff BigOperators

namespace DixmierMalliavin.Euclidean

private structure Test (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  val : E → ℂ
  smooth : ContDiff ℝ ∞ val
  compact : HasCompactSupport val

variable {A B X : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Multiply the two independent smooth kernels; compactness on just one axis
would not suffice here. -/
private def tensor (k : Test A) (l : Test B) : Test (A × B) where
  val z := k.val z.1 * l.val z.2
  smooth := (k.smooth.comp contDiff_fst).mul (l.smooth.comp contDiff_snd)
  compact := by
    apply HasCompactSupport.intro (k.compact.prod l.compact)
    intro z hz
    by_cases h : z.1 ∈ tsupport k.val
    · have h' : z.2 ∉ tsupport l.val := fun h' => hz ⟨h, h'⟩
      simp [image_eq_zero_of_notMem_tsupport h']
    · simp [image_eq_zero_of_notMem_tsupport h]

variable [MeasureSpace A] [MeasureSpace B]

private def partialConv (p : A → X) (k : Test A) (g : Test X) (x : X) : ℂ :=
  ∫ a, k.val a * g.val (x - p a)

/-- Coordinate set `A` factors arbitrary ambient functions, not just pure tensors. -/
private def Factors (p : A → X) : Prop := ∀ f : Test X,
  ∃ (I : Type) (_ : Fintype I) (k : I → Test A) (g : I → Test X),
    ∀ x, f.val x = ∑ i, partialConv p (k i) (g i) x

/-- In particular the second summand may retain `f` itself. -/
private theorem factors_of_two (p : A → X)
    (h : ∀ f : Test X, ∃ (k l : Test A) (g : Test X), ∀ x,
      f.val x = partialConv p k g x + partialConv p l f x) : Factors p := by
  intro f
  obtain ⟨k, l, g, he⟩ := h f
  refine ⟨Bool, inferInstance, (fun b => if b then l else k),
    (fun b => if b then f else g), fun x => ?_⟩
  simpa [Fintype.sum_bool, add_comm] using he x

variable [BorelSpace A] [BorelSpace B] [SecondCountableTopology A] [SecondCountableTopology B]
  [IsLocallyFiniteMeasure (volume : Measure A)] [IsLocallyFiniteMeasure (volume : Measure B)]
  [SigmaFinite (volume : Measure A)] [SigmaFinite (volume : Measure B)]

private theorem product_integrable (p : A → X) (q : B → X) (hp : Continuous p)
    (hq : Continuous q) (k : Test A) (l : Test B) (g : Test X) (x : X) :
    Integrable (fun z : A × B => (k.val z.1 * l.val z.2) * g.val (x - p z.1 - q z.2))
      (volume.prod volume) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (tensor k l).smooth.continuous.mul (g.smooth.continuous.comp
      ((continuous_const.sub (hp.comp continuous_fst)).sub (hq.comp continuous_snd)))
  · exact (tensor k l).compact.mul_right

/-- Binary coordinate partition induction. Repeatedly apply this to single axes;
for a complete product with the coordinate injections the final shift is identity. -/
private theorem factors_prod (p : A → X) (q : B → X) (hp : Continuous p) (hq : Continuous q)
    (ha : Factors p) (hb : Factors q) : Factors (fun z : A × B => p z.1 + q z.2) := by
  classical
  intro f
  obtain ⟨I, instI, k, g, hf⟩ := ha f
  let : Fintype I := instI
  choose J instJ l v hg using fun i => hb (g i)
  let (i : I) : Fintype (J i) := instJ i
  refine ⟨(i : I) × J i, inferInstance, (fun s => tensor (k s.1) (l s.1 s.2)),
    (fun s => v s.1 s.2), fun x => ?_⟩
  rw [hf, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  let F (j : J i) (z : A × B) := ((k i).val z.1 * (l i j).val z.2) *
    (v i j).val (x - p z.1 - q z.2)
  have hF (j : J i) : Integrable (F j) (volume.prod volume) :=
    product_integrable p q hp hq _ _ _ x
  calc
    partialConv p (k i) (g i) x = ∫ a, ∑ j, ∫ b, F j (a,b) := by
      apply integral_congr_ae
      filter_upwards with a
      rw [hg i, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [partialConv, F, mul_assoc, integral_const_mul]
    _ = ∑ j, ∫ a, ∫ b, F j (a,b) :=
      integral_finsetSum _ (fun j _ => (hF j).integral_prod_left)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← integral_prod (F j) (hF j)]
      simp only [F, partialConv, tensor, MeasureTheory.Measure.volume_eq_prod, sub_add_eq_sub_sub]

/-- Join a specified finite family of coordinate flows. Only the axes present
in this family must satisfy one-dimensional factorization. -/
private theorem factors_fin {n : ℕ} (v : Fin n → X)
    (h : ∀ i, Factors (fun t : ℝ => t • v i)) :
    Factors (fun t : Fin n → ℝ => ∑ i, t i • v i) := by
  classical
  induction n with
  | zero =>
    intro f
    let k : Test (Fin 0 → ℝ) := ⟨fun _ => 1, contDiff_const, .of_compactSpace _⟩
    refine ⟨Unit, inferInstance, fun _ => k, fun _ => f, fun x => ?_⟩
    simp [partialConv, k, Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ)]
  | succ n ih =>
    let p := fun t : ℝ => t • v 0
    let q := fun t : Fin n → ℝ => ∑ i, t i • v i.succ
    have hp : Continuous p := continuous_id.smul continuous_const
    have hq : Continuous q := by dsimp [q]; fun_prop
    have hh := factors_prod p q hp hq (h 0) (ih (fun i => v i.succ) (fun i => h i.succ))
    intro f
    obtain ⟨I, instI, k, g, he⟩ := hh f
    let : Fintype I := instI
    let e := (Fin.consEquivL ℝ (fun _ : Fin (n + 1) => ℝ)).symm
    let K (i : I) : Test (Fin (n + 1) → ℝ) :=
      ⟨fun t => (k i).val (e t), (k i).smooth.comp e.contDiff,
        (k i).compact.comp_homeomorph e.toHomeomorph⟩
    refine ⟨I, inferInstance, K, g, fun x => (he x).trans ?_⟩
    apply Finset.sum_congr rfl
    intro i _
    let F := fun z : ℝ × (Fin n → ℝ) =>
      (k i).val z * (g i).val (x - (p z.1 + q z.2))
    have changeVars := (volume_preserving_piFinSuccAbove
      (fun _ : Fin (n + 1) => ℝ) 0).integral_comp' F
    change (∫ z, F z) = ∫ t, (K i).val t * (g i).val (x - ∑ j, t j • v j)
    rw [← changeVars]
    apply integral_congr_ae
    filter_upwards with t
    rw [Fin.sum_univ_succ]
    rfl

/-- Standard Euclidean convolution, with compact smooth factors on *both* sides. -/
private theorem factors_euclidean {n : ℕ}
    (h : ∀ i : Fin n, Factors (fun t : ℝ => t • Pi.single i (1 : ℝ))) :
    Factors (id : (Fin n → ℝ) → (Fin n → ℝ)) := by
  classical
  have he : (fun t : Fin n → ℝ => ∑ i, t i • Pi.single i (1 : ℝ)) = id := by
    funext t j
    simp [Finset.sum_apply, Pi.single_apply, apply_ite]
  rw [← he]
  exact factors_fin _ h

end DixmierMalliavin.Euclidean

namespace DixmierMalliavin.Euclidean

open MeasureTheory Set Function

/-- Every compactly supported smooth function on a finite real product is a finite sum
of convolutions of compactly supported smooth functions. -/
private theorem euclidean_factors (n : ℕ) : Factors (id : (Fin n → ℝ) → Fin n → ℝ) := by
  classical
  apply factors_euclidean
  intro i
  apply factors_of_two
  intro f
  obtain ⟨g, k, l, hg, hgc, hk, hl, hkc, hlc, he⟩ :=
    DixmierMalliavin.exists_coordinate_factorization i 1 one_pos f.val f.smooth f.compact
  have hk' : HasCompactSupport k := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hkc
  have hl' : HasCompactSupport l := isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hlc
  let G : Test (Fin n → ℝ) :=
    ⟨g, hg, f.compact.of_isClosed_subset (isClosed_tsupport _) hgc⟩
  exact ⟨⟨k, hk, hk'⟩, ⟨l, hl, hl'⟩, G, he⟩


end DixmierMalliavin.Euclidean

namespace DixmierMalliavin.Euclidean

open MeasureTheory
open scoped ContDiff BigOperators

private def pullTest {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (e : A ≃L[ℝ] B) (f : Test B) : Test A where
  val x := f.val (e x)
  smooth := f.smooth.comp e.contDiff
  compact := f.compact.comp_homeomorph e.toHomeomorph

/-- Transport convolution factorization without a Haar normalization constant. -/
private theorem factors_transport_id {A B : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasureSpace A] [MeasureSpace B]
    [BorelSpace A] [BorelSpace B] (e : A ≃L[ℝ] B) (he : MeasurePreserving e volume volume)
    (h : Factors (id : A → A)) : Factors (id : B → B) := by
  classical
  intro f
  obtain ⟨I, instI, k, g, hf⟩ := h (pullTest e f)
  let : Fintype I := instI
  refine ⟨I, instI, (fun i => pullTest e.symm (k i)), (fun i => pullTest e.symm (g i)), ?_⟩
  intro x
  calc
    f.val x = ∑ i, partialConv id (k i) (g i) (e.symm x) := by
      simpa only [pullTest, e.apply_symm_apply] using hf (e.symm x)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      let F (y : B) := (k i).val (e.symm y) * (g i).val (e.symm (x - y))
      change (∫ a, (k i).val a * (g i).val (e.symm x - a)) = ∫ y, F y
      rw [← he.integral_comp e.toHomeomorph.measurableEmbedding F]
      simp only [F, map_sub, e.symm_apply_apply]

/-- Smooth compactly supported factorization for the actual product volume on a
Euclidean space times a finite real coordinate product. -/
private theorem euclidean_product_factors (m n : ℕ) : Factors
    (id : (EuclideanSpace ℝ (Fin m) × (Fin n → ℝ)) → EuclideanSpace ℝ (Fin m) × (Fin n → ℝ)) := by
  classical
  let r := (finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)).symm
  let a := ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin m ⊕ Fin n => ℝ) r
  let b := ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin m) (Fin n) (fun _ => ℝ)
  let c := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin m => ℝ)).symm.prodCongr
    (ContinuousLinearEquiv.refl ℝ (Fin n → ℝ))
  have ha : MeasurePreserving a volume volume :=
    volume_measurePreserving_piCongrLeft (fun _ : Fin m ⊕ Fin n => ℝ) r
  have hb : MeasurePreserving b volume volume :=
    volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin m ⊕ Fin n => ℝ)
  have hc : MeasurePreserving c volume volume :=
    (PiLp.volume_preserving_toLp (Fin m)).prod (MeasurePreserving.id (volume : Measure (Fin n → ℝ)))
  exact factors_transport_id ((a.trans b).trans c) (hc.comp (hb.comp ha))
    (euclidean_factors (m + n))

end DixmierMalliavin.Euclidean

open Set Function Filter
open scoped Topology ContDiff BigOperators

namespace DixmierMalliavin.TorusCut

private def bump (t : ℝ) := Real.smoothTransition (t + 1) - Real.smoothTransition t

private theorem bump_smooth : ContDiff ℝ ∞ bump := by unfold bump; fun_prop

private theorem bump_support {t : ℝ} (ht : bump t ≠ 0) : t ∈ Ioo (-1 : ℝ) 1 := by
  constructor
  · by_contra! h
    exact ht (by simp [bump, Real.smoothTransition.zero_of_nonpos (by linarith : t + 1 ≤ 0),
      Real.smoothTransition.zero_of_nonpos (by linarith : t ≤ 0)])
  · by_contra! h
    exact ht (by simp [bump, Real.smoothTransition.one_of_one_le h,
      Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ t + 1)])

private def shifts (t : ℝ) : Finset ℤ := {-⌊t⌋, -⌊t⌋ - 1}

private theorem zero_off (t : ℝ) (n : ℤ) (h : n ∉ shifts t) : bump (t + n) = 0 := by
  by_contra hn
  obtain ⟨ha, hb⟩ := bump_support hn
  have h₁ : -(⌊t⌋ : ℝ) - 2 < n := by linarith [Int.lt_floor_add_one t]
  have h₂ : (n : ℝ) < -(⌊t⌋ : ℝ) + 1 := by linarith [Int.floor_le t]
  have ha' : -⌊t⌋ - 2 < n := by exact_mod_cast h₁
  have hb' : n < -⌊t⌋ + 1 := by exact_mod_cast h₂
  apply h
  simp only [shifts, Finset.mem_insert, Finset.mem_singleton]
  omega

private theorem sum_shifts (t : ℝ) : ∑ n ∈ shifts t, bump (t + n) = 1 := by
  have h : -⌊t⌋ ≠ -⌊t⌋ - 1 := by omega
  simp only [shifts, Finset.sum_pair h, bump, Int.cast_sub, Int.cast_neg, Int.cast_one]
  rw [show t + (-(⌊t⌋ : ℝ) - 1) + 1 = t + -(⌊t⌋ : ℝ) by ring,
    Real.smoothTransition.one_of_one_le (by linarith [Int.floor_le t] : 1 ≤ t + -(⌊t⌋ : ℝ) + 1),
    Real.smoothTransition.zero_of_nonpos (by linarith [Int.lt_floor_add_one t] : t + (-(⌊t⌋ : ℝ) - 1) ≤ 0)]
  ring

private theorem hasSum_bump (t : ℝ) : HasSum (fun n : ℤ ↦ bump (t + n)) 1 :=
  sum_shifts t ▸ hasSum_sum_of_ne_finset_zero (zero_off t)

variable {ι : Type*} [Fintype ι]

private def window (t : ι → ℝ) : ℝ := ∏ i, bump (t i)

private theorem window_smooth : ContDiff ℝ ∞ (window (ι := ι)) := by
  apply contDiff_prod
  intro i _
  exact bump_smooth.comp (by fun_prop : ContDiff ℝ ∞ (fun t : ι → ℝ ↦ t i))

private theorem window_box {t : ι → ℝ} (ht : window t ≠ 0) :
    t ∈ Set.univ.pi (fun _ ↦ Icc (-1 : ℝ) 1) := fun i _ ↦
  Ioo_subset_Icc_self (bump_support (Finset.prod_ne_zero_iff.mp ht i (Finset.mem_univ i)))

private theorem hasSum_window (t : ι → ℝ) : HasSum (fun n : ι → ℤ ↦ window (fun i ↦ t i + n i)) 1 := by
  classical
  let s := Fintype.piFinset (fun i ↦ shifts (t i))
  have hs : ∑ n ∈ s, window (fun i ↦ t i + n i) = 1 := by
    change (∑ n ∈ Fintype.piFinset (fun i ↦ shifts (t i)), ∏ i, bump (t i + n i)) = 1
    rw [← Finset.prod_univ_sum (fun i ↦ shifts (t i)) (fun i n ↦ bump (t i + n))]
    simp [sum_shifts]
  rw [← hs]
  apply hasSum_sum_of_ne_finset_zero
  intro n hn
  by_contra h
  apply hn
  apply Fintype.mem_piFinset.mpr
  intro i
  by_contra hi
  exact Finset.prod_ne_zero_iff.mp h i (Finset.mem_univ i) (zero_off _ _ hi)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open DixmierMalliavin.Torus

private def lift (f : E × UnitAddTorus ι → ℂ) (u : E × (ι → ℝ)) : ℂ :=
  window u.2 • f (cover u)

private theorem lift_smooth {f : E × UnitAddTorus ι → ℂ} (hf : ContDiff ℝ ∞ (f ∘ cover)) :
    ContDiff ℝ ∞ (lift f) := (window_smooth.comp contDiff_snd).smul hf

private theorem lift_compact {f : E × UnitAddTorus ι → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (lift f) := by
  apply HasCompactSupport.of_support_subset_isCompact ((hf.image continuous_fst).prod
    (isCompact_univ_pi (fun _ : ι ↦ isCompact_Icc (α := ℝ) (a := -1) (b := 1))))
  intro u hu
  change window u.2 • f (cover u) ≠ 0 at hu
  have h₁ : window u.2 ≠ 0 := fun h ↦ hu (by rw [h, zero_smul])
  have h₂ : f (cover u) ≠ 0 := fun h ↦ hu (by rw [h, smul_zero])
  exact ⟨⟨cover u, subset_closure h₂, rfl⟩, window_box h₁⟩

private theorem circle_cast_shift (t : ℝ) (n : ℤ) :
    ((t + n : ℝ) : AddCircle (1 : ℝ)) = (t : AddCircle (1 : ℝ)) := by
  rw [AddCircle.coe_add, show (n : ℝ) = n • (1 : ℝ) by simp [zsmul_eq_mul],
    AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]

private theorem hasSum_lift (f : E × UnitAddTorus ι → ℂ) (x : E) (t : ι → ℝ) :
    HasSum (fun n : ι → ℤ ↦ lift f (x, fun i ↦ t i + n i)) (f (cover (x, t))) := by
  simpa only [lift, cover, circle_cast_shift, one_smul] using
    (hasSum_window t).smul_const (f (cover (x, t)))

end DixmierMalliavin.TorusCut

open MeasureTheory Set Function
open scoped BigOperators

namespace DixmierMalliavin.Torus

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩


local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
variable {ι : Type*} [Fintype ι]

private def zvec (n : ι → ℤ) : ι → ℝ := fun i ↦ n i
private def box : Set (ι → ℝ) := {x | ∀ i, x i ∈ Ioc (-1 : ℝ) 0}
private def cell (n : ι → ℤ) : Set (ι → ℝ) := (· + zvec n) '' box

private theorem mem_cell {n : ι → ℤ} {x : ι → ℝ} :
    x ∈ cell n ↔ ∀ i, ⌈x i⌉ = n i := by
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    apply Int.ceil_eq_iff.mpr
    change (n i : ℝ) - 1 < t i + n i ∧ t i + n i ≤ n i
    obtain ⟨hl, hu⟩ := ht i
    constructor <;> linarith
  · intro h
    refine ⟨x - zvec n, ?_, sub_add_cancel _ _⟩
    intro i
    obtain ⟨hl, hu⟩ := Int.ceil_eq_iff.mp (h i)
    change -1 < x i - n i ∧ x i - n i ≤ 0
    constructor <;> linarith

private theorem hasSum_box {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {f : (ι → ℝ) → V} (hf : Integrable f) :
    HasSum (fun n : ι → ℤ ↦ ∫ t in box, f (t + zvec n)) (∫ t, f t) := by
  classical
  have hm (n : ι → ℤ) : MeasurableSet (cell n) :=
    (measurableEmbedding_addRight (zvec n)).measurableSet_image'
      (MeasurableSet.univ_pi' fun _ ↦ measurableSet_Ioc)
  have hd : Pairwise (fun n m : ι → ℤ ↦ Disjoint (cell n) (cell m)) := by
    intro n m h
    refine disjoint_left.mpr fun x hx hy ↦ h (funext fun i ↦ ?_)
    exact ((mem_cell.mp hx) i).symm.trans ((mem_cell.mp hy) i)
  have hu : ⋃ n : ι → ℤ, cell n = univ :=
    eq_univ_of_forall fun x ↦ mem_iUnion.mpr ⟨fun i ↦ ⌈x i⌉, mem_cell.mpr fun _ ↦ rfl⟩
  have he (n : ι → ℤ) : ∫ t in cell n, f t = ∫ t in box, f (t + zvec n) :=
    (measurePreserving_add_right volume (zvec n)).setIntegral_image_emb
      (measurableEmbedding_addRight _) f box
  simpa only [he, hu, Measure.restrict_univ] using hasSum_integral_iUnion hm hd hf.integrableOn

/-- Weil integration with counting measure on the integer lattice and probability Haar
measure on the torus. No continuity, bounded support or uniform convergence is needed. -/
private theorem integral_periodization {f : (ι → ℝ) → ℂ} {F : UnitAddTorus ι → ℂ}
    (hf : Integrable f) (hF : ∀ t : ι → ℝ, HasSum
      (fun n : ι → ℤ ↦ f (fun i ↦ t i + n i)) (F (fun i ↦ t i))) :
    (∫ t, f t) = ∫ q, F q := by
  classical
  have hi (n : ι → ℤ) : IntegrableOn (fun t ↦ f (t + zvec n)) box :=
    ((measurePreserving_add_right volume (zvec n)).integrableOn_image
      (measurableEmbedding_addRight _) (s := box)).mp hf.integrableOn
  have hs := hasSum_integral_of_summable_integral_norm hi (hasSum_box hf.norm).summable
  rw [UnitAddTorus.integral_preimage F (fun _ ↦ (-1 : ℝ))]
  simp only [neg_add_cancel]
  refine ((hasSum_box hf).unique hs).trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t ↦ (hF t).tsum_eq

variable {E : Type*}

private def shift (x : E × (ι → ℝ)) (n : ι → ℤ) : E × (ι → ℝ) :=
  (x.1, fun i ↦ x.2 i + n i)

private def Periodizes (f : E × (ι → ℝ) → ℂ) (F : E × UnitAddTorus ι → ℂ) : Prop :=
  ∀ x, HasSum (fun n : ι → ℤ ↦ f (shift x n)) (F (cover x))

variable [MeasurableSpace E] (μ : Measure E) [SFinite μ]

/-- Product Weil formula; the nonperiodic coordinates carry their original measure. -/
private theorem integral_periodization_prod {f : E × (ι → ℝ) → ℂ} {F : E × UnitAddTorus ι → ℂ}
    (hf : Integrable f (μ.prod volume)) (hF : Integrable F (μ.prod volume))
    (hp : Periodizes f F) :
    (∫ x, f x ∂μ.prod volume) = ∫ x, F x ∂μ.prod volume := by
  rw [integral_prod _ hf, integral_prod _ hF]
  apply integral_congr_ae
  filter_upwards [hf.prod_right_ae] with e he
  exact integral_periodization he (fun t ↦ hp (e,t))

variable [AddCommGroup E]

private theorem cover_shift (x : E × (ι → ℝ)) (n : ι → ℤ) : cover (shift x n) = cover x := by
  refine Prod.ext rfl ?_
  funext i
  change ((x.2 i + n i : ℝ) : AddCircle (1 : ℝ)) = (x.2 i : AddCircle (1 : ℝ))
  rw [AddCircle.coe_add, show (n i : ℝ) = (n i) • (1 : ℝ) by simp [zsmul_eq_mul],
    AddCircle.coe_zsmul, AddCircle.coe_period, smul_zero, add_zero]

private theorem cover_sub (x y : E × (ι → ℝ)) : cover (x-y) = cover x - cover y := by
  apply Prod.ext rfl
  funext i
  exact AddCircle.coe_sub 1 _ _

/-- Pointwise convolution pushdown, in the absolute-Fubini form. The integrability
hypotheses concern explicit kernels, not the convolution identity or a Weil formula. -/
private theorem hasSum_convolution {f g : E × (ι → ℝ) → ℂ} {F G : E × UnitAddTorus ι → ℂ}
    (hf : Periodizes f F) (hg : Periodizes g G) (x : E × (ι → ℝ))
    (hi : ∀ n, Integrable (fun y ↦ f y * g (shift x n - y)) (μ.prod volume))
    (hs : Summable (fun n ↦ ∫ y, ‖f y * g (shift x n - y)‖ ∂μ.prod volume))
    (hm : Integrable (fun y ↦ f y * G (cover x - cover y)) (μ.prod volume))
    (hq : Integrable (fun q ↦ F q * G (cover x - q)) (μ.prod volume)) :
    HasSum (fun n : ι → ℤ ↦ ∫ y, f y * g (shift x n - y) ∂μ.prod volume)
      (∫ q, F q * G (cover x - q) ∂μ.prod volume) := by
  have hsub (y : E × (ι → ℝ)) (n : ι → ℤ) : shift x n - y = shift (x-y) n := by
    refine Prod.ext ?_ ?_
    · rfl
    funext i
    change x.2 i + n i - y.2 i = x.2 i - y.2 i + n i
    abel
  have hinner (y : E × (ι → ℝ)) : (∑' n, f y * g (shift x n - y)) =
      f y * G (cover x - cover y) := by
    simpa only [hsub, cover_sub] using ((hg (x-y)).mul_left (f y)).tsum_eq
  have h := hasSum_integral_of_summable_integral_norm hi hs
  simp only [hinner] at h
  have hfold := integral_periodization_prod μ hm hq (by
    intro y
    simpa only [cover_shift] using (hf y).mul_right (G (cover x - cover y)))
  exact hfold ▸ h

private theorem compact_interactions [TopologicalSpace E]
    {f g : E × (ι → ℝ) → ℂ} (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (x : E × (ι → ℝ)) : ∃ s : Finset (ι → ℤ), ∀ n ∉ s, ∀ y,
      f y * g (shift x n - y) = 0 := by
  classical
  obtain ⟨A, hA⟩ := hf.exists_bound_of_continuousOn (f := Prod.snd) continuous_snd.continuousOn
  obtain ⟨B, hB⟩ := hg.exists_bound_of_continuousOn (f := Prod.snd) continuous_snd.continuousOn
  let R := A + B + ‖x.2‖
  refine ⟨Fintype.piFinset (fun _ : ι ↦ Finset.Icc (-⌈R⌉) ⌈R⌉), ?_⟩
  intro n hn y
  by_contra h
  have hy := hA y (subset_closure (left_ne_zero_of_mul h : f y ≠ 0))
  have hz := hB (shift x n - y) (subset_closure (right_ne_zero_of_mul h : g (shift x n - y) ≠ 0))
  apply hn
  apply Fintype.mem_piFinset.mpr
  intro i
  have h₁ := (norm_le_pi_norm y.2 i).trans hy
  have h₂ := (norm_le_pi_norm (shift x n - y).2 i).trans hz
  have h₃ := norm_le_pi_norm x.2 i
  rw [Real.norm_eq_abs, abs_le] at h₁ h₂ h₃
  change -(B) ≤ x.2 i + n i - y.2 i ∧ x.2 i + n i - y.2 i ≤ B at h₂
  have hr := Int.le_ceil R
  dsimp [R] at hr
  apply Finset.mem_Icc.mpr
  constructor
  · exact_mod_cast (by linarith : -(⌈R⌉ : ℝ) ≤ n i)
  · exact_mod_cast (by linarith : (n i : ℝ) ≤ ⌈R⌉)

/-- For compact continuous factors the lattice sum of convolution integrals is
actually finite at each evaluation point. Only continuity of the proposed quotient
factors and compact support of the first quotient factor are required downstairs. -/
private theorem convolution_compact [TopologicalSpace E] [IsTopologicalAddGroup E]
    [SecondCountableTopology E] [BorelSpace E] [IsLocallyFiniteMeasure μ]
    {f g : E × (ι → ℝ) → ℂ} {F G : E × UnitAddTorus ι → ℂ}
    (hf : Continuous f) (hg : Continuous g) (hF : Continuous F) (hG : Continuous G)
    (cf : HasCompactSupport f) (cg : HasCompactSupport g) (cF : HasCompactSupport F)
    (pf : Periodizes f F) (pg : Periodizes g G) :
    Periodizes (fun x ↦ ∫ y, f y * g (x-y) ∂μ.prod volume)
      (fun q ↦ ∫ u, F u * G (q-u) ∂μ.prod volume) := by
  classical
  intro x
  have hc : Continuous (cover (ι := ι) (E := E)) := continuous_fst.prodMk
    (continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
      ((continuous_apply i).comp continuous_snd))
  apply hasSum_convolution μ pf pg x
  · intro n
    exact (hf.mul (hg.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport cf.mul_right
  · obtain ⟨s, hs⟩ := compact_interactions cf cg x
    apply summable_of_ne_finset_zero (s := s)
    intro n hn
    simp only [hs n hn, norm_zero, integral_zero]
  · exact (hf.mul (hG.comp (continuous_const.sub hc))).integrable_of_hasCompactSupport cf.mul_right
  · exact (hF.mul (hG.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport cF.mul_right

end DixmierMalliavin.Torus

namespace DixmierMalliavin.Torus

open Filter MeasureTheory Set Function
open scoped ContDiff Topology

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E]

private theorem continuous_cover : Continuous (cover (ι := ι) (E := E)) :=
  continuous_fst.prodMk (continuous_pi fun i ↦ (AddCircle.continuous_mk' (1 : ℝ)).comp
    ((continuous_apply i).comp continuous_snd))

private theorem isOpenQuotientMap_cover : IsOpenQuotientMap (cover (ι := ι) (E := E)) :=
  IsOpenQuotientMap.id.prodMap (IsOpenQuotientMap.piMap
    (fun _ : ι ↦ QuotientAddGroup.isOpenQuotientMap_mk))

private theorem cover_eq_iff_exists_shift (x y : E × (ι → ℝ)) (h : cover x = cover y) :
    ∃ k : ι → ℤ, x = shift y k := by
  have h₁ : x.1 = y.1 := congrArg (fun q : E × UnitAddTorus ι ↦ q.1) h
  have h₂ (i : ι) : ((x.2 i - y.2 i : ℝ) : AddCircle (1 : ℝ)) = 0 := by
    rw [AddCircle.coe_sub, show (x.2 i : AddCircle (1 : ℝ)) = (y.2 i : AddCircle (1 : ℝ))
      from congrArg (fun q : E × UnitAddTorus ι ↦ q.2 i) h, sub_self]
  choose k hk using fun i ↦ (AddCircle.coe_eq_zero_iff (p := (1 : ℝ))).mp (h₂ i)
  refine ⟨k, Prod.ext h₁ (funext fun i ↦ ?_)⟩
  change x.2 i = y.2 i + (k i : ℝ)
  have he := hk i
  simp only [zsmul_eq_mul, mul_one] at he
  linarith

/-- A compactly supported smooth function on the Euclidean cover has a compactly
supported periodization whose pullback is smooth. The lattice sum is locally finite. -/
private theorem exists_smooth_periodization {f : E × (ι → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ F : E × UnitAddTorus ι → ℂ, Periodizes f F ∧ Continuous F ∧ HasCompactSupport F ∧
      ContDiff ℝ (⊤ : ℕ∞) (F ∘ cover) := by
  classical
  obtain ⟨R, hR⟩ := hfc.exists_bound_of_continuousOn (f := Prod.snd) continuous_snd.continuousOn
  let P (x : E × (ι → ℝ)) := ∑' n : ι → ℤ, f (shift x n)
  have hfinite (x : E × (ι → ℝ)) : ∃ s : Finset (ι → ℤ), ∀ᶠ y in 𝓝 x,
      ∀ n ∉ s, f (shift y n) = 0 := by
    let B : ℝ := R + (‖x.2‖ + 1)
    refine ⟨Fintype.piFinset (fun _ : ι ↦ Finset.Icc (-⌈B⌉) ⌈B⌉), ?_⟩
    have hb : ∀ᶠ y : E × (ι → ℝ) in 𝓝 x, ‖y.2‖ < ‖x.2‖ + 1 :=
      continuous_snd.norm.continuousAt.eventually (Iio_mem_nhds (lt_add_one _))
    filter_upwards [hb] with y hy n hn
    by_contra hz
    apply hn
    apply Fintype.mem_piFinset.mpr
    intro i
    have h₁ := (norm_le_pi_norm (shift y n).2 i).trans (hR _ (subset_closure hz))
    have h₂ := (norm_le_pi_norm y.2 i).trans hy.le
    rw [Real.norm_eq_abs, abs_le] at h₁ h₂
    change -R ≤ y.2 i + (n i : ℝ) ∧ y.2 i + (n i : ℝ) ≤ R at h₁
    have hB := Int.le_ceil B
    dsimp [B] at hB
    exact Finset.mem_Icc.mpr ⟨by exact_mod_cast (by linarith : -(⌈B⌉ : ℝ) ≤ n i),
      by exact_mod_cast (by linarith : (n i : ℝ) ≤ ⌈B⌉)⟩
  have hP (x : E × (ι → ℝ)) : HasSum (fun n : ι → ℤ ↦ f (shift x n)) (P x) := by
    obtain ⟨s, hs⟩ := hfinite x
    exact (hasSum_sum_of_ne_finset_zero (hs.self_of_nhds)).summable.hasSum
  have hPsmooth : ContDiff ℝ (⊤ : ℕ∞) P := by
    rw [contDiff_iff_contDiffAt]
    intro x
    obtain ⟨s, hs⟩ := hfinite x
    have H (n : ι → ℤ) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ f (shift y n)) :=
      hf.comp (by change ContDiff ℝ _ (fun y : E × (ι → ℝ) ↦ (y.1, y.2 + zvec n)); fun_prop)
    apply (ContDiff.sum (s := s) (fun n _ ↦ H n)).contDiffAt.congr_of_eventuallyEq
    exact hs.mono fun y hy ↦ (hasSum_sum_of_ne_finset_zero hy).tsum_eq
  have hPshift (x : E × (ι → ℝ)) (k : ι → ℤ) : P (shift x k) = P x := by
    unfold P
    rw [← (Equiv.addRight k).tsum_eq (fun n ↦ f (shift x n))]
    congr 1
    funext n
    apply congrArg f
    refine Prod.ext rfl (funext fun i ↦ ?_)
    change x.2 i + (k i : ℝ) + n i = x.2 i + ((n i + k i : ℤ) : ℝ)
    push_cast
    ring
  obtain ⟨s, hs⟩ := (isOpenQuotientMap_cover (ι := ι) (E := E)).surjective.hasRightInverse
  let F (q : E × UnitAddTorus ι) := P (s q)
  have hF : F ∘ cover = P := by
    funext x
    obtain ⟨k, hk⟩ := cover_eq_iff_exists_shift (s (cover x)) x (hs (cover x))
    exact (congrArg P hk).trans (hPshift x k)
  have hp : Periodizes f F := by
    intro x
    have hh : F (cover x) = P x := congrFun hF x
    rw [hh]
    exact hP x
  refine ⟨F, hp, isOpenQuotientMap_cover.continuous_comp_iff.mp ?_, ?_, ?_⟩
  · rw [hF]
    exact hPsmooth.continuous
  · apply HasCompactSupport.intro (hfc.image continuous_cover)
    intro q hq
    have hz : (fun n : ι → ℤ ↦ f (shift (s q) n)) = 0 := by
      funext n
      apply image_eq_zero_of_notMem_tsupport
      intro h
      exact hq ⟨shift (s q) n, h, (cover_shift _ _).trans (hs q)⟩
    rw [← hs q, ← (hp (s q)).tsum_eq, hz]
    exact tsum_zero
  · rw [hF]
    exact hPsmooth

end DixmierMalliavin.Torus

namespace DixmierMalliavin.Torus

open Filter MeasureTheory Function Set
open scoped ContDiff BigOperators

variable {ι E : Type} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasureSpace E] [BorelSpace E] [SecondCountableTopology E]
  [SigmaFinite (volume : Measure E)] [IsLocallyFiniteMeasure (volume : Measure E)]

private abbrev SmoothTorusTest (f : E × UnitAddTorus ι → ℂ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) (f ∘ cover (E := E) (ι := ι))

private def torusConv (u v : E × UnitAddTorus ι → ℂ) (x : E × UnitAddTorus ι) : ℂ :=
  ∫ y : E × UnitAddTorus ι, u y * v (x - y)
    ∂((volume : Measure E).prod (Measure.pi fun _ : ι ↦
      (AddCircle.haarAddCircle : Measure UnitAddCircle)))

private def smoothCompactConvolutions :
    AddSubmonoid ((E × UnitAddTorus ι) → ℂ) :=
  AddSubmonoid.closure {h | ∃ u v, SmoothTorusTest u ∧ HasCompactSupport u ∧
    SmoothTorusTest v ∧ HasCompactSupport v ∧ h = torusConv u v}

/-- The compact smooth factorization descends from the Euclidean cover to the
product of its Euclidean factor with the torus. -/
private theorem compact_smooth_factorization
    (base : DixmierMalliavin.Euclidean.Factors (id : E × (ι → ℝ) → E × (ι → ℝ)))
    (f : E × UnitAddTorus ι → ℂ) (hf : SmoothTorusTest f)
    (hfc : HasCompactSupport f) : f ∈ smoothCompactConvolutions := by
  classical
  let g := DixmierMalliavin.TorusCut.lift f
  let G : DixmierMalliavin.Euclidean.Test (E × (ι → ℝ)) :=
    ⟨g, DixmierMalliavin.TorusCut.lift_smooth hf, DixmierMalliavin.TorusCut.lift_compact hfc⟩
  obtain ⟨I, hI, k, v, hEq⟩ := base G
  let : Fintype I := hI
  choose K pK hK cK sK using fun i ↦ exists_smooth_periodization (k i).smooth (k i).compact
  choose V pV hV cV sV using fun i ↦ exists_smooth_periodization (v i).smooth (v i).compact
  let H (i : I) : E × UnitAddTorus ι → ℂ := torusConv (K i) (V i)
  have hperiod (i : I) : Periodizes (DixmierMalliavin.Euclidean.partialConv id (k i) (v i)) (H i) :=
    convolution_compact (volume : Measure E) (k i).smooth.continuous (v i).smooth.continuous
      (hK i) (hV i) (k i).compact (v i).compact (cK i) (pK i) (pV i)
  have hsum : f = ∑ i, H i := by
    funext q
    obtain ⟨x, rfl⟩ := (isOpenQuotientMap_cover (E := E) (ι := ι)).surjective q
    have hlift : HasSum (fun n : ι → ℤ ↦ g (shift x n)) (f (cover x)) :=
      DixmierMalliavin.TorusCut.hasSum_lift f x.1 x.2
    have hS : HasSum (fun n : ι → ℤ ↦ ∑ i,
        DixmierMalliavin.Euclidean.partialConv id (k i) (v i) (shift x n))
        (∑ i, H i (cover x)) :=
      hasSum_sum fun i _ ↦ hperiod i x
    have he : (fun n : ι → ℤ ↦ g (shift x n)) =
        (fun n ↦ ∑ i, DixmierMalliavin.Euclidean.partialConv id (k i) (v i) (shift x n)) :=
      funext fun n ↦ hEq (shift x n)
    rw [he] at hlift
    have hs := hlift.unique hS
    simpa only [Finset.sum_apply] using hs
  rw [hsum]
  refine (smoothCompactConvolutions (E := E) (ι := ι)).sum_mem fun i _ ↦ ?_
  exact AddSubmonoid.subset_closure ⟨K i, V i, sK i, cK i, sV i, cV i, rfl⟩


end DixmierMalliavin.Torus

open MeasureTheory Set Function
open scoped NNReal

namespace DixmierMalliavin.Discrete

variable {A D : Type*} [AddCommGroup A] [AddCommGroup D]
  [MeasurableSpace A] [MeasurableSpace D] [MeasurableSingletonClass D]
  [Countable D] [DecidableEq D]

private def put (d : D) (f : A → ℂ) (p : A × D) : ℂ := if p.2 = d then f p.1 else 0

def conv {X : Type*} [AddCommGroup X] [MeasurableSpace X] (μ : Measure X)
    (u v : X → ℂ) (x : X) : ℂ := ∫ y, u y * v (-y + x) ∂μ

/-- Product Haar convolution of two individual fibers. No integrability side conditions:
`integral_prod_mul` applies to the separated integrand even in the undefined-integral case. -/
private theorem put_conv (μ : Measure A) [SFinite μ] (d : D) (u v : A → ℂ) :
    put d (conv μ u v) = conv (μ.prod Measure.count) (put 0 u) (put d v) := by
  funext ⟨x,k⟩
  by_cases hk : k = d
  · subst k
    let δ := ({0} : Set D).indicator (fun _ : D ↦ (1 : ℂ))
    have hδ : ∫ j, δ j ∂Measure.count = 1 := by
      dsimp only [δ]
      rw [integral_indicator_const 1 (measurableSet_singleton _)]
      simp [measureReal_def]
    have H : (fun y : A × D ↦ put 0 u y * put d v (-y + (x,d))) =
        fun y ↦ (u y.1 * v (-y.1 + x)) * δ y.2 := by
      funext ⟨z,j⟩
      by_cases hj : j = 0 <;> simp [put, δ, hj]
    change (if d = d then conv μ u v x else 0) =
      ∫ y, put 0 u y * put d v (-y + (x,d)) ∂μ.prod Measure.count
    rw [ite_eq_left rfl, H, integral_prod_mul (fun y : A ↦ u y * v (-y + x)) δ, hδ, mul_one]
    rfl
  · have H : (fun y : A × D ↦ put 0 u y * put d v (-y + (x,k))) = 0 := by
      funext ⟨z,j⟩
      by_cases hj : j = 0 <;> simp [put, hj, hk]
    change (if k = d then conv μ u v x else 0) =
      ∫ y, put 0 u y * put d v (-y + (x,k)) ∂μ.prod Measure.count
    rw [H, ite_eq_right hk]
    simp

variable [TopologicalSpace A] [T2Space A] [TopologicalSpace D] [DiscreteTopology D]

private theorem put_compact (d : D) {f : A → ℂ} (hf : HasCompactSupport f) : HasCompactSupport (put d f) := by
  apply HasCompactSupport.intro (hf.prod (isCompact_singleton (x := d)))
  rintro ⟨x,j⟩ hj
  by_cases h : j = d
  · subst j
    have hx : x ∉ tsupport f := fun H ↦ hj ⟨H, rfl⟩
    simp [put, image_eq_zero_of_notMem_tsupport hx]
  · simp [put, h]

/-- Choose `P` to be smoothness after pullback to the Euclidean torus cover.
The discrete coordinates introduce no derivatives. -/
theorem finite_slice_factorization (μ : Measure A) [SFinite μ] (P : (A → ℂ) → Prop)
    (hzero : P 0) (f : A × D → ℂ) (hf : HasCompactSupport f)
    (hs : ∀ d, P (fun x ↦ f (x,d)))
    (base : ∀ g, P g → HasCompactSupport g → g ∈ AddSubmonoid.closure
      {h | ∃ u v, P u ∧ HasCompactSupport u ∧ P v ∧ HasCompactSupport v ∧ h = conv μ u v}) :
    f ∈ AddSubmonoid.closure {h | ∃ u v : A × D → ℂ,
      (∀ j, P (fun x ↦ u (x,j))) ∧ HasCompactSupport u ∧
      (∀ j, P (fun x ↦ v (x,j))) ∧ HasCompactSupport v ∧ h = conv (μ.prod Measure.count) u v} := by
  classical
  let S := (hf.image continuous_snd).finite_of_discrete.toFinset
  let C := AddSubmonoid.closure {h | ∃ u v : A × D → ℂ,
      (∀ j, P (fun x ↦ u (x,j))) ∧ HasCompactSupport u ∧
      (∀ j, P (fun x ↦ v (x,j))) ∧ HasCompactSupport v ∧ h = conv (μ.prod Measure.count) u v}
  have hput (d : D) (g : A → ℂ) (hg : P g) (j : D) : P (fun x ↦ put d g (x,j)) := by
    by_cases h : j = d
    · simpa [put, h] using hg
    · simpa [put, h] using (show P (fun _ ↦ 0) from hzero)
  have mem (d : D) : put d (fun x ↦ f (x,d)) ∈ C := by
    have hc : HasCompactSupport (fun x ↦ f (x,d)) := by
      apply HasCompactSupport.intro (hf.image continuous_fst)
      intro x hx
      exact image_eq_zero_of_notMem_tsupport (fun h ↦ hx ⟨(x,d), h, rfl⟩)
    apply AddSubmonoid.closure_induction (motive := fun h _ ↦ put d h ∈ C) _ _ _ (base _ (hs d) hc)
    · rintro _ ⟨u,v,hu,huc,hv,hvc,rfl⟩
      exact AddSubmonoid.subset_closure ⟨put 0 u, put d v, hput _ _ hu, put_compact _ huc,
        hput _ _ hv, put_compact _ hvc, put_conv μ d u v⟩
    · convert C.zero_mem using 1
      ext p
      simp [put]
    · intro a b _ _ ha hb
      convert C.add_mem ha hb using 1
      ext p
      by_cases hp : p.2 = d <;> simp [put, hp]
  have he : f = ∑ d ∈ S, put d (fun x ↦ f (x,d)) := by
    funext ⟨x,j⟩
    by_cases hj : j ∈ S
    · simp [Finset.sum_apply, put, hj]
    · have hx : (x,j) ∉ tsupport f := fun H ↦ hj (by simpa [S] using
            (show j ∈ Prod.snd '' tsupport f from ⟨(x,j), H, rfl⟩))
      simp [Finset.sum_apply, put, hj, image_eq_zero_of_notMem_tsupport hx]
  rw [he]
  exact C.sum_mem fun d _ ↦ mem d

end DixmierMalliavin.Discrete

namespace DixmierMalliavin.Torus

open MeasureTheory
open scoped ContDiff

/-- Compact smooth functions on a product of Euclidean space and a torus are finite
sums of convolutions of compact smooth functions. Smoothness is tested on the real cover. -/
theorem compact_euclidean_torus_factorization (m n : ℕ)
    (f : EuclideanSpace ℝ (Fin m) × UnitAddTorus (Fin n) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (f ∘ cover)) (hc : HasCompactSupport f) :
    f ∈ AddSubmonoid.closure {h |
      ∃ u v : EuclideanSpace ℝ (Fin m) × UnitAddTorus (Fin n) → ℂ,
        ContDiff ℝ (⊤ : ℕ∞) (u ∘ cover) ∧ HasCompactSupport u ∧
        ContDiff ℝ (⊤ : ℕ∞) (v ∘ cover) ∧ HasCompactSupport v ∧
        h = DixmierMalliavin.Discrete.conv ((volume : Measure (EuclideanSpace ℝ (Fin m))).prod
          (Measure.pi fun _ : Fin n ↦ (AddCircle.haarAddCircle : Measure UnitAddCircle))) u v} := by
  refine AddSubmonoid.closure_mono ?_ (compact_smooth_factorization
    (DixmierMalliavin.Euclidean.euclidean_product_factors m n) f hf hc)
  rintro _ ⟨u, v, hu, hcu, hv, hcv, rfl⟩
  exact ⟨u, v, hu, hcu, hv, hcv, by
    funext x
    apply integral_congr_ae
    filter_upwards with y
    rw [sub_eq_add_neg, add_comm x]⟩


end DixmierMalliavin.Torus

end RiemannMasullo
