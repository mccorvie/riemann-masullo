module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4
import RiemannMasullo.AppD_SchwartzBruhat.Sec1c
import RiemannMasullo.Ch02_AdelicTheta.Sec2b
import RiemannMasullo.External.TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import RiemannMasullo.Ch02_AdelicTheta.Sec1
import RiemannMasullo.ForMathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Fintype.Pi
import Mathlib.Topology.LocallyConstant.Algebra

/-! # Product-norm Fourier cutoffs on compact S-adelic bands

A smooth profile with a near-zero plateau gives an actual Schwartz–Bruhat
output on compact Fourier support. The cutoff then descends to theta classes.
-/

@[expose] public noncomputable section

open Filter IsDedekindDomain NumberField Set
open scoped BigOperators Classical ContDiff NNReal NumberField.AdeleRing SchwartzMap TensorProduct Topology

namespace RiemannMasullo

/-- The norm with values below the given threshold grouped into a single fiber. -/
private def cutoffClampedNorm {K : Type*} [Norm K] (δ : ℝ) (x : K) : ℝ :=
  if ‖x‖ < δ then 0 else ‖x‖

private theorem cutoffClampedNorm_nonneg {K : Type*} [SeminormedAddCommGroup K] (δ : ℝ) (x : K) :
    0 ≤ cutoffClampedNorm δ x := by
  unfold cutoffClampedNorm
  split
  · exact le_rfl
  · exact norm_nonneg _

private theorem isLocallyConstant_cutoffClampedNorm {K : Type*} [SeminormedAddCommGroup K]
    [IsUltrametricDist K] {δ : ℝ} (hδ : 0 < δ) :
    IsLocallyConstant (cutoffClampedNorm δ : K → ℝ) := by
  refine (IsLocallyConstant.iff_exists_open _).2 fun x ↦ ?_
  by_cases hx : ‖x‖ < δ
  · refine ⟨{y : K | ‖y‖ < δ}, isOpen_lt continuous_norm continuous_const, hx,
      fun y hy ↦ ?_⟩
    change ‖y‖ < δ at hy
    simp [cutoffClampedNorm, hy, hx]
  · have hx0 : 0 < ‖x‖ := hδ.trans_le (le_of_not_gt hx)
    refine ⟨Metric.ball x ‖x‖, Metric.isOpen_ball, Metric.mem_ball_self hx0, fun y hy ↦ ?_⟩
    have hy' : ‖y - x‖ < ‖x‖ := by simpa only [Metric.mem_ball, dist_eq_norm] using hy
    have hnorm := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hy'.ne
    rw [sub_add_cancel, max_eq_right hy'.le] at hnorm
    simp only [cutoffClampedNorm, hnorm]

/-- On a compact ball the clamped norms have finitely many labels. The indicator
of each label inside that ball is a finite-place Schwartz–Bruhat test. -/
private theorem exists_finitePlace_cutoffNormFibers {F : Type*} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    ∃ (labels : Finset ℝ)
      (fiber : ℝ → SchwartzBruhat (Multiplicative (v.adicCompletion F))),
      (labels : Set ℝ) =
        cutoffClampedNorm δ '' Metric.closedBall (0 : v.adicCompletion F) R ∧
      ∀ c x, fiber c (Multiplicative.ofAdd x) =
        if x ∈ Metric.closedBall 0 R ∧ cutoffClampedNorm δ x = c then 1 else 0 := by
  let K := v.adicCompletion F
  let : ProperSpace K := properSpace_adicCompletion v
  let B := Metric.closedBall (0 : K) R
  let q : K → ℝ := cutoffClampedNorm δ
  have hB : IsCompact B := isCompact_closedBall _ _
  have hBo : IsClopen B := IsUltrametricDist.isClopen_closedBall (0 : K) hR.ne'
  have hq : IsLocallyConstant q := isLocallyConstant_cutoffClampedNorm hδ
  have hfinite : (q '' B).Finite := by
    let : CompactSpace B := isCompact_iff_compactSpace.mp hB
    rw [← range_domRestrict]
    exact (hq.comp_continuous continuous_subtype_val).range_finite
  have htest (c : ℝ) : ∃ f : SchwartzBruhat (Multiplicative K),
      ∀ x : K, f (Multiplicative.ofAdd x) = if x ∈ B ∧ q x = c then 1 else 0 := by
    let U := B ∩ {x : K | q x = c}
    have hU : IsClopen U := hBo.inter (hq.isClopen_fiber c)
    let k := LocallyConstant.charFn ℂ hU
    obtain ⟨f, hf⟩ := (mem_finitePlaceSchwartz_iff (F := F) v (k : K → ℂ)).2
      ⟨k.isLocallyConstant, HasCompactSupport.intro hB fun x hx ↦
        (LocallyConstant.charFn_eq_zero ℂ x hU).2 fun h ↦ hx h.1⟩
    refine ⟨f, fun x ↦ (hf x).trans ?_⟩
    change (LocallyConstant.charFn ℂ hU : K → ℂ) x = _
    rw [LocallyConstant.coe_charFn]
    simp only [Set.indicator, Pi.one_apply, U, mem_inter_iff, mem_ofPred_eq]
  choose fiber hfiber using htest
  exact ⟨hfinite.toFinset, fiber, hfinite.coe_toFinset, hfiber⟩

/-- A product of fiber indicators selects the unique matching tuple of labels
inside the product box. The sum vanishes outside the box. -/
private theorem sum_piFinset_mul_cutoffNormFiberIndicators {ι : Type*} [Fintype ι] [DecidableEq ι]
    (labels : ι → Finset ℝ) (a : ι → ℝ) (inside : ι → Prop)
    (ha : ∀ i, inside i → a i ∈ labels i) (value : (ι → ℝ) → ℂ) :
    (∑ c ∈ Fintype.piFinset labels,
      value c * ∏ i, (if inside i ∧ a i = c i then (1 : ℂ) else 0)) =
      if ∀ i, inside i then value a else 0 := by
  by_cases hall : ∀ i, inside i
  · rw [ite_eq_left hall]
    rw [Finset.sum_eq_single_of_mem a (Fintype.mem_piFinset.2 fun i ↦ ha i (hall i))]
    · simp [hall]
    · intro c _ hca
      have hne : ¬ ∀ i, a i = c i := fun h ↦ hca (funext h).symm
      obtain ⟨i, hi⟩ := not_forall.mp hne
      have hp : (∏ j, (if inside j ∧ a j = c j then (1 : ℂ) else 0)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
      rw [hp, mul_zero]
  · rw [ite_eq_right hall]
    obtain ⟨i, hi⟩ := not_forall.mp hall
    refine Finset.sum_eq_zero fun c _ ↦ ?_
    have hp : (∏ j, (if inside j ∧ a j = c j then (1 : ℂ) else 0)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [hp, mul_zero]

variable {F : Type*} [Field F] [NumberField F]

local notation "M∞" => mixedEmbedding.mixedSpace F
local notation "m∞" => InfiniteAdeleRing.ringEquiv_mixedSpace F
local notation "N∞" => (mixedEmbedding.norm (K := F))

private theorem mixedNorm_eq_arch_product (x : InfiniteAdeleRing F) :
    N∞ (m∞ x) = ∏ w : InfinitePlace F, ‖x w‖ ^ w.mult := by
  rw [mixedEmbedding.norm_apply]
  apply Finset.prod_congr rfl
  intro w _
  congr 1
  by_cases hw : w.IsReal
  · rw [mixedEmbedding.normAtPlace_apply_of_isReal hw, InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero
      (map_zero _) _
  · rw [mixedEmbedding.normAtPlace_apply_of_isComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hw), InfiniteAdeleRing.ringEquiv_mixedSpace_apply]
    exact (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _

private theorem frequency_contDiff_normAtPlace_pow (w : InfinitePlace F) (z : M∞)
    (hz : mixedEmbedding.normAtPlace w z ≠ 0) :
    ContDiffAt ℝ (∞ : ℕ∞ω) (fun z : M∞ ↦ mixedEmbedding.normAtPlace w z ^ w.mult) z := by
  by_cases hw : w.IsReal
  · simp_rw [mixedEmbedding.normAtPlace_apply_of_isReal hw] at *
    have h : ContDiff ℝ (∞ : ℕ∞ω) (fun z : M∞ ↦ z.1 ⟨w, hw⟩) :=
      (contDiff_pi.mp (contDiff_fst (E := ({v : InfinitePlace F // v.IsReal} → ℝ)))) ⟨w, hw⟩
    exact (h.contDiffAt.norm ℝ (norm_ne_zero_iff.mp hz)).pow _
  · let hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    simp_rw [mixedEmbedding.normAtPlace_apply_of_isComplex hc] at *
    have h : ContDiff ℝ (∞ : ℕ∞ω) (fun z : M∞ ↦ z.2 ⟨w, hc⟩) :=
      (contDiff_pi.mp (contDiff_snd (F := ({v : InfinitePlace F // v.IsComplex} → ℂ)))) ⟨w, hc⟩
    exact (h.contDiffAt.norm ℂ (norm_ne_zero_iff.mp hz)).pow _

private theorem frequency_contDiff_mul_mixedNorm_cutoff (q : ℝ → ℂ)
    (hq : ContDiff ℝ (∞ : ℕ∞ω) q) {b : ℝ} (hb : 0 < b)
    (hplateau : EqOn q (fun _ ↦ q 0) (Icc 0 b)) {c : ℝ} (hc : 0 ≤ c) :
    ContDiff ℝ (∞ : ℕ∞ω) (fun z : M∞ ↦ q (c * N∞ z)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : N∞ z = 0
  · apply (contDiffAt_const (c := q 0)).congr_of_eventuallyEq
    have hlt : ∀ᶠ y : M∞ in 𝓝 z, c * N∞ y < b :=
      ((continuous_const.mul (mixedEmbedding.continuous_norm F)).continuousAt.eventually_lt
        continuousAt_const) (by simpa [hz] using hb)
    exact hlt.mono fun y hy ↦ hplateau ⟨mul_nonneg hc (mixedEmbedding.norm_nonneg y), hy.le⟩
  · apply hq.contDiffAt.comp z
    apply contDiffAt_const.mul
    change ContDiffAt ℝ (∞ : ℕ∞ω) (fun x : M∞ ↦
      ∏ w : InfinitePlace F, mixedEmbedding.normAtPlace w x ^ w.mult) z
    exact contDiffAt_prod (t := Finset.univ) fun w _ ↦ frequency_contDiff_normAtPlace_pow w z
      ((mixedEmbedding.norm_ne_zero_iff.mp hz) w)

private theorem exists_frequencyArchBump (q : ℝ → ℂ)
    (hq : ContDiff ℝ (∞ : ℕ∞ω) q) {b : ℝ} (hb : 0 < b)
    (hplateau : EqOn q (fun _ ↦ q 0) (Icc 0 b)) {c : ℝ} (hc : 0 ≤ c)
    {K : Set (InfiniteAdeleRing F)} (hK : IsCompact K) :
    ∃ g : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)),
      HasCompactSupport g.val ∧ ∀ x ∈ K,
        g (Multiplicative.ofAdd x) = q (c * ∏ w : InfinitePlace F, ‖x w‖ ^ w.mult) := by
  have hmc : Continuous (m∞ : InfiniteAdeleRing F → M∞) :=
    continuous_infiniteAdeleRingEquivMixedSpace F
  have hm'c : Continuous (m∞.symm : M∞ → InfiniteAdeleRing F) :=
    continuous_infiniteAdeleRingEquivMixedSpace_symm F
  obtain ⟨β, hβ, -, hβone, hβcompact, -⟩ :=
    (hK.image hmc).exists_contDiff_cutoff_eventuallyEq_one (E := M∞) isOpen_univ (subset_univ _)
  let v : M∞ → ℂ := fun x ↦ (β x : ℂ) * q (c * N∞ x)
  have hv : ContDiff ℝ (∞ : ℕ∞ω) v :=
    (Complex.ofRealCLM.contDiff.comp hβ).mul (frequency_contDiff_mul_mixedNorm_cutoff q hq hb hplateau hc)
  have hvc : HasCompactSupport v := (hβcompact.comp_left Complex.ofReal_zero).mul_right
  let g : InfiniteAdeleRing F → ℂ := fun x ↦ v (m∞ x)
  have hg : g ∘ Multiplicative.toAdd ∈ schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing F)) :=
    (mem_archimedeanSchwartzBruhat_iff g).mpr ⟨hvc.toSchwartzMap hv, fun _ ↦ rfl⟩
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ M∞ :=
    ⟨Multiplicative.toAdd.trans m∞.toEquiv, hmc.comp continuous_toAdd,
      continuous_ofAdd.comp hm'c⟩
  refine ⟨⟨_, hg⟩, hvc.comp_homeomorph e, ?_⟩
  intro x hx
  change v (m∞ x) = _
  dsimp only [v]
  rw [mixedNorm_eq_arch_product, (hβone (m∞ x) ⟨x, hx, rfl⟩).self_of_nhds, Complex.ofReal_one,
    one_mul]

set_option quotPrecheck false

variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "archNorm(" x ")" => (∏ w : InfinitePlace F, ‖(x : InfiniteAdeleRing F) w‖ ^ w.mult)
local notation "prodNorm(" u ")" => archNorm((u : Aₛ).1) * ∏ v : S, ‖(u : Aₛ).2 v‖

private theorem cutoff_compatible_clamp {u : Aₛ}
    (q : ℝ → ℂ) {b : ℝ} (hb : 0 < b)
    (hplateau : EqOn q (fun _ ↦ q 0) (Icc 0 b))
    {R : ℝ} (hR : 1 ≤ R)
    (hbox : u ∈ sLocalPWBox S R) :
    let a := R ^ Fintype.card (InfinitePlace F)
    let c := R ^ Fintype.card S
    let δ := b / (a * c)
    q (archNorm(u.1) * ∏ v : S, cutoffClampedNorm δ (u.2 v)) = q (prodNorm(u)) := by
  classical
  intro a c δ
  have hpos : 0 < R := zero_lt_one.trans_le hR
  have ha : 0 < a := by dsimp [a]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  by_cases hsmall : ∃ v : S, ‖u.2 v‖ < δ
  · obtain ⟨v, hv⟩ := hsmall
    have hzero : (∏ w : S, cutoffClampedNorm δ (u.2 w)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ v) (ite_eq_left hv)
    rw [hzero, mul_zero]
    symm
    apply hplateau
    refine ⟨by positivity, ?_⟩
    have harch : archNorm(u.1) ≤ a := by
      calc
        _ ≤ ∏ _w : InfinitePlace F, R :=
          Finset.prod_le_prod₀ (fun w _ ↦ pow_nonneg (norm_nonneg (u.1 w)) w.mult)
            (fun w _ ↦ hbox.1 w)
        _ = a := by simp only [Finset.prod_const, Finset.card_univ, a]
    have ht : (∏ w ∈ (Finset.univ : Finset S).erase v, ‖u.2 w‖) ≤ c := by
      calc
        _ ≤ ∏ _w ∈ (Finset.univ : Finset S).erase v, R :=
          Finset.prod_le_prod₀ (fun w _ ↦ norm_nonneg _) (fun w _ ↦ hbox.2 w)
        _ ≤ c := by
          simp only [Finset.prod_const, c]
          exact pow_le_pow_right₀ hR ((Finset.card_erase_le).trans (by simp))
    calc
      prodNorm(u) = archNorm(u.1) * (‖u.2 v‖ * ∏ w ∈ (Finset.univ : Finset S).erase v, ‖u.2 w‖) := by
        exact congrArg (archNorm(u.1) * ·)
          (Finset.mul_prod_erase Finset.univ (fun w : S ↦ ‖u.2 w‖) (Finset.mem_univ v)).symm
      _ ≤ a * (δ * c) := mul_le_mul harch (mul_le_mul hv.le ht (by positivity) (by positivity))
        (by positivity) (by positivity)
      _ = b := by
        dsimp only [δ]
        field_simp [ha.ne', hc.ne']
  · apply congrArg q
    congr 1
    apply Finset.prod_congr rfl
    intro v _
    exact ite_eq_right (fun hv ↦ hsmall ⟨v, hv⟩)

private theorem exists_frequency_box {K : Set (Multiplicative Aₛ)} (hK : IsCompact K) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ x ∈ K, x.toAdd ∈ sLocalPWBox S R := by
  let N (x : Aₛ) :=
    (∑ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) + ∑ v : S, ‖x.2 v‖
  have hN : Continuous N := (continuous_finsetSum _ fun w _ ↦
    ((continuous_apply w).comp continuous_fst).norm.pow w.mult).add
      (continuous_finsetSum _ fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm)
  obtain ⟨R, hR⟩ := (hK.image (hN.comp continuous_toAdd)).bddAbove
  refine ⟨max R 1, le_max_right _ _, fun x hx ↦ ?_⟩
  have hxR : N x.toAdd ≤ max R 1 := (hR (mem_image_of_mem _ hx)).trans (le_max_left _ _)
  refine ⟨fun w ↦ ?_, fun v ↦ ?_⟩
  · exact (Finset.single_le_sum (fun i _ ↦ by positivity) (Finset.mem_univ w)).trans
      ((le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)).trans hxR)
  · exact (Finset.single_le_sum (fun i _ ↦ norm_nonneg _) (Finset.mem_univ v)).trans
      ((le_add_of_nonneg_left (Finset.sum_nonneg fun _ _ ↦ by positivity)).trans hxR)

private theorem compactSchwartzBruhat_mul_of_compact
    {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G]
    (u f : SchwartzBruhat G) (hu : HasCompactSupport u.val) (hf : HasCompactSupport f.val) :
    ∃ g : SchwartzBruhat G, HasCompactSupport g.val ∧ ∀ x, g x = u x * f x := by
  have hsmooth : ContDiff ℝ (∞ : ℕ∞ω) (fun z : ℂ ↦ z ^ 2) := contDiff_id.pow _
  obtain ⟨p, hp⟩ := compact_schwartzBruhat_comp (f := u + f) (hu.add hf) hsmooth (by simp)
  obtain ⟨m, hm⟩ := compact_schwartzBruhat_comp (f := u - f) (hu.sub hf) hsmooth (by simp)
  let g : SchwartzBruhat G := (4 : ℂ)⁻¹ • (p - m)
  have hg (x : G) : g x = u x * f x := by
    change (4 : ℂ)⁻¹ * (p x - m x) = _
    rw [show p x = (u x + f x) ^ 2 from congrFun hp x,
        show m x = (u x - f x) ^ 2 from congrFun hm x]
    ring
  exact ⟨g, (funext hg).symm ▸ hu.mul_right (f' := f.val), hg⟩

/-- Paper: Theorem 12.4.1.1, Step II, (12.4.1.8), pp. 516–517.
A smooth product-norm multiplier with a plateau at zero preserves every compactly
supported Schwartz–Bruhat frequency profile. The finite-place norm factors are
clamped below a uniform threshold on the support and split into finitely many
compact open fibers.
Deviation: The compact-support hypothesis is essential and repairs the printed
unrestricted Schwartz–Bruhat claim (ERRATA F246). -/
private theorem exists_sLocalProductNorm_mul_compactSchwartzBruhat (q : ℝ → ℂ)
    (hq : ContDiff ℝ (∞ : ℕ∞ω) q) {b : ℝ} (hb : 0 < b)
    (hplateau : EqOn q (fun _ ↦ q 0) (Icc 0 b))
    (f : Bₛ) (hf : HasCompactSupport f.val) :
    ∃ g : Bₛ, HasCompactSupport g.val ∧ ∀ u : Aₛ,
      g (Multiplicative.ofAdd u) = q (prodNorm(u)) * f (Multiplicative.ofAdd u) := by
  classical
  let (v : S) : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
  let : T2Space (Multiplicative Aₛ) :=
    inferInstanceAs (T2Space (((w : InfinitePlace F) → w.Completion) × FinitePlaceProduct F S))
  let : LocallyCompactSpace (Multiplicative Aₛ) := inferInstanceAs (LocallyCompactSpace Aₛ)
  obtain ⟨R, hR, hbox⟩ := exists_frequency_box hf
  have hRpos := zero_lt_one.trans_le hR
  let δ := b / (R ^ Fintype.card (InfinitePlace F) * R ^ Fintype.card S)
  have hδ : 0 < δ := by positivity
  choose label fiber hlabel hfiber using
    fun v : S ↦ exists_finitePlace_cutoffNormFibers (F := F) v.val hδ hRpos
  let K := (fun x : Multiplicative Aₛ ↦ x.toAdd.1) '' tsupport f.val
  have hK : IsCompact K := hf.image (continuous_fst.comp continuous_toAdd)
  let weight (c : S → ℝ) := ∏ v : S, max 0 (c v)
  have hw (c : S → ℝ) : 0 ≤ weight c := Finset.prod_nonneg fun v _ ↦ le_max_left _ _
  choose arch harchc harch using
    fun c : S → ℝ ↦ exists_frequencyArchBump q hq hb hplateau (hw c) hK
  obtain ⟨e, he⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  let term (c : S → ℝ) : Bₛ := e (arch c ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, fiber v (c v)))
  have hterm (c : S → ℝ) (x : Aₛ) :
      term c (Multiplicative.ofAdd x) = arch c (Multiplicative.ofAdd x.1) *
        ∏ v : S, (if x.2 v ∈ Metric.closedBall 0 R ∧ cutoffClampedNorm δ (x.2 v) = c v
          then (1 : ℂ) else 0) := by
    change e (arch c ⊗ₜ[ℂ] (⨂ₜ[ℂ] v, fiber v (c v))) (Multiplicative.ofAdd x) = _
    rw [he]
    simp_rw [hfiber]
  let D : Set (FinitePlaceProduct F S) :=
    univ.pi fun v : S ↦ Metric.closedBall (0 : v.val.adicCompletion F) R
  have hD : IsCompact D := isCompact_univ_pi fun v ↦ by
    let : ProperSpace (v.val.adicCompletion F) := properSpace_adicCompletion v.val
    exact isCompact_closedBall _ _
  have htermc (c : S → ℝ) : HasCompactSupport (term c).val := by
    let join (y : Multiplicative (InfiniteAdeleRing F) × FinitePlaceProduct F S) :
        Multiplicative Aₛ := Multiplicative.ofAdd (y.1.toAdd, y.2)
    have hjoin : Continuous join := continuous_ofAdd.comp
      ((continuous_toAdd.comp continuous_fst).prodMk continuous_snd)
    have hc : IsCompact (tsupport (arch c).val) := harchc c
    apply HasCompactSupport.intro ((hc.prod hD).image hjoin)
    intro x hx
    by_contra h
    change term c (Multiplicative.ofAdd x.toAdd) ≠ 0 at h
    rw [hterm] at h
    have hmul := mul_ne_zero_iff.mp h
    have ha := subset_tsupport _ hmul.1
    have hd : x.toAdd.2 ∈ D := by
      apply Set.mem_univ_pi.mpr
      intro v
      by_contra hv
      apply hmul.2
      exact Finset.prod_eq_zero (Finset.mem_univ v) (by simp [hv])
    exact hx ⟨(Multiplicative.ofAdd x.toAdd.1, x.toAdd.2), ⟨ha, hd⟩, rfl⟩
  let U : Bₛ := ∑ c ∈ Fintype.piFinset label, term c
  have hU (x : Multiplicative Aₛ) : U x = ∑ c ∈ Fintype.piFinset label, term c x := by
    let ev : Bₛ →ₗ[ℂ] ℂ := (LinearMap.proj x).comp (schwartzBruhatSubmodule (Multiplicative Aₛ)).subtype
    exact map_sum ev _ _
  have hUc : HasCompactSupport U.val := by
    have hU' : U.val = ∑ c ∈ Fintype.piFinset label, (term c).val := by
      funext x
      rw [Finset.sum_apply]
      exact hU x
    rw [hU']
    exact HasCompactSupport.finset_sum fun c _ ↦ htermc c
  have hUeq (x : Multiplicative Aₛ) (hx : x ∈ tsupport f.val) :
      U x = q (prodNorm(x.toAdd)) := by
    let a (v : S) := cutoffClampedNorm δ (x.toAdd.2 v)
    let inside (v : S) := x.toAdd.2 v ∈ Metric.closedBall 0 R
    have hi (v : S) : inside v := by
      change x.toAdd.2 v ∈ Metric.closedBall 0 R
      rw [Metric.mem_closedBall, dist_zero_right]
      exact (hbox x hx).2 v
    have ha (v : S) (hv : inside v) : a v ∈ label v := by
      change a v ∈ (label v : Set ℝ)
      rw [hlabel v]
      exact ⟨x.toAdd.2 v, hv, rfl⟩
    rw [hU]
    change (∑ c ∈ Fintype.piFinset label, term c (Multiplicative.ofAdd x.toAdd)) = _
    simp_rw [hterm]
    rw [sum_piFinset_mul_cutoffNormFiberIndicators label a inside ha
      (fun c ↦ arch c (Multiplicative.ofAdd x.toAdd.1)), ite_eq_left hi]
    rw [harch _ _ ⟨x, hx, rfl⟩]
    have heq : weight a = ∏ v : S, cutoffClampedNorm δ (x.toAdd.2 v) :=
      Finset.prod_congr rfl fun v _ ↦ max_eq_right (cutoffClampedNorm_nonneg _ _)
    rw [heq, mul_comm]
    exact cutoff_compatible_clamp q hb hplateau hR (hbox x hx)
  obtain ⟨g, hgc, hg⟩ := compactSchwartzBruhat_mul_of_compact U f hUc hf
  refine ⟨g, hgc, fun x ↦ ?_⟩
  rw [hg]
  by_cases hx : Multiplicative.ofAdd x ∈ tsupport f.val
  · rw [hUeq _ hx]
    rfl
  · have hfzero : f (Multiplicative.ofAdd x) = 0 := by
      by_contra hn
      exact hx (subset_tsupport _ hn)
    rw [hfzero, mul_zero, mul_zero]

/-- Paper: (12.4.1.8), p. 517. If the multiplied Fourier transform is
Schwartz–Bruhat, its inverse realizes the scalar cutoff and has the prescribed
Fourier transform. -/
theorem sLocalTraceFourierCutoff_exists_of_mul_fourier
    (ρ : SAdeleRing F S → ℂ) (f h : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hh : ∀ u : SAdeleRing F S,
      h (Multiplicative.ofAdd u) = ρ u * sAdeleSchwartzFourier f (Multiplicative.ofAdd u)) :
    ∃ g : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
      (∀ x, sLocalTraceFourierCutoff ρ f x = g (Multiplicative.ofAdd x)) ∧
        sAdeleSchwartzFourier g = h := by
  let g := sAdeleSchwartzFourier (sAdeleSchwartzFourier (sAdeleSchwartzFourier h))
  refine ⟨g, ?_, ?_⟩
  · intro x
    unfold sLocalTraceFourierCutoff
    rw [← funext hh]
    change sAdeleSchwartzFourier h (Multiplicative.ofAdd (-x)) = g (Multiplicative.ofAdd x)
    exact (sLocal_fourier_inversion (sAdeleSchwartzFourier h) x).symm
  · ext x
    change sAdeleSchwartzFourier g (Multiplicative.ofAdd x.toAdd) = h (Multiplicative.ofAdd x.toAdd)
    dsimp only [g]
    rw [sLocal_fourier_inversion, sLocal_fourier_inversion, neg_neg]
/-- Paper: (12.4.1.8), p. 517. On a test with compact Fourier support, the
actual product-norm cutoff is realized by a Schwartz–Bruhat test with Fourier
support contained in the original support. Here the frequency profile is
smooth and constant near zero. -/
theorem sLocalTraceFourierCutoff_realize_compact_band (q : ℝ → ℂ)
    (hq : ContDiff ℝ (∞ : ℕ∞ω) q) {b : ℝ} (hb : 0 < b)
    (hplateau : EqOn q (fun _ ↦ q 0) (Icc 0 b))
    (f : Bₛ) (hf : HasCompactSupport (sAdeleSchwartzFourier f).val) :
    ∃ g : Bₛ, (∀ x : Aₛ,
        sLocalTraceFourierCutoff (fun u ↦ q (prodNorm(u))) f x = g (Multiplicative.ofAdd x)) ∧
      (∀ u : Aₛ, sAdeleSchwartzFourier g (Multiplicative.ofAdd u) =
        q (prodNorm(u)) * sAdeleSchwartzFourier f (Multiplicative.ofAdd u)) ∧
      tsupport (sAdeleSchwartzFourier g).val ⊆ tsupport (sAdeleSchwartzFourier f).val := by
  obtain ⟨h, -, hh⟩ := exists_sLocalProductNorm_mul_compactSchwartzBruhat q hq hb hplateau
    (sAdeleSchwartzFourier f) hf
  obtain ⟨g, hg, hF⟩ := sLocalTraceFourierCutoff_exists_of_mul_fourier
    (fun u ↦ q (prodNorm(u))) f h hh
  refine ⟨g, hg, fun u ↦ ?_, ?_⟩
  · rw [hF]
    exact hh u
  · rw [hF]
    apply closure_mono
    intro u hu
    change h (Multiplicative.ofAdd u.toAdd) ≠ 0 at hu
    rw [hh] at hu
    exact (mul_ne_zero_iff.mp hu).2

local notation "Jₛ" => SIdeleQuotient F S
local notation "Kₛ" => LinearMap.ker (sLocalAdelicTheta F S)
local notation "Uₛ" => (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ

private theorem thetaProductNorm_unit (a : Aₛˣ) :
    prodNorm(a.val) = ((sIdeleNorm F S a).val : ℝ) := by
  let evaluate : (Aₛˣ →* ℝ≥0ˣ) →* ℝ :=
    NNReal.toRealHom.toMonoidHom.comp ((Units.coeHom ℝ≥0).comp (MonoidHom.eval a))
  change prodNorm(a.val) = evaluate (sIdeleNorm F S)
  simp only [sIdeleNorm, map_mul, map_prod]
  rfl

/-- Paper: (12.4.1.8), p. 517. When multiplication by a function of the additive product norm
gives another Schwartz–Bruhat test, its theta sum is multiplied by the same function of the idelic
quotient norm. -/
theorem sLocalAdelicThetaOnClasses_mul_productNorm (q : ℝ → ℂ) (f h : Bₛ)
    (hh : ∀ u : Aₛ, h (Multiplicative.ofAdd u) =
      q (prodNorm(u)) * f (Multiplicative.ofAdd u)) (x : Jₛ) :
    sLocalAdelicThetaOnClasses F S h x =
      q ((sIdeleQuotientNorm F S x).val : ℝ) * sLocalAdelicThetaOnClasses F S f x := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicThetaOnClasses_mk,
    sLocalAdelicTheta_apply, sLocalAdelicTheta_apply, sIdeleQuotientNorm_mk]
  change (∑' ξ : Uₛ, h (Multiplicative.ofAdd (sUnitEmbedding F S ξ * a).val)) =
    q ((sIdeleNorm F S a).val : ℝ) *
      ∑' ξ : Uₛ, f (Multiplicative.ofAdd (sUnitEmbedding F S ξ * a).val)
  rw [← tsum_mul_left]
  refine tsum_congr fun ξ ↦ ?_
  have hξ : sIdeleNorm F S (sUnitEmbedding F S ξ) = 1 :=
    (sIdeleNorm_spec F S).2 ⟨ξ, rfl⟩
  rw [hh, thetaProductNorm_unit, map_mul, hξ, one_mul]

/-- Paper: (12.4.1.8), p. 517. If multiplying the additive Fourier transforms by the product-norm
mask admits Schwartz–Bruhat inverse transforms, their theta classes depend only on the input theta
classes. -/
theorem sLocalThetaFourier_mul_productNorm_mkQ_eq (q : ℝ → ℂ) (f₁ f₂ g₁ g₂ : Bₛ)
    (hf : (Kₛ).mkQ f₁ = (Kₛ).mkQ f₂)
    (hg₁ : ∀ u : Aₛ, sAdeleSchwartzFourier g₁ (Multiplicative.ofAdd u) =
      q (prodNorm(u)) * sAdeleSchwartzFourier f₁ (Multiplicative.ofAdd u))
    (hg₂ : ∀ u : Aₛ, sAdeleSchwartzFourier g₂ (Multiplicative.ofAdd u) =
      q (prodNorm(u)) * sAdeleSchwartzFourier f₂ (Multiplicative.ofAdd u)) :
    (Kₛ).mkQ g₁ = (Kₛ).mkQ g₂ := by
  let e := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
  have he := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2
  have hClass : (Kₛ).mkQ (sAdeleSchwartzFourier f₁) =
      (Kₛ).mkQ (sAdeleSchwartzFourier f₂) := by
    rw [← he f₁, ← he f₂, hf]
  have hTheta := (sLocalAdelicThetaSpace_mk_eq_iff _ _).mp hClass
  apply e.injective
  rw [he g₁, he g₂]
  apply (sLocalAdelicThetaSpace_mk_eq_iff _ _).mpr
  refine ContinuousMap.ext fun x ↦ ?_
  rw [sLocalAdelicThetaOnClasses_mul_productNorm q _ _ hg₁ x,
    sLocalAdelicThetaOnClasses_mul_productNorm q _ _ hg₂ x, hTheta]

/-- Paper: (12.4.1.8), p. 517. A frequency symbol equal to one on the product
band of a test acts as the identity on that test. In particular the sharp
product-ball symbol at the level radius fixes every defining test of the level. -/
theorem sLocalTraceFourierCutoff_eq_self_of_one_on_band
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S))) (B : ℝ)
    (hf : tsupport (sAdeleSchwartzFourier f).val ⊆
      Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S B)
    (ρ : SAdeleRing F S → ℂ)
    (hρ : EqOn ρ 1 (sLocalPWProductRegion S B)) (x : SAdeleRing F S) :
    sLocalTraceFourierCutoff ρ f x = f (Multiplicative.ofAdd x) := by
  have hmult (u : SAdeleRing F S) :
      ρ u * sAdeleSchwartzFourier f (Multiplicative.ofAdd u) =
        1 * sAdeleSchwartzFourier f (Multiplicative.ofAdd u) := by
    by_cases hu : u ∈ sLocalPWProductRegion S B
    · rw [hρ hu]
      rfl
    · have hz : sAdeleSchwartzFourier f (Multiplicative.ofAdd u) = 0 := by
        by_contra hn
        exact hu (hf (subset_tsupport _ hn))
      simp [hz]
  calc
    sLocalTraceFourierCutoff ρ f x = sLocalTraceFourierCutoff (fun _ ↦ 1) f x := by
      unfold sLocalTraceFourierCutoff
      rw [show (fun u ↦ ρ u * sAdeleSchwartzFourier f (Multiplicative.ofAdd u)) =
        (fun u ↦ 1 * sAdeleSchwartzFourier f (Multiplicative.ofAdd u)) from funext hmult]
    _ = _ := sLocalTraceFourierCutoff_one f x

end RiemannMasullo
