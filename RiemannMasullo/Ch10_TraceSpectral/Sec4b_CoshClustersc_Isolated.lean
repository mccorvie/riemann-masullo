module

public import RiemannMasullo.Ch10_TraceSpectral.Sec4b_CoshClustersb_Isolated
public import RiemannMasullo.Ch10_TraceSpectral.Sec3_TraceClass
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import RiemannMasullo.Ch10_TraceSpectral.Sec3_Clusters
import RiemannMasullo.Ch10_TraceSpectral.Sec2
import RiemannMasullo.AppC_LCTVS.Sec3a
import Mathlib

/-! # Positive-width cluster trace-norm summability and boundedness for arbitrary basepoints

This module lifts the section-trivial positive-width (`α ≥ 0`, `s ≥ 0`) cluster trace-norm
summability theorem from `Sec4b_CoshClustersb_Isolated` to arbitrary spectral basepoint
choices `χ` (`IsSpectralBasepointChoice χ`) by componentwise imaginary-ordinate relabelling
(`coshClusterRelabel`), and derives:
- `coshSpectralStripGeometricBlocks_clusters_summable`
- `coshSpectralStripGeometricBlocks_clusters_bddAbove`
- `coshSpectralStripAmbientKernel_clusters_exists`
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set
open scoped BigOperators NNReal NumberField.AdeleRing Topology

namespace RiemannMasullo.Isolated.CoshPositiveWidth

section Relabelling

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
attribute [local instance] instSpectralQuotientPolynormableSec3

variable {F : Type*} [Field F] [NumberField F]

private lemma continuedCompletedHeckeL_ne_top
    (ψ : PontryaginDual (IdeleClassGroup (NumberField.RingOfIntegers F) F)) (z : ℂ) :
    meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ) z ≠ ⊤ := by
  obtain ⟨hΛ, hval⟩ := continuedCompletedHeckeL_spec ψ
  have h2 : meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ) (2 : ℂ) ≠ ⊤ := fun htop ↦ by
    have hbad := completedHeckeL_continuation_zeros ψ _ hΛ hval (by norm_num : 0 < (2 : ℂ).re)
      (by rw [htop]; exact WithTop.coe_lt_top 0)
    norm_num at hbad
  exact hΛ.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (mem_univ _) (mem_univ z) h2

private lemma exists_basepointChoice_twist
    (χ χ₀ : PontryaginDual (ideleClassNorm F).ker →
      PontryaginDual (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    (hχ : IsSpectralBasepointChoice (F := F) χ)
    (hχ₀ : IsSpectralBasepointChoice (F := F) χ₀)
    (ω : PontryaginDual (ideleClassNorm F).ker) :
    ∃ τ : ℝ, ∀ z : ℂ, ideleClassNormTwist (F := F) (χ ω) z =
      ideleClassNormTwist (χ₀ ω) ((τ : ℂ) * Complex.I + z) := by
  let C𝔽 := IdeleClassGroup (NumberField.RingOfIntegers F) F
  have hnorm (ψ : PontryaginDual C𝔽) (z : ℂ) (g : C𝔽) :
      ‖ideleClassNormTwist (F := F) ψ z g‖ = ((ideleClassNorm F g).val : ℝ) ^ z.re := by
    have hpos : 0 < ((ideleClassNorm F g).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
    change ‖((ψ g : Circle) : ℂ) * ((((ideleClassNorm F g).val : ℝ) : ℂ) ^ z)‖ = _
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos]
  have hc : ∀ g : (ideleClassNorm F).ker,
      ideleClassNormTwist (F := F) (χ ω) 0 g.val = (ω g : ℂ) := fun g ↦ by
    have hres : χ ω g.val = ω g := DFunLike.congr_fun (hχ ω) g
    change ((χ ω g.val : Circle) : ℂ) * ((((ideleClassNorm F g.val).val : ℝ) : ℂ) ^ (0 : ℂ)) = _
    rw [Complex.cpow_zero, mul_one, hres]
  obtain ⟨c, hcz, -⟩ := hχ₀.existsUnique_normTwist ω _ hc
  obtain ⟨g, hg⟩ := (ideleGroup_quotient.{_, 0} F).2.2.2.2.2.2.2.2.2.1
    (Units.mk0 (2 : ℝ≥0) (by norm_num))
  have hre : c.re = 0 := by
    have h1 := hnorm (χ ω) 0 g
    have h2 := hnorm (χ₀ ω) c g
    rw [hcz, h2, hg] at h1
    have h3 : (2 : ℝ) ^ c.re = 1 := by simpa using h1
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)] at h3
    have h4 : Real.log 2 * c.re = 0 := (Real.exp_eq_one_iff _).mp h3
    exact (mul_eq_zero.mp h4).resolve_left (Real.log_pos (by norm_num)).ne'
  refine ⟨c.im, fun z ↦ ?_⟩
  have hci : ((c.im : ℝ) : ℂ) * Complex.I = c := by apply Complex.ext <;> simp [hre]
  have h := ideleClassNormTwist_add_of_eq hcz z
  rwa [zero_add, ← hci] at h

private lemma basepointChoice_order_shift
    {ψ ψ₀ : PontryaginDual (IdeleClassGroup (NumberField.RingOfIntegers F) F)} {c : ℂ}
    (h : ∀ z : ℂ, ideleClassNormTwist (F := F) ψ z = ideleClassNormTwist ψ₀ (c + z)) (w : ℂ) :
    (0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ) w ↔
        0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ₀) (c + w)) ∧
      (meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ) w).untop₀.toNat =
        (meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ₀) (c + w)).untop₀.toNat := by
  have hset : (Set.range fun f : adelePolarSubspace F ↦ meromorphicOrderAt
        (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ z)) w) =
      Set.range fun f : adelePolarSubspace F ↦ meromorphicOrderAt
        (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ₀ z)) (c + w) := by
    congr 1
    funext f
    have hfun : (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ z)) =
        (fun z ↦ globalThetaMellinIntegral f.val (ideleClassNormTwist ψ₀ z)) ∘
          fun z : ℂ ↦ c + z := funext fun z ↦ by rw [h z]; rfl
    rw [hfun]
    exact meromorphicOrderAt_comp_of_deriv_ne_zero
      ((differentiable_id.const_add c).analyticAt w)
      (show deriv (fun z : ℂ ↦ c + z) w ≠ 0 by simp)
  have h1 := isLeast_globalThetaMellinIntegral_orders (F := F) ψ w
  have h2 := isLeast_globalThetaMellinIntegral_orders (F := F) ψ₀ (c + w)
  rw [hset] at h1
  have hmax : max 0 (meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ) w) =
      max 0 (meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ₀) (c + w)) := h1.unique h2
  have hne := continuedCompletedHeckeL_ne_top (F := F) ψ w
  have hne₀ := continuedCompletedHeckeL_ne_top (F := F) ψ₀ (c + w)
  cases ho : meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ) w with
  | top => exact absurd ho hne
  | coe k =>
    cases ho₀ : meromorphicOrderAt (continuedCompletedHeckeL (F := F) ψ₀) (c + w) with
    | top => exact absurd ho₀ hne₀
    | coe k₀ =>
      rw [ho, ho₀] at hmax
      have hk : max 0 k = max 0 k₀ := by exact_mod_cast hmax
      refine ⟨?_, ?_⟩
      · have e1 : (0 : WithTop ℤ) < (k : WithTop ℤ) ↔ 0 < k := by exact_mod_cast Iff.rfl
        have e2 : (0 : WithTop ℤ) < (k₀ : WithTop ℤ) ↔ 0 < k₀ := by exact_mod_cast Iff.rfl
        rw [e1, e2]; omega
      · simp only [WithTop.untop₀_coe]; omega

private theorem coshClusterRelabel (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    (χ χ₀ : PontryaginDual (ideleClassNorm F).ker →
      PontryaginDual (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    (hχ : IsSpectralBasepointChoice (F := F) χ)
    (hχ₀ : IsSpectralBasepointChoice (F := F) χ₀)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ (eZ : CoshStripZero (F := F) χ a α ≃ CoshStripZero (F := F) χ₀ a α)
      (eJ : SpectralStripJetIndex (F := F) χ a α s ≃ SpectralStripJetIndex (F := F) χ₀ a α s),
      (∀ z : CoshStripZero (F := F) χ a α, (eZ z).val.1 = z.val.1) ∧
      IsSpectralMarkushevichBasis (x ∘ eJ.symm) (Λ ∘ eJ.symm) ∧
      (∀ j₀, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs ((Λ ∘ eJ.symm) j₀) =
        (spectralStripJet_memLp (F := F) χ₀ hα hs j₀).toLp
          (spectralZeroJet (F := F) (χ₀ j₀.val.1) j₀.val.2.1 j₀.val.2.2.1 j₀.val.2.2.2)) ∧
      (∀ K₀ : Finset (CoshStripZero (F := F) χ₀ a α),
        coshGeometricClusterBlock (F := F) a hα hs φ χ₀ (x ∘ eJ.symm) (Λ ∘ eJ.symm) K₀ =
          coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K₀.map eZ.symm.toEmbedding)) ∧
      (∀ K₀ : Finset (CoshStripZero (F := F) χ₀ a α),
        coshSpectralClusterBlock (F := F) a hα hs φ χ₀ (x ∘ eJ.symm) (Λ ∘ eJ.symm) K₀ =
          coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K₀.map eZ.symm.toEmbedding)) ∧
      (∀ K₀ : Finset (CoshStripZero (F := F) χ₀ a α),
        coshAmbientClusterBlock (F := F) a hα hs φ χ₀ (x ∘ eJ.symm) (Λ ∘ eJ.symm) K₀ =
          coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K₀.map eZ.symm.toEmbedding)) := by
  let C₁ := (ideleClassNorm F).ker
  choose τ hτ using fun ω : PontryaginDual C₁ ↦ exists_basepointChoice_twist χ χ₀ hχ hχ₀ ω
  have hpt (ω : PontryaginDual C₁) (b t : ℝ) :
      ((τ ω : ℝ) : ℂ) * Complex.I + (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        ((b : ℝ) : ℂ) + ((t + τ ω : ℝ) : ℂ) * Complex.I := by push_cast; ring
  have hord (ω : PontryaginDual C₁) (b t : ℝ) :
      (0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
            (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I) ↔
          0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ₀ ω))
            (((b : ℝ) : ℂ) + ((t + τ ω : ℝ) : ℂ) * Complex.I)) ∧
        (meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ ω))
            (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)).untop₀.toNat =
          (meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ₀ ω))
            (((b : ℝ) : ℂ) + ((t + τ ω : ℝ) : ℂ) * Complex.I)).untop₀.toNat := by
    have h0 := basepointChoice_order_shift (hτ ω) (((b : ℝ) : ℂ) + (t : ℂ) * Complex.I)
    rwa [hpt] at h0
  let e₀ : PontryaginDual C₁ × ℝ × ℝ ≃ PontryaginDual C₁ × ℝ × ℝ :=
    ⟨fun p ↦ (p.1, p.2.1, p.2.2 + τ p.1), fun p ↦ (p.1, p.2.1, p.2.2 - τ p.1),
      fun p ↦ Prod.ext rfl (Prod.ext rfl (add_sub_cancel_right p.2.2 (τ p.1))),
      fun p ↦ Prod.ext rfl (Prod.ext rfl (sub_add_cancel p.2.2 (τ p.1)))⟩
  have hZ₀ : ∀ p : PontryaginDual C₁ × ℝ × ℝ,
      (p.2.1 ∈ Icc (-α) α ∧ 0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ p.1))
          (((a + p.2.1 : ℝ) : ℂ) + (p.2.2 : ℂ) * Complex.I)) ↔
        ((e₀ p).2.1 ∈ Icc (-α) α ∧
          0 < meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ₀ (e₀ p).1))
            (((a + (e₀ p).2.1 : ℝ) : ℂ) + ((e₀ p).2.2 : ℂ) * Complex.I)) :=
    fun p ↦ and_congr Iff.rfl (hord p.1 (a + p.2.1) p.2.2).1
  let eZ : CoshStripZero (F := F) χ a α ≃ CoshStripZero (F := F) χ₀ a α := e₀.subtypeEquiv hZ₀
  let e₁ : PontryaginDual C₁ × ℝ × ℝ × ℕ ≃ PontryaginDual C₁ × ℝ × ℝ × ℕ :=
    ⟨fun p ↦ (p.1, p.2.1, p.2.2.1 + τ p.1, p.2.2.2),
      fun p ↦ (p.1, p.2.1, p.2.2.1 - τ p.1, p.2.2.2),
      fun p ↦ Prod.ext rfl (Prod.ext rfl (Prod.ext (add_sub_cancel_right p.2.2.1 (τ p.1)) rfl)),
      fun p ↦ Prod.ext rfl (Prod.ext rfl (Prod.ext (sub_add_cancel p.2.2.1 (τ p.1)) rfl))⟩
  have hJ₀ : ∀ p : PontryaginDual C₁ × ℝ × ℝ × ℕ,
      p.2.2.2 < spectralStripMultiplicity α s p.2.1
          (meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ p.1))
            (((a + p.2.1 : ℝ) : ℂ) + (p.2.2.1 : ℂ) * Complex.I)).untop₀.toNat ↔
        (e₁ p).2.2.2 < spectralStripMultiplicity α s (e₁ p).2.1
          (meromorphicOrderAt (continuedCompletedHeckeL (F := F) (χ₀ (e₁ p).1))
            (((a + (e₁ p).2.1 : ℝ) : ℂ) + ((e₁ p).2.2.1 : ℂ) * Complex.I)).untop₀.toNat :=
    fun p ↦ by
      have he1 : e₁ p = (p.1, p.2.1, p.2.2.1 + τ p.1, p.2.2.2) := rfl
      rw [he1]
      change p.2.2.2 < spectralStripMultiplicity α s p.2.1 _ ↔
        p.2.2.2 < spectralStripMultiplicity α s p.2.1 _
      rw [(hord p.1 (a + p.2.1) p.2.2.1).2]
  let eJ : SpectralStripJetIndex (F := F) χ a α s ≃ SpectralStripJetIndex (F := F) χ₀ a α s :=
    e₁.subtypeEquiv hJ₀
  have hN : ∀ z₀ : CoshStripZero (F := F) χ₀ a α,
      coshStripMult χ₀ a α s z₀ = coshStripMult χ a α s (eZ.symm z₀) := fun z₀ ↦ by
    dsimp only [coshStripMult]
    have h0 := (hord z₀.val.1 (a + z₀.val.2.1) (z₀.val.2.2 - τ z₀.val.1)).2
    rw [sub_add_cancel] at h0
    exact congrArg (spectralStripMultiplicity α s z₀.val.2.1) h0.symm
  have hjet : ∀ (z₀ : CoshStripZero (F := F) χ₀ a α) (m : Fin (coshStripMult χ₀ a α s z₀)),
      eJ.symm (coshStripJet χ₀ a α s z₀ m) = coshStripJet χ a α s (eZ.symm z₀) (finCongr (hN z₀) m) :=
    fun _ _ ↦ rfl
  have hb₀ : IsSpectralMarkushevichBasis (x ∘ eJ.symm) (Λ ∘ eJ.symm) :=
    ⟨fun i ↦ hb.1 (eJ.symm i), fun i j hij ↦ hb.2.1 (eJ.symm i) (eJ.symm j) (fun he ↦ hij (eJ.symm.injective he)),
      by rw [eJ.symm.surjective.range_comp]; exact hb.2.2.1,
      by rw [eJ.symm.surjective.range_comp]; exact hb.2.2.2⟩
  have hj₀ : ∀ j₀ : SpectralStripJetIndex (F := F) χ₀ a α s,
      spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs ((Λ ∘ eJ.symm) j₀) =
        (spectralStripJet_memLp (F := F) χ₀ hα hs j₀).toLp
          (spectralZeroJet (F := F) (χ₀ j₀.val.1) j₀.val.2.1 j₀.val.2.2.1 j₀.val.2.2.2) := fun j₀ ↦ by
    have hfun : spectralZeroJet (F := F) (χ (eJ.symm j₀).val.1) (eJ.symm j₀).val.2.1
        (eJ.symm j₀).val.2.2.1 (eJ.symm j₀).val.2.2.2 =
        spectralZeroJet (F := F) (χ₀ j₀.val.1) j₀.val.2.1 j₀.val.2.2.1 j₀.val.2.2.2 := by
      funext g
      change ideleClassNormTwist (χ j₀.val.1)
          (((j₀.val.2.1 : ℝ) : ℂ) + ((j₀.val.2.2.1 - τ j₀.val.1 : ℝ) : ℂ) * Complex.I) g *
          ((logIdeleClassNorm F g : ℂ)) ^ j₀.val.2.2.2 =
        ideleClassNormTwist (χ₀ j₀.val.1)
          (((j₀.val.2.1 : ℝ) : ℂ) + (j₀.val.2.2.1 : ℂ) * Complex.I) g *
          ((logIdeleClassNorm F g : ℂ)) ^ j₀.val.2.2.2
      rw [hτ j₀.val.1, hpt, sub_add_cancel]
    have h1 := MemLp.coeFn_toLp (spectralStripJet_memLp (F := F) χ hα hs (eJ.symm j₀))
    have h2 := MemLp.coeFn_toLp (spectralStripJet_memLp (F := F) χ₀ hα hs j₀)
    have hhj := hj (eJ.symm j₀)
    change spectralSobolevDualEmbedding F a _ hs (Λ (eJ.symm j₀)) = _
    rw [hhj]
    exact MeasureTheory.Lp.ext (h1.trans ((EventuallyEq.of_eq hfun).trans h2.symm))
  have hproj (K₀ : Finset (CoshStripZero (F := F) χ₀ a α)) :
      coshClusterProj (F := F) a hα hs (x ∘ eJ.symm) (Λ ∘ eJ.symm) K₀
        (coshStripMult χ₀ a α s) (coshStripJet χ₀ a α s) =
      coshClusterProj (F := F) a hα hs x Λ (K₀.map eZ.symm.toEmbedding)
        (coshStripMult χ a α s) (coshStripJet χ a α s) := by
    have hq : quotClusterProj (x ∘ eJ.symm) (Λ ∘ eJ.symm) K₀
        (coshStripMult χ₀ a α s) (coshStripJet χ₀ a α s) =
        quotClusterProj x Λ (K₀.map eZ.symm.toEmbedding)
          (coshStripMult χ a α s) (coshStripJet χ a α s) := by
      unfold quotClusterProj
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun z₀ _ ↦ Fintype.sum_equiv (finCongr (hN z₀)) _ _ fun m ↦ ?_
      exact congrArg (fun j ↦ (Λ j).smulRight (x j)) (hjet z₀ m)
    unfold coshClusterProj
    rw [hq]
  refine ⟨eZ, eJ, fun _ ↦ rfl, hb₀, hj₀, fun K₀ ↦ ?_, fun K₀ ↦ ?_, fun K₀ ↦ ?_⟩
  · dsimp only [coshGeometricClusterBlock]; rw [hproj K₀]
  · dsimp only [coshSpectralClusterBlock]; rw [hproj K₀]
  · dsimp only [coshAmbientClusterBlock]; rw [hproj K₀]

end Relabelling

section ArbitraryBasepointTheorems

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1
attribute [local instance] instSpectralQuotientPolynormableSec3

variable {F : Type*} [Field F] [NumberField F]

private lemma traceNorm_nonneg_c {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (T : nuclearEndomorphisms H) : 0 ≤ traceNorm T := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := H)).norm_nonneg T

private lemma traceNorm_zero_c {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] : traceNorm (0 : nuclearEndomorphisms H) = 0 := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  simpa using (traceNorm_normedSpaceCore (H := H)).norm_smul (0 : ℂ) 0

private lemma traceNorm_add_le_c {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S T : nuclearEndomorphisms H) :
    traceNorm (S + T) ≤ traceNorm S + traceNorm T := by
  let : Norm (nuclearEndomorphisms H) := ⟨traceNorm⟩
  exact (traceNorm_normedSpaceCore (H := H)).norm_triangle S T

lemma sum_mem_nuclear_c {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Finset ι) (T : ι → H →L[ℂ] H)
    (hT : ∀ i ∈ S, IsNuclearOperator (T i)) : IsNuclearOperator (∑ i ∈ S, T i) :=
  Finset.sum_induction T (fun A ↦ IsNuclearOperator A)
    (fun _ _ ha hb ↦ (nuclearEndomorphisms H).add_mem ha hb)
    (nuclearEndomorphisms H).zero_mem hT

private lemma traceNorm_sum_le_c {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (S : Finset ι) (T : ι → nuclearEndomorphisms H) :
    traceNorm (∑ i ∈ S, T i) ≤ ∑ i ∈ S, traceNorm (T i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [traceNorm_zero_c]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (traceNorm_add_le_c _ _).trans (add_le_add le_rfl ih)

private lemma bddAbove_partialSum_traceNorm_of_summable {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : ι → H →L[ℂ] H) (hT : ∀ i, IsNuclearOperator (T i))
    (hsum : Summable (fun i ↦ traceNorm ⟨T i, hT i⟩)) :
    BddAbove (Set.range fun S : Finset ι ↦
      traceNorm ⟨∑ i ∈ S, T i, sum_mem_nuclear_c S T fun i _ ↦ hT i⟩) := by
  refine ⟨∑' i, traceNorm ⟨T i, hT i⟩, ?_⟩
  rintro _ ⟨S, rfl⟩
  dsimp only
  have hsub : (⟨∑ i ∈ S, T i, sum_mem_nuclear_c S T fun i _ ↦ hT i⟩ :
      nuclearEndomorphisms H) = ∑ i ∈ S, (⟨T i, hT i⟩ : nuclearEndomorphisms H) := by
    apply Subtype.ext; rw [Submodule.coe_sum]
  rw [hsub]
  exact (traceNorm_sum_le_c S _).trans (hsum.sum_le_tsum S fun i _ ↦ traceNorm_nonneg_c _)

/-- Positive-width (`α ≥ 0`, `s ≥ 0`) cluster trace-norm summability for the geometric, spectral,
and ambient cluster blocks of `coshTestAction hα hs φ`, for every spectral basepoint choice `χ`
and every Markushevich basis `(x, Λ)` realizing the `χ`-strip jets. -/
theorem coshSpectralStripGeometricBlocks_clusters_summable
    (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    (χ : PontryaginDual (ideleClassNorm F).ker →
      PontryaginDual (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    (hχ : IsSpectralBasepointChoice χ)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ K : (PontryaginDual (ideleClassNorm F).ker × ℤ) → Finset (CoshStripZero (F := F) χ a α),
      (∀ p₁ p₂, p₁ ≠ p₂ → Disjoint (K p₁) (K p₂)) ∧
      (∀ z : CoshStripZero (F := F) χ a α, ∃ p, z ∈ K p) ∧
      (∀ p z, z ∈ K p → z.val.1 = p.1) ∧
      Summable (fun p ↦ traceNorm ⟨coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p),
        coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      Summable (fun p ↦ traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p),
        coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      Summable (fun p ↦ traceNorm ⟨coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K p),
        coshAmbientClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) := by
  classical
  obtain ⟨χ₀, τ₀, hχ₀, hχ₀1, hτ₀, hχ₀τ⟩ := exists_sectionTrivial_basepointChoice F
  obtain ⟨eZ, eJ, heZ_comp, hb₀, hj₀, hblk_g, hblk_s, _⟩ :=
    coshClusterRelabel a hα hs φ χ χ₀ hχ hχ₀ x Λ hb hj
  obtain ⟨K₀, hdisj₀, hcov₀, hcomp₀, hsum_g₀, hsum_s₀⟩ :=
    coshSpectralStripGeometricBlocks_clusters_summable_of_section a hα hs φ χ₀ hχ₀ hχ₀1 τ₀ hτ₀
      hχ₀τ (x ∘ eJ.symm) (Λ ∘ eJ.symm) hb₀ hj₀
  let K : (PontryaginDual (ideleClassNorm F).ker × ℤ) → Finset (CoshStripZero (F := F) χ a α) :=
    fun p ↦ (K₀ p).map eZ.symm.toEmbedding
  have hdisj : ∀ p₁ p₂, p₁ ≠ p₂ → Disjoint (K p₁) (K p₂) := fun p₁ p₂ hne ↦
    (Finset.disjoint_map eZ.symm.toEmbedding).mpr (hdisj₀ p₁ p₂ hne)
  have hcov : ∀ z : CoshStripZero (F := F) χ a α, ∃ p, z ∈ K p := fun z ↦ by
    obtain ⟨p, hp⟩ := hcov₀ (eZ z)
    exact ⟨p, Finset.mem_map.mpr ⟨eZ z, hp, eZ.symm_apply_apply z⟩⟩
  have hcomp : ∀ p z, z ∈ K p → z.val.1 = p.1 := fun p z hz ↦ by
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_map.mp hz
    have he1 : (eZ.symm z₀).val.1 = z₀.val.1 := by
      simpa using (heZ_comp (eZ.symm z₀)).symm
    exact he1.trans (hcomp₀ p z₀ hz₀)
  have hsum_g : Summable (fun p ↦ traceNorm ⟨coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p),
      coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) :=
    hsum_g₀.congr fun p ↦ congrArg traceNorm (Subtype.ext (hblk_g (K₀ p)))
  have hsum_s : Summable (fun p ↦ traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p),
      coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) :=
    hsum_s₀.congr fun p ↦ congrArg traceNorm (Subtype.ext (hblk_s (K₀ p)))
  have hsum_a : Summable (fun p ↦ traceNorm ⟨coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K p),
      coshAmbientClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) := by
    refine (hsum_g.add hsum_s).of_nonneg_of_le (fun _ ↦ traceNorm_nonneg_c _) fun p ↦ ?_
    have hadd : (⟨coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K p),
        coshAmbientClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩ :
        nuclearEndomorphisms (CoshIntervalSobolev F α s)) =
        ⟨coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩ +
        ⟨coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩ :=
      Subtype.ext (coshAmbientClusterBlock_eq_add a hα hs φ χ x Λ (K p))
    rw [hadd]
    exact traceNorm_add_le_c _ _
  exact ⟨K, hdisj, hcov, hcomp, hsum_g, hsum_s, hsum_a⟩

/-- Positive-width (`α ≥ 0`, `s ≥ 0`) boundedness of finite partial-sum trace norms for the
geometric, spectral, and ambient cluster blocks of `coshTestAction hα hs φ`. -/
theorem coshSpectralStripGeometricBlocks_clusters_bddAbove
    (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    (χ : PontryaginDual (ideleClassNorm F).ker →
      PontryaginDual (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    (hχ : IsSpectralBasepointChoice χ)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ K : (PontryaginDual (ideleClassNorm F).ker × ℤ) → Finset (CoshStripZero (F := F) χ a α),
      (∀ p₁ p₂, p₁ ≠ p₂ → Disjoint (K p₁) (K p₂)) ∧
      (∀ z : CoshStripZero (F := F) χ a α, ∃ p, z ∈ K p) ∧
      (∀ p z, z ∈ K p → z.val.1 = p.1) ∧
      BddAbove (Set.range fun S : Finset (PontryaginDual (ideleClassNorm F).ker × ℤ) ↦
        traceNorm ⟨∑ p ∈ S, coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          sum_mem_nuclear_c S _ fun p _ ↦ coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      BddAbove (Set.range fun S : Finset (PontryaginDual (ideleClassNorm F).ker × ℤ) ↦
        traceNorm ⟨∑ p ∈ S, coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          sum_mem_nuclear_c S _ fun p _ ↦ coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      BddAbove (Set.range fun S : Finset (PontryaginDual (ideleClassNorm F).ker × ℤ) ↦
        traceNorm ⟨∑ p ∈ S, coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          sum_mem_nuclear_c S _ fun p _ ↦ coshAmbientClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) := by
  classical
  obtain ⟨K, hdisj, hcov, hcomp, hsum_g, hsum_s, hsum_a⟩ :=
    coshSpectralStripGeometricBlocks_clusters_summable a hα hs φ χ hχ x Λ hb hj
  refine ⟨K, hdisj, hcov, hcomp, ?_, ?_, ?_⟩
  · simpa using bddAbove_partialSum_traceNorm_of_summable
      (fun p ↦ coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p))
      (fun p ↦ coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)) hsum_g
  · simpa using bddAbove_partialSum_traceNorm_of_summable
      (fun p ↦ coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p))
      (fun p ↦ coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)) hsum_s
  · simpa using bddAbove_partialSum_traceNorm_of_summable
      (fun p ↦ coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K p))
      (fun p ↦ coshAmbientClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)) hsum_a

/-- Packaged positive-width (`α ≥ 0`, `s ≥ 0`) cluster decomposition of `coshTestAction hα hs φ`,
recording pairwise disjointness, covering, component preservation, geometric/spectral/ambient
splitting, cluster trace-norm summability, and boundedness of finite partial-sum trace norms. -/
theorem coshSpectralStripAmbientKernel_clusters_exists
    (a : ℝ) {α s : ℝ} (hα : 0 ≤ α) (hs : 0 ≤ s)
    (φ : BruhatCompactSupport (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    (χ : PontryaginDual (ideleClassNorm F).ker →
      PontryaginDual (IdeleClassGroup (NumberField.RingOfIntegers F) F))
    (hχ : IsSpectralBasepointChoice χ)
    (x : SpectralStripJetIndex (F := F) χ a α s →
      spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs)
    (Λ : SpectralStripJetIndex (F := F) χ a α s →
      StrongDual ℂ (spectralSobolevQuotient F a ((neg_nonpos.mpr hα).trans hα) hs))
    (hb : IsSpectralMarkushevichBasis x Λ)
    (hj : ∀ j, spectralSobolevDualEmbedding F a ((neg_nonpos.mpr hα).trans hα) hs (Λ j) =
      (spectralStripJet_memLp (F := F) χ hα hs j).toLp
        (spectralZeroJet (F := F) (χ j.val.1) j.val.2.1 j.val.2.2.1 j.val.2.2.2)) :
    ∃ K : (PontryaginDual (ideleClassNorm F).ker × ℤ) → Finset (CoshStripZero (F := F) χ a α),
      (∀ p₁ p₂, p₁ ≠ p₂ → Disjoint (K p₁) (K p₂)) ∧
      (∀ z : CoshStripZero (F := F) χ a α, ∃ p, z ∈ K p) ∧
      (∀ p z, z ∈ K p → z.val.1 = p.1) ∧
      (∀ p, coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K p) =
        coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p) +
          coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p)) ∧
      Summable (fun p ↦ traceNorm ⟨coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p),
        coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      Summable (fun p ↦ traceNorm ⟨coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p),
        coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      Summable (fun p ↦ traceNorm ⟨coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K p),
        coshAmbientClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      BddAbove (Set.range fun S : Finset (PontryaginDual (ideleClassNorm F).ker × ℤ) ↦
        traceNorm ⟨∑ p ∈ S, coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          sum_mem_nuclear_c S _ fun p _ ↦ coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      BddAbove (Set.range fun S : Finset (PontryaginDual (ideleClassNorm F).ker × ℤ) ↦
        traceNorm ⟨∑ p ∈ S, coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          sum_mem_nuclear_c S _ fun p _ ↦ coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) ∧
      BddAbove (Set.range fun S : Finset (PontryaginDual (ideleClassNorm F).ker × ℤ) ↦
        traceNorm ⟨∑ p ∈ S, coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K p),
          sum_mem_nuclear_c S _ fun p _ ↦ coshAmbientClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)⟩) := by
  classical
  obtain ⟨K, hdisj, hcov, hcomp, hsum_g, hsum_s, hsum_a⟩ :=
    coshSpectralStripGeometricBlocks_clusters_summable a hα hs φ χ hχ x Λ hb hj
  refine ⟨K, hdisj, hcov, hcomp, fun p ↦ coshAmbientClusterBlock_eq_add a hα hs φ χ x Λ (K p),
    hsum_g, hsum_s, hsum_a, ?_, ?_, ?_⟩
  · simpa using bddAbove_partialSum_traceNorm_of_summable
      (fun p ↦ coshGeometricClusterBlock (F := F) a hα hs φ χ x Λ (K p))
      (fun p ↦ coshGeometricClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)) hsum_g
  · simpa using bddAbove_partialSum_traceNorm_of_summable
      (fun p ↦ coshSpectralClusterBlock (F := F) a hα hs φ χ x Λ (K p))
      (fun p ↦ coshSpectralClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)) hsum_s
  · simpa using bddAbove_partialSum_traceNorm_of_summable
      (fun p ↦ coshAmbientClusterBlock (F := F) a hα hs φ χ x Λ (K p))
      (fun p ↦ coshAmbientClusterBlock_mem_nuclear a hα hs φ χ x Λ (K p)) hsum_a

end ArbitraryBasepointTheorems

end RiemannMasullo.Isolated.CoshPositiveWidth
