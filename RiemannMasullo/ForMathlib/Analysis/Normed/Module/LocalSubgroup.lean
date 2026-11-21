module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Closed local subgroups of finite-dimensional real normed spaces

A closed symmetric set containing zero and closed under addition inside a ball agrees with a
linear subspace on a smaller ball.
-/

@[expose] public section

open Metric Set Filter Topology Submodule Module

namespace RiemannMasullo

open Metric Set Filter Topology Submodule Module

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

private theorem good_sup_localSubgroup {R : ℝ} (hR : 0 < R) {A : Set E}
    (hAdd : ∀ x ∈ A, ∀ y ∈ A, ‖x + y‖ ≤ R → x + y ∈ A)
    {W1 W2 : Submodule ℝ E}
    (h1 : ∃ ε > 0, (W1 : Set E) ∩ closedBall (0 : E) ε ⊆ A)
    (h2 : ∃ ε > 0, (W2 : Set E) ∩ closedBall (0 : E) ε ⊆ A) :
    ∃ ε > 0, ((W1 ⊔ W2 : Submodule ℝ E) : Set E) ∩ closedBall (0 : E) ε ⊆ A := by
  classical
  obtain ⟨ε1, hε1, hA1⟩ := h1
  obtain ⟨ε2, hε2, hA2⟩ := h2
  let Ssub := W1 ⊔ W2
  let addMap : W1 × W2 →ₗ[ℝ] Ssub :=
    (W1.subtype.coprod W2.subtype).codRestrict Ssub fun p ↦ add_mem_sup p.1.property p.2.property
  have haddSurj : Function.Surjective addMap := by
    intro z
    obtain ⟨v, hv, w, hw, hz⟩ := mem_sup.mp z.property
    refine ⟨(⟨v, hv⟩, ⟨w, hw⟩), Subtype.ext hz⟩
  obtain ⟨sec, hsec⟩ :=
    addMap.exists_rightInverse_of_surjective (LinearMap.range_eq_top_of_surjective _ haddSurj)
  let secL : Ssub →L[ℝ] W1 × W2 := ⟨sec, sec.continuous_of_finiteDimensional⟩
  let C : ℝ := ‖secL‖ + 1
  have hC : 0 < C := by linarith [norm_nonneg secL]
  have hC1 : 1 ≤ C := by linarith [norm_nonneg secL]
  let ε := min ε1 (min ε2 R) / C
  have hε : 0 < ε := div_pos (lt_min hε1 (lt_min hε2 hR)) hC
  have hεR : ε ≤ R := by
    have hmin : min ε1 (min ε2 R) ≤ R := (min_le_right _ _).trans (min_le_right _ _)
    exact (div_le_iff₀ hC).mpr (hmin.trans (le_mul_of_one_le_right (le_of_lt hR) hC1))
  refine ⟨ε, hε, fun x hx ↦ ?_⟩
  let z : Ssub := ⟨x, hx.1⟩
  have hzε : ‖x‖ ≤ ε := by simpa using (mem_closedBall_iff_norm.mp hx.2)
  have hsecz : addMap (sec z) = z := congr($hsec z)
  let w1 : W1 := (sec z).1
  let w2 : W2 := (sec z).2
  have hsumz : (w1 : E) + (w2 : E) = x := by
    have h1 : addMap (w1, w2) = z := by simpa [w1, w2] using hsecz
    have h2 : ((addMap (w1, w2) : Ssub) : E) = (w1 : E) + (w2 : E) := by
      rfl
    simpa [h2, z] using congrArg Subtype.val h1
  have hw1n : ‖(w1 : E)‖ ≤ min ε1 (min ε2 R) := by
    have hle : ‖(w1 : E)‖ ≤ ‖secL z‖ := by simpa [w1, secL] using norm_fst_le (secL z)
    have hop : ‖secL z‖ ≤ ‖secL‖ * ‖(z : E)‖ := secL.le_opNorm z
    have : ‖(w1 : E)‖ ≤ ‖secL‖ * ε :=
      le_trans hle (le_trans hop (mul_le_mul_of_nonneg_left (by simpa [z] using hzε) (norm_nonneg secL)))
    have hfrac : ‖secL‖ / C ≤ 1 := by rw [div_le_one hC]; linarith
    calc
      ‖(w1 : E)‖ ≤ ‖secL‖ * ε := this
      _ = ‖secL‖ / C * min ε1 (min ε2 R) := by
        simp only [ε]
        ring
      _ ≤ 1 * min ε1 (min ε2 R) := by gcongr
      _ = min ε1 (min ε2 R) := by simp
  have hw2n : ‖(w2 : E)‖ ≤ min ε1 (min ε2 R) := by
    have hle : ‖(w2 : E)‖ ≤ ‖secL z‖ := by simpa [w2, secL] using norm_snd_le (secL z)
    have hop : ‖secL z‖ ≤ ‖secL‖ * ‖(z : E)‖ := secL.le_opNorm z
    have : ‖(w2 : E)‖ ≤ ‖secL‖ * ε :=
      le_trans hle (le_trans hop (mul_le_mul_of_nonneg_left (by simpa [z] using hzε) (norm_nonneg secL)))
    have hfrac : ‖secL‖ / C ≤ 1 := by rw [div_le_one hC]; linarith
    calc
      ‖(w2 : E)‖ ≤ ‖secL‖ * ε := this
      _ = ‖secL‖ / C * min ε1 (min ε2 R) := by
        simp only [ε]
        ring
      _ ≤ 1 * min ε1 (min ε2 R) := by gcongr
      _ = min ε1 (min ε2 R) := by simp
  have hw1A : (w1 : E) ∈ A :=
    hA1 ⟨w1.property, mem_closedBall_iff_norm.mpr (by simpa using hw1n.trans (min_le_left _ _))⟩
  have hw2A : (w2 : E) ∈ A :=
    hA2 ⟨w2.property, mem_closedBall_iff_norm.mpr
      (by simpa using hw2n.trans ((min_le_right _ _).trans (min_le_left _ _)))⟩
  have hnorm : ‖(w1 : E) + (w2 : E)‖ ≤ R := by simpa [hsumz] using hzε.trans hεR
  simpa [hsumz] using hAdd _ hw1A _ hw2A hnorm

/-- A closed local subgroup of a finite-dimensional real normed space: a closed symmetric set
containing zero and closed under sums of norm at most `R` agrees with a linear subspace on
some closed ball of radius at most `R`. -/
public theorem exists_subspace_ball_eq_of_localSubgroup {R : ℝ} (hR : 0 < R) {A : Set E}
    (hA : IsClosed A) (hA0 : (0 : E) ∈ A) (hAsym : ∀ x ∈ A, -x ∈ A)
    (hAdd : ∀ x ∈ A, ∀ y ∈ A, ‖x + y‖ ≤ R → x + y ∈ A) :
    ∃ (V : Submodule ℝ E) (ε : ℝ), 0 < ε ∧ ε ≤ R ∧
      A ∩ closedBall (0 : E) ε = (V : Set E) ∩ closedBall (0 : E) ε := by
  have : ProperSpace E := FiniteDimensional.proper ℝ E
  classical
  let good (W : Submodule ℝ E) : Prop :=
    ∃ ε > 0, (W : Set E) ∩ closedBall (0 : E) ε ⊆ A
  have good_bot : good ⊥ := ⟨R, hR, fun x hx ↦ by
    have : x = 0 := by simpa using hx.1
    simpa [this] using hA0⟩
  let S : Set ℕ := {d | ∃ W : Submodule ℝ E, finrank ℝ W = d ∧ good W}
  have hSne : S.Nonempty := ⟨0, ⊥, finrank_bot ℝ E, good_bot⟩
  have hSbd : BddAbove S := ⟨finrank ℝ E, fun d hd ↦ by
    obtain ⟨W, hW, _⟩ := hd
    simpa [hW] using W.finrank_le⟩
  let d := sSup S
  have hdS : d ∈ S := Nat.sSup_mem hSne hSbd
  obtain ⟨V, hVrank, hVgood⟩ := hdS
  have hVg : good V := hVgood
  obtain ⟨εV, hεV, hVsub⟩ := hVgood
  obtain ⟨F, hF⟩ := V.exists_isCompl
  have hFclosed : IsClosed (F : Set E) := F.isClosed_of_finiteDimensional
  by_cases hclose : ∃ ε > 0, A ∩ closedBall (0 : E) ε ⊆ (V : Set E)
  · obtain ⟨ε0, hε0pos, hAsub⟩ := hclose
    let ε := min ε0 (min εV R)
    have hε : 0 < ε := lt_min hε0pos (lt_min hεV hR)
    have hε0 : ε ≤ ε0 := min_le_left _ _
    have hεVle : ε ≤ εV := (min_le_right _ _).trans (min_le_left _ _)
    have hεR : ε ≤ R := (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨V, ε, hε, hεR, ?_⟩
    ext x
    constructor
    · intro hx
      exact ⟨hAsub ⟨hx.1, closedBall_subset_closedBall hε0 hx.2⟩, hx.2⟩
    · intro hx
      exact ⟨hVsub ⟨hx.1, closedBall_subset_closedBall hεVle hx.2⟩, hx.2⟩
  · exfalso
    have hseq : ∀ n : ℕ, ∃ x : E, x ∈ A ∧ ‖x‖ ≤ 1 / (n + 1 : ℝ) ∧ x ∉ (V : Set E) := by
      intro n
      have hεn : 0 < (1 : ℝ) / (n + 1) := by positivity
      have hnot : ¬ A ∩ closedBall (0 : E) (1 / (n + 1 : ℝ)) ⊆ (V : Set E) := by
        intro hsub
        exact hclose ⟨_, hεn, hsub⟩
      obtain ⟨x, hx, hxnot⟩ := Set.not_subset.mp hnot
      exact ⟨x, hx.1, by simpa using (mem_closedBall_iff_norm.mp hx.2), hxnot⟩
    choose a haA haNorm haNot using hseq
    have nsmul_cast (k : ℕ) (y : E) : k • y = (k : ℝ) • y := by
      induction k with
      | zero => simp
      | succ k ih => rw [succ_nsmul, Nat.cast_succ, add_smul, one_smul, ih]
    have ha0 : Tendsto a atTop (𝓝 (0 : E)) := by
      have hg : Tendsto (fun n : ℕ ↦ (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      exact squeeze_zero_norm haNorm hg
    let proj := V.projection F hF
    have hprojcont : Continuous proj := proj.continuous_of_finiteDimensional
    let f : ℕ → E := fun n ↦ a n - proj (a n)
    have hfF : ∀ n, f n ∈ F := fun n ↦ sub_projection_mem hF (a n)
    have hf0 : Tendsto f atTop (𝓝 (0 : E)) := by
      have hproj0 := (hprojcont.tendsto (0 : E)).comp ha0
      simp only [map_zero, Function.comp_def] at hproj0
      simpa [f] using ha0.sub hproj0
    have hfne : ∀ n, f n ≠ 0 := by
      intro n hz
      apply haNot n
      have : a n = proj (a n) := sub_eq_zero.mp (by simpa [f] using hz)
      rw [this]
      exact projection_apply_mem hF (a n)
    have hEv : ∀ᶠ n in atTop, f n ∈ A := by
      have hproj0 := (hprojcont.tendsto (0 : E)).comp ha0
      simp only [map_zero, Function.comp_def] at hproj0
      filter_upwards [hf0 (closedBall_mem_nhds (0 : E) hR),
        hproj0 (closedBall_mem_nhds (0 : E) hεV)] with n hfn hpn
      have hpnA : proj (a n) ∈ A := hVsub ⟨projection_apply_mem hF (a n), hpn⟩
      have hneg : -(proj (a n)) ∈ A := hAsym _ hpnA
      have hsum : ‖a n + -(proj (a n))‖ ≤ R := by
        simpa [sub_eq_add_neg, f] using (mem_closedBall_iff_norm.mp hfn)
      simpa [f, sub_eq_add_neg] using hAdd _ (haA n) _ hneg hsum
    rw [eventually_atTop] at hEv
    obtain ⟨N, hN⟩ := hEv
    let g : ℕ → E := fun n ↦ f (n + N)
    have hgA : ∀ n, g n ∈ A := fun n ↦ hN _ (Nat.le_add_left _ _)
    have hgF : ∀ n, g n ∈ F := fun n ↦ hfF _
    have hgne : ∀ n, g n ≠ 0 := fun n ↦ hfne _
    have hg0 : Tendsto g atTop (𝓝 (0 : E)) := hf0.comp (tendsto_add_atTop_nat N)
    let uDir : ℕ → E := fun n ↦ (‖g n‖⁻¹) • g n
    have huDirF : ∀ n, uDir n ∈ F := fun n ↦ F.smul_mem _ (hgF n)
    have huDirB : ∀ n, uDir n ∈ closedBall (0 : E) 1 := fun n ↦ by
      rw [mem_closedBall_iff_norm]
      simp [uDir, norm_smul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hgne n))]
    obtain ⟨u, -, φ, hφ, hφu⟩ :=
      tendsto_subseq_of_bounded (isBounded_closedBall) huDirB
    have huNorm : ‖u‖ = 1 := by
      have hlim : Tendsto (fun n ↦ ‖uDir (φ n)‖) atTop (𝓝 ‖u‖) :=
        (continuous_norm.tendsto u).comp hφu
      have hconst : Tendsto (fun n ↦ ‖uDir (φ n)‖) atTop (𝓝 1) := by
        have : (fun n ↦ ‖uDir (φ n)‖) = fun _ ↦ (1 : ℝ) := by
          funext n
          simp [uDir, norm_smul, norm_inv, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hgne _))]
        rw [this]; exact tendsto_const_nhds
      exact tendsto_nhds_unique hlim hconst
    have huF : u ∈ F :=
      hFclosed.mem_of_tendsto hφu (Eventually.of_forall fun n ↦ huDirF (φ n))
    have hu_ne : u ≠ 0 := by
      intro h
      simp [h] at huNorm
    let gφ : ℕ → E := g ∘ φ
    have hgφ0 : Tendsto gφ atTop (𝓝 0) := hg0.comp hφ.tendsto_atTop
    have hgφA : ∀ n, gφ n ∈ A := fun n ↦ hgA _
    have hgφne : ∀ n, gφ n ≠ 0 := fun n ↦ hgne _
    have hdir : Tendsto (fun n ↦ (‖gφ n‖⁻¹) • gφ n) atTop (𝓝 u) := hφu
    have hseg : ∀ t : ℝ, |t| ≤ R → t • u ∈ A := by
      intro t ht
      wlog ht0 : 0 ≤ t generalizing t
      · have htneg : t < 0 := lt_of_not_ge ht0
        have := this (-t) (by simpa using ht) (neg_nonneg.mpr htneg.le)
        simpa using hAsym _ this
      have hmul_mem : ∀ (n k : ℕ), (k : ℝ) * ‖gφ n‖ ≤ R → k • gφ n ∈ A := by
        intro n k hk
        induction k with
        | zero => simpa using hA0
        | succ k ih =>
          have hkR : (k : ℝ) * ‖gφ n‖ ≤ R := by
            refine le_trans ?_ hk
            gcongr
            exact_mod_cast Nat.le_succ k
          have hkA := ih hkR
          have hsum : ‖k • gφ n + gφ n‖ ≤ R := by
            rw [← succ_nsmul, nsmul_cast, norm_smul, Real.norm_natCast]
            exact hk
          simpa [succ_nsmul] using hAdd _ hkA _ (hgφA n) hsum
      let m : ℕ → ℕ := fun n ↦ Int.toNat (Int.floor (t / ‖gφ n‖))
      have hm_le : ∀ n, (m n : ℝ) * ‖gφ n‖ ≤ t := by
        intro n
        have hfloor := Int.floor_le (t / ‖gφ n‖)
        have hm0 : 0 ≤ Int.floor (t / ‖gφ n‖) :=
          Int.floor_nonneg.mpr (div_nonneg ht0 (norm_nonneg (gφ n)))
        have hmint : (m n : ℤ) = Int.floor (t / ‖gφ n‖) := by
          simpa [m] using (Int.toNat_of_nonneg hm0).symm
        have hmr : (m n : ℝ) = (Int.floor (t / ‖gφ n‖) : ℝ) := by exact_mod_cast hmint
        rw [hmr]
        have := mul_le_mul_of_nonneg_right hfloor (norm_nonneg (gφ n))
        rwa [div_mul_cancel₀ _ (norm_ne_zero_iff.mpr (hgφne n))] at this
      have hm_gt : ∀ n, t - ‖gφ n‖ < (m n : ℝ) * ‖gφ n‖ := by
        intro n
        have hgt := Int.lt_floor_add_one (t / ‖gφ n‖)
        have hsub := Int.sub_one_lt_floor (t / ‖gφ n‖)
        have hm0 : 0 ≤ Int.floor (t / ‖gφ n‖) :=
          Int.floor_nonneg.mpr (div_nonneg ht0 (norm_nonneg (gφ n)))
        have hmint : (m n : ℤ) = Int.floor (t / ‖gφ n‖) := by
          simpa [m] using (Int.toNat_of_nonneg hm0).symm
        have hmr : (m n : ℝ) = (Int.floor (t / ‖gφ n‖) : ℝ) := by exact_mod_cast hmint
        rw [hmr]
        have hpos : 0 < ‖gφ n‖ := norm_pos_iff.mpr (hgφne n)
        have := mul_lt_mul_of_pos_right hsub hpos
        have hne : ‖gφ n‖ ≠ 0 := norm_ne_zero_iff.mpr (hgφne n)
        calc
          t - ‖gφ n‖ = (t / ‖gφ n‖ - 1) * ‖gφ n‖ := by field_simp [hne]
          _ < (Int.floor (t / ‖gφ n‖) : ℝ) * ‖gφ n‖ := this
      have htle : t ≤ R := by simpa [abs_of_nonneg ht0] using ht
      have hmA : ∀ n, m n • gφ n ∈ A := fun n ↦
        hmul_mem n (m n) ((hm_le n).trans htle)
      have hcoeff : Tendsto (fun n ↦ (m n : ℝ) * ‖gφ n‖) atTop (𝓝 t) := by
        refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds
          (fun n ↦ le_of_lt (hm_gt n)) hm_le
        simpa using (tendsto_const_nhds.sub ((continuous_norm.tendsto (0 : E)).comp hgφ0))
      have hEq : ∀ n, ((m n : ℝ) * ‖gφ n‖) • ((‖gφ n‖⁻¹) • gφ n) = (m n : ℝ) • gφ n := by
        intro n
        rw [smul_smul]
        congr 1
        field_simp [norm_ne_zero_iff.mpr (hgφne n)]
      have htend : Tendsto (fun n ↦ (m n : ℝ) • gφ n) atTop (𝓝 (t • u)) := by
        have := hcoeff.smul hdir
        simpa [hEq] using this
      have htend' : Tendsto (fun n ↦ m n • gφ n) atTop (𝓝 (t • u)) := by
        have hfun : (fun n ↦ m n • gφ n) = fun n ↦ (m n : ℝ) • gφ n := by
          funext n; exact (nsmul_cast (m n) (gφ n))
        simpa [hfun] using htend
      exact hA.mem_of_tendsto htend' (Eventually.of_forall hmA)
    let L : Submodule ℝ E := ℝ ∙ u
    have hLgood : good L := by
      refine ⟨R, hR, fun z hz ↦ ?_⟩
      obtain ⟨t, rfl⟩ := mem_span_singleton.mp hz.1
      have htabs : |t| ≤ R := by
        have hnorm : ‖t • u‖ ≤ R := by simpa using (mem_closedBall_iff_norm.mp hz.2)
        simpa [norm_smul, huNorm, Real.norm_eq_abs] using hnorm
      exact hseg t htabs
    have hdisj : V ⊓ L = ⊥ := by
      ext x
      constructor
      · intro hx
        obtain ⟨t, ht⟩ := mem_span_singleton.mp hx.2
        by_cases ht0 : t = 0
        · have : x = 0 := by simpa [ht0] using ht.symm
          subst this
          rfl
        · exfalso
          have huV : u ∈ V := by
            have hx' : t • u ∈ V := by simpa [ht] using hx.1
            have : u = t⁻¹ • (t • u) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
            rw [this]
            exact V.smul_mem _ hx'
          have : u ∈ (⊥ : Submodule ℝ E) := by
            rw [← hF.inf_eq_bot]
            exact ⟨huV, huF⟩
          exact hu_ne (by simpa using this)
      · intro hx
        rw [Submodule.mem_bot] at hx
        subst hx
        exact zero_mem _
    let W := V ⊔ L
    have hLrank : finrank ℝ W = finrank ℝ V + 1 := by
      have hsum := finrank_sup_add_finrank_inf_eq V L
      have hrank1 : finrank ℝ L = 1 := finrank_span_singleton hu_ne
      rw [hdisj, finrank_bot ℝ E, add_zero, hrank1] at hsum
      simpa [W] using hsum
    have hsup : good W := good_sup_localSubgroup hR hAdd hVg hLgood
    have hbig : finrank ℝ W ∈ S := ⟨W, rfl, hsup⟩
    have hle : finrank ℝ W ≤ d := le_csSup hSbd hbig
    have hgt : d < finrank ℝ W := by
      rw [hLrank, hVrank]
      exact Nat.lt_succ_self _
    exact not_lt_of_ge hle hgt

end

end RiemannMasullo
