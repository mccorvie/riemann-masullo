module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3
import RiemannMasullo.Ch10_TraceSpectral.Sec1
import Mathlib.Analysis.Complex.ExponentialBounds
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.External.ZetaLab.RHHeight.Main

/-! # Further assertions in the proofs of §10.3 that are false as printed -/

@[expose] public noncomputable section

open Filter MeasureTheory NumberField Set
open scoped NNReal Topology

namespace RiemannMasullo

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

local notation "C𝔽(" F ")" => IdeleClassGroup (𝓞 F) F
local notation "C₁(" F ")" => (ideleClassNorm F).ker
local notation "shift(" b ", " t ")" => ((b : ℝ) : ℂ) + (t : ℂ) * Complex.I
local notation "orderAt(" χ ", " z ")" => meromorphicOrderAt (continuedCompletedHeckeL χ) z
local notation "lineZeros(" χ ", " a ")" => {t : ℝ | 0 < orderAt(χ, shift(a, t))}
local notation "floorCut(" s ")" => Nat.floor ((s - 1) / 2 + 1)

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
As printed: the smallest interval containing the selected ordinates in each active character
can be enlarged at both ends by a common positive amount while still containing exactly
those zeros on the line. The finite selections are stated one character at a time.
See `spectralConvolutionFiniteSum` and ERRATA F178. -/
def Printed.spectralLineSelection_exists_isolatingInterval : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty),
      (K : Set ℝ) ⊆ lineZeros(χ ω, a) →
      ∃ ε : ℝ, 0 < ε ∧
        Icc (K.min' hK - ε) (K.max' hK + ε) ∩ lineZeros(χ ω, a) = (K : Set ℝ)

/-- Three ordered critical-line zeros of the ordinary Riemann zeta function suffice
for the interval counterexample. This is a finite consequence of Hardy's theorem. -/
private theorem spectralLineSelection_three_zeta_zeros :
    ∃ u v w : ℝ, u < v ∧ v < w ∧ riemannZeta (shift(1 / 2, u)) = 0 ∧
      riemannZeta (shift(1 / 2, v)) = 0 ∧ riemannZeta (shift(1 / 2, w)) = 0 := by
  sorry

/-- A critical-line zero of ordinary zeta has positive order for the completed
L-function of the trivial rational character. -/
private theorem spectralLineSelection_mem_lineZeros (t : ℝ)
    (ht : riemannZeta (shift(1 / 2, t)) = 0) :
    t ∈ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2) := by
  let z : ℂ := shift(1 / 2, t)
  have hre : z.re = 1 / 2 := by simp [z]
  have hne : z ≠ 1 := fun h ↦ by norm_num [h] at hre
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  change 0 < meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) z
  rw [← meromorphicOrderAt_finiteHeckeL_continuation _ hm (fun s ↦
    (dedekindZeta_rat_eq_riemannZeta s.property).symm.trans
      (finiteHeckeL_one_eq_dedekindZeta (K := ℚ) s).symm) (by rw [hre]; norm_num)]
  apply (tendsto_zero_iff_meromorphicOrderAt_pos (hm z (mem_univ z))).mp
  change riemannZeta z = 0 at ht
  rw [← ht]
  exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt

/-- Paper: Theorem 10.3.1.1, interval choice before (10.3.1.15), p. 450.
Use F = ℚ, the trivial base character and a = 1/2. Let K consist of the first and third
distinct positive critical-line zeta ordinates. The omitted second ordinate lies inside
the closed interval for every ε > 0. -/
theorem Printed.spectralLineSelection_exists_isolatingInterval_false :
    ¬ Printed.spectralLineSelection_exists_isolatingInterval := by
  classical
  intro hall
  obtain ⟨χ, hχ⟩ := exists_spectralBasepointChoice ℚ
  let χ' := Function.update χ 1 (1 : PontryaginDual C𝔽(ℚ))
  have hχ' : IsSpectralBasepointChoice χ' := by
    intro ω
    by_cases h : ω = 1
    · subst ω
      rw [show χ' 1 = 1 from Function.update_self ..]
      rfl
    · simpa [χ', Function.update_of_ne h] using hχ ω
  obtain ⟨u, v, w, huv, hvw, hu, hv, hw⟩ := spectralLineSelection_three_zeta_zeros
  let K : Finset ℝ := {u, w}
  have huK : u ∈ K := by simp [K]
  have hwK : w ∈ K := by simp [K]
  have hzeros : (K : Set ℝ) ⊆ lineZeros((1 : PontryaginDual C𝔽(ℚ)), 1 / 2) := by
    intro t ht
    rcases (show t = u ∨ t = w by simpa [K] using ht) with rfl | rfl
    · exact spectralLineSelection_mem_lineZeros _ hu
    · exact spectralLineSelection_mem_lineZeros _ hw
  have htriv : χ' 1 = 1 := Function.update_self ..
  obtain ⟨ε, hε, hK⟩ := hall ℚ χ' hχ' (1 / 2) 1 K ⟨u, huK⟩ (by simpa only [htriv] using hzeros)
  rw [htriv] at hK
  have hvK : v ∈ (K : Set ℝ) := by
    rw [← hK]
    refine ⟨⟨?_, ?_⟩, spectralLineSelection_mem_lineZeros _ hv⟩
    · exact (sub_le_self _ hε.le).trans ((K.min'_le u huK).trans huv.le)
    · exact hvw.le.trans ((K.le_max' w hwK).trans (le_add_of_nonneg_right hε.le))
  simp [K, huv.ne', hvw.ne] at hvK

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
As printed: in each such interval the number of jets is at most the floor cutoff times the
logarithm of the greater of the absolute values of the endpoints. The count includes all
the orders below the truncated multiplicity of each zero in the interval.
See `spectralConvolutionFiniteSum` and ERRATA F180. -/
def Printed.spectralLineBand_jetCount_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a s : ℝ), 1 < s → ∀ (ω : PontryaginDual C₁(F)) (K : Finset ℝ) (hK : K.Nonempty)
      (ε : ℝ), 0 < ε →
      let l := K.min' hK - ε
      let r := K.max' hK + ε
      Icc l r ∩ lineZeros(χ ω, a) = (K : Set ℝ) →
      ((∑ t ∈ K, min ((orderAt(χ ω, shift(a, t))).untop₀.toNat) floorCut(s) : ℕ) : ℝ) ≤
        (floorCut(s) : ℝ) * Real.log (max |l| |r|)

/-- **At least ten zeros on the critical line below height 50**: ten distinct ordinates
`0 < t_0 < t_1 < ⋯ < t_9 < 50` with `ζ(1/2 + i t_k) = 0`. Each `t_k` lies in the two-decimal
interval of the corresponding `zero_in_*` theorem. Adapted from Thomas Lince’s
`HardyTenZeros.ten_zeros_on_line_below_fifty` (MIT), retaining the bounds at 22. -/
private theorem spectralLineBand_jetCount_le_false_brackets :
    ∃ ts : Fin 10 → ℝ, ts 1 < 22 ∧ 22 < ts 2 ∧ StrictMono ts ∧
      ∀ k, 0 < ts k ∧ ts k < 50 ∧ riemannZeta (1 / 2 + ts k * Complex.I) = 0 := by
  obtain ⟨t0, h0, z0⟩ := HardyFirstZero.first_zero_on_line
  obtain ⟨t1, h1, z1⟩ := HardyTenZeros.zero_in_2102
  obtain ⟨t2, h2, z2⟩ := HardyTenZeros.zero_in_2501
  obtain ⟨t3, h3, z3⟩ := HardyTenZeros.zero_in_3042
  obtain ⟨t4, h4, z4⟩ := HardyTenZeros.zero_in_3293
  obtain ⟨t5, h5, z5⟩ := HardyTenZeros.zero_in_3758
  obtain ⟨t6, h6, z6⟩ := HardyTenZeros.zero_in_4091
  obtain ⟨t7, h7, z7⟩ := HardyTenZeros.zero_in_4332
  obtain ⟨t8, h8, z8⟩ := HardyTenZeros.zero_in_4800
  obtain ⟨t9, h9, z9⟩ := HardyTenZeros.zero_in_4977
  obtain ⟨l0, u0⟩ := h0
  obtain ⟨l1, u1⟩ := h1
  obtain ⟨l2, u2⟩ := h2
  obtain ⟨l3, u3⟩ := h3
  obtain ⟨l4, u4⟩ := h4
  obtain ⟨l5, u5⟩ := h5
  obtain ⟨l6, u6⟩ := h6
  obtain ⟨l7, u7⟩ := h7
  obtain ⟨l8, u8⟩ := h8
  obtain ⟨l9, u9⟩ := h9
  refine ⟨![t0, t1, t2, t3, t4, t5, t6, t7, t8, t9], ?_, ?_, ?_, ?_⟩
  · change t1 < 22
    linarith
  · change 22 < t2
    linarith
  · refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i <;> simp <;> linarith
  · intro k
    simp only [one_div] at z0 z1 z2 z3 z4 z5 z6 z7 z8 z9
    fin_cases k <;> simp <;> refine ⟨by linarith, by linarith, by assumption⟩

/-- The ten certified ordinates exhaust the count to height fifty. Only the first
two have height at most twenty-two. -/
private theorem spectralLineBand_jetCount_le_false_positive
    (ts : Fin 10 → ℝ) (hmono : StrictMono ts)
    (hts : ∀ i, 0 < ts i ∧ ts i < 50 ∧ riemannZeta (1 / 2 + ts i * Complex.I) = 0)
    (hthird : 22 < ts 2) (hcount : RHHeight.ZeroCountUpTo 50 10)
    (hsimple : RHHeight.RHHeight50) {t : ℝ} (ht : 0 < t) (ht' : t ≤ 22) :
    analyticOrderAt riemannZeta (1 / 2 + t * Complex.I) =
      if t = ts 0 ∨ t = ts 1 then 1 else 0 := by
  classical
  let point (i : Fin 10) : ℂ := 1 / 2 + ts i * Complex.I
  have hinj : Function.Injective point := by
    intro i j h
    apply hmono.injective
    simpa [point] using congrArg Complex.im h
  have hsub : Set.range point ⊆ RHHeight.stripZerosUpTo 50 := by
    rintro _ ⟨i, rfl⟩
    refine ⟨(hts i).2.2, by norm_num [point], by norm_num [point], ?_, ?_⟩
    · simpa [point] using (hts i).1
    · simpa [point] using (hts i).2.1.le
  have hc : (RHHeight.stripZerosUpTo 50).ncard = 10 := hcount
  have heq := Set.eq_of_subset_of_ncard_le hsub
    (by simp [Set.ncard_range_of_injective hinj, hc])
    (Set.finite_of_ncard_ne_zero (by omega))
  let z : ℂ := 1 / 2 + t * Complex.I
  have hEq : riemannZeta z = 0 ↔ t = ts 0 ∨ t = ts 1 := by
    constructor
    · intro hz
      have hzmem : z ∈ RHHeight.stripZerosUpTo 50 :=
        ⟨hz, by norm_num [z], by norm_num [z], by simpa [z] using ht,
          by simpa [z] using (show t ≤ 50 by linarith)⟩
      rw [← heq] at hzmem
      obtain ⟨i, hi⟩ := hzmem
      have hit : ts i = t := by simpa [z, point] using congrArg Complex.im hi
      have hlt : i < 2 := by
        by_contra! hge
        have := hmono.monotone hge
        linarith
      have : i = 0 ∨ i = 1 := by omega
      rcases this with rfl | rfl
      · exact Or.inl hit.symm
      · exact Or.inr hit.symm
    · rintro (rfl | rfl)
      · exact (hts 0).2.2
      · exact (hts 1).2.2
  split_ifs with h
  · exact (hsimple z (hEq.mpr h) (by norm_num [z]) (by norm_num [z])
      (by simpa [z] using ht) (by simpa [z] using (show t ≤ 50 by linarith))).2
  · apply AnalyticAt.analyticOrderAt_eq_zero _ |>.mpr
    · exact fun hz ↦ h (hEq.mp hz)
    · apply analyticOn_riemannZeta
      intro hz
      have := congrArg Complex.re (show z = 1 from hz)
      norm_num [z] at this

/-- The first Euler–Maclaurin block at the central point excludes a real zero.
Take the boundary limit of the quarter-plane error bound. -/
private theorem spectralLineBand_jetCount_le_false_center
    (herr : ∀ z : ℂ, 0 < z.re → 0 < z.im →
      ‖riemannZeta z - (z + 2) * (z + 3) / (12 * (z - 1))‖ ≤
        ‖z * (z + 1) * (z + 2) * (z + 3)‖ * (1 + 1 / (z.re + 3)) / 720) :
    riemannZeta (1 / 2 : ℂ) ≠ 0 := by
  let z (t : ℝ) : ℂ := 1 / 2 + t * Complex.I
  have hz : ContinuousAt z 0 := by dsimp [z]; fun_prop
  have hzeta := (differentiableAt_riemannZeta (s := z 0) (by norm_num [z])).continuousAt.comp hz
  have h₁ : ContinuousAt (fun t ↦ ‖riemannZeta (z t) -
      (z t + 2) * (z t + 3) / (12 * (z t - 1))‖) 0 := by
    fun_prop (disch := norm_num [z])
  have h₂ : ContinuousAt (fun t ↦ ‖z t * (z t + 1) * (z t + 2) * (z t + 3)‖ *
      (1 + 1 / ((z t).re + 3)) / 720) 0 := by
    fun_prop (disch := norm_num [z])
  have hle := le_of_tendsto_of_tendsto
    (h₁.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0)))
    (h₂.tendsto.mono_left nhdsWithin_le_nhds)
    (by filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
        exact herr (z t) (by norm_num [z]) (by simpa [z] using ht))
  intro hzero
  norm_num [z, hzero, norm_div, norm_mul, Complex.norm_real, ← Complex.ofReal_add,
    ← Complex.ofReal_sub, ← Complex.ofReal_div] at hle

/-- The first two positive zeta ordinates and their conjugates are the only
zeros of the rational completed zeta function at heights in `[-22, 22]`.
All four are simple. This is the finite analytic input to the counterexample. -/
private theorem spectralLineBand_jetCount_le_false_low_zeros :
    ∃ u v : ℝ, 0 < u ∧ u < v ∧ v < 22 ∧
      ∀ t ∈ Icc (-22 : ℝ) 22,
        orderAt((1 : PontryaginDual C𝔽(ℚ)), shift((1 / 2 : ℝ), t)) =
          if t = -v ∨ t = -u ∨ t = u ∨ t = v then 1 else 0 := by
  classical
  obtain ⟨ts, hsecond, hthird, hmono, hts⟩ :=
    spectralLineBand_jetCount_le_false_brackets
  refine ⟨ts 0, ts 1, (hts 0).1, hmono (by decide), hsecond, ?_⟩
  intro t ht
  let z (r : ℝ) : ℂ := 1 / 2 + r * Complex.I
  have hne (r : ℝ) : z r ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    norm_num [z] at this
  have hm : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hbridge := meromorphicOrderAt_finiteHeckeL_continuation (1 : PontryaginDual C𝔽(ℚ))
    hm (fun s ↦ by
      rw [finiteHeckeL_one_eq_dedekindZeta, dedekindZeta_rat_eq_riemannZeta s.property])
    (s := z t) (by norm_num [z])
  push_cast
  change meromorphicOrderAt (continuedCompletedHeckeL (1 : PontryaginDual C𝔽(ℚ))) (z t) = _
  rw [← hbridge, (analyticOn_riemannZeta _ (hne t)).meromorphicOrderAt_eq]
  have hpos {r : ℝ} (hr : 0 < r) (hr' : r ≤ 22) := spectralLineBand_jetCount_le_false_positive
    ts hmono hts hthird RHHeight.zero_count_fifty RHHeight.rh_height_fifty hr hr'
  have hu := (hts 0).1
  have hv := (hts 1).1
  rcases lt_trichotomy t 0 with hneg | rfl | hgt
  · have hconj : (starRingEnd ℂ) (z t) = z (-t) := by norm_num [z, map_ofNat]
    have horder := Zeta23.analyticOrderAt_zeta_conj (hne t)
    rw [hconj] at horder
    rw [← horder, hpos (neg_pos.mpr hneg) (by linarith [ht.1])]
    have htu : t ≠ ts 0 := by linarith
    have htv : t ≠ ts 1 := by linarith
    simp only [htu, htv, or_false, neg_eq_iff_eq_neg]
    by_cases h0 : t = -ts 0 <;> by_cases h1 : t = -ts 1 <;> simp [h0, h1]
  · have hz0 : riemannZeta (z 0) ≠ 0 := by
      simpa [z] using spectralLineBand_jetCount_le_false_center
        (fun w hw ht' ↦ RHHeight.norm_zeta_sub_main_one_le (s := w) ⟨hw, ht'⟩)
    rw [(analyticOn_riemannZeta _ (hne 0)).analyticOrderAt_eq_zero.mpr hz0]
    simp [hu.ne', hv.ne', hu.ne, hv.ne]
  · rw [hpos hgt ht.2]
    have htu : t ≠ -ts 0 := by linarith
    have htv : t ≠ -ts 1 := by linarith
    simp only [htu, htv, false_or]
    split <;> simp

/-- Paper: Theorem 10.3.1.1, count following (10.3.1.16), p. 450.
With cutoff one, the four lowest nonreal zeta zeros give four jets in
the band from −22 to 22, while the stated bound is log 22 < 4. -/
theorem Printed.spectralLineBand_jetCount_le_false :
    ¬ Printed.spectralLineBand_jetCount_le := by
  classical
  intro h
  obtain ⟨u, v, hu, huv, hv, hzeros⟩ := spectralLineBand_jetCount_le_false_low_zeros
  obtain ⟨χ₀, hχ₀⟩ := exists_spectralBasepointChoice ℚ
  let χ := Function.update χ₀ 1 1
  have hχ : IsSpectralBasepointChoice χ := by
    intro ω
    by_cases hω : ω = 1
    · subst ω
      simp only [χ, Function.update_self]
      rfl
    · simpa only [χ, Function.update_of_ne hω] using hχ₀ ω
  let K : Finset ℝ := {-v, -u, u, v}
  have hK : K.Nonempty := ⟨v, by simp [K]⟩
  have hmin : K.min' hK = -v := by
    apply le_antisymm (Finset.min'_le _ _ (by simp [K]))
    apply Finset.le_min'
    intro t ht
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> linarith
  have hmax : K.max' hK = v := by
    apply le_antisymm _ (Finset.le_max' _ _ (by simp [K]))
    apply Finset.max'_le
    intro t ht
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl <;> linarith
  have hlo : K.min' hK - (22 - v) = -22 := by rw [hmin]; ring
  have hhi : K.max' hK + (22 - v) = 22 := by rw [hmax]; ring
  have hmem {t : ℝ} (ht : t ∈ K) : t ∈ Icc (-22 : ℝ) 22 := by
    have h₁ := Finset.min'_le K t ht
    have h₂ := Finset.le_max' K t ht
    rw [hmin] at h₁
    rw [hmax] at h₂
    constructor <;> linarith
  have hband : Icc (-22 : ℝ) 22 ∩ lineZeros(χ 1, (1 / 2 : ℝ)) = (K : Set ℝ) := by
    ext t
    change (t ∈ Icc (-22 : ℝ) 22 ∧ 0 < orderAt(χ 1, shift((1 / 2 : ℝ), t))) ↔ t ∈ K
    by_cases ht : t ∈ Icc (-22 : ℝ) 22
    · simp only [χ, Function.update_self, hzeros t ht, ht, true_and]
      by_cases hc : t = -v ∨ t = -u ∨ t = u ∨ t = v <;> simp [K, hc]
    · exact ⟨fun h ↦ (ht h.1).elim, fun hk ↦ (ht (hmem hk)).elim⟩
  have hbound := h ℚ χ hχ (1 / 2) 2 (by norm_num) 1 K hK (22 - v)
    (by linarith) (by simpa only [hlo, hhi] using hband)
  have hcut : floorCut((2 : ℝ)) = 1 := (Nat.floor_eq_iff (by norm_num)).2 (by norm_num)
  have hterm (t : ℝ) (ht : t ∈ K) :
      min (orderAt(χ 1, shift((1 / 2 : ℝ), t))).untop₀.toNat floorCut((2 : ℝ)) = 1 := by
    have hcases : t = -v ∨ t = -u ∨ t = u ∨ t = v := by simpa [K] using ht
    simp only [χ, Function.update_self, hzeros t (hmem ht), ite_eq_left hcases]
    norm_num
  have hcard : K.card = 4 := by
    have huv' : 0 < v := lt_trans hu huv
    simp [K, Finset.card_insert_of_notMem, ne_of_lt huv,
      show -v ≠ -u by linarith, show -v ≠ u by linarith, show -v ≠ v by linarith,
      show -u ≠ u by linarith, show -u ≠ v by linarith]
  rw [Finset.sum_congr rfl hterm, hlo, hhi, hcut] at hbound
  norm_num [hcard] at hbound
  have hexp : (22 : ℝ) < Real.exp 4 := by
    have he : (5 / 2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    calc
      (22 : ℝ) < (5 / 2 : ℝ) ^ 4 := by norm_num
      _ < Real.exp 1 ^ 4 := by gcongr
      _ = Real.exp 4 := by simp
  exact (not_lt_of_ge hbound) ((Real.log_lt_iff_lt_exp (by norm_num)).2 hexp)

section Plancherel

local instance instNormOneLocallyCompactSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : LocallyCompactSpace C₁(F) := by
  have hc : IsCompact ((ideleClassNorm F).ker : Set C𝔽(F)) :=
    (isProperMap_ideleClassNorm F).isCompact_preimage isCompact_singleton
  exact hc.isClosed.locallyCompactSpace

local instance instNormOneHaarSec3SpectralProofPrinted (F : Type) [Field F] [NumberField F] :
    (normOneIdeleClassTamagawaMeasure F).IsHaarMeasure :=
  (multiplicativeTamagawaMeasures_existsUnique F).exists.choose_spec.2.2.2.1

local instance instIdeleClassDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C𝔽(F)) := borel _

local instance instNormOneDualMeasurableSpaceSec3SpectralProofPrinted
    (F : Type) [Field F] [NumberField F] : MeasurableSpace (PontryaginDual C₁(F)) := borel _

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
As printed: in the coordinates induced by the norm section τ, the full Plancherel measure
is the product of ordinary Lebesgue measure in x and the Plancherel measure of the norm-one subgroup.
This is the radial normalization used in the proof of `spectralLineConvolution_trace`
and `spectralStripConvolution_trace` in the paper. See ERRATA F182. -/
def Printed.spectralPlancherelMeasure_eq_radialVolume_prod : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (e : (Multiplicative ℝ × PontryaginDual C₁(F)) ≃ₜ* PontryaginDual C𝔽(F)),
      (∀ (x : ℝ) (ω : PontryaginDual C₁(F)) (r : ℝ≥0ˣ) (k : C₁(F)),
        e (Multiplicative.ofAdd x, ω) (τ r * k.val) =
          ω k * Circle.exp (x * Real.log (r.val : ℝ))) →
      ∀ (ν₁ : Measure (PontryaginDual C₁(F))) (ν : Measure (PontryaginDual C𝔽(F))),
        IsLCAPlancherelMeasure (normOneIdeleClassTamagawaMeasure F) ν₁ →
        IsLCAPlancherelMeasure (ideleClassTamagawaMeasure F) ν →
        (volume.prod ν₁).map (fun p : ℝ × PontryaginDual C₁(F) ↦
          e (Multiplicative.ofAdd p.1, p.2)) = ν

/-- Paper: Theorem 10.3.1.1, Plancherel measure after (10.3.1.25), p. 453.
Take F = ℚ with its norm section and induced dual isomorphism. Use the Gaussian exp(−y²/2)
in y = log |g|, constant on the norm-one subgroup. With the kernel exp(ixy) its radial
transform is √(2π) exp(−x²/2). The printed measure makes its squared norm 2π times the
original squared norm, since the fixed norm-one Plancherel measure already accounts for
the compact factor. The radial Plancherel measure is dx/(2π). -/
theorem Printed.spectralPlancherelMeasure_eq_radialVolume_prod_false :
    ¬ Printed.spectralPlancherelMeasure_eq_radialVolume_prod := by sorry

end Plancherel

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
As printed: for each norm-one character and any numbering of its line-zero ordinates by
the natural numbers, the Fourier–Mellin samples of every test decay rapidly. This is the
claim for an infinite zero set. See `spectralLineConvolution_trace` and ERRATA F183. -/
def Printed.spectralLineSamples_rapid_for_any_numbering : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (a : ℝ) (φ : BruhatCompactSupport C𝔽(F)) (ω : PontryaginDual C₁(F))
      (e : ℕ ≃ lineZeros(χ ω, a)) (k : ℕ),
      Tendsto (fun n : ℕ ↦ (n : ℂ) ^ k * ∫ g,
        φ.val g * ideleClassNormTwist (χ ω) (shift(0, (e n).val)) g
          ∂ideleClassTamagawaMeasure F) atTop (𝓝 0)

/-- Paper: Theorem 10.3.1.1, after (10.3.1.26), p. 453.
Take F = ℚ, the trivial base character and a = 1/2. Modulate a nonzero smooth radial
bump in y = log |g| by exp(icy). Its entire transform has discrete real zeros. Avoid the
countably many frequencies c for which a sample is zero. Place infinitely many samples
vⱼ at increasing nonadjacent indices nⱼ ≥ 1/|vⱼ|, leaving infinitely many ordinates for
the other indices. Then nⱼ|vⱼ| ≥ 1, which violates decay at k = 1. -/
theorem Printed.spectralLineSamples_rapid_for_any_numbering_false :
    ¬ Printed.spectralLineSamples_rapid_for_any_numbering := by sorry

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
As printed: for each integration-by-parts order N > 1, one constant bounds all admitted
Mellin derivatives at nonreal strip zeros by the displayed falling factorial over |z|^N.
The order range on p. 455 includes the low orders in (10.3.2.7). The radial Mellin transform
uses the compact character coefficient for the selected component, as on p. 450 after
(10.3.1.17). See `spectralStripConvolution_traceCauchy` and ERRATA F185. -/
def Printed.spectralStripMellinJet_norm_le : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (χ : PontryaginDual C₁(F) → PontryaginDual C𝔽(F)), IsSpectralBasepointChoice χ →
    ∀ (τ : ℝ≥0ˣ →ₜ* C𝔽(F)), Function.RightInverse τ (ideleClassNorm F) →
    ∀ (a α s : ℝ), 0 ≤ α → 1 < s → ∀ (φ : BruhatCompactSupport C𝔽(F)) (N : ℕ), 1 < N →
      let M (ω : PontryaginDual C₁(F)) (z : ℂ) :=
        ∫ r : ℝ≥0ˣ, ((r.val : ℝ) : ℂ) ^ z *
          (∫ k : C₁(F), (ω k : ℂ) * φ.val (τ r * k.val) ∂normOneIdeleClassTamagawaMeasure F)
          ∂positiveRealHaar
      ∃ C : ℝ, 0 < C ∧ ∀ (ω : PontryaginDual C₁(F)) (b t : ℝ),
        b ∈ Icc (-α) α → t ≠ 0 → 0 < orderAt(χ ω, shift(a + b, t)) →
        let mult := (orderAt(χ ω, shift(a + b, t))).untop₀.toNat
        let count := if b = -α ∨ b = α then min mult floorCut(s) else mult
        ∀ i : ℕ, i < count →
          ‖iteratedDeriv i (M ω) (shift(b, t))‖ ≤
            C * (∏ n ∈ Finset.range N, ((i : ℝ) - (n : ℝ))) / ‖shift(b, t)‖ ^ N

/-- Paper: Theorem 10.3.2.1, (10.3.2.10)–(11), p. 455.
Take F = ℚ, the trivial base character, a = 1/2, α = 1, s = 2 and N = 2. Let z = iγ
for the first positive critical-line zeta ordinate γ. The interior multiplicity admits
i = 0. For φ(g) = h(log |g|) exp(−iγ log |g|), with h a nonnegative smooth bump of
positive integral, M(φ)(iγ) has positive norm. The n = 0 factor forces the right-hand
side to vanish for every constant C. -/
theorem Printed.spectralStripMellinJet_norm_le_false :
    ¬ Printed.spectralStripMellinJet_norm_le := by sorry

end RiemannMasullo
