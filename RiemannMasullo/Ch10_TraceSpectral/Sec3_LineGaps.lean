module

public import RiemannMasullo.Ch10_TraceSpectral.Sec3_LineGram
import Mathlib.Order.SuccPred.LinearLocallyFinite

/-! # The true-neighbor Gram sum on the degree-two spectral line

The bounded-interval finiteness of the Hecke divisor gives each site a predecessor
and successor on its own character. A finite block containing these neighbors already
attains the full coordinate norm. The resulting single-sum criterion for Theorem
10.3.2.1(1), pp. 453–455, is proved in `Sec3_Isolated`.
-/

@[expose] public noncomputable section

open Function MeasureTheory NumberField Set
open scoped InnerProductSpace NNReal NumberField.AdeleRing

namespace RiemannMasullo

private theorem map_pred_of_mem_range {I J : Type*} [LinearOrder I] [LinearOrder J]
    [PredOrder I] [PredOrder J] {e : I → J} (he : StrictMono e) (i : I)
    (hp : Order.pred (e i) ∈ range e) : e (Order.pred i) = Order.pred (e i) := by
  obtain ⟨k, hk⟩ := hp
  by_cases hm : IsMin (e i)
  · have hm' : IsMin i := fun j hj ↦ he.le_iff_le.mp (hm (he.monotone hj))
    rw [Order.pred_eq_iff_isMin.mpr hm, Order.pred_eq_iff_isMin.mpr hm']
  · have hk' : k < i := he.lt_iff_lt.mp (hk ▸ Order.pred_lt_of_not_isMin hm)
    have hi : Order.pred i < i := Order.pred_lt_of_not_isMin hk'.not_isMin
    exact le_antisymm (Order.le_pred_of_lt (he hi))
      (hk ▸ he.monotone (Order.le_pred_of_lt hk'))

/-- Restricting an ordered site family to a subset that contains both true
neighbors preserves its exponential inverse diagonal at the site. -/
theorem exponentialGramDiagonal_comp_of_neighbors {I J : Type*}
    [LinearOrder I] [LinearOrder J] [PredOrder I] [PredOrder J] [SuccOrder I] [SuccOrder J]
    {e : I → J} (he : StrictMono e) (t : J → ℝ) (i : I)
    (hp : Order.pred (e i) ∈ range e) (hs : Order.succ (e i) ∈ range e) :
    exponentialGramDiagonal (t ∘ e) i = exponentialGramDiagonal t (e i) := by
  have P := map_pred_of_mem_range he i hp
  have S : e (Order.succ i) = Order.succ (e i) :=
    map_pred_of_mem_range (I := Iᵒᵈ) (J := Jᵒᵈ) he.dual i hs
  have hp' : Order.pred i = i ↔ Order.pred (e i) = e i := by rw [← P, he.injective.eq_iff]
  have hs' : Order.succ i = i ↔ Order.succ (e i) = e i := by rw [← S, he.injective.eq_iff]
  simp only [exponentialGramDiagonal, Function.comp_apply, hp', hs', P, S]

/-- A principal inverse Gram coordinate is nonnegative, including off its finite support. -/
theorem finiteGramCoordinate_nonneg {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u : I → H) (i : I) (S : Finset I) : 0 ≤ finiteGramCoordinate u i S := by
  classical
  unfold finiteGramCoordinate
  split <;> positivity

/-- Enlarging a principal Gram block can only increase its coefficient norm. -/
theorem monotone_finiteGramCoordinate {I H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {u : I → H} (hu : LinearIndependent ℂ u) (i : I) : Monotone (finiteGramCoordinate u i) := by
  intro S T hST
  obtain ⟨c, hc, he⟩ := (finiteGramCoordinate_isGreatest hu i S).1
  exact (finiteGramCoordinate_isGreatest hu i T).2 ⟨c, Finset.Subset.trans hc hST, he⟩

/-- When coordinate factors increase with their finite supports and attain a
maximum, one common support realizes all factors on any finite outer sum. -/
theorem summable_maxima_iff_common_finite_bound {Z W I : Type*}
    (v : Z → W → ℝ) (circle : Z → Set W) (k : Z → Finset I → ℝ)
    (M K : Z → ℝ) (hv : ∀ z w, 0 ≤ v z w) (hk : ∀ z S, 0 ≤ k z S)
    (hm : ∀ z, Monotone (k z))
    (hM : ∀ z, IsGreatest ((v z) '' circle z) (M z))
    (hK : ∀ z, IsGreatest (range (k z)) (K z)) :
    Summable (fun z ↦ M z * K z) ↔
      ∃ B : ℝ, ∀ (T : Finset Z) (w : Z → W) (S : Finset I),
        (∀ z ∈ T, w z ∈ circle z) → ∑ z ∈ T, v z (w z) * k z S ≤ B := by
  classical
  choose w hw hmax using fun z ↦ (hM z).1
  choose U hU using fun z ↦ (hK z).1
  have hpos (z : Z) : 0 ≤ M z * K z := by
    rw [← hmax z, ← hU z]
    exact mul_nonneg (hv _ _) (hk _ _)
  constructor
  · intro h
    refine ⟨∑' z, M z * K z, fun T p S hp ↦ (Finset.sum_le_sum fun z hz ↦ ?_).trans
      (h.sum_le_tsum T fun z _ ↦ hpos z)⟩
    exact mul_le_mul ((hM z).2 ⟨p z, hp z hz, rfl⟩) ((hK z).2 (mem_range_self S))
      (hk _ _) (hmax z ▸ hv _ _)
  · rintro ⟨B, hB⟩
    refine summable_of_sum_le (c := B) hpos fun T ↦ ?_
    let S := T.biUnion U
    have hstable (z : Z) (hz : z ∈ T) : k z S = K z :=
      le_antisymm ((hK z).2 (mem_range_self S))
        (hU z ▸ hm z (Finset.subset_biUnion_of_mem U hz))
    exact (Finset.sum_congr rfl (fun z hz ↦ congrArg₂ (· * ·) (hmax z) (hstable z hz))).symm.le.trans
      (hB T w S fun z _ ↦ hw z)

end RiemannMasullo

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]

local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "shift(" a ", " t ")" => ((a : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
local notation "mord(" η ", " s ")" => meromorphicOrderAt (continuedCompletedHeckeL (F := F) η) s
local notation "mult(" η ", " s ")" => (mord(η, s)).untop₀.toNat
local notation "uJet(" χ ", " j ")" =>
  (spectralStripJet_memLp χ (le_refl (0 : ℝ)) (by norm_num : (0 : ℝ) ≤ 2) j).toLp
    (spectralZeroJet (F := F) (χ (j).val.1) (j).val.2.1 (j).val.2.2.1 (j).val.2.2.2)

/-- All ordinates of the positive completed Hecke divisor on one character line. -/
def spectralLineZeroOrdinates (η : PontryaginDual C𝔽) (a : ℝ) : Set ℝ :=
  {t | 0 < mult(η, shift(a, t))}

/-- Each bounded interval contains only finitely many ordinates on a fixed character. -/
instance spectralLineZeroOrdinates_locallyFiniteOrder (η : PontryaginDual C𝔽) (a : ℝ) :
    LocallyFiniteOrder (spectralLineZeroOrdinates η a) := by
  apply LocallyFiniteOrder.ofFiniteIcc
  intro b c
  let f (t : ℝ) := shift(a, t)
  let L := continuedCompletedHeckeL η
  let K := Icc b.val c.val
  have hf : Continuous f := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hfi : Injective f := fun x y h ↦ by simpa [f, Complex.add_im, Complex.mul_im] using congrArg Complex.im h
  have hL : MeromorphicOn L (f '' K) := fun z _ ↦ (continuedCompletedHeckeL_spec η).1.meromorphicOn z (mem_univ z)
  have hfin := (MeromorphicOn.divisor L (f '' K)).finiteSupport (isCompact_Icc.image hf)
  apply Set.Finite.of_injOn (f := fun t : spectralLineZeroOrdinates η a ↦ f t.val) _
    (hfi.comp Subtype.val_injective).injOn hfin
  intro t ht
  change MeromorphicOn.divisor L (f '' K) (f t.val) ≠ 0
  rw [hL.divisor_apply ⟨t.val, ht, rfl⟩]
  have hp : 0 < (meromorphicOrderAt L (f t.val)).untop₀.toNat := t.property
  exact fun h ↦ by rw [h] at hp; simp at hp

instance spectralLineZeroOrdinates_predOrder (η : PontryaginDual C𝔽) (a : ℝ) :
    PredOrder (spectralLineZeroOrdinates η a) :=
  LinearLocallyFiniteOrder.predOrder _

instance spectralLineZeroOrdinates_succOrder (η : PontryaginDual C𝔽) (a : ℝ) :
    SuccOrder (spectralLineZeroOrdinates η a) :=
  LinearLocallyFiniteOrder.succOrder _

variable (χ : PontryaginDual (ideleClassNorm F).ker → PontryaginDual (IdeleClassGroup (𝓞 F) F)) {a : ℝ}

local notation "J" => SpectralStripJetIndex (F := F) χ a 0 2

/-- A degree-two retained index has zero offset, jet order zero and positive Hecke multiplicity. -/
theorem spectralStripJet_data_line_two (i : J) :
    i.val.2.1 = 0 ∧ i.val.2.2.2 = 0 ∧ 0 < mult(χ i.val.1, shift(a, i.val.2.2.1)) := by
  have hb : i.val.2.1 = 0 := by simpa using (i.mem_strip_order_pos (le_refl (0 : ℝ))).1
  have hi := i.property
  rw [spectralStripMultiplicity_boundary le_rfl (Or.inr hb)] at hi
  obtain ⟨hm, hk⟩ := (lt_spectralBoundaryMultiplicity _ _ _).mp hi
  have ho : i.val.2.2.2 = 0 := by
    by_contra hn
    have h₁ : (1 : ℝ) ≤ i.val.2.2.2 := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
    linarith
  refine ⟨hb, ho, ?_⟩
  simpa only [hb, ho, add_zero] using hm

private def siteOfLineJet (ω : PontryaginDual C₁) (i : J) (hω : i.val.1 = ω) :
    spectralLineZeroOrdinates (χ ω) a :=
  ⟨i.val.2.2.1, hω ▸ (spectralStripJet_data_line_two χ i).2.2⟩

private def lineJetOfSite (ω : PontryaginDual C₁) (p : spectralLineZeroOrdinates (χ ω) a) : J :=
  ⟨(ω, 0, p.val, 0), by
    change 0 < spectralStripMultiplicity 0 2 0 (mult(χ ω, shift(a + 0, p.val)))
    rw [add_zero, spectralStripMultiplicity_boundary le_rfl (Or.inr rfl)]
    exact (lt_spectralBoundaryMultiplicity _ _ _).mpr ⟨p.property, by norm_num⟩⟩

/-- The inverse diagonal from the two nearest actual zeros, in the complete
ordered set on the character containing the selected jet. -/
def spectralLineTrueGramDiagonal (i : J) : ℝ :=
  exponentialGramDiagonal (fun p : spectralLineZeroOrdinates (χ i.val.1) a ↦ p.val)
    ⟨i.val.2.2.1, (spectralStripJet_data_line_two χ i).2.2⟩

open Classical in
private def lineJetNeighbors (i : J) : Finset J :=
  let p := siteOfLineJet χ i.val.1 i rfl
  {i, lineJetOfSite χ i.val.1 (Order.pred p), lineJetOfSite χ i.val.1 (Order.succ p)}

open Classical in
private theorem gram_of_contains_neighbors (hχ : IsSpectralBasepointChoice χ) (i : J) (S : Finset J)
    (hS : lineJetNeighbors χ i ⊆ S) :
    (‖uJet(χ, i)‖ * finiteGramCoordinate (fun j ↦ uJet(χ, j)) i S) ^ 2 =
      spectralLineTrueGramDiagonal χ i := by
  let ω := i.val.1
  let T := S.filter (fun j ↦ j.val.1 = ω)
  have hi : i ∈ S := hS (by simp [lineJetNeighbors])
  let j : T := ⟨i, Finset.mem_filter.mpr ⟨hi, rfl⟩⟩
  obtain ⟨e, he, hdiag⟩ := spectralStripJet_finiteGram_by_character_line_two χ hχ S ω
  let f (k : Fin T.card) := siteOfLineJet χ ω (e k).val (Finset.mem_filter.mp (e k).property).2
  have hf : StrictMono f := he
  let q := e.symm j
  let p := siteOfLineJet χ ω i rfl
  have hq : e q = j := e.apply_symm_apply j
  have hfp : f q = p := Subtype.ext (by change (e q).val.val.2.2.1 = _; rw [hq]; rfl)
  have hmem (v : spectralLineZeroOrdinates (χ ω) a) (hv : lineJetOfSite χ ω v ∈ S) :
      v ∈ range f := by
    let jv : T := ⟨lineJetOfSite χ ω v, Finset.mem_filter.mpr ⟨hv, rfl⟩⟩
    obtain ⟨k, hk⟩ := e.surjective jv
    exact ⟨k, Subtype.ext (by change (e k).val.val.2.2.1 = v.val; rw [hk]; rfl)⟩
  have hp : Order.pred (f q) ∈ range f := by
    rw [hfp]
    exact hmem _ (hS (by simp [lineJetNeighbors, p, ω]))
  have hs : Order.succ (f q) ∈ range f := by
    rw [hfp]
    exact hmem _ (hS (by simp [lineJetNeighbors, p, ω]))
  have hd := hdiag q
  rw [hq] at hd
  refine hd.trans ?_
  have hc := exponentialGramDiagonal_comp_of_neighbors hf (fun v ↦ v.val) q hp hs
  rw [hfp] at hc
  exact hc

/-- A support of at most three retained jets realizes the true inverse diagonal
and keeps the same value under every finite enlargement. -/
theorem spectralLine_finiteGram_stabilizes_on_three (hχ : IsSpectralBasepointChoice χ) (i : J) :
    ∃ A : Finset J, A.card ≤ 3 ∧ ∀ S : Finset J, A ⊆ S →
      (‖uJet(χ, i)‖ * finiteGramCoordinate (fun j ↦ uJet(χ, j)) i S) ^ 2 =
        spectralLineTrueGramDiagonal χ i := by
  classical
  exact ⟨lineJetNeighbors χ i, Finset.card_le_three, gram_of_contains_neighbors χ hχ i⟩

/-- The full normalized Gram coordinate attains its maximum on the site and its
two true neighboring ordinates, allowing missing neighbors at an endpoint. -/
theorem spectralLine_finiteGram_isGreatest (hχ : IsSpectralBasepointChoice χ) (i : J) :
    IsGreatest (range (fun S ↦ ‖uJet(χ, i)‖ * finiteGramCoordinate (fun j ↦ uJet(χ, j)) i S))
      (Real.sqrt (spectralLineTrueGramDiagonal χ i)) := by
  classical
  let u (j : J) := uJet(χ, j)
  obtain ⟨A, _, hA⟩ := spectralLine_finiteGram_stabilizes_on_three χ hχ i
  have hstable (S : Finset J) (hS : A ⊆ S) : ‖u i‖ * finiteGramCoordinate u i S =
      Real.sqrt (spectralLineTrueGramDiagonal χ i) := by
    rw [← hA S hS]
    exact (Real.sqrt_sq (mul_nonneg (norm_nonneg _) (finiteGramCoordinate_nonneg _ _ _))).symm
  have hm := monotone_finiteGramCoordinate (spectralStripJet_toLp_linearIndependent χ hχ a
    (le_refl 0) (by norm_num : (0 : ℝ) ≤ 2)) i
  refine ⟨⟨A, hstable A Finset.Subset.rfl⟩, ?_⟩
  rintro _ ⟨S, rfl⟩
  exact (mul_le_mul_of_nonneg_left (hm (Finset.subset_union_left (s₁ := S) (s₂ := A))) (norm_nonneg _)).trans
    (hstable (S ∪ A) Finset.subset_union_right).le

local notation "Z" => {z : PontryaginDual C₁ × ℝ × ℝ //
  z.2.1 ∈ Icc (-(0 : ℝ)) 0 ∧ 0 < mord(χ z.1, shift(a + z.2.1, z.2.2))}
local notation "N(" z ")" => spectralStripMultiplicity 0 2 (z).val.2.1
  (mult(χ (z).val.1, shift(a + (z).val.2.1, (z).val.2.2)))

private theorem lineZero_count (z : Z) : N(z) = 1 := by
  have hb : z.val.2.1 = 0 := by simpa using z.property.1
  let η := χ z.val.1
  let w := shift(a + z.val.2.1, z.val.2.2)
  let L := continuedCompletedHeckeL η
  obtain ⟨hL, hLval⟩ := continuedCompletedHeckeL_spec η
  have hfinite : meromorphicOrderAt L w ≠ ⊤ := by
    apply hL.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      isPreconnected_univ (x := 2) (mem_univ _) (mem_univ w)
    intro htop
    have hpos : 0 < meromorphicOrderAt L 2 := htop ▸ WithTop.coe_lt_top (0 : ℤ)
    have hbad := completedHeckeL_continuation_zeros η L hL hLval (by norm_num : 0 < (2 : ℂ).re) hpos
    norm_num at hbad
  have hpos : 0 < meromorphicOrderAt L w := z.property.2
  have hm : 0 < (meromorphicOrderAt L w).untop₀.toNat := by
    cases hn : meromorphicOrderAt L w with
    | top => exact (hfinite hn).elim
    | coe n =>
      rw [hn] at hpos
      rw [WithTop.untop₀_coe]
      have hn' : (0 : ℤ) < n := by exact_mod_cast hpos
      omega
  rw [spectralStripMultiplicity_boundary le_rfl (Or.inr hb), spectralBoundaryMultiplicity]
  have hceil : ⌈((2 : ℝ) - 1) / 2⌉₊ = 1 := by
    apply (Nat.ceil_eq_iff one_ne_zero).mpr
    norm_num
  rw [hceil]
  exact min_eq_right hm

/-- At degree two each positive zero on the width-zero strip has just its value jet. -/
def spectralLineZeroJet (z : Z) : J :=
  ⟨(z.val.1, z.val.2.1, z.val.2.2, 0), by change 0 < N(z); rw [lineZero_count χ z]; decide⟩

/-- Summing over all retained jets at a degree-two line zero evaluates the summand once. -/
theorem spectralLine_sum_retainedJets_two (z : Z) (g : J → ℝ) :
    (∑ m : Fin (N(z)), g ⟨(z.val.1, z.val.2.1, z.val.2.2, m.val), m.isLt⟩) =
      g (spectralLineZeroJet χ z) := by
  have hn := lineZero_count χ z
  let : Unique (Fin (N(z))) := {
    default := ⟨0, by rw [hn]; decide⟩
    uniq := fun m ↦ Fin.ext (by change m.val = 0; have hm : m.val < 1 := lt_of_lt_of_eq m.isLt hn; omega) }
  rw [Fintype.sum_unique]
  rfl

end RiemannMasullo.Isolated
