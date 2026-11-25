module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a
public import RiemannMasullo.ForMathlib.Analysis.Fourier.StripLaplace
import RiemannMasullo.Ch03_IdelicZeta.Sec4
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactLatticeInterpolation
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Gaussian
import RiemannMasullo.ForMathlib.Analysis.MellinTransform.Weighted
import Mathlib.Analysis.Meromorphic.IsolatedZeros

import Mathlib.Analysis.PSeries
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Isolated statements for the separate place sums in §7.1.2

Statements and partial results for open problem #7279 (Theorem 7.1.2.3, pp. 317–323, ERRATA I210).
Nothing in the library imports this file (`AGENTS.md`, "False statements and gaps").

The printed expansion counts a pole shared by two places under each of them, which is refuted
(`Sec1a_Printed.lean`, F88). Counting each pole once requires an assignment of poles to
contributing places. We state the repaired separately summed expansion as a proposition
parameterized by that assignment (asserting nothing), prove that convergent assignments always
share the same total and agree with the contour shift, classify when convergence is independent
of the assignment (including unconditionally over `ℚ`), prove uniform convergence for every
assignment under a summable majorant, establish uniform pole discreteness over any single
rational prime, and prove the exact lattice arithmetic equivalence behind the Gaussian-field
obstruction in #7279.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped BigOperators NNReal Asymptotics

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Primes" => HeightOneSpectrum (𝓞 F)
local notation "Jₛ" => SIdeleQuotient F S
local notation "Tests" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "normₛ" => sIdeleQuotientNorm F S
local notation "chart(" χ ")" => quasiCharacterNormTwist (G := Jₛ) normₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)
local notation "Places" => InfinitePlace F ⊕ S

local instance isolatedCh07Sec1aNormOneMeasurableSpace : MeasurableSpace (normₛ).ker := borel _
local instance isolatedCh07Sec1aNormOneHaar : (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

/-! ## Contributing places and valid pole assignments -/

/-- Paper: Lemma 7.1.2.2, pp. 316–317. Explicit local-pole condition indicating that a place
in `InfinitePlace F ⊕ S` contributes the pole `a` of `sLocalRhoFactor (chart(χ) ·)`.
Deviation: Uses the repaired complex-place sign and shifted finite-place lattice of
`sLocalRhoFactor_poles_iff`. -/
def sLocalPoleContributes (χ : PontryaginDual Jₛ) : Places → ℂ → Prop :=
  Sum.elim
    (fun w a ↦
      (∃ (hw : w.IsReal) (n : ℕ),
        let p := (realLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
        a = -p.1 - ((2 * n + p.2.val : ℕ) : ℂ)) ∨
      (∃ (hw : w.IsComplex) (n : ℕ),
        let p := (complexLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
        a = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)))
    (fun v a ↦
      ∃ (m : ℤ) (t : ℝ),
        let period := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
        t ∈ Ico 0 period ∧
          (∀ x : (v.val.adicCompletion F)ˣ,
            sLocalFiniteRestriction v (chart(χ) 0) x =
              ((‖(x : v.val.adicCompletion F)‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I)) ∧
          a = (((m : ℝ) * period - t : ℝ) : ℂ) * Complex.I)

/-- Paper: Lemma 7.1.2.2, pp. 316–317. A complex point is a pole of the S-local correcting
factor if and only if at least one place in `InfinitePlace F ⊕ S` contributes it. -/
theorem sLocalPoleContributes_exists_iff (χ : PontryaginDual Jₛ) (a : ℂ) :
    meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 ↔
      ∃ v : Places, sLocalPoleContributes χ v a := by
  refine (sLocalRhoFactor_poles_iff χ a).trans ?_
  constructor
  · rintro (⟨w, hw, n, h⟩ | ⟨w, hw, n, h⟩ | ⟨v, m, t, h⟩)
    · exact ⟨Sum.inl w, Or.inl ⟨hw, n, h⟩⟩
    · exact ⟨Sum.inl w, Or.inr ⟨hw, n, h⟩⟩
    · exact ⟨Sum.inr v, m, t, h⟩
  · rintro ⟨w | v, h⟩
    · rcases h with ⟨hw, n, h⟩ | ⟨hw, n, h⟩
      · exact Or.inl ⟨w, hw, n, h⟩
      · exact Or.inr (Or.inl ⟨w, hw, n, h⟩)
    · exact Or.inr (Or.inr ⟨v, h⟩)

/-- Paper: Lemma 7.1.2.2(2), p. 317. At a finite place, the explicit lattice condition agrees
with having a pole of the restricted finite local Tate factor. -/
theorem sLocalPoleContributes_finite_iff_tateFactor (χ : PontryaginDual Jₛ) (v : S) (a : ℂ) :
    sLocalPoleContributes χ (Sum.inr v) a ↔
      meromorphicOrderAt
        (fun z ↦ finiteLocalTateFactor v.val (sLocalFiniteRestriction v (chart(χ) z))) a < 0 := by
  obtain ⟨π, hπ, h⟩ := sLocalRhoFactor_poles_iff_finite χ v
  have hψ : ∀ x : (v.val.adicCompletion F)ˣ, ‖sLocalFiniteRestriction v (chart(χ) 0) x‖ = 1 := by
    intro x
    change ‖((χ _ : Circle) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    rw [Complex.cpow_zero, mul_one, Circle.norm_coe]
  rw [(h a).2.1]
  exact (sLocalRhoFactor_poles_iff_finite_explicit v.val _ hψ π hπ a).symm

/-- Paper: Lemma 7.1.2.2(1), p. 317. At a real archimedean place, the explicit condition agrees
with having a pole of the restricted infinite local Tate factor. -/
theorem sLocalPoleContributes_real_iff_tateFactor (χ : PontryaginDual Jₛ)
    (w : InfinitePlace F) (hw : w.IsReal) (a : ℂ) :
    sLocalPoleContributes χ (Sum.inl w) a ↔
      meromorphicOrderAt
        (fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (chart(χ) z))) a < 0 := by
  rw [(sLocalRhoFactor_poles_iff_real χ w hw a).2.1]
  constructor
  · rintro (⟨_, n, h⟩ | ⟨hc, _⟩)
    · exact ⟨n, h⟩
    · exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr hc)
  · rintro ⟨n, h⟩
    exact Or.inl ⟨hw, n, h⟩

/-- Reconstruction: To count each shared pole once (F88), an assignment chooses one contributing
place in `InfinitePlace F ⊕ S` for every pole of `sLocalRhoFactor (chart(χ) ·)`. -/
def IsValidPoleAssignment (χ : PontryaginDual Jₛ) (assign : ℂ → Places) : Prop :=
  ∀ a : ℂ, meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 →
    sLocalPoleContributes χ (assign a) a

/-- Every unitary S-local character admits a valid pole assignment. -/
theorem exists_isValidPoleAssignment (χ : PontryaginDual Jₛ) :
    ∃ assign : ℂ → Places, IsValidPoleAssignment χ assign := by
  classical
  refine ⟨fun a ↦ if h : ∃ v : Places, sLocalPoleContributes χ v a then h.choose
    else Sum.inl (Classical.arbitrary (InfinitePlace F)), fun a ha ↦ ?_⟩
  have hex : ∃ v : Places, sLocalPoleContributes χ v a :=
    (sLocalPoleContributes_exists_iff χ a).mp ha
  dsimp only
  rw [dite_eq_left hex]
  exact hex.choose_spec

/-! ## Parameterized statement of Theorem 7.1.2.3 -/

open Classical in
/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. The repaired separately summed expansion
parameterized by an explicit pole assignment `assign : ℂ → InfinitePlace F ⊕ S`.
This is a proposition asserting nothing; #7279 asks for which valid assignments, if any, it holds.
Deviation: The open strip `Re z ∈ (-A, 1)` includes zero and the actual archimedean abscissae
(F87); the residue of `(r g)⁻ᶻ Z f z` fixes the Laurent sign and index (F89, I211); the character
contributes its conjugate; shared poles are assigned once according to `assign` (F88).
Reconstruction: The finite outer sum runs over `InfinitePlace F ⊕ S` with the two height ends
escaping independently along `atBot ×ˢ atTop`, matching the bilateral series at each place. -/
def sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor (χ : PontryaginDual Jₛ)
    (A : ℝ) (_hA : 0 < A) (assign : ℂ → Places) : Prop :=
  let Z (f : Tests) (z : ℂ) := sLocalIdelicZFunction f (chart(χ) z)
  let r (g : Jₛ) : ℝ := (normₛ g).val
  let ω := χ.comp (⟨(normₛ).ker.subtype, continuous_subtype_val⟩ : (normₛ).ker →ₜ* Jₛ)
  let θ := sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω
  let poles (h : ℝ × ℝ) := (finite_rectanglePoles
    (f := fun z ↦ sLocalRhoFactor (chart(χ) z)) (a := -A - 1) (b := 2)
    (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
    (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).toFinset
  let partialSum (v : Places) (h : ℝ × ℝ) (f : Tests) (g : Jₛ) :=
    ∑ a ∈ (poles h).filter (assign · = v),
      star (χ g : ℂ) * complexResidue (fun z ↦ (r g : ℂ) ^ (-z) * Z f z) a
  ∃ L : Places → Tests → Jₛ → ℂ,
    (∀ v f (K : Set Jₛ), IsCompact K →
      TendstoUniformlyOn (fun h g ↦ partialSum v h f g) (L v f) (atBot ×ˢ atTop) K) ∧
    (∀ v (g : Jₛ), r g < 1 → ∀ B : Set Tests, Bornology.IsVonNBounded ℂ B →
      TendstoUniformlyOn (fun h f ↦ partialSum v h f g) (fun f ↦ L v f g) (atBot ×ˢ atTop) B) ∧
    (∀ f, Complex.VerticalIntegrable (Z f) (-A) ∧ ∀ g, r g < 1 →
      ‖θ f g - ∑ v, L v f g‖ ≤
        ((∫ y : ℝ, ‖Z f ((-A : ℝ) + (y : ℂ) * Complex.I)‖) / (2 * Real.pi)) * r g ^ A) ∧
    (∀ B : Set Tests, Bornology.IsVonNBounded ℂ B → ∃ C : ℝ, 0 ≤ C ∧
      ∀ f ∈ B, ∀ g, r g < 1 → ‖θ f g - ∑ v, L v f g‖ ≤ C * r g ^ A)

/-! ## Joint limits, contour totals, and assignment invariance -/

open Classical in
/-- Paper: Theorem 7.1.2.3, p. 322. When the separate place sums converge for any assignment,
summing their limits gives the limit of the joint pole sums along any pair of escaping heights. -/
theorem tendsto_jointPoleSum_of_separatePlaceLimits {ι : Type*} [Fintype ι]
    (poles : ℝ × ℝ → Finset ℂ) (assign : ℂ → ι) (term : ℂ → ℂ) (L : ι → ℂ)
    (hL : ∀ v, Tendsto (fun h ↦ ∑ a ∈ (poles h).filter (assign · = v), term a)
      (atBot ×ˢ atTop) (𝓝 (L v))) {lo hi : ℕ → ℝ}
    (hlo : Tendsto lo atTop atBot) (hhi : Tendsto hi atTop atTop) :
    Tendsto (fun n ↦ ∑ a ∈ poles (lo n, hi n), term a) atTop (𝓝 (∑ v, L v)) := by
  have h := tendsto_finsetSum Finset.univ
    (fun v _ ↦ (hL v).comp (hlo.prodMk hhi))
  exact h.congr fun n ↦ Finset.sum_fiberwise (poles (lo n, hi n)) assign term

open Classical in
/-- Any two assignments for which the separate place sums converge yield the same total sum. -/
theorem sum_separatePlaceLimits_eq_of_assignments {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (poles : ℝ × ℝ → Finset ℂ) (term : ℂ → ℂ)
    (assign₁ : ℂ → ι₁) (L₁ : ι₁ → ℂ)
    (hL₁ : ∀ v, Tendsto (fun h ↦ ∑ a ∈ (poles h).filter (assign₁ · = v), term a)
      (atBot ×ˢ atTop) (𝓝 (L₁ v)))
    (assign₂ : ℂ → ι₂) (L₂ : ι₂ → ℂ)
    (hL₂ : ∀ v, Tendsto (fun h ↦ ∑ a ∈ (poles h).filter (assign₂ · = v), term a)
      (atBot ×ˢ atTop) (𝓝 (L₂ v))) :
    ∑ v, L₁ v = ∑ v, L₂ v := by
  have hhi : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun n : ℕ ↦ -(n : ℝ)) atTop atBot := tendsto_neg_atTop_atBot.comp hhi
  exact tendsto_nhds_unique
    (tendsto_jointPoleSum_of_separatePlaceLimits poles assign₁ term L₁ hL₁ hlo hhi)
    (tendsto_jointPoleSum_of_separatePlaceLimits poles assign₂ term L₂ hL₂ hlo hhi)

open Classical in
/-- Paper: Theorem B.3.2.1, p. 606. For the contour shift used on p. 322, if the separate
residue sums converge for any assignment, then their sum equals the normalized difference of
vertical line integrals. -/
theorem sum_separatePlaceLimits_eq_verticalLineIntegral_sub {ι : Type*} [Fintype ι]
    {f Φ : ℂ → ℂ} {a b a' b' σ₁ σ₂ : ℝ} {T : ℤ → ℝ}
    (hT : WitnessesSlowGrowthNearPoles f a b T) (ha : a' < a) (hb : b < b')
    (hΦ : UniformlySchwartzOnStrip Φ a' b') (hσ₁ : a < σ₁) (hσ : σ₁ < σ₂) (hσ₂ : σ₂ < b)
    (hSides : ∀ σ ∈ ({σ₁, σ₂} : Set ℝ),
      let trace := fun y : ℝ ↦ f ((σ : ℂ) + y * Complex.I)
      Continuous trace ∧ ∃ γ > (0 : ℝ), trace =O[comap abs atTop] (fun y : ℝ ↦ |y| ^ γ))
    (hHeights : ∀ k : ℕ, 0 < k → T (-(k : ℤ)) < 0 ∧ 0 < T (k : ℤ))
    (assign : ℂ → ι) (L : ι → ℂ)
    (hL : ∀ v, Tendsto (fun h : ℝ × ℝ ↦ ∑ z ∈
      (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hT.2.1 hσ₁ hσ₂).toFinset.filter
        (assign · = v), complexResidue (fun s ↦ Φ s * f s) z) (atBot ×ˢ atTop) (𝓝 (L v))) :
    ∑ v, L v = (verticalLineIntegral (fun s ↦ Φ s * f s) σ₂ -
      verticalLineIntegral (fun s ↦ Φ s * f s) σ₁) / (2 * (Real.pi : ℂ) * Complex.I) := by
  have hk : ∀ᶠ k : ℕ in atTop, 0 < k := eventually_gt_atTop 0
  have hIndex : Tendsto (fun k : ℕ ↦ (k : ℤ)) atTop (comap abs atTop) := by
    apply tendsto_comap_iff.mpr
    simpa [Function.comp_def, abs_of_nonneg (Int.natCast_nonneg _)] using
      (tendsto_natCast_atTop_atTop (R := ℤ))
  have hLo : Tendsto (fun k : ℕ ↦ T (-(k : ℤ))) atTop atBot := by
    have hNeg : Tendsto (fun k : ℕ ↦ -(k : ℤ)) atTop (comap abs atTop) :=
      tendsto_comap_iff.mpr (by simpa [Function.comp_def] using tendsto_comap_iff.mp hIndex)
    exact (tendsto_neg_atTop_atBot.comp (hT.2.2.2.2.1.comp hNeg)).congr'
      (hk.mono fun k h ↦ neg_eq_iff_eq_neg.mpr (abs_of_neg (hHeights k h).1))
  have hHi : Tendsto (fun k : ℕ ↦ T (k : ℤ)) atTop atTop :=
    (hT.2.2.2.2.1.comp hIndex).congr' (hk.mono fun k h ↦ abs_of_pos (hHeights k h).2)
  exact tendsto_nhds_unique (tendsto_jointPoleSum_of_separatePlaceLimits _ assign _ L hL hLo hHi)
    (tendsto_rectangleResidueSum hT ha hb hΦ hσ₁ hσ hσ₂ hSides hHeights)

/-- Reassigning a finite subset `E ⊆ s` shifts each fiber sum by a constant independent of `s`. -/
private theorem filter_sum_sub_of_subset {ι : Type*} [DecidableEq ι]
    (s E : Finset ℂ) (hEs : E ⊆ s) (assign₁ assign₂ : ℂ → ι)
    (hagree : ∀ a ∈ s, a ∉ E → assign₁ a = assign₂ a) (term : ℂ → ℂ) (v : ι) :
    ∑ a ∈ s.filter (assign₂ · = v), term a =
      (∑ a ∈ s.filter (assign₁ · = v), term a) +
        ((∑ a ∈ E.filter (assign₂ · = v), term a) -
          (∑ a ∈ E.filter (assign₁ · = v), term a)) := by
  classical
  have hsplit (assign : ℂ → ι) :
      ∑ a ∈ s.filter (assign · = v), term a =
        (∑ a ∈ E.filter (assign · = v), term a) +
          (∑ a ∈ (s \ E).filter (assign · = v), term a) := by
    rw [← Finset.sum_union]
    · congr 1
      ext a
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · intro ⟨has, hav⟩
        by_cases haE : a ∈ E
        · exact Or.inl ⟨haE, hav⟩
        · exact Or.inr ⟨⟨has, haE⟩, hav⟩
      · rintro (⟨haE, hav⟩ | ⟨⟨has, _⟩, hav⟩)
        · exact ⟨hEs haE, hav⟩
        · exact ⟨has, hav⟩
    · rw [Finset.disjoint_left]
      intro a ha₁ ha₂
      exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp ha₂).1).2 (Finset.mem_filter.mp ha₁).1
  have hsdiff : (s \ E).filter (assign₂ · = v) = (s \ E).filter (assign₁ · = v) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor <;> rintro ⟨⟨has, haE⟩, hav⟩
    · exact ⟨⟨has, haE⟩, (hagree a has haE).trans hav⟩
    · exact ⟨⟨has, haE⟩, (hagree a has haE).symm.trans hav⟩
  rw [hsplit assign₂, hsplit assign₁, hsdiff]
  ring

/-- A finite set of complex numbers lies inside every sufficiently tall horizontal window. -/
private theorem eventually_im_mem_Ioo_of_finset (E : Finset ℂ) :
    ∀ᶠ h : ℝ × ℝ in atBot ×ˢ atTop, ∀ a ∈ E, a.im ∈ Ioo h.1 h.2 := by
  by_cases hE : E.Nonempty
  · let lo : ℝ := (E.image Complex.im).min' (hE.image Complex.im) - 1
    let hi : ℝ := (E.image Complex.im).max' (hE.image Complex.im) + 1
    have hlo : ∀ᶠ x : ℝ in atBot, x ≤ lo := eventually_le_atBot lo
    have hhi : ∀ᶠ y : ℝ in atTop, hi ≤ y := eventually_ge_atTop hi
    filter_upwards [hlo.prod_mk hhi] with h hh a ha
    have him : a.im ∈ E.image Complex.im := Finset.mem_image_of_mem Complex.im ha
    have hmin : (E.image Complex.im).min' (hE.image Complex.im) ≤ a.im :=
      Finset.min'_le _ _ him
    have hmax : a.im ≤ (E.image Complex.im).max' (hE.image Complex.im) :=
      Finset.le_max' _ _ him
    exact ⟨by dsimp [lo] at hh; linarith [hh.1], by dsimp [hi] at hh; linarith [hh.2]⟩
  · rw [Finset.not_nonempty_iff_eq_empty] at hE
    subst hE
    exact Eventually.of_forall fun _ _ ha ↦ (Finset.notMem_empty _ ha).elim

/-- Adding a constant function independent of the filter index preserves uniform convergence. -/
private theorem tendstoUniformlyOn_add_const {ι X : Type*} {l : Filter ι} {K : Set X}
    {F G : ι → X → ℂ} {L C : X → ℂ}
    (hF : TendstoUniformlyOn F L l K)
    (heq : ∀ᶠ i in l, ∀ x ∈ K, G i x = F i x + C x) :
    TendstoUniformlyOn G (fun x ↦ L x + C x) l K := by
  rw [Metric.tendstoUniformlyOn_iff] at hF ⊢
  intro ε hε
  filter_upwards [hF ε hε, heq] with i hi he x hx
  rw [he x hx, dist_add_right]
  exact hi x hx

/-- One direction of invariance of `sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor` under
changing `assign` on finitely many strip poles. -/
private theorem separatePlaceExpansionFor_mp_of_finite_diff (χ : PontryaginDual Jₛ)
    (A : ℝ) (hA : 0 < A) (assign₁ assign₂ : ℂ → Places)
    (hfin : {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 ∧
      assign₁ a ≠ assign₂ a}.Finite)
    (h₁ : sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₁) :
    sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₂ := by
  classical
  dsimp only [sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor] at h₁ ⊢
  obtain ⟨L₁, hK₁, hB₁, hrem₁, hBrem₁⟩ := h₁
  let E : Finset ℂ := hfin.toFinset
  let Z (f : Tests) (z : ℂ) := sLocalIdelicZFunction f (chart(χ) z)
  let r (g : Jₛ) : ℝ := (normₛ g).val
  let term (f : Tests) (g : Jₛ) (a : ℂ) : ℂ :=
    star (χ g : ℂ) * complexResidue (fun z ↦ (r g : ℂ) ^ (-z) * Z f z) a
  let poles (h : ℝ × ℝ) := (finite_rectanglePoles
    (f := fun z ↦ sLocalRhoFactor (chart(χ) z)) (a := -A - 1) (b := 2)
    (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
    (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).toFinset
  let shift (v : Places) (f : Tests) (g : Jₛ) : ℂ :=
    (∑ a ∈ E.filter (assign₂ · = v), term f g a) -
      (∑ a ∈ E.filter (assign₁ · = v), term f g a)
  have hshift_sum (f : Tests) (g : Jₛ) : ∑ v : Places, shift v f g = 0 := by
    simp only [shift, Finset.sum_sub_distrib, Finset.sum_fiberwise, sub_self]
  have hsub : ∀ᶠ h : ℝ × ℝ in atBot ×ˢ atTop, E ⊆ poles h := by
    filter_upwards [eventually_im_mem_Ioo_of_finset E] with h hh a ha
    have haE := hfin.mem_toFinset.mp ha
    exact (finite_rectanglePoles (f := fun z ↦ sLocalRhoFactor (chart(χ) z)) (a := -A - 1)
      (b := 2) (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
      (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).mem_toFinset.mpr
      ⟨haE.1, hh a ha, haE.2.1⟩
  have hagree (h : ℝ × ℝ) (a : ℂ) (ha : a ∈ poles h) (haE : a ∉ E) :
      assign₁ a = assign₂ a := by
    by_contra hne
    have hap := (finite_rectanglePoles (f := fun z ↦ sLocalRhoFactor (chart(χ) z)) (a := -A - 1)
      (b := 2) (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
      (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).mem_toFinset.mp ha
    exact haE (hfin.mem_toFinset.mpr ⟨hap.1, hap.2.2, hne⟩)
  have hdiff : ∀ᶠ h : ℝ × ℝ in atBot ×ˢ atTop, ∀ (v : Places) (f : Tests) (g : Jₛ),
      (∑ a ∈ (poles h).filter (assign₂ · = v), term f g a) =
        (∑ a ∈ (poles h).filter (assign₁ · = v), term f g a) + shift v f g := by
    filter_upwards [hsub] with h hEs v f g
    exact filter_sum_sub_of_subset (poles h) E hEs assign₁ assign₂ (hagree h) (term f g) v
  refine ⟨fun v f g ↦ L₁ v f g + shift v f g, ?_, ?_, ?_, ?_⟩
  · intro v f K hK
    exact tendstoUniformlyOn_add_const (hK₁ v f K hK)
      (hdiff.mono fun h hh g _ ↦ hh v f g)
  · intro v g hg B hB
    exact tendstoUniformlyOn_add_const (hB₁ v g hg B hB)
      (hdiff.mono fun h hh f _ ↦ hh v f g)
  · intro f
    refine ⟨(hrem₁ f).1, fun g hg ↦ ?_⟩
    have hsum : (∑ v : Places, (L₁ v f g + shift v f g)) = ∑ v : Places, L₁ v f g := by
      rw [Finset.sum_add_distrib, hshift_sum, add_zero]
    simpa only [hsum] using (hrem₁ f).2 g hg
  · intro B hB
    obtain ⟨C, hC, hbound⟩ := hBrem₁ B hB
    refine ⟨C, hC, fun f hf g hg ↦ ?_⟩
    have hsum : (∑ v : Places, (L₁ v f g + shift v f g)) = ∑ v : Places, L₁ v f g := by
      rw [Finset.sum_add_distrib, hshift_sum, add_zero]
    simpa only [hsum] using hbound f hf g hg

/-- Changing a pole assignment on finitely many strip poles does not affect whether the
separately summed expansion of Theorem 7.1.2.3 holds. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_iff_of_finite_diff
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A) (assign₁ assign₂ : ℂ → Places)
    (hfin : {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 ∧
      assign₁ a ≠ assign₂ a}.Finite) :
    sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₁ ↔
      sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₂ := by
  refine ⟨separatePlaceExpansionFor_mp_of_finite_diff χ A hA assign₁ assign₂ hfin, ?_⟩
  have hfin' : {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0 ∧
      assign₂ a ≠ assign₁ a}.Finite :=
    hfin.subset fun a ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3.symm⟩
  exact separatePlaceExpansionFor_mp_of_finite_diff χ A hA assign₂ assign₁ hfin'

/-! ## Classification of shared poles and assignment independence across distinct primes -/

/-- Only finitely many archimedean poles of `sLocalRhoFactor (chart(χ) ·)` have real part in
`[-A, 1]`. -/
theorem sLocalPoleContributes_archimedean_finite_in_strip (χ : PontryaginDual Jₛ) (A : ℝ) :
    {a : ℂ | a.re ∈ Icc (-A) 1 ∧ ∃ w : InfinitePlace F,
      sLocalPoleContributes χ (Sum.inl w) a}.Finite := by
  have hreal (w : InfinitePlace F) (hw : w.IsReal) :
      {a : ℂ | a.re ∈ Icc (-A) 1 ∧
        let p := (realLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
        ∃ n : ℕ, a = -p.1 - ((2 * n + p.2.val : ℕ) : ℂ)}.Finite := by
    let p := (realLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
    let N : ℕ := ⌈A + (-p.1).re⌉₊ + 1
    refine ((Finset.range N).finite_toSet.image
      (fun n : ℕ ↦ -p.1 - ((2 * n + p.2.val : ℕ) : ℂ))).subset ?_
    rintro a ⟨ha, n, rfl⟩
    refine ⟨n, Finset.mem_range.mpr ?_, rfl⟩
    have hre : (-p.1 - ((2 * n + p.2.val : ℕ) : ℂ)).re = (-p.1).re - (2 * n + p.2.val : ℝ) := by
      simp
    have hle : (n : ℝ) ≤ A + (-p.1).re := by
      have hp2 : (0 : ℝ) ≤ (p.2.val : ℝ) := Nat.cast_nonneg _
      have h1 : -A ≤ (-p.1).re - (2 * (n : ℝ) + (p.2.val : ℝ)) := by
        have ha1 : -A ≤ (-p.1 - ((2 * n + p.2.val : ℕ) : ℂ)).re := ha.1
        simpa [hre] using ha1
      linarith
    have hceil : (n : ℝ) ≤ (⌈A + (-p.1).re⌉₊ : ℝ) := hle.trans (Nat.le_ceil _)
    have hnat : n ≤ ⌈A + (-p.1).re⌉₊ := by exact_mod_cast hceil
    omega
  have hcomplex (w : InfinitePlace F) (hw : w.IsComplex) :
      {a : ℂ | a.re ∈ Icc (-A) 1 ∧
        let p := (complexLocalEulerParameters w hw
          (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
        ∃ n : ℕ, a = -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)}.Finite := by
    let p := (complexLocalEulerParameters w hw
      (sLocalInfiniteRestriction w (chart(χ) 0))).exists.choose
    let N : ℕ := ⌈A + (-p.1).re⌉₊ + 1
    refine ((Finset.range N).finite_toSet.image
      (fun n : ℕ ↦ -p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ))).subset ?_
    rintro a ⟨ha, n, rfl⟩
    refine ⟨n, Finset.mem_range.mpr ?_, rfl⟩
    have hre : (-p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)).re =
        (-p.1).re - (p.2.natAbs : ℝ) / 2 - (n : ℝ) := by
      simp
    have hle : (n : ℝ) ≤ A + (-p.1).re := by
      have hp2 : (0 : ℝ) ≤ (p.2.natAbs : ℝ) / 2 := by positivity
      have h1 : -A ≤ (-p.1).re - (p.2.natAbs : ℝ) / 2 - (n : ℝ) := by
        have ha1 : -A ≤ (-p.1 - (p.2.natAbs : ℂ) / 2 - (n : ℂ)).re := ha.1
        simpa [hre] using ha1
      linarith
    have hceil : (n : ℝ) ≤ (⌈A + (-p.1).re⌉₊ : ℝ) := hle.trans (Nat.le_ceil _)
    have hnat : n ≤ ⌈A + (-p.1).re⌉₊ := by exact_mod_cast hceil
    omega
  have hunion :
      {a : ℂ | a.re ∈ Icc (-A) 1 ∧ ∃ w : InfinitePlace F,
        sLocalPoleContributes χ (Sum.inl w) a} =
      ⋃ w : InfinitePlace F,
        {a : ℂ | a.re ∈ Icc (-A) 1 ∧ sLocalPoleContributes χ (Sum.inl w) a} := by
    ext a
    simp
  rw [hunion]
  refine Set.finite_iUnion fun w ↦ ?_
  by_cases hw : w.IsReal
  · refine (hreal w hw).subset ?_
    rintro a ⟨ha, h⟩
    rcases h with ⟨_, n, hn⟩ | ⟨hc, _⟩
    · exact ⟨ha, n, hn⟩
    · exact absurd hw (InfinitePlace.not_isReal_iff_isComplex.mpr hc)
  · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hw
    refine (hcomplex w hc).subset ?_
    rintro a ⟨ha, h⟩
    rcases h with ⟨hr, _⟩ | ⟨_, n, hn⟩
    · exact absurd hr hw
    · exact ⟨ha, n, hn⟩

/-- The absolute norm of a finite place is a positive power of the rational prime below it. -/
private theorem finitePlace_absNorm_eq_prime_pow (v : Primes) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ v.asIdeal.under ℤ = Ideal.span {(ℓ : ℤ)} ∧
      ∃ f : ℕ, 0 < f ∧ v.asIdeal.absNorm = ℓ ^ f := by
  set P := v.asIdeal.under ℤ
  have hP : P.IsPrime := Ideal.IsPrime.under ℤ v.asIdeal
  have hP0 : P ≠ ⊥ := mt Ideal.eq_bot_of_under_eq_bot v.ne_bot
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal P).principal
  have hg' : P = Ideal.span {g} := hg
  have hg0 : g ≠ 0 := by rintro rfl; exact hP0 (by rw [hg']; simp)
  have hgp : Prime g := (Ideal.span_singleton_prime hg0).mp (hg' ▸ hP)
  refine ⟨g.natAbs, Int.prime_iff_natAbs_prime.mp hgp, by rw [hg', Int.span_natAbs], ?_⟩
  have : v.asIdeal.LiesOver P := ⟨rfl⟩
  refine ⟨v.asIdeal.inertiaDeg ℤ, Ideal.inertiaDeg_pos v.asIdeal ℤ, ?_⟩
  rw [← Ideal.absNorm_pow_inertiaDeg P v.asIdeal, hg', Ideal.absNorm_span_singleton]
  simp

/-- The rationals have a single height-one prime above each nonzero prime ideal of `ℤ`. -/
private theorem rat_prime_unique_above (P : Ideal ℤ) [P.IsMaximal]
    (a b : HeightOneSpectrum (𝓞 ℚ))
    (ha : a.asIdeal.under ℤ = P) (hb : b.asIdeal.under ℤ = P) : a = b := by
  have hsum := Ideal.sum_ramification_inertia_eq_finrank P (𝓞 ℚ)
  rw [RingOfIntegers.rank, Module.finrank_self] at hsum
  have hcard : Fintype.card (P.primesOver (𝓞 ℚ)) ≤ 1 := by
    rw [← hsum, Fintype.card_eq_sum_ones]
    refine Finset.sum_le_sum fun q _ ↦ ?_
    have := q.2.1
    have := q.2.2
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Ideal.ramificationIdx_pos ℤ q.1).ne' (Ideal.inertiaDeg_pos q.1 ℤ).ne')
  let ea : P.primesOver (𝓞 ℚ) := ⟨a.asIdeal, a.isPrime, ⟨ha.symm⟩⟩
  let eb : P.primesOver (𝓞 ℚ) := ⟨b.asIdeal, b.isPrime, ⟨hb.symm⟩⟩
  exact HeightOneSpectrum.ext (congrArg Subtype.val (Fintype.card_le_one_iff.mp hcard ea eb))

/-- Finite places with multiplicatively dependent absolute norms lie over the same rational
prime. -/
private theorem finitePlace_under_eq_of_absNorm_pow_eq (v w : Primes) {m n : ℕ}
    (hm : 0 < m) (_hn : 0 < n) (h : v.asIdeal.absNorm ^ m = w.asIdeal.absNorm ^ n) :
    v.under (𝓞 ℚ) = w.under (𝓞 ℚ) := by
  obtain ⟨ℓ, hℓ, hvP, f, hf, hvN⟩ := finitePlace_absNorm_eq_prime_pow v
  obtain ⟨ℓ', hℓ', hwP, g, hg, hwN⟩ := finitePlace_absNorm_eq_prime_pow w
  rw [hvN, hwN, ← pow_mul, ← pow_mul] at h
  have hdvd : ℓ ∣ ℓ' := hℓ.dvd_of_dvd_pow (h ▸ dvd_pow_self ℓ (by positivity))
  have hll : ℓ = ℓ' := (Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp hdvd
  subst hll
  have hpr : (Ideal.span {(ℓ : ℤ)}).IsPrime := hvP ▸ Ideal.IsPrime.under ℤ v.asIdeal
  have : (Ideal.span {(ℓ : ℤ)}).IsMaximal := hpr.isMaximal (by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact_mod_cast hℓ.ne_zero)
  apply rat_prime_unique_above (Ideal.span {(ℓ : ℤ)})
  · change (v.asIdeal.under (𝓞 ℚ)).under ℤ = _
    rw [Ideal.under_under, hvP]
  · change (w.asIdeal.under (𝓞 ℚ)).under ℤ = _
    rw [Ideal.under_under, hwP]

/-- Two poles contributed by the same finite place differ by an integer multiple of its period
times `i`. -/
private theorem sLocalPoleContributes_finite_sub (χ : PontryaginDual Jₛ) (v : S)
    {a₁ a₂ : ℂ} (h₁ : sLocalPoleContributes χ (Sum.inr v) a₁)
    (h₂ : sLocalPoleContributes χ (Sum.inr v) a₂) :
    ∃ k : ℤ, a₂ - a₁ =
      (((k : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) : ℝ) : ℂ) * Complex.I := by
  obtain ⟨m₁, t₁, ht₁, hchar₁, ha₁⟩ := h₁
  obtain ⟨m₂, t₂, ht₂, hchar₂, ha₂⟩ := h₂
  obtain ⟨π, hπ, -⟩ := sLocalRhoFactor_poles_iff_finite χ v
  have hq : 1 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  set L : ℝ := Real.log (v.val.asIdeal.absNorm : ℝ)
  have hL : 0 < L := Real.log_pos hq
  have hπ0 : 0 < ‖π.val‖ := norm_pos_iff.mpr π.ne_zero
  have hcp (t : ℝ) :
      ((‖π.val‖ : ℝ) : ℂ) ^ ((t : ℂ) * Complex.I) =
        Complex.exp (-((t * L : ℝ) : ℂ) * Complex.I) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hπ0.ne'),
      ← Complex.ofReal_log hπ0.le, hπ, Real.log_inv]
    congr 1
    dsimp only [L]
    push_cast
    ring
  have heq : ((‖π.val‖ : ℝ) : ℂ) ^ ((t₁ : ℂ) * Complex.I) =
      ((‖π.val‖ : ℝ) : ℂ) ^ ((t₂ : ℂ) * Complex.I) :=
    (hchar₁ π).symm.trans (hchar₂ π)
  rw [hcp t₁, hcp t₂, Complex.exp_eq_exp_iff_exists_int] at heq
  obtain ⟨n, hn⟩ := heq
  have hreal : -(t₁ * L) = -(t₂ * L) + (n : ℝ) * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hdiff : t₂ - t₁ = (n : ℝ) * (2 * Real.pi / L) := by
    have hLne : L ≠ 0 := hL.ne'
    field_simp [hLne]
    linarith
  refine ⟨m₂ - m₁ - n, ?_⟩
  rw [ha₁, ha₂]
  have hcoeff : ((m₂ : ℝ) * (2 * Real.pi / L) - t₂) -
      ((m₁ : ℝ) * (2 * Real.pi / L) - t₁) =
      (((m₂ - m₁ - n : ℤ) : ℝ) * (2 * Real.pi / L)) := by
    push_cast
    linarith [hdiff]
  calc
    (((m₂ : ℝ) * (2 * Real.pi / L) - t₂ : ℝ) : ℂ) * Complex.I -
        (((m₁ : ℝ) * (2 * Real.pi / L) - t₁ : ℝ) : ℂ) * Complex.I
      = (((((m₂ : ℝ) * (2 * Real.pi / L) - t₂) -
          ((m₁ : ℝ) * (2 * Real.pi / L) - t₁)) : ℝ) : ℂ) * Complex.I := by
          push_cast
          ring
    _ = _ := by rw [hcoeff]

/-- Paper: Theorem 7.1.3.2(1), p. 324. Two finite places in `S` over distinct rational primes
contribute at most one pole in common, for every unitary S-local character `χ`. -/
theorem sLocalPoleContributes_finite_common_subsingleton (χ : PontryaginDual Jₛ)
    (v w : S) (hp : v.val.under (𝓞 ℚ) ≠ w.val.under (𝓞 ℚ)) :
    {a : ℂ | sLocalPoleContributes χ (Sum.inr v) a ∧
      sLocalPoleContributes χ (Sum.inr w) a}.Subsingleton := by
  intro a₁ ha₁ a₂ ha₂
  by_contra hne
  obtain ⟨m, hm⟩ := sLocalPoleContributes_finite_sub χ v ha₁.1 ha₂.1
  obtain ⟨n, hn⟩ := sLocalPoleContributes_finite_sub χ w ha₁.2 ha₂.2
  set lv : ℝ := Real.log (v.val.asIdeal.absNorm : ℝ)
  set lw : ℝ := Real.log (w.val.asIdeal.absNorm : ℝ)
  have hqv : 1 < (v.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm v.val
  have hqw : 1 < (w.val.asIdeal.absNorm : ℝ) := by
    exact_mod_cast HeightOneSpectrum.one_lt_absNorm w.val
  have hlv : 0 < lv := Real.log_pos hqv
  have hlw : 0 < lw := Real.log_pos hqw
  have him : (m : ℝ) * (2 * Real.pi / lv) = (n : ℝ) * (2 * Real.pi / lw) := by
    have := congrArg Complex.im (hm.symm.trans hn)
    simpa only [lv, lw, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_one, mul_zero, add_zero] using this
  have hreal : (m : ℝ) * lw = (n : ℝ) * lv := by
    have h2pi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have : ((m : ℝ) / lv) * (2 * Real.pi) = ((n : ℝ) / lw) * (2 * Real.pi) := by
      linarith [show (m : ℝ) * (2 * Real.pi / lv) = ((m : ℝ) / lv) * (2 * Real.pi) by ring,
        show (n : ℝ) * (2 * Real.pi / lw) = ((n : ℝ) / lw) * (2 * Real.pi) by ring]
    have hdiv : (m : ℝ) / lv = (n : ℝ) / lw := mul_right_cancel₀ h2pi this
    rwa [div_eq_div_iff hlv.ne' hlw.ne'] at hdiv
  have hm0 : m ≠ 0 := by
    rintro rfl
    apply hne
    have : a₂ - a₁ = 0 := by simpa using hm
    exact (sub_eq_zero.mp this).symm
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [Int.cast_zero, zero_mul, mul_eq_zero, hlw.ne', or_false] at hreal
    exact hm0 (by exact_mod_cast hreal)
  have habs : (m.natAbs : ℝ) * lw = (n.natAbs : ℝ) * lv := by
    have := congrArg abs hreal
    rw [abs_mul, abs_mul, abs_of_pos hlw, abs_of_pos hlv] at this
    simpa [Int.cast_abs] using this
  have hpow : ((v.val.asIdeal.absNorm ^ n.natAbs : ℕ) : ℝ) =
      ((w.val.asIdeal.absNorm ^ m.natAbs : ℕ) : ℝ) := by
    push_cast
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (by positivity)) (Set.mem_Ioi.mpr (by positivity))
    rw [Real.log_pow, Real.log_pow]
    linarith
  exact hp (finitePlace_under_eq_of_absNorm_pow_eq v.val w.val
    (Int.natAbs_pos.mpr hn0) (Int.natAbs_pos.mpr hm0) (by exact_mod_cast hpow))

/-- When `S` contains at most one finite place above each rational prime, only finitely many
strip poles in `Re a ∈ (-A, 1)` are contributed by more than one place. -/
theorem finite_sharedStripPoles_of_injective_under (χ : PontryaginDual Jₛ) (A : ℝ)
    (hinj : Injective (fun v : S ↦ v.val.under (𝓞 ℚ))) :
    {a : ℂ | a.re ∈ Ioo (-A) 1 ∧
      ∃ v₁ v₂ : Places, v₁ ≠ v₂ ∧
        sLocalPoleContributes χ v₁ a ∧ sLocalPoleContributes χ v₂ a}.Finite := by
  classical
  have harch := sLocalPoleContributes_archimedean_finite_in_strip χ A
  have hfinPair :
      (⋃ p : S × S, if p.1 ≠ p.2 then
        {a : ℂ | sLocalPoleContributes χ (Sum.inr p.1) a ∧
          sLocalPoleContributes χ (Sum.inr p.2) a}
      else ∅).Finite := by
    refine Set.finite_iUnion fun p ↦ ?_
    split_ifs with hne
    · exact (sLocalPoleContributes_finite_common_subsingleton χ p.1 p.2
        (fun h ↦ hne (hinj h))).finite
    · exact Set.finite_empty
  refine (harch.union hfinPair).subset ?_
  rintro a ⟨hre, v₁, v₂, hne, h₁, h₂⟩
  cases v₁ with
  | inl w =>
    exact Or.inl ⟨⟨hre.1.le, hre.2.le⟩, w, h₁⟩
  | inr v₁ =>
    cases v₂ with
    | inl w =>
      exact Or.inl ⟨⟨hre.1.le, hre.2.le⟩, w, h₂⟩
    | inr v₂ =>
      refine Or.inr (Set.mem_iUnion.mpr ⟨(v₁, v₂), ?_⟩)
      have hvne : v₁ ≠ v₂ := fun h ↦ hne (congrArg Sum.inr h)
      rw [ite_eq_left hvne]
      exact ⟨h₁, h₂⟩

/-- Paper: Theorem 7.1.2.3, pp. 317–323. When `S` contains at most one finite place above each
rational prime, any two valid pole assignments agree outside finitely many strip poles, so the
truth of the separately summed expansion does not depend on the choice of valid assignment. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_iff_of_injective_under
    (χ : PontryaginDual Jₛ) (A : ℝ) (hA : 0 < A)
    (hinj : Injective (fun v : S ↦ v.val.under (𝓞 ℚ)))
    (assign₁ assign₂ : ℂ → Places)
    (h₁ : IsValidPoleAssignment χ assign₁) (h₂ : IsValidPoleAssignment χ assign₂) :
    sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₁ ↔
      sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₂ := by
  apply sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_iff_of_finite_diff χ A hA
  refine (finite_sharedStripPoles_of_injective_under χ A hinj).subset ?_
  rintro a ⟨hre, hord, hne⟩
  exact ⟨hre, assign₁ a, assign₂ a, hne, h₁ a hord, h₂ a hord⟩

/-- Over `ℚ`, every finite set `S` has at most one finite place per rational prime, so the
repaired separately summed expansion of Theorem 7.1.2.3 has the same truth value for every valid
pole assignment. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_rat_iff
    {S : Finset (HeightOneSpectrum (𝓞 ℚ))}
    (χ : PontryaginDual (SIdeleQuotient ℚ S)) (A : ℝ) (hA : 0 < A)
    (assign₁ assign₂ : ℂ → InfinitePlace ℚ ⊕ S)
    (h₁ : IsValidPoleAssignment χ assign₁) (h₂ : IsValidPoleAssignment χ assign₂) :
    sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₁ ↔
      sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor χ A hA assign₂ := by
  refine sLocalHomogeneousAdelicTheta_separatePlaceExpansionFor_iff_of_injective_under
    χ A hA ?_ assign₁ assign₂ h₁ h₂
  intro v w hvw
  apply Subtype.ext
  apply HeightOneSpectrum.ext
  have h := congrArg HeightOneSpectrum.asIdeal hvw
  change v.val.asIdeal.comap (RingHom.id (𝓞 ℚ)) = w.val.asIdeal.comap (RingHom.id (𝓞 ℚ)) at h
  simpa using h

/-! ## Uniform convergence for every assignment under a summable majorant -/

open Classical in
/-- If the residue terms at the strip poles are bounded uniformly on `K` by a summable
nonnegative majorant `M`, then for every assignment `assign`, the separate place partial sums
converge uniformly on `K` along `atBot ×ˢ atTop` to the unconditional sum over each fiber. -/
theorem tendstoUniformlyOn_separatePlacePartialSum_of_summable_bound {ι X : Type*}
    {f : ℂ → ℂ} {a b σ₁ σ₂ : ℝ} (hf : MeromorphicOn f (Complex.re ⁻¹' Ioo a b))
    (hσ₁ : a < σ₁) (hσ₂ : σ₂ < b)
    (assign : ℂ → ι) (term : ℂ → X → ℂ) (K : Set X)
    (M : {z : ℂ // z.re ∈ Ioo σ₁ σ₂ ∧ meromorphicOrderAt f z < 0} → ℝ)
    (hM0 : ∀ z, 0 ≤ M z) (hM : Summable M)
    (hbound : ∀ z, ∀ x ∈ K, ‖term z.val x‖ ≤ M z) (v : ι) :
    let stripPoles := {z : ℂ // z.re ∈ Ioo σ₁ σ₂ ∧ meromorphicOrderAt f z < 0}
    let rectPoles (h : ℝ × ℝ) := (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2)
      hf hσ₁ hσ₂).toFinset
    let partialSum (h : ℝ × ℝ) (x : X) := ∑ z ∈ (rectPoles h).filter (assign · = v), term z x
    let limit (x : X) := ∑' z : stripPoles, if assign z.val = v then term z.val x else 0
    TendstoUniformlyOn partialSum limit (atBot ×ˢ atTop) K := by
  intro stripPoles rectPoles partialSum limit
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hhas : Tendsto (fun s : Finset stripPoles ↦ ∑ b ∈ s, M b) atTop (𝓝 (∑' b, M b)) :=
    hM.hasSum
  rw [Metric.tendsto_atTop] at hhas
  obtain ⟨s₀, hs₀⟩ := hhas (ε / 2) (half_pos hε)
  have htsum_tail : ∀ s : Finset stripPoles, s₀ ⊆ s →
      (∑' z : stripPoles, if z ∉ s then M z else 0) < ε := by
    intro s hs
    have hfin : Summable (fun z : stripPoles ↦ if z ∈ s then M z else 0) :=
      summable_of_ne_finset_zero (s := s) fun z hz ↦ ite_eq_right hz
    have hcompl : Summable (fun z : stripPoles ↦ if z ∉ s then M z else 0) :=
      hM.of_nonneg_of_le (fun z ↦ by by_cases hz : z ∈ s <;> simp [hz, hM0 z])
        (fun z ↦ by by_cases hz : z ∈ s <;> simp [hz, hM0 z])
    have hsplit : (∑' z : stripPoles, if z ∈ s then M z else 0) +
        (∑' z : stripPoles, if z ∉ s then M z else 0) = ∑' z : stripPoles, M z := by
      rw [← hfin.tsum_add hcompl]
      congr 1
      ext z
      by_cases hz : z ∈ s <;> simp [hz]
    have hsum_eq : (∑' z : stripPoles, if z ∈ s then M z else 0) = ∑ z ∈ s, M z := by
      rw [tsum_eq_sum (s := s) (fun z hz ↦ ite_eq_right hz)]
      exact Finset.sum_congr rfl fun z hz ↦ ite_eq_left hz
    have hdist := hs₀ s hs
    rw [Real.dist_eq] at hdist
    have hle : (∑ z ∈ s, M z) ≤ ∑' z : stripPoles, M z :=
      hM.sum_le_tsum s fun z _ ↦ hM0 z
    have hdiff : (∑' z : stripPoles, M z) - (∑ z ∈ s, M z) < ε / 2 := by
      rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hle)] at hdist
      exact hdist
    linarith
  let E : Finset ℂ := s₀.image Subtype.val
  filter_upwards [eventually_im_mem_Ioo_of_finset E] with h hh x hx
  let emb : ↥(rectPoles h) ↪ stripPoles :=
    ⟨fun z ↦ ⟨z.val, by
      have hz := (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hf hσ₁ hσ₂).mem_toFinset.mp z.property
      exact ⟨hz.1, hz.2.2⟩⟩,
      fun a b hab ↦ Subtype.ext (Subtype.mk.inj hab)⟩
  let s : Finset stripPoles := (rectPoles h).attach.map emb
  have hs_sub : s₀ ⊆ s := by
    intro z hz
    have hzE : z.val ∈ E := Finset.mem_image_of_mem Subtype.val hz
    have hzrect : z.val ∈ rectPoles h :=
      (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hf hσ₁ hσ₂).mem_toFinset.mpr
        ⟨z.property.1, hh z.val hzE, z.property.2⟩
    refine Finset.mem_map.mpr ⟨⟨z.val, hzrect⟩, Finset.mem_attach _ _, ?_⟩
    exact Subtype.ext rfl
  let g (z : stripPoles) : ℂ := if assign z.val = v then term z.val x else 0
  have hg_norm (z : stripPoles) : ‖g z‖ ≤ M z := by
    dsimp only [g]
    split_ifs
    · exact hbound z x hx
    · rw [norm_zero]; exact hM0 z
  have hg_summable : Summable g := Summable.of_norm_bounded hM hg_norm
  have hpart : partialSum h x = ∑ z ∈ s, g z := by
    dsimp only [partialSum, s, g]
    rw [Finset.sum_map]
    have hcongr : ∀ z : ↥(rectPoles h),
        (if assign (emb z).val = v then term (emb z).val x else 0) =
          (if assign z.val = v then term z.val x else 0) := fun _ ↦ rfl
    simp_rw [hcongr]
    rw [Finset.sum_attach (rectPoles h) (fun z ↦ if assign z = v then term z x else 0),
      ← Finset.sum_filter]
  have hfin_g : Summable (fun z : stripPoles ↦ if z ∈ s then g z else 0) :=
    summable_of_ne_finset_zero (s := s) fun z hz ↦ ite_eq_right hz
  have hcompl_g : Summable (fun z : stripPoles ↦ if z ∉ s then g z else 0) :=
    Summable.of_norm_bounded hM fun z ↦ by
      by_cases hz : z ∈ s <;> simp [hz, hg_norm z, hM0 z]
  have hsplit_g : limit x = (∑ z ∈ s, g z) + ∑' z : stripPoles, if z ∉ s then g z else 0 := by
    change (∑' z : stripPoles, g z) = _
    have hsum_eq : (∑' z : stripPoles, if z ∈ s then g z else 0) = ∑ z ∈ s, g z := by
      rw [tsum_eq_sum (s := s) (fun z hz ↦ ite_eq_right hz)]
      exact Finset.sum_congr rfl fun z hz ↦ ite_eq_left hz
    rw [← hsum_eq, ← hfin_g.tsum_add hcompl_g]
    congr 1
    ext z
    by_cases hz : z ∈ s <;> simp [hz]
  have hcompl_M : Summable (fun z : stripPoles ↦ if z ∉ s then M z else 0) :=
    hM.of_nonneg_of_le (fun z ↦ by by_cases hz : z ∈ s <;> simp [hz, hM0 z])
      (fun z ↦ by by_cases hz : z ∈ s <;> simp [hz, hM0 z])
  rw [dist_eq_norm, hpart, hsplit_g, add_sub_cancel_left]
  calc
    ‖∑' z : stripPoles, if z ∉ s then g z else 0‖
      ≤ ∑' z : stripPoles, ‖if z ∉ s then g z else 0‖ := norm_tsum_le_tsum_norm hcompl_g.norm
    _ ≤ ∑' z : stripPoles, if z ∉ s then M z else 0 := by
        refine hcompl_g.norm.tsum_le_tsum (fun z ↦ ?_) hcompl_M
        by_cases hz : z ∈ s <;> simp [hz, hg_norm z]
    _ < ε := htsum_tail s hs_sub

/-! ## Uniform pole discreteness over a single rational prime -/

/-- A finite union of translates of a single periodic lattice `ω · ℤ` in `ℝ` is uniformly
discrete. -/
private theorem uniformly_discrete_finite_union_periodic {ι : Type*} [Fintype ι]
    {ω : ℝ} (hω : 0 < ω) (shift : ι → ℝ) :
    ∃ δ > (0 : ℝ), ∀ (i j : ι) (m n : ℤ),
      ((m : ℝ) * ω + shift i) ≠ ((n : ℝ) * ω + shift j) →
      δ ≤ |((m : ℝ) * ω + shift i) - ((n : ℝ) * ω + shift j)| := by
  classical
  let rem (p : ι × ι) : ℝ :=
    (shift p.1 - shift p.2) - (⌊(shift p.1 - shift p.2) / ω⌋ : ℝ) * ω
  have hrem_mem (p : ι × ι) : rem p ∈ Ico 0 ω := by
    have hfl := Int.floor_le ((shift p.1 - shift p.2) / ω)
    have hlt := Int.lt_floor_add_one ((shift p.1 - shift p.2) / ω)
    constructor
    · dsimp [rem]
      have := (le_div_iff₀ hω).mp hfl
      linarith
    · dsimp [rem]
      have := (div_lt_iff₀ hω).mp hlt
      linarith
  let gap (p : ι × ι) : ℝ := if rem p = 0 then ω else min (rem p) (ω - rem p)
  have hgap_pos (p : ι × ι) : 0 < gap p := by
    dsimp [gap]
    split_ifs with h0
    · exact hω
    · have hm := hrem_mem p
      exact lt_min (lt_of_le_of_ne hm.1 (Ne.symm h0)) (sub_pos.mpr hm.2)
  let G : Finset ℝ := insert ω (Finset.univ.image gap)
  have hGne : G.Nonempty := ⟨ω, Finset.mem_insert_self _ _⟩
  let δ : ℝ := G.min' hGne
  have hδ_pos : 0 < δ := by
    rw [Finset.lt_min'_iff]
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx'
    · exact hω
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx'
      exact hgap_pos p
  refine ⟨δ, hδ_pos, fun i j m n hne ↦ ?_⟩
  let k : ℤ := m - n + ⌊(shift i - shift j) / ω⌋
  have hdiff : ((m : ℝ) * ω + shift i) - ((n : ℝ) * ω + shift j) = (k : ℝ) * ω + rem (i, j) := by
    dsimp [k, rem]
    push_cast
    ring
  rw [hdiff]
  by_cases h0 : rem (i, j) = 0
  · rw [h0, add_zero]
    have hk0 : k ≠ 0 := by
      intro hk0
      apply hne
      have hsub0 : ((m : ℝ) * ω + shift i) - ((n : ℝ) * ω + shift j) = 0 := by
        rw [hdiff, hk0, h0]
        simp
      exact sub_eq_zero.mp hsub0
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast this
    have hδw : δ ≤ ω := Finset.min'_le G ω (Finset.mem_insert_self _ _)
    rw [abs_mul, abs_of_pos hω]
    nlinarith
  · have hδg : δ ≤ min (rem (i, j)) (ω - rem (i, j)) := by
      have hmem : gap (i, j) ∈ G :=
        Finset.mem_insert_of_mem (Finset.mem_image_of_mem gap (Finset.mem_univ _))
      have hle := Finset.min'_le G (gap (i, j)) hmem
      simpa [gap, h0] using hle
    have hm := hrem_mem (i, j)
    have hrem_pos : 0 < rem (i, j) := lt_of_le_of_ne hm.1 (Ne.symm h0)
    have hgap_le : min (rem (i, j)) (ω - rem (i, j)) ≤ |(k : ℝ) * ω + rem (i, j)| := by
      by_cases hk : 0 ≤ k
      · have hk' : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        have hpos : 0 ≤ (k : ℝ) * ω + rem (i, j) := by nlinarith
        rw [abs_of_nonneg hpos]
        exact (min_le_left _ _).trans (by nlinarith)
      · have hk' : (k : ℝ) ≤ -1 := by
          have : k ≤ -1 := by omega
          exact_mod_cast this
        have hneg : (k : ℝ) * ω + rem (i, j) ≤ 0 := by nlinarith [hm.2]
        rw [abs_of_nonpos hneg]
        exact (min_le_right _ _).trans (by nlinarith)
    exact hδg.trans hgap_le

/-- Adding a finite set to a uniformly discrete set in `ℂ` preserves uniform discreteness. -/
private theorem uniformly_discrete_union_finite {A B : Set ℂ}
    (hA : A.Finite) (hB : ∃ δ > (0 : ℝ), ∀ x ∈ B, ∀ y ∈ B, x ≠ y → δ ≤ ‖x - y‖) :
    ∃ δ > (0 : ℝ), ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B, x ≠ y → δ ≤ ‖x - y‖ := by
  classical
  obtain ⟨δB, hδB, hBsep⟩ := hB
  let AF : Finset ℂ := hA.toFinset
  have hcross (a : ℂ) : ∃ d > (0 : ℝ), ∀ b ∈ B, a ≠ b → d ≤ ‖a - b‖ := by
    by_cases hnear : ∃ b ∈ B, ‖a - b‖ < δB / 2
    · obtain ⟨b₀, hb₀, hlt⟩ := hnear
      by_cases hab : a = b₀
      · subst hab
        refine ⟨δB, hδB, fun b hb hne ↦ hBsep a hb₀ b hb hne⟩
      · refine ⟨min ‖a - b₀‖ (δB / 2), lt_min (norm_pos_iff.mpr (sub_ne_zero.mpr hab))
            (half_pos hδB), fun b hb hne ↦ ?_⟩
        by_cases hbb : b = b₀
        · subst hbb; exact min_le_left _ _
        · have htri := hBsep b₀ hb₀ b hb (Ne.symm hbb)
          have hsub : ‖b₀ - b‖ ≤ ‖a - b₀‖ + ‖a - b‖ := by
            calc ‖b₀ - b‖ = ‖(b₀ - a) + (a - b)‖ := by ring_nf
              _ ≤ ‖b₀ - a‖ + ‖a - b‖ := norm_add_le _ _
              _ = ‖a - b₀‖ + ‖a - b‖ := by rw [norm_sub_rev]
          exact (min_le_right _ _).trans (by linarith)
    · push Not at hnear
      exact ⟨δB / 2, half_pos hδB, fun b hb _ ↦ hnear b hb⟩
  choose dA hdA hdA_le using hcross
  let pairDists : Finset ℝ :=
    ((AF ×ˢ AF).filter (fun p ↦ p.1 ≠ p.2)).image (fun p ↦ ‖p.1 - p.2‖)
  let crossDists : Finset ℝ := AF.image dA
  let allDists : Finset ℝ := insert δB (pairDists ∪ crossDists)
  have hallNe : allDists.Nonempty := ⟨δB, Finset.mem_insert_self _ _⟩
  let δ : ℝ := allDists.min' hallNe
  have hδ_pos : 0 < δ := by
    rw [Finset.lt_min'_iff]
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr'
    · exact hδB
    · rcases Finset.mem_union.mp hr' with hp | hc
      · obtain ⟨p, hp', rfl⟩ := Finset.mem_image.mp hp
        exact norm_pos_iff.mpr (sub_ne_zero.mpr (Finset.mem_filter.mp hp').2)
      · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hc
        exact hdA a
  refine ⟨δ, hδ_pos, fun x hx y hy hne ↦ ?_⟩
  rcases hx with hxA | hxB <;> rcases hy with hyA | hyB
  · have hmem : ‖x - y‖ ∈ allDists :=
      Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨(x, y), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨hA.mem_toFinset.mpr hxA, hA.mem_toFinset.mpr hyA⟩, hne⟩, rfl⟩))
    exact Finset.min'_le _ _ hmem
  · have hmem : dA x ∈ allDists :=
      Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image_of_mem dA (hA.mem_toFinset.mpr hxA)))
    exact (Finset.min'_le _ _ hmem).trans (hdA_le x y hyB hne)
  · have hmem : dA y ∈ allDists :=
      Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image_of_mem dA (hA.mem_toFinset.mpr hyA)))
    rw [norm_sub_rev]
    exact (Finset.min'_le _ _ hmem).trans (hdA_le y x hxB hne.symm)
  · exact (Finset.min'_le _ _ (Finset.mem_insert_self _ _)).trans (hBsep x hxB y hyB hne)

/-- Paper: Theorem 7.1.2.3, pp. 317–323. If every finite place in `S` lies over the same rational
prime (including `S = ∅`, a single finite place, or any single-prime fiber `S_p`), then all poles
of `sLocalRhoFactor (chart(χ) ·)` in `Re a ∈ [-A, 1]` are uniformly discrete, for every unitary
S-local character `χ` (including characters of infinite order). -/
theorem sLocalStripPoles_uniformly_discrete_of_same_prime (χ : PontryaginDual Jₛ) (A : ℝ)
    (hsame : ∀ v w : S, v.val.under (𝓞 ℚ) = w.val.under (𝓞 ℚ)) :
    let P := {a : ℂ | a.re ∈ Icc (-A) 1 ∧
      meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a < 0}
    ∃ δ > (0 : ℝ), ∀ a ∈ P, ∀ b ∈ P, a ≠ b → δ ≤ ‖a - b‖ := by
  classical
  intro P
  let P_arch : Set ℂ := {a : ℂ | a.re ∈ Icc (-A) 1 ∧
    ∃ w : InfinitePlace F, sLocalPoleContributes χ (Sum.inl w) a}
  let P_fin : Set ℂ := {a : ℂ | ∃ v : S, sLocalPoleContributes χ (Sum.inr v) a}
  have hPsub : P ⊆ P_arch ∪ P_fin := by
    intro a ⟨hre, hord⟩
    obtain ⟨w | v, hv⟩ := (sLocalPoleContributes_exists_iff χ a).mp hord
    · exact Or.inl ⟨hre, w, hv⟩
    · exact Or.inr ⟨v, hv⟩
  have hfin_disc : ∃ δ > (0 : ℝ), ∀ a ∈ P_fin, ∀ b ∈ P_fin, a ≠ b → δ ≤ ‖a - b‖ := by
    by_cases hSne : S.Nonempty
    · let v₀ : S := ⟨hSne.choose, hSne.choose_spec⟩
      obtain ⟨ℓ, hℓ, hv₀P, _, _, _⟩ := finitePlace_absNorm_eq_prime_pow v₀.val
      have hℓ_gt : (1 : ℝ) < (ℓ : ℝ) := by exact_mod_cast hℓ.one_lt
      have hlogℓ : 0 < Real.log (ℓ : ℝ) := Real.log_pos hℓ_gt
      have hf_exists (v : S) : ∃ f : ℕ, 0 < f ∧ v.val.asIdeal.absNorm = ℓ ^ f := by
        obtain ⟨ℓ', hℓ', hvP, f, hf, hvN⟩ := finitePlace_absNorm_eq_prime_pow v.val
        have hunder : v.val.asIdeal.under ℤ = v₀.val.asIdeal.under ℤ := by
          have h := congrArg (fun p : HeightOneSpectrum (𝓞 ℚ) ↦ p.asIdeal.under ℤ) (hsame v v₀)
          simpa [HeightOneSpectrum.under, Ideal.under_under] using h
        have hspan : Ideal.span {(ℓ' : ℤ)} = Ideal.span {(ℓ : ℤ)} := by
          rw [← hvP, hunder, hv₀P]
        have hdvd₁ : (ℓ : ℤ) ∣ (ℓ' : ℤ) :=
          Ideal.mem_span_singleton.mp (hspan ▸ Ideal.subset_span (Set.mem_singleton _))
        have hll : ℓ' = ℓ := (Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp (Int.natCast_dvd_natCast.mp hdvd₁) |>.symm
        subst hll
        exact ⟨f, hf, hvN⟩
      choose deg hdeg_pos hdeg_eq using hf_exists
      let L : ℕ := ∏ v : S, deg v
      have hL_pos : 0 < L := Finset.prod_pos fun v _ ↦ hdeg_pos v
      let ω : ℝ := 2 * Real.pi / ((L : ℝ) * Real.log (ℓ : ℝ))
      have hω_pos : 0 < ω := by positivity
      let shift (v : S) : ℝ :=
        if h : ∃ a : ℂ, sLocalPoleContributes χ (Sum.inr v) a then -h.choose_spec.choose_spec.choose
        else 0
      obtain ⟨δ, hδ, hsep⟩ := uniformly_discrete_finite_union_periodic hω_pos shift
      refine ⟨δ, hδ, fun a ha b hb hne ↦ ?_⟩
      have hcoord (z : ℂ) (hz : z ∈ P_fin) :
          ∃ (v : S) (k : ℤ), z = (((k : ℝ) * ω + shift v : ℝ) : ℂ) * Complex.I := by
        obtain ⟨v, hv⟩ := hz
        have hex : ∃ a : ℂ, sLocalPoleContributes χ (Sum.inr v) a := ⟨z, hv⟩
        let a₀ : ℂ := hex.choose
        have ha₀ : sLocalPoleContributes χ (Sum.inr v) a₀ := hex.choose_spec
        let m₀ : ℤ := ha₀.choose
        let t₀ : ℝ := ha₀.choose_spec.choose
        have ht₀_spec := ha₀.choose_spec.choose_spec
        have hshift_eq : shift v = -t₀ := dite_eq_left hex
        obtain ⟨d, hd⟩ := sLocalPoleContributes_finite_sub χ v ha₀ hv
        have hdvd : deg v ∣ L := Finset.dvd_prod_of_mem deg (Finset.mem_univ v)
        obtain ⟨q, hq⟩ := hdvd
        have hperiod : 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ) = (q : ℝ) * ω := by
          dsimp [ω]
          rw [hdeg_eq v, Nat.cast_pow, Real.log_pow, hq]
          have hdeg0 : (deg v : ℝ) ≠ 0 := by exact_mod_cast (hdeg_pos v).ne'
          have hq0 : (q : ℝ) ≠ 0 := by
            have : q ≠ 0 := by rintro rfl; simp at hq; omega
            exact_mod_cast this
          have hlog0 : Real.log (ℓ : ℝ) ≠ 0 := hlogℓ.ne'
          push_cast
          field_simp [hdeg0, hq0, hlog0]
        refine ⟨v, (m₀ + d) * (q : ℤ), ?_⟩
        have ha₀_eq :
            a₀ = (((m₀ : ℝ) * (2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)) - t₀ : ℝ) : ℂ) *
              Complex.I := ht₀_spec.2.2
        have hz_eq : z = a₀ + (z - a₀) := by ring
        rw [hz_eq, hd, ha₀_eq, hperiod, hshift_eq]
        push_cast
        ring
      obtain ⟨v, k₁, rfl⟩ := hcoord a ha
      obtain ⟨w, k₂, rfl⟩ := hcoord b hb
      have hne' : (k₁ : ℝ) * ω + shift v ≠ (k₂ : ℝ) * ω + shift w := by
        intro heq
        apply hne
        rw [heq]
      have hnorm : ‖(((k₁ : ℝ) * ω + shift v : ℝ) : ℂ) * Complex.I -
          (((k₂ : ℝ) * ω + shift w : ℝ) : ℂ) * Complex.I‖ =
          |((k₁ : ℝ) * ω + shift v) - ((k₂ : ℝ) * ω + shift w)| := by
        rw [← sub_mul, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
          Complex.norm_real, Real.norm_eq_abs]
      rw [hnorm]
      exact hsep v w k₁ k₂ hne'
    · refine ⟨1, zero_lt_one, fun a ha _ _ _ ↦ ?_⟩
      obtain ⟨v, _⟩ := ha
      exact (hSne ⟨v.val, v.property⟩).elim
  obtain ⟨δ, hδ, hsep⟩ :=
    uniformly_discrete_union_finite (sLocalPoleContributes_archimedean_finite_in_strip χ A) hfin_disc
  exact ⟨δ, hδ, fun a ha b hb hne ↦ hsep a (hPsub ha) b (hPsub hb) hne⟩

/-! ## Exact arithmetic criterion on a pole lattice (#7279) -/

/-- The shifted inverse-square sequence `(1 + |m|)⁻²` is summable over `ℤ`. -/
private theorem summable_inv_one_add_abs_sq_int :
    Summable (fun m : ℤ ↦ ((1 + |(m : ℝ)|) ^ 2)⁻¹) := by
  have hnat : Summable (fun n : ℕ ↦ ((1 + (n : ℝ)) ^ 2)⁻¹) := by
    have h := (Real.summable_one_div_nat_pow.mpr (show 1 < 2 by norm_num)).comp_injective
      Nat.succ_injective
    refine h.congr fun n ↦ ?_
    simp [add_comm]
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨?_, ?_⟩
  · exact hnat.congr fun n ↦ by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]
  · exact hnat.congr fun n ↦ by simp [abs_of_nonneg (Nat.cast_nonneg (α := ℝ) n)]

open Classical in
/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323, and the Gaussian-field obstruction in #7279.
For any sequence of complex denominators `D : ℤ → ℂ`, the quotients `b m / D m` (with division
by zero totalized to zero) are summable for every rapidly decreasing sequence `b : ℤ → ℂ` if and
only if `D` satisfies an inverse-polynomial lower bound on its nonzero entries. -/
theorem rapidDecay_div_summable_iff_polyLowerBound (D : ℤ → ℂ) :
    (∀ b : ℤ → ℂ, (∀ k : ℕ, ∃ C : ℝ, ∀ m : ℤ, (1 + |(m : ℝ)|) ^ k * ‖b m‖ ≤ C) →
      Summable (fun m : ℤ ↦ b m / D m)) ↔
    ∃ (c : ℝ) (d : ℕ), 0 < c ∧ ∀ m : ℤ, D m ≠ 0 → c / (1 + |(m : ℝ)|) ^ d ≤ ‖D m‖ := by
  constructor
  · intro hsum
    by_contra hno
    have hstep : ∀ (n M : ℕ), ∃ m : ℤ, M < m.natAbs ∧ D m ≠ 0 ∧
        ‖D m‖ < 1 / (1 + |(m : ℝ)|) ^ n := by
      intro n M
      by_contra hnone
      push Not at hnone
      let box : Finset ℤ := (Finset.Icc (-(M : ℤ)) (M : ℤ)).filter (fun m ↦ D m ≠ 0)
      let norms : Finset ℝ := insert (1 : ℝ) (box.image (fun m ↦ ‖D m‖))
      have hnormsNe : norms.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
      let c : ℝ := norms.min' hnormsNe
      have hc_pos : 0 < c := by
        dsimp only [c]
        rw [Finset.lt_min'_iff]
        intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr'
        · exact zero_lt_one
        · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hr'
          exact norm_pos_iff.mpr (Finset.mem_filter.mp hm).2
      have hc_le1 : c ≤ 1 := Finset.min'_le norms 1 (Finset.mem_insert_self _ _)
      apply hno
      refine ⟨c, n, hc_pos, fun m hm ↦ ?_⟩
      by_cases hM : M < m.natAbs
      · exact (div_le_div_of_nonneg_right hc_le1 (by positivity)).trans (hnone m hM hm)
      · have hm_box : m ∈ box := by
          refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ?_, hm⟩
          have : m.natAbs ≤ M := not_lt.mp hM
          omega
        have hc_leD : c ≤ ‖D m‖ :=
          Finset.min'_le norms ‖D m‖
            (Finset.mem_insert_of_mem (Finset.mem_image_of_mem (fun m ↦ ‖D m‖) hm_box))
        have hpow_ge : (1 : ℝ) ≤ (1 + |(m : ℝ)|) ^ n :=
          one_le_pow₀ (by linarith [abs_nonneg (m : ℝ)])
        exact (div_le_self hc_pos.le hpow_ge).trans hc_leD
    choose pick hpick_gt hpick_ne hpick_lt using hstep
    let seq : ℕ → ℤ := Nat.rec (pick 0 0) (fun j prev ↦ pick (j + 1) prev.natAbs)
    have hseq_ne (j : ℕ) : D (seq j) ≠ 0 := by
      cases j with
      | zero => exact hpick_ne 0 0
      | succ j => exact hpick_ne (j + 1) (seq j).natAbs
    have hseq_lt (j : ℕ) : ‖D (seq j)‖ < 1 / (1 + |(Int.cast (seq j) : ℝ)|) ^ j := by
      cases j with
      | zero => exact hpick_lt 0 0
      | succ j => exact hpick_lt (j + 1) (seq j).natAbs
    have hseq_mono : StrictMono (fun j : ℕ ↦ (seq j).natAbs) := by
      refine strictMono_nat_of_lt_succ fun j ↦ ?_
      exact hpick_gt (j + 1) (seq j).natAbs
    have hseq_inj : Injective seq := fun i j hij ↦
      hseq_mono.injective (congrArg Int.natAbs hij)
    let b : ℤ → ℂ := Set.indicator (Set.range seq) D
    have hb_at (j : ℕ) : b (seq j) = D (seq j) :=
      Set.indicator_of_mem (Set.mem_range_self j) D
    have hb_rapid : ∀ k : ℕ, ∃ C : ℝ, ∀ m : ℤ, (1 + |(m : ℝ)|) ^ k * ‖b m‖ ≤ C := by
      intro k
      let C₀ : ℝ := ∑ j ∈ Finset.range k, (1 + |(Int.cast (seq j) : ℝ)|) ^ k * ‖D (seq j)‖
      refine ⟨1 + C₀, fun m ↦ ?_⟩
      have hC₀_nn : 0 ≤ C₀ := Finset.sum_nonneg fun j _ ↦ by positivity
      rcases Classical.em (m ∈ Set.range seq) with ⟨j, rfl⟩ | hex
      · rw [hb_at j]
        by_cases hjk : j < k
        · have hterm : (1 + |(Int.cast (seq j) : ℝ)|) ^ k * ‖D (seq j)‖ ≤ C₀ :=
            Finset.single_le_sum (f := fun i ↦ (1 + |(Int.cast (seq i) : ℝ)|) ^ k * ‖D (seq i)‖)
              (fun i _ ↦ by positivity) (Finset.mem_range.mpr hjk)
          linarith
        · have hkj : k ≤ j := not_lt.mp hjk
          have hbase : (1 : ℝ) ≤ 1 + |(Int.cast (seq j) : ℝ)| := by
            linarith [abs_nonneg (Int.cast (seq j) : ℝ)]
          have hpow : (1 + |(Int.cast (seq j) : ℝ)|) ^ k ≤ (1 + |(Int.cast (seq j) : ℝ)|) ^ j :=
            pow_le_pow_right₀ hbase hkj
          have hle1 : (1 + |(Int.cast (seq j) : ℝ)|) ^ k * ‖D (seq j)‖ ≤ 1 := by
            calc
              (1 + |(Int.cast (seq j) : ℝ)|) ^ k * ‖D (seq j)‖
                ≤ (1 + |(Int.cast (seq j) : ℝ)|) ^ j * (1 / (1 + |(Int.cast (seq j) : ℝ)|) ^ j) :=
                  mul_le_mul hpow (hseq_lt j).le (norm_nonneg _) (by positivity)
              _ = 1 := by
                  have hpos : (0 : ℝ) < (1 + |(Int.cast (seq j) : ℝ)|) ^ j := by positivity
                  field_simp [hpos.ne']
          linarith
      · have hb0 : b m = 0 := Set.indicator_of_notMem hex D
        rw [hb0, norm_zero, mul_zero]
        linarith
    have hs : Summable (fun m : ℤ ↦ b m / D m) := hsum b hb_rapid
    have hcomp : Tendsto (fun j : ℕ ↦ b (seq j) / D (seq j)) atTop (𝓝 0) :=
      hs.tendsto_cofinite_zero.comp (Nat.cofinite_eq_atTop ▸ hseq_inj.tendsto_cofinite)
    have hone : Tendsto (fun j : ℕ ↦ b (seq j) / D (seq j)) atTop (𝓝 1) :=
      tendsto_const_nhds.congr fun j ↦ (by rw [hb_at j, div_self (hseq_ne j)] : (1 : ℂ) = _)
    exact one_ne_zero (tendsto_nhds_unique hone hcomp)
  · rintro ⟨c, d, hc, hD⟩ b hb
    obtain ⟨C, hC⟩ := hb (d + 2)
    have hC0 : 0 ≤ C := (mul_nonneg (by positivity) (norm_nonneg (b 0))).trans (hC 0)
    refine Summable.of_norm_bounded (summable_inv_one_add_abs_sq_int.mul_left (C / c)) fun m ↦ ?_
    by_cases hm : D m = 0
    · rw [hm, div_zero, norm_zero]
      positivity
    · have hbase : (0 : ℝ) < 1 + |(m : ℝ)| := by linarith [abs_nonneg (m : ℝ)]
      have hDm : c / (1 + |(m : ℝ)|) ^ d ≤ ‖D m‖ := hD m hm
      have hDm_pos : 0 < ‖D m‖ := norm_pos_iff.mpr hm
      have hbm : ‖b m‖ ≤ C / (1 + |(m : ℝ)|) ^ (d + 2) :=
        (le_div_iff₀ (by positivity)).mpr (by rw [mul_comm]; exact hC m)
      rw [norm_div]
      calc
        ‖b m‖ / ‖D m‖
          ≤ (C / (1 + |(m : ℝ)|) ^ (d + 2)) / (c / (1 + |(m : ℝ)|) ^ d) :=
            div_le_div₀ (by positivity) hbm (by positivity) hDm
        _ = (C / c) * ((1 + |(m : ℝ)|) ^ 2)⁻¹ := by
            rw [pow_add]
            field_simp [hc.ne', hbase.ne']

end RiemannMasullo.Isolated

/-! ## Gaussian two-place converse for the separate residue sums

The Gaussian character and the compact Fourier interpolation argument come from
mccorvie's #7279 report (comment 7125686485). Aadrianvv independently identified
the fixed-character necessity (comment 7127211257). The lattice sequence criterion
above is due to dishank-hai (#7458).
-/

namespace RiemannMasullo.Isolated

open scoped Real ContDiff
set_option quotPrecheck false

/-- The norm-nine poles of the fourth-power angular character over the Gaussian field. -/
def gaussianPrimaryCenter (m : ℤ) : ℂ :=
  (m : ℂ) * (2 * Real.pi * Complex.I) / (Real.log 9 : ℂ)

/-- The reciprocal norm-five Euler factor in the Gaussian example of #7279. -/
def gaussianSecondaryFactor (s : ℂ) : ℂ :=
  1 - ((-7 - 24 * Complex.I) / 25) * Complex.exp (-(Real.log 5 : ℂ) * s)

/-- The two-Euler-factor meromorphic function of a compact logarithmic test in #7279. -/
def gaussianTwoFactorZeta (h : ℝ → ℂ) (s : ℂ) : ℂ :=
  bilateralLaplace h s /
    ((1 - Complex.exp (-(Real.log 9 : ℂ) * s)) * gaussianSecondaryFactor s)

private theorem gaussianProfile_analytic {h : ℝ → ℂ} (hh : Continuous h)
    (hc : HasCompactSupport h) (s : ℂ) : AnalyticAt ℂ (bilateralLaplace h) s := by
  have hp (z : ℂ) (x : ℝ) : (Real.exp x : ℂ) ^ z = Complex.exp (z * x) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
      ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp, mul_comm]
  have hA := analyticOnNhd_integral_mul_cpow volume h Real.exp hh.measurable
    Real.continuous_exp.measurable Real.exp_pos (U := univ) isOpen_univ
    (fun a _ ↦ Continuous.integrable_of_hasCompactSupport
      (hh.norm.mul (Real.continuous_exp.rpow_const (fun x ↦ Or.inl (Real.exp_pos x).ne')))
      hc.norm.mul_right)
  change AnalyticAt ℂ (fun z : ℂ ↦ ∫ x : ℝ, h x * Complex.exp (z * x)) s
  simpa only [hp] using hA s (mem_univ _)

private theorem gaussianPrimary_exp (m : ℤ) :
    Complex.exp (-(Real.log 9 : ℂ) * gaussianPrimaryCenter m) = 1 := by
  have hL : (Real.log 9 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  rw [gaussianPrimaryCenter, show -(Real.log 9 : ℂ) *
      ((m : ℂ) * (2 * Real.pi * Complex.I) / (Real.log 9 : ℂ)) =
      ((-m : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I _

private theorem gaussianSecondaryFactor_analytic (s : ℂ) :
    AnalyticAt ℂ gaussianSecondaryFactor s := by
  unfold gaussianSecondaryFactor
  fun_prop

/-- Paper: Theorem 7.1.2.3, p. 318, and the separate absolute sum on p. 389.
At a norm-nine pole away from the norm-five lattice, the residue is the sampled
bilateral Laplace transform divided by the derivative and the surviving Euler factor.
This also covers samples at which the numerator vanishes. -/
theorem gaussianTwoFactorZeta_residue {h : ℝ → ℂ} (hh : Continuous h) (hc : HasCompactSupport h)
    {t : ℝ} (ht : 0 < t) (m : ℤ) (hD : gaussianSecondaryFactor (gaussianPrimaryCenter m) ≠ 0) :
    complexResidue (fun z ↦ (t : ℂ) ^ (-z) * gaussianTwoFactorZeta h z) (gaussianPrimaryCenter m) =
      (t : ℂ) ^ (-gaussianPrimaryCenter m) * bilateralLaplace h (gaussianPrimaryCenter m) /
        ((Real.log 9 : ℂ) * gaussianSecondaryFactor (gaussianPrimaryCenter m)) := by
  let a := gaussianPrimaryCenter m
  let L : ℂ := Real.log 9
  let E (z : ℂ) := 1 - Complex.exp (-L * z)
  have hL : L ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos (by norm_num)).ne'
  have h0 : E a = 0 := sub_eq_zero.mpr (gaussianPrimary_exp m).symm
  have hder : HasDerivAt E L a := by
    have hd := (((hasDerivAt_id a).const_mul (-L)).cexp).const_sub 1
    simpa only [id_eq, mul_one, E, a, L, gaussianPrimary_exp, one_mul, neg_neg] using hd
  have hE : AnalyticAt ℂ E a := by dsimp [E]; fun_prop
  have hn : dslope E a a ≠ 0 := by rw [dslope_same, hder.deriv]; exact hL
  have hW : AnalyticAt ℂ (fun z : ℂ ↦ (t : ℂ) ^ (-z)) a := by
    simp_rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ht.ne')]
    fun_prop
  have hf (z : ℂ) : (z - a) * dslope E a z = E z := by
    simpa only [smul_eq_mul, h0, sub_zero] using sub_smul_dslope E a z
  have heq : (fun z ↦ (t : ℂ) ^ (-z) * gaussianTwoFactorZeta h z) =
      fun z ↦ ((t : ℂ) ^ (-z) * bilateralLaplace h z /
        (dslope E a z * gaussianSecondaryFactor z)) / (z - a) := by
    funext z
    change _ * (_ / (E z * _)) = _
    rw [← hf z]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  have hG : AnalyticAt ℂ (fun z ↦ (t : ℂ) ^ (-z) * bilateralLaplace h z /
      (dslope E a z * gaussianSecondaryFactor z)) a :=
    (hW.mul (gaussianProfile_analytic hh hc a)).div
      ((hE.dslope a).mul (gaussianSecondaryFactor_analytic a)) (mul_ne_zero hn hD)
  change complexResidue _ a = _
  rw [complexResidue_div_sub hG, dslope_same, hder.deriv]

private theorem gaussianPrimaryCenter_re (m : ℤ) : (gaussianPrimaryCenter m).re = 0 := by
  rw [gaussianPrimaryCenter, Complex.div_ofReal_re, Complex.mul_re, Complex.mul_I_re]
  simp

open Classical in
/-- Paper: Theorem 7.1.2.3, p. 318, and the absolute prime sum on p. 389.
Absolute summability for all compact smooth logarithmic tests, at one fixed norm
and outside any finite set of indices, forces an inverse-polynomial lower bound
at every noncolliding index in the Gaussian example. -/
theorem gaussianTwoFactorZeta_polyLowerBound_of_absoluteResidues {t : ℝ} (ht : 0 < t)
    (excluded : Finset ℤ)
    (habs : ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → Function.support h ⊆ Icc 0 (2 * Real.log 9) → Summable (fun m : ℤ ↦
      if m ∈ excluded ∨ gaussianSecondaryFactor (gaussianPrimaryCenter m) = 0 then 0 else
        ‖complexResidue (fun z ↦ (t : ℂ) ^ (-z) * gaussianTwoFactorZeta h z)
          (gaussianPrimaryCenter m)‖)) :
    ∃ (c : ℝ) (d : ℕ), 0 < c ∧ ∀ m : ℤ, gaussianSecondaryFactor (gaussianPrimaryCenter m) ≠ 0 →
      c / (1 + |(m : ℝ)|) ^ d ≤ ‖gaussianSecondaryFactor (gaussianPrimaryCenter m)‖ := by
  apply (rapidDecay_div_summable_iff_polyLowerBound _).mp
  intro b hb
  have hL : 0 < Real.log 9 := Real.log_pos (by norm_num)
  obtain ⟨h, hh, hsupp, hsample⟩ := exists_compactSmooth_logFourier_samples _ hL b hb
  have hc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hs (m : ℤ) : bilateralLaplace h (gaussianPrimaryCenter m) = b m := by
    simpa only [bilateralLaplace, gaussianPrimaryCenter, mul_comm (m : ℂ) (2 * Real.pi * Complex.I)]
      using hsample m
  apply Summable.of_norm
  apply ((habs h hh hsupp).mul_left (Real.log 9)).congr_cofinite
  filter_upwards [excluded.eventually_cofinite_notMem] with m hm
  by_cases hD : gaussianSecondaryFactor (gaussianPrimaryCenter m) = 0
  · simp [hD]
  · have hW : ‖(t : ℂ) ^ (-gaussianPrimaryCenter m)‖ = 1 := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re, gaussianPrimaryCenter_re,
        neg_zero, Real.rpow_zero]
    simp only [hm, hD, or_self, ite_false, gaussianTwoFactorZeta_residue hh.continuous hc ht m hD,
      hs, norm_div, norm_mul, hW, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    field_simp


open Classical in
/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. For the two Gaussian Euler factors
even boundedness above of the real parts of the symmetric residue sums, for every
compact smooth profile on one fixed interval, forces the same polynomial lower bound.
The test can prescribe the phases as well as the sizes of its Fourier samples. -/
theorem gaussianTwoFactorZeta_polyLowerBound_of_bounded_symmetricResidues
    {t : ℝ} (ht : 0 < t) (excluded : Finset ℤ)
    (hbdd : ∀ h : ℝ → ℂ, ContDiff ℝ ∞ h → support h ⊆ Icc 0 (2 * Real.log 9) →
      ∃ A : ℝ, ∀ N : ℕ, (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if m ∈ excluded ∨ gaussianSecondaryFactor (gaussianPrimaryCenter m) = 0 then 0 else
          complexResidue (fun z ↦ (t : ℂ) ^ (-z) * gaussianTwoFactorZeta h z)
            (gaussianPrimaryCenter m)).re ≤ A) :
    ∃ (c : ℝ) (d : ℕ), 0 < c ∧ ∀ m : ℤ, gaussianSecondaryFactor (gaussianPrimaryCenter m) ≠ 0 →
      c / (1 + |(m : ℝ)|) ^ d ≤ ‖gaussianSecondaryFactor (gaussianPrimaryCenter m)‖ := by
  let D (m : ℤ) := gaussianSecondaryFactor (gaussianPrimaryCenter m)
  let W (m : ℤ) := (t : ℂ) ^ (-gaussianPrimaryCenter m)
  have hL : 0 < Real.log 9 := Real.log_pos (by norm_num)
  have hW (m : ℤ) : ‖W m‖ = 1 := by
    dsimp only [W]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.neg_re, gaussianPrimaryCenter_re,
      neg_zero, Real.rpow_zero]
  have hnW (m : ℤ) : W m ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [hW]
    exact one_ne_zero
  apply (rapidDecay_div_summable_iff_polyLowerBound D).mp
  intro b hb
  let a (m : ℤ) := (‖b m‖ : ℂ) * D m / (‖D m‖ : ℂ) / W m
  have ha (m : ℤ) : ‖a m‖ ≤ ‖b m‖ := by
    by_cases hd : D m = 0
    · simp [a, hd]
    · simp only [a, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, hW, div_one]
      exact (mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hd)).le
  obtain ⟨h, hh, hsupp, hsample⟩ := exists_compactSmooth_logFourier_samples _ hL a
    (fun k ↦ (hb k).imp fun C hC m ↦ (mul_le_mul_of_nonneg_left (ha m) (by positivity)).trans (hC m))
  have hc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  have hs (m : ℤ) : bilateralLaplace h (gaussianPrimaryCenter m) = a m := by
    simpa only [bilateralLaplace, gaussianPrimaryCenter, mul_comm (m : ℂ) (2 * Real.pi * Complex.I)]
      using hsample m
  let u (m : ℤ) := if m ∈ excluded then 0 else ‖b m / D m‖ / Real.log 9
  have hu (m : ℤ) : 0 ≤ u m := by dsimp [u]; split_ifs <;> positivity
  have hterm (m : ℤ) :
      (if m ∈ excluded ∨ D m = 0 then 0 else complexResidue
        (fun z ↦ (t : ℂ) ^ (-z) * gaussianTwoFactorZeta h z) (gaussianPrimaryCenter m)) = (u m : ℂ) := by
    by_cases hm : m ∈ excluded
    · simp [hm, u]
    · by_cases hd : D m = 0
      · simp [hm, hd, u]
      · simp only [hm, hd, or_self, ite_false, u, gaussianTwoFactorZeta_residue hh.continuous hc ht m hd, hs,
          norm_div, Complex.ofReal_div, a]
        change W m * (↑‖b m‖ * D m / (‖D m‖ : ℂ) / W m) / ((Real.log 9 : ℂ) * D m) = _
        field_simp [hnW m, hd]
  obtain ⟨A, hA⟩ := hbdd h hh hsupp
  have hsum : Summable u := by
    refine summable_of_sum_le (c := A) hu (fun T ↦ ?_)
    let N := T.sup Int.natAbs
    have hsub : T ⊆ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
      intro m hm
      have hx : m.natAbs ≤ N := Finset.le_sup hm
      rw [Finset.mem_Icc]
      omega
    apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ ↦ hu m)).trans
    have hA' := hA N
    change (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), if m ∈ excluded ∨ D m = 0 then (0 : ℂ) else _).re ≤ A at hA'
    simpa only [hterm, ← Complex.ofReal_sum, Complex.ofReal_re] using hA'
  apply Summable.of_norm
  apply (hsum.mul_right (Real.log 9)).congr_cofinite
  filter_upwards [excluded.eventually_cofinite_notMem] with m hm
  simp [u, hm, hL.ne']

private theorem gaussianTwoFactorZeta_meromorphic {h : ℝ → ℂ} (hh : Continuous h)
    (hc : HasCompactSupport h) (z : ℂ) : MeromorphicAt (gaussianTwoFactorZeta h) z :=
  (gaussianProfile_analytic hh hc z).meromorphicAt.div
    (((by fun_prop : AnalyticAt ℂ (fun s : ℂ ↦ 1 - Complex.exp (-(Real.log 9 : ℂ) * s)) z).mul
      (gaussianSecondaryFactor_analytic z)).meromorphicAt)

private theorem gaussianResidue_congr {f g : ℂ → ℂ} {a : ℂ} (h : f =ᶠ[𝓝[≠] a] g) :
    complexResidue f a = complexResidue g a := by
  obtain ⟨δ, hδ, hEq⟩ := Metric.nhdsWithin_basis_ball.eventually_iff.mp h
  unfold complexResidue limUnder
  refine congrArg lim (Filter.map_congr ?_)
  filter_upwards [Ioo_mem_nhdsGT hδ] with r hr
  rw [circleIntegral.integral_congr hr.1.le fun z hz ↦ hEq ⟨?_, ?_⟩]
  · rw [Metric.mem_ball, Metric.mem_sphere.mp hz]
    exact hr.2
  · rintro rfl
    exact hr.1.ne (by simpa using hz)

/-- Equality on the positive real Mellin axis determines the continued germs. -/
private theorem gaussianResidue_identity {f g : ℂ → ℂ}
    (hf : Meromorphic f) (hg : Meromorphic g) (h : ∀ r : ℝ, 0 < r → f r = g r) (a : ℂ) :
    f =ᶠ[𝓝[≠] a] g := by
  have hlim : Tendsto (fun r : ℝ ↦ (r : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · exact_mod_cast (Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds (a := (1 : ℝ)) (s := Ioi 1)))
    · filter_upwards [self_mem_nhdsWithin] with r hr
      have hr' : 1 < r := hr
      intro he
      change (r : ℂ) = 1 at he
      exact hr'.ne' (by exact_mod_cast he)
  have hfreq : ∃ᶠ z in 𝓝[≠] (1 : ℂ), f z = g z :=
    hlim.frequently (Filter.Eventually.frequently
      (Filter.Eventually.mono self_mem_nhdsWithin (fun r hr ↦ h r (lt_trans zero_lt_one hr))))
  have hΔ : MeromorphicOn (f - g) univ := fun x _ ↦ (hf x).sub (hg x)
  have hO : meromorphicOrderAt (f - g) (1 : ℂ) = ⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    exact (((hf 1).frequently_eq_iff_eventuallyEq (hg 1)).mp hfreq).mono fun z hz ↦ sub_eq_zero.mpr hz
  exact (meromorphicOrderAt_eq_top_iff.mp (hΔ.meromorphicOrderAt_eq_top_of_isPreconnected
    isPreconnected_univ (mem_univ _) (mem_univ a) hO)).mono fun z hz ↦ sub_eq_zero.mp hz
/-- The inverse fourth angular power of the Gaussian prime `2 + i` gives the
norm-five phase in the local character profile. -/
theorem gaussianAngularPhase_two_add_I :
    ((‖(2 + Complex.I : ℂ)‖ : ℂ) / (2 + Complex.I)) ^ 4 = (-7 - 24 * Complex.I) / 25 := by
  have h : ‖(2 + Complex.I : ℂ)‖ ^ 2 = 5 := by
    rw [Complex.sq_norm]
    norm_num [Complex.normSq_apply]
  have h4 : (‖(2 + Complex.I : ℂ)‖ : ℂ) ^ 4 = 25 := by
    rw [show (4 : ℕ) = 2 * 2 by decide, pow_mul, ← Complex.ofReal_pow, h]
    norm_num
  rw [div_pow, h4]
  norm_num [Complex.ext_iff, Complex.div_re, Complex.div_im, Complex.normSq_apply,
    pow_succ, Complex.mul_re, Complex.mul_im]

/-- An annular archimedean test with the inverse of the fourth-power angular character. -/
def gaussianArchLogTest (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  ((‖z‖ : ℂ) / z) ^ 4 * h (2 * Real.log ‖z‖)

private theorem gaussianArchLogTest_zero {h : ℝ → ℂ}
    (hs : support h ⊆ Icc 0 (2 * Real.log 9)) {z : ℂ} (hz : ‖z‖ < 1) :
    gaussianArchLogTest h z = 0 := by
  by_cases hz' : z = 0
  · simp [hz', gaussianArchLogTest]
  have h0 : h (2 * Real.log ‖z‖) = 0 := by
    by_contra ha
    have := (hs ha).1
    linarith [Real.log_neg (norm_pos_iff.mpr hz') hz]
  simp [gaussianArchLogTest, h0]

/-- The lifted test is a genuine Schwartz function supported on the common annulus
`1 ≤ ‖z‖ ≤ 9`, independently of the compact smooth logarithmic profile. -/
theorem gaussianArchLogTest_schwartz {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hs : support h ⊆ Icc 0 (2 * Real.log 9)) :
    ∃ f : SchwartzMap ℂ ℂ, (f : ℂ → ℂ) = gaussianArchLogTest h ∧
      support (f : ℂ → ℂ) ⊆ {z | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 9} := by
  have hS {z : ℂ} (hz : gaussianArchLogTest h z ≠ 0) : 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 9 := by
    refine ⟨le_of_not_gt (fun hn ↦ hz (gaussianArchLogTest_zero hs hn)), ?_⟩
    by_contra! hgt
    have hnon : h (2 * Real.log ‖z‖) ≠ 0 := by
      intro h0
      exact hz (by simp [gaussianArchLogTest, h0])
    have hlog := (hs hnon).2
    linarith [Real.log_lt_log (by norm_num : 0 < (9 : ℝ)) hgt]
  have hcomp : HasCompactSupport (gaussianArchLogTest h) := by
    apply HasCompactSupport.of_support_subset_isCompact (K := Metric.closedBall (0 : ℂ) 9) (isCompact_closedBall _ _)
    exact fun z hz ↦ Metric.mem_closedBall.mpr (by simpa only [dist_zero_right] using (hS hz).2)
  have hsm : ContDiff ℝ ∞ (gaussianArchLogTest h) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) zero_lt_one] with z hz
      exact gaussianArchLogTest_zero hs (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
    · have hn := contDiffAt_norm (n := ∞) ℝ hz
      unfold gaussianArchLogTest
      simp only [div_eq_mul_inv]
      exact (((Complex.ofRealCLM.contDiff.contDiffAt.comp z hn).mul
        ((contDiffAt_id (𝕜 := ℝ)).inv hz)).pow 4).mul
        (hh.contDiffAt.comp z (contDiffAt_const.mul (hn.log (norm_ne_zero_iff.mpr hz))))
  exact ⟨hcomp.toSchwartzMap hsm, rfl, fun _ hz ↦ hS hz⟩

/-- With Euclidean area and the multiplicative density `‖z‖⁻²`, the fourth-power
angular Mellin integral of the test is `π` times its logarithmic Laplace transform. -/
theorem gaussianArchLogTest_mellin (h : ℝ → ℂ) (s : ℂ) :
    (∫ z : ℂ, ((‖z‖ : ℂ)^2)⁻¹ * (gaussianArchLogTest h z *
      (z / (‖z‖ : ℂ))^4 * Complex.exp (s * (2 * (Real.log ‖z‖ : ℂ))))) =
      (Real.pi : ℂ) * bilateralLaplace h s := by
  let M (r : ℝ) := h (2 * Real.log r) * Complex.exp (s * (2 * (Real.log r : ℂ)))
  have hrad (z : ℂ) : ((‖z‖ : ℂ)^2)⁻¹ * (gaussianArchLogTest h z *
      (z / (‖z‖ : ℂ))^4 * Complex.exp (s * (2 * (Real.log ‖z‖ : ℂ)))) =
      ((‖z‖ : ℂ)^2)⁻¹ * M ‖z‖ := by
    by_cases hz : z = 0
    · simp [hz]
    · have hn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
      simp only [gaussianArchLogTest, M]
      field_simp
  simp_rw [hrad]
  rw [Complex.integral_radial (fun r : ℝ ↦ ((r : ℂ)^2)⁻¹ * M r), ← integral_comp_exp]
  have hlog (x : ℝ) : Real.exp x • ((Real.exp x : ℂ) * (((Real.exp x : ℂ)^2)⁻¹ * M (Real.exp x))) =
      (fun y : ℝ ↦ h y * Complex.exp (s * y)) (2 * x) := by
    have hn : (Real.exp x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'
    simp only [M, Real.log_exp, Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_ofNat]
    field_simp
  simp_rw [hlog]
  rw [Measure.integral_comp_mul_left (fun y : ℝ ↦ h y * Complex.exp (s * y)) 2,
    Complex.real_smul, ← bilateralLaplace]
  norm_num
  ring


section GaussianCharacter

open IsDedekindDomain NumberField
open scoped NNReal TensorProduct

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}
local notation "GJ" => SIdeleQuotient F S
local notation "ATest" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "gchart(" χ ")" => quasiCharacterNormTwist (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)
local notation "cm(" hw ")" => InfinitePlace.Completion.ringEquivComplexOfIsComplex hw

local instance (w : InfinitePlace F) : MeasurableSpace w.Completion := borel _
local instance (v : HeightOneSpectrum (𝓞 F)) : MeasurableSpace (v.adicCompletion F)ˣ := borel _

private theorem gaussianArchLocal_realization (χ : PontryaginDual GJ) (w : InfinitePlace F)
    (hw : w.IsComplex)
    (hχ : ∀ u : w.Completionˣ, sLocalInfiniteRestriction w (gchart(χ) 0) u =
      (cm(hw) u.val / (‖cm(hw) u.val‖ : ℂ)) ^ 4)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hs : support h ⊆ Icc 0 (2 * Real.log 9)) :
    ∃ g : SchwartzBruhat (Multiplicative w.Completion), ∀ s : ℂ,
      localIdelicZetaIntegral (infiniteLocalMultiplicativeTamagawaMeasure F w)
        (fun x ↦ g (Multiplicative.ofAdd x)) (sLocalInfiniteRestriction w (gchart(χ) s)) =
        (2 * (Real.pi : ℂ)) * bilateralLaplace h s := by
  let e := cm(hw)
  obtain ⟨f, hf, _⟩ := gaussianArchLogTest_schwartz hh hs
  let g : SchwartzBruhat (Multiplicative w.Completion) :=
    ⟨fun x ↦ gaussianArchLogTest h (e x.toAdd),
      (complexCompletion_mem_schwartzBruhat_iff w hw _).mpr ⟨f, hf⟩⟩
  refine ⟨g, fun s ↦ ?_⟩
  have he (u : w.Completionˣ) : ‖e u.val‖ = ‖u.val‖ :=
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hw).isometry.norm_map_of_map_zero (map_zero e) _
  have hc (u : w.Completionˣ) : sLocalInfiniteRestriction w (gchart(χ) s) u =
      (e u.val / (‖e u.val‖ : ℂ)) ^ 4 * Complex.exp (s * (2 * (Real.log ‖e u.val‖ : ℂ))) := by
    have ht : sLocalInfiniteRestriction w (gchart(χ) s) u =
        sLocalInfiniteRestriction w (gchart(χ) 0) u *
          sLocalInfiniteRestriction w (gchart((1 : PontryaginDual GJ)) s) u := by
      have fact (g : GJ) : gchart(χ) s g = gchart(χ) 0 g * gchart((1 : PontryaginDual GJ)) s g := by
        change _ * _ = ((_ : ℂ) * (_ : ℂ) ^ (0 : ℂ)) * (((1 : PontryaginDual GJ) g : ℂ) * _)
        simp
      exact fact _
    rw [ht, hχ, sLocalInfiniteRestriction_normTwist]
    congr 1
    change ((‖u.val‖ ^ w.mult : ℝ) : ℂ) ^ s = _
    rw [hw.mult_eq_two, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (pow_pos
      (norm_pos_iff.mpr u.ne_zero) 2).ne'), ← Complex.ofReal_log (sq_nonneg _), Real.log_pow,
      he, Complex.ofReal_mul, mul_comm]
    norm_num
  let H (z : ℂ) := gaussianArchLogTest h z * (z / (‖z‖ : ℂ)) ^ 4 *
    Complex.exp (s * (2 * (Real.log ‖z‖ : ℂ)))
  have hfun (u : w.Completionˣ) :
      g (Multiplicative.ofAdd u.val) * sLocalInfiniteRestriction w (gchart(χ) s) u = H (e u.val) := by
    rw [hc]
    exact (mul_assoc _ _ _).symm
  rw [localIdelicZetaIntegral, integral_congr_ae (.of_forall hfun),
    infiniteLocalMultiplicativeTamagawaMeasure_integral_complex w hw H,
    show (∫ z : ℂ, ((‖z‖ : ℂ) ^ 2)⁻¹ * H z) = (Real.pi : ℂ) * bilateralLaplace h s from
      gaussianArchLogTest_mellin h s, mul_assoc]

private theorem gaussianArchFinTensor
    (a : (w : InfinitePlace F) → SchwartzBruhat (Multiplicative w.Completion))
    (b : (v : S) → SchwartzBruhat (Multiplicative (v.val.adicCompletion F))) :
    ∃ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)), ∀ x : SAdeleRing F S,
      f (Multiplicative.ofAdd x) =
        (∏ w, a w (Multiplicative.ofAdd (x.1 w))) * ∏ v, b v (Multiplicative.ofAdd (x.2 v)) := by
  classical
  let G (w : InfinitePlace F) := Multiplicative w.Completion
  let (w : InfinitePlace F) : T2Space (G w) := (inferInstance : T2Space w.Completion)
  let (w : InfinitePlace F) : LocallyCompactSpace (G w) :=
    (inferInstance : LocallyCompactSpace w.Completion)
  let (w : InfinitePlace F) : SecondCountableTopology (G w) :=
    (InfinitePlace.Completion.isometry_extensionEmbedding w).isEmbedding.secondCountableTopology
  obtain ⟨a₀, ha⟩ := schwartzBruhat_pi_test G a
  let e : Multiplicative (InfiniteAdeleRing F) ≃ₜ* ((w : InfinitePlace F) → G w) :=
    { toFun := fun x w ↦ Multiplicative.ofAdd (x.toAdd w)
      invFun := fun x ↦ Multiplicative.ofAdd (fun w ↦ (x w).toAdd)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      continuous_toFun := continuous_id
      continuous_invFun := continuous_id }
  let : T2Space (Multiplicative (InfiniteAdeleRing F)) := e.toHomeomorph.isEmbedding.t2Space
  let : LocallyCompactSpace (Multiplicative (InfiniteAdeleRing F)) :=
    e.toHomeomorph.isOpenEmbedding.locallyCompactSpace
  let arch : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)) :=
    ⟨a₀.val ∘ e, schwartzBruhat_mem_comp_equiv e a₀.property⟩
  obtain ⟨t, ht⟩ := sAdeleSchwartz_inductiveTensor_equiv F S
  refine ⟨t (arch ⊗ₜ[ℂ] (⨂ₜ[ℂ] v : S, b v)), fun x ↦ ?_⟩
  rw [ht arch b x]
  exact congrArg (· * _) (ha (e (Multiplicative.ofAdd x.1)))


/-- In the Gaussian example of #7279 the unique complex place has fourth-power angular
character, and places of norms nine and five are unramified with the indicated
uniformizer values. These assumptions refer only to the character and its places. -/
def HasGaussianTwoPlaceProfile (χ : PontryaginDual GJ) : Prop :=
  let atFinite (q : ℕ) (phase : ℂ) := ∃ (v : S) (p : (v.val.adicCompletion F)ˣ),
    v.val.asIdeal.absNorm = q ∧ ‖p.val‖ = (v.val.asIdeal.absNorm : ℝ)⁻¹ ∧
      (∀ u ∈ (v.val.adicCompletionIntegers F).units, sLocalFiniteRestriction v (gchart(χ) 0) u = 1) ∧
      sLocalFiniteRestriction v (gchart(χ) 0) p = phase
  (∃ (w : InfinitePlace F) (hw : w.IsComplex), (∀ u : InfinitePlace F, u = w) ∧
    ∀ u : w.Completionˣ, sLocalInfiniteRestriction w (gchart(χ) 0) u =
      (cm(hw) u.val / (‖cm(hw) u.val‖ : ℂ)) ^ 4) ∧
    atFinite 9 1 ∧ atFinite 5 ((-7 - 24 * Complex.I) / 25)

/-- Paper: Theorem 7.1.2.3, p. 318. A character with one complex place of angular
weight four and the specified unramified uniformizer values at places of norms nine and five
realizes the Gaussian two-factor function by actual Schwartz–Bruhat tests. At every
other finite place a compact unit test removes its Euler factor. The equality here is for
ordinary convergent Tate integrals on the positive real axis. -/
theorem gaussianTwoFactorZeta_realized_of_character
    (χ : PontryaginDual GJ) (hχ : HasGaussianTwoPlaceProfile χ)
    {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h) (hs : support h ⊆ Icc 0 (2 * Real.log 9)) :
    ∃ f : ATest, ∀ r : ℝ, 0 < r → sLocalIdelicZetaIntegral f (gchart(χ) (r : ℂ)) =
      gaussianTwoFactorZeta h r := by
  classical
  obtain ⟨⟨w, hw, huniq, harch⟩, ⟨v₉, p₉, hq₉, hp₉, hu₉, hχ₉⟩, ⟨v₅, p₅, hq₅, hp₅, hu₅, hχ₅⟩⟩ := hχ
  have hne : v₅ ≠ v₉ := by
    rintro rfl
    omega
  let P (s : ℂ) := 1 - Complex.exp (-(Real.log 9 : ℂ) * s)
  let d (u : S) (s : ℂ) :=
    (if u = v₉ then P s else 1) * (if u = v₅ then gaussianSecondaryFactor s else 1)
  have hfin (u : S) : ∃ (g : SchwartzBruhat (Multiplicative (u.val.adicCompletion F))) (C : ℂ), C ≠ 0 ∧
      ∀ s : ℂ, 0 < s.re → localIdelicZetaIntegral (finiteLocalMultiplicativeTamagawaMeasure F u.val)
        (fun x ↦ g (Multiplicative.ofAdd x)) (sLocalFiniteRestriction u (gchart(χ) s)) = C / d u s := by
    by_cases hv : u = v₉
    · subst u
      obtain ⟨g, C, hC, hg⟩ := exists_sLocalFinite_unramified_zeta_test χ v₉ p₉ hp₉ hu₉
      exact ⟨g, C, hC, fun s hz ↦ by simpa [d, P, hne.symm, hχ₉, hq₉] using hg s hz⟩
    by_cases hv' : u = v₅
    · subst u
      obtain ⟨g, C, hC, hg⟩ := exists_sLocalFinite_unramified_zeta_test χ v₅ p₅ hp₅ hu₅
      exact ⟨g, C, hC, fun s hz ↦ by simpa [d, gaussianSecondaryFactor, hne, hχ₅, hq₅] using hg s hz⟩
    obtain ⟨g, C, hC, hg⟩ := exists_sLocalFinite_constant_zeta_test χ u
    exact ⟨g, C, hC, fun s _ ↦ by simpa [d, hv, hv'] using hg s⟩
  choose b C hC hb using hfin
  obtain ⟨a₀, ha₀⟩ := gaussianArchLocal_realization χ w hw harch hh hs
  let a (u : InfinitePlace F) : SchwartzBruhat (Multiplicative u.Completion) := (huniq u).symm ▸ a₀
  have ha (s : ℂ) : (∏ u : InfinitePlace F, localIdelicZetaIntegral
      (infiniteLocalMultiplicativeTamagawaMeasure F u) (fun x ↦ a u (Multiplicative.ofAdd x))
      (sLocalInfiniteRestriction u (gchart(χ) s))) = (2 * (Real.pi : ℂ)) * bilateralLaplace h s := by
    let : Subsingleton (InfinitePlace F) := ⟨fun i j ↦ (huniq i).trans (huniq j).symm⟩
    rw [Fintype.prod_subsingleton _ w]
    exact ha₀ s
  obtain ⟨f, hf⟩ := gaussianArchFinTensor a b
  let c := (2 * (Real.pi : ℂ)) * ∏ u, C u
  have hcn : c ≠ 0 := mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    (Finset.prod_ne_zero_iff.mpr fun u _ ↦ hC u)
  refine ⟨c⁻¹ • f, fun r hr ↦ ?_⟩
  obtain ⟨Z, hZ⟩ := sLocalIdelicZetaIntegral_tempered (gchart(χ) (r : ℂ)) ⟨χ, r, hr, rfl⟩
  rw [← hZ, map_smul, hZ, smul_eq_mul, sLocalIdelicZetaIntegral_pureTensor _ ⟨χ, r, hr, rfl⟩ f a b hf, ha]
  simp_rw [hb _ (r : ℂ) hr]
  rw [Finset.prod_div_distrib]
  have hprod : (∏ u, d u (r : ℂ)) = P r * gaussianSecondaryFactor r := by
    simp only [d, Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  rw [hprod]
  change c⁻¹ * _ = bilateralLaplace h r / (P r * gaussianSecondaryFactor r)
  rw [show (2 * (Real.pi : ℂ) * bilateralLaplace h r) * ((∏ u, C u) / (P r * gaussianSecondaryFactor r)) =
    c * (bilateralLaplace h r / (P r * gaussianSecondaryFactor r)) by dsimp [c]; ring,
    ← mul_assoc, inv_mul_cancel₀ hcn, one_mul]

end GaussianCharacter

section

open IsDedekindDomain NumberField
open scoped NNReal

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}
local notation "Jₛ" => SIdeleQuotient F S
local notation "Test" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "χs(" χ ", " z ")" => quasiCharacterNormTwist (G := Jₛ) (sIdeleQuotientNorm F S)
  (isProperMap_sIdeleQuotientNorm F S).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ) z


private theorem gaussian_realizes_weighted_residues (χ : PontryaginDual Jₛ)
    (hχ : HasGaussianTwoPlaceProfile χ) (t : ℝ) {h : ℝ → ℂ} (hh : ContDiff ℝ ∞ h)
    (hsupp : support h ⊆ Icc 0 (2 * Real.log 9)) :
    ∃ f : Test, ∀ a : ℂ, complexResidue (fun z ↦ (t : ℂ) ^ (-z) * sLocalIdelicZFunction f (χs(χ,z))) a =
      complexResidue (fun z ↦ (t : ℂ) ^ (-z) * gaussianTwoFactorZeta h z) a := by
  obtain ⟨f, hf⟩ := gaussianTwoFactorZeta_realized_of_character χ hχ hh hsupp
  have hc := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsupp
  refine ⟨f, fun a ↦ ?_⟩
  have hg : (fun z ↦ sLocalIdelicZFunction f (χs(χ,z))) =ᶠ[𝓝[≠] a] gaussianTwoFactorZeta h := by
    apply gaussianResidue_identity (fun z ↦ (sLocalIdelicZFunction_meromorphic f χ).meromorphicOn z trivial)
      (gaussianTwoFactorZeta_meromorphic hh.continuous hc)
    exact fun r hr ↦ (sLocalIdelicZFunction_eq_integral f ⟨χ, r, hr, rfl⟩).trans (hf r hr)
  exact gaussianResidue_congr ((Filter.EventuallyEq.rfl (f := fun z : ℂ ↦ (t : ℂ) ^ (-z))).mul hg)

open Classical in
/-- Paper: Equation (8.4.0.2), p. 389. For a character with the Gaussian local data,
absolute summability of the separate norm-nine residues for all actual S-adelic tests at
one norm implies the polynomial lower bound at every noncolliding integer.
A finite number of indices can be omitted from the convergence hypothesis. -/
theorem gaussian_polyLowerBound_of_sLocal_absoluteResidues
    (χ : PontryaginDual Jₛ) (hχ : HasGaussianTwoPlaceProfile χ) {t : ℝ} (ht : 0 < t) (excluded : Finset ℤ)
    (habs : ∀ f : Test, Summable (fun m : ℤ ↦
      if m ∈ excluded ∨ gaussianSecondaryFactor (gaussianPrimaryCenter m) = 0 then 0 else
        ‖complexResidue (fun z ↦ (t : ℂ) ^ (-z) * sLocalIdelicZFunction f (χs(χ,z)))
          (gaussianPrimaryCenter m)‖)) :
    ∃ (c : ℝ) (d : ℕ), 0 < c ∧ ∀ m : ℤ, gaussianSecondaryFactor (gaussianPrimaryCenter m) ≠ 0 →
      c / (1 + |(m : ℝ)|) ^ d ≤ ‖gaussianSecondaryFactor (gaussianPrimaryCenter m)‖ := by
  apply gaussianTwoFactorZeta_polyLowerBound_of_absoluteResidues ht excluded
  intro h hh hsupp
  obtain ⟨f, hf⟩ := gaussian_realizes_weighted_residues χ hχ t hh hsupp
  simpa only [hf] using habs f

open Classical in
/-- Paper: Theorem 7.1.2.3, pp. 318, 322–323. For the genuine S-local transform,
even upper bounds on the real parts of the symmetric norm-nine residue sums force the
polynomial lower bound. Failure of the latter gives one adelic test with unbounded
real parts of the symmetric sums, for the chosen norm and finite exceptional set. -/
theorem gaussian_polyLowerBound_of_sLocal_bounded_symmetricResidues
    (χ : PontryaginDual Jₛ) (hχ : HasGaussianTwoPlaceProfile χ) {t : ℝ} (ht : 0 < t) (excluded : Finset ℤ)
    (hbdd : ∀ f : Test, ∃ A : ℝ, ∀ N : ℕ, (∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      if m ∈ excluded ∨ gaussianSecondaryFactor (gaussianPrimaryCenter m) = 0 then 0 else
        complexResidue (fun z ↦ (t : ℂ) ^ (-z) * sLocalIdelicZFunction f (χs(χ,z)))
          (gaussianPrimaryCenter m)).re ≤ A) :
    ∃ (c : ℝ) (d : ℕ), 0 < c ∧ ∀ m : ℤ, gaussianSecondaryFactor (gaussianPrimaryCenter m) ≠ 0 →
      c / (1 + |(m : ℝ)|) ^ d ≤ ‖gaussianSecondaryFactor (gaussianPrimaryCenter m)‖ := by
  apply gaussianTwoFactorZeta_polyLowerBound_of_bounded_symmetricResidues ht excluded
  intro h hh hsupp
  obtain ⟨f, hf⟩ := gaussian_realizes_weighted_residues χ hχ t hh hsupp
  simpa only [hf] using hbdd f

end

end RiemannMasullo.Isolated
