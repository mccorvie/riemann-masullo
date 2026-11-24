module

public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec1a

/-! # The separate place sums in the theta expansion of §7.1.2 -/

@[expose] public noncomputable section

open Filter IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped BigOperators NNReal Asymptotics

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F] {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Jₛ" => SIdeleQuotient F S
local notation "Tests" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "normₛ" => sIdeleQuotientNorm F S
set_option quotPrecheck false in
local notation "chart(" χ ")" => quasiCharacterNormTwist (G := Jₛ) normₛ
  (isProperMap_sIdeleQuotientNorm F S).continuous
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp χ)
local notation "Places" => InfinitePlace F ⊕ S

local instance isolatedCh07Sec1aNormOneMeasurableSpace : MeasurableSpace (normₛ).ker := borel _
local instance isolatedCh07Sec1aNormOneHaar : (sLocalNormOneQuotientMeasure F S).IsHaarMeasure :=
  (sLocalNormOneQuotientMeasure_normProduct (F := F) (S := S)).1

open Classical in
/-- Paper: Theorem 7.1.2.3, p. 318. At each place the crossed residues have a separate
sum. For each test this sum converges uniformly on compact subsets of the idele quotient.
For each fixed idele of norm less than one it converges uniformly on bounded sets of
Schwartz–Bruhat tests. The sum over the places gives homogeneous theta with the remainder
of pp. 322–323, including a single remainder constant on each bounded set.
Deviation: The line at `-A` avoids poles of the correcting factor (F90). The open strip
up to real part one includes zero and the actual archimedean abscissae (F87). In the
residue of `r⁻ˢ Z(s)` at `a`, the term of log degree `j` is
`r⁻ᵃ * sLocalZLaurentCoeff f (chart a) (-j-1) * (-log r)ʲ / j!` for
`j < sLocalPolarMultiplicity f (chart a)` (F89, I211). The character contributes its conjugate.
Reconstruction: To count a shared pole once (F88), take its first contributing place in
one fixed enumeration, independent of the test and the summation bounds. At an unramified
finite place the open height interval cuts out the consecutive integers in its shifted
pole lattice (Lemma 7.1.2.2), subject to this removal of duplicates. The two ends of the
ordinary bilateral series tend separately to infinity. The finite outer sum runs directly
over the places, suppressing the grouping by residue characteristic.
Gap: The contour estimate controls only the joint sum. Separate convergence may fail for
some characters. For the angular character in the ℚ(i) example of #7279 even absolute
convergence at the place over 3 for the indicated tests requires an open Diophantine bound.
Nothing in the Lean uses this statement, and it is not known how it connects with the rest
of the proof in Lean; in the paper it is used on pp. 325–326, 333, 349–350, 381, 389–390. -/
theorem sLocalHomogeneousAdelicTheta_separatePlaceExpansion (χ : PontryaginDual Jₛ)
    (A : ℝ) (hA : 0 < A)
    (hline : ∀ a : ℂ, a.re = -A →
      0 ≤ meromorphicOrderAt (fun z ↦ sLocalRhoFactor (chart(χ) z)) a) :
    let Z (f : Tests) (z : ℂ) := sLocalIdelicZFunction f (chart(χ) z)
    let r (g : Jₛ) : ℝ := (normₛ g).val
    let ω := χ.comp (⟨(normₛ).ker.subtype, continuous_subtype_val⟩ : (normₛ).ker →ₜ* Jₛ)
    let θ := sLocalHomogeneousAdelicTheta F S (sLocalNormOneQuotientMeasure F S) ω
    let contributes : Places → ℂ → Prop := Sum.elim
      (fun w a ↦ meromorphicOrderAt
        (fun z ↦ infiniteLocalTateFactor w (sLocalInfiniteRestriction w (chart(χ) z))) a < 0)
      (fun v a ↦
        let period := 2 * Real.pi / Real.log (v.val.asIdeal.absNorm : ℝ)
        ∃ (m : ℤ) (t : ℝ), t ∈ Ico 0 period ∧
          (∀ x : (v.val.adicCompletion F)ˣ, sLocalFiniteRestriction v (chart(χ) 0) x =
            (‖(x : v.val.adicCompletion F)‖ : ℂ) ^ ((t : ℂ) * Complex.I)) ∧
          a = (((m : ℝ) * period - t : ℝ) : ℂ) * Complex.I)
    let places := (Finset.univ : Finset Places).toList
    let place (a : ℂ) := (places.find? (fun v ↦ contributes v a)).getD
      (Sum.inl (Classical.arbitrary (InfinitePlace F)))
    let poles (h : ℝ × ℝ) := (finite_rectanglePoles
      (f := fun z ↦ sLocalRhoFactor (chart(χ) z)) (a := -A - 1) (b := 2)
      (σ₁ := -A) (σ₂ := 1) (t₁ := h.1) (t₂ := h.2)
      (sLocalRhoFactor_meromorphic χ).meromorphicOn (by linarith) (by norm_num)).toFinset
    let partialSum (v : Places) (h : ℝ × ℝ) (f : Tests) (g : Jₛ) :=
      ∑ a ∈ (poles h).filter (place · = v),
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
        ∀ f ∈ B, ∀ g, r g < 1 → ‖θ f g - ∑ v, L v f g‖ ≤ C * r g ^ A) := by
  sorry

open Classical in
/-- Paper: Theorem 7.1.2.3, p. 322. When the separate place sums converge, summing their
limits gives the limit of the sums of distinct poles at any common pair of escaping heights.
Deviation: This finite-partition argument applies to any residue weights and pole windows. -/
theorem tendsto_jointPoleSum_of_separatePlaceLimits {ι : Type*} [Fintype ι]
    (poles : ℝ × ℝ → Finset ℂ) (place : ℂ → ι) (term : ℂ → ℂ) (L : ι → ℂ)
    (hL : ∀ v, Tendsto (fun h ↦ ∑ a ∈ (poles h).filter (place · = v), term a)
      (atBot ×ˢ atTop) (𝓝 (L v))) {lo hi : ℕ → ℝ}
    (hlo : Tendsto lo atTop atBot) (hhi : Tendsto hi atTop atTop) :
    Tendsto (fun n ↦ ∑ a ∈ poles (lo n, hi n), term a) atTop (𝓝 (∑ v, L v)) := by
  have h := tendsto_finsetSum Finset.univ
    (fun v _ ↦ (hL v).comp (hlo.prodMk hhi))
  exact h.congr fun n ↦ Finset.sum_fiberwise (poles (lo n, hi n)) place term

open Classical in
/-- Paper: Theorem B.3.2.1, p. 606. For the contour shift used on p. 322, if the separate
residue sums converge then their sum equals the normalized difference of vertical integrals.
Deviation: Uses the signed heights and boundary hypotheses of `tendsto_rectangleResidueSum`.
The assignment of poles to a finite set of places only serves to partition each rectangle. -/
theorem sum_separatePlaceLimits_eq_verticalLineIntegral_sub {ι : Type*} [Fintype ι]
    {f Φ : ℂ → ℂ} {a b a' b' σ₁ σ₂ : ℝ} {T : ℤ → ℝ}
    (hT : WitnessesSlowGrowthNearPoles f a b T) (ha : a' < a) (hb : b < b')
    (hΦ : UniformlySchwartzOnStrip Φ a' b') (hσ₁ : a < σ₁) (hσ : σ₁ < σ₂) (hσ₂ : σ₂ < b)
    (hSides : ∀ σ ∈ ({σ₁, σ₂} : Set ℝ),
      let trace := fun y : ℝ ↦ f ((σ : ℂ) + y * Complex.I)
      Continuous trace ∧ ∃ γ > (0 : ℝ), trace =O[comap abs atTop] (fun y : ℝ ↦ |y| ^ γ))
    (hHeights : ∀ k : ℕ, 0 < k → T (-(k : ℤ)) < 0 ∧ 0 < T (k : ℤ))
    (place : ℂ → ι) (L : ι → ℂ)
    (hL : ∀ v, Tendsto (fun h : ℝ × ℝ ↦ ∑ z ∈
      (finite_rectanglePoles (t₁ := h.1) (t₂ := h.2) hT.2.1 hσ₁ hσ₂).toFinset.filter
        (place · = v), complexResidue (fun s ↦ Φ s * f s) z) (atBot ×ˢ atTop) (𝓝 (L v))) :
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
  exact tendsto_nhds_unique (tendsto_jointPoleSum_of_separatePlaceLimits _ place _ L hL hLo hHi)
    (tendsto_rectangleResidueSum hT ha hb hΦ hσ₁ hσ hσ₂ hSides hHeights)

end RiemannMasullo
