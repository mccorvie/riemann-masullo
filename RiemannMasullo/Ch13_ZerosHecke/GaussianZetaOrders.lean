module

public import RiemannMasullo.Ch13_ZerosHecke.Targets

/-!
# Orders of a Dedekind zeta function with a quadratic Dirichlet factorization

The Gaussian Dedekind zeta function factors as Riemann zeta times the Dirichlet
L-function of the quadratic character modulo four. This module gives the analytic
consequence of an ordinary factorization on the half-plane of absolute convergence
for any number field and Dirichlet character. In the positive half-plane the divisor
of the continued completed trivial Hecke L-function is the sum of the two ordinary
divisors. Away from the possible pole at one, its positive support is their zero
set union, including common zeros with their full multiplicities.
-/

public noncomputable section

open NumberField Set

namespace RiemannMasullo

local notation "U[" K "]" => PontryaginDual (IdeleClassGroup (𝓞 K) K)

private theorem gaussianZetaOrders_analyticAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ χ.LFunction s := by
  have h : DifferentiableOn ℂ χ.LFunction {1}ᶜ := fun z hz ↦
    (χ.differentiableAt_LFunction z (.inl hz)).differentiableWithinAt
  exact h.analyticAt (isOpen_compl_singleton.mem_nhds hs)

private theorem gaussianZetaOrders_ne_top {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) : meromorphicOrderAt χ.LFunction s ≠ ⊤ := by
  apply (meromorphic_dirichletLFunction χ).meromorphicOrderAt_ne_top_of_isPreconnected
    isPreconnected_univ (mem_univ (2 : ℂ)) (mem_univ s)
  have h₂ := gaussianZetaOrders_analyticAt χ (by norm_num : (2 : ℂ) ≠ 1)
  rw [h₂.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
    (χ.LFunction_ne_zero_of_one_le_re (.inr (by norm_num)) (by norm_num))]
  exact WithTop.zero_ne_top

private theorem gaussianZetaOrders_factorDivisor {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : s ≠ 1) :
    0 ≤ MeromorphicOn.divisor χ.LFunction univ s ∧
      (0 < MeromorphicOn.divisor χ.LFunction univ s ↔ χ.LFunction s = 0) := by
  have ha := gaussianZetaOrders_analyticAt χ hs
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp (gaussianZetaOrders_ne_top χ s)
  have hn : 0 ≤ (m : WithTop ℤ) := hm.symm ▸ ha.meromorphicOrderAt_nonneg
  have hz := ha.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff
  rw [← hm, ← WithTop.coe_zero, WithTop.coe_inj] at hz
  rw [MeromorphicOn.divisor_apply (meromorphic_dirichletLFunction χ) (mem_univ s),
    ← hm, WithTop.untop₀_coe]
  have hm₀ : 0 ≤ m := WithTop.coe_le_coe.mp hn
  refine ⟨hm₀, ?_⟩
  exact ⟨fun h ↦ not_ne_iff.mp (fun hne ↦ h.ne' (hz.mpr hne)),
    fun h ↦ lt_of_le_of_ne hm₀ (fun he ↦ (hz.mp he.symm) h)⟩

/-- A factorization on the half-plane of absolute convergence determines the full
integer divisor of the completed trivial Hecke L-function throughout the positive
half-plane. Common zeros of the two factors contribute the sum of their orders. -/
theorem trivialHeckeDivisor_eq_zeta_add_dirichlet_of_dedekindZeta_eq_mul
    (K : Type*) [Field K] [NumberField K] {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprod : ∀ z : ℂ, 1 < z.re → dedekindZeta K z = riemannZeta z * χ.LFunction z)
    {s : ℂ} (hs : 0 < s.re) :
    MeromorphicOn.divisor (continuedCompletedHeckeL (1 : U[K])) univ s =
      MeromorphicOn.divisor riemannZeta univ s + MeromorphicOn.divisor χ.LFunction univ s := by
  have hζ : MeromorphicOn riemannZeta univ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      meromorphic_dirichletLFunction (1 : DirichletCharacter ℂ 1)
  have hχ := meromorphic_dirichletLFunction χ
  have hζfin : meromorphicOrderAt riemannZeta s ≠ ⊤ := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      gaussianZetaOrders_ne_top (1 : DirichletCharacter ℂ 1) s
  have heq := meromorphicOrderAt_finiteHeckeL_continuation (1 : U[K]) (hζ.mul hχ)
    (fun z ↦ (hprod z.val z.property).symm.trans (finiteHeckeL_one_eq_dedekindZeta z).symm) hs
  rw [MeromorphicOn.divisor_apply (continuedCompletedHeckeL_spec (1 : U[K])).1.meromorphicOn
      (mem_univ s), ← heq, meromorphicOrderAt_mul (hζ s (mem_univ s)) (hχ s (mem_univ s)),
    WithTop.untop₀_add hζfin (gaussianZetaOrders_ne_top χ s),
    MeromorphicOn.divisor_apply hζ (mem_univ s), MeromorphicOn.divisor_apply hχ (mem_univ s)]

/-- At positive real part away from one, the trivial character contributes a
positive completed divisor exactly at the ordinary zeros of either factor. -/
theorem trivialHeckeDivisor_pos_iff_of_dedekindZeta_eq_mul
    (K : Type*) [Field K] [NumberField K] {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprod : ∀ z : ℂ, 1 < z.re → dedekindZeta K z = riemannZeta z * χ.LFunction z)
    {s : ℂ} (hs : 0 < s.re) (h₁ : s ≠ 1) :
    0 < MeromorphicOn.divisor (continuedCompletedHeckeL (1 : U[K])) univ s ↔
      riemannZeta s = 0 ∨ χ.LFunction s = 0 := by
  have hζ : 0 ≤ MeromorphicOn.divisor riemannZeta univ s ∧
      (0 < MeromorphicOn.divisor riemannZeta univ s ↔ riemannZeta s = 0) := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using
      gaussianZetaOrders_factorDivisor (1 : DirichletCharacter ℂ 1) h₁
  have hχ := gaussianZetaOrders_factorDivisor χ h₁
  rw [trivialHeckeDivisor_eq_zeta_add_dirichlet_of_dedekindZeta_eq_mul K χ hprod hs,
    ← hζ.2, ← hχ.2]
  omega

private theorem gaussianZetaOrders_strip {K : Type*} [Field K] [NumberField K]
    (ψ : U[K]) {s : ℂ} (hs : 0 < MeromorphicOn.divisor (continuedCompletedHeckeL ψ) univ s) :
    0 < s.re ∧ s.re < 1 := by
  have hL := continuedCompletedHeckeL_spec ψ
  have hI := continuedCompletedHeckeL_spec ψ⁻¹
  have hright (η : U[K]) {z : ℂ} (hz : 0 < meromorphicOrderAt (continuedCompletedHeckeL η) z) :
      z.re < 1 := by
    obtain h | h := le_or_gt z.re 0
    · exact h.trans_lt zero_lt_one
    · exact completedHeckeL_continuation_zeros η _ (continuedCompletedHeckeL_spec η).1
        (continuedCompletedHeckeL_spec η).2 h hz
  rw [MeromorphicOn.divisor_apply hL.1.meromorphicOn (mem_univ s)] at hs
  have hp : 0 < meromorphicOrderAt (continuedCompletedHeckeL ψ) s := by
    cases h : meromorphicOrderAt (continuedCompletedHeckeL ψ) s with
    | top => simp
    | coe m =>
      rw [h, WithTop.untop₀_coe] at hs
      exact_mod_cast hs
  obtain ⟨ε, hε, hε₀, hfe⟩ :=
    completedHeckeL_continuation_functionalEquation ψ _ _ hL.1 hL.2 hI.1 hI.2
  have hr := meromorphicOrderAt_comp_of_deriv_ne_zero (f := continuedCompletedHeckeL ψ⁻¹)
    (show AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) s by fun_prop)
    (show deriv (fun z : ℂ ↦ 1 - z) s ≠ 0 by simp)
  rw [show (continuedCompletedHeckeL ψ⁻¹ ∘ fun z ↦ 1 - z) = ε * continuedCompletedHeckeL ψ
    from funext hfe, meromorphicOrderAt_mul_of_ne_zero (hε.analyticAt s) (hε₀ s)] at hr
  have href := hright ψ⁻¹ (hr ▸ hp)
  rw [Complex.sub_re, Complex.one_re] at href
  exact ⟨by linarith, hright ψ hp⟩

/-- Paper: Theorem 12.5.1.1, pp. 519–520. Deviation: for a Dedekind zeta
factorization, the exterior zero set on the trivial character is the union of the two ordinary
zero sets in the open critical strip with the same inclusive boundary. -/
theorem trivialHeckeExterior_eq_of_dedekindZeta_eq_mul
    (K : Type*) [Field K] [NumberField K] {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprod : ∀ z : ℂ, 1 < z.re → dedekindZeta K z = riemannZeta z * χ.LFunction z)
    (α : ℝ) :
    {s : ℂ | 0 < MeromorphicOn.divisor (continuedCompletedHeckeL (1 : U[K])) univ s ∧
      α ≤ |s.re - 1 / 2|} =
    {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ α ≤ |s.re - 1 / 2| ∧
      (riemannZeta s = 0 ∨ χ.LFunction s = 0)} := by
  ext s
  constructor
  · rintro ⟨h, hα⟩
    obtain ⟨h₀, h₁⟩ := gaussianZetaOrders_strip (1 : U[K]) h
    have hne : s ≠ 1 := fun e ↦ by simp [e] at h₁
    exact ⟨h₀, h₁, hα, (trivialHeckeDivisor_pos_iff_of_dedekindZeta_eq_mul K χ hprod h₀ hne).mp h⟩
  · rintro ⟨h₀, h₁, hα, h⟩
    have hne : s ≠ 1 := fun e ↦ by simp [e] at h₁
    exact ⟨(trivialHeckeDivisor_pos_iff_of_dedekindZeta_eq_mul K χ hprod h₀ hne).mpr h, hα⟩

/-- For any complex weight whose two ordinary exterior zero sums converge, the
corresponding sum on the trivial Hecke character converges to their sum.
A shared zero contributes the multiplicity of each factor. -/
theorem hasSum_trivialHeckeExterior_of_dedekindZeta_eq_mul
    (K : Type*) [Field K] [NumberField K] {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hprod : ∀ z : ℂ, 1 < z.re → dedekindZeta K z = riemannZeta z * χ.LFunction z)
    (α : ℝ) (w : ℂ → ℂ) (a b : ℂ)
    (hζ : HasSum (fun z : {s : ℂ // (0 < s.re ∧ s.re < 1 ∧ α ≤ |s.re - 1 / 2|) ∧
      riemannZeta s = 0} ↦ (MeromorphicOn.divisor riemannZeta univ z.val : ℂ) * w z.val) a)
    (hχ : HasSum (fun z : {s : ℂ // (0 < s.re ∧ s.re < 1 ∧ α ≤ |s.re - 1 / 2|) ∧
      χ.LFunction s = 0} ↦ (MeromorphicOn.divisor χ.LFunction univ z.val : ℂ) * w z.val) b) :
    HasSum (fun z : {s : ℂ // 0 < MeromorphicOn.divisor (continuedCompletedHeckeL (1 : U[K]))
        univ s ∧ α ≤ |s.re - 1 / 2|} ↦
      (MeromorphicOn.divisor (continuedCompletedHeckeL (1 : U[K])) univ z.val : ℂ) * w z.val)
      (a + b) := by
  classical
  let L := continuedCompletedHeckeL (1 : U[K])
  let window : Set ℂ := {s | 0 < s.re ∧ s.re < 1 ∧ α ≤ |s.re - 1 / 2|}
  let zeros (f : ℂ → ℂ) : Set ℂ := {s | s ∈ window ∧ f s = 0}
  let E : Set ℂ := {s | 0 < MeromorphicOn.divisor L univ s ∧ α ≤ |s.re - 1 / 2|}
  let g (f : ℂ → ℂ) (s : ℂ) := (MeromorphicOn.divisor f univ s : ℂ) * w s
  have hζ' := (hasSum_subtype_iff_indicator (s := zeros riemannZeta) (f := g riemannZeta)).mp hζ
  have hχ' := (hasSum_subtype_iff_indicator (s := zeros χ.LFunction) (f := g χ.LFunction)).mp hχ
  apply (hasSum_subtype_iff_indicator (s := E) (f := g L)).mpr
  refine (hζ'.add hχ').congr_fun fun s ↦ ?_
  have hE : s ∈ E ↔ s ∈ window ∧ (riemannZeta s = 0 ∨ χ.LFunction s = 0) := by
    have he := Set.ext_iff.mp (trivialHeckeExterior_eq_of_dedekindZeta_eq_mul K χ hprod α) s
    simpa only [E, window, L, Set.mem_ofPred_eq, and_assoc] using he
  by_cases he : s ∈ E
  · have hw := (hE.mp he).1
    have hn : s ≠ 1 := fun h ↦ by have := hw.2.1; simp [h] at this
    have hind {n : ℕ} [NeZero n] (η : DirichletCharacter ℂ n) :
        (zeros η.LFunction).indicator (g η.LFunction) s = g η.LFunction s := by
      by_cases hz : η.LFunction s = 0
      · exact Set.indicator_of_mem (show s ∈ zeros η.LFunction from ⟨hw, hz⟩) _
      · obtain ⟨hm, hp⟩ := gaussianZetaOrders_factorDivisor η hn
        have h₀ : MeromorphicOn.divisor η.LFunction univ s = 0 :=
          le_antisymm (le_of_not_gt (fun h ↦ hz (hp.mp h))) hm
        rw [Set.indicator_of_notMem (show s ∉ zeros η.LFunction from fun h ↦ hz h.2)]
        simp [g, h₀]
    have hZ : (zeros riemannZeta).indicator (g riemannZeta) s = g riemannZeta s := by
      simpa only [DirichletCharacter.LFunction_modOne_eq] using hind (1 : DirichletCharacter ℂ 1)
    rw [Set.indicator_of_mem he, hZ, hind χ]
    simp only [g, L, trivialHeckeDivisor_eq_zeta_add_dirichlet_of_dedekindZeta_eq_mul K χ hprod
      hw.1, Int.cast_add, add_mul]
  · have hZ : s ∉ zeros riemannZeta := fun h ↦ he (hE.mpr ⟨h.1, Or.inl h.2⟩)
    have hD : s ∉ zeros χ.LFunction := fun h ↦ he (hE.mpr ⟨h.1, Or.inr h.2⟩)
    rw [Set.indicator_of_notMem he, Set.indicator_of_notMem hZ, Set.indicator_of_notMem hD, zero_add]

end RiemannMasullo
