module

public import RiemannMasullo.Ch02_AdelicTheta.Sec2a
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-! # Chapter 2.2: printed convergence and fractional ideal bounds -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter Function IsDedekindDomain NumberField Set
open scoped ENNReal NNReal NumberField.AdeleRing Pointwise nonZeroDivisors

/-- Paper: Proposition 2.2.1.3, p. 76. As printed: for every full lattice, every norm
inducing the Euclidean topology, and every compact set K, the sum of ‖ξ + x‖^(-σ)
over lattice points outside K is finite when x is in K and σ exceeds the dimension.
This is the pointwise convergence clause of (2.2.1.3), recorded at the
Proposition 2.2.1.3 TODO in `Sec2a.lean`. See ERRATA F207. -/
def Printed.latticeShiftedPowerSum_converges : Prop :=
  ∀ (N : ℕ), 1 ≤ N →
    ∀ (Γ : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology Γ] [IsZLattice ℝ Γ]
      (p : Seminorm ℝ (Fin N → ℝ)), (∀ x, p x = 0 → x = 0) →
      WithSeminorms (fun _ : Unit ↦ p) →
      ∀ (K : Set (Fin N → ℝ)), IsCompact K →
        ∀ (σ : ℝ), (N : ℝ) < σ → ∀ x ∈ K,
          (∑' ξ : ↥((Γ : Set (Fin N → ℝ)) \ K), (ENNReal.ofReal (p (ξ.val + x))) ^ (-σ)) < ⊤

/-- Paper: Proposition 2.2.1.3, p. 76. In dimension one, take the integer lattice,
the absolute value, K = {1}, x = 1 and σ = 2. The index ξ = −1 remains in the
sum and its extended nonnegative real term is 0^(-2) = ∞. -/
theorem Printed.latticeShiftedPowerSum_converges_false :
    ¬ Printed.latticeShiftedPowerSum_converges := by
  intro h
  let b := Pi.basisFun ℝ (Fin 1)
  let x₀ : Fin 1 → ℝ := fun _ ↦ 1
  have hx₀ : x₀ ∈ (Submodule.span ℤ (Set.range b) : Set (Fin 1 → ℝ)) :=
    Submodule.subset_span ⟨0, by funext i; fin_cases i; simp [b, x₀]⟩
  have hmem : -x₀ ∈ ((Submodule.span ℤ (Set.range b) : Set (Fin 1 → ℝ)) \ {x₀}) := by
    refine ⟨neg_mem hx₀, fun hc ↦ ?_⟩
    have := congrFun (Set.mem_singleton_iff.mp hc) 0
    simp [x₀] at this
    norm_num at this
  have hlt := h 1 le_rfl (Submodule.span ℤ (Set.range b)) (normSeminorm ℝ (Fin 1 → ℝ))
    (fun x hx ↦ norm_eq_zero.mp hx) (norm_withSeminorms ℝ (Fin 1 → ℝ)) {x₀}
    isCompact_singleton 2 (by norm_num) x₀ rfl
  refine hlt.ne (eq_top_iff.mpr ?_)
  have hterm : (ENNReal.ofReal (normSeminorm ℝ (Fin 1 → ℝ) ((-x₀) + x₀))) ^ (-(2 : ℝ)) = ⊤ := by
    rw [neg_add_cancel, map_zero, ENNReal.ofReal_zero]
    exact ENNReal.zero_rpow_of_neg (by norm_num)
  rw [← hterm]
  exact le_tsum (fun ξ : ↥((Submodule.span ℤ (Set.range b) : Set (Fin 1 → ℝ)) \ {x₀}) ↦
    (ENNReal.ofReal (normSeminorm ℝ (Fin 1 → ℝ) (ξ.val + x₀))) ^ (-(2 : ℝ))) ⟨_, hmem⟩

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "ℬ(" X ")" => SchwartzBruhat (Multiplicative X)

set_option maxSynthPendingDepth 3 in
/-- Paper: Lemma 2.2.2.1(3), p. 78. As printed: for each number field and each
Schwartz–Bruhat product (2.2.2.2), one fractional ideal bounds the sum (2.2.2.3)
for every idele whose archimedean projection belongs to T∞·E∞. Here T∞ is the
image of a chosen continuous homomorphic section of the archimedean norm and E∞
is the projection of the chosen norm-one fundamental domain. See
`adelicAverage_at_zero_le_fractionalIdeal` and ERRATA F208. -/
def Printed.adelicAverage_at_zero_le_fractionalIdeal : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : CommRing.Pic (𝓞 F) → (ideleNorm F).ker), r 1 = 1 →
    (∀ c, ideleIdealClass F (r c).val = c) →
    ∀ (τ : ℝ≥0ˣ →ₜ* (InfiniteAdeleRing F)ˣ), RightInverse τ (infiniteIdeleNorm F) →
      ∀ (f : ℬ(𝔸[F])) (arch : ℬ(InfiniteAdeleRing F))
        (K : (v : HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F)),
        (∀ v, IsCompact (K v) ∧ IsOpen (K v) ∧
          K v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
        (∀ᶠ v in cofinite, K v = (v.adicCompletionIntegers F : Set (v.adicCompletion F))) →
        (∀ x : 𝔸[F], f (Multiplicative.ofAdd x) = arch (Multiplicative.ofAdd x.1) *
          Set.indicator {y : 𝔸ᶠ[F] | ∀ v, y v ∈ K v} (fun _ ↦ (1 : ℂ)) x.2) →
        ∃ I : FractionalIdeal (𝓞 F)⁰ F,
          let atInfinity := Units.map (RingHom.fst (InfiniteAdeleRing F)
            (FiniteAdeleRing (𝓞 F) F)).toMonoidHom
          let archDomain := (atInfinity.comp (ideleNorm F).ker.subtype) ''
            ideleFundamentalDomain F b v₀ σ r
          ∀ (g : 𝕀[F]), atInfinity g ∈ range τ * archDomain →
            (∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖) ≤
              ∑' ξ : {ξ : Fˣ // (ξ : F) ∈ I},
                ‖arch (Multiplicative.ofAdd
                  (g.val.1 * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖

/-- Paper: Lemma 2.2.2.1(3), p. 78. Over ℚ take the positive real norm section,
the standard domain with archimedean projection {1}, Kᵥ = ℤᵥ at every prime, and
f∞(x) = exp(1 − x²). For any prime p and m ≥ 1 take g∞ = 1, gₚ = pᵐ and all
other components equal to 1. The left sum includes f∞(k/pᵐ) ≥ 1 for each integer
0 < |k| ≤ pᵐ. Both sides are convergent Gaussian lattice sums, and the right side
is fixed as m grows for each fractional ideal. -/
theorem Printed.adelicAverage_at_zero_le_fractionalIdeal_false :
    ¬ Printed.adelicAverage_at_zero_le_fractionalIdeal := by sorry

end RiemannMasullo
