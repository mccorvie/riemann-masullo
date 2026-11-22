module

public import RiemannMasullo.Ch12_TraceGeometric.Sec4

/-! # The printed Fourier cutoff range in §12.4 -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField Set
open scoped ContDiff NumberField.AdeleRing

namespace RiemannMasullo

/-- Paper: Theorem 12.4.1.1, Step II and (12.4.1.8), pp. 516–517.
As printed: Fourier transformation, multiplication by the smoothed product-norm ball, and
inverse Fourier transformation send every additive S-adelic Schwartz–Bruhat test to another
such test.
Deviation: Footnote 2 on p. 514 requests a one-sided extension of Definition 9.3.3.1.
Keep its parameter bounds and upper transition. For the ball in Step II, take the
profile to be one from zero through L − ε and zero from L onwards.
See `sLocalTraceFourierCutoff` and ERRATA F246. -/
def Printed.sLocalTraceFourierCutoff_preservesSchwartzBruhat : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))),
    Subsingleton (CommRing.Pic ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)) →
    (∀ v ∉ S, v.asIdeal.ramificationIdx (𝓞 ℚ) = 1) →
    ∀ (L ε : ℝ), 1 < L → 0 < ε → ε < L⁻¹ →
    ∀ (ρ : ℝ → ℝ), ContDiff ℝ (∞ : ℕ∞ω) ρ → (∀ t, 0 ≤ ρ t ∧ ρ t ≤ 1) →
      EqOn ρ 1 (Icc 0 (L - ε)) → (∀ t ≥ L, ρ t = 0) →
      ∀ f : SchwartzBruhat (Multiplicative (SAdeleRing F S)),
        let symbol := fun u : SAdeleRing F S ↦
          (ρ ((∏ w : InfinitePlace F, ‖u.1 w‖ ^ w.mult) * ∏ v : S, ‖u.2 v‖) : ℂ)
        (fun x : Multiplicative (SAdeleRing F S) ↦ sLocalTraceFourierCutoff symbol f x.toAdd) ∈
          schwartzBruhatSubmodule (G := Multiplicative (SAdeleRing F S))

/-- Paper: Theorem 12.4.1.1, Step II and (12.4.1.8), pp. 516–517.
Take `F = ℚ`, `S = {∞, 2}`, `L = 2` and `ε = 1/4`. For `β(t) = exp(−1/t)` at `t > 0`
and zero elsewhere, use `ρ(t) = β(2−t)/(β(2−t)+β(t−7/4))`. Take the test `b'' ⊗ 1_{ℤ₂ˣ}`,
where `b(x) = exp(−1/((x−1)(2−x)))` on `(1,2)` and zero elsewhere. The test vanishes
near either coordinate origin and has integral zero. Its Fourier transform has a nonzero
entire real factor and a finite factor equal to `1/2` on `ℤ₂`.
For any proposed period subgroup `2ᴺ ℤ₂`, choose `k ≥ max(N,0)` and compare the
frequencies `2ᵏ` and `2ᵏ⁺²`. For real frequencies near `3 · 2ᵏ`, the two product norms
lie on opposite plateaux, and the real Fourier factor is nonzero somewhere in that interval.
The multiplied transform has no common finite-place period. It is continuous and integrable,
so if its inverse transform were Schwartz–Bruhat, Fourier inversion would recover it pointwise
as a Schwartz–Bruhat transform. -/
theorem Printed.sLocalTraceFourierCutoff_preservesSchwartzBruhat_false :
    ¬ Printed.sLocalTraceFourierCutoff_preservesSchwartzBruhat := by sorry

end RiemannMasullo
