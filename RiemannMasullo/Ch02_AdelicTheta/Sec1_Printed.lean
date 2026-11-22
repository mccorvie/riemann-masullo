module

public import RiemannMasullo.Ch02_AdelicTheta.Sec1
import all RiemannMasullo.Ch02_AdelicTheta.Sec1
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

/-! # Chapter 2.1: the printed Schwartz–Bruhat decomposition -/

@[expose] public noncomputable section

namespace RiemannMasullo

open Filter NumberField IsDedekindDomain
open scoped NumberField.AdeleRing IsDedekindDomain.FiniteAdeleRing

local notation "Places(" F ")" => HeightOneSpectrum (𝓞 F)
local notation "ℬ(" R ")" => SchwartzBruhat (Multiplicative R)

/-- Paper: Lemma 2.1.3.2(3), p. 68. As printed: every adelic Schwartz–Bruhat function
is a nonempty finite linear combination of products of archimedean Schwartz functions
and finite adelic rectangle indicators whose factors are compact additive subgroups,
equal to the local integer ring at almost every finite place.
`adeleSchwartz_eq_sum_compactOpen_rectangles` uses compact open sets. See ERRATA F11. -/
def Printed.adeleSchwartz_eq_sum_compactSubgroup_rectangles : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (f : ℬ(𝔸[F])),
    ∃ (r : ℕ) (c : Fin r → ℂ) (arch : Fin r → ℬ(InfiniteAdeleRing F))
      (K : Fin r → (v : Places(F)) → AddSubgroup (v.adicCompletion F))
      (φ : Fin r → ℬ(𝔸[F])),
      1 ≤ r ∧
      (∀ i, (∀ v, IsCompact (K i v : Set (v.adicCompletion F))) ∧
        (∀ᶠ v in cofinite,
          (K i v : Set (v.adicCompletion F)) = (v.adicCompletionIntegers F : Set _)) ∧
        ∀ x : 𝔸[F], φ i (Multiplicative.ofAdd x) =
          arch i (Multiplicative.ofAdd x.1) *
            Set.indicator {y : 𝔸ᶠ[F] | ∀ v, y v ∈ K i v} (fun _ ↦ (1 : ℂ)) x.2) ∧
      f = ∑ i, c i • φ i

/-- Paper: Lemma 2.1.3.2(3), p. 68. Over ℚ use the real Gaussian, the indicator of
`1 + 3ℤ₃` at 3 and the indicators of ℤₚ at every other prime. This is Schwartz–Bruhat.
At the adelic point with real coordinate 0, 3-adic coordinate 1 and other finite
coordinates 0 it has value 1. Changing the 3-adic coordinate to −1 gives value 0.
Every product allowed in the printed decomposition is invariant under this change,
because an additive subgroup is invariant under negation. -/
theorem Printed.adeleSchwartz_eq_sum_compactSubgroup_rectangles_false :
    ¬ Printed.adeleSchwartz_eq_sum_compactSubgroup_rectangles := by
  classical
  intro h
  let v : Places(ℚ) := Rat.HeightOneSpectrum.primesEquiv.symm ⟨3, Nat.prime_three⟩
  let t : 𝔸ᶠ[ℚ] := RestrictedProduct.single (fun w : Places(ℚ) ↦ w.adicCompletionIntegers ℚ) v 1
  let x : Multiplicative 𝔸[ℚ] := .ofAdd (0, t)
  let y : Multiplicative 𝔸[ℚ] := .ofAdd (0, -t)
  have hxy : x ≠ y := by
    intro he
    have hv := congrArg (fun z : Multiplicative 𝔸[ℚ] ↦ z.toAdd.2 v) he
    change t v = -(t v) at hv
    rw [show t v = 1 from RestrictedProduct.single_eq_same _ _ _] at hv
    let : CharZero (v.adicCompletion ℚ) :=
      charZero_of_injective_algebraMap (algebraMap ℚ (v.adicCompletion ℚ)).injective
    norm_num at hv
  let : LocallyCompactSpace (Multiplicative 𝔸[ℚ]) := adeleGroupLocallyCompact ℚ
  let : T2Space (Multiplicative 𝔸[ℚ]) := adeleGroupT2 ℚ
  -- A test supported in the complement of y can be nonzero at x.
  obtain ⟨δ, hδ_apply, _, hδ⟩ := schwartzBruhat_dirac_support x
  have htest : ∃ f : ℬ(𝔸[ℚ]), tsupport f.val ⊆ {y}ᶜ ∧ δ f ≠ 0 := by
    have hx : x ∈ schwartzBruhatDistributionSupport δ := hδ.symm ▸ Set.mem_singleton x
    by_contra! hkill
    exact hx ⟨{y}ᶜ, ⟨isOpen_compl_singleton, hkill⟩, hxy⟩
  obtain ⟨f, hs, hn⟩ := htest
  have hy : f y = 0 := image_eq_zero_of_notMem_tsupport (fun h ↦ hs h rfl)
  obtain ⟨r, c, arch, K, φ, _, hφ, hf⟩ := h ℚ f
  have heven (i : Fin r) : φ i x = φ i y := by
    have hmem : (∀ w, (-t) w ∈ K i w) ↔ ∀ w, t w ∈ K i w := by
      change (∀ w, -(t w) ∈ K i w) ↔ _
      simp only [AddSubgroup.neg_mem_iff]
    refine ((hφ i).2.2 (0, t)).trans (Eq.trans ?_ ((hφ i).2.2 (0, -t)).symm)
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hmem]
  have hev (z : Multiplicative 𝔸[ℚ]) : f z = ∑ i, c i * φ i z :=
    (congrArg (fun g : ℬ(𝔸[ℚ]) ↦ g z) hf).trans (schwartzBruhat_eval_sum c φ z)
  apply hn
  calc
    δ f = f x := hδ_apply f
    _ = f y := by
      rw [hev x, hev y]
      exact Finset.sum_congr rfl fun i _ ↦ congrArg (c i * ·) (heven i)
    _ = 0 := hy

end RiemannMasullo
