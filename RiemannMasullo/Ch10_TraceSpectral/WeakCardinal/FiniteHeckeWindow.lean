module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.PhysicalWeakening
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.HeckeJetGram
public import RiemannMasullo.ForMathlib.Analysis.InnerProductSpace.DualRieszGram

/-! Finite ordinal windows for the actual width-zero Hecke quotient coordinates. -/

@[expose] public noncomputable section

open Filter Function MeasureTheory NumberField Set
open scoped InnerProductSpace NNReal NumberField.AdeleRing Matrix Topology

namespace RiemannMasullo.WeakCardinal

set_option quotPrecheck false

attribute [local instance] instIdeleClassMeasurableSpaceSec1 instIdeleClassBorelSpaceSec1
  instIdeleClassT2Sec1 instIdeleClassLocallyCompactSec1 instIdeleClassSecondCountableSec1
  instIdeleClassHaarMeasureSec1

variable {F : Type*} [Field F] [NumberField F]
local notation "C𝔽" => IdeleClassGroup (𝓞 F) F
local notation "C₁" => (ideleClassNorm F).ker
local notation "ord(" j ")" => (j).val.2.2.1
local notation "jets(" χ ", " a ", " s ")" => SpectralStripJetIndex (F := F) χ a 0 s

/-- All retained coordinates of one character in the closed radius-six ordinate window form
a finite set, with no arithmetic spacing estimate. -/
theorem spectralCardinalWindow_finite (χ : PontryaginDual C₁ → PontryaginDual C𝔽)
    {a s : ℝ} (hs₃ : s ≤ 3) (j : jets(χ, a, s)) :
    {i : jets(χ, a, s) | i.val.1 = j.val.1 ∧ |ord(i)-ord(j)| ≤ 6}.Finite := by
  let E := {i : jets(χ, a, s) | i.val.1 = j.val.1 ∧ |ord(i)-ord(j)| ≤ 6}
  let K := Icc (ord(j)-6) (ord(j)+6)
  let A (t : ℝ) := (a : ℂ) + (t : ℂ)*Complex.I
  let L := continuedCompletedHeckeL (χ j.val.1)
  have hA : Continuous A := continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hi : Injective A := fun x y h ↦ by simpa [A, Complex.add_im, Complex.mul_im] using congrArg Complex.im h
  have hL : MeromorphicOn L (A '' K) := fun z _ ↦ (continuedCompletedHeckeL_spec _).1.meromorphicOn z (mem_univ z)
  have hf := (MeromorphicOn.divisor L (A '' K)).finiteSupport (isCompact_Icc.image hA)
  apply Set.Finite.of_finite_image (f := fun i : jets(χ, a, s) ↦ A (ord(i))) (s := E)
  · apply hf.subset
    rintro _ ⟨i, hmem, rfl⟩
    obtain ⟨hχi, hdist⟩ := hmem
    have ht : ord(i) ∈ K := by obtain ⟨hl, hr⟩ := abs_le.mp hdist; constructor <;> linarith
    change MeromorphicOn.divisor L (A '' K) (A (ord(i))) ≠ 0
    rw [hL.divisor_apply ⟨ord(i), ht, rfl⟩]
    obtain ⟨hb, hk⟩ := retained_offset_order_zero hs₃ i.property
    have hi' := i.property
    rw [spectralStripMultiplicity_boundary (le_refl (0:ℝ)) (Or.inr hb), hχi, hb, add_zero, hk] at hi'
    have hpos := (lt_spectralBoundaryMultiplicity _ _ _).mp hi'
    change (meromorphicOrderAt L (A (ord(i)))).untop₀ ≠ 0
    intro hz
    exact (Nat.ne_of_gt hpos.1) (by change (meromorphicOrderAt L (A (ord(i)))).untop₀.toNat = 0; simp [hz])
  · intro i hiE k hkE hik
    have hit := hi hik
    obtain ⟨ib, im⟩ := retained_offset_order_zero hs₃ i.property
    obtain ⟨kb, km⟩ := retained_offset_order_zero hs₃ k.property
    exact Subtype.ext <| Prod.ext (hiE.1.trans hkE.1.symm) (Prod.ext (ib.trans kb.symm) (Prod.ext hit (im.trans km.symm)))

/-- The entire window used in the finite numerical calculation. -/
def spectralCardinalWindow (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ}
    (hs₃ : s ≤ 3) (j : jets(χ, a, s)) : Finset jets(χ, a, s) :=
  (spectralCardinalWindow_finite χ hs₃ j).toFinset

theorem mem_spectralCardinalWindow (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ}
    (hs₃ : s ≤ 3) (i j : jets(χ, a, s)) :
    i ∈ spectralCardinalWindow χ hs₃ j ↔ i.val.1 = j.val.1 ∧ |ord(i)-ord(j)| ≤ 6 := Set.Finite.mem_toFinset _

local notation "Q(" a ", " hs ")" => spectralSobolevQuotient F a
  ((neg_nonpos.mpr (le_refl (0 : ℝ))).trans le_rfl) hs
local notation "D(" a ", " hs ")" => spectralSobolevDualEmbedding F a
  ((neg_nonpos.mpr (le_refl (0 : ℝ))).trans le_rfl) hs
local notation "wave(" χ ", " hs ", " i ")" =>
  (spectralStripJet_memLp χ (le_refl (0 : ℝ)) hs i).toLp
    (spectralZeroJet (F := F) (χ (i).val.1) (i).val.2.1 (i).val.2.2.1 (i).val.2.2.2)

/-- The Riesz coordinates in the actual quotient have the transposed Gram of the native
Hecke jets. In particular angular orthogonality survives orthogonal lifting. -/
theorem spectralQuotientRiesz_pair (χ : PontryaginDual C₁ → PontryaginDual C𝔽) {a s : ℝ}
    (hs : 0 ≤ s) (f : jets(χ, a, s) → StrongDual ℂ Q(a, hs))
    (hf : ∀ i, D(a, hs) (f i) = wave(χ, hs, i)) (i k : jets(χ, a, s)) :
    f i ((InnerProductSpace.toDual ℂ Q(a, hs)).symm (f k)) =
      ⟪wave(χ, hs, k), wave(χ, hs, i)⟫_ℂ := by
  let T : StrongDual ℂ Q(a, hs) →ₗᵢ[ℂ] _ :=
    ⟨D(a, hs), (spectralSobolevDualEmbedding_isometry_range (F := F) a _ hs).1.norm_map_of_map_zero (map_zero _)⟩
  calc
    _ = ⟪T (f k), T (f i)⟫_ℂ := riesz_inner_eq_realization T _ _
    _ = _ := congrArg₂ (inner ℂ) (hf k) (hf i)

end RiemannMasullo.WeakCardinal
