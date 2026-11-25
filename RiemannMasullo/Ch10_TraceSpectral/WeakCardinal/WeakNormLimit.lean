module

public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.FiniteWindowEstimate
public import RiemannMasullo.Ch10_TraceSpectral.WeakCardinal.FiniteInterpolation

/-! The radius-six comparison for #7406 is developed in issue comment 7163925073.

 Recovering a full native weak norm from finite same-character interpolants. -/

@[expose] public noncomputable section

open Filter MeasureTheory Set
open scoped InnerProductSpace Matrix Topology

namespace RiemannMasullo.WeakCardinal

variable {I J H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V]

open scoped Classical in
/-- The scalar radius-six estimate transfers to the full weak quotient cardinal by cofinal
finite Gram approximation. The required dictionary concerns finite matrices only. -/
theorem weakNorm_radiusSix_of_sameCharacter_gram
    (x : J → H) (f : J → StrongDual ℂ H) (hb : IsSpectralMarkushevichBasis x f)
    (ω : J → I) (t : J → ℝ) (j : J) (E : Finset J)
    (hE : ∀ i, i ∈ E ↔ ω i = ω j ∧ |t i-t j| ≤ 6)
    (hoff : ∀ i k, ω i ≠ ω k → f i ((InnerProductSpace.toDual ℂ H).symm (f k)) = 0)
    {θ : ℝ} (hθ : 1 < θ) (hθ' : θ ≤ 3/2) (D : H →L[ℂ] V) {γ : ℝ} (hγ : 0 ≤ γ)
    (hfinite : ∀ (S : Finset J) (hj : j ∈ S), (∀ i ∈ S, ω i = ω j) →
      Function.Injective (fun k : S ↦ t k.val) ∧
      ‖D (finiteRieszCardinal f j S)‖ = γ * Real.sqrt (finiteSiteWeakForm θ t S j hj))
    (A : Lp ℂ 2 (sobolevMeasure θ) →L[ℂ] Lp ℂ 2 (sobolevMeasure θ)) (hA : ‖A‖ ≤ 13/48)
    (hAeval : ∀ (g : Lp ℂ 2 (sobolevMeasure θ)) i, ω i = ω j →
      (∫ ξ, phase (t i) ξ * A g ξ ∂angularMeasure) =
        (scaledCutoffQuotient (t j) 6 (t i) : ℂ) * (∫ ξ, phase (t i) ξ * g ξ ∂angularMeasure)) :
    let hj : j ∈ E := (hE j).2 ⟨rfl, by simp⟩
    let g := γ * Real.sqrt (finiteSiteWeakForm θ t E j hj)
    (1-radiusSixError)*g ≤ ‖D (x j)‖ ∧ ‖D (x j)‖ ≤ (1+radiusSixError)*g := by
  classical
  intro hj g
  have hiE (i : J) (hi : i ∈ E) := ((hE i).1 hi).1
  have ht := (hfinite E hj hiE).1
  have hlim : Tendsto (fun S ↦ ‖D (finiteRieszCardinal f j S)‖) atTop (𝓝 ‖D (x j)‖) :=
    ((D.continuous.tendsto _).comp (tendsto_finiteRieszCardinal x f hb j)).norm
  have hev : ∀ᶠ S : Finset J in atTop,
      (1-radiusSixError)*g ≤ ‖D (finiteRieszCardinal f j S)‖ ∧
        ‖D (finiteRieszCardinal f j S)‖ ≤ (1+radiusSixError)*g := by
    filter_upwards [eventually_ge_atTop E] with S hS
    let T := S.filter (fun k ↦ ω k = ω j)
    have hTS : T ⊆ S := Finset.filter_subset _ _
    have hET : E ⊆ T := fun i hi ↦ Finset.mem_filter.mpr ⟨hS hi, hiE i hi⟩
    have hTj := hET hj
    have hsame (i : J) (hi : i ∈ T) : ω i = ω j := (Finset.mem_filter.mp hi).2
    have hcard := finiteRieszCardinal_eq_of_subset_orthogonal x f hb hTS hTj (fun k hk hkT l hl ↦
      hoff k l fun hkl ↦ hkT (Finset.mem_filter.mpr ⟨hk, hkl.trans (hsame _ hl)⟩))
    have hwindow : range (fun i : E ↦ t i.val) = radiusSixSites (range (fun i : T ↦ t i.val)) (t j) := by
      ext u
      constructor
      · rintro ⟨i, rfl⟩
        have hn := ((hE i.val).1 i.property).2
        exact ⟨⟨⟨i.val, hET i.property⟩, rfl⟩, by obtain ⟨hl,hr⟩ := abs_le.mp hn; constructor <;> linarith⟩
      · rintro ⟨⟨i,rfl⟩, hl, hr⟩
        exact ⟨⟨i.val,(hE i.val).2 ⟨hsame _ i.property, abs_le.mpr ⟨by linarith, by linarith⟩⟩⟩,rfl⟩
    obtain ⟨hinj, henergy⟩ := hfinite T hTj hsame
    have hcomp := finiteWeakGram_radiusSix_of_multiplier hθ hθ' (fun i : E ↦ t i.val)
      (fun i : T ↦ t i.val) ht hinj ⟨j, hj⟩ ⟨j, hTj⟩ rfl hwindow A hA
      (fun g u hu ↦ by obtain ⟨i,rfl⟩ := hu; exact hAeval g i.val (hsame _ i.property))
    rw [← hcard, henergy, finiteSiteWeakForm_eq]
    dsimp only [g]
    rw [finiteSiteWeakForm_eq]
    constructor
    · simpa only [g, mul_left_comm (1-radiusSixError) γ] using mul_le_mul_of_nonneg_left hcomp.1 hγ
    · simpa only [g, mul_left_comm (1+radiusSixError) γ] using mul_le_mul_of_nonneg_left hcomp.2 hγ
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hlim (hev.mono fun _ h ↦ h.1),
    le_of_tendsto_of_tendsto hlim tendsto_const_nhds (hev.mono fun _ h ↦ h.2)⟩

end RiemannMasullo.WeakCardinal
