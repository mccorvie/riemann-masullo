module

public import RiemannMasullo.Ch02_AdelicTheta.Sec3
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b

/-! # Exact radial support of same-stage Fourier-band theta tests -/

public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Bₛ" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "Jₛ" => SIdeleQuotient F S
local notation "J₁" => (sIdeleQuotientNorm F S).ker
local notation "N(" q ")" => ((sIdeleQuotientNorm F S q).val : ℝ)

/-- The S-unit orbit of an idèle keeps its product norm, so theta vanishes
outside the radial bound on the support of the additive test. -/
theorem sLocalAdelicThetaOnClasses_eq_zero_of_tsupport_subset_productRegion
    (g : Bₛ) {Y : ℝ}
    (hg : tsupport g.val ⊆ Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S Y)
    (q : Jₛ) (hq : Y < N(q)) : sLocalAdelicThetaOnClasses F S g q = 0 := by
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
  rw [sIdeleQuotientNorm_mk] at hq
  rw [sLocalAdelicThetaOnClasses_mk, sLocalAdelicTheta_apply]
  have hzero (ξ : (Set.integer (S : Set (HeightOneSpectrum (𝓞 F))) F)ˣ) :
      g (Multiplicative.ofAdd (sUnitEmbedding F S ξ * a).val) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hle := (mem_sLocalPWProductRegion_units (F := F) (S := S) Y
      (sUnitEmbedding F S ξ * a)).mp (hg hs)
    have hξ : sIdeleNorm F S (sUnitEmbedding F S ξ) = 1 :=
      MonoidHom.mem_ker.mp ((sIdeleNorm_spec F S).2 ⟨ξ, rfl⟩)
    rw [map_mul, hξ, one_mul] at hle
    exact (not_le_of_gt hq) hle
  exact (tsum_congr hzero).trans tsum_zero

/-- The norm-one average preserves the same exact product-norm vanishing. -/
theorem sLocalHomogeneousAdelicThetaLinearMap_eq_zero_of_tsupport_subset_productRegion
    (ω : PontryaginDual J₁) (g : Bₛ) {Y : ℝ}
    (hg : tsupport g.val ⊆ Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S Y)
    (q : Jₛ) (hq : Y < N(q)) :
    sLocalHomogeneousAdelicThetaLinearMap F S ω g q = 0 := by
  rw [sLocalHomogeneousAdelicThetaLinearMap_apply]
  have hterm (h : J₁) :
      sLocalAdelicThetaOnClasses F S g (q * h.val) * (ω h : ℂ) = 0 := by
    have hN : sIdeleQuotientNorm F S (q * h.val) = sIdeleQuotientNorm F S q := by
      rw [map_mul, MonoidHom.mem_ker.mp h.property, mul_one]
    have hq' : Y < N(q * h.val) := hN.symm ▸ hq
    rw [sLocalAdelicThetaOnClasses_eq_zero_of_tsupport_subset_productRegion g hg _ hq', zero_mul]
  simp only [hterm]
  exact integral_zero (α := ↥J₁) (G := ℂ)

/-- For a same-stage generator of the invariant product-band level, the
homogeneous theta of the Fourier transform is supported at quotient norm at
most the original band radius. -/
theorem sLocalPWTests_sameStage_fourierTheta_tsupport_subset
    (ω : PontryaginDual J₁) (f : Bₛ) {Y : ℝ}
    (hf : f ∈ sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S Y)) :
    tsupport (sLocalHomogeneousAdelicThetaLinearMap F S ω (sAdeleSchwartzFourier f)) ⊆
      {q : Jₛ | N(q) ≤ Y} := by
  obtain ⟨g, hg, _, hsupport⟩ :=
    (mem_sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S Y) f).mp hf
  have hself : sAdeleSchwartzTransition F (le_rfl (a := S)) g = g := by
    classical
    apply Subtype.ext
    funext x
    rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, sAdeleSchwartzTransition_apply,
      ite_eq_left (fun w hw ↦ (hw w.property).elim)]
  rw [hself] at hg
  subst f
  refine closure_minimal (fun q hq ↦ ?_) ?_
  · by_contra hle
    exact hq (sLocalHomogeneousAdelicThetaLinearMap_eq_zero_of_tsupport_subset_productRegion
      ω (sAdeleSchwartzFourier g) hsupport q (lt_of_not_ge hle))
  · exact isClosed_le (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_sIdeleQuotientNorm F S).continuous)) continuous_const

/-- Auxiliary result for Theorem 12.4.1.1, p. 514 n. 2. Along a norm section,
reflection in the logarithmic coordinate places the Fourier-test theta
of a same-stage band generator in the right half-line with endpoint
`-Real.log Y`. -/
theorem sLocalPWTests_sameStage_fourierTheta_reflected_log_eq_zero
    (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ (sIdeleQuotientNorm F S))
    (ω : PontryaginDual J₁) (f : Bₛ) {Y : ℝ} (hY : 0 < Y)
    (hf : f ∈ sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S Y))
    (x : ℝ) (hx : x < -Real.log Y) :
    let t : ℝ≥0ˣ := Units.mk0 (Real.exp (-x)).toNNReal (by positivity)
    sLocalHomogeneousAdelicThetaLinearMap F S ω (sAdeleSchwartzFourier f) (τ t) = 0 := by
  intro t
  have ht : (t.val : ℝ) = Real.exp (-x) := Real.coe_toNNReal _ (Real.exp_pos _).le
  have hlog : Real.log Y < -x := by simpa only [neg_neg] using neg_lt_neg hx
  have hN : Y < N(τ t) := by
    rw [hτ, ht]
    exact (Real.log_lt_iff_lt_exp hY).mp hlog
  apply image_eq_zero_of_notMem_tsupport
  exact fun h ↦ (not_le_of_gt hN) (sLocalPWTests_sameStage_fourierTheta_tsupport_subset ω f hf h)

end RiemannMasullo
