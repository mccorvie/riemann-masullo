module

public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3b
import RiemannMasullo.Ch02_AdelicTheta.Sec1

/-! # Positive same-stage bands for compact Fourier support -/

public noncomputable section

open IsDedekindDomain NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

variable {F : Type*} [Field F] [NumberField F]
  {S : Finset (HeightOneSpectrum (𝓞 F))}

/-- Every ordinary S-adelic test with compact Fourier support belongs to a
same-stage Paley–Wiener test space with positive product radius. -/
theorem exists_sLocalPWTests_sameStage_productRegion_of_hasCompactSupport_fourier
    (f : SchwartzBruhat (Multiplicative (SAdeleRing F S)))
    (hf : HasCompactSupport (sAdeleSchwartzFourier f).val) :
    ∃ B > 0, f ∈ sLocalPWTests (F := F) (S := S) (T := S) le_rfl (sLocalPWProductRegion S B) := by
  let m (x : SAdeleRing F S) : ℝ :=
    (∏ w : InfinitePlace F, ‖x.1 w‖ ^ w.mult) * (∏ v : S, ‖x.2 v‖)
  have hm : Continuous m := by
    dsimp only [m]
    exact (continuous_finsetProd Finset.univ (fun w _ ↦
      ((continuous_apply w).comp continuous_fst).norm.pow w.mult)).mul
      (continuous_finsetProd Finset.univ (fun v _ ↦ ((continuous_apply v).comp continuous_snd).norm))
  have hK : IsCompact (tsupport (sAdeleSchwartzFourier f).val) := hf
  obtain ⟨R, hR⟩ := (hK.image (hm.comp continuous_toAdd)).bddAbove
  let B : ℝ := max 1 R
  have hB : 0 < B := zero_lt_one.trans_le (le_max_left _ _)
  have hSupport : tsupport (sAdeleSchwartzFourier f).val ⊆
      Multiplicative.toAdd ⁻¹' sLocalPWProductRegion S B := by
    intro x hx
    change m x.toAdd ≤ B
    exact (hR (Set.mem_image_of_mem _ hx)).trans (le_max_right _ _)
  have hself : sAdeleSchwartzTransition F (le_rfl (a := S)) f = f := by
    classical
    apply Subtype.ext
    funext x
    rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, sAdeleSchwartzTransition_apply,
      ite_eq_left (fun w hw ↦ (hw w.property).elim)]
  exact ⟨B, hB, (mem_sLocalPWTests (F := F) (S := S) (T := S) le_rfl
    (sLocalPWProductRegion S B) f).2 ⟨f, hself, hf, hSupport⟩⟩

end RiemannMasullo
