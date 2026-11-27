module

public import RiemannMasullo.Ch11_ShellStructure.Sec2b
import RiemannMasullo.Ch06_LocalGlobal.Sec1

/-! # The rational singleton Sobolev level from integer-tail tests

The closed weighted theta images are compared in the actual singleton space.
Relative-unit averaging reduces the comparison to the same-radius
normalization of radial Fourier generators.
-/

public noncomputable section

open IsDedekindDomain MeasureTheory NumberField Set
open scoped NumberField.AdeleRing

namespace RiemannMasullo

local notation "Polar(" v ")" => sAdelePolarSubspace ℚ {v}
local notation "PWTheta(" v ", " s ", " ha ")" =>
  sLocalPWThetaSobolevMap (F := ℚ) (S := {v}) (s := s) ha 1
local notation "TailTests(" v ", " B ")" =>
  sLocalPWTests (Finset.empty_subset {v}) (sLocalPWBox (F := ℚ) ∅ B)

/-- Paper: Definition 11.2.1.3(1) and (11.2.1.6), p. 488.
The actual trivial-character singleton level is the closed span of the weighted
images of polar-free integer-tail insertions at the same radius, given the
comparison on radial Fourier generators. Both spans are in the singleton space.
Deviation: Use the positive local twist of the repaired Sobolev level. -/
theorem sLocalInvariantPWSobolev_ratSingleton_eq_standardTail
    (v : HeightOneSpectrum (𝓞 ℚ)) (B : ℝ) (hB : 0 ≤ B)
    {a s : ℝ} (ha : 0 < a) (hs : 0 ≤ s)
    (hRadialGenerator : 0 ≤ B → ∀ (f : Polar(v)),
      tsupport (sAdeleSchwartzFourier f.val).val ⊆
        Multiplicative.toAdd ⁻¹' sLocalPWProductRegion {v} B →
      (∀ x y : SAdeleRing ℚ {v}, x.1 = y.1 →
        Valued.v (x.2 ⟨v, Finset.mem_singleton_self v⟩) =
          Valued.v (y.2 ⟨v, Finset.mem_singleton_self v⟩) →
        sAdeleSchwartzFourier f.val (Multiplicative.ofAdd x) =
          sAdeleSchwartzFourier f.val (Multiplicative.ofAdd y)) →
      ∃ t : Polar(v), t.val ∈ TailTests(v, B) ∧
        PWTheta(v, s, ha) f = PWTheta(v, s, ha) t) :
    sLocalInvariantPWSobolev (F := ℚ) (S := {v}) hs ha 1 B =
      (Submodule.span ℂ (Set.range fun t : {t : Polar(v) // t.val ∈ TailTests(v, B)} ↦
        PWTheta(v, s, ha) t.val)).topologicalClosure := by
  classical
  unfold sLocalInvariantPWSobolev
  apply le_antisymm
  · refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
    rintro _ ⟨f, rfl⟩
    have hf : f.val.val ∈ sLocalPWTests (S := {v}) (T := {v}) le_rfl
        (sLocalPWProductRegion {v} B) ⊓ Polar(v) :=
      Submodule.mem_inf.mpr ⟨f.property, f.val.property⟩
    obtain ⟨g, hg, hTheta, -, hFourierFixed⟩ :=
      exists_ratSingleton_invariantPW_relativeUnit_fixedLift v B f.val.val hf
    obtain ⟨u, hu, -, huBand⟩ :=
      (mem_sLocalPWTests le_rfl (sLocalPWProductRegion {v} B) g).mp (Submodule.mem_inf.mp hg).1
    have hSelf : sAdeleSchwartzTransition ℚ (le_rfl (a := ({v} : Finset _))) u = u := by
      apply Subtype.ext
      funext x
      rw [← show Multiplicative.ofAdd x.toAdd = x from rfl, sAdeleSchwartzTransition_apply,
        ite_eq_left (fun w hw ↦ (hw w.property).elim)]
    have hgBand : tsupport (sAdeleSchwartzFourier g).val ⊆
        Multiplicative.toAdd ⁻¹' sLocalPWProductRegion {v} B :=
      (hSelf.symm.trans hu) ▸ huBand
    let g₀ : Polar(v) := ⟨g, (Submodule.mem_inf.mp hg).2⟩
    have hSobolev : PWTheta(v, s, ha) g₀ = PWTheta(v, s, ha) f.val := by
      have h : sLocalHomogeneousAdelicThetaLinearMap ℚ {v} 1 g₀.val =
          sLocalHomogeneousAdelicThetaLinearMap ℚ {v} 1 f.val.val := hTheta
      unfold sLocalPWThetaSobolevMap
      apply MemLp.toLp_congr
      rw [h]
    obtain ⟨t, ht, htImage⟩ := hRadialGenerator hB g₀ hgBand
      (singletonRadial_of_relativeIntegralIdeleUnits_invariant v (sAdeleSchwartzFourier g)
        hFourierFixed)
    exact ⟨⟨t, ht⟩, htImage.symm.trans hSobolev⟩
  · refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_)
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨t.val, ratSingleton_standardTail_le_productPWTests v B t.property⟩, rfl⟩

end RiemannMasullo
