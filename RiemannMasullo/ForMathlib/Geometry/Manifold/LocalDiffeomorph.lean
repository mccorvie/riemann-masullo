module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

public section

namespace RiemannMasullo

open scoped Manifold

/-- A map that agrees locally with a source chart followed by an inverse target chart
is a local diffeomorphism. -/
theorem isLocalDiffeomorph_of_chartAt {𝕜 E H M N : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
    (I : ModelWithCorners 𝕜 E H) (n : WithTop ℕ∞)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    [TopologicalSpace N] [ChartedSpace H N] [IsManifold I n N] (f : M → N)
    (hcenter : ∀ x, chartAt H x x ∈ (chartAt H (f x)).target)
    (heq : ∀ x y, y ∈ (chartAt H x).source → chartAt H x y ∈ (chartAt H (f x)).target →
      f y = (chartAt H (f x)).symm (chartAt H x y)) :
    IsLocalDiffeomorph I I n f := by
  intro x
  let a := chartAt H x
  let b := chartAt H (f x)
  let e := a.trans b.symm
  have ha : ContMDiffOn I I n a a.source := contMDiffOn_chart
  have ha' : ContMDiffOn I I n a.symm a.target := contMDiffOn_chart_symm
  have hb : ContMDiffOn I I n b b.source := contMDiffOn_chart
  have hb' : ContMDiffOn I I n b.symm b.target := contMDiffOn_chart_symm
  let φ : PartialDiffeomorph I I M N n :=
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := hb'.comp (ha.mono Set.inter_subset_left) Set.inter_subset_right
      contMDiffOn_invFun := ha'.comp (hb.mono Set.inter_subset_left) Set.inter_subset_right }
  rw [IsLocalDiffeomorphAt]
  exact ⟨φ, ⟨mem_chart_source H x, hcenter x⟩, fun y hy ↦ heq x y hy.1 hy.2⟩

end RiemannMasullo
