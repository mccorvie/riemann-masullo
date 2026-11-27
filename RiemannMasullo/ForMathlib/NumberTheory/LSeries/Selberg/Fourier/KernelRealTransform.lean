module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 17. The angular Fourier transform of the real-axis kernel at t equals half the completed
zeta function at 1/2 + it.
Titchmarsh, §10.1, p. 254, first unnumbered display, and §10.10 p. 269. -/
theorem kernel_real_transform (t : ℝ) :
    ft (fun y ↦ K (y : ℂ)) t = completedRiemannZeta (1/2+(t : ℂ)*Complex.I)/2 := by
  sorry

end RiemannMasullo.Selberg
