module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

/-- Card 18. Shifting the kernel from the real axis to height a in the strip multiplies its
Fourier transform at t by exp(at).
Titchmarsh, §10.10, p. 269, rotation of the theta kernel. -/
theorem shift_transform (t a : ℝ) (ha : |a| < Real.pi/4) :
    ft (fun y ↦ K ((y : ℂ)+Complex.I*a)) t =
      (Real.exp (a*t) : ℂ) * ft (fun y ↦ K (y : ℂ)) t := by
  sorry

end RiemannMasullo.Selberg
