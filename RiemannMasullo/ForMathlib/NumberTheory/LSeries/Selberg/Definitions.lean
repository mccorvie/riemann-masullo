module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.HalfCoefficients
public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Weight
-- Use the original complex topology instance in the theta series and Fourier statements.
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.NumberTheory.LSeries.HardyZ
public import Mathlib.NumberTheory.SmoothNumbers
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public noncomputable section

open MeasureTheory Set Classical
open scoped BigOperators

namespace RiemannMasullo.Selberg

/-- The Dirichlet coefficients of the inverse square root of zeta. -/
def alpha (n : ℕ) : ℝ := spectralLineJet_selbergHalfMoebius n

/-- The positive half-zeta coefficients that majorize the absolute values of `alpha`. -/
def posHalf (n : ℕ) : ℝ := spectralLineJet_selbergHalfZeta n

/-- The positive integers from one through the mollifier length `N`. -/
def D (N : ℕ) := Finset.Icc 1 N

/-- The half-Möbius coefficients with Selberg’s logarithmic taper of length `N`. -/
def beta (N n : ℕ) : ℝ :=
  if n ∈ D N then alpha n * (Real.log ((N : ℝ) / n) / Real.log N) else 0

/-- The height corresponding to the mollifier length `N`, namely `N ^ 100`. -/
def H (N : ℕ) : ℕ := N ^ 100

/-- The angle of the theta-kernel shift at height `H N`. -/
def angle (N : ℕ) : ℝ := Real.pi / 4 - 1 / (2 * (H N : ℝ))

/-- Hardy’s Z function multiplied by the Selberg weight for the tapered mollifier. -/
def signal (N : ℕ) (t : ℝ) :=
  spectralLineJet_selbergWeight (H N) N (beta N) t * hardyZ t

/-- The condition that the coefficients have absolute value at most one on `D N`. -/
def bd (N : ℕ) (b : ℕ → ℝ) := ∀ n ∈ D N, |b n| ≤ 1

/-- The condition that `n` is positive and every prime factor of `n` divides `r`. -/
def smooth (r n : ℕ) := n ∈ Nat.factoredNumbers r.primeFactors

/-- The product of `(1 - 1/p)⁻¹` over the primes dividing `r`. -/
noncomputable def smoothMass (r : ℕ) : ℝ :=
  ∏ p ∈ r.primeFactors, (1 - (p : ℝ)⁻¹)⁻¹

/-- The logarithmically weighted sum of `alpha n / n` through `Y` over indices coprime to `r`. -/
def logSum (r : ℕ) (Y : ℝ) : ℝ :=
  ∑ n ∈ (D ⌊Y⌋₊).filter (Nat.Coprime r), alpha n / n * Real.log (Y / n)

/-- The sum of coefficient pairs with product divisible by `r`, weighted by `1 / (k^p v)`. -/
def row (N : ℕ) (b : ℕ → ℝ) (p : ℝ) (r : ℕ) : ℝ :=
  ∑ k ∈ D N, ∑ v ∈ (D N).filter (fun v ↦ r ∣ k*v),
    b k * b v / ((k : ℝ) ^ p * v)

/-- The Jordan totient product at the real exponent `p`. -/
def jordan (p : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) ^ p * ∏ l ∈ r.primeFactors, (1 - (l : ℝ) ^ (-p))

/-- Summation over four independent indices from one through `N`. -/
def fourSum (N : ℕ) (u : ℕ → ℕ → ℕ → ℕ → ℝ) : ℝ :=
  ∑ k ∈ D N, ∑ l ∈ D N, ∑ m ∈ D N, ∑ v ∈ D N, u k l m v

/-- The coefficient product of a quadruple divided by the two denominator indices. -/
def coef (b : ℕ → ℝ) (k l m v : ℕ) : ℝ := b k*b l*b m*b v / ((l : ℝ)*v)

/-- The greatest common divisor of `k*v` and `l*m` divided by `k*m`. -/
def ratio (k l m v : ℕ) : ℝ := (Nat.gcd (k*v) (l*m) : ℝ) / ((k : ℝ)*m)

/-- The four-index mollifier sum with the gcd ratio raised to power `p`. -/
def energy (N : ℕ) (b : ℕ → ℝ) (p : ℝ) : ℝ :=
  fourSum N fun k l m v ↦ coef b k l m v * ratio k l m v ^ p

/-- The complex Gaussian theta sum over positive integers with argument squared. -/
def psi (z : ℂ) : ℂ :=
  ∑' n : ℕ, Complex.exp (-(Real.pi : ℂ)*((n+1 : ℕ) : ℂ)^2*z^2)

/-- The logarithmic theta kernel with the exponential correction term subtracted. -/
def K (z : ℂ) : ℂ :=
  Complex.exp (z/2)*psi (Complex.exp z) - Complex.exp (-z/2)/2

/-- The complex phase `exp(iu)` at real angle `u`. -/
def osc (u : ℝ) : ℂ := Complex.exp (Complex.I * (u : ℂ))

/-- The Fourier integral with angular frequency `t` and phase `exp(ity)`. -/
def ft (f : ℝ → ℂ) (t : ℝ) : ℂ := ∫ y : ℝ, f y * osc (t*y)

/-- The shifted theta kernel summed over the two indices of the mollifier. -/
def dual (N : ℕ) (b : ℕ → ℝ) (y : ℝ) : ℂ :=
  ∑ k ∈ D N, ∑ l ∈ D N, ((b k*b l/Real.sqrt ((k : ℝ)*l) : ℝ) : ℂ) *
    K (((y + Real.log ((k : ℝ)/l) : ℝ) : ℂ) + Complex.I*(angle N : ℂ))

/-- The sum of rotated theta series at the frequencies `k/l` of the mollifier. -/
def g (N : ℕ) (b : ℕ → ℝ) (x : ℝ) : ℂ :=
  ∑ k ∈ D N, ∑ l ∈ D N, ((b k*b l/l : ℝ) : ℂ) *
    psi (((x*k/l : ℝ) : ℂ)*osc (angle N))

/-- The product of the mollifier sums at one and zero in the theta correction. -/
def constTerm (N : ℕ) (b : ℕ → ℝ) : ℝ :=
  (∑ k ∈ D N, b k/k) * (∑ l ∈ D N, b l)

/-- The squared norm integral of `g` on `(1, ∞)` with weight `x^(-q)`. -/
def J (N : ℕ) (b : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∫ x in Ioi (1 : ℝ), ‖g N b x‖^2 * x^(-q)

/-- The real Gaussian sum on the positive integer multiples of `v`. -/
def theta (v : ℝ) : ℝ := ∑' n : ℕ, Real.exp (-(((n+1 : ℕ) : ℝ)*v)^2)

/-- The mass of the standard Gaussian `exp(-x²)` on the positive half-line. -/
def gaussC : ℝ := Real.sqrt Real.pi / 2

/-- The Mellin integral of the difference between the Gaussian sum and its integral approximation. -/
def errorC (q : ℝ) : ℝ := ∫ v in Ioi (0 : ℝ), v^(-q)*(theta v - gaussC/v)

/-- The common Gaussian scale for equal frequencies at height `H N`. -/
def scale (N : ℕ) : ℝ := Real.sqrt (2*Real.pi*Real.sin (1/(H N : ℝ)))

/-- The contribution of equal Gaussian frequencies to the weighted integral `J`. -/
def diag (N : ℕ) (b : ℕ → ℝ) (q : ℝ) : ℝ :=
  fourSum N fun k l m v ↦ coef b k l m v *
    ∫ x in Ioi (1 : ℝ), x^(-q)*theta (scale N / ratio k l m v * x)

/-- The integral of an oscillatory Gaussian with damping `P`, phase coefficient `Q`, and weight `x^(-q)`. -/
def pairInt (P Q q : ℝ) : ℂ :=
  ∫ x in Ioi (1 : ℝ), (x^(-q) : ℝ) *
    Complex.exp ((-(P : ℂ) + Complex.I*(Q : ℂ))*(x : ℂ)^2)

/-- The positive multiple `(m+1)k/l` of a mollifier frequency. -/
def freq (m k l : ℕ) : ℝ := ((m : ℝ)+1)*k/l

/-- The oscillatory Gaussian integral contributed by one ordered pair of theta indices. -/
def pair (N k l u v : ℕ) (q : ℝ) (ij : ℕ × ℕ) : ℂ :=
  let A := freq ij.1 k l
  let B := freq ij.2 u v
  pairInt (Real.pi*Real.sin (1/(H N : ℝ))*(A^2+B^2))
    (Real.pi*Real.cos (1/(H N : ℝ))*(B^2-A^2)) q

/-- The Fourier multiplier obtained by integrating a phase over a window of length `h`. -/
def mult (h y : ℝ) : ℂ := ∫ u in (0 : ℝ)..h, osc (u*y)

/-- The squared norm integral of the tapered dual with weight `exp(-q |y|)`. -/
def dualMass (N : ℕ) (q : ℝ) : ℝ :=
  ∫ y : ℝ, Real.exp (-q*|y|)*‖dual N (beta N) y‖^2

/-- The integral of `f` over the window from `t` to `t+h`. -/
def win (f : ℝ → ℝ) (h t : ℝ) : ℝ := ∫ u in t..t+h, f u

/-- The second moment of a real function on the interval `(0, U]`. -/
def second (U : ℝ) (f : ℝ → ℝ) : ℝ := ∫ t in Ioc (0 : ℝ) U, (f t)^2

end RiemannMasullo.Selberg
