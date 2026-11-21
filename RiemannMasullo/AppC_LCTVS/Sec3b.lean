module

public import RiemannMasullo.AppC_LCTVS.Sec3a_part2

/-!
# Integral kernels

Masullo, Appendix C, §C.3.7, pp. 707–708.
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RiemannMasullo

variable {X : Type*}
  [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X]
  (μ : Measure X) [IsFiniteMeasureOnCompacts μ] [Measure.InnerRegular μ]

-- TODO(paper-gap): The diagonal need not be product-null as asserted on p. 707.
-- For a one-point space with unit point mass, the diagonal has product measure one.

/-- Paper: (C.3.7.1), p. 708. A square-integrable kernel defines a Hilbert-Schmidt
endomorphism of L².
Deviation: The kernel is an L² class. The correspondence from (C.3.6.5)–(C.3.6.6)
uses source-first coordinates, so the operator is obtained by swapping the coordinates. -/
def integralKernelOperator (k : Lp ℂ 2 (μ.prod μ)) :
    hilbertSchmidtOperators (Lp ℂ 2 μ) (Lp ℂ 2 μ) :=
  (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose
    (Lp.compMeasurePreserving Prod.swap (Measure.measurePreserving_swap (μ := μ) (ν := μ)) k)

/-- Paper: (C.3.7.1), p. 708. The operator acts by integrating the product of the
kernel and the input function in the source variable.
Deviation: The integral is required to be defined and to give the operator value
almost everywhere in the target variable. -/
theorem integralKernelOperator_apply (k : Lp ℂ 2 (μ.prod μ)) (f : Lp ℂ 2 μ) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ k (x, y) * f y) μ ∧
      (integralKernelOperator μ k).val f x = ∫ y, k (x, y) * f y ∂μ := by
  let hswap := Measure.measurePreserving_swap (μ := μ) (ν := μ)
  let swapped := Lp.compMeasurePreserving Prod.swap hswap k
  have hkernel : ∀ᵐ p ∂(μ.prod μ), swapped p.swap = k p :=
    hswap.quasiMeasurePreserving.ae (Lp.coeFn_compMeasurePreserving k hswap)
  filter_upwards [Measure.ae_ae_of_ae_prod hkernel,
    (hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose_spec.2 swapped f] with x hx happly
  have hmul : (fun y ↦ swapped (y, x) * f y) =ᵐ[μ] fun y ↦ k (x, y) * f y := by
    filter_upwards [hx] with y hy
    exact congrArg (· * f y) hy
  exact ⟨happly.1.congr hmul, happly.2.trans (integral_congr_ae hmul)⟩

/-- Paper: Theorem C.3.7.1(1), p. 708. The Hilbert-Schmidt norm of the integral
operator is the L² norm of the kernel. -/
theorem schattenNorm_integralKernelOperator (k : Lp ℂ 2 (μ.prod μ)) :
    schattenNorm (integralKernelOperator μ k) = ‖k‖ := by
  unfold integralKernelOperator
  rw [(hilbertSchmidtOperators_equiv_Lp_prod μ μ).choose_spec.1]
  exact Lp.norm_compMeasurePreserving k (Measure.measurePreserving_swap (μ := μ) (ν := μ))

/-- Paper: Theorem C.3.7.1(2)(a), p. 708. If a square-integrable kernel is jointly
continuous at almost every diagonal point and its operator is nuclear, the diagonal
is integrable and its integral is the trace.
Deviation: The continuity and diagonal evaluation use a specified representative
of the L² kernel class. -/
theorem hilbertTrace_integralKernelOperator_of_ae_continuous {k : X × X → ℂ}
    (hk : MemLp k 2 (μ.prod μ))
    (hT : IsNuclearOperator (integralKernelOperator μ (hk.toLp k)).val)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt k (x, x)) :
    Integrable (fun x ↦ k (x, x)) μ ∧
      hilbertTrace ⟨(integralKernelOperator μ (hk.toLp k)).val, hT⟩ =
        ∫ x, k (x, x) ∂μ := by sorry

/-- Paper: Theorem C.3.7.1(2)(b), p. 708. A nuclear integral operator has
Hilbert-Schmidt factors whose kernel convolution represents the original kernel.
The convolution is defined almost everywhere on the diagonal, where it is
integrable and computes the trace.
Deviation: The smoothening is expressed by the factor-kernel convolution
described on pp. 707–708. -/
theorem exists_integralKernel_smoothening (k : Lp ℂ 2 (μ.prod μ))
    (hT : IsNuclearOperator (integralKernelOperator μ k).val) :
    ∃ a b : Lp ℂ 2 (μ.prod μ),
      (integralKernelOperator μ k).val =
        (integralKernelOperator μ a).val.comp (integralKernelOperator μ b).val ∧
      let integrand (p : X × X) (z : X) := a (p.1, z) * b (z, p.2)
      let smoothened (p : X × X) := ∫ z, integrand p z ∂μ
      (∀ᵐ p ∂(μ.prod μ), Integrable (integrand p) μ ∧ smoothened p = k p) ∧
        (∀ᵐ x ∂μ, Integrable (integrand (x, x)) μ) ∧
        Integrable (fun x ↦ smoothened (x, x)) μ ∧
        hilbertTrace ⟨(integralKernelOperator μ k).val, hT⟩ =
          ∫ x, smoothened (x, x) ∂μ := by sorry

end RiemannMasullo
