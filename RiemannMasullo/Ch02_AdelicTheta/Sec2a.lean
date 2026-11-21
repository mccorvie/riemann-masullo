module

public import RiemannMasullo.AppA_AlgebraicNT.Sec3
public import RiemannMasullo.Ch02_AdelicTheta.Sec1
public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.UniformOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Global adelic theta functions

Masullo, §§2.2.1–2.2.3, pp. 74–86. The theta operator sums over nonzero field
elements, with the additive Tamagawa measure used for its Fourier identity.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory NumberField Set Topology
open scoped NNReal NumberField.AdeleRing

namespace RiemannMasullo

section Lattice

/-- Paper: Equation (2.2.1.1), p. 75. The shell consists of vectors with
supremum norm in the half-open interval of width one starting at `r`. -/
def euclideanSupNormShell (N : ℕ) (r : ℝ) : Set (Fin N → ℝ) :=
  {x | ‖x‖ ∈ Ico r (r + 1)}

/-- Paper: Equation (2.2.1.1), p. 75. In dimension one the shell uses the
absolute value of the single coordinate, with the outer endpoint excluded. -/
theorem mem_euclideanSupNormShell_one (x r : ℝ) :
    (fun _ : Fin 1 ↦ x) ∈ euclideanSupNormShell 1 r ↔ r ≤ |x| ∧ |x| < r + 1 := by sorry

/-- Paper: Lemma 2.2.1.1, p. 75. Each shell is bounded in the supremum norm. -/
theorem euclideanSupNormShell_bounded {N : ℕ} (_hN : 1 ≤ N) {r : ℝ} (_hr : 1 ≤ r) :
    IsBounded (euclideanSupNormShell N r) := by
  apply (Metric.isBounded_ball (x := (0 : Fin N → ℝ)) (r := r + 1)).subset
  intro x hx
  simpa only [Metric.mem_ball, dist_zero_right] using hx.2

/-- Paper: Lemma 2.2.1.1, p. 75. Each shell is measurable for completed
Lebesgue measure. -/
theorem euclideanSupNormShell_lebesgueMeasurable {N : ℕ} (_hN : 1 ≤ N) {r : ℝ}
    (_hr : 1 ≤ r) :
    NullMeasurableSet (euclideanSupNormShell N r) volume := by
  exact (measurableSet_Ico.preimage continuous_norm.measurable).nullMeasurableSet

/-- Disjoint balls centered on lattice points fit into a thicker shell. -/
private theorem shell_packing {N : ℕ}
    (Γ : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology Γ] :
    ∃ d : ℝ, 0 < d ∧ d ≤ 1 ∧ ∀ r : ℝ, 2 ≤ r →
      let S := (Γ : Set (Fin N → ℝ)) ∩ euclideanSupNormShell N r
      S.Finite ∧ (S.ncard : ℝ) * (2 * d) ^ N ≤ (2 * (r + 1 + d)) ^ N - (2 * (r - d)) ^ N := by
  classical
  obtain ⟨ε, hε, hiso⟩ := Metric.isOpen_iff.mp (isOpen_discrete ({0} : Set Γ)) 0 (by simp)
  let d := min (ε / 2) 1
  have hd : 0 < d := lt_min (by linarith) zero_lt_one
  have hd1 : d ≤ 1 := min_le_right _ _
  have hdε : d + d ≤ ε := by
    have hle := min_le_left (ε / 2) (1 : ℝ)
    dsimp [d]
    linarith
  refine ⟨d, hd, hd1, ?_⟩
  intro r hr S
  have hb : Bornology.IsBounded (euclideanSupNormShell N r) := by
    apply (Metric.isBounded_ball (x := (0 : Fin N → ℝ)) (r := r + 1)).subset
    intro x hx
    simpa only [Metric.mem_ball, dist_zero_right] using hx.2
  have hclosed : IsClosed (Γ : Set (Fin N → ℝ)) := by
    change IsClosed (Γ.toAddSubgroup : Set (Fin N → ℝ))
    exact AddSubgroup.isClosed_of_discreteTopology
  have hfin : S.Finite := by
    simpa [S, inter_comm] using
      Metric.finite_isBounded_inter_isClosed (s := (Γ : Set (Fin N → ℝ)))
        DiscreteTopology.isDiscrete hb hclosed
  refine ⟨hfin, ?_⟩
  let := hfin.fintype
  -- Discreteness at zero gives the same separation for every pair of lattice points.
  let balls := fun x : S => Metric.ball x.val d
  have hdis : Pairwise (Disjoint on balls) := by
    intro x y hne
    apply Metric.ball_disjoint_ball
    apply hdε.trans
    by_contra! h
    let z : Γ := ⟨x.val - y.val, Γ.sub_mem x.property.1 y.property.1⟩
    have hz : z ∈ Metric.ball (0 : Γ) ε := by
      simpa [z, Metric.mem_ball, dist_eq_norm] using h
    have hz0 : z = 0 := hiso hz
    apply hne
    exact Subtype.ext (sub_eq_zero.mp (congrArg Subtype.val hz0))
  have hbvol (x : Fin N → ℝ) {t : ℝ} (ht : 0 < t) :
      volume.real (Metric.ball x t) = (2 * t) ^ N := by
    simp [measureReal_def, Real.volume_pi_ball _ ht, ENNReal.toReal_ofReal (by positivity : 0 ≤ (2 * t) ^ N)]
  have heq : volume.real (⋃ x, balls x) = (S.ncard : ℝ) * (2 * d) ^ N := by
    rw [measureReal_iUnion_fintype hdis (fun _ => Metric.isOpen_ball.measurableSet)
      (fun x => by dsimp [balls]; rw [Real.volume_pi_ball _ hd]; exact ENNReal.ofReal_ne_top)]
    simp only [balls, hbvol _ hd, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have hi : 0 < r - d := by linarith
  have ho : 0 < r + 1 + d := by linarith
  let outer := Metric.ball (0 : Fin N → ℝ) (r + 1 + d)
  let inner := Metric.ball (0 : Fin N → ℝ) (r - d)
  have hout : volume outer ≠ ⊤ := by
    rw [show outer = _ from rfl, Real.volume_pi_ball _ ho]
    exact ENNReal.ofReal_ne_top
  have hio : inner ⊆ outer := Metric.ball_subset_ball (by linarith)
  have hsub : (⋃ x, balls x) ⊆ outer \ inner := by
    intro y hy
    obtain ⟨x, hx⟩ := mem_iUnion.mp hy
    have hdxy : dist y x.val < d := hx
    have hnorm := abs_norm_sub_norm_le y x.val
    rw [← dist_eq_norm] at hnorm
    obtain ⟨h₁, h₂⟩ := abs_le.mp hnorm
    obtain ⟨hrx₁, hrx₂⟩ : r ≤ ‖x.val‖ ∧ ‖x.val‖ < r + 1 := x.property.2
    simp only [outer, inner, Set.mem_sdiff, Metric.mem_ball, dist_zero_right, not_lt]
    constructor <;> linarith
  have hdiff : volume.real (outer \ inner) = volume.real outer - volume.real inner := by
    have := measureReal_inter_add_sdiff (μ := volume) (s := outer)
      (t := inner) Metric.isOpen_ball.measurableSet hout
    rw [inter_eq_right.mpr hio] at this
    linarith
  calc
    _ = volume.real (⋃ x, balls x) := heq.symm
    _ ≤ volume.real (outer \ inner) :=
      measureReal_mono hsub (measure_ne_top_of_subset sdiff_subset hout)
    _ = _ := by rw [hdiff, hbvol _ ho, hbvol _ hi]


/-- A shell of fixed width has volume of order at most the radius to the power N − 1. -/
private theorem shell_pow_diff_bound (N : ℕ) (hN : 1 ≤ N) (d : ℝ)
    (hd : 0 < d) (hd' : d ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 2 ≤ r →
      (2 * (r + 1 + d)) ^ N - (2 * (r - d)) ^ N ≤ C * r ^ (N - 1) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N from hN)
  refine ⟨(2 + 4 * d) * N * 4 ^ (N - 1), by positivity, ?_⟩
  intro r hr
  let a := 2 * (r + 1 + d)
  let b := 2 * (r - d)
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hba : b ≤ a := by dsimp [a, b]; linarith
  have hdiff : a - b = 2 + 4 * d := by dsimp [a, b]; ring
  have htop : a ≤ 4 * r := by dsimp [a]; linarith
  calc
    a ^ N - b ^ N ≤ |a ^ N - b ^ N| := le_abs_self _
    _ ≤ |a - b| * N * max |a| |b| ^ (N - 1) := abs_pow_sub_pow_le a b N
    _ = (2 + 4 * d) * N * a ^ (N - 1) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hba), hdiff, abs_of_nonneg ha, abs_of_nonneg hb, max_eq_left hba]
    _ ≤ (2 + 4 * d) * N * (4 * r) ^ (N - 1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha htop _) (by positivity)
    _ = _ := by rw [mul_pow]; ring

/-- Paper: Lemma 2.2.1.1, p. 75. For large radii, the shell has finitely many
lattice points and their number is at most a constant times `r ^ (N - 1)`. -/
theorem euclideanSupNormShell_lattice_count {N : ℕ} (_hN : 1 ≤ N)
    (Γ : Submodule ℤ (Fin N → ℝ)) [DiscreteTopology Γ] [IsZLattice ℝ Γ] :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ r : ℝ in atTop,
      ((Γ : Set (Fin N → ℝ)) ∩ euclideanSupNormShell N r).Finite ∧
      (((Γ : Set (Fin N → ℝ)) ∩ euclideanSupNormShell N r).ncard : ℝ) ≤
        C * r ^ (N - 1) := by
  obtain ⟨d, hd, hd', hpack⟩ := shell_packing Γ
  obtain ⟨C, hC, hpow⟩ := shell_pow_diff_bound N _hN d hd hd'
  have hvol : 0 < (2 * d) ^ N := by positivity
  refine ⟨C / (2 * d) ^ N, div_pos hC hvol, ?_⟩
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
  obtain ⟨hfinite, hbound⟩ := hpack r hr
  refine ⟨hfinite, ?_⟩
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ hvol).mpr (hbound.trans (hpow r hr))

-- TODO(paper-gap): Proposition 2.2.1.3, p. 76, excludes Γ ∩ K from the sum,
-- but the term with ξ = -x can remain. Take Γ = ℤ, K = {1}, x = 1 and ξ = -1.

end Lattice

section Adelic

variable {F : Type*} [Field F] [NumberField F]

local notation "𝕀[" F "]" => IdeleGroup (𝓞 F) F
local notation "C[" F "]" => IdeleClassGroup (𝓞 F) F
local notation "ℬ[" F "]" => SchwartzBruhat (Multiplicative 𝔸[F])
local notation "normℝ" => fun (g : C[F]) ↦ ((ideleClassNorm F g : ℝ≥0) : ℝ)
local notation "classOf" => QuotientGroup.mk (s := IdeleGroup.principalSubgroup (𝓞 F) F)
local notation "zeroAdele" => Multiplicative.ofAdd (0 : 𝔸[F])

/-- Paper: Lemma 2.2.2.1, p. 77. The average sums the Schwartz–Bruhat function
at the adeles `g * (ξ + x)` as `ξ` ranges over the nonzero field elements. -/
def adelicAverage (f : ℬ[F]) (g : 𝕀[F]) (x : 𝔸[F]) : ℂ :=
  ∑' ξ : Fˣ, f (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] (ξ : F) + x)))

/-- Paper: Lemma 2.2.2.1, p. 77. The series of absolute values of the summands
in the adelic average converges uniformly on every compact set. -/
theorem adelicAverage_summableUniformlyOn (f : ℬ[F])
    (K : Set (𝕀[F] × 𝔸[F])) (hK : IsCompact K) :
    SummableUniformlyOn (fun (ξ : Fˣ) (p : 𝕀[F] × 𝔸[F]) ↦
      ‖f (Multiplicative.ofAdd (p.1.val * (algebraMap F 𝔸[F] (ξ : F) + p.2)))‖) K := by sorry

/-- Paper: Lemma 2.2.2.1(1), p. 77. Adding the term at `ξ = 0` to the adelic
average gives the sum over all field elements. -/
theorem hasSum_adelicAverage_add_zeroTerm (f : ℬ[F]) (g : 𝕀[F]) (x : 𝔸[F]) :
    HasSum (fun ξ : F ↦ f (Multiplicative.ofAdd (g.val * (algebraMap F 𝔸[F] ξ + x))))
      (adelicAverage f g x + f (Multiplicative.ofAdd (g.val * x))) := by sorry

/-- Paper: Lemma 2.2.2.1(1), p. 77. The adelic average is jointly continuous in
the idele and adele arguments. -/
theorem adelicAverage_continuous (f : ℬ[F]) :
    Continuous (uncurry (adelicAverage f)) := by sorry

/-- Paper: Lemma 2.2.2.1(1), p. 77. The sum with the zero term included is
invariant under addition of a diagonal field element to the adele argument. -/
theorem adelicAverage_add_zeroTerm_add_principal (f : ℬ[F]) (g : 𝕀[F]) (x : 𝔸[F]) (a : F) :
    let y := algebraMap F 𝔸[F] a + x
    adelicAverage f g y + f (Multiplicative.ofAdd (g.val * y)) =
      adelicAverage f g x + f (Multiplicative.ofAdd (g.val * x)) := by sorry

/-- Paper: Lemma 2.2.2.1(2), p. 77. The adelic average at `x = 0` is continuous
as a function of the idele. -/
theorem adelicAverage_at_zero_continuous (f : ℬ[F]) :
    Continuous (fun g : 𝕀[F] ↦ adelicAverage f g 0) := by sorry

/-- Paper: Lemma 2.2.2.1(2), p. 77. The adelic average at `x = 0` is invariant
under multiplication by principal ideles.
Deviation: Invariance is expressed as constancy on the fibers of the quotient map. -/
theorem adelicAverage_at_zero_factorsThrough (f : ℬ[F]) :
    FactorsThrough (fun g : 𝕀[F] ↦ adelicAverage f g 0) classOf := by sorry

-- ERRATA I65: With the Archimedean component fixed at one over ℚ, the
-- p-component p^m and test function 1_Ẑ give contributing rationals in
-- p^(-m) ℤ. The full domain below gives a uniform bound on the denominators.

open scoped Pointwise nonZeroDivisors in
/-- Paper: Lemma 2.2.2.1(3), p. 78. For a product of an Archimedean Schwartz
function and local indicators as in (2.2.2.2), a single fractional ideal gives
the summable Archimedean upper bound (2.2.2.3).
Deviation: The whole idele varies over the canonical norm section times the
norm-one fundamental domain used in the proof. -/
theorem adelicAverage_at_zero_le_fractionalIdeal
    (b : Module.Basis (Fin (Units.rank F)) ℤ (Additive ((𝓞 F)ˣ ⧸ Units.torsion F)))
    (v₀ : InfinitePlace F) (σ : ℂ ≃ₐ[ℝ] ℂ)
    (r : CommRing.Pic (𝓞 F) → (ideleNorm F).ker) (hr₁ : r 1 = 1)
    (hr : ∀ c, ideleIdealClass F (r c).val = c)
    (f : ℬ[F]) (arch : SchwartzBruhat (Multiplicative (InfiniteAdeleRing F)))
    (K : (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) → Set (v.adicCompletion F))
    (hK : ∀ v, IsCompact (K v) ∧ IsOpen (K v) ∧
      K v ⊆ (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (hKcofinite : ∀ᶠ v in cofinite, K v = (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    (hf : ∀ x : 𝔸[F], f (Multiplicative.ofAdd x) = arch (Multiplicative.ofAdd x.1) *
      Set.indicator {y : 𝔸ᶠ[F] | ∀ v, y v ∈ K v} (fun _ ↦ (1 : ℂ)) x.2) :
    ∃ I : FractionalIdeal (𝓞 F)⁰ F,
      ∀ g ∈ Set.range (canonicalIdeleNormSection F) *
          ((ideleNorm F).ker.subtype '' ideleFundamentalDomain F b v₀ σ r),
        let term := fun ξ : {ξ : Fˣ // (ξ : F) ∈ I} ↦
          ‖arch (Multiplicative.ofAdd (g.val.1 * algebraMap F (InfiniteAdeleRing F) (ξ.val : F)))‖
        Summable term ∧
          (∑' ξ : Fˣ, ‖f (Multiplicative.ofAdd (g.val * algebraMap F 𝔸[F] (ξ : F)))‖) ≤
            ∑' ξ, term ξ := by sorry

/-- Paper: Definition 2.2.3.1, p. 81. The global adelic theta function descends
the average at `x = 0` to a continuous function on the idele class group. -/
def adelicTheta (f : ℬ[F]) : C(C[F], ℂ) :=
  IsQuotientMap.lift (f := ⟨classOf, QuotientGroup.continuous_mk⟩)
    (QuotientGroup.isQuotientMap_mk (IdeleGroup.principalSubgroup (𝓞 F) F))
    ⟨fun g ↦ adelicAverage f g 0, adelicAverage_at_zero_continuous f⟩
    (adelicAverage_at_zero_factorsThrough f)

/-- Paper: Definition 2.2.3.1, p. 81. At the class of an idele, theta sums
the test function over its nonzero principal multiples. -/
theorem adelicTheta_mk (f : ℬ[F]) (g : 𝕀[F]) :
    adelicTheta f (classOf g) =
      ∑' ξ : Fˣ, f (Multiplicative.ofAdd (algebraMap F 𝔸[F] (ξ : F) * g.val)) := by sorry

/-- Paper: Definition 2.2.3.1, p. 82. Formation of the global adelic theta
function is complex linear. -/
theorem adelicTheta_isLinear : IsLinearMap ℂ (adelicTheta (F := F)) := by sorry

local instance : MeasurableSpace 𝔸[F] := borel _

/-- Paper: Theorem 2.2.3.2, p. 82. The Fourier integral for the standard adelic
character and the additive Tamagawa measure gives a Schwartz–Bruhat function. -/
theorem adeleSchwartzFourier_mem (f : ℬ[F]) :
    (fun y : Multiplicative 𝔸[F] ↦ tamagawaFourier (additiveTamagawaMeasure F)
      (adeleStandardCharacter F) (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd) ∈
      schwartzBruhatSubmodule (Multiplicative 𝔸[F]) := by sorry

/-- Paper: Theorem 2.2.3.2, p. 82. The Fourier transform in the theta identity
uses the trace character and the covolume-one measure of Appendix A. -/
def adeleSchwartzFourier (f : ℬ[F]) : ℬ[F] :=
  ⟨fun y ↦ tamagawaFourier (additiveTamagawaMeasure F) (adeleStandardCharacter F)
    (fun x ↦ f (Multiplicative.ofAdd x)) y.toAdd, adeleSchwartzFourier_mem f⟩

/-- Paper: Theorem 2.2.3.2, p. 82. The value of the Fourier transform at zero
is the integral of the Schwartz–Bruhat function, which is integrable. -/
theorem adeleSchwartzFourier_apply_zero (f : ℬ[F]) :
    Integrable (fun x ↦ f (Multiplicative.ofAdd x)) (additiveTamagawaMeasure F) ∧
    adeleSchwartzFourier f zeroAdele =
      ∫ x, f (Multiplicative.ofAdd x) ∂additiveTamagawaMeasure F := by sorry

/-- Paper: Theorem 2.2.3.2, p. 82. Adelic Riemann–Roch relates theta at an idele
class to the Fourier-transformed theta at its inverse, including the two zero terms. -/
theorem adelicTheta_riemannRoch (f : ℬ[F]) (g : C[F]) :
    adelicTheta f g = (normℝ g)⁻¹ • adelicTheta (adeleSchwartzFourier f) g⁻¹ +
      (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele - f zeroAdele := by sorry

/-- Paper: Theorem 2.2.3.4(1), p. 83. Theta decays faster than any inverse
power of the idele class norm as that norm tends to infinity. -/
theorem adelicTheta_decay_large (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < normℝ g →
      ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹ := by sorry

/-- Paper: Theorem 2.2.3.4(2), p. 83. After subtracting the explicit polar
terms, theta decays faster than any power of the norm as it tends to zero. -/
theorem adelicTheta_decay_small (f : ℬ[F]) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], normℝ g < T →
      ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
        C * (normℝ g) ^ N := by sorry

/-- Paper: Theorem 2.2.3.4(3), p. 83. If both zero terms vanish, theta
decays at both ends at every exponential rate in the absolute logarithmic norm. -/
theorem adelicTheta_decay_both (f : ℬ[F]) (hf : f zeroAdele = 0)
    (hFourier : adeleSchwartzFourier f zeroAdele = 0) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ g : C[F], T < |Real.log (normℝ g)| →
      ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|) := by sorry

/-- Paper: Theorem 2.2.3.4(4), p. 83. The three decay estimates admit a common
constant and threshold uniform over a bounded set of Schwartz–Bruhat functions.
The two-sided estimate applies to members whose two zero terms vanish. -/
theorem adelicTheta_decay_bounded (B : Set ℬ[F]) (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C T : ℝ, 0 < C ∧ 0 < T ∧ ∀ f ∈ B, ∀ g : C[F],
      (T < normℝ g → ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (normℝ g < T →
        ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
          C * (normℝ g) ^ N) ∧
      (f zeroAdele = 0 → adeleSchwartzFourier f zeroAdele = 0 →
        Real.exp (-|Real.log (normℝ g)|) < T →
        ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) := by sorry

/-- Paper: Theorem 2.2.3.4(5), p. 83. The uniform estimates on a bounded set
hold with threshold one and a common constant. -/
theorem adelicTheta_decay_bounded_threshold_one (B : Set ℬ[F])
    (hB : IsVonNBounded ℂ B) (N : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f ∈ B, ∀ g : C[F],
      (1 < normℝ g → ‖adelicTheta f g‖ ≤ C * ((normℝ g) ^ N)⁻¹) ∧
      (normℝ g < 1 →
        ‖adelicTheta f g - (normℝ g)⁻¹ • adeleSchwartzFourier f zeroAdele + f zeroAdele‖ ≤
          C * (normℝ g) ^ N) ∧
      (f zeroAdele = 0 → adeleSchwartzFourier f zeroAdele = 0 →
        Real.exp (-|Real.log (normℝ g)|) < 1 →
        ‖adelicTheta f g‖ ≤ C * Real.exp (-(N : ℝ) * |Real.log (normℝ g)|)) := by sorry

end Adelic

end RiemannMasullo
