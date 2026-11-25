module

public import RiemannMasullo.Ch06_LocalGlobal.Sec2_RatUnramifiedThetaLattice

/-! Pointwise Euler cancellation for actual normalized rational standard tensors.
The indexing cone consists of products of the selected prime powers, not the
integers coprime to their product. -/

public noncomputable section
namespace RiemannMasullo.RatActualThetaEulerPointwise
open NumberField IsDedekindDomain RatFinitePositiveUnitRep RatUnramifiedThetaLattice
open scoped Classical NumberField.AdeleRing

local notation "V" => HeightOneSpectrum (𝓞 ℚ)
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "rc" => InfinitePlace.Completion.extensionEmbeddingOfIsReal Rat.isReal_infinitePlace

abbrev radius (S : Finset V) (x : (SAdeleRing ℚ S)ˣ) : ℝ := ((sIdeleNorm ℚ S x).val : ℝ)

abbrev theta (S : Finset V) (f : B∞) (x : (SAdeleRing ℚ S)ˣ) : ℂ :=
  sLocalAdelicThetaOnClasses ℚ S (sLocalStandardThetaTensor 1 f) (QuotientGroup.mk x)

def signedProfile (phi : ℝ → ℂ) (r : ℝ) := phi r + phi (-r)

def halfProfile (phi : ℝ → ℂ) (r : ℝ) := (Real.sqrt r : ℂ) * signedProfile phi r

def halfTheta (S : Finset V) (f : B∞) (x : (SAdeleRing ℚ S)ˣ) :=
  (Real.sqrt (radius S x) : ℂ) * theta S f x

variable (f : B∞) (phi : ℝ → ℂ)
  (hf : ∀ a : InfiniteAdeleRing ℚ, f (Multiplicative.ofAdd a) = phi (rc (a Rat.infinitePlace)))

include hf in
private theorem normChart_hasSum (S : Finset V) (x : (SAdeleRing ℚ S)ˣ) (hx : Normalized S x) :
    HasSum (fun n : S → ℕ ↦ signedProfile phi (radius S x * latticeRadius n)) (theta S f x) := by
  simpa only [norm_normalized S hx, signedProfile, theta, radius] using
    actual_unramified_theta_hasSum S f phi hf x hx

include hf in
/-- The half-twist conjugates every dilation by the inverse square root of its radius. -/
theorem halfTheta_lattice_hasSum (S : Finset V) (x : (SAdeleRing ℚ S)ˣ) (hx : Normalized S x) :
    HasSum (fun n : S → ℕ ↦ (Real.sqrt (latticeRadius n) : ℂ)⁻¹ *
      halfProfile phi (radius S x * latticeRadius n)) (halfTheta S f x) := by
  refine ((normChart_hasSum f phi hf S x hx).mul_left (Real.sqrt (radius S x) : ℂ)).congr_fun ?_
  intro n
  have hr : 0 ≤ radius S x := NNReal.coe_nonneg _
  have hL : 0 < latticeRadius n := Finset.prod_pos fun v _ ↦ pow_pos
    (Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v.val))) _
  have hn : (Real.sqrt (latticeRadius n) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hL).ne'
  simp only [halfProfile, Real.sqrt_mul hr, Complex.ofReal_mul]
  field_simp

include hf in
private theorem singleton_hasSum (v : V) (x : (SAdeleRing ℚ {v})ˣ) (hx : Normalized {v} x) :
    HasSum (fun k : ℕ ↦ signedProfile phi (radius {v} x * (v.asIdeal.absNorm : ℝ)^k))
      (theta {v} f x) := by
  classical
  let v₀ : ({v} : Finset V) := ⟨v, Finset.mem_singleton_self _⟩
  let e : ℕ ≃ (({v} : Finset V) → ℕ) :=
    { toFun := fun k _ ↦ k
      invFun := fun n ↦ n v₀
      left_inv := fun _ ↦ rfl
      right_inv := fun n ↦ funext fun w ↦ congrArg n (Subtype.ext (Finset.mem_singleton.mp w.property).symm) }
  let : Subsingleton ↥({v} : Finset V) := ⟨fun a b ↦ Subtype.ext
    ((Finset.mem_singleton.mp a.property).trans (Finset.mem_singleton.mp b.property).symm)⟩
  have h := e.hasSum_iff.mpr (normChart_hasSum f phi hf {v} x hx)
  refine h.congr_fun fun k ↦ ?_
  change _ = signedProfile phi (radius {v} x * latticeRadius (e k))
  unfold latticeRadius
  rw [Fintype.prod_subsingleton _ v₀]
  rfl

include hf in
private theorem empty_theta (x : (SAdeleRing ℚ ∅)ˣ) (hx : Normalized ∅ x) :
    theta ∅ f x = signedProfile phi (radius ∅ x) := by
  classical
  rw [← (normChart_hasSum f phi hf ∅ x hx).tsum_eq, tsum_eq_single (0 : (∅ : Finset V) → ℕ)]
  · simp [latticeRadius]
  · intro n hn
    exact (hn (funext fun v ↦ (Finset.notMem_empty _ v.property).elim)).elim

include hf in
/-- At positive norm `r`, the singleton series minus its `q*r` tail leaves exactly
its zero exponent. Both evaluations use actual normalized representatives. -/
theorem singleton_euler_difference (v : V) (x y : (SAdeleRing ℚ {v})ˣ)
    (hx : Normalized {v} x) (hy : Normalized {v} y)
    (hshift : radius {v} y = radius {v} x * (v.asIdeal.absNorm : ℝ)) :
    halfTheta {v} f x - (Real.sqrt (v.asIdeal.absNorm : ℝ) : ℂ)⁻¹ * halfTheta {v} f y =
      halfProfile phi (radius {v} x) := by
  have ht := (hasSum_nat_add_iff' 1).mpr (singleton_hasSum f phi hf v x hx)
  simp only [Finset.sum_range_one, pow_zero, mul_one, pow_succ] at ht
  have hy' := singleton_hasSum f phi hf v y hy
  rw [hshift] at hy'
  have he : theta {v} f x - signedProfile phi (radius {v} x) = theta {v} f y := by
    apply ht.unique
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hy'
  have hr : 0 ≤ radius {v} x := NNReal.coe_nonneg _
  have hq : 0 < (v.asIdeal.absNorm : ℝ) := Nat.cast_pos.mpr
    (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hn : (Real.sqrt (v.asIdeal.absNorm : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  rw [halfTheta, halfTheta, halfProfile, hshift, Real.sqrt_mul hr, Complex.ofReal_mul, ← he]
  field_simp; ring

include hf in
/-- The surviving term is the true empty-stage half-twisted theta at the same norm. -/
theorem singleton_euler_eq_emptyTheta (v : V) (x y : (SAdeleRing ℚ {v})ˣ)
    (z : (SAdeleRing ℚ ∅)ˣ) (hx : Normalized {v} x) (hy : Normalized {v} y)
    (hz : Normalized ∅ z) (hshift : radius {v} y = radius {v} x * (v.asIdeal.absNorm : ℝ))
    (hsame : radius ∅ z = radius {v} x) :
    halfTheta {v} f x - (Real.sqrt (v.asIdeal.absNorm : ℝ) : ℂ)⁻¹ * halfTheta {v} f y =
      halfTheta ∅ f z := by
  rw [singleton_euler_difference f phi hf v x y hx hy hshift, halfTheta,
    empty_theta f phi hf z hz, hsame, halfProfile]

end RiemannMasullo.RatActualThetaEulerPointwise
