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

private def insertIndex {T : Finset V} (v : V) (kn : ℕ × (T → ℕ))
    (w : ↥(insert v T : Finset V)) : ℕ :=
  if hw : w.val ∈ T then kn.2 ⟨w.val, hw⟩ else kn.1

private def insertIndexEquiv {T : Finset V} (v : V) (hv : v ∉ T) :
    (ℕ × (T → ℕ)) ≃ (↥(insert v T : Finset V) → ℕ) where
  toFun := insertIndex v
  invFun n := (n ⟨v, Finset.mem_insert_self _ _⟩, fun w ↦ n ⟨w.val, Finset.mem_insert_of_mem w.property⟩)
  left_inv kn := by
    apply Prod.ext
    · simp [insertIndex, hv]
    · funext w
      simp [insertIndex, w.property]
  right_inv n := by
    funext w
    by_cases hw : w.val ∈ T
    · simp [insertIndex, hw]
    · have he : w.val = v := (Finset.mem_insert.mp w.property).resolve_right hw
      have he' : w = (⟨v, Finset.mem_insert_self _ _⟩ : ↥(insert v T : Finset V)) := Subtype.ext he
      rw [he']
      simp [insertIndex, hv]

private theorem latticeRadius_insertIndex {T : Finset V} (v : V) (hv : v ∉ T)
    (kn : ℕ × (T → ℕ)) :
    latticeRadius (insertIndexEquiv v hv kn) = (v.asIdeal.absNorm : ℝ)^kn.1 * latticeRadius kn.2 := by
  let E := Finset.subtypeInsertEquivOption hv
  let G : Option T → ℝ := Option.rec ((v.asIdeal.absNorm : ℝ)^kn.1)
    (fun w : T ↦ (w.val.asIdeal.absNorm : ℝ) ^ kn.2 w)
  calc
    _ = ∏ o : Option T, G o := by
      apply Fintype.prod_equiv E
      intro w
      obtain ⟨o, rfl⟩ := E.symm.surjective w
      rw [Equiv.apply_symm_apply]
      cases o with
      | none => simp [G, E, Finset.subtypeInsertEquivOption, insertIndexEquiv, insertIndex, hv]
      | some u => simp [G, E, Finset.subtypeInsertEquivOption, insertIndexEquiv, insertIndex, u.property]
    _ = _ := Fintype.prod_option G

include hf in
private theorem theta_hasSum_rows (T : Finset V) (v : V) (hv : v ∉ T)
    (x : (SAdeleRing ℚ (insert v T))ˣ) (hx : Normalized (insert v T) x) :
    HasSum (fun k : ℕ ↦ ∑' n : T → ℕ,
      signedProfile phi (radius (insert v T) x * ((v.asIdeal.absNorm : ℝ)^k * latticeRadius n)))
      (theta (insert v T) f x) := by
  have h := (insertIndexEquiv v hv).hasSum_iff.mpr (normChart_hasSum f phi hf (insert v T) x hx)
  have he : HasSum (fun kn : ℕ × (T → ℕ) ↦ signedProfile phi
      (radius (insert v T) x * ((v.asIdeal.absNorm : ℝ)^kn.1 * latticeRadius kn.2)))
      (theta (insert v T) f x) :=
    h.congr_fun (fun kn ↦ by simp only [Function.comp_apply, latticeRadius_insertIndex])
  refine he.prod_fiberwise fun k ↦ ?_
  exact (he.summable.comp_injective (i := fun n : T → ℕ ↦ (k, n))
    (fun _ _ e ↦ congrArg Prod.snd e)).hasSum

include hf in
/-- The exact finite-place Euler difference at the actual chart radii `r` and
`q*r` gives the genuine smaller-stage half-theta at `r`. The identity holds for
any finite set of retained places and all normalized representatives. -/
theorem insert_euler_eq_halfTheta (T : Finset V) (v : V) (hv : v ∉ T)
    (x y : (SAdeleRing ℚ (insert v T))ˣ) (z : (SAdeleRing ℚ T)ˣ)
    (hx : Normalized (insert v T) x) (hy : Normalized (insert v T) y) (hz : Normalized T z)
    (hshift : radius (insert v T) y = radius (insert v T) x * (v.asIdeal.absNorm : ℝ))
    (hsame : radius T z = radius (insert v T) x) :
    halfTheta (insert v T) f x - (Real.sqrt (v.asIdeal.absNorm : ℝ) : ℂ)⁻¹ *
      halfTheta (insert v T) f y = halfTheta T f z := by
  let rr := radius (insert v T) x
  let q : ℝ := v.asIdeal.absNorm
  let b (k : ℕ) := ∑' n : T → ℕ, signedProfile phi (rr * (q^k * latticeRadius n))
  have hs : HasSum b (theta (insert v T) f x) := theta_hasSum_rows f phi hf T v hv x hx
  have hs' := (hasSum_nat_add_iff' 1).mpr hs
  rw [Finset.sum_range_one] at hs'
  have h0 : b 0 = theta T f z := by
    rw [← (normChart_hasSum f phi hf T z hz).tsum_eq, hsame]
    simp only [b, rr, pow_zero, one_mul]
  have ht : HasSum (fun k ↦ b (k+1)) (theta (insert v T) f y) := by
    refine (theta_hasSum_rows f phi hf T v hv y hy).congr_fun fun k ↦ ?_
    change b (k + 1) = ∑' n : T → ℕ, signedProfile phi
      (radius (insert v T) y * (q^k * latticeRadius n))
    apply tsum_congr
    intro n
    rw [hshift, pow_succ]
    congr 1
    dsimp only [rr, q]
    ring
  have he := hs'.unique ht
  rw [h0] at he
  have hr : 0 ≤ rr := NNReal.coe_nonneg _
  have hq : 0 < q := Nat.cast_pos.mpr (zero_lt_one.trans (HeightOneSpectrum.one_lt_absNorm v))
  have hn : (Real.sqrt q : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  rw [halfTheta, halfTheta, halfTheta, hshift, hsame]
  change (Real.sqrt rr : ℂ) * theta (insert v T) f x - (Real.sqrt q : ℂ)⁻¹ *
    ((Real.sqrt (rr * q) : ℂ) * theta (insert v T) f y) = (Real.sqrt rr : ℂ) * theta T f z
  rw [Real.sqrt_mul hr, Complex.ofReal_mul, ← he]
  field_simp; ring

end RiemannMasullo.RatActualThetaEulerPointwise
