module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Data.Finset.NatDivisors
public import Mathlib.Data.Set.Card
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Algebra.InfiniteSum.Defs

/-!
# §§14.2–14.3: Global function fields and higher rank

Masullo, pp. 534–536. The Euler product (14.2.0.1) uses every closed point of
the smooth projective curve, including those above infinity for a map to the
projective line.
-/

@[expose] public section

namespace RiemannMasullo

open AlgebraicGeometry CategoryTheory

universe u

variable {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}

/-- Paper: (14.2.0.1), p. 534. The local factor at a closed point, in the
complex parameter on the covering plane. -/
noncomputable def curveZetaEulerFactor (x : closedPoints X) (s : ℂ) : ℂ :=
  (1 - (Nat.card (X.residueField x.val) : ℂ) ^ (-s))⁻¹

/-- Paper: (14.2.0.1), p. 534. The zeta Euler product of a smooth projective
geometrically connected curve over a finite field multiplies the reciprocal
factors determined by the sizes of the residue fields of its closed points.
Deviation: The product is defined on `Re(s) > 1`, its half-plane of absolute
convergence. A smooth proper curve over a field is projective. -/
noncomputable def curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) : ℂ :=
  ∏' x : closedPoints X, curveZetaEulerFactor x s.val

/-- Paper: (14.2.0.1), p. 534. On `Re(s) > 1` the finite products over closed
points converge to the zeta Euler product.
Deviation: `HasProd` asserts convergence of the product in the display. -/
theorem hasProd_curveZetaEulerProduct (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    HasProd (fun x : closedPoints X ↦ curveZetaEulerFactor x s.val)
      (curveZetaEulerProduct f s) := by sorry

/-- Paper: (14.2.0.1), p. 534. The product converges absolutely on its
half-plane of definition. -/
theorem summable_curveZetaEulerFactor_sub_one (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (s : {s : ℂ // 1 < s.re}) :
    Summable (fun x : closedPoints X ↦ ‖curveZetaEulerFactor x s.val - 1‖) := by sorry

/-- The order of `exp w - 1` at a point where `exp w = 1` is `1`. -/
private lemma meromorphicOrderAt_exp_sub_one (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => Complex.exp s - 1) w = 1 := by
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ) (f := fun x : ℂ => x)
    (g := fun s : ℂ => Complex.exp s - 1) (x := w)
    (analyticAt_cexp.sub analyticAt_const) (by simp [Complex.deriv_exp, hw])
  simp only [Function.comp_def] at hcomp
  rw [hcomp, show Complex.exp w - 1 = 0 from by rw [hw]; ring]
  exact meromorphicOrderAt_id (𝕜 := ℂ)

/-- The order of `1 - exp w` at a point where `exp w = 1` is `1`. -/
private lemma meromorphicOrderAt_one_sub_exp (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => 1 - Complex.exp s) w = 1 := by
  have h := meromorphicOrderAt_exp_sub_one w hw
  have hneg : meromorphicOrderAt (fun s : ℂ => -(Complex.exp s - 1)) w = 1 := by
    rw [← meromorphicOrderAt_fun_neg (f := fun s : ℂ => Complex.exp s - 1) (x := w)]
    exact h
  rw [show (fun s : ℂ => 1 - Complex.exp s) = fun s : ℂ => -(Complex.exp s - 1) from by
    funext s; ring]
  exact hneg

/-- The reciprocal local factor `(1 - exp w)⁻¹` has a simple pole at `w`. -/
private lemma meromorphicOrderAt_one_sub_exp_inv (w : ℂ) (hw : Complex.exp w = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - Complex.exp s)⁻¹) w = -1 := by
  have h := meromorphicOrderAt_one_sub_exp w hw
  have hfun : (fun s : ℂ => (1 - Complex.exp s)⁻¹) = (fun s : ℂ => 1 - Complex.exp s)⁻¹ := rfl
  rw [hfun, meromorphicOrderAt_inv, h]

/-- Composing with the affine substitution `s ↦ -(s * L)` (`L ≠ 0`) transports the pole. -/
private lemma meromorphicOrderAt_one_sub_exp_inv_affine (L : ℝ) (hL : L ≠ 0) (z : ℂ)
    (hz : Complex.exp (-(z * (L : ℂ))) = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - Complex.exp (-(s * (L : ℂ))))⁻¹) z = -1 := by
  have h := meromorphicOrderAt_comp_of_deriv_ne_zero (𝕜 := ℂ)
    (f := fun s : ℂ => (1 - Complex.exp s)⁻¹) (g := fun s : ℂ => -(s * (L : ℂ))) (x := z)
    (by fun_prop) (by simp [hL])
  simp only [Function.comp_def] at h
  rw [h]
  exact meromorphicOrderAt_one_sub_exp_inv _ hz

/-- The complex power of a positive natural number, written through the exponential. -/
private lemma natCast_cpow_eq_exp (c : ℕ) (hc : c ≠ 0) (z : ℂ) :
    (c : ℂ) ^ (-z) = Complex.exp (-(z * (Real.log c : ℂ))) := by
  have hc0 : (c : ℂ) ≠ 0 := by simpa using hc
  rw [Complex.cpow_def_of_ne_zero hc0, Complex.natCast_log]
  ring_nf

/-- A single local factor `(1 - c ^ (-s))⁻¹` with `c ≥ 2` has a simple pole at every `z`
where `c ^ (-z) = 1`. -/
private lemma meromorphicOrderAt_cpow_factor (c : ℕ) (hc : 2 ≤ c) (z : ℂ)
    (hz : (c : ℂ) ^ (-z) = 1) :
    meromorphicOrderAt (fun s : ℂ => (1 - (c : ℂ) ^ (-s))⁻¹) z = -1 := by
  have hc0 : c ≠ 0 := by omega
  have hL : Real.log c ≠ 0 := by
    have h1 : (1 : ℝ) < c := by exact_mod_cast hc
    exact ne_of_gt (Real.log_pos h1)
  have hz' : Complex.exp (-(z * (Real.log c : ℂ))) = 1 := by
    rw [← natCast_cpow_eq_exp c hc0 z]
    exact hz
  have hfun : (fun s : ℂ => (1 - (c : ℂ) ^ (-s))⁻¹) =
      fun s : ℂ => (1 - Complex.exp (-(s * (Real.log c : ℂ))))⁻¹ := by
    funext s
    rw [natCast_cpow_eq_exp c hc0 s]
  rw [hfun]
  exact meromorphicOrderAt_one_sub_exp_inv_affine _ hL z hz'

/-- The residue field of a closed point of a curve over a finite field is a finite extension
of the base field, so its cardinality is a positive power of `Nat.card k`. -/
private theorem closedPoint_residueField_card_pow (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] {x : X} (hx : x ∈ closedPoints X) :
    ∃ m : ℕ, 1 ≤ m ∧ Nat.card (X.residueField x) = Nat.card k ^ m := by
  haveI : Smooth f := SmoothOfRelativeDimension.smooth (f := f) (n := 1)
  haveI : LocallyOfFiniteType f := inferInstance
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  have hclosed : IsClosed ({x} : Set X) := hx
  have h1 : LocallyOfFiniteType (X.fromSpecResidueField x) :=
    (isClosed_singleton_iff_locallyOfFiniteType (X := X)).mp hclosed
  have h2 : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  obtain ⟨φ, hφ⟩ := Spec.homEquiv.symm.surjective (X.fromSpecResidueField x ≫ f)
  have h2' : LocallyOfFiniteType (Spec.homEquiv.symm φ) := hφ ▸ h2
  have h3 : RingHom.FiniteType φ.hom := HasRingHomProperty.Spec_iff.mp h2'
  algebraize [φ.hom]
  haveI : Algebra.FiniteType k (X.residueField x) := h3
  haveI : Module.Finite k (X.residueField x) :=
    finite_of_finite_type_of_isJacobsonRing k (X.residueField x)
  haveI : Finite (X.residueField x) := Module.finite_of_finite k (M := X.residueField x)
  have hcard : Nat.card (X.residueField x) = Nat.card k ^ Module.finrank k (X.residueField x) :=
    Module.natCard_eq_pow_finrank (K := k) (V := X.residueField x)
  refine ⟨Module.finrank k (X.residueField x), ?_, hcard⟩
  haveI : Fintype k := Fintype.ofFinite k
  haveI : Fintype (X.residueField x) := Fintype.ofFinite _
  have hq : 2 ≤ Nat.card k := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  have hc : 2 ≤ Nat.card (X.residueField x) := by
    rw [Nat.card_eq_fintype_card]; exact Fintype.one_lt_card
  by_contra hlt
  have h0 : Module.finrank k (X.residueField x) = 0 := by omega
  rw [h0, pow_zero] at hcard
  omega

/-- Paper: §14.2, p. 534. For a finite set of closed points every local
factor has a simple pole at each integral multiple of the imaginary period.
The product has pole order equal to the number of places. -/
theorem curveZetaEulerFactor_prod_order (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (S : Finset (closedPoints X)) (n : ℤ) :
    meromorphicOrderAt (fun s : ℂ ↦ ∏ x ∈ S, curveZetaEulerFactor x s)
      (2 * Real.pi * Complex.I * n / Real.log (Nat.card k)) = -(S.card : ℤ) := by
  have hq : 2 ≤ Nat.card k := by
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hlogk : Real.log (Nat.card k) ≠ 0 := by
    have h1 : (1 : ℝ) < Nat.card k := by exact_mod_cast hq
    exact ne_of_gt (Real.log_pos h1)
  set s0 : ℂ := 2 * Real.pi * Complex.I * n / Real.log (Nat.card k) with hs0
  have hkey : ∀ x ∈ S, meromorphicOrderAt (curveZetaEulerFactor x) s0 = -1 := by
    intro x _
    obtain ⟨m, hm1, hm⟩ := closedPoint_residueField_card_pow f x.2
    have hc2 : 2 ≤ Nat.card (X.residueField x.val) := by
      rw [hm]
      exact le_trans hq (le_self_pow (by omega) (by omega))
    have hval : (Nat.card (X.residueField x.val) : ℂ) ^ (-s0) = 1 := by
      have hc0 : Nat.card (X.residueField x.val) ≠ 0 := by omega
      have hlogc : Real.log (Nat.card (X.residueField x.val)) =
          (m : ℝ) * Real.log (Nat.card k) := by
        rw [hm, Nat.cast_pow, Real.log_pow]
      rw [natCast_cpow_eq_exp _ hc0, hlogc, hs0]
      push_cast
      have hlk : Complex.log ((Nat.card k : ℕ) : ℂ) ≠ 0 := by
        rw [← Complex.natCast_log]
        exact_mod_cast hlogk
      have harg : -((2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) / Complex.log ((Nat.card k : ℕ) : ℂ)) *
            ((m : ℂ) * Complex.log ((Nat.card k : ℕ) : ℂ))) =
          ((-(n * (m : ℤ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
        field_simp
        push_cast
        ring
      rw [harg]
      simpa using Complex.exp_int_mul_two_pi_mul_I (-(n * (m : ℤ)))
    exact meromorphicOrderAt_cpow_factor _ hc2 s0 hval
  rw [meromorphicOrderAt_fun_prod fun x hx =>
    meromorphicAt_of_meromorphicOrderAt_ne_zero (by rw [hkey x hx]; norm_num)]
  rw [Finset.sum_congr rfl hkey, Finset.sum_const]
  norm_num

-- TODO(paper-gap): Page 534 does not construct the function-field Sobolev
-- quotient or show that the trace approximation requires one Mellin test to
-- cancel all finite-stage poles. Under T = q^(-s) these lifts give one point.

/-- A finitely generated algebra over a finite ring has finitely many ring homs into a
finite field. -/
private theorem finite_ringHom_of_adjoin {R A K : Type u} [CommSemiring R] [Finite R]
    [CommRing A] [Algebra R A] [Field K] [Finite K]
    (s : Finset A) (hs : Algebra.adjoin R (s : Set A) = ⊤) : Finite (A →+* K) := by
  refine Finite.of_injective
    (fun φ : A →+* K => (fun r : R => φ (algebraMap R A r), fun a : s => φ a)) ?_
  intro φ ψ h
  simp only [Prod.mk.injEq, funext_iff] at h
  obtain ⟨h1, h2⟩ := h
  have key : ∀ a, a ∈ Algebra.adjoin R (s : Set A) → φ a = ψ a := by
    intro a ha
    refine Algebra.adjoin_induction (p := fun a _ => φ a = ψ a) ?_ ?_ ?_ ?_ ha
    · intro x hx
      exact h2 ⟨x, hx⟩
    · intro r
      exact h1 r
    · intro x y _ _ ihx ihy
      rw [map_add, map_add, ihx, ihy]
    · intro x y _ _ ihx ihy
      rw [map_mul, map_mul, ihx, ihy]
  exact RingHom.ext fun a => key a (hs ▸ Algebra.mem_top)

/-- Morphisms from the spectrum of a finite field into an affine open of a scheme locally of
finite type over a finite field are finite in number. -/
private theorem finite_spec_hom_affineOpen (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    (K : Type u) [Field K] [Finite K] (U : X.Opens) (hU : IsAffineOpen U) :
    Finite (Spec (.of K) ⟶ ↑U) := by
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (.of k)).Opens) := by simp
  let g : Γ(Spec (.of k), ⊤) →+* Γ(X, U) := (Scheme.Hom.appLE f ⊤ U hle).hom
  have hg : g.FiniteType :=
    LocallyOfFiniteType.finiteType_appLE f (isAffineOpen_top _) hU hle
  haveI : Finite Γ(Spec (.of k), ⊤) :=
    Finite.of_injective
      ((Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv : Γ(Spec (.of k), ⊤) → k)
      (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.injective
  have hAfin : Finite (Γ(X, U) →+* K) := by
    letI := g.toAlgebra
    obtain ⟨s, hs⟩ := hg.out
    exact finite_ringHom_of_adjoin s hs
  have h1 : Finite (Spec (.of K) ⟶ Spec (Γ(X, U))) := by
    have h2 : Finite (CommRingCat.of (Γ(X, U)) ⟶ CommRingCat.of K) :=
      Finite.of_injective (fun f => f.hom) (fun f g' h => CommRingCat.Hom.ext h)
    exact Finite.of_injective (fun φ => Spec.homEquiv φ) Spec.homEquiv.injective
  exact Finite.of_injective (fun φ : Spec (.of K) ⟶ ↑U => φ ≫ hU.isoSpec.hom)
    (fun φ ψ h => by
      have := congrArg (fun t => t ≫ hU.isoSpec.inv) h
      simpa [Category.assoc] using this)

/-- A scheme locally of finite type and quasi-compact over a finite field has finitely many
points with values in any fixed finite field. -/
private theorem finite_spec_hom (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    (K : Type u) [Field K] [Finite K] : Finite (Spec (.of K) ⟶ X) := by
  classical
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have hpick : ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) := by
    intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨U, hU⟩, hx⟩
  choose U hU using hpick
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (s := Set.univ)
    (U := fun x : X => (U x : Set X)) (fun x => (U x : X.Opens).isOpen)
    (fun y _ => Set.mem_iUnion.mpr ⟨y, hU y⟩)
  have hcover : ∀ y : X, ∃ x : X, x ∈ t ∧ y ∈ (U x : X.Opens) := by
    intro y
    have h := ht (Set.mem_univ y)
    simpa using h
  haveI hpiece : ∀ x : X, Finite (Spec (.of K) ⟶ ↑(U x : X.Opens)) :=
    fun x => finite_spec_hom_affineOpen f K (U x : X.Opens) (U x).2
  let pt : Spec (.of K) := IsLocalRing.closedPoint K
  haveI : Unique ↥(Spec (.of K)) := inferInstance
  have key : ∀ h : Spec (.of K) ⟶ X,
      ∃ (i : t) (h' : Spec (.of K) ⟶ ↑(U (i : X) : X.Opens)),
        h' ≫ (U (i : X) : X.Opens).ι = h := by
    intro h
    obtain ⟨x, hx, hmem⟩ := hcover (h pt)
    have hrange : Set.range ⇑h ⊆ Set.range ⇑(U x : X.Opens).ι := by
      rw [Scheme.Opens.range_ι]
      intro y hy
      obtain ⟨z, rfl⟩ := hy
      rw [Subsingleton.elim z pt]
      exact hmem
    exact ⟨⟨x, hx⟩, IsOpenImmersion.lift (U x : X.Opens).ι h hrange,
      IsOpenImmersion.lift_fac (U x : X.Opens).ι h hrange⟩
  let F : (Spec (.of K) ⟶ X) → Σ i : t, (Spec (.of K) ⟶ ↑(U (i : X) : X.Opens)) :=
    fun h => ⟨(key h).choose, (key h).choose_spec.choose⟩
  have Ffac : ∀ h, (F h).2 ≫ (U ((F h).1 : X) : X.Opens).ι = h :=
    fun h => (key h).choose_spec.choose_spec
  refine Finite.of_injective F ?_
  intro a b hab
  have h1 := Ffac a
  have h2 := Ffac b
  rw [hab] at h1
  exact h1.symm.trans h2

/-- Paper: §14.2, last paragraph, p. 534. For each degree there are finitely
many closed points whose residue field has that degree over the base field.
Deviation: Page 534 says that the factors repeat "infinitely many times". The
number at each fixed degree is finite, and p. 535 estimates it; it grows as the
degree tends to infinity. -/
theorem curveZeta_closedPointsOfDegree_finite (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) :
    {x : X | x ∈ closedPoints X ∧
      Nat.card (X.residueField x) = Nat.card k ^ m}.Finite := by
  classical
  have hq : 2 ≤ Nat.card k := by
    haveI : Fintype k := Fintype.ofFinite k
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  rcases m with _ | m
  · have hempty : {x : X | x ∈ closedPoints X ∧
        Nat.card (X.residueField x) = Nat.card k ^ 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro hx hc
      obtain ⟨n, hn, hncard⟩ := closedPoint_residueField_card_pow f hx
      have h2 : 2 ≤ Nat.card (X.residueField x) := by
        rw [hncard]
        exact le_trans hq (le_self_pow (by omega) (by omega))
      rw [pow_zero] at hc
      omega
    rw [hempty]
    exact Set.finite_empty
  · set S : Set X := {x : X | x ∈ closedPoints X ∧
      Nat.card (X.residueField x) = Nat.card k ^ (m + 1)} with hSdef
    rcases S.eq_empty_or_nonempty with hempty | ⟨x₀, hx₀⟩
    · rw [hempty]
      exact Set.finite_empty
    · rw [hSdef] at hx₀
      obtain ⟨hx₀cl, hx₀card⟩ := hx₀
      have hK0 : Nat.card (X.residueField x₀) ≠ 0 := by
        rw [hx₀card]
        exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
      haveI : Finite (X.residueField x₀) := (Nat.card_ne_zero.mp hK0).2
      haveI : Fintype (X.residueField x₀) := Fintype.ofFinite _
      haveI : QuasiCompact f := inferInstance
      haveI : Finite (Spec (.of (↥(X.residueField x₀))) ⟶ X) :=
        finite_spec_hom f (↥(X.residueField x₀))
      let pt : ↥(Spec (.of (↥(X.residueField x₀)))) := default
      have hsub : S ⊆ Set.range (fun h : Spec (.of (↥(X.residueField x₀))) ⟶ X => h pt) := by
        intro x hx
        rw [hSdef] at hx
        obtain ⟨hxcl, hxcard⟩ := hx
        have hx0 : Nat.card (X.residueField x) ≠ 0 := by
          rw [hxcard]
          exact pow_ne_zero _ (Nat.card_ne_zero.mpr ⟨⟨0⟩, inferInstance⟩)
        haveI : Finite (X.residueField x) := (Nat.card_ne_zero.mp hx0).2
        haveI : Fintype (X.residueField x) := Fintype.ofFinite _
        have hcard : Fintype.card (X.residueField x) =
            Fintype.card (X.residueField x₀) := by
          have h1 : Fintype.card (X.residueField x) = Nat.card (X.residueField x) :=
            (Nat.card_eq_fintype_card).symm
          have h2 : Fintype.card (X.residueField x₀) = Nat.card (X.residueField x₀) :=
            (Nat.card_eq_fintype_card).symm
          rw [h1, h2, hxcard, hx₀card]
        let e : (X.residueField x) ≃+* (X.residueField x₀) :=
          FiniteField.ringEquivOfCardEq hcard
        let h : Spec (.of (↥(X.residueField x₀))) ⟶ X :=
          Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x
        refine ⟨h, ?_⟩
        show (Spec.map (CommRingCat.ofHom e.toRingHom) ≫ X.fromSpecResidueField x) pt = x
        exact Scheme.fromSpecResidueField_apply x _
      exact Set.Finite.subset (Set.finite_range _) hsub

/-- Paper: §14.2, p. 535. The number of closed points of degree m over k. -/
noncomputable def curveZetaClosedPointCount (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (m : ℕ) : ℕ :=
  {x : X | x ∈ closedPoints X ∧
    Nat.card (X.residueField x) = Nat.card k ^ m}.ncard

/-- Paper: §14.2, p. 535. A closed point of degree d contributes d rational
points over an extension of degree m exactly when d divides m.
Deviation: Uses the exact counting identity behind the printed upper bound. -/
theorem curveZeta_extensionPointCount (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f]
    (K : Type u) [Field K] [Algebra k K] [Finite K] :
    Nat.card {p : Spec (.of K) ⟶ X // p ≫ f = Spec.map (CommRingCat.ofHom (algebraMap k K))} =
      ∑ d ∈ (Module.finrank k K).divisors, d * curveZetaClosedPointCount f d := by sorry

/-- Paper: §14.2, p. 535. The number of degree-m closed points is
q^m/m with error O(q^(m/2)/m) as m tends to infinity.
Deviation: The Big-O constant here is for the given curve. The paper also
specifies uniformity in the curve through its genus. -/
theorem curveZeta_closedPointsOfDegree_asymptotic (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] :
    let q : ℝ := Nat.card k
    (fun m : ℕ ↦ (curveZetaClosedPointCount f m : ℝ) - q ^ m / m) =O[Filter.atTop]
      (fun m : ℕ ↦ Real.sqrt (q ^ m) / m) := by sorry

/-- Paper: §14.2, p. 535. The Weil point-count estimate with genus g gives
an error constant depending only on g in the closed-point count.
Deviation: Uses the numerical Weil hypothesis and the closed-point expression
for the extension-field counts. The displayed constant is an explicit bound. -/
theorem curveZeta_closedPointsOfDegree_bound_of_weil (f : X ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsProper f] [GeometricallyConnected f] (g : ℕ) :
    let q : ℝ := Nat.card k
    let N (r : ℕ) : ℝ := ∑ d ∈ r.divisors, (d : ℝ) * curveZetaClosedPointCount f d
    (∀ r : ℕ, 0 < r → |N r - (q ^ r + 1)| ≤ 2 * g * Real.sqrt (q ^ r)) →
    ∀ m : ℕ, 0 < m → |(curveZetaClosedPointCount f m : ℝ) - q ^ m / m| ≤
      (5 + 6 * (g : ℝ)) * Real.sqrt (q ^ m) / m := by sorry

-- TODO(paper-gap): The comparison on p. 535 refers to the missing Theorem
-- 13.3.1.2. Equation (5.3.1.5) supplies a finite-place principal-value
-- operator. The function-field completion, convergence in the topology of
-- uniform convergence on bounded sets, and trace identity are unspecified.

-- TODO(paper-gap): The gonality equality on p. 535 fails for the Hermitian
-- quartic y³ + y = x⁴ over 𝔽₉. Its genus is three and projection to x has
-- degree three. It is maximal and its sole Frobenius eigenvalue has
-- multiplicity six. For g ≥ 2 the general bound gon_k(X) ≤ g + 1 < 2g
-- follows by Riemann–Roch at a rational point. For g = 1 the strict
-- inequality also fails, since gon_k(E) = 2 = 2g. The printed equality
-- and strict inequality need curve-genus and gonality interfaces.

-- TODO(paper-gap): The supersingular example on p. 536 needs a choice of
-- curve with equal Frobenius eigenvalues. Over 𝔽₉, y² = x³ − x has numerator
-- (1 + 3T)². The supersingular curve y² = x³ + (1 + i)x with i² = −1 has
-- numerator 1 + 9T² and gives simple zeros for the quadratic cover's L-function.

-- TODO(paper-gap): §14.3, p. 536 gives n[F : ℚ] as a proposed multiplicity
-- bound for generic zeros. Page 533 identifies these as non-central zeros.
-- A unitary imaginary norm twist translates the zeros in the s-plane.
-- The higher-rank centering convention and argument need to be supplied
-- before stating the bound (ERRATA R24 and M43).

end RiemannMasullo
