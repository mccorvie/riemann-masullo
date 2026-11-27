module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RatBridge_Isotypic_Isolated

/-!
# The isotypic reduction over ℚ, continued

Workstream B for #7351, stage 3c (continued).

* `ratBridge_dirichlet_isotypic_converse`: every Dirichlet test in the fixed box of size
  `ratDirichletBoxShift N X` has the theta of a test of the absolute Paley–Wiener level (item 7,
  converse).
* `ratIsoSum_ball_expansion`: at a place `p ∤ N` the isotypic sum is a combination of balls.
* `ratBridge_dirichlet_isotypic_unrestricted`: every adelic test has the theta of a Dirichlet test
  of parity `χ(-1)` (item 8).

Nothing imports this module; all declarations live in `namespace RiemannMasullo.Isolated`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology IsDedekindDomain
open scoped NNReal ENNReal SchwartzMap FourierTransform NumberField.AdeleRing TensorProduct

namespace RiemannMasullo.Isolated

set_option quotPrecheck false

open NumberFieldKB.Chebotarev.RatIdele

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Bℚ" => SchwartzBruhat (Multiplicative 𝔸)
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)
local notation "realCoord" =>
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "ν𝔭(" v ")" => finiteLocalAdditiveTamagawaMeasure ℚ v
local notation "ψ𝔭(" v ")" => finiteLocalStandardCharacter ℚ v
local notation "SB(" v ")" => SchwartzBruhat (Multiplicative (HeightOneSpectrum.adicCompletion ℚ v))
local notation "F𝔭(" v ")" => tamagawaFourier ν𝔭(v) ψ𝔭(v)

local instance (w : InfinitePlace ℚ) : MeasurableSpace w.Completion := borel _
local instance : MeasurableSpace (InfiniteAdeleRing ℚ) :=
  inferInstanceAs (MeasurableSpace ((w : InfinitePlace ℚ) → w.Completion))
local instance (v : Vℚ) : MeasurableSpace (v.adicCompletion ℚ) := borel _
local instance (v : Vℚ) : MeasurableSpace (v.adicCompletion ℚ)ˣ := borel _
local instance (S : Finset Vℚ) : MeasurableSpace (SAdeleRing ℚ S) :=
  inferInstanceAs (MeasurableSpace (InfiniteAdeleRing ℚ × ((v : S) → v.val.adicCompletion ℚ)))

section Converse

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ

local notation "Sχ" => ratDirichletS N

/-- The S-local test `h ⊗ ⨂_{w ∣ N} shell_{a_w}`. -/
def shellSLocalTest (hχ : χ.IsPrimitive) (h : 𝓢(ℝ, ℂ)) (a : Sχ → ℤ) :
    SchwartzBruhat (Multiplicative (SAdeleRing ℚ Sχ)) :=
  (sAdeleSchwartz_inductiveTensor_equiv ℚ Sχ).choose
    (archTest h ⊗ₜ[ℂ] (⨂ₜ[ℂ] w, ratShellSB w.val (ratDirichletLocalChar hχ w.val) (a w)))

theorem shellSLocalTest_apply (hχ : χ.IsPrimitive) (h : 𝓢(ℝ, ℂ)) (a : Sχ → ℤ)
    (x : SAdeleRing ℚ Sχ) :
    shellSLocalTest hχ h a (Multiplicative.ofAdd x) =
      h (realCoord (x.1 Rat.infinitePlace)) *
        ∏ w : Sχ, shellTestFun w.val (ratDirichletLocalChar hχ w.val) (a w) (x.2 w) := by
  rw [shellSLocalTest, (sAdeleSchwartz_inductiveTensor_equiv ℚ Sχ).choose_spec, archTest_apply]
  simp only [ratShellSB_apply]

theorem toGlobal_shellSLocalTest (hχ : χ.IsPrimitive) (h : 𝓢(ℝ, ℂ)) (a : Sχ → ℤ) :
    sAdeleSchwartzToGlobal ℚ Sχ (shellSLocalTest hχ h a) =
      ratPhi Sχ h (fun w ↦ ratShellSB w.val (ratDirichletLocalChar hχ w.val) (a w)) := rfl

theorem shellSLocalTest_fourier (hχ : χ.IsPrimitive) (h : 𝓢(ℝ, ℂ)) (a : Sχ → ℤ)
    (y : SAdeleRing ℚ Sχ) :
    sAdeleSchwartzFourier (shellSLocalTest hχ h a) (Multiplicative.ofAdd y) =
      𝓕 h (realCoord (y.1 Rat.infinitePlace)) *
        ∏ w : Sχ, F𝔭(w.val) (shellTestFun w.val (ratDirichletLocalChar hχ w.val) (a w))
          (y.2 w) := by
  rw [ratSLocalFourier_prod Sχ _ (fun z ↦ h (realCoord (z Rat.infinitePlace)))
    (fun w ↦ shellTestFun w.val (ratDirichletLocalChar hχ w.val) (a w))
    (shellSLocalTest_apply hχ h a) y, ratArchFourier_archTest]

private theorem exists_mem_ratDirichletS' (hN : 1 < N) : ∃ v : Vℚ, v ∈ Sχ := by
  have hp := Nat.minFac_prime (show N ≠ 1 by omega)
  refine ⟨placeOf _ hp, (mem_ratDirichletS (NeZero.ne N) _).mpr ?_⟩
  rw [pr_placeOf]
  exact Nat.minFac_dvd N

private theorem shellTestFun_at_zero (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) (a : ℤ) :
    shellTestFun v c a 0 = 0 := by
  rw [shellTestFun, mul_zero]
  unfold unitCharTestFun
  refine Set.indicator_of_notMem (fun h ↦ ?_) _
  obtain ⟨w, hw, hw0⟩ := h
  exact w.ne_zero hw0

private theorem localFourier_zero' (v : Vℚ) (F : v.adicCompletion ℚ → ℂ) :
    F𝔭(v) F 0 = ∫ x, F x ∂ν𝔭(v) := by
  unfold tamagawaFourier
  simp only [mul_zero, finiteLocalStandardCharacter_zero, Circle.coe_one, star_one, mul_one]

private theorem transition_refl'' (S : Finset Vℚ)
    (k : SchwartzBruhat (Multiplicative (SAdeleRing ℚ S))) :
    sAdeleSchwartzTransition ℚ (le_rfl : S ⊆ S) k = k := by
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : SAdeleRing ℚ S, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [sAdeleSchwartzTransition_apply, ite_eq_left_of_eq_true _ _ (eq_true fun w hw ↦ absurd w.2 hw)]

/-- The global test with twisted shells at the places over `N` is polar. -/
theorem ratPhi_shell_mem_polarSubspace (hχ : χ.IsPrimitive) (hN : 1 < N) (h : 𝓢(ℝ, ℂ))
    (a : Sχ → ℤ) :
    ratPhi Sχ h (fun w ↦ ratShellSB w.val (ratDirichletLocalChar hχ w.val) (a w)) ∈
      adelePolarSubspace ℚ := by
  obtain ⟨v₀, hv₀⟩ := exists_mem_ratDirichletS' (N := N) hN
  have hdv : pr v₀ ∣ N := (mem_ratDirichletS (NeZero.ne N) v₀).mp hv₀
  rw [← toGlobal_shellSLocalTest, sAdeleSchwartzToGlobal_mem_polarSubspace_iff]
  constructor
  · rw [shellSLocalTest_apply]
    exact mul_eq_zero_of_right _
      (Finset.prod_eq_zero (Finset.mem_univ ⟨v₀, hv₀⟩) (shellTestFun_at_zero _ _ _))
  · rw [shellSLocalTest_fourier]
    refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ⟨v₀, hv₀⟩) ?_)
    by_contra hne
    have h1 := (shellTestFun_fourier_ne_zero_iff hχ v₀ hdv (a ⟨v₀, hv₀⟩) _).mp hne
    rw [show (0 : SAdeleRing ℚ Sχ).2 ⟨v₀, hv₀⟩ = 0 from rfl, norm_zero] at h1
    exact (zpow_pos (by exact_mod_cast (pr_prime v₀).pos) _).ne' h1.symm

/-- **The shells of a test in the box.** If `h` has Fourier support in `[-X, X]` and every shell
exponent has `q^{e_q + a_q} ≤ X`, the global test with those shells is in the absolute
Paley–Wiener level. -/
theorem ratPhi_shell_mem_absolutePWTests (hχ : χ.IsPrimitive) (hN : 1 < N) {X : ℝ} (h : 𝓢(ℝ, ℂ))
    (hh : IsFourierBand X h) (a : Sχ → ℤ)
    (ha : ∀ w : Sχ, (pr w.val : ℝ) ^ ((N.factorization (pr w.val) : ℤ) + a w) ≤ X) :
    (⟨_, ratPhi_shell_mem_polarSubspace hχ hN h a⟩ : adelePolarSubspace ℚ) ∈
      primaryDivisorialAbsolutePWTests (F := ℚ) Sχ X := by
  change ratPhi Sχ h _ ∈ (sLocalPWTests le_rfl (sLocalPWBox Sχ X)).map (sAdeleSchwartzToGlobal ℚ Sχ)
  refine ⟨shellSLocalTest hχ h a, ?_, rfl⟩
  rw [SetLike.mem_coe, mem_sLocalPWTests]
  refine ⟨shellSLocalTest hχ h a, transition_refl'' _ _, ?_⟩
  set K : Set (Multiplicative (SAdeleRing ℚ Sχ)) := Multiplicative.toAdd ⁻¹' sLocalPWBox Sχ X
  have hKc : IsCompact K := by
    have hK : K = Multiplicative.ofAdd '' sLocalPWBox Sχ X := by
      ext y
      exact ⟨fun h ↦ ⟨y.toAdd, h, rfl⟩, fun ⟨z, hz, hzy⟩ ↦ hzy ▸ hz⟩
    rw [hK]
    exact (isCompact_sLocalPWBox (S := Sχ) X).image continuous_ofAdd
  have hsupp : Function.support (sAdeleSchwartzFourier (shellSLocalTest hχ h a)).val ⊆ K := by
    intro y hy
    obtain ⟨y, rfl⟩ : ∃ z, Multiplicative.ofAdd z = y := ⟨y.toAdd, rfl⟩
    have hy' : sAdeleSchwartzFourier (shellSLocalTest hχ h a) (Multiplicative.ofAdd y) ≠ 0 := hy
    rw [shellSLocalTest_fourier] at hy'
    obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hy'
    refine ⟨fun w ↦ ?_, fun w ↦ ?_⟩
    · obtain rfl : w = Rat.infinitePlace := Subsingleton.elim _ _
      have hr := hh (subset_tsupport _ h1)
      have hn := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
        Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) (y.1 Rat.infinitePlace)
      change ‖realCoord (y.1 Rat.infinitePlace)‖ = _ at hn
      have hm : Rat.infinitePlace.mult = 1 := by
        simp [InfinitePlace.mult, Rat.isReal_infinitePlace]
      change ‖y.1 Rat.infinitePlace‖ ^ Rat.infinitePlace.mult ≤ X
      rw [hm, pow_one, ← hn, Real.norm_eq_abs]
      exact abs_le.mpr hr
    · have hw := Finset.prod_ne_zero_iff.mp h2 w (Finset.mem_univ _)
      have hdv : pr w.val ∣ N := (mem_ratDirichletS (NeZero.ne N) _).mp w.2
      have h3 := (shellTestFun_fourier_ne_zero_iff hχ w.val hdv (a w) (y.2 w)).mp hw
      change ‖y.2 w‖ ≤ X
      rw [h3]
      exact ha w
  let : T2Space (Multiplicative (SAdeleRing ℚ Sχ)) :=
    inferInstanceAs (T2Space (((w : InfinitePlace ℚ) → w.Completion) ×
      ((v : Sχ) → v.val.adicCompletion ℚ)))
  have hcl : tsupport (sAdeleSchwartzFourier (shellSLocalTest hχ h a)).val ⊆ K :=
    closure_minimal hsupp hKc.isClosed
  exact ⟨hKc.of_isClosed_subset (isClosed_tsupport _) hcl, hcl⟩

private theorem prod_ratDirichletS' (f : ℕ → ℝ) :
    ∏ w : Sχ, f (pr w.val) = ∏ q ∈ N.primeFactors, f q := by
  classical
  rw [Finset.prod_coe_sort (ratDirichletS N) (fun w ↦ f (pr w)), ratDirichletS,
    Finset.prod_image fun p _ p' _ h ↦ Subtype.ext (by
      have := congrArg pr h
      rwa [pr_placeOf, pr_placeOf] at this)]
  rw [← Finset.prod_attach N.primeFactors f]
  exact Finset.prod_congr rfl fun p _ ↦ by rw [pr_placeOf]

private theorem exponent_le_log' (p : ℕ) (hp : 1 < p) {X : ℝ} (k : ℕ) (hk : (p : ℝ) ^ k ≤ X) :
    k ≤ Nat.log p ⌊X⌋₊ :=
  Nat.le_log_of_pow_le hp (Nat.le_floor (by exact_mod_cast hk))

/-- Paper: (11.3.1.3), p. 494, over `ℚ`.
**Item 7, converse.** Every real test `f` with Fourier support in `[-R(X), R(X)]` arises: some test
of the absolute Paley–Wiener level `primaryDivisorialAbsolutePWTests ℚ S X` has, on every class
`k · τ(t)`, the homogeneous theta of `dirTest χ f`. The test is the translate of a Dirichlet test
by the largest admissible shells `∏_{q ∣ N} q^{⌊log_q X⌋ - e_q}`. -/
theorem ratBridge_dirichlet_isotypic_converse (hχ : χ.IsPrimitive) (hN : 1 < N) {X : ℝ}
    (hX : ∀ p ∈ N.primeFactors, (p : ℝ) ^ N.factorization p ≤ X) (f : 𝓢(ℝ, ℂ))
    (hf : tsupport (fun x : ℝ ↦ (𝓕 f) x) ⊆
      Set.Icc (-(ratDirichletBoxShift N X)) (ratDirichletBoxShift N X)) :
    ∃ g : adelePolarSubspace ℚ, g ∈ primaryDivisorialAbsolutePWTests (F := ℚ) Sχ X ∧
      ∀ (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker),
        homogeneousAdelicTheta ω g.val (k.val * ratNormSection t) =
          homogeneousAdelicTheta ω (dirTest hχ f) (k.val * ratNormSection t) := by
  have hX1 : 1 ≤ X := by
    obtain ⟨p, hp⟩ : N.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr hN
    exact (one_le_pow₀ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)).trans
      (hX p hp)
  have hdv (w : Sχ) : pr w.val ∣ N := (mem_ratDirichletS (NeZero.ne N) _).mp w.2
  have he (w : Sχ) : N.factorization (pr w.val) ≤ Nat.log (pr w.val) ⌊X⌋₊ :=
    exponent_le_log' (pr w.val) (pr_prime w.val).one_lt _
      (hX _ (Nat.mem_primeFactors.mpr ⟨pr_prime _, hdv w, NeZero.ne N⟩))
  let a : Sχ → ℤ := fun w ↦ ((Nat.log (pr w.val) ⌊X⌋₊ - N.factorization (pr w.val) : ℕ) : ℤ)
  set D := ratPrimePowReal Sχ a with hDdef
  have hD : 0 < D := ratPrimePowReal_pos Sχ a
  set c := ratTranslateScalar hχ Sχ a
  have hc : c ≠ 0 := ratTranslateScalar_ne_zero hχ Sχ a
  let h : 𝓢(ℝ, ℂ) := c⁻¹ • schwartzScale D⁻¹ (inv_ne_zero hD.ne') f
  have hid : c • schwartzScale D hD.ne' h = f := by
    ext x
    simp only [h, smul_apply, schwartzScale_apply, smul_eq_mul]
    rw [mul_inv_cancel_left₀ hc, inv_mul_cancel_left₀ hD.ne']
  have hrep := dirTest_translate_theta hχ hN Sχ a h
  rw [← ratPhi_shell_eq_translate, hid] at hrep
  -- the Fourier band of `h`
  have hDR : D⁻¹ * ratDirichletBoxShift N X = X := by
    have hDprod : D = ∏ q ∈ N.primeFactors, (q : ℝ) ^ (Nat.log q ⌊X⌋₊ - N.factorization q) := by
      rw [hDdef, ratPrimePowReal, ← prod_ratDirichletS' (fun q ↦
        (q : ℝ) ^ (Nat.log q ⌊X⌋₊ - N.factorization q))]
      refine Finset.prod_congr rfl fun w _ ↦ ?_
      simp only [a, zpow_natCast]
    rw [ratDirichletBoxShift, ← hDprod, mul_comm X, ← mul_assoc, inv_mul_cancel₀ hD.ne', one_mul]
  have hh : IsFourierBand X h := by
    have h1 := (show IsFourierBand (ratDirichletBoxShift N X) f from hf).scale (inv_pos.mpr hD)
    rw [hDR] at h1
    exact h1.smul _
  have ha (w : Sχ) : (pr w.val : ℝ) ^ ((N.factorization (pr w.val) : ℤ) + a w) ≤ X := by
    have hp0 : 0 < pr w.val := (pr_prime w.val).pos
    rw [show (N.factorization (pr w.val) : ℤ) + a w = (Nat.log (pr w.val) ⌊X⌋₊ : ℕ) by
      simp only [a]; rw [Nat.cast_sub (he w)]; ring, zpow_natCast]
    calc (pr w.val : ℝ) ^ Nat.log (pr w.val) ⌊X⌋₊ =
          ((pr w.val ^ Nat.log (pr w.val) ⌊X⌋₊ : ℕ) : ℝ) := by
          push_cast; ring
      _ ≤ (⌊X⌋₊ : ℝ) := by
          exact_mod_cast Nat.pow_log_le_self _ (Nat.floor_pos.mpr hX1).ne'
      _ ≤ X := Nat.floor_le (by linarith)
  exact ⟨⟨_, ratPhi_shell_mem_polarSubspace hχ hN h a⟩,
    ratPhi_shell_mem_absolutePWTests hχ hN h hh a ha, fun t k ↦ hrep.eq_dirTest hN t k⟩

end Converse


/-! ### Places not dividing the conductor: radial expansion into balls -/

section Unramified

local notation "UU(" v ")" => ↥((HeightOneSpectrum.adicCompletionIntegers ℚ v).units)

private theorem sb_sum_apply'' {G : Type*} [CommGroup G] [TopologicalSpace G] {κ : Type*}
    (s : Finset κ) (f : κ → SchwartzBruhat G) (x : G) :
    (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

private theorem norm_primeUnit_zpow' (v : Vℚ) (a : ℤ) :
    ‖((ratPrimeUnit v ^ a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ)‖ = (pr v : ℝ) ^ (-a) := by
  rw [Units.val_zpow_eq_zpow_val, norm_zpow, ratPrimeUnit_val, ratPrime_norm, inv_zpow, zpow_neg]

private theorem ratNorm_eq_zpow'' (v : Vℚ) {η : v.adicCompletion ℚ} (hη : η ≠ 0) :
    ∃ m : ℤ, ‖η‖ = (pr v : ℝ) ^ m := by
  have hv0 : Valued.v η ≠ 0 := (Valuation.ne_zero_iff _).mpr hη
  set k := WithZero.log (Valued.v η)
  have hp0 : (0 : ℝ) < pr v := by exact_mod_cast (pr_prime v).pos
  have hvp : Valued.v (pr v : v.adicCompletion ℚ) = WithZero.exp (-1) := by
    simpa only [Rat.cast_natCast, eq_self, ↓reduceIte] using valued_prime v (pr_prime v)
  have h1 : Valued.v (η * ((ratPrimeUnit v ^ k : (v.adicCompletion ℚ)ˣ) :
      v.adicCompletion ℚ)) = 1 := by
    rw [map_mul, Units.val_zpow_eq_zpow_val, map_zpow₀, ratPrimeUnit_val, hvp,
      ← WithZero.exp_log hv0, ← WithZero.exp_zsmul, ← WithZero.exp_add, smul_eq_mul]
    rw [show k + k * -1 = 0 by ring, WithZero.exp_zero]
  have hn := Valued.toNormedField.norm_eq_one_iff.mpr h1
  rw [norm_mul, norm_primeUnit_zpow', zpow_neg, mul_inv_eq_one₀ (zpow_ne_zero _ hp0.ne')] at hn
  exact ⟨k, hn⟩

theorem oneSB_lc (v : Vℚ) :
    IsLocallyConstant ((v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator
        (fun _ ↦ (1 : ℂ))) ∧
      HasCompactSupport ((v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator
        (fun _ ↦ (1 : ℂ))) := by
  have hO : IsClopen (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    Valued.isClopen_valuationSubring _
  have hK : IsCompact (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) :=
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers v)
  refine ⟨(IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_,
    HasCompactSupport.intro hK fun x hx ↦ Set.indicator_of_notMem hx _⟩
  by_cases hx : x ∈ (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ))
  · exact ⟨_, hO.isOpen, hx, fun y hy ↦ by rw [Set.indicator_of_mem hy, Set.indicator_of_mem hx]⟩
  · exact ⟨_, hO.compl.isOpen, hx, fun y hy ↦ by
      rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]⟩

/-- The integer indicator `1_{ℤ_p}`. -/
def oneSB (v : Vℚ) : SB(v) :=
  ((mem_finitePlaceSchwartz_iff ℚ v _).mpr (oneSB_lc v)).choose

theorem oneSB_apply (v : Vℚ) (x : v.adicCompletion ℚ) :
    oneSB v (Multiplicative.ofAdd x) =
      (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)).indicator (fun _ ↦ (1 : ℂ)) x :=
  ((mem_finitePlaceSchwartz_iff ℚ v _).mpr (oneSB_lc v)).choose_spec x

/-- The ball indicator `1_{p^m ℤ_p}` as a scaled integer indicator. -/
theorem ballSB_apply (v : Vℚ) (m : ℤ) (x : v.adicCompletion ℚ) :
    ratUnitScale v ((ratPrimeUnit v ^ m)⁻¹) (oneSB v) (Multiplicative.ofAdd x) =
      if ‖x‖ ≤ (pr v : ℝ) ^ (-m) then 1 else 0 := by
  have hp0 : (0 : ℝ) < pr v := by exact_mod_cast (pr_prime v).pos
  rw [ratUnitScale_apply, oneSB_apply]
  have hiff : ((((ratPrimeUnit v ^ m)⁻¹ : (v.adicCompletion ℚ)ˣ)) : v.adicCompletion ℚ) * x ∈
      (v.adicCompletionIntegers ℚ : Set (v.adicCompletion ℚ)) ↔ ‖x‖ ≤ (pr v : ℝ) ^ (-m) := by
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valued.toNormedField.norm_le_one_iff, norm_mul, Units.val_inv_eq_inv_val, norm_inv,
      norm_primeUnit_zpow', zpow_neg, inv_inv, ← le_inv_mul_iff₀ (zpow_pos hp0 m), mul_one,
      ← zpow_neg]
  by_cases h : ‖x‖ ≤ (pr v : ℝ) ^ (-m)
  · rw [Set.indicator_of_mem (hiff.mpr h), ite_eq_left_of_eq_true _ _ (eq_true h)]
  · rw [Set.indicator_of_notMem (fun h' ↦ h (hiff.mp h')),
      ite_eq_right_of_eq_false _ _ (eq_false h)]

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- At a place `p ∤ N` the local component of `ψ` is trivial on the units. -/
theorem ratDirichletLocalChar_unit_eq_one (hχ : χ.IsPrimitive) (v : Vℚ) (hv : ¬ pr v ∣ N)
    (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) :
    ratDirichletLocalChar hχ v u = 1 := by
  refine ratDirichletLocalChar_eq_one hχ v u hu ?_
  rw [Nat.factorization_eq_zero_of_not_dvd hv, pow_zero, div_one]
  refine (Valuation.map_sub _ _ _).trans (max_le hu.le ?_)
  rw [map_one]

/-- The exponent attached to an index `(a, j)` of the radial expansion. -/
def ratExpIdx (i : ℤ × Fin 3) : ℤ := i.1 + if i.2 = 1 then 1 else 0

/-- **Radial expansion at `p ∤ N`.** The isotypic sum of a local test at a place not dividing `N`
is a finite combination of ball indicators `1_{p^m ℤ_p}`. -/
theorem ratIsoSum_ball_expansion (hχ : χ.IsPrimitive) (v : Vℚ) (hv : ¬ pr v ∣ N) (n : ℕ)
    (b : SB(v)) (hb : IsUnitBallInvariant v n b) :
    ∃ (s : Finset (ℤ × Fin 3)) (coef : ℤ × Fin 3 → ℂ),
      ratIsoSum v (ratDirichletLocalChar hχ v) n b =
        ∑ i ∈ s, coef i • ratUnitScale v ((ratPrimeUnit v ^ ratExpIdx i)⁻¹) (oneSB v) := by
  classical
  set c := ratDirichletLocalChar hχ v
  set P := ratIsoSum v c n b
  have hp1 : (1 : ℝ) < pr v := by exact_mod_cast (pr_prime v).one_lt
  have hp0 : (0 : ℝ) < pr v := by linarith
  have hcU (u : UU(v)) : c ((u : UU(v)) : (v.adicCompletion ℚ)ˣ) = 1 :=
    ratDirichletLocalChar_unit_eq_one hχ v hv _
      (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp u.2)
  have hrad (u : UU(v)) (x : v.adicCompletion ℚ) :
      P (Multiplicative.ofAdd ((((u : UU(v)) : (v.adicCompletion ℚ)ˣ)) * x)) =
        P (Multiplicative.ofAdd x) := by
    rw [ratIsoSum_mul v c n b (fun u _ ↦ hcU u) hb u x, hcU, inv_one, one_mul]
  obtain ⟨hlc, hcs⟩ := (mem_finitePlaceSchwartz_iff ℚ v (fun y ↦ P (Multiplicative.ofAdd y))).mp
    ⟨P, fun _ ↦ rfl⟩
  have hεE := Metric.isOpen_iff.mp (hlc.isOpen_fiber (P (Multiplicative.ofAdd 0))) 0 rfl
  obtain ⟨ε, hε, hεball⟩ := hεE
  have hsmall (x : v.adicCompletion ℚ) (hx : ‖x‖ < ε) :
      P (Multiplicative.ofAdd x) = P (Multiplicative.ofAdd 0) := by
    have h : x ∈ Metric.ball (0 : v.adicCompletion ℚ) ε := by
      rwa [Metric.mem_ball, dist_zero_right]
    exact hεball h
  obtain ⟨R, hR⟩ := (hcs : IsCompact _).isBounded.subset_closedBall 0
  have hlarge (x : v.adicCompletion ℚ) (hx : R < ‖x‖) : P (Multiplicative.ofAdd x) = 0 :=
    image_eq_zero_of_notMem_tsupport (f := fun y ↦ P (Multiplicative.ofAdd y)) fun h ↦ by
      have := hR h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact absurd this (not_le.mpr hx)
  obtain ⟨K₁, hK₁⟩ := pow_unbounded_of_one_lt R hp1
  obtain ⟨K₂, hK₂⟩ := pow_unbounded_of_one_lt ε⁻¹ hp1
  let A₀ : Finset ℤ := Finset.Icc (-(K₁ : ℤ)) K₂
  let α (a : ℤ) : ℂ :=
    P (Multiplicative.ofAdd ((ratPrimeUnit v ^ a : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ))
  let ball (m : ℤ) (x : v.adicCompletion ℚ) : ℂ := if ‖x‖ ≤ (pr v : ℝ) ^ (-m) then 1 else 0
  -- the pointwise radial expansion
  have hexp (x : v.adicCompletion ℚ) : P (Multiplicative.ofAdd x) =
      ∑ a ∈ A₀, α a * (ball a x - ball (a + 1) x) +
        P (Multiplicative.ofAdd 0) * ball ((K₂ : ℤ) + 1) x := by
    by_cases hx0 : x = 0
    · rw [hx0]
      simp only [ball, norm_zero, zpow_nonneg hp0.le, ↓reduceIte, sub_self, mul_zero,
        Finset.sum_const_zero, zero_add, mul_one]
    obtain ⟨m, hm⟩ := ratNorm_eq_zpow'' v hx0
    have hball (k : ℤ) : ball k x = if k ≤ -m then 1 else 0 := by
      simp only [ball, hm]
      by_cases hk : k ≤ -m
      · rw [ite_eq_left_of_eq_true _ _ (eq_true (zpow_le_zpow_right₀ hp1.le (by omega))),
          ite_eq_left_of_eq_true _ _ (eq_true hk)]
      · rw [ite_eq_right_of_eq_false _ _ (eq_false (not_le.mpr
          (zpow_lt_zpow_right₀ hp1 (by omega)))), ite_eq_right_of_eq_false _ _ (eq_false hk)]
    have hdiff (a : ℤ) : ball a x - ball (a + 1) x = if a = -m then 1 else 0 := by
      rw [hball, hball]
      by_cases h1 : a = -m
      · simp only [h1, le_refl, ↓reduceIte, show ¬ (-m + 1 ≤ -m) by omega, sub_zero]
      · by_cases h2 : a ≤ -m
        · simp only [h2, ↓reduceIte, show a + 1 ≤ -m by omega, sub_self, h1]
        · simp only [h2, ↓reduceIte, show ¬ (a + 1 ≤ -m) by omega, sub_self, h1]
    -- radial: `P x = α (-m)`
    have hw0 : ((ratPrimeUnit v ^ (-m))⁻¹ : (v.adicCompletion ℚ)ˣ).val * x ≠ 0 :=
      mul_ne_zero (Units.ne_zero _) hx0
    let w : (v.adicCompletion ℚ)ˣ := Units.mk0 _ hw0
    have hwn : ‖(w : v.adicCompletion ℚ)‖ = 1 := by
      rw [Units.val_mk0, norm_mul, Units.val_inv_eq_inv_val, norm_inv, norm_primeUnit_zpow', hm,
        neg_neg, inv_mul_cancel₀ (zpow_ne_zero _ hp0.ne')]
    have hwv : Valued.v (w : v.adicCompletion ℚ) = 1 := Valued.toNormedField.norm_eq_one_iff.mp hwn
    let wU : UU(v) :=
      ⟨w, HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hwv⟩
    have hxw : x = (w : v.adicCompletion ℚ) *
        ((ratPrimeUnit v ^ (-m) : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) := by
      rw [Units.val_mk0, Units.val_inv_eq_inv_val, mul_comm, ← mul_assoc,
        mul_inv_cancel₀ (Units.ne_zero _), one_mul]
    have hPx : P (Multiplicative.ofAdd x) = α (-m) := by
      rw [hxw]
      exact hrad wU _
    simp only [hdiff]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hball]
    by_cases hin : -m ∈ A₀
    · have hK : ¬ ((K₂ : ℤ) + 1 ≤ -m) := by
        simp only [A₀, Finset.mem_Icc] at hin
        omega
      rw [ite_eq_left_of_eq_true _ _ (eq_true hin), ite_eq_right_of_eq_false _ _ (eq_false hK),
        add_zero, hPx]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hin), zero_add]
      simp only [A₀, Finset.mem_Icc, not_and_or, not_le] at hin
      rcases hin with h | h
      · have hK : ¬ ((K₂ : ℤ) + 1 ≤ -m) := by omega
        rw [ite_eq_right_of_eq_false _ _ (eq_false hK)]
        apply hlarge
        rw [hm]
        calc R < (pr v : ℝ) ^ K₁ := hK₁
          _ = (pr v : ℝ) ^ (K₁ : ℤ) := (zpow_natCast _ _).symm
          _ < (pr v : ℝ) ^ m := zpow_lt_zpow_right₀ hp1 (by omega)
      · have hK : (K₂ : ℤ) + 1 ≤ -m := by omega
        rw [ite_eq_left_of_eq_true _ _ (eq_true hK)]
        apply hsmall
        rw [hm]
        calc (pr v : ℝ) ^ m < (pr v : ℝ) ^ (-(K₂ : ℤ)) := zpow_lt_zpow_right₀ hp1 (by omega)
          _ = ((pr v : ℝ) ^ K₂)⁻¹ := by rw [zpow_neg, zpow_natCast]
          _ < ε := (inv_lt_comm₀ (by positivity) hε).mpr hK₂
  -- the expansion as a finite sum of scaled integer indicators
  let coef : ℤ × Fin 3 → ℂ := fun i ↦
    if i.2 = 0 then α i.1 else if i.2 = 1 then -α i.1 else P (Multiplicative.ofAdd 0)
  refine ⟨A₀ ×ˢ {0, 1} ∪ {((K₂ : ℤ) + 1, 2)}, coef, ?_⟩
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : v.adicCompletion ℚ, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [sb_sum_apply'', hexp x, Finset.sum_union (by
    rw [Finset.disjoint_singleton_right, Finset.mem_product]
    simp), Finset.sum_product, Finset.sum_singleton]
  have hterm (i : ℤ × Fin 3) :
      (coef i • ratUnitScale v ((ratPrimeUnit v ^ ratExpIdx i)⁻¹) (oneSB v))
        (Multiplicative.ofAdd x) = coef i * ball (ratExpIdx i) x := by
    change coef i * _ = _
    rw [ballSB_apply]
  simp only [hterm]
  congr 1
  · refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_pair (by decide)]
    simp only [coef, ratExpIdx, Fin.isValue, ↓reduceIte, add_zero, show (0 : Fin 3) ≠ 1 by decide,
      show (1 : Fin 3) ≠ 0 by decide]
    ring

end Unramified


/-! ### Item 8: the unrestricted isotypic reduction -/

section Unrestricted

private theorem homTheta_smul' (ω₁ : PontryaginDual (ideleClassNorm ℚ).ker) (c : ℂ) (f : Bℚ)
    (y : IdeleClassGroup (𝓞 ℚ) ℚ) :
    homogeneousAdelicTheta ω₁ (c • f) y = c * homogeneousAdelicTheta ω₁ f y :=
  congrArg (fun F : C(IdeleClassGroup (𝓞 ℚ) ℚ, ℂ) ↦ F y)
    (((homogeneousAdelicTheta_isLinear ω₁).mk' _).map_smul c f)

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

set_option hygiene false in
local notation "ω" => ratDirichletNormOneChar hχ

local notation "Sχ" => ratDirichletS N
local notation "UU(" v ")" => ↥((HeightOneSpectrum.adicCompletionIntegers ℚ v).units)

open Classical in
/-- The local factors of the Dirichlet test on a larger stage: `c_q⁻¹ 1_{ℤ_q^×}` at `q ∣ N` and the
integer indicator elsewhere. -/
def ratDirichletBase (hχ : χ.IsPrimitive) (S : Finset Vℚ) (w : S) : SB(w.val) :=
  if w.val ∈ Sχ then unitCharTest w.val (ratDirichletLocalChar hχ w.val) else oneSB w.val

open Classical in
/-- On a stage containing the places over `N`, the global test of the Dirichlet factors is the
Dirichlet test. -/
theorem ratPhi_ratDirichletBase (hχ : χ.IsPrimitive) (S : Finset Vℚ) (hS : Sχ ⊆ S)
    (g : 𝓢(ℝ, ℂ)) : ratPhi S g (ratDirichletBase hχ S) = dirTest hχ g := by
  refine SchwartzBruhat.ext fun x ↦ ?_
  obtain ⟨x, rfl⟩ : ∃ y : 𝔸, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
  rw [ratPhi_apply, dirTest_apply]
  let G : Vℚ → ℂ := fun v ↦ if v ∈ Sχ then unitCharTestFun v (ratDirichletLocalChar hχ v) (x.2 v)
    else if x.2 v ∈ v.adicCompletionIntegers ℚ then 1 else 0
  have hG (w : S) : ratDirichletBase hχ S w (Multiplicative.ofAdd (x.2 w.val)) = G w.val := by
    simp only [ratDirichletBase, G]
    split_ifs with h1 h2 <;> simp [unitCharTest_apply, oneSB_apply, *]
  have hprod : ∏ w : S, ratDirichletBase hχ S w (Multiplicative.ofAdd (x.2 w.val)) =
      (∏ w : Sχ, unitCharTestFun w.val (ratDirichletLocalChar hχ w.val) (x.2 w.val)) *
        if ∀ v ∈ S \ Sχ, x.2 v ∈ v.adicCompletionIntegers ℚ then 1 else 0 := by
    simp only [hG]
    rw [Finset.prod_coe_sort S G, ← Finset.prod_sdiff hS, mul_comm]
    congr 1
    · rw [← Finset.prod_coe_sort Sχ G]
      refine Finset.prod_congr rfl fun w _ ↦ ?_
      simp only [G, w.2, ↓reduceIte]
    · rw [← Finset.prod_boole]
      refine Finset.prod_congr rfl fun v hv ↦ ?_
      simp only [G, (Finset.mem_sdiff.mp hv).2, ↓reduceIte]
  rw [hprod]
  have hiff : (∀ v : Vℚ, v ∉ Sχ → x.2 v ∈ v.adicCompletionIntegers ℚ) ↔
      (∀ v : Vℚ, v ∉ S → x.2 v ∈ v.adicCompletionIntegers ℚ) ∧
        ∀ v ∈ S \ Sχ, x.2 v ∈ v.adicCompletionIntegers ℚ :=
    ⟨fun h ↦ ⟨fun v hv ↦ h v (fun h' ↦ hv (hS h')), fun v hv ↦ h v (Finset.mem_sdiff.mp hv).2⟩,
      fun ⟨h1, h2⟩ v hv ↦ by
        by_cases hvS : v ∈ S
        · exact h2 v (Finset.mem_sdiff.mpr ⟨hvS, hv⟩)
        · exact h1 v hvS⟩
  by_cases h1 : ∀ v : Vℚ, v ∉ S → x.2 v ∈ v.adicCompletionIntegers ℚ
  · by_cases h2 : ∀ v ∈ S \ Sχ, x.2 v ∈ v.adicCompletionIntegers ℚ
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
        ite_eq_left_of_eq_true _ _ (eq_true (hiff.mpr ⟨h1, h2⟩)), mul_one]
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
        ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ h2 (hiff.mp h).2), mul_zero, mul_zero]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false h1),
      ite_eq_right_of_eq_false _ _ (eq_false fun h ↦ h1 (hiff.mp h).1)]

private theorem exists_fourier_bound (v : Vℚ) (b : SB(v)) :
    ∃ X : ℝ, ∀ ξ, X < ‖ξ‖ → F𝔭(v) (fun x ↦ b (Multiplicative.ofAdd x)) ξ = 0 := by
  obtain ⟨-, hcs⟩ := (mem_finitePlaceSchwartz_iff ℚ v
    (fun y ↦ ratLocalFourierSB v b (Multiplicative.ofAdd y))).mp ⟨_, fun _ ↦ rfl⟩
  obtain ⟨R, hR⟩ := (hcs : IsCompact _).isBounded.subset_closedBall 0
  refine ⟨R, fun ξ hξ ↦ ?_⟩
  have h := image_eq_zero_of_notMem_tsupport
    (f := fun y ↦ ratLocalFourierSB v b (Multiplicative.ofAdd y)) (x := ξ) fun h ↦ by
      have := hR h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      exact absurd this (not_le.mpr hξ)
  rwa [ratLocalFourierSB_apply] at h

/-- Every local factor's isotypic sum is a finite combination of scaled Dirichlet factors. -/
private theorem isoSum_expansion (hχ : χ.IsPrimitive) (S : Finset Vℚ) (w : S) (n : ℕ)
    (hn : N.factorization (pr w.val) ≤ n) (b : SB(w.val)) (hb : IsUnitBallInvariant w.val n b) :
    ∃ (s : Finset (ℤ × Fin 3)) (coef : ℤ × Fin 3 → ℂ),
      ratIsoSum w.val (ratDirichletLocalChar hχ w.val) n b =
        ∑ i ∈ s, coef i •
          ratUnitScale w.val ((ratPrimeUnit w.val ^ ratExpIdx i)⁻¹) (ratDirichletBase hχ S w) := by
  classical
  by_cases hw : w.val ∈ Sχ
  · have hdv : pr w.val ∣ N := (mem_ratDirichletS (NeZero.ne N) _).mp hw
    obtain ⟨X, hX⟩ := exists_fourier_bound w.val b
    obtain ⟨A, -, hA⟩ := ratIsoSum_shell_expansion hχ w.val hdv n hn b hb hX
    refine ⟨A ×ˢ {0}, fun i ↦ ratIsoSum w.val (ratDirichletLocalChar hχ w.val) n b
      (Multiplicative.ofAdd ((ratPrimeUnit w.val ^ i.1 : (w.val.adicCompletion ℚ)ˣ) :
        w.val.adicCompletion ℚ)), ?_⟩
    refine hA.trans ?_
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ ↦ ?_
    rw [Finset.sum_singleton]
    simp only [ratDirichletBase, hw, ↓reduceIte, ratExpIdx, Fin.isValue,
      show (0 : Fin 3) ≠ 1 by decide, add_zero]
    rfl
  · have hdv : ¬ pr w.val ∣ N := fun h ↦ hw ((mem_ratDirichletS (NeZero.ne N) _).mpr h)
    obtain ⟨s, coef, h⟩ := ratIsoSum_ball_expansion hχ w.val hdv n b hb
    refine ⟨s, coef, ?_⟩
    rw [h]
    simp only [ratDirichletBase, hw, ↓reduceIte]

/-- **The theta of any pure tensor.** On a stage `S ⊇ S_χ`, every global test with an arbitrary
real archimedean factor and arbitrary local factors has the theta of a Dirichlet test. -/
theorem ratPhi_dirichlet_rep_general (hχ : χ.IsPrimitive) (hN : 1 < N) (S : Finset Vℚ)
    (hS : Sχ ⊆ S) (g : 𝓢(ℝ, ℂ)) (b : ∀ w : S, SB(w.val)) :
    ∃ F : 𝓢(ℝ, ℂ), IsDirichletThetaRep hχ (ratPhi S g b) F := by
  classical
  have hn := fun w : S ↦ exists_unitBallInvariant w.val (b w) (N.factorization (pr w.val))
  choose n hn hinv using hn
  have hexp := fun w : S ↦ isoSum_expansion hχ S w (n w) (hn w) (b w) (hinv w)
  choose s coef hexp using hexp
  have hθ (y : IdeleClassGroup (𝓞 ℚ) ℚ) : homogeneousAdelicTheta ω (ratPhi S g (fun w ↦
      ratIsoSum w.val (ratDirichletLocalChar hχ w.val) (n w) (b w))) y =
        ((∏ w, Fintype.card (UU(w.val) ⧸ ratUnitBall w.val (n w)) : ℕ) : ℂ) *
          homogeneousAdelicTheta ω (ratPhi S g b) y :=
    homTheta_ratPhi_isoReplace hχ S g b (Q := fun w ↦ UU(w.val) ⧸ ratUnitBall w.val (n w))
      (fun w q ↦ ((q.out : UU(w.val)) : (w.val.adicCompletion ℚ)ˣ))
      (fun w q ↦ HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp q.out.2) y
  have hcard : ((∏ w, Fintype.card (UU(w.val) ⧸ ratUnitBall w.val (n w)) : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.prod_pos fun w _ ↦ Fintype.card_pos).ne'
  have hdec : ratPhi S g (fun w ↦ ratIsoSum w.val (ratDirichletLocalChar hχ w.val) (n w) (b w)) =
      ∑ t ∈ Fintype.piFinset s, (∏ w, coef w (t w)) •
        schwartzBruhatUnitTranslate (ratPrimePowIdele S (fun w ↦ ratExpIdx (t w)))
          (dirTest hχ g) := by
    rw [show (fun w ↦ ratIsoSum w.val (ratDirichletLocalChar hχ w.val) (n w) (b w)) = _ from
      funext hexp, ratPhi_sum]
    refine Finset.sum_congr rfl fun t _ ↦ ?_
    rw [ratPhi_smul, ratPhi_unitScale, ratPhi_ratDirichletBase hχ S hS]
    congr 2
    simp only [ratPrimePowIdele, map_inv, Finset.prod_inv_distrib, inv_inv]
  let F' : 𝓢(ℝ, ℂ) := ∑ t ∈ Fintype.piFinset s, (∏ w, coef w (t w)) •
    (ratTranslateScalar hχ S (fun w ↦ ratExpIdx (t w)) •
      schwartzScale (ratPrimePowReal S (fun w ↦ ratExpIdx (t w)))
        (ratPrimePowReal_pos S _).ne' g)
  have hrep' : IsDirichletThetaRep hχ (ratPhi S g (fun w ↦
      ratIsoSum w.val (ratDirichletLocalChar hχ w.val) (n w) (b w))) F' := by
    rw [hdec]
    exact IsDirichletThetaRep.sum hN _ fun t _ ↦
      (dirTest_translate_theta hχ hN S (fun w ↦ ratExpIdx (t w)) g).smul _
  refine ⟨(((∏ w, Fintype.card (UU(w.val) ⧸ ratUnitBall w.val (n w)) : ℕ) : ℂ))⁻¹ • F',
    fun t k ↦ ?_⟩
  have h1 := (hrep'.smul ((((∏ w, Fintype.card (UU(w.val) ⧸ ratUnitBall w.val (n w)) : ℕ) :
    ℂ))⁻¹)) t k
  rw [homTheta_smul', hθ, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul] at h1
  exact h1

private theorem archSB_eq_schwartz' (A : SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))) :
    ∃ a : 𝓢(ℝ, ℂ), ∀ z : InfiniteAdeleRing ℚ,
      A (Multiplicative.ofAdd z) = a (realCoord (z Rat.infinitePlace)) := by
  classical
  let : Unique {w : InfinitePlace ℚ // w.IsReal} :=
    uniqueOfSubsingleton ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  let : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
    ⟨fun w ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr w.property) (IsTotallyReal.isReal w.val)⟩
  let e := (ContinuousLinearEquiv.prodUnique ℝ
      ({w : InfinitePlace ℚ // w.IsReal} → ℝ) ({w : InfinitePlace ℚ // w.IsComplex} → ℂ)).trans
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : {w : InfinitePlace ℚ // w.IsReal} ↦ ℝ))
  obtain ⟨G, hG⟩ := (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun z : InfiniteAdeleRing ℚ ↦ A (Multiplicative.ofAdd z))).mp A.property
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm G, fun z ↦ ?_⟩
  rw [← hG z]
  change G _ = G (e.symm (realCoord (z Rat.infinitePlace)))
  congr 1
  apply e.injective
  rw [e.apply_symm_apply]
  rfl

/-- Paper: (11.3.1.3), p. 494, and Definition 2.2.5.1, p. 95, over `ℚ`.
**Item 8: the unrestricted isotypic reduction.** For a primitive `χ` of conductor `N > 1`, every
adelic Schwartz–Bruhat test `g` (in particular every polar one) has, on every class `k · τ(t)`,
the homogeneous theta for `ω = ψ|_{C₁}` of the Dirichlet test of a real test `f` of parity
`χ(-1)`. -/
theorem ratBridge_dirichlet_isotypic_unrestricted (hχ : χ.IsPrimitive) (hN : 1 < N) (g : Bℚ) :
    ∃ f : 𝓢(ℝ, ℂ), HasDirichletParity χ f ∧
      ∀ (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker),
        homogeneousAdelicTheta ω g (k.val * ratNormSection t) =
          homogeneousAdelicTheta ω (dirTest hχ f) (k.val * ratNormSection t) := by
  classical
  obtain ⟨S, hS⟩ := sAdeleSchwartzToGlobal_exhaustive ℚ g
  obtain ⟨k, hk⟩ := LinearMap.mem_range.mp hS
  have hSS' : S ⊆ S ∪ Sχ := Finset.subset_union_left
  have hχS' : Sχ ⊆ S ∪ Sχ := Finset.subset_union_right
  have hk' : sAdeleSchwartzToGlobal ℚ (S ∪ Sχ) (sAdeleSchwartzTransition ℚ hSS' k) = g := by
    rw [← hk]
    exact LinearMap.congr_fun (sAdeleSchwartzToGlobal_comp ℚ hSS') k
  have hT := exists_tensorRep (S ∪ Sχ) (sAdeleSchwartzTransition ℚ hSS' k)
  obtain ⟨κ, hT⟩ := hT
  obtain ⟨hκ, hT⟩ := hT
  obtain ⟨α, hT⟩ := hT
  obtain ⟨β, hrep⟩ := hT
  have ha := fun i ↦ archSB_eq_schwartz' (α i)
  choose a ha using ha
  have hg : g = ∑ i, ratPhi (S ∪ Sχ) (a i) (β i) := by
    refine SchwartzBruhat.ext fun x ↦ ?_
    obtain ⟨x, rfl⟩ : ∃ y : 𝔸, Multiplicative.ofAdd y = x := ⟨x.toAdd, rfl⟩
    rw [← hk', sAdeleSchwartzToGlobal_apply, sb_sum_apply'']
    simp only [ratPhi_apply]
    split_ifs with h
    · rw [hrep]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [ha]
      rfl
    · simp
  have hF := fun i ↦ ratPhi_dirichlet_rep_general hχ hN (S ∪ Sχ) hχS' (a i) (β i)
  choose F hF using hF
  have hG : IsDirichletThetaRep hχ g (∑ i, F i) := by
    rw [hg]
    exact IsDirichletThetaRep.sum hN _ fun i _ ↦ hF i
  refine ⟨dirichletParityPart χ (∑ i, F i), hasDirichletParity_dirichletParityPart χ _,
    fun t k ↦ ?_⟩
  rw [hG t k, ratBridge_dirichletTest_theta hχ hN, ratBridge_dirichlet_parity hχ hN]

end Unrestricted

end RiemannMasullo.Isolated
