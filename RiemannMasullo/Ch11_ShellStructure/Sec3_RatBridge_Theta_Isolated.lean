module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_DirichletFixedBox_Isolated
public import RiemannMasullo.Ch11_ShellStructure.Sec3_FixedBox
public import RiemannMasullo.Ch11_ShellStructure.RationalThetaLattice
public import RiemannMasullo.External.AlgebraicNumberTheoryLean.Chebotarev.DirichletHecke

/-!
# The adelic Dirichlet test over ℚ and its homogeneous theta

Workstream B for #7351, stage 1: the bridge over `ℚ`, for a primitive Dirichlet character `χ`
of conductor `N > 1`, from the global objects of (11.3.1.3), p. 494 (`homogeneousAdelicTheta`,
`primaryDivisorialStripNorm`) to the rational model of `Sec3_DirichletFixedBox_Isolated`.

* `ratDirichletIdeleChar`: the idelic character `ψ` attached to `χ`, with `ψ(x) = χ(r(x))⁻¹`.
* `dirTest χ f`: the real test `f` at infinity, `χ_q · 1_{ℤ_q^×}` at each `q ∣ N` (the inverse of
  the local component of `ψ` on the units), and the integer indicator elsewhere.
* `ratBridge_dirichletTest_theta`: its homogeneous theta for `ω = ψ|_{C₁}` at `τ(t) · k` is
  `ω(k)⁻¹ · mass · twistedRadialTheta χ f t`.
* `ratBridge_dirichlet_parity`: the twisted theta only sees the `χ`-parity part of `f`.
* `ratBridge_stripNorm`: the half-twisted strip norm of `primaryDivisorialStripNorm` is `mass³`
  times the squared norm of the half-logarithmic profile in `CompactIntervalSobolev`.

Nothing imports this module; all declarations live in `namespace RiemannMasullo.Isolated`.
-/

@[expose] public noncomputable section

open Complex Filter Function MeasureTheory NumberField Set Topology IsDedekindDomain
open scoped NNReal SchwartzMap FourierTransform NumberField.AdeleRing TensorProduct

namespace RiemannMasullo.Isolated

open NumberFieldKB.Chebotarev.RatIdele

set_option quotPrecheck false

local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ
local notation "Cℚ" => IdeleClassGroup (𝓞 ℚ) ℚ
local notation "Bℚ" => SchwartzBruhat (Multiplicative 𝔸)
local notation "B∞" => SchwartzBruhat (Multiplicative (InfiniteAdeleRing ℚ))
local notation "realCoord" =>
  InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "Vℚ" => HeightOneSpectrum (𝓞 ℚ)

/-! ### The real test at the archimedean place -/

section Arch

/-- A real Schwartz function, read in the unique archimedean coordinate, is a Schwartz–Bruhat
test on the infinite adeles of `ℚ`. -/
theorem ratBridge_archTest_mem (f : 𝓢(ℝ, ℂ)) :
    (fun x : Multiplicative (InfiniteAdeleRing ℚ) ↦ f (realCoord (x.toAdd Rat.infinitePlace))) ∈
      schwartzBruhatSubmodule (Multiplicative (InfiniteAdeleRing ℚ)) := by
  classical
  let : Unique {w : InfinitePlace ℚ // w.IsReal} :=
    uniqueOfSubsingleton ⟨Rat.infinitePlace, Rat.isReal_infinitePlace⟩
  let : IsEmpty {w : InfinitePlace ℚ // w.IsComplex} :=
    ⟨fun w ↦ (InfinitePlace.not_isReal_iff_isComplex.mpr w.property) (IsTotallyReal.isReal w.val)⟩
  let e := (ContinuousLinearEquiv.prodUnique ℝ
      ({w : InfinitePlace ℚ // w.IsReal} → ℝ) ({w : InfinitePlace ℚ // w.IsComplex} → ℂ)).trans
    (ContinuousLinearEquiv.piUnique ℝ (fun _ : {w : InfinitePlace ℚ // w.IsReal} ↦ ℝ))
  apply (mem_archimedeanSchwartzBruhat_iff (F := ℚ)
    (fun x : InfiniteAdeleRing ℚ ↦ f (realCoord (x Rat.infinitePlace)))).2
  exact ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f, fun _ ↦ rfl⟩

/-- The archimedean test of a real Schwartz function. -/
def archTest (f : 𝓢(ℝ, ℂ)) : B∞ :=
  ⟨_, ratBridge_archTest_mem f⟩

theorem archTest_apply (f : 𝓢(ℝ, ℂ)) (x : InfiniteAdeleRing ℚ) :
    archTest f (Multiplicative.ofAdd x) = f (realCoord (x Rat.infinitePlace)) := rfl

end Arch

/-! ### The places over the conductor -/

section Places

open Classical in
/-- The finite places of `ℚ` over the primes dividing `N`. -/
def ratDirichletS (N : ℕ) : Finset Vℚ :=
  N.primeFactors.attach.image fun p ↦ placeOf p.1 (Nat.prime_of_mem_primeFactors p.2)

theorem mem_ratDirichletS {N : ℕ} (hN : N ≠ 0) (v : Vℚ) :
    v ∈ ratDirichletS N ↔ pr v ∣ N := by
  classical
  unfold ratDirichletS
  constructor
  · intro hv
    obtain ⟨⟨p, hp⟩, -, rfl⟩ := Finset.mem_image.mp hv
    rw [pr_placeOf]
    exact Nat.dvd_of_mem_primeFactors hp
  · intro hv
    refine Finset.mem_image.mpr ⟨⟨pr v, Nat.mem_primeFactors.mpr ⟨pr_prime v, hv, hN⟩⟩,
      Finset.mem_attach _ _, ?_⟩
    exact ((eq_placeOf_iff v (pr v) (pr_prime v)).mpr rfl).symm

end Places

/-! ### The idelic character of a primitive Dirichlet character -/

section Character

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- The unitary idelic character `ψ` of `ℚ` attached to a primitive Dirichlet character, with
`ψ(x) = χ(r(x))⁻¹` on ideles (`ideleChar`). -/
def ratDirichletIdeleChar (hχ : χ.IsPrimitive) : PontryaginDual Cℚ :=
  (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hχ).choose

theorem ratDirichletIdeleChar_mk (hχ : χ.IsPrimitive) (x : IdQ) :
    (ratDirichletIdeleChar hχ (QuotientGroup.mk x) : ℂ) = ((ideleChar N χ x : ℂˣ) : ℂ) :=
  (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hχ).choose_spec.2.1 x

/-- The restriction `ω` of `ψ` to the norm-one idele classes. -/
def ratDirichletNormOneChar (hχ : χ.IsPrimitive) :
    PontryaginDual (ideleClassNorm ℚ).ker :=
  (ratDirichletIdeleChar hχ).comp ⟨(ideleClassNorm ℚ).ker.subtype, continuous_subtype_val⟩

theorem ratDirichletNormOneChar_apply (hχ : χ.IsPrimitive) (h : (ideleClassNorm ℚ).ker) :
    ratDirichletNormOneChar hχ h = ratDirichletIdeleChar hχ h.val := rfl

/-- The local component of `ψ` at a finite place, as a quasi-character of the local units. -/
def ratDirichletLocalChar (hχ : χ.IsPrimitive) (v : Vℚ) :
    QuasiCharacter (v.adicCompletion ℚ)ˣ :=
  (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp
    ((ratDirichletIdeleChar hχ).comp
      ⟨IdeleClassGroup.ofAdicCompletion (𝓞 ℚ) ℚ v, continuous_ideleClass_ofAdicCompletion ℚ v⟩)

theorem ratDirichletLocalChar_apply (hχ : χ.IsPrimitive) (v : Vℚ) (u : (v.adicCompletion ℚ)ˣ) :
    ratDirichletLocalChar hχ v u =
      ((ideleChar N χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ v u) : ℂˣ) : ℂ) :=
  ratDirichletIdeleChar_mk hχ _

end Character

/-! ### The unit-character test at a finite place -/

section UnitTest

/-- A complex number all of whose powers lie within `r < 1` of one is one. -/
private theorem eq_one_of_forall_norm_pow_sub_one_le' {z : ℂ} {r : ℝ} (hr : r < 1)
    (h : ∀ n : ℕ, ‖z ^ n - 1‖ ≤ r) : z = 1 := by
  by_contra hz
  have hz1 : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  have hpos : 0 < (1 - r) * ‖z - 1‖ := mul_pos (sub_pos.mpr hr) hz1
  obtain ⟨N, hN⟩ := exists_nat_gt (r / ((1 - r) * ‖z - 1‖))
  rw [div_lt_iff₀ hpos] at hN
  have hre : (N : ℝ) * (1 - r) ≤ (∑ n ∈ Finset.range N, z ^ n).re := by
    rw [Complex.re_sum]
    have hle : ∀ n ∈ Finset.range N, 1 - r ≤ (z ^ n).re := fun n _ ↦ by
      have h1 := (abs_le.mp ((Complex.abs_re_le_norm (z ^ n - 1)).trans (h n))).1
      rw [Complex.sub_re, Complex.one_re] at h1
      linarith
    simpa using Finset.card_nsmul_le_sum _ _ _ hle
  have hbound : (∑ n ∈ Finset.range N, z ^ n).re * ‖z - 1‖ ≤ r :=
    calc _ ≤ ‖∑ n ∈ Finset.range N, z ^ n‖ * ‖z - 1‖ :=
          mul_le_mul_of_nonneg_right (Complex.re_le_norm _) hz1.le
      _ = ‖z ^ N - 1‖ := by rw [← norm_mul, geom_sum_mul]
      _ ≤ r := h N
  nlinarith [mul_le_mul_of_nonneg_right hre hz1.le]

/-- A continuous character of the units of a nonarchimedean normed field is trivial near one. -/
private theorem exists_forall_norm_sub_one_lt_map_eq_one' {K : Type*} [NormedField K]
    [IsUltrametricDist K] (c : Kˣ →ₜ* ℂ) :
    ∃ δ > 0, δ ≤ 1 ∧ ∀ t : Kˣ, ‖(t : K) - 1‖ < δ → c t = 1 := by
  have hc : Tendsto c (nhds 1) (nhds 1) := by
    simpa only [map_one] using (map_continuous c).tendsto 1
  have hU := hc (Metric.ball_mem_nhds (1 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2))
  rw [Units.isEmbedding_val₀.nhds_eq_comap, mem_map, mem_comap] at hU
  obtain ⟨s, hs, hsU⟩ := hU
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  refine ⟨min ε 1, lt_min hε one_pos, min_le_right _ _, fun t ht ↦ ?_⟩
  have ht1' : ‖(t : K) - 1‖ < 1 := ht.trans_le (min_le_right _ _)
  have ht1 : ‖(t : K)‖ = 1 := by
    have hne : ‖(1 : K)‖ ≠ ‖(t : K) - 1‖ := by rw [norm_one]; exact ht1'.ne'
    have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
    rwa [add_sub_cancel, norm_one, max_eq_left ht1'.le] at this
  have hpow (n : ℕ) : ‖((t ^ n : Kˣ) : K) - 1‖ < min ε 1 := by
    induction n with
    | zero => simpa using lt_min hε one_pos
    | succ n ih =>
      rw [Units.val_pow_eq_pow_val] at ih ⊢
      have he : (t : K) ^ (n + 1) - 1 = (t : K) ^ n * ((t : K) - 1) + ((t : K) ^ n - 1) := by
        ring
      rw [he]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ih)
      rwa [norm_mul, norm_pow, ht1, one_pow, one_mul]
  refine eq_one_of_forall_norm_pow_sub_one_le' (r := 1 / 2) (by norm_num) fun n ↦ ?_
  have hmem : ((t ^ n : Kˣ) : K) ∈ s := hball (by
    rw [Metric.mem_ball, dist_eq_norm, Units.val_one]
    exact (hpow n).trans_le (min_le_left _ _))
  have hlt := Metric.mem_ball.mp (hsU hmem)
  rw [dist_eq_norm, map_pow] at hlt
  exact hlt.le

/-- An element of a finite completion of `ℚ` is an integral unit exactly when its norm is one. -/
private theorem mem_integerUnits_iff_norm_eq_one' (v : Vℚ) (x : v.adicCompletion ℚ) :
    x ∈ Units.val '' ((v.adicCompletionIntegers ℚ).units : Set (v.adicCompletion ℚ)ˣ) ↔
      ‖x‖ = 1 := by
  have he1 : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 1 :=
    (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v).ne'
  rw [NumberField.FinitePlace.norm_def, NNReal.coe_eq_one,
    WithZeroMulInt.toNNReal_eq_one_iff _ _ he1]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha
  · intro hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    exact ⟨Units.mk0 x hx0,
      HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr hx, rfl⟩

open Classical in
/-- The function `c⁻¹ · 1_{𝒪_v^×}` on a finite completion of `ℚ`. -/
def unitCharTestFun (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) : ℂ :=
  (Units.val '' ((v.adicCompletionIntegers ℚ).units : Set (v.adicCompletion ℚ)ˣ)).indicator
    (fun y ↦ if hy : y ≠ 0 then (c (Units.mk0 y hy))⁻¹ else 0) x

/-- `c⁻¹ · 1_{𝒪_v^×}` is locally constant with compact support. -/
theorem unitCharTestFun_lc (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) :
    IsLocallyConstant (unitCharTestFun v c) ∧ HasCompactSupport (unitCharTestFun v c) := by
  classical
  set O : Set (v.adicCompletion ℚ) := ↑(v.adicCompletionIntegers ℚ) with hO
  have hOc : IsCompact O :=
    isCompact_iff_compactSpace.mpr (compactSpace_adicCompletionIntegers (K := ℚ) v)
  set U₀ : Set (v.adicCompletion ℚ) :=
    Units.val '' ((v.adicCompletionIntegers ℚ).units : Set (v.adicCompletion ℚ)ˣ) with hU₀
  have hU₀O : U₀ ⊆ O := by
    rintro _ ⟨a, ha, rfl⟩
    exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha).le
  refine ⟨(IsLocallyConstant.iff_exists_open _).mpr fun x ↦ ?_,
    HasCompactSupport.intro hOc fun x hx ↦ indicator_of_notMem (fun h ↦ hx (hU₀O h)) _⟩
  by_cases hx : x ∈ U₀
  · obtain ⟨δ, hδ, hδ1, hδc⟩ := exists_forall_norm_sub_one_lt_map_eq_one' c
    have hx1 : ‖x‖ = 1 := (mem_integerUnits_iff_norm_eq_one' v x).mp hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx1
    refine ⟨Metric.ball x δ, Metric.isOpen_ball, Metric.mem_ball_self hδ, fun y hy ↦ ?_⟩
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hy1 : ‖y‖ = 1 := by
      have hne : ‖x‖ ≠ ‖y - x‖ := by rw [hx1]; exact (hy.trans_le hδ1).ne'
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
      rwa [add_sub_cancel, hx1, max_eq_left (hy.trans_le hδ1).le] at this
    have hy0 : y ≠ 0 := by
      rintro rfl
      simp at hy1
    have hyU : y ∈ U₀ := (mem_integerUnits_iff_norm_eq_one' v y).mpr hy1
    simp only [unitCharTestFun]
    rw [← hU₀, indicator_of_mem hyU, indicator_of_mem hx, dite_eq_left hy0, dite_eq_left hx0]
    have ht : Units.mk0 y hy0 = Units.mk0 x hx0 * Units.mk0 (y / x) (div_ne_zero hy0 hx0) :=
      Units.ext (by simp [mul_div_cancel₀ _ hx0])
    have hsmall : ‖((Units.mk0 (y / x) (div_ne_zero hy0 hx0) : (v.adicCompletion ℚ)ˣ) :
        v.adicCompletion ℚ) - 1‖ < δ := by
      rw [Units.val_mk0, show y / x - 1 = (y - x) / x by field_simp, norm_div, hx1, div_one]
      exact hy
    rw [ht, map_mul, hδc _ hsmall, mul_one]
  · refine ⟨U₀ᶜ, ?_, hx, fun y hy ↦ by
      simp only [unitCharTestFun]
      rw [← hU₀, indicator_of_notMem hy, indicator_of_notMem hx]⟩
    have hsphere : U₀ = Metric.sphere 0 1 := by
      ext y
      rw [mem_sphere_zero_iff_norm]
      exact mem_integerUnits_iff_norm_eq_one' v y
    rw [hsphere]
    exact Metric.isClosed_sphere.isOpen_compl

/-- The test `c⁻¹ · 1_{𝒪_v^×}` at a finite place, as a Schwartz–Bruhat function. For a
ramified `c` this is `finiteStandardGaussian v c` (Definition 3.4.3.2(3), p. 152). -/
def unitCharTest (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ) :
    SchwartzBruhat (Multiplicative (v.adicCompletion ℚ)) :=
  ((mem_finitePlaceSchwartz_iff ℚ v (unitCharTestFun v c)).mpr (unitCharTestFun_lc v c)).choose

theorem unitCharTest_apply (v : Vℚ) (c : QuasiCharacter (v.adicCompletion ℚ)ˣ)
    (x : v.adicCompletion ℚ) : unitCharTest v c (Multiplicative.ofAdd x) = unitCharTestFun v c x :=
  ((mem_finitePlaceSchwartz_iff ℚ v (unitCharTestFun v c)).mpr (unitCharTestFun_lc v c)).choose_spec x

end UnitTest

/-! ### The adelic Dirichlet test -/

section DirTest

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

local notation "Sχ" => ratDirichletS N

/-- The `S`-local Dirichlet test: `f` at infinity and `χ_q · 1_{ℤ_q^×}` at each `q ∣ N`, where
`χ_q` is the inverse of the local component of `ψ` on the units. -/
def dirSLocalTest (hχ : χ.IsPrimitive) (f : 𝓢(ℝ, ℂ)) :
    SchwartzBruhat (Multiplicative (SAdeleRing ℚ Sχ)) :=
  let W := FinestLocallyConvex (⨂[ℂ] w : Sχ,
    SchwartzBruhat (Multiplicative (w.val.adicCompletion ℚ)))
  let g : W := ⨂ₜ[ℂ] w : Sχ, unitCharTest w.val (ratDirichletLocalChar hχ w.val)
  (sAdeleSchwartz_inductiveTensor_equiv ℚ Sχ).choose (archTest f ⊗ₜ[ℂ] g)

theorem dirSLocalTest_apply (hχ : χ.IsPrimitive) (f : 𝓢(ℝ, ℂ)) (x : SAdeleRing ℚ Sχ) :
    dirSLocalTest hχ f (Multiplicative.ofAdd x) =
      f (realCoord (x.1 Rat.infinitePlace)) *
        ∏ w : Sχ, unitCharTestFun w.val (ratDirichletLocalChar hχ w.val) (x.2 w) := by
  rw [dirSLocalTest, (sAdeleSchwartz_inductiveTensor_equiv ℚ Sχ).choose_spec]
  simp only [archTest_apply, unitCharTest_apply]

/-- The global Dirichlet test: the `S`-local test with integer indicators outside `S`. -/
def dirTest (hχ : χ.IsPrimitive) (f : 𝓢(ℝ, ℂ)) : Bℚ :=
  sAdeleSchwartzToGlobal ℚ Sχ (dirSLocalTest hχ f)

open Classical in
theorem dirTest_apply (hχ : χ.IsPrimitive) (f : 𝓢(ℝ, ℂ)) (x : 𝔸) :
    dirTest hχ f (Multiplicative.ofAdd x) =
      if ∀ w : Vℚ, w ∉ Sχ → x.2 w ∈ w.adicCompletionIntegers ℚ then
        f (realCoord (x.1 Rat.infinitePlace)) *
          ∏ w : Sχ, unitCharTestFun w.val (ratDirichletLocalChar hχ w.val) (x.2 w.val)
      else 0 := by
  rw [dirTest, sAdeleSchwartzToGlobal_apply, dirSLocalTest_apply]
  rfl

end DirTest

/-! ### Integrality and valuations of rational integers -/

section Integrality

local notation "U" => (v : Vℚ) → (v.adicCompletionIntegers ℚ)ˣ

private theorem finite_integral_iff' (x : ℚ) :
    (∀ v : Vℚ, (algebraMap ℚ 𝔸 x).2 v ∈ v.adicCompletionIntegers ℚ) ↔ ∃ n : ℤ, (n : ℚ) = x := by
  have h := diagonal_mem_integralAdelesOutside ℚ ∅ x
  simp only [integralAdelesOutside, Subring.mem_iInf, Finset.notMem_empty,
    not_false_eq_true, forall_const, Finset.coe_empty, integer_empty, Algebra.mem_bot] at h
  rw [show (∀ v : Vℚ, (algebraMap ℚ 𝔸 x).2 v ∈ v.adicCompletionIntegers ℚ) ↔
    ∃ r : 𝓞 ℚ, algebraMap (𝓞 ℚ) ℚ r = x from h]
  exact ⟨fun ⟨r, hr⟩ ↦ ⟨Rat.ringOfIntegersEquiv r, (Rat.ringOfIntegersEquiv_apply_coe r).trans hr⟩,
    fun ⟨n, hn⟩ ↦ ⟨n, (map_intCast _ n).trans hn⟩⟩

/-- The finite component of a rational number in the adeles is its image in the completion. -/
theorem ratBridge_algebraMap_fin (x : ℚ) (v : Vℚ) :
    (algebraMap ℚ 𝔸 x).2 v = ((x : ℚ) : v.adicCompletion ℚ) :=
  (ratCast_eq v x).symm

/-- The membership of an integer in the prime ideal of a place of `ℚ`. -/
private theorem intCast_mem_asIdeal_iff (v : Vℚ) (n : ℤ) :
    ((n : 𝓞 ℚ) ∈ v.asIdeal) ↔ (pr v : ℤ) ∣ n := by
  rw [Int.natCast_dvd]
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    simpa only [Int.cast_natCast, Int.natAbs_natCast] using natCast_mem_asIdeal_iff v n.natAbs
  · rw [h, Int.cast_neg, Ideal.neg_mem_iff, Int.natAbs_neg]
    simpa only [Int.cast_natCast, Int.natAbs_natCast] using natCast_mem_asIdeal_iff v n.natAbs

private theorem valued_intCast_eq (v : Vℚ) (n : ℤ) :
    Valued.v (((n : ℚ) : ℚ) : v.adicCompletion ℚ) = v.intValuation (n : 𝓞 ℚ) := by
  rw [valued_ratCast, show (n : ℚ) = algebraMap (𝓞 ℚ) ℚ (n : 𝓞 ℚ) by simp, HeightOneSpectrum.valuation_of_algebraMap]

/-- A rational integer is integral at every finite place. -/
theorem ratBridge_valued_intCast_le_one (v : Vℚ) (n : ℤ) :
    Valued.v (((n : ℚ) : ℚ) : v.adicCompletion ℚ) ≤ 1 := by
  rw [valued_intCast_eq]
  exact v.intValuation_le_one _

/-- A rational integer is a unit at a finite place exactly when the prime does not divide it. -/
theorem ratBridge_valued_intCast_eq_one_iff (v : Vℚ) (n : ℤ) :
    Valued.v (((n : ℚ) : ℚ) : v.adicCompletion ℚ) = 1 ↔ ¬ (pr v : ℤ) ∣ n := by
  rw [valued_intCast_eq, HeightOneSpectrum.intValuation_eq_one_iff, intCast_mem_asIdeal_iff]

end Integrality

/-! ### The idelic character on ideles with unit components -/

section Residue

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

private theorem valued_inv_component (z : IdQ) (v : Vℚ) (hz : Valued.v ((z : 𝔸).2 v) = 1) :
    Valued.v (((z⁻¹ : IdQ) : 𝔸).2 v) = 1 := by
  have h : ((z⁻¹ : IdQ) : 𝔸).2 v = ((compV v z)⁻¹ : (v.adicCompletion ℚ)ˣ) := by
    rw [← map_inv, coe_compV]
  rw [h, Units.val_inv_eq_inv_val, map_inv₀, coe_compV, hz, inv_one]

private theorem redP_intCast {p : ℕ} {hp : p.Prime} {e : ℕ} (n : ℤ) :
    redP p hp e (((n : ℚ) : ℚ) : Kp p hp) = n := by
  rw [redP_of_le (ratBridge_valued_intCast_le_one _ n)]
  have : (⟨(((n : ℚ) : ℚ) : Kp p hp), ratBridge_valued_intCast_le_one _ n⟩ : Op p hp) =
      (n : Op p hp) := Subtype.ext (by simp)
  rw [this, map_intCast]

/-- On an idele with positive real part, unit finite components, and component `n⁻¹` at the
primes dividing `N`, the idelic character `x ↦ χ(r(x))⁻¹` takes the value `χ(n)`. -/
private theorem ideleChar_eq_of_components (z : IdQ) (n : ℤ) (h0 : 0 < realPart z)
    (hz : ∀ v : Vℚ, Valued.v ((z : 𝔸).2 v) = 1)
    (hS : ∀ p : N.primeFactors, (z : 𝔸).2 (placeP N p) * (((n : ℚ) : ℚ) : _) = 1) :
    ((ideleChar N χ z : ℂˣ) : ℂ) = χ n := by
  have hrat : ratPart z = 1 :=
    ratPart_eq_one_of h0 fun v ↦ ⟨(hz v).le, (valued_inv_component z v (hz v)).le⟩
  have hunit : unitPart z = z := by simp [unitPart_apply, hrat]
  have hres : resMod N z * (n : ZMod N) = 1 := by
    rw [resMod_apply, resModFun, hunit,
      ← (map_intCast (ZMod.equivPi N (NeZero.ne N)).symm n), ← map_mul,
      ← map_one (ZMod.equivPi N (NeZero.ne N)).symm]
    congr 1
    funext p
    rw [Pi.mul_apply, Pi.intCast_apply, Pi.one_apply, coe_compV,
      ← redP_intCast (hp := Nat.prime_of_mem_primeFactors p.2) (e := N.factorization p) n,
      ← redP_mul (hz _).le (ratBridge_valued_intCast_le_one _ n), hS p, redP_one]
  rw [coe_ideleChar, MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits]
  have h1 : χ (resMod N z) * χ (n : ZMod N) = 1 := by rw [← map_mul, hres, map_one]
  exact (eq_inv_of_mul_eq_one_right h1).symm

end Residue

/-! ### One term of the theta series -/

section Term

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

local notation "Sχ" => ratDirichletS N
local notation "U" => (v : Vℚ) → (v.adicCompletionIntegers ℚ)ˣ

/-- `realPart` as a monoid homomorphism. -/
private def realPartHom : IdQ →* ℝ where
  toFun := realPart
  map_one' := realPart_one
  map_mul' := realPart_mul

/-- `χ(n) = 0` when a prime of the conductor divides `n`. -/
private theorem dirichlet_apply_eq_zero_of_dvd (hN : N ≠ 0) {w : Vℚ} (hw : w ∈ Sχ) {n : ℤ}
    (hn : (pr w : ℤ) ∣ n) : χ n = 0 := by
  apply MulChar.map_nonunit
  intro hu
  have hpN : pr w ∣ N := (mem_ratDirichletS hN w).mp hw
  have : Fact (pr w).Prime := ⟨pr_prime w⟩
  have h := hu.map (ZMod.castHom hpN (ZMod (pr w)))
  rw [map_intCast, (ZMod.intCast_zmod_eq_zero_iff_dvd n (pr w)).mpr hn] at h
  exact not_isUnit_zero h

private theorem valued_unit (w : Vℚ) (u : (w.adicCompletionIntegers ℚ)ˣ) :
    Valued.v (u.val.val : w.adicCompletion ℚ) = 1 := by
  have ha : Valued.v (u.val.val : w.adicCompletion ℚ) ≤ 1 := u.val.property
  have hb : Valued.v (u.inv.val : w.adicCompletion ℚ) ≤ 1 := u.inv.property
  have hab : (u.val.val : w.adicCompletion ℚ) * u.inv.val = 1 := congrArg Subtype.val u.val_inv
  refine le_antisymm ha ?_
  calc (1 : _) = Valued.v ((u.val.val : w.adicCompletion ℚ) * u.inv.val) := by rw [hab, map_one]
    _ = Valued.v (u.val.val : w.adicCompletion ℚ) * Valued.v (u.inv.val : w.adicCompletion ℚ) :=
        map_mul _ _ _
    _ ≤ Valued.v (u.val.val : w.adicCompletion ℚ) * 1 := mul_le_mul' le_rfl hb
    _ = _ := mul_one _

/-- The unit of a completion given by an integer prime to the place times a local unit. -/
private def intUnitMul (w : Vℚ) {n : ℤ} (hn : ¬ (pr w : ℤ) ∣ n)
    (u : (w.adicCompletionIntegers ℚ)ˣ) : (w.adicCompletion ℚ)ˣ :=
  Units.mk0 ((((n : ℚ) : ℚ) : w.adicCompletion ℚ) * u.val.val) (by
    have hv : Valued.v ((((n : ℚ) : ℚ) : w.adicCompletion ℚ) * u.val.val) = 1 := by
      rw [map_mul, (ratBridge_valued_intCast_eq_one_iff w n).mpr hn, one_mul]
      exact valued_unit w u
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv)

private theorem valued_intUnitMul (w : Vℚ) {n : ℤ} (hn : ¬ (pr w : ℤ) ∣ n)
    (u : (w.adicCompletionIntegers ℚ)ˣ) : Valued.v (intUnitMul w hn u : w.adicCompletion ℚ) = 1 := by
  rw [intUnitMul, Units.val_mk0, map_mul, (ratBridge_valued_intCast_eq_one_iff w n).mpr hn, one_mul]
  exact valued_unit w u


/-- **One term of the twisted theta series.** For an idele `g` with real coordinate `t` and
integral unit finite coordinates, and a nonzero integer `n`, the value of the Dirichlet test at
`n g`, multiplied by `ψ(g)`, is `χ(n) f(n t)`. -/
private theorem dirTest_term (hχ : χ.IsPrimitive) (f : 𝓢(ℝ, ℂ)) (g : IdQ) (u : U)
    (hg : ∀ v, (g : 𝔸).2 v = (u v).val.val) {t : ℝ}
    (ht : realCoord ((g : 𝔸).1 Rat.infinitePlace) = t) (ht0 : 0 < t) (n : ℤ) :
    dirTest hχ f (Multiplicative.ofAdd (algebraMap ℚ 𝔸 (n : ℚ) * (g : 𝔸))) *
        ((ideleChar N χ g : ℂˣ) : ℂ) = χ n * f ((n : ℝ) * t) := by
  classical
  have hN : N ≠ 0 := NeZero.ne N
  have hfin (w : Vℚ) : (algebraMap ℚ 𝔸 (n : ℚ) * (g : 𝔸)).2 w =
      (((n : ℚ) : ℚ) : w.adicCompletion ℚ) * (u w).val.val := by
    change (algebraMap ℚ 𝔸 (n : ℚ)).2 w * (g : 𝔸).2 w = _
    rw [ratBridge_algebraMap_fin, hg]
  have hreal : realCoord ((algebraMap ℚ 𝔸 (n : ℚ) * (g : 𝔸)).1 Rat.infinitePlace) = (n : ℝ) * t := by
    change realCoord (algebraMap ℚ Rat.infinitePlace.Completion (n : ℚ) *
      (g : 𝔸).1 Rat.infinitePlace) = _
    rw [map_mul, ht]
    simp
  have hcond : ∀ w : Vℚ, w ∉ Sχ →
      (algebraMap ℚ 𝔸 (n : ℚ) * (g : 𝔸)).2 w ∈ w.adicCompletionIntegers ℚ := by
    intro w _
    rw [hfin]
    exact (w.adicCompletionIntegers ℚ).toSubring.mul_mem
      (ratBridge_valued_intCast_le_one w n) (u w).val.property
  rw [dirTest_apply, ite_eq_left hcond, hreal]
  by_cases hdiv : ∃ w : Sχ, (pr w.val : ℤ) ∣ n
  · obtain ⟨w, hw⟩ := hdiv
    rw [dirichlet_apply_eq_zero_of_dvd hN w.property hw, zero_mul]
    have hzero : unitCharTestFun w.val (ratDirichletLocalChar hχ w.val)
        ((algebraMap ℚ 𝔸 (n : ℚ) * (g : 𝔸)).2 w.val) = 0 := by
      rw [unitCharTestFun, hfin]
      apply indicator_of_notMem
      rintro ⟨a, ha, hae⟩
      have h1 := HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha
      rw [hae, map_mul, valued_unit] at h1
      exact (ratBridge_valued_intCast_eq_one_iff w.val n).mp (by simpa using h1) hw
    rw [Finset.prod_eq_zero (Finset.mem_univ w) hzero, mul_zero, zero_mul]
  · push Not at hdiv
    -- The local factors are the inverse local characters at `n g_w`.
    let a (w : Sχ) : (w.val.adicCompletion ℚ)ˣ := intUnitMul w.val (hdiv w) (u w.val)
    have hfac (w : Sχ) : unitCharTestFun w.val (ratDirichletLocalChar hχ w.val)
        ((algebraMap ℚ 𝔸 (n : ℚ) * (g : 𝔸)).2 w.val) =
          ((ideleChar N χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ w.val (a w)) : ℂˣ) : ℂ)⁻¹ := by
      have hmem : (a w : w.val.adicCompletion ℚ) ∈ Units.val ''
          ((w.val.adicCompletionIntegers ℚ).units : Set (w.val.adicCompletion ℚ)ˣ) := by
        refine ⟨a w, ?_, rfl⟩
        exact HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mpr
          (valued_intUnitMul _ _ _)
      have hval : (algebraMap ℚ 𝔸 (n : ℚ) * (g : 𝔸)).2 w.val = (a w : w.val.adicCompletion ℚ) := by
        rw [hfin]
        rfl
      rw [unitCharTestFun, hval, indicator_of_mem hmem]
      simp only [ne_eq, (a w).ne_zero, not_false_eq_true, ↓reduceDIte, Units.mk0_val,
        ratDirichletLocalChar_apply]
    simp_rw [hfac]
    let P : IdQ := ∏ w : Sχ, IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ w.val (a w)
    let z : IdQ := g * P⁻¹
    have hprod : (∏ w : Sχ,
        ((ideleChar N χ (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ w.val (a w)) : ℂˣ) : ℂ)⁻¹) *
          ((ideleChar N χ g : ℂˣ) : ℂ) = ((ideleChar N χ z : ℂˣ) : ℂ) := by
      simp only [z, P, map_mul, map_inv, map_prod, Units.val_mul, Units.coe_prod,
        Units.val_inv_eq_inv_val]
      rw [Finset.prod_inv_distrib, mul_comm]
    -- Components of `P`.
    have hPv (v : Vℚ) : compV v P = ∏ w : Sχ,
        compV v (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ w.val (a w)) := map_prod _ _ _
    have hPfactor (v : Vℚ) (w : Sχ) :
        Valued.v (compV v (IdeleGroup.ofAdicCompletion (𝓞 ℚ) ℚ w.val (a w)) :
          v.adicCompletion ℚ) = 1 := by
      by_cases hvw : v = w.val
      · subst hvw
        rw [compV_ofAdicCompletion_self]
        exact valued_intUnitMul _ _ _
      · rw [compV_ofAdicCompletion_ne hvw, Units.val_one, map_one]
    have hPval (v : Vℚ) : Valued.v (compV v P : v.adicCompletion ℚ) = 1 := by
      rw [hPv, Units.coe_prod, map_prod]
      exact Finset.prod_eq_one fun w _ ↦ hPfactor v w
    have hzv (v : Vℚ) : (z : 𝔸).2 v = (u v).val.val * ((compV v P : v.adicCompletion ℚ))⁻¹ := by
      rw [← coe_compV, map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, coe_compV, hg]
    have hz : ∀ v : Vℚ, Valued.v ((z : 𝔸).2 v) = 1 := fun v ↦ by
      rw [hzv, map_mul, map_inv₀, hPval, inv_one, mul_one, valued_unit]
    have hreal0 : 0 < realPart z := by
      have hPre : realPart P = 1 := by
        change realPartHom P = 1
        simp only [P, map_prod]
        exact Finset.prod_eq_one fun w _ ↦ realPart_ofAdicCompletion _ _
      have hgz : realPart g = realPart z * realPart P := by
        rw [← realPart_mul]
        simp [z]
      rw [hPre, mul_one] at hgz
      have hgt : realPart g = t := ht
      rw [← hgz, hgt]
      exact ht0
    have hS : ∀ p : N.primeFactors, (z : 𝔸).2 (placeP N p) * (((n : ℚ) : ℚ) : _) = 1 := by
      intro p
      have hmemS : placeP N p ∈ Sχ :=
        (mem_ratDirichletS hN _).mpr (by rw [pr_placeOf]; exact Nat.dvd_of_mem_primeFactors p.2)
      have hPp : (compV (placeP N p) P : (placeP N p).adicCompletion ℚ) =
          (((n : ℚ) : ℚ) : _) * (u (placeP N p)).val.val := by
        rw [hPv, Finset.prod_eq_single ⟨placeP N p, hmemS⟩]
        · rw [compV_ofAdicCompletion_self]
          rfl
        · intro w _ hw
          rw [compV_ofAdicCompletion_ne (fun h ↦ hw (Subtype.ext h.symm))]
        · intro h
          exact (h (Finset.mem_univ _)).elim
      have hu0 : (u (placeP N p)).val.val ≠ 0 := fun h ↦ by
        have := valued_unit _ (u (placeP N p))
        rw [h, map_zero] at this
        exact zero_ne_one this
      have hn0' : (((n : ℚ) : ℚ) : (placeP N p).adicCompletion ℚ) ≠ 0 := fun h ↦ by
        have := (ratBridge_valued_intCast_eq_one_iff _ n).mpr (hdiv ⟨placeP N p, hmemS⟩)
        rw [h, map_zero] at this
        exact zero_ne_one this
      rw [hzv, hPp]
      field_simp
    rw [mul_assoc, hprod, ideleChar_eq_of_components z n hreal0 hz hS, mul_comm]

end Term

/-! ### The twisted theta series -/

section Series

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

local notation "Sχ" => ratDirichletS N
local notation "U" => (v : Vℚ) → (v.adicCompletionIntegers ℚ)ˣ

/-- Where the Dirichlet test does not vanish at `r g`, the rational number `r` is an integer. -/
private theorem dirTest_ne_zero_integral (hχ : χ.IsPrimitive) (f : 𝓢(ℝ, ℂ)) (g : IdQ) (u : U)
    (hg : ∀ v, (g : 𝔸).2 v = (u v).val.val) (r : ℚ)
    (h : dirTest hχ f (Multiplicative.ofAdd (algebraMap ℚ 𝔸 r * (g : 𝔸))) ≠ 0) :
    ∃ n : ℤ, (n : ℚ) = r := by
  classical
  rw [dirTest_apply] at h
  split_ifs at h with hc
  · refine (finite_integral_iff' r).mp fun v ↦ ?_
    have hrg : (algebraMap ℚ 𝔸 r * (g : 𝔸)).2 v ∈ v.adicCompletionIntegers ℚ := by
      by_cases hv : v ∈ Sχ
      · have hfac := Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul h) ⟨v, hv⟩
          (Finset.mem_univ _)
        rw [unitCharTestFun] at hfac
        by_contra hnot
        apply hfac
        apply indicator_of_notMem
        rintro ⟨a, ha, hae⟩
        apply hnot
        change Valued.v ((algebraMap ℚ 𝔸 r * (g : 𝔸)).2 v) ≤ 1
        rw [← hae]
        exact (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one.mp ha).le
      · exact hc v hv
    have he : (u v).val.val * (u v).inv.val = 1 := congrArg Subtype.val (u v).val_inv
    have hm := (v.adicCompletionIntegers ℚ).toSubring.mul_mem hrg (u v).inv.property
    change ((algebraMap ℚ 𝔸 r).2 v * (g : 𝔸).2 v) * (u v).inv.val ∈ _ at hm
    change (algebraMap ℚ 𝔸 r).2 v ∈ (v.adicCompletionIntegers ℚ).toSubring
    simpa only [hg, mul_assoc, he, mul_one] using hm
  · exact (h rfl).elim

/-- **The twisted theta series.** For an idele `g` with real coordinate `t > 0` and integral unit
finite coordinates, the adelic theta of the Dirichlet test at the class of `g`, multiplied by
`ψ(g)`, is the twisted radial theta series `∑ₙ χ(n) f(n t)`. -/
private theorem hasSum_twisted_theta (hχ : χ.IsPrimitive) (hN : 1 < N) (f : 𝓢(ℝ, ℂ)) (g : IdQ)
    (u : U) (hg : ∀ v, (g : 𝔸).2 v = (u v).val.val) {t : ℝ}
    (ht : realCoord ((g : 𝔸).1 Rat.infinitePlace) = t) (ht0 : 0 < t) :
    HasSum (fun n : ℤ ↦ χ n * f ((n : ℝ) * t))
      (adelicTheta (dirTest hχ f) (QuotientGroup.mk g) * ((ideleChar N χ g : ℂˣ) : ℂ)) := by
  classical
  let c : ℂ := ((ideleChar N χ g : ℂˣ) : ℂ)
  let F (r : ℚˣ) := dirTest hχ f (Multiplicative.ofAdd (algebraMap ℚ 𝔸 (r : ℚ) * (g : 𝔸))) * c
  let G (n : ℤ) := χ n * f ((n : ℝ) * t)
  have hG0 : G 0 = 0 := by
    have : Fact (1 < N) := ⟨hN⟩
    simp only [G, Int.cast_zero, MulChar.map_zero, zero_mul]
  let i (n : Function.support G) : ℚˣ := Units.mk0 (n.val : ℚ) (by
    exact_mod_cast (show n.val ≠ 0 from fun h ↦ n.property (h ▸ hG0)))
  have hi : Injective i := by
    intro a b h
    apply Subtype.ext
    exact_mod_cast (show (a.val : ℚ) = b.val from congrArg Units.val h)
  have hval (n : Function.support G) : F (i n) = G n.val :=
    dirTest_term hχ f g u hg ht ht0 n.val
  have hcov : Function.support F ⊆ Set.range i := by
    intro r hr
    change F r ≠ 0 at hr
    obtain ⟨n, hn⟩ := dirTest_ne_zero_integral hχ f g u hg r (left_ne_zero_of_mul hr)
    have hFG : F r = G n := by
      have hrn : r = Units.mk0 (n : ℚ) (by rw [hn]; exact r.ne_zero) := Units.ext hn.symm
      rw [hrn]
      exact dirTest_term hχ f g u hg ht ht0 n
    exact ⟨⟨n, by rw [Function.mem_support, ← hFG]; exact hr⟩, Units.ext hn⟩
  have hsum : HasSum F (adelicTheta (dirTest hχ f) (QuotientGroup.mk g) * c) := by
    rw [adelicTheta_mk]
    apply HasSum.mul_right
    apply Summable.hasSum
    have H := (adelicAverage_summableUniformlyOn (dirTest hχ f) {(g, (0 : 𝔸))}
      isCompact_singleton).summable (Set.mem_singleton (g, (0 : 𝔸)))
    exact (show Summable (fun r : ℚˣ ↦ ‖dirTest hχ f (Multiplicative.ofAdd
      (algebraMap ℚ 𝔸 (r : ℚ) * (g : 𝔸)))‖) by simpa [mul_comm] using H).of_norm
  exact (hasSum_iff_hasSum_of_ne_zero_bij (f := F) (g := G) i hi hcov hval).mp hsum

end Series

/-! ### The homogeneous theta of the Dirichlet test -/

section Homogeneous

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

local notation "U" => (v : Vℚ) → (v.adicCompletionIntegers ℚ)ˣ

local instance ratBridgeClassMeasurableSpace : MeasurableSpace Cℚ := borel _

/-- The canonical norm section of the rational idele classes. -/
def ratNormSection : ℝ≥0ˣ →ₜ* Cℚ :=
  ⟨(QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 ℚ) ℚ)).comp
      (canonicalIdeleNormSection ℚ),
    QuotientGroup.continuous_mk.comp (canonicalIdeleNormSection_continuous ℚ)⟩

theorem ratNormSection_apply (t : ℝ≥0ˣ) :
    ratNormSection t = QuotientGroup.mk (canonicalIdeleNormSection ℚ t) := rfl

theorem ideleClassNorm_ratNormSection (t : ℝ≥0ˣ) : ideleClassNorm ℚ (ratNormSection t) = t :=
  canonicalIdeleNormSection_rightInverse ℚ t

/-- A finite-order character of the rational idele classes is trivial along a norm section. -/
private theorem trivial_on_section_of_isOfFinOrder' (ψ : PontryaginDual Cℚ)
    (hψ : IsOfFinOrder ψ) (τ : ℝ≥0ˣ →ₜ* Cℚ) (t : ℝ≥0ˣ) : ψ (τ t) = 1 := by
  obtain ⟨k, hk, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hψ
  let r := (t : ℝ≥0) ^ ((k : ℝ)⁻¹)
  let u : ℝ≥0ˣ := Units.mk0 r (NNReal.rpow_pos (Units.zero_lt t)).ne'
  have hu : u ^ k = t := Units.ext (NNReal.rpow_inv_natCast_pow _ hk.ne')
  rw [← hu, map_pow, map_pow]
  exact (ContinuousMonoidHom.pow_apply (ψ : Cℚ →ₜ* Circle) k (τ u)).symm.trans
    (congrArg (fun η : PontryaginDual Cℚ ↦ η (τ u)) hpow)

private theorem ratDirichletIdeleChar_section (hχ : χ.IsPrimitive) (t : ℝ≥0ˣ) :
    ratDirichletIdeleChar hχ (ratNormSection t) = 1 :=
  trivial_on_section_of_isOfFinOrder' _
    (DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hχ).choose_spec.1 _ t

private theorem norm_of_integral_unit_representative' (g : IdQ) (u : U)
    (hg : ∀ v, (g : 𝔸).2 v = (u v).val.val) {t : ℝ≥0ˣ}
    (ht : realCoord ((g : 𝔸).1 Rat.infinitePlace) = t.val) :
    ((ideleNorm ℚ g).val : ℝ) = t.val := by
  rw [((ideleNorm_spec ℚ).1 _).2, Fintype.prod_subsingleton _ Rat.infinitePlace]
  have hfin (v : Vℚ) : ‖(g : 𝔸).2 v‖ = 1 := by
    rw [hg]
    apply Valued.toNormedField.norm_eq_one_iff.mpr
    apply (HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one
      (a := Units.map (v.adicCompletionIntegers ℚ).subtype.toMonoidHom (u v))).mp
    exact ⟨(u v).val.property, (u v).inv.property⟩
  rw [finprod_eq_one_of_forall_eq_one hfin, mul_one]
  have h := (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal
    Rat.isReal_infinitePlace).norm_map_of_map_zero (map_zero _) ((g : 𝔸).1 Rat.infinitePlace)
  change ‖realCoord ((g : 𝔸).1 Rat.infinitePlace)‖ = _ at h
  rw [← h, ht]
  simp [InfinitePlace.mult, Rat.isReal_infinitePlace]

/-- At every class `h · τ(t)` with `h` of norm one, the adelic theta of the Dirichlet test times
`ω(h)` is the twisted radial theta series at `t`. -/
private theorem dirTest_theta_mul_char (hχ : χ.IsPrimitive) (hN : 1 < N) (f : 𝓢(ℝ, ℂ))
    (t : ℝ≥0ˣ) (h : (ideleClassNorm ℚ).ker) :
    adelicTheta (dirTest hχ f) (h.val * ratNormSection t) *
        (ratDirichletNormOneChar hχ h : ℂ) = twistedRadialTheta χ f t := by
  obtain ⟨e, herep⟩ := ratIdeleClassGroup_decomposition
  obtain ⟨⟨t', u⟩, hx⟩ := e.surjective (h.val * ratNormSection t)
  obtain ⟨g, harch, hfin, hclass⟩ := herep t' u
  have hnorm : t'.val = t.val := by
    have h1 : ((ideleClassNorm ℚ (QuotientGroup.mk g)).val : ℝ) = t'.val :=
      norm_of_integral_unit_representative' g u hfin harch
    rw [← hclass, hx, map_mul, show ideleClassNorm ℚ h.val = 1 from h.property, one_mul,
      ideleClassNorm_ratNormSection] at h1
    exact_mod_cast h1.symm
  have ht0 : (0 : ℝ) < t.val := NNReal.coe_pos.mpr (Units.zero_lt t)
  have hsum := hasSum_twisted_theta hχ hN f g u hfin (t := t.val)
    (harch.trans (congrArg _ hnorm)) ht0
  have hchar : (ratDirichletNormOneChar hχ h : ℂ) = ((ideleChar N χ g : ℂˣ) : ℂ) := by
    rw [ratDirichletNormOneChar_apply, ← ratDirichletIdeleChar_mk hχ g, ← hclass, hx]
    have hsplit : h.val = (h.val * ratNormSection t) * (ratNormSection t)⁻¹ := by group
    conv_lhs => rw [hsplit]
    rw [map_mul, map_inv, ratDirichletIdeleChar_section, inv_one, mul_one]
  rw [hchar, ← hx, hclass, twistedRadialTheta, hsum.tsum_eq]

local notation "mass" => ((normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal : ℂ)

/-- Paper: Definition 2.2.5.1, p. 95, and (11.3.1.3), p. 494, over `ℚ`.
**The homogeneous theta of the Dirichlet test.** For a primitive Dirichlet character `χ` of
conductor `N > 1`, with `ψ` its idelic character and `ω = ψ|_{C₁}`, the homogeneous theta of
`dirTest χ f` at the class `k · τ(t)` (`k` of norm one, `τ` the canonical norm section) is
`ω(k)⁻¹` times the norm-one Tamagawa mass times the twisted radial theta series
`∑ₘ χ(m) f(m t)` of `Sec3_DirichletFixedBox_Isolated`.
Deviation: The finite factor at `q ∣ N` is `unitCharTest`, the inverse local component of `ψ` on
the units extended by zero. For a ramified component this is `finiteStandardGaussian`; the test
is assembled from the tensor identification rather than from `sLocalStandardThetaTensor`, which
needs a quasi-character of `J_{ℚ,S}`. -/
theorem ratBridge_dirichletTest_theta (hχ : χ.IsPrimitive) (hN : 1 < N) (f : 𝓢(ℝ, ℂ))
    (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker) :
    homogeneousAdelicTheta (ratDirichletNormOneChar hχ) (dirTest hχ f)
        (k.val * ratNormSection t) =
      (ratDirichletNormOneChar hχ k : ℂ)⁻¹ * mass * twistedRadialTheta χ f t := by
  have hk : k.val * ratNormSection t = (k⁻¹).val⁻¹ * ratNormSection t := by
    rw [Subgroup.coe_inv, inv_inv]
  rw [hk, homogeneousAdelicTheta_homogeneous, map_inv, Circle.coe_inv, mul_assoc]
  congr 1
  let H := (ideleClassNorm ℚ).ker
  change (∫ h : H, adelicTheta (dirTest hχ f) (h.val * ratNormSection t) *
    (ratDirichletNormOneChar hχ h : ℂ) ∂_) = _
  simp only [dirTest_theta_mul_char hχ hN f t, integral_const, Measure.real, Complex.real_smul]

end Homogeneous

/-! ### Parity -/

section Parity

variable {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}

/-- Composition with `x ↦ -x` on real Schwartz functions. -/
def schwartzCompNeg : 𝓢(ℝ, ℂ) →L[ℂ] 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (ContinuousLinearEquiv.neg ℝ)

theorem schwartzCompNeg_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : schwartzCompNeg f x = f (-x) := rfl

theorem fourier_schwartzCompNeg (f : 𝓢(ℝ, ℂ)) (ξ : ℝ) :
    (𝓕 (schwartzCompNeg f)) ξ = (𝓕 f) (-ξ) := by
  rw [SchwartzMap.fourier_coe, SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul,
    Real.fourier_real_eq_integral_exp_smul, ← integral_neg_eq_self]
  congr 1
  funext v
  rw [schwartzCompNeg_apply, neg_neg]
  congr 3
  ring_nf

/-- The `χ`-parity part `(f + χ(-1) f(-·)) / 2` of a real Schwartz function. -/
def dirichletParityPart (χ : DirichletCharacter ℂ N) (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  (1 / 2 : ℂ) • (f + χ (-1) • schwartzCompNeg f)

theorem dirichletParityPart_apply (χ : DirichletCharacter ℂ N) (f : 𝓢(ℝ, ℂ)) (x : ℝ) :
    dirichletParityPart χ f x = (1 / 2 : ℂ) * (f x + χ (-1) * f (-x)) := rfl

theorem hasDirichletParity_dirichletParityPart (χ : DirichletCharacter ℂ N) (f : 𝓢(ℝ, ℂ)) :
    HasDirichletParity χ (dirichletParityPart χ f) := by
  intro x
  have h := dirichlet_eval_neg_one_sq χ
  rw [dirichletParityPart_apply, dirichletParityPart_apply, neg_neg]
  linear_combination (-(1 / 2 : ℂ)) * f (-x) * h

/-- The parity part keeps a symmetric Fourier box. -/
theorem dirichletParityPart_fourier_support (χ : DirichletCharacter ℂ N) {f : 𝓢(ℝ, ℂ)} {X : ℝ}
    (hf : tsupport (fun x : ℝ ↦ (𝓕 f) x) ⊆ Icc (-X) X) :
    tsupport (fun x : ℝ ↦ (𝓕 (dirichletParityPart χ f)) x) ⊆ Icc (-X) X := by
  have hneg : tsupport (fun x : ℝ ↦ (𝓕 (schwartzCompNeg f)) x) ⊆ Icc (-X) X := by
    have he : (fun x : ℝ ↦ (𝓕 (schwartzCompNeg f)) x) =
        (fun x : ℝ ↦ (𝓕 f) x) ∘ (Homeomorph.neg ℝ) := by
      funext x
      exact fourier_schwartzCompNeg f x
    rw [he, tsupport_comp_eq_preimage]
    intro x hx
    have := hf hx
    simp only [Set.mem_Icc, Homeomorph.coe_neg] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have hsum : (fun x : ℝ ↦ (𝓕 (dirichletParityPart χ f)) x) =
      fun x : ℝ ↦ (1 / 2 : ℂ) • ((𝓕 f) x + χ (-1) • (𝓕 (schwartzCompNeg f)) x) := by
    funext x
    simp [dirichletParityPart, smul_eq_mul, mul_add]
  rw [hsum]
  exact (tsupport_smul_subset_right (fun _ : ℝ ↦ (1 / 2 : ℂ))
    (fun x : ℝ ↦ (𝓕 f) x + χ (-1) • (𝓕 (schwartzCompNeg f)) x)).trans
    ((tsupport_add (fun x : ℝ ↦ (𝓕 f) x)
      (fun x : ℝ ↦ χ (-1) • (𝓕 (schwartzCompNeg f)) x)).trans
      (Set.union_subset hf ((tsupport_smul_subset_right (fun _ : ℝ ↦ χ (-1))
        (fun x : ℝ ↦ (𝓕 (schwartzCompNeg f)) x)).trans hneg)))

theorem isDirichletFixedBoxTest_dirichletParityPart (χ : DirichletCharacter ℂ N)
    {f : 𝓢(ℝ, ℂ)} {X : ℝ} (hf : tsupport (fun x : ℝ ↦ (𝓕 f) x) ⊆ Icc (-X) X) :
    IsDirichletFixedBoxTest χ X (dirichletParityPart χ f) :=
  ⟨hasDirichletParity_dirichletParityPart χ f, dirichletParityPart_fourier_support χ hf⟩

/-- The twisted radial theta series at `t > 0` converges, with sum `twistedRadialTheta χ f t`. -/
theorem hasSum_twistedRadialTheta (hχ : χ.IsPrimitive) (hN : 1 < N) (f : 𝓢(ℝ, ℂ))
    (t : ℝ≥0ˣ) :
    HasSum (fun m : ℤ ↦ χ m * f ((m : ℝ) * t)) (twistedRadialTheta χ f t) := by
  obtain ⟨_, herep⟩ := ratIdeleClassGroup_decomposition
  obtain ⟨g, harch, hfin, -⟩ := herep t 1
  have h := hasSum_twisted_theta hχ hN f g 1 hfin (t := t.val) harch
    (NNReal.coe_pos.mpr (Units.zero_lt t))
  rw [twistedRadialTheta, h.tsum_eq]
  exact h

/-- Paper: (11.3.1.3), p. 494, over `ℚ`. The twisted radial theta series at `t > 0` only sees
the `χ`-parity part of the test: reindex `m ↦ -m` and use `χ(-1)² = 1`. -/
theorem ratBridge_dirichlet_parity (hχ : χ.IsPrimitive) (hN : 1 < N) (f : 𝓢(ℝ, ℂ))
    (t : ℝ≥0ˣ) :
    twistedRadialTheta χ f t = twistedRadialTheta χ (dirichletParityPart χ f) t := by
  set Θ := twistedRadialTheta χ f t
  have h1 := hasSum_twistedRadialTheta hχ hN f t
  have h2 : HasSum (fun m : ℤ ↦ χ m * f (-((m : ℝ) * t))) (χ (-1) * Θ) := by
    rw [← (Equiv.neg ℤ).hasSum_iff]
    convert h1.mul_left (χ (-1)) using 1
    funext m
    simp only [Function.comp_apply, Equiv.neg_apply, Int.cast_neg, neg_mul, neg_neg]
    rw [show (-(m : ZMod N)) = -1 * (m : ZMod N) by ring, map_mul]
    ring
  have h3 := (h1.add (h2.mul_left (χ (-1)))).mul_left (1 / 2 : ℂ)
  have hval : (1 / 2 : ℂ) * (Θ + χ (-1) * (χ (-1) * Θ)) = Θ := by
    rw [← mul_assoc, dirichlet_eval_neg_one_sq]
    ring
  rw [hval] at h3
  rw [twistedRadialTheta, ← h3.tsum_eq]
  congr 1
  funext m
  rw [dirichletParityPart_apply]
  ring

end Parity

/-! ### The half-twisted strip norm -/

section StripNorm

local instance ratBridgeClassMeasurableSpace' : MeasurableSpace Cℚ := borel _

/-- In logarithmic norm coordinates the Tamagawa measure of the rational idele classes is the
norm-one mass times Lebesgue measure. -/
private theorem ratClassTamagawa_map_log_norm :
    (ideleClassTamagawaMeasure ℚ).map (fun g : Cℚ ↦ Real.log ((ideleClassNorm ℚ g : ℝ≥0) : ℝ)) =
      (normOneIdeleClassTamagawaMeasure ℚ univ).toNNReal • volume := by
  let : BorelSpace Cℚ := ⟨rfl⟩
  let : BorelSpace ℝ≥0ˣ := borelSpace_units_of_continuousInv₀ _
  let : SecondCountableTopology ℝ≥0ˣ := Units.isEmbedding_val₀.secondCountableTopology
  let : SFinite positiveRealHaar := by unfold positiveRealHaar; infer_instance
  let ν := normOneIdeleClassTamagawaMeasure ℚ
  let : CompactSpace (ideleClassNorm ℚ).ker := (ideleClassGroup_finiteness ℚ).2.1
  let : ν.IsHaarMeasure :=
    (multiplicativeTamagawaMeasures_existsUnique ℚ).exists.choose_spec.2.2.2.1
  let σ (t : ℝ≥0ˣ) : Cℚ := ratNormSection t
  have hσ : Continuous σ := ratNormSection.continuous
  have hr : RightInverse σ (ideleClassNorm ℚ) := ideleClassNorm_ratNormSection
  let j (p : ℝ≥0ˣ × (ideleClassNorm ℚ).ker) := σ p.1 * p.2.val
  have hj : Measurable j :=
    ((hσ.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).measurable
  let l (t : ℝ≥0ˣ) := Real.log (t.val : ℝ)
  have hl : Measurable l :=
    Real.measurable_log.comp (NNReal.continuous_coe.comp Units.continuous_val).measurable
  have hmap : positiveRealHaar.map l = volume := by
    let E : ℝ ≃ₜ ℝ≥0ˣ := Real.expOrderIso.toHomeomorph.trans (Nonneg.unitsHomeomorphPos ℝ).symm
    have hE : positiveRealHaar = volume.map E := by
      apply congrArg (fun h : ℝ → ℝ≥0ˣ ↦ volume.map h)
      funext y
      exact Units.ext (NNReal.eq (Real.coe_toNNReal _ (Real.exp_pos y).le))
    rw [hE, Measure.map_map hl E.continuous.measurable]
    have hcomp : l ∘ E = id := funext fun y ↦ Real.log_exp y
    rw [hcomp, Measure.map_id]
  have hcomp : (l ∘ ideleClassNorm ℚ) ∘ j = l ∘ Prod.fst := by
    funext p
    change l (ideleClassNorm ℚ (σ p.1 * p.2.val)) = l p.1
    rw [map_mul, hr, MonoidHom.mem_ker.mp p.2.property, mul_one]
  change (ideleClassTamagawaMeasure ℚ).map (l ∘ ideleClassNorm ℚ) = (ν univ).toNNReal • volume
  rw [← classTamagawa_normProduct σ hσ hr, Measure.map_map
    (hl.comp (isProperMap_ideleClassNorm ℚ).continuous.measurable) hj, hcomp,
    ← Measure.map_map hl measurable_fst, Measure.map_fst_prod, Measure.map_smul, hmap,
    ← Measure.coe_nnreal_smul, ENNReal.coe_toNNReal (measure_ne_top ν univ)]
  exact hl.aemeasurable

private theorem norm_sq_toLp_two' {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {u : β → ℂ} (hu : MemLp u 2 ν) :
    ‖hu.toLp u‖ ^ 2 = ∫ a, ‖u a‖ ^ 2 ∂ν := by
  rw [← @real_inner_self_eq_norm_sq (Lp ℂ 2 ν), L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp] with a ha
  rw [ha, real_inner_self_eq_norm_sq]

local notation "massℝ" => (normOneIdeleClassTamagawaMeasure ℚ Set.univ).toReal

/-- Paper: (10.1.1.6), p. 435, with (11.3.1.3), p. 494, over `ℚ`.
**The strip norm of a homogeneous theta.** Let `g` be a polar adelic test whose homogeneous theta
has modulus `mass · |Θ(t)|` at every class `k · τ(t)` (`k` of norm one), and let
`U(x) = e^{x/2} Θ(eˣ)` lie in the weighted `L²` space of `CompactIntervalSobolev volume id (-α) α s`.
Then the half-twisted strip norm `primaryDivisorialStripNorm (1/2 - α) (1/2 + α) s ω g` of
`Sec3_FixedBox` is `mass^{3/2}` times the norm of `U`: one factor `mass` from the Haar measure on
the norm-one classes and `mass²` from the theta. -/
theorem ratBridge_stripNorm (ω : PontryaginDual (ideleClassNorm ℚ).ker)
    (g : ↥(adelePolarSubspace ℚ)) (Θ : ℝ → ℂ) {α s : ℝ}
    (hΘ : ∀ (t : ℝ≥0ˣ) (k : (ideleClassNorm ℚ).ker),
      ‖homogeneousAdelicTheta ω g.val (k.val * ratNormSection t)‖ = massℝ * ‖Θ t‖)
    (hU : MemLp (fun x : ℝ ↦ (Real.exp (x / 2) : ℂ) * Θ (Real.exp x)) 2
      (intervalSobolevMeasure volume id (-α) α s)) :
    primaryDivisorialStripNorm (1 / 2 - α) (1 / 2 + α) s ω g ^ 2 =
      massℝ ^ 3 * ‖hU.toLp _‖ ^ 2 := by
  let : BorelSpace Cℚ := ⟨rfl⟩
  set m := massℝ with hm
  let U : ℝ → ℂ := fun x ↦ (Real.exp (x / 2) : ℂ) * Θ (Real.exp x)
  let d : ℝ → ℝ := intervalSobolevDensity (-α) α s
  let H : ℝ → ℝ := fun y ↦ ‖U y‖ ^ 2 * d y
  have hd0 (y : ℝ) : 0 < d y := by
    simp only [d, intervalSobolevDensity]
    exact mul_pos ((Real.exp_pos _).trans_le (le_max_left _ _)) (by positivity)
  have hdm : Measurable d := by
    change Measurable fun y ↦ intervalSobolevDensity (-α) α s y
    unfold intervalSobolevDensity
    fun_prop
  -- The integrand on the idele classes factors through the log norm.
  let L : Cℚ → ℝ := fun x ↦ Real.log ((ideleClassNorm ℚ x : ℝ≥0) : ℝ)
  have hpt (x : Cℚ) : ‖homogeneousAdelicTheta ω g.val x‖ ^ 2 *
      intervalSobolevDensity (1 / 2 - α) (1 / 2 + α) s (logIdeleClassNorm ℚ x) = m ^ 2 * H (L x) := by
    let t := ideleClassNorm ℚ x
    let k : (ideleClassNorm ℚ).ker := ⟨x * (ratNormSection t)⁻¹, by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ideleClassNorm_ratNormSection, mul_inv_cancel]⟩
    have hx : x = k.val * ratNormSection t := by simp [k]
    have ht0 : (0 : ℝ) < (t : ℝ≥0) := NNReal.coe_pos.mpr (Units.zero_lt t)
    have hexp : Real.exp (L x) = (t : ℝ≥0) := Real.exp_log ht0
    rw [hx, hΘ t k, ← hx]
    simp only [H, U, d, L, logIdeleClassNorm]
    rw [hexp, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, sub_eq_add_neg,
      ← globalThetaSobolev_norm_density (1 / 2) (-α) α s, show (1 / 2 : ℝ) * L x = L x / 2 by ring]
    simp only [L]
    ring
  -- Measurability of the profile.
  have hdm' : Measurable fun y ↦ ENNReal.ofReal (d y) := ENNReal.measurable_ofReal.comp hdm
  have hac : (volume : Measure ℝ) ≪ intervalSobolevMeasure volume id (-α) α s :=
    withDensity_absolutelyContinuous' hdm'.aemeasurable
      (.of_forall fun y ↦ (ENNReal.ofReal_pos.mpr (hd0 y)).ne')
  have hUm : AEStronglyMeasurable U volume := hU.aestronglyMeasurable.mono_ac hac
  have hHm : AEStronglyMeasurable H volume :=
    ((hUm.norm.pow 2).mul hdm.aestronglyMeasurable)
  -- The class integral as a line integral.
  have hLm : Measurable L :=
    Real.measurable_log.comp (NNReal.continuous_coe.comp
      (Units.continuous_val.comp (isProperMap_ideleClassNorm ℚ).continuous)).measurable
  have hline : ∫ x, H (L x) ∂ideleClassTamagawaMeasure ℚ = m * ∫ y, H y := by
    rw [← integral_map hLm.aemeasurable, ratClassTamagawa_map_log_norm,
      integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul, ENNReal.coe_toNNReal_eq_toReal]
    rw [ratClassTamagawa_map_log_norm]
    exact hHm.mono_ac (Measure.smul_absolutelyContinuous)
  -- The line integral is the squared norm.
  have hnorm : ‖hU.toLp U‖ ^ 2 = ∫ y, H y := by
    rw [norm_sq_toLp_two' hU]
    change ∫ a, ‖U a‖ ^ 2 ∂(volume.withDensity fun y ↦ ENNReal.ofReal (d y)) = _
    rw [integral_withDensity_eq_integral_toReal_smul hdm'
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    congr 1
    funext y
    simp only [H, U, ENNReal.toReal_ofReal (hd0 y).le, smul_eq_mul]
    ring
  have hnn : 0 ≤ ∫ x, ‖homogeneousAdelicTheta ω g.val x‖ ^ 2 *
      intervalSobolevDensity (1 / 2 - α) (1 / 2 + α) s (logIdeleClassNorm ℚ x)
        ∂ideleClassTamagawaMeasure ℚ := by
    refine integral_nonneg fun x ↦ mul_nonneg (sq_nonneg _) ?_
    simp only [intervalSobolevDensity]
    exact mul_nonneg ((Real.exp_pos _).le.trans (le_max_left _ _)) (by positivity)
  rw [primaryDivisorialStripNorm, Real.sq_sqrt hnn]
  simp_rw [hpt]
  rw [integral_const_mul, hline, ← hnorm]
  ring

/-- Paper: (10.1.1.6), p. 435, with (11.3.1.3), p. 494, over `ℚ`. For a primitive Dirichlet
character of conductor `N > 1` and a polar Dirichlet test, the half-twisted strip norm of its
homogeneous theta for `ω = ψ|_{C₁}` is `mass^{3/2}` times the norm of the half-logarithmic profile
`twistedHalfLogProfile χ f` of `Sec3_DirichletFixedBox_Isolated`. -/
theorem ratBridge_stripNorm_dirTest {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (hN : 1 < N) (f : 𝓢(ℝ, ℂ))
    (hpolar : dirTest hχ f ∈ adelePolarSubspace ℚ) {α s : ℝ}
    (hU : MemLp (twistedHalfLogProfile χ f) 2 (intervalSobolevMeasure volume id (-α) α s)) :
    primaryDivisorialStripNorm (1 / 2 - α) (1 / 2 + α) s (ratDirichletNormOneChar hχ)
        ⟨dirTest hχ f, hpolar⟩ ^ 2 = massℝ ^ 3 * ‖hU.toLp _‖ ^ 2 := by
  refine ratBridge_stripNorm (ratDirichletNormOneChar hχ) ⟨dirTest hχ f, hpolar⟩
    (twistedRadialTheta χ f) (fun t k ↦ ?_) hU
  rw [ratBridge_dirichletTest_theta hχ hN f t k, norm_mul, norm_mul, norm_inv, Circle.norm_coe,
    inv_one, one_mul, Complex.norm_real, Real.norm_of_nonneg ENNReal.toReal_nonneg]

end StripNorm

end RiemannMasullo.Isolated
