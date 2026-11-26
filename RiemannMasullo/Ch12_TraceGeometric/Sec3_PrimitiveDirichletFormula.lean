module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_RationalCylinderLimits
public import RiemannMasullo.AppB_AnalyticNT.Sec4b_PositiveLog
import Mathlib.Tactic

/-! # The primitive Dirichlet explicit formula on rational conductor cylinders

The positive-log Hecke formula gives the primitive formula required by the
conductor comparison. At the real place the sign of the rational residue
determines the parity of the gamma factor. At every finite place the actual
local character supplies the primitive prime-power coefficient, including
the ramified primes. Only the principal row has polar corrections.
-/

@[expose] public noncomputable section

open Classical Filter Function IsDedekindDomain MeasureTheory NumberField Set
open scoped ContDiff NumberField.AdeleRing Topology
open NumberFieldKB.Chebotarev.RatIdele
namespace RiemannMasullo.ConductorCylinder
set_option quotPrecheck false

local notation "w₀" => Rat.infinitePlace
local notation "e" => InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace
local notation "i(" x ")" => IdeleGroup.ofCompletion (𝓞 ℚ) ℚ w₀ (Units.map (e).symm.toMonoidHom x)

private theorem ratPart_at_real (x : ℝˣ) :
    ratPart i(x) = if 0 < (x : ℝ) then 1 else -1 := by
  have hR : realPart i(x) = (x : ℝ) := by
    change e ((InfiniteAdeleRing.ofCompletion w₀ ((e).symm (x : ℝ))) w₀) = _
    rw [InfiniteAdeleRing.ofCompletion, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same]
    exact (e).apply_symm_apply _
  have hf (v : Pl) : ratFactor i(x) v = 1 := by
    change prU v ^ (-WithZero.log (Valued.v (1 : v.adicCompletion ℚ))) = 1
    simp
  rw [ratPart_apply, finprod_congr hf, finprod_one, mul_one]
  simp only [sgnInf, MonoidHom.coe_mk, OneHom.coe_mk, hR]

private theorem residue_at_real (q : ℕ) [NeZero q] (x : ℝˣ) :
    resMod q i(x) = if 0 < (x : ℝ) then 1 else -1 := by
  have hf (v : Pl) : (compV v (unitPart i(x)) : v.adicCompletion ℚ) =
      if 0 < (x : ℝ) then 1 else -1 := by
    rw [unitPart_apply, ← map_inv, map_mul, Units.val_mul, coe_compV_diag, ratPart_at_real]
    have h : compV v i(x) = 1 := Units.ext rfl
    rw [h, Units.val_one, one_mul]
    split_ifs <;> simp
  rw [resMod_apply, resModFun]
  apply (ZMod.equivPi q (NeZero.ne q)).injective
  rw [RingEquiv.apply_symm_apply]
  ext p
  rw [hf]
  split_ifs
  · simp [redP_one]
  · have hle : Valued.v (-1 : (placeP q p).adicCompletion ℚ) ≤ 1 := by simp
    rw [redP_of_le hle]
    have hh : (⟨-1, hle⟩ : Op p (Nat.prime_of_mem_primeFactors p.2)) = -1 := rfl
    rw [hh, map_neg, map_one]
    simp

private theorem real_parameters_dirichlet {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
    (hψ : ∀ x : IdQ, (ψ (QuotientGroup.mk x) : ℂ) = (ideleChar q χ x : ℂ))
    (w : InfinitePlace ℚ) (hw : w.IsReal) :
    (realHeckeCharacter_parameters ψ w hw).exists.choose =
      (0, if χ (-1) = 1 then 0 else 1) := by
  obtain rfl : w = w₀ := Subsingleton.elim _ _
  apply (realHeckeCharacter_parameters ψ w₀ hw).unique
    (realHeckeCharacter_parameters ψ w₀ hw).exists.choose_spec
  refine ⟨rfl, fun x ↦ ?_⟩
  change (ψ (QuotientGroup.mk i(x)) : ℂ) * _ ^ (0 : ℂ) = _
  rw [Complex.cpow_zero, mul_one, hψ, coe_ideleChar]
  change (χ (resMod q i(x)))⁻¹ = _
  rw [residue_at_real, Complex.cpow_zero, one_mul]
  split_ifs <;> simp_all
  rcases χ.even_or_odd with he | ho
  · contradiction
  · change χ (-1) = -1 at ho
    simp [ho]

open ConductorDensity RationalConductor

local notation "Zstrip" => {z : ℂ // 0 < z.re ∧ z.re < 1}
local notation "divisor(" χ ")" => MeromorphicOn.divisor (continuedCompletedHeckeL (packetRow χ)) univ

private theorem prime_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (G : ℝ → ℂ) :
    (∑' j, positiveLogPrimeTerm (packetRow χ) G j) = primitivePrimeSeries G χ := by
  classical
  let placeEquiv := Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)
  let g (j : Pl × ℕ) : ℕ := (placeEquiv j.1).val ^ (j.2 + 1)
  have hi : Injective g := by
    intro i j hij
    obtain ⟨hp, hn⟩ := (placeEquiv i.1).property.pow_inj (placeEquiv j.1).property hij
    exact Prod.ext (placeEquiv.injective (Subtype.ext hp)) hn
  let P (n : ℕ) := primeSample G n * χ.primitiveCharacter n
  have hs : support P ⊆ range g := by
    intro n hn
    have hn' : IsPrimePow n := by
      by_contra h
      exact hn (by simp [P, primeSample_eq_zero G h])
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hn'
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
    exact ⟨(placeEquiv.symm ⟨p, hp⟩, k), congrArg (fun p : Nat.Primes ↦ p.val ^ (k + 1))
      (placeEquiv.apply_symm_apply ⟨p, hp⟩)⟩
  change _ = ∑' n, P n
  rw [← hi.tsum_eq hs]
  apply tsum_congr
  intro j
  let v := j.1
  have he : (placeEquiv v).val = pr v := rfl
  change positiveLogPrimeTerm (packetRow χ) G (v, j.2) = P ((placeEquiv v).val ^ (j.2 + 1))
  rw [he]
  simp only [P, primeSample_prime_pow G (pr_prime v) (Nat.succ_ne_zero _), Nat.cast_pow,
    map_pow, Real.log_pow, positiveLogPrimeTerm, absNorm_asIdeal]
  rw [← localPrimeValue_eq_primitive q χ _ (packetRow_value χ) v, localPrimeValue]
  split_ifs <;> simp [mul_right_comm]

private theorem gamma_eq_archTerm (j : ℕ) (G : ℝ → ℂ) :
    positiveLogGammaIntegral (1 / 2) j G = archTerm j G := by
  unfold positiveLogGammaIntegral archTerm
  refine integral_congr_ae (.of_forall fun x ↦ ?_)
  simp only [Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_exp,
    Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_natCast, Complex.ofReal_ofNat,
    show -x / (1 / 2) = -(2 * x) by ring, neg_mul]
  ring

private theorem arch_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (G : ℝ → ℂ) :
    (∑ w, positiveLogArchTerm (packetRow χ) G w) =
      if χ (-1) = 1 then archTerm 0 G else archTerm 1 G := by
  classical
  rw [Fintype.sum_subsingleton _ Rat.infinitePlace]
  rw [positiveLogArchTerm, dite_eq_left Rat.isReal_infinitePlace,
    real_parameters_dirichlet χ (packetRow χ)
      (fun x ↦ (packetRow_value χ _).trans (congrArg Units.val (ratDirichletChar_mk q χ x)))
      _ Rat.isReal_infinitePlace]
  split_ifs <;> simp [← gamma_eq_archTerm]

private theorem packetRow_one {q : ℕ} [NeZero q] : packetRow (1 : DirichletCharacter ℂ q) = 1 := by
  apply PontryaginDual.ext
  intro x
  apply Circle.ext
  rw [packetRow_value, ratDirichletChar_eq_conj]
  simp

private theorem packetRow_nonprincipal {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) :
    (packetRow χ).toMonoidHom.comp (ideleClassNorm ℚ).ker.subtype ≠ 1 := by
  intro h
  apply hχ
  apply angular_lift_injective q
  funext k
  change ((ratDirichletChar q χ k.val : ℂˣ) : ℂ) = ((ratDirichletChar q 1 k.val : ℂˣ) : ℂ)
  rw [← packetRow_value χ, ← packetRow_value (1 : DirichletCharacter ℂ q), packetRow_one]
  exact congrArg (fun x : Circle ↦ (x : ℂ)) (congrArg (fun f : (ideleClassNorm ℚ).ker →* Circle ↦ f k) h)

/-- Section B.4.2 and the signed comparison of §12.3. Each primitive row of
a rational conductor packet satisfies the positive-log explicit formula. The
principal row contributes both polar Laplace moments, a ramified prime contributes
zero at its primitive conductor, and the infinite place uses the actual parity. -/
theorem hasSum_primitiveDirichlet_positiveLog {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (G : ℝ → ℂ) (hG : ContDiff ℝ (∞) G) (hc : HasCompactSupport G) (hs : tsupport G ⊆ Ioi 0) :
    HasSum (fun z : Zstrip ↦ (completedPrimitiveOrder (χ, z) : ℂ) * bilateralLaplace G z.val)
      ((if χ = 1 then bilateralLaplace G 0 + bilateralLaplace G 1 else 0) +
        primeAndArchRow G (archTerm 0 G) (archTerm 1 G) χ) := by
  classical
  let d := divisor(χ)
  let M := bilateralLaplace G
  let ψ := packetRow χ
  obtain ⟨hL, hA⟩ := continuedCompletedHeckeL_spec ψ
  have hfull := hasSum_heckeExplicitFormula_positiveLog ψ G hG hc hs _ hL hA
  rw [prime_sum, arch_sum] at hfull
  have hpos {z : ℂ} (hz : 0 < d z) : 0 < z.re ∧ z.re < 1 :=
    rowZeroSites_mem_criticalStrip ψ ⟨z, hz⟩
  have hpol : d 0 = (if χ = 1 then -1 else 0) ∧ d 1 = (if χ = 1 then -1 else 0) ∧
      ∀ z, z ≠ 0 → z ≠ 1 → 0 ≤ d z := by
    by_cases hχ : χ = 1
    · subst χ
      simpa only [d, packetRow_one, ite_true] using
        principalHeckeDivisor_poles _ (continuedCompletedHeckeL_spec (F := ℚ) 1).1
          (continuedCompletedHeckeL_spec (F := ℚ) 1).2
    · have hnon (z : ℂ) : 0 ≤ d z := by
        rw [show d z = (meromorphicOrderAt (continuedCompletedHeckeL ψ) z).untop₀ from
          MeromorphicOn.divisor_apply hL.meromorphicOn (mem_univ _), WithTop.untop₀_nonneg]
        exact ((completedHeckeL_continuation_entire ψ _ hL hA (packetRow_nonprincipal hχ)).analyticAt z).meromorphicOrderAt_nonneg
      simp only [ite_eq_right hχ]
      exact ⟨le_antisymm (not_lt.mp (fun h ↦ by simpa using (hpos h).1)) (hnon _),
        le_antisymm (not_lt.mp (fun h ↦ by simpa using (hpos h).2)) (hnon _), fun z _ _ ↦ hnon z⟩
  let p (z : ℂ) := if χ = 1 then M z else 0
  change HasSum (fun z : ℂ ↦ (d z : ℂ) * M z) _ at hfull
  have h := ((hfull.add (hasSum_ite_eq 0 (p 0))).add (hasSum_ite_eq 1 (p 1)))
  let Z := {z : ℂ | 0 < z.re ∧ z.re < 1}
  have hzsum : HasSum (fun z : Z ↦ (d z.val : ℂ) * M z.val)
      ((if χ = 1 then M 0 + M 1 else 0) + primeAndArchRow G (archTerm 0 G) (archTerm 1 G) χ) := by
    apply (hasSum_subtype_iff_indicator (s := Z) (f := fun z : ℂ ↦ (d z : ℂ) * M z)).mpr
    convert h.congr_fun (g := Z.indicator (fun z : ℂ ↦ (d z : ℂ) * M z)) (fun z ↦ ?_) using 1
    · by_cases hχ : χ = 1 <;> simp [p, hχ, primeAndArchRow]; ring
    · rcases eq_or_ne z 0 with rfl | hz0
      · by_cases hχ : χ = 1 <;> simp [Z, p, hpol.1, hχ]
      rcases eq_or_ne z 1 with rfl | hz1
      · by_cases hχ : χ = 1 <;> simp [Z, p, hpol.2.1, hχ]
      by_cases hz : z ∈ Z
      · simp [hz, hz0, hz1]
      · have hd : d z = 0 := le_antisymm (not_lt.mp (fun hp ↦ hz (hpos hp))) (hpol.2.2 z hz0 hz1)
        simp [hz, hz0, hz1, hd]
  apply hzsum.congr_fun
  intro z
  have hn := hpol.2.2 z.val (fun h ↦ z.property.1.ne' (by simp [h])) (fun h ↦ z.property.2.ne (by simp [h]))
  rw [← packetRow_divisor_eq]
  congr 1
  exact_mod_cast Int.toNat_of_nonneg hn

/-- The positive-log formula input to the single-modulus cylinder comparison. -/
theorem positiveLogDirichletFormula_proved : PositiveLogDirichletFormula := by
  intro q _ χ G hG hc hs h0 h1
  simpa [h0, h1] using hasSum_primitiveDirichlet_positiveLog χ G hG hc hs

end RiemannMasullo.ConductorCylinder
