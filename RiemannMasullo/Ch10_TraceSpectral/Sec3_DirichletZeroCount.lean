module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.Analysis.Analytic.Order
import RiemannMasullo.Ch13_ZerosHecke.Targets
import RiemannMasullo.Ch01_Introduction.Sec4
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import RiemannMasullo.External.HardyCriticalLine.DigammaFormula
import RiemannMasullo.External.HardyCriticalLine.BellottiWongGammaRemainder

/-!
# A lower bound for the number of zeros of a primitive Dirichlet L-function

For a nontrivial primitive Dirichlet character `χ` modulo `m` and `T ≥ 8`,
`dirichletStripZeroCount_lower` proves

`2π N(2T, χ) ≥ ⌊T/2⌋ (log (T/2)/2 - K₃) - 8 (log (2T)/2 + log m + K₄)`

with absolute constants `K₃`, `K₄`, where `N(T, χ)` (`dirichletStripZeroCount`) counts the zeros
`β + iγ` of `L(s, χ)` with `0 < β < 1` and `|γ| ≤ T` with multiplicity. This is the lower half of
the classical count `N(T, χ) = (T/π) log (qT/2πe) + O(log qT)`, weak in the constants and
sufficient for `Sec3_CloseCriticalZeros.lean`.

The proof is the classical one through the partial fractions of `Λ'/Λ`.

* **The resolvent identity.** For `1 < Re s`, `∑_ρ m_ρ Re 1/(s - ρ) = Re (Λ'/Λ)(s) + C(χ)`,
  where `Λ` is Mathlib's `completedLFunction χ`. This is the library's
  `introTrace_all_characters_completed_resolvent_height_formula` (Ch01 §1.4), transported along
  the identification of the library's completed Hecke L-function of the idele class character of
  `χ` with Mathlib's completed Dirichlet L-function (`continuedCompletedHeckeL_eq`).
* **The constant.** The identity extends to every point where `Λ ≠ 0` (`resolvent_extend`).
  The functional equation, for `Λ'/Λ` and for the multiplicities of the zeros
  (`ρ ↦ 1 - ρ` between `χ` and `χ⁻¹`), gives `C(χ) + C(χ⁻¹) = log m`, and positivity gives
  `C(χ) ≥ -Re (Λ'/Λ)(2)`.
* **The line `Re s = 2`.** `Re (Λ'/Λ)(2 + it) = log (|t| + 2)/2 + O(1)` uniformly in `χ`, by
  Binet's formula for the digamma function (vendored in `External/HardyCriticalLine`) and the
  Dirichlet series of `L'/L`.
* **Counting.** Summing the identity at the integer heights in `[T/2, T]`, each zero contributes
  at most `2π` (an arctan integral), and the zeros above `2T` are controlled by the identity at
  the real point `2T`.

Nothing here is a statement of the paper. The file uses no formalization of the Riemann
hypothesis.
-/

@[expose] public section

open NumberField IsDedekindDomain NumberFieldKB.Chebotarev.RatIdele

namespace RiemannMasullo

/-- `N(T, χ)` of Conrey–Iwaniec–Soundararajan (arXiv:1105.1177, p. 1): the number of zeros
`ρ = β + iγ` of `L(s, χ)` with `0 < β < 1` and `|γ| ≤ T`, each counted with its multiplicity,
as in their Appendix (before (A.6)). Not a statement of the paper. -/
noncomputable def dirichletStripZeroCount {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (T : ℝ) : ℕ :=
  ∑ᶠ (s : ℂ) (_ : 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T), (analyticOrderAt χ.LFunction s).toNat

/-- `N₀'(T, χ)` of Conrey–Iwaniec–Soundararajan (arXiv:1105.1177, p. 1): the number of simple
zeros `ρ = 1/2 + iγ` of `L(s, χ)` with `|γ| ≤ T`. Not a statement of the paper. -/
noncomputable def dirichletSimpleCriticalZeroCount {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (T : ℝ) : ℕ :=
  {γ : ℝ | |γ| ≤ T ∧ analyticOrderAt χ.LFunction ((1 / 2 : ℂ) + γ * Complex.I) = 1}.ncard

end RiemannMasullo

namespace RiemannMasullo.DirichletZeroCount

variable (m : ℕ) [NeZero m]

/-- The idele with real component `r` and `1` at every finite place. -/
local notation "gInf(" r ")" => IdeleGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace r

private theorem compV_ofCompletion (v : Pl) (r : (Rat.infinitePlace).Completionˣ) :
    compV v gInf(r) = 1 :=
  Units.ext rfl

private theorem realPart_ofCompletion (r : (Rat.infinitePlace).Completionˣ) :
    realPart gInf(r) = eInf r := by
  unfold NumberFieldKB.Chebotarev.RatIdele.realPart
  rw [IdeleGroup.val_ofCompletion_apply]
  change eInf (InfiniteAdeleRing.ofCompletion Rat.infinitePlace (r : _) Rat.infinitePlace) = _
  rw [InfiniteAdeleRing.ofCompletion_apply]
  congr 1
  simp

private theorem ratPart_ofCompletion (r : (Rat.infinitePlace).Completionˣ) :
    ratPart gInf(r) = sgnInf gInf(r) := by
  rw [ratPart_apply]
  have h : ∀ v, ratFactor gInf(r) v = 1 := fun v ↦ by
    rw [ratFactor, ordV, compV_ofCompletion, Units.val_one, map_one, WithZero.log_one, neg_zero,
      zpow_zero]
  simp [h]

private theorem redP_neg_one {p : ℕ} {hp : p.Prime} {e : ℕ} : redP p hp e (-1) = -1 := by
  have h1 : Valued.v (-1 : Kp p hp) ≤ 1 := by rw [Valuation.map_neg, map_one]
  rw [redP_of_le h1]
  have : (⟨(-1 : Kp p hp), h1⟩ : Op p hp) = -1 := Subtype.ext (by simp)
  rw [this, map_neg, map_one]

private theorem resMod_ofCompletion (r : (Rat.infinitePlace).Completionˣ) :
    resMod m gInf(r) = if 0 < eInf r then 1 else -1 := by
  have hs : sgnInf gInf(r) = if 0 < eInf r then 1 else -1 := by
    simp only [sgnInf, MonoidHom.coe_mk, OneHom.coe_mk, realPart_ofCompletion]
  have hcomp (p : m.primeFactors) : (compV (placeP m p) (unitPart gInf(r)) :
      (placeP m p).adicCompletion ℚ) = (((if 0 < eInf r then 1 else -1 : ℚˣ) : ℚ) : _) := by
    rw [unitPart_apply, ratPart_ofCompletion, hs, map_mul, Units.val_mul, compV_ofCompletion,
      Units.val_one, one_mul, ← map_inv, coe_compV_diag]
    split_ifs <;> simp
  rw [resMod_apply, resModFun]
  split_ifs with h
  · rw [← map_one (ZMod.equivPi m (NeZero.ne m)).symm]
    congr 1
    funext p
    simp only [hcomp p, h, ↓reduceIte, Units.val_one, Rat.cast_one, Pi.one_apply]
    exact redP_one
  · rw [← map_one (ZMod.equivPi m (NeZero.ne m)).symm, ← map_neg]
    congr 1
    funext p
    simp only [hcomp p, h, ↓reduceIte, Units.val_neg, Units.val_one, Rat.cast_neg, Rat.cast_one,
      Pi.neg_apply, Pi.one_apply]
    exact redP_neg_one

private theorem ideleChar_ofCompletion (χ : DirichletCharacter ℂ m)
    (r : (Rat.infinitePlace).Completionˣ) :
    ((ideleChar m χ gInf(r) : ℂˣ) : ℂ) = if 0 < eInf r then 1 else χ (-1) := by
  rw [coe_ideleChar, MulChar.coe_toUnitHom, MonoidHom.coe_toHomUnits, resMod_ofCompletion]
  split_ifs
  · simp
  · have h2 : χ (-1) * χ (-1) = 1 := by rw [← map_mul, neg_one_mul, neg_neg, map_one]
    exact inv_eq_of_mul_eq_one_right h2


private theorem eInf_ringEquiv_symm (x : ℝ) :
    eInf ((InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm x) = x :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).apply_symm_apply x

open Classical in
/-- The real-place parameters of the idele class character of a Dirichlet character: radial
exponent `0`, and sign parity `0` or `1` according as the character is even or odd. -/
private theorem realParameters_eq (χ : DirichletCharacter ℂ m)
    (ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
    (hψ : ∀ x : IdQ, (ψ (QuotientGroup.mk x) : ℂ) = ((ideleChar m χ x : ℂˣ) : ℂ))
    (v : InfinitePlace ℚ) (hv : v.IsReal) :
    (realHeckeCharacter_parameters ψ v hv).exists.choose =
      ((0 : ℂ), (if χ.Even then 0 else 1 : Fin 2)) := by
  obtain rfl : v = Rat.infinitePlace := Subsingleton.elim _ _
  have hu := realHeckeCharacter_parameters ψ Rat.infinitePlace hv
  refine hu.unique hu.exists.choose_spec ⟨by simp, fun x ↦ ?_⟩
  let e := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
  change (ψ (QuotientGroup.mk (IdeleGroup.ofCompletion (𝓞 ℚ) ℚ Rat.infinitePlace
      (Units.map e.toMonoidHom x))) : ℂ) * _ = _
  rw [hψ, ideleChar_ofCompletion]
  have hx : eInf ((Units.map e.toMonoidHom x : _) : (Rat.infinitePlace).Completion) = x :=
    eInf_ringEquiv_symm (x : ℝ)
  rw [hx]
  rcases χ.even_or_odd with he | ho
  · have h1 : χ (-1) = 1 := he
    simp [he, h1]
    rfl
  · have h1 : χ (-1) = -1 := ho
    simp [ho.not_even, h1]
    split_ifs <;> rfl

open Classical in
/-- Over `ℚ` the gamma factor of the idele class character of a Dirichlet character is Mathlib's
gamma factor of the Dirichlet character. -/
private theorem heckeGammaFactor_eq (χ : DirichletCharacter ℂ m)
    (ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
    (hψ : ∀ x : IdQ, (ψ (QuotientGroup.mk x) : ℂ) = ((ideleChar m χ x : ℂˣ) : ℂ)) (s : ℂ) :
    heckeGammaFactor ψ s = DirichletCharacter.gammaFactor χ s := by
  rw [heckeGammaFactor, Fintype.prod_subsingleton _ Rat.infinitePlace]
  simp only [Rat.isReal_infinitePlace, ↓reduceDIte]
  simp only [realParameters_eq m χ ψ hψ, add_zero]
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]; simp [he]
  · rw [ho.gammaFactor_def]; simp [ho.not_even]


private theorem gammaFactor_ne_zero (χ : DirichletCharacter ℂ m) {s : ℂ} (hs : 0 < s.re) :
    DirichletCharacter.gammaFactor χ s ≠ 0 := by
  rcases χ.even_or_odd with he | ho
  · rw [he.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos hs
  · rw [ho.gammaFactor_def]
    exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)

/-- **The bridge.** For a nontrivial Dirichlet character and an idele class character with the
same values whose finite Hecke L-function is its Dirichlet series, the continued completed Hecke
L-function of the library is Mathlib's completed Dirichlet L-function, everywhere. -/
private theorem continuedCompletedHeckeL_eq (χ : DirichletCharacter ℂ m) (hχ : χ ≠ 1)
    (ψ : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
    (hψ : ∀ x : IdQ, (ψ (QuotientGroup.mk x) : ℂ) = ((ideleChar m χ x : ℂˣ) : ℂ))
    (hL : ∀ (s : ℂ) (hs : 1 < s.re), finiteHeckeL ψ ⟨s, hs⟩ = LSeries (χ ·) s) :
    continuedCompletedHeckeL ψ = DirichletCharacter.completedLFunction χ := by
  have hspec := continuedCompletedHeckeL_spec ψ
  have hΛ : Differentiable ℂ (DirichletCharacter.completedLFunction χ) :=
    DirichletCharacter.differentiable_completedLFunction hχ
  have hagree (s : ℂ) (hs : 1 < s.re) :
      continuedCompletedHeckeL ψ s = DirichletCharacter.completedLFunction χ s := by
    have hs0 : s ≠ 0 := fun h ↦ by rw [h, Complex.zero_re] at hs; linarith
    rw [hspec.2 ⟨s, hs⟩]
    change heckeGammaFactor ψ s * finiteHeckeL ψ ⟨s, hs⟩ = _
    rw [hL s hs, heckeGammaFactor_eq m χ ψ hψ, ← DirichletCharacter.LFunction_eq_LSeries χ hs,
      DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (.inl hs0),
      mul_div_cancel₀ _ (gammaFactor_ne_zero m χ (by linarith))]
  funext s
  have h := meromorphicContinuation_eventuallyEq hspec.1.meromorphicOn
    (fun z _ ↦ (hΛ.analyticAt z).meromorphicAt) hagree s
  exact (((hspec.1 (Set.mem_univ s)).eventuallyEq_nhdsNE_iff_eventuallyEq_nhds
    (hΛ.analyticAt s).meromorphicNFAt).mp h).eq_of_nhds


/-- If the idele class character of a Dirichlet character is trivial, so is the character. -/
private theorem eq_one_of_ideleChar (χ : DirichletCharacter ℂ m)
    (hone : ∀ x : IdQ, ((ideleChar m χ x : ℂˣ) : ℂ) = 1) : χ = 1 := by
  have hprime (p : ℕ) (hp : p.Prime) (hcop : p.Coprime m) : χ p = 1 := by
    have hv : (pr (placeOf p hp)).Coprime m := by rw [pr_placeOf]; exact hcop
    have h0 : ((p : ℕ) : Kp p hp) ≠ 0 := by
      intro h
      have h1 := valued_placeOf (p := p) (hp := hp)
      rw [h, map_zero] at h1
      exact WithZero.exp_ne_zero h1.symm
    have h := ideleChar_uniformizer m χ hv (Units.mk0 _ h0) valued_placeOf
    rw [hone, pr_placeOf] at h
    exact h.symm
  have hnat (n : ℕ) : n.Coprime m → χ n = 1 := by
    induction n using Nat.recOnMul with
    | zero =>
      intro h
      obtain rfl : m = 1 := Nat.coprime_zero_left m |>.mp h
      rw [Subsingleton.elim ((0 : ℕ) : ZMod 1) 1, map_one]
    | one => intro _; simp
    | prime p hp => exact hprime p hp
    | mul a b ha hb =>
      intro h
      rw [Nat.cast_mul, map_mul, ha (Nat.Coprime.coprime_mul_right h),
        hb (Nat.Coprime.coprime_mul_left h), one_mul]
  refine MulChar.ext fun u ↦ ?_
  rw [MulChar.one_apply_coe, ← ZMod.natCast_zmod_val (u : ZMod m)]
  exact hnat _ (ZMod.val_coe_unit_coprime u)


/-- If `exp (x w) = 1` for every real `x`, then `w = 0`. -/
private theorem eq_zero_of_exp_mul_eq_one {w : ℂ} (h : ∀ x : ℝ, Complex.exp (x * w) = 1) :
    w = 0 := by
  set x : ℝ := 1 / (‖w‖ + 1) with hx
  have hx0 : 0 < x := by positivity
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp (h x)
  have hnorm : ‖(x : ℂ) * w‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hx0.le, hx, one_div,
      inv_mul_lt_iff₀ (by positivity)]
    linarith
  have hk0 : k = 0 := by
    by_contra hk0
    have h1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hk0
    have h2 : ‖(x : ℂ) * w‖ = 2 * Real.pi * |(k : ℝ)| := by
      rw [hk, norm_mul, norm_mul, norm_mul, Complex.norm_intCast, Complex.norm_I,
        Complex.norm_ofNat, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
      ring
    nlinarith [Real.pi_gt_three]
  rw [hk0, Int.cast_zero, zero_mul] at hk
  exact (mul_eq_zero.mp hk).resolve_left (Complex.ofReal_ne_zero.mpr hx0.ne')

/-- For a nontrivial character of finite order, a normalization `ψ'` with
`ψ' |·|^0 = ψ |·|^(-a)` that is trivial on a norm section is not trivial. -/
private theorem normalized_ne_one (ψ ψ' : PontryaginDual (IdeleClassGroup (𝓞 ℚ) ℚ))
    (hfin : IsOfFinOrder ψ) (hψ : ψ ≠ 1)
    (τ : NNReal ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ) (hτ : Function.RightInverse τ (ideleClassNorm ℚ))
    (a : ℂ) (htwist : ideleClassNormTwist ψ' 0 = ideleClassNormTwist ψ (-a)) : ψ' ≠ 1 := by
  rintro rfl
  have hval (g : IdeleClassGroup (𝓞 ℚ) ℚ) :
      (ψ g : ℂ) * (((ideleClassNorm ℚ g : NNReal) : ℝ) : ℂ) ^ (-a) = 1 := by
    have h := DFunLike.congr_fun htwist g
    change ((1 : PontryaginDual _) g : ℂ) * _ ^ (0 : ℂ) = (ψ g : ℂ) * _ at h
    rw [Complex.cpow_zero, mul_one] at h
    exact h.symm.trans rfl
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hfin
  have hpos (g : IdeleClassGroup (𝓞 ℚ) ℚ) : (0 : ℝ) < ((ideleClassNorm ℚ g : NNReal) : ℝ) :=
    NNReal.coe_pos.mpr (Units.zero_lt _)
  have hψg (g : IdeleClassGroup (𝓞 ℚ) ℚ) :
      (ψ g : ℂ) = (((ideleClassNorm ℚ g : NNReal) : ℝ) : ℂ) ^ a := by
    have hx : (((ideleClassNorm ℚ g : NNReal) : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (hpos g).ne'
    have hne : (((ideleClassNorm ℚ g : NNReal) : ℝ) : ℂ) ^ a ≠ 0 := by
      rw [Complex.cpow_def_of_ne_zero hx]; exact Complex.exp_ne_zero _
    have h := hval g
    rw [Complex.cpow_neg] at h
    exact (mul_inv_eq_one₀ hne).mp h
  have hpow' (g : IdeleClassGroup (𝓞 ℚ) ℚ) : (ψ g : ℂ) ^ n = 1 := by
    have h := DFunLike.congr_fun hpow g
    rw [show (ψ ^ n) g = (ψ g) ^ n from
      ContinuousMonoidHom.pow_apply (ψ : IdeleClassGroup (𝓞 ℚ) ℚ →ₜ* Circle) n g] at h
    have h' := congrArg (fun z : Circle ↦ (z : ℂ)) h
    simpa using h'
  have ha : a = 0 := by
    refine (mul_eq_zero.mp (eq_zero_of_exp_mul_eq_one (w := a * n) fun x ↦ ?_)).resolve_right
      (Nat.cast_ne_zero.mpr hn.ne')
    let t : NNReal ˣ := Units.mk0 ⟨Real.exp x, (Real.exp_pos x).le⟩
      (ne_of_gt (show (0 : NNReal) < ⟨Real.exp x, _⟩ from Real.exp_pos x))
    have hN : ((ideleClassNorm ℚ (τ t) : NNReal) : ℝ) = Real.exp x := by rw [hτ t]; rfl
    have h := hpow' (τ t)
    rw [hψg, hN, ← Complex.cpow_nat_mul, Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'), ← Complex.ofReal_log (Real.exp_pos x).le,
      Real.log_exp] at h
    rw [← h]
    congr 1
    ring
  apply hψ
  ext1 g
  apply Circle.ext
  rw [hψg, ha, Complex.cpow_zero]
  rfl


/-- A continuous section of the idele class norm over `ℚ`. -/
private theorem exists_normSection : ∃ τ : NNReal ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ,
    Function.RightInverse τ (ideleClassNorm ℚ) := by
  let q : (AdeleRing (𝓞 ℚ) ℚ)ˣ →ₜ* IdeleClassGroup (𝓞 ℚ) ℚ :=
    ⟨QuotientGroup.mk' _, continuous_quotient_mk'⟩
  exact ⟨q.comp ⟨canonicalIdeleNormSection ℚ, canonicalIdeleNormSection_continuous ℚ⟩,
    canonicalIdeleNormSection_rightInverse ℚ⟩

/-- **The resolvent identity for a primitive Dirichlet L-function.** For a nontrivial primitive
character `χ` with completed L-function `Λ`, there is a real constant `C` such that for
`1 < Re s` the multiplicity-weighted real parts `Re (m_ρ / (s - ρ))` over the zeros `ρ` of `Λ` in
`0 < Re ρ < 1` sum to `Re (Λ'/Λ)(s) + C`. -/
private theorem resolvent_identity (χ : DirichletCharacter ℂ m) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ s : ℂ, 1 < s.re →
      HasSum (fun r : {ρ : ℂ // 0 < MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ) Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2} ↦
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ r.val : ℂ) /
          (s - r.val)).re)
        ((logDeriv (DirichletCharacter.completedLFunction χ) s).re + C) := by
  obtain ⟨ψ, hfin, hval, hL⟩ :=
    RiemannMasullo.DirichletCharacter.IsPrimitive.exists_finiteHeckeL_eq_with_values hprim
  have hψ1 : ψ ≠ 1 := fun h ↦ hχ (eq_one_of_ideleChar m χ fun x ↦ by rw [← hval x, h]; rfl)
  have hbridge := continuedCompletedHeckeL_eq m χ hχ ψ hval hL
  obtain ⟨τ, hτ⟩ := exists_normSection
  obtain ⟨ψ', a, ha, hψ'τ, htwist, hres⟩ :=
    introTrace_all_characters_completed_resolvent_height_formula τ hτ ψ
  have hψ' := normalized_ne_one ψ ψ' hfin hψ1 τ hτ a htwist
  obtain ⟨-, -, hsum, -⟩ := hres
  simp only [hψ', ↓reduceIte, add_zero] at hsum
  rw [hbridge] at hsum
  set Λ := DirichletCharacter.completedLFunction χ
  refine ⟨(∑' r : {ρ : ℂ // 0 < MeromorphicOn.divisor Λ Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2},
      ((MeromorphicOn.divisor Λ Set.univ r.val : ℂ) / (2 - (r.val - 1 / 2))).re) -
      (logDeriv Λ (2 + 1 / 2)).re, fun s hs ↦ ?_⟩
  have hz : s - 1 / 2 ∈ Complex.re ⁻¹' Set.Ioi (1 / 2 : ℝ) := by
    simp only [Set.mem_preimage, Set.mem_Ioi, Complex.sub_re, Complex.div_ofNat_re,
      Complex.one_re]
    linarith
  have h := (hsum (s - 1 / 2) hz).1
  rw [sub_add_cancel] at h
  have hfun : (fun r : {ρ : ℂ // 0 < MeromorphicOn.divisor Λ Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2} ↦
      ((MeromorphicOn.divisor Λ Set.univ r.val : ℂ) / (s - 1 / 2 - (r.val - 1 / 2))).re) =
      fun r ↦ ((MeromorphicOn.divisor Λ Set.univ r.val : ℂ) / (s - r.val)).re := by
    funext r; congr 2; ring
  rw [hfun, Complex.add_re, Complex.sub_re, Complex.ofReal_re] at h
  convert h using 1
  ring


/-! ### M2: zeros of `Λ`, the functional equation, and summability -/

section M2

variable {m}

/-- A positive divisor value of an entire function is a zero. -/
private theorem eq_zero_of_divisor_pos {Λ : ℂ → ℂ} (hΛ : Differentiable ℂ Λ) {ρ : ℂ}
    (h : 0 < MeromorphicOn.divisor Λ Set.univ ρ) : Λ ρ = 0 := by
  by_contra hne
  have hord : meromorphicOrderAt Λ ρ = 0 :=
    (hΛ.analyticAt ρ).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hne
  rw [MeromorphicOn.divisor_apply (fun z _ ↦ (hΛ.analyticAt z).meromorphicAt)
    (Set.mem_univ ρ), hord] at h
  exact lt_irrefl _ h

/-- A nontrivial primitive completed Dirichlet L-function has no zeros with `1 ≤ Re s`. -/
private theorem completedLFunction_ne_zero_of_one_le_re {χ : DirichletCharacter ℂ m} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 ≤ s.re) : DirichletCharacter.completedLFunction χ s ≠ 0 := by
  intro h0
  have hs0 : s ≠ 0 := fun h ↦ by rw [h, Complex.zero_re] at hs; linarith
  have hL := DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ s (.inl hs0)
  rw [h0, zero_div] at hL
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs hL

/-- The functional equation as an identity of functions of `w`. -/
private theorem completedLFunction_one_sub_eq {χ : DirichletCharacter ℂ m} (hprim : χ.IsPrimitive)
    (w : ℂ) : DirichletCharacter.completedLFunction χ (1 - w) =
      (m : ℂ) ^ (w - 1 / 2) * DirichletCharacter.rootNumber χ *
        DirichletCharacter.completedLFunction χ⁻¹ w :=
  hprim.completedLFunction_one_sub w

/-- Every zero of a nontrivial primitive completed Dirichlet L-function lies in `0 < Re s < 1`. -/
private theorem completedLFunction_zero_mem_strip {χ : DirichletCharacter ℂ m}
    (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) {ρ : ℂ} (h : DirichletCharacter.completedLFunction χ ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  have hχi : χ⁻¹ ≠ 1 := fun h' ↦ hχ (inv_eq_one.mp h')
  refine ⟨?_, ?_⟩
  · by_contra hle
    have h1 : 1 ≤ (1 - ρ).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have hfe := completedLFunction_one_sub_eq hprim (1 - ρ)
    rw [sub_sub_cancel, h] at hfe
    have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
    rcases mul_eq_zero.mp hfe.symm with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · rw [Complex.cpow_def_of_ne_zero hm] at h3; exact Complex.exp_ne_zero _ h3
      · exact DirichletCharacter.rootNumber_ne_zero hprim h3
    · exact completedLFunction_ne_zero_of_one_le_re hχi h1 h2
  · by_contra hle
    exact completedLFunction_ne_zero_of_one_le_re hχ (not_lt.mp hle) h

/-- **Multiplicities under the functional equation**: the order of `Λ(χ, ·)` at `1 - w` is the
order of `Λ(χ⁻¹, ·)` at `w`. -/
private theorem divisor_one_sub {χ : DirichletCharacter ℂ m} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (w : ℂ) :
    MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ (1 - w) =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ⁻¹) Set.univ w := by
  have hχi : χ⁻¹ ≠ 1 := fun h' ↦ hχ (inv_eq_one.mp h')
  have hΛ := DirichletCharacter.differentiable_completedLFunction hχ
  have hΛi := DirichletCharacter.differentiable_completedLFunction hχi
  rw [MeromorphicOn.divisor_apply (fun z _ ↦ (hΛ.analyticAt z).meromorphicAt) (Set.mem_univ _),
    MeromorphicOn.divisor_apply (fun z _ ↦ (hΛi.analyticAt z).meromorphicAt) (Set.mem_univ _)]
  congr 1
  have hg : AnalyticAt ℂ (fun z : ℂ ↦ 1 - z) w := by fun_prop
  have hg' : deriv (fun z : ℂ ↦ 1 - z) w ≠ 0 := by
    rw [deriv_const_sub, deriv_id'']; norm_num
  rw [← meromorphicOrderAt_comp_of_deriv_ne_zero hg hg']
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hfun : (DirichletCharacter.completedLFunction χ ∘ fun z : ℂ ↦ 1 - z) =
      (fun z : ℂ ↦ (m : ℂ) ^ (z - 1 / 2) * DirichletCharacter.rootNumber χ) *
        DirichletCharacter.completedLFunction χ⁻¹ := by
    funext z
    simp only [Function.comp_apply, Pi.mul_apply]
    rw [completedLFunction_one_sub_eq hprim z]
  rw [hfun]
  apply meromorphicOrderAt_mul_of_ne_zero
  · exact (analyticAt_const.cpow (by fun_prop)
      (Complex.natCast_mem_slitPlane.mpr (NeZero.ne m))).mul analyticAt_const
  · refine mul_ne_zero ?_ (DirichletCharacter.rootNumber_ne_zero hprim)
    rw [Complex.cpow_def_of_ne_zero hm]; exact Complex.exp_ne_zero _

/-! ### M2: extension of the resolvent identity, for a general entire function -/

section Extension

variable {Λ : ℂ → ℂ}

set_option quotPrecheck false
local notation "dv(" Λ ", " ρ ")" => MeromorphicOn.divisor Λ Set.univ ρ
local notation "Zt(" Λ ")" => {ρ : ℂ // 0 < dv(Λ, ρ) ∧ |ρ.re - 1 / 2| < 1 / 2}

/-- The weight `m_ρ / ‖5/2 - ρ‖²` is summable when the resolvent identity holds at `5/2`. -/
private theorem summable_weight {C : ℝ}
    (h : HasSum (fun r : Zt(Λ) ↦ ((dv(Λ, r.val) : ℂ) / ((5 / 2 : ℂ) - r.val)).re)
      ((logDeriv Λ (5 / 2)).re + C)) :
    Summable fun r : Zt(Λ) ↦ (dv(Λ, r.val) : ℝ) / ‖(5 / 2 : ℂ) - r.val‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun r ↦ by have := r.2.1; positivity) (fun r ↦ ?_)
    (h.summable.mul_left (2 / 3))
  have hre : r.val.re < 1 := by have := (abs_lt.mp r.2.2).2; linarith
  have hd : (0 : ℝ) ≤ dv(Λ, r.val) := by exact_mod_cast r.2.1.le
  have hz : (5 / 2 : ℂ) - r.val ≠ 0 := fun h0 ↦ by
    have := congrArg Complex.re h0; simp at this; linarith
  have hn : 0 < ‖(5 / 2 : ℂ) - r.val‖ ^ 2 := by positivity
  have hterm : (((dv(Λ, r.val) : ℤ) : ℂ) / ((5 / 2 : ℂ) - r.val)).re =
      (dv(Λ, r.val) : ℝ) * ((5 / 2 - r.val.re) / ‖(5 / 2 : ℂ) - r.val‖ ^ 2) := by
    rw [div_eq_mul_inv, ← Complex.ofReal_intCast, Complex.re_ofReal_mul, Complex.inv_re,
      Complex.normSq_eq_norm_sq, Complex.sub_re]
    norm_num
  rw [hterm]
  have h1 : (3 / 2) / ‖(5 / 2 : ℂ) - r.val‖ ^ 2 ≤
      (5 / 2 - r.val.re) / ‖(5 / 2 : ℂ) - r.val‖ ^ 2 :=
    div_le_div_of_nonneg_right (by linarith) hn.le
  calc (dv(Λ, r.val) : ℝ) / ‖(5 / 2 : ℂ) - r.val‖ ^ 2 =
        2 / 3 * ((dv(Λ, r.val) : ℝ) * ((3 / 2) / ‖(5 / 2 : ℂ) - r.val‖ ^ 2)) := by
        field_simp
    _ ≤ _ := by gcongr

/-- The termwise bound behind the analyticity of the reference-subtracted resolvent. -/
private theorem norm_resolventTerm_le {s₀ w w₁ ρ : ℂ} {δ D : ℝ} (hδ : 0 < δ)
    (hw : ‖w - w₁‖ < δ / 2) (hρ : δ ≤ ‖w₁ - ρ‖) (hD : ‖s₀ - w₁‖ + δ ≤ D) (hs₀ : s₀ ≠ ρ) :
    ‖1 / (w - ρ) - 1 / (s₀ - ρ)‖ ≤ D * (2 * D / δ + 1) / ‖s₀ - ρ‖ ^ 2 := by
  have hwρ : δ / 2 ≤ ‖w - ρ‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub w₁ w ρ
    rw [norm_sub_rev w₁ w] at this; linarith
  have hwρ0 : w - ρ ≠ 0 := norm_pos_iff.mp (by linarith)
  have hs0 : s₀ - ρ ≠ 0 := sub_ne_zero.mpr hs₀
  have hsw : ‖s₀ - w‖ ≤ D := by
    have := norm_sub_le_norm_sub_add_norm_sub s₀ w₁ w
    rw [norm_sub_rev w₁ w] at this; linarith
  have hD0 : 0 < D := by linarith [norm_nonneg (s₀ - w₁)]
  have hsρ : ‖s₀ - ρ‖ ≤ (2 * D / δ + 1) * ‖w - ρ‖ := by
    have := norm_sub_le_norm_sub_add_norm_sub s₀ w ρ
    have h2 : D ≤ 2 * D / δ * ‖w - ρ‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ]; nlinarith
    nlinarith
  have hid : 1 / (w - ρ) - 1 / (s₀ - ρ) = (s₀ - w) / ((w - ρ) * (s₀ - ρ)) := by
    field_simp; ring
  have hpos : 0 < ‖s₀ - ρ‖ := norm_pos_iff.mpr hs0
  rw [hid, norm_div, norm_mul, div_le_div_iff₀ (by positivity) (by positivity)]
  have hK : 0 ≤ 2 * D / δ + 1 := by positivity
  calc ‖s₀ - w‖ * ‖s₀ - ρ‖ ^ 2 ≤ D * (‖s₀ - ρ‖ * ‖s₀ - ρ‖) := by
        rw [sq]; exact mul_le_mul_of_nonneg_right hsw (by positivity)
    _ ≤ D * ((2 * D / δ + 1) * ‖w - ρ‖ * ‖s₀ - ρ‖) := by
        gcongr
    _ = D * (2 * D / δ + 1) * (‖w - ρ‖ * ‖s₀ - ρ‖) := by ring

/-- A reference-subtracted resolvent term is differentiable away from its pole. -/
private theorem resolventTerm_differentiableAt (d ρ s₀ z : ℂ) (hz : z ≠ ρ) :
    DifferentiableAt ℂ (fun x ↦ d * (1 / (x - ρ) - 1 / (s₀ - ρ))) z := by
  have h1 : DifferentiableAt ℂ (fun x : ℂ ↦ (x - ρ)⁻¹) z :=
    (differentiableAt_id.sub_const ρ).inv (sub_ne_zero.mpr hz)
  simp only [one_div]
  exact (h1.sub_const _).const_mul d

local notation "rT(" Λ ", " r ", " z ")" =>
  ((MeromorphicOn.divisor Λ Set.univ (Subtype.val r) : ℂ) *
    (1 / (z - Subtype.val r) - 1 / ((5 / 2 : ℂ) - Subtype.val r)))
local notation "wt(" Λ ", " r ")" =>
  ((MeromorphicOn.divisor Λ Set.univ (Subtype.val r) : ℝ) / ‖(5 / 2 : ℂ) - Subtype.val r‖ ^ 2)

private theorem five_halves_ne (r : Zt(Λ)) : (5 / 2 : ℂ) ≠ r.val := by
  intro h
  have h1 := (abs_lt.mp r.2.2).2
  have h2 := congrArg Complex.re h
  norm_num at h2; linarith

/-- E1: the local uniform bound for the reference-subtracted resolvent terms. -/
private theorem resolvent_local_bound (hΛ : Differentiable ℂ Λ) (w₁ : ℂ) (hw₁ : Λ w₁ ≠ 0) :
    ∃ δ > 0, ∃ K : ℝ, Metric.ball w₁ δ ⊆ {z | Λ z ≠ 0} ∧
      ∀ z ∈ Metric.ball w₁ (δ / 2), ∀ r : Zt(Λ), ‖rT(Λ, r, z)‖ ≤ K * wt(Λ, r) := by
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp (isOpen_ne_fun hΛ.continuous continuous_const)
    w₁ hw₁
  refine ⟨δ, hδ, (‖(5 / 2 : ℂ) - w₁‖ + δ) * (2 * (‖(5 / 2 : ℂ) - w₁‖ + δ) / δ + 1), hball,
    fun z hz r ↦ ?_⟩
  have hρ : δ ≤ ‖w₁ - r.val‖ := by
    by_contra hlt
    rw [not_le] at hlt
    have hin : r.val ∈ Metric.ball w₁ δ := by
      rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact hlt
    exact hball hin (eq_zero_of_divisor_pos hΛ r.2.1)
  have hz' : ‖z - w₁‖ < δ / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
  have hb := norm_resolventTerm_le hδ hz' hρ le_rfl (five_halves_ne r)
  have hd : (0 : ℝ) ≤ MeromorphicOn.divisor Λ Set.univ r.val := by exact_mod_cast r.2.1.le
  rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hd]
  calc _ ≤ (MeromorphicOn.divisor Λ Set.univ r.val : ℝ) *
        ((‖(5 / 2 : ℂ) - w₁‖ + δ) * (2 * (‖(5 / 2 : ℂ) - w₁‖ + δ) / δ + 1) /
          ‖(5 / 2 : ℂ) - r.val‖ ^ 2) := mul_le_mul_of_nonneg_left hb hd
    _ = _ := by ring

/-- E2: the reference-subtracted resolvent is differentiable where `Λ` does not vanish. -/
private theorem resolvent_differentiableOn (hΛ : Differentiable ℂ Λ)
    (hW : Summable fun r : Zt(Λ) ↦ wt(Λ, r)) :
    DifferentiableOn ℂ (fun z ↦ ∑' r : Zt(Λ), rT(Λ, r, z)) {z | Λ z ≠ 0} := by
  intro w₁ hw₁
  obtain ⟨δ, hδ, K, hball, hb⟩ := resolvent_local_bound hΛ w₁ hw₁
  have hFd (r : Zt(Λ)) : DifferentiableOn ℂ (fun z ↦ rT(Λ, r, z)) (Metric.ball w₁ (δ / 2)) := by
    intro z hz
    have hzU : Λ z ≠ 0 := hball (Metric.ball_subset_ball (by linarith) hz)
    have hzr : z ≠ r.val := by
      intro h
      apply hzU
      rw [h]
      exact eq_zero_of_divisor_pos hΛ r.2.1
    exact (resolventTerm_differentiableAt _ r.val _ z hzr).differentiableWithinAt
  have hd := Complex.differentiableOn_tsum_of_summable_norm (hW.mul_left K) hFd Metric.isOpen_ball
    (fun r z hz ↦ hb z hz r)
  exact (hd.differentiableAt (Metric.ball_mem_nhds w₁ (by positivity))).differentiableWithinAt

/-- E3: the zero set of `Λ` is countable. -/
private theorem zeros_countable (hΛ : Differentiable ℂ Λ) (hne : Λ 2 ≠ 0)
    (hstrip : ∀ ρ, Λ ρ = 0 → 0 < ρ.re ∧ ρ.re < 1)
    (hW : Summable fun r : Zt(Λ) ↦ wt(Λ, r)) : {z | Λ z ≠ 0}ᶜ.Countable := by
  have hpos (r : Zt(Λ)) : 0 < wt(Λ, r) := by
    have h1 : (0 : ℝ) < MeromorphicOn.divisor Λ Set.univ r.val := by exact_mod_cast r.2.1
    have h2 : (0 : ℝ) < ‖(5 / 2 : ℂ) - r.val‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr (five_halves_ne r))
    positivity
  have hsupp := Summable.countable_support_nnreal _ hW.toNNReal
  have hcZ : (Set.univ : Set Zt(Λ)).Countable := hsupp.mono fun r _ ↦ by
    simp only [Function.mem_support, ne_eq, Real.toNNReal_eq_zero, not_le]
    exact hpos r
  have : Countable Zt(Λ) := Set.countable_univ_iff.mp hcZ
  refine (Set.countable_range (fun r : Zt(Λ) ↦ r.val)).mono fun z hz ↦ ?_
  have hz0 : Λ z = 0 := not_not.mp hz
  have han := hΛ.analyticAt z
  have hm : MeromorphicOn Λ Set.univ := fun x _ ↦ (hΛ.analyticAt x).meromorphicAt
  have h2 : meromorphicOrderAt Λ 2 = 0 :=
    (hΛ.analyticAt 2).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hne
  have hfin := hm.meromorphicOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (2 : ℂ)) (Set.mem_univ z) (by rw [h2]; simp)
  have hposo : 0 < meromorphicOrderAt Λ z :=
    lt_of_le_of_ne han.meromorphicOrderAt_nonneg fun h ↦
      han.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp h.symm hz0
  have hdz : 0 < MeromorphicOn.divisor Λ Set.univ z := by
    rw [MeromorphicOn.divisor_apply hm (Set.mem_univ z)]
    rw [← WithTop.coe_untop₀_of_ne_top hfin] at hposo
    exact WithTop.coe_lt_coe.mp hposo
  have hst := hstrip z hz0
  exact ⟨⟨z, hdz, abs_lt.mpr ⟨by linarith, by linarith⟩⟩, rfl⟩

/-- **Extension of the resolvent identity.** If an entire function `Λ`, not identically zero,
has all its zeros in the strip `0 < Re < 1`, and its multiplicity-weighted real resolvent sums to
`Re (Λ'/Λ) + C` on `1 < Re s`, then the same holds at every point where `Λ` does not vanish. -/
private theorem resolvent_extend (hΛ : Differentiable ℂ Λ) (hne : Λ 2 ≠ 0)
    (hstrip : ∀ ρ, Λ ρ = 0 → 0 < ρ.re ∧ ρ.re < 1) {C : ℝ}
    (hres : ∀ s : ℂ, 1 < s.re → HasSum (fun r : Zt(Λ) ↦ ((dv(Λ, r.val) : ℂ) / (s - r.val)).re)
      ((logDeriv Λ s).re + C))
    (w : ℂ) (hw : Λ w ≠ 0) :
    HasSum (fun r : Zt(Λ) ↦ ((dv(Λ, r.val) : ℂ) / (w - r.val)).re) ((logDeriv Λ w).re + C) := by
  have h52 : 1 < (5 / 2 : ℂ).re := by norm_num
  have hW := summable_weight (C := C) (hres _ h52)
  have hUo : IsOpen {z | Λ z ≠ 0} := isOpen_ne_fun hΛ.continuous continuous_const
  have hsumF (z : ℂ) (hz : Λ z ≠ 0) : Summable fun r : Zt(Λ) ↦ rT(Λ, r, z) := by
    obtain ⟨δ, hδ, K, -, hb⟩ := resolvent_local_bound hΛ z hz
    exact Summable.of_norm_bounded (hW.mul_left K)
      (fun r ↦ hb z (Metric.mem_ball_self (by positivity)) r)
  have hlog : DifferentiableOn ℂ (logDeriv Λ) {z | Λ z ≠ 0} := by
    intro z hz
    have : DifferentiableAt ℂ (fun x ↦ deriv Λ x / Λ x) z :=
      (hΛ.analyticAt z).deriv.differentiableAt.div (hΛ z) hz
    exact this.differentiableWithinAt
  have hDan : AnalyticOnNhd ℂ (fun z ↦ (∑' r : Zt(Λ), rT(Λ, r, z)) - logDeriv Λ z)
      {z | Λ z ≠ 0} := ((resolvent_differentiableOn hΛ hW).sub hlog).analyticOnNhd hUo
  have hconn : IsPreconnected {z | Λ z ≠ 0} := by
    have h := (zeros_countable hΛ hne hstrip hW).isConnected_compl_of_one_lt_rank
      (by rw [Complex.rank_real_complex]; norm_num)
    rw [compl_compl] at h
    exact h.isPreconnected
  have hreF (z : ℂ) (hz : Λ z ≠ 0) :
      HasSum (fun r : Zt(Λ) ↦ (rT(Λ, r, z)).re) (∑' r : Zt(Λ), rT(Λ, r, z)).re :=
    Complex.hasSum_re (hsumF z hz).hasSum
  have hterm (z : ℂ) (r : Zt(Λ)) : (rT(Λ, r, z)).re =
      ((dv(Λ, r.val) : ℂ) / (z - r.val)).re - ((dv(Λ, r.val) : ℂ) / ((5 / 2 : ℂ) - r.val)).re := by
    simp only [mul_sub, mul_one_div, Complex.sub_re]
  have hV (z : ℂ) (hz : 1 < z.re) :
      ((∑' r : Zt(Λ), rT(Λ, r, z)) - logDeriv Λ z).re = -(logDeriv Λ (5 / 2)).re := by
    have hzU : Λ z ≠ 0 := fun h0 ↦ by have := (hstrip z h0).2; linarith
    have h3 : HasSum (fun r : Zt(Λ) ↦ (rT(Λ, r, z)).re)
        ((logDeriv Λ z).re + C - ((logDeriv Λ (5 / 2)).re + C)) := by
      simp only [hterm]
      exact (hres z hz).sub (hres _ h52)
    rw [Complex.sub_re, (hreF z hzU).unique h3]
    ring
  have hconst (z : ℂ) (hz : Λ z ≠ 0) :
      ((∑' r : Zt(Λ), rT(Λ, r, z)) - logDeriv Λ z).re = -(logDeriv Λ (5 / 2)).re := by
    rcases AnalyticOnNhd.is_constant_or_isOpen hDan hconn with ⟨c, hc⟩ | hopen
    · have h3U : Λ 3 ≠ 0 := fun h0 ↦ by have := (hstrip 3 h0).2; norm_num at this
      rw [hc z hz, ← hc 3 h3U]
      exact hV 3 (by norm_num)
    · exfalso
      have hVo : IsOpen {z : ℂ | 1 < z.re} := isOpen_lt continuous_const Complex.continuous_re
      have hVU : {z : ℂ | 1 < z.re} ⊆ {z | Λ z ≠ 0} := fun z hz h0 ↦ by
        have := (hstrip z h0).2; simp only [Set.mem_ofPred_eq] at hz; linarith
      have himg := hopen _ hVU hVo
      set G := fun z ↦ (∑' r : Zt(Λ), rT(Λ, r, z)) - logDeriv Λ z
      have h3 : G 3 ∈ G '' {z : ℂ | 1 < z.re} := ⟨3, by norm_num, rfl⟩
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp himg _ h3
      have hmem : G 3 + ((ε / 2 : ℝ) : ℂ) ∈ G '' {z : ℂ | 1 < z.re} := hball (by
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real,
          Real.norm_of_nonneg (by positivity)]
        linarith)
      obtain ⟨y, hy, hyG⟩ := hmem
      have e1 := hV y hy
      have e2 := hV 3 (by norm_num)
      change (G y).re = _ at e1
      change (G 3).re = _ at e2
      rw [hyG, Complex.add_re, Complex.ofReal_re, e2] at e1
      linarith
  have h2 := (hreF w hw).add (hres _ h52)
  have hval := hconst w hw
  rw [Complex.sub_re] at hval
  convert h2 using 1
  · funext r
    rw [hterm]
    ring
  · linarith

end Extension

/-- **The functional equation for `Λ'/Λ`**: `(Λ'/Λ)(1 - w; χ) = -log m - (Λ'/Λ)(w; χ⁻¹)`. -/
private theorem logDeriv_one_sub {χ : DirichletCharacter ℂ m} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (w : ℂ) (hw : DirichletCharacter.completedLFunction χ⁻¹ w ≠ 0) :
    logDeriv (DirichletCharacter.completedLFunction χ) (1 - w) =
      -Complex.log m - logDeriv (DirichletCharacter.completedLFunction χ⁻¹) w := by
  have hχi : χ⁻¹ ≠ 1 := fun h' ↦ hχ (inv_eq_one.mp h')
  have hΛ := DirichletCharacter.differentiable_completedLFunction hχ
  have hΛi := DirichletCharacter.differentiable_completedLFunction hχi
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  set ε := DirichletCharacter.rootNumber χ
  have hε : ε ≠ 0 := DirichletCharacter.rootNumber_ne_zero hprim
  set e : ℂ → ℂ := fun z ↦ (m : ℂ) ^ (z - 1 / 2) * ε with he
  have hfun : (DirichletCharacter.completedLFunction χ ∘ fun z : ℂ ↦ 1 - z) =
      e * DirichletCharacter.completedLFunction χ⁻¹ := by
    funext z
    simp only [Function.comp_apply, Pi.mul_apply, he]
    rw [completedLFunction_one_sub_eq hprim z]
  have hcomp := logDeriv_comp (f := DirichletCharacter.completedLFunction χ)
    (g := fun z : ℂ ↦ 1 - z) (x := w) (hΛ _) (by fun_prop)
  have hderiv : deriv (fun z : ℂ ↦ 1 - z) w = -1 := by
    rw [deriv_const_sub, deriv_id'']
  rw [hderiv, hfun] at hcomp
  have hcpow (z : ℂ) : (m : ℂ) ^ (z - 1 / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hm]; exact Complex.exp_ne_zero _
  have heD : HasDerivAt e ((m : ℂ) ^ (w - 1 / 2) * Complex.log m * 1 * ε) w :=
    (((hasDerivAt_id w).sub_const (1 / 2)).const_cpow (.inl hm)).mul_const ε
  have hmul := logDeriv_mul (f := e) (g := DirichletCharacter.completedLFunction χ⁻¹) w
    (mul_ne_zero (hcpow w) hε) hw heD.differentiableAt (hΛi w)
  have hle : logDeriv e w = Complex.log m := by
    rw [logDeriv_apply, heD.deriv, div_eq_iff (mul_ne_zero (hcpow w) hε)]
    ring
  rw [hmul, hle] at hcomp
  linear_combination hcomp

/-- **Bounds for the constant of the resolvent identity.** For a nontrivial primitive character
`χ` modulo `m` with completed L-function `Λ`, the constant `C` with
`∑ m_ρ Re 1/(s - ρ) = Re (Λ'/Λ)(s) + C` on `1 < Re s` satisfies
`-Re (Λ'/Λ)(2; χ) ≤ C ≤ log m + Re (Λ'/Λ)(2; χ⁻¹)`. -/
private theorem resolvent_identity_bounds (χ : DirichletCharacter ℂ m) (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) :
    ∃ C : ℝ, (∀ s : ℂ, 1 < s.re →
      HasSum (fun r : {ρ : ℂ // 0 < MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ) Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2} ↦
        ((MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ r.val : ℂ) /
          (s - r.val)).re)
        ((logDeriv (DirichletCharacter.completedLFunction χ) s).re + C)) ∧
      -(logDeriv (DirichletCharacter.completedLFunction χ) 2).re ≤ C ∧
      C ≤ Real.log m + (logDeriv (DirichletCharacter.completedLFunction χ⁻¹) 2).re := by
  have hχi : χ⁻¹ ≠ 1 := fun h' ↦ hχ (inv_eq_one.mp h')
  have hprimi : χ⁻¹.IsPrimitive := hprim.inv
  set Λ := DirichletCharacter.completedLFunction χ with hΛdef
  set Λi := DirichletCharacter.completedLFunction χ⁻¹ with hΛidef
  have hΛ : Differentiable ℂ Λ := DirichletCharacter.differentiable_completedLFunction hχ
  have hΛi : Differentiable ℂ Λi := DirichletCharacter.differentiable_completedLFunction hχi
  obtain ⟨C, hC⟩ := resolvent_identity m χ hprim hχ
  obtain ⟨C', hC'⟩ := resolvent_identity m χ⁻¹ hprimi hχi
  -- positivity of the terms at `s = 2`
  have hnonneg (L : ℂ → ℂ) (r : {ρ : ℂ // 0 < MeromorphicOn.divisor L Set.univ ρ ∧
      |ρ.re - 1 / 2| < 1 / 2}) :
      0 ≤ ((MeromorphicOn.divisor L Set.univ r.val : ℂ) / (2 - r.val)).re := by
    have hd : (0 : ℝ) ≤ MeromorphicOn.divisor L Set.univ r.val := by exact_mod_cast r.2.1.le
    have hre : r.val.re < 1 := by have := (abs_lt.mp r.2.2).2; linarith
    rw [div_eq_mul_inv, ← Complex.ofReal_intCast, Complex.re_ofReal_mul, Complex.inv_re]
    apply mul_nonneg hd
    apply div_nonneg _ (Complex.normSq_nonneg _)
    simp only [Complex.sub_re, Complex.re_ofNat]; linarith
  have hlow : -(logDeriv Λ 2).re ≤ C := by
    have := (hC 2 (by norm_num)).nonneg (hnonneg Λ); linarith
  have hlowi : -(logDeriv Λi 2).re ≤ C' := by
    have := (hC' 2 (by norm_num)).nonneg (hnonneg Λi); linarith
  -- the identity at `-1 = 1 - 2`, reindexed by `ρ ↦ 1 - ρ`
  have hne2 : Λ 2 ≠ 0 := completedLFunction_ne_zero_of_one_le_re hχ (by norm_num)
  have hstrip (ρ : ℂ) (h : Λ ρ = 0) := completedLFunction_zero_mem_strip hprim hχ h
  have hm1 : Λ (-1) ≠ 0 := fun h ↦ by have := (hstrip _ h).1; norm_num at this
  have hext := resolvent_extend hΛ hne2 hstrip hC (-1) hm1
  have hdiv (w : ℂ) : MeromorphicOn.divisor Λ Set.univ (1 - w) =
      MeromorphicOn.divisor Λi Set.univ w := divisor_one_sub hprim hχ w
  let eqv : {ρ : ℂ // 0 < MeromorphicOn.divisor Λi Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2} ≃
      {ρ : ℂ // 0 < MeromorphicOn.divisor Λ Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2} :=
    { toFun := fun r ↦ ⟨1 - r.val, by rw [hdiv]; exact r.2.1, by
        rw [Complex.sub_re, Complex.one_re, show 1 - r.val.re - 1 / 2 = -(r.val.re - 1 / 2) by ring,
          abs_neg]; exact r.2.2⟩
      invFun := fun r ↦ ⟨1 - r.val, by rw [← hdiv, sub_sub_cancel]; exact r.2.1, by
        rw [Complex.sub_re, Complex.one_re, show 1 - r.val.re - 1 / 2 = -(r.val.re - 1 / 2) by ring,
          abs_neg]; exact r.2.2⟩
      left_inv := fun r ↦ Subtype.ext (sub_sub_cancel _ _)
      right_inv := fun r ↦ Subtype.ext (sub_sub_cancel _ _) }
  have hre := (eqv.hasSum_iff.mpr hext)
  have hterm (r : {ρ : ℂ // 0 < MeromorphicOn.divisor Λi Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2}) :
      ((MeromorphicOn.divisor Λ Set.univ (eqv r).val : ℂ) / (-1 - (eqv r).val)).re =
        -((MeromorphicOn.divisor Λi Set.univ r.val : ℂ) / (2 - r.val)).re := by
    change ((MeromorphicOn.divisor Λ Set.univ (1 - r.val) : ℂ) / (-1 - (1 - r.val))).re = _
    rw [hdiv, show (-1 : ℂ) - (1 - r.val) = -(2 - r.val) by ring, div_neg, Complex.neg_re]
  simp only [Function.comp_def, hterm] at hre
  have hsum2 := (hC' 2 (by norm_num)).neg
  have heq := hre.unique hsum2
  have hfe := logDeriv_one_sub hprim hχ 2
    (completedLFunction_ne_zero_of_one_le_re hχi (by norm_num))
  rw [show (1 : ℂ) - 2 = -1 by norm_num] at hfe
  rw [hfe, Complex.sub_re, Complex.neg_re, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log (Nat.cast_nonneg m), Complex.ofReal_re] at heq
  exact ⟨C, hC, hlow, by linarith⟩

end M2


/-! ### M3: uniform bounds on the line `Re s = 2` -/

section M3

open MeasureTheory

/-- M3-1: the Binet correction is at most `1/2` in norm to the right of `Re z = 1`. -/
private theorem norm_binetIntegral_le {z : ℂ} (hz : 1 ≤ z.re) :
    ‖HardyCriticalLine.bennettGammaBinetIntegral z‖ ≤ 1 / 2 := by
  unfold HardyCriticalLine.bennettGammaBinetIntegral
  have hint : IntegrableOn (fun t : ℝ ↦ 1 / 2 * Real.exp (-t)) (Set.Ioi 0) := by
    have h := (exp_neg_integrableOn_Ioi 0 one_pos).const_mul (1 / 2)
    simp only [neg_mul, one_mul] at h
    exact h
  calc ‖∫ t in Set.Ioi (0 : ℝ), HardyCriticalLine.bennettGammaBinetKernel t *
        Complex.exp (-(t : ℂ) * z)‖
      ≤ ∫ t in Set.Ioi (0 : ℝ), 1 / 2 * Real.exp (-t) := by
        refine norm_integral_le_of_norm_le hint ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
        have ht' : (0 : ℝ) < t := ht
        rw [norm_mul, Complex.norm_exp]
        have hre : (-(t : ℂ) * z).re = -(t * z.re) := by simp
        rw [hre]
        exact mul_le_mul (HardyCriticalLine.norm_bennettGammaBinetKernel_le_one_half_of_pos ht')
          (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le (by norm_num)
    _ = 1 / 2 := by rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]

/-- M3-2: `Re ψ(z)` is within `1` of `log ‖z‖` to the right of `Re z = 1`. -/
private theorem abs_re_digamma_sub_log_le {z : ℂ} (hz : 1 ≤ z.re) :
    |(Complex.digamma z).re - Real.log ‖z‖| ≤ 1 := by
  have hz0 : 0 < z.re := by linarith
  have hb := HardyCriticalLine.bennettGammaBinetDigamma_eqOn (show z ∈ {z : ℂ | 0 < z.re} from hz0)
  simp only at hb
  have hn : 1 ≤ ‖z‖ := hz.trans (Complex.re_le_norm z)
  have h1 : ‖1 / (2 * z)‖ ≤ 1 / 2 := by
    rw [norm_div, norm_one, norm_mul, Complex.norm_ofNat,
      div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  have h2 := norm_binetIntegral_le hz
  rw [hb, Complex.sub_re, Complex.sub_re, Complex.log_re]
  have e1 := Complex.abs_re_le_norm (1 / (2 * z))
  have e2 := Complex.abs_re_le_norm (HardyCriticalLine.bennettGammaBinetIntegral z)
  rw [abs_le] at e1 e2 ⊢
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

private theorem differentiableAt_Gamma_half {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.Gamma (w / 2) := by
  apply Complex.differentiableAt_Gamma
  intro n h
  have := congrArg Complex.re h
  simp only [Complex.div_ofNat_re, Complex.neg_re, Complex.natCast_re] at this
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

private theorem hasDerivAt_pi_cpow (w : ℂ) :
    HasDerivAt (fun w : ℂ ↦ (Real.pi : ℂ) ^ (-w / 2))
      ((Real.pi : ℂ) ^ (-w / 2) * Complex.log Real.pi * (-1 / 2)) w := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h := ((hasDerivAt_id w).neg.div_const 2).const_cpow (c := (Real.pi : ℂ)) (.inl hπ)
  simpa only [id, Pi.neg_apply] using h

/-- `Γℝ` is differentiable on the right half-plane. -/
private theorem differentiableAt_Gammaℝ {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ Complex.Gammaℝ w := by
  have hfun : Complex.Gammaℝ =
      (fun w : ℂ ↦ (Real.pi : ℂ) ^ (-w / 2)) * fun w ↦ Complex.Gamma (w / 2) :=
    funext Complex.Gammaℝ_def
  rw [hfun]
  exact (hasDerivAt_pi_cpow w).differentiableAt.mul
    ((differentiableAt_Gamma_half hw).comp w (differentiableAt_id.div_const 2))

/-- M3-3: `Γℝ'/Γℝ (w) = -log π / 2 + ψ(w/2)/2` on the right half-plane. -/
private theorem logDeriv_Gammaℝ {w : ℂ} (hw : 0 < w.re) :
    logDeriv Complex.Gammaℝ w = -Complex.log Real.pi / 2 + Complex.digamma (w / 2) / 2 := by
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hw2 : 0 < (w / 2).re := by simp only [Complex.div_ofNat_re]; linarith
  have hfun : Complex.Gammaℝ =
      (fun w : ℂ ↦ (Real.pi : ℂ) ^ (-w / 2)) * fun w ↦ Complex.Gamma (w / 2) :=
    funext Complex.Gammaℝ_def
  have hcp : (Real.pi : ℂ) ^ (-w / 2) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hπ]; exact Complex.exp_ne_zero _
  have hG := differentiableAt_Gamma_half hw
  have hGc : DifferentiableAt ℂ (fun w : ℂ ↦ Complex.Gamma (w / 2)) w :=
    hG.comp w (differentiableAt_id.div_const 2)
  rw [hfun, logDeriv_mul w hcp (Complex.Gamma_ne_zero_of_re_pos (s := w / 2) hw2)
    (hasDerivAt_pi_cpow w).differentiableAt hGc]
  have h1 : logDeriv (fun w : ℂ ↦ (Real.pi : ℂ) ^ (-w / 2)) w = -Complex.log Real.pi / 2 := by
    rw [logDeriv_apply, (hasDerivAt_pi_cpow w).deriv, div_eq_iff hcp]
    ring
  have h2 : logDeriv (fun w : ℂ ↦ Complex.Gamma (w / 2)) w = Complex.digamma (w / 2) / 2 := by
    have hc := logDeriv_comp (f := Complex.Gamma) (g := fun w : ℂ ↦ w / 2) (x := w) hG
      (differentiableAt_id.div_const 2)
    simp only [Function.comp_def] at hc
    rw [hc, ← Complex.digamma_def]
    rw [show deriv (fun w : ℂ ↦ w / 2) w = 1 / 2 from
      ((hasDerivAt_id w).div_const 2).deriv.trans (by simp)]
    ring
  rw [h1, h2]

/-- M3-4: on `Re s = 2 + a` with `0 ≤ a ≤ 1`, `Re Γℝ'/Γℝ` is `log (|t| + 2) / 2` up to an
absolute constant. -/
private theorem abs_re_logDeriv_Gammaℝ_sub_le {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (t : ℝ) :
    |(logDeriv Complex.Gammaℝ ((2 + a : ℝ) + t * Complex.I)).re - Real.log (|t| + 2) / 2| ≤
      (Real.log Real.pi + Real.log 4 + 1) / 2 := by
  set w : ℂ := (2 + a : ℝ) + t * Complex.I with hwdef
  have hwre : w.re = 2 + a := by simp [hwdef]
  have hwim : w.im = t := by simp [hwdef]
  have hw : 0 < w.re := by rw [hwre]; linarith
  set z := w / 2 with hz
  have hzre : z.re = (2 + a) / 2 := by rw [hz, Complex.div_ofNat_re, hwre]
  have hzim : z.im = t / 2 := by rw [hz, Complex.div_ofNat_im, hwim]
  have hz1 : 1 ≤ z.re := by rw [hzre]; linarith
  have hdig := abs_re_digamma_sub_log_le hz1
  have hup : ‖z‖ ≤ |t| + 2 := by
    have := Complex.norm_le_abs_re_add_abs_im z
    rw [hzre, hzim, abs_of_pos (by linarith), abs_div, abs_two] at this
    linarith [abs_nonneg t]
  have hlow : (|t| + 2) / 4 ≤ ‖z‖ := by
    have h1 := Complex.re_le_norm z
    have h2 := Complex.abs_im_le_norm z
    rw [hzre] at h1
    rw [hzim, abs_div, abs_two] at h2
    rcases le_total (|t|) 2 with h | h <;> linarith
  have hzpos : 0 < ‖z‖ := by linarith [abs_nonneg t]
  have hlog1 : Real.log ‖z‖ ≤ Real.log (|t| + 2) := Real.log_le_log hzpos hup
  have hlog2 : Real.log (|t| + 2) - Real.log 4 ≤ Real.log ‖z‖ := by
    have := Real.log_le_log (by positivity) hlow
    rw [Real.log_div (by positivity) (by norm_num)] at this
    exact this
  have hπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  rw [logDeriv_Gammaℝ hw, Complex.add_re, Complex.div_ofNat_re, Complex.div_ofNat_re,
    Complex.neg_re, ← Complex.ofReal_log Real.pi_pos.le, Complex.ofReal_re]
  rw [abs_le] at hdig ⊢
  constructor <;> nlinarith [hdig.1, hdig.2]

open scoped LSeries.notation in
/-- M3-5: on `2 ≤ Re s`, `‖L'/L(s, χ)‖` is at most the absolute constant
`∑ Λ(n) n⁻²`. -/
private theorem norm_logDeriv_LFunction_le {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m) {s : ℂ}
    (hs : 2 ≤ s.re) :
    ‖logDeriv χ.LFunction s‖ ≤ ∑' n, ‖LSeries.term ↗ArithmeticFunction.vonMangoldt 2 n‖ := by
  have hs1 : 1 < s.re := by linarith
  rw [logDeriv_apply, DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs1,
    DirichletCharacter.LFunction_eq_LSeries χ hs1]
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs1
  rw [neg_div] at h
  rw [← neg_neg (deriv (LSeries ↗χ) s / LSeries ↗χ s), ← h, norm_neg]
  have hsum := DirichletCharacter.LSeriesSummable_twist_vonMangoldt χ hs1
  have hsum2 := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num)
  refine (norm_tsum_le_tsum_norm hsum.norm).trans (hsum.norm.tsum_le_tsum (fun n ↦ ?_) hsum2.norm)
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  simp only [LSeries.norm_term_eq, hn, ↓reduceIte]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hχn : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  simp only [Pi.mul_apply, norm_mul]
  rw [show ((2 : ℂ)).re = 2 by norm_num]
  have hΛ : 0 ≤ ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ := norm_nonneg _
  calc ‖χ n‖ * ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ / (n : ℝ) ^ s.re
      ≤ 1 * ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)‖ / (n : ℝ) ^ (2 : ℝ) := by
        gcongr
    _ = _ := by rw [one_mul]

/-- The gamma factor of `χ` is `Γℝ (s + a)` with `a = 0` for even and `a = 1` for odd `χ`, and
its logarithmic derivative is that of `Γℝ` at `s + a`. -/
private theorem logDeriv_gammaFactor {m : ℕ} (χ : DirichletCharacter ℂ m) {s : ℂ} (hs : 0 < s.re) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧ DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) s ∧
      logDeriv (DirichletCharacter.gammaFactor χ) s = logDeriv Complex.Gammaℝ (s + a) := by
  rcases χ.even_or_odd with he | ho
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ :=
      funext fun z ↦ he.gammaFactor_def z
    refine ⟨0, le_rfl, zero_le_one, ?_, ?_⟩
    · rw [hfun]; exact differentiableAt_Gammaℝ hs
    · rw [hfun, Complex.ofReal_zero, add_zero]
  · have hfun : DirichletCharacter.gammaFactor χ = Complex.Gammaℝ ∘ fun z ↦ z + 1 :=
      funext fun z ↦ ho.gammaFactor_def z
    have hs1 : 0 < (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
    have hd : DifferentiableAt ℂ Complex.Gammaℝ ((fun z : ℂ ↦ z + 1) s) :=
      differentiableAt_Gammaℝ hs1
    refine ⟨1, zero_le_one, le_rfl, ?_, ?_⟩
    · rw [hfun]; exact hd.comp s (differentiableAt_id.add_const 1)
    · rw [hfun, logDeriv_comp (f := Complex.Gammaℝ) (g := fun z : ℂ ↦ z + 1) (x := s) hd
        (differentiableAt_id.add_const 1), Complex.ofReal_one]
      rw [show deriv (fun z : ℂ ↦ z + 1) s = 1 from ((hasDerivAt_id s).add_const 1).deriv]
      rw [mul_one]

/-- M3-6: `Λ'/Λ = γ'/γ + L'/L` on `1 < Re s`. -/
private theorem logDeriv_completedLFunction_eq {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    logDeriv (DirichletCharacter.completedLFunction χ) s =
      logDeriv (DirichletCharacter.gammaFactor χ) s + logDeriv χ.LFunction s := by
  have hγ0 (z : ℂ) (hz : 0 < z.re) : DirichletCharacter.gammaFactor χ z ≠ 0 := by
    rcases χ.even_or_odd with he | ho
    · rw [he.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos hz
    · rw [ho.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      DirichletCharacter.gammaFactor χ * χ.LFunction := by
    filter_upwards [(isOpen_lt (continuous_const : Continuous fun _ : ℂ ↦ (0 : ℝ))
      Complex.continuous_re).mem_nhds (show (0 : ℝ) < s.re by linarith)] with z hz
    have hz0 : z ≠ 0 := fun h ↦ by rw [h, Complex.zero_re] at hz; exact lt_irrefl _ hz
    rw [Pi.mul_apply, DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (.inl hz0),
      mul_div_cancel₀ _ (hγ0 z hz)]
  obtain ⟨a, -, -, hdγ, -⟩ := logDeriv_gammaFactor χ (show 0 < s.re by linarith)
  rw [logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds, ← logDeriv_apply]
  exact logDeriv_mul s (hγ0 s (by linarith))
    (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (.inl hχ) hs.le) hdγ
    (DirichletCharacter.differentiableAt_LFunction χ s (.inr hχ))

open scoped LSeries.notation in
/-- **M3: the uniform bound on the line `Re s = 2`.** For every nontrivial Dirichlet character,
`Re Λ'/Λ(2 + it)` is `log (|t| + 2) / 2` up to an absolute constant. -/
private theorem abs_re_logDeriv_completed_sub_le {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hχ : χ ≠ 1) (t : ℝ) :
    |(logDeriv (DirichletCharacter.completedLFunction χ) (2 + t * Complex.I)).re -
        Real.log (|t| + 2) / 2| ≤
      (Real.log Real.pi + Real.log 4 + 1) / 2 +
        ∑' n, ‖LSeries.term ↗ArithmeticFunction.vonMangoldt 2 n‖ := by
  have hs : (2 + t * Complex.I).re = 2 := by simp
  rw [logDeriv_completedLFunction_eq hχ (by rw [hs]; norm_num)]
  obtain ⟨a, ha0, ha1, -, hγ⟩ := logDeriv_gammaFactor χ (show 0 < (2 + t * Complex.I).re by
    rw [hs]; norm_num)
  rw [hγ, Complex.add_re]
  have h1 := abs_re_logDeriv_Gammaℝ_sub_le ha0 ha1 t
  have hpt : (2 + t * Complex.I) + (a : ℂ) = ((2 + a : ℝ) : ℂ) + t * Complex.I := by
    push_cast; ring
  rw [← hpt] at h1
  have h2 := (Complex.abs_re_le_norm _).trans (norm_logDeriv_LFunction_le χ (le_of_eq hs.symm))
  rw [abs_le] at h1 h2 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end M3


/-! ### M4: counting zeros -/

section M4

open MeasureTheory

/-- The Lorentz kernel integrates to an arctan difference. -/
private theorem integral_lorentz {c : ℝ} (hc : 0 < c) (γ a b : ℝ) :
    ∫ t in a..b, c / (c ^ 2 + (t - γ) ^ 2) =
      Real.arctan ((b - γ) / c) - Real.arctan ((a - γ) / c) := by
  have hderiv (t : ℝ) : HasDerivAt (fun t ↦ Real.arctan ((t - γ) / c))
      (c / (c ^ 2 + (t - γ) ^ 2)) t := by
    have h := (Real.hasDerivAt_arctan ((t - γ) / c)).comp t
      (((hasDerivAt_id t).sub_const γ).div_const c)
    have hpos : 0 < c ^ 2 + (t - γ) ^ 2 := add_pos_of_pos_of_nonneg (pow_pos hc 2) (sq_nonneg _)
    have heq : 1 / (1 + ((t - γ) / c) ^ 2) * (1 / c) = c / (c ^ 2 + (t - γ) ^ 2) := by
      field_simp
    exact h.congr_deriv heq
  have hcont : Continuous fun t : ℝ ↦ c / (c ^ 2 + (t - γ) ^ 2) := by
    exact continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
      fun t ↦ (add_pos_of_pos_of_nonneg (pow_pos hc 2) (sq_nonneg _)).ne'
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ ↦ hderiv t)
    (hcont.intervalIntegrable a b)

/-- The Lorentz kernel integrates to at most `π` over any interval. -/
private theorem integral_lorentz_le_pi {c : ℝ} (hc : 0 < c) (γ a b : ℝ) :
    ∫ t in a..b, c / (c ^ 2 + (t - γ) ^ 2) ≤ Real.pi := by
  rw [integral_lorentz hc]
  linarith [Real.arctan_lt_pi_div_two ((b - γ) / c), Real.neg_pi_div_two_lt_arctan ((a - γ) / c)]

/-- One sample of the Lorentz kernel at width `c ≥ 1` is at most twice its integral over the
unit interval centred at the sample. -/
private theorem lorentz_le_two_integral {c : ℝ} (hc : 1 ≤ c) (γ x : ℝ) :
    c / (c ^ 2 + (x - γ) ^ 2) ≤ 2 * ∫ t in (x - 1 / 2)..(x + 1 / 2), c / (c ^ 2 + (t - γ) ^ 2) := by
  have hc0 : 0 < c := by linarith
  have hcont : Continuous fun t : ℝ ↦ c / (c ^ 2 + (t - γ) ^ 2) := by
    exact continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
      fun t ↦ (add_pos_of_pos_of_nonneg (pow_pos hc0 2) (sq_nonneg _)).ne'
  have hlow : ∀ t ∈ Set.Icc (x - 1 / 2) (x + 1 / 2),
      c / (2 * (c ^ 2 + (x - γ) ^ 2)) ≤ c / (c ^ 2 + (t - γ) ^ 2) := by
    intro t ht
    apply div_le_div_of_nonneg_left hc0.le
      (add_pos_of_pos_of_nonneg (pow_pos hc0 2) (sq_nonneg _))
    have h1 : (t - x) ^ 2 ≤ 1 / 4 := by
      nlinarith [mul_nonneg (sub_nonneg.2 ht.1) (sub_nonneg.2 ht.2)]
    nlinarith [sq_nonneg (t - x - (x - γ)), sq_nonneg (t - x + (x - γ))]
  have hint := intervalIntegral.integral_mono_on (by linarith)
    (continuous_const.intervalIntegrable (μ := volume) _ _) (hcont.intervalIntegrable _ _) hlow
  rw [intervalIntegral.integral_const, smul_eq_mul, show x + 1 / 2 - (x - 1 / 2) = 1 by ring,
    one_mul] at hint
  have : c / (c ^ 2 + (x - γ) ^ 2) = 2 * (c / (2 * (c ^ 2 + (x - γ) ^ 2))) := by
    field_simp
  linarith

/-- **The per-zero bound**: the Lorentz kernel of width `c ∈ [1, 2]` summed over any range of
consecutive integers is at most `2π`. -/
private theorem sum_lorentz_le {c : ℝ} (hc : 1 ≤ c) (γ : ℝ) (k₀ n : ℕ) :
    ∑ j ∈ Finset.range n, c / (c ^ 2 + (((k₀ + j : ℕ) : ℝ) - γ) ^ 2) ≤ 2 * Real.pi := by
  have hc0 : 0 < c := by linarith
  have hcont : Continuous fun t : ℝ ↦ c / (c ^ 2 + (t - γ) ^ 2) := by
    exact continuous_const.div (continuous_const.add ((continuous_id.sub continuous_const).pow 2))
      fun t ↦ (add_pos_of_pos_of_nonneg (pow_pos hc0 2) (sq_nonneg _)).ne'
  set a : ℕ → ℝ := fun j ↦ ((k₀ + j : ℕ) : ℝ) - 1 / 2
  have hadj := intervalIntegral.sum_integral_adjacent_intervals (a := a) (n := n)
    (f := fun t ↦ c / (c ^ 2 + (t - γ) ^ 2)) (μ := volume)
    (fun j _ ↦ hcont.intervalIntegrable _ _)
  calc ∑ j ∈ Finset.range n, c / (c ^ 2 + (((k₀ + j : ℕ) : ℝ) - γ) ^ 2)
      ≤ ∑ j ∈ Finset.range n, 2 * ∫ t in a j..a (j + 1), c / (c ^ 2 + (t - γ) ^ 2) := by
        refine Finset.sum_le_sum fun j _ ↦ ?_
        have h := lorentz_le_two_integral hc γ ((k₀ + j : ℕ) : ℝ)
        have e1 : a j = ((k₀ + j : ℕ) : ℝ) - 1 / 2 := rfl
        have e2 : a (j + 1) = ((k₀ + j : ℕ) : ℝ) + 1 / 2 := by
          simp only [a]; push_cast; ring
        rw [e1, e2]; exact h
    _ = 2 * ∫ t in a 0..a n, c / (c ^ 2 + (t - γ) ^ 2) := by rw [← Finset.mul_sum, hadj]
    _ ≤ 2 * Real.pi := by
        have := integral_lorentz_le_pi hc0 γ (a 0) (a n)
        linarith

open scoped LSeries.notation in
/-- S2: at a real point `σ ≥ 2`, `Re Λ'/Λ(σ) ≤ log σ / 2 + 1/2 + ∑ Λ(n) n⁻²`. -/
private theorem re_logDeriv_completed_real_le {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hχ : χ ≠ 1) {σ : ℝ} (hσ : 2 ≤ σ) :
    (logDeriv (DirichletCharacter.completedLFunction χ) σ).re ≤
      Real.log σ / 2 + 1 / 2 + ∑' n, ‖LSeries.term ↗ArithmeticFunction.vonMangoldt 2 n‖ := by
  have hre : (σ : ℂ).re = σ := Complex.ofReal_re σ
  rw [logDeriv_completedLFunction_eq hχ (by rw [hre]; linarith)]
  obtain ⟨a, ha0, ha1, -, hγ⟩ := logDeriv_gammaFactor χ (show 0 < (σ : ℂ).re by rw [hre]; linarith)
  rw [hγ, Complex.add_re]
  have hw : 0 < ((σ : ℂ) + a).re := by simp; linarith
  rw [logDeriv_Gammaℝ hw, Complex.add_re, Complex.div_ofNat_re, Complex.div_ofNat_re,
    Complex.neg_re, ← Complex.ofReal_log Real.pi_pos.le, Complex.ofReal_re]
  set z : ℂ := ((σ : ℂ) + a) / 2
  have hzre : z.re = (σ + a) / 2 := by simp [z]
  have hz1 : 1 ≤ z.re := by rw [hzre]; linarith
  have hdig := (abs_le.mp (abs_re_digamma_sub_log_le hz1)).2
  have hzn : ‖z‖ ≤ σ := by
    have : z = (((σ + a) / 2 : ℝ) : ℂ) := by simp [z]
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by linarith)]; linarith
  have hlog : Real.log ‖z‖ ≤ Real.log σ :=
    Real.log_le_log (by linarith [Complex.re_le_norm z]) hzn
  have hπ : 0 < Real.log Real.pi := Real.log_pos (by linarith [Real.pi_gt_three])
  have hL := (Complex.re_le_norm _).trans (norm_logDeriv_LFunction_le χ
    (show 2 ≤ (σ : ℂ).re by rw [hre]; exact hσ))
  linarith

/-- The real part of a resolvent term at `σ + i t`. -/
private theorem re_resolvent_term (d : ℝ) (σ t : ℝ) (ρ : ℂ) :
    ((d : ℂ) / ((σ : ℂ) + t * Complex.I - ρ)).re =
      d * ((σ - ρ.re) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)) := by
  rw [div_eq_mul_inv, Complex.re_ofReal_mul, Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.add_im, Complex.mul_im]
  ring_nf

/-- S3a: **the per-zero bound.** A zero `β + iγ` (`0 < β < 1`) of multiplicity `d` contributes
to the samples `2 + i t_j` (`T/2 ≤ t_j ≤ T`) at most `2π d` if `|γ| ≤ 2T`, and at most `κ` times
its contribution at the real point `2T` otherwise, where `κ = 16 n / (2T - 1)`. -/
private theorem per_zero_bound {β γ d T : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hd : 0 ≤ d) (hT : 1 ≤ T)
    (k₀ n : ℕ) (hsamp : ∀ j < n, T / 2 ≤ ((k₀ + j : ℕ) : ℝ) ∧ ((k₀ + j : ℕ) : ℝ) ≤ T) :
    ∑ j ∈ Finset.range n, d * ((2 - β) / ((2 - β) ^ 2 + (((k₀ + j : ℕ) : ℝ) - γ) ^ 2)) ≤
      (if |γ| ≤ 2 * T then 2 * Real.pi * d else 0) +
        16 * n / (2 * T - 1) * (d * ((2 * T - β) / ((2 * T - β) ^ 2 + (0 - γ) ^ 2))) := by
  have hc1 : 1 ≤ 2 - β := by linarith
  have hT1 : 0 < 2 * T - 1 := by linarith
  have hG : 0 ≤ d * ((2 * T - β) / ((2 * T - β) ^ 2 + (0 - γ) ^ 2)) :=
    mul_nonneg hd (div_nonneg (by linarith) (by positivity))
  have hκ : 0 ≤ 16 * (n : ℝ) / (2 * T - 1) := by positivity
  split_ifs with hγ
  · rw [← Finset.mul_sum]
    have h := sum_lorentz_le hc1 γ k₀ n
    nlinarith [mul_nonneg hκ hG]
  · rw [zero_add]
    rw [not_le] at hγ
    have hγ2 : 0 < γ ^ 2 := by
      have : 0 < |γ| := by linarith
      nlinarith [sq_abs γ]
    have hterm : ∀ j ∈ Finset.range n, d * ((2 - β) / ((2 - β) ^ 2 + (((k₀ + j : ℕ) : ℝ) - γ) ^ 2))
        ≤ d * (8 / γ ^ 2) := by
      intro j hj
      obtain ⟨h1, h2⟩ := hsamp j (Finset.mem_range.mp hj)
      apply mul_le_mul_of_nonneg_left _ hd
      have hdist : γ ^ 2 / 4 ≤ (((k₀ + j : ℕ) : ℝ) - γ) ^ 2 := by
        have ht0 : 0 ≤ ((k₀ + j : ℕ) : ℝ) := Nat.cast_nonneg _
        have habs : |γ| / 2 ≤ |((k₀ + j : ℕ) : ℝ) - γ| := by
          rw [abs_sub_comm]
          have := abs_sub_abs_le_abs_sub γ ((k₀ + j : ℕ) : ℝ)
          rw [abs_of_nonneg ht0] at this
          linarith
        have := mul_self_le_mul_self (by positivity) habs
        rw [← sq_abs (((k₀ + j : ℕ) : ℝ) - γ)]
        nlinarith [sq_abs γ]
      rw [div_le_div_iff₀ (by positivity) hγ2]
      nlinarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hfar : d * (8 / γ ^ 2) * n ≤
        16 * n / (2 * T - 1) * (d * ((2 * T - β) / ((2 * T - β) ^ 2 + (0 - γ) ^ 2))) := by
      have hden : (2 * T - β) ^ 2 + (0 - γ) ^ 2 ≤ 2 * γ ^ 2 := by
        have : (2 * T - β) ^ 2 ≤ γ ^ 2 := by
          have h4 : (2 * T) ^ 2 < γ ^ 2 := by nlinarith [sq_abs γ, abs_nonneg γ]
          nlinarith
        nlinarith
      have hnum : 2 * T - 1 ≤ 2 * T - β := by linarith
      have hratio : (2 * T - 1) / (2 * γ ^ 2) ≤ (2 * T - β) / ((2 * T - β) ^ 2 + (0 - γ) ^ 2) := by
        have hpos : 0 < (2 * T - β) ^ 2 + (0 - γ) ^ 2 := by nlinarith [sq_nonneg (2 * T - β)]
        rw [div_le_div_iff₀ (by positivity) hpos]
        nlinarith
      calc d * (8 / γ ^ 2) * n = 16 * n / (2 * T - 1) * (d * ((2 * T - 1) / (2 * γ ^ 2))) := by
            field_simp
            ring
        _ ≤ _ := by gcongr
    linarith

private theorem re_resolvent_term_int (z : ℤ) (σ t : ℝ) (ρ : ℂ) :
    ((z : ℂ) / ((σ : ℂ) + t * Complex.I - ρ)).re =
      (z : ℝ) * ((σ - ρ.re) / ((σ - ρ.re) ^ 2 + (t - ρ.im) ^ 2)) := by
  have h := re_resolvent_term (z : ℝ) σ t ρ
  rwa [Complex.ofReal_intCast] at h

open scoped LSeries.notation in
/-- S3b: **the core counting inequality.** For a nontrivial primitive character `χ` mod `m` and
`T ≥ 8`, with `K` the constant of M3,
`⌊T/2⌋ (log (T/2) / 2 - 2K - log 2 / 2) ≤ 2π N + 8 (log (2T)/2 + log m + 1/2 + B + log 2/2 + K)`,
where `N` counts the zeros of `Λ` with `|γ| ≤ 2T` with multiplicity. -/
private theorem zero_count_core {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {T : ℝ} (hT : 8 ≤ T) :
    let B := ∑' n, ‖LSeries.term ↗ArithmeticFunction.vonMangoldt 2 n‖
    let K := (Real.log Real.pi + Real.log 4 + 1) / 2 + B
    (⌊T / 2⌋₊ : ℝ) * (Real.log (T / 2) / 2 - (2 * K + Real.log 2 / 2)) ≤
      2 * Real.pi * ∑' r : {ρ : ℂ // 0 < MeromorphicOn.divisor
          (DirichletCharacter.completedLFunction χ) Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2},
          (if |r.val.im| ≤ 2 * T then
            (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ r.val : ℝ)
            else 0) +
        8 * (Real.log (2 * T) / 2 + Real.log m + (1 / 2 + B + Real.log 2 / 2 + K)) := by
  intro B K
  have hB : ∑' n, ‖LSeries.term ↗ArithmeticFunction.vonMangoldt 2 n‖ = B := rfl
  have hK : (Real.log Real.pi + Real.log 4 + 1) / 2 + B = K := rfl
  have hχi : χ⁻¹ ≠ 1 := fun h' ↦ hχ (inv_eq_one.mp h')
  obtain ⟨C, hres, hClow, hCup⟩ := resolvent_identity_bounds χ hprim hχ
  set Λ := DirichletCharacter.completedLFunction χ with hΛ
  set d : {ρ : ℂ // 0 < MeromorphicOn.divisor Λ Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2} → ℤ :=
    fun r ↦ MeromorphicOn.divisor Λ Set.univ r.val with hd
  have hd0 (r) : (0 : ℝ) ≤ d r := by exact_mod_cast r.2.1.le
  have hβ (r : {ρ : ℂ // 0 < MeromorphicOn.divisor Λ Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2}) :
      0 < r.val.re ∧ r.val.re < 1 := by
    have := abs_lt.mp r.2.2; constructor <;> linarith
  -- the samples
  set n := ⌊T / 2⌋₊
  set k₀ := ⌈T / 2⌉₊
  have hsamp : ∀ j < n, T / 2 ≤ ((k₀ + j : ℕ) : ℝ) ∧ ((k₀ + j : ℕ) : ℝ) ≤ T := by
    intro j hj
    have h1 : T / 2 ≤ (k₀ : ℝ) := Nat.le_ceil _
    have h2 : (k₀ : ℝ) < T / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
    have h3 : (n : ℝ) ≤ T / 2 := Nat.floor_le (by linarith)
    have h4 : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
    push_cast
    constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  -- M3 at `t = 0`, for `χ` and `χ⁻¹`
  have hM0 := abs_re_logDeriv_completed_sub_le hχ 0
  have hM0i := abs_re_logDeriv_completed_sub_le hχi 0
  simp only [Complex.ofReal_zero, zero_mul, add_zero, abs_zero, zero_add] at hM0 hM0i
  rw [hB, hK] at hM0 hM0i
  rw [abs_le] at hM0 hM0i
  -- the sampled resolvent identities
  have hsampled (j : ℕ) : HasSum (fun r ↦ ((d r : ℂ) / ((2 : ℝ) + ((k₀ + j : ℕ) : ℝ) * Complex.I
      - r.val)).re) ((logDeriv Λ ((2 : ℝ) + ((k₀ + j : ℕ) : ℝ) * Complex.I)).re + C) :=
    hres _ (by simp)
  have hlowj (j : ℕ) (hj : j < n) :
      Real.log (T / 2) / 2 - (2 * K + Real.log 2 / 2) ≤
        (logDeriv Λ ((2 : ℝ) + ((k₀ + j : ℕ) : ℝ) * Complex.I)).re + C := by
    have hM := abs_re_logDeriv_completed_sub_le hχ ((k₀ + j : ℕ) : ℝ)
    rw [hB, hK, abs_le] at hM
    have ht := (hsamp j hj).1
    have hlog : Real.log (T / 2) ≤ Real.log (|((k₀ + j : ℕ) : ℝ)| + 2) :=
      Real.log_le_log (by linarith) (by rw [abs_of_nonneg (Nat.cast_nonneg _)]; linarith)
    have e2 : ((2 : ℝ) : ℂ) = 2 := by norm_num
    rw [e2]
    linarith [hM.1, hM0.2]
  have hsumS := hasSum_sum (s := Finset.range n) fun j _ ↦ hsampled j
  -- the comparison series
  set s₂ : ℂ := ((2 * T : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I
  have hs₂ : 1 < s₂.re := by simp [s₂]; linarith
  have hG := hres s₂ hs₂
  have hW := summable_weight (C := C) (hres _ (by norm_num))
  set κ : ℝ := 16 * n / (2 * T - 1)
  have hA : Summable fun r : {ρ : ℂ // 0 < MeromorphicOn.divisor Λ Set.univ ρ ∧
      |ρ.re - 1 / 2| < 1 / 2} ↦ (if |r.val.im| ≤ 2 * T then (d r : ℝ) else 0) := by
    refine Summable.of_nonneg_of_le (fun r ↦ by split_ifs <;> simp [hd0 r]) (fun r ↦ ?_)
      (hW.mul_left (25 / 4 + 4 * T ^ 2))
    split_ifs with hnear
    · have hz : (5 / 2 : ℂ) - r.val ≠ 0 := sub_ne_zero.mpr (five_halves_ne r)
      have hn2 : 0 < ‖(5 / 2 : ℂ) - r.val‖ ^ 2 := by positivity
      have hbound : ‖(5 / 2 : ℂ) - r.val‖ ^ 2 ≤ 25 / 4 + 4 * T ^ 2 := by
        rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
        simp only [Complex.sub_re, Complex.sub_im]
        norm_num
        have h1 := hβ r
        have h2 : r.val.im ^ 2 ≤ 4 * T ^ 2 := by nlinarith [sq_abs r.val.im, abs_nonneg r.val.im]
        nlinarith
      rw [mul_div_assoc', le_div_iff₀ hn2]
      nlinarith [hd0 r]
    · exact mul_nonneg (by positivity) (div_nonneg (hd0 r) (by positivity))
  have hcomb := (hA.hasSum.mul_left (2 * Real.pi)).add (hG.mul_left κ)
  have hle := hasSum_le (fun r ↦ ?_) hsumS hcomb
  · -- assemble
    have hlow : (n : ℝ) * (Real.log (T / 2) / 2 - (2 * K + Real.log 2 / 2)) ≤
        ∑ j ∈ Finset.range n, ((logDeriv Λ ((2 : ℝ) + ((k₀ + j : ℕ) : ℝ) * Complex.I)).re + C) := by
      have := Finset.sum_le_sum fun j hj ↦ hlowj j (Finset.mem_range.mp hj)
      rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at this
    have hκ : κ ≤ 8 := by
      have h3 : (n : ℝ) ≤ T / 2 := Nat.floor_le (by linarith)
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have hκ0 : 0 ≤ κ := div_nonneg (by positivity) (by linarith)
    have hGnn : 0 ≤ (logDeriv Λ s₂).re + C := hG.nonneg fun r ↦ by
      rw [show s₂ = ((2 * T : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I from rfl,
        re_resolvent_term_int]
      have := hβ r
      exact mul_nonneg (hd0 r) (div_nonneg (by linarith) (by positivity))
    have hreal : (logDeriv Λ s₂).re ≤ Real.log (2 * T) / 2 + 1 / 2 + B := by
      have := re_logDeriv_completed_real_le hχ (σ := 2 * T) (by linarith)
      rw [hB] at this
      simpa [s₂] using this
    have hGup : (logDeriv Λ s₂).re + C ≤ Real.log (2 * T) / 2 + Real.log m +
        (1 / 2 + B + Real.log 2 / 2 + K) := by
      linarith [hM0i.2]
    have hfin : κ * ((logDeriv Λ s₂).re + C) ≤ 8 * (Real.log (2 * T) / 2 + Real.log m +
        (1 / 2 + B + Real.log 2 / 2 + K)) := by
      calc κ * ((logDeriv Λ s₂).re + C) ≤ 8 * ((logDeriv Λ s₂).re + C) :=
            mul_le_mul_of_nonneg_right hκ hGnn
        _ ≤ _ := by linarith
    simp only [hd] at hle hlow
    linarith
  · -- the per-zero bound
    rw [show s₂ = ((2 * T : ℝ) : ℂ) + ((0 : ℝ) : ℂ) * Complex.I from rfl, re_resolvent_term_int]
    have hrw (j : ℕ) : ((d r : ℂ) / ((2 : ℝ) + ((k₀ + j : ℕ) : ℝ) * Complex.I - r.val)).re =
        (d r : ℝ) * ((2 - r.val.re) / ((2 - r.val.re) ^ 2 + (((k₀ + j : ℕ) : ℝ) - r.val.im) ^ 2)) :=
      re_resolvent_term_int _ _ _ _
    simp only [hrw]
    have h := per_zero_bound (hβ r).1 (hβ r).2 (hd0 r) (by linarith) k₀ n hsamp
      (γ := r.val.im)
    have e : (if |r.val.im| ≤ 2 * T then 2 * Real.pi * (d r : ℝ) else 0) =
        2 * Real.pi * (if |r.val.im| ≤ 2 * T then (d r : ℝ) else 0) := by split_ifs <;> simp
    rw [e] at h
    convert h using 3

/-- S4a: in `0 < Re s`, the order of `L(χ, ·)` is the divisor of the completed L-function. -/
private theorem toNat_analyticOrderAt_eq_divisor {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    ((analyticOrderAt χ.LFunction s).toNat : ℤ) =
      MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ s := by
  have hU : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt (continuous_const : Continuous fun _ : ℂ ↦ (0 : ℝ)) Complex.continuous_re
  have hγd : DifferentiableOn ℂ (DirichletCharacter.gammaFactor χ) {z : ℂ | 0 < z.re} :=
    fun z hz ↦ (logDeriv_gammaFactor χ hz).choose_spec.2.2.1.differentiableWithinAt
  have hγan : AnalyticAt ℂ (DirichletCharacter.gammaFactor χ) s :=
    hγd.analyticAt (hU.mem_nhds hs)
  have hγ0 (z : ℂ) (hz : 0 < z.re) : DirichletCharacter.gammaFactor χ z ≠ 0 := by
    rcases χ.even_or_odd with he | ho
    · rw [he.gammaFactor_def]; exact Complex.Gammaℝ_ne_zero_of_re_pos hz
    · rw [ho.gammaFactor_def]
      exact Complex.Gammaℝ_ne_zero_of_re_pos (by rw [Complex.add_re, Complex.one_re]; linarith)
  have hev : DirichletCharacter.completedLFunction χ =ᶠ[nhds s]
      DirichletCharacter.gammaFactor χ * χ.LFunction := by
    filter_upwards [hU.mem_nhds hs] with z hz
    have hz0 : z ≠ 0 := fun h ↦ by
      rw [h] at hz; simp only [Complex.zero_re, lt_irrefl] at hz
    rw [Pi.mul_apply, DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ z (.inl hz0),
      mul_div_cancel₀ _ (hγ0 z hz)]
  have hL : AnalyticAt ℂ χ.LFunction s :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have hΛ := DirichletCharacter.differentiable_completedLFunction hχ
  rw [MeromorphicOn.divisor_apply (fun z _ ↦ (hΛ.analyticAt z).meromorphicAt) (Set.mem_univ s),
    meromorphicOrderAt_congr (hev.filter_mono nhdsWithin_le_nhds),
    meromorphicOrderAt_mul_of_ne_zero hγan (hγ0 s hs), hL.meromorphicOrderAt_eq]
  cases analyticOrderAt χ.LFunction s using ENat.recTopCoe with
  | top => simp
  | coe n => simp

/-- S4b: the zeros of `Λ` with `|γ| ≤ T'`, counted with multiplicity, are at most
`dirichletStripZeroCount χ T'`. -/
private theorem near_tsum_le_count {m : ℕ} [NeZero m] {χ : DirichletCharacter ℂ m}
    (hχ : χ ≠ 1) (T' : ℝ) :
    ∑' r : {ρ : ℂ // 0 < MeromorphicOn.divisor
        (DirichletCharacter.completedLFunction χ) Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2},
        (if |r.val.im| ≤ T' then
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) Set.univ r.val : ℝ)
          else 0) ≤
      (dirichletStripZeroCount χ T' : ℝ) := by
  classical
  set Λ := DirichletCharacter.completedLFunction χ
  set g : ℂ → ℕ := fun s ↦ (analyticOrderAt χ.LFunction s).toNat with hg
  set R : Set ℂ := {s | 0 < s.re ∧ s.re < 1 ∧ |s.im| ≤ T'} with hR
  -- finiteness in the closed rectangle
  set Kc : Set ℂ := {s | 0 ≤ s.re ∧ s.re ≤ 1 ∧ |s.im| ≤ T'} with hKc
  have hKcomp : IsCompact Kc := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const Complex.continuous_re).inter
        ((isClosed_le Complex.continuous_re continuous_const).inter
          (isClosed_le (continuous_abs.comp Complex.continuous_im) continuous_const))
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 1 + |T'|)).subset fun s hs ↦ ?_
      rw [Metric.mem_closedBall, dist_zero_right]
      obtain ⟨h1, h2, h3⟩ := hs
      have := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_nonneg h1] at this
      linarith [le_abs_self T']
  have hfinK := (Function.locallyFinsupp.locallyFiniteSupport
    (MeromorphicOn.divisor Λ Set.univ)).finite_inter_support_of_isCompact hKcomp
  have hgd (s : ℂ) (hs : 0 < s.re) : (g s : ℤ) = MeromorphicOn.divisor Λ Set.univ s :=
    toNat_analyticOrderAt_eq_divisor hχ hs
  have hfin : (R ∩ Function.support g).Finite := by
    refine hfinK.subset fun s ⟨hsR, hsg⟩ ↦ ⟨⟨hsR.1.le, hsR.2.1.le, hsR.2.2⟩, ?_⟩
    change MeromorphicOn.divisor Λ Set.univ s ≠ 0
    rw [← hgd s hsR.1]
    exact_mod_cast hsg
  have hN : (dirichletStripZeroCount χ T' : ℝ) =
      ∑ s ∈ hfin.toFinset, (g s : ℝ) := by
    have e : dirichletStripZeroCount χ T' = ∑ᶠ s ∈ R, g s := rfl
    rw [e, ← finsum_mem_inter_support, finsum_mem_eq_finite_toFinset_sum _ hfin]
    push_cast; rfl
  rw [hN]
  refine tsum_le_of_sum_le' (Finset.sum_nonneg fun _ _ ↦ Nat.cast_nonneg _) fun F ↦ ?_
  rw [← Finset.sum_filter]
  set F' := F.filter fun r ↦ |r.val.im| ≤ T'
  let emb : {ρ : ℂ // 0 < MeromorphicOn.divisor Λ Set.univ ρ ∧ |ρ.re - 1 / 2| < 1 / 2} ↪ ℂ :=
    ⟨Subtype.val, Subtype.val_injective⟩
  have hmap : ∑ r ∈ F', (MeromorphicOn.divisor Λ Set.univ r.val : ℝ) =
      ∑ s ∈ F'.map emb, (g s : ℝ) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun r _ ↦ ?_
    have hre : 0 < r.val.re := by have := abs_lt.mp r.2.2; linarith
    change (MeromorphicOn.divisor Λ Set.univ r.val : ℝ) = ((g r.val : ℕ) : ℝ)
    rw [← hgd r.val hre]; push_cast; rfl
  rw [hmap]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun s hs ↦ ?_) fun _ _ _ ↦ Nat.cast_nonneg _
  obtain ⟨r, hrF, rfl⟩ := Finset.mem_map.mp hs
  have hnear := (Finset.mem_filter.mp hrF).2
  have hab := abs_lt.mp r.2.2
  have hre : 0 < r.val.re := by linarith
  rw [Set.Finite.mem_toFinset]
  refine ⟨⟨hre, by change r.val.re < 1; linarith [hab.2], hnear⟩, ?_⟩
  change g r.val ≠ 0
  intro h0
  have := hgd r.val hre
  rw [h0] at this
  exact (ne_of_gt r.2.1) this.symm

open scoped LSeries.notation in
/-- **M4: the lower bound for the zero count.** For a nontrivial primitive Dirichlet character
`χ` modulo `m` and `T ≥ 8`, with absolute constants `K`, `B` (see M3),
`2π N(2T, χ) ≥ ⌊T/2⌋ (log (T/2)/2 - 2K - log 2/2)
  - 8 (log (2T)/2 + log m + 1/2 + B + log 2/2 + K)`. -/
theorem dirichletStripZeroCount_lower {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {T : ℝ} (hT : 8 ≤ T) :
    let B := ∑' n, ‖LSeries.term ↗ArithmeticFunction.vonMangoldt 2 n‖
    let K := (Real.log Real.pi + Real.log 4 + 1) / 2 + B
    (⌊T / 2⌋₊ : ℝ) * (Real.log (T / 2) / 2 - (2 * K + Real.log 2 / 2)) -
        8 * (Real.log (2 * T) / 2 + Real.log m + (1 / 2 + B + Real.log 2 / 2 + K)) ≤
      2 * Real.pi * (dirichletStripZeroCount χ (2 * T) : ℝ) := by
  simp only
  have h1 := zero_count_core χ hprim hχ hT
  have h2 := near_tsum_le_count hχ (2 * T)
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have := mul_le_mul_of_nonneg_left h2 hπ
  simp only at h1
  linarith

end M4

end RiemannMasullo.DirichletZeroCount
