module

public import RiemannMasullo.AppD_SchwartzBruhat.Sec3a_part2
public import Mathlib.Analysis.Distribution.TestFunction

/-!
# Uniform Fourier–Mellin estimates, jump singularities and compactly supported tests

Masullo, Appendix D, §§D.3.4–D.3.6, pp. 815–821.
-/

@[expose] public noncomputable section

namespace RiemannMasullo

open Bornology Filter Function MeasureTheory Set Topology TopologicalSpace
open scoped ContDiff Distributions NNReal

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [hT2 : T2Space G] [LocallyCompactSpace G]
variable (m : G →ₜ* ℝ≥0ˣ)

section RiemannLebesgue

variable (I : Set ℝ) (hm : IsModulation m) (hms : Surjective m)

/-- A continuous real-valued additive character vanishes on a subgroup with open annihilator. -/
private theorem le_ker_of_isOpen_lcaAnnihilator
    (l : G →ₜ* Multiplicative ℝ) {k : Subgroup G}
    (hk : IsOpen (lcaAnnihilator k : Set (PontryaginDual G))) :
    k ≤ l.toMonoidHom.ker := by
  let χ (t : ℝ) : PontryaginDual G :=
    { toFun := fun x ↦ Circle.exp (t * Multiplicative.toAdd (l x))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        rw [map_mul l]
        change Circle.exp (t * (Multiplicative.toAdd (l x) + Multiplicative.toAdd (l y))) = _
        rw [mul_add, Circle.exp_add]
      continuous_toFun := Circle.exp.continuous.comp
        (continuous_const.mul (continuous_toAdd.comp l.continuous)) }
  have hχ : Continuous χ :=
    ContinuousMonoidHom.continuous_of_continuous_uncurry χ
      (Circle.exp.continuous.comp
        (continuous_fst.mul ((continuous_toAdd.comp l.continuous).comp continuous_snd)))
  have hAll : χ ⁻¹' (lcaAnnihilator k : Set (PontryaginDual G)) = univ :=
    IsClopen.eq_univ ⟨((lcaAnnihilator k).isClosed_of_isOpen hk).preimage hχ, hk.preimage hχ⟩
      ⟨0, (mem_lcaAnnihilator_iff k (χ 0)).2 fun x ↦ by
        change Circle.exp (0 * Multiplicative.toAdd (l x.val)) = 1
        simp⟩
  intro x hx
  change Multiplicative.toAdd (l x) = 0
  by_contra h
  let t := Real.pi / Multiplicative.toAdd (l x)
  have ht : t ∈ χ ⁻¹' (lcaAnnihilator k : Set (PontryaginDual G)) := hAll.symm ▸ mem_univ t
  have hxχ := (mem_lcaAnnihilator_iff k (χ t)).1 ht ⟨x, hx⟩
  change Circle.exp (t * Multiplicative.toAdd (l x)) = 1 at hxχ
  exact Circle.exp_pi_ne_one (by simpa only [t, div_mul_cancel₀ _ h] using hxχ)

/-- In each discrete fibre, the lift of a continuous real-valued additive character
is an affine, smooth function of the real and torus cover coordinates. -/
private theorem contDiff_logHom_elementaryCover {d t r : ℕ} {F A : Type*}
    [AddCommGroup F] [TopologicalSpace F] [CommGroup A] [TopologicalSpace A]
    (e : Multiplicative (ElementaryLieGroup d t r F) ≃ₜ* A) (n : A →ₜ* Multiplicative ℝ)
    (z : Fin r → ℤ) (b : F) (p : ℕ∞ω) :
    ContDiff ℝ p (fun xt ↦ Multiplicative.toAdd
      (n (e (Multiplicative.ofAdd (elementaryCover xt z b))))) := by
  let l : ElementaryLieGroup d t r F →+ ℝ :=
    AddMonoidHom.mk' (fun y ↦ Multiplicative.toAdd (n (e (Multiplicative.ofAdd y)))) <| by
      intro x y
      rw [← toAdd_mul, ← map_mul n]
      exact congrArg (fun q ↦ Multiplicative.toAdd (n q))
        (e.map_mul' (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))
  have hl : Continuous l :=
    continuous_toAdd.comp (n.continuous.comp (e.continuous_toFun.comp continuous_ofAdd))
  change ContDiff ℝ p (fun xt ↦ l (elementaryCover xt z b))
  let cover : (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin t)) →+
      ElementaryLieGroup d t r F :=
    { toFun := fun xt ↦ elementaryCover xt 0 0
      map_zero' := by simp [elementaryCover, Pi.zero_def]
      map_add' := by
        intro x y
        simp [elementaryCover, Pi.add_def, Pi.zero_def] }
  have hCover : Continuous cover :=
    continuous_fst.prodMk ((continuous_pi fun i ↦ ((AddCircle.continuous_mk' (1 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ i).comp continuous_snd))).prodMk
        (continuous_const.prodMk continuous_const))
  let l₀ := l.comp cover
  have hLinear : ContDiff ℝ p l₀ := (l₀.toRealLinearMap (hl.comp hCover)).contDiff
  have hAffine : (fun xt ↦ l₀ xt + l (elementaryCover 0 z b)) =
      fun xt ↦ l (elementaryCover xt z b) := by
    funext xt
    change l (elementaryCover xt 0 0) + l (elementaryCover 0 z b) = _
    rw [← map_add]
    simp [elementaryCover, ← Pi.zero_def]
  rw [← hAffine]
  exact hLinear.add contDiff_const

/-- Untwisting by a real power of the modulation preserves every finite order
of Bruhat differentiability. The same good subgroup fixes both functions. -/
private theorem isBruhatContDiff_of_modulationWeight
    {p : ℕ} {a : ℝ} {f : G → ℂ} (hf : IsBruhatContDiff p (modulationWeight m a f)) :
    IsBruhatContDiff p f := by
  have hPos (x : G) : (0 : ℝ) < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  let l : G →ₜ* Multiplicative ℝ :=
    { toFun := fun x ↦ Multiplicative.ofAdd (Real.log ((m x).val : ℝ))
      map_one' := by simp
      map_mul' := fun x y ↦ by
        simp only [map_mul, Units.val_mul, NNReal.coe_mul, ← ofAdd_add]
        rw [Real.log_mul (hPos x).ne' (hPos y).ne']
      continuous_toFun := continuous_ofAdd.comp
        ((NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)).log
          fun x ↦ (hPos x).ne') }
  obtain ⟨k, hk, hInvariant, hDescend⟩ := hf
  have hKer := le_ker_of_isOpen_lcaAnnihilator l hk.2.1
  have hWeight (x : G) :
      modulationWeight m a f x = (Real.exp (Multiplicative.toAdd (l x) * a) : ℂ) * f x := by
    rw [modulationWeight, LinearMap.mulLeft_apply, Pi.mul_apply, Real.rpow_def_of_pos (hPos x)]
    rfl
  have hUndo (x : G) :
      (Real.exp (Multiplicative.toAdd (l x) * -a) : ℂ) * modulationWeight m a f x = f x := by
    rw [hWeight, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
    simp [mul_neg]
  refine ⟨k, hk, ?_, ?_⟩
  · intro h x
    have hh : l h.val = 1 := hKer h.property
    rw [← hUndo (h.val * x), ← hUndo x, hInvariant, map_mul, hh, one_mul]
  · intro s hs
    obtain ⟨g, hg, hSmooth⟩ := hDescend s hs
    let l' : s.val.1 →* Multiplicative ℝ := l.toMonoidHom.comp s.val.1.subtype
    have hKer' : (OrderDual.ofDual s.val.2).comap s.val.1.subtype ≤ l'.ker :=
      fun x hx ↦ hKer (hs ▸ hx)
    let lq : s.quotient →ₜ* Multiplicative ℝ :=
      { toMonoidHom := QuotientGroup.lift _ l' hKer'
        continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.2
          (l.continuous.comp continuous_subtype_val) }
    refine ⟨fun q ↦ (Real.exp (Multiplicative.toAdd (lq q) * -a) : ℂ) * g q,
      fun x ↦ ?_, fun e z b ↦ ?_⟩
    · dsimp only
      rw [hg]
      exact hUndo x.val
    · -- The presentation uses the standard addition on `Fin`.
      let finiteGroup := @Fin.addCommGroup e.finiteOrder ⟨(Fin.pos b).ne'⟩
      have hLog := @contDiff_logHom_elementaryCover e.realDim e.torusDim e.latticeRank
        (Fin e.finiteOrder) s.quotient finiteGroup inferInstance inferInstance inferInstance
        e.equiv.symm lq z b (p : ℕ∞)
      exact (Complex.ofRealCLM.contDiff.comp ((hLog.mul (contDiff_const (c := -a))).exp)).mul
        (hSmooth e z b)

-- TODO(paper-gap): In the proof of Remark D.3.4.1 the product rule differentiates
-- the weight times the function. The weight's derivative has coefficient a * r.

/-- Paper: Remark D.3.4.1, p. 815. A function of prescribed exponential decay
is Bruhat smooth whenever the exponent interval is nonempty. -/
theorem modulatedExponentialDecay_mem_bruhatSmooth (hne : I.Nonempty)
    (f : ModulatedExponentialDecay m I) :
    f.val ∈ bruhatSmoothSubmodule := by
  obtain ⟨a, ha⟩ := hne
  have hw : modulationWeight m a f.val ∈ schwartzBruhatSubmodule G :=
    (Submodule.mem_iInf _).mp f.property ⟨a, ha⟩
  have hs := schwartzBruhat_isBruhatSmooth (⟨modulationWeight m a f.val, hw⟩ : SchwartzBruhat G)
  refine (Submodule.mem_iInf _).2 fun p ↦ ?_
  exact isBruhatContDiff_of_modulationWeight m (hs p)

include hm hms in
/-- Paper: Remark D.3.4.1, p. 815. Invariant differential operators preserve
the Schwartz–Bruhat space with decay exponents in the given interval. -/
theorem modulatedExponentialDecay_invariantDiff (hInt : OrdConnected I) (hne : I.Nonempty)
    (D : bruhatDiffAlgebra G) (f : ModulatedExponentialDecay m I) :
    (D.val ⟨f.val, modulatedExponentialDecay_mem_bruhatSmooth m I hne f⟩).val ∈
      modulatedExponentialDecaySubmodule m I := by sorry

/-- Paper: Theorem D.3.4.2, p. 816. A continuous quasi-character is Bruhat smooth,
so the operator in the symbol formula can act on it. -/
theorem quasiCharacter_mem_bruhatSmooth (c : QuasiCharacter G) :
    (fun x : G ↦ c x) ∈ bruhatSmoothSubmodule := by sorry

/-- Paper: (D.3.4.1), p. 816. The symbol at a quasi-character is the evaluation
at the identity of the differential operator applied to that quasi-character. -/
def bruhatDiffQuasiCharacterSymbol (D : bruhatDiffAlgebra G) (c : QuasiCharacter G) : ℂ :=
  (D.val ⟨fun x : G ↦ c x, quasiCharacter_mem_bruhatSmooth c⟩).val 1

/-- Paper: Theorem D.3.4.2, p. 816. The extended symbol agrees with the
ordinary symbol on unitary characters. -/
theorem bruhatDiffQuasiCharacterSymbol_unitary (D : bruhatDiffAlgebra G) (χ : PontryaginDual G) :
    let coeCircle : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    bruhatDiffQuasiCharacterSymbol D (coeCircle.comp χ) = bruhatDiffSymbol D χ := by sorry

variable [hSC : SecondCountableTopology G] [MeasurableSpace G] [hBorel : BorelSpace G]

-- TODO(paper-gap): The proof of D.3.4.2 starts with a finite basis of the
-- space of one-parameter subgroups. For ℝ_{>0} × 𝕋^ℕ that space is infinite-dimensional.

include hSC hBorel hms in
/-- Paper: Theorem D.3.4.2, p. 816. On a component of the open strip, the
Fourier–Mellin transform of a bounded family in the closed-interval decay space
is bounded by a constant divided by the norm of the symbol above a positive threshold.
The threshold may depend on the component. -/
theorem modulatedFourierMellin_uniform_riemannLebesgue (hInt : OrdConnected I)
    (hne : I.Nonempty) (hOpen : IsOpen I) (hBound : IsBounded I)
    (μ : Measure G) [μ.IsHaarMeasure] (D : bruhatDiffAlgebra G)
    (B : Set (ModulatedExponentialDecay m (closure I))) (hB : IsVonNBounded ℂ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ ω₀ : PontryaginDual m.toMonoidHom.ker,
      ∃ M : ℝ, 0 < M ∧
        ∀ f ∈ B, ∀ c ∈ componentVerticalStrip m.toMonoidHom hm.1 hm.2 ω₀ I,
          M ≤ ‖bruhatDiffQuasiCharacterSymbol D c‖ →
          ‖modulatedFourierMellin m I hm μ f.val c‖ ≤
            C / ‖bruhatDiffQuasiCharacterSymbol D c‖ := by sorry

end RiemannLebesgue

section PoissonSummation

local notation "K" => m.toMonoidHom.ker

open Classical in
/-- Paper: (D.3.5.2), p. 818. In the coordinates of the chosen section, the
replacement equals the original function off the designated fibres and the
arithmetic mean of the two one-sided limits on them. -/
def modulatedJumpMidpointProfile (τ : ℝ≥0ˣ →ₜ* G) (f : G → ℂ) (S : Finset ℝ≥0ˣ)
    (hleft : ∀ (t : S) (g : K),
      ∃ a, Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[<] t.val) (𝓝 a))
    (hright : ∀ (t : S) (g : K),
      ∃ a, Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[>] t.val) (𝓝 a))
    (t : ℝ≥0ˣ) (g : K) : ℂ :=
  if ht : t ∈ S then ((hleft ⟨t, ht⟩ g).choose + (hright ⟨t, ht⟩ g).choose) / 2
  else f (τ t * g.val)

/-- Paper: (D.3.5.2), p. 818. The replacement at a designated fibre is the
midpoint of its given left and right limits. -/
theorem modulatedJumpMidpointProfile_eq_average (τ : ℝ≥0ˣ →ₜ* G) (f : G → ℂ)
    (S : Finset ℝ≥0ˣ)
    (hleft : ∀ (t : S) (g : K),
      ∃ a, Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[<] t.val) (𝓝 a))
    (hright : ∀ (t : S) (g : K),
      ∃ a, Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[>] t.val) (𝓝 a))
    (t : S) (g : K) (a b : ℂ)
    (ha : Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[<] t.val) (𝓝 a))
    (hb : Tendsto (fun u ↦ f (τ u * g.val)) (𝓝[>] t.val) (𝓝 b)) :
    modulatedJumpMidpointProfile m τ f S hleft hright t.val g = (a + b) / 2 := by sorry

-- TODO(paper-gap): Proposition D.3.5.1, (D.3.5.3), reverses the Fourier sign.
-- For γ = e, χ₀ = 1, and a bump in log coordinates supported in (1/8, 3/8)
-- with value 1 at 1/4, the left side at x = exp(1/4) is 1 and the right side
-- samples the periodization at -1/4, where it is 0. The t₀ shift is also spurious.
-- The reference to B.4.1.2 omits that proposition's derivative hypotheses.
-- TODO(paper-gap): The second equality of (D.3.5.5) is missing the factor
-- given by the log-coordinate integral.

/-- Paper: (D.3.5.4), p. 819. A unitary value at the lattice generator has a
unique phase in the half-open interval of length two pi divided by its log-module. -/
theorem existsUnique_modulatedCharacterPhase (γ : G) (hγ : 1 < (m γ).val)
    (χ : PontryaginDual G) :
    let L := Real.log ((m γ).val : ℝ)
    ∃! t : ℝ, t ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t * L) = χ γ := by sorry

/-- Paper: Remark D.3.5.2, p. 818. The cyclic subgroup generated by an element
of module greater than one is discrete, hence closed in the Hausdorff group. -/
theorem modulated_zpowers_discrete (γ : G) (hγ : 1 < (m γ).val) :
    DiscreteTopology (Subgroup.zpowers γ) := by sorry

variable (hm : IsModulation m) (hms : Surjective m)

include hm hms in
/-- Paper: Remark D.3.5.2, p. 818. After choosing a unitary lift for each
norm-one character, a phase correction and an integer frequency parametrize
exactly the unitary characters that are trivial on the cyclic subgroup. -/
theorem modulatedCharacter_zpowers_annihilator (γ : G) (hγ : 1 < (m γ).val)
    (χ : PontryaginDual K → PontryaginDual G)
    (hχ : ∀ (ω₀ : PontryaginDual K) (g : K), χ ω₀ g.val = ω₀ g)
    (t : PontryaginDual K → ℝ)
    (ht : let L := Real.log ((m γ).val : ℝ)
      ∀ ω₀, t ω₀ ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t ω₀ * L) = χ ω₀ γ) :
    let L := Real.log ((m γ).val : ℝ)
    ∃ e : (PontryaginDual K × ℤ) ≃ lcaAnnihilator (Subgroup.zpowers γ),
      ∀ ω₀ n x, (e (ω₀, n)).val x =
        χ ω₀ x * Circle.exp
          ((2 * Real.pi * (n : ℝ) / L - t ω₀) * Real.log ((m x).val : ℝ)) := by sorry

end PoissonSummation

section CompactSupport

/-- Paper: Lemma D.3.6.1, p. 819. The test function submodule consists of
Bruhat smooth functions with compact support. -/
def bruhatCompactSupportSubmodule (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] : Submodule ℂ (G → ℂ) where
  carrier := {f | f ∈ bruhatSmoothSubmodule ∧ HasCompactSupport f}
  zero_mem' := ⟨Submodule.zero_mem _, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨Submodule.add_mem _ hf.1 hg.1, hf.2.add hg.2⟩
  smul_mem' z _ hf := ⟨Submodule.smul_mem _ z hf.1, hf.2.smul_left⟩

/-- Paper: Lemma D.3.6.1, p. 819. For the additive real group the test
function submodule consists of ordinary smooth compactly supported functions.
Deviation: Sanity check in the real-line model. -/
theorem mem_bruhatCompactSupportSubmodule_real_iff (f : Multiplicative ℝ → ℂ) :
    f ∈ bruhatCompactSupportSubmodule (Multiplicative ℝ) ↔
      ContDiff ℝ ∞ (f ∘ Multiplicative.ofAdd) ∧ HasCompactSupport (f ∘ Multiplicative.ofAdd) :=
  by sorry

/-- Paper: Lemma D.3.6.1, p. 819. A fixed-support stage consists of
Schwartz functions on an elementary quotient whose realizations vanish
off the designated compact set. It carries the induced Schwartz topology. -/
def bruhatCompactSupportStage (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G) :
    Submodule ℂ (SchwartzBruhatStage e) :=
  ⨅ x : {x : G // x ∉ (C : Set G)}, LinearMap.ker
    ((LinearMap.proj x.val).comp (schwartzBruhatStageRealization a e))

include hT2 in
/-- Paper: Lemma D.3.6.1, p. 819. An element of an elementary Schwartz
stage belongs to the fixed-support submodule exactly when the topological
support of its realization is contained in the designated compact set. -/
theorem mem_bruhatCompactSupportStage_iff (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G) (f : SchwartzBruhatStage e) :
    f ∈ bruhatCompactSupportStage a e C ↔
      tsupport (schwartzBruhatStageRealization a e f) ⊆ (C : Set G) := by sorry

/-- Paper: Lemma D.3.6.1, p. 819. A function from a fixed-support
elementary stage realizes to a smooth compactly supported function on the group. -/
theorem bruhatCompactSupportStage_realization_mem (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G)
    (f : bruhatCompactSupportStage a e C) :
    schwartzBruhatStageRealization a e f.val ∈ bruhatCompactSupportSubmodule G := by sorry

/-- Paper: Lemma D.3.6.1, p. 819. The stage inclusion is the Schwartz
realization by pullback and extension by zero, with values in the test space. -/
def bruhatCompactSupportStageInclusion (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G) :
    bruhatCompactSupportStage a e C →ₗ[ℂ] bruhatCompactSupportSubmodule G :=
  ((schwartzBruhatStageRealization a e).domRestrict (bruhatCompactSupportStage a e C)).codRestrict
    (bruhatCompactSupportSubmodule G) (bruhatCompactSupportStage_realization_mem a e C)

/-- Paper: Lemma D.3.6.1, p. 819. A test function from a fixed-support stage
has the values of its Schwartz realization on the group. -/
theorem bruhatCompactSupportStageInclusion_apply (a : BruhatStructuralPair G)
    (e : ElementaryLCAPresentation a.quotient) (C : Compacts G)
    (f : bruhatCompactSupportStage a e C) (x : G) :
    (bruhatCompactSupportStageInclusion a e C f).val x =
      schwartzBruhatStageRealization a e f.val x := by sorry

/-- Paper: Lemma D.3.6.1, p. 819. The topology of the test function space
is final locally convex for the fixed-support stage inclusions.
Deviation: We use all compact supports and elementary quotient stages
in place of choosing a cofinal countable presentation. -/
abbrev BruhatCompactSupport (G : Type*) [CommGroup G] [TopologicalSpace G]
    [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] :=
  WithGeneratingSeminorms (bruhatCompactSupportSubmodule G)
    (Subtype.val : {p : Seminorm ℂ (bruhatCompactSupportSubmodule G) //
      ∀ (a : BruhatStructuralPair G) (e : ElementaryLCAPresentation a.quotient) (C : Compacts G),
        Continuous (p ∘ bruhatCompactSupportStageInclusion a e C)} → _)

/-- Paper: Lemma D.3.6.1, p. 819. The test space topology recovers the
usual Mathlib topology of smooth compactly supported functions on the real line.
Deviation: Sanity check in the real-line model. -/
theorem bruhatCompactSupport_real_equiv :
    ∃ e : BruhatCompactSupport (Multiplicative ℝ) ≃L[ℂ] 𝓓((⊤ : Opens ℝ), ℂ),
      ∀ f x, e f x = f.val (Multiplicative.ofAdd x) := by sorry

/-- Paper: Lemma D.3.6.1, p. 819. For a second-countable group the test
function topology admits a countable strict presentation by Fréchet stages. -/
theorem bruhatCompactSupport_strictLF [SecondCountableTopology G] :
    IsStrictLFSpace (BruhatCompactSupport G) := by sorry

variable (I : Set ℝ) (hm : IsModulation m) (hms : Surjective m)

include hm hms in
/-- Paper: Lemma D.3.6.1, p. 819. The compactly supported smooth test
functions form a subspace of the exponential-decay space. -/
theorem bruhatCompactSupport_le_modulatedExponentialDecay :
    bruhatCompactSupportSubmodule G ≤ modulatedExponentialDecaySubmodule m I := by sorry

/-- Paper: Lemma D.3.6.1, p. 819. The canonical inclusion into the
exponential-decay space is the identity on the underlying functions. -/
def bruhatCompactSupportToModulatedExponentialDecay :
    BruhatCompactSupport G →ₗ[ℂ] ModulatedExponentialDecay m I :=
  Submodule.inclusion (bruhatCompactSupport_le_modulatedExponentialDecay m I hm hms)

/-- Paper: Lemma D.3.6.1, p. 819. Applying the inclusion preserves every
pointwise value of the test function. -/
theorem bruhatCompactSupportToModulatedExponentialDecay_apply (f : BruhatCompactSupport G) (x : G) :
    (bruhatCompactSupportToModulatedExponentialDecay m I hm hms f).val x = f.val x := by sorry

variable [hSC : SecondCountableTopology G] (hInt : OrdConnected I) (hne : I.Nonempty)

include hSC hInt hne in
/-- Paper: Lemma D.3.6.1, p. 819. The inclusion of smooth compactly
supported functions is continuous from the test function topology. -/
theorem bruhatCompactSupport_continuous_modulatedExponentialDecay :
    Continuous (bruhatCompactSupportToModulatedExponentialDecay m I hm hms) := by sorry

-- TODO(paper-gap): The proof of continuity invokes the global projective topology
-- for arbitrary I. Theorem D.3.3.7(4) identifies it with the stage limit for compact I.
-- TODO(paper-gap): The seminorms ν_{a,k} in the proof omit polynomial weights.
-- In (D.3.6.2) the r = k term still has ψ(x/m) as a factor. The estimates
-- (D.3.6.3)–(D.3.6.4) omit the resulting cutoff tail even at k = 0.

include hSC hInt hne in
/-- Paper: Lemma D.3.6.1, p. 819. Smooth compactly supported functions are
dense in the exponential-decay space with its locally convex topology. -/
theorem bruhatCompactSupport_dense_modulatedExponentialDecay :
    DenseRange (bruhatCompactSupportToModulatedExponentialDecay m I hm hms) := by sorry

end CompactSupport

end RiemannMasullo
