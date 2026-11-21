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
    · have hLog := contDiff_logHom_elementaryCover e.equiv.symm lq z b (p : ℕ∞)
      exact (Complex.ofRealCLM.contDiff.comp ((hLog.mul (contDiff_const (c := -a))).exp)).mul
        (hSmooth e z b)

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

/-- Paper: Remark D.3.4.1, p. 815. First-order differentiation preserves each
exponential decay condition by the product rule for the modulation weight.
Deviation: If the modulation along the subgroup is exp(rt), the derivative
of the weight at exponent a has coefficient a * r. -/
private theorem bruhatFirstOrder_mem_modulatedExponentialDecay
    (b : LCATopologicalLie G) (f : bruhatSmoothSubmodule (G := G))
    (hf : f.val ∈ modulatedExponentialDecaySubmodule m I) :
    (bruhatFirstOrder b f).val ∈ modulatedExponentialDecaySubmodule m I := by
  refine (Submodule.mem_iInf _).2 fun a ↦ Submodule.mem_comap.2 ?_
  let w (x : G) : ℝ := ((m x).val : ℝ) ^ (a : ℝ)
  have hPos (x : G) : 0 < ((m x).val : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt _)
  let logOrbit : ℝ →+ ℝ := AddMonoidHom.mk'
    (fun t ↦ Real.log ((m (b (Multiplicative.ofAdd t))).val : ℝ)) (by
      intro s t
      simp only [ofAdd_add, map_mul, Units.val_mul, NNReal.coe_mul]
      exact Real.log_mul (hPos _).ne' (hPos _).ne')
  have hLogContinuous : Continuous logOrbit :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (m.continuous.comp (b.continuous.comp continuous_ofAdd)))).log
      fun _ ↦ (hPos _).ne'
  have hLog (t : ℝ) : logOrbit t = t * logOrbit 1 := by
    simpa only [smul_eq_mul, mul_one] using map_real_smul logOrbit hLogContinuous t (1 : ℝ)
  let c := logOrbit 1 * (a : ℝ)
  have hOrbit (x : G) (t : ℝ) :
      w (x * b (Multiplicative.ofAdd t)) = w x * Real.exp (t * c) := by
    unfold w
    rw [map_mul, Units.val_mul, NNReal.coe_mul,
      Real.mul_rpow (hPos x).le (hPos _).le, Real.rpow_def_of_pos (hPos (b _))]
    change _ * Real.exp (logOrbit t * (a : ℝ)) = _
    rw [hLog, mul_assoc]
  have hw (x : G) : HasDerivAt (fun t : ℝ ↦ (w (x * b (Multiplicative.ofAdd t)) : ℂ))
      ((w x * c : ℝ) : ℂ) 0 := by
    have h := (((hasDerivAt_id (0 : ℝ)).mul_const c).exp.const_mul (w x)).ofReal_comp
    simpa only [id, zero_mul, Real.exp_zero, one_mul, hOrbit] using h
  let F := modulationWeight m a f.val
  have hF : F ∈ schwartzBruhatSubmodule G :=
    modulationWeight_mem_schwartzBruhat m I a ⟨f.val, hf⟩
  obtain ⟨A, hA⟩ := bruhatFirstOrder_schwartz b
  have hDF : bruhatDirectionalDeriv b F ∈ schwartzBruhatSubmodule G := by
    have hEq : (A ⟨F, hF⟩).val = bruhatDirectionalDeriv b F := funext (hA ⟨F, hF⟩)
    exact hEq ▸ (A ⟨F, hF⟩).property
  have hTwist : modulationWeight m a (bruhatFirstOrder b f).val =
      bruhatDirectionalDeriv b F - (c : ℂ) • F := by
    funext x
    have h := ((hw x).fun_mul (hasDerivAt_bruhatDirectionalDeriv b
      ((mem_bruhatSmoothSubmodule_iff f.val).1 f.property 1) x)).deriv
    change bruhatDirectionalDeriv b F x =
      ((w x * c : ℝ) : ℂ) * f.val (x * b (Multiplicative.ofAdd 0)) +
        (w (x * b (Multiplicative.ofAdd 0)) : ℂ) * bruhatDirectionalDeriv b f.val x at h
    simp only [ofAdd_zero, map_one, mul_one, Complex.ofReal_mul] at h
    change (w x : ℂ) * bruhatDirectionalDeriv b f.val x =
      bruhatDirectionalDeriv b F x - (c : ℂ) * ((w x : ℂ) * f.val x)
    rw [h]
    ring
  rw [hTwist]
  exact (schwartzBruhatSubmodule G).sub_mem hDF ((schwartzBruhatSubmodule G).smul_mem _ hF)

include hm hms in
/-- Paper: Remark D.3.4.1, p. 815. Invariant differential operators preserve
the Schwartz–Bruhat space with decay exponents in the given interval. -/
theorem modulatedExponentialDecay_invariantDiff (hInt : OrdConnected I) (hne : I.Nonempty)
    (D : bruhatDiffAlgebra G) (f : ModulatedExponentialDecay m I) :
    (D.val ⟨f.val, modulatedExponentialDecay_mem_bruhatSmooth m I hne f⟩).val ∈
      modulatedExponentialDecaySubmodule m I := by
  refine Algebra.adjoin_induction
    (p := fun (A : Module.End ℂ (bruhatSmoothSubmodule (G := G))) _ ↦
      ∀ (g : bruhatSmoothSubmodule (G := G)),
        g.val ∈ modulatedExponentialDecaySubmodule m I →
          (A g).val ∈ modulatedExponentialDecaySubmodule m I)
    ?_ ?_ ?_ ?_ D.property _ f.property
  · rintro _ ⟨b, rfl⟩ g hg
    exact bruhatFirstOrder_mem_modulatedExponentialDecay m I b g hg
  · intro z g hg
    rw [Module.algebraMap_end_apply, Submodule.coe_smul]
    exact (modulatedExponentialDecaySubmodule m I).smul_mem z hg
  · intro A B _ _ hA hB g hg
    rw [LinearMap.add_apply, Submodule.coe_add]
    exact (modulatedExponentialDecaySubmodule m I).add_mem (hA g hg) (hB g hg)
  · intro A B _ _ hA hB g hg
    exact hA (B g) (hB g hg)

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
    bruhatDiffQuasiCharacterSymbol D (coeCircle.comp χ) = bruhatDiffSymbol D χ := rfl

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
    modulatedJumpMidpointProfile m τ f S hleft hright t.val g = (a + b) / 2 := by
  unfold modulatedJumpMidpointProfile
  rw [dif_pos t.property]
  let e : ℝ≥0ˣ ≃ₜ Set.Ioi (0 : ℝ) := Nonneg.unitsHomeomorphPos ℝ
  have : OrderTopology ℝ≥0ˣ := ⟨e.isInducing.eq_induced.trans
    ((show StrictMono e from fun _ _ h ↦ h).induced_topology_eq_preorder
      (e.surjective.range_eq ▸ Set.ordConnected_univ))⟩
  have h1 := tendsto_nhds_unique (hleft t g).choose_spec ha
  have h2 := tendsto_nhds_unique (hright t g).choose_spec hb
  rw [h1, h2]

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
    ∃! t : ℝ, t ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t * L) = χ γ := by
  intro L
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, Circle.exp θ = χ γ := ⟨_, Circle.exp_arg _⟩
  have h (t : ℝ) : (t ∈ Ico 0 (2 * Real.pi / L) ∧ Circle.exp (t * L) = χ γ) ↔
      t = toIcoMod Real.two_pi_pos 0 θ / L := by
    rw [eq_div_iff hL.ne', eq_comm (b := toIcoMod _ _ _), toIcoMod_eq_iff, zero_add, ← hθ,
      eq_comm (a := Circle.exp (t * L)), Circle.exp_eq_exp, mem_Ico, mem_Ico, lt_div_iff₀ hL,
      mul_nonneg_iff_of_pos_right hL]
    simp only [zsmul_eq_mul]
  exact ⟨_, (h _).2 rfl, fun t ht ↦ (h t).1 ht⟩

/-- Paper: Remark D.3.5.2, p. 818. The cyclic subgroup generated by an element
of module greater than one is discrete, hence closed in the Hausdorff group. -/
theorem modulated_zpowers_discrete (γ : G) (hγ : 1 < (m γ).val) :
    DiscreteTopology (Subgroup.zpowers γ) := by
  have hL : 0 < Real.log ((m γ).val : ℝ) := Real.log_pos (by exact_mod_cast hγ)
  have hlog (k : ℤ) : Real.log ((m (γ ^ k)).val : ℝ) = k * Real.log ((m γ).val : ℝ) := by
    rw [map_zpow, Units.val_zpow_eq_zpow_val, NNReal.coe_zpow, Real.log_zpow]
  have hcont : Continuous fun x : Subgroup.zpowers γ ↦ Real.log ((m x.val).val : ℝ) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (m.continuous.comp continuous_subtype_val))).log
      fun x ↦ (NNReal.coe_pos.mpr (Units.zero_lt _)).ne'
  refine discreteTopology_iff_isOpen_singleton_one.2 ?_
  convert (isOpen_Ioo (a := -Real.log ((m γ).val : ℝ))
    (b := Real.log ((m γ).val : ℝ))).preimage hcont
  ext ⟨x, hx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  simp only [mem_singleton_iff, mem_preimage, mem_Ioo, hlog]
  constructor
  · intro h
    have hγk : γ ^ k = 1 := congrArg Subtype.val h
    have hk : (k : ℝ) * Real.log ((m γ).val : ℝ) = 0 := by
      rw [← hlog, hγk]
      simp
    constructor <;> linarith
  · rintro ⟨h₁, h₂⟩
    have h₁' : (-1 : ℝ) < k := by nlinarith
    have h₂' : (k : ℝ) < 1 := by nlinarith
    have hk : -1 < k ∧ k < 1 := by exact_mod_cast And.intro h₁' h₂'
    have hk0 : k = 0 := by omega
    exact Subtype.ext (by simp [hk0])

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
      ContDiff ℝ ∞ (f ∘ Multiplicative.ofAdd) ∧ HasCompactSupport (f ∘ Multiplicative.ofAdd) := by
  have hsm : f ∈ bruhatSmoothSubmodule ↔ ContDiff ℝ ∞ (f ∘ Multiplicative.ofAdd) := by
    rw [mem_bruhatSmoothSubmodule_iff, contDiff_infty]
    exact forall_congr' fun p ↦ isBruhatContDiff_real_iff p f
  have hcs : HasCompactSupport f ↔ HasCompactSupport (f ∘ Multiplicative.ofAdd) :=
    ⟨fun h ↦ h.comp_homeomorph (Homeomorph.ofAdd (X := ℝ)), fun h ↦ by
      simpa [Function.comp_def] using h.comp_homeomorph (Homeomorph.ofAdd (X := ℝ)).symm⟩
  exact and_congr hsm hcs

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
      tsupport (schwartzBruhatStageRealization a e f) ⊆ (C : Set G) := by
  simp only [bruhatCompactSupportStage, Submodule.mem_iInf, LinearMap.mem_ker,
    LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval, Subtype.forall]
  constructor
  · intro h
    refine closure_minimal (fun x hx ↦ ?_) C.isCompact.isClosed
    by_contra hxC
    exact hx (h x hxC)
  · intro h x hx
    by_contra hne
    exact hx (h (subset_tsupport _ hne))

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
      schwartzBruhatStageRealization a e f.val x := rfl

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

-- Avoid the unused-section-variable linter traversing the large seminorm-family types.
set_option linter.unusedSectionVars false in
/-- Paper: Lemma D.3.6.1, p. 819. Applying the inclusion preserves every
pointwise value of the test function. -/
theorem bruhatCompactSupportToModulatedExponentialDecay_apply (f : BruhatCompactSupport G) (x : G) :
    (bruhatCompactSupportToModulatedExponentialDecay m I hm hms f).val x = f.val x := rfl

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
