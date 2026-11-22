module
import RiemannMasullo.ForMathlib.Analysis.Fourier.CompactGroup
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec4
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import RiemannMasullo.ForMathlib.MeasureTheory.Measure.Count
public import RiemannMasullo.ForMathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ParametricIntegral
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Bounded
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Completion
import RiemannMasullo.ForMathlib.Analysis.LocallyConvex.Montel

/-!
# Periodic Schauder bases in the absence of multiplicity

Masullo, §4.5, pp. 197–209. We use the left translation and Haar measure
conventions of §4.4.
-/

@[expose] public noncomputable section

open Bornology Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option quotPrecheck false

namespace RiemannMasullo

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [hSC : SecondCountableTopology G]
variable (m : G →ₜ* ℝ≥0ˣ) (γ : G)
variable (hm : IsModulation m) (hms : Surjective m) (hγ : 1 < (m γ).val)

local notation "K" => m.toMonoidHom.ker
local notation "Γ" => Subgroup.zpowers γ
local notation "Q" => G ⧸ Γ
local notation "S" => SchwartzBruhat Q
local notation "E" => ModulatedExponentialDecay m (Set.univ : Set ℝ)
local notation "L" => Real.log ((m γ).val : ℝ)

local notation "zeroUniv" => (⟨(0 : ℝ), Set.mem_univ _⟩ : (Set.univ : Set ℝ))
local notation "twist₀" => modulatedExponentialDecayTwist m Set.univ zeroUniv
local notation "ρG" => schwartzBruhatTranslationAction (G := G)
local notation "ρQ" =>
  (letI : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_closed m γ hγ
   schwartzBruhatTranslationAction (G := Q))
local notation "q" => QuotientGroup.mk' Γ

local instance instMeasurableSpaceCyclicQuotientSec5 : MeasurableSpace Q := borel _
local notation "H[" ω "]" =>
  (show Submodule ℂ E from (actionIsotype ((ρG).comp (K).subtype) ω).comap twist₀)

/-! ## 4.5.1 Periodization and its isotypic quotients -/

section Periodization

local notation "per" => modulatedPeriodization m γ hm hms hγ

include hm hms in
private theorem modulation_surjective_exists_section :
    ∃ τ : ℝ≥0ˣ →ₜ* G, RightInverse τ m := by
  refine hm.exists_section.elim fun s hs ↦ ?_
  exact ⟨s.comp ⟨(MonoidHom.id ℝ≥0ˣ).codRestrict _ fun t ↦ MonoidHom.mem_range.mpr (hms t),
    continuous_id.subtype_mk _⟩, fun t ↦ hs _⟩

private theorem cyclicCosetIntegral_hasSum [MeasurableSpace G] [BorelSpace G]
    [(Measure.count : Measure Γ).IsHaarMeasure] [(Measure.count : Measure Γ).Regular]
    (f : SchwartzBruhat G) (x : G) :
    HasSum (fun n : ℤ ↦ f (γ ^ n * x)) (schwartzBruhatCosetIntegral Γ Measure.count
      (modulatedCyclicSubgroup_closed m γ hγ) f (QuotientGroup.mk x)) := by
  let hΓ := modulatedCyclicSubgroup_closed m γ hγ
  let g : Γ → ℂ := fun z ↦ f (x * z.val)
  have hg := (lcaCosetIntegral_mem_schwartzBruhat Γ Measure.count hΓ f).1 x
  have hs : HasSum g (∫ z, g z ∂Measure.count) := by
    simpa [integral_countable hg, g] using (integrable_count_iff.mp hg).of_norm.hasSum
  let p : ℤ → Γ := fun n ↦ ⟨γ ^ n, Subgroup.zpow_mem_zpowers γ n⟩
  have hp : Injective p := by
    intro i j hij
    apply (zpow_right_injective₀ (Units.zero_lt (m γ)) hγ.ne')
    simpa only [p, map_zpow, Units.val_zpow_eq_zpow_val] using
      congrArg (fun z : Γ ↦ (m z.val).val) hij
  let e := Equiv.ofBijective p ⟨hp, fun ⟨z, n, hn⟩ ↦ ⟨n, Subtype.ext hn⟩⟩
  rw [schwartzBruhatCosetIntegral_mk]
  have ht : HasSum (fun n : ℤ ↦ f (x * γ ^ n)) (∫ z, g z ∂Measure.count) := e.hasSum_iff.mpr hs
  simpa only [g, mul_comm x] using ht

include hSC in
/-- Paper: Proposition 4.5.1.1(1), pp. 197–198. The orbit sum of §4.4 is linear
and continuous for the two Schwartz–Bruhat topologies. -/
theorem modulatedPeriodization_isLinearMap_continuous :
    IsLinearMap ℂ per ∧ Continuous per := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let := modulated_zpowers_discrete m γ hγ
  let : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure Γ).Regular := count_regular_of_discreteTopology
  refine (modulation_surjective_exists_section m hm hms).elim fun τ hτ ↦ ?_
  refine (modulatedExponentialDecay_continuous_inclusion m univ hm ordConnected_univ univ_nonempty
    τ hτ (mem_univ 0)).elim fun j hj ↦ ?_
  refine (schwartzBruhatCosetIntegral_continuousLinear Γ Measure.count
    (modulatedCyclicSubgroup_closed m γ hγ)).elim fun A hA ↦ ?_
  have h (f : E) : A (j f) = per f := by
    refine (hA (j f)).trans (Subtype.ext (funext fun z ↦ ?_))
    refine QuotientGroup.induction_on z (fun x ↦ ?_)
    exact ((cyclicCosetIntegral_hasSum m γ hγ (j f) x).congr_fun
      (fun n ↦ (hj.2 f (γ ^ n * x)).symm)).unique (modulatedPeriodization_hasSum m γ hm hms hγ f x)
  exact Eq.mp (congrArg (fun F : E → S ↦ IsLinearMap ℂ F ∧ Continuous F) (funext h))
    ⟨(A.comp j).toLinearMap.isLinear, (A.comp j).continuous⟩

/-- Paper: Equation (4.5.1.1), p. 197. Ordinary periodization is the bundled
continuous linear map given by the orbit sum of §4.4. -/
def modulatedPeriodizationCLM : E →L[ℂ] S :=
  let h := modulatedPeriodization_isLinearMap_continuous m γ hm hms hγ
  ⟨IsLinearMap.mk' per h.1, h.2⟩

local notation "P" => modulatedPeriodizationCLM m γ hm hms hγ

-- Equation (4.5.1.2) at each lift is modulatedPeriodization_hasSum in §4.4.

omit hSC in
private theorem schwartzBruhat_norm_bounded (f : SchwartzBruhat G) : ∃ d : ℝ, ∀ x, ‖f x‖ ≤ d := by
  obtain ⟨a, e, s, hs⟩ := (mem_schwartzBruhatSubmodule_iff _).mp f.property
  refine ⟨elementarySchwartzSeminorm (0, 0, 0, 0) s, fun x ↦ ?_⟩
  rw [← show schwartzBruhatStageRealization a e s x = f x from congrFun hs x,
    schwartzBruhatStageRealization_apply]
  split_ifs
  · change (‖s _‖₊ : ENNReal).toReal ≤ (elementarySchwartzBound s.val _).toReal
    apply ENNReal.toReal_mono (s.property.2 _).ne
    rw [elementarySchwartzBound_zero]
    exact le_iSup (fun y ↦ (‖s y‖₊ : ENNReal)) _
  · exact norm_zero.trans_le (apply_nonneg _ _)

omit hSC in
include hγ in
private theorem exists_orbit_majorant (f : E) (C : Set G) (hC : IsCompact C) :
    ∃ d : ℤ → ℝ, Summable d ∧ ∀ n x, x ∈ C → ‖f.val (γ ^ n * x)‖ ≤ d n := by
  let w (x : G) : ℝ := (m x).val
  have hw (x : G) : 0 < w x := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hwc : Continuous w := NNReal.continuous_coe.comp (Units.continuous_val.comp m.continuous)
  obtain ⟨a, ha⟩ := schwartzBruhat_norm_bounded (modulatedExponentialDecayTwist m univ ⟨1, mem_univ _⟩ f)
  obtain ⟨b, hb⟩ := schwartzBruhat_norm_bounded (modulatedExponentialDecayTwist m univ ⟨-1, mem_univ _⟩ f)
  have h₁ (y : G) : ‖f.val y‖ ≤ a * (w y)⁻¹ := by
    have h : ‖(((w y ^ (1 : ℝ)) : ℝ) : ℂ) * f.val y‖ ≤ a := ha y
    rw [Real.rpow_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw y).le] at h
    exact (le_div_iff₀ (hw y)).mpr ((mul_comm _ _).trans_le h) |>.trans_eq (div_eq_mul_inv _ _)
  have h₂ (y : G) : ‖f.val y‖ ≤ b * w y := by
    have h : ‖(((w y ^ (-1 : ℝ)) : ℝ) : ℂ) * f.val y‖ ≤ b := hb y
    rw [Real.rpow_neg_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg (inv_nonneg.mpr (hw y).le)] at h
    exact ((inv_mul_le_iff₀ (hw y)).mp h).trans_eq (mul_comm _ _)
  obtain ⟨A, hA⟩ := (hC.image (continuous_const (y := a) |>.mul (hwc.inv₀ fun x ↦ (hw x).ne'))).bddAbove
  obtain ⟨B, hB⟩ := (hC.image (continuous_const (y := b) |>.mul hwc)).bddAbove
  let d : ℤ → ℝ
    | .ofNat n => A * (w γ)⁻¹ ^ n
    | .negSucc n => B * (w γ)⁻¹ ^ (n + 1)
  have hg : Summable fun n : ℕ ↦ (w γ)⁻¹ ^ n :=
    summable_geometric_of_lt_one (inv_nonneg.mpr (hw γ).le) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hγ))
  have hmul (n : ℤ) (x : G) : w (γ ^ n * x) = w γ ^ n * w x := by
    simp only [w, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul, NNReal.coe_zpow]
  refine ⟨d, .of_nat_of_neg_add_one (hg.mul_left A) (((summable_nat_add_iff 1).mpr hg).mul_left B), ?_⟩
  intro n x hx
  cases n with
  | ofNat n =>
    calc
      _ ≤ a * (w (γ ^ (n : ℤ) * x))⁻¹ := h₁ _
      _ = (a * (w x)⁻¹) * (w γ)⁻¹ ^ n := by rw [hmul, mul_inv_rev, zpow_natCast, inv_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right (hA (mem_image_of_mem _ hx)) (pow_nonneg (inv_nonneg.mpr (hw γ).le) n)
  | negSucc n =>
    calc
      _ ≤ b * w (γ ^ (Int.negSucc n) * x) := h₂ _
      _ = (b * w x) * (w γ)⁻¹ ^ (n + 1) := by
        rw [hmul]
        change b * (w γ ^ (-(↑(n + 1) : ℤ)) * w x) = _
        rw [zpow_neg, zpow_natCast, inv_pow]
        ring
      _ ≤ B * (w γ)⁻¹ ^ (n + 1) := mul_le_mul_of_nonneg_right
        (show b * w x ≤ B from hB ⟨x, hx, rfl⟩) (pow_nonneg (inv_nonneg.mpr (hw γ).le) (n + 1))

/-- Paper: Proposition 4.5.1.1(1), pp. 197–199. The ordinary orbit sums converge
uniformly on compact sets of representatives in the original group.
Deviation: Finite partial sums need representatives because they are generally
functions on G only. -/
theorem modulatedPeriodization_tendstoUniformlyOn (f : E) (C : Set G) (hC : IsCompact C) :
    TendstoUniformlyOn (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, f.val (γ ^ n * x))
      (fun x ↦ P f (q x)) atTop C := by
  have hsum (x : G) : (∑' n : ℤ, f.val (γ ^ n * x)) = P f (q x) :=
    (modulatedPeriodization_hasSum m γ hm hms hγ f x).tsum_eq
  refine (exists_orbit_majorant m γ hγ f C hC).elim fun d h ↦ ?_
  have hd := h.1
  have hf := h.2
  have hu := tendstoUniformlyOn_tsum (f := fun (n : ℤ) x ↦ f.val (γ ^ n * x)) hd hf
  exact hu.congr_right (fun {_} _ ↦ hsum _)

private theorem bruhatOrbit_hasDerivAt (α : LCATopologicalLie G) (g : G → ℂ)
    (hg : IsBruhatContDiff 1 g) (z : G) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ g (z * α (Multiplicative.ofAdd s)))
      (bruhatDirectionalDeriv α g (z * α (Multiplicative.ofAdd t))) t := by
  have h := hasDerivAt_bruhatDirectionalDeriv α hg (z * α (Multiplicative.ofAdd t))
  have hshift := HasDerivAt.comp_sub_const t t (by simpa only [sub_self] using h)
  apply hshift.congr_of_eventuallyEq (.of_forall fun s ↦ ?_)
  change g (z * α (Multiplicative.ofAdd s)) = g (z * α (Multiplicative.ofAdd t) * α (Multiplicative.ofAdd (s - t)))
  rw [mul_assoc, ← map_mul]
  change g (z * α (Multiplicative.ofAdd s)) = g (z * α (Multiplicative.ofAdd (t + (s - t))))
  rw [add_sub_cancel]

include hm hms in
private theorem modulated_directionalDerivative_mem (α : LCATopologicalLie G) (f : E) :
    bruhatDirectionalDeriv α f.val ∈ modulatedExponentialDecaySubmodule m univ :=
  modulatedExponentialDecay_invariantDiff m univ hm hms ordConnected_univ univ_nonempty
    (bruhatDiffGenerator α) f

private theorem periodization_directionalDerivative (α : LCATopologicalLie G) (f : E) :
    let df : E := ⟨bruhatDirectionalDeriv α f.val, modulated_directionalDerivative_mem m hm hms α f⟩
    bruhatDirectionalDeriv α (fun x ↦ P f (q x)) = fun x ↦ P df (q x) := by
  intro df
  funext x
  let path (t : ℝ) := x * α (Multiplicative.ofAdd t)
  have hc : Continuous path := continuous_const.mul (α.continuous.comp continuous_id)
  have hzero : path 0 = x := by simp [path]
  let g (n : ℤ) (t : ℝ) := f.val (γ ^ n * path t)
  let dg (n : ℤ) (t : ℝ) := df.val (γ ^ n * path t)
  have hdiff (n : ℤ) (t : ℝ) : HasDerivAt (g n) (dg n t) t := by
    have hs := (mem_bruhatSmoothSubmodule_iff f.val).mp
      (modulatedExponentialDecay_mem_bruhatSmooth m univ univ_nonempty f) 1
    simpa only [g, dg, path, df, mul_assoc] using bruhatOrbit_hasDerivAt α f.val hs (γ ^ n * x) t
  refine (exists_orbit_majorant m γ hγ df _ ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).image hc)).elim fun d h ↦ ?_
  have hy : (0 : ℝ) ∈ Ioo (-1) 1 := ⟨by norm_num, by norm_num⟩
  have hsum (t : ℝ) := modulatedPeriodization_hasSum m γ hm hms hγ f (path t)
  have H := hasDerivAt_tsum_of_isPreconnected (g := g) (g' := dg) h.1 isOpen_Ioo isPreconnected_Ioo
    (fun n t _ ↦ hdiff n t) (fun n t ht ↦ h.2 n _ ⟨t, ⟨ht.1.le, ht.2.le⟩, rfl⟩)
    hy (hsum 0).summable hy
  have hd := (modulatedPeriodization_hasSum m γ hm hms hγ df (path 0)).tsum_eq
  have hp : (fun t : ℝ ↦ ∑' n, g n t) = fun t ↦ P f (q (path t)) := funext fun t ↦ (hsum t).tsum_eq
  exact (congrArg (fun v : ℝ → ℂ ↦ deriv v 0) hp).symm.trans
    (H.deriv.trans (hd.trans (congrArg (fun y ↦ P df (q y)) hzero)))

/-- Paper: Proposition 4.5.1.1(1), pp. 197–199. On compact sets of lifts,
each iterated directional derivative of the orbit sum is the locally uniform
sum of the corresponding derivatives of the translates. -/
theorem modulatedPeriodization_deriv_tendstoUniformlyOn (f : E)
    (α : LCATopologicalLie G) (r : ℕ) (C : Set G) (hC : IsCompact C) :
    let d := (bruhatDirectionalDeriv α)^[r]
    TendstoUniformlyOn (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, d f.val (γ ^ n * x))
      (d (fun x ↦ P f (q x))) atTop C := by
  intro d
  let D (g : E) : E :=
    ⟨bruhatDirectionalDeriv α g.val, modulated_directionalDerivative_mem m hm hms α g⟩
  let v (g : E) := g.val
  let p (g : E) := fun x ↦ P g (q x)
  have hv : Semiconj v D (bruhatDirectionalDeriv α) := fun _ ↦ rfl
  have hp : Semiconj p D (bruhatDirectionalDeriv α) := fun g ↦
    (periodization_directionalDerivative m γ hm hms hγ α g).symm
  let U (F H : G → ℂ) := TendstoUniformlyOn
    (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, F (γ ^ n * x)) H atTop C
  exact Eq.mp (congrArg₂ U (hv.iterate_right r f) (hp.iterate_right r f))
    (modulatedPeriodization_tendstoUniformlyOn m γ hm hms hγ (D^[r] f) C hC)

/-- Paper: Proposition 4.5.1.1(1), pp. 197–198. Every Schwartz–Bruhat function
on the compact cyclic quotient is a periodization. -/
theorem modulatedPeriodization_surjective : Surjective P := by sorry

-- TODO(paper-gap): Remarks 4.5.1.2 and 4.5.1.4 use arbitrary I for
-- periodization. For I = (1,2), a smooth log-profile equal to one near
-- minus infinity and zero near plus infinity has divergent orbit sums.

-- TODO(paper-gap): The continuity proof on pp. 199–200 assumes that a
-- convergent net in a locally convex space has a bounded tail.
-- The majorant on p. 199 also needs the supremum of the absolute values.
-- Remark 4.5.1.3 uses the tensor comparison of §D.3.3. For the valid
-- sequential assertion in Remarks 4.5.1.2 and 4.5.1.4 see the interval section.

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "perχ" => modulatedIsotypicPeriodization m γ hm hms hγ μ₁ χ

-- Proposition 4.5.1.1(2) is modulatedIsotypicPeriodization_mem in §4.4.

private theorem exists_schwartz_average {X Y : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] (μX : Measure X) [μX.IsHaarMeasure]
    [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [T2Space Y]
    [LocallyCompactSpace Y] [SecondCountableTopology Y] (π : X →ₜ* Y) (ω : PontryaginDual X) :
    ∃ A : (SchwartzBruhat Y) →L[ℂ] (SchwartzBruhat Y), ∀ (f : (SchwartzBruhat Y)) (z : Y), A f z = (μX.real univ : ℂ)⁻¹ *
      ∫ u : X, (ω u : ℂ) * f (π u * z) ∂μX := by
  let : LocallyConvexSpace ℝ (SchwartzBruhat Y) := (withGeneratingSeminorms_spec _ _).toLocallyConvexSpace
  let : T2Space (SchwartzBruhat Y) := schwartzBruhat_t2
  let : QuasiCompleteSpace ℂ (SchwartzBruhat Y) := schwartzBruhat_quasiComplete
  let ρ : X →* ((SchwartzBruhat Y) →L[ℂ] (SchwartzBruhat Y)) := (schwartzBruhatTranslationAction (G := Y)).comp π.toMonoidHom
  have hq : Continuous (π : X → Y) := π.continuous
  have hj : Continuous (fun p : X × (SchwartzBruhat Y) ↦ (π p.1, p.2)) := (hq.comp continuous_fst).prodMk continuous_snd
  have hTranslate := (schwartzBruhatTranslate_continuous (G := Y)).comp hj
  have hρ : Continuous (fun p : X × (SchwartzBruhat Y) ↦ ρ p.1 p.2) := hTranslate.congr fun p ↦
    ((Classical.choose_spec (existsUnique_schwartzBruhatTranslationAction (G := Y)).exists)
      (π p.1) p.2).symm
  have hseq {Z : Type _} [UniformSpace Z] (T : X → Z → Z)
      (hc : Continuous (fun p : X × Z ↦ T p.1 p.2)) (u : ℕ → Z) (v : Z) (hu : Tendsto u atTop (𝓝 v)) :
      TendstoUniformly (fun n k ↦ T k (u n)) (fun k ↦ T k v) atTop := by
    intro U hU
    obtain ⟨W, hW, h⟩ := (isCompact_univ (X := X)).mem_uniformity_of_prod
      (f := fun f : Z ↦ fun k : X ↦ T k f) (s := univ) («q» := v)
      (hc.comp continuous_swap).continuousOn (mem_univ _) (symm_le_uniformity hU)
    rw [nhdsWithin_univ] at hW
    exact (hu.eventually hW).mono fun n hn k ↦ h (u n) hn k (mem_univ k)
  refine (existsUnique_compactActionIsotypicAverage μX ρ hρ schwartzBruhat_bornological (hseq (Z := SchwartzBruhat Y) (fun k f ↦ ρ k f) hρ) ω).exists.elim
    fun A hA ↦ ?_
  refine ⟨(μX.real univ : ℂ)⁻¹ • A, fun f z ↦ congrArg ((μX.real univ : ℂ)⁻¹ * ·) ?_⟩
  refine (schwartzBruhat_dirac_support z).elim fun δ hδ ↦ ?_
  have h := congrArg (fun v : PettisWeakCompletion (SchwartzBruhat Y) ↦
    (show Module.Dual ℂ (StrongDual ℂ (SchwartzBruhat Y)) from v) δ) (hA f).2
  change δ (A f) = ∫ k, δ (star (ω k : ℂ) • ρ k f) ∂μX.restrict univ at h
  let g (k : X) := (ω k : ℂ) * f (π k * z)
  have he (k : X) : δ (star (ω k : ℂ) • ρ k f) = g k⁻¹ := by
    have hw : star (ω k : ℂ) = (ω k⁻¹ : ℂ) := by rw [map_inv, Circle.coe_inv_eq_conj]; rfl
    have harg : ((π k)⁻¹ * z) = π k⁻¹ * z := congrArg (· * z) (π.map_inv k).symm
    calc
      δ (star (ω k : ℂ) • ρ k f) = star (ω k : ℂ) * δ (ρ k f) := δ.map_smul _ _
      _ = star (ω k : ℂ) * f ((π k)⁻¹ * z) := congrArg (star (ω k : ℂ) * ·)
        ((hδ.1 _).trans (schwartzBruhatTranslationAction_apply (π k) z f))
      _ = g k⁻¹ := congrArg₂ (· * ·) hw (congrArg (fun y ↦ f y) harg)
  have hint := integral_congr_ae (μ := μX) (ae_of_all μX he)
  have hi := integral_inv_eq_self g μX
  have h' : δ (A f) = ∫ k, δ (star (ω k : ℂ) • ρ k f) ∂μX := by
    simpa only [Measure.restrict_univ] using h
  exact (hδ.1 (A f)).symm.trans (h'.trans (hint.trans hi))

private theorem hasSum_integral_weighted_orbit (ω : PontryaginDual K) (f : E) (x : G) :
    HasSum (fun n : ℤ ↦ ∫ u : K, (ω u : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁)
      (∫ u : K, (ω u : ℂ) * P f (q (u.val * x)) ∂μ₁) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let C := range (fun u : K ↦ u.val * x)
  have hC : IsCompact C := isCompact_range (continuous_subtype_val.mul continuous_const)
  have hc : Continuous f.val := (schwartzBruhat_continuous (twist₀ f)).congr fun y ↦
    congrFun (modulationWeight_zero m f.val) y
  let F (n : ℤ) (u : K) := (ω u : ℂ) * f.val (γ ^ n * (u.val * x))
  have hmeas (n : ℤ) : AEStronglyMeasurable (F n) μ₁ := ((continuous_subtype_val.comp (map_continuous ω)).mul
    (hc.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const)))).aestronglyMeasurable
  refine (exists_orbit_majorant m γ hγ f C hC).elim fun d hd ↦ ?_
  let result (u : K) := (ω u : ℂ) * P f (q (u.val * x))
  have hb (n : ℤ) : ∀ᵐ u ∂μ₁, ‖F n u‖ ≤ d n := .of_forall fun u ↦
    (norm_mul _ _).trans_le (by rw [Circle.norm_coe, one_mul]; exact hd.2 n _ ⟨u, rfl⟩)
  have hs (u : K) : HasSum (fun n ↦ F n u) (result u) :=
    (modulatedPeriodization_hasSum m γ hm hms hγ f (u.val * x)).mul_left (ω u : ℂ)
  exact hasSum_integral_of_dominated_convergence (F := F) (f := result) (μ := μ₁)
    (fun n _ ↦ d n) hmeas hb (.of_forall fun _ ↦ hd.1) (integrable_const _) (.of_forall hs)

private theorem exists_isotypic_periodization_factor :
    ∃ A : S →L[ℂ] S, (∀ f : E, perχ f = (μ₁.real univ : ℂ) • A (P f)) ∧
      ∀ f : E, A (perχ f) = perχ f := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let π : K →ₜ* Q := ⟨(q).comp (K).subtype, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩
  let ω := PontryaginDual.map (⟨(K).subtype, continuous_subtype_val⟩ : K →ₜ* G) χ
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  refine (exists_schwartz_average μ₁ π ω).elim fun A hA ↦ ⟨A, fun f ↦ ?_, fun f ↦ ?_⟩
  · refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
    have ht := modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ χ f x
    have hs := hasSum_integral_weighted_orbit m γ hm hms hγ μ₁ ω f x
    have hi := ht.unique hs
    have he (u : K) : (ω u : ℂ) * P f (q (u.val * x)) = (ω u : ℂ) * P f (π u * q x) :=
      congrArg (fun z ↦ (ω u : ℂ) * P f z) (map_mul (q) u.val x)
    change perχ f (q x) = M * (A (P f) (q x))
    exact hi.trans ((integral_congr_ae (ae_of_all μ₁ he)).trans
      ((mul_inv_cancel_left₀ hM _).symm.trans (congrArg (M * ·) (hA (P f) (q x)).symm)))
  · refine Subtype.ext (funext fun z ↦ ?_)
    have he (u : K) : (ω u : ℂ) * perχ f (π u * z) = perχ f z := by
      have ht := modulatedIsotypicPeriodization_homogeneous m γ hm hms hγ μ₁ χ f u (π u * z)
      have hi : QuotientGroup.mk u.val⁻¹ * (π u * z) = z :=
        (congrArg (· * (π u * z)) ((q).map_inv u.val)).trans (inv_mul_cancel_left (π u) z)
      exact ht.symm.trans (congrArg (fun y ↦ perχ f y) hi)
    have hi := integral_congr_ae (ae_of_all μ₁ he)
    have hc : (∫ _ : K, perχ f z ∂μ₁) = M * perχ f z := by
      rw [integral_const]
      exact Complex.real_smul
    exact (hA (perχ f) z).trans ((congrArg (M⁻¹ * ·) (hi.trans hc)).trans (inv_mul_cancel_left₀ hM _))

/-- Paper: Proposition 4.5.1.1(3), p. 198. The homogeneous orbit sum of §4.4
is linear and continuous. -/
theorem modulatedIsotypicPeriodization_isLinearMap_continuous :
    IsLinearMap ℂ perχ ∧ Continuous perχ := by
  refine (exists_isotypic_periodization_factor m γ hm hms hγ μ₁ χ).elim fun A hA ↦ ?_
  let B : E →L[ℂ] S := (μ₁.real univ : ℂ) • A.comp P
  have he : perχ = (B : E → S) := funext hA.1
  exact Eq.mpr (congrArg (fun F : E → S ↦ IsLinearMap ℂ F ∧ Continuous F) he)
    ⟨B.toLinearMap.isLinear, B.continuous⟩

/-- Paper: Proposition 4.5.1.1(3), p. 198. Homogeneous periodization is the
bundled continuous linear map given by the character-weighted orbit sum. -/
def modulatedIsotypicPeriodizationCLM : E →L[ℂ] S :=
  let h := modulatedIsotypicPeriodization_isLinearMap_continuous m γ hm hms hγ μ₁ χ
  ⟨IsLinearMap.mk' perχ h.1, h.2⟩

local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

-- The pointwise sum in (2–3) is modulatedIsotypicPeriodization_hasSum in §4.4.

end Periodization

section FourierQuotientDefinitions

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]

local notation "qK" => (q).comp (K).subtype
local notation "Sχ[" ω "]" => actionIsotype ((ρQ).comp qK) ω

-- TODO(paper-gap): In the proof on p. 201 the square of the unnormalized
-- quotient average is its Haar mass times the average itself.

include hm hγ in
/-- Paper: Notation 4.5.1.1, p. 204. The stated normalized compact average,
evaluated on the cyclic quotient, lands in the quotient Schwartz–Bruhat space. -/
theorem modulatedQuotientIsotypicProjector_mem (ω : PontryaginDual K) (f : S) :
    (fun z : Q ↦ (μ₁.real univ : ℂ)⁻¹ *
      ∫ u : K, (ω u : ℂ) * f (qK u * z) ∂μ₁) ∈ schwartzBruhatSubmodule Q ∧
      ∀ z : Q, Integrable (fun u : K ↦ (ω u : ℂ) * f (qK u * z)) μ₁ := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  refine (exists_schwartz_average μ₁
    (⟨qK, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩ : K →ₜ* Q) ω).elim fun A hA ↦ ?_
  refine ⟨Eq.mp (congrArg (· ∈ schwartzBruhatSubmodule Q) (funext (hA f))) (A f).property, fun z ↦ ?_⟩
  have hq : Continuous (qK : K → Q) := QuotientGroup.continuous_mk.comp continuous_subtype_val
  exact ((continuous_subtype_val.comp (map_continuous ω)).mul
    ((schwartzBruhat_continuous f).comp (hq.mul continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

local notation "avg[" ω "," f "]" => (⟨fun z : Q ↦ (μ₁.real univ : ℂ)⁻¹ *
  ∫ u : K, (ω u : ℂ) * f (qK u * z) ∂μ₁,
  (modulatedQuotientIsotypicProjector_mem m γ hm hγ μ₁ ω f).1⟩ : S)

include hm hγ hSC in
/-- Paper: Notation 4.5.1.1, p. 204. The normalized compact average is linear
and continuous in the quotient test-function topology. -/
theorem modulatedQuotientIsotypicProjector_isLinearMap_continuous (ω : PontryaginDual K) :
    let A : S → S := fun f ↦ avg[ω, f]
    IsLinearMap ℂ A ∧ Continuous A := by
  intro B
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  refine (exists_schwartz_average μ₁
    (⟨qK, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩ : K →ₜ* Q) ω).elim fun A hA ↦ ?_
  have h (f : S) : A f = B f := Subtype.ext (funext (hA f))
  exact Eq.mp (congrArg (fun F : S → S ↦ IsLinearMap ℂ F ∧ Continuous F) (funext h))
    ⟨A.toLinearMap.isLinear, A.continuous⟩

/-- Paper: Notation 4.5.1.1, p. 204. The quotient projector is the
character-weighted compact average divided by the mass of the norm-one group. -/
def modulatedQuotientIsotypicProjector (ω : PontryaginDual K) : S →L[ℂ] S :=
  let h := modulatedQuotientIsotypicProjector_isLinearMap_continuous m γ hm hγ μ₁ ω
  let T : S →ₗ[ℂ] S := IsLinearMap.mk' (fun f : S ↦ avg[ω, f]) h.1
  ⟨T, h.2⟩

variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)

variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "a" => modulatedCyclicFourierCoeff m γ hm hγ χ t₀ ht₀ μ₁ ν

local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker
local notation "volQ" => (L * μ₁.real univ : ℂ)

/-- Paper: Equation (4.5.1.12), p. 204. The quotient by the homogeneous
kernel maps to the test-function space by normalized homogeneous periodization.
Deviation: Normalizing recovers ordinary periodization on the isotypic representatives. -/
def modulatedIsotypicPeriodizationQuotient (ω : PontryaginDual K) : V[ω] →L[ℂ] S :=
  (μ₁.real univ : ℂ)⁻¹ • (Pχ[ω]).ker.liftQL (Pχ[ω]) le_rfl

local notation "T[" ω "]" => modulatedIsotypicPeriodizationQuotient m γ hm hms hγ μ₁ χ ω

/-- Paper: Equation (4.5.1.10), p. 204. The quotient functional multiplies the
Fourier coefficient of normalized periodization by the logarithmic period times
the kernel mass. For the compatible Weil measure this is the quotient volume. -/
def modulatedCyclicPairing (ω : PontryaginDual K) (n : ℤ) : StrongDual ℂ (V[ω]) :=
  volQ • (a (ω, n)).comp (T[ω])

end FourierQuotientDefinitions

section IsotypicPeriodizationProperties

local notation "P" => modulatedPeriodizationCLM m γ hm hms hγ

private theorem isOpenMap_to_quotient_of_strictLF {X Y Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z] [T2Space Z]
    (hX : IsStrictLFSpace X) (hY : IsStrictLFSpace Y)
    (C : Y →L[ℂ] Z) (hC : IsQuotientMap C) (F₀ : X →L[ℂ] Z) (hp : Surjective F₀) :
    IsOpenMap F₀ := by
  obtain ⟨hTX, U, hmono, hF, hc, _⟩ := hX
  let : T2Space X := hTX
  have hY' := (lfSpace_quotient_properties («E» := Y)).1 hY
  have hQ := (lfSpace_quotient_properties («E» := Y)).2 hY' C.ker C.isClosed_ker
  obtain ⟨e, _⟩ := exists_quotient_equiv_of_kernel C hC C.ker rfl
  let A := e.symm.toContinuousLinearMap.comp F₀
  have ho : IsOpenMap A := isOpenMap_of_surjective_toLF (X := fun k ↦ U k) hQ hF
    (fun k ↦ (U k).subtypeL)
    (fun k _ ⟨u, hu⟩ ↦ ⟨⟨u.val, hmono k.le_succ u.property⟩, hu⟩)
    (fun x ↦ (hc x).imp fun k hk ↦ ⟨⟨x, hk⟩, rfl⟩) A (e.symm.surjective.comp hp)
  have he : e ∘ A = F₀ := funext fun x ↦ e.apply_symm_apply _
  exact Eq.mp (congrArg IsOpenMap he) (e.isOpenMap.comp ho)

/-- Paper: Remark 4.5.1.2, p. 198. Ordinary periodization on the two-sided
exponentially decaying space is open. -/
theorem modulatedPeriodization_isOpenMap : IsOpenMap P := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let := modulated_zpowers_discrete m γ hγ
  let : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure Γ).Regular := count_regular_of_discreteTopology
  refine (modulation_surjective_exists_section m hm hms).elim fun τ hτ ↦ ?_
  let Y := ModulatedExponentialDecay m ({0} : Set ℝ)
  have hX := modulatedExponentialDecay_strictLF m univ hm ordConnected_univ univ_nonempty τ hτ
  have hY := modulatedExponentialDecay_strictLF m ({0} : Set ℝ) hm (ordConnected_singleton) (singleton_nonempty _) τ hτ
  refine (modulatedExponentialDecay_singleton_schwartz m hm hms 0).elim fun e₀ _ ↦ ?_
  refine (schwartzBruhatCosetIntegral_continuousLinear Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ)).elim
    fun A hA ↦ ?_
  have hq : IsQuotientMap A := Eq.mpr (congrArg IsQuotientMap (funext hA))
    (schwartzBruhatCosetIntegral_isQuotientMap Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ))
  exact isOpenMap_to_quotient_of_strictLF (X := E) (Y := Y) (Z := S) hX hY
    (A.comp e₀.toContinuousLinearMap) (hq.comp e₀.toHomeomorph.isQuotientMap)
    P (modulatedPeriodization_surjective m γ hm hms hγ)

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)
local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

/-- Paper: §4.5 introduction and Proposition 4.5.1.1(2), pp. 197–198.
The homogeneous orbit sums converge uniformly on compact sets of representatives.
Deviation: The finite sums are evaluated on G, where their summands are defined. -/
theorem modulatedIsotypicPeriodization_tendstoUniformlyOn
    (f : E) (C : Set G) (hC : IsCompact C) :
    TendstoUniformlyOn
      (fun s : Finset ℤ ↦ fun x : G ↦
        ∑ n ∈ s, ∫ u : K, (χ u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁)
      (fun x ↦ Pχ f (q x)) atTop C := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let C' := (fun p : K × G ↦ p.1.val * p.2) '' (univ ×ˢ C)
  have hC' : IsCompact C' := (isCompact_univ.prod hC).image
    ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)
  have hsum (x : G) : (∑' n : ℤ, ∫ u : K, (χ u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁) =
      Pχ f (q x) := (modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ χ f x).tsum_eq
  refine (exists_orbit_majorant m γ hγ f C' hC').elim fun d h ↦ ?_
  have hd := h.1
  have hf := h.2
  have hb (n : ℤ) (x : G) (hx : x ∈ C) :
      ‖∫ u : K, (χ u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁‖ ≤ d n * μ₁.real univ := by
    apply norm_integral_le_of_norm_le_const
    exact .of_forall fun u ↦ (norm_mul _ _).trans_le (by
      rw [Circle.norm_coe, one_mul]
      exact hf n _ ⟨(u, x), ⟨mem_univ _, hx⟩, rfl⟩)
  have hu := tendstoUniformlyOn_tsum (f := fun (n : ℤ) (x : G) ↦
    ∫ u : K, (χ u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁) (hd.mul_right (μ₁.real univ)) hb
  exact hu.congr_right fun {_} _ ↦ hsum _

private theorem isotypicPeriodization_directionalDerivative (α : LCATopologicalLie G) (f : E) :
    let df : E := ⟨bruhatDirectionalDeriv α f.val, modulated_directionalDerivative_mem m hm hms α f⟩
    bruhatDirectionalDeriv α (fun x ↦ Pχ f (q x)) = fun x ↦ Pχ df (q x) := by
  intro df
  funext x
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let path (t : ℝ) := x * α (Multiplicative.ofAdd t)
  have hc : Continuous path := continuous_const.mul (α.continuous.comp continuous_id)
  have hzero : path 0 = x := by simp [path]
  let D (u : K × ℝ) := u.1.val * path u.2
  let C := D '' (univ ×ˢ Icc (-1 : ℝ) 1)
  have hC : IsCompact C := (isCompact_univ.prod isCompact_Icc).image
    ((continuous_subtype_val.comp continuous_fst).mul (hc.comp continuous_snd))
  refine (exists_orbit_majorant m γ hγ df C hC).elim fun b hb ↦ ?_
  let F (v : E) (n : ℤ) (t : ℝ) (u : K) := (χ u.val : ℂ) * v.val (γ ^ n * (u.val * path t))
  let g (v : E) (n : ℤ) (t : ℝ) := ∫ u, F v n t u ∂μ₁
  have hcont (v : E) (n : ℤ) (t : ℝ) : Continuous (F v n t) := by
    have hv : Continuous v.val := (schwartzBruhat_continuous (twist₀ v)).congr
      fun z ↦ congrFun (modulationWeight_zero m v.val) z
    exact ((continuous_subtype_val.comp χ.continuous).comp continuous_subtype_val).mul
      (hv.comp (continuous_const.mul (continuous_subtype_val.mul continuous_const)))
  have hbound (n : ℤ) (u : K) (t : ℝ) (ht : t ∈ Ioo (-1) 1) : ‖F df n t u‖ ≤ b n :=
    (norm_mul _ _).trans_le (by rw [Circle.norm_coe, one_mul]
                                exact hb.2 n _ ⟨(u, t), ⟨mem_univ _, ht.1.le, ht.2.le⟩, rfl⟩)
  have hdiff (n : ℤ) (u : K) (t : ℝ) : HasDerivAt (fun s ↦ F f n s u) (F df n t u) t := by
    have hs := (mem_bruhatSmoothSubmodule_iff f.val).mp
      (modulatedExponentialDecay_mem_bruhatSmooth m univ univ_nonempty f) 1
    have ht := bruhatOrbit_hasDerivAt α f.val hs (γ ^ n * (u.val * x)) t
    simpa only [F, df, path, mul_assoc] using ht.const_mul (χ u.val : ℂ)
  have havg (n : ℤ) (t : ℝ) (ht : t ∈ Ioo (-1) 1) : HasDerivAt (g f n) (g df n t) t :=
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ₁) (F := F f n) (F' := F df n)
      (bound := fun _ ↦ b n) (isOpen_Ioo.mem_nhds ht)
      (.of_forall fun s ↦ (hcont f n s).aestronglyMeasurable)
      ((hcont f n t).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      (hcont df n t).aestronglyMeasurable (.of_forall (hbound n)) (integrable_const _)
      (.of_forall fun u s _ ↦ hdiff n u s)).2
  have hdom (n : ℤ) (t : ℝ) (ht : t ∈ Ioo (-1) 1) :
      ‖g df n t‖ ≤ b n * μ₁.real univ :=
    norm_integral_le_of_norm_le_const (.of_forall fun u ↦ hbound n u t ht)
  have hy : (0 : ℝ) ∈ Ioo (-1) 1 := ⟨by norm_num, by norm_num⟩
  have hs (v : E) (t : ℝ) := modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ χ v (path t)
  have H := hasDerivAt_tsum_of_isPreconnected (g := g f) (g' := g df) (hb.1.mul_right (μ₁.real univ))
    isOpen_Ioo isPreconnected_Ioo havg hdom hy (hs f 0).summable hy
  have hp : (fun t ↦ ∑' n, g f n t) = fun t ↦ Pχ f (q (path t)) := funext fun t ↦ (hs f t).tsum_eq
  exact (congrArg (fun v : ℝ → ℂ ↦ deriv v 0) hp).symm.trans
    (H.deriv.trans ((hs df 0).tsum_eq.trans (congrArg (fun y ↦ Pχ df (q y)) hzero)))

/-- Paper: §4.5 introduction and Proposition 4.5.1.1(2), pp. 197–199.
On compact sets of lifts each directional derivative of homogeneous periodization
is the locally uniform sum of the averaged derivatives. -/
theorem modulatedIsotypicPeriodization_deriv_tendstoUniformlyOn (f : E)
    (α : LCATopologicalLie G) (r : ℕ) (C : Set G) (hC : IsCompact C) :
    let d := (bruhatDirectionalDeriv α)^[r]
    TendstoUniformlyOn (fun s : Finset ℤ ↦ fun x : G ↦
      ∑ n ∈ s, ∫ u : K, (χ u.val : ℂ) * d f.val (γ ^ n * (u.val * x)) ∂μ₁)
      (d (fun x ↦ Pχ f (q x))) atTop C := by
  intro d
  let D (g : E) : E :=
    ⟨bruhatDirectionalDeriv α g.val, modulated_directionalDerivative_mem m hm hms α g⟩
  let v (g : E) := g.val
  let p (g : E) := fun x ↦ Pχ g (q x)
  have hv : Semiconj v D (bruhatDirectionalDeriv α) := fun _ ↦ rfl
  have hp : Semiconj p D (bruhatDirectionalDeriv α) := fun g ↦
    (isotypicPeriodization_directionalDerivative m γ hm hms hγ μ₁ χ α g).symm
  let U (F H : G → ℂ) := TendstoUniformlyOn
    (fun s : Finset ℤ ↦ fun x ↦ ∑ n ∈ s, ∫ u : K, (χ u.val : ℂ) * F (γ ^ n * (u.val * x)) ∂μ₁) H atTop C
  exact Eq.mp (congrArg₂ U (hv.iterate_right r f) (hp.iterate_right r f))
    (modulatedIsotypicPeriodization_tendstoUniformlyOn m γ hm hms hγ μ₁ χ (D^[r] f) C hC)

/-- Paper: Proposition 4.5.1.1(3), p. 198. Homogeneous periodization is open
as a map to its image with the subspace topology. -/
theorem modulatedIsotypicPeriodization_isOpenMap_range :
    IsOpenMap ((Pχ).rangeRestrict) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  refine (exists_isotypic_periodization_factor m γ hm hms hγ μ₁ χ).elim fun A hA ↦ ?_
  exact isOpenMap_rangeRestrict_of_factor (X := E) (Y := S) Pχ P A
    (modulatedPeriodization_surjective m γ hm hms hγ) (modulatedPeriodization_isOpenMap m γ hm hms hγ)
    M hM hA.1 hA.2

/-- Paper: Proposition 4.5.1.1(3), p. 198. Homogeneous periodization has closed range. -/
theorem modulatedIsotypicPeriodization_isClosed_range : IsClosed (range Pχ) := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  refine (exists_isotypic_periodization_factor m γ hm hms hγ μ₁ χ).elim fun A hA ↦ ?_
  exact isClosed_range_of_factor (X := E) (Y := S) Pχ P A
    (modulatedPeriodization_surjective m γ hm hms hγ) M hM hA.1 hA.2

end IsotypicPeriodizationProperties

section Difference

variable (I : Set ℝ) (hInt : OrdConnected I) (hne : I.Nonempty)

local notation "D" => ModulatedExponentialDecay m I
local notation "diff" => (fun f : D ↦
  let g : modulatedExponentialDecaySubmodule m I := ⟨fun x ↦ f.val ((γ⁻¹)⁻¹ * x),
    modulatedExponentialDecaySubmodule_translate m I hm hms γ⁻¹ f⟩
  Sub.sub (α := D) f g)

include hSC hInt hne in
/-- Paper: Equations (4.5.1.3) and (4.5.3.3), pp. 198, 208. Subtracting the
translate by the inverse generator is linear and continuous on the decay space. -/
theorem modulatedCyclicDifference_isLinearMap_continuous :
    IsLinearMap ℂ diff ∧ Continuous diff := by
  have h := exists_modulatedExponentialDecay_translationAction (G := G) m I hm hms hInt hne
  obtain ⟨ρ, hρ, -⟩ := h
  let T : D →L[ℂ] D := ContinuousLinearMap.id ℂ D - ρ γ⁻¹
  have hpt : ∀ f : D, diff f = T f := fun f ↦
    congrArg (fun g : D ↦ f - g)
      (@Subtype.ext _ _ (⟨fun x ↦ f.val ((γ⁻¹)⁻¹ * x),
        modulatedExponentialDecaySubmodule_translate m I hm hms γ⁻¹ f⟩ :
          modulatedExponentialDecaySubmodule m I) (ρ γ⁻¹ f)
        (funext fun x ↦ (hρ γ⁻¹ f x).symm))
  have hadd : ∀ x y : D, diff (x + y) = diff x + diff y := fun x y ↦
    (hpt _).trans ((map_add T x y).trans (congrArg₂ (· + ·) (hpt x).symm (hpt y).symm))
  have hsmul : ∀ (c : ℂ) (x : D), diff (c • x) = c • diff x := fun c x ↦
    (hpt _).trans ((map_smul T c x).trans (congrArg (c • ·) (hpt x).symm))
  exact ⟨⟨hadd, hsmul⟩, T.continuous.congr fun f ↦ (hpt f).symm⟩

/-- Paper: Equations (4.5.1.3) and (4.5.3.3), pp. 198, 208. The cyclic
difference sends a function to itself minus its translate by the inverse generator. -/
def modulatedCyclicDifference : D →L[ℂ] D :=
  let h := modulatedCyclicDifference_isLinearMap_continuous m γ hm hms I hInt hne
  let T : D →ₗ[ℂ] D := IsLinearMap.mk' diff h.1
  ⟨T, h.2⟩
set_option linter.unusedSectionVars false in -- Avoid expensive unused-section-variable linting.
/-- Paper: Equations (4.5.1.3) and (4.5.3.3), pp. 198, 208. The difference
at x subtracts the function's value at γx. -/
theorem modulatedCyclicDifference_apply (f : D) (x : G) :
    (modulatedCyclicDifference m γ hm hms I hInt hne f).val x =
      f.val x - f.val (γ * x) := congrArg (fun y : G ↦ f.val x - f.val (y * x)) (inv_inv γ)

end Difference

local notation "Δ" => modulatedCyclicDifference m γ hm hms Set.univ
  (ordConnected_univ) (Set.univ_nonempty)
local notation "P" => modulatedPeriodizationCLM m γ hm hms hγ

section Averages

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]

include hm hms in
private theorem exists_continuous_decay_average (ω : PontryaginDual K) :
    ∃ A : E → E, Continuous A ∧ ∀ f, twist₀ (A f) = schwartzBruhatIsotypicProjector m hm μ₁ ω (twist₀ f) := by
  refine (exists_modulatedExponentialDecay_translationAction m univ hm hms ordConnected_univ univ_nonempty).elim
    fun ρ hρ ↦ ?_
  let Hρ := actionIsotype (ρ.comp (K).subtype) ω
  refine (existsUnique_modulatedExponentialDecay_isotypicProjector m univ hm hms ordConnected_univ
    univ_nonempty μ₁ ρ hρ.1 ω).exists.elim fun A hA ↦ ?_
  have hc := modulatedExponentialDecay_isotypicProjector_continuous m univ hm hms ordConnected_univ
    univ_nonempty μ₁ ρ hρ.1 ω A hA
  exact ⟨fun f ↦ (A f).val, continuous_subtype_val.comp hc, fun f ↦ hA f zeroUniv⟩

include hm in
private theorem homogeneous_average_properties (ω : PontryaginDual K) (f g : E)
    (hg : twist₀ g = schwartzBruhatIsotypicProjector m hm μ₁ ω (twist₀ f)) :
    g ∈ H[ω] ∧ (f ∈ H[ω] → g = f) ∧ ∀ x : G, g.val x = (μ₁.real univ : ℂ)⁻¹ *
      ∫ u : K, (ω u : ℂ) * f.val (u.val * x) ∂μ₁ := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let A := schwartzBruhatIsotypicProjector m hm μ₁ ω
  refine ⟨?_, fun hf ↦ ?_, fun x ↦ ?_⟩
  · refine (schwartzBruhatIsotypicProjector_quotient_equiv m hm μ₁ ω).elim fun iso hiso ↦ ?_
    let y := iso (A.ker.mkQ (twist₀ f))
    have he : y.val = twist₀ g := (hiso (twist₀ f)).trans hg.symm
    exact Eq.mp (congrArg (· ∈ actionIsotype ((ρG).comp (K).subtype) ω) he) y.property
  · have he := hg.trans (schwartzBruhatIsotypicProjector_apply_isotype m hm μ₁ ω (twist₀ f) hf)
    exact Subtype.ext (funext fun x ↦ (congrFun (modulationWeight_zero m g.val) x).symm.trans
      ((congrArg (fun v : SchwartzBruhat G ↦ v x) he).trans (congrFun (modulationWeight_zero m f.val) x)))
  · let F (u : K) := (ω u : ℂ) * f.val (u.val * x)
    have hi (u : K) : star (ω u : ℂ) * (twist₀ f) (u.val⁻¹ * x) = F u⁻¹ := by
      have hw : star (ω u : ℂ) = (ω u⁻¹ : ℂ) := by rw [map_inv, Circle.coe_inv_eq_conj]; rfl
      exact congrArg₂ (· * ·) hw (congrFun (modulationWeight_zero m f.val) (u.val⁻¹ * x))
    have he := (integral_congr_ae (ae_of_all μ₁ hi)).trans (integral_inv_eq_self F μ₁)
    have h₀ := (congrFun (modulationWeight_zero m g.val) x).symm
    have h₁ := congrArg (fun v : SchwartzBruhat G ↦ v x) hg
    have h₂ := (schwartzBruhatIsotypicProjector_apply m hm μ₁ ω (twist₀ f) x).2
    let I₀ := ∫ u : K, star (ω u : ℂ) * (twist₀ f) (u.val⁻¹ * x) ∂μ₁
    have hc : (μ₁.real univ)⁻¹ • I₀ = (μ₁.real univ : ℂ)⁻¹ * (∫ u, F u ∂μ₁) :=
      (show (μ₁.real univ)⁻¹ • I₀ = (((μ₁.real univ)⁻¹ : ℝ) : ℂ) * I₀ from Complex.real_smul).trans (congrArg₂ (· * ·) (Complex.ofReal_inv _) he)
    exact h₀.trans (h₁.trans (h₂.trans hc))

include hm hms in
private theorem exists_homogeneous_average (ω : PontryaginDual K) (f : E) :
    ∃ g : E, g ∈ H[ω] ∧ (f ∈ H[ω] → g = f) ∧ ∀ x : G, g.val x = (μ₁.real univ : ℂ)⁻¹ *
      ∫ u : K, (ω u : ℂ) * f.val (u.val * x) ∂μ₁ := by
  refine (exists_continuous_decay_average m hm hms μ₁ ω).elim fun A hA ↦ ?_
  exact ⟨A f, homogeneous_average_properties m hm μ₁ ω f (A f) (hA.2 f)⟩

private theorem periodization_average_apply (ω : PontryaginDual K) (f g : E)
    (hg : ∀ x : G, g.val x = (μ₁.real univ : ℂ)⁻¹ *
      ∫ u : K, (ω u : ℂ) * f.val (u.val * x) ∂μ₁) (x : G) :
    P g (q x) = (μ₁.real univ : ℂ)⁻¹ * ∫ u : K, (ω u : ℂ) * P f (q (u.val * x)) ∂μ₁ := by
  let M : ℂ := μ₁.real univ
  have hs := (hasSum_integral_weighted_orbit m γ hm hms hγ μ₁ ω f x).mul_left M⁻¹
  have hp := modulatedPeriodization_hasSum m γ hm hms hγ g x
  have he (n : ℤ) : g.val (γ ^ n * x) =
      M⁻¹ * (∫ u : K, (ω u : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁) :=
    (hg _).trans (congrArg (M⁻¹ * ·) (integral_congr_ae (ae_of_all μ₁ fun u ↦
      congrArg (fun z ↦ (ω u : ℂ) * f.val z) (mul_left_comm u.val (γ ^ n) x))))
  exact (hp.congr_fun (fun n ↦ (he n).symm)).unique hs

end Averages

/-- Paper: Proposition 4.5.1.1(1), p. 198. Periodization takes the corresponding
norm-one isotype on the decay space to a closed subspace of the quotient test space. -/
theorem modulatedPeriodization_isClosed_isotype_image (ω : PontryaginDual K) :
    IsClosed (P '' (H[ω] : Set E)) := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure K := Measure.haar
  let π : K →ₜ* Q := ⟨(q).comp (K).subtype, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩
  refine (exists_schwartz_average μ₁ π ω).elim fun A hA ↦ ?_
  have lifts (f : E) : ∃ g : E, g ∈ H[ω] ∧ (f ∈ H[ω] → g = f) ∧ P g = A (P f) := by
    refine (exists_homogeneous_average m hm hms μ₁ ω f).elim fun g hg ↦ ⟨g, hg.1, hg.2.1, ?_⟩
    refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
    have hp := periodization_average_apply m γ hm hms hγ μ₁ ω f g hg.2.2 x
    have he (u : K) : (ω u : ℂ) * P f (q (u.val * x)) = (ω u : ℂ) * P f (π u * q x) :=
      congrArg (fun z ↦ (ω u : ℂ) * P f z) (map_mul (q) u.val x)
    exact hp.trans ((congrArg ((μ₁.real univ : ℂ)⁻¹ * ·) (integral_congr_ae (ae_of_all μ₁ he))).trans
      (hA (P f) (q x)).symm)
  have he : P '' (H[ω] : Set E) = {y | A y = y} := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact (lifts f).elim fun g hg ↦ hg.2.2.symm.trans (congrArg (fun v ↦ P v) (hg.2.1 hf))
    · intro hy
      refine (modulatedPeriodization_surjective m γ hm hms hγ y).elim fun f hf ↦ ?_
      exact (lifts f).elim fun g hg ↦ ⟨g, hg.1, hg.2.2.trans ((congrArg A hf).trans hy)⟩
  exact Eq.mpr (congrArg IsClosed he) (isClosed_eq A.continuous continuous_id)

section DifferenceKernels

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "ωχ" => PontryaginDual.map
  (⟨(K).subtype, continuous_subtype_val⟩ : K →ₜ* G) χ
local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

-- TODO(paper-gap): On p. 202 the multiplier needs χ(γ)⁻¹. With the Mellin
-- weight χ(x)m(x)^s its zero lattice is 2πin/log(m γ) − it₀. The print has
-- the i in the numerator and writes log γ for the logarithm of the module.

-- TODO(paper-gap): The opening of the proof of (6) on p. 203 uses equality
-- with the actual difference range. Part (5) only identifies its closure.

omit [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 4.5.1.1(6), p. 198. The cyclic difference has closed range. -/
theorem modulatedCyclicDifference_isClosed_range : IsClosed (range Δ) := by sorry

omit [MeasurableSpace G] [BorelSpace G] in
private theorem mem_schwartzTranslationIsotype_iff (ω : PontryaginDual K) (f : SchwartzBruhat G) :
    f ∈ actionIsotype ((ρG).comp (K).subtype) ω ↔
      ∀ (u : K) (x : G), f (u.val⁻¹ * x) = (ω u : ℂ) * f x := by
  refine (mem_actionIsotype _ _ _).trans (forall_congr' fun u ↦ ⟨fun h x ↦ ?_, fun h ↦ ?_⟩)
  · have hx := congrArg (fun g : SchwartzBruhat G ↦ g x) h
    change ρG u.val f x = (ω u : ℂ) * f x at hx
    exact (schwartzBruhatTranslationAction_apply u.val x f).symm.trans hx
  · refine Subtype.ext (funext fun x ↦ ?_)
    change ρG u.val f x = (ω u : ℂ) * f x
    exact (schwartzBruhatTranslationAction_apply u.val x f).trans (h x)

omit [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 4.5.1.1(6), pp. 198, 203. Taking the range of the cyclic
difference commutes with passage to any norm-one isotype. -/
theorem modulatedCyclicDifference_range_isotype (ω : PontryaginDual K) :
    (Δ).range ⊓ H[ω] = (H[ω]).map (Δ).toLinearMap := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let μ₁ : Measure K := Measure.haar
  let F (v : E) (x : G) (u : K) := (ω u : ℂ) * v.val (u.val * x)
  have hint (v : E) (x : G) : Integrable (F v x) μ₁ := by
    have hv : Continuous v.val := (schwartzBruhat_continuous (twist₀ v)).congr
      fun z ↦ congrFun (modulationWeight_zero m v.val) z
    exact ((continuous_subtype_val.comp ω.continuous).mul (hv.comp
      (continuous_subtype_val.mul continuous_const))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
  have hΔ (v : E) (x : G) := modulatedCyclicDifference_apply m γ hm hms univ ordConnected_univ univ_nonempty v x
  have hmem (v : E) : v ∈ H[ω] ↔ ∀ (u : K) (x : G), v.val (u.val⁻¹ * x) = (ω u : ℂ) * v.val x := by
    change twist₀ v ∈ actionIsotype ((ρG).comp (K).subtype) ω ↔ _
    have he := mem_schwartzTranslationIsotype_iff m ω (twist₀ v)
    simpa only [show (twist₀ v).val = v.val from modulationWeight_zero m v.val] using he
  apply SetLike.ext
  intro f
  constructor
  · rintro ⟨⟨v, hv⟩, hf⟩
    refine (exists_homogeneous_average m hm hms μ₁ ω v).elim fun g hg ↦ ⟨g, hg.1, ?_⟩
    refine (exists_homogeneous_average m hm hms μ₁ ω f).elim fun u hu ↦ ?_
    have hfix := hu.2.1 hf
    refine Subtype.ext (funext fun x ↦ ?_)
    have he (k : K) : F v x k - F v (γ * x) k = F f x k := by
      have hpoint := (hΔ v (k.val * x)).symm.trans (congrArg (fun y : E ↦ y.val (k.val * x)) hv)
      change (ω k : ℂ) * v.val (k.val * x) - (ω k : ℂ) * v.val (k.val * (γ * x)) = _
      rw [mul_left_comm k.val γ, ← mul_sub, hpoint]
    have hi := (integral_sub (hint v x) (hint v (γ * x))).symm.trans (integral_congr_ae (ae_of_all μ₁ he))
    have hdiff := congrArg₂ (· - ·) (hg.2.2 x) (hg.2.2 (γ * x))
    exact (hΔ g x).trans (hdiff.trans ((mul_sub _ _ _).symm.trans
      ((congrArg ((μ₁.real univ : ℂ)⁻¹ * ·) hi).trans ((hu.2.2 x).symm.trans
        (congrArg (fun t : E ↦ t.val x) hfix)))))
  · rintro ⟨v, hv, h⟩
    refine ⟨⟨v, h⟩, (hmem f).mpr fun u x ↦ ?_⟩
    have hd (z : G) := (congrArg (fun w : E ↦ w.val z) h).symm.trans (hΔ v z)
    have hh := (hmem v).mp hv u
    calc
      _ = v.val (u.val⁻¹ * x) - v.val (γ * (u.val⁻¹ * x)) := hd _
      _ = (ω u : ℂ) * (v.val x - v.val (γ * x)) := by rw [hh, mul_left_comm γ, hh, mul_sub]
      _ = (ω u : ℂ) * f.val x := congrArg ((ω u : ℂ) * ·) (hd x).symm

end DifferenceKernels

section QuotientIsotype

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]

local notation "qK" => (q).comp (K).subtype
local notation "Sχ[" ω "]" => actionIsotype ((ρQ).comp qK) ω

-- TODO(paper-gap): In the proof on p. 201 the square of the unnormalized
-- quotient average is its Haar mass times the average itself.

local notation "Ψ[" ω "]" => modulatedQuotientIsotypicProjector m γ hm hγ μ₁ ω

/-- Paper: Notation 4.5.1.1, p. 204. The normalized average fixes every
function in the norm-one isotype. -/
theorem modulatedQuotientIsotypicProjector_fix (ω : PontryaginDual K) (f : Sχ[ω]) :
    Ψ[ω] f.val = f.val := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_closed m γ hγ
  have hμ : (μ₁.real univ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (measureReal_univ_pos (μ := μ₁)).ne'
  have hf := (mem_actionIsotype _ ω f.val).mp f.property
  -- Rewriting under `f.val` is very slow here, so the steps are explicit terms.
  have hpt (u : K) (z : Q) : (ω u : ℂ) * f.val (qK u * z) = f.val z := by
    have h : schwartzBruhatTranslationAction (G := Q) (qK u⁻¹) f.val z =
        (ω u⁻¹ : ℂ) * f.val z :=
      congrArg (fun g : S ↦ g z) (hf u⁻¹)
    have e : (qK u⁻¹)⁻¹ * z = qK u * z := by rw [map_inv, inv_inv]
    have h' : f.val (qK u * z) = (ω u⁻¹ : ℂ) * f.val z :=
      (congrArg (fun x ↦ f.val x) e).symm.trans
        ((schwartzBruhatTranslationAction_apply (G := Q) (qK u⁻¹) z f.val).symm.trans h)
    have hω : (ω u : ℂ) * (ω u⁻¹ : ℂ) = 1 := by
      rw [← Circle.coe_mul, ← map_mul, mul_inv_cancel, map_one, Circle.coe_one]
    exact (congrArg (fun c ↦ (ω u : ℂ) * c) h').trans
      ((mul_assoc _ _ _).symm.trans ((congrArg (· * f.val z) hω).trans (one_mul _)))
  refine Subtype.ext (funext fun z ↦ ?_)
  change (μ₁.real univ : ℂ)⁻¹ * ∫ u : K, (ω u : ℂ) * f.val (qK u * z) ∂μ₁ = f.val z
  have hint : ∫ u : K, (ω u : ℂ) * f.val (qK u * z) ∂μ₁ = (μ₁.real univ : ℂ) * f.val z :=
    (congrArg (fun g : K → ℂ ↦ ∫ u, g u ∂μ₁) (funext fun u ↦ hpt u z)).trans
      ((integral_const _).trans (Complex.real_smul ..))
  exact (congrArg (fun c ↦ (μ₁.real univ : ℂ)⁻¹ * c) hint).trans
    ((mul_assoc _ _ _).symm.trans ((congrArg (· * f.val z) (inv_mul_cancel₀ hμ)).trans
      (one_mul _)))

/-- Paper: Notation 4.5.1.1 and Equation (4.5.1.9), p. 204. The projector
has range exactly the norm-one isotype on the quotient. -/
theorem modulatedQuotientIsotypicProjector_range (ω : PontryaginDual K) :
    (Ψ[ω]).range = Sχ[ω] := by
  have : IsClosed (Γ : Set G) := modulatedCyclicSubgroup_closed m γ hγ
  refine le_antisymm ?_ fun f hf ↦ ⟨f, modulatedQuotientIsotypicProjector_fix m γ hm hγ μ₁ ω ⟨f, hf⟩⟩
  rintro _ ⟨f, rfl⟩
  refine (mem_actionIsotype _ ω _).mpr fun v ↦ Subtype.ext (funext fun z ↦ ?_)
  change schwartzBruhatTranslationAction (G := Q) (qK v) (Ψ[ω] f) z = (ω v : ℂ) * Ψ[ω] f z
  refine (schwartzBruhatTranslationAction_apply (G := Q) (qK v) z (Ψ[ω] f)).trans ?_
  change (μ₁.real univ : ℂ)⁻¹ * ∫ u : K, (ω u : ℂ) * f (qK u * ((qK v)⁻¹ * z)) ∂μ₁ =
    (ω v : ℂ) * ((μ₁.real univ : ℂ)⁻¹ * ∫ u : K, (ω u : ℂ) * f (qK u * z) ∂μ₁)
  set g : K → ℂ := fun u ↦ (ω u : ℂ) * f (qK u * z) with hg
  have hpt (u : K) : (ω u : ℂ) * f (qK u * ((qK v)⁻¹ * z)) = (ω v : ℂ) * g (u * v⁻¹) := by
    have e : qK (u * v⁻¹) * z = qK u * ((qK v)⁻¹ * z) := by
      rw [map_mul, map_inv, mul_assoc]
    have hω : (ω (u * v⁻¹) : ℂ) = (ω u : ℂ) * (ω v : ℂ)⁻¹ := by
      rw [map_mul, map_inv, Circle.coe_mul, Circle.coe_inv]
    have hv : (ω v : ℂ) ≠ 0 := Circle.coe_ne_zero _
    have h1 : g (u * v⁻¹) = (ω u : ℂ) * (ω v : ℂ)⁻¹ * f (qK u * ((qK v)⁻¹ * z)) :=
      (congrArg (· * f (qK (u * v⁻¹) * z)) hω).trans (congrArg (fun x ↦ _ * f x) e)
    rw [h1]
    field_simp
  have hint : ∫ u : K, (ω u : ℂ) * f (qK u * ((qK v)⁻¹ * z)) ∂μ₁ =
      (ω v : ℂ) * ∫ u : K, g u ∂μ₁ :=
    (congrArg (fun h : K → ℂ ↦ ∫ u, h u ∂μ₁) (funext hpt)).trans
      ((integral_const_mul _ _).trans
        (congrArg (fun c ↦ (ω v : ℂ) * c) (integral_mul_right_eq_self g v⁻¹)))
  rw [hint]
  ring

/-- Paper: Notation 4.5.1.1, p. 204. The normalized quotient projector is idempotent. -/
theorem modulatedQuotientIsotypicProjector_idempotent (ω : PontryaginDual K) :
    (Ψ[ω]).comp Ψ[ω] = Ψ[ω] := ContinuousLinearMap.ext fun f ↦ modulatedQuotientIsotypicProjector_fix m γ hm hγ μ₁ ω ⟨Ψ[ω] f, Eq.mp (congrArg (fun T ↦ Ψ[ω] f ∈ T) (modulatedQuotientIsotypicProjector_range m γ hm hγ μ₁ ω)) (LinearMap.mem_range_self _ f)⟩

variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)

variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "a" => modulatedCyclicFourierCoeff m γ hm hγ χ t₀ ht₀ μ₁ ν
local notation "e" => modulatedCyclicExponential m γ hm hγ χ t₀ ht₀

include hSC hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.5, p. 203. For a fixed norm-one character the
integer family of Fourier coefficient functionals is bounded in the strong dual. -/
theorem modulatedCyclicFourierCoeff_isVonNBounded (ω : PontryaginDual K) :
    IsVonNBounded ℂ (range fun n : ℤ ↦ a (ω, n)) := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompleteSpace S := schwartzBruhat_complete
  apply isVonNBounded_range_clm_of_pointwise (fun n : ℤ ↦ a (ω, n))
  intro f
  apply (NormedSpace.isVonNBounded_iff' ℂ).mpr
  let c : ℂ := ((L * μ₁.real univ)⁻¹ : ℝ)
  refine ⟨‖c‖ * ∫ z, ‖f z‖ ∂ν, ?_⟩
  rintro _ ⟨n, rfl⟩
  have h := (modulatedCyclicFourierCoeff_apply m γ hm hγ χ t₀ ht₀ μ₁ ν (ω, n) f).2
  have hu : (∫ z, ‖f z * star (e (ω, n) z)‖ ∂ν) = ∫ z, ‖f z‖ ∂ν := by
    refine integral_congr_ae (.of_forall fun z ↦ ?_)
    exact (norm_mul _ _).trans ((congrArg (‖f z‖ * ·)
      ((norm_star _).trans (Circle.norm_coe _))).trans (mul_one _))
  calc
    ‖a (ω, n) f‖ = ‖c * ∫ z, f z * star (e (ω, n) z) ∂ν‖ := congrArg norm h
    _ = _ := norm_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans_eq hu) (norm_nonneg c)

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.5, p. 203. The Fourier coefficients restricted
to the quotient isotype form a bounded set in its strong dual. -/
theorem modulatedCyclicFourierCoeff_isotype_isVonNBounded (ω : PontryaginDual K) :
    IsVonNBounded ℂ (range fun n : ℤ ↦ (a (ω, n)).comp (Sχ[ω]).subtypeL) := by
  let A : StrongDual ℂ S →L[ℂ] StrongDual ℂ (Sχ[ω]) := (Sχ[ω]).subtypeL.precomp ℂ
  have hb := modulatedCyclicFourierCoeff_isVonNBounded m γ hm hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω
  exact isVonNBounded_range_comp_clm A (fun n : ℤ ↦ a (ω, n)) hb

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.5, p. 203. The Fourier coefficients restricted
to the quotient isotype form an equicontinuous family. -/
theorem modulatedCyclicFourierCoeff_isotype_equicontinuous (ω : PontryaginDual K) :
    Equicontinuous (fun (n : ℤ) (f : Sχ[ω]) ↦ a (ω, n) f.val) := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : BarrelledSpace ℂ S := schwartzBruhat_barrelled
  have hb := modulatedCyclicFourierCoeff_isVonNBounded m γ hm hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω
  exact equicontinuous_comp_of_isVonNBounded_range_dual (fun n : ℤ ↦ a (ω, n)) hb
    (Sχ[ω]).subtypeL (Sχ[ω]).subtypeL.continuous

local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker
local notation "volQ" => (L * μ₁.real univ : ℂ)

local notation "T[" ω "]" => modulatedIsotypicPeriodizationQuotient m γ hm hms hγ μ₁ χ ω

private theorem periodization_on_isotype (η : PontryaginDual G) (ω : PontryaginDual K)
    (hη : ∀ u : K, η u.val = ω u) (f : E) (hf : f ∈ H[ω]) :
    modulatedIsotypicPeriodization m γ hm hms hγ μ₁ η f = (μ₁.real univ : ℂ) • P f := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hval (x : G) : twist₀ f x = f.val x := congrFun (modulationWeight_zero m f.val) x
  have hω (u : K) (y : G) : (η u.val : ℂ) * f.val (u.val * y) = f.val y := by
    have h := (mem_schwartzTranslationIsotype_iff m ω (twist₀ f)).mp hf u (u.val * y)
    have h' : (twist₀ f) y = (ω u : ℂ) * (twist₀ f) (u.val * y) :=
      (congrArg (fun z ↦ (twist₀ f) z) (inv_mul_cancel_left u.val y).symm).trans h
    calc
      _ = (ω u : ℂ) * f.val (u.val * y) := congrArg (fun c : Circle ↦ (c : ℂ) * _) (hη u)
      _ = (ω u : ℂ) * (twist₀ f) (u.val * y) := congrArg ((ω u : ℂ) * ·) (hval _).symm
      _ = f.val y := h'.symm.trans (hval y)
  refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
  have hs := (modulatedPeriodization_hasSum m γ hm hms hγ f x).mul_left M
  have ht := modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ η f x
  have hconst (n : ℤ) : (∫ u : K, (η u.val : ℂ) * f.val (γ ^ n * (u.val * x)) ∂μ₁) =
      M * f.val (γ ^ n * x) := by
    have he (u : K) := hω u (γ ^ n * x)
    rw [integral_congr_ae (.of_forall fun u ↦ (congrArg (fun y ↦ (η u.val : ℂ) * f.val y)
      (mul_left_comm (γ ^ n) u.val x)).trans (he u)), integral_const]
    exact Complex.real_smul
  exact (ht.congr_fun fun n ↦ (hconst n).symm).unique hs

include hχ in
/-- Paper: Corollary 4.5.1.6 and Equation (4.5.1.12), p. 204. The normalized
quotient map agrees with ordinary periodization on the matching isotype. -/
theorem modulatedIsotypicPeriodizationQuotient_mkQ (ω : PontryaginDual K)
    (f : E) (hf : f ∈ H[ω]) :
    T[ω] ((Pχ[ω]).ker.mkQ f) = P f := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  have he := periodization_on_isotype m γ hm hms hγ μ₁ (χ ω) ω (hχ ω) f hf
  exact (congrArg (M⁻¹ • ·) he).trans (inv_smul_smul₀ hM (P f))

include hχ in
/-- Paper: Equations (4.5.1.7)–(4.5.1.9) and (4.5.1.12), pp. 201, 204.
On every lift the normalized quotient map applies the quotient projector after
ordinary periodization. The unnormalized map of §4.4 multiplies this by the kernel mass. -/
theorem modulatedIsotypicPeriodizationQuotient_projector (ω : PontryaginDual K) (f : E) :
    T[ω] ((Pχ[ω]).ker.mkQ f) = Ψ[ω] (P f) ∧
      Pχ[ω] f = (μ₁.real univ : ℂ) • Ψ[ω] (P f) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  have h (x : G) : Pχ[ω] f (q x) = ∫ u : K, (ω u : ℂ) * P f (q (u.val * x)) ∂μ₁ := by
    have ht := modulatedIsotypicPeriodization_hasSum m γ hm hms hγ μ₁ (χ ω) f x
    have hs := hasSum_integral_weighted_orbit m γ hm hms hγ μ₁ ω f x
    exact (ht.congr_fun fun n ↦ integral_congr_ae (.of_forall fun u ↦
      congrArg (fun c : Circle ↦ (c : ℂ) * _) (hχ ω u).symm)).unique hs
  have normalized : T[ω] ((Pχ[ω]).ker.mkQ f) = Ψ[ω] (P f) := by
    refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
    change M⁻¹ * Pχ[ω] f (q x) = M⁻¹ * ∫ u : K, (ω u : ℂ) * P f (qK u * q x) ∂μ₁
    refine congrArg (M⁻¹ * ·) ((h x).trans (integral_congr_ae (.of_forall fun u ↦ ?_)))
    exact congrArg (fun z ↦ (ω u : ℂ) * P f z) (map_mul (q) u.val x)
  refine ⟨normalized, ?_⟩
  exact (smul_inv_smul₀ hM (Pχ[ω] f)).symm.trans (congrArg (M • ·) normalized)

include hχ in
/-- Paper: Equation (4.5.1.12), p. 204. The induced periodization identifies
the kernel quotient topologically with the quotient isotype. -/
theorem modulatedIsotypicPeriodizationQuotient_equiv (ω : PontryaginDual K) :
    ∃ F : V[ω] ≃L[ℂ] Sχ[ω], ∀ v, (F v).val = T[ω] v := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  have hR := range_smul_comp_of_surjective (X := E) (Y := S) Pχ[ω] P Ψ[ω] (modulatedPeriodization_surjective m γ hm hms hγ)
    M hM (fun f ↦ (modulatedIsotypicPeriodizationQuotient_projector m γ hm hms hγ μ₁ χ hχ ω f).2)
  exact quotient_equiv_of_scaled_range (X := E) (Y := S) Pχ[ω] (modulatedIsotypicPeriodization_isOpenMap_range
    m γ hm hms hγ μ₁ (χ ω)) M⁻¹ (inv_ne_zero hM) _ (hR.trans (modulatedQuotientIsotypicProjector_range
      m γ hm hγ μ₁ ω))

local notation "b[" ω "]" => modulatedCyclicPairing m γ hm hms hγ μ₁ χ t₀ ht₀ ν ω
local notation "pairing[" ω "," n "," f "]" =>
  fun x : G ↦ (f).val x * star (e (ω, n) (q x))

private theorem integral_average_character {X Y : Type*}
    [CommGroup X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X] [CompactSpace X] [SecondCountableTopology X]
    [CommGroup Y] [TopologicalSpace Y] [IsTopologicalGroup Y] [T2Space Y]
    [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] [SecondCountableTopology Y]
    (μX : Measure X) [μX.IsHaarMeasure] (μY : Measure Y) [μY.IsHaarMeasure]
    (π : X →ₜ* Y) (ω : PontryaginDual X) (η : PontryaginDual Y)
    (hη : ∀ u, η (π u) = (ω u)⁻¹) (F : Y → ℂ) (hF : Continuous F) :
    (∫ z, ((μX.real univ : ℂ)⁻¹ * (∫ u, (ω u : ℂ) * F (π u * z) ∂μX)) * star (η z : ℂ) ∂μY) =
      ∫ z, F z * star (η z : ℂ) ∂μY := by
  let M : ℂ := μX.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μX))
  let H (z : Y) (u : X) := ((ω u : ℂ) * F (π u * z)) * star (η z : ℂ)
  let J := ∫ z, F z * star (η z : ℂ) ∂μY
  have hcont : Continuous (Function.uncurry H) := by
    exact (((continuous_subtype_val.comp ω.continuous).comp continuous_snd).mul
      (hF.comp ((π.continuous.comp continuous_snd).mul continuous_fst))).mul
      (((continuous_subtype_val.comp η.continuous).comp continuous_fst).star)
  have hs := integral_integral_swap (μ := μY) (ν := μX)
    (hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
  have hinner (u : X) : (∫ z, H z u ∂μY) = J := by
    have he (z : Y) : H z u = F (π u * z) * star (η (π u * z) : ℂ) := by
      have hc : star (η (π u) : ℂ) = (ω u : ℂ) := by rw [hη, Circle.coe_inv_eq_conj]; exact star_star _
      rw [map_mul, Circle.coe_mul, star_mul', hc]
      dsimp only [H]
      ring
    exact (integral_congr_ae (ae_of_all μY he)).trans
      (integral_mul_left_eq_self (μ := μY) (fun z ↦ F z * star (η z : ℂ)) (π u))
  have hout (z : Y) : (M⁻¹ * (∫ u, (ω u : ℂ) * F (π u * z) ∂μX)) * star (η z : ℂ) =
      M⁻¹ * ∫ u, H z u ∂μX := by rw [mul_assoc, ← integral_mul_const]
  have hj : (∫ _ : X, J ∂μX) = M * J := by rw [integral_const]; exact Complex.real_smul
  exact (integral_congr_ae (ae_of_all μY hout)).trans ((integral_const_mul (μ := μY) _ _).trans
    ((congrArg (M⁻¹ * ·) (hs.trans ((integral_congr_ae (ae_of_all μX hinner)).trans hj))).trans
      (inv_mul_cancel_left₀ hM J)))

private theorem cosetIntegral_mul_pullback {A : Type*} [CommGroup A] [MeasurableSpace A]
    (H : Subgroup A) (μH : Measure H) (f : A → ℂ) (w : A ⧸ H → ℂ) (z : A ⧸ H) :
    lcaCosetIntegral H μH (fun x ↦ f x * w (QuotientGroup.mk x)) z =
      lcaCosetIntegral H μH f z * w z := by
  have he (h : H) : QuotientGroup.mk (z.out * h.val) = z := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff h.val).mpr h.property, mul_one]
    exact Quotient.out_eq' _
  exact (integral_congr_ae (ae_of_all μH fun h ↦ congrArg (fun y ↦ f (z.out * h.val) * w y) (he h))).trans
    (integral_mul_const (w z) _)

private theorem periodization_eq_cosetIntegral [(Measure.count : Measure Γ).IsHaarMeasure]
    [(Measure.count : Measure Γ).Regular] (f : E) (z : Q) :
    lcaCosetIntegral Γ Measure.count f.val z = P f z := by
  refine QuotientGroup.induction_on z fun x ↦ ?_
  have hs := cyclicCosetIntegral_hasSum m γ hγ (twist₀ f) x
  have hp := modulatedPeriodization_hasSum m γ hm hms hγ f x
  have hval : (twist₀ f).val = f.val := modulationWeight_zero m f.val
  have h : lcaCosetIntegral Γ Measure.count (twist₀ f).val (q x) = P f (q x) :=
    (hs.congr_fun (fun n ↦ (congrFun hval _).symm)).unique hp
  exact (congrArg (fun v : G → ℂ ↦ lcaCosetIntegral Γ Measure.count v (q x)) hval).symm.trans h

include hχ in
private theorem modulatedCyclicCharacter_kernel (j : PontryaginDual K × ℤ) (u : K) :
    modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j (QuotientGroup.mk u.val) = (j.1 u)⁻¹ := by
  have h := modulatedCyclicCharacter_mk m γ hγ χ t₀ ht₀ j u.val
  have hu : m u.val = 1 := u.property
  simpa only [hχ j.1 u, hu, Units.val_one, NNReal.coe_one, Real.log_one, mul_zero,
    Circle.exp_zero, mul_one] using h

include hχ hτ hμ hν in
/-- Paper: Equation (4.5.1.10), pp. 204–205. On a lift, the quotient functional
integrates the function against the corresponding annihilator character of G. -/
theorem modulatedCyclicPairing_mkQ (ω : PontryaginDual K) (n : ℤ) (f : E) :
    Integrable (pairing[ω, n, f]) μ ∧
      b[ω] n ((Pχ[ω]).ker.mkQ f) = ∫ x, pairing[ω, n, f] x ∂μ := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let := modulatedCyclicQuotient_compact m γ hm hγ
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : BorelSpace Q := ⟨rfl⟩
  let := modulated_zpowers_discrete m γ hγ
  let : (Measure.count : Measure Γ).IsHaarMeasure := count_isHaarMeasure_of_discreteTopology
  let : (Measure.count : Measure Γ).Regular := count_regular_of_discreteTopology
  let η := modulatedCyclicCharacter m γ hγ χ t₀ ht₀ (ω, n)
  let π : K →ₜ* Q := ⟨qK, QuotientGroup.continuous_mk.comp continuous_subtype_val⟩
  let w (z : Q) := star (η z : ℂ)
  have hη (u : K) : η (π u) = (ω u)⁻¹ :=
    modulatedCyclicCharacter_kernel m γ hγ χ t₀ ht₀ hχ (ω, n) u
  have hf : Integrable f.val μ := by
    have h := modulatedFourierMellin_integrable m univ hm ordConnected_univ univ_nonempty μ isOpen_univ hms f
      ⟨1, Set.mem_univ _⟩
    have he : (fun x : G ↦ f.val x * (1 : QuasiCharacter G) x) = f.val :=
      funext fun x ↦ mul_one (f.val x)
    exact Eq.mp (congrArg (fun F : G → ℂ ↦ Integrable F μ) he) h
  have hw : Continuous (fun x : G ↦ w (q x)) :=
    ((continuous_subtype_val.comp η.continuous).comp QuotientGroup.continuous_mk).star
  have hF : Integrable (fun x : G ↦ f.val x * w (q x)) μ :=
    hf.mul_bdd (c := 1) hw.aestronglyMeasurable (.of_forall fun x ↦ by
      change ‖star (η (q x) : ℂ)‖ ≤ 1
      rw [norm_star, Circle.norm_coe])
  refine ⟨hF, ?_⟩
  let v := (Pχ[ω]).ker.mkQ f
  have ht := (modulatedIsotypicPeriodizationQuotient_projector m γ hm hms hγ μ₁ χ hχ ω f).1
  have hc := (modulatedCyclicFourierCoeff_apply m γ hm hγ χ t₀ ht₀ μ₁ ν (ω, n) (T[ω] v)).2
  have hd : ((↑((L * μ₁.real univ)⁻¹) : ℂ)) = (volQ)⁻¹ :=
    (Complex.ofReal_inv _).trans (congrArg Inv.inv (Complex.ofReal_mul _ _))
  have hvol : (volQ) ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hγ)).ne')
    (Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁)))
  have hcoeff : b[ω] n v = ∫ z, T[ω] v z * w z ∂ν :=
    (congrArg ((volQ) * ·) hc).trans ((congrArg (fun d : ℂ ↦ (volQ) * (d * _)) hd).trans
      (mul_inv_cancel_left₀ hvol _))
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  have hproj := integral_average_character μ₁ ν π ω η hη (fun z ↦ P f z) (schwartzBruhat_continuous _)
  have heq (z : Q) : T[ω] v z * w z = (Ψ[ω] (P f)) z * w z :=
    congrArg (fun y : S ↦ y z * w z) ht
  have hweil := (weilQuotientIntegral_L1 Γ (modulatedCyclicSubgroup_closed m γ hγ) μ Measure.count ν hν hF).2.2
  have hfib (z : Q) : lcaCosetIntegral Γ Measure.count (fun x ↦ f.val x * w (q x)) z = P f z * w z :=
    (cosetIntegral_mul_pullback Γ Measure.count f.val w z).trans
      (congrArg (· * w z) (periodization_eq_cosetIntegral m γ hm hms hγ f z))
  exact hcoeff.trans ((integral_congr_ae (ae_of_all ν heq)).trans (hproj.trans
    (hweil.trans (integral_congr_ae (ae_of_all ν hfib))).symm))

include hχ in
private theorem isotypicProjector_exponential [DecidableEq (PontryaginDual K)] (ω : PontryaginDual K) (j : PontryaginDual K × ℤ) :
    Ψ[ω] (e j) = if j.1 = ω then e j else 0 := by
  classical
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let η := modulatedCyclicCharacter m γ hγ χ t₀ ht₀ j
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  have he (z : Q) (u : K) : (ω u : ℂ) * e j (qK u * z) =
      (star (j.1 u : ℂ) * (ω u : ℂ)) * (η z : ℂ) := by
    change (ω u : ℂ) * (η (qK u * z) : ℂ) = _
    have h := modulatedCyclicCharacter_kernel m γ hγ χ t₀ ht₀ hχ j u
    rw [map_mul, Circle.coe_mul, show η (qK u) = (j.1 u)⁻¹ from h, Circle.coe_inv_eq_conj]
    change (ω u : ℂ) * (star (j.1 u : ℂ) * (η z : ℂ)) = _
    ring
  have h := integral_character_pair μ₁ j.1 ω
  have hf (z : Q) : Ψ[ω] (e j) z = M⁻¹ * ((if j.1 = ω then M else 0) * (η z : ℂ)) := by
    have hi := (integral_congr_ae (ae_of_all μ₁ (he z))).trans
      ((integral_mul_const (η z : ℂ) _).trans (congrArg (· * (η z : ℂ)) h))
    exact congrArg (M⁻¹ * ·) hi
  by_cases hω : j.1 = ω
  · refine Eq.trans (b := e j) ?_ (ite_eq_left hω).symm
    refine Subtype.ext (funext fun z ↦ (hf z).trans ?_)
    exact (congrArg (fun d : ℂ ↦ M⁻¹ * (d * (η z : ℂ))) (ite_eq_left hω)).trans
      (inv_mul_cancel_left₀ hM (η z : ℂ))
  · refine Eq.trans (b := (0 : S)) ?_ (ite_eq_right hω).symm
    refine Subtype.ext (funext fun z ↦ (hf z).trans ?_)
    exact (congrArg (fun d : ℂ ↦ M⁻¹ * (d * (η z : ℂ))) (ite_eq_right hω)).trans
      ((congrArg (M⁻¹ * ·) (zero_mul (η z : ℂ))).trans (mul_zero _))

private theorem absolute_basis_of_retraction {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (T : X →L[ℂ] Y) (R : Y →L[ℂ] X) (hRT : ∀ x, R (T x) = x)
    (y : ℕ → Y) (l : ℕ → StrongDual ℂ Y) (hb : IsSchauderBasis y l)
    (hu : SchauderBasis.IsUnconditional y l) (ha : SchauderBasis.IsAbsolute y l)
    (s : ℕ → ℕ) (hs : Injective s) (hfix : ∀ n, T (R (y (s n))) = y (s n))
    (hzero : ∀ j ∉ range s, R (y j) = 0) (c : ℂ) (hc : c ≠ 0) :
    let x := fun n ↦ c⁻¹ • R (y (s n))
    let f := fun n ↦ c • (l (s n)).comp T
    IsSchauderBasis x f ∧ SchauderBasis.IsAbsolute x f := by
  intro x f
  have he (i : ℕ) (u : X) : f i u • x i = R (l (s i) (T u) • y (s i)) := by
    change (c * l (s i) (T u)) • (c⁻¹ • R (y (s i))) = _
    rw [map_smul, smul_smul, mul_right_comm, mul_inv_cancel₀ hc, one_mul]
  have hbi (i j : ℕ) : f i (x j) = if i = j then 1 else 0 := by
    change c * l (s i) (T (c⁻¹ • R (y (s j)))) = _
    rw [map_smul, hfix, map_smul]
    change c * (c⁻¹ * l (s i) (y (s j))) = _
    rw [mul_inv_cancel_left₀ hc]
    exact (hb.1 (s i) (s j)).trans (by by_cases h : i = j <;> simp [h, hs.eq_iff])
  have hsum (u : X) : HasSum (fun i ↦ f i u • x i) u := by
    let g (j : ℕ) := R (l j (T u) • y j)
    have hall : HasSum g u := (hRT u) ▸ (hu (T u)).map R.toAddMonoidHom R.continuous
    have hvan (j : ℕ) (hj : j ∉ range s) : g j = 0 := by
      change R (_ • y j) = 0
      rw [map_smul, hzero j hj, smul_zero]
    exact ((hs.hasSum_iff hvan).mpr hall).congr_fun fun i ↦ he i u
  refine ⟨⟨hbi, fun u ↦ Tendsto.mono_left (hsum u) (SummationFilter.conditional ℕ).le_atTop⟩, ?_⟩
  intro p hp
  let q₀ := p.comp R.toLinearMap
  refine (ha q₀ (hp.comp R.continuous)).elim fun q₁ hq ↦
    ⟨q₁.comp T.toLinearMap, hq.1.comp T.continuous, fun u ↦ ?_⟩
  let b (j : ℕ) := q₀ (l j (T u) • y j)
  have hbnd := hq.2 (T u)
  have hsel : Summable (b ∘ s) := hbnd.1.comp_injective hs
  have hle := hsel.tsum_le_tsum_of_inj s hs (fun j _ ↦ apply_nonneg _ _) (fun j ↦ le_rfl) hbnd.1
  have heq : (fun j ↦ p (f j u • x j)) = b ∘ s := funext fun j ↦ congrArg p (he j u)
  exact ⟨heq ▸ hsel, (congrArg (fun v : ℕ → ℝ ↦ ∑' j, v j) heq).trans_le (hle.trans hbnd.2)⟩

private theorem dual_basis_of_retraction {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    (T : X →L[ℂ] Y) (R : Y →L[ℂ] X) (hRT : ∀ x, R (T x) = x)
    (y : ℕ → Y) (l : ℕ → StrongDual ℂ Y)
    (hd : ∀ g : StrongDual ℂ Y, HasSum (fun j ↦ g (y j) • l j) g)
    (s : ℕ → ℕ) (hs : Injective s) (hzero : ∀ j ∉ range s, R (y j) = 0)
    (c : ℂ) (hc : c ≠ 0) :
    let x := fun n ↦ c⁻¹ • R (y (s n))
    let f := fun n ↦ c • (l (s n)).comp T
    let d := fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (x n)
    IsSchauderBasis x f → IsSchauderBasis f d ∧ SchauderBasis.IsUnconditional f d := by
  intro x f d hb
  have hbi (i j : ℕ) : d i (f j) = if i = j then 1 else 0 :=
    (hb.1 j i).trans (by by_cases h : i = j <;> simp [h, eq_comm])
  let C : StrongDual ℂ Y →L[ℂ] StrongDual ℂ X := ContinuousLinearMap.precomp ℂ T
  have hsum (g : StrongDual ℂ X) : HasSum (fun j ↦ d j g • f j) g := by
    let h := g.comp R
    have hg : C h = g := ContinuousLinearMap.ext fun u ↦ congrArg g (hRT u)
    let v (j : ℕ) := C (h (y j) • l j)
    have hall : HasSum v g := hg ▸ (hd h).map C.toAddMonoidHom C.continuous
    have hvan (j : ℕ) (hj : j ∉ range s) : v j = 0 := by
      have hz : h (y j) = 0 := (congrArg g (hzero j hj)).trans (map_zero g)
      exact (congrArg C ((congrArg (· • l j) hz).trans (zero_smul ℂ _))).trans (map_zero C)
    refine ((hs.hasSum_iff hvan).mpr hall).congr_fun fun j ↦ ?_
    change (g (c⁻¹ • R (y (s j)))) • (c • (l (s j)).comp T) = C (h (y (s j)) • l (s j))
    rw [map_smul, map_smul, smul_smul]
    change (c⁻¹ * g (R (y (s j))) * c) • _ = g (R (y (s j))) • _
    rw [mul_right_comm, inv_mul_cancel₀ hc, one_mul]
    rfl
  exact ⟨⟨hbi, fun g ↦ Tendsto.mono_left (hsum g) (SummationFilter.conditional ℕ).le_atTop⟩, hsum⟩

private theorem bases_on_selected_indices {X Y J : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    [T2Space Y]
    (T : X →L[ℂ] Y) (R : Y →L[ℂ] X) (hRT : ∀ x, R (T x) = x)
    (y : J → Y) (l : J → StrongDual ℂ Y) (enum : ℕ ≃ J)
    (hb : ∀ σ : ℕ ≃ J, IsSchauderBasis (y ∘ σ) (l ∘ σ) ∧ SchauderBasis.IsAbsolute (y ∘ σ) (l ∘ σ))
    (hd : ∀ σ : ℕ ≃ J, IsSchauderBasis (l ∘ σ)
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (y (σ n))))
    (t : ℕ → J) (ht : Injective t)
    (hfix : ∀ n, T (R (y (enum (enum.symm (t n))))) = y (enum (enum.symm (t n))))
    (hz : ∀ j ∉ range (enum.symm ∘ t), R (y (enum j)) = 0) (c : ℂ) (hc : c ≠ 0) :
    let x := fun n ↦ c⁻¹ • R (y (t n))
    let f := fun n ↦ c • (l (t n)).comp T
    let d := fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (x n)
    IsSchauderBasis x f ∧ SchauderBasis.IsAbsolute x f ∧
      (∀ n, T (x n) = c⁻¹ • y (t n)) ∧ IsSchauderBasis f d ∧ SchauderBasis.IsUnconditional f d := by
  let s := enum.symm ∘ t
  have hs : Injective s := enum.symm.injective.comp ht
  have hu := (SchauderBasis.isUnconditional_iff_forall_permutation _ _ (hb enum).1).mpr
    (fun u σ ↦ ((hb (σ.trans enum)).1.2 u).summable)
  have hv := (SchauderBasis.isUnconditional_iff_forall_permutation _ _ (hd enum)).mpr
    (fun g σ ↦ ((hd (σ.trans enum)).2 g).summable)
  have H := absolute_basis_of_retraction T R hRT (y ∘ enum) (l ∘ enum) (hb enum).1 hu
    (hb enum).2 s hs hfix hz c hc
  have D := dual_basis_of_retraction T R hRT (y ∘ enum) (l ∘ enum) hv s hs hz c hc H.1
  have he (j : ℕ) : enum (s j) = t j := enum.apply_symm_apply _
  dsimp only [Function.comp_apply] at H D
  simp only [he] at H D hfix
  exact ⟨H.1, H.2, fun n ↦ (map_smul T _ _).trans (congrArg (c⁻¹ • ·)
    (show T (R (y (t n))) = y (t n) by simpa only [Equiv.apply_symm_apply] using hfix n)), D⟩

private theorem retain_character_frequencies {X Y A : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [DecidableEq A]
    (T : X →L[ℂ] Y) (R : Y →L[ℂ] X) (P₁ : Y → Y) (v : A × ℤ → Y)
    (hRT : ∀ x, R (T x) = x) (hTR : ∀ y, T (R y) = P₁ y)
    (ω : A) (σ : ℕ ≃ ℤ) (enum : ℕ ≃ A × ℤ)
    (he : ∀ j, P₁ (v j) = if j.1 = ω then v j else 0) :
    let s := fun i ↦ enum.symm (ω, σ i)
    (∀ i, T (R (v (enum (s i)))) = v (enum (s i))) ∧ ∀ j ∉ range s, R (v (enum j)) = 0 := by
  intro s
  constructor
  · intro i
    have heq : (enum (s i)).1 = ω := congrArg Prod.fst (enum.apply_symm_apply (ω, σ i))
    exact (hTR _).trans ((he _).trans (ite_eq_left heq))
  · intro j hj
    have hj' : (enum j).1 ≠ ω := by
      intro hω
      apply hj
      refine ⟨σ.symm (enum j).2, enum.injective ?_⟩
      exact (enum.apply_symm_apply _).trans (Prod.ext hω.symm (σ.apply_symm_apply _))
    have hz := (hTR _).trans ((he (enum j)).trans (ite_eq_right hj'))
    exact (hRT _).symm.trans ((congrArg R hz).trans (map_zero R))

private theorem quotient_bases_on_character_isotype {D₀ Y A : Type*}
    [AddCommGroup D₀] [Module ℂ D₀] [TopologicalSpace D₀] [IsTopologicalAddGroup D₀] [ContinuousSMul ℂ D₀]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℂ Y]
    [T2Space Y] [DecidableEq A]
    (N : Submodule ℂ D₀)
    (T : (D₀ ⧸ N) →L[ℂ] Y) (proj : Y → Y) (v : A × ℤ → Y) (l : A × ℤ → StrongDual ℂ Y)
    (ω : A) (σ : ℕ ≃ ℤ) (c : ℂ) (hc : c ≠ 0) (f : ℕ → StrongDual ℂ (D₀ ⧸ N))
    (hf : ∀ i, f i = c • (l (ω, σ i)).comp T)
    (hR : ∃ R : Y →L[ℂ] (D₀ ⧸ N), (∀ u, R (T u) = u) ∧ ∀ y, T (R y) = proj y)
    (he : ∀ j, proj (v j) = if j.1 = ω then v j else 0)
    (hp : Nonempty (ℕ ≃ A × ℤ) ∧ ∀ p : ℕ ≃ A × ℤ, IsSchauderBasis (v ∘ p) (l ∘ p) ∧
      SchauderBasis.IsAbsolute (v ∘ p) (l ∘ p))
    (hd : ∀ p : ℕ ≃ A × ℤ, IsSchauderBasis (l ∘ p)
      (fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (v (p n)))) :
    ∃ x : ℕ → (D₀ ⧸ N), IsSchauderBasis x f ∧ SchauderBasis.IsAbsolute x f ∧
      (∀ i, T (x i) = c⁻¹ • v (ω, σ i)) ∧
      ∃ d : ℕ → StrongDual ℂ (StrongDual ℂ (D₀ ⧸ N)),
        IsSchauderBasis f d ∧ SchauderBasis.IsUnconditional f d := by
  obtain ⟨⟨enum⟩, hb⟩ := hp
  obtain ⟨R, hRT, hTR⟩ := hR
  let t := fun i : ℕ ↦ (ω, σ i)
  have ht : Injective t := fun _ _ h ↦ σ.injective (congrArg Prod.snd h)
  have hz := retain_character_frequencies T R proj v hRT hTR ω σ enum he
  have h := bases_on_selected_indices T R hRT v l enum hb hd t ht hz.1 hz.2 c hc
  have ef : f = fun i ↦ c • (l (t i)).comp T := funext hf
  subst f
  exact ⟨_, h.1, h.2.1, h.2.2.1, _, h.2.2.2⟩

include hχ in
private theorem exists_basis_retraction (ω : PontryaginDual K) :
    ∃ R : S →L[ℂ] V[ω], (∀ u, R (T[ω] u) = u) ∧ ∀ y, T[ω] (R y) = Ψ[ω] y := by
  have hE := modulatedIsotypicPeriodizationQuotient_equiv m γ hm hms hγ μ₁ χ hχ ω
  have hA := modulatedQuotientIsotypicProjector_range m γ hm hγ μ₁ ω
  have hF := modulatedQuotientIsotypicProjector_fix m γ hm hγ μ₁ ω
  refine hE.elim fun U hU ↦ ?_
  have hmem (y : S) : Ψ[ω] y ∈ Sχ[ω] :=
    (Iff.of_eq (congrArg (fun H : Submodule ℂ S ↦ Ψ[ω] y ∈ H) hA)).mp
      (LinearMap.mem_range_self _ y)
  let B := (Ψ[ω]).codRestrict Sχ[ω] hmem
  let R := U.symm.toContinuousLinearMap.comp B
  have hTR₀ (z : Sχ[ω]) : T[ω] (U.symm z) = z.val :=
    (hU (U.symm z)).symm.trans (congrArg (fun w : Sχ[ω] ↦ w.val) (U.apply_symm_apply z))
  have hB (x : V[ω]) : B (T[ω] x) = U x := by
    refine Subtype.ext ?_
    exact (congrArg Ψ[ω] (hU x).symm).trans (hF (U x))
  have hR (y : S) := ContinuousLinearMap.comp_apply U.symm.toContinuousLinearMap B y
  have hval (y : S) := ContinuousLinearMap.coe_codRestrict_apply Ψ[ω] Sχ[ω] hmem y
  have hRT (x : V[ω]) : R (T[ω] x) = x :=
    (hR _).trans ((congrArg U.symm (hB x)).trans (U.symm_apply_apply x))
  have hTR (y : S) : T[ω] (R y) = Ψ[ω] y :=
    (congrArg T[ω] (hR y)).trans ((hTR₀ (B y)).trans (hval y))
  exact ⟨R, hRT, hTR⟩

include hχ hτ hμ hν in
private theorem quotient_isotype_bases (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    ∃ v : ℕ → V[ω], IsSchauderBasis v (b[ω] ∘ σ) ∧ SchauderBasis.IsAbsolute v (b[ω] ∘ σ) ∧
      (∀ n, T[ω] (v n) = volQ⁻¹ • e (ω, σ n)) ∧
      ∃ d : ℕ → StrongDual ℂ (StrongDual ℂ (V[ω])),
        IsSchauderBasis (b[ω] ∘ σ) d ∧ SchauderBasis.IsUnconditional (b[ω] ∘ σ) d := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  have hvol : (volQ) ≠ 0 := mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (Real.log_pos (by exact_mod_cast hγ)).ne')
    (Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁)))
  have hfull := modulatedCyclicExponential_absoluteBasis m γ hm hms hγ χ hχ t₀ ht₀ μ₁ ν τ hτ μ hμ hν
  have hd (p : ℕ ≃ PontryaginDual K × ℤ) :=
    (modulatedCyclicFourierCoeff_absoluteBasis m γ hm hms hγ χ hχ t₀ ht₀ μ₁ ν τ hτ μ hμ hν p).1
  classical
  have hr := exists_basis_retraction m γ hm hms hγ μ₁ χ hχ ω
  have he := isotypicProjector_exponential m γ hm hγ μ₁ χ t₀ ht₀ hχ ω
  let coordinates := b[ω] ∘ σ
  have hfun (i : ℕ) : coordinates i = volQ • (a (ω, σ i)).comp T[ω] := rfl
  have result := quotient_bases_on_character_isotype (D₀ := E) (Y := S) (Pχ[ω]).ker T[ω] Ψ[ω] (e) (a) ω σ
    volQ hvol coordinates hfun hr he hfull hd
  exact result

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.6, p. 204. For every enumeration of the integer
frequencies the integral functionals form an unconditional Schauder basis
of the strong dual of the kernel quotient. This dual represents the kernel annihilator. -/
theorem modulatedCyclicPairing_unconditionalBasis (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (V[ω])),
      IsSchauderBasis (b[ω] ∘ σ) c ∧
        SchauderBasis.IsUnconditional (b[ω] ∘ σ) c := by
  refine (quotient_isotype_bases m γ hm hms hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω σ).elim
    fun _ hv ↦ hv.2.2.2

-- TODO(paper-gap): In Corollary 4.5.1.6 the full periodization depends on the
-- representative of the homogeneous kernel class. The unnormalized integral pairs to the
-- quotient volume against the matching unscaled exponential.

include hχ hτ hμ hν in
/-- Paper: Corollary 4.5.1.6 and Equation (4.5.1.11), p. 204. The
biorthogonal vectors form an absolute basis of the kernel quotient.
Deviation: Periodization uses isotypic representatives, and the displayed
exponentials are divided by the quotient Haar volume to match (4.5.1.10). -/
theorem modulatedIsotypicPeriodizationQuotient_absoluteBasis
    (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    ∃ v : ℕ → V[ω], IsSchauderBasis v (b[ω] ∘ σ) ∧
      SchauderBasis.IsAbsolute v (b[ω] ∘ σ) ∧
      ∀ n, T[ω] (v n) = volQ⁻¹ • e (ω, σ n) := by
  refine (quotient_isotype_bases m γ hm hms hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω σ).elim
    fun v hv ↦ ⟨v, hv.1, hv.2.1, hv.2.2.1⟩

end QuotientIsotype

/-! ## 4.5.2 Support conditions -/

section Support

variable (B : Set ℝ≥0ˣ) (k : Subgroup G)

-- TODO(paper-gap): The opening of §4.5.2 uses a global completed projective
-- tensor isomorphism despite the compact-generation restriction in Remark 4.5.1.3.

/-- Paper: §4.5.2, p. 205. The fixed-support space consists of compactly supported
two-sided decay functions that vanish off the module window. For the paper's
compact windows their topological support also lies in the window.
Deviation: The support cylinder is written as the preimage of the window under
the module. For a section τ this is τ(B) times the norm-one group. -/
def modulatedCompactSupportSubmodule : Submodule ℂ E :=
  (bruhatCompactSupportSubmodule G).comap (modulatedExponentialDecaySubmodule m Set.univ).subtype ⊓
    ⨅ x : {x : G // m x ∉ B}, LinearMap.ker
      ((LinearMap.proj x.val).comp (modulatedExponentialDecaySubmodule m Set.univ).subtype)

/-- An abstract form of `mem_modulatedCompactSupportSubmodule_iff`: in a function space with
generating seminorms, membership in a submodule `Tf` that cuts out compact support, intersected
with the kernels of evaluation off a closed set `Z`, means compact support with topological
support in `Z`. Stated abstractly so that elaboration does not unfold the decay space. -/
private theorem mem_comap_inf_iInf_ker_proj_iff {X : Type*} [TopologicalSpace X]
    (Sf Tf : Submodule ℂ (X → ℂ)) {ι : Type*} (p : SeminormFamily ℂ Sf ι) (Z : Set X)
    (hZ : IsClosed Z) (hT : ∀ g : Sf, g.val ∈ Tf ↔ HasCompactSupport g.val)
    (f : WithGeneratingSeminorms Sf p) :
    f ∈ (Tf.comap (Sf.subtype : WithGeneratingSeminorms Sf p →ₗ[ℂ] (X → ℂ)) ⊓
        ⨅ x : {x : X // x ∉ Z}, LinearMap.ker
          ((LinearMap.proj x.val).comp (Sf.subtype : WithGeneratingSeminorms Sf p →ₗ[ℂ] (X → ℂ))) :
        Submodule ℂ (WithGeneratingSeminorms Sf p)) ↔
      HasCompactSupport (f : Sf).val ∧ tsupport (f : Sf).val ⊆ Z := by
  refine Submodule.mem_inf.trans (and_congr (hT f) (Submodule.mem_iInf _ |>.trans
    ⟨fun h ↦ closure_minimal (fun x hx ↦ ?_) hZ, fun h x ↦ ?_⟩))
  · by_contra hxZ
    exact hx (LinearMap.mem_ker.mp (h ⟨x, hxZ⟩))
  · exact LinearMap.mem_ker.mpr
      (image_eq_zero_of_notMem_tsupport (f := (f : Sf).val) (x := x.val) fun hx ↦ x.2 (h hx))

-- The section-variable linter scans the large elaborated decay types and takes minutes.
set_option linter.unusedSectionVars false in
/-- Paper: §4.5.2, p. 205. For a closed module window, membership in the
fixed-support space is equivalent to the stated condition on topological support. -/
theorem mem_modulatedCompactSupportSubmodule_iff (hB : IsClosed B) (f : E) :
    f ∈ modulatedCompactSupportSubmodule m B ↔
      HasCompactSupport f.val ∧ tsupport f.val ⊆ m ⁻¹' B :=
  mem_comap_inf_iInf_ker_proj_iff (modulatedExponentialDecaySubmodule m Set.univ)
    (bruhatCompactSupportSubmodule G) _ (m ⁻¹' B) (hB.preimage m.continuous)
    (fun g ↦ ⟨fun h ↦ h.2, fun h ↦
      ⟨modulatedExponentialDecay_mem_bruhatSmooth m Set.univ Set.univ_nonempty g, h⟩⟩) f

/-- Paper: §4.5.2, p. 205. The fixed-support k-stage imposes k-invariance
on the supported decay space, with the topology inherited from the decay space. -/
def modulatedCompactSupportStage : Submodule ℂ E :=
  modulatedCompactSupportSubmodule m B ⊓ (schwartzBruhatInvariantSubmodule k).comap twist₀

/-- Paper: §4.5.2, p. 205. The stage consists of the supported functions
whose values are unchanged by translation by elements of k. -/
theorem mem_modulatedCompactSupportStage_iff (f : E) :
    f ∈ modulatedCompactSupportStage m B k ↔
      f ∈ modulatedCompactSupportSubmodule m B ∧
        ∀ (x : G) (u : k), f.val (u.val * x) = f.val x := by
  have htwist (x : G) : twist₀ f x = f.val x :=
    (modulatedExponentialDecayTwist_apply m Set.univ zeroUniv f x).trans
      ((congrArg (fun r : ℝ ↦ (r : ℂ) * f.val x) (Real.rpow_zero _)).trans
        ((congrArg (· * f.val x) Complex.ofReal_one).trans (one_mul _)))
  change f ∈ modulatedCompactSupportSubmodule m B ∧
    twist₀ f ∈ schwartzBruhatInvariantSubmodule k ↔ _
  refine and_congr_right fun _ ↦
    (mem_schwartzBruhatInvariantSubmodule_iff k (twist₀ f)).trans ?_
  exact forall_congr' fun x ↦ forall_congr' fun u ↦ iff_of_eq (congrArg₂ Eq
    ((htwist (x * u.val)).trans (congrArg f.val (mul_comm x u.val))) (htwist x))

variable (hk : IsCompact (k : Set G))
variable (hperp : IsCompactlyGeneratedGroup (lcaAnnihilator (k.comap m.toMonoidHom.ker.subtype)))
variable (hB : IsCompact B) (hBi : (interior B).Nonempty)

include hSC hm hms hk hperp hB hBi in
/-- Paper: Proposition 4.5.2.1(1), p. 205. The fixed-support k-stage is
a closed subspace of the two-sided decay space. -/
theorem modulatedCompactSupportStage_isClosed :
    IsClosed (modulatedCompactSupportStage m B k : Set E) := by
  let C := m ⁻¹' B
  have hC : IsCompact C := hm.1.isCompact_preimage hB
  have hev (x : G) : Continuous (fun f : E ↦ f.val x) := by
    refine (modulation_surjective_exists_section m hm hms).elim fun τ hτ ↦ ?_
    refine (modulatedExponentialDecay_continuous_inclusion m univ hm ordConnected_univ univ_nonempty
      τ hτ (mem_univ 0)).elim fun j hj ↦ ?_
    refine (schwartzBruhat_dirac_support x).elim fun e he ↦ ?_
    exact (e.continuous.comp j.continuous).congr fun f ↦ (he.1 (j f)).trans (hj.2 f x)
  let vanish : Set E := ⋂ x : {x : G // x ∉ C}, {f | f.val x = 0}
  let invariant : Set E := ⋂ x : G, ⋂ u : k, {f | f.val (u.val * x) = f.val x}
  have hV : IsClosed vanish := isClosed_iInter fun x ↦ isClosed_eq (hev x) continuous_const
  have hJ : IsClosed invariant := isClosed_iInter fun x ↦ isClosed_iInter fun u ↦
    isClosed_eq (hev (u.val * x)) (hev x)
  have hset : (modulatedCompactSupportStage m B k : Set E) = vanish ∩ invariant := by
    apply Set.ext
    intro f
    refine (mem_modulatedCompactSupportStage_iff m B k f).trans ?_
    have hs : tsupport f.val ⊆ C ↔ ∀ x ∉ C, f.val x = 0 :=
      hC.isClosed.closure_subset_iff.trans Function.support_subset_iff'
    have hv : f ∈ modulatedCompactSupportSubmodule m B ↔ f ∈ vanish := by
      refine (mem_modulatedCompactSupportSubmodule_iff m B hB.isClosed f).trans ?_
      constructor
      · intro h
        exact Set.mem_iInter.mpr fun x ↦ hs.mp h.2 _ x.property
      · intro h
        have hb := hs.mpr fun x hx ↦ Set.mem_iInter.mp h ⟨x, hx⟩
        exact ⟨hC.of_isClosed_subset (isClosed_tsupport _) hb, hb⟩
    exact and_congr hv ⟨fun h ↦ Set.mem_iInter.mpr fun x ↦ Set.mem_iInter.mpr (h x),
      fun h x ↦ Set.mem_iInter.mp (Set.mem_iInter.mp h x)⟩
  exact Eq.mpr (congrArg IsClosed hset) (hV.inter hJ)

include hSC hm hms hk hperp hB hBi in
/-- Paper: Proposition 4.5.2.1(1), p. 205. The inherited topology on the
supported k-stage agrees with the fixed-support test-function topology on G/k.
Deviation: The test space is represented by the elementary structural pair
with open subgroup G and compact subgroup k, using the fixed-support stage of §D.3.6. -/
theorem modulatedCompactSupportStage_testFunction_equiv :
    ∃ (p : BruhatStructuralPair G) (e : ElementaryLCAPresentation p.quotient)
      (C : TopologicalSpace.Compacts G)
      (F : bruhatCompactSupportStage p e C ≃L[ℂ] modulatedCompactSupportStage m B k),
      p.val.1 = ⊤ ∧ OrderDual.ofDual p.val.2 = k ∧ (C : Set G) = m ⁻¹' B ∧
      ∀ f, (F f).val.val = schwartzBruhatStageRealization p e f.val := by sorry

-- Remark 4.5.2.2, p. 207, uses the Fréchet topology of this elementary
-- stage. See also modulatedExponentialDecayStage_frechet and
-- modulatedExponentialDecay_stageLimit in §D.3.3.

variable (a b : ℝ≥0ˣ)
variable (ha : 1 < a.val) (hwidth : Real.log ((m γ).val : ℝ) < 2 * Real.log (a.val : ℝ))

local notation "window" => Icc (b / a) (b * a)
local notation "W" => modulatedCompactSupportStage m window k

include hSC hm hms hγ ha hwidth in
/-- Paper: Proposition 4.5.2.1(2), p. 205. A module window wider than one
logarithmic period maps onto the cyclic quotient. -/
theorem modulatedCompactSupport_quotient_image :
    q '' (m ⁻¹' window) = (univ : Set Q) := by
  have hpos (u : ℝ≥0ˣ) : 0 < ((u.val : ℝ≥0) : ℝ) := NNReal.coe_pos.mpr (Units.zero_lt u)
  have hle (u v : ℝ≥0ˣ) : u ≤ v ↔ Real.log (u.val : ℝ) ≤ Real.log (v.val : ℝ) := by
    rw [Real.log_le_log_iff (hpos u) (hpos v), NNReal.coe_le_coe, Units.val_le_val]
  have hdiv : Real.log ((b / a).val : ℝ) = Real.log (b.val : ℝ) - Real.log (a.val : ℝ) := by
    rw [Units.val_div_eq_div_val, NNReal.coe_div, Real.log_div (hpos b).ne' (hpos a).ne']
  have hmul : Real.log ((b * a).val : ℝ) = Real.log (b.val : ℝ) + Real.log (a.val : ℝ) := by
    rw [Units.val_mul, NNReal.coe_mul, Real.log_mul (hpos b).ne' (hpos a).ne']
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hγ)
  refine eq_univ_of_forall fun z ↦ ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  have hx (n : ℤ) : Real.log ((m (γ ^ n * x)).val : ℝ) =
      n * L + Real.log ((m x).val : ℝ) := by
    rw [map_mul m, map_zpow m, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
      NNReal.coe_zpow, Real.log_mul (zpow_ne_zero _ (hpos (m γ)).ne') (hpos (m x)).ne',
      Real.log_zpow]
  generalize ht : (Real.log (b.val : ℝ) - Real.log (a.val : ℝ) -
    Real.log ((m x).val : ℝ)) / L = t
  have htL : t * L = Real.log (b.val : ℝ) - Real.log (a.val : ℝ) -
      Real.log ((m x).val : ℝ) := by
    rw [← ht, div_mul_cancel₀ _ hL.ne']
  have h1 := mul_lt_mul_of_pos_right (Int.lt_floor_add_one t) hL
  have h2 := mul_le_mul_of_nonneg_right (Int.floor_le t) hL.le
  rw [add_one_mul] at h1
  refine ⟨γ ^ (⌊t⌋ + 1) * x, ⟨?_, ?_⟩, ?_⟩
  · rw [hle, hdiv, hx, Int.cast_add, Int.cast_one, add_one_mul]
    linarith
  · rw [hle, hmul, hx, Int.cast_add, Int.cast_one, add_one_mul]
    linarith
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.zpow_mem_zpowers γ _), one_mul]

include hγ hwidth in
/-- Paper: Proposition 4.5.2.1(2), pp. 205–206. The interior of a strict-width
window already meets every orbit. -/
theorem modulatedCompactSupport_quotient_image_interior :
    q '' (m ⁻¹' interior window) = (univ : Set Q) := by
  let v : ℝ≥0ˣ → ℝ := fun t ↦ ((t.val : ℝ≥0) : ℝ)
  have hv : Continuous v := NNReal.continuous_coe.comp Units.continuous_val
  have hvpos (t : ℝ≥0ˣ) : 0 < v t := NNReal.coe_pos.mpr (Units.zero_lt _)
  have hL : 0 < Real.log (v (m γ)) := Real.log_pos (by exact_mod_cast hγ)
  -- The open window lies in the interior of the closed one.
  have hsub : {t : ℝ≥0ˣ | v t ∈ Ioo (v (b / a)) (v (b * a))} ⊆ interior window := by
    refine interior_maximal (fun t ht ↦ ⟨?_, ?_⟩) (isOpen_Ioo.preimage hv)
    · exact Units.val_le_val.mp (NNReal.coe_le_coe.mp ht.1.le)
    · exact Units.val_le_val.mp (NNReal.coe_le_coe.mp ht.2.le)
  have hlo : Real.log (v (b / a)) = Real.log (v b) - Real.log (v a) := by
    simp only [v, Units.val_div_eq_div_val, NNReal.coe_div]
    exact Real.log_div (hvpos b).ne' (hvpos a).ne'
  have hhi : Real.log (v (b * a)) = Real.log (v b) + Real.log (v a) := by
    simp only [v, Units.val_mul, NNReal.coe_mul]
    exact Real.log_mul (hvpos b).ne' (hvpos a).ne'
  have hℓ (x : G) (n : ℤ) :
      Real.log (v (m (x * γ ^ n))) = Real.log (v (m x)) + n * Real.log (v (m γ)) := by
    simp only [v, map_mul, map_zpow, Units.val_mul, Units.val_zpow_eq_zpow_val, NNReal.coe_mul,
      NNReal.coe_zpow]
    rw [Real.log_mul (hvpos (m x)).ne' (zpow_pos (hvpos (m γ)) n).ne', Real.log_zpow]
  -- Every orbit meets the open window, since it is wider than one period.
  refine eq_univ_of_forall fun z ↦ ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective z
  set lγ := Real.log (v (m γ))
  set A₀ := Real.log (v b) - Real.log (v a)
  let n : ℤ := ⌊(A₀ - Real.log (v (m x))) / lγ⌋ + 1
  have hf := Int.floor_le ((A₀ - Real.log (v (m x))) / lγ)
  have hf' := Int.lt_floor_add_one ((A₀ - Real.log (v (m x))) / lγ)
  rw [le_div_iff₀ hL] at hf
  rw [div_lt_iff₀ hL] at hf'
  have hn : (n : ℝ) = ⌊(A₀ - Real.log (v (m x))) / lγ⌋ + 1 := by push_cast [n]; rfl
  have hw : lγ < 2 * Real.log (v a) := hwidth
  refine ⟨x * γ ^ n, hsub ?_, ?_⟩
  · change v (m (x * γ ^ n)) ∈ Ioo (v (b / a)) (v (b * a))
    constructor
    · rw [← Real.log_lt_log_iff (hvpos _) (hvpos _), hlo, hℓ, hn]
      nlinarith
    · rw [← Real.log_lt_log_iff (hvpos _) (hvpos _), hhi, hℓ, hn]
      nlinarith
  · exact QuotientGroup.mk_mul_of_mem x (Subgroup.zpow_mem_zpowers γ n)

include hk hperp ha hwidth in
/-- Paper: Proposition 4.5.2.1(2) and Equation (4.5.2.1), p. 205. On a window
wider than one period, the supported k-stage modulo the periodization kernel
is identified by periodization with the quotient test space on G/(γ^ℤ k). -/
theorem modulatedCompactSupportStage_periodization_equiv :
    let N := (P).ker.comap (W).subtype
    ∃ F : ((W) ⧸ N) ≃L[ℂ] SchwartzBruhat (G ⧸ (Γ ⊔ k)),
      ∀ (f : W) (x : G), F (N.mkQ f) (QuotientGroup.mk x) = P f.val (q x) := by sorry

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)

local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker
local notation "D[" B "]" => modulatedCompactSupportSubmodule m B

-- TODO(paper-gap): Equation (4.5.2.2) is false for arbitrary compact windows
-- with interior. Already G = ℝ_{>0}, χ = 1, B = [1, γ] misses the constant
-- periodization, since a smooth function supported there vanishes at both endpoints.

include hB in
/-- Paper: Theorem 4.5.2.3 and Equation (4.5.2.2), p. 207. The supported
homogeneous quotient is identified with the full quotient by inclusion.
Deviation: The interior of the compact module window must cover the quotient.
Every strict-width interval in part (2) satisfies this condition. -/
theorem modulatedCompactSupport_isotypicQuotient_equiv
    (hcover : (QuotientGroup.mk' (Subgroup.zpowers γ)) '' (m ⁻¹' interior B) =
      (univ : Set (G ⧸ Subgroup.zpowers γ)))
    (ω : PontryaginDual K) :
    let N := (Pχ[ω]).ker.comap (D[B]).subtype
    ∃ F : ((D[B]) ⧸ N) ≃L[ℂ] V[ω],
      ∀ f : D[B], F (N.mkQ f) = (Pχ[ω]).ker.mkQ f.val := by sorry

include hk hperp hB in
/-- Paper: Theorem 4.5.2.3 and Equation (4.5.2.2), p. 207. On a compact window
whose interior covers the quotient, inclusion identifies the two quotients of
k-invariant functions with their quotient topologies.
Deviation: Uses the interior coverage condition on the window. -/
theorem modulatedCompactSupportStage_isotypicQuotient_image
    (hcover : (QuotientGroup.mk' (Subgroup.zpowers γ)) '' (m ⁻¹' interior B) =
      (univ : Set (G ⧸ Subgroup.zpowers γ)))
    (ω : PontryaginDual K) :
    let J : Submodule ℂ E := (schwartzBruhatInvariantSubmodule k).comap twist₀
    let W₀ := modulatedCompactSupportStage m B k
    let i : W₀ →ₗ[ℂ] J := Submodule.inclusion (inf_le_right : W₀ ≤ J)
    let N := (Pχ[ω]).ker.comap W₀.subtype
    let N' := (Pχ[ω]).ker.comap J.subtype
    ∃ F : (W₀ ⧸ N) ≃L[ℂ] (J ⧸ N'), ∀ f : W₀, F (N.mkQ f) = N'.mkQ (i f) := by sorry

variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "bχ[" ω "]" => modulatedCyclicPairing m γ hm hms hγ μ₁ χ t₀ ht₀ ν ω

private theorem unconditionalBasis_int_of_nat {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] (N : Submodule ℂ X) (b : ℤ → StrongDual ℂ (X ⧸ N)) (σ : ℕ ≃ ℤ)
    (h : ∃ c : ℕ → StrongDual ℂ (StrongDual ℂ (X ⧸ N)), IsSchauderBasis (b ∘ σ) c ∧
      SchauderBasis.IsUnconditional (b ∘ σ) c) :
    ∃ d : ℤ → StrongDual ℂ (StrongDual ℂ (X ⧸ N)), (∀ i j, d i (b j) = if i = j then 1 else 0) ∧
      ∀ x, HasSum (fun n ↦ d n x • b n) x := by
  obtain ⟨c, hb, hu⟩ := h
  refine ⟨c ∘ σ.symm, fun i j ↦ ?_, fun x ↦ ?_⟩
  · have h : c (σ.symm i) (b (σ (σ.symm j))) =
        (if σ.symm i = σ.symm j then 1 else 0) := hb.1 _ _
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, Equiv.apply_eq_iff_eq] using h
  · apply σ.hasSum_iff.mp
    exact (hu x).congr_fun fun n ↦ congrArg (fun k ↦ c k x • b (σ n)) (σ.symm_apply_apply n)

include hχ hτ hμ hν in
/-- Paper: Theorem 4.5.2.3(1), p. 207. The lattice integrals indexed by
the integer frequencies give an unconditional basis of the strong dual of
the homogeneous kernel quotient. -/
theorem modulatedCyclicPairing_int_unconditionalBasis (ω : PontryaginDual K) :
    ∃ c : ℤ → StrongDual ℂ (StrongDual ℂ (V[ω])),
      (∀ m n, c m (bχ[ω] n) = if m = n then 1 else 0) ∧
      ∀ u, HasSum (fun n ↦ c n u • bχ[ω] n) u := by
  let σ := Equiv.intEquivNat.symm
  exact unconditionalBasis_int_of_nat (X := E) (Pχ[ω]).ker bχ[ω] σ
    (modulatedCyclicPairing_unconditionalBasis m γ hm hms hγ μ₁ χ t₀ ht₀ hχ ν τ hτ μ hμ hν ω σ)

include hχ hτ hμ hν hwidth in
/-- Paper: Theorem 4.5.2.3(2), pp. 207–208. Biorthogonal representatives can
be chosen with support in the wide module window. Their classes give an
absolute basis, and the induced integral functionals give an unconditional
basis of the strong dual of the supported quotient.
Deviation: The paper's integer family is expressed in an arbitrary enumeration,
as in Corollary 4.5.1.6. -/
theorem modulatedCompactSupport_isotypicQuotient_bases (ω : PontryaginDual K) (σ : ℕ ≃ ℤ) :
    let N := (Pχ[ω]).ker.comap (D[window]).subtype
    let U := (D[window]) ⧸ N
    ∃ (f : ℕ → D[window]) (c : ℕ → StrongDual ℂ U),
      (∀ n (g : D[window]), c n (N.mkQ g) = bχ[ω] (σ n) ((Pχ[ω]).ker.mkQ g.val)) ∧
      IsSchauderBasis (N.mkQ ∘ f) c ∧
      SchauderBasis.IsAbsolute (N.mkQ ∘ f) c ∧
      let d : ℕ → StrongDual ℂ (StrongDual ℂ U) :=
        fun n ↦ ContinuousLinearMap.applyₗ ℂ (RingHom.id ℂ) (N.mkQ (f n))
      IsSchauderBasis c d ∧ SchauderBasis.IsUnconditional c d := by sorry

end Support

/-! ## 4.5.3 Periodization for an open interval containing zero -/

section Interval

variable [MeasurableSpace G] [BorelSpace G]

local notation "S₀" => SchwartzBruhat G

include hγ in
/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208. Counting
measure on the discrete cyclic subgroup is regular Haar measure. -/
theorem modulatedCyclic_countingMeasure :
    (Measure.count : Measure Γ).IsHaarMeasure ∧ (Measure.count : Measure Γ).Regular := by
  have : DiscreteTopology Γ := modulated_zpowers_discrete m γ hγ
  exact ⟨count_isHaarMeasure_of_discreteTopology, count_regular_of_discreteTopology⟩

local notation "cosetPeriodization" => (fun f : S₀ ↦
  letI := (modulatedCyclic_countingMeasure m γ hγ).1
  letI := (modulatedCyclic_countingMeasure m γ hγ).2
  schwartzBruhatCosetIntegral Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ) f)

include hSC in
/-- Paper: Equation (4.5.3.2), p. 208. The coset integral of §D.1.7
with counting measure is linear and continuous on ordinary Schwartz–Bruhat functions. -/
theorem schwartzBruhatCyclicPeriodization_isLinearMap_continuous :
    IsLinearMap ℂ cosetPeriodization ∧ Continuous cosetPeriodization := by
  letI := (modulatedCyclic_countingMeasure m γ hγ).1
  letI := (modulatedCyclic_countingMeasure m γ hγ).2
  refine (schwartzBruhatCosetIntegral_continuousLinear Γ Measure.count
    (modulatedCyclicSubgroup_closed m γ hγ)).elim fun A hA ↦ ?_
  exact Eq.mp (congrArg (fun F : S₀ → S ↦ IsLinearMap ℂ F ∧ Continuous F) (funext hA))
    ⟨A.toLinearMap.isLinear, A.continuous⟩

/-- Paper: Equation (4.5.3.2), p. 208. Ordinary Schwartz–Bruhat periodization
is the coset integral with respect to counting measure on the cyclic subgroup. -/
def schwartzBruhatCyclicPeriodization : S₀ →L[ℂ] S :=
  let h := schwartzBruhatCyclicPeriodization_isLinearMap_continuous m γ hγ
  ⟨IsLinearMap.mk' cosetPeriodization h.1, h.2⟩

local notation "P₀" => schwartzBruhatCyclicPeriodization m γ hγ

/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208. At any lift of
a quotient point the cyclic sum converges to the coset integral. -/
theorem schwartzBruhatCyclicPeriodization_hasSum (f : S₀) (x : G) :
    HasSum (fun n : ℤ ↦ f (γ ^ n * x)) (P₀ f (q x)) := by
  let := (modulatedCyclic_countingMeasure m γ hγ).1
  let := (modulatedCyclic_countingMeasure m γ hγ).2
  exact cyclicCosetIntegral_hasSum m γ hγ f x

/-- Paper: Corollary 4.5.3.1, p. 208. The ordinary Schwartz–Bruhat
periodization is surjective. -/
theorem schwartzBruhatCyclicPeriodization_surjective : Surjective P₀ := by
  let := (modulatedCyclic_countingMeasure m γ hγ).1
  let := (modulatedCyclic_countingMeasure m γ hγ).2
  exact schwartzBruhatCosetIntegral_surjective Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ)

/-- Paper: Corollary 4.5.3.1, p. 208. The ordinary Schwartz–Bruhat
periodization is open. -/
theorem schwartzBruhatCyclicPeriodization_isOpenMap : IsOpenMap P₀ := by
  let := (modulatedCyclic_countingMeasure m γ hγ).1
  let := (modulatedCyclic_countingMeasure m γ hγ).2
  have hq : IsQuotientMap (P₀).toLinearMap.toAddMonoidHom :=
    schwartzBruhatCosetIntegral_isQuotientMap Γ Measure.count (modulatedCyclicSubgroup_closed m γ hγ)
  exact (AddMonoidHom.isOpenQuotientMap_of_isQuotientMap hq).isOpenMap

variable (I : Set ℝ) (hOpen : IsOpen I) (hInt : OrdConnected I) (h0 : 0 ∈ I)

local notation "D" => ModulatedExponentialDecay m I
local notation "zeroI" => (⟨0, h0⟩ : I)
local notation "j₀" => modulatedExponentialDecayTwist m I zeroI
local notation "ΔI" => modulatedCyclicDifference m γ hm hms I hInt (⟨0, h0⟩ : I.Nonempty)

include hSC hm hms hInt in
/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208.
At exponent zero the canonical inclusion into ordinary Schwartz–Bruhat
functions is continuous. -/
theorem modulatedExponentialDecay_zeroTwist_continuous :
    Continuous (fun f : D ↦ (j₀ f : S₀)) := by
  refine (modulation_surjective_exists_section m hm hms).elim fun τ hτ ↦ ?_
  exact (continuous_apply (A := fun _ : I ↦ S₀) zeroI).comp
    (modulatedExponentialDecay_twists_continuous m I hm hInt ⟨0, h0⟩ τ hτ)

/-- Paper: Corollary 4.5.3.1 and Equation (4.5.3.2), p. 208.
The zero twist preserves pointwise values and is the injective inclusion
of the interval decay space into ordinary Schwartz–Bruhat functions. -/
theorem modulatedExponentialDecay_zeroTwist_injective :
    Injective j₀ ∧ ∀ (f : D) (x : G), j₀ f x = f.val x := by
  have h (f : D) (x : G) : j₀ f x = f.val x := by
    exact (modulatedExponentialDecayTwist_apply m I zeroI f x).trans (by simp)
  refine ⟨fun f g hfg ↦ Subtype.ext (funext fun x ↦ ?_), h⟩
  exact (h f x).symm.trans ((congrArg (fun u : S₀ ↦ u x) hfg).trans (h g x))

/-- Paper: Equation (4.5.3.1), p. 208. Periodization at an interval containing
zero composes the zero twist with ordinary Schwartz–Bruhat periodization. -/
def modulatedIntervalPeriodization : D →L[ℂ] S :=
  let j : D →L[ℂ] S₀ :=
    ⟨j₀, modulatedExponentialDecay_zeroTwist_continuous m hm hms I hInt h0⟩
  (P₀).comp j

local notation "PI" => modulatedIntervalPeriodization m γ hm hms hγ I hInt h0

/-- Paper: Equation (4.5.3.1), p. 208. At a lift of a quotient point the
orbit series for an interval-decaying function converges to its periodization. -/
theorem modulatedIntervalPeriodization_hasSum (f : D) (x : G) :
    HasSum (fun n : ℤ ↦ f.val (γ ^ n * x)) (PI f (q x)) := by
  exact (schwartzBruhatCyclicPeriodization_hasSum m γ hγ (j₀ f) x).congr_fun
    fun n ↦ ((modulatedExponentialDecay_zeroTwist_injective m I h0).2 f (γ ^ n * x)).symm

private theorem fullDecay_to_interval_periodization :
    ∃ i : E →L[ℂ] D, (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      ∀ f, PI (i f) = P f := by
  let incl {A : Type _} [CommGroup A] [TopologicalSpace A] (n : A →ₜ* ℝ≥0ˣ) :
      modulatedExponentialDecaySubmodule n univ →ₗ[ℂ] modulatedExponentialDecaySubmodule n I :=
    Submodule.inclusion fun _ hf ↦ (Submodule.mem_iInf _).mpr fun b ↦
      (Submodule.mem_iInf _).mp hf (⟨b.val, mem_univ _⟩ : (univ : Set ℝ))
  let Good := {k : Subgroup G // IsCompact (k : Set G) ∧
    IsCompactlyGeneratedGroup (lcaAnnihilator k)}
  let finalSeminorms (J : Set ℝ) := {p : Seminorm ℂ (modulatedExponentialDecaySubmodule m J) //
    ∀ k : Good, Continuous (p ∘ modulatedExponentialDecayStageInclusion m J k)}
  let gen (J : Set ℝ) := withGeneratingSeminorms_spec _ (Subtype.val : finalSeminorms J → _)
  let F : E →ₗ[ℂ] D := incl m
  have hc : Continuous F := by
    apply (gen I).continuous_of_continuous_comp F
    intro p
    let v : Seminorm ℂ E := p.val.comp F
    apply (gen univ).continuous_seminorm (⟨v, ?_⟩ : finalSeminorms univ)
    intro k
    let n := quotientModulation m k.val k.property.1
    let Y (J : Set ℝ) := ModulatedExponentialDecayStage m J k
    let stageGen (J : Set ℝ) := withGeneratingSeminorms_spec _
      (fun i : J × {p : Seminorm ℂ (SchwartzBruhat (G ⧸ k.val)) // Continuous p} ↦
        i.2.val.comp (modulatedExponentialDecayTwist n J i.1))
    let Fk : Y univ →ₗ[ℂ] Y I := incl n
    have hj : Continuous Fk := by
      apply (stageGen I).continuous_of_continuous_comp Fk
      intro a
      exact (stageGen univ).continuous_seminorm (⟨a.1.val, mem_univ _⟩, a.2)
    exact (p.property k).comp hj
  let i : E →L[ℂ] D := ⟨F, hc⟩
  have comm (f : E) : PI (i f) = P f := by
    refine Subtype.ext (funext fun z ↦ ?_)
    refine QuotientGroup.induction_on z fun x ↦ ?_
    have h₁ := modulatedIntervalPeriodization_hasSum m γ hm hms hγ I hInt h0 (i f) x
    have h₂ := modulatedPeriodization_hasSum m γ hm hms hγ f x
    exact h₁.unique h₂
  exact ⟨i, fun _ _ ↦ rfl, comm⟩

private theorem intervalPeriodization_isQuotientMap : IsQuotientMap PI := by
  refine (fullDecay_to_interval_periodization m γ hm hms hγ I hInt h0).elim fun i hi ↦ ?_
  have hcomp : (PI) ∘ i = P := funext hi.2
  have hopen := (modulatedPeriodization_isOpenMap m γ hm hms hγ).isQuotientMap
    (P).continuous (modulatedPeriodization_surjective m γ hm hms hγ)
  exact IsQuotientMap.of_comp i.continuous (PI).continuous (Eq.mpr (congrArg IsQuotientMap hcomp) hopen)

include hOpen in
/-- Paper: Corollary 4.5.3.1 and Equations (4.5.3.1)–(4.5.3.2), p. 208.
The periodization is surjective, uniquely characterized by the diagram,
and extends two-sided exponential periodization along the canonical inclusion. -/
theorem modulatedIntervalPeriodization_factorization :
    ∃ i : E →L[ℂ] D,
      (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      (∀ f, PI (i f) = P f) ∧
      Surjective PI ∧
      ∀ T : D →L[ℂ] S, T.comp i = P → T = PI := by
  refine (fullDecay_to_interval_periodization m γ hm hms hγ I hInt h0).elim fun i hi ↦ ?_
  have comm := hi.2
  refine ⟨i, hi.1, comm, fun y ↦ ?_, fun T hT ↦ ?_⟩
  · exact (modulatedPeriodization_surjective m γ hm hms hγ y).elim fun f hf ↦ ⟨i f, (comm f).trans hf⟩
  · let := modulatedCyclicSubgroup_closed m γ hγ
    let : T2Space S := schwartzBruhat_t2
    have hd := bruhatCompactSupport_dense_modulatedExponentialDecay m I hm hms hInt ⟨0, h0⟩
    apply DFunLike.coe_injective
    apply hd.equalizer T.continuous (PI).continuous
    funext f
    let g := bruhatCompactSupportToModulatedExponentialDecay m univ hm hms f
    have hg : i g = bruhatCompactSupportToModulatedExponentialDecay m I hm hms f :=
      Subtype.ext (funext (hi.1 g))
    have heq := (DFunLike.congr_fun hT g).trans (comm g).symm
    exact (congrArg T hg).symm.trans (heq.trans (congrArg (PI) hg))

section ProjectivePeriodization

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

open UniformSpace
open scoped TensorProduct

section TensorFlip

attribute [local instance] uniformContinuousConstSMul_of_continuousConstSMul

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X] [TopologicalSpace X]
  [PolynormableSpace ℂ X] [T2Space X] [AddCommGroup Y] [Module ℂ Y]
  [TopologicalSpace Y] [PolynormableSpace ℂ Y] [T2Space Y]

private def inductiveTensorFlip : InductiveTensor X Y →L[ℂ] InductiveTensor Y X := by
  let F₀ : InductiveTensor X Y →ₗ[ℂ] InductiveTensor Y X := (TensorProduct.comm ℂ X Y).toLinearMap
  have h := (continuous_inductiveTensor_iff
    (LinearMap.id : InductiveTensor Y X →ₗ[ℂ] InductiveTensor Y X)).mp continuous_id
  have hc := @continuous_inductiveTensor_iff X Y _ _ _ _ _ _ _ _ _ _ (InductiveTensor Y X) _ _
    (inferInstanceAs (TopologicalSpace (InductiveTensor Y X)))
    (inferInstanceAs (PolynormableSpace ℂ (InductiveTensor Y X))) (inferInstanceAs (T2Space (InductiveTensor Y X))) F₀
  exact ⟨F₀, hc.mpr (⟨h.2, h.1⟩)⟩

private def projectiveTensorFlip : ProjectiveTensor X Y →L[ℂ] ProjectiveTensor Y X := by
  let F₀ : ProjectiveTensor X Y →ₗ[ℂ] ProjectiveTensor Y X := (TensorProduct.comm ℂ X Y).toLinearMap
  have h := (continuous_projectiveTensor_iff
    (LinearMap.id : ProjectiveTensor Y X →ₗ[ℂ] ProjectiveTensor Y X)).mp continuous_id
  have hc := @continuous_projectiveTensor_iff X Y _ _ _ _ _ _ _ _ _ _ (ProjectiveTensor Y X) _ _
    (inferInstanceAs (TopologicalSpace (ProjectiveTensor Y X)))
    (inferInstanceAs (PolynormableSpace ℂ (ProjectiveTensor Y X))) F₀
  exact ⟨F₀, hc.mpr (h.comp continuous_swap)⟩

private def inductiveProjectiveComparison : InductiveTensor X Y →L[ℂ] ProjectiveTensor X Y :=
  ⟨LinearMap.id, continuous_inductiveTensor_to_projectiveTensor⟩

private theorem completion_tensor_flip_comparison
    (h : ∃ C : Completion (InductiveTensor Y X) →L[ℂ] Completion (ProjectiveTensor Y X),
      (C : _ → _) = @Completion.map (InductiveTensor Y X) _ (ProjectiveTensor Y X) _ id ∧
      Bijective C ∧ ∀ B, IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B) :
    ∃ C : Completion (InductiveTensor X Y) →L[ℂ] Completion (ProjectiveTensor X Y),
      (C : _ → _) = @Completion.map (InductiveTensor X Y) _ (ProjectiveTensor X Y) _ id ∧
      Bijective C ∧ ∀ B, IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B := by
  let ci := (inductiveProjectiveComparison (X := X) (Y := Y)).completion
  let cr := (inductiveProjectiveComparison (X := Y) (Y := X)).completion
  let i₀ := inductiveTensorFlip (X := X) (Y := Y)
  let i₁ := inductiveTensorFlip (X := Y) (Y := X)
  let p₀ := projectiveTensorFlip (X := X) (Y := Y)
  let p₁ := projectiveTensorFlip (X := Y) (Y := X)
  have hI (z) : i₁.completion (i₀.completion z) = z := by
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (i₁.completion.continuous.comp i₀.completion.continuous) continuous_id
    | ih x => simp only [ContinuousLinearMap.completion_apply_coe]
              exact congrArg (fun v : InductiveTensor X Y ↦ (v : Completion (InductiveTensor X Y)))
                ((TensorProduct.comm ℂ X Y).symm_apply_apply x)
  have hP (z) : p₁.completion (p₀.completion z) = z := by
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (p₁.completion.continuous.comp p₀.completion.continuous) continuous_id
    | ih x => simp only [ContinuousLinearMap.completion_apply_coe]
              exact congrArg (fun v : ProjectiveTensor X Y ↦ (v : Completion (ProjectiveTensor X Y)))
                ((TensorProduct.comm ℂ X Y).symm_apply_apply x)
  obtain ⟨C, hc, hj, hb⟩ := h
  have eqC (z) : C z = cr z := congrFun hc z
  have comm₀ (z) : p₀.completion (ci z) = C (i₀.completion z) := by
    rw [eqC]
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (p₀.completion.continuous.comp ci.continuous) (cr.continuous.comp i₀.completion.continuous)
    | ih x => simp only [ci, cr, ContinuousLinearMap.completion_apply_coe]; rfl
  have comm₁ (z) : p₁.completion (C z) = ci (i₁.completion z) := by
    rw [eqC]
    induction z using Completion.induction_on with
    | hp => exact isClosed_eq (p₁.completion.continuous.comp cr.continuous) (ci.continuous.comp i₁.completion.continuous)
    | ih x => simp only [ci, cr, ContinuousLinearMap.completion_apply_coe]; rfl
  refine ⟨ci, rfl, ⟨?_, ?_⟩, fun B ↦ ⟨?_, fun hh ↦ hh.image ci⟩⟩
  · intro x y hxy
    have he := hj.1 ((comm₀ x).symm.trans ((congrArg p₀.completion hxy).trans (comm₀ y)))
    exact (hI x).symm.trans ((congrArg i₁.completion he).trans (hI y))
  · intro y
    obtain ⟨x, hx⟩ := hj.2 (p₀.completion y)
    exact ⟨i₁.completion x, (comm₁ x).symm.trans ((congrArg p₁.completion hx).trans (hP y))⟩
  · intro hh
    have hem : C '' (i₀.completion '' B) = p₀.completion '' (ci '' B) := by
      rw [image_image, image_image]
      exact congrArg (fun f ↦ f '' B) (funext fun z ↦ (comm₀ z).symm)
    have h₁ := (hb _).mp (hem ▸ hh.image p₀.completion)
    have hel : i₁.completion '' (i₀.completion '' B) = B := by
      rw [image_image, show (fun z ↦ i₁.completion (i₀.completion z)) = id from funext hI, image_id]
    exact Eq.mp (congrArg (IsVonNBounded ℂ) hel) (h₁.image i₁.completion)

end TensorFlip

private theorem periodization_on_bounded_comparison {X Y W Z : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [ContinuousSMul ℂ X] [T2Space X] [MontelSpace ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    [AddCommGroup W] [Module ℂ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
    [ContinuousSMul ℂ W] [T2Space W] [AddCommGroup Z] [Module ℂ Z] [TopologicalSpace Z]
    (U : Y ≃L[ℂ] X) (J : Y → W)
    (hJ : ∃ C : Y →L[ℂ] W, (C : Y → W) = J ∧ Bijective C ∧
      ∀ B, IsVonNBounded ℂ (C '' B) ↔ IsVonNBounded ℂ B)
    (F : X →L[ℂ] Z) (hF : IsQuotientMap F) :
    ∃ A : W →ₗ[ℂ] Z, SeqContinuous A ∧ Surjective A ∧ (∀ y, A (J y) = F (U y)) ∧
      ∃ B : Z ≃ₗ[ℂ] (W ⧸ A.ker), SeqContinuous B ∧ ∀ w, B (A w) = A.ker.mkQ w := by
  obtain ⟨C, hJC, hC, hb⟩ := hJ
  let C₀ := C.comp U.symm.toContinuousLinearMap
  let c := LinearEquiv.ofBijective C₀.toLinearMap (hC.comp U.symm.bijective)
  have hbound (B : Set X) (hh : IsVonNBounded ℂ (c '' B)) : IsVonNBounded ℂ B := by
    have h₁ : C '' (U.symm '' B) = c '' B := image_image _ _ _
    have h₂ := (hb _).mp (Eq.mpr (congrArg (IsVonNBounded ℂ) h₁) hh)
    exact Eq.mp (congrArg (IsVonNBounded ℂ) (U.image_symm_image B)) (h₂.image U.toContinuousLinearMap)
  have hs := seqContinuous_symm_of_bounded_comparison c C₀.continuous hbound
  obtain ⟨A, hA, hsur, hf, hinv⟩ := quotient_of_sequential_comparison c C₀.continuous hs F hF
  refine ⟨A, hA, hsur, fun y ↦ ?_, hinv⟩
  have hc : c (U y) = C y := congrArg C (U.symm_apply_apply y)
  exact (congrArg A (hc.trans (congrFun hJC y))).symm.trans (hf _)

open UniformSpace in
open scoped TensorProduct in
/-- Paper: Remarks 4.5.1.2 and 4.5.1.4, pp. 198, 203. Periodization on the
projective tensor completion is sequentially continuous and surjective. The
induced bijection has a sequentially continuous inverse.
Deviation: The interval contains zero. The tensor factors are ordered as in
modulatedExponentialDecay_tensor_equiv. General forward continuity fails. -/
theorem modulatedIntervalPeriodization_projective
    (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
    (e : Completion (InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)) ≃L[ℂ] D)
    (he : ∀ (h : SchwartzBruhat K) (p : PositiveRealExponentialDecay I) (u : K) (t : ℝ≥0ˣ),
      (e (Completion.coe' (α := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I))
        (h ⊗ₜ[ℂ] p))).val (u.val * τ t) = h u * p.val (Real.log (t.val : ℝ))) :
    let TI := InductiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
    let TP := ProjectiveTensor (SchwartzBruhat K) (PositiveRealExponentialDecay I)
    ∃ A : Completion TP →ₗ[ℂ] S, SeqContinuous A ∧ Surjective A ∧
      (∀ z : Completion TI, A (@Completion.map TI _ TP _ id z) = PI (e z)) ∧
      ∃ B : S ≃ₗ[ℂ] ((Completion TP) ⧸ A.ker),
        SeqContinuous B ∧ ∀ z, B (A z) = A.ker.mkQ z := by
  intro TI TP
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  let : T2Space (SchwartzBruhat K) := schwartzBruhat_t2
  let : T2Space (PositiveRealExponentialDecay I) := (positiveRealExponentialDecay_isEmbedding I ⟨0, h0⟩).t2Space
  have hstrict := modulatedExponentialDecay_strictLF m I hm hInt ⟨0, h0⟩ τ hτ
  let : T2Space D := hstrict.1
  let : MontelSpace ℂ D := (modulatedExponentialDecay_montel m I hm hInt ⟨0, h0⟩ τ hτ).2
  have hq := intervalPeriodization_isQuotientMap m γ hm hms hγ I hInt h0
  have hrev := modulatedExponentialDecay_tensor_comparison_bounded m I hm hInt ⟨0, h0⟩ τ hτ
  have hcomp := completion_tensor_flip_comparison (X := SchwartzBruhat K) (Y := PositiveRealExponentialDecay I) hrev
  let : PolynormableSpace ℂ (Completion TP) := polynormableSpace_completion
  let : ContinuousSMul ℂ (Completion TP) := PolynormableSpace.continuousSMul ℂ _
  have ha := periodization_on_bounded_comparison (X := D) (Y := Completion TI) (W := Completion TP) (Z := S)
    e (@Completion.map TI _
      TP _ id) hcomp PI hq
  with_reducible exact ha

end ProjectivePeriodization

-- TODO(paper-gap): Remark 4.5.1.4, p. 203, calls the forward quotient
-- bijection continuous. For an infinite product of copies of ℤ/2, the
-- quotient Schwartz space admits a continuous seminorm testing derivative
-- order j at the jth coordinate character. On a fixed compact set no single
-- continuous radial seminorm controls all those derivative orders.

-- TODO(paper-gap): In (4.5.3.6) the ordinary Schwartz–Bruhat quotient map
-- has the interval decay space printed in its codomain. On p. 208 the
-- proof uses the equality of the difference image with the pulled-back
-- closed range before justifying it.

include hOpen in
/-- Paper: Corollary 4.5.3.1(1), p. 208. On the interval decay space the
periodization kernel is exactly the range of the cyclic difference. -/
theorem modulatedIntervalPeriodization_ker_eq_range :
    (PI).ker = (ΔI).range := by sorry

private theorem fullPeriodization_ker_eq_range : (P).ker = (Δ).range := by
  let Pu := modulatedIntervalPeriodization m γ hm hms hγ univ ordConnected_univ (mem_univ 0)
  have h (f : E) (x : G) : P f (q x) = Pu f (q x) :=
    (modulatedPeriodization_hasSum m γ hm hms hγ f x).unique
      (modulatedIntervalPeriodization_hasSum m γ hm hms hγ univ ordConnected_univ (mem_univ 0) f x)
  have hs (f : E) : P f = Pu f :=
    Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (h f))
  have hr := modulatedIntervalPeriodization_ker_eq_range m γ hm hms hγ univ isOpen_univ ordConnected_univ (mem_univ 0)
  refine SetLike.ext fun f ↦ ?_
  have hmemb := Iff.of_eq (congrArg (fun N : Submodule ℂ E ↦ f ∈ N) hr)
  have hzero : (P f = 0) ↔ (Pu f = 0) := Iff.of_eq (congrArg (· = 0) (hs f))
  exact hzero.trans hmemb

omit [MeasurableSpace G] [BorelSpace G] in
/-- Paper: Proposition 4.5.1.1(5), p. 198. The ordinary periodization kernel
is the closure of the image of the cyclic difference. -/
theorem modulatedPeriodization_ker_eq_closure :
    (P).ker = (Δ).range.topologicalClosure := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  have h := fullPeriodization_ker_eq_range m γ hm hms hγ
  exact (IsClosed.submodule_topologicalClosure_eq (s := (P).ker) (P).isClosed_ker).symm.trans
    (congrArg Submodule.topologicalClosure h)

private theorem fullPeriodization_inter_isotype (ω : PontryaginDual K) :
    (P).ker ⊓ H[ω] = (H[ω]).map (Δ).toLinearMap := by
  have h₀ := fullPeriodization_ker_eq_range m γ hm hms hγ
  exact (congrArg (fun N : Submodule ℂ E ↦ N ⊓ H[ω]) h₀).trans
    (modulatedCyclicDifference_range_isotype m γ hm hms ω)

private theorem cyclicDifference_homogeneous_iff {A : Type*} [CommGroup A] (γ : A) (f : A → ℂ)
    (hs : ∀ x, Summable fun n : ℤ ↦ f (γ ^ n * x)) (k : A) (c : ℂ) :
    (∀ x, f (k * x) - f (γ * (k * x)) = c * (f x - f (γ * x))) ↔
      ∀ x, f (k * x) = c * f x := by
  let d (x : A) := f (k * x) - c * f x
  constructor
  · intro h x
    have hinv (z : A) : d (γ * z) = d z := by
      dsimp only [d]
      rw [mul_left_comm k γ]
      linear_combination -(h z)
    have hconst (n : ℕ) : d (γ ^ n * x) = d x := by
      induction n with
      | zero => simp
      | succ n ih => rwa [pow_succ', mul_assoc, hinv]
    have ht (z : A) : Summable (fun n : ℕ ↦ f (γ ^ n * z)) := by
      simpa only [Function.comp_def, zpow_natCast] using (hs z).comp_injective (Nat.cast_injective (R := ℤ))
    have hd : Summable (fun n : ℕ ↦ d (γ ^ n * x)) := by
      simpa only [d, mul_left_comm k] using (ht (k * x)).sub ((ht x).mul_left c)
    exact sub_eq_zero.mp ((summable_const_iff (β := ℕ) (d x)).mp (hd.congr hconst))
  · intro h x
    rw [h x, mul_left_comm γ k, h, mul_sub]

include hOpen in
/-- Paper: Corollary 4.5.3.1(1), pp. 208–209. The difference range in the
interval decay space is closed and restricts to the difference range on each isotype. -/
theorem modulatedIntervalDifference_range_isotype (ω : PontryaginDual K) :
    let H := (actionIsotype ((ρG).comp (K).subtype) ω).comap j₀
    (PI).ker ⊓ H = H.map (ΔI).toLinearMap := by
  intro H
  have val₀ := (modulatedExponentialDecay_zeroTwist_injective m I h0).2
  let homogeneous (g : G → ℂ) :=
    ∀ (u : K) (x : G), g (u.val⁻¹ * x) = (ω u : ℂ) * g x
  have hmem (f : D) : f ∈ H ↔ homogeneous f.val :=
    (mem_schwartzTranslationIsotype_iff m ω (j₀ f)).trans
      (Iff.of_eq (congrArg homogeneous (funext (val₀ f))))
  have iff_diff (f : D) : ΔI f ∈ H ↔ f ∈ H := by
    have hd : (ΔI f).val = fun x ↦ f.val x - f.val (γ * x) :=
      funext (modulatedCyclicDifference_apply m γ hm hms I hInt ⟨0, h0⟩ f)
    refine (hmem _).trans ((Iff.of_eq (congrArg homogeneous hd)).trans (Iff.trans ?_ (hmem f).symm))
    exact forall_congr' fun u ↦ cyclicDifference_homogeneous_iff γ f.val (fun x ↦
      (modulatedIntervalPeriodization_hasSum m γ hm hms hγ I hInt h0 f x).summable) u.val⁻¹ (ω u)
  have hpre : H.comap (ΔI).toLinearMap = H := Submodule.ext iff_diff
  exact (congrArg (· ⊓ H) (modulatedIntervalPeriodization_ker_eq_range m γ hm hms hγ I hOpen hInt h0)).trans
    ((Submodule.map_comap_eq (ΔI).toLinearMap H).symm.trans (congrArg (Submodule.map (ΔI).toLinearMap) hpre))

/-- Paper: Equation (4.5.3.3), p. 208. The cyclic difference on the ordinary
Schwartz–Bruhat space subtracts left translation by the inverse generator. -/
def schwartzBruhatCyclicDifference : S₀ →L[ℂ] S₀ :=
  ContinuousLinearMap.id ℂ S₀ - ρG γ⁻¹

local notation "Δ₀" => schwartzBruhatCyclicDifference γ

/-- Paper: Equation (4.5.3.3), p. 208. The ordinary cyclic difference at x
subtracts the function's value at γx. -/
theorem schwartzBruhatCyclicDifference_apply (f : S₀) (x : G) :
    Δ₀ f x = f x - f (γ * x) := by
  change f x - ρG γ⁻¹ f x = _
  rw [schwartzBruhatTranslationAction_apply, inv_inv]

include hm hms in
/-- Paper: Corollary 4.5.3.1(2), pp. 208–209. On ordinary Schwartz–Bruhat
functions the periodization kernel is exactly the range of the cyclic difference. -/
theorem schwartzBruhatCyclicPeriodization_ker_eq_range :
    (P₀).ker = (Δ₀).range := by sorry

include hm hms in
/-- Paper: Corollary 4.5.3.1(2), pp. 208–209. On each ordinary
Schwartz–Bruhat isotype the kernel consists of differences of functions of that isotype. -/
theorem schwartzBruhatCyclicDifference_range_isotype (ω : PontryaginDual K) :
    let H := actionIsotype ((ρG).comp (K).subtype) ω
    (P₀).ker ⊓ H = H.map (Δ₀).toLinearMap := by
  intro H
  have hpre : H.comap (Δ₀).toLinearMap = H := by
    apply Submodule.ext
    intro f
    refine (mem_schwartzTranslationIsotype_iff m ω (Δ₀ f)).trans (Iff.trans ?_
      (mem_schwartzTranslationIsotype_iff m ω f).symm)
    simp only [schwartzBruhatCyclicDifference_apply]
    exact forall_congr' fun u ↦ cyclicDifference_homogeneous_iff γ f.val (fun x ↦
      (schwartzBruhatCyclicPeriodization_hasSum m γ hγ f x).summable) u.val⁻¹ (ω u)
  exact (congrArg (· ⊓ H) (schwartzBruhatCyclicPeriodization_ker_eq_range m γ hm hms hγ)).trans
    ((Submodule.map_comap_eq (Δ₀).toLinearMap H).symm.trans (congrArg (Submodule.map (Δ₀).toLinearMap) hpre))

include hOpen hγ in
/-- Paper: Corollary 4.5.3.1, (4.5.3.4)–(4.5.3.6), pp. 208–209. The two
inclusions identify the quotients by the three difference ranges, as used
in Corollary 4.6.3.1. Both maps send each function to its own class. -/
theorem modulatedIntervalDifference_quotient_equivs :
    ∃ (i : E →L[ℂ] D)
      (F : (E ⧸ (Δ).range) ≃L[ℂ] (D ⧸ (ΔI).range))
      (J : (D ⧸ (ΔI).range) ≃L[ℂ] (S₀ ⧸ (Δ₀).range)),
      (∀ (f : E) (x : G), (i f).val x = f.val x) ∧
      (∀ f : E, F ((Δ).range.mkQ f) = (ΔI).range.mkQ (i f)) ∧
      ∀ g : D, J ((ΔI).range.mkQ g) = (Δ₀).range.mkQ (j₀ g) := by
  refine (modulatedIntervalPeriodization_factorization m γ hm hms hγ I hOpen hInt h0).elim fun i h ↦ ?_
  have hi := h.1
  have hcomp := h.2.1
  have hP : IsQuotientMap P := (modulatedPeriodization_isOpenMap m γ hm hms hγ).isQuotientMap
    (P).continuous (modulatedPeriodization_surjective m γ hm hms hγ)
  have hPI : IsQuotientMap PI := by
    apply IsQuotientMap.of_comp i.continuous (PI).continuous
    exact Eq.mpr (congrArg IsQuotientMap (funext hcomp)) hP
  have hP₀ := (schwartzBruhatCyclicPeriodization_isOpenMap m γ hγ).isQuotientMap
    (P₀).continuous (schwartzBruhatCyclicPeriodization_surjective m γ hγ)
  have hN := fullPeriodization_ker_eq_range m γ hm hms hγ
  refine (exists_quotient_equiv_of_kernel P hP _ hN).elim fun A hA ↦ ?_
  refine (exists_quotient_equiv_of_kernel PI hPI _
    (modulatedIntervalPeriodization_ker_eq_range m γ hm hms hγ I hOpen hInt h0)).elim fun B hB ↦ ?_
  refine (exists_quotient_equiv_of_kernel P₀ hP₀ _
    (schwartzBruhatCyclicPeriodization_ker_eq_range m γ hm hms hγ)).elim fun C hC ↦ ?_
  refine ⟨i, A.trans B.symm, B.trans C.symm, hi, fun f ↦ ?_, fun g ↦ ?_⟩
  · exact B.symm_apply_eq.mpr ((hA f).trans ((hcomp f).symm.trans (hB (i f)).symm))
  · exact C.symm_apply_eq.mpr ((hB g).trans (hC (j₀ g)).symm)

end Interval

section IsotypicKernel

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure] (χ : PontryaginDual G)

local notation "ωχ" => PontryaginDual.map
  (⟨(K).subtype, continuous_subtype_val⟩ : K →ₜ* G) χ
local notation "Pχ" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ χ

private theorem comap_ker_eq_comap_closure {X Y : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] [IsTopologicalAddGroup X] [ContinuousConstSMul ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y] [T2Space Y]
    (F T : X →L[ℂ] Y) (H N : Submodule ℂ X) (hH : IsClosed (H : Set X))
    (hN : T.ker ⊓ H = N) (c : ℂ) (hc : c ≠ 0) (h : ∀ x : H, F x = c • T x) :
    F.ker.comap H.subtype = N.topologicalClosure.comap H.subtype := by
  have hclosed : (T.ker ⊓ H).topologicalClosure = T.ker ⊓ H :=
    IsClosed.submodule_topologicalClosure_eq (s := T.ker ⊓ H) (T.isClosed_ker.inter hH)
  have hcl := (congrArg Submodule.topologicalClosure hN.symm).trans hclosed
  refine SetLike.ext fun x ↦ ?_
  have hzero : (F x = 0) ↔ (T x = 0) := (Iff.of_eq (congrArg (· = 0) (h x))).trans
    (smul_eq_zero_iff_right hc)
  have hmem := Iff.of_eq (congrArg (fun V : Submodule ℂ X ↦ x.val ∈ V) hcl)
  exact (hzero.trans ⟨fun hx ↦ ⟨hx, x.property⟩, fun hx ↦ hx.1⟩).trans hmem.symm

/-- Paper: Proposition 4.5.1.1(4), p. 198. Inside the isotype, the kernel of
homogeneous periodization is the closure of the differences of isotypic functions.
Deviation: Closure is taken in the ambient decay space and then restricted to
the closed isotype. The linear image already contains the span of the differences. -/
theorem modulatedIsotypicPeriodization_ker_eq_closure :
    (Pχ).ker.comap (H[ωχ]).subtype =
      ((H[ωχ]).map (Δ).toLinearMap).topologicalClosure.comap (H[ωχ]).subtype := by
  let := modulatedCyclicSubgroup_closed m γ hγ
  let : T2Space S := schwartzBruhat_t2
  let : T2Space (SchwartzBruhat G) := schwartzBruhat_t2
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  let H := H[ωχ]
  have hc : IsClosed (H : Set E) := (isClosed_actionIsotype ((ρG).comp (K).subtype) (ωχ)).preimage
    (modulatedExponentialDecay_zeroTwist_continuous m hm hms univ ordConnected_univ (mem_univ 0))
  have hr := fullPeriodization_inter_isotype m γ hm hms hγ (ωχ)
  exact comap_ker_eq_comap_closure (X := E) (Y := S) Pχ P H (H.map (Δ).toLinearMap) hc hr M hM
    (fun v ↦ periodization_on_isotype m γ hm hms hγ μ₁ χ (ωχ) (fun _ ↦ rfl) v.val v.property)

end IsotypicKernel

section QuotientIsotypeInclusion

variable [MeasurableSpace G] [BorelSpace G]
variable (μ₁ : Measure m.toMonoidHom.ker) [μ₁.IsHaarMeasure]
variable (χ : PontryaginDual m.toMonoidHom.ker → PontryaginDual G)
variable (t₀ : PontryaginDual m.toMonoidHom.ker → ℝ)
variable (ht₀ : let period := Real.log ((m γ).val : ℝ)
  ∀ ω, t₀ ω ∈ Ico 0 (2 * Real.pi / period) ∧ Circle.exp (t₀ ω * period) = χ ω γ)
variable (hχ : ∀ (ω : PontryaginDual m.toMonoidHom.ker) (u : m.toMonoidHom.ker),
  χ ω u.val = ω u)
variable (ν : Measure (G ⧸ Subgroup.zpowers γ)) [ν.IsHaarMeasure]
variable (τ : ℝ≥0ˣ →ₜ* G) (hτ : RightInverse τ m)
variable (μ : Measure G) [μ.IsHaarMeasure]
variable (hμ : μ = (μ₁.prod positiveRealHaar).map (fun z : m.toMonoidHom.ker × ℝ≥0ˣ ↦ z.1.val * τ z.2))
variable (hν : IsWeilQuotientMeasure (Subgroup.zpowers γ) μ Measure.count ν)

local notation "qK" => (q).comp (K).subtype
local notation "Ψ[" ω "]" => modulatedQuotientIsotypicProjector m γ hm hγ μ₁ ω
local notation "Pχ[" ω "]" => modulatedIsotypicPeriodizationCLM m γ hm hms hγ μ₁ (χ ω)
local notation "V[" ω "]" => E ⧸ (Pχ[ω]).ker

private theorem quotient_submodule_equiv_of_retraction {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    [AddCommGroup Y] [Module ℂ Y] [TopologicalSpace Y]
    (F : X →L[ℂ] Y) (H N : Submodule ℂ X) (A : X → H) (hc : Continuous A)
    (hA : ∀ x, F (A x).val = F x) (hN : ∀ x : H, F x.val = 0 ↔ x.val ∈ N) :
    ∃ U : (H ⧸ N.comap H.subtype) ≃L[ℂ] (X ⧸ F.ker),
      ∀ x : H, U ((N.comap H.subtype).mkQ x) = F.ker.mkQ x.val := by
  let T := F.ker.mkQL.comp H.subtypeL
  have h : (fun x ↦ T (A x)) = F.ker.mkQ := by
    funext x
    exact (Submodule.Quotient.eq F.ker).mpr ((F.map_sub _ _).trans (sub_eq_zero.mpr (hA x)))
  have hq : IsQuotientMap T := IsQuotientMap.of_comp hc T.continuous
    (Eq.mpr (congrArg IsQuotientMap h) F.ker.isQuotientMap_mkQ)
  have hk : T.ker = N.comap H.subtype := SetLike.ext fun x ↦
    (Submodule.Quotient.mk_eq_zero F.ker).trans (hN x)
  exact exists_quotient_equiv_of_kernel T hq _ hk

include hχ in
/-- Paper: Proposition 4.5.1.1(4,6) and Corollary 4.5.1.6, pp. 198, 202–204.
Inclusion identifies the isotype modulo its cyclic differences with the full
decay space modulo homogeneous periodization. -/
theorem modulatedIsotypicPeriodizationQuotient_fromIsotype (ω : PontryaginDual K) :
    let H₀ := H[ω]
    let N := (H₀.map (Δ).toLinearMap).comap H₀.subtype
    ∃ F : (H₀ ⧸ N) ≃L[ℂ] V[ω], ∀ f : H₀, F (N.mkQ f) = (Pχ[ω]).ker.mkQ f.val := by
  intro H₀
  let : CompactSpace K := isCompact_iff_compactSpace.mp hm.isCompact_ker
  let M : ℂ := μ₁.real univ
  have hM : M ≠ 0 := Complex.ofReal_ne_zero.mpr (measureReal_univ_ne_zero (μ := μ₁))
  refine (exists_continuous_decay_average m hm hms μ₁ ω).elim fun A hA ↦ ?_
  have prop (f : E) := homogeneous_average_properties m hm μ₁ ω f (A f) (hA.2 f)
  let B (f : E) : H₀ := ⟨A f, (prop f).1⟩
  have hc : Continuous B := hA.1.subtype_mk _
  have he (f : E) : P (A f) = Ψ[ω] (P f) := by
    refine Subtype.ext (funext fun z ↦ QuotientGroup.induction_on z (fun x ↦ ?_))
    change P (A f) (q x) = M⁻¹ * ∫ u : K, (ω u : ℂ) * P f (qK u * q x) ∂μ₁
    have h := periodization_average_apply m γ hm hms hγ μ₁ ω f (A f) (prop f).2.2 x
    have hπ (u : K) : (ω u : ℂ) * P f (q (u.val * x)) = (ω u : ℂ) * P f (qK u * q x) :=
      congrArg (fun z ↦ (ω u : ℂ) * P f z) (map_mul (q) u.val x)
    exact h.trans (congrArg (M⁻¹ * ·) (integral_congr_ae (ae_of_all μ₁ hπ)))
  have hA' (f : E) : Pχ[ω] (B f).val = Pχ[ω] f :=
    (periodization_on_isotype m γ hm hms hγ μ₁ (χ ω) ω (hχ ω) _ (prop f).1).trans
      ((congrArg (M • ·) (he f)).trans
        (modulatedIsotypicPeriodizationQuotient_projector m γ hm hms hγ μ₁ χ hχ ω f).2.symm)
  have hi := fullPeriodization_inter_isotype m γ hm hms hγ ω
  have hN (x : H₀) : Pχ[ω] x.val = 0 ↔ x.val ∈ H₀.map (Δ).toLinearMap := by
    have hs := periodization_on_isotype m γ hm hms hγ μ₁ (χ ω) ω (hχ ω) x.val x.property
    have hz := (Iff.of_eq (congrArg (· = 0) hs)).trans (smul_eq_zero_iff_right hM)
    have hx : x.val ∈ (P).ker ⊓ H₀ ↔ x.val ∈ H₀.map (Δ).toLinearMap :=
      Iff.of_eq (congrArg (fun K₀ : Submodule ℂ E ↦ x.val ∈ K₀) hi)
    exact (hz.trans ⟨fun h ↦ ⟨h, x.property⟩, fun h ↦ h.1⟩).trans hx
  exact quotient_submodule_equiv_of_retraction (X := E) (Y := S) Pχ[ω] H₀ (H₀.map (Δ).toLinearMap) B hc hA' hN

end QuotientIsotypeInclusion

section SupportedPrimitive

variable (k : Subgroup G) (a b : ℝ≥0ˣ)
local notation "window" => Icc (b / a) (b * a)
local notation "W" => modulatedCompactSupportStage m window k

private theorem isCompact_unit_interval (l r : ℝ≥0ˣ) : IsCompact (Icc l r) := by
  let e := (Nonneg.unitsHomeomorphPos ℝ).trans Real.expOrderIso.symm.toHomeomorph
  have hmon (a b : ℝ≥0ˣ) : e a ≤ e b ↔ a ≤ b := by
    change Real.expOrderIso.symm _ ≤ Real.expOrderIso.symm _ ↔ _
    exact Real.expOrderIso.symm.le_iff_le
  have he : Icc l r = e ⁻¹' Icc (e l) (e r) :=
    Set.ext fun x ↦ and_congr (hmon l x).symm (hmon x r).symm
  exact he ▸ e.isProperMap.isCompact_preimage isCompact_Icc

private theorem cyclicPrimitive_vanishes_outside {A : Type*} [CommGroup A]
    (w : A →* ℝ≥0ˣ) (t : A) (ht : 1 ≤ w t) (lo hi : ℝ≥0ˣ) (g : A → ℂ)
    (hs : ∀ x, Summable fun n : ℤ ↦ g (t ^ n * x))
    (hf : ∀ x, w x ∉ Icc lo hi → g x = g (t * x)) :
    ∀ x, w x ∉ Icc (w t * lo) hi → g x = 0 := by
  have tail (s : A) (x : A) (h : Summable fun n : ℕ ↦ g (s ^ n * x))
      (hi : ∀ n : ℕ, g (s ^ (n+1) * x) = g (s ^ n * x)) : g x = 0 := by
    have he (n : ℕ) : g (s ^ n * x) = g x := by
      induction n with
      | zero => simp
      | succ n ih => exact (hi n).trans ih
    exact (summable_const_iff (β := ℕ) (g x)).mp (h.congr he)
  intro x hx
  by_cases hh : hi < w x
  · refine tail t x ?_ fun n ↦ ?_
    · simpa only [Function.comp_def, zpow_natCast] using (hs x).comp_injective (Nat.cast_injective (R := ℤ))
    · have hb : hi < w (t ^ n * x) := by
        rw [map_mul, map_pow]
        exact hh.trans_le (le_mul_of_one_le_left' (one_le_pow_of_one_le' ht n))
      simpa only [pow_succ', mul_assoc] using (hf _ fun h ↦ hb.not_ge h.2).symm
  · have hl : w x < w t * lo := lt_of_not_ge fun h ↦ hx ⟨h, le_of_not_gt hh⟩
    have hfirst : (w t)⁻¹ * w x < lo := (inv_mul_lt_iff_lt_mul).mpr hl
    refine tail t⁻¹ x ?_ fun n ↦ ?_
    · have h := (hs x).comp_injective (neg_injective.comp (Nat.cast_injective (R := ℤ)))
      simpa only [Function.comp_def, zpow_neg, zpow_natCast, inv_pow] using h
    · let y := (t⁻¹) ^ (n+1) * x
      have hb : w y < lo := by
        change w ((t⁻¹) ^ (n+1) * x) < lo
        rw [map_mul, map_pow, map_inv, pow_succ, mul_assoc]
        exact (mul_le_of_le_one_left' (pow_le_one' (inv_le_one'.mpr ht) n)).trans_lt hfirst
      have ht' : t * y = (t⁻¹)^n * x := by simp [y, pow_succ', ← mul_assoc]
      exact (hf y fun h ↦ hb.not_ge h.1).trans (congrArg g ht')

-- TODO(paper-gap): Proposition 4.5.2.1(3) has a false support bound. For
-- G = ℝ_{>0}, γ = a > 1 and b = 1, its A is zero. A nonzero bump ψ in
-- (1, γ) gives φ(x) = ψ(x) - ψ(γx) in the kernel with the required support,
-- but a continuous ψ supported in {1} is zero.

/-- Paper: Proposition 4.5.2.1(3), pp. 205–207. A supported kernel element
has a k-invariant primitive supported over the window with its lower endpoint
multiplied by the generator's module.
Deviation: Forward and backward telescoping give this asymmetric interval
in place of the false symmetric bound. -/
theorem modulatedCompactSupportStage_exists_difference
    (f : W) (hf : P f.val = 0) :
    ∃ g : modulatedCompactSupportStage m (Icc (m γ * (b / a)) (b * a)) k,
      Δ g.val = f.val := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  have hker : f.val ∈ (P).ker := hf
  have hr : f.val ∈ (Δ).range := Eq.mp (congrArg (fun N : Submodule ℂ E ↦ f.val ∈ N) (fullPeriodization_ker_eq_range m γ hm hms hγ)) hker
  refine hr.elim fun g hg ↦ ?_
  have hdiff (x : G) : g.val x - g.val (γ * x) = f.val.val x :=
    (modulatedCyclicDifference_apply m γ hm hms univ ordConnected_univ univ_nonempty g x).symm.trans
      (congrArg (fun v : E ↦ v.val x) hg)
  have hs (x : G) := (modulatedPeriodization_hasSum m γ hm hms hγ g x).summable
  have hW := (mem_modulatedCompactSupportStage_iff m window k f.val).mp f.property
  have hF := ((mem_modulatedCompactSupportSubmodule_iff m window (isCompact_unit_interval _ _).isClosed f.val).mp hW.1).2
  have hz (x : G) (hx : m x ∉ window) : g.val x = g.val (γ * x) :=
    sub_eq_zero.mp ((hdiff x).trans (notMem_support.mp fun h ↦ hx (hF (subset_tsupport _ h))))
  let J := Icc (m γ * (b / a)) (b * a)
  have hJ : IsCompact (m ⁻¹' J) := hm.1.isCompact_preimage (isCompact_unit_interval _ _)
  have hvan := cyclicPrimitive_vanishes_outside m.toMonoidHom γ
    (show (1 : ℝ≥0ˣ) ≤ m γ from hγ.le) (b / a) (b * a) g.val hs hz
  have hsup : tsupport g.val ⊆ m ⁻¹' J := hJ.isClosed.closure_subset_iff.mpr
    (Function.support_subset_iff'.mpr hvan)
  have hmem := (mem_modulatedCompactSupportSubmodule_iff m J (isCompact_unit_interval _ _).isClosed g).mpr
    ⟨hJ.of_isClosed_subset (isClosed_tsupport _) hsup, hsup⟩
  refine ⟨⟨g, (mem_modulatedCompactSupportStage_iff m J k g).mpr ⟨hmem, fun x u ↦ ?_⟩⟩, hg⟩
  have hi (z : G) : g.val (u.val * z) - g.val (γ * (u.val * z)) =
      (1 : ℂ) * (g.val z - g.val (γ * z)) :=
    (hdiff _).trans ((hW.2 z u).trans ((hdiff z).symm.trans (one_mul _).symm))
  exact ((cyclicDifference_homogeneous_iff γ g.val hs u.val 1).mp hi x).trans (one_mul _)

end SupportedPrimitive

end RiemannMasullo
