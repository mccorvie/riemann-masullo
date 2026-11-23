module

public import RiemannMasullo.Ch05_ThetaZSpaces.Sec3b
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.MeasureTheory.Function.L2Space
import RiemannMasullo.ForMathlib.Analysis.SpecialFunctions.Pow.Complex

/-! # Second Structure Theorem and the S-local Čech sequence

Masullo, §5.4, pp. 265–277. The set S in Lean lists the finite places.
-/

@[expose] public noncomputable section

open Filter Function IsDedekindDomain MeasureTheory NumberField Set TopologicalSpace Topology
open scoped MeasureTheory NNReal NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false
set_option maxSynthPendingDepth 8

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Aₛ" => SAdeleRing F S
local notation "ℬₛ" => SchwartzBruhat (Multiplicative Aₛ)
local notation "Jₛ" => SIdeleQuotient F S
local notation "mₛ" => sIdeleQuotientNorm F S
local notation "J₁" => (mₛ).ker
local notation "hmₛ" => (isProperMap_sIdeleQuotientNorm F S).continuous
local notation "normℝ(" t ")" => (((t : ℝ≥0ˣ).val : ℝ))
local notation "normChart(" χ ")" => quasiCharacterNormTwist (G := Jₛ) mₛ hmₛ
  ((⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ))
local notation "restrict₁(" χ ")" => ((χ : PontryaginDual Jₛ).comp
  (⟨(mₛ).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* Jₛ))
local notation "Θω(" ω ")" => SLocalHomogeneousThetaSpace F S (ω)
local notation "φω(" ω ")" => sLocalHomogeneousAdelicThetaLinearMap F S (ω)
local notation "Fourierₛ" => sAdeleSchwartzFourier (F := F) (S := S)
local notation "Zₛ" => sLocalIdelicZFunction (F := F) (S := S)
local notation "ρₛ(" χ ", " s ")" => sLocalRhoFactor (F := F) (S := S) (normChart(χ) (s))

local notation "rightInterval" => Ioi (0 : ℝ)
local notation "leftInterval" => Iio (1 : ℝ)
local notation "overlapInterval" => Ioo (0 : ℝ) 1
local notation "rightHalf" => Complex.re ⁻¹' rightInterval
local notation "leftHalf" => Complex.re ⁻¹' leftInterval
local notation "overlap" => Complex.re ⁻¹' overlapInterval
local notation "B⁺" => SchwartzBergman rightInterval
local notation "B⁻" => SchwartzBergman leftInterval
local notation "B⁰" => SchwartzBergman overlapInterval

section SecondStructure

-- The injectivity assertion in (5.4.1.1) is `sLocalThetaMellin_injective` from §5.1.

/-- Paper: (5.4.1.1), p. 265.
The Mellin map on the S-local theta quotient is continuous for compact convergence
on the regular locus of the meromorphic target. -/
theorem continuous_sLocalThetaMellin :
    Continuous (sLocalThetaMellin (F := F) (S := S)) := by
  exact (LinearMap.ker (sLocalAdelicTheta F S)).isQuotientMap_mkQ.continuous_iff.mpr
    (sLocalIdelicMellin_continuous (F := F) (S := S))

/-- Paper: Theorem 5.4.1.1(1), p. 265.
Every norm-one character has a unique unitary lift trivial on the chosen norm section.
Its norm twists give the coordinates used for the Second Structure Theorem. -/
theorem existsUnique_sLocalNormSectionCharacter (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (_hτ : RightInverse τ mₛ) (ω : PontryaginDual J₁) :
    ∃! χ : PontryaginDual Jₛ, restrict₁(χ) = ω ∧ ∀ t, χ (τ t) = 1 := by
  have hk (g : Jₛ) : g / τ (mₛ g) ∈ (mₛ).ker := by
    simp [MonoidHom.mem_ker, _hτ (mₛ g)]
  let p : Jₛ →ₜ* J₁ :=
    { toFun := fun g ↦ ⟨g / τ (mₛ g), hk g⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun g h ↦ Subtype.ext (by simp [mul_div_mul_comm])
      continuous_toFun := (continuous_id.div' (τ.continuous.comp hmₛ)).subtype_mk hk }
  have hp (u : J₁) : p u = u := by
    apply Subtype.ext
    change u.val / τ (mₛ u.val) = u.val
    rw [u.property, map_one, div_one]
  have hτp (t : ℝ≥0ˣ) : p (τ t) = 1 := by
    apply Subtype.ext
    change τ t / τ (mₛ (τ t)) = 1
    simp [_hτ t]
  refine ⟨ω.comp p, ⟨?_, ?_⟩, ?_⟩
  · ext1 u
    exact congrArg ω (hp u)
  · intro t
    change ω (p (τ t)) = 1
    rw [hτp, map_one]
  · rintro χ ⟨hker, hsec⟩
    ext1 g
    change χ g = ω (p g)
    have he := DFunLike.congr_fun hker (p g)
    change χ (g / τ (mₛ g)) = ω (p g) at he
    simpa only [map_div, hsec, div_one] using he

/-- On a closed positive strip, rapid decay controls the tails and continuity controls
the remaining compact rectangle. -/
private theorem existsUnique_sLocalZetaPair_right (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    ∃ u : B⁺, EqOn u.val (fun z ↦ Zₛ f (normChart(χ) z)) rightHalf := by
  let G := fun z ↦ Zₛ f (normChart(χ) z)
  have hG : DifferentiableOn ℂ G rightHalf :=
    (sLocalIdelicZetaIntegral_analyticOn f χ).differentiableOn.congr fun z hz ↦
      sLocalIdelicZFunction_eq_integral f ⟨χ, z, hz, rfl⟩
  refine ⟨⟨(rightHalf).indicator G, fun z hz ↦ indicator_of_notMem hz _,
    hG.congr (fun z hz ↦ indicator_of_mem hz _), ?_⟩, fun z hz ↦ indicator_of_mem hz _⟩
  intro a b hab hsub N
  have ha : 0 < a := hsub (left_mem_Icc.mpr hab)
  have hstrip : UniformlySchwartzOnStrip G (a / 2) (b + a) := by
    simpa only [iteratedDeriv_zero] using
      sLocalIdelicZFunction_schwartzOnStrip f χ (a / 2) (b + a) (by linarith) (by linarith) 0
  obtain ⟨C, hC, htail⟩ := hstrip.2.2 (a / 2) (by linarith) (by linarith) (N+1) (by omega)
  obtain ⟨T, hT⟩ := eventually_atTop.mp (eventually_comap.mp htail)
  let M := max T (max 1 b)
  let K := Complex.reProdIm (Icc a b) (Icc (-M) M)
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn (fun z : ℂ ↦ ‖z ^ N * G z‖) K :=
    ((continuous_id.pow N).continuousOn.mul (hG.continuousOn.mono (show K ⊆ rightHalf from fun _ hz ↦ hsub hz.1))).norm
  obtain ⟨B, hB⟩ := hK.bddAbove_image hc
  refine ⟨max B (2 ^ N * C), ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  change ‖z ^ N * (rightHalf).indicator G z‖ ≤ _
  rw [indicator_of_mem (show z ∈ rightHalf from hsub hz)]
  by_cases hy : |z.im| ≤ M
  · exact (hB ⟨z, ⟨hz, abs_le.mp hy⟩, rfl⟩).trans (le_max_left _ _)
  have hy' := (lt_of_not_ge hy).le
  have hy1 : 1 ≤ |z.im| := (le_max_left _ _).trans ((le_max_right _ _).trans hy')
  have hy0 : 0 < |z.im| := zero_lt_one.trans_le hy1
  have hz' : z.re ∈ Icc a b := hz
  have hdec := hT |z.im| ((le_max_left _ _).trans hy') z.im rfl z.re
    (show z.re ∈ Icc (a / 2 + a / 2) (b + a - a / 2) from ⟨by linarith [hz'.1], by linarith [hz'.2]⟩)
  simp only [Complex.re_add_im] at hdec
  have hnorm : ‖z‖ ≤ 2 * |z.im| := by
    apply (Complex.norm_le_abs_re_add_abs_im z).trans
    rw [abs_of_nonneg (ha.le.trans hz'.1)]
    linarith [hz'.2.trans ((le_max_right 1 b).trans ((le_max_right T _).trans hy'))]
  have hpow : |z.im| ^ N ≤ |z.im| ^ (N + 1) := pow_le_pow_right₀ hy1 (by omega)
  apply le_trans _ (le_max_right _ _)
  rw [norm_mul, norm_pow]
  calc
    _ ≤ (2 * |z.im|) ^ N * (C / |z.im| ^ N) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hnorm _) (hdec.trans
        (div_le_div_of_nonneg_left hC.le (pow_pos hy0 _) hpow)) (norm_nonneg _) (by positivity)
    _ = 2 ^ N * C := by rw [mul_pow]; field_simp

private theorem existsUnique_sLocalZetaPair_reflect (u : B⁺) :
    ∃ v : B⁻, ∀ z, v.val z = u.val (1 - z) := by
  have hpos (z : ℂ) : 1 - z ∈ rightHalf ↔ z ∈ leftHalf := by
    change 0 < (1 - z).re ↔ z.re < 1
    simp
  refine ⟨⟨fun z ↦ u.val (1-z), fun z hz ↦ u.property.1 (mt (hpos z).mp hz),
    u.property.2.1.comp (by fun_prop) (fun z hz ↦ (hpos z).mpr hz), ?_⟩, fun z ↦ rfl⟩
  intro a b hab hsub N
  have hb : b < 1 := hsub (right_mem_Icc.mpr hab)
  have hi : Icc (1-b) (1-a) ⊆ rightInterval := fun _ hw ↦ (sub_pos.mpr hb).trans_le hw.1
  obtain ⟨A, hA⟩ := u.property.2.2 (1-b) (1-a) (by linarith) hi 0
  obtain ⟨B, hB⟩ := u.property.2.2 (1-b) (1-a) (by linarith) hi N
  refine ⟨2 ^ N * max A B, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  let w := 1 - z
  have hw : w ∈ Complex.re ⁻¹' Icc (1-b) (1-a) := by
    change 1-b ≤ (1-z).re ∧ (1-z).re ≤ 1-a
    simp only [Complex.sub_re, Complex.one_re]
    exact ⟨sub_le_sub_left hz.2 _, sub_le_sub_left hz.1 _⟩
  have hbound : ‖z‖ ≤ 1 + ‖w‖ := by simpa [w] using norm_sub_le (1 : ℂ) w
  change ‖z ^ N * u.val w‖ ≤ _
  rw [norm_mul, norm_pow]
  rcases le_total ‖w‖ 1 with h | h
  · have hA' : ‖u.val w‖ ≤ A := by simpa using hA (mem_image_of_mem _ hw)
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (by linarith : ‖z‖ ≤ 2) N)
      (hA'.trans (le_max_left _ _)) (norm_nonneg _) (by positivity)
  · have hB' := hB (mem_image_of_mem _ hw)
    rw [norm_mul, norm_pow] at hB'
    calc
      _ ≤ (2 * ‖w‖) ^ N * ‖u.val w‖ := by gcongr; linarith
      _ = 2 ^ N * (‖w‖ ^ N * ‖u.val w‖) := by rw [mul_pow, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hB'.trans (le_max_right _ _)) (by positivity)

private theorem existsUnique_sLocalZetaPair_eval (χ : PontryaginDual Jₛ) (s : ℂ)
    (hs : s ∈ rightHalf) : ∃ E : Θω(restrict₁(χ)) →ₗ[ℂ] ℂ,
      ∀ f : ℬₛ, E (Submodule.Quotient.mk f) = Zₛ f (normChart(χ) s) := by
  let c := normChart(χ) s
  have htwist (z : ℂ) : quasiCharacterNormTwist mₛ hmₛ c z = normChart(χ) (z + s) := by
    ext1 g
    let N : ℂ := (normℝ(mₛ g) : ℂ)
    change (χ g : ℂ) * N ^ s * N ^ z = (χ g : ℂ) * N ^ (z + s)
    rw [add_comm, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)), mul_assoc]
  have hc : 0 ≤ sLocalIdelicOrderBound c := by
    simp only [sLocalIdelicOrderBound, htwist, le_min_iff]
    have hρ := sLocalRhoFactor_iteratedDeriv_analyticOn χ 0 s hs
    rw [iteratedDeriv_zero] at hρ
    exact ⟨le_rfl, ((show AnalyticAt ℂ (fun w ↦ ρₛ(χ, w)) (0 + s) by simpa using hρ).comp
      (f := fun z : ℂ ↦ z + s) (by fun_prop)).meromorphicOrderAt_nonneg⟩
  let x : {d // 0 ≤ sLocalIdelicOrderBound (F := F) (S := S) d} := ⟨c, hc⟩
  let E : ℬₛ →ₗ[ℂ] ℂ :=
    { toFun := fun f ↦ Zₛ f c
      map_add' := fun f g ↦ congrArg (fun h ↦ DFunLike.coe h x)
        (sLocalIdelicZFunction_isLinear.map_add f g)
      map_smul' := fun a f ↦ congrArg (fun h ↦ DFunLike.coe h x)
        (sLocalIdelicZFunction_isLinear.map_smul a f) }
  refine ⟨(LinearMap.ker (φω(restrict₁(χ)))).liftQ E ?_, fun _ ↦ rfl⟩
  intro f hf
  apply (mem_sLocalHomogeneousAdelicTheta_ker_iff (restrict₁(χ)) f).mp hf x
  intro u
  change (χ u.val : ℂ) * (normℝ(mₛ u.val) : ℂ) ^ s = (χ u.val : ℂ)
  rw [u.prop]
  simp

private theorem existsUnique_sLocalZetaPair_equation (χ : PontryaginDual Jₛ) (f : ℬₛ)
    (s : ℂ) (hs : s ∈ overlap) :
    Zₛ f (normChart(χ) s) = ρₛ(χ, s) * Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s)) := by
  have ht : 1 - s ∈ rightHalf := by simpa [mem_preimage, mem_Ioi] using sub_pos.mpr hs.2
  have hd : dualQuasiCharacter mₛ hmₛ (normChart(χ) s) = normChart(χ⁻¹) (1 - s) := by
    ext1 g
    let N : ℂ := (normℝ(mₛ g) : ℂ)
    have hN : N ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_ne_zero.mpr (mₛ g).ne_zero)
    change N * normChart(χ) s g⁻¹ = ((χ g : ℂ)⁻¹ * N ^ (1-s))
    rw [map_inv]
    change N * ((χ g : ℂ) * N ^ s)⁻¹ = (χ g : ℂ)⁻¹ * N ^ (1-s)
    rw [Complex.cpow_sub _ _ hN, Complex.cpow_one, div_eq_mul_inv, mul_inv_rev]
    ac_rfl
  have he := sLocalIdelicZetaIntegral_functionalEquation f χ s hs
  exact (sLocalIdelicZFunction_eq_integral f ⟨χ, s, hs.1, rfl⟩).trans <| he.trans <|
    congrArg (ρₛ(χ, s) * ·) ((congrArg (sLocalIdelicZetaIntegral (Fourierₛ f)) hd).trans
      (sLocalIdelicZFunction_eq_integral (Fourierₛ f) ⟨χ⁻¹, 1-s, ht, rfl⟩).symm)

private theorem existsUnique_sLocalZetaPair_ext {I : Set ℝ} {u v : SchwartzBergman I}
    (h : EqOn u.val v.val (Complex.re ⁻¹' I)) : u = v := by
  apply Subtype.ext
  funext z
  by_cases hz : z ∈ Complex.re ⁻¹' I
  · exact h hz
  · exact (u.property.1 hz).trans (v.property.1 hz).symm

/-- Multiplication by the functional-equation factor and restriction to the overlap
still detect a left component, by the holomorphic identity theorem. -/
private theorem existsUnique_sLocalZetaPair_left_ext (χ : PontryaginDual Jₛ) (u v : B⁻)
    (h : ∀ z ∈ overlap, ρₛ(χ, z) * u.val z = ρₛ(χ, z) * v.val z) : u = v := by
  have hol (w : B⁻) : AnalyticOnNhd ℂ w.val leftHalf :=
    w.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re)
  have hband : ∀ᶠ s : ℂ in 𝓝[≠] (1 / 2 : ℂ), s ∈ overlap :=
    nhdsWithin_le_nhds ((isOpen_Ioo.preimage Complex.continuous_re).mem_nhds (by
      norm_num [mem_preimage, mem_Ioo]))
  apply existsUnique_sLocalZetaPair_ext
  apply (hol u).eqOn_of_preconnected_of_frequently_eq (hol v)
    (convex_halfSpace_re_lt 1).isPreconnected (z₀ := 1/2) (by norm_num [mem_preimage])
  apply Filter.Eventually.frequently
  filter_upwards [hband, nhdsNE_le_codiscrete _ (sLocalRhoFactor_mul_dual χ)] with z hz hprod
  have hne : ρₛ(χ, z) ≠ 0 := left_ne_zero_of_mul
    (hprod.trans_ne ((Group.isUnit (QuotientGroup.mk (-1 : Aₛˣ) : Jₛ)).map (normChart(χ) z)).ne_zero)
  exact mul_left_cancel₀ hne (h z hz)

/-- Paper: (5.4.1.2), p. 265.
The two zeta restrictions descend uniquely as a linear map on homogeneous theta classes.
Deviation: We use the unitary-lift coordinates of Remark 5.4.1.2. The normalized lift
for a chosen section recovers the coordinates of Theorem 5.4.1.1. If the lift
has frequency x on the section, both entries, as functions of s here, shift by +ix.
The unreflected Fourier Mellin transform separately has frequency -x. -/
theorem existsUnique_sLocalZetaPair (χ : PontryaginDual Jₛ) :
    ∃! U : Θω(restrict₁(χ)) →ₗ[ℂ] B⁺ × B⁻, ∀ (f : ℬₛ),
      EqOn (U (Submodule.Quotient.mk f)).1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
      EqOn (U (Submodule.Quotient.mk f)).2.val
        (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s))) leftHalf := by
  classical
  choose E hE using fun s : rightHalf ↦ existsUnique_sLocalZetaPair_eval χ s.val s.property
  -- The right evaluations descend individually to the quotient. On the overlap they
  -- are also the evaluations of the reflected component multiplied by the Tate factor.
  let T : B⁺ →ₗ[ℂ] (rightHalf → ℂ) :=
    LinearMap.pi fun s ↦ (LinearMap.proj s.val).comp (schwartzBergmanSubmodule rightInterval).subtype
  let D : B⁻ →ₗ[ℂ] (overlap → ℂ) :=
    LinearMap.pi fun s ↦ ρₛ(χ, s.val) •
      ((LinearMap.proj s.val).comp (schwartzBergmanSubmodule leftInterval).subtype)
  have hT : Injective T := fun _ _ he ↦ existsUnique_sLocalZetaPair_ext
    (fun z hz ↦ congrFun he ⟨z, hz⟩)
  have hD : Injective D := fun u v he ↦ existsUnique_sLocalZetaPair_left_ext χ u v
    (fun z hz ↦ congrFun he ⟨z, hz⟩)
  let A := T.leftInverse.comp (LinearMap.pi E)
  let B := D.leftInverse.comp (LinearMap.pi fun s : overlap ↦ E ⟨s.val, s.property.1⟩)
  have spec (f : ℬₛ) : EqOn (A (Submodule.Quotient.mk f)).val
        (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
      EqOn (B (Submodule.Quotient.mk f)).val
        (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s))) leftHalf := by
    refine (existsUnique_sLocalZetaPair_right (F := F) (S := S) χ f).elim fun u hu ↦ ?_
    refine (existsUnique_sLocalZetaPair_right (F := F) (S := S) χ⁻¹ (Fourierₛ f)).elim fun w hw ↦ ?_
    refine (existsUnique_sLocalZetaPair_reflect w).elim fun v hv ↦ ?_
    have hv' : EqOn v.val (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1-s))) leftHalf :=
      fun s hs ↦ (hv s).trans (hw (show 1 - s ∈ rightHalf by
        simpa [mem_preimage, mem_Ioi] using sub_pos.mpr hs))
    have eA : (LinearMap.pi E) (Submodule.Quotient.mk f) = T u :=
      funext fun s ↦ (hE s f).trans (hu s.property).symm
    have eB : (LinearMap.pi fun s : overlap ↦ E ⟨s.val, s.property.1⟩) (Submodule.Quotient.mk f) = D v :=
      funext fun s ↦ (hE ⟨s.val, s.property.1⟩ f).trans
        ((existsUnique_sLocalZetaPair_equation χ f s s.property).trans
          (congrArg (ρₛ(χ, s.val) * ·) (hv' s.property.2).symm))
    have hA : A (Submodule.Quotient.mk f) = u :=
      (congrArg T.leftInverse eA).trans (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hT) u)
    have hB : B (Submodule.Quotient.mk f) = v :=
      (congrArg D.leftInverse eB).trans (LinearMap.leftInverse_apply_of_inj (LinearMap.ker_eq_bot.mpr hD) v)
    exact ⟨fun s hs ↦ (congrArg (fun g : B⁺ ↦ g.val s) hA).trans (hu hs),
      fun s hs ↦ (congrArg (fun g : B⁻ ↦ g.val s) hB).trans (hv' hs)⟩
  refine ⟨A.prod B, spec, ?_⟩
  intro V hV
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro f
  exact Prod.ext (existsUnique_sLocalZetaPair_ext ((hV f).1.trans (spec f).1.symm))
    (existsUnique_sLocalZetaPair_ext ((hV f).2.trans (spec f).2.symm))

/-- Paper: (5.4.1.2), p. 265.
The map pairs the zeta transform with the reflected zeta transform of the Fourier transform.
Deviation: The chart is the unitary-lift chart of Remark 5.4.1.2. -/
def sLocalZetaPair (χ : PontryaginDual Jₛ) : Θω(restrict₁(χ)) →ₗ[ℂ] B⁺ × B⁻ :=
  (existsUnique_sLocalZetaPair (F := F) (S := S) χ).exists.choose

/-- Paper: (5.4.1.2), p. 265.
On test functions the two components evaluate to their respective zeta integrals
on their half-planes of convergence. -/
theorem sLocalZetaPair_mk (χ : PontryaginDual Jₛ) (f : ℬₛ) :
    EqOn (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).1.val
      (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
    EqOn (sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)).2.val
      (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) (1 - s))) leftHalf := by
  have h := (existsUnique_sLocalZetaPair (F := F) (S := S) χ).exists.choose_spec f
  exact h

/-- Paper: (5.4.1.3), p. 266.
Subtracting the corrected second component from the first on the overlap is a
continuous linear map into the Schwartz–Bergman space of the overlap. -/
theorem existsUnique_sLocalZetaMatchingDifference (χ : PontryaginDual Jₛ) :
    ∃! D : B⁺ × B⁻ →L[ℂ] B⁰, ∀ p : B⁺ × B⁻,
      EqOn (D p).val (fun s ↦ p.1.val s - ρₛ(χ, s) * p.2.val s) overlap := by sorry

/-- Paper: (5.4.1.3), p. 266.
The space W is the kernel of the difference of the two restrictions, with the
second restriction multiplied by the local functional-equation factor. -/
def sLocalZetaMatching (χ : PontryaginDual Jₛ) : Submodule ℂ (B⁺ × B⁻) :=
  let difference : B⁺ × B⁻ →L[ℂ] B⁰ :=
    (existsUnique_sLocalZetaMatchingDifference (F := F) (S := S) χ).exists.choose
  LinearMap.ker difference.toLinearMap

/-- A continuous linear map into a Schwartz–Bergman space given pointwise on the strip by a
difference vanishes exactly where the two terms agree on the strip. -/
private theorem mem_sLocalZetaMatching_aux {X : Type*} [AddCommGroup X] [Module ℂ X]
    [TopologicalSpace X] {I : Set ℝ} (D : X →L[ℂ] SchwartzBergman I) (a b : X → ℂ → ℂ)
    (hD : ∀ p, EqOn (D p).val (fun s ↦ a p s - b p s) (Complex.re ⁻¹' I)) (p : X) :
    p ∈ LinearMap.ker D.toLinearMap ↔ EqOn (a p) (b p) (Complex.re ⁻¹' I) := by
  have h0 : ((0 : SchwartzBergman I) : schwartzBergmanSubmodule I).val = 0 := rfl
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  constructor
  · intro h s hs
    have hs' := hD p hs
    rw [h, h0] at hs'
    exact sub_eq_zero.mp hs'.symm
  · intro h
    have hval : ((D p : SchwartzBergman I) : schwartzBergmanSubmodule I).val = 0 := by
      funext s
      by_cases hs : s ∈ Complex.re ⁻¹' I
      · exact (hD p hs).trans (sub_eq_zero.mpr (h hs))
      · exact (D p).property.1 hs
    exact Subtype.ext (hval.trans h0.symm)

/-- Paper: (5.4.1.3), p. 266.
A pair belongs to W exactly when its components satisfy the functional equation
at each point in the overlap strip. -/
theorem mem_sLocalZetaMatching (χ : PontryaginDual Jₛ) (p : B⁺ × B⁻) :
    p ∈ sLocalZetaMatching (F := F) (S := S) χ ↔
      EqOn p.1.val (fun s ↦ ρₛ(χ, s) * p.2.val s) overlap := by
  have h := (existsUnique_sLocalZetaMatchingDifference (F := F) (S := S) χ).exists.choose_spec
  have key := mem_sLocalZetaMatching_aux (I := overlapInterval) _
    (fun p : B⁺ × B⁻ ↦ p.1.val) (fun p s ↦ ρₛ(χ, s) * p.2.val s) h p
  exact key

/-- Paper: Theorem 5.4.1.1(1), p. 266.
The zeta pair is a topological embedding with closed range. -/
theorem sLocalZetaPair_isClosedEmbedding (χ : PontryaginDual Jₛ) :
    IsClosedEmbedding (sLocalZetaPair (F := F) (S := S) χ) := by sorry

/-- Paper: Theorem 5.4.1.1(1), p. 266.
Every matching pair, and only a matching pair, comes from a homogeneous theta class. -/
theorem sLocalZetaPair_range (χ : PontryaginDual Jₛ) :
    (sLocalZetaPair (F := F) (S := S) χ).range = sLocalZetaMatching (F := F) (S := S) χ := by sorry

-- TODO(paper-gap): The two printed translation factors disagree on the overlap.
-- The functional equation and Fourier scaling both give the first factor on both entries.

/-- Paper: Theorem 5.4.1.1(1), p. 266, and Remark 5.4.1.2, p. 266.
Inverse left translation of a test induces multiplication of each zeta coordinate
by the first component's quasi-character evaluated at the translating idele class.
Deviation: Fourier scaling contributes the norm, and inversion of the Fourier
quasi-character gives the same multiplier as in the first coordinate. -/
theorem sLocalZetaPair_translate (χ : PontryaginDual Jₛ) (u : Aₛˣ) (f : ℬₛ) :
    let p : B⁺ × B⁻ := sLocalZetaPair (F := F) (S := S) χ (Submodule.Quotient.mk f)
    let q : B⁺ × B⁻ := sLocalZetaPair (F := F) (S := S) χ
      (Submodule.Quotient.mk (schwartzBruhatUnitTranslate (R := Aₛ) u f))
    EqOn q.1.val (fun s ↦ normChart(χ) s (QuotientGroup.mk u) * p.1.val s) rightHalf ∧
    EqOn q.2.val (fun s ↦ normChart(χ) s (QuotientGroup.mk u) * p.2.val s) leftHalf :=
  by sorry

/-- Paper: Theorem 5.4.1.1(1), pp. 265–266.
The componentwise multipliers give a jointly continuous action on the ambient pair.
Deviation: Both coordinates in the reflected chart have the character of the test. -/
theorem exists_sLocalZetaPair_action (χ : PontryaginDual Jₛ) :
    ∃ A : Jₛ →* ((B⁺ × B⁻) →L[ℂ] (B⁺ × B⁻)),
      Continuous (fun p : Jₛ × (B⁺ × B⁻) ↦ A p.1 p.2) ∧
      ∀ (g : Jₛ) (p : B⁺ × B⁻),
        EqOn (A g p).1.val (fun s ↦ normChart(χ) s g * p.1.val s) rightHalf ∧
        EqOn (A g p).2.val (fun s ↦ normChart(χ) s g * p.2.val s) leftHalf := by sorry

/-- Paper: Theorem 5.4.1.1(2), p. 266.
The quotient topology on every homogeneous S-local theta space is Fréchet. -/
theorem sLocalHomogeneousThetaSpace_frechet (ω : PontryaginDual J₁) :
    IsFrechetTVS (Θω(ω)) := by
  obtain ⟨τ, hτ⟩ := sIdeleQuotientNorm_exists_section F S
  obtain ⟨χ, hχ, _⟩ := existsUnique_sLocalNormSectionCharacter τ hτ ω
  rw [← hχ.1]
  obtain ⟨_, _, hMp, hCp⟩ := schwartzBergman_frechet rightInterval isOpen_Ioi
    ordConnected_Ioi ⟨1, by norm_num⟩
  obtain ⟨_, _, hMm, hCm⟩ := schwartzBergman_frechet leftInterval isOpen_Iio
    ordConnected_Iio ⟨0, by norm_num⟩
  let : MetrizableSpace B⁺ := hMp
  let : MetrizableSpace B⁻ := hMm
  let : CompleteSpace B⁺ := hCp
  let : CompleteSpace B⁻ := hCm
  let T := sLocalZetaPair (F := F) (S := S) χ
  have hT : IsClosedEmbedding T := sLocalZetaPair_isClosedEmbedding χ
  let : UniformSpace Θω(restrict₁(χ)) :=
    IsTopologicalAddGroup.rightUniformSpace Θω(restrict₁(χ))
  have : IsUniformAddGroup Θω(restrict₁(χ)) := isUniformAddGroup_of_addCommGroup
  have hU : IsUniformInducing T :=
    AddMonoidHom.isUniformInducing_of_isInducing (f := T.toAddMonoidHom) hT.isInducing
  exact ⟨inferInstance, hT.isInducing.polynormableSpace (f := T),
    hT.isEmbedding.metrizableSpace, hU.completeSpace hT.isClosed_range.isComplete⟩

/-- A nuclear space is separable for each of its continuous seminorms (as in the private
`seminorm_separable_of_nuclear` of Appendix D §1b): a totally bounded zero-neighbourhood
spans the space and has separable span. -/
private theorem sLocalHomogeneousThetaSpace_separable_seminorm.{w, x} {E : Type x}
    [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [ContinuousSMul ℂ E] (h : IsNuclearTVS.{w} E) (p : Seminorm ℂ E) (hp : Continuous p) :
    SeparableSpace (WithLocalSeminorm p) := by
  obtain ⟨V, hV, htot⟩ := (isSchwartzTVS_of_isNuclearTVS h).2 p hp
  let W : Set (WithLocalSeminorm p) := V
  have hW : TotallyBounded W := htot
  have hAbs : Absorbent ℂ W := by
    change Absorbent ℂ V
    exact absorbent_nhds_zero (𝕜 := ℂ) hV
  have hspan : Submodule.span ℂ W = ⊤ :=
    (hAbs.mono (Submodule.subset_span (R := ℂ))).submodule_eq_top
  have hS := hW.isSeparable.span (R := ℂ)
  rw [hspan, Submodule.top_coe] at hS
  exact isSeparable_univ_iff.mp hS

/-- A nuclear space with a countable neighbourhood basis at zero is separable: for each basic
neighbourhood pick a continuous seminorm ball inside it and a dense sequence for that seminorm. -/
private theorem sLocalHomogeneousThetaSpace_separable_aux.{w, x} {E : Type x} [AddCommGroup E]
    [Module ℂ E] [TopologicalSpace E] [FirstCountableTopology E]
    (h : IsNuclearTVS.{w} E) : SeparableSpace E := by
  let := h.2.1
  let := PolynormableSpace.isTopologicalAddGroup ℂ E
  have hw := PolynormableSpace.withSeminorms ℂ E
  let : ContinuousSMul ℂ E := hw.continuousSMul
  obtain ⟨U, hU⟩ := (𝓝 (0 : E)).exists_antitone_basis
  have hex (n : ℕ) : ∃ q : Seminorm ℂ E, Continuous q ∧ ∃ r > 0, q.ball 0 r ⊆ U n := by
    obtain ⟨s, r, hr, hsub⟩ := (hw.mem_nhds_iff 0 (U n)).mp (hU.mem n)
    refine ⟨s.sup fun p : {p : Seminorm ℂ E // Continuous p} ↦ p.1, ?_, r, hr, hsub⟩
    exact hw.continuous_finsetSup_seminorm s
  choose q hq r hr hsub using hex
  have hsep (n : ℕ) : SeparableSpace (WithLocalSeminorm (q n)) :=
    sLocalHomogeneousThetaSpace_separable_seminorm h (q n) (hq n)
  have hd (n : ℕ) : ∃ d : ℕ → E, ∀ x : E, ∃ m, q n (x - d m) < r n := by
    obtain ⟨d, hd⟩ := exists_dense_seq (WithLocalSeminorm (q n))
    refine ⟨d, fun x ↦ ?_⟩
    let x' : WithLocalSeminorm (q n) := x
    obtain ⟨m, hm⟩ := hd.exists_dist_lt x' (hr n)
    rw [dist_eq_norm] at hm
    exact ⟨m, hm⟩
  choose d hd using hd
  refine ⟨range fun m : ℕ × ℕ ↦ d m.1 m.2, countable_range _, ?_⟩
  intro x
  rw [mem_closure_iff_nhds]
  intro W hW
  have hW0 : (fun y ↦ x + y) ⁻¹' W ∈ 𝓝 (0 : E) :=
    (continuous_const.add continuous_id).continuousAt.preimage_mem_nhds (by simpa using hW)
  obtain ⟨n, -, hn⟩ := hU.1.mem_iff.mp hW0
  obtain ⟨m, hm⟩ := hd n x
  refine ⟨d n m, ?_, ⟨(n, m), rfl⟩⟩
  have : d n m - x ∈ U n := hsub n (by rw [Seminorm.mem_ball, sub_zero, map_sub_rev]; exact hm)
  simpa using hn this

/-- A nuclear Fréchet space is separable. The instances are implicit arguments, so that they are
read off the hypotheses instead of being unfolded through the quotient. -/
private theorem sLocalHomogeneousThetaSpace_separable_of_frechet.{w, x} {E : Type x}
    {_ : AddCommGroup E} {_ : Module ℂ E} {_ : TopologicalSpace E} (hf : IsFrechetTVS E)
    (h : IsNuclearTVS.{w} E) : SeparableSpace E := by
  obtain ⟨_, -, _, -⟩ := hf
  exact sLocalHomogeneousThetaSpace_separable_aux h

/-- Paper: Theorem 5.4.1.1(2), p. 266.
Every homogeneous S-local theta space is separable. -/
theorem sLocalHomogeneousThetaSpace_separable (ω : PontryaginDual J₁) :
    SeparableSpace (Θω(ω)) :=
  sLocalHomogeneousThetaSpace_separable_of_frechet.{0}
    (sLocalHomogeneousThetaSpace_frechet ω) (sLocalHomogeneousThetaSpace_nuclear ω)

-- The nuclearity assertion in (2) is `sLocalHomogeneousThetaSpace_nuclear` from §5.2.3.

/-- Paper: Lemma 5.4.1.3, p. 266.
The quotient-to-pair map is continuous. -/
theorem continuous_sLocalZetaPair (χ : PontryaginDual Jₛ) : Continuous (sLocalZetaPair (F := F) (S := S) χ) := by
  exact (sLocalZetaPair_isClosedEmbedding (F := F) (S := S) χ).continuous

/-- Paper: Lemma 5.4.1.3, p. 266.
The two zeta restrictions determine the homogeneous theta class. -/
theorem injective_sLocalZetaPair (χ : PontryaginDual Jₛ) : Injective (sLocalZetaPair (F := F) (S := S) χ) := by
  exact (sLocalZetaPair_isClosedEmbedding (F := F) (S := S) χ).injective

-- Match the choice of archimedean coordinates in §5.3.4.
local notation "RealModels" => ((w : {v : InfinitePlace F // v.IsReal}) →
  {e : w.val.Completion ≃+* ℝ // IsHomeomorph (e : w.val.Completion → ℝ)})
local notation "ComplexModels" => ((w : {v : InfinitePlace F // v.IsComplex}) →
  {e : w.val.Completion ≃+* ℂ // IsHomeomorph (e : w.val.Completion → ℂ)})

local notation "polarTests(" r ", " c ")" => sAdelePolarFree (F := F) S (r) (c)

local notation "polarKernel(" P ", " ω ")" => LinearMap.ker ((φω(ω)).comp (P).subtype)

/-- Paper: (5.4.1.7), p. 267.
The polar-free homogeneous theta space is the quotient of the polar-free subspace
by the kernel of its restricted homogeneous theta transform.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev SLocalPolarFreeThetaSpace (r : RealModels) (c : ComplexModels) (ω : PontryaginDual J₁) :=
  ↥(polarTests(r, c)) ⧸ polarKernel(polarTests(r, c), ω)

/-- Paper: (5.4.1.7), p. 267.
Two polar-free representatives define the same class exactly when their
homogeneous theta functions coincide. -/
theorem sLocalPolarFreeThetaSpace_mk_eq_iff (r : RealModels) (c : ComplexModels)
    (ω : PontryaginDual J₁) (f g : polarTests(r, c)) :
    (polarKernel(polarTests(r, c), ω)).mkQ f = (polarKernel(polarTests(r, c), ω)).mkQ g ↔
      φω(ω) f.val = φω(ω) g.val := by
  simp only [Submodule.mkQ_apply, Submodule.Quotient.eq, LinearMap.mem_ker, LinearMap.comp_apply,
    Submodule.subtype_apply, Submodule.coe_sub, map_sub, sub_eq_zero]

local notation "polarInclusion(" P ", " ω ")" =>
  (polarKernel(P, ω)).mapQ (LinearMap.ker (φω(ω))) (P).subtype
    (le_of_eq (LinearMap.ker_comp (P).subtype (φω(ω))))

/-- Paper: (5.4.1.7), p. 267.
The zeta pair on the polar-free quotient is the full zeta pair applied to the
class of the same test function. -/
def sLocalPolarFreeZetaPair (χ : PontryaginDual Jₛ) (r : RealModels) (c : ComplexModels) :
    SLocalPolarFreeThetaSpace (F := F) (S := S) r c (restrict₁(χ)) →ₗ[ℂ] B⁺ × B⁻ :=
  (sLocalZetaPair (F := F) (S := S) χ).comp (polarInclusion(polarTests(r, c), restrict₁(χ)))

/-- Paper: (5.4.1.8), p. 267.
The matching pairs in V are those whose first component extends to an entire function. -/
def sLocalPolarFreeMatching (χ : PontryaginDual Jₛ) : Set (B⁺ × B⁻) :=
  {p | p ∈ sLocalZetaMatching (F := F) (S := S) χ ∧
    ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H univ ∧ EqOn H p.1.val rightHalf}

private theorem mem_sLocalPolarFreeMatching_iff_aux (ρ a b : ℂ → ℂ) (hρ : Meromorphic ρ)
    (ha : AnalyticOnNhd ℂ a (Complex.re ⁻¹' Ioi (0 : ℝ)))
    (hb : AnalyticOnNhd ℂ b (Complex.re ⁻¹' Iio (1 : ℝ)))
    (hab : EqOn a (fun s ↦ ρ s * b s) (Complex.re ⁻¹' Ioo (0 : ℝ) 1)) :
    (∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H univ ∧ EqOn H a (Complex.re ⁻¹' Ioi (0 : ℝ))) ↔
      ∀ s ∈ Complex.re ⁻¹' Iio (1 : ℝ), 0 ≤ meromorphicOrderAt (fun z ↦ ρ z * b z) s := by
  have hoL : IsOpen (Complex.re ⁻¹' Iio (1 : ℝ)) := isOpen_Iio.preimage Complex.continuous_re
  have hoR : IsOpen (Complex.re ⁻¹' Ioi (0 : ℝ)) := isOpen_Ioi.preimage Complex.continuous_re
  have hoO : IsOpen (Complex.re ⁻¹' Ioo (0 : ℝ) 1) := isOpen_Ioo.preimage Complex.continuous_re
  have hmg : MeromorphicOn (fun z ↦ ρ z * b z) (Complex.re ⁻¹' Iio (1 : ℝ)) :=
    fun z hz => (hρ z).mul (hb z hz).meromorphicAt
  have hmid : (1 / 2 : ℂ) ∈ Complex.re ⁻¹' Ioo (0 : ℝ) 1 := by
    norm_num [mem_preimage, mem_Ioo]
  have hmidL : (1 / 2 : ℂ) ∈ Complex.re ⁻¹' Iio (1 : ℝ) := by
    norm_num [mem_preimage, mem_Iio]
  have hconn : IsConnected (Complex.re ⁻¹' Iio (1 : ℝ)) :=
    ⟨⟨_, hmidL⟩, (convex_halfSpace_re_lt 1).isPreconnected⟩
  constructor
  · rintro ⟨H, hH, hHa⟩ s hs
    have hdiff : MeromorphicOn (fun z ↦ ρ z * b z - H z) (Complex.re ⁻¹' Iio (1 : ℝ)) :=
      hmg.sub (fun z _ => (hH z (mem_univ _)).meromorphicAt)
    have htop : meromorphicOrderAt (fun z ↦ ρ z * b z - H z) (1 / 2 : ℂ) = ⊤ := by
      rw [meromorphicOrderAt_eq_top_iff]
      filter_upwards [hoO.mem_nhds hmid |> fun h => nhdsWithin_le_nhds h] with z hz
      have h1 := hab hz
      have h2 := hHa (show z ∈ Complex.re ⁻¹' Ioi (0 : ℝ) from hz.1)
      change ρ z * b z - H z = 0
      have h1' : a z = ρ z * b z := h1
      rw [← h1', h2]; ring
    have hall : meromorphicOrderAt (fun z ↦ ρ z * b z - H z) s = ⊤ := by
      by_contra hne
      have := (hdiff.exists_meromorphicOrderAt_ne_top_iff_forall_mem hconn).mp ⟨s, hs, hne⟩
        (1 / 2) hmidL
      exact this htop
    rw [meromorphicOrderAt_eq_top_iff] at hall
    have hev : (fun z ↦ ρ z * b z) =ᶠ[𝓝[≠] s] H := by
      filter_upwards [hall] with z hz
      simpa [sub_eq_zero] using hz
    rw [meromorphicOrderAt_congr hev]
    exact (hH s (mem_univ _)).meromorphicOrderAt_nonneg
  · intro hord
    set G := toMeromorphicNFOn (fun z ↦ ρ z * b z) (Complex.re ⁻¹' Iio (1 : ℝ)) with hG
    have hGan : ∀ z ∈ Complex.re ⁻¹' Iio (1 : ℝ), AnalyticAt ℂ G z := by
      intro z hz
      have hnf : MeromorphicNFAt G z := meromorphicNFOn_toMeromorphicNFOn _ _ hz
      refine hnf.meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
      rw [hG, meromorphicOrderAt_toMeromorphicNFOn hmg hz]
      exact hord z hz
    have hGa : ∀ z ∈ Complex.re ⁻¹' Ioo (0 : ℝ) 1, G z = a z := by
      intro z hz
      have hzL : z ∈ Complex.re ⁻¹' Iio (1 : ℝ) := hz.2
      have hev : G =ᶠ[𝓝[≠] z] a := by
        have h1 := hmg.toMeromorphicNFOn_eq_self_on_nhdsNE hzL
        have h2 : (fun z ↦ ρ z * b z) =ᶠ[𝓝[≠] z] a := by
          filter_upwards [nhdsWithin_le_nhds (hoO.mem_nhds hz)] with w hw using (hab hw).symm
        exact h1.trans h2
      have hca : ContinuousAt a z := (ha z hz.1).continuousAt
      have hcG : ContinuousAt G z := (hGan z hzL).continuousAt
      exact ((hcG.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hca).mp hev).self_of_nhds
    let H : ℂ → ℂ := fun z ↦ if 0 < z.re then a z else G z
    have hHa : EqOn H a (Complex.re ⁻¹' Ioi (0 : ℝ)) := fun z hz => if_pos hz
    have hHG : EqOn H G (Complex.re ⁻¹' Iio (1 : ℝ)) := by
      intro z hz
      by_cases h0 : 0 < z.re
      · exact (if_pos h0).trans (hGa z ⟨h0, hz⟩).symm
      · exact if_neg h0
    refine ⟨H, fun z _ => ?_, hHa⟩
    by_cases hz : z.re < 1
    · exact (hGan z hz).congr (Filter.eventuallyEq_of_mem (hoL.mem_nhds hz) hHG.symm)
    · have hz1 : z ∈ Complex.re ⁻¹' Ioi (0 : ℝ) := by
        change 0 < z.re; linarith [not_lt.mp hz]
      exact (ha z hz1).congr (Filter.eventuallyEq_of_mem (hoR.mem_nhds hz1) hHa.symm)

/-- Paper: (5.4.1.8), p. 267.
In a matching pair the first component has an entire extension exactly when the
continued second component has no poles in the left half-plane. -/
theorem mem_sLocalPolarFreeMatching_iff (χ : PontryaginDual Jₛ) (p : B⁺ × B⁻) :
    p ∈ sLocalPolarFreeMatching (F := F) (S := S) χ ↔ p ∈ sLocalZetaMatching (F := F) (S := S) χ ∧
      ∀ s ∈ leftHalf, 0 ≤ meromorphicOrderAt (fun z ↦ ρₛ(χ, z) * p.2.val z) s := by
  refine and_congr_right fun hp => ?_
  exact mem_sLocalPolarFreeMatching_iff_aux (fun z ↦ ρₛ(χ, z)) p.1.val p.2.val
    (sLocalRhoFactor_meromorphic χ)
    (p.1.property.2.1.analyticOnNhd (isOpen_Ioi.preimage Complex.continuous_re))
    (p.2.property.2.1.analyticOnNhd (isOpen_Iio.preimage Complex.continuous_re))
    ((mem_sLocalZetaMatching χ p).mp hp)

/-- Paper: Proposition 5.4.1.4, p. 267.
The zeta pair on the polar-free quotient is a topological embedding with closed range. -/
theorem sLocalPolarFreeZetaPair_isClosedEmbedding (χ : PontryaginDual Jₛ)
    (r : RealModels) (c : ComplexModels) :
    IsClosedEmbedding (sLocalPolarFreeZetaPair (F := F) (S := S) χ r c) := by sorry

/-- Paper: Proposition 5.4.1.4, p. 267.
The image of the polar-free quotient consists exactly of the matching pairs in V. -/
theorem sLocalPolarFreeZetaPair_range (χ : PontryaginDual Jₛ)
    (r : RealModels) (c : ComplexModels) :
    ((sLocalPolarFreeZetaPair (F := F) (S := S) χ r c).range : Set (B⁺ × B⁻)) =
      sLocalPolarFreeMatching (F := F) (S := S) χ := by sorry

-- The translation formula restricts by `sLocalZetaPair_translate` and
-- `sAdelePolarFree_translate`.

-- TODO(paper-gap): (5.4.1.11) on p. 270 loses the inverse on the different in the
-- last indicator. Boundedness of the multiplier in (5.4.1.10) alone does not
-- imply the closed-range assertion for (5.4.1.12).
-- TODO(paper-gap): The lexicographic order before (5.4.1.14) on p. 270 does not
-- give the claimed inclusions of the pole sets. The limit used for the Laurent
-- coefficient on p. 271 fails at poles of order greater than its exponent.
-- TODO(paper-gap): The proof of (5.4.1.22) on p. 273 needs a comparison of the
-- quotient topologies. The proposed family in (5.4.1.23) fails to span: at two
-- real places with trivial character and cutoff (0,0) it gives one test. The
-- product Gaussian has a double pole at zero. Dilating one factor by 2 adds
-- log(2) times its leading Laurent coefficient to its residue, giving two
-- independent principal parts. The range theorem needs another argument.

-- TODO(paper-gap): Remark 5.4.1.5 on p. 274 cites part (4) of a theorem with two parts.
-- The local Fréchet assertion is part (2). The global assertion is Corollary
-- 6.2.1.2, via Theorem 6.2.1.1 on isotypes for S with trivial S-class group
-- containing the character's ramification.

end SecondStructure

section Cech

-- The quotient measure in §3.3 is defined with this Borel measurable structure.
local instance instSIdeleQuotientMeasurableSpaceSec4 : MeasurableSpace Jₛ := borel _

local instance instSIdeleGroupLocallyCompactSec4 : LocallyCompactSpace Aₛˣ :=
  (sIdeleGroup_description F S).2.2.1

local instance instSIdeleQuotientT2Sec4 : T2Space Jₛ :=
  letI := isClosed_sProjectedDiagonal (F := F) (S := S)
  inferInstance

local notation "Θₛ" => SLocalAdelicThetaSpace F S
local notation "μₛ" => sLocalQuotientTamagawaMeasure F S
local notation "μweighted" => ((μₛ).withDensity (fun g : Jₛ ↦ ENNReal.ofReal (normℝ(mₛ g))))
local notation "L²ₛ" => MeasureTheory.Lp ℂ 2 μweighted
local notation "Ẽ(" I ")" => ModulatedExponentialDecay (⟨mₛ, hmₛ⟩ : Jₛ →ₜ* ℝ≥0ˣ) I
local notation "reflect(" I ")" => ((fun a : ℝ ↦ 1 - a) ⁻¹' I)

/-- Paper: (5.4.2.1), p. 274.
The ordinary theta quotient injects continuously into L² for the norm-weighted
quotient Tamagawa measure. The map keeps the almost-everywhere class of the theta
function attached to a test representative. -/
theorem existsUnique_sLocalThetaWeightedL2 :
    ∃! j : Θₛ →L[ℂ] L²ₛ, Injective j ∧ ∀ f : ℬₛ,
      ((j (Submodule.Quotient.mk f)) : Jₛ → ℂ) =ᵐ[μweighted] sLocalAdelicThetaOnClasses F S f := by sorry

local notation "weightedTheta" =>
  (show Θₛ →L[ℂ] L²ₛ from (existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose)

/-- The L² norm for a measure with a real density is the square root of the weighted
integral of the squared absolute value of any representative. -/
private theorem sLocalThetaWeightedL2_norm_aux {X : Type*} [MeasurableSpace X] (μ : Measure X) (w : X → ℝ)
    (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (F : Lp ℂ 2 (μ.withDensity fun x ↦ ENNReal.ofReal (w x))) (θ : X → ℂ)
    (hF : (F : X → ℂ) =ᵐ[μ.withDensity fun x ↦ ENNReal.ofReal (w x)] θ) :
    ‖F‖ = Real.sqrt (∫ x, ‖θ x‖ ^ 2 * w x ∂μ) := by
  rw [Lp.norm_def, (Lp.memLp F).eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ ↦ by positivity) _),
    Real.sqrt_eq_rpow, ENNReal.toReal_ofNat, one_div]
  congr 1
  rw [integral_congr_ae (hF.mono fun x (hx : F x = θ x) ↦
      show ‖F x‖ ^ (2 : ℝ) = ‖θ x‖ ^ (2 : ℝ) by rw [hx]),
    integral_withDensity_eq_integral_toReal_smul hw.ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun x ↦ ?_)
  simp only [ENNReal.toReal_ofReal (hw0 x), Real.rpow_two, smul_eq_mul, mul_comm]

/-- Paper: (5.4.2.1), p. 274.
The norm of the embedded class equals the square root of the weighted integral
of the squared absolute value of its theta function. -/
theorem sLocalThetaWeightedL2_norm (f : ℬₛ) :
    ‖weightedTheta (Submodule.Quotient.mk f)‖ =
      Real.sqrt (∫ g : Jₛ, ‖sLocalAdelicThetaOnClasses F S f g‖ ^ 2 *
        normℝ(mₛ g) ∂μₛ) := by
  have h := (existsUnique_sLocalThetaWeightedL2 (F := F) (S := S)).exists.choose_spec.2 f
  have hc : Continuous fun g : Jₛ ↦ normℝ(mₛ g) :=
    NNReal.continuous_coe.comp (Units.continuous_val.comp hmₛ)
  have : BorelSpace Jₛ := ⟨rfl⟩
  exact sLocalThetaWeightedL2_norm_aux μₛ (fun g ↦ normℝ(mₛ g)) hc.measurable
    (fun _ ↦ NNReal.coe_nonneg _) _ _ h

variable (F S) in
/-- Paper: (5.4.2.2), p. 274.
The weighted Hilbert completion is realized as the closure of the theta image
in the weighted L² space.

Kept as an `abbrev` for now (#5398): as a `def` with its own instances it breaks proofs and
statements that use it, see the issue. Do not copy this pattern: a new type synonym with
structure is a `def` with its own instances (`AGENTS.md`). -/
abbrev SLocalThetaL2 :=
  ↥(LinearMap.range ((weightedTheta).toLinearMap)).topologicalClosure

local notation "completionMap" => (show Θₛ →ₗ[ℂ] SLocalThetaL2 F S from
  (weightedTheta).toLinearMap.codRestrict
    (LinearMap.range (weightedTheta).toLinearMap).topologicalClosure
    (fun x ↦ Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)))

section DenseHelper
variable {M N : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
  [TopologicalSpace N] [ContinuousAdd N] [ContinuousConstSMul ℂ N]

private theorem denseRange_codRestrict_topologicalClosure (f : M →ₗ[ℂ] N)
    (h : ∀ x, f x ∈ (LinearMap.range f).topologicalClosure) :
    DenseRange (f.codRestrict (LinearMap.range f).topologicalClosure h) := by
  rw [DenseRange, Topology.IsInducing.subtypeVal.dense_iff]
  intro x
  rw [← Set.range_comp]
  exact x.2

end DenseHelper

/-- Paper: (5.4.2.2), p. 274.
The test-function image is dense in the chosen model of the completion. -/
theorem sLocalThetaL2_dense : DenseRange completionMap :=
  denseRange_codRestrict_topologicalClosure _ _

/-- Paper: (5.4.2.1)–(5.4.2.2), p. 274.
S-local Fourier transform has a unique unitary extension to the weighted completion,
given on theta classes by Fourier transform of the test representative. -/
theorem existsUnique_sLocalThetaL2Fourier :
    ∃! e : SLocalThetaL2 F S ≃ₗᵢ[ℂ] SLocalThetaL2 F S, ∀ f : ℬₛ,
      e (completionMap (Submodule.Quotient.mk f)) =
        completionMap (Submodule.Quotient.mk (Fourierₛ f)) := by sorry

local notation "weightedFourier" =>
  (show SLocalThetaL2 F S ≃ₗᵢ[ℂ] SLocalThetaL2 F S from
    (existsUnique_sLocalThetaL2Fourier (F := F) (S := S)).exists.choose)

local notation "decayEval(" I ", " g ")" =>
  (LinearMap.proj (g : Jₛ)).comp (modulatedExponentialDecaySubmodule
    (⟨mₛ, hmₛ⟩ : Jₛ →ₜ* ℝ≥0ˣ) (I)).subtype

/-- Paper: (5.4.2.3), p. 275.
The norm-one isotype in the weighted Schwartz–Bruhat space is the common
eigenspace for inverse left translation. -/
def sLocalDecayIsotype (I : Set ℝ) (ω : PontryaginDual J₁) : Submodule ℂ Ẽ(I) :=
  ⨅ u : J₁, ⨅ g : Jₛ, LinearMap.ker
    (decayEval(I, u.val⁻¹ * g) - (ω u : ℂ) • decayEval(I, g))

local notation "Eω(" I ", " ω ")" => ↥(sLocalDecayIsotype (F := F) (S := S) (I) (ω))

/-- Paper: (5.4.2.3), p. 275.
A weighted test function lies in the isotype exactly when it obeys the
norm-one translation law at every idele class. -/
theorem mem_sLocalDecayIsotype (I : Set ℝ) (ω : PontryaginDual J₁) (φ : Ẽ(I)) :
    φ ∈ sLocalDecayIsotype (F := F) (S := S) I ω ↔
      ∀ (u : J₁) (g : Jₛ), φ.val (u.val⁻¹ * g) = (ω u : ℂ) * φ.val g := by
  have criterion {U X E : Type _} [AddCommGroup E] [Module ℂ E]
      (ev : X → E →ₗ[ℂ] ℂ) (shift : U → X → X) (c : U → ℂ) (f : E) :
      f ∈ (⨅ u, ⨅ x, LinearMap.ker (ev (shift u x) - c u • ev x)) ↔
        ∀ u x, ev (shift u x) f = c u * ev x f := by
    simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul, sub_eq_zero]
  exact criterion (fun g : Jₛ ↦ decayEval(I, g)) (fun (u : J₁) g ↦ u.val⁻¹ * g)
    (fun u ↦ (ω u : ℂ)) φ

/-- A submodule cut out by the coordinate translation law is the isotype of any action
realizing inverse translation on coordinates. -/
private theorem sLocalDecayIsotype_eq_actionIsotype_aux {H E : Type*} [Group H]
    [TopologicalSpace H] [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] (K : Subgroup H)
    (val : E → H → ℂ) (hval : Injective val)
    (hsmul : ∀ (c : ℂ) (f : E), val (c • f) = c • val f) (P : Submodule ℂ E)
    (ω : PontryaginDual K)
    (hP : ∀ φ, φ ∈ P ↔ ∀ (u : K) (g : H), val φ (u.val⁻¹ * g) = (ω u : ℂ) * val φ g)
    (A : H →* (E →L[ℂ] E)) (hA : ∀ (g : H) (f : E) (x : H), val (A g f) x = val f (g⁻¹ * x)) :
    P = actionIsotype (A.comp K.subtype) ω := by
  ext φ
  rw [hP, mem_actionIsotype]
  refine forall_congr' fun u ↦ ⟨fun h ↦ hval (funext fun x ↦ ?_), fun h g ↦ ?_⟩
  · rw [MonoidHom.comp_apply, Subgroup.coe_subtype, hA, h, hsmul, Pi.smul_apply,
      smul_eq_mul]
  · have hg := congrFun (congrArg val h) g
    rwa [MonoidHom.comp_apply, Subgroup.coe_subtype, hA, hsmul, Pi.smul_apply,
      smul_eq_mul] at hg

/-- Paper: (5.4.2.3), p. 275, and Proposition D.3.3.12, p. 811.
The coordinate equations give the Appendix D isotype for its translation action. -/
theorem sLocalDecayIsotype_eq_actionIsotype (I : Set ℝ) (ω : PontryaginDual J₁)
    (A : Jₛ →* (Ẽ(I) →L[ℂ] Ẽ(I)))
    (hA : ∀ (g : Jₛ) (f : Ẽ(I)) (x : Jₛ), (A g f).val x = f.val (g⁻¹ * x)) :
    sLocalDecayIsotype (F := F) (S := S) I ω = actionIsotype (A.comp (mₛ).ker.subtype) ω := by
  have hP := mem_sLocalDecayIsotype (F := F) (S := S) I ω
  have hsmul : ∀ (c : ℂ) (f : Ẽ(I)),
      (fun φ : Ẽ(I) ↦ φ.val) (c • f) = c • (fun φ : Ẽ(I) ↦ φ.val) f := fun _ _ ↦ rfl
  have hval : Injective (fun φ : Ẽ(I) ↦ φ.val) := fun _ _ h ↦ Subtype.ext h
  have key := sLocalDecayIsotype_eq_actionIsotype_aux (mₛ).ker (fun φ : Ẽ(I) ↦ φ.val) hval hsmul
  with_reducible_and_instances exact key _ ω hP A hA

/-- Paper: Proposition 5.4.2.1(1), p. 275.
Fourier transform extends uniquely between the weighted isotype and the conjugate
isotype for the reflected exponent interval. Its value on each embedded homogeneous
theta function is the homogeneous theta function of the Fourier-transformed test.
Deviation: The extension identity uses the two isotypes of the theta quotient. -/
theorem existsUnique_sLocalDecayFourier (χ : PontryaginDual Jₛ) (I : Set ℝ) (_hOpen : IsOpen I)
    (_hInt : OrdConnected I) (_hne : I.Nonempty) (_hsub : I ⊆ overlapInterval) :
    let domain : Submodule ℂ Ẽ(I) := sLocalDecayIsotype (F := F) (S := S) I (restrict₁(χ))
    let codomain : Submodule ℂ Ẽ(reflect(I)) :=
      sLocalDecayIsotype (F := F) (S := S) (reflect(I)) (restrict₁(χ⁻¹))
    ∃! e : domain ≃L[ℂ] codomain,
      let transform : domain → codomain := e
      ∀ f : ℬₛ, ∃ (u : domain) (v : codomain), transform u = v ∧
        (∀ g : Jₛ, u.val.val g = φω(restrict₁(χ)) f g) ∧
        (∀ g : Jₛ, v.val.val g = φω(restrict₁(χ⁻¹)) (Fourierₛ f) g) := by sorry

/-- Paper: Proposition 5.4.2.1(2), p. 275.
If the exponent interval contains one half, the weighted Schwartz–Bruhat space
injects continuously into the theta completion by its almost-everywhere values. -/
theorem existsUnique_sLocalDecayToThetaL2 (I : Set ℝ) (_hOpen : IsOpen I)
    (_hInt : OrdConnected I) (_hsub : I ⊆ overlapInterval) (_hhalf : (1 / 2 : ℝ) ∈ I) :
    ∃! j : Ẽ(I) →L[ℂ] SLocalThetaL2 F S, Injective j ∧ ∀ f : Ẽ(I),
      (((j f).val : L²ₛ) : Jₛ → ℂ) =ᵐ[μweighted] f.val := by sorry

/-- Paper: Proposition 5.4.2.1(2), p. 275.
The unitary Fourier extension agrees on the weighted isotype with the Fourier map
for the reflected interval, after embedding both functions by their L² classes. -/
theorem sLocalDecayFourier_eq_weightedFourier (χ : PontryaginDual Jₛ) (I : Set ℝ) (hOpen : IsOpen I)
    (hInt : OrdConnected I) (hsub : I ⊆ overlapInterval) (hhalf : (1 / 2 : ℝ) ∈ I) :
    let j := (existsUnique_sLocalDecayToThetaL2 (F := F) (S := S)
      I hOpen hInt hsub hhalf).exists.choose
    let e := (existsUnique_sLocalDecayFourier (F := F) (S := S) χ I hOpen hInt ⟨_, hhalf⟩ hsub).exists.choose
    ∀ f : Eω(I, restrict₁(χ)),
      ((((weightedFourier (j f.val)).val : L²ₛ) : Jₛ → ℂ)) =ᵐ[μweighted] (e f).val.val :=
  by sorry

-- TODO(paper-gap): Theorem 5.4.2.2(2) prints incompatible intervals for J_τ.
-- In (3) the asserted half-plane map has poles, already at zero for the trivial
-- character over ℚ with no finite places. In (4) the printed operator omits
-- reflection and applies this multiplier on the entire positive half-plane.
-- Restriction to the overlap gives the continuous difference in the diagram below.
-- In (1), the conjugate character requires the opposite shift when x₀ ≠ 0.

/-- Paper: Theorem 5.4.2.2(2), p. 276.
Radial inversion, with the compact coordinate fixed, exchanges the two weight intervals.
Deviation: The target exponent interval is the reflection of the source interval. -/
theorem existsUnique_sLocalCechRadialReflection (τ : ℝ≥0ˣ →ₜ* Jₛ)
    (_hτ : RightInverse τ mₛ) (ω : PontryaginDual J₁) :
    ∃! J : Eω(rightInterval, ω) ≃L[ℂ] Eω(leftInterval, ω),
      ∀ (f : Eω(rightInterval, ω)) (t : ℝ≥0ˣ) (k : J₁),
        (J f).val.val (τ t * k.val) =
          ((normℝ(t) : ℂ)⁻¹) * f.val.val (τ t⁻¹ * k.val) := by sorry

local notation "upperMiddle(" χ ")" => Eω(rightInterval, restrict₁(χ)) × Eω(rightInterval, restrict₁(χ⁻¹))

/-- Paper: (5.4.2.6), p. 276.
The upper left arrow pairs the two homogeneous theta functions attached to
a test and to its S-adelic Fourier transform. -/
theorem existsUnique_sLocalCechThetaPair (χ : PontryaginDual Jₛ) :
    ∃! U : Θω(restrict₁(χ)) →L[ℂ] upperMiddle(χ), ∀ f : ℬₛ,
      (U (Submodule.Quotient.mk f)).1.val.val = ⇑(φω(restrict₁(χ)) f) ∧
      (U (Submodule.Quotient.mk f)).2.val.val = ⇑(φω(restrict₁(χ⁻¹)) (Fourierₛ f)) := by sorry

local notation "cechThetaPair(" χ ")" => (show Θω(restrict₁(χ)) →L[ℂ] upperMiddle(χ) from
  (existsUnique_sLocalCechThetaPair (F := F) (S := S) χ).exists.choose)

/-- Paper: (5.4.2.6), p. 276.
On the lower row the right half-plane zeta pair maps to the difference of the
first entry and the reflected second entry multiplied on the overlap by the
functional-equation factor. The image of the first map is the kernel of the difference.
Deviation: The multiplier is used on the overlap where it is holomorphic. -/
theorem sLocalCechBergman_exact (χ : PontryaginDual Jₛ) :
    ∃ (U : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁺) (D : B⁺ × B⁺ →L[ℂ] B⁰),
      (∀ f : ℬₛ,
        EqOn (U (Submodule.Quotient.mk f)).1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
        EqOn (U (Submodule.Quotient.mk f)).2.val
          (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf) ∧
      (∀ p : B⁺ × B⁺,
        EqOn (D p).val (fun s ↦ p.1.val s - ρₛ(χ, s) * p.2.val (1 - s)) overlap) ∧
      Function.Exact U D := by sorry

/-- Paper: (5.4.2.6), p. 276.
In the lower row the zeta pair of the test and its Fourier transform is a
topological embedding with closed range. -/
theorem sLocalCechBergman_isClosedEmbedding (χ : PontryaginDual Jₛ) (U : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁺)
    (_hU : ∀ f : ℬₛ,
      EqOn (U (Submodule.Quotient.mk f)).1.val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
      EqOn (U (Submodule.Quotient.mk f)).2.val
        (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf) :
    IsClosedEmbedding U := by sorry

/-- Paper: Theorem 5.4.2.2, p. 276.
Restriction of a unitary character to the norm section defines a unique real
frequency in the Mellin coordinate. -/
theorem existsUnique_sLocalCechFrequency (χ : PontryaginDual Jₛ) (τ : ℝ≥0ˣ →ₜ* Jₛ) :
    ∃! x : ℝ, ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I) :=
  by
    let incl : Circle →ₜ* ℂ := ⟨Circle.coeHom, continuous_subtype_val⟩
    let c := incl.comp (χ.comp τ)
    obtain ⟨z, ⟨hz, hval⟩, huniq⟩ := existsUnique_unitaryComplexPower c
      (fun t ↦ Circle.norm_coe (χ (τ t)))
    have him : (z.im : ℂ) * Complex.I = z := by
      apply Complex.ext <;> simp [hz]
    refine ⟨z.im, fun t ↦ (hval t).trans (by rw [him]), fun x hx ↦ ?_⟩
    have he := huniq ((x : ℂ) * Complex.I) ⟨by simp, hx⟩
    simpa using congrArg Complex.im he

local notation "mellinIntegrand(" τ ", " φ ", " z ")" =>
  (fun t : ℝ≥0ˣ ↦ (φ) ((τ) t) * (normℝ(t) : ℂ) ^ (z))

/-- Paper: Theorem 5.4.2.2(1), p. 276.
On a norm-one isotype, restriction to the norm section followed by the
vertically shifted Mellin integral defines a continuous linear equivalence.
The integrals are absolutely convergent in the open strip. -/
theorem existsUnique_sLocalDecayMellin (τ : ℝ≥0ˣ →ₜ* Jₛ) (_hτ : RightInverse τ mₛ)
    (I : Set ℝ) (_hOpen : IsOpen I) (_hInt : OrdConnected I) (_hne : I.Nonempty)
    (ω : PontryaginDual J₁) (x : ℝ) :
    ∃! M : Eω(I, ω) ≃L[ℂ] SchwartzBergman I, ∀ (f : Eω(I, ω)) (s : ℂ), s.re ∈ I →
      let k := mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I)
      Integrable k positiveRealHaar ∧ (M f).val s = ∫ t, k t ∂positiveRealHaar := by sorry

/-- Paper: Theorem 5.4.2.2(6), p. 277.
The right vertical arrow is the Mellin equivalence on the overlap followed by
translation of the spectral argument by the section's imaginary frequency. -/
theorem existsUnique_sLocalCechStripMellin (x : ℝ) :
    ∃! M : PositiveRealExponentialDecay overlapInterval ≃L[ℂ] B⁰,
      ∀ f s, s ∈ overlap → (M f).val s =
        mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I) := by
  let I : Set ℝ := Ioo 0 1
  have hne : I.Nonempty := ⟨1 / 2, by norm_num [I]⟩
  -- The unimodular multiplier u ↦ exp(i y u), as a Schwartz multiplier.
  let g (y : ℝ) (u : ℝ) : ℂ := Complex.exp (((y * u : ℝ) : ℂ) * Complex.I)
  have hg (y : ℝ) : (g y).HasTemperateGrowth := by
    have h1 : (fun u : ℝ ↦ y * u).HasTemperateGrowth :=
      (y • ContinuousLinearMap.id ℝ ℝ).hasTemperateGrowth
    exact Complex.hasTemperateGrowth_exp_mul_I.comp h1
  have hmem (y : ℝ) (f : logExponentialDecaySubmodule I) :
      (fun u ↦ g y u * f.val u) ∈ logExponentialDecaySubmodule I := by
    apply (Submodule.mem_iInf _).2
    intro a
    refine ⟨SchwartzMap.smulLeftCLM ℂ (g y) (logExponentialDecayTwist I a f), ?_⟩
    funext u
    change SchwartzMap.smulLeftCLM ℂ (g y) (logExponentialDecayTwist I a f) u =
      (Real.exp ((a : ℝ) * u) : ℂ) * (g y u * f.val u)
    rw [SchwartzMap.smulLeftCLM_apply_apply (hg y), logExponentialDecayTwist_apply, smul_eq_mul]
    ring
  let mod (y : ℝ) : PositiveRealExponentialDecay I →ₗ[ℂ] PositiveRealExponentialDecay I :=
    { toFun := fun f ↦ (⟨_, hmem y f⟩ : logExponentialDecaySubmodule I)
      map_add' := fun f h ↦ Subtype.ext (funext fun u ↦ by
        change g y u * (f.val u + h.val u) = g y u * f.val u + g y u * h.val u
        ring)
      map_smul' := fun c f ↦ Subtype.ext (funext fun u ↦ by
        change g y u * (c * f.val u) = c * (g y u * f.val u)
        ring) }
  have hmod (y : ℝ) (f : PositiveRealExponentialDecay I) (u : ℝ) :
      (mod y f).val u = g y u * f.val u := rfl
  have hE := positiveRealExponentialDecay_isEmbedding I hne
  have htw (y : ℝ) (a : I) (f : PositiveRealExponentialDecay I) :
      logExponentialDecayTwist I a (mod y f) =
        SchwartzMap.smulLeftCLM ℂ (g y) (logExponentialDecayTwist I a f) := by
    ext u
    rw [SchwartzMap.smulLeftCLM_apply_apply (hg y), smul_eq_mul]
    refine (logExponentialDecayTwist_apply I a (mod y f) u).trans ?_
    refine Eq.trans ?_ (congrArg (g y u * ·) (logExponentialDecayTwist_apply I a f u)).symm
    change (Real.exp ((a : ℝ) * u) : ℂ) * (g y u * f.val u) = _
    ring
  have hcont (y : ℝ) : Continuous (mod y) := by
    apply hE.continuous_iff.mpr
    apply continuous_pi
    intro a
    exact ((SchwartzMap.smulLeftCLM ℂ (g y)).continuous.comp
      ((continuous_apply a).comp hE.continuous)).congr fun f ↦ (htw y a f).symm
  have hinv (y : ℝ) (f : PositiveRealExponentialDecay I) : mod (-y) (mod y f) = f := by
    apply Subtype.ext
    funext u
    change g (-y) u * (g y u * f.val u) = f.val u
    simp only [g]
    rw [← mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
    simp
  let P : PositiveRealExponentialDecay I ≃L[ℂ] PositiveRealExponentialDecay I :=
    { toLinearMap := mod x
      invFun := mod (-x)
      left_inv := hinv x
      right_inv := fun f ↦ by simpa using hinv (-x) f
      continuous_toFun := hcont x
      continuous_invFun := hcont (-x) }
  have hOpen : IsOpen I := isOpen_Ioo
  have hInt : OrdConnected I := ordConnected_Ioo
  have hspec := (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists.choose_spec
  let A := (existsUnique_positiveRealFourierMellin I hOpen hInt hne).exists.choose
  have hform : ∀ (f : PositiveRealExponentialDecay I) (s : ℂ), s ∈ Complex.re ⁻¹' I →
      ((P.trans A) f).val s = mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I) := by
    intro f s hs
    change (A (mod x f)).val s = _
    rw [hspec (mod x f) s hs]
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    change (t : ℂ) ^ (s - 1) • (g x (Real.log t) * f.val (Real.log t)) =
      (t : ℂ) ^ (s + x * Complex.I - 1) • f.val (Real.log t)
    have hpow : (t : ℂ) ^ (s + x * Complex.I - 1) = (t : ℂ) ^ (s - 1) * g x (Real.log t) := by
      rw [show s + x * Complex.I - 1 = (s - 1) + x * Complex.I by ring,
        Complex.cpow_add _ _ ht0]
      congr 1
      rw [Complex.cpow_def_of_ne_zero ht0, ← Complex.ofReal_log ht.le]
      simp only [g]
      push_cast
      ring_nf
    rw [hpow, smul_eq_mul, smul_eq_mul]
    ring
  refine ⟨P.trans A, hform, ?_⟩
  intro M hM
  apply ContinuousLinearEquiv.ext
  funext f
  apply Subtype.ext
  funext s
  by_cases hs : s ∈ Complex.re ⁻¹' I
  · exact (hM f s hs).trans (hform f s hs).symm
  · exact ((M f).property.1 hs).trans (((P.trans A) f).property.1 hs).symm

/-- Paper: (5.4.2.6), p. 276.
Applying the two shifted Mellin transforms to the upper left arrow gives the
lower zeta pair on every theta class.
Deviation: The first and conjugate isotypes use opposite frequency shifts. -/
theorem sLocalCech_left_commutes (χ : PontryaginDual Jₛ)
    (τ : ℝ≥0ˣ →ₜ* Jₛ) (_hτ : RightInverse τ mₛ)
    (x : ℝ) (_hx : ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I))
    (M₁ : Eω(rightInterval, restrict₁(χ)) ≃L[ℂ] B⁺)
    (M₂ : Eω(rightInterval, restrict₁(χ⁻¹)) ≃L[ℂ] B⁺)
    (_h₁ : ∀ f s, s ∈ rightHalf →
      (M₁ f).val s = ∫ t, mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I) t
        ∂positiveRealHaar)
    (_h₂ : ∀ f s, s ∈ rightHalf →
      (M₂ f).val s = ∫ t, mellinIntegrand(τ, f.val.val, s - (x : ℂ) * Complex.I) t
        ∂positiveRealHaar)
    (f : ℬₛ) :
    let p : upperMiddle(χ) := cechThetaPair(χ) (Submodule.Quotient.mk f)
    EqOn (M₁ p.1).val (fun s ↦ Zₛ f (normChart(χ) s)) rightHalf ∧
    EqOn (M₂ p.2).val (fun s ↦ Zₛ (Fourierₛ f) (normChart(χ⁻¹) s)) rightHalf := by sorry

/-- Paper: Theorem 5.4.2.2(3)–(6) and (5.4.2.6), pp. 276–277.
The upper difference is the unique continuous map whose shifted Mellin transform
is the lower difference. The upper row is exact at the pair of decay spaces.
Deviation: The correcting factor multiplies the reflected transform on the overlap. -/
theorem existsUnique_sLocalCechDifference (χ : PontryaginDual Jₛ)
    (τ : ℝ≥0ˣ →ₜ* Jₛ) (hτ : RightInverse τ mₛ) (x : ℝ)
    (_hx : ∀ t : ℝ≥0ˣ, (χ (τ t) : ℂ) = (normℝ(t) : ℂ) ^ ((x : ℂ) * Complex.I)) :
    ∀ (M₁ : Eω(rightInterval, restrict₁(χ)) ≃L[ℂ] B⁺)
      (M₂ : Eω(rightInterval, restrict₁(χ⁻¹)) ≃L[ℂ] B⁺)
      (M₀ : PositiveRealExponentialDecay overlapInterval ≃L[ℂ] B⁰),
      (∀ f s, s ∈ rightHalf → (M₁ f).val s =
        ∫ t, mellinIntegrand(τ, f.val.val, s + (x : ℂ) * Complex.I) t ∂positiveRealHaar) →
      (∀ f s, s ∈ rightHalf → (M₂ f).val s =
        ∫ t, mellinIntegrand(τ, f.val.val, s - (x : ℂ) * Complex.I) t ∂positiveRealHaar) →
      (∀ f s, s ∈ overlap → (M₀ f).val s =
        mellin (fun t ↦ f.val (Real.log t)) (s + (x : ℂ) * Complex.I)) →
    ∃! D : upperMiddle(χ) →L[ℂ] PositiveRealExponentialDecay overlapInterval,
      (∀ p : upperMiddle(χ), EqOn (M₀ (D p)).val
        (fun s ↦ (M₁ p.1).val s - ρₛ(χ, s) * (M₂ p.2).val (1 - s)) overlap) ∧
      Function.Exact cechThetaPair(χ) D := by sorry

/-- Paper: Remark 5.4.2.3 and (5.4.2.7), p. 277.
The pair of homogeneous theta functions of a test and its Fourier transform
embeds the homogeneous quotient as a closed subspace of the two weighted isotypes. -/
theorem sLocalCechThetaPair_isClosedEmbedding (χ : PontryaginDual Jₛ) : IsClosedEmbedding cechThetaPair(χ) := by
  let τ := (sIdeleQuotientNorm_exists_section F S).choose
  have hτ := (sIdeleQuotientNorm_exists_section F S).choose_spec
  let x := (existsUnique_sLocalCechFrequency χ τ).exists.choose
  have hx := (existsUnique_sLocalCechFrequency χ τ).exists.choose_spec
  have hM₁ := existsUnique_sLocalDecayMellin τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi ⟨1, by norm_num⟩ restrict₁(χ) x
  have hM₂ := existsUnique_sLocalDecayMellin τ hτ rightInterval
    isOpen_Ioi ordConnected_Ioi ⟨1, by norm_num⟩ restrict₁(χ⁻¹) (-x)
  let M₁ : Eω(rightInterval, restrict₁(χ)) ≃L[ℂ] B⁺ := hM₁.exists.choose
  let M₂ : Eω(rightInterval, restrict₁(χ⁻¹)) ≃L[ℂ] B⁺ := hM₂.exists.choose
  have h₁ := hM₁.exists.choose_spec
  have h₂ := hM₂.exists.choose_spec
  let e : upperMiddle(χ) ≃L[ℂ] B⁺ × B⁺ := M₁.prodCongr M₂
  let U : Θω(restrict₁(χ)) →L[ℂ] B⁺ × B⁺ := e.toContinuousLinearMap.comp cechThetaPair(χ)
  have hU : IsClosedEmbedding U := sLocalCechBergman_isClosedEmbedding χ U (by
    intro f
    exact sLocalCech_left_commutes χ τ hτ x hx M₁ M₂
      (fun g s hs ↦ (h₁ g s hs).2)
      (fun g s hs ↦ by simpa only [M₂, neg_mul, Complex.ofReal_neg, sub_eq_add_neg] using
        (h₂ g s hs).2) f)
  have heq : e.symm ∘ U = ⇑cechThetaPair(χ) := by
    funext z
    exact e.symm_apply_apply _
  have h := e.symm.toHomeomorph.isClosedEmbedding.comp hU
  exact heq ▸ h

end Cech

end RiemannMasullo
