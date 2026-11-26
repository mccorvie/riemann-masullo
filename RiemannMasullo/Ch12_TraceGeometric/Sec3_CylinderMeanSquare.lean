module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_CylinderPrimeComparison
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_CylinderPlancherel
public import RiemannMasullo.Ch13_ZerosHecke.DirichletZeroDisplacement
import Mathlib.Tactic

/-! # Unconditional mean square of the signed cylinder comparison

A half-plane Blaschke bound and the functional equation give an inverse-square
height estimate uniform in the conductor. Plancherel on the residue group then
bounds the signed discrepancy at every strip width in quadratic mean.
-/

@[expose] public noncomputable section

open Classical Filter Function Set
open scoped ComplexConjugate ContDiff Topology

namespace RiemannMasullo.ConductorCylinder

open ConductorDensity RationalConductor

set_option quotPrecheck false

local notation "Zstrip" => {z : ℂ // 0 < z.re ∧ z.re < 1}
local notation "ord(" χ ", " z ")" => completedPrimitiveOrder (χ,z)
local notation "height(" z ")" => (1+|(z : Zstrip).val.im|)^2
local notation "sample(" H ", " z ")" => bilateralLaplace H ((z : Zstrip).val-1/2)

/-- For a nonprincipal character the completed primitive multiplicity in the
open strip is the analytic order of the ordinary L-function at level `q`. -/
theorem primitiveOrder_eq_analyticOrder {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (z : Zstrip) : ord(χ,z) = analyticOrderNatAt χ.LFunction z.val := by
  rw [← ordinaryOrder_eq_completedPrimitiveOrder]
  have h := (χ.differentiable_LFunction hχ).analyticAt z.val
  unfold ordinaryOrder analyticOrderNatAt
  rw [h.meromorphicOrderAt_eq]
  rcases eq_or_ne (analyticOrderAt χ.LFunction z.val) ⊤ with ht | ht
  · rw [ht]; rfl
  · obtain ⟨n,hn⟩ := ENat.ne_top_iff_exists.mp ht
    rw [← hn, ENat.map_natCast, ENat.toNat_natCast, WithTop.untop₀_coe, Int.toNat_natCast]

private def rightMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (z : Zstrip) : ℝ :=
  if 1/2 ≤ z.val.re then (ord(χ,z) : ℝ) / height(z) else 0

private theorem right_mass_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    Summable (rightMass χ) ∧ ∑' z, rightMass χ z ≤ 16 * Real.log (16 * (q:ℝ)) := by
  let Z := {ρ : ℂ // 1/2 ≤ ρ.re ∧ ρ.re < 1 ∧ χ.LFunction ρ = 0}
  let e (ρ : Z) : Zstrip := ⟨ρ.val, by linarith [ρ.property.1], ρ.property.2.1⟩
  have hi : Injective e := fun _ _ he ↦ Subtype.ext (congrArg (fun z : Zstrip ↦ z.val) he)
  have hcomp (ρ : Z) : rightMass χ (e ρ) = (analyticOrderNatAt χ.LFunction ρ.val : ℝ) /
      (1+|ρ.val.im|)^2 := by
    unfold rightMass
    rw [ite_eq_left (show 1/2 ≤ (e ρ).val.re from ρ.property.1), primitiveOrder_eq_analyticOrder χ hχ]
  have hcover : support (rightMass χ) ⊆ range e := by
    intro z hz
    by_cases h : 1/2 ≤ z.val.re
    · refine ⟨⟨z.val,h,z.property.2,?_⟩,rfl⟩
      by_contra hne
      have ho := ((χ.differentiable_LFunction hχ).analyticAt z.val).analyticOrderAt_eq_zero.mpr hne
      exact hz (by rw [rightMass, ite_eq_left h, primitiveOrder_eq_analyticOrder χ hχ]; simp [analyticOrderNatAt,ho])
    · exact (hz (by rw [rightMass, ite_eq_right h])).elim
  obtain ⟨hs,hb⟩ := dirichletLFunction_right_halfStrip_height_mass χ hχ
  have hS : Summable (rightMass χ ∘ e) := hs.congr (fun ρ ↦ (hcomp ρ).symm)
  refine ⟨(hi.summable_iff (fun x hx ↦ notMem_support.mp (mt (@hcover x) hx))).mp hS,?_⟩
  rw [← hi.tsum_eq hcover]
  exact (tsum_congr hcomp).le.trans hb

private def flip (z : Zstrip) : Zstrip := (reflect ((1 : DirichletCharacter ℂ 1),z)).2

private theorem flip_involutive : Involutive flip := fun z ↦
  Subtype.ext (by change 1-(1-z.val) = _; ring)

/-- Independently of the character, the entire primitive divisor weighted by
inverse square height has logarithmic mass for nonprincipal rows. -/
theorem primitiveOrder_height_mass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    let w (z : Zstrip) := (ord(χ,z) : ℝ) / height(z)
    Summable w ∧ ∑' z, w z ≤ 32 * Real.log (16 * (q:ℝ)) := by
  intro w
  let e : Zstrip ≃ Zstrip := ⟨flip,flip,flip_involutive,flip_involutive⟩
  obtain ⟨h₁,b₁⟩ := right_mass_bound χ hχ
  obtain ⟨h₂,b₂⟩ := right_mass_bound χ⁻¹ (inv_ne_one.mpr hχ)
  have he : Summable (fun z ↦ rightMass χ⁻¹ (e z)) := h₂.comp_injective e.injective
  have hpos (ψ : DirichletCharacter ℂ q) (z : Zstrip) : 0 ≤ rightMass ψ z := by
    unfold rightMass; split_ifs <;> positivity
  have hb (z : Zstrip) : w z ≤ rightMass χ z + rightMass χ⁻¹ (e z) := by
    by_cases h : 1/2 ≤ z.val.re
    · rw [rightMass, ite_eq_left h]
      exact le_add_of_nonneg_right (hpos _ _)
    · have hre : 1/2 ≤ (e z).val.re := by change 1/2 ≤ (1-z.val).re; simp; linarith
      have him : |(e z).val.im| = |z.val.im| := by change |(1-z.val).im| = _; simp
      have ho : ord(χ⁻¹,e z) = ord(χ,z) := completedPrimitiveOrder_reflect (χ,z)
      simp only [w,rightMass,ite_eq_right h,ite_eq_left hre,him,ho,zero_add,le_refl]
  have hw : Summable w := (h₁.add he).of_nonneg_of_le (fun z ↦ div_nonneg (Nat.cast_nonneg _) (sq_nonneg _)) hb
  refine ⟨hw,(hw.tsum_le_tsum hb (h₁.add he)).trans ?_⟩
  rw [h₁.tsum_add he, e.tsum_eq (rightMass χ⁻¹)]
  linarith

private theorem principal_order (q : ℕ) [NeZero q] (z : Zstrip) :
    ord((1 : DirichletCharacter ℂ q),z) = ord((1 : DirichletCharacter ℂ 1),z) := by
  unfold completedPrimitiveOrder
  simp only [DirichletCharacter.primitiveCharacter_one]
  have he (k : ℕ) [NeZero k] (hk : k = 1) :
      DirichletCharacter.completedLFunction (1 : DirichletCharacter ℂ k) =
        DirichletCharacter.completedLFunction (1 : DirichletCharacter ℂ 1) := by subst k; rfl
  let (n : ℕ) [NeZero n] : NeZero (1 : DirichletCharacter ℂ n).conductor :=
    ⟨(1 : DirichletCharacter ℂ n).conductor_ne_zero⟩
  rw [he _ (@DirichletCharacter.conductor_one ℂ _ q _), he _ (@DirichletCharacter.conductor_one ℂ _ 1 _)]

/-- Mellin sample of the primitive multiplicities omitted by the actual
Hilbert strip trace. At a boundary point only the lost jets contribute. -/
def signedOmittedRow {q : ℕ} [NeZero q] (a s : ℝ) (H : ℝ → ℂ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑' z : Zstrip, ((ord(χ,z) - spectralStripMultiplicity a s (z.val.re-1/2) (ord(χ,z)) : ℕ) : ℂ) *
    sample(H,z)

private theorem norm_omitted_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a s : ℝ)
    (H : ℝ → ℂ) (hsum : Summable (fun z : Zstrip ↦ (ord(χ,z) : ℝ) * ‖sample(H,z)‖)) :
    ‖signedOmittedRow a s H χ‖ ≤ ∑' z : Zstrip, (ord(χ,z) : ℝ) * ‖sample(H,z)‖ := by
  let v (z : Zstrip) := ((ord(χ,z) - spectralStripMultiplicity a s (z.val.re-1/2) (ord(χ,z)) : ℕ) : ℂ) *
    sample(H,z)
  have hb (z : Zstrip) : ‖v z‖ ≤ (ord(χ,z) : ℝ) * ‖sample(H,z)‖ := by
    dsimp only [v]
    rw [norm_mul, Complex.norm_natCast]
    gcongr
    exact Nat.sub_le ..
  have hs := hsum.of_nonneg_of_le (fun z ↦ norm_nonneg (v z)) hb
  exact (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum hb hsum)

/-- The absolute primitive Mellin mass on each nonprincipal Dirichlet row is
bounded logarithmically in the modulus. The constant depends only on the
profile. Zero density and the location of any individual zero are unnecessary. -/
theorem primitiveRow_mellin_mass {H : ℝ → ℂ} (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      let v (z : Zstrip) := (ord(χ,z) : ℝ)*‖sample(H,z)‖
      Summable v ∧ ∑' z, v z ≤ K * Real.log (16*(q:ℝ)) := by
  obtain ⟨C,hC,h₀⟩ := fixed_profile_quadratic_decay hd hc (1/2)
  refine ⟨32*C, by positivity, ?_⟩
  intro q _ χ hχ v
  obtain ⟨hs,hb⟩ := primitiveOrder_height_mass χ hχ
  let w (z : Zstrip) := (ord(χ,z) : ℝ)/height(z)
  have hw : Summable (fun z ↦ C*w z) := hs.mul_left _
  have hcomp (z : Zstrip) : v z ≤ C*w z := by
    have hr : |(z.val-1/2).re| ≤ 1/2 := by
      simp only [Complex.sub_re, Complex.div_ofNat_re, Complex.one_re]
      exact abs_le.mpr ⟨by linarith [z.property.1], by linarith [z.property.2]⟩
    have he := h₀ (z.val-1/2) hr
    rw [show (z.val-1/2).im = z.val.im by simp] at he
    dsimp only [v,w]
    calc _ ≤ (ord(χ,z) : ℝ) * (C / height(z)) := mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
         _ = _ := by ring
  have hv := hw.of_nonneg_of_le (fun z ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) hcomp
  refine ⟨hv,(hv.tsum_le_tsum hcomp hw).trans ?_⟩
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hb hC).trans_eq (by ring)

/-- Uniform bound for every row, including the principal character and
arbitrary Sobolev edge multiplicities. -/
theorem norm_signedOmittedRow_le {H : ℝ → ℂ} (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (hp : tsupport H ⊆ Ioi 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (a s : ℝ),
      ‖signedOmittedRow a s H χ‖ ≤ K * (1+Real.log (16*(q:ℝ))) := by
  obtain ⟨C,hC,h₀⟩ := primitiveRow_mellin_mass hd hc
  let V (z : Zstrip) := (ord((1 : DirichletCharacter ℂ 1),z) : ℝ)*‖sample(H,z)‖
  have hV : Summable V := by
    have h := (hasSum_shifted_primitive_positiveLog (1 : DirichletCharacter ℂ 1) (1/2) H hd hc hp).summable.norm
    simpa only [V,norm_mul,Complex.norm_natCast,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using h
  have hP : 0 ≤ ∑' z, V z := tsum_nonneg (fun z ↦ mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  refine ⟨C+∑' z,V z, add_nonneg hC hP, ?_⟩
  intro q _ χ a s
  have hq : (1:ℝ) ≤ q := by exact_mod_cast NeZero.pos q
  have hl : 0 ≤ Real.log (16*(q:ℝ)) := Real.log_nonneg (by linarith)
  by_cases hχ : χ = 1
  · subst χ
    have he (z : Zstrip) : (ord((1 : DirichletCharacter ℂ q),z) : ℝ)*‖sample(H,z)‖ = V z := by rw [principal_order q]
    have hb := norm_omitted_le (1 : DirichletCharacter ℂ q) a s H (hV.congr (fun z ↦ (he z).symm))
    rw [tsum_congr he] at hb
    exact hb.trans (by nlinarith [mul_nonneg hC hl, mul_nonneg hP hl])
  · obtain ⟨hs,hb⟩ := h₀ q χ hχ
    exact (norm_omitted_le χ a s H hs).trans (hb.trans (by nlinarith [mul_nonneg hP hl]))

/-- The total squared signed error over all residues is logarithmic squared
at every modulus, uniformly in the strip width and edge order. Dividing by
φ(q) gives the mean square per residue. -/
theorem sum_norm_sq_signedOmitted_le {H : ℝ → ℂ} (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H)
    (hp : tsupport H ⊆ Ioi 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : ℕ) [NeZero q] (a s : ℝ),
      ∑ r : (ZMod q)ˣ, ‖cylinderAverage q r (signedOmittedRow a s H)‖^2 ≤
        (K*(1+Real.log (16*(q:ℝ))))^2 := by
  obtain ⟨K,hK,h⟩ := norm_signedOmittedRow_le hd hc hp
  refine ⟨K,hK,?_⟩
  intro q _ a s
  rw [sum_norm_sq_cylinderAverage, div_le_iff₀ (Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q)))]
  calc _ ≤ ∑ _ : DirichletCharacter ℂ q, (K*(1+Real.log (16*(q:ℝ))))^2 :=
          Finset.sum_le_sum (fun χ _ ↦ pow_le_pow_left₀ (norm_nonneg _) (h q χ a s) 2)
       _ = _ := by simp [← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity, mul_comm]

end RiemannMasullo.ConductorCylinder
