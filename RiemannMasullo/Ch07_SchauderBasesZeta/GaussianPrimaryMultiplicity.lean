module

public import RiemannMasullo.Ch03_IdelicZeta.GaussianAngularCharacter
public import RiemannMasullo.Ch07_SchauderBasesZeta.Sec3a
import RiemannMasullo.Ch07_SchauderBasesZeta.GaussianStage

/-!
# Primary orbital indices of the Gaussian angular character

The two Gaussian primes of norm five have different uniformizer values. A norm
twist changes both by the same scalar, so each rational-prime fibre contributes
at most one finite pole place at a given character on the angular component.
-/

public section

namespace RiemannMasullo.Gaussian

open IsDedekindDomain NumberField NumberField.Gaussian
open scoped NNReal

set_option quotPrecheck false

local notation "K" => CyclotomicField 4 ℚ
local notation "J" => SIdeleQuotient K finitePlaces
local notation "M" => sIdeleQuotientNorm K finitePlaces
local notation "J₁" => (M).ker
local notation "mCont" => (isProperMap_sIdeleQuotientNorm K finitePlaces).continuous
local notation "Cχ(" χ ")" => (⟨Circle.coeHom, continuous_subtype_val⟩ : Circle →ₜ* ℂ).comp (χ)
local notation "chart(" χ ")" => quasiCharacterNormTwist (G := J) M mCont (Cχ(χ))

private theorem gaussian_member_cases (v : finitePlaces) :
    v = threeMember ∨ v = plusMember ∨ v = minusMember := by
  rcases (mem_finitePlaces v.val).mp v.prop with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

/-- The local pole criterion expressed using the chosen Gaussian prime generator. -/
private theorem angularCharacter_pole_equation (v : finitePlaces) (a : ℂ)
    (ha : v ∈ sLocalFinitePolePlaces (chart(angularCharacter) a)) :
    sLocalFiniteRestriction v (chart(angularCharacter) 0) (primeUniformizer v) *
        (((v.val.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ a = 1 := by
  let E (c : QuasiCharacter J) (z : ℂ) :=
    finiteLocalEulerFactor v.val (sLocalFiniteRestriction v (quasiCharacterNormTwist M mCont c z))
  have hh : E (chart(angularCharacter) a) = E (Cχ(angularCharacter)) ∘ (· + a) := by
    funext z
    apply congrArg (fun c ↦ finiteLocalEulerFactor v.val (sLocalFiniteRestriction v c))
    ext1 g
    let n : ℂ := (((M g : ℝ≥0) : ℝ) : ℂ)
    change (Cχ(angularCharacter)) g * n ^ a * n ^ z = (Cχ(angularCharacter)) g * n ^ (z + a)
    rw [add_comm z a, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
      (NNReal.coe_ne_zero.mpr (M g).ne_zero)), mul_assoc]
  have hE := (Finset.mem_filter.mp ha).2
  change meromorphicOrderAt (E (chart(angularCharacter) a)) 0 < 0 at hE
  rw [hh, meromorphicOrderAt_comp_add_const_eq_meromorphicOrderAt, zero_add] at hE
  have hT := (sLocalRhoPoleOrder_eq_card_polePlaces_finite angularCharacter v a).mp hE
  let ψ := sLocalFiniteRestriction v (chart(angularCharacter) 0)
  have hψ (x : (v.val.adicCompletion K)ˣ) : ‖ψ x‖ = 1 := by
    change ‖((angularCharacter _ : Circle) : ℂ) * _ ^ (0 : ℂ)‖ = 1
    simp
  obtain ⟨π, hπ, h₀⟩ := sLocalRhoFactor_poles_iff_finite angularCharacter v
  have hlat := (sLocalRhoFactor_poles_iff_finite_explicit v.val ψ hψ π hπ a).mp ((h₀ a).2.1.mp hT)
  have h := ((sLocalRhoFactor_poles_iff_finite_explicit v.val ψ hψ (primeUniformizer v)
    (norm_primeUniformizer v) a).mpr hlat).2
  simpa only [norm_primeUniformizer] using h

private theorem angularCharacter_split_centers_disjoint (a : ℂ) :
    ¬ (plusMember ∈ sLocalFinitePolePlaces (chart(angularCharacter) a) ∧
      minusMember ∈ sLocalFinitePolePlaces (chart(angularCharacter) a)) := by
  rintro ⟨hp, hm⟩
  have h₁ := angularCharacter_pole_equation plusMember a hp
  have h₂ := angularCharacter_pole_equation minusMember a hm
  rw [angularCharacter_two_add_i] at h₁
  rw [angularCharacter_two_sub_i] at h₂
  change _ * (((plusPlace.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ a = 1 at h₁
  change _ * (((minusPlace.asIdeal.absNorm : ℝ)⁻¹ : ℝ) : ℂ) ^ a = 1 at h₂
  rw [absNorm_plusPlace] at h₁
  rw [absNorm_minusPlace] at h₂
  let t : ℂ := (((5 : ℝ)⁻¹ : ℝ) : ℂ) ^ a
  change _ * t = 1 at h₁ h₂
  have ht : t ≠ 0 := fun h ↦ zero_ne_one (by simpa only [h, mul_zero] using h₁)
  have hi := congrArg Complex.im (mul_right_cancel₀ ht (h₁.trans h₂.symm))
  norm_num [Complex.div_im, Complex.normSq_apply] at hi

private theorem angularCharacter_component_chart_exists (c : QuasiCharacter J)
    (hc : ∀ y : J₁, c y.val = (Cχ(angularCharacter)) y.val) : ∃ z : ℂ, chart(angularCharacter) z = c := by
  obtain ⟨σ, hσ⟩ := sIdeleQuotientNorm_exists_section K finitePlaces
  let b : QuasiCharacter J := Cχ(angularCharacter)
  obtain ⟨u, hu, -⟩ := existsUnique_complexPower (b.comp σ)
  obtain ⟨v, hv, -⟩ := existsUnique_complexPower (c.comp σ)
  refine ⟨v - u, ContinuousMonoidHom.ext fun x ↦ ?_⟩
  let t := M x
  let y : J₁ := ⟨x / σ t, by simp [MonoidHom.mem_ker, t, hσ (M x)]⟩
  have hxy : y.val * σ t = x := div_mul_cancel x _
  have hb : b x = b y.val * (((t.val : ℝ) : ℂ)) ^ u := hxy ▸ (map_mul b y.val (σ t)).trans
    (congrArg (b y.val * ·) (hu t))
  have he : c x = c y.val * (((t.val : ℝ) : ℂ)) ^ v := hxy ▸ (map_mul c y.val (σ t)).trans
    (congrArg (c y.val * ·) (hv t))
  change b x * (((t.val : ℝ) : ℂ)) ^ (v - u) = c x
  have hy : c y.val = b y.val := hc y
  rw [hb, he, hy, mul_assoc, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
    (NNReal.coe_ne_zero.mpr t.ne_zero)), add_sub_cancel]

/-- Paper: Theorem 7.3.3.4, p. 360, equations (7.3.3.7)–(7.3.3.9).
At each quasi-character on the Gaussian angular component, each rational-prime
fibre contributes at most one finite place to the primary pole multiplicity. -/
theorem angularCharacter_primaryMultiplicity_le_one (p : HeightOneSpectrum (𝓞 ℚ))
    (c : QuasiCharacter J) (hc : normOneRestriction M c = normOneRestriction M (Cχ(angularCharacter))) :
    sLocalFinitePoleMultiplicity (sLocalPrimaryPlaces finitePlaces p) c ≤ 1 := by
  classical
  obtain ⟨a, rfl⟩ := angularCharacter_component_chart_exists c (fun y ↦ DFunLike.congr_fun hc y)
  apply Finset.card_le_one.mpr
  intro v hv w hw
  obtain ⟨hv, hPv⟩ := Finset.mem_filter.mp hv
  obtain ⟨hw, hPw⟩ := Finset.mem_filter.mp hw
  have he := ((mem_sLocalPrimaryPlaces p v.val).mp hPv).2.trans
    ((mem_sLocalPrimaryPlaces p w.val).mp hPw).2.symm
  have hno := angularCharacter_split_centers_disjoint a
  rcases gaussian_member_cases v with rfl | rfl | rfl <;>
    rcases gaussian_member_cases w with rfl | rfl | rfl <;>
    first | rfl | exact (under_threePlace_ne_under_plusPlace he).elim |
      exact (under_threePlace_ne_under_plusPlace he.symm).elim |
      exact (under_threePlace_ne_under_minusPlace he).elim |
      exact (under_threePlace_ne_under_minusPlace he.symm).elim |
      exact (hno ⟨hv, hw⟩).elim | exact (hno ⟨hw, hv⟩).elim

/-- Paper: Theorem 7.3.3.4, p. 360, equation (7.3.3.8). Every primary orbital index
on the Gaussian angular norm-one component selects the order-zero Fourier evaluation. -/
theorem angularCharacter_primaryOrbitalIndex_offset_zero (p : HeightOneSpectrum (𝓞 ℚ)) :
    let ω := angularCharacter.comp (⟨(M).ker.subtype, continuous_subtype_val⟩ : J₁ →ₜ* J)
    ∀ j : SLocalOrbitalIndex (F := K) (S := finitePlaces) (sLocalPrimaryPlaces finitePlaces p) ω,
      j.val.2 = 0 := by
  intro ω j
  have hm := angularCharacter_primaryMultiplicity_le_one p j.val.1 j.property.1
  exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (j.property.2.trans_le hm))

end RiemannMasullo.Gaussian
