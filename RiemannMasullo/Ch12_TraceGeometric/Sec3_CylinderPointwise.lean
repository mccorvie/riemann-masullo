module

public import RiemannMasullo.Ch12_TraceGeometric.Sec3_CylinderMeanSquare
public import RiemannMasullo.Ch12_TraceGeometric.Sec3_ConductorZeroDetector
import Mathlib.Tactic

/-! # Pointwise signed cylinder comparison at positive width

For rows outside the low-height exceptional set, every omitted jet has
large imaginary part. Fourier averaging combines this fact with a
conductor-uniform logarithmic row bound. Both polar moments are allowed.
-/

@[expose] public noncomputable section

open Classical Filter Set
open scoped ContDiff Topology

namespace RiemannMasullo.ConductorCylinder
open ConductorDensity RationalConductor
set_option quotPrecheck false

local notation "Zstrip" => {z : ℂ // 0 < z.re ∧ z.re < 1}
local notation "ord(" χ ", " z ")" => completedPrimitiveOrder (χ,z)
local notation "miss(" a ", " s ", " χ ", " z ")" => (ord(χ,z) -
  spectralStripMultiplicity a s ((z : Zstrip).val.re-1/2) (ord(χ,z)) : ℕ)
local notation "ht(" z ")" => (1+|(z : Zstrip).val.im|)
local notation "sample(" H ", " z ")" => bilateralLaplace H ((z : Zstrip).val-1/2)

private theorem zero_of_order_pos {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {z : Zstrip} (ho : 0 < ord(χ,z)) : χ.LFunction z.val = 0 := by
  by_contra h
  rw [primitiveOrder_eq_analyticOrder χ hχ] at ho
  simp [analyticOrderNatAt,((χ.differentiable_LFunction hχ).analyticAt z.val).analyticOrderAt_eq_zero.mpr h] at ho

private theorem missed_height {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {d a s T : ℝ} (ha : 2*d ≤ a) (hχ : χ ≠ 1)
    (hr : χ ∉ lowZeroCharacters q (1/2+2*d) T) (hl : χ⁻¹ ∉ lowZeroCharacters q (1/2+2*d) T)
    (z : Zstrip) (hm : 0 < miss(a,s,χ,z)) : T < |z.val.im| := by
  by_contra! ht
  have ho : 0 < ord(χ,z) := hm.trans_le (Nat.sub_le ..)
  have right (ψ : DirichletCharacter ℂ q) (hψ : ψ ≠ 1) (hz : ψ ∉ lowZeroCharacters q (1/2+2*d) T)
      (w : Zstrip) (hw : 0 < ord(ψ,w)) (hh : |w.val.im| ≤ T) : w.val.re < 1/2+2*d :=
    lt_of_not_ge (fun hx ↦ hz (Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hψ,w,hx,hh,zero_of_order_pos hψ hw⟩))
  have h₁ := right χ hχ hr z ho ht
  let w := (reflect (χ,z)).2
  have h₂ := right χ⁻¹ (inv_ne_one.mpr hχ) hl w
    (show 0 < ord(χ⁻¹,w) from (completedPrimitiveOrder_reflect (χ,z)).symm ▸ ho)
    (by change |(1-z.val).im| ≤ T; simpa using ht)
  change (1-z.val).re < _ at h₂
  simp only [Complex.sub_re,Complex.one_re] at h₂
  have hi : z.val.re-1/2 ∈ Ioo (-a) a := ⟨by linarith,by linarith⟩
  rw [spectralStripMultiplicity_interior hi,Nat.sub_self] at hm
  exact hm.false

private theorem norm_good_row {H : ℝ → ℂ} (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (d a s T : ℝ),
      1 ≤ T → 2*d ≤ a → χ ≠ 1 → χ ∉ lowZeroCharacters q (1/2+2*d) T →
      χ⁻¹ ∉ lowZeroCharacters q (1/2+2*d) T →
      ‖signedOmittedRow a s H χ‖ ≤ C*Real.log (16*(q:ℝ))/T := by
  obtain ⟨K,hK,hH⟩ := fixed_profile_rapid_decay 3 hd hc (1/2)
  refine ⟨32*K,by positivity,?_⟩
  intro q _ χ d a s T hT ha hχ hr hl
  let w (z : Zstrip) := (ord(χ,z) : ℝ)/ht(z)^2
  let u (z : Zstrip) := (miss(a,s,χ,z) : ℂ)*sample(H,z)
  obtain ⟨hw,hb⟩ := primitiveOrder_height_mass χ hχ
  have hm (z : Zstrip) : ‖u z‖ ≤ (K/T)*w z := by
    have hh : 0 < ht(z) := by positivity
    have hT₀ : 0 < T := by linarith
    dsimp only [u,w]
    rw [norm_mul,Complex.norm_natCast]
    rcases Nat.eq_zero_or_pos miss(a,s,χ,z) with he | he
    · rw [he,Nat.cast_zero,zero_mul]; positivity
    have ht := missed_height ha hχ hr hl z he
    have hx : |(z.val-1/2).re| ≤ 1/2 := by
      simp only [Complex.sub_re,Complex.div_ofNat_re,Complex.one_re]
      exact abs_le.mpr ⟨by linarith [z.property.1],by linarith [z.property.2]⟩
    have h := hH (z.val-1/2) hx
    rw [show (z.val-1/2).im=z.val.im by simp] at h
    have hk : K/ht(z)^3 ≤ (K/T)/ht(z)^2 := by
      rw [div_div,div_le_div_iff₀ (pow_pos hh _) (mul_pos hT₀ (sq_pos_of_pos hh))]
      nlinarith only [mul_nonneg hK (mul_nonneg (by linarith : 0 ≤ ht(z)-T) (sq_nonneg ht(z)))]
    calc _ ≤ (ord(χ,z):ℝ)*((K/T)/ht(z)^2) := mul_le_mul (by exact_mod_cast Nat.sub_le ..)
            (h.trans hk) (norm_nonneg _) (Nat.cast_nonneg _)
         _ = _ := by ring
  have hw' : Summable (fun z ↦ (K/T)*w z) := hw.mul_left _
  have hu := hw'.of_nonneg_of_le (fun z ↦ norm_nonneg (u z)) hm
  apply (norm_tsum_le_tsum_norm hu).trans ((hu.tsum_le_tsum hm hw').trans ?_)
  rw [tsum_mul_left]
  exact (mul_le_mul_of_nonneg_left hb (div_nonneg hK (by linarith))).trans_eq (by ring)

/-- Pointwise signed omitted-jet estimate before absorbing the logarithmic
row factor. It is simultaneous over all residues, all strip widths at least
`2d`, and every Sobolev boundary convention of the strip formula. -/
theorem norm_cylinder_signedOmitted_log_bound {d : ℝ} (hd : 0 < d) (hd' : d ≤ 1/4)
    (H : ℝ → ℂ) (hsmooth : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (a s : ℝ), 2*d ≤ a →
      ‖cylinderAverage q r (signedOmittedRow a s H)‖ ≤ B*(1+Real.log (16*(q:ℝ)))*
        ((q.totient:ℝ)⁻¹+(q:ℝ)^(-(d^2/64))) := by
  obtain ⟨C,hC,hAll⟩ := norm_signedOmittedRow_le hsmooth hc hp
  obtain ⟨D,hD,hGood⟩ := norm_good_row hsmooth hc
  obtain ⟨J,hJ,hCount⟩ := lowZeroCharacters_power_saving hd hd'
  refine ⟨C+2*C*J+D,by positivity,?_⟩
  intro q _ r a s ha
  let t := d^2/64
  let T := (q:ℝ)^t
  let L := 1+Real.log (16*(q:ℝ))
  let P : ℝ := q.totient
  let b := lowZeroCharacters q (1/2+2*d) T
  let E := insert (1 : DirichletCharacter ℂ q) (b ∪ b.image (·⁻¹))
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hq₀ : 0 < (q:ℝ) := by linarith
  have hP : 0 < P := Nat.cast_pos.mpr (Nat.totient_pos.mpr (NeZero.pos q))
  have hL : 1 ≤ L := by dsimp [L]; linarith [Real.log_nonneg (by linarith : 1 ≤ 16*(q:ℝ))]
  have hT : 1 ≤ T := Real.one_le_rpow hq (by dsimp [t]; positivity)
  have hρ : (q:ℝ)^(-(d^2/8)) ≤ T⁻¹ := by
    rw [show T⁻¹ = (q:ℝ)^(-t) from (Real.rpow_neg hq₀.le _).symm]
    exact Real.rpow_le_rpow_of_exponent_le hq (by dsimp [t]; nlinarith [sq_nonneg d])
  have hb : (b.card:ℝ)/P ≤ J*T⁻¹ := (hCount q).trans (mul_le_mul_of_nonneg_left hρ hJ)
  have hcard : (E.card : ℝ) ≤ 1+2*(b.card:ℝ) := by
    have he := Finset.card_insert_le (1 : DirichletCharacter ℂ q) (b ∪ b.image (·⁻¹))
    have hu := Finset.card_union_le b (b.image (·⁻¹))
    have hi := Finset.card_image_le (f := fun χ : DirichletCharacter ℂ q ↦ χ⁻¹) (s := b)
    exact_mod_cast (show E.card ≤ 1+2*b.card by dsimp only [E]; omega)
  have hcoef : (E.card:ℝ)/P ≤ P⁻¹+2*J*T⁻¹ := by
    calc _ ≤ (1+2*(b.card:ℝ))/P := div_le_div_of_nonneg_right hcard hP.le
         _ = P⁻¹+2*((b.card:ℝ)/P) := by ring
         _ ≤ _ := by linarith
  let v := (signedOmittedRow a s H : DirichletCharacter ℂ q → ℂ)
  have hrow (χ : DirichletCharacter ℂ q) : ‖v χ‖ ≤ (if χ ∈ E then C*L else 0) + D*L/T := by
    by_cases h : χ ∈ E
    · rw [ite_eq_left h]
      exact (hAll q χ a s).trans (le_add_of_nonneg_right (by positivity))
    · rw [ite_eq_right h,zero_add]
      have hχ : χ ≠ 1 := fun he ↦ h (he ▸ Finset.mem_insert_self ..)
      have hr : χ ∉ b := fun hh ↦ h (Finset.mem_insert_of_mem (Finset.mem_union_left _ hh))
      have hl : χ⁻¹ ∉ b := fun hh ↦ h (Finset.mem_insert_of_mem (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨χ⁻¹,hh,inv_inv χ⟩)))
      exact (hGood q χ d a s T hT ha hχ hr hl).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by dsimp only [L]; linarith) hD) (by linarith))
  have heval : ∑ χ, ((if χ ∈ E then C*L else 0)+D*L/T) = (E.card:ℝ)*(C*L)+P*(D*L/T) := by
    rw [Finset.sum_add_distrib, ← Finset.sum_filter]
    simp [P,← Nat.card_eq_fintype_card, DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity]
  apply (norm_cylinderAverage_le r v).trans
  change (∑ χ, ‖v χ‖)/P ≤ _
  calc _ ≤ ((E.card:ℝ)*(C*L)+P*(D*L/T))/P :=
          div_le_div_of_nonneg_right ((Finset.sum_le_sum (fun χ _ ↦ hrow χ)).trans_eq heval) hP.le
       _ = ((E.card:ℝ)/P)*(C*L)+D*L*T⁻¹ := by field_simp
       _ ≤ (P⁻¹+2*J*T⁻¹)*(C*L)+D*L*T⁻¹ := by gcongr
       _ ≤ _ := by
         rw [show (q:ℝ)^(-(d^2/64)) = T⁻¹ from Real.rpow_neg hq₀.le _]
         change _ ≤ (C+2*C*J+D)*L*(P⁻¹+T⁻¹)
         have hLp : 0 ≤ L*P⁻¹ := by positivity
         have hLt : 0 ≤ L*T⁻¹ := by positivity
         nlinarith only [mul_nonneg (mul_nonneg hC hJ) hLp,mul_nonneg hD hLp,mul_nonneg hC hLt]

/-- The inverse unit-group volume admits every power saving up to one half. -/
theorem exists_inv_totient_le_rpow {t : ℝ} (ht : t ≤ 1/2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q], (q.totient : ℝ)⁻¹ ≤ C*(q:ℝ)^(-t) := by
  obtain ⟨C,hC,hbound⟩ := totient_ratio_le_rpow (by norm_num : 0 < (1/2 : ℝ))
  refine ⟨C,hC,?_⟩
  intro q _
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hq₀ : 0 < (q:ℝ) := by linarith
  calc (q.totient:ℝ)⁻¹ = ((q:ℝ)/q.totient)/(q:ℝ) := by field_simp
       _ ≤ (C*(q:ℝ)^(1/2:ℝ))/(q:ℝ) := div_le_div_of_nonneg_right (hbound q) hq₀.le
       _ = C*(q:ℝ)^((1/2:ℝ)-1) := by rw [Real.rpow_sub hq₀,Real.rpow_one]; ring
       _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hq (by linarith)) hC

/-- Unconditional power saving at every single residue cylinder. The profile
and the positive lower width are fixed; the residue, modulus, upper width
and Sobolev edge order are arbitrary. -/
theorem norm_cylinder_signedOmitted_power {δ : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1/2)
    (H : ℝ → ℂ) (hd : ContDiff ℝ (∞) H) (hc : HasCompactSupport H) (hp : tsupport H ⊆ Ioi 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (q : ℕ) [NeZero q] (r : (ZMod q)ˣ) (a s : ℝ), δ ≤ a →
      ‖cylinderAverage q r (signedOmittedRow a s H)‖ ≤ C*(q:ℝ)^(-(δ^2/512)) := by
  let t := δ^2/256
  let e := δ^2/512
  have hte : t = 2*e := by dsimp only [t,e]; ring
  have he : 0 < e := by dsimp [e]; positivity
  have ht' : t ≤ 1/2 := by dsimp [t]; nlinarith [mul_nonneg hδ.le (by linarith : 0 ≤ 1/2-δ)]
  obtain ⟨B,hB,hbound⟩ := norm_cylinder_signedOmitted_log_bound (d := δ/2) (by positivity) (by linarith) H hd hc hp
  obtain ⟨A,hA,hφ⟩ := exists_inv_totient_le_rpow ht'
  let L := 1+Real.log 16+e⁻¹
  have hL : 0 ≤ L := by dsimp [L]; positivity
  refine ⟨B*L*(A+1),by positivity,?_⟩
  intro q _ r a s ha
  have hq : 1 ≤ (q:ℝ) := by exact_mod_cast NeZero.pos q
  have hq₀ : 0 < (q:ℝ) := by linarith
  have hpow : 1 ≤ (q:ℝ)^e := Real.one_le_rpow hq he.le
  have hlog : 1+Real.log (16*(q:ℝ)) ≤ L*(q:ℝ)^e := by
    rw [Real.log_mul (by norm_num) hq₀.ne']
    have h := Real.log_le_rpow_div hq₀.le he
    dsimp only [L]
    rw [div_eq_mul_inv] at h
    nlinarith only [h,hpow,mul_nonneg (Real.log_nonneg (by norm_num : (1:ℝ) ≤ 16)) (sub_nonneg.mpr hpow)]
  have hs' := hbound q r a s (by linarith)
  rw [show (δ/2)^2/64 = t by dsimp [t]; ring] at hs'
  apply hs'.trans
  calc _ ≤ B*(L*(q:ℝ)^e)*((A+1)*(q:ℝ)^(-t)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left hlog hB) _ (by positivity) (by positivity)
          linarith only [hφ q]
       _ = B*L*(A+1)*(q:ℝ)^(-e) := by
          rw [show -e = e+(-t) by linarith,Real.rpow_add hq₀]; ring

end RiemannMasullo.ConductorCylinder
