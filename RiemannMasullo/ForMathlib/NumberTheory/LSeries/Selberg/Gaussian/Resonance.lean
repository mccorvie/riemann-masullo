module

public import RiemannMasullo.ForMathlib.NumberTheory.LSeries.Selberg.Definitions

public section

namespace RiemannMasullo.Selberg

private theorem freq_eq_iff_cross_mul {i j k l m v : ℕ} (hl : 0 < l) (hv : 0 < v) :
    freq i k l = freq j m v ↔ (i + 1) * (k * v) = (j + 1) * (l * m) := by
  rw [freq, freq, div_eq_div_iff (by exact_mod_cast hl.ne') (by exact_mod_cast hv.ne')]
  rw [mul_assoc, mul_assoc, mul_comm (m : ℝ) l]
  norm_cast

/-- The positive solutions of `x * a = y * b` for coprime `a, b` are the
positive multiples of `(b, a)`. Both series use indices starting at zero. -/
private theorem tsum_coprime_pairs {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : a.Coprime b) (F : ℕ → ℂ) :
    (∑' ij : ℕ × ℕ, if (ij.1 + 1) * a = (ij.2 + 1) * b then F ij.1 else 0) =
      ∑' r : ℕ, F ((r + 1) * b - 1) := by
  let p (r : ℕ) : ℕ × ℕ := ((r + 1) * b - 1, (r + 1) * a - 1)
  have h₁ (r : ℕ) : (p r).1 + 1 = (r + 1) * b := Nat.sub_add_cancel (Nat.mul_pos r.succ_pos hb)
  have h₂ (r : ℕ) : (p r).2 + 1 = (r + 1) * a := Nat.sub_add_cancel (Nat.mul_pos r.succ_pos ha)
  have hinj : Function.Injective p := by
    intro r s hrs
    have heq := congrArg (fun ij : ℕ × ℕ ↦ ij.1 + 1) hrs
    rw [h₁, h₁] at heq
    exact Nat.succ.inj (Nat.mul_right_cancel hb heq)
  let term (ij : ℕ × ℕ) := if (ij.1 + 1) * a = (ij.2 + 1) * b then F ij.1 else 0
  have hsupp : Function.support term ⊆ Set.range p := by
    rintro ⟨i, j⟩ hne
    have heq : (i + 1) * a = (j + 1) * b := by
      by_contra h
      exact hne (ite_eq_right h)
    obtain ⟨s, hs⟩ := hab.symm.dvd_of_dvd_mul_right (heq ▸ dvd_mul_left b (j + 1))
    have ht : j + 1 = s * a := by
      apply Nat.mul_right_cancel hb
      rw [← heq, hs]
      ac_rfl
    have hspos : 0 < s := Nat.pos_of_ne_zero (by rintro rfl; simp at hs)
    exact ⟨s - 1, by simp [p, Nat.sub_add_cancel hspos, mul_comm s b, ← hs, ← ht]⟩
  change (∑' ij, term ij) = _
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro r
  have heq : ((p r).1 + 1) * a = ((p r).2 + 1) * b := by
    rw [h₁, h₂]
    ac_rfl
  exact ite_eq_left heq

/-- Card 27. For positive k, l, m, v the equal-frequency pairs reindex as the positive multiples
of km/gcd(kv,lm) in the series of any complex-valued function.
Titchmarsh, §10.11, p. 270, diagonal parametrization. -/
theorem resonance (k l m v : ℕ) (hk : 0 < k) (hl : 0 < l) (hm : 0 < m) (hv : 0 < v) :
    ∀ f : ℝ → ℂ, (∑' ij : ℕ × ℕ, if freq ij.1 k l = freq ij.2 m v then
      f (freq ij.1 k l) else 0) = ∑' j : ℕ, f (((j+1 : ℕ) : ℝ)/ratio k l m v) := by
  intro f
  let d := Nat.gcd (k * v) (l * m)
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ (Nat.mul_pos hk hv)
  obtain ⟨a, b, hab, hkv, hlm⟩ := Nat.exists_coprime (k * v) (l * m)
  change k * v = a * d at hkv
  change l * m = b * d at hlm
  have ha : 0 < a := Nat.pos_of_mul_pos_right (hkv ▸ Nat.mul_pos hk hv)
  have hb : 0 < b := Nat.pos_of_mul_pos_right (hlm ▸ Nat.mul_pos hl hm)
  have heq (i j : ℕ) : freq i k l = freq j m v ↔ (i + 1) * a = (j + 1) * b := by
    rw [freq_eq_iff_cross_mul hl hv, hkv, hlm, ← mul_assoc, ← mul_assoc,
      Nat.mul_right_cancel_iff hd]
  simp_rw [heq]
  rw [tsum_coprime_pairs ha hb hab (fun i ↦ f (freq i k l))]
  apply tsum_congr
  intro r
  congr 1
  have hbr : (b : ℝ) = (l : ℝ) * m / d :=
    (eq_div_iff (by positivity)).2 (by exact_mod_cast hlm.symm)
  change freq ((r + 1) * b - 1) k l = ((r + 1 : ℕ) : ℝ) / ((d : ℝ) / ((k : ℝ) * m))
  rw [freq, ← Nat.cast_add_one, Nat.sub_add_cancel (Nat.mul_pos r.succ_pos hb), Nat.cast_mul, hbr]
  field_simp

end RiemannMasullo.Selberg
