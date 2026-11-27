module

public import RiemannMasullo.Ch02_AdelicTheta.Sec3
public import RiemannMasullo.Ch03_IdelicZeta.Sec3
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec2b
public import RiemannMasullo.Ch05_ThetaZSpaces.Sec5
import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-! # Fourier tail normalization on the theta quotient -/

@[expose] public noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField.AdeleRing

namespace RiemannMasullo

set_option quotPrecheck false

variable {F : Type*} [Field F] [NumberField F]
variable {S : Finset (HeightOneSpectrum (𝓞 F))}

local notation "Tests" => SchwartzBruhat (Multiplicative (SAdeleRing F S))
local notation "FT" => sAdeleSchwartzFourier (F := F) (S := S)
local notation "SUnits" => ((S : Set (HeightOneSpectrum (𝓞 F))).integer F)ˣ
local notation "zeroA" => Multiplicative.ofAdd (0 : SAdeleRing F S)

/-- Ordinary S-local theta vanishes only if both S-local polar evaluations vanish. -/
private theorem localThetaKernel_polar_values_zero (f : Tests)
    (hf : f ∈ (sLocalAdelicTheta F S).ker) : f zeroA = 0 ∧ FT f zeroA = 0 := by
  let G := sAdeleSchwartzToGlobal F S f
  have hG : G ∈ adelePolarSubspace F :=
    globalThetaKernel_le_adelePolarSubspace (F := F)
      (sLocalThetaToGlobal_preserves_kernel (F := F) (S := S) hf)
  obtain ⟨hG0, hGF⟩ := (mem_adelePolarSubspace G).mp hG
  obtain ⟨m, hm, hscale⟩ := sAdeleSchwartzToGlobal_fourier_zero_scale (F := F) (S := S)
  constructor
  · change sAdeleSchwartzToGlobal F S f (Multiplicative.ofAdd 0) = 0 at hG0
    rwa [sAdeleSchwartzToGlobal_apply,
      ite_eq_left (fun v _ ↦ (v.adicCompletionIntegers F).zero_mem), map_zero] at hG0
  · change adeleSchwartzFourier (sAdeleSchwartzToGlobal F S f) (Multiplicative.ofAdd 0) = 0 at hGF
    rw [hscale] at hGF
    exact (mul_eq_zero.mp hGF).resolve_left hm

private theorem ordinaryTheta_sUnitTranslate (u : SUnits) (f : Tests) :
    sLocalAdelicTheta F S (schwartzBruhatUnitTranslate (sUnitEmbedding F S u) f) =
      sLocalAdelicTheta F S f := by
  let d := sUnitEmbedding F S u
  let π : (SAdeleRing F S)ˣ →* SIdeleQuotient F S := QuotientGroup.mk' _
  have hd : π d = 1 := (sIdeleQuotient_mk_eq_one F S d).mpr ⟨u, rfl⟩
  refine ContinuousMap.ext fun x ↦ (sLocalAdelicTheta_unitTranslate d x f).trans ?_
  apply sLocalAdelicTheta_factorsThrough F S f
  change π (d⁻¹ * x) = π x
  rw [map_mul, map_inv, hd, inv_one, one_mul]

private theorem localFourier_four (f : Tests) : FT (FT (FT (FT f))) = f := by
  apply Subtype.ext
  funext x
  change FT (FT (FT (FT f))) x = f x
  exact (sLocal_fourier_inversion (FT (FT f)) x.toAdd).trans
    ((sLocal_fourier_inversion f (-x.toAdd)).trans
      (congrArg (fun y ↦ f (Multiplicative.ofAdd y)) (neg_neg x.toAdd)))

/-- Paper: Theorem 5.2.4.1(1), p. 239, and (11.2.1.6), p. 488.
A finite expansion of an S-local Fourier transform into translates of inserted
tests gives one inserted representative with the same theta image and both
polar values.
Deviation: Use stage compatibility on theta classes at the added places away
from the different. The support of the smaller test comes from the input expansion. -/
theorem sLocalFourier_standardTail_normalize_sum_quotient
    {T : Finset (HeightOneSpectrum (𝓞 F))} (hTS : T ⊆ S)
    (hgood : ∀ v : HeightOneSpectrum (𝓞 F),
      v ∈ S → v ∉ T → ¬ v.asIdeal ∣ differentIdeal ℤ (𝓞 F))
    {ι : Type*} (I : Finset ι) (u : ι → SUnits)
    (b : ι → SchwartzBruhat (Multiplicative (SAdeleRing F T))) (f : Tests)
    (hFourier : FT f = ∑ j ∈ I, schwartzBruhatUnitTranslate (sUnitEmbedding F S (u j))
      (sAdeleSchwartzTransition F hTS (b j))) :
    ∃ g : SchwartzBruhat (Multiplicative (SAdeleRing F T)),
      sAdeleSchwartzFourier g = ∑ j ∈ I, b j ∧
      let t := sAdeleSchwartzTransition F hTS g
      sLocalAdelicTheta F S f = sLocalAdelicTheta F S t ∧
        f zeroA = t zeroA ∧ FT f zeroA = FT t zeroA := by
  classical
  let theta := sLocalAdelicTheta F S
  let lift := sAdeleSchwartzTransition F hTS
  let c := ∑ j ∈ I, b j
  let FT₀ := sAdeleSchwartzFourier (F := F) (S := T)
  let g := FT₀ (FT₀ (FT₀ c))
  let t := lift g
  have hg : FT₀ g = c := localFourier_four c
  have hThetaFT : theta (FT f) = theta (lift c) := by
    calc
      theta (FT f) = ∑ j ∈ I, theta (schwartzBruhatUnitTranslate (sUnitEmbedding F S (u j))
          (lift (b j))) := by rw [hFourier, map_sum]
      _ = ∑ j ∈ I, theta (lift (b j)) :=
        Finset.sum_congr rfl fun j _ ↦ ordinaryTheta_sUnitTranslate (u j) (lift (b j))
      _ = theta (lift c) := by rw [show c = ∑ j ∈ I, b j from rfl, map_sum, map_sum]
  let q := theta.ker.mkQ
  let q₀ := (sLocalAdelicTheta F T).ker.mkQ
  let e := (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose
  let e₀ := (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose
  have hfq : e (q f) = q (FT f) :=
    (existsUnique_sLocalThetaFourier (F := F) (S := S)).exists.choose_spec.2 f
  have hgq : e₀ (q₀ g) = q₀ (FT₀ g) :=
    (existsUnique_sLocalThetaFourier (F := F) (S := T)).exists.choose_spec.2 g
  have htq : e (q t) = q (lift c) := by
    have h := sLocalThetaFourier_transition (F := F) hTS hgood (q₀ g)
    change e (q t) = sLocalThetaTransition (F := F) hTS (e₀ (q₀ g)) at h
    rw [hgq, hg] at h
    exact h
  have hq : q (FT f) = q (lift c) := by
    apply (Submodule.Quotient.eq theta.ker).mpr
    rwa [LinearMap.mem_ker, map_sub, sub_eq_zero]
  have hq' : q f = q t := e.injective (hfq.trans (hq.trans htq.symm))
  have hdiff : f - t ∈ theta.ker := (Submodule.Quotient.eq theta.ker).mp hq'
  have hTheta : theta f = theta t := by
    simpa only [LinearMap.mem_ker, map_sub, sub_eq_zero] using hdiff
  obtain ⟨h0, hF0⟩ := localThetaKernel_polar_values_zero _ hdiff
  let ev : Tests →ₗ[ℂ] ℂ := (LinearMap.proj zeroA).comp (schwartzBruhatSubmodule _).subtype
  have hzero : f zeroA = t zeroA := by
    change ev f = ev t
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact h0
  obtain ⟨M, hM⟩ := sLocal_fourier_continuousLinear (F := F) (S := S)
  have hFourierZero : FT f zeroA = FT t zeroA := by
    change ev (FT f) = ev (FT t)
    rw [← hM f, ← hM t]
    apply sub_eq_zero.mp
    rw [← map_sub, ← map_sub, hM]
    exact hF0
  exact ⟨g, hg, hTheta, hzero, hFourierZero⟩

end RiemannMasullo
