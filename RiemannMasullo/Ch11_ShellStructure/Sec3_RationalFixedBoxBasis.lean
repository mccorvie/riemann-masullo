module

public import RiemannMasullo.Ch11_ShellStructure.Sec3_RationalFixedBoxProjections
public import RiemannMasullo.ForMathlib.Analysis.Fourier.BoundedCircleBasis
public import RiemannMasullo.Ch04_PeriodicSchauderBases.Sec1

/-! # Unconditional bases of actual completed rational packets

Paper: (11.3.1.3)–(11.3.1.4), pp. 494–496. The total cardinal eigenvectors
form an unconditional Schauder basis in the original unweighted logarithmic
Hilbert quotient norm. The actual forward circle action bounds every finite
coordinate projection by `p`, independently of the number or position of modes.
This is the rational trivial-angular fixed-box case; it does not identify a
physical geometric shell or assert a weighted-strip extension.
-/

public noncomputable section
open Set Function
open scoped Topology
namespace RiemannMasullo.RationalPacket

/-- Paper: (11.3.1.3), p. 494. The completed packet expands in integer-mode
cardinal eigenvectors with the prescribed coordinates, including frequency zero.
Deviation: Work on the rational fixed-box quotient with trivial angular
character in unweighted logarithmic `L²`. The expansion converges
unconditionally and every finite coordinate sum has norm at most `p` times
the input norm. -/
theorem exists_fixedBox_unconditional_cardinals {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q) (p : ℕ)
    (hTp1 : ∀ q ∈ insert p T, 1 ≤ q) (hT : ∀ q ∈ T, q.Prime)
    (hp : p.Prime) (hpT : p ∉ T) :
    ∃ v : ℤ → FixedBoxQuotient[X,T,hT1,p,hTp1],
      (∀ j n : ℤ, fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT j (v n) =
        if j = n then 1 else 0) ∧
      (∀ (s : AddCircle (Real.log p)) (n : ℤ),
        fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt s (v n) = _root_.fourier (-n) s • v n) ∧
      (∀ (s : Finset ℤ) (u : FixedBoxQuotient[X,T,hT1,p,hTp1]),
        ‖∑ n ∈ s, fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n u • v n‖ ≤ (p : ℝ) * ‖u‖) ∧
      (∀ u : FixedBoxQuotient[X,T,hT1,p,hTp1],
        HasSum (fun n : ℤ ↦ fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n u • v n) u) ∧
      LinearIndependent ℂ v := by
  let : Fact (0 < Real.log (p : ℝ)) := ⟨Real.log_pos (by exact_mod_cast hp.one_lt)⟩
  obtain ⟨v, hrow, heigen, hproj, hd, hli⟩ :=
    exists_fixedBox_total_eigen_cardinals T hT1 p hTp1 hX hp hpT hT
  have hpj (n : ℤ) (u : FixedBoxQuotient[X,T,hT1,p,hTp1]) :
      _root_.fourierCoeff
        (fun s ↦ fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt s u) (-n) =
        fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT n u • v n := by
    rw [← fixedBoxFourierProjection_apply T hT1 p hTp1 hX hp hpT]
    exact hproj n u
  obtain ⟨hb, hs⟩ := hasSum_of_bounded_circle_modes
    (fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt)
    (continuous_fixedBoxCircleAction T hT1 p hTp1 hX hp.one_lt hpT)
    (Real.sqrt p) (Real.sqrt_nonneg _)
    (norm_fixedBoxCircleAction_le T hT1 p hTp1 hX hp.one_lt)
    (fixedBoxCircleAction_zero T hT1 p hTp1 hX hp.one_lt)
    (fixedBoxCircleAction_add T hT1 p hTp1 hX hp.one_lt hpT)
    v (fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT) hrow heigen hpj hd
  refine ⟨v, hrow, heigen, ?_, hs, hli⟩
  simpa only [Real.sq_sqrt (Nat.cast_nonneg p)] using hb

/-- Paper: (11.3.1.3), p. 494. The integer modes form a Schauder basis of
the completed packet with the prescribed row maps as coordinates.
Deviation: Work on the rational fixed-box quotient with trivial angular
character in unweighted logarithmic `L²`. Every enumeration of the modes
gives an unconditional basis. -/
theorem exists_fixedBox_unconditional_schauderBasis {X : ℝ} (hX : 0 < X)
    (T : Finset ℕ) (hT1 : ∀ q ∈ T, 1 ≤ q) (p : ℕ)
    (hTp1 : ∀ q ∈ insert p T, 1 ≤ q) (hT : ∀ q ∈ T, q.Prime)
    (hp : p.Prime) (hpT : p ∉ T) :
    ∃ v : ℤ → FixedBoxQuotient[X,T,hT1,p,hTp1], ∀ σ : ℕ ≃ ℤ,
      IsSchauderBasis (fun k ↦ v (σ k))
        (fun k ↦ fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT (σ k)) ∧
      SchauderBasis.IsUnconditional (fun k ↦ v (σ k))
        (fun k ↦ fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT (σ k)) := by
  obtain ⟨v, hrow, _, _, hs, _⟩ := exists_fixedBox_unconditional_cardinals hX T hT1 p hTp1 hT hp hpT
  refine ⟨v, fun σ ↦ ?_⟩
  have hu (u : FixedBoxQuotient[X,T,hT1,p,hTp1]) :
      HasSum (fun k : ℕ ↦ fixedBoxPacketRow hX T hT1 p hTp1 hT hp hpT (σ k) u • v (σ k)) u :=
    σ.hasSum_iff.mpr (hs u)
  refine ⟨⟨?_, fun u ↦ Filter.Tendsto.mono_left (hu u) (SummationFilter.conditional ℕ).le_atTop⟩, hu⟩
  intro m n
  simp only [ContinuousLinearMap.coe_coe, hrow, σ.injective.eq_iff]

end RiemannMasullo.RationalPacket
