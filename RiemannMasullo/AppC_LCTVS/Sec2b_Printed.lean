module

public import RiemannMasullo.AppC_LCTVS.Sec2b

/-! # Appendix C.1.5: the printed implication from Schwartz to nuclear Fréchet spaces -/

@[expose] public noncomputable section

namespace RiemannMasullo

/-- Paper: Paragraph after Theorem C.1.5.11, p. 668. As printed: a Schwartz Fréchet
stage is nuclear. `isSchwartzTVS_of_isNuclearTVS` gives the implication in Example C.1.5.10,
and `limitSubspaceTopology_eq_iff_liftsBoundedSets` uses Schwartz stages. See ERRATA F3. -/
def Printed.isNuclearTVS_of_isSchwartzFrechet : Prop :=
  ∀ (E : Type) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] [T2Space E],
    IsFrechetTVS E → IsSchwartzTVS E → IsNuclearTVS.{0} E

/-- Paper: Paragraph after Theorem C.1.5.11, p. 668. Take the Fréchet space of
complex sequences x with `∑ₙ (log (n + 3))^(2k) |xₙ|² < ∞` for every k ≥ 0, with
the corresponding weighted ℓ² norms. Between two successive Hilbert completions
the inclusion has diagonal entries `1 / log (n + 3)`, which tend to zero, so the space
is Schwartz. No inclusion from a higher completion to unweighted ℓ² is Hilbert–Schmidt,
since `∑ₙ (log (n + 3))^(-2k)` diverges for every k. A nuclear connecting map to the
unweighted completion would factor such an inclusion through a continuous map from
some weighted completion, making that inclusion nuclear and hence Hilbert–Schmidt. -/
theorem Printed.isNuclearTVS_of_isSchwartzFrechet_false :
    ¬ Printed.isNuclearTVS_of_isSchwartzFrechet := by sorry

end RiemannMasullo
