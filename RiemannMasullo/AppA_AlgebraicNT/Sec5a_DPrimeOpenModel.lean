module

public import RiemannMasullo.AppA_AlgebraicNT.Sec5a
import RiemannMasullo.ForMathlib.Topology.Algebra.OpenSubgroup

/-!
# Open D′-sequences from uniform covers by translates

This gives a sufficient condition for Definition A.5.2.1 (p. 569) and applies it to the open
image of the product of a proper real normed space and a locally profinite group.
-/

public noncomputable section

open Filter Function MeasureTheory Set Topology
open scoped ENNReal NNReal Pointwise

namespace RiemannMasullo

/-- An open neighborhood basis of finite Haar measure has an open D′-subsequence if each
set of quotients is covered by a uniformly bounded number of translates of the basis set. -/
theorem exists_openDPrimeSequence_of_finiteTranslateCover {G I J : Type*}
    [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [FirstCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] (A : I → Set G) (p : I → Prop)
    (hb : (𝓝 (1 : G)).HasBasis p A) (ho : ∀ i, p i → IsOpen (A i))
    (hf : ∀ i, p i → μ (A i) < ∞) (T : Finset J)
    (hc : ∀ i, p i → ∃ t : J → G, A i * (A i)⁻¹ ⊆ ⋃ j ∈ T, t j • A i) :
    ∃ U : ℕ → Set G, IsDPrimeSequence μ U ∧ ∀ n, IsOpen (U n) := by
  classical
  obtain ⟨u, hu, hb'⟩ := hb.exists_antitone_subbasis
  let U (n : ℕ) := A (u n)
  have h1 (n : ℕ) : 1 ∈ U n := mem_of_mem_nhds (hb.mem_of_mem (hu n))
  have hpos (n : ℕ) : 0 < μ (U n) := (ho _ (hu n)).measure_pos μ ⟨1, h1 n⟩
  refine ⟨U, ⟨⟨fun n ↦ ⟨h1 n, (ho _ (hu n)).measurableSet.nullMeasurableSet,
    hpos n, hf _ (hu n)⟩, hb'.antitone, (T.card : ℝ) + 1, by positivity, ?_⟩,
    fun _ h ↦ hb'.mem_iff.mp h⟩, fun n ↦ ho _ (hu n)⟩
  intro n
  obtain ⟨t, ht⟩ := hc _ (hu n)
  have hi : U n ⊆ U n * (U n)⁻¹ := Set.subset_mul_left _ (by simpa using h1 n)
  have hle : μ (U n * (U n)⁻¹) ≤ (T.card : ℝ≥0∞) * μ (U n) := by
    calc
      _ ≤ μ (⋃ j ∈ T, t j • U n) := measure_mono ht
      _ ≤ ∑ j ∈ T, μ (t j • U n) := measure_biUnion_finset_le _ _
      _ = _ := by simp [measure_smul, nsmul_eq_mul]
  refine ⟨(hpos n).trans_le (measure_mono hi), hle.trans_lt ?_⟩
  rw [mul_comm (T.card : ℝ≥0∞) _, mul_comm (ENNReal.ofReal _) _]
  apply ENNReal.mul_lt_mul_right (hpos n).ne' (hf _ (hu n)).ne
  rw [ENNReal.ofReal_add (Nat.cast_nonneg _) zero_le_one, ENNReal.ofReal_natCast,
    ENNReal.ofReal_one]
  exact_mod_cast Nat.lt_succ_self T.card

section NormedModel

variable {V K G : Type*} [NormedAddCommGroup V]
  [CommGroup K] [TopologicalSpace K] [CommGroup G] [TopologicalSpace G]

private def box (r : ℝ) (H : OpenSubgroup K) : Set (Multiplicative V × K) :=
  (Multiplicative.toAdd ⁻¹' Metric.ball (0 : V) r) ×ˢ (H : Set K)

section LocalBasis

variable [IsTopologicalGroup K] [T2Space K] [LocallyCompactSpace K] [TotallyDisconnectedSpace K]

private theorem box_basis (f : Multiplicative V × K →ₜ* G) (hop : IsOpenMap f) :
    (𝓝 (1 : G)).HasBasis (fun i : ℝ × OpenSubgroup K ↦ 0 < i.1 ∧ IsCompact (i.2 : Set K))
      (fun i ↦ f '' box (V := V) i.1 i.2) := by
  refine ⟨fun W ↦ ⟨fun hW ↦ ?_, ?_⟩⟩
  · have hpre : f ⁻¹' W ∈ 𝓝 ((1 : Multiplicative V), (1 : K)) :=
      f.continuous.continuousAt.preimage_mem_nhds (by change W ∈ 𝓝 (f 1); rwa [map_one])
    obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp hpre
    have hA' : Multiplicative.ofAdd ⁻¹' A ∈ 𝓝 (0 : V) := hA
    obtain ⟨r, hr, hrA⟩ := Metric.mem_nhds_iff.mp hA'
    obtain ⟨H, hH, hHB⟩ := exists_compact_openSubgroup_sub_mem_nhds hB
    refine ⟨(r, H), ⟨hr, hH⟩, image_subset_iff.mpr ?_⟩
    exact (Set.prod_mono hrA hHB).trans hAB
  · rintro ⟨⟨r, H⟩, ⟨hr, -⟩, hW⟩
    have hopen : IsOpen (box (V := V) r H) :=
      (show IsOpen (Multiplicative.toAdd ⁻¹' Metric.ball (0 : V) r) from
        Metric.isOpen_ball).prod H.isOpen
    apply mem_of_superset ((hop _ hopen).mem_nhds ?_) hW
    exact ⟨1, ⟨Metric.mem_ball_self hr, H.one_mem⟩, map_one _⟩

end LocalBasis

variable [NormedSpace ℝ V] [ProperSpace V]

private theorem cover_boxes (f : Multiplicative V × K →ₜ* G) :
    ∃ T : Finset V, ∀ (r : ℝ) (H : OpenSubgroup K), 0 < r → ∃ t : V → G,
      (f '' box r H) * (f '' box r H)⁻¹ ⊆ ⋃ j ∈ T, t j • (f '' box r H) := by
  classical
  obtain ⟨S, -, hS, hcov⟩ :=
    (isCompact_closedBall (0 : V) 2).finite_cover_balls zero_lt_one
  refine ⟨hS.toFinset, fun r H hr ↦ ⟨fun t ↦ f (Multiplicative.ofAdd (r • t), 1), ?_⟩⟩
  rintro z ⟨a, ⟨x, hx, rfl⟩, b, hb, rfl⟩
  obtain ⟨y, hy, ey⟩ := (Set.mem_inv.mp hb : b⁻¹ ∈ f '' box r H)
  have eb : b = (f y)⁻¹ := by rw [ey, inv_inv]
  let v := x.1.toAdd - y.1.toAdd
  have hxB : ‖x.1.toAdd‖ < r := by
    have h : x.1.toAdd ∈ Metric.ball 0 r := hx.1
    simpa only [Metric.mem_ball, dist_zero_right] using h
  have hyB : ‖y.1.toAdd‖ < r := by
    have h : y.1.toAdd ∈ Metric.ball 0 r := hy.1
    simpa only [Metric.mem_ball, dist_zero_right] using h
  have hv : ‖v‖ ≤ 2 * r := (norm_sub_le _ _).trans (by linarith)
  have hV : r⁻¹ • v ∈ Metric.closedBall (0 : V) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hr), inv_mul_eq_div]
    exact (div_le_iff₀ hr).mpr hv
  obtain ⟨t, ht, htB⟩ := Set.mem_iUnion₂.mp (hcov hV)
  have hN : ‖r⁻¹ • v - t‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using htB
  have hs : ‖v - r • t‖ < r := by
    have he : r • (r⁻¹ • v - t) = v - r • t := by
      rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    rw [← he, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    simpa only [mul_one] using mul_lt_mul_of_pos_left hN hr
  let w : Multiplicative V × K := (Multiplicative.ofAdd (v - r • t), x.2 * y.2⁻¹)
  have hw : w ∈ box r H := by
    refine ⟨?_, H.mul_mem hx.2 (H.inv_mem hy.2)⟩
    change v - r • t ∈ Metric.ball (0 : V) r
    simpa only [Metric.mem_ball, dist_zero_right] using hs
  refine Set.mem_iUnion₂.mpr ⟨t, hS.mem_toFinset.mpr ht, ⟨f w, ⟨w, hw, rfl⟩, ?_⟩⟩
  change f (Multiplicative.ofAdd (r • t), 1) * f w = f x * b
  rw [eb, ← map_inv, ← map_mul, ← map_mul]
  apply congrArg f
  apply Prod.ext
  · change r • t + (x.1.toAdd - y.1.toAdd - r • t) = x.1.toAdd + -y.1.toAdd
    abel
  · exact one_mul _

variable [IsTopologicalGroup K] [T2Space K] [LocallyCompactSpace K] [TotallyDisconnectedSpace K]
  [IsTopologicalGroup G] [FirstCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- An open continuous homomorphism from the product of a proper real normed space and a
locally profinite group gives an open D′-sequence for every Haar measure on its target.
A fixed finite cover of the ball of radius two gives the doubling bound at all scales. -/
theorem exists_openDPrimeSequence_of_openMap_normedProd (f : Multiplicative V × K →ₜ* G)
    (hop : IsOpenMap f) (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ U : ℕ → Set G, IsDPrimeSequence μ U ∧ ∀ n, IsOpen (U n) := by
  obtain ⟨T, hT⟩ := cover_boxes f
  let A (i : ℝ × OpenSubgroup K) := f '' box i.1 i.2
  have hopen (i : ℝ × OpenSubgroup K) : IsOpen (A i) := hop _ <|
    (show IsOpen (Multiplicative.toAdd ⁻¹' Metric.ball (0 : V) i.1) from
      Metric.isOpen_ball).prod i.2.isOpen
  have hfin (i : ℝ × OpenSubgroup K) (h : 0 < i.1 ∧ IsCompact (i.2 : Set K)) : μ (A i) < ∞ := by
    let D : Set (Multiplicative V) := Multiplicative.toAdd ⁻¹' Metric.closedBall (0 : V) i.1
    have hD : IsCompact D := isCompact_closedBall (0 : V) i.1
    apply lt_of_le_of_lt (measure_mono (Set.image_mono (Set.prod_mono (show
      Multiplicative.toAdd ⁻¹' Metric.ball (0 : V) i.1 ⊆ D from
        Set.preimage_mono Metric.ball_subset_closedBall)
      (Subset.rfl : (i.2 : Set K) ⊆ _))))
    exact ((hD.prod h.2).image f.continuous).measure_lt_top
  exact exists_openDPrimeSequence_of_finiteTranslateCover μ A _ (box_basis f hop)
    (fun i _ ↦ hopen i) hfin T (fun i hi ↦ hT i.1 i.2 hi.1)

end NormedModel
end RiemannMasullo
