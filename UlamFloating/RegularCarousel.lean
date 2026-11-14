import UlamFloating.PolygonCentroid
import UlamFloating.FirstMoment
import UlamFloating.Extraction
import UlamFloating.Disk

/-!
# Rigidity from regular sampled polygons

An equilateral cyclic polygon has its algebraic centroid at its circumcenter.
Conservation of polygon moments therefore fixes that center along a carousel.
For regular polygons the common edge length also fixes the circumradius.
This closes the final rigidity step without a polygon-to-lamina integral theorem.
-/

namespace UlamFloating

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A carousel of regular polygons with nonzero signed area has a fixed
circumcenter and circumradius. Regularity is an explicit hypothesis. -/
theorem IsCarousel.fixed_circle_of_regular {n : ℕ} {p : Fin n → ℝ → Plane} {l : ℝ}
    (hc : IsCarousel (finRotate n) p l) (o : Orientation ℝ Plane (Fin 2))
    (hA : polygonSignedArea (finRotate n) o (fun i => p i 0) ≠ 0)
    (hreg : ∀ t, IsRegularPolygon (fun i => p i t)) :
    ∃ c : Plane, ∃ R : ℝ, 0 < R ∧ ∀ t i, ‖p i t - c‖ ^ 2 = R := by
  have hn : 3 ≤ n := (hreg 0).1
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  have hrot : finRotate n i0 = i1 := by
    cases n with
    | zero => omega
    | succ m => exact finRotate_of_lt (by omega)
  let d : ℝ := 2 * (1 - Real.cos (2 * Real.pi / n))
  have hedge (t : ℝ) {r : ℝ}
      (hpair : ∀ i j : Fin n, dist (p i t) (p j t) ^ 2 =
        2 * r ^ 2 * (1 - Real.cos (2 * Real.pi * ((i.val : ℝ) - j.val) / n))) :
      l ^ 2 = d * r ^ 2 := by
    have he := hc.edge_length i0 t
    rw [hrot] at he
    have hh := hpair i1 i0
    simp only [i0, i1, Nat.cast_one, Nat.cast_zero, sub_zero, mul_one,
      dist_eq_norm, he] at hh
    dsimp [d]
    nlinarith [hh]
  obtain ⟨_, c0, r0, hr0, _, hpair0⟩ := hreg 0
  have he0 := hedge 0 hpair0
  have hd : d ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at he0
    exact (sq_pos_of_pos hc.length_pos).ne' he0
  refine ⟨polygonCentroid (finRotate n) o (fun i => p i 0), r0 ^ 2,
    sq_pos_of_pos hr0, ?_⟩
  intro t i
  obtain ⟨_, c, r, _, hr, hpair⟩ := hreg t
  have hR : r ^ 2 = r0 ^ 2 :=
    mul_left_cancel₀ hd ((hedge t hpair).symm.trans he0)
  have hAt : polygonSignedArea (finRotate n) o (fun j => p j t) ≠ 0 := by
    rwa [hc.polygonSignedArea_eq o t 0]
  have hcenter := polygonCentroid_eq_of_equidistant (finRotate n) o
    (fun j => p j t) c (fun j => by rw [← dist_eq_norm, hr j])
    (fun j => hc.edge_length j t) hAt
  rw [hc.polygonCentroid_eq o t 0] at hcenter
  rw [hcenter, ← dist_eq_norm, hr i, hR]

/-- Regular rational samples force a constant-chord boundary to be a circle.
The only extra geometric hypothesis is regularity of the sampled polygons. -/
theorem IsUnitSpeedBoundary.isDisk_of_regular_samples
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} {n : ℕ}
    (hb : IsUnitSpeedBoundary K P γ) (hn : 3 ≤ n) (hl : 0 < l)
    (hchord : HasConstantChord γ (P / n) l)
    (hreg : ∀ t, IsRegularPolygon (fun i => boundarySamples γ P n i t)) : IsDisk K := by
  let o : Orientation ℝ Plane (Fin 2) :=
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hc := hb.boundarySamples_isCarousel hl hchord
  have hA := (hb.boundarySamples_strictlyConvex hn 0).polygonSignedArea_ne_zero o
  obtain ⟨c, R, hR, hcircle⟩ := hc.fixed_circle_of_regular o hA hreg
  apply hb.isDisk_of_norm_sq hR
  intro t
  simpa [boundarySamples, sampledVertex] using hcircle t ⟨0, by omega⟩

/-- The genuine pentagon obstruction is the sole remaining premise in this
assembly of geometric one-fifth rigidity. It is not assumed as an axiom. -/
theorem fifth_rigidity_of_pentagon_obstruction
    (hpentagon : pentagonObstructionStatement) : fifthRigidityStatement := by
  intro K hK
  obtain ⟨_, _, P, γ, hb, l, hl, hchord⟩ := hK
  have hchord' : HasConstantChord γ (P / 5) l := by
    convert hchord using 1
    ring
  exact hb.isDisk_of_regular_samples (by omega : 3 ≤ 5) hl hchord'
    (hpentagon K P γ l hb hl hchord')

end UlamFloating
