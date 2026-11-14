import UlamFloating.PolygonMotion
import UlamFloating.Extraction

/-!
# Boundary rotation recovered from a chord-angle increment

For any rational constant-chord boundary with at least three samples,
a fixed angular advance over a time shift rotates every directed edge.
The conserved signed polygon centroid then identifies one fixed center
for the rotation of the original boundary parametrization.
-/

namespace UlamFloating

/-- A translation increment of a real angle lift gives the corresponding
rotation of the represented vectors. No differentiability is required. -/
theorem rotation_of_angle_increment {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
    (o : Orientation ℝ E (Fin 2)) {e : ℝ → E} {θ : ℝ → ℝ} {v : E} {T a : ℝ}
    (he : ∀ t, e t = o.rotation (θ t : Real.Angle) v)
    (hθ : ∀ t, θ (t + T) = θ t + a) (t : ℝ) :
    e (t + T) = o.rotation (a : Real.Angle) (e t) := by
  rw [he (t + T), hθ, add_comm (θ t) a, Real.Angle.coe_add,
    ← o.rotation_rotation, ← he t]

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A fixed angular advance of a rational constant-chord lift rotates the
entire boundary about the conserved signed centroid of its sampled polygon.
The result works for every sample count at least three and does not assume
regular polygons, a disk, or a rotation center in its hypotheses. -/
theorem IsUnitSpeedBoundary.rotation_about_centroid_of_chord_angle_increment
    {K : Set Plane} {P l T a : ℝ} {γ : ℝ → Plane} {n : ℕ}
    (hb : IsUnitSpeedBoundary K P γ) (hn : 3 ≤ n)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ → ℝ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / n) l)
    (hrot : ∀ t, γ (t + P / n) - γ t = Real.cos (θ t) • (γ (P / n) - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ (P / n) - γ 0))
    (hθ : ∀ t, θ (t + T) = θ t + a) (t : ℝ) :
    let c := polygonCentroid (finRotate n) o (fun i => boundarySamples γ P n i 0)
    γ (t + T) - c = o.rotation (a : Real.Angle) (γ t - c) := by
  cases n with
  | zero => omega
  | succ n =>
    have he (s : ℝ) : γ (s + P / (n + 1)) - γ s =
        o.rotation (θ s : Real.Angle) (γ (P / (n + 1)) - γ 0) := by
      simpa only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
        Nat.cast_add, Nat.cast_one] using hrot s
    have hchord := rotation_of_angle_increment o he hθ
    have hcar := hb.boundarySamples_isCarousel hl hc
    have hA := (hb.boundarySamples_strictlyConvex hn t).polygonSignedArea_ne_zero o
    have hedge (i : Fin (n + 1)) :
        boundarySamples γ P (n + 1) (finRotate (n + 1) i) (t + T) -
          boundarySamples γ P (n + 1) i (t + T) =
        o.rotation (a : Real.Angle)
          (boundarySamples γ P (n + 1) (finRotate (n + 1) i) t -
            boundarySamples γ P (n + 1) i t) := by
      rw [boundarySamples_rotate hb.periodic, boundarySamples_rotate hb.periodic]
      simpa only [boundarySamples, sampledVertex, Nat.cast_add, Nat.cast_one,
        add_assoc, add_left_comm, add_comm] using
        hchord (t + (i.val : ℝ) * (P / (n + 1)))
    have h := hcar.sub_centroid_eq_of_rotated_edges o (a : Real.Angle) (t + T) t
      hA hedge 0
    simpa only [boundarySamples, sampledVertex, Fin.val_zero, Nat.cast_zero,
      zero_mul, add_zero] using h

end UlamFloating
