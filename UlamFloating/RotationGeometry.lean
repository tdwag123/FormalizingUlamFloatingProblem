import UlamFloating.RotatingVelocity
import UlamFloating.BoundaryEmbedding

/-!
# Uniform rotation and regular sampled polygons

The complete pairwise distance formula follows from rotation. A simple
periodic boundary rotating uniformly about a center makes exactly one turn,
so its rational samples have the required cyclic order, without star winding.
-/

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Squared distance between two rotations of the same vector. -/
theorem rotation_dist_sq (o : Orientation ℝ E (Fin 2)) (v : E) (a b : ℝ) :
    dist (o.rotation (a : Real.Angle) v) (o.rotation (b : Real.Angle) v) ^ 2 =
      2 * ‖v‖ ^ 2 * (1 - Real.cos (a - b)) := by
  have hi : ⟪o.rotation (a : Real.Angle) v, o.rotation (b : Real.Angle) v⟫_ℝ =
      Real.cos (a - b) * ‖v‖ ^ 2 := by
    simp only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
      inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
    simp only [o.inner_comp_rightAngleRotation, o.inner_rightAngleRotation_left,
      o.inner_rightAngleRotation_right, o.areaForm_apply_self,
      real_inner_self_eq_norm_sq, Real.cos_sub]
    ring
  rw [dist_eq_norm, norm_sub_sq_real, (o.rotation _).norm_map, (o.rotation _).norm_map, hi]
  ring

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Equally spaced positive-radius rotations give a regular polygon with
the full distance table in its specified cyclic order. -/
theorem isRegularPolygon_of_rotation (o : Orientation ℝ Plane (Fin 2))
    {n : ℕ} (hn : 3 ≤ n) {p : Fin n → Plane} {c v : Plane} {phase : ℝ}
    (hv : v ≠ 0)
    (hp : ∀ i, p i = c + o.rotation
      ((phase + 2 * Real.pi * (i.val : ℝ) / n : ℝ) : Real.Angle) v) :
    IsRegularPolygon p := by
  refine ⟨hn, c, ‖v‖, norm_pos_iff.mpr hv, ?_, ?_⟩
  · intro i
    rw [hp, dist_eq_norm, add_sub_cancel_left, (o.rotation _).norm_map]
  · intro i j
    rw [hp i, hp j, dist_add_left, rotation_dist_sq]
    congr 2
    congr 1
    ring

/-- A simple boundary parametrized by positive uniform rotation makes one
full turn in its traversal period. This excludes multiple and star windings. -/
theorem IsUnitSpeedBoundary.rotation_period_eq_two_pi
    {K : Set Plane} {P a : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (ha : 0 < a) {c v : Plane} (hv : v ≠ 0)
    (hrot : ∀ t, γ t - c = o.rotation ((a * t : ℝ) : Real.Angle) v) :
    a * P = 2 * Real.pi := by
  have hzero : γ 0 - c = v := by simpa using hrot 0
  apply angle_eq_two_pi_of_no_return o (e := fun t => γ t - c) (OrderIso.mulLeft₀ a ha)
    (by simp) hb.period_pos
    (show γ 0 - c ≠ 0 by rwa [hzero])
    (show γ P - c = γ 0 - c by
      simpa only [zero_add] using congrArg (fun z => z - c) (hb.periodic 0))
  · intro t
    simpa only [OrderIso.mulLeft₀_apply, o.rotation_apply, Real.Angle.cos_coe,
      Real.Angle.sin_coe, hzero] using hrot t
  · intro t ht htP heq
    have hγ : γ t = γ 0 := sub_left_injective heq
    have ht0 := hb.injOn_Ico 0
      (show t ∈ Set.Ico 0 (0 + P) by simpa only [zero_add] using And.intro ht.le htP)
      (show (0 : ℝ) ∈ Set.Ico 0 (0 + P) by
        simpa only [zero_add] using And.intro (le_refl (0 : ℝ)) hb.period_pos) hγ
    exact ht.ne' ht0

/-- Every rational sample of a unit-speed boundary with uniformly rotating
tangent is a regular polygon. The original simple traversal fixes the winding. -/
theorem IsUnitSpeedBoundary.boundarySamples_regular_of_rotating_velocity
    {K : Set Plane} {P a : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (ha : 0 < a)
    (hv : ∀ t, HasDerivAt (deriv γ) (a • o.rightAngleRotation (deriv γ t)) t)
    {n : ℕ} (hn : 3 ≤ n) (t : ℝ) :
    IsRegularPolygon (fun i => boundarySamples γ P n i t) := by
  let c := γ 0 + a⁻¹ • o.rightAngleRotation (deriv γ 0)
  let v := -(a⁻¹ • o.rightAngleRotation (deriv γ 0))
  have hrot (s : ℝ) : γ s - c = o.rotation ((a * s : ℝ) : Real.Angle) v :=
    rotating_velocity_position_eq o ha.ne'
      (fun r => (hb.contDiff.differentiable (by simp) r).hasDerivAt) hv s
  have hvnorm : ‖v‖ = a⁻¹ := by
    simp only [v, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha),
      o.rightAngleRotation.norm_map, hb.unit_speed, mul_one]
  have hvne : v ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at hvnorm
    exact (inv_pos.mpr ha).ne' hvnorm.symm
  have hturn := hb.rotation_period_eq_two_pi o ha hvne hrot
  apply isRegularPolygon_of_rotation o hn (c := c) (phase := a * t) hvne
  intro i
  change γ (t + (i.val : ℝ) * (P / n)) = _
  have hangle : a * (t + (i.val : ℝ) * (P / n)) =
      a * t + 2 * Real.pi * (i.val : ℝ) / n := by
    calc
      _ = a * t + (a * P) * (i.val : ℝ) / n := by ring
      _ = _ := by rw [hturn]
  rw [← hangle, ← hrot]
  abel

end UlamFloating
