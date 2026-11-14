import UlamFloating.AreaConservation
import Mathlib.Tactic.Module

/-!
# Conservation of signed polygon moments

The edge identity splits the derivative of a polygon's first moment into
two differences of vertex quantities. Both sums cancel under any finite
successor permutation. Equal constant edge lengths enter only in the second
difference, through the derivative of the squared edge length.
-/

namespace UlamFloating

open scoped BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- A two-dimensional vector identity relating the area form and rotation. -/
theorem areaForm_smul_eq_rotation (o : Orientation ℝ E (Fin 2)) (u e : E) :
    o.areaForm u e • e = ‖e‖ ^ 2 • o.rightAngleRotation u -
      ⟪e, u⟫_ℝ • o.rightAngleRotation e := by
  apply ext_inner_right ℝ
  intro z
  simp only [inner_sub_left, real_inner_smul_left, o.inner_rightAngleRotation_left]
  have h := o.inner_mul_areaForm_sub e u z
  rw [o.areaForm_swap e u] at h
  linarith

/-- Under the two carousel laws, the area-vector correction is itself a
difference of rotated velocities. No nonzero-edge assumption is needed. -/
theorem areaForm_smul_eq_velocity_difference (o : Orientation ℝ E (Fin 2))
    {e u v : E} (horth : ⟪e, v - u⟫_ℝ = 0)
    (hmid : ∃ a : ℝ, u + v = a • e) :
    o.areaForm u e • e = -(‖e‖ ^ 2 / 2) •
      (o.rightAngleRotation v - o.rightAngleRotation u) := by
  obtain ⟨a, ha⟩ := hmid
  have hi := congrArg (fun w => ⟪e, w⟫_ℝ) ha
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hi
  simp only [inner_sub_right] at horth
  have hcoef : ⟪e, u⟫_ℝ = a * ‖e‖ ^ 2 / 2 := by linarith
  have hv : v = a • e - u := by rw [← ha]; abel
  rw [areaForm_smul_eq_rotation, hcoef, hv, map_sub, map_smul]
  module

/-- The algebraic derivative of one first-moment summand, before imposing
the constant-length law. -/
theorem moment_edge_rate (o : Orientation ℝ E (Fin 2)) {p q u v : E}
    (hmid : ∃ a : ℝ, u + v = a • (q - p)) :
    (o.areaForm u q + o.areaForm p v) • (p + q) +
        o.areaForm p q • (u + v) =
      (2 * o.areaForm u p) • p - (2 * o.areaForm v q) • q -
        o.areaForm u (q - p) • (q - p) := by
  obtain ⟨a, ha⟩ := hmid
  have hv : v = a • (q - p) - u := by rw [← ha]; abel
  rw [hv]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, o.areaForm_apply_self, o.areaForm_swap p u]
  module

end UlamFloating
