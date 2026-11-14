import UlamFloating.ChordAngularVelocity
import UlamFloating.Disk

/-!
# Circles from uniformly rotating velocity

The center is obtained directly by differentiation. No existence theorem
for differential equations and no prior circle parametrization is needed.
-/

namespace UlamFloating

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- A curve whose velocity rotates at a constant nonzero rate has a fixed
center `γ + a⁻¹ • Jv`. This statement does not require unit speed. -/
theorem rotating_velocity_center_eq (o : Orientation ℝ E (Fin 2))
    {γ v : ℝ → E} {a : ℝ} (ha : a ≠ 0)
    (hγ : ∀ t, HasDerivAt γ (v t) t)
    (hv : ∀ t, HasDerivAt v (a • o.rightAngleRotation (v t)) t) (s t : ℝ) :
    γ s + a⁻¹ • o.rightAngleRotation (v s) =
      γ t + a⁻¹ • o.rightAngleRotation (v t) := by
  have hd (r : ℝ) : HasDerivAt
      (fun q => γ q + a⁻¹ • o.rightAngleRotation (v q)) 0 r := by
    have hj := o.rightAngleRotation.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      r (hv r)
    change HasDerivAt (fun q => o.rightAngleRotation (v q))
      (o.rightAngleRotation (a • o.rightAngleRotation (v r))) r at hj
    have h := (hγ r).add (hj.const_smul a⁻¹)
    simpa only [map_smul, o.rightAngleRotation_rightAngleRotation,
      smul_smul, inv_mul_cancel₀ ha, one_smul, add_neg_cancel] using h
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) s t

/-- A unit-speed curve whose velocity rotates at constant positive rate
lies on a circle of radius the reciprocal of that rate. -/
theorem exists_circle_of_rotating_unit_velocity (o : Orientation ℝ E (Fin 2))
    {γ v : ℝ → E} {a : ℝ} (ha : 0 < a)
    (hγ : ∀ t, HasDerivAt γ (v t) t)
    (hv : ∀ t, HasDerivAt v (a • o.rightAngleRotation (v t)) t)
    (hunit : ∀ t, ‖v t‖ = 1) :
    ∃ c : E, ∀ t, ‖γ t - c‖ = a⁻¹ := by
  refine ⟨γ 0 + a⁻¹ • o.rightAngleRotation (v 0), ?_⟩
  intro t
  have hc := rotating_velocity_center_eq o ha.ne' hγ hv t 0
  have he : γ t - (γ 0 + a⁻¹ • o.rightAngleRotation (v 0)) =
      -(a⁻¹ • o.rightAngleRotation (v t)) := by rw [← hc]; abel
  rw [he, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha),
    o.rightAngleRotation.norm_map, hunit, mul_one]

/-- Uniformly rotating velocity gives an explicit rotation of the position
about its fixed center. No unit-speed hypothesis is needed. -/
theorem rotating_velocity_position_eq (o : Orientation ℝ E (Fin 2))
    {γ v : ℝ → E} {a : ℝ} (ha : a ≠ 0)
    (hγ : ∀ t, HasDerivAt γ (v t) t)
    (hv : ∀ t, HasDerivAt v (a • o.rightAngleRotation (v t)) t) (t : ℝ) :
    γ t - (γ 0 + a⁻¹ • o.rightAngleRotation (v 0)) =
      o.rotation ((a * t : ℝ) : Real.Angle) (-(a⁻¹ • o.rightAngleRotation (v 0))) := by
  have hd (s : ℝ) : HasDerivAt (fun r => a * r) a s := by
    simpa only [mul_one] using (hasDerivAt_id s).const_mul a
  have hvel : v t = o.rotation ((a * t : ℝ) : Real.Angle) (v 0) := by
    simpa only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe] using
      rotation_solution_eq o hd (mul_zero a) hv t
  have hc := rotating_velocity_center_eq o ha hγ hv t 0
  calc
    _ = -(a⁻¹ • o.rightAngleRotation (v t)) := by rw [← hc]; abel
    _ = _ := by
      rw [hvel]
      simp only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
        map_add, map_smul, map_neg, o.rightAngleRotation_rightAngleRotation]
      module

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Constant positive rotation rate of the unit boundary tangent forces
the compact body to be a disk. -/
theorem IsUnitSpeedBoundary.isDisk_of_rotating_velocity
    {K : Set Plane} {P : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) {a : ℝ} (ha : 0 < a)
    (hv : ∀ t, HasDerivAt (deriv γ) (a • o.rightAngleRotation (deriv γ t)) t) :
    IsDisk K := by
  obtain ⟨c, hc⟩ := exists_circle_of_rotating_unit_velocity o ha
    (fun t => (hb.contDiff.differentiable (by simp) t).hasDerivAt) hv hb.unit_speed
  exact ⟨c, a⁻¹, inv_pos.mpr ha, hb.eq_closedBall (inv_pos.mpr ha) hc⟩

end UlamFloating
