import UlamFloating.ConstantAngles
import UlamFloating.PentagonGeometry
import UlamFloating.RotationGeometry

/-!
# The constant geometric pentagon solution

If the sampled-angle curve is constant, its tangent–chord angles are π/5.
The boundary tangent then rotates at a constant positive rate, so the body
is a disk. This closes the constant branch of the geometric angle reduction.
-/

namespace UlamFloating

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A constant geometric five-angle curve forces uniform rotation of the
original boundary tangent, with exact rate `(2/l) sin(π/5)`. -/
theorem IsUnitSpeedBoundary.fifth_velocity_rotation_of_constant_angles
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l)
    (hθ : ContDiff ℝ 1 (fun t => θ t))
    (hpos : ∀ t, 0 < deriv (fun s => θ s) t)
    (hrot : ∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0))
    (hp : ∀ t, θ (t + P) = θ t + 2 * Real.pi)
    (hconst : ∃ c, ∀ t, cyclicAngleCurve θ P 5 t = c) (t : ℝ) :
    HasDerivAt (deriv γ)
      (((2 / l) * Real.sin (Real.pi / 5)) • o.rightAngleRotation (deriv γ t)) t := by
  have hh : 0 < P / 5 := div_pos hb.period_pos (by norm_num)
  have hhalf : 2 * (P / 5) < P := by linarith [hb.period_pos]
  obtain ⟨α, ha, _, hsum, hspeed, htan⟩ :=
    hb.exists_tangent_chord_angles_with_rotation o θ hh hhalf hl hc hθ hpos hrot
  have hinc (s : ℝ) : θ (s + P / 5) - θ s = 2 * Real.pi / 5 :=
    angle_increment_eq_of_constant_cyclic_curve (by decide : 5 ≠ 0) hp hconst s
  have hfive : 5 * (P / 5) = P := by ring
  have ha' : Function.Periodic α (5 * (P / 5)) := by rwa [hfive]
  have hturn (s : ℝ) : θ (s + 5 * (P / 5)) = θ s + 2 * Real.pi := by
    rw [hfive, hp]
  have halpha (s : ℝ) : α s = Real.pi / 5 := by
    have h := five_tangent_angle_eq ha' hturn hsum s
    have h1 := hinc (s + P / 5)
    have h3 := hinc (s + 3 * (P / 5))
    rw [show s + P / 5 + P / 5 = s + 2 * (P / 5) by ring] at h1
    rw [show s + 3 * (P / 5) + P / 5 = s + 4 * (P / 5) by ring] at h3
    linarith
  have hv (s : ℝ) : deriv γ s =
      o.rotation ((θ s - Real.pi / 5 : ℝ) : Real.Angle)
        (l⁻¹ • (γ (P / 5) - γ 0)) := by
    apply (o.rotation ((Real.pi / 5 : ℝ) : Real.Angle)).injective
    rw [← halpha s, ← htan s, halpha s, o.rotation_rotation, ← Real.Angle.coe_add]
    rw [show Real.pi / 5 + (θ s - Real.pi / 5) = θ s by ring]
    rw [map_smul, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe, ← hrot s]
  have hdθ : HasDerivAt (fun s => θ s) ((2 / l) * Real.sin (Real.pi / 5)) t := by
    have h := (hθ.differentiable (by simp) t).hasDerivAt
    rwa [hspeed, halpha] at h
  have hd := hasDerivAt_rotation o (hdθ.sub_const (Real.pi / 5))
    (l⁻¹ • (γ (P / 5) - γ 0))
  have hfun : (fun s => o.rotation ((θ s - Real.pi / 5 : ℝ) : Real.Angle)
      (l⁻¹ • (γ (P / 5) - γ 0))) = deriv γ := funext (fun s => (hv s).symm)
  rwa [hfun, ← hv t] at hd

/-- Constancy of the actual five-angle curve forces the body to be a disk.
All lift hypotheses are available from the one-turn chord construction. -/
theorem IsUnitSpeedBoundary.isDisk_of_constant_fifth_angles
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l)
    (hθ : ContDiff ℝ 1 (fun t => θ t))
    (hpos : ∀ t, 0 < deriv (fun s => θ s) t)
    (hrot : ∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0))
    (hp : ∀ t, θ (t + P) = θ t + 2 * Real.pi)
    (hconst : ∃ c, ∀ t, cyclicAngleCurve θ P 5 t = c) : IsDisk K := by
  have ha : 0 < (2 / l) * Real.sin (Real.pi / 5) :=
    mul_pos (div_pos (by norm_num) hl)
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos]))
  exact hb.isDisk_of_rotating_velocity o ha
    (hb.fifth_velocity_rotation_of_constant_angles o θ hl hc hθ hpos hrot hp hconst)

/-- Constancy of the geometric five-angle curve forces every sampled
pentagon to be regular, with its original cyclic ordering. -/
theorem IsUnitSpeedBoundary.regular_pentagons_of_constant_angles
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l)
    (hθ : ContDiff ℝ 1 (fun t => θ t))
    (hpos : ∀ t, 0 < deriv (fun s => θ s) t)
    (hrot : ∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0))
    (hp : ∀ t, θ (t + P) = θ t + 2 * Real.pi)
    (hconst : ∃ c, ∀ t, cyclicAngleCurve θ P 5 t = c) (t : ℝ) :
    IsRegularPolygon (fun i => boundarySamples γ P 5 i t) := by
  have ha : 0 < (2 / l) * Real.sin (Real.pi / 5) :=
    mul_pos (div_pos (by norm_num) hl)
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos]))
  exact hb.boundarySamples_regular_of_rotating_velocity o ha
    (hb.fifth_velocity_rotation_of_constant_angles o θ hl hc hθ hpos hrot hp hconst)
    (by decide : 3 ≤ 5) t

end UlamFloating
