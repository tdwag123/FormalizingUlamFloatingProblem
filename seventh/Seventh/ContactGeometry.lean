import Seventh.ContactAlgebra
import UlamFloating.RotatingVelocity

/-!
# Contact-angle data extracted from the original boundary

All geometric equations below refer to the same original boundary. In
particular an arbitrary solution of the angle ODE does not qualify. No scaling,
curvature bound, or smoothness beyond the input `C¹` boundary is assumed.
-/

namespace UlamFloating.Seventh

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Geometric contact-angle data, with the original chord length and boundary
retained. The chord lift need not be normalized at zero in applications. -/
structure ContactSystem (γ : ℝ → Plane) (P h l : ℝ)
    (o : Orientation ℝ Plane (Fin 2)) (θ α : ℝ → ℝ) : Prop where
  contDiff_lift : ContDiff ℝ 1 θ
  contDiff_angle : ContDiff ℝ 1 α
  periodic_angle : Function.Periodic α P
  full_turn : ∀ t, θ (t + P) = θ t + 2 * Real.pi
  angle_range : ∀ t, 0 < α t ∧ α t < Real.pi
  chord_rotation : ∀ t, γ (t + h) - γ t =
    Real.cos (θ t) • (γ h - γ 0) + Real.sin (θ t) • o.rightAngleRotation (γ h - γ 0)
  consecutive : ∀ t, α t + α (t + h) = θ (t + h) - θ t
  angular_speed : ∀ t, deriv θ t = (2 / l) * Real.sin (α t)
  tangent_rotation : ∀ t, l⁻¹ • (γ (t + h) - γ t) =
    o.rotation (α t : Real.Angle) (deriv γ t)

/-- A constant-chord boundary at one seventh has `C¹` contact angles, with
the lift, derivative law, phase relation, and original tangent all preserved. -/
theorem exists_contactSystem {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l) :
    ∃ (o : Orientation ℝ Plane (Fin 2)) (θ α : ℝ → ℝ),
      ContactSystem γ P (P / 7) l o θ α := by
  have hh : 0 < P / 7 := div_pos hb.period_pos (by norm_num)
  have hhalf : 2 * (P / 7) < P := by linarith [hb.period_pos]
  obtain ⟨o, θ, hθ, _, _, _, hbound, hrot, hshift⟩ :=
    hb.chord_angle_coordinates_one_turn hh hhalf hl hc
  have hp (t : ℝ) : θ (t + P) = θ t + 2 * Real.pi := by
    simpa only [Int.cast_one, one_mul] using hshift t 1
  obtain ⟨α, ha, harange, hsum, hspeed, htan⟩ :=
    hb.exists_tangent_chord_angles_with_rotation o θ hh hhalf hl hc hθ
      (fun t => (hbound t).1) hrot
  have hseven : 7 * (P / 7) = P := by ring
  have ha' : Function.Periodic α (7 * (P / 7)) := by rwa [hseven]
  have hp' (t : ℝ) : θ (t + 7 * (P / 7)) = θ t + 2 * Real.pi := by rw [hseven, hp]
  exact ⟨o, θ, α, hθ, contDiff_seven_contact_angle ha' hp' hsum hθ,
    ha, hp, harange, hrot, hsum, hspeed, htan⟩

/-- The seven sampled contact angles sum pointwise to pi. -/
theorem ContactSystem.seven_angle_sum {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (t : ℝ) :
    ∑ i : Fin 7, α (t + (i.val : ℝ) * (P / 7)) = Real.pi := by
  have he : 7 * (P / 7) = P := by ring
  apply seven_contact_angle_sum (h := P / 7)
  · simpa only [he] using hs.periodic_angle
  · simpa only [he] using hs.full_turn
  · exact hs.consecutive

/-- The contact-angle chain holds with the unnormalized side length. -/
theorem ContactSystem.chain {γ : ℝ → Plane} {P h l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) :
    deriv α t + deriv α (t + h) =
      (2 / l) * (Real.sin (α (t + h)) - Real.sin (α t)) :=
  contact_angle_chain (hs.contDiff_angle.differentiable (by simp))
    (hs.contDiff_lift.differentiable (by simp)) hs.consecutive hs.angular_speed t

/-- Reconstruction of the actual tangent from the chord lift and contact angle. -/
theorem ContactSystem.tangent_eq {γ : ℝ → Plane} {P h l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) :
    deriv γ t = o.rotation ((θ t - α t : ℝ) : Real.Angle)
      (l⁻¹ • (γ h - γ 0)) := by
  apply (o.rotation (α t : Real.Angle)).injective
  rw [← hs.tangent_rotation, o.rotation_rotation, ← Real.Angle.coe_add]
  rw [show α t + (θ t - α t) = θ t by ring]
  rw [map_smul, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
    ← hs.chord_rotation]

/-- The tangent lift `θ - α` is `C¹`; differentiating gives the curvature
coefficient `(2/l) sin α - α'`. Its nonnegativity is a separate convexity step. -/
theorem ContactSystem.tangent_deriv {γ : ℝ → Plane} {P h l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) :
    HasDerivAt (deriv γ)
      (((2 / l) * Real.sin (α t) - deriv α t) • o.rightAngleRotation (deriv γ t)) t := by
  have hd := ((hs.contDiff_lift.differentiable (by simp) t).hasDerivAt).sub
    ((hs.contDiff_angle.differentiable (by simp) t).hasDerivAt)
  rw [hs.angular_speed] at hd
  have hv := hasDerivAt_rotation o hd (l⁻¹ • (γ h - γ 0))
  simp only [Pi.sub_apply] at hv
  have he : (fun s => o.rotation ((θ s - α s : ℝ) : Real.Angle)
      (l⁻¹ • (γ h - γ 0))) = deriv γ := funext (fun s => (hs.tangent_eq s).symm)
  rwa [he, ← hs.tangent_eq t] at hv

/-- The constant-contact-angle branch is a disk, for arbitrary positive
chord length. The conclusion is equality of the body with a closed disk. -/
theorem ContactSystem.isDisk_of_constant {K : Set Plane} {P h l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (hconst : ∀ t, α t = α 0) : IsDisk K := by
  have ha : 0 < (2 / l) * Real.sin (α 0) :=
    mul_pos (div_pos (by norm_num) hl)
      (Real.sin_pos_of_pos_of_lt_pi (hs.angle_range 0).1 (hs.angle_range 0).2)
  apply hb.isDisk_of_rotating_velocity o ha
  intro t
  have hd : deriv α t = 0 := by
    rw [show α = fun _ => α 0 from funext hconst]
    simp
  simpa only [hconst t, hd, sub_zero] using hs.tangent_deriv t

end UlamFloating.Seventh
