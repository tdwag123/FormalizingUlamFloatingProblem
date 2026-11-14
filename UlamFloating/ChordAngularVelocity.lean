import UlamFloating.ChordAngleRange
import UlamFloating.TangentChordAngles

/-!
# Angular velocity of geometric chord lifts

The derivative of any differentiable chord-angle lift equals the intrinsic
angular speed. In particular a lift with positive derivative has positive
tangent–chord orientation, independently of how the lift was constructed.
-/

namespace UlamFloating

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Differentiating a planar rotation gives angular speed times the
right-angle rotation of the current vector. -/
theorem hasDerivAt_rotation (o : Orientation ℝ E (Fin 2)) {θ : ℝ → ℝ}
    {a t : ℝ} (hθ : HasDerivAt θ a t) (v : E) :
    HasDerivAt (fun s => o.rotation (θ s : Real.Angle) v)
      (a • o.rightAngleRotation (o.rotation (θ t : Real.Angle) v)) t := by
  have hd := (hθ.cos.smul_const v).add (hθ.sin.smul_const (o.rightAngleRotation v))
  simp only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
    map_add, map_smul, o.rightAngleRotation_rightAngleRotation]
  convert hd using 1
  module

/-- A real lift reconstructing a rotating curve has the intrinsic angular
speed as its derivative whenever that curve is nonzero. -/
theorem angular_derivative_eq (o : Orientation ℝ E (Fin 2)) {e : ℝ → E}
    {θ : ℝ → ℝ} {a t : ℝ} (hθ : DifferentiableAt ℝ θ t)
    (he : HasDerivAt e (a • o.rightAngleRotation (e t)) t) (hne : e t ≠ 0)
    (hrot : ∀ s, e s = o.rotation (θ s : Real.Angle) (e 0)) : deriv θ t = a := by
  have hd := hasDerivAt_rotation o hθ.hasDerivAt (e 0)
  have hfun : (fun s => o.rotation (θ s : Real.Angle) (e 0)) = e :=
    funext (fun s => (hrot s).symm)
  rw [hfun, ← hrot t] at hd
  apply smul_left_injective ℝ (show o.rightAngleRotation (e t) ≠ 0 from
    fun hz => hne (o.rightAngleRotation.injective (by simpa using hz)))
  exact hd.unique he

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Every differentiable real chord-angle lift has the expected exact
angular speed, in its own orientation. -/
theorem IsUnitSpeedBoundary.chord_angle_deriv {K : Set Plane} {P h l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) {θ : ℝ → ℝ}
    (hl : 0 < l) (hc : HasConstantChord γ h l) {t : ℝ}
    (hθ : DifferentiableAt ℝ θ t)
    (hrot : ∀ s, γ (s + h) - γ s = Real.cos (θ s) • (γ h - γ 0) +
      Real.sin (θ s) • o.rightAngleRotation (γ h - γ 0)) :
    deriv θ t = 2 * o.areaForm (deriv γ t) (γ (t + h) - γ t) / l ^ 2 := by
  apply angular_derivative_eq o hθ (hb.hasDerivAt_chord_rotation o hl hc t)
  · intro hz
    have := hc t
    rw [dist_eq_norm, hz, norm_zero] at this
    exact hl.ne' this.symm
  · intro s
    simpa only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe, zero_add]
      using hrot s

/-- Positivity of a chord lift's angular derivative determines the
positive orientation of its tangent and chord. -/
theorem IsUnitSpeedBoundary.chord_area_pos_of_angle_deriv_pos
    {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) {θ : ℝ → ℝ}
    (hl : 0 < l) (hc : HasConstantChord γ h l) {t : ℝ}
    (hθ : DifferentiableAt ℝ θ t) (hpos : 0 < deriv θ t)
    (hrot : ∀ s, γ (s + h) - γ s = Real.cos (θ s) • (γ h - γ 0) +
      Real.sin (θ s) • o.rightAngleRotation (γ h - γ 0)) :
    0 < o.areaForm (deriv γ t) (γ (t + h) - γ t) := by
  rw [hb.chord_angle_deriv o hl hc hθ hrot] at hpos
  have := (div_pos_iff_of_pos_right (sq_pos_of_pos hl)).mp hpos
  linarith

end UlamFloating
