import UlamFloating.BoundaryTangentAngles
import UlamFloating.PentagonDynamics

/-!
# Five-angle identities from tangent–chord geometry

The odd cyclic linear system determines each tangent angle from the chord
increments. Substitution in the sine speed law gives the pentagon equation.
-/

namespace UlamFloating

/-- Solve the five consecutive tangent-angle equations using one full turn
and periodicity. This is a real linear identity without trigonometry. -/
theorem five_tangent_angle_eq {α θ : ℝ → ℝ} {h : ℝ}
    (ha : Function.Periodic α (5 * h))
    (hθ : ∀ t, θ (t + 5 * h) = θ t + 2 * Real.pi)
    (hsum : ∀ t, α t + α (t + h) = θ (t + h) - θ t) (t : ℝ) :
    α t = Real.pi - (θ (t + 2 * h) - θ (t + h)) -
      (θ (t + 4 * h) - θ (t + 3 * h)) := by
  have h0 := hsum t
  have h1 := hsum (t + h)
  have h2 := hsum (t + 2 * h)
  have h3 := hsum (t + 3 * h)
  have h4 := hsum (t + 4 * h)
  rw [show t + h + h = t + 2 * h by ring] at h1
  rw [show t + 2 * h + h = t + 3 * h by ring] at h2
  rw [show t + 3 * h + h = t + 4 * h by ring] at h3
  rw [show t + 4 * h + h = t + 5 * h by ring, ha, hθ] at h4
  linarith

/-- On a five-chord traversal, the geometric sine speed law can be written
using two nonadjacent cyclic angle coordinates. -/
theorem five_chord_angle_speed {α θ : ℝ → ℝ} {h k : ℝ}
    (ha : Function.Periodic α (5 * h))
    (hθ : ∀ t, θ (t + 5 * h) = θ t + 2 * Real.pi)
    (hsum : ∀ t, α t + α (t + h) = θ (t + h) - θ t)
    (hspeed : ∀ t, deriv θ t = k * Real.sin (α t)) (t : ℝ) :
    deriv θ t = -k * Real.sin ((Real.pi + θ (t + h) - θ (t + 2 * h)) +
      (Real.pi + θ (t + 3 * h) - θ (t + 4 * h))) := by
  rw [hspeed]
  have halpha := five_tangent_angle_eq ha hθ hsum t
  have he : α t = ((Real.pi + θ (t + h) - θ (t + 2 * h)) +
      (Real.pi + θ (t + 3 * h) - θ (t + 4 * h))) - Real.pi := by linarith
  rw [he, Real.sin_sub_pi]
  ring

/-- Differentiating pi minus a consecutive chord increment gives the
five-angle equation in a single time coordinate. -/
theorem hasDerivAt_five_angle_coordinate {α θ : ℝ → ℝ} {h k : ℝ}
    (ha : Function.Periodic α (5 * h))
    (hθ : ∀ t, θ (t + 5 * h) = θ t + 2 * Real.pi)
    (hd : Differentiable ℝ θ)
    (hsum : ∀ t, α t + α (t + h) = θ (t + h) - θ t)
    (hspeed : ∀ t, deriv θ t = k * Real.sin (α t)) (t : ℝ) :
    let x := fun s => Real.pi + θ s - θ (s + h)
    HasDerivAt x (k * (Real.sin (x (t + 2 * h) + x (t + 4 * h)) -
      Real.sin (x (t + h) + x (t + 3 * h)))) t := by
  intro x
  have hv := ((hd (t + h)).hasDerivAt.scomp t ((hasDerivAt_id t).add_const h))
  have hx : HasDerivAt x (deriv θ t - deriv θ (t + h)) t := by
    simpa only [one_smul] using ((hd t).hasDerivAt.const_add Real.pi).sub hv
  have he (s : ℝ) : deriv θ s = -k * Real.sin (x (s + h) + x (s + 3 * h)) := by
    simpa only [x, show s + h + h = s + 2 * h by ring,
      show s + 3 * h + h = s + 4 * h by ring] using
        five_chord_angle_speed ha hθ hsum hspeed s
  rw [he t, he (t + h), show t + h + h = t + 2 * h by ring,
    show t + h + 3 * h = t + 4 * h by ring] at hx
  convert hx using 1
  ring

end UlamFloating
