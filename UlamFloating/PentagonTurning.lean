import UlamFloating.PeriodicPrimitive
import UlamFloating.PentagonGeometry

/-!
# The angular advance over a pentagon shape period

The geometric sine law expresses chord angular velocity as a function of
the shape coordinates. Consequently every shape period is a period of
angular velocity. One full boundary turn then fixes the angular advance
over any shape period whose integer multiple is the traversal period.
-/

namespace UlamFloating

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Express the angular velocity of the original chord lift directly in
the sampled shape coordinates, retaining its geometric time scale. -/
theorem IsUnitSpeedBoundary.fifth_chord_angle_speed
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l)
    (hθ : ContDiff ℝ 1 (fun t => θ t))
    (hpos : ∀ t, 0 < deriv (fun s => θ s) t)
    (hrot : ∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0))
    (hturn : ∀ t, θ (t + P) = θ t + 2 * Real.pi) (t : ℝ) :
    deriv (fun s => θ s) t = -(2 / l) *
      Real.sin (cyclicAngleCurve θ P 5 t 1 + cyclicAngleCurve θ P 5 t 3) := by
  have hh : 0 < P / 5 := div_pos hb.period_pos (by norm_num)
  have hhalf : 2 * (P / 5) < P := by linarith [hb.period_pos]
  obtain ⟨α, ha, _, hsum, hspeed⟩ :=
    hb.exists_tangent_chord_angles o θ hh hhalf hl hc hθ hpos hrot
  have hfive : 5 * (P / 5) = P := by ring
  have ha' : Function.Periodic α (5 * (P / 5)) := by rwa [hfive]
  have hturn' (s : ℝ) : θ (s + 5 * (P / 5)) = θ s + 2 * Real.pi := by
    rw [hfive, hturn]
  have he := five_chord_angle_speed ha' hturn' hsum hspeed t
  simpa only [cyclicAngleCurve, PiLp.toLp_apply, cyclicAngleCoordinates,
    boundarySamples, sampledVertex, Fin.val_one,
    show (3 : Fin 5).val = 3 by decide,
    Nat.cast_one, Nat.cast_ofNat, one_mul,
    show t + P / 5 + P / 5 = t + 2 * (P / 5) by ring,
    show t + 3 * (P / 5) + P / 5 = t + 4 * (P / 5) by ring] using he

/-- Every period of the sampled pentagon shape is a period of the angular
velocity of its actual chord lift. -/
theorem IsUnitSpeedBoundary.periodic_chord_angle_deriv_of_fifth_shape_period
    {K : Set Plane} {P l T : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l)
    (hθ : ContDiff ℝ 1 (fun t => θ t))
    (hpos : ∀ t, 0 < deriv (fun s => θ s) t)
    (hrot : ∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0))
    (hturn : ∀ t, θ (t + P) = θ t + 2 * Real.pi)
    (hp : Function.Periodic (cyclicAngleCurve θ P 5) T) :
    Function.Periodic (deriv (fun s => θ s)) T := by
  intro t
  rw [hb.fifth_chord_angle_speed o θ hl hc hθ hpos hrot hturn,
    hb.fifth_chord_angle_speed o θ hl hc hθ hpos hrot hturn, hp]

/-- If `P = m T`, a shape period `T` advances the actual chord angle by
exactly `2π/m`. This uses the one-turn boundary lift, not a rotation
number supplied as an additional hypothesis. -/
theorem IsUnitSpeedBoundary.chord_angle_advance_of_fifth_shape_period
    {K : Set Plane} {P l T : ℝ} {m : ℕ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l)
    (hθ : ContDiff ℝ 1 (fun t => θ t))
    (hpos : ∀ t, 0 < deriv (fun s => θ s) t)
    (hrot : ∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0))
    (hturn : ∀ t, θ (t + P) = θ t + 2 * Real.pi)
    (hp : Function.Periodic (cyclicAngleCurve θ P 5) T)
    (hm : m ≠ 0) (hP : P = (m : ℝ) * T) (t : ℝ) :
    θ (t + T) - θ t = 2 * Real.pi / m := by
  apply sub_eq_div_of_periodic_deriv (hθ.differentiable (by simp))
    (hb.periodic_chord_angle_deriv_of_fifth_shape_period o θ hl hc hθ hpos hrot hturn hp) hm
  rw [← hP]
  have he := hturn 0
  simp only [zero_add] at he
  linarith

end UlamFloating
