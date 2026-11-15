import Seventh.ArcProjection
import Seventh.Averages
import Seventh.Variance

/-!
# The centered periodic part of the tangent lift

Arclength remains the independent variable. The affine term has speed `2π/P`,
and its periodic remainder is centered by subtracting its actual integral.
-/

namespace UlamFloating.Seventh

open MeasureTheory

/-- The mean-zero periodic remainder of the lifted tangent angle. -/
noncomputable def tangentFluctuation (P : ℝ) (θ α : ℝ → ℝ) (t : ℝ) : ℝ :=
  θ t - α t - (2 * Real.pi / P) * t -
    P⁻¹ * ∫ s in (0 : ℝ)..P, θ s - α s - (2 * Real.pi / P) * s

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem ContactSystem.contDiff_tangentFluctuation {γ : ℝ → Plane} {P h l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) : ContDiff ℝ 1 (tangentFluctuation P θ α) := by
  have hθ := hs.contDiff_lift
  have hα := hs.contDiff_angle
  unfold tangentFluctuation
  fun_prop

theorem ContactSystem.periodic_tangentFluctuation {γ : ℝ → Plane} {P h l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (hP : 0 < P) :
    Function.Periodic (tangentFluctuation P θ α) P := by
  intro t
  simp only [tangentFluctuation, hs.full_turn, hs.periodic_angle t]
  field_simp
  ring

theorem ContactSystem.integral_tangentFluctuation {γ : ℝ → Plane} {P h l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (hP : 0 < P) :
    (∫ t in (0 : ℝ)..P, tangentFluctuation P θ α t) = 0 := by
  have hθ := hs.contDiff_lift.continuous
  have hα := hs.contDiff_angle.continuous
  unfold tangentFluctuation
  rw [intervalIntegral.integral_sub
    ((show Continuous (fun t => θ t - α t - (2 * Real.pi / P) * t) by fun_prop).intervalIntegrable _ _)
    intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [← mul_assoc, mul_inv_cancel₀ hP.ne', one_mul, sub_self]

/-- The exact shift relation between tangent fluctuation and centered contact angle. -/
theorem ContactSystem.shift_tangentFluctuation {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (t : ℝ) :
    tangentFluctuation P θ α (t + P / 7) - tangentFluctuation P θ α t =
      2 * (α t - Real.pi / 7) := by
  have hi := hs.tangent_lift_increment t
  have he : (2 * Real.pi / P) * (P / 7) = 2 * (Real.pi / 7) := by field_simp
  dsimp [tangentFluctuation]
  rw [mul_add]
  linarith

/-- The derivative law in arclength coordinates, with the affine term removed. -/
theorem ContactSystem.hasDerivAt_tangentFluctuation {γ : ℝ → Plane} {P h l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) :
    HasDerivAt (tangentFluctuation P θ α)
      ((2 / l) * Real.sin (α t) - deriv α t - 2 * Real.pi / P) t := by
  have hθ := (hs.contDiff_lift.differentiable (by simp) t).hasDerivAt
  have hα := (hs.contDiff_angle.differentiable (by simp) t).hasDerivAt
  have hd := ((hθ.sub hα).sub ((hasDerivAt_id t).const_mul (2 * Real.pi / P))).sub_const
    (P⁻¹ * ∫ s in (0 : ℝ)..P, θ s - α s - (2 * Real.pi / P) * s)
  simpa only [tangentFluctuation, hs.angular_speed, mul_one, Pi.sub_apply, id_eq] using hd

end UlamFloating.Seventh
