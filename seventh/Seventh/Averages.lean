import Seventh.ContactGeometry
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact contact-angle averages

The chord length is arbitrary. The dimensionless frequency is `π l / P`;
it specializes to the PDF's `2π/P` after the normalization `l=2`.
-/

namespace UlamFloating.Seventh

open MeasureTheory

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Translation does not change an integral over one full period. -/
theorem integral_translate_periodic {f : ℝ → ℝ} {P : ℝ}
    (hp : Function.Periodic f P) (d : ℝ) :
    (∫ t in (0 : ℝ)..P, f (t + d)) = ∫ t in (0 : ℝ)..P, f t := by
  rw [intervalIntegral.integral_comp_add_right]
  simpa [add_comm] using hp.intervalIntegral_add_eq d 0

/-- The pointwise partition identity gives mean contact angle `π/7`. -/
theorem ContactSystem.integral_angle {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) :
    (∫ t in (0 : ℝ)..P, α t) = P * (Real.pi / 7) := by
  have hi : (∫ t in (0 : ℝ)..P, ∑ i : Fin 7, α (t + (i.val : ℝ) * (P / 7))) =
      P * Real.pi := by
    simp only [hs.seven_angle_sum, intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [intervalIntegral.integral_finset_sum] at hi
  · simp_rw [integral_translate_periodic hs.periodic_angle] at hi
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hi
    norm_num at hi
    linarith
  · intro i _
    exact (hs.contDiff_angle.continuous.comp (continuous_id.add continuous_const)).intervalIntegrable _ _

/-- The chord's full turn gives the exact integral of the sine of its contact angle. -/
theorem ContactSystem.integral_sin_angle {γ : ℝ → Plane} {P h l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (hl : 0 < l) :
    (∫ t in (0 : ℝ)..P, Real.sin (α t)) = Real.pi * l := by
  have hi := intervalIntegral.integral_deriv_eq_sub
    (fun t (_ : t ∈ Set.uIcc 0 P) => hs.contDiff_lift.differentiable (by simp) t)
    (hs.contDiff_lift.continuous_deriv_one.intervalIntegrable _ _)
  have hturn := hs.full_turn 0
  simp only [zero_add] at hturn
  rw [hturn] at hi
  simp_rw [hs.angular_speed] at hi
  rw [intervalIntegral.integral_const_mul] at hi
  have hmul := congrArg (fun z : ℝ => l * z) hi
  field_simp [hl.ne'] at hmul
  nlinarith

end UlamFloating.Seventh
