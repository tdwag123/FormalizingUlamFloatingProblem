import Seventh.ContactFourier

/-!
# Closure of the actual boundary

The first-harmonic estimate needs the closed curve, not just its contact-angle
equations. We integrate the original unit tangent and use its rotation formula.
-/

namespace UlamFloating.Seventh

open MeasureTheory
open scoped InnerProductSpace

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem integral_boundary_deriv_eq_zero {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) : (∫ t in (0 : ℝ)..P, deriv γ t) = 0 := by
  have he := intervalIntegral.integral_deriv_eq_sub
    (fun t (_ : t ∈ Set.uIcc 0 P) => hb.contDiff.differentiable (by simp) t)
    (hb.contDiff.continuous_deriv_one.intervalIntegrable _ _)
  have hp := hb.periodic 0
  simp only [zero_add] at hp
  rwa [hp, sub_self] at he

theorem integral_inner_boundary_deriv_eq_zero {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (v : Plane) :
    (∫ t in (0 : ℝ)..P, ⟪v, deriv γ t⟫_ℝ) = 0 := by
  have he := (innerSL ℝ v).intervalIntegral_comp_comm (μ := volume)
    (hb.contDiff.continuous_deriv_one.intervalIntegrable 0 P)
  change (∫ t in (0 : ℝ)..P, ⟪v, deriv γ t⟫_ℝ) = ⟪v, ∫ t in (0 : ℝ)..P, deriv γ t⟫_ℝ at he
  rw [integral_boundary_deriv_eq_zero hb, inner_zero_right] at he
  exact he

/-- Both components of the exponential of the true lifted tangent integrate to zero. -/
theorem ContactSystem.integral_exp_tangent_lift_eq_zero {K : Set Plane} {P h l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ h l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) :
    (∫ t in (0 : ℝ)..P, Complex.exp (((θ t - α t : ℝ) : ℂ) * Complex.I)) = 0 := by
  let v := l⁻¹ • (γ h - γ 0)
  have hv : ‖v‖ = 1 := by
    have he : ‖γ h - γ 0‖ = l := by simpa [dist_eq_norm] using hc 0
    simp [v, norm_smul, Real.norm_eq_abs, abs_of_pos hl, he, hl.ne']
  have hcross : ⟪v, o.rightAngleRotation v⟫_ℝ = 0 := by
    rw [o.inner_rightAngleRotation_right, o.areaForm_apply_self, neg_zero]
  have hcross' : ⟪o.rightAngleRotation v, v⟫_ℝ = 0 := by rw [real_inner_comm, hcross]
  have hcos (t : ℝ) : ⟪v, deriv γ t⟫_ℝ = Real.cos (θ t - α t) := by
    rw [hs.tangent_eq]
    change ⟪v, o.rotation ((θ t - α t : ℝ) : Real.Angle) v⟫_ℝ = _
    simp only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
      inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      hv, one_pow, mul_one, hcross, mul_zero, add_zero]
  have hsin (t : ℝ) : ⟪o.rightAngleRotation v, deriv γ t⟫_ℝ = Real.sin (θ t - α t) := by
    rw [hs.tangent_eq]
    change ⟪o.rightAngleRotation v, o.rotation ((θ t - α t : ℝ) : Real.Angle) v⟫_ℝ = _
    simp only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
      inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      o.rightAngleRotation.norm_map, hv, one_pow, mul_one, hcross', mul_zero, zero_add]
  have hc0 := integral_inner_boundary_deriv_eq_zero hb v
  have hs0 := integral_inner_boundary_deriv_eq_zero hb (o.rightAngleRotation v)
  simp_rw [hcos] at hc0
  simp_rw [hsin] at hs0
  have hθ := hs.contDiff_lift.continuous
  have hα := hs.contDiff_angle.continuous
  simp_rw [exp_real_mul_I]
  rw [intervalIntegral.integral_add
    ((show Continuous (fun t => (Real.cos (θ t - α t) : ℂ)) by fun_prop).intervalIntegrable _ _)
    ((show Continuous (fun t => (Real.sin (θ t - α t) : ℂ) * Complex.I) by fun_prop).intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal, hc0, hs0]
  simp

/-- Closure expressed as the first Fourier coefficient of the tangent exponential. -/
theorem ContactSystem.fourier_exp_tangentFluctuation_eq_zero
    {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l) (hc : HasConstantChord γ h l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) :
    fourierCoeffOn hb.period_pos
      (fun t => Complex.exp ((tangentFluctuation P θ α t : ℂ) * Complex.I)) (-1) = 0 := by
  let m := P⁻¹ * ∫ s in (0 : ℝ)..P, θ s - α s - (2 * Real.pi / P) * s
  have he (t : ℝ) : fourier 1 (t : AddCircle P) *
      Complex.exp ((tangentFluctuation P θ α t : ℂ) * Complex.I) =
      Complex.exp (-(m : ℂ) * Complex.I) * Complex.exp (((θ t - α t : ℝ) : ℂ) * Complex.I) := by
    rw [fourier_coe_apply, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    change 2 * (Real.pi : ℂ) * Complex.I * (1 : ℤ) * (t : ℂ) / (P : ℂ) +
      ((θ t - α t - (2 * Real.pi / P) * t - m : ℝ) : ℂ) * Complex.I = _
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div,
      Complex.ofReal_ofNat, Int.cast_one]
    ring
  rw [fourierCoeffOn_integral]
  simp only [neg_neg]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, hs.integral_exp_tangent_lift_eq_zero hb hl hc,
    mul_zero, mul_zero]

end UlamFloating.Seventh
