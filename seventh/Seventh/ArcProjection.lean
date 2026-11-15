import Seventh.Curvature
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Projection of the intervening boundary arc

This is the common-boundary input to Lemma 3.1 of the supplied proof. We
derive `h * cos (α t) ≤ l` from the actual arc `γ([t,t+h])`; it is not a
consequence asserted for arbitrary solutions of the angle equations.
-/

namespace UlamFloating.Seventh

open MeasureTheory
open scoped InnerProductSpace

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Inner product of two rotations of one unit vector. -/
theorem inner_rotations_unit (o : Orientation ℝ Plane (Fin 2)) {v : Plane}
    (hv : ‖v‖ = 1) (a b : ℝ) :
    ⟪o.rotation (a : Real.Angle) v, o.rotation (b : Real.Angle) v⟫_ℝ =
      Real.cos (b - a) := by
  have hcross : ⟪v, o.rightAngleRotation v⟫_ℝ = 0 := by
    rw [o.inner_rightAngleRotation_right, o.areaForm_apply_self, neg_zero]
  have hcross' : ⟪o.rightAngleRotation v, v⟫_ℝ = 0 := by
    rw [real_inner_comm, hcross]
  simp only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    hcross, hcross', mul_zero, add_zero, zero_add,
    real_inner_self_eq_norm_sq, o.rightAngleRotation.norm_map, hv, one_pow, mul_one]
  rw [Real.cos_sub]

/-- The actual lifted tangent direction is monotone by convexity. -/
theorem ContactSystem.tangent_lift_monotone {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l) (hc : HasConstantChord γ h l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) : Monotone (fun t => θ t - α t) := by
  have hdθ := hs.contDiff_lift.differentiable (by simp)
  have hdα := hs.contDiff_angle.differentiable (by simp)
  apply monotone_of_deriv_nonneg (hdθ.sub hdα)
  intro t
  rw [deriv_sub (hdθ t) (hdα t), hs.angular_speed]
  exact hs.curvature_nonneg hb hl hc t

/-- Reflection fixes the real tangent-angle increment, without a branch ambiguity. -/
theorem ContactSystem.tangent_lift_increment {P h l : ℝ} {γ : ℝ → Plane}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) :
    (θ (t + h) - α (t + h)) - (θ t - α t) = 2 * α t := by
  have he := hs.consecutive t
  linarith

/-- Every tangent on the intervening arc projects onto the chord direction
by at least `cos (α t)`. Acuteness of the contact angle is not assumed. -/
theorem ContactSystem.chord_projection_bound {K : Set Plane} {P h l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ h l) {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) {t u : ℝ} (hu : u ∈ Set.Icc t (t + h)) :
    Real.cos (α t) ≤ ⟪l⁻¹ • (γ (t + h) - γ t), deriv γ u⟫_ℝ := by
  let v := l⁻¹ • (γ h - γ 0)
  have hv : ‖v‖ = 1 := by
    have he : ‖γ h - γ 0‖ = l := by simpa [dist_eq_norm] using hc 0
    simp [v, norm_smul, Real.norm_eq_abs, abs_of_pos hl, he, hl.ne']
  have hedge : l⁻¹ • (γ (t + h) - γ t) = o.rotation (θ t : Real.Angle) v := by
    rw [map_smul, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
      ← hs.chord_rotation]
  rw [hedge, hs.tangent_eq, inner_rotations_unit o hv]
  have hlo := hs.tangent_lift_monotone hb hl hc hu.1
  have hhi := hs.tangent_lift_monotone hb hl hc hu.2
  have hinc := hs.tangent_lift_increment t
  have habs : |θ u - α u - θ t| ≤ α t := abs_le.mpr ⟨by linarith, by linarith⟩
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (θ u - α u - θ t))
    (hs.angle_range t).2.le habs
  simpa only [Real.cos_abs] using hcos

/-- Exact boundary-arc projection inequality, before division or arccosine.
For `h=P/7` it gives the lower-angle bound used by the certificate. -/
theorem ContactSystem.arc_projection {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hh : 0 < h) (hl : 0 < l)
    (hc : HasConstantChord γ h l) {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) : h * Real.cos (α t) ≤ l := by
  let e := l⁻¹ • (γ (t + h) - γ t)
  let f := fun s => ⟪e, γ s⟫_ℝ
  let g := fun s => ⟪e, deriv γ s⟫_ℝ
  have hd (s : ℝ) : HasDerivAt f (g s) s :=
    (innerSL ℝ e).hasFDerivAt.comp_hasDerivAt s
      (hb.contDiff.differentiable (by simp) s).hasDerivAt
  have hg : Continuous g := (innerSL ℝ e).continuous.comp hb.contDiff.continuous_deriv_one
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s (_ : s ∈ Set.uIcc t (t + h)) => hd s) (hg.intervalIntegrable _ _)
  have he : ‖γ (t + h) - γ t‖ = l := by simpa [dist_eq_norm] using hc t
  have hdiff : f (t + h) - f t = l := by
    dsimp [f, e]
    rw [← inner_sub_right, real_inner_smul_left, real_inner_self_eq_norm_sq, he]
    field_simp [hl.ne']
  rw [hdiff] at hi
  have hle := intervalIntegral.integral_mono_on (by linarith : t ≤ t + h)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.cos (α t)) volume t (t + h))
    (hg.intervalIntegrable _ _) (fun s hs' => hs.chord_projection_bound hb hl hc hs')
  rw [hi] at hle
  simpa using hle

end UlamFloating.Seventh
