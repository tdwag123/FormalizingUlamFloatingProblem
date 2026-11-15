import Seventh.Variance
import Seventh.AngleBounds
import Mathlib.Analysis.Convex.Deriv

/-!
# A quantitative concavity estimate for sine

The lower bound on the second derivative gives the Jensen deficit that
controls the contact-angle variance.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

/-- Adding a quadratic compensates for the minimum magnitude of sine's
second derivative on a positive acute interval. -/
theorem concave_sin_add_quadratic {B U : ℝ} (hB : 0 ≤ B) (hU : U ≤ Real.pi / 2) :
    ConcaveOn ℝ (Icc B U) (fun x => Real.sin x + (Real.sin B / 2) * x ^ 2) := by
  let f : ℝ → ℝ := fun x => Real.sin x + (Real.sin B / 2) * x ^ 2
  let g : ℝ → ℝ := fun x => Real.cos x + Real.sin B * x
  have hf (x : ℝ) : HasDerivAt f (g x) x := by
    convert (Real.hasDerivAt_sin x).add
      (((hasDerivAt_id x).pow 2).const_mul (Real.sin B / 2)) using 1
    dsimp [f, g]
    ring
  have hg (x : ℝ) : HasDerivAt g (-Real.sin x + Real.sin B) x := by
    convert (Real.hasDerivAt_cos x).add ((hasDerivAt_id x).const_mul (Real.sin B)) using 1
    simp
  have hdf : deriv f = g := funext (fun x => (hf x).deriv)
  apply concaveOn_of_deriv2_nonpos' (convex_Icc B U)
    (fun x _ => (hf x).differentiableAt.differentiableWithinAt)
  · rw [hdf]
    exact fun x _ => (hg x).differentiableAt.differentiableWithinAt
  · intro x hx
    change deriv (deriv f) x ≤ 0
    rw [hdf, (hg x).deriv]
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ B) (hx.2.trans hU) hx.1
    linarith

/-- Sine lies below its tangent by a definite quadratic amount. -/
theorem sin_le_tangent_sub_quadratic {B U a z : ℝ} (hB : 0 ≤ B)
    (hU : U ≤ Real.pi / 2) (ha : a ∈ Icc B U) (hz : z ∈ Icc B U) :
    Real.sin z ≤ Real.sin a + Real.cos a * (z - a) -
      (Real.sin B / 2) * (z - a) ^ 2 := by
  have hd : HasDerivAt (fun x => Real.sin x + (Real.sin B / 2) * x ^ 2)
      (Real.cos a + Real.sin B * a) a := by
    convert (Real.hasDerivAt_sin a).add
      (((hasDerivAt_id a).pow 2).const_mul (Real.sin B / 2)) using 1
    dsimp
    ring
  have h := concave_le_tangent (concave_sin_add_quadratic hB hU) ha hz hd
  nlinarith only [h]

/-- The sine Jensen deficit bounds the variance from below. -/
theorem sine_deficit_ge_variance {P a B U : ℝ} {f : ℝ → ℝ} (hP : 0 < P)
    (hf : Continuous f) (hmean : (∫ t in (0 : ℝ)..P, f t) = P * a)
    (hB : 0 ≤ B) (hU : U ≤ Real.pi / 2) (ha : a ∈ Icc B U)
    (hrange : ∀ t ∈ Icc 0 P, f t ∈ Icc B U) :
    (Real.sin B / 2) * intervalVariance P f a ≤
      Real.sin a - P⁻¹ * ∫ t in (0 : ℝ)..P, Real.sin (f t) := by
  have hdev : Continuous (fun t => f t - a) := hf.sub continuous_const
  have hlin : Continuous (fun t => Real.sin a + Real.cos a * (f t - a)) := by fun_prop
  have hquad : Continuous (fun t => (Real.sin B / 2) * (f t - a) ^ 2) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hP.le
    ((Real.continuous_sin.comp hf).intervalIntegrable 0 P)
    ((hlin.sub hquad).intervalIntegrable 0 P)
    (fun t ht => sin_le_tangent_sub_quadratic hB hU ha (hrange t ht))
  simp only [Function.comp_apply] at hi
  rw [intervalIntegral.integral_sub (hlin.intervalIntegrable _ _) (hquad.intervalIntegrable _ _),
    intervalIntegral.integral_add intervalIntegrable_const
      ((continuous_const.mul hdev).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_sub_mean hf hmean] at hi
  simp only [mul_zero, add_zero, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  have he := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hP.le)
  rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hP.ne', one_mul] at he
  dsimp [intervalVariance]
  nlinarith only [he]

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The quantitative Jensen estimate for the original geometric contact angle. -/
theorem ContactSystem.variance_le_sine_deficit {K : Set Plane} {P l B : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α)
    (hB0 : 0 < B) (hB : ∀ t, B ≤ α t) :
    intervalVariance P α (Real.pi / 7) ≤
      2 * (Real.sin (Real.pi / 7) - Real.pi * l / P) / Real.sin B := by
  have hBa : B ≤ Real.pi / 7 := by
    have hm := hs.angle_le_of_lower hB 0
    have hb0 := hB 0
    linarith
  have hBpi : B < Real.pi := by linarith [Real.pi_pos]
  have hsB := Real.sin_pos_of_pos_of_lt_pi hB0 hBpi
  have he := sine_deficit_ge_variance hb.period_pos hs.contDiff_angle.continuous
    hs.integral_angle hB0.le
    (by linarith [Real.pi_gt_d2] : (6 : ℝ) / 5 ≤ Real.pi / 2)
    (show Real.pi / 7 ∈ Icc B ((6 : ℝ) / 5) from ⟨hBa, by linarith [Real.pi_lt_d4]⟩)
    (fun t _ => ⟨hB t, (hs.angle_lt_six_fifths hb hl hc t).le⟩)
  rw [hs.integral_sin_angle hl] at he
  apply (le_div_iff₀ hsB).mpr
  simp only [div_eq_mul_inv] at he ⊢
  nlinarith only [he]

end UlamFloating.Seventh
