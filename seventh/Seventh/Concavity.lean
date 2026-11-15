import Seventh.Averages
import Seventh.ArcProjection
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# Supporting-line and lower contact-angle bounds

The dimensionless parameter is `λ = π l / P`, so no normalization of the
boundary or chord length is required. These lemmas precede the numerical
lower bound `21/50 < λ` in the supplied argument.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

/-- A differentiable concave real function lies below each tangent line. -/
theorem concave_le_tangent {f : ℝ → ℝ} {S : Set ℝ} {a z d : ℝ}
    (hf : ConcaveOn ℝ S f) (ha : a ∈ S) (hz : z ∈ S) (hd : HasDerivAt f d a) :
    f z ≤ f a + d * (z - a) := by
  rcases lt_trichotomy a z with hlt | rfl | hgt
  · have hq := hf.slope_le_of_hasDerivAt ha hz hlt hd
    rw [slope_def_field] at hq
    have he := (div_le_iff₀ (sub_pos.mpr hlt)).mp hq
    linarith
  · simp
  · have hq := hf.le_slope_of_hasDerivAt hz ha hgt hd
    rw [slope_def_field] at hq
    have he := (le_div_iff₀ (sub_pos.mpr hgt)).mp hq
    nlinarith

/-- The sine supporting-line inequality on its full concavity interval. -/
theorem sin_le_tangent {a z : ℝ} (ha : a ∈ Icc 0 Real.pi) (hz : z ∈ Icc 0 Real.pi) :
    Real.sin z ≤ Real.sin a + Real.cos a * (z - a) :=
  concave_le_tangent strictConcaveOn_sin_Icc.concaveOn ha hz (Real.hasDerivAt_sin a)

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Averaging the supporting-line inequality gives the upper bound on λ. -/
theorem ContactSystem.frequency_le_sin {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (hl : 0 < l) :
    Real.pi * l / P ≤ Real.sin (Real.pi / 7) := by
  let a := Real.pi / 7
  have ha : a ∈ Icc 0 Real.pi := ⟨by dsimp [a]; positivity, by dsimp [a]; linarith [Real.pi_pos]⟩
  have hα := hs.contDiff_angle.continuous
  have hlinear : Continuous (fun t => Real.sin a + Real.cos a * (α t - a)) := by fun_prop
  have hterm : Continuous (fun t => Real.cos a * (α t - a)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hP.le
    ((Real.continuous_sin.comp hs.contDiff_angle.continuous).intervalIntegrable 0 P)
    (hlinear.intervalIntegrable 0 P)
    (fun t _ => sin_le_tangent ha ⟨(hs.angle_range t).1.le, (hs.angle_range t).2.le⟩)
  simp only [Function.comp_apply] at hi
  rw [hs.integral_sin_angle hl, intervalIntegral.integral_add
      intervalIntegrable_const (hterm.intervalIntegrable 0 P),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      (hs.contDiff_angle.continuous.intervalIntegrable _ _) intervalIntegrable_const,
    hs.integral_angle] at hi
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, a, sub_self,
    mul_zero, add_zero] at hi
  exact (div_le_iff₀ hP).mpr (by nlinarith)

/-- Arc projection puts every contact angle above `arccos (l/h)`.
The arccosine statement is valid even before establishing `l/h < 1`. -/
theorem ContactSystem.arccos_lower_bound {K : Set Plane} {P h l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hh : 0 < h) (hl : 0 < l)
    (hc : HasConstantChord γ h l) {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) :
    Real.arccos (l / h) ≤ α t := by
  have he := hs.arc_projection hb hh hl hc t
  have hcos : Real.cos (α t) ≤ l / h := (le_div_iff₀ hh).mpr (by nlinarith)
  have h := Real.arccos_le_arccos hcos
  rwa [Real.arccos_cos (hs.angle_range t).1.le (hs.angle_range t).2.le] at h

end UlamFloating.Seventh
