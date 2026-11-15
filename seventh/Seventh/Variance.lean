import Seventh.Concavity
import Mathlib.Algebra.Field.Periodic

/-!
# Variance on one traversal interval

These estimates are independent of the heptagon geometry. Zero variance for
a continuous periodic function gives pointwise constancy, not merely an
almost-everywhere statement.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

/-- Normalized mean squared deviation on a traversal of length `P`. -/
noncomputable def intervalVariance (P : ℝ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  P⁻¹ * ∫ t in (0 : ℝ)..P, (f t - a) ^ 2

/-- Mean squared deviation is nonnegative for a positive traversal length. -/
theorem intervalVariance_nonneg {P a : ℝ} {f : ℝ → ℝ} (hP : 0 < P) :
    0 ≤ intervalVariance P f a :=
  mul_nonneg (inv_nonneg.mpr hP.le)
    (intervalIntegral.integral_nonneg_of_forall hP.le (fun t => sq_nonneg (f t - a)))

/-- Subtracting the prescribed mean gives zero integral. -/
theorem integral_sub_mean {P a : ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    (hmean : (∫ t in (0 : ℝ)..P, f t) = P * a) :
    (∫ t in (0 : ℝ)..P, f t - a) = 0 := by
  rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const, hmean]
  simp

/-- A continuous periodic function of zero variance equals its prescribed mean everywhere. -/
theorem eq_mean_of_variance_zero {P a : ℝ} {f : ℝ → ℝ} (hP : 0 < P)
    (hf : Continuous f) (hp : Function.Periodic f P) (hV : intervalVariance P f a = 0) :
    ∀ t, f t = a := by
  have hi : (∫ t in (0 : ℝ)..P, (f t - a) ^ 2) = 0 :=
    (mul_eq_zero.mp hV).resolve_left (inv_ne_zero hP.ne')
  have hzero (s : ℝ) (hs : s ∈ Icc 0 P) : f s = a := by
    by_contra hne
    have hpos := intervalIntegral.integral_pos hP
      (((hf.sub continuous_const).pow 2).continuousOn)
      (fun t _ => sq_nonneg (f t - a)) ⟨s, hs, sq_pos_of_ne_zero (sub_ne_zero.mpr hne)⟩
    rw [hi] at hpos
    exact (lt_irrefl 0) hpos
  intro t
  obtain ⟨s, hs, he⟩ := hp.exists_mem_Ico₀ hP t
  have hz := hzero s ⟨hs.1, hs.2.le⟩
  simpa only [he] using hz

/-- A variable in `[B,U]` with prescribed mean `a` has variance at most
`(a-B)(U-a)`. This is the bounded-range estimate used in both proof routes. -/
theorem intervalVariance_le_range {P a B U : ℝ} {f : ℝ → ℝ} (hP : 0 < P)
    (hf : Continuous f) (hmean : (∫ t in (0 : ℝ)..P, f t) = P * a)
    (hrange : ∀ t ∈ Icc 0 P, B ≤ f t ∧ f t ≤ U) :
    intervalVariance P f a ≤ (a - B) * (U - a) := by
  have hdev : Continuous (fun t => f t - a) := hf.sub continuous_const
  have hlinear : Continuous (fun t =>
      (B + U - 2 * a) * (f t - a) + (a - B) * (U - a)) := by fun_prop
  have hi := intervalIntegral.integral_mono_on (μ := volume) hP.le
    ((hdev.pow 2).intervalIntegrable 0 P) (hlinear.intervalIntegrable 0 P)
    (fun t ht => show (f t - a) ^ 2 ≤
      (B + U - 2 * a) * (f t - a) + (a - B) * (U - a) by
        have hprod := mul_nonneg (sub_nonneg.mpr (hrange t ht).1)
          (sub_nonneg.mpr (hrange t ht).2)
        nlinarith)
  rw [intervalIntegral.integral_add
    ((continuous_const.mul hdev).intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, integral_sub_mean hf hmean] at hi
  simp only [mul_zero, zero_add, intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  have hmul := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hP.le)
  simpa only [intervalVariance, ← mul_assoc, inv_mul_cancel₀ hP.ne', one_mul] using hmul

end UlamFloating.Seventh
