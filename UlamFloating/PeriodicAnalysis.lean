import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Algebra.Field.Periodic

/-!
# Derivatives and energy of periodic curves

Periodicity passes to the derivative. The derivative has zero integral over
a full period, and its squared norm has positive integral for a nonconstant
continuously differentiable curve.
-/

namespace UlamFloating

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The derivative of a differentiable periodic function has the same period. -/
theorem periodic_deriv {f : ℝ → E} {T : ℝ} (hp : Function.Periodic f T)
    (hf : Differentiable ℝ f) : Function.Periodic (deriv f) T := by
  intro t
  have h := (hf (t + T)).hasDerivAt.scomp t ((hasDerivAt_id t).add_const T)
  simp only [one_smul] at h
  have heq : (fun s => f (s + T)) = f := funext hp
  change HasDerivAt (fun s => f (s + T)) (deriv f (t + T)) t at h
  rw [heq] at h
  exact h.unique (hf t).hasDerivAt

/-- A periodic continuously differentiable function has mean-zero derivative. -/
theorem integral_deriv_eq_zero_of_periodic [CompleteSpace E] {f : ℝ → E} {T : ℝ}
    (hp : Function.Periodic f T) (hf : ContDiff ℝ 1 f) :
    (∫ t in (0 : ℝ)..T, deriv f t) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => (hf.differentiable (by simp) t).hasDerivAt)
    (hf.continuous_deriv_one.intervalIntegrable 0 T)]
  simpa only [zero_add, sub_self] using congrArg (fun z => z - f 0) (hp 0)

omit [NormedSpace ℝ E] in
/-- A nonzero continuous periodic function has strictly positive squared
norm integral over every full positive period starting at zero. -/
theorem integral_norm_sq_pos_of_periodic {f : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hp : Function.Periodic f T) (hf : Continuous f) (hne : ∃ t, f t ≠ 0) :
    0 < ∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2 := by
  obtain ⟨t, ht⟩ := hne
  obtain ⟨s, hs, hts⟩ := hp.exists_mem_Ico₀ hT t
  apply intervalIntegral.integral_pos hT (hf.norm.pow 2).continuousOn
    (fun t _ => sq_nonneg _) ⟨s, ⟨hs.1, hs.2.le⟩, ?_⟩
  exact sq_pos_of_pos (norm_pos_iff.mpr (hts ▸ ht))

/-- The velocity of a nonconstant continuously differentiable periodic curve
has positive energy over one positive period. -/
theorem integral_deriv_norm_sq_pos {f : ℝ → E} {T : ℝ} (hT : 0 < T)
    (hp : Function.Periodic f T) (hf : ContDiff ℝ 1 f)
    (hnc : ¬ ∃ c, ∀ t, f t = c) :
    0 < ∫ t in (0 : ℝ)..T, ‖deriv f t‖ ^ 2 := by
  have hd := hf.differentiable (by simp)
  apply integral_norm_sq_pos_of_periodic hT (periodic_deriv hp hd) hf.continuous_deriv_one
  by_contra h
  push_neg at h
  exact hnc ⟨f 0, fun t => is_const_of_deriv_eq_zero hd h t 0⟩

end UlamFloating
