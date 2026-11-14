import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# Translation increments of primitives of periodic functions

A differentiable curve with periodic derivative changes by a fixed vector
over each period. A known increment over a positive integer multiple of
that period determines the vector exactly. No integration is required.
-/

namespace UlamFloating

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A primitive of a periodic derivative has a constant translation increment. -/
theorem sub_eq_of_periodic_deriv {f : ℝ → E} {T : ℝ}
    (hf : Differentiable ℝ f) (hp : Function.Periodic (deriv f) T) (s t : ℝ) :
    f (s + T) - f s = f (t + T) - f t := by
  have hd (r : ℝ) : HasDerivAt (fun q => f (q + T) - f q) 0 r := by
    have hshift : HasDerivAt (fun q => f (q + T)) (deriv f (r + T)) r := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        (hf (r + T)).hasDerivAt.scomp r ((hasDerivAt_id r).add_const T)
    simpa only [hp r, sub_self] using hshift.sub (hf r).hasDerivAt
  exact is_const_of_deriv_eq_zero (fun r => (hd r).differentiableAt)
    (fun r => (hd r).deriv) s t

/-- Iterate a fixed translation increment along any natural multiple. -/
theorem add_nat_mul_of_add_const {f : ℝ → E} {T : ℝ} {v : E}
    (h : ∀ t, f (t + T) = f t + v) (n : ℕ) (t : ℝ) :
    f (t + (n : ℝ) * T) = f t + (n : ℝ) • v := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, ← add_assoc, h, ih,
      add_smul, one_smul, add_assoc]

/-- An increment over `m` periods determines the increment over one period
for a differentiable curve with periodic derivative. -/
theorem sub_eq_inv_smul_of_periodic_deriv {f : ℝ → E} {T : ℝ} {A : E} {m : ℕ}
    (hf : Differentiable ℝ f) (hp : Function.Periodic (deriv f) T)
    (hm : m ≠ 0) (hA : f ((m : ℝ) * T) - f 0 = A) (t : ℝ) :
    f (t + T) - f t = (m : ℝ)⁻¹ • A := by
  have hi (s : ℝ) : f (s + T) = f s + (f T - f 0) := by
    have he := sub_eq_of_periodic_deriv hf hp s 0
    simpa only [zero_add, add_zero, add_comm] using (sub_eq_iff_eq_add.mp he)
  have he := add_nat_mul_of_add_const hi m 0
  simp only [zero_add] at he
  have hmul : (m : ℝ) • (f T - f 0) = A := by rw [← hA, he]; abel
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
  have hv : f T - f 0 = (m : ℝ)⁻¹ • A := by
    rw [← hmul, smul_smul, inv_mul_cancel₀ hmR, one_smul]
  simpa only [zero_add, hv] using sub_eq_of_periodic_deriv hf hp t 0

/-- Scalar version: the increment over one period is the total increment
divided by the positive integer multiplicity. -/
theorem sub_eq_div_of_periodic_deriv {f : ℝ → ℝ} {T A : ℝ} {m : ℕ}
    (hf : Differentiable ℝ f) (hp : Function.Periodic (deriv f) T)
    (hm : m ≠ 0) (hA : f ((m : ℝ) * T) - f 0 = A) (t : ℝ) :
    f (t + T) - f t = A / m := by
  simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using
    sub_eq_inv_smul_of_periodic_deriv hf hp hm hA t

end UlamFloating
