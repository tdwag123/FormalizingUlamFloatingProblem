import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Kernel-checked trigonometric enclosures

Numerical certificates use the real Taylor theorem and exact rational arithmetic.
No result of an external numerical program is accepted as an axiom. The generic
remainder lemma is applicable to any smooth real function with bounded derivatives.
-/

namespace UlamFloating.Seventh

open scoped Nat
open Set

/-- Taylor polynomial at zero, using ordinary iterated derivatives. -/
noncomputable def taylorAtZero (f : ℝ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), ((k ! : ℝ)⁻¹ * x ^ k) * iteratedDeriv k f 0

/-- A Lagrange remainder bound expressed entirely with ordinary derivatives. -/
theorem taylorAtZero_error {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f) (n : ℕ) {x C : ℝ}
    (hx : 0 < x) (hbound : ∀ y ∈ Ioo 0 x, |iteratedDeriv (n + 1) f y| ≤ C) :
    |f x - taylorAtZero f n x| ≤ C * x ^ (n + 1) / (n + 1)! := by
  have hdiff : ContDiff ℝ (n + 1) f := hf.of_le (by simp)
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv hx hdiff.contDiffOn
  have ht : taylorWithinEval f n (Icc 0 x) 0 x = taylorAtZero f n x := by
    rw [taylor_within_apply]
    unfold taylorAtZero
    apply Finset.sum_congr rfl
    intro k _
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Icc hx)
      (hf.of_le (by simp)).contDiffAt ⟨le_rfl, hx.le⟩]
    simp only [sub_zero, smul_eq_mul]
  rw [ht, sub_zero] at he
  rw [he, abs_div, abs_mul, abs_pow, abs_of_pos hx, Nat.abs_cast]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (hbound y hy)
    (pow_nonneg hx.le _)) (by positivity)

/-- Sine enclosure of any specified finite Taylor order. -/
theorem sin_taylor_error (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |Real.sin x - taylorAtZero Real.sin n x| ≤ x ^ (n + 1) / (n + 1)! := by
  simpa using taylorAtZero_error Real.contDiff_sin n hx
    (fun y _ => Real.abs_iteratedDeriv_sin_le_one (n + 1) y)

/-- Cosine enclosure of any specified finite Taylor order. -/
theorem cos_taylor_error (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |Real.cos x - taylorAtZero Real.cos n x| ≤ x ^ (n + 1) / (n + 1)! := by
  simpa using taylorAtZero_error Real.contDiff_cos n hx
    (fun y _ => Real.abs_iteratedDeriv_cos_le_one (n + 1) y)

end UlamFloating.Seventh
