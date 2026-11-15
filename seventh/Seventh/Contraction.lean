import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The terminal contraction step

The estimates that feed these lemmas must be proved for the actual boundary.
They are not numerical assumptions silently added to the rigidity theorem.
-/

namespace UlamFloating.Seventh

/-- An energy split with strictly contracting component bounds has zero energy. -/
theorem energy_eq_zero_of_contraction {V A B q k : ℝ}
    (hV : 0 ≤ V) (hsplit : V = A + B) (hA : A ≤ q * V) (hB : B ≤ k * V)
    (hstrict : q + k < 1) : V = 0 := by
  have hnonpos : (1 - (q + k)) * V ≤ 0 := by nlinarith
  have hpos : 0 < 1 - (q + k) := by linarith
  have hvle : V ≤ 0 := (mul_le_mul_iff_right₀ hpos).mp (by simpa using hnonpos)
  exact le_antisymm hvle hV

/-- Exact arithmetic in the fixed-angle route: `(3/4)² + (5/12)² = 53/72 < 1`. -/
theorem fixed_interval_contraction :
    (3 / 4 : ℝ) ^ 2 + (5 / 12 : ℝ) ^ 2 = 53 / 72 ∧ (53 / 72 : ℝ) < 1 := by
  norm_num

/-- The two squared-norm bounds of the fixed-angle route force zero variance. -/
theorem energy_eq_zero_of_fixed_bounds {V A B : ℝ} (hV : 0 ≤ V)
    (hsplit : V = A + B) (hA : A ≤ (3 / 4 : ℝ) ^ 2 * V)
    (hB : B ≤ (5 / 12 : ℝ) ^ 2 * V) : V = 0 :=
  energy_eq_zero_of_contraction hV hsplit hA hB (by norm_num)

/-- The variable-interval certificate's `19/20` margin is also a contraction. -/
theorem energy_eq_zero_of_certificate {V A B q k : ℝ} (hV : 0 ≤ V)
    (hsplit : V = A + B) (hA : A ≤ q * V) (hB : B ≤ k * V)
    (hcertificate : q + k < 19 / 20) : V = 0 :=
  energy_eq_zero_of_contraction hV hsplit hA hB (by linarith)

end UlamFloating.Seventh
