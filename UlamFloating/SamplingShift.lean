import UlamFloating.FiniteSampling

/-!
# Arbitrary finite sampling shifts

A cyclic index advance of any natural number of steps equals the
corresponding time translation, including all wraps around the cycle.
-/

namespace UlamFloating

open Fin.NatCast

/-- Advancing a cyclic sample by `k` indices translates time by `k` sampling
intervals. The target type is arbitrary and only periodicity is needed. -/
theorem boundarySamples_add_nat {E : Type*} {γ : ℝ → E} {P : ℝ}
    (hp : Function.Periodic γ P) {n : ℕ} (i : Fin (n + 1)) (k : ℕ) (t : ℝ) :
    boundarySamples γ P (n + 1) (i + (k : Fin (n + 1))) t =
      boundarySamples γ P (n + 1) i (t + (k : ℝ) * (P / (n + 1))) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    rw [Nat.cast_succ, ← add_assoc, ← finRotate_succ_apply,
      boundarySamples_rotate hp, ih]
    congr 1
    push_cast
    ring

end UlamFloating
