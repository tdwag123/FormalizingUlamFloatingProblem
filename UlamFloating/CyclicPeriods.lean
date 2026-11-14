import UlamFloating.CyclicMotion
import UlamFloating.PeriodSubgroup

/-!
# Least periods of cyclic coordinate motions

A period gap gives a least positive period. The traversal period is a
positive natural-number multiple of it, and the cyclic coordinate law
excludes multiplicities divisible by the entire cycle length.
-/

namespace UlamFloating

open scoped BigOperators

/-- A nonconstant cyclic motion with fixed coordinate sum and a positive
period bound has a least positive period. Its traversal multiplicity is
positive and is not divisible by the coordinate cycle length. -/
theorem exists_least_period_cyclic_motion {n : ℕ}
    {x : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {P A ε : ℝ}
    (hP : 0 < P) (hp : Function.Periodic x P) (hε : 0 < ε)
    (hbound : ∀ T, 0 < T → Function.Periodic x T → ε ≤ T)
    (hshift : ∀ t i, x t (finRotate (n + 1) i) = x (t + P / (n + 1)) i)
    (hsum : ∀ t, ∑ i, x t i = A) (hnc : ¬ ∃ c, ∀ t, x t = c) :
    ∃ (T : ℝ) (m : ℕ), IsLeast {S | Function.Periodic x S ∧ 0 < S} T ∧
      0 < m ∧ P = (m : ℝ) * T ∧ ¬ (n + 1) ∣ m ∧ ε ≤ T := by
  obtain ⟨T, hT⟩ := exists_least_positive_period_of_lower_bound hP hp hε hbound
  obtain ⟨m, hmpos, hm⟩ := (periodic_pos_iff_nat_mul_of_isLeast hT hP).mp hp
  exact ⟨T, m, hT, hmpos, hm,
    cycle_length_not_dvd_period_multiple hshift hsum hnc hT.1.1 hm,
    hbound T hT.1.2 hT.1.1⟩

end UlamFloating
