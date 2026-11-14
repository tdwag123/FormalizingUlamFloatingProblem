import UlamFloating.SamplingShift

/-!
# Cyclic time shifts and period divisibility

A motion with a cyclic coordinate shift cannot have the shift itself as
a period unless all coordinates agree. With a fixed coordinate sum this
forces constancy. The consequence for period multiples is purely algebraic.
-/

namespace UlamFloating

open scoped BigOperators

/-- Invariance under the one-step rotation of a nonempty finite cycle
makes every value equal to the value at index zero. The target is arbitrary. -/
theorem eq_initial_of_finRotate_invariant {Y : Type*} {n : ℕ} (f : Fin (n + 1) → Y)
    (hf : ∀ i, f (finRotate (n + 1) i) = f i) (i : Fin (n + 1)) : f i = f 0 := by
  induction i using Fin.induction with
  | zero => rfl
  | succ i hi =>
    have hrot : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
    rw [← hrot]
    exact (hf i.castSucc).trans hi

/-- A cyclic coordinate motion of fixed sum is constant if the cyclic
time shift is itself a period. No continuity or differential equation is needed. -/
theorem constant_of_periodic_cyclic_shift {n : ℕ}
    {x : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {h A : ℝ}
    (hshift : ∀ t i, x t (finRotate (n + 1) i) = x (t + h) i)
    (hsum : ∀ t, ∑ i, x t i = A) (hp : Function.Periodic x h) :
    ∃ c, ∀ t, x t = c := by
  have he (t : ℝ) (i : Fin (n + 1)) : x t i = x t 0 :=
    eq_initial_of_finRotate_invariant (fun j => x t j)
      (fun j => (hshift t j).trans (congrArg (fun v => v j) (hp t))) i
  have hvalue (t : ℝ) : x t 0 = A / ((n : ℝ) + 1) := by
    have hs := hsum t
    simp_rw [he t] at hs
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at hs
    exact (eq_div_iff (by positivity)).mpr (by simpa only [mul_comm] using hs)
  refine ⟨WithLp.toLp 2 (fun _ => A / ((n : ℝ) + 1)), ?_⟩
  intro t
  ext i
  exact (he t i).trans (hvalue t)

/-- In a nonconstant cyclic coordinate motion of fixed sum, the number
of coordinates cannot divide a period multiplicity `P = m T`. Here `P/n`
is the time shift implementing one coordinate rotation. -/
theorem cycle_length_not_dvd_period_multiple {n m : ℕ}
    {x : ℝ → EuclideanSpace ℝ (Fin (n + 1))} {P T A : ℝ}
    (hshift : ∀ t i, x t (finRotate (n + 1) i) = x (t + P / (n + 1)) i)
    (hsum : ∀ t, ∑ i, x t i = A) (hnc : ¬ ∃ c, ∀ t, x t = c)
    (hp : Function.Periodic x T) (hm : P = (m : ℝ) * T) : ¬ (n + 1) ∣ m := by
  rintro ⟨q, hq⟩
  have hstep : P / ((n : ℝ) + 1) = (q : ℝ) * T := by
    rw [hm, hq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  apply hnc
  apply constant_of_periodic_cyclic_shift hshift hsum
  rw [hstep]
  exact hp.nat_mul q

end UlamFloating
