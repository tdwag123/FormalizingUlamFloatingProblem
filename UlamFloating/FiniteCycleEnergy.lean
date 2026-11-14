import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Energy estimates on finite cycles

The difference estimate works for any finite permutation. For five indices,
the two complementary pair sums partition all off-diagonal products. Their
energy identity gives a useful bound on the zero-sum subspace.
-/

namespace UlamFloating

open scoped BigOperators

/-- Taking differences along a finite permutation increases squared energy
by at most a factor of four. -/
theorem sum_sq_sub_perm_le {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (u : ι → ℝ) :
    ∑ i, (u i - u (next i)) ^ 2 ≤ 4 * ∑ i, (u i) ^ 2 := by
  calc
    _ ≤ ∑ i, (2 * (u i) ^ 2 + 2 * (u (next i)) ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      nlinarith [sq_nonneg (u i + u (next i))]
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        Equiv.sum_comp next (fun i => (u i) ^ 2)]
      ring

/-- On five cyclic indices, the two complementary pair-sum energies add
to three times the vertex energy plus the square of the total sum. -/
theorem pentagon_pair_energy_identity (u : Fin 5 → ℝ) :
    (∑ i, (u (i + 2) + u (i + 4)) ^ 2) +
        (∑ i, (u i + u (i + 1)) ^ 2) =
      3 * ∑ i, (u i) ^ 2 + (∑ i, u i) ^ 2 := by
  have hsum (f : Fin 5 → ℝ) : ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
    simp only [Fin.sum_univ_succ]
    change f 0 + (f 1 + (f 2 + (f 3 + (f 4 + 0)))) = _
    ring
  simp only [hsum]
  change (u 2 + u 4) ^ 2 + (u 3 + u 0) ^ 2 + (u 4 + u 1) ^ 2 +
      (u 0 + u 2) ^ 2 + (u 1 + u 3) ^ 2 +
      ((u 0 + u 1) ^ 2 + (u 1 + u 2) ^ 2 + (u 2 + u 3) ^ 2 +
        (u 3 + u 4) ^ 2 + (u 4 + u 0) ^ 2) =
    3 * ((u 0) ^ 2 + (u 1) ^ 2 + (u 2) ^ 2 + (u 3) ^ 2 + (u 4) ^ 2) +
      (u 0 + u 1 + u 2 + u 3 + u 4) ^ 2
  ring

/-- The two-step pair-sum operator has squared norm at most three on the
zero-sum subspace of five real coordinates. -/
theorem pentagon_pair_energy_le (u : Fin 5 → ℝ) (hu : ∑ i, u i = 0) :
    ∑ i, (u (i + 2) + u (i + 4)) ^ 2 ≤ 3 * ∑ i, (u i) ^ 2 := by
  have hid := pentagon_pair_energy_identity u
  rw [hu, zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at hid
  have hnonneg : 0 ≤ ∑ i : Fin 5, (u i + u (i + 1)) ^ 2 :=
    Finset.sum_nonneg (fun i _ => sq_nonneg _)
  linarith

/-- A diagonal contraction between pair sums and cyclic differences gives
a squared energy factor of at most twelve on the zero-sum subspace. -/
theorem pentagon_weighted_difference_energy_le (u c : Fin 5 → ℝ)
    (hu : ∑ i, u i = 0) (hc : ∀ i, (c i) ^ 2 ≤ 1) :
    let w : Fin 5 → ℝ := fun i => c i * (u (i + 2) + u (i + 4))
    ∑ i, (w i - w ((finRotate 5).symm i)) ^ 2 ≤ 12 * ∑ i, (u i) ^ 2 := by
  intro w
  have hweight : ∑ i, (w i) ^ 2 ≤ ∑ i, (u (i + 2) + u (i + 4)) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    dsimp [w]
    rw [mul_pow]
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right (hc i) (sq_nonneg (u (i + 2) + u (i + 4)))
  calc
    _ ≤ 4 * ∑ i, (w i) ^ 2 := sum_sq_sub_perm_le (finRotate 5).symm w
    _ ≤ 4 * ∑ i, (u (i + 2) + u (i + 4)) ^ 2 := by gcongr
    _ ≤ 4 * (3 * ∑ i, (u i) ^ 2) := by
      exact mul_le_mul_of_nonneg_left (pentagon_pair_energy_le u hu) (by norm_num)
    _ = _ := by ring

end UlamFloating
