import Seventh.TrigBounds

/-!
# Rationally evaluable trigonometric certificates

The polynomial formulas below are proved equal to the Taylor polynomials.
Each enclosure can therefore be checked by exact rational arithmetic in Lean.
-/

namespace UlamFloating.Seventh

noncomputable def sinPolynomial14 (x : ℝ) : ℝ :=
  x - x ^ 3 / 6 + x ^ 5 / 120 - x ^ 7 / 5040 + x ^ 9 / 362880 -
    x ^ 11 / 39916800 + x ^ 13 / 6227020800

noncomputable def cosPolynomial14 (x : ℝ) : ℝ :=
  1 - x ^ 2 / 2 + x ^ 4 / 24 - x ^ 6 / 720 + x ^ 8 / 40320 -
    x ^ 10 / 3628800 + x ^ 12 / 479001600 - x ^ 14 / 87178291200

theorem sin_polynomial14_error {x : ℝ} (hx : 0 < x) :
    |Real.sin x - sinPolynomial14 x| ≤ x ^ 15 / 1307674368000 := by
  have h := sin_taylor_error 14 hx
  have ht : taylorAtZero Real.sin 14 x = sinPolynomial14 x := by
    norm_num [taylorAtZero, sinPolynomial14, Finset.sum_range_succ,
      Real.iteratedDeriv_add_one_sin, Real.iteratedDeriv_add_one_cos, Nat.factorial]
    ring
  rw [ht] at h
  norm_num [Nat.factorial] at h
  exact h

theorem cos_polynomial14_error {x : ℝ} (hx : 0 < x) :
    |Real.cos x - cosPolynomial14 x| ≤ x ^ 15 / 1307674368000 := by
  have h := cos_taylor_error 14 hx
  have ht : taylorAtZero Real.cos 14 x = cosPolynomial14 x := by
    norm_num [taylorAtZero, cosPolynomial14, Finset.sum_range_succ,
      Real.iteratedDeriv_add_one_sin, Real.iteratedDeriv_add_one_cos, Nat.factorial]
    ring
  rw [ht] at h
  norm_num [Nat.factorial] at h
  exact h

theorem sin_rational_enclosure {x L U : ℝ} (hx : 0 < x)
    (hL : L ≤ sinPolynomial14 x - x ^ 15 / 1307674368000)
    (hU : sinPolynomial14 x + x ^ 15 / 1307674368000 ≤ U) :
    L ≤ Real.sin x ∧ Real.sin x ≤ U := by
  have h := abs_le.mp (sin_polynomial14_error hx)
  constructor <;> linarith [h.1, h.2]

theorem cos_rational_enclosure {x L U : ℝ} (hx : 0 < x)
    (hL : L ≤ cosPolynomial14 x - x ^ 15 / 1307674368000)
    (hU : cosPolynomial14 x + x ^ 15 / 1307674368000 ≤ U) :
    L ≤ Real.cos x ∧ Real.cos x ≤ U := by
  have h := abs_le.mp (cos_polynomial14_error hx)
  constructor <;> linarith [h.1, h.2]

end UlamFloating.Seventh
