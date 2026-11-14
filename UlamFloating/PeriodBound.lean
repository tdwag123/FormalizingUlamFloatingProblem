import UlamFloating.WirtingerEuclidean
import UlamFloating.PeriodicAnalysis
import UlamFloating.Statements

/-!
# A sharp period obstruction from a derivative estimate

For a nonconstant periodic `C²` Euclidean curve satisfying
`‖x''‖ ≤ L * ‖x'‖`, the period is at least `2 * π / L`. The estimate is
dimension-independent and only needs the derivative bound on one period.
-/

namespace UlamFloating

open MeasureTheory Set

/-- A nonconstant periodic `C²` curve whose acceleration is bounded by `L`
times its speed has period at least `2π/L`. It suffices to impose the bound
on the closed interval representing one period. -/
theorem period_ge_of_derivative_bound {ι : Type*} [Fintype ι]
    {x : ℝ → EuclideanSpace ℝ ι} {T L : ℝ}
    (hx : ContDiff ℝ 2 x) (hp : Function.Periodic x T) (hT : 0 < T) (hL : 0 < L)
    (hnc : ¬ ∃ c, ∀ t, x t = c)
    (hb : ∀ t ∈ Icc 0 T, ‖deriv (deriv x) t‖ ≤ L * ‖deriv x t‖) :
    2 * Real.pi / L ≤ T := by
  have hx1 : ContDiff ℝ 1 x := hx.of_le (by norm_num)
  have hy : ContDiff ℝ 1 (deriv x) := hx.deriv'
  have hp1 := periodic_deriv hp (hx1.differentiable (by simp))
  have hp2 := periodic_deriv hp1 (hy.differentiable (by simp))
  have henergy := integral_deriv_norm_sq_pos hT hp hx1 hnc
  have hw := wirtinger_euclidean hT hy.continuous.continuousOn
    hy.continuous_deriv_one.continuousOn
    (fun t _ => (hy.differentiable (by simp) t).hasDerivAt)
    (by simpa only [zero_add] using (hp1 0).symm)
    (by simpa only [zero_add] using (hp2 0).symm)
    (integral_deriv_eq_zero_of_periodic hp hx1)
  have hbenergy : (∫ t in (0 : ℝ)..T, ‖deriv (deriv x) t‖ ^ 2) ≤
      L ^ 2 * (∫ t in (0 : ℝ)..T, ‖deriv x t‖ ^ 2) := by
    calc
      _ ≤ ∫ t in (0 : ℝ)..T, L ^ 2 * ‖deriv x t‖ ^ 2 := by
        apply intervalIntegral.integral_mono_on hT.le
          ((hy.continuous_deriv_one.norm.pow 2).intervalIntegrable 0 T)
          ((continuous_const.mul (hy.continuous.norm.pow 2)).intervalIntegrable 0 T)
        intro t ht
        have h := hb t ht
        nlinarith [norm_nonneg (deriv (deriv x) t), norm_nonneg (deriv x t)]
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hsquare : (2 * Real.pi) ^ 2 ≤ (T * L) ^ 2 := by
    apply (mul_le_mul_iff_left₀ henergy).mp
    calc
      _ ≤ T ^ 2 * (∫ t in (0 : ℝ)..T, ‖deriv (deriv x) t‖ ^ 2) := by
        simpa only [mul_comm] using hw
      _ ≤ T ^ 2 * (L ^ 2 * (∫ t in (0 : ℝ)..T, ‖deriv x t‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hbenergy (sq_nonneg T)
      _ = _ := by ring
  apply (div_le_iff₀ hL).mpr
  nlinarith [Real.pi_pos, mul_pos hT hL]

/-- A derivative-norm bound along a nonconstant periodic solution of an
autonomous differential equation gives the same sharp period obstruction.
Differentiability and the norm bound are only needed along one period. -/
theorem period_ge_of_vectorField_derivative_bound {ι : Type*} [Fintype ι]
    {x : ℝ → EuclideanSpace ℝ ι}
    {F : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι} {T L : ℝ}
    (hx : ContDiff ℝ 2 x) (hp : Function.Periodic x T) (hT : 0 < T) (hL : 0 < L)
    (hnc : ¬ ∃ c, ∀ t, x t = c) (hode : ∀ t, deriv x t = F (x t))
    (hF : ∀ t ∈ Icc 0 T, DifferentiableAt ℝ F (x t))
    (hbound : ∀ t ∈ Icc 0 T, ‖fderiv ℝ F (x t)‖ ≤ L) :
    2 * Real.pi / L ≤ T := by
  apply period_ge_of_derivative_bound hx hp hT hL hnc
  intro t ht
  have hacc : deriv (deriv x) t = fderiv ℝ F (x t) (deriv x t) := by
    conv_lhs => rw [show deriv x = fun s => F (x s) from funext hode]
    exact ((hF t ht).hasFDerivAt.comp_hasDerivAt t
      (hx.differentiable (by norm_num) t).hasDerivAt).deriv
  rw [hacc]
  exact ((fderiv ℝ F (x t)).le_opNorm (deriv x t)).trans
    (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _))

/-- Discharges the blueprint's dimension-independent period obstruction. -/
theorem period_bound : periodBoundStatement := by
  intro d x T L hx hp hT hL hnc hb
  exact period_ge_of_derivative_bound hx hp hT hL hnc (fun t _ => hb t)

end UlamFloating
