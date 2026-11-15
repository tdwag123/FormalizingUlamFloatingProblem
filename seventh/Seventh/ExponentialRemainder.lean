import Seventh.PhaseAlgebra
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The global quadratic remainder of the unit complex exponential

Unlike a local Taylor estimate for arbitrary complex inputs, this bound has
constant `1/2` and applies to every real angle. This is the closure estimate's
required remainder bound.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

theorem hasDerivAt_exp_real_mul_I (x : ℝ) :
    HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I))
      (Complex.exp ((x : ℂ) * Complex.I) * Complex.I) x := by
  convert (Complex.hasDerivAt_exp ((x : ℂ) * Complex.I)).comp x
    (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I) using 1
  simp

theorem norm_exp_real_mul_I_sub_one_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1‖ ≤ |x| := by
  have hd := fun t => hasDerivAt_exp_real_mul_I t
  have he := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (hd t).differentiableAt)
    (fun t _ => show ‖deriv (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) t‖ ≤ (1 : ℝ) by
      rw [(hd t).deriv, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_I, one_mul])
    (mem_univ (0 : ℝ)) (mem_univ x)
  simpa only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_zero, Real.norm_eq_abs,
    one_mul] using he

/-- Global sharp quadratic remainder along the imaginary axis. -/
theorem norm_exp_real_mul_I_remainder_le (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - 1 - (x : ℂ) * Complex.I‖ ≤ x ^ 2 / 2 := by
  let g : ℝ → ℂ := fun t => (Complex.exp ((t : ℂ) * Complex.I) - 1) * Complex.I
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hd (t : ℝ) : HasDerivAt
      (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I) - 1 - (t : ℂ) * Complex.I) (g t) t := by
    convert ((hasDerivAt_exp_real_mul_I t).sub_const 1).sub
      (Complex.ofRealCLM.hasDerivAt.mul_const Complex.I) using 1
    dsimp [g]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t ∈ uIcc 0 x) => hd t) (hg.intervalIntegrable 0 x)
  simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self, sub_zero] at hi
  rw [← hi]
  apply intervalIntegral.norm_integral_le_integral_norm_uIoc.trans
  have he := MeasureTheory.integral_mono_ae (μ := volume.restrict (uIoc (0 : ℝ) x))
    ((hg.norm.intervalIntegrable 0 x).def')
    ((continuous_abs.intervalIntegrable 0 x).def')
    (Filter.Eventually.of_forall (fun t => show ‖g t‖ ≤ |t| by
      dsimp [g]
      rw [norm_mul, Complex.norm_I, mul_one]
      exact norm_exp_real_mul_I_sub_one_le t))
  have habs : (∫ t in uIoc (0 : ℝ) x, |t|) = x ^ 2 / 2 := by
    have hh := integral_pow_abs_sub_uIoc (a := (0 : ℝ)) (b := x) (n := 1)
    norm_num [sq_abs] at hh
    exact hh
  exact he.trans_eq habs

end UlamFloating.Seventh
