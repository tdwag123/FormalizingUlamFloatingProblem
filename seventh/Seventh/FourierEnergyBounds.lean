import Seventh.FirstHarmonic
import Seventh.FrequencyResidues
import Seventh.SecantApproximation

/-!
# Fourier energy bounds

We sum coefficient estimates directly with Parseval. The two exceptional
indices are represented by finitely supported sequences, so no frequency
truncation is introduced in the energy argument.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

/-- Parseval for a continuous periodic real function, with normalized energy. -/
theorem hasSum_real_fourier_energy {P : ℝ} (hP : 0 < P) {f : ℝ → ℝ}
    (hf : Continuous f) (hp : Function.Periodic f P) :
    HasSum (fun n : ℤ => ‖fourierCoeffOn hP (fun t => (f t : ℂ)) n‖ ^ 2)
      (intervalVariance P f 0) := by
  have he := hasSum_sq_fourierCoeffOn hP
    ((Complex.continuous_ofReal.comp hf).continuousOn)
    (congrArg Complex.ofReal (by simpa only [zero_add] using (hp 0).symm))
  simpa only [Function.comp_apply, intervalVariance, sub_zero, one_div, Complex.norm_real, Real.norm_eq_abs,
    sq_abs] using he

/-- A coefficient bound outside `±1`, plus bounds at those two indices, controls
the complete energy sum. -/
theorem energy_le_of_except_first_bounds {v N : ℤ → ℂ} {V E D C : ℝ}
    (hv : HasSum (fun n => ‖v n‖ ^ 2) V) (hN : HasSum (fun n => ‖N n‖ ^ 2) E)
    (hD : 0 ≤ D) (hfirst : ∀ n, n = 1 ∨ n = -1 → ‖v n‖ ^ 2 ≤ C)
    (hother : ∀ n, n ≠ 1 → n ≠ -1 → ‖v n‖ ^ 2 ≤ D * ‖N n‖ ^ 2) :
    V ≤ D * E + 2 * C := by
  have hex := (hasSum_ite_eq (1 : ℤ) C).add (hasSum_ite_eq (-1 : ℤ) C)
  have hsum := (hN.mul_left D).add hex
  have he := hasSum_le (g := fun n => D * ‖N n‖ ^ 2 +
      ((if n = 1 then C else 0) + (if n = -1 then C else 0))) (fun n => ?_) hv hsum
  · linarith
  · by_cases hp : n = 1
    · subst n
      have hf := hfirst 1 (Or.inl rfl)
      norm_num
      nlinarith [mul_nonneg hD (sq_nonneg ‖N 1‖)]
    by_cases hn : n = -1
    · subst n
      have hf := hfirst (-1) (Or.inr rfl)
      norm_num
      nlinarith [mul_nonneg hD (sq_nonneg ‖N (-1)‖)]
    simpa only [if_neg hp, if_neg hn, add_zero] using hother n hp hn

/-- The nonlinear error after subtracting a linear approximation to sine. -/
noncomputable def sineRemainder (a c x : ℝ) : ℝ := Real.sin x - Real.sin a - c * (x - a)

theorem continuous_sineRemainder (a c : ℝ) : Continuous (sineRemainder a c) := by
  unfold sineRemainder
  fun_prop

/-- The relative secant error gives a normalized squared-energy estimate. -/
theorem sineRemainder_energy_le {P a c w : ℝ} {f : ℝ → ℝ}
    (hP : 0 < P) (hw : 0 ≤ w) (hf : Continuous f)
    (he : ∀ t ∈ Icc 0 P, |sineRemainder a c (f t)| ≤ w * |f t - a|) :
    intervalVariance P (fun t => sineRemainder a c (f t)) 0 ≤
      w ^ 2 * intervalVariance P f a := by
  have hi := integral_sq_le_of_abs_le hP.le hw
    ((continuous_sineRemainder a c).comp hf) (hf.sub continuous_const) he
  have hm := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hP.le)
  simpa only [intervalVariance, sub_zero, mul_left_comm] using hm

/-- Nonzero coefficients of the remainder retain the sine coefficient and subtract
the linear coefficient. No assumption on the remainder's mean is made. -/
theorem fourier_sineRemainder {P a c : ℝ} {f : ℝ → ℝ} (hP : 0 < P)
    (hf : Continuous f) {n : ℤ} (hn : n ≠ 0) :
    fourierCoeffOn hP (fun t => (sineRemainder a c (f t) : ℂ)) n =
      fourierCoeffOn hP (fun t => (Real.sin (f t) : ℂ)) n -
        (c : ℂ) * fourierCoeffOn hP (fun t => ((f t - a : ℝ) : ℂ)) n := by
  have he : (fun t => (sineRemainder a c (f t) : ℂ)) =
      fun t => ((Real.sin (f t) : ℂ) - (Real.sin a : ℂ)) - (c : ℂ) * ((f t - a : ℝ) : ℂ) := by
    ext t
    simp only [sineRemainder, Complex.ofReal_sub, Complex.ofReal_mul]
  rw [he, fourierCoeffOn_sub hP (by fun_prop) (by fun_prop),
    fourierCoeffOn_sub hP (by fun_prop) continuous_const,
    fourierCoeffOn_const_of_ne_zero hP _ hn, sub_zero, fourierCoeffOn.const_mul]

end UlamFloating.Seventh
