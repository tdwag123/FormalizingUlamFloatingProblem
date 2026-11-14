import UlamFloating.FourierEnergy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Periodic Wirtinger inequality

The zero Fourier coefficient vanishes for a mean-zero function. At every
other integer frequency, differentiation increases squared Fourier energy
by at least the square of the fundamental frequency. Parseval then gives
the sharp periodic Wirtinger inequality.
-/

namespace UlamFloating

open MeasureTheory Set
open scoped Real

/-- A nonzero Fourier mode satisfies the sharp fundamental-frequency energy
bound, using equality of the function's endpoint values. -/
theorem fourierCoeffOn_energy_le {T : ℝ} (hT : 0 < T) {f g : ℝ → ℂ}
    (hder : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable g volume 0 T) (hend : f 0 = f T)
    {n : ℤ} (hn : n ≠ 0) :
    (2 * Real.pi) ^ 2 * ‖fourierCoeffOn hT f n‖ ^ 2 ≤
      T ^ 2 * ‖fourierCoeffOn hT g n‖ ^ 2 := by
  have hcoeff := fourierCoeffOn_of_hasDerivAt hT hn
    (fun t ht => hder t (by simpa only [uIcc_of_le hT.le] using ht)) hg
  rw [← hend, sub_self, mul_zero, zero_sub, Complex.ofReal_zero, sub_zero] at hcoeff
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have heq : (2 * (Real.pi : ℂ) * Complex.I * n) * fourierCoeffOn hT f n =
      (T : ℂ) * fourierCoeffOn hT g n := by
    rw [hcoeff]
    field_simp
  have hnorm := congrArg (fun z : ℂ => ‖z‖ ^ 2) heq
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos hT, Complex.norm_I, mul_one] at hnorm
  have hnreal : 1 ≤ ‖(n : ℂ)‖ ^ 2 := by
    have hi : (1 : ℤ) ≤ n ^ 2 := by nlinarith [sq_pos_of_ne_zero hn]
    have hr : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hi
    simpa only [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, sq_abs] using hr
  nlinarith [sq_nonneg (2 * Real.pi * ‖fourierCoeffOn hT f n‖)]

/-- Sharp interval Wirtinger inequality with periodic endpoint conditions
for a continuously differentiable complex-valued function of mean zero. -/
theorem wirtinger_complex {T : ℝ} (hT : 0 < T) {f g : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hder : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t)
    (hfend : f 0 = f T) (hgend : g 0 = g T)
    (hmean : (∫ t in (0 : ℝ)..T, f t) = 0) :
    (2 * Real.pi) ^ 2 * (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) ≤
      T ^ 2 * (∫ t in (0 : ℝ)..T, ‖g t‖ ^ 2) := by
  have hzero : fourierCoeffOn hT f 0 = 0 := by
    rw [fourierCoeffOn_eq_integral]
    simp only [neg_zero, fourier_zero, one_smul, hmean, smul_zero]
  have hcoeff (n : ℤ) : (2 * Real.pi) ^ 2 * ‖fourierCoeffOn hT f n‖ ^ 2 ≤
      T ^ 2 * ‖fourierCoeffOn hT g n‖ ^ 2 := by
    by_cases hn : n = 0
    · subst n
      rw [hzero, norm_zero, zero_pow (by decide), mul_zero]
      positivity
    · exact fourierCoeffOn_energy_le hT hder (hg.intervalIntegrable_of_Icc hT.le) hfend hn
  have hsum := hasSum_le hcoeff ((hasSum_sq_fourierCoeffOn hT hf hfend).mul_left ((2 * Real.pi) ^ 2))
    ((hasSum_sq_fourierCoeffOn hT hg hgend).mul_left (T ^ 2))
  have h := mul_le_mul_of_nonneg_left hsum hT.le
  convert h using 1 <;> field_simp

end UlamFloating
