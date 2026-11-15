import Seventh.FourierBasic
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Exact phase identities for the seventh shift

These identities hold at every integer frequency. Divisibility by seven,
rather than a cutoff on the magnitude of the frequency, detects resonance.
-/

namespace UlamFloating.Seventh

theorem exp_real_mul_I (b : ℝ) :
    Complex.exp ((b : ℂ) * Complex.I) = (Real.cos b : ℂ) + (Real.sin b : ℂ) * Complex.I := by
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem exp_double_angle_sub_one (b : ℝ) :
    Complex.exp ((2 * b : ℝ) * Complex.I) - 1 =
      (2 * Complex.I * (Real.sin b : ℂ)) * Complex.exp ((b : ℂ) * Complex.I) := by
  rw [exp_real_mul_I, exp_real_mul_I]
  apply Complex.ext
  all_goals
    simp only [Real.sin_two_mul, Real.cos_two_mul, Complex.add_re, Complex.sub_re,
      Complex.mul_re, Complex.add_im, Complex.sub_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im,
      mul_zero, add_zero, zero_add, sub_zero, zero_sub, mul_one]
    norm_num
  all_goals nlinarith [Real.sin_sq_add_cos_sq b]

theorem exp_double_angle_add_one (b : ℝ) :
    Complex.exp ((2 * b : ℝ) * Complex.I) + 1 =
      (2 * (Real.cos b : ℂ)) * Complex.exp ((b : ℂ) * Complex.I) := by
  rw [exp_real_mul_I, exp_real_mul_I]
  apply Complex.ext <;>
    simp only [Real.sin_two_mul, Real.cos_two_mul, Complex.add_re,
      Complex.mul_re, Complex.add_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
      Complex.I_re, Complex.I_im,
      mul_zero, add_zero, zero_add, sub_zero, mul_one] <;>
    norm_num <;> ring

theorem sin_frequency_eq_zero_iff (n : ℤ) :
    Real.sin ((n : ℝ) * (Real.pi / 7)) = 0 ↔ (7 : ℤ) ∣ n := by
  constructor
  · intro hs
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hs
    have he : (n : ℝ) = 7 * (k : ℝ) := by
      have hz : Real.pi * ((n : ℝ) - 7 * (k : ℝ)) = 0 := by nlinarith only [hk]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left Real.pi_ne_zero)
    exact ⟨k, by exact_mod_cast he⟩
  · rintro ⟨k, rfl⟩
    have he : ((7 * k : ℤ) : ℝ) * (Real.pi / 7) = (k : ℝ) * Real.pi := by push_cast; ring
    rw [he, Real.sin_int_mul_pi]

theorem fourier_seventh_phase {P : ℝ} (hP : 0 < P) (n : ℤ) :
    fourier n ((P / 7 : ℝ) : AddCircle P) =
      Complex.exp (((2 * ((n : ℝ) * (Real.pi / 7)) : ℝ) : ℂ) * Complex.I) := by
  rw [fourier_coe_apply]
  congr 1
  push_cast
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  field_simp

theorem fourier_seventh_phase_eq_one_iff {P : ℝ} (hP : 0 < P) (n : ℤ) :
    fourier n ((P / 7 : ℝ) : AddCircle P) = 1 ↔ (7 : ℤ) ∣ n := by
  rw [← sin_frequency_eq_zero_iff]
  rw [fourier_seventh_phase hP n, ← sub_eq_zero, exp_double_angle_sub_one]
  simp only [mul_eq_zero, Complex.exp_ne_zero, or_false, Complex.I_ne_zero,
    Complex.ofReal_eq_zero]
  norm_num

/-- The magnitude of the shift phase minus one is twice the sine magnitude. -/
theorem norm_fourier_seventh_phase_sub_one {P : ℝ} (hP : 0 < P) (n : ℤ) :
    ‖fourier n ((P / 7 : ℝ) : AddCircle P) - 1‖ =
      2 * |Real.sin ((n : ℝ) * (Real.pi / 7))| := by
  rw [fourier_seventh_phase hP n, exp_double_angle_sub_one]
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I]

/-- Eliminate the tangent coefficient from its shift and derivative relations. -/
theorem multiplier_of_phase_relations {b l w : ℝ} {u v s : ℂ}
    (hl : l ≠ 0) (hsin : Real.sin b ≠ 0)
    (hshift : (Complex.exp ((2 * b : ℝ) * Complex.I) - 1) * u = 2 * v)
    (hderiv : Complex.I * (w : ℂ) * u = (2 / (l : ℂ)) * s - Complex.I * (w : ℂ) * v) :
    s = ((l * w / 2) * (Real.cos b / Real.sin b) : ℝ) * v := by
  have hplus : (Complex.exp ((2 * b : ℝ) * Complex.I) + 1) * u = 2 * (u + v) := by
    linear_combination hshift
  have hr : Complex.I * (Real.sin b : ℂ) * (u + v) = (Real.cos b : ℂ) * v := by
    calc
      _ = Complex.I * (Real.sin b : ℂ) *
          ((Complex.exp ((2 * b : ℝ) * Complex.I) + 1) * u / 2) := by rw [hplus]; ring
      _ = (Real.cos b : ℂ) *
          ((Complex.exp ((2 * b : ℝ) * Complex.I) - 1) * u / 2) := by
            rw [exp_double_angle_add_one, exp_double_angle_sub_one]
            ring
      _ = _ := by rw [hshift]; ring
  have hlC : (l : ℂ) ≠ 0 := by exact_mod_cast hl
  have hsC : (Real.sin b : ℂ) ≠ 0 := by exact_mod_cast hsin
  have he : (2 / (l : ℂ)) * (Real.sin b : ℂ) * s = (w : ℂ) * (Real.cos b : ℂ) * v := by
    linear_combination -(Real.sin b : ℂ) * hderiv + (w : ℂ) * hr
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  field_simp [hlC, hsC] at he ⊢
  linear_combination he

end UlamFloating.Seventh
