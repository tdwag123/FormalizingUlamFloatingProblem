import UlamFloating.FourierEnergy
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Interval Fourier coefficient identities

These lemmas use mathlib's `fourierCoeffOn` directly. Translation is proved
for periodic functions; the derivative identity retains the actual period.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

theorem fourier_monomial_add {P : ℝ} (n : ℤ) (x y : AddCircle P) :
    fourier n (x + y) = fourier n x * fourier n y := by
  simp only [fourier_apply, zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]

theorem continuous_fourier_monomial (P : ℝ) (n : ℤ) :
    Continuous (fun t : ℝ => fourier n (t : AddCircle P)) :=
  (fourier n).continuous.comp (AddCircle.continuous_mk' P)

theorem periodic_fourier_monomial (P : ℝ) (n : ℤ) :
    Function.Periodic (fun t : ℝ => fourier n (t : AddCircle P)) P := by
  intro t
  simp only [AddCircle.coe_add_period]

/-- Fourier coefficients on `[0,P]` written as complex-valued interval integrals. -/
theorem fourierCoeffOn_integral {P : ℝ} (hP : 0 < P) (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn hP f n = (P⁻¹ : ℂ) *
      ∫ t in (0 : ℝ)..P, fourier (-n) (t : AddCircle P) * f t := by
  rw [fourierCoeffOn_eq_integral]
  simp only [fourier_coe_apply, sub_zero, one_div, smul_eq_mul,
    Complex.real_smul, Complex.ofReal_inv]

theorem fourierCoeffOn_add {P : ℝ} (hP : 0 < P) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    fourierCoeffOn hP (fun t => f t + g t) n =
      fourierCoeffOn hP f n + fourierCoeffOn hP g n := by
  simp only [fourierCoeffOn_integral, mul_add]
  rw [intervalIntegral.integral_add
    (((continuous_fourier_monomial P (-n)).mul hf).intervalIntegrable _ _)
    (((continuous_fourier_monomial P (-n)).mul hg).intervalIntegrable _ _), mul_add]

theorem fourierCoeffOn_sub {P : ℝ} (hP : 0 < P) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) (n : ℤ) :
    fourierCoeffOn hP (fun t => f t - g t) n =
      fourierCoeffOn hP f n - fourierCoeffOn hP g n := by
  simp only [fourierCoeffOn_integral, mul_sub]
  rw [intervalIntegral.integral_sub
    (((continuous_fourier_monomial P (-n)).mul hf).intervalIntegrable _ _)
    (((continuous_fourier_monomial P (-n)).mul hg).intervalIntegrable _ _), mul_sub]

/-- Translating a periodic function multiplies its Fourier coefficient by a phase. -/
theorem fourierCoeffOn_translate {P : ℝ} (hP : 0 < P) {f : ℝ → ℂ}
    (hp : Function.Periodic f P) (d : ℝ) (n : ℤ) :
    fourierCoeffOn hP (fun t => f (t + d)) n =
      fourier n (d : AddCircle P) * fourierCoeffOn hP f n := by
  let F : ℝ → ℂ := fun t => fourier (-n) (t : AddCircle P) * f t
  have hF : Function.Periodic F P := by
    intro t
    change fourier (-n) ((t + P : ℝ) : AddCircle P) * f (t + P) =
      fourier (-n) (t : AddCircle P) * f t
    rw [AddCircle.coe_add_period, hp t]
  have hphase : fourier n (d : AddCircle P) * fourier (-n) (d : AddCircle P) = 1 := by
    rw [← fourier_add, add_neg_cancel, fourier_zero]
  have he (t : ℝ) : fourier (-n) (t : AddCircle P) * f (t + d) =
      fourier n (d : AddCircle P) * F (t + d) := by
    change fourier (-n) (t : AddCircle P) * f (t + d) =
      fourier n (d : AddCircle P) * (fourier (-n) ((t + d : ℝ) : AddCircle P) * f (t + d))
    rw [AddCircle.coe_add, fourier_monomial_add]
    calc
      _ = (fourier n (d : AddCircle P) * fourier (-n) (d : AddCircle P)) *
          (fourier (-n) (t : AddCircle P) * f (t + d)) := by rw [hphase, one_mul]
      _ = _ := by ring
  simp only [fourierCoeffOn_integral, he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_add_right]
  have hi := hF.intervalIntegral_add_eq d 0
  simp only [zero_add] at hi
  rw [zero_add, show P + d = d + P by ring, hi]
  dsimp [F]
  ring

/-- The nonzero-frequency derivative identity for a periodic endpoint pair. -/
theorem fourierCoeffOn_derivative {P : ℝ} (hP : 0 < P) {f g : ℝ → ℂ}
    (hder : ∀ t ∈ Icc 0 P, HasDerivAt f (g t) t)
    (hg : IntervalIntegrable g volume 0 P) (hend : f 0 = f P)
    {n : ℤ} (hn : n ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I * n) * fourierCoeffOn hP f n =
      (P : ℂ) * fourierCoeffOn hP g n := by
  have hc := fourierCoeffOn_of_hasDerivAt hP hn
    (fun t ht => hder t (by simpa only [uIcc_of_le hP.le] using ht)) hg
  rw [← hend, sub_self, mul_zero, zero_sub, Complex.ofReal_zero, sub_zero] at hc
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hc]
  field_simp

theorem fourierCoeffOn_zero_function {P : ℝ} (hP : 0 < P) (n : ℤ) :
    fourierCoeffOn hP (fun _ => (0 : ℂ)) n = 0 := by
  simp [fourierCoeffOn_integral]

theorem fourierCoeffOn_const_of_ne_zero {P : ℝ} (hP : 0 < P) (c : ℂ)
    {n : ℤ} (hn : n ≠ 0) : fourierCoeffOn hP (fun _ => c) n = 0 := by
  have he := fourierCoeffOn_derivative hP (fun t _ => hasDerivAt_const t c)
    (intervalIntegrable_const (c := (0 : ℂ))) rfl hn
  rw [fourierCoeffOn_zero_function, mul_zero] at he
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hpC : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  exact (mul_eq_zero.mp he).resolve_left (by simp [hnC, hpC])

/-- The derivative multiplier for real-valued functions, with complex coefficients. -/
theorem fourierCoeffOn_real_derivative {P : ℝ} (hP : 0 < P) {f g : ℝ → ℝ}
    (hder : ∀ t ∈ Icc 0 P, HasDerivAt f (g t) t) (hg : Continuous g)
    (hend : f 0 = f P) {n : ℤ} (hn : n ≠ 0) :
    Complex.I * ((2 * Real.pi * (n : ℝ) / P : ℝ) : ℂ) *
      fourierCoeffOn hP (fun t => (f t : ℂ)) n =
      fourierCoeffOn hP (fun t => (g t : ℂ)) n := by
  have he := fourierCoeffOn_derivative hP (fun t ht => (hder t ht).ofReal_comp)
    ((Complex.continuous_ofReal.comp hg).intervalIntegrable _ _) (congrArg Complex.ofReal hend) hn
  have hPC : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  apply mul_left_cancel₀ hPC
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I * n) *
        fourierCoeffOn hP (fun t => (f t : ℂ)) n := by
      simp only [Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat, Complex.ofReal_intCast]
      field_simp
    _ = _ := he

/-- Every Fourier coefficient is bounded by the normalized integral of the norm. -/
theorem norm_fourierCoeffOn_le {P : ℝ} (hP : 0 < P) (f : ℝ → ℂ) (n : ℤ) :
    ‖fourierCoeffOn hP f n‖ ≤ P⁻¹ * ∫ t in (0 : ℝ)..P, ‖f t‖ := by
  rw [fourierCoeffOn_integral, norm_mul]
  have hscalar : ‖(P⁻¹ : ℂ)‖ = P⁻¹ := by
    simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hP]
  rw [hscalar]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hP.le)
  have he := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun t => fourier (-n) (t : AddCircle P) * f t) hP.le
  have hn (t : ℝ) : ‖fourier (-n) (t : AddCircle P)‖ = 1 := Circle.norm_coe _
  simpa only [norm_mul, hn, one_mul] using he

/-- Opposite Fourier coefficients of a real function are conjugate. -/
theorem fourierCoeffOn_real_neg {P : ℝ} (hP : 0 < P) {f : ℝ → ℝ}
    (hf : Continuous f) (n : ℤ) :
    fourierCoeffOn hP (fun t => (f t : ℂ)) (-n) =
      starRingEnd ℂ (fourierCoeffOn hP (fun t => (f t : ℂ)) n) := by
  have hcont := (continuous_fourier_monomial P (-n)).mul (Complex.continuous_ofReal.comp hf)
  have hi := Complex.conjCLE.toContinuousLinearMap.intervalIntegral_comp_comm (μ := volume)
    (hcont.intervalIntegrable 0 P)
  change (∫ t in (0 : ℝ)..P, starRingEnd ℂ (fourier (-n) (t : AddCircle P) * (f t : ℂ))) =
    starRingEnd ℂ (∫ t in (0 : ℝ)..P, fourier (-n) (t : AddCircle P) * (f t : ℂ)) at hi
  simp only [map_mul, ← fourier_neg, neg_neg, Complex.conj_ofReal] at hi
  rw [fourierCoeffOn_integral, fourierCoeffOn_integral, map_mul]
  rw [← hi]
  simp only [neg_neg, map_inv₀, Complex.conj_ofReal]

end UlamFloating.Seventh
