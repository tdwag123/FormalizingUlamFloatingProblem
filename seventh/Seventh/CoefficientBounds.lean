import Seventh.FourierEnergyBounds

/-!
# Coefficient estimates for the geometric system

The remainder's coefficients control all angle modes except the first pair.
The tangent modes require separate treatment at the nonzero multiples of seven.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem ContactSystem.fourier_remainder_multiplier {γ : ℝ → Plane} {P l c : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (hl : 0 < l)
    {n : ℤ} (hn : ¬ (7 : ℤ) ∣ n) :
    fourierCoeffOn hP (fun t => (sineRemainder (Real.pi / 7) c (α t) : ℂ)) n =
      ((seventhMultiplier (Real.pi * l / P) n - c : ℝ) : ℂ) *
        fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n := by
  rw [fourier_sineRemainder hP hs.contDiff_angle.continuous (fun h => hn (by simp [h])),
    hs.fourier_sine_multiplier hP hl hn]
  simp only [seventhMultiplier, Complex.ofReal_sub]
  ring

/-- A positive gap between the multiplier and the secant center controls every
nonexceptional angle coefficient, including the vanishing resonant coefficients. -/
theorem ContactSystem.angle_coefficient_bound {γ : ℝ → Plane} {P l c δ : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (hl : 0 < l)
    (hδ : 0 < δ) (hgap : SpectralGapBounds (Real.pi * l / P) c δ)
    {n : ℤ} (hp : n ≠ 1) (hm : n ≠ -1) :
    ‖fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n‖ ^ 2 ≤
      (δ⁻¹) ^ 2 * ‖fourierCoeffOn hP
        (fun t => (sineRemainder (Real.pi / 7) c (α t) : ℂ)) n‖ ^ 2 := by
  by_cases hseven : (7 : ℤ) ∣ n
  · rw [hs.fourier_angle_eq_zero_of_seven_dvd hP hseven, norm_zero, zero_pow (by decide)]
    positivity
  have hfreq : 0 ≤ Real.pi * l / P := by positivity
  have hg := hgap.mode_gap hfreq hseven hp hm
  have he := congrArg norm (hs.fourier_remainder_multiplier (c := c) hP hl hseven)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at he
  have hn := mul_le_mul_of_nonneg_right hg
    (norm_nonneg (fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n))
  rw [← he] at hn
  have hsq := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hn
  rw [mul_pow] at hsq
  have hscaled := mul_le_mul_of_nonneg_left hsq (sq_nonneg δ⁻¹)
  simpa only [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hδ.ne', one_pow, one_mul] using hscaled

/-- Nonresonant tangent modes are controlled by the centered contact angle. -/
theorem ContactSystem.tangent_coefficient_bound_of_not_seven_dvd {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P)
    {n : ℤ} (hn : ¬ (7 : ℤ) ∣ n) :
    ‖fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n‖ ^ 2 ≤
      (Real.sin (Real.pi / 7))⁻¹ ^ 2 *
        ‖fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n‖ ^ 2 := by
  have hsine : 0 < Real.sin (Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have he := hs.fourier_norm_relation hP n
  have hm := mul_le_mul_of_nonneg_right (abs_sin_frequency_ge hn)
    (norm_nonneg (fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n))
  rw [he] at hm
  have hsq := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hm
  rw [mul_pow] at hsq
  have hscaled := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.sin (Real.pi / 7))⁻¹)
  simpa only [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hsine.ne', one_pow, one_mul] using hscaled

/-- At a nonzero resonant mode, the nonlinear remainder controls the tangent. -/
theorem ContactSystem.resonant_tangent_norm_relation {γ : ℝ → Plane} {P l c : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (hl : 0 < l)
    {n : ℤ} (hn : (7 : ℤ) ∣ n) (hn0 : n ≠ 0) :
    (Real.pi * l / P) * |(n : ℝ)| *
      ‖fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n‖ =
      ‖fourierCoeffOn hP (fun t => (sineRemainder (Real.pi / 7) c (α t) : ℂ)) n‖ := by
  have hv := hs.fourier_angle_eq_zero_of_seven_dvd hP hn
  have hN := fourier_sineRemainder (a := Real.pi / 7) (c := c) hP hs.contDiff_angle.continuous hn0
  rw [hv, mul_zero, sub_zero] at hN
  have hd := hs.fourier_derivative hP hn0
  rw [hv, mul_zero, sub_zero, ← hN] at hd
  have he := congrArg norm hd
  simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
    norm_div, Complex.norm_ofNat, abs_of_pos Real.pi_pos, abs_of_pos hP,
    abs_of_pos hl] at he
  field_simp [hl.ne', hP.ne'] at he ⊢
  nlinarith only [he]

theorem ContactSystem.tangent_coefficient_bound_of_seven_dvd {γ : ℝ → Plane} {P l c : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (hl : 0 < l)
    {n : ℤ} (hn : (7 : ℤ) ∣ n) (hn0 : n ≠ 0) :
    ‖fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n‖ ^ 2 ≤
      (7 * (Real.pi * l / P))⁻¹ ^ 2 *
        ‖fourierCoeffOn hP (fun t => (sineRemainder (Real.pi / 7) c (α t) : ℂ)) n‖ ^ 2 := by
  have habsZ : (7 : ℤ) ≤ |n| := by
    obtain ⟨k, hk⟩ := hn
    rcases le_total 0 n with h | h
    · rw [abs_of_nonneg h]
      omega
    · rw [abs_of_nonpos h]
      omega
  have habs : (7 : ℝ) ≤ |(n : ℝ)| := by exact_mod_cast habsZ
  have hfreq : 0 < Real.pi * l / P := by positivity
  have hscale : 0 < 7 * (Real.pi * l / P) := by positivity
  have he := hs.resonant_tangent_norm_relation (c := c) hP hl hn hn0
  have hm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left habs hfreq.le)
    (norm_nonneg (fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n))
  rw [he] at hm
  have hm' : (7 * (Real.pi * l / P)) *
      ‖fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n‖ ≤
      ‖fourierCoeffOn hP (fun t => (sineRemainder (Real.pi / 7) c (α t) : ℂ)) n‖ := by
    nlinarith only [hm]
  have hsq := (sq_le_sq₀ (by positivity) (norm_nonneg _)).mpr hm'
  rw [mul_pow] at hsq
  have hscaled := mul_le_mul_of_nonneg_left hsq (sq_nonneg (7 * (Real.pi * l / P))⁻¹)
  simpa only [← mul_assoc, ← mul_pow, inv_mul_cancel₀ hscale.ne', one_pow, one_mul] using hscaled

/-- A uniform coefficient bound covering all integer modes. -/
theorem ContactSystem.tangent_coefficient_bound {γ : ℝ → Plane} {P l c : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (hl : 0 < l) (n : ℤ) :
    ‖fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n‖ ^ 2 ≤
      (Real.sin (Real.pi / 7))⁻¹ ^ 2 *
        ‖fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n‖ ^ 2 +
      (7 * (Real.pi * l / P))⁻¹ ^ 2 *
        ‖fourierCoeffOn hP (fun t => (sineRemainder (Real.pi / 7) c (α t) : ℂ)) n‖ ^ 2 := by
  by_cases hn0 : n = 0
  · subst n
    rw [hs.fourier_tangent_zero hP, norm_zero, zero_pow (by decide)]
    positivity
  by_cases hn : (7 : ℤ) ∣ n
  · exact (hs.tangent_coefficient_bound_of_seven_dvd hP hl hn hn0).trans
      (le_add_of_nonneg_left (by positivity))
  · exact (hs.tangent_coefficient_bound_of_not_seven_dvd hP hn).trans
      (le_add_of_nonneg_right (by positivity))

end UlamFloating.Seventh
