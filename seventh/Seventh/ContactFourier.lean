import Seventh.PhaseAlgebra
import Seventh.TangentFluctuation

/-!
# Fourier relations of the geometric contact system

The coefficients are those of the actual contact angle and tangent lift of
the boundary. No independent solution of the angle equations is substituted.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The shift relation holds coefficientwise, including resonant modes. -/
theorem ContactSystem.fourier_shift {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (n : ℤ) :
    (fourier n ((P / 7 : ℝ) : AddCircle P) - 1) *
      fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n =
    2 * fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n := by
  let u := tangentFluctuation P θ α
  have hu : Continuous (fun t => (u t : ℂ)) :=
    Complex.continuous_ofReal.comp hs.contDiff_tangentFluctuation.continuous
  have hp : Function.Periodic (fun t => (u t : ℂ)) P := by
    intro t
    change (tangentFluctuation P θ α (t + P) : ℂ) = (tangentFluctuation P θ α t : ℂ)
    rw [hs.periodic_tangentFluctuation hP t]
  have he : (fun t => (u (t + P / 7) : ℂ) - (u t : ℂ)) =
      fun t => (2 : ℂ) * ((α t - Real.pi / 7 : ℝ) : ℂ) := by
    ext t
    exact_mod_cast hs.shift_tangentFluctuation hP t
  have hh := congrArg (fun f : ℝ → ℂ => fourierCoeffOn hP f n) he
  dsimp only at hh
  have hus : Continuous (fun t => (u (t + P / 7) : ℂ)) :=
    hu.comp (continuous_id.add continuous_const)
  rw [fourierCoeffOn_sub hP hus hu,
    fourierCoeffOn_translate hP hp, fourierCoeffOn.const_mul] at hh
  change _ * fourierCoeffOn hP (fun t => (u t : ℂ)) n = _
  linear_combination hh

/-- Every multiple of seven has zero centered contact-angle coefficient. -/
theorem ContactSystem.fourier_angle_eq_zero_of_seven_dvd {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P)
    {n : ℤ} (hn : (7 : ℤ) ∣ n) :
    fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n = 0 := by
  have he := hs.fourier_shift hP n
  rw [(fourier_seventh_phase_eq_one_iff hP n).mpr hn, sub_self, zero_mul] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

/-- The first harmonic and the other nonresonant modes share the exact norm relation. -/
theorem ContactSystem.fourier_norm_relation {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (n : ℤ) :
    |Real.sin ((n : ℝ) * (Real.pi / 7))| *
      ‖fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n‖ =
    ‖fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n‖ := by
  have he := congrArg norm (hs.fourier_shift hP n)
  rw [norm_mul, norm_fourier_seventh_phase_sub_one hP, norm_mul, Complex.norm_ofNat] at he
  linarith

/-- The centering of the tangent lift removes its zero Fourier mode. -/
theorem ContactSystem.fourier_tangent_zero {γ : ℝ → Plane} {P h l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (hP : 0 < P) :
    fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) 0 = 0 := by
  rw [fourierCoeffOn_integral]
  simp only [neg_zero, fourier_zero, one_mul, intervalIntegral.integral_ofReal,
    hs.integral_tangentFluctuation hP, Complex.ofReal_zero, mul_zero]

/-- The tangent derivative law as an exact Fourier identity at every nonzero mode. -/
theorem ContactSystem.fourier_derivative {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) {n : ℤ} (hn : n ≠ 0) :
    Complex.I * ((2 * Real.pi * (n : ℝ) / P : ℝ) : ℂ) *
        fourierCoeffOn hP (fun t => (tangentFluctuation P θ α t : ℂ)) n =
      (2 / (l : ℂ)) * fourierCoeffOn hP (fun t => (Real.sin (α t) : ℂ)) n -
      Complex.I * ((2 * Real.pi * (n : ℝ) / P : ℝ) : ℂ) *
        fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n := by
  have hα := hs.contDiff_angle.continuous
  have hα' := hs.contDiff_angle.continuous_deriv_one
  have hu := fourierCoeffOn_real_derivative hP
    (fun t _ => hs.hasDerivAt_tangentFluctuation t)
    (show Continuous (fun t => (2 / l) * Real.sin (α t) - deriv α t - 2 * Real.pi / P) by fun_prop)
    (by simpa only [zero_add] using (hs.periodic_tangentFluctuation hP 0).symm) hn
  have hv := fourierCoeffOn_real_derivative hP
    (fun t _ => ((hs.contDiff_angle.differentiable (by simp) t).hasDerivAt).sub_const (Real.pi / 7))
    hα' (by simpa only [zero_add] using
      congrArg (fun z => z - Real.pi / 7) (hs.periodic_angle 0).symm) hn
  have hsinC : Continuous (fun t => (Real.sin (α t) : ℂ)) := by fun_prop
  have hderC : Continuous (fun t : ℝ => ((deriv α t : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp hα'
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat] at hu
  rw [fourierCoeffOn_sub hP (by fun_prop) continuous_const,
    fourierCoeffOn_const_of_ne_zero hP _ hn, sub_zero,
    fourierCoeffOn_sub hP (by fun_prop) hderC,
    fourierCoeffOn.const_mul] at hu
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat] at hv ⊢
  rw [hu, ← hv]

/-- The exact multiplier `λ n cot(nπ/7)` for every nonresonant integer mode. -/
theorem ContactSystem.fourier_sine_multiplier {γ : ℝ → Plane} {P l : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (hl : 0 < l)
    {n : ℤ} (hn : ¬ (7 : ℤ) ∣ n) :
    fourierCoeffOn hP (fun t => (Real.sin (α t) : ℂ)) n =
      ((Real.pi * l / P * (n : ℝ) * Real.cot ((n : ℝ) * (Real.pi / 7)) : ℝ) : ℂ) *
        fourierCoeffOn hP (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n := by
  have hn0 : n ≠ 0 := fun h => hn (by simp [h])
  have hsin : Real.sin ((n : ℝ) * (Real.pi / 7)) ≠ 0 :=
    fun h => hn ((sin_frequency_eq_zero_iff n).mp h)
  have hshift := hs.fourier_shift hP n
  rw [fourier_seventh_phase hP] at hshift
  have he := multiplier_of_phase_relations hl.ne' hsin hshift (hs.fourier_derivative hP hn0)
  rw [he, Real.cot_eq_cos_div_sin]
  congr 2
  ring

end UlamFloating.Seventh
