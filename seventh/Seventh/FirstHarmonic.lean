import Seventh.ExponentialRemainder
import Seventh.BoundaryClosure
import Seventh.Variance

/-!
# First-harmonic control from closure

The quadratic remainder of the unit exponential bounds each of the two first
Fourier coefficients of the centered tangent lift by half its squared energy.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

/-- A closed unit-tangent exponential suppresses the negative first harmonic. -/
theorem norm_first_fourierCoeff_le_of_closure {P : ℝ} (hP : 0 < P) {u : ℝ → ℝ}
    (hu : Continuous u)
    (hclosure : fourierCoeffOn hP (fun t => Complex.exp ((u t : ℂ) * Complex.I)) (-1) = 0) :
    ‖fourierCoeffOn hP (fun t => (u t : ℂ)) (-1)‖ ≤ intervalVariance P u 0 / 2 := by
  let R : ℝ → ℂ := fun t => Complex.exp ((u t : ℂ) * Complex.I) - 1 - Complex.I * (u t : ℂ)
  have huc : Continuous (fun t => (u t : ℂ)) := Complex.continuous_ofReal.comp hu
  have hR : Continuous R := by dsimp [R]; fun_prop
  have hRnorm (t : ℝ) : ‖R t‖ ≤ (u t) ^ 2 / 2 := by
    simpa only [R, mul_comm Complex.I] using norm_exp_real_mul_I_remainder_le (u t)
  have hcoeff : fourierCoeffOn hP R (-1) = -Complex.I * fourierCoeffOn hP (fun t => (u t : ℂ)) (-1) := by
    change fourierCoeffOn hP (fun t => (Complex.exp ((u t : ℂ) * Complex.I) - 1) -
      Complex.I * (u t : ℂ)) (-1) = _
    rw [fourierCoeffOn_sub hP (by fun_prop) (by fun_prop),
      fourierCoeffOn_sub hP (by fun_prop) continuous_const,
      hclosure, fourierCoeffOn_const_of_ne_zero hP 1 (by norm_num),
      fourierCoeffOn.const_mul]
    ring
  have hc := norm_fourierCoeffOn_le hP R (-1)
  rw [hcoeff, norm_mul, norm_neg, Complex.norm_I, one_mul] at hc
  have hi := intervalIntegral.integral_mono_on (μ := volume) hP.le
    (hR.norm.intervalIntegrable _ _) (((hu.pow 2).div_const 2).intervalIntegrable _ _)
    (fun t _ => hRnorm t)
  rw [intervalIntegral.integral_div] at hi
  have hm := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hP.le)
  have he : P⁻¹ * ((∫ t in (0 : ℝ)..P, (u t) ^ 2) / 2) = intervalVariance P u 0 / 2 := by
    simp only [intervalVariance, sub_zero]
    ring
  exact hc.trans (hm.trans_eq he)

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Both first tangent harmonics obey the closure bound for the original boundary. -/
theorem ContactSystem.first_tangent_harmonic_bound {K : Set Plane} {P h l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ h l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) {n : ℤ} (hn : n = 1 ∨ n = -1) :
    ‖fourierCoeffOn hb.period_pos (fun t => (tangentFluctuation P θ α t : ℂ)) n‖ ≤
      intervalVariance P (tangentFluctuation P θ α) 0 / 2 := by
  have he := norm_first_fourierCoeff_le_of_closure hb.period_pos
    hs.contDiff_tangentFluctuation.continuous (hs.fourier_exp_tangentFluctuation_eq_zero hb hl hc)
  rcases hn with rfl | rfl
  · have hconj := fourierCoeffOn_real_neg hb.period_pos hs.contDiff_tangentFluctuation.continuous (1 : ℤ)
    have hnorm := congrArg norm hconj
    simpa only [hnorm, Complex.norm_conj] using he
  · exact he

end UlamFloating.Seventh
