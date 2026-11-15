import Seventh.PreliminaryBounds
import Seventh.Variance

/-!
# The lower bound on the dimensionless frequency

The argument uses a fixed rational lower bound on the angle, followed by
the secant inequality for sine. All numerical comparisons are proved by
Taylor estimates in Lean.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

theorem cos_nine_twentyfifths_gt : (93589 : ℝ) / 100000 < Real.cos (9 / 25) := by
  have h := cos_taylor_error 6 (x := (9 : ℝ) / 25) (by norm_num)
  norm_num [taylorAtZero, Finset.sum_range_succ, Real.iteratedDeriv_add_one_sin,
    Real.iteratedDeriv_add_one_cos, Nat.factorial] at h ⊢
  have hlo := (abs_le.mp h).1
  linarith

theorem lower_frequency_projection_comparison :
    (21 : ℝ) / 50 < (Real.pi / 7) * Real.cos (9 / 25) := by
  have hcos := cos_nine_twentyfifths_gt
  have hp := mul_lt_mul_of_pos_left hcos (by positivity : 0 < Real.pi / 7)
  nlinarith [Real.pi_gt_d4]

theorem sin_nine_twentyfifths_gt : (352 : ℝ) / 1000 < Real.sin (9 / 25) := by
  have h := sin_taylor_error 5 (x := (9 : ℝ) / 25) (by norm_num)
  norm_num [taylorAtZero, Finset.sum_range_succ, Real.iteratedDeriv_add_one_sin,
    Real.iteratedDeriv_add_one_cos, Nat.factorial] at h ⊢
  have hlo := (abs_le.mp h).1
  linarith

theorem sin_fiftyfour_twentyfifths_gt : (830 : ℝ) / 1000 < Real.sin (54 / 25) := by
  have h := sin_taylor_error 11 (x := (54 : ℝ) / 25) (by norm_num)
  norm_num [taylorAtZero, Finset.sum_range_succ, Real.iteratedDeriv_add_one_sin,
    Real.iteratedDeriv_add_one_cos, Nat.factorial] at h ⊢
  have hlo := (abs_le.mp h).1
  linarith

theorem lower_frequency_sine_comparison :
    (21 : ℝ) / 50 < (6 * Real.sin (9 / 25) + Real.sin (54 / 25)) / 7 := by
  linarith [sin_nine_twentyfifths_gt, sin_fiftyfour_twentyfifths_gt]

/-- A concave function lies above its endpoint secant, without division. -/
theorem concave_chord_le {f : ℝ → ℝ} {S : Set ℝ} {B U z : ℝ}
    (hf : ConcaveOn ℝ S f) (hB : B ∈ S) (hU : U ∈ S)
    (hzB : B ≤ z) (hzU : z ≤ U) :
    (U - z) * f B + (z - B) * f U ≤ (U - B) * f z := by
  rcases hzB.eq_or_lt with rfl | hBz
  · simp
  rcases hzU.eq_or_lt with rfl | hzU
  · simp
  have h := hf.neg.secant_mono_aux1 hB hU hBz hzU
  dsimp at h
  nlinarith

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Six other contact angles consume at least `6 B` of the total `π`. -/
theorem ContactSystem.angle_le_of_lower {γ : ℝ → Plane} {P l B : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hB : ∀ t, B ≤ α t) (t : ℝ) :
    α t ≤ Real.pi - 6 * B := by
  have hsum := hs.seven_angle_sum t
  simp [Fin.sum_univ_succ] at hsum
  have h1 := hB (t + P / 7)
  have h2 := hB (t + 2 * (P / 7))
  have h3 := hB (t + 3 * (P / 7))
  have h4 := hB (t + 4 * (P / 7))
  have h5 := hB (t + 5 * (P / 7))
  have h6 := hB (t + 6 * (P / 7))
  linarith

/-- A hypothetical small frequency would force every contact angle above `9/25`. -/
theorem ContactSystem.angle_gt_nine_twentyfifths_of_frequency_le
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α)
    (hsmall : Real.pi * l / P ≤ 21 / 50) (t : ℝ) : 9 / 25 < α t := by
  have hP := hb.period_pos
  have hproj := hs.arc_projection hb (by positivity : 0 < P / 7) hl hc t
  by_contra hnot
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (hs.angle_range t).1.le
    (by linarith [Real.pi_gt_d2] : (9 : ℝ) / 25 ≤ Real.pi) (le_of_not_gt hnot)
  have hp : (P / 7) * Real.cos (9 / 25) ≤ l :=
    (mul_le_mul_of_nonneg_left hcos (by positivity)).trans hproj
  have hfreq := (div_le_iff₀ hP).mp hsmall
  have hscaled := mul_lt_mul_of_pos_left lower_frequency_projection_comparison hP
  have hpi := mul_le_mul_of_nonneg_left hp Real.pi_pos.le
  nlinarith

/-- The seven-angle partition and concavity give a lower bound on mean sine. -/
theorem ContactSystem.frequency_ge_of_angle_lower {γ : ℝ → Plane} {P l B : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (hl : 0 < l)
    (hB0 : 0 ≤ B) (hBpi : 7 * B < Real.pi) (hB : ∀ t, B ≤ α t) :
    (6 * Real.sin B + Real.sin (6 * B)) / 7 ≤ Real.pi * l / P := by
  have hα := hs.contDiff_angle.continuous
  have hleft : Continuous (fun t => (Real.pi - 6 * B - α t) * Real.sin B +
      (α t - B) * Real.sin (6 * B)) := by fun_prop
  have hright : Continuous (fun t => (Real.pi - 7 * B) * Real.sin (α t)) := by fun_prop
  have hpoint (t : ℝ) :
      (Real.pi - 6 * B - α t) * Real.sin B + (α t - B) * Real.sin (6 * B) ≤
        (Real.pi - 7 * B) * Real.sin (α t) := by
    have h := concave_chord_le strictConcaveOn_sin_Icc.concaveOn
      (show B ∈ Icc 0 Real.pi from ⟨hB0, by linarith⟩)
      (show Real.pi - 6 * B ∈ Icc 0 Real.pi from ⟨by linarith, by linarith⟩)
      (hB t) (hs.angle_le_of_lower hB t)
    rw [Real.sin_pi_sub] at h
    nlinarith
  have hi := intervalIntegral.integral_mono_on (μ := volume) hP.le
    (hleft.intervalIntegrable 0 P) (hright.intervalIntegrable 0 P) (fun t _ => hpoint t)
  rw [intervalIntegral.integral_add
      (((continuous_const.sub hα).mul continuous_const).intervalIntegrable _ _)
      (((hα.sub continuous_const).mul continuous_const).intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
    intervalIntegral.integral_sub intervalIntegrable_const (hα.intervalIntegrable _ _),
    intervalIntegral.integral_sub (hα.intervalIntegrable _ _) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, hs.integral_angle, hs.integral_sin_angle hl] at hi
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hi
  have he : (Real.pi - 7 * B) * (P * ((6 * Real.sin B + Real.sin (6 * B)) / 7)) ≤
      (Real.pi - 7 * B) * (Real.pi * l) := by nlinarith only [hi]
  have he' := (mul_le_mul_iff_right₀ (by linarith : 0 < Real.pi - 7 * B)).mp he
  exact (le_div_iff₀ hP).mpr (by nlinarith only [he'])

/-- The strict lower endpoint of the PDF's numerical parameter interval. -/
theorem ContactSystem.frequency_gt {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) :
    (21 : ℝ) / 50 < Real.pi * l / P := by
  by_contra hn
  have hsmall := le_of_not_gt hn
  have hB := fun t => (hs.angle_gt_nine_twentyfifths_of_frequency_le hb hl hc hsmall t).le
  have hi := hs.frequency_ge_of_angle_lower hb.period_pos hl
    (by norm_num : 0 ≤ (9 : ℝ) / 25)
    (by linarith [Real.pi_gt_d2] : 7 * ((9 : ℝ) / 25) < Real.pi) hB
  norm_num at hi
  have hn := lower_frequency_sine_comparison
  norm_num at hn
  linarith

/-- A certified frequency upper endpoint gives a rational contact-angle lower bound. -/
theorem ContactSystem.angle_gt_of_frequency_comparison {K : Set Plane} {P l B r : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α)
    (hBpi : B ≤ Real.pi) (hr : Real.pi * l / P ≤ r)
    (hcomp : r < (Real.pi / 7) * Real.cos B) (t : ℝ) : B < α t := by
  have hP := hb.period_pos
  have hproj := hs.arc_projection hb (by positivity : 0 < P / 7) hl hc t
  by_contra hn
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (hs.angle_range t).1.le hBpi (le_of_not_gt hn)
  have hp := (mul_le_mul_of_nonneg_left hcos (by positivity : 0 ≤ P / 7)).trans hproj
  have hfreq := (div_le_iff₀ hP).mp hr
  have hscaled := mul_lt_mul_of_pos_left hcomp hP
  have hpi := mul_le_mul_of_nonneg_left hp Real.pi_pos.le
  nlinarith

end UlamFloating.Seventh
