import Seventh.TrigBounds
import Seventh.Concavity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Exact preliminary numerical bounds

These inequalities are reconstructed from Taylor's theorem inside Lean.
The original research bundle and its numerical outputs are not used.
-/

namespace UlamFloating.Seventh

/-- A rational lower bound sufficient for the quarter-radian comparison. -/
theorem cos_quarter_gt : (968 : ℝ) / 1000 < Real.cos (1 / 4) := by
  have h := cos_taylor_error 4 (x := (1 : ℝ) / 4) (by norm_num)
  norm_num [taylorAtZero, Finset.sum_range_succ, Real.iteratedDeriv_add_one_sin,
    Real.iteratedDeriv_add_one_cos, Nat.factorial] at h ⊢
  have hlo := (abs_le.mp h).1
  linarith

/-- A rational upper bound for sine at a rational upper bound on `π/7`. -/
theorem sin_upper_endpoint_lt : Real.sin ((4488 : ℝ) / 10000) < 434 / 1000 := by
  have h := sin_taylor_error 5 (x := (4488 : ℝ) / 10000) (by norm_num)
  norm_num [taylorAtZero, Finset.sum_range_succ, Real.iteratedDeriv_add_one_sin,
    Real.iteratedDeriv_add_one_cos, Nat.factorial] at h ⊢
  have hhi := (abs_le.mp h).2
  linarith

/-- The upper bound on the circular value of the dimensionless frequency. -/
theorem sin_pi_div_seven_lt : Real.sin (Real.pi / 7) < 434 / 1000 := by
  have ha : Real.pi / 7 ≤ (4488 : ℝ) / 10000 := by linarith [Real.pi_lt_d4]
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ Real.pi / 7)
    (by linarith [Real.pi_gt_d2] : (4488 : ℝ) / 10000 ≤ Real.pi / 2) ha
  exact hm.trans_lt sin_upper_endpoint_lt

/-- The first strict numerical comparison in equation (13) of the PDF. -/
theorem quarter_projection_comparison :
    Real.sin (Real.pi / 7) < (Real.pi / 7) * Real.cos (1 / 4) := by
  have hpi := Real.pi_gt_d2
  have hcos := cos_quarter_gt
  have hprod := mul_lt_mul_of_pos_left hcos (by positivity : 0 < Real.pi / 7)
  have hs := sin_pi_div_seven_lt
  nlinarith

/-- The geometric contact angle is strictly larger than one quarter radian. -/
theorem ContactSystem.angle_gt_quarter {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (t : ℝ) : 1 / 4 < α t := by
  have hP : 0 < P := hb.period_pos
  have hfreq := hs.frequency_le_sin hb.period_pos hl
  have hproj := hs.arc_projection hb (by positivity : 0 < P / 7) hl hc t
  have hstrict := quarter_projection_comparison
  by_contra hnot
  have hangle : α t ≤ 1 / 4 := le_of_not_gt hnot
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (hs.angle_range t).1.le
    (by linarith [Real.pi_gt_d2] : (1 : ℝ) / 4 ≤ Real.pi) hangle
  have hfreq' := (div_le_iff₀ hb.period_pos).mp hfreq
  have hp : (P / 7) * Real.cos (1 / 4) ≤ l :=
    (mul_le_mul_of_nonneg_left hcos (by positivity)).trans hproj
  have hscaled := mul_lt_mul_of_pos_left hstrict hb.period_pos
  have hpi := mul_le_mul_of_nonneg_left hp Real.pi_pos.le
  nlinarith

end UlamFloating.Seventh
