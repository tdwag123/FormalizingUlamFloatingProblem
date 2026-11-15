import Seventh.FrequencyBounds

/-!
# Uniform upper bounds for the contact angle

The neighboring-sine inequality and the seven-angle partition force every
contact angle below `6/5`. The proof does not assume that the angles are acute.
-/

namespace UlamFloating.Seventh

open Set

theorem sin_six_fifths_gt : (93 : ℝ) / 100 < Real.sin (6 / 5) := by
  have h := sin_taylor_error 9 (x := (6 : ℝ) / 5) (by norm_num)
  norm_num [taylorAtZero, Finset.sum_range_succ, Real.iteratedDeriv_add_one_sin,
    Real.iteratedDeriv_add_one_cos, Nat.factorial] at h ⊢
  have hlo := (abs_le.mp h).1
  linarith

theorem cos_eleven_tenths_lt : Real.cos ((11 : ℝ) / 10) < 46 / 100 := by
  have h := cos_taylor_error 8 (x := (11 : ℝ) / 10) (by norm_num)
  norm_num [taylorAtZero, Finset.sum_range_succ, Real.iteratedDeriv_add_one_sin,
    Real.iteratedDeriv_add_one_cos, Nat.factorial] at h ⊢
  have hhi := (abs_le.mp h).2
  linarith

/-- Sine is at least its common endpoint value on a symmetric subinterval. -/
theorem sin_ge_on_symmetric_interval {a z : ℝ} (ha : 0 ≤ a)
    (hhalf : a < Real.pi / 2) (hlo : a ≤ z) (hhi : z ≤ Real.pi - a) :
    Real.sin a ≤ Real.sin z := by
  have he := concave_chord_le strictConcaveOn_sin_Icc.concaveOn
    (show a ∈ Icc 0 Real.pi from ⟨ha, by linarith [Real.pi_pos]⟩)
    (show Real.pi - a ∈ Icc 0 Real.pi from ⟨by linarith [Real.pi_pos], by linarith⟩)
    hlo hhi
  rw [Real.sin_pi_sub] at he
  have hm : (Real.pi - 2 * a) * Real.sin a ≤ (Real.pi - 2 * a) * Real.sin z := by
    nlinarith only [he]
  exact (mul_le_mul_iff_right₀ (by linarith : 0 < Real.pi - 2 * a)).mp hm

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The outside four angles constrain the sum of the immediate neighbors. -/
theorem ContactSystem.three_angle_sum_le {γ : ℝ → Plane} {P l B : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hB : ∀ t, B ≤ α t) (t : ℝ) :
    α t + α (t + P / 7) + α (t + 2 * (P / 7)) ≤ Real.pi - 4 * B := by
  have hsum := hs.seven_angle_sum t
  simp [Fin.sum_univ_succ] at hsum
  have h3 := hB (t + 3 * (P / 7))
  have h4 := hB (t + 4 * (P / 7))
  have h5 := hB (t + 5 * (P / 7))
  have h6 := hB (t + 6 * (P / 7))
  linarith

/-- The neighbor inequality expressed solely in terms of the central angle. -/
theorem ContactSystem.sin_le_cos_angle {K : Set Plane} {P l B : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α)
    (hB0 : 0 ≤ B) (hB : ∀ t, B ≤ α t) (t : ℝ) :
    Real.sin (α t) ≤ 2 * Real.cos (α t / 2 + 2 * B) := by
  let s := t - P / 7
  have hst : s + P / 7 = t := by dsimp [s]; ring
  have hsum := hs.three_angle_sum_le hB s
  rw [hst] at hsum
  have hn := hs.sin_le_neighbors hb hl hc s
  rw [hst] at hn
  let x := α s
  let y := α (s + 2 * (P / 7))
  have hx : 0 < x := (hs.angle_range s).1
  have hy : 0 < y := (hs.angle_range (s + 2 * (P / 7))).1
  have hz : 0 < α t := (hs.angle_range t).1
  have hsum' : x + y ≤ Real.pi - α t - 4 * B := by dsimp [x, y]; linarith
  have hmid : (x + y) / 2 ∈ Icc 0 Real.pi := ⟨by positivity, by linarith⟩
  have htx := sin_le_tangent hmid
    ⟨hx.le, (hs.angle_range s).2.le⟩
  have hty := sin_le_tangent hmid
    ⟨hy.le, (hs.angle_range (s + 2 * (P / 7))).2.le⟩
  have hm := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ (x + y) / 2)
    (by linarith : (Real.pi - α t - 4 * B) / 2 ≤ Real.pi / 2)
    (by linarith : (x + y) / 2 ≤ (Real.pi - α t - 4 * B) / 2)
  rw [show (Real.pi - α t - 4 * B) / 2 = Real.pi / 2 - (α t / 2 + 2 * B) by ring,
    Real.sin_pi_div_two_sub] at hm
  change Real.sin (α t) ≤ Real.sin x + Real.sin y at hn
  nlinarith

/-- All geometric contact angles lie below `6/5`, hence are acute. -/
theorem ContactSystem.angle_lt_six_fifths {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (t : ℝ) : α t < 6 / 5 := by
  have hB := fun s => (hs.angle_gt_quarter hb hl hc s).le
  have hupper := hs.angle_le_of_lower hB t
  have hn := hs.sin_le_cos_angle hb hl hc (by norm_num : 0 ≤ (1 : ℝ) / 4) hB t
  by_contra hnot
  have hlo : (6 : ℝ) / 5 ≤ α t := le_of_not_gt hnot
  have hsine := sin_ge_on_symmetric_interval (by norm_num : 0 ≤ (6 : ℝ) / 5)
    (by linarith [Real.pi_gt_d2] : (6 : ℝ) / 5 < Real.pi / 2) hlo (by linarith)
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi (by norm_num : 0 ≤ (11 : ℝ) / 10)
    (by linarith [Real.pi_pos] : α t / 2 + 2 * (1 / 4) ≤ Real.pi)
    (by linarith : (11 : ℝ) / 10 ≤ α t / 2 + 2 * (1 / 4))
  linarith [sin_six_fifths_gt, cos_eleven_tenths_lt]

/-- A certified sine/cosine comparison improves the uniform upper angle bound. -/
theorem ContactSystem.angle_lt_of_comparison {K : Set Plane} {P l B U : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α)
    (hB0 : 0 ≤ B) (hU0 : 0 ≤ U) (hB : ∀ t, B ≤ α t)
    (hcomp : 2 * Real.cos (U / 2 + 2 * B) < Real.sin U) (t : ℝ) : α t < U := by
  have hacute : α t < Real.pi / 2 := by
    linarith [hs.angle_lt_six_fifths hb hl hc t, Real.pi_gt_d2]
  have hBpi : B ≤ Real.pi / 7 := by
    have hm := hs.angle_le_of_lower hB 0
    have hb0 := hB 0
    linarith
  have hn := hs.sin_le_cos_angle hb hl hc hB0 hB t
  by_contra hnot
  have hUα := le_of_not_gt hnot
  have hsin := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ U) hacute.le hUα
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ U / 2 + 2 * B)
    (by linarith [Real.pi_pos] : α t / 2 + 2 * B ≤ Real.pi)
    (by linarith : U / 2 + 2 * B ≤ α t / 2 + 2 * B)
  linarith

end UlamFloating.Seventh
