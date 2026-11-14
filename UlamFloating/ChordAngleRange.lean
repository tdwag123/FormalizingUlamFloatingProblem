import UlamFloating.SampledAngles

/-!
# Convex ranges and extraction of cyclic angle coordinates

A direction change of pi or more over one chord interval would force two
interlaced or adjacent chords to be parallel. Strict convexity excludes
this. Consequently the sampled real angle coordinates lie in `(0, π)`.
The differential equation for these coordinates is not asserted here.
-/

namespace UlamFloating

open scoped BigOperators

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A global increasing chord angle advances by less than pi over one
chord interval smaller than half the boundary period. -/
theorem IsUnitSpeedBoundary.chord_angle_increment_lt_pi
    {K : Set Plane} {P h : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ) (hh : 0 < h) (hhalf : 2 * h < P)
    (hrot : ∀ t, γ (t + h) - γ t = Real.cos (θ t) • (γ h - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ h - γ 0)) (t : ℝ) :
    θ (t + h) - θ t < Real.pi := by
  by_contra hnot
  have hge : Real.pi ≤ θ (t + h) - θ t := le_of_not_gt hnot
  let s := θ.symm (θ t + Real.pi)
  have hs : θ s = θ t + Real.pi := θ.apply_symm_apply _
  have hts : t < s := θ.strictMono.lt_iff_lt.mp (by rw [hs]; linarith [Real.pi_pos])
  have hsh : s ≤ t + h := θ.le_iff_le.mp (by rw [hs]; linarith)
  have hopposite : γ (s + h) - γ s = -(γ (t + h) - γ t) := by
    rw [hrot s, hrot t, hs, Real.cos_add_pi, Real.sin_add_pi]
    module
  rcases lt_or_eq_of_le hsh with hsh | hsh
  · have hbad := hb.chord_not_parallel_of_interlaced hts hsh
      (by linarith : t + h < s + h) (by linarith : s + h < t + P) (-1)
    exact hbad (by simpa only [neg_one_smul] using hopposite)
  · rw [hsh] at hopposite
    have hbad := hb.chord_not_parallel_of_adjacent
      (by linarith : t < t + h) (by linarith : t + h < t + h + h)
      (by linarith : t + h + h < t + P) (-1)
    exact hbad (by simpa only [neg_one_smul] using hopposite)

/-- Pi minus the direction change of consecutive chords lies in `(0, π)`. -/
theorem IsUnitSpeedBoundary.angle_coordinate_pos_lt_pi
    {K : Set Plane} {P h : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ) (hh : 0 < h) (hhalf : 2 * h < P)
    (hrot : ∀ t, γ (t + h) - γ t = Real.cos (θ t) • (γ h - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ h - γ 0)) (t : ℝ) :
    0 < Real.pi + θ t - θ (t + h) ∧ Real.pi + θ t - θ (t + h) < Real.pi := by
  have hsmall := hb.chord_angle_increment_lt_pi o θ hh hhalf hrot t
  have hlarge := θ.strictMono (show t < t + h by linarith)
  constructor <;> linarith

/-- Extract periodic `C¹` cyclic angle coordinates from constant-chord
boundary data for any `n ≥ 3`. The angle range, exact sum, and one-step
time-shift law are conclusions. No pentagon ODE is assumed or concluded. -/
theorem IsUnitSpeedBoundary.exists_cyclic_angle_coordinates
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} {n : ℕ}
    (hb : IsUnitSpeedBoundary K P γ) (hn : 3 ≤ n) (hl : 0 < l)
    (hc : HasConstantChord γ (P / n) l) :
    ∃ (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ),
      ContDiff ℝ 1 (fun t => θ t) ∧ θ 0 = 0 ∧ θ P = 2 * Real.pi ∧
      (∀ t, γ (t + P / n) - γ t = Real.cos (θ t) • (γ (P / n) - γ 0) +
        Real.sin (θ t) • o.rightAngleRotation (γ (P / n) - γ 0)) ∧
      (∀ i : Fin n, ContDiff ℝ 1 (cyclicAngleCoordinates θ P n i) ∧
        Function.Periodic (cyclicAngleCoordinates θ P n i) P) ∧
      (∀ t, ∑ i, cyclicAngleCoordinates θ P n i t = ((n : ℝ) - 2) * Real.pi) ∧
      (∀ i t, 0 < cyclicAngleCoordinates θ P n i t ∧
        cyclicAngleCoordinates θ P n i t < Real.pi) ∧
      (∀ i t, cyclicAngleCoordinates θ P n (finRotate n i) t =
        cyclicAngleCoordinates θ P n i (t + P / n)) := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hh : 0 < P / n := div_pos hb.period_pos hnpos
  have hhalf : 2 * (P / n) < P := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hnpos).mpr
    nlinarith [hb.period_pos]
  obtain ⟨o, θ, hθc, _, hθ0, hturn, _, hrot, hshift⟩ :=
    hb.chord_angle_coordinates_one_turn hh hhalf hl hc
  have hp : ∀ t, θ (t + P) = θ t + 2 * Real.pi := by
    intro t
    simpa only [Int.cast_one, one_mul] using hshift t 1
  refine ⟨o, θ, hθc, hθ0, hturn, hrot, ?_, ?_, ?_, ?_⟩
  · intro i
    exact ⟨cyclicAngleCoordinates_contDiff hθc P i, cyclicAngleCoordinates_periodic hp i⟩
  · intro t
    rw [cyclicAngleCoordinates_sum hp (by omega : n ≠ 0)]
    ring
  · intro i t
    exact hb.angle_coordinate_pos_lt_pi o θ hh hhalf hrot
      (t + (i.val : ℝ) * (P / n))
  · exact cyclicAngleCoordinates_rotate hp

end UlamFloating
