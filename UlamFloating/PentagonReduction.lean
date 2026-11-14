import UlamFloating.PentagonConstant

/-!
# Reduction of fifth-density rigidity to nonconstant geometric motion

A counterexample to disk rigidity would yield a nonconstant convex
five-angle solution with the original boundary reconstruction and cyclic
time shift. The analytic lower bound applies to every positive period of
that solution, including periods smaller than the boundary period.
-/

namespace UlamFloating

open scoped BigOperators

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A nondisk with the constant one-fifth chord property would produce a
nonconstant geometric pentagon solution. Every positive period of its
angle curve satisfies the proved analytic lower bound. -/
theorem IsUnitSpeedBoundary.nonconstant_pentagon_solution_with_lift_of_not_isDisk
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l) (hnotdisk : ¬ IsDisk K) :
    ∃ (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ),
      ContDiff ℝ 1 (fun t => θ t) ∧
      (∀ t, 0 < deriv (fun s => θ s) t) ∧
      (∀ t, θ (t + P) = θ t + 2 * Real.pi) ∧
      (∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
        Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0)) ∧
      let x := cyclicAngleCurve θ P 5
      ContDiff ℝ 1 x ∧ Function.Periodic x P ∧
      (∀ t, ∑ i, x t i = 3 * Real.pi) ∧
      (∀ t i, 0 < x t i ∧ x t i < Real.pi) ∧
      (∀ t i, x t (i + 1) = x (t + P / 5) i) ∧
      (∀ t, deriv x t = (2 / l) • pentagonAngleField (x t)) ∧
      (¬ ∃ c, ∀ t, x t = c) ∧
      (∀ T : ℝ, 0 < T → Function.Periodic x T → l * Real.pi / (2 * Real.sqrt 3) ≤ T) := by
  have hh : 0 < P / 5 := div_pos hb.period_pos (by norm_num)
  have hhalf : 2 * (P / 5) < P := by linarith [hb.period_pos]
  obtain ⟨o, θ, hθ, _, _, _, hbound, hrot, hshift⟩ :=
    hb.chord_angle_coordinates_one_turn hh hhalf hl hc
  have hp (t : ℝ) : θ (t + P) = θ t + 2 * Real.pi := by
    simpa only [Int.cast_one, one_mul] using hshift t 1
  have hnc : ¬ ∃ c, ∀ t, cyclicAngleCurve θ P 5 t = c := by
    intro hconst
    exact hnotdisk (hb.isDisk_of_constant_fifth_angles o θ hl hc hθ
      (fun t => (hbound t).1) hrot hp hconst)
  have hx := cyclicAngleCurve_contDiff hθ P 5
  have hode := hb.pentagon_angle_deriv o θ hl hc hθ (fun t => (hbound t).1) hrot hp
  refine ⟨o, θ, hθ, fun t => (hbound t).1, hp, hrot, hx,
    cyclicAngleCurve_periodic hp 5, ?_, ?_, ?_, hode, hnc, ?_⟩
  · intro t
    change (∑ i, cyclicAngleCoordinates θ P 5 i t) = 3 * Real.pi
    rw [cyclicAngleCoordinates_sum hp (by decide : 5 ≠ 0)]
    norm_num
    ring
  · intro t i
    exact hb.angle_coordinate_pos_lt_pi o θ hh hhalf hrot
      (t + (i.val : ℝ) * (P / 5))
  · intro t i
    change cyclicAngleCoordinates θ P 5 (i + 1) t =
      cyclicAngleCoordinates θ P 5 i (t + P / 5)
    simpa only [finRotate_succ_apply, Nat.cast_ofNat] using
      cyclicAngleCoordinates_rotate hp i t
  · intro T hT hper
    exact pentagonAngleField_period_ge_of_length hx hper hT hl hnc hode

/-- A nondisk yields a nonconstant geometric pentagon solution, with a
lower bound on every positive shape period. This version omits the
additional differentiability and turning data of the chord lift. -/
theorem IsUnitSpeedBoundary.nonconstant_pentagon_solution_of_not_isDisk
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l) (hnotdisk : ¬ IsDisk K) :
    ∃ (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ),
      (∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
        Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0)) ∧
      let x := cyclicAngleCurve θ P 5
      ContDiff ℝ 1 x ∧ Function.Periodic x P ∧
      (∀ t, ∑ i, x t i = 3 * Real.pi) ∧
      (∀ t i, 0 < x t i ∧ x t i < Real.pi) ∧
      (∀ t i, x t (i + 1) = x (t + P / 5) i) ∧
      (∀ t, deriv x t = (2 / l) • pentagonAngleField (x t)) ∧
      (¬ ∃ c, ∀ t, x t = c) ∧
      (∀ T : ℝ, 0 < T → Function.Periodic x T → l * Real.pi / (2 * Real.sqrt 3) ≤ T) := by
  obtain ⟨o, θ, _, _, _, hrest⟩ :=
    hb.nonconstant_pentagon_solution_with_lift_of_not_isDisk hl hc hnotdisk
  exact ⟨o, θ, hrest⟩

end UlamFloating
