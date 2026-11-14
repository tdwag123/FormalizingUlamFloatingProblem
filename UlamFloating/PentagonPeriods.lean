import UlamFloating.CyclicPeriods
import UlamFloating.PentagonReduction
import UlamFloating.PentagonTurning
import UlamFloating.BoundaryRotation

/-!
# The least shape period of a hypothetical fifth-density counterexample

The geometric extraction, constant-case rigidity, and analytic period gap
give a genuine least positive shape period. The boundary period is a
positive integer multiple of it, and that integer is coprime to five.
The actual chord direction advances by exactly `2π/m` over that period.
The original boundary rotates by this angle about one fixed center.
These conclusions do not yet exclude every possible nonconstant motion.
-/

namespace UlamFloating

open scoped BigOperators

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A nondisk satisfying the one-fifth chord condition would yield a
nonconstant geometric angle solution with least positive period `T`.
The traversal has `P = m T` with positive `m` coprime to five, and `T`
satisfies the analytic lower bound. The chord angle advances by `2π/m`
over this same period. All geometric reconstruction data remain. -/
theorem IsUnitSpeedBoundary.least_pentagon_period_of_not_isDisk
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
      ∃ (T : ℝ) (m : ℕ), IsLeast {S | Function.Periodic x S ∧ 0 < S} T ∧
        0 < m ∧ Nat.Coprime m 5 ∧ P = (m : ℝ) * T ∧
        l * Real.pi / (2 * Real.sqrt 3) ≤ T ∧
        (∀ t, θ (t + T) - θ t = 2 * Real.pi / m) ∧
        ∃ c : Plane, ∀ t, γ (t + T) - c =
          o.rotation ((2 * Real.pi / m : ℝ) : Real.Angle) (γ t - c) := by
  obtain ⟨o, θ, hθ, hpos, hturn, hrot, hx, hp, hsum, hrange, hshift, hode, hnc, hbound⟩ :=
    hb.nonconstant_pentagon_solution_with_lift_of_not_isDisk hl hc hnotdisk
  have hε : 0 < l * Real.pi / (2 * Real.sqrt 3) := by positivity
  have hshift' : ∀ t i, cyclicAngleCurve θ P 5 t (finRotate 5 i) =
      cyclicAngleCurve θ P 5 (t + P / (4 + 1)) i := by
    intro t i
    have hi : finRotate 5 i = i + 1 := finRotate_succ_apply i
    have h := (congrArg (fun j => cyclicAngleCurve θ P 5 t j) hi).trans (hshift t i)
    simpa only [show (4 : ℝ) + 1 = 5 by norm_num] using h
  obtain ⟨T, m, hT, hmpos, hm, hnotdiv, hTbound⟩ :=
    exists_least_period_cyclic_motion hb.period_pos hp hε hbound hshift' hsum hnc
  have hcop : Nat.Coprime m 5 :=
    ((by decide : Nat.Prime 5).coprime_iff_not_dvd.mpr hnotdiv).symm
  have hadvance :=
    hb.chord_angle_advance_of_fifth_shape_period o θ hl hc hθ hpos hrot hturn
      hT.1.1 (Nat.ne_of_gt hmpos) hm
  refine ⟨o, θ, hrot, hx, hp, hsum, hrange, hshift, hode, hnc,
    T, m, hT, hmpos, hcop, hm, hTbound, hadvance, ?_⟩
  refine ⟨polygonCentroid (finRotate 5) o (fun i => boundarySamples γ P 5 i 0), ?_⟩
  intro t
  exact hb.rotation_about_centroid_of_chord_angle_increment (by decide : 3 ≤ 5)
    o θ hl hc hrot (fun s => by linarith [hadvance s]) t

end UlamFloating
