import UlamFloating.SampledAngles
import UlamFloating.SamplingShift

/-!
# Euclidean curves of cyclic angles

Bundle the finite angle coordinates in their Euclidean space, so that
ordinary differential equations and norm estimates apply directly.
-/

noncomputable section

namespace UlamFloating

open Fin.NatCast

/-- The Euclidean curve whose components are the cyclic angle coordinates. -/
def cyclicAngleCurve (θ : ℝ → ℝ) (P : ℝ) (n : ℕ) (t : ℝ) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => cyclicAngleCoordinates θ P n i t)

/-- Bundling the coordinates preserves continuous differentiability. -/
theorem cyclicAngleCurve_contDiff {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (P : ℝ) (n : ℕ) :
    ContDiff ℝ 1 (cyclicAngleCurve θ P n) := by
  apply (contDiff_piLp 2).mpr
  exact fun i => cyclicAngleCoordinates_contDiff hθ P i

/-- Bundling the coordinates preserves their period. -/
theorem cyclicAngleCurve_periodic {θ : ℝ → ℝ} {P A : ℝ}
    (hp : ∀ t, θ (t + P) = θ t + A) (n : ℕ) :
    Function.Periodic (cyclicAngleCurve θ P n) P := by
  intro t
  ext i
  exact cyclicAngleCoordinates_periodic hp i t

/-- Arbitrary cyclic shifts of angle coordinates equal time translations. -/
theorem cyclicAngleCoordinates_add_nat {θ : ℝ → ℝ} {P A : ℝ}
    (hp : ∀ t, θ (t + P) = θ t + A) {n : ℕ} (i : Fin (n + 1)) (k : ℕ) (t : ℝ) :
    cyclicAngleCoordinates θ P (n + 1) (i + (k : Fin (n + 1))) t =
      cyclicAngleCoordinates θ P (n + 1) i (t + (k : ℝ) * (P / (n + 1))) :=
  boundarySamples_add_nat (periodic_angle_difference hp) i k t

end UlamFloating
