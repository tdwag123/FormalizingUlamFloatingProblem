import UlamFloating.ChordWinding

/-!
# Periodic cyclic angle coordinates

From a real lift of the directed chord angle, take pi minus its change
over one sampling interval. These coordinates are periodic and transform
under cyclic index rotation by a time shift. Their sum is obtained by
telescoping. Positivity and the pentagon differential equation are separate
geometric assertions, not hypotheses hidden in this definition.
-/

noncomputable section

namespace UlamFloating

open scoped BigOperators

/-- Pi minus the direction change between consecutive sampled chords.
The coordinate at index `i` corresponds to the shared vertex `i+1`.
Geometric applications separately identify it with an interior angle. -/
def cyclicAngleCoordinates (θ : ℝ → ℝ) (P : ℝ) (n : ℕ) : Fin n → ℝ → ℝ :=
  boundarySamples (fun t => Real.pi + θ t - θ (t + P / n)) P n

/-- Subtracting a translated real angle cancels any fixed angular increment
over a period. -/
theorem periodic_angle_difference {θ : ℝ → ℝ} {P A h : ℝ}
    (hp : ∀ t, θ (t + P) = θ t + A) :
    Function.Periodic (fun t => Real.pi + θ t - θ (t + h)) P := by
  intro t
  dsimp only
  rw [show t + P + h = (t + h) + P by ring, hp, hp]
  ring

/-- Cyclic angle coordinates inherit `C¹` regularity from their real angle lift. -/
theorem cyclicAngleCoordinates_contDiff {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ)
    (P : ℝ) {n : ℕ} (i : Fin n) : ContDiff ℝ 1 (cyclicAngleCoordinates θ P n i) := by
  have hbase : ContDiff ℝ 1 (fun t => Real.pi + θ t - θ (t + P / n)) :=
    (contDiff_const.add hθ).sub (hθ.comp (contDiff_id.add contDiff_const))
  exact hbase.comp (contDiff_id.add contDiff_const)

/-- Each cyclic angle coordinate is periodic even though its real angle lift
increases by a nonzero amount over one period. -/
theorem cyclicAngleCoordinates_periodic {θ : ℝ → ℝ} {P A : ℝ}
    (hp : ∀ t, θ (t + P) = θ t + A) {n : ℕ} (i : Fin n) :
    Function.Periodic (cyclicAngleCoordinates θ P n i) P := by
  intro t
  have h := periodic_angle_difference (h := P / n) hp (t + (i.val : ℝ) * (P / n))
  simpa only [cyclicAngleCoordinates, boundarySamples, sampledVertex,
    add_assoc, add_left_comm, add_comm] using h

/-- Rotating the finite angle index is the same as advancing by one
sampling interval, including the last-to-first wrap. -/
theorem cyclicAngleCoordinates_rotate {θ : ℝ → ℝ} {P A : ℝ}
    (hp : ∀ t, θ (t + P) = θ t + A) {n : ℕ} (i : Fin n) (t : ℝ) :
    cyclicAngleCoordinates θ P n (finRotate n i) t =
      cyclicAngleCoordinates θ P n i (t + P / n) :=
  boundarySamples_rotate (periodic_angle_difference hp) i t

/-- The cyclic angle sum is `nπ` minus the total angular increment.
For a once-turning lift this is `(n-2)π`; in particular it is `3π` for five samples. -/
theorem cyclicAngleCoordinates_sum {θ : ℝ → ℝ} {P A : ℝ}
    (hp : ∀ t, θ (t + P) = θ t + A) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    ∑ i, cyclicAngleCoordinates θ P n i t = (n : ℝ) * Real.pi - A := by
  let f : ℕ → ℝ := fun i => θ (t + (i : ℝ) * (P / n))
  have htel : (∑ i : Fin n, (f i.val - f (i.val + 1))) = f 0 - f n := by
    simpa only [Finset.sum_range] using Finset.sum_range_sub' f n
  have heq (i : Fin n) : cyclicAngleCoordinates θ P n i t =
      Real.pi + (f i.val - f (i.val + 1)) := by
    dsimp [cyclicAngleCoordinates, boundarySamples, sampledVertex, f]
    rw [show t + ((i.val + 1 : ℕ) : ℝ) * (P / n) =
      t + (i.val : ℝ) * (P / n) + P / n by push_cast; ring]
    ring
  simp_rw [heq]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, htel]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hfn : f n = θ t + A := by
    dsimp [f]
    rw [show (n : ℝ) * (P / n) = P by field_simp, hp]
  rw [hfn]
  simp only [f, Nat.cast_zero, zero_mul, add_zero]
  ring

end UlamFloating
