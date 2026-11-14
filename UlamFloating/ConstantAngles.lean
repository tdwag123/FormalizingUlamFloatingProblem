import UlamFloating.SampledAngleCurve

/-!
# Constant sampled-angle curves

Time constancy of the sampled vector forces all its coordinates to agree.
A prescribed total turn then determines the common chord increment.
These facts use only sampling and finite sums, not boundary geometry.
-/

namespace UlamFloating

open scoped BigOperators

/-- If a sampled-angle curve is constant in time, every coordinate equals
the initial zero coordinate, because sampling is translation in time. -/
theorem cyclicAngleCoordinates_eq_initial_of_constant {θ : ℝ → ℝ} {P : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hconst : ∃ c, ∀ t, cyclicAngleCurve θ P n t = c)
    (i : Fin n) (t : ℝ) :
    cyclicAngleCoordinates θ P n i t =
      cyclicAngleCoordinates θ P n ⟨0, Nat.pos_of_ne_zero hn⟩ 0 := by
  obtain ⟨c, hc⟩ := hconst
  have he := congrArg (fun z : EuclideanSpace ℝ (Fin n) => z ⟨0, Nat.pos_of_ne_zero hn⟩)
    ((hc (t + (i.val : ℝ) * (P / n))).trans (hc 0).symm)
  simpa only [cyclicAngleCurve, PiLp.toLp_apply, cyclicAngleCoordinates,
    boundarySamples, sampledVertex, Nat.cast_zero, zero_mul, add_zero, zero_add] using he

/-- A constant sampled-angle curve with total angular increment `A` has
chord increments exactly `A/n`, for any nonempty sampling cycle. -/
theorem angle_increment_eq_of_constant_cyclic_curve {θ : ℝ → ℝ} {P A : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hp : ∀ t, θ (t + P) = θ t + A)
    (hconst : ∃ c, ∀ t, cyclicAngleCurve θ P n t = c) (t : ℝ) :
    θ (t + P / n) - θ t = A / n := by
  let z : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hall := cyclicAngleCoordinates_eq_initial_of_constant hn hconst
  have hs := cyclicAngleCoordinates_sum hp hn 0
  simp_rw [hall] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hz := hall z t
  dsimp [cyclicAngleCoordinates, boundarySamples, sampledVertex, z] at hs hz
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add] at hs hz
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  apply (eq_div_iff hnR).mpr
  nlinarith

/-- The constant sampled-angle vector is determined by its total angular
increment: every coordinate is `π - A/n`. -/
theorem cyclicAngleCoordinates_value_of_constant {θ : ℝ → ℝ} {P A : ℝ} {n : ℕ}
    (hn : n ≠ 0) (hp : ∀ t, θ (t + P) = θ t + A)
    (hconst : ∃ c, ∀ t, cyclicAngleCurve θ P n t = c) (i : Fin n) (t : ℝ) :
    cyclicAngleCoordinates θ P n i t = Real.pi - A / n := by
  have h := angle_increment_eq_of_constant_cyclic_curve hn hp hconst
    (t + (i.val : ℝ) * (P / n))
  dsimp [cyclicAngleCoordinates, boundarySamples, sampledVertex]
  linarith

end UlamFloating
