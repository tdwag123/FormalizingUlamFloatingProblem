import UlamFloating.Extraction
import UlamFloating.Triangle

/-!
# Equilateral quadrilateral geometry

Four equilateral edges with distinct opposite vertices form a parallelogram.
The proof uses perpendicular bisectors and works without assuming polygon order.
These are the geometric inputs for the four-vertex carousel reduction.
-/

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The perpendicular-bisector identity, with a midpoint expressed by vectors. -/
theorem inner_sub_midpoint (a b c : E) :
    ⟪c - a, b - (1 / 2 : ℝ) • (a + c)⟫_ℝ =
      (‖b - a‖ ^ 2 - ‖b - c‖ ^ 2) / 2 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_right, real_inner_smul_right,
    real_inner_comm a b, real_inner_comm a c, real_inner_comm b c]
  ring

/-- Squared distance to the midpoint in terms of the three squared distances. -/
theorem norm_sub_midpoint_sq (a b c : E) :
    ‖b - (1 / 2 : ℝ) • (a + c)‖ ^ 2 =
      (‖b - a‖ ^ 2 + ‖b - c‖ ^ 2) / 2 - ‖c - a‖ ^ 2 / 4 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm a b, real_inner_comm a c, real_inner_comm b c]
  ring

/-- Parallel vectors of equal norm are equal or opposite. -/
theorem eq_or_eq_neg_of_norm_eq_of_smul {x y : E} {k : ℝ}
    (hnorm : ‖y‖ = ‖x‖) (hrep : y = k • x) : y = x ∨ y = -x := by
  by_cases hx : x = 0
  · left
    simpa [hx] using hrep
  rw [hrep, norm_smul, Real.norm_eq_abs] at hnorm
  have habs : |k| = 1 := mul_right_cancel₀ (norm_ne_zero_iff.mpr hx)
    (hnorm.trans (one_mul ‖x‖).symm)
  have hk : k ^ 2 = 1 := by nlinarith [sq_abs k]
  rcases sq_eq_one_iff.mp hk with hk | hk
  · left
    simpa only [hk, one_smul] using hrep
  · right
    simpa only [hk, neg_one_smul] using hrep

variable [Fact (Module.finrank ℝ E = 2)]

/-- A planar equilateral quadrilateral with distinct opposite vertices is a
parallelogram. Cyclic order and convexity need not be assumed. -/
theorem parallelogram_of_equilateral (o : Orientation ℝ E (Fin 2))
    {a b c d : E} {l : ℝ} (hac : a ≠ c) (hbd : b ≠ d)
    (hba : ‖b - a‖ = l) (hcb : ‖c - b‖ = l)
    (hdc : ‖d - c‖ = l) (had : ‖a - d‖ = l) : a + c = b + d := by
  let m := (1 / 2 : ℝ) • (a + c)
  let x := b - m
  let y := d - m
  have hbc : ‖b - c‖ = l := by rwa [norm_sub_rev]
  have hda : ‖d - a‖ = l := by rwa [norm_sub_rev]
  have horthx : ⟪c - a, x⟫_ℝ = 0 := by
    dsimp [x, m]
    rw [inner_sub_midpoint, hba, hbc]
    ring
  have horthy : ⟪c - a, y⟫_ℝ = 0 := by
    dsimp [y, m]
    rw [inner_sub_midpoint, hda, hdc]
    ring
  have hnx : ‖x‖ ^ 2 = l ^ 2 - ‖c - a‖ ^ 2 / 4 := by
    dsimp [x, m]
    rw [norm_sub_midpoint_sq, hba, hbc]
    ring
  have hny : ‖y‖ ^ 2 = l ^ 2 - ‖c - a‖ ^ 2 / 4 := by
    dsimp [y, m]
    rw [norm_sub_midpoint_sq, hda, hdc]
    ring
  have hnorm : ‖y‖ = ‖x‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
  have hxy : y ≠ x := by
    intro heq
    have hdb : d = b := by simpa [x, y] using congrArg (fun z => z + m) heq
    exact hbd hdb.symm
  have hx : x ≠ 0 := by
    intro hx
    have hy : y = 0 := norm_eq_zero.mp (by simpa only [hx, norm_zero] using hnorm)
    exact hxy (hy.trans hx.symm)
  obtain ⟨k, hrep⟩ := exists_smul_of_inner_eq_zero o hx
    (sub_ne_zero.mpr hac.symm) horthx horthy
  have hyx : y = -x := (eq_or_eq_neg_of_norm_eq_of_smul hnorm hrep).resolve_left hxy
  have hd : d = -(b - m) + m := (sub_eq_iff_eq_add).mp hyx
  rw [hd]
  dsimp [m]
  module

end UlamFloating
