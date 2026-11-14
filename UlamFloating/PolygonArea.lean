import UlamFloating.Geometry

/-!
# Nonzero signed area of strictly convex polygons

The shoelace sum can be computed using displacements from any origin. With
the origin at a vertex of a strictly convex polygon, every edge contributes
nonnegatively, and an edge not incident to that vertex contributes positively.
This proves nonvanishing without any integration or centroid identification.
-/

namespace UlamFloating

open scoped BigOperators

/-- A skew-bilinear polygon sum equals the sum of the oriented edge triangles
from any chosen origin. The identity is independent of dimension and ordering. -/
theorem sum_bilinear_edge_origin {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) (hskew : ∀ x y, B x y = -B y x)
    (p : ι → E) (c : E) :
    ∑ i, B (p (next i) - p i) (c - p i) = ∑ i, B (p i) (p (next i)) := by
  have hdiag (x : E) : B x x = 0 := by have := hskew x x; linarith
  have hedge (i : ι) : B (p (next i) - p i) (c - p i) =
      (B (p (next i)) c - B (p i) c) + B (p i) (p (next i)) := by
    simp only [map_sub, LinearMap.sub_apply, hdiag, hskew (p (next i)) (p i)]
    ring
  simp_rw [hedge]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Equiv.sum_comp next (fun i => B (p i) c), sub_self, zero_add]

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Reversing orientation negates polygonal signed area. -/
theorem polygonSignedArea_neg_orientation {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (o : Orientation ℝ Plane (Fin 2)) (p : ι → Plane) :
    polygonSignedArea next (-o) p = -polygonSignedArea next o p := by
  simp [polygonSignedArea, planeAreaForm, Orientation.areaForm_neg_orientation,
    Finset.sum_neg_distrib]

/-- Strict edge-side inequalities make the signed area positive in that
orientation. This only uses the polygon's cyclic side inequalities. -/
theorem polygonSignedArea_pos_of_edge_sides {n : ℕ} (hn : 3 ≤ n)
    (p : Fin n → Plane) (o : Orientation ℝ Plane (Fin 2))
    (ho : ∀ i j, j ≠ i → j ≠ finRotate n i →
      0 < o.areaForm (p (finRotate n i) - p i) (p j - p i)) :
    0 < polygonSignedArea (finRotate n) o p := by
  cases n with
  | zero => omega
  | succ m =>
    let z : Fin (m + 1) := ⟨0, by omega⟩
    let k : Fin (m + 1) := ⟨1, by omega⟩
    have hsum : 0 < ∑ i, o.areaForm (p (finRotate (m + 1) i) - p i) (p z - p i) := by
      apply Finset.sum_pos'
      · intro i _
        by_cases hi : z = i
        · rw [hi, sub_self, map_zero]
        by_cases hnext : z = finRotate (m + 1) i
        · rw [hnext, o.areaForm_apply_self]
        exact (ho i z hi hnext).le
      · refine ⟨k, Finset.mem_univ _, ho k z ?_ ?_⟩
        · intro h
          have := congrArg Fin.val h
          norm_num [z, k] at this
        · have hrot : finRotate (m + 1) k = ⟨2, by omega⟩ := finRotate_of_lt (by omega)
          rw [hrot]
          intro h
          have := congrArg Fin.val h
          norm_num [z] at this
    rw [sum_bilinear_edge_origin (finRotate (m + 1)) o.areaForm o.areaForm_swap p (p z)] at hsum
    exact mul_pos (by norm_num : (0 : ℝ) < 1 / 2) hsum

/-- A strictly convex polygon has nonzero signed area in either orientation. -/
theorem IsStrictlyConvexPolygon.polygonSignedArea_ne_zero {n : ℕ} {p : Fin n → Plane}
    (hp : IsStrictlyConvexPolygon p) (o : Orientation ℝ Plane (Fin 2)) :
    polygonSignedArea (finRotate n) o p ≠ 0 := by
  obtain ⟨hn, _, o', ho'⟩ := hp
  have hpos := polygonSignedArea_pos_of_edge_sides hn p o' ho'
  rcases o.eq_or_eq_neg o' (by simp [Plane]) with rfl | rfl
  · exact hpos.ne'
  · rw [polygonSignedArea_neg_orientation]
    exact neg_ne_zero.mpr hpos.ne'

end UlamFloating
