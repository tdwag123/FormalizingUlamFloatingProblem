import UlamFloating.PolygonCentroid
import UlamFloating.CyclicMotion
import UlamFloating.FirstMoment
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-!
# Polygon moments and rigid motions recovered from edge vectors

An area-preserving linear map carries the signed centroid to the centroid
of the image polygon. Equal cyclic edges determine a polygon up to
translation. Together these facts recover the centered polygon directly
from its edges, without choosing a circumcircle or assuming regularity.
-/

namespace UlamFloating

open scoped BigOperators InnerProductSpace

/-- Rotation preserves the oriented area form in any oriented Euclidean plane. -/
theorem areaForm_rotation {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] (o : Orientation ℝ E (Fin 2))
    (a : Real.Angle) (u v : E) :
    o.areaForm (o.rotation a u) (o.rotation a v) = o.areaForm u v := by
  simp only [o.rotation_apply, map_add, LinearMap.add_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  simp only [o.areaForm_comp_rightAngleRotation, o.areaForm_rightAngleRotation_left,
    o.areaForm_rightAngleRotation_right]
  calc
    _ = (a.cos ^ 2 + a.sin ^ 2) * o.areaForm u v := by ring
    _ = _ := by rw [a.cos_sq_add_sin_sq, one_mul]

/-- Equal directed edges around a nonempty finite cycle determine all
vertices up to the translation between the initial vertices. -/
theorem eq_add_of_cyclic_edges_eq {E : Type*} [AddCommGroup E] {n : ℕ}
    (p q : Fin (n + 1) → E)
    (he : ∀ i, q (finRotate (n + 1) i) - q i = p (finRotate (n + 1) i) - p i)
    (i : Fin (n + 1)) : q i = p i + (q 0 - p 0) := by
  have hd : ∀ j, q (finRotate (n + 1) j) - p (finRotate (n + 1) j) = q j - p j := by
    intro j
    calc
      _ = (q (finRotate (n + 1) j) - q j) -
          (p (finRotate (n + 1) j) - p j) + (q j - p j) := by abel
      _ = _ := by rw [he, sub_self, zero_add]
  have h := eq_initial_of_finRotate_invariant (fun j => q j - p j) hd i
  have h' := sub_eq_iff_eq_add.mp h
  simpa only [add_comm] using h'

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Signed polygon area is preserved by any linear map preserving the
oriented area form. The successor permutation is arbitrary. -/
theorem polygonSignedArea_map {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ Plane (Fin 2)) (L : Plane →ₗ[ℝ] Plane)
    (hL : ∀ u v, o.areaForm (L u) (L v) = o.areaForm u v) (p : ι → Plane) :
    polygonSignedArea next o (fun i => L (p i)) = polygonSignedArea next o p := by
  simp only [polygonSignedArea, planeAreaForm, hL]

/-- Signed first moments commute with an area-preserving linear map. -/
theorem polygonFirstMoment_map {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ Plane (Fin 2)) (L : Plane →ₗ[ℝ] Plane)
    (hL : ∀ u v, o.areaForm (L u) (L v) = o.areaForm u v) (p : ι → Plane) :
    polygonFirstMoment next o (fun i => L (p i)) = L (polygonFirstMoment next o p) := by
  simp only [polygonFirstMoment, planeAreaForm, hL, map_smul, map_sum, map_add]

/-- Signed centroids commute with area-preserving linear maps. This
identity also holds for the totalized definition at zero signed area. -/
theorem polygonCentroid_map {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ Plane (Fin 2)) (L : Plane →ₗ[ℝ] Plane)
    (hL : ∀ u v, o.areaForm (L u) (L v) = o.areaForm u v) (p : ι → Plane) :
    polygonCentroid next o (fun i => L (p i)) = L (polygonCentroid next o p) := by
  simp only [polygonCentroid, polygonSignedArea_map next o L hL,
    polygonFirstMoment_map next o L hL, map_smul]

/-- An area-preserving linear relation between cyclic edge vectors gives
the same relation between vertices centered at their signed centroids.
Only nonzero signed area is needed, not convexity or regularity. -/
theorem sub_centroid_eq_of_edges_eq_map {n : ℕ} (p q : Fin (n + 1) → Plane)
    (o : Orientation ℝ Plane (Fin 2)) (L : Plane →ₗ[ℝ] Plane)
    (hL : ∀ u v, o.areaForm (L u) (L v) = o.areaForm u v)
    (hA : polygonSignedArea (finRotate (n + 1)) o p ≠ 0)
    (he : ∀ i, q (finRotate (n + 1) i) - q i =
      L (p (finRotate (n + 1) i) - p i)) (i : Fin (n + 1)) :
    q i - polygonCentroid (finRotate (n + 1)) o q =
      L (p i - polygonCentroid (finRotate (n + 1)) o p) := by
  have hp (j : Fin (n + 1)) : q j = L (p j) + (q 0 - L (p 0)) :=
    eq_add_of_cyclic_edges_eq (fun k => L (p k)) q
      (fun k => by simpa only [map_sub] using he k) j
  have hLA : polygonSignedArea (finRotate (n + 1)) o (fun j => L (p j)) ≠ 0 := by
    rwa [polygonSignedArea_map _ o L hL]
  have hc : polygonCentroid (finRotate (n + 1)) o q =
      L (polygonCentroid (finRotate (n + 1)) o p) + (q 0 - L (p 0)) := by
    conv_lhs => rw [show q = (fun j => L (p j) + (q 0 - L (p 0))) from funext hp]
    rw [polygonCentroid_translate _ o _ _ hLA, polygonCentroid_map _ o L hL]
  rw [hc, hp i, add_sub_add_right_eq_sub, map_sub]

/-- If two configurations of a carousel have rotated edge vectors, their
positions are related by that rotation about the conserved signed centroid. -/
theorem IsCarousel.sub_centroid_eq_of_rotated_edges {n : ℕ}
    {p : Fin (n + 1) → ℝ → Plane} {l : ℝ}
    (hc : IsCarousel (finRotate (n + 1)) p l)
    (o : Orientation ℝ Plane (Fin 2)) (a : Real.Angle) (s t : ℝ)
    (hA : polygonSignedArea (finRotate (n + 1)) o (fun i => p i t) ≠ 0)
    (he : ∀ i, p (finRotate (n + 1) i) s - p i s =
      o.rotation a (p (finRotate (n + 1) i) t - p i t)) (i : Fin (n + 1)) :
    p i s - polygonCentroid (finRotate (n + 1)) o (fun j => p j 0) =
      o.rotation a (p i t - polygonCentroid (finRotate (n + 1)) o (fun j => p j 0)) := by
  have h := sub_centroid_eq_of_edges_eq_map (fun j => p j t) (fun j => p j s) o
    (o.rotation a).toLinearEquiv.toLinearMap (areaForm_rotation o a) hA he i
  simpa only [hc.polygonCentroid_eq o s 0, hc.polygonCentroid_eq o t 0] using h

end UlamFloating
