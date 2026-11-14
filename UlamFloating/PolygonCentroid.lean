import UlamFloating.PolygonArea
import UlamFloating.MomentConservation

/-!
# Translation of polygon moments and centers of equilateral cyclic polygons

The algebraic centroid agrees with the circumcenter for every equilateral
cyclic polygon of nonzero signed area. The finite-sum arguments allow any
successor permutation and do not use integration over the polygon interior.
-/

namespace UlamFloating

open scoped BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- The alternating three-vector identity in an oriented Euclidean plane. -/
theorem areaForm_smul_three (o : Orientation ℝ E (Fin 2)) (a b c : E) :
    o.areaForm a b • c = o.areaForm a c • b + o.areaForm c b • a := by
  by_cases ha : a = 0
  · simp [ha]
  have hb := (o.basisRightAngleRotation a ha).sum_repr b
  have hc := (o.basisRightAngleRotation a ha).sum_repr c
  simp only [Fin.sum_univ_two, o.coe_basisRightAngleRotation,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hb hc
  rw [← hb, ← hc]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul, o.areaForm_apply_self, o.areaForm_rightAngleRotation_right,
    o.areaForm_rightAngleRotation_left, real_inner_self_eq_norm_sq]
  module

/-- Translating all vertices leaves a skew-bilinear polygon sum unchanged. -/
theorem sum_areaForm_translate {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ E (Fin 2)) (p : ι → E) (c : E) :
    ∑ i, o.areaForm (p i + c) (p (next i) + c) =
      ∑ i, o.areaForm (p i) (p (next i)) := by
  have hedge (i : ι) : o.areaForm (p i + c) (p (next i) + c) =
      o.areaForm (p i) (p (next i)) +
        (o.areaForm (p i) c - o.areaForm (p (next i)) c) := by
    simp only [map_add, LinearMap.add_apply, o.areaForm_apply_self,
      o.areaForm_swap c (p (next i))]
    ring
  simp_rw [hedge]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Equiv.sum_comp next (fun i => o.areaForm (p i) c), sub_self, add_zero]

/-- Translation changes the unnormalized first moment by three times the
shoelace sum times the translation vector. -/
theorem sum_moment_translate {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ E (Fin 2)) (p : ι → E) (c : E) :
    ∑ i, o.areaForm (p i + c) (p (next i) + c) •
        ((p i + c) + (p (next i) + c)) =
      (∑ i, o.areaForm (p i) (p (next i)) • (p i + p (next i))) +
        (3 * ∑ i, o.areaForm (p i) (p (next i))) • c := by
  let F : ι → E := fun i => o.areaForm (p i) c • (p i + (2 : ℝ) • c)
  have hedge (i : ι) :
      o.areaForm (p i + c) (p (next i) + c) •
          ((p i + c) + (p (next i) + c)) =
        o.areaForm (p i) (p (next i)) • (p i + p (next i)) +
          (3 * o.areaForm (p i) (p (next i))) • c + (F i - F (next i)) := by
    have h := areaForm_smul_three o (p i) (p (next i)) c
    rw [o.areaForm_swap c (p (next i))] at h
    simp only [map_add, LinearMap.add_apply, o.areaForm_apply_self,
      o.areaForm_swap c (p (next i))]
    dsimp [F]
    calc
      _ = o.areaForm (p i) (p (next i)) • (p i + p (next i)) +
          (2 * o.areaForm (p i) (p (next i))) • c +
          (o.areaForm (p i) c • p (next i) +
            -(o.areaForm (p (next i)) c) • p i) +
          (o.areaForm (p i) c • (p i + (2 : ℝ) • c) -
            o.areaForm (p (next i)) c • (p (next i) + (2 : ℝ) • c)) := by module
      _ = _ := by rw [← h]; module
  simp_rw [hedge]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Equiv.sum_comp next F,
    sub_self, add_zero, Finset.sum_add_distrib, ← Finset.sum_smul, ← Finset.mul_sum]

/-- An equal-radius edge contributes a rotated edge vector to the first
moment. With fixed radius and edge length, its coefficient is constant. -/
theorem areaForm_smul_add_of_norm_sq_eq (o : Orientation ℝ E (Fin 2))
    {a b : E} {R l : ℝ} (ha : ‖a‖ ^ 2 = R) (hb : ‖b‖ ^ 2 = R)
    (he : ‖b - a‖ = l) :
    o.areaForm a b • (a + b) =
      (2 * R - l ^ 2 / 2) • (o.rightAngleRotation a - o.rightAngleRotation b) := by
  have hi : ⟪a, b⟫_ℝ = R - l ^ 2 / 2 := by
    have h := norm_sub_sq_real b a
    rw [he, ha, hb, ← real_inner_comm b a] at h
    linarith
  have h1 := areaForm_smul_eq_rotation o b a
  rw [o.areaForm_swap b a, neg_smul] at h1
  have h1' : o.areaForm a b • a =
      -(‖a‖ ^ 2 • o.rightAngleRotation b - ⟪a, b⟫_ℝ • o.rightAngleRotation a) :=
    neg_eq_iff_eq_neg.mp h1
  rw [smul_add, h1', areaForm_smul_eq_rotation o a b, ha, hb,
    ← real_inner_comm b a, hi]
  module

/-- The first moment about the common center vanishes for equal-radius,
equal-edge polygons, with any finite successor permutation. -/
theorem sum_moment_eq_zero_of_norm_sq_eq {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (o : Orientation ℝ E (Fin 2))
    (p : ι → E) {R l : ℝ} (hr : ∀ i, ‖p i‖ ^ 2 = R)
    (he : ∀ i, ‖p (next i) - p i‖ = l) :
    ∑ i, o.areaForm (p i) (p (next i)) • (p i + p (next i)) = 0 := by
  simp_rw [areaForm_smul_add_of_norm_sq_eq o (hr _) (hr _) (he _)]
  rw [← Finset.smul_sum, Finset.sum_sub_distrib,
    Equiv.sum_comp next (fun i => o.rightAngleRotation (p i)), sub_self, smul_zero]

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Signed polygon area is invariant under translation. -/
theorem polygonSignedArea_translate {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ Plane (Fin 2)) (p : ι → Plane) (c : Plane) :
    polygonSignedArea next o (fun i => p i + c) = polygonSignedArea next o p := by
  unfold polygonSignedArea planeAreaForm
  rw [sum_areaForm_translate]

/-- Translating a polygon adds area times displacement to its first moment. -/
theorem polygonFirstMoment_translate {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ Plane (Fin 2)) (p : ι → Plane) (c : Plane) :
    polygonFirstMoment next o (fun i => p i + c) =
      polygonFirstMoment next o p + polygonSignedArea next o p • c := by
  unfold polygonFirstMoment polygonSignedArea planeAreaForm
  rw [sum_moment_translate]
  module

/-- The signed centroid of a polygon with nonzero area translates with it. -/
theorem polygonCentroid_translate {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ Plane (Fin 2)) (p : ι → Plane) (c : Plane)
    (hA : polygonSignedArea next o p ≠ 0) :
    polygonCentroid next o (fun i => p i + c) = polygonCentroid next o p + c := by
  unfold polygonCentroid
  rw [polygonSignedArea_translate, polygonFirstMoment_translate, smul_add,
    smul_smul, inv_mul_cancel₀ hA, one_smul]

/-- For an equilateral cyclic polygon of nonzero signed area, the algebraic
centroid is its circumcenter. No convexity or regular labeling is required. -/
theorem polygonCentroid_eq_of_equidistant {ι : Type*} [Fintype ι]
    (next : Equiv.Perm ι) (o : Orientation ℝ Plane (Fin 2))
    (p : ι → Plane) (c : Plane) {R l : ℝ}
    (hr : ∀ i, ‖p i - c‖ ^ 2 = R) (he : ∀ i, ‖p (next i) - p i‖ = l)
    (hA : polygonSignedArea next o p ≠ 0) : polygonCentroid next o p = c := by
  let q : ι → Plane := fun i => p i - c
  have hp : (fun i => q i + c) = p := by funext i; simp [q]
  have hqA : polygonSignedArea next o q ≠ 0 := by
    rwa [← polygonSignedArea_translate next o q c, hp]
  have hqM : polygonFirstMoment next o q = 0 := by
    unfold polygonFirstMoment planeAreaForm
    rw [sum_moment_eq_zero_of_norm_sq_eq next o q hr (fun i => by
      simpa only [q, sub_sub_sub_cancel_right] using he i), smul_zero]
  have hqC : polygonCentroid next o q = 0 := by
    simp only [polygonCentroid, hqM, smul_zero]
  rw [← hp, polygonCentroid_translate next o q c hqA, hqC, zero_add]

end UlamFloating
