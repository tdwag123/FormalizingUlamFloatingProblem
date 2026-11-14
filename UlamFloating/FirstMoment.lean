import UlamFloating.MomentConservation

/-!
# First-moment and centroid conservation for planar carousels

The invariant is the signed area moment, not the average of the vertices.
Identification with the centroid of the polygon's interior is a separate theorem.
-/

namespace UlamFloating

open scoped BigOperators InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- The first-moment derivative cancels for equal-length edges satisfying
the two local carousel laws. -/
theorem sum_moment_rate_eq_zero {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ E (Fin 2)) (p v : ι → E) (l : ℝ)
    (hlen : ∀ i, ‖p (next i) - p i‖ = l)
    (horth : ∀ i, ⟪p (next i) - p i, v (next i) - v i⟫_ℝ = 0)
    (hmid : ∀ i, ∃ a : ℝ, v i + v (next i) = a • (p (next i) - p i)) :
    ∑ i, ((o.areaForm (v i) (p (next i)) + o.areaForm (p i) (v (next i))) •
      (p i + p (next i)) + o.areaForm (p i) (p (next i)) • (v i + v (next i))) = 0 := by
  let F : ι → E := fun i =>
    (2 * o.areaForm (v i) (p i)) • p i - (l ^ 2 / 2) • o.rightAngleRotation (v i)
  have hedge : ∀ i,
      (o.areaForm (v i) (p (next i)) + o.areaForm (p i) (v (next i))) •
        (p i + p (next i)) + o.areaForm (p i) (p (next i)) • (v i + v (next i)) =
        F i - F (next i) := by
    intro i
    rw [moment_edge_rate o (hmid i),
      areaForm_smul_eq_velocity_difference o (horth i) (hmid i), hlen i]
    dsimp [F]
    module
  simp_rw [hedge]
  rw [Finset.sum_sub_distrib, Equiv.sum_comp next F]
  exact sub_self _

/-- The unnormalized signed first moment is constant along any planar carousel.
This form works on every oriented two-dimensional real inner product space. -/
theorem IsCarousel.sum_areaForm_smul_eq {ι : Type*} [Fintype ι]
    {next : Equiv.Perm ι} {p : ι → ℝ → E} {l : ℝ}
    (hc : IsCarousel next p l) (o : Orientation ℝ E (Fin 2)) (s t : ℝ) :
    ∑ i, o.areaForm (p i s) (p (next i) s) • (p i s + p (next i) s) =
      ∑ i, o.areaForm (p i t) (p (next i) t) • (p i t + p (next i) t) := by
  have hp (i : ι) (t : ℝ) : HasDerivAt (p i) (deriv (p i) t) t :=
    ((hc.contDiff i).differentiable (by simp) t).hasDerivAt
  have hd : ∀ t, HasDerivAt
      (fun t => ∑ i, o.areaForm (p i t) (p (next i) t) • (p i t + p (next i) t)) 0 t := by
    intro t
    have hedge (i : ι) := (o.areaForm'.hasDerivAt_of_bilinear
      (hp i t) (hp (next i) t)).fun_smul ((hp i t).add (hp (next i) t))
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hedge i)
    have hz := sum_moment_rate_eq_zero next o (fun i => p i t)
      (fun i => deriv (p i) t) l (fun i => hc.edge_length i t)
      (fun i => inner_edge_velocity_eq_zero (hp i t) (hp (next i) t)
        (hc.edge_length i)) (fun i => hc.midpoint_parallel i t)
    have hsum' : HasDerivAt
        (fun t => ∑ i, o.areaForm (p i t) (p (next i) t) • (p i t + p (next i) t))
        (∑ i, ((o.areaForm (deriv (p i) t) (p (next i) t) +
          o.areaForm (p i t) (deriv (p (next i)) t)) • (p i t + p (next i) t) +
          o.areaForm (p i t) (p (next i) t) • (deriv (p i) t + deriv (p (next i)) t))) t := by
      simpa only [Orientation.areaForm'_apply, add_comm] using hsum
    rw [hz] at hsum'
    exact hsum'
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The signed first moment of a finite planar carousel is constant in time. -/
theorem IsCarousel.polygonFirstMoment_eq {ι : Type*} [Fintype ι]
    {next : Equiv.Perm ι} {p : ι → ℝ → Plane} {l : ℝ}
    (hc : IsCarousel next p l) (o : Orientation ℝ Plane (Fin 2)) (s t : ℝ) :
    polygonFirstMoment next o (fun i => p i s) =
      polygonFirstMoment next o (fun i => p i t) := by
  exact congrArg (fun a : Plane => (1 / 6 : ℝ) • a) (hc.sum_areaForm_smul_eq o s t)

/-- Constancy of the signed centroid. The identity also holds for zero signed
area under the totalized definition; geometric use requires nonzero area. -/
theorem IsCarousel.polygonCentroid_eq {ι : Type*} [Fintype ι]
    {next : Equiv.Perm ι} {p : ι → ℝ → Plane} {l : ℝ}
    (hc : IsCarousel next p l) (o : Orientation ℝ Plane (Fin 2)) (s t : ℝ) :
    polygonCentroid next o (fun i => p i s) =
      polygonCentroid next o (fun i => p i t) := by
  unfold polygonCentroid
  rw [hc.polygonSignedArea_eq o s t, hc.polygonFirstMoment_eq o s t]

/-- Discharges the first-moment conservation specification. -/
theorem carousel_firstMoment : carouselFirstMomentStatement := by
  intro n next p l hc o s t
  exact hc.polygonFirstMoment_eq o s t

/-- Discharges the fixed signed-centroid specification. -/
theorem carousel_centroid : carouselCentroidStatement := by
  intro n next p l hc o _ s t
  exact hc.polygonCentroid_eq o s t

end UlamFloating
