import UlamFloating.SquareKinematics

/-!
# Square geometry along four-vertex carousels

Distinct opposite vertices yield a parallelogram at every time. Its midpoint
laws and differentiated diagonal identity force perpendicular adjacent edges
and a fixed vertex average.
-/

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- At every time, a four-vertex carousel with distinct vertices is a parallelogram. -/
theorem IsCarousel.four_parallelogram {p : Fin 4 → ℝ → E} {l : ℝ}
    (hc : IsCarousel (finRotate 4) p l) (o : Orientation ℝ E (Fin 2))
    (hinj : ∀ t, Function.Injective (fun i => p i t)) (t : ℝ) :
    p 0 t + p 2 t = p 1 t + p 3 t := by
  apply parallelogram_of_equilateral o
    ((hinj t).ne (by decide : (0 : Fin 4) ≠ 2))
    ((hinj t).ne (by decide : (1 : Fin 4) ≠ 3))
  · simpa using hc.edge_length 0 t
  · simpa using hc.edge_length 1 t
  · simpa using hc.edge_length 2 t
  · simpa using hc.edge_length 3 t

/-- The total vertex derivative vanishes in a four-vertex carousel with
distinct vertices. -/
theorem IsCarousel.sum_four_deriv_eq_zero {p : Fin 4 → ℝ → E} {l : ℝ}
    (hc : IsCarousel (finRotate 4) p l) (o : Orientation ℝ E (Fin 2))
    (hinj : ∀ t, Function.Injective (fun i => p i t)) (t : ℝ) :
    deriv (p 0) t + deriv (p 1) t + deriv (p 2) t + deriv (p 3) t = 0 := by
  have hpara := hc.four_parallelogram o hinj t
  have harea : o.areaForm (p 1 t - p 0 t) (p 2 t - p 1 t) ≠ 0 := by
    apply areaForm_ne_zero_of_parallelogram o hc.length_pos hpara
      ((hinj t).ne (by decide : (0 : Fin 4) ≠ 2))
      ((hinj t).ne (by decide : (1 : Fin 4) ≠ 3))
    · simpa using hc.edge_length 0 t
    · simpa using hc.edge_length 3 t
  have h2 : p 3 t - p 2 t = -(p 1 t - p 0 t) := by
    calc
      p 3 t - p 2 t = (p 1 t + p 3 t) - (p 1 t + p 2 t) := by abel
      _ = (p 0 t + p 2 t) - (p 1 t + p 2 t) := by rw [← hpara]
      _ = -(p 1 t - p 0 t) := by abel
  have h3 : p 0 t - p 3 t = -(p 2 t - p 1 t) := by
    calc
      p 0 t - p 3 t = (p 0 t + p 2 t) - (p 3 t + p 2 t) := by abel
      _ = (p 1 t + p 3 t) - (p 3 t + p 2 t) := by rw [hpara]
      _ = -(p 2 t - p 1 t) := by abel
  apply sum_four_velocity_eq_zero o harea
  · simpa using hc.midpoint_parallel 0 t
  · simpa using hc.midpoint_parallel 1 t
  · simpa [h2] using hc.midpoint_parallel 2 t
  · simpa [h3] using hc.midpoint_parallel 3 t

/-- The vertex sum, hence vertex average, is fixed along a four-vertex carousel. -/
theorem IsCarousel.sum_four_eq {p : Fin 4 → ℝ → E} {l : ℝ}
    (hc : IsCarousel (finRotate 4) p l) (o : Orientation ℝ E (Fin 2))
    (hinj : ∀ t, Function.Injective (fun i => p i t)) (s t : ℝ) :
    p 0 s + p 1 s + p 2 s + p 3 s = p 0 t + p 1 t + p 2 t + p 3 t := by
  have hp (i : Fin 4) (t : ℝ) : HasDerivAt (p i) (deriv (p i) t) t :=
    ((hc.contDiff i).differentiable (by simp) t).hasDerivAt
  have hd : ∀ t, HasDerivAt (fun t => p 0 t + p 1 t + p 2 t + p 3 t) 0 t := by
    intro t
    have hz := hc.sum_four_deriv_eq_zero o hinj t
    simpa only [hz] using (((hp 0 t).add (hp 1 t)).add (hp 2 t)).add (hp 3 t)
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

/-- Adjacent edges of a four-vertex carousel with distinct vertices are perpendicular. -/
theorem IsCarousel.four_edges_inner_eq_zero {p : Fin 4 → ℝ → E} {l : ℝ}
    (hc : IsCarousel (finRotate 4) p l) (o : Orientation ℝ E (Fin 2))
    (hinj : ∀ t, Function.Injective (fun i => p i t)) (t : ℝ) :
    ⟪p 1 t - p 0 t, p 2 t - p 1 t⟫_ℝ = 0 := by
  have hp (i : Fin 4) (t : ℝ) : HasDerivAt (p i) (deriv (p i) t) t :=
    ((hc.contDiff i).differentiable (by simp) t).hasDerivAt
  have hfun : (fun t => p 0 t + p 2 t) = fun t => p 1 t + p 3 t :=
    funext (hc.four_parallelogram o hinj)
  have hd := (hp 0 t).add (hp 2 t)
  change HasDerivAt (fun t => p 0 t + p 2 t) _ t at hd
  rw [hfun] at hd
  have hdiag := hd.unique ((hp 1 t).add (hp 3 t))
  apply inner_edges_eq_zero_of_carousel_laws (hc.regular 0 t)
    (hc.sum_four_deriv_eq_zero o hinj t) hdiag
  · apply inner_edge_velocity_eq_zero (hp 0 t) (hp 1 t)
    simpa using hc.edge_length 0
  · apply inner_edge_velocity_eq_zero (hp 1 t) (hp 2 t)
    simpa using hc.edge_length 1
  · simpa using hc.midpoint_parallel 0 t
  · simpa using hc.midpoint_parallel 1 t

end UlamFloating
