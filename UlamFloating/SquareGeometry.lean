import UlamFloating.SquareCarousel

/-!
# Radius and complete distance formula for squares

The algebraic square data are a parallelogram identity, two equal adjacent
lengths, and perpendicular adjacent edges. We recover both the circumradius
and the full cyclic distance formula used by `IsRegularPolygon`.
-/

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every vertex of a square lies at squared distance `l²/2` from its average. -/
theorem square_norm_sub_average_sq {p : Fin 4 → E} {l : ℝ}
    (hpara : p 0 + p 2 = p 1 + p 3) (horth : ⟪p 1 - p 0, p 2 - p 1⟫_ℝ = 0)
    (h01 : ‖p 1 - p 0‖ = l) (h12 : ‖p 2 - p 1‖ = l) (i : Fin 4) :
    ‖p i - (1 / 4 : ℝ) • (p 0 + p 1 + p 2 + p 3)‖ ^ 2 = l ^ 2 / 2 := by
  have hm : (1 / 4 : ℝ) • (p 0 + p 1 + p 2 + p 3) =
      (1 / 2 : ℝ) • (p 0 + p 2) := by
    calc
      _ = (1 / 4 : ℝ) • ((p 0 + p 2) + (p 1 + p 3)) := by congr 1; abel
      _ = _ := by rw [← hpara]; module
  have h3 : p 3 = p 0 + p 2 - p 1 := by
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using hpara.symm
  have hsum : ‖(p 1 - p 0) + (p 2 - p 1)‖ ^ 2 = 2 * l ^ 2 := by
    rw [norm_add_sq_real, horth, h01, h12]
    ring
  have hdiff : ‖(p 1 - p 0) - (p 2 - p 1)‖ ^ 2 = 2 * l ^ 2 := by
    rw [norm_sub_sq_real, horth, h01, h12]
    ring
  have hplus : ‖(1 / 2 : ℝ) • ((p 1 - p 0) + (p 2 - p 1))‖ ^ 2 = l ^ 2 / 2 := by
    rw [norm_smul, mul_pow, hsum]
    norm_num
    ring
  have hminus : ‖(1 / 2 : ℝ) • ((p 1 - p 0) - (p 2 - p 1))‖ ^ 2 = l ^ 2 / 2 := by
    rw [norm_smul, mul_pow, hdiff]
    norm_num
    ring
  rw [hm]
  fin_cases i
  · change ‖p 0 - (1 / 2 : ℝ) • (p 0 + p 2)‖ ^ 2 = l ^ 2 / 2
    rw [show p 0 - (1 / 2 : ℝ) • (p 0 + p 2) =
      -((1 / 2 : ℝ) • ((p 1 - p 0) + (p 2 - p 1))) by module, norm_neg]
    exact hplus
  · change ‖p 1 - (1 / 2 : ℝ) • (p 0 + p 2)‖ ^ 2 = l ^ 2 / 2
    rw [show p 1 - (1 / 2 : ℝ) • (p 0 + p 2) =
      (1 / 2 : ℝ) • ((p 1 - p 0) - (p 2 - p 1)) by module]
    exact hminus
  · change ‖p 2 - (1 / 2 : ℝ) • (p 0 + p 2)‖ ^ 2 = l ^ 2 / 2
    rw [show p 2 - (1 / 2 : ℝ) • (p 0 + p 2) =
      (1 / 2 : ℝ) • ((p 1 - p 0) + (p 2 - p 1)) by module]
    exact hplus
  · change ‖p 3 - (1 / 2 : ℝ) • (p 0 + p 2)‖ ^ 2 = l ^ 2 / 2
    rw [h3]
    rw [show p 0 + p 2 - p 1 - (1 / 2 : ℝ) • (p 0 + p 2) =
      -((1 / 2 : ℝ) • ((p 1 - p 0) - (p 2 - p 1))) by module, norm_neg]
    exact hminus

/-- The squared-distance table of a square: zero, one side squared, or one
diagonal squared. Distinct indices of the same parity are opposite vertices. -/
theorem square_distance_sq {p : Fin 4 → E} {l : ℝ}
    (hpara : p 0 + p 2 = p 1 + p 3) (horth : ⟪p 1 - p 0, p 2 - p 1⟫_ℝ = 0)
    (h01 : ‖p 1 - p 0‖ = l) (h12 : ‖p 2 - p 1‖ = l) (i j : Fin 4) :
    ‖p i - p j‖ ^ 2 =
      if i = j then 0 else if (i.val + j.val) % 2 = 0 then 2 * l ^ 2 else l ^ 2 := by
  have h3 : p 3 = p 0 + p 2 - p 1 := by
    apply (eq_sub_iff_add_eq).mpr
    simpa only [add_comm] using hpara.symm
  have h23 : ‖p 3 - p 2‖ = l := by
    rw [h3, show p 0 + p 2 - p 1 - p 2 = -(p 1 - p 0) by abel, norm_neg, h01]
  have h30 : ‖p 0 - p 3‖ = l := by
    rw [h3, show p 0 - (p 0 + p 2 - p 1) = -(p 2 - p 1) by abel, norm_neg, h12]
  have h02 : ‖p 0 - p 2‖ ^ 2 = 2 * l ^ 2 := by
    rw [norm_sub_rev (p 0) (p 2),
      show p 2 - p 0 = (p 1 - p 0) + (p 2 - p 1) by abel,
      norm_add_sq_real, horth, h01, h12]
    ring
  have h13 : ‖p 1 - p 3‖ ^ 2 = 2 * l ^ 2 := by
    rw [h3, show p 1 - (p 0 + p 2 - p 1) = (p 1 - p 0) - (p 2 - p 1) by abel,
      norm_sub_sq_real, horth, h01, h12]
    ring
  have h12_rev : ‖p 1 - p 2‖ = l := by rwa [norm_sub_rev]
  have h23_rev : ‖p 2 - p 3‖ = l := by rwa [norm_sub_rev]
  fin_cases i <;> fin_cases j <;>
    simp [h01, h12, h23, h30, h02, h13, h12_rev, h23_rev, norm_sub_rev]

/-- The trigonometric four-vertex distance table in cyclic order. -/
theorem square_cosine_table (i j : Fin 4) :
    1 - Real.cos (2 * Real.pi * ((i.val : ℝ) - j.val) / 4) =
      if i = j then 0 else if (i.val + j.val) % 2 = 0 then 2 else 1 := by
  have h1 : Real.cos (Real.pi * (1 / 2)) = 0 := by
    simpa only [div_eq_mul_inv, one_mul] using Real.cos_pi_div_two
  have h3 : Real.cos (Real.pi * (3 / 2)) = 0 := by
    rw [show Real.pi * (3 / 2) = Real.pi / 2 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_two, neg_zero]
  have hn1 : Real.cos (Real.pi * (-1 / 2)) = 0 := by
    rw [show Real.pi * (-1 / 2) = -(Real.pi * (1 / 2)) by ring, Real.cos_neg, h1]
  have hn3 : Real.cos (Real.pi * (-3 / 2)) = 0 := by
    rw [show Real.pi * (-3 / 2) = -(Real.pi * (3 / 2)) by ring, Real.cos_neg, h3]
  fin_cases i <;> fin_cases j <;> norm_num <;> ring_nf <;>
    norm_num [h1, h3, hn1, hn3, Real.cos_neg, Real.cos_pi]

/-- A planar equilateral parallelogram with perpendicular adjacent edges is
a regular polygon according to the full pairwise-distance definition. -/
theorem regularPolygon_four_of_parallelogram {p : Fin 4 → Plane} {l : ℝ}
    (hl : 0 < l) (hpara : p 0 + p 2 = p 1 + p 3)
    (horth : ⟪p 1 - p 0, p 2 - p 1⟫_ℝ = 0)
    (h01 : ‖p 1 - p 0‖ = l) (h12 : ‖p 2 - p 1‖ = l) : IsRegularPolygon p := by
  have hq : 0 < l ^ 2 / 2 := div_pos (sq_pos_of_pos hl) (by norm_num)
  refine ⟨by decide, (1 / 4 : ℝ) • (p 0 + p 1 + p 2 + p 3),
    Real.sqrt (l ^ 2 / 2), Real.sqrt_pos.mpr hq, ?_, ?_⟩
  · intro i
    rw [dist_eq_norm]
    have hr := square_norm_sub_average_sq hpara horth h01 h12 i
    have hs := Real.sq_sqrt hq.le
    nlinarith [norm_nonneg (p i - (1 / 4 : ℝ) • (p 0 + p 1 + p 2 + p 3)),
      Real.sqrt_nonneg (l ^ 2 / 2)]
  · intro i j
    rw [dist_eq_norm]
    norm_num only [Nat.cast_ofNat]
    rw [square_distance_sq hpara horth h01 h12,
      square_cosine_table, Real.sq_sqrt hq.le]
    split_ifs <;> ring

/-- Every four-vertex carousel with distinct vertices has a fixed center and
constant squared radius `l²/2`. -/
theorem IsCarousel.square_fixed_center [Fact (Module.finrank ℝ E = 2)]
    {p : Fin 4 → ℝ → E} {l : ℝ} (hc : IsCarousel (finRotate 4) p l)
    (o : Orientation ℝ E (Fin 2)) (hinj : ∀ t, Function.Injective (fun i => p i t)) :
    ∃ c : E, ∀ (t : ℝ) (i : Fin 4), ‖p i t - c‖ ^ 2 = l ^ 2 / 2 := by
  refine ⟨(1 / 4 : ℝ) • (p 0 0 + p 1 0 + p 2 0 + p 3 0), ?_⟩
  intro t i
  rw [← hc.sum_four_eq o hinj t 0]
  refine square_norm_sub_average_sq (p := fun i => p i t) (hc.four_parallelogram o hinj t)
    (hc.four_edges_inner_eq_zero o hinj t) ?_ ?_ i
  · simpa using hc.edge_length 0 t
  · simpa using hc.edge_length 1 t

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- At every time, the four vertices form a regular polygon in their given order. -/
theorem IsCarousel.isRegularPolygon_four {p : Fin 4 → ℝ → Plane} {l : ℝ}
    (hc : IsCarousel (finRotate 4) p l) (o : Orientation ℝ Plane (Fin 2))
    (hinj : ∀ t, Function.Injective (fun i => p i t)) (t : ℝ) :
    IsRegularPolygon (fun i => p i t) := by
  apply regularPolygon_four_of_parallelogram hc.length_pos (hc.four_parallelogram o hinj t)
    (hc.four_edges_inner_eq_zero o hinj t)
  · simpa using hc.edge_length 0 t
  · simpa using hc.edge_length 1 t

end UlamFloating
