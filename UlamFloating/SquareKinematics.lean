import UlamFloating.Quadrilateral

/-!
# Four-vertex carousel kinematics

The alternating midpoint equations fix the vertex average of a nondegenerate
parallelogram carousel. Differentiating the parallelogram identity and imposing
the rigid-edge derivatives then forces a right angle.
-/

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Planar

variable [Fact (Module.finrank ℝ E = 2)]

/-- Vanishing oriented area with a nonzero first vector means parallelism. -/
theorem exists_smul_of_areaForm_eq_zero (o : Orientation ℝ E (Fin 2))
    {e f : E} (he : e ≠ 0) (harea : o.areaForm e f = 0) : ∃ a : ℝ, f = a • e := by
  have hn : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  have h := norm_sq_smul_eq_inner_add_area o e f
  rw [harea, zero_smul, add_zero] at h
  refine ⟨⟪e, f⟫_ℝ / ‖e‖ ^ 2, ?_⟩
  calc
    f = (‖e‖ ^ 2)⁻¹ • (‖e‖ ^ 2 • f) := by rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    _ = (⟪e, f⟫_ℝ / ‖e‖ ^ 2) • e := by rw [h, smul_smul]; congr 1; ring

/-- Equal-length vectors which are neither equal nor opposite enclose nonzero area. -/
theorem areaForm_ne_zero_of_norm_eq (o : Orientation ℝ E (Fin 2))
    {e f : E} (he : e ≠ 0) (hn : ‖f‖ = ‖e‖) (hfe : f ≠ e) (hfneg : f ≠ -e) :
    o.areaForm e f ≠ 0 := by
  intro h
  obtain ⟨a, ha⟩ := exists_smul_of_areaForm_eq_zero o he h
  exact (eq_or_eq_neg_of_norm_eq_of_smul hn ha).elim hfe hfneg

/-- Distinct diagonals prevent adjacent edges of an equilateral parallelogram
from being parallel. -/
theorem areaForm_ne_zero_of_parallelogram (o : Orientation ℝ E (Fin 2))
    {a b c d : E} {l : ℝ} (hl : 0 < l) (hpara : a + c = b + d)
    (hac : a ≠ c) (hbd : b ≠ d) (hba : ‖b - a‖ = l) (had : ‖a - d‖ = l) :
    o.areaForm (b - a) (c - b) ≠ 0 := by
  have hedge : c - b = d - a := by
    calc
      c - b = (a + c) - (a + b) := by abel
      _ = (b + d) - (a + b) := by rw [hpara]
      _ = d - a := by abel
  rw [hedge]
  apply areaForm_ne_zero_of_norm_eq o
  · intro he
    have h := hba
    rw [he, norm_zero] at h
    exact hl.ne' h.symm
  · rw [norm_sub_rev d a, had, hba]
  · intro h
    exact hbd (sub_left_inj.mp h).symm
  · intro h
    have hsum : b + d = a + a := by
      rw [(sub_eq_iff_eq_add).mp h]
      abel
    exact hac (add_left_cancel (hpara.trans hsum)).symm

/-- The alternating midpoint equations of a nondegenerate parallelogram
force the total vertex velocity to vanish. -/
theorem sum_four_velocity_eq_zero (o : Orientation ℝ E (Fin 2))
    {e f u v w z : E} (harea : o.areaForm e f ≠ 0)
    (h0 : ∃ a : ℝ, u + v = a • e) (h1 : ∃ b : ℝ, v + w = b • f)
    (h2 : ∃ c : ℝ, w + z = c • (-e)) (h3 : ∃ d : ℝ, z + u = d • (-f)) :
    u + v + w + z = 0 := by
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  obtain ⟨c, hc⟩ := h2
  obtain ⟨d, hd⟩ := h3
  have hlinear : (a - c) • e + (d - b) • f = 0 := by
    calc
      (a - c) • e + (d - b) • f = a • e - b • f + c • (-e) - d • (-f) := by module
      _ = (u + v) - (v + w) + (w + z) - (z + u) := by rw [← ha, ← hb, ← hc, ← hd]
      _ = 0 := by abel
  have hf := congrArg (fun x => o.areaForm f x) hlinear
  simp only [map_add, map_smul, smul_eq_mul, o.areaForm_apply_self,
    mul_zero, add_zero, map_zero] at hf
  have hfe : o.areaForm f e ≠ 0 := by
    rw [o.areaForm_swap f e]
    exact neg_ne_zero.mpr harea
  have hac : a = c := sub_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hfe)
  calc
    u + v + w + z = (u + v) + (w + z) := by abel
    _ = c • e + c • (-e) := by rw [ha, hc, hac]
    _ = 0 := by module

end Planar

/-- If a parallelogram's velocity sum is zero and its diagonal-sum identity
is differentiated, opposite vertex velocities are opposite. -/
theorem opposite_velocities_of_sum_eq_zero {u v w z : E}
    (hsum : u + v + w + z = 0) (hdiag : u + w = v + z) : w = -u ∧ z = -v := by
  have hu : (2 : ℝ) • (u + w) = 0 := by
    calc
      (2 : ℝ) • (u + w) = (u + w) + (v + z) := by rw [← hdiag]; module
      _ = 0 := by convert hsum using 1; abel
  have huw : u + w = 0 := (smul_eq_zero.mp hu).resolve_left (by norm_num)
  have hvz : v + z = 0 := hdiag.symm.trans huw
  exact ⟨eq_neg_of_add_eq_zero_left (by simpa [add_comm] using huw),
    eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hvz)⟩

/-- A regular parallelogram carousel must have orthogonal adjacent edges. -/
theorem inner_edges_eq_zero_of_carousel_laws {e f u v w z : E}
    (hu : u ≠ 0) (hsum : u + v + w + z = 0) (hdiag : u + w = v + z)
    (horth0 : ⟪e, v - u⟫_ℝ = 0) (horth1 : ⟪f, w - v⟫_ℝ = 0)
    (h0 : ∃ a : ℝ, u + v = a • e) (h1 : ∃ b : ℝ, v + w = b • f) :
    ⟪e, f⟫_ℝ = 0 := by
  obtain ⟨hw, _⟩ := opposite_velocities_of_sum_eq_zero hsum hdiag
  obtain ⟨a, ha⟩ := h0
  obtain ⟨b, hb⟩ := h1
  have hvu : v - u = b • f := by simpa only [hw, sub_eq_add_neg] using hb
  have hwv : w - v = -(a • e) := by rw [hw, ← ha]; abel
  rw [hvu, real_inner_smul_right] at horth0
  rw [hwv, inner_neg_right, real_inner_smul_right, real_inner_comm e f] at horth1
  by_contra hne
  have hb0 : b = 0 := (mul_eq_zero.mp horth0).resolve_right hne
  have ha0 : a = 0 := (mul_eq_zero.mp (neg_eq_zero.mp horth1)).resolve_right hne
  have hsumuv : u + v = 0 := by simpa only [ha0, zero_smul] using ha
  have hdiff : v - u = 0 := by simpa only [hb0, zero_smul] using hvu
  have hv : v = u := sub_eq_zero.mp hdiff
  have hz : (2 : ℝ) • u = 0 := by simpa only [two_smul, hv] using hsumuv
  exact hu ((smul_eq_zero.mp hz).resolve_left (by norm_num))

end UlamFloating
