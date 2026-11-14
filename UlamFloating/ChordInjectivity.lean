import UlamFloating.BoundaryConvexity

/-!
# A boundary chord vector cannot repeat within one traversal

For a parameter increment smaller than half the period, equal directed
chord vectors contradict the cyclic order on a strictly convex boundary.
This provides the geometric input needed to show that a global chord angle
makes exactly one turn. Constant chord length is not used here.
-/

namespace UlamFloating

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Diagonals with interlaced boundary endpoints are not parallel. -/
theorem IsUnitSpeedBoundary.chord_not_parallel_of_interlaced
    {K : Set Plane} {P : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d < a + P)
    (k : ℝ) : γ d - γ b ≠ k • (γ c - γ a) := by
  obtain ⟨o, ho⟩ := hb.exists_positive_orientation
  let e := γ c - γ a
  have hleft := hb.areaForm_pos_of_ordered o ho hab hbc (hcd.trans hda)
  have hright := hb.areaForm_pos_of_ordered o ho (hab.trans hbc) hcd hda
  change 0 < o.areaForm (γ b - γ a) e at hleft
  rw [o.areaForm_swap] at hleft
  change 0 < o.areaForm e (γ d - γ a) at hright
  intro heq
  have hdecomp : γ d - γ a = k • e + (γ b - γ a) := by
    dsimp [e]
    rw [← heq]
    abel
  rw [hdecomp, map_add, map_smul, o.areaForm_apply_self, smul_zero, zero_add] at hright
  linarith

/-- Consecutive edges through three ordered boundary points are not parallel. -/
theorem IsUnitSpeedBoundary.chord_not_parallel_of_adjacent
    {K : Set Plane} {P : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    {a b c : ℝ} (hab : a < b) (hbc : b < c) (hca : c < a + P) (k : ℝ) :
    γ c - γ b ≠ k • (γ b - γ a) := by
  obtain ⟨o, ho⟩ := hb.exists_positive_orientation
  have harea := hb.areaForm_pos_of_ordered o ho hab hbc hca
  intro heq
  rw [show γ c - γ a = (γ c - γ b) + (γ b - γ a) by abel,
    map_add, heq, map_smul, o.areaForm_apply_self, smul_zero, add_zero] at harea
  exact (lt_irrefl 0) harea

/-- Interlaced endpoints on a strictly convex boundary cannot give equal
directed diagonal vectors. -/
theorem IsUnitSpeedBoundary.chord_ne_of_interlaced
    {K : Set Plane} {P : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d < a + P) :
    γ d - γ b ≠ γ c - γ a := by
  simpa only [one_smul] using hb.chord_not_parallel_of_interlaced hab hbc hcd hda 1

/-- Disjoint directed edges in cyclic boundary order cannot be equal vectors. -/
theorem IsUnitSpeedBoundary.chord_ne_of_disjoint
    {K : Set Plane} {P : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    {a b c d : ℝ} (hab : a < b) (hbc : b < c) (hcd : c < d) (hda : d < a + P) :
    γ d - γ c ≠ γ b - γ a := by
  obtain ⟨o, ho⟩ := hb.exists_positive_orientation
  have hleft := hb.areaForm_pos_of_ordered o ho hab hbc (hcd.trans hda)
  have hright := hb.areaForm_pos_of_ordered o ho hcd hda
    (by linarith : a + P < c + P)
  rw [hb.periodic] at hright
  intro heq
  rw [heq, show γ a - γ c = -(γ c - γ a) by abel, map_neg] at hright
  linarith

/-- Consecutive edges through three ordered boundary points cannot be equal. -/
theorem IsUnitSpeedBoundary.chord_ne_of_adjacent
    {K : Set Plane} {P : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    {a b c : ℝ} (hab : a < b) (hbc : b < c) (hca : c < a + P) :
    γ c - γ b ≠ γ b - γ a := by
  simpa only [one_smul] using hb.chord_not_parallel_of_adjacent hab hbc hca 1

/-- For an increment less than half a traversal, the chord vector never
returns to its initial value at an intermediate parameter. -/
theorem IsUnitSpeedBoundary.chord_vector_ne_initial
    {K : Set Plane} {P h : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (hh : 0 < h) (hhalf : 2 * h < P) {t : ℝ} (ht : 0 < t) (htP : t < P) :
    γ (t + h) - γ t ≠ γ h - γ 0 := by
  rcases lt_trichotomy t h with hth | rfl | hht
  · exact hb.chord_ne_of_interlaced ht hth (by linarith) (by linarith)
  · exact hb.chord_ne_of_adjacent hh (by linarith) (by linarith)
  · rcases lt_trichotomy (t + h) P with htp | htp | htp
    · exact hb.chord_ne_of_disjoint hh hht (by linarith) (by linarith)
    · have hnot := hb.chord_ne_of_adjacent htP (by linarith : P < P + h)
        (by linarith : P + h < t + P)
      have hp0 : γ P = γ 0 := by simpa only [zero_add] using hb.periodic 0
      rw [hp0, show P + h = h + P by ring, hb.periodic] at hnot
      rw [htp, hp0]
      exact Ne.symm hnot
    · have hnot := hb.chord_ne_of_interlaced htP htp
        (by linarith : t + h < P + h) (by linarith : P + h < t + P)
      have hp0 : γ P = γ 0 := by simpa only [zero_add] using hb.periodic 0
      rw [hp0, show P + h = h + P by ring, hb.periodic] at hnot
      exact Ne.symm hnot

end UlamFloating
