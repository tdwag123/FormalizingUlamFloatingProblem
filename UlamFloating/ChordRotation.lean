import UlamFloating.Extraction

/-!
# Rotation of constant chords

The second carousel law is expressed without choosing an angle branch.
On a strictly convex boundary, one orientation makes every chord's angular
speed positive. Its upper bound is two divided by the chord length.
-/

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- The local carousel laws express relative velocity as a rotated edge.
This is the second carousel law without choosing angular coordinates. -/
theorem velocity_sub_eq_rotation (o : Orientation ℝ E (Fin 2))
    {e u v : E} (he : e ≠ 0) (horth : ⟪e, v - u⟫_ℝ = 0)
    (hmid : ∃ a : ℝ, u + v = a • e) :
    v - u = (2 * o.areaForm u e / ‖e‖ ^ 2) • o.rightAngleRotation e := by
  have hn : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  obtain ⟨a, ha⟩ := hmid
  have hm := congrArg (fun z => o.areaForm e z) ha
  simp only [map_add, map_smul, smul_eq_mul, o.areaForm_apply_self, mul_zero] at hm
  have harea : o.areaForm e (v - u) = 2 * o.areaForm u e := by
    rw [map_sub, o.areaForm_swap u e]
    linarith
  have hdec := norm_sq_smul_eq_inner_add_area o e (v - u)
  rw [horth, zero_smul, zero_add, harea] at hdec
  calc
    _ = (‖e‖ ^ 2)⁻¹ • (‖e‖ ^ 2 • (v - u)) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    _ = _ := by rw [hdec, smul_smul]; congr 1; ring

/-- For a unit endpoint velocity, the absolute angular speed of a fixed
positive-length edge is at most two divided by its length. -/
theorem abs_angular_speed_le (o : Orientation ℝ E (Fin 2)) {e u : E} {l : ℝ}
    (hl : 0 < l) (he : ‖e‖ = l) (hu : ‖u‖ = 1) :
    |2 * o.areaForm u e / l ^ 2| ≤ 2 / l := by
  have ha := o.abs_areaForm_le u e
  rw [hu, he, one_mul] at ha
  rw [abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
    abs_of_pos (sq_pos_of_pos hl)]
  apply (div_le_iff₀ (sq_pos_of_pos hl)).mpr
  have heq : (2 / l) * l ^ 2 = 2 * l := by field_simp
  rw [heq]
  linarith

/-- Every carousel edge satisfies the intrinsic second carousel law. -/
theorem IsCarousel.edge_rotation {ι : Type*} {next : Equiv.Perm ι}
    {p : ι → ℝ → E} {l : ℝ} (hc : IsCarousel next p l)
    (o : Orientation ℝ E (Fin 2)) (i : ι) (t : ℝ) :
    deriv (p (next i)) t - deriv (p i) t =
      (2 * o.areaForm (deriv (p i) t) (p (next i) t - p i t) / l ^ 2) •
        o.rightAngleRotation (p (next i) t - p i t) := by
  have he : p (next i) t - p i t ≠ 0 := by
    intro hz
    have hlen := hc.edge_length i t
    rw [hz, norm_zero] at hlen
    exact hc.length_pos.ne' hlen.symm
  have hp := ((hc.contDiff i).differentiable (by simp) t).hasDerivAt
  have hq := ((hc.contDiff (next i)).differentiable (by simp) t).hasDerivAt
  simpa only [hc.edge_length i t] using velocity_sub_eq_rotation o he
    (inner_edge_velocity_eq_zero hp hq (hc.edge_length i)) (hc.midpoint_parallel i t)

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The intrinsic chord derivative holds in either orientation. Positivity
of angular speed is a separate consequence of choosing the boundary orientation. -/
theorem IsUnitSpeedBoundary.hasDerivAt_chord_rotation {K : Set Plane} {P h l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (hl : 0 < l) (hc : HasConstantChord γ h l)
    (t : ℝ) :
    HasDerivAt (fun s => γ (s + h) - γ s)
      ((2 * o.areaForm (deriv γ t) (γ (t + h) - γ t) / l ^ 2) •
        o.rightAngleRotation (γ (t + h) - γ t)) t := by
  have he : ‖γ (t + h) - γ t‖ = l := by simpa only [dist_eq_norm] using hc t
  have hne : γ (t + h) - γ t ≠ 0 := by
    intro hz
    rw [hz, norm_zero] at he
    exact hl.ne' he.symm
  have hp := (hb.contDiff.differentiable (by simp) t).hasDerivAt
  have hq : HasDerivAt (fun s => γ (s + h)) (deriv γ (t + h)) t := by
    simpa using (hb.contDiff.differentiable (by simp) (t + h)).hasDerivAt.scomp t
      ((hasDerivAt_id t).add_const h)
  have hv := velocity_sub_eq_rotation o hne
    (inner_edge_velocity_eq_zero hp hq (fun s => by simpa [dist_eq_norm] using hc s))
    (hb.chord_midpoint_parallel hl hc t)
  rw [he] at hv
  exact hv ▸ hq.sub hp

/-- Constant positive chords of a strictly convex unit-speed boundary rotate
strictly in one direction, with angular speed at most `2/l`. This theorem
also supplies the derivative of the chord vector, without an angle lift. -/
theorem IsUnitSpeedBoundary.chord_rotation {K : Set Plane} {P h l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ h l) :
    ∃ o : Orientation ℝ Plane (Fin 2), ∀ t,
      let e := γ (t + h) - γ t
      let a := 2 * o.areaForm (deriv γ t) e / l ^ 2
      HasDerivAt (fun s => γ (s + h) - γ s) (a • o.rightAngleRotation e) t ∧
        0 < a ∧ a ≤ 2 / l := by
  obtain ⟨o, ho⟩ := hb.exists_positive_orientation
  refine ⟨o, ?_⟩
  intro t
  dsimp only
  have he : ‖γ (t + h) - γ t‖ = l := by simpa only [dist_eq_norm] using hc t
  have hne : γ (t + h) ≠ γ t := by
    intro hz
    rw [hz, sub_self, norm_zero] at he
    exact hl.ne' he.symm
  have harea := ho t (γ (t + h)) (hb.mem (t + h)) hne
  refine ⟨hb.hasDerivAt_chord_rotation o hl hc t,
    div_pos (mul_pos (by norm_num) harea) (sq_pos_of_pos hl), ?_⟩
  exact (le_abs_self _).trans (abs_angular_speed_le o hl he (hb.unit_speed t))

end UlamFloating
