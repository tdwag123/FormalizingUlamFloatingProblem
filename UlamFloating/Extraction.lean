import UlamFloating.BoundaryConvexity
import UlamFloating.Statements

/-!
# The carousel laws from a strictly convex boundary

This file proves the analytic part of convex carousel extraction. Finite samples
have constant equal edges, unit-speed regularity, and edge-parallel midpoint
velocities. Strict convexity and cyclic order of the sampled polygon are separate
geometric conclusions; they are not assumed or asserted by this analytic result.
-/

namespace UlamFloating

open scoped InnerProductSpace

section Planar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- In the plane, two vectors orthogonal to the same nonzero vector are parallel. -/
theorem exists_smul_of_inner_eq_zero (o : Orientation ℝ E (Fin 2))
    {e z w : E} (he : e ≠ 0) (hw : w ≠ 0)
    (heorth : ⟪w, e⟫_ℝ = 0) (hzorth : ⟪w, z⟫_ℝ = 0) :
    ∃ a : ℝ, z = a • e := by
  have hnw : ‖w‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hw)
  have hne : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  have h := o.inner_mul_areaForm_sub w e z
  rw [heorth, hzorth, zero_mul, mul_zero, sub_self] at h
  have harea : o.areaForm e z = 0 := (mul_eq_zero.mp h.symm).resolve_left hnw
  have hdecomp := norm_sq_smul_eq_inner_add_area o e z
  rw [harea, zero_smul, add_zero] at hdecomp
  refine ⟨⟪e, z⟫_ℝ / ‖e‖ ^ 2, ?_⟩
  calc
    z = (‖e‖ ^ 2)⁻¹ • (‖e‖ ^ 2 • z) := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (⟪e, z⟫_ℝ / ‖e‖ ^ 2) • e := by
      rw [hdecomp, smul_smul]
      congr 1
      ring

/-- Equal speeds and constant edge length imply the midpoint law whenever
the endpoint velocities are distinct. The distinctness hypothesis is essential. -/
theorem midpoint_parallel_of_equal_norms (o : Orientation ℝ E (Fin 2))
    {e u v : E} (he : e ≠ 0) (huv : u ≠ v) (hnorm : ‖u‖ = ‖v‖)
    (horth : ⟪e, v - u⟫_ℝ = 0) : ∃ a : ℝ, u + v = a • e := by
  apply exists_smul_of_inner_eq_zero o he (sub_ne_zero.mpr huv.symm)
  · rwa [real_inner_comm e (v - u)]
  · simp only [inner_sub_left, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_comm u v, hnorm]
    ring

end Planar

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A constant positive chord of a strictly convex unit-speed boundary has
edge-parallel midpoint velocity. -/
theorem IsUnitSpeedBoundary.chord_midpoint_parallel {K : Set Plane} {P : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) {h l : ℝ}
    (hl : 0 < l) (hc : HasConstantChord γ h l) (t : ℝ) :
    ∃ a : ℝ, deriv γ t + deriv γ (t + h) = a • (γ (t + h) - γ t) := by
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hne : γ (t + h) ≠ γ t := by
    intro heq
    have hh := hc t
    rw [heq, dist_self] at hh
    exact hl.ne' hh.symm
  apply midpoint_parallel_of_equal_norms o (sub_ne_zero.mpr hne)
    (hb.deriv_ne_of_ne hne.symm) ((hb.unit_speed t).trans (hb.unit_speed (t + h)).symm)
  have hp := (hb.contDiff.differentiable (by simp) t).hasDerivAt
  have hq : HasDerivAt (fun s => γ (s + h)) (deriv γ (t + h)) t := by
    simpa using (hb.contDiff.differentiable (by simp) (t + h)).hasDerivAt.scomp t
      ((hasDerivAt_id t).add_const h)
  exact inner_edge_velocity_eq_zero hp hq (fun s => by simpa [dist_eq_norm] using hc s)

/-- The finite rational samples of a constant-chord boundary satisfy all
carousel kinematic laws. This theorem does not yet assert polygon order. -/
theorem IsUnitSpeedBoundary.boundarySamples_isCarousel {K : Set Plane} {P : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) {n : ℕ} {l : ℝ}
    (hl : 0 < l) (hc : HasConstantChord γ (P / n) l) :
    IsCarousel (finRotate n) (boundarySamples γ P n) l := by
  have hd : Differentiable ℝ γ := hb.contDiff.differentiable (by simp)
  refine ⟨hl, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hb.contDiff.comp (contDiff_id.add contDiff_const)
  · intro i t
    rw [deriv_boundarySamples hd]
    exact hb.deriv_ne_zero _
  · intro i t
    simpa only [dist_eq_norm] using hc.boundarySamples_edge hb.periodic i t
  · intro i t
    rw [deriv_boundarySamples hd, deriv_boundarySamples_rotate hd hb.periodic,
      boundarySamples_rotate hb.periodic]
    simpa only [boundarySamples, sampledVertex, add_comm, add_left_comm, add_assoc] using
      hb.chord_midpoint_parallel hl hc (t + (i.val : ℝ) * (P / n))

/-- Complete extraction of a cyclically ordered convex carousel from a
constant-chord boundary, including the time-shift identity. -/
theorem carousel_extraction : carouselExtractionStatement := by
  intro n hn K P γ l hb hl hchord
  exact ⟨hb.boundarySamples_isCarousel hl hchord,
    hb.boundarySamples_strictlyConvex hn, boundarySamples_rotate hb.periodic⟩

end UlamFloating
