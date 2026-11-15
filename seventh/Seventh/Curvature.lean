import Seventh.ContactGeometry
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Convexity gives nonnegative curvature

We obtain the curvature sign from supporting tangent lines. This avoids
assuming a positive curvature lower bound or an initially twice differentiable
boundary. The contact construction already supplies differentiability of the tangent.
-/

namespace UlamFloating.Seventh

open Filter
open scoped Topology InnerProductSpace

/-- At a local minimum, a continuous real function has nonnegative second
derivative (with mathlib's totalized derivative convention). -/
theorem second_deriv_nonneg_of_local_min {f : ℝ → ℝ} {t : ℝ}
    (hc : ContinuousAt f t) (hmin : IsLocalMin f t) : 0 ≤ deriv (deriv f) t := by
  by_contra hnot
  have hneg : deriv (deriv f) t < 0 := lt_of_not_ge hnot
  have hmax := isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hc
  have he : f =ᶠ[𝓝 t] fun _ => f t := by
    filter_upwards [hmin, hmax] with s hsmin hsmax
    exact le_antisymm hsmax hsmin
  have hz := he.deriv.deriv_eq
  simp only [deriv_const', deriv_const] at hz
  linarith

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A positively oriented supported unit tangent can only turn with
nonnegative angular velocity. This lemma is independent of chord sampling. -/
theorem curvature_nonneg_of_support {γ : ℝ → Plane}
    (o : Orientation ℝ Plane (Fin 2)) {t k : ℝ}
    (hγ : Differentiable ℝ γ) (hunit : ‖deriv γ t‖ = 1)
    (hv : HasDerivAt (deriv γ) (k • o.rightAngleRotation (deriv γ t)) t)
    (hsupport : ∀ s, 0 ≤ o.areaForm (deriv γ t) (γ s - γ t)) : 0 ≤ k := by
  let f : ℝ → ℝ := fun s => o.areaForm (deriv γ t) (γ s - γ t)
  let L := o.areaForm' (deriv γ t)
  have hd (s : ℝ) : HasDerivAt f (o.areaForm (deriv γ t) (deriv γ s)) s := by
    exact L.hasFDerivAt.comp_hasDerivAt s ((hγ s).hasDerivAt.sub_const (γ t))
  have hmin : IsLocalMin f t := by
    apply Filter.Eventually.of_forall
    intro s
    simpa only [f, sub_self, map_zero] using hsupport s
  have hsecond := second_deriv_nonneg_of_local_min (hd t).continuousAt hmin
  have hdf : deriv f = fun s => o.areaForm (deriv γ t) (deriv γ s) :=
    funext (fun s => (hd s).deriv)
  have hd2 := L.hasFDerivAt.comp_hasDerivAt t hv
  change HasDerivAt (fun s => o.areaForm (deriv γ t) (deriv γ s))
    (o.areaForm (deriv γ t) (k • o.rightAngleRotation (deriv γ t))) t at hd2
  rw [hdf, hd2.deriv, map_smul, smul_eq_mul, o.areaForm_rightAngleRotation_right,
    real_inner_self_eq_norm_sq, hunit, one_pow, mul_one] at hsecond
  exact hsecond

/-- The orientation of a contact system puts the whole body on the left of
every directed tangent. Its positive chord angle fixes the orientation. -/
theorem ContactSystem.support_nonneg {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l) (hc : HasConstantChord γ h l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) {x : Plane} (hx : x ∈ K) :
    0 ≤ o.areaForm (deriv γ t) (x - γ t) := by
  by_cases he : x = γ t
  · simp [he]
  obtain ⟨c, hcint⟩ := hb.interior_nonempty
  have hedge : γ (t + h) ≠ γ t := by
    intro heq
    have hlen := hc t
    rw [heq, dist_self] at hlen
    linarith
  have hangle : 0 < deriv θ t := by
    rw [hs.angular_speed]
    exact mul_pos (div_pos (by norm_num) hl)
      (Real.sin_pos_of_pos_of_lt_pi (hs.angle_range t).1 (hs.angle_range t).2)
  have hchord := hb.chord_area_pos_of_angle_deriv_pos o hl hc
    (hs.contDiff_lift.differentiable (by simp) t) hangle hs.chord_rotation
  have hcenter := (mul_pos_iff_of_pos_left hchord).mp
    (hb.areaForm_mul_pos o hcint t (hb.mem (t + h)) hedge)
  exact ((mul_pos_iff_of_pos_right hcenter).mp
    (hb.areaForm_mul_pos o hcint t hx he)).le

/-- Convexity supplies the missing sign in the contact-angle curvature formula. -/
theorem ContactSystem.curvature_nonneg {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l) (hc : HasConstantChord γ h l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) :
    0 ≤ (2 / l) * Real.sin (α t) - deriv α t :=
  curvature_nonneg_of_support o (hb.contDiff.differentiable (by simp)) (hb.unit_speed t)
    (hs.tangent_deriv t) (fun s => hs.support_nonneg hb hl hc t (hb.mem s))

/-- Both endpoint curvatures bound the speed of the contact angle. -/
theorem ContactSystem.abs_angle_deriv_le {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l) (hc : HasConstantChord γ h l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) :
    |deriv α t| ≤ (2 / l) * Real.sin (α t) := by
  have hleft := hs.curvature_nonneg hb hl hc t
  have hright := hs.curvature_nonneg hb hl hc (t + h)
  have hchain := hs.chain t
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The neighboring-sine inequality of the proposed proof follows from
nonnegative curvature at the two outside endpoints. -/
theorem ContactSystem.sin_le_neighbors {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l) (hc : HasConstantChord γ h l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (t : ℝ) :
    Real.sin (α (t + h)) ≤ Real.sin (α t) + Real.sin (α (t + 2 * h)) := by
  have h0 := hs.curvature_nonneg hb hl hc t
  have h3 := hs.curvature_nonneg hb hl hc (t + 3 * h)
  have hc0 := hs.chain t
  have hc1 := hs.chain (t + h)
  have hc2 := hs.chain (t + 2 * h)
  rw [show t + h + h = t + 2 * h by ring] at hc1
  rw [show t + 2 * h + h = t + 3 * h by ring] at hc2
  have hk : 0 < 2 / l := div_pos (by norm_num) hl
  have he : (2 / l) * Real.sin (α (t + h)) ≤
      (2 / l) * (Real.sin (α t) + Real.sin (α (t + 2 * h))) := by linarith
  exact (mul_le_mul_iff_right₀ hk).mp he

end UlamFloating.Seventh
