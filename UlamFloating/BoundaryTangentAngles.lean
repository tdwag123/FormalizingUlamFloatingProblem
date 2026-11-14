import UlamFloating.ChordAngularVelocity

/-!
# Tangent angles along a constant-chord boundary

Positive tangent–chord angles are periodic. Their consecutive sums are
the real increments of the global chord lift, and their sines give its
angular speed. These are the geometric inputs to the odd-polygon equations.
-/

namespace UlamFloating

open scoped InnerProductSpace

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A positive differentiable chord lift determines periodic tangent–chord
angles, their consecutive-sum identity, the exact sine speed law, and
the rotation taking the original unit tangent to its normalized chord. -/
theorem IsUnitSpeedBoundary.exists_tangent_chord_angles_with_rotation
    {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ)
    (hh : 0 < h) (hhalf : 2 * h < P) (hl : 0 < l) (hc : HasConstantChord γ h l)
    (hθ : ContDiff ℝ 1 (fun t => θ t))
    (hpos : ∀ t, 0 < deriv (fun s => θ s) t)
    (hrot : ∀ t, γ (t + h) - γ t = Real.cos (θ t) • (γ h - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ h - γ 0)) :
    ∃ α : ℝ → ℝ, Function.Periodic α P ∧
      (∀ t, 0 < α t ∧ α t < Real.pi) ∧
      (∀ t, α t + α (t + h) = θ (t + h) - θ t) ∧
      (∀ t, deriv (fun s => θ s) t = (2 / l) * Real.sin (α t)) ∧
      (∀ t, l⁻¹ • (γ (t + h) - γ t) =
        o.rotation (α t : Real.Angle) (deriv γ t)) := by
  let e : ℝ → Plane := fun t => γ (t + h) - γ t
  have he (t : ℝ) : ‖e t‖ = l := by simpa only [e, dist_eq_norm] using hc t
  have hlocal (t : ℝ) : ∃ a : ℝ, 0 < a ∧ a < Real.pi ∧
      Real.cos a = ⟪deriv γ t, l⁻¹ • e t⟫_ℝ ∧
      Real.sin a = o.areaForm (deriv γ t) (e t) / l ∧
      l⁻¹ • e t = o.rotation (a : Real.Angle) (deriv γ t) ∧
      deriv γ (t + h) = o.rotation (a : Real.Angle) (l⁻¹ • e t) := by
    have hp := (hb.contDiff.differentiable (by simp) t).hasDerivAt
    have hq : HasDerivAt (fun s => γ (s + h)) (deriv γ (t + h)) t := by
      simpa using (hb.contDiff.differentiable (by simp) (t + h)).hasDerivAt.scomp t
        ((hasDerivAt_id t).add_const h)
    exact exists_positive_chord_angle o hl (he t) (hb.unit_speed t)
      (hb.chord_area_pos_of_angle_deriv_pos o hl hc
        (hθ.differentiable (by simp) t) (hpos t) hrot)
      (inner_edge_velocity_eq_zero hp hq he) (hb.chord_midpoint_parallel hl hc t)
  choose α ha0 hap hcos hsin hfirst hsecond using hlocal
  have hep : Function.Periodic e P := by
    intro t
    dsimp [e]
    rw [show t + P + h = t + h + P by ring, hb.periodic, hb.periodic]
  refine ⟨α, ?_, fun t => ⟨ha0 t, hap t⟩, ?_, ?_, hfirst⟩
  · intro t
    apply Real.injOn_cos ⟨(ha0 _).le, (hap _).le⟩ ⟨(ha0 _).le, (hap _).le⟩
    rw [hcos, hcos, hep,
      periodic_deriv hb.periodic (hb.contDiff.differentiable (by simp))]
  · intro t
    have hne : l⁻¹ • e t ≠ 0 := by
      have hn : ‖l⁻¹ • e t‖ = 1 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hl), he,
          inv_mul_cancel₀ hl.ne']
      intro hz
      rw [hz, norm_zero] at hn
      exact zero_ne_one hn
    have hr (s : ℝ) : e s = o.rotation (θ s : Real.Angle) (γ h - γ 0) := by
      simpa only [e, o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe]
        using hrot s
    have hrelative : l⁻¹ • e (t + h) =
        o.rotation ((θ (t + h) - θ t : ℝ) : Real.Angle) (l⁻¹ • e t) := by
      rw [map_smul, hr t, o.rotation_rotation, ← Real.Angle.coe_add, sub_add_cancel,
        ← hr (t + h)]
    exact tangent_chord_angle_add o hne ⟨ha0 t, hap t⟩ ⟨ha0 _, hap _⟩
      ⟨sub_pos.mpr (θ.strictMono (by linarith)),
        hb.chord_angle_increment_lt_pi o θ hh hhalf hrot t⟩
      (hsecond t) (hfirst (t + h)) hrelative
  · intro t
    rw [hb.chord_angle_deriv o hl hc (hθ.differentiable (by simp) t) hrot, hsin]
    dsimp only [e]
    ring

/-- A positive differentiable chord lift determines periodic tangent–chord
angles, their consecutive-sum identity, and the exact sine speed law. -/
theorem IsUnitSpeedBoundary.exists_tangent_chord_angles
    {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ)
    (hh : 0 < h) (hhalf : 2 * h < P) (hl : 0 < l) (hc : HasConstantChord γ h l)
    (hθ : ContDiff ℝ 1 (fun t => θ t))
    (hpos : ∀ t, 0 < deriv (fun s => θ s) t)
    (hrot : ∀ t, γ (t + h) - γ t = Real.cos (θ t) • (γ h - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ h - γ 0)) :
    ∃ α : ℝ → ℝ, Function.Periodic α P ∧
      (∀ t, 0 < α t ∧ α t < Real.pi) ∧
      (∀ t, α t + α (t + h) = θ (t + h) - θ t) ∧
      (∀ t, deriv (fun s => θ s) t = (2 / l) * Real.sin (α t)) := by
  obtain ⟨α, hp, hrange, hsum, hspeed, _⟩ :=
    hb.exists_tangent_chord_angles_with_rotation o θ hh hhalf hl hc hθ hpos hrot
  exact ⟨α, hp, hrange, hsum, hspeed⟩

end UlamFloating
