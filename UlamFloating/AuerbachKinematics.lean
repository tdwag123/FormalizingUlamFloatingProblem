import UlamFloating.HydrostaticMeasure
import UlamFloating.BoundaryConvexity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Module

/-!
# The differential core of Auerbach's constant-chord argument

If the centered cap moment is normal to the chord and its derivative is the
moving-cap flux, then the chord length is constant. This theorem separates the
finite-dimensional argument from the measure-theoretic flux formula. Its flux
hypothesis must be established for actual waterline caps before it can be used
to prove the physical floating equivalence.
-/

namespace UlamFloating

open scoped InnerProductSpace

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A positive proper boundary increment always gives a nonzero chord. -/
theorem IsUnitSpeedBoundary.chord_ne_zero {K : Set Plane} {P h : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hh : 0 < h) (hhP : h < P) (t : ℝ) :
    γ (t + h) - γ t ≠ 0 := by
  intro hz
  have he := hb.injOn_Ico t (show t + h ∈ Set.Ico t (t + P) by constructor <;> linarith)
    (show t ∈ Set.Ico t (t + P) by constructor <;> linarith [hb.period_pos])
    (sub_eq_zero.mp hz)
  linarith

/-- The chord turns strictly in the positive orientation, without assuming constant length. -/
theorem IsUnitSpeedBoundary.chord_turning_pos {K : Set Plane} {P h : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hh : 0 < h) (hhP : h < P)
    (o : Orientation ℝ Plane (Fin 2))
    (ho : ∀ t x, x ∈ K → x ≠ γ t → 0 < o.areaForm (deriv γ t) (x - γ t)) (t : ℝ) :
    0 < o.areaForm (γ (t + h) - γ t)
      (deriv (fun s => γ (s + h) - γ s) t) := by
  have hne := sub_ne_zero.mp (hb.chord_ne_zero hh hhP t)
  have hp := (hb.contDiff.differentiable (by simp) t).hasDerivAt
  have hq := ((hb.contDiff.differentiable (by simp) (t + h)).hasDerivAt).scomp t
    ((hasDerivAt_id t).add_const h)
  simp only [one_smul] at hq
  have hd : HasDerivAt (fun s => γ (s + h) - γ s)
      (deriv γ (t + h) - deriv γ t) t := hq.sub hp
  rw [hd.deriv, map_sub]
  have hleft := ho t (γ (t + h)) (hb.mem _) hne
  have hright := ho (t + h) (γ t) (hb.mem _) hne.symm
  rw [show γ t - γ (t + h) = -(γ (t + h) - γ t) by abel,
    map_neg, o.areaForm_swap (deriv γ (t + h)) (γ (t + h) - γ t), neg_neg] at hright
  rw [o.areaForm_swap (deriv γ t) (γ (t + h) - γ t)] at hleft
  linarith

/-- Torque and its derivative determine the centered first moment exactly. -/
theorem normal_moment_eq_of_inner_derivative
    (o : Orientation ℝ Plane (Fin 2)) {e v M : Plane}
    (he : e ≠ 0) (hrot : o.areaForm e v ≠ 0)
    (hnormal : ⟪e, M⟫_ℝ = 0)
    (hderiv : ⟪v, M⟫_ℝ = -(o.areaForm e v * ‖e‖ ^ 2 / 12)) :
    M = -(‖e‖ ^ 2 / 12) • o.rightAngleRotation e := by
  have hL : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  have hdec := norm_sq_smul_eq_inner_add_area o e M
  rw [hnormal, zero_smul, zero_add] at hdec
  have hi := congrArg (fun x => ⟪x, v⟫_ℝ) hdec
  simp only [real_inner_smul_left, o.inner_rightAngleRotation_left] at hi
  rw [real_inner_comm v M, hderiv] at hi
  have hc : o.areaForm e M = -(‖e‖ ^ 2 * ‖e‖ ^ 2 / 12) := by
    apply mul_left_cancel₀ hrot
    nlinarith [hi]
  have heq : ‖e‖ ^ 2 • M =
      ‖e‖ ^ 2 • (-(‖e‖ ^ 2 / 12) • o.rightAngleRotation e) := by
    rw [hdec, hc]
    module
  have := congrArg (fun x => (‖e‖ ^ 2)⁻¹ • x) heq
  simpa only [smul_smul, ← mul_assoc, inv_mul_cancel₀ hL, one_smul, one_mul] using this

/-- Normal cap moment plus the cap flux law forces every chord to have the same length. -/
theorem constant_norm_of_normal_moment_flux
    (o : Orientation ℝ Plane (Fin 2)) {e M : ℝ → Plane}
    (he : Differentiable ℝ e) (hne : ∀ t, e t ≠ 0)
    (hrot : ∀ t, o.areaForm (e t) (deriv e t) ≠ 0)
    (hflux : ∀ t, HasDerivAt M
      ((o.areaForm (e t) (deriv e t) / 12) • e t) t)
    (hnormal : ∀ t, ⟪e t, M t⟫_ℝ = 0) :
    ∃ l : ℝ, 0 < l ∧ ∀ t, ‖e t‖ = l := by
  have hmoment (t : ℝ) : M t = -(‖e t‖ ^ 2 / 12) • o.rightAngleRotation (e t) := by
    apply normal_moment_eq_of_inner_derivative o (hne t) (hrot t) (hnormal t)
    have hd := (he t).hasDerivAt.inner ℝ (hflux t)
    have hzero : (fun t => ⟪e t, M t⟫_ℝ) = fun _ => (0 : ℝ) := funext hnormal
    rw [hzero] at hd
    have hi := hd.unique (hasDerivAt_const t (0 : ℝ))
    simp only [real_inner_smul_right, real_inner_self_eq_norm_sq] at hi
    linarith
  have hnorm (t : ℝ) : ‖M t‖ = ‖e t‖ ^ 3 / 12 := by
    rw [hmoment t, norm_smul, Real.norm_eq_abs, abs_neg,
      abs_of_nonneg (by positivity : 0 ≤ ‖e t‖ ^ 2 / 12),
      o.rightAngleRotation.norm_map]
    ring
  have hd (t : ℝ) : HasDerivAt (fun t => ⟪M t, M t⟫_ℝ) 0 t := by
    have h := (hflux t).inner ℝ (hflux t)
    have hz : ⟪M t, e t⟫_ℝ = 0 := (real_inner_comm _ _).trans (hnormal t)
    simpa only [real_inner_smul_left, real_inner_smul_right,
      hz, hnormal t, mul_zero, add_zero] using h
  have henergy (t : ℝ) : ‖M t‖ ^ 2 = ‖M 0‖ ^ 2 := by
    simpa only [real_inner_self_eq_norm_sq] using
      is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
        (fun t => (hd t).deriv) t 0
  refine ⟨‖e 0‖, norm_pos_iff.mpr (hne 0), fun t => ?_⟩
  have hM : ‖M t‖ = ‖M 0‖ := by
    nlinarith [henergy t, norm_nonneg (M t), norm_nonneg (M 0)]
  rw [hnorm t, hnorm 0] at hM
  apply (pow_left_inj₀ (norm_nonneg (e t)) (norm_nonneg (e 0)) (by decide : (3 : ℕ) ≠ 0)).mp
  linarith

/-- The differential moment argument applies to the original convex boundary.
The flux equation is still an explicit hypothesis, to be supplied by cap integration. -/
theorem IsUnitSpeedBoundary.constantChord_of_normal_moment_flux
    {K : Set Plane} {P h : ℝ} {γ M : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hh : 0 < h) (hhP : h < P)
    (o : Orientation ℝ Plane (Fin 2))
    (ho : ∀ t x, x ∈ K → x ≠ γ t → 0 < o.areaForm (deriv γ t) (x - γ t))
    (hflux : ∀ t, HasDerivAt M
      ((o.areaForm (γ (t + h) - γ t)
        (deriv (fun s => γ (s + h) - γ s) t) / 12) • (γ (t + h) - γ t)) t)
    (hnormal : ∀ t, ⟪γ (t + h) - γ t, M t⟫_ℝ = 0) :
    ∃ l : ℝ, 0 < l ∧ HasConstantChord γ h l := by
  have he : Differentiable ℝ (fun s => γ (s + h) - γ s) :=
    ((hb.contDiff.differentiable (by simp)).comp (differentiable_id.add_const h)).sub
      (hb.contDiff.differentiable (by simp))
  obtain ⟨l, hl, hlength⟩ := constant_norm_of_normal_moment_flux o he
    (hb.chord_ne_zero hh hhP) (fun t => (hb.chord_turning_pos hh hhP o ho t).ne')
    hflux hnormal
  exact ⟨l, hl, fun t => by simpa only [dist_eq_norm] using hlength t⟩

end UlamFloating
