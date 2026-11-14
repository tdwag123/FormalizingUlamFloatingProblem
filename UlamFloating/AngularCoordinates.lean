import UlamFloating.ChordRotation
import UlamFloating.IntegralCoordinates
import UlamFloating.PeriodicAnalysis
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Global angular coordinates from the rotation equation

Integrating angular speed gives a global real angle. The reconstruction
formula is proved by differentiating in a rotating frame, without a branch
of the argument function or an assumed winding number.
-/

namespace UlamFloating

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- A solution of the planar rotation equation is reconstructed from any
primitive of its angular speed that vanishes at zero. -/
theorem rotation_solution_eq (o : Orientation ℝ E (Fin 2))
    {e : ℝ → E} {θ a : ℝ → ℝ} (hθ : ∀ t, HasDerivAt θ (a t) t)
    (hθ0 : θ 0 = 0) (he : ∀ t, HasDerivAt e (a t • o.rightAngleRotation (e t)) t)
    (t : ℝ) : e t = Real.cos (θ t) • e 0 + Real.sin (θ t) • o.rightAngleRotation (e 0) := by
  let y : ℝ → E := fun s =>
    Real.cos (θ s) • e s - Real.sin (θ s) • o.rightAngleRotation (e s)
  have hy (s : ℝ) : HasDerivAt y 0 s := by
    have hj := o.rightAngleRotation.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt
      s (he s)
    change HasDerivAt (fun r => o.rightAngleRotation (e r))
      (o.rightAngleRotation (a s • o.rightAngleRotation (e s))) s at hj
    simp only [map_smul, o.rightAngleRotation_rightAngleRotation] at hj
    have hd := ((hθ s).cos.fun_smul (he s)).sub ((hθ s).sin.fun_smul hj)
    convert hd using 1
    module
  have hconst : y t = e 0 := by
    have h := is_const_of_deriv_eq_zero (fun s => (hy s).differentiableAt)
      (fun s => (hy s).deriv) t 0
    simpa only [y, hθ0, Real.cos_zero, Real.sin_zero, one_smul, zero_smul, sub_zero] using h
  calc
    e t = (Real.cos (θ t) ^ 2 + Real.sin (θ t) ^ 2) • e t := by
      rw [Real.cos_sq_add_sin_sq, one_smul]
    _ = Real.cos (θ t) • y t + Real.sin (θ t) • o.rightAngleRotation (y t) := by
      dsimp [y]
      simp only [map_sub, map_smul, o.rightAngleRotation_rightAngleRotation]
      module
    _ = _ := by rw [hconst]

/-- A continuous angular speed gives a global integral reconstruction of
every solution of its planar rotation equation. -/
theorem rotation_solution_eq_integral (o : Orientation ℝ E (Fin 2))
    {e : ℝ → E} {a : ℝ → ℝ} (ha : Continuous a)
    (he : ∀ t, HasDerivAt e (a t • o.rightAngleRotation (e t)) t) (t : ℝ) :
    e t = Real.cos (∫ s in (0 : ℝ)..t, a s) • e 0 +
      Real.sin (∫ s in (0 : ℝ)..t, a s) • o.rightAngleRotation (e 0) := by
  exact rotation_solution_eq o (fun s => (ha.integral_hasStrictDerivAt 0 s).hasDerivAt)
    (by simp) he t

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Constant positive boundary chords admit increasing global real angular
coordinates, with `C¹` inverse, bounded positive angular speed, and an
integer-period shift law. No winding number is assumed in this statement. -/
theorem IsUnitSpeedBoundary.chord_angle_coordinates {K : Set Plane} {P h l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ h l) :
    ∃ (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ),
      ContDiff ℝ 1 (fun t => θ t) ∧ ContDiff ℝ 1 (fun t => θ.symm t) ∧ θ 0 = 0 ∧
      (∀ t, 0 < deriv (fun s => θ s) t ∧ deriv (fun s => θ s) t ≤ 2 / l) ∧
      (∀ t, γ (t + h) - γ t = Real.cos (θ t) • (γ h - γ 0) +
        Real.sin (θ t) • o.rightAngleRotation (γ h - γ 0)) ∧
      (∀ t (k : ℤ), θ (t + (k : ℝ) * P) = θ t + (k : ℝ) * θ P) := by
  obtain ⟨o, ho⟩ := hb.chord_rotation hl hc
  let e : ℝ → Plane := fun t => γ (t + h) - γ t
  let a : ℝ → ℝ := fun t => 2 * o.areaForm (deriv γ t) (e t) / l ^ 2
  have he : ∀ t, HasDerivAt e (a t • o.rightAngleRotation (e t)) t := fun t => (ho t).1
  have hpos : ∀ t, 0 < a t := fun t => (ho t).2.1
  have hbound : ∀ t, a t ≤ 2 / l := fun t => (ho t).2.2
  have hce : Continuous e :=
    (hb.contDiff.continuous.comp (continuous_id.add continuous_const)).sub hb.contDiff.continuous
  have hca : Continuous a := by
    have hA : Continuous (fun t => o.areaForm (deriv γ t) (e t)) := by
      simpa only [Function.comp_apply, Orientation.areaForm'_apply] using
        (o.areaForm'.continuous.comp hb.contDiff.continuous_deriv_one).clm_apply hce
    exact (continuous_const.mul hA).div_const _
  have hep : Function.Periodic e P := by
    intro t
    dsimp [e]
    rw [show t + P + h = (t + h) + P by ring, hb.periodic, hb.periodic]
  have hap : Function.Periodic a P := by
    intro t
    dsimp [a]
    rw [periodic_deriv hb.periodic (hb.contDiff.differentiable (by simp)) t, hep]
  obtain ⟨θ, hθ, hθc, hθinv, hd, _⟩ := exists_integral_orderIso hca hpos hap hb.period_pos
  have hθ0 : θ 0 = 0 := by rw [hθ]; simp
  refine ⟨o, θ, hθc, hθinv, hθ0, ?_, ?_, ?_⟩
  · intro t
    rw [(hd t).deriv]
    exact ⟨hpos t, hbound t⟩
  · intro t
    simpa only [e, zero_add] using rotation_solution_eq o hd hθ0 he t
  · intro t k
    simp only [hθ]
    exact integral_add_int_mul_period hca hap t k

end UlamFloating
