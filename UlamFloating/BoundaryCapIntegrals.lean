import UlamFloating.MomentConservation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Moving boundary-arc integrals

The signed area and first-moment expressions for an arc closed by its chord
are defined here as line integrals. Their identification with planar volume
and its first moment is a separate Green-formula obligation; it is not a
definitional equality. The differential identities use only a C¹ curve.
-/

noncomputable section

namespace UlamFloating

open MeasureTheory
open scoped InnerProductSpace

section MovingInterval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Translating both endpoints of an integral gives the difference of endpoint values. -/
theorem hasDerivAt_integral_translate {f : ℝ → E} (hf : Continuous f) (h t : ℝ) :
    HasDerivAt (fun s => ∫ x in s..s + h, f x) (f (t + h) - f t) t := by
  have hd (b : ℝ) := intervalIntegral.integral_hasDerivAt_right
    (hf.intervalIntegrable 0 b) hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hshift := (hd (t + h)).scomp t ((hasDerivAt_id t).add_const h)
  have hdiff := hshift.sub (hd t)
  simp only [one_smul] at hdiff
  convert hdiff using 1
  funext s
  apply (eq_sub_iff_add_eq).mpr
  simpa only [add_comm] using intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable 0 s) (hf.intervalIntegrable s (s + h))

end MovingInterval

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Signed line-integral area of a boundary arc closed by its chord. -/
def boundaryCapArea (o : Orientation ℝ Plane (Fin 2)) (γ : ℝ → Plane) (h t : ℝ) : ℝ :=
  (1 / 2 : ℝ) * ((∫ s in t..t + h, o.areaForm (γ s) (deriv γ s)) -
    o.areaForm (γ t) (γ (t + h)))

/-- Signed line-integral first moment of the same closed arc. -/
def boundaryCapMoment (o : Orientation ℝ Plane (Fin 2)) (γ : ℝ → Plane) (h t : ℝ) : Plane :=
  (1 / 3 : ℝ) • (∫ s in t..t + h, o.areaForm (γ s) (deriv γ s) • γ s) -
    (1 / 6 : ℝ) • (o.areaForm (γ t) (γ (t + h)) • (γ t + γ (t + h)))

/-- The area derivative depends only on the chord and the endpoint velocity sum. -/
theorem hasDerivAt_boundaryCapArea (o : Orientation ℝ Plane (Fin 2))
    {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ) (h t : ℝ) :
    HasDerivAt (boundaryCapArea o γ h)
      ((1 / 2 : ℝ) * o.areaForm (γ (t + h) - γ t)
        (deriv γ t + deriv γ (t + h))) t := by
  have hc : Continuous (fun s => o.areaForm (γ s) (deriv γ s)) :=
    (o.areaForm'.continuous.comp hγ.continuous).clm_apply hγ.continuous_deriv_one
  have hp := (hγ.differentiable (by simp) t).hasDerivAt
  have hq := ((hγ.differentiable (by simp) (t + h)).hasDerivAt).scomp t
    ((hasDerivAt_id t).add_const h)
  simp only [one_smul] at hq
  have he := o.areaForm'.hasDerivAt_of_bilinear hp hq
  have hd := ((hasDerivAt_integral_translate hc h t).sub he).const_mul (1 / 2)
  convert hd using 1
  change (1 / 2 : ℝ) * o.areaForm (γ (t + h) - γ t)
      (deriv γ t + deriv γ (t + h)) =
    (1 / 2 : ℝ) * (o.areaForm (γ (t + h)) (deriv γ (t + h)) -
      o.areaForm (γ t) (deriv γ t) - (o.areaForm (γ t) (deriv γ (t + h)) +
        o.areaForm (deriv γ t) (γ (t + h))))
  simp only [map_sub, LinearMap.sub_apply, map_add, o.areaForm_swap (deriv γ t) (γ (t + h))]
  ring

/-- An edge-parallel midpoint velocity preserves the boundary-arc area expression. -/
theorem boundaryCapArea_eq_of_midpoint_parallel (o : Orientation ℝ Plane (Fin 2))
    {γ : ℝ → Plane} (hγ : ContDiff ℝ 1 γ) (h : ℝ)
    (hmid : ∀ t, ∃ a : ℝ,
      deriv γ t + deriv γ (t + h) = a • (γ (t + h) - γ t)) (s t : ℝ) :
    boundaryCapArea o γ h s = boundaryCapArea o γ h t := by
  have hd (t : ℝ) : HasDerivAt (boundaryCapArea o γ h) 0 t := by
    obtain ⟨a, ha⟩ := hmid t
    simpa only [ha, map_smul, smul_eq_mul, o.areaForm_apply_self, mul_zero] using
      hasDerivAt_boundaryCapArea o hγ h t
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

/-- Under the midpoint law, the first-moment derivative is an endpoint correction. -/
theorem hasDerivAt_boundaryCapMoment_of_midpoint_parallel
    (o : Orientation ℝ Plane (Fin 2)) {γ : ℝ → Plane}
    (hγ : ContDiff ℝ 1 γ) (h t : ℝ)
    (hmid : ∃ a : ℝ, deriv γ t + deriv γ (t + h) = a • (γ (t + h) - γ t)) :
    HasDerivAt (boundaryCapMoment o γ h)
      ((1 / 6 : ℝ) • (o.areaForm (deriv γ t) (γ (t + h) - γ t) •
        (γ (t + h) - γ t))) t := by
  have hc : Continuous (fun s => o.areaForm (γ s) (deriv γ s) • γ s) :=
    ((o.areaForm'.continuous.comp hγ.continuous).clm_apply
      hγ.continuous_deriv_one).smul hγ.continuous
  have hp := (hγ.differentiable (by simp) t).hasDerivAt
  have hq := ((hγ.differentiable (by simp) (t + h)).hasDerivAt).scomp t
    ((hasDerivAt_id t).add_const h)
  simp only [one_smul] at hq
  have he := (o.areaForm'.hasDerivAt_of_bilinear hp hq).smul (hp.add hq)
  have hd := ((hasDerivAt_integral_translate hc h t).const_smul (1 / 3 : ℝ)).sub
    (he.const_smul (1 / 6 : ℝ))
  have halg := moment_edge_rate o hmid
  rw [o.areaForm_swap (deriv γ t) (γ t),
    o.areaForm_swap (deriv γ (t + h)) (γ (t + h))] at halg
  convert hd using 1
  change (1 / 6 : ℝ) • (o.areaForm (deriv γ t) (γ (t + h) - γ t) •
      (γ (t + h) - γ t)) =
    (1 / 3 : ℝ) • (o.areaForm (γ (t + h)) (deriv γ (t + h)) • γ (t + h) -
      o.areaForm (γ t) (deriv γ t) • γ t) -
    (1 / 6 : ℝ) • (o.areaForm (γ t) (γ (t + h)) • (deriv γ t + deriv γ (t + h)) +
      (o.areaForm (γ t) (deriv γ (t + h)) + o.areaForm (deriv γ t) (γ (t + h))) •
        (γ t + γ (t + h)))
  rw [add_comm (o.areaForm (γ t) (γ (t + h)) • _),
    add_comm (o.areaForm (γ t) (deriv γ (t + h))), halg]
  module

/-- For constant chords, the rotating correction to the cap moment is constant. -/
theorem boundaryCapMoment_add_rotation_eq
    (o : Orientation ℝ Plane (Fin 2)) {γ : ℝ → Plane}
    (hγ : ContDiff ℝ 1 γ) {h l : ℝ} (hchord : HasConstantChord γ h l)
    (hmid : ∀ t, ∃ a : ℝ, deriv γ t + deriv γ (t + h) = a • (γ (t + h) - γ t))
    (s t : ℝ) :
    boundaryCapMoment o γ h s + (l ^ 2 / 12) • o.rightAngleRotation (γ (s + h) - γ s) =
      boundaryCapMoment o γ h t + (l ^ 2 / 12) • o.rightAngleRotation (γ (t + h) - γ t) := by
  have hd (t : ℝ) : HasDerivAt
      (fun t => boundaryCapMoment o γ h t +
        (l ^ 2 / 12) • o.rightAngleRotation (γ (t + h) - γ t)) 0 t := by
    have hp := (hγ.differentiable (by simp) t).hasDerivAt
    have hq := ((hγ.differentiable (by simp) (t + h)).hasDerivAt).scomp t
      ((hasDerivAt_id t).add_const h)
    simp only [one_smul] at hq
    have horth := inner_edge_velocity_eq_zero hp hq (by
      intro r
      simpa only [dist_eq_norm, Function.comp_apply, id_eq] using hchord r)
    have halg := areaForm_smul_eq_velocity_difference o horth (hmid t)
    have hn : ‖γ (t + h) - γ t‖ = l := by simpa only [dist_eq_norm] using hchord t
    have hrot := ((o.rightAngleRotation.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt
      t (hq.sub hp)).const_smul (l ^ 2 / 12)
    have hs := (hasDerivAt_boundaryCapMoment_of_midpoint_parallel o hγ h t (hmid t)).add hrot
    convert hs using 1
    change (0 : Plane) = (1 / 6 : ℝ) •
      (o.areaForm (deriv γ t) (γ (t + h) - γ t) • (γ (t + h) - γ t)) +
        (l ^ 2 / 12) • o.rightAngleRotation (deriv γ (t + h) - deriv γ t)
    change o.areaForm (deriv γ t) (γ (t + h) - γ t) • (γ (t + h) - γ t) = _ at halg
    dsimp only [Function.comp_apply, id_eq] at halg
    rw [hn] at halg
    rw [halg, map_sub]
    module
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

end UlamFloating
