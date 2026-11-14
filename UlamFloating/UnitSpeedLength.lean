import UlamFloating.Statements
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Metric length of unit-speed curves

A unit-speed differentiable curve has metric total variation equal to the
length of its parameter interval. The proof compares the difference quotients
of cumulative variation with the norms of the curve's difference quotients.
-/

namespace UlamFloating

open Set Filter
open scoped Topology ENNReal

/-- A one-Lipschitz curve has variation at most the parameter interval length. -/
theorem eVariationOn_le_of_one_lipschitz {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} (hf : LipschitzWith 1 f) (a b : ℝ) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (b - a) := by
  have hcomp := hf.lipschitzOnWith.comp_eVariationOn_le
    (g := fun t : ℝ => t) (s := Icc a b) (fun _ _ => mem_univ _)
  have hid := (monotone_id.monotoneOn univ : MonotoneOn (fun t : ℝ => t) univ).eVariationOn_le
    (mem_univ a) (mem_univ b)
  simp only [Function.comp_def, ENNReal.coe_one, one_mul] at hcomp
  exact hcomp.trans (by simpa only [univ_inter] using hid)

/-- On an ordered interval, signed variation of a one-Lipschitz curve lies
between its endpoint distance and the length of the interval. -/
theorem variation_bounds_of_one_lipschitz {E : Type*} [PseudoMetricSpace E]
    {f : ℝ → E} (hf : LipschitzWith 1 f)
    {a b : ℝ} (hab : a ≤ b) :
    dist (f b) (f a) ≤ variationOnFromTo f univ a b ∧
      variationOnFromTo f univ a b ≤ b - a := by
  rw [variationOnFromTo.eq_of_le f univ hab, univ_inter]
  have hu := eVariationOn_le_of_one_lipschitz hf a b
  have hfinite : eVariationOn f (Icc a b) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hu
  constructor
  · have h := ENNReal.toReal_mono hfinite
      (eVariationOn.edist_le f (show b ∈ Icc a b from ⟨hab, le_rfl⟩)
        (show a ∈ Icc a b from ⟨le_rfl, hab⟩))
    simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg] using h
  · have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hu
    simpa only [ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using h

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Difference quotients of cumulative variation dominate the norm of the
curve's difference quotients and are at most one. -/
theorem slope_variation_bounds {f : ℝ → E} (hf : LipschitzWith 1 f) (a t s : ℝ)
    (hst : s ≠ t) :
    ‖slope f t s‖ ≤ slope (variationOnFromTo f univ a) t s ∧
      slope (variationOnFromTo f univ a) t s ≤ 1 := by
  let v := variationOnFromTo f univ a
  have hadd (u w : ℝ) : v w - v u = variationOnFromTo f univ u w := by
    have h := variationOnFromTo.add (hf.locallyBoundedVariationOn univ)
      (mem_univ a) (mem_univ u) (mem_univ w)
    dsimp [v]
    linarith
  have hnorm : ‖slope f t s‖ = dist (f s) (f t) / |s - t| := by
    simp only [slope_def_module, norm_smul, norm_inv, Real.norm_eq_abs, dist_eq_norm]
    rw [div_eq_mul_inv, mul_comm]
  change ‖slope f t s‖ ≤ slope v t s ∧ slope v t s ≤ 1
  rw [hnorm, slope_def_field]
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · have hbounds := variation_bounds_of_one_lipschitz hf hlt.le
    rw [abs_of_neg (sub_neg.mpr hlt), neg_sub]
    rw [show v s - v t = -(v t - v s) by ring,
      show s - t = -(t - s) by ring, neg_div_neg_eq, hadd]
    constructor
    · exact (div_le_div_iff_of_pos_right (sub_pos.mpr hlt)).mpr
        (by simpa only [dist_comm] using hbounds.1)
    · exact (div_le_one (sub_pos.mpr hlt)).mpr hbounds.2
  · have hbounds := variation_bounds_of_one_lipschitz hf hgt.le
    rw [abs_of_pos (sub_pos.mpr hgt), hadd]
    exact ⟨(div_le_div_iff_of_pos_right (sub_pos.mpr hgt)).mpr hbounds.1,
      (div_le_one (sub_pos.mpr hgt)).mpr hbounds.2⟩

/-- Cumulative signed variation of a differentiable unit-speed curve has
derivative one. Continuity of the derivative is not required. -/
theorem hasDerivAt_variation_of_unit_speed {f : ℝ → E} (hf : Differentiable ℝ f)
    (hunit : ∀ t, ‖deriv f t‖ = 1) (a t : ℝ) :
    HasDerivAt (variationOnFromTo f univ a) 1 t := by
  have hlip : LipschitzWith 1 f := lipschitzWith_of_nnnorm_deriv_le hf
    (fun s => by exact_mod_cast (hunit s).le)
  apply hasDerivAt_iff_tendsto_slope.mpr
  have hlim : Tendsto (fun s => ‖slope f t s‖) (𝓝[≠] t) (𝓝 1) := by
    simpa only [hunit t] using (hasDerivAt_iff_tendsto_slope.mp (hf t).hasDerivAt).norm
  apply hlim.squeeze' tendsto_const_nhds
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (slope_variation_bounds hlip a t s hs).1
  · filter_upwards [self_mem_nhdsWithin] with s hs
    exact (slope_variation_bounds hlip a t s hs).2

/-- Signed variation of a differentiable unit-speed curve is the signed
length of its parameter interval, for either order of endpoints. -/
theorem variation_eq_sub_of_unit_speed {f : ℝ → E} (hf : Differentiable ℝ f)
    (hunit : ∀ t, ‖deriv f t‖ = 1) (a b : ℝ) :
    variationOnFromTo f univ a b = b - a := by
  have hd (t : ℝ) : HasDerivAt (fun s => variationOnFromTo f univ a s - s) 0 t := by
    simpa only [sub_self] using (hasDerivAt_variation_of_unit_speed hf hunit a t).sub (hasDerivAt_id t)
  have h := is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) b a
  simp only [variationOnFromTo.self] at h
  linarith

/-- Metric total variation of a unit-speed differentiable curve equals the
length of every ordered parameter interval. -/
theorem eVariationOn_eq_of_unit_speed {f : ℝ → E} (hf : Differentiable ℝ f)
    (hunit : ∀ t, ‖deriv f t‖ = 1) {a b : ℝ} (hab : a ≤ b) :
    eVariationOn f (Icc a b) = ENNReal.ofReal (b - a) := by
  have hlip : LipschitzWith 1 f := lipschitzWith_of_nnnorm_deriv_le hf
    (fun s => by exact_mod_cast (hunit s).le)
  have hfinite : eVariationOn f (Icc a b) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (eVariationOn_le_of_one_lipschitz hlip a b)
  have hv := variation_eq_sub_of_unit_speed hf hunit a b
  rw [variationOnFromTo.eq_of_le f univ hab, univ_inter] at hv
  rw [← ENNReal.ofReal_toReal hfinite, hv]

/-- The integral of speed over a unit-speed boundary traversal is its period. -/
theorem IsUnitSpeedBoundary.traversalLength_eq {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) : traversalLength γ P = P := by
  simp only [traversalLength, hb.unit_speed, intervalIntegral.integral_const,
    sub_zero, smul_eq_mul, mul_one]

/-- Discharges both the integral and metric length claims for a unit-speed boundary. -/
theorem unit_speed_boundary_length : unitSpeedBoundaryLengthStatement := by
  intro K P γ hb
  refine ⟨hb.traversalLength_eq, ?_⟩
  simpa only [sub_zero] using eVariationOn_eq_of_unit_speed
    (hb.contDiff.differentiable (by simp)) hb.unit_speed hb.period_pos.le

end UlamFloating
