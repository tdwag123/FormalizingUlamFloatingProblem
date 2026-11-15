import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Differentiating bounded integrals with a moving cut

The primitive of a bounded integrable function is Lipschitz even if the
integrand is discontinuous away from the cut. This permits differentiation
under the outer integral at a flat waterline: only almost-everywhere continuity
on that waterline is needed.
-/

namespace UlamFloating

open MeasureTheory Set Filter Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A uniformly bounded locally integrable function has a Lipschitz primitive. -/
theorem lipschitzWith_integral_primitive {f : ℝ → E} {M : ℝ≥0}
    (hint : ∀ a b, IntervalIntegrable f volume a b)
    (hbound : ∀ x, ‖f x‖ ≤ M) (a : ℝ) :
    LipschitzWith M (fun b => ∫ x in a..b, f x) := by
  apply LipschitzWith.of_dist_le_mul
  intro b c
  rw [dist_eq_norm, Real.dist_eq, intervalIntegral.integral_interval_sub_left
    (hint a b) (hint a c)]
  exact intervalIntegral.norm_integral_le_of_norm_le_const (fun x _ => hbound x)

variable [CompleteSpace E]

/-- A moving upper limit differentiates against the density at the cut. -/
theorem hasDerivAt_integral_moving_upper {f : ℝ → E} {b : ℝ → ℝ}
    {b' a t : ℝ} (hint : IntervalIntegrable f volume a (b t))
    (hmeas : StronglyMeasurable f) (hf : ContinuousAt f (b t))
    (hb : HasDerivAt b b' t) :
    HasDerivAt (fun s => ∫ x in a..b s, f x) (b' • f (b t)) t :=
  (intervalIntegral.integral_hasDerivAt_right hint hmeas.stronglyMeasurableAtFilter hf).scomp t hb

/-- Differentiation of sliced integrals at a flat moving cut. The integrand may
have discontinuities elsewhere, as occurs for the indicator of a convex body. -/
theorem hasDerivAt_integral_slices_moving_cut
    {X : Type*} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {f : X → ℝ → E} {b : ℝ → X → ℝ} {v : X → ℝ} {t a ε : ℝ}
    {M L : ℝ≥0} (hε : 0 < ε)
    (hint : ∀ x r s, IntervalIntegrable (f x) volume r s)
    (hmeas : ∀ x, StronglyMeasurable (f x))
    (hbound : ∀ x y, ‖f x y‖ ≤ M)
    (hcut : ∀ x, b t x = 0)
    (hFmeas : ∀ s, AEStronglyMeasurable (fun x => ∫ y in a..b s x, f x y) μ)
    (hvmeas : AEStronglyMeasurable (fun x => v x • f x 0) μ)
    (hblip : ∀ᵐ x ∂μ, LipschitzOnWith L (fun s => b s x) (ball t ε))
    (hbdiff : ∀ᵐ x ∂μ, HasDerivAt (fun s => b s x) (v x) t)
    (hcont : ∀ᵐ x ∂μ, ContinuousAt (f x) 0) :
    HasDerivAt (fun s => ∫ x, ∫ y in a..b s x, f x y ∂volume ∂μ)
      (∫ x, v x • f x 0 ∂μ) t := by
  have hFint : Integrable (fun x => ∫ y in a..b t x, f x y) μ := by
    apply (integrable_const ((M : ℝ) * |a|)).mono' (hFmeas t)
    apply Eventually.of_forall
    intro x
    rw [hcut]
    simpa only [zero_sub, abs_neg] using
      intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := 0)
        (fun y _ => hbound x y)
  have hLip : ∀ᵐ x ∂μ, LipschitzOnWith (Real.nnabs ((M : ℝ) * L))
      (fun s => ∫ y in a..b s x, f x y) (ball t ε) := by
    filter_upwards [hblip] with x hx
    have hp := lipschitzWith_integral_primitive (hint x) (hbound x) a
    convert hp.comp_lipschitzOnWith hx using 1
    simp
  have hdiff : ∀ᵐ x ∂μ, HasDerivAt (fun s => ∫ y in a..b s x, f x y)
      (v x • f x 0) t := by
    filter_upwards [hbdiff, hcont] with x hx hc
    have hcf : ContinuousAt (f x) (b t x) := by simpa only [hcut] using hc
    simpa only [hcut] using hasDerivAt_integral_moving_upper
      (b := fun s => b s x) (t := t) (a := a) (hint x a (b t x))
      (hmeas x) hcf hx
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (F := fun s x => ∫ y in a..b s x, f x y) (bound := fun _ => (M : ℝ) * L) hε
    (Eventually.of_forall hFmeas) hFint hvmeas hLip (integrable_const _) hdiff).2

end UlamFloating
