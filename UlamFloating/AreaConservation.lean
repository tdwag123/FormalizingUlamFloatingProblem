import UlamFloating.Invariants
import UlamFloating.Statements
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Conservation of signed polygon area

The analytic core is stated for an arbitrary continuous skew bilinear form on
a real normed space. Neither equal lengths nor convexity are needed for area
conservation: differentiability and the midpoint-parallel law suffice.
-/

namespace UlamFloating

open scoped BigOperators

/-- A cyclic sum of values of a continuous skew bilinear form is constant when
successive velocity sums are parallel to the corresponding edges. -/
theorem sum_bilinear_apply_const_of_midpoint_parallel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (B : E →L[ℝ] E →L[ℝ] ℝ) (hskew : ∀ x y, B x y = -B y x)
    (p : ι → ℝ → E) (hp : ∀ i, Differentiable ℝ (p i))
    (hmid : ∀ i t, ∃ a : ℝ,
      deriv (p i) t + deriv (p (next i)) t = a • (p (next i) t - p i t))
    (s t : ℝ) :
    ∑ i, B (p i s) (p (next i) s) = ∑ i, B (p i t) (p (next i) t) := by
  have hd : ∀ t, HasDerivAt (fun t => ∑ i, B (p i t) (p (next i) t)) 0 t := by
    intro t
    have hedge (i : ι) := B.hasDerivAt_of_bilinear
      (hp i t).hasDerivAt (hp (next i) t).hasDerivAt
    have hsum := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hedge i)
    have hz : (∑ i, (B (p i t) (deriv (p (next i)) t) +
        B (deriv (p i) t) (p (next i) t))) = 0 := by
      simpa only [ContinuousLinearMap.toLinearMap₁₂_apply, add_comm] using
        sum_area_rate_eq_zero next B.toLinearMap₁₂ hskew
          (fun i => p i t) (fun i => deriv (p i) t) (fun i => hmid i t)
    rw [hz] at hsum
    exact hsum
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The signed area of a finite planar carousel is constant in time. -/
theorem IsCarousel.polygonSignedArea_eq
    {ι : Type*} [Fintype ι] {next : Equiv.Perm ι} {p : ι → ℝ → Plane} {l : ℝ}
    (hc : IsCarousel next p l) (o : Orientation ℝ Plane (Fin 2)) (s t : ℝ) :
    polygonSignedArea next o (fun i => p i s) =
      polygonSignedArea next o (fun i => p i t) := by
  have h := sum_bilinear_apply_const_of_midpoint_parallel next o.areaForm'
    (fun x y => o.areaForm_swap x y) p
    (fun i => (hc.contDiff i).differentiable (by simp)) hc.midpoint_parallel s t
  exact congrArg (fun a : ℝ => (1 / 2 : ℝ) * a) h

/-- Discharges the signed-area conservation specification in the blueprint. -/
theorem carousel_area : carouselAreaStatement := by
  intro n next p l hc o s t
  exact hc.polygonSignedArea_eq o s t

end UlamFloating
