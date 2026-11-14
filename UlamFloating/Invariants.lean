import UlamFloating.Carousel

/-!
# A dimension-independent signed-area cancellation

The finite-sum identity uses any skew bilinear form and any permutation of the
vertices. Applying it to the derivative of polygonal signed area is a separate
analytic step; no area conservation theorem is claimed by the identity alone.
-/

namespace UlamFloating

open scoped BigOperators

/-- The derivative-shaped sum for polygonal area vanishes under the midpoint
law. This algebraic core does not require equal edge lengths or convexity. -/
theorem sum_area_rate_eq_zero
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ)
    (hskew : ∀ x y, B x y = -B y x)
    (p v : ι → E)
    (hmid : ∀ i, ∃ a : ℝ, v i + v (next i) = a • (p (next i) - p i)) :
    ∑ i, (B (v i) (p (next i)) + B (p i) (v (next i))) = 0 := by
  have hdiag : ∀ x, B x x = 0 := by
    intro x
    have hx := hskew x x
    linarith
  have hedge : ∀ i, B (v i) (p (next i)) + B (p i) (v (next i)) =
      B (v i) (p i) - B (v (next i)) (p (next i)) := by
    intro i
    rcases hmid i with ⟨a, ha⟩
    have hz : B (v i + v (next i)) (p (next i) - p i) = 0 := by
      rw [ha, map_smul, LinearMap.smul_apply, hdiag, smul_zero]
    simp only [map_add, LinearMap.add_apply, map_sub] at hz
    rw [hskew (p i) (v (next i))]
    linarith
  simp_rw [hedge]
  rw [Finset.sum_sub_distrib, Equiv.sum_comp next (fun i => B (v i) (p i))]
  exact sub_self _

end UlamFloating
