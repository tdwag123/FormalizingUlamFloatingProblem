import UlamFloating.Statements
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.RCLike.Real
import Mathlib.Topology.Order.Compact

/-!
# Recovering a ball from its boundary

These lemmas need neither a boundary parametrization nor convexity. A compact
set with nonempty interior whose frontier lies on a sphere is the corresponding
closed ball. The proof uses an extremum of distance and connectedness of the
open ball, so it applies in any nontrivial real normed space.
-/

namespace UlamFloating

open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- A compact nonempty set lies in any closed ball containing its frontier. -/
theorem subset_closedBall_of_frontier_subset {K : Set E} (hK : IsCompact K)
    (hne : K.Nonempty) {c : E} {r : ℝ} (hf : frontier K ⊆ closedBall c r) :
    K ⊆ closedBall c r := by
  obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne
    ((continuous_id.dist continuous_const).continuousOn :
      ContinuousOn (fun y : E => dist y c) K)
  have hbound : K ⊆ closedBall c (dist x c) := fun y hy => hmax hy
  have hxfront : x ∈ frontier K := by
    refine ⟨subset_closure hx, ?_⟩
    intro hxint
    have hlt : dist x c < dist x c := by
      simpa only [interior_closedBall', mem_ball] using interior_mono hbound hxint
    exact (lt_irrefl _) hlt
  intro y hy
  change dist y c ≤ r
  exact le_trans (hmax hy) (hf hxfront)

/-- A compact set with nonempty interior and frontier contained in a positive
radius sphere is exactly the closed ball. -/
theorem eq_closedBall_of_frontier_subset_sphere {K : Set E} (hK : IsCompact K)
    (hne : (interior K).Nonempty) {c : E} {r : ℝ} (hr : 0 < r)
    (hf : frontier K ⊆ sphere c r) : K = closedBall c r := by
  have hbound : K ⊆ closedBall c r :=
    subset_closedBall_of_frontier_subset hK (hne.mono interior_subset)
      (hf.trans sphere_subset_closedBall)
  have hcover : ball c r ⊆ interior K ∪ Kᶜ := by
    intro y hy
    by_cases hyK : y ∈ K
    · left
      by_contra hyint
      have heq : dist y c = r := hf ⟨subset_closure hyK, hyint⟩
      exact (ne_of_lt hy) heq
    · exact Or.inr hyK
  have hdisjoint : Disjoint (interior K) Kᶜ :=
    Set.disjoint_left.mpr (fun y hy hyc => hyc (interior_subset hy))
  have hinter : (ball c r ∩ interior K).Nonempty := by
    obtain ⟨y, hy⟩ := hne
    refine ⟨y, ?_, hy⟩
    simpa only [interior_closedBall'] using interior_mono hbound hy
  have hball : ball c r ⊆ interior K :=
    (convex_ball c r).isPreconnected.subset_left_of_subset_union
      isOpen_interior hK.isClosed.isOpen_compl hdisjoint hcover hinter
  apply Subset.antisymm hbound
  have hclosure := closure_mono (hball.trans interior_subset)
  simpa only [closure_ball c hr.ne', hK.isClosed.closure_eq] using hclosure

/-- The boundary-data version of the ball reconstruction theorem. -/
theorem IsUnitSpeedBoundary.eq_closedBall {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) {c : Plane} {r : ℝ}
    (hr : 0 < r) (hcircle : ∀ t, ‖γ t - c‖ = r) : K = closedBall c r := by
  apply eq_closedBall_of_frontier_subset_sphere hb.isCompact hb.interior_nonempty hr
  intro x hx
  rw [← hb.range_eq_frontier] at hx
  obtain ⟨t, rfl⟩ := hx
  exact (mem_sphere_iff_norm).mpr (hcircle t)

/-- Discharges the circle-boundary-to-disk specification. -/
theorem circle_boundary_disk : circleBoundaryDiskStatement := by
  intro K P γ hb c r hr hcircle
  exact hb.eq_closedBall hr hcircle

/-- A positive constant squared distance from the boundary to a point suffices
for disk rigidity. This avoids choosing a square-root expression upstream. -/
theorem IsUnitSpeedBoundary.isDisk_of_norm_sq {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) {c : Plane} {q : ℝ}
    (hq : 0 < q) (hsq : ∀ t, ‖γ t - c‖ ^ 2 = q) : IsDisk K := by
  refine ⟨c, Real.sqrt q, Real.sqrt_pos.mpr hq, hb.eq_closedBall
    (Real.sqrt_pos.mpr hq) ?_⟩
  intro t
  have hroot := Real.sq_sqrt hq.le
  have hn := norm_nonneg (γ t - c)
  have hr := Real.sqrt_nonneg q
  nlinarith [hsq t]

end UlamFloating
