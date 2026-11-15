import Seventh.Rigidity

/-!
# Expanded statement audit

This corollary exposes every geometric hypothesis of the boundary structure.
The only conclusion is that the original body is a positive-radius closed disk.
-/

namespace UlamFloating.Seventh

/-- Expanded form of the seventh-density theorem, exposing all input hypotheses. -/
theorem rigidity_expanded (K : Set Plane) (P l : ℝ) (γ : ℝ → Plane)
    (hcompact : IsCompact K) (hconvex : StrictConvex ℝ K)
    (hinterior : (interior K).Nonempty) (hP : 0 < P)
    (hregular : ContDiff ℝ 1 γ) (hperiodic : Function.Periodic γ P)
    (hsimple : ∀ s t, γ s = γ t ↔ ∃ k : ℤ, s = t + (k : ℝ) * P)
    (hspeed : ∀ t, ‖deriv γ t‖ = 1) (hboundary : Set.range γ = frontier K)
    (hl : 0 < l) (hchord : ∀ t, dist (γ (t + P / 7)) (γ t) = l) :
    ∃ center : Plane, ∃ radius : ℝ, 0 < radius ∧ K = Metric.closedBall center radius := by
  exact rigidity_of_boundary
    ⟨hcompact, hconvex, hinterior, hP, hregular, hperiodic, hsimple, hspeed, hboundary⟩ hl hchord

end UlamFloating.Seventh
