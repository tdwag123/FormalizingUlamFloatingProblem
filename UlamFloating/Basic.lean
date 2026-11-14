import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Strict
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Perimetral chord geometry

The metric part of the API is independent of dimension and differentiability.
`HasPerimetralChordProperty` is a geometric condition, not a definition of physical
floating equilibrium. The bridge to hydrostatics is a separate proof obligation.
-/

namespace UlamFloating

section Metric

variable {E : Type*} [PseudoMetricSpace E]

/-- All chords of parameter increment `h` have the specified length `l`.
For a unit-speed boundary, `h` is an arc length. -/
def HasConstantChord (γ : ℝ → E) (h l : ℝ) : Prop :=
  ∀ t, dist (γ (t + h)) (γ t) = l

theorem HasConstantChord.nonneg {γ : ℝ → E} {h l : ℝ}
    (hc : HasConstantChord γ h l) : 0 ≤ l := by
  rw [← hc 0]
  exact dist_nonneg

theorem HasConstantChord.neg {γ : ℝ → E} {h l : ℝ}
    (hc : HasConstantChord γ h l) : HasConstantChord γ (-h) l := by
  intro t
  have ht := hc (t - h)
  simpa [sub_eq_add_neg, dist_comm] using ht

/-- Complementary arcs of a periodic curve determine the same chord lengths. -/
theorem HasConstantChord.complement {γ : ℝ → E} {P h l : ℝ}
    (hc : HasConstantChord γ h l) (hp : Function.Periodic γ P) :
    HasConstantChord γ (P - h) l := by
  intro t
  have he : t + (P - h) = (t - h) + P := by ring
  rw [he, hp (t - h)]
  simpa [sub_eq_add_neg] using hc.neg t

/-- Changing the starting point of a parametrization preserves its chord law. -/
theorem HasConstantChord.shift {γ : ℝ → E} {h l : ℝ}
    (hc : HasConstantChord γ h l) (a : ℝ) :
    HasConstantChord (fun t => γ (t + a)) h l := by
  intro t
  change dist (γ (t + h + a)) (γ (t + a)) = l
  have he : t + h + a = (t + a) + h := by ring
  rw [he]
  exact hc (t + a)

end Metric

/-- The Euclidean plane, with the Euclidean rather than product maximum norm. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- A compact strictly convex planar body with a once-traversed, `C¹`,
unit-speed periodic boundary parametrization of period `P`.

Existence of such a parametrization from an intrinsic regularity hypothesis is
not built into this structure as a theorem. It must be proved separately.
-/
structure IsUnitSpeedBoundary (K : Set Plane) (P : ℝ) (γ : ℝ → Plane) : Prop where
  isCompact : IsCompact K
  strictConvex : StrictConvex ℝ K
  interior_nonempty : (interior K).Nonempty
  period_pos : 0 < P
  contDiff : ContDiff ℝ 1 γ
  periodic : Function.Periodic γ P
  simple : ∀ s t, γ s = γ t ↔ ∃ k : ℤ, s = t + (k : ℝ) * P
  unit_speed : ∀ t, ‖deriv γ t‖ = 1
  range_eq_frontier : Set.range γ = frontier K

/-- The constant-chord formulation at perimetral density `σ`.
The parameter `σ` is not the area fraction or the material density. -/
def HasPerimetralChordProperty (K : Set Plane) (σ : ℝ) : Prop :=
  0 < σ ∧ σ < 1 ∧ ∃ P γ, IsUnitSpeedBoundary K P γ ∧
    ∃ l : ℝ, 0 < l ∧ HasConstantChord γ (σ * P) l

/-- A disk has positive radius and includes its boundary. -/
def IsDisk (K : Set Plane) : Prop :=
  ∃ c : Plane, ∃ r : ℝ, 0 < r ∧ K = Metric.closedBall c r

/-- The target proposition at a given perimetral density.
Defining this proposition does not prove it. -/
def PerimetralRigidity (σ : ℝ) : Prop :=
  ∀ K : Set Plane, HasPerimetralChordProperty K σ → IsDisk K

theorem HasPerimetralChordProperty.complement {K : Set Plane} {σ : ℝ}
    (h : HasPerimetralChordProperty K σ) : HasPerimetralChordProperty K (1 - σ) := by
  rcases h with ⟨hσ, hσ', P, γ, hb, l, hl, hc⟩
  refine ⟨by linarith, by linarith, P, γ, hb, l, hl, ?_⟩
  have he : (1 - σ) * P = P - σ * P := by ring
  rw [he]
  exact hc.complement hb.periodic

/-- A rigidity result automatically gives the complementary density. -/
theorem PerimetralRigidity.complement {σ : ℝ} (h : PerimetralRigidity σ) :
    PerimetralRigidity (1 - σ) := by
  intro K hK
  apply h K
  have hc := hK.complement
  simpa only [sub_sub_cancel] using hc

end UlamFloating
