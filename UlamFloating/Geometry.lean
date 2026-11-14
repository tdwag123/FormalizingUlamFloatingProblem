import UlamFloating.Sampling
import UlamFloating.Carousel
import Mathlib.Analysis.InnerProductSpace.TwoDim
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.EMetricSpace.BoundedVariation

/-!
# Geometric and physical interfaces for the remaining blueprint statements

These definitions record geometric data, not rigidity conclusions. In particular,
floating equilibrium is expressed using cap areas and centroids, without assuming
constant chord lengths. Signed polygon moments use mathlib's oriented area form.
-/

noncomputable section

namespace UlamFloating

open scoped BigOperators InnerProductSpace
open MeasureTheory

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The oriented Euclidean area form, specialized from mathlib to the plane. -/
def planeAreaForm (o : Orientation ℝ Plane (Fin 2)) : Plane →ₗ[ℝ] Plane →ₗ[ℝ] ℝ :=
  o.areaForm

/-- A once-traversed regular boundary, before choosing an arc-length parameter. -/
structure IsRegularBoundary (K : Set Plane) (Q : ℝ) (φ : ℝ → Plane) : Prop where
  isCompact : IsCompact K
  strictConvex : StrictConvex ℝ K
  interior_nonempty : (interior K).Nonempty
  period_pos : 0 < Q
  contDiff : ContDiff ℝ 1 φ
  periodic : Function.Periodic φ Q
  simple : ∀ s t, φ s = φ t ↔ ∃ k : ℤ, s = t + (k : ℝ) * Q
  regular : ∀ t, deriv φ t ≠ 0
  range_eq_frontier : Set.range φ = frontier K

/-- Integral of speed over one specified traversal. -/
def traversalLength (φ : ℝ → Plane) (Q : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..Q, ‖deriv φ t‖

/-- The finite-indexed rational sampling of a boundary. -/
def boundarySamples {E : Type*} (γ : ℝ → E) (P : ℝ) (n : ℕ) : Fin n → ℝ → E :=
  fun i t => sampledVertex γ (P / n) t i.val

/-- A cyclically ordered strictly convex polygon: every remaining vertex lies
strictly on the same oriented side of each edge. The orientation may be either
choice; no orientation is imposed on the input boundary parametrization. -/
def IsStrictlyConvexPolygon {n : ℕ} (p : Fin n → Plane) : Prop :=
  3 ≤ n ∧ Function.Injective p ∧ ∃ o : Orientation ℝ Plane (Fin 2),
    ∀ i j, j ≠ i → j ≠ finRotate n i →
      0 < planeAreaForm o (p (finRotate n i) - p i) (p j - p i)

/-- A regular polygon in cyclic order, characterized by its circumradius and
all pairwise chord distances. This allows either orientation and arbitrary center.
The complete distance formula excludes star-order labelings. -/
def IsRegularPolygon {n : ℕ} (p : Fin n → Plane) : Prop :=
  3 ≤ n ∧ ∃ c : Plane, ∃ r : ℝ, 0 < r ∧
    (∀ i, dist (p i) c = r) ∧
    ∀ i j, dist (p i) (p j) ^ 2 =
      2 * r ^ 2 * (1 - Real.cos (2 * Real.pi * ((i.val : ℝ) - j.val) / n))

/-- Signed polygon area, allowing any finite successor permutation. -/
def polygonSignedArea {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ Plane (Fin 2)) (p : ι → Plane) : ℝ :=
  (1 / 2 : ℝ) * ∑ i, planeAreaForm o (p i) (p (next i))

/-- Signed first moment about the origin. This is not the sum of the vertices. -/
def polygonFirstMoment {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ Plane (Fin 2)) (p : ι → Plane) : Plane :=
  (1 / 6 : ℝ) • ∑ i, planeAreaForm o (p i) (p (next i)) • (p i + p (next i))

/-- The signed moment divided by signed area; used geometrically only after
the signed area is shown to be nonzero. -/
def polygonCentroid {ι : Type*} [Fintype ι] (next : Equiv.Perm ι)
    (o : Orientation ℝ Plane (Fin 2)) (p : ι → Plane) : Plane :=
  (polygonSignedArea next o p)⁻¹ • polygonFirstMoment next o p

/-- Unsigned planar area. Applications establish finite measure separately. -/
def planarArea (K : Set Plane) : ℝ := (volume K).toReal

/-- Centroid of uniform planar area measure, used for positive finite-area sets. -/
def laminaCentroid (K : Set Plane) : Plane :=
  (planarArea K)⁻¹ • ∫ x in K, x

/-- The portion of a body on the lower side of a specified oriented waterline. -/
def waterlineCap (K : Set Plane) (u : Plane) (a : ℝ) : Set Plane :=
  K ∩ {x | ⟪u, x⟫_ℝ ≤ a}

/-- Hydrostatic equilibrium at a cut: fixed area fraction and zero torque
about the body's centroid. The centroid displacement is normal to the waterline. -/
def IsEquilibriumCut (K : Set Plane) (ρ : ℝ) (u : Plane) (a : ℝ) : Prop :=
  ‖u‖ = 1 ∧ planarArea (waterlineCap K u a) = ρ * planarArea K ∧
    ∃ b : ℝ, laminaCentroid (waterlineCap K u a) - laminaCentroid K = b • u

/-- Floating at a prescribed perimetral fraction. One material/area density `ρ`
works for all cuts. Every boundary parameter gives an equilibrium chord, and
every oriented normal occurs. No constant-length hypothesis is included. -/
def FloatsWithPerimetralDensity (K : Set Plane) (σ : ℝ) : Prop :=
  0 < σ ∧ σ < 1 ∧ ∃ P γ, IsUnitSpeedBoundary K P γ ∧
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      (∀ t, ∃ u a, IsEquilibriumCut K ρ u a ∧
        ⟪u, γ t⟫_ℝ = a ∧ ⟪u, γ (t + σ * P)⟫_ℝ = a) ∧
      (∀ u : Plane, ‖u‖ = 1 → ∃ t a, IsEquilibriumCut K ρ u a ∧
        ⟪u, γ t⟫_ℝ = a ∧ ⟪u, γ (t + σ * P)⟫_ℝ = a)

end UlamFloating
