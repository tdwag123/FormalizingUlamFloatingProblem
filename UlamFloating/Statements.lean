import UlamFloating.Geometry

/-!
# Exact specifications of the blueprint claims

Every declaration in this file has type `Prop`: it specifies a mathematical
statement and does NOT assert a proof of it. These specifications introduce no
axioms or admitted theorems. A proof will be a separately named theorem whose
type is the corresponding proposition. The blueprint must not mark these
specifications as proved merely because this file compiles.
-/

namespace UlamFloating

open MeasureTheory

/-- Arc-length normalization, including a genuine increasing reparametrization
and identification with metric total variation. -/
def arcLengthNormalizationStatement : Prop :=
  ∀ (K : Set Plane) (Q : ℝ) (φ : ℝ → Plane), IsRegularBoundary K Q φ →
    ∃ (P : ℝ) (γ : ℝ → Plane) (e : ℝ ≃o ℝ),
      P = traversalLength φ Q ∧ IsUnitSpeedBoundary K P γ ∧
      ContDiff ℝ 1 (fun t => e t) ∧ ContDiff ℝ 1 (fun t => e.symm t) ∧
      e 0 = 0 ∧ (∀ t, e (t + P) = e t + Q) ∧
      (∀ t, γ t = φ (e t)) ∧
      eVariationOn φ (Set.Icc 0 Q) = ENNReal.ofReal P

/-- A unit-speed traversal has metric length equal to its period. -/
def unitSpeedBoundaryLengthStatement : Prop :=
  ∀ (K : Set Plane) (P : ℝ) (γ : ℝ → Plane), IsUnitSpeedBoundary K P γ →
    traversalLength γ P = P ∧ eVariationOn γ (Set.Icc 0 P) = ENNReal.ofReal P

/-- Extraction includes cyclic indexing, strict convexity, and the one-curve
time-shift condition, in addition to the carousel laws. -/
def carouselExtractionStatement : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (K : Set Plane) (P : ℝ) (γ : ℝ → Plane) (l : ℝ),
    IsUnitSpeedBoundary K P γ → 0 < l → HasConstantChord γ (P / n) l →
      IsCarousel (finRotate n) (boundarySamples γ P n) l ∧
      (∀ t, IsStrictlyConvexPolygon (fun i => boundarySamples γ P n i t)) ∧
      ∀ i t, boundarySamples γ P n (finRotate n i) t =
        boundarySamples γ P n i (t + P / n)

/-- Signed area is conserved by any finite planar carousel. -/
def carouselAreaStatement : Prop :=
  ∀ (n : ℕ) (next : Equiv.Perm (Fin n)) (p : Fin n → ℝ → Plane) (l : ℝ),
    IsCarousel next p l → ∀ (o : Orientation ℝ Plane (Fin 2)) (s t : ℝ),
      polygonSignedArea next o (fun i => p i s) = polygonSignedArea next o (fun i => p i t)

/-- Signed first moment is conserved; equal edge lengths are retained. -/
def carouselFirstMomentStatement : Prop :=
  ∀ (n : ℕ) (next : Equiv.Perm (Fin n)) (p : Fin n → ℝ → Plane) (l : ℝ),
    IsCarousel next p l → ∀ (o : Orientation ℝ Plane (Fin 2)) (s t : ℝ),
      polygonFirstMoment next o (fun i => p i s) =
        polygonFirstMoment next o (fun i => p i t)

/-- The shoelace centroid agrees with the area centroid of the enclosed convex
polygon. The nonzero signed area conclusion handles either orientation. -/
def polygonCentroidStatement : Prop :=
  ∀ (n : ℕ) (p : Fin n → Plane), IsStrictlyConvexPolygon p →
    ∀ o : Orientation ℝ Plane (Fin 2),
      polygonSignedArea (finRotate n) o p ≠ 0 ∧
      polygonCentroid (finRotate n) o p = laminaCentroid (convexHull ℝ (Set.range p))

/-- The fixed signed centroid conclusion from the invariant blueprint node. -/
def carouselCentroidStatement : Prop :=
  ∀ (n : ℕ) (next : Equiv.Perm (Fin n)) (p : Fin n → ℝ → Plane) (l : ℝ),
    IsCarousel next p l → ∀ (o : Orientation ℝ Plane (Fin 2)),
      polygonSignedArea next o (fun i => p i 0) ≠ 0 →
      ∀ s t, polygonCentroid next o (fun i => p i s) =
        polygonCentroid next o (fun i => p i t)

/-- Equality of the body with the specified disk, not just circle containment. -/
def circleBoundaryDiskStatement : Prop :=
  ∀ (K : Set Plane) (P : ℝ) (γ : ℝ → Plane), IsUnitSpeedBoundary K P γ →
    ∀ (c : Plane) (r : ℝ), 0 < r → (∀ t, ‖γ t - c‖ = r) →
      K = Metric.closedBall c r

/-- Dimension-independent derivative estimate giving a period obstruction. -/
def periodBoundStatement : Prop :=
  ∀ (d : ℕ) (x : ℝ → EuclideanSpace ℝ (Fin d)) (T L : ℝ),
    ContDiff ℝ 2 x → Function.Periodic x T → 0 < T → 0 < L →
    (¬ ∃ c, ∀ t, x t = c) → (∀ t, ‖deriv (deriv x) t‖ ≤ L * ‖deriv x t‖) →
      2 * Real.pi / L ≤ T

/-- Fixed triangle center and its exact radius. -/
def triangleReductionStatement : Prop :=
  ∀ (K : Set Plane) (P : ℝ) (γ : ℝ → Plane) (l : ℝ),
    IsUnitSpeedBoundary K P γ → 0 < l → HasConstantChord γ (P / 3) l →
      ∃ c : Plane, ∀ (t : ℝ) (i : Fin 3),
        ‖boundarySamples γ P 3 i t - c‖ ^ 2 = l ^ 2 / 3

/-- Every quadrilateral is a square, with a single fixed center and radius. -/
def squareReductionStatement : Prop :=
  ∀ (K : Set Plane) (P : ℝ) (γ : ℝ → Plane) (l : ℝ),
    IsUnitSpeedBoundary K P γ → 0 < l → HasConstantChord γ (P / 4) l →
      (∀ t, IsRegularPolygon (fun i => boundarySamples γ P 4 i t)) ∧
      ∃ c : Plane, ∀ (t : ℝ) (i : Fin 4),
        ‖boundarySamples γ P 4 i t - c‖ ^ 2 = l ^ 2 / 2

/-- The genuine pentagon obstruction, without assuming the sought regularity. -/
def pentagonObstructionStatement : Prop :=
  ∀ (K : Set Plane) (P : ℝ) (γ : ℝ → Plane) (l : ℝ),
    IsUnitSpeedBoundary K P γ → 0 < l → HasConstantChord γ (P / 5) l →
      ∀ t, IsRegularPolygon (fun i => boundarySamples γ P 5 i t)

/-- The specification of geometric rigidity at perimetral density one third. -/
def thirdRigidityStatement : Prop := PerimetralRigidity (1 / 3)

/-- The specification of geometric rigidity at perimetral density one quarter. -/
def quarterRigidityStatement : Prop := PerimetralRigidity (1 / 4)

/-- The specification of geometric rigidity at perimetral density one fifth. -/
def fifthRigidityStatement : Prop := PerimetralRigidity (1 / 5)

/-- Auerbach's forward reduction, with the physical predicate independent of
the constant-chord property it is supposed to imply. -/
def hydrostaticReductionStatement : Prop :=
  ∀ (K : Set Plane) (σ : ℝ), FloatsWithPerimetralDensity K σ →
    HasPerimetralChordProperty K σ

/-- The combined physical target, for all three requested perimetral densities. -/
def physicalRigidityStatement : Prop :=
  ∀ (K : Set Plane) (σ : ℝ), (σ = 1 / 3 ∨ σ = 1 / 4 ∨ σ = 1 / 5) →
    FloatsWithPerimetralDensity K σ → IsDisk K

end UlamFloating
