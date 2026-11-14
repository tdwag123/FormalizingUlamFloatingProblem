import UlamFloating.Zindler
import UlamFloating.Rigidity

/-!
# The physical Zindler equivalence: specification and conditional consequences

Theorem 2 and Remark 3 of Asipchuk--Kosmakov--Zatitskii,
`https://arxiv.org/abs/2604.10330`, motivate the specification below. It uses
the given boundary parametrization, not an unspecified replacement. The
Zindler side is equivalent to a single positive constant chord length; strict
convexity and the midpoint law follow from the geometric construction.

The physical equivalence is NOT proved here. Definitions ending in `Statement`
only specify propositions. The assembly theorems retain the missing physical
input as an explicit premise and do not depend on the fifth-density result.
-/

namespace UlamFloating

/-- Physical floating is equivalent to the Zindler construction on any specified
unit-speed boundary, for every polygon size `n ≥ 3`. Both physical directions
remain proof obligations. Material density is existential in the physical predicate. -/
def zindlerEquivalenceStatement : Prop :=
  ∀ (n : ℕ), 3 ≤ n → ∀ (K : Set Plane) (P : ℝ) (γ : ℝ → Plane),
    IsUnitSpeedBoundary K P γ →
      (FloatsWithPerimetralDensity K (1 / (n : ℝ)) ↔
        ∃ l : ℝ, IsZindlerCarousel (boundarySamples γ P n) l)

/-- The physical conclusions for one third and one quarter, independent of the
unfinished fifth-density problem. This definition is not a proof. -/
def physicalThirdQuarterRigidityStatement : Prop :=
  ∀ (K : Set Plane) (σ : ℝ), (σ = 1 / 3 ∨ σ = 1 / 4) →
    FloatsWithPerimetralDensity K σ → IsDisk K

/-- The specified Zindler equivalence has exactly the constant-chord geometric
content of the cited theorem, on the same boundary parametrization. -/
theorem zindlerEquivalenceStatement_iff : zindlerEquivalenceStatement ↔
    ∀ (n : ℕ), 3 ≤ n → ∀ (K : Set Plane) (P : ℝ) (γ : ℝ → Plane),
      IsUnitSpeedBoundary K P γ →
        (FloatsWithPerimetralDensity K (1 / (n : ℝ)) ↔
          ∃ l : ℝ, 0 < l ∧ HasConstantChord γ (P / n) l) := by
  unfold zindlerEquivalenceStatement
  constructor <;> intro h n hn K P γ hb
  · exact (h n hn K P γ hb).trans (exists_congr fun _ => hb.isZindlerCarousel_iff (by omega))
  · exact (h n hn K P γ hb).trans
      (exists_congr fun _ => (hb.isZindlerCarousel_iff (by omega)).symm)

/-- Forward hydrostatic reduction suffices to construct a boundary Zindler
carousel. The hydrostatic premise has not been discharged. -/
theorem boundaryZindlerCarousel_of_hydrostatic_reduction
    (hphysical : hydrostaticReductionStatement) {K : Set Plane} {n : ℕ} (hn : 2 ≤ n)
    (hfloat : FloatsWithPerimetralDensity K (1 / (n : ℝ))) :
    HasBoundaryZindlerCarousel K n :=
  (hasBoundaryZindlerCarousel_iff hn).mpr (hphysical K _ hfloat)

/-- Physical rigidity at one third and one quarter requires only the forward
physical reduction; no fifth-density premise is needed. -/
theorem physical_third_quarter_rigidity_of_hydrostatic_reduction
    (hphysical : hydrostaticReductionStatement) : physicalThirdQuarterRigidityStatement := by
  intro K σ hσ hfloat
  have hc := hphysical K σ hfloat
  rcases hσ with rfl | rfl
  · exact third_rigidity K hc
  · exact quarter_rigidity K hc

/-- The proposed physical equivalence would transfer any geometric rigidity
theorem at `1 / n` to the physical formulation. -/
theorem physical_rigidity_of_zindler_equivalence
    (hequiv : zindlerEquivalenceStatement) {n : ℕ} (hn : 3 ≤ n)
    (hrigid : PerimetralRigidity (1 / (n : ℝ))) {K : Set Plane}
    (hfloat : FloatsWithPerimetralDensity K (1 / (n : ℝ))) : IsDisk K := by
  obtain ⟨P, γ, hb, _⟩ := hfloat.2.2
  obtain ⟨l, hz⟩ := (hequiv n hn K P γ hb).mp hfloat
  exact hrigid K ((hasBoundaryZindlerCarousel_iff (by omega : 2 ≤ n)).mp ⟨P, γ, l, hb, hz⟩)

/-- The full physical equivalence would complete the physical third and quarter
cases using the geometric theorems already proved. -/
theorem physical_third_quarter_rigidity_of_zindler_equivalence
    (hequiv : zindlerEquivalenceStatement) : physicalThirdQuarterRigidityStatement := by
  intro K σ hσ hfloat
  rcases hσ with rfl | rfl
  · exact physical_rigidity_of_zindler_equivalence hequiv (by omega : 3 ≤ 3) third_rigidity hfloat
  · exact physical_rigidity_of_zindler_equivalence hequiv (by omega : 3 ≤ 4) quarter_rigidity hfloat

end UlamFloating
