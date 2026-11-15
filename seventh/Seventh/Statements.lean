import UlamFloating.Basic
import UlamFloating.Geometry

/-!
# Seventh-density targets

These are proposition definitions, not asserted theorems. The geometric target
allows every positive chord length. The physical target additionally needs the
independent hydrostatic reduction from the parent project.
-/

namespace UlamFloating.Seventh

/-- Full geometric rigidity at one seventh, without a symmetry assumption. -/
def rigidityStatement : Prop := PerimetralRigidity (1 / 7)

/-- Physical rigidity at one seventh, using the existing equilibrium predicate. -/
def physicalRigidityStatement : Prop :=
  ∀ K : Set Plane, FloatsWithPerimetralDensity K (1 / 7) → IsDisk K

end UlamFloating.Seventh
