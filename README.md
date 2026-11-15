# Ulam floating problem: perimetral densities 1/3, 1/4, 1/5, 1/7

A Lean 4 formalization and Lean blueprint. **Geometric rigidity at perimetral
densities 1/3 and 1/4 is proved in Lean.** The 1/5 result remains unproved.
Each checked theorem says that a compact strictly convex planar body with a
simple C¹ unit-speed boundary and constant positive chords at the specified fraction of
the perimeter is a closed disk of positive radius. The separate physical
equilibrium reduction remains unproved.

**Geometric rigidity at density 1/7 is also proved**, in the separate
[seventh project](seventh/README.md). Its proof reconstructs all 139 numerical
certificates in Lean and concludes the same disk property from the original
boundary hypotheses. See [the final theorem](seventh/Seventh/Rigidity.lean)
and [its fully expanded statement](seventh/Seventh/StatementAudit.lean).
The independent completion audit is `cd seventh && python scripts/check.py --require-target`.

Start with [the blueprint](blueprint/src/content.tex). It contains definitions,
proof dependencies, the triangle and square proof routes, the pentagon research
obligation, and a separate bridge to physical equilibrium. Perimetral density
is not material density or submerged area fraction.

The final checked geometric results are `UlamFloating.third_rigidity` and
`UlamFloating.quarter_rigidity` in [Rigidity.lean](UlamFloating/Rigidity.lean).
Their hypotheses and disk conclusion are defined in [Basic.lean](UlamFloating/Basic.lean).
The proof reductions use sampled equilateral triangles with a fixed center at
density 1/3, and sampled squares with a fixed center at density 1/4.

Both cases appear in Theorem 5 of J. Bracho, L. Montejano, and D. Oliveros,
*Carousels, Zindler curves and the floating body problem*, Periodica Mathematica
Hungarica 49(2), 9–23 (2004):
[published paper, printed page 18 / PDF page 10](https://www.matem.unam.mx/~roli/investigacion/articulos/CarrouP.pdf#page=10).
The paper's physical-equilibrium reduction is separate from the geometric
results currently proved here.

The Zindler construction is explicit in [Zindler.lean](UlamFloating/Zindler.lean).
`IsZindlerCarousel` describes a cyclic carousel whose regular closed trajectories
all have the same image. For a specified boundary, `zindler_construction` proves
that the samples `γ(t + i * P / n)` form an inscribed, strictly convex Zindler
carousel, with the cyclic time-shift identity. The geometric carousel and
constant-chord formulations are proved equivalent (also for two chairs).

[FloatingEquivalence.lean](UlamFloating/FloatingEquivalence.lean) states the full
physical equivalence on a specified boundary, following Theorem 2 and Remark 3
of [Asipchuk–Kosmakov–Zatitskii](https://arxiv.org/pdf/2604.10330).
`zindlerEquivalenceStatement` is an **unproved proposition specification**.
`physicalThirdQuarterRigidityStatement` separately records the physical 1/3 and
1/4 target. Checked conditional assembly theorems show that the forward
hydrostatic reduction, or the full Zindler equivalence, would complete those
two cases without any assumption about 1/5.

## Library

| Module | Scope |
| --- | --- |
| `UlamFloating.Basic` | Metric chord property, boundary data, disk and rigidity propositions, complementary densities |
| `UlamFloating.Sampling` | Rational sampling, closure, and equal edge lengths |
| `UlamFloating.Carousel` | Rigid-edge derivative, equal endpoint speeds, reflection law, carousel interface |
| `UlamFloating.Invariants` | General skew-bilinear area-rate cancellation over a finite permutation |
| `UlamFloating.Geometry` | Regular boundaries, polygon geometry, signed moments, and independent physical-equilibrium definitions |
| `UlamFloating.Statements` | Precise propositions for the remaining blueprint obligations; these are specifications, not proofs |
| `UlamFloating.AreaConservation` | Signed-area conservation from the midpoint law in any real normed space |
| `UlamFloating.MomentConservation` | Planar first-moment edge identities using the oriented area form and right-angle rotation |
| `UlamFloating.FirstMoment` | First-moment and signed-centroid conservation over any finite successor permutation |
| `UlamFloating.Disk` | Reconstruction of a closed ball from a spherical frontier in any nontrivial real normed space |
| `UlamFloating.Triangle` | Fixed center and exact squared radius of any three-vertex carousel, in any real inner product space |
| `UlamFloating.FiniteSampling` | Finite cyclic shifts, closing edges, and translated derivative formulas |
| `UlamFloating.BoundaryEmbedding` | Injectivity on a traversal interval and distinct rational samples |
| `UlamFloating.BoundaryTangents` | Strict supporting functionals, consistent tangent orientation, and distinct directed tangents |
| `UlamFloating.BoundaryConvexity` | Noncollinear frontier triples, positive traversal orientation, and cyclic convexity of rational samples |
| `UlamFloating.Extraction` | Full convex carousel extraction: velocity laws, polygon order, and time shift from the boundary hypotheses |
| `UlamFloating.Zindler` | General Zindler carousels, rational boundary construction, and equivalence with constant chords |
| `UlamFloating.FloatingEquivalence` | Physical Zindler equivalence specification and conditional physical third/quarter conclusions |
| `UlamFloating.ChordRotation` | Intrinsic second carousel law and positive, bounded rotation of constant boundary chords |
| `UlamFloating.AngularCoordinates` | Global real chord angles from the rotation equation, with an increasing continuously differentiable coordinate and inverse |
| `UlamFloating.ChordInjectivity` | Nonparallel interlaced and adjacent chords, and no intermediate return of a directed chord vector |
| `UlamFloating.ChordWinding` | Integer rotation increments and exactly one turn of constant boundary chords |
| `UlamFloating.SampledAngles` | Cyclic angle coordinates with regularity, periodicity, finite-index shift, and exact angle sum |
| `UlamFloating.ChordAngleRange` | Convex angle ranges and geometric extraction of periodic cyclic angle coordinates for every `n ≥ 3` |
| `UlamFloating.TangentChordAngles` | Positive real angles between unit vectors, reflection as rotation, and real angle addition without full-turn ambiguity |
| `UlamFloating.ChordAngularVelocity` | Differentiating rotations and identifying the exact angular speed of a geometric chord lift |
| `UlamFloating.BoundaryTangentAngles` | Periodic positive tangent–chord angles, consecutive-angle sums, and the geometric sine speed law |
| `UlamFloating.SamplingShift` | Arbitrary natural-number cyclic sampling shifts for periodic functions into any target |
| `UlamFloating.SampledAngleCurve` | Euclidean curves of sampled angles, continuous differentiability, periodicity, and arbitrary cyclic shifts |
| `UlamFloating.PentagonAngleRelations` | Solving the five tangent-angle equations and deriving the scalar five-angle differential equation |
| `UlamFloating.PentagonGeometry` | The actual sampled geometric angles satisfy the pentagon equation; extraction retains the original chord reconstruction |
| `UlamFloating.ConstantAngles` | A constant sampled-angle curve has equal coordinates and a chord increment fixed by its total turn |
| `UlamFloating.RotatingVelocity` | Fixed centers, circle reconstruction, and disk rigidity from uniformly rotating unit velocity |
| `UlamFloating.RotationGeometry` | Rotation distance formula, one-turn winding, and regularity of every rational sample of a uniformly rotating boundary |
| `UlamFloating.PentagonConstant` | The constant geometric five-angle branch forces uniform tangent rotation, a disk, and regular sampled pentagons |
| `UlamFloating.PentagonReduction` | A nondisk would yield a nonconstant geometric pentagon solution satisfying the lower bound on every positive shape period |
| `UlamFloating.PeriodSubgroup` | The additive subgroup of periods, existence of a least positive period from a gap, and classification of all periods as its integer multiples |
| `UlamFloating.CyclicMotion` | Fixed-sum cyclic motions are constant if the coordinate-shift interval is a period; divisible traversal multiplicities are excluded |
| `UlamFloating.CyclicPeriods` | Least positive periods and nondivisible multiplicities for general cyclic coordinate motions |
| `UlamFloating.PentagonPeriods` | A hypothetical nondisk has a least shape period `T`, with `P = m T` and positive `m` coprime to five |
| `UlamFloating.PeriodicPrimitive` | Fixed translation increments for primitives with periodic derivatives in any real normed space, and division by an integer period multiplicity |
| `UlamFloating.PentagonTurning` | The actual chord angular velocity is determined by shape; a shape period `T` with `P = m T` advances the chord angle by exactly `2π/m` |
| `UlamFloating.PolygonMotion` | Transformation of polygon moments under area-preserving linear maps and reconstruction of centered polygons from their edge vectors |
| `UlamFloating.BoundaryRotation` | A fixed chord-angle increment rotates the original rational-chord boundary about its conserved signed polygon centroid |
| `UlamFloating.PolygonArea` | General skew-bilinear edge-triangle identity and nonzero signed area of strictly convex polygons |
| `UlamFloating.PolygonCentroid` | Translation of signed moments and equality of signed centroid with circumcenter for equilateral cyclic polygons |
| `UlamFloating.RegularCarousel` | Fixed circle for regular-polygon carousels, rigidity from regular samples, and explicit one-fifth assembly |
| `UlamFloating.Quadrilateral` | Equilateral quadrilaterals with distinct diagonals are parallelograms |
| `UlamFloating.SquareKinematics` | Nondegenerate parallelogram velocity identities and perpendicular adjacent edges |
| `UlamFloating.SquareCarousel` | Fixed vertex sum and square geometry for four-vertex carousels |
| `UlamFloating.SquareGeometry` | Fixed square center, circumradius, and full cyclic distance formula |
| `UlamFloating.Rigidity` | Unconditional geometric one-third and one-quarter rigidity, and explicit assembly implications for remaining targets |
| `UlamFloating.FourierEnergy` | Parseval and summability for continuous functions, with interval-integral normalization |
| `UlamFloating.Wirtinger` | Nonzero Fourier-mode energy estimate and complex periodic Wirtinger inequality |
| `UlamFloating.WirtingerEuclidean` | Sharp periodic Wirtinger inequality in arbitrary finite dimension |
| `UlamFloating.PeriodicAnalysis` | Periodic derivatives, zero mean velocity, and positive energy for nonconstant curves |
| `UlamFloating.PeriodBound` | Period at least `2π/L` from an acceleration bound, including an autonomous-equation corollary |
| `UlamFloating.FiniteCycleEnergy` | Permutation-difference energy and five-cycle pair-sum estimates on the zero-sum subspace |
| `UlamFloating.PentagonDynamics` | Smooth five-angle field, exact acceleration estimate, and period lower bound with explicit time scaling |
| `UlamFloating.UnitSpeedLength` | Metric total variation equals parameter interval length for differentiable unit-speed curves in any real normed space |
| `UlamFloating.IntegralCoordinates` | Increasing integral coordinates for positive periodic speed, with a continuously differentiable inverse |
| `UlamFloating.ArcLength` | Unit-speed reparametrization in real normed spaces and normalization of regular boundary data |

Signed-area, first-moment, and signed-centroid conservation are proved, as are
the triangle-carousel fixed-center theorem and the circle-to-disk bridge.
Every blueprint claim has a Lean statement. `UlamFloating.third_rigidity` and
`UlamFloating.quarter_rigidity` prove `PerimetralRigidity (1 / 3)` and
`PerimetralRigidity (1 / 4)` without extra extraction or reduction premises:
the carousel laws and square geometry follow from the boundary assumptions.
The full extraction theorem is also proved, including strict convexity of the
sampled polygon in its cyclic order and the time-shift identity. Signed area
is nonzero for any strictly convex polygon, in either orientation.
The dimension-independent period bound is proved through periodic Wirtinger.
The integral and metric length of a unit-speed traversal both equal its period;
the general metric-length lemma does not need continuity of the derivative.
Arc-length normalization is proved for regular periodic curves in any real normed space,
including preservation of the boundary and metric traversal length.
The algebraic signed centroid equals the circumcenter of every equilateral
cyclic polygon with nonzero signed area. This gives a fixed-circle theorem
for regular-polygon carousels and disk rigidity from regular rational samples.
The one-fifth assembly now needs only the pentagon obstruction as an explicit
premise; it does not depend on polygon-to-lamina centroid identification.
Constant boundary chords have positive angular speed bounded by `2/l`.
For nonconstant periodic solutions of the explicitly specified five-angle
equation, the period is at least `π/√3`, or `lπ/(2√3)` with side length `l`.
This exact estimate uses finite-cycle energy inequalities. Global real chord
angles and their one-turn winding are now proved. For every `n ≥ 3`, the
boundary yields periodic continuously differentiable cyclic angle coordinates
in `(0, π)`, with sum `(n-2)π` and the required one-step cyclic time shift.
The actual geometric coordinates now satisfy the five-angle equation in Lean,
with the exact scale `2/l`. This follows from periodic positive tangent–chord
angles, the reflection law, and the one-turn identity. The extraction theorem
retains the real lift and its reconstruction of the original boundary chords.
The constant geometric angle branch now forces uniform rotation of the original
unit tangent, hence a disk and regular sampled pentagons with the full cyclic
distance table. A nondisk would therefore give a nonconstant geometric angle
solution. Every positive period of that solution satisfies the analytic lower
bound, including periods smaller than the boundary period. A least positive
shape period `T` now exists, and `P = m T` for a positive natural number `m`
coprime to five. The same geometric lift advances by exactly `2π/m` over
each least shape period. The original boundary rotates by that angle about
one fixed center, obtained from its conserved signed polygon centroid.
The period subgroup API is reusable for arbitrary target
types and ordered Archimedean additive groups. A stronger geometric or period
obstruction remains necessary to exclude all nonconstant motions; the present
period estimate and multiplicity constraint do not prove fifth-density rigidity.
The 1/5 theorem, polygon-to-lamina centroid identification,
and the hydrostatic reduction remain unproved. The design aims for mathlib reuse; it has not
undergone upstream review.

Verification: `lake build` passes. The current blueprint has 139 nodes and
286 Lean links: 251 proved lemmas, 7 statement-only propositions, and 28 other
definitions or structures. The full declaration audit passes, including the
polygon-motion and boundary-rotation lemmas, with no admitted proofs or
nonstandard axioms in their dependencies. The CI workflow runs the full
current audit on every push.
The audit rejects a proposition specification marked as proved and checks that
proof links really name Lean theorems.
The lemma count includes eleven explicitly conditional assembly results.
The audit also checks the exact unconditional types `PerimetralRigidity (1 / 3)`
and `PerimetralRigidity (1 / 4)`, independently of their named specification aliases.
Both checked rigidity theorems concern the geometric constant-chord formulation.

## Build

The project pins Lean and mathlib to `v4.24.0`; `lake-manifest.json` locks exact
dependency revisions. With elan available:

```sh
lake update
lake exe cache get
lake build
python scripts/check_blueprint.py
```

For a smaller cache download, use module names (not paths relative to this
repository):

```sh
lake exe cache get Mathlib.Analysis.InnerProductSpace.Calculus Mathlib.Analysis.Convex.Strict Mathlib.Topology.MetricSpace.ProperSpace Mathlib.Tactic.Linarith Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp Mathlib.Tactic.Abel
```

The validation script checks dependency labels and Lean declaration links,
builds the library, and uses Lean's own axiom collector to traverse the union
of all linked declarations' dependencies with a shared visited set.
It rejects dependencies on `sorryAx` or any axiom beyond Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`.
Run `python scripts/test_blueprint_audit.py` after building to check that the
audit accepts valid proofs and rejects transitive custom axioms, admitted
proofs, missing declarations, and specifications incorrectly presented as proofs.

## Blueprint

Install the pinned renderer in a Python environment (Graphviz may need a system
installation, depending on your platform):

```sh
python -m pip install -r blueprint/requirements.txt
python scripts/build_blueprint.py
python scripts/check_blueprint_html.py
```

This portable web build does not require a system TeX installation. Its entry
point is `blueprint/web/index.html`. On a configured LaTeX installation,
`leanblueprint pdf` builds `blueprint/src/print.tex`. Local generated output
and downloaded dependencies are ignored.
The portable build links Lean declarations to a generated local source listing.
No repository or documentation hosting URL is fabricated. Configure doc-gen
links after choosing a remote. The standard `leanblueprint web` command also
renders the blueprint, but does not generate this local source index.

To view this project alongside other local projects, use its dedicated server:

```sh
python scripts/serve_blueprint.py
```

Open <http://127.0.0.1:8873/>. The server uses an absolute project directory
and refuses to share its port with another server. Use `--port` to choose
a different available port.

## Mathematical source issue at 1/5

The available [2001 author-hosted classification paper](https://www.matem.unam.mx/~luis/pdfs/volantin2.pdf)
labels period monotonicity a conjecture and discusses numerical evidence in
Section 4. Its period contradiction and exceptional cases need a rigorous
replacement or a verified later source before they can enter a Lean proof.
The [2004 carousel paper](https://www.matem.unam.mx/~luis/pdfs/volantin1.pdf)
asserts the fifth-density result and refers back to this work. This project
records that source gap rather than introducing an axiom. It does not claim
that no rigorous proof exists elsewhere.

## Next milestones

1. Exclude nonconstant geometric pentagon motion using its proved period,
   multiplicity, and exact angular advance; close density 1/5.
2. Identify the signed polygon centroid with the lamina centroid.
3. Prove the hydrostatic reduction and the combined physical rigidity result.

Keep reusable metric, calculus, and finite-sum lemmas general. Do not assume
central symmetry, regular sampled polygons, or the desired rigidity inside
the public geometric definitions. Add `\leanok` only after compilation and
axiom auditing; leave mathematical gaps explicit in the blueprint.
