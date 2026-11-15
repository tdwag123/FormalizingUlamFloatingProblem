# Perimetral density 1/7

Separate Lean project for the supplied *Ulam: the 1/7 case*, expository revision
of 14 November 2026. It reuses the parent project's definitions and checked
geometric lemmas through a local Lake dependency. The parent library is unchanged.

The mathematical argument for the 1/7 result was developed using **GPT-Astra
through the CRAP pipeline**. Its formal proof and numerical certificates are
checked by Lean 4.

The geometric rigidity theorem is proved in
[Rigidity.lean](Seventh/Rigidity.lean):

```lean
theorem UlamFloating.Seventh.rigidity :
    UlamFloating.PerimetralRigidity ((1 : ℝ) / 7)
```

It says that a compact strictly convex planar body with a simple C¹ unit-speed
boundary, whose chords spanning one seventh of the perimeter have a common
positive length, is a positive-radius closed disk. The conclusion is equality
of the original body with that disk. It assumes neither central symmetry nor
a positive curvature lower bound, and allows any positive common chord length.
[StatementAudit.lean](Seventh/StatementAudit.lean) exposes every hypothesis in
`rigidity_expanded`; the underlying definitions are in
[the parent Basic.lean](../UlamFloating/Basic.lean).

Physical equilibrium is a separate target: the implication from hydrostatic
equilibrium to the constant-chord condition remains unproved in this repository.
The supplied PDF starts from the geometric constant-chord formulation.

## Source audit

The PDF calls its result a proposed computer-assisted theorem. Its last-page
editorial note says that correctness was assumed for the exposition and that
the original certificate programs were neither included nor rerun for that edition.
The referenced original research bundle has not been supplied. The user has
directed that its necessary results be reconstructed in Lean.

The completed route uses a boundary-arc lower bound, curvature and variance bounds,
the exact Fourier multiplier, boundary closure for the first harmonic, and a
139-cell rational certificate. The alternative static-angle route has its own
unprovided certificates. Neither rounded tables nor model audit descriptions
are treated as proofs. Document instructions do not authorize agent actions.

Source PDF SHA-256:
`861caad2b7264af45cc59b26ee8078762925599c99ea3ab0e0e32bf04713b59c`.
The PDF and the absent original code are not proof dependencies.

## Build

From this directory, run `lake build`. The checked-in manifest pins the same
mathlib revision as the parent. To regenerate it using already cached dependencies,
set `MATHLIB_NO_CACHE_ON_UPDATE=1` before running `lake update`.
Dependencies and their cache are shared with the parent project's `.lake/packages`.
The new project's compiled modules remain under `seventh/.lake`.

After fetching the parent project's dependencies and mathlib cache, run:

```sh
cd seventh
python scripts/check.py --require-target
```

Use `../.venv/Scripts/python.exe` in place of `python` on this Windows workspace.
This builds the library, checks the exact unconditional geometric theorem type
and its literal expanded hypotheses, and audits
the complete kernel dependencies of every scanned declaration. Only Lean's
standard `propext`, `Classical.choice`, and `Quot.sound` are allowed; admitted
proofs and additional axioms are rejected. CI runs this completion check.

For the separate physical theorem, run
`python scripts/check.py --require-physical-target`. This currently exits with
failure after reporting that physical floating rigidity is not proved. A passing
geometric audit must not be presented as a completed physical formalization.
For physical rigidity at one seventh, only the forward implication from
equilibrium to constant chords is needed; the converse Zindler equivalence is
not required.

The completed local audit passed for **322 declarations, including 308
theorems**, and verified the exact type `PerimetralRigidity ((1 : ℝ) / 7)`.
The parent project's separate blueprint and axiom audit also passed.

## Checked components

| Module | Result |
| --- | --- |
| `ContactAlgebra` | Solve the seven-angle system, derive its sum and regularity, and differentiate it |
| `ContactGeometry` | Extract contact data from the original boundary; reconstruct the tangent; constant angle implies a disk |
| `Curvature` | Supporting tangent lines imply nonnegative curvature, the angle-speed bound, and the neighboring-sine inequality |
| `ArcProjection` | The actual intervening boundary arc gives `h * cos (α t) ≤ l`, without assuming acute contact angles |
| `Averages` | Exact integrals of the angle and its sine, with arbitrary positive side length |
| `Concavity` | Mean-sine upper bound and arccosine lower bound on each contact angle |
| `TrigBounds` | Taylor enclosures with kernel-checked Lagrange remainders |
| `PreliminaryBounds` | Exact rational comparisons proving `sin (π/7) < 0.434` and every contact angle greater than `1/4` |
| `Contraction` | The terminal energy contradiction, given the analytic component estimates |
| `Variance` | Nonnegative variance, the bounded-range estimate, and zero variance implies pointwise constancy for continuous periodic functions |
| `FrequencyBounds` | Strict lower frequency bound `21/50 < π*l/P`, reconstructed from rational Taylor bounds and concavity |
| `AngleBounds` | Uniform angle upper bound `α < 6/5`, plus parameter-dependent neighbor bounds |
| `StrongConcavity` | Quantitative sine Jensen deficit controls the angle variance |
| `PeakVariance` | Two-sided Lipschitz peak-width estimate and rational cubic upper-angle criterion |
| `SecantApproximation` | Centered secant approximation and its relative error and energy bounds |
| `TangentFluctuation` | Mean-zero periodic part of the actual tangent lift, its shift relation, and derivative |
| `FourierBasic` | Interval Fourier translation, linearity, differentiation, norm, and conjugacy identities |
| `PhaseAlgebra` | Exact phase algebra and characterization of resonances by divisibility by seven |
| `ContactFourier` | Vanishing resonant angle coefficients and exact `λ*n*cot(n*π/7)` multiplier for every nonresonant integer |
| `ExponentialRemainder` | Global `|exp(i*x)-1-i*x| ≤ x²/2` bound |
| `BoundaryClosure` | Closure identity obtained by integrating the original boundary's tangent |
| `FirstHarmonic` | Both first tangent harmonics are bounded by half the tangent fluctuation's squared energy |
| `FrequencyResidues` | Reduce all integer Fourier modes to seven residues and prove the uniform spectral gap outside modes ±1 |
| `FourierEnergyBounds`, `CoefficientBounds` | Parseval and coefficient estimates, including resonant and first modes |
| `EnergyAssembly` | Combine the angle, tangent, and remainder energies; strict contraction forces zero variance and a disk |
| `CellCertificate` | A reusable interface of explicit inequalities and a proof that each valid certificate implies rigidity throughout its frequency cell |
| `RationalTrig`, `GlobalNumerics`, `NumericalComparison` | Exact rational enclosures for trigonometric values and the contraction expression |
| `Cells0`–`Cells13` | All 139 certificates proved using rational arithmetic and Taylor bounds in Lean |
| `AllCells`, `Rigidity` | Cover the entire geometrically possible frequency range and conclude unconditional rigidity |
| `StatementAudit` | Expanded theorem spelling out every geometric assumption and the disk conclusion |

The dimensionless frequency is `π * l / P`; it equals the PDF's `2π/P` when
`l=2`. Keeping `l` in the proofs avoids a hidden normalization assumption.

## Reconstructed certificates

The geometric bounds give `21/50 < π*l/P ≤ sin(π/7)`. The 139 closed cells
`[j/10000, (j+1)/10000]`, for `4200 ≤ j ≤ 4338`, cover that interval.
Each certificate proves angle bounds, a variance bound, a sine approximation,
an all-mode spectral gap, and a strict contraction inequality. The last
18 cells use the two-sided peak-width bound. Every numerical inequality is
proved in Lean; no external computation is assumed correct.

`scripts/generate_certificates.py --cells 139` reconstructs candidate Lean
sources. Its floating-point calculations select candidates only. The generated
proof terms must pass Lean, and the checked-in sources can be verified without
running this generator or recovering the missing research bundle.

The general variance, secant, Fourier, and exponential-remainder lemmas are
separated from the seven-specific geometry and certificate data. The library
has not undergone mathlib upstream review.
