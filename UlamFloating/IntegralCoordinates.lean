import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Coordinates from a positive periodic speed

Integrating a positive continuous periodic real function gives an increasing
`C¹` order isomorphism of the real line. Its inverse is also `C¹`, and has
derivative the reciprocal speed. This construction does not involve curves,
convexity, or planar geometry.
-/

namespace UlamFloating

open MeasureTheory Set

/-- Moving the upper endpoint by an integer number of periods adds the same
integer multiple of the one-period integral. -/
theorem integral_add_int_mul_period {v : ℝ → ℝ} {Q : ℝ}
    (hv : Continuous v) (hp : Function.Periodic v Q) (t : ℝ) (k : ℤ) :
    (∫ u in (0 : ℝ)..(t + (k : ℝ) * Q), v u) =
      (∫ u in (0 : ℝ)..t, v u) + (k : ℝ) * ∫ u in (0 : ℝ)..Q, v u := by
  rw [(hp.int_mul k).intervalIntegral_add_eq_add 0 t (fun a b => hv.intervalIntegrable a b)]
  have h := hp.intervalIntegral_add_zsmul_eq k 0 (fun a b => hv.intervalIntegrable a b)
  simpa only [zero_add, zsmul_eq_mul] using congrArg (fun z => (∫ u in (0 : ℝ)..t, v u) + z) h

/-- A continuous positive speed has a strictly increasing cumulative integral. -/
theorem strictMono_integral_of_pos {v : ℝ → ℝ} (hv : Continuous v)
    (hpos : ∀ t, 0 < v t) : StrictMono (fun t => ∫ u in (0 : ℝ)..t, v u) := by
  exact strictMono_of_hasDerivAt_pos
    (fun t => (hv.integral_hasStrictDerivAt 0 t).hasDerivAt) hpos

/-- The primitive of a positive continuous periodic speed covers the whole
real line. Integer multiples of a period supply brackets for every value. -/
theorem surjective_integral_of_pos_periodic {v : ℝ → ℝ} {Q : ℝ}
    (hv : Continuous v) (hpos : ∀ t, 0 < v t) (hp : Function.Periodic v Q)
    (hQ : 0 < Q) : Function.Surjective (fun t => ∫ u in (0 : ℝ)..t, v u) := by
  let P : ℝ := ∫ u in (0 : ℝ)..Q, v u
  have hP : 0 < P := intervalIntegral.intervalIntegral_pos_of_pos
    (hv.intervalIntegrable 0 Q) hpos hQ
  have hint (k : ℤ) : (∫ u in (0 : ℝ)..(k : ℝ) * Q, v u) = (k : ℝ) * P := by
    simpa only [zero_add, zsmul_eq_mul] using
      hp.intervalIntegral_add_zsmul_eq k 0 (fun a b => hv.intervalIntegrable a b)
  have hcont : Continuous (fun t => ∫ u in (0 : ℝ)..t, v u) :=
    (intervalIntegral.differentiable_integral_of_continuous hv).continuous
  intro y
  let k : ℤ := ⌊y / P⌋
  have hlo : (k : ℝ) * P ≤ y := (le_div_iff₀ hP).mp (Int.floor_le (y / P))
  have hhi : y ≤ ((k + 1 : ℤ) : ℝ) * P := by
    have h := (div_lt_iff₀ hP).mp (Int.lt_floor_add_one (y / P))
    exact le_of_lt (by simpa only [Int.cast_add, Int.cast_one] using h)
  have hab : (k : ℝ) * Q ≤ ((k + 1 : ℤ) : ℝ) * Q := by
    simp only [Int.cast_add, Int.cast_one]
    nlinarith
  obtain ⟨t, _, ht⟩ := intermediate_value_Icc hab hcont.continuousOn
    (show y ∈ Icc (∫ u in (0 : ℝ)..(k : ℝ) * Q, v u)
      (∫ u in (0 : ℝ)..((k + 1 : ℤ) : ℝ) * Q, v u) by rw [hint, hint]; exact ⟨hlo, hhi⟩)
  exact ⟨t, ht⟩

/-- Cumulative integration of a positive continuous periodic speed is a
`C¹` order isomorphism, with `C¹` inverse and the expected derivative laws. -/
theorem exists_integral_orderIso {v : ℝ → ℝ} {Q : ℝ}
    (hv : Continuous v) (hpos : ∀ t, 0 < v t) (hp : Function.Periodic v Q) (hQ : 0 < Q) :
    ∃ A : ℝ ≃o ℝ,
      (∀ t, A t = ∫ u in (0 : ℝ)..t, v u) ∧
      ContDiff ℝ 1 (fun t => A t) ∧ ContDiff ℝ 1 (fun t => A.symm t) ∧
      (∀ t, HasDerivAt (fun s => A s) (v t) t) ∧
      (∀ t, HasDerivAt (fun s => A.symm s) (v (A.symm t))⁻¹ t) := by
  let A : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective
    (fun t => ∫ u in (0 : ℝ)..t, v u) (strictMono_integral_of_pos hv hpos)
    (surjective_integral_of_pos_periodic hv hpos hp hQ)
  have hA (t : ℝ) : A t = ∫ u in (0 : ℝ)..t, v u := rfl
  have hd (t : ℝ) : HasDerivAt (fun s => A s) (v t) t :=
    (hv.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hc : ContDiff ℝ 1 (fun t => A t) := by
    apply contDiff_one_iff_deriv.mpr
    refine ⟨fun t => (hd t).differentiableAt, ?_⟩
    simpa only [funext (fun t => (hd t).deriv)] using hv
  have hcinv : ContDiff ℝ 1 (fun t => A.symm t) :=
    A.toHomeomorph.contDiff_symm_deriv (fun t => (hpos t).ne') hd hc
  refine ⟨A, hA, hc, hcinv, hd, ?_⟩
  intro t
  exact HasDerivAt.of_local_left_inverse A.symm.continuous.continuousAt
    (hd (A.symm t)) (hpos _).ne' (Filter.Eventually.of_forall A.apply_symm_apply)

end UlamFloating
