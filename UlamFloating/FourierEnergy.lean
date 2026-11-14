import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

/-!
# Fourier energy on a compact interval

Parseval's identity for continuous functions with matching endpoint values,
expressed using interval integrals and mathlib's `fourierCoeffOn`.
-/

namespace UlamFloating

open MeasureTheory ContinuousMap Set
open scoped ENNReal

/-- The squared Fourier coefficients of a continuous function on a circle
are summable. -/
theorem summable_sq_fourierCoeff {T : ℝ} [Fact (0 < T)] (f : C(AddCircle T, ℂ)) :
    Summable (fun n : ℤ => ‖fourierCoeff f n‖ ^ 2) := by
  have h := (lp.memℓp (fourierBasis.repr (toLp 2 AddCircle.haarAddCircle ℂ f))).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, fourierBasis_repr,
    fourierCoeff_toLp] using h

/-- Parseval's identity for a continuous function on a circle, without an
explicit coercion through the almost-everywhere quotient `Lp`. -/
theorem tsum_sq_fourierCoeff_continuous {T : ℝ} [Fact (0 < T)]
    (f : C(AddCircle T, ℂ)) :
    ∑' n : ℤ, ‖fourierCoeff f n‖ ^ 2 =
      ∫ t : AddCircle T, ‖f t‖ ^ 2 ∂AddCircle.haarAddCircle := by
  have h := tsum_sq_fourierCoeff (toLp 2 AddCircle.haarAddCircle ℂ f)
  simp_rw [fourierCoeff_toLp] at h
  rw [h]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toAEEqFun AddCircle.haarAddCircle f] with t ht
  exact congrArg (fun z : ℂ => ‖z‖ ^ 2) ht

/-- Interval Parseval identity, with the normalization factor `1 / T`.
Continuity and equality at the two endpoints suffice; no periodic extension
is included among the hypotheses. -/
theorem hasSum_sq_fourierCoeffOn {T : ℝ} (hT : 0 < T) {f : ℝ → ℂ}
    (hf : ContinuousOn f (Icc 0 T)) (hend : f 0 = f T) :
    HasSum (fun n : ℤ => ‖fourierCoeffOn hT f n‖ ^ 2)
      ((1 / T) * ∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) := by
  letI : Fact (0 < T) := ⟨hT⟩
  let F : C(AddCircle T, ℂ) := ⟨AddCircle.liftIoc T 0 f,
    AddCircle.liftIoc_zero_continuous hend hf⟩
  have hcoeff (n : ℤ) : fourierCoeff F n = fourierCoeffOn hT f n := by
    simpa only [zero_add] using (fourierCoeff_liftIoc_eq (T := T) (a := 0) f n)
  have hint := AddCircle.intervalIntegral_preimage T 0 (fun z : AddCircle T => ‖F z‖ ^ 2)
  simp only [zero_add, AddCircle.volume_eq_smul_haarAddCircle, integral_smul_measure,
    ENNReal.toReal_ofReal hT.le, smul_eq_mul] at hint
  have heq : (∫ t in (0 : ℝ)..T, ‖F (t : AddCircle T)‖ ^ 2) =
      ∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2 := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with t ht
    have ht' : t ∈ Ioc 0 (0 + T) := by simpa [Set.uIoc_of_le hT.le] using ht
    change ‖AddCircle.liftIoc T 0 f (t : AddCircle T)‖ ^ 2 = _
    rw [AddCircle.liftIoc_coe_apply ht']
  rw [heq] at hint
  have henergy : (∫ z : AddCircle T, ‖F z‖ ^ 2 ∂AddCircle.haarAddCircle) =
      (1 / T) * ∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2 := by
    rw [hint]
    field_simp
  have h := (summable_sq_fourierCoeff F).hasSum
  rw [tsum_sq_fourierCoeff_continuous, henergy] at h
  simpa only [hcoeff] using h

end UlamFloating
