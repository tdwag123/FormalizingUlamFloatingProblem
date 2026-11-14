import UlamFloating.Wirtinger
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Vector-valued periodic Wirtinger inequality

Applying the complex scalar inequality to the real coordinates and summing
gives the same sharp constant in every finite-dimensional Euclidean space.
-/

namespace UlamFloating

open MeasureTheory Set
open scoped BigOperators

/-- Sharp periodic Wirtinger inequality in arbitrary finite dimension. -/
theorem wirtinger_euclidean {ι : Type*} [Fintype ι] {T : ℝ} (hT : 0 < T)
    {f g : ℝ → EuclideanSpace ℝ ι}
    (hf : ContinuousOn f (Icc 0 T)) (hg : ContinuousOn g (Icc 0 T))
    (hder : ∀ t ∈ Icc 0 T, HasDerivAt f (g t) t)
    (hfend : f 0 = f T) (hgend : g 0 = g T)
    (hmean : (∫ t in (0 : ℝ)..T, f t) = 0) :
    (2 * Real.pi) ^ 2 * (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) ≤
      T ^ 2 * (∫ t in (0 : ℝ)..T, ‖g t‖ ^ 2) := by
  let L (i : ι) : EuclideanSpace ℝ ι →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (PiLp.proj 2 (fun _ : ι => ℝ) i)
  have hcoord (i : ι) :
      (2 * Real.pi) ^ 2 * (∫ t in (0 : ℝ)..T, ‖f t i‖ ^ 2) ≤
        T ^ 2 * (∫ t in (0 : ℝ)..T, ‖g t i‖ ^ 2) := by
    have h := wirtinger_complex hT
      ((L i).continuous.comp_continuousOn hf) ((L i).continuous.comp_continuousOn hg)
      (fun t ht => (L i).hasFDerivAt.comp_hasDerivAt t (hder t ht))
      (congrArg (L i) hfend) (congrArg (L i) hgend) ?_
    · simpa only [L, Function.comp_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
        PiLp.proj_apply, Complex.norm_real] using h
    · change (∫ t in (0 : ℝ)..T, (L i) (f t)) = 0
      rw [(L i).intervalIntegral_comp_comm (hf.intervalIntegrable_of_Icc hT.le), hmean, map_zero]
  have hfi (i : ι) : IntervalIntegrable (fun t => ‖f t i‖ ^ 2) volume 0 T :=
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).continuous.comp_continuousOn hf).norm.pow 2).intervalIntegrable_of_Icc hT.le
  have hgi (i : ι) : IntervalIntegrable (fun t => ‖g t i‖ ^ 2) volume 0 T :=
    (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : ι => ℝ) i).continuous.comp_continuousOn hg).norm.pow 2).intervalIntegrable_of_Icc hT.le
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hcoord i)
  simp_rw [← Finset.mul_sum] at hsum
  rw [← intervalIntegral.integral_finset_sum (fun i _ => hfi i),
    ← intervalIntegral.integral_finset_sum (fun i _ => hgi i)] at hsum
  simpa only [← EuclideanSpace.norm_sq_eq] using hsum

end UlamFloating
