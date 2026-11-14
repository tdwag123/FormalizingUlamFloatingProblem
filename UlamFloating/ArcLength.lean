import UlamFloating.IntegralCoordinates
import UlamFloating.PeriodicAnalysis
import UlamFloating.UnitSpeedLength
import Mathlib.Order.Interval.Set.OrderIso

/-!
# Arc-length normalization of regular periodic curves

The inverse of cumulative speed gives a global increasing `C¹` change of
parameter. Integer period shifts, unit speed, and metric length are proved
for curves in arbitrary real normed spaces before applying the construction
to planar boundary data.
-/

namespace UlamFloating

open Set MeasureTheory

/-- A regular `C¹` periodic curve in any real normed space admits a global
increasing `C¹` unit-speed parametrization. The new period is both its
integrated speed and its metric total variation over the original period. -/
theorem exists_unitSpeed_reparam {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : ℝ → E} {Q : ℝ} (hφ : ContDiff ℝ 1 φ) (hreg : ∀ t, deriv φ t ≠ 0)
    (hperiod : Function.Periodic φ Q) (hQ : 0 < Q) :
    ∃ (P : ℝ) (e : ℝ ≃o ℝ), 0 < P ∧
      P = (∫ t in (0 : ℝ)..Q, ‖deriv φ t‖) ∧
      ContDiff ℝ 1 (fun t => e t) ∧ ContDiff ℝ 1 (fun t => e.symm t) ∧
      e 0 = 0 ∧ (∀ (t : ℝ) (k : ℤ), e (t + (k : ℝ) * P) = e t + (k : ℝ) * Q) ∧
      (∀ t, ‖deriv (fun s => φ (e s)) t‖ = 1) ∧
      eVariationOn φ (Icc 0 Q) = ENNReal.ofReal P := by
  let v : ℝ → ℝ := fun t => ‖deriv φ t‖
  have hv : Continuous v := hφ.continuous_deriv_one.norm
  have hvpos (t : ℝ) : 0 < v t := norm_pos_iff.mpr (hreg t)
  have hvperiod : Function.Periodic v Q := by
    intro t
    exact congrArg norm (periodic_deriv hperiod (hφ.differentiable (by simp)) t)
  obtain ⟨A, hA, hc, hcinv, _, hdinv⟩ := exists_integral_orderIso hv hvpos hvperiod hQ
  let P : ℝ := ∫ t in (0 : ℝ)..Q, v t
  have hP : 0 < P := intervalIntegral.intervalIntegral_pos_of_pos
    (hv.intervalIntegrable 0 Q) hvpos hQ
  have hA0 : A 0 = 0 := by rw [hA]; simp
  have hAQ : A Q = P := hA Q
  have hAshift (t : ℝ) (k : ℤ) : A (t + (k : ℝ) * Q) = A t + (k : ℝ) * P := by
    simp_rw [hA]
    exact integral_add_int_mul_period hv hvperiod t k
  have he0 : A.symm 0 = 0 := by
    apply A.injective
    rw [A.apply_symm_apply, hA0]
  have heshift (t : ℝ) (k : ℤ) : A.symm (t + (k : ℝ) * P) =
      A.symm t + (k : ℝ) * Q := by
    apply A.injective
    rw [A.apply_symm_apply, hAshift, A.apply_symm_apply]
  have hunit (t : ℝ) : ‖deriv (fun s => φ (A.symm s)) t‖ = 1 := by
    have hd := (hφ.differentiable (by simp) (A.symm t)).hasDerivAt.scomp t (hdinv t)
    change HasDerivAt (fun s => φ (A.symm s)) ((v (A.symm t))⁻¹ • deriv φ (A.symm t)) t at hd
    rw [hd.deriv, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hvpos _))]
    exact inv_mul_cancel₀ (hvpos _).ne'
  have hmetric : eVariationOn φ (Icc 0 Q) = ENNReal.ofReal P := by
    have heq : φ = (fun t => φ (A.symm t)) ∘ A := by
      ext t
      simp only [Function.comp_apply, A.symm_apply_apply]
    calc
      eVariationOn φ (Icc 0 Q) =
          eVariationOn ((fun t => φ (A.symm t)) ∘ A) (Icc 0 Q) :=
            congrArg (fun f : ℝ → E => eVariationOn f (Icc 0 Q)) heq
      _ = eVariationOn (fun t => φ (A.symm t)) (A '' Icc 0 Q) :=
        eVariationOn.comp_eq_of_monotoneOn _ _ (A.monotone.monotoneOn _)
      _ = eVariationOn (fun t => φ (A.symm t)) (Icc 0 P) := by rw [A.image_Icc, hA0, hAQ]
      _ = ENNReal.ofReal P := by
        simpa only [sub_zero] using eVariationOn_eq_of_unit_speed
          ((hφ.comp hcinv).differentiable (by simp)) hunit hP.le
  exact ⟨P, A.symm, hP, rfl, hcinv, hc, he0, heshift, hunit, hmetric⟩

/-- Arc-length normalization preserves all boundary data, including exact
integer-period simplicity, and identifies the original traversal's metric
length with the new period. -/
theorem arc_length_normalization : arcLengthNormalizationStatement := by
  intro K Q φ hb
  obtain ⟨P, e, hP, hlength, hec, heinv, he0, hshift, hunit, hmetric⟩ :=
    exists_unitSpeed_reparam hb.contDiff hb.regular hb.periodic hb.period_pos
  let γ : ℝ → Plane := fun t => φ (e t)
  have hshift1 (t : ℝ) : e (t + P) = e t + Q := by simpa using hshift t 1
  have hboundary : IsUnitSpeedBoundary K P γ := by
    refine ⟨hb.isCompact, hb.strictConvex, hb.interior_nonempty, hP,
      hb.contDiff.comp hec, ?_, ?_, hunit, ?_⟩
    · intro t
      change φ (e (t + P)) = φ (e t)
      rw [hshift1]
      exact hb.periodic (e t)
    · intro s t
      change φ (e s) = φ (e t) ↔ ∃ k : ℤ, s = t + (k : ℝ) * P
      constructor
      · intro h
        obtain ⟨k, hk⟩ := (hb.simple (e s) (e t)).mp h
        refine ⟨k, e.injective ?_⟩
        rw [hshift]
        exact hk
      · rintro ⟨k, rfl⟩
        rw [hshift]
        exact hb.periodic.int_mul k (e t)
    · rw [← hb.range_eq_frontier]
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨e t, rfl⟩
      · rintro ⟨t, rfl⟩
        obtain ⟨s, hs⟩ := e.surjective t
        exact ⟨s, congrArg φ hs⟩
  exact ⟨P, γ, e, hlength, hboundary, hec, heinv, he0, hshift1, fun _ => rfl, hmetric⟩

end UlamFloating
