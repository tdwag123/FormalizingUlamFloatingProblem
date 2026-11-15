import UlamFloating.HydrostaticMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Continuity of integrals over moving waterline caps

For a fixed integrable density, translating and rotating a nondegenerate
waterline varies its cap integral continuously. The proof uses dominated
convergence and the nullity of the limiting waterline, not boundary formulas.
-/

noncomputable section

namespace UlamFloating

open MeasureTheory Set Filter
open scoped Topology InnerProductSpace

/-- Integrals over a moving cap are continuous whenever its limiting normal is nonzero. -/
theorem continuousAt_integral_waterlineCap
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Plane} {f : Plane → E} (hf : IntegrableOn f K)
    {u : Plane} (hu : u ≠ 0) (a : ℝ) :
    ContinuousAt (fun z : Plane × ℝ => ∫ x in waterlineCap K z.1 z.2, f x) (u, a) := by
  let F : Plane × ℝ → Plane → E := fun z => {x | ⟪z.1, x⟫_ℝ ≤ z.2}.indicator f
  have hmeas (z : Plane × ℝ) : MeasurableSet {x : Plane | ⟪z.1, x⟫_ℝ ≤ z.2} :=
    (isClosed_le (continuous_const.inner continuous_id) continuous_const).measurableSet
  have hzero : ∀ᵐ x ∂(volume : Measure Plane), ⟪u, x⟫_ℝ ≠ a := by
    rw [ae_iff]
    simpa only [not_not] using volume_waterline_eq_zero hu a
  have hlim : ∀ᵐ x ∂volume.restrict K,
      Tendsto (fun z => F z x) (𝓝 (u, a)) (𝓝 (F (u, a) x)) := by
    filter_upwards [ae_restrict_of_ae hzero] with x hx
    by_cases hle : ⟪u, x⟫_ℝ ≤ a
    · have hlt : ⟪u, x⟫_ℝ < a := lt_of_le_of_ne hle hx
      have he : ∀ᶠ z : Plane × ℝ in 𝓝 (u, a), ⟪z.1, x⟫_ℝ < z.2 :=
        ((continuous_fst.inner continuous_const).continuousAt.eventually_lt
          continuous_snd.continuousAt hlt)
      have hF : (fun z => F z x) =ᶠ[𝓝 (u, a)] (fun _ => f x) := he.mono fun z hz => by
        exact indicator_of_mem (show x ∈ {x | ⟪z.1, x⟫_ℝ ≤ z.2} from hz.le) f
      have hFx : F (u, a) x = f x :=
        indicator_of_mem (show x ∈ {x | ⟪u, x⟫_ℝ ≤ a} from hle) f
      rw [hFx]
      exact tendsto_const_nhds.congr' hF.symm
    · have hlt : a < ⟪u, x⟫_ℝ := lt_of_not_ge hle
      have he : ∀ᶠ z : Plane × ℝ in 𝓝 (u, a), z.2 < ⟪z.1, x⟫_ℝ :=
        continuous_snd.continuousAt.eventually_lt
          (continuous_fst.inner continuous_const).continuousAt hlt
      have hF : (fun z => F z x) =ᶠ[𝓝 (u, a)] (fun _ => 0) := he.mono fun z hz => by
        exact indicator_of_notMem (show x ∉ {x | ⟪z.1, x⟫_ℝ ≤ z.2} from not_le.mpr hz) f
      have hFx : F (u, a) x = 0 :=
        indicator_of_notMem (show x ∉ {x | ⟪u, x⟫_ℝ ≤ a} from hle) f
      rw [hFx]
      exact tendsto_const_nhds.congr' hF.symm
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict K)
    (fun x => ‖f x‖)
    (Eventually.of_forall fun z => hf.aestronglyMeasurable.indicator (hmeas z))
    (Eventually.of_forall fun z => Eventually.of_forall fun x =>
      norm_indicator_le_norm_self (s := {x | ⟪z.1, x⟫_ℝ ≤ z.2}) f x)
    hf.norm hlim
  have he (z : Plane × ℝ) : (∫ x in K, F z x) = ∫ x in waterlineCap K z.1 z.2, f x :=
    setIntegral_indicator (hmeas z)
  simp_rw [he] at ht
  exact ht.congr' (Eventually.of_forall he)

/-- The actual submerged area varies continuously with a nonzero waterline normal. -/
theorem continuousAt_planarArea_waterlineCap {K : Set Plane} (hK : IsCompact K)
    {u : Plane} (hu : u ≠ 0) (a : ℝ) :
    ContinuousAt (fun z : Plane × ℝ => planarArea (waterlineCap K z.1 z.2)) (u, a) := by
  have hf : IntegrableOn (fun _ : Plane => (1 : ℝ)) K :=
    continuous_const.continuousOn.integrableOn_compact hK
  simpa only [setIntegral_const, smul_eq_mul, mul_one, Measure.real, planarArea] using
    continuousAt_integral_waterlineCap hf hu a

/-- The actual submerged first moment varies continuously with the waterline. -/
theorem continuousAt_laminaFirstMoment_waterlineCap {K : Set Plane} (hK : IsCompact K)
    {u : Plane} (hu : u ≠ 0) (a : ℝ) :
    ContinuousAt (fun z : Plane × ℝ => laminaFirstMoment (waterlineCap K z.1 z.2))
      (u, a) :=
  continuousAt_integral_waterlineCap (integrableOn_laminaFirstMoment hK) hu a

end UlamFloating
