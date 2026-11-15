import Seventh.CoefficientBounds
import Seventh.Contraction

/-!
# Assembly of the spectral energy estimates

The energies are normalized interval integrals. Parseval is applied to the
entire integer spectrum, including the resonant nonlinear remainder modes.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The full tangent energy is controlled by angle energy and remainder energy. -/
theorem ContactSystem.tangent_energy_le {γ : ℝ → Plane} {P l c : ℝ}
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (hP : 0 < P) (hl : 0 < l) :
    intervalVariance P (tangentFluctuation P θ α) 0 ≤
      (Real.sin (Real.pi / 7))⁻¹ ^ 2 * intervalVariance P α (Real.pi / 7) +
      (7 * (Real.pi * l / P))⁻¹ ^ 2 *
        intervalVariance P (fun t => sineRemainder (Real.pi / 7) c (α t)) 0 := by
  have hvp : Function.Periodic (fun t => α t - Real.pi / 7) P := by
    intro t; dsimp; rw [hs.periodic_angle t]
  have hNp : Function.Periodic (fun t => sineRemainder (Real.pi / 7) c (α t)) P := by
    intro t; dsimp only; rw [hs.periodic_angle t]
  have hu := hasSum_real_fourier_energy hP hs.contDiff_tangentFluctuation.continuous
    (hs.periodic_tangentFluctuation hP)
  have hv := hasSum_real_fourier_energy hP (hs.contDiff_angle.continuous.sub continuous_const) hvp
  have hN := hasSum_real_fourier_energy hP
    ((continuous_sineRemainder (Real.pi / 7) c).comp hs.contDiff_angle.continuous) hNp
  have he := hasSum_le (fun n => hs.tangent_coefficient_bound (c := c) hP hl n) hu
    ((hv.mul_left ((Real.sin (Real.pi / 7))⁻¹ ^ 2)).add
      (hN.mul_left ((7 * (Real.pi * l / P))⁻¹ ^ 2)))
  simpa only [intervalVariance, sub_zero] using he

/-- Each first angle harmonic is bounded quadratically by tangent energy. -/
theorem ContactSystem.first_angle_harmonic_sq_bound {K : Set Plane} {P l : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) {n : ℤ} (hn : n = 1 ∨ n = -1) :
    ‖fourierCoeffOn hb.period_pos (fun t => ((α t - Real.pi / 7 : ℝ) : ℂ)) n‖ ^ 2 ≤
      (Real.sin (Real.pi / 7)) ^ 2 / 4 *
        (intervalVariance P (tangentFluctuation P θ α) 0) ^ 2 := by
  have hsine : 0 < Real.sin (Real.pi / 7) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])
  have hsin : |Real.sin ((n : ℝ) * (Real.pi / 7))| = Real.sin (Real.pi / 7) := by
    rcases hn with rfl | rfl <;>
      simp only [Int.cast_one, Int.cast_neg, one_mul, neg_mul, Real.sin_neg, abs_neg,
        abs_of_pos hsine]
  have hrel := hs.fourier_norm_relation hb.period_pos n
  rw [hsin] at hrel
  have hu := hs.first_tangent_harmonic_bound hb hl hc hn
  have hU0 := intervalVariance_nonneg (f := tangentFluctuation P θ α) (a := 0) hb.period_pos
  have hm := mul_le_mul_of_nonneg_left hu hsine.le
  rw [hrel] at hm
  have hsquare := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hm
  nlinarith only [hsquare]

/-- The complete angle energy is bounded by the gapped remainder plus the first pair. -/
theorem ContactSystem.angle_energy_le {K : Set Plane} {P l c δ : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α)
    (hδ : 0 < δ) (hgap : SpectralGapBounds (Real.pi * l / P) c δ) :
    intervalVariance P α (Real.pi / 7) ≤
      δ⁻¹ ^ 2 * intervalVariance P (fun t => sineRemainder (Real.pi / 7) c (α t)) 0 +
      (Real.sin (Real.pi / 7)) ^ 2 / 2 *
        (intervalVariance P (tangentFluctuation P θ α) 0) ^ 2 := by
  have hvp : Function.Periodic (fun t => α t - Real.pi / 7) P := by
    intro t; dsimp; rw [hs.periodic_angle t]
  have hNp : Function.Periodic (fun t => sineRemainder (Real.pi / 7) c (α t)) P := by
    intro t; dsimp only; rw [hs.periodic_angle t]
  have hv := hasSum_real_fourier_energy hb.period_pos
    (hs.contDiff_angle.continuous.sub continuous_const) hvp
  have hN := hasSum_real_fourier_energy hb.period_pos
    ((continuous_sineRemainder (Real.pi / 7) c).comp hs.contDiff_angle.continuous) hNp
  have he := energy_le_of_except_first_bounds hv hN (sq_nonneg δ⁻¹)
    (fun n hn => hs.first_angle_harmonic_sq_bound hb hl hc hn)
    (fun n hp hm => hs.angle_coefficient_bound hb.period_pos hl hδ hgap hp hm)
  simp only [Function.comp_apply, intervalVariance, sub_zero] at he ⊢
  nlinarith only [he]

/-- The scalar energy argument, independent of the geometry and Fourier API. -/
theorem zero_energy_of_three_bounds {V U E A B D F w Vmax : ℝ}
    (hV0 : 0 ≤ V) (hU0 : 0 ≤ U) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hE : E ≤ w ^ 2 * V) (hU : U ≤ A * V + B * E)
    (hV : V ≤ D * E + F * U ^ 2) (hmax : V ≤ Vmax)
    (hcontract : D * w ^ 2 + F * (A + B * w ^ 2) ^ 2 * Vmax < 1) : V = 0 := by
  have hD0 : 0 ≤ A + B * w ^ 2 := by positivity
  have hUE : U ≤ (A + B * w ^ 2) * V := by
    have he := mul_le_mul_of_nonneg_left hE hB
    nlinarith only [hU, he]
  have hUsq := (sq_le_sq₀ hU0 (mul_nonneg hD0 hV0)).mpr hUE
  have hE' := mul_le_mul_of_nonneg_left hE hD
  have hU' := mul_le_mul_of_nonneg_left hUsq hF
  have hmax' := mul_le_mul_of_nonneg_right hmax hV0
  have hmax'' := mul_le_mul_of_nonneg_left hmax' (mul_nonneg hF (sq_nonneg (A + B * w ^ 2)))
  have hfinal : V ≤ (D * w ^ 2 + F * (A + B * w ^ 2) ^ 2 * Vmax) * V := by
    nlinarith only [hV, hE', hU', hmax'']
  by_contra hn
  have hpos := lt_of_le_of_ne hV0 (Ne.symm hn)
  have he := mul_lt_mul_of_pos_right hcontract hpos
  nlinarith only [he, hfinal]

/-- The geometric rigidity conclusion from a valid spectral certificate.
The numerical certificate must still be supplied; this is not the unconditional theorem. -/
theorem ContactSystem.isDisk_of_spectral_certificate {K : Set Plane} {P l c δ w Vmax : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α)
    (hδ : 0 < δ) (hw : 0 ≤ w) (hgap : SpectralGapBounds (Real.pi * l / P) c δ)
    (herr : ∀ t, |sineRemainder (Real.pi / 7) c (α t)| ≤ w * |α t - Real.pi / 7|)
    (hmax : intervalVariance P α (Real.pi / 7) ≤ Vmax)
    (hcontract : δ⁻¹ ^ 2 * w ^ 2 + (Real.sin (Real.pi / 7)) ^ 2 / 2 *
      ((Real.sin (Real.pi / 7))⁻¹ ^ 2 + (7 * (Real.pi * l / P))⁻¹ ^ 2 * w ^ 2) ^ 2 * Vmax < 1) :
    IsDisk K := by
  have hV0 := intervalVariance_nonneg (f := α) (a := Real.pi / 7) hb.period_pos
  have hU0 := intervalVariance_nonneg (f := tangentFluctuation P θ α) (a := 0) hb.period_pos
  have hE := sineRemainder_energy_le hb.period_pos hw hs.contDiff_angle.continuous (fun t _ => herr t)
  have hU := hs.tangent_energy_le (c := c) hb.period_pos hl
  have hV := hs.angle_energy_le hb hl hc hδ hgap
  have hzero := zero_energy_of_three_bounds hV0 hU0 (sq_nonneg _) (sq_nonneg _)
    (sq_nonneg _) (by positivity) hE hU hV hmax hcontract
  have hconstant := eq_mean_of_variance_zero hb.period_pos hs.contDiff_angle.continuous
    hs.periodic_angle hzero
  exact hs.isDisk_of_constant hb hl (fun t => (hconstant t).trans (hconstant 0).symm)

end UlamFloating.Seventh
