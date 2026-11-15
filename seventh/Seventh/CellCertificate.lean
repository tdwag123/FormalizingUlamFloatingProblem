import Seventh.EnergyAssembly
import Seventh.PeakVariance

/-!
# Certificates for closed frequency cells

A certificate consists only of explicit real inequalities. Its application
derives the angle interval, variance, approximation, spectral gap, and final
strict contraction from the original boundary hypotheses.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

/-- Data checked for one cell `ell ≤ π*l/P ≤ r`. -/
structure CellCertificate (ell r B U c w δ J V : ℝ) : Prop where
  frequency_pos : 0 < ell
  lower_pos : 0 < B
  lower_lt_mean : B < Real.pi / 7
  mean_lt_upper : Real.pi / 7 < U
  upper_le : U ≤ 6 / 5
  width_nonneg : 0 ≤ w
  gap_pos : 0 < δ
  variance_nonneg : 0 ≤ V
  projection : r < (Real.pi / 7) * Real.cos B
  jensen : 2 * (Real.sin (Real.pi / 7) - ell) ≤ J * Real.sin B
  angle_upper : 2 * Real.cos (U / 2 + 2 * B) < Real.sin U ∨
    3 * Real.pi * J < ell * (U - Real.pi / 7) ^ 3
  variance : J ≤ V ∨ (Real.pi / 7 - B) * (U - Real.pi / 7) ≤ V
  approximation_lower : (c - w) * (U - Real.pi / 7) ≤ Real.sin U - Real.sin (Real.pi / 7)
  approximation_upper : Real.sin (Real.pi / 7) - Real.sin B ≤ (c + w) * (Real.pi / 7 - B)
  gap_center : δ ≤ c
  gap_two : seventhMultiplier r 2 ≤ c - δ
  gap_three : seventhMultiplier r 3 ≤ c - δ
  gap_eight : c + δ ≤ seventhMultiplier ell 8
  gap_nine : c + δ ≤ seventhMultiplier ell 9
  gap_ten : c + δ ≤ seventhMultiplier ell 10
  contraction : δ⁻¹ ^ 2 * w ^ 2 + Real.sin (Real.pi / 7) ^ 2 / 2 *
    ((Real.sin (Real.pi / 7))⁻¹ ^ 2 + (7 * ell)⁻¹ ^ 2 * w ^ 2) ^ 2 * V < 1

theorem seventhMultiplier_mono_frequency {f g : ℝ} (hfg : f ≤ g) {n : ℤ}
    (hn : 0 ≤ n) (hr1 : 1 ≤ n % 7) (hr3 : n % 7 ≤ 3) :
    seventhMultiplier f n ≤ seventhMultiplier g n := by
  unfold seventhMultiplier
  rw [cot_frequency_residue n]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfg (by exact_mod_cast hn)) (cot_residue_pos hr1 hr3).le

theorem CellCertificate.spectralGap {ell r B U c w δ J V frequency : ℝ}
    (hc : CellCertificate ell r B U c w δ J V) (hlo : ell ≤ frequency) (hhi : frequency ≤ r) :
    SpectralGapBounds frequency c δ where
  center := hc.gap_center
  mode_two := (seventhMultiplier_mono_frequency hhi (by norm_num) (by norm_num) (by norm_num)).trans hc.gap_two
  mode_three := (seventhMultiplier_mono_frequency hhi (by norm_num) (by norm_num) (by norm_num)).trans hc.gap_three
  mode_eight := hc.gap_eight.trans (seventhMultiplier_mono_frequency hlo (by norm_num) (by norm_num) (by norm_num))
  mode_nine := hc.gap_nine.trans (seventhMultiplier_mono_frequency hlo (by norm_num) (by norm_num) (by norm_num))
  mode_ten := hc.gap_ten.trans (seventhMultiplier_mono_frequency hlo (by norm_num) (by norm_num) (by norm_num))

theorem CellCertificate.contraction_at_frequency {ell r B U c w δ J V frequency : ℝ}
    (hc : CellCertificate ell r B U c w δ J V) (hlo : ell ≤ frequency) :
    δ⁻¹ ^ 2 * w ^ 2 + Real.sin (Real.pi / 7) ^ 2 / 2 *
      ((Real.sin (Real.pi / 7))⁻¹ ^ 2 + (7 * frequency)⁻¹ ^ 2 * w ^ 2) ^ 2 * V < 1 := by
  have hell := hc.frequency_pos
  have hfrequency := hell.trans_le hlo
  have hinv : (7 * frequency)⁻¹ ≤ (7 * ell)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr (by linarith)
  have hsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hinv
  have hD := add_le_add_left (mul_le_mul_of_nonneg_right hsq (sq_nonneg w))
    ((Real.sin (Real.pi / 7))⁻¹ ^ 2)
  have hDsquare := (sq_le_sq₀ (by positivity) (by positivity)).mpr hD
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hDsquare (by positivity : 0 ≤ Real.sin (Real.pi / 7) ^ 2 / 2))
    hc.variance_nonneg
  linarith [hc.contraction]

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A checked cell certificate proves rigidity for every boundary whose frequency lies in it. -/
theorem CellCertificate.isDisk {K : Set Plane} {P l ell r B U c w δ J V : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hchord : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α)
    (hcert : CellCertificate ell r B U c w δ J V)
    (hlo : ell ≤ Real.pi * l / P) (hhi : Real.pi * l / P ≤ r) : IsDisk K := by
  have hBpi : B < Real.pi := by linarith [hcert.lower_lt_mean, Real.pi_pos]
  have hB : ∀ t, B ≤ α t := fun t =>
    (hs.angle_gt_of_frequency_comparison hb hl hchord hBpi.le hhi hcert.projection t).le
  have hsinB := Real.sin_pos_of_pos_of_lt_pi hcert.lower_pos hBpi
  have hJ : intervalVariance P α (Real.pi / 7) ≤ J := by
    have he := hs.variance_le_sine_deficit hb hl hchord hcert.lower_pos hB
    have he' := (le_div_iff₀ hsinB).mp he
    have hJ := hcert.jensen
    nlinarith
  have hU : ∀ t, α t < U := by
    rcases hcert.angle_upper with hn | hp
    · exact hs.angle_lt_of_comparison hb hl hchord hcert.lower_pos.le
        (by linarith [hcert.mean_lt_upper, Real.pi_pos]) hB hn
    · exact hs.angle_lt_of_peak_bound hb hl hchord hcert.frequency_pos hlo
        hcert.mean_lt_upper.le hJ hp
  have hV : intervalVariance P α (Real.pi / 7) ≤ V := by
    rcases hcert.variance with hj | hr
    · exact hJ.trans hj
    · exact (intervalVariance_le_range hb.period_pos hs.contDiff_angle.continuous hs.integral_angle
        (fun t _ => ⟨hB t, (hU t).le⟩)).trans hr
  have herr (t : ℝ) : |sineRemainder (Real.pi / 7) c (α t)| ≤ w * |α t - Real.pi / 7| := by
    have hconc : ConcaveOn ℝ (Icc B U) Real.sin :=
      strictConcaveOn_sin_Icc.concaveOn.subset
        (Icc_subset_Icc hcert.lower_pos.le (by linarith [hcert.upper_le, Real.pi_gt_d2]))
        (convex_Icc _ _)
    exact abs_sub_linear_le_of_endpoint_bounds hconc hcert.lower_lt_mean hcert.mean_lt_upper
      ⟨hB t, (hU t).le⟩ hcert.approximation_lower hcert.approximation_upper
  exact hs.isDisk_of_spectral_certificate hb hl hchord hcert.gap_pos hcert.width_nonneg
    (hcert.spectralGap hlo hhi) herr hV (hcert.contraction_at_frequency hlo)

end UlamFloating.Seventh
