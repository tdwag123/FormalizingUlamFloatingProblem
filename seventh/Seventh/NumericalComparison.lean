import Seventh.GlobalNumerics
import Seventh.CellCertificate

/-! Convert a wholly rational contraction check into the trigonometric one. -/

namespace UlamFloating.Seventh

theorem certificate_contraction_of_rational {ell δ w V : ℝ}
    (hell : 0 < ell) (hV : 0 ≤ V)
    (hnum : δ⁻¹ ^ 2 * w ^ 2 + (((347107 : ℝ) / 800000) ^ 2 / 2) *
      ((((10847093 : ℝ) / 25000000)⁻¹ ^ 2) + (7 * ell)⁻¹ ^ 2 * w ^ 2) ^ 2 * V < 1) :
    δ⁻¹ ^ 2 * w ^ 2 + Real.sin (Real.pi / 7) ^ 2 / 2 *
      ((Real.sin (Real.pi / 7))⁻¹ ^ 2 + (7 * ell)⁻¹ ^ 2 * w ^ 2) ^ 2 * V < 1 := by
  have hs := certificate_sin_1
  simp only [one_mul] at hs
  have hspos : 0 < Real.sin (Real.pi / 7) := by linarith [hs.1]
  have hinv : (Real.sin (Real.pi / 7))⁻¹ ≤ ((10847093 : ℝ) / 25000000)⁻¹ :=
    (inv_le_inv₀ hspos (by norm_num)).mpr hs.1
  have hinvsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hinv
  have hD := add_le_add_right hinvsq ((7 * ell)⁻¹ ^ 2 * w ^ 2)
  have hDsq := (sq_le_sq₀ (by positivity) (by positivity)).mpr hD
  have hSsq := (sq_le_sq₀ hspos.le (by norm_num)).mpr hs.2
  have hF := div_le_div_of_nonneg_right hSsq (by norm_num : (0 : ℝ) ≤ 2)
  have hprod := mul_le_mul hF hDsq (sq_nonneg _)
    (by positivity : 0 ≤ ((347107 : ℝ) / 800000) ^ 2 / 2)
  have he := mul_le_mul_of_nonneg_right hprod hV
  linarith only [he, hnum]

end UlamFloating.Seventh
