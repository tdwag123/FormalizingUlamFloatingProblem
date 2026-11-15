import Seventh.PhaseAlgebra
import Seventh.AngleBounds

/-!
# Reduction of temporal frequencies modulo seven

Sine magnitudes and cotangents reduce to six residue classes. The multiplier
itself retains the full integer index, including arbitrarily high frequencies.
-/

namespace UlamFloating.Seventh

theorem frequency_angle_decomposition (n : ℤ) :
    (n : ℝ) * (Real.pi / 7) = ((n % 7 : ℤ) : ℝ) * (Real.pi / 7) +
      ((n / 7 : ℤ) : ℝ) * Real.pi := by
  have he : (n : ℝ) = ((n % 7 : ℤ) : ℝ) + 7 * ((n / 7 : ℤ) : ℝ) := by
    exact_mod_cast (Int.emod_add_mul_ediv n 7).symm
  calc
    _ = (((n % 7 : ℤ) : ℝ) + 7 * ((n / 7 : ℤ) : ℝ)) * (Real.pi / 7) := by rw [← he]
    _ = _ := by ring

theorem abs_sin_frequency_residue (n : ℤ) :
    |Real.sin ((n : ℝ) * (Real.pi / 7))| =
      |Real.sin (((n % 7 : ℤ) : ℝ) * (Real.pi / 7))| := by
  have he : |(-1 : ℝ) ^ (n / 7)| = 1 := by
    rw [← Real.norm_eq_abs, norm_zpow]
    norm_num
  rw [frequency_angle_decomposition, Real.sin_add_int_mul_pi, abs_mul, he, one_mul]

/-- All nonresonant integer modes have sine magnitude at least `sin(π/7)`. -/
theorem abs_sin_frequency_ge {n : ℤ} (hn : ¬ (7 : ℤ) ∣ n) :
    Real.sin (Real.pi / 7) ≤ |Real.sin ((n : ℝ) * (Real.pi / 7))| := by
  have hr0 := Int.emod_nonneg n (by norm_num : (7 : ℤ) ≠ 0)
  have hr7 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 7)
  have hrne : n % 7 ≠ 0 := fun h => hn (Int.dvd_of_emod_eq_zero h)
  have hr1 : (1 : ℝ) ≤ ((n % 7 : ℤ) : ℝ) := by exact_mod_cast (show 1 ≤ n % 7 by omega)
  have hr6 : ((n % 7 : ℤ) : ℝ) ≤ (6 : ℝ) := by exact_mod_cast (show n % 7 ≤ 6 by omega)
  have ha : 0 < Real.pi / 7 := by positivity
  have hlo := mul_le_mul_of_nonneg_right hr1 ha.le
  have hhi := mul_le_mul_of_nonneg_right hr6 ha.le
  have hs := sin_ge_on_symmetric_interval ha.le
    (by linarith [Real.pi_pos] : Real.pi / 7 < Real.pi / 2)
    (by linarith : Real.pi / 7 ≤ ((n % 7 : ℤ) : ℝ) * (Real.pi / 7))
    (by linarith : ((n % 7 : ℤ) : ℝ) * (Real.pi / 7) ≤ Real.pi - Real.pi / 7)
  rw [abs_sin_frequency_residue]
  exact hs.trans (le_abs_self _)

theorem cot_frequency_residue (n : ℤ) :
    Real.cot ((n : ℝ) * (Real.pi / 7)) =
      Real.cot (((n % 7 : ℤ) : ℝ) * (Real.pi / 7)) := by
  rw [frequency_angle_decomposition, Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin,
    Real.sin_add_int_mul_pi, Real.cos_add_int_mul_pi]
  exact mul_div_mul_left _ _ (zpow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0))

/-- The exact spectral multiplier in dimensionless frequency coordinates. -/
noncomputable def seventhMultiplier (frequency : ℝ) (n : ℤ) : ℝ :=
  frequency * (n : ℝ) * Real.cot ((n : ℝ) * (Real.pi / 7))

theorem seventhMultiplier_neg (frequency : ℝ) (n : ℤ) :
    seventhMultiplier frequency (-n) = seventhMultiplier frequency n := by
  simp only [seventhMultiplier, Int.cast_neg, neg_mul, Real.cot_eq_cos_div_sin,
    Real.cos_neg, Real.sin_neg, div_neg, mul_neg, neg_neg]

/-- Cotangents of the first three nonzero residues are positive. -/
theorem cot_residue_pos {r : ℤ} (hlo : 1 ≤ r) (hhi : r ≤ 3) :
    0 < Real.cot ((r : ℝ) * (Real.pi / 7)) := by
  have hrlo : (1 : ℝ) ≤ r := by exact_mod_cast hlo
  have hrhi : (r : ℝ) ≤ 3 := by exact_mod_cast hhi
  have hl := mul_le_mul_of_nonneg_right hrlo (by positivity : 0 ≤ Real.pi / 7)
  have hh := mul_le_mul_of_nonneg_right hrhi (by positivity : 0 ≤ Real.pi / 7)
  rw [Real.cot_eq_cos_div_sin]
  apply div_pos
  · apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_pos]
  · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

/-- Cotangents of the final three nonzero residues are negative. -/
theorem cot_residue_neg {r : ℤ} (hlo : 4 ≤ r) (hhi : r ≤ 6) :
    Real.cot ((r : ℝ) * (Real.pi / 7)) < 0 := by
  have hrlo : (4 : ℝ) ≤ r := by exact_mod_cast hlo
  have hrhi : (r : ℝ) ≤ 6 := by exact_mod_cast hhi
  have hl := mul_le_mul_of_nonneg_right hrlo (by positivity : 0 ≤ Real.pi / 7)
  have hh := mul_le_mul_of_nonneg_right hrhi (by positivity : 0 ≤ Real.pi / 7)
  rw [Real.cot_eq_cos_div_sin]
  apply div_neg_of_neg_of_pos
  · apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> linarith [Real.pi_pos]
  · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith [Real.pi_pos]

/-- The full multiplier increases along each of its three positive residue classes. -/
theorem seventhMultiplier_mono_residue {frequency : ℝ} {m n : ℤ}
    (hf : 0 ≤ frequency) (hm : 1 ≤ m % 7) (hm3 : m % 7 ≤ 3)
    (hres : m % 7 = n % 7) (hmn : m ≤ n) :
    seventhMultiplier frequency m ≤ seventhMultiplier frequency n := by
  unfold seventhMultiplier
  rw [cot_frequency_residue m, cot_frequency_residue n, ← hres]
  apply mul_le_mul_of_nonneg_right _ (cot_residue_pos hm hm3).le
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmn) hf

/-- Six finite comparisons suffice to bound every nonexceptional mode. -/
structure SpectralGapBounds (frequency c δ : ℝ) : Prop where
  center : δ ≤ c
  mode_two : seventhMultiplier frequency 2 ≤ c - δ
  mode_three : seventhMultiplier frequency 3 ≤ c - δ
  mode_eight : c + δ ≤ seventhMultiplier frequency 8
  mode_nine : c + δ ≤ seventhMultiplier frequency 9
  mode_ten : c + δ ≤ seventhMultiplier frequency 10

theorem SpectralGapBounds.positive_mode_gap {frequency c δ : ℝ}
    (hs : SpectralGapBounds frequency c δ) (hf : 0 ≤ frequency)
    {n : ℤ} (hn : 2 ≤ n) (hseven : ¬ (7 : ℤ) ∣ n) :
    δ ≤ |seventhMultiplier frequency n - c| := by
  have hr0 := Int.emod_nonneg n (by norm_num : (7 : ℤ) ≠ 0)
  have hr7 := Int.emod_lt_of_pos n (by norm_num : (0 : ℤ) < 7)
  have hrne : n % 7 ≠ 0 := fun h => hseven (Int.dvd_of_emod_eq_zero h)
  by_cases hr4 : 4 ≤ n % 7
  · have hcot := (cot_residue_neg hr4 (by omega : n % 7 ≤ 6)).le
    have hmul : seventhMultiplier frequency n ≤ 0 := by
      rw [seventhMultiplier, cot_frequency_residue]
      exact mul_nonpos_of_nonneg_of_nonpos
        (mul_nonneg hf (by exact_mod_cast (by omega : 0 ≤ n))) hcot
    have he := neg_le_abs (seventhMultiplier frequency n - c)
    linarith [hs.center]
  have hr1 : 1 ≤ n % 7 := by omega
  have hr3 : n % 7 ≤ 3 := by omega
  interval_cases hr : n % 7
  · have hm := seventhMultiplier_mono_residue hf (m := 8) (by norm_num) (by norm_num)
      (by omega : 8 % 7 = n % 7) (by omega : 8 ≤ n)
    have he := le_abs_self (seventhMultiplier frequency n - c)
    linarith [hs.mode_eight]
  · by_cases heq : n = 2
    · subst n
      have he := neg_le_abs (seventhMultiplier frequency 2 - c)
      linarith [hs.mode_two]
    have hm := seventhMultiplier_mono_residue hf (m := 9) (by norm_num) (by norm_num)
      (by omega : 9 % 7 = n % 7) (by omega : 9 ≤ n)
    have he := le_abs_self (seventhMultiplier frequency n - c)
    linarith [hs.mode_nine]
  · by_cases heq : n = 3
    · subst n
      have he := neg_le_abs (seventhMultiplier frequency 3 - c)
      linarith [hs.mode_three]
    have hm := seventhMultiplier_mono_residue hf (m := 10) (by norm_num) (by norm_num)
      (by omega : 10 % 7 = n % 7) (by omega : 10 ≤ n)
    have he := le_abs_self (seventhMultiplier frequency n - c)
    linarith [hs.mode_ten]

/-- The finite comparisons cover all integer modes except the first pair and resonances. -/
theorem SpectralGapBounds.mode_gap {frequency c δ : ℝ}
    (hs : SpectralGapBounds frequency c δ) (hf : 0 ≤ frequency)
    {n : ℤ} (hseven : ¬ (7 : ℤ) ∣ n) (hp : n ≠ 1) (hm : n ≠ -1) :
    δ ≤ |seventhMultiplier frequency n - c| := by
  have hn0 : n ≠ 0 := fun h => hseven (by simp [h])
  by_cases hn : 0 ≤ n
  · exact hs.positive_mode_gap hf (by omega) hseven
  · have he := hs.positive_mode_gap hf (n := -n) (by omega)
      (by simpa only [dvd_neg] using hseven)
    simpa only [seventhMultiplier_neg] using he

end UlamFloating.Seventh
