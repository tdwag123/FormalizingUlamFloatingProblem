import Seventh.Concavity
import Seventh.Variance

/-!
# Uniform secant approximation of a concave function

The midpoint of the endpoint slopes gives a linear approximation with an
error proportional to distance from the expansion point. This construction
is reusable for concave functions other than sine.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

/-- For a concave function, secant slopes from a fixed base point decrease. -/
theorem concave_secant_antitone {f : ℝ → ℝ} {S : Set ℝ} {a x y : ℝ}
    (hf : ConcaveOn ℝ S f) (ha : a ∈ S) (hx : x ∈ S) (hy : y ∈ S)
    (hxa : x ≠ a) (hya : y ≠ a) (hxy : x ≤ y) :
    (f y - f a) / (y - a) ≤ (f x - f a) / (x - a) := by
  have he := hf.neg.secant_mono ha hx hy hxa hya hxy
  simp only [Pi.neg_apply] at he
  rw [show -f x - -f a = -(f x - f a) by ring,
    show -f y - -f a = -(f y - f a) by ring, neg_div, neg_div] at he
  linarith

/-- The center of the two endpoint secant slopes. -/
noncomputable def secantCenter (f : ℝ → ℝ) (B a U : ℝ) : ℝ :=
  ((f U - f a) / (U - a) + (f B - f a) / (B - a)) / 2

/-- Half the difference of the two endpoint secant slopes. -/
noncomputable def secantWidth (f : ℝ → ℝ) (B a U : ℝ) : ℝ :=
  ((f B - f a) / (B - a) - (f U - f a) / (U - a)) / 2

theorem secantWidth_nonneg {f : ℝ → ℝ} {B a U : ℝ}
    (hf : ConcaveOn ℝ (Icc B U) f) (hBa : B < a) (haU : a < U) :
    0 ≤ secantWidth f B a U := by
  have he := concave_secant_antitone hf ⟨hBa.le, haU.le⟩
    ⟨le_rfl, (hBa.trans haU).le⟩ ⟨(hBa.trans haU).le, le_rfl⟩
    hBa.ne haU.ne' (hBa.trans haU).le
  dsimp [secantWidth]
  linarith

/-- The deviation from the centered linear approximation is uniformly bounded. -/
theorem abs_sub_secantCenter_le {f : ℝ → ℝ} {B a U z : ℝ}
    (hf : ConcaveOn ℝ (Icc B U) f) (hBa : B < a) (haU : a < U)
    (hz : z ∈ Icc B U) :
    |f z - f a - secantCenter f B a U * (z - a)| ≤
      secantWidth f B a U * |z - a| := by
  by_cases hza : z = a
  · subst z; simp
  have hlo := concave_secant_antitone hf ⟨hBa.le, haU.le⟩ hz
    ⟨(hBa.trans haU).le, le_rfl⟩ hza haU.ne' hz.2
  have hhi := concave_secant_antitone hf ⟨hBa.le, haU.le⟩
    ⟨le_rfl, (hBa.trans haU).le⟩ hz hBa.ne hza hz.1
  have he : |(f z - f a) / (z - a) - secantCenter f B a U| ≤ secantWidth f B a U := by
    dsimp [secantCenter, secantWidth]
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hid : f z - f a - secantCenter f B a U * (z - a) =
      ((f z - f a) / (z - a) - secantCenter f B a U) * (z - a) := by
    field_simp [sub_ne_zero.mpr hza]
  rw [hid, abs_mul]
  exact mul_le_mul_of_nonneg_right he (abs_nonneg _)

/-- Pointwise relative approximation error implies the corresponding energy bound. -/
theorem integral_sq_le_of_abs_le {P w : ℝ} {N v : ℝ → ℝ}
    (hP : 0 ≤ P) (hw : 0 ≤ w) (hN : Continuous N) (hv : Continuous v)
    (he : ∀ t ∈ Icc 0 P, |N t| ≤ w * |v t|) :
    (∫ t in (0 : ℝ)..P, (N t) ^ 2) ≤ w ^ 2 * ∫ t in (0 : ℝ)..P, (v t) ^ 2 := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_mono_on (μ := volume) hP
    ((hN.pow 2).intervalIntegrable _ _)
    ((continuous_const.mul (hv.pow 2)).intervalIntegrable _ _)
  intro t ht
  have hsq := sq_le_sq₀ (abs_nonneg (N t)) (mul_nonneg hw (abs_nonneg (v t))) |>.mpr (he t ht)
  simpa only [sq_abs, mul_pow] using hsq

/-- A rational center and width may be certified directly by the endpoint
secant inequalities, avoiding division in the certificate itself. -/
theorem abs_sub_linear_le_of_endpoint_bounds {f : ℝ → ℝ} {B a U z c w : ℝ}
    (hf : ConcaveOn ℝ (Icc B U) f) (hBa : B < a) (haU : a < U)
    (hz : z ∈ Icc B U)
    (hlower : (c - w) * (U - a) ≤ f U - f a)
    (hupper : f a - f B ≤ (c + w) * (a - B)) :
    |f z - f a - c * (z - a)| ≤ w * |z - a| := by
  by_cases hza : z = a
  · subst z; simp
  have hlo := concave_secant_antitone hf ⟨hBa.le, haU.le⟩ hz
    ⟨(hBa.trans haU).le, le_rfl⟩ hza haU.ne' hz.2
  have hhi := concave_secant_antitone hf ⟨hBa.le, haU.le⟩
    ⟨le_rfl, (hBa.trans haU).le⟩ hz hBa.ne hza hz.1
  have hpminus : c - w ≤ (f U - f a) / (U - a) :=
    (le_div_iff₀ (sub_pos.mpr haU)).mpr hlower
  have hpplus : (f B - f a) / (B - a) ≤ c + w := by
    have he := (div_le_iff₀ (sub_pos.mpr hBa)).mpr hupper
    rw [show f B - f a = -(f a - f B) by ring,
      show B - a = -(a - B) by ring, neg_div_neg_eq]
    exact he
  have he : |(f z - f a) / (z - a) - c| ≤ w :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hid : f z - f a - c * (z - a) = ((f z - f a) / (z - a) - c) * (z - a) := by
    field_simp [sub_ne_zero.mpr hza]
  rw [hid, abs_mul]
  exact mul_le_mul_of_nonneg_right he (abs_nonneg _)

end UlamFloating.Seventh
