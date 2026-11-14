import UlamFloating.ChordWinding
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Geometry.Euclidean.Angle.Oriented.Rotation

/-!
# Positive tangent–chord angles

The local reflection law is converted to real angles in `(0, π)`.
The statements apply to any oriented two-dimensional real inner product space.
-/

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Positively oriented unit vectors have a real angle strictly between zero
and pi, whose cosine and sine are their inner product and oriented area. -/
theorem exists_positive_unit_angle (o : Orientation ℝ E (Fin 2)) {u w : E}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (harea : 0 < o.areaForm u w) :
    ∃ α : ℝ, 0 < α ∧ α < Real.pi ∧
      Real.cos α = ⟪u, w⟫_ℝ ∧ Real.sin α = o.areaForm u w ∧
      w = o.rotation (α : Real.Angle) u := by
  have hid := o.inner_sq_add_areaForm_sq u w
  rw [hu, hw] at hid
  have hc0 : -1 < ⟪u, w⟫_ℝ := by nlinarith [sq_pos_of_pos harea]
  have hc1 : ⟪u, w⟫_ℝ < 1 := by nlinarith [sq_pos_of_pos harea]
  let α := Real.arccos ⟪u, w⟫_ℝ
  have ha0 : 0 < α := Real.arccos_pos.mpr hc1
  have hap : α < Real.pi := by
    apply lt_of_le_of_ne (Real.arccos_le_pi _)
    intro heq
    have := Real.arccos_eq_pi.mp heq
    linarith
  have hcos : Real.cos α = ⟪u, w⟫_ℝ := Real.cos_arccos hc0.le hc1.le
  have hsin : Real.sin α = o.areaForm u w := by
    have hs := Real.sin_pos_of_pos_of_lt_pi ha0 hap
    have hs2 := Real.cos_sq_add_sin_sq α
    rw [hcos] at hs2
    nlinarith
  refine ⟨α, ha0, hap, hcos, hsin, ?_⟩
  have hd := norm_sq_smul_eq_inner_add_area o u w
  simpa only [hu, one_pow, one_smul, o.rotation_apply, Real.Angle.cos_coe,
    Real.Angle.sin_coe, hcos, hsin] using hd

/-- Reflection in a unit chord sends the incoming tangent to the same
positive rotation of the chord as the chord is of the incoming tangent. -/
theorem reflection_eq_rotation (o : Orientation ℝ E (Fin 2)) {u w v : E} {α : ℝ}
    (hu : ‖u‖ = 1) (hw : w = o.rotation (α : Real.Angle) u)
    (hv : v = (2 * ⟪w, u⟫_ℝ) • w - u) :
    v = o.rotation (α : Real.Angle) w := by
  have hi : ⟪w, u⟫_ℝ = Real.cos α := by
    rw [hw, o.rotation_apply]
    simp only [Real.Angle.cos_coe, Real.Angle.sin_coe, inner_add_left,
      real_inner_smul_left, real_inner_self_eq_norm_sq, hu, one_pow,
      mul_one, o.inner_rightAngleRotation_left, o.areaForm_apply_self, mul_zero, add_zero]
  rw [hv, hi, hw]
  simp only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe,
    map_add, map_smul, o.rightAngleRotation_rightAngleRotation]
  match_scalars <;> nlinarith [Real.cos_sq_add_sin_sq α]

/-- Two real rotation angles in `(0, 2π)` acting identically on a nonzero
vector are equal as real numbers, not merely modulo a full turn. -/
theorem rotation_angle_unique (o : Orientation ℝ E (Fin 2)) {w : E} (hw : w ≠ 0)
    {a b : ℝ} (ha0 : 0 < a) (ha2 : a < 2 * Real.pi)
    (hb0 : 0 < b) (hb2 : b < 2 * Real.pi)
    (hab : o.rotation (a : Real.Angle) w = o.rotation (b : Real.Angle) w) : a = b := by
  have he : o.rotation ((a - b : ℝ) : Real.Angle) w = w := by
    have h := congrArg (o.rotation (- (b : Real.Angle))) hab
    rw [o.rotation_rotation, o.rotation_rotation, neg_add_cancel, o.rotation_zero] at h
    simpa only [Real.Angle.coe_sub, sub_eq_add_neg, add_comm] using h
  have he' : w = Real.cos (a - b) • w +
      Real.sin (a - b) • o.rightAngleRotation w := by
    simpa only [o.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe] using he.symm
  obtain ⟨k, hk⟩ := rotation_angle_eq_int_mul o hw he'
  have hklo : (-1 : ℝ) < k := by nlinarith [Real.pi_pos]
  have hkhi : (k : ℝ) < 1 := by nlinarith [Real.pi_pos]
  have hklo' : (-1 : ℤ) < k := by exact_mod_cast hklo
  have hkhi' : k < (1 : ℤ) := by exact_mod_cast hkhi
  have hk0 : k = 0 := by omega
  simp only [hk0, Int.cast_zero, zero_mul] at hk
  linarith

/-- At two consecutive chords, the direction increment is the sum of
their positive tangent–chord angles. The range hypotheses resolve the
possible full-turn ambiguity. -/
theorem tangent_chord_angle_add (o : Orientation ℝ E (Fin 2))
    {w z v : E} {α β δ : ℝ} (hw : w ≠ 0)
    (ha : 0 < α ∧ α < Real.pi) (hb : 0 < β ∧ β < Real.pi)
    (hd : 0 < δ ∧ δ < Real.pi)
    (hv : v = o.rotation (α : Real.Angle) w)
    (hz : z = o.rotation (β : Real.Angle) v)
    (hzw : z = o.rotation (δ : Real.Angle) w) : α + β = δ := by
  apply rotation_angle_unique o hw (by linarith) (by linarith)
    hd.1 (by linarith [Real.pi_pos])
  rw [hz, hv, o.rotation_rotation, ← Real.Angle.coe_add] at hzw
  simpa only [add_comm] using hzw

/-- A positive-length chord with unit incoming velocity and the carousel
laws admits a positive tangent–chord angle. Both endpoint rotations and
the exact sine and cosine formulas are conclusions. -/
theorem exists_positive_chord_angle (o : Orientation ℝ E (Fin 2))
    {e u v : E} {l : ℝ} (hl : 0 < l) (he : ‖e‖ = l) (hu : ‖u‖ = 1)
    (harea : 0 < o.areaForm u e) (horth : ⟪e, v - u⟫_ℝ = 0)
    (hmid : ∃ a : ℝ, u + v = a • e) :
    ∃ α : ℝ, 0 < α ∧ α < Real.pi ∧
      Real.cos α = ⟪u, l⁻¹ • e⟫_ℝ ∧ Real.sin α = o.areaForm u e / l ∧
      l⁻¹ • e = o.rotation (α : Real.Angle) u ∧
      v = o.rotation (α : Real.Angle) (l⁻¹ • e) := by
  have hw : ‖l⁻¹ • e‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hl), he,
      inv_mul_cancel₀ hl.ne']
  have ha : 0 < o.areaForm u (l⁻¹ • e) := by
    simpa only [map_smul, smul_eq_mul] using mul_pos (inv_pos.mpr hl) harea
  obtain ⟨α, ha0, hap, hcos, hsin, hrot⟩ := exists_positive_unit_angle o hu hw ha
  refine ⟨α, ha0, hap, hcos, ?_, hrot, ?_⟩
  · simpa only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm] using hsin
  · apply reflection_eq_rotation o hu hrot
    have hne : e ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at he
      exact hl.ne' he.symm
    rw [velocity_eq_reflection hne horth hmid, he, real_inner_smul_left, smul_smul]
    congr 2
    ring

end UlamFloating
