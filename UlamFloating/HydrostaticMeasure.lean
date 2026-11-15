import UlamFloating.Geometry
import UlamFloating.BoundaryTangents
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Area, first moments, and hydrostatic torque

These lemmas concern the actual restricted planar volume measure used in
`IsEquilibriumCut`. No boundary-integral formula or constant-chord assumption
is included in the physical definitions.
-/

noncomputable section

namespace UlamFloating

open MeasureTheory Set
open scoped InnerProductSpace

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The first moment of planar area measure about the origin. -/
def laminaFirstMoment (K : Set Plane) : Plane := ∫ x in K, x

/-- A genuine waterline has planar measure zero. -/
theorem volume_waterline_eq_zero {u : Plane} (hu : u ≠ 0) (a : ℝ) :
    volume {x : Plane | ⟪u, x⟫_ℝ = a} = 0 := by
  let H : AffineSubspace ℝ Plane :=
    { carrier := {x | ⟪u, x⟫_ℝ = a}
      smul_vsub_vadd_mem := by
        intro r x y z hx hy hz
        change ⟪u, r • (x - y) + z⟫_ℝ = a
        simp only [inner_add_right, real_inner_smul_right, inner_sub_right]
        change ⟪u, x⟫_ℝ = a at hx
        change ⟪u, y⟫_ℝ = a at hy
        change ⟪u, z⟫_ℝ = a at hz
        rw [hx, hy, hz]
        ring }
  have hproper : H ≠ ⊤ := by
    intro htop
    have hzero : (0 : Plane) ∈ H := by rw [htop]; trivial
    have hone : u ∈ H := by rw [htop]; trivial
    change ⟪u, (0 : Plane)⟫_ℝ = a at hzero
    change ⟪u, u⟫_ℝ = a at hone
    simp only [inner_zero_right] at hzero
    exact hu ((inner_self_eq_zero).mp (hone.trans hzero.symm))
  exact Measure.addHaar_affineSubspace volume H hproper

theorem isCompact_waterlineCap {K : Set Plane} (hK : IsCompact K)
    (u : Plane) (a : ℝ) : IsCompact (waterlineCap K u a) :=
  hK.inter_right (isClosed_le (continuous_const.inner continuous_id) continuous_const)

theorem integrableOn_laminaFirstMoment {K : Set Plane} (hK : IsCompact K) :
    IntegrableOn (fun x : Plane => x) K :=
  continuous_id.continuousOn.integrableOn_compact hK

theorem waterlineCap_union_neg (K : Set Plane) (u : Plane) (a : ℝ) :
    waterlineCap K u a ∪ waterlineCap K (-u) (-a) = K := by
  ext x
  simp only [waterlineCap, mem_union, mem_inter_iff, mem_setOf_eq, inner_neg_left,
    neg_le_neg_iff]
  constructor
  · rintro (h | h) <;> exact h.1
  · intro hx
    rcases le_total ⟪u, x⟫_ℝ a with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩

theorem waterlineCap_aedisjoint_neg (K : Set Plane) {u : Plane} (hu : u ≠ 0) (a : ℝ) :
    AEDisjoint volume (waterlineCap K u a) (waterlineCap K (-u) (-a)) := by
  apply measure_mono_null _ (volume_waterline_eq_zero hu a)
  intro x hx
  exact le_antisymm hx.1.2 (by simpa using hx.2.2)

/-- Complementary cap areas add to the area of the original body. -/
theorem planarArea_waterlineCap_add_neg {K : Set Plane} (hK : IsCompact K)
    {u : Plane} (hu : u ≠ 0) (a : ℝ) :
    planarArea (waterlineCap K u a) + planarArea (waterlineCap K (-u) (-a)) =
      planarArea K := by
  have hC := isCompact_waterlineCap hK u a
  have hD := isCompact_waterlineCap hK (-u) (-a)
  have he := measure_union₀ hD.measurableSet.nullMeasurableSet
    (waterlineCap_aedisjoint_neg K hu a)
  rw [waterlineCap_union_neg] at he
  unfold planarArea
  rw [he, ENNReal.toReal_add hC.measure_ne_top hD.measure_ne_top]

/-- Complementary cap first moments add to the body's first moment. -/
theorem laminaFirstMoment_waterlineCap_add_neg {K : Set Plane} (hK : IsCompact K)
    {u : Plane} (hu : u ≠ 0) (a : ℝ) :
    laminaFirstMoment (waterlineCap K u a) +
      laminaFirstMoment (waterlineCap K (-u) (-a)) = laminaFirstMoment K := by
  have hC := isCompact_waterlineCap hK u a
  have hD := isCompact_waterlineCap hK (-u) (-a)
  have he := integral_union_ae (waterlineCap_aedisjoint_neg K hu a)
    hD.measurableSet.nullMeasurableSet
    (integrableOn_laminaFirstMoment hC) (integrableOn_laminaFirstMoment hD)
  rw [waterlineCap_union_neg] at he
  exact he.symm

theorem planarArea_pos {K : Set Plane} (hK : IsCompact K)
    (hi : (interior K).Nonempty) : 0 < planarArea K :=
  ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume hi).ne' hK.measure_ne_top

theorem planarArea_mono {K L : Set Plane} (hL : IsCompact L) (hKL : K ⊆ L) :
    planarArea K ≤ planarArea L :=
  ENNReal.toReal_mono hL.measure_ne_top (measure_mono hKL)

theorem area_smul_laminaCentroid {K : Set Plane} (hA : planarArea K ≠ 0) :
    planarArea K • laminaCentroid K = laminaFirstMoment K := by
  simp [laminaCentroid, laminaFirstMoment, smul_smul, hA]

/-- Zero torque can be expressed without dividing by the cap area. -/
theorem centroid_normal_iff_firstMoment {K C : Set Plane} {ρ : ℝ} {u : Plane}
    (hC : planarArea C ≠ 0) (harea : planarArea C = ρ * planarArea K) :
    (∃ b : ℝ, laminaCentroid C - laminaCentroid K = b • u) ↔
      ∃ b : ℝ, laminaFirstMoment C - ρ • laminaFirstMoment K = b • u := by
  have hK : planarArea K ≠ 0 := by
    intro hz
    exact hC (by rw [harea, hz, mul_zero])
  have he : planarArea C • (laminaCentroid C - laminaCentroid K) =
      laminaFirstMoment C - ρ • laminaFirstMoment K := by
    rw [smul_sub, area_smul_laminaCentroid hC]
    congr 1
    rw [harea, mul_smul, area_smul_laminaCentroid hK]
  constructor
  · rintro ⟨b, hb⟩
    exact ⟨planarArea C * b, by rw [← he, hb, smul_smul]⟩
  · rintro ⟨b, hb⟩
    refine ⟨(planarArea C)⁻¹ * b, ?_⟩
    have h := congrArg (fun x => (planarArea C)⁻¹ • x) (he.trans hb)
    simpa [smul_smul, hC] using h

/-- In the plane, a vector is normal to a line iff its tangential component vanishes. -/
theorem exists_smul_iff_inner_rightAngleRotation_eq_zero
    (o : Orientation ℝ Plane (Fin 2)) {u v : Plane} (hu : ‖u‖ = 1) :
    (∃ b : ℝ, v = b • u) ↔ ⟪o.rightAngleRotation u, v⟫_ℝ = 0 := by
  constructor
  · rintro ⟨b, rfl⟩
    simp
  · intro h
    refine ⟨⟪u, v⟫_ℝ, ?_⟩
    have he := norm_sq_smul_eq_inner_add_area o u v
    rw [hu, one_pow, one_smul, ← o.inner_rightAngleRotation_left, h,
      zero_smul, add_zero] at he
    exact he

/-- Equilibrium is exactly the area constraint and vanishing tangential first moment. -/
theorem isEquilibriumCut_iff_firstMoment (o : Orientation ℝ Plane (Fin 2))
    {K : Set Plane} (hK : IsCompact K) (hi : (interior K).Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ) (u : Plane) (a : ℝ) :
    IsEquilibriumCut K ρ u a ↔
      ‖u‖ = 1 ∧ planarArea (waterlineCap K u a) = ρ * planarArea K ∧
        ⟪o.rightAngleRotation u,
          laminaFirstMoment (waterlineCap K u a) - ρ • laminaFirstMoment K⟫_ℝ = 0 := by
  have hpos := planarArea_pos hK hi
  constructor
  · rintro ⟨hu, ha, ht⟩
    have hc : planarArea (waterlineCap K u a) ≠ 0 := by rw [ha]; positivity
    exact ⟨hu, ha, (exists_smul_iff_inner_rightAngleRotation_eq_zero o hu).mp
      ((centroid_normal_iff_firstMoment hc ha).mp ht)⟩
  · rintro ⟨hu, ha, ht⟩
    have hc : planarArea (waterlineCap K u a) ≠ 0 := by rw [ha]; positivity
    exact ⟨hu, ha, (centroid_normal_iff_firstMoment hc ha).mpr
      ((exists_smul_iff_inner_rightAngleRotation_eq_zero o hu).mpr ht)⟩

/-- Reversing the waterline exchanges submerged and emerged densities. -/
theorem IsEquilibriumCut.complement {K : Set Plane} (hK : IsCompact K)
    (hi : (interior K).Nonempty) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1)
    {u : Plane} {a : ℝ} (he : IsEquilibriumCut K ρ u a) :
    IsEquilibriumCut K (1 - ρ) (-u) (-a) := by
  have hu : u ≠ 0 := by intro h; simpa [h] using he.1
  have hA := planarArea_pos hK hi
  have hsum := planarArea_waterlineCap_add_neg hK hu a
  have hD : planarArea (waterlineCap K (-u) (-a)) = (1 - ρ) * planarArea K := by
    rw [he.2.1] at hsum
    linarith
  have hCpos : 0 < planarArea (waterlineCap K u a) := by rw [he.2.1]; positivity
  have hDpos : 0 < planarArea (waterlineCap K (-u) (-a)) := by
    rw [hD]
    exact mul_pos (sub_pos.mpr hρ') hA
  refine ⟨by simpa using he.1, hD, ?_⟩
  apply (centroid_normal_iff_firstMoment hDpos.ne' hD).mpr
  obtain ⟨b, hb⟩ := (centroid_normal_iff_firstMoment hCpos.ne' he.2.1).mp he.2.2
  refine ⟨b, ?_⟩
  have hm := laminaFirstMoment_waterlineCap_add_neg hK hu a
  have hm' : laminaFirstMoment (waterlineCap K (-u) (-a)) =
      laminaFirstMoment K - laminaFirstMoment (waterlineCap K u a) := by
    rw [← hm]; abel
  rw [hm', sub_smul, one_smul, smul_neg]
  rw [show laminaFirstMoment K - laminaFirstMoment (waterlineCap K u a) -
      (laminaFirstMoment K - ρ • laminaFirstMoment K) =
      -(laminaFirstMoment (waterlineCap K u a) - ρ • laminaFirstMoment K) by abel, hb]

end UlamFloating
