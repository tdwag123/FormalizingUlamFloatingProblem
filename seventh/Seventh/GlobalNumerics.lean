import Seventh.RationalTrig
import Seventh.FrequencyResidues

/-! Exact global enclosures. Generated candidates; all proofs are checked by Lean. -/

namespace UlamFloating.Seventh

theorem certificate_pi_bounds : ((6283185307 : ℝ) / 2000000000) ≤ Real.pi ∧ Real.pi ≤ ((3926990817 : ℝ) / 1250000000) := by
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

theorem certificate_angle_bounds : ((897597901 : ℝ) / 2000000000) ≤ Real.pi / 7 ∧ Real.pi / 7 ≤ ((2243994753 : ℝ) / 5000000000) := by
  constructor <;> linarith [Real.pi_gt_d20, Real.pi_lt_d20]

theorem certificate_sin_1 : ((10847093 : ℝ) / 25000000) ≤ Real.sin (1 * (Real.pi / 7)) ∧ Real.sin (1 * (Real.pi / 7)) ≤ ((347107 : ℝ) / 800000) := by
  have hL := sin_rational_enclosure (x := ((897597901 : ℝ) / 2000000000)) (L := ((10847093 : ℝ) / 25000000)) (U := ((347107 : ℝ) / 800000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hU := sin_rational_enclosure (x := ((2243994753 : ℝ) / 5000000000)) (L := ((10847093 : ℝ) / 25000000)) (U := ((347107 : ℝ) / 800000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hxL : ((897597901 : ℝ) / 2000000000) ≤ (1 * (Real.pi / 7)) := by linarith [certificate_angle_bounds.1]
  have hxU : (1 * (Real.pi / 7)) ≤ ((2243994753 : ℝ) / 5000000000) := by linarith [certificate_angle_bounds.2]

  have hmL := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ ((897597901 : ℝ) / 2000000000))
    (by linarith [Real.pi_pos] : (1 * (Real.pi / 7)) ≤ Real.pi / 2) hxL
  have hmU := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ (1 * (Real.pi / 7)))
    (by linarith [Real.pi_gt_d2] : ((2243994753 : ℝ) / 5000000000) ≤ Real.pi / 2) hxU
  exact ⟨hL.1.trans hmL, hmU.trans hU.2⟩

theorem certificate_cos_1 : ((18019377 : ℝ) / 20000000) ≤ Real.cos (1 * (Real.pi / 7)) ∧ Real.cos (1 * (Real.pi / 7)) ≤ ((11262111 : ℝ) / 12500000) := by
  have hL := cos_rational_enclosure (x := ((897597901 : ℝ) / 2000000000)) (L := ((18019377 : ℝ) / 20000000)) (U := ((11262111 : ℝ) / 12500000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hU := cos_rational_enclosure (x := ((2243994753 : ℝ) / 5000000000)) (L := ((18019377 : ℝ) / 20000000)) (U := ((11262111 : ℝ) / 12500000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hxL : ((897597901 : ℝ) / 2000000000) ≤ (1 * (Real.pi / 7)) := by linarith [certificate_angle_bounds.1]
  have hxU : (1 * (Real.pi / 7)) ≤ ((2243994753 : ℝ) / 5000000000) := by linarith [certificate_angle_bounds.2]

  have hmL := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : 0 ≤ ((897597901 : ℝ) / 2000000000))
    (by linarith [Real.pi_pos] : (1 * (Real.pi / 7)) ≤ Real.pi) hxL
  have hmU := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ (1 * (Real.pi / 7)))
    (by linarith [Real.pi_gt_d2] : ((2243994753 : ℝ) / 5000000000) ≤ Real.pi) hxU
  exact ⟨hU.1.trans hmU, hmL.trans hL.2⟩

theorem certificate_cot_1 : ((5191303 : ℝ) / 2500000) ≤ Real.cot (1 * (Real.pi / 7)) ∧ Real.cot (1 * (Real.pi / 7)) ≤ ((20765217 : ℝ) / 10000000) := by
  have hs := certificate_sin_1
  have hc := certificate_cos_1
  have hpos : 0 < Real.sin (1 * (Real.pi / 7)) := by linarith [hs.1]
  rw [Real.cot_eq_cos_div_sin]
  constructor
  · apply (le_div_iff₀ hpos).mpr
    nlinarith only [hs.2, hc.1]
  · apply (div_le_iff₀ hpos).mpr
    nlinarith only [hs.1, hc.2]

theorem certificate_sin_2 : ((78183147 : ℝ) / 100000000) ≤ Real.sin (2 * (Real.pi / 7)) ∧ Real.sin (2 * (Real.pi / 7)) ≤ ((1563663 : ℝ) / 2000000) := by
  have hL := sin_rational_enclosure (x := ((897597901 : ℝ) / 1000000000)) (L := ((78183147 : ℝ) / 100000000)) (U := ((1563663 : ℝ) / 2000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hU := sin_rational_enclosure (x := ((2243994753 : ℝ) / 2500000000)) (L := ((78183147 : ℝ) / 100000000)) (U := ((1563663 : ℝ) / 2000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hxL : ((897597901 : ℝ) / 1000000000) ≤ (2 * (Real.pi / 7)) := by linarith [certificate_angle_bounds.1]
  have hxU : (2 * (Real.pi / 7)) ≤ ((2243994753 : ℝ) / 2500000000) := by linarith [certificate_angle_bounds.2]

  have hmL := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ ((897597901 : ℝ) / 1000000000))
    (by linarith [Real.pi_pos] : (2 * (Real.pi / 7)) ≤ Real.pi / 2) hxL
  have hmU := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ (2 * (Real.pi / 7)))
    (by linarith [Real.pi_gt_d2] : ((2243994753 : ℝ) / 2500000000) ≤ Real.pi / 2) hxU
  exact ⟨hL.1.trans hmL, hmU.trans hU.2⟩

theorem certificate_cos_2 : ((62348979 : ℝ) / 100000000) ≤ Real.cos (2 * (Real.pi / 7)) ∧ Real.cos (2 * (Real.pi / 7)) ≤ ((31174491 : ℝ) / 50000000) := by
  have hL := cos_rational_enclosure (x := ((897597901 : ℝ) / 1000000000)) (L := ((62348979 : ℝ) / 100000000)) (U := ((31174491 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hU := cos_rational_enclosure (x := ((2243994753 : ℝ) / 2500000000)) (L := ((62348979 : ℝ) / 100000000)) (U := ((31174491 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hxL : ((897597901 : ℝ) / 1000000000) ≤ (2 * (Real.pi / 7)) := by linarith [certificate_angle_bounds.1]
  have hxU : (2 * (Real.pi / 7)) ≤ ((2243994753 : ℝ) / 2500000000) := by linarith [certificate_angle_bounds.2]

  have hmL := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : 0 ≤ ((897597901 : ℝ) / 1000000000))
    (by linarith [Real.pi_pos] : (2 * (Real.pi / 7)) ≤ Real.pi) hxL
  have hmU := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ (2 * (Real.pi / 7)))
    (by linarith [Real.pi_gt_d2] : ((2243994753 : ℝ) / 2500000000) ≤ Real.pi) hxU
  exact ⟨hU.1.trans hmU, hmL.trans hL.2⟩

theorem certificate_cot_2 : ((1993683 : ℝ) / 2500000) ≤ Real.cot (2 * (Real.pi / 7)) ∧ Real.cot (2 * (Real.pi / 7)) ≤ ((498421 : ℝ) / 625000) := by
  have hs := certificate_sin_2
  have hc := certificate_cos_2
  have hpos : 0 < Real.sin (2 * (Real.pi / 7)) := by linarith [hs.1]
  rw [Real.cot_eq_cos_div_sin]
  constructor
  · apply (le_div_iff₀ hpos).mpr
    nlinarith only [hs.2, hc.1]
  · apply (div_le_iff₀ hpos).mpr
    nlinarith only [hs.1, hc.2]

theorem certificate_sin_3 : ((9749279 : ℝ) / 10000000) ≤ Real.sin (3 * (Real.pi / 7)) ∧ Real.sin (3 * (Real.pi / 7)) ≤ ((97492793 : ℝ) / 100000000) := by
  have hL := sin_rational_enclosure (x := ((2692793703 : ℝ) / 2000000000)) (L := ((9749279 : ℝ) / 10000000)) (U := ((97492793 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hU := sin_rational_enclosure (x := ((6731984259 : ℝ) / 5000000000)) (L := ((9749279 : ℝ) / 10000000)) (U := ((97492793 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hxL : ((2692793703 : ℝ) / 2000000000) ≤ (3 * (Real.pi / 7)) := by linarith [certificate_angle_bounds.1]
  have hxU : (3 * (Real.pi / 7)) ≤ ((6731984259 : ℝ) / 5000000000) := by linarith [certificate_angle_bounds.2]

  have hmL := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ ((2692793703 : ℝ) / 2000000000))
    (by linarith [Real.pi_pos] : (3 * (Real.pi / 7)) ≤ Real.pi / 2) hxL
  have hmU := Real.sin_le_sin_of_le_of_le_pi_div_two
    (by linarith [Real.pi_pos] : -(Real.pi / 2) ≤ (3 * (Real.pi / 7)))
    (by linarith [Real.pi_gt_d2] : ((6731984259 : ℝ) / 5000000000) ≤ Real.pi / 2) hxU
  exact ⟨hL.1.trans hmL, hmU.trans hU.2⟩

theorem certificate_cos_3 : ((5563023 : ℝ) / 25000000) ≤ Real.cos (3 * (Real.pi / 7)) ∧ Real.cos (3 * (Real.pi / 7)) ≤ ((4450419 : ℝ) / 20000000) := by
  have hL := cos_rational_enclosure (x := ((2692793703 : ℝ) / 2000000000)) (L := ((5563023 : ℝ) / 25000000)) (U := ((4450419 : ℝ) / 20000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hU := cos_rational_enclosure (x := ((6731984259 : ℝ) / 5000000000)) (L := ((5563023 : ℝ) / 25000000)) (U := ((4450419 : ℝ) / 20000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hxL : ((2692793703 : ℝ) / 2000000000) ≤ (3 * (Real.pi / 7)) := by linarith [certificate_angle_bounds.1]
  have hxU : (3 * (Real.pi / 7)) ≤ ((6731984259 : ℝ) / 5000000000) := by linarith [certificate_angle_bounds.2]

  have hmL := Real.cos_le_cos_of_nonneg_of_le_pi
    (by norm_num : 0 ≤ ((2692793703 : ℝ) / 2000000000))
    (by linarith [Real.pi_pos] : (3 * (Real.pi / 7)) ≤ Real.pi) hxL
  have hmU := Real.cos_le_cos_of_nonneg_of_le_pi
    (by positivity : 0 ≤ (3 * (Real.pi / 7)))
    (by linarith [Real.pi_gt_d2] : ((6731984259 : ℝ) / 5000000000) ≤ Real.pi) hxU
  exact ⟨hU.1.trans hmU, hmL.trans hL.2⟩

theorem certificate_cot_3 : ((2282433 : ℝ) / 10000000) ≤ Real.cot (3 * (Real.pi / 7)) ∧ Real.cot (3 * (Real.pi / 7)) ≤ ((570609 : ℝ) / 2500000) := by
  have hs := certificate_sin_3
  have hc := certificate_cos_3
  have hpos : 0 < Real.sin (3 * (Real.pi / 7)) := by linarith [hs.1]
  rw [Real.cot_eq_cos_div_sin]
  constructor
  · apply (le_div_iff₀ hpos).mpr
    nlinarith only [hs.2, hc.1]
  · apply (div_le_iff₀ hpos).mpr
    nlinarith only [hs.1, hc.2]

end UlamFloating.Seventh
