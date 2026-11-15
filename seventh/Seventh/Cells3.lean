import Seventh.Cells2

/-! Rational cell certificates, verified by Lean. -/

namespace UlamFloating.Seventh

set_option maxHeartbeats 1000000 in
theorem cell_4230 : CellCertificate ((423 : ℝ) / 1000) ((4231 : ℝ) / 10000) ((340047 : ℝ) / 1000000) ((473081 : ℝ) / 500000) ((33627 : ℝ) / 40000) ((8209 : ℝ) / 100000) ((124793 : ℝ) / 1000000) ((13053 : ℝ) / 200000) ((54091 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((340047 : ℝ) / 1000000)) (L := ((33353139 : ℝ) / 100000000)) (U := ((16676571 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((473081 : ℝ) / 500000)) (L := ((811177 : ℝ) / 1000000)) (U := ((81117703 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((340047 : ℝ) / 1000000)) (L := ((47136949 : ℝ) / 50000000)) (U := ((94273901 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((46127 : ℝ) / 40000)) (L := ((8111747 : ℝ) / 20000000)) (U := ((20279369 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((340047 : ℝ) / 1000000))
      (sub_le_sub_left hA.1 ((473081 : ℝ) / 500000)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

set_option maxHeartbeats 1000000 in
theorem cell_4231 : CellCertificate ((4231 : ℝ) / 10000) ((529 : ℝ) / 1250) ((339379 : ℝ) / 1000000) ((59237 : ℝ) / 62500) ((210113 : ℝ) / 250000) ((20609 : ℝ) / 250000) ((31311 : ℝ) / 250000) ((16197 : ℝ) / 250000) ((54601 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((339379 : ℝ) / 1000000)) (L := ((8322539 : ℝ) / 25000000)) (U := ((33290159 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((59237 : ℝ) / 62500)) (L := ((16242583 : ℝ) / 20000000)) (U := ((40606459 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((339379 : ℝ) / 1000000)) (L := ((23574039 : ℝ) / 25000000)) (U := ((94296159 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((576327 : ℝ) / 500000)) (L := ((40606351 : ℝ) / 100000000)) (U := ((20303177 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((339379 : ℝ) / 1000000))
      (sub_le_sub_left hA.1 ((59237 : ℝ) / 62500)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

set_option maxHeartbeats 1000000 in
theorem cell_4232 : CellCertificate ((529 : ℝ) / 1250) ((4233 : ℝ) / 10000) ((338709 : ℝ) / 1000000) ((237357 : ℝ) / 250000) ((840227 : ℝ) / 1000000) ((2587 : ℝ) / 31250) ((125697 : ℝ) / 1000000) ((64309 : ℝ) / 1000000) ((13779 : ℝ) / 250000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((338709 : ℝ) / 1000000)) (L := ((3322697 : ℝ) / 10000000)) (U := ((33226973 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((237357 : ℝ) / 250000)) (L := ((81308263 : ℝ) / 100000000)) (U := ((40654133 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((338709 : ℝ) / 1000000)) (L := ((2357961 : ℝ) / 2500000)) (U := ((94318443 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((288033 : ℝ) / 250000)) (L := ((40654049 : ℝ) / 100000000)) (U := ((10163513 : ℝ) / 25000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((338709 : ℝ) / 1000000))
      (sub_le_sub_left hA.1 ((237357 : ℝ) / 250000)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

set_option maxHeartbeats 1000000 in
theorem cell_4233 : CellCertificate ((4233 : ℝ) / 10000) ((2117 : ℝ) / 5000) ((338037 : ℝ) / 1000000) ((951071 : ℝ) / 1000000) ((840001 : ℝ) / 1000000) ((83133 : ℝ) / 1000000) ((126151 : ℝ) / 1000000) ((63829 : ℝ) / 1000000) ((27817 : ℝ) / 500000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((338037 : ℝ) / 1000000)) (L := ((33163581 : ℝ) / 100000000)) (U := ((518181 : ℝ) / 1562500))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((951071 : ℝ) / 1000000)) (L := ((81403801 : ℝ) / 100000000)) (U := ((20350951 : ℝ) / 25000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((338037 : ℝ) / 1000000)) (L := ((94340747 : ℝ) / 100000000)) (U := ((377363 : ℝ) / 400000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2303219 : ℝ) / 2000000)) (L := ((2035089 : ℝ) / 5000000)) (U := ((40701783 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((338037 : ℝ) / 1000000))
      (sub_le_sub_left hA.1 ((951071 : ℝ) / 1000000)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

set_option maxHeartbeats 1000000 in
theorem cell_4234 : CellCertificate ((2117 : ℝ) / 5000) ((847 : ℝ) / 2000) ((67473 : ℝ) / 200000) ((190543 : ℝ) / 200000) ((419887 : ℝ) / 500000) ((83483 : ℝ) / 1000000) ((126607 : ℝ) / 1000000) ((63347 : ℝ) / 1000000) ((11231 : ℝ) / 200000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((67473 : ℝ) / 200000)) (L := ((2068761 : ℝ) / 6250000)) (U := ((33100179 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((190543 : ℝ) / 200000)) (L := ((10187397 : ℝ) / 12500000)) (U := ((81499179 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((67473 : ℝ) / 200000)) (L := ((23590753 : ℝ) / 25000000)) (U := ((18872603 : ℝ) / 20000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((92087 : ℝ) / 80000)) (L := ((8149891 : ℝ) / 20000000)) (U := ((20374729 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((67473 : ℝ) / 200000))
      (sub_le_sub_left hA.1 ((190543 : ℝ) / 200000)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

set_option maxHeartbeats 1000000 in
theorem cell_4235 : CellCertificate ((847 : ℝ) / 2000) ((1059 : ℝ) / 2500) ((336691 : ℝ) / 1000000) ((190873 : ℝ) / 200000) ((419773 : ℝ) / 500000) ((41917 : ℝ) / 500000) ((127063 : ℝ) / 1000000) ((3929 : ℝ) / 62500) ((56679 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((336691 : ℝ) / 1000000)) (L := ((4129571 : ℝ) / 12500000)) (U := ((33036571 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((190873 : ℝ) / 200000)) (L := ((40797339 : ℝ) / 50000000)) (U := ((81594681 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((336691 : ℝ) / 1000000)) (L := ((943853 : ℝ) / 1000000)) (U := ((94385303 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2301129 : ℝ) / 2000000)) (L := ((40797211 : ℝ) / 100000000)) (U := ((20398607 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((336691 : ℝ) / 1000000))
      (sub_le_sub_left hA.1 ((190873 : ℝ) / 200000)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

set_option maxHeartbeats 1000000 in
theorem cell_4236 : CellCertificate ((1059 : ℝ) / 2500) ((4237 : ℝ) / 10000) ((21001 : ℝ) / 62500) ((956019 : ℝ) / 1000000) ((839317 : ℝ) / 1000000) ((42093 : ℝ) / 500000) ((797 : ℝ) / 6250) ((62379 : ℝ) / 1000000) ((57207 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((21001 : ℝ) / 62500)) (L := ((32972851 : ℝ) / 100000000)) (U := ((16486427 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((956019 : ℝ) / 1000000)) (L := ((20422547 : ℝ) / 25000000)) (U := ((81690191 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((21001 : ℝ) / 62500)) (L := ((47203789 : ℝ) / 50000000)) (U := ((94407581 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2300083 : ℝ) / 2000000)) (L := ((8168991 : ℝ) / 20000000)) (U := ((20422479 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((21001 : ℝ) / 62500))
      (sub_le_sub_left hA.1 ((956019 : ℝ) / 1000000)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

set_option maxHeartbeats 1000000 in
theorem cell_4237 : CellCertificate ((4237 : ℝ) / 10000) ((2119 : ℝ) / 5000) ((16767 : ℝ) / 50000) ((239419 : ℝ) / 250000) ((839087 : ℝ) / 1000000) ((84539 : ℝ) / 1000000) ((63989 : ℝ) / 500000) ((15473 : ℝ) / 250000) ((28869 : ℝ) / 500000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((16767 : ℝ) / 50000)) (L := ((1028407 : ℝ) / 3125000)) (U := ((32909027 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((239419 : ℝ) / 250000)) (L := ((5111603 : ℝ) / 6250000)) (U := ((81785651 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((16767 : ℝ) / 50000)) (L := ((47214923 : ℝ) / 50000000)) (U := ((94429849 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((574759 : ℝ) / 500000)) (L := ((40892733 : ℝ) / 100000000)) (U := ((638949 : ℝ) / 1562500))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((16767 : ℝ) / 50000))
      (sub_le_sub_left hA.1 ((239419 : ℝ) / 250000)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

set_option maxHeartbeats 1000000 in
theorem cell_4238 : CellCertificate ((2119 : ℝ) / 5000) ((4239 : ℝ) / 10000) ((167331 : ℝ) / 500000) ((47967 : ℝ) / 50000) ((104857 : ℝ) / 125000) ((42447 : ℝ) / 500000) ((64219 : ℝ) / 500000) ((15351 : ℝ) / 250000) ((58273 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((167331 : ℝ) / 500000)) (L := ((32844993 : ℝ) / 100000000)) (U := ((8211249 : ℝ) / 25000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((47967 : ℝ) / 50000)) (L := ((16376257 : ℝ) / 20000000)) (U := ((10235161 : ℝ) / 12500000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((167331 : ℝ) / 500000)) (L := ((11806517 : ℝ) / 12500000)) (U := ((94452139 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((574497 : ℝ) / 500000)) (L := ((20470273 : ℝ) / 50000000)) (U := ((40940549 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((167331 : ℝ) / 500000))
      (sub_le_sub_left hA.1 ((47967 : ℝ) / 50000)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

set_option maxHeartbeats 1000000 in
theorem cell_4239 : CellCertificate ((4239 : ℝ) / 10000) ((53 : ℝ) / 125) ((333983 : ℝ) / 1000000) ((60063 : ℝ) / 62500) ((838623 : ℝ) / 1000000) ((341 : ℝ) / 4000) ((128899 : ℝ) / 1000000) ((30457 : ℝ) / 500000) ((58811 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((333983 : ℝ) / 1000000)) (L := ((8195213 : ℝ) / 25000000)) (U := ((6556171 : ℝ) / 20000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((60063 : ℝ) / 62500)) (L := ((3279077 : ℝ) / 4000000)) (U := ((2561779 : ℝ) / 3125000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((333983 : ℝ) / 1000000)) (L := ((5904651 : ℝ) / 6250000)) (U := ((94474419 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((114847 : ℝ) / 100000)) (L := ((10247087 : ℝ) / 25000000)) (U := ((40988351 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  refine {
    frequency_pos := by norm_num
    lower_pos := by norm_num
    lower_lt_mean := by linarith only [hA.1]
    mean_lt_upper := by linarith only [hA.2]
    upper_le := by norm_num
    width_nonneg := by norm_num
    gap_pos := by norm_num
    variance_nonneg := by norm_num
    projection := ?_
    jensen := ?_
    angle_upper := ?_
    variance := ?_
    approximation_lower := ?_
    approximation_upper := ?_
    gap_center := by norm_num
    gap_two := ?_
    gap_three := ?_
    gap_eight := ?_
    gap_nine := ?_
    gap_ten := ?_
    contraction := ?_ }
  · have hp := mul_le_mul hA.1 hCB.1 (by norm_num) (by positivity : 0 ≤ Real.pi / 7)
    exact lt_of_lt_of_le (by norm_num) hp
  · nlinarith only [hS.2, hSB.1]
  · left
    norm_num at hCN ⊢
    nlinarith only [hCN.2, hSU.1]
  · right
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((333983 : ℝ) / 1000000))
      (sub_le_sub_left hA.1 ((60063 : ℝ) / 62500)) (by linarith only [hA.2]) (by norm_num)
    exact hp.trans (by norm_num)
  · nlinarith only [hA.1, hS.2, hSU.1]
  · nlinarith only [hA.1, hS.2, hSB.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (2 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (3 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.2]
  · have ht := certificate_cot_1
    unfold seventhMultiplier
    rw [cot_frequency_residue (8 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_2
    unfold seventhMultiplier
    rw [cot_frequency_residue (9 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · have ht := certificate_cot_3
    unfold seventhMultiplier
    rw [cot_frequency_residue (10 : ℤ)]
    norm_num at ht ⊢
    nlinarith only [ht.1]
  · apply certificate_contraction_of_rational (by norm_num) (by norm_num)
    norm_num

end UlamFloating.Seventh
