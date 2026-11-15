import Seventh.Cells0

/-! Rational cell certificates, verified by Lean. -/

namespace UlamFloating.Seventh

set_option maxHeartbeats 1000000 in
theorem cell_4210 : CellCertificate ((421 : ℝ) / 1000) ((4211 : ℝ) / 10000) ((70633 : ℝ) / 200000) ((182881 : ℝ) / 200000) ((211237 : ℝ) / 250000) ((75381 : ℝ) / 1000000) ((23191 : ℝ) / 200000) ((37251 : ℝ) / 500000) ((44529 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((70633 : ℝ) / 200000)) (L := ((17293459 : ℝ) / 50000000)) (U := ((34586921 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((182881 : ℝ) / 200000)) (L := ((79219961 : ℝ) / 100000000)) (U := ((19804991 : ℝ) / 25000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((70633 : ℝ) / 200000)) (L := ((5864267 : ℝ) / 6250000)) (U := ((3753131 : ℝ) / 4000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((465413 : ℝ) / 400000)) (L := ((19804921 : ℝ) / 50000000)) (U := ((7921969 : ℝ) / 20000000))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((70633 : ℝ) / 200000))
      (sub_le_sub_left hA.1 ((182881 : ℝ) / 200000)) (by linarith only [hA.2]) (by norm_num)
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
theorem cell_4211 : CellCertificate ((4211 : ℝ) / 10000) ((1053 : ℝ) / 2500) ((352521 : ℝ) / 1000000) ((915953 : ℝ) / 1000000) ((105593 : ℝ) / 125000) ((75707 : ℝ) / 1000000) ((116387 : ℝ) / 1000000) ((74053 : ℝ) / 1000000) ((22489 : ℝ) / 500000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((352521 : ℝ) / 1000000)) (L := ((17263243 : ℝ) / 50000000)) (U := ((34526489 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((915953 : ℝ) / 1000000)) (L := ((39657167 : ℝ) / 50000000)) (U := ((79314337 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((352521 : ℝ) / 1000000)) (L := ((93850527 : ℝ) / 100000000)) (U := ((9385053 : ℝ) / 10000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2326037 : ℝ) / 2000000)) (L := ((39657033 : ℝ) / 100000000)) (U := ((9914259 : ℝ) / 25000000))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((352521 : ℝ) / 1000000))
      (sub_le_sub_left hA.1 ((915953 : ℝ) / 1000000)) (by linarith only [hA.2]) (by norm_num)
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
theorem cell_4212 : CellCertificate ((1053 : ℝ) / 2500) ((4213 : ℝ) / 10000) ((563 : ℝ) / 1600) ((917507 : ℝ) / 1000000) ((422269 : ℝ) / 500000) ((76033 : ℝ) / 1000000) ((116821 : ℝ) / 1000000) ((73603 : ℝ) / 1000000) ((45431 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((563 : ℝ) / 1600)) (L := ((34465851 : ℝ) / 100000000)) (U := ((17232927 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((917507 : ℝ) / 1000000)) (L := ((39704441 : ℝ) / 50000000)) (U := ((15881777 : ℝ) / 20000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((563 : ℝ) / 1600)) (L := ((93872811 : ℝ) / 100000000)) (U := ((46936407 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2325007 : ℝ) / 2000000)) (L := ((7940861 : ℝ) / 20000000)) (U := ((9926077 : ℝ) / 25000000))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((563 : ℝ) / 1600))
      (sub_le_sub_left hA.1 ((917507 : ℝ) / 1000000)) (by linarith only [hA.2]) (by norm_num)
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
theorem cell_4213 : CellCertificate ((4213 : ℝ) / 10000) ((2107 : ℝ) / 5000) ((87807 : ℝ) / 250000) ((114883 : ℝ) / 125000) ((844331 : ℝ) / 1000000) ((76361 : ℝ) / 1000000) ((117257 : ℝ) / 1000000) ((1143 : ℝ) / 15625) ((22943 : ℝ) / 500000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((87807 : ℝ) / 250000)) (L := ((8601277 : ℝ) / 25000000)) (U := ((34405111 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((114883 : ℝ) / 125000)) (L := ((79503421 : ℝ) / 100000000)) (U := ((1242241 : ℝ) / 1562500))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((87807 : ℝ) / 250000)) (L := ((93895091 : ℝ) / 100000000)) (U := ((46947547 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((290497 : ℝ) / 250000)) (L := ((9937903 : ℝ) / 25000000)) (U := ((7950323 : ℝ) / 20000000))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((87807 : ℝ) / 250000))
      (sub_le_sub_left hA.1 ((114883 : ℝ) / 125000)) (by linarith only [hA.2]) (by norm_num)
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
theorem cell_4214 : CellCertificate ((2107 : ℝ) / 5000) ((843 : ℝ) / 2000) ((17529 : ℝ) / 50000) ((1473 : ℝ) / 1600) ((211031 : ℝ) / 250000) ((76689 : ℝ) / 1000000) ((29423 : ℝ) / 250000) ((72699 : ℝ) / 1000000) ((5793 : ℝ) / 125000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((17529 : ℝ) / 50000)) (L := ((34344257 : ℝ) / 100000000)) (U := ((1717213 : ℝ) / 5000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1473 : ℝ) / 1600)) (L := ((79598009 : ℝ) / 100000000)) (U := ((19899503 : ℝ) / 25000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((17529 : ℝ) / 50000)) (L := ((46958683 : ℝ) / 50000000)) (U := ((93917369 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((464589 : ℝ) / 400000)) (L := ((39798909 : ℝ) / 100000000)) (U := ((310929 : ℝ) / 781250))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((17529 : ℝ) / 50000))
      (sub_le_sub_left hA.1 ((1473 : ℝ) / 1600)) (by linarith only [hA.2]) (by norm_num)
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
theorem cell_4215 : CellCertificate ((843 : ℝ) / 2000) ((527 : ℝ) / 1250) ((34993 : ℝ) / 100000) ((57637 : ℝ) / 62500) ((168783 : ℝ) / 200000) ((3851 : ℝ) / 50000) ((118129 : ℝ) / 1000000) ((14449 : ℝ) / 200000) ((9361 : ℝ) / 200000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((34993 : ℝ) / 100000)) (L := ((8570801 : ℝ) / 25000000)) (U := ((34283207 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((57637 : ℝ) / 62500)) (L := ((15938553 : ℝ) / 20000000)) (U := ((2490399 : ℝ) / 3125000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((34993 : ℝ) / 100000)) (L := ((9393967 : ℝ) / 10000000)) (U := ((93939673 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((290239 : ℝ) / 250000)) (L := ((39846287 : ℝ) / 100000000)) (U := ((3984629 : ℝ) / 10000000))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((34993 : ℝ) / 100000))
      (sub_le_sub_left hA.1 ((57637 : ℝ) / 62500)) (by linarith only [hA.2]) (by norm_num)
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
theorem cell_4216 : CellCertificate ((527 : ℝ) / 1250) ((4217 : ℝ) / 10000) ((2183 : ℝ) / 6250) ((11547 : ℝ) / 12500) ((421853 : ℝ) / 500000) ((1547 : ℝ) / 20000) ((59283 : ℝ) / 500000) ((7179 : ℝ) / 100000) ((47269 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((2183 : ℝ) / 6250)) (L := ((4277767 : ℝ) / 12500000)) (U := ((34222139 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((11547 : ℝ) / 12500)) (L := ((39893693 : ℝ) / 50000000)) (U := ((79787389 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((2183 : ℝ) / 6250)) (L := ((46980967 : ℝ) / 50000000)) (U := ((93961937 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((29011 : ℝ) / 25000)) (L := ((4986701 : ℝ) / 12500000)) (U := ((39893611 : ℝ) / 100000000))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((2183 : ℝ) / 6250))
      (sub_le_sub_left hA.1 ((11547 : ℝ) / 12500)) (by linarith only [hA.2]) (by norm_num)
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
theorem cell_4217 : CellCertificate ((4217 : ℝ) / 10000) ((2109 : ℝ) / 5000) ((87157 : ℝ) / 250000) ((185067 : ℝ) / 200000) ((105437 : ℝ) / 125000) ((38841 : ℝ) / 500000) ((29751 : ℝ) / 250000) ((71333 : ℝ) / 1000000) ((47737 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((87157 : ℝ) / 250000)) (L := ((6832173 : ℝ) / 20000000)) (U := ((8540217 : ℝ) / 25000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((185067 : ℝ) / 200000)) (L := ((9985279 : ℝ) / 12500000)) (U := ((15976447 : ℝ) / 20000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((87157 : ℝ) / 250000)) (L := ((93984227 : ℝ) / 100000000)) (U := ((9398423 : ℝ) / 10000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2319847 : ℝ) / 2000000)) (L := ((7988193 : ℝ) / 20000000)) (U := ((4992621 : ℝ) / 12500000))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((87157 : ℝ) / 250000))
      (sub_le_sub_left hA.1 ((185067 : ℝ) / 200000)) (by linarith only [hA.2]) (by norm_num)
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
theorem cell_4218 : CellCertificate ((2109 : ℝ) / 5000) ((4219 : ℝ) / 10000) ((13919 : ℝ) / 40000) ((14483 : ℝ) / 15625) ((168657 : ℝ) / 200000) ((15603 : ℝ) / 200000) ((29861 : ℝ) / 250000) ((567 : ℝ) / 8000) ((48207 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((13919 : ℝ) / 40000)) (L := ((17049743 : ℝ) / 50000000)) (U := ((34099489 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((14483 : ℝ) / 15625)) (L := ((79977 : ℝ) / 100000)) (U := ((79977003 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((13919 : ℝ) / 40000)) (L := ((47003257 : ℝ) / 50000000)) (U := ((94006517 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((579703 : ℝ) / 500000)) (L := ((19994201 : ℝ) / 50000000)) (U := ((7997681 : ℝ) / 20000000))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((13919 : ℝ) / 40000))
      (sub_le_sub_left hA.1 ((14483 : ℝ) / 15625)) (by linarith only [hA.2]) (by norm_num)
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
theorem cell_4219 : CellCertificate ((4219 : ℝ) / 10000) ((211 : ℝ) / 500) ((347321 : ℝ) / 1000000) ((464247 : ℝ) / 500000) ((13173 : ℝ) / 15625) ((78349 : ℝ) / 1000000) ((23977 : ℝ) / 200000) ((14083 : ℝ) / 200000) ((1217 : ℝ) / 25000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((347321 : ℝ) / 1000000)) (L := ((34037999 : ℝ) / 100000000)) (U := ((17019001 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((464247 : ℝ) / 500000)) (L := ((20017967 : ℝ) / 25000000)) (U := ((80071871 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((347321 : ℝ) / 1000000)) (L := ((18805759 : ℝ) / 20000000)) (U := ((47014399 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((1158889 : ℝ) / 1000000)) (L := ((5004473 : ℝ) / 12500000)) (U := ((40035787 : ℝ) / 100000000))
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
    have hp := mul_le_mul (sub_le_sub_right hA.2 ((347321 : ℝ) / 1000000))
      (sub_le_sub_left hA.1 ((464247 : ℝ) / 500000)) (by linarith only [hA.2]) (by norm_num)
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
