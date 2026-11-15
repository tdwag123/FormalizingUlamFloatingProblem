import Seventh.Cells5

/-! Rational cell certificates, verified by Lean. -/

namespace UlamFloating.Seventh

set_option maxHeartbeats 1000000 in
theorem cell_4260 : CellCertificate ((213 : ℝ) / 500) ((4261 : ℝ) / 10000) ((159701 : ℝ) / 500000) ((498583 : ℝ) / 500000) ((833483 : ℝ) / 1000000) ((93009 : ℝ) / 1000000) ((8677 : ℝ) / 62500) ((50217 : ℝ) / 1000000) ((25109 : ℝ) / 500000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((159701 : ℝ) / 500000)) (L := ((6279977 : ℝ) / 20000000)) (U := ((1962493 : ℝ) / 6250000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((498583 : ℝ) / 500000)) (L := ((41996819 : ℝ) / 50000000)) (U := ((83993641 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((159701 : ℝ) / 500000)) (L := ((47471167 : ℝ) / 50000000)) (U := ((94942337 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((1137387 : ℝ) / 1000000)) (L := ((10499183 : ℝ) / 25000000)) (U := ((8399347 : ℝ) / 20000000))
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
  · left
    norm_num
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
theorem cell_4261 : CellCertificate ((4261 : ℝ) / 10000) ((2131 : ℝ) / 5000) ((79673 : ℝ) / 250000) ((31217 : ℝ) / 31250) ((33329 : ℝ) / 40000) ((5837 : ℝ) / 62500) ((69659 : ℝ) / 500000) ((24843 : ℝ) / 500000) ((49687 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((79673 : ℝ) / 250000)) (L := ((7833117 : ℝ) / 25000000)) (U := ((31332471 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((31217 : ℝ) / 31250)) (L := ((42044997 : ℝ) / 50000000)) (U := ((84089997 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((79673 : ℝ) / 250000)) (L := ((23741151 : ℝ) / 25000000)) (U := ((94964607 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((142107 : ℝ) / 125000)) (L := ((10511229 : ℝ) / 25000000)) (U := ((42044919 : ℝ) / 100000000))
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
  · left
    norm_num
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
theorem cell_4262 : CellCertificate ((2131 : ℝ) / 5000) ((4263 : ℝ) / 10000) ((15899 : ℝ) / 50000) ((1000729 : ℝ) / 1000000) ((166593 : ℝ) / 200000) ((46889 : ℝ) / 500000) ((69903 : ℝ) / 500000) ((24577 : ℝ) / 500000) ((9831 : ℝ) / 200000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((15899 : ℝ) / 50000)) (L := ((6252969 : ℝ) / 20000000)) (U := ((1954053 : ℝ) / 6250000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1000729 : ℝ) / 1000000)) (L := ((84186463 : ℝ) / 100000000)) (U := ((42093233 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((15899 : ℝ) / 50000)) (L := ((94986889 : ℝ) / 100000000)) (U := ((23746723 : ℝ) / 25000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2272649 : ℝ) / 2000000)) (L := ((21046567 : ℝ) / 50000000)) (U := ((42093137 : ℝ) / 100000000))
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
  · left
    norm_num
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
theorem cell_4263 : CellCertificate ((4263 : ℝ) / 10000) ((533 : ℝ) / 1250) ((158633 : ℝ) / 500000) ((1002521 : ℝ) / 1000000) ((13011 : ℝ) / 15625) ((18833 : ℝ) / 200000) ((17537 : ℝ) / 125000) ((2431 : ℝ) / 50000) ((48621 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((158633 : ℝ) / 500000)) (L := ((3899627 : ℝ) / 12500000)) (U := ((31197019 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1002521 : ℝ) / 1000000)) (L := ((526769 : ℝ) / 625000)) (U := ((84283043 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((158633 : ℝ) / 500000)) (L := ((23752297 : ℝ) / 25000000)) (U := ((95009191 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((454317 : ℝ) / 400000)) (L := ((21070693 : ℝ) / 50000000)) (U := ((42141389 : ℝ) / 100000000))
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
  · left
    norm_num
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
theorem cell_4264 : CellCertificate ((533 : ℝ) / 1250) ((853 : ℝ) / 2000) ((316551 : ℝ) / 1000000) ((251079 : ℝ) / 250000) ((416221 : ℝ) / 500000) ((94553 : ℝ) / 1000000) ((70393 : ℝ) / 500000) ((12021 : ℝ) / 250000) ((9617 : ℝ) / 200000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((316551 : ℝ) / 1000000)) (L := ((31129077 : ℝ) / 100000000)) (U := ((778227 : ℝ) / 2500000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((251079 : ℝ) / 250000)) (L := ((84379507 : ℝ) / 100000000)) (U := ((8437951 : ℝ) / 10000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((316551 : ℝ) / 1000000)) (L := ((9503147 : ℝ) / 10000000)) (U := ((95031473 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((56763 : ℝ) / 50000)) (L := ((4218967 : ℝ) / 10000000)) (U := ((42189673 : ℝ) / 100000000))
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
  · left
    norm_num
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
theorem cell_4265 : CellCertificate ((853 : ℝ) / 2000) ((2133 : ℝ) / 5000) ((63167 : ℝ) / 200000) ((251529 : ℝ) / 250000) ((832179 : ℝ) / 1000000) ((47471 : ℝ) / 500000) ((141277 : ℝ) / 1000000) ((9509 : ℝ) / 200000) ((23773 : ℝ) / 500000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((63167 : ℝ) / 200000)) (L := ((15530513 : ℝ) / 50000000)) (U := ((31061029 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((251529 : ℝ) / 250000)) (L := ((8447597 : ℝ) / 10000000)) (U := ((84475973 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((63167 : ℝ) / 200000)) (L := ((47526867 : ℝ) / 50000000)) (U := ((95053737 : ℝ) / 100000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((141841 : ℝ) / 125000)) (L := ((21118949 : ℝ) / 50000000)) (U := ((42237901 : ℝ) / 100000000))
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
  · left
    norm_num
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
theorem cell_4266 : CellCertificate ((2133 : ℝ) / 5000) ((4267 : ℝ) / 10000) ((315117 : ℝ) / 1000000) ((1007923 : ℝ) / 1000000) ((166383 : ℝ) / 200000) ((95333 : ℝ) / 1000000) ((141769 : ℝ) / 1000000) ((11751 : ℝ) / 250000) ((9401 : ℝ) / 200000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((315117 : ℝ) / 1000000)) (L := ((3099277 : ℝ) / 10000000)) (U := ((30992773 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1007923 : ℝ) / 1000000)) (L := ((84572533 : ℝ) / 100000000)) (U := ((10571567 : ℝ) / 12500000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((315117 : ℝ) / 1000000)) (L := ((95076011 : ℝ) / 100000000)) (U := ((47538007 : ℝ) / 50000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2268391 : ℝ) / 2000000)) (L := ((42286159 : ℝ) / 100000000)) (U := ((21143081 : ℝ) / 50000000))
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
  · left
    norm_num
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
theorem cell_4267 : CellCertificate ((4267 : ℝ) / 10000) ((1067 : ℝ) / 2500) ((314397 : ℝ) / 1000000) ((1009737 : ℝ) / 1000000) ((831649 : ℝ) / 1000000) ((47863 : ℝ) / 500000) ((17783 : ℝ) / 125000) ((23231 : ℝ) / 500000) ((46463 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((314397 : ℝ) / 1000000)) (L := ((30924307 : ℝ) / 100000000)) (U := ((3092431 : ℝ) / 10000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1009737 : ℝ) / 1000000)) (L := ((10583649 : ℝ) / 12500000)) (U := ((16933839 : ℝ) / 20000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((314397 : ℝ) / 1000000)) (L := ((95098301 : ℝ) / 100000000)) (U := ((1485911 : ℝ) / 1562500))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((90693 : ℝ) / 80000)) (L := ((42334453 : ℝ) / 100000000)) (U := ((5291807 : ℝ) / 12500000))
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
  · left
    norm_num
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
theorem cell_4268 : CellCertificate ((1067 : ℝ) / 2500) ((4269 : ℝ) / 10000) ((78419 : ℝ) / 250000) ((505777 : ℝ) / 500000) ((415691 : ℝ) / 500000) ((96119 : ℝ) / 1000000) ((142759 : ℝ) / 1000000) ((45917 : ℝ) / 1000000) ((22959 : ℝ) / 500000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((78419 : ℝ) / 250000)) (L := ((30855733 : ℝ) / 100000000)) (U := ((3856967 : ℝ) / 12500000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((505777 : ℝ) / 500000)) (L := ((21191433 : ℝ) / 25000000)) (U := ((16953147 : ℝ) / 20000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((78419 : ℝ) / 250000)) (L := ((95120573 : ℝ) / 100000000)) (U := ((1486259 : ℝ) / 1562500))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((1133129 : ℝ) / 1000000)) (L := ((2119139 : ℝ) / 5000000)) (U := ((42382783 : ℝ) / 100000000))
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
  · left
    norm_num
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
theorem cell_4269 : CellCertificate ((4269 : ℝ) / 10000) ((427 : ℝ) / 1000) ((312953 : ℝ) / 1000000) ((1013379 : ℝ) / 1000000) ((831113 : ℝ) / 1000000) ((19303 : ℝ) / 200000) ((17907 : ℝ) / 125000) ((4537 : ℝ) / 100000) ((45371 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((312953 : ℝ) / 1000000)) (L := ((30786953 : ℝ) / 100000000)) (U := ((7696739 : ℝ) / 25000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1013379 : ℝ) / 1000000)) (L := ((16972483 : ℝ) / 20000000)) (U := ((42431209 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((312953 : ℝ) / 1000000)) (L := ((95142857 : ℝ) / 100000000)) (U := ((4757143 : ℝ) / 5000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2265191 : ℝ) / 2000000)) (L := ((5303887 : ℝ) / 12500000)) (U := ((42431099 : ℝ) / 100000000))
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
  · left
    norm_num
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
