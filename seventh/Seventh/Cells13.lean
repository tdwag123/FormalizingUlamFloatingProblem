import Seventh.Cells12

/-! Rational cell certificates, verified by Lean. -/

namespace UlamFloating.Seventh

set_option maxHeartbeats 1000000 in
theorem cell_4330 : CellCertificate ((433 : ℝ) / 1000) ((4331 : ℝ) / 10000) ((10611 : ℝ) / 40000) ((30509 : ℝ) / 31250) ((841791 : ℝ) / 1000000) ((93833 : ℝ) / 1000000) ((146501 : ℝ) / 1000000) ((6743 : ℝ) / 1000000) ((843 : ℝ) / 125000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((10611 : ℝ) / 40000)) (L := ((3277183 : ℝ) / 12500000)) (U := ((26217467 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((30509 : ℝ) / 31250)) (L := ((82842397 : ℝ) / 100000000)) (U := ((103553 : ℝ) / 125000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((10611 : ℝ) / 40000)) (L := ((48251021 : ℝ) / 50000000)) (U := ((19300409 : ℝ) / 20000000))
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
  · right
    calc
      3 * Real.pi * ((6743 : ℝ) / 1000000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((6743 : ℝ) / 1000000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((433 : ℝ) / 1000) * (((30509 : ℝ) / 31250) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((433 : ℝ) / 1000) * (((30509 : ℝ) / 31250) - Real.pi / 7) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by norm_num)
        linarith only [hA.2]
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
theorem cell_4331 : CellCertificate ((4331 : ℝ) / 10000) ((1083 : ℝ) / 2500) ((33053 : ℝ) / 125000) ((119511 : ℝ) / 125000) ((845433 : ℝ) / 1000000) ((90327 : ℝ) / 1000000) ((143087 : ℝ) / 1000000) ((5999 : ℝ) / 1000000) ((3 : ℝ) / 500) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((33053 : ℝ) / 125000)) (L := ((6533833 : ℝ) / 25000000)) (U := ((5227067 : ℝ) / 20000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((119511 : ℝ) / 125000)) (L := ((10211771 : ℝ) / 12500000)) (U := ((81694171 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((33053 : ℝ) / 125000)) (L := ((96524319 : ℝ) / 100000000)) (U := ((48262161 : ℝ) / 50000000))
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
  · right
    calc
      3 * Real.pi * ((5999 : ℝ) / 1000000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((5999 : ℝ) / 1000000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((4331 : ℝ) / 10000) * (((119511 : ℝ) / 125000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((4331 : ℝ) / 10000) * (((119511 : ℝ) / 125000) - Real.pi / 7) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by norm_num)
        linarith only [hA.2]
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
theorem cell_4332 : CellCertificate ((1083 : ℝ) / 2500) ((4333 : ℝ) / 10000) ((26357 : ℝ) / 100000) ((933993 : ℝ) / 1000000) ((849359 : ℝ) / 1000000) ((43269 : ℝ) / 500000) ((139389 : ℝ) / 1000000) ((21 : ℝ) / 4000) ((5251 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((26357 : ℝ) / 100000)) (L := ((2605289 : ℝ) / 10000000)) (U := ((26052893 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((933993 : ℝ) / 1000000)) (L := ((20100017 : ℝ) / 25000000)) (U := ((80400071 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((26357 : ℝ) / 100000)) (L := ((96546603 : ℝ) / 100000000)) (U := ((48273303 : ℝ) / 50000000))
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
  · right
    calc
      3 * Real.pi * ((21 : ℝ) / 4000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((21 : ℝ) / 4000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((1083 : ℝ) / 2500) * (((933993 : ℝ) / 1000000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((1083 : ℝ) / 2500) * (((933993 : ℝ) / 1000000) - Real.pi / 7) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by norm_num)
        linarith only [hA.2]
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
theorem cell_4333 : CellCertificate ((4333 : ℝ) / 10000) ((2167 : ℝ) / 5000) ((262713 : ℝ) / 1000000) ((454777 : ℝ) / 500000) ((853629 : ℝ) / 1000000) ((16481 : ℝ) / 200000) ((33837 : ℝ) / 250000) ((4497 : ℝ) / 1000000) ((2249 : ℝ) / 500000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((262713 : ℝ) / 1000000)) (L := ((1298507 : ℝ) / 5000000)) (U := ((25970143 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((454777 : ℝ) / 500000)) (L := ((4932687 : ℝ) / 6250000)) (U := ((15784599 : ℝ) / 20000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((262713 : ℝ) / 1000000)) (L := ((19313779 : ℝ) / 20000000)) (U := ((48284449 : ℝ) / 50000000))
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
  · right
    calc
      3 * Real.pi * ((4497 : ℝ) / 1000000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((4497 : ℝ) / 1000000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((4333 : ℝ) / 10000) * (((454777 : ℝ) / 500000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((4333 : ℝ) / 10000) * (((454777 : ℝ) / 500000) - Real.pi / 7) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by norm_num)
        linarith only [hA.2]
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
theorem cell_4334 : CellCertificate ((2167 : ℝ) / 5000) ((867 : ℝ) / 2000) ((130927 : ℝ) / 500000) ((35281 : ℝ) / 40000) ((858347 : ℝ) / 1000000) ((1216 : ℝ) / 15625) ((65429 : ℝ) / 500000) ((3739 : ℝ) / 1000000) ((187 : ℝ) / 50000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((130927 : ℝ) / 500000)) (L := ((12943589 : ℝ) / 50000000)) (U := ((25887181 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((35281 : ℝ) / 40000)) (L := ((77202751 : ℝ) / 100000000)) (U := ((38601377 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((130927 : ℝ) / 500000)) (L := ((1509237 : ℝ) / 1562500)) (U := ((96591171 : ℝ) / 100000000))
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
  · right
    calc
      3 * Real.pi * ((3739 : ℝ) / 1000000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((3739 : ℝ) / 1000000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((2167 : ℝ) / 5000) * (((35281 : ℝ) / 40000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((2167 : ℝ) / 5000) * (((35281 : ℝ) / 40000) - Real.pi / 7) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by norm_num)
        linarith only [hA.2]
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
theorem cell_4335 : CellCertificate ((867 : ℝ) / 2000) ((271 : ℝ) / 625) ((4078 : ℝ) / 15625) ((850257 : ℝ) / 1000000) ((863669 : ℝ) / 1000000) ((36319 : ℝ) / 500000) ((31441 : ℝ) / 250000) ((93 : ℝ) / 31250) ((2977 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((4078 : ℝ) / 15625)) (L := ((25803907 : ℝ) / 100000000)) (U := ((2580391 : ℝ) / 10000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((850257 : ℝ) / 1000000)) (L := ((37572499 : ℝ) / 50000000)) (U := ((75145001 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((4078 : ℝ) / 15625)) (L := ((48306723 : ℝ) / 50000000)) (U := ((96613449 : ℝ) / 100000000))
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
  · right
    calc
      3 * Real.pi * ((93 : ℝ) / 31250) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((93 : ℝ) / 31250) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((867 : ℝ) / 2000) * (((850257 : ℝ) / 1000000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((867 : ℝ) / 2000) * (((850257 : ℝ) / 1000000) - Real.pi / 7) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by norm_num)
        linarith only [hA.2]
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
theorem cell_4336 : CellCertificate ((271 : ℝ) / 625) ((4337 : ℝ) / 10000) ((260127 : ℝ) / 1000000) ((50763 : ℝ) / 62500) ((217467 : ℝ) / 250000) ((4161 : ℝ) / 62500) ((119793 : ℝ) / 1000000) ((69 : ℝ) / 31250) ((2209 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((260127 : ℝ) / 1000000)) (L := ((25720327 : ℝ) / 100000000)) (U := ((2572033 : ℝ) / 10000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((50763 : ℝ) / 62500)) (L := ((72580781 : ℝ) / 100000000)) (U := ((4536299 : ℝ) / 6250000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((260127 : ℝ) / 1000000)) (L := ((96635731 : ℝ) / 100000000)) (U := ((48317867 : ℝ) / 50000000))
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
  · right
    calc
      3 * Real.pi * ((69 : ℝ) / 31250) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((69 : ℝ) / 31250) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((271 : ℝ) / 625) * (((50763 : ℝ) / 62500) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((271 : ℝ) / 625) * (((50763 : ℝ) / 62500) - Real.pi / 7) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by norm_num)
        linarith only [hA.2]
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
theorem cell_4337 : CellCertificate ((4337 : ℝ) / 10000) ((2169 : ℝ) / 5000) ((259259 : ℝ) / 1000000) ((763559 : ℝ) / 1000000) ((877511 : ℝ) / 1000000) ((59071 : ℝ) / 1000000) ((112379 : ℝ) / 1000000) ((287 : ℝ) / 200000) ((359 : ℝ) / 250000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((259259 : ℝ) / 1000000)) (L := ((25636437 : ℝ) / 100000000)) (U := ((640911 : ℝ) / 2500000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((763559 : ℝ) / 1000000)) (L := ((2765987 : ℝ) / 4000000)) (U := ((34574839 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((259259 : ℝ) / 1000000)) (L := ((96658019 : ℝ) / 100000000)) (U := ((48329011 : ℝ) / 50000000))
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
  · right
    calc
      3 * Real.pi * ((287 : ℝ) / 200000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((287 : ℝ) / 200000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((4337 : ℝ) / 10000) * (((763559 : ℝ) / 1000000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((4337 : ℝ) / 10000) * (((763559 : ℝ) / 1000000) - Real.pi / 7) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by norm_num)
        linarith only [hA.2]
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
theorem cell_4338 : CellCertificate ((2169 : ℝ) / 5000) ((4339 : ℝ) / 10000) ((258389 : ℝ) / 1000000) ((691377 : ℝ) / 1000000) ((444127 : ℝ) / 500000) ((9693 : ℝ) / 200000) ((12733 : ℝ) / 125000) ((657 : ℝ) / 1000000) ((329 : ℝ) / 500000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((258389 : ℝ) / 1000000)) (L := ((5110467 : ℝ) / 20000000)) (U := ((12776169 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((691377 : ℝ) / 1000000)) (L := ((63759857 : ℝ) / 100000000)) (U := ((3187993 : ℝ) / 5000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((258389 : ℝ) / 1000000)) (L := ((96680287 : ℝ) / 100000000)) (U := ((9668029 : ℝ) / 10000000))
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
  · right
    calc
      3 * Real.pi * ((657 : ℝ) / 1000000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((657 : ℝ) / 1000000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((2169 : ℝ) / 5000) * (((691377 : ℝ) / 1000000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((2169 : ℝ) / 5000) * (((691377 : ℝ) / 1000000) - Real.pi / 7) ^ 3 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply pow_le_pow_left₀ (by norm_num)
        linarith only [hA.2]
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
