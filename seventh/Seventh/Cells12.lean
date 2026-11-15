import Seventh.Cells11

/-! Rational cell certificates, verified by Lean. -/

namespace UlamFloating.Seventh

set_option maxHeartbeats 1000000 in
theorem cell_4320 : CellCertificate ((54 : ℝ) / 125) ((4321 : ℝ) / 10000) ((54729 : ℝ) / 200000) ((1115551 : ℝ) / 1000000) ((815293 : ℝ) / 1000000) ((5949 : ℝ) / 50000) ((25223 : ℝ) / 200000) ((13943 : ℝ) / 1000000) ((1743 : ℝ) / 125000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((54729 : ℝ) / 200000)) (L := ((27024259 : ℝ) / 100000000)) (U := ((13512131 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1115551 : ℝ) / 1000000)) (L := ((89815317 : ℝ) / 100000000)) (U := ((2245383 : ℝ) / 2500000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((54729 : ℝ) / 200000)) (L := ((3851169 : ℝ) / 4000000)) (U := ((24069807 : ℝ) / 25000000))
    (by norm_num) (by norm_num [cosPolynomial14]) (by norm_num [cosPolynomial14])
  have hCN := cos_rational_enclosure (x := ((2210131 : ℝ) / 2000000)) (L := ((4490759 : ℝ) / 10000000)) (U := ((44907593 : ℝ) / 100000000))
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
theorem cell_4321 : CellCertificate ((4321 : ℝ) / 10000) ((2161 : ℝ) / 5000) ((272819 : ℝ) / 1000000) ((1109819 : ℝ) / 1000000) ((816461 : ℝ) / 1000000) ((23589 : ℝ) / 200000) ((127123 : ℝ) / 1000000) ((6621 : ℝ) / 500000) ((13243 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((272819 : ℝ) / 1000000)) (L := ((26944723 : ℝ) / 100000000)) (U := ((13472363 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1109819 : ℝ) / 1000000)) (L := ((89561817 : ℝ) / 100000000)) (U := ((4478091 : ℝ) / 5000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((272819 : ℝ) / 1000000)) (L := ((48150757 : ℝ) / 50000000)) (U := ((96301517 : ℝ) / 100000000))
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
      3 * Real.pi * ((6621 : ℝ) / 500000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((6621 : ℝ) / 500000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((4321 : ℝ) / 10000) * (((1109819 : ℝ) / 1000000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((4321 : ℝ) / 10000) * (((1109819 : ℝ) / 1000000) - Real.pi / 7) ^ 3 := by
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
theorem cell_4322 : CellCertificate ((2161 : ℝ) / 5000) ((4323 : ℝ) / 10000) ((271991 : ℝ) / 1000000) ((548903 : ℝ) / 500000) ((818827 : ℝ) / 1000000) ((57857 : ℝ) / 500000) ((12933 : ℝ) / 100000) ((1567 : ℝ) / 125000) ((12537 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((271991 : ℝ) / 1000000)) (L := ((1679061 : ℝ) / 6250000)) (U := ((26864979 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((548903 : ℝ) / 500000)) (L := ((89021001 : ℝ) / 100000000)) (U := ((22255251 : ℝ) / 25000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((271991 : ℝ) / 1000000)) (L := ((96323791 : ℝ) / 100000000)) (U := ((48161897 : ℝ) / 50000000))
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
      3 * Real.pi * ((1567 : ℝ) / 125000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((1567 : ℝ) / 125000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((2161 : ℝ) / 5000) * (((548903 : ℝ) / 500000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((2161 : ℝ) / 5000) * (((548903 : ℝ) / 500000) - Real.pi / 7) ^ 3 := by
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
theorem cell_4323 : CellCertificate ((4323 : ℝ) / 10000) ((1081 : ℝ) / 2500) ((6779 : ℝ) / 25000) ((1085283 : ℝ) / 1000000) ((32851 : ℝ) / 40000) ((113401 : ℝ) / 1000000) ((65809 : ℝ) / 500000) ((11827 : ℝ) / 1000000) ((2957 : ℝ) / 250000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((6779 : ℝ) / 25000)) (L := ((13392461 : ℝ) / 50000000)) (U := ((1071397 : ℝ) / 4000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1085283 : ℝ) / 1000000)) (L := ((1768871 : ℝ) / 2000000)) (U := ((88443553 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((6779 : ℝ) / 25000)) (L := ((48173041 : ℝ) / 50000000)) (U := ((19269217 : ℝ) / 20000000))
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
      3 * Real.pi * ((11827 : ℝ) / 1000000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((11827 : ℝ) / 1000000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((4323 : ℝ) / 10000) * (((1085283 : ℝ) / 1000000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((4323 : ℝ) / 10000) * (((1085283 : ℝ) / 1000000) - Real.pi / 7) ^ 3 := by
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
theorem cell_4324 : CellCertificate ((1081 : ℝ) / 2500) ((173 : ℝ) / 400) ((270327 : ℝ) / 1000000) ((1072179 : ℝ) / 1000000) ((823817 : ℝ) / 1000000) ((55497 : ℝ) / 500000) ((134001 : ℝ) / 1000000) ((5557 : ℝ) / 500000) ((2223 : ℝ) / 200000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((270327 : ℝ) / 1000000)) (L := ((1669041 : ℝ) / 6250000)) (U := ((26704659 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((1072179 : ℝ) / 1000000)) (L := ((4391223 : ℝ) / 5000000)) (U := ((87824463 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((270327 : ℝ) / 1000000)) (L := ((96368361 : ℝ) / 100000000)) (U := ((24092091 : ℝ) / 25000000))
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
      3 * Real.pi * ((5557 : ℝ) / 500000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((5557 : ℝ) / 500000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((1081 : ℝ) / 2500) * (((1072179 : ℝ) / 1000000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((1081 : ℝ) / 2500) * (((1072179 : ℝ) / 1000000) - Real.pi / 7) ^ 3 := by
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
theorem cell_4325 : CellCertificate ((173 : ℝ) / 400) ((2163 : ℝ) / 5000) ((67373 : ℝ) / 250000) ((132301 : ℝ) / 125000) ((413233 : ℝ) / 500000) ((339 : ℝ) / 3125) ((13649 : ℝ) / 100000) ((2599 : ℝ) / 250000) ((10397 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((67373 : ℝ) / 250000)) (L := ((26624179 : ℝ) / 100000000)) (U := ((13312091 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((132301 : ℝ) / 125000)) (L := ((10894701 : ℝ) / 12500000)) (U := ((87157611 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((67373 : ℝ) / 250000)) (L := ((48195313 : ℝ) / 50000000)) (U := ((96390629 : ℝ) / 100000000))
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
      3 * Real.pi * ((2599 : ℝ) / 250000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((2599 : ℝ) / 250000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((173 : ℝ) / 400) * (((132301 : ℝ) / 125000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((173 : ℝ) / 400) * (((132301 : ℝ) / 125000) - Real.pi / 7) ^ 3 := by
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
theorem cell_4326 : CellCertificate ((2163 : ℝ) / 5000) ((4327 : ℝ) / 10000) ((268653 : ℝ) / 1000000) ((104391 : ℝ) / 100000) ((829231 : ℝ) / 1000000) ((2117 : ℝ) / 20000) ((17387 : ℝ) / 125000) ((4837 : ℝ) / 500000) ((387 : ℝ) / 40000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((268653 : ℝ) / 1000000)) (L := ((13271649 : ℝ) / 50000000)) (U := ((26543301 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((104391 : ℝ) / 100000)) (L := ((43218847 : ℝ) / 50000000)) (U := ((86437697 : ℝ) / 100000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((268653 : ℝ) / 1000000)) (L := ((96412929 : ℝ) / 100000000)) (U := ((24103233 : ℝ) / 25000000))
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
      3 * Real.pi * ((4837 : ℝ) / 500000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((4837 : ℝ) / 500000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((2163 : ℝ) / 5000) * (((104391 : ℝ) / 100000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((2163 : ℝ) / 5000) * (((104391 : ℝ) / 100000) - Real.pi / 7) ^ 3 := by
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
theorem cell_4327 : CellCertificate ((4327 : ℝ) / 10000) ((541 : ℝ) / 1250) ((267813 : ℝ) / 1000000) ((102859 : ℝ) / 100000) ((6657 : ℝ) / 8000) ((103091 : ℝ) / 1000000) ((14183 : ℝ) / 100000) ((2237 : ℝ) / 250000) ((8949 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((267813 : ℝ) / 1000000)) (L := ((13231151 : ℝ) / 50000000)) (U := ((5292461 : ℝ) / 20000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((102859 : ℝ) / 100000)) (L := ((85657223 : ℝ) / 100000000)) (U := ((42828613 : ℝ) / 50000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((267813 : ℝ) / 1000000)) (L := ((12054399 : ℝ) / 12500000)) (U := ((19287039 : ℝ) / 20000000))
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
      3 * Real.pi * ((2237 : ℝ) / 250000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((2237 : ℝ) / 250000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((4327 : ℝ) / 10000) * (((102859 : ℝ) / 100000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((4327 : ℝ) / 10000) * (((102859 : ℝ) / 100000) - Real.pi / 7) ^ 3 := by
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
theorem cell_4328 : CellCertificate ((541 : ℝ) / 1250) ((4329 : ℝ) / 10000) ((266969 : ℝ) / 1000000) ((101233 : ℝ) / 100000) ((417583 : ℝ) / 500000) ((50093 : ℝ) / 500000) ((18089 : ℝ) / 125000) ((4109 : ℝ) / 500000) ((8219 : ℝ) / 1000000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((266969 : ℝ) / 1000000)) (L := ((26380901 : ℝ) / 100000000)) (U := ((3297613 : ℝ) / 12500000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((101233 : ℝ) / 100000)) (L := ((84806877 : ℝ) / 100000000)) (U := ((530043 : ℝ) / 625000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((266969 : ℝ) / 1000000)) (L := ((24114373 : ℝ) / 25000000)) (U := ((19291499 : ℝ) / 20000000))
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
      3 * Real.pi * ((4109 : ℝ) / 500000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((4109 : ℝ) / 500000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((541 : ℝ) / 1250) * (((101233 : ℝ) / 100000) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((541 : ℝ) / 1250) * (((101233 : ℝ) / 100000) - Real.pi / 7) ^ 3 := by
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
theorem cell_4329 : CellCertificate ((4329 : ℝ) / 10000) ((433 : ℝ) / 1000) ((266123 : ℝ) / 1000000) ((12437 : ℝ) / 12500) ((838379 : ℝ) / 1000000) ((97109 : ℝ) / 1000000) ((29553 : ℝ) / 200000) ((7483 : ℝ) / 1000000) ((1871 : ℝ) / 250000) := by
  have hA := certificate_angle_bounds
  have hS := certificate_sin_1
  simp only [one_mul] at hS
  have hSB := sin_rational_enclosure (x := ((266123 : ℝ) / 1000000)) (L := ((26299289 : ℝ) / 100000000)) (U := ((6574823 : ℝ) / 25000000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hSU := sin_rational_enclosure (x := ((12437 : ℝ) / 12500)) (L := ((83873717 : ℝ) / 100000000)) (U := ((2096843 : ℝ) / 2500000))
    (by norm_num) (by norm_num [sinPolynomial14]) (by norm_num [sinPolynomial14])
  have hCB := cos_rational_enclosure (x := ((266123 : ℝ) / 1000000)) (L := ((3859191 : ℝ) / 4000000)) (U := ((48239889 : ℝ) / 50000000))
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
      3 * Real.pi * ((7483 : ℝ) / 1000000) ≤ 3 * ((3926990817 : ℝ) / 1250000000) * ((7483 : ℝ) / 1000000) := by
        nlinarith only [certificate_pi_bounds.2]
      _ < ((4329 : ℝ) / 10000) * (((12437 : ℝ) / 12500) - ((2243994753 : ℝ) / 5000000000)) ^ 3 := by norm_num
      _ ≤ ((4329 : ℝ) / 10000) * (((12437 : ℝ) / 12500) - Real.pi / 7) ^ 3 := by
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
