import UlamFloating.FiniteSampling

/-!
# Injectivity of a single boundary traversal

The period and simplicity fields give injectivity on every half-open traversal
interval. In particular, rational finite samples are distinct. These facts are
separate from the cyclic-order and strict-convexity conclusions for polygons.
-/

namespace UlamFloating

/-- A once-traversed periodic boundary is injective on any half-open interval
of length one period. -/
theorem IsUnitSpeedBoundary.injOn_Ico {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (a : ℝ) : Set.InjOn γ (Set.Ico a (a + P)) := by
  intro s hs t ht heq
  obtain ⟨k, hk⟩ := (hb.simple s t).mp heq
  have hklo : (-1 : ℤ) < k := by
    by_contra h
    have hk' : (k : ℝ) ≤ -1 := by exact_mod_cast (le_of_not_gt h)
    have hm := mul_le_mul_of_nonneg_right hk' hb.period_pos.le
    linarith [hs.1, ht.2]
  have hkhi : k < (1 : ℤ) := by
    by_contra h
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast (le_of_not_gt h)
    have hm := mul_le_mul_of_nonneg_right hk' hb.period_pos.le
    linarith [ht.1, hs.2]
  have hkzero : k = 0 := by omega
  simpa only [hkzero, Int.cast_zero, zero_mul, add_zero] using hk

/-- Distinct finite indices give distinct points in a rational sampling of
a once-traversed boundary. -/
theorem IsUnitSpeedBoundary.boundarySamples_injective {K : Set Plane} {P : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (n : ℕ) (t : ℝ) :
    Function.Injective (fun i : Fin n => boundarySamples γ P n i t) := by
  intro i j hij
  have hn : (0 : ℝ) < n := by exact_mod_cast Fin.pos i
  have hstep : 0 < P / n := div_pos hb.period_pos hn
  have hmem (k : Fin n) : t + (k.val : ℝ) * (P / n) ∈ Set.Ico t (t + P) := by
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep.le)
    · apply add_lt_add_left
      calc
        (k.val : ℝ) * (P / n) < (n : ℝ) * (P / n) :=
          mul_lt_mul_of_pos_right (by exact_mod_cast k.isLt) hstep
        _ = P := by field_simp
  have hparam := hb.injOn_Ico t (hmem i) (hmem j) hij
  have hcast : (i.val : ℝ) = (j.val : ℝ) :=
    mul_right_cancel₀ hstep.ne' (add_left_cancel hparam)
  apply Fin.ext
  exact_mod_cast hcast

end UlamFloating
