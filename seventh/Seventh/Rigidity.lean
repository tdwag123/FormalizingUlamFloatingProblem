import Seventh.AllCells
import Seventh.Statements
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Rigidity at perimetral density one seventh

The numerical cells cover the full interval allowed by the boundary geometry.
The conclusion is equality of the original body with a positive-radius closed
disk, with no symmetry or curvature lower bound assumed.
-/

namespace UlamFloating.Seventh

/-- Every admissible boundary with constant one-seventh chords bounds a disk. -/
theorem rigidity_of_boundary {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l) : IsDisk K := by
  obtain ⟨o, θ, α, hs⟩ := exists_contactSystem hb hl hc
  let frequency := Real.pi * l / P
  have hP := hb.period_pos
  have hpositive : 0 < frequency := by dsimp [frequency]; positivity
  have hlower : (21 : ℝ) / 50 < frequency := hs.frequency_gt hb hl hc
  have hupper : frequency ≤ Real.sin (Real.pi / 7) := hs.frequency_le_sin hP hl
  have hsine := certificate_sin_1
  simp only [one_mul] at hsine
  let j : ℕ := ⌊10000 * frequency⌋₊
  have hscaled : 0 ≤ 10000 * frequency := by positivity
  have hjlo : 4200 ≤ j := (Nat.le_floor_iff hscaled).mpr (by norm_num; linarith)
  have hjhi : j ≤ 4338 := by
    have he : j < 4339 := (Nat.floor_lt hscaled).mpr (by norm_num; linarith [hsine.2])
    omega
  obtain ⟨B, U, c, w, δ, J, V, hcert⟩ := certificate_for_index j hjlo hjhi
  have hcelllo : (j : ℝ) / 10000 ≤ frequency := by
    have he := Nat.floor_le hscaled
    change (j : ℝ) ≤ 10000 * frequency at he
    linarith
  have hcellhi : frequency ≤ ((j + 1 : ℕ) : ℝ) / 10000 := by
    have he := Nat.lt_floor_add_one (10000 * frequency)
    change 10000 * frequency < (j : ℝ) + 1 at he
    push_cast
    linarith
  exact hcert.isDisk hb hl hc hs hcelllo hcellhi

/-- The unconditional constant-chord rigidity theorem at perimetral density `1/7`. -/
theorem rigidity : PerimetralRigidity ((1 : ℝ) / 7) := by
  intro K hK
  obtain ⟨_, _, P, γ, hb, l, hl, hc⟩ := hK
  rw [show ((1 : ℝ) / 7) * P = P / 7 by ring] at hc
  exact rigidity_of_boundary hb hl hc

end UlamFloating.Seventh
