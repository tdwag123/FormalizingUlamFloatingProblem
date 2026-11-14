import UlamFloating.PentagonAngleRelations
import UlamFloating.SampledAngleCurve

/-!
# Geometric extraction of the pentagon differential equation

The angle equation is derived from the original constant-chord boundary
hypotheses. No differential equation or tangent-angle system is assumed.
-/

namespace UlamFloating

open scoped BigOperators

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The actual five sampled chord-angle coordinates satisfy the pentagon
equation with the time scale determined by the chord length. -/
theorem IsUnitSpeedBoundary.pentagon_angle_deriv
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l)
    (hθ : ContDiff ℝ 1 (fun t => θ t))
    (hpos : ∀ t, 0 < deriv (fun s => θ s) t)
    (hrot : ∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
      Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0))
    (hshift : ∀ t, θ (t + P) = θ t + 2 * Real.pi) (t : ℝ) :
    deriv (cyclicAngleCurve θ P 5) t =
      (2 / l) • pentagonAngleField (cyclicAngleCurve θ P 5 t) := by
  have hh : 0 < P / 5 := div_pos hb.period_pos (by norm_num)
  have hhalf : 2 * (P / 5) < P := by linarith [hb.period_pos]
  obtain ⟨α, ha, _, hsum, hspeed⟩ :=
    hb.exists_tangent_chord_angles o θ hh hhalf hl hc hθ hpos hrot
  have hfive : 5 * (P / 5) = P := by ring
  have ha' : Function.Periodic α (5 * (P / 5)) := by rwa [hfive]
  have hturn (s : ℝ) : θ (s + 5 * (P / 5)) = θ s + 2 * Real.pi := by
    rw [hfive, hshift]
  have hdx (s : ℝ) := hasDerivAt_five_angle_coordinate ha' hturn
    (hθ.differentiable (by simp)) hsum hspeed s
  have hdcurve := ((cyclicAngleCurve_contDiff hθ P 5).differentiable (by simp) t).hasDerivAt
  ext i
  have hd := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i).hasFDerivAt.comp_hasDerivAt t hdcurve
  change HasDerivAt (cyclicAngleCoordinates θ P 5 i)
    (deriv (cyclicAngleCurve θ P 5) t i) t at hd
  have hbase := (hdx (t + (i.val : ℝ) * (P / 5))).scomp t
    ((hasDerivAt_id t).add_const ((i.val : ℝ) * (P / 5)))
  have hval := hd.unique hbase
  change deriv (cyclicAngleCurve θ P 5) t i =
    (2 / l) * (pentagonAngleField (cyclicAngleCurve θ P 5 t) i)
  rw [pentagonAngleField_apply]
  change deriv (cyclicAngleCurve θ P 5) t i = (2 / l) *
    (Real.sin (cyclicAngleCoordinates θ P 5 (i + 2) t +
      cyclicAngleCoordinates θ P 5 (i + 4) t) -
     Real.sin (cyclicAngleCoordinates θ P 5 (i + 1) t +
      cyclicAngleCoordinates θ P 5 (i + 3) t))
  have hs1 := cyclicAngleCoordinates_rotate hshift i t
  have hs2 := cyclicAngleCoordinates_add_nat hshift i 2 t
  have hs3 := cyclicAngleCoordinates_add_nat hshift i 3 t
  have hs4 := cyclicAngleCoordinates_add_nat hshift i 4 t
  norm_num at hs1 hs2 hs3 hs4
  rw [hs2, hs4, hs1, hs3]
  simpa only [one_smul, cyclicAngleCoordinates, boundarySamples, sampledVertex,
    Nat.cast_ofNat, Nat.cast_one, one_mul, add_assoc, add_left_comm, add_comm] using hval

/-- Every constant one-fifth chord boundary produces a periodic convex
five-angle solution with the precise equation, sum, and cyclic time shift. -/
theorem IsUnitSpeedBoundary.exists_pentagon_angle_solution
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (hl : 0 < l) (hc : HasConstantChord γ (P / 5) l) :
    ∃ (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ),
      (∀ t, γ (t + P / 5) - γ t = Real.cos (θ t) • (γ (P / 5) - γ 0) +
        Real.sin (θ t) • o.rightAngleRotation (γ (P / 5) - γ 0)) ∧
      let x := cyclicAngleCurve θ P 5
      ContDiff ℝ 1 x ∧ Function.Periodic x P ∧
      (∀ t, ∑ i, x t i = 3 * Real.pi) ∧
      (∀ t i, 0 < x t i ∧ x t i < Real.pi) ∧
      (∀ t i, x t (i + 1) = x (t + P / 5) i) ∧
      (∀ t, deriv x t = (2 / l) • pentagonAngleField (x t)) := by
  have hh : 0 < P / 5 := div_pos hb.period_pos (by norm_num)
  have hhalf : 2 * (P / 5) < P := by linarith [hb.period_pos]
  obtain ⟨o, θ, hθ, _, _, _, hbound, hrot, hshift⟩ :=
    hb.chord_angle_coordinates_one_turn hh hhalf hl hc
  have hp (t : ℝ) : θ (t + P) = θ t + 2 * Real.pi := by
    simpa only [Int.cast_one, one_mul] using hshift t 1
  refine ⟨o, θ, hrot, cyclicAngleCurve_contDiff hθ P 5,
    cyclicAngleCurve_periodic hp 5, ?_, ?_, ?_, ?_⟩
  · intro t
    change (∑ i, cyclicAngleCoordinates θ P 5 i t) = 3 * Real.pi
    rw [cyclicAngleCoordinates_sum hp (by decide : 5 ≠ 0)]
    norm_num
    ring
  · intro t i
    exact hb.angle_coordinate_pos_lt_pi o θ hh hhalf hrot
      (t + (i.val : ℝ) * (P / 5))
  · intro t i
    change cyclicAngleCoordinates θ P 5 (i + 1) t =
      cyclicAngleCoordinates θ P 5 i (t + P / 5)
    simpa only [finRotate_succ_apply, Nat.cast_ofNat] using
      cyclicAngleCoordinates_rotate hp i t
  · exact hb.pentagon_angle_deriv o θ hl hc hθ (fun t => (hbound t).1) hrot hp

end UlamFloating
