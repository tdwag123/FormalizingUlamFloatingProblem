import UlamFloating.AngularCoordinates
import UlamFloating.ChordInjectivity

/-!
# One full turn of constant boundary chords

A nonzero vector fixed by a rotation has angle an integer multiple of two pi.
An increasing global angle with no intermediate return makes exactly one turn.
The convex-boundary chord nonreturn theorem supplies that geometric hypothesis.
-/

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- A rotation fixing a nonzero vector has angle an integer multiple of two pi. -/
theorem rotation_angle_eq_int_mul (o : Orientation ℝ E (Fin 2)) {e : E} (he : e ≠ 0)
    {θ : ℝ} (hrot : e = Real.cos θ • e + Real.sin θ • o.rightAngleRotation e) :
    ∃ k : ℤ, θ = (k : ℝ) * (2 * Real.pi) := by
  have hi := congrArg (fun z => ⟪e, z⟫_ℝ) hrot
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    o.inner_rightAngleRotation_right, o.areaForm_apply_self, neg_zero, mul_zero, add_zero] at hi
  have hn : 0 < ‖e‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr he)
  have hcos : Real.cos θ = 1 := by nlinarith
  obtain ⟨k, hk⟩ := (Real.cos_eq_one_iff θ).mp hcos
  exact ⟨k, hk.symm⟩

/-- Increasing global angular coordinates make exactly one turn if the
nonzero rotating vector first returns at the specified positive endpoint. -/
theorem angle_eq_two_pi_of_no_return (o : Orientation ℝ E (Fin 2))
    {e : ℝ → E} (θ : ℝ ≃o ℝ) (hθ0 : θ 0 = 0) {P : ℝ} (hP : 0 < P)
    (he0 : e 0 ≠ 0) (heP : e P = e 0)
    (hrot : ∀ t, e t = Real.cos (θ t) • e 0 + Real.sin (θ t) • o.rightAngleRotation (e 0))
    (hnoreturn : ∀ t, 0 < t → t < P → e t ≠ e 0) : θ P = 2 * Real.pi := by
  obtain ⟨k, hk⟩ := rotation_angle_eq_int_mul o he0 (heP.symm.trans (hrot P))
  have hpos : 0 < θ P := by simpa only [hθ0] using θ.strictMono hP
  have hkpos : (0 : ℝ) < k := by
    rw [hk] at hpos
    exact (mul_pos_iff_of_pos_right Real.two_pi_pos).mp hpos
  have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
  have hkge : (1 : ℝ) ≤ k := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
  have hge : 2 * Real.pi ≤ θ P := by rw [hk]; nlinarith [Real.pi_pos]
  have hle : θ P ≤ 2 * Real.pi := by
    by_contra hnot
    have hlt : 2 * Real.pi < θ P := lt_of_not_ge hnot
    let s := θ.symm (2 * Real.pi)
    have hs : θ s = 2 * Real.pi := θ.apply_symm_apply _
    have hs0 : 0 < s := θ.strictMono.lt_iff_lt.mp (by rw [hθ0, hs]; exact Real.two_pi_pos)
    have hsP : s < P := θ.strictMono.lt_iff_lt.mp (by rw [hs]; exact hlt)
    apply hnoreturn s hs0 hsP
    simpa only [hs, Real.cos_two_pi, Real.sin_two_pi, one_smul, zero_smul, add_zero] using hrot s
  exact le_antisymm hle hge

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- For increments less than half the boundary period, the global chord
angle makes exactly one turn. Its integer shift law has increment `2π`. -/
theorem IsUnitSpeedBoundary.chord_angle_coordinates_one_turn
    {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (hh : 0 < h) (hhalf : 2 * h < P) (hl : 0 < l) (hc : HasConstantChord γ h l) :
    ∃ (o : Orientation ℝ Plane (Fin 2)) (θ : ℝ ≃o ℝ),
      ContDiff ℝ 1 (fun t => θ t) ∧ ContDiff ℝ 1 (fun t => θ.symm t) ∧ θ 0 = 0 ∧
      θ P = 2 * Real.pi ∧
      (∀ t, 0 < deriv (fun s => θ s) t ∧ deriv (fun s => θ s) t ≤ 2 / l) ∧
      (∀ t, γ (t + h) - γ t = Real.cos (θ t) • (γ h - γ 0) +
        Real.sin (θ t) • o.rightAngleRotation (γ h - γ 0)) ∧
      (∀ t (k : ℤ), θ (t + (k : ℝ) * P) = θ t + (k : ℝ) * (2 * Real.pi)) := by
  obtain ⟨o, θ, hθc, hθinv, hθ0, hbound, hrot, hshift⟩ := hb.chord_angle_coordinates hl hc
  let e : ℝ → Plane := fun t => γ (t + h) - γ t
  have he0 : e 0 ≠ 0 := by
    have he : ‖e 0‖ = l := by simpa only [e, dist_eq_norm] using hc 0
    intro hz
    rw [hz, norm_zero] at he
    exact hl.ne' he.symm
  have heP : e P = e 0 := by
    dsimp [e]
    rw [show P + h = h + P by ring, hb.periodic]
    simpa only [zero_add] using congrArg (fun z => γ h - z) (hb.periodic 0)
  have hturn := angle_eq_two_pi_of_no_return o θ hθ0 hb.period_pos he0 heP
    (fun t => by simpa only [e, zero_add] using hrot t)
    (fun t ht htP => by simpa only [e, zero_add] using hb.chord_vector_ne_initial hh hhalf ht htP)
  refine ⟨o, θ, hθc, hθinv, hθ0, hturn, hbound, hrot, ?_⟩
  intro t k
  rw [hshift, hturn]

end UlamFloating
