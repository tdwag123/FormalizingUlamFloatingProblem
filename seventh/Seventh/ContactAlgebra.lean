import UlamFloating.BoundaryTangentAngles
import Mathlib.Tactic.FinCases

/-!
# Seven contact angles: exact algebra

The odd-cycle system is solved over the reals, without assuming extra
regularity of its solution. This is the regularity bridge in Section 2 of
the supplied argument. The angle sum and differential equation are derived,
not imposed on an arbitrary periodic motion.
-/

namespace UlamFloating.Seventh

/-- The seven consecutive angle equations uniquely determine the first angle. -/
theorem seven_contact_angle_eq {α θ : ℝ → ℝ} {h : ℝ}
    (ha : Function.Periodic α (7 * h))
    (hturn : ∀ t, θ (t + 7 * h) = θ t + 2 * Real.pi)
    (hsum : ∀ t, α t + α (t + h) = θ (t + h) - θ t) (t : ℝ) :
    α t = Real.pi - (θ (t + 2 * h) - θ (t + h)) -
      (θ (t + 4 * h) - θ (t + 3 * h)) -
      (θ (t + 6 * h) - θ (t + 5 * h)) := by
  have h0 := hsum t
  have h1 := hsum (t + h)
  have h2 := hsum (t + 2 * h)
  have h3 := hsum (t + 3 * h)
  have h4 := hsum (t + 4 * h)
  have h5 := hsum (t + 5 * h)
  have h6 := hsum (t + 6 * h)
  rw [show t + h + h = t + 2 * h by ring] at h1
  rw [show t + 2 * h + h = t + 3 * h by ring] at h2
  rw [show t + 3 * h + h = t + 4 * h by ring] at h3
  rw [show t + 4 * h + h = t + 5 * h by ring] at h4
  rw [show t + 5 * h + h = t + 6 * h by ring] at h5
  rw [show t + 6 * h + h = t + 7 * h by ring, ha, hturn] at h6
  linarith

/-- The pointwise sum of seven consecutive contact angles is one half-turn. -/
theorem seven_contact_angle_sum {α θ : ℝ → ℝ} {h : ℝ}
    (ha : Function.Periodic α (7 * h))
    (hturn : ∀ t, θ (t + 7 * h) = θ t + 2 * Real.pi)
    (hsum : ∀ t, α t + α (t + h) = θ (t + h) - θ t) (t : ℝ) :
    ∑ i : Fin 7, α (t + (i.val : ℝ) * h) = Real.pi := by
  have h0 := hsum t
  have h1 := hsum (t + h)
  have h2 := hsum (t + 2 * h)
  have h3 := hsum (t + 3 * h)
  have h4 := hsum (t + 4 * h)
  have h5 := hsum (t + 5 * h)
  have h6 := hsum (t + 6 * h)
  rw [show t + h + h = t + 2 * h by ring] at h1
  rw [show t + 2 * h + h = t + 3 * h by ring] at h2
  rw [show t + 3 * h + h = t + 4 * h by ring] at h3
  rw [show t + 4 * h + h = t + 5 * h by ring] at h4
  rw [show t + 5 * h + h = t + 6 * h by ring] at h5
  rw [show t + 6 * h + h = t + 7 * h by ring, ha, hturn] at h6
  simp only [Fin.sum_univ_succ]
  norm_num only [Fin.val_zero, Fin.val_succ, Nat.cast_zero, Nat.cast_add,
    Nat.cast_one, zero_mul, add_zero, zero_add, one_mul] at *
  norm_num at *
  linarith

/-- Solving the odd-cycle system gives the regularity of the contact angle
from the chord lift, without differentiating an initially merely defined angle. -/
theorem contDiff_seven_contact_angle {α θ : ℝ → ℝ} {h : ℝ} {k : WithTop ℕ∞}
    (ha : Function.Periodic α (7 * h))
    (hturn : ∀ t, θ (t + 7 * h) = θ t + 2 * Real.pi)
    (hsum : ∀ t, α t + α (t + h) = θ (t + h) - θ t)
    (hθ : ContDiff ℝ k θ) : ContDiff ℝ k α := by
  have he : α = fun t => Real.pi - (θ (t + 2 * h) - θ (t + h)) -
      (θ (t + 4 * h) - θ (t + 3 * h)) -
      (θ (t + 6 * h) - θ (t + 5 * h)) :=
    funext (seven_contact_angle_eq ha hturn hsum)
  rw [he]
  fun_prop

/-- Differentiation of consecutive angle sums gives the contact-angle chain
with the exact scale `k` of the chord angular velocity. -/
theorem contact_angle_chain {α θ : ℝ → ℝ} {h k : ℝ}
    (ha : Differentiable ℝ α) (hθ : Differentiable ℝ θ)
    (hsum : ∀ t, α t + α (t + h) = θ (t + h) - θ t)
    (hspeed : ∀ t, deriv θ t = k * Real.sin (α t)) (t : ℝ) :
    deriv α t + deriv α (t + h) = k * (Real.sin (α (t + h)) - Real.sin (α t)) := by
  have hαshift : HasDerivAt (fun s => α (s + h)) (deriv α (t + h)) t := by
    simpa using (ha (t + h)).hasDerivAt.scomp t ((hasDerivAt_id t).add_const h)
  have hθshift : HasDerivAt (fun s => θ (s + h)) (deriv θ (t + h)) t := by
    simpa using (hθ (t + h)).hasDerivAt.scomp t ((hasDerivAt_id t).add_const h)
  have hleft := (ha t).hasDerivAt.add hαshift
  have hright := hθshift.sub (hθ t).hasDerivAt
  change HasDerivAt (fun s => α s + α (s + h)) _ t at hleft
  rw [show (fun s => α s + α (s + h)) = (fun s => θ (s + h) - θ s)
    from funext hsum] at hleft
  have he := hleft.unique hright
  rw [hspeed, hspeed] at he
  linarith

/-- Explicit seven-angle vector field, retaining the chord-length scale. -/
theorem seven_contact_angle_deriv {α θ : ℝ → ℝ} {h k : ℝ}
    (ha : Function.Periodic α (7 * h))
    (hturn : ∀ t, θ (t + 7 * h) = θ t + 2 * Real.pi)
    (hsum : ∀ t, α t + α (t + h) = θ (t + h) - θ t)
    (hθ : Differentiable ℝ θ)
    (hspeed : ∀ t, deriv θ t = k * Real.sin (α t)) (t : ℝ) :
    HasDerivAt α (k * (Real.sin (α (t + h)) - Real.sin (α (t + 2 * h)) +
      Real.sin (α (t + 3 * h)) - Real.sin (α (t + 4 * h)) +
      Real.sin (α (t + 5 * h)) - Real.sin (α (t + 6 * h)))) t := by
  have hd (j : ℝ) : HasDerivAt (fun s => θ (s + j * h))
      (k * Real.sin (α (t + j * h))) t := by
    simpa [hspeed] using (hθ (t + j * h)).hasDerivAt.scomp t
      ((hasDerivAt_id t).add_const (j * h))
  have hcalc := (((hasDerivAt_const t Real.pi).sub ((hd 2).sub (hd 1))).sub
    ((hd 4).sub (hd 3))).sub ((hd 6).sub (hd 5))
  have he : (fun s => Real.pi - (θ (s + 2 * h) - θ (s + 1 * h)) -
      (θ (s + 4 * h) - θ (s + 3 * h)) -
      (θ (s + 6 * h) - θ (s + 5 * h))) = α := by
    funext s
    simpa using (seven_contact_angle_eq ha hturn hsum s).symm
  change HasDerivAt (fun s => Real.pi - (θ (s + 2 * h) - θ (s + 1 * h)) -
      (θ (s + 4 * h) - θ (s + 3 * h)) -
      (θ (s + 6 * h) - θ (s + 5 * h))) _ t at hcalc
  rw [he] at hcalc
  convert hcalc using 1
  simp only [one_mul]
  ring

end UlamFloating.Seventh
