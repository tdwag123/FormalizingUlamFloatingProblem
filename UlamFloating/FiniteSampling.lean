import UlamFloating.Geometry
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Finite cyclic samples of periodic curves

The cyclic indexing identities apply to arbitrary targets. Differentiability
and the carousel laws are added separately, without assuming polygon convexity.
-/

namespace UlamFloating

/-- Rotation of the finite vertex index is the same as shifting time by one
sampling interval, including the wrap from the last vertex to the first. -/
theorem boundarySamples_rotate {E : Type*} {γ : ℝ → E} {P : ℝ}
    (hp : Function.Periodic γ P) {n : ℕ} (i : Fin n) (t : ℝ) :
    boundarySamples γ P n (finRotate n i) t =
      boundarySamples γ P n i (t + P / n) := by
  cases n with
  | zero => exact Fin.elim0 i
  | succ n =>
    by_cases hi : i = Fin.last n
    · subst i
      simp only [finRotate_last, boundarySamples, Fin.val_zero, Fin.val_last,
        sampledVertex_zero]
      rw [← sampledVertex_succ]
      simpa only [zero_add, sampledVertex_zero] using
        (sampledVertex_add_period hp (Nat.succ_ne_zero n) t 0).symm
    · simp only [boundarySamples, coe_finRotate_of_ne_last hi]
      exact sampledVertex_succ γ (P / ((n + 1 : ℕ) : ℝ)) t i.val

/-- The equal-edge law on finite cyclic samples, including the closing edge. -/
theorem HasConstantChord.boundarySamples_edge {E : Type*} [PseudoMetricSpace E]
    {γ : ℝ → E} {P l : ℝ} {n : ℕ} (hc : HasConstantChord γ (P / n) l)
    (hp : Function.Periodic γ P) (i : Fin n) (t : ℝ) :
    dist (boundarySamples γ P n (finRotate n i) t) (boundarySamples γ P n i t) = l := by
  rw [boundarySamples_rotate hp]
  exact hc.shift ((i.val : ℝ) * (P / n)) t

/-- Sampling is a translation of the parameter, so its derivative is the
original derivative at the translated parameter. -/
theorem hasDerivAt_boundarySamples {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} (hγ : Differentiable ℝ γ) (P : ℝ) {n : ℕ} (i : Fin n) (t : ℝ) :
    HasDerivAt (boundarySamples γ P n i)
      (deriv γ (t + (i.val : ℝ) * (P / n))) t := by
  simpa [boundarySamples, sampledVertex] using
    (hγ (t + (i.val : ℝ) * (P / n))).hasDerivAt.scomp t
      ((hasDerivAt_id t).add_const ((i.val : ℝ) * (P / n)))

/-- Derivative formula for finite samples. -/
theorem deriv_boundarySamples {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} (hγ : Differentiable ℝ γ) (P : ℝ) {n : ℕ} (i : Fin n) (t : ℝ) :
    deriv (boundarySamples γ P n i) t = deriv γ (t + (i.val : ℝ) * (P / n)) :=
  (hasDerivAt_boundarySamples hγ P i t).deriv

/-- The derivative at a rotated sample can be evaluated at the next time
on the original sample, even at the cyclic wrap. -/
theorem deriv_boundarySamples_rotate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : ℝ → E} {P : ℝ} (hγ : Differentiable ℝ γ) (hp : Function.Periodic γ P)
    {n : ℕ} (i : Fin n) (t : ℝ) :
    deriv (boundarySamples γ P n (finRotate n i)) t =
      deriv γ (t + P / n + (i.val : ℝ) * (P / n)) := by
  have heq : boundarySamples γ P n (finRotate n i) =
      fun s => boundarySamples γ P n i (s + P / n) :=
    funext (boundarySamples_rotate hp i)
  rw [heq]
  have hd := (hasDerivAt_boundarySamples hγ P i (t + P / n)).scomp t
    ((hasDerivAt_id t).add_const (P / n))
  simpa using hd.deriv

/-- A regular unit-speed boundary has no zero tangent. -/
theorem IsUnitSpeedBoundary.deriv_ne_zero {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (t : ℝ) : deriv γ t ≠ 0 := by
  intro h
  have hs := hb.unit_speed t
  rw [h, norm_zero] at hs
  exact zero_ne_one hs

/-- Each parameter value lies on the frontier of the body. -/
theorem IsUnitSpeedBoundary.mem_frontier {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (t : ℝ) : γ t ∈ frontier K := by
  rw [← hb.range_eq_frontier]
  exact ⟨t, rfl⟩

/-- Each boundary value belongs to the compact body. -/
theorem IsUnitSpeedBoundary.mem {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (t : ℝ) : γ t ∈ K :=
  hb.isCompact.isClosed.frontier_subset (hb.mem_frontier t)

end UlamFloating
