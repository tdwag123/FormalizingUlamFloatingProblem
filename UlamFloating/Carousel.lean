import UlamFloating.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic.Abel

/-!
# Carousel kinematics

The local laws work in any real inner product space. The successor is an arbitrary
permutation of a finite index type, so the algebra also applies to several cycles.
Geometric applications additionally require one cyclic orbit and convexity.
-/

noncomputable section

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A differentiable edge of constant length is orthogonal to its velocity. -/
theorem inner_edge_velocity_eq_zero {p q : ℝ → E} {u v : E} {t l : ℝ}
    (hp : HasDerivAt p u t) (hq : HasDerivAt q v t)
    (hl : ∀ s, ‖q s - p s‖ = l) :
    ⟪q t - p t, v - u⟫_ℝ = 0 := by
  have hedge : HasDerivAt (fun s => q s - p s) (v - u) t := hq.sub hp
  have hd := HasDerivAt.inner ℝ hedge hedge
  have he : (fun s => ⟪q s - p s, q s - p s⟫_ℝ) = fun _ => l ^ 2 := by
    funext s
    rw [real_inner_self_eq_norm_sq, hl s]
  rw [he] at hd
  have hz := hd.unique (hasDerivAt_const t (l ^ 2))
  have hsymm := real_inner_comm (q t - p t) (v - u)
  linarith

/-- The two local carousel laws force equal endpoint speeds. -/
theorem norm_eq_of_carousel_laws {e u v : E}
    (horth : ⟪e, v - u⟫_ℝ = 0)
    (hparallel : ∃ a : ℝ, u + v = a • e) : ‖u‖ = ‖v‖ := by
  rcases hparallel with ⟨a, ha⟩
  have hz : ⟪u + v, v - u⟫_ℝ = 0 := by
    rw [ha, real_inner_smul_left, horth, mul_zero]
  simp only [inner_add_left, inner_sub_right, real_inner_self_eq_norm_sq] at hz
  rw [real_inner_comm v u] at hz
  nlinarith [norm_nonneg u, norm_nonneg v]

/-- First carousel law, in projection form: the second velocity is the
reflection of the first velocity in the line spanned by the edge. -/
theorem velocity_eq_reflection {e u v : E} (he : e ≠ 0)
    (horth : ⟪e, v - u⟫_ℝ = 0)
    (hparallel : ∃ a : ℝ, u + v = a • e) :
    v = (2 * ⟪e, u⟫_ℝ / ‖e‖ ^ 2) • e - u := by
  rcases hparallel with ⟨a, ha⟩
  have hn : ‖e‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  have hi := congrArg (fun w => ⟪e, w⟫_ℝ) ha
  simp only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at hi
  simp only [inner_sub_right] at horth
  have hc : 2 * ⟪e, u⟫_ℝ / ‖e‖ ^ 2 = a := by
    apply (div_eq_iff hn).2
    linarith
  rw [hc, ← ha]
  abel

/-- A collection of `C¹` moving vertices with equal constant positive edge
lengths and edge-parallel midpoint velocities. The velocity sum is twice the
midpoint velocity, so its use here avoids division by two. -/
structure IsCarousel {ι : Type*} (next : Equiv.Perm ι)
    (p : ι → ℝ → E) (l : ℝ) : Prop where
  length_pos : 0 < l
  contDiff : ∀ i, ContDiff ℝ 1 (p i)
  regular : ∀ i t, deriv (p i) t ≠ 0
  edge_length : ∀ i t, ‖p (next i) t - p i t‖ = l
  midpoint_parallel : ∀ i t, ∃ a : ℝ,
    deriv (p i) t + deriv (p (next i)) t = a • (p (next i) t - p i t)

end UlamFloating
