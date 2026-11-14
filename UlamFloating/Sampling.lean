import UlamFloating.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Rational sampling of periodic curves

Natural-number indices deliberately precede a finite cyclic interface. Closure
and all side-length equalities are proved, rather than stored as assumptions.
-/

namespace UlamFloating

variable {E : Type*}

/-- The `i`th vertex obtained by sampling with increment `h`, starting at time `t`. -/
def sampledVertex (γ : ℝ → E) (h t : ℝ) (i : ℕ) : E :=
  γ (t + (i : ℝ) * h)

@[simp] theorem sampledVertex_zero (γ : ℝ → E) (h t : ℝ) :
    sampledVertex γ h t 0 = γ t := by
  simp [sampledVertex]

theorem sampledVertex_succ (γ : ℝ → E) (h t : ℝ) (i : ℕ) :
    sampledVertex γ h t (i + 1) = sampledVertex γ h (t + h) i := by
  unfold sampledVertex
  congr 1
  push_cast
  ring

/-- A rational step of `P / n` closes after `n` samples. -/
theorem sampledVertex_add_period {γ : ℝ → E} {P : ℝ}
    (hp : Function.Periodic γ P) {n : ℕ} (hn : n ≠ 0) (t : ℝ) (i : ℕ) :
    sampledVertex γ (P / n) t (i + n) = sampledVertex γ (P / n) t i := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  unfold sampledVertex
  have he : t + ((i + n : ℕ) : ℝ) * (P / n) = (t + (i : ℝ) * (P / n)) + P := by
    push_cast
    field_simp [hn']
    ring
  rw [he, hp]

/-- Every edge of the sampled polygon has the same prescribed length. -/
theorem HasConstantChord.sampled_edge [PseudoMetricSpace E]
    {γ : ℝ → E} {h l : ℝ} (hc : HasConstantChord γ h l) (t : ℝ) (i : ℕ) :
    dist (sampledVertex γ h t (i + 1)) (sampledVertex γ h t i) = l := by
  unfold sampledVertex
  have he : t + ((i + 1 : ℕ) : ℝ) * h = (t + (i : ℝ) * h) + h := by
    push_cast
    ring
  rw [he]
  exact hc (t + (i : ℝ) * h)

end UlamFloating
