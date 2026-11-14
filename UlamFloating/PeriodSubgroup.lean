import Mathlib.Algebra.Ring.Periodic
import Mathlib.GroupTheory.Archimedean
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import UlamFloating.Basic

/-!
# The subgroup of periods and a least positive period

The domain is an additive group and the target is arbitrary. A positive
lower bound on positive periods makes the subgroup cyclic. In particular,
no continuity or differential-equation hypothesis is needed for this step.
-/

namespace UlamFloating

/-- All additive periods of a function, including zero and negative periods. -/
def periodSubgroup {G Y : Type*} [AddGroup G] (f : G → Y) : AddSubgroup G where
  carrier := {T | Function.Periodic f T}
  zero_mem' := fun x => congrArg f (add_zero x)
  add_mem' := fun hp hq => hp.add_period hq
  neg_mem' := fun hp => hp.neg

/-- Membership in the period subgroup is the usual periodicity predicate. -/
@[simp] theorem mem_periodSubgroup {G Y : Type*} [AddGroup G] (f : G → Y) (T : G) :
    T ∈ periodSubgroup f ↔ Function.Periodic f T := Iff.rfl

section Ordered

variable {G Y : Type*} [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
  [Archimedean G] {f : G → Y}

/-- A positive lower bound on all positive periods, together with one
positive period, guarantees existence of a least positive period. -/
theorem exists_least_positive_period_of_lower_bound {P ε : G}
    (hP : 0 < P) (hp : Function.Periodic f P) (hε : 0 < ε)
    (hbound : ∀ T, 0 < T → Function.Periodic f T → ε ≤ T) :
    ∃ T, IsLeast {S | Function.Periodic f S ∧ 0 < S} T := by
  have hbot : periodSubgroup f ≠ ⊥ := by
    intro heq
    have hmem : P ∈ periodSubgroup f := hp
    rw [heq] at hmem
    exact hP.ne' (by simpa only [AddSubgroup.mem_bot] using hmem)
  apply AddSubgroup.exists_isLeast_pos hbot hε
  apply Set.disjoint_left.mpr
  intro T hT hmem
  exact (not_lt_of_ge (hbound T hmem.1 hT)) hmem.2

/-- A least positive period generates the entire subgroup of periods. -/
theorem periodSubgroup_eq_zmultiples_of_isLeast {T : G}
    (hT : IsLeast {S | Function.Periodic f S ∧ 0 < S} T) :
    periodSubgroup f = AddSubgroup.zmultiples T := by
  rw [AddSubgroup.zmultiples_eq_closure]
  exact AddSubgroup.cyclic_of_min hT

/-- Every period is an integer multiple of the least positive period,
and every such integer multiple is a period. -/
theorem periodic_iff_zsmul_of_isLeast {T : G}
    (hT : IsLeast {S | Function.Periodic f S ∧ 0 < S} T) (S : G) :
    Function.Periodic f S ↔ ∃ k : ℤ, S = k • T := by
  change S ∈ periodSubgroup f ↔ _
  rw [periodSubgroup_eq_zmultiples_of_isLeast hT, AddSubgroup.mem_zmultiples_iff]
  simp only [eq_comm]

end Ordered

/-- A positive real period is a positive natural-number multiple of the
least positive period. This uses no regularity assumption on the function. -/
theorem periodic_pos_iff_nat_mul_of_isLeast {Y : Type*} {f : ℝ → Y} {T P : ℝ}
    (hT : IsLeast {S | Function.Periodic f S ∧ 0 < S} T) (hP : 0 < P) :
    Function.Periodic f P ↔ ∃ m : ℕ, 0 < m ∧ P = (m : ℝ) * T := by
  constructor
  · intro hp
    obtain ⟨k, hk⟩ := (periodic_iff_zsmul_of_isLeast hT P).mp hp
    rw [zsmul_eq_mul] at hk
    have hkpos : (0 : ℝ) < k := by
      rw [hk] at hP
      exact (mul_pos_iff_of_pos_right hT.1.2).mp hP
    have hkpos' : (0 : ℤ) < k := by exact_mod_cast hkpos
    lift k to ℕ using hkpos'.le
    exact ⟨k, by exact_mod_cast hkpos', by simpa only [Int.cast_natCast] using hk⟩
  · rintro ⟨m, _, rfl⟩
    exact hT.1.1.nat_mul m

end UlamFloating
