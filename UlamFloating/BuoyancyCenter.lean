import UlamFloating.HydrostaticMeasure
import Mathlib.Tactic.Module

/-!
# The center required in the converse floating argument

A circular cap-moment locus proves equilibrium only after its center has been
identified with the area fraction times the body's first moment. This theorem
expresses that requirement as an exact equivalence for actual waterline caps.
No centering condition is inserted into the definition of a Zindler carousel.
-/

namespace UlamFloating

open scoped InnerProductSpace

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- A circular cap-moment formula gives equilibrium in all directions exactly
when its center agrees with the appropriately scaled body moment. -/
theorem equilibrium_iff_capMoment_center
    {ι : Type*} (o : Orientation ℝ Plane (Fin 2))
    {K : Set Plane} (hK : IsCompact K) (hi : (interior K).Nonempty)
    {ρ r : ℝ} (hρ : 0 < ρ) {c : Plane} {u : ι → Plane} {a : ι → ℝ}
    (hunit : ∀ i, ‖u i‖ = 1)
    (hcover : ∀ v : Plane, ‖v‖ = 1 → ∃ i, u i = v)
    (harea : ∀ i, planarArea (waterlineCap K (u i) (a i)) = ρ * planarArea K)
    (hmoment : ∀ i, laminaFirstMoment (waterlineCap K (u i) (a i)) = c + r • u i) :
    (∀ i, IsEquilibriumCut K ρ (u i) (a i)) ↔ c = ρ • laminaFirstMoment K := by
  have hpos := planarArea_pos hK hi
  have hcpos (i : ι) : planarArea (waterlineCap K (u i) (a i)) ≠ 0 := by
    rw [harea i]
    positivity
  constructor
  · intro he
    have hparallel (v : Plane) (hv : ‖v‖ = 1) :
        ∃ b : ℝ, c - ρ • laminaFirstMoment K = b • v := by
      obtain ⟨i, rfl⟩ := hcover v hv
      obtain ⟨b, hb⟩ := (centroid_normal_iff_firstMoment (hcpos i) (harea i)).mp (he i).2.2
      rw [hmoment i] at hb
      refine ⟨b - r, ?_⟩
      calc
        c - ρ • laminaFirstMoment K =
            (c + r • u i - ρ • laminaFirstMoment K) - r • u i := by abel
        _ = (b - r) • u i := by rw [hb, sub_smul]
    let v : Plane := EuclideanSpace.basisFun (Fin 2) ℝ 0
    have hv : ‖v‖ = 1 := by simp [v]
    obtain ⟨b, hb⟩ := hparallel v hv
    obtain ⟨d, hd⟩ := hparallel (o.rightAngleRotation v) (by simpa using hv)
    have heq := congrArg (fun x => ⟪v, x⟫_ℝ) (hb.symm.trans hd)
    dsimp only at heq
    have horth : ⟪v, o.rightAngleRotation v⟫_ℝ = 0 := by simp
    simp only [real_inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow,
      mul_one, horth, mul_zero] at heq
    apply sub_eq_zero.mp
    simpa only [heq, zero_smul] using hb
  · intro hcenter i
    refine ⟨hunit i, harea i, ?_⟩
    apply (centroid_normal_iff_firstMoment (hcpos i) (harea i)).mpr
    refine ⟨r, ?_⟩
    rw [hmoment i, hcenter]
    abel

end UlamFloating
