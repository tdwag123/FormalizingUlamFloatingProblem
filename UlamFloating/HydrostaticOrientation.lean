import UlamFloating.CapContinuity
import UlamFloating.BoundaryEmbedding

/-!
# Consistent orientation of equilibrium waterlines

The floating predicate chooses a waterline independently at each boundary
parameter. A continuous choice of unit normal to those same chords changes
the material density, at most, to its complement. Continuity of the actual
cap area makes that choice global.
-/

namespace UlamFloating

open Set
open scoped InnerProductSpace

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- The only two unit normals to a nonzero planar chord differ by sign. -/
theorem unit_normals_eq_or_neg (o : Orientation ℝ Plane (Fin 2))
    {e u v : Plane} (he : e ≠ 0) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hue : ⟪u, e⟫_ℝ = 0) (hve : ⟪v, e⟫_ℝ = 0) : v = u ∨ v = -u := by
  have hdec := norm_sq_smul_eq_inner_add_area o u e
  rw [hu, one_pow, one_smul, hue, zero_smul, zero_add] at hdec
  have hcoef : o.areaForm u e ≠ 0 := by
    intro hz
    exact he (by simpa [hz] using hdec)
  have hz := congrArg (fun x => ⟪v, x⟫_ℝ) hdec
  dsimp only at hz
  rw [hve, real_inner_smul_right, o.inner_rightAngleRotation_right,
    o.areaForm_swap v u, neg_neg] at hz
  have harea : o.areaForm u v = 0 := (mul_eq_zero.mp hz.symm).resolve_left hcoef
  have hdecv := norm_sq_smul_eq_inner_add_area o u v
  rw [hu, one_pow, one_smul, harea, zero_smul, add_zero] at hdecv
  have hn := congrArg norm hdecv
  rw [hv, norm_smul, Real.norm_eq_abs, hu, mul_one] at hn
  have hc : ⟪u, v⟫_ℝ = 1 ∨ ⟪u, v⟫_ℝ = -1 := by
    rcases le_or_gt 0 ⟪u, v⟫_ℝ with h | h
    · exact Or.inl (by rw [abs_of_nonneg h] at hn; exact hn.symm)
    · exact Or.inr (by rw [abs_of_neg h] at hn; linarith)
  rcases hc with hc | hc
  · exact Or.inl (by simpa [hc] using hdecv)
  · exact Or.inr (by simpa [hc] using hdecv)

/-- A continuous real function taking only two values is constant. -/
theorem continuous_eq_of_two_values {f : ℝ → ℝ} (hf : Continuous f) {a b : ℝ}
    (hvalues : ∀ t, f t = a ∨ f t = b) (s t : ℝ) : f s = f t := by
  have hnot (s t : ℝ) (hlt : f s < f t) : False := by
    obtain ⟨x, hx⟩ := intermediate_value_univ s t hf
      (show (f s + f t) / 2 ∈ Icc (f s) (f t) by constructor <;> linarith)
    rcases hvalues s with hs | hs <;> rcases hvalues t with ht | ht <;>
      rcases hvalues x with hxt | hxt <;> linarith
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hnot s t hlt
  · exact hnot t s hlt

/-- Any chosen orientation of the same chord is an equilibrium cut at the original
material density or its complement. -/
theorem IsEquilibriumCut.of_same_chord
    (o : Orientation ℝ Plane (Fin 2)) {K : Set Plane} (hK : IsCompact K)
    (hi : (interior K).Nonempty) {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1)
    {u v p q : Plane} {a b : ℝ} (he : IsEquilibriumCut K ρ u a)
    (hpq : q ≠ p) (hv : ‖v‖ = 1)
    (hup : ⟪u, p⟫_ℝ = a) (huq : ⟪u, q⟫_ℝ = a)
    (hvp : ⟪v, p⟫_ℝ = b) (hvq : ⟪v, q⟫_ℝ = b) :
    IsEquilibriumCut K ρ v b ∨ IsEquilibriumCut K (1 - ρ) v b := by
  have hue : ⟪u, q - p⟫_ℝ = 0 := by rw [inner_sub_right, huq, hup, sub_self]
  have hve : ⟪v, q - p⟫_ℝ = 0 := by rw [inner_sub_right, hvq, hvp, sub_self]
  rcases unit_normals_eq_or_neg o (sub_ne_zero.mpr hpq) he.1 hv hue hve with h | h
  · subst v
    have hab : b = a := hvp.symm.trans hup
    exact Or.inl (hab ▸ he)
  · subst v
    have hab : b = -a := by rw [inner_neg_left, hup] at hvp; exact hvp.symm
    rw [hab]
    exact Or.inr (he.complement hK hi hρ hρ')

/-- Pointwise orientation choices cannot switch the area density along a continuous family. -/
theorem exists_fixed_density_of_continuous_equilibrium_cuts
    {K : Set Plane} (hK : IsCompact K) (hi : (interior K).Nonempty)
    {ρ : ℝ} (hρ : 0 < ρ) (hρ' : ρ < 1)
    {u : ℝ → Plane} {a : ℝ → ℝ} (hu : Continuous u) (ha : Continuous a)
    (hunit : ∀ t, ‖u t‖ = 1)
    (he : ∀ t, IsEquilibriumCut K ρ (u t) (a t) ∨
      IsEquilibriumCut K (1 - ρ) (u t) (a t)) :
    ∃ d : ℝ, 0 < d ∧ d < 1 ∧ (d = ρ ∨ d = 1 - ρ) ∧
      ∀ t, IsEquilibriumCut K d (u t) (a t) := by
  let A : ℝ → ℝ := fun t => planarArea (waterlineCap K (u t) (a t))
  have hne (t : ℝ) : u t ≠ 0 := by
    intro hz
    have hh := hunit t
    rw [hz, norm_zero] at hh
    norm_num at hh
  have hA : Continuous A := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact ContinuousAt.comp (f := fun s : ℝ => (u s, a s)) (x := t)
      (continuousAt_planarArea_waterlineCap hK (hne t) (a t))
      (hu.prodMk ha).continuousAt
  have hval (t : ℝ) : A t = ρ * planarArea K ∨ A t = (1 - ρ) * planarArea K :=
    (he t).imp (fun h => h.2.1) (fun h => h.2.1)
  have hconst := continuous_eq_of_two_values hA hval
  have hpos := planarArea_pos hK hi
  rcases he 0 with hzero | hzero
  · refine ⟨ρ, hρ, hρ', Or.inl rfl, fun t => ?_⟩
    rcases he t with ht | ht
    · exact ht
    · have hc : ρ = 1 - ρ := by
        have hs := hconst 0 t
        change planarArea (waterlineCap K (u 0) (a 0)) =
          planarArea (waterlineCap K (u t) (a t)) at hs
        rw [hzero.2.1, ht.2.1] at hs
        exact mul_right_cancel₀ hpos.ne' hs
      rwa [← hc] at ht
  · refine ⟨1 - ρ, by linarith, by linarith, Or.inr rfl, fun t => ?_⟩
    rcases he t with ht | ht
    · have hc : 1 - ρ = ρ := by
        have hs := hconst 0 t
        change planarArea (waterlineCap K (u 0) (a 0)) =
          planarArea (waterlineCap K (u t) (a t)) at hs
        rw [hzero.2.1, ht.2.1] at hs
        exact mul_right_cancel₀ hpos.ne' hs
      rwa [hc]
    · exact ht

end UlamFloating
