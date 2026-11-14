import UlamFloating.FiniteSampling
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Order.IntermediateValue

/-!
# Supporting lines and directed boundary tangents

Strict convexity gives a strictly supporting functional at each boundary point.
Fermat's theorem makes that functional vanish on the tangent. In dimension two,
the oriented area between an interior displacement and the tangent is nonzero;
its sign is constant along a regular `C¹` curve. This is the orientation input
needed for the carousel midpoint law.
-/

namespace UlamFloating

open Set
open scoped InnerProductSpace

section Support

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- At a noninterior point of a strictly convex set, a continuous linear
functional strictly separates that point from every other point of the set. -/
theorem exists_strict_support {K : Set E} (hK : StrictConvex ℝ K) {p : E}
    (hp : p ∈ K) (hpint : p ∉ interior K) :
    ∃ f : E →L[ℝ] ℝ, ∀ x ∈ K, x ≠ p → f x < f p := by
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK.convex.interior
    isOpen_interior hpint
  refine ⟨f, ?_⟩
  intro x hx hxp
  have hmid := hK hx hp hxp (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  have h := hf _ hmid
  simp only [map_add, map_smul, smul_eq_mul] at h
  linarith

/-- A supporting functional annihilates the derivative of a differentiable
curve that stays in the strictly convex set. -/
theorem exists_strict_support_tangent {K : Set E} (hK : StrictConvex ℝ K)
    {γ : ℝ → E} (hmem : ∀ s, γ s ∈ K) {t : ℝ} {u : E}
    (hd : HasDerivAt γ u t) (hfront : γ t ∉ interior K) :
    ∃ f : E →L[ℝ] ℝ, f u = 0 ∧ ∀ x ∈ K, x ≠ γ t → f x < f (γ t) := by
  obtain ⟨f, hf⟩ := exists_strict_support hK (hmem t) hfront
  refine ⟨f, ?_, hf⟩
  have hmax : IsLocalMax (fun s => f (γ s)) t := by
    apply Filter.Eventually.of_forall
    intro s
    by_cases hs : γ s = γ t
    · exact le_of_eq (congrArg f hs)
    · exact (hf _ (hmem s) hs).le
  exact hmax.hasDerivAt_eq_zero (f.hasFDerivAt.comp_hasDerivAt t hd)

end Support

section Planar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (Module.finrank ℝ E = 2)]

/-- Orthogonal decomposition using a vector and its oriented right-angle
rotation, with denominators cleared. -/
theorem norm_sq_smul_eq_inner_add_area (o : Orientation ℝ E (Fin 2)) (u x : E) :
    ‖u‖ ^ 2 • x = ⟪u, x⟫_ℝ • u + o.areaForm u x • o.rightAngleRotation u := by
  apply ext_inner_right ℝ
  intro z
  simp only [real_inner_smul_left, inner_add_left, o.inner_rightAngleRotation_left]
  exact (o.inner_mul_inner_add_areaForm_mul_areaForm u x z).symm

/-- Two displacements strictly on the same side of a tangent line have area
coordinates with the same sign. -/
theorem areaForm_mul_pos_of_support (o : Orientation ℝ E (Fin 2))
    (f : E →L[ℝ] ℝ) {u x y : E} (hu : ‖u‖ = 1) (hfu : f u = 0)
    (hx : f x < 0) (hy : f y < 0) : 0 < o.areaForm u x * o.areaForm u y := by
  have hfx := congrArg f (norm_sq_smul_eq_inner_add_area o u x)
  have hfy := congrArg f (norm_sq_smul_eq_inner_add_area o u y)
  simp only [hu, one_pow, one_smul, map_add, map_smul, smul_eq_mul, hfu,
    mul_zero, zero_add] at hfx hfy
  rw [hfx] at hx
  rw [hfy] at hy
  have hpos := mul_pos_of_neg_of_neg hx hy
  have heq : (o.areaForm u x * f (o.rightAngleRotation u)) *
      (o.areaForm u y * f (o.rightAngleRotation u)) =
      (o.areaForm u x * o.areaForm u y) * (f (o.rightAngleRotation u)) ^ 2 := by ring
  rw [heq] at hpos
  by_contra h
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h)
    (sq_nonneg (f (o.rightAngleRotation u))))) hpos

end Planar

/-- A continuous nonvanishing real function on a preconnected space has a
constant sign, expressed without choosing either sign. -/
theorem mul_pos_of_continuous_ne_zero {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    {f : X → ℝ} (hf : Continuous f) (hne : ∀ x, f x ≠ 0) (s t : X) :
    0 < f s * f t := by
  rcases lt_or_gt_of_ne (hne s) with hs | hs
  · have ht : f t < 0 := by
      by_contra ht
      obtain ⟨x, hx⟩ := intermediate_value_univ s t hf ⟨hs.le, le_of_not_gt ht⟩
      exact hne x hx
    exact mul_pos_of_neg_of_neg hs ht
  · have ht : 0 < f t := by
      by_contra ht
      obtain ⟨x, hx⟩ := intermediate_value_univ t s hf ⟨le_of_not_gt ht, hs.le⟩
      exact hne x hx
    exact mul_pos hs ht

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Interior and other boundary displacements lie strictly on the same side
of the tangent line. -/
theorem IsUnitSpeedBoundary.areaForm_mul_pos {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (o : Orientation ℝ Plane (Fin 2))
    {c : Plane} (hc : c ∈ interior K) (t : ℝ) {x : Plane}
    (hx : x ∈ K) (hxt : x ≠ γ t) :
    0 < o.areaForm (deriv γ t) (x - γ t) * o.areaForm (deriv γ t) (c - γ t) := by
  obtain ⟨f, hft, hf⟩ := exists_strict_support_tangent hb.strictConvex hb.mem
    ((hb.contDiff.differentiable (by simp) t).hasDerivAt) (hb.mem_frontier t).2
  have hct : c ≠ γ t := by
    intro h
    exact (hb.mem_frontier t).2 (h ▸ hc)
  apply areaForm_mul_pos_of_support o f (hb.unit_speed t) hft
  · rw [map_sub]
    exact sub_neg.mpr (hf x hx hxt)
  · rw [map_sub]
    exact sub_neg.mpr (hf c (interior_subset hc) hct)

/-- The tangent and the displacement toward an interior point are never
parallel on a regular strictly convex boundary. -/
theorem IsUnitSpeedBoundary.tangent_area_ne_zero {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (o : Orientation ℝ Plane (Fin 2))
    {c : Plane} (hc : c ∈ interior K) (t : ℝ) :
    o.areaForm (deriv γ t) (c - γ t) ≠ 0 := by
  have hct : c ≠ γ t := by
    intro h
    exact (hb.mem_frontier t).2 (h ▸ hc)
  have h := hb.areaForm_mul_pos o hc t (interior_subset hc) hct
  intro hz
  rw [hz, mul_zero] at h
  exact (lt_irrefl 0) h

/-- The orientation of the directed tangent relative to an interior point
is constant along the whole boundary. -/
theorem IsUnitSpeedBoundary.tangent_area_mul_pos {K : Set Plane} {P : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2)) {c : Plane} (hc : c ∈ interior K) (s t : ℝ) :
    0 < o.areaForm (deriv γ s) (c - γ s) * o.areaForm (deriv γ t) (c - γ t) := by
  apply mul_pos_of_continuous_ne_zero
    (f := fun t => o.areaForm (deriv γ t) (c - γ t)) (s := s) (t := t)
  · exact (o.areaForm'.continuous.comp hb.contDiff.continuous_deriv_one).clm_apply
      (continuous_const.sub hb.contDiff.continuous)
  · exact hb.tangent_area_ne_zero o hc

/-- Distinct boundary points have distinct directed unit tangents. Strict
convexity rules out a common supporting line, while the constant orientation
rules out equal directed tangents on opposite supporting lines. -/
theorem IsUnitSpeedBoundary.deriv_ne_of_ne {K : Set Plane} {P : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) {s t : ℝ} (hst : γ s ≠ γ t) :
    deriv γ s ≠ deriv γ t := by
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  obtain ⟨c, hc⟩ := hb.interior_nonempty
  have hs := hb.areaForm_mul_pos o hc s (hb.mem t) hst.symm
  have ht := hb.areaForm_mul_pos o hc t (hb.mem s) hst
  have hsign := hb.tangent_area_mul_pos o hc s t
  intro hvel
  have hflip : o.areaForm (deriv γ t) (γ s - γ t) =
      -o.areaForm (deriv γ s) (γ t - γ s) := by
    rw [← hvel]
    simp only [map_sub]
    ring
  rw [hflip] at ht
  have hprod := mul_pos hs ht
  have heq : (o.areaForm (deriv γ s) (γ t - γ s) *
      o.areaForm (deriv γ s) (c - γ s)) *
      (-o.areaForm (deriv γ s) (γ t - γ s) * o.areaForm (deriv γ t) (c - γ t)) =
      -(o.areaForm (deriv γ s) (γ t - γ s)) ^ 2 *
      (o.areaForm (deriv γ s) (c - γ s) * o.areaForm (deriv γ t) (c - γ t)) := by ring
  rw [heq] at hprod
  exact (not_lt_of_ge (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
    hsign.le)) hprod

end UlamFloating
