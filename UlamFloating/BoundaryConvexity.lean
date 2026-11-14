import UlamFloating.BoundaryTangents
import UlamFloating.BoundaryEmbedding
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Cyclic order on a strictly convex boundary

Three distinct frontier points of a strictly convex planar body are not
collinear. Along a simple regular traversal, their oriented area has the sign
of the tangent orientation. These facts recover polygon convexity from the
order of the boundary parameters.
-/

namespace UlamFloating

open Set Filter
open scoped Topology InnerProductSpace

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Three distinct points on the frontier of a closed strictly convex planar
set enclose nonzero oriented area. -/
theorem areaForm_ne_zero_of_mem_frontier {K : Set Plane}
    (hK : StrictConvex ℝ K) (hclosed : IsClosed K)
    (o : Orientation ℝ Plane (Fin 2)) {a b c : Plane}
    (ha : a ∈ frontier K) (hb : b ∈ frontier K) (hc : c ∈ frontier K)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    o.areaForm (b - a) (c - a) ≠ 0 := by
  have ham := hclosed.frontier_subset ha
  have hbm := hclosed.frontier_subset hb
  have hcm := hclosed.frontier_subset hc
  intro hz
  have he : b - a ≠ 0 := sub_ne_zero.mpr hab.symm
  have hn : ‖b - a‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr he)
  have hdecomp := norm_sq_smul_eq_inner_add_area o (b - a) (c - a)
  rw [hz, zero_smul, add_zero] at hdecomp
  let k : ℝ := ⟪b - a, c - a⟫_ℝ / ‖b - a‖ ^ 2
  have hk : c - a = k • (b - a) := by
    calc
      _ = (‖b - a‖ ^ 2)⁻¹ • (‖b - a‖ ^ 2 • (c - a)) := by
        rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
      _ = _ := by rw [hdecomp, smul_smul]; congr 1; dsimp [k]; ring
  obtain ⟨f, hf⟩ := exists_strict_support hK ham ha.2
  have hfa := hf b hbm hab.symm
  have hfc := hf c hcm hac.symm
  have hfk := congrArg f hk
  simp only [map_sub, map_smul, smul_eq_mul] at hfk
  have hkpos : 0 < k := by nlinarith
  obtain ⟨g, hg⟩ := exists_strict_support hK hbm hb.2
  have hga := hg a ham hab
  have hgc := hg c hcm hbc.symm
  have hgk := congrArg g hk
  simp only [map_sub, map_smul, smul_eq_mul] at hgk
  have hklt : k < 1 := by nlinarith
  have hcint := hK ham hbm hab (sub_pos.mpr hklt) hkpos (by ring : 1 - k + k = 1)
  have hrepr : (1 - k) • a + k • b = c := by
    calc
      _ = a + k • (b - a) := by module
      _ = c := by rw [← hk]; abel
  rw [hrepr] at hcint
  exact hc.2 hcint

/-- A continuous function with no zeros to the right of a zero has positive
sign there if its derivative at that zero is positive. -/
theorem pos_on_Ioo_of_hasDerivAt_pos {f : ℝ → ℝ} {a b d : ℝ}
    (hf : ContinuousOn f (Ioo a b)) (hfa : f a = 0)
    (hd : HasDerivAt f d a) (hdpos : 0 < d)
    (hne : ∀ x ∈ Ioo a b, f x ≠ 0) : ∀ x ∈ Ioo a b, 0 < f x := by
  intro x hx
  have hslope := (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2
  have hnear : ∀ᶠ y in 𝓝[>] a, 0 < slope f a y := hslope.eventually (eventually_gt_nhds hdpos)
  have hbelow : ∀ᶠ y in 𝓝[>] a, y < b :=
    nhdsWithin_le_nhds (eventually_lt_nhds (hx.1.trans hx.2))
  have habove : ∀ᶠ y in 𝓝[>] a, a < y := self_mem_nhdsWithin
  obtain ⟨y, hy, hyslope, hyb⟩ := (habove.and (hnear.and hbelow)).exists
  have hypos : 0 < f y := by
    simp only [slope_def_field, hfa, sub_zero] at hyslope
    exact (div_pos_iff_of_pos_right (sub_pos.mpr hy)).mp hyslope
  by_contra hnot
  have hxneg : f x < 0 := lt_of_le_of_ne (le_of_not_gt hnot) (hne x hx)
  obtain ⟨z, hz, hfz⟩ := isPreconnected_Ioo.intermediate_value hx ⟨hy, hyb⟩ hf
    ⟨hxneg.le, hypos.le⟩
  exact hne z hz hfz

/-- A regular strictly convex boundary admits an orientation in which every
other point of the body lies strictly to the left of each directed tangent. -/
theorem IsUnitSpeedBoundary.exists_positive_orientation {K : Set Plane} {P : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) :
    ∃ o : Orientation ℝ Plane (Fin 2), ∀ t x, x ∈ K → x ≠ γ t →
      0 < o.areaForm (deriv γ t) (x - γ t) := by
  obtain ⟨c, hc⟩ := hb.interior_nonempty
  have hall (o : Orientation ℝ Plane (Fin 2))
      (ho : 0 < o.areaForm (deriv γ 0) (c - γ 0)) :
      ∀ t x, x ∈ K → x ≠ γ t → 0 < o.areaForm (deriv γ t) (x - γ t) := by
    intro t x hx hxt
    have ht := (mul_pos_iff_of_pos_left ho).mp (hb.tangent_area_mul_pos o hc 0 t)
    exact (mul_pos_iff_of_pos_right ht).mp (hb.areaForm_mul_pos o hc t hx hxt)
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  rcases lt_or_gt_of_ne (hb.tangent_area_ne_zero o hc 0) with hneg | hpos
  · refine ⟨-o, hall (-o) ?_⟩
    simpa only [Orientation.areaForm_neg_orientation, LinearMap.neg_apply] using neg_pos.mpr hneg
  · exact ⟨o, hall o hpos⟩

/-- Three boundary parameters in increasing order within one traversal have
positive oriented area, in the positive tangent orientation. -/
theorem IsUnitSpeedBoundary.areaForm_pos_of_ordered {K : Set Plane} {P : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ)
    (o : Orientation ℝ Plane (Fin 2))
    (ho : ∀ t x, x ∈ K → x ≠ γ t → 0 < o.areaForm (deriv γ t) (x - γ t))
    {a b c : ℝ} (hab : a < b) (hbc : b < c) (hca : c < a + P) :
    0 < o.areaForm (γ b - γ a) (γ c - γ a) := by
  have hac : a < c := hab.trans hbc
  have ha : a ∈ Ico a (a + P) := ⟨le_rfl, lt_add_of_pos_right a hb.period_pos⟩
  have hc : c ∈ Ico a (a + P) := ⟨hac.le, hca⟩
  have hγac : γ a ≠ γ c := fun h => hac.ne (hb.injOn_Ico a ha hc h)
  let f : ℝ → ℝ := fun s => o.areaForm (γ s - γ a) (γ c - γ a)
  have hcont : Continuous f :=
    (o.areaForm'.flip (γ c - γ a)).continuous.comp (hb.contDiff.continuous.sub continuous_const)
  have hd : HasDerivAt f (o.areaForm (deriv γ a) (γ c - γ a)) a := by
    exact (o.areaForm'.flip (γ c - γ a)).hasFDerivAt.comp_hasDerivAt a
      (((hb.contDiff.differentiable (by simp)) a).hasDerivAt.sub_const (γ a))
  apply pos_on_Ioo_of_hasDerivAt_pos hcont.continuousOn (by simp [f]) hd
    (ho a (γ c) (hb.mem c) hγac.symm) ?_ b ⟨hab, hbc⟩
  intro s hs
  have hsI : s ∈ Ico a (a + P) := ⟨hs.1.le, hs.2.trans hca⟩
  exact areaForm_ne_zero_of_mem_frontier hb.strictConvex hb.isCompact.isClosed o
    (hb.mem_frontier a) (hb.mem_frontier s) (hb.mem_frontier c)
    (fun h => hs.1.ne (hb.injOn_Ico a ha hsI h)) hγac
    (fun h => hs.2.ne (hb.injOn_Ico a hsI hc h))

/-- Cyclic rotation preserves the oriented area of a triangle. -/
theorem areaForm_sub_cyclic (o : Orientation ℝ Plane (Fin 2)) (a b c : Plane) :
    o.areaForm (b - a) (c - a) = o.areaForm (c - b) (a - b) := by
  simp only [map_sub, LinearMap.sub_apply, o.areaForm_apply_self]
  have hab := o.areaForm_swap a b
  have hac := o.areaForm_swap a c
  have hbc := o.areaForm_swap b c
  linarith

/-- Rational samples of a strictly convex boundary form a strictly convex
polygon in their specified cyclic order. No chord-length hypothesis is needed. -/
theorem IsUnitSpeedBoundary.boundarySamples_strictlyConvex {K : Set Plane} {P : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) {n : ℕ} (hn : 3 ≤ n) (t : ℝ) :
    IsStrictlyConvexPolygon (fun i => boundarySamples γ P n i t) := by
  obtain ⟨o, ho⟩ := hb.exists_positive_orientation
  refine ⟨hn, hb.boundarySamples_injective n t, o, ?_⟩
  intro i j hji hjnext
  cases n with
  | zero => omega
  | succ m =>
    let q : Fin (m + 1) → ℝ := fun k => t + (k.val : ℝ) * (P / (m + 1 : ℕ))
    have hstep : 0 < P / (m + 1 : ℕ) := div_pos hb.period_pos (by positivity)
    have hqmono {u v : Fin (m + 1)} (huv : u.val < v.val) : q u < q v := by
      apply add_lt_add_left
      exact mul_lt_mul_of_pos_right (by exact_mod_cast huv) hstep
    have hqlo (k : Fin (m + 1)) : t ≤ q k :=
      le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg _) hstep.le)
    have hqhi (k : Fin (m + 1)) : q k < t + P := by
      apply add_lt_add_left
      calc
        (k.val : ℝ) * (P / (m + 1 : ℕ)) < (m + 1 : ℕ) * (P / (m + 1 : ℕ)) :=
          mul_lt_mul_of_pos_right (by exact_mod_cast k.isLt) hstep
        _ = P := by field_simp
    have hwithin (u v : Fin (m + 1)) : q v < q u + P := by
      have := hqhi v
      have := hqlo u
      linarith
    change 0 < o.areaForm (γ (q (finRotate (m + 1) i)) - γ (q i)) (γ (q j) - γ (q i))
    by_cases hi : i = Fin.last m
    · subst i
      rw [finRotate_last]
      have hj0 : 0 < j.val := by
        have : j ≠ 0 := by simpa using hjnext
        by_contra h
        apply this
        apply Fin.ext
        simp only [Fin.val_zero]
        omega
      have hjm : j.val < m := by
        have : j.val ≠ m := fun h => hji (Fin.ext h)
        omega
      rw [areaForm_sub_cyclic o (γ (q (Fin.last m))) (γ (q 0)) (γ (q j))]
      exact hb.areaForm_pos_of_ordered o ho (hqmono hj0) (hqmono hjm) (hwithin _ _)
    · have hnext : (finRotate (m + 1) i).val = i.val + 1 := coe_finRotate_of_ne_last hi
      have hinext : q i < q (finRotate (m + 1) i) := hqmono (by omega)
      rcases lt_or_gt_of_ne (show j.val ≠ i.val from fun h => hji (Fin.ext h)) with hjlt | hjgt
      · rw [← areaForm_sub_cyclic o (γ (q j)) (γ (q i)) (γ (q (finRotate (m + 1) i)))]
        exact hb.areaForm_pos_of_ordered o ho (hqmono hjlt) hinext (hwithin _ _)
      · have hjnextval : j.val ≠ (finRotate (m + 1) i).val :=
          fun h => hjnext (Fin.ext h)
        exact hb.areaForm_pos_of_ordered o ho hinext (hqmono (by omega)) (hwithin _ _)

end UlamFloating
