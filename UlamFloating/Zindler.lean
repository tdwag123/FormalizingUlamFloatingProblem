import UlamFloating.Extraction

/-!
# Zindler carousels and rational boundary sampling

A Zindler carousel is a cyclic carousel whose regular closed trajectories have
the same image. This definition does not impose convexity, unit speed, or a
particular phase relation. Rational samples of a strictly convex unit-speed
boundary satisfy the stronger cyclic time-shift and polygon convexity properties.

The construction here is geometric. The physical floating equivalence is a
separate specification in `UlamFloating.FloatingEquivalence`.
-/

namespace UlamFloating

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A cyclic carousel with at least two chairs, all tracing the same regular
closed curve. Self-intersections are allowed in this general definition. -/
structure IsZindlerCarousel {n : ℕ} (p : Fin n → ℝ → E) (l : ℝ) : Prop
    extends IsCarousel (finRotate n) p l where
  two_le : 2 ≤ n
  closed : ∀ i, ∃ P : ℝ, 0 < P ∧ Function.Periodic (p i) P
  same_range : ∀ i j, Set.range (p i) = Set.range (p j)

/-- Every rational sample traverses the entire original curve. -/
theorem range_boundarySamples {F : Type*} (γ : ℝ → F) (P : ℝ) {n : ℕ}
    (i : Fin n) : Set.range (boundarySamples γ P n i) = Set.range γ := by
  ext x
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t + (i.val : ℝ) * (P / n), rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t - (i.val : ℝ) * (P / n), ?_⟩
    simp [boundarySamples, sampledVertex]

/-- A period of the original curve is a period of each sample. -/
theorem periodic_boundarySamples {F : Type*} {γ : ℝ → F} {P : ℝ}
    (hp : Function.Periodic γ P) {n : ℕ} (i : Fin n) :
    Function.Periodic (boundarySamples γ P n i) P := by
  intro t
  simpa [boundarySamples, sampledVertex, add_assoc, add_comm, add_left_comm] using
    hp (t + (i.val : ℝ) * (P / n))

/-- Positive constant chords construct a Zindler carousel on the given boundary.
This includes the exceptional two-chair case; polygon convexity requires `n ≥ 3`. -/
theorem IsUnitSpeedBoundary.boundarySamples_isZindlerCarousel {K : Set Plane}
    {P : ℝ} {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) {n : ℕ}
    (hn : 2 ≤ n) {l : ℝ} (hl : 0 < l) (hc : HasConstantChord γ (P / n) l) :
    IsZindlerCarousel (boundarySamples γ P n) l where
  toIsCarousel := hb.boundarySamples_isCarousel hl hc
  two_le := hn
  closed i := ⟨P, hb.period_pos, periodic_boundarySamples hb.periodic i⟩
  same_range i j := (range_boundarySamples γ P i).trans (range_boundarySamples γ P j).symm

/-- Recover the original chord condition from the first edge, with no convexity
or differential hypothesis. The successor relation handles cyclic indexing. -/
theorem hasConstantChord_of_boundarySamples_edge {F : Type*} [PseudoMetricSpace F]
    {γ : ℝ → F} {P l : ℝ} {n : ℕ} (hn : 0 < n) (hp : Function.Periodic γ P)
    (he : ∀ (i : Fin n) t,
      dist (boundarySamples γ P n (finRotate n i) t) (boundarySamples γ P n i t) = l) :
    HasConstantChord γ (P / n) l := by
  intro t
  have h := he ⟨0, hn⟩ t
  rw [boundarySamples_rotate hp] at h
  simpa [boundarySamples, sampledVertex] using h

/-- On a specified unit-speed strictly convex boundary, the Zindler construction
is equivalent to the positive constant-chord condition. -/
theorem IsUnitSpeedBoundary.isZindlerCarousel_iff {K : Set Plane} {P : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) {n : ℕ} (hn : 2 ≤ n) {l : ℝ} :
    IsZindlerCarousel (boundarySamples γ P n) l ↔
      0 < l ∧ HasConstantChord γ (P / n) l := by
  constructor
  · intro hz
    refine ⟨hz.length_pos, hasConstantChord_of_boundarySamples_edge (by omega) hb.periodic ?_⟩
    intro i t
    simpa only [dist_eq_norm] using hz.edge_length i t
  · rintro ⟨hl, hc⟩
    exact hb.boundarySamples_isZindlerCarousel hn hl hc

/-- A body admits the rational Zindler construction when its boundary samples
form a Zindler carousel. The boundary data supply simplicity and strict convexity. -/
def HasBoundaryZindlerCarousel (K : Set Plane) (n : ℕ) : Prop :=
  ∃ (P : ℝ) (γ : ℝ → Plane) (l : ℝ),
    IsUnitSpeedBoundary K P γ ∧ IsZindlerCarousel (boundarySamples γ P n) l

/-- The existential geometric formulations agree, including at density one half. -/
theorem hasBoundaryZindlerCarousel_iff {K : Set Plane} {n : ℕ} (hn : 2 ≤ n) :
    HasBoundaryZindlerCarousel K n ↔ HasPerimetralChordProperty K (1 / (n : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  constructor
  · rintro ⟨P, γ, l, hb, hz⟩
    obtain ⟨hl, hc⟩ := (hb.isZindlerCarousel_iff hn).mp hz
    refine ⟨div_pos zero_lt_one hn0, (div_lt_one hn0).mpr hn1, P, γ, hb, l, hl, ?_⟩
    convert hc using 1
    ring
  · rintro ⟨_, _, P, γ, hb, l, hl, hc⟩
    refine ⟨P, γ, l, hb, hb.boundarySamples_isZindlerCarousel hn hl ?_⟩
    convert hc using 1
    ring

/-- The constructed carousel is inscribed in the original boundary, strictly
convex in cyclic order, and advances by one chair after time `P / n`. -/
theorem IsUnitSpeedBoundary.zindler_construction {K : Set Plane} {P : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) {n : ℕ} (hn : 3 ≤ n)
    {l : ℝ} (hl : 0 < l) (hc : HasConstantChord γ (P / n) l) :
    IsZindlerCarousel (boundarySamples γ P n) l ∧
      (∀ i, Set.range (boundarySamples γ P n i) = frontier K) ∧
      (∀ t, IsStrictlyConvexPolygon (fun i => boundarySamples γ P n i t)) ∧
      ∀ i t, boundarySamples γ P n (finRotate n i) t =
        boundarySamples γ P n i (t + P / n) := by
  exact ⟨hb.boundarySamples_isZindlerCarousel (by omega) hl hc,
    fun i => (range_boundarySamples γ P i).trans hb.range_eq_frontier,
    hb.boundarySamples_strictlyConvex hn, boundarySamples_rotate hb.periodic⟩

end UlamFloating
