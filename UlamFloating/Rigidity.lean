import UlamFloating.Disk
import UlamFloating.Triangle
import UlamFloating.Extraction
import UlamFloating.SquareGeometry
import UlamFloating.BoundaryEmbedding

/-!
# Rigidity at one third and one quarter, and assembly for the remaining targets

Geometric rigidity at one third and one quarter is proved without additional premises. The
conditional assembly lemmas keep all remaining hypotheses explicit. No
specification is used as an axiom.
-/

namespace UlamFloating

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Once the sampled triangle is a carousel, its fixed center and the disk
bridge imply rigidity of the entire body. -/
theorem IsUnitSpeedBoundary.isDisk_of_triangle_carousel
    {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ)
    (hc : IsCarousel (finRotate 3) (boundarySamples γ P 3) l) : IsDisk K := by
  obtain ⟨c, hcenter⟩ := hc.triangle_fixed_center
  apply hb.isDisk_of_norm_sq (c := c)
    (div_pos (sq_pos_of_pos hc.length_pos) (by norm_num : (0 : ℝ) < 3))
  intro t
  simpa [boundarySamples, sampledVertex] using hcenter t 0

/-- The triangle reduction follows from the extraction statement,
without a polygon-to-lamina centroid theorem. -/
theorem triangle_reduction_of_carousel_extraction
    (hex : carouselExtractionStatement) : triangleReductionStatement := by
  intro K P γ l hb hl hchord
  exact (hex 3 (by omega) K P γ l hb hl hchord).1.triangle_fixed_center

/-- The triangle radius reduction is the only hypothesis of this final
assembly step for geometric density one third. -/
theorem third_rigidity_of_triangle_reduction
    (htriangle : triangleReductionStatement) : thirdRigidityStatement := by
  intro K hK
  obtain ⟨_, _, P, γ, hb, l, hl, hchord⟩ := hK
  have hchord' : HasConstantChord γ (P / 3) l := by
    convert hchord using 1
    ring
  obtain ⟨c, hcenter⟩ := htriangle K P γ l hb hl hchord'
  apply hb.isDisk_of_norm_sq (c := c)
    (div_pos (sq_pos_of_pos hl) (by norm_num : (0 : ℝ) < 3))
  intro t
  simpa [boundarySamples, sampledVertex] using hcenter t 0

/-- Assembly of one-third rigidity with convex carousel extraction as an
explicit premise. The unconditional extraction theorem is proved separately. -/
theorem third_rigidity_of_carousel_extraction
    (hex : carouselExtractionStatement) : thirdRigidityStatement :=
  third_rigidity_of_triangle_reduction (triangle_reduction_of_carousel_extraction hex)

/-- Rational samples at one third have one fixed center and squared radius
`l²/3`, using the carousel laws derived from the boundary hypotheses. -/
theorem triangle_reduction : triangleReductionStatement := by
  intro K P γ l hb hl hchord
  exact (hb.boundarySamples_isCarousel hl hchord).triangle_fixed_center

/-- Geometric Ulam rigidity at perimetral density one third. A compact strictly
convex body with a simple `C¹` unit-speed boundary and constant positive chords
at one third of its perimeter is a closed disk of positive radius. -/
theorem third_rigidity : thirdRigidityStatement :=
  third_rigidity_of_triangle_reduction triangle_reduction

/-- The square radius reduction implies geometric rigidity at one quarter. -/
theorem quarter_rigidity_of_square_reduction
    (hsquare : squareReductionStatement) : quarterRigidityStatement := by
  intro K hK
  obtain ⟨_, _, P, γ, hb, l, hl, hchord⟩ := hK
  have hchord' : HasConstantChord γ (P / 4) l := by
    convert hchord using 1
    ring
  obtain ⟨_, c, hcenter⟩ := hsquare K P γ l hb hl hchord'
  apply hb.isDisk_of_norm_sq (c := c)
    (div_pos (sq_pos_of_pos hl) (by norm_num : (0 : ℝ) < 2))
  intro t
  simpa [boundarySamples, sampledVertex] using hcenter t 0

/-- Samples at one quarter form regular squares with one fixed center and
squared circumradius `l²/2`. All hypotheses come from the original boundary. -/
theorem square_reduction : squareReductionStatement := by
  intro K P γ l hb hl hchord
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  have hc : IsCarousel (finRotate 4) (boundarySamples γ P 4) l :=
    hb.boundarySamples_isCarousel hl hchord
  have hinj : ∀ t, Function.Injective (fun i : Fin 4 => boundarySamples γ P 4 i t) :=
    hb.boundarySamples_injective 4
  exact ⟨hc.isRegularPolygon_four o hinj, hc.square_fixed_center o hinj⟩

/-- Geometric Ulam rigidity at perimetral density one quarter, for compact
strictly convex bodies with a simple `C¹` unit-speed boundary. -/
theorem quarter_rigidity : quarterRigidityStatement :=
  quarter_rigidity_of_square_reduction square_reduction

/-- The physical conclusion follows from the independent hydrostatic reduction
and all three geometric rigidity results. Each remains an explicit premise. -/
theorem physical_rigidity_of_geometric
    (hphysical : hydrostaticReductionStatement)
    (hthird : thirdRigidityStatement) (hquarter : quarterRigidityStatement)
    (hfifth : fifthRigidityStatement) : physicalRigidityStatement := by
  intro K σ hσ hfloat
  have hchord := hphysical K σ hfloat
  rcases hσ with rfl | rfl | rfl
  · exact hthird K hchord
  · exact hquarter K hchord
  · exact hfifth K hchord

end UlamFloating
