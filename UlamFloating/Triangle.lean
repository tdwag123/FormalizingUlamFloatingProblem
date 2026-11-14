import UlamFloating.FirstMoment

/-!
# Equilateral triangle carousels

For three vertices, the fixed-center statement has a direct inner-product
proof. It does not require identifying the signed centroid with a lamina
centroid. The local algebra is independent of dimension.
-/

namespace UlamFloating

open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Three equal-length edges summing to zero have pairwise inner product
equal to minus half the squared side length. -/
theorem inner_edges_of_equilateral {e f g : E} {l : ℝ}
    (hsum : e + f + g = 0) (he : ‖e‖ = l) (hf : ‖f‖ = l) (hg : ‖g‖ = l) :
    ⟪e, f⟫_ℝ = -(l ^ 2 / 2) ∧ ⟪e, g⟫_ℝ = -(l ^ 2 / 2) ∧
      ⟪f, g⟫_ℝ = -(l ^ 2 / 2) := by
  have h0 := congrArg (fun x => ⟪e, x⟫_ℝ) hsum
  have h1 := congrArg (fun x => ⟪f, x⟫_ℝ) hsum
  have h2 := congrArg (fun x => ⟪g, x⟫_ℝ) hsum
  simp only [inner_add_right, inner_zero_right, real_inner_self_eq_norm_sq, he, hf, hg,
    real_inner_comm e f, real_inner_comm e g, real_inner_comm f g] at h0 h1 h2
  constructor
  · linarith
  constructor <;> linarith

/-- The sum of the three vertex velocities of an equilateral carousel is zero. -/
theorem triangle_velocity_sum_eq_zero {e f g u v w : E} {l : ℝ}
    (hl : 0 < l) (hsum : e + f + g = 0)
    (he : ‖e‖ = l) (hf : ‖f‖ = l) (hg : ‖g‖ = l)
    (horth0 : ⟪e, v - u⟫_ℝ = 0) (horth1 : ⟪f, w - v⟫_ℝ = 0)
    (hmid0 : ∃ a : ℝ, u + v = a • e)
    (hmid1 : ∃ b : ℝ, v + w = b • f)
    (hmid2 : ∃ c : ℝ, w + u = c • g) : u + v + w = 0 := by
  obtain ⟨hef, heg, hfg⟩ := inner_edges_of_equilateral hsum he hf hg
  obtain ⟨a, ha⟩ := hmid0
  obtain ⟨b, hb⟩ := hmid1
  obtain ⟨c, hc⟩ := hmid2
  have hvu : v - u = b • f - c • g := by rw [← hb, ← hc]; abel
  have hwv : w - v = c • g - a • e := by rw [← hc, ← ha]; abel
  rw [hvu, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    hef, heg] at horth0
  rw [hwv, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
    hfg, real_inner_comm e f, hef] at horth1
  have hbc : b = c := by
    have h : (b - c) * l ^ 2 = 0 := by nlinarith [horth0]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hl.ne'))
  have hca : c = a := by
    have h : (c - a) * l ^ 2 = 0 := by nlinarith [horth1]
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right (pow_ne_zero 2 hl.ne'))
  subst b
  subst c
  have hz : (2 : ℝ) • (u + v + w) = 0 := by
    calc
      (2 : ℝ) • (u + v + w) = (u + v) + (v + w) + (w + u) := by module
      _ = a • (e + f + g) := by rw [ha, hb, hc]; module
      _ = 0 := by rw [hsum, smul_zero]
  exact (smul_eq_zero.mp hz).resolve_left (by norm_num)

/-- Squared distance from a vertex to the vertex average, expressed entirely
in terms of the three squared edge lengths. -/
theorem norm_sub_triangle_average_sq (a b c : E) :
    ‖a - (1 / 3 : ℝ) • (a + b + c)‖ ^ 2 =
      (2 * ‖a - b‖ ^ 2 + 2 * ‖a - c‖ ^ 2 - ‖b - c‖ ^ 2) / 9 := by
  simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
    inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
    real_inner_comm b a, real_inner_comm c a, real_inner_comm c b]
  ring

/-- Every vertex of an equilateral triangle is at squared distance `l²/3`
from the vertex average. -/
theorem equilateral_norm_sub_average_sq {a b c : E} {l : ℝ}
    (hab : ‖a - b‖ = l) (hac : ‖a - c‖ = l) (hbc : ‖b - c‖ = l) :
    ‖a - (1 / 3 : ℝ) • (a + b + c)‖ ^ 2 = l ^ 2 / 3 := by
  rw [norm_sub_triangle_average_sq, hab, hac, hbc]
  ring

/-- The vertex sum of a three-vertex carousel is constant in time. -/
theorem IsCarousel.sum_three_eq {p : Fin 3 → ℝ → E} {l : ℝ}
    (hc : IsCarousel (finRotate 3) p l) (s t : ℝ) :
    p 0 s + p 1 s + p 2 s = p 0 t + p 1 t + p 2 t := by
  have hp (i : Fin 3) (t : ℝ) : HasDerivAt (p i) (deriv (p i) t) t :=
    ((hc.contDiff i).differentiable (by simp) t).hasDerivAt
  have h01 : ∀ t, ‖p 1 t - p 0 t‖ = l := by simpa using hc.edge_length 0
  have h12 : ∀ t, ‖p 2 t - p 1 t‖ = l := by simpa using hc.edge_length 1
  have h20 : ∀ t, ‖p 0 t - p 2 t‖ = l := by simpa using hc.edge_length 2
  have hd : ∀ t, HasDerivAt (fun t => p 0 t + p 1 t + p 2 t) 0 t := by
    intro t
    have hz : deriv (p 0) t + deriv (p 1) t + deriv (p 2) t = 0 :=
      triangle_velocity_sum_eq_zero hc.length_pos (by abel) (h01 t) (h12 t) (h20 t)
        (inner_edge_velocity_eq_zero (hp 0 t) (hp 1 t) h01)
        (inner_edge_velocity_eq_zero (hp 1 t) (hp 2 t) h12)
        (by simpa using hc.midpoint_parallel 0 t)
        (by simpa using hc.midpoint_parallel 1 t)
        (by simpa using hc.midpoint_parallel 2 t)
    simpa only [hz] using ((hp 0 t).add (hp 1 t)).add (hp 2 t)
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t

/-- An equilateral triangle carousel has one fixed center and circumradius.
No convexity or lamina-centroid identification is used. -/
theorem IsCarousel.triangle_fixed_center {p : Fin 3 → ℝ → E} {l : ℝ}
    (hc : IsCarousel (finRotate 3) p l) :
    ∃ c : E, ∀ (t : ℝ) (i : Fin 3), ‖p i t - c‖ ^ 2 = l ^ 2 / 3 := by
  refine ⟨(1 / 3 : ℝ) • (p 0 0 + p 1 0 + p 2 0), ?_⟩
  intro t i
  rw [← hc.sum_three_eq t 0]
  have h10 : ‖p 1 t - p 0 t‖ = l := by simpa using hc.edge_length 0 t
  have h21 : ‖p 2 t - p 1 t‖ = l := by simpa using hc.edge_length 1 t
  have h02 : ‖p 0 t - p 2 t‖ = l := by simpa using hc.edge_length 2 t
  have h01 : ‖p 0 t - p 1 t‖ = l := by rwa [norm_sub_rev]
  have h12 : ‖p 1 t - p 2 t‖ = l := by rwa [norm_sub_rev]
  have h20 : ‖p 2 t - p 0 t‖ = l := by rwa [norm_sub_rev]
  fin_cases i
  · exact equilateral_norm_sub_average_sq h01 h02 h12
  · simpa only [add_comm, add_left_comm, add_assoc] using
      equilateral_norm_sub_average_sq h10 h12 h02
  · simpa only [add_comm, add_left_comm, add_assoc] using
      equilateral_norm_sub_average_sq h20 h21 h01

end UlamFloating
