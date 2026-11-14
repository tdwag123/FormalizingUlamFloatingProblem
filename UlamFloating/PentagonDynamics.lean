import UlamFloating.FiniteCycleEnergy
import UlamFloating.PeriodBound
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# An exact period estimate for the five-angle equation

The field below is the side-length-two pentagon angle equation. This file
proves a period estimate for its solutions. It does not assume that an
arbitrary boundary in the geometric problem has already been lifted to
such an angle solution; that extraction is proved in `PentagonGeometry`.
-/

noncomputable section

namespace UlamFloating

open scoped BigOperators

/-- The five-angle carousel equation, with side length normalized to two.
Indices are cyclic. Subtracting the preceding pair-sine is equivalent to
`sin (x (i+2) + x (i+4)) - sin (x (i+1) + x (i+3))`. -/
def pentagonAngleField (x : EuclideanSpace ℝ (Fin 5)) : EuclideanSpace ℝ (Fin 5) :=
  WithLp.toLp 2 (fun i =>
    Real.sin (x (i + 2) + x (i + 4)) -
      Real.sin (x ((finRotate 5).symm i + 2) + x ((finRotate 5).symm i + 4)))

/-- The coordinate formula with cyclic additions instead of an inverse
successor permutation. -/
theorem pentagonAngleField_apply (x : EuclideanSpace ℝ (Fin 5)) (i : Fin 5) :
    pentagonAngleField x i = Real.sin (x (i + 2) + x (i + 4)) -
      Real.sin (x (i + 1) + x (i + 3)) := by
  fin_cases i <;> rfl

/-- The pentagon angle field is smooth on the whole ambient space. -/
theorem contDiff_pentagonAngleField (n : WithTop ℕ∞) : ContDiff ℝ n pentagonAngleField := by
  apply (contDiff_piLp 2).mpr
  intro i
  change ContDiff ℝ n (fun x : EuclideanSpace ℝ (Fin 5) =>
    Real.sin (x (i + 2) + x (i + 4)) -
      Real.sin (x ((finRotate 5).symm i + 2) + x ((finRotate 5).symm i + 4)))
  fun_prop

/-- The sum of the five angular velocities is zero, without a constraint
on the input angles. -/
theorem pentagonAngleField_sum (x : EuclideanSpace ℝ (Fin 5)) :
    ∑ i, pentagonAngleField x i = 0 := by
  change (∑ i : Fin 5, (Real.sin (x (i + 2) + x (i + 4)) -
    Real.sin (x ((finRotate 5).symm i + 2) + x ((finRotate 5).symm i + 4)))) = 0
  rw [Finset.sum_sub_distrib, Equiv.sum_comp (finRotate 5).symm
    (fun i => Real.sin (x (i + 2) + x (i + 4))), sub_self]

/-- A `C¹` solution of a `C¹` autonomous equation is `C²`, in any real
normed space. No existence or uniqueness theorem is required. -/
theorem contDiff_two_of_deriv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℝ → E} {F : E → E} (hx : ContDiff ℝ 1 x) (hF : ContDiff ℝ 1 F)
    (hode : ∀ t, deriv x t = F (x t)) : ContDiff ℝ 2 x := by
  have hd : ContDiff ℝ 1 (deriv x) := by
    rw [show deriv x = F ∘ x from funext hode]
    exact hF.comp hx
  exact contDiff_succ_iff_deriv.mpr
    ⟨hx.differentiable (by simp), by norm_num, hd⟩

/-- Along a `C¹` solution of the pentagon angle equation, acceleration is
bounded by `2√3` times speed. The bound is global and uses no numerical data. -/
theorem pentagonAngleField_acceleration_bound {x : ℝ → EuclideanSpace ℝ (Fin 5)}
    (hx : ContDiff ℝ 1 x) (hode : ∀ t, deriv x t = pentagonAngleField (x t)) (t : ℝ) :
    ‖deriv (deriv x) t‖ ≤ (2 * Real.sqrt 3) * ‖deriv x t‖ := by
  have hx2 := contDiff_two_of_deriv_eq hx
    (contDiff_pentagonAngleField 1) hode
  have hdx := hx.differentiable (by simp)
  have hv : ContDiff ℝ 1 (deriv x) := hx2.deriv'
  have hddx := hv.differentiable (by simp)
  have hcoord (i : Fin 5) : HasDerivAt (fun s => x s i) (deriv x t i) t :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i).hasFDerivAt.comp_hasDerivAt t
      (hdx t).hasDerivAt
  let w : Fin 5 → ℝ := fun i =>
    Real.cos (x t (i + 2) + x t (i + 4)) * (deriv x t (i + 2) + deriv x t (i + 4))
  have hacc (i : Fin 5) : deriv (deriv x) t i = w i - w ((finRotate 5).symm i) := by
    have hd := (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 5 => ℝ) i).hasFDerivAt.comp_hasDerivAt t
      (hddx t).hasDerivAt
    change HasDerivAt (fun s => deriv x s i) (deriv (deriv x) t i) t at hd
    rw [show (fun s => deriv x s i) = (fun s => pentagonAngleField (x s) i) from
      funext (fun s => congrArg (fun v : EuclideanSpace ℝ (Fin 5) => v i) (hode s))] at hd
    exact hd.unique (((hcoord (i + 2)).add (hcoord (i + 4))).sin.sub
      (((hcoord ((finRotate 5).symm i + 2)).add
        (hcoord ((finRotate 5).symm i + 4))).sin))
  have hsum : ∑ i, deriv x t i = 0 := by rw [hode]; exact pentagonAngleField_sum _
  have he := pentagon_weighted_difference_energy_le (fun i => deriv x t i)
    (fun i => Real.cos (x t (i + 2) + x t (i + 4))) hsum (fun i => Real.cos_sq_le_one _)
  have he' : ‖deriv (deriv x) t‖ ^ 2 ≤ 12 * ‖deriv x t‖ ^ 2 := by
    simpa only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, hacc, w] using he
  have hs : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hcoef : 0 ≤ 2 * Real.sqrt 3 := by positivity
  have hsquare : ((2 * Real.sqrt 3) * ‖deriv x t‖) ^ 2 = 12 * ‖deriv x t‖ ^ 2 := by
    rw [mul_pow, mul_pow, hs]
    ring
  nlinarith [norm_nonneg (deriv (deriv x) t), norm_nonneg (deriv x t),
    mul_nonneg hcoef (norm_nonneg (deriv x t))]

/-- Every positive period of a nonconstant `C¹` solution of the five-angle
equation is at least `π/√3`. This is a certified lower bound, not a claim
of optimality or of period monotonicity. -/
theorem pentagonAngleField_period_ge {x : ℝ → EuclideanSpace ℝ (Fin 5)} {T : ℝ}
    (hx : ContDiff ℝ 1 x) (hp : Function.Periodic x T) (hT : 0 < T)
    (hnc : ¬ ∃ c, ∀ t, x t = c) (hode : ∀ t, deriv x t = pentagonAngleField (x t)) :
    Real.pi / Real.sqrt 3 ≤ T := by
  have hx2 := contDiff_two_of_deriv_eq hx
    (contDiff_pentagonAngleField 1) hode
  have h := period_ge_of_derivative_bound hx2 hp hT
    (by positivity : 0 < 2 * Real.sqrt 3) hnc
    (fun t _ => pentagonAngleField_acceleration_bound hx hode t)
  have heq : 2 * Real.pi / (2 * Real.sqrt 3) = Real.pi / Real.sqrt 3 := by ring
  rwa [heq] at h

/-- The period estimate with an explicit positive time scale. This permits
arbitrary chord lengths without silently normalizing the boundary speed. -/
theorem pentagonAngleField_period_ge_scaled {x : ℝ → EuclideanSpace ℝ (Fin 5)}
    {T k : ℝ} (hx : ContDiff ℝ 1 x) (hp : Function.Periodic x T)
    (hT : 0 < T) (hk : 0 < k) (hnc : ¬ ∃ c, ∀ t, x t = c)
    (hode : ∀ t, deriv x t = k • pentagonAngleField (x t)) :
    Real.pi / Real.sqrt 3 / k ≤ T := by
  let y : ℝ → EuclideanSpace ℝ (Fin 5) := fun s => x (s / k)
  have hy : ContDiff ℝ 1 y := hx.comp (contDiff_id.div_const k)
  have hyp : Function.Periodic y (k * T) := by
    intro s
    dsimp [y]
    rw [show (s + k * T) / k = s / k + T by field_simp]
    exact hp _
  have hync : ¬ ∃ c, ∀ t, y t = c := by
    rintro ⟨c, hc⟩
    apply hnc
    refine ⟨c, fun t => ?_⟩
    simpa only [y, mul_div_cancel_left₀ _ hk.ne'] using hc (k * t)
  have hyode (s : ℝ) : deriv y s = pentagonAngleField (y s) := by
    have hd := (hx.differentiable (by simp) (s / k)).hasDerivAt.scomp s
      ((hasDerivAt_id s).div_const k)
    change HasDerivAt y ((1 / k) • deriv x (s / k)) s at hd
    rw [hd.deriv, hode, smul_smul, one_div_mul_cancel hk.ne', one_smul]
  have h := pentagonAngleField_period_ge hy hyp (mul_pos hk hT) hync hyode
  exact (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using h)

/-- For side length `l`, the five-angle equation has time factor `2/l`.
Its nonconstant periodic solutions have period at least `lπ/(2√3)`. -/
theorem pentagonAngleField_period_ge_of_length {x : ℝ → EuclideanSpace ℝ (Fin 5)}
    {T l : ℝ} (hx : ContDiff ℝ 1 x) (hp : Function.Periodic x T)
    (hT : 0 < T) (hl : 0 < l) (hnc : ¬ ∃ c, ∀ t, x t = c)
    (hode : ∀ t, deriv x t = (2 / l) • pentagonAngleField (x t)) :
    l * Real.pi / (2 * Real.sqrt 3) ≤ T := by
  have h := pentagonAngleField_period_ge_scaled hx hp hT
    (div_pos (by norm_num) hl) hnc hode
  have heq : Real.pi / Real.sqrt 3 / (2 / l) = l * Real.pi / (2 * Real.sqrt 3) := by
    field_simp
  rwa [heq] at h

end UlamFloating
