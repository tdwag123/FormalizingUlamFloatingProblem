import Seventh.StrongConcavity
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A peak-width lower bound for variance

A Lipschitz bound forces a positive deviation to persist on both sides of
its peak. Integrating the squared linear lower bounds gives a cubic estimate.
-/

namespace UlamFloating.Seventh

open MeasureTheory Set

theorem integral_linear_sq (d L R : ℝ) :
    (∫ x in (0 : ℝ)..R, (d - L * x) ^ 2) = d ^ 2 * R - d * L * R ^ 2 + L ^ 2 * R ^ 3 / 3 := by
  have hd (x : ℝ) : HasDerivAt
      (fun x : ℝ => d ^ 2 * x - d * L * x ^ 2 + L ^ 2 * x ^ 3 / 3)
      ((d - L * x) ^ 2) x := by
    convert (((hasDerivAt_id x).const_mul (d ^ 2)).sub
      (((hasDerivAt_id x).pow 2).const_mul (d * L))).add
      ((((hasDerivAt_id x).pow 3).const_mul (L ^ 2)).div_const 3) using 1
    simp only [id_eq]
    ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x (_ : x ∈ uIcc 0 R) => hd x)
    ((show Continuous (fun x : ℝ => (d - L * x) ^ 2) by fun_prop).intervalIntegrable _ _)
  simpa using hi

/-- A pointwise Lipschitz estimate gives the integral lower bound on a tent's half. -/
theorem linear_sq_le_integral {g : ℝ → ℝ} {d L R : ℝ}
    (hg : Continuous g) (hR : 0 ≤ R) (hL : 0 ≤ L) (hwidth : L * R ≤ d)
    (hlower : ∀ x ∈ Icc 0 R, d - L * x ≤ g x) :
    d ^ 2 * R - d * L * R ^ 2 + L ^ 2 * R ^ 3 / 3 ≤ ∫ x in (0 : ℝ)..R, (g x) ^ 2 := by
  rw [← integral_linear_sq]
  apply intervalIntegral.integral_mono_on (μ := volume) hR
    ((show Continuous (fun x : ℝ => (d - L * x) ^ 2) by fun_prop).intervalIntegrable _ _)
    ((hg.pow 2).intervalIntegrable _ _)
  intro x hx
  have hnonneg : 0 ≤ d - L * x := by
    have he := mul_le_mul_of_nonneg_left hx.2 hL
    linarith
  exact sq_le_sq₀ hnonneg (hnonneg.trans (hlower x hx)) |>.mpr (hlower x hx)

/-- A periodic Lipschitz function cannot have an arbitrarily narrow positive peak.
The explicit width hypothesis ensures that the two sides fit within one period. -/
theorem peak_cubic_le_variance {P a L : ℝ} {f : ℝ → ℝ} (hP : 0 < P) (hL : 0 < L)
    (hf : Continuous f) (hp : Function.Periodic f P)
    (hlip : ∀ x y, |f y - f x| ≤ L * |y - x|) (t : ℝ)
    (hdev : 0 ≤ f t - a) (hwidth : 2 * (f t - a) ≤ L * P) :
    2 * (f t - a) ^ 3 ≤ 3 * L * P * intervalVariance P f a := by
  let d := f t - a
  let R := d / L
  have hR : 0 ≤ R := div_nonneg hdev hL.le
  have hLR : L * R = d := by dsimp [R]; field_simp
  have hRwidth : 2 * R ≤ P := by nlinarith
  let g : ℝ → ℝ := fun x => (f (t + x) - a) ^ 2
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hgp : Function.Periodic g P := by
    intro x
    dsimp [g]
    rw [← add_assoc, hp (t + x)]
  have hplus := linear_sq_le_integral
    (show Continuous (fun x => f (t + x) - a) by fun_prop) hR hL.le hLR.le
    (fun x hx => show d - L * x ≤ f (t + x) - a by
      have h := hlip t (t + x)
      rw [add_sub_cancel_left, abs_of_nonneg hx.1] at h
      have he := (abs_le.mp h).1
      dsimp [d]
      linarith)
  have hminus := linear_sq_le_integral
    (show Continuous (fun x => f (t - x) - a) by fun_prop) hR hL.le hLR.le
    (fun x hx => show d - L * x ≤ f (t - x) - a by
      have h := hlip t (t - x)
      rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg hx.1] at h
      have he := (abs_le.mp h).1
      dsimp [d]
      linarith)
  have hminus' : d ^ 2 * R - d * L * R ^ 2 + L ^ 2 * R ^ 3 / 3 ≤
      ∫ x in -R..(0 : ℝ), g x := by
    have he : (fun x => (f (t - x) - a) ^ 2) = fun x => g (-x) := by
      ext x; simp [g, sub_eq_add_neg]
    rw [he, intervalIntegral.integral_comp_neg, neg_zero] at hminus
    exact hminus
  have hadd := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hg.intervalIntegrable (-R) 0) (hg.intervalIntegrable 0 R)
  have hmono := intervalIntegral.integral_mono_interval (μ := volume)
    (le_refl (-R)) (by linarith : -R ≤ R) (by linarith : R ≤ -R + P)
    (Filter.Eventually.of_forall (fun x => sq_nonneg (f (t + x) - a)))
    (hg.intervalIntegrable (-R) (-R + P))
  have hperiod := hgp.intervalIntegral_add_eq (-R) 0
  simp only [zero_add] at hperiod
  rw [hperiod] at hmono
  have hmean : (∫ x in (0 : ℝ)..P, g x) = ∫ x in (0 : ℝ)..P, (f x - a) ^ 2 := by
    dsimp [g]
    rw [intervalIntegral.integral_comp_add_left (fun x => (f x - a) ^ 2) t]
    have hq : Function.Periodic (fun x => (f x - a) ^ 2) P := fun x => by
      dsimp
      rw [hp x]
    have he := hq.intervalIntegral_add_eq t 0
    simpa only [add_zero, zero_add] using he
  rw [hmean] at hmono
  change _ ≤ ∫ x in (0 : ℝ)..R, g x at hplus
  have htotal : 2 * (d ^ 2 * R - d * L * R ^ 2 + L ^ 2 * R ^ 3 / 3) ≤
      ∫ x in (0 : ℝ)..P, (f x - a) ^ 2 := by linarith
  have halgebra : 3 * L * (2 * (d ^ 2 * R - d * L * R ^ 2 + L ^ 2 * R ^ 3 / 3)) =
      2 * d ^ 3 := by rw [← hLR]; ring
  have he := mul_le_mul_of_nonneg_left htotal (by positivity : 0 ≤ 3 * L)
  rw [halgebra] at he
  dsimp [intervalVariance]
  have hcancel : 3 * L * P * (P⁻¹ * ∫ x in (0 : ℝ)..P, (f x - a) ^ 2) =
      3 * L * ∫ x in (0 : ℝ)..P, (f x - a) ^ 2 := by field_simp
  rw [hcancel]
  exact he

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

/-- Contact-angle speed is bounded in the original arclength variable. -/
theorem ContactSystem.angle_lipschitz {K : Set Plane} {P h l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l) (hc : HasConstantChord γ h l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P h l o θ α) (x y : ℝ) :
    |α y - α x| ≤ (2 / l) * |y - x| := by
  have hbound (t : ℝ) : ‖deriv α t‖ ≤ 2 / l := by
    rw [Real.norm_eq_abs]
    have he := hs.abs_angle_deriv_le hb hl hc t
    have hm := mul_le_mul_of_nonneg_left (Real.sin_le_one (α t))
      (by positivity : 0 ≤ 2 / l)
    linarith
  have he := (convex_univ : Convex ℝ (univ : Set ℝ)).norm_image_sub_le_of_norm_deriv_le
    (fun t _ => hs.contDiff_angle.differentiable (by simp) t) (fun t _ => hbound t)
    (mem_univ x) (mem_univ y)
  simpa only [Real.norm_eq_abs] using he

/-- A positive deviation of the angle gives the cubic lower bound on variance,
without normalizing the chord length or the period. -/
theorem ContactSystem.peak_cube_le_variance {K : Set Plane} {P l : ℝ} {γ : ℝ → Plane}
    (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α) (t : ℝ)
    (hdev : Real.pi / 7 ≤ α t) :
    l * (α t - Real.pi / 7) ^ 3 ≤ 3 * P * intervalVariance P α (Real.pi / 7) := by
  have hP := hb.period_pos
  have hfreq := (div_le_iff₀ hP).mp (hs.frequency_le_sin hP hl)
  have hsine := sin_pi_div_seven_lt
  have hangle := hs.angle_lt_six_fifths hb hl hc t
  have hwidth : 2 * (α t - Real.pi / 7) ≤ (2 / l) * P := by
    have hlsmall : l < P := by
      have h1 := mul_lt_mul_of_pos_right hsine hP
      nlinarith [Real.pi_gt_d2]
    have hdsmall : α t - Real.pi / 7 < 1 := by linarith [Real.pi_gt_d2]
    have he : l * (α t - Real.pi / 7) < P := by nlinarith
    have he' := mul_le_mul_of_nonneg_left he.le (by positivity : 0 ≤ 2 / l)
    field_simp [hl.ne'] at he' ⊢
    nlinarith
  have hp := peak_cubic_le_variance hP (by positivity : 0 < 2 / l)
    hs.contDiff_angle.continuous hs.periodic_angle (hs.angle_lipschitz hb hl hc) t
    (sub_nonneg.mpr hdev) hwidth
  have he := mul_le_mul_of_nonneg_left hp hl.le
  field_simp [hl.ne'] at he
  nlinarith only [he]

/-- A rational cubic comparison supplies a peak upper bound without cube roots. -/
theorem ContactSystem.angle_lt_of_peak_bound {K : Set Plane} {P l ell U V : ℝ}
    {γ : ℝ → Plane} (hb : IsUnitSpeedBoundary K P γ) (hl : 0 < l)
    (hc : HasConstantChord γ (P / 7) l)
    {o : Orientation ℝ Plane (Fin 2)} {θ α : ℝ → ℝ}
    (hs : ContactSystem γ P (P / 7) l o θ α)
    (hell : 0 < ell) (hfreq : ell ≤ Real.pi * l / P)
    (hU : Real.pi / 7 ≤ U) (hV : intervalVariance P α (Real.pi / 7) ≤ V)
    (hcomp : 3 * Real.pi * V < ell * (U - Real.pi / 7) ^ 3) (t : ℝ) : α t < U := by
  have hP := hb.period_pos
  by_contra hn
  have hUt := le_of_not_gt hn
  have hp := hs.peak_cube_le_variance hb hl hc t (hU.trans hUt)
  have hpow : (U - Real.pi / 7) ^ 3 ≤ (α t - Real.pi / 7) ^ 3 :=
    pow_le_pow_left₀ (sub_nonneg.mpr hU) (by linarith) 3
  have hfreq' := (le_div_iff₀ hb.period_pos).mp hfreq
  have he1 := mul_le_mul_of_nonneg_right hfreq'
    (pow_nonneg (sub_nonneg.mpr (hU.trans hUt)) 3)
  have he2 := mul_le_mul_of_nonneg_left hp Real.pi_pos.le
  have he3 := mul_le_mul_of_nonneg_left hV (by positivity : 0 ≤ 3 * Real.pi * P)
  have he4 := mul_le_mul_of_nonneg_left hpow (mul_nonneg hell.le hb.period_pos.le)
  have he5 := mul_lt_mul_of_pos_left hcomp hb.period_pos
  nlinarith only [he1, he2, he3, he4, he5]

end UlamFloating.Seventh
