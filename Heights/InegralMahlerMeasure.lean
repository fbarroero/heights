import Mathlib

namespace Polynomial

open Real

noncomputable def logMahlerMeasure (p : ℂ[X]) :=
    (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖(fun z : ℂ ↦ p.eval z) (circleMap 0 1 x)‖

theorem logMahlerMeasure_def (p : ℂ[X]) : p.logMahlerMeasure =
    (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖(fun z : ℂ ↦ p.eval z) (circleMap 0 1 x)‖ := rfl

@[simp]
theorem logMahlerMeasure_one : (1 : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_const (z : ℂ) : (C z).logMahlerMeasure = log ‖z‖ := by
  simp only [logMahlerMeasure, mul_inv_rev, eval_C, Complex.norm_eq_abs,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring_nf
  rw [CommGroupWithZero.mul_inv_cancel π pi_ne_zero]
  simp

@[simp]
theorem logMahlerMeasure_X : (X : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_monomial (n : ℕ) (z : ℂ) : (monomial n z).logMahlerMeasure = log ‖z‖  := by
  simp only [logMahlerMeasure, mul_inv_rev, eval_monomial, norm_mul, Complex.norm_eq_abs, norm_pow,
    abs_circleMap_zero, abs_one, one_pow, mul_one, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul]
  ring_nf
  rw [CommGroupWithZero.mul_inv_cancel π pi_ne_zero]
  simp

noncomputable def MahlerMeasure (p : ℂ[X]) := if p ≠ 0 then  exp (p.logMahlerMeasure) else 0

theorem MahlerMeasure_def (p : ℂ[X]) : p.MahlerMeasure = if p ≠ 0 then
    exp ((2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖(fun z : ℂ ↦ p.eval z) (circleMap 0 1 x)‖)
    else 0 := rfl

@[simp]
theorem MahlerMeasure_zero : (0 : ℂ[X]).MahlerMeasure = 0 := by simp [MahlerMeasure]

@[simp]
theorem MahlerMeasure_one : (1 : ℂ[X]).MahlerMeasure = 1 :=by simp [MahlerMeasure]

@[simp]
theorem MahlerMeasure_const (z : ℂ) : (C z).MahlerMeasure = ‖z‖ := by
  simp only [MahlerMeasure, ne_eq, map_eq_zero, logMahlerMeasure_const, Complex.norm_eq_abs,
    ite_not]
  split_ifs with h
  simp [h]
  simp [h, exp_log]


@[simp]
theorem MahlerMeasure_prod (p q : ℂ[X]) : (p * q).MahlerMeasure =
    p.MahlerMeasure * q.MahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  rw [← ne_eq] at hp hq
  simp only [MahlerMeasure, ne_eq, mul_eq_zero, hp, hq, or_self, not_false_eq_true, ↓reduceIte,
    logMahlerMeasure, mul_inv_rev, eval_mul, norm_mul, Complex.norm_eq_abs]
  rw [ ← exp_add, ← left_distrib]
  congr
  rw [← intervalIntegral.integral_add]
  --integrabilità prendere da Kebekus
  /- conv => enter [1,1,2,1]; ext x; rw [log_mul (by
    simp [circleMap]
    sorry)]; -/
  have : IntervalIntegrable (fun x ↦ log x) MeasureTheory.volume 0 (2 * π) := by
    exact intervalIntegral.intervalIntegrable_log'
  have : IntervalIntegrable (fun x ↦ log (Complex.abs x)) MeasureTheory.volume 0 (2 * π) := by
    sorry
  sorry
  simp only [IntervalIntegrable, MeasureTheory.IntegrableOn]
  constructor
--MeasureTheory.integrable_of_norm_sub_le
  sorry
  sorry
  sorry

theorem logMahlerMeasure_eq (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + ((p.roots).map (fun a ↦ max 0 log ‖a‖)).sum := by sorry --use jensen

theorem MahlerMeasure_eq (p : ℂ[X]) : p.MahlerMeasure =
    ‖p.leadingCoeff‖ * ((p.roots).map (fun a ↦ max 1 ‖a‖)).prod := by
  by_cases hp : p = 0; simp [hp]
  simp only [MahlerMeasure, ne_eq, hp, not_false_eq_true, ↓reduceIte, logMahlerMeasure_eq,
    Complex.norm_eq_abs, Pi.sup_apply, Pi.zero_apply]
  rw [exp_add, exp_log (AbsoluteValue.pos Complex.abs <| leadingCoeff_ne_zero.mpr hp)]
  simp only [exp_multiset_sum, Multiset.map_map, Function.comp_apply, mul_eq_mul_left_iff,
    map_eq_zero, leadingCoeff_eq_zero, hp, or_false]
  apply congr_arg _ <|Multiset.map_congr rfl _
  intro x hx
  rw [Monotone.map_max exp_monotone]
  by_cases h : x = 0; simp [h]
  simp [exp_log <| AbsoluteValue.pos Complex.abs h]

@[simp]
theorem MahlerMeasure_C_mul_X_add_C {z₁ z₀ : ℂ} (h1 : z₁ ≠ 0) : (C z₁ * X + C z₀).MahlerMeasure =
    ‖z₁‖ * max 1 ‖z₁⁻¹ * z₀‖ := by
  have hpol : C z₁ * X + C z₀ ≠ 0 := by
    by_contra! h
    apply h1
    rw [ext_iff] at h
    specialize h 1
    simp_all
  simp only [MahlerMeasure, ne_eq, hpol, not_false_eq_true, ↓reduceIte, logMahlerMeasure_eq,
    Complex.norm_eq_abs, roots_C_mul_X_add_C z₀ h1, Pi.sup_apply, Pi.zero_apply,
    Multiset.map_singleton, map_neg_eq_map, AbsoluteValue.map_mul, map_inv₀, Multiset.sum_singleton,
    norm_mul, norm_inv]
  rw [exp_add, exp_log (AbsoluteValue.pos Complex.abs <| leadingCoeff_ne_zero.mpr hpol)]
  simp only [Monotone.map_max exp_monotone, exp_zero]
  by_cases hz₀ : z₀ = 0; simp [hz₀]
  congr
  · simp [leadingCoeff, h1]
  · rw [exp_log (mul_pos (inv_pos.mpr <| AbsoluteValue.pos Complex.abs h1)
      <| AbsoluteValue.pos Complex.abs hz₀)]

@[simp]
theorem MahlerMeasure_degree_eq_one {p :ℂ[X]} (h : p.degree = 1) : p.MahlerMeasure =
    ‖p.coeff 1‖₊ * max 1 ‖(p.coeff 1)⁻¹ * p.coeff 0‖₊ := by
  rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1 by rw [h])]
  simp [show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h]

end Polynomial
