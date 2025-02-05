import Mathlib

namespace Polynomial

open Real


noncomputable def logMahlerMeasure {p : ℂ[X]} := (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖(fun z : ℂ ↦ p.eval z) (circleMap 0 1 x)‖

@[simp]
theorem logMahlerMeasure_one : (1 : ℂ[X]).logMahlerMeasure = 0 :=by simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_const (z : ℂ) : (C z).logMahlerMeasure = log ‖z‖ := by
  simp only [logMahlerMeasure, mul_inv_rev, eval_C, Complex.norm_eq_abs,
    intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  ring_nf
  rw [CommGroupWithZero.mul_inv_cancel π pi_ne_zero]
  simp

@[simp]
theorem logMahlerMeasure_X : (X : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure]

noncomputable def MahlerMeasure (p : ℂ[X]) := if p ≠ 0 then  exp (p.logMahlerMeasure) else 0

@[simp]
theorem mahler_measure_zero : (0 : ℂ[X]).MahlerMeasure = 0 := by simp [MahlerMeasure]

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

  /- conv => enter [1,1,2,1]; ext x; rw [log_mul (by
    simp [circleMap]

    sorry)]; -/
  have : IntervalIntegrable (fun x ↦ log x) MeasureTheory.volume 0 (2 * π) := by
    exact intervalIntegral.intervalIntegrable_log'

  have : IntervalIntegrable (fun x ↦ log (Complex.abs x)) MeasureTheory.volume 0 (2 * π) := by

    sorry
  sorry



  simp [IntervalIntegrable, MeasureTheory.IntegrableOn]
  constructor

  sorry

  sorry
  sorry

theorem logMahlerMeasure_def (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + ((p.roots).map (fun a ↦ max 0 log ‖a‖)).sum := by sorry --use jensen



end Polynomial
