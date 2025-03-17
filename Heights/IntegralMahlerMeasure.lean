import Mathlib
import Heights.ofFn

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
  field_simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_X : (X : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_monomial (n : ℕ) (z : ℂ) : (monomial n z).logMahlerMeasure = log ‖z‖  := by
  field_simp [logMahlerMeasure]

noncomputable def MahlerMeasure (p : ℂ[X]) := if p ≠ 0 then  exp (p.logMahlerMeasure) else 0

theorem MahlerMeasure_def (p : ℂ[X]) : p.MahlerMeasure = if p ≠ 0 then
    exp ((2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖(fun z : ℂ ↦ p.eval z) (circleMap 0 1 x)‖)
    else 0 := rfl

theorem logMahlerMeasure_eq_log_MahlerMeasure {p : ℂ[X]} (h_p : p ≠ 0) :
    p.logMahlerMeasure = log p.MahlerMeasure := by simp [logMahlerMeasure, MahlerMeasure, h_p]

@[simp]
theorem MahlerMeasure_zero : (0 : ℂ[X]).MahlerMeasure = 0 := by simp [MahlerMeasure]

@[simp]
theorem MahlerMeasure_one : (1 : ℂ[X]).MahlerMeasure = 1 :=by simp [MahlerMeasure]

@[simp]
theorem MahlerMeasure_const (z : ℂ) : (C z).MahlerMeasure = ‖z‖ := by
  simp only [MahlerMeasure, ne_eq, map_eq_zero, logMahlerMeasure_const, ite_not]
  split_ifs with h
  · simp [h]
  · simp [h, exp_log]

@[simp]
theorem MahlerMeasure_prod (p q : ℂ[X]) : (p * q).MahlerMeasure =
    p.MahlerMeasure * q.MahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  rw [← ne_eq] at hp hq
  simp only [MahlerMeasure, ne_eq, mul_eq_zero, hp, hq, or_self, not_false_eq_true, ↓reduceIte,
    logMahlerMeasure, mul_inv_rev, eval_mul, Complex.norm_mul]
  rw [ ← exp_add, ← left_distrib]
  congr
  rw [← intervalIntegral.integral_add]
  --integrabilità prendere da Kebekus
  /- conv => enter [1,1,2,1]; ext x; rw [log_mul (by
    simp [circleMap]
    sorry)]; -/
  have : IntervalIntegrable (fun x ↦ log x) MeasureTheory.volume 0 (2 * π) := by
    exact intervalIntegral.intervalIntegrable_log'
  have : IntervalIntegrable (fun x ↦ log (‖x‖)) MeasureTheory.volume 0 (2 * π) := by
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
    Pi.sup_apply, Pi.zero_apply]
  rw [exp_add, exp_log (norm_pos_iff.mpr <| leadingCoeff_ne_zero.mpr hp)]
  simp only [exp_multiset_sum, Multiset.map_map, Function.comp_apply, mul_eq_mul_left_iff,
    norm_eq_zero, leadingCoeff_eq_zero, hp, or_false]
  apply congr_arg _ <|Multiset.map_congr rfl _
  intro x hx
  rw [Monotone.map_max exp_monotone]
  by_cases h : x = 0; simp [h]
  simp [exp_log <| norm_pos_iff.mpr h]

@[simp]
theorem MahlerMeasure_C_mul_X_add_C {z₁ z₀ : ℂ} (h1 : z₁ ≠ 0) : (C z₁ * X + C z₀).MahlerMeasure =
    ‖z₁‖ * max 1 ‖z₁⁻¹ * z₀‖ := by
  have hpol : C z₁ * X + C z₀ ≠ 0 := by simp [← degree_ne_bot, h1]
  simp only [MahlerMeasure, ne_eq, hpol, not_false_eq_true, ↓reduceIte, logMahlerMeasure_eq,
    roots_C_mul_X_add_C z₀ h1, Pi.sup_apply, Pi.zero_apply, Multiset.map_singleton, norm_neg,
    Complex.norm_mul, norm_inv, Multiset.sum_singleton]
  rw [exp_add, exp_log (norm_pos_iff.mpr <| leadingCoeff_ne_zero.mpr hpol)]
  simp only [Monotone.map_max exp_monotone, exp_zero]
  by_cases hz₀ : z₀ = 0; simp [hz₀]
  congr
  · simp [leadingCoeff, h1]
  · rw [exp_log (mul_pos (inv_pos.mpr <| norm_pos_iff.mpr h1)
      <| norm_pos_iff.mpr hz₀)]

@[simp]
theorem MahlerMeasure_degree_eq_one {p :ℂ[X]} (h : p.degree = 1) : p.MahlerMeasure =
    ‖p.coeff 1‖₊ * max 1 ‖(p.coeff 1)⁻¹ * p.coeff 0‖₊ := by
  rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1 by rw [h])]
  simp [show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h]

@[simp]
theorem logMahlerMeasure_C_mul_X_add_C {z₁ z₀ : ℂ} (h1 : z₁ ≠ 0) : (C z₁ * X + C z₀).logMahlerMeasure =
    log (‖z₁‖ * max 1 ‖z₁⁻¹ * z₀‖) := by
  have hpol : C z₁ * X + C z₀ ≠ 0 := by simp [← degree_ne_bot, h1]
  rw [logMahlerMeasure_eq_log_MahlerMeasure hpol, MahlerMeasure_C_mul_X_add_C h1]

lemma l1 (p : ℂ[X]) : p.MahlerMeasure ≤  ∑ i : Fin p.natDegree, ‖(toFn p.natDegree) p i‖ := by
  by_cases hp : p = 0; simp [hp]
  simp only [MahlerMeasure, ne_eq, hp, not_false_eq_true, ↓reduceIte, logMahlerMeasure, mul_inv_rev,
    eval, circleMap, Complex.ofReal_one, one_mul, zero_add, toFn, AddMonoidHom.coe_mk,
    ZeroHom.coe_mk]
  trans (rexp (log (∑ i : Fin p.natDegree, ‖(toFn p.natDegree) p i‖)))
  gcongr
  rw [← intervalIntegral.integral_const_mul]


  sorry
  sorry
--Finset.sum univ (fun i : Fin p.natDegree ↦ ‖toFn p.natDegree p i‖)

end Polynomial
