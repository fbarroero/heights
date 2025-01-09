import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.ComputeDegree

namespace Polynomial

variable {K : Type*} [NormedField K]

noncomputable def MahlerMeasure (p : K[X]) := ‖leadingCoeff p‖₊ *
    ((p.roots).map (fun a ↦ max 1 ‖a‖₊)).prod

@[simp]
theorem mahler_measure_zero : (0 : K[X]).MahlerMeasure = 0 := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_one : (1 : K[X]).MahlerMeasure = 1 := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_const (z : K) : (C z).MahlerMeasure = ‖z‖₊ := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_X : (X : K[X]).MahlerMeasure = 1 := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_C_mul_X_add_C {z₁ z₀ : K} (h1 : z₁ ≠ 0) : (C z₁ * X + C z₀).MahlerMeasure =
    ‖z₁‖₊ * max 1 ‖z₁⁻¹ * z₀‖₊ := by
  simp [h1, MahlerMeasure, leadingCoeff, roots_C_mul_X_add_C z₀ h1]

@[simp]
theorem mahler_measure_degree_eq_one {p : K[X]} (h : degree p = 1) : p.MahlerMeasure =
    ‖p.coeff 1‖₊ * max 1 ‖(p.coeff 1)⁻¹ * p.coeff 0‖₊ := by
  rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1 by rw [h])]
  have h1 : p.coeff 1 ≠ 0 := coeff_ne_zero_of_eq_degree h
  simp [mahler_measure_C_mul_X_add_C h1]

@[simp]
theorem mahler_measure_mul (p q : K[X]) : (p * q).MahlerMeasure = p.MahlerMeasure * q.MahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  simp [MahlerMeasure, mul_assoc, mul_left_comm (Multiset.map (fun x ↦ 1 ⊔ ‖x‖₊) p.roots).prod _ _,
    roots_mul (mul_ne_zero hp hq)]





variable (p : ℤ[X])


#check MahlerMeasure (map (algebraMap ℤ ℂ) p)



end Polynomial

--#min_imports
