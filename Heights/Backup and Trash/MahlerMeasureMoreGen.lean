import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.ComputeDegree

namespace Polynomial

variable {R : Type u} [CommSemiring R] (K : Type*) [NormedField K] [Algebra R K]

noncomputable def MahlerMeasure (p : R[X]) := ‖leadingCoeff (map (algebraMap R K) p)‖₊ *
    (((map (algebraMap R K) p).roots).map (fun a ↦ max 1 ‖a‖₊)).prod

@[simp]
theorem mahler_measure_zero : MahlerMeasure K (0 : R[X]) = 0 := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_one : MahlerMeasure K (1 : R[X]) = 1 := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_const (z : R) : MahlerMeasure K (C z) = ‖algebraMap R K z‖₊ := by
  simp [MahlerMeasure]

@[simp]
theorem mahler_measure_X : MahlerMeasure K (X : R[X])= 1 := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_C_mul_X_add_C {z₁ z₀ : R} (h1 : algebraMap R K z₁ ≠ 0) : MahlerMeasure K (C z₁ * X + C z₀) =
    ‖algebraMap R K z₁‖₊ * max 1 ‖(algebraMap R K z₁)⁻¹ * (algebraMap R K z₀)‖₊ := by
  simp [h1, MahlerMeasure, leadingCoeff, roots_C_mul_X_add_C]

--------

@[simp]
theorem mahler_measure_degree_eq_one {p : K[X]} (h : degree p = 1) : MahlerMeasure p =
    ‖p.coeff 1‖₊ * max 1 ‖(p.coeff 1)⁻¹ * p.coeff 0‖₊ := by
  rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1 by rw [h])]
  have h1 : p.coeff 1 ≠ 0 := coeff_ne_zero_of_eq_degree h
  simp [mahler_measure_C_mul_X_add_C h1]

@[simp]
theorem mahler_measure_mul (p q : K[X]) : MahlerMeasure (p * q) = MahlerMeasure p * MahlerMeasure q := by
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  simp [MahlerMeasure, mul_assoc, mul_left_comm (Multiset.map (fun x ↦ 1 ⊔ ‖x‖₊) p.roots).prod _ _,
    roots_mul (mul_ne_zero hp hq)]

end Polynomial

--#min_imports
