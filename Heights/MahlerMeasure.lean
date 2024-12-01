import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Tactic.ComputeDegree

namespace Polynomial

noncomputable def MahlerMeasure (p : Polynomial ℂ) := ‖leadingCoeff p‖ *
    (Multiset.map (fun (a : ℂ) ↦ max 1 ‖a‖) p.roots).prod

--instance : FunLike (FinitePlace K) K ℝ where

@[simp]
theorem MM_zero : MahlerMeasure 0 = 0 := by
  simp only [MahlerMeasure, leadingCoeff_zero, norm_zero, roots_zero, Complex.norm_eq_abs,
    Multiset.map_zero, Multiset.prod_zero, mul_one]

@[simp]
theorem MM_const (z : ℂ) : MahlerMeasure (C z) = ‖z‖ := by
  simp only [MahlerMeasure, leadingCoeff_C, Complex.norm_eq_abs, roots_C, Multiset.map_zero,
    Multiset.prod_zero, mul_one]

@[simp]
theorem MM_X : MahlerMeasure X = 1 := by
  simp only [MahlerMeasure, monic_X, Monic.leadingCoeff, norm_one, roots_X, Complex.norm_eq_abs,
    Multiset.map_singleton, AbsoluteValue.map_zero, zero_le_one, sup_of_le_left,
    Multiset.prod_singleton, mul_one]

@[simp]
theorem MM_linear (z₁ z₀ : ℂ) (h1 : z₁ ≠ 0) : MahlerMeasure (C z₁ * X - C z₀) = ‖z₁‖ * max 1 ‖z₀ / z₁‖ := by
  simp only [MahlerMeasure, Complex.norm_eq_abs, norm_div]
  have : (C z₁ * X - C z₀).leadingCoeff = z₁ := by
    rw [leadingCoeff]
    simp_all only [ne_eq, natDegree_sub_C, _root_.map_eq_zero, not_false_eq_true, natDegree_mul_X, natDegree_C,
      zero_add, coeff_sub, coeff_mul_X, coeff_C_zero, coeff_C_succ, sub_zero]
  rw [this]
  simp only [mul_eq_mul_left_iff, map_eq_zero]
  left
  have : C z₁ * X - C z₀ = C z₁ * (X - C (z₀ / z₁)) := by
    rw [mul_sub, ← C_mul, mul_div_cancel₀ z₀ h1]
  have : (C z₁ * X - C z₀).roots = (X - C (z₀ / z₁)).roots := by
    rw [this]
    exact roots_C_mul (X - C (z₀ / z₁)) h1
  simp_all only [ne_eq, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_sub_C, mul_one,
    not_false_eq_true, roots_C_mul, roots_X_sub_C, Multiset.map_singleton, map_div₀,
    Multiset.prod_singleton]

theorem MM_2 : MahlerMeasure (X - C 2) = 2 := by
  simp only [MahlerMeasure, Complex.norm_eq_abs]
  have : ((X : ℂ[X]) - C 2).leadingCoeff = 1 := by
    simp only [leadingCoeff_X_sub_C]
  rw [this]
  simp only [AbsoluteValue.map_one, roots_X_sub_C, Multiset.map_singleton, Complex.abs_ofNat,
    Nat.one_le_ofNat, sup_of_le_right, Multiset.prod_singleton, one_mul]

theorem MM_mul (p q : Polynomial ℂ) : MahlerMeasure (p * q) = MahlerMeasure p * MahlerMeasure q := by
  simp only [MahlerMeasure, leadingCoeff_mul, norm_mul, Complex.norm_eq_abs]
  rw [mul_assoc, mul_assoc, mul_left_comm ((Multiset.map (fun x ↦ 1 ⊔ Complex.abs x) p.roots).prod)
    (Complex.abs q.leadingCoeff) _]
  simp only [mul_eq_mul_left_iff, map_eq_zero, leadingCoeff_eq_zero]
  by_cases hp : p = 0
  · simp only [hp, zero_mul, roots_zero, Multiset.map_zero, Multiset.prod_zero, one_mul,
    _root_.map_eq_zero, leadingCoeff_eq_zero, leadingCoeff_zero, AbsoluteValue.map_zero, or_true]
  · left
    by_cases hq : q = 0
    · simp only [hq, mul_zero, roots_zero, Multiset.map_zero, Multiset.prod_zero, mul_one,
      leadingCoeff_zero, AbsoluteValue.map_zero, or_true]
    · left
      rw [roots_mul (mul_ne_zero hp hq)]
      simp only [Multiset.map_add, Multiset.prod_add]

  theorem Kronecker {p : Polynomial ℤ} (h_monic : Monic p) (h_irr : Irreducible p)
    (h_MM : MahlerMeasure (map coe p) = 1) : p = X ∨ ∃ n : ℕ, p = cyclotomic n ℤ := by
  by_cases h : p = X; left; exact h; right
  use natDegree p
  convert_to map coe p = map coe (cyclotomic p.natDegree ℤ)
  refine ⟨fun a ↦ congrArg (map coe) a, fun a ↦ map_injective coe (RingHom.injective_int coe) a⟩

  simp only [map_cyclotomic]
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots]
  sorry
  sorry
  sorry
-- https://mathoverflow.net/questions/10911/english-reference-for-a-result-of-kronecker


end Polynomial
