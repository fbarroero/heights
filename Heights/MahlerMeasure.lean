import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.ComputeDegree
import Heights.poly_norm
import Mathlib

namespace Polynomial

noncomputable def MahlerMeasure (p : Polynomial ℂ) := ‖leadingCoeff p‖₊ *
    (Multiset.map (fun (a : ℂ) ↦ max 1 ‖a‖₊) p.roots).prod

--instance : FunLike (FinitePlace K) K ℝ where

@[simp]
theorem MM_zero : MahlerMeasure 0 = 0 := by
  simp only [MahlerMeasure, leadingCoeff_zero, nnnorm_zero, roots_zero, Multiset.map_zero,
    Multiset.prod_zero, mul_one]

@[simp]
theorem MM_const (z : ℂ) : MahlerMeasure (C z) = ‖z‖₊ := by
  simp only [MahlerMeasure, leadingCoeff_C, roots_C, Multiset.map_zero, Multiset.prod_zero, mul_one]

@[simp]
theorem MM_X : MahlerMeasure X = 1 := by
  simp only [MahlerMeasure, monic_X, Monic.leadingCoeff, nnnorm_one, roots_X,
    Multiset.map_singleton, nnnorm_zero, zero_le, sup_of_le_left, Multiset.prod_singleton, mul_one]

@[simp]
theorem MM_linear (z₁ z₀ : ℂ) (h1 : z₁ ≠ 0) : MahlerMeasure (C z₁ * X - C z₀) = ‖z₁‖₊ * max 1 ‖z₀ / z₁‖₊ := by
  simp only [MahlerMeasure, Complex.norm_eq_abs, norm_div]
  have : (C z₁ * X - C z₀).leadingCoeff = z₁ := by
    rw [leadingCoeff]
    simp_all only [ne_eq, natDegree_sub_C, _root_.map_eq_zero, not_false_eq_true, natDegree_mul_X, natDegree_C,
      zero_add, coeff_sub, coeff_mul_X, coeff_C_zero, coeff_C_succ, sub_zero]
  rw [this]
  simp only [mul_eq_mul_left_iff, _root_.map_eq_zero]
  left
  have : C z₁ * X - C z₀ = C z₁ * (X - C (z₀ / z₁)) := by
    rw [mul_sub, ← C_mul, mul_div_cancel₀ z₀ h1]
  have : (C z₁ * X - C z₀).roots = (X - C (z₀ / z₁)).roots := by
    rw [this]
    exact roots_C_mul (X - C (z₀ / z₁)) h1
  simp_all only [ne_eq, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_sub_C, mul_one,
    not_false_eq_true, roots_C_mul, roots_X_sub_C, Multiset.map_singleton, nnnorm_div,
    Multiset.prod_singleton, NNReal.coe_max, NNReal.coe_one, NNReal.coe_div, coe_nnnorm,
    Complex.norm_eq_abs]

theorem MM_2 : MahlerMeasure (X - C 2) = 2 := by
  simp only [MahlerMeasure, leadingCoeff_X_sub_C, nnnorm_one, roots_X_sub_C, Multiset.map_singleton,
    Complex.nnnorm_ofNat, Nat.one_le_ofNat, sup_of_le_right, Multiset.prod_singleton, one_mul]

@[simp]
theorem MM_mul (p q : Polynomial ℂ) : MahlerMeasure (p * q) = MahlerMeasure p * MahlerMeasure q := by
  simp only [MahlerMeasure, leadingCoeff_mul, nnnorm_mul]
  rw [mul_assoc, mul_assoc, mul_eq_mul_left_iff]
  norm_cast
  rw[mul_left_comm (Multiset.map (fun x ↦ 1 ⊔ ‖x‖₊) p.roots).prod
    _ _]
  simp only [mul_eq_mul_left_iff, map_eq_zero, leadingCoeff_eq_zero]
  by_cases hp : p = 0
  · simp only [hp, zero_mul, roots_zero, Multiset.map_zero, Multiset.prod_zero, one_mul,
    nnnorm_eq_zero, leadingCoeff_eq_zero, leadingCoeff_zero, nnnorm_zero, or_true]
  · left
    by_cases hq : q = 0
    · simp only [hq, mul_zero, roots_zero, Multiset.map_zero, Multiset.prod_zero, mul_one,
      leadingCoeff_zero, nnnorm_zero, or_true]
    · left
      rw [roots_mul (mul_ne_zero hp hq)]
      simp only [Multiset.map_add, Multiset.prod_add]

open Classical

theorem Complex.bdd_coeff_of_bdd_roots_and_lead {p : Polynomial ℂ} {B : NNReal}
    (h_bdd : (Multiset.map (fun (a : ℂ) ↦ ‖a‖₊) p.roots).sup ≤ B) (n : ℕ) :
    ‖p.coeff n‖₊ ≤ ‖p.leadingCoeff‖₊ * Nat.choose p.natDegree n * B ^ (p.natDegree - n) :=
  Polynomial.bdd_coeff_of_bdd_roots_and_lead h_bdd n


theorem Kronecker {p : Polynomial ℤ} (h_monic : Monic p) (h_irr : Irreducible p)
    (h_MM : MahlerMeasure (map coe p) = 1) : p = X ∨ ∃ n, p = cyclotomic n ℤ := by
  sorry


--what's below is wrong
theorem Kronecker' {p : Polynomial ℤ} (h_monic : Monic p) (h_irr : Irreducible p)
    (h_MM : MahlerMeasure (map coe p) = 1) : p = X ∨ p = cyclotomic (natDegree p) ℤ := by
  rw [or_iff_not_imp_left]
  intro hp_ne_X
  by_cases h_deg_p : p.natDegree = 0; simp_all only [Monic.natDegree_eq_zero_iff_eq_one,
    natDegree_one, cyclotomic_zero]
  convert_to map coe p = map coe (cyclotomic p.natDegree ℤ)
  · exact ⟨fun a ↦ congrArg (map coe) a, fun a ↦ map_injective coe (RingHom.injective_int coe) a⟩
  simp only [map_cyclotomic]
  refine eq_of_dvd_of_natDegree_le_of_leadingCoeff ?_ ?_ ?_
  refine Splits.dvd_of_roots_le_roots (IsAlgClosed.splits (map coe p)) (map_monic_ne_zero h_monic) ?_

  sorry

  sorry


  sorry

  /- have h_root1 : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I * (1 / p.natDegree))) p.natDegree := by
    rw [Complex.isPrimitiveRoot_iff _ _ h_deg_p]
    by_cases h_deg_p₁ : p.natDegree = 1
    · refine ⟨0, by omega, exists_prop.mpr ⟨(Nat.coprime_zero_left p.natDegree).mpr h_deg_p₁, ?_⟩⟩
      simp only [CharP.cast_eq_zero, h_deg_p₁, Nat.cast_one, div_one, mul_zero, Complex.exp_zero,
        ne_eq, one_ne_zero, not_false_eq_true, div_self, mul_one, Complex.exp_two_pi_mul_I]
    · refine ⟨1, by omega, exists_prop.mpr ⟨Nat.gcd_one_left p.natDegree, ?_⟩⟩
      rw [Nat.cast_one]
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots h_root1]
  rw [Polynomial.eq_prod_roots_of_splits_id (p:=map coe p) (IsAlgClosed.splits (map coe p))] -/



-- https://mathoverflow.net/questions/10911/english-reference-for-a-result-of-kronecker


end Polynomial
