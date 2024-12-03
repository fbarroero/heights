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

--change to complex poly
theorem bdd_coeff_of_bdd_roots_and_lead {p : Polynomial ℤ} (h₀ : p ≠ 0) {B : NNReal}
    (h_bdd : (Multiset.map (fun (a : ℂ) ↦ ‖a‖₊) (map coe p).roots).sup ≤ B) :
    ∀ n, ‖(map coe p).coeff n‖₊ ≤ Nat.choose p.natDegree n * B * ‖p.leadingCoeff‖₊ := by --change const on the right accordingly?
  simp_all only [Multiset.sup_le, Multiset.mem_map, mem_roots', IsRoot.def,
    forall_exists_index, and_imp, eq_intCast, Complex.nnnorm_intCast]
  have h_deg_eq : (map coe p).natDegree = p.natDegree := by
    rw [natDegree_map_eq_iff]
    left
    simp_all only [ne_eq, eq_intCast, Int.cast_eq_zero, leadingCoeff_eq_zero, not_false_eq_true]
  have h_lead_eq : (map coe p).leadingCoeff = p.leadingCoeff := by
    simp only [leadingCoeff, coeff_map, eq_intCast, ← h_deg_eq]
  have : p.leadingCoeff ≠ 0  := by exact leadingCoeff_ne_zero.mpr h₀
  intro n
  by_cases h : p.natDegree < n; simp_all only [← h_deg_eq, coeff_map,
    coeff_eq_zero_of_natDegree_lt h, eq_intCast, Int.cast_zero, nnnorm_zero, zero_le]
  simp only [not_lt, ← h_deg_eq] at h
  rw [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgClosed.splits_codomain (map coe p))) h]
  simp only [h_lead_eq, nnnorm_mul, Complex.nnnorm_intCast, nnnorm_pow, nnnorm_neg, nnnorm_one,
    one_pow, mul_one]
  rw [mul_comm]
  simp_all only [ne_eq, eq_intCast, Int.cast_eq_zero, not_false_eq_true, true_or,
    leadingCoeff_eq_zero, nnnorm_pos, mul_le_mul_right]
  simp only [Multiset.esymm]
  rw [Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]
  have := (norm_sum_le (E:=ℂ) ((Multiset.powersetCard (p.natDegree - n) (map coe p).roots).toFinset)) (fun x ↦ ↑(Multiset.count x (Multiset.powersetCard (p.natDegree - n) (map coe p).roots)) * x.prod)
  apply le_trans this
  simp only [norm_mul, Complex.norm_natCast, NNReal.val_eq_coe, NNReal.coe_mul,
    NNReal.coe_natCast]

  have : ∀ x ∈ (Multiset.powersetCard (p.natDegree - n) (map coe p).roots).toFinset, Multiset.count x (Multiset.powersetCard (p.natDegree - n) (map coe p).roots) = Nat.choose p.natDegree n := by
    intro x a
    simp_all only [eq_intCast, ne_eq, Int.cast_eq_zero, leadingCoeff_eq_zero,
      not_false_eq_true, true_or, Complex.norm_eq_abs, norm_mul, RCLike.norm_natCast,
      Multiset.mem_toFinset, Multiset.mem_powersetCard]
    obtain ⟨left, right⟩ := a
    simp_all only [natDegree_map_eq_iff, eq_intCast, ne_eq, Int.cast_eq_zero, leadingCoeff_eq_zero, not_false_eq_true,
      true_or]
    rw [Multiset.count_eq_card.mpr]

    sorry
    intro y hy
    sorry
  sorry


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
