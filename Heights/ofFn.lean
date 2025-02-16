import Mathlib

namespace Polynomial

variable {R : Type u} [Semiring R] [Dec : DecidableEq R]--[DecidablePred fun x ↦ List.getD x 0 ≠ 0]

open List

def ofFn (n : ℕ) : (Fin n → R) →+ R[X] where
  toFun v := ⟨(List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [getD_getElem?, h]
  map_zero' := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [getD_getElem?, h]

@[simp]
theorem ofFn_zero (n : ℕ) : ofFn n (0 : Fin n → R) = 0 := by simp

@[simp]
theorem coeff_eq_val_of_lt {n i : ℕ} (v : Fin n → R) (hi : i < n) :
    (ofFn n v).coeff i = v ⟨i, hi⟩ := by
  simp [ofFn, hi]

@[simp]
theorem coeff_eq_zero_of_ge {n i : ℕ} (v : Fin n → R) (hi : n ≤ i) :
    (ofFn n v).coeff i = 0 := by simp [ofFn, hi, Nat.not_lt_of_ge hi]

theorem ofFn_natDegree_lt {n : ℕ} (h : 1 ≤ n) (v : Fin n → R) : (ofFn n v).natDegree < n := by
  rw [Nat.lt_iff_le_pred h, natDegree_le_iff_coeff_eq_zero]
  intro _ _
  apply coeff_eq_zero_of_ge
  omega

theorem ofFn_sum_monomial {n : ℕ} (v : Fin n → R) : ofFn n v =
    ∑ i : Fin n, Polynomial.monomial i (v i) := by
  by_cases h : n = 0; subst h; simp [ofFn]
  rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at h
  rw [as_sum_range' (ofFn n v) n (ofFn_natDegree_lt h v), Finset.sum_range]
  congr
  simp

end Polynomial

namespace Polynomial

variable {R : Type u} [Semiring R]

open Classical List

noncomputable def ofFn' (n : ℕ) : (Fin (n) → R) →+ R[X] where
  toFun v := ⟨(List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [getD_getElem?, h]
  map_zero' := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [getD_getElem?, h]

@[simp]
theorem ofFn'_zero (n : ℕ) : ofFn' n (0 : Fin n → R) = 0 := by simp

@[simp]
theorem coeff_eq_val_of_lt' {n i : ℕ} (v : Fin n → R) (hi : i < n) :
    (ofFn n v).coeff i = v ⟨i, hi⟩ := by
  simp [ofFn, hi]

@[simp]
theorem coeff_eq_zero_of_ge' {n i : ℕ} (v : Fin n → R) (hi : n ≤ i) :
    (ofFn n v).coeff i = 0 := by simp [ofFn, hi, Nat.not_lt_of_ge hi]

theorem ofFn_natDegree_lt' {n : ℕ} (h : 1 ≤ n) (v : Fin n → R) : (ofFn n v).natDegree < n := by
  rw [Nat.lt_iff_le_pred h, natDegree_le_iff_coeff_eq_zero]
  intro _ _
  apply coeff_eq_zero_of_ge
  omega

theorem ofFn'_sum_monomial {n : ℕ} (v : Fin n → R) : ofFn n v =
    ∑ i : Fin n, Polynomial.monomial i (v i) := by
  by_cases h : n = 0; subst h; simp [ofFn]
  rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at h
  rw [as_sum_range' (ofFn n v) n (ofFn_natDegree_lt h v), Finset.sum_range]
  congr
  simp

end Polynomial
