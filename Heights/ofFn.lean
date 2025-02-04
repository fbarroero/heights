import Mathlib

namespace Polynomial

variable {R : Type u} [Semiring R] [Dec : DecidableEq R]--[DecidablePred fun x ↦ List.getD x 0 ≠ 0]

open List

def ofFn (n : ℕ) : (Fin n → R) →+ R[X] where
  toFun v := ⟨(List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    simp only [ Pi.add_apply, coeff_ofFinsupp, List.toFinsupp_apply,
      List.getD_eq_getElem?_getD, coeff_add]
    by_cases h : i < n
    · simp [h]
    · simp [getD_getElem?, h]
  map_zero' := by
    ext i
    simp only [Pi.zero_apply, List.ofFn_const, coeff_ofFinsupp,
      List.toFinsupp_apply, coeff_zero, List.getD_eq_getElem?_getD]
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
theorem coeff_eq_zero_of_gt {n i : ℕ} (v : Fin n → R) (hi : n ≤ i) :
    (ofFn n v).coeff i = 0 := by simp [ofFn, hi, Nat.not_lt_of_ge hi]

theorem ofFn_natDegree_lt {n : ℕ} (h : 1 ≤ n) (v : Fin n → R) : (ofFn n v).natDegree < n := by
  rw [Nat.lt_iff_le_pred h, natDegree_le_iff_coeff_eq_zero]
  intro _ _
  apply coeff_eq_zero_of_gt
  omega

--to Mathlib?
/- omit Dec in
lemma foo {n : ℕ} {p : R[X]} (h_deg : p.natDegree < n) : p = ∑ i : Fin n, Polynomial.monomial i (p.coeff i) := by
  have := as_sum_range' p n h_deg
  nth_rewrite 1 [this]
  rw [Finset.sum_range] -/
  /-

  ext i
  simp only [finset_sum_coeff, coeff_monomial, ite_congr rfl (congrArg p.coeff) (congrFun rfl)]
  rw [Finset.sum_ite_zero _ _ (by omega)]
  simp only [Finset.mem_univ, true_and]
  split_ifs with h; rfl
  apply coeff_eq_zero_of_natDegree_lt <| lt_of_lt_of_le h_deg _
  by_contra! hi
  exact (not_exists.mp h) ⟨i, hi⟩ <| rfl -/

theorem ofFn_def {n : ℕ} (v : Fin n → R) : ofFn n v =
    ∑ i : Fin n, Polynomial.monomial i (v i) := by
  by_cases h : n = 0; subst h; simp [ofFn]
  rw [← ne_eq, ← Nat.one_le_iff_ne_zero] at h
  rw [as_sum_range' (ofFn n v) n (ofFn_natDegree_lt h v), Finset.sum_range]
  congr
  simp
  /-


  by_cases h : 1 ≤ n
  rw [foo (ofFn_natDegree_lt h v)]
  congr
  simp
  simp at h
  subst h
  simp [ofFn] -/


end Polynomial

namespace Polynomial

variable {R : Type u} [Semiring R]

open Classical List in
noncomputable def ofFn' (n : ℕ) : (Fin (n + 1) → R) →+ R[X] where
  toFun v := ⟨(List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    simp only [ Pi.add_apply, coeff_ofFinsupp, List.toFinsupp_apply,
      List.getD_eq_getElem?_getD, coeff_add]
    by_cases h : i < (n + 1)
    · simp [h, -ofFn_succ]
    · simp [getD_getElem?, h]
  map_zero' := by
    ext i
    simp only [Pi.zero_apply, List.ofFn_const, coeff_ofFinsupp,
      List.toFinsupp_apply, coeff_zero, List.getD_eq_getElem?_getD]
    by_cases h : i < n + 1
    · simp [-ofFn_succ, h]
    · simp [getD_getElem?, h]

namespace Int
