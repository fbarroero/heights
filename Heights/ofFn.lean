/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib
/-!
# `Polynomial.ofFn` and `Polynomial.toFn`

In this file we introduce `ofFn` and `toFn`, two functions that associate a polynomial to the vector
of its coefficients and vice versa. We prove some basic lemmas about these functions.

## Main definitions

- `Polynomial.toFn n` associates a polynomial to the vector of its first `n` coefficients.
- `Polynomial.ofFn n` associates a vector of lenght `n` to a polynomial that has the entries of the
  vector as coefficients.

-/

namespace Polynomial

section toFn

variable {R : Type u} [Semiring R]

/-- `toFn n f` is the vector of the first `n` coefficients of the polynomial `f`. -/
def toFn (n : ℕ) : R[X] →+ Fin n → R where
  toFun p := fun i ↦ p.coeff i
  map_add' x y := by
    simp
    rfl
  map_zero' := by
    simp
    rfl

@[simp]
theorem toFn_zero (n : ℕ) : toFn n (0 : R[X]) = 0 := by simp

end toFn
section ofFn

variable {R : Type u} [Semiring R] [Dec : DecidableEq R]

/-- `ofFn n v` is the polynomial whose coefficients are the entries of the vector `v`. -/
def ofFn (n : ℕ) : (Fin n → R) →+ R[X] where
  toFun v := ⟨(List.ofFn v).toFinsupp⟩
  map_add' x y := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [List.getD_getElem?, h]
  map_zero' := by
    ext i
    by_cases h : i < n
    · simp [h]
    · simp [List.getD_getElem?, h]

@[simp]
theorem ofFn_zero (n : ℕ) : ofFn n (0 : Fin n → R) = 0 := by simp

@[simp]
theorem ofFn_zero' (v : Fin 0 → R) : ofFn 0 v = 0 := rfl

lemma ne_zero_of_ofFn_ne_zero {n : ℕ} {v : Fin n → R} (h : ofFn n v ≠ 0) : n ≠ 0 := by
  contrapose! h
  subst h
  simp


/-- If `i < n` the `i`-th coefficient of `ofFn n v` is `v i`. -/
@[simp]
theorem coeff_eq_val_of_lt {n i : ℕ} (v : Fin n → R) (hi : i < n) :
    (ofFn n v).coeff i = v ⟨i, hi⟩ := by
  simp [ofFn, hi]

/-- If `n ≤ i` the `i`-th coefficient of `ofFn n v` is `0`. -/
@[simp]
theorem coeff_eq_zero_of_ge {n i : ℕ} (v : Fin n → R) (hi : n ≤ i) : (ofFn n v).coeff i = 0 := by
  simp [ofFn, hi, Nat.not_lt_of_ge hi]

/-- `ofFn n v` has `natDegree` at most `n`. -/
theorem ofFn_natDegree_lt {n : ℕ} (h : 1 ≤ n) (v : Fin n → R) : (ofFn n v).natDegree < n := by
  rw [Nat.lt_iff_le_pred h, natDegree_le_iff_coeff_eq_zero]
  exact fun _ h ↦ coeff_eq_zero_of_ge _ <| Nat.le_of_pred_lt h

/-- `ofFn n v` has `degree` at most `n`. -/
theorem ofFn_degree_lt {n : ℕ} (v : Fin n → R) : (ofFn n v).degree < n := by
  by_cases h : ofFn n v = 0
  · simp only [h, degree_zero]
    exact Batteries.compareOfLessAndEq_eq_lt.mp rfl
  · exact (natDegree_lt_iff_degree_lt h).mp
      <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr <| ne_zero_of_ofFn_ne_zero h) _

theorem ofFn_sum_monomial {n : ℕ} (v : Fin n → R) : ofFn n v =
    ∑ i : Fin n, Polynomial.monomial i (v i) := by
  by_cases h : n = 0; subst h; simp [ofFn]
  rw [as_sum_range' (ofFn n v) n <| ofFn_natDegree_lt (Nat.one_le_iff_ne_zero.mpr h) v,
    Finset.sum_range]
  congr
  simp

theorem toFn_comp_ofFn_eq_id (n : ℕ) (v : Fin n → R) : toFn n (ofFn n v) = v := by simp [toFn]

/- theorem leftInverse_toFn_ofFn (n : ℕ) : Function.LeftInverse (toFn n) (ofFn (R := R) n) :=
  toFn_comp_ofFn_eq_id n

theorem rightInverse_ofFn_toFn (n : ℕ) : Function.RightInverse (ofFn (R := R) n) (toFn n) :=
  toFn_comp_ofFn_eq_id n

theorem hasLeftInverse_ofFn (n : ℕ) : Function.HasLeftInverse (ofFn (R := R) n) :=
  Exists.intro (toFn n) (leftInverse_toFn_ofFn  n)

theorem hasRightInverse_ofFn (n : ℕ) : Function.HasRightInverse (toFn (R := R) n) :=
  Exists.intro (ofFn n) (leftInverse_toFn_ofFn  n) -/

theorem injective_ofFn (n : ℕ) : Function.Injective (ofFn (R := R) n) :=
  Function.LeftInverse.injective <| toFn_comp_ofFn_eq_id n

theorem surjective_toFn (n : ℕ) : Function.Surjective (toFn (R := R) n) :=
  Function.RightInverse.surjective <| toFn_comp_ofFn_eq_id n

theorem ofFn_comp_toFn_eq_id_of_natDegree_le {n : ℕ} {p : R [X]} (h_deg : p.natDegree < n) :
    ofFn n (toFn n p) = p := by
  ext i
  by_cases h : i < n
  · simp [h, toFn]
  · simp only [ofFn, toFn, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff_ofFinsupp,
    List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, ↓reduceDIte,
    Option.getD_none]
    apply (coeff_eq_zero_of_natDegree_lt _).symm
    omega

end ofFn

#min_imports

/-
section ofFn'

variable {R : Type u} [Semiring R]

open Classical

open List in
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

theorem toFn_comp_ofFn'_eq_id (n : ℕ) (v : Fin n → R) : toFn n (ofFn' n v) = v := by
  simp [toFn, ofFn']

theorem leftInverse_toFn_ofFn' (n : ℕ) : Function.LeftInverse (toFn n) (ofFn' (R := R) n) :=
  toFn_comp_ofFn_eq_id n

theorem rightInverse_ofFn'_toFn (n : ℕ) : Function.RightInverse (ofFn' (R := R) n) (toFn n) :=
  toFn_comp_ofFn_eq_id n

theorem hasLeftInverse_ofFn' (n : ℕ) : Function.HasLeftInverse (ofFn' (R := R) n) :=
  Exists.intro (toFn n) (leftInverse_toFn_ofFn  n)

theorem hasRightInverse_ofFn' (n : ℕ) : Function.HasRightInverse (toFn (R := R) n) :=
  Exists.intro (ofFn' n) (leftInverse_toFn_ofFn  n)

theorem injective_ofFn' (n : ℕ) : Function.Injective (ofFn' (R := R) n) :=
  Function.LeftInverse.injective <| leftInverse_toFn_ofFn' n

theorem ofFn'_comp_toFn_eq_id_of_natDegree_lt {n : ℕ} {p : R [X]} (h_deg : p.natDegree < n) :
    ofFn' n (toFn n p) = p := by
  ext i
  by_cases h : i < n
  · simp [h, toFn, ofFn']
  · simp only [ofFn', toFn, AddMonoidHom.coe_mk, ZeroHom.coe_mk, coeff_ofFinsupp,
    List.toFinsupp_apply, List.getD_eq_getElem?_getD, List.getElem?_ofFn, h, ↓reduceDIte,
    Option.getD_none]
    apply (coeff_eq_zero_of_natDegree_lt _).symm
    omega

end ofFn'

end Polynomial

section withClassical

variable {K : Type u} [Field K] [NumberField K]

open NumberField Polynomial Classical

noncomputable def aaa (n : ℕ) (v : Fin n → K) : K[X] := (ofFn n v)

end withClassical

section withoutClassical

variable {K : Type u} [Field K] [NumberField K]

open NumberField Polynomial

noncomputable def aaaa (n : ℕ) (v : Fin n → K) : K[X] := (ofFn' n v)

end withoutClassical
 -/
