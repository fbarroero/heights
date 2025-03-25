import Mathlib

namespace Polynomial

variable {R : Type u} [Semiring R]

noncomputable def ofFinToSemiring (n : ℕ) := fun f : Fin (n + 1) → R ↦ ∑ i in Finset.range (n + 1),
  Polynomial.monomial i (f i)

@[simp]
theorem of_fin_to_semiring_zero {n : ℕ} : ofFinToSemiring n (0 : Fin (n + 1) → R) = 0 := by
  simp [ofFinToSemiring]

@[simp]
theorem coeff_eq_val_of_lt {n i : ℕ} (v : Fin (n + 1) → R) (hi : i < n + 1) :
    ((ofFinToSemiring n) v).coeff i = v i := by
  simp only [ofFinToSemiring, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_range, ite_eq_left_iff, not_lt]
  intro
  omega

@[simp]
theorem coeff_eq_zero_of_gt {n i : ℕ} (v : Fin (n + 1) → R) (hi : n + 1 ≤ i) :
    ((ofFinToSemiring n) v).coeff i = 0 := by
  simp only [ofFinToSemiring, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq',
    Finset.mem_range, ite_eq_right_iff]
  intro
  omega

theorem natDegree_le {n : ℕ} (v : Fin (n + 1) → R) : ((ofFinToSemiring n) v).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr <| fun _ a ↦ coeff_eq_zero_of_gt v a

end Polynomial
