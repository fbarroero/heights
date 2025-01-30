import Mathlib

namespace Polynomial
/- open scoped Classical
noncomputable section -/

variable {R : Type u} [Semiring R] [DecidableEq R]--[DecidablePred fun x ↦ List.getD x 0 ≠ 0]

def ofFn (n : ℕ) : (Fin (n + 1) → R) →+ R[X] where
  toFun v := ⟨(List.ofFn v).toFinsupp⟩
  map_add' x y := by

    ext i
    simp only [List.ofFn_succ, Pi.add_apply, coeff_ofFinsupp, List.toFinsupp_apply,
      List.getD_eq_getElem?_getD, coeff_add]

    sorry
  map_zero' := by
    ext i
    simp only [Pi.zero_apply, List.ofFn_const, coeff_ofFinsupp,
      List.toFinsupp_apply, coeff_zero]
    by_cases h : i < n + 1
    rw [List.getD_eq_getElem]
    sorry
    sorry

    sorry

end Polynomial

namespace Polynomial
open scoped Classical
noncomputable section

variable {R : Type u} [Semiring R]

def ofFn' (n : ℕ) : (Fin (n + 1) → R) →+ R[X] where
  toFun v := ⟨(List.ofFn v).toFinsupp⟩
  map_add' x y := by sorry
  map_zero' := sorry

namespace Int
