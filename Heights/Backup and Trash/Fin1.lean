import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib

namespace Polynomial

variable {R : Type u} [Semiring R]

-- find another place for this? Finsupp
@[simp]
theorem zero_eq : {toFun := fun _ => 0, support := ∅, mem_support_toFun := by simp} =
    (0 : ℕ →₀ R) := rfl

noncomputable def ofFinToSemiring (n : ℕ) : (Fin (n + 1) → R) →+ R[X] where
  toFun v := ⟨let f : ℕ → R := fun i => if h : i < n + 1 then v ⟨i, h⟩ else 0
  {
    toFun := f,
    support := (Set.Finite.subset (t := f.support) (Finset.finite_toSet (Finset.range (n + 1)))
        (by simp_all [f])).toFinset,
    mem_support_toFun := by simp
  }⟩
  map_add' x y := by
    ext m
    simp only [Pi.add_apply, coeff_ofFinsupp, Finsupp.coe_mk, coeff_add]
    split; all_goals simp
  map_zero' := by simp

@[simp]
theorem of_fin_to_semiring_zero {n : ℕ} : ofFinToSemiring n (0 : Fin (n + 1) → R) = 0 := by simp

@[simp]
theorem coeff_eq_val_of_lt {n i : ℕ} (v : Fin (n + 1) → R) (hi : i < n + 1) :
    ((ofFinToSemiring n) v).coeff i = v i := by
  simp only [ofFinToSemiring, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    coeff_ofFinsupp, Finsupp.coe_mk, hi, ↓reduceDIte]
  congr
  exact (Nat.mod_eq_of_lt hi).symm

@[simp]
theorem coeff_eq_zero_of_gt {n i : ℕ} (v : Fin (n + 1) → R) (hi : n + 1 ≤ i) :
    ((ofFinToSemiring n) v).coeff i = 0 := by simp [ofFinToSemiring, hi]

theorem of_fin_to_semiring_def {n : ℕ} (v : Fin (n + 1) → R) : (ofFinToSemiring n) v =
    ∑ i in Finset.range (n + 1), Polynomial.monomial i (v i) := by
  rw [← coeff_inj]
  ext i
  by_cases hi : i < n + 1
  · simp [coeff_eq_val_of_lt, coeff_monomial, hi]
  · simp [coeff_eq_zero_of_gt, coeff_monomial, hi, ofFinToSemiring]

theorem natDegree_le {n : ℕ} (v : Fin (n + 1) → R) : ((ofFinToSemiring n) v).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr <| fun _ a ↦ coeff_eq_zero_of_gt v a

noncomputable def toFin (n : ℕ) : R[X] →+ (Fin (n + 1) → R) where
  toFun p i := p.coeff i
  map_add' x y := by
    simp only [coeff_add]
    rfl
  map_zero' := rfl

end Polynomial
