import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Roots

namespace Polynomial

variable {R : Type u} [Semiring R]

private noncomputable def ofFinToSemiring_aux (n : ℕ) : (Fin (n + 1) → R) → (ℕ →₀ R) := by
  intro v
  let f : ℕ → R := fun i => if h : i < n + 1 then v ⟨i, h⟩ else 0
  have hfin : f.support.Finite := Set.Finite.subset (Finset.finite_toSet (Finset.range (n + 1)))
    (by  simp_all [f])
  exact {toFun := f, support := hfin.toFinset, mem_support_toFun := (by simp [f])}

-- find another place for this?
@[simp]
theorem zero_eq : {toFun := fun _ => 0, support := ∅, mem_support_toFun := by simp} =
    (0 : ℕ →₀ R) := rfl

noncomputable def ofFinToSemiring (n : ℕ) : (Fin (n + 1) → R) →+ R[X] where
  toFun t := ⟨ofFinToSemiring_aux n t⟩
  map_add' x y := by
    ext m
    simp only [ofFinToSemiring_aux, Pi.add_apply, coeff_ofFinsupp, Finsupp.coe_mk, coeff_add]
    split; all_goals simp
  map_zero' := by simp [ofFinToSemiring_aux]

--theorem ofFinToSemiring_def (n : ℕ) (v : Fin (n + 1) → R) : ofFinToSemiring n v = v := by sorry

@[simp]
theorem coeff_eq_val_of_lt {n i : ℕ} (v : Fin (n + 1) → R) (hi : i < n + 1) :
    ((ofFinToSemiring n) v).coeff i = v i := by
  simp only [ofFinToSemiring, ofFinToSemiring_aux, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    coeff_ofFinsupp, Finsupp.coe_mk, hi, ↓reduceDIte]
  congr
  exact Eq.symm (Nat.mod_eq_of_lt hi)

@[simp]
theorem coeff_eq_zero_of_gt {n i : ℕ} (v : Fin (n + 1) → R) (hi : n + 1 ≤ i) :
    ((ofFinToSemiring n) v).coeff i = 0 := by simp [ofFinToSemiring, ofFinToSemiring_aux, hi]

theorem natDegree_le {n : ℕ} (v : Fin (n + 1) → R) : ((ofFinToSemiring n) v).natDegree ≤ n := by
  rw [natDegree_le_iff_coeff_eq_zero]
  exact fun _ a ↦ coeff_eq_zero_of_gt v a

noncomputable def toFin (n : ℕ) : R[X] →+ (Fin (n + 1) → R) where
  toFun p i := p.coeff i
  map_add' x y := by
    simp only [coeff_add]
    rfl
  map_zero' := rfl



end Polynomial
