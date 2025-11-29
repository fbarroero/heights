import Heights.IntMahlerMeasureofFn

namespace Polynomial

variable {p : ℤ[X]} {K : Type*} [Field K] [NumberField K]

open NumberField

theorem aa {x : K} (hx : IsIntegral ℤ x) (h : ∀ v : InfinitePlace K, v x = 1) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by

  sorry



-- ConjRootClass.minpoly.map_eq_prod
open ConjRootClass




theorem t2 {c : ConjRootClass ℚ ℂ} (h : ∀ x ∈ c.carrier, ‖x‖ = 1) :
    (c.minpoly.map (algebraMap ℚ ℂ)).mahlerMeasure = 1 := by
  have : Fintype c.carrier := {
    elems := by

      sorry,
    complete := sorry
  }

  --rw [ConjRootClass.minpoly.map_eq_prod]
  sorry

theorem t1 {c : ConjRootClass ℚ ℂ} (h : ∀ x ∈ c.carrier, ‖x‖ = 1) {x : ℂ} (hx : x ∈ c.carrier) :
    ∃ n, 0 < n ∧ x ^ n = 1 := by

  sorry


theorem Kronecker' (hd : p.natDegree ≠ 0) (h_irr : Irreducible p) (h_mon : p.Monic)
    (hp : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) :
    ∃ k, (p.map (Int.castRingHom ℂ)).roots.toFinset = primitiveRoots k ℂ := by

  sorry


theorem Kronecker (hd : p.natDegree ≠ 0) (h_irr : Irreducible p) (h_mon : p.Monic)
    (hp : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) : p = cyclotomic p.natDegree ℤ := by
  obtain ⟨k, hk⟩ := Kronecker' hd h_irr h_mon hp

  sorry



end Polynomial
