import Mathlib

variable {A : Type*} [CommRing A] [IsDomain A]
variable {B : Type*} [CommRing B] [IsDomain B] [Algebra A B]

theorem minpoly_pow_natDegree_le (x : B) (n : ℕ) (hn : 0 < n) :
    (minpoly A (x ^ n)).natDegree ≤ (minpoly A x).natDegree := by
  by_cases hx : IsIntegral A x
  · -- x^n is integral since x is integral
    have hxn : IsIntegral A (x ^ n) := hx.pow n

    -- Key: A[x^n] ⊆ A[x], so the rank satisfies [A[x^n] : A] ≤ [A[x] : A]
    have subset : Algebra.adjoin A {x ^ n} ≤ Algebra.adjoin A {x} := by
      apply Algebra.adjoin_le
      intro y hy
      simp at hy
      rw [hy]
      refine pow_mem ?_ n
      exact Algebra.self_mem_adjoin_singleton A x

    -- The natDegree of minpoly equals the rank of the adjoin algebra
    rw [minpoly.natDegree_eq_rank_of_isIntegral hxn]
    rw [minpoly.natDegree_eq_rank_of_isIntegral hx]

    -- Use that submodules have rank bounded by the ambient module
    exact Submodule.rank_le_of_le subset (Algebra.adjoin A {x}).toSubmodule_injective

  · -- If x is not integral, minpoly A x = 0, so its natDegree is 0
    rw [minpoly.eq_zero hx]
    simp
