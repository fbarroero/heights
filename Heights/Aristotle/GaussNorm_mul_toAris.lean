import Mathlib

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)

namespace Polynomial

variable (p : R[X])

theorem isNonarchimedean_gaussNorm [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    (hna : IsNonarchimedean v) {c : ℝ} (hc : 0 ≤ c) : IsNonarchimedean (gaussNorm v c) := by
  intro p q
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  by_cases hpq : p + q = 0; simp [hpq, hc, gaussNorm_nonneg]
  rw [gaussNorm]
  simp only [support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte, coeff_add,
    Finset.sup'_le_iff, mem_support_iff]
  intro i hi
  calc
  v (p.coeff i + q.coeff i) * c ^ i
    ≤ max (v (p.coeff i)) (v (q.coeff i)) * c ^ i := by
    gcongr
    exact hna (p.coeff i) (q.coeff i)
  _ = max (v (p.coeff i) * c ^ i) (v (q.coeff i) * c ^ i) := by
    rw [max_mul_of_nonneg _ _ (pow_nonneg hc _)]
  _ ≤ max (gaussNorm v c p) (gaussNorm v c q) := by
    apply max_le_max <;>
    exact le_gaussNorm v _ hc i

theorem gaussNorm_mul [IsDomain R] (habs : IsAbsoluteValue v) (hna : IsNonarchimedean v) (p q : R[X]) :
    (p * q).gaussNorm v c = p.gaussNorm v c * q.gaussNorm v c := by
  by_cases hpq : ¬ p * q = 0
  · have h_supp_p : p.support.Nonempty := support_nonempty.mpr <| left_ne_zero_of_mul hpq
    have h_supp_q : q.support.Nonempty := support_nonempty.mpr <| right_ne_zero_of_mul hpq
    simp only [gaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte, h_supp_p,
      h_supp_q]
    apply le_antisymm
    · simp only [Finset.sup'_le_iff, mem_support_iff, ne_eq]
      intro i hi
      rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      let g := fun k ↦ p.coeff (k, i - k).1 * q.coeff (k, i - k).2
      sorry

    · sorry
  · rw [not_not, mul_eq_zero] at hpq
    cases hpq with
    | inl h => simp [h]
    | inr h => simp [h]

end Polynomial
