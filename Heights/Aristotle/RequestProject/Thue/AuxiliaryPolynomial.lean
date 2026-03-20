/-
# Section 1.3: The Auxiliary Polynomial

This file formalizes the statements from Section 1.3, which constructs the auxiliary
polynomial used in the proof of Thue's Theorem. The key results are:

  - Lemma 1.3.1: Powers of an algebraic integer expressed in a ℤ-basis
  - Proposition 1.3.2: Construction of auxiliary polynomials P, Q with controlled
    coefficients and a prescribed vanishing order at α
-/

import Mathlib

open Polynomial Complex

noncomputable section

/-! ## Powers of Algebraic Integers -/

/-- **Lemma 1.3.1.** Let `α` be an algebraic integer of degree `d = [ℚ(α) : ℚ]`.
There exists a constant `c₁(α) > 1` such that for all `i ≥ 0` there are integers
`a_{i,0}, …, a_{i,d-1} ∈ ℤ` with `|a_{i,j}| ≤ c₁(α)^i` for all `j` and
`α^i = ∑_{j=0}^{d-1} a_{i,j} · α^j`.

The proof proceeds by induction on `i`, using the minimal polynomial relation
`α^d = -a₁ α^{d-1} - ⋯ - a_d` to reduce higher powers. The constant is
`c₁ = 2 · max{|a₁|, …, |a_d|}`. -/
theorem algebraic_integer_power_basis (α : ℂ) (hα : IsIntegral ℤ α)
    (d : ℕ) (hd : d = (minpoly ℤ α).natDegree) (hd_pos : 0 < d) :
    ∃ c₁ : ℝ, 1 < c₁ ∧
      ∀ i : ℕ, ∃ a : Fin d → ℤ,
        (∀ j : Fin d, (|a j| : ℝ) ≤ c₁ ^ i) ∧
        (α ^ i = ∑ j : Fin d, (a j : ℂ) * α ^ (j : ℕ)) := by
  sorry

/-! ## Construction of the Auxiliary Polynomial -/

/-- **Proposition 1.3.2 (Construction of auxiliary polynomials).**
Let `α ∈ ℂ \ ℚ` be an algebraic integer with `d = [ℚ(α) : ℚ]`.
Let `D ≥ 1` and `m ≥ 1` be integers and `δ ∈ (0, 1/2]` with
`2(D + 1) > (d + δ)m`.

Then there exist `P, Q ∈ ℤ[X]`, not both zero, such that:
  (i)   `max{deg P, deg Q} ≤ D`,
  (ii)  `max{‖P‖, ‖Q‖} ≤ c₂(α)^{D/δ}` for some constant `c₂(α) = 8^d · c₁(α)^{2d}`,
  (iii) `P - αQ ∈ ℂ[X]` is nonzero and vanishes at `α` with multiplicity ≥ m.

The proof uses Siegel's Lemma (Lemma 1.2.2) applied to the `dm` homogeneous linear
equations in `2(D+1)` unknowns expressing the vanishing conditions, after eliminating
powers of `α` using Lemma 1.3.1. The matrix norm is bounded by `2^D · c₁(α)^{D+1}`. -/
theorem auxiliary_polynomial_construction (α : ℂ) (hα : IsIntegral ℤ α)
    (hα_irr : ¬ (∃ q : ℚ, (q : ℂ) = α))
    (d : ℕ) (hd : d = (minpoly ℤ α).natDegree) (hd_pos : 0 < d)
    (D m : ℕ) (hD : 1 ≤ D) (hm : 1 ≤ m) (δ : ℝ) (hδ_pos : 0 < δ) (hδ_le : δ ≤ 1/2)
    (h_dim : 2 * (D + 1) > (d + δ) * m) :
    ∃ c₂ : ℝ, 0 < c₂ ∧
    ∃ P Q : Polynomial ℤ, (P ≠ 0 ∨ Q ≠ 0) ∧
      -- (i) degree bound
      P.natDegree ≤ D ∧ Q.natDegree ≤ D ∧
      -- (ii) coefficient bound: max{‖P‖, ‖Q‖} ≤ c₂^{D/δ}
      (∀ i, (|P.coeff i| : ℝ) ≤ c₂ ^ ((D : ℝ) / δ)) ∧
      (∀ i, (|Q.coeff i| : ℝ) ≤ c₂ ^ ((D : ℝ) / δ)) ∧
      -- (iii) P - αQ vanishes at α with order ≥ m:
      --   (d^k/dX^k)(P - αQ)(α) = 0  for all k ∈ {0, …, m-1}
      (∀ k : ℕ, k < m →
        Polynomial.aeval α (Polynomial.derivative^[k] P) -
        α * Polynomial.aeval α (Polynomial.derivative^[k] Q) = 0) ∧
      -- P - αQ is not identically zero as a polynomial over ℂ
      (P.map (Int.castRingHom ℂ) - Polynomial.C α * Q.map (Int.castRingHom ℂ) ≠ 0) := by
  sorry

end
