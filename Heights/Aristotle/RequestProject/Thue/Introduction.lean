/-
# Section 1.1: Introduction

This file formalizes the statements from Section 1.1 of the paper on Thue's Theorem,
including:
  - Theorem 1.1.1: Finiteness of solutions to Thue equations
  - Theorem 1.1.4: Liouville's inequality
  - Theorem 1.1.6: Thue's approximation theorem (1909)
  - Theorem 1.1.8: Dirichlet's approximation theorem
  - Corollary 1.1.9: Infinitely many good approximations iff irrational
-/

import Mathlib

open Complex Polynomial

noncomputable section

/-! ## Thue Equations -/

/-- A Thue form is a homogeneous polynomial `F ∈ ℚ[X, Y]`.
    We represent it as a function `ℤ × ℤ → ℚ` arising from evaluating
    a homogeneous polynomial of degree `d` with rational coefficients. -/
structure ThueForm where
  /-- The degree of the homogeneous polynomial. -/
  degree : ℕ
  /-- The underlying homogeneous polynomial as an `MvPolynomial`. -/
  poly : MvPolynomial (Fin 2) ℚ
  /-- The polynomial is homogeneous of the given degree. -/
  is_homogeneous : poly.IsHomogeneous degree
  /-- The polynomial is irreducible. -/
  is_irreducible : Irreducible poly

/-- Evaluate a Thue form at an integer point. -/
def ThueForm.eval (F : ThueForm) (x y : ℤ) : ℚ :=
  MvPolynomial.eval ![((x : ℤ) : ℚ), ((y : ℤ) : ℚ)] F.poly

/-- **Theorem 1.1.1 (Thue's Theorem on Thue equations).**
Let `F ∈ ℚ[X, Y]` be a homogeneous irreducible polynomial of degree at least 3.
For every rational number `k ∈ ℚ \ {0}`, the set
`{(x, y) ∈ ℤ² : F(x, y) = k}` is finite. -/
theorem thue_equation_finite (F : ThueForm) (hd : F.degree ≥ 3) (k : ℚ) (hk : k ≠ 0) :
    Set.Finite {p : ℤ × ℤ | F.eval p.1 p.2 = k} := by
  sorry

/-! ## Liouville's Inequality -/

/-- **Theorem 1.1.4 (Liouville's Inequality).**
Let `α ∈ ℂ` be an algebraic number with `d = [ℚ(α) : ℚ]` and `x, y ∈ ℤ` with
`y ≥ 1`. If `α ≠ x/y`, then `|α - x/y| ≥ 1 / (2^d · (1 + |α|)^d · H(α)^d · y^d)`.

We state a simplified version: there exists a constant `C(α) > 0` depending only
on `α` such that `|α - x/y| ≥ C(α) / y^d` for all `x, y ∈ ℤ` with `y ≥ 1`
and `α ≠ x/y`. -/
theorem liouville_inequality (α : ℂ) (hα : IsAlgebraic ℚ α)
    (d : ℕ) (hd : d = (minpoly ℚ α).natDegree) (hd_pos : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℤ, (1 : ℤ) ≤ y → (α ≠ ↑x / ↑y) →
      C / (y : ℝ) ^ d ≤ ‖α - ↑x / ↑y‖ := by
  sorry

/-! ## Thue's Approximation Theorem -/

/-- **Theorem 1.1.6 (Thue, 1909).**
Let `α ∈ ℂ` be an algebraic number with `d = [ℚ(α) : ℚ]`. For all `ε > 0` there
exists a constant `C(α, ε) > 0` such that
  `|α - x/y| ≥ C(α, ε) / |y|^(d/2 + 1 + ε)`
for all `x, y ∈ ℤ` with `y ≠ 0` and `x/y ≠ α`. -/
theorem thue_approximation (α : ℂ) (hα : IsAlgebraic ℚ α)
    (d : ℕ) (hd : d = (minpoly ℚ α).natDegree) (hd_ge : d ≥ 3) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℤ, y ≠ 0 → (α ≠ ↑x / ↑y) →
      C / (|↑y| : ℝ) ^ ((d : ℝ) / 2 + 1 + ε) ≤ ‖α - ↑x / ↑y‖ := by
  sorry

/-! ## Dirichlet's Approximation Theorem -/

/-- **Theorem 1.1.8 (Dirichlet's Approximation Theorem).**
Let `α ∈ ℝ` and `Q > 0` an integer. There exist `p, q ∈ ℤ` with `gcd(p, q) = 1`
such that `1 ≤ q ≤ Q` and `|α - p/q| ≤ 1/(q(Q + 1))`. -/
theorem dirichlet_approximation (α : ℝ) (Q : ℕ) (hQ : 0 < Q) :
    ∃ p q : ℤ, Int.gcd p q = 1 ∧ (1 : ℤ) ≤ q ∧ q ≤ Q ∧
      |α - ↑p / ↑q| ≤ 1 / (↑q * (↑Q + 1)) := by
  sorry

/-- **Corollary 1.1.9.**
Let `α ∈ ℝ`. There are infinitely many pairs `(p, q) ∈ ℤ²` with `q ≥ 1` and
`|α - p/q| < 1/q²` if and only if `α ∉ ℚ`. -/
theorem infinitely_many_good_approximations_iff_irrational (α : ℝ) :
    (∀ S : Finset (ℤ × ℤ), ∃ p q : ℤ, (1 : ℤ) ≤ q ∧ (p, q) ∉ S ∧
      |α - ↑p / ↑q| < 1 / (↑q) ^ 2) ↔ Irrational α := by
  sorry

/-- The forward direction of Corollary 1.1.9: if `α` is irrational, there are
infinitely many good rational approximations. -/
theorem irrational_has_infinitely_many_approximations (α : ℝ) (hα : Irrational α) :
    ∀ S : Finset (ℤ × ℤ), ∃ p q : ℤ, (1 : ℤ) ≤ q ∧ (p, q) ∉ S ∧
      |α - ↑p / ↑q| < 1 / (↑q) ^ 2 := by
  sorry

/-- The backward direction of Corollary 1.1.9: if `α` is rational, there are only
finitely many good rational approximations (in reduced form). -/
theorem rational_has_finitely_many_approximations (α : ℝ) (hα : ¬Irrational α) :
    ∃ S : Finset (ℤ × ℤ), ∀ p q : ℤ, (1 : ℤ) ≤ q → |α - ↑p / ↑q| < 1 / (↑q) ^ 2 →
      (p, q) ∈ S := by
  sorry

end
