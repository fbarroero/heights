/-
# Section 1.4: Proof of Thue's Theorem

This file formalizes the statements from Section 1.4, which contains the core proof
machinery for Thue's Theorem. The key results are:

  - Remark 1.4.1: Basic multiplicity bound for a single polynomial
  - Lemma 1.4.2: Multiplicity estimate for P - θQ across distinct points
  - Lemma 1.4.5: Integrality and bound on the sequences xₙ, yₙ
  - Lemma 1.4.6: Approximation quality |xₙ - yₙα|
  - Lemma 1.4.7: Existence of n with xₙ - θyₙ ≠ 0
  - Theorem 1.4.8: Key estimate — the inductive step
  - Final proof of Thue's Theorem 1.1.6
-/

import Mathlib

open Polynomial Complex

noncomputable section

/-! ## Multiplicity Estimates -/

/-- **Remark 1.4.1 (Basic multiplicity bound).**
If `P ∈ ℂ[X] \ {0}` and `z₁, …, z_E ∈ ℂ` are pairwise distinct, then
`∑ₑ ord_{zₑ} P ≤ deg P`. -/
theorem sum_root_multiplicities_le_degree (P : Polynomial ℂ) (hP : P ≠ 0)
    {E : ℕ} (z : Fin E → ℂ) (hz : Function.Injective z) :
    ∑ e : Fin E, P.rootMultiplicity (z e) ≤ P.natDegree := by
  sorry

/-- **Lemma 1.4.2 (Multiplicity estimate).**
Let `D, d ≥ 1` be integers, `z₀, …, z_d ∈ ℂ` pairwise distinct, and
`θ₀, …, θ_d ∈ ℂ` arbitrary.
Let `P, Q ∈ ℂ[X]` be polynomials of degree at most `D`.
If `P - μQ ≠ 0` for any `μ ∈ ℂ`, then
  `∑_{i=0}^{d} ord_{zᵢ}(P - θᵢQ) ≤ d + 2D`.

This is a key estimate that goes beyond the trivial bound of Remark 1.4.1 by
allowing the "twist" `θᵢ` to vary with each evaluation point. The proof
eliminates the `θᵢ` by considering `W = PQ' - P'Q`, which is independent
of the `θᵢ`. -/
theorem multiplicity_estimate {d : ℕ} (hd : 1 ≤ d) (D : ℕ) (hD : 1 ≤ D)
    (z : Fin (d + 1) → ℂ) (hz : Function.Injective z)
    (θ : Fin (d + 1) → ℂ)
    (P Q : Polynomial ℂ) (hPdeg : P.natDegree ≤ D) (hQdeg : Q.natDegree ≤ D)
    (h_nonprop : ∀ μ : ℂ, P - Polynomial.C μ * Q ≠ 0) :
    ∑ i : Fin (d + 1),
      (P - Polynomial.C (θ i) * Q).rootMultiplicity (z i) ≤ d + 2 * D := by
  sorry

/-! ## The Sequences xₙ, yₙ

Given polynomials `P, Q ∈ ℤ[X]` of degree ≤ D and integers `a, b` (with `b ≥ 1`),
we define (following equation (1.11) of the paper):

  `yₙ = bᴰ/n! · (dⁿQ/dXⁿ)(a/b)`
  `xₙ = bᴰ/n! · (dⁿP/dXⁿ)(a/b)`

These are integers and provide successive approximations to `α`.
-/

/-- The integer `yₙ` from equation (1.11): `yₙ = bᴰ · ∑_j q_j · C(j,n) · aʲ⁻ⁿ · bⁿ⁻ʲ`.
This equals `bᴰ/n! · (dⁿQ/dXⁿ)(a/b)` and is always an integer. -/
def thue_seq_y (Q : Polynomial ℤ) (a b : ℤ) (D n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (D + 1), Q.coeff j * (j.choose n) * a ^ (j - n) * b ^ (D - j + n)

/-- The integer `xₙ` from equation (1.11): `xₙ = bᴰ/n! · (dⁿP/dXⁿ)(a/b)`. -/
def thue_seq_x (P : Polynomial ℤ) (a b : ℤ) (D n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (D + 1), P.coeff j * (j.choose n) * a ^ (j - n) * b ^ (D - j + n)

/-- **Lemma 1.4.5.** For every integer `n ≥ 0`, the numbers `xₙ, yₙ` are integers
and `|yₙ| ≤ c₃(α)^{D/δ} · bᴰ`.

The bound follows from the coefficient bounds on `Q` from Proposition 1.3.2 and
standard binomial coefficient estimates (`C(j,n) ≤ 2ʲ`). -/
theorem thue_yn_bound (α : ℂ) (hα : IsIntegral ℤ α)
    (d : ℕ) (hd : d = (minpoly ℤ α).natDegree) (hd_pos : 0 < d)
    (D : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ_le : δ ≤ 1/2)
    (a b : ℤ) (hb : 1 ≤ b) (hab : ‖(α : ℂ) - ↑a / ↑b‖ ≤ 1) :
    ∃ c₃ : ℝ, 1 < c₃ ∧
      ∀ Q : Polynomial ℤ, Q.natDegree ≤ D →
        (∀ i, (|Q.coeff i| : ℝ) ≤ c₃ ^ ((D : ℝ) / δ)) →
        ∀ n : ℕ, (|thue_seq_y Q a b D n| : ℝ) ≤ c₃ ^ ((D : ℝ) / δ) * (b : ℝ) ^ D := by
  sorry

/-! ## Approximation Quality -/

/-- **Lemma 1.4.6.** For all `n ∈ {0, …, m}` we have
  `|xₙ - yₙ α| ≤ c₄(α)^{D/δ} · bᴰ · |α - a/b|^{m-n}`.

The better the starting approximation `a/b` is to `α`, the smaller
`|yₙα - xₙ|` is going to be. The proof uses the Taylor expansion of
`R = P - αQ` around `α`, which vanishes to order `≥ m` by construction. -/
theorem thue_approximation_quality (α : ℂ) (hα : IsIntegral ℤ α)
    (d : ℕ) (hd : d = (minpoly ℤ α).natDegree) (hd_pos : 0 < d)
    (D m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ_le : δ ≤ 1/2)
    (a b : ℤ) (hb : 1 ≤ b)
    (P Q : Polynomial ℤ)
    (hPdeg : P.natDegree ≤ D) (hQdeg : Q.natDegree ≤ D)
    -- P - αQ vanishes at α with order ≥ m
    (hvanish : ∀ k : ℕ, k < m →
      Polynomial.aeval α (Polynomial.derivative^[k] P) -
      α * Polynomial.aeval α (Polynomial.derivative^[k] Q) = 0) :
    ∃ c₄ : ℝ, 0 < c₄ ∧
      ∀ n : ℕ, n ≤ m →
        ‖(thue_seq_x P a b D n : ℂ) - (thue_seq_y Q a b D n : ℂ) * α‖ ≤
          c₄ ^ ((D : ℝ) / δ) * (b : ℝ) ^ D *
          ‖α - (a : ℂ) / (b : ℂ)‖ ^ (m - n) := by
  sorry

/-! ## Choosing the Right Index n -/

/-- The parameter `D` as chosen in equation (1.13):
  `D = ⌊(d + 2δ)m / 2⌋`.
This choice satisfies `2(D+1) > (d + 2δ)m`, which is needed for Proposition 1.3.2. -/
def thue_param_D (d : ℕ) (δ : ℝ) (m : ℕ) : ℕ :=
  ⌊((d : ℝ) + 2 * δ) * m / 2⌋₊

/-- **Lemma 1.4.7.** Let `θ ∈ ℂ`. There exists an integer `n ≥ 0` with
`n ≤ 2δm + d` and `xₙ - θyₙ ≠ 0`.

The proof splits into two cases:
- **Case 1:** `P = μQ` for some `μ`. Then `R = (μ - α)Q`, and using the vanishing
  order at all conjugates of `α`, one shows `dm ≤ D`, giving the bound.
- **Case 2:** `P - μQ ≠ 0` for all `μ`. Apply Lemma 1.4.2 with `z₀ = a/b` and
  `{z₁,…,z_d}` the conjugates of `α`, to bound `ord_{a/b}(P - θQ) ≤ 2D + d - md`. -/
theorem exists_good_index
    (d : ℕ) (hd_ge : 2 ≤ d)
    (D m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hδ_le : δ ≤ 1/4)
    (hDm : D = thue_param_D d δ m)
    (P Q : Polynomial ℤ) (hPdeg : P.natDegree ≤ D) (hQdeg : Q.natDegree ≤ D)
    (a b : ℤ) (hb : 1 ≤ b) (θ : ℂ)
    -- P - αQ ≠ 0 as a polynomial over ℂ (from Proposition 1.3.2(iii))
    (α : ℂ) (hα : IsIntegral ℤ α) (hα_irr : ¬ (∃ q : ℚ, (q : ℂ) = α))
    (hd : d = (minpoly ℤ α).natDegree)
    (hR_ne : P.map (Int.castRingHom ℂ) - Polynomial.C α * Q.map (Int.castRingHom ℂ) ≠ 0)
    -- P - αQ vanishes at α with order ≥ m
    (hvanish : ∀ k : ℕ, k < m →
      Polynomial.aeval α (Polynomial.derivative^[k] P) -
      α * Polynomial.aeval α (Polynomial.derivative^[k] Q) = 0) :
    ∃ n : ℕ, (n : ℝ) ≤ 2 * δ * m + d ∧
      thue_seq_x P a b D n - θ * thue_seq_y Q a b D n ≠ 0 := by
  sorry

/-! ## The Key Estimate -/

/-- **Theorem 1.4.8 (Key Estimate).**
Let `α` be an algebraic integer with `[ℚ(α) : ℚ] = d ≥ 2` and let `ε > 0`.
There exists a constant `T = T(α, ε) > 1` with the following property:
If there exist `a, b ∈ ℤ` with `b > T` and `|α - a/b| < 1/b^{1+d/2+ε}`,
then `|α - x/y| ≥ C(α, ε) / y^{1+d/2+2ε}` for all `x, y ∈ ℤ` with `y ≥ 1`.

This is the core inductive step: a single good approximation `a/b` implies a
universal lower bound for all approximations `x/y`, with a slightly worse exponent.

The proof combines:
  - The auxiliary polynomial from Proposition 1.3.2
  - The bound `|xₙ - yₙα|` from Lemma 1.4.6
  - The index selection from Lemma 1.4.7
  - The fundamental inequality (1.17): `1/y ≤ |xₙ - αyₙ| + |yₙ| · |x/y - α|` -/
theorem thue_key_estimate (α : ℂ) (hα : IsIntegral ℤ α)
    (d : ℕ) (hd : d = (minpoly ℤ α).natDegree) (hd_ge : 2 ≤ d)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ T : ℝ, 1 < T ∧ ∃ C : ℝ, 0 < C ∧
      ∀ a b : ℤ, (b : ℝ) > T →
        ‖(α : ℂ) - ↑a / ↑b‖ < 1 / (b : ℝ) ^ (1 + (d : ℝ) / 2 + ε) →
        ∀ x y : ℤ, (1 : ℤ) ≤ y →
          C / (y : ℝ) ^ (1 + (d : ℝ) / 2 + 2 * ε) ≤
            ‖(α : ℂ) - ↑x / ↑y‖ := by
  sorry

/-! ## Final Proof of Thue's Theorem -/

/-- **Proof of Thue's Theorem (Theorem 1.1.6).**
Without loss of generality, `α` is an irrational algebraic integer.
Let `T` be as in Theorem 1.4.8.

**Case 1:** If `y ≤ T` for all solutions `(x, y)` to `|α - x/y| < 1/y^{1+d/2+ε/2}`,
then there are finitely many such `y`, and for each `y` there are at most two
possible `x` (since `|x - αy| < 1`). This gives the bound directly.

**Case 2:** If there exist `(a, b)` with `b > T` satisfying the inequality, then
Theorem 1.4.8 with `ε/2` gives the conclusion. -/
theorem thue_theorem_final (α : ℂ) (hα : IsAlgebraic ℚ α)
    (d : ℕ) (hd : d = (minpoly ℚ α).natDegree) (hd_ge : d ≥ 3)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x y : ℤ, y ≠ 0 → (α ≠ ↑x / ↑y) →
      C / (|↑y| : ℝ) ^ ((d : ℝ) / 2 + 1 + ε) ≤ ‖(α : ℂ) - ↑x / ↑y‖ := by
  sorry

/-! ## Remark 1.4.9: Ineffectivity

The constants `c₁(α), …, c₄(α)` that appear in the preparation of the proof can
in principle be determined explicitly if one knows the minimal polynomial of `α` over ℚ.
However, the final constant `C(α, ε)` cannot be calculated with this method, because
the proof proceeds by contradiction: it assumes the existence of a "starting
approximation" `a/b`, and the resulting constant depends on `a` and `b`, which
are not known explicitly. This is the fundamental reason why Thue's Theorem is
**ineffective** — it proves finiteness without giving a way to enumerate all solutions.
-/

end
