/-
# Section 1.2: Siegel's Lemma

This file formalizes the statements from Section 1.2, which contains Siegel's Lemma
— a fundamental quantitative result about integer solutions to homogeneous linear
systems. It is the key tool for constructing auxiliary polynomials in the proof of
Thue's Theorem.

  - Definition 1.2.1: Maximum norm on matrices and vectors
  - Lemma 1.2.2: Siegel's Lemma
  - Example 1.2.3: Application to polynomials with small coefficients
-/

import Mathlib

open Matrix Finset

noncomputable section

/-! ## The Maximum Norm -/

/-- **Definition 1.2.1.** The maximum (sup) norm of an integer vector `x ∈ ℤ^N`,
defined as `max_i |x_i|`. -/
def vecMaxNorm {N : ℕ} (x : Fin N → ℤ) : ℤ :=
  if h : 0 < N then
    Finset.sup' Finset.univ ⟨⟨0, h⟩, Finset.mem_univ _⟩ (fun i => |x i|)
  else 0

/-- **Definition 1.2.1.** The maximum (sup) norm of an integer matrix `A ∈ M_{M,N}(ℤ)`,
defined as `max_{i,j} |A_{i,j}|`. -/
def matMaxNorm {M N : ℕ} (A : Matrix (Fin M) (Fin N) ℤ) : ℤ :=
  if hM : 0 < M then
    if hN : 0 < N then
      Finset.sup' Finset.univ ⟨⟨0, hM⟩, Finset.mem_univ _⟩
        (fun i => Finset.sup' Finset.univ ⟨⟨0, hN⟩, Finset.mem_univ _⟩ (fun j => |A i j|))
    else 0
  else 0

/-! ## Siegel's Lemma -/

/-- **Lemma 1.2.2 (Siegel's Lemma).**
Let `M, N` be integers with `N > M ≥ 1` and `A ∈ M_{M,N}(ℤ)`.
Let `B ≥ 1` be a real number with `‖A‖ ≤ B`.
There exists `x ∈ ℤ^N \ {0}` with `‖x‖ ≤ (NB)^{M/(N-M)}` such that `Ax = 0`.

The proof uses the Pigeonhole Principle: consider all integer points in `[0,T]^N`
where `T = ⌊(NB)^{M/(N-M)}⌋`. The number of such points is `(T+1)^N`, while the
number of possible image vectors under `A` is at most `(BNT+1)^M`.
By the choice of `T`, we have `(T+1)^N > (BNT+1)^M`, so two distinct points must
have the same image, yielding a nontrivial kernel element. -/
theorem siegel_lemma {M N : ℕ} (hM : 1 ≤ M) (hNM : M < N)
    (A : Matrix (Fin M) (Fin N) ℤ) (B : ℝ) (hB : 1 ≤ B)
    (hAB : (matMaxNorm A : ℝ) ≤ B) :
    ∃ x : Fin N → ℤ, x ≠ 0 ∧
      (∀ i : Fin M, ∑ j : Fin N, A i j * x j = 0) ∧
      (∀ j : Fin N, (|x j| : ℝ) ≤ (N * B) ^ ((M : ℝ) / ((N : ℝ) - (M : ℝ)))) := by
  sorry

/-! ## Application: Polynomials with Small Coefficients -/

/-- **Example 1.2.3.** For any `M ≥ 1`, there exists a nonzero polynomial `P ∈ ℤ[X]`
divisible by `(X - 1)^M` whose coefficients lie in `{0, ±1}`.

The divisibility condition `(X-1)^M | P` is equivalent to `P^{(i)}(1) = 0` for
`i = 0, …, M-1`. Writing `P = ∑_{j=0}^{N-1} a_j X^j`, this gives `M` linear equations
in `N` unknowns with integer coefficients bounded by `N^M`.
By Siegel's Lemma with `N` large enough, one finds `P` with `‖P‖ ≤ N^{M(M+1)/(N-M)}`.
Since `N^{M(M+1)/(N-M)} → 1` as `N → ∞`, choosing `N` large gives `‖P‖ < 2`. -/
theorem exists_small_coeff_multiple_of_power (M : ℕ) (hM : 1 ≤ M) :
    ∃ P : Polynomial ℤ, P ≠ 0 ∧
      (Polynomial.X - 1) ^ M ∣ P ∧
      (∀ i, |P.coeff i| ≤ 1) := by
  sorry

end
