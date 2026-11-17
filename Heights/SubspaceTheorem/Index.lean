module

public import Heights.SubspaceTheorem.Defs
public import Heights.SubspaceTheorem.Polynomial

/-!
# Polynomials in several blocks of variables

This file contains the definitions used for polynomials in several blocks of variables.
Schmidt's generalisation of Roth's lemma `Schmidt.generalized_roth_lemma`
([evertse1993], Proposition 3.4.2, [schmidt1980], Chapter VI, Theorem 10B), which used to be
stated here, is proved in the file `GeneralizedRothLemma`, from Roth's lemma
([schmidt1980], Chapter V, Theorem 10A) proved in the file `RothLemma`.

The other result on polynomials needed in the proof of the Subspace Theorem
([evertse1993], Section 3.4), the construction of the auxiliary polynomial
`Schmidt.polynomial_theorem` ([evertse1993], Proposition 3.4.3, [schmidt1980], Chapter VI,
Theorem 7A), is in the file `PolynomialTheorem`.

We consider polynomials `P(X₁, …, Xₘ)` in `m` blocks `X_h = (X_{h k})_{k : ι}` of `n` variables,
that is, elements of `MvPolynomial (Fin m × ι) ℤ`.
-/

@[expose] public section

open Matrix

namespace Schmidt

variable {m : ℕ} {ι : Type*} [Fintype ι]

/-- A polynomial `P(X₁, …, Xₘ)` in `m` blocks of variables is homogeneous of degree `d h` in the
block `X_h` for every `h`. The set of these polynomials is denoted by `ℛ(d)` in
[evertse1993]. -/
def IsBlockHomogeneous {R : Type*} [CommSemiring R] (P : MvPolynomial (Fin m × ι) R)
    (d : Fin m → ℕ) : Prop :=
  ∀ h, MvPolynomial.IsWeightedHomogeneous (fun p : Fin m × ι ↦ if p.1 = h then 1 else 0) P (d h)

/-- The quantity `(i / d) = ∑ h, (i_{h 1} + ⋯ + i_{h n}) / d_h` attached to a multi-index `i`. The
*index* of `P` at the point `x` with respect to `d` is the minimum of `(i / d)` over the `i` such
that the divided derivative `P_i` does not vanish at `x`. -/
noncomputable def blockWeight (d : Fin m → ℕ) (i : Fin m × ι →₀ ℕ) : ℝ :=
  ∑ h, (∑ k, (i (h, k) : ℝ)) / d h

/-- The height of a polynomial with integer coefficients: the maximum of the absolute values of
its coefficients. -/
def height {σ : Type*} (P : MvPolynomial σ ℤ) : ℕ :=
  P.support.sup fun j ↦ (P.coeff j).natAbs

/-- The polynomial `P(X₁, …, Xₘ)` written as a polynomial in the variables
`U_{h k} = L_k(X_h)`. The coefficients of `linExpand L P_i` are denoted by `d_{P, i}(j)`
in [evertse1993]. -/
noncomputable def linExpand [DecidableEq ι] (L : Matrix ι ι ℝ)
    (P : MvPolynomial (Fin m × ι) ℤ) : MvPolynomial (Fin m × ι) ℝ :=
  MvPolynomial.aeval
    (fun p : Fin m × ι ↦ ∑ k, MvPolynomial.C (L⁻¹ p.2 k) * MvPolynomial.X (p.1, k)) P

end Schmidt
