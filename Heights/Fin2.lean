import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Roots

namespace Polynomial

variable {R : Type u} [Semiring R]

noncomputable def ofFinToSemiring (n : ℕ) := fun f : Fin (n + 1) → R ↦ ∑ i in Finset.range (n + 1),
  Polynomial.monomial i (f i)

end Polynomial
