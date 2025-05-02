import Mathlib

namespace Polynomial

variable {R α : Type*} [Semiring R] [Semiring α] [LinearOrder α]
 (f : AbsoluteValue R α) (hna : IsNonarchimedean f)

def GaussNorm : R[X] → α := fun p ↦ if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (f (p.coeff i)) else 0

include hna in
theorem isNonarchimedean_GaussNorm [AddLeftMono α] : IsNonarchimedean (GaussNorm f) := sorry

end Polynomial
