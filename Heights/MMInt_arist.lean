import Mathlib

namespace Polynomial

variable {p : ℤ[X]}


lemma miao (hlc : ‖(map (Int.castRingHom ℂ) p).leadingCoeff‖ = 1) (hpx : p ≠ X)
    (hroots : (Multiset.map (fun a ↦ max 1 ‖a‖) (map (Int.castRingHom ℂ) p).roots).prod = 1)
    {z : ℂ} (hz : z ∈ p.aroots ℂ) :
    ∃ n, 0 < n ∧ z ^ n = 1 := by

  sorry

end Polynomial
