import Heights.IntMahlerMeasureofFn

namespace Polynomial

variable {p : ℤ[X]}

theorem Kronecker (hd : p.natDegree ≠ 0) (h_irr : Irreducible p) (h_mon : p.Monic)
    (hp : (p.map (Int.castRingHom ℂ)).mahlerMeasure = 1) : p = cyclotomic p.natDegree ℤ := by
  simp [hd, cyclotomic]
  sorry


end Polynomial
