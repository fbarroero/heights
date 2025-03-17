import Mathlib.RingTheory.DedekindDomain.AdicValuation

variable {R : Type u_1} [CommRing R] [IsDedekindDomain R] {K : Type u_2} [Field K] [Algebra R K]
    [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R)

theorem valuation_ne_zero {x : K} (hx : x ≠ (0 : K)) : v.valuation x ≠ 0 := by
  simp_all only [ne_eq, map_eq_zero, not_false_eq_true]

theorem boh  (x : K) (h_x_nezero : x ≠ 0) :
    ∃ (π a b : R) (n : ℤ), b ≠ 0 ∧ v.intValuationDef π = ↑(Multiplicative.ofAdd (-1 : ℤ)) ∧
    n =  Multiplicative.toAdd WithZero.unzero (valuation_ne_zero v h_x_nezero) ∧
    x = (algebraMap R K π) ^ n * (algebraMap R K a / algebraMap R K b)
    := by sorry
