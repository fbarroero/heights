import Mathlib

namespace Polynomial

section eraseDen

variable {R S : Type*} --[DecidableEq R]
[CommRing R] --[CommMonoidWithZero R] [IsCancelMulZero R]
[NormalizedGCDMonoid R] --[IsDomain R]
(M : Submonoid R)
[CommRing S] [Algebra R S] [IsLocalization M S]
(p : Polynomial S)

noncomputable def eraseDen : Polynomial R :=
  normalize (IsLocalization.integerNormalization M p).primPart

end eraseDen

section intMinpoly

variable {R K : Type*} [DecidableEq R] [CommRing R] --[CommMonoidWithZero R] [IsCancelMulZero R]
[NormalizedGCDMonoid R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] [DecidableEq K]

variable (R) in
noncomputable def intMinpoly (x : K) : Polynomial R :=  (minpoly K x).eraseDen (nonZeroDivisors R)

theorem foo (x : K) : x ∈ (intMinpoly R x).aroots K := by

  sorry

end intMinpoly

end Polynomial
