import Mathlib

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S : Type*} [CommRing R]  [IsDedekindDomain R] [CommRing S] [IsDedekindDomain S]
[Algebra R S] --[FunLike F R S]  (f : F)  [RingHomClass F R S]

def comap (f : R →+* S) (v : HeightOneSpectrum S) : HeightOneSpectrum R := {
  asIdeal := v.asIdeal.comap f
  isPrime := Ideal.comap_isPrime f v.asIdeal
  ne_bot := by

    sorry
}


end IsDedekindDomain.HeightOneSpectrum
