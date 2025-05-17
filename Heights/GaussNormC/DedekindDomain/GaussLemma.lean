import Heights.GaussNormC.Polynomial.GaussNormC
import Heights.AbsoluteValue.adicAbv
import Mathlib

variable {R K F : Type*} [CommRing R] [IsDedekindDomain R] [FunLike F R ℝ] (v : F) {b : ℝ} (hb : 1 < b)
[Field K] [Algebra R K] [IsFractionRing R K]

namespace Polynomial

variable (p : R[X])

open IsDedekindDomain

theorem isPrimitive_iff_forall_gaussNormC_eq_one {b : NNReal} (hb : 1 < b) : p.IsPrimitive ↔
    ∀ (P : HeightOneSpectrum R), (p.map (algebraMap R K)).gaussNormC (IsDedekindDomain.HeightOneSpectrum.adicAbv P hb) = 1 := by
  sorry

end Polynomial
