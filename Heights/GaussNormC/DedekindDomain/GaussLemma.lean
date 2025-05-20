import Heights.GaussNormC.Polynomial.GaussNormC
import Heights.AbsoluteValue.adicAbv
import Mathlib

variable {R K F : Type*} [CommRing R] [IsDedekindDomain R] [FunLike F R ℝ] (v : F) {b : ℝ} (hb : 1 < b)
[Field K] [Algebra R K] [IsFractionRing R K]

namespace Polynomial

variable (p : R[X])

open IsDedekindDomain HeightOneSpectrum

theorem isPrimitive_iff_forall_gaussNormC_eq_one {b : NNReal} (hb : 1 < b) : p.IsPrimitive ↔
    ∀ (P : HeightOneSpectrum R), (p.map (algebraMap R K)).gaussNormC (IsDedekindDomain.HeightOneSpectrum.adicAbv P hb) = 1 := by

  by_cases hp0 : p = 0 --add hypothesis p ≠ 0??
  · rw [← not_iff_not]
    simp [hp0, IsPrimitive, gaussNormC, support_nonempty]

    constructor
    intro h
    constructor

    sorry
    classical

    sorry
    sorry
  have h_supp : (map (algebraMap R K) p).support.Nonempty := by
    apply support_nonempty.mpr
    intro h
    apply hp0
    sorry
  constructor
  · intro hp P
    simp [h_supp, gaussNormC, support_nonempty]
    simp [hp0, IsPrimitive, gaussNormC, support_nonempty] at hp
    sorry

  · sorry

end Polynomial
