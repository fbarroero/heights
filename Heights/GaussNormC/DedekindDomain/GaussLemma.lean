import Heights.GaussNormC.Polynomial.GaussNormC
import Heights.AbsoluteValue.adicAbv
import Heights.Polynomial.IsPrimitive
import Mathlib

variable {R K F : Type*} [CommRing R] [IsDedekindDomain R] [FunLike F R ℝ] (v : F) {b : ℝ} (hb : 1 < b)
[Field K] [Algebra R K] [IsFractionRing R K]

namespace Polynomial

variable (p : R[X])

open IsDedekindDomain HeightOneSpectrum

theorem gaussNormC_one_eq_one_iff_span (P : HeightOneSpectrum R) {b : NNReal} (hb : 1 < b) :
    (p.map (algebraMap R K)).gaussNormC (IsDedekindDomain.HeightOneSpectrum.adicAbv P hb) 1 = 1
    ↔ (P.asIdeal ∣ Ideal.span p.coeffs.toSet) := by

  sorry

theorem isPrimitive_iff_forall_gaussNormC_eq_one [Nontrivial R] {b : NNReal} (hb : 1 < b) : p.IsPrimitive ↔
    ∀ (P : HeightOneSpectrum R), (p.map (algebraMap R K)).gaussNormC (IsDedekindDomain.HeightOneSpectrum.adicAbv P hb) 1 = 1 := by

  by_cases hp0 : p = 0 --add hypothesis p ≠ 0??
  · --rw [← not_iff_not]
    simp [hp0, IsPrimitive, gaussNormC, support_nonempty]

    constructor
    intro h P
    specialize h 0
    subst hp0
    simp_all only [isUnit_zero_iff, zero_ne_one]
    intro hP
    exfalso
    apply hP


    sorry

  -- until here  case p = 0
  -- case p ≠ 0

  have h_supp : (map (algebraMap R K) p).support.Nonempty := by
    apply support_nonempty.mpr
    refine (Polynomial.map_ne_zero_iff ?_).mpr hp0
    exact FaithfulSMul.algebraMap_injective R K
  rw [isPrim p]



  constructor
  · intro hp P
    --rw [IsPrimitive] at hp


    /- contrapose!
    intro hp

    rw [IsPrimitive, not_forall]
    simp only [Classical.not_imp]
    rcases hp with ⟨P, hP⟩
    simp only [gaussNormC, h_supp, ↓reduceDIte, coeff_map, one_pow, mul_one] at hP -/



    sorry

  · sorry

end Polynomial
