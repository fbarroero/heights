import Heights.GaussNormC.Polynomial.GaussNormC
import Heights.Polynomial.IsPrimitive
import Mathlib

variable {R K F : Type*} [CommRing R] [FunLike F R ℝ] (v : F) {b : ℝ} (hb : 1 < b)
[Field K] [Algebra R K] [IsFractionRing R K]


namespace Ideal

theorem ne_top_iff_exists_isMaximal {I : Ideal R} : I ≠ ⊤ ↔ ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M := by
  sorry

end Ideal

variable [IsDedekindDomain R]

namespace IsDedekindDomain

theorem Ideal.ne_top_iff_exists [Nontrivial R] (hR : ¬IsField R) {I : Ideal R} : I ≠ ⊤ ↔ ∃ P : HeightOneSpectrum R, P.asIdeal ∣ I := by
  rw [Ideal.ne_top_iff_exists_isMaximal]
  constructor
  · rintro ⟨M, hMmax, hIM⟩
    have hMbot := Ring.ne_bot_of_isMaximal_of_not_isField hMmax hR
    let M' : MaximalSpectrum R := ⟨M, hMmax⟩
    let P := (HeightOneSpectrum.equivMaximalSpectrum hR).invFun M'
    use P
    exact Ideal.dvd_iff_le.mpr hIM
  · rintro ⟨P, hP⟩
    use ((HeightOneSpectrum.equivMaximalSpectrum hR) P).asIdeal
    constructor
    exact ((HeightOneSpectrum.equivMaximalSpectrum hR) P).isMaximal
    exact Ideal.le_of_dvd hP

end IsDedekindDomain

namespace Polynomial

variable (p : R[X])

open IsDedekindDomain HeightOneSpectrum

theorem gaussNormC_one_eq_one_iff_span (P : HeightOneSpectrum R) {b : NNReal} (hb : 1 < b) :
    (p.map (algebraMap R K)).gaussNormC (adicAbv P hb) 1 ≠ 1 ↔ (P.asIdeal ∣ Ideal.span p.coeffs.toSet) := by

  sorry

theorem span_coeffs_eq_top_iff_forall_gaussNormC_eq_one [Nontrivial R] (hR : ¬IsField R) {b : NNReal} (hb : 1 < b) :
    Ideal.span (p.coeffs.toSet) = ⊤ ↔
    ∀ (P : HeightOneSpectrum R), (p.map (algebraMap R K)).gaussNormC (adicAbv P hb) 1 = 1 := by
  rw [← not_iff_not, ← ne_eq]
  simp only [not_forall, gaussNormC_one_eq_one_iff_span]
  exact Ideal.ne_top_iff_exists hR


theorem isPrimitive_iff_forall_gaussNormC_eq_one [Nontrivial R] [IsBezout R] (hR : ¬IsField R)  {b : NNReal} (hb : 1 < b) : p.IsPrimitive ↔
    ∀ (P : HeightOneSpectrum R), (p.map (algebraMap R K)).gaussNormC (adicAbv P hb) 1 = 1 := by
  rw [isPrimitive_iff_span_coeffs_eq_top, span_coeffs_eq_top_iff_forall_gaussNormC_eq_one (K := K) p hR hb]
/-
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
  --rw [isPrim p]



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

  · sorry -/

end Polynomial
