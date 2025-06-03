import Heights.GaussNormC.Polynomial.GaussNormC
import Heights.Polynomial.IsPrimitive
import Heights.AbsoluteValue.adicAbv
import Mathlib

variable {R K F : Type*} [CommRing R] [FunLike F R ℝ] (v : F) {b : ℝ} (hb : 1 < b)
[Field K] [Algebra R K] [IsFractionRing R K]


namespace Ideal
--PRd
theorem ne_top_iff_exists_isMaximal {I : Ideal R} : I ≠ ⊤ ↔ ∃ M : Ideal R, M.IsMaximal ∧ I ≤ M := by
  refine ⟨exists_le_maximal I, ?_⟩
  contrapose!
  rintro rfl M hMmax
  rw [top_le_iff]
  exact IsMaximal.ne_top hMmax

end Ideal

variable [IsDedekindDomain R]

namespace IsDedekindDomain
--PRd
theorem Ideal.ne_top_iff_exists [Nontrivial R] (hR : ¬IsField R) {I : Ideal R} : I ≠ ⊤ ↔ ∃ P : HeightOneSpectrum R, I ≤ P.asIdeal := by
  rw [Ideal.ne_top_iff_exists_isMaximal]
  constructor
  · rintro ⟨M, hMmax, hIM⟩
    exact ⟨(HeightOneSpectrum.equivMaximalSpectrum hR).invFun <| ⟨M, hMmax⟩, hIM⟩
  · rintro ⟨P, hP⟩
    exact ⟨((HeightOneSpectrum.equivMaximalSpectrum hR) P).asIdeal, ((HeightOneSpectrum.equivMaximalSpectrum hR) P).isMaximal, hP⟩

end IsDedekindDomain

namespace Polynomial

variable (p : R[X])

open IsDedekindDomain HeightOneSpectrum

theorem gaussNormC_one_eq_one_iff_span (P : HeightOneSpectrum R) {b : NNReal} (hb : 1 < b) :
    (p.map (algebraMap R K)).gaussNormC (adicAbv P hb) 1 ≠ 1 ↔ (Ideal.span p.coeffs.toSet ≤ P.asIdeal) := by
  rw [Ideal.span_le, Set.subset_def]
  by_cases hp0 : p = 0
  · simp [hp0]
  · --rw [← ne_eq] at hp0
    have h_supp : (p.map (algebraMap R K)).support = p.support := support_map_of_injective p <| FaithfulSMul.algebraMap_injective R K
    have hsupp_nonempty : (p.map (algebraMap R K)).support.Nonempty := by
      rw [support_nonempty, Polynomial.map_ne_zero_iff <| FaithfulSMul.algebraMap_injective R K]
      exact hp0
    simp [hp0, hsupp_nonempty, gaussNormC, ne_eq, coeff_map, one_pow, mul_one, ← adicAbv_coe_lt_one_iff (K := K) P hb]
    constructor
    · contrapose!
      simp only [forall_exists_index, and_imp]
      intro r hr hP
      rw [mem_coeffs_iff] at hr
      obtain ⟨n, hn1, hn2⟩ := hr
      rw [← h_supp] at hn1
      have hcoeffle := adicAbv_coe_le_one (K := K) P hb
      have hr' : (P.adicAbv hb) ((algebraMap R K) r) = 1 := le_antisymm (adicAbv_coe_le_one (K := K) P hb r) hP
      apply le_antisymm <| Finset.sup'_le _ _ fun b _ ↦ hcoeffle (p.coeff b)
      rw [← hr', hn2]
      apply Finset.le_sup' (f := fun x ↦ (P.adicAbv hb) ((algebraMap R K) (p.coeff x))) hn1
    · intro h
      apply ne_of_lt
      rw [Finset.sup'_lt_iff]
      intro n hn
      rw [h_supp, mem_support_iff] at hn
      exact h _ <| coeff_mem_coeffs p n hn

theorem span_coeffs_eq_top_iff_forall_gaussNormC_eq_one [Nontrivial R] (hR : ¬IsField R) {b : NNReal} (hb : 1 < b) :
    Ideal.span (p.coeffs.toSet) = ⊤ ↔
    ∀ (P : HeightOneSpectrum R), (p.map (algebraMap R K)).gaussNormC (adicAbv P hb) 1 = 1 := by
  rw [← not_iff_not, ← ne_eq]
  simp [gaussNormC_one_eq_one_iff_span, Ideal.ne_top_iff_exists hR]

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
