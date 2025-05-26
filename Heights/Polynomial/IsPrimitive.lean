import Mathlib

variable {R : Type*} [CommSemiring R]

namespace Polynomial

variable (p : R[X])

--PR this
theorem isPrimitive_of_span_coeffs_eq_top (h : Ideal.span (p.coeffs.toSet) = ⊤) :
    IsPrimitive p := by
  by_contra h
  simp only [IsPrimitive, not_forall, Classical.not_imp] at h
  obtain ⟨r, hr1, hr2⟩ := h
  rw [C_dvd_iff_dvd_coeff] at hr1
  have : Ideal.span (p.coeffs.toSet) ≤ Ideal.span {r} := by
    rw [Ideal.span_le, Set.subset_def]
    intro a ha
    rw [Finset.mem_coe, mem_coeffs_iff] at ha
    rcases ha with ⟨n, hn1, hn2⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton, hn2]
    exact hr1 n
  simp_all

section NormalizedGCDMonoid

variable [CommRing R] [IsDomain R] [NormalizedGCDMonoid R]

--needs GCD monoid
theorem isPrimitive_iff_span_coeffs_eq_top  : IsPrimitive p ↔ Ideal.span (p.coeffs.toSet) = ⊤ := by
  have hset : p.coeffs.toSet = Set.range (fun i : p.support ↦ p.coeff i) := by
    ext a
    simp [mem_coeffs_iff]
    apply Iff.intro
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only [not_false_eq_true]
    · intro a_1
      obtain ⟨w, h⟩ := a_1
      obtain ⟨left, right⟩ := h
      subst right
      apply Exists.intro
      · apply And.intro
        on_goal 2 => {rfl
        }
        · simp_all only [not_false_eq_true]
  --rw [Ideal.eq_top_iff_one, hset, Ideal.mem_span_range_iff_exists_fun]
  refine ⟨?_, fun a ↦ isPrimitive_of_span_coeffs_eq_top p a⟩
  sorry

end NormalizedGCDMonoid

end Polynomial
