import Mathlib

namespace Polynomial

section Primitive

variable {R : Type*} [CommSemiring R] (p : R[X])

--PR this
theorem isPrimitive_of_span_coeffs_eq_top {R : Type*} [CommSemiring R] (p : R[X]) (h : Ideal.span (p.coeffs.toSet) = ⊤) :
    IsPrimitive p := by
  by_contra h
  simp only [IsPrimitive, not_forall, Classical.not_imp] at h
  obtain ⟨r, hr, _⟩ := h
  rw [C_dvd_iff_dvd_coeff] at hr
  have : Ideal.span (p.coeffs.toSet) ≤ Ideal.span {r} := by
    rw [Ideal.span_le, Set.subset_def]
    intro a ha
    rw [Finset.mem_coe, mem_coeffs_iff] at ha
    rcases ha with ⟨n, _, hn⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton, hn]
    exact hr n
  simp_all

end Primitive
section NormalizedGCDMonoid

variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R] (p : R[X])

theorem span_content_eq_span_coeffs [NormalizedGCDMonoid R] (p : R[X]) :
    Ideal.span {p.content} = Ideal.span (p.coeffs.toSet) := by

  apply le_antisymm
  · rw [Ideal.span_singleton_le_iff_mem]

    sorry
  sorry

--PRd
theorem isPrimitive_iff_span_coeffs_eq_top : IsPrimitive p ↔ Ideal.span (p.coeffs.toSet) = ⊤ := by
  /- have hset : p.coeffs.toSet = Set.range (fun i : p.support ↦ p.coeff i) := by
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
        · simp_all only [not_false_eq_true] -/
  --rw [Ideal.eq_top_iff_one, hset, Ideal.mem_span_range_iff_exists_fun]
  refine ⟨?_, fun a ↦ isPrimitive_of_span_coeffs_eq_top p a⟩
  contrapose!
  intro h
  have : Submodule.IsPrincipal (Ideal.span (p.coeffs.toSet)) := by
    apply IsBezout.isPrincipal_of_FG
    use p.coeffs
  simp only [IsPrimitive, not_forall]
  let r := Submodule.IsPrincipal.generator (Ideal.span (p.coeffs.toSet))
  use r
  have hr1 : C r ∣ p := by
    rw [C_dvd_iff_dvd_coeff]
    intro n
    have : p.coeff n ∈ Ideal.span (p.coeffs.toSet) := by
      by_cases h_coeff : p.coeff n ≠ 0;
      · rw [← Ideal.span_singleton_le_iff_mem]
        gcongr
        simp only [Set.singleton_subset_iff, Finset.mem_coe]
        exact coeff_mem_coeffs p n h_coeff
      · simp_all
    rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at this
    obtain ⟨a, ha⟩ := this
    simp [ha, r]
  have hr2 : ¬ IsUnit r := by
    by_contra hr
    apply h
    rw [← Ideal.span_singleton_eq_top] at hr
    simp_all only [ne_eq, Ideal.span_singleton_generator, r]
  exact not_forall.mp fun a ↦ hr2 (a hr1)
  /-


  rw [Ideal.eq_top_iff_one, hset, Ideal.mem_span_range_iff_exists_fun, isPrimitive_iff_content_eq_one, content]
  intro h

 -/

end NormalizedGCDMonoid

end Polynomial
