/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/

import Mathlib.RingTheory.Polynomial.Content

/-!
# GCD structures on polynomials

Definitions and basic results about polynomials over GCD domains, particularly their contents
and primitive polynomials.

## Main Definitions
Let `p : R[X]`.
- `p.content` is the `gcd` of the coefficients of `p`.
- `p.IsPrimitive` indicates that `p.content = 1`.

## Main Results
- `Polynomial.content_mul`: if `p q : R[X]`, then `(p * q).content = p.content * q.content`.
- `Polynomial.NormalizedGcdMonoid`: the polynomial ring of a GCD domain is itself a GCD domain.

## Note

This has nothing to do with minimal polynomials of primitive elements in finite fields.

-/


namespace Polynomial

section Primitive

variable {R : Type*} [CommSemiring R]

def contentIdeal (p : R[X]) := Ideal.span (p.coeffs.toSet)

theorem contentIdeal_def (p : R[X]) : p.contentIdeal = Ideal.span (p.coeffs.toSet) := rfl

theorem coeff_mem_contentIdeal (p : R[X]) (n : ℕ) :
    p.coeff n ∈ p.contentIdeal := by
  by_cases h : p.coeff n = 0
  · simp [contentIdeal_def, h]
  · simp only [contentIdeal_def, Ideal.mem_span]
    exact fun _ hJ ↦ Set.mem_of_subset_of_mem hJ <| Finset.mem_coe.mpr <| coeff_mem_coeffs p n h

/-- If the coefficients of `p` geneate the whole ring, then `p` is primitive. -/
theorem isPrimitive_of_span_coeffs_eq_top {p : R[X]} (h : p.contentIdeal = ⊤) :
    IsPrimitive p := by
  by_contra h
  simp only [IsPrimitive, not_forall, Classical.not_imp] at h
  obtain ⟨r, hr, _⟩ := h
  rw [C_dvd_iff_dvd_coeff] at hr
  have : Ideal.span (p.coeffs.toSet) ≤ Ideal.span {r} := by
    rw [Ideal.span_le]
    intro a ha
    rw [Finset.mem_coe, mem_coeffs_iff] at ha
    rcases ha with ⟨n, _, hn⟩
    rw [SetLike.mem_coe, Ideal.mem_span_singleton, hn]
    exact hr n
  simp_all [contentIdeal]

end Primitive

variable {R : Type*} [CommRing R] [IsDomain R]

section NormalizedGCDMonoid

variable [NormalizedGCDMonoid R]


section PrimPart


end PrimPart

end NormalizedGCDMonoid

section IsBezout

variable [IsBezout R]

omit [IsDomain R] in
/-- The polynomial `p` is primitive if and only if the coefficients of `p` geneate the whole ring.
-/
theorem isPrimitive_iff_span_coeffs_eq_top (p : R[X]) :
    IsPrimitive p ↔ Ideal.span (p.coeffs.toSet) = ⊤ := by
  refine ⟨?_, fun a ↦ isPrimitive_of_span_coeffs_eq_top a⟩
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
    have := p.coeff_mem_contentIdeal n
    rw [contentIdeal, Submodule.IsPrincipal.mem_iff_eq_smul_generator] at this
    obtain ⟨a, ha⟩ := this
    simp [ha, r]
  have hr2 : ¬IsUnit r := by
    by_contra hr
    apply h
    simp_all [← Ideal.span_singleton_eq_top, r]
  exact not_forall.mp fun a ↦ hr2 (a hr1)

end IsBezout

end Polynomial
