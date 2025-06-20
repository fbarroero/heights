/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib

/-!
# The content ideal of a polynomial

## Main Definitions
Let `p : R[X]`.
- `p.contentIdeal` is the `Ideal R` generated by the coefficients of `p`.
-

## Main Results
-
-

-/

namespace Polynomial

open Ideal

variable {R : Type*} [Semiring R] (p : R[X])

/-- The content ideal of a polynomial `p` is the ideal generated by its coefficients. -/
def contentIdeal := span (p.coeffs.toSet)

theorem contentIdeal_def : p.contentIdeal = span (p.coeffs.toSet) := rfl

@[simp]
theorem contenIdeal_zero : (0 : R[X]).contentIdeal = ⊥ := by
  simp [contentIdeal_def]

theorem coeff_mem_contentIdeal (n : ℕ) : p.coeff n ∈ p.contentIdeal := by
  by_cases h : p.coeff n = 0
  · simp [h]
  · rw [contentIdeal_def, mem_span]
    exact fun _ hJ ↦ Set.mem_of_subset_of_mem hJ <| Finset.mem_coe.mpr <| coeff_mem_coeffs p n h

@[simp]
theorem contentIdeal_monomial (n : ℕ) (r : R) : (monomial n r).contentIdeal = Ideal.span {r} := by
  by_cases h : r = 0
  · simp [h, Set.singleton_zero]
  · rw [contentIdeal_def, coeffs_monomial _ h, Finset.coe_singleton]

@[simp]
theorem contentIdeal_C (r : R) : (C r).contentIdeal = Ideal.span {r} := by
  rw [← monomial_zero_left]
  exact contentIdeal_monomial 0 r

theorem contentIdeal_X_mul (p : R[X]) : (X * p).contentIdeal = p.contentIdeal := by
  simp [contentIdeal_def]

  sorry


section CommSemiring

variable {R : Type*} [CommSemiring R] --(p : R[X])

theorem contentIdeal_le_contentIdeal_of_dvd {p q : R[X]} (hpq : p ∣ q) :
    q.contentIdeal ≤ p.contentIdeal := by
  rw [contentIdeal_def, span_le]
  intro _ h1
  rw [Finset.mem_coe, mem_coeffs_iff] at h1
  obtain ⟨_, _, h2⟩ := h1
  obtain ⟨_, h3⟩ := hpq
  rw [h3, coeff_mul] at h2
  rw [h2]
  exact Ideal.sum_mem _ <| fun _ _ ↦ mul_mem_right _ _ <| coeff_mem_contentIdeal p _

/-- If the coefficients of `p` geneate the whole ring, then `p` is primitive. -/
theorem isPrimitive_of_contentIdeal_eq_top {p : R[X]} (h : p.contentIdeal = ⊤) :
    IsPrimitive p := by
  by_contra h
  simp only [IsPrimitive, not_forall, Classical.not_imp] at h
  obtain ⟨r, hr, _⟩ := h
  apply contentIdeal_le_contentIdeal_of_dvd at hr
  simp_all

end CommSemiring

section IsBezout

variable {R : Type*} [CommSemiring R] [IsBezout R] (p : R[X])

/-- The polynomial `p` is primitive if and only if the coefficients of `p` geneate the whole ring.
-/
theorem isPrimitive_iff_contentIdeal_eq_top :
    IsPrimitive p ↔ p.contentIdeal = ⊤ := by
  refine ⟨?_, fun a ↦ isPrimitive_of_contentIdeal_eq_top a⟩
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
    sorry
    --simp_all [← Ideal.span_singleton_eq_top, r]
  exact not_forall.mp fun a ↦ hr2 (a hr1)

end IsBezout

end Polynomial
