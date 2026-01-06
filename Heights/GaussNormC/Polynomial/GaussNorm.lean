/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib
/-!
# Gauss norm for polynomials
This file defines the Gauss norm for polynomials. Given a polynomial `p` in `R[X]`, a function
`v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
values of `v (p.coeff i) * c ^ i` for all `i` in the support of `p`.


## Main Definitions and Results
* `Polynomial.gaussNormC` is the supremum of the set of all values of `v (p.coeff i) * c ^ i`
  for all `i` in the support of `p`, where `p` is a polynomial in `R[X]`, `v : R → ℝ` is a function
  and `c` is a  real number.
* `Polynomial.gaussNormC_coe_powerSeries`: the Gauss norm of a polynomial is equal to its
  Gauss norm as a power series.
* `Polynomial.gaussNormC_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.
* `Polynomial.gaussNormC_eq_zero_iff`: if `v x = 0 ↔ x = 0` for all `x : R`, then the Gauss
  norm is zero if and only if the polynomial is zero.
-/

namespace IsNonarchimedean

variable {R : Type*} [Semiring R] [LinearOrder R] {a b : R} {m n : ℕ}

-- this goes to Mathlib.Algebra.Order.Ring.IsNonarchimedean

open Finset in
lemma apply_sum_eq_of_lt {α β F : Type*} [AddCommGroup α] [FunLike F α R] [AddGroupSeminormClass F α R] {f : F}
    (nonarch : IsNonarchimedean f) {s : Finset β} {l : β → α} {k : β} (hk : k ∈ s)
    (hmax : ∀ j ∈ s, j ≠ k → f (l j) < f (l k)) : f (∑ i ∈ s, l i) = f (l k) := by
  have : s.Nonempty := by use k
  revert k
  induction this using Nonempty.cons_induction with
  | singleton a => simp_all
  | cons a s _ hs _ =>
    intro k hk hmax
    by_cases ha : k = a
    · rw [sum_cons, ha]
      apply add_eq_left_of_lt nonarch
      grw [apply_sum_le_sup_of_isNonarchimedean nonarch hs]
      grind [sup'_lt_iff]
    · simp only [mem_cons, false_or, forall_eq_or_imp, ha] at hk hmax
      grind [add_eq_right_of_lt nonarch]

end IsNonarchimedean


variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)

namespace Polynomial

variable (p : R[X])

/--
def gaussNormC : ℝ := if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (v (p.coeff i) * c ^ i) else 0

@[simp]
lemma gaussNormC_zero : gaussNormC v c 0 = 0 := by simp [gaussNormC]

theorem exists_eq_gaussNormC [ZeroHomClass F R ℝ] : ∃ i, p.gaussNormC v c = v (p.coeff i) * c ^ i := by
  by_cases h_supp : p.support.Nonempty
  · simp only [gaussNormC, h_supp]
    obtain ⟨i, hi1, hi2⟩ := Finset.exists_mem_eq_sup' h_supp fun i ↦ (v (p.coeff i) * c ^ i)
    exact ⟨i, hi2⟩
  · simp_all

private lemma sup'_nonneg_of_ne_zero [NonnegHomClass F R ℝ] {p : R[X]} (h : p.support.Nonempty)
    {c : ℝ} (hc : 0 ≤ c) : 0 ≤ p.support.sup' h fun i ↦ (v (p.coeff i) * c ^ i) := by
  simp only [Finset.le_sup'_iff, mem_support_iff]
  use p.natDegree
  simp_all only [support_nonempty, ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true,
    true_and]
  positivity

private lemma aux_bdd [ZeroHomClass F R ℝ] : BddAbove {x | ∃ i, v (p.coeff i) * c ^ i = x} := by
  let f : p.support → ℝ := fun i ↦ v (p.coeff i) * c ^ i.1
  have h_fin : (f '' ⊤ ∪ {0}).Finite := by
    apply Set.Finite.union _ <| Set.finite_singleton 0
    apply Set.Finite.image f
    rw [Set.top_eq_univ, Set.finite_univ_iff, ← @Finset.coe_sort_coe]
    exact Finite.of_fintype p.support
  apply Set.Finite.bddAbove <| Set.Finite.subset h_fin _
  intro x hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi]
  by_cases hi : i ∈ p.support
  · left
    use ⟨i, hi⟩
    simp [f]
  · right
    simp [not_mem_support_iff.mp hi]

private lemma gaussNormC_nonempty : {x | ∃ i, v (p.coeff i) * c ^ i = x}.Nonempty := by
  use v (p.coeff 0) * c ^ 0, 0

@[simp]
theorem gaussNormC_coe_powerSeries [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    {c : ℝ} (hc : 0 ≤ c) : (p.toPowerSeries).gaussNormC v c = p.gaussNormC v c:= by
  by_cases hp : p = 0; simp [hp]
  have h_supp : p.support.Nonempty := support_nonempty.mpr hp
  simp only [gaussNormC, support_nonempty, ne_eq, hp, not_false_eq_true, ↓reduceDIte,
    PowerSeries.gaussNormC, coeff_coe]
  apply le_antisymm
  · apply Real.sSup_le  _ <| sup'_nonneg_of_ne_zero v h_supp hc
    intro x hx
    obtain ⟨i, hi⟩ := hx
    rw [← hi]
    by_cases h : i ∈ p.support
    · exact Finset.le_sup' (fun j ↦ v (p.coeff j) * c ^ j) h
    · simp_all [sup'_nonneg_of_ne_zero v h_supp hc]
  · obtain ⟨i, hi⟩ := exists_eq_gaussNormC v c p
    simp only [gaussNormC, h_supp, ↓reduceDIte] at hi
    rw [hi]
    apply le_csSup (aux_bdd v c p)
    simp

@[simp]
theorem gaussNormC_eq_zero_iff [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) {c : ℝ} (hc : 0 < c) : p.gaussNormC v c = 0 ↔ p = 0 := by
  rw [← gaussNormC_coe_powerSeries _ _ (le_of_lt hc), PowerSeries.gaussNormC_eq_zero_iff h_eq_zero hc
    (by simpa only [coeff_coe] using aux_bdd v c p), coe_eq_zero_iff]

theorem gaussNormC_nonneg {c : ℝ} (hc : 0 ≤ c) [NonnegHomClass F R ℝ] : 0 ≤ p.gaussNormC v c := by
  by_cases hp : p.support.Nonempty
  · simp_all [gaussNormC, sup'_nonneg_of_ne_zero, -Finset.le_sup'_iff]
  · simp [gaussNormC, hp]

@[simp]
lemma gaussNormC_C [ZeroHomClass F R ℝ] (r : R) : (C r).gaussNormC v c = v r := by
  by_cases hr : r = (0 : R); simp [gaussNormC, hr]
  simp [gaussNormC, support_C, hr]

@[simp]
theorem gaussNormC_monomial [ZeroHomClass F R ℝ] (n : ℕ) (r : R) :
    (monomial n r).gaussNormC v c = v r * c ^ n := by
  by_cases hr : r = 0; simp [gaussNormC, hr]
  simp [gaussNormC, support_monomial, hr]

lemma le_gaussNormC [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (p : R[X]) {c : ℝ}
    (hc : 0 ≤ c) (i : ℕ) : v (p.coeff i) * c ^ i ≤ p.gaussNormC v c := by
  rw [← gaussNormC_coe_powerSeries _ _ hc, ← coeff_coe]
  apply PowerSeries.le_gaussNormC
  simpa using aux_bdd v c p

 -/

--This goes to Mathlib.RingTheory.Polynomial.GaussNorm

@[simp]
lemma gaussNorm_c_eq_zero [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] :
    p.gaussNorm v 0 = v (p.coeff 0) := by
  have : (fun i ↦ v (p.coeff i) * 0 ^ i) = fun i ↦ if i = 0 then v (p.coeff 0) else 0 := by
      aesop
  rcases eq_or_ne (p.coeff 0) 0 with _ | hcoeff0
  · simp_all [gaussNorm]
  · have : p.support.Nonempty := by
      use 0
      simp [hcoeff0]
    apply le_antisymm
    · aesop (add norm (by simp [gaussNorm, Finset.sup'_le_iff]))
    · grind [p.le_gaussNorm v (le_refl 0) 0]

/-- There exists a minimal index `i` such that the Gauss norm of `p` at `c` is attained at `i`. -/
lemma exists_min_eq_gaussNorm [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (p : R[X]) (hc : 0 ≤ c) :
    ∃ i, p.gaussNorm v c = v (p.coeff i) * c ^ i ∧
    ∀ j, j < i →  v (p.coeff j) * c ^ j < p.gaussNorm v c := by
  have h_nonempty : {i | gaussNorm v c p = v (p.coeff i) * c ^ i}.Nonempty := by
    obtain ⟨i, hi⟩ := exists_eq_gaussNorm v c p
    exact ⟨i, Set.mem_setOf.mpr hi⟩
  refine ⟨Nat.find h_nonempty, Nat.find_spec h_nonempty, ?_⟩
  intro j hj_lt
  simp only [Nat.lt_find_iff, Set.mem_setOf_eq] at hj_lt
  exact lt_of_le_of_ne (le_gaussNorm v _ hc j) fun a ↦ hj_lt j (Nat.le_refl j) a.symm

/-- The Gauss Norm is nonarchimedean if `v` is nonarchimedean. -/
theorem isNonarchimedean_gaussNorm [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    (hna : IsNonarchimedean v) {c : ℝ} (hc : 0 ≤ c) : IsNonarchimedean (gaussNorm v c) := by
  intro p q
  rcases eq_or_ne p 0 with hp | _
  · simp [hp]
  rcases eq_or_ne q 0 with hq | _
  · simp [hq]
  rcases eq_or_ne (p + q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg]
  simp only [gaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte,
    Finset.sup'_le_iff]
  intro i _
  calc
  v (p.coeff i + q.coeff i) * c ^ i
    ≤ max (v (p.coeff i)) (v (q.coeff i)) * c ^ i := by
    gcongr
    exact hna (p.coeff i) (q.coeff i)
  _ = max (v (p.coeff i) * c ^ i) (v (q.coeff i) * c ^ i) := by
    rw [max_mul_of_nonneg _ _ (pow_nonneg hc _)]
  _ ≤ max (gaussNorm v c p) (gaussNorm v c q) := by
    apply max_le_max <;>
    exact le_gaussNorm v _ hc i

open Finset in
/-- The Gauss Norm is submultiplicative if `v` is nonarchimedean. -/
theorem gaussNorm_mul_le_mul_gaussNorm [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] [MulHomClass F R ℝ]
    (hna : IsNonarchimedean v) (p q : R[X]) (hc : 0 ≤ c) :
    (p * q).gaussNorm v c ≤ p.gaussNorm v c * q.gaussNorm v c := by
  rcases eq_or_ne (p * q) 0 with hpq | hpq
  · simp [hpq, hc, gaussNorm_nonneg, mul_nonneg]
  have h_supp_p : p.support.Nonempty := support_nonempty.mpr <| left_ne_zero_of_mul hpq
  have h_supp_q : q.support.Nonempty := support_nonempty.mpr <| right_ne_zero_of_mul hpq
  simp only [gaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte, h_supp_p,
    h_supp_q, sup'_le_iff, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  intro i _
  obtain ⟨j, _, _⟩ := IsNonarchimedean.finset_image_add_of_nonempty hna _ nonempty_range_add_one
  calc
  v (∑ j ∈ range (i + 1), p.coeff j * q.coeff (i - j)) * c ^ i
  _ ≤ v (p.coeff j * q.coeff (i - j)) * c ^ i := by gcongr
  _ = (v (p.coeff j) * c ^ j) * (v (q.coeff (i - j)) * c ^ (i - j)) := by
      have : c ^ j * c ^ (i - j) = c ^ i := by simp_all [← pow_add]
      grind
  _ ≤ (p.support.sup' _ fun i ↦ v (p.coeff i) * c ^ i)
    * q.support.sup' _ fun i ↦ v (q.coeff i) * c ^ i := by
      have hp_le := p.le_gaussNorm v hc j
      have hq_le := q.le_gaussNorm v hc (i - j)
      have := p.gaussNorm_nonneg v hc
      simp_all only [gaussNorm, ↓reduceDIte]
      gcongr

----

open Finset in
/-- If `v` is nonarchimedean the Gauss norm of a product is at least the product of the Gauss norms.
-/
theorem mul_gaussNorm_le_gaussNorm_mul {R F : Type*} [Ring R] [FunLike F R ℝ] [ZeroHomClass F R ℝ]
    [NonnegHomClass F R ℝ] [MulHomClass F R ℝ] [AddGroupSeminormClass F R ℝ]
    {v : F} (hna : IsNonarchimedean v) (p q : R[X]) (hc : 0 < c) :  ---set 1 ≤ c
    p.gaussNorm v c * q.gaussNorm v c ≤ (p * q).gaussNorm v c := by
  have hc0 : 0 ≤ c := le_of_lt hc
  obtain ⟨i, hi_p, hlt_p⟩ := exists_min_eq_gaussNorm v c p hc0
  obtain ⟨j, hj_q, hlt_q⟩ := exists_min_eq_gaussNorm v c q hc0
  -- i and j are the minimal indices where the gauss norms are attained
  wlog hvpq : v (p.coeff i) ≠ 0 ∧ v (q.coeff j) ≠ 0
  · grind [mul_mul_mul_comm, gaussNorm_nonneg]
  have := hvpq.1
  have := hvpq.2
  apply le_of_eq_of_le _ <| (p * q).le_gaussNorm v hc0 (i + j)
  -- gaussNorm v c p * gaussNorm v c q is actually equal to v ((p * q).coeff (i + j)) * c ^ (i + j)
  rw [hi_p, hj_q, coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    IsNonarchimedean.apply_sum_eq_of_lt hna (k := i) (by simp)]
  · grind
  intro x hx hneq
  apply lt_of_mul_lt_mul_right _ <| pow_nonneg hc0 (i + j)
  convert_to v (p.coeff x) * c ^ x * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) <
    v (p.coeff i) * v (q.coeff j) * c ^ (i + j)
  · have : x + (i + j - x) = i + j := by simp_all
    grind
  · simp
  rcases lt_or_gt_of_ne hneq
  · calc
    v (p.coeff x) * c ^ x * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
    _ ≤ v (p.coeff x) * c ^ x * gaussNorm v c q := by
        gcongr
        exact q.le_gaussNorm v hc0 (i + j - x)
    _ = v (p.coeff x) * c ^ x * (v (q.coeff j) * c ^ j) := by
        rw [hj_q]
    _ < v (p.coeff i) * c ^ i * (v (q.coeff j) * c ^ j) := by
        gcongr 1
        grind
    _ = v (p.coeff i) * v (q.coeff j) * c ^ (i + j) := by
        ring
  · calc
    v (p.coeff x) * c ^ x * (v (q.coeff (i + j - x)) * c ^ (i + j - x))
    _ ≤ gaussNorm v c p * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by
        gcongr
        exact p.le_gaussNorm v hc0 x
    _ = v (p.coeff i) * c ^ i * (v (q.coeff (i + j - x)) * c ^ (i + j - x)) := by
        rw [hi_p]
    _ < v (p.coeff i) * c ^ i * (v (q.coeff j) * c ^ j) := by
        gcongr 1
        grind
    _ = v (p.coeff i) * v (q.coeff j) * c ^ (i + j) := by
        ring

/- Note:
Not sure this version is useful
-/
open Finset in
theorem mul_gaussNorm_le_gaussNorm_mul' {R F : Type*} [Ring R] [IsDomain R] [FunLike F R ℝ] [ZeroHomClass F R ℝ]
    [NonnegHomClass F R ℝ] [MulHomClass F R ℝ] [AddGroupSeminormClass F R ℝ]
    {v : F} (hna : IsNonarchimedean v) (p q : R[X]) (hc : 0 ≤ c) :  ---set 1 ≤ c
    p.gaussNorm v c * q.gaussNorm v c ≤ (p * q).gaussNorm v c := by
  rcases eq_or_lt_of_le hc with hc0 | hc0
  · rcases eq_or_ne (p * q) 0 <;> aesop
  exact mul_gaussNorm_le_gaussNorm_mul c hna p q hc0

/-- If `v` is nonarchimedean the Gauss norm of a product is the product of the Gauss norms. -/
theorem gaussNorm_mul {R F : Type*} [Ring R] [FunLike F R ℝ] [ZeroHomClass F R ℝ]
    [NonnegHomClass F R ℝ] [MulHomClass F R ℝ] [AddGroupSeminormClass F R ℝ] {v : F}
    (hna : IsNonarchimedean v) (p q : R[X]) (hc : 0 < c) :
    (p * q).gaussNorm v c = p.gaussNorm v c * q.gaussNorm v c :=
  le_antisymm (gaussNorm_mul_le_mul_gaussNorm v c hna p q (le_of_lt hc))
  <| mul_gaussNorm_le_gaussNorm_mul c hna p q hc

instance gaussNorm_isAbsoluteValue {R F : Type*} [Ring R] [FunLike F R ℝ] [ZeroHomClass F R ℝ]
    [NonnegHomClass F R ℝ] [MulHomClass F R ℝ] [AddGroupSeminormClass F R ℝ] {v : F}
    (hna : IsNonarchimedean v) (h_eq_zero : ∀ x : R, v x = 0 → x = 0) (hc : 0 < c) :
    IsAbsoluteValue (gaussNorm v c) := {
  abv_nonneg' p := p.gaussNorm_nonneg v <| le_of_lt hc
  abv_eq_zero' := gaussNorm_eq_zero_iff v _ h_eq_zero hc
  abv_add' p q := by
    grind [isNonarchimedean_gaussNorm v hna (le_of_lt hc) p q, gaussNorm_nonneg]
  abv_mul' p q := gaussNorm_mul c hna p q hc}



end Polynomial
/-
namespace PowerSeries

@[simp]
theorem gaussNormC_C [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] {c : ℝ} (hc : 0 ≤ c) (r : R) :
    (C R r).gaussNorm v c = v r := by
  simp [← @Polynomial.coe_C, hc]

@[simp]
theorem gaussNormC_monomial [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] {c : ℝ} (hc : 0 ≤ c)
    (n : ℕ) (r : R) : (monomial R n r).gaussNorm v c = v r * c ^ n := by
  simp [← @Polynomial.coe_monomial, hc]

end PowerSeries
 -/
--#min_imports

namespace Polynomial
section AbsoluteValue

variable (v : AbsoluteValue R ℝ)

--TODO



end AbsoluteValue

end Polynomial
