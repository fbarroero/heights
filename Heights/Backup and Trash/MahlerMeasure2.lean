--to Mathlib.Analysis.Polynomial.MahlerMeasure.lean

/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/

import Mathlib

/-!
# Mahler Measure

In this file ...

## Main definitions


## Main results

- `bdd_coeff_of_bdd_roots_and_lead`: if a polynomial splits its coefficients are bounded in terms of
the `NNNorm` of its leading coefficient and roots.

-/
namespace Polynomial

section Definition_and_API

variable {K : Type*} [NormedField K]

noncomputable def MahlerMeasure (p : K[X]) := ‖p.leadingCoeff‖₊ *
    ((p.roots).map (fun a ↦ max 1 ‖a‖₊)).prod

@[simp]
theorem mahler_measure_zero : (0 : K[X]).MahlerMeasure = 0 := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_one : (1 : K[X]).MahlerMeasure = 1 := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_const (z : K) : (C z).MahlerMeasure = ‖z‖₊ := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_X : (X : K[X]).MahlerMeasure = 1 := by simp [MahlerMeasure]

@[simp]
theorem mahler_measure_C_mul_X_add_C {z₁ z₀ : K} (h1 : z₁ ≠ 0) : (C z₁ * X + C z₀).MahlerMeasure =
    ‖z₁‖₊ * max 1 ‖z₁⁻¹ * z₀‖₊ := by
  simp [h1, MahlerMeasure, leadingCoeff, roots_C_mul_X_add_C z₀ h1]

@[simp]
theorem mahler_measure_degree_eq_one {p : K[X]} (h : p.degree = 1) : p.MahlerMeasure =
    ‖p.coeff 1‖₊ * max 1 ‖(p.coeff 1)⁻¹ * p.coeff 0‖₊ := by
  rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1 by rw [h])]
  simp [mahler_measure_C_mul_X_add_C (show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h)]

@[simp]
theorem mahler_measure_mul (p q : K[X]) : (p * q).MahlerMeasure =
    p.MahlerMeasure * q.MahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  simp [MahlerMeasure, mul_assoc, mul_left_comm (Multiset.map (fun x ↦ 1 ⊔ ‖x‖₊) p.roots).prod _ _,
    roots_mul (mul_ne_zero hp hq)]

lemma one_le_prod_max_one_nnnorm_roots (p : K[X]) :
    1 ≤ (p.roots.map (fun a ↦ max 1 ‖a‖₊)).prod := by
  apply Multiset.one_le_prod_of_one_le
  simp only [Multiset.mem_map]
  rintro _ ⟨a, _, rfl⟩
  exact le_max_left 1 ‖a‖₊

lemma leading_coeff_le_mahler_measure (p : K[X]) : ‖p.leadingCoeff‖₊ ≤ p.MahlerMeasure :=
  le_mul_of_one_le_right' <| one_le_prod_max_one_nnnorm_roots p

lemma prod_max_one_nnnorm_roots_le_mahler_measure_of_one_le_leading_coeff {p : K[X]}
    (hlc : 1 ≤ ‖p.leadingCoeff‖₊) : (p.roots.map (fun a ↦ max 1 ‖a‖₊)).prod ≤ p.MahlerMeasure :=
  le_mul_of_one_le_left' hlc

theorem roots_le_mahler_measure_of_one_le_leading_coeff {p : K[X]} (hlc : 1 ≤ ‖p.leadingCoeff‖₊) :
    (p.roots.map (fun x ↦ ‖x‖₊)).sup ≤ p.MahlerMeasure := by
  apply le_trans _ <| prod_max_one_nnnorm_roots_le_mahler_measure_of_one_le_leading_coeff hlc
  simp only [Multiset.sup_le, Multiset.mem_map]
  rintro _ ⟨x, hx, rfl⟩
  apply le_trans <| le_max_right 1 _
  refine Multiset.single_le_prod ?_ (1 ⊔ ‖x‖₊) (Multiset.mem_map_of_mem (fun x ↦ 1 ⊔ ‖x‖₊) hx)
  simp only [Multiset.mem_map]
  rintro _ ⟨_, _, rfl⟩
  simp

end Definition_and_API

/-!If `p` is the polynomial `a_d X ^ d + ... + a_0` then, for all `n ∈ {0, ..., d}`,
`‖a_n‖₊ ≤ ‖a_d‖₊ * d.choose n * (sup ‖r‖₊) ^ (d - n)` where `r` ranges over the roots of `p`. -/
open Classical Multiset in
theorem bdd_coeff_of_bdd_roots_and_leading_coeff {K : Type*} [NormedField K]  {p : K[X]}
    (hsplit : p.Splits (RingHom.id K)) (n : ℕ) :
    ‖p.coeff n‖₊ ≤ ‖p.leadingCoeff‖₊ * p.natDegree.choose n *
    (p.roots.map (fun a ↦ ‖a‖₊)).sup ^ (p.natDegree - n) := by
  by_cases h₀ : p = 0; simp [h₀] --exclude the zero polynomial
  by_cases h : p.natDegree < n; simp [coeff_eq_zero_of_natDegree_lt h] --may assume n ≤ p.natDegree
  rw [not_lt] at h
  simp only [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (hsplit)) h, esymm,
    Finset.sum_multiset_map_count, nsmul_eq_mul, nnnorm_mul, nnnorm_pow, nnnorm_neg, nnnorm_one,
    one_pow, mul_one, mul_assoc ‖p.leadingCoeff‖₊,
    mul_le_mul_left (nnnorm_pos.mpr (leadingCoeff_ne_zero.mpr h₀))]
  apply le_trans <| nnnorm_sum_le _ _
  simp_rw [Finset.prod_multiset_count, nnnorm_mul, nnnorm_prod, nnnorm_pow]
  let S := p.roots.powersetCard (p.natDegree - n)
  let B := (p.roots.map (fun a ↦ ‖a‖₊)).sup
  calc
      ∑ P ∈ S.toFinset, ‖(S.count P : K)‖₊ * ∏ x ∈ P.toFinset, ‖x‖₊ ^ P.count x
    ≤ ∑ P ∈ S.toFinset, ‖(S.count P : K)‖₊ * ∏ x ∈ P.toFinset, B ^ P.count x := by
          gcongr with P hP z hz
          simp only [mem_toFinset, mem_powersetCard, S] at hP
          exact Multiset.le_sup <| mem_map_of_mem (fun a ↦ ‖a‖₊) <| mem_of_le hP.1 (mem_dedup.mp hz)
  _ = ∑ P ∈ S.toFinset, ‖(S.count P : K)‖₊ * B ^ (p.natDegree - n) := by
          apply Finset.sum_congr rfl
          intro P hP
          simp_all [S, Finset.prod_pow_eq_pow_sum]
  _ ≤ ∑ P ∈ S.toFinset, (S.count P) * B ^ (p.natDegree - n) := by
          gcongr with P hP
          apply le_trans <| Nat.norm_cast_le _
          simp
  _ = (p.natDegree.choose n) * B ^ (p.natDegree - n) := by
          by_cases hB : B = 0
          by_cases hd : p.natDegree - n = 0
          · simp [S, Nat.le_antisymm h <| Nat.le_of_sub_eq_zero hd]
          · simp [hB, hd]
          · rw [← Finset.sum_mul]
            congr
            norm_cast
            simp only [← Nat.choose_symm h, S, mem_powersetCard, mem_toFinset, imp_self,
            implies_true, sum_count_eq_card, card_powersetCard]
            congr
            exact splits_iff_card_roots.mp hsplit

end Polynomial
