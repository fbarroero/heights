--to Mathlib.NumberTheory.MahlerMeasure.lean

/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Heights.IntegralMahlerMeasure
import Heights.ofFn

namespace Polynomial

section Int

open Int

open Finset in
theorem card_eq_of_natDegree_le_of_coeff_le {n : ℕ} (hn : 1 ≤ n) {B₁ B₂ : Fin n → ℝ}
    (h_B : ∀ i, ceil (B₁ i) ≤ floor (B₂ i)) :
    Nat.card {p : ℤ[X] // p.natDegree < n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i} =
    ∏ i : Fin n, (floor (B₂ i) - ceil (B₁ i) + 1)  := by
  let Bp := fun i ↦ floor (B₂ i)
  let Bm := fun i ↦ ceil (B₁ i)
  let Box := Icc Bm Bp
  let BoxPoly := {p : ℤ[X] // p.natDegree < n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i}
  have hf (p : BoxPoly) : (fun i : Fin n ↦ p.val.coeff i) ∈ Box := by
    simp only [mem_Icc, Box, Bm, Bp]
    obtain ⟨val, h_deg, bounds⟩ := p
    refine ⟨fun i ↦ ceil_le.mpr (bounds i).1, fun i ↦ le_floor.mpr (bounds i).2⟩
  let f : BoxPoly → Box := fun p => ⟨fun i ↦ p.val.coeff i, hf p⟩
  let g : Box → BoxPoly := fun p => ⟨ofFn n p.val, by
    refine ⟨ofFn_natDegree_lt hn p.val, ?_⟩
    intro i
    obtain ⟨val, prop⟩ := p
    simp only [mem_Icc, Box, Bm, Bp] at prop
    simp only [coeff_eq_val_of_lt val i.2, Fin.cast_val_eq_self]
    refine ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩
    ⟩
  have hfBij : f.Bijective := by
    refine Function.bijective_iff_has_inverse.mpr ⟨g, ?_, fun _ ↦ by simp [f, g]⟩
    intro p
    ext i
    simp only [Bm, f, Box, Bp, g, BoxPoly]
    by_cases h : i < n
    · simp [ofFn, h]
    · rw [not_lt] at h
      simp only [h, coeff_eq_zero_of_ge]
      rw [coeff_eq_zero_of_natDegree_lt]
      omega
  rw [Nat.card_eq_of_bijective f hfBij]
  simp only [Box, Nat.card_eq_finsetCard (Icc Bm Bp), Pi.card_Icc,
    card_Icc, Bp, Bm, prod_const, card_univ, Fintype.card_fin, sub_neg_eq_add]
  push_cast
  congr
  ext i
  specialize h_B i
  rw [ofNat_toNat, add_sub_right_comm ⌊B₂ i⌋ 1 ⌈B₁ i⌉]
  apply max_eq_left
  omega

/- open Int in
--inutile? forse API in generale
theorem bound {p : ℤ[X]} {n : ℕ} {B : NNReal} (h₀ : p ≠ 0) (h_deg : p.natDegree ≤ n)
    (h_lead : ‖p.leadingCoeff‖₊ ≤ B)
    (h_roots : (((p.map (castRingHom ℂ)).roots).map (fun a ↦ ‖a‖₊)).sup ≤ B) :
    (p.map (castRingHom ℂ)).MahlerMeasure ≤ B ^ (n + 1) := by
  have h_B : 1 ≤ B := by
    apply le_trans _ h_lead
    rw [← Polynomial.leadingCoeff_ne_zero] at h₀
    rw [← NNReal.natCast_natAbs]
    norm_cast
    refine Nat.one_le_iff_ne_zero.mpr ?_
    exact natAbs_ne_zero.mpr h₀
  have h₀' : ¬map (castRingHom ℂ) p = 0 := by
    rw [← ne_eq]
    rw [Polynomial.map_ne_zero_iff (castRingHom ℂ).injective_int ]
    exact h₀
  have h_deg_eq : (map (castRingHom ℂ) p).natDegree =  p.natDegree := by
    simp only [natDegree_map_eq_iff, eq_intCast, ne_eq, cast_eq_zero, leadingCoeff_eq_zero]
    exact Decidable.not_or_of_imp (congrArg natDegree)
  have : ‖(map (castRingHom ℂ) p).leadingCoeff‖₊ = ‖p.leadingCoeff‖₊ := by
    rw [← Complex.nnnorm_intCast]
    congr
    rw [leadingCoeff, leadingCoeff]
    simp [h_deg_eq]
  calc
  (p.map (castRingHom ℂ)).MahlerMeasure
    ≤ ‖(map (castRingHom ℂ) p).leadingCoeff‖₊ * B ^ p.natDegree := by
    rw [MahlerMeasure]
    gcongr
    simp only [Multiset.sup_le, Multiset.mem_map, mem_roots', ne_eq, h₀', not_false_eq_true,
      IsRoot.def, true_and, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at h_roots
    have : p.natDegree = (Multiset.map (fun a ↦ 1 ⊔ ‖a‖₊) (map (castRingHom ℂ) p).roots).card := by
      rw [← h_deg_eq,
        Polynomial.natDegree_eq_card_roots (IsAlgClosed.splits (map (castRingHom ℂ) p))]
      simp
    rw [this]
    apply Multiset.prod_le_pow_card (Multiset.map (fun a ↦ 1 ⊔ ‖a‖₊) (map (castRingHom ℂ) p).roots) B
    intro x a
    simp_all only [ne_eq, Multiset.card_map, Multiset.mem_map, mem_roots', not_false_eq_true, IsRoot.def, true_and]
    obtain ⟨w, h⟩ := a
    obtain ⟨left, right⟩ := h
    subst right
    simp_all only [sup_le_iff, and_self]
  _ ≤ ‖(map (castRingHom ℂ) p).leadingCoeff‖₊ * B ^ n := by
    gcongr
    exact h_B
  _ ≤ B ^ (n + 1) := by
    rw [this, pow_succ' B n]
    exact mul_le_mul_right' h_lead (B ^ n) -/

open Int in
theorem card1 {n : ℕ} (hn : 1 ≤ n) (B : NNReal) :
    Nat.card {p : ℤ[X] // p.natDegree < n ∧ ∀ i : Fin n, |p.coeff i| ≤
    (n.choose i * B ^ (n - i) : ℝ)} =
    ∏ i : Fin n, (2 * Nat.floor (n.choose i * B ^ (n - i)) + 1) := by
  let B₁ := fun i : Fin n ↦ - (n.choose i * B ^ (n - i) : ℝ)
  let B₂ := fun i : Fin n ↦ (n.choose i * B ^ (n - i) : ℝ)
  have h_B (i : Fin n) : ⌈B₁ i⌉ ≤ ⌊B₂ i⌋ := by
    simp only [ceil_neg, neg_le_self_iff, le_floor, cast_zero, B₁, B₂]
    exact_mod_cast zero_le (↑(n.choose ↑i) * B ^ (n - ↑i))
  zify
  have (i : Fin n) : 0 ≤ (n.choose i) * B ^ (n - i) := by positivity
  --have := fun (i : Fin (n + 1)) ↦ Int.natCast_floor_eq_floor (this i)
  have (i : Fin n) : (⌊(n.choose i) * B ^ (n - i)⌋₊ : ℤ) = ⌊(n.choose i) * (B : ℝ) ^ (n - i)⌋ := by
    apply natCast_floor_eq_floor
    exact this i
  conv => enter [2,2]; ext i; enter [1]; rw [this, two_mul, ← sub_neg_eq_add, ← ceil_neg]
  have := card_eq_of_natDegree_le_of_coeff_le hn h_B
  simp [B₁, B₂] at this
  rw [← this]
  congr
  ext p
  refine and_congr (by norm_cast) ?_
  refine forall_congr' ?_
  intro i
  rw [abs_le]

open Int in
def funct (n : ℕ) (B : NNReal) :
    {p : ℤ[X] // p.natDegree < n ∧ (p.map (castRingHom ℂ)).MahlerMeasure ≤ B} →
    {p : ℤ[X] // p.natDegree < n ∧ ∀ i : Fin n, |p.coeff i| ≤ (n.choose i * B ^ (n - i) : ℝ)} := by
  apply Subtype.map id
  intro p hp
  obtain ⟨h_deg, bound⟩ := hp
  rw [id_eq]
  refine ⟨h_deg, ?_⟩
  by_cases h_p : p = 0; simp only [h_p, coeff_zero, abs_zero, cast_zero]; norm_cast; simp
  intro i
  by_cases h_i : p.natDegree < i; simp only [coeff_eq_zero_of_natDegree_lt h_i, abs_zero,
    cast_zero]; norm_cast; simp
  norm_cast
  have h_norm : |p.coeff i| = (‖p.coeff i‖₊ : ℝ) := by
    simp only [cast_abs, coe_nnnorm]
    rfl
  rw [h_norm]
  have h_deg_eq : (p.map (castRingHom ℂ)).natDegree =  p.natDegree := by
    simp only [natDegree_map_eq_iff, eq_intCast, ne_eq, cast_eq_zero, leadingCoeff_eq_zero]
    exact Decidable.not_or_of_imp (congrArg natDegree)
  have h_nnnorm (j : ℕ) : ‖p.coeff j‖₊ = ‖(p.map (castRingHom ℂ)).coeff j‖₊ := by
    rw [← Complex.nnnorm_intCast]
    congr
    simp
  rw [h_nnnorm]
  have h_split : Splits (RingHom.id ℂ) (p.map (castRingHom ℂ)) :=
    IsAlgClosed.splits (p.map (castRingHom ℂ))
  have h_one_le : 1 ≤ ‖(p.map (castRingHom ℂ)).leadingCoeff‖₊ := by
    rw [leadingCoeff, ← h_nnnorm, h_deg_eq, ← NNReal.natCast_natAbs, ← leadingCoeff]
    norm_cast
    exact Nat.one_le_iff_ne_zero.mpr (natAbs_ne_zero.mpr (leadingCoeff_ne_zero.mpr h_p))
  norm_cast
  refine le_trans (bdd_coeff_of_bdd_roots_and_leading_coeff h_split i) ?_
  rw [mul_comm ‖(p.map (castRingHom ℂ)).leadingCoeff‖₊, mul_assoc]
  have : n - i = 1 + (n - 1 - i) := by omega
  rw [this]
  rw [pow_add, pow_one]
  gcongr
  · rw [h_deg_eq]
    exact Nat.choose_le_choose i <| le_of_lt h_deg
  · exact le_trans (leading_coeff_le_mahler_measure (p.map (castRingHom ℂ))) bound
  · apply le_trans _ bound
    exact le_trans h_one_le (leading_coeff_le_mahler_measure (p.map (castRingHom ℂ)))
  · exact le_trans (roots_le_mahler_measure_of_one_le_leading_coeff h_one_le) bound
  · rw [h_deg_eq]
    omega

theorem inj (n : ℕ) (B : NNReal) : (funct n B).Injective :=
  Subtype.map_injective _ Function.injective_id

theorem Northcott {n : ℕ} (hn : 1 ≤ n) (B : NNReal) :
    Nat.card {p : ℤ[X] // p.natDegree < n ∧ (p.map (castRingHom ℂ)).MahlerMeasure ≤ B} ≤
    ∏ i : Fin n, (2 * Nat.floor (Nat.choose n i * B ^ (n - i)) + 1) := by
  have h1 := card1 hn B
  have h2 : ∏ i : Fin n, (2 * ⌊n.choose i * B ^ (n - i)⌋₊ + 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    omega
  have : Finite {p : ℤ[X] // p.natDegree < n ∧ ∀ i : Fin n, |p.coeff i| ≤
    (n.choose i * B ^ (n - i) : ℝ)} := by
      apply Nat.finite_of_card_ne_zero _
      rw [h1]
      exact h2
  apply le_trans <| Nat.card_le_card_of_injective (funct n B) (inj n B)
  rw [h1]

end Int

end Polynomial
