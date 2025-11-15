--to Mathlib.NumberTheory.MahlerMeasure.lean

/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Heights.IntegralMahlerMeasure
namespace Polynomial

section Int

open Int

open Finset in
theorem card_eq_of_natDegree_le_of_coeff_le {n : ℕ} (hn : 1 ≤ n) {B₁ B₂ : Fin n → ℝ}
    (h_B : ∀ i, ⌈B₁ i⌉ ≤ ⌊B₂ i⌋) :
    Nat.card {p : ℤ[X] | p.natDegree < n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i} =
    ∏ i : Fin n, (⌊B₂ i⌋ - ⌈B₁ i⌉ + 1)  := by
  let Bp := fun i ↦ ⌊B₂ i⌋
  let Bm := fun i ↦ ⌈B₁ i⌉
  let Box := Icc Bm Bp
  let BoxPoly := {p : ℤ[X] | p.natDegree < n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i}
  let f : BoxPoly → Box := fun p => ⟨toFn n p , by
    simp only [mem_Icc, Box, Bm, Bp]
    refine ⟨fun i ↦ ceil_le.mpr (p.property.2 i).1, fun i ↦ le_floor.mpr (p.property.2 i).2⟩⟩
  let g : Box → BoxPoly := fun p => ⟨ofFn n p, by
    refine ⟨ofFn_natDegree_lt hn p.val, ?_⟩
    intro i
    obtain ⟨_, prop⟩ := p
    simp only [mem_Icc, Box] at prop
    simp only [Fin.is_lt, ofFn_coeff_eq_val_of_lt, Fin.eta]
    refine ⟨ceil_le.mp (prop.1 i), le_floor.mp (prop.2 i)⟩⟩
  have hfBij : f.Bijective := by
    refine Function.bijective_iff_has_inverse.mpr ⟨g, ?_, ?_⟩
    · intro p
      simp [f, g, ofFn_comp_toFn_eq_id_of_natDegree_lt (p.property.1)]
    · intro ⟨_, _⟩
      ext i
      simp_all [toFn, f, g]
  rw [Nat.card_eq_of_bijective f hfBij]
  simp only [Box, Nat.card_eq_finsetCard (Icc Bm Bp), Pi.card_Icc,
    card_Icc, Bp, Bm, prod_const, card_univ, Fintype.card_fin, sub_neg_eq_add]
  push_cast
  congr
  ext i
  specialize h_B i
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
    Nat.card {p : ℤ[X] | p.natDegree < n ∧ ∀ i : Fin n, |p.coeff i| ≤ (n.choose i * B : ℝ)} =
    ∏ i : Fin n, (2 * ⌊n.choose i * B⌋₊ + 1) := by
  let B₁ := fun i : Fin n ↦ - (n.choose i * B  : ℝ)
  let B₂ := fun i : Fin n ↦ (n.choose i * B : ℝ)
  have h_B (i : Fin n) : ⌈B₁ i⌉ ≤ ⌊B₂ i⌋ := by
    simp only [ceil_neg, neg_le_self_iff, le_floor, cast_zero, B₁, B₂]
    exact_mod_cast zero_le (↑(n.choose ↑i) * B)
  zify
  have (i : Fin n) : (⌊(n.choose i) * B ⌋₊ : ℤ) = ⌊(n.choose i) * (B : ℝ)⌋ := by
    apply natCast_floor_eq_floor
    have (i : Fin n) : 0 ≤ (n.choose i) * B := by positivity
    exact this i
  conv => enter [2,2]; ext i; enter [1]; rw [this, two_mul, ← sub_neg_eq_add, ← ceil_neg]
  simp [← card_eq_of_natDegree_le_of_coeff_le hn h_B, B₁, B₂, abs_le]

open Int in
def funct (n : ℕ) (B : NNReal) :
    {p : ℤ[X] | p.natDegree < n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} →
    {p : ℤ[X] | p.natDegree < n ∧ ∀ i : Fin n, |p.coeff i| ≤ (n.choose i * B : ℝ)} := by
  apply Subtype.map id
  intro p hp
  obtain ⟨h_deg, _⟩ := hp
  rw [id_eq]
  refine ⟨h_deg, ?_⟩
  have h_deg_eq : (p.map (castRingHom ℂ)).natDegree =  p.natDegree := by
    simp only [natDegree_map_eq_iff, eq_intCast, ne_eq, cast_eq_zero, leadingCoeff_eq_zero]
    exact Decidable.not_or_of_imp (congrArg natDegree)
  intro i
  by_cases h_i : p.natDegree < i
  · simp only [coeff_eq_zero_of_natDegree_lt h_i, abs_zero, cast_zero]
    norm_cast
    exact zero_le (↑(n.choose ↑i) * B)
  · rw [not_lt] at h_i
    have h_norm : |p.coeff i| = (‖(p.map (castRingHom ℂ)).coeff i‖₊ : ℝ) := by
      simp_all only [cast_abs, coeff_map, eq_intCast, Complex.nnnorm_intCast, coe_nnnorm]
      rfl
    rw [h_norm]
    apply le_trans (norm_coeff_le_binom_mahlerMeasure i (map (castRingHom ℂ) p))
    gcongr
    · exact mahlerMeasure_nonneg (map (castRingHom ℂ) p)
    · rw [h_deg_eq]
      simp only [h_i, Nat.choose_symm]
      apply Nat.choose_le_choose i <| le_of_lt h_deg

theorem Northcott {n : ℕ} (hn : 1 ≤ n) (B : NNReal) :
    Nat.card {p : ℤ[X] | p.natDegree < n ∧ (p.map (castRingHom ℂ)).mahlerMeasure ≤ B} ≤
    ∏ i : Fin n, (2 * Nat.floor (Nat.choose n i * B) + 1) := by
  have h1 := card1 hn B
  have h2 : ∏ i : Fin n, (2 * ⌊n.choose i * B⌋₊ + 1) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    omega
  have : Finite {p : ℤ[X] | p.natDegree < n ∧ ∀ i : Fin n, |p.coeff i| ≤
    (n.choose i * B : ℝ)} := by
      apply Nat.finite_of_card_ne_zero _
      rw [h1]
      exact h2
  apply le_trans <| Nat.card_le_card_of_injective (funct n B) (Subtype.map_injective _ Function.injective_id)
  rw [h1]

end Int

end Polynomial
