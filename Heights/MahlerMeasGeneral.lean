import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.ComputeDegree
import Heights.poly_norm

namespace Polynomial

section Definition_and_API

variable {K : Type*} [NormedField K]

noncomputable def MahlerMeasure (p : K[X]) := ‖leadingCoeff p‖₊ *
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
  have h1 : p.coeff 1 ≠ 0 := coeff_ne_zero_of_eq_degree h
  simp [mahler_measure_C_mul_X_add_C h1]

@[simp]
theorem mahler_measure_mul (p q : K[X]) : (p * q).MahlerMeasure = p.MahlerMeasure * q.MahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  simp [MahlerMeasure, mul_assoc, mul_left_comm (Multiset.map (fun x ↦ 1 ⊔ ‖x‖₊) p.roots).prod _ _,
    roots_mul (mul_ne_zero hp hq)]

end Definition_and_API

section Int

open Int
--inutile?
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
    exact mul_le_mul_right' h_lead (B ^ n)

def funct (n : ℕ) (B : NNReal) :
    {p : ℤ[X] // p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).MahlerMeasure ≤ B} →
    {p : ℤ[X] // p.natDegree ≤ n ∧ ∀ i, ‖(p.map (castRingHom ℂ)).coeff i‖₊ ≤ ‖p.leadingCoeff‖₊ * Nat.choose p.natDegree i * B ^ (p.natDegree - i)} := by
  intro a
  obtain ⟨p, prop⟩ := a
  obtain ⟨h_deg, bound⟩ := prop
  refine ⟨p, h_deg, ?_⟩
  intro i
  have h_deg_eq : (map (castRingHom ℂ) p).natDegree =  p.natDegree := by
    simp only [natDegree_map_eq_iff, eq_intCast, ne_eq, cast_eq_zero, leadingCoeff_eq_zero]
    exact Decidable.not_or_of_imp (congrArg natDegree)
  have h_nnnorm_lc : ‖(map (castRingHom ℂ) p).leadingCoeff‖₊ = ‖p.leadingCoeff‖₊ := by
    rw [← Complex.nnnorm_intCast]
    congr
    rw [leadingCoeff, leadingCoeff]
    simp [h_deg_eq]
  rw [← h_nnnorm_lc, ← h_deg_eq]
  refine bdd_coeff_of_bdd_roots_and_lead (IsAlgClosed.splits (p.map (castRingHom ℂ))) ?_ i

  sorry

theorem inj (n : ℕ) (B : NNReal) : (funct n B).Injective := by sorry

theorem Northcott (n : ℕ) (B : NNReal) :
    Nat.card {p : ℤ[X] // p.natDegree ≤ n ∧ (p.map (castRingHom ℂ)).MahlerMeasure ≤ B} ≤
    (2 * Nat.floor B + 1) ^ (n + 1) := by

  sorry


end Int

end Polynomial

--#min_imports
