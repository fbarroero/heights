import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.ComputeDegree
import Mathlib

namespace Polynomial

noncomputable def MahlerMeasure (p : Polynomial ℂ) := ‖leadingCoeff p‖₊ *
    (Multiset.map (fun (a : ℂ) ↦ max 1 ‖a‖₊) p.roots).prod

--instance : FunLike (FinitePlace K) K ℝ where

@[simp]
theorem MM_zero : MahlerMeasure 0 = 0 := by
  simp only [MahlerMeasure, leadingCoeff_zero, nnnorm_zero, roots_zero, Multiset.map_zero,
    Multiset.prod_zero, mul_one]

@[simp]
theorem MM_const (z : ℂ) : MahlerMeasure (C z) = ‖z‖₊ := by
  simp only [MahlerMeasure, leadingCoeff_C, roots_C, Multiset.map_zero, Multiset.prod_zero, mul_one]

@[simp]
theorem MM_X : MahlerMeasure X = 1 := by
  simp only [MahlerMeasure, monic_X, Monic.leadingCoeff, nnnorm_one, roots_X,
    Multiset.map_singleton, nnnorm_zero, zero_le, sup_of_le_left, Multiset.prod_singleton, mul_one]

@[simp]
theorem MM_linear (z₁ z₀ : ℂ) (h1 : z₁ ≠ 0) : MahlerMeasure (C z₁ * X - C z₀) = ‖z₁‖₊ * max 1 ‖z₀ / z₁‖₊ := by
  simp only [MahlerMeasure, Complex.norm_eq_abs, norm_div]
  have : (C z₁ * X - C z₀).leadingCoeff = z₁ := by
    rw [leadingCoeff]
    simp_all only [ne_eq, natDegree_sub_C, _root_.map_eq_zero, not_false_eq_true, natDegree_mul_X, natDegree_C,
      zero_add, coeff_sub, coeff_mul_X, coeff_C_zero, coeff_C_succ, sub_zero]
  rw [this]
  simp only [mul_eq_mul_left_iff, _root_.map_eq_zero]
  left
  have : C z₁ * X - C z₀ = C z₁ * (X - C (z₀ / z₁)) := by
    rw [mul_sub, ← C_mul, mul_div_cancel₀ z₀ h1]
  have : (C z₁ * X - C z₀).roots = (X - C (z₀ / z₁)).roots := by
    rw [this]
    exact roots_C_mul (X - C (z₀ / z₁)) h1
  simp_all only [ne_eq, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X_sub_C, mul_one,
    not_false_eq_true, roots_C_mul, roots_X_sub_C, Multiset.map_singleton, nnnorm_div,
    Multiset.prod_singleton, NNReal.coe_max, NNReal.coe_one, NNReal.coe_div, coe_nnnorm,
    Complex.norm_eq_abs]

theorem MM_2 : MahlerMeasure (X - C 2) = 2 := by
  simp only [MahlerMeasure, leadingCoeff_X_sub_C, nnnorm_one, roots_X_sub_C, Multiset.map_singleton,
    Complex.nnnorm_ofNat, Nat.one_le_ofNat, sup_of_le_right, Multiset.prod_singleton, one_mul]

@[simp]
theorem MM_mul (p q : Polynomial ℂ) : MahlerMeasure (p * q) = MahlerMeasure p * MahlerMeasure q := by
  simp only [MahlerMeasure, leadingCoeff_mul, nnnorm_mul]
  rw [mul_assoc, mul_assoc, mul_eq_mul_left_iff]
  norm_cast
  rw[mul_left_comm (Multiset.map (fun x ↦ 1 ⊔ ‖x‖₊) p.roots).prod
    _ _]
  simp only [mul_eq_mul_left_iff, map_eq_zero, leadingCoeff_eq_zero]
  by_cases hp : p = 0
  · simp only [hp, zero_mul, roots_zero, Multiset.map_zero, Multiset.prod_zero, one_mul,
    nnnorm_eq_zero, leadingCoeff_eq_zero, leadingCoeff_zero, nnnorm_zero, or_true]
  · left
    by_cases hq : q = 0
    · simp only [hq, mul_zero, roots_zero, Multiset.map_zero, Multiset.prod_zero, mul_one,
      leadingCoeff_zero, nnnorm_zero, or_true]
    · left
      rw [roots_mul (mul_ne_zero hp hq)]
      simp only [Multiset.map_add, Multiset.prod_add]

open Classical

theorem bdd_coeff_of_bdd_roots_and_lead {K : Type*} [NormedField K]
    [IsAlgClosed K] [CharZero K] {p : Polynomial K} (h₀ : p ≠ 0) {B : NNReal}
    (h_bdd : (Multiset.map (fun (a : K) ↦ ‖a‖₊) p.roots).sup ≤ B) :
    ∀ n, ‖p.coeff n‖₊ ≤ Nat.choose p.natDegree n * B ^ (p.natDegree - n) * ‖p.leadingCoeff‖₊ := by
  intro n
  have h_lcoeff : p.leadingCoeff ≠ 0  := leadingCoeff_ne_zero.mpr h₀
  by_cases h : p.natDegree < n; simp only [coeff_eq_zero_of_natDegree_lt h, nnnorm_zero, zero_le]
  rw [not_lt] at h
  simp only [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgClosed.splits_codomain p))
    h, Multiset.esymm, Finset.sum_multiset_map_count, nnnorm_mul, nnnorm_pow, nnnorm_neg,
    nnnorm_one, one_pow, mul_one, mul_comm _ ‖p.leadingCoeff‖₊, mul_le_mul_left
    (nnnorm_pos.mpr h_lcoeff), nsmul_eq_mul]
  apply le_trans (norm_sum_le _ _)
  simp_rw [Finset.prod_multiset_count, norm_mul, norm_prod, norm_pow]
  simp only [Multiset.sup_le, Multiset.mem_map, mem_roots', IsRoot.def, forall_exists_index,
    and_imp] at h_bdd
  have h1 : ∀ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset, ∀ z ∈ x.toFinset, ‖z‖₊ ≤ B := by
    intro x hx z hz
    apply h_bdd ‖z‖₊ z h₀ _ rfl
    simp only [Multiset.mem_toFinset, Multiset.mem_powersetCard] at hx
    obtain ⟨h_root, _⟩ := hx
    have : z ∈ p.roots := Multiset.mem_of_le h_root (Multiset.mem_dedup.mp hz)
    rw [mem_roots', IsRoot.def] at this
    exact this.2
  calc
      ∑ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset,
        ‖((Multiset.count x (Multiset.powersetCard (p.natDegree - n) p.roots)) : K)‖ *
        ∏ x_1 ∈ x.toFinset, ‖x_1‖ ^ Multiset.count x_1 x
    ≤ ∑ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset,
        ‖((Multiset.count x (Multiset.powersetCard (p.natDegree - n) p.roots)) : K)‖ *
        ∏ x_1 ∈ x.toFinset, (B : ℝ) ^ Multiset.count x_1 x := by
          gcongr with x hx z hz
          exact h1 x hx z hz
  _ = ∑ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset,
        ‖((Multiset.count x (Multiset.powersetCard (p.natDegree - n) p.roots)) : K)‖ *
        (B : ℝ) ^ (p.natDegree - n) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [mul_eq_mul_left_iff, nnnorm_eq_zero, Nat.cast_eq_zero,
            Multiset.count_eq_zero, Multiset.mem_powersetCard, not_and, Finset.prod_pow_eq_pow_sum]
          left
          congr
          simp_all only [Multiset.mem_toFinset, Multiset.mem_powersetCard, implies_true,
              Multiset.sum_count_eq_card]
  _ ≤ ↑(p.natDegree.choose n) * (B : ℝ) ^ (p.natDegree - n) := by
          by_cases hB : B = 0
          by_cases hd : p.natDegree - n = 0
          · simp only [hd, Multiset.powersetCard_zero_left, Multiset.toFinset_singleton,
              Multiset.nodup_singleton, hB, pow_zero, mul_one, Finset.sum_singleton,
              Multiset.mem_singleton, Multiset.count_eq_one_of_mem, Nat.cast_one, norm_one]
            rw [Nat.le_antisymm h <| Nat.le_of_sub_eq_zero hd, Nat.choose_self, Nat.cast_one]
          · simp only [hB, NNReal.coe_zero, ne_eq, hd, not_false_eq_true, zero_pow, mul_zero,
            Finset.sum_const_zero, le_refl]
          · rw [← Finset.sum_mul, mul_le_mul_right (mod_cast pow_pos (pos_iff_ne_zero.mpr hB) _)]
            apply le_trans (Finset.sum_le_sum (fun _ _ ↦ Nat.norm_cast_le _))
            simp only [norm_one, mul_one]
            norm_cast
            simp only [Multiset.mem_powersetCard, Multiset.mem_toFinset, imp_self, implies_true,
              Multiset.sum_count_eq_card, Multiset.card_powersetCard]
            rw [← Nat.choose_symm h]
            apply le_of_eq
            congr
            rw [← splits_iff_card_roots]
            exact IsAlgClosed.splits p


theorem Complex.bdd_coeff_of_bdd_roots_and_lead {p : Polynomial ℂ} (h₀ : p ≠ 0) {B : NNReal}
    (h_bdd : (Multiset.map (fun (a : ℂ) ↦ ‖a‖₊) p.roots).sup ≤ B) :
    ∀ n, ‖p.coeff n‖₊ ≤ Nat.choose p.natDegree n * B ^ (p.natDegree - n) * ‖p.leadingCoeff‖₊ :=
  fun _ ↦ Polynomial.bdd_coeff_of_bdd_roots_and_lead h₀ h_bdd _

theorem Kronecker {p : Polynomial ℤ} (h_monic : Monic p) (h_irr : Irreducible p)
    (h_MM : MahlerMeasure (map coe p) = 1) : p = X ∨ ∃ n : ℕ, p = cyclotomic n ℤ := by
  rw [or_iff_not_imp_left]
  intro hp_ne_X
  by_cases h_deg_p : p.natDegree = 0; use 0; simp_all only [Monic.natDegree_eq_zero_iff_eq_one, cyclotomic_zero]
  use natDegree p
  convert_to map coe p = map coe (cyclotomic p.natDegree ℤ)
  refine ⟨fun a ↦ congrArg (map coe) a, fun a ↦ map_injective coe (RingHom.injective_int coe) a⟩
  simp only [map_cyclotomic]
  have : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I * (1 / p.natDegree))) p.natDegree := by
    rw [Complex.isPrimitiveRoot_iff _ _ h_deg_p]

    sorry




  rw [cyclotomic_eq_prod_X_sub_primitiveRoots]

  sorry

  sorry
  sorry
-- https://mathoverflow.net/questions/10911/english-reference-for-a-result-of-kronecker


end Polynomial
