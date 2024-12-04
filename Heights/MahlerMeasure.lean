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

example {ι : Type u_1}  {M : Type u_4}  [OrderedCancelAddCommMonoid M]  {s : Finset ι}  {f g : ι → M} (h : ∀ i ∈ s, f i = g i) :
∑ i ∈ s, f i = ∑ i ∈ s, g i := by
  exact Finset.sum_congr rfl h

theorem bdd_coeff_of_bdd_roots_and_lead {p : Polynomial ℂ} (h₀ : p ≠ 0) {B : NNReal}
    (h_bdd : (Multiset.map (fun (a : ℂ) ↦ ‖a‖₊) p.roots).sup ≤ B) :
    ∀ n, ‖p.coeff n‖₊ ≤ Nat.choose p.natDegree n * B ^ (p.natDegree - n) * ‖p.leadingCoeff‖₊ := by
  intro n
  simp_all only [Multiset.sup_le, Multiset.mem_map, mem_roots', not_false_eq_true, IsRoot.def, true_and,
    forall_exists_index]
  have : p.leadingCoeff ≠ 0  := leadingCoeff_ne_zero.mpr h₀
  by_cases h : p.natDegree < n; simp only [coeff_eq_zero_of_natDegree_lt h, nnnorm_zero, zero_le]
  rw [not_lt] at h
  simp only [coeff_eq_esymm_roots_of_card
    (splits_iff_card_roots.mp (IsAlgClosed.splits_codomain  p)) h, mul_comm _ ‖p.leadingCoeff‖₊,
    nnnorm_mul, nnnorm_pow, nnnorm_neg, nnnorm_one, one_pow, mul_one, ge_iff_le, mul_le_mul_left,
    nnnorm_pos.mpr this, Multiset.esymm, Finset.sum_multiset_map_count, nsmul_eq_mul]
  apply le_trans (norm_sum_le _ _)
  simp only [norm_mul, Complex.norm_natCast, Complex.norm_eq_abs, NNReal.val_eq_coe, NNReal.coe_mul,
    NNReal.coe_natCast, Finset.prod_multiset_count, Complex.abs_natCast, map_prod,
    AbsoluteValue.map_pow, NNReal.coe_pow]
  have h1 : ∀ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset, ∀ z ∈ x.toFinset, ‖z‖₊ ≤ B := by
    intro x hx z hz
    apply h_bdd ‖z‖₊ z
    simp_all only [ne_eq, not_false_eq_true, true_and, and_imp, forall_apply_eq_imp_iff₂,
      leadingCoeff_eq_zero, Multiset.mem_toFinset, Multiset.mem_powersetCard, and_true]
    obtain ⟨left, right⟩ := hx
    have : z ∈ p.roots := Multiset.mem_of_le left hz
    simp only [mem_roots', ne_eq, IsRoot.def] at this
    exact this.2
  have h2 : ∀ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset, ∀ z ∈ x.toFinset, Multiset.count z x ≤ p.natDegree - n := by
    intro x hx z hz
    simp_all only [ne_eq, not_false_eq_true, true_and, and_imp, forall_apply_eq_imp_iff₂, leadingCoeff_eq_zero,
      Multiset.mem_toFinset, Multiset.mem_powersetCard]
    obtain ⟨left, right⟩ := hx
    rw [← right]
    exact Multiset.count_le_card z x
  calc
  ∑ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset,
    ↑(Multiset.count x (Multiset.powersetCard (p.natDegree - n) p.roots)) *
      ∏ x_1 ∈ x.toFinset, Complex.abs x_1 ^ Multiset.count x_1 x ≤
  ∑ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset,
    ↑(Multiset.count x (Multiset.powersetCard (p.natDegree - n) p.roots)) *
      ∏ x_1 ∈ x.toFinset, (B : ℝ) ^ Multiset.count x_1 x := by
      gcongr with x hx z hz
      exact h1 x hx z hz
  _ = ∑ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset,
    ↑(Multiset.count x (Multiset.powersetCard (p.natDegree - n) p.roots)) *
    (B : ℝ) ^ (p.natDegree - n) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp_all only [ne_eq, not_false_eq_true, true_and, and_imp, forall_apply_eq_imp_iff₂, leadingCoeff_eq_zero,
        Multiset.mem_toFinset, Multiset.mem_powersetCard, mul_eq_mul_left_iff, Nat.cast_eq_zero,
        Multiset.count_eq_zero, and_self, not_true_eq_false, or_false]
      obtain ⟨left, right⟩ := hx
      rw [Finset.prod_pow_eq_pow_sum]
      congr
      simp_all only [Multiset.mem_toFinset, implies_true, Multiset.sum_count_eq_card]
  _ ≤ ↑(p.natDegree.choose n) * ↑B ^ (p.natDegree - n) := by
    by_cases hB : B = 0
    by_cases hd : p.natDegree - n = 0
    · simp only [hd, Multiset.powersetCard_zero_left, Multiset.toFinset_singleton,
      Multiset.nodup_singleton, hB, NNReal.coe_zero, pow_zero, mul_one, Finset.sum_singleton,
      Multiset.mem_singleton, Multiset.count_eq_one_of_mem, Nat.cast_one, Nat.one_le_cast]
      rw [Nat.le_antisymm h <| Nat.le_of_sub_eq_zero hd, Nat.choose_self]
    · simp only [hB, NNReal.coe_zero, ne_eq, hd, not_false_eq_true, zero_pow, mul_zero,
      Finset.sum_const_zero, le_refl]
    rw [← Finset.sum_mul, mul_le_mul_right (mod_cast pow_pos (pos_iff_ne_zero.mpr hB) _)]
    norm_cast
    simp only [Multiset.mem_powersetCard, Multiset.mem_toFinset, imp_self, implies_true,
      Multiset.sum_count_eq_card, Multiset.card_powersetCard]
    let i : ℂ →+* ℂ := {
      toFun := id
      map_one' := rfl
      map_mul' _ _ := rfl
      map_zero' := rfl
      map_add' _ _:= rfl
    }
    have h3: Multiset.card p.roots = p.natDegree := by
      rw [natDegree_eq_card_roots (i:=i) (IsAlgClosed.splits_domain p)]
      simp only [i]
      congr
      ext n
      simp only [coeff_map, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, id_eq]
    rw [h3]
    apply le_of_eq
    simp only [h, Nat.choose_symm]



/-

--change to complex poly
theorem bdd_coeff_of_bdd_roots_and_lead' {p : Polynomial ℤ} (h₀ : p ≠ 0) {B : NNReal}
    (h_bdd : (Multiset.map (fun (a : ℂ) ↦ ‖a‖₊) (map coe p).roots).sup ≤ B) :
    ∀ n, ‖(map coe p).coeff n‖₊ ≤ Nat.choose p.natDegree n * B * ‖p.leadingCoeff‖₊ := by --change const on the right accordingly?
  simp_all only [Multiset.sup_le, Multiset.mem_map, mem_roots', IsRoot.def,
    forall_exists_index, and_imp, eq_intCast, Complex.nnnorm_intCast]
  have h_deg_eq : (map coe p).natDegree = p.natDegree := by
    rw [natDegree_map_eq_iff]
    left
    simp_all only [ne_eq, eq_intCast, Int.cast_eq_zero, leadingCoeff_eq_zero, not_false_eq_true]
  have h_lead_eq : (map coe p).leadingCoeff = p.leadingCoeff := by
    simp only [leadingCoeff, coeff_map, eq_intCast, ← h_deg_eq]
  have : p.leadingCoeff ≠ 0  := by exact leadingCoeff_ne_zero.mpr h₀
  intro n
  by_cases h : p.natDegree < n; simp_all only [← h_deg_eq, coeff_map,
    coeff_eq_zero_of_natDegree_lt h, eq_intCast, Int.cast_zero, nnnorm_zero, zero_le]
  simp only [not_lt, ← h_deg_eq] at h
  rw [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgClosed.splits_codomain (map coe p))) h]
  simp only [h_lead_eq, nnnorm_mul, Complex.nnnorm_intCast, nnnorm_pow, nnnorm_neg, nnnorm_one,
    one_pow, mul_one]
  rw [mul_comm]
  simp_all only [ne_eq, eq_intCast, Int.cast_eq_zero, not_false_eq_true, true_or,
    leadingCoeff_eq_zero, nnnorm_pos, mul_le_mul_right]
  simp only [Multiset.esymm]
  rw [Finset.sum_multiset_map_count]
  simp only [nsmul_eq_mul]


  have := (norm_sum_le (E:=ℂ) ((Multiset.powersetCard (p.natDegree - n) (map coe p).roots).toFinset)) (fun x ↦ ↑(Multiset.count x (Multiset.powersetCard (p.natDegree - n) (map coe p).roots)) * x.prod)
  apply le_trans this
  simp only [norm_mul, Complex.norm_natCast, NNReal.val_eq_coe, NNReal.coe_mul,
    NNReal.coe_natCast]

  have : ∀ x ∈ (Multiset.powersetCard (p.natDegree - n) (map coe p).roots).toFinset, Multiset.count x (Multiset.powersetCard (p.natDegree - n) (map coe p).roots) = Nat.choose p.natDegree n := by
    intro x a
    simp_all only [eq_intCast, ne_eq, Int.cast_eq_zero, leadingCoeff_eq_zero,
      not_false_eq_true, true_or, Complex.norm_eq_abs, norm_mul, RCLike.norm_natCast,
      Multiset.mem_toFinset, Multiset.mem_powersetCard]
    obtain ⟨left, right⟩ := a
    simp_all only [natDegree_map_eq_iff, eq_intCast, ne_eq, Int.cast_eq_zero, leadingCoeff_eq_zero, not_false_eq_true,
      true_or]
    rw [Multiset.count_eq_card.mpr]

    sorry
    intro y hy
    sorry
  sorry -/


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
