import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Real.StarOrdered
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Rify
--import Mathlib

open Classical

namespace Polynomial

theorem bdd_coeff_of_bdd_roots_and_lead {K : Type*} [NormedField K] [CharZero K] {p : Polynomial K}
    (hsplit : Splits (RingHom.id K) p) {B : NNReal}
    (h_bdd : (Multiset.map (fun (a : K) ↦ ‖a‖₊) p.roots).sup ≤ B) (n : ℕ) :
    ‖p.coeff n‖₊ ≤ ‖p.leadingCoeff‖₊ * Nat.choose p.natDegree n * B ^ (p.natDegree - n) := by
  by_cases h₀ : p = 0; simp [h₀]
  by_cases h : p.natDegree < n; simp [coeff_eq_zero_of_natDegree_lt h]
  rw [not_lt] at h
  simp only [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (hsplit)) h, Multiset.esymm,
    Finset.sum_multiset_map_count, nsmul_eq_mul, nnnorm_mul, nnnorm_pow, nnnorm_neg, nnnorm_one,
    one_pow, mul_one, mul_assoc ‖p.leadingCoeff‖₊,
    mul_le_mul_left (nnnorm_pos.mpr (leadingCoeff_ne_zero.mpr h₀)), ge_iff_le]
  apply le_trans (norm_sum_le _ _)
  simp_rw [Finset.prod_multiset_count, norm_mul, norm_prod, norm_pow]
  simp only [Multiset.sup_le, Multiset.mem_map, mem_roots', IsRoot.def, forall_exists_index,
    and_imp] at h_bdd
  calc
      ∑ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset,
        ‖((Multiset.count x (Multiset.powersetCard (p.natDegree - n) p.roots)) : K)‖ *
        ∏ x_1 ∈ x.toFinset, ‖x_1‖ ^ Multiset.count x_1 x
    ≤ ∑ x ∈ (Multiset.powersetCard (p.natDegree - n) p.roots).toFinset,
        ‖((Multiset.count x (Multiset.powersetCard (p.natDegree - n) p.roots)) : K)‖ *
        ∏ x_1 ∈ x.toFinset, (B : ℝ) ^ Multiset.count x_1 x := by
          gcongr with x hx z hz
          apply h_bdd ‖z‖₊ z h₀ _ rfl
          simp only [Multiset.mem_toFinset, Multiset.mem_powersetCard] at hx
          have : z ∈ p.roots := Multiset.mem_of_le hx.1 (Multiset.mem_dedup.mp hz)
          rw [mem_roots', IsRoot.def] at this
          exact this.2
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
          · simp [hB, hd]
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
            exact hsplit
section Semiring

variable {R : Type u} [Semiring R]

noncomputable def polConstr (n : ℕ) := fun f : Fin (n + 1) → R => ∑ i in Finset.range (n + 1),
  Polynomial.monomial i (f i)

end Semiring

theorem trivial {B : NNReal} (n : ℕ) : Nat.card {p : Polynomial ℤ // p.natDegree ≤ n ∧
    Finset.univ.sup (fun i : Fin (n + 1) ↦ ‖p.coeff i‖₊) ≤ B} = (2 * (Nat.floor B) + 1) ^ (n + 1) := by
  simp only [Finset.sup_le_iff, Finset.mem_univ, forall_const, Set.coe_setOf]
  let Bp := fun i : Fin (n + 1) ↦ (Nat.floor B : ℤ)
  let Bm := fun i : Fin (n + 1) ↦ - (Nat.floor B : ℤ)
  let Box := Finset.Icc Bm Bp
  let BoxPoly := {p : Polynomial ℤ // p.natDegree ≤ n ∧ ∀ i : Fin (n + 1), ‖p.coeff ↑i‖₊ ≤ B}
  have hf (p : BoxPoly) : (fun i : Fin (n + 1) ↦ p.val.coeff i) ∈ Box := by
    simp only [Finset.mem_Icc, Box, Bm, Bp]
    refine ⟨Pi.le_def.mpr ?_, Pi.le_def.mpr ?_⟩
    any_goals intro i
    any_goals have hcoef := p.property.2 i
    any_goals rw [← Int.abs_le_floor_nnreal_iff] at hcoef
    exact neg_le_of_abs_le hcoef
    exact le_of_max_le_left hcoef
  let f : BoxPoly → Box := fun p => ⟨fun i ↦ p.val.coeff i, hf p⟩
  have hfBij : f.Bijective := by
    refine (Function.bijective_iff_existsUnique f).mpr ?_
    simp only [Subtype.forall]
    intro v hv
    let p : BoxPoly := by
      refine ⟨polConstr n v, ?_, ?_⟩
      · simp only [polConstr]
        apply Polynomial.natDegree_sum_le_of_forall_le
        intro i hi
        simp only [Finset.mem_range] at hi
        rw [Polynomial.natDegree_monomial i (v i)]
        split
        next h => simp_all only [zero_le]
        next h => exact Nat.le_of_lt_succ hi
      . intro i
        simp only [polConstr]
        simp only [finset_sum_coeff,  Polynomial.coeff_monomial]
        simp only [Finset.sum_ite_eq', Finset.mem_range, Fin.is_lt, ↓reduceIte,
          Fin.cast_val_eq_self]
        simp only [Finset.mem_Icc, Box, Bm, Bp] at hv
        obtain ⟨left, right⟩ := hv
        rw [← Int.abs_le_floor_nnreal_iff]
        specialize left i
        specialize right i
        simp_all only
        rw [@abs_le]
        exact And.symm ⟨right, left⟩
    use p
    simp only
    constructor
    · ext i
      simp only [f, Subtype.coe_mk, polConstr, finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, Fin.is_lt, ↓reduceIte,
          Fin.cast_val_eq_self]
    · intro q hq
      apply Subtype.eq
      rw [← Polynomial.coeff_inj]
      ext i
      simp only [f, Subtype.coe_mk, polConstr, finset_sum_coeff, Polynomial.coeff_monomial, Finset.sum_ite_eq', Finset.mem_range, Fin.is_lt, ↓reduceIte,
          Fin.cast_val_eq_self] at hq
      simp only [Subtype.mk.injEq] at hq
      subst hq
      simp_all only
      obtain ⟨q, propertyq⟩ := q
      obtain ⟨degq, boxq⟩ := propertyq
      obtain ⟨p1, propertyp⟩ := p
      obtain ⟨degp, boxp⟩ := propertyp
      simp only [polConstr, Fin.val_natCast, finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq',
        Finset.mem_range]
      by_cases h : i < n + 1
      · simp_all only [Finset.mem_Icc, ↓reduceIte, Box, Bm, Bp]
        congr
        exact Eq.symm (Nat.mod_eq_of_lt h)
      · split
        next h_1 => exact False.elim (h h_1)
        next h_1 =>
          simp_all only [not_lt]
          apply coeff_eq_zero_of_natDegree_lt
          omega
  rw [Nat.card_eq_of_bijective f hfBij]
  simp only [Box]
  convert_to (Finset.Icc Bm Bp).card = (2 * (Nat.floor B) + 1) ^ (n + 1)
  · exact Nat.card_eq_finsetCard (Finset.Icc Bm Bp)
  simp_rw [Pi.card_Icc, Int.card_Icc, Bp, Bm]
  simp only [sub_neg_eq_add, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zero_le, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, pow_left_inj₀]
  zify
  rw [Int.toNat_eq_max, add_comm, ← add_assoc]
  have : ↑⌊B⌋₊ + ↑⌊B⌋₊ = 2 * (⌊B⌋₊ : ℤ) := by ring
  simp_rw [this]
  exact rfl

--#min_imports

/-
#find_home! bdd_coeff_of_bdd_roots_and_lead
says
[Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order,
Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog,
Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart] -/

end Polynomial
