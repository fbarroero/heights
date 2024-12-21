import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Vieta
--import Mathlib

open Classical

namespace Polynomial

theorem bdd_coeff_of_bdd_roots_and_lead {K : Type*} [NormedField K]
    [IsAlgClosed K] [CharZero K] {p : Polynomial K} {B : NNReal}
    (h_bdd : (Multiset.map (fun (a : K) ↦ ‖a‖₊) p.roots).sup ≤ B) (n : ℕ) :
    ‖p.coeff n‖₊ ≤ ‖p.leadingCoeff‖₊ * Nat.choose p.natDegree n * B ^ (p.natDegree - n) := by
  by_cases h₀ : p = 0; simp [h₀]
  by_cases h : p.natDegree < n; simp [coeff_eq_zero_of_natDegree_lt h]
  rw [not_lt] at h
  simp only [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgClosed.splits_codomain p))
    h, Multiset.esymm, Finset.sum_multiset_map_count, nsmul_eq_mul, nnnorm_mul, nnnorm_pow,
    nnnorm_neg, nnnorm_one, one_pow, mul_one, mul_assoc ‖p.leadingCoeff‖₊,
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
            exact IsAlgClosed.splits p

theorem Northcott {B : NNReal} : {p : Polynomial ℤ |
    Finset.univ.sup (fun n : Fin p.natDegree ↦ ‖p.coeff n‖₊) ≤ B}.Finite := by

  sorry

--#min_imports

/-
#find_home! bdd_coeff_of_bdd_roots_and_lead
says
[Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order,
Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog,
Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart] -/

end Polynomial
