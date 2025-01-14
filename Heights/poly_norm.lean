import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Pi.Interval
import Mathlib.Data.Real.StarOrdered
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Polynomial.Vieta
import Mathlib.Tactic.Rify
import Heights.Fin1
--import Mathlib

open Classical

namespace Polynomial

open Multiset in
theorem bdd_coeff_of_bdd_roots_and_lead {K : Type*} [NormedField K] [CharZero K] {p : K[X]}
    (hsplit : Splits (RingHom.id K) p) {B : NNReal}
    (h_bdd : ((p.roots).map (fun a ↦ ‖a‖₊)).sup ≤ B) (n : ℕ) :
    ‖p.coeff n‖₊ ≤ ‖p.leadingCoeff‖₊ * Nat.choose p.natDegree n * B ^ (p.natDegree - n) := by
  by_cases h₀ : p = 0; simp [h₀]
  by_cases h : p.natDegree < n; simp [coeff_eq_zero_of_natDegree_lt h]
  rw [not_lt] at h
  simp only [coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (hsplit)) h, esymm,
    Finset.sum_multiset_map_count, nsmul_eq_mul, nnnorm_mul, nnnorm_pow, nnnorm_neg, nnnorm_one,
    one_pow, mul_one, mul_assoc ‖p.leadingCoeff‖₊,
    mul_le_mul_left (nnnorm_pos.mpr (leadingCoeff_ne_zero.mpr h₀))]
  apply le_trans <| norm_sum_le _ _
  simp_rw [Finset.prod_multiset_count, norm_mul, norm_prod, norm_pow]
  simp only [Multiset.sup_le, mem_map, forall_exists_index, and_imp] at h_bdd
  let S := (p.roots).powersetCard (p.natDegree - n)
  calc
      ∑ P ∈ S.toFinset, ‖(S.count P : K)‖ * ∏ x ∈ P.toFinset, ‖x‖ ^ P.count x
    ≤ ∑ P ∈ S.toFinset, ‖(S.count P : K)‖ * ∏ x ∈ P.toFinset, (B : ℝ) ^ P.count x := by
          gcongr with P hP z hz
          simp only [mem_toFinset, mem_powersetCard, S] at hP
          exact h_bdd ‖z‖₊ z (mem_of_le hP.1 (mem_dedup.mp hz)) rfl
  _ = ∑ P ∈ S.toFinset, ‖(S.count P : K)‖ * (B : ℝ) ^ (p.natDegree - n) := by
          apply Finset.sum_congr rfl
          intro x hx
          simp only [mem_toFinset, mem_powersetCard, S] at hx
          simp [S, hx, Finset.prod_pow_eq_pow_sum]
  _ ≤ ∑ P ∈ S.toFinset, (S.count P) * (B : ℝ) ^ (p.natDegree - n) := by
          gcongr with P hP
          apply le_trans <| Nat.norm_cast_le _
          simp
  _ = ↑(p.natDegree.choose n) * (B : ℝ) ^ (p.natDegree - n) := by
          by_cases hB : B = 0
          by_cases hd : p.natDegree - n = 0
          · simp [S, hd, hB, Nat.le_antisymm h <| Nat.le_of_sub_eq_zero hd]
          · simp [hB, hd]
          · rw [← Finset.sum_mul]
            simp only [mul_eq_mul_right_iff, pow_eq_zero_iff', NNReal.coe_eq_zero, hB, ne_eq,
              false_and, or_false]
            norm_cast
            simp only [← Nat.choose_symm h, S, mem_powersetCard, mem_toFinset, imp_self,
            implies_true, sum_count_eq_card, card_powersetCard]
            congr
            exact splits_iff_card_roots.mp hsplit

open Finset in
theorem card_eq_of_natDegree_le_of_coeff_le {n : ℕ} {B₁ B₂ : Fin (n + 1) → ℝ}
    (h_B : ∀ i, Int.ceil (B₁ i) ≤ Int.floor (B₂ i)) :
    Nat.card {p : ℤ[X] // p.natDegree ≤ n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i} =
    ∏ i : Fin (n + 1), (Int.floor (B₂ i) - Int.ceil (B₁ i) + 1)  := by
  let Bp := fun i ↦ Int.floor (B₂ i)
  let Bm := fun i ↦ Int.ceil (B₁ i)
  let Box := Icc Bm Bp
  let BoxPoly := {p : ℤ[X] // p.natDegree ≤ n ∧ ∀ i, B₁ i ≤ p.coeff i ∧ p.coeff i ≤ B₂ i}
  have hf (p : BoxPoly) : (fun i : Fin (n + 1) ↦ p.val.coeff i) ∈ Box := by
    simp only [mem_Icc, Box, Bm, Bp]
    obtain ⟨val, h_deg, bounds⟩ := p
    refine ⟨fun i ↦ Int.ceil_le.mpr (bounds i).1, fun i ↦ Int.le_floor.mpr (bounds i).2⟩
  let f : BoxPoly → Box := fun p => ⟨fun i ↦ p.val.coeff i, hf p⟩
  let g : Box → BoxPoly := fun p => ⟨ofFinToSemiring n p, by
    refine ⟨natDegree_le p.val, ?_⟩
    intro i
    obtain ⟨val, prop⟩ := p
    simp only [mem_Icc, Box, Bm, Bp] at prop
    simp only [coeff_eq_val_of_lt val i.2, Fin.cast_val_eq_self]
    refine ⟨Int.ceil_le.mp (prop.1 i), Int.le_floor.mp (prop.2 i)⟩
    ⟩
  have hfBij : f.Bijective := by
    refine Function.bijective_iff_has_inverse.mpr ⟨g, ?_, fun _ ↦ by simp [f, g]⟩
    intro p
    ext i
    simp only [Bm, f, Box, Bp, g, BoxPoly]
    by_cases h : i < n + 1
    · simp [h, Nat.mod_eq_of_modEq rfl h]
    · rw [not_lt] at h
      simp only [h, coeff_eq_zero_of_gt]
      replace h : n < i := h
      rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_le_of_lt p.property.1 h)]
  rw [Nat.card_eq_of_bijective f hfBij]
  simp only [Box, Nat.card_eq_finsetCard (Icc Bm Bp), Pi.card_Icc,
    Int.card_Icc, Bp, Bm, prod_const, card_univ, Fintype.card_fin, sub_neg_eq_add]
  push_cast
  congr
  ext i
  specialize h_B i
  rw [Int.ofNat_toNat, add_sub_right_comm ⌊B₂ i⌋ 1 ⌈B₁ i⌉]
  apply max_eq_left
  omega


/- open Finset in
theorem card_eq_of_natDegree_le_of_coeff_le' {B : NNReal} (n : ℕ) :
    Nat.card {p : ℤ[X] // p.natDegree ≤ n ∧ ∀ i, ‖p.coeff i‖₊ ≤ B} =
    (2 * Nat.floor B + 1) ^ (n + 1) := by
  let Bp := fun i : Fin (n + 1) ↦ (Nat.floor B : ℤ)
  let Bm := fun i : Fin (n + 1) ↦ -(Nat.floor B : ℤ)
  let Box := Icc Bm Bp
  let BoxPoly := {p : ℤ[X] // p.natDegree ≤ n ∧ ∀ i, ‖p.coeff i‖₊ ≤ B}
  have hf (p : BoxPoly) : (fun i : Fin (n + 1) ↦ p.val.coeff i) ∈ Box := by
    simp only [mem_Icc, Box, Bm, Bp]
    have hcoef := p.property.2
    simp_rw [← Int.abs_le_floor_nnreal_iff] at hcoef
    refine ⟨Pi.le_def.mpr (fun i ↦ neg_le_of_abs_le <| hcoef i),
      Pi.le_def.mpr (fun i ↦ le_of_max_le_left <| hcoef i)⟩
  let f : BoxPoly → Box := fun p => ⟨fun i ↦ p.val.coeff i, hf p⟩
  let g : Box → BoxPoly := fun p => ⟨ofFinToSemiring n p, by
    refine ⟨natDegree_le p.val, ?_⟩
    intro i
    by_cases h : n + 1 ≤ i
    · simp only [h, coeff_eq_zero_of_gt, nnnorm_zero, zero_le]
    · rw [not_le] at h
      obtain ⟨val, prop⟩ := p
      simp only [mem_Icc, Box, Bm, Bp] at prop
      simp [coeff_eq_val_of_lt val h, ← Int.abs_le_floor_nnreal_iff, abs_le, prop.1 i, prop.2 i]
    ⟩
  have hfBij : f.Bijective := by
    refine Function.bijective_iff_has_inverse.mpr ⟨g, ?_, fun _ ↦ by simp [f, g]⟩
    intro p
    ext i
    simp only
    by_cases h : i < n + 1
    · simp [h, Nat.mod_eq_of_modEq rfl h]
    · rw [not_lt] at h
      simp only [h, coeff_eq_zero_of_gt]
      replace h : n < i := h
      rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_le_of_lt p.property.1 h)]
  simp only [Nat.card_eq_of_bijective f hfBij, Box, Nat.card_eq_finsetCard (Icc Bm Bp), Pi.card_Icc,
    Int.card_Icc, Bp, Bm, prod_const, card_univ, Fintype.card_fin, sub_neg_eq_add]
  norm_cast
  --rw [Int.toNat_natCast]
  ring
 -/
/-
section Semiring

variable {R : Type u} [Semiring R]

noncomputable def polConstr (n : ℕ) := fun f : Fin (n + 1) → R ↦ ∑ i in Finset.range (n + 1),
  Polynomial.monomial i (f i)

noncomputable def foo (n : ℕ) : (Fin (n + 1) → R) → (ℕ →₀ R) := by
  intro v
  let f : ℕ → R := fun i => if h : i < n + 1 then v ⟨i, h⟩ else 0
  have hfin : f.support.Finite := Set.Finite.subset (Finset.finite_toSet (Finset.range (n + 1)))
    (by  simp_all [f])
  exact {toFun := f, support := hfin.toFinset, mem_support_toFun := (by simp [f])}

noncomputable def polConstr' (n : ℕ) : (Fin (n + 1) → R) →+ R[X] where
  toFun t := ⟨foo n t⟩
  map_add' x y := by
    ext m
    simp only [foo, Pi.add_apply, coeff_ofFinsupp, Finsupp.coe_mk, coeff_add]
    split; all_goals simp
  map_zero' := by
    simp only [foo, Pi.zero_apply, dite_eq_ite, ite_self, Function.support_zero,
      Set.toFinite_toFinset, Set.toFinset_empty, ofFinsupp_eq_zero]
    rfl

end Semiring

open Finset in
theorem trivial' {B : NNReal} (n : ℕ) : Nat.card {p : ℤ[X] // p.natDegree ≤ n ∧
    univ.sup (fun i : Fin (n + 1) ↦ ‖p.coeff i‖₊) ≤ B} = (2 * (Nat.floor B) + 1) ^ (n + 1) := by
  simp only [Finset.sup_le_iff, mem_univ, forall_const, Set.coe_setOf]
  let Bp := fun i : Fin (n + 1) ↦ (Nat.floor B : ℤ)
  let Bm := fun i : Fin (n + 1) ↦ -(Nat.floor B : ℤ)
  let Box := Icc Bm Bp
  let BoxPoly := {p : ℤ[X] // p.natDegree ≤ n ∧ ∀ i : Fin (n + 1), ‖p.coeff i‖₊ ≤ B}
  have hf (p : BoxPoly) : (fun i : Fin (n + 1) ↦ p.val.coeff i) ∈ Box := by
    simp only [mem_Icc, Box, Bm, Bp]
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
        simp only [mem_range] at hi
        rw [Polynomial.natDegree_monomial i (v i)]
        split
        next h => simp_all only [zero_le]
        next h => exact Nat.le_of_lt_succ hi
      . intro i
        simp only [polConstr]
        simp only [finset_sum_coeff,  Polynomial.coeff_monomial]
        simp only [sum_ite_eq', mem_range, Fin.is_lt, ↓reduceIte,
          Fin.cast_val_eq_self]
        simp only [mem_Icc, Box, Bm, Bp] at hv
        obtain ⟨left, right⟩ := hv
        rw [← Int.abs_le_floor_nnreal_iff]
        specialize left i
        specialize right i
        simp_all only
        rw [abs_le]
        exact And.symm ⟨right, left⟩
    use p
    simp only
    constructor
    · ext i
      simp only [f, Subtype.coe_mk, polConstr, finset_sum_coeff, Polynomial.coeff_monomial, sum_ite_eq', mem_range, Fin.is_lt, ↓reduceIte,
          Fin.cast_val_eq_self]
    · intro q hq
      apply Subtype.eq
      rw [← Polynomial.coeff_inj]
      ext i
      simp only [f, Subtype.coe_mk, polConstr, finset_sum_coeff, Polynomial.coeff_monomial, sum_ite_eq', mem_range, Fin.is_lt, ↓reduceIte,
          Fin.cast_val_eq_self] at hq
      simp only [Subtype.mk.injEq] at hq
      subst hq
      simp_all only
      obtain ⟨q, propertyq⟩ := q
      obtain ⟨degq, boxq⟩ := propertyq
      obtain ⟨p1, propertyp⟩ := p
      obtain ⟨degp, boxp⟩ := propertyp
      simp only [polConstr, Fin.val_natCast, finset_sum_coeff, coeff_monomial, sum_ite_eq',
        mem_range]
      by_cases h : i < n + 1
      · simp_all only [mem_Icc, ↓reduceIte, Box, Bm, Bp]
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
  convert_to (Icc Bm Bp).card = (2 * (Nat.floor B) + 1) ^ (n + 1)
  · exact Nat.card_eq_finsetCard (Finset.Icc Bm Bp)
  simp_rw [Pi.card_Icc, Int.card_Icc, Bp, Bm]
  simp only [sub_neg_eq_add, prod_const, card_univ, Fintype.card_fin, zero_le, ne_eq,
    AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false, not_false_eq_true, pow_left_inj₀]
  zify
  rw [Int.toNat_eq_max, add_comm, ← add_assoc]
  have : ↑⌊B⌋₊ + ↑⌊B⌋₊ = 2 * (⌊B⌋₊ : ℤ) := by ring
  simp_rw [this]
  exact rfl
 -/
--#min_imports

/-
#find_home! bdd_coeff_of_bdd_roots_and_lead
says
[Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order,
Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog,
Mathlib.Analysis.CStarAlgebra.SpecialFunctions.PosPart] -/

end Polynomial
