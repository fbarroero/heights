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

open Real

noncomputable def logMahlerMeasure (p : ℂ[X]) :=
    (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖

theorem logMahlerMeasure_def (p : ℂ[X]) : p.logMahlerMeasure =
    (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖ := rfl

@[simp]
theorem logMahlerMeasure_zero : (0 : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_one : (1 : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_const (z : ℂ) : (C z).logMahlerMeasure = log ‖z‖ := by
  field_simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_X : (X : ℂ[X]).logMahlerMeasure = 0 := by simp [logMahlerMeasure]

@[simp]
theorem logMahlerMeasure_monomial (n : ℕ) (z : ℂ) : (monomial n z).logMahlerMeasure = log ‖z‖ := by
  field_simp [logMahlerMeasure]

noncomputable def MahlerMeasure (p : ℂ[X]) := if p ≠ 0 then exp (p.logMahlerMeasure) else 0

theorem MahlerMeasure_def {p : ℂ[X]} (hp : p ≠ 0): p.MahlerMeasure =
    exp ((2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖) :=
  by simp [MahlerMeasure, hp, logMahlerMeasure_def]

theorem logMahlerMeasure_eq_log_MahlerMeasure {p : ℂ[X]} (h_p : p ≠ 0) :
    p.logMahlerMeasure = log p.MahlerMeasure := by simp [logMahlerMeasure, MahlerMeasure, h_p]

@[simp]
theorem MahlerMeasure_zero : (0 : ℂ[X]).MahlerMeasure = 0 := by simp [MahlerMeasure]

@[simp]
theorem MahlerMeasure_one : (1 : ℂ[X]).MahlerMeasure = 1 :=by simp [MahlerMeasure]

@[simp]
theorem MahlerMeasure_const (z : ℂ) : (C z).MahlerMeasure = ‖z‖ := by
  simp only [MahlerMeasure, ne_eq, map_eq_zero, logMahlerMeasure_const, ite_not]
  split_ifs with h
  · simp [h]
  · simp [h, exp_log]

theorem MahlerMeasure_nonneg (p : ℂ[X]) : 0 ≤ p.MahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  rw [MahlerMeasure_def hp]
  apply exp_nonneg

@[simp]
theorem MahlerMeasure_eq_zero_iff (p : ℂ[X]) : p.MahlerMeasure = 0 ↔ p = 0 := by
  refine ⟨?_, by simp_all [MahlerMeasure_zero]⟩
  contrapose!
  intro h
  simp [MahlerMeasure_def h]

lemma MahlerMeasure_integrable (p : ℂ[X]) : IntervalIntegrable (fun x ↦ log ‖eval (circleMap 0 1 x) p‖) MeasureTheory.volume 0 (2 * π) := by
  -- Kebekus
  sorry

@[simp]
theorem MahlerMeasure_prod (p q : ℂ[X]) : (p * q).MahlerMeasure =
    p.MahlerMeasure * q.MahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  rw [← ne_eq] at hp hq
  simp only [MahlerMeasure, ne_eq, mul_eq_zero, hp, hq, or_self, not_false_eq_true, ↓reduceIte,
    logMahlerMeasure, mul_inv_rev, eval_mul, Complex.norm_mul]
  rw [← exp_add, ← left_distrib]
  congr
  rw [← intervalIntegral.integral_add (MahlerMeasure_integrable p) (MahlerMeasure_integrable q)]
  apply intervalIntegral.integral_congr_ae
  rw [MeasureTheory.ae_iff]
  apply Set.Finite.measure_zero _ MeasureTheory.volume
  simp only [Classical.not_imp]
  --have hpq : p * q ≠ 0 := (mul_ne_zero_iff_right hq).mpr hp
  apply Set.Finite.of_finite_image (f := circleMap 0 1)
  · apply Set.Finite.subset (Multiset.finite_toSet (p * q).roots)
    rintro z ⟨_, ha, _⟩
    simp only [mem_roots', ne_eq, mul_eq_zero, hp, hq, or_self, not_false_eq_true, IsRoot.def,
      true_and, Set.mem_setOf_eq]
    obtain ⟨_, prop⟩ := ha
    contrapose prop
    rw [log_mul]<;>
    simp_all
  · exact Set.InjOn.mono (fun _ hx ↦ hx.1) (injOn_circleMap_of_abs_sub_le (zero_ne_one' ℝ).symm (by simp [le_of_eq, pi_nonneg]))


theorem logMahlerMeasure_eq (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + ((p.roots).map (fun a ↦ max 0 log ‖a‖)).sum := by sorry --use jensen kebekus

theorem logMahlerMeasure_eq_nnnorm (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖₊ + ((p.roots).map (fun a ↦ max 0 log ‖a‖₊)).sum := by
  simp [logMahlerMeasure_eq]

/- theorem logMahlerMeasure_eq' (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + ∑ (a ∈ p.roots), (0 ⊔ (log ‖a‖)) := by sorry
 -/
theorem MahlerMeasure_eq (p : ℂ[X]) : p.MahlerMeasure =
    ‖p.leadingCoeff‖ * ((p.roots).map (fun a ↦ max 1 ‖a‖)).prod := by
  by_cases hp : p = 0; simp [hp]
  simp only [MahlerMeasure, ne_eq, hp, not_false_eq_true, ↓reduceIte, logMahlerMeasure_eq,
    Pi.sup_apply, Pi.zero_apply]
  rw [exp_add, exp_log (norm_pos_iff.mpr <| leadingCoeff_ne_zero.mpr hp)]
  simp only [exp_multiset_sum, Multiset.map_map, Function.comp_apply, mul_eq_mul_left_iff,
    norm_eq_zero, leadingCoeff_eq_zero, hp, or_false]
  apply congr_arg _ <|Multiset.map_congr rfl _
  intro x hx
  rw [Monotone.map_max exp_monotone]
  by_cases h : x = 0; simp [h]
  simp [exp_log <| norm_pos_iff.mpr h]

theorem MahlerMeasure_eq_nnnorm (p : ℂ[X]) : p.MahlerMeasure =
    ‖p.leadingCoeff‖₊ * ((p.roots).map (fun a ↦ max 1 ‖a‖₊)).prod := by
  by_cases hp : p = 0; simp [hp]
  push_cast
  simp [MahlerMeasure_eq, hp]

@[simp]
theorem MahlerMeasure_C_mul_X_add_C {z₁ z₀ : ℂ} (h1 : z₁ ≠ 0) : (C z₁ * X + C z₀).MahlerMeasure =
    ‖z₁‖ * max 1 ‖z₁⁻¹ * z₀‖ := by
  have hpol : C z₁ * X + C z₀ ≠ 0 := by simp [← degree_ne_bot, h1]
  simp only [MahlerMeasure, ne_eq, hpol, not_false_eq_true, ↓reduceIte, logMahlerMeasure_eq,
    roots_C_mul_X_add_C z₀ h1, Pi.sup_apply, Pi.zero_apply, Multiset.map_singleton, norm_neg,
    Complex.norm_mul, norm_inv, Multiset.sum_singleton]
  rw [exp_add, exp_log (norm_pos_iff.mpr <| leadingCoeff_ne_zero.mpr hpol)]
  simp only [Monotone.map_max exp_monotone, exp_zero]
  by_cases hz₀ : z₀ = 0; simp [hz₀]
  congr
  · simp [leadingCoeff, h1]
  · rw [exp_log (mul_pos (inv_pos.mpr <| norm_pos_iff.mpr h1)
      <| norm_pos_iff.mpr hz₀)]

@[simp]
theorem MahlerMeasure_degree_eq_one {p :ℂ[X]} (h : p.degree = 1) : p.MahlerMeasure =
    ‖p.coeff 1‖ * max 1 ‖(p.coeff 1)⁻¹ * p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (show degree p ≤ 1 by rw [h])]
  simp [show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h]

@[simp]
theorem logMahlerMeasure_C_mul_X_add_C {z₁ z₀ : ℂ} (h1 : z₁ ≠ 0) : (C z₁ * X + C z₀).logMahlerMeasure =
    log (‖z₁‖ * max 1 ‖z₁⁻¹ * z₀‖) := by
  have hpol : C z₁ * X + C z₀ ≠ 0 := by simp [← degree_ne_bot, h1]
  rw [logMahlerMeasure_eq_log_MahlerMeasure hpol, MahlerMeasure_C_mul_X_add_C h1]

lemma one_le_prod_max_one_norm_roots (p : ℂ[X]) :
    1 ≤ (p.roots.map (fun a ↦ max 1 ‖a‖)).prod := by
  refine Multiset.one_le_prod ?_
  simp only [Multiset.mem_map]
  rintro _ ⟨a, _, rfl⟩
  exact le_max_left 1 ‖a‖

lemma leading_coeff_le_mahlerMeasure (p : ℂ[X]) : ‖p.leadingCoeff‖ ≤ p.MahlerMeasure := by
  rw [MahlerMeasure_eq]
  exact le_mul_of_one_le_right (norm_nonneg p.leadingCoeff) (one_le_prod_max_one_norm_roots p)

lemma prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leading_coeff {p : ℂ[X]}
    (hlc : 1 ≤ ‖p.leadingCoeff‖) : (p.roots.map (fun a ↦ max 1 ‖a‖)).prod ≤ p.MahlerMeasure := by
  rw [MahlerMeasure_eq]
  exact le_mul_of_one_le_left (le_trans zero_le_one (one_le_prod_max_one_norm_roots p)) hlc

theorem roots_le_mahlerMeasure_of_one_le_leading_coeff {p : ℂ[X]} (hlc : 1 ≤ ‖p.leadingCoeff‖) :
    (p.roots.map (fun x ↦ ‖x‖₊)).sup ≤ p.MahlerMeasure := by
  apply le_trans _ <| prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leading_coeff hlc
  have : (Multiset.map (fun a ↦ 1 ⊔ ‖a‖) p.roots).prod = (Multiset.map (fun a ↦ 1 ⊔ ‖a‖₊) p.roots).prod := by
    norm_cast
    simp
  rw [this]
  simp only [NNReal.coe_le_coe, Multiset.sup_le, Multiset.mem_map, ne_eq, IsRoot.def,
    forall_exists_index, and_imp]
  intro b x hx hxb
  rw [← hxb]
  apply le_trans <| le_max_right 1 _
  refine Multiset.single_le_prod ?_ (1 ⊔ ‖x‖₊) (Multiset.mem_map_of_mem (fun a ↦ 1 ⊔ ‖a‖₊) hx)
  simp only [Multiset.mem_map]
  rintro _ ⟨_, _, rfl⟩
  simp

private lemma bar (p q : Prop) : (p → q) ∧ p ↔ (p ∧ q) := by
  apply Iff.intro
  · intro a
    simp_all only [and_self]
  · intro a
    simp_all only [imp_self, and_self]

open Set in
lemma l1 (p : ℂ[X]) : p.MahlerMeasure ≤  ∑ i : Fin (p.natDegree + 1), ‖toFn (p.natDegree + 1) p i‖ := by
  by_cases hp : p = 0; simp [hp]
  simp only [MahlerMeasure, ne_eq, hp, not_false_eq_true, ↓reduceIte, logMahlerMeasure, mul_inv_rev]
  calc
  rexp (π⁻¹ * 2⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖) ≤
      rexp (π⁻¹ * 2⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log (∑ i : Fin (p.natDegree + 1), ‖toFn (p.natDegree + 1) p i‖)) := by
    gcongr
    apply intervalIntegral.integral_mono_ae_restrict (le_of_lt two_pi_pos) (MahlerMeasure_integrable p) (by simp)
    simp only [Filter.EventuallyLE, Filter.eventually_iff_exists_mem]
    let v := {x : ℝ | x ∈ Icc 0 (2 * π) ∧ eval (circleMap 0 1 x) p ≠ 0}
    use v
    constructor
    · rw [MeasureTheory.mem_ae_iff]
      simp only [compl, ne_eq, mem_setOf_eq, not_and, Decidable.not_not, and_imp,
        measurableSet_Icc, MeasureTheory.Measure.restrict_apply', Inter.inter, Set.inter, v, bar]
      refine Set.Finite.measure_zero ?_ MeasureTheory.volume
      have h1 : {a | a ∈ Icc 0 (2 * π) ∧ eval (circleMap 0 1 a) p = 0} \ {2 * π} = {a | a ∈ Ico 0 (2 * π) ∧ eval (circleMap 0 1 a) p = 0} := by
        ext x
        simp only [mem_Icc, mem_diff, mem_setOf_eq, mem_singleton_iff, mem_Ico, v]
        apply Iff.intro
        · intro a
          simp_all only [true_and, and_true, v]
          obtain ⟨left, right⟩ := a
          obtain ⟨left, right_1⟩ := left
          obtain ⟨left, right_2⟩ := left
          exact lt_of_le_of_ne right_2 right
        · intro a
          simp_all only [true_and, and_true, v]
          obtain ⟨left, right⟩ := a
          obtain ⟨left, right_1⟩ := left
          apply And.intro
          · exact le_of_lt right_1
          · apply Aesop.BuiltinRules.not_intro
            intro a
            subst a
            simp_all only [Nat.ofNat_pos, mul_nonneg_iff_of_pos_left, lt_self_iff_false, v]
      have : {a | a ∈ Icc 0 (2 * π) ∧ eval (circleMap 0 1 a) p = 0}.Finite ↔ {a | a ∈ Ico 0 (2 * π) ∧ eval (circleMap 0 1 a) p = 0}.Finite := by
        constructor
        · intro h
          rw [← h1]
          exact Finite.diff h
        · intro h
          apply Set.Finite.of_diff (t := {2 * π})
          rw [← h1] at h
          exact h
          exact finite_singleton (2 * π)
      rw [this]
      apply Set.Finite.of_finite_image (f := circleMap 0 1)
      · apply Set.Finite.subset (Multiset.finite_toSet (p.roots))
        simp_all only [mem_Icc, mem_Ico, mem_roots', ne_eq, not_false_eq_true, IsRoot.def, true_and, image_subset_iff,
          preimage_setOf_eq, setOf_subset_setOf, implies_true, v]
      · intro _ hx _ hy h
        exact injOn_circleMap_of_abs_sub_le' (c := 0) (one_ne_zero) (by linarith) hx.1 hy.1 h
    · intro x hx
      gcongr; simp_all [v]
      simp only [eval, eval₂, RingHom.id_apply, toFn, LinearMap.pi_apply, lcoeff_apply, v]
      trans p.sum (fun i a ↦ ‖a * (circleMap 0 1 x) ^ i‖)
      · -- generalise this, triangular ineq for Polynomial.sum
        simp only [sum, Complex.norm_mul, norm_pow, norm_circleMap_zero, abs_one, one_pow, mul_one,
        v]
        refine norm_sum_le_of_le p.support ?_
        simp
      · --sum_eq_of_subset
        simp only [Complex.norm_mul, norm_pow, norm_circleMap_zero, abs_one, one_pow, mul_one, v]
        rw [sum_eq_of_subset (s := Finset.range (p.natDegree + 1)) _ (by simp) supp_subset_range_natDegree_succ]
        apply le_of_eq
        exact Finset.sum_range fun i ↦ ‖p.coeff i‖
  _ ≤ rexp (log (∑ i : Fin (p.natDegree + 1), ‖toFn (p.natDegree + 1) p i‖)) := by
    gcongr
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring_nf
    simp [pi_ne_zero]
  _ ≤ ∑ i : Fin (p.natDegree + 1), ‖(toFn (p.natDegree + 1)) p i‖ := by
    rw [exp_log]
    apply Finset.sum_pos' (fun i _ ↦ norm_nonneg (toFn (p.natDegree + 1) p i))
    use ⟨p.natDegree, lt_add_one p.natDegree⟩
    simp only [Finset.mem_univ, norm_pos_iff, ne_eq, true_and]
    contrapose hp
    simp_all [toFn]

open Finset BigOperators in
theorem prod_le_prod_of_subset_of_one_le'' {ι : Type*}  {f : ι → ℝ} {s t : Finset ι} (h1 : 1 ≤ ∏ i ∈ s, f i) (h : s ⊆ t) (hf : ∀ i ∈ t, 1 ≤ f i) :
    ∏ i ∈ s, f i ≤ ∏ i ∈ t, f i := by
  classical calc
      ∏ i ∈ s, f i ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i := by
        refine le_mul_of_one_le_left (le_trans zero_le_one h1) ?_

        apply Multiset.one_le_prod
        intro a ha

        simp_all only [sdiff_val, Multiset.mem_map]
        obtain ⟨w, h_1⟩ := ha
        obtain ⟨left, right⟩ := h_1
        subst right
        apply hf w
        refine mem_def.mpr ?_

        sorry
        --le_mul_of_one_le_left' <| one_le_prod' <| by simpa only [mem_sdiff, and_imp]
      _ = ∏ i ∈ t \ s ∪ s, f i := (prod_union sdiff_disjoint).symm
      _ = ∏ i ∈ t, f i := by rw [sdiff_union_of_subset h]



open Multiset in
theorem norm_coeff_le_binom_mahlerMeasure (n : ℕ) (p : ℂ[X]) : ‖p.coeff n‖ ≤ (p.natDegree).choose (p.natDegree - n) * p.MahlerMeasure := by
  --case p 0
  by_cases hp : p = 0; simp [hp]
  by_cases hn: p.natDegree < n; simp [coeff_eq_zero_of_natDegree_lt hn, le_of_lt hn, MahlerMeasure_nonneg]
  rw [not_lt] at hn
  rw [MahlerMeasure_eq, coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgClosed.splits p)) hn]
  rw [← mul_assoc, mul_comm _ ‖p.leadingCoeff‖, mul_assoc ‖p.leadingCoeff‖]
  simp only [Complex.norm_mul, norm_pow, norm_neg, norm_one, one_pow, mul_one]
  rw [mul_le_mul_left (norm_pos_iff.mpr (leadingCoeff_ne_zero.mpr hp))]
  simp only [esymm, Finset.sum_multiset_map_count, nsmul_eq_mul]
  apply le_trans <| norm_sum_le _ _
  simp_rw [/- Finset.prod_multiset_count ,-/ norm_mul]
  let S := (powersetCard (p.natDegree - n) p.roots)


  --let T := (Multiset.map (fun a ↦ 1 ⊔ ‖a‖) p.roots)

  calc
  ∑ x ∈ S.toFinset, ‖(count x S : ℂ)‖ * ‖x.prod‖
     ≤ ∑ x ∈ S.toFinset, ‖(count x S : ℂ)‖ * ((p.roots).map (fun a ↦ max 1 ‖a‖)).prod := by
    simp [S]
    gcongr with x hx
    simp_all only [mem_toFinset, mem_powersetCard, S]
    obtain ⟨left, right⟩ := hx
    simp only [Finset.prod_multiset_count, norm_prod, norm_pow, S]
    calc
    ∏ x_1 ∈ x.toFinset, ‖x_1‖ ^ count x_1 x
      ≤ ∏ x_1 ∈ x.toFinset, (1 ⊔ ‖x_1‖) ^ count x_1 x := by
      gcongr with a
      exact le_max_right 1 ‖a‖
    _ ≤ ∏ x_1 ∈ p.roots.toFinset, (1 ⊔ ‖x_1‖) ^ count x_1 x := by
      apply prod_le_prod_of_subset_of_one_le''
      --lift to nnnreals
      --apply Finset.prod_le_prod_of_subset_of_one_le' (s:= x.toFinset) (t := p.roots.toFinset) (f := fun x_1 ↦ (1 ⊔ ‖x_1‖) ^ count x_1 x)
      sorry
      sorry
    _ = ∏ m ∈ (Multiset.map (fun a ↦ 1 ⊔ ‖a‖) p.roots).toFinset, m ^ count m (Multiset.map (fun a ↦ 1 ⊔ ‖a‖) p.roots) := by

      sorry




    /- trans ∏ x_1 ∈ x.toFinset, (1 ⊔ ‖x_1‖) ^ count x_1 x
    · gcongr with a
      exact le_max_right 1 ‖a‖
    · sorry -/
  _  ≤ ↑(p.natDegree.choose (p.natDegree - n)) * (Multiset.map (fun a ↦ 1 ⊔ ‖a‖) p.roots).prod := by
    simp only [Complex.norm_natCast, ← Finset.sum_mul]
    gcongr

    sorry
    simp only [S]
    norm_cast
    simp only [mem_powersetCard, mem_toFinset, imp_self, implies_true, sum_count_eq_card,
      card_powersetCard, S]
    apply le_of_eq
    congr
    exact splits_iff_card_roots.mp (IsAlgClosed.splits p)
  /-




  calc
  ∑ x ∈ S.toFinset, ‖(count x S : ℂ)‖ * ∏ x_1 ∈ x.toFinset, ‖x_1‖ ^ count x_1 x




     ≤ ∑ x ∈ S.toFinset, ‖(count x S : ℂ)‖ * ((p.roots).map (fun a ↦ max 1 ‖a‖)).prod := by sorry
  _  ≤ ↑(p.natDegree.choose (p.natDegree - n)) * (Multiset.map (fun a ↦ 1 ⊔ ‖a‖) p.roots).prod := by
    simp
    sorry
 -/


end Polynomial
