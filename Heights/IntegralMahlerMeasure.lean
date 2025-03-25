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
    (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖(fun z : ℂ ↦ p.eval z) (circleMap 0 1 x)‖

theorem logMahlerMeasure_def (p : ℂ[X]) : p.logMahlerMeasure =
    (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖(fun z : ℂ ↦ p.eval z) (circleMap 0 1 x)‖ := rfl

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
theorem logMahlerMeasure_monomial (n : ℕ) (z : ℂ) : (monomial n z).logMahlerMeasure = log ‖z‖  := by
  field_simp [logMahlerMeasure]

noncomputable def MahlerMeasure (p : ℂ[X]) := if p ≠ 0 then exp (p.logMahlerMeasure) else 0

theorem MahlerMeasure_def {p : ℂ[X]} (hp : p ≠ 0): p.MahlerMeasure =
    exp ((2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖(fun z : ℂ ↦ p.eval z) (circleMap 0 1 x)‖) :=
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

lemma MahlerMeasure_integrable (p : ℂ[X]) : IntervalIntegrable (fun x ↦ log ‖eval (circleMap 0 1 x) p‖) MeasureTheory.volume 0 (2 * π) := by
  -- Kebekus
  sorry
--in PR
lemma circleMap_eq_circleMap_iff_exists_int {a b r : ℝ} {z : ℂ} (h_r : r ≠ 0) : circleMap z r a = circleMap z r b ↔ ∃ (n : ℤ) , a * Complex.I = b * Complex.I + n * (2 * π * Complex.I) := by
  constructor
  · have : circleMap z r a = circleMap z r b  ↔ (Complex.exp (a * Complex.I)).arg = (Complex.exp (b * Complex.I)).arg := by
      simp [circleMap, Complex.ext_norm_arg_iff, h_r]
    simp [this, Complex.arg_eq_arg_iff, Complex.exp_eq_exp_iff_exists_int]
  · simp [circleMap, h_r, Complex.exp_eq_exp_iff_exists_int]
--in PR
lemma eq_of_circleMap_eq {a b r : ℝ} {z : ℂ} (h_r : r ≠ 0) (h_dist : |a - b| < 2 * π) (h : circleMap z r a = circleMap z r b) :
    a = b := by
  rw [circleMap_eq_circleMap_iff_exists_int h_r] at h
  obtain ⟨n, hn⟩ := h
  simp only [show n * (2 * π * Complex.I) = (n * 2 * π) * Complex.I by ring, ← add_mul, mul_eq_mul_right_iff, Complex.I_ne_zero, or_false] at hn
  norm_cast at hn
  simp only [hn, Int.cast_mul, Int.cast_ofNat, mul_assoc, add_sub_cancel_left, abs_mul,
    Nat.abs_ofNat, abs_of_pos pi_pos] at h_dist
  field_simp at h_dist
  norm_cast at h_dist
  simp [hn, Int.abs_lt_one_iff.mp h_dist]
--in PR
theorem injOn_circleMap_of_lt {a b r : ℝ} {z : ℂ} (h_r : r ≠ 0) (h_dist : |a - b| ≤ 2 * π) :
    (Ι a b).InjOn (circleMap z r) := by
  rintro _ ⟨_, _⟩ _ ⟨_, _⟩ h
  apply eq_of_circleMap_eq h_r _ h
  rw [abs_lt]
  constructor <;> linarith [max_sub_min_eq_abs' a b]

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
  · exact Set.InjOn.mono (fun _ hx ↦ hx.1) (injOn_circleMap_of_lt (zero_ne_one' ℝ).symm (by simp [le_of_eq, pi_nonneg]))


theorem logMahlerMeasure_eq (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + ((p.roots).map (fun a ↦ max 0 log ‖a‖)).sum := by sorry --use jensen kebekus

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


lemma l1 (p : ℂ[X]) : p.MahlerMeasure ≤  ∑ i : Fin (p.natDegree + 1), ‖toFn (p.natDegree + 1) p i‖ := by
  by_cases hp : p = 0; simp [hp]
  simp only [MahlerMeasure, ne_eq, hp, not_false_eq_true, ↓reduceIte, logMahlerMeasure, mul_inv_rev]
  calc
  rexp (π⁻¹ * 2⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖) ≤
      rexp (π⁻¹ * 2⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log (∑ i : Fin (p.natDegree + 1), ‖toFn (p.natDegree + 1) p i‖)) := by
    gcongr
    apply intervalIntegral.integral_mono (le_of_lt two_pi_pos) (MahlerMeasure_integrable p) (by simp)
    -- meglio almost everywhere per evitare radici di f?
    intro x
    simp only
    by_cases h : eval (circleMap 0 1 x) p = 0
    simp [h]
    apply log_nonneg

    sorry
    sorry
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
/-


  trans (rexp (log (∑ i : Fin (p.natDegree + 1), ‖toFn (p.natDegree + 1) p i‖)))
  gcongr
  rw [← intervalIntegral.integral_const_mul]


  sorry
 -/

--Finset.sum univ (fun i : Fin p.natDegree ↦ ‖toFn p.natDegree p i‖)

end Polynomial
