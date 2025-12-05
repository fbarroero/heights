/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib
/-!
# Mahler Measure of complex polynomials

In this file we define the Mahler measure of a polynomial over `ℂ[X]` and prove some basic
properties.

## Main definitions

- `Polynomial.logMahlerMeasure p`: the logarithmic Mahler measure of a polynomial `p` defined as
`(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖`.
- `Polynomial.mahlerMeasure p`: the (exponential) Mahler measure of a polynomial `p`, which is equal
to `e ^ (logMahlerMeasure p)` if `p` is nonzero, and `0` otherwise.

## Main results

- `Polynomial.mahlerMeasure_mul`: the Mahler measure of the product of two polynomials is the
product of their Mahler measures.
-/

namespace Polynomial

open Real
/-
/-- The logarithmic Mahler measure of a polynomial `p` defined as
`(2 * π)⁻¹ * ∫ x ∈ (0, 2 * π), log ‖p (e ^ (i * x))‖` -/
noncomputable def logMahlerMeasure (p : ℂ[X]) := circleAverage (fun x ↦ log ‖eval x p‖) 0 1

theorem logMahlerMeasure_def (p : ℂ[X]) : p.logMahlerMeasure = circleAverage (fun x ↦ log ‖eval x p‖) 0 1 := rfl
   -- (2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖ := rfl

@[simp]
theorem logMahlerMeasure_zero : (0 : ℂ[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
theorem logMahlerMeasure_one : (1 : ℂ[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
theorem logMahlerMeasure_const (z : ℂ) : (C z).logMahlerMeasure = log ‖z‖ := by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

@[simp]
theorem logMahlerMeasure_X : (X : ℂ[X]).logMahlerMeasure = 0 := by
  simp [logMahlerMeasure_def, circleAverage_def]

@[simp]
theorem logMahlerMeasure_monomial (n : ℕ) (z : ℂ) : (monomial n z).logMahlerMeasure = log ‖z‖ := by
  simp [logMahlerMeasure_def, circleAverage_def, mul_assoc]

/-- The Mahler measure of a polynomial `p` defined as `e ^ (logMahlerMeasure p)` if `p` is nonzero
and `0` otherwise -/
noncomputable def mahlerMeasure (p : ℂ[X]) := if p ≠ 0 then exp (p.logMahlerMeasure) else 0

theorem mahlerMeasure_def_of_ne_zero {p : ℂ[X]} (hp : p ≠ 0): p.mahlerMeasure =
    exp ((2 * π)⁻¹ * ∫ (x : ℝ) in (0)..(2 * π), log ‖eval (circleMap 0 1 x) p‖) :=
  by simp [mahlerMeasure, hp, logMahlerMeasure_def, circleAverage_def]

theorem logMahlerMeasure_eq_log_MahlerMeasure {p : ℂ[X]} :
    p.logMahlerMeasure = log p.mahlerMeasure := by
  rw [mahlerMeasure]
  split_ifs <;> simp_all [logMahlerMeasure_def, circleAverage_def]

@[simp]
theorem mahlerMeasure_zero : (0 : ℂ[X]).mahlerMeasure = 0 := by simp [mahlerMeasure]

@[simp]
theorem mahlerMeasure_one : (1 : ℂ[X]).mahlerMeasure = 1 := by simp [mahlerMeasure]

@[simp]
theorem mahlerMeasure_const (z : ℂ) : (C z).mahlerMeasure = ‖z‖ := by
  simp only [mahlerMeasure, ne_eq, map_eq_zero, logMahlerMeasure_const, ite_not]
  split_ifs with h
  · simp [h]
  · simp [h, exp_log]

theorem mahlerMeasure_nonneg (p : ℂ[X]) : 0 ≤ p.mahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  rw [mahlerMeasure_def_of_ne_zero hp]
  apply exp_nonneg

@[simp]
theorem mahlerMeasure_eq_zero_iff (p : ℂ[X]) : p.mahlerMeasure = 0 ↔ p = 0 := by
  refine ⟨?_, by simp_all [mahlerMeasure_zero]⟩
  contrapose
  exact fun h ↦ by simp [mahlerMeasure_def_of_ne_zero h]

lemma meromorphicAt_aeval (x : ℂ) (p : ℂ[X]) : MeromorphicAt (fun z ↦ aeval z p) x := by --add this somewhere
  use 0
  simp [-coe_aeval_eq_eval, AnalyticAt.aeval_polynomial, Differentiable.analyticAt]


private lemma mahlerMeasure_integrable (p : ℂ[X]) :
    IntervalIntegrable (fun x ↦ log ‖p.eval (circleMap 0 1 x)‖) MeasureTheory.volume 0 (2 * π) := by
  --lasciare come sopra
  sorry

theorem mahlerMeasure_mul (p q : ℂ[X]) : (p * q).mahlerMeasure =
    p.mahlerMeasure * q.mahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  rw [← ne_eq] at hp hq
  simp only [mahlerMeasure, ne_eq, mul_eq_zero, hp, hq, or_self, not_false_eq_true, ↓reduceIte,
    logMahlerMeasure, eval_mul, norm_mul, circleAverage_def, mul_inv_rev, smul_eq_mul]
  rw [← exp_add, ← left_distrib]
  congr
  rw [← intervalIntegral.integral_add (mahlerMeasure_integrable p) (mahlerMeasure_integrable q)]
  apply intervalIntegral.integral_congr_ae
  rw [MeasureTheory.ae_iff]
  apply Set.Finite.measure_zero _ MeasureTheory.volume
  simp only [Classical.not_imp]
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
 -/
/-
--In mathlib
theorem mahlerMeasure_pos_of_ne_zero0 {p : ℂ[X]} (hp : p ≠ 0) : 0 < p.mahlerMeasure := by
  grind [exp_pos, mahlerMeasure_def_of_ne_zero]

--In mathlib
theorem prod_mahlerMeasure_eq_mahlerMeasure_prod0 (s : Multiset ℂ[X]) :
    (s.prod).mahlerMeasure = (s.map (fun p ↦ p.mahlerMeasure)).prod := by
  induction' s using Multiset.induction_on with _ _ ih
  · simp
  · simp [mahlerMeasure_mul, ih]

--In mathlib
theorem logMahlerMeasure_mul_eq_add_logMahelerMeasure0 {p q : ℂ[X]} (hpq : p * q ≠ 0) :
    (p * q).logMahlerMeasure = p.logMahlerMeasure + q.logMahlerMeasure := by
  simp_all [logMahlerMeasure_eq_log_MahlerMeasure, mahlerMeasure_mul, log_mul]

--In mathlib
theorem posLog_eq_log_max_one0 {x : ℝ} (hx : 0 ≤ x) : log⁺ x = log (max 1 x) := by
  grind [le_abs, posLog_eq_log, log_one, max_eq_left, log_nonpos, posLog_def]

theorem logMahlerMeasure_C_mul0 {a : ℂ} (ha : a ≠ 0) {p : ℂ[X]} (hp : p ≠ 0) :
    (C a * p).logMahlerMeasure = log ‖a‖ + p.logMahlerMeasure := by
  rw [logMahlerMeasure_mul_eq_add_logMahelerMeasure0 (by simp [ha, hp]), logMahlerMeasure_const]

open MeromorphicOn Metric in
/-- The logarithmic Mahler measure of `X - C z` is `log⁺` of the absolute value of `z`. -/
@[simp]
theorem logMahlerMeasure_X_sub_C0 (z : ℂ) : (X - C z).logMahlerMeasure = log⁺ ‖z‖ := by
  by_cases hz₀ : z = 0
  · simp [hz₀, posLog_def]
  have hmeroOn (U : Set ℂ) : MeromorphicOn (fun x ↦ x - z) U :=
    (MeromorphicOn.id).sub <| const z
  have hmeroAt (u : ℂ) : MeromorphicAt (fun x ↦ x - z) u := hmeroOn (Eq u) u rfl
  have hmeroBall : MeromorphicOn (fun x ↦ x - z) (closedBall 0 |1|) :=
    hmeroOn (closedBall 0 |1|)
  have : MeromorphicOn (fun x ↦ (X - C z).eval x) (closedBall 0 |1|) :=
    (analyticOnNhd_id.aeval_polynomial (X - C z)).meromorphicOn
  rw [logMahlerMeasure_def, circleAverage_log_norm zero_ne_one.symm this]
  --get rid of the `meromorphicTrailingCoeffAt`
  have : meromorphicTrailingCoeffAt (fun x ↦ (X - C z).eval x) 0 = -z := by
    rw [(AnalyticAt.aeval_polynomial analyticAt_id (X - C z)).meromorphicTrailingCoeffAt_of_ne_zero
      (by simp [hz₀])]
    simp
  rw [this]
  simp only [eval_sub, eval_X, eval_C, zero_sub, norm_neg, one_mul, log_inv, mul_neg, log_one,
    mul_zero, add_zero]
  -- divisor computations
  let B := closedBall (0 : ℂ) |1|
  have hdiv0 {u : ℂ} (hu : u ≠ z) : divisor (fun x ↦ x - z) B u = 0 := by
    by_cases hu' : u ∈ B
    · rw [divisor_apply (hmeroOn B) hu', ← WithTop.untop₀_coe 0]
      congr
      rw [meromorphicOrderAt_eq_int_iff (hmeroAt u)]
      use fun x ↦ x - z
      simp only [zpow_zero, smul_eq_mul, one_mul, Filter.eventually_true, and_true]
      exact ⟨analyticAt_id.fun_sub analyticAt_const, sub_ne_zero_of_ne hu⟩
    · simp_all
  have hzdiv1 (h : z ∈ B) : (divisor (fun x ↦ x - z) B) z = 1 := by
      simp_all only [eval_sub, eval_X, eval_C, divisor_apply]
      rw [← WithTop.untop₀_coe 1]
      congr
      rw [meromorphicOrderAt_eq_int_iff (hmeroAt z)]
      simp only [ne_eq, zpow_one, smul_eq_mul]
      use fun x ↦ 1
      simpa using analyticAt_const
  --separate cases depending on whether z in in the open ball 0 |1| or not
  by_cases hzBall : z ∈ ball 0 |1|;
  · have : ‖z‖ < 1 := by rwa [mem_ball, dist_zero_right, abs_one] at hzBall
    have : ‖z‖ ≤ 1 := le_of_lt this
    have hzcb : z ∈ B := Set.mem_of_mem_of_subset hzBall ball_subset_closedBall
    rw [← finsum_mem_support]
    have : (fun u ↦ -((divisor (fun x ↦ x - z) (closedBall 0 |1|) u) * log ‖u‖)).support = {z} := by
      rw [Function.support_eq_iff]
      constructor
      · simp only [ne_eq, neg_eq_zero, mul_eq_zero, Int.cast_eq_zero, log_eq_zero, norm_eq_zero]
        grind [norm_nonneg, ne_of_lt]
      · intro _ hu
        rw [Set.mem_singleton_iff] at hu
        rw [hdiv0 hu]
        simp
    simp only [this, Set.mem_singleton_iff, finsum_cond_eq_left]
    rw [hzdiv1 hzcb]
    grind [log_nonpos , norm_nonneg, posLog_def]
  · have h1lez : 1 ≤ ‖z‖ := by grind [mem_ball, dist_zero_right, abs_one]
    rw [← finsum_mem_support]
    have : (fun u ↦ -((divisor (fun x ↦ x - z) (closedBall 0 |1|) u) * log ‖u‖)).support = ∅ := by
      rw [Function.support_eq_empty_iff]
      ext x
      simp only [Pi.zero_apply, neg_eq_zero, mul_eq_zero, Int.cast_eq_zero, log_eq_zero,
        norm_eq_zero]
      rw [or_iff_not_imp_right]
      simp only [not_or, and_imp]
      intro _ h _
      by_cases hx : x = z
      · rw [hx] at h ⊢
        apply Function.locallyFinsuppWithin.apply_eq_zero_of_notMem
          (divisor (fun x ↦ x - z) (closedBall 0 |1|))
        grind [abs_one, mem_closedBall, dist_zero_right]
      · exact hdiv0 hx
    simp [this, posLog_eq_log_max_one <| norm_nonneg z, h1lez]

@[simp]
theorem logMahlerMeasure_X_add_C0 (z : ℂ) : (X + C z).logMahlerMeasure = log⁺ ‖z‖ := by
  simp [← sub_neg_eq_add, ← map_neg]

theorem logMahlerMeasure_C_mul_X_add_C0 {a : ℂ} (b : ℂ) (ha : a ≠ 0) :
    (C a * X + C b).logMahlerMeasure = log ‖a‖ + log⁺ ‖a⁻¹ * b‖ := by
  rw [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    logMahlerMeasure_C_mul ha (X_add_C_ne_zero (a⁻¹ * b)), logMahlerMeasure_X_add_C]

theorem logMahlerMeasure_degree_eq_one {p : ℂ[X]} (h : p.degree = 1) : p.logMahlerMeasure =
    log ‖p.coeff 1‖ + log⁺ ‖(p.coeff 1)⁻¹ * p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [logMahlerMeasure_C_mul_X_add_C0 _ (show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h)]

/-- The Mahler measure of `X - C z` equals `max 1 ‖z‖`. -/
@[simp]
theorem mahlerMeasure_X_sub_C0 (z : ℂ) : (X - C z).mahlerMeasure = max 1 ‖z‖ := by
  have := logMahlerMeasure_X_sub_C z
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rwa [posLog_eq_log_max_one (norm_nonneg z),
    exp_log (mahlerMeasure_pos_of_ne_zero <| X_sub_C_ne_zero z),
    exp_log (lt_of_lt_of_le zero_lt_one <| le_max_left 1 ‖z‖)] at this

@[simp]
theorem mahlerMeasure_X_add_C0 (z : ℂ) : (X + C z).mahlerMeasure = max 1 ‖z‖ := by
  simp [← sub_neg_eq_add, ← map_neg]

theorem mahlerMeasure_C_mul_X_add_C {a : ℂ} (b : ℂ) (ha : a ≠ 0) :
    (C a * X + C b).mahlerMeasure = ‖a‖ * max 1 ‖a⁻¹ * b‖ := by
  simp [show C a * X + C b = C a * (X + C (a⁻¹ * b)) by simp [mul_add, ← map_mul, ha],
    mahlerMeasure_mul, -map_mul]

theorem mahlerMeasure_degree_eq_one {p : ℂ[X]} (h : p.degree = 1) : p.mahlerMeasure =
    ‖p.coeff 1‖ * max 1 ‖(p.coeff 1)⁻¹ * p.coeff 0‖ := by
  rw [eq_X_add_C_of_degree_le_one (le_of_eq h)]
  simp [mahlerMeasure_C_mul_X_add_C _ (show p.coeff 1 ≠ 0 by exact coeff_ne_zero_of_eq_degree h)]

--put somewhere
open Multiset in
lemma log_prod_eq_sum_log {s : Multiset ℝ} (h : ∀ x ∈ s, x ≠ 0) : log s.prod = (s.map (fun x ↦ log x)).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp_all only [ne_eq, mem_cons, or_true, not_false_eq_true, implies_true, forall_const,
      forall_eq_or_imp, prod_cons, map_cons, sum_cons]
    have : s.prod ≠ 0 := by
      apply prod_ne_zero
      grind
    rw [log_mul h.1 this, add_right_inj, ih]

/-- The logarithmic Mahler measure of `p` is the `log` of the absolute value of its leading
  coefficient plus the sum of the `log`s of the absolute values of its roots lying outside the unit
  disk. -/
theorem logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖ + ((p.roots).map (fun a ↦ log⁺ ‖a‖)).sum := by
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ x ∈ Multiset.map (fun x ↦ max 1 ‖x‖) p.roots, x ≠ 0 := by grind [Multiset.mem_map]
  nth_rw 1 [eq_prod_roots_of_splits_id (IsAlgClosed.splits p)]
  rw [logMahlerMeasure_mul_eq_add_logMahelerMeasure (by simp [hp, X_sub_C_ne_zero])]
  simp [posLog_eq_log_max_one,logMahlerMeasure_eq_log_MahlerMeasure,
    prod_mahlerMeasure_eq_mahlerMeasure_prod, log_prod_eq_sum_log this]

/-- The Mahler measure of `p` is the the absolute value of its leading coefficient times the product
  absolute values of its roots lying outside the unit disk. -/
theorem mahlerMeasure_eq_leadingCoeff_mul_prod_roots (p : ℂ[X]) : p.mahlerMeasure =
    ‖p.leadingCoeff‖ * ((p.roots).map (fun a ↦ max 1 ‖a‖)).prod := by
  by_cases hp : p = 0; simp [hp]
  have := logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots p
  rw [logMahlerMeasure_eq_log_MahlerMeasure] at this
  apply_fun exp at this
  rw [exp_add, exp_log <| mahlerMeasure_pos_of_ne_zero0 hp,
    exp_log <|norm_pos_iff.mpr <| leadingCoeff_ne_zero.mpr hp] at this
  simp [this, exp_multiset_sum, posLog_eq_log_max_one, exp_log]
 -/
----------


/- theorem logMahlerMeasure_eq_nnnorm (p : ℂ[X]) : p.logMahlerMeasure =
    log ‖p.leadingCoeff‖₊ + ((p.roots).map (fun a ↦ log⁺ ‖a‖₊)).sum := by
  simp [logMahlerMeasure_eq_log_leadingCoeff_add_sum_log_roots] -/

--try to get rid of this, used in norm_coeff_le_binom_mahlerMeasure
/- theorem mahlerMeasure_eq_nnnorm (p : ℂ[X]) : p.mahlerMeasure =
    ‖p.leadingCoeff‖₊ * ((p.roots).map (fun a ↦ max 1 ‖a‖₊)).prod := by
  by_cases hp : p = 0; simp [hp]
  push_cast
  simp [mahlerMeasure_eq_leadingCoeff_mul_prod_roots] -/
/-
lemma one_le_prod_max_one_norm_roots (p : ℂ[X]) : 1 ≤ (p.roots.map (fun a ↦ max 1 ‖a‖)).prod := by
  grind [Multiset.one_le_prod, Multiset.mem_map]

lemma leading_coeff_le_mahlerMeasure (p : ℂ[X]) : ‖p.leadingCoeff‖ ≤ p.mahlerMeasure := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  exact le_mul_of_one_le_right (norm_nonneg p.leadingCoeff) (one_le_prod_max_one_norm_roots p)

lemma prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff {p : ℂ[X]}
    (hlc : 1 ≤ ‖p.leadingCoeff‖) : (p.roots.map (fun a ↦ max 1 ‖a‖)).prod ≤ p.mahlerMeasure := by
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  exact le_mul_of_one_le_left (le_trans zero_le_one (one_le_prod_max_one_norm_roots p)) hlc
 -/
/-
theorem roots_le_mahlerMeasure_of_one_le_leading_coeff {p : ℂ[X]} (hlc : 1 ≤ ‖p.leadingCoeff‖) :
    (p.roots.map (fun x ↦ ‖x‖₊)).sup ≤ p.mahlerMeasure := by
  apply le_trans _ <| prod_max_one_norm_roots_le_mahlerMeasure_of_one_le_leadingCoeff hlc
  have : (Multiset.map (fun a ↦ 1 ⊔ ‖a‖) p.roots).prod = (Multiset.map (fun a ↦ 1 ⊔ ‖a‖₊) p.roots).prod := by
    norm_cast
    simp
  rw [this]
  simp only [NNReal.coe_le_coe, Multiset.sup_le, Multiset.mem_map,
    forall_exists_index, and_imp]
  intro b x hx hxb
  rw [← hxb]
  apply le_trans <| le_max_right 1 _
  refine Multiset.single_le_prod ?_ (1 ⊔ ‖x‖₊) (Multiset.mem_map_of_mem (fun a ↦ 1 ⊔ ‖a‖₊) hx)
  simp only [Multiset.mem_map]
  rintro _ ⟨_, _, rfl⟩
  simp -/
/-
lemma a (p q : ℝ → Prop) : {a | p a ∧ q a} = {a | p a} ∩ {a | q a} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_inter_iff] -/

open Filter MeasureTheory Set in
/-- The Mahler measure of a polynomial is bounded above by the sum of the norms of its coefficients.
-/
lemma mahlerMeasure_le_sum_norm_coeff' (p : ℂ[X]) : p.mahlerMeasure ≤ p.sum fun _ a ↦ ‖a‖ := by
  by_cases hp : p = 0; simp [hp]
  simp only [mahlerMeasure, ne_eq, hp, logMahlerMeasure]
  have : 0 < p.sum fun x a ↦ ‖a‖ := by
    apply Finset.sum_pos' (fun i _ ↦ norm_nonneg (p.coeff i))
    use p.natDegree
    simp [hp]
  have : (p.sum fun _ a ↦ ‖a‖) = rexp (circleAverage (fun _ ↦ log (p.sum fun _ a ↦ ‖a‖)) 0 1) := by
    simp [circleAverage_def, mul_assoc, exp_log this]
  rw [this]
  simp only [not_false_eq_true, reduceIte, circleAverage_def]
  gcongr
  apply intervalIntegral.integral_mono_ae_restrict (le_of_lt two_pi_pos)
    p.intervalIntegrable_mahlerMeasure (by simp)
  simp only [EventuallyLE, eventually_iff_exists_mem]
  use {x : ℝ | eval (circleMap 0 1 x) p ≠ 0}
  constructor
  · rw [mem_ae_iff]
    simp only [compl, mem_setOf_eq, Decidable.not_not, measurableSet_Icc,
      Measure.restrict_apply', Inter.inter, Set.inter]
    apply Finite.measure_zero <| Finite.of_diff _ <| finite_singleton (2 * π)
    have : {a | eval (circleMap 0 1 a) p = 0 ∧ a ∈ Icc 0 (2 * π)} \ {2 * π}
        = {a | a ∈ Ico 0 (2 * π) ∧ eval (circleMap 0 1 a) p = 0} := by
      ext
      grind
    rw [this]
    apply Finite.of_finite_image (f := circleMap 0 1)
    · apply (Multiset.finite_toSet (p.roots)).subset
      simp [hp]
    · exact fun _ h _ k l ↦ injOn_circleMap_of_abs_sub_le' (one_ne_zero) (by linarith) h.1 k.1 l
  · intro x hx
    gcongr
    simp only [eval, eval₂, RingHom.id_apply]
    apply norm_sum_le_of_le p.support
    simp


open Filter MeasureTheory Set in
/-- The Mahler measure of a polynomial is bounded above by the sum of the norms of its coefficients.
-/
lemma mahlerMeasure_le_sum_norm_coeff'' (p : ℂ[X]) : p.mahlerMeasure ≤
    ∑ i : Fin (p.natDegree + 1), ‖p.coeff i‖ := by
  by_cases hp : p = 0; simp [hp]
  simp only [mahlerMeasure, ne_eq, hp, logMahlerMeasure]
  have : (circleAverage (fun x ↦ log ‖eval x p‖) 0 1) ≤
      (circleAverage (fun x ↦ log (∑ i : Fin (p.natDegree + 1), ‖p.coeff i‖)) 0 1):= by
    simp only [circleAverage_def, mul_inv_rev, smul_eq_mul]
    gcongr
    apply intervalIntegral.integral_mono_ae_restrict (le_of_lt two_pi_pos)
      (intervalIntegrable_mahlerMeasure p) (by simp)
    simp only [EventuallyLE, eventually_iff_exists_mem]
    use {x : ℝ | x ∈ Icc 0 (2 * π) ∧ eval (circleMap 0 1 x) p ≠ 0}
    constructor
    · rw [mem_ae_iff]
      have : {a | (a ∈ Icc 0 (2 * π) → eval (circleMap 0 1 a) p = 0) ∧ a ∈ Icc 0 (2 * π)}
          = {a | a ∈ Icc 0 (2 * π) ∧ eval (circleMap 0 1 a) p = 0} := by aesop
      simp only [compl, mem_setOf_eq, not_and, Decidable.not_not, measurableSet_Icc,
        Measure.restrict_apply', Inter.inter, Set.inter, this]
      apply Finite.measure_zero _
      have : {a | a ∈ Icc 0 (2 * π) ∧ eval (circleMap 0 1 a) p = 0} \ {2 * π} =
          {a | a ∈ Ico 0 (2 * π) ∧ eval (circleMap 0 1 a) p = 0} := by
        ext
        grind
      apply Finite.of_diff _ <| finite_singleton (2 * π)
      rw [this]
      apply Finite.of_finite_image (f := circleMap 0 1)
      · apply (Multiset.finite_toSet (p.roots)).subset
        simp [hp]
      · exact fun _ h _ k l ↦ injOn_circleMap_of_abs_sub_le' (one_ne_zero) (by linarith) h.1 k.1 l
    · intro x hx
      gcongr
      · simp_all
      simp only [eval, eval₂, RingHom.id_apply]
      calc
      ‖p.sum fun e a ↦ a * circleMap 0 1 x ^ e‖ ≤
          p.sum (fun i a ↦ ‖a * (circleMap 0 1 x) ^ i‖) := by
        apply norm_sum_le_of_le p.support
        simp
      _ = ∑ i : Fin (p.natDegree + 1), ‖p.coeff ↑i‖ := by
        simp only [norm_mul, norm_pow, norm_circleMap_zero, abs_one, one_pow, mul_one]
        rw [sum_eq_of_subset _ (by simp) supp_subset_range_natDegree_succ]
        exact Finset.sum_range fun i ↦ ‖p.coeff i‖
  have : 0 < ∑ i : Fin (p.natDegree + 1), ‖p.coeff i‖ := by
    apply Finset.sum_pos' (fun (i : Fin (p.natDegree + 1)) _ ↦ norm_nonneg (p.coeff i))
    use ⟨p.natDegree, lt_add_one p.natDegree⟩
    simp [hp]
  calc
  rexp (circleAverage (fun x ↦ log ‖eval x p‖) 0 1) ≤
      rexp (circleAverage (fun x ↦ log (∑ i : Fin (p.natDegree + 1), ‖p.coeff i‖)) 0 1) := by
    gcongr
  _ ≤ ∑ i : Fin (p.natDegree + 1), ‖p.coeff i‖ := by
    simp [circleAverage_def, mul_assoc, exp_log this]

open Multiset in
theorem norm_coeff_le_binom_mahlerMeasure (n : ℕ) (p : ℂ[X]) :
    ‖p.coeff n‖ ≤ (p.natDegree).choose (p.natDegree - n) * p.mahlerMeasure := by
  by_cases hp : p = 0; simp [hp]
  by_cases hn: p.natDegree < n
  · simp [coeff_eq_zero_of_natDegree_lt hn, le_of_lt hn, mahlerMeasure_nonneg]
  rw [not_lt] at hn
  rw [mahlerMeasure_eq_leadingCoeff_mul_prod_roots,
    coeff_eq_esymm_roots_of_card (splits_iff_card_roots.mp (IsAlgClosed.splits p)) hn, mul_assoc]
  simp only [norm_mul, norm_pow, norm_neg, one_mem, CStarRing.norm_of_mem_unitary, one_pow, one_mul]
  conv => enter [2]; rw [← mul_assoc, mul_comm _ ‖p.leadingCoeff‖, mul_assoc]
  rw [mul_le_mul_iff_right₀ (by simp [leadingCoeff_ne_zero.mpr hp]), esymm,
    Finset.sum_multiset_map_count]
  apply le_trans <| norm_sum_le _ _
  simp only [nsmul_eq_mul, norm_mul, _root_.norm_natCast]
  let S := (powersetCard (p.natDegree - n) p.roots)
  calc
  ∑ x ∈ S.toFinset, (count x S) * ‖x.prod‖
     ≤ ∑ x ∈ S.toFinset, (count x S) * ((p.roots).map (fun a ↦ max 1 ‖a‖)).prod := by
    gcongr with x hx
    simp only [mem_toFinset, mem_powersetCard, S] at hx
    rw [Finset.prod_multiset_map_count, Finset.prod_multiset_count, norm_prod]
    simp only [norm_pow]
    calc
    ∏ x_1 ∈ x.toFinset, ‖x_1‖ ^ count x_1 x
      ≤ ∏ x_1 ∈ x.toFinset, (1 ⊔ ‖x_1‖) ^ count x_1 x := by
      gcongr with a
      exact le_max_right 1 ‖a‖
    _ ≤ ∏ m ∈ p.roots.toFinset, (1 ⊔ ‖m‖) ^ count m x := by
      simp only [← coe_nnnorm]
      norm_cast
      apply Finset.prod_le_prod_of_subset_of_one_le' (toFinset_subset.mpr (subset_of_le hx.1))
      exact fun a _ _ ↦ one_le_pow₀ (le_max_left 1 ‖a‖)
    _ ≤ ∏ m ∈ p.roots.toFinset, (1 ⊔ ‖m‖) ^ count m p.roots := by
      gcongr with a
      · exact le_max_left 1 ‖a‖
      · exact hx.1
  _  = ↑(p.natDegree.choose (p.natDegree - n)) * (Multiset.map (fun a ↦ 1 ⊔ ‖a‖) p.roots).prod := by
    rw [← Finset.sum_mul]
    congr
    norm_cast
    simp only [mem_powersetCard, mem_toFinset, imp_self, implies_true, sum_count_eq_card,
      card_powersetCard, S]
    congr
    exact splits_iff_card_roots.mp (IsAlgClosed.splits p)




end Polynomial
