/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.RingTheory.PowerSeries.Order
/-!
# Gauss norm for power series
This file defines the Gauss norm for power series. Given a power series `f` in `R⟦X⟧`, a function
`v : R → ℝ` and a real number `c`, the Gauss norm is defined as the supremum of the set of all
values of `v (f.coeff R i) * c ^ i` for all `i : ℕ`.


## Main Definitions and Results
* `PowerSeries.gaussNormC` is the supremum of the set of all values of `v (f.coeff R i) * c ^ i`
  for all `i : ℕ`, where `f` is a power series in `R⟦X⟧`, `v : R → ℝ` is a function and `c` is a
  real number.
* `PowerSeries.gaussNormC_nonneg`: if `v` is a non-negative function, then the Gauss norm is
  non-negative.
* `PowerSeries.gaussNormC_eq_zero_iff`: if `v x = 0 ↔ x = 0` for all `x : R`, then the Gauss
  norm is zero if and only if the power series is zero.
-/

namespace PowerSeries

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ) (f : R⟦X⟧)

noncomputable def gaussNormC : ℝ := sSup {v (f.coeff R i) * c ^ i | (i : ℕ)}

@[simp]
theorem gaussNormC_zero [ZeroHomClass F R ℝ] : gaussNormC v c 0 = 0 := by simp [gaussNormC]

private lemma gaussNormC_nonempty : {x | ∃ i, v (f.coeff R i) * c ^ i = x}.Nonempty := by
  use v (f.coeff R 0) * c ^ 0, 0

lemma le_gaussNormC [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    (hbd : BddAbove {x | ∃ i, v (f.coeff R i) * c ^ i = x}) (i : ℕ) :
  v (f.coeff R i) * c ^ i ≤ f.gaussNormC v c := by
  apply le_csSup hbd
  simp

theorem gaussNormC_nonneg [NonnegHomClass F R ℝ] : 0 ≤ f.gaussNormC v c := by
  rw [gaussNormC]
  by_cases h : ¬ BddAbove {x | ∃ i, v (f.coeff R i) * c ^ i = x}; simp [h]
  rw [not_not] at h
  rw [Real.le_sSup_iff h <| gaussNormC_nonempty v c f]
  simp only [Set.mem_setOf_eq, zero_add, exists_exists_eq_and]
  intro ε hε
  use 0
  simpa using lt_of_lt_of_le hε <| apply_nonneg v (f.constantCoeff R)

@[simp]
theorem gaussNormC_eq_zero_iff [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] {v : F}
    (h_eq_zero : ∀ x : R, v x = 0 → x = 0) {f : R⟦X⟧} {c : ℝ} (hc : 0 < c)
    (hbd : BddAbove {x | ∃ i, v (f.coeff R i) * c ^ i = x})  :
    f.gaussNormC v c = 0 ↔ f = 0 := by
  refine ⟨?_, fun hf ↦ by simp [hf]⟩
  contrapose!
  intro hf
  apply ne_of_gt
  obtain ⟨n, hn⟩ := exists_coeff_ne_zero_iff_ne_zero.mpr hf
  calc
  0 < v (f.coeff R n) * c ^ n := by
    apply mul_pos _ (pow_pos hc _)
    specialize h_eq_zero (f.coeff R n)
    simp_all only [ne_eq, iff_false]
    positivity
  _ ≤ sSup {x | ∃ i, v (f.coeff R i) * c ^ i = x} := by
    rw [Real.le_sSup_iff hbd <| gaussNormC_nonempty v c f]
    simp only [Set.mem_setOf_eq, exists_exists_eq_and]
    intro ε hε
    use n
    simp [hε]

end PowerSeries

--#min_imports



/-
--This is false
theorem isNonarchimedean_gaussNormC [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]
    (hna : IsNonarchimedean v)
    (f : R⟦X⟧ ) {c : ℝ} (hc : 0 ≤ c) :
    IsNonarchimedean (gaussNormC v c) := by
  intro f g
  rw [gaussNormC]
  apply Real.sSup_le _ (by simp)
  intro x hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi, map_add]
  calc
  v ((coeff R i) f + (coeff R i) g) * c ^ i ≤
    max (v ((coeff R i) f)) (v ((coeff R i) g)) * c ^ i := by
    gcongr
    exact hna ((coeff R i) f) ((coeff R i) g)
  _ = max (v ((coeff R i) f) * c ^ i) (v ((coeff R i) g) * c ^ i) :=
    max_mul_of_nonneg _ _ (pow_nonneg hc _)
  _ ≤ max (gaussNormC v c f) (gaussNormC v c g) := by
    gcongr
    sorry
    sorry



end PowerSeries -/
