/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Mathlib

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)

namespace PowerSeries

noncomputable def gaussNormC (f : R⟦X⟧) : ℝ := sSup {v (f.coeff R i) * c ^ i | (i : ℕ)}

@[simp]
theorem gaussNormC_zero [ZeroHomClass F R ℝ] : gaussNormC v c 0 = 0 := by simp [gaussNormC]

lemma gaussNormC_nonempty (f : R⟦X⟧) : {x | ∃ i, v ((coeff R i) f) * c ^ i = x}.Nonempty := by
  use v (f.coeff R 0) * c ^ 0, 0

@[simp]
theorem gaussNormC_nonneg (f : R⟦X⟧) [NonnegHomClass F R ℝ] : 0 ≤ f.gaussNormC v c := by
  simp [gaussNormC]
  by_cases h : ¬ BddAbove {x | ∃ i, v (f.coeff R i) * c ^ i = x}; simp [h]
  rw [not_not] at h
  rw [Real.le_sSup_iff h <| gaussNormC_nonempty v c f]
  simp only [Set.mem_setOf_eq, zero_add, exists_exists_eq_and]
  intro ε hε
  use 0
  simp [lt_of_lt_of_le hε <| apply_nonneg v (f.constantCoeff R)]

@[simp]
theorem gaussNormC_eq_zero_iff [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] {v : F}
    (h_eq_zero : ∀ x : R, v x = 0 ↔ x = 0) {f : R⟦X⟧} {c : ℝ} (hc : 0 < c)
    (hbd : BddAbove {x | ∃ i, v (f.coeff R i) * c ^ i = x})  :
    f.gaussNormC v c = 0 ↔ f = 0 := by
  refine ⟨?_, fun hf ↦ by simp [hf]⟩
  contrapose!
  intro hf
  simp only [gaussNormC]
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
