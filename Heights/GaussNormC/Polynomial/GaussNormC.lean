/-
Copyright (c) 2025 Fabrizio Barroero. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Barroero
-/
import Heights.GaussNormC.PowerSeries.GaussNormC

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)

namespace Polynomial

/-- -/
def gaussNormC (p : R[X]) : ℝ := if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (v (p.coeff i) * c ^ i) else 0

@[simp]
lemma gaussNormC_zero : gaussNormC v c 0 = 0 := by simp [gaussNormC]

private lemma sup'_nonneg_of_ne_zero {p : R[X]} (h : p.support.Nonempty) (hc : 0 ≤ c)
    [NonnegHomClass F R ℝ]: 0 ≤ p.support.sup' h fun i ↦ (v (p.coeff i) * c ^ i) := by
  simp only [Finset.le_sup'_iff, mem_support_iff]
  use p.natDegree
  simp_all only [support_nonempty, ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true,
    true_and]
  positivity

@[simp]
theorem gaussNormC_nonneg (p : R[X]) {c : ℝ} (hc : 0 ≤ c) [NonnegHomClass F R ℝ] :
    0 ≤ p.gaussNormC v c := by
  by_cases hp : p.support.Nonempty
  · simp_all [gaussNormC, sup'_nonneg_of_ne_zero, -Finset.le_sup'_iff]
  · simp [gaussNormC, hp]

@[simp]
lemma gaussNormC_C [ZeroHomClass F R ℝ] (r : R) : (C r).gaussNormC v c = v r := by
  by_cases hr : r = (0 : R); simp [gaussNormC, hr]
  simp [gaussNormC, support_C, hr]

lemma le_gaussNormC [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ] (p : R[X]) (i : ℕ) {c : ℝ}
    (hc : 0 ≤ c) : v (p.coeff i) * c ^ i ≤ p.gaussNormC v c := by
  by_cases hp : p = 0; simp [hp]
  by_cases hi : ¬ i ∈ p.support; simp_all
  simp only [mem_support_iff, not_not] at hi
  simp only [gaussNormC, support_nonempty, ne_eq, hp, not_false_eq_true, ↓reduceDIte,
    Finset.le_sup'_iff, mem_support_iff]
  use i

private lemma aux_bdd [ZeroHomClass F R ℝ] (p : R[X]) :
    BddAbove {x | ∃ i, v (p.coeff i) * c ^ i = x} := by
  apply Set.Finite.bddAbove
  let f : p.support → ℝ := fun i ↦ v (p.coeff i) * c ^ i.1
  let t := f '' ⊤ ∪ {0}
  have h_fin : t.Finite := by
    apply Set.Finite.union _ <| Set.finite_singleton 0
    apply Set.Finite.image f
    rw [Set.top_eq_univ, Set.finite_univ_iff, ← @Finset.coe_sort_coe]
    exact Finite.of_fintype p.support
  apply Set.Finite.subset h_fin
  intro x hx
  obtain ⟨i, hi⟩ := hx
  rw [← hi]
  by_cases hi : i ∈ p.support
  · left
    use ⟨i, hi⟩
    simp [f]
  · right
    simp [not_mem_support_iff.mp hi]

lemma gaussNormC_nonempty (p : R[X]) : {x | ∃ i, v (p.coeff i) * c ^ i = x}.Nonempty := by
  use v (p.coeff 0) * c ^ 0, 0

theorem gaussNormC_coe_powerSeries [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ ] (p : R[X])
    {c : ℝ} (hc : 0 ≤ c) :
    p.gaussNormC v c = (p.toPowerSeries).gaussNormC v c := by
  by_cases hp : p = 0; simp [hp]
  have h_supp : p.support.Nonempty := support_nonempty.mpr hp
  simp only [gaussNormC, support_nonempty, ne_eq, hp, not_false_eq_true, ↓reduceDIte,
    PowerSeries.gaussNormC, coeff_coe]
  apply le_antisymm
  · rw [Real.le_sSup_iff (aux_bdd v c p) (gaussNormC_nonempty v c p)]
    sorry
  · apply Real.sSup_le
    intro x hx
    obtain ⟨i, hi⟩ := hx
    rw [← hi]

    --simp [sSup, -Finset.le_sup'_iff, mem_support_iff, ne_eq, aux_bdd v c p]
    /-


    apply Real.sSup_le
    intro x hx
    obtain ⟨i, hi⟩ := hx -/
    sorry
    sorry


@[simp]
theorem gaussNormC_monomial [ZeroHomClass F R ℝ] (n : ℕ) (r : R) :
    (monomial n r).gaussNormC v c = v r * c ^ n := by
  by_cases hr : r = 0; simp [gaussNormC, hr]
  simp [gaussNormC, support_monomial, hr]

@[simp]
theorem gaussNormC_eq_zero_iff [ZeroHomClass F R ℝ] [NonnegHomClass F R ℝ]  (h_eq_zero : ∀ x : R, v x = 0 ↔ x = 0)
    (p : R[X]) {c : ℝ} (hc : 0 < c) : p.gaussNormC v c = 0 ↔ p = 0 := by
  rw [gaussNormC_coe_powerSeries _ _ (le_of_lt hc), PowerSeries.gaussNormC_eq_zero_iff h_eq_zero hc, coe_eq_zero_iff]
  simp only [coeff_coe]
  exact aux_bdd v c p
/-
  simp only [gaussNormC, support_nonempty, dite_eq_right_iff]
  refine ⟨?_, fun _ _ ↦ by simp_all⟩
  contrapose!
  intro hp
  simp_all only [ne_eq, not_false_eq_true, exists_true_left]
  apply ne_of_gt
  calc
  0 < v (p.coeff p.natDegree) * c ^ p.natDegree := by
    apply mul_pos _ (pow_pos hc _)
    specialize h_eq_zero (p.coeff p.natDegree)
    simp_all only [coeff_natDegree, leadingCoeff_eq_zero, iff_false]
    positivity
  _ ≤ p.support.sup' (support_nonempty.mpr hp) fun i ↦ v (p.coeff i) * c ^ i :=
    Finset.le_sup' (fun i ↦ v (p.coeff i) * c ^ i) (natDegree_mem_support_of_nonzero hp) -/

theorem isNonarchimedean_gaussNormC [NonnegHomClass F R ℝ]
    (hna : IsNonarchimedean v)
    (p : R[X]) {c : ℝ} (hc : 0 ≤ c) :
    IsNonarchimedean (gaussNormC v c) := by
  intro p q
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  by_cases hpq : p + q = 0; simp [hpq, hc]
  simp only [gaussNormC, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte, coeff_add,
    hp, hq, Finset.sup'_le_iff, mem_support_iff]
  intro i hi
  calc
  v (p.coeff i + q.coeff i) * c ^ i ≤ max (v (p.coeff i)) (v (q.coeff i)) * c ^ i := by
    gcongr
    exact hna (p.coeff i) (q.coeff i)
  _ = max (v (p.coeff i) * c ^ i) (v (q.coeff i) * c ^ i) := by
    rw [max_mul_of_nonneg _ _ (pow_nonneg hc _)]
  _ ≤ max (p.support.sup' (support_nonempty.mpr hp) fun i ↦ v (p.coeff i) * c ^ i)
      (q.support.sup' (support_nonempty.mpr hq) fun i ↦ v (q.coeff i) * c ^ i) := by
    apply max_le_max <;>
    sorry


section AbsoluteValue

variable (v : AbsoluteValue R ℝ)



end AbsoluteValue

end Polynomial
