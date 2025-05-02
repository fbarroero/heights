import Mathlib

namespace PowerSeries

variable {R : Type*} [Semiring R] --[Semiring α] [LinearOrder α]
 (v : AbsoluteValue R ℝ) (hna : IsNonarchimedean v) (c : ℝ)

noncomputable def gaussNormC (f : PowerSeries R) : ℝ := sSup {v (f.coeff R i) * c ^ i | (i : ℕ)}

@[simp]
theorem gaussNormC_zero : gaussNormC v c 0 = 0 := by simp [gaussNormC]

end PowerSeries

namespace Polynomial

variable {R : Type*} [Semiring R] (v : AbsoluteValue R ℝ) (hna : IsNonarchimedean v) (c : ℝ)

def gaussNormC (p : R[X]) : ℝ := if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (v (p.coeff i) * c ^ i) else 0

@[simp]
theorem gaussNorm_zero : gaussNormC v c 0 = 0 := by simp [gaussNormC]

theorem eq (p : R[X]) : p.gaussNormC v c = (p.toPowerSeries).gaussNormC v c  := by
  by_cases hp : p = 0; simp [hp]
  have h_supp : p.support.Nonempty := support_nonempty.mpr hp
  have h : (p.toPowerSeries).gaussNormC v c ≤ p.gaussNormC v c := by
    apply Real.sSup_le
    intro x hx
    obtain ⟨i, hi⟩ := hx
    simp only [← hi, coeff_coe, gaussNormC, support_nonempty, ne_eq, hp, not_false_eq_true,
      ↓reduceDIte]
    by_cases h : i ∈ p.support
    · exact Finset.le_sup' (fun j ↦ v (p.coeff j) * c ^ j) h
    · simp [h, -Finset.le_sup'_iff, not_mem_support_iff.mp h]
      --same as below
      sorry
    simp [gaussNormC]
    simp [h_supp, -Finset.le_sup'_iff]
    --lemma in other file
    sorry
  simp only [gaussNormC, support_nonempty, ne_eq, hp, not_false_eq_true, ↓reduceDIte,
    AbsoluteValue.map_mul, PowerSeries.gaussNormC, coeff_coe]
  apply le_antisymm
  · rw [Real.le_sSup_iff]
    · sorry
    · use p.gaussNormC v c
      rw [@mem_upperBounds]
      --simp [PowerSeries.GaussNormC] at h
      intro x hx
      --apply le_trans _ h
      obtain ⟨i, hi⟩ := hx
      rw [← hi]
      --should be able to finish




/-
      simp [GaussNormC, h_supp]
      rw [mem_upperBounds]
      intro x hx
      obtain ⟨i, hi⟩ := hx
      rw [← hi] -/
      sorry
    · use v (p.coeff 0) * c ^ 0, 0
  · simp_all [PowerSeries.gaussNormC, gaussNormC, h_supp, -Finset.le_sup'_iff]

end Polynomial

section Coram

variable (c : ℝ) (R : Type*) [NormedRing R] [IsUltrametricDist R]

noncomputable def gaussNormC' : PowerSeries R → ℝ :=
  fun f => sSup {‖f.coeff R i‖ * c ^ i | (i : ℕ)}

theorem gaussNormC'_zero : gaussNormC' c R 0 = 0 := by simp [gaussNormC']

theorem gaussNormC'_eq (f : PowerSeries R) : gaussNormC' c R f = f.gaussNormC v c := by

  sorry

end Coram
