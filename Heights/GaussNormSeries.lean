import Mathlib

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)
namespace PowerSeries

noncomputable def gaussNormC (f : PowerSeries R) : ℝ := sSup {v (f.coeff R i) * c ^ i | (i : ℕ)}

--#find_home! gaussNormC
--gives [Mathlib.NumberTheory.ZetaValues, Mathlib.NumberTheory.ModularForms.QExpansion]
@[simp]
theorem gaussNormC_zero [ZeroHomClass F R ℝ] : gaussNormC v c 0 = 0 := by simp [gaussNormC]

end PowerSeries

namespace Polynomial

def gaussNormC (p : R[X]) : ℝ := if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (v (p.coeff i) * c ^ i) else 0

@[simp]
theorem gaussNormC_zero : gaussNormC v c 0 = 0 := by simp [gaussNormC]

@[simp]
lemma gaussNormC_C [ZeroHomClass F R ℝ] (r : R) : gaussNormC v c (C r) = v r := by
  by_cases hr : r = (0 : R); simp [gaussNormC, hr]
  simp [gaussNormC, support_C, hr]

  --simp [gaussNormC, support_C]

@[simp]
theorem eq [ZeroHomClass F R ℝ] (p : R[X]) : (p.toPowerSeries).gaussNormC v c = p.gaussNormC v c:= by
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
  · simp_all [PowerSeries.gaussNormC, gaussNormC, h_supp, -Finset.le_sup'_iff]
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


end Polynomial

@[simp]
theorem PowerSeries.gaussNormC_C [ZeroHomClass F R ℝ] (r : R) : gaussNormC v c (C R r) = v r := by
  simp [← @Polynomial.coe_C]


section Coram

variable (c : ℝ) (R F : Type*) [NormedRing R] --[IsUltrametricDist R]

noncomputable def gaussNormC' : PowerSeries R → ℝ :=
  fun f => sSup {‖f.coeff R i‖ * c ^ i | (i : ℕ)}

--theorem gaussNormC'_zero : gaussNormC' c R 0 = 0 := by simp [gaussNormC']

theorem gaussNormC'_eq (f : PowerSeries R) : gaussNormC' c R f = f.gaussNormC (NormedRing.toRingNorm R) c := by
  simp [gaussNormC', PowerSeries.gaussNormC]


end Coram
