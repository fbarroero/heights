import Mathlib

variable {R F : Type*} [Semiring R] [FunLike F R ℝ] (v : F) (c : ℝ)
namespace PowerSeries

noncomputable def gaussNormC (f : PowerSeries R) : ℝ := sSup {v (f.coeff R i) * c ^ i | (i : ℕ)}

@[simp]
lemma gaussNormC_zero [ZeroHomClass F R ℝ] : gaussNormC v c 0 = 0 := by simp [gaussNormC]

end PowerSeries

namespace Polynomial

def gaussNormC (p : R[X]) : ℝ := if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (v (p.coeff i) * c ^ i) else 0

@[simp]
lemma gaussNormC_zero : gaussNormC v c 0 = 0 := by simp [gaussNormC]

@[simp]
lemma gaussNormC_C [ZeroHomClass F R ℝ] (r : R) : (C r).gaussNormC v c = v r := by
  by_cases hr : r = (0 : R); simp [gaussNormC, hr]
  simp [gaussNormC, support_C, hr]

@[simp]
theorem gaussNormC_toPowerSeries [ZeroHomClass F R ℝ] (p : R[X]) : (p.toPowerSeries).gaussNormC v c = p.gaussNormC v c := by
  sorry

end Polynomial

@[simp]
theorem PowerSeries.gaussNormC_C [ZeroHomClass F R ℝ] (r : R) : (C R r).gaussNormC v c = v r := by
  simp [← @Polynomial.coe_C]

section NormedRing

variable (c : ℝ) (R F : Type*) [NormedRing R]

noncomputable def gaussNormC' : PowerSeries R → ℝ :=
  fun f => sSup {‖f.coeff R i‖ * c ^ i | (i : ℕ)}

theorem gaussNormC'_eq (f : PowerSeries R) : gaussNormC' c R f = f.gaussNormC (NormedRing.toRingNorm R) c := by
  simp [gaussNormC', PowerSeries.gaussNormC]

end NormedRing
