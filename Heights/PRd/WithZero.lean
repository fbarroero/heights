import Mathlib.Data.Int.WithZero

--#min_imports

noncomputable section

open scoped  NNReal

open Multiplicative WithZero Equiv WithZeroMulInt

theorem toNNReal_eq_one_iff {e : NNReal} (m : ℤₘ₀) (he0 : e ≠ 0) (he1 : e ≠ 1) :
    toNNReal he0 m = 1 ↔ m = 1 := by
  by_cases hm : m = 0
  · subst hm
    simp_all only [ne_eq, map_zero, zero_ne_one]
  · constructor
    · rw [toNNReal_neg_apply he0 hm]
      intro h
      rw [zpow_eq_one_iff_right₀ (zero_le e) he1] at h
      rw [← WithZero.coe_unzero hm]
      simp_all only [ne_eq, toAdd_eq_zero, coe_one]
    · intro a
      subst a
      simp_all only [ne_eq, one_ne_zero, not_false_eq_true, map_one]

theorem toNNReal_lt_one_iff {e : NNReal} {m : ℤₘ₀} (he : 1 < e) :
    toNNReal (ne_zero_of_lt he) m < 1 ↔ m < 1 := by
  have mono := toNNReal_strictMono he
  have : 1 = (toNNReal (ne_zero_of_lt he)) 1 := rfl
  simp_rw [this]
  constructor
  · contrapose!
    exact fun h ↦ (StrictMono.le_iff_le mono).mpr h
  · exact fun h ↦ mono h

theorem toNNReal_le_one_iff {e : NNReal} {m : ℤₘ₀} (he : 1 < e) :
    toNNReal (ne_zero_of_lt he) m ≤ 1 ↔ m ≤ 1 := by
  have mono := toNNReal_strictMono he
  constructor
  · apply le_imp_le_of_lt_imp_lt
    exact fun a ↦ LT.lt.trans_eq' (mono a) rfl
  · apply le_imp_le_of_lt_imp_lt
    exact fun h ↦ (StrictMono.lt_iff_lt mono).mp h
