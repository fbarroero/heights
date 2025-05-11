import Mathlib

namespace Real


theorem sSup_eq_sup' (s : Set ℝ) (h_nonempty : s.Nonempty) (h_fin : s.Finite) :
    sSup s = (h_fin.toFinset).sup' ((Set.Finite.toFinset_nonempty h_fin).mpr h_nonempty) (id)  := by
  have : h_fin.toFinset.Nonempty := by
    exact (Set.Finite.toFinset_nonempty h_fin).mpr h_nonempty
  have hbdd : BddAbove s := by
    sorry
  let t := h_fin.toFinset

  obtain ⟨x, hx⟩ := Real.exists_isLUB h_nonempty hbdd
  have : (h_fin.toFinset).sup' ((Set.Finite.toFinset_nonempty h_fin).mpr h_nonempty) (id) = x := by sorry
  classical

  simp_all [sSup, h_nonempty, h_fin, Set.Finite.toFinset_nonempty, Set.Finite.toFinset, hbdd, hx]



  sorry

end Real
