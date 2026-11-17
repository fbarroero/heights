module

public import Heights.SubspaceTheorem.Main

/-!
# Roth's theorem as a consequence of the Subspace Theorem

As a sanity check of our statement of the Subspace Theorem, we deduce Roth's theorem from its
case `n = 2`, applied to the linear forms `X - α Y` and `Y`
(see [evertse1993], Theorem 1.1 and the discussion following it).
-/

@[expose] public section

open Matrix

namespace Schmidt

/-- Two vectors of `ℚ²` with non-zero determinant are not contained in a proper subspace. -/
private lemma eq_top_of_det_ne_zero {V : Submodule ℚ (Fin 2 → ℚ)} {u w : Fin 2 → ℚ}
    (hu : u ∈ V) (hw : w ∈ V) (h : u 0 * w 1 - u 1 * w 0 ≠ 0) : V = ⊤ := by
  refine eq_top_iff.mpr fun v _ ↦ ?_
  have : v = ((v 0 * w 1 - v 1 * w 0) / (u 0 * w 1 - u 1 * w 0)) • u +
      ((u 0 * v 1 - u 1 * v 0) / (u 0 * w 1 - u 1 * w 0)) • w := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff h]
    fin_cases i <;> simp <;> ring
  rw [this]
  exact V.add_mem (V.smul_mem _ hu) (V.smul_mem _ hw)

/-- **Roth's theorem**, as a consequence of the Subspace Theorem: if `α` is a real algebraic
number and `ε > 0`, then there are only finitely many rational numbers `p / q` such that
`|α - p / q| < 1 / q ^ (2 + ε)`. -/
theorem roth (α : ℝ) (hα : IsAlgebraic ℚ α) {ε : ℝ} (hε : 0 < ε) :
    {r : ℚ | |α - r| < 1 / (r.den : ℝ) ^ (2 + ε)}.Finite := by
  -- the linear forms `X - α Y` and `Y`
  let L : Matrix (Fin 2) (Fin 2) ℝ := !![1, -α; 0, 1]
  have hL : L.det ≠ 0 := by simp [L, Matrix.det_fin_two]
  have halg : ∀ i j, IsAlgebraic ℚ (L i j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [L, isAlgebraic_zero, isAlgebraic_one, hα.neg]
  obtain ⟨T, hT, hcov⟩ := subspace_theorem_real L hL halg (ε := ε / 2) (by positivity)
  -- general facts on the approximations `r = p / q`
  have hfacts : ∀ r : ℚ, |α - r| < 1 / (r.den : ℝ) ^ (2 + ε) →
      |(r.num : ℝ)| ≤ (|α| + 1) * r.den ∧
      |((r.num : ℝ) - α * r.den) * r.den| ≤ (r.den : ℝ) ^ (-ε) := by
    intro r hr
    have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    have hq1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    have hr' : (r : ℝ) = r.num / r.den := by exact_mod_cast (Rat.num_div_den r).symm
    have hdiff : (r.num : ℝ) - α * r.den = -(α - r) * r.den := by
      rw [hr']
      field_simp
      ring
    have hlt1 : |α - r| < 1 :=
      hr.trans_le (by
        rw [div_le_one (by positivity)]
        exact Real.one_le_rpow hq1 (by positivity))
    constructor
    · have : (r.num : ℝ) = (α - (α - r)) * r.den := by
        rw [hr']
        field_simp
        ring
      rw [this, abs_mul, abs_of_pos hq]
      gcongr
      calc |α - (α - r)| ≤ |α| + |α - r| := abs_sub _ _
        _ ≤ |α| + 1 := by gcongr
    · rw [hdiff, abs_mul, abs_mul, abs_neg, abs_of_pos hq]
      calc |α - r| * r.den * r.den ≤ 1 / (r.den : ℝ) ^ (2 + ε) * r.den * r.den := by gcongr
        _ = (r.den : ℝ) ^ (-ε) := by
          rw [Real.rpow_add hq, Real.rpow_neg hq.le, Real.rpow_two]
          field_simp
  -- the approximations with small denominator
  have hsmall : {r : ℚ | |α - r| < 1 / (r.den : ℝ) ^ (2 + ε) ∧ (r.den : ℝ) < |α| + 1}.Finite := by
    obtain ⟨N, hN⟩ := exists_nat_gt ((|α| + 1) * (|α| + 1))
    refine ((Set.finite_Icc (-(N : ℤ)) N).prod (Set.finite_Icc (0 : ℤ) N)).image
      (fun p : ℤ × ℤ ↦ (p.1 : ℚ) / p.2) |>.subset fun r ⟨hr, hden⟩ ↦ ?_
    refine ⟨(r.num, r.den), ⟨?_, ?_⟩, by simpa using Rat.num_div_den r⟩
    · have h1 : |(r.num : ℝ)| ≤ N :=
        ((hfacts r hr).1.trans (by gcongr)).trans hN.le
      have h2 : |r.num| ≤ (N : ℤ) := by exact_mod_cast h1
      exact Set.mem_Icc.mpr (abs_le.mp h2)
    · have h1 : (r.den : ℝ) ≤ N := by
        have h0 : (0 : ℝ) ≤ |α| := abs_nonneg α
        nlinarith [hden, hN]
      have h1' : (r.den : ℤ) ≤ (N : ℤ) := by exact_mod_cast h1
      exact ⟨Int.natCast_nonneg _, h1'⟩
  -- the approximations with large denominator are solutions of the inequality in the
  -- Subspace Theorem
  have hbig : ∀ r : ℚ, |α - r| < 1 / (r.den : ℝ) ^ (2 + ε) → |α| + 1 ≤ (r.den : ℝ) →
      ∃ V ∈ T, (fun i ↦ ((![r.num, r.den] : Fin 2 → ℤ) i : ℚ)) ∈ V := by
    intro r hr hden
    refine hcov _ ?_
    have hq : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
    have hq1 : (1 : ℝ) ≤ r.den := by exact_mod_cast r.den_pos
    have hnorm : ‖(![r.num, r.den] : Fin 2 → ℤ)‖ ≤ (r.den : ℝ) ^ 2 := by
      refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i ↦ ?_
      fin_cases i
      · change ‖r.num‖ ≤ _
        rw [Int.norm_eq_abs]
        calc |(r.num : ℝ)| ≤ (|α| + 1) * r.den := (hfacts r hr).1
          _ ≤ r.den * r.den := by gcongr
          _ = (r.den : ℝ) ^ 2 := (sq _).symm
      · change ‖(r.den : ℤ)‖ ≤ _
        rw [Int.norm_eq_abs, Int.cast_natCast, abs_of_pos hq]
        nlinarith
    have hnorm_pos : 0 < ‖(![r.num, r.den] : Fin 2 → ℤ)‖ := by
      rw [norm_pos_iff]
      intro h
      have := congrFun h 1
      simp [r.den_ne_zero] at this
    rw [mem_solutionSet]
    calc |∏ i, eval L ![r.num, r.den] i| = |((r.num : ℝ) - α * r.den) * r.den| := by
          simp [eval, L, Matrix.mulVec, dotProduct, Fin.prod_univ_two, Fin.sum_univ_two]
          ring_nf
      _ ≤ (r.den : ℝ) ^ (-ε) := (hfacts r hr).2
      _ = ((r.den : ℝ) ^ 2) ^ (-(ε / 2)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hq.le]
          congr 1
          push_cast
          ring
      _ ≤ ‖(![r.num, r.den] : Fin 2 → ℤ)‖ ^ (-(ε / 2)) :=
          Real.rpow_le_rpow_of_nonpos hnorm_pos hnorm (by linarith)
  -- each proper subspace contains at most one of them
  have hbigfin : {r : ℚ | |α - r| < 1 / (r.den : ℝ) ^ (2 + ε) ∧ |α| + 1 ≤ (r.den : ℝ)}.Finite := by
    have h : ∀ r ∈ {r : ℚ | |α - r| < 1 / (r.den : ℝ) ^ (2 + ε) ∧ |α| + 1 ≤ (r.den : ℝ)},
        ∃ V ∈ T, (fun i ↦ ((![r.num, r.den] : Fin 2 → ℤ) i : ℚ)) ∈ V :=
      fun r hr ↦ hbig r hr.1 hr.2
    choose! f hfT hfV using h
    refine Set.Finite.of_injOn (f := f) (t := (T : Set _)) (fun r hr ↦ hfT r hr) ?_
      T.finite_toSet
    intro r hr r' hr' hrr'
    by_contra hne
    refine hT _ (hfT r hr) (eq_top_of_det_ne_zero (hfV r hr) (hrr' ▸ hfV r' hr') ?_)
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    intro h0
    apply hne
    rw [Rat.eq_iff_mul_eq_mul]
    have h1 : (r.num : ℚ) * (r'.den : ℚ) = (r.den : ℚ) * (r'.num : ℚ) := by
      push_cast at h0
      linarith
    exact_mod_cast (by rw [h1]; ring : (r.num : ℚ) * (r'.den : ℚ) = (r'.num : ℚ) * (r.den : ℚ))
  refine (hsmall.union hbigfin).subset fun r hr ↦ ?_
  rcases lt_or_ge (r.den : ℝ) (|α| + 1) with h | h
  · exact .inl ⟨hr, h⟩
  · exact .inr ⟨hr, h⟩

end Schmidt
