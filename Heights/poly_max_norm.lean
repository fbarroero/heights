import Mathlib

namespace Polynomial

--https://kconrad.math.uconn.edu/blurbs/ringtheory/gaussnormlemma.pdf

variable {R α F : Type*} [Semiring R] [Semiring α] [LinearOrder α] --[SemilatticeSup α]
 (f : AbsoluteValue R α) (hna : IsNonarchimedean f)

theorem sup'_nonneg_of_ne_zero {p : R[X]} (h : p ≠ 0) :
    0 ≤ p.support.sup' (by simp [h]) fun i ↦ f (p.coeff i) := by
  --have h_supp_deg : p.natDegree ∈ p.support := by simp [h]
  have hlc : p.coeff p.natDegree ≠ 0 := by simp [h]
  simp only [Finset.le_sup'_iff, mem_support_iff, ne_eq, apply_nonneg, and_true]
  exact ⟨p.natDegree, hlc⟩

theorem coeff_le_sup {p : R[X]} (h : p ≠ 0) (i : ℕ) :
    f (p.coeff i) ≤ p.support.sup' (by simp [h]) (fun j ↦ f (p.coeff j)) := by
  by_cases hs : i ∈ p.support;
  · exact Finset.le_sup' (fun j ↦ f (p.coeff j)) hs
  · simp_all [mem_support_iff, sup'_nonneg_of_ne_zero f h]

variable [DecidableEq R]

noncomputable def GaussNorm : R[X] → α := fun p ↦ if h : p ≠ 0 then p.support.sup' (by simp [h]) fun i ↦
    (f (p.coeff i)) else 0

@[simp]
theorem max_zero : GaussNorm f 0 = 0 := by simp [GaussNorm]

@[simp]
theorem GaussNorm_nonneg (p : R[X]) : 0 ≤ GaussNorm f p := by
  simp only [GaussNorm, ne_eq, dite_not]
  by_cases hp : p = 0; simp [hp]
  simp only [hp, ↓reduceDIte, Finset.le_sup'_iff, mem_support_iff, apply_nonneg, and_true]
  refine ⟨p.natDegree, mem_support_iff.mp <| natDegree_mem_support_of_nonzero hp⟩


@[simp]
theorem max_eq_zero_iff (p : R[X]) : p.GaussNorm f = 0 ↔ p = 0 := by
  simp only [GaussNorm, ne_eq, dite_not, dite_eq_left_iff]
  refine ⟨?_, fun hp _ ↦ by simp [hp]⟩
  contrapose!
  intro hp
  simp_all only [ne_eq, not_false_eq_true, exists_true_left]
  intro h0
  have pos : 0 < f (p.coeff p.natDegree) := by simp_all
  have h_supp_deg : p.natDegree ∈ p.support := by simp [hp]
  have := Finset.le_sup' (α := α) (fun i ↦ f (p.coeff i)) h_supp_deg
  rw [h0, ← not_lt] at this
  exact this pos

theorem coeff_le_GaussNorm (p : R[X]) (i : ℕ) :
    f (p.coeff i) ≤ GaussNorm f p := by
  by_cases h : i ∈ p.support;
  · rw [GaussNorm]
    have h' : p ≠ 0 := by
      rw [← nonempty_support_iff]
      exact ⟨i, h⟩
    simp only [ne_eq, h', not_false_eq_true, ↓reduceDIte, Finset.le_sup'_iff, mem_support_iff]
    refine ⟨i, mem_support_iff.mp h, le_refl (f (p.coeff i))⟩
  · simp [not_mem_support_iff.mp h]

noncomputable def GaussNormAbs [IsDomain R] [AddLeftMono α] : AbsoluteValue R[X] α where
  toFun := GaussNorm f
  map_mul' := by
    intro p q
    by_cases hp : p = 0; simp [hp]
    by_cases hq : q = 0; simp [hq]
    have hpq : p * q ≠ 0 := by simp [hp, hq]
    simp [GaussNorm, hp, hq, hpq]
    sorry
  nonneg' := fun x ↦ GaussNorm_nonneg f x
  eq_zero' := fun p ↦ max_eq_zero_iff f p
  add_le' := by
    intro p q
    by_cases hp : p = 0; simp [hp]
    by_cases hq : q = 0; simp [hq]
    by_cases hpq : p + q = 0;
    · simp only [hpq, max_zero]
      refine Left.add_nonneg ?_ ?_
      exact GaussNorm_nonneg f p
      exact GaussNorm_nonneg f q
    · simp only [GaussNorm, ne_eq, hpq, not_false_eq_true, ↓reduceDIte, coeff_add, hp, hq,
      Finset.sup'_le_iff, mem_support_iff]
      intro b hcoeff
      apply le_trans <| AbsoluteValue.add_le f (p.coeff b) (q.coeff b)
      exact add_le_add (coeff_le_sup f hp b) (coeff_le_sup f hq b)

end Polynomial

--#min_imports
