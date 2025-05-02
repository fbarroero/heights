import Mathlib

namespace Polynomial

--https://kconrad.math.uconn.edu/blurbs/ringtheory/gaussnormlemma.pdf

variable {R α : Type*} [Semiring R] [Semiring α] [LinearOrder α]
 (f : AbsoluteValue R α) (hna : IsNonarchimedean f)

theorem sup'_nonneg_of_ne_zero {p : R[X]} (h : p.support.Nonempty) :
    0 ≤ p.support.sup' h fun i ↦ f (p.coeff i) := by
  simp only [Finset.le_sup'_iff]
  exact ⟨p.natDegree, by simp_all⟩

theorem coeff_le_sup {p : R[X]} (h : p.support.Nonempty) (i : ℕ) :
    f (p.coeff i) ≤ p.support.sup' h (fun j ↦ f (p.coeff j)) := by
  by_cases hs : i ∈ p.support;
  · exact Finset.le_sup' (fun j ↦ f (p.coeff j)) hs
  · simp_all [sup'_nonneg_of_ne_zero f h]

def GaussNorm : R[X] → α := fun p ↦ if h : p.support.Nonempty then p.support.sup' h fun i ↦
    (f (p.coeff i)) else 0

@[simp]
theorem GaussNorm_zero : GaussNorm f 0 = 0 := by simp [GaussNorm]

@[simp]
theorem GaussNorm_nonneg (p : R[X]) : 0 ≤ GaussNorm f p := by
  simp only [GaussNorm]
  by_cases hp : p.support.Nonempty
  · simp [hp, sup'_nonneg_of_ne_zero, -Finset.le_sup'_iff]
  · simp [hp]

@[simp]
theorem GaussNorm_C (r : R) : GaussNorm f (C r) = f r := by
  by_cases hr : r = 0
  · simp [hr]
  · simp_all [GaussNorm, support_C]

@[simp]
theorem GaussNorm_monomial (n : ℕ) (r : R) : GaussNorm f (Polynomial.monomial n r) = f r := by
  by_cases hr : r = 0
  · simp [hr]
  · simp_all [GaussNorm, support_monomial]

@[simp] --TODO: golf
theorem max_eq_zero_iff (p : R[X]) : p.GaussNorm f = 0 ↔ p = 0 := by
  simp only [GaussNorm, support_nonempty, dite_eq_right_iff]
  refine ⟨?_, fun hp _ ↦ by simp [hp]⟩
  --
  /- intro hp
  refine leadingCoeff_eq_zero.mp ?_
  rw [← f.eq_zero']
  simp only [MulHom.toFun_eq_coe, AbsoluteValue.coe_toMulHom]
  by_cases h : p = 0; simp [h]
  specialize hp h
  have : p.natDegree ∈ p.support := by exact natDegree_mem_support_of_nonzero h
  have := Finset.le_sup' (α := α) (fun n ↦ f (p.coeff n)) (natDegree_mem_support_of_nonzero h) -/

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
    simp only [support_nonempty, ne_eq, h', not_false_eq_true, ↓reduceDIte, Finset.le_sup'_iff,
      mem_support_iff]
    refine ⟨i, mem_support_iff.mp h, le_refl (f (p.coeff i))⟩
  · simp [not_mem_support_iff.mp h]


include hna in
theorem isNonarchimedean_GaussNorm [AddLeftMono α] : IsNonarchimedean (GaussNorm f) := by
  intro p q
  by_cases hp : p = 0; simp [hp]
  by_cases hq : q = 0; simp [hq]
  by_cases hpq : p + q = 0; simp [hpq]
  simp only [GaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte, coeff_add, hp,
    hq, Finset.sup'_le_iff, mem_support_iff]
  intro b hcoeff
  apply le_trans (hna (p.coeff b) (q.coeff b))
  apply max_le_max <;>
  apply coeff_le_sup

noncomputable def GaussNormAbs [IsDomain R] [ IsStrictOrderedRing α] [MulPosMono α] [PosMulMono α] : AbsoluteValue R[X] α where
  toFun := GaussNorm f
  map_mul' := by --Finish this
    intro p q
    by_cases hp : p = 0; simp [hp]
    by_cases hq : q = 0; simp [hq]
    have hpq : p * q ≠ 0 := by simp [hp, hq]
    simp_all only [← support_nonempty, ne_eq, GaussNorm, dite_true]
    apply le_antisymm
    · simp only [support_nonempty, ne_eq, not_false_eq_true, Finset.sup'_le_iff, mem_support_iff]
      intro b a
      simp_all only [ne_eq, mul_eq_zero, or_self, not_false_eq_true]
      rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      let g := fun k ↦ p.coeff (k, b - k).1 * q.coeff (k, b - k).2
      obtain ⟨x, hx1, hx2⟩ := IsNonarchimedean.finset_image_add_of_nonempty (t := Finset.range b.succ) hna g Finset.nonempty_range_succ
      apply le_trans hx2
      simp only [AbsoluteValue.map_mul, g]
      gcongr
      · apply sup'_nonneg_of_ne_zero
      · apply coeff_le_sup
      · apply coeff_le_sup
    ·

      sorry
  nonneg' := fun x ↦ GaussNorm_nonneg f x
  eq_zero' := fun p ↦ max_eq_zero_iff f p
  add_le' := by
    intro p q
    apply IsNonarchimedean.add_le
    exact fun x ↦ GaussNorm_nonneg f x
    exact isNonarchimedean_GaussNorm f hna
    /- by_cases hp : p = 0; simp [hp]
    by_cases hq : q = 0; simp [hq]
    by_cases hpq : p + q = 0;
    · simp only [hpq, GaussNorm_zero]
      refine Left.add_nonneg ?_ ?_
      exact GaussNorm_nonneg f p
      exact GaussNorm_nonneg f q
    · simp only [GaussNorm, support_nonempty, ne_eq, hpq, not_false_eq_true, ↓reduceDIte,
      coeff_add, hp, hq, Finset.sup'_le_iff, mem_support_iff]
      intro b hcoeff
      apply le_trans <| AbsoluteValue.add_le f (p.coeff b) (q.coeff b)
      exact add_le_add (coeff_le_sup f (by simp [hp]) b) (coeff_le_sup f (by simp [hq]) b) -/





end Polynomial

--#min_imports
