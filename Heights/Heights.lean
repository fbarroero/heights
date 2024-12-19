import Heights.ProductFormula
import Mathlib.Algebra.Order.Group.Finset
import Mathlib.LinearAlgebra.Projectivization.Basic

open Function LinearAlgebra.Projectivization NumberField
variable {K : Type*} [Field K] [NumberField K]


noncomputable def HeightProj {n : ℕ} : ℙ K (Fin n → K) → ℝ := by
  by_cases h_n : n = 0; exact fun x ↦ (1 : ℝ)
  have h₀ : (@Finset.univ (Fin n)).Nonempty := by
    simp only [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp (Nat.zero_lt_of_ne_zero h_n)
  let supinf : (w : InfinitePlace K) → (Fin n → K) → ℝ :=
    fun w x ↦ Finset.univ.sup' h₀ (fun i : Fin n ↦ (w (x i)) ^ w.mult)
  let supfin : (w : FinitePlace K) → (Fin n → K) → ℝ :=
    fun w x ↦ Finset.univ.sup' h₀ (fun i : Fin n ↦ (w (x i)))
  have hinf (t : K) (w : InfinitePlace K) (x : Fin n → K) : supinf w (t • x) = (w t) ^ w.mult * supinf w x := by
    by_cases h_t : t = 0; simp only [h_t, zero_smul, map_zero, ne_eq, InfinitePlace.mult_ne_zero,
      not_false_eq_true, zero_pow, zero_mul, supinf]
    sorry

    simp only [Pi.smul_apply, smul_eq_mul, map_mul, supinf]
    rw [Finset.mul₀_sup' (pow_pos (InfinitePlace.pos_iff.mpr h_t) w.mult)]
    congr
    ext i
    exact mul_pow (w t) (w (x i)) w.mult
  have hfin (t : K) (w : FinitePlace K) (x : Fin n → K) : supfin w (t • x) = (w t).toNNReal * supfin w x := by
    simp only [Pi.smul_apply, smul_eq_mul, _root_.map_mul, supfin]
    rw [mul_comm, NNReal.finset_sup_mul]
    congr
    ext i
    simp only [apply_nonneg, Real.toNNReal_mul, NNReal.coe_mul, Real.coe_toNNReal', sup_of_le_left, mul_comm]
  let f : {v : Fin n → K // v ≠ 0} → ℝ :=
    fun x ↦ ((∏ w : InfinitePlace K, supinf w x : ℝ) * (∏ᶠ w : FinitePlace K, supfin w x : ℝ)) ^
    ((Module.finrank ℚ K) : ℝ)⁻¹
  have hfproj : ∀ (x y : { v : Fin n → K // v ≠ 0 }) (t : K), x = t • (y : Fin n → K) → f x = f y := by
    intro x y t hxyt
    have hsupp : (mulSupport fun w ↦ (supfin w y : ℝ)).Finite := by
      simp only [mulSupport, supfin]
      let s : Fin n → Set (FinitePlace K) := fun i : Fin n ↦ (fun w : FinitePlace K ↦ w (y.val i)).mulSupport --{w : FinitePlace K | (w (y.val i)) ≠ 1}
      have h_fin (i : Fin n) (h : y.val i ≠ 0) : (s i).Finite := FinitePlace.mulSupport_finite h
      have h_subs : (mulSupport fun w ↦ (supfin w y : ℝ)) ⊆ ⋃ i ∈ {j | y.val j ≠ 0}, s i := by
        refine mulSupport_subset_iff.mpr ?_
        simp only [ne_eq, NNReal.coe_eq_one, Set.mem_setOf_eq, Set.mem_iUnion, mem_mulSupport,
          exists_prop, supfin, s]
        intro w hw
        contrapose! hw
        simp [Finset.sup]

        sorry

      sorry
    have h_t_nezero : t ≠ 0 := by
      intro h
      subst h
      simp only [ne_eq, zero_smul] at hxyt
      obtain ⟨val, property⟩ := x
      simp_all only [ne_eq, not_true_eq_false]
    simp only [ne_eq, NNReal.coe_prod, f, hxyt]
    congr 1
    --norm_cast
    simp_rw [hinf, hfin]
    norm_cast
    simp only [NNReal.coe_prod, NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal', apply_nonneg,
      sup_of_le_left]
    rw [Finset.prod_mul_distrib, finprod_mul_distrib (FinitePlace.mulSupport_finite h_t_nezero) hsupp, mul_mul_mul_comm,
      prod_eq_one h_t_nezero, one_mul]
  exact Projectivization.lift f hfproj

noncomputable def HeightProj' {n : ℕ} : ℙ K (Fin n → K) → ℝ := by
  by_cases h_n : n = 0; exact fun x ↦ (1 : ℝ)
  let supinf : (w : InfinitePlace K) → (Fin n → K) → NNReal :=
    fun w x ↦ Finset.univ.sup (fun i : Fin n ↦ (w (x i)).toNNReal ^ w.mult)
  let supfin : (w : FinitePlace K) → (Fin n → K) → NNReal :=
    fun w x ↦ Finset.univ.sup (fun i : Fin n ↦ (w (x i)).toNNReal)
  have hinf (t : K) (w : InfinitePlace K) (x : Fin n → K) : supinf w (t • x) = (w t).toNNReal ^ w.mult * supinf w x := by
    simp only [Pi.smul_apply, smul_eq_mul, _root_.map_mul, supinf, NNReal.mul_finset_sup]
    conv => lhs; rhs; simp only [apply_nonneg, Real.toNNReal_mul, mul_pow]
  have hfin (t : K) (w : FinitePlace K) (x : Fin n → K) : supfin w (t • x) = (w t).toNNReal * supfin w x := by
    simp only [Pi.smul_apply, smul_eq_mul, _root_.map_mul, supfin]
    rw [mul_comm, NNReal.finset_sup_mul]
    congr
    ext i
    simp only [apply_nonneg, Real.toNNReal_mul, NNReal.coe_mul, Real.coe_toNNReal', sup_of_le_left, mul_comm]
  let f : {v : Fin n → K // v ≠ 0} → ℝ :=
    fun x ↦ ((∏ w : InfinitePlace K, supinf w x : ℝ) * (∏ᶠ w : FinitePlace K, supfin w x : ℝ)) ^
    ((Module.finrank ℚ K) : ℝ)⁻¹
  have hfproj : ∀ (x y : { v : Fin n → K // v ≠ 0 }) (t : K), x = t • (y : Fin n → K) → f x = f y := by
    intro x y t hxyt
    have hsupp : (mulSupport fun w ↦ (supfin w y : ℝ)).Finite := by
      simp only [mulSupport, supfin]
      let s : Fin n → Set (FinitePlace K) := fun i : Fin n ↦ (fun w : FinitePlace K ↦ w (y.val i)).mulSupport --{w : FinitePlace K | (w (y.val i)) ≠ 1}
      have h_fin (i : Fin n) (h : y.val i ≠ 0) : (s i).Finite := FinitePlace.mulSupport_finite h
      have h_subs : (mulSupport fun w ↦ (supfin w y : ℝ)) ⊆ ⋃ i ∈ {j | y.val j ≠ 0}, s i := by
        refine mulSupport_subset_iff.mpr ?_
        simp only [ne_eq, NNReal.coe_eq_one, Set.mem_setOf_eq, Set.mem_iUnion, mem_mulSupport,
          exists_prop, supfin, s]
        intro w hw
        contrapose! hw
        simp [Finset.sup]

        sorry

      sorry
    have h_t_nezero : t ≠ 0 := by
      intro h
      subst h
      simp only [ne_eq, zero_smul] at hxyt
      obtain ⟨val, property⟩ := x
      simp_all only [ne_eq, not_true_eq_false]
    simp only [ne_eq, NNReal.coe_prod, f, hxyt]
    congr 1
    --norm_cast
    simp_rw [hinf, hfin]
    norm_cast
    simp only [NNReal.coe_prod, NNReal.coe_mul, NNReal.coe_pow, Real.coe_toNNReal', apply_nonneg,
      sup_of_le_left]
    rw [Finset.prod_mul_distrib, finprod_mul_distrib (FinitePlace.mulSupport_finite h_t_nezero) hsupp, mul_mul_mul_comm,
      prod_eq_one h_t_nezero, one_mul]
  exact Projectivization.lift f hfproj
