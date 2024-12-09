import Heights.ProductFormula
import Mathlib.LinearAlgebra.Projectivization.Basic

open Function LinearAlgebra.Projectivization NumberField
variable {K : Type*} [Field K] [NumberField K]

noncomputable def HeightProj {n : ℕ} : ℙ K (Fin n → K) → ℝ := by
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
